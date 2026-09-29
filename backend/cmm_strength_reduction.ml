(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42-44-45"]

open! Int_replace_polymorphic_compare
open Cmm
module V = Backend_var
module VP = Backend_var.With_provenance

exception Not_applicable

(* {1 Generic traversal} *)

let map_subexpressions f (expr : expression) : expression =
  match expr with
  | Cconst_int _ | Cconst_natint _ | Cconst_float32 _ | Cconst_float _
  | Cconst_vec128 _ | Cconst_vec256 _ | Cconst_vec512 _ | Cconst_mask _
  | Cconst_symbol _ | Cvar _ | Cinvalid _ ->
    expr
  | Clet (v, def, body) -> Clet (v, f def, f body)
  | Cphantom_let (v, def, body) -> Cphantom_let (v, def, f body)
  | Cname_for_debugger (v, body) -> Cname_for_debugger (v, f body)
  | Ctuple exprs -> Ctuple (List.map f exprs)
  | Cop (op, args, dbg) -> Cop (op, List.map f args, dbg)
  | Csequence (e1, e2) -> Csequence (f e1, f e2)
  | Cifthenelse (cond, dbg_cond, ifso, dbg_ifso, ifnot, dbg_ifnot) ->
    Cifthenelse (f cond, dbg_cond, f ifso, dbg_ifso, f ifnot, dbg_ifnot)
  | Cswitch (sel, index, cases, dbg) ->
    Cswitch (f sel, index, Array.map (fun (case, dbg) -> f case, dbg) cases, dbg)
  | Ccatch (flag, handlers, body) ->
    Ccatch
      ( flag,
        List.map
          (fun (handler : static_handler) ->
            { handler with body = f handler.body })
          handlers,
        f body )
  | Cexit (lbl, args, traps) -> Cexit (lbl, List.map f args, traps)

let iter_subexpressions f expr =
  ignore
    (map_subexpressions
       (fun sub ->
         f sub;
         sub)
       expr
      : expression)

let binders_of expr =
  match expr with
  | Clet (v, _, _) | Cphantom_let (v, _, _) | Cname_for_debugger (v, _) ->
    [VP.var v]
  | Ccatch (_, handlers, _) ->
    List.concat_map
      (fun (handler : static_handler) ->
        List.map (fun (param, _) -> VP.var param) handler.params)
      handlers
  | _ -> []

(* Every variable bound anywhere within [expr], [expr] itself included. *)
let rec bound_variables acc expr =
  let acc =
    List.fold_left (fun acc v -> V.Set.add v acc) acc (binders_of expr)
  in
  let acc = ref acc in
  iter_subexpressions (fun sub -> acc := bound_variables !acc sub) expr;
  !acc

(* Variables bound more than once in a function body. [Cmm] is normally in
   single-binding form, but expressions do get duplicated on the way here, and
   the analysis below reasons about a variable from its binding, so a variable
   with two bindings must simply be left alone. *)
let duplicate_binders ~params body =
  let seen = ref (V.Set.of_list params) in
  let duplicated = ref V.Set.empty in
  let rec loop expr =
    List.iter
      (fun v ->
        if V.Set.mem v !seen
        then duplicated := V.Set.add v !duplicated
        else seen := V.Set.add v !seen)
      (binders_of expr);
    iter_subexpressions loop expr
  in
  loop body;
  !duplicated

let rec occurs var expr =
  match expr with
  | Cvar v -> V.same v var
  | _ ->
    let found = ref false in
    iter_subexpressions (fun sub -> found := !found || occurs var sub) expr;
    !found

(* {1 Machtypes}

   The derived variable is live across the loop's GC safepoint, so it must not
   be derived from a pointer: the collector would have no way to update it.
   Pointer arithmetic in [Cmm] uses [Caddv]/[Cadda] rather than [Caddi], so this
   only rules out malformed input, but the failure mode is heap corruption, so
   check for it rather than assume it. *)

let is_int_machtype machtype = equal_machtype machtype typ_int

let is_int_expression int_vars expr =
  match expr with
  | Cconst_int _ | Cconst_natint _ -> true
  | Cvar v -> V.Set.mem v int_vars
  | Cop (op, _, _) -> (
    match op with
    | Caddi | Csubi | Cmuli | Cand | Cor | Cxor | Clsl | Clsr | Casr | Cclz
    | Cctz | Cpopcnt | Ccmpi _ | Ccmpf _ ->
      true
    | _ -> false)
  | _ -> false

let add_int_var ~duplicated int_vars v =
  if V.Set.mem v duplicated then int_vars else V.Set.add v int_vars

let add_int_params ~duplicated int_vars params =
  List.fold_left
    (fun int_vars (param, machtype) ->
      if is_int_machtype machtype
      then add_int_var ~duplicated int_vars (VP.var param)
      else int_vars)
    int_vars params

(* {1 Affine functions of the loop counter}

   [{ multiplier; offset }] denotes the value [multiplier * counter + offset].
   Both are kept small, so that every constant computed from them stays well
   inside the host [int] and a wrong constant cannot be produced silently. *)

type affine =
  { multiplier : int;
    offset : int
  }

let max_affine = 1 lsl 20

let in_range n = n >= -max_affine && n <= max_affine

let normalise affine =
  if in_range affine.multiplier && in_range affine.offset
  then Some affine
  else None

(* An operand pair of which exactly one side is an in-range constant. *)
let split_constant args =
  match args with
  | [inner; Cconst_int (n, _)] | [Cconst_int (n, _); inner] ->
    if in_range n then Some (inner, n) else None
  | _ -> None

let rec affine_of ~affines (expr : expression) =
  match expr with
  | Cvar v -> V.Map.find_opt v affines
  | Cop (Clsl, [inner; Cconst_int (shift, _)], _) when shift >= 0 && shift <= 20
    -> (
    match affine_of ~affines inner with
    | None -> None
    | Some { multiplier; offset } ->
      normalise { multiplier = multiplier lsl shift; offset = offset lsl shift }
    )
  | Cop (Caddi, args, _) -> (
    match split_constant args with
    | None -> None
    | Some (inner, n) -> (
      match affine_of ~affines inner with
      | None -> None
      | Some affine -> normalise { affine with offset = affine.offset + n }))
  | Cop (Csubi, [inner; Cconst_int (n, _)], _) when in_range n -> (
    match affine_of ~affines inner with
    | None -> None
    | Some affine -> normalise { affine with offset = affine.offset - n })
  | _ -> None

(* Variables of [body] that are affine functions of [counter], [counter]
   included. A [Clet] whose defining expression is affine is recorded before its
   own body is scanned, so chains of such bindings are followed. *)
let affines_of_body ~duplicated ~counter body =
  if V.Set.mem counter duplicated
  then V.Map.empty
  else
    let affines =
      ref (V.Map.singleton counter { multiplier = 1; offset = 0 })
    in
    let rec loop expr =
      (match expr with
      | Clet (v, def, _) when not (V.Set.mem (VP.var v) duplicated) -> (
        match affine_of ~affines:!affines def with
        | Some affine -> affines := V.Map.add (VP.var v) affine !affines
        | None -> ())
      | _ -> ());
      iter_subexpressions loop expr
    in
    loop body;
    !affines

(* Apply the affine function to [start], folding when that is a constant. *)
let apply_affine { multiplier; offset } start dbg =
  match start with
  | Cconst_int (n, _) when in_range n ->
    Cconst_int ((multiplier * n) + offset, dbg)
  | _ ->
    let scaled =
      if multiplier = 1
      then start
      else Cop (Cmuli, [start; Cconst_int (multiplier, dbg)], dbg)
    in
    if offset = 0
    then scaled
    else Cop (Caddi, [scaled; Cconst_int (offset, dbg)], dbg)

(* {1 Exits} *)

let is_label label (handler : static_handler) =
  Static_label.equal handler.label label

(* The argument lists of every [Cexit] to [label] within [roots]. Raises
   [Not_applicable] if [label] is rebound by a nested handler, since then we
   cannot tell which exits belong to which handler. *)
let collect_exit_args ~label ~roots =
  let acc = ref [] in
  let rec loop expr =
    (match expr with
    | Ccatch (_, handlers, _) ->
      if List.exists (is_label label) handlers then raise Not_applicable
    | Cexit (Lbl l, args, _) when Static_label.equal l label ->
      acc := args :: !acc
    | _ -> ());
    iter_subexpressions loop expr
  in
  List.iter loop roots;
  !acc

(* How one exit supplies the loop counter:

   - [Step n]: it passes [counter + n], so a value [m * counter + c] carried
   alongside becomes [m * counter + c + m * n]: the carried value is stepped by
   the constant [m * n]. Both the original and the carried addition are wrapping
   native additions, and wrapping addition is associative, so the two agree on
   every input, overflow included.

   - [Fresh start]: the exit passes something that is not a constant step, so
   the carried value is rebuilt as [invariant + f start]. [start] is restricted
   to constants and variables so that it can be duplicated without duplicating
   work or effects. *)
type exit_arg =
  | Step of int
  | Fresh of expression

let classify_exit_arg ~affines (arg : expression) =
  match affine_of ~affines arg with
  | Some { multiplier = 1; offset } -> Some (Step offset)
  | Some _ -> None
  | None -> (
    match arg with Cconst_int _ | Cvar _ -> Some (Fresh arg) | _ -> None)

let rec add_exit_args ~label ~extra expr =
  match expr with
  | Cexit (Lbl l, args, traps) when Static_label.equal l label ->
    let extra_args = extra args in
    Cexit
      (Lbl l, List.map (add_exit_args ~label ~extra) args @ extra_args, traps)
  | _ -> map_subexpressions (add_exit_args ~label ~extra) expr

(* {1 Derived induction variables} *)

(* [Some (invariant, index)] if [expr] is [invariant + index] or [index +
   invariant], where [index] is an affine function of the loop counter and
   [invariant] is not. *)
let sum_with ~affines (expr : expression) =
  match expr with
  | Cop (Caddi, [Cvar a; Cvar b], _) -> (
    match V.Map.mem a affines, V.Map.mem b affines with
    | false, true -> Some (a, b)
    | true, false -> Some (b, a)
    | true, true | false, false -> None)
  | _ -> None

let same_pair (a1, b1) (a2, b2) = V.same a1 a2 && V.same b1 b2

let sum_candidates ~affines expr =
  let acc = ref [] in
  let rec loop expr =
    (match sum_with ~affines expr with
    | Some pair ->
      if not (List.exists (same_pair pair) !acc) then acc := pair :: !acc
    | None -> ());
    iter_subexpressions loop expr
  in
  loop expr;
  List.rev !acc

let rec replace_sum ~affines ~pair ~derived expr =
  match sum_with ~affines expr with
  | Some found when same_pair found pair -> Cvar derived
  | Some _ | None ->
    map_subexpressions (replace_sum ~affines ~pair ~derived) expr

let nth_arg args index =
  match List.nth_opt args index with
  | Some arg -> arg
  | None -> raise Not_applicable

(* Transform the [Ccatch Recursive] node [expr] for the handler named [label].
   Raises [Not_applicable] if nothing can or should be done, in which case the
   caller keeps the original node. *)
let reduce ~duplicated ~int_vars ~label ~expr =
  let flag, handlers, body =
    match expr with
    | Ccatch (flag, handlers, body) -> flag, handlers, body
    | _ -> raise Not_applicable
  in
  let handler =
    match List.find_opt (is_label label) handlers with
    | Some handler -> handler
    | None -> raise Not_applicable
  in
  let roots =
    body :: List.map (fun (handler : static_handler) -> handler.body) handlers
  in
  let exits = collect_exit_args ~label ~roots in
  (match exits with [] -> raise Not_applicable | _ :: _ -> ());
  let arity = List.length handler.params in
  List.iter
    (fun args ->
      if List.compare_length_with args arity <> 0 then raise Not_applicable)
    exits;
  (* The first integer parameter that every exit either steps by a constant or
     resets to a duplicable value, and that at least one exit steps. *)
  let rec find_counter index params =
    match params with
    | [] -> raise Not_applicable
    | (param, machtype) :: params ->
      let affines =
        if is_int_machtype machtype
        then affines_of_body ~duplicated ~counter:(VP.var param) handler.body
        else V.Map.empty
      in
      let classified =
        if V.Map.is_empty affines
        then []
        else
          List.map
            (fun args -> classify_exit_arg ~affines (nth_arg args index))
            exits
      in
      let eligible =
        List.exists
          (function Some (Step _) -> true | Some (Fresh _) | None -> false)
          classified
        && List.for_all Option.is_some classified
      in
      if eligible then index, affines else find_counter (index + 1) params
  in
  let index, affines = find_counter 0 handler.params in
  (* The invariant must be bound outside the whole [Ccatch]. [Cmm] has no
     assignment, so a binding is the only way a variable can change: being bound
     outside makes it loop-invariant, and also guarantees it is in scope at
     every exit, including the entry edges where the derived variable is
     initialised. *)
  let bound_inside = bound_variables V.Set.empty expr in
  let usable invariant =
    (not (V.Set.mem invariant bound_inside)) && V.Set.mem invariant int_vars
  in
  let candidates =
    List.filter
      (fun (invariant, _) -> usable invariant)
      (sum_candidates ~affines handler.body)
  in
  let derived, handler_body =
    List.fold_left
      (fun (derived, handler_body) pair ->
        let var = V.create_local "sr_index" in
        let rewritten = replace_sum ~affines ~pair ~derived:var handler_body in
        (* If the invariant is still needed inside the loop for something other
           than this sum, then carrying the sum as well costs a register rather
           than saving one, so leave the candidate alone. *)
        if occurs (fst pair) rewritten
        then derived, handler_body
        else (pair, var) :: derived, rewritten)
      ([], handler.body) candidates
  in
  let derived = List.rev derived in
  (match derived with [] -> raise Not_applicable | _ :: _ -> ());
  let dbg = handler.dbg in
  let extra args =
    let classified = classify_exit_arg ~affines (nth_arg args index) in
    List.map
      (fun ((invariant, index_var), var) ->
        let affine =
          match V.Map.find_opt index_var affines with
          | Some affine -> affine
          | None -> raise Not_applicable
        in
        match classified with
        | Some (Step n) ->
          Cop (Caddi, [Cvar var; Cconst_int (affine.multiplier * n, dbg)], dbg)
        | Some (Fresh start) ->
          Cop (Caddi, [Cvar invariant; apply_affine affine start dbg], dbg)
        | None -> raise Not_applicable)
      derived
  in
  let extra_params =
    List.map (fun (_, var) -> VP.create var, typ_int) derived
  in
  let handlers =
    List.map
      (fun (handler : static_handler) ->
        let handler =
          if is_label label handler
          then
            { handler with
              params = handler.params @ extra_params;
              body = handler_body
            }
          else handler
        in
        { handler with body = add_exit_args ~label ~extra handler.body })
      handlers
  in
  Ccatch (flag, handlers, add_exit_args ~label ~extra body)

(* {1 Interior pointers}

   A loop that contains no safepoint may hold pointers into the middle of a heap
   block: no collection can happen while they are live, so the collector never
   has to make sense of them. [Addr] is exactly that kind of value -- a derived
   pointer, ignored by the GC, and a fatal error ("bad GC root") if it is ever
   live at a frame descriptor. So in such a loop the address of an array row can
   be formed once, ahead of the loop, instead of being rebuilt from a row index
   on every iteration.

   An access [a.(b + i)] reaches [Cmm] as

   {v (+a (+a a (<< (+ b i) 2)) -8) v}

   with [i] an affine function [m * c + k] of the handler parameter [c] that is
   the loop counter. [Caddi], [Cadda] and [Clsl] are wrapping native operations
   and shifting distributes over wrapping addition, so that address is equal, on
   every input and overflow included, to

   {v (+a (+a (+a a (<< b 2)) (<< c 3)) -4) v}

   whose leading summand is loop-invariant. Hoisting it leaves one addressing
   mode [disp(base, counter, scale)] per row, so four rows share one index
   register and one increment where they used to carry four running indices. The
   counter is used naked, so the retagging of a [for] counter leaves the loop as
   well.

   Only the address operand of a [Cload] or a [Cstore] is rewritten, so the
   derived pointer is consumed by the addressing mode that needs it and by
   nothing else. *)

(* Operations at which a frame descriptor may be emitted or the GC may run.
   Written as a complete match, so that a new [Cmm] operation is a compile error
   here rather than a silently permitted safepoint.

   [Craise] is not one of them: the amd64 emitter records the frame of a raise
   with an empty live set, and [Raise_notrace] records no frame at all, so the
   bound-check raises of a checked array access cannot turn a derived pointer
   into a GC root. [Cdivi] and [Cmodi] are rejected because their
   division-by-zero path is a call. *)
let operation_is_safepoint (op : operation) =
  match op with
  | Capply _ | Cextcall _ | Calloc _ | Cpoll | Cprobe _ | Cbeginregion
  | Cendregion | Catomic _ | Cdivi _ | Cmodi _ ->
    true
  | Cload _ | Cstore _ | Caddi | Csubi | Cmuli | Cmulhi _ | Caddi128 | Csubi128
  | Cmuli64 _ | Cand | Cor | Cxor | Clsl | Clsr | Casr | Cbswap _ | Ccsel _
  | Cclz | Cctz | Cpopcnt | Cprefetch _ | Ccmpi _ | Caddv | Cadda | Cnegf _
  | Cabsf _ | Caddf _ | Csubf _ | Cmulf _ | Cdivf _ | Cpackf32
  | Creinterpret_cast _ | Cstatic_cast _ | Ccmpf _ | Craise _
  | Cprobe_is_enabled _ | Copaque | Ctuple_field _ | Cdls_get | Ctls_get
  | Cdomain_index | Cpause ->
    false

(* Does no collection happen anywhere inside [expr]? A nested loop is covered by
   the same walk: a back edge only carries a poll when polling is enabled, and
   the caller has already established that it is not. *)
let rec is_gc_free expr =
  match expr with
  | Cop (op, _, _) when operation_is_safepoint op -> false
  | _ ->
    let safe = ref true in
    iter_subexpressions (fun sub -> if !safe then safe := is_gc_free sub) expr;
    !safe

(* {2 Address expressions}

   [{ root; scale; index; disp }] denotes [root + scale * index + disp]. At most
   one scaled term is accepted; anything else declines. *)

type address =
  { root : V.t;
    scale : int;
    index : expression option;
    disp : int
  }

let set_index address scale index =
  match address.index with
  | Some _ -> None
  | None -> Some { address with scale; index = Some index }

let rec address_of (expr : expression) =
  match expr with
  | Cvar root -> Some { root; scale = 1; index = None; disp = 0 }
  | Cop (Cadda, [lhs; rhs], _) -> (
    match address_of lhs with
    | None -> None
    | Some address -> (
      match rhs with
      | Cconst_int (n, _) when in_range n ->
        Some { address with disp = address.disp + n }
      | Cop (Clsl, [inner; Cconst_int (shift, _)], _)
        when shift >= 0 && shift <= 3 ->
        set_index address (1 lsl shift) inner
      | Cop (Cmuli, args, _) -> (
        match split_constant args with
        | Some (inner, n) when n = 1 || n = 2 || n = 4 || n = 8 ->
          set_index address n inner
        | Some _ | None -> set_index address 1 rhs)
      | _ -> set_index address 1 rhs))
  | _ -> None

(* {2 Index expressions}

   [{ invariant; coefficient; multiplier; offset }] denotes

   {v coefficient * invariant + multiplier * counter + offset v}

   Only one invariant term is carried: it is what becomes the hoisted pointer,
   and two of them would need two pointers. *)

type index =
  { invariant : V.t option;
    coefficient : int;
    multiplier : int;
    offset : int
  }

let zero_index =
  { invariant = None; coefficient = 0; multiplier = 0; offset = 0 }

let normalise_index index =
  if
    in_range index.coefficient && in_range index.multiplier
    && in_range index.offset
  then Some index
  else None

let add_index left right =
  match left.invariant, right.invariant with
  | Some _, Some _ -> None
  | None, invariant | invariant, None ->
    normalise_index
      { invariant;
        coefficient = left.coefficient + right.coefficient;
        multiplier = left.multiplier + right.multiplier;
        offset = left.offset + right.offset
      }

let scale_index n index =
  normalise_index
    { index with
      coefficient = index.coefficient * n;
      multiplier = index.multiplier * n;
      offset = index.offset * n
    }

(* [Clet]-bound definitions are followed, because a checked array access binds
   the index expression to a variable and shares it with the bound check. Fuel
   bounds the work; [Cmm] bindings are acyclic, so it is not needed for
   termination. *)
let rec index_of ~affines ~defs ~invariant ~fuel (expr : expression) =
  if fuel <= 0
  then None
  else
    let recurse = index_of ~affines ~defs ~invariant ~fuel:(fuel - 1) in
    match expr with
    | Cconst_int (n, _) when in_range n -> Some { zero_index with offset = n }
    | Cvar v -> (
      match V.Map.find_opt v affines with
      | Some (affine : affine) ->
        normalise_index
          { zero_index with
            multiplier = affine.multiplier;
            offset = affine.offset
          }
      | None -> (
        if invariant v
        then Some { zero_index with invariant = Some v; coefficient = 1 }
        else
          match V.Map.find_opt v defs with
          | Some def -> recurse def
          | None -> None))
    | Cop (Caddi, [lhs; rhs], _) -> (
      match recurse lhs, recurse rhs with
      | Some lhs, Some rhs -> add_index lhs rhs
      | (None | Some _), _ -> None)
    | Cop (Csubi, [lhs; Cconst_int (n, _)], _) when in_range n -> (
      match recurse lhs with
      | Some lhs -> add_index lhs { zero_index with offset = -n }
      | None -> None)
    | Cop (Clsl, [inner; Cconst_int (shift, _)], _)
      when shift >= 0 && shift <= 20 -> (
      match recurse inner with
      | Some index -> scale_index (1 lsl shift) index
      | None -> None)
    | Cop (Cmuli, args, _) -> (
      match split_constant args with
      | None -> None
      | Some (inner, n) -> (
        match recurse inner with
        | Some index -> scale_index n index
        | None -> None))
    | _ -> None

(* The [Clet] bindings of [body], excluding variables bound more than once in
   the function. *)
let defs_of_body ~duplicated body =
  let defs = ref V.Map.empty in
  let rec loop expr =
    (match expr with
    | Clet (v, def, _) when not (V.Set.mem (VP.var v) duplicated) ->
      defs := V.Map.add (VP.var v) def !defs
    | _ -> ());
    iter_subexpressions loop expr
  in
  loop body;
  !defs

(* {2 The rewrite} *)

let rec log2 n acc =
  if n = 1
  then Some acc
  else if n <= 0 || n land 1 = 1
  then None
  else log2 (n lsr 1) (acc + 1)

let scale_by n expr dbg =
  if n = 1
  then expr
  else
    match log2 n 0 with
    | Some shift -> Cop (Clsl, [expr; Cconst_int (shift, dbg)], dbg)
    | None -> Cop (Cmuli, [expr; Cconst_int (n, dbg)], dbg)

(* The scales an x86 addressing mode can apply to its index register. A wider
   step would need a shift inside the loop, which is what this pass is trying to
   remove. *)
let is_addressing_scale n = n = 0 || n = 1 || n = 2 || n = 4 || n = 8

let same_base (root, invariant, bytes) (root', invariant', bytes') =
  V.same root root' && V.same invariant invariant' && bytes = bytes'

(* Rewrite the load and store addresses of [body] against [counter]. Returns the
   bindings to hoist and the new body. *)
let hoist_bases ~affines ~defs ~invariant ~counter ~dbg body =
  let bases = ref [] in
  let base_var key =
    match List.find_opt (fun (key', _) -> same_base key key') !bases with
    | Some (_, var) -> var
    | None ->
      let var = V.create_local "ip_base" in
      bases := (key, var) :: !bases;
      var
  in
  let rewrite_address dbg expr =
    match address_of expr with
    | None -> expr
    | Some { root; scale; index; disp } -> (
      if not (invariant root)
      then expr
      else
        let index =
          match index with
          | None -> Some zero_index
          | Some index -> index_of ~affines ~defs ~invariant ~fuel:24 index
        in
        match index with
        | None -> expr
        | Some { invariant = inv; coefficient; multiplier; offset } ->
          let bytes = scale * coefficient in
          let step = scale * multiplier in
          let displacement = (scale * offset) + disp in
          if
            (not (in_range bytes))
            || (not (in_range step))
            || (not (in_range displacement))
            || not (is_addressing_scale step)
          then expr
          else
            let base =
              match inv with
              | Some inv when bytes <> 0 -> Cvar (base_var (root, inv, bytes))
              | Some _ | None -> Cvar root
            in
            let base =
              if step = 0
              then base
              else Cop (Cadda, [base; scale_by step (Cvar counter) dbg], dbg)
            in
            if displacement = 0
            then base
            else Cop (Cadda, [base; Cconst_int (displacement, dbg)], dbg))
  in
  let rec loop expr =
    match expr with
    | Cop ((Cload _ as op), [address], dbg) ->
      Cop (op, [rewrite_address dbg (loop address)], dbg)
    | Cop ((Cstore _ as op), [address; value], dbg) ->
      Cop (op, [rewrite_address dbg (loop address); loop value], dbg)
    | _ -> map_subexpressions loop expr
  in
  let body = loop body in
  let bindings =
    List.map
      (fun ((root, inv, bytes), var) ->
        var, Cop (Cadda, [Cvar root; scale_by bytes (Cvar inv) dbg], dbg))
      !bases
  in
  bindings, body

(* Form interior pointers for the handler named [label] of the [Ccatch
   Recursive] node [expr]. Returns the bindings to wrap around the node, and the
   node. Raises [Not_applicable] if nothing can or should be done, in which case
   the caller keeps the original node. *)
let interior_pointers ~duplicated ~label ~expr =
  let flag, handlers, body =
    match expr with
    | Ccatch (flag, handlers, body) -> flag, handlers, body
    | _ -> raise Not_applicable
  in
  let handler =
    match List.find_opt (is_label label) handlers with
    | Some handler -> handler
    | None -> raise Not_applicable
  in
  (* The derived pointers live across the whole node, so the whole node has to
     be free of safepoints, not just the handler being rewritten. *)
  if not (is_gc_free expr) then raise Not_applicable;
  let bound_inside = bound_variables V.Set.empty expr in
  let invariant v = not (V.Set.mem v bound_inside) in
  let defs = defs_of_body ~duplicated handler.body in
  let dbg = handler.dbg in
  let rec try_counter params =
    match params with
    | [] -> raise Not_applicable
    | (param, machtype) :: params ->
      let counter = VP.var param in
      let affines =
        if is_int_machtype machtype
        then affines_of_body ~duplicated ~counter handler.body
        else V.Map.empty
      in
      if V.Map.is_empty affines
      then try_counter params
      else
        let bindings, rewritten =
          hoist_bases ~affines ~defs ~invariant ~counter ~dbg handler.body
        in
        (* Nothing was hoisted: the rewrite would at best shuffle a constant
           between two equivalent addressing modes, so leave the loop to the
           strength reduction instead. *)
        if List.compare_length_with bindings 0 = 0
        then try_counter params
        else bindings, rewritten
  in
  let bindings, rewritten = try_counter handler.params in
  let handlers =
    List.map
      (fun (handler : static_handler) ->
        if is_label label handler
        then { handler with body = rewritten }
        else handler)
      handlers
  in
  bindings, Ccatch (flag, handlers, body)

(* {1 Driver} *)

let rec rewrite ~duplicated ~strength_reduction ~form_interior_pointers int_vars
    expr =
  let rewrite =
    rewrite ~duplicated ~strength_reduction ~form_interior_pointers
  in
  match expr with
  | Clet (v, def, body) ->
    let def = rewrite int_vars def in
    let int_vars =
      if is_int_expression int_vars def
      then add_int_var ~duplicated int_vars (VP.var v)
      else int_vars
    in
    Clet (v, def, rewrite int_vars body)
  | Ccatch (flag, handlers, body) -> (
    (* Bottom-up, so that an inner loop is already in its final form when the
       loop enclosing it is examined. *)
    let handlers =
      List.map
        (fun (handler : static_handler) ->
          let int_vars = add_int_params ~duplicated int_vars handler.params in
          { handler with body = rewrite int_vars handler.body })
        handlers
    in
    let expr = Ccatch (flag, handlers, rewrite int_vars body) in
    match flag with
    | Normal | Exn_handler -> expr
    | Recursive ->
      (* Interior pointers first. Where they fire they subsume the strength
         reduction: a fixed base plus the loop counter is strictly better than a
         running index, and the sum [b + i] the strength reduction looks for is
         gone from the addresses it rewrote, so the two cannot both fire on one
         access and leave the loop carrying both. *)
      let bindings, expr =
        if not form_interior_pointers
        then [], expr
        else
          List.fold_left
            (fun (bindings, expr) (handler : static_handler) ->
              match
                interior_pointers ~duplicated ~label:handler.label ~expr
              with
              | new_bindings, expr -> new_bindings @ bindings, expr
              | exception Not_applicable -> bindings, expr)
            ([], expr) handlers
      in
      let expr =
        if not strength_reduction
        then expr
        else
          List.fold_left
            (fun expr (handler : static_handler) ->
              match reduce ~duplicated ~int_vars ~label:handler.label ~expr with
              | expr -> expr
              | exception Not_applicable -> expr)
            expr handlers
      in
      List.fold_left
        (fun expr (var, def) -> Clet (VP.create var, def, expr))
        expr bindings)
  | _ -> map_subexpressions (rewrite int_vars) expr

(* Interior pointers are only correct where no collection can happen, and a loop
   only escapes the back-edge poll of [Cfg_polling] when polling is disabled for
   the whole unit or the function is annotated [@poll error], in which case any
   remaining polling point is a compile error. Deciding it here rather than
   trusting the backend keeps the failure mode "the pass declines" instead of
   the backend's "bad GC root", which names no loop and no source location. *)
let polls_are_impossible (fundecl : fundecl) =
  (not Config.poll_insertion)
  || !Oxcaml_flags.disable_poll_insertion
  ||
  match fundecl.fun_poll with
  | Lambda.Error_poll -> true
  | Lambda.Default_poll -> false

let fundecl (fundecl : fundecl) =
  let strength_reduction = !Oxcaml_flags.cmm_strength_reduction in
  let form_interior_pointers =
    !Oxcaml_flags.cmm_interior_pointers && polls_are_impossible fundecl
  in
  if not (strength_reduction || form_interior_pointers)
  then fundecl
  else
    let params = List.map (fun (param, _) -> VP.var param) fundecl.fun_args in
    let duplicated = duplicate_binders ~params fundecl.fun_body in
    let int_vars = add_int_params ~duplicated V.Set.empty fundecl.fun_args in
    { fundecl with
      fun_body =
        rewrite ~duplicated ~strength_reduction ~form_interior_pointers int_vars
          fundecl.fun_body
    }
