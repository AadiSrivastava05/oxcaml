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

(* How many times each variable is read in [expr]. *)
let occurrence_counts expr =
  let counts = ref V.Map.empty in
  let rec loop expr =
    (match expr with
    | Cvar v ->
      counts
        := V.Map.update v
             (function None -> Some 1 | Some n -> Some (n + 1))
             !counts
    | _ -> ());
    iter_subexpressions loop expr
  in
  loop expr;
  !counts

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
  (* An external call that cannot allocate records no frame and cannot run the
     collector: a builtin is selected as an instruction in place of the call,
     and any other is a plain C call with no GC interaction (the [noalloc]
     contract). A SIMD loop is made of builtins; [exp] and friends are the
     rest. *)
  | Cextcall { alloc; _ } -> alloc
  | Capply _ | Calloc _ | Cpoll | Cprobe _ | Cbeginregion | Cendregion
  | Catomic _ | Cdivi _ | Cmodi _ ->
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

(* Does [expr] contain a loop that will still have a poll on its back edge?
   [is_gc_free] does not ask, because without polling a back edge is not a
   safepoint. With polling on, every loop keeps its poll unless it is a counted
   loop, and a derived pointer carried by an enclosing loop would be live across
   that poll, which [Emit] rejects as a bad GC root. *)
let rec contains_polled_loop expr =
  match expr with
  | Ccatch (Recursive, handlers, _)
    when List.exists
           (fun (handler : static_handler) -> not handler.is_bounded)
           handlers ->
    true
  | _ ->
    let found = ref false in
    iter_subexpressions
      (fun sub -> if not !found then found := contains_polled_loop sub)
      expr;
    !found

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

(* {1 Induction variables with a loop-invariant stride}

   [reduce] carries [invariant + m * counter + c] for an integer constant [m]. A
   loop over the rows of a matrix needs more than that: the base of row [r] is
   [r * columns], which steps by the loop-invariant [columns] rather than by a
   constant, so [reduce] cannot express it and the multiplication is rebuilt on
   every row. The same shape sits one level above every interior pointer
   [hoist_bases] forms, since the pointer to a row is the array plus a multiple
   of [columns]: the inner loop walks a row by an addressing mode, and then the
   outer loop recomputes all of the row pointers from scratch.

   This carries any [Clet]-bound value of the form [start + stride * counter]
   whose [stride] and [start] are built only from constants and from variables
   bound outside the whole [Ccatch]. Such a value then steps by a single
   addition of a quantity computed once before the loop. Constant strides are
   deliberately left to [reduce], which also knows when carrying one pays for
   the register it costs.

   Two things restrict it to loops that cannot reach a collection. A value
   derived from a pointer is a pointer the collector cannot update, exactly as
   for the interior pointers above. And hoisting the stride out of the loop
   reads its operands once instead of once per iteration, which is the same
   computation only if nothing can move them in between. *)

type coeff =
  | Const of int
  | Term of expression

let coeff_expr ~dbg = function
  | Const n -> Cconst_int (n, dbg)
  | Term expr -> expr

(* Constants are kept small for the same reason as in [affine], so that nothing
   computed from them can overflow silently; a larger one is carried as an
   expression and left to the backend. *)
let coeff_of_int ~dbg n =
  if in_range n then Const n else Term (Cconst_int (n, dbg))

let add_coeff ~dbg a b =
  match a, b with
  | Const 0, c | c, Const 0 -> c
  | Const m, Const n -> coeff_of_int ~dbg (m + n)
  | (Const _ | Term _), (Const _ | Term _) ->
    Term (Cop (Caddi, [coeff_expr ~dbg a; coeff_expr ~dbg b], dbg))

let sub_coeff ~dbg a b =
  match a, b with
  | c, Const 0 -> c
  | Const m, Const n -> coeff_of_int ~dbg (m - n)
  | (Const _ | Term _), (Const _ | Term _) ->
    Term (Cop (Csubi, [coeff_expr ~dbg a; coeff_expr ~dbg b], dbg))

let mul_coeff ~dbg a b =
  match a, b with
  | Const 0, _ | _, Const 0 -> Const 0
  | Const 1, c | c, Const 1 -> c
  | Const m, Const n -> coeff_of_int ~dbg (m * n)
  | (Const _ | Term _), (Const _ | Term _) ->
    Term (Cop (Cmuli, [coeff_expr ~dbg a; coeff_expr ~dbg b], dbg))

let shift_coeff ~dbg c n =
  match c with
  | Const 0 -> Const 0
  | Const m when in_range (m lsl n) -> Const (m lsl n)
  | Const _ | Term _ ->
    Term (Cop (Clsl, [coeff_expr ~dbg c; Cconst_int (n, dbg)], dbg))

(* [n * c], preferring the shift the backend would have to find anyway. *)
let scale_coeff ~dbg n c =
  if n >= 1
  then Term (scale_by n (coeff_expr ~dbg c) dbg)
  else mul_coeff ~dbg c (Const n)

(* An expression that cannot change within the loop and can be evaluated before
   it: pure, total, and reading only variables bound outside the whole node.
   [relaxed] drops the requirement that those variables hold integers, which is
   sound only when nothing can move a pointer while the loop runs. *)
let rec invariant_int ~invariant ~int_vars ~relaxed expr =
  match expr with
  | Cconst_int _ | Cconst_natint _ -> true
  | Cvar v -> invariant v && (relaxed || V.Set.mem v int_vars)
  | Cop
      ((Caddi | Csubi | Cmuli | Cand | Cor | Cxor | Clsl | Clsr | Casr), args, _)
    ->
    List.for_all (invariant_int ~invariant ~int_vars ~relaxed) args
  | _ -> false

(* [{ stride; offset; pointer }] denotes [pointer + (stride * counter +
   offset)], with [pointer] absent for an integer. *)
type linear =
  { stride : coeff;
    offset : coeff;
    pointer : expression option
  }

let is_scalar linear =
  match linear.pointer with None -> true | Some _ -> false

let rec linear_of ~dbg ~counter ~invariant ~int_vars ~relaxed ~forms expr =
  let recurse = linear_of ~dbg ~counter ~invariant ~int_vars ~relaxed ~forms in
  let scalar stride offset = Some { stride; offset; pointer = None } in
  match expr with
  | Cvar v when V.same v counter -> scalar (Const 1) (Const 0)
  | Cvar v when V.Map.mem v forms -> V.Map.find_opt v forms
  | _ when invariant_int ~invariant ~int_vars ~relaxed expr ->
    scalar (Const 0) (Term expr)
  | Cop (Caddi, [a; b], _) -> (
    match recurse a, recurse b with
    | Some a, Some b when is_scalar a && is_scalar b ->
      scalar
        (add_coeff ~dbg a.stride b.stride)
        (add_coeff ~dbg a.offset b.offset)
    | (Some _ | None), (Some _ | None) -> None)
  | Cop (Csubi, [a; b], _) -> (
    match recurse a, recurse b with
    | Some a, Some b when is_scalar a && is_scalar b ->
      scalar
        (sub_coeff ~dbg a.stride b.stride)
        (sub_coeff ~dbg a.offset b.offset)
    | (Some _ | None), (Some _ | None) -> None)
  | Cop (Cmuli, [a; b], _) -> (
    (* Linear only when one side does not involve the counter. *)
    match recurse a, recurse b with
    | Some a, Some b when is_scalar a && is_scalar b -> (
      match a.stride, b.stride with
      | Const 0, _ ->
        scalar
          (mul_coeff ~dbg a.offset b.stride)
          (mul_coeff ~dbg a.offset b.offset)
      | _, Const 0 ->
        scalar
          (mul_coeff ~dbg b.offset a.stride)
          (mul_coeff ~dbg b.offset a.offset)
      | (Const _ | Term _), (Const _ | Term _) -> None)
    | (Some _ | None), (Some _ | None) -> None)
  | Cop (Clsl, [a; Cconst_int (n, _)], _) when n >= 0 && n <= 20 -> (
    match recurse a with
    | Some a when is_scalar a ->
      scalar (shift_coeff ~dbg a.stride n) (shift_coeff ~dbg a.offset n)
    | Some _ | None -> None)
  | Cop (Cadda, [a; b], _) -> (
    (* The root of an interior pointer is a variable bound outside the loop; it
       is matched here rather than by [recurse] so that it cannot be mistaken
       for an integer under [relaxed]. *)
    let rooted =
      match a with
      | Cvar p when invariant p -> (
        match recurse b with
        | Some b when is_scalar b -> Some { b with pointer = Some (Cvar p) }
        | Some _ | None -> None)
      | _ -> None
    in
    match rooted with
    | Some _ -> rooted
    | None -> (
      match recurse a, recurse b with
      | Some a, Some b when (not (is_scalar a)) && is_scalar b ->
        Some
          { stride = add_coeff ~dbg a.stride b.stride;
            offset = add_coeff ~dbg a.offset b.offset;
            pointer = a.pointer
          }
      | (Some _ | None), (Some _ | None) -> None))
  | _ -> None

let same_int_op (a : operation) (b : operation) =
  match a, b with
  | Caddi, Caddi
  | Csubi, Csubi
  | Cmuli, Cmuli
  | Cand, Cand
  | Cor, Cor
  | Cxor, Cxor
  | Clsl, Clsl
  | Clsr, Clsr
  | Casr, Casr
  | Cadda, Cadda ->
    true
  | _ -> false

(* Structural equality over the expressions built above: constants, variables
   and the pure integer operations. The row pointers of one loop all advance by
   the same number of bytes, and computing that once is one register rather than
   one per pointer. *)
let rec same_expression a b =
  match a, b with
  | Cconst_int (m, _), Cconst_int (n, _) -> Int.equal m n
  | Cvar u, Cvar v -> V.same u v
  | Cop (op, args, _), Cop (op', args', _) ->
    same_int_op op op'
    && List.compare_lengths args args' = 0
    && List.for_all2 same_expression args args'
  | _ -> false

(* The linear form of every [Clet]-bound variable of [body] that has one,
   following chains of such bindings as [affines_of_body] does. *)
let forms_of_body ~dbg ~duplicated ~counter ~invariant ~int_vars ~relaxed body =
  let forms = ref V.Map.empty in
  let rec loop expr =
    (match expr with
    | Clet (v, def, _) when not (V.Set.mem (VP.var v) duplicated) -> (
      match
        linear_of ~dbg ~counter ~invariant ~int_vars ~relaxed ~forms:!forms def
      with
      | Some linear -> forms := V.Map.add (VP.var v) linear !forms
      | None -> ())
    | _ -> ());
    iter_subexpressions loop expr
  in
  loop body;
  !forms

(* Replace the defining expression of each carried variable by the parameter
   that now holds it. The binding itself stays, so nothing has to be substituted
   and the copy folds away in register allocation; whatever the definition used
   to read becomes unused, and the backend drops it. *)
let replace_defs ~carried expr =
  let rec loop expr =
    match expr with
    | Clet (v, def, body) -> (
      match V.Map.find_opt (VP.var v) carried with
      | Some var -> Clet (v, Cvar var, loop body)
      | None -> Clet (v, loop def, loop body))
    | _ -> map_subexpressions loop expr
  in
  loop expr

(* At most this many values are carried out of one loop, so that the parameters
   added cannot by themselves exhaust the register file. *)
let max_carried = 6

(* Carry the invariant-strided induction variables of the handler named [label]
   of the [Ccatch Recursive] node [expr]. Returns the bindings to wrap around
   the node, and the node. Raises [Not_applicable] if nothing can or should be
   done, in which case the caller keeps the original node. *)
let reduce_invariant_strides ~duplicated ~int_vars ~relaxed ~carry_pointers
    ~label ~expr =
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
  let dbg = handler.dbg in
  let bound_inside = bound_variables V.Set.empty expr in
  let invariant v = not (V.Set.mem v bound_inside) in
  let rec find_counter index params =
    match params with
    | [] -> raise Not_applicable
    | (param, machtype) :: params ->
      let counter = VP.var param in
      let affines =
        if is_int_machtype machtype
        then affines_of_body ~duplicated ~counter handler.body
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
      if eligible
      then index, counter, affines, classified
      else find_counter (index + 1) params
  in
  let index, counter, affines, _classified = find_counter 0 handler.params in
  let forms =
    forms_of_body ~dbg ~duplicated ~counter ~invariant ~int_vars ~relaxed
      handler.body
  in
  let defs = defs_of_body ~duplicated handler.body in
  (* A constant stride is [reduce]'s business, and carrying a value derived from
     a pointer is sound only where no collection can happen. *)
  let worth_carrying _ linear =
    match linear.stride with
    | Const _ -> false
    | Term _ -> (
      match linear.pointer with None -> true | Some _ -> carry_pointers)
  in
  let candidates =
    V.Map.filter
      (fun v linear -> V.Map.mem v defs && worth_carrying v linear)
      forms
  in
  (* Carrying a value makes whatever it was computed from dead, and the row
     index a row pointer is built from is exactly such a value. Drop every
     candidate that nothing reads once the others are carried, rather than
     spending a register on a value the backend is about to delete. *)
  let rec prune candidates =
    let probe = V.Map.mapi (fun _ _ -> V.create_local "ivs_probe") candidates in
    let rewritten = replace_defs ~carried:probe handler.body in
    let kept = V.Map.filter (fun v _ -> occurs v rewritten) candidates in
    if V.Map.cardinal kept = V.Map.cardinal candidates then kept else prune kept
  in
  let candidates = prune candidates in
  if V.Map.is_empty candidates then raise Not_applicable;
  if V.Map.cardinal candidates > max_carried then raise Not_applicable;
  let ordered = V.Map.bindings candidates in
  let carried = List.map (fun (v, _) -> v, V.create_local "ivs") ordered in
  let lookup table v =
    match List.find_opt (fun (v', _) -> V.same v v') table with
    | Some (_, var) -> var
    | None -> raise Not_applicable
  in
  let handler_body =
    replace_defs
      ~carried:
        (List.fold_left
           (fun map (v, _) -> V.Map.add v (lookup carried v) map)
           V.Map.empty ordered)
      handler.body
  in
  (* The step is the only thing that has to survive into the loop, so it is the
     only thing bound before it; a fresh start is built where it is used, which
     is an edge that runs once. *)
  let steps = ref [] in
  let step_var def =
    match List.find_opt (fun (def', _) -> same_expression def def') !steps with
    | Some (_, var) -> var
    | None ->
      let var = V.create_local "ivs_step" in
      steps := (def, var) :: !steps;
      var
  in
  let extra args =
    let classified = classify_exit_arg ~affines (nth_arg args index) in
    List.map
      (fun (v, linear) ->
        let var = lookup carried v in
        match classified with
        | Some (Step n) ->
          let add =
            match linear.pointer with None -> Caddi | Some _ -> Cadda
          in
          let step =
            step_var (coeff_expr ~dbg (scale_coeff ~dbg n linear.stride))
          in
          Cop (add, [Cvar var; Cvar step], dbg)
        | Some (Fresh start) -> (
          let scaled =
            match start with
            | Cconst_int (0, _) -> Const 0
            | Cconst_int (1, _) -> linear.stride
            | _ -> mul_coeff ~dbg linear.stride (Term start)
          in
          let value = coeff_expr ~dbg (add_coeff ~dbg scaled linear.offset) in
          match linear.pointer with
          | None -> value
          | Some pointer -> Cop (Cadda, [pointer; value], dbg))
        | None -> raise Not_applicable)
      ordered
  in
  let extra_params =
    List.map
      (fun (v, linear) ->
        ( VP.create (lookup carried v),
          match linear.pointer with None -> typ_int | Some _ -> typ_addr ))
      ordered
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
  let expr = Ccatch (flag, handlers, add_exit_args ~label ~extra body) in
  List.map (fun (def, var) -> var, def) !steps, expr

(* {1 Pointers into rows of vectors}

   A 128-bit access to an unboxed array, [Float64x2.Array.unsafe_get a ~idx],
   reaches [Cmm] with its tagged index untagged inside the address:

   {v (+a a (<< (>>s idx 1) 3)) v}

   [idx] is an affine function of the loop counter like any other index, but the
   arithmetic shift hides it from [index_of], so neither the interior pointers
   nor the strength reduction see through it, and every access of a SIMD loop
   pays its own untag and scale.

   The shift is still exact where it matters. For integers [y] and [q],
   [(y + 2q) >>s 1 = (y >>s 1) + q] whenever [y + 2q] does not overflow, and an
   index that addresses memory has not. Writing the index as [y + 2q], with [y]
   the part that varies plus the index's low bit, every access to one array at
   the same [y] is one pointer

   {v p = a + ((y >>s 1) << s) v}

   plus the constant [q << s], which the addressing mode absorbs. Where every
   step [n] of the counter makes [m * n] even, [y] steps by [m * n] and [p] by
   the constant [(m * n / 2) << s], so [p] is carried as a loop parameter: built
   from scratch on each edge that enters the loop, advanced by one addition on
   each back edge. Like any carried derived pointer it is representable only
   where no safepoint can be reached while it is live. *)

let max_vector_pointers = 6

type vector_key =
  { vroot : V.t;
    vinv : V.t option;
    vcoefficient : int;
    vmultiplier : int;
    low_bit : int;
    shift : int
  }

let same_vector_key a b =
  V.same a.vroot b.vroot
  && (match a.vinv, b.vinv with
     | None, None -> true
     | Some u, Some v -> V.same u v
     | (None | Some _), _ -> false)
  && a.vcoefficient = b.vcoefficient
  && a.vmultiplier = b.vmultiplier
  && a.low_bit = b.low_bit && a.shift = b.shift

(* [(+a root (<< (>>s index 1) shift))] *)
let vector_address (expr : expression) =
  match expr with
  | Cop
      ( Cadda,
        [ Cvar root;
          Cop
            ( Clsl,
              [ Cop (Casr, [index; Cconst_int (1, _)], _);
                Cconst_int (shift, _) ],
              _ ) ],
        _ )
    when shift >= 0 && shift <= 3 ->
    Some (root, index, shift)
  | _ -> None

(* Carry vector-row pointers for the handler named [label] of the [Ccatch
   Recursive] node [expr]. Returns the new node. Raises [Not_applicable] if
   nothing can be done, in which case the caller keeps the original node. *)
let vector_pointers ~duplicated ~label ~expr =
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
  let dbg = handler.dbg in
  let bound_inside = bound_variables V.Set.empty expr in
  let invariant v = not (V.Set.mem v bound_inside) in
  let defs = defs_of_body ~duplicated handler.body in
  (* Each integer parameter is tried as the counter, as in
     [reduce_invariant_strides]; the first that addresses a vector row wins. *)
  let attempt index (param, machtype) =
    if not (is_int_machtype machtype)
    then None
    else
      let counter = VP.var param in
      let affines = affines_of_body ~duplicated ~counter handler.body in
      if V.Map.is_empty affines
      then None
      else
        let classified =
          List.map
            (fun args -> classify_exit_arg ~affines (nth_arg args index))
            exits
        in
        let steps =
          List.filter_map
            (function Some (Step n) -> Some n | Some (Fresh _) | None -> None)
            classified
        in
        if
          (not (List.for_all Option.is_some classified))
          || List.compare_length_with steps 0 = 0
        then None
        else
          let pointers = ref [] in
          let pointer_for key =
            match
              List.find_opt (fun (key', _) -> same_vector_key key key') !pointers
            with
            | Some (_, var) -> Some var
            | None ->
              if List.compare_length_with !pointers max_vector_pointers >= 0
              then None
              else
                let var = V.create_local "vp" in
                pointers := (key, var) :: !pointers;
                Some var
          in
          let rewrite_address dbg expr =
            match vector_address expr with
            | None -> expr
            | Some (root, index, shift) -> (
              if not (invariant root)
              then expr
              else
                match index_of ~affines ~defs ~invariant ~fuel:24 index with
                | None -> expr
                | Some { invariant = inv; coefficient; multiplier; offset } -> (
                  let exact =
                    multiplier <> 0
                    && List.for_all
                         (fun n ->
                           in_range (multiplier * n)
                           && (multiplier * n) land 1 = 0)
                         steps
                  in
                  let displacement = (offset asr 1) lsl shift in
                  if not (exact && in_range displacement)
                  then expr
                  else
                    let key =
                      { vroot = root;
                        vinv = inv;
                        vcoefficient = coefficient;
                        vmultiplier = multiplier;
                        low_bit = offset land 1;
                        shift
                      }
                    in
                    match pointer_for key with
                    | None -> expr
                    | Some var ->
                      if displacement = 0
                      then Cvar var
                      else
                        Cop
                          ( Cadda,
                            [Cvar var; Cconst_int (displacement, dbg)],
                            dbg )))
          in
          let rec loop expr =
            match expr with
            | Cop ((Cload _ as op), [address], dbg) ->
              Cop (op, [rewrite_address dbg (loop address)], dbg)
            | Cop ((Cstore _ as op), [address; value], dbg) ->
              Cop (op, [rewrite_address dbg (loop address); loop value], dbg)
            | _ -> map_subexpressions loop expr
          in
          let handler_body = loop handler.body in
          match !pointers with
          | [] -> None
          | _ :: _ -> Some (index, affines, List.rev !pointers, handler_body)
  in
  let rec first index params =
    match params with
    | [] -> raise Not_applicable
    | param :: params -> (
      match attempt index param with
      | Some found -> found
      | None -> first (index + 1) params)
  in
  let index, affines, pointers, handler_body = first 0 handler.params in
  (* [root + (((coefficient * inv + multiplier * start + low_bit) >>s 1) <<
     shift)], the pointer for a counter equal to [start]. *)
  let start_pointer key start =
    let varying =
      if key.vmultiplier = 1
      then start
      else Cop (Cmuli, [start; Cconst_int (key.vmultiplier, dbg)], dbg)
    in
    let with_inv =
      match key.vinv with
      | Some inv when key.vcoefficient <> 0 ->
        Cop (Caddi, [scale_by key.vcoefficient (Cvar inv) dbg; varying], dbg)
      | Some _ | None -> varying
    in
    let y =
      if key.low_bit = 0
      then with_inv
      else Cop (Caddi, [with_inv; Cconst_int (key.low_bit, dbg)], dbg)
    in
    let untagged = Cop (Casr, [y; Cconst_int (1, dbg)], dbg) in
    Cop (Cadda, [Cvar key.vroot; scale_by (1 lsl key.shift) untagged dbg], dbg)
  in
  let extra args =
    match classify_exit_arg ~affines (nth_arg args index) with
    | Some (Step n) ->
      List.map
        (fun (key, var) ->
          let bytes = ((key.vmultiplier * n) asr 1) lsl key.shift in
          if bytes = 0
          then Cvar var
          else Cop (Cadda, [Cvar var; Cconst_int (bytes, dbg)], dbg))
        pointers
    | Some (Fresh start) ->
      List.map (fun (key, _) -> start_pointer key start) pointers
    | None -> raise Not_applicable
  in
  let extra_params =
    List.map (fun (_, var) -> VP.create var, typ_addr) pointers
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

(* {1 Loop-invariant code motion}

   flambda2 has no loop-invariant code motion, so a computation that depends on
   nothing the loop changes is still evaluated on every iteration. The row loop
   of a matrix product recomputes the inner loop's trip count from the column
   count every time round: five instructions in front of an inner loop of
   thirteen, none of which depend on the row.

   A [Clet] in a loop body whose defining expression reads only variables bound
   outside the whole [Ccatch] is bound before the loop instead. Restricted to
   the pure, total integer operations, because moving a binding out from under a
   conditional evaluates it on a path that did not reach it, and only a total
   operation may be evaluated there. The restriction on reading a variable not
   known to hold an integer is the one above, for the same reason: reading it
   once instead of once per iteration is the same computation only if nothing
   can move it in between.

   Chains are followed, since a variable already hoisted is bound outside by the
   time the next one is considered. *)

(* At most this many bindings leave one loop. Each one trades an evaluation per
   iteration for a live range across the whole loop, which is only a win while
   there are registers left to hold them. *)
let max_hoisted = 4

(* What it costs to recompute a definition once. Hoisting pays that cost once
   instead of every iteration, in exchange for one value live across the loop.
   An add or a shift is not worth a register: the addressing modes absorb those
   for free, and spilling one value to save one [lea] is a loss. A multiply is,
   at three to four cycles and a port the loop's arithmetic also wants. *)
let rec recompute_cost expr =
  let args_cost args = List.fold_left (fun n a -> n + recompute_cost a) 0 args in
  match expr with
  | Cconst_int _ | Cconst_natint _ | Cvar _ -> 0
  | Cop (Cmuli, args, _) -> 3 + args_cost args
  | Cop ((Caddi | Csubi | Cand | Cor | Cxor | Clsl | Clsr | Casr), args, _) ->
    1 + args_cost args
  | _ -> 1

(* A definition this expensive earns its register even when no operand dies. *)
let min_cost_under_pressure = 3

(* How many such bindings may leave one loop, and how many values that loop may
   already carry before none may. The loop already ties up one register per
   carried value; below this there are enough left that one more live range
   does not force a spill, and above it the measurement that produced this pass
   says hoisting loses. *)
let max_pressure_hoists = 2

let max_carried_under_pressure = 6

let hoist_invariants ~duplicated ~int_vars ~relaxed ~counts ~expr =
  let flag, handlers, body =
    match expr with
    | Ccatch (flag, handlers, body) -> flag, handlers, body
    | _ -> raise Not_applicable
  in
  let bound_inside = bound_variables V.Set.empty expr in
  let hoisted = ref [] in
  let already = ref V.Set.empty in
  let invariant v = (not (V.Set.mem v bound_inside)) || V.Set.mem v !already in
  (* A variable or a constant is already as cheap as it can be, and hoisting one
     only lengthens its live range. *)
  let worth def =
    match def with
    | Cvar _ | Cconst_int _ | Cconst_natint _ -> false
    | _ -> true
  in
  (* Hoisting moves an evaluation out of the loop and a value into it, so it
     only pays where the operands die as a result. A variable this definition
     reads that is read anywhere else stays live across the loop regardless, and
     then the binding costs a register instead of saving one -- which on a loop
     already at the limit means a reload per iteration in place of a computation
     per iteration of the loop above it. This is the register-neutrality
     condition [reduce] applies to its invariant, for the same reason. *)
  let operands_die def =
    V.Map.for_all
      (fun v n ->
        match V.Map.find_opt v counts with
        | Some total -> Int.equal total n
        | None -> false)
      (occurrence_counts def)
  in
  (* Values the loop already holds in registers across its back edge. *)
  let carried =
    List.fold_left
      (fun n (handler : static_handler) -> n + List.length handler.params)
      0 handlers
  in
  let pressure_budget =
    ref
      (if carried <= max_carried_under_pressure then max_pressure_hoists else 0)
  in
  (* Register-neutral hoists are always taken. One that adds a live range is
     taken only while there is budget for it and the computation it removes is
     dear enough to pay for the register -- which is what lets an invariant
     multiply leave a loop whose operands are all live elsewhere anyway. *)
  let affordable def =
    operands_die def
    || recompute_cost def >= min_cost_under_pressure
       && !pressure_budget > 0
       && (decr pressure_budget;
           true)
  in
  let hoistable v def =
    (not (V.Set.mem v duplicated))
    && List.compare_length_with !hoisted max_hoisted < 0
    && worth def
    && invariant_int ~invariant ~int_vars ~relaxed def
    && affordable def
  in
  let rec loop expr =
    match expr with
    | Clet (v, def, inner) when hoistable (VP.var v) def ->
      hoisted := (VP.var v, def) :: !hoisted;
      already := V.Set.add (VP.var v) !already;
      loop inner
    | _ -> map_subexpressions loop expr
  in
  let handlers =
    List.map
      (fun (handler : static_handler) ->
        { handler with body = loop handler.body })
      handlers
  in
  match !hoisted with
  | [] -> raise Not_applicable
  (* Accumulated by prepending, so the first one hoisted is last in the list and
     the driver, folding left, binds it outermost -- which is what the ones
     after it may refer to. *)
  | _ :: _ -> !hoisted, Ccatch (flag, handlers, body)

(* {1 Counted loops}

   The poll on a loop's back edge is there so that the loop cannot keep a
   domain from a stop-the-world collection forever. Removing it changes nothing
   the loop computes; it only matters if the loop never ends. So a loop that is
   proved to end needs no back-edge poll: one poll on its exits gives the same
   guarantee, and its body is then free to carry derived pointers.

   The proof. The loop has one integer parameter [c] (the counter) that every
   back edge passes as [c + n], for one constant [n], and one test [x R B] that
   every back edge is reached through, where [x = m * c + k] (constants [m],
   [k]) and [B] is a pure expression of variables bound outside the loop. All
   arithmetic is on 64-bit words modulo 2^64, and [m * (c + n) + k = x + m * n]
   holds exactly in that ring, so from one iteration to the next [x] changes by
   exactly [d = m * n], whatever wraps. [B] is the same on every iteration.

   - [x < B], [d > 0], given [B <= max - d + 1]: an iteration that continues has
     [x < B], so [x + d <= B - 1 + d <= max] does not wrap; [x] strictly rises
     while the loop continues, and the loop ends within [(B - x0) / d + 1]
     iterations. [x <= B] needs [B <= max - d]; [x > B] and [x >= B] with
     [d < 0] are the mirror images at [min].
   - [x <> B], [|d|] a power of two, given [x0 <= B] and [(B - x0) land (d - 1)
     = 0] (for [d > 0]; mirrored for [d < 0]): [x] stays a multiple of [d] below
     [B], so [x + d <= B] does not wrap, and [x] reaches [B] exactly after
     [(B - x0) / d] iterations. The low bits of [B - x0] are exact even when
     the subtraction wraps, because [d] divides 2^64.
   - [x = B]: [x] changes by [d <> 0] each iteration, so the test fails on the
     second iteration at the latest.

   Without the side conditions none of this holds: [i < n] stepping by 16 never
   ends if [n] is within 15 of [max], and [i <> n] never ends if [n - i] is odd
   and the step is 2. Where the side condition follows from the range of [B]
   it is decided here; otherwise it is tested once on entry, and the loop is
   compiled twice: the poll-free version, and an exact copy of the original,
   polls included, for when the test fails.

   Only the outermost counted loop of a nest gets the exit poll; one inside it
   is covered by it, and a poll between two counted loops would stop the outer
   one from carrying pointers across the inner. *)

let counted_loops_enabled = ref false

let found_counted = ref false

(* The [Clet] definitions of the whole function, for [range]. *)
let function_defs = ref V.Map.empty

let word_max = Nativeint.max_int

let word_min = Nativeint.min_int

(* [a + b] on the host, or [None] if it overflows. *)
let add_exact a b =
  let sum = Nativeint.add a b in
  if
    Bool.equal (Nativeint.compare a 0n >= 0) (Nativeint.compare b 0n >= 0)
    && not
         (Bool.equal (Nativeint.compare sum 0n >= 0)
            (Nativeint.compare a 0n >= 0))
  then None
  else Some sum

let neg_exact a =
  if Nativeint.equal a word_min then None else Some (Nativeint.neg a)

(* Bounds [(lo, hi)] that the signed value of [expr] provably lies within, if
   any are known. Only what is exact on 64-bit words is used. *)
let rec range ~fuel (expr : expression) =
  if fuel <= 0
  then None
  else
    let recurse = range ~fuel:(fuel - 1) in
    match expr with
    | Cconst_int (n, _) -> Some (Nativeint.of_int n, Nativeint.of_int n)
    | Cconst_natint (n, _) -> Some (n, n)
    | Cvar v -> (
      match V.Map.find_opt v !function_defs with
      | Some def -> recurse def
      | None -> None)
    | Cop (Casr, [e; Cconst_int (k, _)], _) when k >= 1 && k <= 63 ->
      let lo, hi =
        match recurse e with Some r -> r | None -> word_min, word_max
      in
      Some (Nativeint.shift_right lo k, Nativeint.shift_right hi k)
    | Cop (Clsr, [_; Cconst_int (k, _)], _) when k >= 1 && k <= 63 ->
      Some (0n, Nativeint.shift_right_logical (-1n) k)
    | Cop (Cand, [_; Cconst_int (c, _)], _) when c >= 0 ->
      Some (0n, Nativeint.of_int c)
    | Cop (Cand, [Cconst_int (c, _); _], _) when c >= 0 ->
      Some (0n, Nativeint.of_int c)
    | Cop (Caddi, [a; b], _) -> (
      match recurse a, recurse b with
      | Some (lo1, hi1), Some (lo2, hi2) -> (
        match add_exact lo1 lo2, add_exact hi1 hi2 with
        | Some lo, Some hi -> Some (lo, hi)
        | (Some _ | None), (Some _ | None) -> None)
      | (Some _ | None), (Some _ | None) -> None)
    | Cop (Csubi, [a; b], _) -> (
      match recurse a, recurse b with
      | Some (lo1, hi1), Some (lo2, hi2) -> (
        match neg_exact hi2, neg_exact lo2 with
        | Some nhi2, Some nlo2 -> (
          match add_exact lo1 nhi2, add_exact hi1 nlo2 with
          | Some lo, Some hi -> Some (lo, hi)
          | (Some _ | None), (Some _ | None) -> None)
        | (Some _ | None), (Some _ | None) -> None)
      | (Some _ | None), (Some _ | None) -> None)
    | _ -> None

(* The test that bounds a counted loop: [x continue_when bound] holds on every
   iteration that takes a back edge, with [x = affine (counter)] changing by
   [step] per iteration. *)
type guard =
  { index : int;
    affine : affine;
    continue_when : integer_comparison;
    bound : expression;
    step : int
  }

type precondition =
  | Always
  | Never
  | Check of
      { check : expression -> expression;
            (** Given the counter's value on entry, an expression that is
                non-zero iff the loop is proved to end. *)
        uses_start : bool
            (** Whether [check] reads that value; one that does not depends only
                on values fixed for the whole loop. *)
      }

let is_power_of_two n = n > 0 && n land (n - 1) = 0

let precondition ~dbg guard =
  let d = guard.step in
  (* [B <= max] and [B >= min] hold of every word. *)
  let at_most limit =
    if Nativeint.equal limit word_max
    then Always
    else
      match range ~fuel:16 guard.bound with
      | Some (_, hi) when Nativeint.compare hi limit <= 0 -> Always
      | Some (lo, _) when Nativeint.compare lo limit > 0 -> Never
      | Some _ | None ->
        Check
          { check =
              (fun _ ->
                Cop (Ccmpi Cle, [guard.bound; Cconst_natint (limit, dbg)], dbg));
            uses_start = false
          }
  in
  let at_least limit =
    if Nativeint.equal limit word_min
    then Always
    else
      match range ~fuel:16 guard.bound with
      | Some (lo, _) when Nativeint.compare lo limit >= 0 -> Always
      | Some (_, hi) when Nativeint.compare hi limit < 0 -> Never
      | Some _ | None ->
        Check
          { check =
              (fun _ ->
                Cop (Ccmpi Cge, [guard.bound; Cconst_natint (limit, dbg)], dbg));
            uses_start = false
          }
  in
  let dn = Nativeint.of_int d in
  match guard.continue_when with
  | Ceq -> Always
  | Clt when d > 0 -> at_most (Nativeint.add (Nativeint.sub word_max dn) 1n)
  | Cle when d > 0 -> at_most (Nativeint.sub word_max dn)
  | Cgt when d < 0 -> at_least (Nativeint.sub (Nativeint.sub word_min dn) 1n)
  | Cge when d < 0 -> at_least (Nativeint.sub word_min dn)
  | Cne when is_power_of_two (abs d) ->
    Check
      { uses_start = true;
        check =
      (fun start ->
        let x0 = apply_affine guard.affine start dbg in
        let before, distance =
          if d > 0
          then
            ( Cop (Ccmpi Cle, [x0; guard.bound], dbg),
              Cop (Csubi, [guard.bound; x0], dbg) )
          else
            ( Cop (Ccmpi Cge, [x0; guard.bound], dbg),
              Cop (Csubi, [x0; guard.bound], dbg) )
        in
        if abs d = 1
        then before
        else
          Cop
            ( Cand,
              [ before;
                Cop
                  ( Ccmpi Ceq,
                    [ Cop (Cand, [distance; Cconst_int (abs d - 1, dbg)], dbg);
                      Cconst_int (0, dbg) ],
                    dbg ) ],
              dbg ))
      }
  | Clt | Cle | Cgt | Cge | Cne | Cult | Cugt | Cule | Cuge -> Never

let same_guard ((a1 : affine), c1, b1) ((a2 : affine), c2, b2) =
  a1.multiplier = a2.multiplier
  && a1.offset = a2.offset
  && Stdlib.( = ) c1 c2
  && same_expression b1 b2

(* The guard of the loop [handler] of [expr], if it is a counted loop. *)
let counted_guard ~duplicated ~int_vars ~expr (handler : static_handler) =
  let label = handler.label in
  let bound_inside = bound_variables V.Set.empty expr in
  let invariant v = not (V.Set.mem v bound_inside) in
  let back_edges =
    try collect_exit_args ~label ~roots:[handler.body]
    with Not_applicable -> []
  in
  let attempt index (param, machtype) =
    if
      (not (is_int_machtype machtype))
      || List.compare_length_with back_edges 0 = 0
    then None
    else
      let counter = VP.var param in
      let affines = affines_of_body ~duplicated ~counter handler.body in
      let step_of args =
        match List.nth_opt args index with
        | None -> None
        | Some arg -> (
          match classify_exit_arg ~affines arg with
          | Some (Step n) when n <> 0 -> Some n
          | Some (Step _ | Fresh _) | None -> None)
      in
      match List.map step_of back_edges with
      | Some n :: rest
        when List.for_all
               (function Some n' -> n' = n | None -> false)
               rest ->
        let bound e = invariant_int ~invariant ~int_vars ~relaxed:true e in
        (* [cond] as [x cmp bound] with [x] the affine side, if it is one. *)
        let classify cond =
          match cond with
          | Cop (Ccmpi ((Ceq | Cne | Clt | Cgt | Cle | Cge) as cmp), [a; b], _)
            -> (
            match affine_of ~affines a, affine_of ~affines b with
            | Some affine, None when affine.multiplier <> 0 && bound b ->
              Some (affine, cmp, b)
            | None, Some affine when affine.multiplier <> 0 && bound a ->
              Some (affine, swap_integer_comparison cmp, a)
            | (Some _ | None), (Some _ | None) -> None)
          | _ -> None
        in
        (* For each back edge, the tests it is reached through, each as the
           relation that holds when the back edge is taken. *)
        let per_edge = ref [] in
        let rec walk active expr =
          match expr with
          | Cexit (Lbl l, args, _) when Static_label.equal l label ->
            per_edge := active :: !per_edge;
            List.iter (walk active) args
          | Cifthenelse (cond, _, if_true, _, if_false, _) -> (
            walk active cond;
            match classify cond with
            | Some (affine, cmp, b) ->
              walk ((affine, cmp, b) :: active) if_true;
              walk ((affine, negate_integer_comparison cmp, b) :: active) if_false
            | None ->
              walk active if_true;
              walk active if_false)
          | _ -> iter_subexpressions (walk active) expr
        in
        walk [] handler.body;
        let dominating =
          match !per_edge with
          | [] -> []
          | first :: others ->
            List.filter
              (fun g -> List.for_all (List.exists (same_guard g)) others)
              first
        in
        let proofs =
          List.filter_map
            (fun ((affine : affine), continue_when, b) ->
              let d = affine.multiplier * n in
              if not (in_range d)
              then None
              else
                let guard =
                  { index; affine; continue_when; bound = b; step = d }
                in
                match precondition ~dbg:handler.dbg guard with
                | Never -> None
                | (Always | Check _) as pre -> Some (guard, pre))
            dominating
        in
        (* A guard that needs no check beats one that does. *)
        (match
           List.find_opt
             (fun (_, pre) ->
               match pre with Always -> true | Never | Check _ -> false)
             proofs
         with
        | Some proof -> Some proof
        | None -> ( match proofs with proof :: _ -> Some proof | [] -> None))
      | _ -> None
  in
  let rec first index params =
    match params with
    | [] -> None
    | param :: params -> (
      match attempt index param with
      | Some found -> Some found
      | None -> first (index + 1) params)
  in
  first 0 handler.params

let rec handler_labels acc expr =
  let acc =
    match expr with
    | Ccatch (_, handlers, _) ->
      List.map (fun (handler : static_handler) -> handler.label) handlers @ acc
    | _ -> acc
  in
  let acc = ref acc in
  iter_subexpressions (fun sub -> acc := handler_labels !acc sub) expr;
  !acc

(* [Cexit] arguments are evaluated right to left; binding them to temporaries
   has to keep that order. *)
let bind_right_to_left temps args body =
  List.fold_left2
    (fun body temp arg -> Clet (VP.create temp, arg, body))
    body temps args

(* Poll on every way out of the counted loop [node]: each exit from its
   poll-free handler to a label bound outside [node], and falling out of it.
   Exit arguments are evaluated before the poll, so nothing the loop derived is
   live across it. The fallback copy polls on its own back edge. *)
let poll_on_exits ~dbg node =
  match node with
  | Ccatch (flag, handlers, body) ->
    let inside = handler_labels [] node in
    let leaves (target : exit_label) =
      match target with
      | Return_lbl -> true
      | Lbl l -> not (List.exists (Static_label.equal l) inside)
    in
    let rec loop expr =
      match expr with
      | Cexit (target, args, traps) when leaves target ->
        let temps = List.map (fun _ -> V.create_local "exit_arg") args in
        bind_right_to_left temps args
          (Csequence
             ( Cop (Cpoll, [], dbg),
               Cexit (target, List.map (fun temp -> Cvar temp) temps, traps) ))
      | _ -> map_subexpressions loop expr
    in
    let handlers =
      List.map
        (fun (handler : static_handler) ->
          if handler.is_bounded
          then { handler with body = loop handler.body }
          else handler)
        handlers
    in
    let result = V.create_local "loop_result" in
    Clet
      ( VP.create result,
        Ccatch (flag, handlers, body),
        Csequence (Cop (Cpoll, [], dbg), Cvar result) )
  | _ -> node

(* Add the exit polls of the counted loops that need them. A counted loop
   inside a loop that keeps its poll needs none: [Cfg_polling] puts a poll on
   that loop's back edge wherever a path through it reaches no safepoint, which
   a path through a counted loop now is, so the time to a poll stays bounded
   by one of its iterations. A counted loop inside another counted loop is
   covered by the outer one's exit poll. *)
let rec add_exit_polls ~in_polled_loop expr =
  match expr with
  | Ccatch (Recursive, handlers, body) ->
    if List.exists (fun (handler : static_handler) -> handler.is_bounded) handlers
    then
      if in_polled_loop
      then expr
      else poll_on_exits ~dbg:(List.hd handlers).dbg expr
    else
      Ccatch
        ( Recursive,
          List.map
            (fun (handler : static_handler) ->
              { handler with
                body = add_exit_polls ~in_polled_loop:true handler.body
              })
            handlers,
          add_exit_polls ~in_polled_loop body )
  | _ -> map_subexpressions (add_exit_polls ~in_polled_loop) expr

(* A copy of [expr] in which every label and variable bound inside it is
   renamed, so that it can stand next to the original. Debugger-only bindings
   are dropped from the copy. *)
let fresh_copy expr =
  let renamed =
    List.map (fun l -> l, Lambda.next_raise_count ()) (handler_labels [] expr)
  in
  let relabel l =
    match List.find_opt (fun (l', _) -> Static_label.equal l l') renamed with
    | Some (_, l') -> l'
    | None -> l
  in
  let fresh env v =
    let v' = V.create_local (V.name (VP.var v)) in
    VP.create v', V.Map.add (VP.var v) v' env
  in
  let rec copy env expr =
    match expr with
    | Cvar v -> (
      match V.Map.find_opt v env with Some v' -> Cvar v' | None -> expr)
    | Clet (v, def, body) ->
      let def = copy env def in
      let v, env = fresh env v in
      Clet (v, def, copy env body)
    | Cphantom_let (_, _, body) | Cname_for_debugger (_, body) -> copy env body
    | Ccatch (flag, handlers, body) ->
      let handlers =
        List.map
          (fun (handler : static_handler) ->
            let params, env =
              List.fold_right
                (fun (param, machtype) (params, env) ->
                  let param, env = fresh env param in
                  (param, machtype) :: params, env)
                handler.params ([], env)
            in
            { handler with
              label = relabel handler.label;
              params;
              body = copy env handler.body
            })
          handlers
      in
      Ccatch (flag, handlers, copy env body)
    | Cexit (target, args, traps) ->
      let target =
        match target with Lbl l -> Lbl (relabel l) | Return_lbl -> Return_lbl
      in
      let traps =
        List.map
          (function Push l -> Push (relabel l) | Pop l -> Pop (relabel l))
          traps
      in
      Cexit (target, List.map (copy env) args, traps)
    | _ -> map_subexpressions (copy env) expr
  in
  copy V.Map.empty expr

(* [node] holds the poll-free loop [original.label] that the pipeline produced
   from [original]. Add an exact copy of [original], polls included, and enter
   the poll-free loop only where [pre] holds of the counter's entry value. *)
let add_slow_path ~(original : static_handler) ~index ~pre node =
  let label = original.label in
  let slow =
    match
      fresh_copy (Ccatch (Recursive, [original], Cexit (Lbl label, [], [])))
    with
    | Ccatch (_, [slow], _) -> { slow with is_bounded = false }
    | _ -> Misc.fatal_error "Cmm_strength_reduction.add_slow_path"
  in
  let arity = List.length original.params in
  let dbg = original.dbg in
  let rec branch expr =
    match expr with
    | Cexit (Lbl l, args, traps) when Static_label.equal l label ->
      let given = List.filteri (fun i _ -> i < arity) args in
      let extra = List.filteri (fun i _ -> i >= arity) args in
      let temps = List.map (fun _ -> V.create_local "entry_arg") given in
      let vars = List.map (fun temp -> Cvar temp) temps in
      bind_right_to_left temps given
        (Cifthenelse
           ( pre (List.nth vars index),
             dbg,
             Cexit (Lbl label, vars @ extra, traps),
             dbg,
             Cexit (Lbl slow.label, vars, traps),
             dbg ))
    | _ -> map_subexpressions branch expr
  in
  let found = ref None in
  let rec find expr =
    match expr with
    | Ccatch (Recursive, [fast], body) when Static_label.equal fast.label label
      ->
      found := Some expr;
      Ccatch (Recursive, [fast; slow], branch body)
    | _ -> map_subexpressions find expr
  in
  let versioned = find node in
  match !found with
  | Some fast_node -> versioned, fast_node
  | None -> Misc.fatal_error "Cmm_strength_reduction.add_slow_path: no loop"

(* {2 Nests}

   An inner loop that carries an entry check has a fallback copy that polls, so
   the loop around it could not be counted, and a nest such as attention --
   positions, then a dot product per position -- polled once per position. A
   check of [B] alone ([uses_start = false]) has the same value wherever it is
   evaluated inside a loop that binds none of [B]'s variables. So when the
   outer loop is counted, the inner check is moved to the outer loop's entry:
   inside the outer loop's poll-free version the inner loop runs poll-free
   with no check, and the outer loop's fallback copy keeps the inner loop as it
   was. This repeats outwards, so the poll-free region is the whole nest. *)

(* Loops with an entry check, by the label of their poll-free handler: the loop
   without its fallback copy, and the check if it does not read the counter's
   entry value. *)
let versioned_loops :
    (Static_label.t * (expression * expression option)) list ref =
  ref []

(* [expr] in terms of variables bound outside a loop: every variable in
   [inside] is replaced by its definition. Only pure, total integer
   operations are allowed, so the result is the value [expr] has anywhere in
   the loop. [None] if that is not possible. *)
let lift_out ~inside expr =
  let rec go ~fuel expr =
    if fuel <= 0
    then None
    else
      match expr with
      | Cconst_int _ | Cconst_natint _ -> Some expr
      | Cvar v -> (
        if not (V.Set.mem v inside)
        then Some expr
        else
          match V.Map.find_opt v !function_defs with
          | Some def -> go ~fuel:(fuel - 1) def
          | None -> None)
      | Cop
          ( (( Caddi | Csubi | Cmuli | Cand | Cor | Cxor | Clsl | Clsr | Casr
             | Ccmpi _ ) as op),
            args,
            dbg ) ->
        let args = List.map (go ~fuel:(fuel - 1)) args in
        if List.for_all Option.is_some args
        then Some (Cop (op, List.filter_map Fun.id args, dbg))
        else None
      | _ -> None
  in
  go ~fuel:32 expr

let versioned_entry handlers =
  List.find_map
    (fun (handler : static_handler) ->
      List.find_map
        (fun (label, entry) ->
          if Static_label.equal label handler.label then Some entry else None)
        !versioned_loops)
    handlers

(* [body] with every inner loop that carries an entry check replaced by its
   poll-free version, and those checks lifted out of the loop whose variables
   are [inside]; [None] if one of them cannot be lifted. *)
let specialize ~inside body =
  let checks = ref [] and ok = ref true in
  let rec go expr =
    match expr with
    | Ccatch (Recursive, handlers, _) -> (
      match versioned_entry handlers with
      | Some (fast_node, Some check) -> (
        match lift_out ~inside check with
        | Some lifted ->
          checks := lifted :: !checks;
          fast_node
        | None ->
          ok := false;
          expr)
      | Some (_, None) ->
        ok := false;
        expr
      | None -> map_subexpressions go expr)
    | _ -> map_subexpressions go expr
  in
  let body = go body in
  if !ok then Some (body, List.rev !checks) else None

let conjunction ~dbg checks =
  match checks with
  | [] -> Cconst_int (1, dbg)
  | first :: rest ->
    List.fold_left (fun acc c -> Cop (Cand, [acc; c], dbg)) first rest

(* The loop's own precondition, with the inner checks lifted into it. *)
let with_lifted ~dbg pre lifted =
  match pre, lifted with
  | (Always | Never), [] -> pre
  | Always, _ :: _ ->
    Check { check = (fun _ -> conjunction ~dbg lifted); uses_start = false }
  | Check { check; uses_start }, _ ->
    Check
      { check = (fun start -> conjunction ~dbg (check start :: lifted));
        uses_start
      }
  | Never, _ :: _ -> Never

(* -dcounted-loops *)
let current_function = ref ""

let report ~dbg decision =
  if !Oxcaml_flags.dump_counted_loops
  then
    Format.eprintf "@[<h>counted-loops %s %a: %s@]@." !current_function
      Debuginfo.print_compact dbg decision

(* {1 Driver} *)

let rec rewrite ~duplicated ~strength_reduction ~form_interior_pointers
    ~invariant_strides ~carry_pointers ~licm ~counts int_vars expr =
  let rewrite =
    rewrite ~duplicated ~strength_reduction ~form_interior_pointers
      ~invariant_strides ~carry_pointers ~licm ~counts
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
      (* Reading a variable once before the loop instead of once per iteration
         is the same computation only where nothing can move it in between, and
         a pointer may only be derived where nothing can move it at all. *)
      let gc_free = is_gc_free expr in
      let pipeline ?(gc_free = gc_free) ~form_interior_pointers ~carry_pointers
          ~handlers expr =
        let relaxed = form_interior_pointers && gc_free in
        (* Invariants first: what leaves the loop here is bound outside it, so the
           passes below may treat it as loop-invariant. *)
        let hoisted, expr =
          if not (licm && relaxed)
          then [], expr
          else
            match
              hoist_invariants ~duplicated ~int_vars ~relaxed ~counts ~expr
            with
            | hoisted, expr -> hoisted, expr
            | exception Not_applicable -> [], expr
        in
        (* Interior pointers next. Where they fire they subsume the strength
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
        (* Vector rows before [reduce], which would otherwise carry the index
           sums these addresses are built from and hide their counter. *)
        let expr =
          if not (carry_pointers && relaxed)
          then expr
          else
            List.fold_left
              (fun expr (handler : static_handler) ->
                match vector_pointers ~duplicated ~label:handler.label ~expr with
                | expr -> expr
                | exception Not_applicable -> expr)
              expr handlers
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
        (* The row loop above an interior pointer steps it by a multiple of the
           row length, which is a loop-invariant value rather than a constant, so
           [reduce] cannot carry it and every row rebuilds the pointer from the
           row index. *)
        let bindings, expr =
          if not (strength_reduction && invariant_strides && relaxed)
          then bindings, expr
          else
            List.fold_left
              (fun (bindings, expr) (handler : static_handler) ->
                match
                  reduce_invariant_strides ~duplicated ~int_vars ~relaxed
                    ~carry_pointers ~label:handler.label ~expr
                with
                | new_bindings, expr -> new_bindings @ bindings, expr
                | exception Not_applicable -> bindings, expr)
              (bindings, expr) handlers
        in
        List.fold_left
          (fun expr (var, def) -> Clet (VP.create var, def, expr))
          expr (bindings @ hoisted)
      in
      (* Where a safepoint is possible the pointer passes decline, because a
         derived pointer may not be live across one. A counted loop has no
         back-edge poll -- it polls on its exits instead -- so inside it the
         passes run as they would on a unit compiled without polling. *)
      let counted =
        if not (!counted_loops_enabled && not form_interior_pointers)
        then None
        else
          match expr, handlers with
          | Ccatch (_, _, entry), [original] -> (
            let dbg = original.dbg in
            let decline reason =
              report ~dbg ("not counted: " ^ reason);
              None
            in
            match
              specialize ~inside:(bound_variables V.Set.empty expr)
                original.body
            with
            | None -> decline "an inner loop's entry check cannot be lifted"
            | Some (body, lifted) -> (
              let handler = { original with body } in
              let node = Ccatch (Recursive, [handler], entry) in
              if not (is_gc_free node)
              then decline "a GC point inside"
              else if contains_polled_loop body || contains_polled_loop entry
              then decline "a loop inside that keeps its poll"
              else
                match counted_guard ~duplicated ~int_vars ~expr:node handler with
                | None -> decline "no counter with a dominating guard"
                | Some (guard, pre) ->
                  let pre = with_lifted ~dbg pre lifted in
                  report ~dbg
                    (Printf.sprintf "counted, %s%s"
                       (match pre with
                       | Always | Never -> "no entry check"
                       | Check _ -> "entry check")
                       (match lifted with
                       | [] -> ""
                       | _ :: _ ->
                         Printf.sprintf " (%d inner check(s) lifted)"
                           (List.length lifted)));
                  Some (original, handler, node, guard, pre)))
          | _, _ :: _ :: _ ->
            report
              ~dbg:(List.hd handlers).dbg
              "not counted: several handlers";
            None
          | _, _ -> None
      in
      match counted with
      | None -> pipeline ~form_interior_pointers ~carry_pointers ~handlers expr
      | Some (original, handler, node, guard, pre) -> (
        found_counted := true;
        let fast = { handler with is_bounded = true } in
        let expr =
          match node with
          | Ccatch (flag, _, entry) -> Ccatch (flag, [fast], entry)
          | _ -> node
        in
        let expr =
          pipeline ~gc_free:true ~form_interior_pointers:true
            ~carry_pointers:true ~handlers:[fast] expr
        in
        match pre with
        | Always | Never -> expr
        | Check { check; uses_start } ->
          let versioned, fast_node =
            add_slow_path ~original ~index:guard.index ~pre:check expr
          in
          versioned_loops
            := ( fast.label,
                 ( fast_node,
                   if uses_start
                   then None
                   else Some (check (Cconst_int (0, original.dbg))) ) )
               :: !versioned_loops;
          versioned))
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
  let invariant_strides = !Oxcaml_flags.cmm_invariant_strides in
  let licm = !Oxcaml_flags.cmm_licm in
  (* A carried pointer is live across the loop's back edge, which is where a
     poll would go, so it is only representable where that loop has no
     safepoint: either the whole unit is compiled without polling, or this
     function is annotated [@poll error]. [Cfg_selectgen] admits an [Addr] in a
     [Ccatch] register under exactly the same condition. *)
  let carry_pointers =
    !Oxcaml_flags.cmm_carried_pointers && polls_are_impossible fundecl
  in
  (* The proofs above are about 64-bit words, computed with a 64-bit host. *)
  counted_loops_enabled
    := !Oxcaml_flags.cmm_counted_loops
       && (not (polls_are_impossible fundecl))
       && Arch.size_int = 8 && Nativeint.size = 64;
  found_counted := false;
  versioned_loops := [];
  current_function := fundecl.fun_name.sym_name;
  if
    not
      (strength_reduction || form_interior_pointers || licm
     || !counted_loops_enabled)
  then fundecl
  else
    let params = List.map (fun (param, _) -> VP.var param) fundecl.fun_args in
    let duplicated = duplicate_binders ~params fundecl.fun_body in
    let int_vars = add_int_params ~duplicated V.Set.empty fundecl.fun_args in
    let counts = occurrence_counts fundecl.fun_body in
    function_defs := defs_of_body ~duplicated fundecl.fun_body;
    let body =
      rewrite ~duplicated ~strength_reduction ~form_interior_pointers
        ~invariant_strides ~carry_pointers ~licm ~counts int_vars
        fundecl.fun_body
    in
    let body =
      if !found_counted then add_exit_polls ~in_polled_loop:false body else body
    in
    { fundecl with fun_body = body }
