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

(* {1 Driver} *)

let rec rewrite ~duplicated int_vars expr =
  match expr with
  | Clet (v, def, body) ->
    let def = rewrite ~duplicated int_vars def in
    let int_vars =
      if is_int_expression int_vars def
      then add_int_var ~duplicated int_vars (VP.var v)
      else int_vars
    in
    Clet (v, def, rewrite ~duplicated int_vars body)
  | Ccatch (flag, handlers, body) -> (
    (* Bottom-up, so that an inner loop is already in its final form when the
       loop enclosing it is examined. *)
    let handlers =
      List.map
        (fun (handler : static_handler) ->
          let int_vars = add_int_params ~duplicated int_vars handler.params in
          { handler with body = rewrite ~duplicated int_vars handler.body })
        handlers
    in
    let expr = Ccatch (flag, handlers, rewrite ~duplicated int_vars body) in
    match flag with
    | Normal | Exn_handler -> expr
    | Recursive ->
      List.fold_left
        (fun expr (handler : static_handler) ->
          match reduce ~duplicated ~int_vars ~label:handler.label ~expr with
          | expr -> expr
          | exception Not_applicable -> expr)
        expr handlers)
  | _ -> map_subexpressions (rewrite ~duplicated int_vars) expr

let fundecl (fundecl : fundecl) =
  if not !Oxcaml_flags.cmm_strength_reduction
  then fundecl
  else
    let params = List.map (fun (param, _) -> VP.var param) fundecl.fun_args in
    let duplicated = duplicate_binders ~params fundecl.fun_body in
    let int_vars = add_int_params ~duplicated V.Set.empty fundecl.fun_args in
    { fundecl with fun_body = rewrite ~duplicated int_vars fundecl.fun_body }
