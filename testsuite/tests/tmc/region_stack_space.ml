(* TEST
 stack-allocation;
 native;
*)


let[@inline never] local_pair () = exclave_ (1, 2)

let[@inline never] use_local (local_ _x : int * int) = ()

(* tail recursive, no region. Stack space constant *)
let rec rev_map acc xs ~f =
  match xs with
  | [] -> acc
  | x::xs -> rev_map ((f x)::acc) xs ~f

(* tail recursive, with a region. Stack space constant *)
let rec rev_map_with_local acc xs ~f = 
  let p = local_pair () in
  ignore (Sys.opaque_identity (fst p));
  match xs with
  | [] -> acc
  | x::xs -> rev_map_with_local (f x::acc) xs ~f

(* TMC, no region, Stack space constant *)
let[@tail_mod_cons] rec map_plain t ~f =
  match t with
  | [] -> []
  | hd :: tl -> f hd :: map_plain tl ~f


(* TMC, with region, no local parameterse, Stack space constant *)
let[@tail_mod_cons] rec map_exclave t ~f =
  let p = local_pair () in
  ignore (Sys.opaque_identity (fst p));
  match t with
  | [] -> []
  | hd :: tl -> f hd :: map_exclave tl ~f

(* TMC, with region, no local parameters, does a local allocation that actually escapes into a call. *)
let[@tail_mod_cons] rec map_local t ~f =
  let local_ p = (Sys.opaque_identity 1, Sys.opaque_identity 2) in
  use_local p;
  match t with
  | [] -> []
  | hd :: tl -> f hd :: map_local tl ~f

(* TMC, regions + parameters at local. 
 * This could be constant stack space, but currently isn't.
 * Raise a warning to users that `@tail_mod_cons` isn't doing what it says here
 * *)
let[@tail_mod_cons] rec map_local_param (bound : (int * int) @ local) t ~f =
  let p = local_pair () in
  ignore (Sys.opaque_identity (fst p));
  use_local bound;
  match t with
  | [] -> []
  | hd :: tl -> f hd :: map_local_param bound tl ~f

(* TMC, regions + the recursive call _uses_ the data we create on each local stack frame.
 * This fundementally can't be constant stack space.
 * Ideally, the type system would reject this? 
 *)
let[@tail_mod_cons] rec map_using_local t ~f = 
  let f' = stack_ (fun x -> (f x) + 1) in 
  match t with
  | [] -> []
  | hd :: tl -> f' hd :: map_using_local tl ~f:f'

(* TMC, mutliple regions. Constant stack space *)
let[@tail_mod_cons] rec map_nested_regions t ~f =
  let p = local_pair () in
  ignore (Sys.opaque_identity (fst p));
  let go t =
    let q = local_pair () in
    ignore (Sys.opaque_identity (fst q));
    match t with
    | [] -> []
    | hd :: tl -> f hd :: map_nested_regions tl ~f
  in
  go t

(* TMC, mutliple regions. Constant stack space *)
let[@tail_mod_cons] rec map_nested_regions_shared t ~f =
  let p = local_pair () in
  ignore (Sys.opaque_identity (fst p));
  let go t =
    let q = local_pair () in
    ignore (Sys.opaque_identity (fst q));
    match t with
    | [] -> []
    | hd :: tl -> f hd :: map_nested_regions_shared tl ~f
  in
  if Sys.opaque_identity true then go t else go (List.rev t)

(* TMC through mutually recursive helper:
 * Region appears because we can infer the option is at local 
 *)
let[@tail_mod_cons] rec map_via_helper t ~f =
  match t with
  | [] -> []
  | hd :: tl ->
      let first =
        match Sys.opaque_identity (Some hd), Sys.opaque_identity (Some 0) with
        | Some x, Some y -> Some (min x y)
        | None, x | x, None -> x
      in
      let repeat = match first with None -> 0 | Some _ -> 1 in
      f hd :: helper ~repeat tl ~f
and[@tail_mod_cons] helper ~repeat t ~f =
  if repeat = 0 then map_via_helper t ~f
  else 0 :: helper ~repeat:(repeat - 1) t ~f

let depth () = Printexc.raw_backtrace_length (Printexc.get_callstack 10_000)

(* Tail-recursive, so building the input does not itself grow the stack. *)
let rec build acc n = if n = 0 then acc else build (n :: acc) (n - 1)

let large = 50

(* TMC guarantees [f] is applied to each element before the recursive call,
   so the samples come out in list order. The first element is mapped by the
   direct function before it delegates to the dps variant, so its depth
   differs either way; compare from the second element onwards.

   Only the shape is checked, never the absolute depths, which shift with the
   optimization level. *)
let report name map =
  let samples = ref [] in
  let sample i = samples := depth () :: !samples; i in
  ignore (map (build [] large) ~f:sample);
  match List.rev !samples with
  | [] | [_] -> Printf.printf "%-32s too few samples\n" name
  | _first :: (base :: _ as rest) ->
      let constant = List.for_all (fun d -> d = base) rest in
      Printf.printf "%-32s constant stack: %b\n" name constant

let () =
  report "rev_map" (rev_map []);
  report "rev_map_with_local" (rev_map_with_local []);
  report "map_plain" map_plain;
  report "map_exclave" map_exclave;
  report "map_local" map_local;
  report "map_local_param" (map_local_param (1, 2));
  report "map_using_local" map_using_local;
  report "map_nested_regions" map_nested_regions;
  report "map_nested_regions_shared" map_nested_regions_shared;
  report "map_via_helper" map_via_helper
