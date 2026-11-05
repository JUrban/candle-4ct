(* ========================================================================= *)
(* 4CT_candle/prelude.ml: Candle-specific set-up before loading 4CT.         *)
(* candle/compute.ml overloads +, -, * (and friends) with the cval           *)
(* operations Cexp_*; remove these so that ordinary arithmetic terms are     *)
(* parsed as in HOL Light.  cval terms are written with Cexp_* explicitly.   *)
(* ========================================================================= *)

the_interface :=
  filter (fun (_,(c,_)) ->
            let n = String.length c in
            not (n >= 5 && String.sub c 0 5 = "Cexp_"))
         (!the_interface);;

(* OCaml for-loops are not supported by Candle's parser: the converted      *)
(* sources use for_loop a b (fun i -> body) for "for i = a to b do body done" *)
let rec for_loop a b (f:int->unit) =
  if a > b then () else (f a; for_loop (a + 1) b f);;
