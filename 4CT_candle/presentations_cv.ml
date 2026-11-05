(* ========================================================================= *)
(* 4CT_candle/presentations_cv.ml                                            *)
(*                                                                           *)
(* Candle version of 4CT/presentations.ml: the seven presentation lemmas     *)
(* exclude5 .. exclude11 (excluded_arity (:A) n, n = 5..11) by the           *)
(* interpreter of present_cv.ml, side conditions by Kernel.compute.          *)
(* ========================================================================= *)

needs "4CT_candle/present_cv.ml";;

let exclude5 = prove_exclude 5 present5_steps;;
let exclude6 = prove_exclude 6 present6_steps;;
let exclude7 = prove_exclude 7 present7_steps;;
let exclude8 = prove_exclude 8 present8_steps;;
let exclude9 = prove_exclude 9 present9_steps;;
let exclude10 = prove_exclude 10 present10_steps;;
let exclude11 = prove_exclude 11 present11_steps;;
