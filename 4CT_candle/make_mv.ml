(* ========================================================================= *)
(* 4CT_candle/make_mv.ml: Multivariate with Autoformalization/planar_graph.ml *)
(* (for sections P and M), as at the start of 4CT/make.ml.                   *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/permutations.ml";;
needs "Autoformalization/planar_graph.ml";;

prioritize_num();;

parse_as_infix("::",(23,"right"));;
override_interface("::",`CONS`);;
