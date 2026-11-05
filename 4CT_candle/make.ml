(* ========================================================================= *)
(* 4CT_candle/make.ml: the Four Colour Theorem in Candle, end to end.        *)
(*                                                                           *)
(* After hol.ml (Candle's start-up) and from the Candle root directory,      *)
(*                                                                           *)
(*   loads "4CT_candle/make.ml";;                                            *)
(*                                                                           *)
(* (with CML_HEAP_SIZE large enough, see REPORT.md) loads Multivariate with  *)
(* planar_graph.ml, the 4CT development with the Kernel.compute versions of  *)
(* the HOL Light evaluation files, runs Part 2 and proves FOUR_COLOR,        *)
(* FOUR_COLOR_PLANAR_GRAPH, FOUR_COLOR_KURATOWSKI, FOUR_COLOR_WAGNER,        *)
(* FOUR_COLOR_MAP and FOUR_COLOR_MAP_EXPLICIT with no hypotheses, checked by *)
(* check_axioms ().                                                          *)
(* ========================================================================= *)

needs "4CT_candle/prelude.ml";;
needs "4CT_candle/make_mv.ml";;
needs "4CT_candle/make_part1.ml";;
needs "4CT_candle/make_part2.ml";;
