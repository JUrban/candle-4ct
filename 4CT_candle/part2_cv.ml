(* ========================================================================= *)
(* 4CT_candle/part2_cv.ml                                                    *)
(*                                                                           *)
(* Part 2 for Candle: the reducibility check check_reducible cfNNN <=> T     *)
(* for the 633 configurations by Kernel.compute (Candle's verified           *)
(* compute primitive), through the cv translations of cvtrans.ml.            *)
(* The functions translated are the definitions of the Part 1 files or       *)
(* first-order reformulations of them proved here (several follow            *)
(* 4CT/part2_eval.ml, which does the same for eval_compile).                 *)
(* ========================================================================= *)

needs "4CT/cfreducible.ml";;
needs "4CT_candle/cvtrans.ml";;

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

do_list (fun n -> ignore (cv_register_type n))
  ["color"; "edge_perm"; "cpstep"; "ctree"; "ctree_pair"; "gtree";
   "gtree_pair"; "bit_stack"; "gram_symbol"; "gtree_restriction";
   "ctree_restriction"];;

do_list (fun n -> ignore (cv_prove_inj n))
  ["color"; "edge_perm"; "cpstep"; "bit_stack"; "gram_symbol"; "ctree"; "gtree"];;

(* ------------------------------------------------------------------------- *)
(* Lists and colours.                                                        *)
(* ------------------------------------------------------------------------- *)

let cvt th = ignore (cv_translate th);;

do_list cvt [LENGTH; APPEND; REVERSE];;
cvt (INST_TYPE [`:color`,`:A`] MEM);;
