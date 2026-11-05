(* ========================================================================= *)
(* 4CT_candle/make_part1.ml: Part 1 of 4CT/make.ml (sections A-G, P, M) for  *)
(* Candle.  The HOL Light evaluation files are replaced by their Kernel.     *)
(* compute versions: birkhoff.ml loads 4CT_candle/birkhoff_cv.ml (Birkhoff   *)
(* checks), unavoidability.ml loads 4CT_candle/unavoid_cv.ml (quiz tree,     *)
(* discharge bounds, hubcaps; for quiztree_eval.ml and redpart_eval.ml) and  *)
(* 4CT_candle/presentations_cv.ml (for presentations.ml).                    *)
(* ========================================================================= *)

(* A. Foundation                                                             *)
needs "4CT/general.ml";;
needs "4CT/hypermap.ml";;
needs "4CT/geometry.ml";;
needs "4CT/color.ml";;
needs "4CT/coloring.ml";;
needs "4CT/walkup.ml";;
needs "4CT/jordan.ml";;
needs "4CT/chromogram.ml";;
needs "4CT/kempe.ml";;

(* B. Surgery                                                                *)
needs "4CT/patch.ml";;
needs "4CT/snip.ml";;
needs "4CT/preembedding.ml";;
needs "4CT/revsnip.ml";;
needs "4CT/embed_prelim.ml";;
needs "4CT/cfmap.ml";;
needs "4CT/sew.ml";;
needs "4CT/revsnip_tail.ml";;

(* C. Trees                                                                  *)
needs "4CT/dyck.ml";;
needs "4CT/ctree.ml";;
needs "4CT/gtree.ml";;
needs "4CT/cfcolor.ml";;
needs "4CT/initctree.ml";;
needs "4CT/initgtree.ml";;
needs "4CT/ctreerestrict.ml";;
needs "4CT/gtreerestrict.ml";;
needs "4CT/kempetree.ml";;
needs "4CT/cpcolor_correct.ml";;

(* D. Birkhoff, embedding, contract                                          *)
needs "4CT/birkhoff.ml";;
needs "4CT/embed.ml";;
needs "4CT/contract.ml";;
needs "4CT/embed_contract.ml";;

(* E. Reducibility                                                           *)
needs "4CT/cfcontract.ml";;
needs "4CT/kempetree_wrap.ml";;
needs "4CT/cfreducible.ml";;

(* F. Configurations                                                         *)
needs "4CT/part.ml";;
needs "4CT/part_mirror.ml";;
needs "4CT/quiz.ml";;
needs "4CT/cube.ml";;
needs "4CT/configurations.ml";;

(* G. Unavoidability                                                         *)
needs "4CT/part_converse.ml";;
needs "4CT/discharge.ml";;
needs "4CT/hubcap.ml";;
needs "4CT/cfquiz.ml";;
needs "4CT/quiztree.ml";;
needs "4CT/redpart.ml";;
needs "4CT/present.ml";;
needs "4CT_candle/unavoid_cv.ml";;
needs "4CT_candle/presentations_cv.ml";;
needs "4CT/unavoidability.ml";;
needs "4CT/four_color.ml";;

(* P. Planar graphs                                                          *)
needs "4CT/planar_graph_link.ml";;
needs "4CT/four_color_planar.ml";;

(* M. Plane maps                                                             *)
needs "4CT/map_defs.ml";;
needs "4CT/map_grid.ml";;
needs "4CT/map_main.ml";;
needs "4CT/four_color_map.ml";;

print_string "=== 4CT_candle/make_part1.ml: Part 1 (the mathematics) loaded ===\n";;
