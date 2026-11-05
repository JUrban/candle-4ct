(* ========================================================================= *)
(* 4CT_candle/make_part2.ml: Part 2 (|- check_reducible cfNNN for the 633    *)
(* configurations by Kernel.compute, part2_run_cv.ml), REDUCIBILITY, and the *)
(* theorem in all its forms, with check_axioms().                            *)
(* ========================================================================= *)

needs "4CT_candle/part2_run_cv.ml";;

p2_cv_run 1 633;;

let REDUCIBILITY =
  if not (length !p2_cv_results = 633) then failwith "Part 2 incomplete" else
  prove(`reducibility`,
    REWRITE_TAC[reducibility; ALL_MEM; the_configs; ALL] THEN
    REWRITE_TAC (map snd !p2_cv_results));;

let FOUR_COLOR = MP FOUR_COLOR_HYPERMAP REDUCIBILITY;;
let FOUR_COLOR_PLANAR_GRAPH =
  MP FOUR_COLOR_PLANAR_GRAPH_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_KURATOWSKI =
  MP FOUR_COLOR_KURATOWSKI_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_WAGNER = MP FOUR_COLOR_WAGNER_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_MAP = MP FOUR_COLOR_MAP_OF_REDUCIBILITY REDUCIBILITY;;
let FOUR_COLOR_MAP_EXPLICIT =
  MP FOUR_COLOR_MAP_EXPLICIT_OF_REDUCIBILITY REDUCIBILITY;;

do_list
 (fun (name,th) ->
    print_string ("=== 4CT_candle/make_part2.ml: " ^ name ^ " = " ^
                  string_of_thm th ^ " (hyps " ^
                  string_of_int (length (hyp th)) ^ ") ===\n"))
 [("FOUR_COLOR",FOUR_COLOR); ("FOUR_COLOR_PLANAR_GRAPH",FOUR_COLOR_PLANAR_GRAPH);
  ("FOUR_COLOR_KURATOWSKI",FOUR_COLOR_KURATOWSKI);
  ("FOUR_COLOR_WAGNER",FOUR_COLOR_WAGNER); ("FOUR_COLOR_MAP",FOUR_COLOR_MAP);
  ("FOUR_COLOR_MAP_EXPLICIT",FOUR_COLOR_MAP_EXPLICIT)];;

check_axioms ();;
print_string ("=== check_axioms passed; axioms: " ^
              String.concat ", " (map string_of_thm (axioms())) ^ " ===\n");;
