(* ========================================================================= *)
(* 4CT_candle/present_cv.ml                                                  *)
(*                                                                           *)
(* The interpreter of Gonthier's presentation scripts present5.v to          *)
(* present11.v (the step data of 4CT/presentations_data.ml) with             *)
(* Kernel.compute in place of the CBV evaluation of 4CT/present_eval.ml.    *)
(*                                                                           *)
(* The steps are run as in present_eval.ml: a Pcase step applies             *)
(* SUCCEED_BY_SPLIT and its ground part and boolean subterms (good_split,    *)
(* split_part, the conditional part) are evaluated by cv_eval; the side      *)
(* conditions of the Reducible, Hubcap and Similar steps are assumed while   *)
(* the script runs, then proved in batches (one Kernel.compute run per       *)
(* batch of their conjunction) and discharged by PROVE_HYP.                  *)
(* ========================================================================= *)

needs "4CT_candle/unavoid_cv.ml";;
needs "4CT/present_steps_type.ml";;
needs "4CT/presentations_data.ml";;

let ploc_term l =
  match l with
    Spoke -> `Pspoke` | Hat -> `Phat` | Fan1 -> `Pfan1` | Fan2 -> `Pfan2`
  | Fan3 -> `Pfan3`;;

let int_term b =
  if b < 0 then
    mk_comb(`(--):int->int`, mk_comb(`(&):num->int`, mk_small_numeral (0 - b)))
  else mk_comb(`(&):num->int`, mk_small_numeral b);;

(* Coq `$[j1,j2]<=b ... $`: Hubcap2 (j1-1) (j2-1) b (...), outermost first   *)
let hubcap_term items =
  itlist (fun it rest ->
            match it with
              Hc1(j,b) -> list_mk_comb(`Hubcap1`, [mk_small_numeral (j-1);
                                                   int_term b; rest])
            | Hc2(j1,j2,b) ->
                list_mk_comb(`Hubcap2`,
                  [mk_small_numeral (j1-1); mk_small_numeral (j2-1);
                   int_term b; rest]))
         items `Hubcap0`;;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the ground subterms with the given head constants.         *)
(* ------------------------------------------------------------------------- *)

let cv_ground_heads = ["good_split"; "split_part"; "COND"; "pcons_"];;

let rec cv_collect t acc =
  let h = fst(strip_comb t) in
  if is_const h && mem (fst(dest_const h)) cv_ground_heads && frees t = [] then
    (if mem t acc then acc else t :: acc)
  else if is_comb t then cv_collect (rator t) (cv_collect (rand t) acc)
  else if is_abs t then cv_collect (body t) acc
  else acc;;

let CV_GROUND_CONV tm =
  let ts = cv_collect tm [] in
  if ts = [] then REFL tm else REWRITE_CONV (map cv_eval ts) tm;;

let CV_TAC = CONV_TAC CV_GROUND_CONV;;

(* ------------------------------------------------------------------------- *)
(* The step tactics.  Goals have the form `succeeds_in (:A) p0 p` with the   *)
(* assumption `check_reducibility` and labelled `successful (:A) ps` facts.  *)
(* ------------------------------------------------------------------------- *)

let step_count = ref 0;;
let side_conditions = ref ([]:term list);;

let SIDE_TAC g =
  let w = snd g in
  side_conditions := w :: !side_conditions; ACCEPT_TAC (ASSUME w) g;;

let count_step name tac g =
  step_count := !step_count + 1;
  try tac g
  with Failure s -> failwith ("PRESENT_CV step " ^ string_of_int !step_count ^
                              " (" ^ name ^ "): " ^ s);;

let PCASE_TAC lab loc j k lo block cont =
  count_step "Pcase"
   (MATCH_MP_TAC(ISPECL
     [ploc_term loc; mk_small_numeral (j-1); mk_small_numeral k;
      (if lo then `T` else `F`)] SUCCEED_BY_SPLIT) THEN
    CV_TAC THEN CONJ_TAC) THENL
  [block;
   (if lab = "_" then DISCH_THEN(K ALL_TAC) else DISCH_THEN(LABEL_TAC lab))
     THEN cont];;

let REDUCIBLE_TAC =
  count_step "Reducible"
   (MATCH_MP_TAC SUCCEED_BY_REDUCIBILITY THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; SIDE_TAC]);;

let HUBCAP_TAC items =
  count_step "Hubcap"
   (MATCH_MP_TAC(ISPEC (hubcap_term items) SUCCEED_BY_HUBCAP) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIDE_TAC]);;

let SIMILAR_TAC lab j mir =
  count_step "Similar"
   (USE_THEN lab (fun th ->
      MATCH_MP_TAC(ISPECL
        [mk_small_numeral j; (if mir then `T` else `F`); rand(concl th)]
                          SUCCEED_BY_SIMILARITY) THEN
      CONJ_TAC THENL [ACCEPT_TAC th; SIDE_TAC]));;

(* A block at depth d: Pcases at depth d (each followed by its indented      *)
(* block) ending with a terminal step at depth d.                            *)
let rec build_block d steps =
  match steps with
    [] -> failwith "build_block: malformed presentation"
  | (d1, st) :: rest ->
      if not (d1 = d) then failwith "build_block: malformed presentation" else
      match st with
        Pcase(lab,loc,j,k,lo) ->
          let (block, rest1) = build_block (d+1) rest in
          let (cont, rest2) = build_block d rest1 in
          (PCASE_TAC lab loc j k lo block cont, rest2)
      | Reducible -> (REDUCIBLE_TAC, rest)
      | Hubcap items -> (HUBCAP_TAC items, rest)
      | Similar(lab,j,mir) -> (SIMILAR_TAC lab j mir, rest);;

let PRESENTATION_TAC steps =
  let (tac, rest) = build_block 0 steps in
  if not (rest = []) then failwith "PRESENTATION_TAC: trailing steps" else
  MATCH_MP_TAC EXCLUDE_ARITY THEN DISCH_TAC THEN CV_TAC THEN tac;;

(* ------------------------------------------------------------------------- *)
(* The side conditions, proved in batches.                                   *)
(* ------------------------------------------------------------------------- *)

let cv_side_fold_conv = PURE_REWRITE_CONV[GSYM HUBCAP_FIT_RP_DEF];;

let rec cv_split_conj n th =
  if n = 1 then [th] else CONJUNCT1 th :: cv_split_conj (n-1) (CONJUNCT2 th);;

let cv_prove_sides ws =
  let w = list_mk_conj ws in
  let th0 = cv_side_fold_conv w in
  let th1 = EQT_ELIM (cv_eval (rhs(concl th0))) in
  cv_split_conj (length ws) (EQ_MP (SYM th0) th1);;

let rec cv_chunks n l =
  if l = [] then [] else
  if length l <= n then [l] else
  let a,b = chop_list n l in a :: cv_chunks n b;;

let side_batch = ref 100;;

let prove_exclude n steps =
  step_count := 0; side_conditions := [];
  let tm = mk_comb(`excluded_arity (:A)`, mk_small_numeral n) in
  let th0 = TAC_PROOF(([],tm), PRESENTATION_TAC steps) in
  let sides = setify (fun x y -> alphaorder x y <= 0) !side_conditions in
  print_string ("PRESENT_CV: exclude" ^ string_of_int n ^ " script done, " ^
                string_of_int !step_count ^ " steps, " ^
                string_of_int (length sides) ^ " side conditions\n");
  let ths = flat (map cv_prove_sides (cv_chunks !side_batch sides)) in
  let th = itlist PROVE_HYP ths th0 in
  if not (hyp th = []) then
    failwith ("prove_exclude " ^ string_of_int n ^ ": " ^
              string_of_int (length (hyp th)) ^ " side conditions failed")
  else
   (print_string ("PRESENT_CV: exclude" ^ string_of_int n ^ " proved\n");
    if concl th = tm then th else EQ_MP (ALPHA (concl th) tm) th);;
