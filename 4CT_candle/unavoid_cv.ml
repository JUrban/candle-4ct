(* ========================================================================= *)
(* 4CT_candle/unavoid_cv.ml                                                  *)
(*                                                                           *)
(* cv translations for the unavoidability computations (replacing the CBV    *)
(* evaluations of quiztree_eval.ml, redpart_eval.ml and present_eval.ml):   *)
(* parts and ranges (part.ml), quizzes (quiz.ml, cfquiz.ml), the quiz tree  *)
(* (quiztree.ml), reducible parts (redpart.ml), discharge rules             *)
(* (discharge.ml) and hubcaps (hubcap.ml).                                   *)
(* ========================================================================= *)

needs "4CT/present.ml";;
needs "4CT_candle/part2_cv.ml";;
needs "4CT_candle/cvint.ml";;

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

do_list (fun n -> ignore (cv_register_type n))
  ["prange"; "subpart_loc"; "part"; "part_rel"; "qarity"; "question"; "quiz";
   "quiz_tree"; "zpart_loc"; "zpart"; "hubcap"];;
do_list (fun n -> ignore (cv_prove_inj n))
  ["prange"; "subpart_loc"; "part"; "part_rel"; "qarity"; "question"];;

(* ------------------------------------------------------------------------- *)
(* Ranges (part.ml).  cmp_range quantifies over arities: its 225 values are  *)
(* tabulated (as in redpart_eval.ml).                                        *)
(* ------------------------------------------------------------------------- *)

do_list cvt [rlo; rhi; rbounded; apply_part_rel; notPsubset; meet_prel;
             prange_of_bounds];;
cvt (REWRITE_RULE[MAX; MIN] meet_range);;

let cv_decide_forall_conv c =
  try EQT_INTRO(prove(c, ARITH_TAC)) with Failure _ ->
    EQF_INTRO(tryfind
      (fun k -> prove(mk_neg c, REWRITE_TAC[NOT_FORALL_THM] THEN
                                EXISTS_TAC (mk_small_numeral k) THEN
                                ARITH_TAC))
      (5--13));;
let cv_cmp_range_conv tm =
  let th1 = REWRITE_CONV[cmp_range; mem_range] tm in
  let th1 = CONV_RULE (RAND_CONV (DEPTH_CONV BETA_CONV)) th1 in
  let rec simp t =
    if is_cond t then
      let c,(x,y) = dest_cond t in
      let th = REWRITE_CONV[cv_decide_forall_conv c] t in
      TRANS th (simp (rand(concl th)))
    else REFL t in
  TRANS th1 (simp (rand(concl th1)));;
let cv_prange_consts =
  map (fun s -> mk_const(s,[]))
      ["Pr55";"Pr66";"Pr77";"Pr88";"Pr99";"Pr56";"Pr67";"Pr78";"Pr89";"Pr57";
       "Pr68";"Pr79";"Pr58";"Pr69";"Pr59"];;
let CMP_RANGE_TABLE = end_itlist CONJ
  (flat (map (fun r1 -> map (fun r2 -> cv_cmp_range_conv
                              (list_mk_comb(`cmp_range`,[r1;r2])))
                            cv_prange_consts) cv_prange_consts));;
cvt CMP_RANGE_TABLE;;

let MEM_RANGE_E = cv_eta mem_range;;
cvt MEM_RANGE_E;;
do_list cvt [prange_lo; prange_hi; good_rsplit; split_range];;

(* ------------------------------------------------------------------------- *)
(* Parts (part.ml).                                                          *)
(* ------------------------------------------------------------------------- *)

do_list cvt [size_part; drop_part; take_part; cat_part; catrev_part; rev_part;
             rot_part; get_spoke; next_hat; get_hat; get_fan1r; get_fan2r;
             get_fan3r; get_fan1l; get_fan2l; get_fan3l; mirror_part_rec;
             mirror_part; cmp_part; meet_part];;

let PCONS__CLAUSES = prove
 (`pcons_ 0 = Pnil /\ (!n. pcons_ (SUC n) = Pcons Pr59 Pr59 (pcons_ n))`,
  REWRITE_TAC[pcons_; ITER]);;
cvt PCONS__CLAUSES;;
