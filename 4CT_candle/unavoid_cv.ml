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
do_list cvt [prange_lo; prange_hi; good_rsplit];;
cvt (REWRITE_RULE[COND_RATOR] split_range);;

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

do_list cvt [gsplit_spoke; gsplit_hat; gsplit_fan1; gsplit_fan2; gsplit_fan3;
             good_split; ssplit_spoke; ssplit_hat; ssplit_fan1; ssplit_fan2;
             ssplit_fan3; split_part];;

(* ------------------------------------------------------------------------- *)
(* Quizzes (quiz.ml, cfquiz.ml).                                             *)
(* ------------------------------------------------------------------------- *)

do_list cvt [nat_of_qarity; qarity_of_nat; isQaskR; flatq; flipq; isQuizR;
             flatqz; qra; qrb; flipqz; small_qarity; bad_small_arity;
             large_qarity; bad_ring_arity; isQaskL; isCpR; cpr_arg; rqs_Y; rqs_H];;
cv_add_unfold noquiz;;

(* cfquiz_Y / cfquiz_H with their continuation (always rqs_Y / rqs_H         *)
(* partially applied) inlined                                                *)
let cfq_Y = new_definition
 `cfq_Y rq1 rq2 rq3 qs = cfquiz_Y rq1 rq2 (rqs_Y rq1 rq3 qs)`;;
let CFQ_Y = REWRITE_RULE[GSYM cfq_Y]
  (GEN_ALL (CONV_RULE (RAND_CONV (REWRITE_CONV[cfquiz_Y])) (SPEC_ALL cfq_Y)));;
let cfq_H = new_definition
 `cfq_H rq1 rq2 rq3 qs = cfquiz_H rq1 rq2 (rqs_H rq1 rq3 qs)`;;
let CFQ_H = REWRITE_RULE[GSYM cfq_H]
  (GEN_ALL (CONV_RULE (RAND_CONV (REWRITE_CONV[cfquiz_H])) (SPEC_ALL cfq_H)));;
let cv_inline_lets th =
  CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[LET_DEF; LET_END_DEF] th);;
cvt (cv_inline_lets CFQ_Y);; cvt (cv_inline_lets CFQ_H);;

let CFQUIZ_REC_CV =
  let c0 = SPEC_ALL (CONJUNCT1 cfquiz_rec) and c1 = SPEC_ALL (CONJUNCT2 cfquiz_rec) in
  let qs0 = rand (lhs (concl c0)) and qs1 = rand (lhs (concl c1)) in
  let ty = `:bool#num#question` in
  end_itlist CONJ (CONJUNCTS (cv_inst_var qs0 (cv_list_pats ty 2) c0) @
                   CONJUNCTS (cv_inst_var qs1 (cv_list_pats ty 3) c1));;
let CFQUIZ_REC_CV = REWRITE_RULE[GSYM cfq_Y; GSYM cfq_H] CFQUIZ_REC_CV;;
cvt CFQUIZ_REC_CV;;

(* cpradius2 and cfquiz with the ring size explicit, on cpadj_t            *)
let cpradius2_t = define
 `(cpradius2_t n (cp:(cpstep)list) 0 = F) /\
  (cpradius2_t n cp (SUC i) =
     (let cm0 = cfmask1_n n cp i in
      let mk1 = SND (cpadj_t cm0 cp) in
      let mk2 = SND (cpadj_t (FST cm0, mk1) cp) in
      if all_true mk2 then T else cpradius2_t n cp i))`;;
let cpradius_ok = define
 `(cpradius_ok n (cp:(cpstep)list) 0 = T) /\
  (cpradius_ok n cp (SUC i) <=>
     cpadj_ok (cfmask1_n n cp i) cp /\
     cpadj_ok (FST (cfmask1_n n cp i), SND (cpadj_t (cfmask1_n n cp i) cp)) cp /\
     cpradius_ok n cp i)`;;
do_list cvt [cpradius2_t; cpradius_ok];;
let CPRADIUS2_T = prove
 (`!k cp. cpradius_ok (cprsize cp) cp k
          ==> cpradius2 cp k = cpradius2_t (cprsize cp) cp k`,
  INDUCT_TAC THEN REWRITE_TAC[cpradius2; cpradius2_t; cpradius_ok] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; CFMASK1_N] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[CPADJ_T; ALL_TRUE]);;

let cfquiz_t = new_definition
 `cfquiz_t n (cf:(cpstep)list#(num)list) =
    if cpradius2_t n (cfprog cf) (cpksize (cfprog cf))
    then cfquiz_rec (cfprog cf) (REPLICATE n (F, 0, Qask0)) else noquiz`;;
let cfquiz_ok = new_definition
 `cfquiz_ok n (cf:(cpstep)list#(num)list) <=>
    cpradius_ok n (cfprog cf) (cpksize (cfprog cf))`;;
do_list cvt [cfquiz_t; cfquiz_ok];;
let CFQUIZ_T = prove
 (`!cf. cfquiz_ok (cprsize (cfprog cf)) cf
        ==> cfquiz cf = cfquiz_t (cprsize (cfprog cf)) cf`,
  GEN_TAC THEN REWRITE_TAC[cfquiz_ok; cfquiz; cfquiz_t; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN SIMP_TAC[CPRADIUS2_T]);;

(* ------------------------------------------------------------------------- *)
(* The quiz tree (quiztree.ml).  qzt_put1 takes the insertion as a function *)
(* argument; insert_path inserts a leaf along a path of arities instead.     *)
(* ------------------------------------------------------------------------- *)

do_list cvt [qzt_proper; isQztHubNode];;

let insert_path = define
 `(insert_path [] (q1,q2,q3) t = QztLeaf q1 q2 q3 t) /\
  (insert_path (CONS qa qs) l QztNil = QztNil) /\
  (insert_path (CONS qa qs) l (QztLeaf a b c t) = QztLeaf a b c t) /\
  (insert_path (CONS qa qs) l (QztNode t5 t6 t7 t8) =
     (if qa = Qa5 then QztNode (insert_path qs l t5) t6 t7 t8
      else if qa = Qa6 then QztNode t5 (insert_path qs l t6) t7 t8
      else if qa = Qa7 then QztNode t5 t6 (insert_path qs l t7) t8
      else if qa = Qa8 then QztNode t5 t6 t7 (insert_path qs l t8)
      else QztNode t5 t6 t7 t8)) /\
  (insert_path (CONS qa qs) l (QztHubNode t58 t9 t10 t11) =
     (if qa = Qa9 then QztHubNode t58 (insert_path qs l t9) t10 t11
      else if qa = Qa10 then QztHubNode t58 t9 (insert_path qs l t10) t11
      else if qa = Qa11 then QztHubNode t58 t9 t10 (insert_path qs l t11)
      else QztHubNode (insert_path (CONS qa qs) l t58) t9 t10 t11))`;;

let QZT_PUT1_PATH = prove
 (`!qa qs l. qzt_put1 qa (insert_path qs l) = insert_path (CONS qa qs) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MATCH_MP_TAC quiz_tree_INDUCT THEN
  REWRITE_TAC[qzt_put1; insert_path] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;
let INSERT_PATH_LEAF = prove
 (`!q1 q2 q3. insert_path [] (q1,q2,q3) = QztLeaf q1 q2 q3`,
  REWRITE_TAC[FUN_EQ_THM; insert_path]);;
let QZT_PUT3_PATH = prove
 (`!qa1 qa2 qa3 q1 q2 q3 t. qzt_put3 qa1 qa2 qa3 q1 q2 q3 t =
      insert_path [qa1; qa2; qa3] (q1,q2,q3) t`,
  REWRITE_TAC[qzt_put3; GSYM INSERT_PATH_LEAF; QZT_PUT1_PATH]);;
cvt insert_path;;
cvt QZT_PUT3_PATH;;
cvt qzt_put3rot;;
let QZT_PUT_E = prove
 (`!qa1 qa2 qa3 q1 q2 q3 t. qzt_put qa1 qa2 qa3 q1 q2 q3 t =
     if 8 < nat_of_qarity qa1 then qzt_put3 qa1 qa2 qa3 q1 q2 q3 t
     else qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qzt_put] THEN COND_CASES_TAC THEN
  REWRITE_TAC[]);;
cvt QZT_PUT_E;;

(* ------------------------------------------------------------------------- *)
(* Quiz tree lookups and reducible parts (redpart.ml).                       *)
(* ------------------------------------------------------------------------- *)

do_list cvt [qzt_size; qzt_get1; qzt_get2; qzt_get3; qzt_getr];;
let QZT_TRUNCATE_CLAUSES = prove
 (`qzt_truncate QztNil = QztNil /\
   (!q1 q2 q3 t. qzt_truncate (QztLeaf q1 q2 q3 t) = QztLeaf q1 q2 q3 t) /\
   (!t5 t6 t7 t8. qzt_truncate (QztNode t5 t6 t7 t8) = QztNode t5 t6 t7 t8) /\
   (!t9 t10 t11. qzt_truncate (QztHubNode QztNil t9 t10 t11) =
   QztHubNode QztNil t9 t10 t11) /\
   (!q1 q2 q3 t t9 t10 t11. qzt_truncate
   (QztHubNode (QztLeaf q1 q2 q3 t) t9 t10 t11) =
                            QztHubNode (QztLeaf q1 q2 q3 t) t9 t10 t11) /\
   (!t5 t6 t7 t8 t9 t10 t11. qzt_truncate
   (QztHubNode (QztNode t5 t6 t7 t8) t9 t10 t11) =
                             QztNode t5 t6 t7 t8) /\
   (!s9 s10 s11 s58 t9 t10 t11. qzt_truncate
   (QztHubNode (QztHubNode s58 s9 s10 s11) t9 t10 t11) =
                                QztHubNode (QztHubNode s58 s9 s10 s11)
                                t9 t10 t11)`,
  REWRITE_TAC[qzt_truncate]);;
cvt QZT_TRUNCATE_CLAUSES;;

do_list cvt [zp_zi; zp_pl; zp_pr; zproper; hub_range; zrange_loc; zrange;
             shift_part; zshiftl_aux; zshiftl; zshiftr_aux; zshiftr; zfanL; zfanR;
             zfanLt; zfanRt; zstepL_loc; zstepL; zstepR_loc; zstepR; zstepLt_loc;
             zstepLt; zstepRt_loc; zstepRt; topqa; fitqa; popqa; fitqzp];;

(* The cluster: red_rec is always redpart_loop qt ahub d; each red_X gets    *)
(* the data qt ahub d instead (rps_X), with red_pcons inlined.               *)
let rps_rr = `redpart_loop (rqt0:quiz_tree) (rah0:qarity) (rd0:num)`;;
let rps_list =
  [("red_popr_spoke",red_popr_spoke); ("red_popr_hat",red_popr_hat);
   ("red_popl_spoke",red_popl_spoke); ("red_popl_hat",red_popl_hat);
   ("red_popl_fan1l",red_popl_fan1l); ("red_popl_fan2l",red_popl_fan2l);
   ("red_popl_fan3l",red_popl_fan3l); ("red_popl_fan1r",red_popl_fan1r);
   ("red_popl_fan2r",red_popl_fan2r); ("red_popl_fan3r",red_popl_fan3r);
   ("red_pop_loc",red_pop_loc); ("red_pop",red_pop); ("red_popqzp",red_popqzp);
   ("red_qzt_leaf",red_qzt_leaf); ("red_zpart_cases",red_zpart_cases);
   ("red_zpart_step",red_zpart_step); ("red_zpart_rec",red_zpart_rec);
   ("red_zpart",red_zpart)];;

let rps_defs = map (fun (n,_) ->
    let c = mk_const(n,[]) in
    let atys = tl (fst(splitlist dest_fun_ty (type_of c))) in
    let xs = map (fun (i,ty) -> mk_var("x" ^ string_of_int i, ty))
                 (zip (1--length atys) atys) in
    let qt = `rqt0:quiz_tree` and ahub = `rah0:qarity` and d = `rd0:num` in
    let lhs = list_mk_comb(mk_var("rps_" ^ n,
                itlist (fun a t -> mk_fun_ty (type_of a) t) (qt::ahub::d::xs) bool_ty),
                qt::ahub::d::xs) in
    (n, new_definition (mk_eq(lhs, list_mk_comb(c, rps_rr :: xs))))) rps_list;;

let rps_clauses (n, th) =
  let cls = map SPEC_ALL (cv_clauses th) in
  let cls = map (INST [rps_rr, `red_rec:part->bool`]) cls in
  let fold = map (fun (_,d) -> GSYM (SPEC_ALL d)) rps_defs in
  let simp th =
    let th = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [red_pcons; LET_DEF; LET_END_DEF]
                                   THENC TOP_DEPTH_CONV BETA_CONV)) th in
    PURE_REWRITE_RULE fold th in
  end_itlist CONJ (map (fun c -> GEN_ALL (simp c)) cls);;

let REDPART_LOOP_CV = prove
 (`(!qt ahub p'. redpart_loop qt ahub 0 p' = F) /\
   (!qt ahub d p'. redpart_loop qt ahub (SUC d) p' =
       rps_red_zpart qt ahub d ahub qt (rev_part p') p')`,
  REWRITE_TAC[redpart_loop; GSYM (assoc "red_zpart" rps_defs)] THEN
  REWRITE_TAC[assoc "red_zpart" rps_defs]);;

let rps_measure off rank size vs =
  let d = mk_comb(`cval_sum_size`, el 2 vs) in
  let a = mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `2` d)
                   (mk_small_numeral off) in
  let c = match size with None -> `0` | Some i -> mk_comb(`cval_sum_size`, el i vs) in
  mk_pair(a, mk_pair(mk_small_numeral rank, c));;

let RPS_CLUSTER = cv_translate_cluster
  (("cv_redpart_loop", REDPART_LOOP_CV, rps_measure 0 20 None) ::
   map (fun (n,_) ->
     let rank, size =
       (match n with
          "red_zpart" -> 19, None
        | "red_zpart_rec" -> 18, Some 8
        | "red_zpart_step" -> 17, None
        | "red_zpart_cases" -> 16, None
        | "red_qzt_leaf" -> 15, Some 10
        | "red_popqzp" -> 14, Some 6
        | "red_pop" -> 13, None
        | "red_pop_loc" -> 12, None
        | _ -> 1, None) in
     ("cv_rps_" ^ n, rps_clauses (n, assoc n rps_list), rps_measure 1 rank size))
   rps_list);;

cvt redpart;;

(* ------------------------------------------------------------------------- *)
(* Discharge rules (discharge.ml).                                           *)
(* ------------------------------------------------------------------------- *)

(* simultaneous lets as nested lets (keeps the sharing)                       *)
let rec cv_simlet_conv2 tm =
  let h,args = strip_comb tm in
  if is_const h && fst(dest_const h) = "LET" && length args >= 3 then
    let f = hd args and x = el 1 args and rest = tl(tl args) in
    let a,body = dest_abs f in
    let a' = variant (frees (list_mk_comb(f, x :: rest))) a in
    let body' = vsubst [a',a] body in
    let inner = list_mk_comb(mk_icomb(mk_const("LET",[]), body'), rest) in
    let letc = mk_icomb(mk_const("LET",[]),
                 mk_abs(a', mk_icomb(mk_const("LET_END",[]), inner))) in
    prove(mk_eq(tm, mk_comb(letc, x)), REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
          CONV_TAC(DEPTH_CONV BETA_CONV) THEN REFL_TAC)
  else failwith "cv_simlet_conv2";;
let cv_nest_lets th = end_itlist CONJ (map (fun c ->
    GEN_ALL (CONV_RULE (RAND_CONV (TOP_DEPTH_CONV cv_simlet_conv2)) c))
    (cv_clauses th));;

do_list cv_add_unfold
  [drule1; drule2; drule2_P; drule3; drule3_P; drule4; drule4_P; drule5;
   drule6; drule7; drule8; drule9; drule10; drule10_P; drule11; drule12;
   drule13; drule14; drule15; drule16; drule17; drule18; drule19; drule20;
   drule21; drule22; drule23; drule24; drule25; drule26; drule27; drule28;
   drule29; drule30; drule31; drule31_P; drule32; base_drules];;

let SYM_DRULE_CV = prove
 (`!p. sym_drule p =
       let k = size_part p - 1 in
       rot_part k (rot_part k (rot_part k (rot_part k (rot_part k
         (mirror_part p)))))`,
  GEN_TAC THEN REWRITE_TAC[sym_drule; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[ARITH_RULE `5 = SUC(SUC(SUC(SUC(SUC 0))))`; ITER]);;
do_list cvt [SYM_DRULE_CV; symmetrize_drules];;
cv_add_unfold the_drules;;

let psd = define
 `(psd nhub [] = []) /\
  (psd nhub (CONS p r) = if size_part p = nhub then CONS p (psd nhub r)
                         else psd nhub r)`;;
let PICK_SOURCE_PSD = prove
 (`!nhub r. pick_source_drules nhub r = psd nhub r`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[pick_source_drules; FILTER; psd] THEN
  REWRITE_TAC[GSYM pick_source_drules] THEN ASM_REWRITE_TAC[]);;
do_list cvt [psd; sort_drules_rec; sort_drules; dboundK];;

(* the drule forks for hub sizes 5..11: the converse parts of the explicit  *)
(* rules by rewriting                                                        *)
let THE_DRULES_VALUE = cv_eval `the_drules`;;
let cv_drop_num_conv tm =
  match strip_comb tm with
    (c,[n;p]) when is_const c && fst(dest_const c) = "drop_part" &&
                   is_numeral n && not (n = `0`) ->
      (RATOR_CONV (RAND_CONV num_CONV) THENC REWRITE_CONV[drop_part]) tm
  | _ -> failwith "cv_drop_num_conv";;
let cv_converse_step =
  REWRITE_CONV[converse_part; conv_part4; conv_part5; conv_part12; conv_part3;
               cp4_aux; cp12_auxA; cp12_auxB; cp12_auxC; cp3_1; cp3_2; cp3_3;
               pcons_s; drop_part; LET_DEF; LET_END_DEF; FST; SND; COND_CLAUSES;
               distinctness "prange"; GSYM (distinctness "prange")] THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  TRY_CONV (ONCE_DEPTH_CONV cv_drop_num_conv);;
let cv_converse_conv = REPEATC (CHANGED_CONV cv_converse_step);;
let CONVERSE_VALUES =
  map (fun p -> cv_converse_conv (mk_comb(`converse_part`, p)))
      (dest_list (rhs (concl THE_DRULES_VALUE)));;
let pick_target_cv = define
 `(pick_target_cv nhub [] = []) /\
  (pick_target_cv nhub (CONS (rq:prange#part) l) =
     if mem_range (FST rq) nhub then CONS (SND rq) (pick_target_cv nhub l)
     else pick_target_cv nhub l)`;;
let PICK_TARGET_CV = prove
 (`!nhub l. pick_target_drules nhub l = pick_target_cv nhub (MAP converse_part l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[pick_target_drules; pick_target_cv; MAP]);;
let drule_conv_data = new_definition
 `drule_conv_data = MAP converse_part the_drules`;;
let DRULE_CONV_DATA =
  REWRITE_RULE CONVERSE_VALUES (REWRITE_RULE[THE_DRULES_VALUE; MAP] drule_conv_data);;
let the_drule_fork_cv = new_definition
 `the_drule_fork_cv nhub = (psd nhub the_drules, pick_target_cv nhub drule_conv_data)`;;
let THE_DRULE_FORK_CV = prove
 (`!nhub. the_drule_fork nhub = the_drule_fork_cv nhub`,
  REWRITE_TAC[the_drule_fork; the_drule_fork_cv; PICK_SOURCE_PSD; PICK_TARGET_CV;
              drule_conv_data]);;
cvt pick_target_cv;;
cv_add_unfold DRULE_CONV_DATA;;
cvt the_drule_fork_cv;;
cv_fun_thms := ("the_drule_fork",
   REWRITE_RULE[GSYM THE_DRULE_FORK_CV] (assoc "the_drule_fork_cv" (!cv_fun_thms)))
   :: !cv_fun_thms;;

(* ------------------------------------------------------------------------- *)
(* The quiz tree (present.ml the_quiz_tree), with the ring sizes of the      *)
(* configurations given by cprsize_conv.                                     *)
(* ------------------------------------------------------------------------- *)

do_list cvt [normq; isQaskLR; qLR_l; qLR_r];;
cvt (cv_nest_lets store_qz_aux);;
do_list cvt [store_qz; store_cf_qz];;
let QZT_EMPTY_VALUE =
  CONV_RULE (RAND_CONV (REWRITE_CONV[LET_DEF; LET_END_DEF] THENC
                        TOP_DEPTH_CONV BETA_CONV)) qzt_empty;;
cv_add_unfold QZT_EMPTY_VALUE;;

let cfqt_t = define
 `(cfqt_t qt [] = qt) /\
  (cfqt_t qt (CONS (((cf:(cpstep)list#(num)list),sy),n) rest) =
     let qt2 = store_cf_qz (cfquiz_t n cf) sy qt in
     if isQztHubNode qt2 then cfqt_t qt2 rest else QztNil)`;;
let cfqt_ok = define
 `(cfqt_ok [] = T) /\
  (cfqt_ok (CONS (((cf:(cpstep)list#(num)list),(sy:bool)),(n:num)) rest) <=>
     cfquiz_ok n cf /\ cfqt_ok rest)`;;
do_list cvt [cfqt_t; cfqt_ok];;
let CFQT_T = prove
 (`!l qt. ALL (\x. SND x = cprsize (cfprog (FST (FST x)))) l /\ cfqt_ok l
          ==> cfquiz_tree_rec qt (MAP FST l) = cfqt_t qt l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; cfquiz_tree_rec; cfqt_t] THEN
  STRUCT_CASES_TAC (ISPEC `h:((cpstep list # num list) # bool) # num` PAIR_SURJECTIVE) THEN
  STRUCT_CASES_TAC (ISPEC `x:(cpstep list # num list) # bool` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[cfqt_t; cfqt_ok; ALL; FST; SND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[CFQUIZ_T]);;

let cv_config_defs_u = [cf001;cf002;cf003;cf004;cf005;cf006;cf007;cf008;cf009;cf010;cf011;cf012;cf013;cf014;cf015;cf016;cf017;cf018;cf019;cf020;cf021;cf022;cf023;cf024;cf025;cf026;cf027;cf028;cf029;cf030;cf031;cf032;cf033;cf034;cf035;cf036;cf037;cf038;cf039;cf040;cf041;cf042;cf043;cf044;cf045;cf046;cf047;cf048;cf049;cf050;cf051;cf052;cf053;cf054;cf055;cf056;cf057;cf058;cf059;cf060;cf061;cf062;cf063;cf064;cf065;cf066;cf067;cf068;cf069;cf070;cf071;cf072;cf073;cf074;cf075;cf076;cf077;cf078;cf079;cf080;cf081;cf082;cf083;cf084;cf085;cf086;cf087;cf088;cf089;cf090;cf091;cf092;cf093;cf094;cf095;cf096;cf097;cf098;cf099;cf100;cf101;cf102;cf103;cf104;cf105;cf106;cf107;cf108;cf109;cf110;cf111;cf112;cf113;cf114;cf115;cf116;cf117;cf118;cf119;cf120;cf121;cf122;cf123;cf124;cf125;cf126;cf127;cf128;cf129;cf130;cf131;cf132;cf133;cf134;cf135;cf136;cf137;cf138;cf139;cf140;cf141;cf142;cf143;cf144;cf145;cf146;cf147;cf148;cf149;cf150;cf151;cf152;cf153;cf154;cf155;cf156;cf157;cf158;cf159;cf160;cf161;cf162;cf163;cf164;cf165;cf166;cf167;cf168;cf169;cf170;cf171;cf172;cf173;cf174;cf175;cf176;cf177;cf178;cf179;cf180;cf181;cf182;cf183;cf184;cf185;cf186;cf187;cf188;cf189;cf190;cf191;cf192;cf193;cf194;cf195;cf196;cf197;cf198;cf199;cf200;cf201;cf202;cf203;cf204;cf205;cf206;cf207;cf208;cf209;cf210;cf211;cf212;cf213;cf214;cf215;cf216;cf217;cf218;cf219;cf220;cf221;cf222;cf223;cf224;cf225;cf226;cf227;cf228;cf229;cf230;cf231;cf232;cf233;cf234;cf235;cf236;cf237;cf238;cf239;cf240;cf241;cf242;cf243;cf244;cf245;cf246;cf247;cf248;cf249;cf250;cf251;cf252;cf253;cf254;cf255;cf256;cf257;cf258;cf259;cf260;cf261;cf262;cf263;cf264;cf265;cf266;cf267;cf268;cf269;cf270;cf271;cf272;cf273;cf274;cf275;cf276;cf277;cf278;cf279;cf280;cf281;cf282;cf283;cf284;cf285;cf286;cf287;cf288;cf289;cf290;cf291;cf292;cf293;cf294;cf295;cf296;cf297;cf298;cf299;cf300;cf301;cf302;cf303;cf304;cf305;cf306;cf307;cf308;cf309;cf310;cf311;cf312;cf313;cf314;cf315;cf316;cf317;cf318;cf319;cf320;cf321;cf322;cf323;cf324;cf325;cf326;cf327;cf328;cf329;cf330;cf331;cf332;cf333;cf334;cf335;cf336;cf337;cf338;cf339;cf340;cf341;cf342;cf343;cf344;cf345;cf346;cf347;cf348;cf349;cf350;cf351;cf352;cf353;cf354;cf355;cf356;cf357;cf358;cf359;cf360;cf361;cf362;cf363;cf364;cf365;cf366;cf367;cf368;cf369;cf370;cf371;cf372;cf373;cf374;cf375;cf376;cf377;cf378;cf379;cf380;cf381;cf382;cf383;cf384;cf385;cf386;cf387;cf388;cf389;cf390;cf391;cf392;cf393;cf394;cf395;cf396;cf397;cf398;cf399;cf400;cf401;cf402;cf403;cf404;cf405;cf406;cf407;cf408;cf409;cf410;cf411;cf412;cf413;cf414;cf415;cf416;cf417;cf418;cf419;cf420;cf421;cf422;cf423;cf424;cf425;cf426;cf427;cf428;cf429;cf430;cf431;cf432;cf433;cf434;cf435;cf436;cf437;cf438;cf439;cf440;cf441;cf442;cf443;cf444;cf445;cf446;cf447;cf448;cf449;cf450;cf451;cf452;cf453;cf454;cf455;cf456;cf457;cf458;cf459;cf460;cf461;cf462;cf463;cf464;cf465;cf466;cf467;cf468;cf469;cf470;cf471;cf472;cf473;cf474;cf475;cf476;cf477;cf478;cf479;cf480;cf481;cf482;cf483;cf484;cf485;cf486;cf487;cf488;cf489;cf490;cf491;cf492;cf493;cf494;cf495;cf496;cf497;cf498;cf499;cf500;cf501;cf502;cf503;cf504;cf505;cf506;cf507;cf508;cf509;cf510;cf511;cf512;cf513;cf514;cf515;cf516;cf517;cf518;cf519;cf520;cf521;cf522;cf523;cf524;cf525;cf526;cf527;cf528;cf529;cf530;cf531;cf532;cf533;cf534;cf535;cf536;cf537;cf538;cf539;cf540;cf541;cf542;cf543;cf544;cf545;cf546;cf547;cf548;cf549;cf550;cf551;cf552;cf553;cf554;cf555;cf556;cf557;cf558;cf559;cf560;cf561;cf562;cf563;cf564;cf565;cf566;cf567;cf568;cf569;cf570;cf571;cf572;cf573;cf574;cf575;cf576;cf577;cf578;cf579;cf580;cf581;cf582;cf583;cf584;cf585;cf586;cf587;cf588;cf589;cf590;cf591;cf592;cf593;cf594;cf595;cf596;cf597;cf598;cf599;cf600;cf601;cf602;cf603;cf604;cf605;cf606;cf607;cf608;cf609;cf610;cf611;cf612;cf613;cf614;cf615;cf616;cf617;cf618;cf619;cf620;cf621;cf622;cf623;cf624;cf625;cf626;cf627;cf628;cf629;cf630;cf631;cf632;cf633];;
let CPRSIZE_CONFIGS = map (fun cfdef ->
    let cf = lhs (concl cfdef) in
    let cp = fst (dest_pair (rhs (concl cfdef))) in
    TRANS (REWRITE_CONV[cfprog; cfdef; FST] (mk_comb(`cprsize`, mk_comb(`cfprog`, cf))))
          (cprsize_conv (mk_comb (`cprsize`, cp)))) cv_config_defs_u;;
let the_cf_sizes = new_definition
  (mk_eq(`the_cf_sizes:num list`,
         mk_list(map (fun th -> rhs(concl th)) CPRSIZE_CONFIGS, `:num`)));;
let cf_triples = new_definition
  `cf_triples = ZIP (ZIP the_configs the_configs_sym) the_cf_sizes`;;
let MAP_FST_ZIP_CV = prove
 (`!l1:A list l2:B list. LENGTH l1 = LENGTH l2 ==> MAP FST (ZIP l1 l2) = l1`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ZIP; MAP; LENGTH; NOT_SUC; SUC_INJ; FST]);;
let CF_TRIPLES_FST = prove
 (`MAP FST cf_triples = ZIP the_configs the_configs_sym`,
  REWRITE_TAC[cf_triples] THEN MATCH_MP_TAC MAP_FST_ZIP_CV THEN
  REWRITE_TAC[the_configs; the_configs_sym; the_cf_sizes; ZIP; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let CF_TRIPLES_SIZES = prove
 (`ALL (\x. SND x = cprsize (cfprog (FST (FST x)))) cf_triples`,
  REWRITE_TAC[cf_triples; the_configs; the_configs_sym; the_cf_sizes; ZIP; ALL;
              FST; SND] THEN REWRITE_TAC CPRSIZE_CONFIGS);;
let CF_TRIPLES_LIST = REWRITE_CONV[cf_triples; the_configs; the_configs_sym;
                                    the_cf_sizes; ZIP] `cf_triples`;;
do_list cv_add_unfold (cv_config_defs_u @ [CF_TRIPLES_LIST]);;
let CF_TRIPLES_OK = EQT_ELIM (cv_eval `cfqt_ok cf_triples`);;
let THE_QUIZ_TREE_CV = prove
 (`the_quiz_tree = cfqt_t qzt_empty cf_triples`,
  REWRITE_TAC[the_quiz_tree; cfquiz_tree; GSYM CF_TRIPLES_FST] THEN
  MATCH_MP_TAC CFQT_T THEN REWRITE_TAC[CF_TRIPLES_SIZES; CF_TRIPLES_OK]);;
(* evaluate it once; the quiz tree's code is then its value                 *)
let THE_QUIZ_TREE_ENC =
  let th1 = cv_tr (fun _ -> failwith "")
              (mk_comb(`cv_of_quiz_tree`, rhs(concl THE_QUIZ_TREE_CV))) in
  let th2 = cv_compute (rand(concl th1)) in
  TRANS (AP_TERM `cv_of_quiz_tree` THE_QUIZ_TREE_CV) (TRANS th1 th2);;
let cv_the_quiz_tree = new_definition
  (mk_eq(`cv_the_quiz_tree:cval`, rhs(concl THE_QUIZ_TREE_ENC)));;
cv_fun_thms := ("the_quiz_tree", TRANS THE_QUIZ_TREE_ENC (SYM cv_the_quiz_tree))
               :: !cv_fun_thms;;
cv_code := cv_the_quiz_tree :: !cv_code;;

(* ------------------------------------------------------------------------- *)
(* The discharge bound checks and hubcaps (hubcap.ml), with the reducibility *)
(* predicate redp fixed to redpart the_quiz_tree.                            *)
(* ------------------------------------------------------------------------- *)

let cv_rp = `redpart the_quiz_tree`;;
(* f redp args = f_rp args, and the clauses of f_rp                         *)
let cv_specialize_redp name th =
  let c = mk_const(name, []) in
  let atys,rty0 = splitlist dest_fun_ty (type_of c) in
  let k = index `:part->bool` atys in
  let otys = map snd (filter (fun (i,_) -> not (i = k))
                        (zip (0--(length atys - 1)) atys)) in
  let xs = map (fun (i,ty) -> mk_var("y" ^ string_of_int i, ty))
               (zip (1--length otys) otys) in
  let rty = itlist (fun a t -> mk_fun_ty (type_of a) t) xs rty0 in
  let xs1,xs2 = chop_list k xs in
  let def = new_definition (mk_eq(list_mk_comb(mk_var(name ^ "_rp", rty), xs),
                                  list_mk_comb(c, xs1 @ [cv_rp] @ xs2))) in
  (def, th);;
let cv_rp_clauses defs th =
  let cls = map (INST [cv_rp, `redp:part->bool`] o SPEC_ALL) (cv_clauses th) in
  let fold = map (fun d -> GSYM (SPEC_ALL d)) defs in
  end_itlist CONJ (map (fun c -> GEN_ALL (PURE_REWRITE_RULE fold c)) cls);;

let nth0_cv = define
 `(nth0_cv ([]:num list) i = 0) /\
  (nth0_cv (CONS h t) i = if i = 0 then h else nth0_cv t (i - 1))`;;
let NTH0_CV = prove
 (`!v i. nth0 v i = nth0_cv v i`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[nth0; nth0_cv; LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; EL; HD; TL; LT_0; LT_SUC; SUC_SUB1; nth0]);;
do_list cvt [nth0_cv; incr_nth; check_unfit; tally_hubcap];;
cvt (cv_nest_lets (REWRITE_RULE[NTH0_CV] hubcap_cover_rec));;
cvt (cv_nest_lets (REWRITE_RULE[NTH0_CV] hubcap_cover));;
do_list cvt [hubcap_rot; hub_subn];;

let CHECK_DBOUND1_REC_RP_DEF = fst (cv_specialize_redp "check_dbound1_rec" check_dbound1_rec);;
let CHECK_DBOUND1_REC_RP =
  cv_split_clauses 1 (cv_rp_clauses [CHECK_DBOUND1_REC_RP_DEF] check_dbound1_rec);;
cvt (cv_nest_lets CHECK_DBOUND1_REC_RP);;
let CHECK_DBOUND1_RP_DEF = fst (cv_specialize_redp "check_dbound1" check_dbound1);;
cvt (cv_rp_clauses [CHECK_DBOUND1_REC_RP_DEF; CHECK_DBOUND1_RP_DEF] check_dbound1);;

(* Coq unavoidability.v:33: the four closed boolean evaluations             *)
let THE_DBOUND1_CHECK = prove
 (`!n. 5 <= n /\ n <= 8
       ==> check_dbound1 (redpart the_quiz_tree) (the_drule_fork n)
       (pcons_ n) 5`,
  REWRITE_TAC[ARITH_RULE
    `5 <= n /\ n <= 8 <=> n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  REWRITE_TAC[GSYM CHECK_DBOUND1_RP_DEF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  CONV_TAC(fun tm -> cv_eval tm));;

(* single and dual target bound checks; num_of_int is int_pos under v >= 0  *)
let CHECK_DBOUND2_REC_RP_DEF =
  fst (cv_specialize_redp "check_dbound2_rec" check_dbound2_rec);;
let CHECK_DBOUND2_REC_RP =
  cv_split_clauses 1 (cv_rp_clauses [CHECK_DBOUND2_REC_RP_DEF] check_dbound2_rec);;
cvt (cv_nest_lets CHECK_DBOUND2_REC_RP);;
let check_dbound2_t = define
 `check_dbound2_t rf p (b:int) =
    let sdt = sort_drules p (SND rf) in
    let sds = sort_drules p (FST rf) in
    let v = &(FST sds) - &(FST sdt) + b in
    if v < &0 then F
    else check_dbound2_rec_rp p (SND sdt) (SND sds) [] (int_pos v)
           (LENGTH (SND sdt) + 2)`;;
let CV_INT_POS_TAC defs =
  REPEAT GEN_TAC THEN REWRITE_TAC(defs @ [LET_DEF; LET_END_DEF]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[INT_NOT_LT]) THEN
  ASM_SIMP_TAC[NUM_OF_INT_POS];;
let CHECK_DBOUND2_T = prove
 (`!rf p b. check_dbound2 (redpart the_quiz_tree) rf p b = check_dbound2_t rf p b`,
  CV_INT_POS_TAC [check_dbound2; check_dbound2_t; CHECK_DBOUND2_REC_RP_DEF]);;
cvt check_dbound2_t;;

let CHECK_2DBOUND2_REC_RP_DEF =
  fst (cv_specialize_redp "check_2dbound2_rec" check_2dbound2_rec);;
let CHECK_2DBOUND2_REC_RP =
  cv_split_clauses 3 (cv_rp_clauses [CHECK_2DBOUND2_REC_RP_DEF] check_2dbound2_rec);;
cvt (cv_nest_lets CHECK_2DBOUND2_REC_RP);;
let check_2dbound2_t = define
 `check_2dbound2_t nhub rf p1 i (b:int) =
    let p2 = rot_part i p1 in
    let sd1t = sort_drules p1 (SND rf) in
    let sd1s = sort_drules p1 (FST rf) in
    let sd2t = sort_drules p2 (SND rf) in
    let sd2s = sort_drules p2 (FST rf) in
    let v = &(FST sd1s + FST sd2s) - &(FST sd1t + FST sd2t) + b in
    if v < &0 then F
    else check_2dbound2_rec_rp nhub p1 p2 (SND sd1t) (SND sd1s) [] (SND sd2t)
           (SND sd2s) [] i (int_pos v) (LENGTH (SND sd1t) + (LENGTH (SND sd2t) + 3))`;;
let CHECK_2DBOUND2_T = prove
 (`!nhub rf p1 i b. check_2dbound2 nhub (redpart the_quiz_tree) rf p1 i b =
                    check_2dbound2_t nhub rf p1 i b`,
  CV_INT_POS_TAC [check_2dbound2; check_2dbound2_t; CHECK_2DBOUND2_REC_RP_DEF]);;
cvt check_2dbound2_t;;

let HUBCAP_FIT_RP_DEF = fst (cv_specialize_redp "hubcap_fit" hubcap_fit);;
cvt (PURE_REWRITE_RULE[CHECK_DBOUND2_T; CHECK_2DBOUND2_T]
       (cv_rp_clauses [HUBCAP_FIT_RP_DEF] hubcap_fit));;
