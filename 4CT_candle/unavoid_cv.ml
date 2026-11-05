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
