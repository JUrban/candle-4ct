(* ========================================================================= *)
(* 4CT_candle/kempe_cv.ml                                                    *)
(*                                                                           *)
(* cv translations (cvtrans.ml) of the colour, colour-tree and chromogram-  *)
(* tree functions and of the Kempe closure (ctree.ml ... kempetree.ml), for  *)
(* the Birkhoff checks (birkhoff_cv.ml) and the reducibility check           *)
(* (part2_cv.ml) by Kernel.compute.  Lambda-free, first-order forms are      *)
(* proved here where the definitions use continuations or partial functions *)
(* (several follow 4CT/part2_eval.ml).                                       *)
(* ========================================================================= *)

needs "4CT/kempetree.ml";;
needs "4CT_candle/cvtrans.ml";;

let cvt th = ignore (cv_translate th);;
let cvt_as n th = ignore (cv_translate_as n th);;

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

do_list (fun n -> ignore (cv_register_type n))
  ["color"; "edge_perm"; "cpstep"; "ctree"; "ctree_pair"; "gtree";
   "gtree_pair"; "bit_stack"; "gram_symbol"; "gtree_restriction";
   "ctree_restriction"];;

do_list (fun n -> ignore (cv_prove_inj n))
  ["color"; "edge_perm"; "cpstep"; "bit_stack"; "gram_symbol"; "ctree";
   "gtree"];;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

do_list cvt [LENGTH; APPEND; REVERSE];;
cvt_as "cv_MEM_color" (INST_TYPE [`:color`,`:A`] MEM);;

let last_of = define
 `(last_of (h:A) [] = h) /\ (last_of h (CONS x t) = last_of x t)`;;
let LAST_LAST_OF = prove
 (`!t h:A. LAST (CONS h t) = last_of h t`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LAST; last_of];
    GEN_TAC THEN ONCE_REWRITE_TAC[LAST] THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; last_of]]);;
cvt last_of;;

(* ------------------------------------------------------------------------- *)
(* Colours and traces (color.ml).                                            *)
(* ------------------------------------------------------------------------- *)

do_list cvt [addc_DEF; permc_DEF; edge_rot_DEF; cbit0; cbit1; ccons; inv_eperm;
             ptrace; sumt; ctrace; permt];;
cvt (cv_split_def 0 head_color);;
cvt (cv_split_def 0 proper_trace);;
cvt (REWRITE_RULE[LAST_LAST_OF] (cv_split_def 0 trace_DEF));;
do_list cvt [untrace; even_tail];;
cvt (cv_split_def 0 ttail);;
do_list cvt [even_trace; etrace_perm; etrace; etail; eptrace];;

(* ------------------------------------------------------------------------- *)
(* Colour trees (ctree.ml).                                                  *)
(* ------------------------------------------------------------------------- *)

cvt palette;;
do_list cvt [ctree_empty; ctree_leaf; ctree_empty_node; ctree_lsub; ctree_msub;
             ctree_rsub];;

let CTREE_SEL_CLAUSES = prove
 (`(!t1 t2 t3. ctree_sel (CtreeNode t1 t2 t3) Color0 = CtreeEmpty /\
               ctree_sel (CtreeNode t1 t2 t3) Color1 = t1 /\
               ctree_sel (CtreeNode t1 t2 t3) Color2 = t2 /\
               ctree_sel (CtreeNode t1 t2 t3) Color3 = t3) /\
   (!t c. ctree_sel (CtreeLeaf t) c = CtreeEmpty) /\
   (!c. ctree_sel CtreeEmpty c = CtreeEmpty)`,
  REWRITE_TAC[ctree_sel; palette]);;
cvt CTREE_SEL_CLAUSES;;
cvt ctree_proper;;
cvt (cv_split_clauses 1 ctree_sub);;
cvt ctree_mem;;
cv_add_unfold ctree_empty_pair;;
cv_add_unfold ctree_simple_leaf;;
cvt ctree_pair_sub;;

let CTREE_LEAF_OF_CLAUSES = prove
 (`ctree_leaf_of 0 = CtreeEmpty /\
   (!n. ctree_leaf_of (SUC n) = CtreeLeaf (ctree_leaf_of n))`,
  REWRITE_TAC[ctree_leaf_of; ITER]);;
cvt CTREE_LEAF_OF_CLAUSES;;
do_list cvt [ctree_cons; ctree_cons0; ctree_cons1; ctree_cons2; ctree_cons3];;

let CTREE_CONS_E_CLAUSES = prove
 (`!t. ctree_cons_e Color0 t = ctree_cons0 t /\
       ctree_cons_e Color1 t = ctree_cons1 t /\
       ctree_cons_e Color2 t = ctree_cons2 t /\
       ctree_cons_e Color3 t = ctree_cons3 t`,
  REWRITE_TAC[ctree_cons_e; palette]);;
cvt CTREE_CONS_E_CLAUSES;;

let CTREE_OF_TTAIL_CLAUSES = prove
 (`ctree_of_ttail [] = ctree_simple_leaf /\
   (!c et. ctree_of_ttail (CONS c et) = ctree_cons_e c (ctree_of_ttail et))`,
  REWRITE_TAC[ctree_of_ttail; ITLIST]);;
cvt CTREE_OF_TTAIL_CLAUSES;;
do_list cvt [ctree_union; ctree_rotl; ctree_rotr; ctree_cons_rot;
             ctree_union_rotlr; ctree_rotlr; ctree_disjoint];;

(* ------------------------------------------------------------------------- *)
(* Helpers: eta-expanded clauses (part2_eval.ml) and equality rewrites.      *)
(* ------------------------------------------------------------------------- *)

let rec cv_eta_expand_eq th =
  let r = rhs (concl th) in
  if is_abs r then
    let v = variant (frees (concl th)) (bndvar r) in
    cv_eta_expand_eq (CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th v))
  else th;;
let cv_eta th = end_itlist CONJ
  (map (fun c -> GEN_ALL (cv_eta_expand_eq (SPEC_ALL c))) (CONJUNCTS th));;

let cv_eq_thm tyname =
  let ty = mk_type(tyname, []) in
  let refl = INST_TYPE [ty, `:A`] REFL_CLAUSE in
  let ds = try CONJUNCTS (distinctness tyname) with Failure _ -> [] in
  let dist = flat (map (fun th ->
      let th' = SPEC_ALL th in
      [EQF_INTRO th'; EQF_INTRO (GSYM th')]) ds) in
  let inj = try CONJUNCTS (injectivity tyname) with Failure _ -> [] in
  end_itlist CONJ (refl :: dist @ inj);;

let EQ_COLOR = cv_eq_thm "color" and EQ_GRAM_SYMBOL = cv_eq_thm "gram_symbol";;

(* ------------------------------------------------------------------------- *)
(* Chromogram trees (gtree.ml).                                              *)
(* ------------------------------------------------------------------------- *)

do_list cvt [gtree_empty; gtree_isleaf; gtree_sel; gtree_leaf_mem; gtree_mem;
             gtree_empty_and; gtree_empty4];;
cv_add_unfold empty_gtree_pair;;
do_list cvt [gtree_pair_sub; gtree_cons_pairs];;

(* ------------------------------------------------------------------------- *)
(* Restrictions (ctreerestrict.ml, gtreerestrict.ml), first-order forms     *)
(* (part2_eval.ml).                                                          *)
(* ------------------------------------------------------------------------- *)

let GTR_CONS_FO = prove
 (`(!bs r. gtr_cons bs CtreeEmpty r = r) /\
   (!bs lf r. gtr_cons bs (CtreeLeaf lf) r = GtrCons bs (CtreeLeaf lf) r) /\
   (!bs t1 t2 t3 r. gtr_cons bs (CtreeNode t1 t2 t3) r =
   GtrCons bs (CtreeNode t1 t2 t3) r)`,
  REWRITE_TAC[gtr_cons; ctree_empty]);;
let CTR_CONS_FO = prove
 (`(!bs r. ctr_cons bs GtreeEmpty r = r) /\
   (!bs t0 t1 t2 t3 r. ctr_cons bs (GtreeNode t0 t1 t2 t3) r =
   CtrCons bs (GtreeNode t0 t1 t2 t3) r) /\
   (!bs r. ctr_cons bs GtreeLeaf0 r = CtrCons bs GtreeLeaf0 r) /\
   (!bs r. ctr_cons bs GtreeLeaf1 r = CtrCons bs GtreeLeaf1 r) /\
   (!bs r. ctr_cons bs GtreeLeaf2 r = CtrCons bs GtreeLeaf2 r) /\
   (!bs r. ctr_cons bs GtreeLeaf3 r = CtrCons bs GtreeLeaf3 r) /\
   (!bs r. ctr_cons bs GtreeLeaf01 r = CtrCons bs GtreeLeaf01 r) /\
   (!bs r. ctr_cons bs GtreeLeaf12 r = CtrCons bs GtreeLeaf12 r) /\
   (!bs r. ctr_cons bs GtreeLeaf13 r = CtrCons bs GtreeLeaf13 r) /\
   (!bs r. ctr_cons bs GtreeLeaf23 r = CtrCons bs GtreeLeaf23 r)`,
  REWRITE_TAC[ctr_cons; gtree_empty]);;
cvt GTR_CONS_FO;; cvt CTR_CONS_FO;;
do_list cvt [gtr_isnil; cons_pop; ctr_cons_pop; ctr_isnil; ctree_leaf_child;
             ctree_decr; ctree_if_e; ctree_leaf_pair; ctree_cons_pairs];;

let gtr_split_acc = define
 `(gtr_split_acc (CtreeNode t1 t2 t3) bs
     (q:gtree_restriction#gtree_restriction#gtree_restriction
      #gtree_restriction) =
     (gtr_cons (Bpush0 bs) t2 (gtr_cons (Bpush1 bs) t3 (FST q)),
      gtr_cons bs t1 (FST (SND q)),
      cons_pop bs t2 t3 (FST (SND (SND q))),
      cons_pop bs t3 t2 (SND (SND (SND q))))) /\
  (gtr_split_acc (CtreeLeaf lf) bs q = q) /\
  (gtr_split_acc CtreeEmpty bs q = q)`;;
let gtr_split4 = define
 `(gtr_split4 GtrNil
 (q:gtree_restriction#gtree_restriction#gtree_restriction#gtree_restriction) =
 q) /\
  (gtr_split4 (GtrCons bs t r) q = gtr_split4 r (gtr_split_acc t bs q))`;;
let gtr_apply4 = new_definition
 `gtr_apply4
 (continue:gtree_restriction->gtree_restriction->gtree_restriction
  ->gtree_restriction->A)
             (q:gtree_restriction#gtree_restriction#gtree_restriction
              #gtree_restriction) =
    continue (FST q) (FST (SND q)) (FST (SND (SND q))) (SND (SND (SND q)))`;;
let GTR_SPLIT_FN_FO = prove
 (`!r (continue:gtree_restriction->gtree_restriction->gtree_restriction
  ->gtree_restriction->A) r0 r1 r2 r3.
     gtr_split_fn r continue r0 r1 r2 r3 =
     gtr_apply4 continue (gtr_split4 r (r0,r1,r2,r3))`,
  MATCH_MP_TAC gtree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[gtr_split_fn; gtr_split4; gtr_apply4; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:ctree`; `r:gtree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[gtr_split_fn; gtr_split4] THEN
    STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    ASM_REWRITE_TAC[case_ctree_node; gtr_split_acc; FST; SND]]);;
cvt gtr_split_acc;; cvt gtr_split4;;

let gtree_restrict_q = new_definition
 `gtree_restrict_q t0 t1 t2 t3
  (q:gtree_restriction#gtree_restriction#gtree_restriction#gtree_restriction) =
    gtree_cons_pairs (GtreeNode t0 t1 t2 t3)
      (gtree_restrict t0 (FST q)) (gtree_restrict t1 (FST (SND q)))
      (gtree_restrict t2 (FST (SND (SND q))))
      (gtree_restrict t3 (SND (SND (SND q))))`;;
let GTREE_RESTRICT_FO_NODE = prove
 (`!t0 t1 t2 t3 r.
     gtree_restrict (GtreeNode t0 t1 t2 t3) r =
     (if gtr_isnil r then GtreePair GtreeEmpty (GtreeNode t0 t1 t2 t3)
      else gtree_restrict_q t0 t1 t2 t3
      (gtr_split4 r (GtrNil,GtrNil,GtrNil,GtrNil)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gtree_restrict; gtr_split; GTR_SPLIT_FN_FO; gtr_apply4;
              gtree_restrict_q]);;

let gtr_match0_t = define
 `(gtr_match0_t (CtreeNode t1 t2 t3) = (ctree_leaf t2 \/ ctree_leaf t3)) /\
  (gtr_match0_t (CtreeLeaf lf) = F) /\ (gtr_match0_t CtreeEmpty = F)`;;
let gtr_match1_t = define
 `(gtr_match1_t (CtreeNode t1 t2 t3) = ctree_leaf t1) /\
  (gtr_match1_t (CtreeLeaf lf) = F) /\ (gtr_match1_t CtreeEmpty = F)`;;
let gtr_match2_bs = define
 `(gtr_match2_bs Bstack0 (t2:ctree) (t3:ctree) = F) /\
  (gtr_match2_bs (Bpush0 bs') t2 t3 = ctree_leaf t2) /\
  (gtr_match2_bs (Bpush1 bs') t2 t3 = ctree_leaf t3)`;;
let gtr_match2_t = define
 `(gtr_match2_t (CtreeNode t1 t2 t3) bs = gtr_match2_bs bs t2 t3) /\
  (gtr_match2_t (CtreeLeaf lf) bs = F) /\ (gtr_match2_t CtreeEmpty bs = F)`;;
let gtr_match3_t = define
 `(gtr_match3_t (CtreeNode t1 t2 t3) bs = gtr_match2_bs bs t3 t2) /\
  (gtr_match3_t (CtreeLeaf lf) bs = F) /\ (gtr_match3_t CtreeEmpty bs = F)`;;
let GTR_MATCH0_FO = prove
 (`gtr_match0 GtrNil = F /\
   (!bs t r'. gtr_match0 (GtrCons bs t r') =
   (gtr_match0_t t \/ gtr_match0 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match0];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    REWRITE_TAC[gtr_match0; case_ctree_node; gtr_match0_t; DISJ_ASSOC]]);;
let GTR_MATCH1_FO = prove
 (`gtr_match1 GtrNil = F /\
   (!bs t r'. gtr_match1 (GtrCons bs t r') =
   (gtr_match1_t t \/ gtr_match1 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match1];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    REWRITE_TAC[gtr_match1; case_ctree_node; gtr_match1_t; DISJ_ASSOC]]);;
let GTR_MATCH2_FO = prove
 (`gtr_match2 GtrNil = F /\
   (!bs t r'. gtr_match2 (GtrCons bs t r') =
   (gtr_match2_t t bs \/ gtr_match2 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match2];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    STRUCT_CASES_TAC(SPEC `bs:bit_stack` (cases "bit_stack")) THEN
    REWRITE_TAC[gtr_match2; case_ctree_node; case_bitstack; gtr_match2_t;
                gtr_match2_bs; DISJ_ASSOC]]);;
let GTR_MATCH3_FO = prove
 (`gtr_match3 GtrNil = F /\
   (!bs t r'. gtr_match3 (GtrCons bs t r') =
   (gtr_match3_t t bs \/ gtr_match3 r'))`,
  CONJ_TAC THENL
   [REWRITE_TAC[gtr_match3];
    REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
    STRUCT_CASES_TAC(SPEC `bs:bit_stack` (cases "bit_stack")) THEN
    REWRITE_TAC[gtr_match3; case_ctree_node; case_bitstack; gtr_match3_t;
                gtr_match2_bs; DISJ_ASSOC]]);;
do_list cvt [gtr_match0_t; gtr_match1_t; gtr_match2_bs; gtr_match2_t;
             gtr_match3_t; GTR_MATCH0_FO; GTR_MATCH1_FO; GTR_MATCH2_FO;
             GTR_MATCH3_FO];;
do_list cv_add_unfold
  [gtp_0_e; gtp_1_e; gtp_2_e; gtp_3_e; gtp_01_e; gtp_12_e; gtp_13_e; gtp_23_e;
   gtp_e_0; gtp_e_1; gtp_e_2; gtp_e_3; gtp_e_01; gtp_e_12; gtp_e_13; gtp_e_23;
   gtp_0_1; gtp_1_0; gtp_1_2; gtp_2_1; gtp_1_3; gtp_3_1; gtp_2_3; gtp_3_2];;

(* gtree_restrict and gtree_restrict_q together: the node clause with the   *)
(* split tuple matched by a pattern                                          *)
let GTREE_RESTRICT_CV = prove
 (`(!t0 t1 t2 t3 r.
     gtree_restrict (GtreeNode t0 t1 t2 t3) r =
     (if gtr_isnil r then GtreePair GtreeEmpty (GtreeNode t0 t1 t2 t3)
      else let q = gtr_split4 r (GtrNil,GtrNil,GtrNil,GtrNil) in
           gtree_cons_pairs (GtreeNode t0 t1 t2 t3)
             (gtree_restrict t0 (FST q)) (gtree_restrict t1 (FST (SND q)))
             (gtree_restrict t2 (FST (SND (SND q))))
             (gtree_restrict t3 (SND (SND (SND q)))))) /\
   (!r. gtree_restrict GtreeLeaf0 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf0
      else if gtr_match0 r then gtp_0_e else gtp_e_0)) /\
   (!r. gtree_restrict GtreeLeaf1 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf1
      else if gtr_match1 r then gtp_1_e else gtp_e_1)) /\
   (!r. gtree_restrict GtreeLeaf2 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf2
      else if gtr_match2 r then gtp_2_e else gtp_e_2)) /\
   (!r. gtree_restrict GtreeLeaf3 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf3
      else if gtr_match3 r then gtp_3_e else gtp_e_3)) /\
   (!r. gtree_restrict GtreeLeaf01 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf01
      else if gtr_match0 r then (if gtr_match1 r then gtp_01_e else gtp_0_1)
      else if gtr_match1 r then gtp_1_0 else gtp_e_01)) /\
   (!r. gtree_restrict GtreeLeaf12 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf12
      else if gtr_match1 r then (if gtr_match2 r then gtp_12_e else gtp_1_2)
      else if gtr_match2 r then gtp_2_1 else gtp_e_12)) /\
   (!r. gtree_restrict GtreeLeaf13 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf13
      else if gtr_match1 r then (if gtr_match3 r then gtp_13_e else gtp_1_3)
      else if gtr_match3 r then gtp_3_1 else gtp_e_13)) /\
   (!r. gtree_restrict GtreeLeaf23 r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeLeaf23
      else if gtr_match2 r then (if gtr_match3 r then gtp_23_e else gtp_2_3)
      else if gtr_match3 r then gtp_3_2 else gtp_e_23)) /\
   (!r. gtree_restrict GtreeEmpty r =
     (if gtr_isnil r then GtreePair GtreeEmpty GtreeEmpty
     else empty_gtree_pair))`,
  REWRITE_TAC[GTREE_RESTRICT_FO_NODE; gtree_restrict_q; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[gtree_restrict]);;
cvt GTREE_RESTRICT_CV;;

(* ctree_restriction splitting and the leaf decrements                       *)
let ctr_split_acc = define
 `(ctr_split_acc (GtreeNode t0 t1 t2 t3) bs
  (q:ctree_restriction#ctree_restriction#ctree_restriction) =
     (ctr_cons bs t1 (FST q),
      ctr_cons (Bpush0 bs) t0 (ctr_cons_pop bs t2 t3 (FST (SND q))),
      ctr_cons (Bpush1 bs) t0 (ctr_cons_pop bs t3 t2 (SND (SND q))))) /\
  (ctr_split_acc GtreeLeaf0 bs q = q) /\ (ctr_split_acc GtreeLeaf1 bs q = q) /\
  (ctr_split_acc GtreeLeaf2 bs q = q) /\ (ctr_split_acc GtreeLeaf3 bs q = q) /\
  (ctr_split_acc GtreeLeaf01 bs q = q) /\
  (ctr_split_acc GtreeLeaf12 bs q = q) /\
  (ctr_split_acc GtreeLeaf13 bs q = q) /\
  (ctr_split_acc GtreeLeaf23 bs q = q) /\
  (ctr_split_acc GtreeEmpty bs q = q)`;;
let ctr_split3 = define
 `(ctr_split3 CtrNil
  (q:ctree_restriction#ctree_restriction#ctree_restriction) = q) /\
  (ctr_split3 (CtrCons bs t r) q = ctr_split3 r (ctr_split_acc t bs q))`;;
let ctr_apply3 = new_definition
 `ctr_apply3
  (continue:ctree_restriction->ctree_restriction->ctree_restriction->A)
             (q:ctree_restriction#ctree_restriction#ctree_restriction) =
    continue (FST q) (FST (SND q)) (SND (SND q))`;;
let CTR_SPLIT_FN_FO = prove
 (`!r (continue:ctree_restriction->ctree_restriction->ctree_restriction->A) r1
  r2 r3.
     ctr_split_fn r continue r1 r2 r3 =
     ctr_apply3 continue (ctr_split3 r (r1,r2,r3))`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[ctr_split_fn; ctr_split3; ctr_apply3; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:gtree`; `r:ctree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[ctr_split_fn; ctr_split3] THEN
    STRUCT_CASES_TAC(SPEC `t:gtree` (cases "gtree")) THEN
    ASM_REWRITE_TAC[case_gtree_node; ctr_split_acc; FST; SND]]);;
cvt ctr_split_acc;; cvt ctr_split3;;

let ctr_decr3 = define
 `(ctr_decr3 (lf1:ctree) (lf2:ctree) (lf3:ctree) CtrNil = (lf1,lf2,lf3)) /\
  (ctr_decr3 lf1 lf2 lf3 (CtrCons bs t r) =
     ctr_decr3 (ctr_e_decr bs t Color1 lf1) (ctr_e_decr bs t Color2 lf2)
     (ctr_e_decr bs t Color3 lf3) r)`;;
let ctree_apply3 = new_definition
 `ctree_apply3 (cont:ctree->ctree->ctree->A) (q:ctree#ctree#ctree) =
  cont (FST q) (FST (SND q)) (SND (SND q))`;;
let CTR_DECR_FO = prove
 (`!r (cont:ctree->ctree->ctree->A) lf1 lf2 lf3.
     ctr_decr cont lf1 lf2 lf3 r =
     ctree_apply3 cont (ctr_decr3 lf1 lf2 lf3 r)`,
  MATCH_MP_TAC ctree_restriction_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[ctr_decr; ctr_decr3; ctree_apply3; FST; SND];
    MAP_EVERY X_GEN_TAC [`bs:bit_stack`; `t:gtree`; `r:ctree_restriction`] THEN
    DISCH_TAC THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ctr_decr; ctr_decr3]]);;

let cdec1 = new_definition `cdec1 bs t lf = ctr_e_decr bs t Color1 lf`;;
let cdec2 = new_definition `cdec2 bs t lf = ctr_e_decr bs t Color2 lf`;;
let cdec3 = new_definition `cdec3 bs t lf = ctr_e_decr bs t Color3 lf`;;
let CTR_DECR3_FO = prove
 (`(!lf1 lf2 lf3. ctr_decr3 lf1 lf2 lf3 CtrNil = (lf1,lf2,lf3)) /\
   (!lf1 lf2 lf3 bs t r.
      ctr_decr3 lf1 lf2 lf3 (CtrCons bs t r) =
      ctr_decr3 (cdec1 bs t lf1) (cdec2 bs t lf2) (cdec3 bs t lf3) r)`,
  REWRITE_TAC[ctr_decr3; cdec1; cdec2; cdec3]);;
let match_count_fn_e = cv_eta match_count_fn;;
let cdec_conv =
  REWRITE_CONV
    [cdec1; cdec2; cdec3; ctr_e_decr; gtree_sub; match_count; match_count_fn_e;
     gtree_mem; gtree_sel; gtree_leaf_mem; gtree_empty;
     gtree_isleaf; case_bitstack; EQ_GRAM_SYMBOL; EQ_COLOR; NOT_CONS_NIL] THENC
  NUM_REDUCE_CONV;;
let cdec_rules c =
  let bs_pats = [`Bstack0`; `Bpush0 bs'`; `Bpush1 bs'`] in
  let t_pats =
  [`GtreeNode a b c d`; `GtreeLeaf0`; `GtreeLeaf1`; `GtreeLeaf2`; `GtreeLeaf3`;
   `GtreeLeaf01`; `GtreeLeaf12`; `GtreeLeaf13`; `GtreeLeaf23`; `GtreeEmpty`] in
  end_itlist CONJ
    (flat (map (fun bsp -> map (fun tp -> GEN_ALL (cdec_conv
                            (list_mk_comb (c, [bsp; tp; `lf:ctree`])))) t_pats)
               bs_pats));;
let CDEC1_RULES = cdec_rules `cdec1` and CDEC2_RULES = cdec_rules `cdec2`
and CDEC3_RULES = cdec_rules `cdec3`;;
let _ =
  if exists (fun c -> can (find_term (fun t -> is_const t &&
                     fst (dest_const t) = "gtree_sub")) (concl c))
            (CONJUNCTS CDEC1_RULES @ CONJUNCTS CDEC2_RULES @ CONJUNCTS CDEC3_RULES)
  then failwith "cdec rules: unevaluated gtree_sub" else ();;
cvt CDEC1_RULES;; cvt CDEC2_RULES;; cvt CDEC3_RULES;; cvt CTR_DECR3_FO;;

let ctree_restrict_node = define
 `(ctree_restrict_node h (CtreeNode t1 t2 t3) r =
     (if h = 0 then
        ctree_leaf_pair t1 t2 t3 (FST (ctr_decr3 t1 t2 t3 r))
          (FST (SND (ctr_decr3 t1 t2 t3 r))) (SND (SND (ctr_decr3 t1 t2 t3 r)))
      else ctree_cons_pairs
             (ctree_restrict (h - 1) t1 (FST (ctr_split3 r (CtrNil,CtrNil,CtrNil))))
             (ctree_restrict (h - 1) t2
                (FST (SND (ctr_split3 r (CtrNil,CtrNil,CtrNil)))))
             (ctree_restrict (h - 1) t3
                (SND (SND (ctr_split3 r (CtrNil,CtrNil,CtrNil))))))) /\
  (ctree_restrict_node h (CtreeLeaf lf) r = ctree_empty_pair) /\
  (ctree_restrict_node h CtreeEmpty r = ctree_empty_pair)`;;
let CTREE_RESTRICT_FO = prove
 (`!h t r. ctree_restrict h t r =
           (if ctr_isnil r then CtreePair t CtreeEmpty
           else ctree_restrict_node h t r)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `h:num` num_CASES) THEN
  REWRITE_TAC[ctree_restrict; ctree_restrict_fn] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  STRUCT_CASES_TAC(SPEC `t:ctree` (cases "ctree")) THEN
  REWRITE_TAC[case_ctree_node; ctree_restrict_node; NOT_SUC; SUC_SUB1;
              CTR_DECR_FO; ctree_apply3; ctree_leaf_pair; ctr_split;
              CTR_SPLIT_FN_FO; ctr_apply3; ctree_restrict]);;
let CTREE_RESTRICT_CV = prove
 (`(!h r. ctree_restrict h CtreeEmpty r =
      (if ctr_isnil r then CtreePair CtreeEmpty CtreeEmpty
       else ctree_empty_pair)) /\
   (!h lf r. ctree_restrict h (CtreeLeaf lf) r =
      (if ctr_isnil r then CtreePair (CtreeLeaf lf) CtreeEmpty
       else ctree_empty_pair)) /\
   (!h t1 t2 t3 r. ctree_restrict h (CtreeNode t1 t2 t3) r =
      (if ctr_isnil r then CtreePair (CtreeNode t1 t2 t3) CtreeEmpty
       else if h = 0 then
         (let q = ctr_decr3 t1 t2 t3 r in
          ctree_leaf_pair t1 t2 t3 (FST q) (FST (SND q)) (SND (SND q)))
       else
         (let q = ctr_split3 r (CtrNil,CtrNil,CtrNil) in
          ctree_cons_pairs (ctree_restrict (h - 1) t1 (FST q))
                           (ctree_restrict (h - 1) t2 (FST (SND q)))
                           (ctree_restrict (h - 1) t3 (SND (SND q))))))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CTREE_RESTRICT_FO] THEN
  REWRITE_TAC[ctree_restrict_node; LET_DEF; LET_END_DEF]);;
cvt CTREE_RESTRICT_CV;;

(* ------------------------------------------------------------------------- *)
(* List rotations (embed_prelim.ml).                                         *)
(* ------------------------------------------------------------------------- *)

let CV_LEN_FACTS = prove
 (`(!n. ~(SUC (SUC n) < 2)) /\ (!n. ~(SUC (SUC n) <= 1)) /\ SUC 0 < 2 /\
   SUC 0 <= 1 /\ 0 < 2 /\ 0 <= 1`, ARITH_TAC);;

let cvt_split i th = cvt (cv_split_clauses i th);;
cvt_split 1 take_list;;
cvt_split 1 drop_list;;
do_list cvt [rot_list; rotr_list];;

(* ------------------------------------------------------------------------- *)
(* Configuration colourings (cfcolor.ml), with the colour-map arguments of   *)
(* cfcbr1 / cfcbr2 represented by edge permutations.                         *)
(* ------------------------------------------------------------------------- *)

let CTREE_CONS_PERM_CLAUSES = prove
 (`!g c t. ctree_cons_perm g c t = ctree_cons_e (g c) t`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `c:color` (cases "color")) THEN
  REWRITE_TAC[ctree_cons_perm; palette]);;

let cfcbr2_e = new_definition
 `cfcbr2_e p et = cfcbr2 (ctree_cons_perm (permc p)) et`;;
let CFCBR2_E = prove
 (`(!p. cfcbr2_e p [] = ctree_simple_leaf) /\
   (!p e et. cfcbr2_e p (CONS e et) = ctree_cons_e (permc p e) (cfcbr2_e p et))`,
  REWRITE_TAC[cfcbr2_e; cfcbr2; CTREE_CONS_PERM_CLAUSES]);;
let cfcbr2_f = new_definition
 `cfcbr2_f p et = cfcbr2 (ctree_cons_perm (\c. permc Eperm132 (permc p c))) et`;;
let CFCBR2_F = prove
 (`(!p. cfcbr2_f p [] = ctree_simple_leaf) /\
   (!p e et. cfcbr2_f p (CONS e et) =
             ctree_cons_e (permc Eperm132 (permc p e)) (cfcbr2_f p et))`,
  REWRITE_TAC[cfcbr2_f; cfcbr2; CTREE_CONS_PERM_CLAUSES]);;
let cfcbr1_e = new_definition `cfcbr1_e p et = cfcbr1 (permc p) et`;;
let CFCBR1_E = prove
 (`(!p. cfcbr1_e p [] = ctree_simple_leaf) /\
   (!p e et. cfcbr1_e p (CONS e et) =
       if permc p e = Color0 then CtreeEmpty
       else if permc p e = Color1 then ctree_cons1 (cfcbr1_e p et)
       else if permc p e = Color2 then ctree_cons2 (cfcbr2_e p et)
       else ctree_cons2 (cfcbr2_f p et))`,
  REWRITE_TAC[cfcbr1_e; cfcbr1; cfcbr2_e; cfcbr2_f; ETA_AX]);;
cvt CFCBR2_E;; cvt CFCBR2_F;; cvt CFCBR1_E;;

let CPBRANCH_CLAUSES = prove
 (`cpbranch [] = CtreeEmpty /\ (!a. cpbranch [a] = CtreeEmpty) /\
   (!a b t. cpbranch (CONS a (CONS b t)) =
      if b = Color0 then CtreeEmpty else cfcbr1_e (edge_rot b) t)`,
  REWRITE_TAC[cpbranch; LENGTH; HD; TL; CV_LEN_FACTS; cfcbr1_e]);;
cvt CPBRANCH_CLAUSES;;

let cpcol = new_definition `cpcol cp et = ITLIST cpcolor1 cp cpbranch et`;;
let CPCOL_CLAUSES = prove
 (`(!et. cpcol [] et = cpbranch et) /\
   (!n cp et. cpcol (CONS (CpR n) cp) et = cpcol cp (rot_list n et)) /\
   (!cp. cpcol (CONS CpRr cp) [] = CtreeEmpty) /\
   (!cp a. cpcol (CONS CpRr cp) [a] = CtreeEmpty) /\
   (!cp a b t. cpcol (CONS CpRr cp) (CONS a (CONS b t)) =
      cpcol cp (rotr_list 1 (CONS a (CONS b t)))) /\
   (!cp. cpcol (CONS CpY cp) [] = CtreeEmpty) /\
   (!cp a t. cpcol (CONS CpY cp) (CONS a t) =
      ctree_union (cpcol cp (CONS (permc Eperm231 a) (CONS (permc Eperm312 a) t)))
                  (cpcol cp (CONS (permc Eperm312 a) (CONS (permc Eperm231 a) t)))) /\
   (!cp. cpcol (CONS CpH cp) [] = CtreeEmpty) /\
   (!cp a. cpcol (CONS CpH cp) [a] = CtreeEmpty) /\
   (!cp a b t. cpcol (CONS CpH cp) (CONS a (CONS b t)) =
      if a = b then
        ctree_union (cpcol cp (CONS (permc Eperm231 a) (CONS (permc Eperm231 a) t)))
                    (cpcol cp (CONS (permc Eperm312 a) (CONS (permc Eperm312 a) t)))
      else cpcol cp (CONS b (CONS a t))) /\
   (!cp et. cpcol (CONS CpU cp) et =
      ctree_union (cpcol cp (CONS Color1 (CONS Color1 et)))
        (ctree_union (cpcol cp (CONS Color2 (CONS Color2 et)))
                     (cpcol cp (CONS Color3 (CONS Color3 et))))) /\
   (!cp. cpcol (CONS CpK cp) [] = CtreeEmpty) /\
   (!cp a. cpcol (CONS CpK cp) [a] = CtreeEmpty) /\
   (!cp a b t. cpcol (CONS CpK cp) (CONS a (CONS b t)) =
      if a = b then CtreeEmpty else cpcol cp (CONS (addc a b) t)) /\
   (!cp. cpcol (CONS CpA cp) [] = CtreeEmpty) /\
   (!cp a. cpcol (CONS CpA cp) [a] = CtreeEmpty) /\
   (!cp a b t. cpcol (CONS CpA cp) (CONS a (CONS b t)) =
      if a = b then cpcol cp (if t = [] then CONS a (CONS b t) else t)
      else CtreeEmpty)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[cpcol; ITLIST; cpcolor1; LENGTH; HD; TL; NOT_CONS_NIL;
              CV_LEN_FACTS] THEN
  REWRITE_TAC[GSYM cpcol]);;
cvt CPCOL_CLAUSES;;

let CPCOLOR0_CPCOL = prove
 (`(cpcolor0 [] = cpcol [] [Color1; Color1]) /\
   (!n cp'. cpcolor0 (CONS (CpR n) cp') = cpcolor0 cp') /\
   (!cp'. cpcolor0 (CONS CpRr cp') = cpcol (CONS CpRr cp') [Color1; Color1]) /\
   (!cp'. cpcolor0 (CONS CpY cp') = cpcol cp' [Color1; Color2; Color3]) /\
   (!cp'. cpcolor0 (CONS CpH cp') = cpcol (CONS CpH cp') [Color1; Color1]) /\
   (!cp'. cpcolor0 (CONS CpU cp') =
       ctree_union (cpcol cp' [Color1; Color1; Color2; Color2])
                   (cpcol cp' [Color1; Color1; Color1; Color1])) /\
   (!cp'. cpcolor0 (CONS CpK cp') = cpcol (CONS CpK cp') [Color1; Color1]) /\
   (!cp'. cpcolor0 (CONS CpA cp') = cpcol (CONS CpA cp') [Color1; Color1])`,
  REWRITE_TAC[cpcolor0; cpcol]);;
cvt CPCOLOR0_CPCOL;;

cvt cpcolor;;

(* ------------------------------------------------------------------------- *)
(* The initial trees (initctree.ml, initgtree.ml, dyck.ml).                  *)
(* ------------------------------------------------------------------------- *)

cvt (cv_eta gen_dyck_fn);;
cvt gen_dyck;;
cvt count_cbit1;;

let leaf_add = define
 `(leaf_add 0 t = t) /\ (leaf_add (SUC n) t = CtreeLeaf (leaf_add n t))`;;
let LEAF_ADD_ADD = prove
 (`!a b t. leaf_add a (leaf_add b t) = leaf_add (a + b) t`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[leaf_add; ADD_CLAUSES]);;
let CTREE_ADD_DYCK_LEAF_ADD = prove
 (`!n m t. ctree_add_dyck m n t = leaf_add (gen_dyck (SUC m) (m + 2 * n)) t`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_DYCK_CLAUSES; GEN_DYCK_CLAUSES; leaf_add; ONE];
    INDUCT_TAC THEN GEN_TAC THEN
    ASM_REWRITE_TAC[ADD_DYCK_CLAUSES; GEN_DYCK_CLAUSES; LEAF_ADD_ADD]]);;
cvt leaf_add;;
cvt CTREE_ADD_DYCK_LEAF_ADD;;

cvt (cv_eta leaf_from1_fn);;
do_list cvt [ctree_leaf_table_from; ctree_leaf_table; ctree_merge_pair;
             ctree_pairmap; ctree_merge_table; ctree_prune_1; ctree_prune_2;
             ctree_prune_3];;

let ctree_merge_iter = define
 `(ctree_merge_iter 0 tab = tab) /\
  (ctree_merge_iter (SUC n) tab = ctree_merge_table (ctree_merge_iter n tab))`;;
let CTREE_MERGE_ITER = prove
 (`!n tab. ITER n ctree_merge_table tab = ctree_merge_iter n tab`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; ctree_merge_iter]);;
let tree_of_tab = define
 `(tree_of_tab [] = CtreeEmpty) /\
  (tree_of_tab [p] = CtreeEmpty) /\
  (tree_of_tab (CONS p (CONS q rs)) =
    ctree_cons (ctree_prune_1 (ctree_pair_sub p T))
               (ctree_prune_2 (ctree_pair_sub q F))
               (ctree_prune_3 (ctree_pair_sub q T)))`;;
let CTREE_INIT_TREE_CV = prove
 (`!h. ctree_init_tree h =
       tree_of_tab (ctree_merge_iter (h - 1) (ctree_leaf_table h))`,
  GEN_TAC THEN REWRITE_TAC[ctree_init_tree; CTREE_MERGE_ITER; LET_DEF;
                           LET_END_DEF] THEN
  SPEC_TAC(`ctree_merge_iter (h - 1) (ctree_leaf_table h)`,`l:ctree_pair list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[tree_of_tab; LENGTH; CV_LEN_FACTS] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[tree_of_tab; LENGTH; CV_LEN_FACTS; HD; TL]);;
do_list cvt [ctree_merge_iter; tree_of_tab; CTREE_INIT_TREE_CV];;

cv_add_unfold init_gtree_h1;;
cvt gtree_merge_pairs;;
cvt (cv_split_clauses 4 (cv_eta gtree_merge_line_fn));;
cvt gtree_merge_line;;
let git_step = define
 `(git_step [] d = []) /\ (git_step [a] d = [a]) /\
  (git_step (CONS a (CONS b t)) d = gtree_merge_line b a empty_gtree_pair t d)`;;
let GTREE_INIT_TABLE_FN_CV = prove
 (`(!d. gtree_init_table_fn 0 d = init_gtree_h1) /\
   (!h d. gtree_init_table_fn (SUC h) d =
          git_step (gtree_init_table_fn h (SUC d)) d)`,
  REWRITE_TAC[gtree_init_table_fn; LET_DEF; LET_END_DEF] THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`gtree_init_table_fn h (SUC d)`,`l:gtree_pair list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[git_step; LENGTH; CV_LEN_FACTS] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[git_step; LENGTH; CV_LEN_FACTS; HD; TL]);;
do_list cvt [git_step; GTREE_INIT_TABLE_FN_CV; gtree_init_table];;
let git_head = define
 `(git_head [] = GtreeEmpty) /\ (git_head (CONS p t) = gtree_pair_sub p F)`;;
let GTREE_INIT_TREE_CV = prove
 (`!h. gtree_init_tree h =
       (if h = 0 then GtreeEmpty else git_head (gtree_init_table 0 (h - 1)))`,
  GEN_TAC THEN REWRITE_TAC[gtree_init_tree; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SPEC_TAC(`gtree_init_table 0 (h - 1)`,`l:gtree_pair list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[git_head; NOT_CONS_NIL; HD]);;
do_list cvt [git_head; GTREE_INIT_TREE_CV];;

(* ------------------------------------------------------------------------- *)
(* The Kempe closure (kempetree.ml), first-order: the two ktc_stepp levels   *)
(* inlined, the restriction let-bound.                                       *)
(* ------------------------------------------------------------------------- *)

let KEMPE_TREE_CLOSURE_CV = prove
 (`(!h ctu ctr gtu. kempe_tree_closure h 0 ctu ctr gtu =
      (ctu, gtree_restrict gtu (GtrCons Bstack0 ctr GtrNil))) /\
   (!h d ctu ctr gtu. kempe_tree_closure h (SUC d) ctu ctr gtu =
      let kr0 = kempe_tree_closure h d ctu ctr gtu in
      let kr1 =
        (let c1 = FST kr0 in
         let r1 = gtree_pair_sub (SND kr0) F in
         let u1 = gtree_pair_sub (SND kr0) T in
         if ctree_empty c1 then (c1, GtreePair r1 u1)
         else if gtree_empty r1 then (c1, GtreePair r1 u1)
         else if gtree_empty u1 then (CtreeEmpty, empty_gtree_pair)
         else let p = ctree_restrict h c1 (CtrCons Bstack0 r1 CtrNil) in
              kempe_tree_closure h d (ctree_pair_sub p F)
                (ctree_rotlr (ctree_pair_sub p T)) u1) in
      let c2 = FST kr1 in
      let r2 = gtree_pair_sub (SND kr1) F in
      let u2 = gtree_pair_sub (SND kr1) T in
      if ctree_empty c2 then (c2, GtreePair r2 u2)
      else if gtree_empty r2 then (c2, GtreePair r2 u2)
      else if gtree_empty u2 then (CtreeEmpty, empty_gtree_pair)
      else let p = ctree_restrict h c2 (CtrCons Bstack0 r2 CtrNil) in
           kempe_tree_closure h d (ctree_pair_sub p F)
             (ctree_rotlr (ctree_pair_sub p T)) u2)`,
  REWRITE_TAC[kempe_tree_closure; kempe_tree_closure_fn; ktc_stepp; ktc_step;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;
cvt KEMPE_TREE_CLOSURE_CV;;

let kempe_tree_h = new_definition
 `kempe_tree_h h (cp:(cpstep)list) =
    FST (kempe_tree_closure h (SUC (SUC h)) (ctree_init_tree (SUC h))
         (cpcolor cp) (gtree_init_tree (SUC h)))`;;
cvt kempe_tree_h;;
