(* ========================================================================= *)
(* 4CT_candle/birkhoff_cv.ml                                                 *)
(*                                                                           *)
(* The four Birkhoff checks of birkhoff.ml (Gonthier's birkhoff2..5) by      *)
(* Kernel.compute.  Loaded from 4CT/birkhoff.ml after the definitions of     *)
(* Birkhoff_check and its parts; the statements are those of the HOL Light   *)
(* development (which evaluates them with CBV_CONV).                         *)
(*                                                                           *)
(* Birkhoff_check2 takes the basis check and its own partial application as *)
(* function arguments; bc2 is its first-order form for a basis given as the *)
(* list L of the basis colour trees (check_basis t = EX (ctree_disjoint t) L)*)
(* with do_Birkhoff_check2 inlined.                                          *)
(* ========================================================================= *)

needs "4CT_candle/kempe_cv.ml";;

cvt (INST_TYPE [`:color`,`:A`] BUTLAST);;
cvt ctree_pick_rev_rec;;
cvt ctree_pick_rev;;

let tl0 = define `(tl0 ([]:color list) = []) /\ (tl0 (CONS h t) = t)`;;
cvt tl0;;

let ex_disj = define
 `(ex_disj t [] = F) /\
  (ex_disj t (CONS c l) <=> ctree_disjoint t c \/ ex_disj t l)`;;
let EX_DISJ = prove
 (`!t l. EX (ctree_disjoint t) l <=> ex_disj t l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; ex_disj]);;
cvt ex_disj;;

let bc2 = define
 `(bc2 h L c1 g1 0 c2 g2 = F) /\
  (bc2 h L c1 g1 (SUC n) c2 g2 =
     let cs = ctree_pick_rev c1 c2 in
     if cs = [] then F else
     (let et = BUTLAST cs in
      if MEM Color0 et then F else
      let pr = kempe_tree_closure (h - 1) h c1 (ctree_of_ttail (etrace et)) g1 in
      gtree_empty (gtree_pair_sub (SND pr) F) /\
      (ex_disj (FST pr) L \/
       bc2 h L c2 g2 n (FST pr) (gtree_pair_sub (SND pr) T))) /\
     (let et = REVERSE (tl0 cs) in
      if MEM Color0 et then F else
      let pr = kempe_tree_closure (h - 1) h c2 (ctree_of_ttail (etrace et)) g2 in
      gtree_empty (gtree_pair_sub (SND pr) F) /\
      (ex_disj (FST pr) L \/
       bc2 h L c1 g1 n (FST pr) (gtree_pair_sub (SND pr) T))))`;;

let BIRKHOFF_CHECK2_BC2 = prove
 (`!h L n c1 g1 c2 g2.
     Birkhoff_check2 h (\t. EX (ctree_disjoint t) L) c1 g1 n c2 g2 <=>
     bc2 h L c1 g1 n c2 g2`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[birkhoff_check2; bc2] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[do_Birkhoff_check2; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[EX_DISJ] THEN
  SPEC_TAC(`ctree_pick_rev c1 c2`,`cs:color list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; TL; tl0]);;
cvt bc2;;

(* Birkhoff_check h m from the iteration count niter and the basis cps      *)
let cv_cprsize_conv tm =
  if is_comb tm && is_const (rator tm) && fst(dest_const(rator tm)) = "cprsize"
  then cprsize_conv tm else failwith "cv_cprsize_conv";;

let BIRKHOFF_CHECK_CV h m niter cps =
  let goal = list_mk_comb(`Birkhoff_check`, [mk_small_numeral h; mk_small_numeral m]) in
  let cpl = mk_list(cps, `:cpstep list`) in
  let th1 = prove(mk_comb(mk_comb(`ALL:(cpstep list->bool)->(cpstep list)list->bool`,
                     list_mk_comb(`Birkhoff_check1`, [mk_small_numeral h; mk_small_numeral m])), cpl),
    REWRITE_TAC[ALL; birkhoff_check1; CUBIC_PROG_CLAUSES; CUBIC_STEP_CLAUSES; cpcard] THEN
    CONV_TAC(ONCE_DEPTH_CONV cv_cprsize_conv) THEN CONV_TAC NUM_REDUCE_CONV) in
  let hn = mk_small_numeral h in
  let l = rand(concl(REWRITE_CONV[MAP] (mk_icomb(mk_icomb(`MAP:(cpstep list->ctree)->(cpstep list)list->ctree list`, `cpcolor`), cpl)))) in
  let bctm = list_mk_comb(`bc2`, [hn; l; mk_comb(`ctree_init_tree`, hn);
               mk_comb(`gtree_init_tree`, hn); mk_small_numeral niter;
               mk_comb(`ctree_init_tree`, hn); mk_comb(`gtree_init_tree`, hn)]) in
  let th2 = EQT_ELIM (cv_eval bctm) in
  let th3 = prove(goal,
    REWRITE_TAC[birkhoff_check] THEN EXISTS_TAC (mk_small_numeral niter) THEN
    EXISTS_TAC cpl THEN REWRITE_TAC[th1; BIRKHOFF_CHECK2_BC2; MAP; th2]) in
  print_string ("BIRKHOFF_EVAL: " ^ string_of_term (concl th3) ^ " proved\n");
  th3;;

let BIRKHOFF_CHECK_1_0 = BIRKHOFF_CHECK_CV 1 0 1 [`[]:cpstep list`];;

let BIRKHOFF_CHECK_2_0 = BIRKHOFF_CHECK_CV 2 0 1 [`[CpY]`];;

let BIRKHOFF_CHECK_3_0 = BIRKHOFF_CHECK_CV 3 0 4 [`[CpU]`; `[CpR 1; CpU]`];;

let BIRKHOFF_CHECK_4_1 = BIRKHOFF_CHECK_CV 4 1 10
  [`[CpU; CpY]`; `[CpR 1; CpU; CpY]`; `[CpR 2; CpU; CpY]`;
   `[CpR 3; CpU; CpY]`; `[CpR 4; CpU; CpY]`; `[CpH; CpR 4; CpY; CpY; CpY]`];;
