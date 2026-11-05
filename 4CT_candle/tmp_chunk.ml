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
let KEMPE_TREE_H = prove
 (`!cp. kempe_tree cp =
 (if 2 <= cprsize cp then kempe_tree_h (cprsize cp - 2) cp else CtreeEmpty)`,
  REWRITE_TAC[kempe_tree; kempe_tree_h; LET_DEF; LET_END_DEF]);;
cvt kempe_tree_h;;
