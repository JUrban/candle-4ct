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
