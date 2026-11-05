(* ========================================================================= *)
(* 4CT_candle/part2_cv.ml                                                    *)
(*                                                                           *)
(* Part 2 for Candle: check_reducible cfNNN <=> T for the 633                *)
(* configurations by Kernel.compute, through the cv translations of          *)
(* cvtrans.ml (the Kempe side is in kempe_cv.ml).                            *)
(*                                                                           *)
(* The contract side (cfcontract.ml) uses HD, TL and EL, mostly guarded by   *)
(* length tests (turned into list patterns here), but in cfctr_map, cpadj    *)
(* and ctrband partly unguarded.  For those, total versions (with arbitrary  *)
(* values on too-short lists) are proved equal to the definitions under      *)
(* cfctr_ok resp. computable conditions cpadj_ok, ctrband_cvok, which are      *)
(* checked by Kernel.compute together with the reducibility check.  The      *)
(* ring size cprsize (cfprog cf) is semantic; it is computed by birkhoff.ml's*)
(* cprsize_conv and passed to sized versions of the definitions.             *)
(* ========================================================================= *)

needs "4CT/cfreducible.ml";;
needs "4CT_candle/kempe_cv.ml";;

(* ------------------------------------------------------------------------- *)
(* Instantiating list arguments by patterns of a given depth.                *)
(* ------------------------------------------------------------------------- *)

let rec cv_el_conv tm =
  let n,l = dest_binary "EL" tm in
  if n = `0` then REWR_CONV (CONJUNCT1 EL) tm
  else (RATOR_CONV (RAND_CONV num_CONV) THENC REWR_CONV (CONJUNCT2 EL) THENC
        RAND_CONV (TRY_CONV (REWR_CONV TL)) THENC cv_el_conv) tm;;

let cv_ineq_conv tm =
  if (is_binary "<=" tm || is_binary "<" tm) &&
     type_of (lhand tm) = `:num` then
    (try EQT_INTRO (ARITH_RULE tm) with Failure _ ->
     try EQF_INTRO (ARITH_RULE (mk_neg tm)) with Failure _ ->
     failwith "cv_ineq_conv")
  else failwith "cv_ineq_conv";;

let cv_pat_simp_conv =
  REWRITE_CONV[LENGTH; HD; TL; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11;
               LET_DEF; LET_END_DEF; COND_CLAUSES] THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  TOP_DEPTH_CONV (CHANGED_CONV cv_el_conv) THENC
  REWRITE_CONV[HD; TL] THENC
  ONCE_DEPTH_CONV cv_ineq_conv THENC
  REWRITE_CONV[COND_CLAUSES; NOT_CONS_NIL; GSYM NOT_CONS_NIL];;

(* [] ; [x1] ; ... ; [x1..x(d-1)] ; x1 :: .. :: xd :: rest                  *)
let cv_list_pats ty d =
  let xs = map (fun _ -> cv_fresh ty) (1--d) in
  let rest = cv_fresh (mk_type("list",[ty])) in
  let mk l t = itlist (fun x t -> mk_cons x t) l t in
  let nil = mk_const("NIL", [ty,`:A`]) in
  map (fun k -> mk (fst(chop_list k xs)) nil) (0--(d-1)) @
  [mk xs rest];;

(* instantiate argument i of the clause th by each pattern and simplify     *)
let cv_inst_pats i pats th =
  let th = SPEC_ALL th in
  let x = el i (snd(strip_comb(lhs(concl th)))) in
  end_itlist CONJ
    (map (fun p -> GEN_ALL (CONV_RULE (RAND_CONV cv_pat_simp_conv)
                                     (INST [p,x] th))) pats);;

(* ------------------------------------------------------------------------- *)
(* Counting helpers for the FILTER / EX / ALL with lambdas.                  *)
(* ------------------------------------------------------------------------- *)

let count_true = define
 `(count_true [] = 0) /\
  (count_true (CONS b l) = (if b then 1 else 0) + count_true l)`;;
let COUNT_TRUE = prove
 (`!l. LENGTH (FILTER (\b. b) l) = count_true l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LENGTH; count_true] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;
let count_false = define
 `(count_false [] = 0) /\
  (count_false (CONS b l) = (if b then 0 else 1) + count_false l)`;;
let COUNT_FALSE = prove
 (`!l. LENGTH (FILTER (\b. ~b) l) = count_false l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LENGTH; count_false] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;
let exists_false = define
 `(exists_false [] = F) /\ (exists_false (CONS b l) <=> ~b \/ exists_false l)`;;
let EXISTS_FALSE = prove
 (`!l. EX (\b. ~b) l <=> exists_false l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; exists_false]);;
let all_true = define
 `(all_true [] = T) /\ (all_true (CONS b l) <=> b /\ all_true l)`;;
let ALL_TRUE = prove
 (`!l. ALL (\b. b) l <=> all_true l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; all_true]);;
let count_h = define
 `(count_h [] = 0) /\
  (count_h (CONS s cp) = (if s = CpH then 1 else 0) + count_h cp)`;;
let COUNT_H = prove
 (`!cp. LENGTH (FILTER (\s. s = CpH) cp) = count_h cp`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LENGTH; count_h] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC);;
do_list cvt [count_true; count_false; exists_false; all_true; count_h];;

(* ------------------------------------------------------------------------- *)
(* Masks and contract maps (cfcontract.ml).                                  *)
(* ------------------------------------------------------------------------- *)

cvt_as "cv_MEM_num" (INST_TYPE [`:num`,`:A`] MEM);;
cvt REPLICATE;;
do_list cvt [ctrmsize; ctrmask_rec; ctrmask; cfcontract_ref; cfprog;
             cfcontract_mask; nsp];;
cvt (INST_TYPE [`:bool`,`:A`] (cv_split_clauses 1 mask_list));;

(* total head / tail of boolean lists                                        *)
let hd0 = define `(hd0 [] = F) /\ (hd0 (CONS (h:bool) t) = h)`;;
let tlb = define `(tlb ([]:bool list) = []) /\ (tlb (CONS (h:bool) t) = t)`;;
do_list cvt [hd0; tlb];;

let LEN_GE_1 = prove
 (`!l:A list. 1 <= LENGTH l <=> ?a t. l = CONS a t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[ARITH_RULE `~(1 <= 0) /\ 1 <= SUC n`]);;
let LEN_GE_2 = prove
 (`!l:A list. 2 <= LENGTH l <=> ?a b t. l = CONS a (CONS b t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11] THENL
   [ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`t:A list`,`t:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11] THEN
  REWRITE_TAC[ARITH_RULE `2 <= SUC (SUC n)`; ARITH_RULE `~(2 <= SUC 0)`] THEN
  MESON_TAC[]);;
let LEN_GE_3 = prove
 (`!l:A list. 3 <= LENGTH l <=> ?a b c t. l = CONS a (CONS b (CONS c t))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_CONS_NIL; CONS_11; ARITH_RULE `~(3 <= 0)`] THEN
  REWRITE_TAC[ARITH_RULE `3 <= SUC n <=> 2 <= n`; LEN_GE_2] THEN MESON_TAC[]);;

(* cfctr_ok with list patterns                                               *)
let cv_inst_var v pats th =
  end_itlist CONJ
    (map (fun p -> GEN_ALL (CONV_RULE (RAND_CONV cv_pat_simp_conv)
                                     (INST [p,v] (SPEC_ALL th)))) pats);;

let CFCTR_OK_CV =
  let cls = CONJUNCTS cfctr_ok in
  let cy = SPEC_ALL (el 3 cls) and ch = SPEC_ALL (el 4 cls) in
  let cp' = rand(rand(lhs(concl cy))) in
  let mr = el 0 (snd(strip_comb(lhs(concl cy))))
  and mc = el 1 (snd(strip_comb(lhs(concl cy)))) in
  let cy0 = CONV_RULE (RAND_CONV cv_pat_simp_conv) (INST [`[]:cpstep list`, cp'] cy) in
  let s = cv_fresh `:cpstep` and t = cv_fresh `:cpstep list` in
  let cy1 = CONV_RULE (RAND_CONV cv_pat_simp_conv) (INST [mk_cons s t, cp'] cy) in
  let cy0s = cv_inst_var mr (cv_list_pats `:bool` 3) cy0 in
  let cy1s = flat (map (fun th -> CONJUNCTS (cv_inst_var mc (cv_list_pats `:bool` 1) th))
                     (CONJUNCTS (cv_inst_var mr (cv_list_pats `:bool` 2) cy1))) in
  let mrh = el 0 (snd(strip_comb(lhs(concl ch))))
  and mch = el 1 (snd(strip_comb(lhs(concl ch)))) in
  let chs = flat (map (fun th -> CONJUNCTS (cv_inst_var mch (cv_list_pats `:bool` 3) th))
                     (CONJUNCTS (cv_inst_var mrh (cv_list_pats `:bool` 2) ch))) in
  let chs = map (fun th -> GEN_ALL (CONV_RULE (RAND_CONV (REWRITE_CONV[ALL_TRUE]))
                                     (SPEC_ALL th))) chs in
  end_itlist CONJ ([el 0 cls; el 1 cls; el 2 cls] @ CONJUNCTS cy0s @ cy1s @ chs @
                   [el 5 cls; el 6 cls; el 7 cls]);;
cvt CFCTR_OK_CV;;

(* cfctr_map: a total version, equal to it where cfctr_ok holds              *)
let cfctr_map_t = define
 `(cfctr_map_t mr mc [] = ([]:(cpstep)list)) /\
  (cfctr_map_t mr mc (CONS (CpR i) cp') =
     (let mr' = rotr_list i mr in
      CONS (CpR (count_false (take_list i mr'))) (cfctr_map_t mr' mc cp'))) /\
  (cfctr_map_t mr mc (CONS CpRr cp') = []) /\
  (cfctr_map_t [] mc [CpY] = []) /\
  (cfctr_map_t [b1] mc [CpY] = []) /\
  (cfctr_map_t [b1; b2] mc [CpY] = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 (CONS b3 mr'))) mc [CpY] =
     (if b1 \/ (b2 \/ b3) then [] else [CpY])) /\
  (cfctr_map_t [] mc (CONS CpY (CONS s cp'')) = []) /\
  (cfctr_map_t [b1] mc (CONS CpY (CONS s cp'')) = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) [] (CONS CpY (CONS s cp'')) = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) (CONS b3 mc') (CONS CpY (CONS s cp'')) =
     (if b1 \/ b2 then cfctr_map_t (CONS b3 mr') mc' (CONS s cp'')
      else CONS (if b3 then CpU else CpY)
                (cfctr_map_t (CONS b3 mr') mc' (CONS s cp'')))) /\
  (cfctr_map_t [] mc (CONS CpH cp') = []) /\
  (cfctr_map_t [b1] mc (CONS CpH cp') = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) [] (CONS CpH cp') = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) [b3] (CONS CpH cp') = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) [b3; b4] (CONS CpH cp') = []) /\
  (cfctr_map_t (CONS b1 (CONS b2 mr')) (CONS b3 (CONS b4 (CONS b5 mc')))
               (CONS CpH cp') =
     (let cpc = cfctr_map_t (CONS b4 (CONS b5 mr')) mc' cp' in
      if b3 then cpc
      else if b1 then (if b2 then CONS CpA cpc else if b5 then cpc
                       else CONS CpK cpc)
      else if b2 then (if b4 then cpc else CONS CpK cpc)
      else if b4 then (if b5 then CONS CpU cpc else CONS CpY cpc)
      else if b5 then CONS CpY cpc else CONS CpH cpc)) /\
  (cfctr_map_t mr mc (CONS CpU cp') = []) /\
  (cfctr_map_t mr mc (CONS CpK cp') = []) /\
  (cfctr_map_t mr mc (CONS CpA cp') = [])`;;

let LIST_NONEMPTY = prove
 (`!l:A list. ~(l = []) <=> ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let CV_SUBST_VARS_TAC =
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
            is_eq (concl th) && is_var (lhs (concl th)))));;

let CFCTR_MAP_T = prove
 (`!cp mr mc. cfctr_ok mr mc cp ==> cfctr_map mr mc cp = cfctr_map_t mr mc cp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[cfctr_ok] THEN
  STRUCT_CASES_TAC (SPEC `h:cpstep` (cases "cpstep")) THEN
  REWRITE_TAC[cfctr_ok; cfctr_map; cfctr_map_t; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT GEN_TAC THENL
   [ASM_SIMP_TAC[COUNT_FALSE];
    ASM_CASES_TAC `t:cpstep list = []` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `s:cpstep` (X_CHOOSE_THEN `c:cpstep list`
        SUBST_ALL_TAC) o REWRITE_RULE[LIST_NONEMPTY])] THEN
    REWRITE_TAC[LEN_GE_1; LEN_GE_2; LEN_GE_3] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV (CHANGED_CONV cv_el_conv)) THEN
    ASM_SIMP_TAC[cfctr_map_t; HD; TL; LET_DEF; LET_END_DEF] THEN
    CV_SUBST_VARS_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[HD; TL]) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[LEN_GE_1; LEN_GE_2; LEN_GE_3] THEN STRIP_TAC THEN
    CV_SUBST_VARS_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV (CHANGED_CONV cv_el_conv)) THEN
    RULE_ASSUM_TAC (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV cv_el_conv))) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[HD; TL]) THEN
    REWRITE_TAC[HD; TL; cfctr_map_t; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[]]);;
cvt cfctr_map_t;;

let CFCTR_CV = prove
 (`!mr mc cp. cfctr mr mc cp =
     if cfctr_ok mr mc cp then SOME (cfctr_map_t mr mc cp) else NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cfctr] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CFCTR_MAP_T]);;
cvt CFCTR_CV;;

(* ------------------------------------------------------------------------- *)
(* cpadj and ctrband: total versions (hd0, tlb for HD, TL) and the          *)
(* conditions under which they agree with the definitions.                   *)
(* ------------------------------------------------------------------------- *)

let cpadj_t = define
  `(cpadj_t (cm:(bool)list#(bool)list) [] =
      (CONS (hd0 (tlb (FST cm))) (CONS (hd0 (FST cm)) []), SND cm)) /\
   (cpadj_t cm (CONS (CpR n) cp') =
      (let r = cpadj_t (rotr_list n (FST cm), SND cm) cp' in
       (rot_list n (FST r), SND r))) /\
   (cpadj_t cm (CONS CpY cp') =
      (let mr = FST cm in
       let b0 = hd0 mr in let b1 = hd0 (tlb mr) in let b2 = hd0 (tlb (tlb mr)) in
       let res = cpadj_t (CONS b0 (CONS b2 (tlb (tlb (tlb mr)))), SND cm) cp' in
       let a0 = hd0 (FST res) in let a2 = hd0 (tlb (FST res)) in
       let mr' = tlb (tlb (FST res)) in
       (CONS (a0 \/ b1) (CONS (b0 \/ b2) (CONS (a2 \/ b1) mr')), SND res))) /\
   (cpadj_t cm (CONS CpH cp') =
      (let mr = FST cm in let mk = SND cm in
       let b0 = hd0 mr in let b1 = hd0 (tlb mr) in let b1' = hd0 mk in
       let res = cpadj_t (CONS b0 (CONS b1' (tlb (tlb mr))), tlb mk) cp' in
       let a0 = hd0 (FST res) in let a1 = hd0 (tlb (FST res)) in
       let mr' = tlb (tlb (FST res)) in
       (CONS (a0 \/ b1)
             (CONS (b0 \/ b1' \/ hd0 (APPEND (tlb (tlb mr)) [b0]))
                   (if mr' = [] then [] else CONS (hd0 mr' \/ b1) (tlb mr'))),
        CONS (a1 \/ b1) (SND res)))) /\
   (cpadj_t cm (CONS CpRr cp') = ([],[])) /\
   (cpadj_t cm (CONS CpU cp') = ([],[])) /\
   (cpadj_t cm (CONS CpK cp') = ([],[])) /\
   (cpadj_t cm (CONS CpA cp') = ([],[]))`;;

let cpadj_ok = define
  `(cpadj_ok (cm:(bool)list#(bool)list) [] <=> 2 <= LENGTH (FST cm)) /\
   (cpadj_ok cm (CONS (CpR n) cp') <=> cpadj_ok (rotr_list n (FST cm), SND cm) cp') /\
   (cpadj_ok cm (CONS CpY cp') <=>
      3 <= LENGTH (FST cm) /\
      (let mr = FST cm in
       let cm' = (CONS (hd0 mr) (CONS (hd0 (tlb (tlb mr))) (tlb (tlb (tlb mr)))),
                  SND cm) in
       cpadj_ok cm' cp' /\ 2 <= LENGTH (FST (cpadj_t cm' cp')))) /\
   (cpadj_ok cm (CONS CpH cp') <=>
      2 <= LENGTH (FST cm) /\ 1 <= LENGTH (SND cm) /\
      (let mr = FST cm in let mk = SND cm in
       let cm' = (CONS (hd0 mr) (CONS (hd0 mk) (tlb (tlb mr))), tlb mk) in
       cpadj_ok cm' cp' /\ 2 <= LENGTH (FST (cpadj_t cm' cp')))) /\
   (cpadj_ok cm (CONS CpRr cp') <=> F) /\
   (cpadj_ok cm (CONS CpU cp') <=> F) /\
   (cpadj_ok cm (CONS CpK cp') <=> F) /\
   (cpadj_ok cm (CONS CpA cp') <=> F)`;;

let HD0_TLB_CONS = prove
 (`(!h t. hd0 (CONS h t) = h) /\ (!h t. tlb (CONS h t) = t)`,
  REWRITE_TAC[hd0; tlb]);;

let HD0_APPEND1 = prove
 (`!l x. hd0 (APPEND l [x]) = HD (APPEND l [x])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; HD; hd0]);;
let COND_HD0 = prove
 (`!l b. (if l = [] then [] else CONS (hd0 l \/ b) (tlb l)) =
         (if l = [] then [] else CONS (HD l \/ b) (TL l))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; hd0; tlb; NOT_CONS_NIL]);;

let CPADJ_T = prove
 (`!cp cm. cpadj_ok cm cp ==> cpadj cm cp = cpadj_t cm cp`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; cpadj_ok; LEN_GE_2] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[cpadj; cpadj_t; HD; TL; hd0; tlb];
    STRUCT_CASES_TAC (SPEC `h:cpstep` (cases "cpstep")) THEN
    REWRITE_TAC[FORALL_PAIR_THM; cpadj_ok; LEN_GE_1; LEN_GE_2; LEN_GE_3;
                LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
    CV_SUBST_VARS_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HD0_TLB_CONS; FST; SND]) THEN
    ASM_SIMP_TAC[cpadj; cpadj_t; LET_DEF; LET_END_DEF; FST; SND; HD; TL;
                 HD0_TLB_CONS] THEN
    REWRITE_TAC[HD0_APPEND1; COND_HD0]]);;

let ctrband_t = define
 `(ctrband_t (cm:(bool)list) [] = ([]:(bool)list,[]:(bool)list)) /\
  (ctrband_t cm (CONS (CpR n) cp') =
     (let r = ctrband_t cm cp' in (rot_list n (FST r), SND r))) /\
  (ctrband_t cm (CONS CpRr cp') = ([],[])) /\
  (ctrband_t cm (CONS CpY cp') =
     (if cp' = [] then (REPLICATE 3 F, [])
      else
        (let b1 = hd0 cm in let cm' = tlb cm in
         let res = ctrband_t cm' cp' in let mr = FST res in let mk = SND res in
         if 2 <= LENGTH mr then
           (CONS (b1 \/ hd0 mr) (CONS F (CONS (b1 \/ hd0 (tlb mr)) (tlb (tlb mr)))),
            mk)
         else ([],[])))) /\
  (ctrband_t cm (CONS CpH cp') =
     (let b1 = hd0 cm in let b0 = hd0 (tlb cm) in let b2 = hd0 (tlb (tlb cm)) in
      let cm' = tlb (tlb (tlb cm)) in
      let res = ctrband_t cm' cp' in let mr = FST res in let mk = SND res in
      if 3 <= LENGTH mr then
        (CONS (b0 \/ hd0 mr)
              (CONS b1 (CONS (b2 \/ hd0 (tlb (tlb mr))) (tlb (tlb (tlb mr))))),
         CONS (b0 \/ b1 \/ b2 \/ hd0 (tlb mr)) mk)
      else ([],[]))) /\
  (ctrband_t cm (CONS CpU cp') = ([],[])) /\
  (ctrband_t cm (CONS CpK cp') = ([],[])) /\
  (ctrband_t cm (CONS CpA cp') = ([],[]))`;;

let ctrband_cvok = define
 `(ctrband_cvok (cm:(bool)list) [] <=> T) /\
  (ctrband_cvok cm (CONS (CpR n) cp') <=> ctrband_cvok cm cp') /\
  (ctrband_cvok cm (CONS CpRr cp') <=> T) /\
  (ctrband_cvok cm (CONS CpY cp') <=>
     (cp' = [] \/ (1 <= LENGTH cm /\ ctrband_cvok (tlb cm) cp'))) /\
  (ctrband_cvok cm (CONS CpH cp') <=>
     3 <= LENGTH cm /\ ctrband_cvok (tlb (tlb (tlb cm))) cp') /\
  (ctrband_cvok cm (CONS CpU cp') <=> T) /\
  (ctrband_cvok cm (CONS CpK cp') <=> T) /\
  (ctrband_cvok cm (CONS CpA cp') <=> T)`;;

let HD_TL_LEN2 = prove
 (`!l. 2 <= LENGTH l ==> hd0 l = HD l /\ hd0 (tlb l) = HD (TL l) /\
                         tlb (tlb l) = TL (TL l) /\ tlb l = TL l`,
  REWRITE_TAC[LEN_GE_2] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[HD; TL; hd0; tlb]);;
let HD_TL_LEN3 = prove
 (`!l. 3 <= LENGTH l ==> hd0 l = HD l /\ hd0 (tlb l) = HD (TL l) /\
                         hd0 (tlb (tlb l)) = HD (TL (TL l)) /\
                         tlb (tlb (tlb l)) = TL (TL (TL l))`,
  REWRITE_TAC[LEN_GE_3] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[HD; TL; hd0; tlb]);;

let CTRBAND_T = prove
 (`!cp cm. ctrband_cvok cm cp ==> ctrband cm cp = ctrband_t cm cp`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ctrband; ctrband_t]; ALL_TAC] THEN
  STRUCT_CASES_TAC (SPEC `h:cpstep` (cases "cpstep")) THEN
  REWRITE_TAC[ctrband_cvok; LEN_GE_1; LEN_GE_3; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  CV_SUBST_VARS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[HD0_TLB_CONS; FST; SND]) THEN
  ASM_SIMP_TAC[ctrband; ctrband_t; LET_DEF; LET_END_DEF; FST; SND; HD; TL;
               HD0_TLB_CONS] THEN
  TRY (ASM_CASES_TAC `t:cpstep list = []` THEN ASM_REWRITE_TAC[]) THEN
  TRY (COND_CASES_TAC THEN ASM_SIMP_TAC[HD_TL_LEN2; HD_TL_LEN3]));;

(* ------------------------------------------------------------------------- *)
(* The triad check and the contract tree, with the ring size n explicit.     *)
(* ------------------------------------------------------------------------- *)

cvt mask_pred1_from;; cvt mask_pred1;;
let CPKSIZE_CV = REWRITE_RULE[COUNT_H] cpksize;;
cvt CPKSIZE_CV;;
let cfmask1_n = new_definition
  `cfmask1_n n (cp:(cpstep)list) (i:num) =
     (REPLICATE n F, mask_pred1 i (cpksize cp))`;;
let CFMASK1_N = prove
 (`!cp i. cfmask1 cp i = cfmask1_n (cprsize cp) cp i`,
  REWRITE_TAC[cfmask1; cfmask1_n]);;
cvt cfmask1_n;;

cvt cpadj_t;; cvt cpadj_ok;;
cvt ctrband_t;; cvt ctrband_cvok;;

let cptriad_t = define
 `(cptriad_t n (ccm:(bool)list#(bool)list) (cp:(cpstep)list) 0 = F) /\
  (cptriad_t n ccm cp (SUC i') =
     let adjm = cpadj_t (cfmask1_n n cp i') cp in
     let mct = APPEND (mask_list (FST ccm) (FST adjm))
                      (mask_list (SND ccm) (SND adjm)) in
     if exists_false mct /\ 2 < count_true mct then T
     else cptriad_t n ccm cp i')`;;
let cptriad_ok = define
 `(cptriad_ok n (cp:(cpstep)list) 0 = T) /\
  (cptriad_ok n cp (SUC i) <=>
     cpadj_ok (cfmask1_n n cp i) cp /\ cptriad_ok n cp i)`;;
do_list cvt [cptriad_t; cptriad_ok];;

let valid_ctrm_t = new_definition
 `valid_ctrm_t n (cm:(bool)list) (cp:(cpstep)list) =
    (let k = count_true cm in
     if k = 4 then cptriad_t n (ctrband_t cm cp) cp (count_h cp)
     else 0 < k /\ k <= 3)`;;
let valid_ok = new_definition
 `valid_ok n (cm:(bool)list) (cp:(cpstep)list) <=>
    (count_true cm = 4 ==> ctrband_cvok cm cp /\ cptriad_ok n cp (count_h cp))`;;
do_list cvt [valid_ctrm_t; valid_ok];;

let cco_t = define
 `(cco_t n cm cp NONE = NONE) /\
  (cco_t n cm cp (SOME cpc) =
     if valid_ctrm_t n cm cp then SOME (cpcolor cpc) else NONE)`;;
let contract_t = new_definition
 `contract_t n (cf:(cpstep)list#(num)list) =
    cco_t n (cfcontract_mask cf) (cfprog cf)
      (cfctr (REPLICATE n F) (cfcontract_mask cf) (cfprog cf))`;;
let check_red_t = define
 `(check_red_t (kp:ctree) NONE = F) /\
  (check_red_t kp (SOME cct) = ctree_disjoint kp cct)`;;
let sized_check = new_definition
 `sized_check n (cf:(cpstep)list#(num)list) <=>
    2 <= n /\ valid_ok n (cfcontract_mask cf) (cfprog cf) /\
    check_red_t (kempe_tree_h (n - 2) (cfprog cf)) (contract_t n cf)`;;
do_list cvt [cco_t; contract_t; check_red_t; sized_check];;

(* ------------------------------------------------------------------------- *)
(* Soundness of the sized check.                                             *)
(* ------------------------------------------------------------------------- *)

let CPTRIAD_T = prove
 (`!k ccm cp. cptriad_ok (cprsize cp) cp k
              ==> cptriad ccm cp k = cptriad_t (cprsize cp) ccm cp k`,
  INDUCT_TAC THEN REWRITE_TAC[cptriad; cptriad_t; cptriad_ok] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; CFMASK1_N] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[CPADJ_T; EXISTS_FALSE; COUNT_TRUE]);;

let VALID_CTRM_T = prove
 (`!cm cp. valid_ok (cprsize cp) cm cp
           ==> valid_ctrm cm cp = valid_ctrm_t (cprsize cp) cm cp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_ok; valid_ctrm; valid_ctrm_t;
    LET_DEF; LET_END_DEF; COUNT_TRUE; CPKSIZE_CV] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CTRBAND_T; CPTRIAD_T]);;

let SIZED_CHECK_SOUND = prove
 (`!cf. sized_check (cprsize (cfprog cf)) cf ==> check_reducible cf`,
  GEN_TAC THEN REWRITE_TAC[sized_check; check_reducible; contract_t;
    contract_ctree; kempe_tree; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM kempe_tree_h] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
  SPEC_TAC(`cfctr (REPLICATE (cprsize (cfprog cf)) F) (cfcontract_mask cf)
              (cfprog cf)`, `oc:(cpstep list)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[cco_t; check_red_t; distinctness "option"] THEN
  CONV_TAC(ONCE_DEPTH_CONV MATCH_CONV) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_SIMP_TAC[VALID_CTRM_T] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[check_red_t; distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;
