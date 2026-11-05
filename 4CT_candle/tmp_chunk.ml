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
