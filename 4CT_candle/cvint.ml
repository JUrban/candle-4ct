(* ========================================================================= *)
(* 4CT_candle/cvint.ml                                                       *)
(*                                                                           *)
(* Integers for cvtrans.ml.  An integer i is encoded as the pair             *)
(* (int_pos i, int_negp i) of natural numbers with i = &a - &b and a = 0 or *)
(* b = 0, so that  cv_of_int (&a - &b) = (a - b, b - a)  (truncating        *)
(* subtraction) for all a, b.  The integer operations &, --, +, -, *, <, <=  *)
(* get code by that equation; int_pos is a total num_of_int (0 for negative  *)
(* arguments).                                                               *)
(* ========================================================================= *)

needs "4CT_candle/cvtrans.ml";;

let int_pos = new_definition
 `int_pos (i:int) = if &0 <= i then num_of_int i else 0`;;
let int_negp = new_definition
 `int_negp (i:int) = if &0 <= i then 0 else num_of_int (--i)`;;
let cv_of_int = new_definition
 `cv_of_int (i:int) = Cexp_pair (Cexp_num (int_pos i)) (Cexp_num (int_negp i))`;;

let INT_DECOMP = prove
 (`!i:int. i = &(int_pos i) - &(int_negp i)`,
  GEN_TAC THEN REWRITE_TAC[int_pos; int_negp] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_SUB_RZERO; INT_SUB_LZERO;
               INT_ARITH `~(&0 <= i:int) ==> &0 <= --i`; INT_NEG_NEG]);;

let CV_OF_INT_DIFF = prove
 (`!a b. cv_of_int (&a - &b) = Cexp_pair (Cexp_num (a - b)) (Cexp_num (b - a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cv_of_int; int_pos; int_negp; injectivity "cval"] THEN
  DISJ_CASES_TAC (ARITH_RULE `b <= a \/ a < b`) THENL
   [ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_POS; NUM_OF_INT_OF_NUM] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(&0 <= &a - &b:int)` ASSUME_TAC THENL
     [REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[INT_NEG_SUB] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; LT_IMP_LE; NUM_OF_INT_OF_NUM] THEN
    ASM_ARITH_TAC]);;

let CV_OF_INT_11 = prove
 (`!i j. cv_of_int i = cv_of_int j <=> i = j`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[INT_DECOMP] THEN
  REWRITE_TAC[CV_OF_INT_DIFF; injectivity "cval"] THEN
  REWRITE_TAC[GSYM INT_DECOMP] THEN
  MAP_EVERY (fun t -> MP_TAC (SPEC t INT_DECOMP)) [`i:int`; `j:int`] THEN
  REPEAT DISCH_TAC THEN STRIP_TAC THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `&a - &b:int = &c - &d <=> &a + &d:int = &c + &b`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

cv_types := ("int", (`cv_of_int`, [], cv_of_int)) :: !cv_types;;
cv_inj := ("int", CV_OF_INT_11) :: !cv_inj;;

(* code: v = (a,b) and w = (c,d) encode &a - &b and &c - &d                  *)
let cvi_norm = new_definition
 `cvi_norm x y = Cexp_pair (Cexp_sub x y) (Cexp_sub y x)`;;
let cvi_of_num = new_definition `cvi_of_num v = Cexp_pair v (Cexp_num 0)`;;
let cvi_neg = new_definition `cvi_neg v = Cexp_pair (Cexp_snd v) (Cexp_fst v)`;;
let cvi_add = new_definition
 `cvi_add v w = cvi_norm (Cexp_add (Cexp_fst v) (Cexp_fst w))
                         (Cexp_add (Cexp_snd v) (Cexp_snd w))`;;
let cvi_sub = new_definition
 `cvi_sub v w = cvi_norm (Cexp_add (Cexp_fst v) (Cexp_snd w))
                         (Cexp_add (Cexp_snd v) (Cexp_fst w))`;;
let cvi_mul = new_definition
 `cvi_mul v w =
    cvi_norm (Cexp_add (Cexp_mul (Cexp_fst v) (Cexp_fst w))
                       (Cexp_mul (Cexp_snd v) (Cexp_snd w)))
             (Cexp_add (Cexp_mul (Cexp_fst v) (Cexp_snd w))
                       (Cexp_mul (Cexp_snd v) (Cexp_fst w)))`;;
let cvi_lt = new_definition
 `cvi_lt v w = Cexp_less (Cexp_add (Cexp_fst v) (Cexp_snd w))
                         (Cexp_add (Cexp_fst w) (Cexp_snd v))`;;
let cvi_le = new_definition
 `cvi_le v w = Cexp_less (Cexp_add (Cexp_fst v) (Cexp_snd w))
                         (Cexp_add (Cexp_add (Cexp_fst w) (Cexp_snd v)) (Cexp_num 1))`;;
let cvi_pos = new_definition `cvi_pos v = Cexp_fst v`;;

let CVI_RW = [cvi_norm; cvi_of_num; cvi_neg; cvi_add; cvi_sub; cvi_mul; cvi_lt;
              cvi_le; cvi_pos; cexp_fst_def; cexp_snd_def; cexp_add_def;
              cexp_sub_def; cexp_mul_def; cexp_less_def; cv_of_bool];;

let CVI_DECOMP_TAC =
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
  REWRITE_TAC[CV_OF_INT_DIFF] THEN
  REWRITE_TAC[GSYM INT_DECOMP];;

let CV_INT_THMS = [
  ("int_of_num", prove
   (`!n. cv_of_int (&n) = cvi_of_num (Cexp_num n)`,
    GEN_TAC THEN ONCE_REWRITE_TAC[INT_ARITH `&n:int = &n - &0`] THEN
    REWRITE_TAC[CV_OF_INT_DIFF; cvi_of_num; SUB_0; ARITH_RULE `0 - n = 0`]));
  ("int_neg", prove
   (`!i. cv_of_int (--i) = cvi_neg (cv_of_int i)`,
    GEN_TAC THEN ONCE_REWRITE_TAC[SPEC `i:int` INT_DECOMP] THEN
    REWRITE_TAC[INT_NEG_SUB; CV_OF_INT_DIFF; cvi_neg; cexp_fst_def;
                cexp_snd_def]));
  ("int_add", prove
   (`!i j. cv_of_int (i + j) = cvi_add (cv_of_int i) (cv_of_int j)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
    REWRITE_TAC[INT_ARITH `(&a - &b) + (&c - &d):int = &(a + c) - &(b + d)`;
                GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[CV_OF_INT_DIFF] THEN REWRITE_TAC CVI_RW));
  ("int_sub", prove
   (`!i j. cv_of_int (i - j) = cvi_sub (cv_of_int i) (cv_of_int j)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
    REWRITE_TAC[INT_ARITH `(&a - &b) - (&c - &d):int = &(a + d) - &(b + c)`;
                GSYM INT_OF_NUM_ADD] THEN
    REWRITE_TAC[CV_OF_INT_DIFF] THEN REWRITE_TAC CVI_RW));
  ("int_mul", prove
   (`!i j. cv_of_int (i * j) = cvi_mul (cv_of_int i) (cv_of_int j)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
    REWRITE_TAC[INT_ARITH `(&a - &b) * (&c - &d):int =
                           &(a * c + b * d) - &(a * d + b * c)`;
                GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC[CV_OF_INT_DIFF] THEN REWRITE_TAC CVI_RW));
  ("int_lt", prove
   (`!i j. cv_of_bool (i < j) = cvi_lt (cv_of_int i) (cv_of_int j)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
    REWRITE_TAC[CV_OF_INT_DIFF] THEN REWRITE_TAC CVI_RW THEN
    REWRITE_TAC[INT_ARITH `(&a - &b) < (&c - &d):int <=> &(a + d) < &(c + b)`;
                GSYM INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN
    REWRITE_TAC[injectivity "cval"] THEN
    MAP_EVERY (fun t -> MP_TAC (SPEC t INT_DECOMP)) [`i:int`; `j:int`] THEN
    REWRITE_TAC[int_pos; int_negp] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[] THEN ARITH_TAC));
  ("int_le", prove
   (`!i j. cv_of_bool (i <= j) = cvi_le (cv_of_int i) (cv_of_int j)`,
    REPEAT GEN_TAC THEN
    MAP_EVERY (fun t -> ONCE_REWRITE_TAC[SPEC t INT_DECOMP]) [`i:int`; `j:int`] THEN
    REWRITE_TAC[CV_OF_INT_DIFF] THEN REWRITE_TAC CVI_RW THEN
    REWRITE_TAC[INT_ARITH `(&a - &b) <= (&c - &d):int <=> &(a + d) <= &(c + b)`;
                GSYM INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN
    REWRITE_TAC[injectivity "cval"] THEN
    MAP_EVERY (fun t -> MP_TAC (SPEC t INT_DECOMP)) [`i:int`; `j:int`] THEN
    REWRITE_TAC[int_pos; int_negp] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[] THEN ARITH_TAC));
  ("int_pos", prove
   (`!i. Cexp_num (int_pos i) = cvi_pos (cv_of_int i)`,
    REWRITE_TAC[cvi_pos; cv_of_int; cexp_fst_def]))];;

cv_fun_thms := CV_INT_THMS @ !cv_fun_thms;;
cv_code := map SPEC_ALL [cvi_norm; cvi_of_num; cvi_neg; cvi_add; cvi_sub;
                         cvi_mul; cvi_lt; cvi_le; cvi_pos] @ !cv_code;;

(* the total num_of_int *)
let NUM_OF_INT_POS = prove
 (`!i:int. &0 <= i ==> num_of_int i = int_pos i`,
  SIMP_TAC[int_pos]);;
