(* ========================================================================= *)
(* 4CT_candle/cvtrans.ml                                                     *)
(*                                                                           *)
(* A translator from first-order HOL functions to cval ("cv") functions for  *)
(* Candle's verified compute primitive Kernel.compute, in the style of       *)
(* HOL4's cv_transLib.                                                       *)
(*                                                                           *)
(* Encoders.  Every supported type ty has an encoder enc_ty : ty -> cval:    *)
(*   num -> Cexp_num, bool -> cv_of_bool (T = 1, F = 0), A # B ->           *)
(*   cv_of_prod enc_A enc_B, a type variable A -> a variable enc_A, and a    *)
(*   datatype T (registered with cv_register_type) -> cv_of_T applied to the *)
(*   encoders of its type arguments.  A datatype value is encoded as         *)
(*     nullary constructor number j (in order)      -> Cexp_num j            *)
(*     the only non-nullary constructor, args xs     -> args xs              *)
(*     non-nullary constructor number j, args xs     -> Cexp_pair (num j) xs *)
(*   where args [x] = enc x (or Cexp_pair (enc x) (num 0) if the type also   *)
(*   has nullary constructors and no tags) and args (x::xs) for two or more  *)
(*   arguments is the right-nested Cexp_pair of the encodings.               *)
(*                                                                           *)
(* Functions.  For a function f given by clauses with constructor patterns,  *)
(* cv_translate defines a constant cv_f : cval -> ... -> cval by             *)
(* well-founded recursion (measure: cval_sum_size of one argument, chosen    *)
(* automatically), proves the compute equation |- cv_f v1 .. vn = E (E a    *)
(* compute expression) and the correctness theorem                           *)
(*   |- !x1 .. xn. enc (f x1 .. xn) = cv_f (enc x1) .. (enc xn).             *)
(* The code of each clause is produced by "pushing the encoder in"          *)
(* (cv_tr_conv), which at the same time proves it correct.                   *)
(* ========================================================================= *)

let cv_ty = `:cval`;;
let cexp_num_tm = `Cexp_num` and cexp_pair_tm = `Cexp_pair`
and cexp_fst_tm = `Cexp_fst` and cexp_snd_tm = `Cexp_snd`
and cexp_if_tm = `Cexp_if` and cexp_eq_tm = `Cexp_eq`
and cexp_ispair_tm = `Cexp_ispair` and cexp_add_tm = `Cexp_add`
and cexp_sub_tm = `Cexp_sub` and cexp_less_tm = `Cexp_less`;;

let mk_cnum n = mk_comb(cexp_num_tm, mk_small_numeral n);;
let mk_cpair a b = list_mk_comb(cexp_pair_tm, [a; b]);;
let mk_cfst a = mk_comb(cexp_fst_tm, a) and mk_csnd a = mk_comb(cexp_snd_tm, a);;
let mk_cif c a b = list_mk_comb(cexp_if_tm, [c; a; b]);;
let mk_ceq a b = list_mk_comb(cexp_eq_tm, [a; b]);;
let mk_cispair a = mk_comb(cexp_ispair_tm, a);;

(* ------------------------------------------------------------------------- *)
(* Basic encoders and lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let cv_of_bool = new_definition
  `cv_of_bool b = Cexp_num (if b then 1 else 0)`;;

let CV_OF_BOOL_CLAUSES = prove
 (`cv_of_bool T = Cexp_num 1 /\ cv_of_bool F = Cexp_num 0`,
  REWRITE_TAC[cv_of_bool]);;

let CV_OF_BOOL_11 = prove
 (`!a b. cv_of_bool a = cv_of_bool b <=> a = b`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`a:bool`; `b:bool`] THEN
  REWRITE_TAC[cv_of_bool; injectivity "cval"] THEN ARITH_TAC);;

let cv_of_prod = new_definition
  `cv_of_prod (f:A->cval) (g:B->cval) p = Cexp_pair (f (FST p)) (g (SND p))`;;

let CV_OF_PROD_PAIR = prove
 (`!f g (a:A) (b:B). cv_of_prod f g (a,b) = Cexp_pair (f a) (g b)`,
  REWRITE_TAC[cv_of_prod]);;

let CV_OF_PROD_11 = prove
 (`!f g. (!x y. (f:A->cval) x = f y <=> x = y) /\
         (!x y. (g:B->cval) x = g y <=> x = y)
         ==> !p q. cv_of_prod f g p = cv_of_prod f g q <=> p = q`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t PAIR_SURJECTIVE))
   [`p:A#B`; `q:A#B`] THEN
  ASM_REWRITE_TAC[cv_of_prod; injectivity "cval"; PAIR_EQ]);;

let CEXP_NUM_11 = prove
 (`!m n. Cexp_num m = Cexp_num n <=> m = n`,
  REWRITE_TAC[injectivity "cval"]);;

let CEXP_IF_TRUE = prove
 (`!p q. Cexp_if (Cexp_num 1) p q = p`,
  REWRITE_TAC[ONE; cexp_if_def]);;

let CEXP_IF_FALSE = prove
 (`!p q. Cexp_if (Cexp_num 0) p q = q`,
  REWRITE_TAC[cexp_if_def]);;

let CV_TR_COND = prove
 (`!(e:A->cval) c a b.
     e (if c then a else b) = Cexp_if (cv_of_bool c) (e a) (e b)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[CV_OF_BOOL_CLAUSES; CEXP_IF_TRUE; CEXP_IF_FALSE]);;

let CV_TR_FST = prove
 (`!(f:A->cval) (g:B->cval) p. f (FST p) = Cexp_fst (cv_of_prod f g p)`,
  REWRITE_TAC[cv_of_prod; cexp_fst_def]);;

let CV_TR_SND = prove
 (`!(f:A->cval) (g:B->cval) p. g (SND p) = Cexp_snd (cv_of_prod f g p)`,
  REWRITE_TAC[cv_of_prod; cexp_snd_def]);;

let CV_TR_EQ = prove
 (`!(e:A->cval). (!x y. e x = e y <=> x = y)
     ==> !x y. cv_of_bool (x = y) = Cexp_eq (e x) (e y)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cexp_eq_def; cv_of_bool] THEN
  REWRITE_TAC[ONE]);;

let CV_TR_NUM = prove
 (`(!m n. Cexp_num (m + n) = Cexp_add (Cexp_num m) (Cexp_num n)) /\
   (!m n. Cexp_num (m - n) = Cexp_sub (Cexp_num m) (Cexp_num n)) /\
   (!m n. Cexp_num (m * n) = Cexp_mul (Cexp_num m) (Cexp_num n)) /\
   (!m n. Cexp_num (m DIV n) = Cexp_div (Cexp_num m) (Cexp_num n)) /\
   (!m n. Cexp_num (m MOD n) = Cexp_mod (Cexp_num m) (Cexp_num n)) /\
   (!n. Cexp_num (SUC n) = Cexp_add (Cexp_num n) (Cexp_num 1)) /\
   (!n. Cexp_num (PRE n) = Cexp_sub (Cexp_num n) (Cexp_num 1))`,
  REWRITE_TAC[cexp_add_def; cexp_sub_def; cexp_mul_def; cexp_div_def;
              cexp_mod_def; ADD1; injectivity "cval"] THEN ARITH_TAC);;

let CV_TR_BOOL = prove
 (`(!m n. cv_of_bool (m < n) = Cexp_less (Cexp_num m) (Cexp_num n)) /\
   (!m n. cv_of_bool (m <= n) =
          Cexp_less (Cexp_num m) (Cexp_add (Cexp_num n) (Cexp_num 1))) /\
   (!m n. cv_of_bool (m > n) = Cexp_less (Cexp_num n) (Cexp_num m)) /\
   (!m n. cv_of_bool (m >= n) =
          Cexp_less (Cexp_num n) (Cexp_add (Cexp_num m) (Cexp_num 1))) /\
   (!p. cv_of_bool (~p) = Cexp_if (cv_of_bool p) (Cexp_num 0) (Cexp_num 1)) /\
   (!p q. cv_of_bool (p /\ q) =
          Cexp_if (cv_of_bool p) (cv_of_bool q) (Cexp_num 0)) /\
   (!p q. cv_of_bool (p \/ q) =
          Cexp_if (cv_of_bool p) (Cexp_num 1) (cv_of_bool q)) /\
   (!p q. cv_of_bool (p ==> q) =
          Cexp_if (cv_of_bool p) (cv_of_bool q) (Cexp_num 1))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[cexp_less_def; cexp_add_def; GT; GE; GSYM ONE] THEN
  REWRITE_TAC[cv_of_bool; LT_SUC_LE; GSYM ADD1] THEN
  TRY (BOOL_CASES_TAC `p:bool` THEN TRY (BOOL_CASES_TAC `q:bool`)) THEN
  REWRITE_TAC[CEXP_IF_TRUE; CEXP_IF_FALSE]);;

(* cval_sum_size facts for the termination and induction proofs *)
let CSS_FST_LE = prove
 (`!x. cval_sum_size (Cexp_fst x) <= cval_sum_size x`,
  MATCH_MP_TAC cval_INDUCT THEN
  REWRITE_TAC[cexp_fst_def; cval_sum_size_def] THEN ARITH_TAC)
and CSS_SND_LE = prove
 (`!x. cval_sum_size (Cexp_snd x) <= cval_sum_size x`,
  MATCH_MP_TAC cval_INDUCT THEN
  REWRITE_TAC[cexp_snd_def; cval_sum_size_def] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The type registry.                                                        *)
(*   cv_types : tyname -> (generic encoder constant, type variables (in the   *)
(*              order of the type's arguments), encoder definition)          *)
(*   cv_cons  : constructor name -> (tyname, kind, tag, arity, number of     *)
(*              nullary constructors) with kind 0 nullary (tag = its index   *)
(*              among the nullary ones), 1 the only non-nullary one          *)
(*              (untagged), 2 tagged non-nullary.                            *)
(*   cv_inj   : tyname -> injectivity theorem of the encoder                 *)
(* ------------------------------------------------------------------------- *)

let cv_types = ref ([] : (string * (term * hol_type list * thm)) list);;
let cv_cons = ref ([] : (string * (string * int * int * int * int)) list);;
let cv_inj = ref ([] : (string * thm) list);;
let cv_enc_clauses = ref ([] : thm list);;

let cv_sanitize s =
  implode (filter (fun c -> isalnum c) (explode s));;

let rec cv_enc_of ty =
  if is_vartype ty then
    mk_var("enc_" ^ cv_sanitize (dest_vartype ty), mk_fun_ty ty cv_ty)
  else
    let name,args = dest_type ty in
    if name = "num" then cexp_num_tm
    else if name = "bool" then `cv_of_bool`
    else if name = "prod" then
      let ea = cv_enc_of (hd args) and eb = cv_enc_of (hd (tl args)) in
      list_mk_comb(inst [hd args,`:A`; hd(tl args),`:B`] `cv_of_prod:(A->cval)->(B->cval)->A#B->cval`,
                   [ea; eb])
    else if name = "fun" then failwith ("cv_enc_of: function type " ^ string_of_type ty)
    else
      let c,tvs,_ = try assoc name (!cv_types) with Failure _ ->
        failwith ("cv_enc_of: unregistered type " ^ name) in
      let c' = inst (zip args tvs) c in
      list_mk_comb(c', map cv_enc_of args);;

(* the constructors of a type, from its cases theorem, in order               *)
let cv_constructors tyname =
  let th = if tyname = "num" then num_CASES else cases tyname in
  let x,bod = dest_forall (concl th) in
  let ds = disjuncts bod in
  let con d = let _,e = strip_exists d in fst(strip_comb(rhs e)) in
  (type_of x, map con ds, th);;

let cv_register_type tyname =
  let ty,cons,_ = cv_constructors tyname in
  let tvs = snd(dest_type ty) in
  let encname = "cv_of_" ^ tyname in
  let encty = itlist (fun a t -> mk_fun_ty (mk_fun_ty a cv_ty) t) tvs
                (mk_fun_ty ty cv_ty) in
  let encv = mk_var(encname, encty) in
  let penc = map cv_enc_of tvs in
  let arity c = length (fst(splitlist dest_fun_ty (type_of c))) in
  let nullary = filter (fun c -> arity c = 0) cons
  and nonnull = filter (fun c -> arity c > 0) cons in
  let na = length nullary and nb = length nonnull in
  (* encoders of the argument types: the recursive occurrences use encv    *)
  let enc_arg aty =
    if aty = ty then list_mk_comb(encv, penc) else cv_enc_of aty in
  let rec tuple ts = match ts with
      [t] -> t | t::rest -> mk_cpair t (tuple rest) | [] -> failwith "tuple" in
  let clause c =
    let atys = fst(splitlist dest_fun_ty (type_of c)) in
    let vs = map (fun (i,aty) -> mk_var("x" ^ string_of_int i, aty))
                 (zip (0--(length atys - 1)) atys) in
    let lhs = mk_comb(list_mk_comb(encv, penc), list_mk_comb(c, vs)) in
    let encs = map (fun v -> mk_comb(enc_arg (type_of v), v)) vs in
    let rhs =
      if atys = [] then mk_cnum (index c nullary)
      else if nb = 1 then
        (if length encs = 1 && na > 0 then mk_cpair (hd encs) (mk_cnum 0)
         else tuple encs)
      else mk_cpair (mk_cnum (index c nonnull)) (tuple encs) in
    mk_eq(lhs, rhs) in
  let def = define (list_mk_conj (map clause cons)) in
  let enc = fst(strip_comb(lhand(snd(strip_forall(hd(conjuncts(concl def))))))) in
  let enc = fst(strip_comb(rator(lhand(snd(strip_forall(hd(conjuncts(concl def)))))))) in
  cv_types := (tyname, (enc, tvs, def)) :: !cv_types;
  cv_enc_clauses := CONJUNCTS def @ !cv_enc_clauses;
  do_list (fun c ->
     let k = if arity c = 0 then 0 else if nb = 1 then 1 else 2 in
     let tag = if arity c = 0 then index c nullary
               else if nb = 1 then 0 else index c nonnull in
     cv_cons := (fst(dest_const c), (tyname, k, tag, arity c, na)) :: !cv_cons)
    cons;
  def;;

(* lists are needed by almost everything *)
let cv_of_list_DEF = cv_register_type "list";;
let cv_of_option_DEF = cv_register_type "option";;

(* injectivity of an encoder, by induction                                   *)
let cv_prove_inj tyname =
  let ty,cons,cth = cv_constructors tyname in
  let tvs = snd(dest_type ty) in
  let e = cv_enc_of ty in
  let _,ind,_ = assoc tyname (!inductive_type_store) in
  let x = mk_var("x",ty) and y = mk_var("y",ty) in
  let goal = mk_forall(x, mk_forall(y,
               mk_eq(mk_eq(mk_comb(e,x), mk_comb(e,y)), mk_eq(x,y)))) in
  let hyps = map (fun tv ->
      let ev = cv_enc_of tv in
      let a = mk_var("a",tv) and b = mk_var("b",tv) in
      list_mk_forall([a;b], mk_eq(mk_eq(mk_comb(ev,a),mk_comb(ev,b)),
                                  mk_eq(a,b)))) tvs in
  let gl = if hyps = [] then goal else mk_imp(list_mk_conj hyps, goal) in
  let _,_,def = assoc tyname (!cv_types) in
  let injs = (try [injectivity tyname] with Failure _ -> []) @
             (try [distinctness tyname] with Failure _ -> []) in
  let injs = injs @ (try map GSYM (CONJUNCTS (distinctness tyname))
                     with Failure _ -> []) in
  let th = prove(gl,
    (if hyps = [] then ALL_TAC else STRIP_TAC) THEN
    MATCH_MP_TAC ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    (fun (asl,w) -> STRUCT_CASES_TAC (ISPEC (rand(rand w)) cth) (asl,w)) THEN
    ASM_REWRITE_TAC (def :: injectivity "cval" :: distinctness "cval" ::
                     map GSYM (CONJUNCTS (distinctness "cval")) @ injs) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[]) in
  cv_inj := (tyname, th) :: !cv_inj;
  th;;

let CV_OF_LIST_11 = cv_prove_inj "list";;
let CV_OF_OPTION_11 = cv_prove_inj "option";;

(* ------------------------------------------------------------------------- *)
(* Injectivity of an arbitrary encoder term.                                 *)
(* ------------------------------------------------------------------------- *)

let rec cv_inj_of ty =
  if ty = `:num` then CEXP_NUM_11
  else if ty = bool_ty then CV_OF_BOOL_11
  else if is_vartype ty then failwith "cv_inj_of: type variable"
  else
    let name,args = dest_type ty in
    if name = "prod" then
      let th = ISPECL [cv_enc_of (hd args); cv_enc_of (hd(tl args))] CV_OF_PROD_11 in
      MP th (CONJ (cv_inj_of (hd args)) (cv_inj_of (hd(tl args))))
    else
      let th = try assoc name (!cv_inj) with Failure _ ->
        cv_prove_inj name in
      let _,tvs,_ = assoc name (!cv_types) in
      let th = INST_TYPE (zip args tvs) th in
      let olds = map (fun tv -> mk_var("enc_" ^ cv_sanitize (dest_vartype tv),
                        mk_fun_ty (type_subst (zip args tvs) tv) cv_ty)) tvs in
      let th = INST (zip (map cv_enc_of args) olds) th in
      if args = [] then th
      else MP th (end_itlist CONJ (map cv_inj_of args));;

(* ------------------------------------------------------------------------- *)
(* Translation tables.                                                       *)
(* ------------------------------------------------------------------------- *)

let cv_fun_thms = ref ([] : (string * thm) list);;  (* f |-> enc(f xs) = cv_f .. *)
let cv_code = ref ([] : thm list);;                 (* compute equations         *)
let cv_unfold = ref ([] : (string * thm) list);;    (* 0-ary c |-> |- c = t      *)

let cv_con_clause = ref ([] : (string * thm) list);;
let cv_add_con_clauses ths =
  cv_con_clause :=
    map (fun th -> let l = lhs(concl(SPEC_ALL th)) in
                   (fst(dest_const(fst(strip_comb(rand l)))), SPEC_ALL th)) ths
    @ !cv_con_clause;;
cv_add_con_clauses (CONJUNCTS cv_of_list_DEF @ CONJUNCTS cv_of_option_DEF @
                    CONJUNCTS CV_OF_BOOL_CLAUSES @ [CV_OF_PROD_PAIR]);;

let cv_register_type0 = cv_register_type;;
let cv_register_type tyname =
  let def = cv_register_type0 tyname in
  cv_add_con_clauses (CONJUNCTS def); def;;

let is_hole tm =
  is_comb tm && type_of tm = cv_ty && not (type_of (rand tm) = cv_ty);;

let cv_let_conv tm =
  (* LET (\x. b) a = b[a/x] *)
  (REWR_CONV LET_DEF THENC BETA_CONV) tm;;

let cv_num_ops = CONJUNCTS CV_TR_NUM and cv_bool_ops = CONJUNCTS CV_TR_BOOL;;

let cv_try_rewr ths tm = tryfind (fun th -> PART_MATCH lhs th tm) ths;;

(* encoder variables left free by matching (e.g. the element encoder in    *)
(* LENGTH's theorem) are instantiated with the canonical encoders             *)
let cv_fix_encvars tm th =
  let fvs = subtract (frees (concl th)) (frees tm) in
  let evs = filter (fun v -> let n = fst(dest_var v) in
                     String.length n > 4 && String.sub n 0 4 = "enc_") fvs in
  if evs = [] then th else
  INST (map (fun v -> (cv_enc_of (fst(dest_fun_ty (type_of v))), v)) evs) th;;

let cv_tr_step extra tm =
  let e,t = dest_comb tm in
  if is_cond t then
    let c,(a,b) = dest_cond t in ISPECL [e;c;a;b] CV_TR_COND else
  if is_comb t && is_const (rator t) && fst(dest_const(rator t)) = "LET_END" then
    AP_TERM e (ISPEC (rand t) LET_END_DEF) else
  let h,args = strip_comb t in
  if is_const h && can (assoc (fst(dest_const h))) (!cv_con_clause) then
    PART_MATCH lhs (assoc (fst(dest_const h)) (!cv_con_clause)) tm else
  if e = `cv_of_bool` && is_eq t then
    let x,y = dest_eq t in
    SPECL [x;y] (MATCH_MP (ISPEC (cv_enc_of (type_of x)) CV_TR_EQ)
                          (cv_inj_of (type_of x))) else
  if e = `cv_of_bool` && (try ignore(cv_try_rewr cv_bool_ops tm); true
                          with Failure _ -> false) then
    cv_try_rewr cv_bool_ops tm else
  if e = cexp_num_tm && (try ignore(cv_try_rewr cv_num_ops tm); true
                         with Failure _ -> false) then
    cv_try_rewr cv_num_ops tm else
  if is_const h && (fst(dest_const h) = "FST" || fst(dest_const h) = "SND") && length args = 1 then
    let p = hd args in
    let ty1,ty2 = (match dest_type (type_of p) with
                     (_,[a;b]) -> (a,b) | _ -> failwith "cv_tr: FST/SND") in
    let th = ISPECL [cv_enc_of ty1; cv_enc_of ty2; p]
               (if fst(dest_const h) = "FST" then CV_TR_FST else CV_TR_SND) in
    th else
  try extra tm with Failure _ ->
  if is_const h && can (assoc (fst(dest_const h))) (!cv_fun_thms) then
    let th = tryfind (fun (n,th) -> if n = fst(dest_const h) then PART_MATCH lhs th tm
                                    else failwith "")
                     (!cv_fun_thms) in
    cv_fix_encvars tm th else
  if is_const h && args = [] && can (assoc (fst(dest_const h))) (!cv_unfold) then
    AP_TERM e (assoc (fst(dest_const h)) (!cv_unfold)) else
  failwith ("cv_tr: cannot translate " ^ string_of_term t);;

let rec cv_tr extra tm =
  let e,t = dest_comb tm in
  if is_var t || (e = cexp_num_tm && is_numeral t) then REFL tm
  else if is_let t then cv_tr_let extra tm
  else
    let th = cv_tr_step extra tm in
    TRANS th (cv_walk extra (rand(concl th)))
and cv_walk extra tm =
  if is_hole tm then cv_tr extra tm
  else if is_comb tm then
    let l,r = dest_comb tm in MK_COMB(cv_walk extra l, cv_walk extra r)
  else if is_abs tm then
    let v,b = dest_abs tm in ABS v (cv_walk extra b)
  else REFL tm
and cv_tr_let extra tm =
  let e,t = dest_comb tm in
  let f,a = dest_comb t in
  let x,b = dest_abs (rand f) in
  let ea = cv_enc_of (type_of x) in
  let tha = cv_tr extra (mk_comb(ea,a)) in
  let thb = cv_tr extra (mk_comb(e,b)) in
  let exv = mk_comb(ea,x) in
  let w = variant (frees (concl thb) @ frees(concl tha))
            (mk_var("cv_" ^ cv_sanitize (fst(dest_var x)), cv_ty)) in
  let bw = subst [w,exv] (rand(concl thb)) in
  if vfree_in x bw then failwith "cv_tr_let: let variable used outside encoder" else
  let th1 = AP_TERM e (cv_let_conv t) in
  let th2 = INST [a,x] thb in
  let lamw = mk_abs(w,bw) in
  let th3 = CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM lamw tha) in
  let letc = mk_const("LET",[cv_ty,`:A`; cv_ty,`:B`]) in
  let th4 = cv_let_conv (mk_comb(mk_comb(letc, lamw), rand(concl tha))) in
  TRANS (TRANS (TRANS th1 th2) th3) (SYM th4);;

(* ------------------------------------------------------------------------- *)
(* Pattern compilation into a decision tree.                                 *)
(* ------------------------------------------------------------------------- *)

type cv_dtree =
    Cv_leaf of term list * thm
  | Cv_split of term list * term * (term * term list * cv_dtree) list;;

let cv_fresh_ctr = ref 0;;
let cv_fresh ty =
  cv_fresh_ctr := !cv_fresh_ctr + 1;
  mk_var("cvp" ^ string_of_int (!cv_fresh_ctr), ty);;

(* constructors of a type, instantiated to the type ty, with the cases thm   *)
let cv_type_cons ty =
  if ty = `:num` then ([`0`; `SUC`], num_CASES)
  else if ty = bool_ty then ([`T`; `F`], BOOL_CASES_AX)
  else
    let name,args = dest_type ty in
    if name = "prod" then
      ([inst [hd args,`:A`; hd(tl args),`:B`] `(,):A->B->A#B`],
       INST_TYPE [hd args,`:A`; hd(tl args),`:B`] PAIR_SURJECTIVE)
    else
      let gty,cons,cth = cv_constructors name in
      let tyi = type_match gty ty [] in
      (map (inst tyi) cons, INST_TYPE tyi cth);;

let cv_con_args c =
  let atys = fst(splitlist dest_fun_ty (type_of c)) in
  map cv_fresh atys;;

(* pattern head, args (num numerals other than 0 must be SUC-converted)      *)
let cv_dest_pat p =
  if p = `0` then (`0`, []) else
  let h,args = strip_comb p in (h, args);;

let rec cv_compile nodeargs cols rows =
  match rows with
    [] -> failwith ("cv_translate: incomplete patterns at " ^
                    String.concat " " (map string_of_term nodeargs))
  | (pats,th)::_ when forall is_var pats ->
      let th' = INST (zip cols pats) th in
      Cv_leaf(nodeargs, th')
  | (pats,_)::_ ->
      let j = index true (map (fun p -> not (is_var p)) pats) in
      let y = el j cols in
      let ty = type_of y in
      let cons,_ = cv_type_cons ty in
      let branch c =
        let zs = cv_con_args c in
        let cz = list_mk_comb(c, zs) in
        let nodeargs' = map (subst [cz,y]) nodeargs in
        let cols' = fst(chop_list j cols) @ zs @ tl(snd(chop_list j cols)) in
        let row (pats,th) =
          let p = el j pats in
          let pre = fst(chop_list j pats) and post = tl(snd(chop_list j pats)) in
          if is_var p then [(pre @ zs @ post, INST [cz,p] th)]
          else
            let h,qs = cv_dest_pat p in
            if h = c then [(pre @ qs @ post, th)] else [] in
        (c, zs, cv_compile nodeargs' cols' (flat (map row rows))) in
      Cv_split(nodeargs, y, map branch cons);;

(* convert numeral patterns k > 0 into SUC form in the lhs of a clause       *)
let rec cv_suc_pat_conv tm =
  if is_numeral tm && not (tm = `0`) then
    (num_CONV THENC RAND_CONV cv_suc_pat_conv) tm
  else if is_comb tm then COMB_CONV cv_suc_pat_conv tm
  else REFL tm;;

let cv_prep_clause th =
  let th = SPEC_ALL th in
  let th = CONV_RULE (LAND_CONV (RAND_CONV cv_suc_pat_conv)) th in
  let rec fix th =
    let l = lhs(concl th) in
    let f,args = strip_comb l in
    if exists (fun a -> is_numeral a && not (a = `0`)) args then
      fix (CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV cv_suc_pat_conv)) th)
    else th in
  fix (CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV cv_suc_pat_conv)) (SPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Code generation.                                                          *)
(* ------------------------------------------------------------------------- *)

let rec cv_tuple ts = match ts with
    [t] -> t | t::rest -> mk_cpair t (cv_tuple rest) | [] -> failwith "cv_tuple";;

(* field paths of the arguments of constructor c at cval path p              *)
let cv_field_paths ty c p =
  let m = length (fst(splitlist dest_fun_ty (type_of c))) in
  let rec fields q m = if m = 1 then [q] else mk_cfst q :: fields (mk_csnd q) (m-1) in
  if ty = `:num` then
    (if c = `0` then [] else [list_mk_comb(`Cexp_sub`, [p; mk_cnum 1])])
  else if ty = bool_ty then []
  else if fst(dest_type ty) = "prod" then [mk_cfst p; mk_csnd p]
  else
    let tyname,k,tag,ar,na = assoc (fst(dest_const c)) (!cv_cons) in
    if ar = 0 then []
    else if k = 1 then
      (if ar = 1 && na > 0 then [mk_cfst p] else fields p ar)
    else fields (mk_csnd p) ar;;

(* select among codes indexed 0..k-1 by the cval number at path q            *)
let rec cv_select q lo codes =
  match codes with
    [c] -> c
  | _ -> let n = length codes in
         if n <= 3 then
           mk_cif (mk_ceq q (mk_cnum lo)) (hd codes) (cv_select q (lo+1) (tl codes))
         else
           let h = n / 2 in
           let c1,c2 = chop_list h codes in
           mk_cif (list_mk_comb(cexp_less_tm, [q; mk_cnum (lo+h)]))
                  (cv_select q lo c1) (cv_select q (lo+h) c2);;

let cv_dispatch ty p branch_codes =
  (* branch_codes: (constructor, code) in constructor order *)
  if ty = `:num` then
    (match branch_codes with [(_,c0);(_,c1)] -> mk_cif p c1 c0
     | _ -> failwith "cv_dispatch num")
  else if ty = bool_ty then
    (match branch_codes with [(_,ct);(_,cf)] -> mk_cif p ct cf
     | _ -> failwith "cv_dispatch bool")
  else if fst(dest_type ty) = "prod" then snd(hd branch_codes)
  else
    let info c = assoc (fst(dest_const c)) (!cv_cons) in
    let nulls = filter (fun (c,_) -> let _,_,_,ar,_ = info c in ar = 0) branch_codes
    and nons = filter (fun (c,_) -> let _,_,_,ar,_ = info c in ar > 0) branch_codes in
    let nullcode () = cv_select p 0 (map snd nulls) in
    let noncode () =
      if length nons = 1 then snd(hd nons)
      else cv_select (mk_cfst p) 0 (map snd nons) in
    if nulls = [] then noncode ()
    else if nons = [] then nullcode ()
    else mk_cif (mk_cispair p) (noncode ()) (nullcode ());;

(* replace the holes enc x (x a pattern variable) by their cval paths       *)
let cv_subst_holes pmap code =
  let holes = find_terms (fun t -> is_hole t && is_var (rand t) &&
                                   can (rev_assoc (rand t)) pmap) code in
  let sub = map (fun h -> (rev_assoc (rand h) pmap, h)) holes in
  subst sub code;;

(* the code of a decision tree; tr translates a leaf rhs hole               *)
let rec cv_gen_code tr pmap tree =
  match tree with
    Cv_leaf(_,th) ->
      let r = rhs(concl th) in
      let e = cv_enc_of (type_of r) in
      let code = rand(concl(tr (mk_comb(e, r)))) in
      cv_subst_holes pmap code
  | Cv_split(_,y,branches) ->
      let p = rev_assoc y pmap in
      let ty = type_of y in
      let bc (c,zs,sub) =
        let paths = cv_field_paths ty c p in
        (c, cv_gen_code tr (zip paths zs @ pmap) sub) in
      cv_dispatch ty p (map bc branches);;

(* ------------------------------------------------------------------------- *)
(* Normalisation used to compare the two sides of a leaf in the proofs.     *)
(* ------------------------------------------------------------------------- *)

let CEXP_IF_SUC = prove
 (`!m p q. Cexp_if (Cexp_num (SUC m)) p q = p`, REWRITE_TAC[cexp_if_def]);;
let CEXP_IF_PAIR = prove
 (`!a b p q. Cexp_if (Cexp_pair a b) p q = q`, REWRITE_TAC[cexp_if_def]);;
let CEXP_EQ_NUM = prove
 (`!m n. Cexp_eq (Cexp_num m) (Cexp_num n) = Cexp_num (if m = n then 1 else 0)`,
  REWRITE_TAC[cexp_eq_def; CEXP_NUM_11; ONE]);;
let CEXP_LESS_NUM = prove
 (`!m n. Cexp_less (Cexp_num m) (Cexp_num n) = Cexp_num (if m < n then 1 else 0)`,
  REWRITE_TAC[cexp_less_def; ONE]);;
let CEXP_ISPAIR_CLAUSES = prove
 (`(!a b. Cexp_ispair (Cexp_pair a b) = Cexp_num 1) /\
   (!n. Cexp_ispair (Cexp_num n) = Cexp_num 0)`,
  REWRITE_TAC[cexp_ispair_def; ONE]);;
let CEXP_SUB_SUC1 = prove
 (`!n. Cexp_sub (Cexp_num (SUC n)) (Cexp_num 1) = Cexp_num n`,
  REWRITE_TAC[cexp_sub_def; SUC_SUB1]);;

let cv_norm_thms () =
  !cv_enc_clauses @
  [CV_OF_PROD_PAIR; CV_OF_BOOL_CLAUSES; cexp_fst_def; cexp_snd_def;
   CEXP_ISPAIR_CLAUSES; CEXP_IF_TRUE; CEXP_IF_FALSE; CEXP_IF_SUC; CEXP_IF_PAIR;
   CEXP_EQ_NUM; CEXP_LESS_NUM; CEXP_SUB_SUC1];;

let cv_norm_conv tm =
  let ths = cv_norm_thms () in
  (PURE_REWRITE_CONV ths THENC NUM_REDUCE_CONV THENC
   PURE_REWRITE_CONV (COND_CLAUSES :: ths)) tm;;

(* ------------------------------------------------------------------------- *)
(* Termination: the admissibility walker.                                    *)
(* ------------------------------------------------------------------------- *)

let CV_EXISTS_EQ_NUM = prove
 (`!n. (?m:num. n = m) <=> T`, MESON_TAC[]);;

let CEXP_IF_CONG = prove
 (`!c1 c2 a1 a2 b1 b2.
     c1 = c2 ==> ((?m. c1 = Cexp_num (SUC m)) ==> a1 = a2) ==>
     (~(?m. c1 = Cexp_num (SUC m)) ==> b1 = b2) ==>
     Cexp_if c1 a1 b1 = Cexp_if c2 a2 b2`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  STRUCT_CASES_TAC (SPEC `c2:cval` (cases "cval")) THEN
  REWRITE_TAC[injectivity "cval"; distinctness "cval"; cexp_if_def] THEN
  TRY (STRUCT_CASES_TAC (SPEC `a:num` num_CASES)) THEN
  REWRITE_TAC[cexp_if_def; NOT_SUC; GSYM NOT_SUC; SUC_INJ; CV_EXISTS_EQ_NUM]);;

(* prove  conds ==> cval_sum_size a < cval_sum_size v  (v a variable)       *)
let cv_add_size_facts : tactic = fun (asl,w) ->
  let fs = find_terms (fun t -> is_comb t &&
             (rator t = cexp_fst_tm || rator t = cexp_snd_tm)) w in
  let facts = map (fun t -> if rator t = cexp_fst_tm then SPEC (rand t) CSS_FST_LE
                            else SPEC (rand t) CSS_SND_LE) fs in
  MAP_EVERY MP_TAC facts (asl,w);;

let cv_measure_rw () =
  [cexp_fst_def; cexp_snd_def; CEXP_ISPAIR_CLAUSES; cval_sum_size_def;
   injectivity "cval"; distinctness "cval"; GSYM (distinctness "cval");
   CEXP_EQ_NUM; CEXP_LESS_NUM; cexp_sub_def; NOT_SUC; GSYM NOT_SUC;
   cexp_add_def];;

(* split the cval variables x occurring as Cexp_ispair x (or as the subject *)
(* of a numeric test) in the goal, repeatedly                                *)
let rec cv_split_ispair_tac depth : tactic = fun (asl,w) ->
  if depth = 0 then ALL_TAC (asl,w) else
  let cands = find_terms (fun t -> is_comb t && rator t = cexp_ispair_tm &&
                                   is_var (rand t)) w in
  match cands with
    [] -> ALL_TAC (asl,w)
  | t::_ ->
     (STRUCT_CASES_TAC (SPEC (rand t) (cases "cval")) THEN
      REWRITE_TAC (cv_measure_rw ()) THEN
      cv_split_ispair_tac (depth - 1)) (asl,w);;

let cv_measure_tac v : tactic =
  STRUCT_CASES_TAC (SPEC v (cases "cval")) THEN
  REWRITE_TAC (cv_measure_rw ()) THEN
  cv_split_ispair_tac 4 THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[cval_sum_size_def] THEN
  cv_add_size_facts THEN ARITH_TAC;;

let cv_prove_measure conds a v =
  let w = itlist (curry mk_imp) conds (list_mk_comb(`(<)`, [mk_comb(`cval_sum_size`, a);
                                                 mk_comb(`cval_sum_size`, v)])) in
  let vv = mk_var("cvmv", cv_ty) in
  let w' = subst [vv, v] w in
  let th = prove(mk_forall(vv,w'), GEN_TAC THEN cv_measure_tac vv) in
  let th = SPEC v th in
  rev_itlist (fun c th -> MP th (ASSUME c)) conds th;;

(* walk t[f] proving t[f] = t[g] given the IH assumption ih:                *)
(*    !z. MEASURE m z x ==> f z = g z  , with m = \x. css(sel x)            *)
let rec cv_cong f g ih msel x conds t =
  if not (free_in f t) then REFL t else
  if is_comb t && rator t = f then
    let arg = rand t in
    if free_in f arg then failwith "cv_cong: nested recursion" else
    let ihs = SPEC arg ih in
    let mterm = lhand(concl ihs) in
    (* mterm = MEASURE m arg x; reduce it to css(sel arg) < css(sel x) *)
    let red = (REWRITE_CONV[MEASURE] THENC DEPTH_CONV BETA_CONV THENC
               REWRITE_CONV[FST; SND]) mterm in
    let a = rand(lhand(rand(concl red))) and v = rand(rand(rand(concl red))) in
    let mth = cv_prove_measure conds a v in
    MP ihs (EQ_MP (SYM red) mth)
  else
    let h,args = strip_comb t in
    if h = cexp_if_tm && length args = 3 then
      let c,a,b = (match args with [c;a;b] -> (c,a,b) | _ -> failwith "") in
      let thc = cv_cong f g ih msel x conds c in
      let c1 = lhs(concl thc) in
      let p = mk_exists(`m:num`, mk_eq(c1, mk_comb(cexp_num_tm, `SUC m`))) in
      let np = mk_neg p in
      let tha = DISCH p (cv_cong f g ih msel x (conds @ [p]) a) in
      let thb = DISCH np (cv_cong f g ih msel x (conds @ [np]) b) in
      let th0 = ISPECL [c1; rand(concl thc); a; rand(rand(concl tha));
                        b; rand(rand(concl thb))] CEXP_IF_CONG in
      MP (MP (MP th0 thc) tha) thb
    else if is_comb t then
      let l,r = dest_comb t in
      MK_COMB(cv_cong f g ih msel x conds l, cv_cong f g ih msel x conds r)
    else if is_abs t then
      let v,b = dest_abs t in ABS v (cv_cong f g ih msel x conds b)
    else REFL t;;

(* ------------------------------------------------------------------------- *)
(* Defining cv_f from its code.                                              *)
(* ------------------------------------------------------------------------- *)

let mk_fst p = mk_icomb(`FST:A#B->A`, p)
and mk_snd p = mk_icomb(`SND:A#B->B`, p);;

(* sel_i x for an n-tuple x *)
let rec cv_sels x n =
  if n = 1 then [x] else
  mk_fst x :: cv_sels (mk_snd x) (n-1);;

let rec cv_mk_tuple ts = match ts with
    [t] -> t | t::rest -> mk_pair(t, cv_mk_tuple rest) | [] -> failwith "";;

(* code: E with free cval variables vs and the function variable cvf         *)
(* (possibly absent).  k: measure position.  Returns the compute equation    *)
(* |- cv_f v1 .. vn = E[cv_f/cvf].                                           *)
let cv_define_code name cvf vs code k =
  let n = length vs in
  let fty = type_of cvf in
  if not (free_in cvf code) then
    new_definition (mk_eq(list_mk_comb(mk_var(name,fty), vs), code))
  else
    let tupty = type_of (cv_mk_tuple vs) in
    let x = mk_var("cvx", tupty) in
    let g = mk_var("cvg", mk_fun_ty tupty cv_ty) in
    let lam = list_mk_abs(vs, mk_comb(g, cv_mk_tuple vs)) in
    let e1 = subst [lam, cvf] code in
    let e1 = rand(concl(DEPTH_CONV BETA_CONV e1)) in
    let sels = cv_sels x n in
    let e2 = vsubst (zip sels vs) e1 in
    let hh = mk_abs(g, mk_abs(x, e2)) in
    let msel = el k sels in
    let m = mk_abs(x, mk_comb(`cval_sum_size`, msel)) in
    let r = mk_comb(inst [tupty,`:A`] `MEASURE:(A->num)->A->A->bool`, m) in
    let wfr = INST_TYPE [tupty,`:A`; cv_ty,`:B`] WF_REC in
    let wfr = INST [r, rand(lhand(concl wfr))] wfr in
    let th0 = MP wfr (ISPEC m WF_MEASURE) in
    let th1 = ISPEC hh th0 in
    (* admissibility *)
    let ff = mk_var("cvf1", type_of g) and gg = mk_var("cvg1", type_of g) in
    let z = mk_var("cvz", tupty) in
    let ihtm = mk_forall(z, mk_imp(list_mk_comb(r,[z;x]),
                                   mk_eq(mk_comb(ff,z), mk_comb(gg,z)))) in
    let ih = ASSUME ihtm in
    let bf = (RATOR_CONV BETA_CONV THENC BETA_CONV) (list_mk_comb(hh,[ff;x]))
    and bg = (RATOR_CONV BETA_CONV THENC BETA_CONV) (list_mk_comb(hh,[gg;x])) in
    let ef = rand(concl bf) in
    let cth = cv_cong ff gg ih msel x [] ef in
    let adm = TRANS (TRANS bf cth) (SYM bg) in
    let adm = GEN ff (GEN gg (GEN x (DISCH ihtm adm))) in
    let th2 = MP th1 adm in
    if n = 1 then
      let th3 = new_specification [name] th2 in
      let th4 = SPEC (hd vs) th3 in
      CONV_RULE (RAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)) th4
    else
      let th3 = new_specification [name ^ "_tup"] th2 in
      let ct = mk_const(name ^ "_tup", []) in
      let cdef = new_definition
        (mk_eq(list_mk_comb(mk_var(name,fty), vs), mk_comb(ct, cv_mk_tuple vs))) in
      let th4 = SPEC (cv_mk_tuple vs) th3 in
      let th5 = CONV_RULE (RAND_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV)) th4 in
      let th6 = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV[FST; SND])) th5 in
      let th7 = CONV_RULE (RAND_CONV (PURE_REWRITE_CONV[GSYM cdef])) th6 in
      TRANS (SPEC_ALL cdef) th7;;

(* ------------------------------------------------------------------------- *)
(* The correctness proof.                                                    *)
(* ------------------------------------------------------------------------- *)

(* the subterm of tm at the position of y in the pattern pat               *)
let rec cv_corr pat tm y =
  if pat = y then tm
  else if is_comb pat && is_comb tm then
    (try cv_corr (rator pat) (rator tm) y with Failure _ ->
         cv_corr (rand pat) (rand tm) y)
  else failwith "cv_corr";;

let cv_measure_lt a b =
  prove(mk_comb(mk_comb(`(<)`, mk_comb(`cval_sum_size`, a)),
                mk_comb(`cval_sum_size`, b)),
        REWRITE_TAC (cval_sum_size_def :: CV_OF_PROD_PAIR :: CV_OF_BOOL_CLAUSES ::
                     !cv_enc_clauses) THEN ARITH_TAC);;

(* goal: [css(enc x_k) = n ==>] enc (f args) = cv_f (enc args)               *)
let rec cv_tree_tac f code_eq kopt tree : tactic = fun (asl,w) ->
  let concl_eq = if is_imp w then rand w else w in
  let fapp = rand(lhs concl_eq) in
  match tree with
    Cv_split(nodeargs,y,branches) ->
      let y' = cv_corr (list_mk_comb(f,nodeargs)) fapp y in
      let _,cth = cv_type_cons (type_of y) in
      (STRUCT_CASES_TAC (ISPEC y' cth) THENL
         (map (fun (_,_,sub) -> cv_tree_tac f code_eq kopt sub) branches))
      (asl,w)
  | Cv_leaf(nodeargs,th) ->
      ((match kopt with
         None -> ALL_TAC
       | Some _ -> DISCH_TAC) THEN
      (fun (asl,w) ->
        let enc_u = rator(lhs w) in
        let fapp = rand(lhs w) in
        let cl = PART_MATCH lhs th fapp in
        let lhs_th = AP_TERM enc_u cl in
        let oracle =
          match kopt with
            None -> (fun tm -> failwith "no recursion")
          | Some (k, ih) ->
             let meq = snd(hd asl) in
             (fun tm ->
                let e,t = dest_comb tm in
                let h,ys = strip_comb t in
                if not (h = f) then failwith "not recursive" else
                let yk = el k ys in
                let ek = cv_enc_of (type_of yk) in
                let ms = mk_comb(`cval_sum_size`, mk_comb(ek, yk)) in
                let ih1 = SPEC ms ih in
                let patk = rand(lhand(concl meq)) in
                let lt = cv_measure_lt (mk_comb(ek,yk)) patk in
                let lt = EQ_MP (AP_TERM (rator(concl lt)) meq) lt in
                let ih2 = MP ih1 lt in
                let ih3 = SPECL ys ih2 in
                MP ih3 (REFL ms)) in
        let tr_th = cv_tr oracle (rand(concl lhs_th)) in
        let args = snd(strip_comb fapp) in
        let cvs = snd(strip_comb(lhs(concl code_eq))) in
        let rhs_inst = INST (zip (map (fun a -> mk_comb(cv_enc_of (type_of a), a)) args)
                                 cvs) code_eq in
        let n1 = cv_norm_conv (rand(concl tr_th)) in
        let n2 = cv_norm_conv (rand(concl rhs_inst)) in
        let l = TRANS (TRANS lhs_th tr_th) n1 in
        let r = TRANS rhs_inst n2 in
        if not (aconv (rand(concl l)) (rand(concl r))) then
          (print_string ("\ncv leaf mismatch:\n  " ^ string_of_term (rand(concl l)) ^
                         "\n  " ^ string_of_term (rand(concl r)) ^ "\n");
           failwith "cv_tree_tac: leaf mismatch")
        else ACCEPT_TAC (TRANS l (SYM r)) (asl,w)))
      (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The translator.                                                           *)
(* ------------------------------------------------------------------------- *)

let cv_verbose = ref true;;

let rec cv_clauses th =
  flat (map (fun c -> let c = SPEC_ALL c in
                      if is_conj (concl c) then cv_clauses c else [c])
            (CONJUNCTS th));;

let cv_translate_as cname0 th =
  let cls = map cv_prep_clause (cv_clauses th) in
  let f,args0 = strip_comb (lhs (concl (hd cls))) in
  let fname = fst(dest_const f) in
  let n = length args0 in
  let xs = map (fun a -> cv_fresh (type_of a)) args0 in
  let rows = map (fun th -> (snd(strip_comb(lhs(concl th))), th)) cls in
  let tree = cv_compile xs xs rows in
  let vs = map (fun i -> mk_var("v" ^ string_of_int i, cv_ty)) (1--n) in
  let pmap = zip vs xs in
  let res_ty = type_of (lhs(concl(hd cls))) in
  let enc_u = cv_enc_of res_ty in
  let encx x = mk_comb(cv_enc_of (type_of x), x) in
  let cvfty = itlist (fun _ t -> mk_fun_ty cv_ty t) xs cv_ty in
  let cvf = mk_var("cvf", cvfty) in
  let rec_ass = list_mk_forall(xs, mk_eq(mk_comb(enc_u, list_mk_comb(f, xs)),
                                         list_mk_comb(cvf, map encx xs))) in
  let rec_th = ASSUME rec_ass in
  let oracle tm =
    let e,t = dest_comb tm in
    if fst(strip_comb t) = f then PART_MATCH lhs rec_th tm
    else failwith "not recursive" in
  let code = cv_gen_code (cv_tr oracle) pmap tree in
  let recursive = free_in cvf code in
  let cname = if cname0 = "" then "cv_" ^ fname else cname0 in
  let code_eq, kopt =
    if not recursive then (cv_define_code cname cvf vs code 0, None)
    else
      let rec tryk k =
        if k >= n then failwith ("cv_translate: no measure found for " ^ fname)
        else try (cv_define_code cname cvf vs code k, Some k)
             with Failure s ->
               (if !cv_verbose then
                  print_string ("  [measure on argument " ^ string_of_int k ^
                                " failed: " ^ s ^ "]\n");
                tryk (k+1)) in
      tryk 0 in
  let code_eq = SPEC_ALL code_eq in
  let cvc = fst(strip_comb(lhs(concl code_eq))) in
  let goal_body = mk_eq(mk_comb(enc_u, list_mk_comb(f,xs)),
                        list_mk_comb(cvc, map encx xs)) in
  let corr =
    match kopt with
      None -> prove(list_mk_forall(xs, goal_body),
                    REPEAT GEN_TAC THEN cv_tree_tac f code_eq None tree)
    | Some k ->
        let xk = el k xs in
        let nv = mk_var("cvn", `:num`) in
        let ms = mk_comb(`cval_sum_size`, encx xk) in
        let g = mk_forall(nv, list_mk_forall(xs, mk_imp(mk_eq(ms, nv), goal_body))) in
        let th = prove(g,
          MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
          (fun (asl,w) ->
             cv_tree_tac f code_eq (Some(k, snd(hd asl))) tree (asl,w))) in
        let th1 = SPECL xs (SPEC ms th) in
        GENL xs (MP th1 (REFL ms)) in
  let corr = GEN_ALL corr in
  cv_fun_thms := (fname, corr) :: !cv_fun_thms;
  let cname_of th = fst(dest_const(fst(strip_comb(lhs(concl th))))) in
  cv_code := code_eq :: filter (fun th -> not (cname_of th = cname_of code_eq))
                               (!cv_code);
  if !cv_verbose then
    print_string ("cv_translate: " ^ fname ^ " -> " ^ cname ^
                  (if recursive then " (recursive)" else "") ^ "\n");
  corr;;

let cv_translate th = cv_translate_as "" th;;

(* ------------------------------------------------------------------------- *)
(* Helpers for preparing clauses.                                            *)
(* ------------------------------------------------------------------------- *)

let cv_simp_thms () =
  [NOT_CONS_NIL; GSYM NOT_CONS_NIL; HD; TL; CONS_11; COND_CLAUSES; NOT_SUC;
   GSYM NOT_SUC; SUC_INJ; FST; SND; PAIR_EQ; option_DISTINCT; option_INJ;
   GSYM option_DISTINCT] @
  flat (map (fun (n,_) ->
     (try [injectivity n] with Failure _ -> []) @
     (try [distinctness n; GSYM (distinctness n)] with Failure _ -> []))
     (filter (fun (n,_) -> not (n = "list") && not (n = "option")) (!cv_types)));;

(* case-split argument i of a definition f x1 .. xn = rhs into constructor  *)
(* clauses, simplifying each                                                 *)
let cv_split_def i th =
  let th = SPEC_ALL th in
  let f,args = strip_comb (lhs (concl th)) in
  let x = el i args in
  let cons,_ = cv_type_cons (type_of x) in
  let simp = cv_simp_thms () in
  let clause c =
    let zs = cv_con_args c in
    let th1 = INST [list_mk_comb(c,zs), x] th in
    GEN_ALL (CONV_RULE (RAND_CONV (REWRITE_CONV simp)) th1) in
  end_itlist CONJ (map clause cons);;

(* split argument i in every clause where it is a variable                   *)
let cv_split_clauses i th =
  end_itlist CONJ (map (fun c ->
     let c' = SPEC_ALL c in
     let a = el i (snd(strip_comb(lhs(concl c')))) in
     if is_var a then cv_split_def i c' else c') (CONJUNCTS th));;

(* register a 0-ary constant to be unfolded by its definition |- c = t       *)
let cv_add_unfold th =
  let c = lhs(concl th) in
  cv_unfold := (fst(dest_const c), th) :: !cv_unfold;;

(* ------------------------------------------------------------------------- *)
(* Evaluation of a ground term by Kernel.compute:  |- t = value.             *)
(* ------------------------------------------------------------------------- *)

let rec cv_decode ty v =
  if ty = `:num` then rand v
  else if ty = bool_ty then (if rand v = `0` then `F` else `T`)
  else
    let name,args = dest_type ty in
    if name = "prod" then
      let l,b = dest_comb v in let a = rand l in
      mk_pair(cv_decode (hd args) a, cv_decode (hd(tl args)) b)
    else
      let cons,_ = cv_type_cons ty in
      let info c = assoc (fst(dest_const c)) (!cv_cons) in
      let nulls = filter (fun c -> let _,_,_,ar,_ = info c in ar = 0) cons
      and nons = filter (fun c -> let _,_,_,ar,_ = info c in ar > 0) cons in
      let rec fields q m =
        if m = 1 then [q] else
        let l,r = dest_comb q in rand l :: fields r (m-1) in
      let build c q =
        let atys = fst(splitlist dest_fun_ty (type_of c)) in
        let _,k,_,ar,na = info c in
        let qs = if k = 1 && ar = 1 && na > 0 then [rand(rator q)]
                 else fields q ar in
        list_mk_comb(c, map2 cv_decode atys qs) in
      if is_comb v && rator v = cexp_num_tm then
        el (dest_small_numeral (rand v)) nulls
      else if length nons = 1 then build (hd nons) v
      else
        let l,q = dest_comb v in
        let tag = dest_small_numeral (rand (rand l)) in
        build (el tag nons) q;;

let cv_eval tm =
  let ty = type_of tm in
  let e = cv_enc_of ty in
  let th1 = cv_tr (fun _ -> failwith "") (mk_comb(e, tm)) in
  let th2 = compute (!cv_code) (rand(concl th1)) in
  let v = rand(concl th2) in
  let x = cv_decode ty v in
  let th3 = PURE_REWRITE_CONV (!cv_enc_clauses @ [CV_OF_PROD_PAIR; CV_OF_BOOL_CLAUSES])
              (mk_comb(e, x)) in
  let inj = cv_inj_of ty in
  EQ_MP (SPECL [tm; x] inj) (TRANS (TRANS th1 th2) (SYM th3));;
