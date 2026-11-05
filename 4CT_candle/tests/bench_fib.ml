new_constant("cfib", `:cval->cval`);;
let fib_ax = new_axiom
 `!n. cfib n = Cexp_if (Cexp_less n (Cexp_num 2)) n
     (Cexp_add (cfib (Cexp_sub n (Cexp_num 1)))
               (cfib (Cexp_sub n (Cexp_num 2))))`;;
let fib_eq = SPEC_ALL fib_ax;;
