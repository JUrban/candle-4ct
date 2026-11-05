# Four Colour Theorem on Candle — interim report

Branch `candle-4ct` of the Candle repository (on Candle master, CakeML
regression artefact 3660, i.e. current CakeML master).

## Goal

Port the HOL Light 4CT development (`4CT/`, already in Candle master since
the merge of HOL Light 31fe213) to Candle, replacing HOL Light's
proof-producing evaluators (eval_compile, the CBV engine `compute_fast.ml`)
by Candle's verified compute primitive `Kernel.compute` (the analogue of
HOL4's `cv_compute`), and prove all forms of the theorem (hypermaps, planar
graphs, plane maps) with no hypotheses and no extra axioms
(`check_axioms ()`).

## How to build

From the Candle root, after `hol.ml`:

    loads "4CT_candle/make.ml";;

which is `prelude.ml`, `make_mv.ml` (Multivariate + planar_graph.ml),
`make_part1.ml` (4CT sections A-G, P, M with the Kernel.compute files) and
`make_part2.ml` (the 633 reducibility checks, `REDUCIBILITY`, the six
theorems, `check_axioms ()`).  The development runs used DMTCP checkpoints
between these stages (`4CT_candle/tools/cdriver.py`).

## Infrastructure

* `4CT_candle/tools/cdriver.py`: pexpect driver for Candle with DMTCP
  checkpoint/restore (`--restore CK`, items `ckpt:NAME`); `crepl.py`: a
  persistent Candle REPL behind a socket.  DMTCP (built from source)
  checkpoints a Candle session in 5-110 s; restore takes 5-110 s.
* `candle/compute.ml` fix: CakeML commit 1af98e502 changed `Cexp_if` on
  pairs to take the else branch; Candle master's `cexp_if_def` was stale, so
  `Kernel.compute` rejected its initialisation theorems.  Fixed on the branch.
* `4CT_candle/prelude.ml`: removes the `Cexp_*` overloads of `+ - *` that
  break ordinary arithmetic parsing in 4CT; `for_loop`.

## Candle compatibility of the HOL Light sources

All mathematics files load in Candle with small source changes: the record
type and arrays of the CFACE_TAC procedure in `geometry.ml` (constructor
record with refs, `Array.get/set`, `for_loop`), string continuations
(`4CT/*.ml`, `Autoformalization/planar_graph.ml`), `Printf`.  The
evaluation files are replaced (see below): `birkhoff.ml` loads
`birkhoff_cv.ml` instead of its CBV block, `unavoidability.ml` loads
`unavoid_cv.ml` and `presentations_cv.ml` instead of `redpart_eval.ml` and
`presentations.ml`.  Rough load times (Candle, shared machine): hol.ml
110 s; Multivariate to moretop.ml 40 min, cauchy.ml 4 min, planar_graph.ml
about 25 min; 4CT sections A-E 5 min, part.ml 5 min, the rest about 2 min.

## The cv translator (`4CT_candle/cvtrans.ml`, `cvint.ml`)

A HOL Light/Candle analogue of HOL4's `cv_transLib`:

* encoders `cv_of_T` for registered datatypes (nullary constructors as
  numbers, others as tagged pairs), `cv_of_list`, `cv_of_prod`, `cv_of_bool`,
  numbers as `Cexp_num`, integers as pairs of numbers (`cvint.ml`:
  `cv_of_int i = (int_pos i, int_negp i)`, with code for `& -- + - * < <=`);
  injectivity proved automatically;
* `cv_tr`: pushes an encoder into a term, producing compute-expression code
  and its correctness proof at once (COND, LET, constructors, arithmetic,
  boolean operators, equality, FST/SND, translated functions);
* pattern compilation of the defining clauses into a dispatch tree;
* `cv_f` defined by `WF_REC` with measure `cval_sum_size` of an argument
  (found automatically; admissibility by a congruence walker with path
  conditions), so the compute equation holds for all cvals;
* correctness `enc (f x) = cv_f (enc x)` by well-founded induction on the
  measure, following the dispatch tree;
* clusters of mutually recursive functions (`cv_translate_cluster`) with
  lexicographic measures (`LEX3`), for the redpart family;
* `cv_eval t`: `|- t = value` via `Kernel.compute`, with the value decoded.

Partial functions (HD, TL, EL) are handled by splitting the clauses on the
list argument or by total versions proved equal under side conditions that
are computed together with the check; semantic notions (`cprsize`) by
sized variants with the size computed beforehand.

## The computations

* `kempe_cv.ml`: colours, traces, colour trees, chromogram trees, the
  restrictions, cpcolor (colour-map arguments defunctionalised to edge
  permutations), initial trees, the Kempe closure.
* `birkhoff_cv.ml`: the four Birkhoff checks (about 20 s).
* `part2_cv.ml`, `part2_run_cv.ml`: the contract side and
  `SIZED_CHECK_SOUND: sized_check (cprsize (cfprog cf)) cf ==>
  check_reducible cf`; `|- check_reducible cfNNN` for each configuration.
  All 633 pass; 17,852 s of CPU in total (1-128 s per configuration,
  measured with 6 parallel workers on a shared machine).  HOL Light's
  sequential native Part 2 takes about 8 h 45 min.
* `unavoid_cv.ml`: the quiz tree (`THE_QUIZ_TREE_CV`, computed in 15 s,
  then used as a value), redpart (a cluster of 19 mutually recursive
  functions), the discharge rules and forks, `THE_DBOUND1_CHECK` (4.5 s),
  check_dbound2, check_2dbound2, hubcap_cover and hubcap_fit with the
  reducibility predicate fixed to `redpart the_quiz_tree`.
* `present_cv.ml`: the interpreter of the 14,421 presentation steps
  (exclude5..exclude11).  Pcase steps evaluate their ground
  `good_split`/`split_part` subterms by `cv_eval`; the Reducible, Hubcap and
  Similar side conditions are assumed while the script runs, then proved in
  batches of 100 (one Kernel.compute run per batch) and discharged by
  `PROVE_HYP`.  exclude5 5 s, exclude6 62 s, exclude7 (5,299 steps)
  about 10 min.

## Status

* Part 1 complete in Candle (from the Multivariate + planar_graph.ml
  checkpoint): sections A-G, P and M in 3,590 s, including the seven
  presentation lemmas (2,105 s), the quiz tree, the discharge bounds and the
  Birkhoff checks; every theorem `FOUR_COLOR_*_OF_REDUCIBILITY` and
  `FOUR_COLOR_HYPERMAP : reducibility ==> ...` is proved.
* Part 2 (the 633 checks, all already validated separately, about 5 h of
  Kernel.compute, on par with HOL4's cv_compute: 5 h 33 min in the
  hol4-four-colour benchmarks) running in the same process lineage, then
  REDUCIBILITY, the six theorems and `check_axioms ()`.
* Profile: for cf110, Kernel.compute takes 93.7 s of about 96 s; the
  translation and the proof wrappers are negligible.
