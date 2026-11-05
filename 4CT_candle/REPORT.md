# Four Colour Theorem on Candle — interim report

Branch `candle-4ct` of the Candle repository (on Candle master, CakeML
regression artefact 3660, i.e. current CakeML master).

## Goal

Port the HOL Light 4CT development (`4CT/`, already in Candle master since
the merge of HOL Light 31fe213) to Candle, replacing HOL Light's
proof-producing evaluators (eval_compile, the CBV engine `compute_fast.ml`)
by Candle's verified compute primitive `Kernel.compute` (the analogue of
HOL4's `cv_compute`), and prove all forms of the theorem (hypermaps, planar
graphs, plane maps) with no extra axioms.

## Infrastructure

* `4CT_candle/tools/cdriver.py`: pexpect driver for Candle with DMTCP
  checkpoint/restore (`--restore CK`, items `ckpt:NAME`).  DMTCP (built from
  source) checkpoints a Candle session in 5-80 s; restore takes 5-40 s.
* `candle/compute.ml` fix: CakeML commit 1af98e502 changed `Cexp_if` on
  pairs to take the else branch; Candle master's `cexp_if_def` was stale, so
  `Kernel.compute` rejected its initialisation theorems.  Fixed on the branch.
* `4CT_candle/prelude.ml`: removes the `Cexp_*` overloads of `+ - *` that
  break ordinary arithmetic parsing in 4CT; `for_loop`.

## Candle compatibility of the 4CT mathematics

Sections A-G (all mathematics files except the evaluation files) load in
Candle with small source changes: the record type and arrays of the
CFACE_TAC procedure in `geometry.ml` (constructor record with refs,
`Array.get/set`, `for_loop`), string continuations, `Printf`.  Rough Candle
load times (4 GB heap): sections A-E 5 min, part.ml 5 min, the rest about
2 min.  Multivariate up to `moretop.ml` loads in 42 min (planar_graph.ml in
progress).

## The cv translator (`4CT_candle/cvtrans.ml`)

A HOL Light/Candle analogue of HOL4's `cv_transLib`:

* encoders `cv_of_T` for registered datatypes (nullary constructors as
  numbers, others as tagged pairs), `cv_of_list`, `cv_of_prod`, `cv_of_bool`,
  numbers as `Cexp_num`, injectivity proved automatically;
* `cv_tr`: pushes an encoder into a term, producing compute-expression code
  and its correctness proof at once (COND, LET, constructors, arithmetic,
  boolean operators, equality, FST/SND, translated functions);
* pattern compilation of the defining clauses into a dispatch tree;
* `cv_f` defined by `WF_REC` with measure `cval_sum_size` of an argument
  (found automatically; admissibility by a congruence walker with path
  conditions), so the compute equation holds for all cvals;
* correctness `enc (f x) = cv_f (enc x)` by well-founded induction on the
  measure, following the dispatch tree;
* `cv_eval t`: `|- t = value` via `Kernel.compute`, with the value decoded.

## Translated so far

* `kempe_cv.ml`: colours, traces, colour trees, chromogram trees, the
  restrictions (first-order forms of part2_eval.ml), cpcolor (colour-map
  arguments defunctionalised to edge permutations), initial trees
  (`ctree_add_dyck` via `gen_dyck`), the Kempe closure (higher-order
  recursion made first-order).
* `birkhoff_cv.ml`: the four Birkhoff checks of birkhoff.ml proved by
  `Kernel.compute` (first-order `bc2` for `Birkhoff_check2`), in about 20 s
  in total.
* `part2_cv.ml`: the contract side; partial HD/TL/EL handled by list
  patterns or by total versions proved equal under side conditions that are
  computed together with the check; `SIZED_CHECK_SOUND`:
  `sized_check (cprsize (cfprog cf)) cf ==> check_reducible cf`.
* `part2_run_cv.ml`: `check_reducible cfNNN` per configuration.

## Status of Part 2

All 633 configurations are being checked (6 parallel timing workers from
a checkpoint); the first 140 all passed, at 1-26 s per configuration.

## Remaining

* unavoidability computations (quiz tree, discharge bounds, the 14,421
  presentation steps) by cv instead of CBV (int support in `cvint.ml`);
* Multivariate + planar_graph.ml + sections P, M in Candle;
* the final single-process build of all theorems and `check_axioms()`.
