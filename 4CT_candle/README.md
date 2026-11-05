# 4CT_candle: the Four Colour Theorem in Candle

The HOL Light proof of the Four Colour Theorem (`4CT/`, Gonthier's proof as
ported to HOL Light) built in Candle, with HOL Light's proof-producing
evaluation (eval_compile, the CBV engine) replaced by Candle's verified
`Kernel.compute`, the analogue of HOL4's `cv_compute`.

The result is the theorem in all six forms of `4CT/make.ml`, with no
hypotheses and no axioms beyond `INFINITY_AX`, `SELECT_AX` and `ETA_AX`
(`check_axioms ()`):

    FOUR_COLOR               (hypermaps)
    FOUR_COLOR_PLANAR_GRAPH  FOUR_COLOR_KURATOWSKI  FOUR_COLOR_WAGNER
    FOUR_COLOR_MAP           FOUR_COLOR_MAP_EXPLICIT

## Running

From the Candle root, in Candle (`./candle.sh`, then `#use "hol.ml";;`),
with a heap of at least 12 GB (`CML_HEAP_SIZE=12000`):

    loads "4CT_candle/make.ml";;

Stages: `prelude.ml`; `make_mv.ml` (Multivariate and
`Autoformalization/planar_graph.ml`, about 1 h 10 min); `make_part1.ml` (the
4CT mathematics, sections A-G, P, M, with the computations of Part 1, about
1 h); `make_part2.ml` (the 633 reducibility checks, about 5 h, and the final
theorems).  `tools/cdriver.py` runs the same stages with DMTCP checkpoints
in between (`tools/run_p2.sh` for Part 2 from a Part 1 checkpoint).

## Files

| file | contents |
|------|----------|
| `prelude.ml` | removes the `Cexp_*` overloads of `+ - *`; `for_loop` |
| `cvtrans.ml` | the cv translator: encoders, `cv_tr`, pattern compilation, `WF_REC` definitions of the cv code with automatic measures, correctness by well-founded induction, mutually recursive clusters, `cv_eval` |
| `cvint.ml` | integers as pairs of numbers, code for `& -- + - * < <=` |
| `kempe_cv.ml` | colours, colour and chromogram trees, restrictions, cpcolor, initial trees, Kempe closure |
| `birkhoff_cv.ml` | the four Birkhoff checks (loaded by `4CT/birkhoff.ml`) |
| `part2_cv.ml` | the contract side; `SIZED_CHECK_SOUND` |
| `part2_run_cv.ml` | `check_reducible cfNNN` for each configuration |
| `unavoid_cv.ml` | quiz tree, redpart, discharge rules and forks, dbound checks, hubcaps |
| `present_cv.ml`, `presentations_cv.ml` | the presentation interpreter; exclude5 .. exclude11 |
| `make*.ml` | the build |
| `REPORT.md` | report, timings |

Changes to the shared HOL Light sources (all small, for Candle's OCaml
dialect or to load the files above): `candle/compute.ml` (`Cexp_if` on
pairs, as in current CakeML), `4CT/geometry.ml` (constructor record, arrays,
loops), string continuations in several `4CT/*.ml` files and
`Autoformalization/planar_graph.ml`, `Printf` in `4CT/birkhoff.ml` and
`4CT/presentations_data.ml`, `4CT/birkhoff.ml` and `4CT/unavoidability.ml`
loading the Candle computation files.
