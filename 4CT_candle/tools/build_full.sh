#!/bin/bash
# Clean end-to-end build following 4CT_candle/make.ml, from base12 (hol.ml + prelude, 12 GB heap)
# with DMTCP checkpoints at the stage boundaries and every 100 Part 2 configurations.
cd /project/work
python3 tools/cdriver.py --restore base12 --log logs/full.log \
  4CT_candle/make_mv.ml ckpt:full_mv \
  4CT_candle/make_part1.ml ckpt:full_p1 \
  4CT_candle/part2_run_cv.ml \
  'cmd:p2_cv_run 1 100' ckpt:full_p2a 'cmd:p2_cv_run 101 200' ckpt:full_p2b \
  'cmd:p2_cv_run 201 300' ckpt:full_p2a 'cmd:p2_cv_run 301 400' ckpt:full_p2b \
  'cmd:p2_cv_run 401 500' ckpt:full_p2a 'cmd:p2_cv_run 501 600' ckpt:full_p2b \
  4CT_candle/make_part2.ml ckpt:full_done > logs/full.out 2>&1
