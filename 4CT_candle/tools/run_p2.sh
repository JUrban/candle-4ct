#!/bin/bash
# Part 2 + final theorems from the Part 1 checkpoint (default mv_p1), checkpointing every 100 configs
cd /project/work
ck=${1:-mv_p1}
python3 tools/cdriver.py --restore $ck --log logs/p2fin.log \
  4CT_candle/part2_run_cv.ml \
  'cmd:p2_cv_run 1 100' ckpt:fin_a 'cmd:p2_cv_run 101 200' ckpt:fin_b \
  'cmd:p2_cv_run 201 300' ckpt:fin_a 'cmd:p2_cv_run 301 400' ckpt:fin_b \
  'cmd:p2_cv_run 401 500' ckpt:fin_a 'cmd:p2_cv_run 501 600' ckpt:fin_b \
  4CT_candle/make_part2.ml ckpt:fin_done > logs/p2fin.out 2>&1
