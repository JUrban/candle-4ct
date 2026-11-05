#!/bin/bash
# wait for the Part 1 cdriver (pid $1) to end; if it checkpointed mv_p1, clean up and start Part 2
cd /project/work
while kill -0 $1 2>/dev/null; do sleep 10; done
if grep -aq "^CKPT /project/work/ckpt/mv_p1" logs/p1.out; then
  sleep 5; kill $2 2>/dev/null; sleep 3; kill -9 $2 2>/dev/null
  echo "Part 1 OK, starting Part 2 $(date +%T)"
  tools/run_p2.sh mv_p1
  echo "Part 2 driver ended $(date +%T)"; tail -5 logs/p2fin.out
else
  echo "Part 1 did not checkpoint mv_p1 $(date +%T)"; grep -a "^FAIL" logs/p1.out | cut -c1-300
fi
