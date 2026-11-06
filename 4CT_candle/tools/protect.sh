#!/bin/bash
# protect.sh MAINPID: find the newest other DMTCP cake process (the clean build), make it the OOM
# killer's first choice, and kill it if MemAvailable < 3 GB; re-attaches across its restarts/restores
main=$1
while true; do
  for p in $(ps -u mptp -o pid=,comm= | awk '$2 ~ /cake|mtcp_restart/ {print $1}'); do
    [ "$p" = "$main" ] && continue
    cur=$(cat /proc/$p/oom_score_adj 2>/dev/null)
    [ "$cur" != "1000" ] && echo 1000 > /proc/$p/oom_score_adj 2>/dev/null && echo "oom_adj 1000 on $p $(date +%T)"
    av=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
    if [ "$av" -lt 3 ]; then echo "LOW MEM ${av}G: killing clean build $p $(date +%T)"; kill $p; fi
  done
  pgrep -f "[c]driver.py --restore base12" >/dev/null || { echo "clean build driver gone $(date +%T)"; break; }
  sleep 5
done
