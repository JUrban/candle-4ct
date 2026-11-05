#!/bin/bash
# kill the PM test's cake process if MemAvailable < 3 GB (protects the main run); exits when the test ends
sleep 20
pid=""; while [ -z "$pid" ]; do pid=$(ps -eo pid,comm | grep "DMTCP:cake" | awk '$1 != 16368 {print $1}' | head -1); sleep 3; done
echo "watching $pid"
while kill -0 $pid 2>/dev/null; do
  av=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)
  if [ $av -lt 3 ]; then echo "LOW MEM ${av}G: killing $pid $(date +%T)"; kill $pid; break; fi
  sleep 5
done
echo "memwatch end $(date +%T)"
