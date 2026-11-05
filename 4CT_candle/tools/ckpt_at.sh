#!/bin/bash
# ckpt_at.sh PORT PATTERN LOG NAME: when PATTERN appears in LOG, checkpoint the DMTCP computation
# on coordinator PORT and move the images to /project/work/ckpt/NAME
port=$1; pat=$2; log=$3; name=$4
until grep -aq "$pat" "$log"; do sleep 2; done
echo "trigger $(date +%T)"
/project/opt/dmtcp/bin/dmtcp_command --coord-port $port --bcheckpoint
rc=$?
d=/project/work/ckpt/$name; rm -rf $d; mkdir -p $d
mv /project/work/ckpt/sess_$port/ckpt_*.dmtcp $d/ && echo "ckpt $name rc=$rc $(date +%T) $(du -sh $d | cut -f1)"
