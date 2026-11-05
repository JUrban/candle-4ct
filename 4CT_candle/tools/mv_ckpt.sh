#!/bin/bash
# mv_ckpt.sh PORT NAME: wait for the DMTCP images in sess_PORT to be complete, move them to ckpt/NAME
cd /project/work/ckpt
s=sess_$1
until [ -z "$(ls $s/*.temp 2>/dev/null)" ] && ls $s/ckpt_cake_*.dmtcp >/dev/null 2>&1; do sleep 5; done
rm -rf $2; mkdir $2; mv $s/ckpt_*.dmtcp $2/ && echo "moved to $2: $(du -sh $2 | cut -f1) $(date +%T)"
