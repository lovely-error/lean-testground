#!/usr/bin/env bash
# Does making the residual stream wider "trivially" improve the model?
#
# Every run below gets the SAME compute budget: steps are chosen inversely
# proportional to parameter count, so params x steps is constant. That is the
# comparison that matters -- comparing at equal *steps* would just be measuring
# "the bigger model also got more arithmetic", which answers nothing.
#
# Everything else is held fixed: same corpus, same 4 layers, same 4 heads, same
# dFF/d ratio, same learning rate, same seed, same context.
set -u
BIN=./.lake/build/bin/tinystories.exe
mkdir -p sweep

run () {   # $1 = d_model, $2 = dFF, $3 = steps
  d=$1; ff=$2; st=$3
  echo "=== d_model=$d  dFF=$ff  steps=$st ==="
  $BIN train --data data --ckpt "sweep/w$d.bin" \
      --dim "$d" --ff "$ff" --layers 4 --heads 4 --ctx 64 \
      --steps "$st" --batch 8 --lr 0.0008 --warmup 40 \
      --logevery 50 --evalevery "$st" --ckptevery "$st" --seed 1234 \
      > "sweep/w$d.log" 2>&1
  echo "    final: $(grep '\[eval\]' "sweep/w$d.log" | tail -1)"
}

run 64   256  850
run 128  512  300
run 192  768  150
run 256 1024   90
echo "SWEEP COMPLETE"
