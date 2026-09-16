#!/usr/bin/env bash
# Same fixed-compute comparison as width_sweep.sh, but with 4x the budget.
# If width is worthless the ordering stays put; if there is a compute-optimal
# width that moves right with budget, d=128 should close on (or pass) d=64.
set -u
BIN=./.lake/build/bin/tinystories.exe
mkdir -p sweep
run () {
  d=$1; ff=$2; st=$3
  echo "=== 4x budget: d_model=$d steps=$st ==="
  $BIN train --data data --ckpt "sweep/x$d.bin" \
      --dim "$d" --ff "$ff" --layers 4 --heads 4 --ctx 64 \
      --steps "$st" --batch 8 --lr 0.0008 --warmup 60 \
      --logevery 200 --evalevery "$st" --ckptevery "$st" --seed 1234 \
      > "sweep/x$d.log" 2>&1
  echo "    final: $(grep '\[eval\]' "sweep/x$d.log" | tail -1)"
}
run 64  256 3400
run 128 512 1200
echo "CROSSOVER COMPLETE"
