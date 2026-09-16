#!/usr/bin/env bash
# Does a contrast-derived control vector steer Gemma 4's topic?
#
# Notes on the two non-obvious flags:
#   -no-cnv                 llama-completion auto-enables conversation mode when
#                           the model ships a chat template, which would answer
#                           the prompt as a chat turn instead of continuing it.
#   FNAME:SCALE relative    the arg parser splits on the FIRST colon, so an
#                           absolute Windows path (C:\...) is unparseable. The
#                           vector is copied next to this script and referenced
#                           relatively.
#
# Identical prompt, greedy decoding, identical settings across runs. The ONLY
# variable is control-vector strength.
set -u
cd "$(dirname "$0")/.." || exit 1
SP="C:/Users/WRETCH~1/AppData/Local/Temp/claude/E--Code-lean-testground/f2ae5179-4665-4cb1-9583-70ed1b46151e/scratchpad"
BIN="$SP/llama.cpp/build/bin/llama-completion.exe"
MDL="E:/lms/lmstudio-community/gemma-4-E4B-it-QAT-GGUF/gemma-4-E4B-it-QAT-Q4_0.gguf"
cp -f "$SP/elephant_cv.gguf" ./elephant_cv.gguf
OUT="steer_results.txt"
PROMPT="Once upon a time there was"

: > "$OUT"
for scale in 0 1.0 2.0 3.0; do
  echo "===== scale = $scale =====" >> "$OUT"
  if [ "$scale" = "0" ]; then
    "$BIN" -m "$MDL" -p "$PROMPT" -n 100 --temp 0 -no-cnv -t 6 -c 512 --no-warmup \
      < /dev/null > "$SP/run_$scale.raw" 2>"$SP/run_$scale.err"
  else
    "$BIN" -m "$MDL" -p "$PROMPT" -n 100 --temp 0 -no-cnv -t 6 -c 512 --no-warmup \
      --control-vector-scaled "elephant_cv.gguf:$scale" \
      < /dev/null > "$SP/run_$scale.raw" 2>"$SP/run_$scale.err"
  fi
  rc=$?
  tr -d '\r' < "$SP/run_$scale.raw" >> "$OUT"
  printf '\n\n' >> "$OUT"
  echo "done scale=$scale rc=$rc bytes=$(wc -c < "$SP/run_$scale.raw")"
done
echo "STEER_TEST_COMPLETE"
