#!/bin/sh
# Checks the relational-biology Lean laws the way the DELPHI law registry does:
#   1. the library builds;
#   2. no `sorry`, and every theorem and definition uses only Lean's standard axioms
#      (propext, Classical.choice, Quot.sound);
#   3. every file in broken/ fails to compile, with the error named on its first
#      line ('-- expect: ...'), so a typo or a missing import cannot pass as a failure.
set -eu
cd "$(dirname "$0")"

lake build >/dev/null
echo "build: ok"

if grep -rn --include='*.lean' -w 'sorry' RelationalLaws; then
  echo "FAIL: sorry found"; exit 1
fi

mkdir -p .lake && AX=.lake/axioms.lean
{
  echo 'import RelationalLaws'
  # every theorem and definition in every module, qualified by the module's namespace
  for f in RelationalLaws/*.lean; do
    ns=$(sed -n 's/^namespace //p' "$f" | head -1)
    sed -n -E 's/^(theorem|def) ([^ ({:]+).*/\2/p' "$f" | while read -r t; do
      echo "#print axioms $ns.$t"
    done
  done
} > "$AX"
OUT=$(lake env lean "$AX")
rm -f "$AX"
echo "$OUT" | sed 's/^/  /'
BAD=$(echo "$OUT" | grep -o '\[.*\]' | tr -d '[]' | tr ',' '\n' | tr -d ' ' \
  | grep -v -x -e propext -e Classical.choice -e Quot.sound || true)
if [ -n "$BAD" ]; then echo "FAIL: non-standard axioms: $BAD"; exit 1; fi
echo "axioms: standard only"

for f in broken/*.lean; do
  # each broken file names, on its first line, the error it must fail with
  expect=$(sed -n '1s/^-- expect: //p' "$f")
  if [ -z "$expect" ]; then
    echo "FAIL: $f has no '-- expect:' first line"; exit 1
  fi
  if ERR=$(lake env lean "$f" 2>&1); then
    echo "FAIL: $f compiled"; exit 1
  fi
  if ! echo "$ERR" | grep -q -F "$expect"; then
    echo "FAIL: $f fails, but not with the expected error ($expect):"; echo "$ERR"; exit 1
  fi
  echo "broken: $f fails as required ($expect)"
done
echo "all checks passed"
