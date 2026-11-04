#!/bin/sh
# Checks the relational-biology Lean laws the way the DELPHI law registry does:
#   1. the library builds;
#   2. no `sorry` and only Lean's standard axioms (propext, Classical.choice, Quot.sound);
#   3. every file in broken/ fails to compile, and fails on a proof error,
#      not on a missing name or a syntax slip.
set -eu
cd "$(dirname "$0")"

lake build >/dev/null
echo "build: ok"

if grep -rn --include='*.lean' -w 'sorry' RelationalLaws; then
  echo "FAIL: sorry found"; exit 1
fi

AX=$(mktemp -t axioms).lean
{
  echo 'import RelationalLaws'
  for t in replicates_iff_evalInjective not_replicates_full replicates_constant repair_is_metabolism_up; do
    echo "#print axioms RelationalLaws.Replication.$t"
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
  if ERR=$(lake env lean "$f" 2>&1); then
    echo "FAIL: $f compiled"; exit 1
  fi
  if echo "$ERR" | grep -q -E 'unknown (identifier|constant)|unexpected token'; then
    echo "FAIL: $f fails for the wrong reason:"; echo "$ERR"; exit 1
  fi
  echo "broken: $f fails as required ($(echo "$ERR" | grep -m1 error | sed 's/.*error: //'))"
done
echo "all checks passed"
