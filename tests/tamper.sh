#!/bin/bash
# Tampering tests for gate.sh (adapted from the EulerIneq / Brocard developments' tests/tamper.sh).
# Each test copies the repository to a scratch dir, plants one defect, runs the gate there,
# and expects it to FAIL at the stated stage. The real repository is never modified.
# Tests run one at a time (Lean builds are memory-heavy).
# Defects are planted in FermatNapoleon/Main.lean unless stated otherwise.
# Usage: bash tests/tamper.sh [tests...]
#   (default: sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt)
# falsehyp drops the angle hypothesis `(hA : ∠ B A C < 2π/3)` from `napoleon_fermat` (H4.2 (iii));
# without it the common point of the lines need not see the sides under 2π/3 (the weight y_A can be
# negative), and the proof uses `hA`, so the gate must fail at the build stage.
# falsehyp2 drops `(hFB : F ∈ line[ℝ, B, B'])` from `napoleon_fermat` (then `F` is an arbitrary
# point of `AA'`), so the gate must again fail at the build stage.
# falsehyp3 drops `(hAB : A ≠ B)` from `ptolemy_eq_iff` in FermatNapoleon/Ptolemy.lean (H4.1). The
# statement becomes false: for A = B and C, D not collinear with A, `AC·AD = 0·CD + AC·AD` holds but
# neither alternative on the right does (no point is strictly between A and A). The gate must fail
# at the build stage.
# falsestmt changes the line angle of H4.4 from `π / 3` to the false `π / 4`, so the gate must fail
# at the build stage.
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/fermatnapoleon_tamper_XXXXXX")"
C=FermatNapoleon/Main.lean
K=FermatNapoleon/Ptolemy.lean
EL='end FermatNapoleon'

ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; O=ENVIRON["_O"]; if(!done){ off=0; if(A!="" && !st){ q=index($0,A); if(q>0){ st=1; off=q-1 } } if(A=="" || st){ p=index(substr($0,off+1),O); if(p>0){ p+=off; $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(O)); done=1 } } } print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{FermatNapoleon,FermatNapoleon.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'FermatNapoleon.napoleon' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    wrap)     ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="FermatNapoleon.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="FermatNapoleon.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    falsehyp) subst_lit "$d/$C" '    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)' '' 'theorem napoleon_fermat' || return 1
              ! grep -q '(hA : ∠' "$d/$C" || return 1 ;;
    falsehyp2) subst_lit "$d/$C" '    (hFB : F ∈ line[ℝ, t.points 1, napoleonApex o t 1]) :' '    :' 'theorem napoleon_fermat' || return 1
               ! grep -q '(hFB : ' "$d/$C" || return 1 ;;
    falsehyp3) subst_lit "$d/$K" '{A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C)' '{A B C D : P} (hAC : A ≠ C)' 'theorem ptolemy_eq_iff' || return 1
               grep 'theorem ptolemy_eq_iff' "$d/$K" | grep -q '{A B C D : P} (hAC : A ≠ C)' || return 1 ;;
    falsestmt) subst_lit "$d/$C" '(t.points 1 -ᵥ napoleonApex o t 1) = π / 3 := by' '(t.points 1 -ᵥ napoleonApex o t 1) = π / 4 := by' 'theorem napoleon_angle' || return 1
               grep -q 'napoleonApex o t 1) = π / 4 := by' "$d/$C" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp|falsehyp2|falsehyp3|falsestmt) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro wrap falsehyp falsehyp2 falsehyp3 falsestmt}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
