#!/bin/bash
# Gate for the FermatNapoleon Lean formalisation (Ptolemy equality, Fermat–Napoleon configuration). Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="FermatNapoleon"
LIB="FermatNapoleon"
REQUIRED="FermatNapoleon.triSign FermatNapoleon.outerApex FermatNapoleon.napoleonApex FermatNapoleon.napoleonCenter FermatNapoleon.decomp FermatNapoleon.cramer FermatNapoleon.triSign_mul_pos FermatNapoleon.triSign_sq FermatNapoleon.outerApex_vsub FermatNapoleon.napoleonApex_zero FermatNapoleon.napoleonApex_one FermatNapoleon.napoleonApex_two FermatNapoleon.gram_pos FermatNapoleon.areaForm_smul_J_left FermatNapoleon.areaForm_smul_J_right FermatNapoleon.apex_frame FermatNapoleon.apex_inner FermatNapoleon.apex_sum FermatNapoleon.napoleonCenter_vsub FermatNapoleon.fermat_frame FermatNapoleon.sOppSide_of_areaForm FermatNapoleon.inner_comb FermatNapoleon.cos_two_pi_div_three FermatNapoleon.arccos_neg_half FermatNapoleon.norm_eq_of_inner_eq FermatNapoleon.angle_eq_of_inner FermatNapoleon.inner_gt_of_angle_lt FermatNapoleon.weight_pos FermatNapoleon.centroid_three_vsub FermatNapoleon.apex_outward FermatNapoleon.napoleon_dist_eq FermatNapoleon.fermat_point_spec FermatNapoleon.napoleon_concurrent FermatNapoleon.napoleon_fermat FermatNapoleon.napoleon FermatNapoleon.napoleon_angle FermatNapoleon.sbtw_real FermatNapoleon.ptolemy_real FermatNapoleon.ptolemy_collinear FermatNapoleon.inv_norm_sub FermatNapoleon.smul_of_gram_eq_zero FermatNapoleon.inv_inv_vec FermatNapoleon.ptolemy_vec FermatNapoleon.norm_sub_eq_of_inner FermatNapoleon.sphere_vec FermatNapoleon.cross_vec FermatNapoleon.ptolemy_eq_iff FermatNapoleon.l14b_outerApex_eq FermatNapoleon.l14b_apexes FermatNapoleon.l14_apex_outward FermatNapoleon.l14_napoleon_dist_eq FermatNapoleon.l14_napoleon_concurrent FermatNapoleon.l14_napoleon_fermat FermatNapoleon.l14_napoleon FermatNapoleon.l14_napoleon_angle FermatNapoleon.l14_ptolemy_eq_iff FermatNapoleon.l14_ptolemy_collinear FermatNapoleon.l14_ptolemy_real FermatNapoleon.l14_angle_lt FermatNapoleon.l14_ne_of_angle FermatNapoleon.l14_dist_sq FermatNapoleon.l14_dist FermatNapoleon.l14_ne FermatNapoleon.l14_not_collinear FermatNapoleon.l14_sbtw FermatNapoleon.l14_centroid FermatNapoleon.l14T FermatNapoleon.l14T_sign FermatNapoleon.l14w_napoleon FermatNapoleon.l14w_ptolemy_cyclic FermatNapoleon.l14w_ptolemy_collinear FermatNapoleon.l14w_ptolemy_real FermatNapoleon.Blind.BlindSemiperimeter FermatNapoleon.Blind.BlindArea FermatNapoleon.Blind.BlindHeronGamma FermatNapoleon.Blind.BlindEquilateral FermatNapoleon.Blind.BlindInClosedTriangle FermatNapoleon.Blind.BlindStrictlyInside FermatNapoleon.Blind.BlindDistToLine FermatNapoleon.Blind.BlindOrientationSign FermatNapoleon.Blind.BlindOuterApex FermatNapoleon.Blind.BlindApexA FermatNapoleon.Blind.BlindApexB FermatNapoleon.Blind.BlindApexC FermatNapoleon.Blind.BlindNapoleonA FermatNapoleon.Blind.BlindNapoleonB FermatNapoleon.Blind.BlindNapoleonC FermatNapoleon.Blind.agree_sign FermatNapoleon.Blind.agree_outerApex FermatNapoleon.Blind.agree_apexA FermatNapoleon.Blind.agree_apexB FermatNapoleon.Blind.agree_apexC FermatNapoleon.Blind.agree_centerA FermatNapoleon.Blind.agree_centerB FermatNapoleon.Blind.agree_centerC FermatNapoleon.Blind.agree_centroid FermatNapoleon.Blind.agree_orders_real FermatNapoleon.Blind.agree_orders FermatNapoleon.Blind.blind28_stmt FermatNapoleon.Blind.blind37_stmt FermatNapoleon.Blind.blind38_stmt FermatNapoleon.Blind.blind39_stmt FermatNapoleon.Blind.blind40_stmt FermatNapoleon.Blind.blind41_stmt FermatNapoleon.Blind.blind42_stmt FermatNapoleon.Blind.blind43_stmt FermatNapoleon.Blind.blind44_stmt FermatNapoleon.Blind.blind45_stmt FermatNapoleon.Blind.blind46_stmt FermatNapoleon.Blind.blind47_stmt FermatNapoleon.Blind.blind48_stmt FermatNapoleon.Blind.blind49_stmt FermatNapoleon.Blind.blind50_stmt FermatNapoleon.Blind.rb_28 FermatNapoleon.Blind.br_28 FermatNapoleon.Blind.rb_37 FermatNapoleon.Blind.rb_38 FermatNapoleon.Blind.rb_39 FermatNapoleon.Blind.br_37_38_39 FermatNapoleon.Blind.rb_40 FermatNapoleon.Blind.rb_41 FermatNapoleon.Blind.br_40_41 FermatNapoleon.Blind.rb_42 FermatNapoleon.Blind.br_42 FermatNapoleon.Blind.rb_43 FermatNapoleon.Blind.rb_44 FermatNapoleon.Blind.br_43_44 FermatNapoleon.Blind.rb_45 FermatNapoleon.Blind.rb_46 FermatNapoleon.Blind.rb_47 FermatNapoleon.Blind.br_45_46_47 FermatNapoleon.Blind.rb_48 FermatNapoleon.Blind.rb_49 FermatNapoleon.Blind.rb_50 FermatNapoleon.Blind.br_48_49_50 FermatNapoleon.Classical.ClassicalSideA FermatNapoleon.Classical.ClassicalSideB FermatNapoleon.Classical.ClassicalSideC FermatNapoleon.Classical.ClassicalSemiperimeter FermatNapoleon.Classical.ClassicalAreaPts FermatNapoleon.Classical.ClassicalArea FermatNapoleon.Classical.ClassicalCentroid FermatNapoleon.Classical.ClassicalEquilateral FermatNapoleon.Classical.ClassicalSumSq FermatNapoleon.Classical.ClassicalInsideOrOn FermatNapoleon.Classical.ClassicalStrictlyInside FermatNapoleon.Classical.ClassicalDistToLine FermatNapoleon.Classical.ClassicalIsFermatPoint FermatNapoleon.Classical.ClassicalAnglesLt120 FermatNapoleon.Classical.ClassicalOutwardEquilateralApex FermatNapoleon.Classical.ClassicalDistSum FermatNapoleon.Classical.ClassicalDistSqSum FermatNapoleon.Classical.ClassicalInOrderOnCircleOrLine FermatNapoleon.Classical.real_order_iff FermatNapoleon.Classical.col_iff FermatNapoleon.Classical.coplanar_of_cross FermatNapoleon.Classical.sbtw_of_concyclic FermatNapoleon.Classical.inner_of_angle' FermatNapoleon.Classical.vne_of_angle FermatNapoleon.Classical.vne_of_angle' FermatNapoleon.Classical.unit_sum FermatNapoleon.Classical.fermat_unique_vec FermatNapoleon.Classical.fermat_unique FermatNapoleon.Classical.cov_P2 FermatNapoleon.Classical.apex_eq FermatNapoleon.Classical.classical_apexes FermatNapoleon.Classical.cov_F2a FermatNapoleon.Classical.cov_F2b FermatNapoleon.Classical.cov_F2c FermatNapoleon.Classical.cov_F2d FermatNapoleon.Classical.cov_F3"
SOURCES="FermatNapoleon/*.lean FermatNapoleon.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
