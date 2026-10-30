import Mathlib

/-!
# Generic helper lemmas (no dimension assumption)

`inner_comb`, `cos_two_pi_div_three` and `arccos_neg_half` are adapted from the Erdős–Mordell /
Fermat–Torricelli development (`ErdosMordell.inner_comb`, `ErdosMordell.cos_two_pi_div_three`,
`ErdosMordell.arccos_neg_half`).
-/

open Affine EuclideanGeometry
open scoped RealInnerProductSpace Real

namespace FermatNapoleon

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Inner product of two combinations of `p`, `q`. -/
lemma inner_comb (p q : V) (α β γ δ : ℝ) :
    ⟪α • p + β • q, γ • p + δ • q⟫ =
      α * γ * ‖p‖ ^ 2 + (α * δ + β * γ) * ⟪p, q⟫ + β * δ * ‖q‖ ^ 2 := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm p q]
  ring

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

lemma arccos_neg_half : Real.arccos (-(1 / 2)) = 2 * π / 3 := by
  rw [Real.arccos_neg, Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
    Real.cos_pi_div_three.symm]
  ring

lemma norm_eq_of_inner_eq {U W : V} (h : ⟪U, U⟫ = ⟪W, W⟫) : ‖U‖ = ‖W‖ := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `‖U‖ = ‖W‖ ≠ 0` and `2 ⟪U, W⟫ + ⟪U, U⟫ = 0` give the angle `2π/3`. -/
lemma angle_eq_of_inner {U W : V} (h0 : 0 < ⟪U, U⟫) (h1 : ⟪U, U⟫ = ⟪W, W⟫)
    (h2 : 2 * ⟪U, W⟫ + ⟪U, U⟫ = 0) : InnerProductGeometry.angle U W = 2 * π / 3 := by
  have hn := norm_eq_of_inner_eq h1
  rw [real_inner_self_eq_norm_sq] at h0 h2
  have hU0 : ‖U‖ * ‖U‖ ≠ 0 := by rw [← sq]; exact h0.ne'
  have e : ⟪U, W⟫ / (‖U‖ * ‖W‖) = -(1 / 2) := by
    rw [← hn, div_eq_iff hU0]; linear_combination h2 / 2
  unfold InnerProductGeometry.angle
  rw [e, arccos_neg_half]

/-- An angle `< 2π/3` between nonzero vectors gives `⟪x, y⟫ > -1/2 ‖x‖ ‖y‖` (adapted from
`ErdosMordell.inner_gt_of_angle_lt`). -/
lemma inner_gt_of_angle_lt {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : InnerProductGeometry.angle x y < 2 * π / 3) :
    -(1 / 2) * (‖x‖ * ‖y‖) < ⟪x, y⟫ := by
  have hc : Real.cos (2 * π / 3) < Real.cos (InnerProductGeometry.angle x y) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg x y)
      (by linarith [Real.pi_pos]) h
  rw [cos_two_pi_div_three] at hc
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  have : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)
  nlinarith

/-- Positivity of the Fermat weights `1 + 2 α m` from `m > -Q/2`. -/
lemma weight_pos {α D Q m : ℝ} (hα : 0 < α) (hD : 4 * α ^ 2 * D = 3) (hQ : Q ^ 2 - m ^ 2 = D)
    (hm : -(1 / 2) * Q < m) : 0 < 1 + 2 * α * m := by
  rcases le_or_gt 0 m with h | h
  · positivity
  · have h1 : 4 * m ^ 2 < Q ^ 2 := by nlinarith
    have h2 : (2 * α * m) ^ 2 < 1 := by nlinarith
    nlinarith

/-- Centroid of three points, seen from an arbitrary point. -/
lemma centroid_three_vsub (a b c X : P) :
    Finset.univ.centroid ℝ ![a, b, c] -ᵥ X =
      (1 / 3 : ℝ) • (a -ᵥ X) + (1 / 3 : ℝ) • (b -ᵥ X) + (1 / 3 : ℝ) • (c -ᵥ X) := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
    (Finset.sum_centroidWeights_eq_one_of_card_ne_zero _ _ (by simp)) X, vadd_vsub,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
  simp [Finset.centroidWeights_apply]

end FermatNapoleon
