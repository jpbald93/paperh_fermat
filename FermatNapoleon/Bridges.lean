import FermatNapoleon.Basic
import FermatNapoleon.Lemmas

/-!
# Bridges: the Napoleon apexes in the frame `p = B - A`, `q = C - A`

With `b² = ‖q‖²`, `c² = ‖p‖²`, `k = ⟪p, q⟫`, `ω = ω(p, q)` (Mathlib's `Orientation.areaForm`) and
`σ = triSign o t`, put `α = σ √3 / (2 ω) > 0`; then `4 α² (b² c² - k²) = 3` and
* `A' - A = (1/2 + α (b² - k)) p + (1/2 + α (c² - k)) q`,
* `B' - B = (-α b² - 1) p + (1/2 + α k) q`,
* `C' - C = (1/2 + α k) p + (-α c² - 1) q`.
All metric statements then reduce to polynomial identities modulo `4 α² (b² c² - k²) = 3`.
-/

open Affine EuclideanGeometry Module
open scoped RealInnerProductSpace Real

namespace FermatNapoleon

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Every vector in the plane decomposes along `d` and `J d`. -/
theorem decomp (x d : V) :
    ‖d‖ ^ 2 • x = ⟪d, x⟫ • d + o.areaForm d x • o.rightAngleRotation d := by
  set v := ‖d‖ ^ 2 • x - (⟪d, x⟫ • d + o.areaForm d x • o.rightAngleRotation d) with hv
  have h1 : ⟪d, v⟫ = 0 := by
    simp only [hv, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, o.inner_rightAngleRotation_right, o.areaForm_apply_self]
    ring
  have h2 : o.areaForm d v = 0 := by
    simp only [hv, map_sub, map_add, map_smul, smul_eq_mul, o.areaForm_apply_self,
      o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq]
    ring
  have h3 := o.inner_sq_add_areaForm_sq d v
  rw [h1, h2] at h3
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · have hd2 : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hd)
    have : ‖v‖ ^ 2 = 0 := by
      have : ‖d‖ ^ 2 * ‖v‖ ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hd2
      · exact h
    have hv0 : v = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    exact sub_eq_zero.1 hv0

/-- Cramer's rule in the plane. -/
theorem cramer {p q : V} (h : o.areaForm p q ≠ 0) (x : V) :
    o.areaForm p q • x = o.areaForm x q • p + o.areaForm p x • q := by
  set v := o.areaForm p q • x - (o.areaForm x q • p + o.areaForm p x • q) with hv
  have h1 : o.areaForm p v = 0 := by
    simp only [hv, map_sub, map_add, map_smul, smul_eq_mul, o.areaForm_apply_self]; ring
  have h2 : o.areaForm q v = 0 := by
    simp only [hv, map_sub, map_add, map_smul, smul_eq_mul, o.areaForm_apply_self]
    rw [o.areaForm_swap q p, o.areaForm_swap x q]; ring
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have hd := decomp o v p
  rw [h1, zero_smul, add_zero] at hd
  have hc : ‖p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hp)
  have hv' : v = (‖p‖ ^ 2)⁻¹ • (⟪p, v⟫ • p) := by rw [← hd, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h3 : o.areaForm q v = (‖p‖ ^ 2)⁻¹ * ⟪p, v⟫ * o.areaForm q p := by
    conv_lhs => rw [hv']
    simp only [map_smul, smul_eq_mul]; ring
  rw [h2, o.areaForm_swap q p] at h3
  have : (‖p‖ ^ 2)⁻¹ * ⟪p, v⟫ = 0 := by
    rcases mul_eq_zero.1 h3.symm with h4 | h4
    · exact h4
    · exact absurd (neg_eq_zero.1 h4) h
  have hv0 : v = 0 := by rw [hv', smul_smul, this, zero_smul]
  rw [hv] at hv0
  exact sub_eq_zero.1 hv0

/-- `σ ω(p, q) > 0` for a nondegenerate triangle. -/
theorem triSign_mul_pos (t : Triangle ℝ P)
    (h : o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) ≠ 0) :
    0 < triSign o t * o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) := by
  unfold triSign
  split_ifs with hp
  · linarith
  · push Not at hp; have := lt_of_le_of_ne hp h; linarith

theorem triSign_sq (t : Triangle ℝ P) : triSign o t ^ 2 = 1 := by
  unfold triSign; split_ifs <;> norm_num

/-- The rotation defining the apexes, in terms of `J`. -/
theorem outerApex_vsub (t : Triangle ℝ P) (X Y : P) :
    outerApex o t X Y -ᵥ X = (1 / 2 : ℝ) • (Y -ᵥ X) -
      (triSign o t * (√3 / 2)) • o.rightAngleRotation (Y -ᵥ X) := by
  rw [outerApex, vadd_vsub, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  unfold triSign
  split_ifs
  · rw [one_mul, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three,
      neg_smul, sub_eq_add_neg, one_mul]
  · rw [neg_one_mul, neg_neg, Real.cos_pi_div_three, Real.sin_pi_div_three, neg_one_mul,
      neg_smul, sub_neg_eq_add]

theorem napoleonApex_zero (t : Triangle ℝ P) :
    napoleonApex o t 0 = outerApex o t (t.points 1) (t.points 2) := rfl

theorem napoleonApex_one (t : Triangle ℝ P) :
    napoleonApex o t 1 = outerApex o t (t.points 2) (t.points 0) := rfl

theorem napoleonApex_two (t : Triangle ℝ P) :
    napoleonApex o t 2 = outerApex o t (t.points 0) (t.points 1) := rfl

omit [Fact (finrank ℝ V = 2)] in
/-- The Gram determinant of a nondegenerate triangle is positive (adapted from
`ErdosMordell.gram_pos` in the Erdős–Mordell development). -/
theorem gram_pos (t : Triangle ℝ P) :
    0 < ‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
      ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2 := by
  have hncol : ¬ Collinear ℝ ({t.points 1, t.points 0, t.points 2} : Set P) := by
    rw [← affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)]
    exact t.independent
  have hsin := sin_pos_of_not_collinear hncol
  have h1 := InnerProductGeometry.cos_angle_mul_norm_mul_norm (t.points 1 -ᵥ t.points 0)
    (t.points 2 -ᵥ t.points 0)
  have h2 := Real.sin_sq_add_cos_sq (∠ (t.points 1) (t.points 0) (t.points 2))
  have hpn : 0 < ‖t.points 1 -ᵥ t.points 0‖ :=
    norm_pos_iff.2 (vsub_ne_zero.2 (t.independent.injective.ne (by decide)))
  have hqn : 0 < ‖t.points 2 -ᵥ t.points 0‖ :=
    norm_pos_iff.2 (vsub_ne_zero.2 (t.independent.injective.ne (by decide)))
  rw [← h1]
  change 0 < _ - (Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) * _) ^ 2
  have : 0 < ‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 := by positivity
  nlinarith [pow_pos hsin 2]

/-- `ω J p` and `ω J q` in the frame `p, q`. -/
theorem areaForm_smul_J_left {p q : V} (h : o.areaForm p q ≠ 0) :
    o.areaForm p q • o.rightAngleRotation p = (-⟪p, q⟫) • p + ‖p‖ ^ 2 • q := by
  rw [cramer o h, o.areaForm_rightAngleRotation_left, o.areaForm_rightAngleRotation_right,
    real_inner_self_eq_norm_sq]

theorem areaForm_smul_J_right {p q : V} (h : o.areaForm p q ≠ 0) :
    o.areaForm p q • o.rightAngleRotation q = (-‖q‖ ^ 2) • p + ⟪p, q⟫ • q := by
  rw [cramer o h, o.areaForm_rightAngleRotation_left, o.areaForm_rightAngleRotation_right,
    real_inner_self_eq_norm_sq]

/-- Frame bridge: the apexes `A'`, `B'`, `C'` in the frame `p = B - A`, `q = C - A`. -/
theorem apex_frame (t : Triangle ℝ P) :
    ∃ α : ℝ, 0 < α ∧
      4 * α ^ 2 * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2) = 3 ∧
      napoleonApex o t 0 -ᵥ t.points 0 =
        (1 / 2 + α * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
          ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫)) • (t.points 1 -ᵥ t.points 0) +
        (1 / 2 + α * (‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
          ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫)) • (t.points 2 -ᵥ t.points 0) ∧
      napoleonApex o t 1 -ᵥ t.points 1 =
        (-α * ‖t.points 2 -ᵥ t.points 0‖ ^ 2 - 1) • (t.points 1 -ᵥ t.points 0) +
        (1 / 2 + α * ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) •
          (t.points 2 -ᵥ t.points 0) ∧
      napoleonApex o t 2 -ᵥ t.points 2 =
        (1 / 2 + α * ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) •
          (t.points 1 -ᵥ t.points 0) +
        (-α * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 - 1) • (t.points 2 -ᵥ t.points 0) := by
  set p := t.points 1 -ᵥ t.points 0 with hp
  set q := t.points 2 -ᵥ t.points 0 with hq
  set σ := triSign o t with hσ
  set w := o.areaForm p q with hw
  have hgram := gram_pos t
  rw [← hp, ← hq] at hgram
  have hw2 : w ^ 2 = ‖q‖ ^ 2 * ‖p‖ ^ 2 - ⟪p, q⟫ ^ 2 := by
    have := o.inner_sq_add_areaForm_sq p q; rw [← hw] at this; linarith
  have hw0 : w ≠ 0 := by rintro h; rw [h] at hw2; linarith
  have hσw : 0 < σ * w := triSign_mul_pos o t hw0
  have hσ2 : σ ^ 2 = 1 := triSign_sq o t
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set α := σ * √3 / (2 * w) with hα
  have hαw : σ * (√3 / 2) = α * w := by rw [hα]; field_simp
  have hα0 : 0 < α := by
    have : α = √3 * (σ * w) / (2 * w ^ 2) := by rw [hα]; field_simp
    rw [this]; positivity
  clear_value α
  have hJ : ∀ x : V, (σ * (√3 / 2)) • o.rightAngleRotation x = α • (w • o.rightAngleRotation x) := by
    intro x; rw [hαw, smul_smul]
  have hJp := areaForm_smul_J_left o hw0
  have hJq := areaForm_smul_J_right o hw0
  rw [← hw] at hJp hJq
  refine ⟨α, hα0, ?_, ?_, ?_, ?_⟩
  · rw [← hw2]; linear_combination (-2) * (2 * α * w + σ * √3) * hαw + 3 * hσ2 + σ ^ 2 * hs3
  · rw [napoleonApex_zero, ← vsub_add_vsub_cancel _ (t.points 1), outerApex_vsub, ← hσ, hJ,
      ← vsub_sub_vsub_cancel_right (t.points 2) (t.points 1) (t.points 0), ← hp, ← hq, map_sub,
      smul_sub]
    linear_combination (norm := module) (-α) • hJq + α • hJp
  · rw [napoleonApex_one, ← vsub_add_vsub_cancel _ (t.points 2), outerApex_vsub, ← hσ, hJ,
      ← vsub_sub_vsub_cancel_right (t.points 2) (t.points 1) (t.points 0), ← hp, ← hq,
      ← neg_vsub_eq_vsub_rev (t.points 2) (t.points 0), ← hq, map_neg, smul_neg]
    linear_combination (norm := module) α • hJq
  · rw [napoleonApex_two, ← vsub_add_vsub_cancel _ (t.points 0), outerApex_vsub, ← hσ, hJ,
      ← hp, ← neg_vsub_eq_vsub_rev (t.points 2) (t.points 0), ← hq]
    linear_combination (norm := module) (-α) • hJp

/-- Gram data of the vectors `A' - A`, `B' - B`, `C' - C`: equal squared lengths `M > 0` and
pairwise inner products `-M/2`. -/
theorem apex_inner (t : Triangle ℝ P) :
    ∃ M : ℝ, 0 < M ∧
      ⟪napoleonApex o t 0 -ᵥ t.points 0, napoleonApex o t 0 -ᵥ t.points 0⟫ = M ∧
      ⟪napoleonApex o t 1 -ᵥ t.points 1, napoleonApex o t 1 -ᵥ t.points 1⟫ = M ∧
      ⟪napoleonApex o t 2 -ᵥ t.points 2, napoleonApex o t 2 -ᵥ t.points 2⟫ = M ∧
      2 * ⟪napoleonApex o t 0 -ᵥ t.points 0, napoleonApex o t 1 -ᵥ t.points 1⟫ = -M ∧
      2 * ⟪napoleonApex o t 1 -ᵥ t.points 1, napoleonApex o t 2 -ᵥ t.points 2⟫ = -M ∧
      2 * ⟪napoleonApex o t 2 -ᵥ t.points 2, napoleonApex o t 0 -ᵥ t.points 0⟫ = -M := by
  obtain ⟨α, hα, hH, h0, h1, h2⟩ := apex_frame o t
  set p := t.points 1 -ᵥ t.points 0
  set q := t.points 2 -ᵥ t.points 0
  have hm : 0 ≤ ‖q - p‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, real_inner_comm p q] at hm
  refine ⟨⟪napoleonApex o t 0 -ᵥ t.points 0, napoleonApex o t 0 -ᵥ t.points 0⟫, ?_, rfl,
    ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h0, h1, h2, inner_comb]
  · have e : 4 * α * ((1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) *
        ‖p‖ ^ 2 + ((1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) +
        (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫))) * ⟪p, q⟫ +
        (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) * ‖q‖ ^ 2) =
        4 * α * (‖q‖ ^ 2 + ‖p‖ ^ 2 - ⟪p, q⟫) + 6 := by
      linear_combination (α * ‖q‖ ^ 2 + α * ‖p‖ ^ 2 - 2 * α * ⟪p, q⟫ + 2) * hH
    have : 0 < 4 * α * (‖q‖ ^ 2 + ‖p‖ ^ 2 - ⟪p, q⟫) + 6 := by
      have : 0 ≤ ‖q‖ ^ 2 + ‖p‖ ^ 2 - ⟪p, q⟫ := by linarith [sq_nonneg ‖p‖, sq_nonneg ‖q‖]
      positivity
    rw [← e] at this
    exact pos_of_mul_pos_right this (by positivity)
  · linear_combination (-(‖p‖ ^ 2 - 2 * ⟪p, q⟫) / 4) * hH
  · linear_combination (-(‖q‖ ^ 2 - 2 * ⟪p, q⟫) / 4) * hH
  · linear_combination (-(‖q‖ ^ 2 - ‖p‖ ^ 2) / 4) * hH
  · linear_combination ((‖q‖ ^ 2 + ‖p‖ ^ 2 - 4 * ⟪p, q⟫) / 4) * hH
  · linear_combination ((‖q‖ ^ 2 - ‖p‖ ^ 2) / 4) * hH

/-- The three vectors `A' - A`, `B' - B`, `C' - C` sum to zero. -/
theorem apex_sum (t : Triangle ℝ P) :
    (napoleonApex o t 0 -ᵥ t.points 0) + (napoleonApex o t 1 -ᵥ t.points 1) +
      (napoleonApex o t 2 -ᵥ t.points 2) = 0 := by
  obtain ⟨α, -, -, h0, h1, h2⟩ := apex_frame o t
  rw [h0, h1, h2]
  module

/-- Centre bridge: `Nᵢ - A = ((B - A) + (C - A) + (Pᵢ' - Pᵢ)) / 3`. -/
theorem napoleonCenter_vsub (t : Triangle ℝ P) (i : Fin 3) :
    napoleonCenter o t i -ᵥ t.points 0 = (1 / 3 : ℝ) • ((t.points 1 -ᵥ t.points 0) +
      (t.points 2 -ᵥ t.points 0) + (napoleonApex o t i -ᵥ t.points i)) := by
  rw [napoleonCenter, centroid_three_vsub]
  fin_cases i <;> simp
  · rw [← vsub_add_vsub_cancel (napoleonApex o t 1) (t.points 1) (t.points 0)]; module
  · rw [← vsub_add_vsub_cancel (napoleonApex o t 2) (t.points 2) (t.points 0)]; module

/-- Fermat-point bridge: with `y_A = 1 + 2αk`, `y_B = 1 + 2α(c² - k)`, `y_C = 1 + 2α(b² - k)` and
`S = y_A + y_B + y_C > 0`, the point `F = A + (y_A/S)(A' - A)` satisfies
`F - B = (y_B/S)(B' - B)` and `F - C = (y_C/S)(C' - C)`. -/
theorem fermat_frame (t : Triangle ℝ P) :
    ∃ α yA yB yC : ℝ, 0 < α ∧
      4 * α ^ 2 * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2) = 3 ∧
      yA = 1 + 2 * α * ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ∧
      yB = 1 + 2 * α * (‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) ∧
      yC = 1 + 2 * α * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) ∧
      0 < yA + yB + yC ∧
      yA • (napoleonApex o t 0 -ᵥ t.points 0) + (yA + yB + yC) • (t.points 0 -ᵥ t.points 1) =
        yB • (napoleonApex o t 1 -ᵥ t.points 1) ∧
      yA • (napoleonApex o t 0 -ᵥ t.points 0) + (yA + yB + yC) • (t.points 0 -ᵥ t.points 2) =
        yC • (napoleonApex o t 2 -ᵥ t.points 2) := by
  obtain ⟨α, hα, hH, h0, h1, h2⟩ := apex_frame o t
  set p := t.points 1 -ᵥ t.points 0 with hp
  set q := t.points 2 -ᵥ t.points 0 with hq
  have hm : 0 ≤ ‖q - p‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, real_inner_comm p q] at hm
  refine ⟨α, _, _, _, hα, hH, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have : 0 ≤ ‖q‖ ^ 2 + ‖p‖ ^ 2 - ⟪p, q⟫ := by linarith [sq_nonneg ‖p‖, sq_nonneg ‖q‖]
    have : 0 ≤ α * (‖q‖ ^ 2 + ‖p‖ ^ 2 - ⟪p, q⟫) := mul_nonneg hα.le this
    linarith
  · rw [h0, h1, ← neg_vsub_eq_vsub_rev (t.points 1), ← hp]
    rw [← sub_eq_zero]
    have e1 : (1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) -
        ((1 + 2 * α * ⟪p, q⟫) + (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) +
          (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫))) -
        (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (-α * ‖q‖ ^ 2 - 1) = 0 := by
      linear_combination (1 / 2 : ℝ) * hH
    have e2 : (1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) -
        (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * ⟪p, q⟫) = 0 := by ring
    calc _ = ((1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) -
        ((1 + 2 * α * ⟪p, q⟫) + (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) +
          (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫))) -
        (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (-α * ‖q‖ ^ 2 - 1)) • p +
        ((1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) -
        (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * ⟪p, q⟫)) • q := by module
      _ = 0 := by rw [e1, e2]; simp
  · rw [h0, h2, ← neg_vsub_eq_vsub_rev (t.points 2), ← hq]
    rw [← sub_eq_zero]
    have e1 : (1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) -
        ((1 + 2 * α * ⟪p, q⟫) + (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) +
          (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫))) -
        (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (-α * ‖p‖ ^ 2 - 1) = 0 := by
      linear_combination (1 / 2 : ℝ) * hH
    have e2 : (1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) -
        (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * ⟪p, q⟫) = 0 := by ring
    calc _ = ((1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖q‖ ^ 2 - ⟪p, q⟫)) -
        (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (1 / 2 + α * ⟪p, q⟫)) • p +
        ((1 + 2 * α * ⟪p, q⟫) * (1 / 2 + α * (‖p‖ ^ 2 - ⟪p, q⟫)) -
        ((1 + 2 * α * ⟪p, q⟫) + (1 + 2 * α * (‖p‖ ^ 2 - ⟪p, q⟫)) +
          (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫))) -
        (1 + 2 * α * (‖q‖ ^ 2 - ⟪p, q⟫)) * (-α * ‖p‖ ^ 2 - 1)) • q := by module
      _ = 0 := by rw [e1, e2]; simp

/-- Opposite sides of a line in the plane, via the area form. -/
theorem sOppSide_of_areaForm {X Y Z W : P} (hXY : X ≠ Y)
    (h : o.areaForm (Y -ᵥ X) (Z -ᵥ X) * o.areaForm (Y -ᵥ X) (W -ᵥ X) < 0) :
    (line[ℝ, X, Y]).SOppSide Z W := by
  set d := Y -ᵥ X with hd
  have hd0 : d ≠ 0 := vsub_ne_zero.2 hXY.symm
  have hn : 0 < ‖d‖ ^ 2 := by positivity
  set c := (‖d‖ ^ 2)⁻¹
  have hZ := decomp o (Z -ᵥ X) d
  have hW := decomp o (W -ᵥ X) d
  have mem : ∀ r : ℝ, r • d +ᵥ X ∈ line[ℝ, X, Y] := fun r =>
    smul_vsub_vadd_mem_affineSpan_pair r X Y
  have eZ : Z -ᵥ ((c * ⟪d, Z -ᵥ X⟫) • d +ᵥ X) =
      (c * o.areaForm d (Z -ᵥ X)) • o.rightAngleRotation d := by
    rw [vsub_vadd_eq_vsub_sub]
    calc Z -ᵥ X - (c * ⟪d, Z -ᵥ X⟫) • d =
        c • (‖d‖ ^ 2 • (Z -ᵥ X) - ⟪d, Z -ᵥ X⟫ • d) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hn.ne', one_smul, mul_smul]
      _ = _ := by rw [hZ]; module
  have eW : W -ᵥ ((c * ⟪d, W -ᵥ X⟫) • d +ᵥ X) =
      (c * o.areaForm d (W -ᵥ X)) • o.rightAngleRotation d := by
    rw [vsub_vadd_eq_vsub_sub]
    calc W -ᵥ X - (c * ⟪d, W -ᵥ X⟫) • d =
        c • (‖d‖ ^ 2 • (W -ᵥ X) - ⟪d, W -ᵥ X⟫ • d) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hn.ne', one_smul, mul_smul]
      _ = _ := by rw [hW]; module
  have notmem : ∀ V' : P, o.areaForm d (V' -ᵥ X) ≠ 0 → V' ∉ line[ℝ, X, Y] := by
    intro V' hV hm
    rw [← vsub_vadd V' X, vadd_left_mem_affineSpan_pair] at hm
    obtain ⟨r, hr⟩ := hm
    rw [← hr, ← hd, map_smul, o.areaForm_apply_self, smul_zero] at hV
    exact hV rfl
  have hc : 0 < c := inv_pos.2 hn
  refine AffineSubspace.sOppSide_of_vsub_eq_smul (mem _) (mem _) eZ eW ?_ (notmem Z ?_) (notmem W ?_)
  · have : c * o.areaForm d (Z -ᵥ X) * (c * o.areaForm d (W -ᵥ X)) =
        c ^ 2 * (o.areaForm d (Z -ᵥ X) * o.areaForm d (W -ᵥ X)) := by ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
  · intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
  · intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h

end FermatNapoleon
