import FermatNapoleon.Bridges

/-!
# H4.2–H4.4: the Fermat–Napoleon configuration

`A, B, C = t.points 0, 1, 2`; `A', B', C' = napoleonApex o t 0, 1, 2` are the apexes of the
equilateral triangles erected outward on `BC`, `CA`, `AB`.
-/

open Affine EuclideanGeometry Module
open scoped RealInnerProductSpace Real

namespace FermatNapoleon

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- The apexes are outward: `A'` and `A` lie on opposite sides of the line `BC` (and similarly
for `B'`, `C'`). -/
theorem apex_outward (t : Triangle ℝ P) (i : Fin 3) :
    (line[ℝ, t.points (i + 1), t.points (i + 2)]).SOppSide (t.points i) (napoleonApex o t i) := by
  set p := t.points 1 -ᵥ t.points 0 with hp
  set q := t.points 2 -ᵥ t.points 0 with hq
  have hgram := gram_pos t
  have hw2 := o.inner_sq_add_areaForm_sq p q
  have hw0 : o.areaForm p q ≠ 0 := by
    intro h; rw [h] at hw2; rw [← hp, ← hq] at hgram; nlinarith
  have hσw := triSign_mul_pos o t hw0
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  -- generic step: the side `XY` is traversed in the orientation of `t`
  have key : ∀ X Y Z : P, X ≠ Y → o.areaForm (Y -ᵥ X) (Z -ᵥ X) = o.areaForm p q →
      (line[ℝ, X, Y]).SOppSide Z (outerApex o t X Y) := by
    intro X Y Z hXY hω
    apply sOppSide_of_areaForm o hXY
    rw [hω, outerApex_vsub, map_sub, map_smul, map_smul, o.areaForm_apply_self,
      o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq]
    have hd : 0 < ‖Y -ᵥ X‖ ^ 2 := by
      have : Y -ᵥ X ≠ 0 := vsub_ne_zero.2 hXY.symm
      positivity
    have : o.areaForm p q * (1 / 2 * 0 - triSign o t * (√3 / 2) * ‖Y -ᵥ X‖ ^ 2) =
        -((triSign o t * o.areaForm p q) * (√3 / 2) * ‖Y -ᵥ X‖ ^ 2) := by ring
    simp only [smul_eq_mul] at *
    rw [this, neg_lt_zero]
    positivity
  have ne : ∀ {j k : Fin 3}, j ≠ k → t.points j ≠ t.points k :=
    fun h => t.independent.injective.ne h
  fin_cases i
  · refine key _ _ _ (ne (by decide)) ?_
    change o.areaForm (t.points 2 -ᵥ t.points 1) (t.points 0 -ᵥ t.points 1) = _
    rw [← vsub_sub_vsub_cancel_right (t.points 2) (t.points 1) (t.points 0),
      ← neg_vsub_eq_vsub_rev (t.points 1) (t.points 0), ← hp, ← hq, map_sub, map_neg]
    simp only [LinearMap.sub_apply, o.areaForm_apply_self]
    rw [o.areaForm_swap q p]; ring
  · refine key _ _ _ (ne (by decide)) ?_
    change o.areaForm (t.points 0 -ᵥ t.points 2) (t.points 1 -ᵥ t.points 2) = _
    rw [← vsub_sub_vsub_cancel_right (t.points 1) (t.points 2) (t.points 0),
      ← neg_vsub_eq_vsub_rev (t.points 2) (t.points 0), ← hp, ← hq, map_neg, map_sub]
    simp only [LinearMap.neg_apply, o.areaForm_apply_self]
    rw [o.areaForm_swap q p]; ring
  · exact key _ _ _ (ne (by decide)) rfl

/-- H4.2 (i): `AA' = BB' = CC'`. -/
theorem napoleon_dist_eq (t : Triangle ℝ P) :
    dist (t.points 0) (napoleonApex o t 0) = dist (t.points 1) (napoleonApex o t 1) ∧
      dist (t.points 1) (napoleonApex o t 1) = dist (t.points 2) (napoleonApex o t 2) := by
  obtain ⟨M, -, h0, h1, h2, -⟩ := apex_inner o t
  simp only [dist_comm (t.points _), dist_eq_norm_vsub V]
  exact ⟨norm_eq_of_inner_eq (h0.trans h1.symm), norm_eq_of_inner_eq (h1.trans h2.symm)⟩

/-- The explicit common point: `F - A = (y_A/S)(A' - A)`, `F - B = (y_B/S)(B' - B)`,
`F - C = (y_C/S)(C' - C)`. -/
theorem fermat_point_spec (t : Triangle ℝ P) :
    ∃ (α yA yB yC : ℝ) (F : P), 0 < α ∧
      4 * α ^ 2 * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 * ‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ^ 2) = 3 ∧
      yA = 1 + 2 * α * ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫ ∧
      yB = 1 + 2 * α * (‖t.points 1 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) ∧
      yC = 1 + 2 * α * (‖t.points 2 -ᵥ t.points 0‖ ^ 2 -
        ⟪t.points 1 -ᵥ t.points 0, t.points 2 -ᵥ t.points 0⟫) ∧
      0 < yA + yB + yC ∧
      F -ᵥ t.points 0 = (yA / (yA + yB + yC)) • (napoleonApex o t 0 -ᵥ t.points 0) ∧
      F -ᵥ t.points 1 = (yB / (yA + yB + yC)) • (napoleonApex o t 1 -ᵥ t.points 1) ∧
      F -ᵥ t.points 2 = (yC / (yA + yB + yC)) • (napoleonApex o t 2 -ᵥ t.points 2) := by
  obtain ⟨α, yA, yB, yC, hα, hH, hA, hB, hC, hS, e1, e2⟩ := fermat_frame o t
  set S := yA + yB + yC
  refine ⟨α, yA, yB, yC, (yA / S) • (napoleonApex o t 0 -ᵥ t.points 0) +ᵥ t.points 0, hα, hH,
    hA, hB, hC, hS, vadd_vsub _ _, ?_, ?_⟩
  · rw [vadd_vsub_assoc, div_eq_inv_mul, div_eq_inv_mul, ← smul_smul, ← smul_smul, ← e1]
    have : S⁻¹ • (S • (t.points 0 -ᵥ t.points 1)) = t.points 0 -ᵥ t.points 1 := by
      rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [smul_add, this]
  · rw [vadd_vsub_assoc, div_eq_inv_mul, div_eq_inv_mul, ← smul_smul, ← smul_smul, ← e2]
    have : S⁻¹ • (S • (t.points 0 -ᵥ t.points 2)) = t.points 0 -ᵥ t.points 2 := by
      rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [smul_add, this]

/-- H4.2 (ii): the lines `AA'`, `BB'`, `CC'` are concurrent. -/
theorem napoleon_concurrent (t : Triangle ℝ P) :
    ∃ F : P, F ∈ line[ℝ, t.points 0, napoleonApex o t 0] ∧
      F ∈ line[ℝ, t.points 1, napoleonApex o t 1] ∧
      F ∈ line[ℝ, t.points 2, napoleonApex o t 2] := by
  obtain ⟨α, yA, yB, yC, F, -, -, -, -, -, -, h0, h1, h2⟩ := fermat_point_spec o t
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [← vsub_vadd F (t.points 0), h0]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
  · rw [← vsub_vadd F (t.points 1), h1]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
  · rw [← vsub_vadd F (t.points 2), h2]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- H4.2 (iii): if all angles of `t` are `< 2π/3`, the common point `F` of the three lines sees
the sides under `2π/3`, and `AA' = FA + FB + FC`. -/
theorem napoleon_fermat (t : Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3)
    (F : P) (hFA : F ∈ line[ℝ, t.points 0, napoleonApex o t 0])
    (hFB : F ∈ line[ℝ, t.points 1, napoleonApex o t 1]) :
    ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧ ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      dist (t.points 0) (napoleonApex o t 0) =
        dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) := by
  obtain ⟨α, yA, yB, yC, F0, hα, hH, hA', hB', hC', hS, h0, h1, h2⟩ := fermat_point_spec o t
  obtain ⟨M, hM, n0, n1, n2, i01, i12, i20⟩ := apex_inner o t
  set p := t.points 1 -ᵥ t.points 0 with hp
  set q := t.points 2 -ᵥ t.points 0 with hq
  have hp0 : p ≠ 0 := vsub_ne_zero.2 (t.independent.injective.ne (by decide))
  have hq0 : q ≠ 0 := vsub_ne_zero.2 (t.independent.injective.ne (by decide))
  have hqp : q - p ≠ 0 := by
    rw [hp, hq, vsub_sub_vsub_cancel_right]
    exact vsub_ne_zero.2 (t.independent.injective.ne (by decide))
  -- the weights are positive exactly because the angles are `< 2π/3`
  have pA : 0 < yA := by
    rw [hA']
    exact weight_pos hα hH (Q := ‖p‖ * ‖q‖) (by ring) (inner_gt_of_angle_lt hp0 hq0 hA)
  have pB : 0 < yB := by
    have eB : ∠ (t.points 2) (t.points 1) (t.points 0) =
        InnerProductGeometry.angle (q - p) (-p) := by
      rw [EuclideanGeometry.angle, hp, hq, vsub_sub_vsub_cancel_right, neg_vsub_eq_vsub_rev]
    rw [eB] at hB
    have h := inner_gt_of_angle_lt hqp (neg_ne_zero.2 hp0) hB
    have e : ⟪q - p, -p⟫ = ‖p‖ ^ 2 - ⟪p, q⟫ := by
      rw [inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]; ring
    have e2 : ‖q - p‖ ^ 2 = ‖q‖ ^ 2 + ‖p‖ ^ 2 - 2 * ⟪p, q⟫ := by
      rw [norm_sub_sq_real, real_inner_comm]; ring
    rw [e, norm_neg] at h
    rw [hB']
    refine weight_pos hα hH (Q := ‖q - p‖ * ‖p‖) ?_ h
    rw [mul_pow, e2]; ring
  have pC : 0 < yC := by
    have eC : ∠ (t.points 0) (t.points 2) (t.points 1) =
        InnerProductGeometry.angle (-q) (p - q) := by
      rw [EuclideanGeometry.angle, hp, hq, vsub_sub_vsub_cancel_right, neg_vsub_eq_vsub_rev]
    rw [eC] at hC
    have hpq : p - q ≠ 0 := by intro h; exact hqp (by rw [← neg_sub, h, neg_zero])
    have h := inner_gt_of_angle_lt (neg_ne_zero.2 hq0) hpq hC
    have e : ⟪-q, p - q⟫ = ‖q‖ ^ 2 - ⟪p, q⟫ := by
      rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]; ring
    have e2 : ‖p - q‖ ^ 2 = ‖q‖ ^ 2 + ‖p‖ ^ 2 - 2 * ⟪p, q⟫ := by
      rw [norm_sub_sq_real]; ring
    rw [e, norm_neg] at h
    rw [hC']
    refine weight_pos hα hH (Q := ‖q‖ * ‖p - q‖) ?_ h
    rw [mul_pow, e2]; ring
  set S := yA + yB + yC
  set uA := napoleonApex o t 0 -ᵥ t.points 0
  set uB := napoleonApex o t 1 -ᵥ t.points 1
  set uC := napoleonApex o t 2 -ᵥ t.points 2
  -- `F` is the explicit point `F0`, since the lines `AA'` and `BB'` are not parallel
  have eF : F = F0 := by
    rw [← vsub_vadd F (t.points 0), vadd_left_mem_affineSpan_pair] at hFA
    rw [← vsub_vadd F (t.points 1), vadd_left_mem_affineSpan_pair] at hFB
    obtain ⟨r, hr⟩ := hFA
    obtain ⟨r', hr'⟩ := hFB
    have key : (r - yA / S) • uA = (r' - yB / S) • uB := by
      rw [sub_smul, sub_smul, hr, hr', ← h0, ← h1, vsub_sub_vsub_cancel_right,
        vsub_sub_vsub_cancel_right]
    have k1 : (r - yA / S) * M = (r' - yB / S) * ⟪uA, uB⟫ := by
      have := congrArg (fun v => ⟪v, uA⟫) key
      simp only [real_inner_smul_left] at this
      rw [n0, real_inner_comm] at this; exact this
    have k2 : (r - yA / S) * ⟪uA, uB⟫ = (r' - yB / S) * M := by
      have := congrArg (fun v => ⟪v, uB⟫) key
      simp only [real_inner_smul_left] at this
      rw [n1] at this; exact this
    have hz : (r - yA / S) * M = 0 := by
      linear_combination (4 * k1 + 2 * k2 + (2 * (r' - yB / S) - (r - yA / S)) * i01) / 3
    have hr0 : r = yA / S := by
      rcases mul_eq_zero.1 hz with h | h
      · linarith
      · exact absurd h hM.ne'
    apply (vsub_left_cancel_iff (p := t.points 0)).1
    rw [← hr, h0, hr0]
  subst eF
  have cA : 0 < yA / S := div_pos pA hS
  have cB : 0 < yB / S := div_pos pB hS
  have cC : 0 < yC / S := div_pos pC hS
  have fA : t.points 0 -ᵥ F = -((yA / S) • uA) := by rw [← h0, neg_vsub_eq_vsub_rev]
  have fB : t.points 1 -ᵥ F = -((yB / S) • uB) := by rw [← h1, neg_vsub_eq_vsub_rev]
  have fC : t.points 2 -ᵥ F = -((yC / S) • uC) := by rw [← h2, neg_vsub_eq_vsub_rev]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [EuclideanGeometry.angle, fA, fB, InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_smul_left_of_pos _ _ cA,
      InnerProductGeometry.angle_smul_right_of_pos _ _ cB]
    exact angle_eq_of_inner (by rw [n0]; exact hM) (n0.trans n1.symm) (by rw [n0]; linarith)
  · rw [EuclideanGeometry.angle, fB, fC, InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_smul_left_of_pos _ _ cB,
      InnerProductGeometry.angle_smul_right_of_pos _ _ cC]
    exact angle_eq_of_inner (by rw [n1]; exact hM) (n1.trans n2.symm) (by rw [n1]; linarith)
  · rw [EuclideanGeometry.angle, fC, fA, InnerProductGeometry.angle_neg_neg,
      InnerProductGeometry.angle_smul_left_of_pos _ _ cC,
      InnerProductGeometry.angle_smul_right_of_pos _ _ cA]
    exact angle_eq_of_inner (by rw [n2]; exact hM) (n2.trans n0.symm) (by rw [n2]; linarith)
  · have L1 : ‖uB‖ = ‖uA‖ := norm_eq_of_inner_eq (n1.trans n0.symm)
    have L2 : ‖uC‖ = ‖uA‖ := norm_eq_of_inner_eq (n2.trans n0.symm)
    rw [dist_eq_norm_vsub V F, dist_eq_norm_vsub V F, dist_eq_norm_vsub V F, h0, h1, h2,
      norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg cA.le, Real.norm_of_nonneg cB.le,
      Real.norm_of_nonneg cC.le, L1, L2, dist_comm, dist_eq_norm_vsub V]
    field_simp
    rfl

/-- H4.3 (Napoleon's theorem): the centres of the outer equilateral triangles form an
equilateral triangle whose centroid is the centroid of `t`. -/
theorem napoleon (t : Triangle ℝ P) :
    dist (napoleonCenter o t 0) (napoleonCenter o t 1) =
        dist (napoleonCenter o t 1) (napoleonCenter o t 2) ∧
      dist (napoleonCenter o t 1) (napoleonCenter o t 2) =
        dist (napoleonCenter o t 2) (napoleonCenter o t 0) ∧
      Finset.univ.centroid ℝ ![napoleonCenter o t 0, napoleonCenter o t 1, napoleonCenter o t 2] =
        t.centroid := by
  obtain ⟨M, -, h0, h1, h2, i01, i12, i20⟩ := apex_inner o t
  have hs := apex_sum o t
  have hd : ∀ i j : Fin 3, dist (napoleonCenter o t i) (napoleonCenter o t j) =
      ‖(1 / 3 : ℝ) • ((napoleonApex o t i -ᵥ t.points i) - (napoleonApex o t j -ᵥ t.points j))‖ := by
    intro i j
    rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right _ _ (t.points 0), napoleonCenter_vsub,
      napoleonCenter_vsub, ← smul_sub]
    congr 2; abel
  have hn : ∀ x y : V, ⟪x, x⟫ = M → ⟪y, y⟫ = M → 2 * ⟪x, y⟫ = -M → ⟪x - y, x - y⟫ = 3 * M := by
    intro x y hx hy hxy
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm x y]; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hd, hd, norm_smul, norm_smul]; congr 1
    apply norm_eq_of_inner_eq
    rw [hn _ _ h0 h1 i01, hn _ _ h1 h2 i12]
  · rw [hd, hd, norm_smul, norm_smul]; congr 1
    apply norm_eq_of_inner_eq
    rw [hn _ _ h1 h2 i12, hn _ _ h2 h0 i20]
  · have ht : t.points = ![t.points 0, t.points 1, t.points 2] := by
      ext i; fin_cases i <;> rfl
    apply (vsub_left_cancel_iff (p := t.points 0)).1
    rw [centroid_three_vsub, napoleonCenter_vsub, napoleonCenter_vsub, napoleonCenter_vsub,
      Affine.Simplex.centroid, ht, centroid_three_vsub]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, vsub_self,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
    linear_combination (norm := module) (1 / 9 : ℝ) • hs

/-- H4.4: the directed lines `AA'`, `BB'`, `CC'` pairwise make the angle `2π/3`, so the lines
make the angle `π/3`. -/
theorem napoleon_angle (t : Triangle ℝ P) :
    InnerProductGeometry.angle (napoleonApex o t 0 -ᵥ t.points 0)
        (napoleonApex o t 1 -ᵥ t.points 1) = 2 * π / 3 ∧
      InnerProductGeometry.angle (napoleonApex o t 1 -ᵥ t.points 1)
        (napoleonApex o t 2 -ᵥ t.points 2) = 2 * π / 3 ∧
      InnerProductGeometry.angle (napoleonApex o t 2 -ᵥ t.points 2)
        (napoleonApex o t 0 -ᵥ t.points 0) = 2 * π / 3 ∧
      InnerProductGeometry.angle (napoleonApex o t 0 -ᵥ t.points 0)
        (t.points 1 -ᵥ napoleonApex o t 1) = π / 3 := by
  obtain ⟨M, hM, h0, h1, h2, i01, i12, i20⟩ := apex_inner o t
  have a01 := angle_eq_of_inner (by rw [h0]; exact hM) (h0.trans h1.symm) (by rw [h0]; linarith)
  refine ⟨a01, angle_eq_of_inner (by rw [h1]; exact hM) (h1.trans h2.symm) (by rw [h1]; linarith),
    angle_eq_of_inner (by rw [h2]; exact hM) (h2.trans h0.symm) (by rw [h2]; linarith), ?_⟩
  rw [← neg_vsub_eq_vsub_rev (napoleonApex o t 1), InnerProductGeometry.angle_neg_right, a01]
  ring

end FermatNapoleon
