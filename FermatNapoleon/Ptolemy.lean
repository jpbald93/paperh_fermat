import Mathlib

/-!
# H4.1: the equality case of Ptolemy's inequality

Mathlib has Ptolemy's inequality `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist` and the
equality for a cyclic quadrilateral with crossing diagonals
`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`. Here we prove the converse:
for four distinct points (in any real inner product space),
`AC · BD = AB · CD + BC · AD` holds iff
* `A, B, C, D` are cospherical and the open segments `AC` and `BD` meet, or
* `A, B, C, D` are collinear, one of `B, D` lies strictly between `A` and `C`, and one of `A, C`
  lies strictly between `B` and `D` (the eight orders `ABCD`, `BCDA`, `CDAB`, `DABC` and their
  reversals).

Proof of the hard direction: invert about `A` (by hand on vectors, x' = x/|x|²). The
equality becomes `B'C' + C'D' = B'D'`, so `C'` lies between `B'` and `D'`. If the configuration is
not collinear, the sphere through `A` with centre `A + m`, `⟪m, b'⟫ = ⟪m, d'⟫ = 1/2`, contains
the four points, and the point `X = A + c' / κ`, `κ = (1-μ)|b'|² + μ|d'|²` (where
`c' = (1-μ) b' + μ d'`, and `x' = x/|x|²` for `x = B-A, C-A, D-A`) lies
strictly inside both diagonals. The collinear case reduces to four real numbers.
-/

open EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace FermatNapoleon

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Strict betweenness on the real line. -/
lemma sbtw_real {x y z : ℝ} : Sbtw ℝ x y z ↔ (x < y ∧ y < z) ∨ (z < y ∧ y < x) := by
  unfold Sbtw
  rcases le_total x z with h | h
  · rw [wbtw_iff_of_le h]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact Or.inl ⟨lt_of_le_of_ne h1 (Ne.symm h3), lt_of_le_of_ne h2 h4⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨⟨h1.le, h2.le⟩, h1.ne', h2.ne⟩
      · exfalso; linarith
  · rw [wbtw_comm, wbtw_iff_of_le h]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact Or.inr ⟨lt_of_le_of_ne h1 (Ne.symm h4), lt_of_le_of_ne h2 h3⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exfalso; linarith
      · exact ⟨⟨h1.le, h2.le⟩, h2.ne, h1.ne'⟩

/-- The collinear case on the real line. -/
theorem ptolemy_real {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    |a - c| * |b - d| = |a - b| * |c - d| + |b - c| * |a - d| ↔
      (Sbtw ℝ a b c ∨ Sbtw ℝ a d c) ∧ (Sbtw ℝ b a d ∨ Sbtw ℝ b c d) := by
  simp only [sbtw_real]
  rcases hab.lt_or_gt with h1 | h1 <;> rcases hac.lt_or_gt with h2 | h2 <;>
    rcases had.lt_or_gt with h3 | h3 <;> rcases hbc.lt_or_gt with h4 | h4 <;>
    rcases hbd.lt_or_gt with h5 | h5 <;> rcases hcd.lt_or_gt with h6 | h6
  all_goals first
    | (exfalso; linarith)
    | (have n1 := not_lt.2 h1.le; have n2 := not_lt.2 h2.le; have n3 := not_lt.2 h3.le
       have n4 := not_lt.2 h4.le; have n5 := not_lt.2 h5.le; have n6 := not_lt.2 h6.le
       simp only [abs_of_pos, abs_of_neg, sub_pos, sub_neg, h1, h2, h3, h4, h5, h6, n1, n2, n3,
         n4, n5, n6, and_true, true_and, and_false, false_and, or_false, false_or, iff_true,
         iff_false, and_self, or_self]
       first
         | ring1
         | (intro h; linarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2), mul_pos (sub_pos.2 h1) (sub_pos.2 h3), mul_pos (sub_pos.2 h1) (sub_pos.2 h4), mul_pos (sub_pos.2 h1) (sub_pos.2 h5), mul_pos (sub_pos.2 h1) (sub_pos.2 h6), mul_pos (sub_pos.2 h2) (sub_pos.2 h3), mul_pos (sub_pos.2 h2) (sub_pos.2 h4), mul_pos (sub_pos.2 h2) (sub_pos.2 h5), mul_pos (sub_pos.2 h2) (sub_pos.2 h6), mul_pos (sub_pos.2 h3) (sub_pos.2 h4), mul_pos (sub_pos.2 h3) (sub_pos.2 h5), mul_pos (sub_pos.2 h3) (sub_pos.2 h6), mul_pos (sub_pos.2 h4) (sub_pos.2 h5), mul_pos (sub_pos.2 h4) (sub_pos.2 h6), mul_pos (sub_pos.2 h5) (sub_pos.2 h6)]))

/-- The collinear case: transport to the real line along `lineMap A C`. -/
theorem ptolemy_collinear {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hcol : Collinear ℝ ({A, B, C, D} : Set P)) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D) := by
  have hB : B ∈ line[ℝ, A, C] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAC
  have hD : D ∈ line[ℝ, A, C] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAC
  rw [← vsub_vadd B A, vadd_left_mem_affineSpan_pair] at hB
  rw [← vsub_vadd D A, vadd_left_mem_affineSpan_pair] at hD
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨δ, hδ⟩ := hD
  obtain ⟨f, hf⟩ : ∃ f : ℝ →ᵃ[ℝ] P, f = AffineMap.lineMap A C := ⟨_, rfl⟩
  have eA : A = f 0 := by rw [hf, AffineMap.lineMap_apply_zero]
  have eC : C = f 1 := by rw [hf, AffineMap.lineMap_apply_one]
  have eB : B = f β := by rw [hf, AffineMap.lineMap_apply, hβ, vsub_vadd]
  have eD : D = f δ := by rw [hf, AffineMap.lineMap_apply, hδ, vsub_vadd]
  have hi : Function.Injective f := hf ▸ AffineMap.lineMap_injective ℝ hAC
  have hL : 0 < dist A C := dist_pos.2 hAC
  have hd : ∀ x y : ℝ, dist (f x) (f y) = |x - y| * dist A C := by
    intro x y; rw [hf, dist_lineMap_lineMap, Real.dist_eq]
  have n1 : (0 : ℝ) ≠ β := fun h => hAB (by rw [eA, eB, h])
  have n2 : (0 : ℝ) ≠ 1 := zero_ne_one
  have n3 : (0 : ℝ) ≠ δ := fun h => hAD (by rw [eA, eD, h])
  have n4 : β ≠ 1 := fun h => hBC (by rw [eB, eC, h])
  have n5 : β ≠ δ := fun h => hBD (by rw [eB, eD, h])
  have n6 : (1 : ℝ) ≠ δ := fun h => hCD (by rw [eC, eD, h])
  set L := dist A C
  rw [eA, eB, eC, eD]
  simp only [hd, hi.sbtw_map_iff]
  rw [← ptolemy_real n1 n2 n3 n4 n5 n6]
  have hL2 : L ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    apply mul_right_cancel₀ hL2
    linear_combination h
  · intro h
    linear_combination L ^ 2 * h

/-- Inversion in the unit sphere about the origin scales distances (vector form). -/
lemma inv_norm_sub {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖y‖ * ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖ = ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h : (‖x‖ * ‖y‖ * ‖(‖x‖ ^ 2)⁻¹ • x - (‖y‖ ^ 2)⁻¹ • y‖) ^ 2 = ‖x - y‖ ^ 2 := by
    rw [mul_pow, norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    field_simp
    ring
  exact (pow_left_inj₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h

/-- If `y = r x` with `x ≠ 0`, or `‖x‖²‖y‖² = ⟪x, y⟫²`, then `y` is a multiple of `x`. -/
lemma smul_of_gram_eq_zero {x y : V} (hx : x ≠ 0) (h : ‖x‖ ^ 2 * ‖y‖ ^ 2 - ⟪x, y⟫ ^ 2 = 0) :
    y = (⟪x, y⟫ / ‖x‖ ^ 2) • x := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  have hv : ‖‖x‖ ^ 2 • y - ⟪x, y⟫ • x‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    rw [real_inner_comm y x] at *
    linear_combination ‖x‖ ^ 2 * h
  have : ‖x‖ ^ 2 • y - ⟪x, y⟫ • x = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hv)
  rw [div_eq_inv_mul, mul_smul, ← sub_eq_zero.1 this, smul_smul, inv_mul_cancel₀ hx2, one_smul]

/-- Inversion `x ↦ x / ‖x‖²` is an involution on nonzero vectors. -/
lemma inv_inv_vec {x : V} (hx : x ≠ 0) : (‖(‖x‖ ^ 2)⁻¹ • x‖ ^ 2)⁻¹ • ((‖x‖ ^ 2)⁻¹ • x) = x := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have : ‖(‖x‖ ^ 2)⁻¹ • x‖ = ‖x‖⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  rw [this, smul_smul]
  convert one_smul ℝ x using 2
  field_simp

/-- Vector form of the equality case: inverting about the origin, `c'` lies strictly between
`b'` and `d'`. -/
lemma ptolemy_vec {b c d : V} (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hbc : b ≠ c) (hcd : c ≠ d)
    (h : ‖c‖ * ‖b - d‖ = ‖b‖ * ‖c - d‖ + ‖b - c‖ * ‖d‖) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧
      (‖c‖ ^ 2)⁻¹ • c = (1 - μ) • ((‖b‖ ^ 2)⁻¹ • b) + μ • ((‖d‖ ^ 2)⁻¹ • d) := by
  set b' := (‖b‖ ^ 2)⁻¹ • b
  set c' := (‖c‖ ^ 2)⁻¹ • c
  set d' := (‖d‖ ^ 2)⁻¹ • d
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  rw [← inv_norm_sub hb hd, ← inv_norm_sub hc hd, ← inv_norm_sub hb hc] at h
  have h2 : dist b' c' + dist c' d' = dist b' d' := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    have : ‖b‖ * ‖c‖ * ‖d‖ * (‖b' - c'‖ + ‖c' - d'‖ - ‖b' - d'‖) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h3 | h3
    · exfalso; have : 0 < ‖b‖ * ‖c‖ * ‖d‖ := by positivity
      linarith
    · linarith
  obtain ⟨μ, ⟨hμ0, hμ1⟩, hμ⟩ := dist_add_dist_eq_iff.1 h2
  rw [AffineMap.lineMap_apply_module] at hμ
  have inj : ∀ {x y : V}, x ≠ 0 → y ≠ 0 → (‖x‖ ^ 2)⁻¹ • x = (‖y‖ ^ 2)⁻¹ • y → x = y := by
    intro x y hx hy hxy
    rw [← inv_inv_vec hx, ← inv_inv_vec hy, hxy]
  refine ⟨μ, lt_of_le_of_ne hμ0 ?_, lt_of_le_of_ne hμ1 ?_, hμ.symm⟩
  · rintro rfl
    apply hbc; apply inj hb hc
    change b' = c'
    rw [← hμ]; simp
  · rintro rfl
    apply hcd; apply inj hc hd
    change c' = d'
    rw [← hμ]; simp

/-- If `⟪m, x / ‖x‖²⟫ = 1/2` then `x` lies on the sphere with centre `m` through `0`. -/
lemma norm_sub_eq_of_inner {m x : V} (hx : x ≠ 0) (h : ⟪m, (‖x‖ ^ 2)⁻¹ • x⟫ = 1 / 2) :
    ‖x - m‖ = ‖m‖ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [real_inner_smul_right] at h
  have h' : 2 * ⟪x, m⟫ = ‖x‖ ^ 2 := by
    rw [real_inner_comm]; field_simp at h; linarith
  have : ‖x - m‖ ^ 2 = ‖m‖ ^ 2 := by rw [norm_sub_sq_real]; linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- The sphere through `0`, `b`, `d` (inverses `b'`, `d'` not parallel) contains `c` when
`c' = (1 - μ) b' + μ d'`. -/
lemma sphere_vec {b' d' c' : V} {μ : ℝ} (hc : c' = (1 - μ) • b' + μ • d')
    (hg : ‖b'‖ ^ 2 * ‖d'‖ ^ 2 - ⟪b', d'⟫ ^ 2 ≠ 0) :
    ∃ m : V, ⟪m, b'⟫ = 1 / 2 ∧ ⟪m, c'⟫ = 1 / 2 ∧ ⟪m, d'⟫ = 1 / 2 := by
  set g := ‖b'‖ ^ 2 * ‖d'‖ ^ 2 - ⟪b', d'⟫ ^ 2
  set m := ((‖d'‖ ^ 2 - ⟪b', d'⟫) / (2 * g)) • b' + ((‖b'‖ ^ 2 - ⟪b', d'⟫) / (2 * g)) • d'
  have e1 : ⟪m, b'⟫ = 1 / 2 := by
    simp only [m, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_comm b' d']
    field_simp; ring
  have e2 : ⟪m, d'⟫ = 1 / 2 := by
    simp only [m, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp; ring
  refine ⟨m, e1, ?_, e2⟩
  rw [hc, inner_add_right, real_inner_smul_right, real_inner_smul_right, e1, e2]; ring

/-- The crossing point of the diagonals. -/
lemma cross_vec {b d : V} (hb : b ≠ 0) (hd : d ≠ 0) (hbd : (‖b‖ ^ 2)⁻¹ • b ≠ (‖d‖ ^ 2)⁻¹ • d)
    {μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ‖(1 - μ) • ((‖b‖ ^ 2)⁻¹ • b) + μ • ((‖d‖ ^ 2)⁻¹ • d)‖ ^ 2 < κ ∧
      κ = (1 - μ) * (‖b‖ ^ 2)⁻¹ + μ * (‖d‖ ^ 2)⁻¹ := by
  set b' := (‖b‖ ^ 2)⁻¹ • b
  set d' := (‖d‖ ^ 2)⁻¹ • d
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  have nb : ‖b'‖ ^ 2 = (‖b‖ ^ 2)⁻¹ := by
    simp only [b', norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖b‖ ^ 2)⁻¹)]
    field_simp
  have nd : ‖d'‖ ^ 2 = (‖d‖ ^ 2)⁻¹ := by
    simp only [d', norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖d‖ ^ 2)⁻¹)]
    field_simp
  have hpos : 0 < ‖b' - d'‖ ^ 2 := by
    have : b' - d' ≠ 0 := sub_ne_zero.2 hbd
    positivity
  refine ⟨_, by positivity, ?_, rfl⟩
  rw [norm_sub_sq_real] at hpos
  have e : ‖(1 - μ) • b' + μ • d'‖ ^ 2 =
      (1 - μ) ^ 2 * ‖b'‖ ^ 2 + 2 * ((1 - μ) * μ) * ⟪b', d'⟫ + μ ^ 2 * ‖d'‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq b',
      ← real_inner_self_eq_norm_sq d']
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm b' d']
    ring
  rw [e, ← nb, ← nd]
  have : 0 < μ * (1 - μ) := mul_pos h0 (by linarith)
  nlinarith

/-- H4.1: characterisation of the equality case in Ptolemy's inequality. -/
theorem ptolemy_eq_iff {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Cospherical ({A, B, C, D} : Set P) ∧ ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      (Collinear ℝ ({A, B, C, D} : Set P) ∧
        (Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D)) := by
  constructor
  swap
  · rintro (⟨hs, X, hX1, hX2⟩ | ⟨hcol, hbt⟩)
    · have := mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hs hX1.angle₁₂₃_eq_pi
        hX2.angle₁₂₃_eq_pi
      rw [dist_comm D A] at this
      exact this.symm
    · exact (ptolemy_collinear hAB hAC hAD hBC hBD hCD hcol).2 hbt
  intro h
  have dA : ∀ X : P, dist A X = ‖X -ᵥ A‖ := fun X => by rw [dist_comm, dist_eq_norm_vsub V]
  have dXY : ∀ X Y : P, dist X Y = ‖(X -ᵥ A) - (Y -ᵥ A)‖ := fun X Y => by
    rw [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  set b := B -ᵥ A with hb
  set c := C -ᵥ A with hc
  set d := D -ᵥ A with hd
  have hb0 : b ≠ 0 := vsub_ne_zero.2 hAB.symm
  have hc0 : c ≠ 0 := vsub_ne_zero.2 hAC.symm
  have hd0 : d ≠ 0 := vsub_ne_zero.2 hAD.symm
  have hbc : b ≠ c := fun e => hBC (vsub_left_cancel e)
  have hcd : c ≠ d := fun e => hCD (vsub_left_cancel e)
  have hbd : b ≠ d := fun e => hBD (vsub_left_cancel e)
  rw [dA, dA, dA, dXY B D, dXY C D, dXY B C] at h
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := ptolemy_vec hb0 hc0 hd0 hbc hcd h
  set b' := (‖b‖ ^ 2)⁻¹ • b
  set c' := (‖c‖ ^ 2)⁻¹ • c
  set d' := (‖d‖ ^ 2)⁻¹ • d
  have hb'0 : b' ≠ 0 := smul_ne_zero (by positivity) hb0
  have hbd' : b' ≠ d' := by
    intro e
    apply hbd
    rw [← inv_inv_vec hb0, ← inv_inv_vec hd0]
    change (‖b'‖ ^ 2)⁻¹ • b' = (‖d'‖ ^ 2)⁻¹ • d'
    rw [e]
  by_cases hg : ‖b'‖ ^ 2 * ‖d'‖ ^ 2 - ⟪b', d'⟫ ^ 2 = 0
  · -- collinear case
    right
    have hcol : Collinear ℝ ({A, B, C, D} : Set P) := by
      rw [collinear_iff_of_mem (p₀ := A) (by simp)]
      refine ⟨b, ?_⟩
      have key : ∀ {x : V} {s : ℝ}, x ≠ 0 → (‖x‖ ^ 2)⁻¹ • x = s • b' →
          ∃ r : ℝ, x = r • b := by
        intro x s hx e
        have hx' := inv_inv_vec hx
        rw [e] at hx'
        refine ⟨(‖s • b'‖ ^ 2)⁻¹ * s * (‖b‖ ^ 2)⁻¹, ?_⟩
        rw [← hx']
        simp only [b', smul_smul]
        congr 1; ring
      have hd' := smul_of_gram_eq_zero hb'0 hg
      set k := ⟪b', d'⟫ / ‖b'‖ ^ 2 with hk
      clear_value k
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by rw [one_smul, hb, vsub_vadd]⟩
      · obtain ⟨r, hr⟩ := key hc0 (s := (1 - μ) + μ * k)
          (by change c' = _; rw [hμ, hd']; module)
        exact ⟨r, by rw [← hr, hc, vsub_vadd]⟩
      · obtain ⟨r, hr⟩ := key hd0 (s := k) hd'
        exact ⟨r, by rw [← hr, hd, vsub_vadd]⟩
    refine ⟨hcol, (ptolemy_collinear hAB hAC hAD hBC hBD hCD hcol).1 ?_⟩
    rw [dA, dA, dA, dXY B D, dXY C D, dXY B C]; exact h
  · -- cospherical case
    left
    obtain ⟨m, mb, mc, md⟩ := sphere_vec hμ hg
    obtain ⟨κ, hκ0, hκc, hκ⟩ := cross_vec hb0 hd0 hbd' hμ0 hμ1
    rw [← hμ] at hκc
    have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have nc : ‖c'‖ ^ 2 = (‖c‖ ^ 2)⁻¹ := by
      simp only [c', norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖c‖ ^ 2)⁻¹)]
      field_simp
    rw [nc] at hκc
    have hcκ : 1 < ‖c‖ ^ 2 * κ := by
      have := mul_lt_mul_of_pos_left hκc (by positivity : 0 < ‖c‖ ^ 2)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    refine ⟨⟨m +ᵥ A, ‖m‖, ?_⟩, ⟨(κ⁻¹ • c') +ᵥ A, ?_, ?_⟩⟩
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · rw [dist_comm, dist_vadd_left]
      · rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← hb]; exact norm_sub_eq_of_inner hb0 mb
      · rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← hc]; exact norm_sub_eq_of_inner hc0 mc
      · rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← hd]; exact norm_sub_eq_of_inner hd0 md
    · have e : κ⁻¹ • c' +ᵥ A = AffineMap.lineMap A C ((‖c‖ ^ 2 * κ)⁻¹) := by
        rw [AffineMap.lineMap_apply, ← hc, smul_smul, mul_inv, mul_comm]
      rw [e, sbtw_lineMap_iff]
      exact ⟨hAC, by positivity, inv_lt_one_of_one_lt₀ hcκ⟩
    · have e : κ⁻¹ • c' +ᵥ A = AffineMap.lineMap B D (κ⁻¹ * (μ * (‖d‖ ^ 2)⁻¹)) := by
        rw [AffineMap.lineMap_apply, ← vsub_sub_vsub_cancel_right D B A, ← hb, ← hd]
        conv_rhs => rw [← vsub_vadd B A]
        rw [vadd_vadd, ← hb]
        congr 1
        have k1 : κ⁻¹ * ((1 - μ) * (‖b‖ ^ 2)⁻¹) = 1 - κ⁻¹ * (μ * (‖d‖ ^ 2)⁻¹) := by
          rw [show (1 - μ) * (‖b‖ ^ 2)⁻¹ = κ - μ * (‖d‖ ^ 2)⁻¹ by rw [hκ]; ring, mul_sub,
            inv_mul_cancel₀ hκ0.ne']
        rw [hμ]
        simp only [b', d', smul_smul, smul_add]
        linear_combination (norm := module) k1 • b
      rw [e, sbtw_lineMap_iff]
      have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
      have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
      refine ⟨hBD, by positivity, ?_⟩
      rw [hκ, inv_mul_lt_one₀ (by rw [← hκ]; exact hκ0)]
      have : 0 < (1 - μ) * (‖b‖ ^ 2)⁻¹ := mul_pos (by linarith) (by positivity)
      linarith

end FermatNapoleon
