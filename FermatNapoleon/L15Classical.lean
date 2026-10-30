import FermatNapoleon.Basic
import FermatNapoleon.Lemmas
import FermatNapoleon.Bridges
import FermatNapoleon.Ptolemy
import FermatNapoleon.Main
import FermatNapoleon.L14

/-!
# Layer 15: classical statements (FermatNapoleon)

An independent writer stated the classical theorems in the textbook form, using only Mathlib
and a few elementary definitions, in a separate file, `PaperHClassical.lean`
(sha256 begins 0ac73f94ec9efdb8). This file copies that file's `Classical*` definitions
verbatim (inside the namespace `FermatNapoleon.Classical`) and restates each classical statement with
its verbatim type as `cov_<name>`, proved from the library. Helper lemmas marked NEW PROOF are
arguments that are not in the rest of the library.
-/

open EuclideanGeometry Real
open scoped RealInnerProductSpace

noncomputable section

namespace FermatNapoleon.Classical

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Definitions not (directly) in Mathlib -/

/-- Side `a = BC`. -/
def ClassicalSideA (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)
/-- Side `b = CA`. -/
def ClassicalSideB (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)
/-- Side `c = AB`. -/
def ClassicalSideC (t : Affine.Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)

/-- Semiperimeter `s = (a+b+c)/2`. -/
def ClassicalSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (ClassicalSideA t + ClassicalSideB t + ClassicalSideC t) / 2

/-- Area of the triangle with vertices `A B C`: `Δ = ½·AB·AC·sin A`. -/
def ClassicalAreaPts (A B C : P) : ℝ :=
  1 / 2 * dist A B * dist A C * Real.sin (∠ B A C)

/-- Area `Δ` of a triangle. -/
def ClassicalArea (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalAreaPts (t.points 0) (t.points 1) (t.points 2)

/-- Centroid `G`. -/
def ClassicalCentroid (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ t.points

/-- Equilateral: `a = b = c`. -/
def ClassicalEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  ClassicalSideA t = ClassicalSideB t ∧ ClassicalSideB t = ClassicalSideC t

/-- Sum of squared sides `a² + b² + c²`. -/
def ClassicalSumSq (t : Affine.Triangle ℝ P) : ℝ :=
  ClassicalSideA t ^ 2 + ClassicalSideB t ^ 2 + ClassicalSideC t ^ 2

/-- `X` lies inside or on the triangle (closed convex hull of the vertices):
all barycentric coordinates nonnegative. -/
def ClassicalInsideOrOn (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` lies strictly inside the triangle: all barycentric coordinates positive
(works in any ambient dimension, i.e. relative interior). -/
def ClassicalStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line through `Y` and `Z`. -/
def ClassicalDistToLine (X Y Z : P) : ℝ :=
  Metric.infDist X (affineSpan ℝ {Y, Z} : Set P)

/-- Fermat point: a point seeing each side under `120°`. -/
def ClassicalIsFermatPoint (t : Affine.Triangle ℝ P) (F : P) : Prop :=
  ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
  ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
  ∠ (t.points 0) F (t.points 1) = 2 * π / 3

/-- All angles of the triangle are less than `120°`. -/
def ClassicalAnglesLt120 (t : Affine.Triangle ℝ P) : Prop :=
  ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
  ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
  ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3

/-- `X'` is the apex of the equilateral triangle erected outward on side `YZ`
of a triangle whose third vertex is `X`: `X'Y = X'Z = YZ`, and `X'` lies on the
opposite side of line `YZ` from `X`. -/
def ClassicalOutwardEquilateralApex (X Y Z X' : P) : Prop :=
  dist X' Y = dist Y Z ∧ dist X' Z = dist Y Z ∧
  (affineSpan ℝ {Y, Z}).SOppSide X X'

/-- Sum of distances `XA + XB + XC`. -/
def ClassicalDistSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) + dist X (t.points 1) + dist X (t.points 2)

/-- Sum of squared distances `XA² + XB² + XC²`. -/
def ClassicalDistSqSum (t : Affine.Triangle ℝ P) (X : P) : ℝ :=
  dist X (t.points 0) ^ 2 + dist X (t.points 1) ^ 2 + dist X (t.points 2) ^ 2

/-- Four distinct points lie "in this order" `A, B, C, D` on a circle or line:
either they are concyclic and the diagonals `AC`, `BD` meet (convex position in
the order `ABCD`), or they are collinear and the pair `{A, C}` separates
`{B, D}` (exactly one of `B, D` lies strictly between `A` and `C`). -/
def ClassicalInOrderOnCircleOrLine (A B C D : P) : Prop :=
  (Concyclic ({A, B, C, D} : Set P) ∧
      ∃ X : P, Wbtw ℝ A X C ∧ Wbtw ℝ B X D) ∨
  (Collinear ℝ ({A, B, C, D} : Set P) ∧ (Sbtw ℝ A B C ↔ ¬ Sbtw ℝ A D C))

/-! ### Helpers (NEW PROOF unless stated) -/

/-- Collinear-case order condition on the real line: repository form ↔ classical form. -/
lemma real_order_iff {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ((Sbtw ℝ a b c ∨ Sbtw ℝ a d c) ∧ (Sbtw ℝ b a d ∨ Sbtw ℝ b c d)) ↔
      (Sbtw ℝ a b c ↔ ¬ Sbtw ℝ a d c) := by
  simp only [FermatNapoleon.sbtw_real]
  rcases hab.lt_or_gt with h1 | h1 <;> rcases hac.lt_or_gt with h2 | h2 <;>
    rcases had.lt_or_gt with h3 | h3 <;> rcases hbc.lt_or_gt with h4 | h4 <;>
    rcases hbd.lt_or_gt with h5 | h5 <;> rcases hcd.lt_or_gt with h6 | h6
  all_goals first
    | (exfalso; linarith)
    | (have n1 := not_lt.2 h1.le; have n2 := not_lt.2 h2.le; have n3 := not_lt.2 h3.le
       have n4 := not_lt.2 h4.le; have n5 := not_lt.2 h5.le; have n6 := not_lt.2 h6.le
       simp [h1, h2, h3, h4, h5, h6, n1, n2, n3, n4, n5, n6])

/-- Collinear case for points (transport along `lineMap A C`, as in the repository's
`ptolemy_collinear`). -/
lemma col_iff {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hcol : Collinear ℝ ({A, B, C, D} : Set P)) :
    ((Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D)) ↔
      (Sbtw ℝ A B C ↔ ¬ Sbtw ℝ A D C) := by
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
  have n1 : (0 : ℝ) ≠ β := fun h => hAB (by rw [eA, eB, h])
  have n2 : (0 : ℝ) ≠ 1 := zero_ne_one
  have n3 : (0 : ℝ) ≠ δ := fun h => hAD (by rw [eA, eD, h])
  have n4 : β ≠ 1 := fun h => hBC (by rw [eB, eC, h])
  have n5 : β ≠ δ := fun h => hBD (by rw [eB, eD, h])
  have n6 : (1 : ℝ) ≠ δ := fun h => hCD (by rw [eC, eD, h])
  rw [eA, eB, eC, eD]
  simp only [hi.sbtw_map_iff]
  exact real_order_iff n1 n2 n3 n4 n5 n6

/-- Crossing diagonals force coplanarity. -/
lemma coplanar_of_cross {A B C D X : P} (hX1 : Sbtw ℝ A X C) (hX2 : Sbtw ℝ B X D) :
    Coplanar ℝ ({A, B, C, D} : Set P) := by
  have hXs : X ∈ affineSpan ℝ ({A, B, C} : Set P) :=
    affineSpan_mono ℝ (by intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)
      hX1.wbtw.mem_affineSpan
  have hBs : B ∈ affineSpan ℝ ({A, B, C} : Set P) := mem_affineSpan ℝ (by simp)
  have hD : D ∈ line[ℝ, B, X] :=
    hX2.wbtw.collinear.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hX2.left_ne
  have hDs : D ∈ affineSpan ℝ ({A, B, C} : Set P) := affineSpan_pair_le_of_mem_of_mem hBs hXs hD
  have e : ({A, B, C, D} : Set P) = insert D {A, B, C} := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [e, coplanar_insert_iff_of_mem_affineSpan hDs]
  exact coplanar_triple ℝ A B C

/-- In a cospherical configuration of four distinct points, weakly crossing diagonals cross
strictly. -/
lemma sbtw_of_concyclic {A B C D X : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hs : Cospherical ({A, B, C, D} : Set P))
    (hX1 : Wbtw ℝ A X C) (hX2 : Wbtw ℝ B X D) : Sbtw ℝ A X C ∧ Sbtw ℝ B X D := by
  have nc : ∀ {p q r : P}, p ∈ ({A, B, C, D} : Set P) → q ∈ ({A, B, C, D} : Set P) →
      r ∈ ({A, B, C, D} : Set P) → p ≠ q → p ≠ r → q ≠ r → ¬ Collinear ℝ ({p, q, r} : Set P) := by
    intro p q r hp hq hr hpq hpr hqr
    rw [← affineIndependent_iff_not_collinear_set]
    refine Cospherical.affineIndependent_of_ne (hs.subset ?_) hpq hpr hqr
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hXA : X ≠ A := by
    rintro rfl; exact nc (by simp) (by simp) (by simp) hAB.symm hBD hAD hX2.collinear
  have hXC : X ≠ C := by
    rintro rfl; exact nc (by simp) (by simp) (by simp) hBC hBD hCD hX2.collinear
  have hXB : X ≠ B := by
    rintro rfl; exact nc (by simp) (by simp) (by simp) hAB hAC hBC hX1.collinear
  have hXD : X ≠ D := by
    rintro rfl; exact nc (by simp) (by simp) (by simp) hAD hAC hCD.symm hX1.collinear
  exact ⟨⟨hX1, hXA, hXC⟩, ⟨hX2, hXB, hXD⟩⟩

/-- `2π/3` angle in inner-product form. -/
lemma inner_of_angle' {A F B : P} (h : ∠ A F B = 2 * π / 3) :
    ⟪A -ᵥ F, B -ᵥ F⟫ = -(1 / 2) * (‖A -ᵥ F‖ * ‖B -ᵥ F‖) := by
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  unfold EuclideanGeometry.angle at h
  rw [h, FermatNapoleon.cos_two_pi_div_three]

lemma vne_of_angle {A F B : P} (h : ∠ A F B = 2 * π / 3) : A -ᵥ F ≠ 0 := by
  intro e; rw [vsub_eq_zero_iff_eq] at e; subst e
  rw [angle_self_left] at h; linarith [Real.pi_pos]

lemma vne_of_angle' {A F B : P} (h : ∠ A F B = 2 * π / 3) : B -ᵥ F ≠ 0 :=
  vne_of_angle (B := A) (by rw [angle_comm]; exact h)

/-- Unit vectors at mutual `2π/3` sum to zero. -/
lemma unit_sum {a b c : V} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : ⟪a, b⟫ = -(1 / 2) * (‖a‖ * ‖b‖)) (hbc : ⟪b, c⟫ = -(1 / 2) * (‖b‖ * ‖c‖))
    (hca : ⟪c, a⟫ = -(1 / 2) * (‖c‖ * ‖a‖)) :
    ‖a‖⁻¹ • a + ‖b‖⁻¹ • b + ‖c‖⁻¹ • c = 0 := by
  have na := norm_pos_iff.2 ha; have nb := norm_pos_iff.2 hb; have nc := norm_pos_iff.2 hc
  rw [← inner_self_eq_zero (𝕜 := ℝ)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm a b, real_inner_comm b c, real_inner_comm c a, hab, hbc, hca]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Uniqueness of the point seeing three points under mutual `2π/3` (vector form). NEW PROOF. -/
lemma fermat_unique_vec {a b c g : V} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : ⟪a, b⟫ = -(1 / 2) * (‖a‖ * ‖b‖)) (hbc : ⟪b, c⟫ = -(1 / 2) * (‖b‖ * ‖c‖))
    (hca : ⟪c, a⟫ = -(1 / 2) * (‖c‖ * ‖a‖))
    (ha' : a - g ≠ 0) (hb' : b - g ≠ 0) (hc' : c - g ≠ 0)
    (hab' : ⟪a - g, b - g⟫ = -(1 / 2) * (‖a - g‖ * ‖b - g‖))
    (hbc' : ⟪b - g, c - g⟫ = -(1 / 2) * (‖b - g‖ * ‖c - g‖))
    (hca' : ⟪c - g, a - g⟫ = -(1 / 2) * (‖c - g‖ * ‖a - g‖)) : g = 0 := by
  have unit : ∀ x : V, x ≠ 0 → ‖‖x‖⁻¹ • x‖ = 1 ∧ ⟪x, ‖x‖⁻¹ • x⟫ = ‖x‖ := by
    intro x hx
    have hn := norm_pos_iff.2 hx
    refine ⟨by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'], ?_⟩
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have le : ∀ x u : V, ‖u‖ = 1 → ⟪x, u⟫ ≤ ‖x‖ := by
    intro x u hu; have := real_inner_le_norm x u; rwa [hu, mul_one] at this
  set ua := ‖a‖⁻¹ • a; set ub := ‖b‖⁻¹ • b; set uc := ‖c‖⁻¹ • c
  set va := ‖a - g‖⁻¹ • (a - g); set vb := ‖b - g‖⁻¹ • (b - g); set vc := ‖c - g‖⁻¹ • (c - g)
  have su : ua + ub + uc = 0 := unit_sum ha hb hc hab hbc hca
  have sv : va + vb + vc = 0 := unit_sum ha' hb' hc' hab' hbc' hca'
  obtain ⟨ua1, ua2⟩ := unit a ha; obtain ⟨ub1, ub2⟩ := unit b hb; obtain ⟨uc1, uc2⟩ := unit c hc
  obtain ⟨va1, va2⟩ := unit _ ha'; obtain ⟨vb1, vb2⟩ := unit _ hb'; obtain ⟨vc1, vc2⟩ := unit _ hc'
  have la := le (a - g) ua ua1; have lb := le (b - g) ub ub1; have lc := le (c - g) uc uc1
  have ma := le a va va1; have mb := le b vb vb1; have mc := le c vc vc1
  have e1 : ⟪a - g, ua⟫ + ⟪b - g, ub⟫ + ⟪c - g, uc⟫ = ‖a‖ + ‖b‖ + ‖c‖ := by
    have : ⟪g, ua + ub + uc⟫ = 0 := by rw [su, inner_zero_right]
    simp only [inner_sub_left, inner_add_right] at this ⊢; linarith
  have e2 : ⟪a, va⟫ + ⟪b, vb⟫ + ⟪c, vc⟫ = ‖a - g‖ + ‖b - g‖ + ‖c - g‖ := by
    have : ⟪g, va + vb + vc⟫ = 0 := by rw [sv, inner_zero_right]
    have ea : ⟪a, va⟫ = ⟪a - g, va⟫ + ⟪g, va⟫ := by rw [inner_sub_left]; ring
    have eb : ⟪b, vb⟫ = ⟪b - g, vb⟫ + ⟪g, vb⟫ := by rw [inner_sub_left]; ring
    have ec : ⟪c, vc⟫ = ⟪c - g, vc⟫ + ⟪g, vc⟫ := by rw [inner_sub_left]; ring
    simp only [inner_add_right] at this
    rw [ea, eb, ec]; linarith
  have qa : ⟪a - g, ua⟫ = ‖a - g‖ := by linarith
  have qb : ⟪b - g, ub⟫ = ‖b - g‖ := by linarith
  -- equality in Cauchy–Schwarz
  have cs : ∀ x u : V, ‖u‖ = 1 → ⟪x, u⟫ = ‖x‖ → x = ‖x‖ • u := by
    intro x u hu h
    rw [← sub_eq_zero, ← norm_eq_zero, ← sq_eq_zero_iff (M₀ := ℝ), norm_sub_sq_real,
      norm_smul, real_inner_smul_right, h, hu, Real.norm_of_nonneg (norm_nonneg _)]
    ring
  have xa := cs _ _ ua1 qa; have xb := cs _ _ ub1 qb
  have aa : a = ‖a‖ • ua := by simp only [ua, smul_smul]; rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 ha), one_smul]
  have bb : b = ‖b‖ • ub := by simp only [ub, smul_smul]; rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hb), one_smul]
  have ga : g = (‖a‖ - ‖a - g‖) • ua := by
    rw [sub_smul, ← aa, ← xa]; abel
  have gb : g = (‖b‖ - ‖b - g‖) • ub := by
    rw [sub_smul, ← bb, ← xb]; abel
  have uab : ⟪ua, ub⟫ = -(1 / 2) := by
    simp only [ua, ub, real_inner_smul_left, real_inner_smul_right, hab]
    have na := norm_pos_iff.2 ha; have nb := norm_pos_iff.2 hb
    field_simp
  have uaa : ⟪ua, ua⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ua1]; norm_num
  have ubb : ⟪ub, ub⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ub1]; norm_num
  have i1 : ⟪g, ua⟫ = ‖a‖ - ‖a - g‖ := by
    conv_lhs => rw [ga]
    rw [real_inner_smul_left, uaa, mul_one]
  have i1' : ⟪g, ua⟫ = (‖b‖ - ‖b - g‖) * (-(1 / 2)) := by
    conv_lhs => rw [gb]
    rw [real_inner_smul_left, real_inner_comm, uab]
  have i2 : ⟪g, ub⟫ = ‖b‖ - ‖b - g‖ := by
    conv_lhs => rw [gb]
    rw [real_inner_smul_left, ubb, mul_one]
  have i2' : ⟪g, ub⟫ = (‖a‖ - ‖a - g‖) * (-(1 / 2)) := by
    conv_lhs => rw [ga]
    rw [real_inner_smul_left, uab]
  have hz : ‖a‖ - ‖a - g‖ = 0 := by linarith
  rw [ga, hz, zero_smul]

/-- Uniqueness of the Fermat point (points form). NEW PROOF. -/
lemma fermat_unique {A B C F G : P} (h1 : ∠ A F B = 2 * π / 3) (h2 : ∠ B F C = 2 * π / 3)
    (h3 : ∠ C F A = 2 * π / 3) (g1 : ∠ A G B = 2 * π / 3) (g2 : ∠ B G C = 2 * π / 3)
    (g3 : ∠ C G A = 2 * π / 3) : G = F := by
  have e : ∀ X : P, X -ᵥ G = (X -ᵥ F) - (G -ᵥ F) := fun X => (vsub_sub_vsub_cancel_right X G F).symm
  have := fermat_unique_vec (g := G -ᵥ F) (vne_of_angle h1) (vne_of_angle h2) (vne_of_angle h3)
    (inner_of_angle' h1) (inner_of_angle' h2) (inner_of_angle' h3)
    (by rw [← e]; exact vne_of_angle g1) (by rw [← e]; exact vne_of_angle g2)
    (by rw [← e]; exact vne_of_angle g3)
    (by rw [← e, ← e]; exact inner_of_angle' g1) (by rw [← e, ← e]; exact inner_of_angle' g2)
    (by rw [← e, ← e]; exact inner_of_angle' g3)
  exact vsub_eq_zero_iff_eq.1 this

/-- P2 (Ptolemy's theorem and converse). For four distinct points, equality holds iff
A,B,C,D lie in this order on a circle or a line.
-- AMBIGUOUS: "in this order" is read cyclically (the pair {A,C} separates {B,D}).
-- For collinear points the literal reading `Sbtw A B C ∧ Sbtw B C D` would make the
-- "only if" direction false (e.g. order B,C,D,A on a line also gives equality). -/
theorem cov_P2 (A B C D : P) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      ClassicalInOrderOnCircleOrLine A B C D := by
  rw [FermatNapoleon.ptolemy_eq_iff hAB hAC hAD hBC hBD hCD]
  unfold ClassicalInOrderOnCircleOrLine
  constructor
  · rintro (⟨hs, X, hX1, hX2⟩ | ⟨hcol, hb⟩)
    · exact Or.inl ⟨⟨hs, coplanar_of_cross hX1 hX2⟩, X, hX1.wbtw, hX2.wbtw⟩
    · exact Or.inr ⟨hcol, (col_iff hAB hAC hAD hBC hBD hCD hcol).1 hb⟩
  · rintro (⟨hc, X, hX1, hX2⟩ | ⟨hcol, hb⟩)
    · exact Or.inl ⟨hc.1, X, sbtw_of_concyclic hAB hAC hAD hBC hBD hCD hc.1 hX1 hX2⟩
    · exact Or.inr ⟨hcol, (col_iff hAB hAC hAD hBC hBD hCD hcol).2 hb⟩

section Plane

variable [Fact (Module.finrank ℝ V = 2)]

/-- In the plane, the outward equilateral apex is unique: it coincides with the apex given by
an explicit rotation formula that lies on the opposite side. NEW PROOF (uses the repository's
`decomp` and `sOppSide_of_areaForm`). -/
lemma apex_eq (o : Orientation ℝ V (Fin 2)) {X Y Z A0 A' : P} {s : ℝ} (hs : s ^ 2 = 1)
    (hYZ : Y ≠ Z)
    (h0 : A0 -ᵥ Y = (1 / 2 : ℝ) • (Z -ᵥ Y) - (s * (√3 / 2)) • o.rightAngleRotation (Z -ᵥ Y))
    (h0side : (line[ℝ, Y, Z]).SOppSide X A0)
    (h1 : dist A' Y = dist Y Z) (h2 : dist A' Z = dist Y Z)
    (h1side : (line[ℝ, Y, Z]).SOppSide X A') : A' = A0 := by
  set d := Z -ᵥ Y with hd
  set v := A' -ᵥ Y with hv
  have hd0 : d ≠ 0 := vsub_ne_zero.2 hYZ.symm
  have hn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have nv : ‖v‖ = ‖d‖ := by
    rw [hv, hd, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, h1, dist_comm]
  have nvd : ‖v - d‖ = ‖d‖ := by
    rw [hv, hd, vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, h2,
      dist_comm]
  have hi : ⟪d, v⟫ = ‖d‖ ^ 2 / 2 := by
    have := norm_sub_sq_real v d
    rw [nvd, nv, real_inner_comm] at this; linarith
  have hω := o.inner_sq_add_areaForm_sq d v
  rw [hi, nv] at hω
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hω2 : o.areaForm d v ^ 2 = (s * (√3 / 2) * ‖d‖ ^ 2) ^ 2 := by
    have : (s * (√3 / 2) * ‖d‖ ^ 2) ^ 2 = s ^ 2 * √3 ^ 2 / 4 * ‖d‖ ^ 4 := by ring
    rw [this, hs, h3]; nlinarith
  have hJ : o.areaForm d (A0 -ᵥ Y) = -(s * (√3 / 2) * ‖d‖ ^ 2) := by
    rw [h0, map_sub, map_smul, map_smul, o.areaForm_apply_self,
      o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hω2 with e | e
  · exfalso
    have hopp : (line[ℝ, Y, Z]).SOppSide A0 A' := by
      apply FermatNapoleon.sOppSide_of_areaForm o hYZ
      rw [← hd, ← hv, hJ, e]
      have : 0 < s ^ 2 * (√3 / 2) ^ 2 * ‖d‖ ^ 4 := by
        rw [hs]; have : 0 < √3 := by positivity
        positivity
      nlinarith
    exact (h0side.trans hopp).not_sOppSide h1side
  · have key := FermatNapoleon.decomp o v d
    rw [hi, e] at key
    have : v = A0 -ᵥ Y := by
      apply smul_right_injective V (show ‖d‖ ^ 2 ≠ 0 by positivity)
      simp only
      rw [key, h0]
      module
    exact vsub_left_cancel this

/-- The classical outward apexes are the repository's `napoleonApex` for a suitable orientation. -/
lemma classical_apexes (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    ∃ o : Orientation ℝ V (Fin 2), A' = FermatNapoleon.napoleonApex o t 0 ∧
      B' = FermatNapoleon.napoleonApex o t 1 ∧ C' = FermatNapoleon.napoleonApex o t 2 := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let o : Orientation ℝ V (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2)).orientation
  refine ⟨o, ?_, ?_, ?_⟩
  · exact apex_eq o (FermatNapoleon.triSign_sq o t)
      (t.independent.injective.ne (by decide)) (FermatNapoleon.outerApex_vsub o t _ _)
      (FermatNapoleon.apex_outward o t 0) hA'.1 hA'.2.1 hA'.2.2
  · exact apex_eq o (FermatNapoleon.triSign_sq o t)
      (t.independent.injective.ne (by decide)) (FermatNapoleon.outerApex_vsub o t _ _)
      (FermatNapoleon.apex_outward o t 1) hB'.1 hB'.2.1 hB'.2.2
  · exact apex_eq o (FermatNapoleon.triSign_sq o t)
      (t.independent.injective.ne (by decide)) (FermatNapoleon.outerApex_vsub o t _ _)
      (FermatNapoleon.apex_outward o t 2) hC'.1 hC'.2.1 hC'.2.2

/-- F2 (Fermat–Napoleon). In the plane, erect equilateral triangles BCA′, CAB′, ABC′
outward on the sides. Then AA′ = BB′ = CC′. -/
theorem cov_F2a (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    dist (t.points 0) A' = dist (t.points 1) B' ∧
      dist (t.points 1) B' = dist (t.points 2) C' := by
  obtain ⟨o, rfl, rfl, rfl⟩ := classical_apexes t A' B' C' hA' hB' hC'
  exact FermatNapoleon.napoleon_dist_eq o t

/-- F2 (Fermat–Napoleon). … the lines AA′, BB′, CC′ are concurrent. -/
theorem cov_F2b (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    ∃ Q : P, Q ∈ affineSpan ℝ {t.points 0, A'} ∧ Q ∈ affineSpan ℝ {t.points 1, B'} ∧
      Q ∈ affineSpan ℝ {t.points 2, C'} := by
  obtain ⟨o, rfl, rfl, rfl⟩ := classical_apexes t A' B' C' hA' hB' hC'
  exact FermatNapoleon.napoleon_concurrent o t

/-- F2 (Fermat–Napoleon). … if all angles are < 120° they meet at the Fermat point F and
AA′ = FA + FB + FC. -/
theorem cov_F2c (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C')
    (h : ClassicalAnglesLt120 t) (F : P) (hF : ClassicalIsFermatPoint t F) :
    F ∈ affineSpan ℝ {t.points 0, A'} ∧ F ∈ affineSpan ℝ {t.points 1, B'} ∧
      F ∈ affineSpan ℝ {t.points 2, C'} ∧ dist (t.points 0) A' = ClassicalDistSum t F := by
  obtain ⟨o, rfl, rfl, rfl⟩ := classical_apexes t A' B' C' hA' hB' hC'
  obtain ⟨F0, h0, h1, h2⟩ := FermatNapoleon.napoleon_concurrent o t
  obtain ⟨a01, a12, a20, hd⟩ := FermatNapoleon.napoleon_fermat o t h.1 h.2.1 h.2.2 F0 h0 h1
  obtain rfl : F = F0 := fermat_unique a01 a12 a20 hF.2.2 hF.1 hF.2.1
  exact ⟨h0, h1, h2, hd⟩

/-- F2 (Fermat–Napoleon). … and the lines meet at 60° angles.
-- AMBIGUOUS: the angle between two (unoriented) lines is taken as the angle between
-- direction vectors up to supplement, i.e. the vector angle is 60° or 120°. -/
theorem cov_F2d (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    (InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = π / 3 ∨
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3) ∧
    (InnerProductGeometry.angle (B' -ᵥ t.points 1) (C' -ᵥ t.points 2) = π / 3 ∨
      InnerProductGeometry.angle (B' -ᵥ t.points 1) (C' -ᵥ t.points 2) = 2 * π / 3) ∧
    (InnerProductGeometry.angle (C' -ᵥ t.points 2) (A' -ᵥ t.points 0) = π / 3 ∨
      InnerProductGeometry.angle (C' -ᵥ t.points 2) (A' -ᵥ t.points 0) = 2 * π / 3) := by
  obtain ⟨o, rfl, rfl, rfl⟩ := classical_apexes t A' B' C' hA' hB' hC'
  obtain ⟨x, y, z, -⟩ := FermatNapoleon.napoleon_angle o t
  exact ⟨Or.inr x, Or.inr y, Or.inr z⟩

/-- F3 (Napoleon). The centres of these three equilateral triangles form an equilateral
triangle whose centre is the centroid of ABC.  The centre of the equilateral triangle
`BCA′` is its centroid. -/
theorem cov_F3 (t : Affine.Triangle ℝ P) (A' B' C' : P)
    (hA' : ClassicalOutwardEquilateralApex (t.points 0) (t.points 1) (t.points 2) A')
    (hB' : ClassicalOutwardEquilateralApex (t.points 1) (t.points 2) (t.points 0) B')
    (hC' : ClassicalOutwardEquilateralApex (t.points 2) (t.points 0) (t.points 1) C') :
    let Oa := Finset.univ.centroid ℝ ![t.points 1, t.points 2, A']
    let Ob := Finset.univ.centroid ℝ ![t.points 2, t.points 0, B']
    let Oc := Finset.univ.centroid ℝ ![t.points 0, t.points 1, C']
    dist Oa Ob = dist Ob Oc ∧ dist Ob Oc = dist Oc Oa ∧
      Finset.univ.centroid ℝ ![Oa, Ob, Oc] = ClassicalCentroid t := by
  intro Oa Ob Oc
  obtain ⟨o, rfl, rfl, rfl⟩ := classical_apexes t A' B' C' hA' hB' hC'
  exact FermatNapoleon.napoleon o t

end Plane

end FermatNapoleon.Classical
