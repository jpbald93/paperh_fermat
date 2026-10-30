import FermatNapoleon.Main
import FermatNapoleon.Ptolemy

/-!
# Layer 14: Mathlib-only restatements and witnesses

Each `l14_*` theorem restates a main theorem with a type that mentions only Mathlib notions.
The local `triSign`, `outerApex`, `napoleonApex` and `napoleonCenter` are unfolded: the apexes
`A', B', C'` enter as points satisfying the explicit formula
`A' = (½ (C - B) - σ (√3/2) J (C - B)) +ᵥ B` (and cyclically), where `J = o.rightAngleRotation`
and `σ = if 0 < o.areaForm (B - A) (C - A) then 1 else -1` (this is Mathlib's rotation by
`-σ π/3`, bridge `l14b_outerApex_eq`), and the Napoleon centres as
`Finset.univ.centroid ℝ ![B, C, A']` (and cyclically). The Ptolemy theorems are already stated
with Mathlib notions only and are restated verbatim.
The `l14w_*` theorems are explicit witnesses in `ℂ` (with `Complex.orientation`, for which
`J z = I * z`).
-/

open Affine EuclideanGeometry Module
open scoped RealInnerProductSpace Real

namespace FermatNapoleon

section General

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-! ### Bridges -/

theorem l14b_outerApex_eq (t : Triangle ℝ P) (X Y : P) :
    outerApex o t X Y = ((1 / 2 : ℝ) • (Y -ᵥ X) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (Y -ᵥ X)) +ᵥ X := by
  rw [eq_vadd_iff_vsub_eq, outerApex_vsub, triSign]

theorem l14b_apexes (t : Triangle ℝ P) (A' B' C' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0) :
    napoleonApex o t 0 = A' ∧ napoleonApex o t 1 = B' ∧ napoleonApex o t 2 = C' := by
  rw [hA', hB', hC']
  exact ⟨l14b_outerApex_eq o t _ _, l14b_outerApex_eq o t _ _, l14b_outerApex_eq o t _ _⟩

/-! ### Mathlib-only restatements -/

theorem l14_apex_outward (t : Triangle ℝ P) (i : Fin 3) (A' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points (i + 2) -ᵥ t.points (i + 1)) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points (i + 2) -ᵥ t.points (i + 1))) +ᵥ t.points (i + 1)) :
    (line[ℝ, t.points (i + 1), t.points (i + 2)]).SOppSide (t.points i) A' := by
  rw [hA', ← l14b_outerApex_eq]
  exact apex_outward o t i

theorem l14_napoleon_dist_eq (t : Triangle ℝ P) (A' B' C' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0) :
    dist (t.points 0) A' = dist (t.points 1) B' ∧ dist (t.points 1) B' = dist (t.points 2) C' := by
  obtain ⟨e0, e1, e2⟩ := l14b_apexes o t A' B' C' hA' hB' hC'
  subst e0 e1 e2
  exact napoleon_dist_eq o t

theorem l14_napoleon_concurrent (t : Triangle ℝ P) (A' B' C' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0) :
    ∃ F : P, F ∈ line[ℝ, t.points 0, A'] ∧ F ∈ line[ℝ, t.points 1, B'] ∧
      F ∈ line[ℝ, t.points 2, C'] := by
  obtain ⟨e0, e1, e2⟩ := l14b_apexes o t A' B' C' hA' hB' hC'
  subst e0 e1 e2
  exact napoleon_concurrent o t

theorem l14_napoleon_fermat (t : Triangle ℝ P) (A' B' C' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3)
    (F : P) (hFA : F ∈ line[ℝ, t.points 0, A']) (hFB : F ∈ line[ℝ, t.points 1, B']) :
    ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧ ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      dist (t.points 0) A' = dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2) := by
  obtain ⟨e0, e1, e2⟩ := l14b_apexes o t A' B' C' hA' hB' hC'
  subst e0 e1 e2
  exact napoleon_fermat o t hA hB hC F hFA hFB

theorem l14_napoleon (t : Triangle ℝ P) (A' B' C' N₀ N₁ N₂ : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0)
    (hN₀ : N₀ = Finset.univ.centroid ℝ ![t.points 1, t.points 2, A'])
    (hN₁ : N₁ = Finset.univ.centroid ℝ ![t.points 2, t.points 0, B'])
    (hN₂ : N₂ = Finset.univ.centroid ℝ ![t.points 0, t.points 1, C']) :
    dist N₀ N₁ = dist N₁ N₂ ∧ dist N₁ N₂ = dist N₂ N₀ ∧
      Finset.univ.centroid ℝ ![N₀, N₁, N₂] = t.centroid := by
  obtain ⟨e0, e1, e2⟩ := l14b_apexes o t A' B' C' hA' hB' hC'
  subst e0 e1 e2 hN₀ hN₁ hN₂
  exact napoleon o t

theorem l14_napoleon_angle (t : Triangle ℝ P) (A' B' C' : P)
    (hA' : A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1)
    (hB' : B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2)
    (hC' : C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          o.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0) :
    InnerProductGeometry.angle (A' -ᵥ t.points 0) (B' -ᵥ t.points 1) = 2 * π / 3 ∧
      InnerProductGeometry.angle (B' -ᵥ t.points 1) (C' -ᵥ t.points 2) = 2 * π / 3 ∧
      InnerProductGeometry.angle (C' -ᵥ t.points 2) (A' -ᵥ t.points 0) = 2 * π / 3 ∧
      InnerProductGeometry.angle (A' -ᵥ t.points 0) (t.points 1 -ᵥ B') = π / 3 := by
  obtain ⟨e0, e1, e2⟩ := l14b_apexes o t A' B' C' hA' hB' hC'
  subst e0 e1 e2
  exact napoleon_angle o t

end General

section Ptolemy

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem l14_ptolemy_eq_iff {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Cospherical ({A, B, C, D} : Set P) ∧ ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      (Collinear ℝ ({A, B, C, D} : Set P) ∧
        (Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D)) :=
  ptolemy_eq_iff hAB hAC hAD hBC hBD hCD

theorem l14_ptolemy_collinear {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) (hcol : Collinear ℝ ({A, B, C, D} : Set P)) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D) :=
  ptolemy_collinear hAB hAC hAD hBC hBD hCD hcol

theorem l14_ptolemy_real {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    |a - c| * |b - d| = |a - b| * |c - d| + |b - c| * |a - d| ↔
      (Sbtw ℝ a b c ∨ Sbtw ℝ a d c) ∧ (Sbtw ℝ b a d ∨ Sbtw ℝ b c d) :=
  ptolemy_real hab hac had hbc hbd hcd

/-- An angle with nonnegative inner product is `< 2π/3`. -/
theorem l14_angle_lt {A B C : P} (h : 0 ≤ ⟪A -ᵥ B, C -ᵥ B⟫) : ∠ A B C < 2 * π / 3 := by
  have : ∠ A B C ≤ π / 2 := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg h (by positivity)
  linarith [Real.pi_pos]

theorem l14_ne_of_angle {A F B : P} (h : ∠ A F B = 2 * π / 3) : F ≠ A := by
  rintro rfl
  rw [angle_self_left] at h
  linarith [Real.pi_pos]

end Ptolemy

/-! ### Witnesses (in `ℂ`) -/

attribute [local instance] Complex.finrank_real_complex_fact

theorem l14_dist_sq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

theorem l14_dist (z w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = r ^ 2) : dist z w = r := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hr]

theorem l14_ne (z w : ℂ) (h : z.re ≠ w.re ∨ z.im ≠ w.im) : z ≠ w := by
  rintro rfl; tauto

theorem l14_not_collinear (X Y Z : ℂ)
    (h : (Y.re - X.re) * (Z.im - X.im) - (Y.im - X.im) * (Z.re - X.re) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set ℂ) := by
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  apply h
  have h0 := congrArg Complex.re hr; have h1 := congrArg Complex.im hr
  have h2 := congrArg Complex.re hs; have h3 := congrArg Complex.im hs
  simp only [vadd_eq_add, Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]; ring

theorem l14_sbtw (X M Z : ℂ) (hne : X ≠ Z) (h0 : M.re = (X.re + Z.re) / 2)
    (h1 : M.im = (X.im + Z.im) / 2) : Sbtw ℝ X M Z := by
  have : M = midpoint ℝ X Z := by
    apply Complex.ext <;> simp [midpoint_eq_smul_add, h0, h1] <;> ring
  rw [this]; exact sbtw_midpoint_of_ne ℝ hne

theorem l14_centroid (a b c : ℂ) :
    Finset.univ.centroid ℝ ![a, b, c] = (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b + (1 / 3 : ℝ) • c := by
  have h := centroid_three_vsub a b c (0 : ℂ)
  simpa using h

/-- The witness triangle `A = 0`, `B = 4`, `C = 3i` (positively oriented, `σ = 1`). -/
noncomputable def l14T : Triangle ℝ ℂ :=
  ⟨![0, 4, 3 * Complex.I], affineIndependent_iff_not_collinear_set.2
    (l14_not_collinear _ _ _ (by simp))⟩

theorem l14T_sign :
    (if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else -1) = 1 := by
  rw [if_pos]; simp [l14T]

/-- Witness for the Napoleon theorems: for `A = 0`, `B = 4`, `C = 3i` the outer apexes are
`A' = (2 + 3√3/2) + (3/2 + 2√3) i`, `B' = -3√3/2 + (3/2) i`, `C' = 2 - 2√3 i`; they are pairwise
distinct and distinct from the vertices; all angles are `< 2π/3` (inner products `0, 16, 9`); the
Napoleon centres `N₀`, `N₁` are distinct (real parts `2 + √3/2` and `-√3/2`), so the Napoleon
triangle is non-degenerate; the common point `F` of the three lines exists, sees the sides under
`2π/3`, and is distinct from the three vertices. -/
theorem l14w_napoleon : ∃ t : Triangle ℝ ℂ, ∃ A' B' C' : ℂ,
    t.points = ![0, 4, 3 * Complex.I] ∧
    A' = ((2 + 3 * √3 / 2 : ℝ) : ℂ) + ((3 / 2 + 2 * √3 : ℝ) : ℂ) * Complex.I ∧
    B' = ((-(3 * √3 / 2) : ℝ) : ℂ) + ((3 / 2 : ℝ) : ℂ) * Complex.I ∧
    C' = ((2 : ℝ) : ℂ) + ((-(2 * √3) : ℝ) : ℂ) * Complex.I ∧
    A' = ((1 / 2 : ℝ) • (t.points 2 -ᵥ t.points 1) -
        ((if 0 < Complex.orientation.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (t.points 2 -ᵥ t.points 1)) +ᵥ t.points 1 ∧
    B' = ((1 / 2 : ℝ) • (t.points 0 -ᵥ t.points 2) -
        ((if 0 < Complex.orientation.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (t.points 0 -ᵥ t.points 2)) +ᵥ t.points 2 ∧
    C' = ((1 / 2 : ℝ) • (t.points 1 -ᵥ t.points 0) -
        ((if 0 < Complex.orientation.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (t.points 1 -ᵥ t.points 0)) +ᵥ t.points 0 ∧
    A' ≠ B' ∧ B' ≠ C' ∧ C' ≠ A' ∧
    A' ≠ t.points 0 ∧ B' ≠ t.points 1 ∧ C' ≠ t.points 2 ∧
    ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3 ∧
    ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3 ∧
    ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3 ∧
    Finset.univ.centroid ℝ ![t.points 1, t.points 2, A'] ≠
      Finset.univ.centroid ℝ ![t.points 2, t.points 0, B'] ∧
    ∃ F : ℂ, F ∈ line[ℝ, t.points 0, A'] ∧ F ∈ line[ℝ, t.points 1, B'] ∧
      F ∈ line[ℝ, t.points 2, C'] ∧
      ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧ ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3 ∧
      F ≠ t.points 0 ∧ F ≠ t.points 1 ∧ F ≠ t.points 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3p : 0 < √3 := by positivity
  have hs := l14T_sign
  have eA : ((2 + 3 * √3 / 2 : ℝ) : ℂ) + ((3 / 2 + 2 * √3 : ℝ) : ℂ) * Complex.I =
      ((1 / 2 : ℝ) • (l14T.points 2 -ᵥ l14T.points 1) -
        ((if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (l14T.points 2 -ᵥ l14T.points 1)) +ᵥ l14T.points 1 := by
    rw [hs]; apply Complex.ext <;> simp [l14T] <;> ring
  have eB : ((-(3 * √3 / 2) : ℝ) : ℂ) + ((3 / 2 : ℝ) : ℂ) * Complex.I =
      ((1 / 2 : ℝ) • (l14T.points 0 -ᵥ l14T.points 2) -
        ((if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (l14T.points 0 -ᵥ l14T.points 2)) +ᵥ l14T.points 2 := by
    rw [hs]; apply Complex.ext <;> simp [l14T] <;> ring
  have eC : ((2 : ℝ) : ℂ) + ((-(2 * √3) : ℝ) : ℂ) * Complex.I =
      ((1 / 2 : ℝ) • (l14T.points 1 -ᵥ l14T.points 0) -
        ((if 0 < Complex.orientation.areaForm (l14T.points 1 -ᵥ l14T.points 0) (l14T.points 2 -ᵥ l14T.points 0) then (1 : ℝ) else -1) * (√3 / 2)) •
          Complex.orientation.rightAngleRotation (l14T.points 1 -ᵥ l14T.points 0)) +ᵥ l14T.points 0 := by
    rw [hs]; apply Complex.ext <;> simp [l14T] <;> ring
  have hA : ∠ (l14T.points 1) (l14T.points 0) (l14T.points 2) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, Complex.inner])
  have hB : ∠ (l14T.points 2) (l14T.points 1) (l14T.points 0) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, Complex.inner])
  have hC : ∠ (l14T.points 0) (l14T.points 2) (l14T.points 1) < 2 * π / 3 :=
    l14_angle_lt (by simp [l14T, Complex.inner])
  obtain ⟨F, hFA, hFB, hFC⟩ := l14_napoleon_concurrent Complex.orientation l14T _ _ _ eA eB eC
  obtain ⟨f1, f2, f3, -⟩ :=
    l14_napoleon_fermat Complex.orientation l14T _ _ _ eA eB eC hA hB hC F hFA hFB
  refine ⟨l14T, _, _, _, rfl, rfl, rfl, rfl, eA, eB, eC, ?_, ?_, ?_, ?_, ?_, ?_, hA, hB, hC, ?_,
    F, hFA, hFB, hFC, f1, f2, f3, l14_ne_of_angle f1, l14_ne_of_angle f2, l14_ne_of_angle f3⟩
  · apply l14_ne; left; simp; nlinarith
  · apply l14_ne; left; simp; nlinarith
  · apply l14_ne; left; simp
  · apply l14_ne; left; simp [l14T]; nlinarith
  · apply l14_ne; left; simp [l14T]; nlinarith
  · apply l14_ne; right; simp [l14T]; nlinarith
  · rw [l14_centroid, l14_centroid]
    apply l14_ne; left; simp [l14T]; nlinarith

/-- Ptolemy equality, cyclic case: the rectangle `A = 0`, `B = 4`, `C = 4 + 3i`, `D = 3i`
(circumcentre `2 + 3/2 i`, radius `5/2`, diagonals crossing at the centre); the four points are
pairwise distinct and not collinear, and `5 · 5 = 4 · 4 + 3 · 3`. -/
theorem l14w_ptolemy_cyclic : ∃ A B C D : ℂ,
    A = 0 ∧ B = 4 ∧ C = 4 + 3 * Complex.I ∧ D = 3 * Complex.I ∧
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    Cospherical ({A, B, C, D} : Set ℂ) ∧ (∃ X : ℂ, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧
    ¬ Collinear ℝ ({A, B, C, D} : Set ℂ) ∧
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D := by
  have hAB : (0 : ℂ) ≠ 4 := l14_ne _ _ (by simp)
  have hAC : (0 : ℂ) ≠ 4 + 3 * Complex.I := l14_ne _ _ (by simp)
  have hAD : (0 : ℂ) ≠ 3 * Complex.I := l14_ne _ _ (by simp)
  have hBC : (4 : ℂ) ≠ 4 + 3 * Complex.I := l14_ne _ _ (by simp)
  have hBD : (4 : ℂ) ≠ 3 * Complex.I := l14_ne _ _ (by simp)
  have hCD : (4 + 3 * Complex.I : ℂ) ≠ 3 * Complex.I := l14_ne _ _ (by simp)
  have hcos : Cospherical ({(0 : ℂ), 4, 4 + 3 * Complex.I, 3 * Complex.I} : Set ℂ) := by
    refine ⟨(2 : ℂ) + (3 / 2 : ℝ) * Complex.I, 5 / 2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl | rfl) <;> exact l14_dist _ _ _ (by norm_num) (by simp <;> norm_num)
  have hX : ∃ X : ℂ, Sbtw ℝ 0 X (4 + 3 * Complex.I) ∧ Sbtw ℝ 4 X (3 * Complex.I) :=
    ⟨(2 : ℂ) + (3 / 2 : ℝ) * Complex.I, l14_sbtw _ _ _ hAC (by norm_num) (by norm_num),
      l14_sbtw _ _ _ hBD (by norm_num) (by norm_num)⟩
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, hAB, hAC, hAD, hBC, hBD, hCD, hcos, hX, ?_,
    (l14_ptolemy_eq_iff hAB hAC hAD hBC hBD hCD).2 (Or.inl ⟨hcos, hX⟩)⟩
  intro hc
  exact l14_not_collinear 0 4 (3 * Complex.I) (by simp)
    (hc.subset (by intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto))

/-- Ptolemy equality, collinear case: `A = 0`, `B = 1`, `C = 2`, `D = 3` on the real axis
(pairwise distinct, `B` strictly between `A, C` and `C` strictly between `B, D`;
`2 · 2 = 1 · 1 + 1 · 3`). -/
theorem l14w_ptolemy_collinear : ∃ A B C D : ℂ,
    A = 0 ∧ B = 1 ∧ C = 2 ∧ D = 3 ∧
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    Collinear ℝ ({A, B, C, D} : Set ℂ) ∧ Sbtw ℝ A B C ∧ Sbtw ℝ B C D ∧
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D := by
  have hAB : (0 : ℂ) ≠ 1 := l14_ne _ _ (by simp)
  have hAC : (0 : ℂ) ≠ 2 := l14_ne _ _ (by simp)
  have hAD : (0 : ℂ) ≠ 3 := l14_ne _ _ (by simp)
  have hBC : (1 : ℂ) ≠ 2 := l14_ne _ _ (by norm_num)
  have hBD : (1 : ℂ) ≠ 3 := l14_ne _ _ (by norm_num)
  have hCD : (2 : ℂ) ≠ 3 := l14_ne _ _ (by norm_num)
  have hcol : Collinear ℝ ({(0 : ℂ), 1, 2, 3} : Set ℂ) := by
    rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    refine ⟨1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro p (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
  have h1 : Sbtw ℝ (0 : ℂ) 1 2 := l14_sbtw _ _ _ hAC (by simp) (by simp)
  have h2 : Sbtw ℝ (1 : ℂ) 2 3 := l14_sbtw _ _ _ hBD (by norm_num) (by simp)
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, hAB, hAC, hAD, hBC, hBD, hCD, hcol, h1, h2,
    (l14_ptolemy_collinear hAB hAC hAD hBC hBD hCD hcol).2 ⟨Or.inl h1, Or.inr h2⟩⟩

/-- Witness for `ptolemy_real`: `0, 1, 2, 3` satisfy both sides, while `0, 1, 3, 2` (also
pairwise distinct) satisfy neither (`3 ≠ 1 + 4`), so the equivalence is not trivially true. -/
theorem l14w_ptolemy_real :
    ((Sbtw ℝ (0 : ℝ) 1 2 ∨ Sbtw ℝ (0 : ℝ) 3 2) ∧ (Sbtw ℝ (1 : ℝ) 0 3 ∨ Sbtw ℝ (1 : ℝ) 2 3)) ∧
    |(0 : ℝ) - 2| * |1 - 3| = |(0 : ℝ) - 1| * |2 - 3| + |(1 : ℝ) - 2| * |0 - 3| ∧
    ¬ ((Sbtw ℝ (0 : ℝ) 1 3 ∨ Sbtw ℝ (0 : ℝ) 2 3) ∧ (Sbtw ℝ (1 : ℝ) 0 2 ∨ Sbtw ℝ (1 : ℝ) 3 2)) ∧
    |(0 : ℝ) - 3| * |1 - 2| ≠ |(0 : ℝ) - 1| * |3 - 2| + |(1 : ℝ) - 3| * |0 - 2| := by
  have e1 : |(0 : ℝ) - 2| * |1 - 3| = |(0 : ℝ) - 1| * |2 - 3| + |(1 : ℝ) - 2| * |0 - 3| := by
    norm_num [abs_of_neg, abs_of_pos]
  have e2 : |(0 : ℝ) - 3| * |1 - 2| ≠ |(0 : ℝ) - 1| * |3 - 2| + |(1 : ℝ) - 3| * |0 - 2| := by
    norm_num [abs_of_neg, abs_of_pos]
  refine ⟨(l14_ptolemy_real (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).1 e1, e1, fun h => e2 ((l14_ptolemy_real (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 h), e2⟩

end FermatNapoleon
