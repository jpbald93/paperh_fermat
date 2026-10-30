import FermatNapoleon.Basic
import FermatNapoleon.Lemmas
import FermatNapoleon.Bridges
import FermatNapoleon.Ptolemy
import FermatNapoleon.Main
import FermatNapoleon.L14

/-!
# Layer 13: blind restatement (FermatNapoleon)

An independent writer, who saw only the plain-English text of the paper and not this library,
formalised its theorem statements in a separate file, `PaperHBlind.lean`
(sha256 begins e257c271479a928f). This file copies that file's `Blind*` definitions verbatim
(inside the namespace `FermatNapoleon.Blind`) and each blind statement verbatim as `blindK_stmt`.
For each statement it proves `rb_K` (library theorem → blind statement) and `br_K` (blind
statement → library theorem). Where the paper's statement was split by the blind writer into
several parts, the reverse direction is proved jointly (e.g. `br_456`). The `agree_*` lemmas
identify the blind definitions with the library's. No proof uses a library theorem other than
the one being compared and the definition-level agreement lemmas.
-/

universe u v

namespace FermatNapoleon.Blind
open EuclideanGeometry Real

noncomputable section

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Semiperimeter `s = (a+b+c)/2`. -/
def BlindSemiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 1) (t.points 2) + dist (t.points 2) (t.points 0) +
    dist (t.points 0) (t.points 1)) / 2

/-- Area `Δ = ½ |AB| |AC| sin ∠BAC`. -/
def BlindArea (t : Affine.Triangle ℝ P) : ℝ :=
  1 / 2 * dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
    Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))

/-- Heron's polynomial `Γ(a,b,c) = ¼(2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴)` (auxiliary definition). -/
def BlindHeronGamma (a b c : ℝ) : ℝ :=
  1 / 4 * (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4)

/-- "Equilateral" is `|AB| = |BC| ∧ |BC| = |CA|`. -/
def BlindEquilateral (t : Affine.Triangle ℝ P) : Prop :=
  dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) ∧
    dist (t.points 1) (t.points 2) = dist (t.points 2) (t.points 0)

/-- `X` is in the closed triangle: `X = w₀A + w₁B + w₂C` with all `wᵢ ≥ 0`, `∑ wᵢ = 1`. -/
def BlindInClosedTriangle (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- `X` is strictly inside the triangle: as above with all `wᵢ > 0`. -/
def BlindStrictlyInside (t : Affine.Triangle ℝ P) (X : P) : Prop :=
  ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
    X = Finset.univ.affineCombination ℝ t.points w

/-- Distance from `X` to the line `YZ`: `|X π_{YZ}(X)|`, `π_{YZ}` the orthogonal projection. -/
def BlindDistToLine (X Y Z : P) : ℝ :=
  dist X (EuclideanGeometry.orthogonalProjection line[ℝ, Y, Z] X : P)

/-! ### Oriented plane setting (Section "Fermat and Napoleon") -/

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Orientation sign `σ ∈ {1,-1}` of `t`: `σ = 1` iff `ω(B-A, C-A) > 0`. -/
def BlindOrientationSign (t : Affine.Triangle ℝ P) : ℝ :=
  if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then 1 else -1

/-- Outer apex on `XY`: the image of `Y` under the rotation about `X` by `-σπ/3`. -/
def BlindOuterApex (t : Affine.Triangle ℝ P) (X Y : P) : P :=
  o.rotation ((-(BlindOrientationSign o t * π / 3) : ℝ) : Real.Angle) (Y -ᵥ X) +ᵥ X

/-- `A'`: outer apex on `BC`. -/
def BlindApexA (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 1) (t.points 2)
/-- `B'`: outer apex on `CA`. -/
def BlindApexB (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 2) (t.points 0)
/-- `C'`: outer apex on `AB`. -/
def BlindApexC (t : Affine.Triangle ℝ P) : P := BlindOuterApex o t (t.points 0) (t.points 1)

/-- `N_A`: centroid of `B C A'`. -/
def BlindNapoleonA (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 1, t.points 2, BlindApexA o t]
/-- `N_B`: centroid of `C A B'`. -/
def BlindNapoleonB (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 2, t.points 0, BlindApexB o t]
/-- `N_C`: centroid of `A B C'`. -/
def BlindNapoleonC (t : Affine.Triangle ℝ P) : P :=
  Finset.univ.centroid ℝ ![t.points 0, t.points 1, BlindApexC o t]

end Oriented

end -- noncomputable section

open EuclideanGeometry Real

/-! ### Agreement lemmas (Blind ↔ repository) -/

section AgreeOriented
variable {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

theorem agree_sign (t : Affine.Triangle ℝ P) :
    BlindOrientationSign o t = FermatNapoleon.triSign o t := rfl

theorem agree_outerApex (t : Affine.Triangle ℝ P) (X Y : P) :
    BlindOuterApex o t X Y = FermatNapoleon.outerApex o t X Y := by
  unfold BlindOuterApex FermatNapoleon.outerApex
  rw [agree_sign, mul_div_assoc]

theorem agree_apexA (t : Affine.Triangle ℝ P) : BlindApexA o t = FermatNapoleon.napoleonApex o t 0 :=
  agree_outerApex o t _ _
theorem agree_apexB (t : Affine.Triangle ℝ P) : BlindApexB o t = FermatNapoleon.napoleonApex o t 1 :=
  agree_outerApex o t _ _
theorem agree_apexC (t : Affine.Triangle ℝ P) : BlindApexC o t = FermatNapoleon.napoleonApex o t 2 :=
  agree_outerApex o t _ _

theorem agree_centerA (t : Affine.Triangle ℝ P) :
    BlindNapoleonA o t = FermatNapoleon.napoleonCenter o t 0 := by
  unfold BlindNapoleonA FermatNapoleon.napoleonCenter; rw [agree_apexA]; rfl
theorem agree_centerB (t : Affine.Triangle ℝ P) :
    BlindNapoleonB o t = FermatNapoleon.napoleonCenter o t 1 := by
  unfold BlindNapoleonB FermatNapoleon.napoleonCenter; rw [agree_apexB]; rfl
theorem agree_centerC (t : Affine.Triangle ℝ P) :
    BlindNapoleonC o t = FermatNapoleon.napoleonCenter o t 2 := by
  unfold BlindNapoleonC FermatNapoleon.napoleonCenter; rw [agree_apexC]; rfl

omit [Fact (Module.finrank ℝ V = 2)] in
/-- Mathlib's `Simplex.centroid` is the blind `Finset.univ.centroid ℝ t.points`. -/
theorem agree_centroid (t : Affine.Triangle ℝ P) : t.centroid = Finset.univ.centroid ℝ t.points := rfl

end AgreeOriented

section AgreePtolemy
variable {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- On the real line: the repository's rendering of the "eight orders" equals the blind one. -/
theorem agree_orders_real {a b c d : ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ((Sbtw ℝ a b c ∨ Sbtw ℝ a d c) ∧ (Sbtw ℝ b a d ∨ Sbtw ℝ b c d)) ↔
      ((Sbtw ℝ a b c ∧ Sbtw ℝ b c d) ∨ (Sbtw ℝ b c d ∧ Sbtw ℝ c d a) ∨
          (Sbtw ℝ c d a ∧ Sbtw ℝ d a b) ∨ (Sbtw ℝ d a b ∧ Sbtw ℝ a b c) ∨
          (Sbtw ℝ d c b ∧ Sbtw ℝ c b a) ∨ (Sbtw ℝ a d c ∧ Sbtw ℝ d c b) ∨
          (Sbtw ℝ b a d ∧ Sbtw ℝ a d c) ∨ (Sbtw ℝ c b a ∧ Sbtw ℝ b a d)) := by
  simp only [FermatNapoleon.sbtw_real]
  rcases hab.lt_or_gt with h1 | h1 <;> rcases hac.lt_or_gt with h2 | h2 <;>
    rcases had.lt_or_gt with h3 | h3 <;> rcases hbc.lt_or_gt with h4 | h4 <;>
    rcases hbd.lt_or_gt with h5 | h5 <;> rcases hcd.lt_or_gt with h6 | h6
  all_goals first
    | (exfalso; linarith)
    | (have n1 := not_lt.2 h1.le; have n2 := not_lt.2 h2.le; have n3 := not_lt.2 h3.le
       have n4 := not_lt.2 h4.le; have n5 := not_lt.2 h5.le; have n6 := not_lt.2 h6.le
       simp [h1, h3, h4, h6, n1, n3, n4, n6])

/-- For four distinct collinear points: repository order condition ↔ blind order condition
(transport along `lineMap A C`, as in the repository's `ptolemy_collinear`). -/
theorem agree_orders {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D) (hcol : Collinear ℝ ({A, B, C, D} : Set P)) :
    ((Sbtw ℝ A B C ∨ Sbtw ℝ A D C) ∧ (Sbtw ℝ B A D ∨ Sbtw ℝ B C D)) ↔
      ((Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
          (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C) ∨
          (Sbtw ℝ D C B ∧ Sbtw ℝ C B A) ∨ (Sbtw ℝ A D C ∧ Sbtw ℝ D C B) ∨
          (Sbtw ℝ B A D ∧ Sbtw ℝ A D C) ∨ (Sbtw ℝ C B A ∧ Sbtw ℝ B A D)) := by
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
  have n3 : (0 : ℝ) ≠ δ := fun h => hAD (by rw [eA, eD, h])
  have n4 : β ≠ 1 := fun h => hBC (by rw [eB, eC, h])
  have n5 : β ≠ δ := fun h => hBD (by rw [eB, eD, h])
  have n6 : (1 : ℝ) ≠ δ := fun h => hCD (by rw [eC, eD, h])
  rw [eA, eB, eC, eD]
  simp only [hi.sbtw_map_iff]
  exact agree_orders_real n1 zero_ne_one n3 n4 n5 n6

end AgreePtolemy

-- verbatim from blind_28
def blind28_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P]
    (A B C D : P) (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C)
    (hBD : B ≠ D) (hCD : C ≠ D),
    dist A C * dist B D = dist A B * dist C D + dist B C * dist A D ↔
      (Cospherical ({A, B, C, D} : Set P) ∧ ∃ X : P, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∨
      (Collinear ℝ ({A, B, C, D} : Set P) ∧
        ((Sbtw ℝ A B C ∧ Sbtw ℝ B C D) ∨ (Sbtw ℝ B C D ∧ Sbtw ℝ C D A) ∨
          (Sbtw ℝ C D A ∧ Sbtw ℝ D A B) ∨ (Sbtw ℝ D A B ∧ Sbtw ℝ A B C) ∨
          (Sbtw ℝ D C B ∧ Sbtw ℝ C B A) ∨ (Sbtw ℝ A D C ∧ Sbtw ℝ D C B) ∨
          (Sbtw ℝ B A D ∧ Sbtw ℝ A D C) ∨ (Sbtw ℝ C B A ∧ Sbtw ℝ B A D)))

-- verbatim from blind_37
def blind37_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    (line[ℝ, t.points 1, t.points 2]).SOppSide (t.points 0) (BlindApexA o t)

-- verbatim from blind_38
def blind38_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    (line[ℝ, t.points 2, t.points 0]).SOppSide (t.points 1) (BlindApexB o t)

-- verbatim from blind_39
def blind39_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    (line[ℝ, t.points 0, t.points 1]).SOppSide (t.points 2) (BlindApexC o t)

-- verbatim from blind_40
def blind40_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    dist (t.points 0) (BlindApexA o t) = dist (t.points 1) (BlindApexB o t)

-- verbatim from blind_41
def blind41_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    dist (t.points 1) (BlindApexB o t) = dist (t.points 2) (BlindApexC o t)

-- verbatim from blind_42
def blind42_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    ∃ F : P, F ∈ line[ℝ, t.points 0, BlindApexA o t] ∧ F ∈ line[ℝ, t.points 1, BlindApexB o t] ∧
      F ∈ line[ℝ, t.points 2, BlindApexC o t]

-- verbatim from blind_43
def blind43_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) (F : P)
    (hFA : F ∈ line[ℝ, t.points 0, BlindApexA o t]) (hFB : F ∈ line[ℝ, t.points 1, BlindApexB o t]),
    ∠ (t.points 0) F (t.points 1) = 2 * π / 3 ∧ ∠ (t.points 1) F (t.points 2) = 2 * π / 3 ∧
      ∠ (t.points 2) F (t.points 0) = 2 * π / 3

-- verbatim from blind_44
def blind44_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P)
    (hA : ∠ (t.points 1) (t.points 0) (t.points 2) < 2 * π / 3)
    (hB : ∠ (t.points 2) (t.points 1) (t.points 0) < 2 * π / 3)
    (hC : ∠ (t.points 0) (t.points 2) (t.points 1) < 2 * π / 3) (F : P)
    (hFA : F ∈ line[ℝ, t.points 0, BlindApexA o t]) (hFB : F ∈ line[ℝ, t.points 1, BlindApexB o t]),
    dist (t.points 0) (BlindApexA o t) =
      dist F (t.points 0) + dist F (t.points 1) + dist F (t.points 2)

-- verbatim from blind_45
def blind45_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    InnerProductGeometry.angle (BlindApexA o t -ᵥ t.points 0) (BlindApexB o t -ᵥ t.points 1) =
      2 * π / 3

-- verbatim from blind_46
def blind46_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    InnerProductGeometry.angle (BlindApexB o t -ᵥ t.points 1) (BlindApexC o t -ᵥ t.points 2) =
      2 * π / 3

-- verbatim from blind_47
def blind47_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    InnerProductGeometry.angle (BlindApexC o t -ᵥ t.points 2) (BlindApexA o t -ᵥ t.points 0) =
      2 * π / 3

-- verbatim from blind_48
def blind48_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    dist (BlindNapoleonA o t) (BlindNapoleonB o t) =
      dist (BlindNapoleonB o t) (BlindNapoleonC o t)

-- verbatim from blind_49
def blind49_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    dist (BlindNapoleonB o t) (BlindNapoleonC o t) =
      dist (BlindNapoleonC o t) (BlindNapoleonA o t)

-- verbatim from blind_50
def blind50_stmt : Prop :=
  ∀ {V : Type u} {P : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (t : Affine.Triangle ℝ P),
    Finset.univ.centroid ℝ ![BlindNapoleonA o t, BlindNapoleonB o t, BlindNapoleonC o t] =
      Finset.univ.centroid ℝ t.points

/-! ### Comparisons -/

-- blind_28 ↔ ptolemy_eq_iff
theorem rb_28 : (type_of% @FermatNapoleon.ptolemy_eq_iff.{u, v}) → blind28_stmt.{u, v} := by
  intro h V P _ _ _ _ A B C D hAB hAC hAD hBC hBD hCD
  rw [h hAB hAC hAD hBC hBD hCD]
  constructor
  · rintro (h1 | ⟨hc, ho⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨hc, (agree_orders hAB hAC hAD hBC hBD hCD hc).1 ho⟩
  · rintro (h1 | ⟨hc, ho⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨hc, (agree_orders hAB hAC hAD hBC hBD hCD hc).2 ho⟩

theorem br_28 : blind28_stmt.{u, v} → (type_of% @FermatNapoleon.ptolemy_eq_iff.{u, v}) := by
  intro h V P _ _ _ _ A B C D hAB hAC hAD hBC hBD hCD
  rw [h A B C D hAB hAC hAD hBC hBD hCD]
  constructor
  · rintro (h1 | ⟨hc, ho⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨hc, (agree_orders hAB hAC hAD hBC hBD hCD hc).2 ho⟩
  · rintro (h1 | ⟨hc, ho⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨hc, (agree_orders hAB hAC hAD hBC hBD hCD hc).1 ho⟩

-- blind_37, 38, 39 ↔ apex_outward (∀ i : Fin 3); B→R needs all three blind items jointly
theorem rb_37 : (type_of% @FermatNapoleon.apex_outward.{u, v}) → blind37_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexA]; exact h o t 0

theorem rb_38 : (type_of% @FermatNapoleon.apex_outward.{u, v}) → blind38_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexB]; exact h o t 1

theorem rb_39 : (type_of% @FermatNapoleon.apex_outward.{u, v}) → blind39_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexC]; exact h o t 2

theorem br_37_38_39 : blind37_stmt.{u, v} ∧ blind38_stmt.{u, v} ∧ blind39_stmt.{u, v} →
    (type_of% @FermatNapoleon.apex_outward.{u, v}) := by
  rintro ⟨h0, h1, h2⟩ V P _ _ _ _ _ o t i
  fin_cases i
  · have := h0 o t; rw [agree_apexA] at this; exact this
  · have := h1 o t; rw [agree_apexB] at this; exact this
  · have := h2 o t; rw [agree_apexC] at this; exact this

-- blind_40, 41 ↔ napoleon_dist_eq
theorem rb_40 : (type_of% @FermatNapoleon.napoleon_dist_eq.{u, v}) → blind40_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexA, agree_apexB]; exact (h o t).1

theorem rb_41 : (type_of% @FermatNapoleon.napoleon_dist_eq.{u, v}) → blind41_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexB, agree_apexC]; exact (h o t).2

theorem br_40_41 : blind40_stmt.{u, v} ∧ blind41_stmt.{u, v} →
    (type_of% @FermatNapoleon.napoleon_dist_eq.{u, v}) := by
  rintro ⟨h0, h1⟩ V P _ _ _ _ _ o t
  have a := h0 o t; have b := h1 o t
  rw [agree_apexA, agree_apexB] at a; rw [agree_apexB, agree_apexC] at b
  exact ⟨a, b⟩

-- blind_42 ↔ napoleon_concurrent
theorem rb_42 : (type_of% @FermatNapoleon.napoleon_concurrent.{u, v}) → blind42_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexA, agree_apexB, agree_apexC]; exact h o t

theorem br_42 : blind42_stmt.{u, v} → (type_of% @FermatNapoleon.napoleon_concurrent.{u, v}) := by
  intro h V P _ _ _ _ _ o t
  have := h o t; rw [agree_apexA, agree_apexB, agree_apexC] at this; exact this

-- blind_43, 44 ↔ napoleon_fermat
theorem rb_43 : (type_of% @FermatNapoleon.napoleon_fermat.{u, v}) → blind43_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t hA hB hC F hFA hFB
  rw [agree_apexA] at hFA; rw [agree_apexB] at hFB
  obtain ⟨a, b, c, -⟩ := h o t hA hB hC F hFA hFB
  exact ⟨a, b, c⟩

theorem rb_44 : (type_of% @FermatNapoleon.napoleon_fermat.{u, v}) → blind44_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t hA hB hC F hFA hFB
  rw [agree_apexA] at hFA ⊢; rw [agree_apexB] at hFB
  exact (h o t hA hB hC F hFA hFB).2.2.2

theorem br_43_44 : blind43_stmt.{u, v} ∧ blind44_stmt.{u, v} →
    (type_of% @FermatNapoleon.napoleon_fermat.{u, v}) := by
  rintro ⟨h0, h1⟩ V P _ _ _ _ _ o t hA hB hC F hFA hFB
  rw [← agree_apexA] at hFA ⊢; rw [← agree_apexB] at hFB
  obtain ⟨a, b, c⟩ := h0 o t hA hB hC F hFA hFB
  exact ⟨a, b, c, h1 o t hA hB hC F hFA hFB⟩

-- blind_45, 46, 47 ↔ napoleon_angle (4 conjuncts; the 4th, the line angle π/3, follows from
-- blind_45 by `InnerProductGeometry.angle_neg_right`)
theorem rb_45 : (type_of% @FermatNapoleon.napoleon_angle.{u, v}) → blind45_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexA, agree_apexB]; exact (h o t).1

theorem rb_46 : (type_of% @FermatNapoleon.napoleon_angle.{u, v}) → blind46_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexB, agree_apexC]; exact (h o t).2.1

theorem rb_47 : (type_of% @FermatNapoleon.napoleon_angle.{u, v}) → blind47_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_apexC, agree_apexA]; exact (h o t).2.2.1

theorem br_45_46_47 : blind45_stmt.{u, v} ∧ blind46_stmt.{u, v} ∧ blind47_stmt.{u, v} →
    (type_of% @FermatNapoleon.napoleon_angle.{u, v}) := by
  rintro ⟨h0, h1, h2⟩ V P _ _ _ _ _ o t
  have a := h0 o t; have b := h1 o t; have c := h2 o t
  rw [agree_apexA, agree_apexB] at a; rw [agree_apexB, agree_apexC] at b
  rw [agree_apexC, agree_apexA] at c
  refine ⟨a, b, c, ?_⟩
  rw [show t.points 1 -ᵥ FermatNapoleon.napoleonApex o t 1 =
      -(FermatNapoleon.napoleonApex o t 1 -ᵥ t.points 1) from (neg_vsub_eq_vsub_rev _ _).symm,
    InnerProductGeometry.angle_neg_right, a]
  ring

-- blind_48, 49, 50 ↔ napoleon
theorem rb_48 : (type_of% @FermatNapoleon.napoleon.{u, v}) → blind48_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_centerA, agree_centerB, agree_centerC]; exact (h o t).1

theorem rb_49 : (type_of% @FermatNapoleon.napoleon.{u, v}) → blind49_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_centerA, agree_centerB, agree_centerC]; exact (h o t).2.1

theorem rb_50 : (type_of% @FermatNapoleon.napoleon.{u, v}) → blind50_stmt.{u, v} := by
  intro h V P _ _ _ _ _ o t
  rw [agree_centerA, agree_centerB, agree_centerC, ← agree_centroid]; exact (h o t).2.2

theorem br_48_49_50 : blind48_stmt.{u, v} ∧ blind49_stmt.{u, v} ∧ blind50_stmt.{u, v} →
    (type_of% @FermatNapoleon.napoleon.{u, v}) := by
  rintro ⟨h0, h1, h2⟩ V P _ _ _ _ _ o t
  have a := h0 o t; have b := h1 o t; have c := h2 o t
  rw [agree_centerA, agree_centerB, agree_centerC] at a b c
  rw [← agree_centroid] at c
  exact ⟨a, b, c⟩

end FermatNapoleon.Blind
