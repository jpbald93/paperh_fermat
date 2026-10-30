import Mathlib

/-!
# Definitions for the Fermat–Napoleon configuration

The plane is a two-dimensional real inner product space `V` (`Fact (finrank ℝ V = 2)`), with an
orientation `o`, acting on a Euclidean affine plane `P`. For a triangle `t` with vertices
`A, B, C = t.points 0, 1, 2`:

* `triSign o t` is `1` if `t` is positively oriented w.r.t. `o` (`ω(B - A, C - A) > 0`) and `-1`
  otherwise;
* `outerApex o t X Y` rotates `Y - X` about `X` by `-triSign o t · π/3` (Mathlib's
  `Orientation.rotation`); for a side `XY` traversed in the orientation of `t` this is the apex of
  the equilateral triangle erected *outward* on `XY` (see `FermatNapoleon.apex_outward`);
* `napoleonApex o t i` is that apex on the side opposite to vertex `i`, i.e. `A'`, `B'`, `C'` for
  `i = 0, 1, 2`;
* `napoleonCenter o t i` is the centre (centroid) of the `i`-th outer equilateral triangle.
-/

open Affine EuclideanGeometry Module
open scoped RealInnerProductSpace Real

namespace FermatNapoleon

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Orientation sign of a triangle: `1` if `ω(B - A, C - A) > 0`, else `-1`. -/
noncomputable def triSign (t : Triangle ℝ P) : ℝ :=
  if 0 < o.areaForm (t.points 1 -ᵥ t.points 0) (t.points 2 -ᵥ t.points 0) then 1 else -1

/-- The image of `Y` under the rotation about `X` by `-triSign o t · π/3`. -/
noncomputable def outerApex (t : Triangle ℝ P) (X Y : P) : P :=
  o.rotation ((-(triSign o t * (π / 3)) : ℝ) : Real.Angle) (Y -ᵥ X) +ᵥ X

/-- Apex of the outer equilateral triangle on the side opposite to vertex `i`. -/
noncomputable def napoleonApex (t : Triangle ℝ P) (i : Fin 3) : P :=
  outerApex o t (t.points (i + 1)) (t.points (i + 2))

/-- Centre of the outer equilateral triangle on the side opposite to vertex `i`. -/
noncomputable def napoleonCenter (t : Triangle ℝ P) (i : Fin 3) : P :=
  Finset.univ.centroid ℝ ![t.points (i + 1), t.points (i + 2), napoleonApex o t i]

end FermatNapoleon
