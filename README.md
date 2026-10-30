# Ptolemy equality and the Fermat–Napoleon configuration in Lean 4 / Mathlib

**Paper:** J. Bald, *Classical triangle inequalities and the Fermat–Napoleon configuration in Lean 4* (2026). Companion repositories: https://github.com/jpbald93/paperh_euler, https://github.com/jpbald93/paperh_mordell.

**Toolchain:** Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (see `lake-manifest.json`).
**Check:** `lake build && bash gate.sh`, then `bash tests/tamper.sh`. **Licence:** Apache-2.0.

Library: `FermatNapoleon`
(Mathlib pinned via `lake-manifest.json`, toolchain in `lean-toolchain`).

## Setting
* H4.1 holds in any real inner product space `V` with Euclidean affine space `P`.
* H4.2–H4.4 are planar: `[Fact (finrank ℝ V = 2)]` and an orientation `o : Orientation ℝ V (Fin 2)`.
  The triangle is `t : Affine.Triangle ℝ P`, with `A, B, C = t.points 0, 1, 2`.
* `FermatNapoleon.triSign o t` is `1` when `t` is positively oriented (`ω(B−A, C−A) > 0`) and `−1`
  otherwise. `outerApex o t X Y` is `Y` rotated about `X` by `−triSign·π/3` (Mathlib's
  `Orientation.rotation`). `napoleonApex o t i` is the apex on the side opposite vertex `i`
  (`A' = rot_B(C)`, `B' = rot_C(A)`, `C' = rot_A(B)`). `napoleonCenter o t i` is the centroid of
  that equilateral triangle. Because the rotation sign follows the orientation of `t`, the apexes
  are *outward*, which is proved as `apex_outward`.

## Main results
| Statement (plain English) | Lean name | Location |
|---|---|---|
| H4.1: for distinct `A,B,C,D`: `AC·BD = AB·CD + BC·AD` iff (the points are cospherical and the open segments `AC`, `BD` meet) or (they are collinear, `B` or `D` lies strictly between `A` and `C`, and `A` or `C` lies strictly between `B` and `D`; these are the orders ABCD, BCDA, CDAB, DABC and their reversals) | `FermatNapoleon.ptolemy_eq_iff` | FermatNapoleon/Ptolemy.lean:238 |
| The collinear case for four reals | `FermatNapoleon.ptolemy_real` | FermatNapoleon/Ptolemy.lean:51 |
| The collinear case for points | `FermatNapoleon.ptolemy_collinear` | FermatNapoleon/Ptolemy.lean:71 |
| The apexes are outward: `A` and `A'` lie strictly on opposite sides of line `BC` (likewise for `B'`, `C'`) | `FermatNapoleon.apex_outward` | FermatNapoleon/Main.lean:20 |
| H4.2 (i): `AA' = BB' = CC'` | `FermatNapoleon.napoleon_dist_eq` | FermatNapoleon/Main.lean:63 |
| H4.2 (ii): the lines `AA'`, `BB'`, `CC'` have a common point | `FermatNapoleon.napoleon_concurrent` | FermatNapoleon/Main.lean:99 |
| H4.2 (iii): if all angles are `< 2π/3`, any `F` on both `AA'` and `BB'` satisfies `∠AFB = ∠BFC = ∠CFA = 2π/3` and `AA' = FA + FB + FC` | `FermatNapoleon.napoleon_fermat` | FermatNapoleon/Main.lean:111 |
| H4.3 (Napoleon): the outer centres form an equilateral triangle whose centroid is `t.centroid` | `FermatNapoleon.napoleon` | FermatNapoleon/Main.lean:222 |
| H4.4: the vectors `A'−A`, `B'−B`, `C'−C` pairwise make the angle `2π/3`, so the lines make the angle `π/3` | `FermatNapoleon.napoleon_angle` | FermatNapoleon/Main.lean:258 |

## Method
* **Ptolemy.** Mathlib already has the inequality (`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`) and the cospherical equality (`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`). The second gives the easy direction. For the converse, invert about `A` (`x ↦ x/|x|²`). Equality turns into `B'C' + C'D' = B'D'`, so `C' = (1−μ)B' + μD'` with `0 < μ < 1` (Mathlib's `dist_add_dist_eq_iff`). If `B'`, `D'` are parallel the four points are collinear, and the claim reduces to four reals (`ptolemy_real`, by cases on the order). Otherwise an explicit centre `m` with `⟪m, x'⟫ = 1/2` gives the circle, and `X = A + C'/κ` is the crossing point of the diagonals.
* **Fermat–Napoleon.** The bridge `apex_frame` writes `A'−A`, `B'−B`, `C'−C` in the frame `p = B−A`, `q = C−A`. It uses one scalar `α > 0` with `4α²(|p|²|q|²−⟪p,q⟫²) = 3`, obtained from the rotation formula `R_{∓π/3} v = ½v ∓ (√3/2)Jv` and Cramer's rule in the plane. Each metric fact is then a polynomial identity modulo that relation, closed by `linear_combination` with explicit cofactors (checked first with sympy/mpmath). The common point is `F = A + (y_A/S)(A'−A)`, with `y_A = 1+2α⟪p,q⟫`, `y_B = 1+2α(|p|²−⟪p,q⟫)`, `y_C = 1+2α(|q|²−⟪p,q⟫)`, `S = y_A+y_B+y_C > 0`. The angle hypotheses `< 2π/3` are exactly what make `y_A`, `y_B`, `y_C > 0`. Some helper lemmas are adapted (with attribution) from the Erdős–Mordell/Fermat–Torricelli development.

## Building and checking
```
lake build                # build the library
bash gate.sh              # no sorry/axiom/forbidden commands; build; #print axioms for every
                          # definition, bridge and theorem -> PASS (47 declarations, standard axioms only)
bash tests/tamper.sh      # 9 planted defects, each must be rejected -> ALL TAMPERING TESTS REJECTED
```
Do not run `lake update`. The Mathlib build is expected in `.lake/packages`.
