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

## Layer 13 (blind restatement)

An independent writer, who saw only the plain-English statements of the paper and not this library,
wrote the theorem statements in Lean on their own (`PaperHBlind.lean`, sha256 beginning
`e257c271479a928f`). `FermatNapoleon/L13Blind.lean` (namespace `FermatNapoleon.Blind`) copies the
writer's definitions and statements 28 and 37–50 verbatim. For each one it proves both directions
against the library theorem: `rb_K` (library → blind) and `br_K` (blind → library).

* All 15 blind statements are proved equivalent to the library in both directions (13 of them
  jointly). The writer split five library theorems into parts: outward apexes (37–39), equal
  distances (40–41), meeting at the Fermat point (43–44), the 60° angles (45–47) and Napoleon's
  theorem (48–50). Each part follows from the library theorem, and together the parts give it back
  (`br_37_38_39`, `br_40_41`, `br_43_44`, `br_45_46_47`, `br_48_49_50`). Ptolemy's equality case (28)
  and the concurrence (42) are equivalent individually.
* The agreement lemmas show that the writer's orientation sign, outward apexes, Napoleon centres and
  centroid are the library's. `agree_orders` shows that the writer's eight order conditions for four
  collinear points are the library's condition.
* No difference in meaning was found.

## Layer 14 (Mathlib-only restatements and witnesses)

`FermatNapoleon/L14.lean` restates every main theorem using only Mathlib notions. The outward apexes
are written out explicitly by the rotation formula, and the Napoleon centres as centroids. All 9
restatements (`l14_*`) are proved from the library, together with two bridges that connect the
library's apex definition to the explicit formula. Four witness theorems (`l14w_*`) show that the
hypotheses can be satisfied: the triangle 0, 4, 3i in the complex plane with its apexes, Fermat point
and a non-degenerate Napoleon triangle; a rectangle (cyclic case of Ptolemy); and collinear points.

## Layer 15 (classical statements)

An independent writer also stated the classical theorems in textbook form, using only Mathlib and a few
elementary definitions (`PaperHClassical.lean`, sha256 beginning `0ac73f94ec9efdb8`).
`FermatNapoleon/L15Classical.lean` (namespace `FermatNapoleon.Classical`) copies these definitions
verbatim and restates each assigned classical statement with its verbatim type as `cov_<name>`.

* All 6 classical statements are proved from the library: Ptolemy's equality case with its converse
  (P2), the Fermat–Napoleon statements (F2a equal lengths, F2b concurrence, F2c meeting at the Fermat
  point, F2d 60° angles) and Napoleon's theorem (F3).
* NEW PROOFS. These translate between the classical definitions and the library's; they are not part
  of the earlier layers:
  * `real_order_iff`, `col_iff`: the classical order condition for four collinear points is the library's.
  * `coplanar_of_cross`, `sbtw_of_concyclic`: crossing diagonals of four concyclic points (weak versus
    strict crossing).
  * `inner_of_angle'`, `vne_of_angle`, `vne_of_angle'`, `unit_sum`, `fermat_unique_vec`,
    `fermat_unique`: the point seeing three points at mutual 120° is unique (used for F2c, where the
    classical statement starts from the Fermat point instead of the intersection of the lines).
  * `apex_eq`, `classical_apexes`: in the plane, an apex defined classically (an equilateral triangle
    on the far side of the edge) is the library's apex for the orientation given by any basis.

## Building and checking
```
lake build                # build the library
bash gate.sh              # no sorry/axiom/forbidden commands; build; #print axioms for every
                          # definition, bridge and theorem -> PASS (171 declarations, standard axioms only)
bash tests/tamper.sh      # 9 planted defects, each must be rejected -> ALL TAMPERING TESTS REJECTED
```
Do not run `lake update`. The Mathlib build is expected in `.lake/packages`.
