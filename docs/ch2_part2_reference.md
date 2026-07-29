# CH2 Part 2 API Reference: Contour Shifting, Residues, and Reflection

Lean definitions, lemmas, and theorem statements for the contour-shifting part of
`PrimeNumberTheoremAnd/IEANTN/CH2/CH2.lean`.

This file is an index of the declarations that are most useful when working in the CH2 contour
section: the rectangle geometry, the contour integral primitives, the simple-pole residue
machinery, the upper/lower half-plane shift lemmas, and the Proposition 5.2 specialisation.

---

## Status

This reference tracks the declarations that actually exist in `IEANTN/CH2/CH2.lean`.

- The residue-theorem, upper/lower rectangle lemmas, and the central-strip rectangle support for
  `lemma_5_1_c` are implemented.
- Several later blueprint theorems, notably `lemma_5_1_c` through `lemma_5_1_h`,
  `lemma_5_1`, and `prop_5_2_a` through `prop_5_2`, are present as theorem statements but still
  have `sorry` proofs in the current file.
- Private lemmas are included when they are important for maintainers, even though they are not
  exported API.

---

## Glossary

| Symbol | Lean Type | Meaning | Notes |
| :--- | :--- | :--- | :--- |
| `LadderParams` | `class` | Container for `σ`, `T`, `δ` | Encodes the contour geometry used throughout Lemma 5.1 and Proposition 5.2. |
| `l.R` | `Set ℂ` | `re ≤ 1`, `|im| ≤ T` | Main closed rectangle. |
| `l.Rboundary` | `Set ℂ` | Boundary of `R` | Right edge plus top/bottom edges. |
| `l.Rpos` | `Set ℂ` | `re ≤ 1`, `δ ≤ im ≤ T` | Upper strip above the contour `C`. |
| `l.RposBar` | `Set ℂ` | `re ≤ 1`, `-T ≤ im ≤ -δ` | Lower strip below the conjugate contour. |
| `l.RC` | `Set ℂ` | `re ≤ 1`, `|im| ≤ δ` | Central strip between `C` and `\bar C`. |
| `HIntegral f x₁ x₂ y` | `E` | `∫ x in x₁..x₂, f (x + y * I)` | Generic horizontal rectangle edge integral from `ResidueCalcOnRectangles.lean`. |
| `VIntegral f x y₁ y₂` | `E` | `I • ∫ y in y₁..y₂, f (x + y * I)` | Generic vertical rectangle edge integral from `ResidueCalcOnRectangles.lean`. |
| `intVSeg c a b F` | `ℂ` | Vertical segment integral | Integrates along `c + i[a,b]`. |
| `intHSeg h a b F` | `ℂ` | Horizontal segment integral | Integrates along `[a,b] + ih`. |
| `intHRay h b F` | `ℂ` | Horizontal ray integral | Integrates along `(-∞, b] + ih`. |
| `RectangleIntegral' f z w` | `ℂ` | `(1 / (2 * π * I)) • RectangleIntegral f z w` | Imported, not defined locally. Source: `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`, where `RectangleIntegral f z w = HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im + VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im`. |
| `residue f z₀` | `ℂ` | Simple-pole residue placeholder | Deliberately temporary; only reliable for simple poles. |
| `sumResiduesIn f S` | `ℂ` | `tsum` of residues over `S` | Analytic points contribute `0`. |
| `l.sumResiduesLim f S` | `ℂ` | Improper residue sum via `σ n → -∞` | Used for the central strip `RC`, where infinitely many poles may occur. |
| `ConjAntisymm g` | `Prop` | `g(\bar s) = -\overline{g(s)}` | Used for `G_star` and the imaginary-part reduction. |
| `ConjSymm F` | `Prop` | `F(\bar s) = \overline{F(s)}` | Used in the lower-half reflection and Proposition 5.2. |

### Imported Rectangle Integral

`RectangleIntegral'` is used heavily in the contour-shifting proofs, but it is imported rather than
defined in `IEANTN/CH2/CH2.lean`.

- Definition:
  `RectangleIntegral' f z w = (1 / (2 * π * I)) • RectangleIntegral f z w`
- Underlying unprimed integral:
  `RectangleIntegral f z w = HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im + VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im`
- Source:
  `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`
- Why it matters here:
  `CH2.lean` uses `RectangleIntegral'` as the normalized contour integral to match the `1 / (2π i)`
  factors in Lemma 5.1 and Proposition 5.2.

### Important theorems for `RectangleIntegral'`

These are the main results worth knowing before reading the CH2 contour proofs.

| Name | Where | What it gives | Why it matters in CH2 |
| :--- | :--- | :--- | :--- |
| `RectangleIntegral'_congr` | `ResidueCalcOnRectangles.lean` | If two functions agree on `RectangleBorder z w`, then their `RectangleIntegral'` values are equal | Lets you replace an integrand by a boundary-equal normal form or decomposition. |
| `HolomorphicOn.vanishesOnRectangle` | `ResidueCalcOnRectangles.lean` | A holomorphic function has zero rectangle integral | This is the vanishing step for the holomorphic remainder after removing principal parts. |
| `ResidueTheoremInRectangle` | `ResidueCalcOnRectangles.lean` | `RectangleIntegral' (fun s => c / (s - p)) z w = c` when `p` is in the interior | The atomic residue computation for a single simple pole. |
| `ResidueTheoremOnRectangleWithSimplePole` | `ResidueCalcOnRectangles.lean` | If `f = g + A / (s - p)` with `g` holomorphic, then `RectangleIntegral' f z w = A` | One-pole version of the residue theorem. |
| `ResidueTheoremOnRectangleWithSimplePole'` | `ResidueCalcOnRectangles.lean` | Big-O variant of the previous theorem | Useful when the principal-part decomposition is only known asymptotically near the pole. |
| `ContinuousOn.rectangleBorderIntegrable` | `ResidueCalcOnRectangles.lean` | Continuity on the rectangle gives `RectangleBorderIntegrable` | Standard way to discharge border-integrability side goals. |
| `RectangleBorderIntegrable.add` | `ResidueCalcOnRectangles.lean` | Rectangle integrals distribute over sums | Used when splitting an integrand into holomorphic and principal-part pieces. |
| `rectangleIntegral'_toMeromorphicNFOn_eq` *(private)* | `CH2.lean` | Replace `f` by `toMeromorphicNFOn f` in `RectangleIntegral'` | First CH2-specific normal-form reduction step. |
| `toMeromorphicNFOn_add_integral` *(private)* | `CH2.lean` | Splits the normal form into holomorphic part plus principal part inside `RectangleIntegral'` | Core decomposition step in the CH2 residue theorem proof. |
| `RectangleIntegral'_eq_sumResiduesIn` | `CH2.lean` | Full simple-pole residue theorem on rectangles | The public theorem that CH2 applies to upper and lower truncated rectangles. |
| `upperRectangleIntegral'_eq_sumResiduesIn` | `CH2.lean` | Specialised residue theorem for the upper truncated rectangle | Plug-in theorem for `lemma_5_1_a`. |
| `lowerRectangleIntegral'_eq_sumResiduesIn` | `CH2.lean` | Specialised residue theorem for the lower truncated rectangle | Plug-in theorem for `lemma_5_1_b`. |

### How to work with `RectangleIntegral'`

In this codebase, the usual workflow is:

1. Normalize the geometric setup.
   Prove the rectangle inequalities on real and imaginary parts, and establish that the boundary
   contains no poles.

2. Replace the integrand if needed.
   If you only care about the boundary values, use `RectangleIntegral'_congr`.
   In CH2 this is often done through `rectangleIntegral'_toMeromorphicNFOn_eq`.

3. Split off the singular part.
   Use the meromorphic normal form and decompose it into:
   a holomorphic remainder plus a finite sum of principal-part terms `c / (s - p)`.
   In CH2 this is exactly what `toMeromorphicNFOn_add_integral` and
   `rectangleIntegral'_sum_div_sub` implement.

4. Kill the holomorphic remainder.
   Apply `HolomorphicOn.vanishesOnRectangle` to the holomorphic part.

5. Evaluate the pole terms.
   For one pole, use `ResidueTheoremInRectangle` or
   `ResidueTheoremOnRectangleWithSimplePole`.
   For finitely many poles, sum the single-pole contributions, or use
   `RectangleIntegral'_eq_sumResiduesIn`.

6. Convert the residue set into the region you actually want.
   In CH2 the raw rectangle pole set is usually rewritten into strip language via
   `sumResiduesIn_upperRectangle_eq_sumResiduesIn_Rpos` or
   `sumResiduesIn_lowerRectangle_eq_sumResiduesIn_RposBar`.

### CH2-specific pattern

For the contour-shifting lemmas in `CH2.lean`, `RectangleIntegral'` is almost never the final goal.
Instead the proof pattern is:

- reduce a vertical segment integral to `intCnPlus` or `intCnMinus` plus `RectangleIntegral`
- renormalize to `RectangleIntegral'`
- apply the appropriate rectangle residue theorem
- rewrite the residue set from “poles in this literal rectangle” to “poles in `Rpos` or `RposBar`
  with `σ n < re`”

That is the path from
`intVSeg_eq_intCnPlus_add_rectangleIntegral` / `intVSeg_eq_intCnMinus_add_rectangleIntegral`
to `lemma_5_1_a` / `lemma_5_1_b`.

### `HIntegral` / `VIntegral` versus `intHSeg` / `intVSeg`

There are two closely related layers in the code.

#### 1. The generic rectangle layer

- `HIntegral` and `VIntegral` live in `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean`.
- They are generic over `f : ℂ → E`, where `E` is any complex normed space.
- They are the primitives used to define `RectangleIntegral` and `RectangleIntegral'`.

Definitions:

- `HIntegral f x₁ x₂ y = ∫ x in x₁..x₂, f (x + y * I)`
- `VIntegral f x y₁ y₂ = I • ∫ y in y₁..y₂, f (x + y * I)`

Mathematical role:

- They model the four oriented edges of a rectangle.
- `HIntegral` is a horizontal path integral with `ds = dx`.
- `VIntegral` is a vertical path integral with `ds = i dy`, which is why it carries the extra
  factor `I`.
- All rectangle residue theorems are built on top of this layer.

#### 2. The CH2 contour layer

- `intHSeg` and `intVSeg` live in `IEANTN/CH2/CH2.lean`.
- They are specialized to complex-valued integrands `F : ℂ → ℂ`.
- They are the primitives used to define the actual contours in Lemma 5.1:
  `intC`, `intCinf`, `intCnPlus`, `intCnMinus`, `intCn1Plus`, `intCn1Minus`.

Definitions:

- `intHSeg h a b F = ∫ r in a..b, F (r + h * I)`
- `intVSeg c a b F = ∫ t in a..b, F (c + t * I) * I`

Mathematical role:

- They encode the contour pieces in the same order and notation as the CH2 paper.
- `intHSeg` and `intVSeg` are not there to replace the rectangle API; they are there so the
  contour-shifting statements are easy to read and manipulate.

#### 3. What is actually different?

Mathematically:

- `HIntegral` and `intHSeg` are the same kind of horizontal line integral.
- `VIntegral` and `intVSeg` are the same kind of vertical line integral.
- In both vertical definitions, the extra `I` comes from `ds = i dt`.

In Lean:

- `HIntegral` / `VIntegral` are generic and rectangle-oriented.
- `intHSeg` / `intVSeg` are CH2-specific and contour-oriented.
- `VIntegral` uses scalar multiplication `I • ∫ ...`, while `intVSeg` uses complex multiplication
  `∫ ... * I`; for complex-valued functions these are equivalent after the usual rewrites.
- The argument order differs:
  `HIntegral f x₁ x₂ y` versus `intHSeg h a b F`,
  `VIntegral f x y₁ y₂` versus `intVSeg c a b F`.

#### 4. How the proofs move between the two layers

The standard CH2 proof pattern is:

1. State and manipulate contour identities using `intHSeg` / `intVSeg`.
2. Rewrite the rectangle term into `HIntegral` / `VIntegral` form.
3. Package that as `RectangleIntegral` or `RectangleIntegral'`.
4. Apply the rectangle residue theorem.

This is exactly what happens in:

- `intVSeg_eq_intCnPlus_add_rectangleIntegral`
- `intVSeg_eq_intCnMinus_add_rectangleIntegral`

Inside those lemmas:

- horizontal sides are usually identified by `rfl`
- vertical sides are matched by rewriting between `I • ∫ ...` and `∫ ... * I`

#### 5. API for `HIntegral` / `VIntegral`

These are the main lemmas to use on the generic rectangle side.

| Name | Use |
| :--- | :--- |
| `HIntegral_symm` | Reverse horizontal orientation. |
| `VIntegral_symm` | Reverse vertical orientation. |
| `RectangleBorderIntegrable` | Bundle the four side-integrability assumptions. |
| `ContinuousOn.rectangleBorderIntegrable` | Get border integrability from continuity. |
| `RectangleBorderIntegrable.add` | Split a rectangle integral across a sum of functions. |
| `RectangleIntegralHSplit` / `RectangleIntegralVSplit` | Cut a rectangle into two smaller rectangles. |
| `RectangleIntegral'_congr` | Replace the integrand when boundary values agree. |
| `HolomorphicOn.vanishesOnRectangle` | Kill holomorphic pieces. |
| `ResidueTheoremInRectangle` | Evaluate the integral of a single simple-pole term. |
| `ResidueTheoremOnRectangleWithSimplePole` | One-pole rectangle residue theorem. |

#### 6. API for `intHSeg` / `intVSeg`

These are the tools that show up on the CH2 contour side.

| Name | Use |
| :--- | :--- |
| `intVSeg_eq_intCnPlus_add_rectangleIntegral` | Replace the upper central segment by the upper contour plus a rectangle term. |
| `intVSeg_eq_intCnMinus_add_rectangleIntegral` | Lower-half analogue. |
| `intervalIntegral.integral_add_adjacent_intervals` | Glue adjacent CH2 contour segments. |
| `intervalIntegral.integral_symm` | Reverse contour segment orientation after unfolding. |
| `G_mul_cpow_integrable_vseg` | Prove upper-half vertical segment integrability for `G(s) x^s`. |
| `G_mul_cpow_integrable_vseg_lower` | Lower-half analogue. |
| `l.intCnPlus`, `l.intCnMinus`, `l.intCn1Plus`, `l.intCn1Minus` | Canonical named contour combinations used in the statements. |

Rule of thumb:

- If the goal is about a literal contour piece from Lemma 5.1, use `intHSeg` / `intVSeg`.
- If the goal is about a rectangle, residues, boundary integrability, or vanishing of a holomorphic
  part, move to `HIntegral` / `VIntegral` and then to `RectangleIntegral'`.

---

## Main Public Results

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `RectangleIntegral'_eq_sumResiduesIn` | Rectangle integral equals sum of residues in the rectangle | The local simple-pole residue theorem used throughout the file. |
| `lemma_5_1_a` | Upper half of the central line equals `C_n^+` plus residues in `Rpos ∩ {σ n < re}` | First contour shift in the upper half-plane. |
| `lemma_5_1_b` | Lower half of the central line equals `C_n^-` plus residues in `RposBar ∩ {σ n < re}` | Lower-half analogue of `lemma_5_1_a`, using reflection. |
| `lemma_5_1` | Full contour-shifting identity of CH2 Lemma 5.1 | Main contour decomposition into `Cinf`, `intC`, off-axis residues, and the improper `RC` residue sum. |
| `prop_5_2` | Specialisation of Lemma 5.1 to the Graham-Vaaler weight `Phi_lambda` | Packages the contour-shift identity with explicit error terms for Proposition 5.2. |

---

## 1. Geometry and Contour Primitives

These are the declarations to reach for when you need to place a point or a path inside the right
region, or when you need the explicit decomposition of the contours used in Lemma 5.1.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `LadderParams.hT` | `0 < l.T` | Immediate positivity witness for the rectangle height. |
| `LadderParams.Rboundary_subset_R` | `l.Rboundary ⊆ l.R` | Moves boundary points into the ambient rectangle. |
| `LadderParams.Rboundary_subset_ladder` | `l.Rboundary ⊆ l.ladder` | Lets boundary boundedness/no-pole facts be viewed as ladder facts. |
| `LadderParams.L_subset_R` | `l.L ⊆ l.R` | Same for the ladder columns. |
| `LadderParams.L_subset_ladder` | `l.L ⊆ l.ladder` | Records that the truncation columns are part of the full ladder. |
| `LadderParams.admissible_contour_subset_R` | `l.admissible_contour ⊆ l.R` | Same for the contour `C`. |
| `LadderParams.admissible_contour_subset_RC` | `l.admissible_contour ⊆ l.RC` | Places the contour on the upper edge of the central strip. |
| `LadderParams.Rpos_subset_R` | `l.Rpos ⊆ l.R` | Upper strip sits in `R`. |
| `LadderParams.RposBar_subset_R` | `l.RposBar ⊆ l.R` | Lower strip sits in `R`. |
| `LadderParams.RC_subset_R` | `l.RC ⊆ l.R` | Central strip sits in `R`. |
| `LadderParams.belowContour_subset_RC` | `l.belowContour ⊆ l.RC` | Shows the pole-free open strip below `C` still lies in the central region. |
| `LadderParams.belowContour_disjoint_admissible_contour` | `Disjoint l.belowContour l.admissible_contour` | Formalizes that points strictly below `C` are not on the contour. |
| `LadderParams.conj_mem_R_iff` | `conj z ∈ R ↔ z ∈ R` | Conjugation symmetry of the ambient rectangle. |
| `LadderParams.conj_mem_ladder_iff` | `conj z ∈ ladder ↔ z ∈ ladder` | Conjugation symmetry of the full ladder/boundary set. |
| `LadderParams.conj_mem_Rboundary_iff` | `conj z ∈ Rboundary ↔ z ∈ Rboundary` | Conjugation symmetry of the boundary. |
| `LadderParams.conj_mem_RC_iff` | `conj z ∈ RC ↔ z ∈ RC` | Conjugation symmetry of the central strip. |
| `LadderParams.conj_mem_Rpos_iff_mem_RposBar` | `conj z ∈ Rpos ↔ z ∈ RposBar` | Swaps upper and lower strips under conjugation. |
| `LadderParams.upperRectangle_subset_Rpos` | Upper truncated rectangle lies in `Rpos` | Main region lemma for `lemma_5_1_a`. |
| `LadderParams.lowerRectangle_subset_RposBar` | Lower truncated rectangle lies in `RposBar` | Lower-half analogue used in `lemma_5_1_b`. |
| `intVSeg` | Vertical segment integral | Core primitive for central-line and ladder-column integrals. |
| `intHSeg` | Horizontal segment integral | Core primitive for top/bottom and contour segments. |
| `intHRay` | Horizontal ray integral | Used for `C` and `Cinf`. |
| `l.intVerticalAt c` | `intVSeg c (-T) T` | The full vertical line at real part `c`. |
| `l.intCinf` | Top ray minus bottom ray | The contour `C_\infty` in Lemma 5.1. |
| `l.intC` | Vertical `1 → 1+iδ` minus horizontal ray `1+iδ → -∞+iδ` | The simplified contour `C`. |
| `l.intCnPlus` | Four-piece upper truncated contour | The contour `C_n^+`. |
| `l.intCnMinus` | Four-piece lower truncated contour | The contour `C_n^-`. |
| `l.intCn1Plus` | `C_n^+` without the top segment | The contour `C_{n,1}^+`. |
| `l.intCn1Minus` | `C_n^-` without the bottom segment | The contour `C_{n,1}^-`. |

---

## 2. Residue and Meromorphicity Helpers

These are the reusable local analytic lemmas that power the rectangle residue theorem and the
contour-shifting arguments.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `residue_eq_of_tendsto` | If `(z - p) f z → c`, then `residue f p = c` | Direct interface for proving a residue value. |
| `residue_analyticAt_eq_zero` | Analytic points have residue `0` | Used to ignore non-poles in residue sums. |
| `simplePole_sub_residue_isBigO_one` | `f - residue/(z-p)` is bounded near a simple pole | Standard principal-part subtraction lemma. |
| `HasSimplePolesOn.mono` | Restrict a simple-pole hypothesis to a smaller set | Lets rectangle-specific residue theorems inherit a global simple-pole hypothesis on `R`. |
| `analyticAt_rpow` | `s ↦ (x : ℂ)^s` is analytic for `x > 0` | Basic regularity of the `x^s` factor. |
| `meromorphicAt_rpow` | `s ↦ (x : ℂ)^s` is meromorphic for `x > 0` | Meromorphic wrapper around `analyticAt_rpow`. |
| `meromorphicOrderAt_rpow` | The order of `s ↦ (x : ℂ)^s` is `0` | Crucial when showing `x^s` does not create poles. |
| `residue_eq_zero_of_not_pole_of_meromorphicAt` | Meromorphic + nonnegative order implies residue `0` | Used when converting rectangle pole sets into larger ambient regions. |
| `meromorphicOrderAt_starRingEnd` | Symmetric or antisymmetric functions preserve pole order under conjugation | Key reflection lemma for the lower-half arguments. |
| `sumResiduesIn_inter_eq_of_set_eq` | Equal pole intersections give equal residue sums once residues vanish off the pole set | Generic set-rewrite tool behind the rectangle-to-strip residue conversions. |

### Rectangle-level residue theorem support

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `RectangleIntegral'_eq_sumResiduesIn` | Rectangle integral equals the sum of residues of interior poles | Main public residue theorem used by both half-plane shifts. |
| `sumResiduesIn_upperRectangle_eq_sumResiduesIn_Rpos` | Upper rectangle pole set may be replaced by `Rpos ∩ {σ n < re}` | Converts the geometric rectangle residue set into the natural strip truncation. |
| `sumResiduesIn_lowerRectangle_eq_sumResiduesIn_RposBar` | Lower rectangle pole set may be replaced by `RposBar ∩ {σ n < re}` | Lower-half analogue. |

---

## 3. Upper-Half Contour-Shift Lemmas

These are the public lemmas that build the upper-half contour shift.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `upperRectangle_meromorphicOn` | `G(s) x^s` is meromorphic on the upper truncated rectangle | Rewrites `G` to `G_circ + G_star` because `im s > 0` there. |
| `upperRectangleIntegral'_eq_sumResiduesIn` | Upper rectangle integral equals the residue sum in that rectangle | Applies the general residue theorem after restricting to the upper region. |
| `intVSeg_eq_intCnPlus_add_rectangleIntegral` | `intVSeg 1 0 T = intCnPlus + RectangleIntegral` | Algebraic contour decomposition before residues are inserted. |
| `upperRectangle_no_poles_boundary` | No poles of `G(s) x^s` lie on the upper rectangle boundary | Uses boundedness on `Rboundary`, `L`, and the contour. |
| `lemma_5_1_a` | Upper central segment equals upper contour plus upper-strip residues | First main contour shift in CH2 Lemma 5.1. |

### Useful private helpers in the upper-half proof

| Name | Role |
| :--- | :--- |
| `filter_eventuallyEq_G_pos` | Replaces `G` by `G_circ + G_star` near points with positive imaginary part. |
| `mem_RectangleBorder_upper_cases` | Classifies upper rectangle boundary points into contour / ladder / boundary cases. |
| `G_mul_cpow_integrable_vseg` | Proves interval integrability of `t ↦ G(1+it) x^(1+it) i` on upper subsegments. |
| `continuousOn_toMeromorphicNFOn_subset` | Upgrades pole-free meromorphic normal forms to continuity on any subset `S ⊆ l.R`. |
| `ae_eq_NF_vseg` | Almost-everywhere equality between a meromorphic function and its normal form along a vertical path. |

---

## 4. Lower-Half and Reflection Lemmas

These are the lower-half analogues, together with the conjugation machinery that makes them work.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `ConjSymm` | `F(\bar s) = \overline{F(s)}` | Reflection hypothesis for even-type pieces such as `G_circ` or `F`. |
| `intVSeg_eq_intCnMinus_add_rectangleIntegral` | `intVSeg 1 (-T) 0 = intCnMinus + RectangleIntegral` | Lower-half contour decomposition. |
| `lowerRectangle_meromorphicOn` | `G(s) x^s` is meromorphic on the lower truncated rectangle | Rewrites `G` to `G_circ - G_star` because `im s < 0` there. |
| `lowerRectangle_no_poles_boundary` | No poles of `G(s) x^s` lie on the lower rectangle boundary | Uses conjugation symmetry plus boundedness hypotheses. |
| `lowerRectangleIntegral'_eq_sumResiduesIn` | Lower rectangle integral equals the residue sum in that rectangle | Lower-half residue theorem application. |
| `sumResiduesIn_lowerRectangle_eq_sumResiduesIn_RposBar` | Lower rectangle residue set equals `RposBar ∩ {σ n < re}` | Converts the residue set to the natural lower strip truncation. |
| `lemma_5_1_b` | Lower central segment equals lower contour plus lower-strip residues | Lower-half analogue of `lemma_5_1_a`. |

### Reflection utilities

| Name | Role |
| :--- | :--- |
| `conj_reflect_involutive` *(private)* | `conj_reflect` is an involution, so reflection can be undone cleanly. |
| `tendsto_starRingEnd_nhds` *(private)* | Sends neighborhoods at `conj a` back to neighborhoods at `a`. |
| `tendsto_starRingEnd_nhdsWithin_ne` *(private)* | Same transport on punctured neighborhoods, needed for pole order arguments. |
| `analyticAt_conj_reflect` *(private)* | Reflection preserves analyticity. |
| `meromorphicAt_conj_reflect` *(private)* | Reflection preserves meromorphicity. |
| `meromorphicAt_conj_reflect_iff` *(private)* | Reflection gives a two-way equivalence of meromorphicity. |
| `meromorphicOrderAt_conj_reflect` *(private)* | Reflection preserves local meromorphic order. |
| `meromorphicOrderAt_starRingEnd` | Public wrapper: symmetric or antisymmetric functions have equal orders at `z` and `\bar z`. |
| `conj_intVSeg_of_antisymm` | Conjugating a vertical segment integral reflects it to `intVSeg c (-b) (-a)` | Public contour-integral reflection identity used in `lemma_5_1_d`. |
| `conj_intHSeg_of_antisymm` | Conjugating a horizontal segment integral reflects it to `intHSeg (-h) b a` | Horizontal analogue for the contour pieces in `C_{n,1}^\pm`. |

### Useful private helpers in the lower-half proof

| Name | Role |
| :--- | :--- |
| `filter_eventuallyEq_G_neg` | Replaces `G` by `G_circ - G_star` near points with negative imaginary part. |
| `meromorphicOrderAt_neg_nonneg` | If `F` has nonnegative order, then so does `-F`. |
| `meromorphicOrderAt_mul_cpow_eq` | Multiplying by `x^s` does not change the meromorphic order when `x > 0`. |
| `mem_RectangleBorder_lower_cases` | Classifies lower rectangle boundary points into contour / ladder / boundary cases. |
| `G_mul_cpow_integrable_vseg_lower` | Lower-half interval-integrability lemma for `t ↦ G(1+it) x^(1+it) i`. |

---

## 5. Limit and Assembly Theorems for Lemma 5.1

These declarations are the theorem-level endpoints used to assemble the full contour-shifting
formula. Several of them are currently scaffolded with `sorry`, but they define the intended API.

### Central-strip rectangle support

These implemented lemmas are the residue-theorem backbone behind `lemma_5_1_c`.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `intCn1Plus_add_intCn1Minus_eq_rectangleIntegral_add_verticalAt` | `intCn1Plus + intCn1Minus = RectangleIntegral + intVerticalAt (σ n)` | Algebraic decomposition that exposes the central rectangle and the `σ n` column. |
| `centralRectangle_subset_RC` | Central truncated rectangle lies in `RC` | Main geometry lemma for the strip between `C` and `\bar C`. |
| `centralRectangle_meromorphicOn` | `G_circ(s) x^s` is meromorphic on the central rectangle | Regularity input for the central-strip residue theorem. |
| `centralRectangle_no_poles_boundary` | No poles of `G_circ(s) x^s` lie on the central rectangle boundary | Boundary hypothesis for the central-strip residue theorem. |
| `centralRectangleIntegral'_eq_sumResiduesIn` | Central rectangle integral equals the residue sum in that rectangle | Central-strip analogue of the upper/lower rectangle residue theorems. |
| `sumResiduesIn_centralRectangle_eq_sumResiduesIn_RC` | Central rectangle pole set may be replaced by `RC ∩ {σ n < re}` | Converts the geometric rectangle residue set to the paper's central-strip truncation. |

### Useful private helpers for the limit proofs

These helpers are not theorem-level endpoints, but they are the main reusable tools behind
`lemma_5_1_e`, `lemma_5_1_f`, and `lemma_5_1_h`.

| Name | Role |
| :--- | :--- |
| `meromorphicOrderAt_nonneg_on_of_bounded` | Generic extractor: if `F(s) x₀^s` is bounded with no poles on `S ⊆ l.R`, then `F` has nonnegative meromorphic order on `S`. |
| `aestronglyMeasurable_horizontal_path_mul_cpow_of_meromorphic` | Proves AE strong measurability of `r ↦ F(r + hI) x^(r+hI)` on `(-∞,1]` from meromorphicity on `l.R` and a no-pole hypothesis on the horizontal path. |
| `aestronglyMeasurable_hray_of_meromorphic` | Boundary-ray wrapper around the previous lemma for the special case `|h| = l.T`. |
| `norm_G_mul_cpow_le_of_base_bound` | Pointwise estimate: a bound on `‖G(s) x₀^s‖` at one horizontal-path point upgrades to a bound on `‖G(s) x^s‖` by the factor `exp(log(x/x₀) · re(s))`. |
| `bound_G_mul_cpow_hray` | Boundary-ray wrapper around `norm_G_mul_cpow_le_of_base_bound`; used in the top/bottom ray integrability proof. |
| `G_mul_cpow_integrable_hray` | Gives integrability of `G(s) x^s` on the upper or lower horizontal boundary ray. |
| `intVSeg_tendsto_zero_of_bounded_on_L` | Generic far-left column estimate: if `F(s) x₀^s` is bounded on `l.L`, then `intVSeg (σ n) a b (F(s) x^s) → 0` for any fixed `a ≤ b` with `[a,b] ⊆ [-T,T]`. |

| Name | Simplified Statement | Intended Role |
| :--- | :--- | :--- |
| `lemma_5_1_c` | The `G_circ` parts of `C_{n,1}^+` and `C_{n,1}^-` shift to the `σ n` column plus residues in `RC` | Handles the even/symmetric part in the central strip. |
| `lemma_5_1_d` | The `G_star` integrals on `C_{n,1}^+` and `C_{n,1}^-` combine into `2 i Im(...)` | Uses conjugation-antisymmetry to reduce to one contour integral. |
| `lemma_5_1_e` | The top and bottom horizontal segments converge to `intCinf` as `n → ∞` | Turns truncated top/bottom pieces into the limiting contour at infinity. |
| `lemma_5_1_f` | The `σ n`-column integral of `G_circ(s) x^s` tends to `0` | Vanishing of the far-left vertical column. |
| `lemma_5_1_g` | Truncated residue sums over `{σ n < re}` converge to the full finite residue sum | Exhaustion lemma for finite pole sets. |
| `lemma_5_1_h` | `intCn1Plus` for `G_star(s) x^s` tends to `intC` | Convergence of the truncated contour `C_{n,1}^+` to the full contour `C`. |
| `lemma_5_1` | Full Lemma 5.1 contour-shifting identity | Final assembly theorem. |

---

## 6. Proposition 5.2 Specialisation

The last section specialises the contour-shifting machinery to the Graham-Vaaler weight.

| Name | Simplified Statement | Role |
| :--- | :--- | :--- |
| `LadderParams.zOf` | `z(s) = (s - 1)/(iT)` | Rescales the central line `1 + i[-T,T]` to `[-1,1]`. |
| `Phi_lambda` | Combined `Phi_circ` / `Phi_star` weight with sign `lam` | The CH2 Proposition 5.2 weight. |
| `prop_5_2_a` | Applies `lemma_5_1` to `Phi_lambda(l.zOf s) * F(s)` | Reduction of Proposition 5.2 to Lemma 5.1. |
| `prop_5_2_b` | Bounds the `intCinf` term | Extracts the explicit horizontal-ray error term. |
| `prop_5_2_c` | Bounds the `Im intC` term | Controls the contour contribution from `Phi_star`. |
| `prop_5_2` | Final Proposition 5.2 bound | Packages the residue terms and the two error contributions. |

---

## 7. How to Use This File

- If you need a contour decomposition, start with `intVSeg_eq_intCnPlus_add_rectangleIntegral` or
  `intVSeg_eq_intCnMinus_add_rectangleIntegral`.
- If you need residues in a truncated rectangle, use `upperRectangleIntegral'_eq_sumResiduesIn` or
  `lowerRectangleIntegral'_eq_sumResiduesIn`, then convert the residue set with the corresponding
  `sumResiduesIn_*_eq_*` lemma.
- If the lower half-plane is involved, expect a reflection step through `ConjSymm`,
  `ConjAntisymm`, and `meromorphicOrderAt_starRingEnd`.
- If you are debugging why `x^s` does not introduce poles, the key lemmas are
  `analyticAt_rpow`, `meromorphicAt_rpow`, and `meromorphicOrderAt_rpow`.
- If you are extending the implementation rather than just consuming the public API, the private
  helpers in Sections 3 and 4 are the main proof-engineering utilities.
