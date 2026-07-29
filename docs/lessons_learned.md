# Formalization Lessons Learned

Tactic pitfalls, type-system friction, and proof strategies encountered while formalizing `CH2.lean`. This guide is organized pedagogically to help navigate common Lean 4 hurdles.

---

## 1. The First-Aid Kit: Immediate Troubleshooting

If a tactic fails unexpectedly, check this table first.

### 1.1 Quick Reference: What Failure Tells You

| Symptom | Most Likely Cause |
| :--- | :--- |
| `aesop` timeouts on geometric probability or measure bounds | **Lack of Specific Heuristics**: `aesop` excels at logic and category theory but struggles with high-level `Measure.map` symmetries or geometric bounds, often chasing deep definitional unfoldings instead. Unroll symmetric probability bounds manually using `Measure.map` and `measureReal_union_add_inter` instead. |
| Defeq loop on `lake env lean` with combinatorics | **Missing Structural Instance**: Asking Lean to dynamically synthesize `LocallyFiniteOrder` for complex subset structures like `Finpartition s` using the generic `Fintype.toLocallyFiniteOrder` fallback triggers a defeq explosion. Manually construct the explicit order structures or find alternative API. |
| Hanging typeclass synthesis on `IsGaussian` and `StrongDual` | **Multilinear Map Overload**: The `IsGaussian μ` typeclass mixed with continuous linear functionals (`StrongDual`) and `centeredDual` forces Lean to resolve overlapping `BorelSpace` and `NormedSpace` branches exponentially. Provide explicit instances or avoid unbundling the multilinear maps natively. |
| Defeq loop or timeout on `rintro rfl` | **Expensive Context Search**: `rfl` in a pattern match forces Lean to check definitional equality across the entire local context. In files with heavy topological/measure structures (e.g. `EuclideanSpace`, `stdGaussian`), replacing variables triggers expensive, non-terminating defeq searches. Use `intro h_eq; rw [h_eq]` followed by explicit constructor building instead. |
| `linarith` fails on inner products or Finset sums | **Pi-Type / Sum Blindness**: `linarith` only solves linear inequalities over numeric scalars. It cannot see "inside" a `Finset.sum` or a Pi-type function evaluation. Unfold higher-level inner products (e.g., `EuclideanSpace`) into explicit `Finset.sum` and manually manipulate them with algebraic lemmas until they become scalar inequalities `linarith` can process. |
| `rw` fails with "pattern not found" after `dsimp` | **Definitional Over-Reduction**: `dsimp` aggressively reduces definitional equalities. It may reduce an expression (e.g., an inner product functional) so completely that a subsequent `rw` expecting the abstract form fails to match. |
| `simp [le_antisymm_iff]` leaves `y ≤ 0 ∧ 0 ≤ y` | **Bidirectional Blindness**: `simp` blindly rewrites sub-terms and may leave equivalent symmetric fragments instead of closing the goal. Explicit `exact` with constructor building (e.g., `⟨le_refl _, le_refl _⟩`) is safer. |
| `linarith` fails on `EuclideanSpace` or `WithLp.toLp 2` | **Topology Obscures Algebra**: While `EuclideanSpace` is great for topological properties (variance, integrals), it obscures algebraic properties from solvers like `linarith`. You must use bridging lemmas (like `innerProduct_eq_inner_toLp`) to translate between the "topological world" and the "algebraic world". |
| `HPow ℕ ℝ ?m` | **Default Type Fallback**: Lean defaulted an un-annotated numeric base like `2` to `(2 : ℕ)` in a real-power expression. Use explicit type signatures: `(2 : ℝ) ^ (-1/4 : ℝ)`. |
| `gcongr` fails on `x ^ y ≤ x ^ z` | **Positivity Blindspot**: `positivity` (which `gcongr` relies on) fails to prove `0 ≤ x ^ y` for real powers. Use manual order lemmas like `mul_le_mul_of_nonneg_right` and explicitly supply `Real.rpow_nonneg`. |
| `Invalid field trans_le` | **Projection Failure**: dot-notation on a `Prop` (inequality). Use functional application `le_trans` or `h1.trans h2`. |
| Dot-notation `h.foo` fails | Type of `h` is a `def` alias or `∃`, not a `structure` |
| `apply` fails with coercion mismatch | `↑` wrapper order or negation placement prevents unification |
| `exact_mod_cast` fails | Bridge between types is propositional, not a simple coercion |
| `rw` says "Did not find occurrence" | Prior `simp` changed the AST; use `show` to check; or measure mismatch in integrals |
| `simp` enters infinite loop | Symmetry lemma oriented in a non-terminating direction |
| "No goals to be solved" | A preceding tactic already closed the goal |
| Goal displays `z ∈ sorry ()` | Metavariable poisoning from an earlier error; fix the *first* error |
| `exact` fails with type mismatch | Syntactically different but mathematically equal terms; use `convert ... using 1` |
| `clear h` fails though `h` is not printed in the goal | Hidden cast/transport term (`Eq.ndrec`) from an earlier `change`/`convert`; inspect with `set_option pp.proofs true` or `pp.all true` |
| `exact` fails with `Max ℂ` | Codomain mismatch: using ℂ-witness for ℝ-integrand. Use `.norm` to stay in ℝ. |
| `calc` type mismatch | AST mismatch (e.g. `-(u * v)` vs `-u * v`). Normalize or match proof term structure. |
| `ae_of_all` loses `u \in s` | Generalizing to all `u` discards measure restriction. Use `filter_upwards [ae_restrict_mem ...]`. |
| `Invalid field neg_pos` | Dot-notation on a `Prop` (inequality). Use functional application `neg_pos.mpr`. |
| `nhdsWithin \le nhds` goal | `convert` was used where `mono_left` or `Tendsto.mono_left` was needed |
| `0 < re ?m` in continuity | `continuousAt_cpow_const` (constant base) used instead of `continuousAt_const_cpow` (constant exponent) |
| `positivity` fails on `0 \le b` | Transitivity Blindness; tactic cannot see `0 < a \le b`. Use `(h_pos.trans_le h_le).le` |
| `apply` fails with coerced limits | AST mismatch between `↑(a/b)` and `↑a/↑b` in `nhds`; use `convert ... using 1`. |
| Named argument mismatch | Parameter names (e.g. `y` vs `b`) must match Mathlib exactly; verify via `grep` on packages. |
| `convert ... using 1` on `Tendsto` | Bridges `↑`-distribution mismatches in the limit point while preserving the filter structure. |
| `MeasureTheory.measure_singleton` fails | AST mismatch: set is `Set.Icc a a` not `{a}`. Use `Set.Icc_self` first. |
| `mod_cast` fails on `PNat \le ℝ` | Coercion tower is too complex; use `Nat.one_le_cast.mpr` or `(Nat.one_le n).cast_le` |
| `rfl` fails on `n^1 = n` | Definitional mismatch; use `simp` or `Complex.cpow_one` |
| `apply` fails on `1 \le \beta` for `0 \le \beta` | Rigid Unification; `apply` doesn't bridge inequalities. Use `zero_le_one.trans` |
| `refine` fails on `rexp 0` vs `1` | Definitional Identity Rigidity; `refine` can fail on definitionally equal terms inside compositions. Use `convert ... using 1` |
| `positivity` fails on `a n` | Universal Blindness; structural tactics do not instantiate `∀ n, 0 ≤ a n`. Use `have : 0 ≤ a n := ha_pos n`. |
| `rw [mul_comm ↑↑n]` fails | Coercion AST mismatch; `rw` is sensitive to the hidden structure of `PNat` casts. Use `push_cast` then `simp_rw [mul_comm (n : ℝ)]`. |
| `Invalid field mp` | **Prop Dot-Notation Trap**: Dot-notation (e.g., `h.mp`) only works on **Structures** (like `Iff` or `Eq`). It fails on **Propositions** (like `Real.le`). Use the `_iff` version of the lemma (e.g., `log_le_log_iff`) to get a structure. |
| `positivity` / `norm_num` fails on let-bound variable | **Let-Binding Opacity**: The tactic cannot see the value behind a local `let` binding. Use `dsimp [var]` to unfold the definition before calling the tactic. |
| `List.getLast_mem` type mismatch | **Implicit List Argument**: `List.getLast_mem` takes the list as an implicit argument. Pass only the non-emptiness proof `h_ne`. |
| `Invalid field and: ... Exists.and` | **Projection Failure on Existential Aliases**: Dot-notation on a type alias (`Eventually` or `∈`) where the definition reduces to `Exists` (such as `t ∈ F ⊓ G`) causes Lean to look for `Exists.and`. Use fully qualified names (e.g. `Filter.Eventually.and`) via standard function application instead. |
| `failed to synthesize instance ... NeBot` | **Typeclass Syntax-Sensitivity**: Lean's `synthInstance` matches syntactically. A definitionally equal but syntactically distinct set (e.g. `{x | (fun x ↦ x > a) x}` vs `Set.Ioi a`) will fail. Define a local `haveI` instance matching the exact syntax inside the tactic block (`by`). |
| `CompleteSpace ?m.XXXX` in polymorphic theorem application | **Implicit Type Unresolved**: Applying a theorem polymorphic in `E : CompleteSpace` (e.g. `intervalIntegral.integral_eq_sub_of_hasDerivAt`) with `?_` holes leaves `E` as a metavar. Fix: supply a named argument `(f := fun t : ℝ ↦ ...)` to pin `E = ℝ`. |
| `rw [← thm h₁ h₂]` creates unresolved `?m.XXXX` | **Backward Rewrite Metavar**: A backward rewrite where `h₁`/`h₂` come from `ContinuousOn.intervalIntegrable` does not pin all implicit arguments (e.g. the split point). Use the theorem **forward** inside `linarith [thm h₁ h₂]` instead, with `h₁`/`h₂` from `Continuous.intervalIntegrable a b` with explicit endpoints. |
| `interval_decide` leaves extra unsolved goal | **Sqrt Normalization Side Effect**: `interval_decide` normalizes `√(p/q)` → `√p / √q` and emits the equivalence as a side goal. Close it with `· left; ring` or `· ring` depending on whether the goal is a disjunction. |
| `interval_decide` fails immediately on `√1.0` | **OfScientific Sqrt Argument + norm_num Overshoot**: `Real.sqrt_one` only fires on `OfNat` `1`, not `OfScientific` `1.0`. Using `norm_num [Real.sqrt_one]` to fix this also normalizes other literals (e.g. `1.5 → 3/2`) and then splits `√(3/2) → √3 / √2`, which gives `interval_decide` looser interval bounds and causes it to fail. Fix: use a **targeted `have`** to rewrite only the problematic subterm: `have h : (1.0 : ℝ) * √(1.0 : ℝ) = 1 := by have : (1.0 : ℝ) = 1 := by norm_num; simp [this, Real.sqrt_one]`, then `rw [h, mul_one]` before `interval_decide`. |
| `ht.1` or `ht.2` projection fails after `rw [Set.mem_uIcc]` | **Disjunction Not Conjunction**: `Set.mem_uIcc` gives `(a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)`, not a conjunction. Use `rw [Set.uIcc_of_le (by norm_num : a ≤ b), Set.mem_Icc] at ht` to convert to `Icc` first. |
| `change` failed with definitional equality error | **Definitional Mismatch for Pointwise vs Point-Free**: Typeclass resolution or type coercions (like `↑x` or `HPow.hPow`) can block definitional equality check in `change`. Use a propositional equality helper instead: `have h_eq : (fun s ↦ f s * g s) = f * g := by ext1; rfl` and rewrite using `rw [h_eq]`. |
| `linarith` failed to find a contradiction on `WithTop ℤ` | **Non-Ring Typeclass Restriction**: `linarith` only operates on linearly ordered rings/fields/semirings. `WithTop ℤ` is not a ring, so `linarith` treats order relations on it as opaque. Use order-theoretic contradiction lemmas like `not_lt.mpr` or `not_le.mpr` directly. |
| `Invalid projection: Projections cannot be used on functions` | **Negated Conjunction as Function**: A hypothesis like `¬(P ∧ Q)` from the False branch of `split_ifs` is definitionally `P ∧ Q → False`. Do not project with `.1`/`.2`. |
| `Invalid field integral` | **Dot Notation Removal**: `μ.integral f` is no longer supported in Mathlib4. Use standard function application `integral μ f`. |
| `positivity` fails on custom `def` | **Definitional Opacity**: `positivity` operates syntactically and cannot see through custom `def` wrappers (like a custom magnitude function). Unfold the `def` first. |
| `unexpected token 'sorry'; expected ':='` | **Calc Block Strictness**: A hanging `sorry` after an `apply` inside a `calc` step breaks the parser. Use `:= sorry` directly or wrap properly in `by ...`. |
| `don't know how to synthesize implicit argument` | **Unused Implicit Parameter**: A polymorphic structure (e.g., `{p d : ℕ}`) that doesn't use `d` in its fields cannot infer `d` automatically when instantiated. |
| `Application type mismatch` on `Fin.elim0` | **Prop vs Type Trap**: `Fin.elim0` returns data (`Type`), but a proof (`Prop`) over an empty domain is expected. Use a proof lambda `fun j => j.elim0`. |
| `failed to synthesize instance ... InnerProductSpace ℝ (ι → ℝ)` | **Missing L2 Instance**: Mathlib does not put a default inner product on standard function types `ι → ℝ` to avoid diamond issues with other Lp norms. Use the `EuclideanSpace ℝ ι` type synonym instead. |
| `failed to synthesize instance ... InnerProductSpace ℝ (E × F)` | **Product Topologies are L∞**: Mathlib assigns the $L_\infty$ maximum norm (`max ‖u‖ ‖v‖`) to standard product types, which does not induce an inner product space. Use `WithLp 2 (E × F)` for the $L_2$ product topology. |
| `failed to synthesize instance ... HDiv (EuclideanSpace ...)` | **No Vector Division**: `EuclideanSpace` has a `Module` instance but no overloaded division by scalars. Use scalar multiplication `(c⁻¹ : ℝ) • v` or `(1/2 : ℝ) • v`. |
| `field_simp` made no progress | **Definition Opacity / Import Sensitivity**: `field_simp` works on exposed fractions and relies on the global `simp` set. A new upstream import can change the `simp` set and break it. Unfold definitions with `dsimp` first. |
| Type mismatch on `WithLp.equiv` | **Equivalence Directionality**: `WithLp.equiv p α` maps *from* the $L_p$ space *to* the base type `α`. To cast a raw function into the $L_p$ space, you must use its inverse: `(WithLp.equiv p α).symm`. |
| `positivity` fails on `x * x` | **AST Rigidity**: `positivity` recognizes `x ^ 2` but treats `x * x` as generic multiplication. Use `mul_self_nonneg`. |
| `failed to compile definition ... decidableLE` | **Noncomputable Arithmetic**: Filtering sets on real inequalities (e.g. `|w^T x| ≤ \tau \|x\|`) requires classical logic. Add `noncomputable def`. |
| `failed to synthesize instance ... Fintype ℕ` for `Measure.pi` | **Infinite Products**: `Measure.pi` strictly requires finite index types. For countable products over `ℕ`, use `MeasureTheory.Measure.infinitePi`. |
| `x ⊙ y = y ⊙ x` parses as `(x ⊙ y = y) ⊙ x` | **Precedence Collision**: Custom algebraic notations (like `⊙`) must have precedence strictly higher than equality (50), e.g., `infixl:73`. |
| `failed to synthesize instance ... MeasurableSpace (EuclideanSpace ...)` | **Type synonym mismatch**: `EuclideanSpace` does not inherit `Pi.measurableSpace` by default. Provide it via `variable [MeasurableSpace ...]` but ensure lemma signatures do not shadow the `d` variable. |
| Type mismatch on `1` for `EuclideanSpace` | **Missing OfNat instance**: Vector spaces typically lack `One`. Use `(EuclideanSpace.equiv _ _).symm (fun _ ↦ 1)`. |
| `failed to synthesize instance ... IsGaussian (Measure.pi ...)` | **Missing Fintype Instance**: Mathlib does not provide a blanket `IsGaussian` instance for `Measure.pi` over a generic `Fintype` index set out of the box. You must explicitly construct it or tie it to `stdGaussian`. |
| `typeclass instance problem is stuck IsOrderedRing ?m` | **Metavariable in Coercion**: Using an unconstrained cast like `Nat.cast_nonneg _` inside a complex `simp` leaves the target type ambiguous (`?m`). Explicitly provide the argument, e.g., `Nat.cast_nonneg (card S)`. |
| `Type mismatch` when passing `fun x ↦ ...` to a lemma expecting `E →L[ℝ] ℝ` | **Continuous Linear Map Requirement**: Lean will not automatically coerce a bare function to a `StrongDual` (Continuous Linear Map). Use `LinearMap.toContinuousLinearMap` to construct the bundled map explicitly. |
| `tactic 'linarith' failed to find a contradiction` on `↑S.card ≤ 2 * S_bound` | **Syntactic Equivalence & Non-negativity Blindspot**: `linarith` treats `r` and `B^(2/3)/m^(1/3)` as distinct free variables if not definitionally unfolded, and cannot infer non-linear bounds (like `(B/r)^2 ≥ 0` or `√(...) ≥ 0`) automatically. Use `dsimp [S_bound]` or `rw [← h_r_def]` to unify terms and pass non-negativity hypotheses explicitly into `linarith [h_S_card, h_mr, h_sqrt, h_br]`. |
| `nlinarith` fails on real powers `x ^ (4/3 : ℝ)` | **Non-Integer Exponent Opacity**: `nlinarith` only automatically deduces non-negativity for integer squares ($x^2 \ge 0$). Prove non-negativity using `Real.rpow_nonneg` and pass explicit hypotheses to `nlinarith [h_rpow_nonneg]`. |
| `Application type mismatch` on `div_le_div_of_nonneg_right` | **AST Parenthesization Rigidity**: `a * (b / c)` is syntactically distinct from `(a * b) / c`. `div_le_div_of_nonneg_right` expects `(a / c) ≤ (b / c)`. Re-parenthesize with `ring` or `rw [mul_div_assoc]` before applying division order lemmas. |
| `Application type mismatch` on `exact mul_nonneg h1 h2` (EuclideanSpace) | **Type Inference on `EuclideanSpace` Sub-terms**: The hypothesis `0 ≤ q i` infers a type based on the base space, whereas the goal expects terms cast through `WithLp.equiv` (e.g. `q.ofLp i`). Explicitly provide named implicit arguments `(a := q.ofLp i) (b := z.ofLp i)` to guide the typechecker. |
| `Unknown constant MyStruct.field` | **Prop Structure Projections**: Lean 4 does not auto-generate projection functions (e.g., `.nonneg` or `.symm`) for `structure` definitions in `Prop` (unless they are a `class`). However, it *does* reserve the field names. You cannot use dot notation or `MyStruct.field`. **Fix**: Define manual getter lemmas with different names (e.g., `lemma MyStruct.get_field`) and use `cases h` to destruct the structure internally to extract the field. |
| `Tactic rcases failed: ... is not an inductive datatype` | **rcases on Prop Structures**: When `rcases` is applied to a `Prop` structure, it unwraps the structure. If the underlying field has a dependent function type, `rcases` gets confused and fails, leaking the unwrapped type in the error message. **Fix**: Use the built-in `cases` tactic instead, which handles Prop structures more robustly without aggressive type unfolding. |
| `unexpected token 'λ'; expected command` after an otherwise-fine `rcases ... with hλ0 \| hλpos` | **Greek `λ` Is a Reserved Token, Not an Identifier Character**: Lean 4 reserves the bare Greek letter `λ` as alternative syntax for `fun`, so it cannot appear *inside* a user-chosen identifier (`hλ0`, `hλpos`), even though other Greek letters (`ε`, `α`, `ι`) are fine. The parser silently mis-names the pattern variable (Lean 4's diagnostics may even show an unrelated later `unsolved goals` error first, since the parse failure aborts the rest of the tactic block). **Fix**: spell out `lambda` in identifiers (`hlam0`, `hlampos`) — matches this project's existing convention of naming the parameter itself `lambda` rather than `λ`. |
| `rw [hx0] at hmono` fails to find `posEffectiveParameter u 0` although the type of `hmono` prints it | **Antitone/Monotone Beta-Redex**: `(tiltedLoss_antitone_along_pos_flow ... ht : (fun t => f t) t ≤ (fun t => f t) 0` is not beta-reduced automatically, so its *displayed* type looks rewritable but the underlying term is a `(fun t => ...) 0` redex that `rw` cannot match syntactically (the same family as the point-free vs. lambda trap in §3.1, but arising from `Antitone`/`Monotone` application rather than `deriv`). **Fix**: use `simp only [hx0] at hmono` (simp beta-reduces as part of normalization) instead of `rw [hx0] at hmono`. |

### 1.2 Metavariable Poisoning (The "Silent Killer")
**The Problem:** An unknown identifier, a failed `apply`, or a polymorphic theorem where implicit arguments are missing causes Lean to assign a metavariable (e.g., `?m.403`), which renders as `sorry ()` in the infoview.
**Polymorphic Theorem Grounding:** Theorems like `integrable_zero` have an implicit target space `ε'`. If you pass them into another lemma (like `Integrable.congr`) without grounding the target type, Lean will create a metavariable `ε'✝` and fail to synthesize its `TopologicalSpace` instance.
**The Fix:**
1.  **Grounding**: Always provide an explicit type for polymorphic theorems: `integrable_zero (ε' := ℝ)`.
2.  **Elaboration Order**: Ignore the immediate failing tactic. Scroll to the **earliest** elaboration error in the file and fix that first.
3.  **Type Anchoring**: In `have` blocks, use `show exact_type; sorry` to force Lean to verify the statement's type.

### 1.3 Filter Transformation Strategy: The "Triple Move"
**The Pattern:** Mapping integrability from `atBot` to `atTop` (or vice versa) requires a synchronized "Triple Move" across three domains:
1.  **The Filter**: Transform the filter using a mapping lemma (e.g., `Filter.map_neg_atTop : map neg atTop = atBot`).
2.  **The Integrand**: Compose the function with the mapping operation (e.g., `f ∘ neg`).
3.  **The Measure**: Transform the measure (e.g., `volume.comap neg`).
**The Pitfall:** Transforming only one or two of these leads to "IntegrableAtFilter" goals that are mathematically correct but syntactically unprovable due to measure-filter mismatches. Use `MeasurableEmbedding.integrableAtFilter_iff_comap` to perform the triple move atomically.

### 1.4 Measure Theory Typeclasses and `measureReal`
**The Problem:** `MeasureTheory` in Lean 4 heavily relies on typeclasses like `IsProbabilityMeasure μ` and `IsFiniteMeasure μ`. For product measures (like `Measure.pi`), these are not automatically inferred unless the marginal measures explicitly provide them. If missing, tactics like `simp` or `apply` will fail cryptically or leave unresolvable metavariables.
**The Fix:** Always verify that the underlying 1D measures have the appropriate instances. If applying theorems about `measureReal` (like `measureReal_mono`), remember that unlike `ENNReal`, real-valued measures require explicit finiteness proofs (`IsFiniteMeasure μ` or `μ t ≠ ∞`).

### 1.5 Casing and Indicators for Algebraic Tactics
**The Problem:** Algebraic tactics (`ring`, `linarith`) cannot dismantle piecewise functions, absolute values (`|x|`), or `max a b` directly.
**The Fix:** Use `split_ifs` to break down `if-then-else` indicators, and `rcases le_total 0 a with ha | ha` to dismantle absolute values or ReLU functions into linear pieces that `linarith` can handle.

---

## 2. The Golden Rules of Workflow

### 2.1 Rule 1: Verify Before Implementation
**Never** write a lemma name into the source code unless its existence and signature have been confirmed in the **current turn** via `#check`, `grep`, or `exact?`. "Plausible" or "intuitive" names (e.g., `abs_le_of_le_of_le`) are almost always incorrect. Using a hallucinated name lead to immediate compilation failure and metavariable poisoning (see 1.2).

**Signature Check:** Use `grep -A 2` or `#check` to confirm the exact number and types of arguments. Many lemmas (e.g. `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`) have specialized signatures that only handle specific base cases. Use `@lemma_name` to see all implicit arguments and typeclass requirements.

**Variable Argument Inflation:** In Mathlib source files, `variable` blocks in sections often turn implicit properties or measures into **explicit arguments** for all theorems in that section. A theorem header like `theorem foo (f : E → F)` might actually require `Measure.foo μ f` if `μ` was a `variable` in its source file. Always check the full signature using `#check`.

**Current-Context Verification vs Source-File Verification:** Seeing a theorem in a Mathlib source file is not enough. You must also verify the name in the **current import context**. A theorem may exist only under a fully qualified namespace (`ProbabilityTheory.IndepFun.integral_bilin`), while a shorter name you guessed (`IndepFun.integral_bilin`) is unavailable and will fail with `unknown identifier`. The correct workflow is:
1. search source files to find candidate lemmas;
2. `#check` the **exact fully qualified name** in a scratch file importing the same modules as the target file;
3. only then write it into the real proof.

**Import-Direction Check:** `grep` searches text on disk, not the transitive import closure, and Mathlib's import arrows are not always in the direction you expect. Verified instance: `ProbabilityTheory.iIndepFun_infinitePi` is declared in `Mathlib/Probability/Independence/InfinitePi.lean`, which *imports* `Mathlib/Probability/ProductMeasure.lean` — so a file importing only `Mathlib.Probability.ProductMeasure` gets `Measure.infinitePi` and `infinitePi_map_eval` but **not** `iIndepFun_infinitePi` (`unknown identifier`). Before using a grep-found lemma, either inspect the import arrow (`grep "^import" <declaring file>`) or, faster, `#check` the name in the scratch preamble (Rule 8) first — one compile catches all such failures at once.

### 2.2 Rule 2: Editing Precision
**Small, contiguous edits are safer than large block replacements.** This is not a style preference; it is a correctness requirement. A single large edit can silently delete a hypothesis or shift the targets of all subsequent replacements.
- **One logical change per edit.** Never replace more than ~10-20 lines in a single operation unless the block is entirely self-contained.
- **Use Content-Based Matching:** Use tools like `multi_replace_file_content` that target specific strings rather than line ranges to avoid "line-number drift".
- **Target Content Precision:** `multi_replace_file_content` will fail silently if the `TargetContent` does not match the file's exact string perfectly (e.g., missing or extra implicit variables in a lemma signature). Always verify the exact signature using `view_file` or `grep_search` before running the replacement.
- **Verify after every edit:** Use `view_file` to confirm the surrounding context matches your mental model.
- **The "Duplicate Line" Symptom:** If a `multi_replace` call accidentally duplicates a line (e.g., `refine ...` appearing twice), the IDE will report a `Type mismatch` or `No goals to be solved` on a line that looks syntactically correct. Always check the `view_file` output for the *entire block* after a complex replacement to ensure no duplicate injections occurred.

### 2.4 Rule 4: Atomic-to-Consolidated Workflow
When a "Big Tactic" (like a long `simp only` list or `field_simp`) fails, deconstruct it into atomic `rw` calls. This reveals the exact subterm (e.g., `|T⁻¹|` vs `|T|`) that prevents syntactic matching. Only consolidate the proof into a single block after every atomic step is verified.

### 2.5 Rule 5: Linter Skepticism (Unification vs. Algebra)
- **Unification Tactics** (`convert`, `congr`) can often unify `•` and `*` via argument matching.
- **Algebraic Tactics** (`ring`, `field_simp`) are syntactically rigid and treat `•` as an opaque atom.
- **The Lesson**: If a linter suggests removing a normalization lemma, check if a subsequent algebraic tactic in the same block will require that normalization.
| `continuousAt_const (b := ...)` | Named argument for the constant value. | **Hallucinated Parameter.** The argument is named `y`. Use `(y := ...)` or rely on unification. |

### 2.6 Rule 6: Exact Over Brittle Rewriting
**The Problem:** Rewriting (`rw`) is sensitive to the syntactic form of coercions. A goal might contain `Neg.neg` while a lemma uses `⇑(MeasurableEquiv.neg ℝ)`. These are definitionally equal but syntactically distinct, causing `rw` to fail.
**The Fix:** Use `convert` or `exact` with the specific proof term. For example, `exact (MeasurableEquiv.neg ℝ).map_symm.symm` successfully bridges the gap between `comap Neg.neg` and `map Neg.neg` where `rw` fails.

**`integral_map` Orientation Trap:** `MeasureTheory.integral_map` is oriented
`∫ y, f y ∂ Measure.map φ μ = ∫ x, f (φ x) ∂μ`.
If your goal is written as `∫ x, f (φ x) ∂μ = ...`, a direct `rw [MeasureTheory.integral_map ...]` often fails with "Did not find occurrence" because the theorem matches the opposite side and with a different binder shape. The robust pattern is a `calc` block:
```lean
calc
  ∫ x, f (φ x) ∂μ = ∫ y, f y ∂ Measure.map φ μ := by
    symm
    exact MeasureTheory.integral_map hφ hf
  _ = ...
```
Do not force this with repeated `rw`; switch to `calc` as soon as orientation becomes nontrivial.

**`MeasurableEmbedding.integral_map` vs `MeasureTheory.integral_map`:** `MeasureTheory.integral_map` is highly demanding, requiring `AEMeasurable` for the embedding and `AEStronglyMeasurable` for the function. For structural injections (like `w ↦ (w, true)`), prefer `MeasurableEmbedding.integral_map` and `MeasurableEmbedding.integrable_map_iff`, which take a `MeasurableEmbedding` directly and sidestep complex AE measurability conditions.

### 2.3 Rule 3: Pattern-Based Search
Search by mathematical pattern, not by guessed name.
- **Keyword Search:** `grep -rn "keyword" .lake/packages/mathlib/`
- **Concept Search:** Use `leansearch` for word-based queries (e.g., "integral of product").
- **Type-Structure Search:** Use `loogle` with wildcards like `loogle "(?a → ?b) → List ?a → List ?b"`.
- **Naming Conventions:**
    - Implication: `conclusion_of_hypothesis` (e.g., `continuous_of_isOpen_preimage`)
    - Equivalence: `property_iff_characterization` (e.g., `compact_iff_finite_subcover`)
    - Operation: `operation_structure` (e.g., `integral_add`, `measure_union`)
    - Non-negativity: `lemmaName₀` (e.g., `pow_le_pow_left₀`)

### 2.7 Rule 7: Modularize Tactic-Heavy Subgoals
When dealing with a master theorem that involves multiple long `linarith` or `simp` sequences (like proving integration bounds for multiple segments), extract them into `private lemma` helpers. This localizes failures immediately, prevents the main theorem body from bloating, and avoids repeating complex context setup.

### 2.8 Rule 8: The `scratch.lean` Verification Workflow
Relying exclusively on the main file for testing tactic blocks often yields cascading, obscure IDE lint errors because Lean tries to evaluate the entire file state. By isolating your proof steps in a `scratch.lean` file and running `lake env lean scratch.lean`, you can iterate rapidly. Ensure that you only inject mathematically sound, `sorry`-free proofs into the main project.
**Background Task Trap**: When running `lake env lean scratch.lean` asynchronously, do not assume success just because `cat task.log` is temporarily empty or outputs "completed successfully" without errors. Always wait for the definitive `<SYSTEM_MESSAGE>` that explicitly prints the final exit code. A missing identifier or failed typeclass instance might be flushed to the error log slightly after the process terminates.

**The `#check` Preamble:** Start every scratch file with a batched block of `#check @Candidate.lemma.name` lines for *every* library lemma the proof plan touches (10+ lines is fine). One compile (~10-15 s) then validates all names, namespaces, arities, and instance arguments at once — e.g. it reveals that `Measure.infinitePi_map_eval` takes the measure family `μ` as an **explicit** argument (Variable Argument Inflation, Rule 1) *before* you write proof code around the wrong signature, and it catches missing imports (Import-Direction Check, Rule 1). Fix all `unknown identifier`/signature errors in the preamble before writing a single tactic; this keeps every subsequent error local to the proof step that caused it. In the NTK SLLN session, a 10-line preamble caught 5 independent errors in one compile, and the main file then compiled on the first attempt after porting.

**Source Elaboration Does Not Refresh an Imported `.olean`:** Running `lake env lean Path/To/Changed.lean` checks that source file directly, but a separate scratch file which imports the changed module can still load the module's older compiled `.olean`. The resulting `unknown identifier` is particularly misleading: the declaration is visibly present in the source and the source itself compiles. Before importing newly added declarations in a scratch file, run a targeted `lake build` for that module. During rapid development, an even safer alternative is to import only stable dependencies and restate the candidate lemma locally in the scratch file. Distinguish this compiled-artifact problem from Rule 13's stale editor diagnostics: both display obsolete information, but only rebuilding the module refreshes an imported `.olean`.

### 2.9 Rule 9: Skeleton-First Proof Development
For lengthy proofs (like Maurey sampling bounds), writing a single monolithic tactic block is an anti-pattern. Instead, establish a "skeleton" using `have` statements for each required hypothesis (e.g., `hC`, `hN`, `hF_meas`, `hF_L2`) and temporarily `sorry` them out. This bounds the context, proves that the overall logical architecture is correct, and allows you to systematically conquer the proof one lemma at a time.

### 2.10 Rule 10: Calculus and Mean Value Theorem Strategy
**The Problem:** Bounding terms like `|σ(r) - σ(s) - σ'(s)(r - s)|` using the integral form of the Taylor remainder (`\int_s^r ...`) leads to an explosion of measure theory preconditions (e.g., proving `IntervalIntegrable`, `Measurable`, and reasoning about `uIcc`). The analytical overhead often makes simple algebraic inequalities intractable.
**The Fix:** Avoid integration for basic scalar calculus bounds unless absolutely necessary. Instead, use algebraic construction combined with the Mean Value Theorem (`exists_hasDerivAt_eq_slope`). Construct an auxiliary function `g(t)` such that `g(s) = 0` and `g(r) = 0`, then apply the MVT repeatedly to extract the Lagrange remainder purely algebraically.

### 2.11 Rule 11: Exact Signatures in Scratchpads
When moving a theorem to a `scratch.lean` file (Rule 8), always copy the exact signature and context (variables/implicits) from the main file. Lean 4 does not always auto-implicit variables (like dimension sizes `{d m : ℕ}`) inside complex structures unless they are explicitly declared in the scratchpad's context.

### 2.12 Rule 12: Monolithic `calc` Blocks are Anti-Patterns
Translating long, multi-step algebraic inequalities into a single massive `calc` block overwhelms the Lean kernel, causes timeouts, and generates cascading errors where a type mismatch at the end manifests as an error at the beginning. Break long proofs into isolated `have` lemmas (e.g., `have h_bound1 : ...`, `have h_bound2 : ...`). This allows the type-checker to process each step instantly, localizes errors, and makes fixing type coercions trivial.

### 2.13 Rule 13: Beware of Stale IDE Lint Errors (The "Ghost Error" Trap)
When performing large refactors across multiple files, if a core dependency file fails to compile due to a severe type error, Lean 4 may halt AST generation for all downstream files. The IDE infoview will then freeze and continue to display **obsolete** lint and type errors for those downstream files, even after you have fixed the underlying code.
**The Trap**: Attempting to "fix" these frozen errors will cause you to break perfectly valid code.
**The Fix**: Whenever a multi-file dependency chain is involved and IDE feedback seems contradictory, **always run a synchronous `lake build`** (via terminal) to force a fresh compilation and obtain the absolute ground-truth AST state before making further edits.

### 2.14 Rule 14: Parallel Build Output Truncation
When running a global `lake build` (e.g. `lake build LeanMachineLearning`), Lean builds dependencies in parallel. If a foundational file fails (e.g. due to a missing import), the terminal output might truncate that specific failure and only show the success of independent branches, ending with "Build completed successfully (N jobs)". This causes downstream files to throw confusing `unknown identifier` errors (especially with `autoImplicit` off). **Fix:** If a downstream identifier is inexplicably missing, run a targeted build of that specific downstream file (e.g., `lake build LeanMachineLearning.Optimization.Lasso.Theorems`) to force Lean to trace the exact failure path through the dependency graph.

### 2.15 Rule 15: The `scratch.lean` Main File Hang Trap
If your `scratch.lean` file imports the main project file (e.g., `Kernel.lean`), and the main file currently has a hanging tactic (like `rintro rfl`), running `lake env lean scratch.lean` will hang during the build of the main file. Always ensure the main file is syntactically terminating (even if filled with `sorry`s) before testing dependencies in a scratchpad.

### 2.16 Rule 16: Detect Defeq Loops Early
When a Lean task runs over 30 seconds on a simple geometric or algebraic goal, it is almost certainly stuck in a defeq loop. Do not wait for it to finish. Use the `manage_task` tool to check `status` and `kill` these runaway tasks to save time and compute, then inspect the last tactic applied (often `rfl`, `aesop`, or `simp` on heavy structures). For heavy automation in scratch files, wrap `#synth` or tactics with `set_option synthInstance.maxHeartbeats 1000` to force a fast failure instead of hanging the background task.

### 2.17 Rule 17: Isolate Tactic-Shape Failures in a Scratch File Immediately, Not After a Second Guess
**The Problem:** When a tactic combination (especially derivative/algebra combinators like `.sub`, `.add`, `convert ... using n`, `abel`) fails with an opaque error inside a long, deeply-wrapped proof (`EuclideanSpace`/`WithLp`/`set`-bound locals), it is tempting to try a second variant directly in the main file. This wastes a full compile-debug cycle because the surrounding wrappers obscure which part of the combination actually failed.

**The Fix (verified, Lasso `MirrorFlow.lean` session):** The moment a tactic-shape failure cannot be explained from the error message alone, reproduce the *exact* combinator chain in a 10-15 line scratch file with abstract types (`variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]`, `f g h : ℝ → E`), stripped of all project-specific wrappers. Concretely: `convert ((hf.sub hg).add hh) using 1; abel` failed inside the real proof with `abel_nf made no progress on the goal`, and the error alone gave no clue why. The abstract scratch reproduction immediately revealed that `(hf.sub hg).add hh : HasDerivAt (fun τ => f τ - g τ + h τ) (f' - g' + h') τ` is **already** the eta-expanded form needed — `HasDerivAt.sub`/`.add` unfold through `Pi.sub`/`Pi.add`, which are definitionally the pointwise lambda — so `convert ... using 1` was never necessary. The actual fix was to `rw` only the *derivative value* to `0` via a separately-proved `have hval : f' - g' + h' = 0 := by abel` and then `rw [hval] at hsum; exact hsum`. Apply this "isolate before re-guessing" discipline to *every* opaque tactic-combinator failure, not just to lemma-name lookups (Rule 1 already covers that narrower case).

### 2.18 Rule 18: Never Hallucinate Mathematical Bounds (No Goal Forcing)
**The Problem:** When faced with a complex differential inequality (like the product-rule derivative of `Eᵋ(s)/(1+sλ)`), if the algebraic expansion yields multiple terms but the tactic state seems too hard to manage, it is extremely tempting to simply "drop" the difficult terms (like the complementarity defects) and try to prove that the derivative is bounded *solely* by the easy term (the dual path bound).
**The Result:** You end up formalizing a mathematically false statement. Lean will never let you prove it, and you will waste hours fighting with `nlinarith` and `positivity` on a goal that is fundamentally untrue.
**The Fix:** Always verify your formalized theorem against the ground-truth textbook/notes equation (e.g., Eq. 806). If the math says there are 5 terms, your Lean theorem must account for all 5 terms. Do not hallucinate a stronger, simplified bound just because it looks easier to type.

### 2.19 Rule 19: API Extraction over Goal State Bloat
**The Problem:** Translating a large algebraic summation (like 4 distinct complementarity defect bounds) directly inside a massive `calc` block leads to a completely unreadable goal state, making it impossible to see the structure of the proof and causing Lean to time out on typeclass resolution.
**The Fix:** Extract complex algebraic sub-components into **reusable API helper lemmas** with `sorry`.
1. Define a helper lemma (e.g., `energy_complementarity_bound`) that encapsulates exactly the algebraic defect terms and provides the global bound.
2. Define a helper lemma (e.g., `dual_path_derivative_inner_bound`) that encapsulates the Cauchy-Schwarz bound.
3. Prove the main theorem by simply summing these two API lemmas with `add_le_add`.
This approach keeps the main proof structural, localized, and strictly aligned with the textbook's narrative flow.

---

## 3. Tactic Mastery & AST Awareness

### 3.1 Rewriting and the AST (Abstract Syntax Tree)
`rw` operates on the AST, not the visual display.
- **Syntactic Match:** `rw` is a syntactic pattern matcher. `-(π/4)` and `-π/4` are different AST nodes (`Neg (Div π 4)` vs `Div (Neg π) 4`); `rfl` and `exact` will fail on them. Use `ring`, `norm_num`, or `linarith` to bridge.
- **Coercion Grouping (The "Hidden Coercion" Trap):** `rw [Complex.re_ofReal_mul]` (pattern `(↑r * z).re`) will fail if your term is `(↑r1 * ↑r2 * z).re`. Multiplication is left-associative, so Lean sees `((↑r1 * ↑r2) * z).re`. The first factor `(↑r1 * ↑r2)` is a complex product, not a single coercion `↑r`. **Fix**: Use `norm_cast` or `rw [← Complex.ofReal_mul]` first to gather the real factors.
- **Visual Deception:** `set_integral univ f` and `integral f` look identical in the infoview but are different nodes. Use `show` or `set_option pp.all true` to reveal the true AST.
- **Dependent Binder Domains:** Equalities like `n = 189` do not rewrite transparently inside binder domains such as `fun j : Fin (n + 1) ↦ ...` or hidden parameters like `@επ_num n ...`. First expose the hidden parameter with `change @foo n ...`; then perform the transport in a small auxiliary goal rather than trying `rw` or `simpa` directly on the main target.
- **L-to-R Scanning:** `rw` picks the first matching term. In `|a|/|b|`, `rw [abs_of_pos]` will fail if the numerator isn't positive. Use `nth_rw` to target denominators.
- **Definitional Projections:** Use `erw` when the goal has `(f x).re` but the lemma uses `RCLike.re` (definitional but not syntactic identity).
- **Point-free vs Lambda:** `deriv (fun w ↦ f w / g w) z` and `deriv (f / g) z` are eta-equal but syntactically distinct. `rw` will not see through this. Use `change` or `dsimp` to normalize.
- **Notation Precedence Collision:** Assigning precedence 50 (the same as equality) to a custom algebraic operator (like `notation:50 x " ⊙ " y`) causes catastrophic left-to-right parsing errors. An equation like `x ⊙ y = y ⊙ x` will parse as `(x ⊙ y = y) ⊙ x`. Always use strictly higher precedence like `infixl:73` for arithmetic operations.
- **`Set.mem_uIcc` Disjunction Trap:** `Set.mem_uIcc` rewrites membership to a **disjunction** `(a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)`, not a conjunction. Attempting `.1`/`.2` projection on the resulting hypothesis will fail with "invalid field notation." Fix: when the interval direction is known (`a ≤ b`), use `rw [Set.uIcc_of_le (by norm_num : a ≤ b), Set.mem_Icc] at ht` to first normalize `Set.uIcc a b` to `Set.Icc a b`.
- **Root-Operation Rigidity:** `apply` and `rw` only see the "outermost" operation of a term. If a goal is `(-T) * log x \le 0`, `apply neg_nonpos.mpr` (which expects `-(T * log x) \le 0`) will fail because the root of the goal is `*`, while the lemma expects `-`. **Fix**: Use `rw [neg_mul]` or `rw [← neg_mul]` to move the negation to the root of the expression before applying order lemmas.
- **Set Preimages and Definitional Equivalence:** Lean aggressively simplifies preimages and complements definitionally. When evaluating `(fun z => z.1) ⁻¹' Sᶜ`, Lean treats `z ∉ N` as `¬ (z.1 ∉ S)`. Untangling this double negation is better handled by primitive logic like `by_contra h; exact h_not h` rather than hunting for specific hallucinated set lemmas like `Set.not_mem_compl_iff.mp`.
- **Scoped Notation Does Not Travel:** Notation is enabled per-file by `open`/`open scoped`, and the pretty-printer (and Mathlib source you copy from) shows the notation without its enabler. Copying a statement fragment across files therefore copies the notation but not the `open` that makes it parse. Verified instances: `(· ⟂ᵢ[μ] ·) on X` fails with `unknown identifier 'on'` without `open Function` (`on` = `Function.onFun`); `𝓝` fails without `open Topology`. **Fix:** add the `open`, or write the scope-free form (`Function.onFun (· ⟂ᵢ[μ] ·) X`, `nhds`). First grep the *target* file for how it already writes the concept (e.g. `Kernel.lean` spells `nhds` everywhere) and match that convention.
- **Higher-Order Rewrite Patterns Need Explicit Functions:** `rw` is a syntactic matcher with weak higher-order unification. `rw [Fin.sum_univ_eq_sum_range]` (pattern `∑ i : Fin n, ?f ↑i`) fails with "Did not find occurrence" on the goal `∑ j : Fin n, ntkSummand σ' x x' (rows ↑j)` because `?f ↑j` must be abstracted out of the nested application `ntkSummand σ' x x' (rows ↑j)`. **Fix:** pass the function (and index) explicitly so matching becomes first-order: `rw [Fin.sum_univ_eq_sum_range (fun i => ntkSummand σ' x x' (rows i)) n]`. Alternative: `simp only [Fin.sum_univ_eq_sum_range]`, whose matcher handles such patterns more robustly. Rule of thumb: whenever a rewrite lemma takes a function as an explicit argument and the target body is more than a top-level `F i`, supply the function.

### 3.2 Normalization (Algebraic & Casting)
- **Field Simp:** Requires syntactic witnesses. Create `have h_denom : expr ≠ 0 := ...` matching the denominator exactly. Unfold aliases like `coth` or `tanh` first to synchronize internal representations.
- **Ring vs Denominators:** Clear all denominators with `field_simp` before calling `ring`. `ring` treats `⁻¹` as an opaque atom and cannot derive `x * x⁻¹ = 1`.
- **The "Field-Simp Sandwich":** When simplifying identities like `(x-1)/(x-1) = 1`, `field_simp` may fail if the numerator and denominator are syntactically different (e.g., `x - 1` vs `x + -1`). **Protocol**: (1) Use `rw [← sub_eq_add_neg]` to unify the syntax; (2) Use `field_simp [witnesses]` to clear denominators; (3) Use `ring` to solve the numerator. Avoid calling `ring_nf` while denominators or inverses are present, as it will distribute the numerator across the inverse (e.g., `σ * A - A`), making cancellation impossible.
- **Field_simp vs Real Powers:** `field_simp` only operates on terms in the `Field` typeclass (i.e., `/` and `⁻¹`). It treats real powers (`Real.rpow`) as **opaque atoms** (Rule 109). Even if terms like $x \cdot x^{-\sigma}$ appear in the goal, `ring` and `field_simp` will not simplify them to $x^{1-\sigma}$. You must explicitly unify the exponents using `Real.rpow_add`, `Real.rpow_add_one`, or `Real.rpow_sub_one` before calling the algebraic solvers.
- **Coercions are Opaque:** `-↑z.re` is `Neg (ofReal z.re)`. `apply` will fail if it expects `ofReal (-z.re)`. Use `push_cast` or `rw [← Complex.ofReal_neg]` to move negation inside.
- **Projection Opacity (.re / .im):** The real-part projection `.re` acts as a rigid wrapper. Algebraic tactics like `ring` treat `(z).re` as a black box and will not distribute over `+` or `*`. Furthermore, `.re` blocks syntactic matching: `Complex.add_re` (pattern `(z + w).re`) will not fire if the addition is inside a multiplication (e.g. `(Multiplier * (A + B)).re`). You must **Expand** (distribute) outer multipliers before you can **Linearize** (split) the projection. **Note**: If the multiplier is real, `rw` will still fail unless the multiplier is a **single** `↑r` node (see Coercion Grouping in 3.1).
- **Notation Unfolding & Projection Failure:** Dot-notation (e.g., `h.integrable_iff`) for notations/aliases like `EventuallyEq` (`=ᵐ`) will fail if Lean has "seen through" the notation to its raw measure-zero definition. Once unfolded, the namespace-based projection system cannot find the lemma. **Fix**: Use the functional form `Filter.EventuallyEq.integrable_iff h` to force the application.
- **The Scalar Bridge (• vs *):** Scalar multiplication (`•`) is a "blind spot" for `ring` and `field_simp`. It treats `r • x` as an opaque operator. Always use `simp only [smul_eq_mul]` to convert it to standard field multiplication before using algebraic tactics or `convert`.
- **Scalar Multiplication (`•`) vs Real Multiplication (`*`) in Integrals:** Mathlib 4 makes a strict distinction between scalar multiplication (`c • f x`) and algebraic multiplication (`c * f x`). The canonical way to factor a constant out of an integral over a real vector space is to rewrite the multiplication into a scalar multiplication using `← smul_eq_mul`, apply `MeasureTheory.integral_smul`, and then revert back using `smul_eq_mul` (do not look for `integral_mul_left`).
- **Pre-simplifying transcendental inputs to `interval_decide`:** `interval_decide` fails to automatically evaluate expressions containing symbolic or unsimplified transcendental functions (like `log (exp 30)`). Simplify these using identity lemmas (like `log_exp 30`) to numerical constants before calling `interval_decide`.
- **`interval_decide` Sqrt Side Goal:** When `interval_decide` encounters expressions like `√(p/q)`, it normalizes them to `√p / √q` and emits the identity as an extra side goal (often a disjunction). Always check for remaining goals after `interval_decide` and close them with `left; ring` or `ring`.
- **`interval_bound` Fraction Normalization Mismatch:** `interval_bound n` internally normalizes decimal literals (e.g., `9.2211 → 92211/10000`) when constructing the interval certificate. When the proof result is applied to the original decimal literal, this causes a type mismatch (`92211/10000` vs `9.2211`). Ensure the `∀ x ∈ Set.Icc` bounds and the instantiation point both use the same literal form.
- **Numeric Literal Non-Definitional Equality (`44` vs `44.0`):** `(44 : ℝ)` is elaborated via `OfNat` while `(44.0 : ℝ)` is elaborated via `OfScientific`. These are propositionally but **not definitionally** equal, so `exact` and `linarith` cannot bridge them automatically. Use `have : (44 : ℝ) = (44.0 : ℝ) := by norm_num` then `linarith`.
- **Zero Literal Coercion Mismatch (`(0 : ℝ)` vs `↑0`):** `(0 : ℝ)` elaborates via `OfNat` to `0`, whereas `Nat.cast 0` elaborates to `↑0`. Tactics like `positivity` or theorems expecting explicit `Nat.cast` bounds (like `div_nonneg` combined with `Nat.cast_nonneg`) will fail with `Type mismatch ... 0 ≤ 0 vs 0 ≤ ↑0`. **Fix:** Omit the explicit `(0 : ℝ)` type signature and let the elaborator unify the term directly, or explicitly write `Nat.cast_nonneg 0` instead of `(0 : ℝ)`.
- **`gcongr` non-negativity propagation for products:** `gcongr` on products requires all remaining factors in a product to be non-negative. If `positivity` cannot automatically deduce this, you must explicitly prove non-negativity beforehand in the local context (e.g., `have h_adm : 0 ≤ admissible_bound ...`) or fall back to manual order lemmas like `mul_le_mul_of_nonneg_right`.
- **`intervalIntegral.integral_nonneg`:** When proving the non-negativity of an interval integral, prefer `intervalIntegral.integral_nonneg` over `intervalIntegral.integral_nonneg_of_forall` if the integrand is only guaranteed to be non-negative on the integration interval `[a, b]` rather than globally.
- **Exponent Unification for `ring` (Reverse `rw` Direction):** `ring` and `ring_nf` treat different powers of a variable (like $y^k$ and $y^{k-1}$) as completely distinct, opaque algebraic variables (atoms). Thus, algebraic solvers cannot simplify or cancel them automatically. To resolve this, use a reverse rewrite `rw [← h_pow_sub]` (where `h_pow_sub : y * y ^ (k - 1) = y ^ k`) to replace the standalone `y ^ k` on the RHS with `y * y ^ (k - 1)`. This unifies all power terms under a single base atom `y ^ (k - 1)`, permitting `ring` to distribute and close the identity.
- **Symmetry Orientation:** Orient `simp` lemmas toward a canonical form (e.g., `f (-z) = f z`) to remove negations. Avoid providing lemmas in both directions to prevent infinite loops.
- **Definitional Evaluation for Deep Recursive Lookups (`dsimp` vs `simp`)**: Running `simp` on deep recursive definitions (like `List.getD` or list concatenation on concrete lists of length 199) with opaque parameters causes Lean's rewrite engine to blow up the stack, leading to the `maximum recursion depth has been reached` error. Instead, use definitional simplification (`dsimp [defs...]`) to unfold the opaque constants first, allowing Lean to evaluate recursive lookup logic definitionally and instantly.
- **Underlying Composition Exposure**: Standard library helpers like `List.getD` are defined via underlying operations (e.g. `Option.getD` and `List.getElem?`). When unfolding notation using `dsimp`, the outer helper is replaced by its constituent operations. You must include these underlying helper constants (`List.getElem?` and `Option.getD`) in the `dsimp` unfolding list so that they can be evaluated, otherwise the lookup will remain un-evaluated in the goal.
- **List.getElem Conversion for Simp**: The most efficient and standard way to evaluate list lookups in `simp only` is to convert `.getD` to standard `List.getElem` (`list[index]`) using `List.getD_eq_getElem` first, and then rewrite using the highly optimized `List.getElem_zero_cons` and `List.getElem_succ_cons` lemmas.
- **Standard List Append and getElem Naming Conventions in Lean 4**:
  * In Lean 4, list concatenation `++` compiles to `HAppend.hAppend`, which is simplified using `List.cons_append` and `List.nil_append` (not `List.append`).
  * The standard list lookup simplifier lemmas put the index before the constructor: `List.getElem_zero_cons` and `List.getElem_succ_cons` (not `cons_zero` or `cons_succ`).
| `intervalIntegral.integral_same` | `∫ x in a..a, f x = 0` | Simplifies integral over an empty interval (upper bound equals lower bound). | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `Real.log_exp` | `log (exp x) = x` | Unfolds exp/log composition (requires real `x`). | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.exp_le_exp` / `Real.exp_lt_exp` | `exp x ≤ exp y ↔ x ≤ y` / `exp x < exp y ↔ x < y` | Converts exponential inequalities to linear exponent inequalities. | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Real.div_rpow` | `(x / y) ^ z = x ^ z / y ^ z` | Distributes power over division (requires non-negative bases). | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.sqrt_sq` | `0 ≤ x → √(x ^ 2) = x` | Simplifies square root of square. | `Mathlib/Data/Real/Sqrt.lean` |

- **Translate Into the Library's Canonical Form:** Big theorems conclude in *their* normal form, not yours. Verified instance: `ProbabilityTheory.strong_law_ae` concludes `Tendsto (fun n => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω)) atTop (𝓝 μ[X 0])` — scalar multiplication `•`, a `Finset.range` sum, and `μ[f]` notation for the integral. If your own definition uses `*` and `∑ j : Fin n`, do not restate or fight the library theorem; bridge the forms with one conversion lemma each: `smul_eq_mul` for `• → *`, `Fin.sum_univ_eq_sum_range` for `range → Fin`, and remember `μ[f]` is notation for `∫ x, f x ∂μ` when rewriting the limit value. Proving `(fun n => ...) = (fun width => ...)` by `ext n` plus these two rewrites is short and robust.

### 3.3 Do Not Normalize Balanced Goals
Avoid calling powerful normalization tactics like `field_simp` or `simp` on goals that are already syntactically identical (e.g., `⊢ A * B = A * B`).
- **The Danger**: These tactics can perturb the AST (e.g., reassociating or pushing constants across binders) on one side but not the other, destroying the identity. This is particularly frequent with logical conjunctions (`∧`); `simp` may re-parenthesize them into a form that is mathematically equivalent but syntactically distinct, causing `rfl` to fail.
- **The Fix**: Once a goal is balanced, close it immediately with `rfl`, `congr`, `ring`, or **`tauto`** for propositional reordering.

### 3.3 Unification & Proof Flow
- **Refine vs Apply:** Use `refine` for complex goals (complex analysis, measure theory) where `apply` fails to guess implicit arguments (measure, instances).
- **Convert as a Bridge:** Use `convert` when the math is correct but ASTs differ (commutativity, constant normalization). It generates equality subgoals solvable by `ring` or `simp`.
- **Method Syntax on Propositions:** A proof term like `hXY : X ⟂ᵢ[μ] Y` is a proof of a proposition, not a structure carrying methods. Even when a theorem is named `ProbabilityTheory.IndepFun.integral_bilin`, writing `hXY.integral_bilin ...` can fail because Lean tries field projection on the proof term instead of theorem application. Use explicit application:
  `ProbabilityTheory.IndepFun.integral_bilin hXY hX hY (innerₗ H)`.
- **IsBigO Unification Drift (Manual Witnesses):** Lean's unification for product splits in `IsBigO.mul` is "greedy" and algebraically blind. When splitting a target like $a / (bc)$, Lean may guess $g_1 = a$ and $g_2 = (bc)⁻¹$. If your actual bound is $f_1 =O a/b$, this split will cause `apply` to fail. Always anchor the unification by defining pieces as named `have` statements (e.g. `have h1 : f1 =O g1`) before multiplying them.
- **Add_le_add Anchor:** Use `add_le_add (le_refl X) h` instead of `add_le_add_left h _` to anchor unification in `trans` chains when Lean fails to guess the "constant" part.
- **Implicit Argument Poisoning (Tactics-in-Terms):** Avoid using global tactics like `by linarith` or `simp` *inside* a proof term (e.g., to prove an implicit positivity witness for `comp_div`). These tactics are "greedy" and may pick an unrelated variable (e.g., `x` from the context) to satisfy the proof, causing the implicit constant (e.g., the scaling factor `R`) to unify with the wrong value. **Fix**: Use explicit constants (`zero_lt_two`) or specialized tactics (`by norm_num`) within `exact` terms.
- **Positivity vs Metavariables:** Prove `0 < x` witnesses *before* calling tactics that create metavariables (like `refine`). `positivity` cannot solve `0 < ?m`.
- **Iff-Projections in Order Lemmas:** Many core lemmas like `inv_le_inv₀`, `mul_pos_iff`, and `div_le_div_iff` are defined as `iff` statements for flexibility. `apply` will fail if it expects a direct implication. Use `.mp` or `.mpr` projections, or `rwa [iff_lemma] at h` to normalize hypotheses before application.
- **fun_prop vs. Local Hypotheses:** `fun_prop` is a typeclass-driven automation tactic. It often fails when a necessary property (like `NeZero` for the base of a complex power) is available as a local hypothesis (`hx : 0 < x`) rather than a global instance. In such cases, skip `fun_prop` and use explicit continuity lemmas (e.g., `Continuous.const_cpow`) that accept propositional witnesses.
- **Finset Sum Continuity & Subtype Domain Isolation:** When proving the continuity of a finite sum over a `Finset` on a subtype domain (e.g., `fun y : Set.Icc ... ↦ ∑ ℓ, f ℓ y`), do not use `fun_prop` if it struggles to unify local subtype boundary constraints (like $y > 0$). Instead, follow this atomic protocol:
  1. Define explicit local helpers to prove the coerced argument is positive/non-zero across the subtype domain (e.g., `have h_y_pos : ∀ y : Set.Icc ..., 0 < (y : ℝ)`).
  2. Use `apply Continuous.add` and `refine continuous_finset_sum (Finset.Icc ...) (fun ℓ _ ↦ ?_)` to decompose the sum.
  3. Individually prove the continuity of each term using explicit Mathlib lemmas like `Continuous.log`, `Continuous.rpow`, and `Continuous.pow`, passing in your local non-zero/positivity proofs as explicit arguments.
- **Let `exact` Do the Delta-Unfolding:** `exact` checks definitional equality at default transparency, which delta-unfolds ordinary `def`s, beta/eta-reduces, and sees through `Function.comp` and `set`/`let` variables. So state hypotheses in the shape that is easiest to *produce* and let `exact` bridge to the goal's shape; all three of these verified examples closed with a plain `exact` in one proof: (1) `Finset.measurable_sum ... : Measurable fun a => ∑ i ∈ univ, a i * x i` closes the goal `Measurable fun w => w ⊙ x` (unfolding `innerProduct`); (2) `hcoord.comp hg_meas : IdentDistrib (g ∘ fun rows => rows i) μ μ` closes `IdentDistrib (fun rows => g (rows i)) μ μ` (unfolding `Function.comp` + beta); (3) `hfin.const_mul (x ⊙ x')` closes a goal stated with `empiricalNTKFromRows`/`limitingNTK` while the hypothesis mentions the unfolded sums and integral. Do not pre-`rw` or `unfold` for `exact`'s benefit — try `exact` first and reach for `rw`/`simp only` only when the mismatch is *propositional*, not definitional.

---

## 4. The "Leaf Solvers": Inequalities & Arithmetic

### 4.1 Linarith & Nlinarith
- **Negated Goal Interpretation:** When `linarith` fails, the error often says `a✝ : [Negated Goal] ⊢ False`. Do not mistake `a✝` for the target. `linarith` proves goals by negating them, adding them to context, and searching for a contradiction.
- **Structure Unpacking Blindness:** `linarith` cannot natively deduce properties from packed structure hypotheses (e.g., `l.hδ : δ ∈ Ioo 0 (T/4)`). It will not extract `0 < δ` automatically. You must explicitly pass the unpacked projections (e.g., `linarith [l.hδ.1, l.hδ.2]`).
- **Linearity:** `linarith` only handles linear arithmetic. It treats `|w.im|`, `Complex.im w`, and `w.im` as unrelated opaque atoms.
- **Context-Bound Scope of `omega`:** `omega` is a linear integer arithmetic solver that operates strictly on hypotheses explicitly bound to the local context. If `omega` fails to prove simple nat bounds (like `k ≠ 0` when `1 ≤ k` is conceptually true), verify if `1 ≤ k` is present in the lemma/theorem signature. Without explicit numerical boundaries on `k` in the local context, `omega` treats `k` as an unconstrained natural number (which can be `0`), making the proof impossible.
- **Structural Logical Blindness:** `linarith` is an arithmetic solver, not a propositional one. It cannot solve conjunctions (e.g., `⊢ A ∧ B`) even if both `A` and `B` are linear inequalities it could solve individually. It will fail with "failed to find a contradiction." Use `tauto` for propositional bookkeeping or `constructor` to split the goal before calling `linarith`.
- **Manual Witnesses:** For non-linear terms (`log`, `exp`, `π`), provide linear bounds as witnesses: `linarith [Real.log_le_one, Real.pi_pos]`. If the bound isn't simple, use a `have` to prove a linear version (e.g. `log 2 ≤ 1`).
- **Transcendental Transitivity:** `linarith` cannot deduce `0 ≤ u` from `h : Real.log 2 ≤ u` alone, because it treats `Real.log 2` as an opaque atom and does not know its sign. You must additionally supply `h_pos : 0 < Real.log 2` (proved by e.g. `interval_decide`) so that `linarith [h, h_pos]` can chain the inequalities `0 < Real.log 2 ≤ u`.
- **Structural Blindness:** `linarith` does not split conjunctions or absolute values. Use `rw [abs_lt]` + `constructor` or `abs_cases x` first. Expose inequalities in set wrappers (e.g., `w ∈ Ioo a b`) using `simp only [Set.mem_Ioo]`.
- **Normalization for Linear Projections:** When a goal involves projections from `ℂ` (like `z.re \ge 1`), `linarith` may attempt to synthesize a `Preorder ℂ` instance and fail. Always strip complex wrappers using `simp only [Complex.re_add, Complex.re_ofReal, ...]` to reduce the goal to pure `ℝ` inequalities before calling the tactic.
- **Structural Set Membership Blindness:** `linarith` does not automatically unfold set memberships. If you have a hypothesis `hy : y ∈ Set.Iic (-1)`, `linarith` will not see `y ≤ -1`. You must provide the explicit witness `Set.mem_Iic.mp hy` as an argument to `linarith`.
- **Syntactic Term Equivalence Rigidity:** `linarith` treats syntactically distinct expressions (like `r` vs `B ^ (2 / 3 : ℝ) / (m : ℝ) ^ (1 / 3 : ℝ)`) as completely unrelated free variables. If one hypothesis uses `r` and another hypothesis uses its expanded definition, `linarith` will fail to deduce linear bounds (such as `S_card ≤ 2 * S_bound`). Unfold or rewrite terms (`dsimp [r]` or `rw [h_r_def]`) so that all hypotheses share identical syntactic tokens before calling `linarith`.
- **Nlinarith for Squares:** Use `nlinarith [norm_nonneg z, sq_nonneg ‖z‖]` to derive `‖z‖ < 1` from `‖z‖^2 < 1`.

### 4.2 Gcongr & Positivity
- **Product Bounds:** `gcongr` on `a * b ≤ a * c` requires a witness `0 ≤ a`.
- **Directionality in Multiplicative Order Lemmas (Left vs Right):** In Mathlib, the suffixes `_left` and `_right` in multiplication order lemmas (e.g., `nonpos_of_mul_nonneg_left`) refer to the **conclusion variable**, not the hypothesis factor.
    - `nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0` targets the **left** factor `a`.
    - `nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0` targets the **right** factor `b`.
    - **The Lesson**: If your goal is `log (n/x) \le 0` (the right factor), use `_right`.
- **Shared Witnesses:** Define strict positivity witnesses (e.g., `h_pos : 0 < x`) as named `have` statements at the top level of a proof block. Proving them inline makes them invisible to other tactic calls in the same block.
- **`positivity` Blindspots with `rpow`:** `positivity` currently fails to automatically discharge non-negativity for real powers `x ^ y`. Since `gcongr` delegates side-goals to `positivity`, `gcongr` will fail entirely without providing a way to manually supply the proof. **Fix**: Explicitly use manual monotonicity lemmas (e.g., `mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hm_pos.le _)`) to guarantee stability.

### 4.3 Division & Powers
- **Div_le_div₀ Signature:** `apply div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b)` to prove `a/b ≤ c/d`. Note the specific argument order (numerators first).
- **Pow_le_pow_iff_left₀:** Use `.mp` or `.mpr` projections from the iff to target the desired direction of the power transformation.
- **Power Nesting:** `rw [pow_mul]` bridges the gap between `x ^ (2 * 2)` and `(x ^ 2) ^ 2`.
- **Greedy Binder Scoping:** Binders like `∫`, `∑`, `∀`, `∃`, and `λ` are greedy. `∫ y, f y - g y` is parsed as `∫ y, (f y - g y)`. In `calc` blocks, this often causes `rw` to fail because the pattern `∫ y, f y` is buried inside a larger integrand. **Fix:** Use explicit parentheses to terminate binders: `(∫ y, f y) - g y`.
- **Calc Block Term Persistence:** Tactics in a `by` block justify the equality but **do not change the literal text** of the current term in the `calc` chain. If you write `∫ y` in the `calc` chain, it remains `∫ y` even if you use `rw [← setIntegral_univ]` in the proof. To ensure `rw` succeeds in the next step, your `have` anchors must match the *literal text* written in the `calc` block, or you must explicitly normalize the `calc` terms.

### 4.4 Set Decidability and Computability
- **Decidability vs Computability in Sets**: Filtering collections (like `Finset`) based on real inequalities (e.g. `|w^T x| ≤ \tau \|x\|`) involves continuous mathematics which is undecidable in Lean's type theory. Because standard operations on `Finset` rely on `Decidable` logic to generate executable code, these definitions will fail to compile. **Fix**: Explicitly prefix any definition that branches or filters on real arithmetic with `noncomputable def`.

---

## 5. The Type System: ℝ, ℂ, and Subtypes

### 5.1 The ℝ/ℂ Boundary and Function Spaces
- **Coercion Opaque:** `↑` is an opaque function to `ring`. `push_cast` is essential when mixing ℝ components with ℂ coercions.
- **Integrability Instance Loss:** Lean must re-verify `Integrable` when a function's type changes (e.g. projecting via `.re`). Use `norm_cast` to pull equations into the original domain first.
- **The Integrability Codomain Trap (ℝ vs ℂ):** If a goal integrand is `ℝ`-valued (e.g., it contains `‖f u‖`, `max`, or `abs`) but your hypothesis is for a `ℂ`-valued function, dot-notation `h.const_mul` will attempt to elaborate the constant as `ℂ`. This causes `ℝ`-only operators like `max` to fail with `failed to synthesize instance of type class Max ℂ`. **Fix**: Apply `.norm` to the integrability witness first to anchor the codomain in `ℝ`.
- **Measure Scaling Types (`ENNReal` vs `ℝ`):** When working with measures (e.g., `SignedMeasure`), scaling happens via `c • μ` where `c : ℝ≥0∞` (`ENNReal`). However, values like `totalMass μ` are computed as `ℝ`. Attempting to directly equate scalar multiplication of a measure with a real-valued inverse leads to cryptic type class resolution failures (`HMul ℝ ENNReal`). Keep measure evaluations in `ENNReal` as long as possible before converting to `Real`.
- **Norm Eq Abs:** For `ℝ`, prefer `|x|` over `‖x‖`. Use `simp [Real.norm_eq_abs]` to normalize. `linarith` and `positivity` often treat them as distinct atoms.
- **The Pi Norm Reality Check**: The default norm on general function types `ι → ℝ` (or `ι → ℂ`) in Mathlib is the **supremum norm (Pi norm)**, not the L2 Euclidean norm. Assuming that `‖x‖^2 = \sum x_i^2` will fail mathematically unless the function type is wrapped in `EuclideanSpace ι ℝ` or you explicitly define and compute with a custom Frobenius norm.
- **Instance Resolution Does Not Unfold `def`s:** Typeclass search matches instance conclusions against the goal without unfolding regular (non-`@[reducible]`) definitions. Verified instance: with `gaussianRowMeasure d` a project `def` equal to `Measure.pi (fun _ : Fin d => gaussianReal 0 1)`, the goal `IsProbabilityMeasure (gaussianRowMeasure d)` fails to synthesize even though `Measure.pi.instIsProbabilityMeasure` and the `gaussianReal` probability instance both exist. **Fix (verified):** ship a dedicated instance next to the wrapper:
  ```lean
  instance : IsProbabilityMeasure (gaussianRowMeasure d) := by
    unfold gaussianRowMeasure
    infer_instance
  ```
  Rule: every project-level `def` wrapping a measure (or any type with relevant instances) should declare its own instances immediately after the definition.

### 5.2 Structures, Existentials, and Definitions
- **AnalyticAt is an Existential:** `AnalyticAt` is a `def` alias for `∃ p, ...`. Dot-notation `h.const_mul` will fail; use `AnalyticAt.const_mul h`.
- **Measure-Theory Namespace Families:** Core Bochner lemmas that "feel" global are often namespaced: `MeasureTheory.integral_sub`, `MeasureTheory.integral_const`, `MeasureTheory.memLp_const`, `MeasureTheory.MemLp.sub`, `MeasureTheory.MemLp.integrable`. If an unqualified guess like `integral_sub` or `memLp_const` fails, do not invent variants; first try the `MeasureTheory.` namespace and verify with `#check`.
- **Anonymous Subtypes:** Subtype constructors `⟨z, hz⟩` often need type annotations in polymorphic contexts (like `Set.range f`) to tell Lean which subtype is targeted.
- **Opaque Local Definitions:** `set` or `let` definitions (e.g. `let y n := ...` or `let b := row.1`) are opaque to `rw` and often "invisible" to structural tactics like `positivity` and `norm_num`. Use `unfold f` or `dsimp [f]` (or `dsimp [b, row, Table_15]`) first to expose the concrete values, or prove witnesses using the exact `let` name to anchor the tactic.
- **Dependent Arrow Scope:** A nondependent arrow `h : n = k → P n` does **not** make the proof of `n = k` available while Lean elaborates the codomain `P n`. If subtype witnesses or hidden proof fields inside `P n` need that equality, write the statement as `∀ hk : n = k, P n` so the equality proof is in scope during elaboration.
- **Implicit Parameters in List Lemmas**: In lemmas like `List.getLast_mem`, the list parameter is implicit `{l : List α}` because its identity is inferred from the type of the non-emptiness proof `h : l ≠ []`. Do not supply the list explicitly (e.g., write `List.getLast_mem h_ne` instead of `List.getLast_mem l h_ne`), otherwise it will cause an application type mismatch.
- **Ne_eq for Negation:** `a ≠ b` is `¬(a = b)`. Use `rw [ne_eq]` to expose the equality for subsequent rewrites (e.g., `rw [ne_eq, Real.sinh_eq_zero]`).
- **Explicit PNat to Nat Casts:** Lemmas like `Set.finite_lt_nat` expect `ℕ`. Even if Lean's infoview shows `n` as a number, it might be a `PNat`. Use `(n : ℕ)` explicitly in the argument to avoid synthesis or type mismatch errors.
- **one_mul for Syntactic Matching:** `rw` will fail to match `x` if `field_simp` or `lt_div_iff₀` leaves a `1 *` factor. Use `one_mul` to normalize the AST.
- **Alias Lemma Arguments and Implicits:** Alias lemmas (like `injOn` for `injOn_of_injective`) preserve the implicit-argument structure of the original. Providing an explicit argument (like a set $s$) to an alias can cause it to be interpreted as an argument to the *result* (e.g. an element $x \in s$) if the alias's set argument is implicit `{s}`. Use `@` or specialized lemmas instead.
- **Specialized Lemmas for Subtypes:** When working with coercions like `PNat.val`, prefer specialized lemmas like `Set.injOn_subtype_val` over generic `Injective.injOn` aliases to avoid unification ambiguities and metavariable poisoning.
- **Eventually-Projection Failures**: Since `Eventually` is a type alias for filter membership `∈`, and `∈` on filter infimums (`𝓝 a ⊓ 𝓟 s`) is definitionally defined as an existential `Exists`, Lean 4's dot-notation resolves to `Exists.and` (or `Exists.exists`) and fails. Use the fully qualified names `Filter.Eventually.and` and `Filter.Eventually.exists` with standard function application instead of dot-notation.
- **Typeclass Search Syntax-Sensitivity**: Lean 4's typeclass instance search (`synthInstance`) is highly syntax-sensitive to maintain performance. If a set in a filter is unified to a lambda expression (e.g., `{x | (fun x ↦ x > a) x}`), typeclass search for `NeBot` will fail to match standard instances registered for `Set.Ioi a` (even though they are definitionally equal). Resolve this by defining a local instance with the `haveI` tactic inside the tactic block (`by`) matching the exact syntax printed in the error message: `haveI : Filter.NeBot (nhdsWithin a {x | (fun x ↦ x > a) x}) := nhdsWithin_Ioi_neBot le_rfl`.
- **Equality Elimination Rewrites the Whole Dependent Context:** `cases h_eq` on a hypothesis such as `h_eq : i.val = 189` does not merely rewrite the target. Lean transports every hypothesis depending on `i`, including hidden subtype proofs, and may fail with a dependent-elimination error. The reliable pattern is to move the transport into a fresh helper lemma over a new variable that carries no dependent baggage.
- **`lift` Auto-Coercion on Context:** The `lift` tactic automatically coerces the lifted expression in all existing hypotheses in the local context. If a hypothesis `h` was present before `lift`, its type is immediately updated (e.g., `meromorphicOrderAt f p < 0` becomes `↑n < 0`). Writing manual rewrites like `rw [← hn] at h` afterwards will fail as the pattern is already gone.
- **Set Relations as Equivalences:** Set relation lemmas (such as `Set.disjoint_right`) are often `Iff` equivalences rather than implications. They must be projected with `.mp` or `.mpr`. When calling the projection, ensure the right-hand set membership is passed first (L-to-R argument scanning).
- **Value-Level Congruence in `convert`:** `convert` automatically applies extensionality on function binders, transforming function-level equality `f = g` to value-level equality `f x = g x`. Calling `ext` inside a `convert` block will fail because the goal is already at the base type (e.g., `ℂ`).
- **Coercion wrappers (Set / Finset):** Coercion from Finset to Set (`↑`) is a separate AST node. Set lemmas (such as `Set.Finite.mem_toFinset`) will fail to match on coerced finsets unless `Finset.mem_coe` is applied first.
- **Domain Unification in Subtype Sums:** A sum over `{x // x ∈ s}` (Finset subtype) and a sum over `{x // x ∈ (s : Set)}` (Set subtype) are sums over different types. Before equating them, you must unify their domains by rewriting with `Set.Finite.coe_toFinset` to prevent type mismatches.

---

## 6. Advanced Analysis Patterns

### 6.1 Filters & Limits
- **atTop = cofinite for ℕ+:** If `atTop_le_cofinite` fails due to missing `NoTopOrder ℕ+` instance, use a manual proof using basis lemmas:
  ```lean
  refine le_antisymm ?_ ?_
  · rw [Filter.atTop_basis.le_iff]; intro n
    exact (Set.finite_lt_nat (n : ℕ)).subset (fun (x : ℕ+) hx ↦ hx) |>.compl_mem_cofinite
  · rw [Filter.atTop_basis.ge_iff]; intro n _
    exact (Set.finite_lt_nat (n : ℕ)).subset (fun (x : ℕ+) hx ↦ hx) |>.compl_mem_cofinite
  ```
- **Filter Basis Unification:** In complex filters (like intersections of `comap` and `principal`), `squeeze'` often fails to unify. Use `h_basis.eventually_iff.mpr ⟨1, True.intro, fun z hz ↦ ...⟩` to solve the goal as a simple real inequality.
- **Asymptotic Singularities (n=1):** Asymptotic congruence (`isBigO_congr`) requires an `EventuallyEq` proof. If the functions involve terms like $\log n$ or $1/x$, the identity may be undefined at the boundary ($n=1$ or $x=0$). Using `Eventually.of_forall` forces a universal proof that will fail for lack of positivity witnesses. Always use `filter_upwards [eventually_ge_atTop 2]` to restrict the proof to the well-defined region and provide the strict witnesses needed for `field_simp`.
- **Lambda Binders:** Complex filters often require explicit lambda binders and type annotations to avoid "Invalid field notation" errors: `refine Filter.Tendsto.squeeze' (h := fun (z : ℂ) ↦ ...)`.
- **Mono_left for Filter Subsets:** Use `.mono_left nhdsWithin_le_nhds` when the goal source filter is a sub-filter of the lemma's. `convert` generates a false equality goal (`nhdsWithin = nhds`).
- **Root Namespace Limits:** Basic limit lemmas like `tendsto_const_nhds` are often in the root namespace, not `Filter`.

### 6.2 Infinite Sums & Integrals
- **Tsum Congruence:** `congr` on `tsum f = tsum g` stripped the summation operator and turns the goal into `f = g`. Use `ext n` or `funext n` to solve.
- **Integral Sum Strategy:** (1) `Standardize` via `simp only` to unify definitions; (2) `Expand` via `simp_rw [sub_mul]` to push scalars inside; (3) `Linearize` via `integral_sub` to split; (4) `Algebra` via `ring` to cancel.
- **Higher-Order Subgoal Flow:** The order of subgoals for `dominated_convergence` variants depends on the lemma's argument order. For example, `tendsto_integral_filter_of_dominated_convergence` typically expects (1) AEStronglyMeasurable, (2) Integrand Bound, (3) Integrable Bound, and (4) Pointwise Limit. Always `#check` the signature or consult usage examples (e.g., `Wiener.lean`) to avoid "Type Mismatch" errors.
- **Dominated Convergence:** Use `tendsto_tsum_of_dominated_convergence` for Tannery's Theorem and `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` for integrals.

### 6.3 Complex Analysis & Specialized Logic
- **Coth Normalization:** `coth z := 1 / tanh z`. Prefer `cosh / sinh` to avoid artificial `cosh z ≠ 0` dependencies. `cosh / sinh` is well-defined exactly when `sinh z ≠ 0`.
- **Closure of Preimage Strips:** Use `Complex.closure_preimage_im` and `closure_Ioo` to rewrite the closure of an open strip to a closed strip.
- **AnalyticOn Sensitivity:** `AnalyticOn` is sensitive to set representation. Use `convert` if there's a mismatch between `{w | P w}` and `f ⁻¹' S`.
- **Even Functions:** For even functions, use `CharZero.eq_neg_self_iff` to prove $f'(0) = 0$ from $f'(0) = -f'(0)$.
- **Square Root Trick:** For `‖f‖^2 → 1` goals, use `Filter.Tendsto.sqrt` + `Real.sqrt_sq` to derive `‖f‖ → 1`.

---

## 7. The Anchor Principle (Identity Management)

### 7.1 Complex Power/Algebraic Identities
**The Problem:** In analysis proofs (especially `IsBigO`), we often encounter identities like:
$$ C' \cdot \log n^{-\beta} = C \cdot \left(\frac{T}{4\pi} \log n\right)^{-\beta} $$
Attempting to prove this via a long chain of `rw` calls (`mul_assoc`, `← Real.mul_rpow`, `Real.rpow_neg`) inside a main proof block is brittle. Any change in associativity or hidden coercion (e.g. `(log n : ℝ)`) causes the syntactic matching to fail.

**The Fix:** pull the identity into a named `have` statement (an **Anchor**).
```lean
have h_rhs : C' * log n ^ (-β) = C * ((T / (4 * π)) * log n)⁻¹ ^ β := by
   dsimp [C']; rw [mul_assoc, ← Real.mul_rpow ..., Real.rpow_neg ...]
rw [h_rhs]
```
This verifies the algebraic identity in a clean environment and allows `exact` or `gcongr` to work on the main goal without ambiguity.

### 7.2 Gcongr Goal Ordering & Greedy Matching
- **Greedy Matching:** `gcongr` with a multiplier like `C * X ≤ C * Y` will prioritize the monotonicity goal `0 ≤ C` before the main goal `X ≤ Y`.
- **Goal Splitting Failure:** If `C` is a variable without an explicit positivity witness, `gcongr` will leave you with `0 ≤ C`. If you try to apply an inequality (like `X ≤ Y`) to this goal, Lean will report a **Type Mismatch**.
- **The Fix:** Either prove `0 ≤ C` *before* the `gcongr` call, or use a specific order lemma like `mul_le_mul_of_nonneg_left` which allows explicit control over the argument order.

### 7.3 Type Anchoring for Coercions (The "Transparent" Trap)
**The Problem:** In `have` statements for limits or integrals, Lean may infer the domain as `ℝ` even if the target goal is in `ℂ`. Coercions (`↑`) are definitionally "transparent" to the user but can be "opaque" to Lean's unification if the limit value (e.g. `1`) is not explicitly typed.
**The Fix:** Always anchor the types in your anchors. Use explicit annotations like `: ℂ` and typed constants like `(1 : ℂ)` to force Lean into the correct domain. Example: `have h : Tendsto f l (nhds (1 : ℂ))`.


### 7.3 Subtraction-to-Sum Anchor (The `rw` Subtraction Trap)
**The Problem:** `rw` is a syntactic matcher. If a goal is $A = B - C$ and a lemma is $A + C = B$, `rw [← lemma]` will fail to match $B - C$ because it lacks the addition operator.
**The Fix:** Use `eq_sub_iff_add_eq` (or `sub_eq_iff_eq_add`) to transform the subtraction into a sum *before* applying the lemma. Alternatively, use `congr 1` to strip the common factor and `convert` to bridge the identity.

---

## 8. Search Tools & Resources

| Tool | When to use | How |
| :--- | :--- | :--- |
| `grep` | You know a keyword or naming fragment | `grep -rn "keyword" .lake/packages/mathlib/` |
| `leansearch` | You know the concept in words | `leansearch "integral of product"` |
| `loogle` | You know the input/output types | `loogle "(?a → ?b) → List ?a → List ?b"` |

**Workflow:** Decompose your goal into subject + predicate, predict the name using naming conventions (2.3), then `grep` the current file first before searching Mathlib. `CH2.lean` contains specialized helpers (e.g., `sinh_ne_zero_of_re_ne_zero`) for common analytical bottlenecks.

**Grep Blind Spot 1 — Namespaced Declarations:** A lemma declared as `theorem sum_univ_eq_sum_range` inside `namespace Fin` never contains the literal string `Fin.sum_univ_eq_sum_range` in its declaration, so `grep -rn "theorem Fin.sum_univ_eq_sum_range"` returns nothing even though the lemma exists. **Fix:** grep the short name (`grep -rn "sum_univ_eq_sum_range"`), or grep usage sites in other Mathlib files (`← Fin.sum_univ_eq_sum_range` appears in `Mathlib/NumberTheory/Bernoulli.lean`), which confirm both existence and the fully-qualified form.

**Grep Blind Spot 2 — `to_additive`-Generated Lemmas:** Additive versions of multiplicative lemmas are generated by the `@[to_additive]` attribute and have **no literal declaration string anywhere**. Verified instances: `Fin.sum_univ_eq_sum_range` (generated from `Fin.prod_univ_eq_prod_range`, `Mathlib/Data/Fintype/BigOperators.lean:226`) and `Finset.measurable_sum` (generated from `Finset.measurable_prod`, `Mathlib/MeasureTheory/Group/Arithmetic.lean:829`). If grep for an additive name finds only usage sites, grep the corresponding multiplicative name (`prod` for `sum`, `mul` for `add`) to locate the declaration file.

---

## 9. Integral & Measure Theory Nuances

### 9.1 Indicator Transformation Direction
`integral_indicator` is oriented `indicator_integral = set_integral`.
- **Set-to-Indicator:** To convert a restricted integral `∫ x in s, f x` to a global integral `∫ x, indicator s f x`, you must use `rw [← integral_indicator]`. Failing to use `←` will result in a "Did not find occurrence" error.

### 9.2 The Measure Namespace
Many foundational integral lemmas (like `integral_comp_div`, `integral_comp_add`) are located in the `Measure` namespace.
- **Usage:** Use `Measure.integral_comp_div` instead of the global `integral_comp_div`.
- **Operator Normalization:** These lemmas often return results using scalar multiplication (`•` or `smul`). If your goal involves complex multiplication (`*`), you must normalize with `simp only [smul_eq_mul]` to match the patterns.

### 9.3 Rewriting Inside Integral Binders (Rule 153 Expanded)
`rw` cannot see through binders (`∫`, `∑`, `λ`).
- **The Symptom:** You have `∫ x, f x` and a lemma for `f`, but `rw` fails.
- **The Fix:** Use `congr 1; ext x` to move the goal inside the integral. Only then can you use tactics like `rw [le_div_iff₀]` on the integrand or indicator condition.

### 9.4 Measure Rigidity and Restrictions
`Integrable f volume` does not unify with `Integrable f (volume.restrict s)` in `exact` calls, even though the former implies the latter.
- **The Fix**: Use `hf.mono_measure Measure.restrict_le_self` or `hf.integrableOn s` to explicitly bridge the measure difference. Lean will unify the implicit set `s` with the goal's restriction.
- **Support Preservation**: Avoid `ae_of_all` when bounding integrals over restricted sets. `ae_of_all` expects the bound to hold for **all** elements of the type. Use `filter_upwards [MeasureTheory.ae_restrict_mem hs]` to introduce the membership hypothesis `hx : x ∈ s` into your context.

### 9.5 Complex Analysis Friction: Push vs Pull
When dealing with coerced real exponentials `↑(rexp r)`, you have two strategies for simplification:
1.  **Pushing (`push_cast`)**: Moves the coercion inside: `Complex.exp ↑r`. Use this if you need to stay in `ℂ` to match other complex terms. Note: `Complex.norm_exp` will then introduce a complex projection `.re`, which may require `norm_cast` to simplify.
2.  **Pulling (`Complex.norm_ofReal`)**: Strips the complex norm immediately: `‖↑(rexp r)‖ = |rexp r|`. This is almost always superior for bounding terms, as it avoids introducing complex projections into a real goal.

### 9.6 The "Prop" Dot-Notation Trap
Dot-notation (e.g., `h.foo`) is a projection for **Structures** (Integrable, Continuous, etc.). It does **not** work for logical lemmas on **Propositions** (e.g., `a < b`).
- **The Symptom**: `Invalid field neg_pos ... for type LT.lt`.
- **The Fix**: Use functional application: `neg_pos.mpr h`.

### 9.7 The "Universe-Restricted" Mismatch
`∫ x in univ, f x ∂(μ.restrict s)` is definitionally equal to `∫ x in s, f x ∂μ`.
- **The Problem:** Even though they are definitionally equal, `rw` will fail to match high-level lemmas (like `integral_union_ae`) if the AST is in the "noisy" universe-restricted form.
- **The Fix:** Use `MeasureTheory.setIntegral_univ` on the specific measure `μ.restrict s`. This converts the integral to `integral (μ.restrict s) f`, which is the canonical form for the `∫ x in s` notation.

### 9.4 Convert for ℝ/ℂ Boundary Coefficients
When matching coefficients across the `ℝ/ℂ` boundary (e.g., matching `2 * ↑π` in the goal with `|2 * π|` in a lemma), `rw` often fails due to AST differences in multiplication and coercion.
- **The Fix:** Use `convert Measure.lemma_name ... using 1`. This generates a clean subgoal for the coefficient equality (e.g., `(2 * π : ℂ) = ↑|2 * π|`) which can be solved with `simp [abs_of_pos ..., push_cast]`.

### 9.5 Syntactic Sign Normalization for Integrals
When using `convert` on integral limits, the domains must match **exactly**. Even mathematically equal domains like `-T * (log x / 2π)` and `T * (-log x / 2π)` will cause `convert` to leave an unsolved goal.
- **The Fix:** Use a "Normalization Block" like `simp only [neg_mul, mul_neg, mul_div_assoc]` to move all minus signs to a canonical position (usually the front of the numerator) before attempting to bridge the identity.

### 9.6 Measure Invariance via Scaling
**The Tip:** Fundamental symmetries like the negation-invariance of the Lebesgue measure on $\mathbb{R}$ are often best proven via general scaling lemmas rather than searching for specific named constants.
**Verified Tactic:** `simpa using Real.smul_map_volume_mul_left (a := -1) (by norm_num)` is the robust way to prove `Measure.map neg volume = volume`.

### 10.2 The "Convert-Push-Simplify" Protocol
For all mixed-type algebraic identities (especially `ℝ/ℂ` boundaries), follow this mandatory 3-step sequence:
1.  **Convert** scalar multiplication to field multiplication using `Algebra.smul_def`.
2.  **Push** real-field operations (inverses, negation) into the complex field using `push_cast`.
3.  **Simplify** the now-unified field expression using `field_simp` and `ring`.
Failure to follow this sequence leads to opaque atoms that `ring` cannot solve.

### 10.3 The "Standardize-Expand-Linearize" Protocol
For identities involving projections (`.re`, `.im`) and multipliers, follow this sequence:
1.  **Standardize**: Use `push_cast` to unify real-to-complex coercions into single `↑` nodes.
2.  **Expand**: Use `simp_rw [mul_add, add_mul, add_div]` to distribute multipliers/divisors into the parentheses *inside* the projection.
3.  **Linearize**: Use `Complex.add_re` and `Complex.re_ofReal_mul` to pull the projection to the leaves.
4.  **Solve**: Once the goal is expressed as pure real arithmetic, use `field_simp` and `ring`.

### 11. Subgoal Alignment and Isolation
For lemmas with many positional arguments (like `integral_union_ae` or `dominated_convergence`), a "Type mismatch" in a proof term (e.g., passing a proof for `Iic` to a goal for `Ici`) often indicates that you are misaligned with the lemma's argument order.
- **The Fix:** Use `·` (dot) for every subgoal. This isolates the goal and prevents error-poisoning. If `exact` fails with a cryptic type error, re-read the lemma signature using `#check` to confirm which set/hypothesis corresponds to which goal index.

### 12. Lean 4 Specific Learnings (BarronNorm & Sampling)
* **Calc Block Indentation Swallowing:** Nesting a `calc` block inside a `by` block that is itself a step in an outer `calc` block can break Lean 4's strict indentation parser. The parser may "swallow" the subsequent steps of the outer `calc` block into the inner one, leaving the target state completely mismatched and causing tactics like `ring` to fail with bizarre errors (e.g., "not a positivity goal"). **Fix:** Flatten the proof structure. Use `exact sorry` or `exact ...` for the side goal to terminate the `by` block without opening a nested `calc`.
* **simpa and Metric vs Absolute Values:** When transforming `dist A B` into `\|A - B\|` (like in `LipschitzWith.dist_le_mul`), `simpa using h` may aggressively simplify the RHS (`dist A B` to `abs`) but fail on the LHS (`dist (f A) (f B)`). This creates an unbridgeable type mismatch. **Fix:** Do not rely on `simpa` to magically translate all `dist` terms. Explicitly standardize the hypothesis using `rw [Real.dist_eq, Real.dist_eq] at h` before passing it to `simpa`.
* **Pi-Type Typeclasses and Named Arguments:** For functions like `iIndepFun` that expect an implicit typeclass over a Pi type (`[m : ∀ x, MeasurableSpace (β x)]`), Lean 4's instance resolution cannot automatically synthesize it (it lacks explicit lambda abstraction). You must manually pass a function returning the local instance. **Crucially**, you cannot pass `(fun _ => inferInstance)` as a positional explicit argument, as this shifts all subsequent arguments and causes typeclass expectation errors. **Fix:** Use Lean 4's named argument syntax: `(m := fun _ => inferInstance)`.
* **Topological Spaces and MeasurableSpace:** In Mathlib 4, `borel` is a definition, not an automatic global instance. Even if `H` is a `TopologicalSpace` (e.g. `NormedAddCommGroup H`), methods like `Integrable` will fail with "failed to synthesize instance of type class MeasurableSpace H" unless you explicitly add `[MeasurableSpace H]` to the variables/theorem assumptions.
* **Set Mapping with Custom Structures:** When building a set using `Set.image`, if you map anonymous tuple brackets `⟨w, true⟩`, Lean infers the resulting set as `Set (X × Bool)`. If you later check membership `x ∈ S` where `x` is a custom `structure SignedSample`, typeclass resolution for the `∈` operator (`Membership`) fails completely. **Fix:** Always use explicit structure constructors (e.g., `SignedSample.mk w true`) inside `Set.image` to enforce strict type inference.

---

## 13. Category Theory & Algebraic Geometry (Schemes)

Lessons from formalizing scheme theory (`AlgebraicJacobian/Picard/*`): residue fields, stalks, morphism properties, and group schemes. The recurring enemy is **dependent types indexed on scheme points**, where two terms are *definitionally* equal but not *syntactically* equal.

### 13.1 Point-Indexed Dependent Types Cause "Defeq Hell"
`X.residueField x` and `Scheme.Hom.residueFieldMap f x : Y.residueField (f x) ⟶ X.residueField x` have **types that mention the point** `f x`. Concretely, for a section `e : Spec k ⟶ X` and structure map `π : X ⟶ Spec k`, the point `(e ≫ π).base default` and `π.base (e.base default)` are definitionally equal (composition of the underlying continuous maps) but **not syntactically equal**. Consequences:
- `rw [h]` where `h : … = pbar ≫ sbar` **fails to find the pattern**, because `pbar ≫ sbar` is not syntactically present (its domain type `residueField (π (e default))` was written as `residueField ((e ≫ π) default)`).
- The anonymous-constructor composition `pbar ≫ sbar` may itself fail to typecheck for the same reason (domain/codomain point mismatch).
- **Fix:** do **not** try to `rw` these into alignment. Transport with `▸` (see 13.2) or route through a structural instance (see 13.4).

### 13.2 `▸` Transports Across Defeq; `rw` Does Not
The single most useful escape hatch. `rw` is a *syntactic* pattern matcher and chokes on point-indexed defeq. `h ▸ (term : T[lhs])` produces `T[rhs]` by rewriting the *whole type* via a motive, tolerating the defeq indexing. Verified pattern:
```lean
have hc : (e ≫ π).residueFieldMap default = pbar ≫ sbar := residueFieldMap_comp e π default
haveI hiso : IsIso (pbar ≫ sbar) := hc ▸ (inferInstance : IsIso ((e ≫ π).residueFieldMap default))
```
Rule: when `rw`/`exact` fails on a term that is defeq-but-not-syntactic, reach for `▸`. Use `rw` only when the pattern appears syntactically **in the goal** (e.g. `rw [hsec]` where the goal literally contains `e ≫ π`).

### 13.3 The "not type-correct under `instances` transparency" Diagnostic
When a rewrite (`Category.comp_id`, etc.) fails and the error appends *"The target expression is not type-correct under the `instances` transparency level"*, it means a prior rewrite unfolded a semireducible def and left a term whose well-typedness depends on defeq that instance-transparency won't see. **This is a stop sign**: abandon rw-based massaging and switch to `▸`, `convert`, or a structural instance.

### 13.4 `Category.comp_id` Is Fragile; Prefer Structural Instances for `IsIso`
- `Category.comp_id` (`f ≫ 𝟙 = f`) **will not fire** when the `𝟙`'s object is defeq-not-syntactic to the intended one. E.g. after `rw [residueFieldMap_id]` you get `𝟙 (residueField ((𝟙) default))`; the composite `iso.hom ≫ 𝟙` is only type-correct up to defeq, so the pattern `?f ≫ 𝟙 ?m` cannot unify. **Do not manufacture a `≫ 𝟙` you then need to cancel.**
- `infer_instance` is **not robust on rewritten goals** carrying defeq annotations: both `IsIso (𝟙 _)` and `IsIso (iso.hom ≫ 𝟙 _)` failed to synthesize after rewrites, even though the underlying instances exist.
- **Fix (verified):** obtain `IsIso` from a **clean structural instance** and transport with `▸`. For `f = e ≫ π = 𝟙`, use that `𝟙` is an open immersion and the instance `[IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x)`:
  ```lean
  haveI : IsOpenImmersion (e ≫ π) := by rw [hsec]; infer_instance
  haveI : IsIso (pbar ≫ sbar) := hc ▸ (inferInstance : IsIso ((e ≫ π).residueFieldMap default))
  ```

### 13.5 Dot/Field Notation Fails on Categorical Combinators (`𝟙`, `≫`)
Field notation `x.f` resolves the namespace from the **head constant** of `x`'s type. `(𝟙 X).residueFieldMap x` fails with *"Field projection operates on types of the form `C …`"* because `𝟙 X = CategoryStruct.id X` — its head is not `Scheme.Hom`. **Fix:** use explicit application `Hom.residueFieldMap (𝟙 X) x`. Same for morphisms built via `≫`, `.op`, `pullback.snd`, etc.

### 13.6 Split-Epi + Mono ⟹ Iso (the standard "field-hom retraction is iso" pattern)
To prove a residue-field map `sbar : κ(x) → κ(pt)` (or any concrete-category hom between fields) is an iso, given a retraction:
- `IsSplitEpi sbar` from a section: `⟨⟨inv (pbar ≫ sbar) ≫ pbar, by rw [Category.assoc, IsIso.inv_hom_id]⟩⟩` (needs `IsIso (pbar ≫ sbar)`).
- `Mono sbar` from injectivity of a field hom: `ConcreteCategory.mono_of_injective sbar sbar.hom.injective` (a ring hom out of a `Field` is injective; `sbar.hom` extracts the `RingHom` from a `CommRingCat` morphism).
- Combine: `isIso_of_mono_of_isSplitEpi sbar : IsIso sbar`, then `asIso sbar : κ(x) ≅ κ(pt)`.
Do **not** reach for `CommRingCat.mono_iff_injective` — it does not exist (use `ConcreteCategory.mono_of_injective`).

### 13.7 fpqc Descent via `MorphismProperty.DescendsAlong`
To descend a morphism property `P` (e.g. `UniversallyClosed`, `Smooth`) from a base change along `Spec k̄ → Spec k` to the original morphism, use the descent instance + `of_pullback_snd_of_descendsAlong`. The field extension map is surjective + flat + quasi-compact, all by `inferInstance`. Verified one-liner (identical pattern to Mathlib's `smooth_of_grpObj`):
```lean
exact MorphismProperty.of_pullback_snd_of_descendsAlong
  (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h
```
The `Q g` proof is nested `⟨⟨surj, flat⟩, qc⟩` because `⊓` is left-associative. Descent instances exist for `UniversallyClosed` (Stacks 02KS), `UniversallyOpen`, `Smooth`, `Etale`, `LocallyOfFiniteType`, etc. (see `Morphisms/FlatDescent.lean`, `Morphisms/LocalFlatDescent.lean`).

### 13.8 Workflow: IDE Diagnostics vs Full Build
For iterative scheme-theory proofs, the editor's per-edit `ide_diagnostics` (≈1 s) is far faster than `lake build` (tens of seconds to minutes, because the import chain re-elaborates). Edit → read diagnostics → fix, and reserve `lake build` for final verification and for instance-cache/cross-file issues the language server can report stale. Also: this repo has background agent loops that rewrite files; **re-read a file (and check `git status`) immediately before acting on it**, or you may plan against a stale version.

### 13.9 Inner Products on EuclideanSpace and Definitional Equality
**The Problem:** Trying to prove `inner ℝ v y = ∑ i, v.ofLp i * y.ofLp i` using `rfl` fails with a `Type mismatch` because the inner product on `EuclideanSpace ℝ ι` (an alias for `PiLp 2 (fun _ ↦ ℝ)`) does not beta/eta reduce exactly to a sum of real multiplications.
**The Fix:** Use the explicit API lemmas.
1. Use `PiLp.inner_apply` to expand the inner product over the components: `inner x y = ∑ i, inner (x i) (y i)`.
2. Use `Real.inner_apply` (via `simp only [Real.inner_apply]`) to convert the component-wise generic inner product on reals to standard multiplication: `inner (a : ℝ) (b : ℝ) = a * b`.

**Beware `dsimp [inner]`**: Do not aggressively use `dsimp [inner]` to unfold the inner product before using API lemmas. This unfolds down to the `InnerProductSpace.Core.inner` representation, destroying the syntactic shape expected by `PiLp.inner_apply` and causing `rw` to fail with "Did not find occurrence".

## 14. Calculus and Euclidean-Space Proof Engineering (Lasso Mirror Flow)

### 14.1 `HasDerivAt` Contains Hidden Algebraic Structure Arguments

`HasDerivAt f f' t` is defined through `HasDerivAtFilter`, scalar multiplication, and `toSpanSingleton`. Consequently, it depends not only on the displayed types and terms, but also on the elaborated `AddCommGroup`, `Module`, topology, and scalar-action instances. Two derivative propositions can print identically while retaining different instance terms.

This occurred when composing a tilted-loss gradient with a real-valued trajectory. The proposed term

```lean
(hasGradientAt_tiltedLoss M r lambda hM x).hasFDerivAt.comp_hasDerivAt t hx
```

produced goals comparing `Real.instAddCommGroup` with `Real.normedAddCommGroup.toAddCommGroup`, and `Semiring.toModule` with `RCLike.toInnerProductSpaceReal.toModule`. The function, point, and displayed derivative were already equal. The failure was entirely in these hidden structure arguments.

- `simpa` cannot solve this: simplification does not prove equality between distinct typeclass structures.
- `convert ... using 1` is useful diagnostically because it exposes the hidden equality goals, but it does not make them true.
- `Subsingleton.elim` is not a remedy. The types `AddCommGroup ℝ` and `Module ℝ ℝ` are not subsingletons: in general, a carrier can support more than one algebraic structure.
- Repeated unfolding usually makes the goal less stable because it exposes still more implementation-level structure.

The robust response is to change the proof boundary. For the positive DLN flow, prove monotonicity of the weight-space objective using `ConvexOpt.gf_monotone_decrease`, then transfer the result through the exact value identity
`tiltedLoss M r lambda (coordinateSquare u) = posDlnObjective M r lambda u`.
This avoids manufacturing an equality between instance implementations while preserving the intended mathematics.

### 14.2 Composition Lemmas Preserve Point-Free Syntax

`HasFDerivAt.comp_hasDerivAt` concludes a derivative for `l ∘ f`. A goal may instead contain the eta-expanded function `fun t => l (f t)`. `Function.comp_apply` rewrites applications such as `(l ∘ f) t`; it does not necessarily rewrite a function object stored inside `HasDerivAt`. Therefore

```lean
simpa only [Function.comp_apply] using hcomp
```

can fail even though the two functions are extensionally and definitionally equal. Use

```lean
convert hcomp using 1 <;> rfl
```

when the only mismatch is point-free composition versus its lambda form. Inspect the goals produced by `convert`: if they mention algebraic structures rather than functions or values, the problem is the instance diamond from §14.1 and this eta-conversion pattern is not sufficient.

### 14.3 Normalize Representation Before Differentiation or `ring`

The positive-DLN file uses both `M.mulVec x` and the Euclidean-space wrapper `matVec M x`. Although `matVec` is defined from `mulVec`, `ring` treats `(M.mulVec x) i` and `(matVec M x) i` as unrelated atoms until the wrapper is unfolded or an equality is supplied. A polynomial identity mixing both spellings therefore need not close.

Choose one representation for the whole local lemma. For coordinate algebra, state the identity using `matVec`, unfold `matVec`, `euclideanOf`, and `coordinateSquare` together, and only then call `ring`. For topological or gradient statements, retain `EuclideanSpace` and use its API rather than alternating between raw functions and wrappers mid-proof.

The same rule applies to derivatives. A componentwise proof of a prospective `matVec_hasDerivAt` reached the final transport step but then selected `PiLp.normedAddCommGroup`/`PiLp.normedSpace` on one side and `WithLp.instAddCommGroup`/`WithLp.instModule` on the other. These are syntax-sensitive instance paths for the same wrapper family. Keep the derivative construction and conclusion in one representation, or package the linear operator once as a continuous linear map and use that bundled map throughout. Do not expect a broad `simpa [matVec, euclideanOf, e]` to repair an instance mismatch introduced earlier.

### 14.4 Three Small Elaboration and Tactic Traps

1. A documented declaration scoped by `omit` must put the scope command first:
   ```lean
   omit [Fintype ι] in
   /-- Documentation. -/
   lemma name ... := ...
   ```
   Placing the documentation comment before `omit` makes the parser expect the declaration immediately and reports `unexpected token 'omit'; expected 'lemma'`.
2. A structure literal used in a `have` needs an assignment token: write `have h : T := { field := value }`, not `have h : T where ...`. The `where` syntax belongs to declaration bodies and selected term constructs, not this `have` form.
3. `congr 1` does not algebraically cancel a common scalar factor. From `lambda * a = lambda * b`, cancellation requires `lambda ≠ 0`; without it, the original theorem may be true only because `a` and `b` are independently equal. In the tilted-loss identity, rewrite the norm and inner-product expressions to the same finite sum and let `simp` close the equality instead of trying to cancel `lambda`.

### 14.5 Build Monotonicity from a Derivative Certificate

For a real-valued curve `F : ℝ → ℝ`, the reusable proof pattern is:

1. produce `∀ t, HasDerivAt F (F' t) t`;
2. prove `∀ t, F' t ≤ 0`;
3. apply `antitone_of_hasDerivAt_nonpos`.

For ordinary gradient flow, `ConvexOpt.gf_monotone_decrease` supplies step 1 with derivative `-‖gradient f (w t)‖ ^ 2`, and `neg_nonpos.mpr (sq_nonneg _)` supplies step 2. This isolates calculus from order reasoning and is more reusable than re-running the chain rule inside each antitonicity theorem.

For an effective parameter `x(t) = u(t)^2`, first ask whether the effective-space objective is exactly the weight-space objective. In the Lasso development,

```lean
tiltedLoss M r lambda (coordinateSquare u) = posDlnObjective M r lambda u
```

turns the target into the already established weight-space monotonicity theorem. The coordinatewise dissipation identity remains valuable API for later estimates, but it need not be the implementation route for every monotonicity corollary.

### 14.6 Workflow Retrospective and Corrective Protocol

Several failed approaches violated earlier rules in concrete ways:

- Looking for plausible names such as `HasGradientAt.comp_hasDerivAt`, `matVec_hasDerivAt`, and a trajectory-level antitonicity projection before verifying them violated Rule 1. Repository and pinned-Mathlib `rg` searches showed that the first and third capabilities have different APIs and the second name is absent.
- Importing the edited module in a scratch file before rebuilding its `.olean` weakened Rule 8's guarantee and led to false `unknown identifier` diagnoses. The direct source check and the import check were consulting different artifacts.
- Continuing to push `simpa`, `convert`, and `Subsingleton.elim` after `convert` exposed structure-equality goals violated Rule 4's purpose: the atomic diagnostic had already shown that the obstruction was not algebraic normalization.
- Calling `ring` while both `mulVec` and `matVec` remained in the goal ignored Rule 5 and §3.2: algebraic tactics only normalize expressions after wrapper syntax has been synchronized.

Use this protocol for future calculus proofs in wrapper-heavy spaces:

1. Write the mathematical derivative and sign argument before choosing Lean lemmas.
2. Search the current file, repository, and pinned `.lake/packages/mathlib`, then `#check` every selected declaration under the target imports.
3. Keep raw functions, `EuclideanSpace`, `PiLp`, and `WithLp` in separate proof layers; cross a boundary with one explicit equivalence or bundled continuous linear map.
4. When `convert` exposes equality of typeclass structures, stop the low-level transport attempt and seek a theorem stated at the desired abstraction level or an exact objective identity.
5. Test a local reproduction against stable imports. If the scratch file must import newly edited declarations, rebuild the module first.
6. Compile the actual target file with `lake env lean <file>` after each coherent edit and treat that result, not stale IDE or scratch-import output, as the final verification.

### 1.6 Decidability in Lemma Signatures
**The Problem:** If a lemma signature (the theorem statement itself) uses a construct that requires decidability (e.g., `if h : i ∈ s then ...` where `s : Finset κ`), Lean will fail with `failed to synthesize instance Decidable (i ∈ s)` during parsing. Attempting to fix this by adding `haveI : DecidableEq κ := Classical.decEq κ` inside the proof (`by ...`) fails because the signature is parsed before the proof.
**The Fix:** Prepend the lemma with `open Classical in` to provide classical decidability during the elaboration of the entire lemma statement and its proof.

### 1.7 Defeq Bypassing `simp` on Type Synonyms
**The Problem:** When working with type synonyms like `EuclideanSpace ℝ κ` (which uses `WithLp 2`), tactics like `simp only [PiLp.inner_apply, Real.inner_apply]` can leave behind opaque structural artifacts like `((WithLp.equiv 2 _).symm f).ofLp` or `starRingEnd ℝ`. `ring` treats these as opaque atoms and fails to close the goal.
**The Fix:** Because `ofLp`, `WithLp.equiv.symm`, and real `inner` are *definitionally equal* to function application and scalar multiplication, skip `simp` entirely. Use `change` to directly state the algebraic form (e.g., `change f i * f i = _`), followed immediately by `ring`. This is vastly more robust than hunting for structural `simp` lemmas.

### 14.7 `HasDerivAt.sum` vs `HasDerivAt.fun_sum`: Point-Free Sum vs. Eta-Expanded Lambda-Sum
**The Problem:** `HasDerivAt.sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) : HasDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x` (`Mathlib/Analysis/Calculus/Deriv/Add.lean`) exists under exactly the name one would guess, and *is* the right lemma mathematically — but its conclusion sums `A i` **in the function space** (a `Finset.sum` of `ℝ → E` values, via the `Pi.add`/`AddCommMonoid (ℝ → E)` instance), not the eta-expanded `fun x => ∑ i ∈ u, A i x`. Applying it where the goal is stated in the eta-expanded form (e.g. differentiating `fun τ => M.mulVec (g τ) i = ∑ j, M i j * g τ j` coordinatewise) produces a type mismatch:
```
HasDerivAt.sum fun j x => hterm j
has type
  HasDerivAt (∑ i_1 ∈ ?m, fun τ => M i i_1 * e (g τ) i_1) (∑ i_1 ∈ ?m, M i i_1 * e g' i_1) t
but is expected to have type
  HasDerivAt (fun x => ∑ i_1, M i i_1 * e (g x) i_1) (∑ i_1, M i i_1 * e g' i_1) t
```
**The Fix:** Use the sibling lemma `HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) : HasDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x`, which is exactly the eta-expanded form. Several Mathlib additive-derivative combinators come in this `X`/`fun_X` pair (generated via the `@[to_fun]` attribute). Note `HasDerivAt.add`/`.sub` are also stated in the pointwise-`Pi` form but happen to unfold *definitionally* to the eta-expanded lambda (so `exact`/`rw` still close goals stated as `fun τ => f τ + g τ` — see §2.17), whereas `HasDerivAt.sum`'s conclusion (`Finset.sum` over an arbitrary `Finset`, not a binary `Pi.add`) does not reduce as transparently — the mismatch is visible immediately in the elaborated type, as above. When composing a *finite, index-dependent family* of derivative facts (as opposed to two or three named ones), search explicitly for a `fun_`-prefixed variant before falling back to `convert`.

### 14.8 Proving `F t = F 0` via a Zero-Derivative FTC, Not by Computing the Real Derivative's Integral
**The Problem:** To show a mirror-map gradient increment along a flow lies in a fixed subspace (concretely: `entropyMirrorGradient (x t) - entropyMirrorGradient (x 0) = t • r - matVec M (posIntegratedTrajectory u t)`), the direct route is to integrate the (nonzero, matrix-valued) derivative of each piece and invoke `intervalIntegral.integral_eq_sub_of_hasDerivAt`. This forces separate continuity/interval-integrability side conditions for that real, more complex derivative expression (e.g. continuity of `t ↦ posEffectiveParameter u t`, which itself takes work to establish).

**The Fix (verified):** Instead, package the entire claimed identity as `F τ := entropyMirrorGradient (x τ) - τ • r + matVec M (posIntegratedTrajectory u τ)` and show `HasDerivAt F 0 τ` for *every* `τ` (the three pieces' derivatives cancel by construction: `(r - Mx(τ)) - r + Mx(τ) = 0`). Then apply `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) intervalIntegrable_const` with the **constant zero function** as the "derivative" — `intervalIntegrable_const` trivially discharges the integrability side condition (no continuity proof needed for the real, nonzero pieces), and `∫ 0 = 0` (`intervalIntegral.integral_zero`) immediately gives `F t - F 0 = 0`, i.e. `F t = F 0`. This pattern — prove a quantity invariant along a flow by showing its derivative is *identically zero* and applying FTC with the zero integrand — sidesteps continuity/measurability bookkeeping for the "real" (nonzero) pieces entirely, and generalizes to any "conserved quantity along a flow" argument.

### 14.9 `simp [defA, defB]` Unfolds Definitions but Does Not Chain into Unrelated Algebraic Facts
**The Problem:** After unfolding `posIntegratedTrajectory u 0` (an integral over the degenerate interval `[0,0]`) via `simp [posIntegratedTrajectory, euclideanOf]`, the goal was left as `matVec M (euclideanOf fun i => 0) = 0` rather than being closed — `simp` correctly evaluated the degenerate integral to the zero function, but it does not automatically know that a linear map (`matVec M`, a project-defined wrapper around `Matrix.mulVec`) sends the zero vector to zero, since that requires its own (unsupplied) simp lemma or reasoning through `matVec`'s definition.

**The Fix:** Split into two separately-named, separately-proved facts rather than expecting one `simp` call to chain an unfolding step with a downstream algebraic consequence:
```lean
have hz : posIntegratedTrajectory u 0 = 0 := by
  ext i; simp [posIntegratedTrajectory, euclideanOf]
have hmz : matVec M (0 : EuclideanSpace ℝ ι) = 0 := by
  ext i; simp [matVec, euclideanOf]
```
then combine with `rw [hz, hmz]` (or `simp [hz, hmz]`) rather than throwing the whole unfolding list at `simp` in one shot. This is a specific, concrete instance of "modularize tactic-heavy subgoals" (Rule 7): a `simp` call unfolding a project `def` is not a substitute for proving the algebraic fact that follows from that unfolding.

### 14.10 Reduce a Coordinatewise Generalized-Entropy Identity to Mathlib's `InformationTheory.klFun` Instead of Reproving Gibbs' Inequality
**The Problem:** `entropyBregman`'s coordinate term `a * Real.log (a / b) - a + b` (`a, b > 0`) is exactly the unnormalized Bregman divergence / KL-type "log-sum" inequality (Gibbs' inequality). One route is to prove nonnegativity and the equality case directly from `Real.log_le_sub_one_of_pos` or `Real.one_sub_inv_le_log_of_pos` (both exist in `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` and do give a correct, short nonnegativity proof) — but this route requires *separately* re-deriving the equality-case ("term = 0 iff a = b") characterization from scratch, since those two lemmas are one-directional inequalities, not iffs.

**The Fix (verified, more mergeable):** Recognize the identity `a * Real.log (a / b) - a + b = b * InformationTheory.klFun (a / b)` (provable by `dsimp [InformationTheory.klFun]; field_simp; ring`, for `b ≠ 0`), where `InformationTheory.klFun x = x * log x + 1 - x` (`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`) is Mathlib's Kullback-Leibler generator function. `klFun` already has both directions proved and available off the shelf: `klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x` and `klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1` (built from `strictConvexOn_klFun` via strict-convexity-implies-unique-minimizer machinery). Reusing this gives both the nonnegativity lemma *and* the equality case (needed for a Bregman-projection uniqueness argument) essentially for free, instead of separately re-deriving strict-convexity machinery. General lesson: before proving a "looks standard" real-analysis inequality (log-sum, entropy, relative-entropy style) from primitives, check `Mathlib.InformationTheory.KullbackLeibler` and `Mathlib.Analysis.Convex.SpecificFunctions` for an existing named generator function with the equality case already built in.

### 14.11 `IsMinOn f s a` Does Not Imply `a ∈ s` — Read the Filter Definition Before Trusting an "argmin" Reading
**The Problem:** `IsMinOn f s a` (`Mathlib/Order/Filter/Extr.lean`) unfolds to `IsMinFilter f (𝓟 s) a`, i.e. `∀ᶠ x in 𝓟 s, f a ≤ f x`, which via `isMinOn_iff : IsMinOn f s a ↔ ∀ x ∈ s, f a ≤ f x` means only "`a` beats every point of `s`" — it says **nothing** about whether `a` itself belongs to `s`. A theorem stating "the minimizer of `f` on `s` is unique" as `∀ y, IsMinOn f s y → y = a₀` (with no `y ∈ s` hypothesis) is generally **false**: take `y` to be any point outside `s` at which `f` happens to attain a value at least as small as `f a₀` (e.g. for a Bregman divergence `f x = entropyBregman x y₀` and `y := y₀`, `f y₀ = entropyBregman y₀ y₀ = 0` is the unconstrained global minimum of `entropyBregman · y₀` over *all* nonnegative points, so `IsMinOn f s y₀` is satisfied vacuously even when `y₀ ∉ s` and `y₀ ≠ a₀`).

**The Fix:** When formalizing "the unique minimizer of `f` over a constraint set `s` is `a₀`," always add the membership hypothesis explicitly: `∀ y, y ∈ s → IsMinOn f s y → y = a₀` (or unpack `s`'s defining conjunction directly, e.g. `Nonnegative y → matVec M y = matVec M x → IsMinOn f s y → y = x`). This is not a Lean quirk to work around cosmetically — it is a real mathematical gap in the naive statement, and it can only be caught by reading `IsMinOn`'s actual `Prop` content (via `#print`/source, or the `isMinOn_iff` unfolding lemma), not by pattern-matching on the English word "argmin" implied by the name.

### 14.12 Enforce Strict Isomorphism in `scratch.lean` 
**The Problem:** I created a proof for `exact h1` in `scratch.lean` assuming the goal was exactly `e.symm.finsetCongr (e.finsetCongr B'') ∈ P.parts`. However, in the main file, the type contained an unreduced `.toEmbedding` coercion: `e.symm.finsetCongr.toEmbedding (e.finsetCongr.toEmbedding B'')`. Because my scratch file missed this subtle type coercion, it falsely validated the proof, leading to a persistent "Type Mismatch Illusion" when injected into production.
**The Fix:** Never hand-write the goal state into `scratch.lean`. Always copy the *exact* type signatures, including all implicit coercions (`↑`, `.toEmbedding`, `.toFun`) from the raw `lake build` output or Lean Infoview into the scratchpad to prevent false positive compilations.

### 14.13 Do Not Chase Stale IDE Lint Errors
**The Problem:** I repeatedly tried to fix `unexpected token 'omit'` errors and type mismatches that were actually from older failed compilations, because I didn't wait for the synchronous `lake build` output. This led me to write patches for lines that had already shifted or been resolved.
**The Fix:** Do not act on immediate IDE feedback when fixing complex type or syntax errors. Instead, wait for the system to explicitly notify that the background `lake env lean` task has finished with a clear exit status, and only rely on that ground truth.

### 14.14 Target Definitional Equality Before Syntactic Equality (`simp`/`rw` vs `change`)
**The Problem:** `simp` and `rw` require strict syntactic matches (AST equivalence). They fail completely on deeply layered terms like `e.symm.finsetCongr.toEmbedding (e.finsetCongr.toEmbedding B'')` if the intermediate definitions aren't explicitly unfolded, even if mathematically they are identical (e.g. via `Finset.map_map`).
**The Fix:** When dealing with heavily layered equivalence types mapping to sets or subsets, bypass `rw` and prioritize `change` (e.g., `change B'' ∈ P.parts`). `change` forces Lean to check definitional equality, allowing the unifier to bridge the gap without strict syntactic matching.

### 14.15 DifferentiableAt / Chain Rule Roadblock (Mathlib's `deriv` vs Piecewise Functions)
**The Problem:** When attempting to reason about the derivative of a piecewise or constrained continuous function (e.g. `pathDelta = max 0 ...`), Mathlib's `deriv` defaults to `0` at non-differentiable points. Standard chain rule lemmas (like `HasDerivAt.max`) do not apply smoothly without proving strict `DifferentiableAt` everywhere, which is mathematically false for `max`. Attempting to force algebraic equational reasoning through `deriv` fails.
**The Fix:** Avoid differentiating non-smooth functions directly. Instead, break the argument down into structural inequalities over limits or use integral formulations (like `intervalIntegral.integral_eq_sub_of_hasDerivAt` coupled with `intervalIntegrable_const` for bounding). For the Lasso path, we bypassed the non-differentiability of `pathDelta` by integrating its bounds over intervals where the derivative is well-defined, rather than forcing a global `HasDerivAt` proof.

### 14.16 `linarith` Limitations on Non-linear / Asymptotic Bounds
**The Problem:** `linarith` fails to resolve bounds that involve non-linear transformations (e.g., $1/\log(1/\varepsilon)$ or `max` operations) unless the specific bounding relationship is explicitly stated as a linear inequality in the context first. It cannot "look inside" functions or asymptotic terms.
**The Fix:** Manually unroll non-linear or piecewise functions (like `max`) using specific lemmas (e.g., `le_max_left`, `lt_max_of_lt_left`) to create standalone linear inequality hypotheses (`have h_linear : A ≤ B := ...`). Only then feed these simplified hypotheses to `linarith`.

### 14.17 Matrix Operations on `EuclideanSpace` vs `ι → ℝ`
**The Problem:** `EuclideanSpace` and the standard function space `ι → ℝ` are distinct types in Lean, despite being mathematically isomorphic. Attempting to seamlessly apply standard Mathlib Matrix APIs (like `Matrix.mulVec`) to `EuclideanSpace` vectors, especially when disguised behind project-specific definitions like `matVec`, causes type mismatches and missing instance errors (e.g., `matVec_add`).
**The Fix:** Always explicitly coerce or unfold custom linear algebra definitions (`matVec`) down to the base `Matrix.mulVec` operation. Ensure that vectors are operating in the correct algebraic domain before invoking structural lemmas like `Matrix.mulVec_add` or spectral theorems (like PSD matrix bounds). 

