## Hallucinated Lemmas (Do Not Use)

These are lemmas that sound plausible but **do not exist** in Mathlib (or the project), or exist with different names/signatures. Organized by theme to make common mistake patterns easier to recognize.

---

## 1. Tactic Behavior Misconceptions

Tactics that don't support the operations you'd expect, or have subtle scope restrictions.

| Hallucinated Behavior | What was expected | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `linarith` (for `A ∧ B`) | Solve multiple inequalities in one goal. | **Structural Failure.** `linarith` only solves single leaf goals. Split with `constructor` or use `tauto`. |
| `linarith_finset_sum` | A tactic extension to deduce `∑ (x_i - y_i)^2 = 0 ↔ x = y` natively. | **Hallucinated Tactic.** `linarith` cannot see inside `Finset.sum`. You must manually unroll the sums into explicit scalars before using `linarith` or apply algebraic Finset identities. |
| `linarith` automatically interpreting `Set.Ioo` | `linarith` deducing bounds from interval membership. | **Context Blindness.** `linarith` does not understand sets. You must project or rewrite into inequalities first. |
| `linarith` automatically extracting structure properties | `linarith` natively understanding `l.hδ` to imply `0 < δ`. | **Context Blindness.** Tactics do not auto-unpack structures. You must explicitly pass `[l.hδ.1, l.hδ.2]`. |
| `positivity` (for `x ≤ 0`) | Proving negativity. | **Domain Failure.** `positivity` only proves `x ≥ 0` or `x > 0`. Use `rw [neg_nonpos]` or `apply neg_nonpos.mpr` first to flip the goal. |
| `positivity` (for proving `x > 1` bounds) | Proving that constants/exponentials are strictly greater than 1. | **Domain Failure.** `positivity` only proves `x > 0` or `x ≥ 0`. Prove bounds relative to 1 using transitivity (e.g., `Real.exp_le_exp` and `Real.exp_one_gt_two`). |
| `omega` (for unconstrained `k`) | Automatically prove bounds like `k ≠ 0` from local context. | **Context Blindness.** `omega` only sees hypotheses in the local context. Without an explicit `1 ≤ k` bound in the signature, `k` is unconstrained and the goal is unprovable. |
| `IsOpen.fun_prop` | Prove openness of sets using `fun_prop`. | **Domain Failure.** `fun_prop` only supports function-property goals (continuity, measurability). Use `continuity` or `isOpen_lt`. |
| `Fintype.toLocallyFiniteOrder` for `Finpartition` | Automatically deriving interval finiteness for set partitions. | **Defeq Hang.** Synthesizing this instance via the generic fallback on the complex power-set wrapper causes Lean's typeclass inference to loop infinitely. Explicit structural proofs are required. |
| `ContinuousAt.continuousAt` | Dot-projection on a continuity proof. | **Type Error.** `ContinuousAt f x` is a `Prop`, not a structure. Use the proof term directly. |
| `div_neg_of_neg_of_pos` vs `div_neg_of_pos_of_neg` | Quotient sign analysis. | **Orientation Confusion.** `div_neg_of_neg_of_pos` is `(Neg/Pos)`. `div_neg_of_pos_of_neg` is `(Pos/Neg)`. Use `positivity` to avoid manual sign variants. |
| `h.neg_pos` | Dot-notation for negation-of-inequality. | **Namespace Error.** Props do not support dot-notation for group lemmas. Use functional application `neg_pos.mpr h`. |
| `Continuous.mul_const` | Continuity of multiplication by a constant (dot-notation). | **Namespace Error.** Use `fun_prop` or `Continuous.mul continuous_const`. |
| `Continuous.const_mul` | Continuity of constant multiplication (dot-notation). | **Namespace Error.** Use `fun_prop` or `continuous_const.mul`. |
| `continuousAt_const (b := ...)` | Named argument for the constant value. | **Hallucinated Parameter.** The argument is named `y`. Use `(y := ...)` or rely on unification. |
| `n = k → term` (as if `h : n = k` were already available inside `term`) | Elaborating subtype witnesses or hidden proof fields using the equality. | **Scope Error.** A plain arrow is nondependent, so the equality proof is not in scope while Lean elaborates `term`. Use `∀ hk : n = k, term` instead. |
| `cases h_eq` on `h_eq : i.val = k` | Rewriting only the target while leaving the rest of the context unchanged. | **Dependent-Elimination Error.** `cases` transports the whole dependent context, including hidden subtype proofs. Move the transport into a fresh helper subgoal over a new variable. |
| `clear h` when the printed goal does not mention `h` | Removing an apparently unused equality or transport witness. | **Hidden-Cast Trap.** Earlier `change`/`convert` steps may have inserted an `Eq.ndrec` cast that still depends on `h`. Inspect with `set_option pp.proofs true` or `pp.all true` first. |
| `mul_pos_iff.mp` (as direct implication) | Extracting factors from `0 < a * b`. | **Iff Conflict.** `mul_pos_iff` returns a disjunction `(0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)`. Use `mul_pos_iff_of_pos_left` instead. |
| `h.integrable_iff` (on unfolded `EventuallyEq`) | Dot-notation on `EventuallyEq`. | **Projection Failure.** If the `EventuallyEq` notation is unfolded by Lean, dot-notation fails. Use the functional form `Filter.EventuallyEq.integrable_iff h`. |
| `PNat.coe_injective.injOn s` | Using `injOn` as a function of the set. | **Implicit Conflict.** The set argument `{s}` is implicit in the alias; passing it explicitly is a type mismatch. Use `Set.injOn_subtype_val` or `@Function.Injective.injOn`. |
| definitional equality of scientific float and division (e.g., `3.5530e-8` and `35530 / 10 ^ 12`) | Unifying them in `change` | **Definitional Rigidity.** Decimal float literals use `OfScientific` while division representations use division on `Real`. They are propositionally equal but not definitionally equal. Use `have h : 3.5530e-8 = 35530 / 10 ^ 12 := by norm_num` then `rw [h]`. |
| out-of-order declarations (referencing later identifiers) | Accessing later lemmas in helper proofs | **Sequential Scope.** Lean processes file contents top-down. Precursor lemmas must be defined prior to the dependent proofs. Rearrange declarations bottom-up. |
| `ext1 s` (inside `convert` for function-level goals) | Apply extensionality to show function equality. | **Tactic Congruence Action.** `convert` automatically applies extensionality on function binders, transforming function-level equality `f = g` to value-level equality `f x = g x`. Calling `ext` inside a `convert` block will fail. Use `simp` directly on the generated value-level equation. |
| `norm_pos_iff.mpr` (on `¬‖w‖ = 0`) | Apply positivity equivalence directly to a negated equality | **Type Mismatch.** `norm_pos_iff` operates on `w ≠ 0`, not `¬‖w‖ = 0` (even though they are propositionally equivalent). Use `lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)`. |
| `one_mul` (on coerced Reals) | Simplify `↑1 * X` to `X` | **Syntactic Mismatch.** Coercing `NNReal` 1 to `ℝ` creates an AST of `↑1`, which `one_mul` (expecting literal `1`) doesn't match. Use `simp` or `push_cast` instead. |
| `notation:50` for algebraic operators | Assigning precedence 50 so it binds correctly | **Parser Hallucination.** Equality is 50, so custom operators must have strictly higher precedence (e.g., `infixl:73`) to prevent left-to-right parsing errors like `x ⊙ y = y ⊙ x` becoming `(x ⊙ y = y) ⊙ x`. |
| `Set.not_mem_compl_iff.mp` | Resolving `x ∉ Sᶜ ⊢ x ∈ S` | **Hallucinated / Unnecessary.** Lean aggressively simplifies sets. Use primitive logic `by_contra h; exact h_not h` instead. |
| `Measurable.prod_mk` | Tuple construction of measurable functions | **Name Error.** Lean 4 shifted to camelCase: use `Measurable.prodMk`. |
| `rw [measureReal_compl]` | Expected it to generate two goals: `MeasurableSet s` and `μ s ≠ ∞`. | **Tactic Behavior Misconception.** `measureReal_compl` only generates `MeasurableSet s`. Providing an extra `· exact measure_ne_top _ _` will cause `error: No goals to be solved`. |
| `rw [Fin.sum_univ_eq_sum_range]` (no explicit function argument) | Rewriting `∑ j : Fin n, Y (rows ↑j)` into a `Finset.range n` sum. | **Higher-Order Pattern Failure.** `rw` cannot abstract `?f ↑j` out of the nested application `Y (rows ↑j)`; it fails with "Did not find occurrence". Pass the function explicitly: `rw [Fin.sum_univ_eq_sum_range (fun i => Y (rows i)) n]`, or use `simp only [Fin.sum_univ_eq_sum_range]` whose matcher handles such patterns. |
| `HDiv` for vectors (`v / 2`) | Dividing a vector by a scalar using `/`. | **Instance Missing.** `EuclideanSpace` does not support vector-by-scalar division. Use scalar multiplication `(1/2 : ℝ) • v`. |
| Automatic $L^2$ norms for tuples | Assuming `E × F` inherits a Hilbert space norm. | **Instance Missing.** Mathlib gives tuples the $L_\infty$ maximum norm. Explicitly wrap it in `WithLp 2 (E × F)`. |
| `lasso_reduction` | A project-specific placeholder lemma that I assumed had mathematical content. | **Hallucinated.** It was defined as `lemma lasso_reduction : True := trivial`. Inspect the source of project stubs before relying on them. |
| `ring` on `EuclideanSpace` | Simplify vector algebra (e.g. `x + (y - x) = y`) automatically. | **Domain Failure.** `ring` only handles commutative rings (scalars). Use `abel` for vector addition/subtraction, but note that `abel` cannot distribute scalar multiplication (`•`). Use explicit `smul_add` and `add_smul` rewrites first. |
| `deriv (fun x => f x * g x)` auto-simplifying via `simp` | Applying the product rule seamlessly without manual differentiability proofs in the context. | **Context Blindness.** The `simp` simplifier refuses to expand the product rule (`deriv_mul`) unless the local context can transparently prove that both `f` and `g` are differentiable. Abstract the derivative expansions into modular helper lemmas instead of fighting the simplifier inline. |

---

## 2. Interval Arithmetic (LeanCert Tactics)

Issues specific to the `interval_decide` / `certify_bound` tactics from the `leancert` package.

| Hallucinated Behavior | What was expected | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `interval_decide n` (depth argument) | Increasing certificate search depth for `interval_decide`. | **Invalid Syntax.** `interval_decide` takes no numeric argument. Use `certify_bound n` (or its alias `interval_bound n`) for universally-quantified bounds with adjustable Taylor depth. |
| `ContinuousOn.intervalIntegrable` (as a bound-pinning alternative) | Producing `IntervalIntegrable f volume a b` with concrete, pinned endpoints. | **Metavar Trap.** `ContinuousOn.intervalIntegrable` exists but takes `{a b : ℝ}` as implicit arguments inferred from the `uIcc` hypothesis. Using it in a backward rewrite `rw [← integral_add_adjacent_intervals h1 h2]` often leaves endpoints as metavariables. Use `Continuous.intervalIntegrable a b` with explicit `a b` instead. |
| `interval_decide` with `√(p/q)` goals closes completely | `interval_decide` closes a goal involving `√0.79` etc. | **Sqrt Side Goal.** `interval_decide` normalizes `√(p/q)` → `√p / √q` and emits the equivalence as an extra side goal. Always check for remaining goals afterward; close them with `· left; ring` or `· ring`. |

---

## 3. Naming & Namespace Errors

These lemmas exist in Mathlib but under a different name or namespace. Calling the wrong form causes a "unknown identifier" error or unification failure.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Real.tendsto_inv_atTop_zero` | $1/x \to 0$ as $x \to \infty$. | **Namespace Error.** Use `tendsto_inv_atTop_zero` (global namespace, `Mathlib/Topology/Algebra/Order/Field.lean`). |
| `Matrix.dotProduct` (as a mandatory namespace) | Assume `dotProduct` requires `Matrix.` prefix when matrix libraries are imported. | **Namespace Refactor.** When `Mathlib.Data.Matrix.Basic` is imported, `dotProduct` is exposed to the root namespace. You do not need the `Matrix.` prefix. |
| `WithLp.equiv` (mapping *into* Lp) | Assume `WithLp.equiv p α x` coerces `x : α` into the $L_p$ space. | **Orientation Error.** The equivalence maps *from* the $L_p$ space *to* the base type. Use `(WithLp.equiv p α).symm x` to cast into the $L_p$ space. |
| `rexp_lt_rexp` | $e^x < e^y \iff x < y$ | **Name Error.** Use `Real.exp_lt_exp` (an `Iff`, in `Mathlib/Analysis/Complex/Exponential.lean`). |
| `div_le_div` | Bounding `a/b ≤ c/d`. | **Ambiguous/Wrong Name.** Use `div_le_div₀` for the unbundled version with explicit hypotheses. |
| `div_le_of_le_mul` | Bounding `A / C ≤ B` from `A ≤ B * C`. | **Name Error.** Removed in Mathlib4. Use `div_le_iff₀` instead. |
| `div_le_one_iff₀` | Equivalent of `div_le_one₀`. | **Hallucinated Suffix.** Use `div_le_one₀`. |
| `div_le_one` | `x / y ≤ 1 ↔ x ≤ y`. | **Ambiguous.** Use `div_le_one₀` (with `0 < y`). |
| `EventuallyEq.refl` | Identity relation for filters. | **Namespace Error.** The correct form is `Filter.EventuallyEq.refl`. |
| `Filter.inf_le_left` | Membership in filter intersection. | **Exists correctly** as `Filter.inf_le_left`. Was hallucinated in context, but the lemma is valid. |
| `Asymptotics.IsBigO.refl` | Identity asymptotic bound. | **Namespace Error.** Use `isBigO_refl` (top-level) or `Asymptotics.isBigO_refl`. |
| `Asymptotics.IsBigO.congr` | Changing functions in `IsBigO`. | **Namespace Error.** Use `isBigO_congr` or `Asymptotics.isBigO_congr`. |
| `Filter.eventually_of_forall` | Converting universal truth to eventually. | **Namespace Error.** Use `Filter.Eventually.of_forall` (note the capital `E`). |
| `tsum_re` | Distribute real-part over infinite sum. | **Namespace Error.** Use `Complex.re_tsum`. |
| `re_add` | Distribute real-part of sum. | **Namespace Error.** Use `Complex.add_re`. |
| `re_sub` | Distribute real-part of subtraction. | **Namespace Error.** Use `Complex.sub_re`. |
| `re_mul` | Distribute real-part over product. | **Namespace Error.** Use `Complex.mul_re` or `Complex.re_ofReal_mul`. |
| `div_add` | Distribute division over addition. | **Name Error.** Use `add_div`. |
| `IsBigO.div_const` | Dividing a bound by a constant. | **Hallucinated.** Use `IsBigO.const_mul_left` or `IsBigO.const_mul_right` with the inverse `c⁻¹`. |
| `setIntegral_nonneg` | Prove `0 ≤ ∫ x in s, f x`. | **Namespace Error.** Use `MeasureTheory.setIntegral_nonneg`. |
| `fourier_inv_fourier_eq` | Fourier inversion formula. | **Name Error.** Use `MeasureTheory.Integrable.fourierInv_fourier_eq`. |
| `Tannery` | Tannery's Theorem for sums. | **Name Error.** Use `tendsto_tsum_of_dominated_convergence`. |
| `finite_Iio` (for PNat) | Proof that `{x | x < n}` is finite. | **Hallucinated.** Use `(Set.finite_lt_nat n).subset` or `(Finset.Iio n).finite_toSet`. |
| `Filter.le_atTop_iff` | `l ≤ atTop ↔ ...` | **Hallucinated.** Use `Filter.atTop_basis.ge_iff` instead. |
| `atTop_le_cofinite` (for PNat) | `atTop ≤ cofinite` on `ℕ+`. | **Conditional.** Requires `NoTopOrder` instance; use a manual `le_antisymm` proof if synthesis fails. |
| `summable_of_nonneg_of_le` | Comparison test for series. | **Capitalization Error.** Use `Summable.of_nonneg_of_le` (note capital `S`). |
| `integral_univ` | Universal integral conversion. | **Name Error.** Use `MeasureTheory.setIntegral_univ`. |
| `VectorFourier.fourierInv_eq` | Inverse Fourier integral representation. | **Namespace Error.** Use `Real.fourierInv_eq`. |
| `finrank_self` | Dimension of a field over itself. | **Namespace Error.** The full name is `Module.finrank_self` (`Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean`). |
| `integral_mul_left` | Factoring constant from integral. | **Namespace Error.** Use `integral_const_mul` or `MeasureTheory.integral_mul_left`. |
| `lt_div_iff₀` (matching `≤`) | Rewriting `a ≤ b / c`. | **Syntactic Mismatch.** `lt_div_iff₀` is for strict inequalities `<`. Use `le_div_iff₀` for `≤`. |
| `setIntegral_congr` | Congruence for set integrals. | **Name Error.** Use `MeasureTheory.setIntegral_congr_fun` or `MeasureTheory.Integrable.congr`. |
| `measure_singleton` | `μ {x} = 0` | **Namespace Error.** Use `MeasureTheory.measure_singleton` and ensure `μ` is atomless. |
| Explicit Möbius Function of `Finpartition` | `μ(P, ⊤) = (-1)^{\|P\|-1} (\|P\|-1)!` | **Missing Theory.** Mathlib defines the abstract `IncidenceAlgebra.moebius_bot` but has zero concrete instantiations mapping it to the factorials for set partitions. Do not rely on abstract combinatorics API to compute concrete constants. |
| `Finpartition.sum_bind` | Swapping $\sum_{P} \sum_{Q \in \Pi(P)}$ to $\sum_{Q} \sum_{P \ge Q}$ | **Missing Theory.** Mathlib has `Finset.sum_bind` but no specific structural equivalents for iterating over partition refinements. |
| `iteratedDeriv_exp_quadratic_zero` | `iteratedDeriv n (fun t => exp(v * t^2 / 2)) 0 = (n-1)!! v^(n/2)` | **Missing Theory.** Mathlib lacks pure calculus properties for the higher derivatives of Gaussian kernels evaluated at zero (Hermite polynomials). |
| Stein's Lemma for Polynomials | `∫ x, L(x) * ∏ K_j(x) dμ = ∑_j Cov(L, K_j) ∫ x, ∏ K_k(x) dμ` | **Missing Theory.** Mathlib possesses basic integration by parts but lacks the generalized Stein's lemma for multilinear products of dual observables under Gaussian measures. |
| `zero_le_one.trans_le` | Transitivity via dot-notation. | **Hallucinated.** Use `zero_le_one.trans h_le` (`.trans` not `.trans_le`). |
| `h_ab.trans_le` | Dot-notation transitivity on Props. | **Namespace Error.** Props don't support dot-notation for order lemmas. Use `le_trans h_ab`. |
| `summable_nat_to_pnat` | Bridging `Summable` on `ℕ` to `ℕ+`. | **Name Error.** Use `summable_pnat_iff_summable_nat`. |
| `log_le_log` (as `Iff`) | Use as structure for `.mp` projection. | **Return Type Error.** It returns a `Prop` (inequality). Use `log_le_log_iff` which is an `Iff`. |
| `nhdsWithin_Ioi_self_neBot` | Right-neighborhood within filter is non-empty. | **Name Error.** Use `nhdsWithin_Ioi_neBot le_rfl` or `nhdsGT_neBot`. |
| `Exists.and` | Filter or proposition projection operator. | **Hallucinated.** Lean attempts to project `Exists.and` if a filter membership type resolves to `Exists`. Use `Filter.Eventually.and` via standard function application. |
| `List.getLast_mem l h` | Access membership with explicit list `l`. | **Signature Error.** The list `l` is implicit `{l : List α}`. Call with `List.getLast_mem h` only. |
| `Complex.ofReal_smul` | Bridge scalar and field multiplication for coerced reals. | **Name Error.** Use `Algebra.smul_def` or `smul_eq_mul`. |
| `nonpos_of_mul_nonneg_left` (for right target) | Bounding the **right** factor when the left is negative. | **Orientation Error.** `_left` targets the left factor. Use `nonpos_of_mul_nonneg_right` for the right factor. |
| `Continuous.sum` | Prove continuity of a finite sum. | **Name Error.** Use `continuous_finset_sum` instead. |
| `Real.rpow_nonneg_of_nonneg` | Prove `0 ≤ x ^ y` from `0 ≤ x`. | **Name Error.** Use `Real.rpow_nonneg`. |
| `rpow_mul_rpow` | `x^a · x^b = x^(a+b)` for real powers. | **Name Error.** Use `Real.rpow_add` (requires `0 < x`). |
| `IndepFun.integral_bilin` | Compute the expectation of a bilinear form of independent random variables. | **Namespace Error.** Use `ProbabilityTheory.IndepFun.integral_bilin`. Verify the fully qualified name in the current import context with `#check`. |
| `IndepFun.comp` | Preserve independence after postcomposing by measurable functions. | **Namespace Error.** Use `ProbabilityTheory.IndepFun.comp`. |
| `Set.smul_Ici` | Scaling an interval `[a, ∞)`. | **Namespace Error.** Use `LinearOrderedField.smul_Ici` (`Mathlib/Algebra/Order/Field/Pointwise.lean`). |
| `Set.Ici_inter_Iic_self` | `Ici a ∩ Iic a = {a}` | **Name Error.** Use `Set.Ici_inter_Iic` (gives `Icc a a`) followed by `Set.Icc_self`. |
| `Complex.abs_re_le_abs` | Bounding real part by absolute value. | **Name Error.** Use `Complex.abs_re_le_norm` (or `RCLike.abs_re_le_norm`). |
| `Summable.const_div` | Divide a sum by a constant. | **Name Error.** Use `Summable.mul_left` or `Summable.mul_right` with the inverse `c⁻¹`. |
| `inv_le_inv_of_le` | Bounding `b⁻¹ ≤ a⁻¹` given `a ≤ b`. | **Name Error.** Use `inv_le_inv₀` or `(inv_le_inv₀ hb ha).mpr hab`. |
| `integrableAtFilter_atBot_iff_comp_neg` | Mapping integrability between `atBot` and `atTop`. | **Hallucinated.** Use `rw [← Filter.map_neg_atTop]` followed by `MeasurableEmbedding.integrableAtFilter_iff_comap`. |
| `IsBigO.mul_split` | Splitting products in Big-O notation. | **Hallucinated.** Use explicit `have` anchors for each factor and `IsBigO.mul`. |
| `Filter.Tendsto.comp_id` | Composing a limit with identity. | **Hallucinated.** Use `Filter.Tendsto.congr'` or `convert`. |
| `tendsto_pow_mul_exp_neg_atTop_nhds_zero` | $x^n e^{-ax} \to 0$ | **Exists** as `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` in `Mathlib/Analysis/SpecialFunctions/Exp.lean`. |
| `List.get?` | Standard option list lookup | **Deprecated.** Renamed to `List.getElem?` to align with the `GetElem?` typeclass. |
| `List.getD_cons` | Equation lemma to simplify `List.getD` on lists | **Hallucinated.** `List.getD` compiles to `Option.getD` and `List.getElem?`, so it doesn't have direct equations. Use `List.getD_eq_getElem` followed by `List.getElem_zero_cons` / `List.getElem_succ_cons`. |
| `List.getElem_cons_zero` | List lookup at index 0 | **Name Error.** Index name precedes constructor name. Use `List.getElem_zero_cons`. |
| `List.getElem_cons_succ` | List lookup at index i + 1 | **Name Error.** Index name precedes constructor name. Use `List.getElem_succ_cons`. |
| `List.append` | Simplify list concatenation `++` | **Wrong Rewrite Suffix.** evaluated using the recursive equations `List.cons_append` and `List.nil_append` rather than definition name. |
| `Real.cos_lipschitz.dist_le_mul` | Lipschitz continuity for `cos` distance | **Hallucinated Namespace.** The correct property is `Real.lipschitzWith_cos`, which must be passed as an argument to the global lemma `LipschitzWith.dist_le_mul`. |
| `iIndepFun (fun _ => inferInstance)` | Pass typeclass arguments positionally | **Signature Error.** Lean 4 implicit named parameters cannot be passed positionally. You must use named arguments: `iIndepFun (m := fun _ => inferInstance)`. |
| `reluLinearization.relu` | Use `relu` from `Linearization.lean` | **Hallucinated Namespace.** The correct namespace is `NTK.relu` or just `relu` with `LeanMachineLearning.Optimization.NTK.Linearization` imported. |
| `relu_linearization_error_le net x W W₀` | Use the 1D scalar lemma directly on network structures. | **Signature Error.** `relu_linearization_error_le` is a scalar lemma that takes `(a b : ℝ)`. It does not accept `net`, `x`, or `W`. |
| `taylor_remainder_lagrange` (for `ℝ → ℝ`) | A simple, directly applicable 1D Lagrange remainder theorem based on `deriv`. | **Buried/Inaccessible.** Mathlib uses multilinear maps and `ContDiff` for Taylor theorems. Instead of struggling with Banach space overhead, construct an auxiliary function and apply `exists_hasDerivAt_eq_slope` twice (MVT). |
| `cauchy_schwarz` (as a tactic) | Automatically unwrap nested Euclidean/Frobenius norms with Cauchy-Schwarz. | **Hallucinated.** No such universal tactic exists. Use `Finset.sum_mul_sq_le_sq_mul_sq` and manually unwrap norms instead. |
| Auto-simplification of `deriv` | `deriv (fun x => x^2) = fun x => 2*x` solved instantly by `simp`. | **Context Blindness.** `simp` cannot compute derivatives without proofs of differentiability. Use specific `HasDerivAt` properties (like `hasDerivAt_pow`) and prove differentiability concurrently. |
| `(· ⟂ᵢ[μ] ·) on X` (ambient `on` notation) | Pairwise-independence relation over an indexed family, as in `strong_law_ae`'s statement. | **Scope Error.** `on` is notation for `Function.onFun` and requires `open Function`; without it Lean reports `unknown identifier 'on'`. Write `Function.onFun (· ⟂ᵢ[μ] ·) X` explicitly or add the open. |
| `HasGradientAt.comp_hasDerivAt` | Compose a multivariable gradient certificate with a scalar-parameterized curve. | **Hallucinated.** Convert with `HasGradientAt.hasFDerivAt`, then use `HasFDerivAt.comp_hasDerivAt`. If that exposes incompatible hidden `AddCommGroup`/`Module` instances, do not force structure equality; use an existing energy-dissipation theorem or an exact objective bridge instead. |
| `matVec_hasDerivAt` | Differentiate `fun t ↦ matVec M (x t)` by linearity. | **Absent in the pinned project and Mathlib.** Package `matVec M` as a continuous linear map and compose its `hasFDerivAt`, or build coordinates with `hasDerivAt_pi`, `HasDerivAt.fun_sum`, and `HasDerivAt.const_mul`. Keep the entire proof in one `EuclideanSpace`/`PiLp` representation to avoid `PiLp` versus `WithLp` instance mismatches. |
| `ConvexOpt.GFTrajectory.antitone` / `ConvexOpt.gf_antitone` | Obtain objective antitonicity directly from a gradient-flow trajectory. | **Hallucinated.** Use `ConvexOpt.gf_monotone_decrease` to get derivative `-‖gradient f (w t)‖²`, prove it is nonpositive with `neg_nonpos.mpr (sq_nonneg _)`, and apply `antitone_of_hasDerivAt_nonpos`. |
| `coordinateSquare_nonnegative` | State that the coordinatewise square of a Euclidean vector is nonnegative. | **Absent under this name.** For a positive-DLN trajectory use `Lasso.posEffectiveParameter_nonnegative`; for a standalone vector unfold `coordinateSquare`/`euclideanOf` coordinatewise and apply `mul_self_nonneg`. |
| `HasDerivAt.sum (fun j _ => hterm j)` (assumed to produce an eta-expanded lambda-sum) | Differentiate `fun τ => ∑ j, A j τ` from per-index `HasDerivAt (A j) (A' j) t` facts (e.g. summing `HasDerivAt`s over `j : ι` to differentiate a matrix-vector product `M.mulVec (g τ)` coordinatewise). | **Wrong shape, not a wrong name.** `HasDerivAt.sum` exists and is correctly named, but its conclusion is `HasDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x` — a `Finset.sum` **in the function space** (via `Pi.add`), which Lean reports as `HasDerivAt (∑ i_1 ∈ ?m, fun τ => M i i_1 * e (g τ) i_1) (...)`, not `HasDerivAt (fun x => ∑ i_1, M i i_1 * e (g x) i_1) (...)`. Use the eta-expanded sibling `HasDerivAt.fun_sum (h : ∀ i ∈ u, HasDerivAt (A i) (A' i) x) : HasDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x` instead. |

---

## 4. Integration & Measure Theory

Lemmas for integrals or measure theory that don't exist or have incorrect signatures/hypotheses.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `MeasureTheory.integral_restrict_eq_setIntegral` | Relate restricted integral to set integral (global form). | **Hallucinated.** Use `rfl` or `MeasureTheory.setIntegral_univ` to bridge `∫ x in s, f x ∂μ` and `integral (μ.restrict s) f`. |
| `integral_restrict_eq_setIntegral` | Same as above (no namespace). | **Hallucinated.** Use `MeasureTheory.setIntegral_univ` and `rfl`. |
| `MeasureTheory.Measure.integral` | Dot notation `μ.integral f` for integrals. | **Namespace Refactor.** Dot notation for measure was removed in Mathlib4. Use `integral μ f`. |
| `integral_sub` | Split the integral of a difference. | **Namespace Error.** Use `MeasureTheory.integral_sub`. |
| `integral_const` | Evaluate the integral of a constant function. | **Namespace Error.** Use `MeasureTheory.integral_const`. |
| `memLp_const` | Put a constant function in `L^p`. | **Namespace Error.** Use `MeasureTheory.memLp_const`. |
| `MemLp.sub` | Show `f - g` is in `L^p`. | **Namespace Error.** Use `MeasureTheory.MemLp.sub`. |
| `Measure.setIntegral_comp_div` | Scaling restricted (set) integrals by `x/a`. | **Name Error.** Use `Measure.setIntegral_comp_smul` (takes the measure and the scalar as explicit arguments). |
| `integral_comp_div` (missing μ) | Scaling integrals in files with `variable (μ : Measure E)`. | **Signature Mismatch.** The measure becomes an explicit first argument. Use `Measure.integral_comp_div volume f a`. |
| `integrableAtFilter_comp_neg` | `IntegrableAtFilter (f ∘ neg) l` from `IntegrableAtFilter f l`. | **Hallucinated.** Use `integrableAtFilter_atBot_iff_comp_neg` for atBot/atTop mapping (itself an alias chain — see section 3). |
| `Real.volume_comap_neg` | Negation-invariance of Lebesgue measure. | **Hallucinated.** Use `(MeasurableEquiv.neg ℝ).map_symm.symm` + `Real.smul_map_volume_mul_left`. |
| `Integrable.restrict s` | Direct integrability restriction projection. | **Hallucinated.** Use `.integrableOn s` or `.mono_measure Measure.restrict_le_self`. |
| `List.sublist_of_length_eq` | `l₁ <+ l₂ → l₁.length = l₂.length → l₁ = l₂` | Standard list sublist identity. | `Mathlib/Data/List/Basic.lean` |

---

## 11. Combinatorics & Partition Lattice (Cumulant Formalization)

Lemmas hallucinated during the formalization of cumulants and partition lattices.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `jointMoment_eq_blockMoment_univ` | One-step equivalence between joint moment and block moment on `Finset.univ`. | **Hallucinated.** This requires an explicit manual definition bridge because `jointMoment` and `blockMoment` have slightly different signatures (one takes a tuple of indices, one evaluates on a `Finset`). |
| `Finset.prod_union_inter` | `∏ x ∈ s ∪ t, f x = (∏ x ∈ s, f x) * (∏ x ∈ t, f x) / (∏ x ∈ s ∩ t, f x)` | **Hallucinated / Unconditional.** Requires `f x` to be invertible. Use `Finset.prod_union` with `Disjoint s t` instead. |
| `MeasureTheory.integral_add` (without integrability) | Splits an integral of a sum into a sum of integrals unconditionally. | **Hypothesis Required.** Integrals do not split unconditionally. You must provide `Integrable f` and `Integrable g`. |
| `IndepFun.integral_mul` | The expectation of a product of independent variables factors into the product of their expectations. | **Name/Signature Error.** The correct theorem is `ProbabilityTheory.IndepFun.integral_bilin`. It requires explicitly specifying the bilinear map (e.g., `mul` for real numbers). |
| `Finpartition.sum_cumulantTransform` | A pre-existing generalized Möbius inversion identity for partition lattices to prove vanishing of cumulants. | **Hallucinated.** While general Möbius inversion exists in Mathlib (`Order.Mobius`), there is no out-of-the-box structural theorem stating that `cumulantTransform` vanishes on split functions. Must be proved manually (`cumulantTransform_eq_zero_of_split`). |
| `integral_union_ae` | `∫ x in s ∪ t, f x = ∫ x in s, f x + ∫ x in t, f x` without conditions. | **Hypothesis Required.** Requires `AEDisjoint μ s t`. Fails if sets overlap on non-null sets. The correct lemma is `MeasureTheory.integral_union_ae`. |
| `measureReal_univ` | Simplify `μ.real Set.univ` for a probability measure. | **Hallucinated.** Use `simp [MeasureTheory.integral_const]` or the `IsProbabilityMeasure` instance to simplify the measure of `univ`. |
| `Integrable.comp_aemeasurable` | Compose an integrable function with an a.e.-measurable map. | **Hallucinated.** For pushforwards, use `MeasureTheory.integral_map`, `integrable_map_measure`, or prove the mapped integrability statement directly. |
| `MemLp.comp_aemeasurable` | Compose an `L^p` function with an a.e.-measurable map. | **Hallucinated.** Use pushforward-space lemmas (`Measure.map`, `MeasureTheory.integral_map`) and the existing `MemLp` lemmas that match the exact measure context. |
| `Measure.pi.isProbabilityMeasure` (as a direct unconditional instance) | Produce `IsProbabilityMeasure` for `Measure.pi` automatically. | **Context Trap.** `Measure.pi` preserves `IsProbabilityMeasure`, but the marginal measures (like `gaussianReal`) must explicitly have their instances in scope. If they are missing, synthesis fails cryptically. |
| `gaussianReal_isProbabilityMeasure` | Default global instance for `IsProbabilityMeasure (gaussianReal m v)`. | **Instance Scope Error.** May require explicit instantiation (`haveI : IsProbabilityMeasure ...`) or specific imports to trigger resolution. |
| `integral_gaussian_density_le_tau` | High-level API bounding the integral of $\frac{1}{\sqrt{2\pi}} e^{-x^2/2}$ over $[- \tau, \tau]$ by $\tau$. | **Hallucinated.** Mathlib lacks high-level Gaussian density bounding APIs. Proving this requires descending deep into Lebesgue integration, which is non-trivial. |
| `AEStronglyMeasurable.norm` | Turn `AEStronglyMeasurable f` into a named theorem for `AEStronglyMeasurable (fun x ↦ ‖f x‖)`. | **Name Error / Projection Guess.** Do not guess this theorem name. Search for the exact measurability lemma or work through a verified `MemLp`/`AEMeasurable` result instead. |
| `MeasureTheory.integral_mul_left` | Factoring constant from real multiplication integral | **Namespace / Type Error.** Bridge to `MeasureTheory.integral_smul` using `smul_eq_mul` instead. |
| `hoeffding_bernoulli` | A specific Bernoulli concentration bound theorem. | **Hallucinated.** Mathlib handles Bernoulli bounds via the generalized sub-Gaussian API. Use `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` for bounded variables. |
| `map_gaussianRowMeasure_dotProduct` | Pushing forward a row measure via dot product. | **Hallucinated Name.** Mathlib uses `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`, applied to a `ContinuousLinearMap`. |
| `IsGaussian (Measure.pi ...)` (auto-synthesis) | Auto-synthesis of `IsGaussian` for product measures over `Fintype`. | **Instance Missing.** Mathlib does not provide a blanket `IsGaussian` instance for `Measure.pi`. You must construct it manually or rely on `stdGaussian`. |
| `iIndepFun_infinitePi` (expected from `Mathlib.Probability.ProductMeasure`) | Independence of coordinate-wise functions under an infinite product measure. | **Import-Direction Error.** The lemma lives *upstream* in `Mathlib/Probability/Independence/InfinitePi.lean`, which imports `ProductMeasure.lean` — not vice versa. Add `import Mathlib.Probability.Independence.InfinitePi` explicitly. |
| `Measure.infinitePi_map_eval i` (index-only argument) | Pushforward of `Measure.infinitePi μ` under coordinate evaluation. | **Signature Error.** `μ` is an explicit argument (variable-block inflation): `Measure.infinitePi_map_eval μ i`. Same for the root-namespace `measurePreserving_eval_infinitePi μ i`. Verify with `#check @MeasureTheory.Measure.infinitePi_map_eval`. |

---

## 5. Complex Analysis

Lemmas about complex-valued functions or complex projections.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Complex.norm_eq_abs` | Relate complex norm to absolute value. | **Hallucinated.** Use `Complex.abs` directly (the coercion handles the bridge). |
| `Complex.abs` (as primary operator) | Absolute value of a complex number. | **Superseded.** While it exists, `positivity` and other tactics expect the generic norm `‖z‖`. Use `norm`. |
| `Complex.normSq_abs` | Norm-square absolute value identity. | **Hallucinated.** Use `Complex.normSq` or `Complex.sq_norm`. |
| `norm_le_norm_iff_normSq_le` | Norm-to-square bridge. | **Hallucinated.** Use `pow_le_pow_iff_left₀` or `sq_le_sq`. |
| `Complex.isCompact_re_im` | Prove compactness of re/im rectangles. | **Hallucinated.** Use `IsCompact.image` of a product of `isCompact_Icc` intervals. |
| `Complex.re_add_mul_I` | Project real part of `↑x + ↑y * I`. | **Hallucinated.** Use `Complex.add_re`, `Complex.ofReal_re`, `Complex.mul_re`, and `Complex.I_re`. |
| `Complex.im_add_mul_I` | Project imaginary part of `↑x + ↑y * I`. | **Hallucinated.** Use `Complex.add_im`, `Complex.ofReal_im`, `Complex.mul_im`, and `Complex.I_im`. |
| `Complex.ofReal_re` (general) | Simplify any real-part of a cast. | **Structural Failure.** It only matches `(↑r).re`. It fails for `(z * w).re`. Use `norm_cast` or `Complex.mul_re` etc. |
| `Max ℂ` | `max` instance for complex numbers. | **Hallucinated.** ℂ is not linearly ordered. Convert the context to `ℝ` using `.norm` or `.re` before using `max`. |
| `AnalyticAt.dslope` | Prove `dslope f a` is analytic at a point. | **Hallucinated as a theorem name.** `HasFPowerSeriesAt` lemmas for `dslope` exist, but no `AnalyticAt.dslope`. Use Riemann's theorem on removable singularities. |
| `AnalyticOn.dslope` | Prove `dslope f a` is analytic on a set. | **Hallucinated.** Use pointwise `AnalyticAt` lemmas inside a binder. |
| `h.neg_pos` | Dot-notation negation-of-inequality on complex types. | **Namespace Error.** Use `neg_pos.mpr h`. |
| `meromorphicOrderAt_mul_lambda` | Apply multiplication order rule directly to pointwise lambda product `fun s ↦ G s * x^s` | **Syntactic Mismatch.** `meromorphicOrderAt_mul` requires a point-free function multiplication `f * g`. Rewrite the lambda expression to point-free representation using `have h_eq : (fun s ↦ f s * g s) = f * g := by ext1; rfl` and `rw [h_eq]` first. |

---

## 6. Real Analysis & Special Functions

Lemmas about real-valued functions, hyperbolic functions, and special constants.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Real.sinh_def` | Definition of `Real.sinh`. | **Name Error.** Use `Real.sinh_eq` instead. |
| `Real.tendsto_sinh_atTop` | Prove `sinh x → ∞` as `x → ∞`. | **Hallucinated.** Use `tendsto_atTop_mono'` with a bound like `(exp x - 1) / 2` and `Real.tendsto_exp_atTop`. |
| `Real.sinh_sq_add_sin_sq_pos` | Prove `sinh² x + sin² y > 0`. | **Hallucinated.** Use `positivity` or `add_pos_of_pos_of_nonneg`. |
| `Real.sinh_sq_le_sinh_sq_add_sin_sq` | Prove `sinh² x ≤ sinh² x + sin² y`. | **Hallucinated.** Use `le_add_of_nonneg_right (sq_nonneg ...)`. |
| `Real.sinh_nonneg` | Prove `0 ≤ sinh x` from `0 ≤ x`. | **Hallucinated as a standalone lemma.** Use `Real.sinh_nonneg_iff.mpr h` (the iff version exists). |
| `Real.sinh_sq_cosh_sq` | `sinh² x · cosh² x = sinh² x + sinh⁴ x`. | **Hallucinated.** Use `rw [Real.cosh_sq]` and then `ring`. |

---

## 7. Order, Algebra & Arithmetic

Lemmas for inequalities, power functions, or real arithmetic.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `abs_le_of_le_of_le` | Double bounding an absolute value. | **Hallucinated.** Use `abs_le.mpr ⟨..., ...⟩`. |
| `pow_le_pow_left` | Power inequality for non-negative bases. | **Partial.** Exists for `ENNReal`, but use `pow_le_pow_left₀` for the general unbundled version. |
| `Real.rpow_nonneg_of_nonneg` | Prove `0 ≤ x ^ y` from `0 ≤ x`. | **Name Error.** Use `Real.rpow_nonneg`. |
| `rpow_mul_rpow` | `x^a · x^b = x^(a+b)` for real powers. | **Name Error.** Use `Real.rpow_add` (requires `0 < x`). |
| `Real.sqrt_pow` | Simplify `Real.sqrt (B ^ (2/3))` into `B ^ (1/3)`. | **Type / Signature Mismatch.** `pow` implies `Nat` powers (`^ n`). For real powers (`rpow`), compose `Real.sqrt_eq_rpow` and `← Real.rpow_mul`. |
| `Real.rpow_two` | Cleanly convert `x ^ 2` to `x ^ (2 : ℝ)`. | **Hallucinated.** Bridging `HPow ℝ ℕ` and `HPow ℝ ℝ` is best solved using `norm_num` inside a `congr 1` block. |
| `Real.rpow_add` (without side conditions) | Apply `x ^ y * x ^ z = x ^ (y + z)` unconditionally. | **Hypothesis Required.** `Real.rpow_add` strictly requires the base to be positive. Omission causes silent rewrite failures. |
| `inv_le_inv_of_le` | Bounding `b⁻¹ ≤ a⁻¹` given `a ≤ b`. | **Name Error.** Use `(inv_le_inv₀ hb ha).mpr hab`. |
| `mul_pos_iff.mp` (as implication) | Extracting factors from `0 < a * b`. | **Iff Conflict.** Returns a disjunction. Use `mul_pos_iff_of_pos_left` instead. |
| `nonpos_of_mul_nonneg_left` (for right target) | Bounding the right factor when the left is negative. | **Orientation Error.** `_left` targets the left factor. Use `nonpos_of_mul_nonneg_right`. |
| `norm_sq_eq_def` | Rewrite a norm square into a standard algebraic form. | **Hallucinated.** In real inner-product spaces use `real_inner_self_eq_norm_sq`; for centered expansions use `norm_sub_sq_real`. |
| `norm_sq_eq_real_inner` | Rewrite `‖x‖²` as `⟪x, x⟫`. | **Hallucinated.** Use `real_inner_self_eq_norm_sq` and, if needed, rewrite in the opposite direction. |
| `norm_sq_eq_inner` | Generic norm-square/inner-product identity. | **Hallucinated.** Use the field-specific theorem already verified in context, typically `real_inner_self_eq_norm_sq`. |
| `Finset.norm_sum_sq` | Closed form for the norm square of a finite sum. | **Hallucinated.** Expand manually with `real_inner_self_eq_norm_sq`, `sum_inner`, and `inner_sum`. |
| `Finset.sum_norm_sq_eq_norm_sum_sq_iff_real_inner_eq_zero` | Characterize vanishing cross terms for a finite family. | **Hallucinated.** Use manual finite-sum expansion and prove the cross terms vanish one by one. |
| `Finset.norm_sum_sq_eq_sum_norm_sq_iff_real_inner_eq_zero` | Rewrite the norm square of a sum as a sum of squares under orthogonality conditions. | **Hallucinated.** For ad hoc proofs, expand with `sum_inner`/`inner_sum`; for genuine orthogonality, search the `OrthogonalFamily` API instead of guessing `Finset` names. |
| `Set.mem_uIcc` giving a conjunction `a ≤ x ∧ x ≤ b` | Projecting left/right bounds directly from a `uIcc` membership. | **Returns Disjunction.** `Set.mem_uIcc` unfolds to `(a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)`. Use `rw [Set.uIcc_of_le (by norm_num : a ≤ b), Set.mem_Icc] at ht` first. |
| `(44 : ℝ) = (44.0 : ℝ)` definitionally (via `rfl`) | Treating integer and scientific decimal literals as definitionally equal. | **Propositional Only.** `(44 : ℝ)` uses `OfNat` and `(44.0 : ℝ)` uses `OfScientific`; they differ in elaboration. Use `have : (44 : ℝ) = (44.0 : ℝ) := by norm_num` then `linarith`. |
| `div_le_div` | Bounding `a/b ≤ c/d`. | **Ambiguous/Wrong Name.** Use `div_le_div₀`. |
| `div_le_one` | `x / y ≤ 1 ↔ x ≤ y` | **Ambiguous.** Use `div_le_one₀`. |
| `not_lt_of_le` / `not_lt_of_ge` | Direct implication to show `¬ a < b` from `b ≤ a` | **Hallucinated.** These do not exist as global implication lemmas. The standard library uses the equivalence `not_lt : ¬a < b ↔ b ≤ a`. Use `not_lt.mpr` to obtain the implication direction. |
| `Fin.append_left_or_right` | Concatenate and case-split Fin intervals | **Hallucinated.** Use `Fin.addCases` for structural induction over split index sets like `Fin (n + m)`. |
| `neg_mul_eq_neg_mul_symm` | Symmetric variant for `-(a * b) = (-a) * b` | **Hallucinated.** Combine `neg_one_mul` and `neg_mul` instead. |
| `linarith` auto-substituting `r` from `let r := ...` | `linarith` automatically expanding `let` definitions. | **Syntactic Term Equivalence Failure.** `linarith` treats `r` and `B^(2/3)/m^(1/3)` as distinct opaque atoms. Rewrite with `dsimp [r]` or `rw [h_r_def]` to synchronize syntactic terms before calling `linarith`. |
| `nlinarith` automatically proving $x^{4/3} \ge 0$ | `nlinarith` inferring non-negativity of real fractional powers. | **Non-Integer Exponent Opacity.** `nlinarith` only handles integer squares ($x^2 \ge 0$). Prove non-negativity using `Real.rpow_nonneg` and pass explicit hypotheses to `nlinarith [h_rpow_nonneg]`. |
| `div_le_div_of_nonneg_right` on `a * (b / c)` | Applying division inequality directly to `a * (b / c) ≤ (d * b) / c`. | **AST Mismatch.** `div_le_div_of_nonneg_right` expects `(X / c) ≤ (Y / c)`. Convert `a * (b / c)` to `(a * b) / c` using `ring` or `rw [mul_div_assoc]` before applying the lemma. |
| `Nat.cast_pos.mpr (by linarith)` from `m ≠ 0` | `linarith` inferring `1 ≤ m` from `m ≠ 0` for `m : ℕ`. | **Domain Limitation.** `linarith` on `ℕ` does not infer `1 ≤ m` from `m ≠ 0`. Use `Nat.pos_of_ne_zero hm` to get `1 ≤ m`, then `Nat.cast_pos.mpr`. |
| `PiLp.norm_bound` | Bounding an individual component of a `EuclideanSpace` vector by its norm. | **Hallucinated.** Use `norm_le_pi_norm`. |
| `inner_nonneg_of_nonneg` | Proving that the inner product of two non-negative vectors is non-negative. | **Hallucinated.** Expand the inner product to a sum using `PiLp.inner_apply`, then use `Finset.sum_nonneg` combined with `mul_nonneg`. |
| `Real.le_of_sq_le_sq` | Deducing `x ≤ y` from `x^2 ≤ y^2` (for non-negative variables). | **Hallucinated.** Use `Real.sqrt_le_sqrt` on both sides and simplify using `Real.sqrt_sq`. |
| `(h : a ≤ b).eq_or_gt` / `LE.le.eq_or_gt` | Case-split a `0 ≤ x` hypothesis into "equals `0`" or "is `> 0`", to derive strict positivity from nonnegativity plus a `≠ 0` side fact. | **Hallucinated.** No `eq_or_gt` projection exists on `LE.le`. Use `LE.le.lt_or_eq : a ≤ b → a < b ∨ a = b` — note the disjunct **order is reversed** from the guessed name (`lt` comes first, not `eq`). For directly combining `0 ≤ x` and `x ≠ 0` into `0 < x`, it is simpler to skip the case split entirely and use `lt_of_le_of_ne (h_nonneg) (Ne.symm h_ne_zero)`. |
| `div_eq_one` applied to `(a b : ℝ)` | Prove `a / b = 1 ↔ a = b` for real numbers, e.g. while deriving an equality case for a Bregman-divergence-style identity. | **Wrong typeclass.** `div_eq_one : a / b = 1 ↔ a = b` (`Mathlib/Algebra/Group/Basic.lean`) is stated for `Group`, and `ℝ` under multiplication is **not** a `Group` (`0` has no inverse; only `ℝˣ` is a group). Do not search for a `GroupWithZero` analogue by guessing suffixes (`div_eq_one_iff_eq`, `div_eq_one₀`, etc.); for `b ≠ 0` prove it directly: `constructor; · intro h; field_simp at h; linarith; · intro h; rw [h]; exact div_self hb.ne'`. |

---

## 8. Filters, Topology & Limits

Lemmas for filter operations, neighborhood bases, or topological limits.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Real.tendsto_sinh_atTop` | `sinh x → ∞` | **Hallucinated.** Use `tendsto_atTop_mono'` with bound `(exp x - 1) / 2`. |
| `Filter.Tendsto.atTop_sub` | Subtracting a constant from an `atTop` limit. | **Hallucinated.** Use `tendsto_atTop_add_const_right` with a negative constant. |
| `Filter.le_atTop_iff` | `l ≤ atTop ↔ ...` | **Hallucinated.** Use `Filter.atTop_basis.ge_iff`. |
| `atTop_le_cofinite` (for PNat) | `atTop ≤ cofinite` on `ℕ+`. | **Conditional.** Requires `NoTopOrder ℕ+` instance. Use manual `le_antisymm` proof if synthesis fails. |
| `Filter.Tendsto.comp_id` | Composing a limit with identity. | **Hallucinated.** Use `Filter.Tendsto.congr'` or `convert`. |
| `nhdsWithin_Ioi_self_neBot` | Right-neighborhood within filter is non-empty. | **Name Error.** Use `nhdsWithin_Ioi_neBot le_rfl` or `nhdsGT_neBot`. |
| `Set.Ici_inter_Iic_self` | `Ici a ∩ Iic a = {a}` | **Name Error.** Use `Set.Ici_inter_Iic` (gives `Icc a a`) then `Set.Icc_self`. |
| `Set.smul_Ici` | Scaling interval `[a, ∞)`. | **Namespace Error.** Use `LinearOrderedField.smul_Ici` from `Mathlib/Algebra/Order/Field/Pointwise.lean`. |
| `Exists.and` | Projection for filter or proposition operator. | **Hallucinated.** Lean confusingly resolves `Exists.and` when a filter membership type unfolds to `Exists`. Use `Filter.Eventually.and` via standard function application. |
| `IsOpen.fun_prop` | Proving openness using `fun_prop`. | **Domain Failure.** `fun_prop` handles function properties only. Use `isOpen_lt` or `isOpen_gt`. |
| `Filter.eventually_of_forall` | Converting universal truth to eventually. | **Namespace Error.** Use `Filter.Eventually.of_forall` (capital `E`). |
| `𝓝` (ambient notation) | Neighborhood filter in `have` statements and goals. | **Scope Error.** `𝓝` is scoped notation requiring `open Topology`. Without it: `unknown identifier '𝓝'`. Use `open Topology` or spell `nhds`; match the target file's existing convention. |

---

## 9. Summability & Series

Lemmas for convergence of infinite series.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Summable.const_div` | Divide a sum by a constant. | **Hallucinated.** Use `Summable.mul_left` or `Summable.mul_right` with the inverse `c⁻¹`. |
| `summable_of_nonneg_of_le` | Comparison test for non-negative series. | **Capitalization Error.** Use `Summable.of_nonneg_of_le` (capital `S`). |
| `summable_nat_to_pnat` | Bridging `Summable` on `ℕ` to `ℕ+`. | **Name Error.** Use `summable_pnat_iff_summable_nat`. |
| `tsum_re` | Distribute real-part over infinite sum. | **Namespace Error.** Use `Complex.re_tsum`. |
| `Tannery` | Tannery's Theorem for sums. | **Name Error.** Use `tendsto_tsum_of_dominated_convergence`. |
| `fourier_inv_fourier_eq` | Fourier inversion formula. | **Name Error.** Use `MeasureTheory.Integrable.fourierInv_fourier_eq`. |
| `summable_complex_then_summable_real_part` | Convergence of real part of complex series. | **Project-Specific.** Exists in `PrimeNumberTheoremAnd/ZetaBounds.lean`, not Mathlib. |

---

## 10. Type System, Coercions & Projections

Errors arising from coercion paths, structural vs propositional equality, or dot-notation on opaque types.

| Hallucinated Name | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `Complex.ofReal_smul` | Bridge scalar and field multiplication across ℝ/ℂ. | **Hallucinated.** Use `Algebra.smul_def` or `smul_eq_mul`. |
| `Complex.ofReal_re` (general case) | Simplify `(f z * ↑r).re` via `ofReal_re`. | **Structural Failure.** It only matches `(↑r).re`. For products, use `Complex.mul_re` and `Complex.re_ofReal_mul`. |
| `linarith` natively understanding `(↑t).re = t` | Assuming `linarith` knows casts. | **Structural Failure.** It treats `(↑t).re` as an opaque atom. You must `simp` with `Complex.ofReal_re` first. |
| `Max ℂ` | `max` instance for ℂ. | **Hallucinated.** ℂ is not linearly ordered. Convert to `ℝ` using `.norm` or `.re`. |
| `Integrable.restrict s` | Direct integrability restriction projection. | **Hallucinated.** Use `.integrableOn s` or `.mono_measure Measure.restrict_le_self`. |
| `I'_nonneg` | Prove non-negativity of `I'`. | **Hallucinated.** Use `unfold I'; split_ifs <;> positivity`. |
| `PNat.coe_injective.injOn s` | Using `injOn` as a function of the set. | **Implicit Conflict.** Set argument `{s}` is implicit; passing it explicitly causes a type mismatch. Use `Set.injOn_subtype_val` instead. |
| `(44 : ℝ) = (44.0 : ℝ)` via `rfl` | Definitional equality of `OfNat` and `OfScientific` literals. | **Propositional Only.** Use `norm_num` to prove the equality. |
| `omega` (for unconstrained `k`) | Automatically prove bounds like `k ≠ 0` for free variables. | **Context Blindness.** `omega` does not search the environment. Ensure all bounds are in the local context. |
| `List.getLast_mem l h` | Access last element membership with explicit list. | **Signature Error.** The list `l` is implicit `{l : List α}`. Call `List.getLast_mem h` only. |
| `Set.disjoint_right` (without `.mp` projection) | Direct function application to prove disjointness. | **Type Mismatch.** In this version of Mathlib, `Set.disjoint_right` is an `Iff` statement. Project it with `.mp` or `.mpr` first, and ensure the right-hand set membership is passed first. |
| `MeromorphicAt.sum` (on lambda sums) | Prove meromorphy of `fun z ↦ ∑ n ∈ s, G n z` directly. | **Type Mismatch.** `MeromorphicAt.sum` is for point-free sums of functions (`∑ n ∈ s, G n`). Use `MeromorphicAt.fun_sum` for lambda sums. |
| `Set.Finite.mem_toFinset` (on coerced finset sets) | Match `p ∈ ↑s.toFinset` directly. | **Pattern Matching Failure.** Coercion `↑` from `Finset` to `Set` is a separate AST node. Strip the coercion using `Finset.mem_coe` first. |
| *Automatic Tuple-to-Structure Coercion* | `Set.image` mapping `⟨w, true⟩` to a Set of structures | **Type Error.** Anonymous tuples don't coerce to custom structures inside a set mapping context (it creates a `Set (X × Y)`). Use explicit constructors like `SignedSample.mk`. |
| `norm_sq_eq_innerProduct` | `‖x‖^2 = x ⊙ x` for generic functions `ι → ℝ` | **False identity for Pi norm.** Standard function types use the sup-norm (Pi norm), not the L2 norm. You must use `EuclideanSpace ι ℝ` for the L2 norm identity to hold. |
| `EuclideanSpace.measurableSpace` | Provide `MeasurableSpace` for `EuclideanSpace` | **Unknown constant.** Mathlib does not provide an explicit `MeasurableSpace` for `EuclideanSpace`. You must declare it manually (e.g. via `borel`). |
| `InnerProductSpace ℝ (ι → ℝ)` | Assume `ι → ℝ` carries a default inner product. | **Instance Missing.** Mathlib strictly avoids assigning an inner product to standard function types. Use `EuclideanSpace ℝ ι` (which is `WithLp 2 (ι → ℝ)`). |
| `Pi.inner_apply_eq` | Trivial `simp` lemma to unfold standard `⟪x, y⟫` directly into a `Finset.sum` for `Pi` types. | **Hallucinated.** Pi types do not have the $L_2$ inner product by default. You must use `WithLp.toLp 2` bridging and `innerProduct_eq_inner_toLp` to access the algebraic Finset representation. |
| `inner_eq_sum` (for `EuclideanSpace`) | Monolithic lemma that expands `inner ℝ v y` directly to `∑ i, v i * y i`. | **Hallucinated.** Mathlib splits this into two steps: `PiLp.inner_apply` for the sum, and `Real.inner_apply` (via `simp`) for the real multiplication. |
| `rfl` for `inner (v i) (y i) = v i * y i` | Assuming `inner` on reals evaluates definitionally to multiplication. | **Definitional Rigidity.** The `InnerProductSpace` instance wraps the multiplication. It is propositionally equal via `Real.inner_apply`, not definitionally equal via `rfl`. |
| `InnerProductSpace ℝ (E × F)` | Assume the product of inner product spaces is an inner product space. | **Instance Missing.** The standard product `E × F` is endowed with the $L_\infty$ maximum norm. Use `WithLp 2 (E × F)` to obtain the $L_2$ product topology. |
| `OfNat (EuclideanSpace ℝ (Fin d)) 1` | `1` as the all-ones vector in `EuclideanSpace` | **Instance Missing.** `EuclideanSpace` only has `Zero` (as a vector space). You must map a constant function `fun _ ↦ 1` via `EuclideanSpace.equiv.symm`. |
| `inferInstanceAs` (for non-defeq wrappers) | Force an instance from `Fin d → ℝ` to `EuclideanSpace` | **Definitional Rigidity.** `inferInstanceAs` strictly requires definitional equality. `EuclideanSpace` is a type synonym wrapped in `WithLp 2`, so it fails. |
| `infer_instance : IsProbabilityMeasure myMeasureDef` (project `def` wrapping `Measure.pi` / `Measure.infinitePi`) | Auto-synthesis of measure instances through a project-level definition. | **Def-Unfolding Failure.** Typeclass resolution does not unfold regular `def`s (only `@[reducible]` ones), so instances on the underlying measure are invisible. Declare a dedicated instance: `instance : IsProbabilityMeasure myMeasureDef := by unfold myMeasureDef; infer_instance`. |
| `IsPositiveSemidefinite.nonneg` | Auto-generated projection for a `Prop` structure. | **Unknown constant.** Lean 4 does not generate projection constants for `Prop` structures by default. Define manual getter lemmas like `IsPositiveSemidefinite.get_nonneg` using `cases` to destruct it. |
| `hM_psd.nonneg` | Dot notation access for a `Prop` structure. | **Invalid field.** Fails because the projection constant doesn't exist, and causes confusing error messages by unwrapping the structure type in the error string. Use `get_nonneg hM_psd`. |

---

## 11. Category Theory & Algebraic Geometry (Schemes)

Hallucinated names, invalid syntax, and false assumptions about tactic/instance behavior when working with schemes, residue fields, and morphism properties.

| Hallucinated Name / Behavior | What it was supposed to do | Confirmed Status / What to use instead |
| :--- | :--- | :--- |
| `CommRingCat.mono_iff_injective` | Prove `Mono f` from injectivity of a ring hom. | **Unknown constant.** Does not exist. Use `ConcreteCategory.mono_of_injective f hinj` (where `hinj : Function.Injective f`; for a field hom, `f.hom.injective`). |
| `(𝟙 X).residueFieldMap x` (dot notation) | Residue-field map of the identity morphism. | **Invalid Field Notation.** `𝟙 X = CategoryStruct.id X`, whose head is not `Scheme.Hom`, so `.residueFieldMap` is not found. Use explicit application `Hom.residueFieldMap (𝟙 X) x`. Same for `≫`, `.op`, `pullback.snd`. |
| `Category.comp_id` collapsing `iso.hom ≫ 𝟙` | Simplify `f ≫ 𝟙 = f` after a `residueFieldMap_id` rewrite. | **Won't fire on defeq object.** When the `𝟙`'s object is `residueField ((𝟙) default)` (defeq-not-syntactic to `residueField default`), the pattern `?f ≫ 𝟙 ?m` can't unify (error appends *"not type-correct under `instances` transparency"*). **Do not produce a `≫ 𝟙` you must cancel** — route via a structural instance + `▸`. |
| `infer_instance` for `IsIso (𝟙 _)` / `IsIso (iso.hom ≫ 𝟙 _)` on a rewritten goal | Auto-synthesize `IsIso` of an identity or an iso-composite. | **Fails on rewritten goals.** The instances exist, but defeq annotations left by prior rewrites break unification. Get `IsIso` from a clean source (e.g. `[IsOpenImmersion f] → IsIso (f.residueFieldMap x)`) and transport with `hc ▸ (inferInstance : IsIso …)`. |
| `AlgebraicGeometry.residueFieldIsoBase` (for a general field `k`) | `X.residueField x ≅ .of k` for a `k`-rational point. | **Wrong hypotheses.** It exists but requires `[IsAlgClosed K]` (and a *closed* point). For a general field, prove `κ(x) ≅ k` manually: a section `e` gives a residue-field retraction that is split-epi + mono ⟹ iso (`isIso_of_mono_of_isSplitEpi`). |
| `rw [h]` to align point-indexed `residueFieldMap` terms (e.g. `h : (e ≫ π).residueFieldMap default = pbar ≫ sbar`) | Rewrite a residue-field composite into a syntactically different but defeq form. | **Syntactic matcher fails on defeq points.** `(e ≫ π) default` vs `π (e default)` are defeq, not syntactic, so `rw` reports "did not find occurrence" or a type-mismatch on the composite. Use `h ▸ (term)` to transport the whole type instead. |
| `WithLp.ofLp_symm_apply` | Cancel `.ofLp` with `(WithLp.equiv ...).symm` using `simp`. | **Hallucinated / Unnecessary.** `ofLp` and `WithLp.equiv.symm` are definitionally equal to standard evaluation. Skip `simp` entirely and use `change` or `dsimp` to bypass the type synonym abstractions. |
| `starRingEnd_apply` / `star_trivial` | Use `ring` to natively cancel complex conjugation `starRingEnd ℝ` on real numbers. | **Tactic Domain Failure.** `ring` treats `starRingEnd` as an opaque atom. It doesn't know conjugation on `ℝ` is the identity. Use `change` to bypass `inner` completely to raw multiplication `x * y`, making `ring` work instantly. |
| `Finset.sum_apply'` (for `EuclideanSpace`/`WithLp`-valued sums) | Evaluate `(∑ i, f i) j` for `f : ι → EuclideanSpace ℝ ι` coordinatewise. | **Wrong Domain.** `Finset.sum_apply'` is the `Finsupp` version; the genuine-`Pi`-type version (`Finset.sum_apply`, `@[simp]`) also does not fire because `EuclideanSpace ℝ ι = WithLp 2 (ι → ℝ)` is a type *synonym*, not syntactically `Π i, M i`, so `rw`/`rfl` cannot bridge it even though it's propositionally true. **Fix**: plain `simp` alone closes `(∑ i, f i) j = ∑ i, f i j` directly (Mathlib's `WithLp`/`PiLp` simp set handles it) — try that before hand-rolling a `map_sum` transport through `WithLp.linearEquiv`. |
| `EuclideanSpace.single_apply` | Evaluate `(EuclideanSpace.single i a) j`. | **Deprecated, not removed.** Still compiles but warns; use `PiLp.single_apply p 𝕜 i a j` instead (note the different, more general signature with an explicit `p` and `𝕜`). |
| `omit [DecidableEq α] in` | Suppress unused variable warnings for variables like `[DecidableEq α]` in Lean 4. | **Syntax Error.** `omit` is a Lean 3 legacy keyword and does not work this way in Lean 4. To natively fix an `unusedSectionVars` warning, bind the variable trivially in the proof with `let _ := ‹DecidableEq α›`. |
| `Finpartition.mapEquiv` | Map a partition across an equivalence. | **Hallucinated.** Mathlib does not natively provide a way to map partitions across equivalences. The entire function (and its properties like `parts_mapEquiv`) must be constructed from scratch in the project. |
| `Equiv.finsetCongr_symm` | Syntactically rewrite `(e.finsetCongr).symm` directly to `e.symm.finsetCongr`. | **Hallucinated / Unnecessary.** While they are definitionally equal, the lack of a syntactic lemma for `rw` causes failures. Use `change` instead to bypass syntactic equality and rely on definitional equality. |
| `congr 1` Auto-Closing Goals | Attempting to use `congr 1` then manually providing a proof term. | **Tactic Behavior Misconception.** `congr` strips outer functions to compare arguments. However, if the arguments are definitionally equal, `congr 1` silently applies `rfl` and closes the goal. Attempting to supply a proof afterward leads to `No goals to be solved` errors. |
| `positiveScaledDualPath` | A hallucinated helper lemma name for the Lasso LCP dual path properties. | **Hallucinated.** Does not exist. Use the algebraic definition `M z(s) - s r + s \lambda \mathbf{1}` directly from the `LCP` conditions. |
| `matVec_add` | Auto-distribution of custom `matVec` operator over addition. | **Missing API.** `matVec` is a custom wrapper. Unfold `matVec` first and use Mathlib's `Matrix.mulVec_add` directly. |
| `deriv_inner_matVec` or generic `HasDerivAt` for `pathDelta` | Assuming Mathlib has off-the-shelf chain rules for `max 0 (inner ...)` that bypass non-differentiability. | **Mathematically False / Hallucinated.** `deriv` of `max` at 0 is 0, breaking the chain rule. Instead of forcing differentiation, break the bound down into structural API lemmas with integrals or encapsulate it inside an explicit algebraic hypothesis `h_deriv_eq` without relying on Mathlib's `deriv`. |
