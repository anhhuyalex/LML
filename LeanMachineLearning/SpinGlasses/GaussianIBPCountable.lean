/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import LeanMachineLearning.ForMathlib.Topology.Algebra.InfiniteSum.PiProd
public import LeanMachineLearning.SpinGlasses.GaussianIBP

/-!
# Gaussian integration by parts for a countable configuration space

This file extends the replica covariance formula of `SpinGlasses/GaussianIBP.lean` to a
**countable** configuration space `α` ([Panchenko, 2013, Lemma 1.2, Eqs. (1.30)--(1.35)]).  The
reference weights `G : α → ℝ` are positive and summable, `(x, y)` is a centered Gaussian process
with uniformly bounded variances, and the Gibbs weights are
`G a exp (y a) / ∑ᵦ G b exp (y b)`.  Gibbs averages over `n` replicas are series over `R → α`.

The proof truncates `α` to finite sets `A m` increasing to `α`, applies the finite formula
`SpinGlasses.integral_gibbs_replica_average_gaussian_option` on the finite type `↥(A m)`
(`integral_truncated_gibbs_replica_average_gaussian`, which uses the bridge
`integral_pi_count_tilted_subtype` between replica averages on `↥A` and series on `α`), and passes
to the limit `m → ∞` by dominated convergence:

* for each fixed disorder the truncated weights are dominated by `g a / g a₁` and converge
  (`truncated_gibbs_weights`), so Tannery's theorem for series over `R → α`
  (`tendsto_tsum_prod_pi`) gives the pointwise limit;
* the disorder-dependent bound `M ∑_b (g b / g a₁) |x b|` is integrable by the Gaussian estimate
  `ProbabilityTheory.ae_summable_and_integrable_tsum_mul_exp`, which uses the exponential moments of
  the Gaussian increments `y b - y a₁` and Cauchy--Schwarz.

## Main declaration

* `SpinGlasses.integral_gibbs_replica_average_gaussian_countable`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped Matrix Topology

namespace SpinGlasses

variable {α J R : Type*}

/-- **Finite truncation of a series over replicas.**  The `J`-fold product of the Gibbs measure
of a finite `A ⊆ α` (a measure on `J → ↥A`) integrates `Ψ ∘ val` to the series
`∑' σ, (∏ j, 1_A(σ j) g(σ j) / ∑_{b ∈ A} g b) Ψ σ` over `J → α`. -/
theorem integral_pi_count_tilted_subtype [Fintype J] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Finset α) (g : α → ℝ) (f : A → ℝ)
    (hf : ∀ b : A, Real.exp (f b) = g b) (Ψ : (J → α) → ℝ) :
    ∫ σ : J → A, Ψ (fun j => (σ j).1) ∂(Measure.pi fun _ : J => Measure.count.tilted f) =
      ∑' σ : J → α, (∏ j, if σ j ∈ A then g (σ j) / ∑ b ∈ A, g b else 0) * Ψ σ := by
  classical
  rw [integral_pi_count_tilted]
  have hZ : ∑ b : A, Real.exp (f b) = ∑ b ∈ A, g b := by
    simp_rw [hf]; exact Finset.sum_coe_sort A g
  simp_rw [hZ, hf]
  rw [tsum_eq_sum (s := Fintype.piFinset fun _ : J => A)]
  · refine Finset.sum_bij (fun σ _ => fun j => (σ j).1) (fun σ _ => ?_) (fun σ _ τ _ h => ?_)
      (fun τ hτ => ?_) (fun σ _ => ?_)
    · exact Fintype.mem_piFinset.2 fun j => (σ j).2
    · exact funext fun j => Subtype.ext (congrFun h j)
    · refine ⟨fun j => ⟨τ j, Fintype.mem_piFinset.1 hτ j⟩, Finset.mem_univ _, rfl⟩
    · congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [(σ j).2]
  · intro σ hσ
    rw [Fintype.mem_piFinset] at hσ
    push Not at hσ
    obtain ⟨j, hj⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]

/-- **Truncated Gibbs weights:** for positive summable `g` and finite sets `A m` increasing to
`α` and containing `a₀`, the truncated normalized weights `g a / ∑_{b ∈ A m} g b` (on `A m`) are
dominated by `g a / g a₀` and converge to `g a / ∑ᵦ g b`. -/
theorem truncated_gibbs_weights [DecidableEq α] {g : α → ℝ} (hg : ∀ a, 0 < g a)
    (hs : Summable g) {A : ℕ → Finset α} (hA : Monotone A) (hAu : ∀ a, ∃ m, a ∈ A m) {a₀ : α}
    (h0 : ∀ m, a₀ ∈ A m) :
    (∀ m a, 0 ≤ (if a ∈ A m then g a / ∑ b ∈ A m, g b else 0) ∧
      (if a ∈ A m then g a / ∑ b ∈ A m, g b else 0) ≤ g a / g a₀) ∧
    ∀ a, Tendsto (fun m => if a ∈ A m then g a / ∑ b ∈ A m, g b else 0) atTop
      (𝓝 (g a / ∑' b, g b)) := by
  have hSpos : ∀ m, 0 < ∑ b ∈ A m, g b := fun m =>
    Finset.sum_pos (fun b _ => hg b) ⟨a₀, h0 m⟩
  refine ⟨fun m a => ?_, fun a => ?_⟩
  · split_ifs with ha
    · refine ⟨div_nonneg (hg a).le (hSpos m).le, div_le_div_of_nonneg_left (hg a).le (hg a₀) ?_⟩
      exact Finset.single_le_sum (f := g) (fun b _ => (hg b).le) (h0 m)
    · exact ⟨le_rfl, div_nonneg (hg a).le (hg a₀).le⟩
  · have hT : Tendsto (fun m => ∑ b ∈ A m, g b) atTop (𝓝 (∑' b, g b)) :=
      hs.hasSum.comp (tendsto_atTop_finset_of_monotone hA hAu)
    have hSne : ∑' b, g b ≠ 0 := (hs.tsum_pos (fun b => (hg b).le) a₀ (hg a₀)).ne'
    obtain ⟨m₀, hm₀⟩ := hAu a
    refine ((tendsto_const_nhds.div hT hSne)).congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    simp [hA hm hm₀]

/-- **Convergence of truncated replica averages.** -/
theorem tendsto_truncated_replica_average [Fintype J] [DecidableEq α] {g : α → ℝ}
    (hg : ∀ a, 0 < g a) (hs : Summable g) {A : ℕ → Finset α} (hA : Monotone A)
    (hAu : ∀ a, ∃ m, a ∈ A m) {a₀ : α} (h0 : ∀ m, a₀ ∈ A m) {Ψ : (J → α) → ℝ}
    (hΨ : Summable fun σ : J → α => (∏ j, g (σ j) / g a₀) * |Ψ σ|) :
    Tendsto (fun m => ∑' σ : J → α,
        (∏ j, if σ j ∈ A m then g (σ j) / ∑ b ∈ A m, g b else 0) * Ψ σ) atTop
      (𝓝 (∑' σ : J → α, (∏ j, g (σ j) / ∑' b, g b) * Ψ σ)) := by
  obtain ⟨hb, ht⟩ := truncated_gibbs_weights hg hs hA hAu h0
  exact tendsto_tsum_prod_pi (w := fun m a => if a ∈ A m then g a / ∑ b ∈ A m, g b else 0)
    (w₀ := fun a => g a / ∑' b, g b) (B := fun a => g a / g a₀) (Eventually.of_forall hb) ht hΨ

/-- **Domination bound for a truncated replica average.**  For `g > 0`, a finite `A ∋ a₁` and a
bounded observable `Φ`,
`|∑_σ (∏ⱼ 1_A g/∑_A g)(σ j) Φ(σ) χ(σ j₀)| ≤ M ∑_b (g b / g a₁) |χ b|`. -/
theorem abs_tsum_truncated_mul_eval_le [Fintype J] [DecidableEq α] {g : α → ℝ}
    (hg : ∀ a, 0 < g a) {A : Finset α} {a₁ : α} (ha₁ : a₁ ∈ A) (χ : α → ℝ) (j₀ : J)
    {Φ : (J → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M)
    (hs : Summable fun b => g b / g a₁ * |χ b|) :
    |∑' σ : J → α, (∏ j, if σ j ∈ A then g (σ j) / ∑ b ∈ A, g b else 0) *
        (Φ σ * χ (σ j₀))| ≤ M * ∑' b, g b / g a₁ * |χ b| := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty A := ⟨⟨a₁, ha₁⟩⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ (fun _ => a₁))
  have hf : ∀ b : A, Real.exp (Real.log (g b.1)) = g b.1 := fun b => Real.exp_log (hg _)
  rw [← integral_pi_count_tilted_subtype A g (fun b : A => Real.log (g b.1)) hf
    (fun σ => Φ σ * χ (σ j₀))]
  refine (abs_integral_pi_count_tilted_mul_eval_le (R := J) (fun b : A => Real.log (g b.1))
    (fun b : A => χ b.1) j₀ (Φ := fun σ => Φ fun j => (σ j).1) fun σ => hΦ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hM
  rw [integral_count_tilted]
  simp_rw [hf]
  have hS : ∑ b : A, g b.1 = ∑ b ∈ A, g b := Finset.sum_coe_sort A g
  have hSge : g a₁ ≤ ∑ b ∈ A, g b :=
    Finset.single_le_sum (f := g) (fun b _ => (hg b).le) ha₁
  calc ∑ a : A, g a.1 / (∑ b : A, g b.1) * |χ a.1|
      ≤ ∑ a : A, g a.1 / g a₁ * |χ a.1| := by
        rw [hS]
        refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact div_le_div_of_nonneg_left (hg _).le (hg a₁) hSge
    _ = ∑ a ∈ A, g a / g a₁ * |χ a| := Finset.sum_coe_sort A fun a => g a / g a₁ * |χ a|
    _ ≤ ∑' a, g a / g a₁ * |χ a| :=
        hs.sum_le_tsum _ fun a _ => mul_nonneg (div_nonneg (hg a).le (hg a₁).le) (abs_nonneg _)

/-- **Bound for a truncated replica average of a bounded observable:** `|⟨Ψ⟩| ≤ K` if `|Ψ| ≤ K`. -/
theorem abs_tsum_truncated_le [Fintype J] [DecidableEq α] {g : α → ℝ}
    (hg : ∀ a, 0 < g a) {A : Finset α} {a₁ : α} (ha₁ : a₁ ∈ A) {Ψ : (J → α) → ℝ} {K : ℝ}
    (hΨ : ∀ σ, |Ψ σ| ≤ K) :
    |∑' σ : J → α, (∏ j, if σ j ∈ A then g (σ j) / ∑ b ∈ A, g b else 0) * Ψ σ| ≤ K := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty A := ⟨⟨a₁, ha₁⟩⟩
  have hf : ∀ b : A, Real.exp (Real.log (g b.1)) = g b.1 := fun b => Real.exp_log (hg _)
  rw [← integral_pi_count_tilted_subtype A g (fun b : A => Real.log (g b.1)) hf Ψ]
  exact abs_integral_pi_count_tilted_le (R := J) _ (Ψ := fun σ : J → A => Ψ fun j => (σ j).1)
    fun σ => hΨ _

section Truncation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Measurability of a truncated replica average in the random weights. -/
theorem aemeasurable_tsum_prod_pi_of_forall_notMem [Fintype J] {A : Finset α} {w : Ω → α → ℝ}
    (hw : ∀ a, AEMeasurable (fun ω => w ω a) P) (hw0 : ∀ ω a, a ∉ A → w ω a = 0)
    {Ψ : Ω → (J → α) → ℝ} (hΨ : ∀ σ, AEMeasurable (fun ω => Ψ ω σ) P) :
    AEMeasurable (fun ω => ∑' σ : J → α, (∏ j, w ω (σ j)) * Ψ ω σ) P := by
  classical
  have h : ∀ ω, ∑' σ : J → α, (∏ j, w ω (σ j)) * Ψ ω σ =
      ∑ σ ∈ Fintype.piFinset fun _ : J => A, (∏ j, w ω (σ j)) * Ψ ω σ := fun ω => by
    refine tsum_eq_sum fun σ hσ => ?_
    rw [Fintype.mem_piFinset] at hσ
    push Not at hσ
    obtain ⟨j, hj⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (hw0 ω _ hj), zero_mul]
  simp_rw [h]
  exact Finset.aemeasurable_fun_sum _ fun σ _ =>
    (Finset.aemeasurable_fun_prod _ fun j _ => hw (σ j)).mul (hΨ σ)

/-- **The replica formula for a finite truncation of a countable configuration space**, written
as series over `R → α` and `Option R → α` with the truncated Gibbs weights. -/
theorem integral_truncated_gibbs_replica_average_gaussian [DecidableEq α] [Fintype R]
    (x y : α → Ω → ℝ)
    (hxy : IsGaussianProcess (Sum.elim x y) P)
    (hx : ∀ a, ∫ ω, x a ω ∂P = 0) (hy : ∀ a, ∫ ω, y a ω ∂P = 0)
    (C : α → α → ℝ) (hC : ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P) (G : α → ℝ)
    (hG : ∀ a, 0 < G a) (A : Finset α) (hA : A.Nonempty) (r₀ : R) (Φ : (R → α) → ℝ) :
    ∫ ω, ∑' σ : R → α, (∏ r, if σ r ∈ A then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω) ∂P =
      ∫ ω, ∑' τ : Option R → α, (∏ o, if τ o ∈ A then G (τ o) * Real.exp (y (τ o) ω) /
          ∑ b ∈ A, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))) ∂P := by
  let _ : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have : Nonempty A := hA.to_subtype
  have hxyA : HasGaussianLaw (fun ω (s : A ⊕ A) =>
      Sum.elim (fun b : A => x b.1) (fun b : A => y b.1) s ω) P := by
    have h := (hxy.comp_right (Sum.map (Subtype.val : A → α) (Subtype.val : A → α))
      ).hasGaussianLaw_pi
    have e : (Sum.elim x y ∘ Sum.map (Subtype.val : A → α) (Subtype.val : A → α)) =
        Sum.elim (fun b : A => x b.1) (fun b : A => y b.1) := by
      funext s; cases s <;> rfl
    rwa [e] at h
  have h := integral_gibbs_replica_average_gaussian_option (R := R) (fun (b : A) ω => x b.1 ω)
    (fun (b : A) ω => y b.1 ω) hxyA (fun b => hx b.1) (fun b => hy b.1) (fun b b' => C b.1 b'.1)
    (fun b b' => hC _ _) (fun b => Real.log (G b.1)) r₀ (fun σ => Φ fun r => (σ r).1)
  have hf : ∀ (ω : Ω) (b : A), Real.exp (y b.1 ω + Real.log (G b.1)) = G b.1 * Real.exp (y b.1 ω) :=
    fun ω b => by rw [Real.exp_add, Real.exp_log (hG _), mul_comm]
  have e1 : ∀ ω, ∫ σ : R → A, Φ (fun r => (σ r).1) * x (σ r₀).1 ω ∂(Measure.pi fun _ : R =>
        Measure.count.tilted fun b : A => y b.1 ω + Real.log (G b.1)) =
      ∑' σ : R → α, (∏ r, if σ r ∈ A then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω) := fun ω =>
    integral_pi_count_tilted_subtype A (fun a => G a * Real.exp (y a ω))
      (fun b : A => y b.1 ω + Real.log (G b.1)) (hf ω) (fun σ => Φ σ * x (σ r₀) ω)
  have e2 : ∀ ω, ∫ τ : Option R → A, Φ (fun r => (τ (some r)).1) *
        (∑ r, C (τ (some r₀)).1 (τ (some r)).1 - Fintype.card R * C (τ (some r₀)).1 (τ none).1)
        ∂(Measure.pi fun _ : Option R =>
          Measure.count.tilted fun b : A => y b.1 ω + Real.log (G b.1)) =
      ∑' τ : Option R → α, (∏ o, if τ o ∈ A then G (τ o) * Real.exp (y (τ o) ω) /
          ∑ b ∈ A, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))) := fun ω =>
    integral_pi_count_tilted_subtype A (fun a => G a * Real.exp (y a ω))
      (fun b : A => y b.1 ω + Real.log (G b.1)) (hf ω) (fun τ => Φ (fun r => τ (some r)) *
        (∑ r, C (τ (some r₀)) (τ (some r)) - Fintype.card R * C (τ (some r₀)) (τ none)))
  simp_rw [← e1, ← e2]
  exact h

/-- **Gaussian integration by parts for a countable configuration space
(Panchenko Lemma 1.2, Eqs. (1.30)–(1.35)).**  Let `α` be countable, `G > 0` summable, and
`(x, y)` a centered Gaussian process with `𝔼 x(a)², 𝔼 y(a)² ≤ v`.  The Gibbs weights
`G a exp (y a) / ∑ᵦ G b exp (y b)` are an a.s. well defined probability on `α`, and for a bounded
observable `Φ` of `n = |R|` replicas,
`𝔼⟨Φ x(σ^{r₀})⟩ = 𝔼⟨Φ (∑ᵣ C(σ^{r₀}, σʳ) - n C(σ^{r₀}, σ^{n+1}))⟩`
(`⟨·⟩` are series over `R → α` and `Option R → α`).  Proof: Eq. (1.29) for finite truncations
(`integral_gibbs_replica_average_gaussian_option`) and dominated convergence. -/
theorem integral_gibbs_replica_average_gaussian_countable [Countable α] [Nonempty α]
    [Fintype R] (x y : α → Ω → ℝ) (hxy : IsGaussianProcess (Sum.elim x y) P)
    (hx : ∀ a, ∫ ω, x a ω ∂P = 0) (hy : ∀ a, ∫ ω, y a ω ∂P = 0) {v : ℝ}
    (hxv : ∀ a, ∫ ω, x a ω ^ 2 ∂P ≤ v) (hyv : ∀ a, ∫ ω, y a ω ^ 2 ∂P ≤ v)
    (C : α → α → ℝ) (hC : ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P) (G : α → ℝ)
    (hG : ∀ a, 0 < G a) (hGs : Summable G) (r₀ : R) (Φ : (R → α) → ℝ) {M : ℝ}
    (hΦ : ∀ σ, |Φ σ| ≤ M) :
    ∫ ω, ∑' σ : R → α, (∏ r, G (σ r) * Real.exp (y (σ r) ω) /
          ∑' b, G b * Real.exp (y b ω)) * (Φ σ * x (σ r₀) ω) ∂P =
      ∫ ω, ∑' τ : Option R → α, (∏ o, G (τ o) * Real.exp (y (τ o) ω) /
          ∑' b, G b * Real.exp (y b ω)) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))) ∂P := by
  classical
  have hP := hxy.isProbabilityMeasure
  obtain ⟨a₁⟩ := ‹Nonempty α›
  obtain ⟨e, he⟩ := exists_surjective_nat α
  let A : ℕ → Finset α := fun m => insert a₁ ((Finset.range (m + 1)).image e)
  have hA : Monotone A := fun m n hmn =>
    Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.range_mono (by omega)))
  have hAu : ∀ a, ∃ m, a ∈ A m := fun a => by
    obtain ⟨n, rfl⟩ := he a
    exact ⟨n, Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)⟩
  have hA0 : ∀ m, a₁ ∈ A m := fun m => Finset.mem_insert_self _ _
  have key : ∀ m, ∫ ω, ∑' σ : R → α, (∏ r, if σ r ∈ A m then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω) ∂P =
      ∫ ω, ∑' τ : Option R → α, (∏ o, if τ o ∈ A m then G (τ o) * Real.exp (y (τ o) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))) ∂P := fun m =>
    integral_truncated_gibbs_replica_average_gaussian x y hxy hx hy C hC G hG (A m)
      ⟨a₁, hA0 m⟩ r₀ Φ
  -- Gaussian facts
  have hxm : ∀ b, MemLp (x b) 2 P := fun b =>
    (hxy.hasGaussianLaw_eval (t := Sum.inl b)).memLp_two
  have hym : ∀ b, MemLp (y b) 2 P := fun b =>
    (hxy.hasGaussianLaw_eval (t := Sum.inr b)).memLp_two
  have hxa : ∀ b, AEMeasurable (x b) P := fun b => hxy.aemeasurable (Sum.inl b)
  have hya : ∀ b, AEMeasurable (y b) P := fun b => hxy.aemeasurable (Sum.inr b)
  have hZg : ∀ b, HasGaussianLaw (fun ω => y b ω - y a₁ ω) P := fun b =>
    hxy.hasGaussianLaw_fun_sub (s := Sum.inr b) (t := Sum.inr a₁)
  have hZ0 : ∀ b, ∫ ω, (y b ω - y a₁ ω) ∂P = 0 := fun b => by
    rw [integral_sub ((hym b).integrable one_le_two) ((hym a₁).integrable one_le_two), hy, hy,
      sub_zero]
  have hZv : ∀ b, ∫ ω, (y b ω - y a₁ ω) ^ 2 ∂P ≤ 4 * v := fun b => by
    have h1 := (hym b).integrable_sq
    have h2 := (hym a₁).integrable_sq
    calc ∫ ω, (y b ω - y a₁ ω) ^ 2 ∂P ≤ ∫ ω, (2 * y b ω ^ 2 + 2 * y a₁ ω ^ 2) ∂P :=
          integral_mono (((hym b).sub (hym a₁)).integrable_sq)
            ((h1.const_mul 2).add (h2.const_mul 2))
            fun ω => by nlinarith [sq_nonneg (y b ω + y a₁ ω)]
      _ = 2 * ∫ ω, y b ω ^ 2 ∂P + 2 * ∫ ω, y a₁ ω ^ 2 ∂P := by
          rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * v := by linarith [hyv b, hyv a₁]
  have hS1 := ae_summable_and_integrable_tsum_mul_exp (P := P) (X := fun _ _ => (1 : ℝ))
    (Z := fun b ω => y b ω - y a₁ ω) (G := G) (fun b => (hG b).le) hGs hZg hZ0
    (fun _ => memLp_const 1) (a := 1) (by simp) hZv
  have hS2 := ae_summable_and_integrable_tsum_mul_exp (P := P) (X := x)
    (Z := fun b ω => y b ω - y a₁ ω) (G := G) (fun b => (hG b).le) hGs hZg hZ0 hxm hxv hZv
  -- a.e. summability of the Gibbs weights
  have hgs : ∀ᵐ ω ∂P, Summable fun b => G b * Real.exp (y b ω) := by
    filter_upwards [hS1.1] with ω hω
    refine (hω.mul_left (Real.exp (y a₁ ω))).congr fun b => ?_
    rw [abs_one, one_mul, Real.exp_sub]
    field_simp
  have hgx : ∀ᵐ ω ∂P, Summable fun b =>
      G b * Real.exp (y b ω) / (G a₁ * Real.exp (y a₁ ω)) * |x b ω| := by
    filter_upwards [hS2.1] with ω hω
    refine (hω.mul_left (G a₁)⁻¹).congr fun b => ?_
    rw [Real.exp_sub]
    field_simp
  -- the covariance is bounded
  have hCb : ∀ a b, |C a b| ≤ v := fun a b => by
    rw [hC]
    have hint : Integrable (fun ω => x a ω * y b ω) P := (hxm a).integrable_mul (hym b)
    calc |∫ ω, x a ω * y b ω ∂P| ≤ ∫ ω, |x a ω * y b ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (x a ω ^ 2 / 2 + y b ω ^ 2 / 2) ∂P :=
          integral_mono hint.abs (((hxm a).integrable_sq.div_const 2).add
            ((hym b).integrable_sq.div_const 2)) fun ω => by
            rw [abs_mul]; nlinarith [sq_nonneg (|x a ω| - |y b ω|), sq_abs (x a ω), sq_abs (y b ω)]
      _ = (∫ ω, x a ω ^ 2 ∂P) / 2 + (∫ ω, y b ω ^ 2 ∂P) / 2 := by
          rw [integral_add ((hxm a).integrable_sq.div_const 2) ((hym b).integrable_sq.div_const 2),
            integral_div, integral_div]
      _ ≤ v := by linarith [hxv a, hyv b]
  -- measurability of the truncated weights
  have hwm : ∀ (m : ℕ) (a : α), AEMeasurable (fun ω => if a ∈ A m then G a * Real.exp (y a ω) /
      ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) P := fun m a => by
    by_cases ha : a ∈ A m
    · simp only [ha, ite_true]
      exact (aemeasurable_const.mul (Real.measurable_exp.comp_aemeasurable (hya a))).div
        (Finset.aemeasurable_fun_sum _ fun b _ => aemeasurable_const.mul
          (Real.measurable_exp.comp_aemeasurable (hya b)))
    · simp only [ha, ite_false]; exact aemeasurable_const
  have hLmeas : ∀ m, AEStronglyMeasurable (fun ω => ∑' σ : R → α,
      (∏ r, if σ r ∈ A m then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω)) P := fun m =>
    (aemeasurable_tsum_prod_pi_of_forall_notMem (A := A m) (hwm m)
      (fun ω a ha => by simp [ha]) (Ψ := fun ω σ => Φ σ * x (σ r₀) ω)
      (fun σ => aemeasurable_const.mul (hxa _))).aestronglyMeasurable
  have hRmeas : ∀ m, AEStronglyMeasurable (fun ω => ∑' τ : Option R → α,
      (∏ o, if τ o ∈ A m then G (τ o) * Real.exp (y (τ o) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none)))) P := fun m =>
    (aemeasurable_tsum_prod_pi_of_forall_notMem (A := A m) (hwm m)
      (fun ω a ha => by simp [ha])
      (Ψ := fun ω τ => Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
        Fintype.card R * C (τ (some r₀)) (τ none))) (fun τ => aemeasurable_const)
      ).aestronglyMeasurable
  -- bounds
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hΦ fun _ => a₁)
  set K : ℝ := M * (Fintype.card R * v + Fintype.card R * v) with hK
  have hΨb : ∀ τ : Option R → α, |Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
      Fintype.card R * C (τ (some r₀)) (τ none))| ≤ K := fun τ => by
    rw [abs_mul]
    refine mul_le_mul (hΦ _) ?_ (abs_nonneg _) hM0
    calc |∑ r, C (τ (some r₀)) (τ (some r)) - Fintype.card R * C (τ (some r₀)) (τ none)|
        ≤ |∑ r, C (τ (some r₀)) (τ (some r))| + |Fintype.card R * C (τ (some r₀)) (τ none)| :=
          abs_sub _ _
      _ ≤ Fintype.card R * v + Fintype.card R * v := by
          refine add_le_add ?_ ?_
          · calc |∑ r, C (τ (some r₀)) (τ (some r))| ≤ ∑ r, |C (τ (some r₀)) (τ (some r))| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _r : R, v := Finset.sum_le_sum fun r _ => hCb _ _
              _ = Fintype.card R * v := by simp
          · rw [abs_mul, Nat.abs_cast]
            exact mul_le_mul_of_nonneg_left (hCb _ _) (Nat.cast_nonneg _)
  have hgpos : ∀ ω b, 0 < G b * Real.exp (y b ω) := fun ω b => mul_pos (hG b) (Real.exp_pos _)
  -- left-hand side
  have hbL : Integrable (fun ω => M * ((G a₁)⁻¹ *
      ∑' b, G b * (|x b ω| * Real.exp (y b ω - y a₁ ω)))) P := (hS2.2.const_mul _).const_mul M
  have hLb : ∀ m, ∀ᵐ ω ∂P, ‖∑' σ : R → α, (∏ r, if σ r ∈ A m then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω)‖ ≤
      M * ((G a₁)⁻¹ * ∑' b, G b * (|x b ω| * Real.exp (y b ω - y a₁ ω))) := fun m => by
    filter_upwards [hgx] with ω hω
    rw [Real.norm_eq_abs]
    refine (abs_tsum_truncated_mul_eval_le (g := fun b => G b * Real.exp (y b ω)) (hgpos ω)
      (hA0 m) (fun b => x b ω) r₀ hΦ hω).trans (le_of_eq ?_)
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun b => ?_
    rw [Real.exp_sub]
    field_simp
  have hLlim : ∀ᵐ ω ∂P, Tendsto (fun m => ∑' σ : R → α,
      (∏ r, if σ r ∈ A m then G (σ r) * Real.exp (y (σ r) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) * (Φ σ * x (σ r₀) ω)) atTop
      (𝓝 (∑' σ : R → α, (∏ r, G (σ r) * Real.exp (y (σ r) ω) /
          ∑' b, G b * Real.exp (y b ω)) * (Φ σ * x (σ r₀) ω))) := by
    filter_upwards [hgs, hgx] with ω hs hx'
    exact tendsto_truncated_replica_average (g := fun b => G b * Real.exp (y b ω)) (hgpos ω) hs
      hA hAu (hA0) (Ψ := fun σ => Φ σ * x (σ r₀) ω)
      (summable_prod_pi_mul_abs_eval (fun a => (hgpos ω a).le.trans' le_rfl |> fun _ =>
        div_nonneg (hgpos ω a).le (hgpos ω a₁).le) (hs.div_const _) hx' r₀ hΦ)
  -- right-hand side
  have hRb : ∀ m, ∀ᵐ ω ∂P, ‖∑' τ : Option R → α, (∏ o, if τ o ∈ A m then G (τ o) *
          Real.exp (y (τ o) ω) / ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none)))‖ ≤ K := fun m => ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_tsum_truncated_le (g := fun b => G b * Real.exp (y b ω)) (hgpos ω) (hA0 m) hΨb
  have hRlim : ∀ᵐ ω ∂P, Tendsto (fun m => ∑' τ : Option R → α,
      (∏ o, if τ o ∈ A m then G (τ o) * Real.exp (y (τ o) ω) /
          ∑ b ∈ A m, G b * Real.exp (y b ω) else 0) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none)))) atTop
      (𝓝 (∑' τ : Option R → α, (∏ o, G (τ o) * Real.exp (y (τ o) ω) /
          ∑' b, G b * Real.exp (y b ω)) *
        (Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))))) := by
    filter_upwards [hgs] with ω hs
    refine tendsto_truncated_replica_average (J := Option R) (g := fun b => G b * Real.exp (y b ω))
      (hgpos ω) hs hA hAu hA0 (Ψ := fun τ => Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀))
        (τ (some r)) - Fintype.card R * C (τ (some r₀)) (τ none))) ?_
    have hB := summable_prod_pi (J := Option R) (f := fun _ a => G a * Real.exp (y a ω) /
      (G a₁ * Real.exp (y a₁ ω))) (fun _ a => div_nonneg (hgpos ω a).le (hgpos ω a₁).le)
      fun _ => hs.div_const _
    refine (hB.mul_left K).of_nonneg_of_le (fun τ => mul_nonneg
      (Finset.prod_nonneg fun o _ => div_nonneg (hgpos ω _).le (hgpos ω a₁).le) (abs_nonneg _))
      fun τ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hΨb τ)
      (Finset.prod_nonneg fun o _ => div_nonneg (hgpos ω _).le (hgpos ω a₁).le)
  have h1 := tendsto_integral_of_dominated_convergence _ hLmeas hbL hLb hLlim
  have h2 := tendsto_integral_of_dominated_convergence (fun _ => K) hRmeas (integrable_const K)
    hRb hRlim
  exact tendsto_nhds_unique (h1.congr key) h2

end Truncation

end SpinGlasses
