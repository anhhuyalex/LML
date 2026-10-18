/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeReplicaSum
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities
public import LeanMachineLearning.SpinGlasses.GaussianIBPCountable

/-!
# The Gaussian field of a Ruelle cascade

Let `ℓ` be an array of i.i.d. standard Gaussians indexed by the vertices `v` of the tree and the
children `m` of `v`. The field `g(α) = ∑ᵢ σᵢ ℓ(α|ᵢ, αᵢ)` on the leaves `α : Fin r → ℕ` is a
centred Gaussian process with covariance `E g(α) g(β) = ∑_{i < α ∧ β} σᵢ²`, because the labels of
two leaves at level `i` are the same coordinate of `ℓ` exactly when the leaves agree up to and
including level `i`. With this field the countable Gaussian integration by parts of
`GaussianIBPCountable.lean` applies to the Gibbs measure of the cascade.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

/-- The coordinate of the label array read by the `i`-th step of the leaf `α`. -/
theorem coordinate_eq_iff {r : ℕ} (α β : Fin r → ℕ) (i j : Fin r) :
    ((⟨i, Fin.take i i.isLt.le α⟩ : Σ p : ℕ, Fin p → ℕ), α i) =
      ((⟨j, Fin.take j j.isLt.le β⟩ : Σ p : ℕ, Fin p → ℕ), β j) ↔
      i = j ∧ i.val < (prefixOverlap α β).val := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hij : i = j := Fin.ext (congrArg Sigma.fst h1)
    subst hij
    have htake : Fin.take i i.isLt.le α = Fin.take i i.isLt.le β := eq_of_heq (Sigma.mk.inj h1).2
    refine ⟨rfl, ?_⟩
    refine Nat.lt_of_succ_le (le_prefixOverlap α β (i.val + 1) i.isLt (fun k hk => ?_))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact congrFun htake ⟨k, hk⟩
    · have : k = i := Fin.ext hk
      subst this
      exact h2
  · rintro ⟨rfl, hi⟩
    have htake : Fin.take i i.isLt.le α = Fin.take i i.isLt.le β :=
      (take_eq_take_iff_le_prefixOverlap i.isLt.le α β).2 hi.le
    rw [htake, prefixOverlap_agree α β i hi]

variable {r : ℕ} (σ : ℕ → ℝ)

/-- The coordinates of the label array are independent. -/
theorem iIndepFun_labelArray :
    iIndepFun (fun (c : (Σ p : ℕ, Fin p → ℕ) × ℕ)
        (ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) => ℓ c.1 c.2)
      (Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
  iIndepFun_uncurry_infinitePi'
    (μ := fun _ : Σ p : ℕ, Fin p → ℕ => fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ _ x => x) (by fun_prop)

/-- Every coordinate of the label array is a standard Gaussian. -/
theorem hasLaw_labelArray (c : (Σ p : ℕ, Fin p → ℕ) × ℕ) :
    HasLaw (fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ => ℓ c.1 c.2) (gaussianReal 0 1)
      (Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
  hasLaw_eval_infinitePi_infinitePi (fun _ _ => gaussianReal 0 1) c.1 c.2

/-- The i.i.d. standard Gaussian label array. -/
theorem isGaussianProcess_labelArray :
    IsGaussianProcess (fun (c : (Σ p : ℕ, Fin p → ℕ) × ℕ)
        (ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) => ℓ c.1 c.2)
      (Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
  isGaussianProcess_of_iIndepFun_gaussianReal iIndepFun_labelArray hasLaw_labelArray

/-- The law of the label array: independent standard Gaussians indexed by the children of all
vertices. -/
local notation "μΛ" => Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

variable {σ} {g : (Fin r → ℕ) → ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ}
  (hg : ∀ α ℓ, g α ℓ = ∑ i : Fin r, σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i))

include hg in
/-- The leaf field `g(α) = ∑ᵢ σᵢ ℓ(α|ᵢ, αᵢ)` is a Gaussian process. -/
theorem isGaussianProcess_leafField : IsGaussianProcess g μΛ := by
  classical
  refine (isGaussianProcess_labelArray).of_isGaussianProcess fun α => ?_
  refine ⟨Finset.univ.image fun i : Fin r => (⟨i, Fin.take i i.isLt.le α⟩, α i),
    ∑ i : Fin r, σ i • ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ => ℝ) ⟨(⟨i, Fin.take i i.isLt.le α⟩, α i),
        Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩, fun ℓ => ?_⟩
  simp [hg, Finset.restrict_def]

include hg in
/-- The leaf field is centred. -/
theorem integral_leafField (α : Fin r → ℕ) : ∫ ℓ, g α ℓ ∂μΛ = 0 := by
  have hlaw := hasLaw_labelArray
  have hint : ∀ i : Fin r, Integrable (fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ =>
      σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i)) μΛ := fun i =>
    ((hlaw (⟨i, Fin.take i i.isLt.le α⟩, α i)).hasGaussianLaw.memLp_two.integrable
      one_le_two).const_mul _
  simp_rw [hg]
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, integral_gaussianReal_coordinate hlaw
    (⟨i, Fin.take i i.isLt.le α⟩, α i), mul_zero]

include hg in
/-- **The covariance of the leaf field**: `E g(α) g(β) = ∑_{i < α ∧ β} σᵢ²`. -/
theorem integral_leafField_mul (α β : Fin r → ℕ) :
    ∫ ℓ, g α ℓ * g β ℓ ∂μΛ =
      ∑ i : Fin r, if i.val < (prefixOverlap α β).val then σ i ^ 2 else 0 := by
  classical
  have hlaw := hasLaw_labelArray
  have hint : ∀ c c' : (Σ p : ℕ, Fin p → ℕ) × ℕ, Integrable (fun ℓ :
      (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ => ℓ c.1 c.2 * ℓ c'.1 c'.2) μΛ := fun c c' =>
    (hlaw c).hasGaussianLaw.memLp_two.integrable_mul (hlaw c').hasGaussianLaw.memLp_two
  have hI : ∀ i j : Fin r, Integrable (fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ =>
      σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) *
        (σ j * ℓ ⟨j, Fin.take j j.isLt.le β⟩ (β j))) μΛ := fun i j => by
    have e : (fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ =>
        σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) *
          (σ j * ℓ ⟨j, Fin.take j j.isLt.le β⟩ (β j))) =
        fun ℓ => (σ i * σ j) * (ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) *
          ℓ ⟨j, Fin.take j j.isLt.le β⟩ (β j)) := funext fun ℓ => by ring
    rw [e]
    exact (hint (⟨i, Fin.take i i.isLt.le α⟩, α i) (⟨j, Fin.take j j.isLt.le β⟩, β j)).const_mul _
  have hc : ∀ i j : Fin r, ∫ ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ,
      σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) *
        (σ j * ℓ ⟨j, Fin.take j j.isLt.le β⟩ (β j)) ∂μΛ =
      σ i * σ j * (if i = j ∧ i.val < (prefixOverlap α β).val then 1 else 0) := fun i j => by
    have h := integral_gaussianReal_coordinate_scaled_mul_scaled iIndepFun_labelArray hlaw
      (⟨⟨i, Fin.take i i.isLt.le α⟩, α i⟩ : (Σ p : ℕ, Fin p → ℕ) × ℕ)
      ⟨⟨j, Fin.take j j.isLt.le β⟩, β j⟩ (σ i) (σ j)
    simp only [coordinate_eq_iff] at h
    exact h
  simp_rw [hg, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hI i j]
  simp_rw [hc]
  rw [Finset.sum_eq_single i]
  · by_cases hi : i.val < (prefixOverlap α β).val <;> simp [hi, sq]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

include hg in
/-- The leaf field, doubled, is a Gaussian process: this is the pair `(x, y)` of the Gaussian
integration by parts with `x = y = g`. -/
theorem isGaussianProcess_leafField_sumElim : IsGaussianProcess (Sum.elim g g) μΛ := by
  have h := (isGaussianProcess_leafField hg).comp_right (fun s : (Fin r → ℕ) ⊕ (Fin r → ℕ) =>
    Sum.elim id id s)
  convert h using 1
  ext s ℓ
  cases s <;> rfl

include hg in
/-- **Gaussian integration by parts for the Gibbs measure of the cascade, conditionally on the
weights.** For deterministic positive summable weights `G` on the leaves, the leaf field `g` with
covariance `Q (α ∧ β)` and a bounded observable `Φ` of replicas,
`E ⟨Φ g(σ^{r₀})⟩ = E ⟨Φ (∑_r Q(σ^{r₀} ∧ σ^r) - n Q(σ^{r₀} ∧ σ^{n+1}))⟩`. -/
theorem integral_gibbs_leafField_ibp {R : Type*} [Fintype R] (Q : Fin (r + 1) → ℝ)
    (hQ : ∀ m, Q m = ∑ i : Fin r, if i.val < m.val then σ i ^ 2 else 0)
    (G : (Fin r → ℕ) → ℝ) (hG : ∀ a, 0 < G a) (hGs : Summable G) (r₀ : R)
    (Φ : (R → Fin r → ℕ) → ℝ) {M : ℝ} (hΦ : ∀ τ, |Φ τ| ≤ M) :
    ∫ ℓ, ∑' τ : R → Fin r → ℕ, (∏ k, G (τ k) * Real.exp (g (τ k) ℓ) /
          ∑' b, G b * Real.exp (g b ℓ)) * (Φ τ * g (τ r₀) ℓ) ∂μΛ =
      ∫ ℓ, ∑' τ : Option R → Fin r → ℕ, (∏ o, G (τ o) * Real.exp (g (τ o) ℓ) /
          ∑' b, G b * Real.exp (g b ℓ)) *
        (Φ (fun k => τ (some k)) * (∑ k, Q (prefixOverlap (τ (some r₀)) (τ (some k))) -
          Fintype.card R * Q (prefixOverlap (τ (some r₀)) (τ none)))) ∂μΛ := by
  have hcov : ∀ a b, Q (prefixOverlap a b) = ∫ ℓ, g a ℓ * g b ℓ ∂μΛ := fun a b => by
    rw [integral_leafField_mul hg, hQ]
  have hvar : ∀ a, ∫ ℓ, g a ℓ ^ 2 ∂μΛ ≤ ∑ i : Fin r, σ i ^ 2 := fun a => by
    have e : ∫ ℓ, g a ℓ ^ 2 ∂μΛ = ∫ ℓ, g a ℓ * g a ℓ ∂μΛ := by simp_rw [sq]
    rw [e, integral_leafField_mul hg]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with h
    · exact le_rfl
    · exact sq_nonneg (σ i)
  exact integral_gibbs_replica_average_gaussian_countable (P := μΛ) g g
    (isGaussianProcess_leafField_sumElim hg) (integral_leafField hg) (integral_leafField hg)
    hvar hvar (fun a b => Q (prefixOverlap a b)) (fun a b => hcov a b) G hG hGs r₀ Φ hΦ

end SpinGlasses
