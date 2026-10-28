/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianTiltedFreeEnergy
public import LeanMachineLearning.SpinGlasses.SKGaussianFluctuation
public import LeanMachineLearning.SpinGlasses.SKSmartPathProfile
public import LeanMachineLearning.SpinGlasses.SKSmartPath
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound
public import LeanMachineLearning.SpinGlasses.SKFixedPointRS
public import LeanMachineLearning.SpinGlasses.SKPathOverlapMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Moments of the free-energy fluctuation of the SK model (Talagrand, Lemma 1.4.12)

For the SK model with deterministic field `h`, put `A_N = N⁻¹ log Z_N` and
`p_N = 𝔼 A_N`.  The free energy `log Z_N` is a Lipschitz function of the Gaussian disorder, hence
sub-Gaussian (`hasSubgaussianMGF_log_sum_exp`), and this gives Eq. (1.113) of the book for `c = 0`:
`𝔼 |A_N - p_N|^k ≤ K_k / N^{k/2}` with `K_k = 2 k! exp (β² / 2)`, for every `β` and `h`.
More generally, this holds along the entire smart path `H_s = cos s · SK + sin s · cavity + h ∑ σᵢ`
with `v / N ≤ (3/2) β²`.

## Main declarations

* `SpinGlasses.integral_pow_abs_sub_integral_log_sum_exp_le`: general moment bound for a Gaussian
  log-sum-exp free energy.
* `SpinGlasses.integral_pow_abs_free_energy_sub_le`: `√N^k 𝔼 |A_N - p_N|^k ≤ 2 k! exp (β² / 2)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.4.12.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix NNReal

namespace SpinGlasses

/-- **Moments of a Gaussian log-sum-exp free energy.**  For any centered Gaussian field `g` on a
finite configuration space `α` with variance bounded by `v`, the free energy
`F = log ∑ₐ exp (g a + bias a)` has concentrated moments:
`(√N)^k 𝔼 |N⁻¹ F - N⁻¹ 𝔼 F|^k ≤ 2 k! exp (v / N)`. -/
theorem integral_pow_abs_sub_integral_log_sum_exp_le {α Ω : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace Ω] {P : Measure Ω}
    {g : α → Ω → ℝ} (hg : HasGaussianLaw (fun ω a => g a ω) P)
    (hm : ∀ a, Measurable (g a)) (h0 : ∀ a, ∫ ω, g a ω ∂P = 0)
    {v : ℝ} (hv : ∀ a, ∫ ω, g a ω ^ 2 ∂P ≤ v) (bias : α → ℝ)
    (k : ℕ) {N : ℕ} (hN : 0 < N) :
    let F : Ω → ℝ := fun ω => Real.log (∑ a, Real.exp (g a ω + bias a))
    Integrable (fun ω => |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| ^ k) P ∧
    Real.sqrt N ^ k * ∫ ω, |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| ^ k ∂P ≤
      2 * Nat.factorial k * Real.exp (v / N) := by
  intro F
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hsub : HasSubgaussianMGF (fun ω => F ω - ∫ ω', F ω' ∂P) (2 * v.toNNReal) P :=
    hasSubgaussianMGF_log_sum_exp hg hm h0 hv bias
  have hF0 : Measurable F :=
    Measurable.log (Finset.measurable_sum _ fun a _ =>
      Real.measurable_exp.comp ((hm a).add_const (bias a)))
  have hFm : Measurable fun ω => F ω - ∫ ω', F ω' ∂P := hF0.sub_const _
  obtain ⟨hint, hexp⟩ := hsub.integral_pow_abs_le hFm k (inv_pos.2 hs)
  have hN' : (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hN0.le]
  have e : ∀ ω, (Real.sqrt N) ^ k * |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| ^ k =
      ((Real.sqrt N)⁻¹) ^ k * |F ω - ∫ ω', F ω' ∂P| ^ k := fun ω => by
    have e1 : (Real.sqrt N) * |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| =
        (Real.sqrt N)⁻¹ * |F ω - ∫ ω', F ω' ∂P| := by
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN0), hN']
      field_simp
    rw [← mul_pow, e1, mul_pow]
  have e2 : ∀ ω, |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| ^ k =
      ((N : ℝ)⁻¹) ^ k * |F ω - ∫ ω', F ω' ∂P| ^ k := fun ω => by
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN0), mul_pow]
  have hintF : Integrable (fun ω => |(N : ℝ)⁻¹ * F ω - (N : ℝ)⁻¹ * ∫ ω', F ω' ∂P| ^ k) P :=
    Integrable.congr (hint.const_mul (((N : ℝ)⁻¹) ^ k))
      (Filter.Eventually.of_forall fun ω => (e2 ω).symm)
  refine ⟨hintF, ?_⟩
  rw [← integral_const_mul]
  simp_rw [e]
  rw [integral_const_mul]
  refine hexp.trans (le_of_eq ?_)
  congr 1
  congr 1
  have hv0 : 0 ≤ v := by
    obtain ⟨a₀⟩ := ‹Nonempty α›
    exact (integral_nonneg fun _ => sq_nonneg _).trans (hv a₀)
  push_cast
  rw [Real.coe_toNNReal _ hv0, inv_pow, Real.sq_sqrt hN0.le]
  ring

/-- **Lemma 1.4.12 (Talagrand, Eq. (1.113) with deterministic field).**  The free energy
`A_N = N⁻¹ log Z_N` of the SK model has moments of every order `k` concentrated at scale
`N^{-1/2}`: `(√N)^k 𝔼 |A_N - 𝔼 A_N|^k ≤ 2 k! exp (β² / 2)` for all `β`, `h` and `N > 0`, and
`|A_N - 𝔼 A_N|^k` is integrable.  The constant does not depend on `h` or `N`. -/
theorem integral_pow_abs_free_energy_sub_le (β h : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    Integrable (fun g : FinPairs N → ℝ => |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g σ)) - (N : ℝ)⁻¹ * ∫ g', Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g' σ)) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)|
        ^ k) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
    Real.sqrt N ^ k * ∫ g : FinPairs N → ℝ, |(N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g σ)) - (N : ℝ)⁻¹ * ∫ g', Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (skGibbsEnergy N β h g' σ)) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)|
        ^ k ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      2 * Nat.factorial k * Real.exp (β ^ 2 / 2) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨a, ha, hv⟩ := exists_sk_linear_data N β h
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hg : HasGaussianLaw (fun g σ => a σ ⬝ᵥ g)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    hasGaussianLaw_dotProduct_family a
  have hm : ∀ σ, Measurable fun g : FinPairs N → ℝ => a σ ⬝ᵥ g := fun σ => by fun_prop
  have h0 : ∀ σ, ∫ g, a σ ⬝ᵥ g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) = 0 :=
    fun σ => integral_dotProduct_pi_gaussianReal (a σ)
  have hv' : ∀ σ, ∫ g, (a σ ⬝ᵥ g) ^ 2 ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      β ^ 2 * N / 2 := by
    intro σ
    rw [show (fun g => (a σ ⬝ᵥ g) ^ 2) = fun g => (a σ ⬝ᵥ g) * (a σ ⬝ᵥ g) from funext fun g => sq _,
      integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    exact hv σ
  have hkey := integral_pow_abs_sub_integral_log_sum_exp_le hg hm h0 hv'
    (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)) k hN
  have heq : ∀ g, (∑ σ : Fin N → ℤˣ, Real.exp (a σ ⬝ᵥ g + h * ∑ i, ((σ i : ℤ) : ℝ))) =
      ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) := fun g =>
    Finset.sum_congr rfl fun σ _ => by rw [ha]
  simp_rw [heq] at hkey
  have hc : (β ^ 2 * (N : ℝ) / 2) / (N : ℝ) = β ^ 2 / 2 := by
    field_simp
  rw [hc] at hkey
  exact hkey

/-- **Variance bound for the smart path field of a fixed configuration.**
`𝔼 (cos s F_σ + sin s G_σ)² ≤ β² N` uniformly in `s`, for the independent jointly Gaussian
fields `F` (the SK couplings) and `G` (the cavity field) of `exists_sk_smart_path_fields`. -/
theorem integral_smart_path_field_sq_le {N : ℕ} (hN : 0 < N) (β q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) (σ : Fin N → ℤˣ)
    {P : Measure ((FinPairs N → ℝ) × (Fin N → ℝ))}
    (hP : P = (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1))
    (F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hF : ∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
      ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
    (hG : ∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ))
    (hXY : HasGaussianLaw (fun (ω : (FinPairs N → ℝ) × (Fin N → ℝ))
        (t : (Fin N → ℤˣ) ⊕ (Fin N → ℤˣ)) =>
      Sum.elim (fun σ (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) => F ω.1 σ)
        (fun σ ω => G ω.2 σ) t ω) P)
    (h0 : ∀ σ τ, ∫ ω, F ω.1 σ * G ω.2 τ ∂P = 0) :
    ∫ ω, (Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ) ^ 2 ∂P ≤ β ^ 2 * N := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hlin := integral_lincomb_mul_lincomb hXY h0 (Real.cos s) (Real.sin s)
    (Real.cos s) (Real.sin s) σ σ
  refine le_of_eq_of_le (by simpa only [sq] using hlin) ?_
  subst hP
  set Pg : Measure (FinPairs N → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  set Pz : Measure (Fin N → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  set P := Pg.prod Pz
  have : IsProbabilityMeasure Pg := inferInstance
  have : IsProbabilityMeasure Pz := inferInstance
  have hF_sq : ∫ ω, F ω.1 σ * F ω.1 σ ∂P ≤ β ^ 2 * N / 2 := by
    rw [integral_fun_fst (fun g => F g σ * F g σ), probReal_univ, one_smul]
    simp_rw [hF]
    rw [integral_sk_pair_field_mul_eq_overlap hN β σ σ]
    have h1 : (((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ i : ℤ) : ℝ))) ^ 2 -
        (N : ℝ)⁻¹) = 1 - (N : ℝ)⁻¹ := by
      have hcard := card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
        (fun i => units_cast_sq (σ i))
      simp only [Fintype.card_fin] at hcard
      rw [hcard, one_pow]
    rw [h1]
    have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
    have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have hinv_nonneg : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hle1 : 1 - (N : ℝ)⁻¹ ≤ 1 := by linarith
    have hpos : 0 ≤ (N : ℝ) * β ^ 2 / 2 := by positivity
    calc (N : ℝ) * β ^ 2 / 2 * (1 - (N : ℝ)⁻¹)
        ≤ (N : ℝ) * β ^ 2 / 2 * 1 := mul_le_mul_of_nonneg_left hle1 hpos
      _ = β ^ 2 * N / 2 := by ring
  have hG_sq : ∫ ω, G ω.2 σ * G ω.2 σ ∂P ≤ β ^ 2 * N := by
    rw [integral_fun_snd (fun z => G z σ * G z σ), probReal_univ, one_smul]
    simp_rw [hG]
    rw [integral_decoupled_gaussian_field_mul β q hq
      (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((σ i : ℤ) : ℝ))]
    have hdot : ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ i : ℤ) : ℝ)) = N := by
      have hcard := card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
        (fun i => units_cast_sq (σ i))
      simp only [Fintype.card_fin] at hcard
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      calc ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ i : ℤ) : ℝ))
          = (N : ℝ) * ((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ i : ℤ) : ℝ))) := by
            rw [← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
        _ = (N : ℝ) * 1 := by rw [hcard]
        _ = N := mul_one _
    rw [hdot]
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hqN : q * N ≤ 1 * N := mul_le_mul_of_nonneg_right hq1 hN_nonneg
    have hbeta : 0 ≤ β ^ 2 := sq_nonneg β
    calc β ^ 2 * q * N = β ^ 2 * (q * N) := by ring
      _ ≤ β ^ 2 * (1 * N) := mul_le_mul_of_nonneg_left hqN hbeta
      _ = β ^ 2 * N := by ring
  calc Real.cos s * Real.cos s * (∫ ω, F ω.1 σ * F ω.1 σ ∂P) +
        Real.sin s * Real.sin s * (∫ ω, G ω.2 σ * G ω.2 σ ∂P)
      ≤ Real.cos s * Real.cos s * (β ^ 2 * N) + Real.sin s * Real.sin s * (β ^ 2 * N) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (hF_sq.trans ?_) (mul_self_nonneg _))
          (mul_le_mul_of_nonneg_left hG_sq (mul_self_nonneg _))
        have : 0 ≤ β ^ 2 * N := by positivity
        linarith
    _ = β ^ 2 * N := by
        rw [← add_mul, ← sq, ← sq, add_comm, Real.sin_sq_add_cos_sq, one_mul]

/-- **Lemma 1.4.12 along the smart path (Talagrand, Eq. (1.113) along the path).**
The free energy `A_N(s) = N⁻¹ log Z_N(s)` along the smart path has moments of every order `k`
concentrated at scale `N^{-1/2}` uniformly in `s ∈ ℝ`:
`(√N)^k 𝔼 |A_N(s) - 𝔼 A_N(s)|^k ≤ 2 k! exp ((3/2) β²)`, and `|A_N(s) - 𝔼 A_N(s)|^k` is integrable.
The constant is independent of `s`, `h`, `q` and `N`. -/
theorem integral_pow_abs_smart_path_free_energy_sub_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) (k : ℕ) :
    let P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
             (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    let energy : ((FinPairs N → ℝ) × (Fin N → ℝ)) → (Fin N → ℤˣ) → ℝ := fun ω σ =>
      Real.cos s * ((Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, ω.1 p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
      Real.sin s * (β * Real.sqrt q * ∑ i, ω.2 i * ((σ i : ℤ) : ℝ)) +
      h * ∑ i, ((σ i : ℤ) : ℝ)
    let A_s : ((FinPairs N → ℝ) × (Fin N → ℝ)) → ℝ := fun ω =>
      (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (energy ω σ))
    Integrable (fun ω => |A_s ω - ∫ ω', A_s ω' ∂P| ^ k) P ∧
    Real.sqrt N ^ k * ∫ ω, |A_s ω - ∫ ω', A_s ω' ∂P| ^ k ∂P ≤
      2 * Nat.factorial k * Real.exp (3 / 2 * β ^ 2) := by
  intro P energy A_s
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨F, G, hF, hG, hFm, hGm, hXG', hX0, hY0, h0, -⟩ :=
    exists_sk_smart_path_fields hN β q hq (P := P) rfl
  set g : (Fin N → ℤˣ) → ((FinPairs N → ℝ) × (Fin N → ℝ)) → ℝ :=
    fun σ ω => Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ
  have hg : HasGaussianLaw (fun ω σ => g σ ω) P := hXG'.cos_sin_combination s
  have hm : ∀ σ, Measurable (g σ) := fun σ => by
    have e : g σ = fun ω => Real.cos s *
        ((Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, ω.1 p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        Real.sin s * (β * Real.sqrt q * ∑ i, ω.2 i * ((σ i : ℤ) : ℝ)) := by
      ext ω
      simp only [g, hF, hG]
    rw [e]
    fun_prop
  have hg0 : ∀ σ, ∫ ω, g σ ω ∂P = 0 := fun σ =>
    integral_lincomb_eq_zero hX0 hY0 (fun a => (hXG'.eval (Sum.inl a)).integrable)
      (fun a => (hXG'.eval (Sum.inr a)).integrable) (Real.cos s) (Real.sin s) σ
  have hv : ∀ σ, ∫ ω, g σ ω ^ 2 ∂P ≤ 3 / 2 * β ^ 2 * N := fun σ =>
    (integral_smart_path_field_sq_le hN β q hq hq1 s σ rfl F G hF hG hXG' h0).trans
      (by nlinarith [sq_nonneg β, Nat.cast_nonneg (α := ℝ) N])
  have hkey := integral_pow_abs_sub_integral_log_sum_exp_le hg hm hg0 hv
    (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)) k hN
  have heq : ∀ ω, (∑ σ : Fin N → ℤˣ, Real.exp (g σ ω + h * ∑ i, ((σ i : ℤ) : ℝ))) =
      ∑ σ : Fin N → ℤˣ, Real.exp (energy ω σ) := fun ω =>
    Finset.sum_congr rfl fun σ _ => by
      congr 1
      simp only [g, energy, hF, hG]
  simp_rw [heq] at hkey
  have hc : (3 / 2 * β ^ 2 * (N : ℝ)) / (N : ℝ) = 3 / 2 * β ^ 2 := by
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_right₀ _ hN0
  rw [hc] at hkey
  rw [integral_const_mul (N : ℝ)⁻¹]
  exact hkey

/-- **Replica-symmetric free energy along the smart path.**
`skPathRS β h q s = log 2 + 𝔼 log cosh (β √q z + h) + (β² / 4) (1 - q)² cos² s`.
At `s = 0` it equals the static RS bound `rsFunctional β h q`; at `s = π/2` it equals the
decoupled free energy. -/
noncomputable def skPathRS (β h q s : ℝ) : ℝ :=
  Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) +
    β ^ 2 / 4 * (1 - q) ^ 2 * Real.cos s ^ 2

@[simp] theorem skPathRS_zero (β h q : ℝ) :
    skPathRS β h q 0 = rsFunctional β h q := by
  simp only [skPathRS, rsFunctional, Real.cos_zero, one_pow, mul_one]

@[simp] theorem skPathRS_pi_div_two (β h q : ℝ) :
    skPathRS β h q (Real.pi / 2) =
      Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) := by
  simp only [skPathRS, Real.cos_pi_div_two, sq, mul_zero, add_zero]

theorem hasDerivAt_skPathRS (β h q s : ℝ) :
    HasDerivAt (skPathRS β h q)
      (-(β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin s * Real.cos s)) s := by
  have hcos : HasDerivAt (fun x => Real.cos x ^ 2) (-2 * Real.sin s * Real.cos s) s := by
    convert (Real.hasDerivAt_cos s).pow 2 using 1
    ring
  have hderiv := (hcos.const_mul (β ^ 2 / 4 * (1 - q) ^ 2)).const_add
    (Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1))
  have e : (fun x => Real.log 2 +
      ∫ y : ℝ, Real.log (Real.cosh (β * Real.sqrt q * y + h)) ∂(gaussianReal 0 1) +
      β ^ 2 / 4 * (1 - q) ^ 2 * Real.cos x ^ 2) = skPathRS β h q := rfl
  rw [e] at hderiv
  have ed : β ^ 2 / 4 * (1 - q) ^ 2 * (-2 * Real.sin s * Real.cos s) =
      -(β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin s * Real.cos s) := by ring
  rw [ed] at hderiv
  exact hderiv

/-- **Deterministic bound on the expected smart path free energy.**
For `β² < 1/4`, a fixed point `q`, and `s ∈ [0, π/2]`, the expected smart path free energy
`φ(s) = 𝔼 A_N(s)` satisfies
`|φ(s) - skPathRS β h q s| ≤ (β² / 4) * K₁ / N`, where
`K₁ = (1/2 - 2β²)^{-1/2} / (1/4 - β²)`. -/
theorem sk_smart_path_free_energy_sub_rs_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {s : ℝ} (hs : s ∈ Set.Icc 0 (Real.pi / 2))
    {φ A : ℝ → ℝ}
    (hpi : φ (Real.pi / 2) = Real.log 2 +
      ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1))
    (hderiv : ∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2)) t)
    (hA : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      A t = ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
          Real.cos t * ((Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
          Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
          h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1))) :
    let K1 : ℝ := (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2)
    |φ s - skPathRS β h q s| ≤ β ^ 2 / 4 * K1 / N := by
  intro K1
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hK1pos : 0 ≤ K1 := by
    have h1 : 0 ≤ (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ := by positivity
    have h2 : 0 < 1 / 4 - β ^ 2 := by linarith
    exact div_nonneg h1 h2.le
  have hA_le : ∀ t ∈ Set.Icc 0 (Real.pi / 2), |A t| ≤ K1 / N := fun t ht => by
    have hpow := sk_path_expected_pow_overlap_le hN β h q hfix hβ 1 ht
    have hr : 2 * 1 = 2 := rfl
    rw [hr] at hpow
    have hAeq := hA t ht
    have hAnn : 0 ≤ A t := by
      rw [hAeq]
      exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    have hK1 : (Nat.factorial 1 : ℝ) * (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ /
        ((1 / 4 - β ^ 2) ^ 1 * (N : ℝ) ^ 1) = K1 / N := by
      simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one, K1, div_div]
    rw [hK1] at hpow
    rw [abs_of_nonneg hAnn, hAeq]
    exact hpow
  set K := β ^ 2 / 2 * K1 / N
  have hhd : ∀ t, ∃ D, HasDerivAt (fun x => φ x - skPathRS β h q x)
      (Real.sin t * Real.cos t * D) t ∧ (t ∈ Set.Icc 0 (Real.pi / 2) → |D| ≤ K) := fun t => by
    refine ⟨β ^ 2 / 2 * A t, ?_, fun ht => ?_⟩
    · have hd := (hderiv t).sub (hasDerivAt_skPathRS β h q t)
      have ed : (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2) -
          -(β ^ 2 / 2 * (1 - q) ^ 2 * Real.sin t * Real.cos t)) =
          Real.sin t * Real.cos t * (β ^ 2 / 2 * A t) := by ring
      rw [ed] at hd
      exact hd
    · have hAt := hA_le t ht
      have hpos : 0 ≤ β ^ 2 / 2 := by positivity
      calc |β ^ 2 / 2 * A t| = β ^ 2 / 2 * |A t| := by
            rw [abs_mul, abs_of_nonneg hpos]
        _ ≤ β ^ 2 / 2 * (K1 / N) := mul_le_mul_of_nonneg_left hAt hpos
        _ = K := by ring
  have hpi_sub : φ (Real.pi / 2) - skPathRS β h q (Real.pi / 2) = 0 := by
    rw [hpi, skPathRS_pi_div_two, sub_self]
  have hsub := Real.abs_sub_le_of_exists_hasDerivAt_Icc hhd hs.1 hs.2 le_rfl
  rw [hpi_sub, zero_sub, abs_neg] at hsub
  refine hsub.trans ?_
  have hsin : Real.sin (Real.pi / 2) ^ 2 - Real.sin s ^ 2 ≤ 1 := by
    have : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    rw [this, one_pow]
    linarith [sq_nonneg (Real.sin s)]
  have hK_nonneg : 0 ≤ K / 2 := by positivity
  calc K / 2 * (Real.sin (Real.pi / 2) ^ 2 - Real.sin s ^ 2)
      ≤ K / 2 * 1 := mul_le_mul_of_nonneg_left hsin hK_nonneg
    _ = β ^ 2 / 4 * K1 / N := by ring

/-- **Moments of the smart-path free energy around the RS value.**
For `β² < 1/4`, a fixed point `q`, and `s ∈ [0, π/2]`,
`V(s) = A_N(s) - skPathRS β h q s` satisfies
`√N^k 𝔼 |V(s)|^k ≤ 2^{k-1} (2 k! exp ((3/2) β²) + ((β² / 4) * K₁)^k)`
where `K₁ = (1/2 - 2β²)^{-1/2} / (1/4 - β²)`. -/
theorem integral_pow_abs_smart_path_V_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {s : ℝ} (hs : s ∈ Set.Icc 0 (Real.pi / 2)) (k : ℕ) :
    let P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
             (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    let energy : ((FinPairs N → ℝ) × (Fin N → ℝ)) → (Fin N → ℤˣ) → ℝ := fun ω σ =>
      Real.cos s * ((Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, ω.1 p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
      Real.sin s * (β * Real.sqrt q * ∑ i, ω.2 i * ((σ i : ℤ) : ℝ)) +
      h * ∑ i, ((σ i : ℤ) : ℝ)
    let A_s : ((FinPairs N → ℝ) × (Fin N → ℝ)) → ℝ := fun ω =>
      (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (energy ω σ))
    let K1 : ℝ := (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2)
    Integrable (fun ω => |A_s ω - skPathRS β h q s| ^ k) P ∧
    Real.sqrt N ^ k * ∫ ω, |A_s ω - skPathRS β h q s| ^ k ∂P ≤
      2 ^ (k - 1) * (2 * Nat.factorial k * Real.exp (3 / 2 * β ^ 2) + (β ^ 2 / 4 * K1) ^ k) := by
  intro P energy A_s K1
  have hq_mem := fixedPoint_mem_Icc hfix
  have hq : 0 ≤ q := hq_mem.1
  have hq1 : q ≤ 1 := hq_mem.2
  have hprobP : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  obtain ⟨hint_cent, hmom_cent⟩ :=
    integral_pow_abs_smart_path_free_energy_sub_le hN β h q hq hq1 s k
  obtain ⟨φ, A, -, hpi, hderiv, -, hA, hφ⟩ := exists_sk_smart_path_profile hN β h q hq
  have hsub := sk_smart_path_free_energy_sub_rs_le hN β h q hfix hβ hs hpi hderiv (fun t ht => hA t)
  have hφ_eq : φ s = ∫ ω, A_s ω ∂P := by
    rw [hφ s]
    dsimp [A_s, energy]
    rw [← integral_const_mul]
  have hmean_sub : |∫ ω, A_s ω ∂P - skPathRS β h q s| ≤ β ^ 2 / 4 * K1 / N := by
    rw [← hφ_eq]
    exact hsub
  set X := fun ω => A_s ω - ∫ ω', A_s ω' ∂P
  set c := ∫ ω', A_s ω' ∂P - skPathRS β h q s
  have hpoint : ∀ ω, |A_s ω - skPathRS β h q s| ^ k ≤
      2 ^ (k - 1) * (|X ω| ^ k + |c| ^ k) := fun ω => by
    have hid : A_s ω - skPathRS β h q s = X ω + c := by ring
    rw [hid]
    exact abs_add_pow_le (X ω) c k
  have hint_c : Integrable (fun _ : (FinPairs N → ℝ) × (Fin N → ℝ) => |c| ^ k) P :=
    integrable_const (|c| ^ k)
  have hint_sum : Integrable (fun ω => 2 ^ (k - 1) * (|X ω| ^ k + |c| ^ k)) P :=
    (hint_cent.add hint_c).const_mul (2 ^ (k - 1))
  have hmeas : AEStronglyMeasurable (fun ω => |A_s ω - skPathRS β h q s| ^ k) P := by
    refine Measurable.aestronglyMeasurable ?_
    refine (Continuous.measurable (by fun_prop : Continuous fun x : ℝ =>
      |x - skPathRS β h q s| ^ k)).comp ?_
    dsimp [A_s]
    refine Measurable.const_mul ?_ (N : ℝ)⁻¹
    refine Real.measurable_log.comp ?_
    refine Finset.measurable_sum _ fun σ _ => ?_
    refine Real.measurable_exp.comp ?_
    dsimp [energy]
    fun_prop
  have hint_V : Integrable (fun ω => |A_s ω - skPathRS β h q s| ^ k) P :=
    Integrable.mono' hint_sum hmeas (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint ω)
  refine ⟨hint_V, ?_⟩
  have h_int_le : ∫ ω, |A_s ω - skPathRS β h q s| ^ k ∂P ≤
      2 ^ (k - 1) * (∫ ω, |X ω| ^ k ∂P + |c| ^ k) := by
    have h1 := integral_mono hint_V hint_sum hpoint
    rw [integral_const_mul, integral_add hint_cent hint_c, integral_const,
      probReal_univ, one_smul] at h1
    exact h1
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hsqrt_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hpow_nonneg : 0 ≤ Real.sqrt N ^ k := by positivity
  have hmul := mul_le_mul_of_nonneg_left h_int_le hpow_nonneg
  have hK1pos : 0 ≤ K1 := by
    have h1 : 0 ≤ (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ := by positivity
    have h2 : 0 < 1 / 4 - β ^ 2 := by linarith
    exact div_nonneg h1 h2.le
  have hc_le : Real.sqrt N * |c| ≤ β ^ 2 / 4 * K1 := by
    calc Real.sqrt N * |c| ≤ Real.sqrt N * (β ^ 2 / 4 * K1 / N) :=
          mul_le_mul_of_nonneg_left hmean_sub hsqrt_nonneg
      _ = (β ^ 2 / 4 * K1) * (Real.sqrt N / N) := by ring
      _ ≤ (β ^ 2 / 4 * K1) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
        have hle : Real.sqrt N ≤ N := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
        exact div_le_one_of_le₀ hle (by positivity)
      _ = β ^ 2 / 4 * K1 := mul_one _
  have hpow_c_le : Real.sqrt N ^ k * |c| ^ k ≤ (β ^ 2 / 4 * K1) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hc_le k
  calc Real.sqrt N ^ k * ∫ ω, |A_s ω - skPathRS β h q s| ^ k ∂P
      ≤ Real.sqrt N ^ k * (2 ^ (k - 1) * (∫ ω, |X ω| ^ k ∂P + |c| ^ k)) := hmul
    _ = 2 ^ (k - 1) * (Real.sqrt N ^ k * ∫ ω, |X ω| ^ k ∂P + Real.sqrt N ^ k * |c| ^ k) := by ring
    _ ≤ 2 ^ (k - 1) * (2 * Nat.factorial k * Real.exp (3 / 2 * β ^ 2) + (β ^ 2 / 4 * K1) ^ k) := by
      refine mul_le_mul_of_nonneg_left (add_le_add hmom_cent hpow_c_le) (by positivity)

end SpinGlasses
