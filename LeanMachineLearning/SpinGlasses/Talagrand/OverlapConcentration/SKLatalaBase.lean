/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica
public import LeanMachineLearning.SpinGlasses.SKDecoupled
public import LeanMachineLearning.SpinGlasses.SKFixedPoint
public import LeanMachineLearning.SpinGlasses.SKLatalaCompensated
public import LeanMachineLearning.SpinGlasses.SKFirstMoment
public import LeanMachineLearning.ForMathlib.Probability.Moments.TwoPointHoeffding
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.ExpSq
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# The base case of Latała's argument (Talagrand, Proposition 1.4.8)

The decoupled model (`t = 0` in Talagrand's parametrization, `s = π / 2` here) has exactly
sub-Gaussian overlap: `𝔼⟨exp (u N (R₁,₂ - q))⟩ ≤ exp (N u² / 2)`.  This module turns such a
sub-Gaussian moment generating function bound into the bound
`𝔼⟨exp (λ N (R₁,₂ - q)²)⟩ ≤ (1 - 2 λ)^{-1/2}` by the Gaussian linearization
`exp (θ x² / 2) = 𝔼_g exp (√θ g x)`.

## Main declarations

* `SpinGlasses.integral_exp_sq_le_of_mgf_le`: the Gaussian linearization trick for
  replica averages of Gibbs measures with disorder.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {Z : Type*} [MeasurableSpace Z]

/-- **Gaussian linearization of a sub-Gaussian replica observable.**  Let `X` be an observable of
`n` replicas and `f z` a Gibbs energy depending measurably on a parameter `z`.  If
`𝔼_z ⟨exp (u X)⟩_z ≤ exp (c u² / 2)` for all real `u`, then for `0 ≤ θ` with `θ c < 1`,
`𝔼_z ⟨exp (θ X² / 2)⟩_z ≤ (1 - θ c)^{-1/2}`.
(Write `exp (θ x² / 2) = 𝔼_g exp (√θ g x)` for a standard Gaussian `g`, exchange the integrals and
apply the hypothesis with `u = √θ g`.) -/
theorem integral_exp_sq_le_of_mgf_le [Finite α] [Nonempty α] [Fintype R]
    {P : Measure Z} [IsProbabilityMeasure P] {f : Z → α → ℝ}
    (hf : ∀ a, AEMeasurable (fun z => f z a) P) (X : (R → α) → ℝ) {c θ : ℝ} (hθ : 0 ≤ θ)
    (hθc : θ * c < 1)
    (hmgf : ∀ u : ℝ, ∫ z, ∫ σ, Real.exp (u * X σ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f z)) ∂P ≤ Real.exp (c * u ^ 2 / 2)) :
    ∫ z, ∫ σ, Real.exp (θ / 2 * X σ ^ 2)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f z)) ∂P ≤
      (Real.sqrt (1 - θ * c))⁻¹ := by
  have := Fintype.ofFinite α
  classical
  obtain ⟨B, hB⟩ : ∃ B, ∀ σ, |X σ| ≤ B :=
    (Set.finite_range fun σ => |X σ|).bddAbove.imp fun B hB σ => hB ⟨σ, rfl⟩
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  set m : Z → Measure (R → α) := fun z => Measure.pi fun _ : R => Measure.count.tilted (f z)
    with hm
  have hs : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ
  -- the integrand as an integral against a Gaussian
  have hexp : ∀ x : ℝ, Real.exp (θ / 2 * x ^ 2) = ∫ g, Real.exp (Real.sqrt θ * g * x) ∂γ :=
    fun x => by
      have e : ∀ g : ℝ, Real.sqrt θ * g * x = (Real.sqrt θ * x) * g := fun g => by ring
      simp_rw [e]
      rw [hγ, integral_exp_mul_gaussianReal_zero_one, mul_pow, hs]
      congr 1
      ring
  -- exchange of the replica average and the Gaussian average
  have hsum : ∀ (z : Z) (g : ℝ), ∫ σ, Real.exp (Real.sqrt θ * g * X σ) ∂m z =
      ∑ σ, (m z).real {σ} • Real.exp (Real.sqrt θ * g * X σ) := fun z g =>
    integral_fintype Integrable.of_finite
  have hswap : ∀ z, ∫ σ, Real.exp (θ / 2 * X σ ^ 2) ∂m z =
      ∫ g, ∫ σ, Real.exp (Real.sqrt θ * g * X σ) ∂m z ∂γ := fun z => by
    simp_rw [hsum, smul_eq_mul]
    rw [integral_fintype Integrable.of_finite, integral_finsetSum]
    · refine sum_congr rfl fun σ _ => ?_
      rw [integral_const_mul, ← hexp, smul_eq_mul]
    · intro σ _
      refine Integrable.const_mul ?_ _
      have e : ∀ g : ℝ, Real.sqrt θ * g * X σ = (Real.sqrt θ * X σ) * g := fun g => by ring
      simp_rw [e]
      exact integrable_exp_mul_gaussianReal _
  set G : Z → ℝ → ℝ := fun z g => ∫ σ, Real.exp (Real.sqrt θ * g * X σ) ∂m z with hG
  have hGmeas : AEMeasurable (fun p : Z × ℝ => G p.1 p.2) (P.prod γ) :=
    aemeasurable_integral_pi_count_tilted (R := R) (g := fun (p : Z × ℝ) a => f p.1 a)
      (Θ := fun (p : Z × ℝ) σ => Real.exp (Real.sqrt θ * p.2 * X σ))
      (fun a => (hf a).comp_quasiMeasurePreserving
        (measurePreserving_fst (μ := P) (ν := γ)).quasiMeasurePreserving) fun σ =>
      (by fun_prop : Measurable fun p : Z × ℝ =>
        Real.exp (Real.sqrt θ * p.2 * X σ)).aemeasurable
  have hGbd : ∀ (z : Z) (g : ℝ), |G z g| ≤ Real.exp (Real.sqrt θ * B * |g|) := fun z g =>
    abs_integral_pi_count_tilted_le _ fun σ => by
      rw [abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      calc Real.sqrt θ * g * X σ ≤ |Real.sqrt θ * g * X σ| := le_abs_self _
        _ = Real.sqrt θ * |g| * |X σ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg θ)]
        _ ≤ Real.sqrt θ * |g| * B := mul_le_mul_of_nonneg_left (hB σ) (by positivity)
        _ = Real.sqrt θ * B * |g| := by ring
  have hGint : Integrable (fun p : Z × ℝ => G p.1 p.2) (P.prod γ) :=
    Integrable.mono' ((integrable_exp_mul_abs_gaussianReal (Real.sqrt θ * B)).comp_snd P)
      hGmeas.aestronglyMeasurable (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]; exact hGbd p.1 p.2)
  calc ∫ z, ∫ σ, Real.exp (θ / 2 * X σ ^ 2) ∂m z ∂P = ∫ z, ∫ g, G z g ∂γ ∂P :=
        integral_congr_ae (ae_of_all _ hswap)
    _ = ∫ g, ∫ z, G z g ∂P ∂γ := integral_integral_swap hGint
    _ ≤ ∫ g, Real.exp (c * θ / 2 * g ^ 2) ∂γ := by
        refine integral_mono hGint.integral_prod_right (integrable_exp_mul_sq_gaussianReal
          (by nlinarith [mul_comm θ c])) fun g => ?_
        have := hmgf (Real.sqrt θ * g)
        refine this.trans_eq ?_
        rw [mul_pow, hs]
        congr 1
        ring
    _ = (Real.sqrt (1 - θ * c))⁻¹ := by
        rw [integral_exp_mul_sq_gaussianReal (by nlinarith [mul_comm θ c])]
        congr 2
        ring

/-- The two-replica, one-site factor of the decoupled model:
`∑_{s,t = ±1} e^{s y + t y + u (s t - q)} = 4 cosh² y · e^{-u q} (cosh u + tanh² y sinh u)`. -/
theorem sum_sum_exp_overlap_site (y u q : ℝ) :
    (∑ s : ℤˣ, ∑ t : ℤˣ, Real.exp (((s : ℤ) : ℝ) * y) * (Real.exp (((t : ℤ) : ℝ) * y) *
      Real.exp (u * (((s : ℤ) : ℝ) * ((t : ℤ) : ℝ) - q)))) =
    4 * Real.cosh y ^ 2 *
      (Real.exp (-(u * q)) * (Real.cosh u + Real.tanh y ^ 2 * Real.sinh u)) := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  simp only [sum_units_int, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul,
    neg_mul, mul_one, mul_neg, neg_neg]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  simp only [Real.cosh_eq, Real.sinh_eq]
  have h1 : Real.exp (u * (1 - q)) = Real.exp u * Real.exp (-(u * q)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (u * (-1 - q)) = Real.exp (-u) * Real.exp (-(u * q)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]
  simp only [Real.exp_neg]
  have := Real.exp_pos y
  have := Real.exp_pos u
  field_simp
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The pair of replicas factorizes over the sites of the decoupled model.** -/
theorem sum_sum_decoupled_overlap_exp (y : ι → ℝ) (u q : ℝ) :
    ∑ a : ι → ℤˣ, ∑ b : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * y i) *
      (Real.exp (∑ i, ((b i : ℤ) : ℝ) * y i) *
        Real.exp (u * ∑ i, (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ) - q))) =
      ∏ i, (4 * Real.cosh (y i) ^ 2 *
        (Real.exp (-(u * q)) * (Real.cosh u + Real.tanh (y i) ^ 2 * Real.sinh u))) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [← Finset.prod_mul_distrib]
  have h : ∀ a : ι → ℤˣ, ∑ b : ι → ℤˣ, ∏ i, (Real.exp (((a i : ℤ) : ℝ) * y i) *
      (Real.exp (((b i : ℤ) : ℝ) * y i) *
        Real.exp (u * (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ) - q)))) =
      ∏ i, ∑ t : ℤˣ, Real.exp (((a i : ℤ) : ℝ) * y i) *
        (Real.exp (((t : ℤ) : ℝ) * y i) * Real.exp (u * (((a i : ℤ) : ℝ) * ((t : ℤ) : ℝ) - q))) :=
    fun a => by
      rw [hypercube_sum_prod_eq_prod_add (fun i t => Real.exp (((a i : ℤ) : ℝ) * y i) *
        (Real.exp (((t : ℤ) : ℝ) * y i) * Real.exp (u * (((a i : ℤ) : ℝ) * ((t : ℤ) : ℝ) - q))))]
      exact Finset.prod_congr rfl fun i _ => by rw [sum_units_int]
  simp_rw [h]
  rw [hypercube_sum_prod_eq_prod_add (fun i s => ∑ t : ℤˣ, Real.exp (((s : ℤ) : ℝ) * y i) *
    (Real.exp (((t : ℤ) : ℝ) * y i) * Real.exp (u * (((s : ℤ) : ℝ) * ((t : ℤ) : ℝ) - q))))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← sum_sum_exp_overlap_site]
  simp only [sum_units_int]

omit [DecidableEq ι] in
/-- **The exponential overlap moment of the decoupled model.**  For two independent replicas of
the Gibbs measure of non-interacting spins in the fields `Y i`,
`⟨exp (u ∑ᵢ (σ¹ᵢ σ²ᵢ - q))⟩ = ∏ᵢ e^{-u q} (cosh u + tanh² Yᵢ sinh u)`. -/
theorem integral_decoupled_pair_exp (Y : ι → ℝ) (u q : ℝ) :
    ∫ σ : Fin 2 → (ι → ℤˣ),
        Real.exp (u * ∑ i, (((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q))
          ∂(Measure.pi fun _ : Fin 2 =>
            Measure.count.tilted fun a => ∑ i, ((a i : ℤ) : ℝ) * Y i) =
      ∏ i, (Real.exp (-(u * q)) * (Real.cosh u + Real.tanh (Y i) ^ 2 * Real.sinh u)) := by
  classical
  rw [integral_pi_fin_two_count_tilted _ (fun a b : ι → ℤˣ =>
    Real.exp (u * ∑ i, (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ) - q)))]
  have hZ := decoupled_partition_function_eq Y
  have hZ0 : 0 < ∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i) := by
    rw [hZ]; positivity
  have key : ∀ G : (ι → ℤˣ) → (ι → ℤˣ) → ℝ,
      ∑ a : ι → ℤˣ, ∑ b : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * Y i) /
          (∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i)) *
        (Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i) /
          ∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i)) * G a b =
      ((∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i))⁻¹) ^ 2 *
        ∑ a : ι → ℤˣ, ∑ b : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * Y i) *
          (Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i) * G a b) := fun G => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [key (fun a b => Real.exp (u * ∑ i, (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ) - q))),
    sum_sum_decoupled_overlap_exp, hZ, Finset.prod_mul_distrib]
  have h4 : ∏ i, (4 * Real.cosh (Y i) ^ 2) =
      ((2 : ℝ) ^ Fintype.card ι * ∏ i, Real.cosh (Y i)) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, mul_pow, ← pow_mul,
      mul_comm (Fintype.card ι) 2, pow_mul]
    simp
    norm_num
  have hpos : 0 < (2 : ℝ) ^ Fintype.card ι * ∏ i, Real.cosh (Y i) := by positivity
  rw [h4]
  field_simp
  simp_rw [mul_comm (Real.sinh u)]

section Decoupled

open scoped Real Matrix

/-- **Sub-Gaussian overlap of the decoupled model (Talagrand Eq. (1.105)).**  At the fixed point
`q = 𝔼 tanh² (β √q z + h)` of the self-consistency equation,
`𝔼 ⟨exp (u ∑ᵢ (σ¹ᵢ σ²ᵢ - q))⟩ ≤ exp (N u² / 2)` for every real `u`. -/
theorem integral_decoupled_pair_exp_le {N : ℕ} (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) (u : ℝ) :
    ∫ z : Fin N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp (u * ∑ i, (((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q))
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ Real.exp (N * u ^ 2 / 2) := by
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hq0 := hqI.1
  have hq1 := hqI.2
  simp_rw [decoupled_field_eq, integral_decoupled_pair_exp]
  rw [integral_fintype_prod_eq_prod (E := fun _ : Fin N => ℝ)
    (μ := fun _ : Fin N => gaussianReal 0 1)
    (fun _ x => Real.exp (-(u * q)) *
      (Real.cosh u + Real.tanh (β * Real.sqrt q * x + h) ^ 2 * Real.sinh u))]
  have hone : ∫ x : ℝ, Real.exp (-(u * q)) * (Real.cosh u +
      Real.tanh (β * Real.sqrt q * x + h) ^ 2 * Real.sinh u) ∂(gaussianReal 0 1) =
      (Real.cosh u + q * Real.sinh u) * Real.exp (-(q * u)) := by
    rw [integral_const_mul, integral_add (integrable_const _)
      ((integrable_tanh_sq _ (by fun_prop)).mul_const _), integral_const, integral_mul_const,
      hfix]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [mul_comm u q, mul_comm]
  simp_rw [hone]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show Real.exp (N * u ^ 2 / 2) = Real.exp (u ^ 2 / 2) ^ N by
      rw [← Real.exp_nat_mul]; ring_nf]
  have hq : |q| ≤ 1 := abs_le.2 ⟨by linarith, hq1⟩
  exact pow_le_pow_left₀ (mul_nonneg (cosh_add_mul_sinh_nonneg q hq u) (Real.exp_pos _).le)
    (cosh_add_mul_sinh_mul_exp_neg_le q hq u) N

/-- **Proposition 1.4.8 (base case at `t = 0`).**  At the fixed point `q = 𝔼 tanh² (β √q z + h)`,
for `0 ≤ λ < 1 / 2` the decoupled model satisfies
`𝔼 ⟨exp (λ N (R₁,₂ - q)²)⟩ ≤ (1 - 2 λ)^{-1/2}`. -/
theorem integral_decoupled_exp_overlap_sq_le {N : ℕ} (hN : 0 < N) (β h q lam : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2) :
    ∫ z : Fin N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * lam) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ (Real.sqrt (1 - 2 * lam))⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have hmain := integral_exp_sq_le_of_mgf_le (α := Fin N → ℤˣ) (R := Fin 2)
    (P := Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (f := fun (z : Fin N → ℝ) (a : Fin N → ℤˣ) =>
      β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ))
    (fun a => (by fun_prop : Measurable fun z : Fin N → ℝ =>
      β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ)).aemeasurable)
    (fun σ => ∑ i, (((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q)) (c := N) (θ := 2 * lam / N)
    (by positivity) (by field_simp; linarith)
    (fun u => integral_decoupled_pair_exp_le β h q hfix u)
  refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun z => ?_)) (hmain.trans_eq ?_)
  · refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only
    congr 1
    have e : ∑ i, (((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q) =
        N * ((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ)) - q) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_sub,
        ← mul_assoc, mul_inv_cancel₀ hN0, one_mul, nsmul_eq_mul]
      rfl
    rw [e]
    field_simp
  · rw [div_mul_cancel₀ _ hN0]

end Decoupled

end SpinGlasses
