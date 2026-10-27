/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianTiltedFreeEnergy
public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.SKFirstMoment
public import LeanMachineLearning.SpinGlasses.SKGaussianFluctuation

/-!
# The coupled free energy (Talagrand, Eqs. (1.283)--(1.286))

Two copies of a system with energy `f` that interact through `λ Θ(σ¹, σ²)` have partition function
`Z_λ = ∑_{σ¹,σ²} exp(f σ¹ + f σ² + λ Θ(σ¹, σ²))`.  Since `Z_0 = (∑_σ exp (f σ))²`, one has
`log Z_λ - log Z_0 = log ⟨exp(λ Θ)⟩`, the average being over two independent replicas of the
Gibbs measure of `f`.  For `Θ = R₁₂ · M` this is the identity (1.286).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eqs. (1.283)--(1.286).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SpinGlasses

/-- **Eq. (1.286), finite form.**  For a finite nonempty configuration space `α`, an energy
`f` and a pair interaction `Θ`,
`log ∑_{x,y} exp(f x + f y + Θ x y) - log ∑_{x,y} exp(f x + f y)
  = log 𝔼_{σ¹,σ² ∼ Gibbs(f)} exp(Θ(σ¹, σ²))`. -/
theorem log_sum_sum_exp_coupled_sub {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) (Θ : α → α → ℝ) :
    Real.log (∑ x, ∑ y, Real.exp (f x + f y + Θ x y)) -
        Real.log (∑ x, ∑ y, Real.exp (f x + f y)) =
      Real.log (∫ σ : Fin 2 → α, Real.exp (Θ (σ 0) (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f)) := by
  have hZ : 0 < ∑ b, Real.exp (f b) := Finset.sum_pos (fun b _ => Real.exp_pos _)
    Finset.univ_nonempty
  have hA : 0 < ∑ x, ∑ y, Real.exp (f x + f y + Θ x y) :=
    Finset.sum_pos (fun x _ => Finset.sum_pos (fun y _ => Real.exp_pos _) Finset.univ_nonempty)
      Finset.univ_nonempty
  have hZ2 : ∑ x, ∑ y, Real.exp (f x + f y) = (∑ b, Real.exp (f b)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Real.exp_add]
  have hint : ∫ σ : Fin 2 → α, Real.exp (Θ (σ 0) (σ 1))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) =
      (∑ x, ∑ y, Real.exp (f x + f y + Θ x y)) / (∑ b, Real.exp (f b)) ^ 2 := by
    rw [integral_pi_fin_two_count_tilted f (fun x y => Real.exp (Θ x y)), Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Real.exp_add]
    field_simp
  rw [hint, hZ2, Real.log_div hA.ne' (pow_pos hZ 2).ne']

section SK

/-- **The coupled partition function** `Z_{N,λ}` of two SK systems with the same disorder `g`
that interact through `λ N R₁,₂ = λ ∑ᵢ σ¹ᵢ σ²ᵢ` (Talagrand, Eqs. (1.283), (1.284)); here `M`
is the number of spins. -/
noncomputable def skCoupledPartition (M : ℕ) (β h lam : ℝ) (g : FinPairs M → ℝ) : ℝ :=
  ∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ, Real.exp (skGibbsEnergy M β h g σ +
    skGibbsEnergy M β h g τ + lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))

/-- **The coupled free energy** `ψ_M(λ) = M⁻¹ 𝔼 log Z_{M,λ} - M⁻¹ 𝔼 log Z_{M,0}`
(Talagrand, Eq. (1.285)). -/
noncomputable def skCoupledFreeEnergy (M : ℕ) (β h lam : ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ((∫ g, Real.log (skCoupledPartition M β h lam g)
      ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) -
    ∫ g, Real.log (skCoupledPartition M β h 0 g)
      ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1))

/-- **The mean overlap of the coupled system** `𝔼 ⟨R₁,₂⟩_λ`, where `⟨·⟩_λ` is the Gibbs average
for the Hamiltonian (1.283), `R₁,₂ = M⁻¹ ∑ᵢ σ¹ᵢ σ²ᵢ`; this is `ψ_M'(λ)`
(`hasDerivAt_skCoupledFreeEnergy`). -/
noncomputable def skCoupledOverlapMean (M : ℕ) (β h lam : ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∫ g, (∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ,
    (∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) * Real.exp (skGibbsEnergy M β h g σ +
      skGibbsEnergy M β h g τ + lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))) /
    skCoupledPartition M β h lam g ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)

/-- **The two-replica system as a Gaussian field on pairs of configurations.**  There are
coefficient vectors `a`, offsets `d` and the overlap numerator `b` on the pairs `(σ, τ)` such that
the energy of the pair is the linear form `a (σ, τ) ⬝ᵥ g + d (σ, τ)` of the disorder, with
variance `a ⬝ᵥ a ≤ 2 β² M`. -/
theorem exists_sk_coupled_data (M : ℕ) (β h : ℝ) :
    ∃ (a : (Fin M → ℤˣ) × (Fin M → ℤˣ) → FinPairs M → ℝ)
      (d b : (Fin M → ℤˣ) × (Fin M → ℤˣ) → ℝ),
      (∀ x g, skGibbsEnergy M β h g x.1 + skGibbsEnergy M β h g x.2 = a x ⬝ᵥ g + d x) ∧
      (∀ x, b x = ∑ i, ((x.1 i : ℤ) : ℝ) * ((x.2 i : ℤ) : ℝ)) ∧
      (∀ x, |b x| ≤ M) ∧ ∀ x, a x ⬝ᵥ a x ≤ 2 * β ^ 2 * M := by
  refine ⟨fun x p => (Real.sqrt M)⁻¹ * β * (((x.1 p.val.1 : ℤ) : ℝ) * ((x.1 p.val.2 : ℤ) : ℝ) +
      ((x.2 p.val.1 : ℤ) : ℝ) * ((x.2 p.val.2 : ℤ) : ℝ)),
    fun x => h * (∑ i, ((x.1 i : ℤ) : ℝ) + ∑ i, ((x.2 i : ℤ) : ℝ)),
    fun x => ∑ i, ((x.1 i : ℤ) : ℝ) * ((x.2 i : ℤ) : ℝ), fun x g => ?_, fun x => rfl,
    fun x => ?_, fun x => ?_⟩
  · have e : ∀ u : Fin M → ℤˣ, ∑ i : FinPairs M, (Real.sqrt M)⁻¹ * β *
        (g i * ((u i.val.1 : ℤ) : ℝ) * ((u i.val.2 : ℤ) : ℝ)) =
        ∑ i : FinPairs M, (Real.sqrt M)⁻¹ * β * (((u i.val.1 : ℤ) : ℝ) *
          ((u i.val.2 : ℤ) : ℝ)) * g i := fun u =>
      Finset.sum_congr rfl fun i _ => by ring
    simp only [skGibbsEnergy, dotProduct, Finset.mul_sum, mul_add, add_mul]
    rw [e x.1, e x.2, Finset.sum_add_distrib]
    ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    simp only [abs_mul, abs_units_cast_eq_one, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [dotProduct]
    have hc : ((Real.sqrt M)⁻¹ * β) ^ 2 = β ^ 2 / M := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
      ring
    obtain ⟨A, hA⟩ : ∃ A : FinPairs M → ℝ, ∀ p, A p = ((x.1 p.val.1 : ℤ) : ℝ) *
        ((x.1 p.val.2 : ℤ) : ℝ) + ((x.2 p.val.1 : ℤ) : ℝ) * ((x.2 p.val.2 : ℤ) : ℝ) :=
      ⟨_, fun _ => rfl⟩
    simp only [dotProduct, ← hA]
    have hterm : ∀ p : FinPairs M, ((Real.sqrt M)⁻¹ * β * A p) * ((Real.sqrt M)⁻¹ * β * A p) ≤
        4 * (β ^ 2 / M) := fun p => by
      have h1 : |((x.1 p.val.1 : ℤ) : ℝ) * ((x.1 p.val.2 : ℤ) : ℝ)| = 1 := by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
      have h2 : |((x.2 p.val.1 : ℤ) : ℝ) * ((x.2 p.val.2 : ℤ) : ℝ)| = 1 := by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
      have h3 : |A p| ≤ 2 := by
        rw [hA]
        linarith [abs_add_le (((x.1 p.val.1 : ℤ) : ℝ) * ((x.1 p.val.2 : ℤ) : ℝ))
          (((x.2 p.val.1 : ℤ) : ℝ) * ((x.2 p.val.2 : ℤ) : ℝ))]
      have h4 : A p * A p ≤ 4 := by
        nlinarith [sq_abs (A p), abs_nonneg (A p)]
      have hβM : 0 ≤ β ^ 2 / M := by positivity
      calc ((Real.sqrt M)⁻¹ * β * A p) * ((Real.sqrt M)⁻¹ * β * A p)
          = ((Real.sqrt M)⁻¹ * β) ^ 2 * (A p * A p) := by ring
        _ ≤ (β ^ 2 / M) * 4 := by rw [hc]; exact mul_le_mul_of_nonneg_left h4 hβM
        _ = 4 * (β ^ 2 / M) := by ring
    refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_finPairs, Nat.cast_choose_two]
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [show (4 : ℝ) * (β ^ 2 / M) = 4 * β ^ 2 / M from by ring]
    rw [mul_div_assoc', div_le_iff₀ hM']
    nlinarith [sq_nonneg β, mul_nonneg (sq_nonneg β) hM'.le]

/-- The coupled partition function is the partition function of the Gaussian field `a x ⬝ᵥ g`
on pairs of configurations, tilted by `λ b`. -/
theorem skCoupledPartition_eq {M : ℕ} {β h : ℝ}
    {a : (Fin M → ℤˣ) × (Fin M → ℤˣ) → FinPairs M → ℝ} {d b : (Fin M → ℤˣ) × (Fin M → ℤˣ) → ℝ}
    (hE : ∀ x g, skGibbsEnergy M β h g x.1 + skGibbsEnergy M β h g x.2 = a x ⬝ᵥ g + d x)
    (hb : ∀ x, b x = ∑ i, ((x.1 i : ℤ) : ℝ) * ((x.2 i : ℤ) : ℝ)) (lam : ℝ)
    (g : FinPairs M → ℝ) :
    skCoupledPartition M β h lam g = ∑ x, Real.exp (a x ⬝ᵥ g + d x + lam * b x) := by
  unfold skCoupledPartition
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hE x g, hb x]

/-- `ψ_M(0) = 0`. -/
theorem skCoupledFreeEnergy_zero (M : ℕ) (β h : ℝ) : skCoupledFreeEnergy M β h 0 = 0 := by
  simp [skCoupledFreeEnergy]

/-- **Derivative of the coupled free energy** (Talagrand, after (1.286)):
`ψ_M'(λ) = 𝔼 ⟨R₁,₂⟩_λ`. -/
theorem hasDerivAt_skCoupledFreeEnergy (M : ℕ) (β h t : ℝ) :
    HasDerivAt (skCoupledFreeEnergy M β h) (skCoupledOverlapMean M β h t) t := by
  obtain ⟨a, d, b, hE, hb, -, -⟩ := exists_sk_coupled_data M β h
  have hΨ := hasDerivAt_integral_log_sum_exp_tilt a d b t
  have hfun : skCoupledFreeEnergy M β h = fun s => (M : ℝ)⁻¹ * ((∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) -
      ∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) := by
    funext s
    simp only [skCoupledFreeEnergy, skCoupledPartition_eq hE hb]
  rw [hfun]
  refine ((hΨ.sub_const _).const_mul (M : ℝ)⁻¹).congr_deriv ?_
  unfold skCoupledOverlapMean
  congr 1
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [skCoupledPartition_eq hE hb, Finset.sum_div]
  rw [← Finset.sum_product']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hE x g, hb x]
  rw [← hb x]
  ring

/-- **Convexity of the coupled free energy** (Hölder's inequality, after (1.286)). -/
theorem convexOn_skCoupledFreeEnergy (M : ℕ) (β h : ℝ) :
    ConvexOn ℝ Set.univ (skCoupledFreeEnergy M β h) := by
  obtain ⟨a, d, b, hE, hb, -, -⟩ := exists_sk_coupled_data M β h
  have hc := convexOn_integral_log_sum_exp_tilt a d b
  have hfun : skCoupledFreeEnergy M β h = fun s => (M : ℝ)⁻¹ * ((∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) -
      ∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) := by
    funext s
    simp only [skCoupledFreeEnergy, skCoupledPartition_eq hE hb]
  rw [hfun]
  refine ⟨convex_univ, fun s _ t _ θ₁ θ₂ h₁ h₂ h12 => ?_⟩
  have := hc.2 (Set.mem_univ s) (Set.mem_univ t) h₁ h₂ h12
  simp only [smul_eq_mul] at this ⊢
  have hM : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg M)
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right this
    (∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1))) hM
  have h3 : θ₁ * ((M : ℝ)⁻¹ * ((∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) -
      ∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1))) +
      θ₂ * ((M : ℝ)⁻¹ * ((∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + t * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) -
      ∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1))) =
      (M : ℝ)⁻¹ * ((θ₁ * (∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + s * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) +
      θ₂ * (∫ g : FinPairs M → ℝ,
      Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + t * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1))) -
      ∫ g : FinPairs M → ℝ, Real.log (∑ x, Real.exp (a x ⬝ᵥ g + d x + 0 * b x))
        ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)) := by
    have : θ₂ = 1 - θ₁ := by linarith
    subst this
    ring
  linarith

/-- The coupled partition function is positive. -/
theorem skCoupledPartition_pos (M : ℕ) (β h lam : ℝ) (g : FinPairs M → ℝ) :
    0 < skCoupledPartition M β h lam g :=
  Finset.sum_pos (fun _ _ => Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
    Finset.univ_nonempty

/-- **`𝔼 ⟨R₁,₂⟩ ≥ 0`.**  At `λ = 0` the numerator of the Gibbs average of the overlap is
`∑ᵢ (∑_σ σᵢ e^{-H(σ)})²`, since the two replicas are independent. -/
theorem skCoupledOverlapMean_zero_nonneg (M : ℕ) (β h : ℝ) :
    0 ≤ skCoupledOverlapMean M β h 0 := by
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg M)) (integral_nonneg fun g => ?_)
  refine div_nonneg ?_ (skCoupledPartition_pos M β h 0 g).le
  have e : ∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ, (∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) *
      Real.exp (skGibbsEnergy M β h g σ + skGibbsEnergy M β h g τ + 0 * ∑ i,
        ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) =
      ∑ i, (∑ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ) * Real.exp (skGibbsEnergy M β h g σ)) ^ 2 := by
    simp only [zero_mul, add_zero, Real.exp_add, sq, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul]
    trace_state
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [e]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Gaussian concentration of the coupled log-partition function:**
`ℙ(y ≤ |log Z_{M,λ} - 𝔼 log Z_{M,λ}|) ≤ 2 exp (-y² / (8 β² M))`. -/
theorem measureReal_abs_sub_integral_log_skCoupledPartition_ge_le (M : ℕ) (β h lam : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (Measure.pi fun _ : FinPairs M => gaussianReal 0 1).real
      {g | y ≤ |Real.log (skCoupledPartition M β h lam g) -
        ∫ g', Real.log (skCoupledPartition M β h lam g')
          ∂(Measure.pi fun _ : FinPairs M => gaussianReal 0 1)|} ≤
      2 * Real.exp (-y ^ 2 / (4 * (2 * β ^ 2 * M))) := by
  obtain ⟨a, d, b, hE, hb, -, hv⟩ := exists_sk_coupled_data M β h
  have := measureReal_abs_sub_integral_log_sum_exp_tilt_ge_le a d b hv lam hy
  simpa only [skCoupledPartition_eq hE hb] using this

end SK

end SpinGlasses
