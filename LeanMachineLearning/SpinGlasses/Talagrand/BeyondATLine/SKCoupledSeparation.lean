/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKArbitraryCenter
public import LeanMachineLearning.SpinGlasses.SKCoupledFreeEnergy
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Instability of the overlap beyond the AT line (Talagrand, Proposition 1.9.7)

Under `h ≠ 0` and `β² (1 - 2q + q̂) > 1`, Proposition 1.9.5 puts a mass `≥ δ' / M` of the
two-replica Gibbs measure at distance `≥ δ'` from any centre `x ≥ 0`.  With `x = 𝔼 ⟨R₁,₂⟩` this is
a non-negligible upper or lower tail; tilting by `exp (λ M R₁,₂)` amplifies it, Gaussian
concentration of `log Z_{M,λ}` and `log Z_{M,0}` transfers the samplewise bound to the mean, and
convexity of `ψ_M` gives `ψ_M'(λ) - ψ_M'(-λ) > δ' / 2` for each fixed `λ > 0` and `M` large.

## Main declaration

* `SpinGlasses.sk_coupled_derivative_separation`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.9.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix

namespace SpinGlasses

/-- Polynomial factors are beaten by exponentials: `M e^{-κ M} < ε` for all large `M`. -/
theorem exists_nat_forall_mul_exp_neg_lt {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → (M : ℝ) * Real.exp (-κ * M) < ε := by
  have h : Filter.Tendsto (fun M : ℕ => (M : ℝ) * Real.exp (-κ * M)) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ).comp
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  exact Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hε))

/-- The SK energy of `N + 1` spins in the explicit form used by Proposition 1.9.5. -/
theorem skGibbsEnergy_succ_eq (N : ℕ) (β h : ℝ) (g : FinPairs (N + 1) → ℝ) :
    skGibbsEnergy (N + 1) β h g = fun a : Fin (N + 1) → ℤˣ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ) := by
  funext a
  simp only [skGibbsEnergy, Nat.cast_add, Nat.cast_one]

/-- A set where `|R - x| ≥ δ'` is covered by the sets where `R ≥ x + δ'` and `R ≤ x - δ'`. -/
theorem sum_filter_abs_sub_le {α : Type*} [Fintype α] (F R : α → ℝ) (hF : ∀ y, 0 ≤ F y)
    (x δ' : ℝ) :
    ∑ y ∈ Finset.univ.filter (fun y => δ' ≤ |R y - x|), F y ≤
      ∑ y ∈ Finset.univ.filter (fun y => x + δ' ≤ R y), F y +
        ∑ y ∈ Finset.univ.filter (fun y => R y ≤ x - δ'), F y := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h1 : x + δ' ≤ R y
  · by_cases h2 : R y ≤ x - δ' <;> by_cases h3 : δ' ≤ |R y - x| <;>
      simp [h1, h2, h3, hF y]
  · by_cases h2 : R y ≤ x - δ'
    · by_cases h3 : δ' ≤ |R y - x| <;> simp [h1, h2, h3, hF y]
    · have h3 : ¬ δ' ≤ |R y - x| := by
        intro h
        rcases le_abs'.1 h with h | h <;> [exact h2 (by linarith); exact h1 (by linarith)]
      simp [h1, h2, h3]

/-- **One of the two tails carries half of the mass.**  If the averaged two-replica Gibbs mass of
`{|R₁,₂ - x| ≥ δ'}` is at least `δ' / (N + 1)`, then the averaged Gibbs mass of
`{R₁,₂ ≥ x + δ'}` or of `{R₁,₂ ≤ x - δ'}` is at least `δ' / (2 (N + 1))` (Eqs. (1.287), (1.288)). -/
theorem exists_tail_mass_ge (N : ℕ) (β h x δ' : ℝ)
    (hν : δ' / ((N : ℝ) + 1) ≤ ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (if δ' ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| then (1 : ℝ) else 0)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    (δ' / (2 * ((N : ℝ) + 1)) ≤ ∫ g : FinPairs (N + 1) → ℝ,
      (∑ y ∈ Finset.univ.filter (fun y : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) =>
          x + δ' ≤ (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (y.1 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (y.2 i : ℝ))),
        Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2)) /
        ∑ y : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
          Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2)
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ∨
    (δ' / (2 * ((N : ℝ) + 1)) ≤ ∫ g : FinPairs (N + 1) → ℝ,
      (∑ y ∈ Finset.univ.filter (fun y : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) =>
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (y.1 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (y.2 i : ℝ)) ≤ x - δ'),
        Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2)) /
        ∑ y : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
          Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2)
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  set R : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) → ℝ := fun y => (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin (N + 1) => (y.1 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (y.2 i : ℝ)) with hR
  have hmass : ∀ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (if δ' ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - x| then (1 : ℝ) else 0)
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)) =
      (∑ y ∈ Finset.univ.filter (fun y => δ' ≤ |R y - x|),
        Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2)) /
        ∑ y : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
          Real.exp (skGibbsEnergy (N + 1) β h g y.1 + skGibbsEnergy (N + 1) β h g y.2) :=
    fun g => by
    rw [← skGibbsEnergy_succ_eq N β h g]
    exact (sum_filter_exp_pair_div (skGibbsEnergy (N + 1) β h g)
      (fun u v => δ' ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (u i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (v i : ℝ)) - x|)).symm
  simp only [hmass] at hν
  have hint₁ := integrable_skCoupled_mass (N + 1) β h
    (Finset.univ.filter (fun y => x + δ' ≤ R y))
  have hint₂ := integrable_skCoupled_mass (N + 1) β h
    (Finset.univ.filter (fun y => R y ≤ x - δ'))
  have hle := integral_mono (integrable_skCoupled_mass (N + 1) β h
    (Finset.univ.filter (fun y => δ' ≤ |R y - x|))) (hint₁.add hint₂) (fun g => by
    simp only [Pi.add_apply]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (sum_filter_abs_sub_le _ R
      (fun y => (Real.exp_pos _).le) x δ') (Finset.sum_pos (fun y _ => Real.exp_pos _)
        Finset.univ_nonempty).le)
  simp only [Pi.add_apply] at hle
  rw [integral_add hint₁ hint₂] at hle
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  have : δ' / ((N : ℝ) + 1) = 2 * (δ' / (2 * ((N : ℝ) + 1))) := by
    field_simp
  linarith [hcon.1, hcon.2]

/-- **Proposition 1.9.7** (Talagrand): beyond the Almeida-Thouless line the overlap is unstable
under the coupling.  Assume `h ≠ 0`, the fixed-point identities `q = 𝔼 tanh² (β √q z + h)`,
`q̂ = 𝔼 tanh⁴ (β √q z + h)` and `β² (1 - 2 q + q̂) > 1` (Eq. (1.266)).  Then there is `δ' > 0`
(that of Eq. (1.280)) such that for every `λ > 0` and all sufficiently large `N`,
`ψ_{N+1}'(λ) - ψ_{N+1}'(-λ) > δ' / 2`, where `ψ_M'(λ) = 𝔼 ⟨R₁,₂⟩_λ` is the derivative of the
coupled free energy (`hasDerivAt_skCoupledFreeEnergy`).  The threshold depends on `λ`. -/
theorem sk_coupled_derivative_separation (β h q qhat : ℝ) (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      δ' / 2 < skCoupledOverlapMean (N + 1) β h lam - skCoupledOverlapMean (N + 1) β h (-lam) := by
  obtain ⟨δ', hδ', N₁, hind⟩ := sk_overlap_center_indicator β h q qhat hh hfix hqhat hAT
  have hβ : β ≠ 0 := by
    rintro rfl
    norm_num at hAT
  refine ⟨δ', hδ', fun lam hlam => ?_⟩
  set κ : ℝ := lam ^ 2 * δ' ^ 2 / (2048 * β ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨N₂, hN₂⟩ := exists_nat_forall_mul_exp_neg_lt hκ0 (show 0 < δ' / 16 by positivity)
  have hc0 : 0 < lam * δ' / 8 := by positivity
  obtain ⟨N₃, hN₃⟩ := exists_nat_forall_mul_exp_neg_lt hc0 (show 0 < δ' / 4 by positivity)
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂' : N₂ ≤ N + 1 := (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN).trans
    (Nat.le_succ N)
  have hN₃' : N₃ ≤ N + 1 := (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN).trans
    (Nat.le_succ N)
  have hMpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos N)
  have h₁ : 16 * ((N + 1 : ℕ) : ℝ) * Real.exp (-(lam ^ 2 * δ' ^ 2 / (2048 * β ^ 2)) *
      ((N + 1 : ℕ) : ℝ)) < δ' := by
    have := hN₂ (N + 1) hN₂'
    nlinarith
  have h₂ : Real.exp (-(|lam| * δ' / 8) * ((N + 1 : ℕ) : ℝ)) ≤ δ' / (4 * ((N + 1 : ℕ) : ℝ)) := by
    have := hN₃ (N + 1) hN₃'
    rw [abs_of_pos hlam, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨ν₂, hν₂⟩ : ∃ ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ,
      ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    ⟨fun Φ => _, fun _ => rfl⟩
  have hx0 := skCoupledOverlapMean_zero_nonneg (N + 1) β h
  have hindN := hind N hN₁' ν₂ hν₂ _ hx0
  rw [hν₂] at hindN
  have hconv := convexOn_skCoupledFreeEnergy (N + 1) β h
  have hder := hasDerivAt_skCoupledFreeEnergy (N + 1) β h
  have hzero := skCoupledFreeEnergy_zero (N + 1) β h
  have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rcases exists_tail_mass_ge N β h _ δ' hindN with hup | hdn
  · have hgt := skCoupledFreeEnergy_gt (N + 1) (Nat.succ_pos N) β h lam
      (skCoupledOverlapMean (N + 1) β h 0) δ' hβ hlam.ne' hδ' _ (fun y hy => ?_)
      (by rw [hcast]; exact hup) h₁ h₂
    · have := deriv_sub_deriv_gt_of_convex hconv hder hzero hlam (c := 3 * δ' / 4)
        (Or.inl (by rw [abs_of_pos hlam] at hgt; linarith))
      linarith
    · have hy' := (Finset.mem_filter.1 hy).2
      simp only [dotProduct] at hy'
      rw [le_inv_mul_iff₀ (by positivity)] at hy'
      rw [abs_of_pos hlam, hcast]
      nlinarith [mul_le_mul_of_nonneg_left hy' hlam.le]
  · have hgt := skCoupledFreeEnergy_gt (N + 1) (Nat.succ_pos N) β h (-lam)
      (skCoupledOverlapMean (N + 1) β h 0) δ' hβ (neg_ne_zero.2 hlam.ne') hδ' _
      (fun y hy => ?_) (by rw [hcast]; exact hdn) (by rw [neg_sq]; exact h₁)
      (by rw [abs_neg]; exact h₂)
    · have := deriv_sub_deriv_gt_of_convex hconv hder hzero hlam (c := 3 * δ' / 4)
        (Or.inr (by rw [abs_neg, abs_of_pos hlam] at hgt; linarith))
      linarith
    · have hy' := (Finset.mem_filter.1 hy).2
      simp only [dotProduct] at hy'
      rw [inv_mul_le_iff₀ (by positivity)] at hy'
      rw [abs_neg, abs_of_pos hlam, hcast]
      nlinarith [mul_le_mul_of_nonneg_left hy' hlam.le]

end SpinGlasses
