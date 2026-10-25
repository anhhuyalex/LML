/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKLastSpinApprox
public import LeanMachineLearning.SpinGlasses.GibbsCavityDeviation
public import LeanMachineLearning.SpinGlasses.SKCorrelationDecay
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration

/-!
# Adding a spin barely moves an old magnetization (Talagrand, Lemma 1.7.4, Eq. (1.186))

For `4 β₀² < 1` and the `(N+1)`-spin SK system at `|β| ≤ β₀`, with `β_- = β √(N/(N+1))`,
`𝔼 (⟨σ_i⟩ - ⟨σ_i⟩_-)² ≤ K / (N+1)` for every old site `i < N`
(`SpinGlasses.sk_old_spin_cavity_approx`).

The proof has three steps.

1. *Cavity formula.*  `⟨σ_i⟩ - ⟨σ_i⟩_- = ⟨σ̇_i cosh L⟩_- / ⟨cosh L⟩_-` with `⟨cosh L⟩_- ≥ 1`
   (`integral_comp_castSucc_sub_integral`), so the square is at most `⟨σ̇_i cosh L⟩_-²`.
2. *Model-independent estimate.*  The Gaussian average over the new couplings and the sum over the
   sites of this square is at most `N Λ (17/2) E⟨(R - q)²⟩` (`sum_integral_gibbs_cosh_sq_le`).
3. *Site symmetry.*  The disorder average of the square does not depend on the site
   (`integral_sum_sum_centered_perm`), so each site gets `1/N` of the sum, and the overlap moment
   is `K / N` (`sk_overlap_moment_le_of_exp_unif`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- Dividing by a number at least `1` does not increase a square. -/
theorem sq_div_le_sq_of_one_le {x d : ℝ} (hd : 1 ≤ d) : (x / d) ^ 2 ≤ x ^ 2 := by
  have hd0 : 0 < d := lt_of_lt_of_le one_pos hd
  rw [div_pow]
  exact div_le_self (sq_nonneg x) (one_le_pow₀ hd)

/-- **Cavity formula for an old magnetization.**  In the `(N+1)`-spin SK system the Gibbs mean of
an old spin differs from its mean in the `N`-spin system at `β_- = β √(N/(N+1))` by
`⟨σ̇_i cosh L⟩_- / ⟨cosh L⟩_-`, where `L ρ = β (N+1)^{-1/2} ∑_j y_j ρ_j + h` and `y` are the
couplings of the new spin. -/
theorem sk_old_spin_deviation_eq {N : ℕ} (hN : 0 < N) (β h : ℝ) (g : FinPairs (N + 1) → ℝ)
    (i : Fin N) :
    (∫ σ : Fin (N + 1) → ℤˣ, ((σ i.castSucc : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))) -
      ∫ a, ((a i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N
        (β * Real.sqrt ((N : ℝ) / (N + 1))) h (skCavityDisorderEquiv N g).1)) =
    (∫ a, (((a i : ℤ) : ℝ) - ∫ a', ((a' i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h (skCavityDisorderEquiv N g).1))) *
        Real.cosh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
          ∑ j, (skCavityDisorderEquiv N g).2 j * ((a j : ℤ) : ℝ) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h (skCavityDisorderEquiv N g).1))) /
      ∫ a, Real.cosh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
          ∑ j, (skCavityDisorderEquiv N g).2 j * ((a j : ℤ) : ℝ) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h (skCavityDisorderEquiv N g).1)) := by
  set A : (Fin N → ℤˣ) → ℝ := skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h
    (skCavityDisorderEquiv N g).1 with hA
  set L : (Fin N → ℤˣ) → ℝ := fun ρ => (Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
    ∑ j, (skCavityDisorderEquiv N g).2 j * ((ρ j : ℤ) : ℝ) + h with hL
  have hE : skGibbsEnergy (N + 1) β h g = fun σ : Fin (N + 1) → ℤˣ =>
      A (fun i => σ i.castSucc) + ((σ (Fin.last N) : ℤ) : ℝ) * L (fun i => σ i.castSucc) :=
    funext fun σ => by
      rw [skGibbsEnergy_succ_cavity hN β h g σ, dotProduct_sk_beta_minus N β hN]
  rw [hE]
  exact integral_comp_castSucc_sub_integral N A L (fun ρ => ((ρ i : ℤ) : ℝ))

section Symmetric

variable {N : ℕ} (b h c : ℝ)
  (S : Fin N → (FinPairs N → ℝ) → ℝ)
  (hS : ∀ i go, S i go = ∫ y : Fin N → ℝ, (∫ a, (((a i : ℤ) : ℝ) -
          ∫ a', ((a' i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N b h go))) *
        Real.cosh (c * ∑ j, y j * ((a j : ℤ) : ℝ) + h)
          ∂(Measure.count.tilted (skGibbsEnergy N b h go))) ^ 2
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1))
  (w : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hw : ∀ go a, w go a = Real.exp (skGibbsEnergy N b h go a) /
      ∑ x, Real.exp (skGibbsEnergy N b h go x))
  (K : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
  (hK : ∀ a a', K a a' = (Real.cosh (2 * h) *
        Real.exp (c ^ 2 * (N + ∑ i, ((a i : ℤ) : ℝ) * ((a' i : ℤ) : ℝ))) +
        Real.exp (c ^ 2 * (N - ∑ i, ((a i : ℤ) : ℝ) * ((a' i : ℤ) : ℝ)))) / 2)

include hw in
/-- The Gibbs weights of the `N`-spin SK system are a site-symmetric random Gibbs state. -/
theorem sk_cavity_weights_symmetric :
    (∀ go a, 0 ≤ w go a) ∧ (∀ go, ∑ a, w go a = 1) ∧ (∀ a, Measurable fun go => w go a) ∧
    ∀ π : Equiv.Perm (Fin N), ∃ φ : (FinPairs N → ℝ) → (FinPairs N → ℝ),
      MeasurePreserving φ (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      ∀ go a, w (φ go) a = w go (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a) := by
  have hw' : w = fun go a => Real.exp (skGibbsEnergy N b h go a) /
      ∑ x, Real.exp (skGibbsEnergy N b h go x) := funext fun go => funext (hw go)
  subst hw'
  exact sk_gibbsWeight_siteSymmetric b h (fun go a => skGibbsEnergy N b h go a) fun _ _ => rfl

include hS hw hK

/-- **The averaged cavity deviation as a double Gibbs sum.**  `S i go` is the Gaussian average
of the squared Gibbs average `⟨σ̇_i cosh L_y⟩²` of the `N`-spin system with couplings `go`; it is
the double sum of the weights `w go` against the kernel `K`. -/
theorem sk_cavity_sq_eq_sum (i : Fin N) (go : FinPairs N → ℝ) :
    S i go = ∑ a, ∑ a', w go a * w go a' *
      ((((a i : ℤ) : ℝ) - ∑ x, w go x * ((x i : ℤ) : ℝ)) *
        (((a' i : ℤ) : ℝ) - ∑ x, w go x * ((x i : ℤ) : ℝ))) * K a a' := by
  rw [hS, integral_gibbs_cosh_sq_centered (fun (i : Fin N) (a : Fin N → ℤˣ) => ((a i : ℤ) : ℝ))
    (fun i a => units_cast_sq (a i)) (skGibbsEnergy N b h go) c h i]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  simp only [hw, hK]

/-- The averaged cavity deviation is integrable in the old disorder. -/
theorem integrable_sk_cavity_sq (i : Fin N) :
    Integrable (S i) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  obtain ⟨hw0, hw1, hwm, -⟩ := sk_cavity_weights_symmetric b h w hw
  have hc : Continuous fun v : (Fin N → ℤˣ) → ℝ => ∑ a, ∑ a', v a * v a' *
      ((((a i : ℤ) : ℝ) - ∑ x, v x * ((x i : ℤ) : ℝ)) *
        (((a' i : ℤ) : ℝ) - ∑ x, v x * ((x i : ℤ) : ℝ))) * K a a' := by fun_prop
  have := integrable_comp_weights (P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    hw0 hw1 hwm hc
  refine this.congr (ae_of_all _ fun go => ?_)
  exact (sk_cavity_sq_eq_sum b h c S hS w hw K hK i go).symm

/-- **Site symmetry of the averaged cavity deviation.**  The disorder average of `S i` does not
depend on the site `i`. -/
theorem integral_sk_cavity_sq_perm (i j : Fin N) :
    ∫ go, S j go ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      ∫ go, S i go ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  obtain ⟨-, -, hwm, hsym⟩ := sk_cavity_weights_symmetric b h w hw
  have hact : ∀ (π : Equiv.Perm (Fin N)) (k : Fin N) (a : Fin N → ℤˣ),
      (((Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a) k : ℤ) : ℝ) = ((a (π k) : ℤ) : ℝ) :=
    fun π k a => by simp
  have hKinv : ∀ (π : Equiv.Perm (Fin N)) (a a' : Fin N → ℤˣ),
      K (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a) (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a') =
        K a a' := fun π a a' => by
    have hs : ∑ k, (((Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a) k : ℤ) : ℝ) *
        (((Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) a') k : ℤ) : ℝ) =
        ∑ k, ((a k : ℤ) : ℝ) * ((a' k : ℤ) : ℝ) := by
      simp_rw [hact]
      exact Equiv.sum_comp π fun k => ((a k : ℤ) : ℝ) * ((a' k : ℤ) : ℝ)
    rw [hK, hK, hs]
  have key := integral_sum_sum_centered_perm
    (P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    (ξ := fun (k : Fin N) (a : Fin N → ℤˣ) => ((a k : ℤ) : ℝ)) (w := w) hwm
    (fun π => Equiv.arrowCongr π.symm (Equiv.refl ℤˣ)) hact K hKinv hsym (Equiv.swap i j) i
  simp only [Equiv.swap_apply_left] at key
  refine (integral_congr_ae (ae_of_all _ fun go =>
    sk_cavity_sq_eq_sum b h c S hS w hw K hK j go)).trans ?_
  refine Eq.trans key ?_
  exact (integral_congr_ae (ae_of_all _ fun go =>
    sk_cavity_sq_eq_sum b h c S hS w hw K hK i go)).symm

/-- **The averaged cavity deviation at one site is of order `1/N`.**  If the field coefficient
satisfies `N c² ≤ β₀²` and the overlap moment of the `N`-spin system is at most `K' / N`, then
`𝔼 S i ≤ Λ₀ (17/2) K' / N` with `Λ₀ = β₀² e^{2β₀²} (cosh (2h) + 1) / 2`, for every site `i`. -/
theorem integral_sk_cavity_sq_le (hN : 0 < N) {β₀ : ℝ} (hB : (N : ℝ) * c ^ 2 ≤ β₀ ^ 2) (q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {K' : ℝ}
    (hOM : ∫ go, overlapMoment (fun (i : Fin N) (a : Fin N → ℤˣ) => ((a i : ℤ) : ℝ))
      (skGibbsEnergy N b h go) q 1 ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
        K' / N) (i : Fin N) :
    ∫ go, S i go ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      β₀ ^ 2 * Real.exp (2 * β₀ ^ 2) * (Real.cosh (2 * h) + 1) / 2 * (17 / 2) * (K' / N) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set Λ₀ : ℝ := β₀ ^ 2 * Real.exp (2 * β₀ ^ 2) * (Real.cosh (2 * h) + 1) / 2 with hΛ₀
  have hc2 : 0 ≤ (N : ℝ) * c ^ 2 := by positivity
  have hΛ₀0 : 0 ≤ Λ₀ := by
    have := Real.cosh_pos (2 * h)
    positivity
  have hΛle : (N : ℝ) * c ^ 2 * Real.exp (2 * ((N : ℝ) * c ^ 2)) * (Real.cosh (2 * h) + 1) / 2 ≤
      Λ₀ := by
    have hc := Real.cosh_pos (2 * h)
    have h1 : Real.exp (2 * ((N : ℝ) * c ^ 2)) ≤ Real.exp (2 * β₀ ^ 2) :=
      Real.exp_le_exp.2 (by linarith)
    rw [hΛ₀]
    gcongr
  set ξ : Fin N → (Fin N → ℤˣ) → ℝ := fun i a => ((a i : ℤ) : ℝ) with hξ
  have hξ2 : ∀ i a, ξ i a ^ 2 = 1 := fun i a => units_cast_sq (a i)
  have hOMnn : ∀ go, 0 ≤ overlapMoment ξ (skGibbsEnergy N b h go) q 1 := fun go =>
    integral_nonneg fun τ => Even.pow_nonneg ⟨1, by ring⟩ _
  have hOMint : Integrable (fun go => overlapMoment ξ (skGibbsEnergy N b h go) q 1) P :=
    integrable_overlapMoment_skGibbsEnergy N b h q 1
  -- pointwise bound for the sum over the sites
  have hpt : ∀ go, ∑ j, S j go ≤ N * Λ₀ * (17 / 2) * overlapMoment ξ (skGibbsEnergy N b h go) q 1 :=
    fun go => by
    have hhub := sum_integral_gibbs_cosh_sq_le ξ hξ2 hN (skGibbsEnergy N b h go) c h q hq
    simp_rw [hS] at *
    calc _ ≤ _ := hhub
      _ ≤ N * Λ₀ * (17 / 2) * overlapMoment ξ (skGibbsEnergy N b h go) q 1 := by
        have := hOMnn go
        have h2 : (N : ℝ) * ((N : ℝ) * c ^ 2 * Real.exp (2 * ((N : ℝ) * c ^ 2)) *
            (Real.cosh (2 * h) + 1) / 2) ≤ N * Λ₀ := mul_le_mul_of_nonneg_left hΛle hN0.le
        have h3 := mul_le_mul_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 17 / 2)
        exact mul_le_mul_of_nonneg_right h3 this
  have hsumint : Integrable (fun go => ∑ j, S j go) P :=
    integrable_finsetSum _ fun j _ => integrable_sk_cavity_sq b h c S hS w hw K hK j
  have hint_sum : ∑ j, ∫ go, S j go ∂P = ∫ go, ∑ j, S j go ∂P :=
    (integral_finsetSum _ fun j _ => integrable_sk_cavity_sq b h c S hS w hw K hK j).symm
  have hall : ∑ j, ∫ go, S j go ∂P = N * ∫ go, S i go ∂P := by
    rw [Finset.sum_congr rfl fun j _ => integral_sk_cavity_sq_perm b h c S hS w hw K hK i j,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbound : ∫ go, ∑ j, S j go ∂P ≤ N * Λ₀ * (17 / 2) * (K' / N) := by
    calc ∫ go, ∑ j, S j go ∂P
        ≤ ∫ go, N * Λ₀ * (17 / 2) * overlapMoment ξ (skGibbsEnergy N b h go) q 1 ∂P :=
          integral_mono hsumint (hOMint.const_mul _) hpt
      _ = N * Λ₀ * (17 / 2) * ∫ go, overlapMoment ξ (skGibbsEnergy N b h go) q 1 ∂P :=
          integral_const_mul _ _
      _ ≤ N * Λ₀ * (17 / 2) * (K' / N) :=
          mul_le_mul_of_nonneg_left hOM (by positivity)
  have : (N : ℝ) * ∫ go, S i go ∂P ≤ N * (Λ₀ * (17 / 2) * (K' / N)) := by
    calc (N : ℝ) * ∫ go, S i go ∂P = ∫ go, ∑ j, S j go ∂P := by rw [← hall, hint_sum]
      _ ≤ N * Λ₀ * (17 / 2) * (K' / N) := hbound
      _ = N * (Λ₀ * (17 / 2) * (K' / N)) := by ring
  exact le_of_mul_le_mul_left this hN0

end Symmetric

/-- **Talagrand, Lemma 1.7.4, Eq. (1.186).**  For `4 β₀² < 1` and `h` there is `K` such that for all
`|β| ≤ β₀`, `N ≥ 1` and every old site `i < N`,
`𝔼 (⟨σ_i⟩ - ⟨σ_i⟩_-)² ≤ K / (N+1)`, where `⟨·⟩` is the Gibbs measure of the `(N+1)`-spin system and
`⟨·⟩_-` that of the first `N` spins with the old couplings at `β_- = β √(N/(N+1))`.  The old
couplings are the first component of `skCavityDisorderEquiv N g`. -/
theorem sk_old_spin_cavity_approx (β₀ : ℝ) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, |β| ≤ β₀ → ∀ N : ℕ, 0 < N → ∀ i : Fin N,
      ∫ g : FinPairs (N + 1) → ℝ,
        ((∫ σ : Fin (N + 1) → ℤˣ, ((σ i.castSucc : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))) -
          ∫ a, ((a i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N
            (β * Real.sqrt ((N : ℝ) / (N + 1))) h (skCavityDisorderEquiv N g).1))) ^ 2
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) := by
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp_unif β₀ hβ₀' 1
  set Λ₀ : ℝ := β₀ ^ 2 * Real.exp (2 * β₀ ^ 2) * (Real.cosh (2 * h) + 1) / 2 with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by
    have := Real.cosh_pos (2 * h)
    positivity
  refine ⟨17 * Λ₀ * K' + 1, by positivity, fun β hβ N hN i => ?_⟩
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt ((N : ℝ) / (N + 1)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one (by positivity)).mpr (by linarith))
  have hβm : |β * Real.sqrt ((N : ℝ) / (N + 1))| ≤ β₀ := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc _ ≤ |β| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ β₀ := by rw [mul_one]; exact hβ
  have hb2 : (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 ≤ β₀ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hβm 2
  have hB : (N : ℝ) * ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) ^ 2 ≤ β₀ ^ 2 := by
    have hsq : ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) ^ 2 = β ^ 2 / ((N : ℝ) + 1) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]; ring
    rw [hsq]
    have hβ2 : β ^ 2 ≤ β₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
    calc (N : ℝ) * (β ^ 2 / ((N : ℝ) + 1)) = β ^ 2 * ((N : ℝ) / ((N : ℝ) + 1)) := by ring
      _ ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).mpr (by linarith)) (sq_nonneg _)
      _ ≤ β₀ ^ 2 := by rw [mul_one]; exact hβ2
  obtain ⟨q, hqI, hq⟩ := exists_fixedPoint (β * Real.sqrt ((N : ℝ) / (N + 1))) h
  have hOM : ∫ go, overlapMoment (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
      (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go) q 1
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K' / N := by
    have := hK' _ h q hq.symm hb2 N hN
    rw [pow_one] at this
    exact this
  -- the abstract objects
  obtain ⟨S, hS⟩ : ∃ S : Fin N → (FinPairs N → ℝ) → ℝ, ∀ j go, S j go =
      ∫ y : Fin N → ℝ, (∫ a, (((a j : ℤ) : ℝ) - ∫ a', ((a' j : ℤ) : ℝ) ∂(Measure.count.tilted
          (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go))) *
        Real.cosh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ l, y l * ((a l : ℤ) : ℝ) + h)
          ∂(Measure.count.tilted (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go))) ^ 2
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ go a, w go a =
      Real.exp (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go a) /
        ∑ x, Real.exp (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go x) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ, ∀ a a', K a a' =
      (Real.cosh (2 * h) * Real.exp (((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) ^ 2 *
          (N + ∑ l, ((a l : ℤ) : ℝ) * ((a' l : ℤ) : ℝ))) +
        Real.exp (((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) ^ 2 *
          (N - ∑ l, ((a l : ℤ) : ℝ) * ((a' l : ℤ) : ℝ)))) / 2 := ⟨_, fun _ _ => rfl⟩
  have hSle := integral_sk_cavity_sq_le (β * Real.sqrt ((N : ℝ) / (N + 1))) h
    ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) S hS w hw K hK hN hB q hqI hOM i
  -- transport to the product of the old and the new disorder
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1
  let F : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun v =>
    ((∫ a, (((a i : ℤ) : ℝ) - ∫ a', ((a' i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h v.1))) *
        Real.cosh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ j, v.2 j * ((a j : ℤ) : ℝ) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h v.1))) /
      ∫ a, Real.cosh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ j, v.2 j * ((a j : ℤ) : ℝ) + h)
        ∂(Measure.count.tilted (skGibbsEnergy N
          (β * Real.sqrt ((N : ℝ) / (N + 1))) h v.1))) ^ 2
  have hF0 : ∀ v, 0 ≤ F v := fun v => sq_nonneg _
  have hFS : ∀ go, ∫ y, F (go, y) ∂Q ≤ S i go := fun go => by
    rw [hS i go]
    refine integral_mono_of_nonneg (ae_of_all _ fun y => hF0 _) ?_ (ae_of_all _ fun y => ?_)
    · exact integrable_sq_integral_gibbs_cosh
        (fun (j : Fin N) (a : Fin N → ℤˣ) => ((a j : ℤ) : ℝ))
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go)
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β) h
        (fun a => ((a i : ℤ) : ℝ) - ∫ a', ((a' i : ℤ) : ℝ) ∂(Measure.count.tilted
          (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h go)))
    · exact sq_div_le_sq_of_one_le (one_le_integral_cosh _ _)
  calc _ = ∫ g : FinPairs (N + 1) → ℝ, F (skCavityDisorderEquiv N g)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
        refine integral_congr_ae (ae_of_all _ fun g => ?_)
        simp only [F]
        rw [sk_old_spin_deviation_eq hN β h g i]
    _ = ∫ v, F v ∂(P.prod Q) := (measurePreserving_skCavityDisorderEquiv N).integral_comp' F
    _ ≤ ∫ go, ∫ y, F (go, y) ∂Q ∂P := integral_prod_le_integral_integral_of_nonneg hF0
    _ ≤ ∫ go, S i go ∂P := integral_mono_of_nonneg
        (ae_of_all _ fun go => integral_nonneg fun y => hF0 _)
        (integrable_sk_cavity_sq _ h _ S hS w hw K hK i) (ae_of_all _ hFS)
    _ ≤ Λ₀ * (17 / 2) * (K' / N) := by simpa only [hΛ₀, mul_assoc] using hSle
    _ ≤ (17 * Λ₀ * K' + 1) / ((N : ℝ) + 1) := by
        have h1 : K' / N ≤ 2 * K' / ((N : ℝ) + 1) := by
          rw [div_le_div_iff₀ hN0 (by positivity)]
          have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith
        calc Λ₀ * (17 / 2) * (K' / N) ≤ Λ₀ * (17 / 2) * (2 * K' / ((N : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 17 * Λ₀ * K' / ((N : ℝ) + 1) := by ring
          _ ≤ (17 * Λ₀ * K' + 1) / ((N : ℝ) + 1) :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
