/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDisorderDerivative
public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPPotential
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaDiffDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityBounds

/-!
# Algebraic preparations for the Gaussian integration by parts on the smart path

Talagrand Section 2.2, Proposition 2.2.3. The Gaussian integration by parts itself is not
formalized yet; this module contains the algebra it will use.

* `smartPath_sqrt_scaling_prefactor_eq`, `smartPath_auxiliary_prefactor_eq_neg`: the prefactors
  that cancel the `√s` and `√(1 - s)` denominators of the energy derivative (2.27);
* `replicaPairCombination_eq_half_replica_covariance_combination` and
  `replicaPairCombination_lastSpinKernel`: the two-replica combination of (2.24)--(2.25) as half of
  the four-term covariance combination of the cavity method.

The objects of the path (`smartPathEnergy`, `smartPathBase`, ...) are in `SmartPathModel.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- Square-root scaling prefactor of the Gaussian integration by parts on the smart path:
`(1 / (2 * √(N + 1))) * (1 / √s) * √(s / (N + 1)) = 1 / (2 * (N + 1))` for `s > 0`. With `s = t`
this is the quenched-disorder prefactor, with `s = 1 - t` the auxiliary-spin one. -/
theorem smartPath_sqrt_scaling_prefactor_eq {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (1 / Real.sqrt s) *
      Real.sqrt (s / (N + 1 : ℕ)) =
    1 / (2 * (N + 1 : ℝ)) := by
  push_cast
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [Real.sqrt_div hs.le]
  have h1 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have h2 : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h3 := Real.mul_self_sqrt hN.le
  field_simp
  nlinarith [h3]

/-- Simplification of the auxiliary spin prefactor: the product
`(1 / (2 * √(N + 1))) * (- 1 / √(1 - t)) * √((1 - t) / (N + 1))` simplifies to
`- 1 / (2 * (N + 1))`, cancelling the `√(1 - t)` denominator. -/
theorem smartPath_auxiliary_prefactor_eq_neg {N : ℕ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (- (1 / Real.sqrt (1 - t))) *
      Real.sqrt ((1 - t) / (N + 1 : ℕ)) =
    - (1 / (2 * (N + 1 : ℝ))) := by
  have := smartPath_sqrt_scaling_prefactor_eq (N := N) (sub_pos.2 ht.2)
  linear_combination -this

/-- Connection with the 4-term replica covariance combination from `SKCavityBounds.lean`:
for any kernel with constant diagonal, `replicaPairCombination` is exactly half of the 4-term
combination. -/
theorem replicaPairCombination_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairCombination U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairCombination]
  ring

/-- For the last-spin interaction kernel `lastSpinKernel x y = ε_x ε_y` the diagonal is `1`
(`σ_{N+1}² = 1`) and the kernel is symmetric, so `replicaPairCombination` is half of the four-term
replica covariance combination, with no hypothesis on the replicas. Note: `[LinearOrder R]` is
only used to order the pairs `r < r'` without double counting. -/
theorem replicaPairCombination_lastSpinKernel {N M : ℕ} {R : Type*} [Fintype R] [LinearOrder R]
    (τ : Option (Option R) → SmartPathState N M) :
    replicaPairCombination (lastSpinKernel (N := N) (M := M)) τ =
      ((∑ r : R, ∑ r' : R, lastSpinKernel (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, lastSpinKernel (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * lastSpinKernel (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            lastSpinKernel (τ (some none)) (τ none)) / 2 :=
  replicaPairCombination_eq_half_replica_covariance_combination _ 1 lastSpinKernel_self
    lastSpinKernel_comm τ

/-- **Second derivative of a replica average in a linear coupling** (the model-free core of the
`E'_Y` term of Proposition 2.2.3). Let `X` be a bounded observable of one spin with `X² = C`. The
replica difference, with the replica average over `|R| + 1` replicas, of the replica difference of
`F · X_i` against `c X` is twice `c` times the two-fresh-replica average of `F` against the pair
combination of the kernel `X ⊗ X`:
`∑_i cov(F X_i, ∑ c X) - n cov(F X_*, ∑ c X) = 2 c ⟨F · replicaPairCombination (X ⊗ X)⟩`.
The proof moves everything to `|R| + 2` replicas (`replicaDiff_eq_integral`), uses
`replicaPairCombination_eq_half_replica_covariance_combination`, and exchanges the two fresh
replicas (`integral_replica_swap_fresh`). -/
theorem replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage
    {α R : Type*} [MeasurableSpace α] [Fintype R] [LinearOrder R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ}
    (hFb : ∀ σ, |F σ| ≤ M) (X : α → ℝ) (hX : Measurable X) {B : ℝ} (hXb : ∀ a, |X a| ≤ B)
    (C c : ℝ) (hC : ∀ a, X a * X a = C) :
    replicaDiffWith (fun G => replicaDiff ν G (fun a => c * X a)) F X =
      2 * c * replicaPairAverage ν F (fun a b => X a * X b) := by
  classical
  set n : ℝ := (Fintype.card R : ℝ) with hn
  set P2 : Measure (Option (Option R) → α) := Measure.pi fun _ => ν with hP2
  set f : (Option (Option R) → α) → ℝ := fun σ => F fun j => σ (some (some j)) with hf
  set S : (Option (Option R) → α) → ℝ := fun σ => ∑ r, X (σ (some (some r))) with hS
  set Xa : (Option (Option R) → α) → ℝ := fun σ => X (σ (some none)) with hXa
  set Xb : (Option (Option R) → α) → ℝ := fun σ => X (σ none) with hXb'
  set W : (Option (Option R) → α) → ℝ := fun σ => ∑ o : Option R, c * X (σ (some o)) -
    (n + 1) * (c * X (σ none)) with hW
  -- measurability and bounds of the atoms
  have hXm (k : Option (Option R)) : Measurable fun σ : Option (Option R) → α => X (σ k) :=
    hX.comp (measurable_pi_apply k)
  have hXbd (k : Option (Option R)) : ∃ K, ∀ σ : Option (Option R) → α, |X (σ k)| ≤ K :=
    ⟨B, fun σ => hXb _⟩
  have hfm : Measurable f := hF.comp (by fun_prop)
  have hfbd : ∃ K, ∀ σ, |f σ| ≤ K := ⟨M, fun σ => hFb _⟩
  have hSm : Measurable S := Finset.measurable_sum _ fun r _ => hXm _
  have hSbd : ∃ K, ∀ σ, |S σ| ≤ K := exists_abs_le_sum _ fun r _ => hXbd _
  have hcXm (k : Option (Option R)) : Measurable fun σ : Option (Option R) → α => c * X (σ k) :=
    (hXm k).const_mul c
  have hcXbd (k : Option (Option R)) : ∃ K, ∀ σ : Option (Option R) → α, |c * X (σ k)| ≤ K :=
    exists_abs_le_mul (exists_abs_le_const c) (hXbd k)
  have hWm : Measurable W :=
    (Finset.measurable_sum _ fun o _ => hcXm _).sub ((hcXm _).const_mul _)
  have hWbd : ∃ K, ∀ σ, |W σ| ≤ K :=
    exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hcXbd _)
      (exists_abs_le_mul (exists_abs_le_const _) (hcXbd _))
  have hint (g : (Option (Option R) → α) → ℝ) (hg : Measurable g) (hb : ∃ K, ∀ σ, |g σ| ≤ K) :
      Integrable g P2 := by
    obtain ⟨K, hK⟩ := hb
    exact integrable_of_measurable_bound hg hK
  -- step 1: each replica difference over `Option R` is one integral over `Option (Option R)`
  have key1 (i : Option R) :
      replicaDiff ν (fun τ : Option R → α => F (fun j => τ (some j)) * X (τ i))
          (fun a => c * X a) =
        ∫ σ, f σ * X (σ (some i)) * W σ ∂P2 := by
    have hGm : Measurable fun τ : Option R → α => F (fun j => τ (some j)) * X (τ i) :=
      (hF.comp (by fun_prop)).mul (hX.comp (measurable_pi_apply i))
    rw [replicaDiff_eq_integral ν _ hGm (M := M * B) (fun τ => by
        rw [abs_mul]
        exact mul_le_mul (hFb _) (hXb _) (abs_nonneg _)
          ((abs_nonneg _).trans (hFb fun j => τ (some j))))
      (fun a => c * X a) (hX.const_mul c) (B := |c| * B) (fun a => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb a) (abs_nonneg _))]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [W, f, Fintype.card_option, Nat.cast_succ, hn]
  simp only [replicaDiffWith]
  rw [Finset.sum_congr rfl fun i _ => key1 (some i), key1 none]
  -- step 2: one integral
  have hI (k : Option (Option R)) : Integrable (fun σ => f σ * X (σ k) * W σ) P2 :=
    hint _ ((hfm.mul (hXm k)).mul hWm) (exists_abs_le_mul (exists_abs_le_mul hfbd (hXbd k)) hWbd)
  have hcomb : (∑ i : R, ∫ σ, f σ * X (σ (some (some i))) * W σ ∂P2) -
      n * ∫ σ, f σ * X (σ (some none)) * W σ ∂P2 =
      ∫ σ, (∑ i : R, f σ * X (σ (some (some i))) * W σ -
        n * (f σ * X (σ (some none)) * W σ)) ∂P2 := by
    rw [integral_sub (integrable_finsetSum _ fun i _ => hI _) ((hI _).const_mul n),
      integral_finsetSum _ fun i _ => hI _, integral_const_mul]
  rw [hcomb]
  -- step 3: swap the two fresh replicas
  have hK : Measurable fun p : α × α => X p.1 * X p.2 :=
    (hX.comp measurable_fst).mul (hX.comp measurable_snd)
  have hswap : ∫ σ, f σ * (S σ * Xb σ) ∂P2 = ∫ σ, f σ * (S σ * Xa σ) ∂P2 := by
    have hr (k : Option (Option R)) (r : R) : Integrable
        (fun σ => f σ * (X (σ (some (some r))) * X (σ k))) P2 :=
      hint _ (hfm.mul ((hXm _).mul (hXm k)))
        (exists_abs_le_mul hfbd (exists_abs_le_mul (hXbd _) (hXbd _)))
    simp only [S, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun r _ => hr none r, integral_finsetSum _ fun r _ => hr (some none) r]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact integral_replica_swap_fresh ν F hF (K := fun a b => X a * X b) hK r
  -- step 4: the pair combination of `X ⊗ X` and the pointwise identity
  have hXam : Measurable Xa := hXm _
  have hXbm : Measurable Xb := hXm _
  have hXabd : ∃ K, ∀ σ, |Xa σ| ≤ K := hXbd _
  have hXbbd : ∃ K, ∀ σ, |Xb σ| ≤ K := hXbd _
  set A : (Option (Option R) → α) → ℝ := fun σ => f σ * (S σ * S σ - 2 * n * (S σ * Xa σ) -
    n * C + n * (n + 1) * (Xa σ * Xb σ)) with hA
  have hAm : Measurable A :=
    hfm.mul ((((hSm.mul hSm).sub (((hSm.mul hXam).const_mul _))).sub measurable_const).add
      ((hXam.mul hXbm).const_mul _))
  have hAbd : ∃ K, ∀ σ, |A σ| ≤ K :=
    exists_abs_le_mul hfbd (exists_abs_le_add (exists_abs_le_sub (exists_abs_le_sub
      (exists_abs_le_mul hSbd hSbd) (exists_abs_le_mul (exists_abs_le_const _)
        (exists_abs_le_mul hSbd hXabd))) (exists_abs_le_const _))
      (exists_abs_le_mul (exists_abs_le_const _) (exists_abs_le_mul hXabd hXbbd)))
  have hcombpt (σ : Option (Option R) → α) :
      f σ * replicaPairCombination (fun a b => X a * X b) σ = A σ / 2 := by
    rw [replicaPairCombination_eq_half_replica_covariance_combination (fun a b => X a * X b) C
      hC (fun a b => mul_comm _ _) σ]
    have hSS : (∑ r : R, ∑ r' : R, X (σ (some (some r))) * X (σ (some (some r')))) =
        S σ * S σ := by
      simp only [S, Finset.sum_mul_sum]
    have hSa : (∑ r : R, X (σ (some (some r))) * X (σ (some none))) = S σ * Xa σ := by
      simp only [S, Xa, Finset.sum_mul]
    simp only [A, hSS, hSa, hC, hn]
    ring
  -- step 5: assemble
  have hpt (σ : Option (Option R) → α) :
      (∑ i : R, f σ * X (σ (some (some i))) * W σ -
        n * (f σ * X (σ (some none)) * W σ)) =
      c * A σ + ((n + 1) * c * (f σ * (S σ * Xa σ)) - (n + 1) * c * (f σ * (S σ * Xb σ))) := by
    have hXa2 : Xa σ * Xa σ = C := hC _
    have hW' : W σ = c * (Xa σ + S σ) - (n + 1) * (c * Xb σ) := by
      simp only [W, Fintype.sum_option, ← Finset.mul_sum, S, Xa, Xb]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hW']
    simp only [A]
    change f σ * S σ * _ - _ = _
    linear_combination (-(n * c * f σ)) * hXa2
  have h1 : Integrable (fun σ => f σ * (S σ * Xa σ)) P2 :=
    hint _ (hfm.mul (hSm.mul hXam)) (exists_abs_le_mul hfbd (exists_abs_le_mul hSbd hXabd))
  have h2 : Integrable (fun σ => f σ * (S σ * Xb σ)) P2 :=
    hint _ (hfm.mul (hSm.mul hXbm)) (exists_abs_le_mul hfbd (exists_abs_le_mul hSbd hXbbd))
  have hA' : Integrable A P2 := hint A hAm hAbd
  have hg : Integrable (fun σ => (n + 1) * c * (f σ * (S σ * Xa σ)) -
      (n + 1) * c * (f σ * (S σ * Xb σ))) P2 := (h1.const_mul _).sub (h2.const_mul _)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add (hA'.const_mul c) hg,
    integral_sub (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hswap]
  have hpair : replicaPairAverage ν F (fun a b => X a * X b) = (∫ σ, A σ ∂P2) / 2 := by
    unfold replicaPairAverage
    rw [← integral_div]
    exact integral_congr_ae (ae_of_all _ hcombpt)
  rw [hpair]
  ring

/-- Derivative of the replica difference of the last spin in the last field `y`, in terms of
the two-fresh-replica average (the `E'_Y` Stein step of Proposition 2.2.3 for fixed `y`). -/
theorem hasDerivAt_replicaDiff_lastSpin_lastField {N M : ℕ} {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    (y : ℝ) :
    HasDerivAt (fun r => replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r)))
        F (fun x => ((x.1.2 : ℤ) : ℝ)))
      (2 * Real.sqrt (1 - t) * replicaPairAverage
        ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel) y := by
  set q := Real.sqrt (1 - t) with hq
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
  have hεb (x : SmartPathState N M) : |((x.1.2 : ℤ) : ℝ)| ≤ 1 := (abs_units_cast_eq_one _).le
  have hE' : ∀ (r : ℝ) (x : SmartPathState N M),
      |q * ((x.1.2 : ℤ) : ℝ)| ≤ q := fun r x => by
    rw [abs_mul, abs_units_cast_eq_one, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hbd := hasDerivAt_replicaDiff_tilted_replicaDiff
    (μ := smartPathBase N M) (E := fun r => smartPathEnergy u t (ω₀, r))
    (E' := fun _ x => q * ((x.1.2 : ℤ) : ℝ)) (t := y) (s := Metric.ball y 1)
    (Metric.ball_mem_nhds y one_pos)
    (fun r _ => measurable_smartPathEnergy_slice hu t (ω₀, r))
    (by fun_prop) (B := M * B + q * (|y| + 1)) (fun r hr x => by
      refine (perceptron_smart_path_energy_le hB t (ω₀, r) x).trans ?_
      have : |r| ≤ |y| + 1 := by
        have := abs_sub_abs_le_abs_sub r y
        have h2 := Metric.mem_ball.1 hr
        rw [Real.dist_eq] at h2
        linarith
      have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg (1 - t))
      linarith)
    (b := fun _ => q) (integrable_const _) (fun r _ x => hE' r x)
    (fun x r _ => hasDerivAt_smartPathEnergy_lastField u t ω₀ x r) hF hFb hε hεb
    (integrable_of_measurable_bound (by fun_prop) (M := q) (hE' y))
  have := hν y
  have hbr := replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F hF hFb
    (fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ)) hε hεb 1 q
    (fun x => by rw [← sq]; exact units_cast_sq _)
  exact hbr ▸ hbd

/-- **The `E'_Y` term of Proposition 2.2.3 (Stein in the last field).** For the last field
`y ∼ 𝒩(0, v)` (`v = 0` allowed), the `y`-average of the replica difference of the energy
derivative `E'_Y` is `-v` times the `y`-average of the two-fresh-replica average of the last-spin
kernel `ε_x ε_y`, the other disorder `ω₀ = (g, a)` being fixed. -/
theorem integral_replicaDiff_smartPathEnergyDerivY {N M : ℕ} {R : Type*} [Fintype R]
    [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Measurable u)
    {B : ℝ} (hB : ∀ x, u x ≤ B) (v : ℝ≥0) (ω₀ : (Fin M → Fin N → ℝ) × (Fin M → ℝ))
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    ∫ y, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
        (smartPathEnergyDerivY t (ω₀, y)) ∂(gaussianReal 0 v) =
      -(v : ℝ) * ∫ y, replicaPairAverage
        ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel
        ∂(gaussianReal 0 v) := by
  set q := Real.sqrt (1 - t) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  have hν (r : ℝ) : IsProbabilityMeasure
      ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, r))) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hB (ω₀, r) t
  set Gf : ℝ → ℝ := fun y => replicaDiff
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
    (fun x => ((x.1.2 : ℤ) : ℝ)) with hGf
  set PA : ℝ → ℝ := fun y => replicaPairAverage
    ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F lastSpinKernel with hPA
  have hderiv (y : ℝ) : HasDerivAt Gf (2 * q * PA y) y :=
    hasDerivAt_replicaDiff_lastSpin_lastField hu hB ω₀ F hF hFb y
  have hGc : Continuous Gf := continuous_iff_continuousAt.2 fun y => (hderiv y).continuousAt
  have hPAm : Measurable fun y => 2 * q * PA y := by
    have : (fun y => 2 * q * PA y) = deriv Gf := funext fun y => (hderiv y).deriv.symm
    rw [this]
    exact measurable_deriv Gf
  -- uniform bounds
  have hGb (y : ℝ) : |Gf y| ≤ C * (Fintype.card R + Fintype.card R) := by
    have := hν y
    have hε : Measurable fun x : SmartPathState N M => ((x.1.2 : ℤ) : ℝ) := by fun_prop
    rw [hGf]
    dsimp only
    rw [replicaDiff_eq_integral _ F hF hFb _ hε (B := 1) (fun x => (abs_units_cast_eq_one _).le)]
    refine abs_integral_le_of_forall_abs_le _ fun σ => ?_
    rw [abs_mul]
    refine mul_le_mul (hFb _) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hFb fun j => σ (some j)))
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simp [abs_units_cast_eq_one]
    · rw [abs_mul, abs_units_cast_eq_one, mul_one, Nat.abs_cast]
  have hPAb : ∃ K, ∀ y, |2 * q * PA y| ≤ K := by
    obtain ⟨K, hK⟩ := exists_abs_replicaPairCombination_le (R := R)
      (U := lastSpinKernel (N := N) (M := M)) ⟨1, fun a b => by
        unfold lastSpinKernel
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]⟩
    refine ⟨2 * q * (C * K), fun y => ?_⟩
    have := hν y
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hPA]
    dsimp only
    unfold replicaPairAverage
    refine abs_integral_le_of_forall_abs_le _ fun τ => ?_
    rw [abs_mul]
    exact mul_le_mul (hFb _) (hK τ) (abs_nonneg _)
      ((abs_nonneg _).trans (hFb fun j => τ (some (some j))))
  obtain ⟨K, hK⟩ := hPAb
  have hxF : Integrable (fun y => y * Gf y) (gaussianReal 0 v) := by
    have := (IsGaussian.integrable_id (μ := gaussianReal 0 v)).bdd_mul_of_abs_le
      (F := Gf) hGc.aestronglyMeasurable (ae_of_all _ hGb)
    simpa only [mul_comm, id] using this
  have hF' : Integrable (fun y => 2 * q * PA y) (gaussianReal 0 v) :=
    integrable_of_measurable_bound hPAm hK
  have hStein := integral_id_mul_gaussianReal_eq v hderiv hxF hF'
  have hpt (y : ℝ) : replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t (ω₀, y))) F
      (smartPathEnergyDerivY t (ω₀, y)) = (-(1 / (2 * q)) * y) * Gf y := by
    have hfun : smartPathEnergyDerivY t (ω₀, y) =
        fun x => (-(1 / (2 * q)) * y) * ((x.1.2 : ℤ) : ℝ) := by
      funext x
      simp only [smartPathEnergyDerivY, hq]
      ring
    rw [hfun]
    exact replicaDiff_const_mul _ F _ _
  simp_rw [hpt]
  have hmul : ∫ y, (-(1 / (2 * q)) * y) * Gf y ∂(gaussianReal 0 v) =
      -(1 / (2 * q)) * ∫ y, y * Gf y ∂(gaussianReal 0 v) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [hmul, hStein, integral_const_mul]
  field_simp

end SpinGlasses
