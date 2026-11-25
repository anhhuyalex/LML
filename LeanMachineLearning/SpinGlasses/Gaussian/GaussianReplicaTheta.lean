/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianReplicaRatioHessian
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedHolder
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaComparison

/-!
# Extra replicas for the kernel sums of the cavity derivative

For a finite spin set, an observable `f` of `n` replicas and a kernel `K`, the average of
`f ∑_k G_k K(σ_r, k)` over `n` replicas is the average of `f K(σ_r, σ_*)` over `n + 1` replicas,
and the average of `f ∑_{l,k} G_l G_k K(l, k)` is the average of `f K(σ_*, σ_{**})` over `n + 2`
replicas. These identify the terms of `Θ` (Talagrand's (2.55)--(2.58)) with replica sums.

* `SpinGlasses.integral_pi_option_kernel`, `SpinGlasses.integral_pi_option_option_kernel`.
-/

@[expose] public section

open MeasureTheory

namespace SpinGlasses

variable {κ R : Type*} [Fintype κ] [Fintype R] [DecidableEq κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

omit [Fintype κ] [DecidableEq κ] in
/-- **One extra replica.** For a probability law `ν` on a finite spin set,
`⟨f K(σ_r, σ_*)⟩_{n+1} = ⟨f ∫ K(σ_r, b) dν(b)⟩_n`. -/
theorem integral_pi_option_kernel [Finite κ] (ν : Measure κ) [IsProbabilityMeasure ν]
    (f : (R → κ) → ℝ) (r : R) (K : κ → κ → ℝ) :
    ∫ σ : Option R → κ, f (fun i => σ (some i)) * K (σ (some r)) (σ none)
        ∂(Measure.pi fun _ : Option R => ν) =
      ∫ σ : R → κ, f σ * ∫ b, K (σ r) b ∂ν ∂(Measure.pi fun _ : R => ν) := by
  classical
  have := Fintype.ofFinite κ
  have hexp : ∀ (σ : Option R → κ), f (fun i => σ (some i)) * K (σ (some r)) (σ none) =
      ∑ a : κ, (f (fun i => σ (some i)) * if σ (some r) = a then (1 : ℝ) else 0) *
        K a (σ none) := fun σ => by
    simp [mul_ite]
  have hexp' : ∀ (σ : R → κ), f σ * ∫ b, K (σ r) b ∂ν =
      ∑ a : κ, (f σ * if σ r = a then (1 : ℝ) else 0) * ∫ b, K a b ∂ν := fun σ => by
    simp [mul_ite]
  simp_rw [hexp, hexp']
  rw [integral_finsetSum _ fun a _ => Integrable.of_finite,
    integral_finsetSum _ fun a _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_pi_fresh_replica_mul ν (e := Option.some) (Option.some_injective R)
    (r := none) (fun i => Option.some_ne_none i)
    (fun ρ => f ρ * if ρ r = a then (1 : ℝ) else 0) (K a)
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable,
    integral_mul_const]

omit [Fintype κ] [DecidableEq κ] in
/-- **Two extra replicas.** `⟨f K(σ_*, σ_{**})⟩_{n+2} = ⟨f⟩_n ∬ K dν dν`. -/
theorem integral_pi_option_option_kernel [Finite κ] (ν : Measure κ) [IsProbabilityMeasure ν]
    (f : (R → κ) → ℝ) (K : κ → κ → ℝ) :
    ∫ σ : Option (Option R) → κ, f (fun i => σ (some (some i))) * K (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => ν) =
      (∫ σ : R → κ, f σ ∂(Measure.pi fun _ : R => ν)) * ∫ a, ∫ b, K a b ∂ν ∂ν := by
  have h1 := integral_pi_option_kernel (R := Option R) ν
    (fun τ : Option R → κ => f (fun i => τ (some i))) none K
  rw [h1]
  exact integral_pi_fresh_replica_mul ν (e := Option.some) (Option.some_injective R)
    (r := none) (fun i => Option.some_ne_none i) f (fun a => ∫ b, K a b ∂ν)
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable

section Pointwise

variable [DecidableEq R] (c : κ → κ → ℝ) (G : κ → ℝ) (σ : R → κ)

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- **`Θ` as a sum over distinct replica pairs, pointwise.** With `N_l = ∑_r 1[σ_r = l]`,
`X_l = N_l - n G_l` and `n = |R|`,
`∑_{l,k} c l k [X_l X_k - n G_l (1[l=k] - G_k)] - ∑_l c l l X_l`
`= ∑_{r ≠ r'} c(σ_r, σ_{r'}) - n ∑_r ∑_k G_k (c(σ_r, k) + c(k, σ_r))`
`  + n (n + 1) ∑_{l,k} G_l G_k c l k`. -/
theorem theta_eq_pair_sum :
    (∑ l, ∑ k, c l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) - Fintype.card R * G l) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) - Fintype.card R * G k) -
        Fintype.card R * G l * ((if l = k then 1 else 0) - G k)) -
      ∑ l, c l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) - Fintype.card R * G l)) =
    ∑ r, ∑ r', (if r = r' then 0 else c (σ r) (σ r')) -
      Fintype.card R * ∑ r, ∑ k, G k * (c (σ r) k + c k (σ r)) +
      Fintype.card R * (Fintype.card R + 1) * ∑ l, ∑ k, G l * G k * c l k := by
  have hF1 : ∀ g : κ → ℝ, ∑ l, g l * (∑ r, if σ r = l then (1 : ℝ) else 0) = ∑ r, g (σ r) :=
    fun g => by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
  have hNN : ∑ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) *
      (∑ r, if σ r = k then (1 : ℝ) else 0)) = ∑ r, ∑ r', c (σ r) (σ r') := by
    have h1 : ∀ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) *
        (∑ r, if σ r = k then (1 : ℝ) else 0)) =
        (∑ r', c l (σ r')) * (∑ r, if σ r = l then (1 : ℝ) else 0) := fun l => by
      rw [← hF1 (c l), Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [h1]
    exact hF1 (fun l => ∑ r', c l (σ r'))
  have hB2 : ∑ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) * G k) =
      ∑ r, ∑ k, G k * c (σ r) k := by
    have h1 : ∀ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) * G k) =
        (∑ k, G k * c l k) * (∑ r, if σ r = l then (1 : ℝ) else 0) := fun l => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [h1]
    exact hF1 (fun l => ∑ k, G k * c l k)
  have hB1 : ∑ l, ∑ k, c l k * (G l * (∑ r, if σ r = k then (1 : ℝ) else 0)) =
      ∑ r, ∑ l, G l * c l (σ r) := by
    rw [Finset.sum_comm]
    have h1 : ∀ k, ∑ l, c l k * (G l * (∑ r, if σ r = k then (1 : ℝ) else 0)) =
        (∑ l, G l * c l k) * (∑ r, if σ r = k then (1 : ℝ) else 0) := fun k => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [h1]
    exact hF1 (fun k => ∑ l, G l * c l k)
  have hD : ∑ l, c l l * (∑ r, if σ r = l then (1 : ℝ) else 0) = ∑ r, c (σ r) (σ r) :=
    hF1 (fun l => c l l)
  have hδ : ∑ l, ∑ k, c l k * (G l * if l = k then (1 : ℝ) else 0) = ∑ l, c l l * G l :=
    Finset.sum_congr rfl fun l _ => by
      rw [Finset.sum_eq_single l (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp
  have hpairs : ∑ r, ∑ r', (if r = r' then 0 else c (σ r) (σ r')) =
      ∑ r, ∑ r', c (σ r) (σ r') - ∑ r, c (σ r) (σ r) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : ∀ r' : R, (if r = r' then (0 : ℝ) else c (σ r) (σ r')) =
        c (σ r) (σ r') - if r = r' then c (σ r) (σ r') else 0 := fun r' => by
      split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  set n : ℝ := (Fintype.card R : ℝ) with hn
  have e1 : ∑ l, ∑ k, c l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) - n * G l) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) - n * G k) -
        n * G l * ((if l = k then 1 else 0) - G k)) =
      ∑ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) *
          (∑ r, if σ r = k then (1 : ℝ) else 0)) -
        n * ∑ l, ∑ k, c l k * ((∑ r, if σ r = l then (1 : ℝ) else 0) * G k) -
        n * ∑ l, ∑ k, c l k * (G l * (∑ r, if σ r = k then (1 : ℝ) else 0)) +
        (n * n + n) * ∑ l, ∑ k, c l k * (G l * G k) -
        n * ∑ l, ∑ k, c l k * (G l * if l = k then (1 : ℝ) else 0) := by
    have hmul : ∀ (m : ℝ) (g : κ → κ → ℝ), m * ∑ l, ∑ k, g l k = ∑ l, ∑ k, m * g l k :=
      fun m g => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
    simp only [hmul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ l, c l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) - n * G l) =
      ∑ l, c l l * (∑ r, if σ r = l then (1 : ℝ) else 0) - n * ∑ l, c l l * G l := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∑ r, ∑ k, G k * (c (σ r) k + c k (σ r)) =
      ∑ r, ∑ k, G k * c (σ r) k + ∑ r, ∑ k, G k * c k (σ r) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have e4 : ∑ r, ∑ l, G l * c l (σ r) = ∑ r, ∑ k, G k * c k (σ r) := rfl
  have e5 : ∑ l, ∑ k, G l * G k * c l k = ∑ l, ∑ k, c l k * (G l * G k) :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2, hNN, hB2, hB1, hD, hδ, hpairs, e3, e5]
  rw [← e4]
  ring

end Pointwise

section Integrated

variable [Nonempty κ] [DecidableEq R]

/-- **`⟨f Θ⟩` as a sum of replica averages.** For the Gibbs law `ν = count.tilted E` of a finite
spin set, with `G l = ν {l}`, the average of `f Θ` over `n` replicas is
`∑_{r ≠ r'} ⟨f c(σ_r, σ_{r'})⟩_n - n ∑_r (⟨f c(σ_r, σ_*)⟩_{n+1} + ⟨f c(σ_*, σ_r)⟩_{n+1})`
`+ n (n + 1) ⟨f c(σ_*, σ_{**})⟩_{n+2}`: the replica sum over `ℓ ≠ ℓ'` with the extra replicas
`n + 1, n + 2` of Talagrand's (2.55)--(2.58). -/
theorem integral_theta_eq_replicas (E : κ → ℝ) (c : κ → κ → ℝ) (f : (R → κ) → ℝ) :
    ∫ σ : R → κ, (∑ l, ∑ k, c l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {l}) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {k}) -
        Fintype.card R * (Measure.count.tilted E).real {l} *
          ((if l = k then 1 else 0) - (Measure.count.tilted E).real {k})) -
      ∑ l, c l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {l})) * f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted E) =
    ∑ r, ∑ r', (if r = r' then 0 else ∫ σ : R → κ, c (σ r) (σ r') * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted E)) -
      Fintype.card R * ∑ r, (∫ σ : Option R → κ, f (fun i => σ (some i)) *
          c (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted E) +
        ∫ σ : Option R → κ, f (fun i => σ (some i)) * c (σ none) (σ (some r))
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted E)) +
      Fintype.card R * (Fintype.card R + 1) *
        ∫ σ : Option (Option R) → κ, f (fun i => σ (some (some i))) * c (σ (some none)) (σ none)
          ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted E) := by
  have hmean : ∀ g : κ → ℝ, ∫ b, g b ∂(Measure.count.tilted E) =
      ∑ k, (Measure.count.tilted E).real {k} * g k := fun g => by
    rw [integral_count_tilted]
    exact Finset.sum_congr rfl fun k _ => by rw [real_count_tilted_singleton]
  have hθ := fun σ : R → κ => theta_eq_pair_sum c (fun l => (Measure.count.tilted E).real {l}) σ
  simp only [hθ]
  have hP1 : ∫ σ : R → κ, (∑ r, ∑ r', (if r = r' then (0 : ℝ) else c (σ r) (σ r'))) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted E) =
      ∑ r, ∑ r', (if r = r' then 0 else ∫ σ : R → κ, c (σ r) (σ r') * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted E)) := by
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum _ fun r' _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun r' _ => ?_
    by_cases h : r = r' <;> simp [h]
  have hP2 : ∫ σ : R → κ, (∑ r, ∑ k, (Measure.count.tilted E).real {k} *
        (c (σ r) k + c k (σ r))) * f σ ∂(Measure.pi fun _ : R => Measure.count.tilted E) =
      ∑ r, (∫ σ : Option R → κ, f (fun i => σ (some i)) * c (σ (some r)) (σ none)
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted E) +
        ∫ σ : Option R → κ, f (fun i => σ (some i)) * c (σ none) (σ (some r))
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted E)) := by
    have hr : ∀ r, ∫ σ : R → κ, (∑ k, (Measure.count.tilted E).real {k} *
          (c (σ r) k + c k (σ r))) * f σ ∂(Measure.pi fun _ : R => Measure.count.tilted E) =
        ∫ σ : R → κ, f σ * ∫ b, c (σ r) b ∂(Measure.count.tilted E)
          ∂(Measure.pi fun _ : R => Measure.count.tilted E) +
        ∫ σ : R → κ, f σ * ∫ b, c b (σ r) ∂(Measure.count.tilted E)
          ∂(Measure.pi fun _ : R => Measure.count.tilted E) := fun r => by
      rw [← integral_add Integrable.of_finite Integrable.of_finite]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      simp only [hmean, mul_add, Finset.sum_add_distrib]
      ring
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun k _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_pi_option_kernel (Measure.count.tilted E) f r c,
      integral_pi_option_kernel (Measure.count.tilted E) f r (fun a b => c b a), ← hr r]
    exact integral_congr_ae (ae_of_all _ fun σ => by simp [Finset.sum_mul])
  have hP3 : ∫ σ : R → κ, (∑ l, ∑ k, (Measure.count.tilted E).real {l} *
        (Measure.count.tilted E).real {k} * c l k) * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted E) =
      ∫ σ : Option (Option R) → κ, f (fun i => σ (some (some i))) * c (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted E) := by
    rw [integral_pi_option_option_kernel (Measure.count.tilted E) f c, integral_const_mul]
    simp only [hmean]
    rw [mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : ∀ σ : R → κ, ((∑ r, ∑ r', (if r = r' then (0 : ℝ) else c (σ r) (σ r'))) -
        Fintype.card R * ∑ r, ∑ k, (Measure.count.tilted E).real {k} * (c (σ r) k + c k (σ r)) +
        Fintype.card R * (Fintype.card R + 1) * ∑ l, ∑ k, (Measure.count.tilted E).real {l} *
          (Measure.count.tilted E).real {k} * c l k) * f σ =
      (∑ r, ∑ r', (if r = r' then (0 : ℝ) else c (σ r) (σ r'))) * f σ -
        Fintype.card R * ((∑ r, ∑ k, (Measure.count.tilted E).real {k} *
          (c (σ r) k + c k (σ r))) * f σ) +
        Fintype.card R * (Fintype.card R + 1) * ((∑ l, ∑ k, (Measure.count.tilted E).real {l} *
          (Measure.count.tilted E).real {k} * c l k) * f σ) := fun σ => by ring
  simp_rw [hsplit]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const_mul, hP1, hP2, hP3]

/-- **Absolute bound for `⟨fΘ⟩` by pair averages.** If `|c| ≤ m` pointwise then
`|⟨fΘ⟩_n| ≤ ∑_{r ≠ r'} ⟨|f| m(σ_r, σ_{r'})⟩_n
  + n ∑_r (⟨|f| m(σ_r, σ_*)⟩_{n+1} + ⟨|f| m(σ_*, σ_r)⟩_{n+1})
  + n (n + 1) ⟨|f| m(σ_*, σ_{**})⟩_{n+2}`. -/
theorem abs_integral_theta_le (E : κ → ℝ) (c m : κ → κ → ℝ) (hcm : ∀ a b, |c a b| ≤ m a b)
    (f : (R → κ) → ℝ) :
    |∫ σ : R → κ, (∑ l, ∑ k, c l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {l}) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {k}) -
        Fintype.card R * (Measure.count.tilted E).real {l} *
          ((if l = k then 1 else 0) - (Measure.count.tilted E).real {k})) -
      ∑ l, c l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted E).real {l})) * f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted E)| ≤
    ∑ r, ∑ r', (if r = r' then 0 else ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
        ∂(Measure.pi fun _ : R => Measure.count.tilted E)) +
      Fintype.card R * ∑ r, (∫ σ : Option R → κ, |f (fun i => σ (some i))| *
          m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted E) +
        ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted E)) +
      Fintype.card R * (Fintype.card R + 1) *
        ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
          m (σ (some none)) (σ none)
          ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted E) := by
  rw [integral_theta_eq_replicas]
  have hbd : ∀ {ι : Type _} [Fintype ι] (μ : Measure (ι → κ)) [IsFiniteMeasure μ]
      (g h : (ι → κ) → ℝ), (∀ σ, |g σ| ≤ h σ) → |∫ σ, g σ ∂μ| ≤ ∫ σ, h σ ∂μ :=
    fun μ _ g h hgh => (abs_integral_le_integral_abs (μ := μ) (f := g)).trans
      (integral_mono (Integrable.of_finite (f := fun σ => |g σ|)) (Integrable.of_finite (f := h))
        (fun σ => hgh σ))
  have hn0 : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
  have b1 : ∀ r r' : R, |∫ σ : R → κ, c (σ r) (σ r') * f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted E)| ≤
      ∫ σ : R → κ, |f σ| * m (σ r) (σ r') ∂(Measure.pi fun _ : R => Measure.count.tilted E) :=
    fun r r' => hbd _ _ _ fun σ => by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hcm _ _) (abs_nonneg _)
  have b2 : ∀ r : R, |∫ σ : Option R → κ, f (fun i => σ (some i)) * c (σ (some r)) (σ none)
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted E)| ≤
      ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ (some r)) (σ none)
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted E) := fun r =>
    hbd _ _ _ fun σ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcm _ _) (abs_nonneg _)
  have b3 : ∀ r : R, |∫ σ : Option R → κ, f (fun i => σ (some i)) * c (σ none) (σ (some r))
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted E)| ≤
      ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted E) := fun r =>
    hbd _ _ _ fun σ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcm _ _) (abs_nonneg _)
  have b4 : |∫ σ : Option (Option R) → κ, f (fun i => σ (some (some i))) *
        c (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted E)| ≤
      ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
        m (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted E) :=
    hbd _ _ _ fun σ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcm _ _) (abs_nonneg _)
  refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
  · refine Finset.abs_sum_le_sum_of_abs_le _ fun r _ => ?_
    refine Finset.abs_sum_le_sum_of_abs_le _ fun r' _ => ?_
    by_cases h : r = r'
    · simp [h]
    · simpa [h] using b1 r r'
  · rw [abs_mul, abs_of_nonneg hn0]
    refine mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_of_abs_le _ fun r _ =>
      (abs_add_le _ _).trans (add_le_add (b2 r) (b3 r))) hn0
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left b4 (by positivity)

omit [Nonempty κ] [DecidableEq R] [DecidableEq κ] [Fintype R] in
/-- **Constants under the replica average.** The kernel sums with coefficients outside the replica
integral are the replica average of the kernel sum: for any finite measure `μ` on the replicas,
`∑_{l,k} c_{lk} ⟨T_{lk} f⟩ - ∑_l c_{ll} ⟨X_l f⟩ = ⟨(∑_{l,k} c_{lk} T_{lk} - ∑_l c_{ll} X_l) f⟩`. -/
theorem sum_mul_integral_eq_integral_sum [Finite R] (μ : Measure (R → κ)) [IsFiniteMeasure μ]
    (c : κ → κ → ℝ) (T : κ → κ → (R → κ) → ℝ) (X : κ → (R → κ) → ℝ) (f : (R → κ) → ℝ) :
    ∑ l, ∑ k, c l k * ∫ σ, T l k σ * f σ ∂μ - ∑ l, c l l * ∫ σ, X l σ * f σ ∂μ =
      ∫ σ, (∑ l, ∑ k, c l k * T l k σ - ∑ l, c l l * X l σ) * f σ ∂μ := by
  symm
  simp only [sub_mul, Finset.sum_mul, mul_assoc]
  simp (disch := first | exact Integrable.of_finite |
      (intro _ _; exact Integrable.of_finite)) only [integral_sub, integral_finsetSum,
    integral_const_mul]

end Integrated

section Holder

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty κ]

omit [DecidableEq κ] [Fintype κ] in
/-- **Hölder for a pair average of a random Gibbs state.** For a replica family `ι` containing the
`R` replicas of an observable `F` (via an injection `e`) and two distinct replicas `i ≠ j`,
`𝔼⟨|F| m(σ_i, σ_j)⟩ ≤ (𝔼⟨|F|^p⟩)^{1/p} (𝔼⟨m(σ_1, σ_2)^r⟩)^{1/r}` with the pair average reduced to
two replicas. -/
theorem integral_integral_pair_holder [Finite κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → κ → ℝ) (hE : ∀ a, Measurable fun ω => E ω a) {e : R → ι} (he : Function.Injective e)
    {i j : ι} (hij : i ≠ j) (F : (R → κ) → ℝ) (m : κ → κ → ℝ) (hm : ∀ a b, 0 ≤ m a b) {p r : ℝ}
    (hpr : p.HolderConjugate r) :
    ∫ ω, ∫ σ : ι → κ, |F (fun s => σ (e s))| * m (σ i) (σ j)
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) ∂μ ≤
      (∫ ω, ∫ σ : R → κ, |F σ| ^ p ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ) ^
        (1 / p) *
      (∫ ω, ∫ τ : Fin 2 → κ, m (τ 0) (τ 1) ^ r
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) ∂μ) ^ (1 / r) := by
  have key := integral_integral_mul_le_Lp_mul_Lq μ
    (fun ω => Measure.pi fun _ : ι => Measure.count.tilted (E ω)) hpr
    (A := fun σ : ι → κ => |F (fun s => σ (e s))|) (B := fun σ : ι → κ => m (σ i) (σ j))
    (fun _ => abs_nonneg _) (fun σ => hm _ _)
    (measurable_integral_pi_count_tilted (Θ := fun _ τ => |F (fun s => τ (e s))| ^ p) hE
      fun _ => measurable_const).aestronglyMeasurable
    (measurable_integral_pi_count_tilted (Θ := fun _ τ => m (τ i) (τ j) ^ r) hE
      fun _ => measurable_const).aestronglyMeasurable
  have e1 : ∀ ω, ∫ σ : ι → κ, |F (fun s => σ (e s))| ^ p
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) =
      ∫ σ : R → κ, |F σ| ^ p ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) := fun ω =>
    integral_pi_comp_injective (Measure.count.tilted (E ω)) he (fun σ => |F σ| ^ p)
      (measurable_of_finite _).aestronglyMeasurable
  have hρ : Function.Injective (![i, j] : Fin 2 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij]
  have e2 : ∀ ω, ∫ σ : ι → κ, m (σ i) (σ j) ^ r
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) =
      ∫ τ : Fin 2 → κ, m (τ 0) (τ 1) ^ r
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) := fun ω =>
    integral_pi_comp_injective (Measure.count.tilted (E ω)) hρ (fun τ => m (τ 0) (τ 1) ^ r)
      (measurable_of_finite _).aestronglyMeasurable
  simpa only [e1, e2] using key

omit [DecidableEq κ] [Fintype κ] in
/-- A bounded replica observable has an integrable average over a measurable random Gibbs state. -/
theorem integrable_integral_pi_count_tilted' [Finite κ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Ω → κ → ℝ) (hE : ∀ a, Measurable fun ω => E ω a) {ι' : Type*} [Fintype ι']
    (g : (ι' → κ) → ℝ) :
    Integrable (fun ω => ∫ σ, g σ ∂(Measure.pi fun _ : ι' => Measure.count.tilted (E ω))) μ := by
  classical
  have := Fintype.ofFinite κ
  have hm : Measurable fun ω => ∫ σ, g σ ∂(Measure.pi fun _ : ι' => Measure.count.tilted (E ω)) :=
    measurable_integral_pi_count_tilted (Θ := fun _ τ => g τ) hE fun _ => measurable_const
  refine Integrable.of_bound (C := ∑ σ, |g σ|) hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_integral_pi_count_tilted_le _ fun σ =>
    Finset.single_le_sum (f := fun σ => |g σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)

omit [DecidableEq κ] [Fintype κ] in
/-- **Hölder for a pair average against `α d + β`.** For `α ≥ 0` and a nonnegative kernel `d`,
`𝔼⟨|F| (α d(σ_i,σ_j) + β)⟩ ≤ α (𝔼⟨|F|^p⟩)^{1/p} (𝔼⟨d^r⟩)^{1/r} + β 𝔼⟨|F|⟩`. -/
theorem integral_integral_pair_holder_affine [Finite κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → κ → ℝ) (hE : ∀ a, Measurable fun ω => E ω a) {e : R → ι} (he : Function.Injective e)
    {i j : ι} (hij : i ≠ j) (F : (R → κ) → ℝ) (d : κ → κ → ℝ) (hd : ∀ a b, 0 ≤ d a b)
    {α β : ℝ} (hα : 0 ≤ α) {p r : ℝ} (hpr : p.HolderConjugate r) :
    ∫ ω, ∫ σ : ι → κ, |F (fun s => σ (e s))| * (α * d (σ i) (σ j) + β)
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) ∂μ ≤
      α * ((∫ ω, ∫ σ : R → κ, |F σ| ^ p ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))
          ∂μ) ^ (1 / p) *
        (∫ ω, ∫ τ : Fin 2 → κ, d (τ 0) (τ 1) ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) ∂μ) ^ (1 / r)) +
      β * ∫ ω, ∫ σ : R → κ, |F σ| ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ := by
  classical
  have hsplit : ∀ ω, ∫ σ : ι → κ, |F (fun s => σ (e s))| * (α * d (σ i) (σ j) + β)
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) =
      α * ∫ σ : ι → κ, |F (fun s => σ (e s))| * d (σ i) (σ j)
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) +
      β * ∫ σ : R → κ, |F σ| ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) := fun ω => by
    have h1 : ∫ σ : ι → κ, |F (fun s => σ (e s))|
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) =
        ∫ σ : R → κ, |F σ| ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) :=
      integral_pi_comp_injective (Measure.count.tilted (E ω)) he (fun σ => |F σ|)
        (measurable_of_finite _).aestronglyMeasurable
    rw [← h1, ← integral_const_mul, ← integral_const_mul, ← integral_add Integrable.of_finite
      Integrable.of_finite]
    exact integral_congr_ae (ae_of_all _ fun σ => by ring)
  simp_rw [hsplit]
  have i1 : Integrable (fun ω => ∫ σ : ι → κ, |F (fun s => σ (e s))| * d (σ i) (σ j)
      ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω))) μ :=
    integrable_integral_pi_count_tilted' μ E hE _
  have i2 : Integrable (fun ω => ∫ σ : R → κ, |F σ|
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) μ :=
    integrable_integral_pi_count_tilted' μ E hE _
  rw [integral_add (i1.const_mul α) (i2.const_mul β), integral_const_mul, integral_const_mul]
  have hH := integral_integral_pair_holder μ E hE he hij F d hd hpr
  have hH' : ∫ ω, ∫ σ : ι → κ, |F (fun s => σ (e s))| * d (σ i) (σ j)
        ∂(Measure.pi fun _ : ι => Measure.count.tilted (E ω)) ∂μ ≤
      (∫ ω, ∫ σ : R → κ, |F σ| ^ p ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))
          ∂μ) ^ (1 / p) *
        (∫ ω, ∫ τ : Fin 2 → κ, d (τ 0) (τ 1) ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) ∂μ) ^ (1 / r) := hH
  exact add_le_add (mul_le_mul_of_nonneg_left hH' hα) le_rfl

omit [DecidableEq κ] in
/-- **The disorder-averaged bound for `𝔼⟨fΘ⟩`.** If the kernels satisfy `|c ω a b| ≤ α d a b + β`
(`d ≥ 0`, `α, β ≥ 0`), then
`|𝔼⟨fΘ_{c ω}⟩| ≤ (4 n² + n) (α (𝔼⟨|f|^p⟩)^{1/p} (𝔼⟨d(σ_1,σ_2)^r⟩)^{1/r} + β 𝔼⟨|f|⟩)`,
the replica estimate behind Talagrand's (2.40). -/
theorem abs_integral_integral_theta_le [DecidableEq κ] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Ω → κ → ℝ) (hE : ∀ a, Measurable fun ω => E ω a)
    (c : Ω → κ → κ → ℝ) (d : κ → κ → ℝ) (hd : ∀ a b, 0 ≤ d a b) {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hcm : ∀ ω a b, |c ω a b| ≤ α * d a b + β) (f : (R → κ) → ℝ) {p r : ℝ}
    (hpr : p.HolderConjugate r) :
    |∫ ω, ∫ σ : R → κ, (∑ l, ∑ k, c ω l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {l}) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {k}) -
        Fintype.card R * (Measure.count.tilted (E ω)).real {l} *
          ((if l = k then 1 else 0) - (Measure.count.tilted (E ω)).real {k})) -
      ∑ l, c ω l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {l})) * f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ| ≤
    (4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
      (α * ((∫ ω, ∫ σ : R → κ, |f σ| ^ p ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))
          ∂μ) ^ (1 / p) *
        (∫ ω, ∫ τ : Fin 2 → κ, d (τ 0) (τ 1) ^ r
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) ∂μ) ^ (1 / r)) +
      β * ∫ ω, ∫ σ : R → κ, |f σ| ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ) := by
  classical
  set U : ℝ := α * ((∫ ω, ∫ σ : R → κ, |f σ| ^ p
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ) ^ (1 / p) *
    (∫ ω, ∫ τ : Fin 2 → κ, d (τ 0) (τ 1) ^ r
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E ω)) ∂μ) ^ (1 / r)) +
    β * ∫ ω, ∫ σ : R → κ, |f σ| ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ
    with hU
  have hU0 : 0 ≤ U := by
    refine add_nonneg (mul_nonneg hα (mul_nonneg (Real.rpow_nonneg ?_ _) (Real.rpow_nonneg ?_ _)))
      (mul_nonneg hβ ?_)
    · exact integral_nonneg fun ω => integral_nonneg fun σ => Real.rpow_nonneg (abs_nonneg _) _
    · exact integral_nonneg fun ω => integral_nonneg fun τ => Real.rpow_nonneg (hd _ _) _
    · exact integral_nonneg fun ω => integral_nonneg fun σ => abs_nonneg _
  have hn0 : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
  set m : κ → κ → ℝ := fun a b => α * d a b + β with hm
  -- the pair averages, each integrable in the disorder
  have iR : ∀ r r' : R, Integrable (fun ω => ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) μ := fun r r' =>
    integrable_integral_pi_count_tilted' μ E hE _
  have iO : ∀ r : R, Integrable (fun ω => ∫ σ : Option R → κ, |f (fun i => σ (some i))| *
      m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω))) μ :=
    fun r => integrable_integral_pi_count_tilted' μ E hE _
  have iO' : ∀ r : R, Integrable (fun ω => ∫ σ : Option R → κ, |f (fun i => σ (some i))| *
      m (σ none) (σ (some r)) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω))) μ :=
    fun r => integrable_integral_pi_count_tilted' μ E hE _
  have iOO : Integrable (fun ω => ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
      m (σ (some none)) (σ none)
      ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E ω))) μ :=
    integrable_integral_pi_count_tilted' μ E hE _
  -- Hölder for each pair family
  have pR : ∀ r r' : R, r ≠ r' → ∫ ω, ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω)) ∂μ ≤ U := fun r r' hrr =>
    integral_integral_pair_holder_affine μ E hE (e := id) Function.injective_id hrr f d hd hα hpr
  have pO : ∀ r : R, ∫ ω, ∫ σ : Option R → κ, |f (fun i => σ (some i))| *
      m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) ∂μ ≤
      U := fun r =>
    integral_integral_pair_holder_affine μ E hE (e := Option.some) (Option.some_injective R)
      (Option.some_ne_none r) f d hd hα hpr
  have pO' : ∀ r : R, ∫ ω, ∫ σ : Option R → κ, |f (fun i => σ (some i))| *
      m (σ none) (σ (some r)) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) ∂μ ≤
      U := fun r =>
    integral_integral_pair_holder_affine μ E hE (e := Option.some) (Option.some_injective R)
      (Option.some_ne_none r).symm f d hd hα hpr
  have pOO : ∫ ω, ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
      m (σ (some none)) (σ none)
      ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E ω)) ∂μ ≤ U :=
    integral_integral_pair_holder_affine μ E hE (e := fun i => some (some i))
      (fun a b hab => by simpa using hab) (Option.some_ne_none none) f d hd hα hpr
  have iR' : ∀ r r' : R, Integrable (fun ω => if r = r' then (0 : ℝ) else
      ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) μ := fun r r' => by
    by_cases h : r = r'
    · simp [h]
    · simpa [h] using iR r r'
  have hint : ∀ r r' : R, ∫ ω, (if r = r' then (0 : ℝ) else ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) ∂μ ≤ U := fun r r' => by
    by_cases h : r = r'
    · simp [h, hU0]
    · simpa [h] using pR r r' h
  obtain ⟨A, hA⟩ : ∃ A : Ω → ℝ, ∀ ω, A ω = ∑ r, ∑ r', (if r = r' then (0 : ℝ) else
      ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Ω → ℝ, ∀ ω, B ω = ∑ r, (∫ σ : Option R → κ,
      |f (fun i => σ (some i))| * m (σ (some r)) (σ none)
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) +
      ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω))) := ⟨_, fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Ω → ℝ, ∀ ω, C ω = ∫ σ : Option (Option R) → κ,
      |f (fun i => σ (some (some i)))| * m (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E ω)) :=
    ⟨_, fun _ => rfl⟩
  have iA : Integrable A μ := by
    have : A = fun ω => ∑ r, ∑ r', (if r = r' then (0 : ℝ) else
        ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) := funext hA
    rw [this]
    exact integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => iR' r r'
  have iB : Integrable B μ := by
    have : B = fun ω => ∑ r, (∫ σ : Option R → κ, |f (fun i => σ (some i))| *
          m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) +
        ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω))) := funext hB
    rw [this]
    exact integrable_finsetSum _ fun r _ => (iO r).add (iO' r)
  have iC : Integrable C μ := by
    have : C = fun ω => ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
        m (σ (some none)) (σ none)
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E ω)) := funext hC
    rw [this]
    exact iOO
  have hA' : ∫ ω, A ω ∂μ ≤ (Fintype.card R : ℝ) ^ 2 * U := by
    have : ∫ ω, A ω ∂μ = ∑ r, ∑ r', ∫ ω, (if r = r' then (0 : ℝ) else
        ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) ∂μ := by
      simp_rw [hA]
      rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun r' _ => iR' r r']
      exact Finset.sum_congr rfl fun r _ => integral_finsetSum _ fun r' _ => iR' r r'
    rw [this]
    calc _ ≤ ∑ r : R, ∑ r' : R, U :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun r' _ => hint r r'
      _ = _ := by simp [sq]; ring
  have hB' : ∫ ω, B ω ∂μ ≤ 2 * (Fintype.card R : ℝ) * U := by
    have : ∫ ω, B ω ∂μ = ∑ r, (∫ ω, ∫ σ : Option R → κ, |f (fun i => σ (some i))| *
        m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) ∂μ +
      ∫ ω, ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) ∂μ) := by
      simp_rw [hB]
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun r _ => integral_add (iO r) (iO' r)
      · exact fun r _ => (iO r).add (iO' r)
    rw [this]
    calc _ ≤ ∑ r : R, (U + U) := Finset.sum_le_sum fun r _ => add_le_add (pO r) (pO' r)
      _ = _ := by simp [mul_comm]; ring
  have hC' : ∫ ω, C ω ∂μ ≤ U := by
    simp_rw [hC]; exact pOO
  have hrhs : ∀ ω, (∑ r, ∑ r', (if r = r' then (0 : ℝ) else
        ∫ σ : R → κ, |f σ| * m (σ r) (σ r')
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))) +
      Fintype.card R * ∑ r, (∫ σ : Option R → κ, |f (fun i => σ (some i))| *
          m (σ (some r)) (σ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω)) +
        ∫ σ : Option R → κ, |f (fun i => σ (some i))| * m (σ none) (σ (some r))
          ∂(Measure.pi fun _ : Option R => Measure.count.tilted (E ω))) +
      Fintype.card R * (Fintype.card R + 1) *
        ∫ σ : Option (Option R) → κ, |f (fun i => σ (some (some i)))| *
          m (σ (some none)) (σ none)
          ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted (E ω))) =
      A ω + Fintype.card R * B ω + Fintype.card R * (Fintype.card R + 1) * C ω :=
    fun ω => by rw [hA, hB, hC]
  have iRHS : Integrable (fun ω => A ω + Fintype.card R * B ω +
      Fintype.card R * (Fintype.card R + 1) * C ω) μ :=
    (iA.add (iB.const_mul _)).add (iC.const_mul _)
  calc _ ≤ ∫ ω, |∫ σ : R → κ, (∑ l, ∑ k, c ω l k * (((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {l}) *
        ((∑ r, if σ r = k then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {k}) -
        Fintype.card R * (Measure.count.tilted (E ω)).real {l} *
          ((if l = k then 1 else 0) - (Measure.count.tilted (E ω)).real {k})) -
      ∑ l, c ω l l * ((∑ r, if σ r = l then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (E ω)).real {l})) * f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E ω))| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (A ω + Fintype.card R * B ω + Fintype.card R * (Fintype.card R + 1) * C ω) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) iRHS
        (ae_of_all _ fun ω => by
          beta_reduce
          rw [← hrhs ω]
          exact abs_integral_theta_le (E ω) (c ω) m (hcm ω) f)
    _ = ∫ ω, A ω ∂μ + Fintype.card R * ∫ ω, B ω ∂μ +
        Fintype.card R * (Fintype.card R + 1) * ∫ ω, C ω ∂μ := by
      have h1 := integral_add (μ := μ) (f := fun ω => A ω + Fintype.card R * B ω)
        (g := fun ω => Fintype.card R * (Fintype.card R + 1) * C ω)
        (iA.add (iB.const_mul _)) (iC.const_mul _)
      have h2 := integral_add (μ := μ) (f := A) (g := fun ω => Fintype.card R * B ω) iA
        (iB.const_mul _)
      rw [h1, h2, integral_const_mul, integral_const_mul]
    _ ≤ (4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) * U := by
      nlinarith [mul_le_mul_of_nonneg_left hB' hn0, mul_le_mul_of_nonneg_left hC'
        (by positivity : (0 : ℝ) ≤ Fintype.card R * (Fintype.card R + 1))]

omit [DecidableEq κ] [Fintype κ] in
/-- **Comparison of finite Gibbs averages for site energies at bounded distance.** If
`|E₁ ω a - E₀ ω a| ≤ C`, the disorder average of an `R`-replica Gibbs average of `g ≥ 0` under
`E₁` is at most `exp (2 |R| C)` times that under `E₀`. -/
theorem integral_integral_count_tilted_le_exp_mul [Finite κ] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E₀ E₁ : Ω → κ → ℝ) (hE₀ : ∀ a, Measurable fun ω => E₀ ω a)
    (hE₁ : ∀ a, Measurable fun ω => E₁ ω a) {C : ℝ} (hC : ∀ ω a, |E₁ ω a - E₀ ω a| ≤ C)
    (g : (R → κ) → ℝ) (hg : ∀ σ, 0 ≤ g σ) :
    ∫ ω, ∫ σ : R → κ, g σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E₁ ω)) ∂μ ≤
      Real.exp (2 * Fintype.card R * C) *
        ∫ ω, ∫ σ : R → κ, g σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E₀ ω)) ∂μ := by
  classical
  have := Fintype.ofFinite κ
  have hm : ∀ E : Ω → κ → ℝ, (∀ a, Measurable fun ω => E ω a) →
      Measurable fun p : Ω × κ => E p.1 p.2 := fun E hE =>
    measurable_from_prod_countable_left (fun a => hE a)
  refine integral_integral_pi_tilted_le_exp_mul_of_abs_sub_le (μ := Measure.count) (ι := R)
    (P := μ) (E₀ := E₀) (E₁ := E₁) (hm E₀ hE₀) (hm E₁ hE₁)
    (B := fun ω => ∑ a, |E₀ ω a| + ∑ a, |E₁ ω a|) (fun ω a => ?_) (fun ω a => ?_) hC
    (G := fun _ σ => g σ) ((measurable_of_finite g).comp measurable_snd) (M := ∑ σ, |g σ|)
    (fun _ σ => hg σ)
    (fun _ σ => ?_)
  · exact (le_abs_self _).trans ((Finset.single_le_sum (f := fun a => |E₀ ω a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  · exact (le_abs_self _).trans ((Finset.single_le_sum (f := fun a => |E₁ ω a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
  · exact (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |g σ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ σ))

omit [DecidableEq κ] [Fintype κ] in
/-- A bounded random replica observable `g ω` has an integrable Gibbs average over a measurable
random Gibbs state that depends on two independent environments, and the average over the second
environment is integrable in the first. -/
theorem integrable_integral_integral_count_tilted [Finite κ] {Ω₀ Ξ : Type*} [MeasurableSpace Ω₀]
    [MeasurableSpace Ξ] (P₀ : Measure Ω₀) [IsFiniteMeasure P₀] (P : Measure Ξ) [IsFiniteMeasure P]
    (E : Ω₀ → Ξ → κ → ℝ) (hE : ∀ a, Measurable fun z : Ω₀ × Ξ => E z.1 z.2 a) {ι' : Type*}
    [Fintype ι'] (g : Ω₀ → (ι' → κ) → ℝ) (hg : ∀ σ, Measurable fun ω => g ω σ)
    {C : ℝ} (hgb : ∀ ω σ, |g ω σ| ≤ C) :
    Integrable (fun ω => ∫ ξ, ∫ σ, g ω σ ∂(Measure.pi fun _ : ι' =>
      Measure.count.tilted (E ω ξ)) ∂P) P₀ := by
  have hm : Measurable fun z : Ω₀ × Ξ => ∫ σ, g z.1 σ ∂(Measure.pi fun _ : ι' =>
      Measure.count.tilted (E z.1 z.2)) :=
    measurable_integral_pi_count_tilted (R := ι') (g := fun (z : Ω₀ × Ξ) (a : κ) => E z.1 z.2 a)
      (Θ := fun (z : Ω₀ × Ξ) (σ : ι' → κ) => g z.1 σ) hE
      (fun σ => (hg σ).comp measurable_fst)
  have hI : Integrable (fun z : Ω₀ × Ξ => ∫ σ, g z.1 σ ∂(Measure.pi fun _ : ι' =>
      Measure.count.tilted (E z.1 z.2))) (P₀.prod P) :=
    Integrable.of_bound (C := C) hm.aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact abs_integral_pi_count_tilted_le _ fun σ => hgb _ σ)
  exact hI.integral_prod_left

omit [DecidableEq κ] [Fintype κ] in
/-- **Comparison of nested disorder-averaged Gibbs averages.** If the site energies of two random
Gibbs states, depending on two independent environments `ω, ξ`, differ by at most `C`, then for a
bounded nonnegative observable `g ω` of `|R|` replicas the average over `(ω, ξ)` under the second
is at most `exp (2 |R| C)` times that under the first. -/
theorem integral_integral_integral_count_tilted_le_exp_mul [Finite κ] {Ω₀ Ξ : Type*}
    [MeasurableSpace Ω₀] [MeasurableSpace Ξ] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (P : Measure Ξ) [IsProbabilityMeasure P] (E₀ E₁ : Ω₀ → Ξ → κ → ℝ)
    (hE₀ : ∀ a, Measurable fun z : Ω₀ × Ξ => E₀ z.1 z.2 a)
    (hE₁ : ∀ a, Measurable fun z : Ω₀ × Ξ => E₁ z.1 z.2 a) {C : ℝ}
    (hC : ∀ ω ξ a, |E₁ ω ξ a - E₀ ω ξ a| ≤ C) (g : Ω₀ → (R → κ) → ℝ)
    (hg : ∀ σ, Measurable fun ω => g ω σ) (hg0 : ∀ ω σ, 0 ≤ g ω σ) {M : ℝ}
    (hgM : ∀ ω σ, g ω σ ≤ M) :
    ∫ ω, ∫ ξ, ∫ σ, g ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E₁ ω ξ)) ∂P ∂P₀ ≤
      Real.exp (2 * Fintype.card R * C) *
        ∫ ω, ∫ ξ, ∫ σ, g ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (E₀ ω ξ)) ∂P ∂P₀ := by
  have hgb : ∀ ω σ, |g ω σ| ≤ M := fun ω σ => by
    rw [abs_of_nonneg (hg0 ω σ)]
    exact hgM ω σ
  rw [← integral_const_mul]
  refine integral_mono (integrable_integral_integral_count_tilted P₀ P E₁ hE₁ g hg hgb)
    ((integrable_integral_integral_count_tilted P₀ P E₀ hE₀ g hg hgb).const_mul _) fun ω => ?_
  exact integral_integral_count_tilted_le_exp_mul P (E₀ ω) (E₁ ω)
    (fun a => (hE₀ a).comp (measurable_const.prodMk measurable_id))
    (fun a => (hE₁ a).comp (measurable_const.prodMk measurable_id)) (hC ω) (g ω) (hg0 ω)

omit [DecidableEq κ] [Fintype κ] in
/-- **Moments of a bounded observable.** For `0 ≤ h ≤ M` and `p ≥ 0`, the average of `h ^ p`
over a random Gibbs state is at most `M ^ p`. -/
theorem integral_integral_rpow_count_tilted_le [Finite κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → κ → ℝ) {ι' : Type*} [Fintype ι'] (h : (ι' → κ) → ℝ) {M p : ℝ} (hp : 0 ≤ p)
    (h0 : ∀ σ, 0 ≤ h σ) (hM : ∀ σ, h σ ≤ M) :
    ∫ ω, ∫ σ, h σ ^ p ∂(Measure.pi fun _ : ι' => Measure.count.tilted (E ω)) ∂μ ≤ M ^ p := by
  have hb : ∀ σ, |h σ ^ p| ≤ M ^ p := fun σ => by
    rw [abs_of_nonneg (Real.rpow_nonneg (h0 σ) p)]
    exact Real.rpow_le_rpow (h0 σ) (hM σ) hp
  have hin : ∀ ω, ∫ σ, h σ ^ p ∂(Measure.pi fun _ : ι' => Measure.count.tilted (E ω)) ≤ M ^ p :=
    fun ω => (le_abs_self _).trans (abs_integral_pi_count_tilted_le _ hb)
  calc _ ≤ ∫ _ω, M ^ p ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => integral_nonneg fun σ =>
          Real.rpow_nonneg (h0 σ) p) (integrable_const _) (ae_of_all _ hin)
    _ = M ^ p := by simp

end Holder

end SpinGlasses
