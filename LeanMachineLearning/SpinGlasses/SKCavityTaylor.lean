/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityContraction

/-!
# Second-order expansion along the cavity path (Talagrand's Proposition 1.8.1, Eq. (1.216))

For an observable `f` of `n` replicas, `ν(f)` is the `(N+1)`-spin SK average (the coupled endpoint
of the cavity path), `ν₀(f)` the decoupled endpoint, and `ν₀'(f)` the value at the decoupled
endpoint of the first derivative (Eq. (1.151)).  The first-order estimate (1.215) is
`sk_cavity_nu_sub_nu_zero_le` (Proposition 1.6.5); here we prove the second-order estimate
`|ν(f) - ν₀(f) - ν₀'(f)| ≤ K(n, β) ν(|f|^p)^{1/p} ν(|R_{1,2} - q|^{2r})^{1/r}`.

The second derivative is the first-derivative formula applied to the `(n+2)`-replica observable
`f · (replica kernel combination)`; the replicas `Option (Option (Fin n))` are identified with
`Fin (n + 2)` by `finSuccEquiv`.  The Hölder step bounds the average of
`|f| |R_{ab} - q| |R_{cd} - q|` by `sk_replica_holder_dev_dev`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The Hölder step of the second-order estimate.**  Let `F₂` be the `(n+2)`-replica observable
`f · (replica kernel combination)` obtained by differentiating once (the replicas
`Option (Option (Fin n))` identified with `Fin (n+2)` by `e`).  Then the coupled average of
`|F₂| · W`, with `W` the weighted deviation sum over the pairs of `n + 4` replicas, is at most
`8 β² n² (n+2)²` times the Hölder product with the doubled exponent `2 r`. -/
theorem integral_abs_lifted_mul_dev_le (N n : ℕ) (β q h : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {p r : ℝ} (hpr : p.HolderConjugate r)
    (e : Option (Option (Fin n)) ≃ Fin (n + 2)) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        (q - (N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)))
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    let F₂ : (Fin (n + 2) → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      f (fun r => σ (e (some (some r)))) *
        (2 * (∑ p : Fin n × Fin n with p.1 < p.2,
            U (σ (e (some (some p.1)))) (σ (e (some (some p.2))))) -
          2 * (n : ℝ) * ∑ r : Fin n, U (σ (e (some (some r)))) (σ (e (some none))) +
          (n : ℝ) * ((n : ℝ) + 1) * U (σ (e (some none))) (σ (e none)))
    ∫ g, ∫ τ : Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ,
        |F₂ (fun r => τ (some (some r)))| *
          ((∑ p : Fin (n + 2) × Fin (n + 2) with p.1 < p.2,
              dev (τ (some (some p.1))) (τ (some (some p.2)))) +
            ((n + 2 : ℕ) : ℝ) * ∑ r : Fin (n + 2), dev (τ (some (some r))) (τ (some none)) +
            ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 1) / 2 * dev (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin (n + 2))) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    8 * β ^ 2 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 *
      ((∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r)) := by
  intro Esk U dev F₂
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => Esk g c) := by
    dsimp [Esk]
    fun_prop
  obtain ⟨ι, _, pr, cw, hpairs, hc, hcw, hW⟩ := exists_replica_pair_weights n
  obtain ⟨ι', _, pr', cw', hpairs', hc', hcw', hW'⟩ := exists_replica_pair_weights (n + 2)
  let κ : Option (Option (Fin n)) → Option (Option (Fin (n + 2))) := fun o => some (some (e o))
  have hκ : Function.Injective κ := fun a b hab =>
    e.injective (Option.some_injective _ (Option.some_injective _ hab))
  let ρ : Fin n → Option (Option (Fin (n + 2))) := fun r => κ (some (some r))
  have hρ : Function.Injective ρ := fun a b hab =>
    Option.some_injective _ (Option.some_injective _ (hκ hab))
  let G : ι × ι' → (Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ) → ℝ := fun jj τ =>
    |f (fun s => τ (ρ s))| * (dev (τ (κ (pr jj.1).1)) (τ (κ (pr jj.1).2)) *
      dev (τ (pr' jj.2).1) (τ (pr' jj.2).2))
  have hpt : ∀ τ : Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ,
      |F₂ (fun r => τ (some (some r)))| *
        ((∑ p : Fin (n + 2) × Fin (n + 2) with p.1 < p.2,
            dev (τ (some (some p.1))) (τ (some (some p.2)))) +
          ((n + 2 : ℕ) : ℝ) * ∑ r : Fin (n + 2), dev (τ (some (some r))) (τ (some none)) +
          ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 1) / 2 * dev (τ (some none)) (τ none)) ≤
        ∑ jj : ι × ι', (2 * β ^ 2 * (cw jj.1 * cw' jj.2)) * G jj τ := fun τ => by
    have hU := abs_sk_cavity_angle_combination_le N n β q (fun o => τ (κ o))
    have hD : 0 ≤ ∑ j', cw' j' * dev (τ (pr' j').1) (τ (pr' j').2) :=
      Finset.sum_nonneg fun j' _ => mul_nonneg (hc' j') (abs_nonneg _)
    rw [hW' dev τ]
    calc _ ≤ (|f (fun s => τ (ρ s))| * (2 * β ^ 2 * ∑ j, cw j *
            dev (τ (κ (pr j).1)) (τ (κ (pr j).2)))) *
          ∑ j', cw' j' * dev (τ (pr' j').1) (τ (pr' j').2) := by
          refine mul_le_mul_of_nonneg_right ?_ hD
          rw [show F₂ (fun r => τ (some (some r))) = f (fun s => τ (ρ s)) * _ from rfl, abs_mul]
          refine mul_le_mul_of_nonneg_left (hU.trans (le_of_eq ?_)) (abs_nonneg _)
          rw [← hW dev (fun o => τ (κ o))]
      _ = _ := by
          rw [show (|f (fun s => τ (ρ s))| * (2 * β ^ 2 * ∑ j, cw j *
              dev (τ (κ (pr j).1)) (τ (κ (pr j).2)))) *
              ∑ j', cw' j' * dev (τ (pr' j').1) (τ (pr' j').2) =
              2 * β ^ 2 * |f (fun s => τ (ρ s))| *
                ((∑ j, cw j * dev (τ (κ (pr j).1)) (τ (κ (pr j).2))) *
                  ∑ j', cw' j' * dev (τ (pr' j').1) (τ (pr' j').2)) by ring,
            Finset.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          simp only [G]
          ring
  have hdet (Θ : (Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ) → ℝ) :
      Integrable (fun g : FinPairs (N + 1) → ℝ =>
        ∫ τ : Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ, Θ τ
          ∂(Measure.pi fun _ : Option (Option (Fin (n + 2))) => Measure.count.tilted (Esk g)))
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (g : FinPairs (N + 1) → ℝ) => Esk g a)
      (fun a => (hEg a).aemeasurable) Θ
  set X : ℝ := (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r) with hX
  refine (integral_mono (hdet _) (hdet fun τ =>
    ∑ jj : ι × ι', (2 * β ^ 2 * (cw jj.1 * cw' jj.2)) * G jj τ) fun g =>
    integral_mono Integrable.of_finite Integrable.of_finite hpt).trans ?_
  have key := integral_integral_finset_sum_le
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (fun g => Measure.pi fun _ : Option (Option (Fin (n + 2))) => Measure.count.tilted (Esk g))
    (Finset.univ : Finset (ι × ι')) (fun jj => 2 * β ^ 2 * (cw jj.1 * cw' jj.2)) G X
    (fun _ _ => Integrable.of_finite) (fun jj => hdet (G jj))
    (fun jj _ => mul_nonneg (by positivity) (mul_nonneg (hc _) (hc' _)))
    (fun jj _ => sk_replica_holder_dev_dev N n β h q hρ f hpr
      (fun h => hpairs jj.1 (hκ h)) (hpairs' jj.2))
  refine key.trans (le_of_eq ?_)
  have hsum : ∑ jj : ι × ι', 2 * β ^ 2 * (cw jj.1 * cw' jj.2) =
      2 * β ^ 2 * ((∑ j, cw j) * ∑ j', cw' j') := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [hsum, hcw, hcw']
  push_cast
  ring

/-- **Talagrand's Proposition 1.8.1, Eq. (1.216).**  For an observable `f` of `n` replicas and
conjugate exponents `p, r`,
`|ν(f) - ν₀(f) - ν₀'(f)| ≤ K(n, β) ν(|f|^p)^{1/p} ν(|R_{1,2} - q|^{2r})^{1/r}`,
where `ν` is the `(N+1)`-spin SK average (the coupled endpoint of the cavity path), `ν₀` the
decoupled endpoint (angle `π/2`) and `ν₀'(f)` the value there of the first derivative (Eq. (1.151),
with the truncated overlap `R⁻`).  The constant is `4 n² (n+2)² β⁴ exp (4 (n+4)² β²)`. -/
theorem sk_cavity_nu_sub_nu_zero_sub_deriv_le (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) {p r : ℝ}
    (hpr : p.HolderConjugate r) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    let dev : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (y i : ℝ)) - q|
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
    4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
      ((∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r)) := by
  intro B E Esk K dev
  let P₀ : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)))
  have hUK : ∀ a b, U a b = -K a b := fun a b => by simp only [U, K]; ring
  let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
    (Equiv.optionCongr (finSuccEquiv n).symm).trans (finSuccEquiv (n + 1)).symm
  let Ucomb : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    2 * (∑ p : Fin n × Fin n with p.1 < p.2, U (τ (some (some p.1))) (τ (some (some p.2)))) -
      2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none)
  let F₂ : (Fin (n + 2) → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    f (fun r => σ (e (some (some r)))) * Ucomb (fun o => σ (e o))
  let Ψ : ℝ → ℝ := fun s => ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
    ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s g' ω)) ∂P ∂P₀
  let G : ℝ → ℝ := fun s => ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
    ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, f (fun r => τ (some (some r))) * Ucomb τ
    ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s g' ω)) ∂P ∂P₀
  set X : ℝ := (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ| ^ p
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / p) *
      (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, dev (σ 0) (σ 1) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ^ (1 / r) with hX
  have hX0 : 0 ≤ X := mul_nonneg
    (Real.rpow_nonneg (integral_nonneg fun g => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) _)
    (Real.rpow_nonneg (integral_nonneg fun g => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) _)
  set Kb : ℝ := 16 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 *
    Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) * X with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  have hΨ : ∀ s, HasDerivAt Ψ (Real.sin s * Real.cos s * G s) s := fun s =>
    hasDerivAt_integral_sk_cavity_path_angle_offDiag N n β q h hq f s
  have hGe : G = fun s => ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin (n + 2) → Fin (N + 1) → ℤˣ,
      F₂ σ ∂(Measure.pi fun _ : Fin (n + 2) => Measure.count.tilted (E s g' ω)) ∂P ∂P₀ := by
    funext s
    refine integral_congr_ae (ae_of_all _ fun g' => ?_)
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact integral_pi_count_tilted_reindex e (E s g' ω)
      (fun τ => f (fun r => τ (some (some r))) * Ucomb τ)
  let Ucomb₂ : (Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    2 * (∑ p : Fin (n + 2) × Fin (n + 2) with p.1 < p.2,
        U (τ (some (some p.1))) (τ (some (some p.2)))) -
      2 * ((n + 2 : ℕ) : ℝ) * ∑ r : Fin (n + 2), U (τ (some (some r))) (τ (some none)) +
      ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 1) * U (τ (some none)) (τ none)
  let D₂ : ℝ → ℝ := fun s => ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
    ∫ τ : Option (Option (Fin (n + 2))) → Fin (N + 1) → ℤˣ,
      F₂ (fun r => τ (some (some r))) * Ucomb₂ τ
    ∂(Measure.pi fun _ : Option (Option (Fin (n + 2))) => Measure.count.tilted (E s g' ω))
    ∂P ∂P₀
  have hd₂ : ∀ s, HasDerivAt G (Real.sin s * Real.cos s * D₂ s) s := fun s => by
    rw [hGe]
    exact hasDerivAt_integral_sk_cavity_path_angle_offDiag N (n + 2) β q h hq F₂ s
  have hG : ∀ s, ∃ D, HasDerivAt G (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc (0 : ℝ) (π / 2) → |D| ≤ Kb) := fun s => by
    refine ⟨D₂ s, hd₂ s, fun hs => ?_⟩
    · refine (abs_sk_cavity_angle_derivative_le N (n + 2) β q h hq F₂ hs).trans ?_
      have hT := integral_abs_lifted_mul_dev_le N n β q h f hpr e
      have hc : ((n + 2 : ℕ) : ℝ) + 2 = (n : ℝ) + 4 := by push_cast; ring
      rw [hc]
      calc _ ≤ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
            (8 * β ^ 2 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * X) :=
            mul_le_mul_of_nonneg_left hT (by positivity)
        _ = Kb := by rw [hKb]; ring
  have h2 := Real.abs_sub_sub_half_le_of_second_order hKb0 hΨ hG
  have h0 : Ψ 0 = ∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_sk_cavity_path_zero N n β q h f
  have hder : (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω)) ∂P ∂P₀) = -(G (π / 2) / 2) := by
    have hpt : ∀ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
        f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none)) =
          -(1 / 2) * (f (fun r => τ (some (some r))) * Ucomb τ) := fun τ => by
      simp only [Ucomb, hUK]
      simp only [Finset.sum_neg_distrib]
      ring
    simp only [hpt, integral_const_mul, G]
    ring
  rw [hder, ← h0]
  have h3 : Ψ (π / 2) = ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω)) ∂P ∂P₀ := rfl
  rw [← h3]
  have h4 := h2
  rw [abs_sub_comm] at h4
  calc _ = |Ψ (π / 2) - Ψ 0 - G (π / 2) / 2| := by
        rw [← abs_neg]
        congr 1
        ring
    _ ≤ Kb / 4 := h2
    _ = _ := by rw [hKb]; ring

/-- **Talagrand's Eq. (1.216) with `τ₁ = τ₂ = 2`.**  For an observable `f` of `n` replicas,
`|ν(f) - ν₀(f) - ν₀'(f)| ≤ K(n, β) ν(f²)^{1/2} ν((R_{1,2} - q)⁴)^{1/2}`,
where `ν` is the `(N+1)`-spin SK average (the coupled endpoint of the cavity path), `ν₀` the
decoupled endpoint (angle `π/2`) and `ν₀'(f)` the value there of the first derivative (Eq. (1.151),
with the truncated overlap `R⁻`).  The constant is `4 n² (n+2)² β⁴ exp (4 (n+4)² β²)`. -/
theorem sk_cavity_nu_sub_nu_zero_sub_deriv_le_two (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
    4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
      (Real.sqrt (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) *
      Real.sqrt (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) := by
  intro B E Esk K
  have := sk_cavity_nu_sub_nu_zero_sub_deriv_le N n β q h hq f Real.HolderConjugate.two_two
  have e4 : ∀ x : ℝ, |x| ^ (2 * (2 : ℝ)) = x ^ 4 := fun x => by
    rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Even.pow_abs ⟨2, rfl⟩ x
  simp only [Real.rpow_two, sq_abs, e4, ← Real.sqrt_eq_rpow] at this
  exact this

end SpinGlasses
