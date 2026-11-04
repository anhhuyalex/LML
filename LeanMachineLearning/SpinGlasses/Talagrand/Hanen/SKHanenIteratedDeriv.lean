/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.SpinGlasses.Gibbs.GibbsReplicaMarginal
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCavityReplicaPairs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IntervalDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityDomination
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityContraction
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCavityTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrderMoments
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.Contractions.SKOverlapCLTStep

/-!
# Iterated cavity derivatives and Taylor bounds
(Talagrand Lemmas 1.11.3, 1.11.5, Corollaries 1.11.6, 1.11.7)

This module formalizes the quantitative differential calculus along the cavity path:
* `skCavityPathMean`: the disorder-averaged $n$-replica Gibbs average along the cavity path
  $u \mapsto \nu_u(f)$ parameterized by $u \in [0, 1]$ ($u = 1$ is coupled, $u = 0$ is decoupled).
* `skCavityPathDerivKernel`: the observable on `Option (Option (Fin n))` produced by differentiating
  with respect to $u$.
* `hasDerivAt_skCavityPathMean`: differentiability of $u \mapsto \nu_u(f)$ on $(0, 1)$ via
  `hasDerivAt_integral_sk_cavity_path_square`.
* Reindexing the two fresh replicas gives another cavity-path mean on `Fin (n + 2)`.

The iterated derivative bounds and their connection to decoupled vanishing remain open.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The disorder-averaged `n`-replica Gibbs average along the cavity path parameterized by
`u ∈ [0, 1]`. Here `u = 1` corresponds to the coupled system ($s = 0$), and `u = 0` corresponds
to the decoupled endpoint ($s = \pi / 2$). -/
noncomputable def skCavityPathMean (N n : ℕ) (β q h : ℝ) (u : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) : ℝ :=
  let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
    (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs N,
          g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  let s := Real.arccos (Real.sqrt u)
  let E : (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' ω a =>
    Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
      (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
    Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
  ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
    ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g' ω))
    ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
  ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)

/-- The cavity interaction kernel:
$K(a, b) = \beta^2 \varepsilon(a) \varepsilon(b) (R^-(a, b) - q)$. -/
noncomputable def skCavityPathKernel (N : ℕ) (β q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) : ℝ :=
  β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
    ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)

/-- The truncated Ising overlap deviation $|R^-(a, b) - q|$. -/
noncomputable def skCavityTruncDev (N : ℕ) (q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) : ℝ :=
  |((N + 1 : ℝ)⁻¹ *
    ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)|

/-- The observable produced on `Option (Option (Fin n))` replicas by differentiating
`skCavityPathMean` with respect to `u`. -/
noncomputable def skCavityPathDerivKernel (N n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
  f (fun r => τ (some (some r))) *
    ((∑ p : Fin n × Fin n with p.1 < p.2,
        skCavityPathKernel N β q (τ (some (some p.1))) (τ (some (some p.2)))) -
      (n : ℝ) * ∑ r : Fin n,
        skCavityPathKernel N β q (τ (some (some r))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 *
        skCavityPathKernel N β q (τ (some none)) (τ none))

/-- The cavity derivative kernel is the canonical signed sum over distinct replica pairs. -/
theorem skCavityPathDerivKernel_eq_pair_sum (N n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :
    skCavityPathDerivKernel N n β q f τ =
      (f (fun r => τ (some (some r)))) * ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j * skCavityPathKernel N β q
          (τ (skCavityReplicaPairMap j).1) (τ (skCavityReplicaPairMap j).2) := by
  rw [skCavityPathDerivKernel, sk_cavity_signed_pair_sum]

/-- Pointwise bound on the cavity interaction kernel: $|K(a, b)| \le \beta^2 |R^-(a, b) - q|$. -/
theorem abs_skCavityPathKernel_le (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    |skCavityPathKernel N β q a b| ≤ β ^ 2 * skCavityTruncDev N q a b := by
  dsimp only [skCavityPathKernel, skCavityTruncDev]
  rw [abs_mul, abs_mul, abs_mul]
  have ha : |(a (Fin.last N) : ℝ)| = 1 := by
    rcases units_cast_eq_one_or (a (Fin.last N)) with h | h <;> simp [h]
  have hb : |(b (Fin.last N) : ℝ)| = 1 := by
    rcases units_cast_eq_one_or (b (Fin.last N)) with h | h <;> simp [h]
  rw [ha, hb, mul_one, mul_one, abs_sq]

/-- **Talagrand's Eq. (1.151).** Derivative of the cavity path expectation with respect to
the square parameter `u ∈ (0, 1)`. -/
theorem hasDerivAt_skCavityPathMean (N n : ℕ) (β q h t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ);
    let E : (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' ω a =>
      Real.cos (Real.arccos (Real.sqrt t)) * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin (Real.arccos (Real.sqrt t)) * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) +
        B g' a;
    HasDerivAt (skCavityPathMean N n β q h · f)
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          skCavityPathDerivKernel N n β q f τ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) t :=
  hasDerivAt_integral_sk_cavity_path_square N n β q h t hq ht f

/-- The cavity path mean is continuous, including at both endpoints. -/
theorem continuous_skCavityPathMean (N n : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    Continuous (fun u => skCavityPathMean N n β q h u f) := by
  let Φ : ℝ → ℝ := fun s =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
              (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
            Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) +
            ((Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (a p.val.1.castSucc : ℝ) *
                (a p.val.2.castSucc : ℝ)) + h * ∑ i : Fin (N + 1), (a i : ℝ))))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_integral_sk_cavity_path_angle_offDiag N n β q h hq f s).continuousAt
  exact hcont.comp (Real.continuous_arccos.comp Real.continuous_sqrt)

/-- The cavity derivative is another cavity-path mean, with two fresh replicas reindexed
by `Fin (n + 2)`. This gives an iterable first-derivative step on the open interval. -/
theorem hasDerivAt_skCavityPathMean_fin_step (N n : ℕ) (β q h t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
      by simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    HasDerivAt (skCavityPathMean N n β q h · f)
      (skCavityPathMean N (n + 2) β q h t
        (fun τ => skCavityPathDerivKernel N n β q f (fun i => τ (e i)))) t := by
  dsimp only
  let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
    by simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
  apply (hasDerivAt_skCavityPathMean N n β q h t hq ht f).congr_deriv
  dsimp only [skCavityPathMean]
  congr 1
  funext g
  congr 1
  funext ω
  apply integral_pi_count_tilted_reindex e

/-- Replica count after iterating the two-fresh-replica cavity derivative. -/
def skCavityIterReplicaCount : ℕ → ℕ → ℕ
  | 0, n => n
  | m + 1, n => skCavityIterReplicaCount m (n + 2)

/-- Each cavity derivative introduces two fresh replicas. -/
theorem skCavityIterReplicaCount_eq (m n : ℕ) : skCavityIterReplicaCount m n = n + 2 * m := by
  induction m generalizing n with
  | zero => simp [skCavityIterReplicaCount]
  | succ m ih => simp only [skCavityIterReplicaCount, ih]; omega

/-- The observable obtained by iterating the reindexed cavity derivative kernel. -/
noncomputable def skCavityIterKernel (N : ℕ) (β q : ℝ) :
    (m n : ℕ) → ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →
      ((Fin (skCavityIterReplicaCount m n) → Fin (N + 1) → ℤˣ) → ℝ)
  | 0, _, f => f
  | m + 1, n, f =>
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) := by
      simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    skCavityIterKernel N β q m (n + 2)
      (fun τ => skCavityPathDerivKernel N n β q f (fun i => τ (e i)))

/-- All interior derivatives are cavity means of the corresponding iterated kernel. -/
theorem iteratedDeriv_skCavityPathMean (N m : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    iteratedDeriv m (fun t => skCavityPathMean N n β q h t f) u =
      skCavityPathMean N (skCavityIterReplicaCount m n) β q h u
        (skCavityIterKernel N β q m n f) := by
  induction m generalizing n f with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ']
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) := by
      simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    let g := fun (τ : Fin (n + 2) → Fin (N + 1) → ℤˣ) =>
      skCavityPathDerivKernel N n β q f (fun i => τ (e i))
    have heq : deriv (fun t => skCavityPathMean N n β q h t f) =ᶠ[nhds u]
        (fun t => skCavityPathMean N (n + 2) β q h t g) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
      exact (hasDerivAt_skCavityPathMean_fin_step N n β q h t hq ht f).deriv
    rw [heq.iteratedDeriv_eq m, ih (n + 2) g]
    rfl

/-- The first derivative formula extends to the closed interval, including its endpoints. -/
theorem hasDerivWithinAt_skCavityPathMean_fin_step (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) := by
      simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    HasDerivWithinAt (skCavityPathMean N n β q h · f)
      (skCavityPathMean N (n + 2) β q h u
        (fun τ => skCavityPathDerivKernel N n β q f (fun i => τ (e i)))) (Set.Icc 0 1) u := by
  dsimp only
  let e : Option (Option (Fin n)) ≃ Fin (n + 2) := by
    simpa [Fintype.card_option, Nat.add_assoc] using
      (Fintype.equivFin (Option (Option (Fin n))))
  let g := fun (τ : Fin (n + 2) → Fin (N + 1) → ℤˣ) =>
    skCavityPathDerivKernel N n β q f (fun i => τ (e i))
  apply hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num)
    (skCavityPathMean N n β q h · f) (skCavityPathMean N (n + 2) β q h · g)
    (continuous_skCavityPathMean N n β q h hq f)
    (continuous_skCavityPathMean N (n + 2) β q h hq g) ?_ u hu
  exact fun t ht => hasDerivAt_skCavityPathMean_fin_step N n β q h t hq ht f

/-- All derivatives within the closed interval are means of the iterated cavity kernel. -/
theorem iteratedDerivWithin_skCavityPathMean (N m : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t f) (Set.Icc 0 1) u =
      skCavityPathMean N (skCavityIterReplicaCount m n) β q h u
        (skCavityIterKernel N β q m n f) := by
  induction m generalizing n f with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDerivWithin_succ']
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) := by
      simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    let g := fun (τ : Fin (n + 2) → Fin (N + 1) → ℤˣ) =>
      skCavityPathDerivKernel N n β q f (fun i => τ (e i))
    have heq : Set.EqOn (derivWithin (fun t => skCavityPathMean N n β q h t f)
        (Set.Icc 0 1)) (fun t => skCavityPathMean N (n + 2) β q h t g) (Set.Icc 0 1) := by
      intro t ht
      exact (hasDerivWithinAt_skCavityPathMean_fin_step N n β q h hq f t ht).derivWithin
        (uniqueDiffOn_Icc_zero_one t ht)
    calc
      _ = iteratedDerivWithin m (fun t => skCavityPathMean N (n + 2) β q h t g)
            (Set.Icc 0 1) u := iteratedDerivWithin_congr heq hu
      _ = _ := ih (n + 2) g

/-- The cavity path is smooth to every finite order on the closed interval. -/
theorem contDiffOn_skCavityPathMean (N n : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ∀ k : ℕ, ContDiffOn ℝ k (fun t => skCavityPathMean N n β q h t f) (Set.Icc 0 1) := by
  intro k
  apply contDiffOn_of_differentiableOn_deriv (n := k)
  intro m _
  have heq : Set.EqOn
      (iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t f) (Set.Icc 0 1))
      (fun t => skCavityPathMean N (skCavityIterReplicaCount m n) β q h t
        (skCavityIterKernel N β q m n f)) (Set.Icc 0 1) := by
    intro t ht
    exact iteratedDerivWithin_skCavityPathMean N m β q h hq n f t ht
  apply DifferentiableOn.congr ?_ heq
  intro t ht
  exact (hasDerivWithinAt_skCavityPathMean_fin_step N (skCavityIterReplicaCount m n) β q h hq
    (skCavityIterKernel N β q m n f) t ht).differentiableWithinAt


/-- The second cavity derivative on the open interval, obtained by applying the
reindexed first-derivative formula twice. -/
theorem hasDerivAt_deriv_skCavityPathMean (N n : ℕ) (β q h t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
      by simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin n))))
    let e' : Option (Option (Fin (n + 2))) ≃ Fin ((n + 2) + 2) :=
      by simpa [Fintype.card_option, Nat.add_assoc] using
        (Fintype.equivFin (Option (Option (Fin (n + 2)))))
    let g := fun (τ : Fin (n + 2) → Fin (N + 1) → ℤˣ) =>
      skCavityPathDerivKernel N n β q f (fun i => τ (e i))
    HasDerivAt (deriv (skCavityPathMean N n β q h · f))
      (skCavityPathMean N ((n + 2) + 2) β q h t
        (fun τ => skCavityPathDerivKernel N (n + 2) β q g (fun i => τ (e' i)))) t := by
  dsimp only
  let e : Option (Option (Fin n)) ≃ Fin (n + 2) :=
    by simpa [Fintype.card_option, Nat.add_assoc] using
      (Fintype.equivFin (Option (Option (Fin n))))
  let g := fun (τ : Fin (n + 2) → Fin (N + 1) → ℤˣ) =>
    skCavityPathDerivKernel N n β q f (fun i => τ (e i))
  have heq : deriv (skCavityPathMean N n β q h · f) =ᶠ[nhds t]
      (fun u => skCavityPathMean N (n + 2) β q h u g) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact (hasDerivAt_skCavityPathMean_fin_step N n β q h u hq hu f).deriv
  exact (hasDerivAt_skCavityPathMean_fin_step N (n + 2) β q h t hq ht g).congr_of_eventuallyEq
    heq

/-- Bound on the derivative kernel `skCavityPathDerivKernel` in terms of centered overlaps. -/
theorem abs_skCavityPathDerivKernel_le (N n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :
    |skCavityPathDerivKernel N n β q f τ| ≤
      β ^ 2 * |f (fun r => τ (some (some r)))| *
        (∑ p : Fin n × Fin n with p.1 < p.2,
            skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) +
          (n : ℝ) * ∑ r : Fin n,
            skCavityTruncDev N q (τ (some (some r))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 *
            skCavityTruncDev N q (τ (some none)) (τ none)) := by
  let X := ∑ p : Fin n × Fin n with p.1 < p.2,
    skCavityPathKernel N β q (τ (some (some p.1))) (τ (some (some p.2)))
  let Y := (n : ℝ) * ∑ r : Fin n,
    skCavityPathKernel N β q (τ (some (some r))) (τ (some none))
  let Z := (n : ℝ) * ((n : ℝ) + 1) / 2 *
    skCavityPathKernel N β q (τ (some none)) (τ none)
  have h_inner : |X - Y + Z| ≤ β ^ 2 *
      (∑ p : Fin n × Fin n with p.1 < p.2,
          skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) +
        (n : ℝ) * ∑ r : Fin n,
          skCavityTruncDev N q (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 *
          skCavityTruncDev N q (τ (some none)) (τ none)) := by
    have htri : |X - Y + Z| ≤ |X| + |Y| + |Z| := by
      linarith [abs_add_le (X - Y) Z, abs_sub X Y]
    refine htri.trans ?_
    have hX : |X| ≤ β ^ 2 * ∑ p : Fin n × Fin n with p.1 < p.2,
        skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun p hp => abs_skCavityPathKernel_le N β q _ _).trans ?_
      rw [← mul_sum]
    have hY : |Y| ≤ (n : ℝ) * (β ^ 2 * ∑ r : Fin n,
        skCavityTruncDev N q (τ (some (some r))) (τ (some none))) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun r hr => abs_skCavityPathKernel_le N β q _ _).trans ?_
      rw [← mul_sum]
    have hZ : |Z| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 *
        (β ^ 2 * skCavityTruncDev N q (τ (some none)) (τ none)) := by
      rw [abs_mul]
      have hpos : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by positivity
      rw [abs_of_nonneg hpos]
      exact mul_le_mul_of_nonneg_left (abs_skCavityPathKernel_le N β q _ _) hpos
    linarith
  dsimp only [skCavityPathDerivKernel]
  rw [abs_mul]
  have h_prod := mul_le_mul_of_nonneg_left h_inner
    (abs_nonneg (f (fun r => τ (some (some r)))))
  calc |f (fun r => τ (some (some r)))| * |X - Y + Z| ≤
      |f (fun r => τ (some (some r)))| * (β ^ 2 * _) := h_prod
  _ = β ^ 2 * |f (fun r => τ (some (some r)))| * _ := by ring

end SpinGlasses
