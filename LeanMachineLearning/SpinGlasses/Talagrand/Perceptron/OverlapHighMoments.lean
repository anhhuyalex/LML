/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingSmartPath
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingHamiltonian
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKOverlapMoments
public import LeanMachineLearning.ForMathlib.Data.Finset.SumBound
public import LeanMachineLearning.ForMathlib.Order.Interval.Finset.FinSwap

/-!
# Higher moments and exponential concentration of the overlap (Talagrand Section 2.5, Theorem 2.5.1)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, Theorem 2.5.1,
Eqs. (2.94)--(2.98).

For the `s`-interpolating Hamiltonian (2.76) on `N + 1` spins and `M` constraints at any
`s ∈ [0, 1]`, under assumption (2.7) and small load `α K(D) ≤ 1`, any solution `(q, r)` of (2.68)
satisfies
$$\forall k \ge 0, \quad
  \nu_s\!\left((R_{1,2} - q)^{2k}\right) \le \left(\frac{64 k}{N + 1}\right)^k.$$
Proving the bound uniformly over `s ∈ [0, 1]` establishes both Theorem 2.5.1 (`s = 1`) and the
uniformity exercise required in the proof of Theorem 2.5.3.

We also deduce an exponential square-moment corollary (an addition beyond the printed text):
for `0 ≤ c ≤ 1 / 200` (inside `c < 1 / (64 e)`),
$$\nu_s\!\left(\exp\!\left(c (N + 1) (R_{1,2} - q)^2\right)\right) \le 8.$$
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-! ### Elementary partial-sum bounds and permutation symmetry on `Finset.Ici n` -/

/-- Any partial sum `((N + 1)⁻¹) * ∑ i ∈ S, (σ₀_i σ₁_i - q)` over a subset `S ⊆ Finset.univ` of
`Fin (N + 1)` has modulus at most `2` when `q ∈ [0, 1]`. -/
private lemma abs_partial_overlap_sub_le_two {N : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (S : Finset (Fin (N + 1))) (x y : Fin (N + 1) → ℤˣ) :
    |((N : ℝ) + 1)⁻¹ * ∑ i ∈ S, (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)| ≤ 2 := by
  simpa using Finset.abs_inv_card_mul_sum_le S
    (f := fun i => ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)
    (fun i => abs_units_cast_mul_sub_le_two (x i) (y i) hq)

/-- **Site-symmetry identity on `Finset.Ici n` for the `s`-interpolating Gibbs measure:**
for any `n : Fin (N + 1)` and `k : ℕ`, with `A_n = (N + 1)⁻¹ ∑_{i ≥ n} (σ₀_i σ₁_i - q)`,
`ν_s(A_n^{2k+2}) = ((N + 1 - n) / (N + 1)) * ν_s((ε₁ ε₂ - q) A_n^{2k+1})`. -/
private lemma integral_interpolating_partial_overlap_succ_eq_last {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (n : Fin (N + 1)) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A_fn (x y : Fin (N + 1) → ℤˣ) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.Ici n, (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        A_fn (σ 0).1 (σ 1).1 ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s =
      (((Finset.Ici n).card : ℝ) / ((N : ℝ) + 1)) *
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((σ 0).1 (Fin.last N) : ℤ) : ℝ) * (((σ 1).1 (Fin.last N) : ℤ) : ℝ) - q) *
            A_fn (σ 0).1 (σ 1).1 ^ (2 * k + 1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
  intro P_g P_z P_z' P_s μ_s E_s A_fn
  let Θ (i : Fin (N + 1)) (x y : Fin (N + 1) → ℤˣ) : ℝ :=
    (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) * A_fn x y ^ (2 * k + 1)
  have hlast_mem : Fin.last N ∈ Finset.Ici n := Finset.mem_Ici.2 (Fin.le_last n)
  have hA_swap {i : Fin (N + 1)} (hi : i ∈ Finset.Ici n) (x y : Fin (N + 1) → ℤˣ) :
      A_fn (fun j => x (Equiv.swap i (Fin.last N) j))
        (fun j => y (Equiv.swap i (Fin.last N) j)) = A_fn x y := by
    dsimp only [A_fn]
    congr 1
    refine Equiv.Perm.sum_comp (Equiv.swap i (Fin.last N)) (Finset.Ici n)
      (fun j => ((x j : ℤ) : ℝ) * ((y j : ℤ) : ℝ) - q) fun a ha => ?_
    by_cases hai : a = i
    · exact Finset.mem_coe.2 (hai ▸ hi)
    · by_cases hal : a = Fin.last N
      · exact Finset.mem_coe.2 (hal ▸ hlast_mem)
      · exact absurd (Equiv.swap_apply_of_ne_of_ne hai hal) ha
  have hsite {i : Fin (N + 1)} (hi : i ∈ Finset.Ici n) :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ (Fin.last N) (σ 0).1 (σ 1).1
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s :=
    integral_interpolating_two_replica_site_swap hu hB s q r Θ i fun x y => by
      simp only [Θ, hA_swap hi, Equiv.swap_apply_right]
  let Ω := ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)
  let E_eff (ω : Ω) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
    ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)
  have haux (ω : Ω) (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) := by
    have hE_swap (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x = (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ j : Fin M, u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)) := add_comm _ _
    simp_rw [show E_s ω = _ from funext hE_swap]
    exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
      (fun τ j ξ => u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
        ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ)))
      (fun τ j => hu.comp (by fun_prop)) (fun _ => B) (fun _ _ _ => hB _) Φ
  have hE_eff_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω : Ω => E_eff ω τ := by
    dsimp only [E_eff]
    have hm1 : Measurable fun ω : Ω =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).mul measurable_const
    have hm2 : Measurable fun ω : Ω =>
        ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1) := by
      refine Finset.measurable_sum _ fun j _ => Real.measurable_log.comp ?_
      have hj : Measurable fun p : Ω × ℝ =>
          Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 j i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 j + Real.sqrt (1 - q) * p.2))) := by
        have hs1 : Measurable fun p : Ω × ℝ =>
            ∑ i : Fin (N + 1), p.1.1.1 j i * ((τ i : ℤ) : ℝ) := by
          refine Finset.measurable_sum _ fun i _ => ?_
          have mg : Measurable fun p : Ω × ℝ => p.1.1.1 j i :=
            (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
              (measurable_fst.comp (measurable_fst.comp measurable_fst)))
          exact mg.mul_const _
        have hz1 : Measurable fun p : Ω × ℝ => p.1.1.2 j :=
          (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
        exact Real.measurable_exp.comp (hu.comp
          (((hs1.const_mul _).const_mul _).add
            (((hz1.const_mul _).add (measurable_snd.const_mul _)).const_mul _)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    exact hm1.add hm2
  have hP_prob : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
  have hint (i : Fin (N + 1)) :
      Integrable (fun ω : Ω => ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (τ 0) (τ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))) P_s := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite
      (fun τ : Fin 2 → Fin (N + 1) → ℤˣ => Θ i (τ 0) (τ 1))
    exact integrable_integral_pi_count_tilted_of_bound E_eff hE_eff_m
      (fun _ τ => Θ i (τ 0) (τ 1)) (fun _ => measurable_const) C (fun _ τ => hC τ)
  have hsum :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (∑ i ∈ Finset.Ici n, Θ i (σ 0).1 (σ 1).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ∑ i ∈ Finset.Ici n,
          ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
    have hlhs : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (∑ i ∈ Finset.Ici n, Θ i (σ 0).1 (σ 1).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, (∑ i ∈ Finset.Ici n, Θ i (τ 0) (τ 1))
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s :=
      integral_congr_ae (ae_of_all _ fun ω =>
        haux ω (fun τ => ∑ i ∈ Finset.Ici n, Θ i (τ 0) (τ 1)))
    have hrhs (i : Fin (N + 1)) : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (τ 0) (τ 1)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s :=
      integral_congr_ae (ae_of_all _ fun ω => haux ω (fun τ => Θ i (τ 0) (τ 1)))
    rw [hlhs]
    simp_rw [hrhs]
    exact integral_integral_finset_sum P_s
      (fun ω => Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))
      (Finset.Ici n) (fun i (τ : Fin 2 → Fin (N + 1) → ℤˣ) => Θ i (τ 0) (τ 1))
      (fun _ _ _ => Integrable.of_finite) (fun i _ => hint i)
  have hpt (x y : Fin (N + 1) → ℤˣ) :
      ∑ i ∈ Finset.Ici n, Θ i x y = ((N : ℝ) + 1) * A_fn x y ^ (2 * k + 2) := by
    have h1 : ∑ i ∈ Finset.Ici n, (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) =
        ((N : ℝ) + 1) * A_fn x y := by
      dsimp only [A_fn]
      have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    dsimp only [Θ]
    rw [← Finset.sum_mul, h1, pow_succ']
    ring
  have hν_lhs :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (∑ i ∈ Finset.Ici n, Θ i (σ 0).1 (σ 1).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ((N : ℝ) + 1) * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          A_fn (σ 0).1 (σ 1).1 ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
    simp_rw [hpt, integral_const_mul]
  have hν_rhs :
      (∑ i ∈ Finset.Ici n,
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ((Finset.Ici n).card : ℝ) *
          ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            Θ (Fin.last N) (σ 0).1 (σ 1).1
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
    rw [Finset.sum_congr rfl fun i hi => hsite hi, Finset.sum_const, nsmul_eq_mul]
  rw [hν_lhs, hν_rhs] at hsum
  have hL : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmul : (((Finset.Ici n).card : ℝ) / ((N : ℝ) + 1)) *
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        Θ (Fin.last N) (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
      (((Finset.Ici n).card : ℝ) *
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ (Fin.last N) (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) /
        ((N : ℝ) + 1) := div_mul_eq_mul_div _ _ _
  dsimp only [Θ] at hsum hmul
  rw [hmul, ← hsum, mul_div_cancel_left₀ _ hL.ne']

/-- Symmetry identity `ν_s(A'^{2k}) = ν_s(A_{n+1}^{2k})` when `n < N`: removing `Fin.last N` from
`Finset.Ici n` has the same `2k`-th moment as `Finset.Ici ⟨n + 1, ...⟩`. -/
private lemma integral_interpolating_partial_erase_last_eq_succ {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (n : Fin (N + 1)) (hn : n.1 < N) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ *
          ∑ i ∈ (Finset.Ici n).erase (Fin.last N),
            ((((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((N : ℝ) + 1)⁻¹ *
          ∑ i ∈ Finset.Ici (⟨n.1 + 1, by omega⟩ : Fin (N + 1)),
            ((((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
  intro P_g P_z P_z' P_s μ_s E_s
  let n' : Fin (N + 1) := ⟨n.1 + 1, by omega⟩
  let Θ (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ *
      ∑ j ∈ Finset.Ici n', (((τ 0 j : ℤ) : ℝ) * ((τ 1 j : ℤ) : ℝ) - q)) ^ (2 * k)
  have hperm := interpolating_replica_site_perm (L := N + 1) (M := M) (R := Fin 2) hu hB s q r
    (Equiv.swap n (Fin.last N)) Θ
  rw [← hperm]
  refine integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun σ => ?_))
  dsimp only [Θ]
  rw [← Finset.sum_Ici_erase_last_eq_sum_Ici_succ_swap n hn
    (fun i => ((((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q))]

/-! ### Induction step for `ν_s(A_n^{2k})` -/

/-- Numerical step in Eq. (2.97):
`16 * (2k + 1) / L * (64 k / L)^k ≤ ((2k + 1) / (4 (k + 1))) * (64 (k + 1) / L)^{k + 1}`. -/
private lemma overlap_high_moment_decoupled_arith (k : ℕ) {L : ℝ} (hL : 0 < L) :
    16 * (2 * (k : ℝ) + 1) / L * (64 * (k : ℝ) / L) ^ k ≤
      (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpow : (64 * (k : ℝ) / L) ^ k ≤ (64 * ((k : ℝ) + 1) / L) ^ k :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hL.le) k
  calc 16 * (2 * (k : ℝ) + 1) / L * (64 * (k : ℝ) / L) ^ k
      ≤ 16 * (2 * (k : ℝ) + 1) / L * (64 * ((k : ℝ) + 1) / L) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
        rw [pow_succ]
        field_simp
        ring

/-- Numerical step for the `1 / (N + 1)` remainder in Eq. (2.98):
`(1 / (4 L)) * (64 k / L)^k ≤ (1 / (256 (k + 1))) * (64 (k + 1) / L)^{k + 1}`. -/
private lemma overlap_high_moment_rem_arith (k : ℕ) {L : ℝ} (hL : 0 < L) :
    (1 / (4 * L)) * (64 * (k : ℝ) / L) ^ k ≤
      (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpow : (64 * (k : ℝ) / L) ^ k ≤ (64 * ((k : ℝ) + 1) / L) ^ k :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hL.le) k
  calc (1 / (4 * L)) * (64 * (k : ℝ) / L) ^ k
      ≤ (1 / (4 * L)) * (64 * ((k : ℝ) + 1) / L) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
        rw [pow_succ]
        field_simp
        ring

/-- **One-step estimate Eq. (2.98) for a single partial sum `A_n` (`n < N`) at `M + 1`
constraints:** assuming `ν_s(A_m^{2k}) ≤ (64 k / (N + 1))^k` for all `m`, `ν_s(A_n^{2k+2})`
satisfies
`ν_s(A_n^{2k+2}) ≤ (1/4) ν_s(A_n^{2k+2}) + (1/4) ν_s(A_0^{2k+2}) + (1/2) (64(k+1)/(N+1))^{k+1}`. -/
private lemma integral_interpolating_partial_overlap_step_lt
    {D K_der K_dom : ℝ}
    (h_der : ∀ (N M : ℕ) {s t q : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
      q ∈ Icc (0 : ℝ) 1 → ∀ (r : ℝ) {u : ℝ → ℝ},
      (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
      (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
      ∀ (f : (Fin 2 → PerceptronSpin N) → ℝ) {p₁ p₂ : ℝ}, p₁.HolderConjugate p₂ →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let d_spin (σ τ : PerceptronSpin N) : ℝ :=
        |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
          ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
      let rhat := perceptronRhat u q
      let v : ℝ≥0 := (s * (α * rhat)).toNNReal
      let P := interpSPDisorder N (M + 1) v
      let μ (ω : InterpSPDisorder N (M + 1)) :=
        (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)
      ∃ d',
        HasDerivAt
          (fun t' => ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), f (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t' q r ω)) ∂P)
          d' t ∧
        |d'| ≤ α * K_der *
          ((∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
              |f (fun l => (x l).1)| ^ p₁ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) ^ (1 / p₁) *
            (∫ ω, ∫ a : Fin 2 → InterpSPState N (M + 1),
              d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) ^ (1 / p₂) +
            1 / (N + 1) *
              ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
                |f (fun l => (x l).1)| ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P))
    (h_dom : ∀ (N M : ℕ) {s t q : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      q ∈ Icc (0 : ℝ) 1 → ∀ (r : ℝ) {u : ℝ → ℝ},
      (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
      (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
      ((M : ℝ) + 1) / ((N : ℝ) + 1) * K_dom ≤ 1 →
      ∀ (F : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ), (∀ σ, 0 ≤ F σ) →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let rhat := perceptronRhat u q
      let v : ℝ≥0 := (s * (α * rhat)).toNNReal
      let P_g := Measure.pi fun _ : Fin (M + 1) =>
        Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
      let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
      let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
      let P_s := (P_g.prod P_z).prod P_z'
      let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
      let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
          (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
        (∑ j : Fin (M + 1), u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
      (∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          F (fun l => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x l).1.1 (x l).1.2)
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω))
          ∂(interpSPDisorder N (M + 1) v)) ≤
        2 * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ), F (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s)
    {N M : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    {q r : ℝ} (hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
    (hr : r = (((M : ℝ) + 1) / ((N : ℝ) + 1)) * perceptronRhat u q)
    (hα_dom : ((M : ℝ) + 1) / ((N : ℝ) + 1) * K_dom ≤ 1)
    (hα_der : ((M : ℝ) + 1) / ((N : ℝ) + 1) * (32 * K_der) ≤ 1)
    {k : ℕ} (n : Fin (N + 1)) (hn : n.1 < N) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A_fn (m : Fin (N + 1)) (x y : Fin (N + 1) → ℤˣ) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.Ici m, (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)
    (∀ m : Fin (N + 1),
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          A_fn m (σ 0).1 (σ 1).1 ^ (2 * k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
        (64 * (k : ℝ) / ((N : ℝ) + 1)) ^ k) →
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        A_fn n (σ 0).1 (σ 1).1 ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      (1 / 4) * (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          A_fn n (σ 0).1 (σ 1).1 ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) +
      (1 / 4) * (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          A_fn 0 (σ 0).1 (σ 1).1 ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) +
      (1 / 2) * (64 * ((k : ℝ) + 1) / ((N : ℝ) + 1)) ^ (k + 1) := by
  intro P_g P_z P_z' P_s μ_s E_s A_fn ih
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let L : ℝ := (N : ℝ) + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  let α : ℝ := ((M : ℝ) + 1) / L
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  let rhat := perceptronRhat u q
  have hrhat0 : 0 ≤ rhat := perceptronRhat_nonneg u q
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 hrhat0
  let v : ℝ≥0 := (s * (α * rhat)).toNNReal
  have hv_sr : v = (s * r).toNNReal := by rw [hr]
  let P_sp := interpSPDisorder N (M + 1) v
  let snoc_pair (a : Fin 2 → PerceptronSpin N) (l : Fin 2) : Fin (N + 1) → ℤˣ :=
    Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (a l).1 (a l).2
  let A_sp (a : Fin 2 → PerceptronSpin N) : ℝ :=
    A_fn n (snoc_pair a 0) (snoc_pair a 1)
  let A'_full (x y : Fin (N + 1) → ℤˣ) : ℝ :=
    L⁻¹ * ∑ i ∈ (Finset.Ici n).erase (Fin.last N), (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)
  let A'_old (ρ : Fin 2 → Fin N → ℤˣ) : ℝ :=
    L⁻¹ * ∑ i ∈ Finset.Ici (⟨n.1, hn⟩ : Fin N), (((ρ 0 i : ℤ) : ℝ) * ((ρ 1 i : ℤ) : ℝ) - q)
  have hA'_snoc (a : Fin 2 → PerceptronSpin N) :
      A'_old (fun l => (a l).1) = A'_full (snoc_pair a 0) (snoc_pair a 1) := by
    dsimp only [A'_old, A'_full, snoc_pair]
    congr 1
    refine Finset.sum_bij (fun i _ => i.castSucc) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Ici] at hi
      rw [Finset.mem_erase, Finset.mem_Ici]
      exact ⟨Fin.castSucc_ne_last i, hi⟩
    · intro i₁ _ i₂ _ h
      exact Fin.castSucc_injective N h
    · intro j hj
      rw [Finset.mem_erase, Finset.mem_Ici] at hj
      rcases Fin.eq_castSucc_of_ne_last hj.1 with ⟨i, rfl⟩
      exact ⟨i, Finset.mem_Ici.2 hj.2, rfl⟩
    · intro i _
      simp [Fin.snoc_castSucc]
  have hA_diff (a : Fin 2 → PerceptronSpin N) :
      A_sp a - A'_old (fun l => (a l).1) =
        L⁻¹ * ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q) := by
    rw [hA'_snoc a]
    dsimp only [A_sp, A_fn, A'_full, snoc_pair, L]
    have hlast_in : Fin.last N ∈ Finset.Ici n := Finset.mem_Ici.2 (Fin.le_last n)
    rw [← mul_sub, ← Finset.sum_erase_add (Finset.Ici n) _ hlast_in]
    simp only [Fin.snoc_last]
    ring
  let f_sp (a : Fin 2 → PerceptronSpin N) : ℝ :=
    ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q) * A_sp a ^ (2 * k + 1)
  let g_path (t : ℝ) : ℝ :=
    ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), f_sp (fun l => (x l).1)
      ∂(Measure.pi fun _ : Fin 2 =>
        (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)) ∂P_sp
  let V_n : ℝ :=
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      A_fn n (σ 0).1 (σ 1).1 ^ (2 * k + 2)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s
  let V_0 : ℝ :=
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      A_fn 0 (σ 0).1 (σ 1).1 ^ (2 * k + 2)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s
  have hVn0 : 0 ≤ V_n :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _
  have hV00 : 0 ≤ V_0 :=
    integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _
  -- Step 1: V_n ≤ g_path 1 via site symmetry on Ici n
  have hVn_le_g1 : V_n ≤ g_path 1 := by
    have hsym := integral_interpolating_partial_overlap_succ_eq_last (N := N) (M := M + 1)
      hu.measurable (fun x => hu.le x) s q r n k
    let F_last (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
      (((τ 0 (Fin.last N) : ℤ) : ℝ) * ((τ 1 (Fin.last N) : ℤ) : ℝ) - q) *
        A_fn n (τ 0) (τ 1) ^ (2 * k + 1)
    have hsnoc_f (a : Fin 2 → PerceptronSpin N) : f_sp a = F_last (snoc_pair a) := by
      dsimp only [f_sp, F_last, A_sp, snoc_pair]
      simp only [Fin.snoc_last]
    have hg1 : g_path 1 =
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          ((((σ 0).1 (Fin.last N) : ℤ) : ℝ) * (((σ 1).1 (Fin.last N) : ℤ) : ℝ) - q) *
            A_fn n (σ 0).1 (σ 1).1 ^ (2 * k + 1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s := by
      dsimp only [g_path]
      simp_rw [hsnoc_f]
      exact integral_interpSP_one_eq (N := N) (M := M + 1) hu.measurable (fun x => hu.le x)
        s q r v F_last
    have hVn_eq : V_n = (((Finset.Ici n).card : ℝ) / L) * g_path 1 := by
      rw [hg1]
      exact hsym
    rw [hVn_eq]
    have hcard_pos : 0 < ((Finset.Ici n).card : ℝ) / L := by
      have hne : (Finset.Ici n).Nonempty := ⟨n, Finset.mem_Ici.2 le_rfl⟩
      have hcp : (0 : ℝ) < (Finset.Ici n).card := by exact_mod_cast hne.card_pos
      exact div_pos hcp hL
    have hcard_le : ((Finset.Ici n).card : ℝ) / L ≤ 1 := by
      rw [div_le_one hL]
      have hc : (Finset.Ici n).card ≤ Fintype.card (Fin (N + 1)) := (Finset.Ici n).card_le_univ
      rw [Fintype.card_fin] at hc
      dsimp only [L]
      exact_mod_cast hc
    have hg1_nn : 0 ≤ g_path 1 := by
      have : 0 ≤ ((Finset.Ici n).card : ℝ) / L * g_path 1 := by rw [← hVn_eq]; exact hVn0
      exact nonneg_of_mul_nonneg_right this hcard_pos
    exact mul_le_of_le_one_left hg1_nn hcard_le
  -- Step 2: |g_path 0| ≤ ((2k + 1) / (4(k + 1))) * (64(k + 1) / L)^{k + 1} (Eq. (2.97))
  have hg0_le : |g_path 0| ≤
      (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
    have hdec0 : ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
        ((((x 0).1.2 : ℤ) : ℝ) * (((x 1).1.2 : ℤ) : ℝ) - q) *
          (A'_old (fun l => (x l).1.1) ^ (2 * k + 1))
        ∂(Measure.pi fun _ : Fin 2 =>
          (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp = 0 := by
      dsimp only [P_sp]
      rw [hv_sr]
      exact integral_interpSP_zero_old_spin_mul_sub_eq_zero (N := N) (M := M + 1)
        hu.measurable (fun x => hu.le x) hs hr0 hq (fun ρ => A'_old ρ ^ (2 * k + 1))
    let f_diff (a : Fin 2 → PerceptronSpin N) : ℝ :=
      ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q) *
        (A_sp a ^ (2 * k + 1) - A'_old (fun l => (a l).1) ^ (2 * k + 1))
    have hg0_eq_diff : g_path 0 = ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
        f_diff (fun l => (x l).1)
        ∂(Measure.pi fun _ : Fin 2 =>
          (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp := by
      obtain ⟨C₁, hC₁⟩ := exists_abs_le_of_finite f_sp
      let f_old_sp (a : Fin 2 → PerceptronSpin N) : ℝ :=
        ((((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q) *
          (A'_old (fun l => (a l).1) ^ (2 * k + 1))
      obtain ⟨C₂, hC₂⟩ := exists_abs_le_of_finite f_old_sp
      have hμ0 (ω : InterpSPDisorder N (M + 1)) :
          IsProbabilityMeasure ((interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) :=
        isProbabilityMeasure_tilted_interpSPEnergy hu.measurable (fun x => hu.le x) s 0 q r ω
      have hint_sp {G : (Fin 2 → PerceptronSpin N) → ℝ} {C' : ℝ} (hC' : ∀ a, |G a| ≤ C') :
          Integrable (fun ω => ∫ x : Fin 2 → InterpSPState N (M + 1), G (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω))) P_sp := by
        let F_obs (_ : InterpSPDisorder N (M + 1)) (x : Fin 2 → InterpSPState N (M + 1)) : ℝ :=
          G (fun l => (x l).1)
        have hFm : Measurable fun p : InterpSPDisorder N (M + 1) ×
            (Fin 2 → InterpSPState N (M + 1)) => F_obs p.1 p.2 :=
          (measurable_of_finite G).comp (measurable_pi_iff.2 fun l =>
            measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))
        have hm_E : Measurable fun p : InterpSPDisorder N (M + 1) × InterpSPState N (M + 1) =>
            interpSPEnergy u s 0 q r p.1 p.2 := by
          unfold interpSPEnergy interpSPField
          simp only [smartPathFieldNoAux_eq]
          refine ((Finset.measurable_sum _ fun j _ =>
            hu.measurable.comp (by fun_prop)).add ?_).add ?_
          · fun_prop
          · fun_prop
        have hm_int := measurable_integral_pi_tilted (μ := interpSPBase N (M + 1)) hm_E hFm
        exact Integrable.of_bound hm_int.aestronglyMeasurable
          |C'| (ae_of_all _ fun _ => by
            rw [Real.norm_eq_abs]
            exact abs_integral_le_of_forall_abs_le _ fun _ => (hC' _).trans (le_abs_self _))
      have hin_sp {G : (Fin 2 → PerceptronSpin N) → ℝ} {C' : ℝ} (hC' : ∀ a, |G a| ≤ C')
          (ω : InterpSPDisorder N (M + 1)) :
          Integrable (fun x : Fin 2 → InterpSPState N (M + 1) => G (fun l => (x l).1))
            (Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) :=
        Integrable.of_bound
          ((measurable_of_finite G).comp (measurable_pi_iff.2 fun l =>
            measurable_fst.comp (measurable_pi_apply l))).aestronglyMeasurable
          |C'| (ae_of_all _ fun _ => by rw [Real.norm_eq_abs]; exact (hC' _).trans (le_abs_self _))
      have hpt_sub (ω : InterpSPDisorder N (M + 1)) :
          ∫ x : Fin 2 → InterpSPState N (M + 1), f_diff (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) =
          (∫ x : Fin 2 → InterpSPState N (M + 1), f_sp (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω))) -
          (∫ x : Fin 2 → InterpSPState N (M + 1), f_old_sp (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω))) := by
        have heq_f (x : Fin 2 → InterpSPState N (M + 1)) :
            f_diff (fun l => (x l).1) = f_sp (fun l => (x l).1) - f_old_sp (fun l => (x l).1) := by
          dsimp only [f_diff, f_sp, f_old_sp]; ring
        simp_rw [heq_f]
        exact integral_sub (hin_sp hC₁ ω) (hin_sp hC₂ ω)
      symm
      simp_rw [hpt_sub]
      rw [integral_sub (hint_sp hC₁) (hint_sp hC₂)]
      dsimp only [f_old_sp, g_path]
      rw [hdec0, sub_zero]
    rw [hg0_eq_diff]
    let H_dom (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
      (4 * (2 * (k : ℝ) + 1) / L) *
        (A_fn n (τ 0) (τ 1) ^ (2 * k) + A'_full (τ 0) (τ 1) ^ (2 * k))
    have hH_nn (τ : Fin 2 → Fin (N + 1) → ℤˣ) : 0 ≤ H_dom τ := by
      dsimp only [H_dom]
      exact mul_nonneg (by positivity)
        (add_nonneg (Even.pow_nonneg ⟨k, by ring⟩ _) (Even.pow_nonneg ⟨k, by ring⟩ _))
    have hf_diff_le (a : Fin 2 → PerceptronSpin N) :
        |f_diff a| ≤ H_dom (snoc_pair a) := by
      dsimp only [f_diff, H_dom]
      rw [abs_mul]
      have heps : |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| ≤ 2 :=
        abs_units_cast_mul_sub_le_two (a 0).2 (a 1).2 hq_mem
      have hsub_le : |A_sp a - A'_old (fun l => (a l).1)| ≤ 2 / L := by
        rw [hA_diff a, abs_mul, abs_of_pos (inv_pos.2 hL)]
        calc L⁻¹ * |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q|
            ≤ L⁻¹ * 2 := mul_le_mul_of_nonneg_left heps (inv_pos.2 hL).le
          _ = 2 / L := by ring
      have hodd := abs_pow_odd_sub_pow_odd_le k (A_sp a) (A'_old (fun l => (a l).1))
      have hodd' : |A_sp a ^ (2 * k + 1) - A'_old (fun l => (a l).1) ^ (2 * k + 1)| ≤
          (2 * (k : ℝ) + 1) * (2 / L) *
            (A_sp a ^ (2 * k) + A'_full (snoc_pair a 0) (snoc_pair a 1) ^ (2 * k)) := by
        calc |A_sp a ^ (2 * k + 1) - A'_old (fun l => (a l).1) ^ (2 * k + 1)|
            ≤ (2 * (k : ℝ) + 1) * |A_sp a - A'_old (fun l => (a l).1)| *
                (A_sp a ^ (2 * k) + A'_old (fun l => (a l).1) ^ (2 * k)) := hodd
          _ ≤ (2 * (k : ℝ) + 1) * (2 / L) *
                (A_sp a ^ (2 * k) + A'_old (fun l => (a l).1) ^ (2 * k)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsub_le (by positivity))
                (add_nonneg (Even.pow_nonneg ⟨k, by ring⟩ _) (Even.pow_nonneg ⟨k, by ring⟩ _))
          _ = (2 * (k : ℝ) + 1) * (2 / L) *
                (A_sp a ^ (2 * k) + A'_full (snoc_pair a 0) (snoc_pair a 1) ^ (2 * k)) := by
              rw [hA'_snoc a]
      calc |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| *
            |A_sp a ^ (2 * k + 1) - A'_old (fun l => (a l).1) ^ (2 * k + 1)|
          ≤ 2 * ((2 * (k : ℝ) + 1) * (2 / L) *
              (A_sp a ^ (2 * k) + A'_full (snoc_pair a 0) (snoc_pair a 1) ^ (2 * k))) :=
            mul_le_mul heps hodd' (abs_nonneg _) zero_le_two
        _ = (4 * (2 * (k : ℝ) + 1) / L) *
              (A_fn n (snoc_pair a 0) (snoc_pair a 1) ^ (2 * k) +
                A'_full (snoc_pair a 0) (snoc_pair a 1) ^ (2 * k)) := by
            dsimp only [A_sp]; ring
    have habs_int :
        |∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), f_diff (fun l => (x l).1)
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp| ≤
        ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), H_dom (snoc_pair (fun l => (x l).1))
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp := by
      have hm1 := integral_interpSP_mono (N := N) (M := M + 1) hu.measurable (fun x => hu.le x)
        s 0 q r v (G₁ := f_diff) (G₂ := fun a => H_dom (snoc_pair a))
        (fun a => (le_abs_self _).trans (hf_diff_le a))
      have hm2 := integral_interpSP_mono (N := N) (M := M + 1) hu.measurable (fun x => hu.le x)
        s 0 q r v (G₁ := fun a => -H_dom (snoc_pair a)) (G₂ := f_diff)
        (fun a => neg_le_of_abs_le (hf_diff_le a))
      have hneg_pull : (∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          -H_dom (snoc_pair (fun l => (x l).1))
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp) =
        -∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          H_dom (snoc_pair (fun l => (x l).1))
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp := by
        simp only [integral_neg]
      rw [hneg_pull] at hm2
      exact abs_le.2 ⟨hm2, hm1⟩
    have hdom0 := h_dom N M hs ⟨le_rfl, zero_le_one⟩ hq_mem r hd hb hα_dom H_dom hH_nn
    have hH_end : ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        H_dom (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      (8 * (2 * (k : ℝ) + 1) / L) * (64 * (k : ℝ) / L) ^ k := by
      let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
      have hP_prob : IsProbabilityMeasure P_s := by
        dsimp only [P_s, P_g, P_z, P_z']; infer_instance
      have hE_m : Measurable fun p : Ω × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => E_s p.1 p.2 :=
        measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
      have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
          E_s ω x ≤ (M + 1 : ℕ) * D +
            ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
        refine add_le_add ((Finset.sum_le_sum fun _ _ => hu.le _).trans_eq (by simp))
          (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
      have hν_prob (ω : Ω) : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
        isProbabilityMeasure_tilted_of_ae_le
          (Measurable.of_uncurry_left hE_m).aemeasurable (ae_of_all _ (hEb ω))
      have hint_spin (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) :
          Integrable (fun ω : Ω => ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
            Φ (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) P_s := by
        obtain ⟨C, hC⟩ := exists_abs_le_of_finite Φ
        have hGm : Measurable fun p : Ω × (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
            Φ (fun l => (p.2 l).1) :=
          (measurable_of_finite Φ).comp (measurable_pi_iff.2 fun l =>
            measurable_fst.comp ((measurable_pi_apply l).comp measurable_snd))
        exact integrable_integral_pi_tilted (P := P_s) (μ := μ_s) hE_m hν_prob
          (G := fun _ σ => Φ (fun l => (σ l).1)) hGm (M := C) (fun _ _ => hC _)
      have hin_spin (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) (ω : Ω) :
          Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
            Φ (fun l => (σ l).1)) (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
        obtain ⟨C, hC⟩ := exists_abs_le_of_finite Φ
        exact Integrable.of_bound
          ((measurable_of_finite Φ).comp (measurable_pi_iff.2 fun l =>
            measurable_fst.comp (measurable_pi_apply l))).aestronglyMeasurable
          C (ae_of_all _ fun _ => by rw [Real.norm_eq_abs]; exact hC _)
      let Φ₁ (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ := A_fn n (τ 0) (τ 1) ^ (2 * k)
      let Φ₂ (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ := A'_full (τ 0) (τ 1) ^ (2 * k)
      have hpt_H (ω : Ω) :
          ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
            H_dom (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) =
          (4 * (2 * (k : ℝ) + 1) / L) *
            ((∫ σ, Φ₁ (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) +
             (∫ σ, Φ₂ (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)))) := by
        dsimp only [H_dom, Φ₁, Φ₂]
        rw [integral_const_mul, integral_add (hin_spin Φ₁ ω) (hin_spin Φ₂ ω)]
      simp_rw [hpt_H]
      rw [integral_const_mul, integral_add (hint_spin Φ₁) (hint_spin Φ₂)]
      have h1_ih : (∫ ω, ∫ σ, Φ₁ (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) ≤
          (64 * (k : ℝ) / L) ^ k := ih n
      have h2_eq := integral_interpolating_partial_erase_last_eq_succ (N := N) (M := M + 1)
        hu.measurable (fun x => hu.le x) s q r n hn k
      have h2_ih : (∫ ω, ∫ σ, Φ₂ (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) ≤
          (64 * (k : ℝ) / L) ^ k := by
        dsimp only [Φ₂, A'_full, L]
        rw [h2_eq]
        exact ih ⟨n.1 + 1, by omega⟩
      calc (4 * (2 * (k : ℝ) + 1) / L) * _
          ≤ (4 * (2 * (k : ℝ) + 1) / L) * ((64 * (k : ℝ) / L) ^ k + (64 * (k : ℝ) / L) ^ k) :=
            mul_le_mul_of_nonneg_left (add_le_add h1_ih h2_ih) (by positivity)
        _ = (8 * (2 * (k : ℝ) + 1) / L) * (64 * (k : ℝ) / L) ^ k := by ring
    calc |∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), f_diff (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s 0 q r ω)) ∂P_sp|
        ≤ 2 * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
            H_dom (fun l => (σ l).1) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s :=
          habs_int.trans hdom0
      _ ≤ 2 * ((8 * (2 * (k : ℝ) + 1) / L) * (64 * (k : ℝ) / L) ^ k) :=
          mul_le_mul_of_nonneg_left hH_end zero_le_two
      _ = 16 * (2 * (k : ℝ) + 1) / L * (64 * (k : ℝ) / L) ^ k := by ring
      _ ≤ (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) :=
          overlap_high_moment_decoupled_arith k hL
  -- Step 3: Derivative bound |g_path' t| along t ∈ (0, 1) with τ₁ = (2k+2)/(2k+1), τ₂ = 2k+2
  let τ₁ : ℝ := (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1)
  let τ₂ : ℝ := 2 * (k : ℝ) + 2
  have hτ_conj : τ₁.HolderConjugate τ₂ := by
    have hm_pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have hc := Real.HolderConjugate.succ_div_self hm_pos
    simpa only [τ₁, τ₂, show (2 * (k : ℝ) + 1) + 1 = 2 * (k : ℝ) + 2 by ring] using hc
  let B_der : ℝ :=
    (1 / 4) * V_n + (1 / 4) * V_0 +
      (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1)
  have hg_deriv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      ∃ d', HasDerivAt g_path d' t ∧ |d'| ≤ B_der := by
    obtain ⟨d', hd', hbd⟩ := h_der N M hs ht hq_mem r hd hb f_sp hτ_conj
    refine ⟨d', hd', hbd.trans ?_⟩
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let μ_t (ω : InterpSPDisorder N (M + 1)) :=
      (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)
    let A_t : ℝ := ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
      |f_sp (fun l => (x l).1)| ^ τ₁ ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp
    let B_t : ℝ := ∫ ω, ∫ a : Fin 2 → InterpSPState N (M + 1),
      d_spin (a 0).1 (a 1).1 ^ τ₂ ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp
    let I_t : ℝ := ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
      |f_sp (fun l => (x l).1)| ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp
    have hAt0 : 0 ≤ A_t :=
      integral_nonneg fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    have hBt0 : 0 ≤ B_t :=
      integral_nonneg fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    have hf_pow_le (a : Fin 2 → PerceptronSpin N) :
        |f_sp a| ^ τ₁ ≤ (2 : ℝ) ^ τ₁ * A_sp a ^ (2 * k + 2) := by
      dsimp only [f_sp]
      rw [abs_mul, abs_pow]
      have heps : |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| ≤ 2 :=
        abs_units_cast_mul_sub_le_two (a 0).2 (a 1).2 hq_mem
      have h1 : (|(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| * |A_sp a| ^ (2 * k + 1)) ^ τ₁ ≤
          (2 * |A_sp a| ^ (2 * k + 1)) ^ τ₁ :=
        Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right heps (by positivity)) hτ_conj.pos.le
      have h2 : (2 * |A_sp a| ^ (2 * k + 1)) ^ τ₁ = (2 : ℝ) ^ τ₁ * A_sp a ^ (2 * k + 2) := by
        rw [Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_natCast |A_sp a| (2 * k + 1),
          ← Real.rpow_mul (abs_nonneg _)]
        have hexp : ((2 * k + 1 : ℕ) : ℝ) * τ₁ = ((2 * k + 2 : ℕ) : ℝ) := by
          dsimp only [τ₁]
          have hne : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
          push_cast; field_simp
        rw [hexp, Real.rpow_natCast, Even.pow_abs ⟨k + 1, by ring⟩]
      exact h1.trans_eq h2
    have hAt_le : A_t ≤ (2 : ℝ) ^ τ₁ * (2 * V_n) := by
      have hm := integral_interpSP_mono (N := N) (M := M + 1) hu.measurable (fun x => hu.le x)
        s t q r v (G₁ := fun a => |f_sp a| ^ τ₁)
        (G₂ := fun a => (2 : ℝ) ^ τ₁ * A_sp a ^ (2 * k + 2)) hf_pow_le
      have hpull : (∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          (2 : ℝ) ^ τ₁ * A_sp (fun l => (x l).1) ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp) =
        (2 : ℝ) ^ τ₁ * ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          A_fn n (snoc_pair (fun l => (x l).1) 0) (snoc_pair (fun l => (x l).1) 1) ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp := by
        dsimp only [A_sp]
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun _ => by dsimp only; rw [integral_const_mul])
      have hd_Vn := h_dom N M hs ⟨ht.1.le, ht.2.le⟩ hq_mem r hd hb hα_dom
        (fun τ => A_fn n (τ 0) (τ 1) ^ (2 * k + 2))
        (fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _)
      exact (hm.trans_eq hpull).trans (mul_le_mul_of_nonneg_left hd_Vn (by positivity))
    have hAt_rpow : A_t ^ (1 / τ₁) ≤ 4 * V_n ^ (1 / τ₁) := by
      have h2_rpow : (2 : ℝ) ^ (1 / τ₁) ≤ 2 := by
        have h1_le : 1 / τ₁ ≤ 1 := by
          rw [div_le_one hτ_conj.pos]; exact hτ_conj.lt.le
        calc (2 : ℝ) ^ (1 / τ₁) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two h1_le
          _ = 2 := Real.rpow_one 2
      calc A_t ^ (1 / τ₁)
          ≤ ((2 : ℝ) ^ τ₁ * (2 * V_n)) ^ (1 / τ₁) :=
            Real.rpow_le_rpow hAt0 hAt_le (div_nonneg zero_le_one hτ_conj.pos.le)
        _ = ((2 : ℝ) ^ τ₁) ^ (1 / τ₁) * (2 : ℝ) ^ (1 / τ₁) * V_n ^ (1 / τ₁) := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow zero_le_two hVn0, mul_assoc]
        _ = 2 * (2 : ℝ) ^ (1 / τ₁) * V_n ^ (1 / τ₁) := by
            rw [← Real.rpow_mul zero_le_two, mul_one_div_cancel hτ_conj.ne_zero, Real.rpow_one]
        _ ≤ 2 * 2 * V_n ^ (1 / τ₁) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2_rpow zero_le_two)
              (Real.rpow_nonneg hVn0 _)
        _ = 4 * V_n ^ (1 / τ₁) := by ring
    have hBt_le : B_t ≤ 2 * V_0 := by
      have hBt_eq : B_t = ∫ ω, ∫ a : Fin 2 → InterpSPState N (M + 1),
          A_fn 0 (snoc_pair (fun l => (a l).1) 0) (snoc_pair (fun l => (a l).1) 1) ^ (2 * k + 2)
          ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp := by
        refine integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun a => ?_))
        have hτ2_nat : τ₂ = ((2 * k + 2 : ℕ) : ℝ) := by dsimp only [τ₂]; push_cast; ring
        calc d_spin (a 0).1 (a 1).1 ^ τ₂
            = d_spin (a 0).1 (a 1).1 ^ ((2 * k + 2 : ℕ) : ℝ) := by rw [hτ2_nat]
          _ = d_spin (a 0).1 (a 1).1 ^ (2 * k + 2) := Real.rpow_natCast _ _
          _ = A_fn 0 (snoc_pair (fun l => (a l).1) 0)
                (snoc_pair (fun l => (a l).1) 1) ^ (2 * k + 2) := by
              dsimp only [d_spin, A_fn, snoc_pair]
              rw [Even.pow_abs ⟨k + 1, by ring⟩]
              congr 1
              have hIci0 : (Finset.Ici (0 : Fin (N + 1))) = Finset.univ := by ext i; simp
              rw [hIci0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul, Fin.sum_univ_castSucc]
              simp only [Fin.snoc_castSucc, Fin.snoc_last]
              have hL_ne : ((N : ℝ) + 1) ≠ 0 := by positivity
              push_cast; field_simp
      rw [hBt_eq]
      exact h_dom N M hs ⟨ht.1.le, ht.2.le⟩ hq_mem r hd hb hα_dom
        (fun τ => A_fn 0 (τ 0) (τ 1) ^ (2 * k + 2))
        (fun _ => Even.pow_nonneg ⟨k + 1, by ring⟩ _)
    have hBt_rpow : B_t ^ (1 / τ₂) ≤ 2 * V_0 ^ (1 / τ₂) := by
      have h2_rpow : (2 : ℝ) ^ (1 / τ₂) ≤ 2 := by
        have h1_le : 1 / τ₂ ≤ 1 := by
          rw [div_le_one hτ_conj.symm.pos]; exact hτ_conj.symm.lt.le
        calc (2 : ℝ) ^ (1 / τ₂) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two h1_le
          _ = 2 := Real.rpow_one 2
      calc B_t ^ (1 / τ₂)
          ≤ (2 * V_0) ^ (1 / τ₂) :=
            Real.rpow_le_rpow hBt0 hBt_le (div_nonneg zero_le_one hτ_conj.symm.pos.le)
        _ = (2 : ℝ) ^ (1 / τ₂) * V_0 ^ (1 / τ₂) := Real.mul_rpow zero_le_two hV00
        _ ≤ 2 * V_0 ^ (1 / τ₂) :=
            mul_le_mul_of_nonneg_right h2_rpow (Real.rpow_nonneg hV00 _)
    have hprod_le : A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂) ≤ 8 * (V_n + V_0) := by
      calc A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂)
          ≤ (4 * V_n ^ (1 / τ₁)) * (2 * V_0 ^ (1 / τ₂)) :=
            mul_le_mul hAt_rpow hBt_rpow (Real.rpow_nonneg hBt0 _) (by positivity)
        _ = 8 * (V_n ^ (1 / τ₁) * V_0 ^ (1 / τ₂)) := by ring
        _ ≤ 8 * (V_n + V_0) :=
            mul_le_mul_of_nonneg_left (rpow_inv_mul_rpow_inv_le_add hτ_conj hVn0 hV00)
              (by norm_num)
    have hf_abs_le (a : Fin 2 → PerceptronSpin N) : |f_sp a| ≤ 4 * A_sp a ^ (2 * k) := by
      dsimp only [f_sp]
      rw [abs_mul, abs_pow, pow_succ, Even.pow_abs ⟨k, by ring⟩]
      have heps : |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| ≤ 2 :=
        abs_units_cast_mul_sub_le_two (a 0).2 (a 1).2 hq_mem
      have hA_le2 : |A_sp a| ≤ 2 :=
        abs_partial_overlap_sub_le_two hq_mem (Finset.Ici n) (snoc_pair a 0) (snoc_pair a 1)
      have hAn_nn : 0 ≤ A_sp a ^ (2 * k) := Even.pow_nonneg ⟨k, by ring⟩ _
      calc |(((a 0).2 : ℤ) : ℝ) * (((a 1).2 : ℤ) : ℝ) - q| * (A_sp a ^ (2 * k) * |A_sp a|)
          ≤ 2 * (A_sp a ^ (2 * k) * 2) :=
            mul_le_mul heps
              (mul_le_mul_of_nonneg_left hA_le2 hAn_nn)
              (mul_nonneg hAn_nn (abs_nonneg _)) zero_le_two
        _ = 4 * A_sp a ^ (2 * k) := by ring
    have hIt_le : I_t ≤ 8 * (64 * (k : ℝ) / L) ^ k := by
      have hm := integral_interpSP_mono (N := N) (M := M + 1) hu.measurable (fun x => hu.le x)
        s t q r v (G₁ := fun a => |f_sp a|) (G₂ := fun a => 4 * A_sp a ^ (2 * k)) hf_abs_le
      have hpull : (∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          4 * A_sp (fun l => (x l).1) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp) =
        4 * ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          A_fn n (snoc_pair (fun l => (x l).1) 0) (snoc_pair (fun l => (x l).1) 1) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin 2 => μ_t ω) ∂P_sp := by
        dsimp only [A_sp]
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun _ => by dsimp only; rw [integral_const_mul])
      have hd_2k := h_dom N M hs ⟨ht.1.le, ht.2.le⟩ hq_mem r hd hb hα_dom
        (fun τ => A_fn n (τ 0) (τ 1) ^ (2 * k))
        (fun _ => Even.pow_nonneg ⟨k, by ring⟩ _)
      calc I_t ≤ 4 * (2 * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
              A_fn n (σ 0).1 (σ 1).1 ^ (2 * k)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) :=
            (hm.trans_eq hpull).trans (mul_le_mul_of_nonneg_left hd_2k (by norm_num))
        _ ≤ 4 * (2 * (64 * (k : ℝ) / L) ^ k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih n) zero_le_two) (by norm_num)
        _ = 8 * (64 * (k : ℝ) / L) ^ k := by ring
    have hαK_le : α * K_der ≤ 1 / 32 := by linarith [hα_der]
    have hIt0 : 0 ≤ I_t := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
    have hrem_le : α * K_der * (1 / L * I_t) ≤
        (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by
      have hstep1 : α * K_der * (1 / L * I_t) ≤
          (1 / 32) * (1 / L * (8 * (64 * (k : ℝ) / L) ^ k)) :=
        mul_le_mul hαK_le (mul_le_mul_of_nonneg_left hIt_le (by positivity))
          (by positivity) (by norm_num)
      have hstep2 : (1 / 32) * (1 / L * (8 * (64 * (k : ℝ) / L) ^ k)) =
          (1 / (4 * L)) * (64 * (k : ℝ) / L) ^ k := by
        have hL_ne : L ≠ 0 := hL.ne'
        field_simp; ring
      exact (hstep1.trans_eq hstep2).trans (overlap_high_moment_rem_arith k hL)
    have hmain_le : α * K_der * (A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂)) ≤
        (1 / 4) * V_n + (1 / 4) * V_0 := by
      calc α * K_der * (A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂))
          ≤ (1 / 32) * (8 * (V_n + V_0)) :=
            mul_le_mul hαK_le hprod_le
              (mul_nonneg (Real.rpow_nonneg hAt0 _) (Real.rpow_nonneg hBt0 _)) (by norm_num)
        _ = (1 / 4) * V_n + (1 / 4) * V_0 := by ring
    dsimp only [B_der]
    calc α * K_der * (A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂) + 1 / (N + 1) * I_t)
        = α * K_der * (A_t ^ (1 / τ₁) * B_t ^ (1 / τ₂)) + α * K_der * (1 / L * I_t) := by
            dsimp only [L]; ring
      _ ≤ ((1 / 4) * V_n + (1 / 4) * V_0) +
            (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) :=
          add_le_add hmain_le hrem_le
      _ = (1 / 4) * V_n + (1 / 4) * V_0 +
            (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by ring
  -- Step 4: Combine V_n ≤ g_path 1 ≤ |g_path 0| + B_der
  have hg_cont : ContinuousOn g_path (Icc 0 1) :=
    continuousOn_integral_interpSP hu.continuous hu.abs_le s q r v f_sp
  have hinc : |g_path 1 - g_path 0| ≤ B_der := by
    have h := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hg_cont hg_deriv
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    simpa only [sub_zero, abs_one, mul_one] using h
  have hg1_le : g_path 1 ≤ |g_path 0| + B_der := by
    have h1 := (abs_le.1 hinc).2
    have h2 : g_path 0 ≤ |g_path 0| := le_abs_self _
    linarith
  have hcoef :
      (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) + 1 / (256 * ((k : ℝ) + 1)) ≤ 1 / 2 := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hpow_nn : 0 ≤ (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by positivity
  calc V_n ≤ g_path 1 := hVn_le_g1
    _ ≤ |g_path 0| + B_der := hg1_le
    _ ≤ (2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) +
          ((1 / 4) * V_n + (1 / 4) * V_0 +
            (1 / (256 * ((k : ℝ) + 1))) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1)) :=
        add_le_add hg0_le le_rfl
    _ = (1 / 4) * V_n + (1 / 4) * V_0 +
          ((2 * (k : ℝ) + 1) / (4 * ((k : ℝ) + 1)) + 1 / (256 * ((k : ℝ) + 1))) *
            (64 * ((k : ℝ) + 1) / L) ^ (k + 1) := by ring
    _ ≤ (1 / 4) * V_n + (1 / 4) * V_0 + (1 / 2) * (64 * ((k : ℝ) + 1) / L) ^ (k + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hpow_nn)

/-- **Induction over `k` for all partial sums `A_n` (`n : Fin (N + 1)`) at `M + 1` constraints
(Eq. (2.95)).** -/
private lemma integral_interpolating_partial_overlap_pow_le_succ_constraints
    {D K_der K_dom : ℝ}
    (h_der : ∀ (N M : ℕ) {s t q : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
      q ∈ Icc (0 : ℝ) 1 → ∀ (r : ℝ) {u : ℝ → ℝ},
      (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
      (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
      ∀ (f : (Fin 2 → PerceptronSpin N) → ℝ) {p₁ p₂ : ℝ}, p₁.HolderConjugate p₂ →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let d_spin (σ τ : PerceptronSpin N) : ℝ :=
        |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
          ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
      let rhat := perceptronRhat u q
      let v : ℝ≥0 := (s * (α * rhat)).toNNReal
      let P := interpSPDisorder N (M + 1) v
      let μ (ω : InterpSPDisorder N (M + 1)) :=
        (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω)
      ∃ d',
        HasDerivAt
          (fun t' => ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1), f (fun l => (x l).1)
            ∂(Measure.pi fun _ : Fin 2 =>
              (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t' q r ω)) ∂P)
          d' t ∧
        |d'| ≤ α * K_der *
          ((∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
              |f (fun l => (x l).1)| ^ p₁ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) ^ (1 / p₁) *
            (∫ ω, ∫ a : Fin 2 → InterpSPState N (M + 1),
              d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P) ^ (1 / p₂) +
            1 / (N + 1) *
              ∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
                |f (fun l => (x l).1)| ∂(Measure.pi fun _ : Fin 2 => μ ω) ∂P))
    (h_dom : ∀ (N M : ℕ) {s t q : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      q ∈ Icc (0 : ℝ) 1 → ∀ (r : ℝ) {u : ℝ → ℝ},
      (∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) →
      (∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D) →
      ((M : ℝ) + 1) / ((N : ℝ) + 1) * K_dom ≤ 1 →
      ∀ (F : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ), (∀ σ, 0 ≤ F σ) →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let rhat := perceptronRhat u q
      let v : ℝ≥0 := (s * (α * rhat)).toNNReal
      let P_g := Measure.pi fun _ : Fin (M + 1) =>
        Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
      let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
      let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
      let P_s := (P_g.prod P_z).prod P_z'
      let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
        (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
      let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
          (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
        (∑ j : Fin (M + 1), u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
      (∫ ω, ∫ x : Fin 2 → InterpSPState N (M + 1),
          F (fun l => Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) (x l).1.1 (x l).1.2)
          ∂(Measure.pi fun _ : Fin 2 =>
            (interpSPBase N (M + 1)).tilted (interpSPEnergy u s t q r ω))
          ∂(interpSPDisorder N (M + 1) v)) ≤
        2 * ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ), F (fun l => (σ l).1)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s)
    {N M : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    {q r : ℝ} (hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
    (hr : r = (((M : ℝ) + 1) / ((N : ℝ) + 1)) * perceptronRhat u q)
    (hα_dom : ((M : ℝ) + 1) / ((N : ℝ) + 1) * K_dom ≤ 1)
    (hα_der : ((M : ℝ) + 1) / ((N : ℝ) + 1) * (32 * K_der) ≤ 1)
    (k : ℕ) (n : Fin (N + 1)) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ j : Fin (M + 1), u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        (((N : ℝ) + 1)⁻¹ *
          ∑ i ∈ Finset.Ici n, ((((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      (64 * (k : ℝ) / ((N : ℝ) + 1)) ^ k := by
  intro P_g P_z P_z' P_s μ_s E_s
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let Ω := ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)
  have hP_prob : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
  have hE_m : Measurable fun p : Ω × ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => E_s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s ω x ≤ (M + 1 : ℕ) * D +
        ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hu.le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hμ_prob (ω : Ω) : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hE_m).aemeasurable (ae_of_all _ (hEb ω))
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  let A_fn (m : Fin (N + 1)) (x y : Fin (N + 1) → ℤˣ) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i ∈ Finset.Ici m, (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)
  have hall : ∀ k' : ℕ, ∀ m : Fin (N + 1),
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        A_fn m (σ 0).1 (σ 1).1 ^ (2 * k')
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      (64 * (k' : ℝ) / ((N : ℝ) + 1)) ^ k' := by
    intro k'
    induction k' with
    | zero =>
      intro m
      simp
    | succ k' ih =>
      have hlast_bound :
          ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
            A_fn (Fin.last N) (σ 0).1 (σ 1).1 ^ (2 * (k' + 1))
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
          (64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)) ^ (k' + 1) := by
        have hpt_last (x y : Fin (N + 1) → ℤˣ) :
            A_fn (Fin.last N) x y ^ (2 * (k' + 1)) ≤
              (64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)) ^ (k' + 1) := by
          have hIci_last : Finset.Ici (Fin.last N) = {Fin.last N} := by
            ext i
            simp only [Finset.mem_Ici, Finset.mem_singleton]
            exact ⟨fun h => le_antisymm (Fin.le_last i) h, fun h => by rw [h]⟩
          have habs_last : |A_fn (Fin.last N) x y| ≤ 2 / ((N : ℝ) + 1) := by
            dsimp only [A_fn]
            rw [hIci_last, Finset.sum_singleton, abs_mul,
              abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1))]
            calc ((N : ℝ) + 1)⁻¹ * |((x (Fin.last N) : ℤ) : ℝ) * ((y (Fin.last N) : ℤ) : ℝ) - q|
                ≤ ((N : ℝ) + 1)⁻¹ * 2 :=
                  mul_le_mul_of_nonneg_left
                    (abs_units_cast_mul_sub_le_two _ _ hq_mem) (by positivity)
              _ = 2 / ((N : ℝ) + 1) := by ring
          have hsq : A_fn (Fin.last N) x y ^ 2 ≤ 64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) := by
            rw [← sq_abs]
            calc |A_fn (Fin.last N) x y| ^ 2
                ≤ (2 / ((N : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs_last 2
              _ = 4 / (((N : ℝ) + 1) * ((N : ℝ) + 1)) := by
                  rw [div_pow]; ring
              _ ≤ 4 / ((N : ℝ) + 1) := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
              _ ≤ 64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) := by
                  refine div_le_div_of_nonneg_right ?_ (by positivity)
                  have hk1 : (1 : ℝ) ≤ (k' + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k'
                  linarith
          calc A_fn (Fin.last N) x y ^ (2 * (k' + 1))
              = (A_fn (Fin.last N) x y ^ 2) ^ (k' + 1) := pow_mul _ 2 (k' + 1)
            _ ≤ (64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)) ^ (k' + 1) :=
                pow_le_pow_left₀ (sq_nonneg _) hsq (k' + 1)
        refine (le_abs_self _).trans ?_
        exact abs_integral_le_of_forall_abs_le P_s fun ω =>
          abs_integral_le_of_forall_abs_le _ fun σ => by
            rw [abs_of_nonneg (Even.pow_nonneg ⟨k' + 1, by ring⟩ _)]
            exact hpt_last (σ 0).1 (σ 1).1
      have hm0 :
          ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
            A_fn 0 (σ 0).1 (σ 1).1 ^ (2 * (k' + 1))
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
          (64 * ((k' + 1 : ℕ) : ℝ) / ((N : ℝ) + 1)) ^ (k' + 1) := by
        by_cases hN0 : 0 < N
        · have h0_lt : (0 : Fin (N + 1)).1 < N := hN0
          have hstep0 := integral_interpolating_partial_overlap_step_lt h_der h_dom
            hs hd hb hq hr hα_dom hα_der 0 h0_lt ih
          dsimp only at hstep0
          have hcast : ((k' + 1 : ℕ) : ℝ) = (k' : ℝ) + 1 := by push_cast; ring
          rw [show 2 * (k' + 1) = 2 * k' + 2 by ring, hcast]
          linarith
        · have hN_eq : N = 0 := by omega
          have h0_eq_last : (0 : Fin (N + 1)) = Fin.last N := by ext; simp [hN_eq]
          rw [h0_eq_last]
          exact hlast_bound
      intro m
      by_cases hm_lt : m.1 < N
      · have hstep_m := integral_interpolating_partial_overlap_step_lt h_der h_dom
          hs hd hb hq hr hα_dom hα_der m hm_lt ih
        dsimp only at hstep_m
        have hcast : ((k' + 1 : ℕ) : ℝ) = (k' : ℝ) + 1 := by push_cast; ring
        rw [show 2 * (k' + 1) = 2 * k' + 2 by ring, hcast] at hm0 ⊢
        linarith
      · have hm_eq_last : m = Fin.last N := by
          ext; have := m.2; simp [Fin.last]; omega
        rw [hm_eq_last]
        exact hlast_bound
  exact hall k n

/-! ### Zero-constraint (`M = 0`) case, Theorem 2.5.1, and exponential moment corollary -/

/-- **Higher overlap moments at `M = 0` constraints:** when `M = 0` (`q = 0, r = 0`), the
Hamiltonian `E_s` vanishes identically, so the spin marginal is the uniform hypercube law (`β = 0,
q = 0, h = 0` in `sk_overlap_moment_le`), giving `ν_s((R_{1,2} - 0)^{2k}) ≤ (64 k / (N + 1))^k`
for all `k : ℕ`. -/
private lemma integral_interpolating_overlap_pow_le_zero_constraints
    (N : ℕ) (u : ℝ → ℝ) (s : ℝ) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin 0 => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin 0 => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_s := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin 0 => gaussianReal 0 1)
    let E_s (ω : ((Fin 0 → Fin (N + 1) → ℝ) × (Fin 0 → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ)) : ℝ :=
      (∑ j : Fin 0, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt 0 * ω.1.2 j + Real.sqrt (1 - 0) * x.2 j))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt 0
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ),
        (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - 0) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
      (64 * (k : ℝ) / ((N : ℝ) + 1)) ^ k := by
  intro P_g P_z P_z' P_s μ_s E_s
  have hP0 : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
  have hE0 (ω : ((Fin 0 → Fin (N + 1) → ℝ) × (Fin 0 → ℝ)) × (Fin (N + 1) → ℝ)) :
      E_s ω = 0 := by funext x; simp [E_s]
  have haux0 (ω : ((Fin 0 → Fin (N + 1) → ℝ) × (Fin 0 → ℝ)) × (Fin (N + 1) → ℝ))
      (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
        ∂(Measure.pi fun _ : Fin 2 => (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted 0) := by
    rw [hE0 ω]
    have h0_split (x : (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ)) :
        (0 : (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ) → ℝ) x =
          (0 : (Fin (N + 1) → ℤˣ) → ℝ) x.1 + ∑ _j : Fin 0, (0 : ℝ) := by simp
    simp_rw [show (0 : (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ) → ℝ) = _ from funext h0_split]
    simpa using integral_pi_tilted_count_prod_sum (fun _ : Fin 0 => gaussianReal 0 1)
      (0 : (Fin (N + 1) → ℤˣ) → ℝ) (fun _ _ _ => (0 : ℝ))
      (fun _ _ => measurable_const) (fun _ => (0 : ℝ)) (fun _ _ _ => le_rfl) Φ
  let Φ_k (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - 0) ^ (2 * k)
  change (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin 0 → ℝ), Φ_k (fun l => (σ l).1)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) ≤ _
  rw [integral_congr_ae (ae_of_all _ fun ω => haux0 ω Φ_k),
    integral_const, probReal_univ, one_smul]
  rcases k with _ | k
  · have : IsProbabilityMeasure ((Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted 0) :=
      isProbabilityMeasure_tilted Integrable.of_finite
    have h1 : Φ_k = fun _ => (1 : ℝ) := by funext _; simp [Φ_k]
    rw [h1, integral_const, probReal_univ, one_smul, pow_zero]
  · have hsk := sk_overlap_moment_le N 0 0 0 ⟨le_rfl, zero_le_one⟩ (by simp) (by norm_num)
      (k + 1) (Nat.succ_pos k)
    dsimp only at hsk
    have hsk_zero (g : FinPairs (N + 1) → ℝ) :
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * (0 : ℝ) *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            (0 : ℝ) * ∑ i : Fin (N + 1), (a i : ℝ)) =
          (0 : (Fin (N + 1) → ℤˣ) → ℝ) := by
      funext a; simp
    simp_rw [hsk_zero, integral_const, probReal_univ, one_smul] at hsk
    simpa only [Φ_k, dotProduct] using hsk

/-- **Talagrand Theorem 2.5.1 (Eq. (2.94)), uniformly along the `s`-interpolating path:**
Given `D ∈ ℝ`, there exists `K ≥ 0` (chosen before `N, M, s, u, q, r, k`) such that whenever `u`
satisfies (2.7), `(M / (N + 1)) * K ≤ 1`, `(q, r)` solves (2.68), and `s ∈ [0, 1]`, for every
`k : ℕ`:
$$\nu_s\!\left((R_{1,2} - q)^{2k}\right) \le \left(\frac{64 k}{N + 1}\right)^k.$$ -/
theorem integral_interpolating_overlap_pow_le (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (k : ℕ),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_s := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤
          (64 * (k : ℝ) / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K_der, hK_der0, h_der⟩ := exists_hasDerivAt_interpSP_abs_le_holder (Fin 2) D
  obtain ⟨K_dom, hK_dom0, h_dom⟩ := integral_interpSP_fin_two_le_two_mul_interpolating D
  let K : ℝ := max K_dom (32 * K_der)
  refine ⟨K, le_max_of_le_left hK_dom0, ?_⟩
  intro N M s hs u hd hb hα q r hq hr k
  rcases M with _ | M
  · have hr0 : r = 0 := by simp [hr]
    have hq0 : q = 0 := by simp [hq, hr0]
    dsimp only
    rw [hq0, hr0]
    exact integral_interpolating_overlap_pow_le_zero_constraints N u s k
  dsimp only
  let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
  have hα_cast : ((M + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = α := by push_cast; rfl
  rw [hα_cast] at hα hr
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα_dom : α * K_dom ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_left K_dom (32 * K_der)) hα0).trans hα
  have hα_der : α * (32 * K_der) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (le_max_right K_dom (32 * K_der)) hα0).trans hα
  have hmain := integral_interpolating_partial_overlap_pow_le_succ_constraints h_der h_dom
    hs hd hb hq hr hα_dom hα_der k 0
  dsimp only at hmain
  refine le_trans (le_of_eq ?_) hmain
  refine integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun σ => ?_))
  dsimp only
  congr 1
  have hIci0 : (Finset.Ici (0 : Fin (N + 1))) = Finset.univ := by ext i; simp
  rw [hIci0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hL_ne : ((N : ℝ) + 1) ≠ 0 := by positivity
  push_cast; field_simp

/-- **Talagrand Theorem 2.5.1 (Eq. (2.94)) for the original perceptron (`s = 1`):**
under (2.7), `(M / (N + 1)) * K ≤ 1`, and `(q, r)` solving (2.68), for every `k : ℕ`:
$$\nu\!\left((R_{1,2} - q)^{2k}\right) \le \left(\frac{64 k}{N + 1}\right)^k.$$ -/
theorem integral_perceptron_overlap_pow_le (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (k : ℕ),
        ∫ g : Fin M → Fin (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            (((N : ℝ) + 1)⁻¹ * ∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ) - q) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin 2 =>
              (Measure.count : Measure (Fin (N + 1) → ℤˣ)).tilted
                fun τ : Fin (N + 1) → ℤˣ =>
                  ∑ j, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)))
            ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) ≤
          (64 * (k : ℝ) / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K, hK0, hK⟩ := integral_interpolating_overlap_pow_le D
  refine ⟨K, hK0, ?_⟩
  intro N M u hd hb hα q r hq hr k
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hs1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h := hK N M hs1 hd hb hα hq hr k
  dsimp only at h
  refine le_trans (le_of_eq ?_) h
  symm
  let Φ (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - q) ^ (2 * k)
  let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
  let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  let P_1 := (P_g.prod P_z).prod P_z'
  let μ_1 := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  let E_perc (g : Fin M → Fin (N + 1) → ℝ) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    ∑ j : Fin M, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ))
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_1.tilted (fun x =>
          (∑ j : Fin M, u (Real.sqrt 1 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc ω.1.1)) := by
    have hE_simp (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        (∑ j : Fin M, u (Real.sqrt 1 *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
          Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r) =
        E_perc ω.1.1 x.1 + ∑ _j : Fin M, (0 : ℝ) := by
      simp [E_perc]
    simp_rw [hE_simp]
    simpa using integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (E_perc ω.1.1) (fun _ _ _ => (0 : ℝ))
      (fun _ _ => measurable_const) (fun _ => (0 : ℝ)) (fun _ _ _ => le_rfl) Φ
  change (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
      ∂(Measure.pi fun _ : Fin 2 => μ_1.tilted _) ∂P_1) =
    ∫ g, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc g)) ∂P_g
  simp_rw [hpt]
  have hP_z : IsProbabilityMeasure P_z := by dsimp [P_z]; infer_instance
  have hP_z' : IsProbabilityMeasure P_z' := by dsimp [P_z']; infer_instance
  let I_g (g : Fin M → Fin (N + 1) → ℝ) : ℝ :=
    ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_perc g))
  have hIg_int : Integrable I_g P_g := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite Φ
    exact integrable_integral_pi_count_tilted_sum_potential hu.measurable
      (fun _ τ => Φ τ) (fun _ => measurable_const) (fun _ τ => hC τ)
  have hfub1 : ∫ ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ),
      I_g ω.1.1 ∂((P_g.prod P_z).prod P_z') =
    ∫ p : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ), I_g p.1 ∂(P_g.prod P_z) := by
    rw [integral_prod _ ((hIg_int.comp_fst P_z).comp_fst P_z')]
    simp
  rw [hfub1, integral_prod _ (hIg_int.comp_fst P_z)]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

/-- Elementary factorial domination `(k : ℝ)^k ≤ k! * e^k`. -/
private lemma nat_pow_self_le_factorial_mul_exp (k : ℕ) :
    (k : ℝ) ^ k ≤ (Nat.factorial k : ℝ) * (Real.exp 1) ^ k := by
  have h := Real.pow_le_factorial_mul_exp (Nat.cast_nonneg k) k
  have he : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  rwa [he] at h

/-- Real exponential power series `HasSum (fun k => x^k / k!) (exp x)`. -/
private lemma hasSum_pow_div_factorial_real (x : ℝ) :
    HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
  have hsum : Summable (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) :=
    Real.summable_pow_div_factorial x
  have heq : Real.exp x = ∑' k : ℕ, x ^ k / (Nat.factorial k : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [heq]
  exact hsum.hasSum

/-- **Exponential square-moment corollary of Theorem 2.5.1 (addition beyond Section 2.5):**
Given `D ∈ ℝ`, there exists `K ≥ 0` (the constant of Theorem 2.5.1) such that whenever `u` satisfies
(2.7), `(M / (N + 1)) * K ≤ 1`, `(q, r)` solves (2.68), `s ∈ [0, 1]`, and `0 ≤ c ≤ 1 / 200`
(so `64 c e ≤ 7 / 8 < 1`), the `s`-interpolating two-replica law satisfies
$$\nu_s\!\left(\exp\!\left(c (N + 1) (R_{1,2} - q)^2\right)\right) \le 8.$$ -/
theorem integral_interpolating_exp_overlap_sub_sq_le (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {s c : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (_hc : c ∈ Icc (0 : ℝ) (1 / 200))
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_s := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            Real.exp (c * ((N : ℝ) + 1) *
              (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q) ^ 2)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s ≤ 8 := by
  obtain ⟨K, hK0, hK⟩ := integral_interpolating_overlap_pow_le D
  refine ⟨K, hK0, ?_⟩
  intro N M s c hs hc u hd hb hα q r hq hr P_g P_z P_z' P_s μ_s E_s
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  let Ω := ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)
  let L : ℝ := (N : ℝ) + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hP_prob : IsProbabilityMeasure P_s := by dsimp only [P_s, P_g, P_z, P_z']; infer_instance
  have hE_m : Measurable fun p : Ω × ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => E_s p.1 p.2 :=
    measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hEb (ω : Ω) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E_s ω x ≤ M * D + ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| := by
    refine add_le_add ((Finset.sum_le_sum fun _ _ => hu.le _).trans_eq (by simp))
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul]
  have hν_prob (ω : Ω) : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_of_ae_le
      (Measurable.of_uncurry_left hE_m).aemeasurable (ae_of_all _ (hEb ω))
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by
    rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  let d_pair (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - q) ^ 2
  have hd_le4 (τ : Fin 2 → Fin (N + 1) → ℤˣ) : d_pair τ ≤ 4 := by
    dsimp only [d_pair]
    rw [← sq_abs]
    have habs := abs_spin_overlap_sub_le_two hq_mem (τ 0) (τ 1)
    calc |((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - q| ^ 2
        ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 4 := by norm_num
  let term (k : ℕ) (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ :=
    (c * L * d_pair τ) ^ k / (Nat.factorial k : ℝ)
  have hterm_nn (k : ℕ) (τ : Fin 2 → Fin (N + 1) → ℤˣ) : 0 ≤ term k τ := by
    dsimp only [term, d_pair]
    have hc0 : 0 ≤ c := hc.1
    positivity
  let M_exp : ℝ := Real.exp (c * L * 4)
  have hS_le (m : ℕ) (τ : Fin 2 → Fin (N + 1) → ℤˣ) :
      ∑ k ∈ Finset.range m, term k τ ≤ Real.exp (c * L * d_pair τ) :=
    sum_le_hasSum (Finset.range m) (fun k _ => hterm_nn k τ)
      (hasSum_pow_div_factorial_real (c * L * d_pair τ))
  have hexp_le_M (τ : Fin 2 → Fin (N + 1) → ℤˣ) :
      Real.exp (c * L * d_pair τ) ≤ M_exp := by
    refine Real.exp_le_exp.2 ?_
    exact mul_le_mul_of_nonneg_left (hd_le4 τ) (mul_nonneg hc.1 hL.le)
  let E_eff (ω : Ω) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
    ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)
  have haux (ω : Ω) (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) := by
    have hE_swap (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E_s ω x = (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ j : Fin M, u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)) := add_comm _ _
    simp_rw [show E_s ω = _ from funext hE_swap]
    exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
      (fun τ j ξ => u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
        ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ)))
      (fun τ j => hu.measurable.comp (by fun_prop)) (fun _ => D) (fun _ _ _ => hu.le _) Φ
  have hE_eff_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω : Ω => E_eff ω τ := by
    dsimp only [E_eff]
    have hm1 : Measurable fun ω : Ω =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).mul measurable_const
    have hm2 : Measurable fun ω : Ω =>
        ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1) := by
      refine Finset.measurable_sum _ fun j _ => Real.measurable_log.comp ?_
      have hj : Measurable fun p : Ω × ℝ =>
          Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 j i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 j + Real.sqrt (1 - q) * p.2))) := by
        have hs1 : Measurable fun p : Ω × ℝ =>
            ∑ i : Fin (N + 1), p.1.1.1 j i * ((τ i : ℤ) : ℝ) := by
          refine Finset.measurable_sum _ fun i _ => ?_
          have mg : Measurable fun p : Ω × ℝ => p.1.1.1 j i :=
            (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
              (measurable_fst.comp (measurable_fst.comp measurable_fst)))
          exact mg.mul_const _
        have hz1 : Measurable fun p : Ω × ℝ => p.1.1.2 j :=
          (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
        exact Real.measurable_exp.comp (hu.measurable.comp
          (((hs1.const_mul _).const_mul _).add
            (((hz1.const_mul _).add (measurable_snd.const_mul _)).const_mul _)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    exact hm1.add hm2
  have hterm_int_le (k : ℕ) :
      (∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, term k τ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s) ≤
        ((7 : ℝ) / 8) ^ k := by
    have h_unaux : (∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, term k τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s) =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), term k (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s :=
      integral_congr_ae (ae_of_all _ fun ω => (haux ω (term k)).symm)
    rw [h_unaux]
    have hpull_c : ∀ τ : Fin 2 → Fin (N + 1) → ℤˣ,
        term k τ = ((c * L) ^ k / (Nat.factorial k : ℝ)) *
          (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ 0 i : ℤ) : ℝ) * ((τ 1 i : ℤ) : ℝ) - q) ^ (2 * k) := by
      intro τ
      dsimp only [term, d_pair]
      rw [mul_pow, ← pow_mul]
      ring
    simp_rw [hpull_c, integral_const_mul]
    have hc0 : 0 ≤ c := hc.1
    have hmom := hK N M hs hd hb hα hq hr k
    dsimp only at hmom
    have hfac_pos : (0 : ℝ) < Nat.factorial k := by positivity
    have hstep1 : ((c * L) ^ k / (Nat.factorial k : ℝ)) *
        (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) - q) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) ≤
        ((c * L) ^ k / (Nat.factorial k : ℝ)) * (64 * (k : ℝ) / L) ^ k :=
      mul_le_mul_of_nonneg_left hmom (by positivity)
    refine hstep1.trans ?_
    have hL_cancel : (c * L) ^ k * (64 * (k : ℝ) / L) ^ k = (64 * c) ^ k * (k : ℝ) ^ k := by
      rw [← mul_pow]
      have h1 : c * L * (64 * (k : ℝ) / L) = 64 * c * (k : ℝ) := by
        have hL_ne : L ≠ 0 := hL.ne'
        field_simp
      rw [h1, mul_pow]
    rw [div_mul_eq_mul_div, hL_cancel]
    have hkk := nat_pow_self_le_factorial_mul_exp k
    have h64ce : 64 * c * Real.exp 1 ≤ 7 / 8 := by
      have he3 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
      nlinarith [hc.1, hc.2, Real.exp_pos 1]
    calc (64 * c) ^ k * (k : ℝ) ^ k / (Nat.factorial k : ℝ)
        ≤ (64 * c) ^ k * ((Nat.factorial k : ℝ) * Real.exp 1 ^ k) / (Nat.factorial k : ℝ) := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkk (by positivity))
            hfac_pos.le
      _ = (64 * c) ^ k * Real.exp 1 ^ k := by
          have hne : (Nat.factorial k : ℝ) ≠ 0 := hfac_pos.ne'
          field_simp
      _ = (64 * c * Real.exp 1) ^ k := by rw [← mul_pow]
      _ ≤ ((7 : ℝ) / 8) ^ k := pow_le_pow_left₀ (by positivity) h64ce k
  have hpartial_le (m : ℕ) :
      (∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, (∑ k ∈ Finset.range m, term k τ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s) ≤ 8 := by
    have hint_k (k : ℕ) :
        Integrable (fun ω : Ω => ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, term k τ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))) P_s := by
      obtain ⟨C, hC⟩ := exists_abs_le_of_finite (term k)
      exact integrable_integral_pi_count_tilted_of_bound E_eff hE_eff_m
        (fun _ τ => term k τ) (fun _ => measurable_const) C (fun _ τ => hC τ)
    rw [integral_integral_finset_sum P_s
      (fun ω => Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))
      (Finset.range m) (fun k τ => term k τ)
      (fun _ _ _ => Integrable.of_finite) (fun k _ => hint_k k)]
    have hgeom : ∑ k ∈ Finset.range m, ((7 : ℝ) / 8) ^ k ≤ 8 := by
      have hhas : HasSum (fun k : ℕ => ((7 : ℝ) / 8) ^ k) ((1 - (7 : ℝ) / 8)⁻¹) :=
        hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
      have hsum_le := sum_le_hasSum (Finset.range m) (fun k _ => by positivity) hhas
      exact hsum_le.trans_eq (by norm_num)
    exact (Finset.sum_le_sum fun k _ => hterm_int_le k).trans hgeom
  have hgoal_aux :
      (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Real.exp (c * L * d_pair (fun l => (σ l).1))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) =
        ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Real.exp (c * L * d_pair τ)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s :=
    integral_congr_ae (ae_of_all _ fun ω => haux ω (fun τ => Real.exp (c * L * d_pair τ)))
  change (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      Real.exp (c * L * d_pair (fun l => (σ l).1))
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) ∂P_s) ≤ 8
  rw [hgoal_aux]
  have htendsto : Tendsto
      (fun m : ℕ => ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, (∑ k ∈ Finset.range m, term k τ)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s)
      atTop
      (𝓝 (∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Real.exp (c * L * d_pair τ)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P_s)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M_exp) ?_ (integrable_const M_exp)
      ?_ (ae_of_all _ fun ω => ?_)
    · intro m
      let Sm (τ : Fin 2 → Fin (N + 1) → ℤˣ) : ℝ := ∑ k ∈ Finset.range m, term k τ
      obtain ⟨C, hC⟩ := exists_abs_le_of_finite Sm
      exact (integrable_integral_pi_count_tilted_of_bound E_eff hE_eff_m
        (fun _ τ => Sm τ) (fun _ => measurable_const) C (fun _ τ => hC τ)).aestronglyMeasurable
    · intro m
      refine ae_of_all _ fun ω => ?_
      have _ : IsProbabilityMeasure (Measure.count.tilted (E_eff ω)) :=
        isProbabilityMeasure_tilted Integrable.of_finite
      rw [Real.norm_of_nonneg (integral_nonneg fun _ =>
        Finset.sum_nonneg fun k _ => hterm_nn k _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun τ => by
        rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => hterm_nn k _)]
        exact (hS_le m τ).trans (hexp_le_M τ))
    · have _ : IsProbabilityMeasure (Measure.count.tilted (E_eff ω)) :=
        isProbabilityMeasure_tilted Integrable.of_finite
      refine tendsto_integral_of_dominated_convergence (fun _ => M_exp) ?_
        (integrable_const M_exp) ?_ (ae_of_all _ fun τ => ?_)
      · intro m
        exact (measurable_of_finite fun τ => ∑ k ∈ Finset.range m, term k τ).aestronglyMeasurable
      · intro m
        refine ae_of_all _ fun τ => ?_
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => hterm_nn k _)]
        exact (hS_le m τ).trans (hexp_le_M τ)
      · exact (hasSum_pow_div_factorial_real (c * L * d_pair τ)).tendsto_sum_nat
  exact le_of_tendsto htendsto (Eventually.of_forall hpartial_le)

end SpinGlasses
