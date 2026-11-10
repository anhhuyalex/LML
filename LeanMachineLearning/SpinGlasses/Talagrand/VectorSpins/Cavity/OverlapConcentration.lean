/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Overlap
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.SiteSymmetry

/-!
# Theorem 1.12.1 (Talagrand): the overlaps concentrate

Assume `q`, `ρ` satisfy (1.372)--(1.373) and `β² d² ≤ 1/200`.  For the vector SK model with `N + 1`
sites, the expected squared errors of the overlaps `R_{1,2}` and `R_{1,1}` obey
`A + B ≤ K(d) / (N + 1)`.  This file assembles the proof from the cavity path (Proposition 1.12.4,
Corollary 1.12.5), the decoupled system at `t = 0`, site symmetry and the closing inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- AM--GM for square roots. -/
theorem sqrt_mul_sqrt_le_half_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- The closing algebra of Theorem 1.12.1: from `A ≤ K + κ √A (√(2B+ε) + √(2A+ε))` and the
same for `B`, with `κ ≤ 1/6`, we get `A + B ≤ 4K + ε`. -/
theorem add_le_of_coupled_sqrt_bounds {A B K ε κ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hκ0
  : 0 ≤ κ)
    (hκ : κ ≤ 1 / 6)
    (h1 : A ≤ K + κ * Real.sqrt A * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)))
    (h2 : B ≤ K + κ * Real.sqrt B * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε))) :
    A + B ≤ 4 * K + ε := by
  have hB' : 0 ≤ 2 * B + ε := by positivity
  have hA' : 0 ≤ 2 * A + ε := by positivity
  have a1 := sqrt_mul_sqrt_le_half_add hA hB'
  have a2 := sqrt_mul_sqrt_le_half_add hA hA'
  have b1 := sqrt_mul_sqrt_le_half_add hB hB'
  have b2 := sqrt_mul_sqrt_le_half_add hB hA'
  have e1 : Real.sqrt A * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) ≤
      (A + (2 * B + ε)) / 2 + (A + (2 * A + ε)) / 2 := by rw [mul_add]; linarith
  have e2 : Real.sqrt B * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) ≤
      (B + (2 * B + ε)) / 2 + (B + (2 * A + ε)) / 2 := by rw [mul_add]; linarith
  have f1 : κ * Real.sqrt A * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) ≤
      κ * ((A + (2 * B + ε)) / 2 + (A + (2 * A + ε)) / 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e1 hκ0
  have f2 : κ * Real.sqrt B * (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) ≤
      κ * ((B + (2 * B + ε)) / 2 + (B + (2 * A + ε)) / 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left e2 hκ0
  nlinarith [mul_nonneg hκ0 hA, mul_nonneg hκ0 hB, mul_nonneg hκ0 hε,
    mul_nonneg (sub_nonneg.2 hκ) hA, mul_nonneg (sub_nonneg.2 hκ) hB,
    mul_nonneg (sub_nonneg.2 hκ) hε]

section Setup

variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure α) [IsProbabilityMeasure μ]
  (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
  (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (ρ q : Fin d → Fin d → ℝ)
  {P : Measure Ω} [IsProbabilityMeasure P] {gt : FinPairs (N + 1) → Ω → ℝ}
  {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}

include hξ hbound in
omit [IsProbabilityMeasure P] in
/-- **The cavity system at `t = 1` is the `(N+1)`-site system.**  For the couplings `g`, `g'`
being the restriction of the family `gt` to the old pairs and the pairs with the last site, the
average `ν_1` of a function of `R` replicas is the disorder average of the `R`-replica Gibbs
average of the vector SK energy. -/
theorem skVectorCavityAverage_one_eq {R : Type*} [Fintype R]
    (hg : ∀ p ω, g p ω = gt ⟨(p.val.1.castSucc, p.val.2.castSucc),
      Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ ω)
    (hg' : ∀ i ω, g' i ω = gt ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ ω)
    (G : (R → Fin (N + 1) → α) → ℝ) (hG : Measurable G) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option R) → Fin (N + 1) → α =>
        G fun c => σ (some (some c))) =
      ∫ ω, ∫ x : R → Fin (N + 1) → α, G x ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun x => skVectorEnergy (N + 1) β (fun p => gt p ω) (fun i => ξ (x i)))) ∂P := by
  rw [skVectorCavityAverage_old μ ξ hξ hbound β ρ q G hG 1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show _ = _
  have hE : skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
      (fun u => Y u ω) 1 = fun x => skVectorEnergy (N + 1) β (fun p => gt p ω)
        (fun i => ξ (x i)) := by
    funext x
    have := skVectorCavityEnergy_one ξ β ρ q (fun p => gt p ω) (fun u => Y u ω) x
    rw [← this]
    simp only [hg, hg']
  simp only [hE]

include hξ hbound in
/-- The Gibbs averages of the cavity path are integrable in the Gaussian environment, for any
number of replicas. -/
theorem integrable_integral_skVectorCavity {R : Type*} [Fintype R] (hgm : ∀ p, Measurable (g p))
    (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u)) (t : ℝ)
    (G : (R → Fin (N + 1) → α) → ℝ) (hG : Measurable G) (hGb : ∃ M, ∀ x, |G x| ≤ M) :
    Integrable (fun ω => ∫ x, G x ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
        (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))) P :=
  integrable_integral_pi_tilted (ι := R) (P := P) (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (measurable_skVectorCavityEnergy_joint ξ hξ N β ρ q hgm hg'm hYm t)
    (fun _ => isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ (Nat.cast_nonneg d) hbound N
      β ρ q
      _ _ _ t) hG hGb.choose_spec

omit [IsProbabilityMeasure P] in
include hξ hbound in
/-- **Symmetry between sites, summed over the matrix entries** (Eq. (1.383)): at `t = 1`,
`ν(∑ᵤᵥ (ε^a_u ε^b_v - Tᵤᵥ)(R^{u,v}_{a,b} - Tᵤᵥ)) = ν(∑ᵤᵥ (R^{u,v}_{a,b} - Tᵤᵥ)²)`. -/
theorem skVectorCavityAverage_one_overlap_variance_eq_last_spin [IsProbabilityMeasure P]
    (hgt : ∀ p, Measurable (gt p))
    (hsym : ∀ π : Equiv.Perm (Fin (N + 1)),
      Measure.map (fun ω => (fun p => gt p ω) ∘ (pairPerm π).symm) P =
        Measure.map (fun ω p => gt p ω) P)
    (hg : ∀ p ω, g p ω = gt ⟨(p.val.1.castSucc, p.val.2.castSucc),
      Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ ω)
    (hg' : ∀ i ω, g' i ω = gt ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ ω)
    (a b : Fin 2) (T : Fin d → Fin d → ℝ) (hT : ∀ u v, |T u v| ≤ d) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorLastSpinDeviation ξ N a b T u v (fun c => σ (some (some c))) *
            skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c)))) =
      skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c))) ^ 2) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgt' : Measurable fun ω p => gt p ω := measurable_pi_iff.2 hgt
  have hm1 : Measurable fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorLastSpinDeviation ξ N a b T u v τ * skVectorOverlapDeviation ξ N a b T u v τ :=
    Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
      (measurable_skVectorLastSpinDeviation ξ hξ a b T u v).mul
        (measurable_skVectorOverlapDeviation ξ hξ a b T u v)
  have hm2 : Measurable fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorOverlapDeviation ξ N a b T u v τ ^ 2 :=
    Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
      (measurable_skVectorOverlapDeviation ξ hξ a b T u v).pow_const 2
  rw [skVectorCavityAverage_one_eq μ ξ hξ hbound β ρ q hg hg' _ hm1,
    skVectorCavityAverage_one_eq μ ξ hξ hbound β ρ q hg hg' _ hm2]
  set Q : Ω → Measure (Fin 2 → Fin (N + 1) → α) := fun ω => Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun x => skVectorEnergy (N + 1) β (fun p => gt p ω) (fun i => ξ (x i))) with hQ
  have hprob : ∀ ω, IsProbabilityMeasure (Q ω) := fun ω => by
    have := isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β (fun p => gt p ω)
    exact inferInstance
  have hI : ∀ G : (Fin 2 → Fin (N + 1) → α) → ℝ, Measurable G → (∃ M, ∀ x, |G x| ≤ M) →
      Integrable (fun ω => ∫ x, G x ∂(Q ω)) P := fun G hG hGb =>
    integrable_integral_skVectorEnergy μ ξ hξ hbound β hgt' G hG hGb
  have hb : ∀ (F : Fin d → Fin d → (Fin 2 → Fin (N + 1) → α) → ℝ) (C : ℝ),
      (∀ u v x, |F u v x| ≤ C) → ∀ u v, ∃ M, ∀ x, |F u v x| ≤ M := fun F C h u v => ⟨C, h u v⟩
  have hsum_prod : ∀ (F : Fin d → Fin d → (Fin 2 → Fin (N + 1) → α) → ℝ)
      (hF : ∀ u v, Measurable (F u v)) (hFb : ∀ u v, ∃ M, ∀ x, |F u v x| ≤ M),
      ∫ ω, ∫ x, ∑ u, ∑ v, F u v x ∂(Q ω) ∂P =
        ∑ u, ∑ v, ∫ ω, ∫ x, F u v x ∂(Q ω) ∂P := fun F hF hFb => by
    have := integral_integral_finset_sum P Q (Finset.univ : Finset (Fin d × Fin d))
      (fun p x => F p.1 p.2 x)
      (fun p _ ω => integrable_of_measurable_bound (hF p.1 p.2) (hFb p.1 p.2).choose_spec)
      (fun p _ => hI _ (hF p.1 p.2) (hFb p.1 p.2))
    simpa only [Fintype.sum_prod_type] using this
  rw [hsum_prod
      (fun u v x => skVectorLastSpinDeviation ξ N a b T u v x * skVectorOverlapDeviation ξ N a b T
        u v x)
      (fun u v => (measurable_skVectorLastSpinDeviation ξ hξ a b T u v).mul
        (measurable_skVectorOverlapDeviation ξ hξ a b T u v))
      (fun u v => ⟨(d + d) * (d + d), fun x => by
        rw [abs_mul]
        exact mul_le_mul (abs_skVectorLastSpinDeviation_le ξ hbound a b T u v (hT u v) x)
          (abs_skVectorOverlapDeviation_le ξ hbound a b T u v (hT u v) x) (abs_nonneg _)
          (add_nonneg hr hr)⟩),
    hsum_prod
      (fun u v x => skVectorOverlapDeviation ξ N a b T u v x ^ 2)
      (fun u v => (measurable_skVectorOverlapDeviation ξ hξ a b T u v).pow_const 2)
      (fun u v => ⟨(d + d) ^ 2, fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_skVectorOverlapDeviation_le ξ hbound a b T u v
          (hT u v) x) 2 |>.trans' (by rw [sq_abs])⟩)]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  have := skVector_overlap_variance_eq_last_spin μ ξ hξ hbound β (gt := fun ω p => gt p ω) hgt' hsym
    a b u v (T u v) (hT u v)
  simp only [skVectorOverlapDeviation, skVectorLastSpinDeviation, sq]
  exact this.symm

include hξ hbound in
/-- **The bound `|ν₀(f)| ≤ K(d)/N`** of the proof of Theorem 1.12.1, summed over the matrix entries:
if the centered last-site products decouple from the old sites at `t = 0`, then
`|ν₀(∑ᵤᵥ (ε^a_u ε^b_v - Tᵤᵥ)(R^{u,v}_{a,b} - Tᵤᵥ))| ≤ 2 d⁴/(N+1)`. -/
theorem abs_skVectorCavityAverage_zero_sum_le
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (a b : Fin 2) (T : Fin d → Fin d → ℝ) (hT : ∀ u v, |T u v| ≤ d)
    (hdec : ∀ u v, ∀ Ψ : (Fin 2 → Fin N → α) → ℝ, Measurable Ψ →
      ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T u v)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0) :
    |skVectorCavityAverage μ ξ N β ρ q P g g' Y 0 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorLastSpinDeviation ξ N a b T u v (fun c => σ (some (some c))) *
            skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c))))| ≤
      (d : ℝ) * d * (2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1)) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm1 : Measurable fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorLastSpinDeviation ξ N a b T u v τ * skVectorOverlapDeviation ξ N a b T u v τ :=
    Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
      (measurable_skVectorLastSpinDeviation ξ hξ a b T u v).mul
        (measurable_skVectorOverlapDeviation ξ hξ a b T u v)
  rw [skVectorCavityAverage_old μ ξ hξ hbound β ρ q _ hm1 0]
  set Q : Ω → Measure (Fin 2 → Fin (N + 1) → α) := fun ω => Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) 0) with hQ
  have hprob : ∀ ω, IsProbabilityMeasure (Q ω) := fun ω => by
    have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) 0
    exact inferInstance
  have hI : ∀ G : (Fin 2 → Fin (N + 1) → α) → ℝ, Measurable G → (∃ M, ∀ x, |G x| ≤ M) →
      Integrable (fun ω => ∫ x, G x ∂(Q ω)) P := fun G hG hGb =>
    integrable_integral_skVectorCavity μ ξ hξ hbound β ρ q hgm hg'm hYm 0 G hG hGb
  have hsum_prod : ∀ (F : Fin d → Fin d → (Fin 2 → Fin (N + 1) → α) → ℝ)
      (hF : ∀ u v, Measurable (F u v)) (hFb : ∀ u v, ∃ M, ∀ x, |F u v x| ≤ M),
      ∫ ω, ∫ x, ∑ u, ∑ v, F u v x ∂(Q ω) ∂P =
        ∑ u, ∑ v, ∫ ω, ∫ x, F u v x ∂(Q ω) ∂P := fun F hF hFb => by
    have := integral_integral_finset_sum P Q (Finset.univ : Finset (Fin d × Fin d))
      (fun p x => F p.1 p.2 x)
      (fun p _ ω => integrable_of_measurable_bound (hF p.1 p.2) (hFb p.1 p.2).choose_spec)
      (fun p _ => hI _ (hF p.1 p.2) (hFb p.1 p.2))
    simpa only [Fintype.sum_prod_type] using this
  rw [hsum_prod
    (fun u v x => skVectorLastSpinDeviation ξ N a b T u v x * skVectorOverlapDeviation ξ N a b T u
      v x)
    (fun u v => (measurable_skVectorLastSpinDeviation ξ hξ a b T u v).mul
      (measurable_skVectorOverlapDeviation ξ hξ a b T u v))
    (fun u v => ⟨(d + d) * (d + d), fun x => by
      rw [abs_mul]
      exact mul_le_mul (abs_skVectorLastSpinDeviation_le ξ hbound a b T u v (hT u v) x)
        (abs_skVectorOverlapDeviation_le ξ hbound a b T u v (hT u v) x) (abs_nonneg _)
        (add_nonneg hr hr)⟩)]
  exact abs_double_sum_le _ fun u v =>
    abs_skVectorCavityAverage_zero_overlap_le μ ξ hξ hbound β ρ q hgm hg'm hYm a b u v (T u v) (hT
      u v)
      (hdec u v)

include hξ hbound in
/-- If `X ≤ 2 W + e` pointwise for bounded measurable `X`, `W`, then `ν_t(X) ≤ 2 ν_t(W) + e`. -/
theorem skVectorCavityAverage_le_two_mul_add
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (t : ℝ) (X W : (Fin 2 → Fin (N + 1) → α) → ℝ) (hX : Measurable X) (hW : Measurable W)
    {MX MW : ℝ} (hXb : ∀ σ, |X σ| ≤ MX) (hWb : ∀ σ, |W σ| ≤ MW) (e : ℝ)
    (hXW : ∀ σ, X σ ≤ 2 * W σ + e) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => X fun c => σ (some (some c))) ≤
      2 * skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => W fun c => σ (some (some c))) + e := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [skVectorCavityAverage_old μ ξ hξ hbound β ρ q X hX t,
    skVectorCavityAverage_old μ ξ hξ hbound β ρ q W hW t]
  set Q : Ω → Measure (Fin 2 → Fin (N + 1) → α) := fun ω => Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t) with hQ
  have hprob : ∀ ω, IsProbabilityMeasure (Q ω) := fun ω => by
    have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
    exact inferInstance
  have hIX := integrable_integral_skVectorCavity (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm t X hX
    ⟨MX, hXb⟩
  have hIW := integrable_integral_skVectorCavity (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm t W hW
    ⟨MW, hWb⟩
  have hinner : ∀ ω, ∫ σ, X σ ∂(Q ω) ≤ 2 * ∫ σ, W σ ∂(Q ω) + e := fun ω => by
    have := hprob ω
    have hi2 : Integrable (fun σ => 2 * W σ) (Q ω) :=
      (integrable_of_measurable_bound (m := Q ω) hW hWb).const_mul 2
    have h1 := integral_mono (integrable_of_measurable_bound (m := Q ω) hX hXb)
      (show Integrable (fun σ => 2 * W σ + e) (Q ω) from hi2.add (integrable_const e)) hXW
    have h2 : ∫ σ, (2 * W σ + e) ∂(Q ω) = 2 * ∫ σ, W σ ∂(Q ω) + e := by
      rw [integral_add hi2 (integrable_const e), integral_const_mul, integral_const]
      simp
    exact h2 ▸ h1
  have hIs : Integrable (fun ω => 2 * ∫ σ, W σ ∂(Q ω) + e) P :=
    (hIW.const_mul 2).add (integrable_const e)
  calc ∫ ω, ∫ σ, X σ ∂(Q ω) ∂P ≤ ∫ ω, (2 * ∫ σ, W σ ∂(Q ω) + e) ∂P :=
        integral_mono hIX hIs hinner
    _ = 2 * ∫ ω, ∫ σ, W σ ∂(Q ω) ∂P + e := by
        rw [integral_add (hIW.const_mul 2) (integrable_const e), integral_const_mul,
          integral_const]
        simp
        rfl

include hξ hbound in
/-- **One side of the closing inequality** (Eq. (1.385)).  For the replicas `a`, `b` and the
target `T` (`‖T‖_F ≤ d`, decoupled at `t = 0`), the squared overlap error `A_T = ν_1(∑ (R - T)²)`
satisfies `A_T ≤ 2d⁴/(N+1) + 16 β² d² e^{20 β² d²} A_T^{1/2}(√(2B+ε) + √(2A+ε))`, provided the
cavity-overlap errors at `t = 1` are at most `2A + ε` and `2B + ε`. -/
theorem skVector_overlap_variance_le_sqrt (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hn : SKVectorCavityGaussianData P N d β q g g' Y)
    (hg : ∀ p ω, g p ω = gt ⟨(p.val.1.castSucc, p.val.2.castSucc),
      Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ ω)
    (hg' : ∀ i ω, g' i ω = gt ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ ω)
    (hgt : ∀ p, Measurable (gt p))
    (hsym : ∀ π : Equiv.Perm (Fin (N + 1)),
      Measure.map (fun ω => (fun p => gt p ω) ∘ (pairPerm π).symm) P =
        Measure.map (fun ω p => gt p ω) P)
    (a b : Fin 2) (T : Fin d → Fin d → ℝ) (hT2 : ∑ u, ∑ v, T u v ^ 2 ≤ (d : ℝ) ^ 2)
    (hdec : ∀ u v, ∀ Ψ : (Fin 2 → Fin N → α) → ℝ, Measurable Ψ →
      ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T u v)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0)
    (A B ε : ℝ)
    (hXA : skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
          (σ (some (some (1 : Fin 2)))) u v - q u v) ^ 2) ≤ 2 * A + ε)
    (hXB : skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
          (σ (some (some (0 : Fin 2)))) u v - ρ u v) ^ 2) ≤ 2 * B + ε) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c))) ^ 2) ≤
      (d : ℝ) * d * (2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1)) +
        16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) *
          Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
            Fin (N + 1) → α => ∑ u, ∑ v,
              skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c))) ^ 2)) *
          (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgm := hn.measurable_old_coupling
  have hg'm := hn.measurable_new_coupling
  have hYm := hn.measurable_field
  have hTb : ∀ u v, |T u v| ≤ d := abs_entry_le_of_sum_sq_le T hT2
  have hqb : ∀ u v, |q u v| ≤ d := abs_entry_le_of_sum_sq_le q hq2
  have hmf : Measurable fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorLastSpinDeviation ξ N a b T u v τ * skVectorOverlapDeviation ξ N a b T u v τ :=
    Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
      (measurable_skVectorLastSpinDeviation ξ hξ a b T u v).mul
        (measurable_skVectorOverlapDeviation ξ hξ a b T u v)
  have hmw := measurable_sum_sq_skVectorOverlapDeviation (N := N) ξ hξ a b T
  have hfb : ∀ τ : Fin 2 → Fin (N + 1) → α, |∑ u, ∑ v,
      skVectorLastSpinDeviation ξ N a b T u v τ * skVectorOverlapDeviation ξ N a b T u v τ| ≤
      (d : ℝ) * d * ((d + d) * (d + d)) := fun τ =>
    abs_double_sum_le _ fun u v => by
      rw [abs_mul]
      exact mul_le_mul (abs_skVectorLastSpinDeviation_le ξ hbound a b T u v (hTb u v) τ)
        (abs_skVectorOverlapDeviation_le ξ hbound a b T u v (hTb u v) τ) (abs_nonneg _)
        (add_nonneg hr hr)
  have hwb := abs_sum_sq_skVectorOverlapDeviation_le ξ hbound a b T hTb (N := N)
  have hstep := skVectorCavityAverage_one_le_zero_add_deriv μ ξ hξ hbound β ρ q hq hq2 hρ2 hn
    (fun τ => ∑ u, ∑ v, skVectorLastSpinDeviation ξ N a b T u v τ * skVectorOverlapDeviation ξ N a
      b T u v τ)
    (fun τ => ∑ u, ∑ v, skVectorOverlapDeviation ξ N a b T u v τ ^ 2) hmf hmw
    (by positivity) (by positivity) hfb hwb
    (fun τ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _)
    (fun τ => sq_sum_lastSpinDeviation_mul_overlapDeviation_le ξ hbound a b T hT2 τ)
  have hsymm := skVectorCavityAverage_one_overlap_variance_eq_last_spin (Y := Y) μ ξ hξ hbound β ρ
    q hgt hsym hg hg' a b T
    hTb
  have h0 := abs_skVectorCavityAverage_zero_sum_le μ ξ hξ hbound β ρ q hgm hg'm hYm a b T hTb hdec
  set K0 : ℝ := (d : ℝ) * d * (2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1)) with hK0
  set W1 := skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
    Fin (N + 1) → α => ∑ u, ∑ v,
      skVectorOverlapDeviation ξ N a b T u v (fun c => σ (some (some c))) ^ 2) with hW1
  rw [hsymm] at hstep
  have hκ : 0 ≤ 16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) := by positivity
  have hsq : Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin
    2)) →
        Fin (N + 1) → α => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
          (σ (some (some (0 : Fin 2)))) u v - ρ u v) ^ 2)) +
      Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2))))
          (σ (some (some (1 : Fin 2)))) u v - q u v) ^ 2)) ≤
      Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε) :=
    add_le_add (Real.sqrt_le_sqrt hXB) (Real.sqrt_le_sqrt hXA)
  calc W1 ≤ _ := hstep
    _ ≤ K0 + 16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) * Real.sqrt W1 *
        (Real.sqrt (2 * B + ε) + Real.sqrt (2 * A + ε)) := by
      refine add_le_add (le_trans (le_abs_self _) h0) ?_
      exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hκ (Real.sqrt_nonneg _))

/-- **Site invariance of i.i.d. standard Gaussian couplings.**  If the couplings `gt` have the law
of
an i.i.d. family of standard Gaussians, then their law is invariant under every relabelling of the
sites (`hsym` in Theorem 1.12.1). -/
theorem map_comp_pairPerm_eq_of_iid {M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {gt : FinPairs M → Ω → ℝ} (hgt : ∀ p, Measurable (gt p))
    (hlaw : Measure.map (fun ω p => gt p ω) P = Measure.pi fun _ : FinPairs M => gaussianReal 0 1)
    (π : Equiv.Perm (Fin M)) :
    Measure.map (fun ω => (fun p => gt p ω) ∘ (pairPerm π).symm) P =
      Measure.map (fun ω p => gt p ω) P := by
  have hgt' : Measurable fun ω p => gt p ω := measurable_pi_iff.2 hgt
  have h := (measurePreserving_comp_pairPerm (gaussianReal 0 1) π (N := M)).map_eq
  rw [hlaw]
  have : (fun ω => (fun p => gt p ω) ∘ (pairPerm π).symm) =
      (fun g : FinPairs M → ℝ => g ∘ (pairPerm π).symm) ∘ fun ω p => gt p ω := rfl
  have hφ : Measurable fun g : FinPairs M → ℝ => g ∘ (pairPerm π).symm :=
    measurable_pi_iff.2 fun p => measurable_pi_apply _
  rw [this, ← Measure.map_map hφ hgt', hlaw, h]

include hξ hbound in
/-- **Theorem 1.12.1 (Talagrand), the concentration of the overlaps.**  Let `(q, ρ)` satisfy the
fixed-point equations (1.372)--(1.373) for the Gaussian field `Y` of covariance `β² q`, and let
`β² d² ≤ 1/200`.  For the vector SK model with `N + 1` sites and a spin law `μ` with
`∑ᵤ ξ(a)ᵤ² ≤ d`, the expected squared errors of the overlaps
`A = ν(∑ᵤᵥ (R^{u,v}_{1,2} - qᵤᵥ)²)` and `B = ν(∑ᵤᵥ (R^{u,v}_{1,1} - ρᵤᵥ)²)` satisfy
`A + B ≤ (8 d⁴ + 2 d²)/(N + 1)`. Here `ν_1` is the cavity average at `t = 1`, i.e. the Gibbs
average of the `(N+1)`-site system whose couplings are the restriction of `gt`. -/
theorem sum_overlap_variances_le (hβ : β ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200)
    (hq : ∀ u v, q u v = ∫ ω,
      (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)))) ∂P)
    (hρ : ∀ u v, ρ u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
      (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))) ∂P)
    (hn : SKVectorCavityGaussianData P N d β q g g' Y)
    (hg : ∀ p ω, g p ω = gt ⟨(p.val.1.castSucc, p.val.2.castSucc),
      Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ ω)
    (hg' : ∀ i ω, g' i ω = gt ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩ ω)
    (hgt : ∀ p, Measurable (gt p))
    (hsym : ∀ π : Equiv.Perm (Fin (N + 1)),
      Measure.map (fun ω => (fun p => gt p ω) ∘ (pairPerm π).symm) P =
        Measure.map (fun ω p => gt p ω) P)
    (hind : IndepFun (fun ω p => g p ω) (fun ω u => Y u ω) P) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorOverlapDeviation ξ N 0 1 q u v (fun c => σ (some (some c))) ^ 2) +
      skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => ∑ u, ∑ v,
          skVectorOverlapDeviation ξ N 0 0 ρ u v (fun c => σ (some (some c))) ^ 2) ≤
      (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hgm := hn.measurable_old_coupling
  have hg'm := hn.measurable_new_coupling
  have hYm := hn.measurable_field
  obtain ⟨hq2, hρ2⟩ := sum_sq_skVectorFixedPoint_field_le μ ξ hξ hbound β q ρ hYm hρ hq
  have hqsym : ∀ u v, q u v = q v u := fun u v => by
    rw [hq u v, hq v u]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hqb : ∀ u v, |q u v| ≤ d := abs_entry_le_of_sum_sq_le q hq2
  have hρb : ∀ u v, |ρ u v| ≤ d := abs_entry_le_of_sum_sq_le ρ hρ2
  set ε : ℝ := 2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) ^ 2 with hε
  have hε0 : 0 ≤ ε := by positivity
  -- the cavity-overlap errors are controlled by the full overlap errors
  have hXA := skVectorCavityAverage_le_two_mul_add (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm 1
    (fun τ => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (τ 0) (τ 1) u v - q u v) ^ 2)
    (fun τ => ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 q u v τ ^ 2)
    (measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 1 q hq2).1
    (measurable_sum_sq_skVectorOverlapDeviation ξ hξ 0 1 q)
    (measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 1 q hq2).2.2
    (abs_sum_sq_skVectorOverlapDeviation_le ξ hbound 0 1 q hqb) ε
    (fun τ => sum_sq_cavityOverlap_deviation_le ξ hbound 0 1 q τ)
  have hXB := skVectorCavityAverage_le_two_mul_add (P := P) μ ξ hξ hbound β ρ q hgm hg'm hYm 1
    (fun τ => ∑ u, ∑ v, (skVectorCavityOverlap ξ N (τ 0) (τ 0) u v - ρ u v) ^ 2)
    (fun τ => ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 ρ u v τ ^ 2)
    (measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 0 ρ hρ2).1
    (measurable_sum_sq_skVectorOverlapDeviation ξ hξ 0 0 ρ)
    (measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 0 ρ hρ2).2.2
    (abs_sum_sq_skVectorOverlapDeviation_le ξ hbound 0 0 ρ hρb) ε
    (fun τ => sum_sq_cavityOverlap_deviation_le ξ hbound 0 0 ρ τ)
  have hnn : ∀ G : (Fin 2 → Fin (N + 1) → α) → ℝ, (∀ σ, 0 ≤ G σ) →
      0 ≤ skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => G fun c => σ (some (some c))) := fun G hG => by
    unfold skVectorCavityAverage
    exact integral_nonneg fun _ => integral_nonneg fun σ => hG _
  have hA0 := hnn (fun τ => ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 1 q u v τ ^ 2) fun τ =>
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hB0 := hnn (fun τ => ∑ u, ∑ v, skVectorOverlapDeviation ξ N 0 0 ρ u v τ ^ 2) fun τ =>
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hsideA := skVector_overlap_variance_le_sqrt μ ξ hξ hbound β ρ q hqsym hq2 hρ2 hn hg hg' hgt
    hsym 0 1 q
    hq2 (fun u v Ψ hΨ => skVectorCavityAverage_zero_pair_mul_eq_zero μ ξ hξ hbound β ρ q hgm hYm
      hind hq Ψ hΨ u v)
    _ _ ε hXA hXB
  have hsideB := skVector_overlap_variance_le_sqrt μ ξ hξ hbound β ρ q hqsym hq2 hρ2 hn hg hg' hgt
    hsym 0 0 ρ
    hρ2 (fun u v Ψ hΨ => skVectorCavityAverage_zero_diag_mul_eq_zero μ ξ hξ hbound β ρ q hgm hYm
      hind hρ Ψ hΨ u v)
    _ _ ε hXA hXB
  -- the smallness of the contraction constant
  have hs0 : 0 ≤ β ^ 2 * (d : ℝ) ^ 2 := by positivity
  have hκ : 16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) ≤ 1 / 6 := by
    have h20 : 20 * β ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 10 := by nlinarith
    have hexp : Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) ≤ 10 / 9 := by
      refine (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    calc 16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) ≤
          16 * β ^ 2 * (d : ℝ) ^ 2 * (10 / 9) := by
          refine mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1 / 6 := by nlinarith
  have hclose := add_le_of_coupled_sqrt_bounds hA0 hB0 hε0 (by positivity) hκ hsideA hsideB
  refine hclose.trans ?_
  have hM : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hM0 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have h1 : 2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) ^ 2 ≤ 2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) := by
    refine div_le_div_of_nonneg_left (by positivity) hM0 ?_
    nlinarith
  have h2 : 4 * ((d : ℝ) * d * (2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1))) =
      8 * (d : ℝ) ^ 4 / ((N : ℝ) + 1) := by
    field_simp
    ring
  calc 4 * ((d : ℝ) * d * (2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1))) + ε ≤
        8 * (d : ℝ) ^ 4 / ((N : ℝ) + 1) + 2 * (d : ℝ) ^ 2 / ((N : ℝ) + 1) := by
        rw [h2]; exact add_le_add le_rfl h1
    _ = _ := by rw [← add_div]

end Setup

end SpinGlasses
