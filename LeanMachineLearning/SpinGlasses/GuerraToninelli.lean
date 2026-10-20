/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Subadditive
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.JensenLog
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import LeanMachineLearning.SpinGlasses.GaussianComparison
public import LeanMachineLearning.SpinGlasses.MixedPSpin
public import LeanMachineLearning.SpinGlasses.ThermodynamicLimit

/-!
# The Guerra–Toninelli interpolation: superadditivity of the free energy

Let `H_N(σ)`, `σ ∈ {-1, 1}^N`, be centered Gaussian Hamiltonians with covariance
`𝔼 H_N(σ) H_N(τ) = N ξ(N⁻¹ σ ⬝ τ)` for a function `ξ` that is convex on `[-1, 1]`
([Panchenko, 2013, §1.3]).  Writing a configuration of `N + M` spins as a pair `(ρ, τ)` of
configurations of `N` and `M` spins (`Fin.appendEquiv`), the overlap splits as the convex
combination `R(σ, σ') = (N R(ρ, ρ') + M R(τ, τ')) / (N + M)`.  The Hamiltonian `H_{N+M}` is thus
*more correlated* than the independent sum `H_N(ρ) + H_M(τ)` in the sense of
`ξ(R) (N + M) ≤ N ξ(R(ρ, ρ')) + M ξ(R(τ, τ'))` (convexity), and the two have the same variances.
The Gaussian comparison inequality of `SpinGlasses/GaussianComparison.lean` (Gaussian integration
by parts along the Guerra–Toninelli path `√t H_{N+M} + √(1 - t)(H_N + H_M)`) gives
`𝔼 log Z_N + 𝔼 log Z_M ≤ 𝔼 log Z_{N+M}` (Eq. (1.36)), i.e. `N F_N + M F_M ≤ (N + M) F_{N+M}`.

The statement is *abstract in the model*: the Hamiltonian enters only through its Gaussian law and
covariance function `ξ`.  The Sherrington–Kirkpatrick model (`ξ(x) = x²`) and the mixed `p`-spin
models with even `p` and `p = 1` (`ξ(x) = ∑ₚ β_p² x^p`) are instances; no identification of the
SK model with the pure `p = 2` model (a nested versus flat disorder equivalence) is needed.

## Main declarations

* `SpinGlasses.add_mul_apply_le_of_convexOn`: the convexity inequality for weights `N, M`.
* `SpinGlasses.integral_log_sum_exp_add_le`: superadditivity of `N ↦ 𝔼 log Z_N`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3.
* [F. Guerra, F. L. Toninelli, *The thermodynamic limit in mean field spin glass models*,
  Comm. Math. Phys. 230, 2002].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Matrix Topology

namespace SpinGlasses

section Convexity

/-- **Weighted convexity:** for `ξ` convex on `s`, positive weights `a, b` and `x, y ∈ s`,
`(a + b) ξ((a x + b y) / (a + b)) ≤ a ξ(x) + b ξ(y)`. -/
theorem add_mul_apply_le_of_convexOn {s : Set ℝ} {ξ : ℝ → ℝ} (hξ : ConvexOn ℝ s ξ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    (a + b) * ξ ((a * x + b * y) / (a + b)) ≤ a * ξ x + b * ξ y := by
  have hab : 0 < a + b := add_pos ha hb
  have h := hξ.2 hx hy (div_pos ha hab).le (div_pos hb hab).le (by field_simp)
  simp only [smul_eq_mul] at h
  have e : (a * x + b * y) / (a + b) = a / (a + b) * x + b / (a + b) * y := by field_simp
  rw [e]
  calc (a + b) * ξ (a / (a + b) * x + b / (a + b) * y)
      ≤ (a + b) * (a / (a + b) * ξ x + b / (a + b) * ξ y) := mul_le_mul_of_nonneg_left h hab.le
    _ = a * ξ x + b * ξ y := by field_simp

end Convexity

section Overlap

variable {N M : ℕ}

/-- The dot product of two concatenated spin configurations is the sum of the dot products. -/
theorem dotProduct_cast_append (ρ ρ' : Fin N → ℤˣ) (τ τ' : Fin M → ℤˣ) :
    (fun i => (((Fin.append ρ τ i : ℤˣ) : ℤ) : ℝ)) ⬝ᵥ
        (fun i => (((Fin.append ρ' τ' i : ℤˣ) : ℤ) : ℝ)) =
      (fun i => ((ρ i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((ρ' i : ℤ) : ℝ)) +
        (fun i => ((τ i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((τ' i : ℤ) : ℝ)) := by
  simp [dotProduct, Fin.sum_univ_add]

/-- A hypercube configuration has self-overlap `1`: `σ ⬝ σ = K`. -/
theorem dotProduct_units_cast_self {K : ℕ} [Nonempty (Fin K)] (σ : Fin K → ℤˣ) :
    (fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((σ i : ℤ) : ℝ)) = K := by
  have h := card_inv_mul_dotProduct_self_eq_one (ι := Fin K) (fun i => ((σ i : ℤ) : ℝ))
    fun i => units_cast_sq (σ i)
  rw [Fintype.card_fin] at h
  have hK : (K : ℝ) ≠ 0 := (Nat.cast_pos.2 (Fin.pos_iff_nonempty.2 inferInstance)).ne'
  field_simp at h
  exact h

end Overlap

section Superadditivity

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {μ : ∀ N, Measure (Ω N)}
  {H : ∀ N, Ω N → (Fin N → ℤˣ) → ℝ} {ξ : ℝ → ℝ}

/-- **Integrability of the log-partition function of a Gaussian field on the hypercube.** -/
theorem integrable_log_sum_exp_of_hasGaussianLaw {K : ℕ} [IsProbabilityMeasure (μ K)]
    (hm : ∀ σ, Measurable fun ω => H K ω σ)
    (hG : HasGaussianLaw (fun ω σ => H K ω σ) (μ K)) :
    Integrable (fun ω => Real.log (∑ σ, Real.exp (H K ω σ))) (μ K) := by
  simpa using integrable_log_sum_exp (μ := μ K) (H := H K) one_pos hm
    fun σ => (hG.eval σ).integrable

/-- **Superadditivity of the expected log-partition function** (Guerra–Toninelli,
[Panchenko, 2013, Eq. (1.36)]).  Let `H N` be centered Gaussian Hamiltonians on the hypercubes
`Fin N → ℤˣ`, each with covariance `𝔼 H_N(σ) H_N(τ) = N ξ(N⁻¹ σ ⬝ τ)` for the same function `ξ`
convex on `[-1, 1]`.  Then for `N, M > 0`,
`𝔼 log Z_N + 𝔼 log Z_M ≤ 𝔼 log Z_{N+M}` with `Z_N = ∑_σ exp (H_N(σ))`.
(The disorders for different sizes live on different probability spaces `Ω N`.)  The proof is the
Gaussian comparison `integral_log_sum_exp_le_of_covariance_le` on `Ω (N+M) × (Ω N × Ω M)` between
`X(ρ, τ) = H_{N+M}(ρ ⌢ τ)` and the independent sum `Y(ρ, τ) = H_N(ρ) + H_M(τ)`. -/
theorem integral_log_sum_exp_add_le (hξ : ConvexOn ℝ (Set.Icc (-1) 1) ξ)
    (hm : ∀ N, 0 < N → ∀ σ, Measurable fun ω => H N ω σ)
    (hG : ∀ N, 0 < N → HasGaussianLaw (fun ω σ => H N ω σ) (μ N))
    (h0 : ∀ N, 0 < N → ∀ σ, ∫ ω, H N ω σ ∂μ N = 0)
    (hcov : ∀ N, 0 < N → ∀ σ τ, ∫ ω, H N ω σ * H N ω τ ∂μ N =
      N * ξ ((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))))
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N +
        ∫ ω, Real.log (∑ σ, Real.exp (H M ω σ)) ∂μ M ≤
      ∫ ω, Real.log (∑ σ, Real.exp (H (N + M) ω σ)) ∂μ (N + M) := by
  have hNM : 0 < N + M := add_pos hN hM
  have := (hG N hN).isProbabilityMeasure
  have := (hG M hM).isProbabilityMeasure
  have := (hG (N + M) hNM).isProbabilityMeasure
  have hvm : ∀ K (hK : 0 < K), Measurable fun ω => fun σ => H K ω σ := fun K hK =>
    measurable_pi_iff.2 (hm K hK)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  -- the product probability space and the Gaussian vector of the three Hamiltonians
  have hW := (hG (N + M) hNM).prodMk_prod ((hG N hN).prodMk_prod (hG M hM) (hvm N hN) (hvm M hM))
    (hvm (N + M) hNM)
    (((hvm N hN).comp measurable_fst).prodMk ((hvm M hM).comp measurable_snd))
  set μ' : Measure (Ω (N + M) × (Ω N × Ω M)) := (μ (N + M)).prod ((μ N).prod (μ M)) with hμ'
  have hF1 : ∀ σ, HasGaussianLaw (fun ω : Ω (N + M) × (Ω N × Ω M) => H (N + M) ω.1 σ) μ' :=
    fun σ => hW.fst.eval σ
  have hF2 : ∀ ρ, HasGaussianLaw (fun ω : Ω (N + M) × (Ω N × Ω M) => H N ω.2.1 ρ) μ' :=
    fun ρ => hW.snd.fst.eval ρ
  have hF3 : ∀ τ, HasGaussianLaw (fun ω : Ω (N + M) × (Ω N × Ω M) => H M ω.2.2 τ) μ' :=
    fun τ => hW.snd.snd.eval τ
  -- marginals of the product measure
  have hfst : ∀ f : Ω (N + M) → ℝ, ∫ ω, f ω.1 ∂μ' = ∫ ω, f ω ∂μ (N + M) := fun f => by
    simp [hμ', integral_fun_fst]
  have hsnd1 : ∀ f : Ω N → ℝ, ∫ ω, f ω.2.1 ∂μ' = ∫ ω, f ω ∂μ N := fun f => by
    have := integral_fun_snd (μ := μ (N + M)) (ν := (μ N).prod (μ M))
      (fun w : Ω N × Ω M => f w.1)
    simpa [hμ', integral_fun_fst] using this
  have hsnd2 : ∀ f : Ω M → ℝ, ∫ ω, f ω.2.2 ∂μ' = ∫ ω, f ω ∂μ M := fun f => by
    have := integral_fun_snd (μ := μ (N + M)) (ν := (μ N).prod (μ M))
      (fun w : Ω N × Ω M => f w.2)
    simpa [hμ', integral_fun_snd] using this
  -- the two fields: `X` of size `N + M`, and the independent sum `Y`
  set X : (Fin N → ℤˣ) × (Fin M → ℤˣ) → Ω (N + M) × (Ω N × Ω M) → ℝ :=
    fun a ω => H (N + M) ω.1 (Fin.appendEquiv N M a) with hX
  set Y : (Fin N → ℤˣ) × (Fin M → ℤˣ) → Ω (N + M) × (Ω N × Ω M) → ℝ :=
    fun a ω => H N ω.2.1 a.1 + H M ω.2.2 a.2 with hY
  have hXm : ∀ a, Measurable (X a) := fun a => (hm _ hNM _).comp measurable_fst
  have hYm : ∀ a, Measurable (Y a) := fun a =>
    ((hm _ hN _).comp (measurable_fst.comp measurable_snd)).add
      ((hm _ hM _).comp (measurable_snd.comp measurable_snd))
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) μ' := by
    let L : ((Fin (N + M) → ℤˣ) → ℝ) × (((Fin N → ℤˣ) → ℝ) × ((Fin M → ℤˣ) → ℝ)) →L[ℝ]
        (((Fin N → ℤˣ) × (Fin M → ℤˣ)) ⊕ ((Fin N → ℤˣ) × (Fin M → ℤˣ)) → ℝ) :=
      ContinuousLinearMap.pi (Sum.elim
        (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N + M) → ℤˣ => ℝ)
          (Fin.appendEquiv N M a)).comp (ContinuousLinearMap.fst ℝ _ _))
        (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N → ℤˣ => ℝ) a.1).comp
            ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)) +
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M → ℤˣ => ℝ) a.2).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))
    convert hW.map_fun L using 1
    ext ω (a | a) <;> simp [L, hX, hY]
  -- centering and cross-covariance
  have hX0 : ∀ a, ∫ ω, X a ω ∂μ' = 0 := fun a => by
    simp only [hX]
    rw [hfst (fun ω => H (N + M) ω (Fin.appendEquiv N M a))]
    exact h0 _ hNM _
  have hY0 : ∀ a, ∫ ω, Y a ω ∂μ' = 0 := fun a => by
    simp only [hY]
    rw [integral_add (hF2 a.1).integrable (hF3 a.2).integrable,
      hsnd1 (fun ω => H N ω a.1), hsnd2 (fun ω => H M ω a.2), h0 N hN, h0 M hM, add_zero]
  have h0XY : ∀ a b, ∫ ω, X a ω * Y b ω ∂μ' = 0 := fun a b => by
    have := integral_prod_mul (μ := μ (N + M)) (ν := (μ N).prod (μ M))
      (fun x => H (N + M) x (Fin.appendEquiv N M a))
      (fun w : Ω N × Ω M => H N w.1 b.1 + H M w.2 b.2)
    simp only [hX, hY, hμ']
    rw [this, h0 (N + M) hNM, zero_mul]
  -- covariances
  have hAA : ∀ a b, ∫ ω, X a ω * X b ω ∂μ' = ((N + M : ℕ) : ℝ) *
      ξ (((N + M : ℕ) : ℝ)⁻¹ * ((fun i => ((a.1 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.1 i : ℤ) : ℝ)) +
        (fun i => ((a.2 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.2 i : ℤ) : ℝ)))) := fun a b => by
    simp only [hX]
    rw [hfst (fun ω => H (N + M) ω (Fin.appendEquiv N M a) * H (N + M) ω (Fin.appendEquiv N M b)),
      hcov _ hNM]
    simp only [Fin.appendEquiv_apply, dotProduct_cast_append]
  have hBB : ∀ a b, ∫ ω, Y a ω * Y b ω ∂μ' =
      N * ξ ((N : ℝ)⁻¹ * ((fun i => ((a.1 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.1 i : ℤ) : ℝ)))) +
      M * ξ ((M : ℝ)⁻¹ * ((fun i => ((a.2 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.2 i : ℤ) : ℝ)))) :=
    fun a b => by
    set Y1 : (Fin N → ℤˣ) × (Fin M → ℤˣ) → Ω (N + M) × (Ω N × Ω M) → ℝ :=
      fun a ω => H N ω.2.1 a.1 with hY1
    set Y2 : (Fin N → ℤˣ) × (Fin M → ℤˣ) → Ω (N + M) × (Ω N × Ω M) → ℝ :=
      fun a ω => H M ω.2.2 a.2 with hY2
    have hY12 : HasGaussianLaw (fun ω s => Sum.elim Y1 Y2 s ω) μ' := by
      let L : ((Fin (N + M) → ℤˣ) → ℝ) × (((Fin N → ℤˣ) → ℝ) × ((Fin M → ℤˣ) → ℝ)) →L[ℝ]
          (((Fin N → ℤˣ) × (Fin M → ℤˣ)) ⊕ ((Fin N → ℤˣ) × (Fin M → ℤˣ)) → ℝ) :=
        ContinuousLinearMap.pi (Sum.elim
          (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N → ℤˣ => ℝ) a.1).comp
            ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))
          (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M → ℤˣ => ℝ) a.2).comp
            ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))
      convert hW.map_fun L using 1
      ext ω (a | a) <;> simp [L, hY1, hY2]
    have h012 : ∀ a b : (Fin N → ℤˣ) × (Fin M → ℤˣ),
        ∫ ω, Y1 a ω * Y2 b ω ∂μ' = 0 := fun a b => by
      have h1 := integral_fun_snd (μ := μ (N + M)) (ν := (μ N).prod (μ M))
        (fun w : Ω N × Ω M => H N w.1 a.1 * H M w.2 b.2)
      have h2 := integral_prod_mul (μ := μ N) (ν := μ M) (fun x => H N x a.1)
        (fun y => H M y b.2)
      simp only [hμ']
      rw [h1]
      simp [h2, h0 N hN]
    have := integral_lincomb_mul_lincomb hY12 h012 1 1 1 1 a b
    simp only [one_mul] at this
    simp only [hY]
    rw [this, hsnd1 (fun ω => H N ω a.1 * H N ω b.1), hsnd2 (fun ω => H M ω a.2 * H M ω b.2),
      hcov _ hN, hcov _ hM]
  -- equal variances (every self-overlap is `1`) and the covariance comparison (convexity of `ξ`)
  have hdiag : ∀ a, ∫ ω, Y a ω * Y a ω ∂μ' = ∫ ω, X a ω * X a ω ∂μ' := fun a => by
    rw [hAA, hBB, dotProduct_units_cast_self a.1, dotProduct_units_cast_self a.2]
    have e1 : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hNr.ne'
    have e2 : (M : ℝ)⁻¹ * M = 1 := inv_mul_cancel₀ hMr.ne'
    have e3 : ((N + M : ℕ) : ℝ)⁻¹ * ((N : ℝ) + M) = 1 := by
      push_cast
      exact inv_mul_cancel₀ (add_pos hNr hMr).ne'
    rw [e1, e2, e3]
    push_cast
    ring
  have hle : ∀ a b, ∫ ω, X a ω * X b ω ∂μ' ≤ ∫ ω, Y a ω * Y b ω ∂μ' := fun a b => by
    rw [hAA, hBB]
    have hx := abs_card_inv_mul_dotProduct_le_one (ι := Fin N) (fun i => ((a.1 i : ℤ) : ℝ))
      (fun i => ((b.1 i : ℤ) : ℝ)) (fun i => abs_units_cast_le_one _)
      fun i => abs_units_cast_le_one _
    have hy := abs_card_inv_mul_dotProduct_le_one (ι := Fin M) (fun i => ((a.2 i : ℤ) : ℝ))
      (fun i => ((b.2 i : ℤ) : ℝ)) (fun i => abs_units_cast_le_one _)
      fun i => abs_units_cast_le_one _
    rw [Fintype.card_fin] at hx hy
    have h := add_mul_apply_le_of_convexOn hξ hNr hMr (abs_le.1 hx |> fun h => ⟨h.1, h.2⟩)
      (abs_le.1 hy |> fun h => ⟨h.1, h.2⟩)
    have e : ((N + M : ℕ) : ℝ)⁻¹ * ((fun i => ((a.1 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.1 i : ℤ) : ℝ)) +
        (fun i => ((a.2 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.2 i : ℤ) : ℝ))) =
        (N * ((N : ℝ)⁻¹ * ((fun i => ((a.1 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.1 i : ℤ) : ℝ)))) +
          M * ((M : ℝ)⁻¹ * ((fun i => ((a.2 i : ℤ) : ℝ)) ⬝ᵥ (fun i => ((b.2 i : ℤ) : ℝ))))) /
          (N + M) := by
      push_cast
      field_simp
    rw [e]
    push_cast
    exact h
  -- Gaussian comparison and translation back to the three Hamiltonians
  have key := integral_log_sum_exp_le_of_covariance_le hXm hYm hXY hX0 hY0 h0XY hdiag hle
    (fun _ => (0 : ℝ))
  have hZ : ∀ K, ∀ ω, 0 < ∑ σ : Fin K → ℤˣ, Real.exp (H K ω σ) := fun K ω =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZY : ∀ ω, ∑ a, Real.exp (Y a ω + 0) =
      (∑ ρ, Real.exp (H N ω.2.1 ρ)) * ∑ τ, Real.exp (H M ω.2.2 τ) := fun ω => by
    simp only [add_zero, hY, Real.exp_add]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hZX : ∀ ω, ∑ a, Real.exp (X a ω + 0) = ∑ σ, Real.exp (H (N + M) ω.1 σ) := fun ω => by
    simp only [add_zero, hX]
    exact Equiv.sum_comp (Fin.appendEquiv N M) fun σ => Real.exp (H (N + M) ω.1 σ)
  have hintN := integrable_log_sum_exp_of_hasGaussianLaw (hm N hN) (hG N hN)
  have hintM := integrable_log_sum_exp_of_hasGaussianLaw (hm M hM) (hG M hM)
  calc ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N +
        ∫ ω, Real.log (∑ σ, Real.exp (H M ω σ)) ∂μ M
      = ∫ ω, (Real.log (∑ ρ, Real.exp (H N ω.2.1 ρ)) +
          Real.log (∑ τ, Real.exp (H M ω.2.2 τ))) ∂μ' := by
        rw [integral_add ((hintN.comp_fst (μ M)).comp_snd (μ (N + M)))
          ((hintM.comp_snd (μ N)).comp_snd (μ (N + M))),
          hsnd1 (fun ω => Real.log (∑ ρ, Real.exp (H N ω ρ))),
          hsnd2 (fun ω => Real.log (∑ τ, Real.exp (H M ω τ)))]
    _ = ∫ ω, Real.log (∑ a, Real.exp (Y a ω + (fun _ => (0 : ℝ)) a)) ∂μ' :=
        integral_congr_ae (ae_of_all _ fun ω => by
          simp only [hZY, ← Real.log_mul (hZ N ω.2.1).ne' (hZ M ω.2.2).ne'])
    _ ≤ ∫ ω, Real.log (∑ a, Real.exp (X a ω + (fun _ => (0 : ℝ)) a)) ∂μ' := key
    _ = ∫ ω, Real.log (∑ σ, Real.exp (H (N + M) ω.1 σ)) ∂μ' :=
        integral_congr_ae (ae_of_all _ fun ω => by simp only [hZX])
    _ = ∫ ω, Real.log (∑ σ, Real.exp (H (N + M) ω σ)) ∂μ (N + M) :=
        hfst (fun ω => Real.log (∑ σ, Real.exp (H (N + M) ω σ)))

variable (hm : ∀ N, 0 < N → ∀ σ, Measurable fun ω => H N ω σ)
  (hG : ∀ N, 0 < N → HasGaussianLaw (fun ω σ => H N ω σ) (μ N))
  (h0 : ∀ N, 0 < N → ∀ σ, ∫ ω, H N ω σ ∂μ N = 0)
  (hcov : ∀ N, 0 < N → ∀ σ τ, ∫ ω, H N ω σ * H N ω τ ∂μ N =
    N * ξ ((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))))

include hm hG h0 hcov

/-- **A priori bound on the free energy:** `𝔼 log Z_N ≤ N (log 2 + ξ(1) / 2)`.  By Jensen,
`𝔼 log Z_N ≤ log 𝔼 Z_N = log ∑_σ exp (Var H_N(σ) / 2)`, and `Var H_N(σ) = N ξ(1)`. -/
theorem integral_log_sum_exp_le {N : ℕ} (hN : 0 < N) :
    ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N ≤ N * (Real.log 2 + ξ 1 / 2) := by
  have : IsProbabilityMeasure (μ N) := (hG N hN).isProbabilityMeasure
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hZ : ∀ ω, 0 < ∑ σ : Fin N → ℤˣ, Real.exp (H N ω σ) := fun ω =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hexp : ∀ σ, Integrable (fun ω => Real.exp (H N ω σ)) (μ N) := fun σ => by
    simpa using integrable_exp_mul_of_hasGaussianLaw ((hG N hN).eval σ) 1
  have hint : Integrable (fun ω => ∑ σ, Real.exp (H N ω σ)) (μ N) :=
    integrable_finsetSum _ fun σ _ => hexp σ
  have hE : ∀ σ : Fin N → ℤˣ, ∫ ω, Real.exp (H N ω σ) ∂μ N = Real.exp (N * ξ 1 / 2) := fun σ => by
    have h := integral_exp_mul_of_hasGaussianLaw ((hG N hN).eval σ) 1
    have hvar : Var[fun ω => H N ω σ; μ N] = N * ξ 1 := by
      rw [variance_of_integral_eq_zero ((hG N hN).eval σ).aemeasurable (h0 N hN σ)]
      simp only [pow_two]
      rw [hcov N hN σ σ, dotProduct_units_cast_self, inv_mul_cancel₀ (Nat.cast_pos.2 hN).ne']
    simpa [h0 N hN σ, hvar] using h
  refine (integral_log_le_log_integral hZ hint
    (integrable_log_sum_exp_of_hasGaussianLaw (hm N hN) (hG N hN))).trans ?_
  rw [integral_finsetSum _ fun σ _ => hexp σ]
  simp only [hE, Finset.sum_const, Finset.card_univ, card_spin_configurations, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
  exact le_of_eq (by ring)

/-- **Existence of the thermodynamic limit** (Guerra–Toninelli, [Panchenko, 2013, Theorem 1.1]):
for centered Gaussian Hamiltonians on the hypercubes with covariance `N ξ(R)` and `ξ` convex on
`[-1, 1]`, `F_N = N⁻¹ 𝔼 log Z_N` converges to `sup_{N ≥ 1} F_N`.  Superadditivity of `N F_N`
(`integral_log_sum_exp_add_le`), an a priori bound (`integral_log_sum_exp_le`) and Fekete's lemma
(`tendsto_div_atTop_sSup_of_superadditive`). -/
theorem tendsto_free_energy (hξ : ConvexOn ℝ (Set.Icc (-1) 1) ξ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N) atTop
      (𝓝 (sSup ((fun N : ℕ => (N : ℝ)⁻¹ *
        ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N) '' Set.Ici 1))) := by
  set I : ℕ → ℝ := fun N => ∫ ω, Real.log (∑ σ, Real.exp (H N ω σ)) ∂μ N with hI
  set u : ℕ → ℝ := fun N => N * ((N : ℝ)⁻¹ * I N) with hu
  have hu0 : u 0 = 0 := by simp [hu]
  have hu1 : ∀ N, 0 < N → u N = I N := fun N hN => by
    have : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
    simp only [hu]
    field_simp
  have hq : ∀ N : ℕ, u N / N = (N : ℝ)⁻¹ * I N := fun N => by
    rcases N.eq_zero_or_pos with rfl | hN
    · simp [hu]
    · have : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
      simp only [hu]
      field_simp
  have hsup : ∀ m n, u m + u n ≤ u (m + n) := fun m n => by
    rcases m.eq_zero_or_pos with rfl | hm'
    · simp [hu0]
    rcases n.eq_zero_or_pos with rfl | hn'
    · simp [hu0]
    rw [hu1 m hm', hu1 n hn', hu1 (m + n) (add_pos hm' hn')]
    exact integral_log_sum_exp_add_le hξ hm hG h0 hcov hm' hn'
  have hbdd : BddAbove (Set.range fun N : ℕ => u N / N) := by
    refine ⟨max (Real.log 2 + ξ 1 / 2) 0, ?_⟩
    rintro _ ⟨N, rfl⟩
    change u N / (N : ℝ) ≤ _
    rw [hq]
    rcases N.eq_zero_or_pos with rfl | hN
    · simp
    · have h := integral_log_sum_exp_le hm hG h0 hcov hN
      have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
      refine le_max_of_le_left ?_
      rw [← div_eq_inv_mul, div_le_iff₀ hNr]
      linarith [h]
  have := tendsto_div_atTop_sSup_of_superadditive hsup hbdd
  simp only [hq] at this
  exact this

omit hm hG h0 hcov in
/-- **The thermodynamic limit at inverse temperature `β`:** the Hamiltonian `β H_N` has
covariance `N (β² ξ)(R)` with `β² ξ` again convex, so `tendsto_free_energy` applies. -/
theorem tendsto_free_energy_mul (hm : ∀ N, 0 < N → ∀ σ, Measurable fun ω => H N ω σ)
    (hG : ∀ N, 0 < N → HasGaussianLaw (fun ω σ => H N ω σ) (μ N))
    (h0 : ∀ N, 0 < N → ∀ σ, ∫ ω, H N ω σ ∂μ N = 0)
    (hcov : ∀ N, 0 < N → ∀ σ τ, ∫ ω, H N ω σ * H N ω τ ∂μ N =
      N * ξ ((N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))))
    (hξ : ConvexOn ℝ (Set.Icc (-1) 1) ξ) (β : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ ω, Real.log (∑ σ, Real.exp (β * H N ω σ)) ∂μ N) atTop
      (𝓝 (sSup ((fun N : ℕ => (N : ℝ)⁻¹ *
        ∫ ω, Real.log (∑ σ, Real.exp (β * H N ω σ)) ∂μ N) '' Set.Ici 1))) := by
  refine tendsto_free_energy (H := fun N ω σ => β * H N ω σ) (ξ := fun x => β ^ 2 * ξ x)
    (fun N hN σ => (hm N hN σ).const_mul β) (fun N hN => ?_) (fun N hN σ => ?_)
    (fun N hN σ τ => ?_) (by simpa using hξ.smul (sq_nonneg β))
  · simpa [Pi.smul_def] using (hG N hN).fun_smul β
  · rw [integral_const_mul, h0 N hN σ, mul_zero]
  · have : ∀ ω, β * H N ω σ * (β * H N ω τ) = β ^ 2 * (H N ω σ * H N ω τ) := fun ω => by ring
    simp_rw [this]
    rw [integral_const_mul, hcov N hN σ τ]
    ring

end Superadditivity

section SK

variable (H : ∀ N : ℕ, (Fin N → Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N G σ, H N G σ = (Real.sqrt N)⁻¹ *
    ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ (Matrix.of G *ᵥ fun i => ((σ i : ℤ) : ℝ))))

include hH

/-- **The thermodynamic limit of the SK model** (Guerra–Toninelli, [Panchenko, 2013,
Theorem 1.1]): for the Hamiltonian `H_N(σ) = (√N)⁻¹ σ ⬝ (G σ)` with standard Gaussian disorder and
every `β`, `F_N(β) = N⁻¹ 𝔼 log Z_N(β)` converges, to `sup_{N ≥ 1} F_N(β)`.  The SK covariance
`𝔼 H_N(σ) H_N(τ) = N R(σ, τ)²` is that of `ξ(x) = x²`, convex, so the abstract
`tendsto_free_energy_mul` applies; this discharges the hypothesis `h_lim` of
`sk_monotoneOn_inv_mul_limit_sub_log_two` and `sk_exists_tendsto_ground_state_energy`. -/
theorem sk_tendsto_free_energy (β : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) atTop
      (𝓝 (sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) ''
          Set.Ici 1))) := by
  refine tendsto_free_energy_mul (Ω := fun N : ℕ => Fin N → Fin N → ℝ)
    (μ := fun N : ℕ => Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (H := H) (ξ := fun x => x ^ 2) (fun N hN σ => ?_) (fun N hN => ?_) (fun N hN σ => ?_)
    (fun N hN σ τ => ?_)
    (Even.convexOn_pow even_two |>.subset (Set.subset_univ _) (convex_Icc _ _)) β
  · simpa only [hH, Fintype.card_fin] using (sk_measurable_integrable σ).1
  · exact hasGaussianLaw_skHamiltonian (H N) fun G σ => by
      simpa only [Fintype.card_fin] using hH N G σ
  · exact integral_skHamiltonian_eq_zero (H N) (fun G σ => by
      simpa only [Fintype.card_fin] using hH N G σ) σ
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simpa only [Fintype.card_fin] using integral_skHamiltonian_mul_skHamiltonian_units (H N)
      (fun G σ => by simpa only [Fintype.card_fin] using hH N G σ) σ τ

/-- **The ground-state energy of the SK model converges** ([Panchenko, 2013, Eq. (1.10)]):
`N⁻¹ 𝔼 max_σ H_N(σ)` converges.  Unlike `sk_exists_tendsto_ground_state_energy`, no free-energy
limit is assumed: it is supplied by `sk_tendsto_free_energy`. -/
theorem sk_tendsto_ground_state_energy :
    ∃ E₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, (H N G).max
      ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) atTop
        (𝓝 E₀) :=
  (sk_exists_tendsto_ground_state_energy H hH
    (F := fun β => sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) ''
          Set.Ici 1))
    fun β _ => sk_tendsto_free_energy H hH β).imp fun _ h => h.1

/-- **Monotonicity of the SK free energy in the temperature, unconditionally:** with
`F(β) = lim_N F_N(β) = sup_{N ≥ 1} F_N(β)`, the function `β ↦ β⁻¹ (F(β) - log 2)` is
non-decreasing on `(0, ∞)`. -/
theorem sk_monotoneOn_free_energy_limit :
    MonotoneOn (fun β : ℝ => β⁻¹ * (sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ G,
      Real.log (∑ σ, Real.exp (β * H N G σ))
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) ''
          Set.Ici 1) - Real.log 2)) (Set.Ioi 0) :=
  sk_monotoneOn_inv_mul_limit_sub_log_two H hH
    (F := fun β => sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ G, Real.log (∑ σ, Real.exp (β * H N G σ))
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin N => gaussianReal 0 1)) ''
          Set.Ici 1))
    fun β _ => sk_tendsto_free_energy H hH β

end SK

section Mixed

variable {β : ℕ → ℝ}

/-- **Convexity of the covariance function** ([Panchenko, 2013, §1.3]): if `β_p = 0` for every odd
`p ≥ 3` and `∑ₚ |β_p| < ∞`, then `ξ(x) = ∑ₚ β_p² x^p` is convex on `[-1, 1]`.  Each term is convex:
`x^p` for even `p`, the linear function `x` for `p = 1`, and the term vanishes for odd `p ≥ 3`. -/
theorem convexOn_sum_sq_mul_pow (hβ : Summable fun p => |β p|)
    (hodd : ∀ p, Odd p → 3 ≤ p → β p = 0) :
    ConvexOn ℝ (Set.Icc (-1) 1) (fun x => ∑' p, β p ^ 2 * x ^ p) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hs : ∀ z ∈ Set.Icc (-1 : ℝ) 1, Summable fun p => β p ^ 2 * z ^ p := fun z hz =>
    summable_sq_mul_pow_of_summable_abs hβ (abs_le.2 hz)
  have hz : a • x + b • y ∈ Set.Icc (-1 : ℝ) 1 := (convex_Icc (-1 : ℝ) 1) hx hy ha hb hab
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((hs x hx).mul_left a) ((hs y hy).mul_left b)]
  refine (hs _ hz).tsum_le_tsum (fun p => ?_) (((hs x hx).mul_left a).add ((hs y hy).mul_left b))
  by_cases hp : β p = 0
  · simp [hp]
  rcases Nat.even_or_odd p with he | ho
  · have h := (Even.convexOn_pow he).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h
    calc β p ^ 2 * (a * x + b * y) ^ p ≤ β p ^ 2 * (a * x ^ p + b * y ^ p) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = a * (β p ^ 2 * x ^ p) + b * (β p ^ 2 * y ^ p) := by ring
  · have hp1 : p = 1 := by
      by_contra hne
      exact hp (hodd p ho (by obtain ⟨k, rfl⟩ := ho; omega))
    subst hp1
    have : b = 1 - a := by linarith
    subst this
    simp only [pow_one]
    ring_nf
    exact le_rfl

end Mixed

section MixedModel

variable {β : ℕ → ℝ} (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|)
  (hodd : ∀ p, Odd p → 3 ≤ p → β p = 0)
  (H : ∀ N : ℕ, (∀ p : ℕ, (Fin p → Fin N) → ℝ) → (Fin N → ℤˣ) → ℝ)
  (hH : ∀ N g σ, H N g σ = ∑' p, β p * ((Real.sqrt N)⁻¹ ^ (p - 1) *
    ∑ idx, g p idx * ∏ k, ((σ (idx k) : ℤ) : ℝ)))

include hβ0 hβ hodd hH

omit hβ0 hβ hodd in
/-- The mixed Hamiltonian written with `Fintype.card (Fin N)`, as in `MixedPSpin.lean`. -/
private lemma mixedPSpin_hH' (N : ℕ) : ∀ g σ, H N g σ = ∑' p, β p *
    ((Real.sqrt (Fintype.card (Fin N)))⁻¹ ^ (p - 1) *
      ∑ idx, g p idx * ∏ k, ((σ (idx k) : ℤ) : ℝ)) := fun g σ => by
  simpa only [Fintype.card_fin] using hH N g σ

omit hβ hodd in
/-- With no spins the Hamiltonian vanishes: `Fin p → Fin 0` is empty for `p ≥ 1`, and `β₀ = 0`. -/
private lemma mixedPSpin_zero (g σ) : H 0 g σ = 0 := by
  rw [hH 0 g σ]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rcases p with _ | p
  · simp [hβ0]
  · simp

/-- **The thermodynamic limit of the mixed `p`-spin model with even `p` and `p = 1`**
(Guerra–Toninelli, [Panchenko, 2013, Theorem 1.1]): if `β₀ = 0`, `∑ₚ |β_p| < ∞` and `β_p = 0`
for odd `p ≥ 3`, then for every inverse temperature `t`, `F_N(t) = N⁻¹ 𝔼 log Z_N(t)` converges, to
`sup_{N ≥ 1} F_N(t)`.  The covariance function `ξ(x) = ∑ₚ β_p² x^p` is convex on `[-1, 1]`
(`convexOn_sum_sq_mul_pow`), and the Hamiltonian is a Gaussian process
(`mixedPSpin_hasGaussianLaw`), so the abstract `tendsto_free_energy_mul` applies. -/
theorem mixedPSpin_tendsto_free_energy (t : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ g, Real.log (∑ σ, Real.exp (t * H N g σ))
        ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N => gaussianReal 0 1))
      atTop
      (𝓝 (sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ g, Real.log (∑ σ, Real.exp (t * H N g σ))
        ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N => gaussianReal 0 1))
          '' Set.Ici 1))) := by
  refine tendsto_free_energy_mul
    (Ω := fun N : ℕ => ∀ p : ℕ, (Fin p → Fin N) → ℝ)
    (μ := fun N : ℕ => Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N =>
      gaussianReal 0 1)
    (H := H) (ξ := fun x => ∑' p, β p ^ 2 * x ^ p) (fun N hN σ => ?_) (fun N hN => ?_)
    (fun N hN σ => ?_) (fun N hN σ τ => ?_) (convexOn_sum_sq_mul_pow hβ hodd) t
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact (mixedPSpin_hypercube_hyps (H N) (mixedPSpin_hH' H hH N) hβ0 hβ σ).1
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact mixedPSpin_hasGaussianLaw (H N) (mixedPSpin_hH' H hH N) hβ0 hβ
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    exact integral_mixedPSpin_eq_zero (H N) (mixedPSpin_hH' H hH N) hβ0 hβ σ
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simpa only [Fintype.card_fin] using integral_mixedPSpin_hypercube_mul_mixedPSpin_hypercube
      (H N) (mixedPSpin_hH' H hH N) hβ0 hβ σ τ

/-- **The ground-state energy of the mixed `p`-spin model converges** ([Panchenko, 2013,
Eq. (1.10)]) for `β₀ = 0`, `∑ₚ |β_p| < ∞` and `β_p = 0` for odd `p ≥ 3`: `N⁻¹ 𝔼 max_σ H_N(σ)`
converges, the free-energy limits being supplied by `mixedPSpin_tendsto_free_energy`. -/
theorem mixedPSpin_tendsto_ground_state_energy :
    ∃ E₀, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ g, (H N g).max
      ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N => gaussianReal 0 1))
        atTop (𝓝 E₀) := by
  have := exists_tendsto_ground_state_energy (ι := fun N : ℕ => Fin N) (l := atTop)
    (Ω := fun N : ℕ => ∀ p : ℕ, (Fin p → Fin N) → ℝ)
    (μ := fun N : ℕ => Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N =>
      gaussianReal 0 1)
    (H := H)
    (fun N σ => by
      rcases N.eq_zero_or_pos with rfl | hN
      · simp only [mixedPSpin_zero hβ0 H hH]
        exact measurable_const
      · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        exact (mixedPSpin_hypercube_hyps (H N) (mixedPSpin_hH' H hH N) hβ0 hβ σ).1)
    (fun N σ => by
      rcases N.eq_zero_or_pos with rfl | hN
      · simp only [mixedPSpin_zero hβ0 H hH]
        exact integrable_const _
      · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        exact (mixedPSpin_hypercube_hyps (H N) (mixedPSpin_hH' H hH N) hβ0 hβ σ).2)
    (F := fun t => sSup ((fun N : ℕ => (N : ℝ)⁻¹ * ∫ g, Real.log (∑ σ, Real.exp (t * H N g σ))
        ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → Fin N => gaussianReal 0 1))
          '' Set.Ici 1))
    (fun t _ => by
      simpa only [Fintype.card_fin] using mixedPSpin_tendsto_free_energy hβ0 hβ hodd H hH t)
  simpa only [Fintype.card_fin] using this.imp fun _ h => h.1

end MixedModel

end SpinGlasses
