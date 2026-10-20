/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica
public import LeanMachineLearning.SpinGlasses.SKSmartPath
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ChebyshevAssociation

/-!
# Latała's compensated functional (Talagrand, Lemma 1.4.5 and Corollaries 1.4.6-1.4.7)

This module proves the replica-decoupling inequality and the monotonicity of the compensated
exponential functional along a trigonometric Gaussian interpolation.  Everything is done for an
abstract nonnegative symmetric "overlap function" `A : α → α → ℝ` with constant diagonal and
`U σ τ = -κ (A σ τ - c)`; the Sherrington–Kirkpatrick instance
`A σ τ = (R(σ, τ) - q)²` is a consequence of Talagrand's Eq. (1.64).

## Main declarations

* `SpinGlasses.replica_decoupling_comb_nonneg`: pointwise (in the disorder) form of Lemma 1.4.5
  combined with the derivative formula of Lemma 1.4.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

variable [Finite α] [Nonempty α]

/-- **Lemma 1.4.5 (replica decoupling) inside the derivative formula.**  For a Gibbs measure
`count.tilted f`, a nonnegative symmetric overlap function `A` with constant diagonal, covariances
`U σ τ = -κ (A σ τ - c)` with `κ ≥ 0`, and `u ≥ 0`, the combination of Lemma 1.4.2 for
`Φ(σ¹, σ²) = exp (u A(σ¹, σ²))` plus the moving-observable term `8 κ ⟨A exp (u A)⟩` is
nonnegative.  The proof is Chebyshev's association inequality
`⟨A⟩ ⟨exp (u A)⟩ ≤ ⟨A exp (u A)⟩` for the independent replicas `σ³, σ⁴`. -/
theorem replica_decoupling_comb_nonneg (f : α → ℝ) (A U : α → α → ℝ) (κ c a₀ u : ℝ)
    (hA0 : ∀ σ τ, 0 ≤ A σ τ) (hAs : ∀ σ τ, A σ τ = A τ σ) (hAd : ∀ σ, A σ σ = a₀)
    (hU : ∀ σ τ, U σ τ = -κ * (A σ τ - c)) (hκ : 0 ≤ κ) (hu : 0 ≤ u) :
    0 ≤ ∫ τ : Option (Option (Fin 2)) → α,
        Real.exp (u * A (τ (some (some 0))) (τ (some (some 1)))) *
          ((∑ r : Fin 2, ∑ r' : Fin 2, U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card (Fin 2) * ∑ r : Fin 2, U (τ (some (some r))) (τ (some none)) -
            Fintype.card (Fin 2) * U (τ (some none)) (τ (some none)) +
            Fintype.card (Fin 2) * (Fintype.card (Fin 2) + 1) * U (τ (some none)) (τ none))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => Measure.count.tilted f) +
      8 * κ * ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Real.exp (u * A (σ 0) (σ 1))
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) := by
  classical
  set μ : Measure α := Measure.count.tilted f with hμ
  set Φ : (Fin 2 → α) → ℝ := fun σ => Real.exp (u * A (σ 0) (σ 1)) with hΦ
  -- the integrand is `-κ (2 A₁₂ - 4 A₁₃ - 4 A₂₃ + 6 A₃₄) Φ`
  have hpt : ∀ τ : Option (Option (Fin 2)) → α,
      Real.exp (u * A (τ (some (some 0))) (τ (some (some 1)))) *
          ((∑ r : Fin 2, ∑ r' : Fin 2, U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card (Fin 2) * ∑ r : Fin 2, U (τ (some (some r))) (τ (some none)) -
            Fintype.card (Fin 2) * U (τ (some none)) (τ (some none)) +
            Fintype.card (Fin 2) * (Fintype.card (Fin 2) + 1) * U (τ (some none)) (τ none)) =
        (-κ * 2) * (Φ (fun r => τ (some (some r))) * A (τ (some (some 0))) (τ (some (some 1)))) +
          (4 * κ) * (Φ (fun r => τ (some (some r))) * A (τ (some (some 0))) (τ (some none))) +
          (4 * κ) * (Φ (fun r => τ (some (some r))) * A (τ (some (some 1))) (τ (some none))) +
          (-κ * 6) * (Φ (fun r => τ (some (some r))) * A (τ (some none)) (τ none)) := fun τ => by
    simp only [hΦ, hU, Fin.sum_univ_two, Fintype.card_fin, hAd]
    rw [hAs (τ (some (some 1))) (τ (some (some 0)))]
    push_cast
    ring
  simp_rw [hpt]
  simp only [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
  -- the four integrals
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hG : ∀ G : (Fin 2 → α) → ℝ,
      ∫ τ : Option (Option (Fin 2)) → α, G (fun r => τ (some (some r)))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) =
        ∫ σ, G σ ∂(Measure.pi fun _ : Fin 2 => μ) := fun G =>
    (integral_pi_option_count_tilted_marginal (R := Option (Fin 2)) f
      (fun σ' => G (fun r => σ' (some r)))).trans
      (integral_pi_option_count_tilted_marginal (R := Fin 2) f G)
  have h12 : ∫ τ : Option (Option (Fin 2)) → α,
      Φ (fun r => τ (some (some r))) * A (τ (some (some 0))) (τ (some (some 1)))
        ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) =
      ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Φ σ ∂(Measure.pi fun _ : Fin 2 => μ) := by
    rw [← integral_congr_ae (ae_of_all _ fun σ : Fin 2 → α => mul_comm (Φ σ) (A (σ 0) (σ 1)))]
    exact hG fun σ => Φ σ * A (σ 0) (σ 1)
  have h13 : 0 ≤ ∫ τ : Option (Option (Fin 2)) → α,
      Φ (fun r => τ (some (some r))) * A (τ (some (some 0))) (τ (some none))
        ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) :=
    integral_nonneg fun τ => mul_nonneg (Real.exp_pos _).le (hA0 _ _)
  have h23 : 0 ≤ ∫ τ : Option (Option (Fin 2)) → α,
      Φ (fun r => τ (some (some r))) * A (τ (some (some 1))) (τ (some none))
        ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) :=
    integral_nonneg fun τ => mul_nonneg (Real.exp_pos _).le (hA0 _ _)
  have h34 : ∫ τ : Option (Option (Fin 2)) → α,
      Φ (fun r => τ (some (some r))) * A (τ (some none)) (τ none)
        ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) =
      (∫ σ, Φ σ ∂(Measure.pi fun _ : Fin 2 => μ)) *
        ∫ σ : Fin 2 → α, A (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ) := by
    rw [integral_pi_fin_two μ (fun x y => A x y)]
    have h1 := integral_pi_option_count_tilted (R := Option (Fin 2)) f
      (fun σ' a => Φ (fun r => σ' (some r)) * A (σ' none) a)
    simp only at h1
    have h2 := integral_pi_option_count_tilted (R := Fin 2) f
      (fun σ x => ∫ a, Φ σ * A x a ∂μ)
    rw [h1, h2]
    simp_rw [integral_const_mul]
    exact integral_mul_const _ _
  have hcheb : (∫ σ : Fin 2 → α, A (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ)) *
      ∫ σ, Φ σ ∂(Measure.pi fun _ : Fin 2 => μ) ≤
      ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Φ σ ∂(Measure.pi fun _ : Fin 2 => μ) :=
    integral_comp_mul_integral_comp_le (X := fun σ : Fin 2 → α => A (σ 0) (σ 1))
      (f := id) (g := fun t => Real.exp (u * t)) monotone_id
      (fun a b hab => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hab hu))
      Integrable.of_finite Integrable.of_finite Integrable.of_finite
  rw [h12, h34]
  have hmain : 0 ≤ κ * (6 * ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Φ σ ∂(Measure.pi fun _ : Fin 2 => μ) +
      4 * ∫ τ : Option (Option (Fin 2)) → α,
        Φ (fun r => τ (some (some r))) * A (τ (some (some 0))) (τ (some none))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) +
      4 * ∫ τ : Option (Option (Fin 2)) → α,
        Φ (fun r => τ (some (some r))) * A (τ (some (some 1))) (τ (some none))
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => μ) -
      6 * ((∫ σ, Φ σ ∂(Measure.pi fun _ : Fin 2 => μ)) *
        ∫ σ : Fin 2 → α, A (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ))) :=
    mul_nonneg hκ (by linarith)
  have e : ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Real.exp (u * A (σ 0) (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => μ) =
      ∫ σ : Fin 2 → α, A (σ 0) (σ 1) * Φ σ ∂(Measure.pi fun _ : Fin 2 => μ) := rfl
  rw [e]
  linarith

section Compensated

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : α → Ω → ℝ}

/-- **Monotonicity of the compensated functional (Talagrand, Corollary 1.4.7).**
Along the trigonometric interpolation `s ↦ cos s · X + sin s · Y + h` between two jointly Gaussian
centred fields with `𝔼 X Y = 0`, suppose the covariance difference is
`𝔼 Y_σ Y_τ - 𝔼 X_σ X_τ = -κ (A σ τ - c)` for a nonnegative symmetric function `A` with constant
diagonal and `κ ≥ 0`.  Then for `u₀ ≥ 4 κ` the functional
`s ↦ 𝔼⟨exp ((u₀ - 4 κ cos² s) A(σ¹, σ²))⟩_s` is nondecreasing on `[0, π/2]`. -/
theorem monotoneOn_compensated_functional
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (h : α → ℝ) (A : α → α → ℝ) (κ c a₀ u₀ : ℝ)
    (hcov : ∀ σ τ, ∫ ω, Y σ ω * Y τ ω ∂P - ∫ ω, X σ ω * X τ ω ∂P = -κ * (A σ τ - c))
    (hA0 : ∀ σ τ, 0 ≤ A σ τ) (hAs : ∀ σ τ, A σ τ = A τ σ) (hAd : ∀ σ, A σ σ = a₀)
    (hκ : 0 ≤ κ) (hu₀ : 4 * κ ≤ u₀) :
    MonotoneOn (fun s => ∫ ω, ∫ σ : Fin 2 → α,
        Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1))
          ∂(Measure.pi fun _ : Fin 2 =>
            Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + h a) ∂P)
      (Set.Icc 0 (Real.pi / 2)) := by
  classical
  have hP := hXY.isProbabilityMeasure
  obtain ⟨K, hK⟩ : ∃ K, ∀ σ τ, A σ τ ≤ K :=
    (Set.finite_range fun p : α × α => A p.1 p.2).bddAbove.imp fun K hK σ τ => hK ⟨(σ, τ), rfl⟩
  set C : ℝ := |u₀| + 4 * |κ| with hC
  have hC0 : 0 ≤ C := by positivity
  have hu : ∀ s, |u₀ - 4 * κ * Real.cos s ^ 2| ≤ C := fun s => by
    refine (abs_sub _ _).trans ?_
    have e : |4 * κ * Real.cos s ^ 2| = 4 * |κ| * Real.cos s ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_nonneg (sq_nonneg (Real.cos s))]
    rw [e, hC]
    have := Real.cos_sq_le_one s
    nlinarith [abs_nonneg κ, abs_nonneg u₀]
  set M : ℝ := Real.exp (C * K) with hM
  have hbd : ∀ s (σ : Fin 2 → α), Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1)) ≤ M :=
    fun s σ => Real.exp_le_exp.2 <| by
      have h1 := (le_abs_self _).trans (hu s)
      have h2 := hA0 (σ 0) (σ 1)
      have h3 := hK (σ 0) (σ 1)
      nlinarith [mul_le_mul_of_nonneg_right h1 h2, mul_le_mul_of_nonneg_left h3 hC0]
  have hK0 : 0 ≤ K := (hA0 (Classical.arbitrary α) (Classical.arbitrary α)).trans
    (hK _ _)
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  have hg : ∀ (t : ℝ) a, AEMeasurable (fun ω => Real.cos t * X a ω + Real.sin t * Y a ω + h a)
      P := fun t a => ((((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _).aemeasurable
  have hderiv : ∀ t, HasDerivAt (fun s => ∫ ω, ∫ σ : Fin 2 → α,
        Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1))
          ∂(Measure.pi fun _ : Fin 2 =>
            Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + h a) ∂P) _ t :=
    fun t => hasDerivAt_integral_replica_trig_moving (R := Fin 2) hXm hYm hXY hX hY h0
      (fun a b => ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P) (fun _ _ => rfl) h
      (Φ := fun s σ => Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1)))
      (Φ' := fun s σ => (8 * κ * Real.sin s * Real.cos s) *
        (A (σ 0) (σ 1) * Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1))))
      (M := M) (M' := 8 * |κ| * (K * M))
      (fun s σ => by
        have hu : HasDerivAt (fun s => (u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1))
            (8 * κ * Real.sin s * Real.cos s * A (σ 0) (σ 1)) s := by
          have := (((Real.hasDerivAt_cos s).pow 2).const_mul (4 * κ)).const_sub u₀
            |>.mul_const (A (σ 0) (σ 1))
          convert this using 1
          simp only [Nat.cast_ofNat]
          ring
        convert hu.exp using 1
        ring)
      (fun s σ => by
        rw [abs_of_pos (Real.exp_pos _)]; exact hbd s σ)
      (fun s σ => by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8),
          abs_of_nonneg (hA0 _ _), abs_of_pos (Real.exp_pos _)]
        have hs := Real.abs_sin_le_one s
        have hc := Real.abs_cos_le_one s
        have hsc : |Real.sin s| * |Real.cos s| ≤ 1 := by
          nlinarith [abs_nonneg (Real.sin s), abs_nonneg (Real.cos s)]
        have hAe : A (σ 0) (σ 1) * Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1)) ≤
            K * M := mul_le_mul (hK _ _) (hbd s σ) (Real.exp_pos _).le hK0
        have hAe0 : 0 ≤ A (σ 0) (σ 1) *
            Real.exp ((u₀ - 4 * κ * Real.cos s ^ 2) * A (σ 0) (σ 1)) :=
          mul_nonneg (hA0 _ _) (Real.exp_pos _).le
        nlinarith [abs_nonneg κ, mul_nonneg (abs_nonneg κ) hAe0,
          mul_le_mul_of_nonneg_left hsc (mul_nonneg (abs_nonneg κ) hAe0)])
      t
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (Real.pi / 2))
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt) fun t ht => ?_
  rw [interior_Icc] at ht
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le
    (ht.2.le.trans (by linarith [Real.pi_pos]))
  have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [ht.1, Real.pi_pos], ht.2.le⟩
  have hu0 : 0 ≤ u₀ - 4 * κ * Real.cos t ^ 2 := by nlinarith [Real.cos_sq_le_one t]
  rw [← integral_const_mul, ← integral_add]
  · refine integral_nonneg fun ω => ?_
    change (0 : ℝ) ≤ _
    have hcomb := replica_decoupling_comb_nonneg
      (fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) A
      (fun a b => ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P) κ c a₀
      (u₀ - 4 * κ * Real.cos t ^ 2) hA0 hAs hAd hcov hκ hu0
    simp only [integral_const_mul]
    have := mul_nonneg (mul_nonneg hsin hcos) hcomb
    linarith
  · exact (integrable_integral_pi_count_tilted_det (R := Option (Option (Fin 2))) (hg t)
      _).const_mul _
  · exact integrable_integral_pi_count_tilted_det (R := Fin 2) (hg t) _

end Compensated

section SK

open scoped Real Matrix

/-- **Corollary 1.4.7 along the SK smart path.**  For `0 ≤ t ≤ π / 2` and `lam ≥ 2 β²`, the
expected two-replica Gibbs average of `exp ((lam - 2 β² cos² t) N (R₁,₂ - q)²)` for the smart-path
energy at time `t` (SK field `cos t · X`, cavity field `sin t · Y`) is at most the same average
`𝔼⟨exp (lam N (R₁,₂ - q)²)⟩` in the decoupled model (`t = π / 2`).  In Talagrand's parametrization
this is the monotonicity of `t ↦ ν_t (exp ((λ - 2 t β²) N (R₁,₂ - q)²))`. -/
theorem sk_compensated_path_le_decoupled {N : ℕ} (hN : 0 < N) (β h q lam : ℝ) (hq : 0 ≤ q)
    (hlam : 2 * β ^ 2 ≤ lam) {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * (lam - 2 * β ^ 2 * Real.cos t ^ 2)) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
      ∫ z : Fin N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * lam) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  obtain ⟨F, G, hF, hG, hFm, hGm, hXG, hX0, hY0, h0, hcov⟩ :=
    exists_sk_smart_path_fields hN β q hq (P := Pg.prod Pz) (by rw [hPg, hPz])
  obtain ⟨r, hr⟩ : ∃ r : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ, ∀ σ τ,
      r σ τ = (N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  have hmono := monotoneOn_compensated_functional (P := Pg.prod Pz)
    (X := fun σ ω => F ω.1 σ) (Y := fun σ ω => G ω.2 σ)
    (fun σ => (measurable_pi_apply σ |>.comp hFm).comp measurable_fst)
    (fun σ => (measurable_pi_apply σ |>.comp hGm).comp measurable_snd) hXG hX0 hY0 h0
    (fun a => h * ∑ i, ((a i : ℤ) : ℝ)) (fun σ τ => (r σ τ - q) ^ 2) ((N : ℝ) * β ^ 2 / 2)
    (q ^ 2 + (N : ℝ)⁻¹) ((1 - q) ^ 2) ((N : ℝ) * lam)
    (fun σ τ => by simpa only [hr] using hcov σ τ) (fun σ τ => sq_nonneg _)
    (fun σ τ => by simp only [hr, dotProduct_comm (fun i => ((σ i : ℤ) : ℝ))])
    (fun σ => by
      have := card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
        (fun i => units_cast_sq (σ i))
      rw [Fintype.card_fin] at this
      simp only [hr, this])
    (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_left hlam (Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hle := hmono ht (Set.right_mem_Icc.2 (by positivity)) ht.2
  have hL : (N : ℝ) * lam - 4 * ((N : ℝ) * β ^ 2 / 2) * Real.cos t ^ 2 =
      N * (lam - 2 * β ^ 2 * Real.cos t ^ 2) := by ring
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, one_mul, zero_mul, zero_add,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, hL, hF, hG,
    hr] at hle
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin N → ℝ) → ℝ, ∀ z, Ψ z =
      ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * lam) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have e2 := integral_fun_snd (μ := Pg) (ν := Pz) Ψ
  simp only [hΨ, probReal_univ, one_smul] at e2
  rw [e2] at hle
  subst hPg hPz
  exact hle

/-- **Corollary 1.4.7 at the endpoints of the SK smart path.**  For `s ≥ 0`, the Gibbs average
`𝔼⟨exp (s N (R₁,₂ - q)²)⟩` of the SK model with `N` spins is at most the same average
`𝔼⟨exp ((s + 2 β²) N (R₁,₂ - q)²)⟩` in the decoupled (Guerra cavity) model with site disorder
`β √q zᵢ`, for every `q ≥ 0`.  Here `⟨·⟩` is the average over two independent replicas. -/
theorem sk_compensated_le_decoupled {N : ℕ} (hN : 0 < N) (β h q s : ℝ) (hq : 0 ≤ q)
    (hs : 0 ≤ s) :
    ∫ g : FinPairs N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * s) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ∫ z : Fin N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * (s + 2 * β ^ 2)) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have hle := sk_compensated_path_le_decoupled hN β h q (s + 2 * β ^ 2) hq (by linarith)
    (Set.left_mem_Icc.2 (by positivity))
  simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero, one_pow, mul_one,
    add_sub_cancel_right] at hle
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (FinPairs N → ℝ) → ℝ, ∀ g, Ψ g =
      ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * s) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ)) := ⟨_, fun _ => rfl⟩
  have e1 := integral_fun_fst (μ := Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1) Ψ
  simp only [hΨ, probReal_univ, one_smul] at e1
  rw [e1] at hle
  exact hle

end SK

end SpinGlasses
