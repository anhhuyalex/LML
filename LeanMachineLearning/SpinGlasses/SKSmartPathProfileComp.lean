/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSmartPathProfile
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationNonlinear

/-!
# A smooth function of the free energy along the SK smart path (Talagrand, Eq. (1.125))

For a `C²` function `W` of exponential growth (e.g. a polynomial), the expectation
`ψ(t) = 𝔼 W (A(t))` of `W` at the normalized free energy `A(t) = N⁻¹ log Z_t` of the smart path
`H_t = cos t · SK + sin t · cavity + h ∑ σᵢ` is differentiable with
$$ψ'(t) = \tfrac{β²}{2} \sin t \cos t\; 𝔼\Big[W'(A)\big(⟨(R_{1,2}-q)²⟩ - (1-q)²\big) -
  N^{-1} W''(A)\big(⟨(R_{1,2}-q)²⟩ - q² - N^{-1}\big)\Big].$$
For `W = id` this is `exists_sk_smart_path_profile`; the second term is the new one needed for the
central limit theorem for the free energy (Talagrand, Theorem 1.4.11).

## Main declarations

* `SpinGlasses.sum_hessian_comp_eq`: the finite algebra turning the double sum over the covariance
  difference into the overlap expression.
* `SpinGlasses.exists_sk_smart_path_profile_comp`: the profile.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eq. (1.125).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The double sum over the Hessian of `F_W` against a completed-square covariance.**  If the
covariance difference is `D l k = -c (S l k - q² - n)` with `S l l = (1 - q)²`, and `w` are weights
summing to one, then
`∑_{l,k} D l k (n² W'' w_l w_k + n W' w_l (1[l = k] - w_k)) =
  c n W' (Q - (1 - q)²) - c n² W'' (Q - q² - n)` with `Q = ∑_{l,k} w_l w_k S l k`. -/
theorem sum_hessian_comp_eq {K κ : Type*} [CommRing K] [Fintype κ] [DecidableEq κ] (w : κ → K)
    (hw : ∑ l, w l = 1) (S D : κ → κ → K) (c q n a₁ a₂ : K)
    (hD : ∀ l k, D l k = -c * (S l k - q ^ 2 - n)) (hS : ∀ l, S l l = (1 - q) ^ 2) :
    ∑ l, ∑ k, D l k * (n ^ 2 * a₂ * w l * w k + n * a₁ * (w l * ((if l = k then 1 else 0) - w k)))
      = c * n * a₁ * ((∑ l, ∑ k, w l * w k * S l k) - (1 - q) ^ 2) -
        c * n ^ 2 * a₂ * ((∑ l, ∑ k, w l * w k * S l k) - q ^ 2 - n) := by
  have hww : ∑ l, ∑ k, w l * w k = 1 := by
    rw [← Finset.sum_mul_sum, hw, one_mul]
  have e1 : ∑ l, ∑ k, w l * w k * (S l k - q ^ 2 - n) =
      (∑ l, ∑ k, w l * w k * S l k) - q ^ 2 - n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, hww, one_mul]
  have e2 : ∑ l, ∑ k, w l * (if l = k then (1 : K) else 0) * (S l k - q ^ 2 - n) =
      (1 - q) ^ 2 - q ^ 2 - n := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, hS, ← Finset.sum_mul, hw, one_mul]
  have key : ∀ l k, D l k * (n ^ 2 * a₂ * w l * w k +
      n * a₁ * (w l * ((if l = k then 1 else 0) - w k))) =
      -c * n ^ 2 * a₂ * (w l * w k * (S l k - q ^ 2 - n)) +
      (-c * n * a₁) * (w l * (if l = k then (1 : K) else 0) * (S l k - q ^ 2 - n) -
        w l * w k * (S l k - q ^ 2 - n)) := fun l k => by
    rw [hD]; ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, e1, e2]
  ring

/-- **The pointwise form of Eq. (1.125) for the SK covariance.**  For a field `y + hh` on the
hypercube and covariance differences `D σ τ = -(Nβ²/2)((R(σ,τ) - q)² - (q² + N⁻¹))`,
`∑_{σ,τ} D σ τ H_{στ} = (β²/2) (W'(A) (Q - (1-q)²) - N⁻¹ W''(A) (Q - q² - N⁻¹))` with
`A = N⁻¹ log ∑ exp (y + hh)` and `Q` the Gibbs average of `(R_{1,2} - q)²`. -/
theorem sum_freeEnergyCompHessian_eq {N : ℕ} (hN : 0 < N) (β q : ℝ) (W : ℝ → ℝ)
    (y hh : (Fin N → ℤˣ) → ℝ) (D : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ)
    (hD : ∀ σ τ, D σ τ = -((N : ℝ) * β ^ 2 / 2) * ((((N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) - q) ^ 2 -
        (q ^ 2 + (N : ℝ)⁻¹))) :
    ∑ σ, ∑ τ, D σ τ * freeEnergyCompHessian W (N : ℝ)⁻¹ hh y σ τ =
      β ^ 2 / 2 * (deriv W ((N : ℝ)⁻¹ * Real.log (∑ a, Real.exp (y a + hh a))) *
          ((∫ σ : Fin 2 → (Fin N → ℤˣ),
            (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a => y a + hh a)) -
            (1 - q) ^ 2) -
        (N : ℝ)⁻¹ * deriv (deriv W) ((N : ℝ)⁻¹ * Real.log (∑ a, Real.exp (y a + hh a))) *
          ((∫ σ : Fin 2 → (Fin N → ℤˣ),
            (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a => y a + hh a)) -
            q ^ 2 - (N : ℝ)⁻¹)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hZ : 0 < ∑ a, Real.exp (y a + hh a) := sum_exp_add_pos hh y
  have hw : ∑ a, Real.exp (y a + hh a) / ∑ b, Real.exp (y b + hh b) = 1 := by
    rw [← Finset.sum_div, div_self hZ.ne']
  have hdiag : ∀ σ : Fin N → ℤˣ, ((((N : ℝ)⁻¹ *
      ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ i : ℤ) : ℝ))) - q) ^ 2) = (1 - q) ^ 2 :=
    fun σ => by
      have h1 := card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
        (fun i => units_cast_sq (σ i))
      simp only [Fintype.card_fin] at h1
      rw [h1]
  have hQ := integral_pi_fin_two_count_tilted (fun a => y a + hh a) (fun x y => (((N : ℝ)⁻¹ *
    ((fun i => ((x i : ℤ) : ℝ)) ⬝ᵥ fun i => ((y i : ℤ) : ℝ))) - q) ^ 2)
  have key := sum_hessian_comp_eq (fun a => Real.exp (y a + hh a) / ∑ b, Real.exp (y b + hh b))
    hw (fun x y => (((N : ℝ)⁻¹ * ((fun i => ((x i : ℤ) : ℝ)) ⬝ᵥ fun i => ((y i : ℤ) : ℝ))) -
      q) ^ 2) D ((N : ℝ) * β ^ 2 / 2) q (N : ℝ)⁻¹
    (deriv W ((N : ℝ)⁻¹ * Real.log (∑ a, Real.exp (y a + hh a))))
    (deriv (deriv W) ((N : ℝ)⁻¹ * Real.log (∑ a, Real.exp (y a + hh a))))
    (fun σ τ => by rw [hD]; ring) hdiag
  unfold freeEnergyCompHessian
  rw [key]
  simp only [hQ, mul_assoc]
  field_simp

/-- **Eq. (1.125) for the SK smart path.**  For `N > 0`, `q ≥ 0` and `W` of class `C²` with `W`,
`W'`, `W''` of exponential growth there are the SK pair field `F` and cavity field `G` and a
function `ψ`, `ψ s = 𝔼 W (N⁻¹ log Z_s)` for the smart-path partition function `Z_s`, such that
`ψ 0` is the expectation of `W (A_N)` for the SK model, `ψ (π/2)` that of `W` at the decoupled free
energy `log 2 + N⁻¹ ∑ᵢ log cosh (β √q zᵢ + h)`, and
`ψ' t = (β²/2) sin t cos t 𝔼 [W'(A_t) (Q_t - (1-q)²) - N⁻¹ W''(A_t) (Q_t - q² - N⁻¹)]` where
`Q_t = ⟨(R_{1,2} - q)²⟩_t`.  For `W = id` the second term vanishes
(`exists_sk_smart_path_profile`). -/
theorem exists_sk_smart_path_profile_comp {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q)
    {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) {C₀ c₀ C₁ c₁ C₂ c₂ : ℝ}
    (hW0 : ∀ x, |W x| ≤ C₀ * Real.exp (c₀ * |x|))
    (hW1 : ∀ x, |deriv W x| ≤ C₁ * Real.exp (c₁ * |x|))
    (hW2 : ∀ x, |deriv (deriv W) x| ≤ C₂ * Real.exp (c₂ * |x|)) :
    ∃ (F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ) (G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
      (ψ : ℝ → ℝ),
      (∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ∧
      (∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ)) ∧
      (∀ s, ψ s = ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), W ((N : ℝ)⁻¹ *
        Real.log (∑ σ : Fin N → ℤˣ, Real.exp (Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ +
          h * ∑ i, ((σ i : ℤ) : ℝ))))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1))) ∧
      ψ 0 = ∫ g : FinPairs N → ℝ, W ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ))))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      ψ (Real.pi / 2) = ∫ z : Fin N → ℝ, W (Real.log 2 + (N : ℝ)⁻¹ * ∑ i,
        Real.log (Real.cosh (β * Real.sqrt q * z i + h)))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ∧
      ∀ t, HasDerivAt ψ (β ^ 2 / 2 * Real.sin t * Real.cos t *
        ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ),
          (deriv W ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (Real.cos t * F ω.1 σ +
              Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ)))) *
            ((∫ σ : Fin 2 → (Fin N → ℤˣ),
              (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
                Real.cos t * F ω.1 a + Real.sin t * G ω.2 a + h * ∑ i, ((a i : ℤ) : ℝ))) -
              (1 - q) ^ 2) -
          (N : ℝ)⁻¹ * deriv (deriv W) ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
              Real.exp (Real.cos t * F ω.1 σ + Real.sin t * G ω.2 σ +
                h * ∑ i, ((σ i : ℤ) : ℝ)))) *
            ((∫ σ : Fin 2 → (Fin N → ℤˣ),
              (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
                Real.cos t * F ω.1 a + Real.sin t * G ω.2 a + h * ∑ i, ((a i : ℤ) : ℝ))) -
              q ^ 2 - (N : ℝ)⁻¹))
          ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1))) t := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  obtain ⟨F, G, hF, hG, hFm, hGm, hXG', hX0, hY0, h0, hCov'⟩ :=
    exists_sk_smart_path_fields hN β q hq (P := Pg.prod Pz) (by rw [hPg, hPz])
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ∀ s, ψ s = ∫ ω, W ((N : ℝ)⁻¹ *
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ +
        h * ∑ i, ((σ i : ℤ) : ℝ)))) ∂(Pg.prod Pz) := ⟨_, fun _ => rfl⟩
  refine ⟨F, G, ψ, hF, hG, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hψ s, hPg, hPz]
  · rw [hψ]
    simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    rw [integral_fun_fst (fun g : FinPairs N → ℝ => W ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ))))), probReal_univ, one_smul, hPg]
  · rw [hψ]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]
    rw [integral_fun_snd (fun z : Fin N → ℝ => W ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (G z σ + h * ∑ i, ((σ i : ℤ) : ℝ))))), probReal_univ, one_smul, hPz]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hG, decoupled_field_eq]
    rw [log_decoupled_partition_function_eq (fun i => β * Real.sqrt q * z i + h)]
    simp only [Fintype.card_fin]
    congr 1
    field_simp
  · intro t
    have hψfun : ψ = fun s => ∫ ω, W ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ +
          h * ∑ i, ((σ i : ℤ) : ℝ)))) ∂(Pg.prod Pz) := funext hψ
    have hder := hasDerivAt_integral_comp_log_sum_exp_trig_integral
      (X := fun σ ω => F ω.1 σ) (Y := fun σ ω => G ω.2 σ) (P := Pg.prod Pz) hXG' hX0 hY0 h0
      hW hW0 hW1 hW2 (N : ℝ)⁻¹ (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)) t
    rw [hψfun]
    subst hPg hPz
    refine hder.congr_deriv ?_
    have hpt : ∀ ω : (FinPairs N → ℝ) × (Fin N → ℝ),
        ∑ σ : Fin N → ℤˣ, ∑ τ : Fin N → ℤˣ,
          ((∫ ω', G ω'.2 σ * G ω'.2 τ ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 1))) -
            ∫ ω', F ω'.1 σ * F ω'.1 τ ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin N => gaussianReal 0 1))) *
          freeEnergyCompHessian W (N : ℝ)⁻¹ (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ))
            (fun m => Real.cos t * F ω.1 m + Real.sin t * G ω.2 m) σ τ =
        _ := fun ω => sum_freeEnergyCompHessian_eq hN β q W
          (fun m => Real.cos t * F ω.1 m + Real.sin t * G ω.2 m)
          (fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)) _ hCov'
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
    ring

/-- `|x - a|^m ≤ m! exp |a| exp |x|`: powers have exponential growth. -/
theorem abs_sub_pow_le (a x : ℝ) (m : ℕ) :
    |x - a| ^ m ≤ (Nat.factorial m : ℝ) * Real.exp |a| * Real.exp (1 * |x|) := by
  calc |x - a| ^ m ≤ (Nat.factorial m : ℝ) * Real.exp |x - a| :=
        Real.pow_le_factorial_mul_exp (abs_nonneg _) m
    _ ≤ (Nat.factorial m : ℝ) * (Real.exp |a| * Real.exp |x|) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        calc |x - a| = |x + -a| := by rw [sub_eq_add_neg]
          _ ≤ |x| + |-a| := abs_add_le _ _
          _ = |a| + |x| := by rw [abs_neg]; ring
    _ = _ := by rw [one_mul]; ring

/-- The first derivative of `x ↦ (x - a)^k`. -/
theorem deriv_sub_pow (a : ℝ) (k : ℕ) :
    deriv (fun x : ℝ => (x - a) ^ k) = fun x => (k : ℝ) * (x - a) ^ (k - 1) := by
  funext x
  simp

/-- The second derivative of `x ↦ (x - a)^k`. -/
theorem deriv_deriv_sub_pow (a : ℝ) (k : ℕ) :
    deriv (deriv fun x : ℝ => (x - a) ^ k) =
      fun x => (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (x - a) ^ (k - 1 - 1) := by
  rw [deriv_sub_pow]
  funext x
  simp [mul_assoc]

/-- `x ↦ (x - a)^k` is smooth with the exponential-growth bounds required by
`exists_sk_smart_path_profile_comp`. -/
theorem sub_pow_growth (a : ℝ) (k : ℕ) :
    ContDiff ℝ 2 (fun x : ℝ => (x - a) ^ k) ∧
    (∀ x, |(x - a) ^ k| ≤ ((Nat.factorial k : ℝ) * Real.exp |a|) * Real.exp (1 * |x|)) ∧
    (∀ x, |deriv (fun x : ℝ => (x - a) ^ k) x| ≤
      ((k : ℝ) * (Nat.factorial (k - 1) : ℝ) * Real.exp |a|) * Real.exp (1 * |x|)) ∧
    (∀ x, |deriv (deriv fun x : ℝ => (x - a) ^ k) x| ≤
      ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * (Nat.factorial (k - 1 - 1) : ℝ) * Real.exp |a|) *
        Real.exp (1 * |x|)) := by
  refine ⟨by fun_prop, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [abs_pow, mul_assoc]
    simpa [mul_assoc] using abs_sub_pow_le a x k
  · rw [deriv_sub_pow, abs_mul, abs_pow, Nat.abs_cast]
    have := abs_sub_pow_le a x (k - 1)
    calc (k : ℝ) * |x - a| ^ (k - 1) ≤ (k : ℝ) * ((Nat.factorial (k - 1) : ℝ) * Real.exp |a| *
          Real.exp (1 * |x|)) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := by ring
  · rw [deriv_deriv_sub_pow, abs_mul, abs_mul, abs_pow, Nat.abs_cast, Nat.abs_cast]
    have := abs_sub_pow_le a x (k - 1 - 1)
    calc (k : ℝ) * ((k - 1 : ℕ) : ℝ) * |x - a| ^ (k - 1 - 1) ≤ (k : ℝ) * ((k - 1 : ℕ) : ℝ) *
          ((Nat.factorial (k - 1 - 1) : ℝ) * Real.exp |a| * Real.exp (1 * |x|)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- **Eq. (1.125) for `W(x) = (x - a)^k`** (Talagrand, proof of Theorem 1.4.11).  With
`A_t(ω) = N⁻¹ log Z_t(ω)` the free energy of the smart path and `Q_t(ω) = ⟨(R_{1,2} - q)²⟩_t` the
Gibbs average of the squared overlap, `ψ(t) = 𝔼 (A_t - a)^k` has the derivative
`(β²/2) sin t cos t 𝔼 [k (A_t - a)^{k-1} (Q_t - (1-q)²) -
  N⁻¹ k (k-1) (A_t - a)^{k-2} (Q_t - q² - N⁻¹)]`,
with `ψ 0` the `k`-th moment of `A_N - a` in the SK model and `ψ (π/2)` that of the decoupled
system. -/
theorem exists_sk_smart_path_profile_pow {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) (a : ℝ)
    (k : ℕ) :
    ∃ (F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ) (G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ)
      (ψ : ℝ → ℝ) (A Q : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ),
      (∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ∧
      (∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ)) ∧
      (∀ t ω, A t ω = (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (Real.cos t * F ω.1 σ + Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ)))) ∧
      (∀ t ω, Q t ω = ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b =>
          Real.cos t * F ω.1 b + Real.sin t * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ))) ∧
      (∀ s, ψ s = ∫ ω, (A s ω - a) ^ k
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1))) ∧
      ψ 0 = ∫ g : FinPairs N → ℝ, ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ))) - a) ^ k
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      ψ (Real.pi / 2) = ∫ z : Fin N → ℝ, (Real.log 2 + (N : ℝ)⁻¹ * ∑ i,
        Real.log (Real.cosh (β * Real.sqrt q * z i + h)) - a) ^ k
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ∧
      ∀ t, HasDerivAt ψ (β ^ 2 / 2 * Real.sin t * Real.cos t *
        ∫ ω, (((k : ℝ) * (A t ω - a) ^ (k - 1)) * (Q t ω - (1 - q) ^ 2) -
          (N : ℝ)⁻¹ * ((k : ℝ) * ((k - 1 : ℕ) : ℝ) * (A t ω - a) ^ (k - 1 - 1)) *
            (Q t ω - q ^ 2 - (N : ℝ)⁻¹))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1))) t := by
  obtain ⟨hW, hW0, hW1, hW2⟩ := sub_pow_growth a k
  obtain ⟨F, G, ψ, hF, hG, hψ, h0, hπ, hder⟩ := exists_sk_smart_path_profile_comp hN β h q hq
    hW hW0 hW1 hW2
  obtain ⟨A, hA⟩ : ∃ A : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ, ∀ t ω, A t ω =
      (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (Real.cos t * F ω.1 σ +
        Real.sin t * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ, ∀ t ω, Q t ω =
      ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b =>
          Real.cos t * F ω.1 b + Real.sin t * G ω.2 b + h * ∑ i, ((b i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨F, G, ψ, A, Q, hF, hG, hA, hQ, ?_, h0, hπ, fun t => ?_⟩
  · intro s
    rw [hψ s]
    simp only [hA]
  · have := hder t
    simp only [deriv_deriv_sub_pow] at this
    simp only [deriv_sub_pow] at this
    simp only [hA, hQ]
    exact this

end SpinGlasses
