/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# ODE tools: Grönwall, bootstrap, linear-ODE stability, and global flows

Network-independent analytic tools used by the gradient-flow development:

* `NTK.gronwall_exponential_decay_Icc`, `NTK.gronwall_exponential_decay`,
  `NTK.gronwallBound_le_mul_exp` : Grönwall-type decay.
* `NTK.integral_exp_neg_le` : `∫₀ᵀ exp(-c t) dt ≤ 1/c`.
* `NTK.le_of_forall_bootstrap` : the continuous-induction (bootstrap) principle on `[0, T]`.
* Global flow of a locally Lipschitz field with a priori bounds (Picard-Lindelöf on a truncation,
  the bootstrap, and gluing of finite windows).
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace NTK

variable {ι : Type*} {d m P : ℕ}

/-! ### Reusable Analytic Tool: Grönwall Differential Inequality -/

/-- Interval-Restricted Grönwall Decay Lemma:
If a scalar quantity `E(t)` is continuous on `[0, T]`, differentiable on `(0, T)`, and satisfies
`E'(t) ≤ -c * E(t)` there, then `E(t) ≤ E(0) * exp(-c * t)` for all `t ∈ [0, T]`.
Only interior differentiability is needed, so this applies to forward-time trajectories, and the
localized form enables continuous induction bootstrap arguments where the differential inequality
only holds while the state remains inside a bootstrap region. -/
lemma gronwall_exponential_decay_Icc {E E' : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hEc : ContinuousOn E (Set.Icc 0 T)) (hE : ∀ t ∈ Set.Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, E' t ≤ -c * E t) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    E t ≤ E 0 * Real.exp (-c * t) := by
  let g : ℝ → ℝ := fun s => E s * Real.exp (c * s)
  have hg_deriv : ∀ s ∈ Set.Ioo 0 T,
      HasDerivAt g ((E' s + c * E s) * Real.exp (c * s)) s := by
    intro s hs
    have h1 := hE s hs
    have h2 : HasDerivAt (fun u => Real.exp (c * u)) (Real.exp (c * s) * c) s := by
      have hc : HasDerivAt (fun u => c * u) (c * 1) s := (hasDerivAt_id s).const_mul c
      rw [mul_one] at hc
      exact hc.exp
    have hprod := h1.mul h2
    convert hprod using 1
    ring
  have hg_cont : ContinuousOn g (Set.Icc 0 T) := hEc.mul (by fun_prop)
  have hg_within : ∀ s ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt g ((E' s + c * E s) * Real.exp (c * s)) (interior (Set.Icc 0 T)) s :=
    fun s hs => (hg_deriv s (by rwa [interior_Icc] at hs)).hasDerivWithinAt
  have hg_nonpos : ∀ s ∈ interior (Set.Icc 0 T), (E' s + c * E s) * Real.exp (c * s) ≤ 0 := by
    intro s hs
    have hle : E' s + c * E s ≤ 0 := by
      linarith [hbound s (by rwa [interior_Icc] at hs)]
    have hexp : 0 ≤ Real.exp (c * s) := (Real.exp_pos _).le
    exact mul_nonpos_of_nonpos_of_nonneg hle hexp
  have h_anti : AntitoneOn g (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hg_cont hg_within hg_nonpos
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have h_le := h_anti h0_mem ht ht.1
  dsimp [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (-c * t)).le
  have h_exp_cancel : E t * Real.exp (c * t) * Real.exp (-c * t) = E t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, mul_one]
  rw [h_exp_cancel] at h_mul
  exact h_mul

/-- Grönwall Differential Inequality for Exponential Decay:
If a differentiable scalar quantity `E(t)` satisfies `E'(t) ≤ -c * E(t)` with `c > 0`,
then `E(t) ≤ E(0) * exp(-c * t)` for all `t ≥ 0`.
Specialization of `gronwall_exponential_decay_Icc` to the interval `[0, t]`. -/
lemma gronwall_exponential_decay {E E' : ℝ → ℝ} {c : ℝ}
    (hE : ∀ t, HasDerivAt E (E' t) t)
    (hbound : ∀ t, E' t ≤ -c * E t) (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ E 0 * Real.exp (-c * t) :=
  gronwall_exponential_decay_Icc ht (fun s _ => (hE s).continuousAt.continuousWithinAt)
    (fun s _ => hE s) (fun s _ => hbound s) t ⟨ht, le_rfl⟩

/-- Mathlib's Grönwall bound is at most `(δ + ε x) e^{K x}` (for `K, ε ≥ 0`), an expression that is
monotone in the time `x ≥ 0` and easy to use for a priori estimates. -/
lemma gronwallBound_le_mul_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hKpos
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    have hexp : 0 < Real.exp (K * x) := Real.exp_pos _
    have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
      have h2 := Real.one_sub_le_exp_neg (K * x)
      have h3 : Real.exp (K * x) * Real.exp (-(K * x)) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have h4 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ε * x * Real.exp (K * x) := by field_simp
    nlinarith

/-- Reusable bound: `∫₀ᵀ exp(-c t) dt ≤ 1/c` for `c > 0`, dropping the (nonnegative) `1 - exp(-cT)`
factor from the exact closed form `(1 - exp(-cT))/c`. -/
lemma integral_exp_neg_le (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, Real.exp (-c * t) ≤ c⁻¹ := by
  have hc' : -c ≠ 0 := by linarith
  rw [show (fun t : ℝ => Real.exp (-c * t)) = (fun t => Real.exp ((-c) * t)) from rfl]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hc']
  rw [integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  have h1 : Real.exp (-c * T) - 1 ≤ 0 := by
    have := Real.exp_le_one_iff.mpr (by nlinarith : -c * T ≤ 0)
    linarith
  rw [show (-c)⁻¹ * (Real.exp (-c * T) - 1) = c⁻¹ * (1 - Real.exp (-c * T)) by
    field_simp; ring]
  have h3 : 0 ≤ c⁻¹ := by positivity
  calc
    c⁻¹ * (1 - Real.exp (-c * T)) ≤ c⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ h3
      linarith [Real.exp_nonneg (-c * T)]
    _ = c⁻¹ := by ring
/-- **Continuous-induction (bootstrap) principle on `[0, T]`.** Let `d` be continuous and
`C < r` (only continuity on `[0, T]` is needed). Suppose that whenever `d ≤ r` holds on all of
`[0, S]` (for `S ∈ [0, T]`), the sharper
bound `d S ≤ C` holds. Then `d ≤ C` on all of `[0, T]`, i.e. `d` can never reach the threshold
`r`. Used for the displacement bootstraps: `d t = ‖θ(t) - θ₀‖` while the Jacobian estimates only
hold inside a ball. -/
theorem le_of_forall_bootstrap {d : ℝ → ℝ} {r C T : ℝ} (hd : ContinuousOn d (Set.Icc 0 T))
    (hCr : C < r)
    (hT : 0 ≤ T) (h0 : d 0 ≤ r)
    (hstep : ∀ S ∈ Set.Icc (0 : ℝ) T, (∀ t ∈ Set.Icc (0 : ℝ) S, d t ≤ r) → d S ≤ C) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, d t ≤ C := by
  have hzero : d 0 ≤ C := hstep 0 ⟨le_rfl, hT⟩ fun t ht => by
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    exact h0
  have hclosed : IsClosed ({t : ℝ | d t ≤ C} ∩ Set.Icc 0 T) := by
    have := hd.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := C))
    rwa [Set.inter_comm] at this
  have h := IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
    (s := {t : ℝ | d t ≤ C}) (a := 0) (b := T) hclosed hzero (fun t ht hsub => ?_)
  · exact fun t htT => h htT
  have hdt : d t < r := (hsub ⟨ht.1, le_rfl⟩).trans_lt hCr
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hd t ⟨ht.1, ht.2.le⟩) (r - d t)
    (by linarith)
  have hδ' : 0 < min δ (T - t) := lt_min hδ (by linarith [ht.2])
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show t < t + min δ (T - t) by linarith)) ?_
  intro u hu
  have huT : u ≤ T := by linarith [hu.2, min_le_right δ (T - t)]
  refine hstep u ⟨by linarith [ht.1, hu.1], huT⟩ fun t' ht' => ?_
  by_cases hle : t' ≤ t
  · exact (hsub ⟨ht'.1, hle⟩).trans hCr.le
  · have hlt : t < t' := not_le.1 hle
    have hdist : dist t' t < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [ht'.2, hu.2, min_le_left δ (T - t)]
    have hlt' := hball ⟨by linarith [ht'.1], by linarith [ht'.2, hu.2, huT]⟩ hdist
    rw [Real.dist_eq] at hlt'
    linarith [(abs_lt.1 hlt').2]

/-! ### Global Flow of a Locally Lipschitz Field with A Priori Bounds

Generic construction, independent of neural networks, of the two-sided flow of an autonomous field
`V` that is Lipschitz on balls and admits a priori bounds on solutions. It specializes Mathlib's
Picard-Lindelöf theorem to a truncation of `V`, closes the truncation with the continuous-induction
bootstrap `le_of_forall_bootstrap`, and glues the finite windows by uniqueness. -/

section GlobalFlowConstruction

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The radial cutoff `1` on the ball of radius `A` and `0` outside the ball of radius `2A`, as a
`1/A`-Lipschitz function. -/
lemma abs_cutoff_sub_le {A : ℝ} (hA : 0 < A) (x y : E) :
    |max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))| ≤ A⁻¹ * ‖x - y‖ := by
  have h1 : |(2 - ‖x‖ / A) - (2 - ‖y‖ / A)| ≤ A⁻¹ * ‖x - y‖ := by
    have : (2 - ‖x‖ / A) - (2 - ‖y‖ / A) = -(A⁻¹ * (‖x‖ - ‖y‖)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hA)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (inv_pos.2 hA).le
  have hclamp : LipschitzWith 1 (fun u : ℝ => max 0 (min 1 u)) :=
    (LipschitzWith.id.const_min 1).const_max 0
  have h := hclamp.dist_le_mul (2 - ‖x‖ / A) (2 - ‖y‖ / A)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h.trans h1

omit [NormedSpace ℝ E] in
lemma cutoff_eq_zero {A : ℝ} (hA : 0 < A) {x : E} (hx : 2 * A ≤ ‖x‖) :
    max 0 (min 1 (2 - ‖x‖ / A)) = 0 := by
  have h2 : 2 ≤ ‖x‖ / A := by rw [le_div_iff₀ hA]; linarith
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [NormedSpace ℝ E] in
lemma cutoff_eq_one {A : ℝ} (hA : 0 < A) {x : E} (hx : ‖x‖ ≤ A) :
    max 0 (min 1 (2 - ‖x‖ / A)) = 1 := by
  have h1 : ‖x‖ / A ≤ 1 := by rw [div_le_iff₀ hA]; linarith
  rw [min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

/-- **Cutoff of a locally Lipschitz vector field.** If `V` is bounded by `M` and `K`-Lipschitz on
the ball of radius `2A`, then `x ↦ χ(x) • V x`, with the radial cutoff `χ` (`1` on the ball of
radius `A`,
`0` outside the ball of radius `2A`), is `(K + M / A)`-Lipschitz on all of `E`. -/
lemma norm_cutoff_smul_sub_le {V : E → E} {A K M : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hbdd : ∀ x, ‖x‖ ≤ 2 * A → ‖V x‖ ≤ M)
    (hlip : ∀ x y, ‖x‖ ≤ 2 * A → ‖y‖ ≤ 2 * A → ‖V x - V y‖ ≤ K * ‖x - y‖) (x y : E) :
    ‖max 0 (min 1 (2 - ‖x‖ / A)) • V x - max 0 (min 1 (2 - ‖y‖ / A)) • V y‖ ≤
      (K + A⁻¹ * M) * ‖x - y‖ := by
  have hχ0 : ∀ z : E, 0 ≤ max 0 (min 1 (2 - ‖z‖ / A)) := fun z => le_max_left _ _
  have hχ1 : ∀ z : E, max 0 (min 1 (2 - ‖z‖ / A)) ≤ 1 :=
    fun z => max_le zero_le_one (min_le_left _ _)
  have hχlip := abs_cutoff_sub_le hA x y
  have hAM : 0 ≤ A⁻¹ * M := by positivity
  by_cases hx : ‖x‖ ≤ 2 * A <;> by_cases hy : ‖y‖ ≤ 2 * A
  · -- both inside the ball of radius `2A`
    have h1 : max 0 (min 1 (2 - ‖x‖ / A)) • V x - max 0 (min 1 (2 - ‖y‖ / A)) • V y =
        (max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))) • V x +
          max 0 (min 1 (2 - ‖y‖ / A)) • (V x - V y) := by
      rw [sub_smul, smul_sub]; abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hχ0 y)]
    have h2 : |max 0 (min 1 (2 - ‖x‖ / A)) - max 0 (min 1 (2 - ‖y‖ / A))| * ‖V x‖ ≤
        A⁻¹ * ‖x - y‖ * M := mul_le_mul hχlip (hbdd x hx) (norm_nonneg _) (by positivity)
    have h3 : max 0 (min 1 (2 - ‖y‖ / A)) * ‖V x - V y‖ ≤ K * ‖x - y‖ :=
      (mul_le_mul_of_nonneg_right (hχ1 y) (norm_nonneg _)).trans
        (by rw [one_mul]; exact hlip x y hx hy)
    nlinarith [h2, h3]
  · -- `y` outside: its cutoff vanishes
    have hy0 := cutoff_eq_zero hA (not_le.1 hy).le
    rw [hy0, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
    have hd : max 0 (min 1 (2 - ‖x‖ / A)) ≤ A⁻¹ * ‖x - y‖ := by
      have := hχlip
      rw [hy0, sub_zero, abs_of_nonneg (hχ0 x)] at this
      exact this
    calc max 0 (min 1 (2 - ‖x‖ / A)) * ‖V x‖ ≤ (A⁻¹ * ‖x - y‖) * M :=
          mul_le_mul hd (hbdd x hx) (norm_nonneg _) (by positivity)
      _ ≤ (K + A⁻¹ * M) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  · have hx0 := cutoff_eq_zero hA (not_le.1 hx).le
    rw [hx0, zero_smul, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hχ0 y)]
    have hd : max 0 (min 1 (2 - ‖y‖ / A)) ≤ A⁻¹ * ‖x - y‖ := by
      have := hχlip
      rw [hx0, zero_sub, abs_neg, abs_of_nonneg (hχ0 y)] at this
      exact this
    calc max 0 (min 1 (2 - ‖y‖ / A)) * ‖V y‖ ≤ (A⁻¹ * ‖x - y‖) * M :=
          mul_le_mul hd (hbdd y hy) (norm_nonneg _) (by positivity)
      _ ≤ (K + A⁻¹ * M) * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  · rw [cutoff_eq_zero hA (not_le.1 hx).le, cutoff_eq_zero hA (not_le.1 hy).le]
    simp only [zero_smul, sub_self, norm_zero]
    positivity

variable [CompleteSpace E]

/-- **Local-to-uniform flow of a globally Lipschitz bounded field.** A bounded, globally Lipschitz
autonomous field has a flow on `[-T, T]`, jointly continuous in the initial point (in any ball) and
time. This specializes Mathlib's Picard-Lindelöf theorem with `x₀ = 0` and `a = r + M T`, so the
ball hypothesis is automatic. -/
lemma exists_flow_of_lipschitzWith_of_bound (Vg : E → E) {K M : NNReal} (hVlip : LipschitzWith K Vg)
    (hVb : ∀ x, ‖Vg x‖ ≤ M) (T r : NNReal) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall (0 : E) r, α (x, 0) = x ∧
        ∀ t ∈ Icc (-(T : ℝ)) T, HasDerivWithinAt (fun s => α (x, s)) (Vg (α (x, t)))
          (Icc (-(T : ℝ)) T) t) ∧
      ContinuousOn α (closedBall (0 : E) r ×ˢ Icc (-(T : ℝ)) T) := by
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨by simp, T.2⟩
  have hPL : IsPicardLindelof (fun _ : ℝ => Vg) (⟨0, h0⟩ : Icc (-(T : ℝ)) T) (0 : E)
      (r + M * T) r M K :=
    { lipschitzOnWith := fun _ _ => hVlip.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ _ _ => hVb _
      mul_max_le := by
        simp only [NNReal.coe_add, NNReal.coe_mul, add_sub_cancel_left, zero_sub, sub_zero, neg_neg,
          max_self]
        exact le_rfl }
  exact hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn


/-- **Finite-window flow with an a priori bound.** Suppose `V` is Lipschitz on balls and every
solution on `[0, S]` (`S ≤ T`) that starts in the ball of radius `r` stays in a ball of some radius
`ρ`. Then `V` has a forward flow on `[0, T]`, jointly continuous in the initial point (in the
ball of radius `r`) and time. Proof: truncate `V` outside a large ball, apply
`exists_flow_of_lipschitzWith_of_bound`, and use the continuous-induction bootstrap
`le_of_forall_bootstrap` to show the truncated flow never leaves the region where it agrees with
`V`. Only forward time is used, so nothing is required of the solution for negative times. -/
theorem exists_flow_window (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    (T r : NNReal)
    (hprior : ∃ ρ : ℝ, ∀ (θ : ℝ → E) (S : ℝ), 0 ≤ S → S ≤ T → ‖θ 0‖ ≤ r →
      (∀ t ∈ Icc 0 S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t) → ‖θ S‖ ≤ ρ) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall (0 : E) r, α (x, 0) = x ∧
        ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => α (x, s)) (V (α (x, t)))
          (Icc 0 (T : ℝ)) t) ∧
      ContinuousOn α (closedBall (0 : E) r ×ˢ Icc 0 (T : ℝ)) := by
  obtain ⟨ρ, hρ⟩ := hprior
  set A : ℝ := max ρ r + 1 with hA_def
  have hA : 0 < A := by
    have h0 : (0 : ℝ) ≤ r := r.2
    have := le_max_right ρ (r : ℝ)
    linarith
  obtain ⟨K, hK, hKlip⟩ := hV_lip (2 * A)
  set M : ℝ := ‖V 0‖ + K * (2 * A) with hM_def
  have hM : 0 ≤ M := by positivity
  have hVbdd : ∀ x : E, ‖x‖ ≤ 2 * A → ‖V x‖ ≤ M := fun x hx => by
    have h := hKlip x 0 hx
      (by simp only [norm_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity)
    rw [sub_zero] at h
    have h2 := norm_sub_norm_le (V x) (V 0)
    rw [hM_def]; nlinarith [norm_nonneg x]
  set Vg : E → E := fun x => max 0 (min 1 (2 - ‖x‖ / A)) • V x with hVg
  have hχ0 : ∀ z : E, 0 ≤ max 0 (min 1 (2 - ‖z‖ / A)) := fun z => le_max_left _ _
  have hχ1 : ∀ z : E, max 0 (min 1 (2 - ‖z‖ / A)) ≤ 1 :=
    fun z => max_le zero_le_one (min_le_left _ _)
  have hVg_lip : LipschitzWith ⟨K + A⁻¹ * M, by positivity⟩ Vg :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact norm_cutoff_smul_sub_le hA hK hM hVbdd hKlip x y
  have hVg_bdd : ∀ x, ‖Vg x‖ ≤ (⟨M, hM⟩ : NNReal) := fun x => by
    by_cases hx : ‖x‖ ≤ 2 * A
    · rw [hVg]
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
      calc _ ≤ 1 * ‖V x‖ := mul_le_mul_of_nonneg_right (hχ1 x) (norm_nonneg _)
        _ ≤ M := by rw [one_mul]; exact hVbdd x hx
    · rw [hVg]
      dsimp only
      rw [cutoff_eq_zero hA (not_le.1 hx).le, zero_smul, norm_zero]
      exact hM
  obtain ⟨α, hα, hαc⟩ := exists_flow_of_lipschitzWith_of_bound Vg hVg_lip hVg_bdd T r
  have hsub : Icc (0 : ℝ) T ⊆ Icc (-(T : ℝ)) T := Icc_subset_Icc (by linarith [T.coe_nonneg]) le_rfl
  refine ⟨α, fun x hx => ?_, hαc.mono (prod_mono subset_rfl hsub)⟩
  obtain ⟨h0, hsol⟩ := hα x hx
  refine ⟨h0, ?_⟩
  have hsolF : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => α (x, s)) (Vg (α (x, t))) (Icc 0 (T : ℝ)) t :=
    fun t ht => (hsol t (hsub ht)).mono hsub
  set θ : ℝ → E := fun s => α (x, s) with hθ
  have hxr : ‖x‖ ≤ r := by simpa using hx
  have hθcont : ContinuousOn θ (Icc (0 : ℝ) T) := fun t ht => (hsolF t ht).continuousWithinAt
  have hθ0 : θ 0 = x := h0
  have hρ_lt : ρ < A := by rw [hA_def]; linarith [le_max_left ρ (r : ℝ)]
  have hr_le : (r : ℝ) ≤ A - 1 := by
    have := le_max_right ρ (r : ℝ); rw [hA_def]; linarith
  -- forward bootstrap: `‖θ t‖ ≤ A - 1` for `t ∈ [0, T]`
  have hfwd : ∀ t ∈ Icc (0 : ℝ) T, ‖θ t‖ ≤ A - 1 := by
    refine le_of_forall_bootstrap (d := fun t => ‖θ t‖) (r := A) (C := A - 1)
      hθcont.norm (by linarith) T.coe_nonneg (by rw [hθ0]; linarith) ?_
    intro S hS hb
    have hsolS : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t := by
      intro t ht
      have h1 := (hsolF t ⟨ht.1, ht.2.trans hS.2⟩).mono
        (show Icc (0 : ℝ) S ⊆ Icc 0 (T : ℝ) from Icc_subset_Icc le_rfl hS.2)
      convert h1 using 2
      simp only [hVg]
      rw [cutoff_eq_one hA (hb t ht), one_smul]
    have := hρ θ S hS.1 hS.2 (by rw [hθ0]; exact hxr) hsolS
    rw [hA_def]
    linarith [le_max_left ρ (r : ℝ)]
  intro t ht
  have h1 := hsolF t ht
  convert h1 using 2
  simp only [hVg]
  rw [cutoff_eq_one hA (by linarith [hfwd t ht]), one_smul]

omit [CompleteSpace E] in
/-- **Uniqueness on a forward window.** Two solutions of `x' = V x` on `[0, T]` (`T > 0`),
continuous on `[0, T]` and differentiable on `(0, T)`, with the same value at `0` coincide there,
when `V` is Lipschitz on balls. Continuity makes both solutions bounded, so Mathlib's
`ODE_solution_unique_of_mem_Icc` applies on a large ball. This is a thin adapter (it supplies the
ball and constant) used only by `exists_forward_flow` and `forwardFlow_unique`, hence private. -/
private theorem forwardFlow_unique_window (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {f g : ℝ → E}
    (hfc : ContinuousOn f (Icc 0 T)) (hf : ∀ t ∈ Ioo 0 T, HasDerivAt f (V (f t)) t)
    (hgc : ContinuousOn g (Icc 0 T)) (hg : ∀ t ∈ Ioo 0 T, HasDerivAt g (V (g t)) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  -- a field that is Lipschitz on balls is continuous
  have hVc : Continuous V := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    obtain ⟨K, hK, hKlip⟩ := hV_lip (‖x‖ + 1)
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min 1 (ε / (K + 1)), by positivity, fun y hy => ?_⟩
    have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y x < ε / (K + 1) := lt_of_lt_of_le hy (min_le_right _ _)
    rw [dist_eq_norm] at hy1 hy2 ⊢
    have hyn : ‖y‖ ≤ ‖x‖ + 1 := by linarith [norm_sub_norm_le y x]
    have := hKlip y x hyn (by linarith [norm_nonneg x])
    rw [lt_div_iff₀ (by positivity)] at hy2
    nlinarith [norm_nonneg (y - x)]
  -- solutions have a right derivative at the initial time as well (the derivative has a limit)
  have hright : ∀ {h : ℝ → E}, ContinuousOn h (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, HasDerivAt h (V (h t)) t) → ∀ t ∈ Ico 0 T,
        HasDerivWithinAt h (V (h t)) (Ici t) t := by
    intro h hc hd t ht
    rcases ht.1.eq_or_lt with rfl | hpos
    · have hcw : ContinuousWithinAt h (Ioi 0) 0 :=
        (hc 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self)
      have hlim : Filter.Tendsto (fun x => V (h x)) (nhdsWithin 0 (Ioi 0)) (nhds (V (h 0))) :=
        (hVc.continuousAt.tendsto).comp hcw.tendsto
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 T)
        (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
        ((hc 0 ⟨le_rfl, hT.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hT) ?_
      exact hlim.congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT hT)
        fun x hx => (hd x hx).deriv.symm)
    · exact (hd t ⟨hpos, ht.2⟩).hasDerivWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Cg, hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK, hKlip⟩ := hV_lip (max Cf Cg)
  have hv : ∀ t ∈ Ico 0 T, LipschitzOnWith K.toNNReal ((fun _ : ℝ => V) t)
      ((fun _ : ℝ => closedBall (0 : E) (max Cf Cg)) t) := fun _ _ =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simpa [dist_eq_norm, Real.coe_toNNReal K hK] using
        hKlip x y (by simpa using hx) (by simpa using hy)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
    (s := fun _ => closedBall (0 : E) (max Cf Cg)) hv hfc (hright hfc hf)
    (fun t ht => by simpa using (hCf t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)) hgc
    (hright hgc hg)
    (fun t ht => by simpa using (hCg t (Ico_subset_Icc_self ht)).trans (le_max_right _ _)) h0

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A locally Lipschitz map on a proper normed space is Lipschitz on every closed ball centered at
`0`, in the elementary form used by `exists_forward_flow` and `forwardFlow_unique`. -/
lemma lipschitz_on_ball_of_locallyLipschitz [ProperSpace E] {V : E → E} (hV : LocallyLipschitz V)
    (A : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK⟩ := (hV.locallyLipschitzOn (s := closedBall (0 : E) A)
    ).exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 A)
  refine ⟨K, K.2, fun x z hx hz => ?_⟩
  have := hK.dist_le_mul x (by simpa using hx) z (by simpa using hz)
  simpa [dist_eq_norm] using this

omit [CompleteSpace E] in
/-- **Forward uniqueness of solutions.** If `V` is Lipschitz on balls, two solutions of `x' = V x`
that are continuous on `[0, ∞)` and differentiable for `t > 0`, with the same value at `0`, agree on
`[0, ∞)`. -/
theorem forwardFlow_unique (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    {f g : ℝ → E} (hfc : ContinuousOn f (Ici 0)) (hf : ∀ t, 0 < t → HasDerivAt f (V (f t)) t)
    (hgc : ContinuousOn g (Ici 0)) (hg : ∀ t, 0 < t → HasDerivAt g (V (g t)) t)
    (h0 : f 0 = g 0) : EqOn f g (Ici 0) := fun t ht =>
  forwardFlow_unique_window V hV_lip (T := t + 1) (by linarith [show (0 : ℝ) ≤ t from ht])
    (hfc.mono Icc_subset_Ici_self) (fun s hs => hf s hs.1)
    (hgc.mono Icc_subset_Ici_self) (fun s hs => hg s hs.1) h0 ⟨ht, by linarith⟩

/-- **Forward flow from local Lipschitz continuity and a priori bounds.** Suppose `V` is Lipschitz
on balls and solutions on `[0, S]` starting in a ball stay in a ball whose radius depends only on
the horizon and the starting radius. Then there is a flow `Φ : E → ℝ → E` solving `x' = V x` for all
positive times, with `Φ x 0 = x` and `(x, t) ↦ Φ x t` continuous (for negative times `Φ x t = x` by
construction, which carries no meaning). Solutions are unique (`forwardFlow_unique`), so `Φ` is
*the* forward flow. -/
theorem exists_forward_flow (V : E → E)
    (hV_lip : ∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : E, ‖x‖ ≤ A → ‖y‖ ≤ A → ‖V x - V y‖ ≤ K * ‖x - y‖)
    (hprior : ∀ T r : ℝ, ∃ ρ : ℝ, ∀ (θ : ℝ → E) (S : ℝ), 0 ≤ S → S ≤ T →
      ‖θ 0‖ ≤ r → (∀ t ∈ Icc 0 S, HasDerivWithinAt θ (V (θ t)) (Icc 0 S) t) → ‖θ S‖ ≤ ρ) :
    ∃ Φ : E → ℝ → E, (∀ x, Φ x 0 = x) ∧ (∀ x t, 0 < t → HasDerivAt (Φ x) (V (Φ x t)) t) ∧
      Continuous (fun p : E × ℝ => Φ p.1 p.2) := by
  choose α hα using fun k : ℕ => exists_flow_window V hV_lip ((k + 1 : ℕ) : NNReal)
    ((k + 1 : ℕ) : NNReal) (hprior _ _)
  -- the radius/window `k + 1` in real form
  have hcast : ∀ k : ℕ, (((k + 1 : ℕ) : NNReal) : ℝ) = (k : ℝ) + 1 := fun k => by push_cast; ring
  have hsol : ∀ k : ℕ, ∀ x : E, ‖x‖ ≤ (k : ℝ) + 1 → α k (x, 0) = x ∧
      ∀ t ∈ Icc 0 ((k : ℝ) + 1), HasDerivWithinAt (fun s => α k (x, s))
        (V (α k (x, t))) (Icc 0 ((k : ℝ) + 1)) t := fun k x hx => by
    have := (hα k).1 x (by rw [mem_closedBall, dist_zero_right, hcast]; exact hx)
    simpa [hcast] using this
  have hcont : ∀ k : ℕ, ContinuousOn (α k)
      (closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1)) := fun k => by
    simpa [hcast] using (hα k).2
  -- consistency between different windows
  have hcons : ∀ k k' : ℕ, ∀ x : E, ‖x‖ ≤ (k : ℝ) + 1 → ‖x‖ ≤ (k' : ℝ) + 1 → ∀ t : ℝ,
      0 ≤ t → t ≤ (k : ℝ) + 1 → t ≤ (k' : ℝ) + 1 → α k (x, t) = α k' (x, t) := by
    intro k k' x hx hx' t ht0 ht ht'
    set m : ℕ := min k k' with hm
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast min_le_left k k'
    have hmk' : (m : ℝ) ≤ k' := by exact_mod_cast min_le_right k k'
    have hsub : ∀ j : ℕ, (m : ℝ) ≤ j → Icc 0 ((m : ℝ) + 1) ⊆ Icc 0 ((j : ℝ) + 1) :=
      fun j hj u hu => ⟨hu.1, by linarith [hu.2]⟩
    have hwin : ∀ j : ℕ, (m : ℝ) ≤ j → ‖x‖ ≤ (j : ℝ) + 1 →
        ContinuousOn (fun s => α j (x, s)) (Icc 0 ((m : ℝ) + 1)) ∧
        ∀ s ∈ Ioo 0 ((m : ℝ) + 1), HasDerivAt (fun s => α j (x, s)) (V (α j (x, s))) s :=
      fun j hj hxj =>
        ⟨fun s hs => (((hsol j x hxj).2 s (hsub j hj hs)).mono (hsub j hj)).continuousWithinAt,
          fun s hs => (((hsol j x hxj).2 s (hsub j hj (Ioo_subset_Icc_self hs))).mono
            (hsub j hj)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)⟩
    have hfun := forwardFlow_unique_window V hV_lip (T := (m : ℝ) + 1) (by positivity)
      (hwin k hmk hx).1 (hwin k hmk hx).2 (hwin k' hmk' hx').1 (hwin k' hmk' hx').2
      (by rw [(hsol k x hx).1, (hsol k' x hx').1])
    refine hfun ⟨ht0, ?_⟩
    rcases le_total k k' with h | h
    · rw [hm, min_eq_left h]; exact ht
    · rw [hm, min_eq_right h]; exact ht'
  set Φ : E → ℝ → E := fun x t => α ⌈max ‖x‖ t⌉₊ (x, t) with hΦ_def
  have hΦ : ∀ (x : E) (t : ℝ) (k : ℕ), ‖x‖ ≤ (k : ℝ) + 1 → 0 ≤ t → t ≤ (k : ℝ) + 1 →
      Φ x t = α k (x, t) := by
    intro x t k hx ht0 ht
    have hk₀ : max ‖x‖ t ≤ (⌈max ‖x‖ t⌉₊ : ℝ) := Nat.le_ceil _
    exact hcons _ k x ((le_max_left _ _).trans hk₀ |>.trans (by linarith)) hx t ht0
      ((le_max_right _ _).trans hk₀ |>.trans (by linarith)) ht
  have hmain : (∀ x, Φ x 0 = x) ∧ (∀ x t, 0 < t → HasDerivAt (Φ x) (V (Φ x t)) t) ∧
      ContinuousOn (fun p : E × ℝ => Φ p.1 p.2) (univ ×ˢ Ici 0) := by
    refine ⟨fun x => ?_, fun x t ht => ?_, fun p hp => ?_⟩
    · have hk : ‖x‖ ≤ (⌈max ‖x‖ 0⌉₊ : ℝ) + 1 :=
        ((le_max_left _ _).trans (Nat.le_ceil _)).trans (by linarith)
      rw [hΦ x 0 ⌈‖x‖⌉₊ ((Nat.le_ceil _).trans (by linarith)) le_rfl (by positivity),
        (hsol _ x ((Nat.le_ceil _).trans (by linarith))).1]
    · set k : ℕ := ⌈max ‖x‖ (t + 1)⌉₊ with hk_def
      have hk₀ : max ‖x‖ (t + 1) ≤ (k : ℝ) := Nat.le_ceil _
      have hxk : ‖x‖ ≤ (k : ℝ) + 1 := (le_max_left _ _).trans hk₀ |>.trans (by linarith)
      have ht1 : t + 1 ≤ (k : ℝ) := (le_max_right _ _).trans hk₀
      have hmem : t ∈ Icc 0 ((k : ℝ) + 1) := ⟨ht.le, by linarith⟩
      have hnhds : Icc 0 ((k : ℝ) + 1) ∈ nhds t := Icc_mem_nhds ht (by linarith)
      have hd := ((hsol k x hxk).2 t hmem).hasDerivAt hnhds
      have hev : (fun s => α k (x, s)) =ᶠ[nhds t] Φ x := by
        have hnb : Ioo (t / 2) (t + 1) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hnb] with s hs
        exact (hΦ x s k hxk (by linarith [hs.1]) (by linarith [hs.2])).symm
      rw [hΦ x t k hxk ht.le (by linarith)]
      exact (hd.congr_of_eventuallyEq hev.symm)
    · obtain ⟨x₀, t₀⟩ := p
      have ht₀ : 0 ≤ t₀ := hp.2
      set k : ℕ := ⌈max (‖x₀‖ + 1) (t₀ + 1)⌉₊ with hk_def
      have hk₀ : max (‖x₀‖ + 1) (t₀ + 1) ≤ (k : ℝ) := Nat.le_ceil _
      have hx₀k : ‖x₀‖ + 1 ≤ (k : ℝ) := (le_max_left _ _).trans hk₀
      have ht₀k : t₀ + 1 ≤ (k : ℝ) := (le_max_right _ _).trans hk₀
      have hnb : ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1) ∈ nhds (x₀, t₀) :=
        prod_mem_nhds (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; linarith))
          (Iio_mem_nhds (by linarith))
      have hUsub : ∀ q ∈ ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1), 0 ≤ q.2 →
          ‖q.1‖ ≤ (k : ℝ) + 1 ∧ q.2 ≤ (k : ℝ) + 1 := fun q hq _ => by
        refine ⟨?_, ?_⟩
        · have := mem_ball_zero_iff.1 hq.1
          linarith
        · linarith [mem_Iio.1 hq.2]
      have hmem : (x₀, t₀) ∈ closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1) :=
        ⟨by rw [mem_closedBall, dist_zero_right]; linarith, ht₀, by linarith⟩
      have hat : ContinuousWithinAt (α k) (closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1))
          (x₀, t₀) := (hcont k) (x₀, t₀) hmem
      have hmemW : closedBall (0 : E) ((k : ℝ) + 1) ×ˢ Icc 0 ((k : ℝ) + 1) ∈
          nhdsWithin (x₀, t₀) (univ ×ˢ Ici 0) := by
        rw [mem_nhdsWithin]
        refine ⟨ball (0 : E) (‖x₀‖ + 1) ×ˢ Iio (t₀ + 1), isOpen_ball.prod isOpen_Iio,
          ⟨by rw [mem_ball, dist_zero_right]; linarith, by simp only [mem_Iio]; linarith⟩, ?_⟩
        · rintro q ⟨hq, -, hq0⟩
          obtain ⟨h1, h2⟩ := hUsub q hq hq0
          exact ⟨by rw [mem_closedBall, dist_zero_right]; exact h1, hq0, h2⟩
      refine (hat.mono_of_mem_nhdsWithin hmemW).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [hmemW, self_mem_nhdsWithin] with q hq _
        exact hΦ q.1 q.2 k (by simpa [mem_closedBall, dist_zero_right] using hq.1) hq.2.1
          hq.2.2
      · exact hΦ x₀ t₀ k (by linarith) ht₀ (by linarith)
  obtain ⟨h0, hd, hc⟩ := hmain
  -- extend by the value at `0` for negative times, so that `Φ` is continuous everywhere
  refine ⟨fun x t => Φ x (max t 0), fun x => by simpa using h0 x, fun x t ht => ?_,
    hc.comp_continuous (continuous_fst.prodMk (continuous_snd.max continuous_const))
      fun p => ⟨trivial, show (0 : ℝ) ≤ max p.2 0 from le_max_right _ _⟩⟩
  have e : Φ x (max t 0) = Φ x t := by rw [max_eq_left ht.le]
  change HasDerivAt (fun s => Φ x (max s 0)) (V (Φ x (max t 0))) t
  rw [e]
  exact (hd x t ht).congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [max_eq_left (le_of_lt hs)])

/-- A finite sum of locally Lipschitz functions is locally Lipschitz. -/
lemma locallyLipschitz_finset_sum {α ι β : Type*} [PseudoEMetricSpace α] [SeminormedAddCommGroup β]
    (s : Finset ι) {f : ι → α → β} (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : β)).locallyLipschitz
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The product of two locally Lipschitz real functions is locally Lipschitz (multiplication on
`ℝ × ℝ` is `C¹`, hence locally Lipschitz). Mathlib's `LocallyLipschitz.mul` is the product in a
seminormed commutative *group*, so it does not apply to multiplication in `ℝ`. -/
lemma locallyLipschitz_mul_real {α : Type*} [PseudoEMetricSpace α] {f g : α → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (fun x => f x * g x) :=
  (contDiff_mul.locallyLipschitz (𝕂 := ℝ) (E' := ℝ × ℝ) (F' := ℝ)).comp (hf.prodMk hg)

/-- The Euclidean norm is at most the `ℓ¹` norm of the coordinates. -/
lemma norm_euclidean_le_sum_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (v : EuclideanSpace 𝕜 ι) : ‖v‖ ≤ ∑ k, ‖v k‖ := by
  rw [EuclideanSpace.norm_eq]
  exact Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun k _ => norm_nonneg _,
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun k => ‖v k‖)
      fun k _ => norm_nonneg (v k)⟩

/-- A map into `EuclideanSpace ℝ ι` (`ι` finite) is locally Lipschitz if every coordinate is
locally Lipschitz. Mathlib has no `Pi`/`PiLp` version of this. -/
lemma locallyLipschitz_euclidean_of_coord {α ι : Type*} [PseudoMetricSpace α] [Fintype ι]
    {g : α → EuclideanSpace ℝ ι} (h : ∀ k, LocallyLipschitz (fun x => g x k)) :
    LocallyLipschitz g := by
  intro x
  choose K t ht hK using fun k => h k x
  refine ⟨⟨∑ k, (K k : ℝ), Finset.sum_nonneg fun k _ => (K k).2⟩, ⋂ k, t k,
    Filter.iInter_mem.2 ht, LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  rw [dist_eq_norm]
  refine (norm_euclidean_le_sum_norm _).trans ?_
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  calc ∑ k, |g y k - g z k| ≤ ∑ k, (K k : ℝ) * dist y z := by
        refine Finset.sum_le_sum fun k _ => ?_
        have := (hK k).dist_le_mul y (Set.mem_iInter.1 hy k) z (Set.mem_iInter.1 hz k)
        simpa [Real.dist_eq] using this
    _ = _ := by rw [← Finset.sum_mul]; rfl

end GlobalFlowConstruction

end NTK

end
