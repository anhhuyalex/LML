/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Real functions that are `C²` with bounded value, first and second derivative

`BoundedC2 f` says that `f : X → ℝ` is `C²` and `f`, `fderiv f`, `fderiv (fderiv f)` are bounded.
The class is closed under sums, products, and composition with a scalar function that is `C²`
near the range; in particular a quotient of such functions with denominator bounded below.

* `BoundedC2`, `BoundedC2.add`, `BoundedC2.mul`, `BoundedC2.comp`, `BoundedC2.inv`.
-/

@[expose] public section

open scoped ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A real function on a normed space that is `C²` with bounded value, derivative and second
derivative. -/
def BoundedC2 (f : X → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C

namespace BoundedC2

variable {f g : X → ℝ}

theorem contDiff (hf : BoundedC2 f) : ContDiff ℝ 2 f := hf.1

theorem differentiable (hf : BoundedC2 f) : Differentiable ℝ f :=
  hf.1.differentiable (by norm_num)

theorem differentiable_fderiv (hf : BoundedC2 f) : Differentiable ℝ (fderiv ℝ f) := by
  have : ContDiff ℝ 1 (fderiv ℝ f) := hf.1.fderiv_right (by norm_num)
  exact this.differentiable one_ne_zero

/-- A common bound for the value and the two derivatives, which may be taken nonnegative. -/
theorem exists_bound (hf : BoundedC2 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨C, (abs_nonneg _).trans (hC 0).1, hC⟩

theorem const (c : ℝ) : BoundedC2 (fun _ : X => c) := by
  refine ⟨contDiff_const, |c|, fun x => ⟨le_rfl, ?_, ?_⟩⟩
  · simp only [fderiv_fun_const, Pi.zero_apply]
    exact (ContinuousLinearMap.opNorm_zero (𝕜 := ℝ) (E := X) (F := ℝ)).le.trans (abs_nonneg c)
  · have : fderiv ℝ (fun _ : X => c) = 0 := fderiv_fun_const c
    rw [this]
    simp only [fderiv_zero, Pi.zero_apply]
    exact (ContinuousLinearMap.opNorm_zero (𝕜 := ℝ) (E := X) (F := X →L[ℝ] ℝ)).le.trans
      (abs_nonneg c)

theorem add (hf : BoundedC2 f) (hg : BoundedC2 g) : BoundedC2 (fun x => f x + g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.exists_bound
  obtain ⟨Cg, hCg0, hCg⟩ := hg.exists_bound
  refine ⟨hf.1.add hg.1, Cf + Cg, fun x => ⟨?_, ?_, ?_⟩⟩
  · exact (abs_add_le _ _).trans (add_le_add (hCf x).1 (hCg x).1)
  · rw [fderiv_fun_add (hf.differentiable x) (hg.differentiable x)]
    exact (norm_add_le _ _).trans (add_le_add (hCf x).2.1 (hCg x).2.1)
  · have : fderiv ℝ (fun x => f x + g x) =
        fun x => fderiv ℝ f x + fderiv ℝ g x :=
      funext fun x => fderiv_fun_add (hf.differentiable x) (hg.differentiable x)
    rw [this, fderiv_fun_add (hf.differentiable_fderiv x) (hg.differentiable_fderiv x)]
    have := norm_add_le (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ g) x)
    linarith [(hCf x).2.2, (hCg x).2.2]

theorem mul (hf : BoundedC2 f) (hg : BoundedC2 g) : BoundedC2 (fun x => f x * g x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := hf.exists_bound
  obtain ⟨Cg, hCg0, hCg⟩ := hg.exists_bound
  refine ⟨hf.1.mul hg.1, Cf * Cg + Cf * Cg + Cf * Cg + Cf * Cg, fun x => ⟨?_, ?_, ?_⟩⟩
  · rw [abs_mul]
    have := mul_le_mul (hCf x).1 (hCg x).1 (abs_nonneg _) hCf0
    nlinarith [mul_nonneg hCf0 hCg0]
  · rw [fderiv_fun_mul (hf.differentiable x) (hg.differentiable x)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := mul_le_mul (hCf x).1 (hCg x).2.1 (norm_nonneg _) hCf0
    have h2 := mul_le_mul (hCg x).1 (hCf x).2.1 (norm_nonneg _) hCg0
    nlinarith [mul_nonneg hCf0 hCg0]
  · have hfun : fderiv ℝ (fun x => f x * g x) =
        fun x => f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
      funext fun x => fderiv_fun_mul (hf.differentiable x) (hg.differentiable x)
    rw [hfun, fderiv_fun_add
      (DifferentiableAt.fun_smul (hf.differentiable x) (hg.differentiable_fderiv x))
      (DifferentiableAt.fun_smul (hg.differentiable x) (hf.differentiable_fderiv x)),
      fderiv_fun_smul (hf.differentiable x) (hg.differentiable_fderiv x),
      fderiv_fun_smul (hg.differentiable x) (hf.differentiable_fderiv x)]
    have e1 : ‖f x • fderiv ℝ (fderiv ℝ g) x‖ ≤ Cf * Cg := by
      refine (ContinuousLinearMap.opNorm_smul_le (f x) _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul (hCf x).1 (hCg x).2.2 (ContinuousLinearMap.opNorm_nonneg _) hCf0
    have e2 : ‖(fderiv ℝ f x).smulRight (fderiv ℝ g x)‖ ≤ Cf * Cg := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul (hCf x).2.1 (hCg x).2.1 (norm_nonneg _) hCf0
    have e3 : ‖g x • fderiv ℝ (fderiv ℝ f) x‖ ≤ Cf * Cg := by
      refine (ContinuousLinearMap.opNorm_smul_le (g x) _).trans ?_
      rw [Real.norm_eq_abs, mul_comm Cf]
      exact mul_le_mul (hCg x).1 (hCf x).2.2 (ContinuousLinearMap.opNorm_nonneg _) hCg0
    have e4 : ‖(fderiv ℝ g x).smulRight (fderiv ℝ f x)‖ ≤ Cf * Cg := by
      rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm Cf]
      exact mul_le_mul (hCg x).2.1 (hCf x).2.1 (norm_nonneg _) hCg0
    have n1 := norm_add_le (f x • fderiv ℝ (fderiv ℝ g) x + (fderiv ℝ f x).smulRight (fderiv ℝ g x))
      (g x • fderiv ℝ (fderiv ℝ f) x + (fderiv ℝ g x).smulRight (fderiv ℝ f x))
    have n2 := norm_add_le (f x • fderiv ℝ (fderiv ℝ g) x) ((fderiv ℝ f x).smulRight (fderiv ℝ g x))
    have n3 := norm_add_le (g x • fderiv ℝ (fderiv ℝ f) x) ((fderiv ℝ g x).smulRight (fderiv ℝ f x))
    linarith

/-- **Composition with a scalar function.** If `h` is differentiable with differentiable derivative
at every value of `f`, `h ∘ f` is `C²`, and `h`, `h'`, `h''` are bounded on the range of `f`, then
`h ∘ f` is `BoundedC2`. -/
theorem comp (hf : BoundedC2 f) {h : ℝ → ℝ} (hcomp : ContDiff ℝ 2 (fun x => h (f x)))
    (hh1 : ∀ x, DifferentiableAt ℝ h (f x)) (hh2 : ∀ x, DifferentiableAt ℝ (deriv h) (f x))
    {M : ℝ} (hM : ∀ x, |h (f x)| ≤ M ∧ |deriv h (f x)| ≤ M ∧ |deriv (deriv h) (f x)| ≤ M) :
    BoundedC2 (fun x => h (f x)) := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (0 : X)).1
  have d1 : ∀ x, fderiv ℝ (fun x => h (f x)) x = deriv h (f x) • fderiv ℝ f x := fun x =>
    ((hh1 x).hasDerivAt.comp_hasFDerivAt x (hf.differentiable x).hasFDerivAt).fderiv
  have dc : ∀ x, fderiv ℝ (fun x => deriv h (f x)) x =
      deriv (deriv h) (f x) • fderiv ℝ f x := fun x =>
    ((hh2 x).hasDerivAt.comp_hasFDerivAt x (hf.differentiable x).hasFDerivAt).fderiv
  have dcd : ∀ x, DifferentiableAt ℝ (fun x => deriv h (f x)) x := fun x =>
    ((hh2 x).hasDerivAt.comp_hasFDerivAt x (hf.differentiable x).hasFDerivAt).differentiableAt
  refine ⟨hcomp, M * (1 + 2 * C + C * C), fun x => ⟨?_, ?_, ?_⟩⟩
  · have := (hM x).1
    nlinarith [mul_nonneg hM0 hC0, mul_nonneg hM0 (mul_nonneg hC0 hC0)]
  · rw [d1, norm_smul, Real.norm_eq_abs]
    have := mul_le_mul (hM x).2.1 (hC x).2.1 (norm_nonneg _) hM0
    nlinarith [mul_nonneg hM0 hC0, mul_nonneg hM0 (mul_nonneg hC0 hC0)]
  · have hfun : fderiv ℝ (fun x => h (f x)) = fun x => deriv h (f x) • fderiv ℝ f x := funext d1
    rw [hfun, fderiv_fun_smul (dcd x) (hf.differentiable_fderiv x), dc x]
    have e1 : ‖deriv h (f x) • fderiv ℝ (fderiv ℝ f) x‖ ≤ M * C := by
      refine (ContinuousLinearMap.opNorm_smul_le (deriv h (f x)) _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul (hM x).2.1 (hC x).2.2 (ContinuousLinearMap.opNorm_nonneg _) hM0
    have e2 : ‖(deriv (deriv h) (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ ≤ M * C * C := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (hM x).2.2 (hC x).2.1 (norm_nonneg _) hM0) (hC x).2.1
        (norm_nonneg _) (mul_nonneg hM0 hC0)
    have n1 := norm_add_le (deriv h (f x) • fderiv ℝ (fderiv ℝ f) x)
      ((deriv (deriv h) (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x))
    nlinarith [mul_nonneg hM0 hC0, mul_nonneg hM0 (mul_nonneg hC0 hC0)]

theorem deriv_inv_real : deriv (fun x : ℝ => x⁻¹) = fun x => -(x ^ 2)⁻¹ := deriv_inv'

theorem deriv_deriv_inv_real {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv fun x : ℝ => x⁻¹) x = 2 * (x⁻¹) ^ 3 := by
  rw [deriv_inv_real]
  have h : HasDerivAt (fun x : ℝ => -(x ^ 2)⁻¹) (2 * (x⁻¹) ^ 3) x := by
    have h3 := ((hasDerivAt_pow 2 x).fun_inv (pow_ne_zero 2 hx)).neg
    refine h3.congr_deriv ?_
    field_simp
    ring
  exact h.deriv

/-- **Inverse.** A `BoundedC2` function bounded below by a positive constant has a `BoundedC2`
inverse. -/
theorem inv (hf : BoundedC2 f) {c : ℝ} (hc : 0 < c) (hfc : ∀ x, c ≤ f x) :
    BoundedC2 (fun x => (f x)⁻¹) := by
  have hne : ∀ x, f x ≠ 0 := fun x => (hc.trans_le (hfc x)).ne'
  have hr : ∀ x, (f x)⁻¹ ≤ c⁻¹ := fun x => inv_anti₀ hc (hfc x)
  have hr0 : ∀ x, 0 < (f x)⁻¹ := fun x => inv_pos.2 (hc.trans_le (hfc x))
  have hcc : 0 < c⁻¹ := inv_pos.2 hc
  refine hf.comp (h := fun x : ℝ => x⁻¹) (M := c⁻¹ + c⁻¹ ^ 2 + 2 * c⁻¹ ^ 3)
    (hf.1.inv hne) (fun x => differentiableAt_inv (hne x)) (fun x => ?_) (fun x => ⟨?_, ?_, ?_⟩)
  · rw [deriv_inv_real]
    exact (by fun_prop (disch := exact pow_ne_zero 2 (hne x)) : DifferentiableAt ℝ
      (fun x : ℝ => -(x ^ 2)⁻¹) (f x))
  · rw [abs_of_pos (hr0 x)]
    nlinarith [pow_pos hcc 2, pow_pos hcc 3, hr x]
  · rw [deriv_inv_real, abs_neg, abs_of_pos (inv_pos.2 (pow_pos (hc.trans_le (hfc x)) 2)),
      ← inv_pow]
    have : (f x)⁻¹ ^ 2 ≤ c⁻¹ ^ 2 := pow_le_pow_left₀ (hr0 x).le (hr x) 2
    nlinarith [pow_pos hcc 3, hr x, hcc]
  · rw [deriv_deriv_inv_real (hne x), abs_of_pos (by positivity [hr0 x])]
    have : (f x)⁻¹ ^ 3 ≤ c⁻¹ ^ 3 := pow_le_pow_left₀ (hr0 x).le (hr x) 3
    nlinarith [pow_pos hcc 2, hr x, hcc]

theorem pow (hf : BoundedC2 f) (n : ℕ) : BoundedC2 (fun x => f x ^ n) := by
  induction n with
  | zero => simpa using const (X := X) 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, BoundedC2 (f i)) :
    BoundedC2 (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (X := X) 0
  | insert a s ha ih =>
    simpa [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {f : ι → X → ℝ} (hf : ∀ i ∈ s, BoundedC2 (f i)) :
    BoundedC2 (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (X := X) 1
  | insert a s ha ih =>
    simpa [Finset.prod_insert ha] using
      (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Quotient by a power.** `N / D ^ n` is `BoundedC2` when `N`, `D` are and `D ≥ c > 0`. -/
theorem div_pow (hN : BoundedC2 f) (hD : BoundedC2 g) {c : ℝ} (hc : 0 < c) (hDc : ∀ x, c ≤ g x)
    (n : ℕ) : BoundedC2 (fun x => f x / g x ^ n) := by
  have hpow := hD.pow n
  have hinv := hpow.inv (pow_pos hc n) (fun x => pow_le_pow_left₀ hc.le (hDc x) n)
  simpa [div_eq_mul_inv] using hN.mul hinv

/-- **Replica ratio of bounded `C²` functions.** For positive weights `w`, values `ψ a` that are
`BoundedC2` and bounded below by `c > 0`, and any observable `f` of `R`-tuples of the finite index
set, the Gibbs-type ratio
`(∑_ā f ā ∏_r w (ā r) ψ (ā r) x) / (∑_a w a ψ a x) ^ |R|` is `BoundedC2`. -/
theorem replicaRatio {κ R : Type*} [Fintype κ] [Fintype R] [DecidableEq R] [Nonempty κ]
    {ψ : κ → X → ℝ} (hψ : ∀ a, BoundedC2 (ψ a)) {w : κ → ℝ} (hw : ∀ a, 0 < w a) {c : ℝ}
    (hc : 0 < c) (hψc : ∀ a x, c ≤ ψ a x) (f : (R → κ) → ℝ) :
    BoundedC2 (fun x => (∑ ā : R → κ, f ā * ∏ r, (w (ā r) * ψ (ā r) x)) /
      (∑ a, w a * ψ a x) ^ Fintype.card R) := by
  have hnum : BoundedC2 (fun x => ∑ ā : R → κ, f ā * ∏ r, (w (ā r) * ψ (ā r) x)) :=
    BoundedC2.sum _ fun ā _ => (const (f ā)).mul
      (BoundedC2.prod _ fun r _ => (const (w (ā r))).mul (hψ (ā r)))
  have hden : BoundedC2 (fun x => ∑ a, w a * ψ a x) :=
    BoundedC2.sum _ fun a _ => (const (w a)).mul (hψ a)
  have hW : 0 < ∑ a, w a := Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  refine hnum.div_pow hden (c := c * ∑ a, w a) (mul_pos hc hW) (fun x => ?_) _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left (hψc a x) (hw a).le

end BoundedC2
