/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exponential and hyperbolic moments of linear forms in independent standard Gaussians

For independent standard Gaussians `g : E → ℝ` (law `Measure.pi fun _ => gaussianReal 0 1`) and
coefficients `c : E → ℝ`, `m : ℝ`:

* `integral_exp_sum_mul_gaussianReal`: `𝔼 exp (∑ cₑ gₑ) = exp (∑ cₑ² / 2)`;
* `integral_cosh_sum_mul_gaussianReal`: `𝔼 cosh (∑ cₑ gₑ + m) = cosh m * exp (∑ cₑ² / 2)`.
* `integral_cosh_two_sum_mul_gaussianReal`: the corresponding formula for two independent
  finite Gaussian blocks;
* `integral_cosh_sum_mul_add_mul_gaussianReal`: the product-space formula for a finite block
  and one independent scalar Gaussian.

Both come with their integrability statements.  The one-dimensional case is
`integral_exp_mul_gaussianReal_zero_one`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Moment generating function of a standard Gaussian `𝒩(0, 1)`. -/
theorem integral_exp_mul_gaussianReal_zero_one (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  have h := congr_fun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  dsimp [ProbabilityTheory.mgf] at h
  rw [h]
  ring_nf

/-- Integrability of the exponential of a linear combination of independent standard Gaussians. -/
theorem integrable_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    Integrable (fun g : E → ℝ => Real.exp (∑ e, c e * g e))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  have e : (fun g : E → ℝ => Real.exp (∑ e, c e * g e)) =
      fun g => ∏ e, Real.exp (c e * g e) := by
    ext g
    rw [Real.exp_sum]
  rw [e]
  exact MeasureTheory.Integrable.fintype_prod (fun e => integrable_exp_mul_gaussianReal (c e))

/-- Integral of the exponential of a linear combination of independent standard Gaussians. -/
theorem integral_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    ∫ g : E → ℝ, Real.exp (∑ e, c e * g e)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.exp (∑ e, c e ^ 2 / 2) := by
  simp_rw [Real.exp_sum]
  have h_int := MeasureTheory.integral_fintype_prod_eq_prod
    (E := fun _ : E => ℝ) (μ := fun _ : E => gaussianReal 0 1)
    (fun e (x : ℝ) => Real.exp (c e * x))
  rw [h_int]
  have h (e : E) : ∫ x, Real.exp (c e * x) ∂(gaussianReal 0 1) = Real.exp (c e ^ 2 / 2) :=
    integral_exp_mul_gaussianReal_zero_one (c e)
  rw [Finset.prod_congr rfl fun e _ => h e, ← Real.exp_sum]

/-- Integrability of a product of exponential linear forms in two independent finite Gaussian
blocks. -/
theorem integrable_exp_prod_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) :
    Integrable (fun ω : (K → ℝ) × (L → ℝ) =>
      Real.exp (∑ i, c i * ω.1 i) * Real.exp (∑ j, d j * ω.2 j))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) :=
  (integrable_exp_sum_mul_gaussianReal c).mul_prod
    (integrable_exp_sum_mul_gaussianReal d)

/-- Integrability of a product of an exponential linear form in a finite Gaussian block and an
exponential multiple of an independent scalar Gaussian. -/
theorem integrable_exp_mul_prod_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d : ℝ) :
    Integrable (fun ω : (K → ℝ) × ℝ =>
      Real.exp (∑ i, c i * ω.1 i) * Real.exp (d * ω.2))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  (integrable_exp_sum_mul_gaussianReal c).mul_prod
    (integrable_exp_mul_gaussianReal d)

/-- `cosh` of an affine form is the average of the exponentials of `±` the form. -/
theorem cosh_sum_mul_add_eq {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) (g : E → ℝ) :
    Real.cosh (∑ e, c e * g e + m) =
      (Real.exp m * Real.exp (∑ e, c e * g e) +
        Real.exp (-m) * Real.exp (∑ e, (-c) e * g e)) / 2 := by
  have hneg : ∑ e, (-c) e * g e = -∑ e, c e * g e := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [Real.cosh_eq, hneg, neg_add, Real.exp_add, Real.exp_add]
  ring

/-- Integrability of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integrable_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    Integrable (fun g : E → ℝ => Real.cosh (∑ e, c e * g e + m))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  simp_rw [cosh_sum_mul_add_eq]
  exact (((integrable_exp_sum_mul_gaussianReal c).const_mul _).add
    ((integrable_exp_sum_mul_gaussianReal (-c)).const_mul _)).div_const 2

/-- Integral of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integral_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    ∫ g : E → ℝ, Real.cosh (∑ e, c e * g e + m)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.cosh m * Real.exp (∑ e, c e ^ 2 / 2) := by
  simp_rw [cosh_sum_mul_add_eq]
  rw [integral_div, integral_add ((integrable_exp_sum_mul_gaussianReal c).const_mul _)
    ((integrable_exp_sum_mul_gaussianReal (-c)).const_mul _), integral_const_mul,
    integral_const_mul, integral_exp_sum_mul_gaussianReal c,
    integral_exp_sum_mul_gaussianReal (-c)]
  have hsq : (∑ e, (-c) e ^ 2 / 2) = ∑ e, c e ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  rw [hsq, Real.cosh_eq]
  ring


/-- `cosh` of affine forms in two independent finite Gaussian blocks is the average of the
corresponding positive and negative exponential products. -/
theorem cosh_two_sum_mul_add_eq {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) (ω : (K → ℝ) × (L → ℝ)) :
    Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m) =
      (Real.exp m *
            (Real.exp (∑ i, c i * ω.1 i) * Real.exp (∑ j, d j * ω.2 j)) +
          Real.exp (-m) *
            (Real.exp (∑ i, (-c) i * ω.1 i) *
              Real.exp (∑ j, (-d) j * ω.2 j))) /
        2 := by
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
    Real.cosh_add_add_eq (∑ i, c i * ω.1 i) (∑ j, d j * ω.2 j) m

/-- Integrability of `cosh` of an affine combination of two independent finite Gaussian
blocks. -/
theorem integrable_cosh_two_sum_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) :
    Integrable (fun ω : (K → ℝ) × (L → ℝ) =>
      Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) := by
  simp_rw [cosh_two_sum_mul_add_eq c d m]
  have h1 := integrable_exp_prod_mul_gaussianReal c d
  have h2 := integrable_exp_prod_mul_gaussianReal (-c) (-d)
  exact ((h1.const_mul _).add (h2.const_mul _)).div_const 2

/-- Integral of `cosh` of an affine combination of two independent finite Gaussian blocks. -/
theorem integral_cosh_two_sum_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) :
    ∫ ω : (K → ℝ) × (L → ℝ),
      Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m)
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) =
    Real.cosh m * Real.exp ((∑ i, c i ^ 2 + ∑ j, d j ^ 2) / 2) := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : K ⊕ L => ℝ) (fun _ => gaussianReal 0 1)
  calc
    (∫ ω : (K → ℝ) × (L → ℝ),
        Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m)
        ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod
          (Measure.pi fun _ : L => gaussianReal 0 1))) =
      ∫ ξ : K ⊕ L → ℝ, Real.cosh (∑ k, Sum.elim c d k * ξ k + m)
        ∂(Measure.pi fun _ : K ⊕ L => gaussianReal 0 1) := by
      rw [← hmp.integral_comp']
      congr 1
      funext ω
      simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Fintype.sum_sum_type]
    _ = Real.cosh m * Real.exp (∑ k : K ⊕ L, Sum.elim c d k ^ 2 / 2) :=
      integral_cosh_sum_mul_gaussianReal (Sum.elim c d) m
    _ = Real.cosh m * Real.exp ((∑ i, c i ^ 2 + ∑ j, d j ^ 2) / 2) := by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]


/-- `cosh` of an affine form in a finite Gaussian block and one scalar Gaussian is the average
of the corresponding positive and negative exponential products. -/
theorem cosh_sum_mul_add_mul_eq {K : Type*} [Fintype K] (c : K → ℝ) (d m : ℝ)
    (ω : (K → ℝ) × ℝ) :
    Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m) =
      (Real.exp m * (Real.exp (∑ i, c i * ω.1 i) * Real.exp (d * ω.2)) +
        Real.exp (-m) *
          (Real.exp (∑ i, (-c) i * ω.1 i) * Real.exp (-d * ω.2))) / 2 := by
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
    Real.cosh_add_add_eq (∑ i, c i * ω.1 i) (d * ω.2) m

/-- Integrability of `cosh` of an affine combination of a finite Gaussian block and one
independent scalar Gaussian. -/
theorem integrable_cosh_sum_mul_add_mul_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d m : ℝ) :
    Integrable (fun ω : (K → ℝ) × ℝ =>
      Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  simp_rw [cosh_sum_mul_add_mul_eq c d m]
  have h1 := integrable_exp_mul_prod_gaussianReal c d
  have h2 := integrable_exp_mul_prod_gaussianReal (-c) (-d)
  exact ((h1.const_mul _).add (h2.const_mul _)).div_const 2

/-- Integral of `cosh` of an affine combination of a finite Gaussian block and one independent
scalar Gaussian. -/
theorem integral_cosh_sum_mul_add_mul_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d m : ℝ) :
    ∫ ω : (K → ℝ) × ℝ, Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m)
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) =
    Real.cosh m * Real.exp ((∑ i, c i ^ 2 + d ^ 2) / 2) := by
  simp_rw [cosh_sum_mul_add_mul_eq c d m]
  have h1 := integrable_exp_mul_prod_gaussianReal c d
  have h2 := integrable_exp_mul_prod_gaussianReal (-c) (-d)
  rw [integral_div, integral_add (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, c i * g i))
      (fun z : ℝ => Real.exp (d * z)),
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, (-c) i * g i))
      (fun z : ℝ => Real.exp (-d * z)),
    integral_exp_sum_mul_gaussianReal c, integral_exp_sum_mul_gaussianReal (-c),
    integral_exp_mul_gaussianReal_zero_one d,
    integral_exp_mul_gaussianReal_zero_one (-d)]
  have hc : ∑ i, (-c) i ^ 2 / 2 = ∑ i, c i ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  have hd : (-d) ^ 2 / 2 = d ^ 2 / 2 := by ring
  rw [hc, hd]
  have hsum : ∑ i, c i ^ 2 / 2 + d ^ 2 / 2 =
      (∑ i, c i ^ 2 + d ^ 2) / 2 := by
    rw [← Finset.sum_div, ← add_div]
  have hv : Real.exp (∑ i, c i ^ 2 / 2) * Real.exp (d ^ 2 / 2) =
      Real.exp ((∑ i, c i ^ 2 + d ^ 2) / 2) := by
    rw [← Real.exp_add, hsum]
  rw [hv, Real.cosh_eq]
  ring

/-- Gaussian integration by parts for the exponential: `𝔼[Z exp (c Z)] = c exp (c² / 2)` for
`Z ~ 𝒩(0, 1)`. -/
theorem integral_id_mul_exp_mul_gaussianReal_zero_one (c : ℝ) :
    ∫ t, t * Real.exp (c * t) ∂(gaussianReal 0 1) = c * Real.exp (c ^ 2 / 2) := by
  have hF : ∀ x, HasDerivAt (fun y => Real.exp (c * y)) (c * Real.exp (c * x)) x := fun x => by
    have h := ((hasDerivAt_id' x).const_mul c).exp
    convert h using 1
    ring
  have hxF : Integrable (fun x => x * Real.exp (c * x)) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_exp_mul_abs_gaussianReal (1 + |c|)) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc |x| * Real.exp (c * x) ≤ Real.exp |x| * Real.exp (|c| * |x|) :=
          mul_le_mul (by linarith [Real.add_one_le_exp |x|])
            (Real.exp_le_exp.2 ((le_abs_self _).trans_eq (abs_mul c x)))
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((1 + |c|) * |x|) := by rw [← Real.exp_add]; congr 1; ring
  have hF' : Integrable (fun x => c * Real.exp (c * x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c).const_mul c
  have h := integral_id_mul_gaussianReal_eq (v := 1) hF hxF hF'
  simp only [NNReal.coe_one, one_mul] at h
  rw [h, integral_const_mul, integral_exp_mul_gaussianReal_zero_one]

/-- Integrability of `exp (u ⬝ y)` against i.i.d. standard Gaussians. -/
theorem integrable_exp_dotProduct_gaussianReal {N : ℕ} (u : Fin N → ℝ) :
    Integrable (fun y : Fin N → ℝ => Real.exp (u ⬝ᵥ y))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  have heq : (fun y : Fin N → ℝ => Real.exp (u ⬝ᵥ y)) =
      fun y => Real.exp (∑ i, u i * y i) := by
    ext y; simp [dotProduct]
  rw [heq]
  exact integrable_exp_sum_mul_gaussianReal u

/-- Integrability of `exp (c * (u ⬝ y))` against i.i.d. standard Gaussians. -/
theorem integrable_exp_const_mul_dotProduct_gaussianReal {N : ℕ} (c : ℝ) (u : Fin N → ℝ) :
    Integrable (fun y : Fin N → ℝ => Real.exp (c * (u ⬝ᵥ y)))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simpa only [smul_dotProduct, smul_eq_mul] using integrable_exp_dotProduct_gaussianReal (c • u)

/-- `𝔼 exp (c N^{-1/2} ∑ mᵢ yᵢ) ≤ exp (c² / 2)` for `y` standard Gaussian and `|mᵢ| ≤ 1`. -/
theorem integral_exp_sum_ising_moment_le {N : ℕ} (hN : 0 < N) (c : ℝ)
    (m : Fin N → ℝ) (hm : ∀ i, |m i| ≤ 1) :
    ∫ y : Fin N → ℝ, Real.exp (c * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y))
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
    Real.exp (c ^ 2 / 2) := by
  have heq : (fun y : Fin N → ℝ =>
      Real.exp (c * ((fun i => (Real.sqrt N)⁻¹ * m i) ⬝ᵥ y))) =
      fun y => Real.exp (∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) * y i) := by
    ext y
    simp only [dotProduct]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [heq, integral_exp_sum_mul_gaussianReal]
  have h_sq_le (i : Fin N) : (c * (Real.sqrt N)⁻¹ * m i) ^ 2 ≤ c ^ 2 / (N : ℝ) := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hsqrt_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
    have hm_sq : (m i) ^ 2 ≤ 1 := by
      calc (m i) ^ 2 = |m i| ^ 2 := (sq_abs (m i)).symm
        _ ≤ 1 ^ 2 := by nlinarith [hm i, abs_nonneg (m i)]
        _ = 1 := by norm_num
    calc (c * (Real.sqrt N)⁻¹ * m i) ^ 2
      _ = c ^ 2 * ((Real.sqrt N)⁻¹ ^ 2) * (m i) ^ 2 := by ring
      _ = c ^ 2 * ((Real.sqrt N) ^ 2)⁻¹ * (m i) ^ 2 := by rw [inv_pow]
      _ = (c ^ 2 / (N : ℝ)) * (m i) ^ 2 := by rw [hsqrt_sq]; ring
      _ ≤ (c ^ 2 / (N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hm_sq (by positivity)
      _ = c ^ 2 / (N : ℝ) := mul_one _
  have h_sum_le : ∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) ^ 2 / 2 ≤ c ^ 2 / 2 := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    calc ∑ i : Fin N, (c * (Real.sqrt N)⁻¹ * m i) ^ 2 / 2
      _ ≤ ∑ i : Fin N, (c ^ 2 / (N : ℝ)) / 2 :=
        Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (h_sq_le i) (by positivity)
      _ = (N : ℝ) * ((c ^ 2 / (N : ℝ)) / 2) := by simp [Finset.sum_const]
      _ = c ^ 2 / 2 := by
        field_simp
  exact Real.exp_le_exp_of_le h_sum_le

/-- The product of two `cosh`s of linear forms in the same Gaussian vector `w`, with a common
coefficient `c` and offset `h`, is the average of the `cosh` of the sum and of the difference. -/
theorem cosh_mul_cosh_sum_mul_eq {E : Type*} [Fintype E] (c h : ℝ) (s t w : E → ℝ) :
    Real.cosh (c * ∑ e, w e * s e + h) * Real.cosh (c * ∑ e, w e * t e + h) =
      (Real.cosh (∑ e, (c * (s e + t e)) * w e + 2 * h) +
        Real.cosh (∑ e, (c * (s e - t e)) * w e + 0)) / 2 := by
  rw [Real.cosh_mul_cosh]
  have h1 : ∑ e, (c * (s e + t e)) * w e = c * ∑ e, w e * s e + c * ∑ e, w e * t e := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have h2 : ∑ e, (c * (s e - t e)) * w e = c * ∑ e, w e * s e - c * ∑ e, w e * t e := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [h1, h2]
  congr 3 <;> ring_nf

/-- Integrability of a product of two `cosh`s of linear forms in independent Gaussians. -/
theorem integrable_cosh_mul_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c h : ℝ)
    (s t : E → ℝ) :
    Integrable (fun w : E → ℝ =>
        Real.cosh (c * ∑ e, w e * s e + h) * Real.cosh (c * ∑ e, w e * t e + h))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  simp_rw [cosh_mul_cosh_sum_mul_eq]
  exact ((integrable_cosh_sum_mul_gaussianReal _ _).add
    (integrable_cosh_sum_mul_gaussianReal _ _)).div_const 2

/-- Gaussian second moment of two `cosh`s of linear forms:
`𝔼 cosh (c ⟨w, s⟩ + h) cosh (c ⟨w, t⟩ + h)
  = (cosh (2h) exp (c² ∑ (s+t)²/2) + exp (c² ∑ (s-t)²/2)) / 2`. -/
theorem integral_cosh_mul_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c h : ℝ)
    (s t : E → ℝ) :
    ∫ w : E → ℝ, Real.cosh (c * ∑ e, w e * s e + h) * Real.cosh (c * ∑ e, w e * t e + h)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
      (Real.cosh (2 * h) * Real.exp (∑ e, (c * (s e + t e)) ^ 2 / 2) +
        Real.exp (∑ e, (c * (s e - t e)) ^ 2 / 2)) / 2 := by
  simp_rw [cosh_mul_cosh_sum_mul_eq]
  rw [integral_div, integral_add (integrable_cosh_sum_mul_gaussianReal _ _)
    (integrable_cosh_sum_mul_gaussianReal _ _), integral_cosh_sum_mul_gaussianReal,
    integral_cosh_sum_mul_gaussianReal, Real.cosh_zero]
  ring

/-- A coordinate of an i.i.d. standard Gaussian vector lies in every `L^p`. -/
theorem memLp_coord_pi_gaussianReal {n : ℕ} (i : Fin n) (p : NNReal) :
    MemLp (fun y : Fin n → ℝ => y i) p (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) p).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)

/-- An even power of an affine function of `∑ |yᵢ|` is integrable under the i.i.d. standard
Gaussian law. -/
theorem integrable_even_pow_const_mul_sum_abs_add {n : ℕ} (c d : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun y : Fin n → ℝ => (c * ∑ i, |y i| + d) ^ (2 * k))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hs : MemLp (fun y : Fin n → ℝ => ∑ i, |y i|) ((2 * k : ℕ) : NNReal)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    by
      have := memLp_finsetSum' (Finset.univ : Finset (Fin n))
        (fun i _ => (memLp_coord_pi_gaussianReal i ((2 * k : ℕ) : NNReal)).norm)
      simpa [Finset.sum_fn, Real.norm_eq_abs] using this
  have h1 := (hs.const_mul c).add (memLp_const d)
  have h2 := h1.integrable_norm_pow (by positivity : 2 * k ≠ 0)
  have he : Even (2 * k) := ⟨k, by ring⟩
  simpa [Real.norm_eq_abs, he.pow_abs] using h2
