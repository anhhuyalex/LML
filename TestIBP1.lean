import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

open MeasureTheory ProbabilityTheory Filter Topology Set
namespace MeasureTheory

/-- Pointwise derivative of `z ↦ u'(S₀ + c * z) * exp (u (S₀ + c * z))`. -/
theorem hasDerivAt_deriv_u_mul_exp_affine {u : ℝ → ℝ} {u' u'' : ℝ → ℝ}
    (hu' : ∀ x, HasDerivAt u (u' x) x) (hu'' : ∀ x, HasDerivAt u' (u'' x) x)
    (S₀ c z : ℝ) :
    HasDerivAt (fun t => u' (S₀ + c * t) * Real.exp (u (S₀ + c * t)))
      (c * (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) * Real.exp (u (S₀ + c * z))) z := by
  have hS : HasDerivAt (fun t => S₀ + c * t) c z := by
    simpa using (hasDerivAt_id z).const_mul c |>.const_add S₀
  have h1 : HasDerivAt (fun t => u' (S₀ + c * t)) (u'' (S₀ + c * z) * c) z :=
    (hu'' (S₀ + c * z)).comp z hS
  have h2 : HasDerivAt (fun t => Real.exp (u (S₀ + c * t)))
      (Real.exp (u (S₀ + c * z)) * (u' (S₀ + c * z) * c)) z := by
    simpa only [Function.comp_def] using ((hu' (S₀ + c * z)).comp z hS).exp
  have hprod := h1.mul h2
  convert hprod using 1
  ring

/-- **Gaussian integration by parts for a 1D potential:**
`𝔼 [g u'(S₀ + c g) e^{u(S₀ + c g)}] = v c 𝔼 [(u''(S₀ + c g) + (u'(S₀ + c g))²) e^{u(S₀ + c g)}]`
for `g ~ 𝒩(0, v)`. -/
theorem integral_id_mul_deriv_u_mul_exp_affine_gaussianReal (v : NNReal)
    {u u' u'' : ℝ → ℝ}
    (hu' : ∀ x, HasDerivAt u (u' x) x) (hu'' : ∀ x, HasDerivAt u' (u'' x) x)
    {B D D₂ : ℝ} (hB : ∀ x, u x ≤ B) (hD : ∀ x, |u' x| ≤ D) (hD₂ : ∀ x, |u'' x| ≤ D₂)
    (S₀ c : ℝ) :
    ∫ z, z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))) ∂gaussianReal 0 v =
      (v : ℝ) * c * ∫ z, (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
        Real.exp (u (S₀ + c * z)) ∂gaussianReal 0 v := by
  let F := fun t => u' (S₀ + c * t) * Real.exp (u (S₀ + c * t))
  let F' := fun t => c * (u'' (S₀ + c * t) + (u' (S₀ + c * t)) ^ 2) * Real.exp (u (S₀ + c * t))
  have hF' : ∀ z, HasDerivAt F (F' z) z := fun z =>
    hasDerivAt_deriv_u_mul_exp_affine hu' hu'' S₀ c z
  have hmF : Continuous F := continuous_iff_continuousAt.2 fun x => (hF' x).continuousAt
  have hmF' : Measurable F' := by
    have hcu : Continuous u := continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt
    have hmu : Measurable u := hcu.measurable
    have hdu : Measurable u' := by
      have heq : u' = deriv u := funext fun x => (hu' x).deriv.symm
      rw [heq]
      exact measurable_deriv u
    have hdu' : Measurable u'' := by
      have heq : u'' = deriv u' := funext fun x => (hu'' x).deriv.symm
      rw [heq]
      exact measurable_deriv u'
    dsimp only [F']
    fun_prop
  have hbF (z : ℝ) : |F z| ≤ |D| * Real.exp B := by
    dsimp only [F]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul ((hD _).trans (le_abs_self _)) (Real.exp_le_exp.mpr (hB _))
      (Real.exp_pos _).le (abs_nonneg _)
  have hbF' (z : ℝ) : |F' z| ≤ |c| * (|D₂| + D ^ 2) * Real.exp B := by
    dsimp only [F']
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hsum : |u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2| ≤ |D₂| + D ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ((hD₂ _).trans (le_abs_self _)) ?_)
      rw [sq, abs_mul]
      have hDpos : 0 ≤ |D| := abs_nonneg _
      calc |u' (S₀ + c * z)| * |u' (S₀ + c * z)|
        _ ≤ D * D := mul_le_mul (hD _) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hD _))
        _ = D ^ 2 := (sq D).symm
    exact mul_le_mul (mul_le_mul le_rfl hsum (abs_nonneg _) (abs_nonneg _))
      (Real.exp_le_exp.mpr (hB _)) (Real.exp_pos _).le (by positivity)
  have hG1 : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) := by
    have h : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 v) := memLp_id_gaussianReal 1
    exact h.integrable le_rfl
  have hxF : Integrable (fun z => z * F z) (gaussianReal 0 v) := by
    have heq : (fun z => z * F z) = (fun z => F z * z) := by ext z; ring
    rw [heq]
    exact hG1.bdd_mul hmF.measurable.aestronglyMeasurable (ae_of_all _ hbF)
  have hiF' : Integrable F' (gaussianReal 0 v) :=
    integrable_of_measurable_bound hmF' (M := |c| * (|D₂| + D ^ 2) * Real.exp B)
      (fun z => hbF' z)
  have hstein := integral_id_mul_gaussianReal_eq v hF' hxF hiF'
  have heq_c : (∫ z, F' z ∂gaussianReal 0 v) =
      c * ∫ z, (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
        Real.exp (u (S₀ + c * z)) ∂gaussianReal 0 v := by
    dsimp only [F']
    have hmul : (fun t => c * (u'' (S₀ + c * t) + (u' (S₀ + c * t)) ^ 2) *
        Real.exp (u (S₀ + c * t))) =
        fun t => c * ((u'' (S₀ + c * t) + (u' (S₀ + c * t)) ^ 2) *
        Real.exp (u (S₀ + c * t))) := by ext t; ring
    rw [hmul, integral_const_mul]
  rw [hstein, heq_c]
  ring

end MeasureTheory
