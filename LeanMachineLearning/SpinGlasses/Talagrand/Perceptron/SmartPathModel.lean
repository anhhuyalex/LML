/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.TiltedSmul
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GibbsAverages

/-!
# The perceptron smart path: the named objects

Talagrand Section 2.2, (2.15)--(2.16) and (2.27)--(2.28). A configuration is a pair of a spin
`σ = (old spins, last spin)` and the auxiliary Gaussian vector `ξ`; the quenched disorder is
`ω = ((g, a), y)` (old rows, last disorder coordinates, last field). These objects occur in every
statement about the path, so they are defined once here:

* the types `PerceptronSpin`, `SmartPathState`, `SmartPathDisorder`;
* the field `smartPathField`, the energy `smartPathEnergy` and the three pieces of its derivative
  `smartPathEnergyDerivA`, `smartPathEnergyDerivXi`, `smartPathEnergyDerivY`;
* the path without auxiliary spins `smartPathFieldNoAux`, `smartPathEnergyNoAux`;
* the laws `smartPathBase` and `smartPathDisorder`;
* the potential hypotheses `SmartPathPotential` and `SmartPathPotential₂`;
* the two interaction kernels of Proposition 2.2.3.

The Gibbs measure is not given a name: it is `(smartPathBase N M).tilted (smartPathEnergy u s ω)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- The cast `ℤˣ → ℝ` of a spin is measurable. -/
@[fun_prop]
theorem measurable_units_cast : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) :=
  measurable_of_countable _

/-! ### Types -/

/-- Old spins and the last spin. -/
abbrev PerceptronSpin (N : ℕ) := (Fin N → ℤˣ) × ℤˣ

/-- The smart-path configuration: spins and the auxiliary Gaussian coordinates `ξ`. -/
abbrev SmartPathState (N M : ℕ) := PerceptronSpin N × (Fin M → ℝ)

/-- Quenched disorder `((g, a), y)`. -/
abbrev SmartPathDisorder (N M : ℕ) := ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ

/-! ### Fields, energies and the energy derivative -/

/-- The smart-path field without auxiliary spins (Talagrand (2.14)). -/
noncomputable def smartPathFieldNoAux {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (k : Fin M) : ℝ :=
  (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
    Real.sqrt (s / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ)

/-- The smart-path field `S_{k,s}` of (2.15): the field without auxiliary spins plus the
auxiliary term `√((1 - s) / (N + 1)) ξ_k`. -/
noncomputable def smartPathField {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (k : Fin M) : ℝ :=
  smartPathFieldNoAux s ω x k + Real.sqrt ((1 - s) / (N + 1)) * x.2 k

/-- The smart-path energy `-H_{N,M,s}` of (2.16). -/
noncomputable def smartPathEnergy {N M : ℕ} (u : ℝ → ℝ) (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (smartPathField s ω x k)

/-- The energy of the path without auxiliary spins (Talagrand (2.14)). -/
noncomputable def smartPathEnergyNoAux {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 + ∑ k, u (smartPathFieldNoAux s ω x k)

/-- The quenched-disorder (`a`) component of the derivative (2.27) of the energy. -/
noncomputable def smartPathEnergyDerivA {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ∑ k, deriv u (smartPathField s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
    (ω.1.2 k * ((x.1.2 : ℤ) : ℝ) / Real.sqrt s))

/-- The auxiliary-coordinate (`ξ`) component of the derivative (2.27) of the energy. -/
noncomputable def smartPathEnergyDerivXi {N M : ℕ} (u : ℝ → ℝ) (s : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) : ℝ :=
  ∑ k, deriv u (smartPathField s ω x k) * ((1 / (2 * Real.sqrt (N + 1 : ℕ))) *
    (- x.2 k / Real.sqrt (1 - s)))

/-- The last-field (`Y`) component of the derivative (2.27) of the energy. -/
noncomputable def smartPathEnergyDerivY {N M : ℕ} (s : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) : ℝ :=
  -((x.1.2 : ℤ) : ℝ) * ω.2 / (2 * Real.sqrt (1 - s))

/-! ### Measurability -/

section Measurability

variable {N M : ℕ}

@[fun_prop]
theorem measurable_smartPathFieldNoAux (s : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathFieldNoAux s p.1 p.2 k := by
  unfold smartPathFieldNoAux
  fun_prop

@[fun_prop]
theorem measurable_smartPathField (s : ℝ) (k : Fin M) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathField s p.1 p.2 k := by
  unfold smartPathField
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergy {u : ℝ → ℝ} (hu : Measurable u) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergy u s p.1 p.2 := by
  unfold smartPathEnergy
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyNoAux {u : ℝ → ℝ} (hu : Measurable u) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergyNoAux u s p.1 p.2 := by
  unfold smartPathEnergyNoAux
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyDerivA (u : ℝ → ℝ) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergyDerivA u s p.1 p.2 := by
  have hdu := measurable_deriv u
  unfold smartPathEnergyDerivA
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyDerivXi (u : ℝ → ℝ) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergyDerivXi u s p.1 p.2 := by
  have hdu := measurable_deriv u
  unfold smartPathEnergyDerivXi
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyDerivY (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergyDerivY s p.1 p.2 := by
  unfold smartPathEnergyDerivY
  fun_prop

/-- The energy for a fixed disorder is measurable in the configuration. -/
theorem measurable_smartPathEnergy_slice {u : ℝ → ℝ} (hu : Measurable u) (s : ℝ)
    (ω : SmartPathDisorder N M) :
    Measurable (smartPathEnergy u s ω) :=
  (measurable_smartPathEnergy hu s).comp (measurable_const.prodMk measurable_id)

/-- The energy derivative `E'_a + E'_ξ + E'_Y` is jointly measurable in the disorder and the
configuration. -/
theorem measurable_smartPathEnergyDeriv (u : ℝ → ℝ) (s : ℝ) :
    Measurable fun p : SmartPathDisorder N M × SmartPathState N M =>
      smartPathEnergyDerivA u s p.1 p.2 + smartPathEnergyDerivXi u s p.1 p.2 +
        smartPathEnergyDerivY s p.1 p.2 :=
  ((measurable_smartPathEnergyDerivA u s).add (measurable_smartPathEnergyDerivXi u s)).add
    (measurable_smartPathEnergyDerivY s)

@[fun_prop]
theorem measurable_smartPathEnergyDerivA_slice (u : ℝ → ℝ) (s : ℝ) (ω : SmartPathDisorder N M) :
    Measurable (smartPathEnergyDerivA u s ω) := by
  have hdu := measurable_deriv u
  unfold smartPathEnergyDerivA smartPathField smartPathFieldNoAux
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyDerivXi_slice (u : ℝ → ℝ) (s : ℝ) (ω : SmartPathDisorder N M) :
    Measurable (smartPathEnergyDerivXi u s ω) := by
  have hdu := measurable_deriv u
  unfold smartPathEnergyDerivXi smartPathField smartPathFieldNoAux
  fun_prop

@[fun_prop]
theorem measurable_smartPathEnergyDerivY_slice (s : ℝ) (ω : SmartPathDisorder N M) :
    Measurable (smartPathEnergyDerivY s ω) := by
  unfold smartPathEnergyDerivY
  fun_prop

/-- The energy derivative for a fixed disorder is measurable in the configuration. -/
theorem measurable_smartPathEnergyDeriv_slice (u : ℝ → ℝ) (s : ℝ) (ω : SmartPathDisorder N M) :
    Measurable fun x : SmartPathState N M => smartPathEnergyDerivA u s ω x +
      smartPathEnergyDerivXi u s ω x + smartPathEnergyDerivY s ω x :=
  ((measurable_smartPathEnergyDerivA_slice u s ω).add
    (measurable_smartPathEnergyDerivXi_slice u s ω)).add
    (measurable_smartPathEnergyDerivY_slice s ω)

end Measurability

/-! ### Laws -/

/-- Counting measure on spins times standard Gaussian auxiliary coordinates. -/
noncomputable def smartPathBase (N M : ℕ) : Measure (SmartPathState N M) :=
  (Measure.count : Measure (PerceptronSpin N)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)

instance (N M : ℕ) : IsFiniteMeasure (smartPathBase N M) := by
  unfold smartPathBase; infer_instance

instance (N M : ℕ) : NeZero (smartPathBase N M) := by
  unfold smartPathBase; infer_instance

theorem count_univ_ne_zero (N : ℕ) :
    (Measure.count : Measure (PerceptronSpin N)) Set.univ ≠ 0 := by
  simp

theorem count_univ_ne_top (N : ℕ) : (Measure.count : Measure (PerceptronSpin N)) Set.univ ≠ ⊤ :=
  measure_ne_top _ _

/-- The spin counting measure normalized to a probability measure. -/
noncomputable def smartPathSpinProb (N : ℕ) : Measure (PerceptronSpin N) :=
  ((Measure.count : Measure (PerceptronSpin N)) Set.univ)⁻¹ •
    (Measure.count : Measure (PerceptronSpin N))

instance (N : ℕ) : IsProbabilityMeasure (smartPathSpinProb N) :=
  ⟨by
    unfold smartPathSpinProb
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (count_univ_ne_zero N) (count_univ_ne_top N)⟩

/-- The smart-path base law with the spin counting measure normalized to a probability measure. -/
noncomputable def smartPathBaseProb (N M : ℕ) : Measure (SmartPathState N M) :=
  (smartPathSpinProb N).prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)

instance (N M : ℕ) : IsProbabilityMeasure (smartPathBaseProb N M) := by
  unfold smartPathBaseProb
  infer_instance

theorem smartPathBase_eq_smul (N M : ℕ) :
    smartPathBase N M =
      ((Measure.count : Measure (PerceptronSpin N)) Set.univ) • smartPathBaseProb N M := by
  unfold smartPathBase smartPathBaseProb smartPathSpinProb
  rw [Measure.prod_smul_left, smul_smul, ENNReal.mul_inv_cancel (count_univ_ne_zero N)
    (count_univ_ne_top N), one_smul]

/-- The Gibbs measure does not depend on the scale of the spin counting measure. -/
theorem smartPathBase_tilted_eq (N M : ℕ) (E : SmartPathState N M → ℝ) :
    (smartPathBase N M).tilted E = (smartPathBaseProb N M).tilted E := by
  rw [smartPathBase_eq_smul, tilted_smul _ _ (count_univ_ne_zero N) (count_univ_ne_top N)]

/-- Quenched disorder law: old rows `Pold`, standard Gaussian `a`, and `y ∼ 𝒩(0, v)`. -/
noncomputable def smartPathDisorder {N M : ℕ} (Pold : Measure (Fin M → Fin N → ℝ))
    (v : ℝ≥0) : Measure (SmartPathDisorder N M) :=
  (Pold.prod (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod (gaussianReal 0 v)

instance {N M : ℕ} (Pold : Measure (Fin M → Fin N → ℝ)) [IsFiniteMeasure Pold] (v : ℝ≥0) :
    IsFiniteMeasure (smartPathDisorder Pold v) := by
  unfold smartPathDisorder; infer_instance

/-! ### Potential hypotheses -/

/-- The potential hypotheses of (2.7) used by the smart-path derivative: differentiable,
`|u| ≤ B`, `|u'| ≤ D`. -/
structure SmartPathPotential (u : ℝ → ℝ) (B D : ℝ) : Prop where
  differentiable : Differentiable ℝ u
  abs_le : ∀ z, |u z| ≤ B
  abs_deriv_le : ∀ z, |deriv u z| ≤ D

namespace SmartPathPotential

variable {u : ℝ → ℝ} {B D : ℝ}

theorem continuous (h : SmartPathPotential u B D) : Continuous u := h.differentiable.continuous

theorem measurable (h : SmartPathPotential u B D) : Measurable u := h.continuous.measurable

theorem le (h : SmartPathPotential u B D) (z : ℝ) : u z ≤ B := le_of_abs_le (h.abs_le z)

theorem B_nonneg (h : SmartPathPotential u B D) : 0 ≤ B := (abs_nonneg _).trans (h.abs_le 0)

theorem D_nonneg (h : SmartPathPotential u B D) : 0 ≤ D :=
  (abs_nonneg _).trans (h.abs_deriv_le 0)

end SmartPathPotential

/-- Extension of `SmartPathPotential` requiring `deriv u` to be differentiable with
its derivative `u''` bounded by `D₂`. -/
structure SmartPathPotential₂ (u : ℝ → ℝ) (B D D₂ : ℝ) : Prop extends
    SmartPathPotential u B D where
  differentiable_deriv : Differentiable ℝ (deriv u)
  abs_deriv₂_le : ∀ z, |deriv (deriv u) z| ≤ D₂

/-! ### Interaction kernels of Proposition 2.2.3 -/

/-- Cross-replica interaction kernel of potential derivatives, (2.24):
`ε_x ε_y u'(S_{k,t}(x)) u'(S_{k,t}(y))`. -/
noncomputable def smartPathPotentialKernel {N M : ℕ} (u : ℝ → ℝ) (t : ℝ)
    (ω : SmartPathDisorder N M) (k : Fin M) (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ) * deriv u (smartPathField t ω x k) *
    deriv u (smartPathField t ω y k)

/-- Last-spin interaction kernel, (2.25): `ε_x ε_y`. -/
def lastSpinKernel {N M : ℕ} (x y : SmartPathState N M) : ℝ :=
  ((x.1.2 : ℤ) : ℝ) * ((y.1.2 : ℤ) : ℝ)

theorem lastSpinKernel_self {N M : ℕ} (x : SmartPathState N M) : lastSpinKernel x x = 1 := by
  unfold lastSpinKernel
  rw [← sq]
  exact units_cast_sq _

theorem lastSpinKernel_comm {N M : ℕ} (x y : SmartPathState N M) :
    lastSpinKernel x y = lastSpinKernel y x := by
  unfold lastSpinKernel
  ring

end SpinGlasses
