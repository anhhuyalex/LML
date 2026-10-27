/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.PointwiseLimitKink
public import LeanMachineLearning.SpinGlasses.SKCoupledSeparation

/-!
# Conditional form of Talagrand's Theorem 1.9.6

The coupled free energies `ψ_M` are convex (`convexOn_skCoupledFreeEnergy`), differentiable with
derivative `𝔼 ⟨R₁,₂⟩_λ` (`hasDerivAt_skCoupledFreeEnergy`), and beyond the AT line their
derivatives at `λ` and `-λ` stay a fixed distance apart for large `M`
(`sk_coupled_derivative_separation`).  Hence any pointwise limit of `ψ_{N+1}` is not
differentiable at `0`.  The existence of the limit is **not** proved here; it is an explicit
hypothesis, as in the book, which takes it from the literature.

## Main declaration

* `SpinGlasses.sk_coupled_limit_not_differentiableAt`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.9.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SpinGlasses

/-- **Theorem 1.9.6, conditional on the existence of the limit.**  Let `h ≠ 0`, let `q` be a fixed
point (1.74) with the tanh-fourth-moment `q̂`, and assume `β² (1 - 2q + q̂) > 1`.  If
`ψ_{N+1}(λ) = skCoupledFreeEnergy (N + 1) β h λ` converges to `ψ λ` for every `λ` in a
neighbourhood `(-r, r)` of `0`, then `ψ` is not differentiable at `0`. -/
theorem sk_coupled_limit_not_differentiableAt (β h q qhat : ℝ) (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) {r : ℝ} (hr : 0 < r) {ψ : ℝ → ℝ}
    (hlim : ∀ lam ∈ Ioo (-r) r,
      Tendsto (fun N : ℕ => skCoupledFreeEnergy (N + 1) β h lam) atTop (𝓝 (ψ lam))) :
    ¬ DifferentiableAt ℝ ψ 0 := by
  obtain ⟨δ', hδ', hsep⟩ := sk_coupled_derivative_separation β h q qhat hh hfix hqhat hAT
  refine not_differentiableAt_of_convexOn_tendsto_of_derivative_gap (c := δ' / 2) hr
    (by positivity) (fun N => (convexOn_skCoupledFreeEnergy (N + 1) β h).subset (subset_univ _)
      (convex_Ioo _ _))
    (fun N x _ => hasDerivAt_skCoupledFreeEnergy (N + 1) β h x) hlim ?_
  intro lam hlam
  obtain ⟨N₀, hN₀⟩ := hsep lam hlam.1
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact hN₀ N hN

end SpinGlasses
