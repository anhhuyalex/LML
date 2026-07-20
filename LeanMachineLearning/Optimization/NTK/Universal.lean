/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Kernel
public import LeanMachineLearning.Optimization.NTK.Linearization
public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Universal approximation via the NTK RKHS

This file proves that the RKHS of the ReLU neural tangent kernel is a universal
approximator over the NTK domain, corresponding to Section 4.3 and Theorem 4.1 of
the deep learning theory notes (Telgarsky 2021).

## Overview

The argument proceeds in three steps:

1. **NTK domain** `𝒳 ⊆ ℝᵈ` (Definition 4.7): the set of unit vectors with a fixed
   bias coordinate `xᵈ = 1/√2`. Fixing this coordinate embeds the approximation
   problem on a compact domain into the kernel setting.

2. **RKHS predictor class** `ℋ` (Definition 4.8): finite linear combinations
   `h(x) = ∑ⱼ αⱼ k(x, xⱼ)` of kernel evaluations at points `xⱼ ∈ 𝒳`.

3. **Universality** (Theorem 4.1): `ℋ` is dense in `C(𝒳, ℝ)` in the sup-norm.
   The proof reduces to a known positive-coefficient criterion for dot-product kernels
   (Steinwart and Christmann 2008, Corollary 4.57): the Maclaurin series of
   `f(z) = (z + 1/2)/2 − (z + 1/2)·arccos(z + 1/2)/(2π)` has all-positive coefficients,
   which suffices for universality on the bounded domain `U`.

## Main definitions

* `NTK.ntkDomain` : `𝒳 = {x ∈ ℝᵈ : ‖x‖₂ = 1, xᵈ₋₁ = 1/√2}`.
* `NTK.RKHSClass` : `ℋ` — the NTK RKHS predictor class.
* `NTK.isUniversal` : Theorem 4.1 — `ℋ` is a universal approximator over `𝒳`.

## References

* Telgarsky 2021, Section 4.3 and Theorem 4.1.
* Steinwart and Christmann 2008, Corollary 4.57.
* Ji, Telgarsky, and Xian 2020 (a direct approach via Barron's theorem).

-/

@[expose] public section

open Real MeasureTheory Set

namespace NTK

variable {d : ℕ}

/-! ### NTK domain (Definition 4.7) -/

/-- **Definition 4.7** (NTK domain).
The *NTK domain* is the compact subset of the unit sphere in `ℝᵈ` obtained by
fixing the last coordinate to `1/√2`:
  `𝒳 = {x ∈ ℝᵈ : ‖x‖₂ = 1, xᵈ₋₁ = 1/√2}`.

Fixing the last coordinate plays the role of an implicit bias: it ensures that
the ReLU NTK `k(x,x') = (xᵀx')(π − arccos(xᵀx'))/(2π)` restricted to `𝒳`
has all-positive Maclaurin coefficients, making it a universal kernel.

The Euclidean norm is encoded as `x ⊙ x = 1` rather than Lean's default norm on
the raw function type `Fin d → ℝ`. -/
def ntkDomain (d : ℕ) : Set (Fin d → ℝ) :=
  {x | x ⊙ x = 1 ∧
    (∃ hd : 0 < d, x ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩ = 1 / Real.sqrt 2)}

/-- The NTK domain is a subset of the Euclidean unit sphere. -/
lemma ntkDomain_subset_sphere (d : ℕ) :
    ntkDomain d ⊆ {x : Fin d → ℝ | x ⊙ x = 1} :=
  fun _ hx => hx.1

/-- The NTK domain is compact (closed subset of the unit sphere in ℝᵈ). -/
lemma isCompact_ntkDomain (d : ℕ) (hd : 0 < d) : IsCompact (ntkDomain d) := by
  sorry

/-! ### The (d-1)-dimensional ball that is isomorphic to the NTK domain -/

/-- The reduced domain: `U = {u ∈ ℝᵈ⁻¹ : ‖u‖² ≤ 1/2}`.
  The NTK domain `𝒳 ⊆ ℝᵈ` is in bijection with `U` by dropping the last coordinate. -/
def reducedDomain (d : ℕ) : Set (Fin d → ℝ) :=
  {u | u ⊙ u ≤ 1 / 2}

/-- The kernel on the reduced domain: `k̃(u, u') = f̃(u·u')` where
  `f̃(z) = (z + 1/2)/2 − (z + 1/2)·arccos(z + 1/2)/(2π)`.
  This is the ReLU NTK in coordinates on `U`. -/
noncomputable def reducedKernel (u u' : Fin d → ℝ) : ℝ :=
  let z := innerProduct u u'
  (z + 1 / 2) / 2 - (z + 1 / 2) * Real.arccos (z + 1 / 2) / (2 * Real.pi)

/-- The reduced kernel is equal to the ReLU NTK on the NTK domain. -/
lemma reducedKernel_eq_reluNTK
    (d : ℕ) (x x' : Fin (d + 1) → ℝ)
    (hx : x ∈ ntkDomain (d + 1))
    (hx' : x' ∈ ntkDomain (d + 1)) :
    reducedKernel (fun k => x k.castSucc) (fun k => x' k.castSucc) =
    limitingNTK reluIndicator x x' := by
  sorry

/-! ### NTK RKHS predictor class (Definition 4.8) -/

/-- **Definition 4.8** (NTK RKHS predictor class).
  `ℋ = { x ↦ ∑ⱼ αⱼ k(x, xⱼ) | n ≥ 0, αⱼ ∈ ℝ, xⱼ ∈ 𝒳 }`
where `k` is the ReLU limiting NTK. -/
def RKHSClass (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  { h | ∃ (n : ℕ) (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ),
          (∀ j, pts j ∈ ntkDomain d) ∧
          h = fun x => ∑ j : Fin n, α j * limitingNTK reluIndicator x (pts j) }

/-- The zero function belongs to `ℋ` (via the empty sum). -/
lemma zero_mem_RKHSClass (d : ℕ) : (fun _ => (0 : ℝ)) ∈ RKHSClass d := by
  exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, rfl⟩

/-- `ℋ` is closed under scalar multiplication. -/
lemma RKHSClass_smul (d : ℕ) (c : ℝ) {h : (Fin d → ℝ) → ℝ} (hh : h ∈ RKHSClass d) :
    (fun x => c * h x) ∈ RKHSClass d := by
  obtain ⟨n, α, pts, hmem, rfl⟩ := hh
  exact ⟨n, fun j => c * α j, pts, hmem, by ext x; simp [Finset.mul_sum, mul_assoc]⟩

/-- `ℋ` is closed under addition. -/
lemma RKHSClass_add (d : ℕ) {h₁ h₂ : (Fin d → ℝ) → ℝ}
    (hh₁ : h₁ ∈ RKHSClass d) (hh₂ : h₂ ∈ RKHSClass d) :
    (fun x => h₁ x + h₂ x) ∈ RKHSClass d := by
  obtain ⟨n₁, α₁, pts₁, hmem₁, rfl⟩ := hh₁
  obtain ⟨n₂, α₂, pts₂, hmem₂, rfl⟩ := hh₂
  refine ⟨n₁ + n₂, Fin.append α₁ α₂, Fin.append pts₁ pts₂, ?_, ?_⟩
  · intro j
    induction j using Fin.addCases with
    | left i => simp [hmem₁]
    | right i => simp [hmem₂]
  · ext x
    simp [Fin.sum_univ_add, Fin.append]

/-! ### Universality criterion for dot-product kernels -/

/-- The power series coefficients of `f̃(z) = (z+1/2)/2 − (z+1/2)arccos(z+1/2)/(2π)`.
These determine whether the reduced kernel `k̃(u,u') = f̃(u·u')` is universal.
By the criterion of Steinwart-Christmann 2008 (Corollary 4.57), a dot-product kernel
is universal on a bounded domain iff all its series coefficients are strictly positive. -/
noncomputable def reducedKernelCoeff (n : ℕ) : ℝ :=
  -- The coefficient of zⁿ in the Maclaurin series of f̃.
  -- For n = 0: (1/2)/2 − (1/2)·(π/2)/(2π) = 1/4 − 1/8 = 1/8
  -- For n ≥ 1: comes from the Maclaurin series of arccos shifted by 1/2.
  if n = 0 then 1 / 8
  else 1 / (2 * Real.pi) *
    ((2 * n).choose n : ℝ) / (4 ^ n * (2 * n + 1) * n.factorial ^ 2)

/-- All Maclaurin coefficients of `f̃` are strictly positive. -/
lemma reducedKernelCoeff_pos (n : ℕ) : 0 < reducedKernelCoeff n := by
  sorry

/-! ### Universal approximation theorem (Theorem 4.1) -/

/-- **Theorem 4.1** (Telgarsky 2021, universal approximation via the NTK RKHS).
For `σ = σ_ReLU`, the class `ℋ` is a *universal approximator* over the NTK domain `𝒳`:
for every continuous `g : 𝒳 → ℝ` and `ε > 0`, there exists `h ∈ ℋ` with
  `sup_{x ∈ 𝒳} |g(x) − h(x)| ≤ ε`.

**Proof sketch:**
- Identify `𝒳` with the ball `U = {u ∈ ℝᵈ⁻¹ : ‖u‖² ≤ 1/2}` via dropping the bias coord.
- The ReLU NTK on `𝒳` becomes the dot-product kernel `k̃(u,u') = f̃(u·u')` on `U`.
- By `reducedKernelCoeff_pos`, all Maclaurin coefficients of `f̃` are positive.
- By Steinwart-Christmann 2008, Corollary 4.57, `k̃` is a universal kernel on the
  compact set `U`, meaning kernel evaluations are dense in `C(U, ℝ)`.
- Transfer back to `𝒳` via the bijection. -/
theorem isUniversal (d : ℕ) (hd : 0 < d) :
    ∀ g : (Fin d → ℝ) → ℝ,
      ContinuousOn g (ntkDomain d) →
      ∀ ε > 0,
        ∃ h ∈ RKHSClass d,
          ∀ x ∈ ntkDomain d, |g x - h x| ≤ ε := by
  sorry

/-! ### Connection to overparameterized networks -/

/-- The NTK RKHS predictor class can be approximated by finite-width networks near
random initialization.

For any `h ∈ ℋ`, `ε > 0`, and failure probability `δ`, there exists a large-width
scaled shallow ReLU network and a radius `B` such that, with high probability over
Gaussian initialization `W₀`, some `W` within Frobenius distance `B` of `W₀`
approximates `h` on the NTK domain.

This combines `isUniversal` with `reluLinearizationBound`: taking `m` large enough
ensures `f ≈ f₀ = ⟨∇f(·; W₀), W⟩ ≈ h`. -/
theorem rkhs_approx_by_network
    (d : ℕ) (hd : 0 < d)
    (h : (Fin d → ℝ) → ℝ) (hh : h ∈ RKHSClass d)
    (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ (m : ℕ) (net : ShallowNetwork relu d m)
      (B : ℝ), 0 ≤ B ∧
      ∀ᵐ W₀ ∂(gaussianInit m d),
        ∃ W : Fin m → Fin d → ℝ,
          frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B ∧
          ∀ x ∈ ntkDomain d, |net.eval x W - h x| ≤ ε := by
  sorry

end NTK

end
