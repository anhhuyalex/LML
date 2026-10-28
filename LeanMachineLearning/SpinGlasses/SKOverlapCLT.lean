/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic

/-!
# The covariance function of the overlap fluctuations (Talagrand, Section 1.10)

For `β < 1/2` the fluctuations of the replica overlaps `X_{ℓ,ℓ'} = √N (R_{ℓ,ℓ'} - q)` are
asymptotically Gaussian (Talagrand, Theorem 1.10.1, Eq. (1.290)); the limiting covariance
of two pairs of replicas is determined by the `T`-basis limits `(A², B², C²)` of Section 1.8.  This
file contains only that covariance function, as a combinatorial formula.

**Preparation.** `SKCavityHigherOrder.lean` proves Eqs. (1.298)-(1.299) for products of
individual truncated centered overlaps with a bounded factor; `SKCavityHigherOrderPair.lean`
proves Lemma 1.10.2 for pure products. Products of arbitrary finite linear combinations,
Corollary 1.10.3 and the mixed-moment induction of Theorem 1.10.1 remain open.

An earlier version of this file declared statements with those names; they
were vacuous (an existential remainder chosen to be zero, or a hypothesis returned as the
conclusion) and have been removed.  A faithful statement needs the cavity expectation `ν₀` of
the book (a decoupled cavity average), the `T`-basis objects of Section 1.8, and replicas indexed
independently of the number of sites.

## Main declarations

* `SpinGlasses.skOverlapCov`: the covariance `A² 1_{p₁ = p₂} + B² |p₁ ∩ p₂| + C²`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.10.
-/

@[expose] public section


namespace SpinGlasses

/-- **The asymptotic overlap covariance function $\Sigma$** (Talagrand, Section 1.10):
Given the $T$-basis variances $A^2, B^2, C^2 \ge 0$, the covariance between two replica pairs
$p_1 = \{\ell_1, \ell_2\}$ and $p_2 = \{\ell_3, \ell_4\}$ is:
* $A^2 + 2B^2 + C^2$ if $p_1 = p_2$,
* $B^2 + C^2$ if $|p_1 \cap p_2| = 1$,
* $C^2$ if $p_1 \cap p_2 = \emptyset$. -/
def skOverlapCov (A2 B2 C2 : ℝ) {R : Type*} [DecidableEq R] (p₁ p₂ : Finset R) : ℝ :=
  (if p₁ = p₂ then A2 else 0) +
  (p₁ ∩ p₂).card * B2 +
  C2

@[simp] theorem skOverlapCov_self {R : Type*} [DecidableEq R] (A2 B2 C2 : ℝ)
    {p : Finset R} (hp : p.card = 2) :
    skOverlapCov A2 B2 C2 p p = A2 + 2 * B2 + C2 := by
  simp only [skOverlapCov, Finset.inter_self, hp, ↓reduceIte]
  push_cast
  ring

@[simp] theorem skOverlapCov_disjoint {R : Type*} [DecidableEq R] (A2 B2 C2 : ℝ)
    {p₁ p₂ : Finset R} (hdisj : Disjoint p₁ p₂) (hp1 : p₁.card = 2) :
    skOverlapCov A2 B2 C2 p₁ p₂ = C2 := by
  have hne : p₁ ≠ p₂ := by
    rintro rfl
    have : (p₁ ∩ p₁).card = 0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
    rw [Finset.inter_self, hp1] at this
    norm_num at this
  simp only [skOverlapCov, hne, ↓reduceIte]
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
  push_cast
  ring

end SpinGlasses
