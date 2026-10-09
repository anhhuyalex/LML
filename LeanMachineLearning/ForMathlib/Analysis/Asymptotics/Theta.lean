/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Asymptotics.Theta

/-!
# Two-sided asymptotic equivalence: powers and quotients

Mathlib has `Asymptotics.IsBigO.of_pow` but no two-sided counterpart, and no statement that
`f =Θ g` is the same as `f / g =Θ 1`.  These are the two reductions used to turn a scaling law for a
squared, normalized quantity into a relation between the underlying scales.

## Main declarations

* `Asymptotics.isTheta_pow_iff`: `f ^ n =Θ g ^ n ↔ f =Θ g` for `n ≠ 0`.
* `Asymptotics.isTheta_iff_div_isTheta_one`: `f =Θ g ↔ f / g =Θ 1` when `g` is eventually nonzero.
* `Asymptotics.isTheta_sq_div_one_iff`: the composite `(f / g) ^ 2 =Θ 1 ↔ f =Θ g`.
-/

@[expose] public section

open Filter

namespace Asymptotics

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α}

/-- `f ^ n =Θ g ^ n` is equivalent to `f =Θ g` for `n ≠ 0`. -/
theorem isTheta_pow_iff {f g : α → 𝕜} {n : ℕ} (hn : n ≠ 0) :
    (fun x => f x ^ n) =Θ[l] (fun x => g x ^ n) ↔ f =Θ[l] g :=
  ⟨fun h => ⟨IsBigO.of_pow hn h.1, IsBigO.of_pow hn h.2⟩, fun h => h.pow n⟩

/-- `f =Θ g` is equivalent to `f / g =Θ 1` when `g` is eventually nonzero. -/
theorem isTheta_iff_div_isTheta_one {f g : α → 𝕜} (hg : ∀ᶠ x in l, g x ≠ 0) :
    f =Θ[l] g ↔ (fun x => f x / g x) =Θ[l] (fun _ => (1 : 𝕜)) := by
  have hgg : (fun x => g x / g x) =ᶠ[l] fun _ => (1 : 𝕜) :=
    hg.mono fun x hx => div_self hx
  have hfg : (fun x => f x / g x * g x) =ᶠ[l] f :=
    hg.mono fun x hx => div_mul_cancel₀ (f x) hx
  constructor
  · exact fun h => (h.div (isTheta_refl g l)).trans_eventuallyEq hgg
  · exact fun h => hfg.symm.trans_isTheta
      ((h.mul (isTheta_refl g l)).trans_eventuallyEq (Eventually.of_forall fun x => one_mul (g x)))

/-- `(f / g) ^ 2 =Θ 1` if and only if `f =Θ g` when `g` is eventually nonzero. -/
theorem isTheta_sq_div_one_iff {f g : α → 𝕜} (hg : ∀ᶠ x in l, g x ≠ 0) :
    (fun x => (f x / g x) ^ 2) =Θ[l] (fun _ => (1 : 𝕜)) ↔ f =Θ[l] g := by
  rw [isTheta_iff_div_isTheta_one hg]
  simpa using isTheta_pow_iff (l := l) (f := fun x => f x / g x) (g := fun _ => (1 : 𝕜))
    two_ne_zero

end Asymptotics
