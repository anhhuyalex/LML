/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Functoriality of unordered pairs for equivalences

`Sym2.map` is functorial; for an equivalence `e : α ≃ β` it is an equivalence
`Equiv.sym2Congr e : Sym2 α ≃ Sym2 β`, the unordered-pair analogue of `Equiv.prodCongr`
(and of `Sym.equivCongr` for symmetric powers).
-/

@[expose] public section

namespace Equiv

variable {α β : Type*}

/-- An equivalence `α ≃ β` induces an equivalence of unordered pairs `Sym2 α ≃ Sym2 β`. -/
def sym2Congr (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv c := Sym2.ind (fun x y => by simp [Sym2.map_mk]) c
  right_inv c := Sym2.ind (fun x y => by simp [Sym2.map_mk]) c

@[simp]
theorem sym2Congr_apply (e : α ≃ β) (c : Sym2 α) : sym2Congr e c = Sym2.map e c := rfl

@[simp]
theorem sym2Congr_symm (e : α ≃ β) : (sym2Congr e).symm = sym2Congr e.symm := rfl

end Equiv
