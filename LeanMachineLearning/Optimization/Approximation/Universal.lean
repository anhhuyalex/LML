/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Universal approximation theorem (Hornik-Stinchcombe-White 1989)

This file formalizes the universal approximation results of Chapter 2, Section 2.2.
The key steps are:

1. Show that the cosine and exponential function classes are closed under multiplication,
   making them subalgebras of C(S, ℝ).
2. Apply the Stone-Weierstrass theorem (from Mathlib) to conclude density.
3. Approximate the cosine activation by the sigmoidal activation to transfer universality.

## Main results

* `IsUniversal` : predicate for universal approximation over compact sets
* `cos_mul_mem` : F_{cos,d} is closed under pointwise multiplication
* `exp_mul_mem` : F_{exp,d} is closed under pointwise multiplication
* `networkSubalgebra` : the subalgebra of C(ℝᵈ, ℝ) realized by a network class
* `isUniversal_of_separatesPoints` : a network class that is an algebra and
  separates points is a universal approximator (the Stone-Weierstrass argument)
* `cos_isUniversal` : F_{cos,d} is a universal approximator
* `exp_isUniversal` : F_{exp,d} is a universal approximator
* `sigmoidal_isUniversal` : F_{σ,d} is universal for any sigmoidal σ
* `relu_isUniversal` : F_{ReLU,d} is a universal approximator

-/

@[expose] public section

open Real Filter Topology ContinuousMap

namespace Approximation.Universal

variable {d : ℕ}

private lemma eval_eq_sum_affine {σ : ℝ → ℝ} {d m : ℕ}
    (net : OneHiddenLayer.Network σ d m) (x : EuclideanSpace ℝ (Fin d)) :
    OneHiddenLayer.Network.eval σ net x =
      ∑ i : Fin m,
        net.coeffs i * σ (OneHiddenLayer.affineMap (net.weights i) (net.biases i) x) := by
  simp [OneHiddenLayer.Network.eval]

/-! ### Universal approximation predicate -/

/-- A function class ℱ is a universal approximator over compact sets if for every
    compact S ⊆ ℝᵈ, every continuous g : S → ℝ, and every ε > 0, there is f ∈ ℱ
    with sup_{x ∈ S} |f(x) - g(x)| ≤ ε. -/
def IsUniversal (ℱ : Set ((EuclideanSpace ℝ (Fin d)) → ℝ)) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))), IsCompact S →
  ∀ (g : (EuclideanSpace ℝ (Fin d)) → ℝ), ContinuousOn g S →
  ∀ ε > 0, ∃ f ∈ ℱ, ∀ x ∈ S, |f x - g x| ≤ ε

/-! ### Closure under multiplication -/

/-- F_{cos,d} is closed under pointwise multiplication.
    Proof uses 2cos(y)cos(z) = cos(y+z) + cos(y-z). -/
theorem cos_mul_mem (f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf₁ : f₁ ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d)
    (hf₂ : f₂ ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d) :
    (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d := by
  simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
    Set.mem_iUnion, Set.mem_ofPred_eq] at hf₁ hf₂ ⊢
  rcases hf₁ with ⟨m₁, net₁, rfl⟩
  rcases hf₂ with ⟨m₂, net₂, rfl⟩
  let α := (Fin m₁ × Fin m₂) × Fin 2
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let net : OneHiddenLayer.Network (fun z => Real.cos z) d (Fintype.card α) :=
    { weights := fun k =>
        let ij := (e k).1
        let s := (e k).2
        if s = 0 then net₁.weights ij.1 + net₂.weights ij.2
        else net₁.weights ij.1 - net₂.weights ij.2
      biases := fun k =>
        let ij := (e k).1
        let s := (e k).2
        if s = 0 then net₁.biases ij.1 + net₂.biases ij.2
        else net₁.biases ij.1 - net₂.biases ij.2
      coeffs := fun k =>
        let ij := (e k).1
        net₁.coeffs ij.1 * net₂.coeffs ij.2 / 2 }
  refine ⟨Fintype.card α, net, ?_⟩
  ext x
  let a : Fin m₁ → ℝ := fun i =>
    OneHiddenLayer.affineMap (net₁.weights i) (net₁.biases i) x
  let b : Fin m₂ → ℝ := fun j =>
    OneHiddenLayer.affineMap (net₂.weights j) (net₂.biases j) x
  let term : α → ℝ := fun
    | ⟨⟨i, j⟩, s⟩ =>
        (net₁.coeffs i * net₂.coeffs j / 2) *
          Real.cos (if s = 0 then a i + b j else a i - b j)
  symm
  have h_eval_net :
      OneHiddenLayer.Network.eval (fun z => Real.cos z) net x =
        ∑ k : Fin (Fintype.card α), term (e k) := by
    unfold OneHiddenLayer.Network.eval
    refine Finset.sum_congr rfl ?_
    intro k _
    rcases hk : e k with ⟨⟨i, j⟩, s⟩
    have h_aff :
        OneHiddenLayer.affineMap
            (if s = 0 then net₁.weights i + net₂.weights j else net₁.weights i - net₂.weights j)
            (if s = 0 then net₁.biases i + net₂.biases j else net₁.biases i - net₂.biases j) x
          = if s = 0 then a i + b j else a i - b j := by
      by_cases hs : s = 0
      · rw [if_pos hs, if_pos hs, hs]
        simpa [a, b] using
          (OneHiddenLayer.affineMap_add (net₁.weights i) (net₂.weights j)
            (net₁.biases i) (net₂.biases j) x)
      · rw [if_neg hs, if_neg hs]
        simpa [a, b, hs] using
          (OneHiddenLayer.affineMap_sub (net₁.weights i) (net₂.weights j)
            (net₁.biases i) (net₂.biases j) x)
    simp [hk, term, net, h_aff]
  have h_eval_net₁ :
      OneHiddenLayer.Network.eval (fun z => Real.cos z) net₁ x =
        ∑ i : Fin m₁, net₁.coeffs i * Real.cos (a i) := by
    simpa [a] using eval_eq_sum_affine net₁ x
  have h_eval_net₂ :
      OneHiddenLayer.Network.eval (fun z => Real.cos z) net₂ x =
        ∑ j : Fin m₂, net₂.coeffs j * Real.cos (b j) := by
    simpa [b] using eval_eq_sum_affine net₂ x
  rw [h_eval_net, h_eval_net₁, h_eval_net₂]
  rw [Equiv.sum_comp e term, Fintype.sum_prod_type]
  rw [show (∑ x : Fin m₁ × Fin m₂, ∑ s : Fin 2, term (x, s)) =
      ∑ i : Fin m₁, ∑ j : Fin m₂, ∑ s : Fin 2, term ((i, j), s) by
        simpa using
          (Fintype.sum_prod_type' (f := fun i j => ∑ s : Fin 2, term ((i, j), s)))]
  rw [Finset.sum_mul_sum]
  have hpair :
      ∀ i : Fin m₁, ∀ j : Fin m₂,
        (∑ s : Fin 2, term ((i, j), s)) =
          (net₁.coeffs i * Real.cos (a i)) * (net₂.coeffs j * Real.cos (b j)) := by
    intro i j
    calc
      (∑ s : Fin 2, term ((i, j), s))
          = (net₁.coeffs i * net₂.coeffs j / 2) *
              (Real.cos (a i + b j) + Real.cos (a i - b j)) := by
                rw [Fin.sum_univ_two]
                simp [term]
                ring
      _ = (net₁.coeffs i * net₂.coeffs j / 2) *
            (2 * (Real.cos (a i) * Real.cos (b j))) := by
              rw [add_comm, ← Real.two_mul_cos_mul_cos]
              ring
      _ = (net₁.coeffs i * Real.cos (a i)) * (net₂.coeffs j * Real.cos (b j)) := by
            ring
  simp_rw [hpair]

/-- F_{exp,d} is closed under pointwise multiplication.
    Proof uses exp(aᵀx) · exp(bᵀx) = exp((a+b)ᵀx). -/
theorem exp_mul_mem (f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf₁ : f₁ ∈ OneHiddenLayer.UnboundedClass Real.exp d)
    (hf₂ : f₂ ∈ OneHiddenLayer.UnboundedClass Real.exp d) :
    (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass Real.exp d := by
  simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
    Set.mem_iUnion, Set.mem_ofPred_eq] at hf₁ hf₂ ⊢
  rcases hf₁ with ⟨m₁, net₁, rfl⟩
  rcases hf₂ with ⟨m₂, net₂, rfl⟩
  let α := Fin m₁ × Fin m₂
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let net : OneHiddenLayer.Network Real.exp d (Fintype.card α) :=
    { weights := fun k =>
        let ij := e k
        net₁.weights ij.1 + net₂.weights ij.2
      biases := fun k =>
        let ij := e k
        net₁.biases ij.1 + net₂.biases ij.2
      coeffs := fun k =>
        let ij := e k
        net₁.coeffs ij.1 * net₂.coeffs ij.2 }
  refine ⟨Fintype.card α, net, ?_⟩
  ext x
  let a : Fin m₁ → ℝ := fun i =>
    OneHiddenLayer.affineMap (net₁.weights i) (net₁.biases i) x
  let b : Fin m₂ → ℝ := fun j =>
    OneHiddenLayer.affineMap (net₂.weights j) (net₂.biases j) x
  let term : α → ℝ := fun ij =>
    (net₁.coeffs ij.1 * net₂.coeffs ij.2) * Real.exp (a ij.1 + b ij.2)
  symm
  have h_eval_net :
      OneHiddenLayer.Network.eval Real.exp net x =
        ∑ k : Fin (Fintype.card α), term (e k) := by
    unfold OneHiddenLayer.Network.eval
    refine Finset.sum_congr rfl ?_
    intro k _
    rcases hk : e k with ⟨i, j⟩
    have h_aff :
        OneHiddenLayer.affineMap
            (net₁.weights i + net₂.weights j)
            (net₁.biases i + net₂.biases j) x
          = a i + b j := by
      rw [OneHiddenLayer.affineMap_add]
    simp [hk, term, net, h_aff]
  have h_eval_net₁ :
      OneHiddenLayer.Network.eval Real.exp net₁ x =
        ∑ i : Fin m₁, net₁.coeffs i * Real.exp (a i) := by
    simpa [a] using eval_eq_sum_affine net₁ x
  have h_eval_net₂ :
      OneHiddenLayer.Network.eval Real.exp net₂ x =
        ∑ j : Fin m₂, net₂.coeffs j * Real.exp (b j) := by
    simpa [b] using eval_eq_sum_affine net₂ x
  rw [h_eval_net, h_eval_net₁, h_eval_net₂]
  rw [Equiv.sum_comp e term, Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hpair :
      ∀ i : Fin m₁, ∀ j : Fin m₂,
        term (i, j) =
          (net₁.coeffs i * Real.exp (a i)) * (net₂.coeffs j * Real.exp (b j)) := by
    intro i j
    simp [term, Real.exp_add]
    ring
  simp_rw [hpair]

/-! ### Stone-Weierstrass via Mathlib -/

/-- F_{cos,d} satisfies the Stone-Weierstrass separation condition:
    for x ≠ x', the function z ↦ cos((z-x')ᵀ(x-x')/‖x-x'‖²) separates them. -/
lemma cos_separates_points (x x' : EuclideanSpace ℝ (Fin d)) (h : x ≠ x') :
    ∃ f ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d, f x ≠ f x' := by
  let c : ℝ := (‖x - x'‖ ^ 2)⁻¹
  let w : EuclideanSpace ℝ (Fin d) := c • (x - x')
  let b : ℝ := -c * inner ℝ x' (x - x')
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    Real.cos (OneHiddenLayer.affineMap w b z)
  refine ⟨f, ?_, ?_⟩
  · simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨1, { weights := fun _ => w, biases := fun _ => b, coeffs := fun _ => 1 }, ?_⟩
    ext z
    simp [f, OneHiddenLayer.Network.eval]
  · have hsub : x - x' ≠ 0 := sub_ne_zero.mpr h
    have hnorm : ‖x - x'‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hsq : ‖x - x'‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
    have hx_eval : OneHiddenLayer.affineMap w b x = 1 := by
      rw [OneHiddenLayer.affineMap_smul_sub_inner, real_inner_self_eq_norm_sq]
      simp [c, hsq]
    have hx'_eval : OneHiddenLayer.affineMap w b x' = 0 := by
      rw [OneHiddenLayer.affineMap_smul_sub_inner]
      simp
    have hcos : Real.cos 1 ≠ 1 := by
      intro hcos
      have hle : Real.cos 1 ≤ 5 / 9 := Real.cos_one_le
      linarith
    simp [f, hx_eval, hx'_eval]
    simpa [Real.cos_zero] using hcos

/-- F_{cos,d} does not vanish: cos(0ᵀx) = 1 for all x. -/
lemma cos_nonvanishing (x : EuclideanSpace ℝ (Fin d)) :
    ∃ f ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d, f x ≠ 0 := by
  refine ⟨fun _ => 1, ?_, one_ne_zero⟩
  simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
    Set.mem_iUnion, Set.mem_ofPred_eq]
  -- Use one neuron: weight 0, bias 0, coefficient 1 → eval = 1 * cos(0) = 1
  exact ⟨1, { weights := fun _ => 0, biases := fun _ => 0, coeffs := fun _ => 1 }, by
    funext y
    simp [OneHiddenLayer.Network.eval, OneHiddenLayer.affineMap]⟩

/-! ### Main universality theorems -/

/-! ### The Stone-Weierstrass transfer principle

The main universality proofs in this file all follow the same pattern, due to
(Hornik, Stinchcombe, White 1989): the network class `F_{σ,d}` forms a subalgebra of
`C(ℝᵈ, ℝ)` which separates points, so the Stone-Weierstrass theorem makes it dense.
The following definitions and lemmas package this argument once, for reuse by
`cos_isUniversal`, `exp_isUniversal`, and related results. -/

/-- The subalgebra of `C(EuclideanSpace ℝ (Fin d), ℝ)` of functions realized by
single-hidden-layer networks with activation `σ`, given that the class is closed under
multiplication and contains the constant function `1`. -/
def networkSubalgebra (σ : ℝ → ℝ)
    (hmul : ∀ f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ,
      f₁ ∈ OneHiddenLayer.UnboundedClass σ d →
      f₂ ∈ OneHiddenLayer.UnboundedClass σ d →
      (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass σ d)
    (hone : (1 : (EuclideanSpace ℝ (Fin d)) → ℝ) ∈ OneHiddenLayer.UnboundedClass σ d) :
    Subalgebra ℝ C(EuclideanSpace ℝ (Fin d), ℝ) where
  carrier := { f | (f : (EuclideanSpace ℝ (Fin d)) → ℝ) ∈
    OneHiddenLayer.UnboundedClass σ d }
  add_mem' := fun hf hg => OneHiddenLayer.UnboundedClass.add_mem hf hg
  mul_mem' := fun hf hg => hmul _ _ hf hg
  algebraMap_mem' := fun r => by
    simp only [Set.mem_ofPred_eq]
    have hfun : ⇑(algebraMap ℝ C(EuclideanSpace ℝ (Fin d), ℝ) r) = fun _ => r := by
      funext x; simp [algebraMap_apply]
    rw [hfun]
    have h := OneHiddenLayer.UnboundedClass.smul_mem (σ := σ) (d := d) r hone
    simpa using h

/-- A network class that is an algebra and separates points is a universal approximator.
This is the Stone-Weierstrass argument of (Hornik, Stinchcombe, White 1989):
restrict the network subalgebra to the compact set `S`, note that it still separates
points, and apply Stone-Weierstrass to approximate `g` restricted to `S`. -/
theorem isUniversal_of_separatesPoints (σ : ℝ → ℝ) (hσ : Continuous σ)
    (hmul : ∀ f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ,
      f₁ ∈ OneHiddenLayer.UnboundedClass σ d →
      f₂ ∈ OneHiddenLayer.UnboundedClass σ d →
      (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass σ d)
    (hone : (1 : (EuclideanSpace ℝ (Fin d)) → ℝ) ∈ OneHiddenLayer.UnboundedClass σ d)
    (hsep : ∀ x y : EuclideanSpace ℝ (Fin d), x ≠ y →
      ∃ f ∈ OneHiddenLayer.UnboundedClass σ d, f x ≠ f y) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) := by
  intro S hS g hg ε hε
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  -- Restrict the network subalgebra to the compact set `S`.
  let restr : C(EuclideanSpace ℝ (Fin d), ℝ) →⋆ₐ[ℝ] C(S, ℝ) :=
    ContinuousMap.compStarAlgHom' ℝ ℝ ⟨Subtype.val, continuous_subtype_val⟩
  have hsepS : (Subalgebra.map restr.toAlgHom
      (networkSubalgebra σ hmul hone)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfne⟩ := hsep x y (Subtype.coe_ne_coe.mpr hxy)
    have hfc : Continuous f := OneHiddenLayer.UnboundedClass.continuous hσ hf
    refine ⟨fun z => f z, ⟨restr ⟨f, hfc⟩, ?_, rfl⟩, hfne⟩
    exact Subalgebra.mem_map.mpr ⟨⟨f, hfc⟩, hf, rfl⟩
  obtain ⟨g₀, hg₀⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (Subalgebra.map restr.toAlgHom (networkSubalgebra σ hmul hone)) hsepS
      (S.restrict g) (continuousOn_iff_continuous_restrict.mp hg) ε hε
  obtain ⟨f₀, hf₀, hmap⟩ := Subalgebra.mem_map.mp g₀.2
  refine ⟨f₀, hf₀, fun x hx => ?_⟩
  have h := hg₀ ⟨x, hx⟩
  rw [Real.norm_eq_abs] at h
  have heval : (g₀ : S → ℝ) ⟨x, hx⟩ = f₀ x := by
    have h2 := ContinuousMap.congr_fun hmap ⟨x, hx⟩
    exact h2.symm
  rw [heval] at h
  exact le_of_lt h

/-- The constant function `1` is a cos network: `1 = cos(0ᵀx)`. -/
lemma cos_one_mem : (1 : (EuclideanSpace ℝ (Fin d)) → ℝ) ∈
    OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d := by
  rw [OneHiddenLayer.mem_UnboundedClass_iff]
  exact ⟨1, { weights := fun _ => 0, biases := fun _ => 0, coeffs := fun _ => 1 }, by
    funext x
    simp [OneHiddenLayer.Network.eval, OneHiddenLayer.affineMap]⟩

/-- Lemma 2.2: F_{cos,d} is a universal approximator (Hornik-Stinchcombe-White 1989). -/
theorem cos_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d) :=
  isUniversal_of_separatesPoints (fun z => Real.cos z) Real.continuous_cos
    (fun _ _ hf₁ hf₂ => cos_mul_mem _ _ hf₁ hf₂)
    cos_one_mem (fun x y hxy => cos_separates_points x y hxy)

/-- The constant function `1` is an exp network: `1 = exp(0ᵀx)`. -/
lemma exp_one_mem : (1 : (EuclideanSpace ℝ (Fin d)) → ℝ) ∈
    OneHiddenLayer.UnboundedClass Real.exp d := by
  rw [OneHiddenLayer.mem_UnboundedClass_iff]
  exact ⟨1, { weights := fun _ => 0, biases := fun _ => 0, coeffs := fun _ => 1 }, by
    funext x
    simp [OneHiddenLayer.Network.eval, OneHiddenLayer.affineMap, Real.exp_zero]⟩

/-- F_{exp,d} satisfies the Stone-Weierstrass separation condition:
    for x ≠ x', the function z ↦ exp((z-x')ᵀ(x-x')/‖x-x'‖²) separates them,
    since it takes the values exp(1) and exp(0) at x and x'. -/
lemma exp_separates_points (x x' : EuclideanSpace ℝ (Fin d)) (h : x ≠ x') :
    ∃ f ∈ OneHiddenLayer.UnboundedClass Real.exp d, f x ≠ f x' := by
  let c : ℝ := (‖x - x'‖ ^ 2)⁻¹
  let w : EuclideanSpace ℝ (Fin d) := c • (x - x')
  let b : ℝ := -c * inner ℝ x' (x - x')
  let f : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    Real.exp (OneHiddenLayer.affineMap w b z)
  refine ⟨f, ?_, ?_⟩
  · simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
      Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨1, { weights := fun _ => w, biases := fun _ => b, coeffs := fun _ => 1 }, ?_⟩
    ext z
    simp [f, OneHiddenLayer.Network.eval]
  · have hsub : x - x' ≠ 0 := sub_ne_zero.mpr h
    have hnorm : ‖x - x'‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hsq : ‖x - x'‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
    have hx_eval : OneHiddenLayer.affineMap w b x = 1 := by
      rw [OneHiddenLayer.affineMap_smul_sub_inner, real_inner_self_eq_norm_sq]
      simp [c, hsq]
    have hx'_eval : OneHiddenLayer.affineMap w b x' = 0 := by
      rw [OneHiddenLayer.affineMap_smul_sub_inner]
      simp
    simp only [f, hx_eval, hx'_eval]
    exact Real.exp_strictMono.injective.ne one_ne_zero

/-- Lemma 2.3: F_{exp,d} is a universal approximator. -/
theorem exp_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass Real.exp d) :=
  isUniversal_of_separatesPoints Real.exp Real.continuous_exp
    (fun _ _ hf₁ hf₂ => exp_mul_mem _ _ hf₁ hf₂)
    exp_one_mem (fun x y hxy => exp_separates_points x y hxy)

/-- Theorem 2.3: for any sigmoidal σ, F_{σ,d} is a universal approximator. -/
theorem sigmoidal_isUniversal (σ : ℝ → ℝ) (hσ : Sigmoidal σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) := by
  sorry

/-- Corollary: F_{ReLU,d} is a universal approximator.
    Uses the fact that z ↦ σ_ReLU(z) - σ_ReLU(z-1) exhibits sigmoidal-type behavior. -/
theorem relu_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass reluActivation d) := by
  sorry

/-! ### Alternative Universal Approximation Conditions -/

/-- Cybenko (1989) approach via duality: if ℱ_σ is not dense in C(S, ℝ),
then by duality there exists a signed measure μ such that ∫ σ(wᵀx - b) dμ(x) = 0
for all w, b. One can then show this implies μ = 0, a contradiction. -/
theorem cybenko_duality (σ : ℝ → ℝ) (hσ : Sigmoidal σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) := by
  sorry

/-- Leshno et al (1993): A continuous activation function σ is a universal approximator
if and only if it is not a polynomial. -/
theorem leshno_isUniversal_iff_not_polynomial (σ : ℝ → ℝ) (h_cont : Continuous σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) ↔
    ¬ ∃ (p : Polynomial ℝ), ∀ x, σ x = Polynomial.eval x p := by
  sorry

end Approximation.Universal

end
