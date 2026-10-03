/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.Architecture
public import LeanMachineLearning.Optimization.NTK.Initialization.Setup

/-!
# Splitting One Weight Layer from the Rest of the Initialization

The deep NTK parameters are read from the product space
`DeepSpace d = (Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ)` (the first `d` infinite weight populations and the
readout) with the product of standard Gaussians, `deepMeasure d`. To condition on everything except
one layer `i₀`, we use

* the split `ω ↦ (Function.update ω.1 i₀ 0, ω.2)` zeroes the `i₀`-th population of `ω`,
* `layerBlock n L`: the top-left `n × n` block of a population, i.e. the weight matrix actually
  used by a width-`n` network.

`measurePreserving_layerSplit` states that `(ω ↦ zeroed ω, layerBlock n ∘ eval i₀)` is a measure
preserving map from `deepMeasure d` onto the product of the law of the rest with
`gaussianInit n n`: the layer is independent of the rest and its block is a standard Gaussian
matrix. This is the interface between the concrete network and the conditional Chebyshev bounds
of `Initialization/GaussianConditioning.lean`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory

namespace NTK

/-- The weight populations of the first `d` layers and the readout. -/
abbrev DeepSpace (d : ℕ) := (Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ)

/-- Finite-width network parameters read from a point of `DeepSpace d`. -/
noncomputable def deepParams (d n0 n : ℕ) (ω : DeepSpace d) : DeepMLPParams d n0 n :=
  DeepMLPParams.ofTensor d n0 n (fun k => if h : k < d then ω.1 ⟨k, h⟩ else 0) ω.2

/-- The top-left `n × n` block of a weight population. -/
def layerBlock (n : ℕ) (L : ℕ → ℕ → ℝ) : Fin n → Fin n → ℝ := fun j i => L j.val i.val

lemma measurable_layerBlock (n : ℕ) : Measurable (layerBlock n) :=
  measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i =>
    (measurable_pi_apply i.val).comp (measurable_pi_apply j.val)

/-- Replacing the `i₀`-th weight population by `0` is measurable. -/
lemma measurable_zeroLayer {d : ℕ} (i₀ : Fin d) :
    Measurable (fun ω : DeepSpace d => (Function.update ω.1 i₀ 0, ω.2)) := by
  refine Measurable.prodMk ?_ measurable_snd
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i = i₀
  · subst h; simp only [Function.update_self]; exact measurable_const
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply i).comp measurable_fst

/-- The `n × n` block of a standard Gaussian population is a standard Gaussian matrix. -/
theorem map_layerBlock_infinitePi (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map
      (layerBlock n) = (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0
          1) := by
  let cols : (ℕ → ℕ → ℝ) → (ℕ → Fin n → ℝ) := fun L j i => L j i.val
  let rows : (ℕ → Fin n → ℝ) → (Fin n → Fin n → ℝ) := fun R j => R j.val
  have hcols : Measurable cols :=
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i =>
      (measurable_pi_apply i.val).comp (measurable_pi_apply j)
  have hrows : Measurable rows :=
    measurable_pi_iff.2 fun j => measurable_pi_apply j.val
  have hA : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        gaussianReal 0 1).map cols =
      Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    calc (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1).map cols
        = Measure.infinitePi fun _ : ℕ => Measure.map (fun r : ℕ → ℝ => fun k : Fin n => r k.val)
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
          simpa [cols] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
              (f := fun _ (r : ℕ → ℝ) (k : Fin n) => r k.val)
              (fun _ => measurable_pi_iff.2 fun k => measurable_pi_apply k.val))
      _ = Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
          congr 1
          funext j
          rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
            Measure.infinitePi_eq_pi]
  have hB : (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0
      1)).map rows =
      Measure.pi fun _ : Fin n => (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    rw [show rows = fun R j => R j.val from rfl,
      Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  have hcomp : layerBlock n = rows ∘ cols := rfl
  rw [hcomp, ← Measure.map_map hrows hcols, hA, hB]

/-- Independence of one factor of a product measure's pair from a third coordinate:
if `A ⟂ B` under `μ` then `A ∘ fst ⟂ (B ∘ fst, snd)` under `μ.prod ν`. -/
theorem indepFun_prod_of_indepFun_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : α → γ} {B : α → δ}
    (hA : Measurable A) (hB : Measurable B) (h : IndepFun A B μ) :
    IndepFun (fun ω : α × β => A ω.1) (fun ω : α × β => (B ω.1, ω.2)) (μ.prod ν) := by
  have hAB : Measurable fun a => (A a, B a) := hA.prodMk hB
  refine (indepFun_iff_map_prod_eq_prod_map_map (f := fun ω : α × β => A ω.1)
    (g := fun ω : α × β => (B ω.1, ω.2)) (hA.comp measurable_fst).aemeasurable
    ((hB.comp measurable_fst).prodMk measurable_snd).aemeasurable).2 ?_
  have h1 : (μ.prod ν).map (fun ω : α × β => A ω.1) = μ.map A := by
    rw [show (fun ω : α × β => A ω.1) = A ∘ Prod.fst from rfl,
      ← Measure.map_map hA measurable_fst, Measure.map_fst_prod]
    simp
  have h2 : (μ.prod ν).map (fun ω : α × β => (B ω.1, ω.2)) = (μ.map B).prod ν := by
    have := Measure.map_prod_map μ ν hB (measurable_id (α := β))
    rw [Measure.map_id] at this
    rw [this]; rfl
  have h3 : (μ.prod ν).map (fun ω : α × β => (A ω.1, (B ω.1, ω.2))) =
      (μ.map A).prod ((μ.map B).prod ν) := by
    have e1 := Measure.map_prod_map μ ν hAB (measurable_id (α := β))
    rw [Measure.map_id, ((indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable
      hB.aemeasurable).1 h)] at e1
    have e2 := (measurePreserving_prodAssoc (μ.map A) (μ.map B) ν).map_eq
    have e3 : (fun ω : α × β => (A ω.1, (B ω.1, ω.2))) =
        (MeasurableEquiv.prodAssoc : (γ × δ) × β ≃ᵐ γ × (δ × β)) ∘
          (Prod.map (fun a => (A a, B a)) id) := rfl
    rw [e3, ← Measure.map_map (MeasurableEquiv.prodAssoc.measurable)
      (hAB.prodMap measurable_id), ← e1, e2]
  rw [h1, h2, h3]

/-- Under the product Gaussian measure, one layer is independent of the other layers and the
readout. -/
theorem indepFun_layer_zeroLayer {d : ℕ} (i₀ : Fin d) :
    IndepFun (fun ω : DeepSpace d => ω.1 i₀)
      (fun ω : DeepSpace d => (Function.update ω.1 i₀ 0, ω.2)) ((Measure.pi fun _ : Fin d =>
          Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
  classical
  set L : Measure (ℕ → ℕ → ℝ) := Measure.infinitePi fun _ : ℕ =>
    Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hL
  have hind : iIndepFun (fun (i : Fin d) (w : Fin d → ℕ → ℕ → ℝ) => w i)
      (Measure.pi fun _ : Fin d => L) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hdisj : Disjoint ({i₀} : Finset (Fin d)) (Finset.univ \ {i₀}) := by
    simp
  have h := hind.indepFun_finset {i₀} (Finset.univ \ {i₀}) hdisj
    (fun i => measurable_pi_apply i)
  let G : (↥(Finset.univ \ {i₀}) → ℕ → ℕ → ℝ) → (Fin d → ℕ → ℕ → ℝ) := fun v i =>
    if hi : i = i₀ then 0 else v ⟨i, by simp [hi]⟩
  have hG : Measurable G := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i = i₀
    · simp only [G, hi, dite_true]; exact measurable_const
    · simp only [G, hi, dite_false]; exact measurable_pi_apply _
  have h2 := h.comp (measurable_pi_apply (⟨i₀, Finset.mem_singleton_self i₀⟩ :
    ({i₀} : Finset (Fin d)))) hG
  have e2 : (fun w : Fin d → ℕ → ℕ → ℝ => Function.update w i₀ 0) =
      G ∘ fun (a : Fin d → ℕ → ℕ → ℝ) (i : ↥(Finset.univ \ {i₀})) => a i := by
    funext w i
    by_cases hi : i = i₀
    · subst hi; simp [G]
    · simp [G, hi]
  have h3 : IndepFun (fun w : Fin d → ℕ → ℕ → ℝ => w i₀)
      (fun w : Fin d → ℕ → ℕ → ℝ => Function.update w i₀ 0) (Measure.pi fun _ : Fin d => L) := by
    rw [e2]; exact h2
  have hB' : Measurable (fun w : Fin d → ℕ → ℕ → ℝ => Function.update w i₀ 0) :=
    (measurable_zeroLayer i₀).fst.comp (measurable_id.prodMk (measurable_const (a := 0)))
  exact indepFun_prod_of_indepFun_fst _ _ (measurable_pi_apply i₀) hB' h3

/-- **Layer splitting.** `ω ↦ ((Function.update ω.1 i₀ 0, ω.2), layerBlock n (ω.1 i₀))` is measure
preserving from `deepMeasure d` to the product of the law of `ω ↦ (Function.update ω.1 i₀ 0, ω.2)`
with `gaussianInit n n`. -/
theorem measurePreserving_layerSplit {d : ℕ} (i₀ : Fin d) (n : ℕ) :
    MeasurePreserving
      (fun ω : DeepSpace d => ((Function.update ω.1 i₀ 0, ω.2), layerBlock n (ω.1 i₀)))
      ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      ((((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ
          => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)).map (fun ω : DeepSpace d => (Function.update ω.1 i₀ 0, ω.2))).prod
        (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  have hev : Measurable fun ω : DeepSpace d => layerBlock n (ω.1 i₀) :=
    (measurable_layerBlock n).comp ((measurable_pi_apply i₀).comp measurable_fst)
  have hlaw : ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _
      : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)).map (fun ω : DeepSpace d => layerBlock n (ω.1 i₀)) =
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have h1 : (fun ω : DeepSpace d => layerBlock n (ω.1 i₀)) =
        (layerBlock n ∘ fun w : Fin d → ℕ → ℕ → ℝ => w i₀) ∘ Prod.fst := rfl
    rw [h1, ← Measure.map_map ((measurable_layerBlock n).comp (measurable_pi_apply i₀))
      measurable_fst]
    rw [Measure.map_fst_prod]
    simp only [measure_univ, one_smul]
    have := (measurePreserving_eval (fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) i₀).map_eq
    calc Measure.map (layerBlock n ∘ fun w : Fin d → ℕ → ℕ → ℝ => w i₀)
          (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
        = Measure.map (layerBlock n) (Measure.map (fun w : Fin d → ℕ → ℕ → ℝ => w i₀)
          (Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) :=
          (Measure.map_map (measurable_layerBlock n) (measurable_pi_apply i₀)).symm
      _ = (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0
          1) := by rw [this]; exact map_layerBlock_infinitePi n
  have hind := (indepFun_layer_zeroLayer i₀).symm.comp measurable_id (measurable_layerBlock n)
  refine ⟨(measurable_zeroLayer i₀).prodMk hev, ?_⟩
  rw [← hlaw]
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_zeroLayer i₀).aemeasurable
    hev.aemeasurable).1 (by simpa [Function.comp_def] using hind)

end NTK

end
