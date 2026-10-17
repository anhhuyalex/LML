/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiKernelLIntegral
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.RestrictPartition

/-!
# Locally finite measures form an s-finite kernel

The identity map of the space of measures `Measure α` is not an s-finite kernel: the Giry space
contains measures that are not s-finite. It becomes one after restricting to the *locally finite*
measures `L = {M | ∀ k, M (C k) < ∞}` for an exhaustion `C` of a set `U = ⋃ₖ Cₖ`
(`kernel_locallyFinite`): on `L` it is `M ↦ M.restrict U`, and off `L` it is zero.

As a consequence, `n`-fold integrals against `M.restrict U` are Giry-measurable in `M` on `L`
(`exists_measurable_lintegral_pi_restrict`), which is what is needed to transport an equality
in law of random counting measures to an equality in law of their replica averages.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory

attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α] {C : ℕ → Set α}

/-- The set of locally finite measures, for the exhaustion `C`. -/
private def locFin (C : ℕ → Set α) : Set (Measure α) := {M | ∀ k, M (C k) < ∞}

private theorem measurableSet_locFin (hC : ∀ k, MeasurableSet (C k)) :
    MeasurableSet (locFin C) := by
  have : locFin C = ⋂ k, {M : Measure α | M (C k) < ∞} := by ext; simp [locFin]
  rw [this]
  exact MeasurableSet.iInter fun k => measurableSet_lt (Measure.measurable_coe (hC k))
    measurable_const

/-- Being finite on every set of an exhaustion is a measurable property of a measure. -/
theorem measurableSet_forall_measure_lt_top (hC : ∀ k, MeasurableSet (C k)) :
    MeasurableSet {M : Measure α | ∀ k, M (C k) < ∞} :=
  measurableSet_locFin hC

/-- The piece of the kernel living on the `k`-th shell of the exhaustion, on those measures for
which the mass of the shell lies in `[j, j + 1)`. -/
private noncomputable def shellKernel (hC : ∀ k, MeasurableSet (C k)) (k j : ℕ) :
    Kernel (Measure α) α :=
  ⟨fun M => if M ∈ locFin C ∧ (j : ℝ≥0∞) ≤ M (disjointed C k) ∧ M (disjointed C k) < j + 1
      then M.restrict (disjointed C k) else 0, by
    have hD : MeasurableSet (disjointed C k) := MeasurableSet.disjointed hC k
    refine Measurable.ite ?_ (Measure.measurable_restrict hD) measurable_const
    exact ((measurableSet_locFin hC).inter
      ((measurableSet_le measurable_const (Measure.measurable_coe hD)).inter
        (measurableSet_lt (Measure.measurable_coe hD) measurable_const)))⟩

private instance isFiniteKernel_shellKernel (hC : ∀ k, MeasurableSet (C k)) (k j : ℕ) :
    IsFiniteKernel (shellKernel hC k j) := by
  refine ⟨⟨j + 1, by simp, fun M => ?_⟩⟩
  change (if M ∈ locFin C ∧ (j : ℝ≥0∞) ≤ M (disjointed C k) ∧ M (disjointed C k) < j + 1
      then M.restrict (disjointed C k) else 0) Set.univ ≤ j + 1
  split_ifs with h
  · rw [Measure.restrict_apply_univ]; exact h.2.2.le
  · simp

private theorem shellKernel_sum_apply (hC : ∀ k, MeasurableSet (C k))
    (M : Measure α) :
    Kernel.sum (fun kj : ℕ × ℕ => shellKernel hC kj.1 kj.2) M =
      if M ∈ locFin C then M.restrict (⋃ k, C k) else 0 := by
  by_cases hM : M ∈ locFin C
  · simp only [hM, ite_true]
    ext s hs
    rw [Kernel.sum_apply' _ _ hs,
      ENNReal.tsum_prod (f := fun k j => shellKernel hC k j M s), ← iUnion_disjointed (f := C),
      Measure.restrict_iUnion (disjoint_disjointed C) (MeasurableSet.disjointed hC),
      Measure.sum_apply _ hs]
    refine tsum_congr fun k => ?_
    have hfin : M (disjointed C k) < ∞ :=
      (measure_mono (disjointed_subset C k)).trans_lt (hM k)
    have hj : ∀ j : ℕ, ((j : ℝ≥0∞) ≤ M (disjointed C k) ∧ M (disjointed C k) < j + 1) ↔
        j = ⌊(M (disjointed C k)).toReal⌋₊ := by
      intro j
      obtain ⟨m, hm0, hmeq⟩ : ∃ m : ℝ, 0 ≤ m ∧ M (disjointed C k) = ENNReal.ofReal m :=
        ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hfin.ne).symm⟩
      have hj1 : (j : ℝ≥0∞) + 1 = ENNReal.ofReal ((j : ℝ) + 1) := by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp
      rw [hmeq, ENNReal.toReal_ofReal hm0, hj1, ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_le_ofReal_iff hm0, ENNReal.ofReal_lt_ofReal_iff (by positivity),
        eq_comm, Nat.floor_eq_iff hm0]
    rw [tsum_eq_single (⌊(M (disjointed C k)).toReal⌋₊)]
    · simp [shellKernel, hM, (hj _).2 rfl]
    · intro j hj'
      have : ¬((j : ℝ≥0∞) ≤ M (disjointed C k) ∧ M (disjointed C k) < j + 1) :=
        fun h => hj' ((hj j).1 h)
      simp [shellKernel, hM, this]
  · simp only [hM, ite_false]
    ext s hs
    rw [Kernel.sum_apply' _ _ hs]
    simp [shellKernel, hM]

/-- The restriction of a measure to the union of an exhaustion by measurable sets of finite measure
is σ-finite. -/
theorem sigmaFinite_restrict_iUnion {M : Measure α} (hC : ∀ k, MeasurableSet (C k))
    (hfin : ∀ k, M (C k) < ∞) : SigmaFinite (M.restrict (⋃ k, C k)) := by
  refine ⟨⟨⟨fun k => C k ∪ (⋃ k, C k)ᶜ, fun _ => trivial, fun k => ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply ((hC k).union (MeasurableSet.iUnion hC).compl),
      union_inter_distrib_right, compl_inter_self, union_empty]
    exact (measure_mono inter_subset_left).trans_lt (hfin k)
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ ⋃ k, C k
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨k, Or.inl hk⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

/-- **The locally finite measures form an s-finite kernel.** For an exhaustion `C` of `U = ⋃ₖ Cₖ`
by measurable sets there is an s-finite kernel from `Measure α` to `α`, with σ-finite values,
which is `M ↦ M.restrict U` on the measures finite on every `Cₖ`. -/
theorem exists_sFiniteKernel_locallyFinite (hC : ∀ k, MeasurableSet (C k)) :
    ∃ κ : Kernel (Measure α) α, IsSFiniteKernel κ ∧ (∀ M, SigmaFinite (κ M)) ∧
      ∀ M : Measure α, (∀ k, M (C k) < ∞) → κ M = M.restrict (⋃ k, C k) := by
  refine ⟨Kernel.sum fun kj : ℕ × ℕ => shellKernel hC kj.1 kj.2, inferInstance, fun M => ?_,
    fun M hM => ?_⟩
  · rw [shellKernel_sum_apply hC]
    by_cases hM : M ∈ locFin C
    · simp only [hM, ite_true]
      exact sigmaFinite_restrict_iUnion hC hM
    · simp only [hM, ite_false]; infer_instance
  · rw [shellKernel_sum_apply hC]
    simp [show M ∈ locFin C from hM]

/-- **Giry measurability of replica integrals.** For an exhaustion `C` of `U = ⋃ₖ Cₖ`, the
`n`-fold integral of a measurable function against `M.restrict U` agrees, on the measures that are
finite on every `Cₖ`, with a function of `M` that is measurable for the Giry σ-algebra. -/
theorem exists_measurable_lintegral_pi_restrict (hC : ∀ k, MeasurableSet (C k)) (n : ℕ)
    {Φ : (Fin n → α) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∃ F : Measure α → ℝ≥0∞, Measurable F ∧ ∀ M : Measure α, (∀ k, M (C k) < ∞) →
      F M = ∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n => M.restrict (⋃ k, C k) := by
  obtain ⟨κ, hs, hσ, hκ⟩ := exists_sFiniteKernel_locallyFinite hC
  refine ⟨fun M => ∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n => κ M,
    Measurable.lintegral_pi_kernel κ n (hΦ.comp measurable_snd), fun M hM => ?_⟩
  simp only [hκ M hM]

end MeasureTheory
