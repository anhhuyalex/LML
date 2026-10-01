/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.NeuronSum

/-!
# Two-layer network: finite-width NTK concentration

Chebyshev concentration of the empirical NTK matrix under `initMeasure n d`, convergence in
probability in Frobenius norm, the Rayleigh lower bound transferred from the limiting matrix, and
the initial spectral-gap failure bound.

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

/-! ### Finite-Width NTK Concentration and Transport to `initMeasure` -/

section FiniteWidthNTKConcentration

/-- Evaluation of `empiricalNTKMatrix` on parameters unpacked from the product measure
via `arrowProdEquivProdArrow` matches the single-neuron average summand. -/
private lemma empiricalNTKMatrix_packed_arrowProd_eq_summand {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (n : ℕ)
    (ω : Fin n → (Fin d → ℝ) × ℝ) (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1
                  (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
           φ ((ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
         (ω i).2 ^ 2 *
           deriv φ ((ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
           deriv φ ((ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
           ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ
             (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) := by
  have h := empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum φ n d m hd X
    (packParams (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1
                (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2)
    (fun _ _ => hφ_diff.differentiableAt) α β
  rw [h]
  simp only [unpackW_packParams, unpackA_packParams]
  have h_prod : (d : ℝ)⁻¹ * (X α ⬝ᵥ X β) =
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) :=
    (dotProduct_scaled_dataset d hd (X α) (X β)).symm
  rw [h_prod]
  have h_w (i : Fin n) :
      (Real.sqrt (d : ℝ))⁻¹ *
        ((MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1 i ⬝ᵥ X α) =
      (ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) := by
    rw [dotProduct_mul_right]
    rfl
  have h_w' (i : Fin n) :
      (Real.sqrt (d : ℝ))⁻¹ *
        ((MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).1 i ⬝ᵥ X β) =
      (ω i).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) := by
    rw [dotProduct_mul_right]
    rfl
  have h_a (i : Fin n) :
      (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n) ω).2 i =
      (ω i).2 := rfl
  simp_rw [h_w, h_w', h_a]

/-- Finite-width entrywise Chebyshev concentration of the empirical NTK matrix under
the joint initialization measure `initMeasure n d`. -/
theorem chebyshev_entrywise_empiricalNTKMatrix
    {m d : ℕ} (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (n : ℕ) (hn : 0 < n) (α β : Fin m) {c : ℝ} (hc : 0 < c) :
    (initMeasure n d)
      {p | c ≤ |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) α β - limitingFullNTKMatrix φ X α β|} ≤
      ENNReal.ofReal (fullNTKSummandSecondMoment d φ X α β / ((n : ℝ) * c ^ 2)) := by
  have h_meas_eq : (initMeasure n d) =
      (Measure.pi fun _ : Fin n => singleNeuronMeasure d).map
        (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)) :=
    (measurePreserving_arrowProd_singleNeuronMeasure n d).map_eq.symm
  rw [h_meas_eq, MeasurableEquiv.map_apply]
  set Y := fun u : (Fin d → ℝ) × ℝ =>
    φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
     u.2 ^ 2 * deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
       ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))
  have hY_L2 : MemLp Y 2 (singleNeuronMeasure d) :=
    memLp_two_fullNTK_summand φ hdφ_meas
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)
      (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)
      (hφ_L2 α β) (hdφ_L2 α β)
  have h_cheb := chebyshev_average_pi_le_second_moment (singleNeuronMeasure d) hn Y hY_L2 hc
  have h_int : ∫ x, Y x ∂(singleNeuronMeasure d) = limitingFullNTKMatrix φ X α β :=
    integral_fullNTK_summand_scaled_dataset_eq_limiting hd φ X
      (fun a b => (hφ_L2 a b).integrable (by norm_num))
      (fun a b => (hdφ_L2 a b).integrable (by norm_num)) α β
  rw [h_int] at h_cheb
  have h_set_eq : (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)) ⁻¹'
      {p | c ≤ |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) α β - limitingFullNTKMatrix φ X α β|} =
      {ω | c ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i) - limitingFullNTKMatrix φ X α β|} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [empiricalNTKMatrix_packed_arrowProd_eq_summand hd φ hφ_diff X n ω α β]
  rw [h_set_eq]
  exact h_cheb

/-- If a matrix has Frobenius norm at least `ε`, at least one entry has absolute value at
least `ε / m`. Kept private to `NetworkParam.lean` until a second caller appears. -/
private lemma exists_entry_ge_of_frobenius_ge {m : ℕ} (hm : 0 < m)
    (A : Matrix (Fin m) (Fin m) ℝ) {ε : ℝ} (hε : 0 < ε) (hA : ε ≤ ‖A‖) :
    ∃ p : Fin m × Fin m, ε / (m : ℝ) ≤ |A p.1 p.2| := by
  by_contra! h_all
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have h_ne : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 hm
  have h_entry : ∀ (i j : Fin m), ‖A i j‖ ^ (2 : ℝ) < (ε / (m : ℝ)) ^ (2 : ℝ) := by
    intro i j
    have := h_all (i, j)
    rw [Real.norm_eq_abs]
    have h1 : 0 ≤ |A i j| := abs_nonneg _
    have h2 : 0 < ε / (m : ℝ) := div_pos hε hm_pos
    exact Real.rpow_lt_rpow h1 this (by norm_num)
  have h_sum_inner : ∀ (i : Fin m), ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) <
      (m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ) := by
    intro i
    have h : ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) < ∑ _j : Fin m, (ε / (m : ℝ)) ^ (2 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 h_ne) (fun j _ => h_entry i j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have h_sum_outer : ∑ i : Fin m, (∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) <
      (m : ℝ) * ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) := by
    have h : ∑ i : Fin m, (∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) <
        ∑ _i : Fin m, ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 h_ne) (fun i _ => h_sum_inner i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact h
  have heq : (m : ℝ) * ((m : ℝ) * (ε / (m : ℝ)) ^ (2 : ℝ)) = ε ^ (2 : ℝ) := by
    have hm_ne : ((m : ℝ) ^ (2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hm_pos 2).ne'
    rw [Real.div_rpow hε.le hm_pos.le]
    calc (m : ℝ) * ((m : ℝ) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)))
      _ = ((m : ℝ) * (m : ℝ)) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)) := by ring
      _ = ((m : ℝ) ^ (2 : ℝ)) * (ε ^ (2 : ℝ) / (m : ℝ) ^ (2 : ℝ)) := by
        congr 1
        rw [Real.rpow_two]
        ring
      _ = ε ^ (2 : ℝ) := mul_div_cancel₀ _ hm_ne
  rw [heq] at h_sum_outer
  rw [Matrix.frobenius_norm_def] at hA
  have h_sum_nonneg : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have h_norm_lt : (∑ i : Fin m, ∑ j : Fin m, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) <
      (ε ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_lt_rpow h_sum_nonneg h_sum_outer (by norm_num)
  have heq2 : (ε ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ε := by
    rw [← Real.rpow_mul hε.le]
    norm_num
  rw [heq2] at h_norm_lt
  exact not_lt_of_ge hA h_norm_lt

/-- Finite-width matrix Chebyshev concentration of the empirical NTK in Frobenius norm
under the joint initialization measure `initMeasure n d`. -/
theorem chebyshev_matrix_empiricalNTKMatrix
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    (initMeasure n d)
      {p | ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
      ENNReal.ofReal (((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * ε ^ 2)) := by
  set E : Fin m × Fin m → Set (Matrix (Fin n) (Fin d) ℝ × (Fin n → ℝ)) := fun p =>
    {pt | ε / (m : ℝ) ≤
      |empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) p.1 p.2 - limitingFullNTKMatrix φ X p.1 p.2|}
  have h_sub : {pt | ε ≤
      ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X‖} ⊆
      ⋃ p : Fin m × Fin m, E p := by
    intro pt hpt
    simp only [Set.mem_ofPred_eq] at hpt
    have h_ex := exists_entry_ge_of_frobenius_ge hm
      (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X) hε hpt
    rcases h_ex with ⟨p, hp⟩
    simp only [Set.mem_iUnion]
    exact ⟨p, hp⟩
  have h_meas_union : (initMeasure n d)
      {pt | ε ≤ ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams pt.1 pt.2) - limitingFullNTKMatrix φ X‖} ≤
      (initMeasure n d) (⋃ p : Fin m × Fin m, E p) :=
    measure_mono h_sub
  have h_union_le : (initMeasure n d) (⋃ p : Fin m × Fin m, E p) ≤
      ∑ p : Fin m × Fin m, (initMeasure n d) (E p) :=
    measure_iUnion_fintype_le (initMeasure n d) _
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have h_eps_m_pos : 0 < ε / (m : ℝ) := div_pos hε hm_pos
  have h_entry_le : ∀ p : Fin m × Fin m, (initMeasure n d) (E p) ≤
      ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    fun p => chebyshev_entrywise_empiricalNTKMatrix hd φ hφ_diff hdφ_meas X hφ_L2 hdφ_L2 n hn
      p.1 p.2 h_eps_m_pos
  have h_sum_le : (∑ p : Fin m × Fin m, (initMeasure n d) (E p)) ≤
      ∑ p : Fin m × Fin m,
        ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 /
          ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    Finset.sum_le_sum fun p _ => h_entry_le p
  refine h_meas_union.trans (h_union_le.trans (h_sum_le.trans ?_))
  have hn_eps_pos : 0 < (n : ℝ) * (ε / (m : ℝ)) ^ 2 :=
    mul_pos (Nat.cast_pos.2 hn) (sq_pos_of_ne_zero h_eps_m_pos.ne')
  have h_nonneg : ∀ p : Fin m × Fin m,
      0 ≤ fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2) :=
    fun p => div_nonneg (fullNTKSummandSecondMoment_nonneg d φ X p.1 p.2) hn_eps_pos.le
  have h_sum_eq :
      (∑ p : Fin m × Fin m,
        ENNReal.ofReal (fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2))) =
      ENNReal.ofReal (∑ p : Fin m × Fin m,
        fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) :=
    (ENNReal.ofReal_sum_of_nonneg fun p _ => h_nonneg p).symm
  rw [h_sum_eq]
  have heq : (∑ p : Fin m × Fin m,
        fullNTKSummandSecondMoment d φ X p.1 p.2 / ((n : ℝ) * (ε / (m : ℝ)) ^ 2)) =
      ((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * ε ^ 2) := by
    rw [← Finset.sum_div]
    rw [div_pow]
    have hm_ne : (m : ℝ) ≠ 0 := hm_pos.ne'
    calc (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
          ((n : ℝ) * (ε ^ 2 / (m : ℝ) ^ 2))
      _ = (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
            (((n : ℝ) * ε ^ 2) / (m : ℝ) ^ 2) := by
        congr 1
        ring
      _ = (m : ℝ) ^ 2 * (∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
            ((n : ℝ) * ε ^ 2) := by
        rw [div_div_eq_mul_div]
        ring
  rw [heq]

/-- Qualitative finite-width convergence in probability of the empirical NTK matrix to
`limitingFullNTKMatrix` under the varying initialization measure `initMeasure n d`. -/
theorem tendsto_initMeasure_empiricalNTKMatrix_ge_eps
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖})
      Filter.atTop
      (nhds 0) := by
  let C := (m : ℝ) ^ 2 * ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2
  have h_le : ∀ n : ℕ, 0 < n →
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
        ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2)) := fun n hn =>
    chebyshev_matrix_empiricalNTKMatrix hm hd φ hφ_diff hdφ_meas X hφ_L2 hdφ_L2 n hn hε
  have h_real : Filter.Tendsto (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) Filter.atTop (nhds 0) := by
    have h_const : (fun n : ℕ => C / ((n : ℝ) * ε ^ 2)) =
        (fun n : ℕ => (C / ε ^ 2) * (n : ℝ)⁻¹) := by
      ext n
      ring
    rw [h_const]
    have h_inv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h_mul := Filter.Tendsto.const_mul (C / ε ^ 2) h_inv
    rw [mul_zero] at h_mul
    exact h_mul
  have h_lim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2))) Filter.atTop
      (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal h_real
  have h_le_eventually : ∀ᶠ n in Filter.atTop,
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} ≤
        ENNReal.ofReal (C / ((n : ℝ) * ε ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact h_le n (Nat.zero_lt_one.trans_le hn)
  have h_bot : ∀ᶠ n in Filter.atTop, 0 ≤
      (initMeasure n d)
        {p | ε ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} := by
    filter_upwards with n
    exact bot_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim h_bot h_le_eventually



/-- If the empirical NTK at initialization is within Frobenius distance `lambda_inf / 2` of
`limitingFullNTKMatrix φ X`, it satisfies the Rayleigh quotient lower bound
`(lambda_inf / 2) ‖v‖²`. -/
theorem initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
    {m d : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (n : ℕ) (p : (Fin n → Fin d → ℝ) × (Fin n → ℝ))
    (lambda_inf : ℝ)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (h_dist : ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖ ≤ lambda_inf / 2)
    (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_inf / 2) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams p.1 p.2) *ᵥ v.ofLp) := by
  have h_rr₀ := rayleigh_lower_bound_of_sub_smul_posSemidef (limitingFullNTKMatrix φ X)
    lambda_inf hK_gap
  have h_bound := rayleigh_quotient_lower_bound_of_matrix_dist
    (empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams p.1 p.2))
    (limitingFullNTKMatrix φ X) lambda_inf (lambda_inf / 2) h_rr₀ h_dist v
  have heq : lambda_inf - lambda_inf / 2 = lambda_inf / 2 := by ring
  rwa [heq] at h_bound

/-- Finite-width probability bound for initial empirical NTK spectral gap failure under
`initMeasure n d`.
By Chebyshev's inequality and Rayleigh perturbation, the probability that the empirical NTK fails to
satisfy the spectral lower bound `(lambda_inf / 2) ‖v‖²` decays as `O(1 / n)`. -/
theorem chebyshev_matrix_empiricalNTKMatrix_spectral_gap_failure
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef)
    (n : ℕ) (hn : 0 < n) :
    (initMeasure n d)
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
        (lambda_inf / 2) * ‖v‖ ^ 2 ≤
          v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ≤
      ENNReal.ofReal (((m : ℝ) ^ 2 *
        ∑ p : Fin m × Fin m, fullNTKSummandSecondMoment d φ X p.1 p.2) /
        ((n : ℝ) * (lambda_inf / 2) ^ 2)) := by
  have h_sub : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
      (lambda_inf / 2) * ‖v‖ ^ 2 ≤
        v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
          (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ⊆
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | lambda_inf / 2 ≤
        ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
          (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    by_contra! h_lt
    exact hp (initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
      φ X n p lambda_inf hK_gap h_lt.le)
  have h_failure_le_tail : (initMeasure n d)
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
        (lambda_inf / 2) * ‖v‖ ^ 2 ≤
          v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)} ≤
      (initMeasure n d)
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | lambda_inf / 2 ≤
          ‖empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams p.1 p.2) - limitingFullNTKMatrix φ X‖} :=
    measure_mono h_sub
  have h_eps_pos : 0 < lambda_inf / 2 := half_pos hlambda_inf
  exact h_failure_le_tail.trans (chebyshev_matrix_empiricalNTKMatrix hm hd φ hφ_diff hdφ_meas X
    hφ_L2 hdφ_L2 n hn h_eps_pos)

/-- Spectral-gap failure measure tends to zero:
the measure of the set where the empirical NTK fails the Rayleigh lower bound
`(lambda_inf / 2) ‖v‖²` tends to 0 as width `n → ∞`. -/
theorem tendsto_initMeasure_initial_spectral_gap_failure
    {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α β : Fin m, MemLp (fun w =>
      deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) 2 (gaussianRowMeasure d))
    (lambda_inf : ℝ) (hlambda_inf : 0 < lambda_inf)
    (hK_gap : (limitingFullNTKMatrix φ X - lambda_inf • 1).PosSemidef) :
    Filter.Tendsto
      (fun n : ℕ => (initMeasure n d)
        {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | ¬ ∀ v : EuclideanSpace ℝ (Fin m),
          (lambda_inf / 2) * ‖v‖ ^ 2 ≤
            v.ofLp ⬝ᵥ (empiricalNTKMatrix (netFromParams φ n d)
              (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) (packParams p.1 p.2) *ᵥ v.ofLp)})
      Filter.atTop
      (nhds 0) := by
  have h_eps_pos : 0 < lambda_inf / 2 := half_pos hlambda_inf
  have h_tail := tendsto_initMeasure_empiricalNTKMatrix_ge_eps hm hd φ hφ_diff hdφ_meas X
    hφ_L2 hdφ_L2 (hε := h_eps_pos)
  apply Filter.Tendsto.squeeze' tendsto_const_nhds h_tail
  · filter_upwards with n
    exact bot_le
  · filter_upwards with n
    exact measure_mono (fun p hp => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      by_contra! h_lt
      exact hp (initial_empiricalNTKMatrix_rayleigh_lower_bound_of_frobenius_le
        φ X n p lambda_inf hK_gap h_lt.le))

end FiniteWidthNTKConcentration

end

end NTK
