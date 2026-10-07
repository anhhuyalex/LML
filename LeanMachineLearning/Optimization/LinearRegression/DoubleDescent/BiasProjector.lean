/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.Householder
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomMatrixFoundations

/-!
# Concentration of the omitted signal of a Gaussian random subspace

Milestone 7e of the double-descent plan ([Bach, 2024]; [Hastie et al., 2022];
[Belkin et al., 2019]). Let `S` be an `n₀ × n` matrix with i.i.d. standard normal entries and `P_S`
the orthogonal projector onto its column space. For every fixed `θ ∈ ℝ^{n₀}`, the omitted signal
`‖(1 - P_S) θ‖²` concentrates at `(1 - n/n₀) ‖θ‖²`; this is the leading term of the bias of random
features regression, `‖(M X - 1) θ⋆‖² = ‖θ⊥‖² + ‖fit error‖²` (`bias_eq_omitted_add_fit_error`).

* `measure_projector_norm_sq_dev_le`: for a fixed orthogonal projection `P` of trace `r` and a
  Gaussian vector `g`, `ℙ (|‖P g‖² - r| ≥ ε r) ≤ 60 / (ε⁴ r²)` (`χ²_r` tail bound);
* `measure_resid_deviation_le`: **non-asymptotic bound** `ℙ (|‖(1 - P_S) θ‖² - (1 - n/n₀) ‖θ‖²| >
  4 ε ‖θ‖²) ≤ 60 / (ε⁴ n²) + 60 / (ε⁴ n₀²)`, for every `θ`;
* `tendsto_measure_resid_deviation`: convergence in probability along `n_k → ∞`, `n_k ≤ n₀_k`.

*Proof strategy (no Sherman-Morrison, no Haar measure).* The event depends on `θ` only through
`‖θ‖` (left orthogonal invariance of `S`, `map_gaussianMatrix_orthogonal_mul`, and Householder
reflections, `Matrix.exists_orthogonal_mulVec_eq`) and is scale invariant, so its probability is
unchanged if `θ` is replaced by an independent Gaussian vector `g`. By Fubini the problem becomes
a statement about a fixed full-rank `S` and a Gaussian `g`, where `‖P_S g‖² ~ χ²_n`
(`map_dotProduct_projector_mulVec`) and `‖g‖² ~ χ²_{n₀}` concentrate, and
`‖P_S g‖² / ‖g‖² ≈ n / n₀`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK Filter Topology
open scoped Matrix

universe u


/-- **Tail bound for a projected Gaussian vector.** -/
theorem measure_projector_norm_sq_dev_le {ι : Type u} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsStarProjection P) (r : ℕ) (hr : (r : ℝ) = P.trace) (hr0 : 0 < r) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {g | ε * r ≤ |(P *ᵥ g) ⬝ᵥ (P *ᵥ g) - r|} ≤ ENNReal.ofReal (60 / (ε ^ 4 * (r : ℝ) ^ 2)) := by
  have hlaw := map_dotProduct_projector_mulVec P hP r hr
  have hmeas : Measurable fun g : ι → ℝ => (P *ᵥ g) ⬝ᵥ (P *ᵥ g) := by fun_prop
  have hset : MeasurableSet {y : ℝ | ε * r ≤ |y - r|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin r)) := by
    have : NeZero r := ⟨hr0.ne'⟩
    infer_instance
  have h1 := Measure.map_apply (μ := Measure.pi fun _ : ι => gaussianReal 0 1) hmeas hset
  rw [hlaw] at h1
  have h2 := Measure.map_apply (μ := stdGaussian (EuclideanSpace ℝ (Fin r)))
    (f := fun x => ‖x‖ ^ 2) (by fun_prop) hset
  have hb := measureReal_norm_sq_sub_ge_le (E := EuclideanSpace ℝ (Fin r)) hε
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hb
  have : (fun g : ι → ℝ => (P *ᵥ g) ⬝ᵥ (P *ᵥ g)) ⁻¹' {y : ℝ | ε * r ≤ |y - r|} =
      {g | ε * r ≤ |(P *ᵥ g) ⬝ᵥ (P *ᵥ g) - r|} := rfl
  rw [← this, ← h1, h2]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hb

/-- **Ratio arithmetic.** If `a ≈ n` and `b ≈ n₀` within relative error `ε ≤ 1/2` and `n ≤ n₀`,
then `a` is within `4 ε b` of `(n/n₀) b`. -/
private theorem abs_sub_lt_of_close {a b n n₀ ε : ℝ} (hn : 0 < n) (hnn : n ≤ n₀) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (ha : |a - n| < ε * n) (hb : |b - n₀| < ε * n₀) :
    |(n / n₀) * b - a| < 4 * ε * b := by
  have hn₀ : 0 < n₀ := lt_of_lt_of_le hn hnn
  rw [abs_lt] at ha hb ⊢
  have hr : n / n₀ * n₀ = n := div_mul_cancel₀ _ hn₀.ne'
  have hr0 : 0 < n / n₀ := by positivity
  have hr1 : n / n₀ ≤ 1 := (div_le_one hn₀).2 hnn
  have h1 : (n / n₀) * (b - n₀) < (n / n₀) * (ε * n₀) :=
    mul_lt_mul_of_pos_left hb.2 hr0
  have h2 : (n / n₀) * (-(ε * n₀)) < (n / n₀) * (b - n₀) :=
    mul_lt_mul_of_pos_left hb.1 hr0
  have h3 : (n / n₀) * (ε * n₀) = ε * n := by rw [mul_left_comm, hr]
  have hbpos : (1 / 2) * n₀ < b := by nlinarith [hb.1]
  have hnn₀ : ε * n ≤ ε * n₀ := mul_le_mul_of_nonneg_left hnn hε.le
  have : 2 * ε * n₀ < 4 * ε * b := by nlinarith
  constructor <;> nlinarith

/-- The residual energy `‖(1 - P_S) x‖²` of a vector `x` against the column space of the matrix
`S`. -/
local notation "resid(" S ", " x ")" =>
  ((1 - gramProjector (Matrix.of S)) *ᵥ x) ⬝ᵥ ((1 - gramProjector (Matrix.of S)) *ᵥ x)

section Residual

variable {n₀ n : ℕ}

private lemma measurable_resid :
    Measurable fun z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) => resid(z.1, z.2) := by
  have hS : Measurable fun z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) =>
      (Matrix.of z.1 : Matrix (Fin n₀) (Fin n) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hP : Measurable fun z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) =>
      gramProjector (Matrix.of z.1) :=
    measurable_matrix_mul (measurable_matrix_mul hS
      (measurable_matrix_nonsing_inv.comp
        (measurable_matrix_mul (measurable_matrix_transpose hS) hS)))
      (measurable_matrix_transpose hS)
  have h1 := measurable_mulVec (measurable_orthogonalComplement hP) measurable_snd
  exact measurable_dotProduct h1 h1

/-- Residual energy under left multiplication by an orthogonal matrix. -/
private lemma resid_orthogonal_mul (U : Matrix (Fin n₀) (Fin n₀) ℝ) (hU : Uᵀ * U = 1)
    (S : Fin n₀ → Fin n → ℝ) (x : Fin n₀ → ℝ) :
    resid(fun i k => (U * Matrix.of S) i k, x) = resid(S, Uᵀ *ᵥ x) := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hP := gramProjector_orthonormal_mul U hU (Matrix.of S)
  have hM : (1 : Matrix (Fin n₀) (Fin n₀) ℝ) - U * gramProjector (Matrix.of S) * Uᵀ =
      U * (1 - gramProjector (Matrix.of S)) * Uᵀ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU']
  have h1 : (1 - gramProjector (Matrix.of fun i k => (U * Matrix.of S) i k)) *ᵥ x =
      U *ᵥ ((1 - gramProjector (Matrix.of S)) *ᵥ (Uᵀ *ᵥ x)) := by
    have : (Matrix.of fun i k => (U * Matrix.of S) i k) = U * Matrix.of S := rfl
    rw [this, hP, hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h2 : ∀ v : Fin n₀ → ℝ, (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = v ⬝ᵥ v := fun v => by
    rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  rw [h1, h2]


private lemma measurableSet_resid_dev (c t : ℝ) (x : Fin n₀ → ℝ) :
    MeasurableSet {S : Fin n₀ → Fin n → ℝ | t * (x ⬝ᵥ x) < |resid(S, x) - c * (x ⬝ᵥ x)|} :=
  measurableSet_lt measurable_const
    (continuous_abs.measurable.comp
      ((measurable_resid.comp (measurable_id.prodMk measurable_const)).sub_const _))

/-- **Transitivity of the Gaussian matrix law on spheres.** The probability that the residual
energy `‖(1 - P_S) x‖²` deviates from `c ‖x‖²` by more than `t ‖x‖²` depends on `x` only through
`‖x‖`: a Householder reflection moves `x` to `y`, and `S ↦ U S` preserves the Gaussian law. -/
private lemma measure_resid_dev_eq (c t : ℝ) {x y : Fin n₀ → ℝ} (hxy : x ⬝ᵥ x = y ⬝ᵥ y) :
    (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {S | t * (x ⬝ᵥ x) < |resid(S, x) - c * (x ⬝ᵥ x)|} =
      (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {S | t * (y ⬝ᵥ y) < |resid(S, y) - c * (y ⬝ᵥ y)|} := by
  obtain ⟨U, -, hUtU, hUy⟩ := Matrix.exists_orthogonal_mulVec_eq y x hxy.symm
  have hUx : Uᵀ *ᵥ x = y := by rw [← hUy, Matrix.mulVec_mulVec, hUtU, Matrix.one_mulVec]
  have hL : Measurable fun W : Fin n₀ → Fin n → ℝ => fun i k => (U * Matrix.of W) i k :=
    Measurable.of_eval fun i => Measurable.of_eval fun k => by
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact Finset.measurable_sum _ fun l _ => by fun_prop
  have hmap := map_gaussianMatrix_orthogonal_mul (q := n) U hUtU
  conv_lhs => rw [← hmap]
  rw [Measure.map_apply hL (measurableSet_resid_dev c t x)]
  congr 1
  ext S
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, resid_orthogonal_mul U hUtU S x, hUx, hxy]

/-- The deviation event is invariant under rescaling `x ↦ a x`, `a ≠ 0`. -/
private lemma resid_dev_smul (c t a : ℝ) (ha : a ≠ 0) (S : Fin n₀ → Fin n → ℝ)
    (x : Fin n₀ → ℝ) :
    t * ((a • x) ⬝ᵥ (a • x)) < |resid(S, a • x) - c * ((a • x) ⬝ᵥ (a • x))| ↔
      t * (x ⬝ᵥ x) < |resid(S, x) - c * (x ⬝ᵥ x)| := by
  have h1 : resid(S, a • x) = a ^ 2 * resid(S, x) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have h2 : (a • x) ⬝ᵥ (a • x) = a ^ 2 * (x ⬝ᵥ x) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have h3 : resid(S, a • x) - c * ((a • x) ⬝ᵥ (a • x)) =
      a ^ 2 * (resid(S, x) - c * (x ⬝ᵥ x)) := by rw [h1, h2]; ring
  rw [h3, h2, abs_mul, abs_of_nonneg (sq_nonneg a), ← mul_assoc, mul_comm t, mul_assoc,
    mul_lt_mul_iff_right₀ (by positivity)]


/-- For a full-column-rank `S`, the deviation event for a single vector `g` forces `‖P_S g‖²` or
`‖g‖²` to deviate from its mean `n`, resp. `n₀`, by the relative amount `ε`. -/
private lemma resid_dev_subset {S : Fin n₀ → Fin n → ℝ}
    (hS : IsUnit ((Matrix.of S)ᵀ * Matrix.of S).det) (hn : 0 < n) (hnn : n ≤ n₀) {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    {g : Fin n₀ → ℝ | 4 * ε * (g ⬝ᵥ g) < |resid(S, g) - (1 - (n : ℝ) / n₀) * (g ⬝ᵥ g)|} ⊆
      {g | ε * (n : ℝ) ≤ |(gramProjector (Matrix.of S) *ᵥ g) ⬝ᵥ (gramProjector (Matrix.of S) *ᵥ g) -
        (n : ℝ)|} ∪ {g | ε * (n₀ : ℝ) ≤ |((1 : Matrix (Fin n₀) (Fin n₀) ℝ) *ᵥ g) ⬝ᵥ
          ((1 : Matrix (Fin n₀) (Fin n₀) ℝ) *ᵥ g) - (n₀ : ℝ)|} := by
  intro g hg
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Matrix.one_mulVec] at h2
  have hP := isOrthogonalProjection_gramProjector (Matrix.of S) hS
  have hpyth := dotProduct_one_sub_gramProjector_mulVec_self (Matrix.of S) hS g
  have hid := mulVec_dot_self_eq _ hP g
  have key := abs_sub_lt_of_close (a := (gramProjector (Matrix.of S) *ᵥ g) ⬝ᵥ
    (gramProjector (Matrix.of S) *ᵥ g)) (b := g ⬝ᵥ g) (n := n) (n₀ := n₀) (by exact_mod_cast hn)
    (by exact_mod_cast hnn) hε hε2 h1 h2
  have heq : resid(S, g) - (1 - (n : ℝ) / n₀) * (g ⬝ᵥ g) =
      (n / n₀) * (g ⬝ᵥ g) - (gramProjector (Matrix.of S) *ᵥ g) ⬝ᵥ
        (gramProjector (Matrix.of S) *ᵥ g) := by
    rw [hpyth, hid]; ring
  rw [Set.mem_ofPred_eq, heq] at hg
  exact absurd key (not_lt.mpr hg.le)

end Residual

section Main

variable {n₀ n : ℕ}

/-- **Bias concentration for a Gaussian projector (non-asymptotic, relative form).** Let `S` be
an `n₀ × n` matrix with i.i.d. standard normal entries, `1 ≤ n ≤ n₀`, `0 < ε ≤ 1/2`. For every
`θ ∈ ℝ^{n₀}`, the residual energy `‖(1 - P_S) θ‖²` is within `4 ε ‖θ‖²` of `(1 - n/n₀) ‖θ‖²`,
except on an event of probability at most `60 / (ε⁴ n²) + 60 / (ε⁴ n₀²)`.

Proof. By left orthogonal invariance of `S` and transitivity of `O(n₀)` on spheres
(`measure_resid_dev_eq`), the failure probability is the same for every `θ` of the same norm and,
by scale invariance, for every `θ ≠ 0`. It is therefore the average over an independent Gaussian
vector `g`; Fubini turns it into the `g`-probability, for fixed full-rank `S`, of
`{|‖P_S g‖² - n| ≥ ε n} ∪ {|‖g‖² - n₀| ≥ ε n₀}` (`resid_dev_subset`), and both are `χ²` tails
(`map_dotProduct_projector_mulVec`, `measureReal_norm_sq_sub_ge_le`). No Sherman-Morrison and no
Haar measure are used. -/
theorem measure_resid_deviation_le (hn : 0 < n) (hnn : n ≤ n₀) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (θ : Fin n₀ → ℝ) :
    (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {S | 4 * ε * (θ ⬝ᵥ θ) < |resid(S, θ) - (1 - (n : ℝ) / n₀) * (θ ⬝ᵥ θ)|} ≤
      ENNReal.ofReal (60 / (ε ^ 4 * (n : ℝ) ^ 2)) +
        ENNReal.ofReal (60 / (ε ^ 4 * (n₀ : ℝ) ^ 2)) := by
  set μ := Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1 with hμ
  set G := Measure.pi fun _ : Fin n₀ => gaussianReal 0 1 with hG
  set c : ℝ := 1 - (n : ℝ) / n₀ with hc
  have hn₀ : 0 < n₀ := lt_of_lt_of_le hn hnn
  by_cases hθ : θ = 0
  · subst hθ
    have : {S : Fin n₀ → Fin n → ℝ | 4 * ε * ((0 : Fin n₀ → ℝ) ⬝ᵥ 0) <
        |resid(S, (0 : Fin n₀ → ℝ)) - c * ((0 : Fin n₀ → ℝ) ⬝ᵥ 0)|} = ∅ := by
      ext S; simp
    rw [this, measure_empty]; exact bot_le
  have hθpos : 0 < θ ⬝ᵥ θ := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (θ i))
    (fun h => hθ (dotProduct_self_eq_zero.mp h.symm))
  have hD : MeasurableSet {z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) |
      4 * ε * (z.2 ⬝ᵥ z.2) < |resid(z.1, z.2) - c * (z.2 ⬝ᵥ z.2)|} :=
    measurableSet_lt (by fun_prop) (continuous_abs.measurable.comp
      (measurable_resid.sub
        (measurable_const.mul (measurable_dotProduct measurable_snd measurable_snd))))
  -- a Gaussian vector is a.e. nonzero
  have hg0 : ∀ᵐ g ∂G, g ≠ 0 := by
    have hbot : (⊥ : Submodule ℝ (Fin n₀ → ℝ)) ≠ ⊤ := by
      intro h
      have : Nontrivial (Fin n₀ → ℝ) := by
        have : NeZero n₀ := ⟨hn₀.ne'⟩
        infer_instance
      obtain ⟨x, hx⟩ := exists_ne (0 : Fin n₀ → ℝ)
      have : x ∈ (⊥ : Submodule ℝ (Fin n₀ → ℝ)) := h ▸ Submodule.mem_top
      exact hx (Submodule.mem_bot ℝ |>.mp this)
    have := pi_gaussianReal_submodule_eq_zero (⊥ : Submodule ℝ (Fin n₀ → ℝ)) hbot
    rw [ae_iff]
    have hset : {g : Fin n₀ → ℝ | ¬ g ≠ 0} =
        ((⊥ : Submodule ℝ (Fin n₀ → ℝ)) : Set (Fin n₀ → ℝ)) := by
      ext g; simp
    rw [hset]
    exact this
  -- the failure probability is the same for every nonzero vector
  have hconst : ∀ᵐ g ∂G, μ {S | 4 * ε * (g ⬝ᵥ g) < |resid(S, g) - c * (g ⬝ᵥ g)|} =
      μ {S | 4 * ε * (θ ⬝ᵥ θ) < |resid(S, θ) - c * (θ ⬝ᵥ θ)|} := by
    filter_upwards [hg0] with g hg
    have hgpos : 0 < g ⬝ᵥ g := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (g i))
      (fun h => hg (dotProduct_self_eq_zero.mp h.symm))
    set a : ℝ := Real.sqrt ((θ ⬝ᵥ θ) / (g ⬝ᵥ g)) with ha
    have ha0 : a ≠ 0 := (Real.sqrt_pos.mpr (div_pos hθpos hgpos)).ne'
    have hay : (a • g) ⬝ᵥ (a • g) = θ ⬝ᵥ θ := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, ha,
        Real.sq_sqrt (div_pos hθpos hgpos).le, div_mul_cancel₀ _ hgpos.ne']
    have h1 : {S : Fin n₀ → Fin n → ℝ | 4 * ε * (g ⬝ᵥ g) < |resid(S, g) - c * (g ⬝ᵥ g)|} =
        {S | 4 * ε * ((a • g) ⬝ᵥ (a • g)) < |resid(S, a • g) - c * ((a • g) ⬝ᵥ (a • g))|} := by
      ext S; exact (resid_dev_smul c (4 * ε) a ha0 S g).symm
    rw [h1]
    exact measure_resid_dev_eq c (4 * ε) hay
  -- Fubini: average over an independent Gaussian vector
  have hfub : μ {S | 4 * ε * (θ ⬝ᵥ θ) < |resid(S, θ) - c * (θ ⬝ᵥ θ)|} =
      (μ.prod G) {z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) |
        4 * ε * (z.2 ⬝ᵥ z.2) < |resid(z.1, z.2) - c * (z.2 ⬝ᵥ z.2)|} := by
    calc μ {S | 4 * ε * (θ ⬝ᵥ θ) < |resid(S, θ) - c * (θ ⬝ᵥ θ)|}
        = ∫⁻ _g, μ {S | 4 * ε * (θ ⬝ᵥ θ) < |resid(S, θ) - c * (θ ⬝ᵥ θ)|} ∂G := by simp
      _ = ∫⁻ g, μ {S | 4 * ε * (g ⬝ᵥ g) < |resid(S, g) - c * (g ⬝ᵥ g)|} ∂G :=
          (lintegral_congr_ae (hconst.mono fun g hg => hg.symm))
      _ = _ := (Measure.prod_apply_symm hD).symm
  rw [hfub, Measure.prod_apply hD]
  have hfull := ae_isUnit_det_gram_gaussianMatrix n n₀ hnn
  calc ∫⁻ S, G (Prod.mk S ⁻¹' {z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) |
          4 * ε * (z.2 ⬝ᵥ z.2) < |resid(z.1, z.2) - c * (z.2 ⬝ᵥ z.2)|}) ∂μ
      ≤ ∫⁻ _S, (ENNReal.ofReal (60 / (ε ^ 4 * (n : ℝ) ^ 2)) +
          ENNReal.ofReal (60 / (ε ^ 4 * (n₀ : ℝ) ^ 2))) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hfull] with S hS
        have hP := isOrthogonalProjection_gramProjector (Matrix.of S) hS
        have hA₁ := measure_projector_norm_sq_dev_le (gramProjector (Matrix.of S)) hP n
          (by rw [trace_gramProjector _ hS]; simp) hn hε
        have hA₂ := measure_projector_norm_sq_dev_le (1 : Matrix (Fin n₀) (Fin n₀) ℝ)
          (IsStarProjection.one _) n₀ (by simp) hn₀ hε
        calc G (Prod.mk S ⁻¹' {z : (Fin n₀ → Fin n → ℝ) × (Fin n₀ → ℝ) |
              4 * ε * (z.2 ⬝ᵥ z.2) < |resid(z.1, z.2) - c * (z.2 ⬝ᵥ z.2)|}) ≤
            G ({g : Fin n₀ → ℝ | ε * (n : ℝ) ≤
              |(gramProjector (Matrix.of S) *ᵥ g) ⬝ᵥ (gramProjector (Matrix.of S) *ᵥ g) - n|} ∪
              {g | ε * (n₀ : ℝ) ≤ |((1 : Matrix (Fin n₀) (Fin n₀) ℝ) *ᵥ g) ⬝ᵥ
                ((1 : Matrix (Fin n₀) (Fin n₀) ℝ) *ᵥ g) - n₀|}) :=
              measure_mono (resid_dev_subset hS hn hnn hε hε2)
          _ ≤ _ := (measure_union_le _ _).trans (add_le_add hA₁ hA₂)
    _ = _ := by simp

/-- **Bias concentration, absolute form.** If `‖θ‖² ≤ M`, the residual energy `‖(1 - P_S) θ‖²`
is within `ε` of `(1 - n/n₀) ‖θ‖²` except on an event of probability at most
`60 / (ε'⁴ n²) + 60 / (ε'⁴ n₀²)`, `ε' = min (ε / (8 M), 1/2)`. -/
theorem measure_resid_deviation_le_of_dotProduct_le (hn : 0 < n) (hnn : n ≤ n₀) {M ε : ℝ}
    (hM : 0 < M) (hε : 0 < ε) (θ : Fin n₀ → ℝ) (hθ : θ ⬝ᵥ θ ≤ M) :
    (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {S | ε ≤ |resid(S, θ) - (1 - (n : ℝ) / n₀) * (θ ⬝ᵥ θ)|} ≤
      ENNReal.ofReal (60 / (min (ε / (8 * M)) (1 / 2) ^ 4 * (n : ℝ) ^ 2)) +
        ENNReal.ofReal (60 / (min (ε / (8 * M)) (1 / 2) ^ 4 * (n₀ : ℝ) ^ 2)) := by
  have hε' : 0 < min (ε / (8 * M)) (1 / 2) := lt_min (by positivity) (by norm_num)
  refine le_trans (measure_mono ?_) (measure_resid_deviation_le hn hnn hε' (min_le_right _ _) θ)
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS ⊢
  have h1 : min (ε / (8 * M)) (1 / 2) ≤ ε / (8 * M) := min_le_left _ _
  have hθ0 : 0 ≤ θ ⬝ᵥ θ := Finset.sum_nonneg fun i _ => mul_self_nonneg (θ i)
  have h2 : 4 * min (ε / (8 * M)) (1 / 2) * (θ ⬝ᵥ θ) ≤ ε / 2 := by
    calc 4 * min (ε / (8 * M)) (1 / 2) * (θ ⬝ᵥ θ) ≤ 4 * (ε / (8 * M)) * M := by
          gcongr
      _ = ε / 2 := by field_simp; ring
  linarith

/-- **Convergence in probability of the bias of a Gaussian projector (7e).** For `n_k ≤ n₀_k`
with `n_k → ∞` and `θ_k ∈ ℝ^{n₀_k}` with `‖θ_k‖² ≤ M`, the probability that `‖(1 - P_{S_k}) θ_k‖²`
differs from `(1 - n_k/n₀_k) ‖θ_k‖²` by at least `ε` tends to `0`. Only `n_k → ∞` is needed, not
that `n_k / n₀_k` converges; the limit `(1 - δ/γ) ‖θ⋆‖²` follows when it does. -/
theorem tendsto_measure_resid_deviation (n₀ nn : ℕ → ℕ) (hnn : ∀ k, nn k ≤ n₀ k)
    (htop : Tendsto nn atTop atTop) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (θ : ∀ k, Fin (n₀ k) → ℝ) (hθ : ∀ k, θ k ⬝ᵥ θ k ≤ M) :
    Tendsto (fun k =>
      (Measure.pi fun _ : Fin (n₀ k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1)
        {S | ε ≤ |resid(S, θ k) - (1 - (nn k : ℝ) / n₀ k) * (θ k ⬝ᵥ θ k)|})
      atTop (𝓝 0) := by
  set ε' : ℝ := min (ε / (8 * M)) (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hnat : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htop
  have hnat₀ : Tendsto (fun k => (n₀ k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => by exact_mod_cast hnn k) hnat
  have hlim : ∀ u : ℕ → ℝ, Tendsto u atTop atTop →
      Tendsto (fun k => ENNReal.ofReal (60 / (ε' ^ 4 * u k ^ 2))) atTop (𝓝 0) := by
    intro u hu
    have h1 : Tendsto (fun k => ε' ^ 4 * u k ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) ((tendsto_pow_atTop (by norm_num)).comp hu)
    have h2 := (tendsto_const_nhds (x := (60 : ℝ))).div_atTop h1
    simpa using ENNReal.tendsto_ofReal h2
  have hsum := (hlim _ hnat).add (hlim _ hnat₀)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun k => bot_le) ?_
  filter_upwards [htop.eventually_gt_atTop 0] with k hk
  exact measure_resid_deviation_le_of_dotProduct_le hk (hnn k) hM hε (θ k) (hθ k)

end Main


end LinearRegression.DoubleDescent

end
