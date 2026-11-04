/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.TsumNonneg
public import LeanMachineLearning.SpinGlasses.AsymptoticGibbsApproximation

/-!
# Gram-matrix approximation for countably many atoms (Panchenko, Theorem 1.3)

`SpinGlasses.exists_continuousOn_gram_approx` treats a finitely supported measure
`Γ = ∑ᵢ wᵢ δ_{ρⁱ}`.  The book states Theorem 1.3 for an arbitrary atomic measure, which is needed
in Chapter 3 for the Ruelle probability cascades (countably many atoms).  Here the countable case
is deduced from the finite one by truncation: if `sₙ` is an increasing sequence of finite sets
exhausting the index type and `Wₙ = ∑_{i ∈ sₙ} wᵢ`, then the renormalized restrictions
`Γₙ = Wₙ⁻¹ ∑_{i ∈ sₙ} wᵢ δ_{ρⁱ}` satisfy the finite theorem with the *same* `m` and `F`, and both
sides converge as `n → ∞`:

* `𝔼 log ⟨φ(g)⟩_{Γₙ} → 𝔼 log ⟨φ(g)⟩_Γ` by dominated convergence, the bound being
  `2 (X + Y)` with `X = ∑ᵢ wᵢ φ(gᵢ)` and `Y = ∑ᵢ wᵢ φ(gᵢ)⁻¹`, integrable for sub-Gaussian `gᵢ`
  (`tendsto_integral_log_trunc`);
* the `Γₙ`-average of the bounded function `F` of `m` replicas converges to its `Γ`-average
  (`tendsto_sum_pi_trunc`).

## Main declarations

* `SpinGlasses.exists_continuousOn_gram_approx_countable`: Theorem 1.3 for a countable family
  with summable weights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped NNReal Matrix

namespace SpinGlasses

section Series

variable {ι : Type*} [Countable ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {v : ℝ≥0} {ψ : ℝ → ℝ} {A : ℝ}

/-- **A Gibbs average over countably many atoms of a nonnegative function of sub-Gaussian
variables** converges almost surely and is integrable, whenever `ψ x ≤ A e^{|x|}`. -/
theorem integrable_tsum_mul_comp (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (hm : ∀ i, Measurable (g i)) (hsub : ∀ i, HasSubgaussianMGF (g i) v P)
    (hψm : Measurable ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ : ∀ x, ψ x ≤ A * Real.exp |x|) :
    (∀ᵐ ω ∂P, Summable fun i => w i * ψ (g i ω)) ∧
      Integrable (fun ω => ∑' i, w i * ψ (g i ω)) P := by
  have hA0 : 0 ≤ A := by simpa using (hψ0 0).trans (hψ 0)
  have hle : ∀ i ω, w i * ψ (g i ω) ≤ (w i * A) * Real.exp (1 * |g i ω|) := fun i ω => by
    calc w i * ψ (g i ω) ≤ w i * (A * Real.exp |g i ω|) :=
          mul_le_mul_of_nonneg_left (hψ _) (hw0 i)
      _ = _ := by rw [one_mul]; ring
  have hbd : ∀ i, Integrable (fun ω => w i * ψ (g i ω)) P ∧
      ∫ ω, w i * ψ (g i ω) ∂P ≤ (w i * A) * (2 * Real.exp (v * 1 ^ 2 / 2)) := fun i => by
    obtain ⟨hI, hJ⟩ := (hsub i).integral_exp_abs_mul_le (hm i) 1
    have hfm : Measurable fun ω => w i * ψ (g i ω) := (hψm.comp (hm i)).const_mul _
    have hint : Integrable (fun ω => w i * ψ (g i ω)) P :=
      (hI.const_mul (w i * A)).mono' hfm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 i) (hψ0 _))]; exact hle i ω)
    refine ⟨hint, ?_⟩
    calc ∫ ω, w i * ψ (g i ω) ∂P ≤ ∫ ω, (w i * A) * Real.exp (1 * |g i ω|) ∂P :=
          integral_mono hint (hI.const_mul _) (hle i)
      _ = (w i * A) * ∫ ω, Real.exp (1 * |g i ω|) ∂P := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (mul_nonneg (hw0 i) hA0)
  refine ae_summable_and_integrable_tsum_of_nonneg
    (fun i => ((hψm.comp (hm i)).const_mul _).aemeasurable)
    (fun i ω => mul_nonneg (hw0 i) (hψ0 _)) (fun i => (hbd i).1) ?_
  have hS : Summable fun i => (w i * A) * (2 * Real.exp (v * 1 ^ 2 / 2)) :=
    (hw.mul_right A).mul_right _
  exact Summable.of_nonneg_of_le (fun i => integral_nonneg fun ω => mul_nonneg (hw0 i) (hψ0 _))
    (fun i => (hbd i).2) hS

end Series

section Truncation

variable {ι : Type*} [Countable ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {v : ℝ≥0} {φ : ℝ → ℝ} {A B : ℝ} {s : ℕ → Finset ι}

omit [Countable ι] in
/-- Along an increasing exhaustion of the index set by finite sets, partial sums of a summable
family converge to its sum. -/
theorem tendsto_finset_sum_exhaust {f : ι → ℝ} {a : ℝ} (hf : HasSum f a) (hs : Monotone s)
    (hsU : ∀ i, ∃ n, i ∈ s n) : Tendsto (fun n => ∑ i ∈ s n, f i) atTop (𝓝 a) :=
  hf.comp (tendsto_atTop_finset_of_monotone hs hsU)

omit [Countable ι] in
/-- **Jensen for the inverse on a finite subset:** `(∑_{i ∈ t} uᵢ xᵢ)⁻¹ ≤ ∑_{i ∈ t} uᵢ xᵢ⁻¹` for
weights `u ≥ 0` summing to `1` over `t` and `x > 0`. -/
theorem inv_finset_sum_mul_le (t : Finset ι) {u x : ι → ℝ} (hu0 : ∀ i, 0 ≤ u i)
    (hu1 : ∑ i ∈ t, u i = 1) (hx : ∀ i, 0 < x i) :
    (∑ i ∈ t, u i * x i)⁻¹ ≤ ∑ i ∈ t, u i * (x i)⁻¹ := by
  have := (convexOn_zpow (𝕜 := ℝ) (-1)).map_sum_le (t := t) (w := u) (p := x)
    (fun i _ => hu0 i) hu1 (fun i _ => hx i)
  simpa [smul_eq_mul] using this

omit [Countable ι] in
/-- A renormalized finite piece of a probability vector has a positive Gibbs average. -/
theorem sum_div_mul_pos (t : Finset ι) {w x : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (ht : 0 < ∑ i ∈ t, w i) (hx : ∀ i, 0 < x i) : 0 < ∑ i ∈ t, w i / (∑ j ∈ t, w j) * x i := by
  obtain ⟨i, hi, hwi⟩ : ∃ i ∈ t, 0 < w i := by
    by_contra h
    push Not at h
    exact absurd (Finset.sum_nonpos fun i hi => h i hi) (not_le.2 ht)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (div_nonneg (hw0 j) ht.le) (hx j).le)
    ⟨i, hi, mul_pos (div_pos hwi ht) (hx i)⟩

/-- **Truncation of the Gibbs measure does not change the free energy in the limit.**  Let `w` be
a probability vector on a countable set, `g i` sub-Gaussian, `φ > 0` continuous with
`φ x ≤ A e^{|x|}` and `(φ x)⁻¹ ≤ B e^{|x|}`, and `sₙ` finite sets increasing to the index type.
Then `𝔼 log ⟨φ(g)⟩_{Γₙ} → 𝔼 log ⟨φ(g)⟩_Γ`, where `Γₙ` is the renormalized restriction of `Γ` to
`sₙ`.  Dominated convergence with the integrable bound `2 (∑ wᵢ φ(gᵢ) + ∑ wᵢ φ(gᵢ)⁻¹)`. -/
theorem tendsto_integral_log_trunc (hw0 : ∀ i, 0 ≤ w i) (hw : HasSum w 1) (hs : Monotone s)
    (hsU : ∀ i, ∃ n, i ∈ s n) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (hφc : Continuous φ) (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) :
    Tendsto (fun n => ∫ ω, Real.log (∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * φ (g i ω)) ∂P)
      atTop (𝓝 (∫ ω, Real.log (∑' i, w i * φ (g i ω)) ∂P)) := by
  obtain ⟨hXs, hXi⟩ := integrable_tsum_mul_comp hw0 hw.summable hm hsub hφc.measurable
    (fun x => (hφ x).le) hA
  obtain ⟨hYs, hYi⟩ := integrable_tsum_mul_comp hw0 hw.summable hm hsub hφc.measurable.inv
    (fun x => (inv_pos.2 (hφ x)).le) hB
  have hW : Tendsto (fun n => ∑ i ∈ s n, w i) atTop (𝓝 1) := tendsto_finset_sum_exhaust hw hs hsU
  have hWev : ∀ᶠ n in atTop, 1 / 2 < ∑ i ∈ s n, w i :=
    hW.eventually (lt_mem_nhds (by norm_num))
  have hrew : ∀ (n : ℕ) (f : ι → ℝ), ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * f i =
      (∑ i ∈ s n, w i * f i) / ∑ j ∈ s n, w j := fun n f => by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => 2 * (∑' i, w i * φ (g i ω) + ∑' i, w i * (φ (g i ω))⁻¹))
    (Eventually.of_forall fun n => ?_) ?_ ((hXi.add hYi).const_mul 2) ?_
  · exact (Real.measurable_log.comp (Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (hm i)).const_mul _)).aestronglyMeasurable
  · filter_upwards [hWev] with n hn
    filter_upwards [hXs, hYs] with ω hX hY
    have hWn : 0 < ∑ i ∈ s n, w i := by linarith
    have hpos := sum_div_mul_pos (s n) hw0 hWn fun i => hφ (g i ω)
    have hu1 : ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) = 1 := by
      rw [← Finset.sum_div]; exact div_self hWn.ne'
    have h1 : ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * φ (g i ω) ≤
        2 * ∑' i, w i * φ (g i ω) := by
      rw [hrew n, div_le_iff₀ hWn]
      have := hX.sum_le_tsum (s n) fun i _ => mul_nonneg (hw0 i) (hφ (g i ω)).le
      have hX0 : 0 ≤ ∑' i, w i * φ (g i ω) := tsum_nonneg fun i => mul_nonneg (hw0 i) (hφ _).le
      nlinarith
    have h2 : (∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * φ (g i ω))⁻¹ ≤
        2 * ∑' i, w i * (φ (g i ω))⁻¹ := by
      refine (inv_finset_sum_mul_le (s n) (fun i => div_nonneg (hw0 i) hWn.le) hu1
        fun i => hφ (g i ω)).trans ?_
      rw [hrew n, div_le_iff₀ hWn]
      have := hY.sum_le_tsum (s n) fun i _ => mul_nonneg (hw0 i) (inv_pos.2 (hφ (g i ω))).le
      have hY0 : 0 ≤ ∑' i, w i * (φ (g i ω))⁻¹ :=
        tsum_nonneg fun i => mul_nonneg (hw0 i) (inv_pos.2 (hφ _)).le
      nlinarith
    rw [Real.norm_eq_abs]
    calc _ ≤ _ := abs_log_le_add_inv hpos
      _ ≤ _ := by linarith
  · filter_upwards [hXs] with ω hX
    obtain ⟨i0, hi0⟩ : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      have hw00 : w = 0 := funext fun i => le_antisymm (h i) (hw0 i)
      rw [hw00] at hw
      exact one_ne_zero (hw.unique hasSum_zero)
    have hXpos : 0 < ∑' i, w i * φ (g i ω) :=
      hX.tsum_pos (fun i => mul_nonneg (hw0 i) (hφ _).le) i0 (mul_pos hi0 (hφ _))
    have h1 := tendsto_finset_sum_exhaust (s := s) hX.hasSum hs hsU
    have h2 : Tendsto (fun n => ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * φ (g i ω)) atTop
        (𝓝 (∑' i, w i * φ (g i ω))) := by
      simp_rw [hrew]
      have h3 := h1.div hW one_ne_zero
      rw [div_one] at h3
      exact h3
    exact (Real.continuousAt_log hXpos.ne').tendsto.comp h2

end Truncation

section Replicas

variable {ι : Type*} [Countable ι] {w : ι → ℝ} {s : ℕ → Finset ι}

omit [Countable ι] in
/-- The product weights `∏ₗ w (j l)` on `Fin m → ι` of `m` i.i.d. replicas from a probability
vector sum to one. -/
theorem hasSum_prod_pi (hw0 : ∀ i, 0 ≤ w i) (hw : HasSum w 1) (m : ℕ) :
    HasSum (fun j : Fin m → ι => ∏ l, w (j l)) 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm : Summable fun p : ι × (Fin m → ι) => w p.1 * ∏ l, w (p.2 l) :=
      Summable.mul_of_nonneg (f := w) (g := fun j : Fin m → ι => ∏ l, w (j l)) hw.summable
        ih.summable hw0 fun j => Finset.prod_nonneg fun l _ => hw0 _
    have hw1 : HasSum (fun p : ι × (Fin m → ι) => w p.1 * ∏ l, w (p.2 l)) (1 * 1) :=
      HasSum.mul (f := w) (g := fun j : Fin m → ι => ∏ l, w (j l)) hw ih hsm
    rw [one_mul] at hw1
    refine ((Fin.consEquiv fun _ : Fin (m + 1) => ι).hasSum_iff).1 ?_
    convert hw1 using 1
    funext p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

omit [Countable ι] in
/-- **The `m`-replica average converges under truncation.**  For a bounded function `F` of `m`
indices, the average over `m` i.i.d. replicas from the renormalized restriction of `w` to `sₙ`
converges to the average over `m` replicas from `w`. -/
theorem tendsto_sum_pi_trunc (hw0 : ∀ i, 0 ≤ w i) (hw : HasSum w 1) (hs : Monotone s)
    (hsU : ∀ i, ∃ n, i ∈ s n) {m : ℕ} {F : (Fin m → ι) → ℝ} {M : ℝ} (hF : ∀ j, |F j| ≤ M) :
    Tendsto (fun n => (∑ j ∈ Fintype.piFinset (fun _ : Fin m => s n), (∏ l, w (j l)) * F j) /
        (∑ i ∈ s n, w i) ^ m) atTop (𝓝 (∑' j : Fin m → ι, (∏ l, w (j l)) * F j)) := by
  have hprod : ∀ j : Fin m → ι, 0 ≤ ∏ l, w (j l) := fun j => Finset.prod_nonneg fun l _ => hw0 _
  have hsum : Summable fun j : Fin m → ι => (∏ l, w (j l)) * F j :=
    Summable.of_norm_bounded ((hasSum_prod_pi hw0 hw m).summable.mul_left M) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hprod j), mul_comm]
      exact mul_le_mul_of_nonneg_right (hF j) (hprod j)
  have hmono : Monotone fun n => Fintype.piFinset (fun _ : Fin m => s n) := fun n n' h j hj => by
    simp only [Fintype.mem_piFinset] at hj ⊢
    exact fun l => hs h (hj l)
  have hex : ∀ j : Fin m → ι, ∃ n, j ∈ Fintype.piFinset (fun _ : Fin m => s n) := fun j => by
    have : ∀ l, ∀ᶠ n in atTop, j l ∈ s n := fun l => eventually_atTop.2
      ⟨(hsU (j l)).choose, fun n hn => hs hn (hsU (j l)).choose_spec⟩
    obtain ⟨n, hn⟩ := (Filter.eventually_all.2 this).exists
    exact ⟨n, Fintype.mem_piFinset.2 hn⟩
  have h1 := tendsto_finset_sum_exhaust (s := fun n => Fintype.piFinset (fun _ : Fin m => s n))
    hsum.hasSum hmono hex
  have hW : Tendsto (fun n => ∑ i ∈ s n, w i) atTop (𝓝 1) := tendsto_finset_sum_exhaust hw hs hsU
  have h2 := h1.div (hW.pow m) (by simp)
  simp only [one_pow, div_one] at h2
  exact h2

omit [Countable ι] in
/-- Sums over replicas drawn from a finite subset `t`, written with the renormalized weights
`w / W`, are sums over the product finset divided by `W ^ m`. -/
theorem sum_pi_subtype {m : ℕ} (t : Finset ι) (W : ℝ) (G : (Fin m → ι) → ℝ) :
    ∑ j : Fin m → t, (∏ l, w (j l) / W) * G (fun l => (j l : ι)) =
      (∑ j ∈ Fintype.piFinset (fun _ : Fin m => t), (∏ l, w (j l)) * G j) / W ^ m := by
  rw [Finset.sum_div]
  refine Finset.sum_bij (fun j _ => fun l => (j l : ι)) (fun j _ => ?_)
    (fun a _ b _ h => ?_) (fun j hj => ?_) (fun j _ => ?_)
  · exact Fintype.mem_piFinset.2 fun l => (j l).2
  · exact funext fun l => Subtype.ext (congrFun h l)
  · exact ⟨fun l => ⟨j l, Fintype.mem_piFinset.1 hj l⟩, Finset.mem_univ _, rfl⟩
  · simp [Finset.prod_div_distrib]
    ring

end Replicas

section Main

universe u u'

/-- **Theorem 1.3 for countably many atoms (Panchenko Eq. (1.64)).**  The conclusion of
`SpinGlasses.exists_continuousOn_gram_approx`, with the same `m` and `F`, holds for a probability
vector `w` on a countable index type (`HasSum w 1`, Gibbs averages `∑' i, w i * ·`) and
jointly Gaussian families `z`, `y` (every finite subfamily is jointly Gaussian) with covariances
`Cz (q i j)`, `Cy (q i j)` and variances at most `vz`, `vy`: the right side is the
`w`-average (a convergent series over `Fin m → ι`) of the continuous bounded function `F` of the
overlaps of `m` replicas.  The proof truncates to finite subsets and passes to the limit
(`tendsto_integral_log_trunc`, `tendsto_sum_pi_trunc`), so no new estimate is needed. -/
theorem exists_continuousOn_gram_approx_countable {Cz Cy : ℝ → ℝ} (hCz : Continuous Cz)
    (hCy : Continuous Cy) (vz vy : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (F : (Fin m → Fin m → ℝ) → ℝ),
      ContinuousOn F {Q | (Matrix.of fun l l' => Cz (Q l l')).PosSemidef ∧
        (Matrix.of fun l l' => Cy (Q l l')).PosSemidef} ∧ (∃ M, ∀ Q, |F Q| ≤ M) ∧
      ∀ (ι : Type u) [Countable ι] (w : ι → ℝ) (q : ι → ι → ℝ), (∀ i, 0 ≤ w i) → HasSum w 1 →
        ∀ (Ω : Type u') [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (z : ι → Ω → ℝ) (Ω' : Type u') [MeasurableSpace Ω'] (P' : Measure Ω')
          [IsProbabilityMeasure P'] (y : ι → Ω' → ℝ),
        (∀ i, Measurable (z i)) → (∀ t : Finset ι, HasGaussianLaw (fun ω (i : t) => z i ω) P) →
        (∀ i, ∫ ω, z i ω ∂P = 0) → (∀ i, ∫ ω, z i ω ^ 2 ∂P ≤ vz) →
        (∀ i j, ∫ ω, z i ω * z j ω ∂P = Cz (q i j)) →
        (∀ i, Measurable (y i)) → (∀ t : Finset ι, HasGaussianLaw (fun ω (i : t) => y i ω) P') →
        (∀ i, ∫ ω, y i ω ∂P' = 0) → (∀ i, ∫ ω, y i ω ^ 2 ∂P' ≤ vy) →
        (∀ i j, ∫ ω, y i ω * y j ω ∂P' = Cy (q i j)) →
        |((∫ ω, Real.log (∑' i, w i * (2 * Real.cosh (z i ω))) ∂P) -
            ∫ ω, Real.log (∑' i, w i * Real.exp (y i ω)) ∂P') -
          ∑' j : Fin m → ι, (∏ l, w (j l)) * F (fun l l' => q (j l) (j l'))| ≤ ε := by
  obtain ⟨m, F, hFc, ⟨M, hM⟩, hfin⟩ := exists_continuousOn_gram_approx.{u, u'} hCz hCy vz vy hε
  refine ⟨m, F, hFc, ⟨M, hM⟩, ?_⟩
  intro ι _ w q hw0 hw Ω _ P _ z Ω' _ P' _ y hzm hzg hz0 hzv hzc hym hyg hy0 hyv hyc
  classical
  -- an exhaustion of the index type by finite sets
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact one_ne_zero (hw.unique hasSum_empty)
  obtain ⟨f, hf⟩ := exists_surjective_nat ι
  let s : ℕ → Finset ι := fun n => (Finset.range (n + 1)).image f
  have hs : Monotone s := fun a b hab =>
    Finset.image_subset_image (Finset.range_mono (by omega))
  have hsU : ∀ i, ∃ n, i ∈ s n := fun i => by
    obtain ⟨k, rfl⟩ := hf i
    exact ⟨k, Finset.mem_image_of_mem f (Finset.mem_range.2 (by omega))⟩
  have hzsub : ∀ i, HasSubgaussianMGF (z i) vz P := fun i => by
    simpa using ((hzg {i}).eval ⟨i, Finset.mem_singleton_self i⟩
      ).hasSubgaussianMGF_of_integral_sq_le (hz0 i) (hzv i)
  have hysub : ∀ i, HasSubgaussianMGF (y i) vy P' := fun i => by
    simpa using ((hyg {i}).eval ⟨i, Finset.mem_singleton_self i⟩
      ).hasSubgaussianMGF_of_integral_sq_le (hy0 i) (hyv i)
  have hW : Tendsto (fun n => ∑ i ∈ s n, w i) atTop (𝓝 1) := tendsto_finset_sum_exhaust hw hs hsU
  have hWev : ∀ᶠ n in atTop, 0 < ∑ i ∈ s n, w i := hW.eventually (lt_mem_nhds one_pos)
  have hA := tendsto_integral_log_trunc (φ := fun x => 2 * Real.cosh x) (A := 2) (B := 1) hw0 hw
    hs hsU hzm hzsub (by fun_prop) (fun x => by positivity) two_cosh_le_exp_abs_mul
    inv_two_cosh_le_exp_abs_mul
  have hB := tendsto_integral_log_trunc (φ := Real.exp) (A := 1) (B := 1) hw0 hw hs hsU hym
    hysub Real.continuous_exp Real.exp_pos exp_le_exp_abs_mul inv_exp_le_exp_abs_mul
  have hT := tendsto_sum_pi_trunc hw0 hw hs hsU
    (F := fun j : Fin m → ι => F (fun l l' => q (j l) (j l'))) (M := M) fun j => hM _
  have hlim := (continuous_abs.tendsto _).comp ((hA.sub hB).sub hT)
  refine le_of_tendsto hlim ?_
  filter_upwards [hWev] with n hn
  have h1 : ∑ i : s n, w i / (∑ j ∈ s n, w j) = 1 := by
    rw [Finset.sum_coe_sort (s n) fun i => w i / (∑ j ∈ s n, w j), ← Finset.sum_div]
    exact div_self hn.ne'
  have h := hfin (s n) (fun i => w i / (∑ j ∈ s n, w j)) (fun i j => q i j)
    (fun i => div_nonneg (hw0 i) hn.le) h1 Ω P (fun i ω => z i ω) Ω' P' (fun i ω => y i ω)
    (fun i => hzm i) (hzg (s n)) (fun i => hz0 i) (fun i => hzv i) (fun i j => hzc i j)
    (fun i => hym i) (hyg (s n)) (fun i => hy0 i) (fun i => hyv i) (fun i j => hyc i j)
  have e := sum_pi_subtype (w := w) (s n) (∑ j ∈ s n, w j)
    (fun j : Fin m → ι => F (fun l l' => q (j l) (j l')))
  have eA : ∀ ω, ∑ i : s n, w i / (∑ j ∈ s n, w j) * (2 * Real.cosh (z i ω)) =
      ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * (2 * Real.cosh (z i ω)) := fun ω =>
    Finset.sum_coe_sort (s n) fun i => w i / (∑ j ∈ s n, w j) * (2 * Real.cosh (z i ω))
  have eB : ∀ ω, ∑ i : s n, w i / (∑ j ∈ s n, w j) * Real.exp (y i ω) =
      ∑ i ∈ s n, w i / (∑ j ∈ s n, w j) * Real.exp (y i ω) := fun ω =>
    Finset.sum_coe_sort (s n) fun i => w i / (∑ j ∈ s n, w j) * Real.exp (y i ω)
  simp only [eA, eB] at h
  rw [e] at h
  exact h

end Main

end SpinGlasses
