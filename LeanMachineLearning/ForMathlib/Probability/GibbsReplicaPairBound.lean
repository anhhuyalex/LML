/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.Data.Finset.SumBound

/-!
# Bounds for replica pair terms

A bounded multiplier of a covariance kernel contributes a mixed pair moment and a first-moment
correction. The finite-sum estimate counts the ordered pairs in a replica derivative.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace MeasureTheory

/-- A bounded multiplier and a pair kernel dominated by a nonnegative distance plus a
constant give a mixed pair moment and an error times the original first moment. -/
theorem integral_pi_pair_mul_bound
    {Ω α R ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R] [Fintype ι]
    (P : Measure Ω) (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    {e : R → ι} (he : Function.Injective e) (i j : ι)
    {f : Ω → (R → α) → ℝ}
    (hf : ∀ᵐ ω ∂P, Integrable (f ω) (Measure.pi fun _ : R => ν ω))
    (hf₁ : Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => ν ω)) P)
    {d : α → α → ℝ} (hd : Measurable fun a : α × α => d a.1 a.2)
    {L ε : ℝ} (hd0 : ∀ a b, 0 ≤ d a b) (hdL : ∀ a b, d a b ≤ L) (hε : 0 ≤ ε)
    (C : α → α → ℝ) (hC : ∀ a b, |C a b| ≤ d a b + ε)
    (H : Ω → (ι → α) → ℝ) {K : ℝ} (hH : ∀ ω σ, |H ω σ| ≤ K)
    (hM : AEStronglyMeasurable (fun ω => ∫ σ : ι → α,
      |f ω (σ ∘ e)| * d (σ i) (σ j) ∂(Measure.pi fun _ : ι => ν ω)) P) :
    let T (ω : Ω) :=
      ∫ σ : ι → α, f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ ∂(Measure.pi fun _ : ι => ν ω)
    (AEStronglyMeasurable T P → Integrable T P) ∧
    |∫ ω, T ω ∂P| ≤
      K * ((∫ ω, ∫ σ : ι → α, |f ω (σ ∘ e)| * d (σ i) (σ j)
        ∂(Measure.pi fun _ : ι => ν ω) ∂P) +
      ε * ∫ ω, ∫ a, |f ω a| ∂(Measure.pi fun _ : R => ν ω) ∂P) := by
  intro T
  let A (ω : Ω) := ∫ a, |f ω a| ∂(Measure.pi fun _ : R => ν ω)
  let M (ω : Ω) := ∫ σ : ι → α, |f ω (σ ∘ e)| * d (σ i) (σ j)
    ∂(Measure.pi fun _ : ι => ν ω)
  have hd₁ : Measurable fun σ : ι → α => d (σ i) (σ j) :=
    hd.comp (show Measurable (fun σ : ι → α => (σ i, σ j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have h₁ (ω : Ω) (hω : Integrable (f ω) (Measure.pi fun _ : R => ν ω)) :
      Integrable (fun σ : ι → α => |f ω (σ ∘ e)|) (Measure.pi fun _ : ι => ν ω) :=
    (measurePreserving_pi_comp_injective (ν ω) he).integrable_comp_of_integrable hω.abs
  have hA (ω : Ω) (hω : Integrable (f ω) (Measure.pi fun _ : R => ν ω)) :
      (∫ σ : ι → α, |f ω (σ ∘ e)| ∂(Measure.pi fun _ : ι => ν ω)) = A ω :=
    integral_pi_comp_injective (ν ω) he (fun a => |f ω a|) hω.abs.aestronglyMeasurable
  have hMi (ω : Ω) (hω : Integrable (f ω) (Measure.pi fun _ : R => ν ω)) :
      Integrable (fun σ : ι → α => |f ω (σ ∘ e)| * d (σ i) (σ j))
        (Measure.pi fun _ : ι => ν ω) :=
    ((h₁ ω hω).bdd_mul_of_abs_le (C := L) hd₁.aestronglyMeasurable
      (ae_of_all _ fun σ => by rw [abs_of_nonneg (hd0 _ _)]; exact hdL _ _)).congr
      (ae_of_all _ fun σ => mul_comm _ _)
  have hMint : Integrable M P := by
    refine (hf₁.const_mul L).mono' hM (hf.mono fun ω hω => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun σ => mul_nonneg (abs_nonneg _) (hd0 _ _))]
    calc
      M ω ≤ ∫ σ : ι → α, L * |f ω (σ ∘ e)| ∂(Measure.pi fun _ : ι => ν ω) :=
        integral_mono (hMi ω hω) ((h₁ ω hω).const_mul L) fun σ => by
          rw [mul_comm L]
          exact mul_le_mul_of_nonneg_left (hdL _ _) (abs_nonneg _)
      _ = L * A ω := by rw [integral_const_mul, hA ω hω]
  have hBd : ∀ᵐ ω ∂P, |∫ σ : ι → α, f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ
        ∂(Measure.pi fun _ : ι => ν ω)| ≤ K * (M ω + ε * A ω) := by
    filter_upwards [hf] with ω hω
    have hg := ((hMi ω hω).add ((h₁ ω hω).const_mul ε)).const_mul K
    have hp (σ : ι → α) : |f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ| ≤
        K * (|f ω (σ ∘ e)| * d (σ i) (σ j) + ε * |f ω (σ ∘ e)|) := by
      rw [abs_mul, abs_mul]
      calc _ ≤ (|f ω (σ ∘ e)| * (d (σ i) (σ j) + ε)) * K :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC _ _) (abs_nonneg _)) (hH _ _)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (add_nonneg (hd0 _ _) hε))
        _ = _ := by ring
    have hh := norm_integral_le_of_norm_le
      (f := fun σ : ι → α => f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ) hg (ae_of_all _ fun σ => by
      change ‖f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ‖ ≤
        K * (|f ω (σ ∘ e)| * d (σ i) (σ j) + ε * |f ω (σ ∘ e)|)
      simpa only [Real.norm_eq_abs] using hp σ)
    change ‖∫ σ : ι → α, f ω (σ ∘ e) * C (σ i) (σ j) * H ω σ
        ∂(Measure.pi fun _ : ι => ν ω)‖ ≤
      ∫ σ : ι → α, K * (|f ω (σ ∘ e)| * d (σ i) (σ j) + ε * |f ω (σ ∘ e)|)
        ∂(Measure.pi fun _ : ι => ν ω) at hh
    rw [integral_const_mul, integral_add (hMi ω hω) ((h₁ ω hω).const_mul ε),
      integral_const_mul, hA ω hω] at hh
    simpa only [Real.norm_eq_abs] using hh
  have hI := (hMint.add (hf₁.const_mul ε)).const_mul K
  have hBn := hBd.mono fun ω hω => by
    simpa only [← Real.norm_eq_abs] using hω
  refine ⟨fun hm => hI.mono' hm hBn, ?_⟩
  have h := norm_integral_le_of_norm_le hI hBn
  change ‖∫ ω, T ω ∂P‖ ≤ ∫ ω, K * (M ω + ε * A ω) ∂P at h
  rw [Real.norm_eq_abs, integral_const_mul, integral_add hMint (hf₁.const_mul ε),
    integral_const_mul] at h
  exact h

end MeasureTheory

namespace Finset

/-- The absolute bound for the four groups with zero, one and two fresh replicas.
The original pairs are ordered and the diagonal is omitted. -/
theorem abs_replica_groups_le
    {R : Type*} [Fintype R] [DecidableEq R]
    (A : R → R → ℝ) (B C : R → ℝ) (D : ℝ) {a b c d : ℝ}
    (ha0 : 0 ≤ a) (hA : ∀ i j, i ≠ j → |A i j| ≤ a)
    (hB : ∀ i, |B i| ≤ b) (hC : ∀ i, |C i| ≤ c) (hD : |D| ≤ d) :
    let n : ℝ := Fintype.card R
    |(∑ i, ∑ j ∈ univ.erase i, A i j) - n * ∑ i, B i - n * ∑ i, C i +
        n * (n + 1) * D| ≤ n ^ 2 * a + n ^ 2 * b + n ^ 2 * c + n * (n + 1) * d := by
  intro n
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hinner (i : R) : |∑ j ∈ univ.erase i, A i j| ≤ n * a := by
    refine (abs_sum_le_sum_of_abs_le _ fun j hj => hA i j (ne_of_mem_erase hj).symm).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have h : ((univ.erase i).card : ℝ) ≤ (Fintype.card R : ℝ) := by
      exact_mod_cast card_le_univ (univ.erase i)
    exact mul_le_mul_of_nonneg_right h ha0
  have hA' : |∑ i, ∑ j ∈ univ.erase i, A i j| ≤ n ^ 2 * a := by
    simpa only [sq, mul_assoc] using abs_sum_le_card_mul_of_abs_le _ hinner
  have hBC (G : R → ℝ) (k : ℝ) (hG : ∀ i, |G i| ≤ k) :
      |n * ∑ i, G i| ≤ n ^ 2 * k := by
    rw [abs_mul, abs_of_nonneg hn]
    simpa only [sq, mul_assoc] using
      mul_le_mul_of_nonneg_left (abs_sum_le_card_mul_of_abs_le G hG) hn
  have hn' : 0 ≤ n * (n + 1) := mul_nonneg hn (by positivity)
  have hD' : |n * (n + 1) * D| ≤ n * (n + 1) * d := by
    rw [abs_mul, abs_of_nonneg hn']
    exact mul_le_mul_of_nonneg_left hD hn'
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add hA' (hBC B b hB))) (hBC C c hC))) hD')

end Finset

namespace MeasureTheory

/-- The pair bound passes through two environment averages once the individual term and
its mixed moment are measurable for the product law. -/
theorem integrable_integral_pi_pair_mul_and_abs_le
    {Ω W α R ι : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace α]
    [Fintype R] [Fintype ι]
    (P : Measure Ω) [SFinite P] (Q : Measure W) [SFinite Q]
    (ν : Ω × W → Measure α) [∀ p, IsProbabilityMeasure (ν p)]
    {e : R → ι} (he : Function.Injective e) (i j : ι)
    {f : Ω × W → (R → α) → ℝ}
    (hf : ∀ᵐ p ∂P.prod Q, Integrable (f p) (Measure.pi fun _ : R => ν p))
    (hf₁ : Integrable (fun p => ∫ a, |f p a| ∂(Measure.pi fun _ : R => ν p)) (P.prod Q))
    {d : α → α → ℝ} (hd : Measurable fun a : α × α => d a.1 a.2)
    {L ε : ℝ} (hd0 : ∀ a b, 0 ≤ d a b) (hdL : ∀ a b, d a b ≤ L) (hε : 0 ≤ ε)
    (C : α → α → ℝ) (hC : ∀ a b, |C a b| ≤ d a b + ε)
    (H : Ω × W → (ι → α) → ℝ) {K : ℝ} (hK : 0 ≤ K) (hH : ∀ p σ, |H p σ| ≤ K)
    (hM : AEStronglyMeasurable (fun p => ∫ σ : ι → α,
      |f p (σ ∘ e)| * d (σ i) (σ j) ∂(Measure.pi fun _ : ι => ν p)) (P.prod Q))
    (hT : AEStronglyMeasurable (fun p => ∫ σ : ι → α,
      f p (σ ∘ e) * C (σ i) (σ j) * H p σ ∂(Measure.pi fun _ : ι => ν p)) (P.prod Q))
    {m : ℝ} (hm : ∫ p, ∫ σ : ι → α,
      |f p (σ ∘ e)| * d (σ i) (σ j) ∂(Measure.pi fun _ : ι => ν p) ∂P.prod Q ≤ m) :
    let T (p : Ω × W) :=
      ∫ σ : ι → α, f p (σ ∘ e) * C (σ i) (σ j) * H p σ ∂(Measure.pi fun _ : ι => ν p)
    Integrable (fun ω => ∫ w, T (ω, w) ∂Q) P ∧
      |∫ ω, ∫ w, T (ω, w) ∂Q ∂P| ≤
        K * (m + ε * ∫ p, ∫ a, |f p a| ∂(Measure.pi fun _ : R => ν p) ∂P.prod Q) := by
  intro T
  obtain ⟨hTi, hTd⟩ :=
    integral_pi_pair_mul_bound (P.prod Q) ν he i j hf hf₁ hd hd0 hdL hε C hC H hH hM
  have hint : Integrable T (P.prod Q) := hTi hT
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [← integral_prod T hint]
  exact hTd.trans (mul_le_mul_of_nonneg_left (add_le_add hm le_rfl) hK)

/-- Bounding the individual integrals bounds the integral of their four-group combination. -/
theorem abs_integral_replica_groups_le
    {Ω R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R] (P : Measure Ω)
    (A : R → R → Ω → ℝ) (B C : R → Ω → ℝ) (D : Ω → ℝ)
    (hAi : ∀ i j, i ≠ j → Integrable (A i j) P)
    (hBi : ∀ i, Integrable (B i) P) (hCi : ∀ i, Integrable (C i) P) (hDi : Integrable D P)
    {a b c d : ℝ} (ha0 : 0 ≤ a)
    (hA : ∀ i j, i ≠ j → |∫ ω, A i j ω ∂P| ≤ a)
    (hB : ∀ i, |∫ ω, B i ω ∂P| ≤ b) (hC : ∀ i, |∫ ω, C i ω ∂P| ≤ c)
    (hD : |∫ ω, D ω ∂P| ≤ d) :
    let n : ℝ := Fintype.card R
    |∫ ω, (∑ i, ∑ j ∈ Finset.univ.erase i, A i j ω) -
        n * (∑ i, B i ω) - n * (∑ i, C i ω) + n * (n + 1) * D ω ∂P| ≤
      n ^ 2 * a + n ^ 2 * b + n ^ 2 * c + n * (n + 1) * d := by
  intro n
  have hAx (i : R) : Integrable (fun ω => ∑ j ∈ Finset.univ.erase i, A i j ω) P :=
    integrable_finsetSum _ fun j hj => hAi i j (Finset.ne_of_mem_erase hj).symm
  have hA' := integrable_finsetSum Finset.univ (fun i _ => hAx i)
  have hB' := (integrable_finsetSum Finset.univ (fun i _ => hBi i)).const_mul n
  have hC' := (integrable_finsetSum Finset.univ (fun i _ => hCi i)).const_mul n
  have hAB : Integrable (fun ω => (∑ i, ∑ j ∈ Finset.univ.erase i, A i j ω) -
      n * (∑ i, B i ω)) P := hA'.sub hB'
  have hABC : Integrable (fun ω => (∑ i, ∑ j ∈ Finset.univ.erase i, A i j ω) -
      n * (∑ i, B i ω) - n * (∑ i, C i ω)) P := hAB.sub hC'
  rw [integral_add hABC (hDi.const_mul (n * (n + 1))),
    integral_sub hAB hC', integral_sub hA' hB',
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => hAx i),
    integral_finsetSum Finset.univ (fun i _ => hBi i),
    integral_finsetSum Finset.univ (fun i _ => hCi i)]
  have eqAx (i : R) :
      ∫ ω, (∑ j ∈ Finset.univ.erase i, A i j ω) ∂P =
        ∑ j ∈ Finset.univ.erase i, ∫ ω, A i j ω ∂P :=
    integral_finsetSum _ fun j hj => hAi i j (Finset.ne_of_mem_erase hj).symm
  simp_rw [eqAx]
  exact Finset.abs_replica_groups_le _ _ _ _ ha0 hA hB hC hD

end MeasureTheory
