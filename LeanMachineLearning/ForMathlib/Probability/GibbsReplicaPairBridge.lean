/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag

/-!
# The two-replica combination: covariance form and the average of its second derivative

Model-free algebra for `replicaPairCombination` (Talagrand (2.24)--(2.25) and Lemma 1.6.3):

* `replica_covariance_combination_cancel_diagonal`, `replica_covariance_combination_eq_two_sum_lt`,
  `neg_half_replica_covariance_offDiag`: the four-term covariance combination of a kernel with
  constant diagonal is `2 ∑_{ℓ<ℓ'} - 2n ∑_ℓ + n(n+1)`, i.e. twice `replicaPairCombination`;
* `replicaPairCombination_eq_half_replica_covariance_combination`: the same statement for
  `replicaPairCombination` itself;
* `replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage`: for a bounded observable `X` with
  `X² = C`, the replica difference of replica differences against `c X` is `2 c` times the
  `replicaPairAverage` of the kernel `X ⊗ X`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace MeasureTheory

/-- The diagonal terms of the replica covariance combination cancel whenever the
covariance has a constant diagonal. This is the algebraic step from the general
Gaussian replica derivative to its cavity form; it does not assume symmetry of `U`. -/
theorem replica_covariance_combination_cancel_diagonal
    {R α : Type*} [Fintype R] [DecidableEq R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (τ : Option (Option R) → α) :
    (∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) -
        (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) =
      (∑ r : R, ∑ r' : R, if r = r' then 0 else
          U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) := by
  have hs (r : R) :
      (∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) =
        C + ∑ r' : R, if r = r' then 0 else
          U (τ (some (some r))) (τ (some (some r'))) := by
    have hh (r' : R) : U (τ (some (some r))) (τ (some (some r'))) =
        (if r = r' then C else 0) +
          (if r = r' then 0 else U (τ (some (some r))) (τ (some (some r')))) := by
      split_ifs with hr
      · subst r'; simp [hdiag]
      · simp
    rw [Finset.sum_congr rfl fun r' _ => hh r', Finset.sum_add_distrib]
    simp
  simp_rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hdiag (τ (some none))]
  ring

/-- For a symmetric covariance kernel, the surviving ordered off-diagonal
terms are twice the strictly ordered replica pairs. This combines diagonal
cancellation with the generic finite-sum reindexing, while remaining
independent of the cavity model. -/
theorem replica_covariance_combination_eq_two_sum_lt
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    (∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) -
        (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) =
      2 * ∑ p : R × R with p.1 < p.2,
          U (τ (some (some p.1))) (τ (some (some p.2))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) := by
  rw [replica_covariance_combination_cancel_diagonal U C hdiag τ,
    sum_sum_offDiag_eq_two_sum_lt
      (fun r r' => U (τ (some (some r))) (τ (some (some r'))))
      (fun r r' => hsym _ _)]

/-- The square-parameter chain rule multiplies the clean angle bracket by
`-1 / 2`. This algebraic form reverses the covariance kernel and gives the
three coefficients used by Talagrand's cavity derivative. -/
theorem neg_half_replica_covariance_offDiag
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ)
    (τ : Option (Option R) → α) :
    -(2 * ∑ p : R × R with p.1 < p.2,
        U (τ (some (some p.1))) (τ (some (some p.2))) -
      2 * (Fintype.card R : ℝ) * ∑ r : R,
        U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        U (τ (some none)) (τ none)) / 2 =
    (∑ p : R × R with p.1 < p.2,
        -U (τ (some (some p.1))) (τ (some (some p.2)))) -
      (Fintype.card R : ℝ) * ∑ r : R,
        -U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 *
        (-U (τ (some none)) (τ none)) := by
  simp only [Finset.sum_neg_distrib]
  ring

/-- Connection with the 4-term replica covariance combination :
for any kernel with constant diagonal, `replicaPairCombination` is exactly half of the 4-term
combination. -/
theorem replicaPairCombination_eq_half_replica_covariance_combination
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    replicaPairCombination U τ =
      ((∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
          2 * (Fintype.card R : ℝ) *
            (∑ r : R, U (τ (some (some r))) (τ (some none))) -
          (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
          (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
            U (τ (some none)) (τ none)) / 2 := by
  rw [replica_covariance_combination_eq_two_sum_lt U C hdiag hsym τ]
  dsimp only [replicaPairCombination]
  ring

/-- **Second derivative of a replica average in a linear coupling** (the model-free core of the
`E'_Y` term of Proposition 2.2.3, and of the diagonal bookkeeping of the `E'_a` term).
For bounded observables `F` and `X`, the replica difference of the replica differences against
`c X` is `2 c` times the two-fresh-replica average of the kernel `X ⊗ X` plus `c` times the
replica difference of the diagonal `X²`:
`∑_i cov(F X_i, ∑ c X) - n cov(F X_*, ∑ c X) = 2 c ⟨F · replicaPairCombination (X ⊗ X)⟩ +
c ⟨F (∑_i X_i² - n X_*²)⟩`. No symmetry or constant-diagonal hypothesis is needed: the diagonal
`X²` is kept as an explicit term (it vanishes for `X² = C`, and equals the `u''`-free part
`(u')²` of the potential kernel when `X = ε u'(S)`). The proof moves everything to `|R| + 2`
replicas (`replicaDiff_eq_integral`), expands `(∑ X)²` with `sum_filter_lt_add_swap`, and
exchanges the two fresh replicas (`integral_replica_swap_fresh`). -/
theorem replicaDiffWith_replicaDiff_eq
    {α R : Type*} [MeasurableSpace α] [Fintype R] [LinearOrder R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ}
    (hFb : ∀ σ, |F σ| ≤ M) (X : α → ℝ) (hX : Measurable X) {B : ℝ} (hXb : ∀ a, |X a| ≤ B)
    (c : ℝ) :
    replicaDiffWith (fun G => replicaDiff ν G (fun a => c * X a)) F X =
      2 * c * replicaPairAverage ν F (fun a b => X a * X b) +
        c * replicaDiff ν F (fun a => X a * X a) := by
  classical
  set n : ℝ := (Fintype.card R : ℝ) with hn
  set P2 : Measure (Option (Option R) → α) := Measure.pi fun _ => ν with hP2
  set f : (Option (Option R) → α) → ℝ := fun σ => F fun j => σ (some (some j)) with hf
  set S : (Option (Option R) → α) → ℝ := fun σ => ∑ r, X (σ (some (some r))) with hS
  set Xa : (Option (Option R) → α) → ℝ := fun σ => X (σ (some none)) with hXa
  set Xb : (Option (Option R) → α) → ℝ := fun σ => X (σ none) with hXb'
  set W : (Option (Option R) → α) → ℝ := fun σ => ∑ o : Option R, c * X (σ (some o)) -
    (n + 1) * (c * X (σ none)) with hW
  -- measurability and bounds of the atoms
  have hXm (k : Option (Option R)) : Measurable fun σ : Option (Option R) → α => X (σ k) :=
    hX.comp (measurable_pi_apply k)
  have hXbd (k : Option (Option R)) : ∃ K, ∀ σ : Option (Option R) → α, |X (σ k)| ≤ K :=
    ⟨B, fun σ => hXb _⟩
  have hfm : Measurable f := hF.comp (by fun_prop)
  have hfbd : ∃ K, ∀ σ, |f σ| ≤ K := ⟨M, fun σ => hFb _⟩
  have hSm : Measurable S := Finset.measurable_sum _ fun r _ => hXm _
  have hSbd : ∃ K, ∀ σ, |S σ| ≤ K := exists_abs_le_sum _ fun r _ => hXbd _
  have hcXm (k : Option (Option R)) : Measurable fun σ : Option (Option R) → α => c * X (σ k) :=
    (hXm k).const_mul c
  have hcXbd (k : Option (Option R)) : ∃ K, ∀ σ : Option (Option R) → α, |c * X (σ k)| ≤ K :=
    exists_abs_le_mul (exists_abs_le_const c) (hXbd k)
  have hWm : Measurable W :=
    (Finset.measurable_sum _ fun o _ => hcXm _).sub ((hcXm _).const_mul _)
  have hWbd : ∃ K, ∀ σ, |W σ| ≤ K :=
    exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hcXbd _)
      (exists_abs_le_mul (exists_abs_le_const _) (hcXbd _))
  have hint (g : (Option (Option R) → α) → ℝ) (hg : Measurable g) (hb : ∃ K, ∀ σ, |g σ| ≤ K) :
      Integrable g P2 := by
    obtain ⟨K, hK⟩ := hb
    exact integrable_of_measurable_bound hg hK
  -- step 1: each replica difference over `Option R` is one integral over `Option (Option R)`
  have key1 (i : Option R) :
      replicaDiff ν (fun τ : Option R → α => F (fun j => τ (some j)) * X (τ i))
          (fun a => c * X a) =
        ∫ σ, f σ * X (σ (some i)) * W σ ∂P2 := by
    have hGm : Measurable fun τ : Option R → α => F (fun j => τ (some j)) * X (τ i) :=
      (hF.comp (by fun_prop)).mul (hX.comp (measurable_pi_apply i))
    rw [replicaDiff_eq_integral ν _ hGm (M := M * B) (fun τ => by
        rw [abs_mul]
        exact mul_le_mul (hFb _) (hXb _) (abs_nonneg _)
          ((abs_nonneg _).trans (hFb fun j => τ (some j))))
      (fun a => c * X a) (hX.const_mul c) (B := |c| * B) (fun a => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb a) (abs_nonneg _))]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [W, f, Fintype.card_option, Nat.cast_succ, hn]
  simp only [replicaDiffWith]
  rw [Finset.sum_congr rfl fun i _ => key1 (some i), key1 none]
  -- step 2: one integral
  have hI (k : Option (Option R)) : Integrable (fun σ => f σ * X (σ k) * W σ) P2 :=
    hint _ ((hfm.mul (hXm k)).mul hWm) (exists_abs_le_mul (exists_abs_le_mul hfbd (hXbd k)) hWbd)
  have hcomb : (∑ i : R, ∫ σ, f σ * X (σ (some (some i))) * W σ ∂P2) -
      n * ∫ σ, f σ * X (σ (some none)) * W σ ∂P2 =
      ∫ σ, (∑ i : R, f σ * X (σ (some (some i))) * W σ -
        n * (f σ * X (σ (some none)) * W σ)) ∂P2 := by
    rw [integral_sub (integrable_finsetSum _ fun i _ => hI _) ((hI _).const_mul n),
      integral_finsetSum _ fun i _ => hI _, integral_const_mul]
  rw [hcomb]
  -- step 3: swap the two fresh replicas
  have hK : Measurable fun p : α × α => X p.1 * X p.2 :=
    (hX.comp measurable_fst).mul (hX.comp measurable_snd)
  have hswap : ∫ σ, f σ * (S σ * Xb σ) ∂P2 = ∫ σ, f σ * (S σ * Xa σ) ∂P2 := by
    have hr (k : Option (Option R)) (r : R) : Integrable
        (fun σ => f σ * (X (σ (some (some r))) * X (σ k))) P2 :=
      hint _ (hfm.mul ((hXm _).mul (hXm k)))
        (exists_abs_le_mul hfbd (exists_abs_le_mul (hXbd _) (hXbd _)))
    simp only [S, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun r _ => hr none r, integral_finsetSum _ fun r _ => hr (some none) r]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact integral_replica_swap_fresh ν F hF (K := fun a b => X a * X b) hK r
  -- step 4: the pair combination of `X ⊗ X` and the pointwise identity
  have hXam : Measurable Xa := hXm _
  have hXbm : Measurable Xb := hXm _
  have hXabd : ∃ K, ∀ σ, |Xa σ| ≤ K := hXbd _
  have hXbbd : ∃ K, ∀ σ, |Xb σ| ≤ K := hXbd _
  set Q : (Option (Option R) → α) → ℝ := fun σ =>
    ∑ r, X (σ (some (some r))) * X (σ (some (some r))) with hQ
  have hQm : Measurable Q := Finset.measurable_sum _ fun r _ => (hXm _).mul (hXm _)
  have hQbd : ∃ K, ∀ σ, |Q σ| ≤ K :=
    exists_abs_le_sum _ fun r _ => exists_abs_le_mul (hXbd _) (hXbd _)
  set A : (Option (Option R) → α) → ℝ := fun σ => f σ * (S σ * S σ - Q σ -
    2 * n * (S σ * Xa σ) + n * (n + 1) * (Xa σ * Xb σ)) with hA
  have hAm : Measurable A :=
    hfm.mul ((((hSm.mul hSm).sub hQm).sub (((hSm.mul hXam).const_mul _))).add
      ((hXam.mul hXbm).const_mul _))
  have hAbd : ∃ K, ∀ σ, |A σ| ≤ K :=
    exists_abs_le_mul hfbd (exists_abs_le_add (exists_abs_le_sub (exists_abs_le_sub
      (exists_abs_le_mul hSbd hSbd) hQbd) (exists_abs_le_mul (exists_abs_le_const _)
        (exists_abs_le_mul hSbd hXabd)))
      (exists_abs_le_mul (exists_abs_le_const _) (exists_abs_le_mul hXabd hXbbd)))
  have hcombpt (σ : Option (Option R) → α) :
      f σ * replicaPairCombination (fun a b => X a * X b) σ = A σ / 2 := by
    have h2 : 2 * ∑ p : R × R with p.1 < p.2,
        X (σ (some (some p.1))) * X (σ (some (some p.2))) = S σ * S σ - Q σ := by
      have := sum_filter_lt_add_swap
        (fun a b : R => X (σ (some (some a))) * X (σ (some (some b))))
      simp only [S, Q, Finset.sum_mul_sum]
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    have hSa : (∑ r : R, X (σ (some (some r))) * X (σ (some none))) = S σ * Xa σ := by
      simp only [S, Xa, Finset.sum_mul]
    simp only [replicaPairCombination, hSa, A, hn]
    linear_combination (f σ / 2) * h2
  -- step 5: assemble
  set D : (Option (Option R) → α) → ℝ := fun σ => f σ * (Q σ - n * (Xa σ * Xa σ)) with hD
  have hDint : Integrable D P2 :=
    hint D (hfm.mul (hQm.sub ((hXam.mul hXam).const_mul _)))
      (exists_abs_le_mul hfbd (exists_abs_le_sub hQbd
        (exists_abs_le_mul (exists_abs_le_const _) (exists_abs_le_mul hXabd hXabd))))
  have hpt (σ : Option (Option R) → α) :
      (∑ i : R, f σ * X (σ (some (some i))) * W σ -
        n * (f σ * X (σ (some none)) * W σ)) =
      c * A σ + ((n + 1) * c * (f σ * (S σ * Xa σ)) - (n + 1) * c * (f σ * (S σ * Xb σ))) +
        c * D σ := by
    have hW' : W σ = c * (Xa σ + S σ) - (n + 1) * (c * Xb σ) := by
      simp only [W, Fintype.sum_option, ← Finset.mul_sum, S, Xa, Xb]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    rw [hW']
    simp only [A, D]
    change f σ * S σ * _ - _ = _
    ring
  have h1 : Integrable (fun σ => f σ * (S σ * Xa σ)) P2 :=
    hint _ (hfm.mul (hSm.mul hXam)) (exists_abs_le_mul hfbd (exists_abs_le_mul hSbd hXabd))
  have h2 : Integrable (fun σ => f σ * (S σ * Xb σ)) P2 :=
    hint _ (hfm.mul (hSm.mul hXbm)) (exists_abs_le_mul hfbd (exists_abs_le_mul hSbd hXbbd))
  have hA' : Integrable A P2 := hint A hAm hAbd
  have hg : Integrable (fun σ => (n + 1) * c * (f σ * (S σ * Xa σ)) -
      (n + 1) * c * (f σ * (S σ * Xb σ))) P2 := (h1.const_mul _).sub (h2.const_mul _)
  have hAg : Integrable (fun σ => c * A σ + ((n + 1) * c * (f σ * (S σ * Xa σ)) -
      (n + 1) * c * (f σ * (S σ * Xb σ)))) P2 := (hA'.const_mul c).add hg
  rw [integral_congr_ae (ae_of_all _ hpt), integral_add hAg (hDint.const_mul c),
    integral_add (hA'.const_mul c) hg,
    integral_sub (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hswap]
  have hpair : replicaPairAverage ν F (fun a b => X a * X b) = (∫ σ, A σ ∂P2) / 2 := by
    rw [replicaPairAverage_eq, ← integral_div]
    exact integral_congr_ae (ae_of_all _ hcombpt)
  have hdiag : replicaDiff ν F (fun a => X a * X a) = ∫ σ, D σ ∂P2 := by
    have hG : Measurable fun τ : Option R → α => F (fun j => τ (some j)) *
        (∑ i, X (τ (some i)) * X (τ (some i)) - (Fintype.card R : ℝ) * (X (τ none) * X (τ none))) :=
      (hF.comp (by fun_prop)).mul ((Finset.measurable_sum _ fun i _ =>
        (hX.comp (measurable_pi_apply _)).mul (hX.comp (measurable_pi_apply _))).sub
        (((hX.comp (measurable_pi_apply _)).mul (hX.comp (measurable_pi_apply _))).const_mul _))
    rw [replicaDiff_eq_integral ν F hF hFb (fun a => X a * X a) (hX.mul hX) (B := B * B)
      (fun a => by
        rw [abs_mul]
        exact mul_le_mul (hXb a) (hXb a) (abs_nonneg _) ((abs_nonneg _).trans (hXb a))),
      ← integral_pi_comp_injective ν (Option.some_injective (Option R)) _ hG.aestronglyMeasurable]
  rw [hpair, hdiag]
  ring

/-- **The same, for a kernel with constant diagonal** (`X² = C`): the correction vanishes. -/
theorem replicaDiffWith_replicaDiff_eq_two_mul_replicaPairAverage
    {α R : Type*} [MeasurableSpace α] [Fintype R] [LinearOrder R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ}
    (hFb : ∀ σ, |F σ| ≤ M) (X : α → ℝ) (hX : Measurable X) {B : ℝ} (hXb : ∀ a, |X a| ≤ B)
    (C c : ℝ) (hC : ∀ a, X a * X a = C) :
    replicaDiffWith (fun G => replicaDiff ν G (fun a => c * X a)) F X =
      2 * c * replicaPairAverage ν F (fun a b => X a * X b) := by
  rw [replicaDiffWith_replicaDiff_eq ν F hF hFb X hX hXb c]
  have : replicaDiff ν F (fun a => X a * X a) = 0 := by
    simp only [hC, replicaDiff_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_self]
  rw [this, mul_zero, add_zero]

end MeasureTheory
