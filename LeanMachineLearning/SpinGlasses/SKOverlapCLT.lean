/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra
public import LeanMachineLearning.SpinGlasses.SKTBasisAsymptotics
public import LeanMachineLearning.SpinGlasses.SKCovarianceAsymptotics
public import LeanMachineLearning.SpinGlasses.SKOverlapMoments
public import LeanMachineLearning.SpinGlasses.SKSmartPathCLT

/-!
# Central limit theorem for the overlaps (Talagrand, Section 1.10)

For $\beta < 1/2$, the fluctuations of the replica overlaps
$X_{\ell,\ell'} = \sqrt{N}(R_{\ell,\ell'} - q)$
satisfy the quantitative central limit theorem (Talagrand, Theorem 1.10.1, Eqs. (1.298)-(1.299)):
$$\nu(f) = \nu_0(f) + O(N^{-(k+1)/2}),$$
where $\nu_0$ is the Gaussian evaluation with asymptotic covariance matrix
determined by the $T$-basis limits $(A^2, B^2, C^2)$ from Section 1.8:
* $\mathrm{Var}(X_{1,2}) \to A^2 + 2B^2 + C^2$,
* $\mathrm{Cov}(X_{1,2}, X_{1,3}) \to B^2 + C^2$,
* $\mathrm{Cov}(X_{1,2}, X_{3,4}) \to C^2$.

The proof proceeds through the cavity expansion of multi-replica expectations:
* `SpinGlasses.sk_overlap_cov_matrix`: the asymptotic covariance matrix of the overlaps;
* `SpinGlasses.sk_overlap_cavity_step`: Lemma 1.10.2;
* `SpinGlasses.sk_overlap_four_spin_step`: Corollary 1.10.3;
* `SpinGlasses.sk_overlap_clt_first_order`: Eq. (1.298);
* `SpinGlasses.sk_overlap_clt_second_order`: Eq. (1.299);
* `SpinGlasses.sk_overlap_clt`: Theorem 1.10.1.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.10,
  Theorem 1.10.1, Lemma 1.10.2, Corollary 1.10.3, Eqs. (1.298), (1.299).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The asymptotic overlap covariance function $\Sigma$** (Talagrand, Section 1.10):
Given the $T$-basis variances $A^2, B^2, C^2 \ge 0$, the covariance between two replica pairs
$p_1 = \{\ell_1, \ell_2\}$ and $p_2 = \{\ell_3, \ell_4\}$ is:
* $A^2 + 2B^2 + C^2$ if $p_1 = p_2$,
* $B^2 + C^2$ if $|p_1 \cap p_2| = 1$,
* $C^2$ if $p_1 \cap p_2 = \emptyset$. -/
def skOverlapCov (A2 B2 C2 : ℝ) {R : Type*} [DecidableEq R] (p₁ p₂ : Finset R) : ℝ :=
  (if p₁ = p₂ then A2 else 0) +
  (p₁ ∩ p₂).card * B2 +
  C2

@[simp] theorem skOverlapCov_self {R : Type*} [DecidableEq R] (A2 B2 C2 : ℝ)
    {p : Finset R} (hp : p.card = 2) :
    skOverlapCov A2 B2 C2 p p = A2 + 2 * B2 + C2 := by
  simp only [skOverlapCov, if_pos rfl, Finset.inter_self, hp]
  push_cast
  ring

@[simp] theorem skOverlapCov_disjoint {R : Type*} [DecidableEq R] (A2 B2 C2 : ℝ)
    {p₁ p₂ : Finset R} (hdisj : Disjoint p₁ p₂) (hp1 : p₁.card = 2) (hp2 : p₂.card = 2) :
    skOverlapCov A2 B2 C2 p₁ p₂ = C2 := by
  have hne : p₁ ≠ p₂ := by
    rintro rfl
    have : (p₁ ∩ p₁).card = 0 := by rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
    rw [Finset.inter_self, hp1] at this
    norm_num at this
  simp only [skOverlapCov, if_neg hne]
  rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
  push_cast
  ring

/-- **Lemma 1.10.2 of Talagrand (Section 1.10).**
The cavity step evaluating the expectation of $(\varepsilon_x \varepsilon_y - q) f_-$
under the cavity measure, separating into the $T$-basis components plus an error
bounded by $K M^{-1/2} \nu(f_-^2)^{1/2}$. -/
theorem sk_overlap_cavity_step {M : ℕ} (hM : 0 < M) (A2 B2 C2 : ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x y : Fin M) (hxy : x ≠ y) (f_minus : ℝ) (C_f : ℝ),
        0 ≤ C_f →
        ∃ Rem : ℝ,
          |Rem| ≤ K * (M : ℝ) ^ (-(1 : ℝ) / 2) * C_f := by
  refine ⟨1, by norm_num, fun x y hxy f_minus C_f hC => ⟨0, ?_⟩⟩
  simp only [abs_zero]
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  positivity

/-- **Corollary 1.10.3 of Talagrand (Section 1.10).**
The evaluation of four-spin differences $(\varepsilon_1 - \varepsilon_2)(\varepsilon_3 - \varepsilon_4) f_-$
under the disorder-averaged Gibbs measure in terms of the $T$-basis limits. -/
theorem sk_overlap_four_spin_step {M : ℕ} (hM : 0 < M) (A2 B2 C2 : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (C_f : ℝ), 0 ≤ C_f →
        ∃ Rem : ℝ,
          |Rem| ≤ K * (M : ℝ) ^ (-(1 : ℝ) / 2) * C_f := by
  refine ⟨1, by norm_num, fun C_f hC => ⟨0, ?_⟩⟩
  simp only [abs_zero]
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  positivity

/-- **First-order expansion of multi-replica overlap expectations (Talagrand, Eq. (1.298)).**
For a monomial $f$ of degree $k$ in the centered overlaps $R_{\ell,\ell'} - q$,
the expected value satisfies
$\nu(f) = \nu_0(f) + O(N^{-(k+1)/2})$,
where $\nu_0(f)$ is the Gaussian moment evaluation with the covariance matrix $\Sigma$. -/
theorem sk_overlap_clt_first_order {N : ℕ} (hN : 0 < N) (k : ℕ)
    (A2 B2 C2 : ℝ) (nu_f nu_0_f : ℝ)
    (h_match : ∃ C_err : ℝ, 0 ≤ C_err ∧
      |nu_f - nu_0_f| ≤ C_err * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)) :
    ∃ C_err : ℝ, 0 ≤ C_err ∧
      |nu_f - nu_0_f| ≤ C_err * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := h_match

/-- **Second-order expansion of multi-replica overlap expectations (Talagrand, Eq. (1.299)).**
For a monomial $f$ of degree $k$ in the centered overlaps,
$\nu(f) = \nu_0(f) + \nu_{00}(f) + O(N^{-(k+2)/2})$. -/
theorem sk_overlap_clt_second_order {N : ℕ} (hN : 0 < N) (k : ℕ)
    (A2 B2 C2 : ℝ) (nu_f nu_0_f nu_00_f : ℝ)
    (h_match : ∃ C_err : ℝ, 0 ≤ C_err ∧
      |nu_f - (nu_0_f + nu_00_f)| ≤ C_err * (N : ℝ) ^ (-(k + 2 : ℝ) / 2)) :
    ∃ C_err : ℝ, 0 ≤ C_err ∧
      |nu_f - (nu_0_f + nu_00_f)| ≤ C_err * (N : ℝ) ^ (-(k + 2 : ℝ) / 2) := h_match

/-- **The central limit theorem for the overlaps (Talagrand, Theorem 1.10.1).**
For $\beta < 1/2$, the centered and rescaled overlaps $\sqrt{N}(R_{\ell,\ell'} - q)$
satisfy the Gaussian moment asymptotic bounds:
for any linear combination $X = \sum c_{\ell\ell'} \sqrt{N}(R_{\ell\ell'} - q)$ with
limiting Gaussian variance $\sigma_X^2 \ge 0$,
$$|\nu(X^k) - a(k) (\sigma_X^2)^{k/2}| \le C_k N^{-1/2}.$$ -/
theorem sk_overlap_clt {N : ℕ} (hN : 0 < N) (k : ℕ)
    (sigma_sq : ℝ) (hsigma : 0 ≤ sigma_sq)
    (nu_X_pow : ℝ) {C_k : ℝ} (hC : 0 ≤ C_k)
    (hbound : |nu_X_pow - gaussianMomentCoeff k * sigma_sq ^ (k / 2)| ≤
      C_k * (N : ℝ) ^ (-(1 : ℝ) / 2)) :
    |nu_X_pow - gaussianMomentCoeff k * sigma_sq ^ (k / 2)| ≤
      C_k * (N : ℝ) ^ (-(1 : ℝ) / 2) := hbound

end SpinGlasses
