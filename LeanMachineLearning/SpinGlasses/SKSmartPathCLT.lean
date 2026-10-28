/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKFreeEnergyMoments
public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound
public import LeanMachineLearning.SpinGlasses.SKPathOverlapMoments
public import LeanMachineLearning.SpinGlasses.SKSmartPathProfileComp
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint

/-!
# The central limit theorem for the SK free energy (Talagrand, Theorem 1.4.11)

For $\beta < 1/2$ and $h \in \mathbb{R}$, the normalized free energy
$A_N = N^{-1} \log Z_N(\beta, h)$ satisfies the quantitative central limit theorem
(Talagrand, Theorem 1.4.11, Eq. (1.109)):
$$\mathbb{E} (A_N - \mathrm{SK}(\beta, h))^k = N^{-k/2} a(k) b^{k/2} + O(N^{-(k+1)/2}),$$
where $a(k) = (k-1)!!$ for even $k$ and $0$ for odd $k$ is the $k$-th Gaussian moment coefficient,
and $b = \mathrm{Var}(\log\cosh(\beta \sqrt{q} z + h)) - \frac{\beta^2 q^2}{2}$.

Along the smart path $s \mapsto \cos s \cdot X + \sin s \cdot Y + h$, the replica-symmetric centered
moments $\psi_k(s) = \mathbb{E}(A(s) - \mathrm{skPathRS}(s))^k$ satisfy the differential equation
$$\psi_k'(s) = \frac{k(k-1)}{2 N} b'(s) \psi_{k-2}(s) + O(N^{-(k+1)/2}),$$
with $b(s) = \mathrm{Var}(\log\cosh Y) - \frac{\beta^2 q^2}{2} \cos^2 s$.
Integrating this ODE by induction on $k$ from the decoupled endpoint $s = \pi/2$ down to $s = 0$
proves Theorem 1.4.11.

## Main declarations

* `SpinGlasses.gaussianMomentCoeff`: the $k$-th moment coefficient $a(k) = (k-1)!!$ for even $k$,
  $0$ for odd $k$.
* `SpinGlasses.skVariance`: the path variance
  $b(s) = \mathrm{Var}(\log\cosh Y) - \frac{\beta^2 q^2}{2} \cos^2 s$.
* `SpinGlasses.sk_clt_ode_step`: the ODE integration step transferring the CLT bound from
  $k-2$ to $k$.
* `SpinGlasses.sk_free_energy_clt`: Theorem 1.4.11 / Eq. (1.109).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.4, Theorem 1.4.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The $k$-th Gaussian moment coefficient $a(k)$** (Talagrand, Eq. (1.109)):
$a(0) = 1$, $a(1) = 0$, and $a(k+2) = (k+1) a(k)$.
For even $k$, $a(k) = (k-1)!!$; for odd $k$, $a(k) = 0$. -/
def gaussianMomentCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | k + 2 => (k + 1 : ℝ) * gaussianMomentCoeff k

@[simp] theorem gaussianMomentCoeff_zero : gaussianMomentCoeff 0 = 1 := rfl
@[simp] theorem gaussianMomentCoeff_one : gaussianMomentCoeff 1 = 0 := rfl
@[simp] theorem gaussianMomentCoeff_add_two (k : ℕ) :
    gaussianMomentCoeff (k + 2) = (k + 1 : ℝ) * gaussianMomentCoeff k := rfl

theorem gaussianMomentCoeff_nonneg (k : ℕ) : 0 ≤ gaussianMomentCoeff k := by
  induction k using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp
    · simp
    · rw [gaussianMomentCoeff_add_two]
      have : 0 ≤ gaussianMomentCoeff n := ih n (by omega)
      positivity

/-- **The path variance $b(s)$ of the free energy** (Talagrand, below Eq. (1.109) and Eq. (1.121)):
$b(s) = \mathrm{Var}(\log\cosh(\beta \sqrt{q} z + h)) - \frac{\beta^2 q^2}{2} \cos^2 s$.
At $s = 0$ it equals the asymptotic variance $b$ of the SK model; at $s = \pi/2$ it equals the
decoupled variance. -/
noncomputable def skVariance (β h q s : ℝ) : ℝ :=
  (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ^ 2 ∂(gaussianReal 0 1) -
    (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1)) ^ 2) -
  β ^ 2 / 2 * q ^ 2 * Real.cos s ^ 2

@[simp] theorem skVariance_pi_div_two (β h q : ℝ) :
    skVariance β h q (Real.pi / 2) =
      ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ^ 2 ∂(gaussianReal 0 1) -
        (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1)) ^ 2 := by
  simp only [skVariance, Real.cos_pi_div_two, sq, mul_zero, sub_zero]

theorem hasDerivAt_skVariance (β h q s : ℝ) :
    HasDerivAt (skVariance β h q) (β ^ 2 * q ^ 2 * Real.sin s * Real.cos s) s := by
  have hcos : HasDerivAt (fun x => Real.cos x ^ 2) (-2 * Real.sin s * Real.cos s) s := by
    convert (Real.hasDerivAt_cos s).pow 2 using 1
    ring
  have hsub := (hcos.const_mul (-(β ^ 2 / 2 * q ^ 2))).const_add
    (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ^ 2 ∂(gaussianReal 0 1) -
      (∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1)) ^ 2)
  have e : (fun x => (∫ y : ℝ,
        Real.log (Real.cosh (β * Real.sqrt q * y + h)) ^ 2 ∂(gaussianReal 0 1) -
        (∫ y : ℝ, Real.log (Real.cosh (β * Real.sqrt q * y + h)) ∂(gaussianReal 0 1)) ^ 2) +
      -(β ^ 2 / 2 * q ^ 2) * Real.cos x ^ 2) = skVariance β h q := by
    ext x; simp only [skVariance]; ring
  rw [e] at hsub
  have ed : -(β ^ 2 / 2 * q ^ 2) * (-2 * Real.sin s * Real.cos s) =
      β ^ 2 * q ^ 2 * Real.sin s * Real.cos s := by ring
  rw [ed] at hsub
  exact hsub

/-- For odd $k$, the Gaussian moment coefficient is zero. -/
theorem gaussianMomentCoeff_odd {k : ℕ} (hk : Odd k) : gaussianMomentCoeff k = 0 := by
  obtain ⟨m, rfl⟩ := hk
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega, gaussianMomentCoeff_add_two, ih, mul_zero]

/-- **The derivative of the reference CLT term along the smart path.**
For both even and odd $k$, the function
$s \mapsto N^{-k/2} a(k) b(s)^{k/2}$ has derivative
$\sin s \cos s \cdot \frac{k(k-1)}{2 N} B \cdot (N^{-(k-2)/2} a(k-2) b(s)^{(k-2)/2})$. -/
theorem hasDerivAt_clt_ref {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k)
    {b : ℝ → ℝ} {B : ℝ} (hb : ∀ s, HasDerivAt b (B * Real.sin s * Real.cos s) s) (s : ℝ) :
    HasDerivAt (fun x => (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * b x ^ (k / 2))
      (Real.sin s * Real.cos s *
        ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
          ((N : ℝ) ^ (-(k - 2 : ℝ) / 2) * gaussianMomentCoeff (k - 2) * b s ^ ((k - 2) / 2)))) s := by
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨m, rfl⟩ := heven
    have hm1 : 1 ≤ m := by omega
    have h_div : (2 * m) / 2 = m := Nat.mul_div_right m (by decide)
    have h_div_prev : (2 * m - 2) / 2 = m - 1 := by
      rw [show 2 * m - 2 = 2 * (m - 1) by omega, Nat.mul_div_right _ (by decide)]
    rw [h_div, h_div_prev]
    have ha_rel : gaussianMomentCoeff (2 * m) =
        (2 * (m : ℝ) - 1) * gaussianMomentCoeff (2 * m - 2) := by
      have : 2 * m = (2 * m - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [gaussianMomentCoeff_add_two]
      push_cast
      ring_nf
    have hpow : HasDerivAt (fun x => b x ^ m)
        ((m : ℝ) * b s ^ (m - 1) * (B * Real.sin s * Real.cos s)) s := (hb s).pow m
    have hd := hpow.const_mul ((N : ℝ) ^ (-(2 * (m : ℝ)) / 2) * gaussianMomentCoeff (2 * m))
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have hNpow : (N : ℝ) ^ (-(2 * (m : ℝ)) / 2) =
        (N : ℝ)⁻¹ * (N : ℝ) ^ (-(2 * (m : ℝ) - 2) / 2) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]
      congr 1
      ring_nf
    have e : ((N : ℝ) ^ (-(2 * (m : ℝ)) / 2) * gaussianMomentCoeff (2 * m)) *
        ((m : ℝ) * b s ^ (m - 1) * (B * Real.sin s * Real.cos s)) =
        Real.sin s * Real.cos s *
          ((2 * (m : ℝ)) * (2 * (m : ℝ) - 1) / (2 * (N : ℝ)) * B *
            ((N : ℝ) ^ (-(2 * (m : ℝ) - 2) / 2) * gaussianMomentCoeff (2 * m - 2) *
              b s ^ (m - 1))) := by
      rw [ha_rel, hNpow]
      ring
    rw [e] at hd
    exact hd
  · have h1 := gaussianMomentCoeff_odd hodd
    have hodd_prev : Odd (k - 2) := by
      obtain ⟨m, rfl⟩ := hodd
      have : 2 * m + 1 - 2 = 2 * (m - 1) + 1 := by omega
      rw [this]
      exact ⟨m - 1, rfl⟩
    have h2 := gaussianMomentCoeff_odd hodd_prev
    have e1 : (fun x => (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * b x ^ (k / 2)) =
        fun _ => 0 := by
      ext x; rw [h1, mul_zero, zero_mul]
    rw [e1]
    have e2 : Real.sin s * Real.cos s *
          ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
            ((N : ℝ) ^ (-(k - 2 : ℝ) / 2) * gaussianMomentCoeff (k - 2) *
              b s ^ ((k - 2) / 2))) = 0 := by
      rw [h2, mul_zero, zero_mul, mul_zero, mul_zero]
    rw [e2]
    exact hasDerivAt_const s 0

/-- **Integration of the CLT moment ODE along the smart path.**
Let $b(s)$ have derivative $B \sin s \cos s$. If $\psi_k$ and $\psi_{k-2}$ satisfy
$\psi_k'(s) = \frac{k(k-1)}{2 N} b'(s) \psi_{k-2}(s) + \mathrm{Rem}(s)$
with remainder bounded by $C_{\mathrm{rem}} N^{-(k+1)/2}$ and the inductive assumption
$|\psi_{k-2}(s) - N^{-(k-2)/2} a(k-2) b(s)^{(k-2)/2}| \le C_{\mathrm{ind}} N^{-(k-1)/2}$,
and the decoupled endpoint satisfies
$|\psi_k(\pi/2) - N^{-k/2} a(k) b(\pi/2)^{k/2}| \le C_{\mathrm{dec}} N^{-(k+1)/2}$,
then at $s = 0$ (the SK model),
$|\psi_k(0) - N^{-k/2} a(k) b(0)^{k/2}| \le
  (C_{\mathrm{dec}} + C_{\mathrm{rem}} / 2 + (k(k-1)/4) B C_{\mathrm{ind}}) N^{-(k+1)/2}$. -/
theorem sk_clt_ode_step {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k)
    {b ψ_k ψ_prev : ℝ → ℝ} {B C_rem C_ind C_dec : ℝ}
    (hb_deriv : ∀ s, HasDerivAt b (B * Real.sin s * Real.cos s) s)
    (hψ_deriv : ∀ s, ∃ D_rem, HasDerivAt ψ_k
      (Real.sin s * Real.cos s *
        ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B * ψ_prev s + D_rem)) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D_rem| ≤ C_rem * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)))
    (hind : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
      |ψ_prev s -
          (N : ℝ) ^ (-(k - 2 : ℝ) / 2) * gaussianMomentCoeff (k - 2) * b s ^ ((k - 2) / 2)| ≤
        C_ind * (N : ℝ) ^ (-(k - 1 : ℝ) / 2))
    (hdec : |ψ_k (Real.pi / 2) -
        (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * b (Real.pi / 2) ^ (k / 2)| ≤
      C_dec * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)) :
    |ψ_k 0 - (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * b 0 ^ (k / 2)| ≤
      (C_dec + C_rem / 2 + (k : ℝ) * (k - 1 : ℝ) / 4 * |B| * C_ind) *
        (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
  set a_prev := gaussianMomentCoeff (k - 2)
  set ref : ℝ → ℝ := fun s => (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * b s ^ (k / 2)
  have href_deriv : ∀ s, HasDerivAt ref
      (Real.sin s * Real.cos s *
        ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
          ((N : ℝ) ^ (-(k - 2 : ℝ) / 2) * a_prev * b s ^ ((k - 2) / 2)))) s :=
    hasDerivAt_clt_ref hN hk hb_deriv
  set Φ : ℝ → ℝ := fun s => ψ_k s - ref s
  have hΦ_deriv : ∀ s, ∃ D, HasDerivAt Φ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D| ≤
        (C_rem + (k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)) :=
    fun s => by
      obtain ⟨D_rem, hD_rem, hD_rem_b⟩ := hψ_deriv s
      have hd_sub := hD_rem.sub (href_deriv s)
      refine ⟨D_rem + (k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
          (ψ_prev s - (N : ℝ) ^ (-(k - 2 : ℝ) / 2) * a_prev * b s ^ ((k - 2) / 2)),
        ?_, fun hs => ?_⟩
      · have e : (Real.sin s * Real.cos s *
              ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B * ψ_prev s + D_rem) -
            Real.sin s * Real.cos s * ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
              ((N : ℝ) ^ (-(k - 2 : ℝ) / 2) * a_prev * b s ^ ((k - 2) / 2)))) =
            Real.sin s * Real.cos s * (D_rem + (k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B *
              (ψ_prev s - (N : ℝ) ^ (-(k - 2 : ℝ) / 2) * a_prev * b s ^ ((k - 2) / 2))) := by ring
        rw [e] at hd_sub
        exact hd_sub
      · have h1 := hD_rem_b hs
        have h2 := hind s hs
        have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
        have hNpow2 : (N : ℝ)⁻¹ * (N : ℝ) ^ (-(k - 1 : ℝ) / 2) =
            (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hNpos]
          congr 1
          ring_nf
        have hk_nonneg : 0 ≤ (k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) := by
          have : 0 ≤ (k : ℝ) - 1 := by linarith [show 2 ≤ (k : ℝ) by exact_mod_cast hk]
          positivity
        have hfac_nonneg : 0 ≤ (k : ℝ) * (k - 1 : ℝ) / 2 * |B| := by
          have : 0 ≤ (k : ℝ) - 1 := by linarith [show 2 ≤ (k : ℝ) by exact_mod_cast hk]
          have : 0 ≤ (k : ℝ) * (k - 1 : ℝ) / 2 := by positivity
          exact mul_nonneg this (abs_nonneg B)
        set diff := ψ_prev s - (N : ℝ) ^ (-(k - 2 : ℝ) / 2) * a_prev * b s ^ ((k - 2) / 2)
        have hT_le : |(k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B * diff| ≤
            ((k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hk_nonneg]
          have e : (k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) =
              ((k : ℝ) * (k - 1 : ℝ) / 2) * (N : ℝ)⁻¹ := by ring_nf
          rw [e]
          calc ((k : ℝ) * (k - 1 : ℝ) / 2) * (N : ℝ)⁻¹ * |B| * |diff|
              = ((k : ℝ) * (k - 1 : ℝ) / 2 * |B|) * ((N : ℝ)⁻¹ * |diff|) := by ring
            _ ≤ ((k : ℝ) * (k - 1 : ℝ) / 2 * |B|) *
                  ((N : ℝ)⁻¹ * (C_ind * (N : ℝ) ^ (-(k - 1 : ℝ) / 2))) := by
              refine mul_le_mul_of_nonneg_left ?_ hfac_nonneg
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = ((k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
              calc ((k : ℝ) * (k - 1 : ℝ) / 2 * |B|) *
                      ((N : ℝ)⁻¹ * (C_ind * (N : ℝ) ^ (-(k - 1 : ℝ) / 2)))
                  = ((k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) *
                      ((N : ℝ)⁻¹ * (N : ℝ) ^ (-(k - 1 : ℝ) / 2)) := by ring
                _ = ((k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) *
                      (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by rw [hNpow2]
        calc |D_rem + (k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B * diff|
            ≤ |D_rem| + |(k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * B * diff| := abs_add_le _ _
          _ ≤ C_rem * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) +
                ((k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) :=
              add_le_add h1 hT_le
          _ = (C_rem + (k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) :=
              by ring
  have hdiff := Real.abs_sub_le_half_of_exists_hasDerivAt hΦ_deriv
  have hpi : |Φ (Real.pi / 2)| ≤ C_dec * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := hdec
  have h0 : |Φ 0| ≤ |Φ (Real.pi / 2)| + |Φ (Real.pi / 2) - Φ 0| := by
    calc |Φ 0| = |Φ 0 - Φ (Real.pi / 2) + Φ (Real.pi / 2)| := by ring
      _ ≤ |Φ 0 - Φ (Real.pi / 2)| + |Φ (Real.pi / 2)| := abs_add_le _ _
      _ = |Φ (Real.pi / 2)| + |Φ (Real.pi / 2) - Φ 0| := by rw [abs_sub_comm, add_comm]
  calc |ψ_k 0 - ref 0| = |Φ 0| := rfl
    _ ≤ |Φ (Real.pi / 2)| + |Φ (Real.pi / 2) - Φ 0| := h0
    _ ≤ C_dec * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) +
          (C_rem + (k : ℝ) * (k - 1 : ℝ) / 2 * |B| * C_ind) *
            (N : ℝ) ^ (-(k + 1 : ℝ) / 2) / 2 := add_le_add hpi hdiff
    _ = (C_dec + C_rem / 2 + (k : ℝ) * (k - 1 : ℝ) / 4 * |B| * C_ind) *
          (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by ring

/-- **CLT base case $k = 0$** (Talagrand, Eq. (1.109)):
The $0$-th moment of $A_N - \mathrm{rsFunctional}$ is identically $1$,
so the difference from $N^{-0/2} a(0) b^{0/2} = 1$ is $0$. -/
theorem sk_clt_zero (N : ℕ) (β h q : ℝ) (V : ℝ) :
    |V ^ 0 - (N : ℝ) ^ (-(0 : ℝ) / 2) * gaussianMomentCoeff 0 *
        (skVariance β h q 0) ^ (0 / 2)| ≤
      0 * (N : ℝ) ^ (-(0 + 1 : ℝ) / 2) := by
  simp

/-- **CLT base case $k = 1$** (Talagrand, Eq. (1.109) / Lemma 1.4.12 endpoint):
For $\beta^2 < 1/4$ and a fixed point $q$, the first centered moment satisfies
$|\varphi(0) - \mathrm{rsFunctional}(\beta, h, q)| \le K_1' N^{-(1+1)/2}$ with
$K_1' = (\beta^2 / 4) K_1$. -/
theorem sk_clt_one {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {φ A : ℝ → ℝ}
    (hpi : φ (Real.pi / 2) = Real.log 2 +
      ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1))
    (hderiv : ∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2)) t)
    (hA : ∀ t ∈ Set.Icc 0 (Real.pi / 2),
      A t = ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
          Real.cos t * ((Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
          Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
          h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1))) :
    let K1 : ℝ := (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2)
    |φ 0 - rsFunctional β h q -
        (N : ℝ) ^ (-(1 : ℝ) / 2) * gaussianMomentCoeff 1 * (skVariance β h q 0) ^ (1 / 2)| ≤
      (β ^ 2 / 4 * K1) * (N : ℝ) ^ (-(1 + 1 : ℝ) / 2) := by
  intro K1
  have hbound := sk_free_energy_sub_rs_le hN β h q hfix hβ hpi hderiv hA
  simp only [gaussianMomentCoeff_one, mul_zero, zero_mul, sub_zero]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have e : (N : ℝ) ^ (-(1 + 1 : ℝ) / 2) = (N : ℝ)⁻¹ := by
    have : -(1 + 1 : ℝ) / 2 = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  rw [e]
  calc |φ 0 - rsFunctional β h q| ≤ β ^ 2 / 4 * K1 / N := hbound
    _ = (β ^ 2 / 4 * K1) * (N : ℝ)⁻¹ := div_eq_mul_inv _ _

/-- **The explicit CLT error constant for the SK free energy** (Talagrand, Theorem 1.4.11).
Given decoupled constants `C_dec : ℕ → ℝ`, remainder constants `C_rem : ℕ → ℝ`,
and the base constant `K1 : ℝ`, this recursive sequence provides the quantitative error bound
for all moments $k \in \mathbb{N}$. -/
def skCLTConst (β q : ℝ) (K1 : ℝ) (C_dec C_rem : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => β ^ 2 / 4 * K1
  | k + 2 => C_dec (k + 2) + C_rem (k + 2) / 2 +
      (k + 2 : ℝ) * (k + 1 : ℝ) / 4 * (β ^ 2 * q ^ 2) * skCLTConst β q K1 C_dec C_rem k

@[simp] theorem skCLTConst_zero (β q K1 : ℝ) (C_dec C_rem : ℕ → ℝ) :
    skCLTConst β q K1 C_dec C_rem 0 = 0 := rfl

@[simp] theorem skCLTConst_one (β q K1 : ℝ) (C_dec C_rem : ℕ → ℝ) :
    skCLTConst β q K1 C_dec C_rem 1 = β ^ 2 / 4 * K1 := rfl

@[simp] theorem skCLTConst_add_two (β q K1 : ℝ) (C_dec C_rem : ℕ → ℝ) (k : ℕ) :
    skCLTConst β q K1 C_dec C_rem (k + 2) =
      C_dec (k + 2) + C_rem (k + 2) / 2 +
        (k + 2 : ℝ) * (k + 1 : ℝ) / 4 * (β ^ 2 * q ^ 2) * skCLTConst β q K1 C_dec C_rem k := rfl

/-- **The CLT induction step along the smart path.**
Transfers the CLT bound from $k-2$ to $k$ using `sk_clt_ode_step`. -/
theorem sk_clt_induction_step {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k)
    (β h q : ℝ) {ψ_k ψ_prev : ℝ → ℝ} {C_rem C_ind C_dec : ℝ}
    (hψ_deriv : ∀ s, ∃ D_rem, HasDerivAt ψ_k
      (Real.sin s * Real.cos s *
        ((k : ℝ) * (k - 1 : ℝ) / (2 * (N : ℝ)) * (β ^ 2 * q ^ 2) * ψ_prev s + D_rem)) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D_rem| ≤ C_rem * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)))
    (hind : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
      |ψ_prev s -
          (N : ℝ) ^ (-(k - 2 : ℝ) / 2) * gaussianMomentCoeff (k - 2) *
            (skVariance β h q s) ^ ((k - 2) / 2)| ≤
        C_ind * (N : ℝ) ^ (-(k - 1 : ℝ) / 2))
    (hdec : |ψ_k (Real.pi / 2) -
        (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k *
          (skVariance β h q (Real.pi / 2)) ^ (k / 2)| ≤
      C_dec * (N : ℝ) ^ (-(k + 1 : ℝ) / 2)) :
    |ψ_k 0 - (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * (skVariance β h q 0) ^ (k / 2)| ≤
      (C_dec + C_rem / 2 + (k : ℝ) * (k - 1 : ℝ) / 4 * (β ^ 2 * q ^ 2) * C_ind) *
        (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
  have hb := hasDerivAt_skVariance β h q
  have hstep := sk_clt_ode_step hN hk hb hψ_deriv hind hdec
  have eB : |β ^ 2 * q ^ 2| = β ^ 2 * q ^ 2 := by
    have : 0 ≤ β ^ 2 * q ^ 2 := by positivity
    exact abs_of_nonneg this
  rw [eB] at hstep
  exact hstep

/-- **Theorem 1.4.11 of Talagrand (Spin Glasses Vol. I, Eq. (1.109)): The Central Limit
Theorem for the Free Energy.**
For $\beta^2 < 1/4$ and a fixed point $q$ of the replica-symmetric equation, the normalized
free energy $A_N = N^{-1} \log Z_N(\beta, h)$ of the SK model satisfies the quantitative
moment bound:
$$|\mathbb{E}(A_N - \mathrm{rsFunctional}(\beta, h, q))^k -
  N^{-k/2} a(k) (\mathrm{skVariance}(\beta, h, q, 0))^{k/2}| \le
  C_k N^{-(k+1)/2}.$$ -/
theorem sk_free_energy_clt {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) (k : ℕ)
    {ψ : ℕ → ℝ → ℝ} {C_dec C_rem : ℕ → ℝ}
    (hψ_0 : ∀ m, ψ m 0 = ∫ g : FinPairs N → ℝ,
      ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
        (Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
        h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q) ^ m
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
    (hψ_dec : ∀ m, |ψ m (Real.pi / 2) -
        (N : ℝ) ^ (-(m : ℝ) / 2) * gaussianMomentCoeff m *
          (skVariance β h q (Real.pi / 2)) ^ (m / 2)| ≤
      C_dec m * (N : ℝ) ^ (-(m + 1 : ℝ) / 2))
    (hψ_deriv : ∀ m ≥ 2, ∀ s, ∃ D_rem, HasDerivAt (ψ m)
      (Real.sin s * Real.cos s *
        ((m : ℝ) * (m - 1 : ℝ) / (2 * (N : ℝ)) * (β ^ 2 * q ^ 2) * ψ (m - 2) s + D_rem)) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D_rem| ≤ C_rem m * (N : ℝ) ^ (-(m + 1 : ℝ) / 2)))
    (hind_path : ∀ m < k, ∀ s ∈ Set.Icc 0 (Real.pi / 2),
      |ψ m s -
          (N : ℝ) ^ (-(m : ℝ) / 2) * gaussianMomentCoeff m * (skVariance β h q s) ^ (m / 2)| ≤
        skCLTConst β q ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2)) C_dec C_rem m *
          (N : ℝ) ^ (-(m + 1 : ℝ) / 2))
    (hψ_one_deriv : ∀ t, HasDerivAt (ψ 1)
      (β ^ 2 / 2 * Real.sin t * Real.cos t *
        (∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
          (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
          ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1)) - (1 - q) ^ 2)) t)
    (hψ_one_pi : ψ 1 (Real.pi / 2) = Real.log 2 +
      ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1)) :
    let K1 : ℝ := (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ / (1 / 4 - β ^ 2)
    |∫ g : FinPairs N → ℝ,
      ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
        (Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
        h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q) ^ k
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) -
      (N : ℝ) ^ (-(k : ℝ) / 2) * gaussianMomentCoeff k * (skVariance β h q 0) ^ (k / 2)| ≤
    skCLTConst β q K1 C_dec C_rem k * (N : ℝ) ^ (-(k + 1 : ℝ) / 2) := by
  intro K1
  rcases k with _ | _ | m
  · simp only [skCLTConst_zero, zero_mul]
    rw [hψ_0 0]
    have e0 : (fun g : FinPairs N → ℝ =>
        ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
          (Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q) ^ 0) = fun _ => 1 := by
      ext; simp
    rw [e0, integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    simp
  · simp only [skCLTConst_one, gaussianMomentCoeff_one, mul_zero, zero_mul, sub_zero]
    rw [hψ_0 1]
    have hone : (fun g : FinPairs N → ℝ =>
        ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
          (Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q) ^ 1) =
        fun g => (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
          (Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q := by
      ext; simp
    rw [hone]
    have hint_sub : (∫ g : FinPairs N → ℝ,
        ((N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
          (Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) - rsFunctional β h q)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (∫ g : FinPairs N → ℝ,
        (N : ℝ)⁻¹ * Real.log (∑ σ : Fin N → ℤˣ, Real.exp (
          (Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) +
          h * ∑ i, ((σ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) - rsFunctional β h q := by
      rw [integral_sub ?_ (integrable_const _)]
      · rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
      · exact (integrable_free_energy_pi_gaussianReal hN β h).const_mul _
    rw [hint_sub]
    have h1 := sk_clt_one hN β h q hfix hβ hψ_one_pi hψ_one_deriv (fun t _ => rfl)
    dsimp [K1] at h1
    simp only [gaussianMomentCoeff_one, mul_zero, zero_mul, sub_zero] at h1
    exact h1
  · have hk : 2 ≤ m + 2 := by omega
    rw [← hψ_0 (m + 2)]
    have hind := hind_path m (by omega)
    have hind' : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
        |ψ m s -
            (N : ℝ) ^ (-(m : ℝ) / 2) * gaussianMomentCoeff m * (skVariance β h q s) ^ (m / 2)| ≤
          skCLTConst β q K1 C_dec C_rem m * (N : ℝ) ^ (-(m + 1 : ℝ) / 2) := hind
    have hind_step : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
        |ψ ((m + 2) - 2) s -
            (N : ℝ) ^ (-(((m + 2 : ℝ) - 2) / 2)) * gaussianMomentCoeff ((m + 2) - 2) *
              (skVariance β h q s) ^ (((m + 2) - 2) / 2)| ≤
          skCLTConst β q K1 C_dec C_rem m * (N : ℝ) ^ (-((m + 2 : ℝ) - 1) / 2) := by
      intro s hs
      have e1 : (m + 2) - 2 = m := by omega
      have e2 : ((m + 2 : ℝ) - 1) / 2 = (m + 1 : ℝ) / 2 := by ring
      have e3 : ((m + 2 : ℝ) - 2) / 2 = (m : ℝ) / 2 := by ring
      rw [e1, e2, e3]
      exact hind' s hs
    have hdec := hψ_dec (m + 2)
    have hder := hψ_deriv (m + 2) hk
    have hstep := sk_clt_induction_step hN hk β h q hder hind_step hdec
    have econst : C_dec (m + 2) + C_rem (m + 2) / 2 +
        (m + 2 : ℝ) * (m + 2 - 1 : ℝ) / 4 * (β ^ 2 * q ^ 2) *
          skCLTConst β q K1 C_dec C_rem m =
      skCLTConst β q K1 C_dec C_rem (m + 2) := by
      rw [skCLTConst_add_two]
      have : (m + 2 : ℝ) - 1 = (m + 1 : ℝ) := by ring
      rw [this]
    rw [econst] at hstep
    exact hstep

end SpinGlasses
