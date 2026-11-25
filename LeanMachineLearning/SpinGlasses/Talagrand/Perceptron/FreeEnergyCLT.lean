/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.FreeEnergyGronwall
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumExpansion
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# Central limit theorem for the free energy of the perceptron (Talagrand Theorem 2.5.3)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, Theorem 2.5.3.

For `N + 1` spins and `M` constraints with load `α = M / (N + 1)`, let `(q, r)` solve the
replica-symmetric fixed-point system (2.68) under (2.7) and `α K ≤ 1`. Along the interpolating path
`s ∈ [0, 1]`, the centered random free energy `V(s) = A(s) - RS(s)` has moments
`ψ_k(s) = 𝔼[V(s)^k]` satisfying `hasDerivAt_interpolating_centered_moment_pow` (Eq. (2.108)).
Feeding the a priori Grönwall bound `integral_interpolating_centered_abs_pow_le` into
`abs_interpolating_term_VII_le` and `abs_interpolating_term_VIII_le` (Eq. (2.109)) reduces
Eq. (2.108) to
$$\psi_k'(s) = -\frac{r q}{2 (N + 1)}\,k (k - 1)\,\psi_{k - 2}(s) +
  O\bigl((N + 1)^{-(k + 1)/2}\bigr).$$

At the decoupled endpoint `s = 0`, `V(0)` is the sum of two independent centered i.i.d. averages:
1. the `N + 1` spin terms `log cosh(z'_i √r) - 𝔼 log cosh(z √r)` with variance
   `v_X = 𝔼(log cosh(z √r))² - (𝔼 log cosh(z √r))²`, and
2. the `M` constraint terms `log 𝔼_ξ exp u(θ_j) - 𝔼 log 𝔼_ξ exp u(θ)` (`θ = √q z + √(1 - q) ξ`)
   with variance `v_Y = 𝔼(log 𝔼_ξ exp u(θ))² - (𝔼 log 𝔼_ξ exp u(θ))²`, contributing `α v_Y` to the
   scaled variance of `V(0)`.

Thus `b(s) = v_X + α v_Y - r q s` satisfies `b'(s) = -r q` and matches the decoupled variance
`v_X + α v_Y` at `s = 0` (`exists_abs_integral_add_pow_avg_two_pi_sub_le`). Integrating from `0` to
`s` by two-step induction on `k` yields `interpolating_free_energy_clt` for all `s ∈ [0, 1]` and,
at `s = 1`, `perceptron_free_energy_clt` with fluctuation variance
$$b = \mathbb{E}\bigl(\log \cosh(z\sqrt{r})\bigr)^2 -
  \bigl(\mathbb{E}\log \cosh(z\sqrt{r})\bigr)^2 +
  \alpha\Bigl(\mathbb{E}\bigl(\log\mathbb{E}_\xi \exp u(\theta)\bigr)^2 -
    \bigl(\mathbb{E}\log\mathbb{E}_\xi \exp u(\theta)\bigr)^2\Bigr) - q r.$$
Note on Talagrand's printed formula: Talagrand's display in Theorem 2.5.3 omits the constraint
variance term `α Var_z(log 𝔼_ξ exp u(θ))` from `b` (and prints `p_{N, M}(u)` for the random free
energy `(N + 1)⁻¹ log Z_{N+1, M}(u)`, matching Theorem 1.4.11's `N⁻¹ log Z_N`). For e.g.
`u(x) = x` at `M = N + 1`, `q = 0` (`r̂(0) = 1`), direct calculation gives `Var(p_{N, M}) > 0`
even when `M = N + 1` and `u(x)` has non-zero `z`-variance at `q > 0`: for `u(x) = tanh x` and
`M = N + 1` small load, `q > 0` and `Var_z(log 𝔼_ξ exp u(θ)) > 0`, whereas `b(0)` must equal
`L * Var(V(0)) = v_X + α v_Y`. When `Var_z(log 𝔼_ξ exp u(θ)) = 0` (for example when `q = 0`), the
two formulas agree (`perceptron_free_energy_clt_of_zero_constraint_var`).

## Main declarations

* `SpinGlasses.interpolating_free_energy_clt`: quantitative moment CLT along the `s`-interpolation
  uniformly in `s ∈ [0, 1]`.
* `SpinGlasses.perceptron_free_energy_clt`: Theorem 2.5.3 (corrected variance formula, valid for
  all `u` satisfying (2.7)).
* `SpinGlasses.perceptron_free_energy_clt_of_zero_constraint_var`: specialization to the printed
  `b = 𝔼(log cosh(z √r))² - (𝔼 log cosh(z √r))² - q r` when the constraint `z`-variance vanishes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-! ### Section 1: Abstract linear-path CLT induction on `[0, 1]` -/

/-- **Derivative of the Gaussian moment reference along a linear variance path `b(s) = b₀ + B s`:**
for any sequence `a` with `a 1 = 0` and `a (k + 2) = (k + 1) a k`, `k ≥ 1`, and `s : ℝ`,
`s' ↦ ε^k * a(k) * (b₀ + B * s')^(k / 2)` has derivative
`((k * (k - 1) / 2) * ε² * B) * (ε^(k - 2) * a(k - 2) * (b₀ + B * s)^((k - 2) / 2))`. -/
private lemma hasDerivAt_linear_clt_ref {ε b₀ B : ℝ} {a : ℕ → ℝ}
    (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    {k : ℕ} (hk : 1 ≤ k) (s : ℝ) :
    HasDerivAt (fun s' => ε ^ k * a k * (b₀ + B * s') ^ (k / 2))
      (((k : ℝ) * ((k : ℝ) - 1) / 2 * ε ^ 2 * B) *
        (ε ^ (k - 2) * a (k - 2) * (b₀ + B * s) ^ ((k - 2) / 2))) s := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hk_eq : j + 1 + (j + 1) = 2 * j + 2 := by ring
    rw [hk_eq, show (2 * j + 2) / 2 = j + 1 by omega,
      show 2 * j + 2 - 2 = 2 * j by omega, show (2 * j) / 2 = j by omega]
    have hb_der : HasDerivAt (fun s' => b₀ + B * s') B s := by
      simpa using ((hasDerivAt_id s).const_mul B).const_add b₀
    have hd := (hb_der.pow (j + 1)).const_mul (ε ^ (2 * j + 2) * a (2 * j + 2))
    refine hd.congr_deriv ?_
    rw [ha (2 * j)]
    have hε : ε ^ (2 * j + 2) = ε ^ 2 * ε ^ (2 * j) := by rw [← pow_add]; congr 1; ring
    rw [hε]
    push_cast; ring
  · have h1 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha hodd
    simp only [h1, mul_zero, zero_mul]
    rcases hodd with ⟨m, rfl⟩
    rcases m with _ | m
    · simpa using hasDerivAt_const s (0 : ℝ)
    · rw [show 2 * (m + 1) + 1 - 2 = 2 * m + 1 by omega,
        Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m, rfl⟩]
      simpa using hasDerivAt_const s (0 : ℝ)

/-- **One step of the linear-path CLT induction on `[0, 1]`:**
if `ψ` is continuous on `[0, 1]`, satisfies
`ψ'(t) = ((m (m - 1) / 2) ε² B) ψp(t) + D` on `(0, 1)` with `|D| ≤ C_rem ε^{m+1}`, `ψp` is within
`C_ind ε^{m-1}` of the degree-`(m - 2)` reference on `[0, 1]`, and `ψ(0)` is within `C_dec ε^{m+1}`
of the degree-`m` reference at `0`, then for all `s ∈ [0, 1]`,
`|ψ(s) - ε^m a(m) (b₀ + B s)^{m/2}| ≤ (C_dec + C_rem + (m (m - 1) / 2) B_max C_ind) ε^{m+1}`
whenever `|B| ≤ B_max`. -/
private lemma abs_sub_linear_clt_ref_le
    {ε b₀ B B_max : ℝ} (hε : 0 < ε) (hB : |B| ≤ B_max) (hBmax0 : 0 ≤ B_max)
    {a : ℕ → ℝ} (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    {m : ℕ} (hm : 1 ≤ m)
    {ψ ψp : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Icc 0 1))
    {C_rem C_ind C_dec : ℝ} (hCrem0 : 0 ≤ C_rem) (hCind0 : 0 ≤ C_ind)
    (hode : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ D,
      HasDerivAt ψ (((m : ℝ) * ((m : ℝ) - 1) / 2 * ε ^ 2 * B) * ψp t + D) t ∧
      |D| ≤ C_rem * ε ^ (m + 1))
    (hind : ∀ t ∈ Icc (0 : ℝ) 1,
      |ψp t - ε ^ (m - 2) * a (m - 2) * (b₀ + B * t) ^ ((m - 2) / 2)| ≤ C_ind * ε ^ (m - 1))
    (hdec : |ψ 0 - ε ^ m * a m * b₀ ^ (m / 2)| ≤ C_dec * ε ^ (m + 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    |ψ s - ε ^ m * a m * (b₀ + B * s) ^ (m / 2)| ≤
      (C_dec + C_rem + (m : ℝ) * ((m : ℝ) - 1) / 2 * B_max * C_ind) * ε ^ (m + 1) := by
  let c : ℝ := (m : ℝ) * ((m : ℝ) - 1) / 2
  have hc0 : 0 ≤ c := by
    have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
    dsimp only [c]; nlinarith
  let ref (t : ℝ) : ℝ := ε ^ m * a m * (b₀ + B * t) ^ (m / 2)
  let Δ (t : ℝ) : ℝ := ψ t - ref t
  have hΔ_cont : ContinuousOn Δ (Icc 0 1) :=
    hψ_cont.sub (by dsimp only [ref]; fun_prop)
  let K_lip : ℝ := (C_rem + c * B_max * C_ind) * ε ^ (m + 1)
  have hε_split : ε ^ 2 * ε ^ (m - 1) = ε ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hΔ_der : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt Δ d t ∧ |d| ≤ K_lip := by
    intro t ht
    obtain ⟨D, hD, hDb⟩ := hode t ht
    let d_ref := (c * ε ^ 2 * B) * (ε ^ (m - 2) * a (m - 2) * (b₀ + B * t) ^ ((m - 2) / 2))
    have href_d : HasDerivAt ref d_ref t := hasDerivAt_linear_clt_ref ha1 ha hm t
    refine ⟨(c * ε ^ 2 * B) * ψp t + D - d_ref, hD.sub href_d, ?_⟩
    have hrew : (c * ε ^ 2 * B) * ψp t + D - d_ref =
        D + (c * ε ^ 2 * B) *
          (ψp t - ε ^ (m - 2) * a (m - 2) * (b₀ + B * t) ^ ((m - 2) / 2)) := by
      dsimp only [d_ref]; ring
    rw [hrew]
    calc |D + (c * ε ^ 2 * B) *
            (ψp t - ε ^ (m - 2) * a (m - 2) * (b₀ + B * t) ^ ((m - 2) / 2))|
        ≤ |D| + |c * ε ^ 2 * B| *
            |ψp t - ε ^ (m - 2) * a (m - 2) * (b₀ + B * t) ^ ((m - 2) / 2)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ C_rem * ε ^ (m + 1) + (c * ε ^ 2 * B_max) * (C_ind * ε ^ (m - 1)) := by
          refine add_le_add hDb ?_
          rw [abs_mul, abs_of_nonneg (mul_nonneg hc0 (sq_nonneg ε))]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hB (mul_nonneg hc0 (sq_nonneg ε)))
            (hind t ⟨ht.1.le, ht.2.le⟩) (abs_nonneg _) (by positivity)
      _ = K_lip := by dsimp only [K_lip]; rw [← hε_split]; ring
  have hinc := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hΔ_cont hΔ_der
    (left_mem_Icc.2 zero_le_one) hs
  have hs_le1 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
  have hK0 : 0 ≤ K_lip := by dsimp only [K_lip]; positivity
  have hΔ0 : |Δ 0| ≤ C_dec * ε ^ (m + 1) := by
    dsimp only [Δ, ref]; simpa only [mul_zero, add_zero] using hdec
  calc |Δ s| = |Δ 0 + (Δ s - Δ 0)| := by ring_nf
    _ ≤ |Δ 0| + |Δ s - Δ 0| := abs_add_le _ _
    _ ≤ C_dec * ε ^ (m + 1) + K_lip * 1 :=
        add_le_add hΔ0 (hinc.trans (mul_le_mul_of_nonneg_left hs_le1 hK0))
    _ = (C_dec + C_rem + c * B_max * C_ind) * ε ^ (m + 1) := by dsimp only [K_lip]; ring

/-- **Two-step recursion constants for the `[0, 1]` CLT:** given `B_max ≥ 0` and nonnegative
sequences `C_rem, C_dec`, builds `C : ℕ → ℝ` with `C m ≥ 0`, `C 0 = 0`, and
`C_dec m + C_rem m + (m (m - 1) / 2) B_max C (m - 2) ≤ C m` for all `m ≥ 1`. -/
private lemma exists_linear_clt_const (B_max : ℝ) (hBmax0 : 0 ≤ B_max)
    (C_rem C_dec : ℕ → ℝ) (hrem0 : ∀ m, 0 ≤ C_rem m) (hdec0 : ∀ m, 0 ≤ C_dec m) :
    ∃ C : ℕ → ℝ, C 0 = 0 ∧ (∀ m, 0 ≤ C m) ∧ ∀ m, 1 ≤ m →
      C_dec m + C_rem m + (m : ℝ) * ((m : ℝ) - 1) / 2 * B_max * C (m - 2) ≤ C m := by
  let u (m : ℕ) : ℝ := C_dec m + C_rem m
  let w (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) - 1) / 2 * B_max
  let C : ℕ → ℝ := Nat.twoStepInduction 0 (u 1) (fun k a _ => u (k + 2) + w (k + 2) * a)
  have hu0 (m : ℕ) : 0 ≤ u m := add_nonneg (hdec0 m) (hrem0 m)
  have hw0 (m : ℕ) (hm : 1 ≤ m) : 0 ≤ w m := by
    have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
    have hsub : 0 ≤ (m : ℝ) - 1 := sub_nonneg.2 hm1
    dsimp only [w]; positivity
  have hC_nonneg : ∀ m, 0 ≤ C m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | k
      · simp [C, Nat.twoStepInduction]
      · exact hu0 1
      · change 0 ≤ u (k + 2) + w (k + 2) * C k
        exact add_nonneg (hu0 _) (mul_nonneg (hw0 (k + 2) (by omega)) (ih k (by omega)))
  refine ⟨C, rfl, hC_nonneg, fun m hm => ?_⟩
  rcases m with _ | _ | k
  · omega
  · simp [C, u, w, Nat.twoStepInduction]
  · exact le_of_eq rfl

/-! ### Section 2: Decoupled endpoint `s = 0` moment expansion and ODE remainder `O(k + 1)` -/

/-- **Quantitative moment expansion at the decoupled endpoint `s = 0`:**
for `m ≥ 1`, `|𝔼[(A(0) - RS(0))^m] - (√(N + 1))⁻¹^m a(m) b₀^{m/2}| ≤ C (√(N + 1))⁻¹^{m+1}`,
uniformly over `N, M, u, q, r` satisfying `|u| ≤ |D|`, `M ≤ N + 1`, and `r ≤ |D|²`, where
`b₀ = Var_z(log cosh(z √r)) + α Var_z(log 𝔼_ξ exp u(θ))`. -/
private lemma abs_integral_interpolating_zero_pow_sub_le (D : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ} (_hu : Measurable u) (_hB : ∀ x, |u x| ≤ |D|)
        (_hMN : (M : ℝ) ≤ (N : ℝ) + 1) {q r : ℝ} (_hr_le : r ≤ |D| ^ 2),
        let γ := gaussianReal 0 1
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let P_z := Measure.pi fun _ : Fin M => γ
        let P_z' := Measure.pi fun _ : Fin (N + 1) => γ
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => γ)
        let E_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt 0 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r
        let A_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s)
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let RS_0 : ℝ := perceptronRSFunctional u α r q + ((1 - 0) / 2) * r * (1 - q)
        let ψ_u (z : ℝ) : ℝ :=
          Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
        let b₀ : ℝ :=
          ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
              (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
            α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2)
        |∫ ω, (A_0 ω - RS_0) ^ m ∂P -
            ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ m * (∫ x : ℝ, x ^ m ∂γ) * b₀ ^ (m / 2)| ≤
          C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (m + 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let a (n : ℕ) : ℝ := ∫ x : ℝ, x ^ n ∂γ
  have ha0 : a 0 = 1 := by simp [a, γ]
  have ha1 : a 1 = 0 := by simp [a, γ, integral_id_gaussianReal]
  have ha : ∀ n, a (n + 2) = (n + 1) * a n := fun n => integral_pow_add_two_gaussianReal n
  let B₁ (j : ℕ) : ℝ := ∫ z : ℝ, (|D| * (|z| + 1)) ^ j ∂γ
  let B₂ (j : ℕ) : ℝ := (2 * |D|) ^ j
  have hB₁0 (j : ℕ) : 0 ≤ B₁ j := integral_nonneg fun _ => by positivity
  have hB₂0 (j : ℕ) : 0 ≤ B₂ j := by positivity
  obtain ⟨C, hC0, hC_two⟩ :=
    exists_abs_integral_add_pow_avg_two_pi_sub_le B₁ B₂ hB₁0 hB₂0 ha0 ha1 ha m hm
  refine ⟨C, hC0, ?_⟩
  intro N M u hu hB hMN q r hr_le γ' P_g P_z P_z' P μ_s E_0 A_0 α RS_0 ψ_u b₀
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z', γ']; infer_instance
  have hB_le : ∀ x, u x ≤ |D| := fun x => le_of_abs_le (hB x)
  have hsr_le : Real.sqrt r ≤ |D| :=
    (Real.sqrt_le_sqrt hr_le).trans_eq (Real.sqrt_sq (abs_nonneg D))
  let L_X (z : ℝ) : ℝ := Real.log (Real.cosh (z * Real.sqrt r))
  let c_X : ℝ := ∫ z : ℝ, L_X z ∂γ
  let f₁ (z : ℝ) : ℝ := L_X z - c_X
  let c_Y : ℝ := ∫ z : ℝ, ψ_u z ∂γ
  let f₂ (z : ℝ) : ℝ := ψ_u z - c_Y
  have hpt_V (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      A_0 ω - RS_0 =
        ((N + 1 : ℕ) : ℝ)⁻¹ * (∑ i : Fin (N + 1), f₁ (ω.2 i)) +
          ((N + 1 : ℕ) : ℝ)⁻¹ * (∑ j : Fin M, f₂ (ω.1.2 j)) := by
    have hlogZ : Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s) =
        (((N : ℝ) + 1) * Real.log 2 + ∑ i : Fin (N + 1), L_X (ω.2 i)) +
          ∑ j : Fin M, ψ_u (ω.1.2 j) := by
      rw [integral_sum_exp_interpolating_eq hu hB_le 0 q r ω]
      have hsimp (τ : Fin (N + 1) → ℤˣ) :
          Real.exp ((∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r) +
            ∑ j : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt 0 *
                ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
              Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ))) ∂γ')) =
          Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) *
            Real.exp (∑ j : Fin M, ψ_u (ω.1.2 j)) := by
        rw [← Real.exp_add]
        refine congrArg Real.exp (congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun _ _ => by rw [sub_zero, Real.sqrt_one]; ring)
          (Finset.sum_congr rfl fun _ _ => ?_))
        dsimp only [ψ_u, γ']
        exact congrArg Real.log (integral_congr_ae (ae_of_all _ fun ξ => by
          dsimp only; rw [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]))
      rw [Finset.sum_congr rfl fun τ _ => hsimp τ, ← Finset.sum_mul]
      have hsum_pos : 0 < ∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * (ω.2 i * Real.sqrt r)) :=
        Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
      rw [Real.log_mul hsum_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
        log_decoupled_partition_function_eq (fun i : Fin (N + 1) => ω.2 i * Real.sqrt r),
        Fintype.card_fin]
      push_cast; rfl
    have hRS0 : RS_0 = Real.log 2 + c_X + α * c_Y := by
      dsimp only [RS_0, c_X, c_Y, L_X, ψ_u, γ, γ']
      rw [perceptronRSFunctional_eq_log_two_add]
      ring
    dsimp only [A_0, f₁, f₂]
    rw [hlogZ, hRS0, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [α]
    have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    generalize (∑ i : Fin (N + 1), L_X (ω.2 i)) = SX_sum
    generalize (∑ j : Fin M, ψ_u (ω.1.2 j)) = SY_sum
    field_simp; ring
  have hLX_m : Measurable L_X :=
    (Real.continuous_cosh.comp (by fun_prop)).log (fun _ => (Real.cosh_pos _).ne') |>.measurable
  have hLX_bd (z : ℝ) : |L_X z| ≤ |D| * |z| := by
    dsimp only [L_X]
    rw [abs_of_nonneg (Real.log_cosh_nonneg _)]
    refine (Real.log_cosh_le_abs _).trans ?_
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right hsr_le (abs_nonneg z)
  have hz1_int : Integrable (fun z : ℝ => |z|) γ :=
    by simpa [pow_one] using (integrable_pow_gaussianReal 0 1 1).abs
  have hcX_bd : |c_X| ≤ |D| := by
    have hz_int : Integrable (fun z : ℝ => |D| * |z|) γ := hz1_int.const_mul |D|
    have h1 : |c_X| ≤ ∫ z : ℝ, |D| * |z| ∂γ :=
      abs_integral_le_integral_abs.trans (integral_mono
        (f := fun z => |L_X z|) (g := fun z => |D| * |z|)
        (hz_int.mono' hLX_m.norm.aestronglyMeasurable
          (ae_of_all _ fun z => by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hLX_bd z))
        hz_int hLX_bd)
    have h_abs_z_le : ∫ z : ℝ, |z| ∂γ ≤ 1 := by
      have hsq : (∫ z : ℝ, |z| ∂γ) ^ 2 ≤ ∫ z : ℝ, |z| ^ 2 ∂γ :=
        MeasureTheory.sq_integral_le_integral_sq continuous_abs.measurable
          (by simpa only [sq_abs] using integrable_pow_gaussianReal 0 1 2)
      have hvar : ∫ z : ℝ, |z| ^ 2 ∂γ = 1 := by
        simp_rw [sq_abs]; simpa using integral_pow_add_two_gaussianReal 0
      rw [hvar] at hsq
      nlinarith [integral_nonneg (μ := γ) fun z => abs_nonneg z]
    rw [integral_const_mul] at h1
    nlinarith [abs_nonneg D]
  have hf₁_bd (z : ℝ) : |f₁ z| ≤ |D| * (|z| + 1) := by
    dsimp only [f₁]
    calc |L_X z - c_X| ≤ |L_X z| + |c_X| := abs_sub _ _
      _ ≤ |D| * |z| + |D| := add_le_add (hLX_bd z) hcX_bd
      _ = |D| * (|z| + 1) := by ring
  have hB₁_int (j : ℕ) : Integrable (fun z : ℝ => (|D| * (|z| + 1)) ^ j) γ := by
    have heq : (fun z : ℝ => (|D| * (|z| + 1)) ^ j) =
        fun z => |D| ^ j * ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * |z ^ l| := by
      funext z; rw [mul_pow, add_pow]; congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [one_pow, mul_one, abs_pow, mul_comm]
    rw [heq]
    exact (integrable_finsetSum (Finset.range (j + 1)) fun l _ =>
      (integrable_pow_gaussianReal 0 1 l).abs.const_mul (j.choose l : ℝ)).const_mul (|D| ^ j)
  have hf₁_int (j : ℕ) : Integrable (fun z : ℝ => f₁ z ^ j) γ :=
    (hB₁_int j).mono' ((hLX_m.sub_const c_X).pow_const j).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf₁_bd z) j)
  have hLX1_int : Integrable L_X γ :=
    (hz1_int.const_mul |D|).mono' hLX_m.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hLX_bd z)
  have hLX2_int : Integrable (fun z => L_X z ^ 2) γ :=
    ((integrable_pow_gaussianReal 0 1 2).const_mul (D ^ 2)).mono'
      (hLX_m.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        calc |L_X z| ^ 2 ≤ (|D| * |z|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hLX_bd z) 2
          _ = D ^ 2 * z ^ 2 := by rw [mul_pow, sq_abs, sq_abs])
  have hf₁_0 : ∫ z, f₁ z ∂γ = 0 := by
    dsimp only [f₁]
    rw [integral_sub hLX1_int (integrable_const c_X), integral_const, probReal_univ, one_smul,
      sub_self]
  have hf₁_mom (j : ℕ) : |∫ z, f₁ z ^ j ∂γ| ≤ B₁ j :=
    abs_integral_le_integral_abs.trans (integral_mono (f := fun z => |f₁ z ^ j|)
      (g := fun z => (|D| * (|z| + 1)) ^ j) (hf₁_int j).abs (hB₁_int j) fun z => by
        dsimp only; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hf₁_bd z) j)
  have hψu_m : Measurable ψ_u :=
    Real.measurable_log.comp (measurable_integral_exp_cavityPath hu q)
  have hψu_bd (z : ℝ) : |ψ_u z| ≤ |D| :=
    abs_log_integral_exp_le_of_ae_abs_le (hu.comp (by fun_prop)).aemeasurable
      (ae_of_all _ fun _ => hB _)
  have hf₂_bd (z : ℝ) : |f₂ z| ≤ 2 * |D| := by
    dsimp only [f₂]
    have hcY_bd : |c_Y| ≤ |D| := abs_integral_le_of_forall_abs_le _ hψu_bd
    linarith [abs_sub (ψ_u z) c_Y, hψu_bd z]
  have hf₂_int (j : ℕ) : Integrable (fun z : ℝ => f₂ z ^ j) γ :=
    Integrable.of_bound ((hψu_m.sub_const c_Y).pow_const j).aestronglyMeasurable
      ((2 * |D|) ^ j) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf₂_bd z) j)
  have hψu1_int : Integrable ψ_u γ :=
    Integrable.of_bound hψu_m.aestronglyMeasurable |D|
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hψu_bd z)
  have hψu2_int : Integrable (fun z => ψ_u z ^ 2) γ :=
    Integrable.of_bound (hψu_m.pow_const 2).aestronglyMeasurable (|D| ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψu_bd z) 2)
  have hf₂_0 : ∫ z, f₂ z ∂γ = 0 := by
    dsimp only [f₂]
    rw [integral_sub hψu1_int (integrable_const c_Y), integral_const, probReal_univ, one_smul,
      sub_self]
  have hf₂_mom (j : ℕ) : |∫ z, f₂ z ^ j ∂γ| ≤ B₂ j :=
    abs_integral_le_of_forall_abs_le _ fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hf₂_bd z) j
  have hv₁_eq : ∫ z, f₁ z ^ 2 ∂γ = (∫ z, L_X z ^ 2 ∂γ) - c_X ^ 2 := by
    have hL2 : MemLp L_X 2 γ := (memLp_two_iff_integrable_sq hLX_m.aestronglyMeasurable).2 hLX2_int
    change (∫ z, (L_X z - ∫ y, L_X y ∂γ) ^ 2 ∂γ) = (∫ z, L_X z ^ 2 ∂γ) - (∫ z, L_X z ∂γ) ^ 2
    rw [← variance_eq_integral hL2.aemeasurable, variance_eq_sub hL2]
    rfl
  have hv₂_eq : ∫ z, f₂ z ^ 2 ∂γ = (∫ z, ψ_u z ^ 2 ∂γ) - c_Y ^ 2 := by
    have hL2 : MemLp ψ_u 2 γ := (memLp_two_iff_integrable_sq hψu_m.aestronglyMeasurable).2 hψu2_int
    change (∫ z, (ψ_u z - ∫ y, ψ_u y ∂γ) ^ 2 ∂γ) = (∫ z, ψ_u z ^ 2 ∂γ) - (∫ z, ψ_u z ∂γ) ^ 2
    rw [← variance_eq_integral hL2.aemeasurable, variance_eq_sub hL2]
    rfl
  -- Rewrite the expectation over `P = (P_g × P_z) × P_z'` as an integral over `P_z' × P_z`.
  have hint_eq :
      ∫ ω, (A_0 ω - RS_0) ^ m ∂P =
        ∫ p : (Fin (N + 1) → ℝ) × (Fin M → ℝ),
          (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f₁ (p.1 i) +
            ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j, f₂ (p.2 j)) ^ m ∂(P_z'.prod P_z) := by
    simp_rw [hpt_V]
    let H (p : (Fin (N + 1) → ℝ) × (Fin M → ℝ)) : ℝ :=
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f₁ (p.1 i) +
        ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j, f₂ (p.2 j)) ^ m
    have hHm : Measurable H := by
      have hm1 : Measurable fun p : (Fin (N + 1) → ℝ) × (Fin M → ℝ) =>
          ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f₁ (p.1 i) :=
        (Finset.measurable_sum _ fun i _ =>
          (hLX_m.sub_const c_X).comp ((measurable_pi_apply i).comp measurable_fst)).const_mul _
      have hm2 : Measurable fun p : (Fin (N + 1) → ℝ) × (Fin M → ℝ) =>
          ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j, f₂ (p.2 j) :=
        (Finset.measurable_sum _ fun j _ =>
          (hψu_m.sub_const c_Y).comp ((measurable_pi_apply j).comp measurable_snd)).const_mul _
      exact (hm1.add hm2).pow_const m
    have hmp : MeasurePreserving
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          (ω.2, ω.1.2))
        P (P_z'.prod P_z) := by
      have h1 : MeasurePreserving
          (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
            (ω.1.2, ω.2)) P (P_z.prod P_z') :=
        (measurePreserving_snd (μ := P_g) (ν := P_z)).prod (MeasurePreserving.id P_z')
      exact (Measure.measurePreserving_swap (μ := P_z) (ν := P_z')).comp h1
    exact hmp.integral_comp_of_aestronglyMeasurable hHm.aestronglyMeasurable
  rw [hint_eq]
  have hmain := hC_two γ γ hf₁_int hf₁_0 hf₁_mom hf₂_int hf₂_0 hf₂_mom (N + 1) M
    (Nat.succ_pos N) (by push_cast; exact hMN)
  have hN_cast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hN_cast] at hmain ⊢
  dsimp only [P_z', P_z, γ', γ] at hmain ⊢
  refine (le_of_eq ?_).trans hmain
  congr 2
  rw [hv₁_eq, hv₂_eq]

/-- **ODE with higher-order remainder `O((N + 1)^{-(m+1)/2})`:**
feeding `integral_interpolating_centered_abs_pow_le` into `abs_interpolating_term_VII_le` and
`abs_interpolating_term_VIII_le` gives `ψ_m'(s) = -(r q / (2 (N + 1))) m (m - 1) ψ_{m-2}(s) + D`
with `|D| ≤ C_rem (√(N + 1))⁻¹^{m+1}` uniformly on `s ∈ (0, 1)`. -/
private lemma exists_hasDerivAt_interpolating_centered_moment_sub_le (D : ℝ) (m : ℕ) :
    ∃ K C_rem : ℝ, 0 ≤ K ∧ 0 ≤ C_rem ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Ioo (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s' *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
        let A (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s)
        let RS (s' : ℝ) : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s') / 2) * r * (1 - q)
        let V (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          A s' ω - RS s'
        let ε : ℝ := (Real.sqrt ((N : ℝ) + 1))⁻¹
        ∃ D_rem : ℝ,
          HasDerivAt (fun s' => ∫ ω, V s' ω ^ m ∂P)
            (((m : ℝ) * ((m : ℝ) - 1) / 2 * ε ^ 2 * (-(r * q))) *
              (∫ ω, V s ω ^ (m - 2) ∂P) + D_rem) s ∧
          |D_rem| ≤ C_rem * ε ^ (m + 1) := by
  obtain ⟨K_7, C_7, hK7_0, hC7_0, h_7⟩ := abs_interpolating_term_VII_le D m
  obtain ⟨K_8, C_8, hK8_0, hC8_0, h_8⟩ := abs_interpolating_term_VIII_le D m
  obtain ⟨K_ap, C_ap, hKap_0, hCap_0, h_ap⟩ := integral_interpolating_centered_abs_pow_le D m
  let K : ℝ := max (max K_7 K_8) (max K_ap 1)
  let C_rem : ℝ := C_7 * (C_ap + 1) + C_8 * (C_ap + 1)
  refine ⟨K, C_rem, by positivity, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s E_s A RS V ε
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hs_cc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  have hα0 : 0 ≤ (M : ℝ) / ((N : ℝ) + 1) := by positivity
  have hα_7 : (M : ℝ) / ((N : ℝ) + 1) * K_7 ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_left _ _)) hα0).trans hα
  have hα_8 : (M : ℝ) / ((N : ℝ) + 1) * K_8 ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _)) hα0).trans hα
  have hα_ap : (M : ℝ) / ((N : ℝ) + 1) * K_ap ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_right _ _)) hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 (perceptronRhat_nonneg u q)
  have hode := hasDerivAt_interpolating_centered_moment_pow (N := N) (M := M) hu hq_mem hr0 hs m
  dsimp only at hode
  let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
    Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
  let VII : ℝ :=
    -(m : ℝ) / 2 * ∫ ω,
      (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
            deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
      V s ω ^ (m - 1) ∂P
  let VIII : ℝ :=
    (m : ℝ) * ((m : ℝ) - 1) / (2 * ((N : ℝ) + 1)) * ∫ ω,
      (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
            deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
      V s ω ^ (m - 2) ∂P
  have hL_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε2 : ε ^ 2 = ((N : ℝ) + 1)⁻¹ := by
    dsimp only [ε]; rw [inv_pow, Real.sq_sqrt hL_pos.le]
  have hε_le1 : ε ≤ 1 := by
    dsimp only [ε]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  refine ⟨VII + VIII, hode.congr_deriv ?_, ?_⟩
  · have hIX_eq :
        -(r * q / (2 * ((N : ℝ) + 1))) * (m : ℝ) * ((m : ℝ) - 1) *
            (∫ ω, V s ω ^ (m - 2) ∂P) =
          ((m : ℝ) * ((m : ℝ) - 1) / 2 * ε ^ 2 * (-(r * q))) *
            (∫ ω, V s ω ^ (m - 2) ∂P) := by
      rw [hε2]
      generalize (∫ ω, V s ω ^ (m - 2) ∂P) = IV2
      field_simp
    dsimp only [P, P_g, P_z, P_z', μ_s, E_s, A, RS, V, S_fn, VII, VIII] at hIX_eq ⊢
    rw [hIX_eq, add_comm]
  · rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · have h0 : VII + VIII = 0 := by dsimp only [VII, VIII]; simp
      rw [h0, abs_zero]; positivity
    have hb7 := h_7 N M hs_cc hd hb hα_7 hq hr
    have hb8 := h_8 N M hs_cc hd hb hα_8 hq hr
    have hb_ap := h_ap N M hs_cc hd hb hα_ap hq hr
    let I_V : ℝ := ∫ ω, |V s ω| ^ m ∂P
    have hIV0 : 0 ≤ I_V := integral_nonneg fun _ => by positivity
    have hm_pos_r : (0 : ℝ) < m := Nat.cast_pos.2 hm_pos
    have hrp_le (r_idx : ℕ) (hr_le : r_idx ≤ m) :
        I_V ^ ((r_idx : ℝ) / (m : ℝ)) ≤ (C_ap + 1) * ε ^ r_idx := by
      have hCap1 : 1 ≤ C_ap + 1 := by linarith
      have hrp_Cap : (C_ap + 1) ^ ((r_idx : ℝ) / (m : ℝ)) ≤ C_ap + 1 := by
        have hdiv_le1 : (r_idx : ℝ) / (m : ℝ) ≤ 1 :=
          (div_le_one hm_pos_r).2 (by exact_mod_cast hr_le)
        calc (C_ap + 1) ^ ((r_idx : ℝ) / (m : ℝ)) ≤ (C_ap + 1) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hCap1 hdiv_le1
          _ = C_ap + 1 := Real.rpow_one _
      have hIV_le : I_V ≤ (C_ap + 1) * ε ^ m :=
        hb_ap.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      calc I_V ^ ((r_idx : ℝ) / (m : ℝ))
          ≤ ((C_ap + 1) * ε ^ m) ^ ((r_idx : ℝ) / (m : ℝ)) :=
            Real.rpow_le_rpow hIV0 hIV_le (by positivity)
        _ = (C_ap + 1) ^ ((r_idx : ℝ) / (m : ℝ)) * (ε ^ m) ^ ((r_idx : ℝ) / (m : ℝ)) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ = (C_ap + 1) ^ ((r_idx : ℝ) / (m : ℝ)) * ε ^ r_idx := by
            congr 1
            rw [← Real.rpow_natCast ε m, ← Real.rpow_mul (by positivity)]
            have hcancel : (m : ℝ) * ((r_idx : ℝ) / (m : ℝ)) = (r_idx : ℝ) := by field_simp
            rw [hcancel, Real.rpow_natCast]
        _ ≤ (C_ap + 1) * ε ^ r_idx :=
            mul_le_mul_of_nonneg_right hrp_Cap (by positivity)
    have h7_final : |VII| ≤ C_7 * (C_ap + 1) * ε ^ (m + 1) := by
      have h1 := hrp_le (m - 1) (Nat.sub_le m 1)
      have hexp7 : ((N : ℝ) + 1)⁻¹ * ε ^ (m - 1) = ε ^ (m + 1) := by
        rw [← hε2, ← pow_add]; congr 1; omega
      calc |VII| ≤ C_7 / ((N : ℝ) + 1) * I_V ^ (((m - 1 : ℕ) : ℝ) / (m : ℝ)) := hb7
        _ ≤ C_7 / ((N : ℝ) + 1) * ((C_ap + 1) * ε ^ (m - 1)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C_7 * (C_ap + 1) * (((N : ℝ) + 1)⁻¹ * ε ^ (m - 1)) := by rw [div_eq_mul_inv]; ring
        _ = C_7 * (C_ap + 1) * ε ^ (m + 1) := by rw [hexp7]
    have h8_final : |VIII| ≤ C_8 * (C_ap + 1) * ε ^ (m + 1) := by
      have h1 := hrp_le (m - 2) (Nat.sub_le m 2)
      have hexp8 : (((N : ℝ) + 1) ^ 2)⁻¹ * ε ^ (m - 2) ≤ ε ^ (m + 1) := by
        have hsq_inv : (((N : ℝ) + 1) ^ 2)⁻¹ = ε ^ 4 := by
          rw [← inv_pow, ← hε2, ← pow_mul]
        rw [hsq_inv, ← pow_add]
        exact pow_le_pow_of_le_one (by positivity) hε_le1 (by omega)
      calc |VIII| ≤ C_8 / ((N : ℝ) + 1) ^ 2 * I_V ^ (((m - 2 : ℕ) : ℝ) / (m : ℝ)) := hb8
        _ ≤ C_8 / ((N : ℝ) + 1) ^ 2 * ((C_ap + 1) * ε ^ (m - 2)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C_8 * (C_ap + 1) * ((((N : ℝ) + 1) ^ 2)⁻¹ * ε ^ (m - 2)) := by
            rw [div_eq_mul_inv]; ring
        _ ≤ C_8 * (C_ap + 1) * ε ^ (m + 1) :=
            mul_le_mul_of_nonneg_left hexp8 (by positivity)
    calc |VII + VIII| ≤ |VII| + |VIII| := abs_add_le _ _
      _ ≤ C_7 * (C_ap + 1) * ε ^ (m + 1) + C_8 * (C_ap + 1) * ε ^ (m + 1) :=
          add_le_add h7_final h8_final
      _ = C_rem * ε ^ (m + 1) := by dsimp only [C_rem]; ring

/-! ### Section 3: Main CLT theorems along the interpolation and at `s = 1` -/

/-- **Quantitative free energy moment CLT along the `s`-interpolation (`s ∈ [0, 1]`):**
Given `D` and `k`, there exist `K, C ≥ 0` (chosen before `N, M, s, u, q, r`) such that under (2.7),
`α K ≤ 1`, `(q, r)` solving (2.68), and `s ∈ [0, 1]`,
`|𝔼[(A(s) - RS(s))^k] - (√(N + 1))⁻¹^k a(k) b(s)^{k/2}| ≤ C (√(N + 1))⁻¹^{k+1}`,
where `b(s) = Var_z(log cosh(z √r)) + α Var_z(log 𝔼_ξ exp u(θ)) - r q s`. -/
theorem interpolating_free_energy_clt (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let γ := gaussianReal 0 1
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let P_z := Measure.pi fun _ : Fin M => γ
        let P_z' := Measure.pi fun _ : Fin (N + 1) => γ
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => γ)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt s *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let RS : ℝ := perceptronRSFunctional u α r q + ((1 - s) / 2) * r * (1 - q)
        let ψ_u (z : ℝ) : ℝ :=
          Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
        let b_s : ℝ :=
          ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
              (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
            α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2) - r * q * s
        |∫ ω, (A ω - RS) ^ k ∂P -
            ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ k * (∫ x : ℝ, x ^ k ∂γ) * b_s ^ (k / 2)| ≤
          C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (k + 1) := by
  choose! K_ode C_rem hKode0 hCrem0 h_ode using
    fun m => exists_hasDerivAt_interpolating_centered_moment_sub_le D m
  have hex_dec : ∀ m : ℕ, ∃ C_d : ℝ, 0 ≤ C_d ∧
      (1 ≤ m → ∀ (N M : ℕ) {u : ℝ → ℝ} (_hu : Measurable u) (_hB : ∀ x, |u x| ≤ |D|)
        (_hMN : (M : ℝ) ≤ (N : ℝ) + 1) {q r : ℝ} (_hr_le : r ≤ |D| ^ 2),
        let γ := gaussianReal 0 1
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let P_z := Measure.pi fun _ : Fin M => γ
        let P_z' := Measure.pi fun _ : Fin (N + 1) => γ
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => γ)
        let E_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (Real.sqrt 0 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - 0) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 0) * ω.2 i * Real.sqrt r
        let A_0 (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_0 ω x) ∂μ_s)
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let RS_0 : ℝ := perceptronRSFunctional u α r q + ((1 - 0) / 2) * r * (1 - q)
        let ψ_u (z : ℝ) : ℝ :=
          Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
        let b₀ : ℝ :=
          ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
              (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
            α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2)
        |∫ ω, (A_0 ω - RS_0) ^ m ∂P -
            ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ m * (∫ x : ℝ, x ^ m ∂γ) * b₀ ^ (m / 2)| ≤
          C_d * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (m + 1)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, le_rfl, fun h => by omega⟩
    · obtain ⟨C_d, hCd0, hCd⟩ := abs_integral_interpolating_zero_pow_sub_le D hm
      exact ⟨C_d, hCd0, fun _ => hCd⟩
  choose! C_dec hCdec0 h_dec using hex_dec
  let B_max : ℝ := |D| ^ 2
  obtain ⟨C_seq, _, hC_nn, hC_rec⟩ :=
    exists_linear_clt_const B_max (by positivity)
      (fun m => if m ≤ k then C_rem m else 0) C_dec
      (fun m => by split_ifs <;> [exact hCrem0 m; exact le_rfl]) hCdec0
  let K : ℝ := 1 + ∑ m ∈ Finset.range (k + 1), K_ode m
  have hK_ge1 : 1 ≤ K :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun m _ => hKode0 m)
  refine ⟨K, C_seq k, zero_le_one.trans hK_ge1, hC_nn k, ?_⟩
  intro N M s hs u hd hb hα q r hq hr γ P_g P_z P_z' P μ_s E_s_s A_s α RS_s ψ_u b_s
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z', γ]; infer_instance
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα1 : α ≤ 1 := by
    have h1 : α * 1 ≤ α * K := mul_le_mul_of_nonneg_left hK_ge1 hα0
    linarith [hα]
  have hMN : (M : ℝ) ≤ (N : ℝ) + 1 :=
    (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).1 hα1
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  have hrhat_mem : perceptronRhat u q ∈ Icc (0 : ℝ) (|D| ^ 2) :=
    rhat_mem_Icc hu.abs_deriv_le_abs q
      (fun z => integrable_exp_cavityPath_new hu.measurable hu.le_abs q z)
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hα0 hrhat_mem.1
  have hr_le : r ≤ |D| ^ 2 := by
    rw [hr]
    calc α * perceptronRhat u q ≤ 1 * |D| ^ 2 :=
          mul_le_mul hα1 hrhat_mem.2 hrhat_mem.1 zero_le_one
      _ = |D| ^ 2 := one_mul _
  have hB_le : |-(r * q)| ≤ B_max := by
    rw [abs_neg, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hq_mem.1]
    calc r * q ≤ |D| ^ 2 * 1 := mul_le_mul hr_le hq_mem.2 hq_mem.1 (sq_nonneg _)
      _ = B_max := mul_one _
  let E_path (t : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ j : Fin M, u (Real.sqrt t *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - t) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
    ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 i * Real.sqrt r
  let A_path (t : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_path t ω x) ∂μ_s)
  let RS_path (t : ℝ) : ℝ :=
    perceptronRSFunctional u α r q + ((1 - t) / 2) * r * (1 - q)
  let ψ (m : ℕ) (t : ℝ) : ℝ := ∫ ω, (A_path t ω - RS_path t) ^ m ∂P
  let b₀ : ℝ :=
    ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
        (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
      α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2)
  let ε : ℝ := (Real.sqrt ((N : ℝ) + 1))⁻¹
  have hε_pos : 0 < ε := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  let a (n : ℕ) : ℝ := ∫ x : ℝ, x ^ n ∂γ
  have ha0 : a 0 = 1 := by simp [a, γ]
  have ha1 : a 1 = 0 := by simp [a, γ, integral_id_gaussianReal]
  have ha : ∀ n, a (n + 2) = (n + 1) * a n := fun n => integral_pow_add_two_gaussianReal n
  -- Apply `linear_clt_induction` up to degree `k` by restricting `ψ` above `k` to the reference
  -- (or simpler: prove by strong induction on `m ≤ k` directly using `abs_sub_linear_clt_ref_le`!).
  have hind_k : ∀ m ≤ k, ∀ t ∈ Icc (0 : ℝ) 1,
      |ψ m t - ε ^ m * a m * (b₀ + (-(r * q)) * t) ^ (m / 2)| ≤
        C_seq m * ε ^ (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hmk t ht
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · have h0 : ψ 0 t = 1 := by simp [ψ]
        rw [h0, ha0, pow_zero, one_mul, Nat.zero_div, pow_zero, mul_one, sub_self, abs_zero]
        exact mul_nonneg (hC_nn 0) (by positivity)
      · have hKode_le : K_ode m ≤ K := by
          dsimp only [K]
          have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hmk)
          have hs := Finset.single_le_sum (fun j _ => hKode0 j) hmem
          linarith
        have hα_m : α * K_ode m ≤ 1 := (mul_le_mul_of_nonneg_left hKode_le hα0).trans hα
        have hprev : ∀ t' ∈ Icc (0 : ℝ) 1,
            |ψ (m - 2) t' - ε ^ (m - 2) * a (m - 2) * (b₀ + (-(r * q)) * t') ^ ((m - 2) / 2)| ≤
              C_seq (m - 2) * ε ^ (m - 1) := by
          intro t' ht'
          rcases Nat.lt_or_ge m 2 with hm2 | hm2
          · obtain rfl : m = 1 := by omega
            have h0 : ψ 0 t' = 1 := by simp [ψ]
            rw [show 1 - 2 = 0 by rfl, h0, ha0]
            simp only [pow_zero, Nat.zero_div, mul_one, sub_self, abs_zero]
            exact hC_nn 0
          · have h := ih (m - 2) (by omega) (by omega) t' ht'
            rwa [show m - 2 + 1 = m - 1 by omega] at h
        have hode_m : ∀ t' ∈ Ioo (0 : ℝ) 1, ∃ D_rem,
            HasDerivAt (ψ m)
              (((m : ℝ) * ((m : ℝ) - 1) / 2 * ε ^ 2 * (-(r * q))) * ψ (m - 2) t' + D_rem) t' ∧
            |D_rem| ≤ (if m ≤ k then C_rem m else 0) * ε ^ (m + 1) := by
          intro t' ht'
          rw [ite_eq_left_iff.2 fun h => absurd hmk h]
          exact h_ode m N M ht' hd hb hα_m hq hr
        have hdec_m : |ψ m 0 - ε ^ m * a m * b₀ ^ (m / 2)| ≤ C_dec m * ε ^ (m + 1) :=
          h_dec m hm_pos N M hu.measurable (fun x => (hu.abs_le x).trans (le_abs_self D))
            hMN hr_le
        have hψm_cont : ContinuousOn (ψ m) (Icc 0 1) :=
          continuousOn_interpolating_centered_moment_pow (N := N) (M := M)
            hu.differentiable.continuous hu.abs_le q r m
        have hstep := abs_sub_linear_clt_ref_le hε_pos hB_le (by positivity) ha1 ha hm_pos
          hψm_cont (by rw [ite_eq_left_iff.2 fun h => absurd hmk h]; exact hCrem0 m)
          (hC_nn (m - 2)) hode_m hprev hdec_m ht
        exact hstep.trans (mul_le_mul_of_nonneg_right (hC_rec m hm_pos) (by positivity))
  have hres := hind_k k le_rfl s hs
  refine (le_of_eq ?_).trans hres
  congr 2
  have hb_eq : b_s = b₀ + -(r * q) * s := by dsimp only [b_s, b₀]; ring
  rw [hb_eq]

/-- **Talagrand Theorem 2.5.3 (Central Limit Theorem for the Free Energy Moments):**
Given `D` and `k`, there exist constants `K, C ≥ 0` (chosen before `N, M, u, q, r`) such that
whenever `u` satisfies (2.7), `α = M / (N + 1)` satisfies `α * K ≤ 1`, and `(q, r)` solves (2.68),
the random finite-size free energy `p_{N+1, M}(g) = (N + 1)⁻¹ log ∑_τ exp(∑_j u(S_j(g, τ)))`
satisfies
$$\left|\mathbb{E}\bigl(p_{N+1, M}(g) - F(\alpha, r, q)\bigr)^k -
  \bigl(\sqrt{N + 1}\bigr)^{-k}\,a(k)\,b^{\lfloor k / 2 \rfloor}\right|
  \le C\,\bigl(\sqrt{N + 1}\bigr)^{-(k + 1)},$$
where `a(k) = 𝔼[x^k]` for `x ~ 𝒩(0, 1)` and
$$b = \mathbb{E}\bigl(\log \cosh(z\sqrt{r})\bigr)^2 -
  \bigl(\mathbb{E}\log \cosh(z\sqrt{r})\bigr)^2 +
  \alpha\Bigl(\mathbb{E}\bigl(\log\mathbb{E}_\xi \exp u(\theta)\bigr)^2 -
    \bigl(\mathbb{E}\log\mathbb{E}_\xi \exp u(\theta)\bigr)^2\Bigr) - q r$$
with `θ = √q z + √(1 - q) ξ` (including the constraint variance term
`α Var_z(log 𝔼_ξ e^{u(θ)})` omitted in Talagrand's printed display). No sign assumption on `b` is
needed. -/
theorem perceptron_free_energy_clt (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let γ := gaussianReal 0 1
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let ψ_u (z : ℝ) : ℝ :=
          Real.log (∫ ξ : ℝ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂γ)
        let b : ℝ :=
          ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
              (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
            α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2) - q * r
        |∫ g : Fin M → Fin (N + 1) → ℝ,
            (((N : ℝ) + 1)⁻¹ * Real.log (∑ τ : Fin (N + 1) → ℤˣ,
                Real.exp (∑ j : Fin M,
                  u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)))) -
              perceptronRSFunctional u α r q) ^ k ∂P_g -
            ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ k * (∫ x : ℝ, x ^ k ∂γ) * b ^ (k / 2)| ≤
          C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (k + 1) := by
  obtain ⟨K, C, hK0, hC0, h_interp⟩ := interpolating_free_energy_clt D k
  refine ⟨K, C, hK0, hC0, ?_⟩
  intro N M u hd hb hα q r hq hr γ P_g α ψ_u b
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hs1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h := h_interp N M hs1 hd hb hα hq hr
  dsimp only at h
  refine (le_of_eq ?_).trans h
  congr 1
  congr 1
  · -- At `s = 1`, `A(1, ω)` depends only on `ω.1.1 = g` and `RS(1) = F(α, r, q)`.
    let P_z := Measure.pi fun _ : Fin M => γ
    let P_z' := Measure.pi fun _ : Fin (N + 1) => γ
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod (Measure.pi fun _ : Fin M => γ)
    let p_g (g : Fin M → Fin (N + 1) → ℝ) : ℝ :=
      (((N : ℝ) + 1)⁻¹ * Real.log (∑ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ j : Fin M,
            u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)))) -
        perceptronRSFunctional u α r q) ^ k
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp
            ((∑ j : Fin M, u (Real.sqrt 1 *
                ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
              Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j))) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r) ∂μ_s) -
          (perceptronRSFunctional u α r q + ((1 - 1) / 2) * r * (1 - q))) ^ k =
        p_g ω.1.1 := by
      dsimp only [p_g]
      congr 1
      have hRS : perceptronRSFunctional u α r q + ((1 - 1) / 2) * r * (1 - q) =
          perceptronRSFunctional u α r q := by ring
      rw [hRS]
      congr 1
      congr 1
      rw [integral_sum_exp_interpolating_eq hu.measurable hu.le 1 q r ω]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => congrArg Real.exp ?_
      have hterm1 : (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - 1) * ω.2 i * Real.sqrt r) =
          0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [sub_self, Real.sqrt_zero]; ring
      rw [hterm1, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hint_exp : (∫ ξ : ℝ, Real.exp (u (Real.sqrt 1 *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ))) ∂γ) =
          Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ))) := by
        have hcongr : (fun ξ : ℝ => Real.exp (u (Real.sqrt 1 *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - 1) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * ξ)))) =
            fun _ : ℝ =>
              Real.exp (u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((τ i : ℤ) : ℝ))) := by
          funext ξ
          rw [Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, add_zero]
        have : IsProbabilityMeasure γ := by dsimp only [γ]; infer_instance
        rw [hcongr, integral_const, probReal_univ, one_smul]
      rw [hint_exp, Real.log_exp]
    symm
    refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
    have h1 := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g.prod P_z) (ν := P_z')
      (fun gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ) => p_g gz.1)
    have h2 := integral_prod_fun_fst_of_isProbabilityMeasure (μ := P_g) (ν := P_z) p_g
    exact h1.trans h2
  · have hb_eq : b =
        ((∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
            (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2) +
          α * ((∫ z : ℝ, ψ_u z ^ 2 ∂γ) - (∫ z : ℝ, ψ_u z ∂γ) ^ 2) - r * q * 1 := by
      dsimp only [b]; ring
    rw [hb_eq]

/-- **Talagrand Theorem 2.5.3 with the printed `b` when the constraint `z`-variance vanishes**
(for instance whenever `q = 0`, i.e., `r̂(0) = 0` or `M = 0`):
under `(∫ ψ_u(z)² dγ) - (∫ ψ_u(z) dγ)² = 0`, `b` reduces to
`𝔼(log cosh(z √r))² - (𝔼 log cosh(z √r))² - q r`. -/
theorem perceptron_free_energy_clt_of_zero_constraint_var (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        (_hvar :
          (∫ z : ℝ, Real.log (∫ ξ : ℝ,
              Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) ^ 2
              ∂gaussianReal 0 1) -
            (∫ z : ℝ, Real.log (∫ ξ : ℝ,
              Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1)
              ∂gaussianReal 0 1) ^ 2 = 0),
        let γ := gaussianReal 0 1
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => γ
        let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
        let b : ℝ :=
          (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ^ 2 ∂γ) -
            (∫ z : ℝ, Real.log (Real.cosh (z * Real.sqrt r)) ∂γ) ^ 2 - q * r
        |∫ g : Fin M → Fin (N + 1) → ℝ,
            (((N : ℝ) + 1)⁻¹ * Real.log (∑ τ : Fin (N + 1) → ℤˣ,
                Real.exp (∑ j : Fin M,
                  u ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, g j i * ((τ i : ℤ) : ℝ)))) -
              perceptronRSFunctional u α r q) ^ k ∂P_g -
            ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ k * (∫ x : ℝ, x ^ k ∂γ) * b ^ (k / 2)| ≤
          C * ((Real.sqrt ((N : ℝ) + 1))⁻¹) ^ (k + 1) := by
  obtain ⟨K, C, hK0, hC0, h_clt⟩ := perceptron_free_energy_clt D k
  refine ⟨K, C, hK0, hC0, ?_⟩
  intro N M u hd hb hα q r hq hr hvar γ P_g α b
  have h := h_clt N M hd hb hα hq hr
  dsimp only at h
  rwa [hvar, mul_zero, add_zero] at h

end SpinGlasses
