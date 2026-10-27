/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCovarianceRows

/-!
# The cavity estimates with a third-moment remainder (Talagrand, Lemma 1.9.4)

Beyond the Almeida--Thouless line the moment bounds `ν((R - q)²) ≤ K/M`, `ν((R - q)⁴) ≤ K/M²`
fail, so the error terms of Section 1.8 are kept in the form
`K (M^{-3/2} + ν(|R_{1,2} - q|³))` (Eq. (1.277)).  This file proves the two Hölder steps with the
exponent pairs `(3, 3/2)` (second-order Taylor error, Eq. (1.216)) and `(3/2, 3)` (the `ν₀ → ν`
error, Eq. (1.215)), and the elementary inequalities that turn them into the cubic remainder.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

section Arithmetic

/-- Weighted AM-GM in the form used for all remainders: if `A ≤ c D'` and `D ≤ D'` then
`A^s D^t ≤ c D'` for `s + t = 1`, `c ≥ 1`. -/
theorem rpow_mul_rpow_le_of_le {A D D' c s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hA : 0 ≤ A) (hAD : A ≤ c * D') (hD : 0 ≤ D) (hDD : D ≤ D') (hc : 1 ≤ c) :
    A ^ s * D ^ t ≤ c * D' := by
  have hD' : 0 ≤ D' := hD.trans hDD
  have hc0 : 0 ≤ c := by linarith
  calc A ^ s * D ^ t ≤ (c * D') ^ s * D' ^ t := by
        gcongr
    _ = c ^ s * (D' ^ s * D' ^ t) := by rw [Real.mul_rpow hc0 hD']; ring
    _ = c ^ s * D' := by
        rw [← Real.rpow_add' hD' (by rw [hst]; norm_num), hst, Real.rpow_one]
    _ ≤ c * D' := by
        gcongr
        calc c ^ s ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc (by linarith)
          _ = c := Real.rpow_one c

/-- `t m² ≤ t³/3 + 2 m³/3` for `t, m ≥ 0` (Young's inequality with exponents `3`, `3/2`). -/
theorem mul_sq_le_cube_third {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    t * m ^ 2 ≤ t ^ 3 / 3 + 2 * m ^ 3 / 3 := by
  nlinarith only [mul_nonneg (sq_nonneg (t - m)) (add_nonneg ht (mul_nonneg (by norm_num : (0 : ℝ)
    ≤ 2) hm))]

/-- `(x + y)³ ≤ 4 (x³ + y³)` for `x, y ≥ 0`. -/
theorem add_pow_three_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith only [mul_nonneg (sq_nonneg (x - y)) (add_nonneg hx hy)]

/-- `(u v)^{3/2} ≤ (u³ + v³)/2` for `u, v ≥ 0`. -/
theorem mul_rpow_three_halves_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u * v) ^ (3 / 2 : ℝ) ≤ (u ^ 3 + v ^ 3) / 2 := by
  have e : ∀ w : ℝ, 0 ≤ w → (w ^ (3 / 2 : ℝ)) ^ 2 = w ^ 3 := fun w hw => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw]
    norm_num
  rw [Real.mul_rpow hu hv]
  nlinarith only [sq_nonneg (u ^ (3 / 2 : ℝ) - v ^ (3 / 2 : ℝ)), e u hu, e v hv]

/-- `|x|^{(3 : ℝ)} = |x|^3`. -/
theorem abs_rpow_three (x : ℝ) : |x| ^ (3 : ℝ) = |x| ^ 3 := Real.rpow_natCast |x| 3

end Arithmetic

section Holder

/-- **The second-order Taylor step with exponents `(3, 3/2)`** (Eq. (1.216) of Proposition 1.8.1
with `τ₁ = 3`, `τ₂ = 3/2`): for `x ≠ y`, an observable `F` of the old spins and
`f = F (ε_xε_y - q)`,
`ν(f)` differs from `∑_j w_j b(c_j) 𝔼⟨F (R⁻_j - q)⟩_{old}` by at most
`4 n² (n+2)² β⁴ exp (4 (n+4)² β²) ν(|f|³)^{1/3} ν(|R_{1,2} - q|³)^{2/3}`. -/
theorem sk_pair_taylor_three (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {x y : Fin n} (hxy : x ≠ y) (F : (Fin n → Fin N → ℤˣ) → ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (Dthree : ℝ)
    (hDthree : Dthree = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν (fun σ => F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (some (some r))) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
    4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
      (ν (fun σ => |F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)| ^ 3) ^ (1 / 3 : ℝ) *
        Dthree ^ (2 / 3 : ℝ)) := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hfixz : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have hpr : (3 : ℝ).HolderConjugate (3 / 2) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have T := sk_cavity_nu_sub_nu_zero_sub_deriv_le N n β q h hq
    (fun σ => F (fun r i => σ r i.castSucc) *
      (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) hpr
  have L := sk_cavity_deriv_zero_pair N n β q h hfix qhat hqhat hxy F
  have Z := sk_cavity_decoupled_pair_zero N β q h hfixz hxy F
  have e32 : (2 * (3 / 2 : ℝ)) = 3 := by norm_num
  have e23 : (1 / (3 / 2) : ℝ) = 2 / 3 := by norm_num
  simp only [e32, e23, abs_rpow_three] at T
  simp only [] at T L Z
  rw [Z, L] at T
  rw [← hν, ← hDthree, ← hν] at T
  simpa using T

/-- **Passing from the `(N+1)`-spin average to the old-spin average with exponents `(3/2, 3)`**
(Eq. (1.215) with `τ₁ = 3/2`, `τ₂ = 3`): for an observable `G` of the first `N` spins of `m`
replicas, `|ν(G) - 𝔼⟨G⟩_{old}| ≤ 2 m² β² exp (4 (m+2)² β²) ν(|G|^{3/2})^{2/3}
ν(|R_{1,2} - q|³)^{1/3}`. -/
theorem sk_old_spin_compare_three (N m : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (G : (Fin m → Fin N → ℤˣ) → ℝ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (Dthree : ℝ)
    (hDthree : Dthree = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν (fun σ => G (fun r i => σ r i.castSucc)) -
      ∫ g', ∫ ρ : Fin m → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)| ≤
    2 * (m : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((m : ℝ) + 2) ^ 2 * β ^ 2) *
      (ν (fun σ => |G (fun r i => σ r i.castSucc)| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
        Dthree ^ (1 / 3 : ℝ)) := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hpr : (3 / 2 : ℝ).HolderConjugate 3 :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have T := sk_cavity_nu_sub_nu_zero_le N m β q h hq (fun σ => G (fun r i => σ r i.castSucc)) hpr
  have h0 := sk_cavity_decoupled_endpoint_replicas N β q h (∅ : Finset (Fin m)) G
  simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, integral_const,
    probReal_univ, one_smul, one_mul] at h0
  have e23 : (1 / (3 / 2) : ℝ) = 2 / 3 := by norm_num
  simp only [e23, abs_rpow_three] at T
  rw [h0] at T
  rw [← hν, ← hDthree, ← hν] at T
  exact T

end Holder

section Bounds

variable (N : ℕ) (β h q : ℝ)

/-- `|X - δ| ^ 3 ≤ 4 (|X| ^ 3 + c ^ 3)` when `|δ| ≤ c`. -/
theorem abs_sub_pow_three_le {X δ c : ℝ} (hδ : |δ| ≤ c) :
    |X - δ| ^ 3 ≤ 4 * (|X| ^ 3 + c ^ 3) := by
  have h1 : |X - δ| ≤ |X| + c := (abs_sub _ _).trans (by linarith)
  have hc : 0 ≤ c := (abs_nonneg _).trans hδ
  calc |X - δ| ^ 3 ≤ (|X| + c) ^ 3 := by gcongr
    _ ≤ 4 * (|X| ^ 3 + c ^ 3) := add_pow_three_le (abs_nonneg _) hc

/-- **The cubic size of `f = (R⁻_{ab} - q)(ε_xε_y - q)`:**
`ν(|f|³) ≤ 32 ν(|R_{1,2} - q|³) + 32/M³`. -/
theorem sk_row_Vf_three (n : ℕ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {x y a b : Fin n} (hab : a ≠ b) :
    ν (fun σ => |((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)| ^ 3) ≤
      32 * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) + 32 / (N + 1) ^ 3 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N n β h ν hν
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hmarg : ν (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q| ^ 3) =
      ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) :=
    sk_nu_pair_marginal N β h n ν hν ν₂ hν₂ hab
      (fun u v => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (v i : ℝ)) - q| ^ 3)
  have hpt : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      |((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)| ^ 3 ≤
      32 * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q| ^ 3 + 32 / (N + 1) ^ 3 := fun σ => by
    set X : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q with hX
    set δ : ℝ := (N + 1 : ℝ)⁻¹ * (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
      with hδ
    have e1 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q = X - δ := by
      simp only [hX, hδ, dotProduct, Fin.sum_univ_castSucc]; ring
    have hs : |((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q| ^ 3 ≤ 8 := by
      calc _ ≤ (2 : ℝ) ^ 3 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_units_cast_mul_sub_le_two _ _ hq) 3
        _ = 8 := by norm_num
    have h3 := abs_sub_pow_three_le (X := X) (δ := δ) (c := (N + 1 : ℝ)⁻¹)
      (abs_inv_mul_sign_le _ hM0 _ _)
    rw [e1, abs_mul, mul_pow]
    have hp := mul_le_mul h3 hs (by positivity) (by positivity)
    have e8 : 32 / ((N : ℝ) + 1) ^ 3 = 32 * ((N + 1 : ℝ)⁻¹ ^ 3) := by
      rw [inv_pow]; ring
    linarith only [hp, e8]
  have h1 := hmono _ _ hpt
  rw [hadd, hsmul, hconst, hmarg] at h1
  exact h1

/-- **The `3/2`-power size of a product of two truncated overlaps:**
`ν(|(R⁻_P - q)(R⁻_Q - q)|^{3/2}) ≤ 4 ν(|R_{1,2} - q|³) + 4/M³`. -/
theorem sk_row_Gb_three (m : ℕ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {p₁ p₂ r₁ r₂ : Fin m} (hp : p₁ ≠ p₂) (hr : r₁ ≠ r₂) :
    ν (fun σ => |((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)| ^ (3 / 2 : ℝ)) ≤
      4 * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) + 4 / (N + 1) ^ 3 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N m β h ν hν
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hmarg : ∀ {u v : Fin m}, u ≠ v →
      ν (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ v i : ℝ)) - q| ^ 3) =
      ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) := fun {u v} huv =>
    sk_nu_pair_marginal N β h m ν hν ν₂ hν₂ huv
      (fun u v => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (v i : ℝ)) - q| ^ 3)
  have hpt : ∀ σ : Fin m → Fin (N + 1) → ℤˣ,
      |((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)| ^ (3 / 2 : ℝ) ≤
      2 * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q| ^ 3 +
        2 * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q| ^ 3 + 4 / (N + 1) ^ 3 := fun σ => by
    set X : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q with hX
    set Y : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q with hY
    set δ : ℝ := (N + 1 : ℝ)⁻¹ * (((σ p₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ p₂ (Fin.last N) : ℤˣ) : ℝ))
      with hδ
    set δ' : ℝ := (N + 1 : ℝ)⁻¹ * (((σ r₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ r₂ (Fin.last N) : ℤˣ) : ℝ))
      with hδ'
    have e1 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q = X - δ := by
      simp only [hX, hδ, dotProduct, Fin.sum_univ_castSucc]; ring
    have e2 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q = Y - δ' := by
      simp only [hY, hδ', dotProduct, Fin.sum_univ_castSucc]; ring
    rw [e1, e2, abs_mul]
    have h1 := mul_rpow_three_halves_le (abs_nonneg (X - δ)) (abs_nonneg (Y - δ'))
    have h2 := abs_sub_pow_three_le (X := X) (δ := δ) (c := (N + 1 : ℝ)⁻¹)
      (abs_inv_mul_sign_le _ hM0 _ _)
    have h3 := abs_sub_pow_three_le (X := Y) (δ := δ') (c := (N + 1 : ℝ)⁻¹)
      (abs_inv_mul_sign_le _ hM0 _ _)
    have e8 : 4 / ((N : ℝ) + 1) ^ 3 = 4 * ((N + 1 : ℝ)⁻¹ ^ 3) := by
      rw [inv_pow]; ring
    linarith only [h1, h2, h3, e8]
  have h1 := hmono _ _ hpt
  rw [hadd, hadd, hsmul, hsmul, hconst, hmarg hp, hmarg hr] at h1
  linarith only [h1]

end Bounds

section RowThree

variable (N : ℕ) (β h q : ℝ)

/-- An `n`-replica SK average of a nonnegative observable is nonnegative. -/
theorem sk_avg_nonneg (n : ℕ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (Φ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (hΦ : ∀ σ, 0 ≤ Φ σ) : 0 ≤ ν Φ := by
  obtain ⟨-, -, hmono, hconst⟩ := sk_replica_avg_calculus N n β h ν hν
  have := hmono (fun _ => 0) Φ hΦ
  rwa [hconst] at this

/-- **The first absolute moment is dominated by the third one:**
`M⁻¹ ν(|R_{1,2} - q|) ≤ ν(|R_{1,2} - q|³)/3 + (2/3) M^{-3/2}`. -/
theorem sk_inv_mul_abs_le_cube
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    (N + 1 : ℝ)⁻¹ * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) ≤
      ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) / 3 +
        2 * (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 / 3 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N 2 β h ν₂ hν₂
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hm2 : (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 2 = (N + 1 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hM0.le]
  have hpt : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      (N + 1 : ℝ)⁻¹ * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ≤
      (1 / 3) * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3 +
        2 * (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3 / 3 := fun σ => by
    have := mul_sq_le_cube_third (abs_nonneg ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ))
      ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) (inv_nonneg.2 (Real.sqrt_nonneg ((N : ℝ) + 1)))
    rw [hm2] at this
    linarith only [this]
  have h1 := hmono _ _ hpt
  have hs := hsmul (1 / 3) (fun σ : Fin 2 → Fin (N + 1) → ℤˣ =>
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3)
  rw [hadd, hsmul, hconst, hs] at h1
  linarith only [h1]

/-- **One row of the covariance system with the cubic remainder** (Talagrand, Lemma 1.9.4: the
computations of Section 1.8 "modulo an error term as in (1.277)").  For any `β`, with no
high-temperature condition and no assumption on the moments of `R_{1,2} - q`: for `x = 0`, `y = 1`
and `a ≠ c` among `4` replicas, `ν((R₀₁ - q)(R_{ac} - q))` differs from `M⁻¹ b(c) +
∑_j w_j b(c_j) ν₆((R_{ac} - q)(R_j - q))` by at most `K(β) (ν(|R_{1,2} - q|³) + M^{-3/2})`. -/
theorem sk_cov_row_bound_three (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1)
    (e : Option (Option (Fin 4)) ≃ Fin (4 + 2))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₆ : ((Fin (4 + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₆ : ∀ Φ, ν₆ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (4 + 2) → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {a c : Fin 4} (hac : a ≠ c) (E : ℝ)
    (hE : E = (2304 * β ^ 4 * Real.exp (256 * β ^ 2) * 32 +
        32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) * 4 + 3) +
        64 * β ^ 2 * Real.exp (144 * β ^ 2)) *
      (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) +
        (Real.sqrt ((N : ℝ) + 1))⁻¹ ^ 3)) :
    |ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ c i : ℝ)) - q)) -
      (N + 1 : ℝ)⁻¹ * skCavityBUnscaled q qhat (skCavityCoincidences (0 : Fin 4) 1 a c) -
      ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
          ν₆ (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some c))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)))| ≤ E := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hM1 : (1 : ℝ) ≤ N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hs1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by rw [Real.one_le_sqrt]; exact hM1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (Real.sqrt ((N : ℝ) + 1))⁻¹ := ⟨_, rfl⟩
  rw [← hm] at hE
  have hm0 : 0 ≤ m := by rw [hm]; exact inv_nonneg.2 (Real.sqrt_nonneg _)
  have hm1 : m ≤ 1 := by rw [hm]; exact inv_le_one_of_one_le₀ hs1
  have hm2 : m ^ 2 = (N + 1 : ℝ)⁻¹ := by rw [hm, inv_pow, Real.sq_sqrt hM0.le]
  have hm3 : (N + 1 : ℝ)⁻¹ ^ 3 ≤ m ^ 3 := by
    rw [← hm2, ← pow_mul]
    exact pow_le_pow_of_le_one hm0 hm1 (by norm_num)
  have hm4 : 1 / ((N : ℝ) + 1) ^ 2 ≤ m ^ 3 := by
    have : 1 / ((N : ℝ) + 1) ^ 2 = m ^ 4 := by
      rw [show m ^ 4 = (m ^ 2) ^ 2 by ring, hm2, inv_pow, one_div]
    rw [this]
    exact pow_le_pow_of_le_one hm0 hm1 (by norm_num)
  have hm33 : (32 : ℝ) / ((N : ℝ) + 1) ^ 3 ≤ 32 * m ^ 3 := by
    have : (32 : ℝ) / ((N : ℝ) + 1) ^ 3 = 32 * ((N + 1 : ℝ)⁻¹ ^ 3) := by rw [inv_pow]; ring
    rw [this]
    linarith only [hm3]
  have hm34 : (4 : ℝ) / ((N : ℝ) + 1) ^ 3 ≤ 4 * m ^ 3 := by
    have : (4 : ℝ) / ((N : ℝ) + 1) ^ 3 = 4 * ((N + 1 : ℝ)⁻¹ ^ 3) := by rw [inv_pow]; ring
    rw [this]
    linarith only [hm3]
  set Δ : ℝ := ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := sk_avg_nonneg N β h 2 ν₂ hν₂ _ fun σ => by positivity
  have hDthree : Δ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := hν₂ _
  have hP : Δ ≤ Δ + m ^ 3 := le_add_of_nonneg_right (pow_nonneg hm0 3)
  have hP0 : 0 ≤ Δ + m ^ 3 := add_nonneg hΔ0 (pow_nonneg hm0 3)
  set Dabs : ℝ := ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) with hDabsdef
  have hDabs0 : 0 ≤ Dabs := sk_avg_nonneg N β h 2 ν₂ hν₂ _ fun σ => abs_nonneg _
  have hDab3 : (N + 1 : ℝ)⁻¹ * Dabs ≤ Δ / 3 + 2 * m ^ 3 / 3 := by
    have := sk_inv_mul_abs_le_cube N β h q ν₂ hν₂
    rwa [← hm] at this
  have hDabP : (N + 1 : ℝ)⁻¹ * Dabs ≤ Δ + m ^ 3 := by
    linarith only [hDab3, hΔ0, pow_nonneg hm0 3]
  let Fab : (Fin 4 → Fin N → ℤˣ) → ℝ := fun ρ => (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin N => (ρ a i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ c i : ℝ)) - q
  have hFv := sk_row_Vf_three N β h q 4 ν₄ hν₄ ν₂ hν₂ hq (x := 0) (y := 1) hac
  have hFnn := sk_avg_nonneg N β h 4 ν₄ hν₄
    (fun σ => |Fab (fun r i => σ r i.castSucc) *
      (((σ 0 (Fin.last N) : ℤˣ) : ℝ) * ((σ 1 (Fin.last N) : ℤˣ) : ℝ) - q)| ^ 3)
    (fun σ => by positivity)
  have hF32 : ν₄ (fun σ => |Fab (fun r i => σ r i.castSucc) *
      (((σ 0 (Fin.last N) : ℤˣ) : ℝ) * ((σ 1 (Fin.last N) : ℤˣ) : ℝ) - q)| ^ 3) ≤
      32 * (Δ + m ^ 3) := by
    refine hFv.trans ?_
    linarith only [hm33]
  have hET := rpow_mul_rpow_le_of_le (s := 1 / 3) (t := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num) hFnn hF32 hΔ0 hP (by norm_num : (1 : ℝ) ≤ 32)
  have hT := sk_pair_taylor_three N 4 β q h hfix qhat hqhat (x := 0) (y := 1) (by decide) Fab
    ν₄ hν₄ Δ hDthree
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hET (by positivity))
  have hso : ∀ r r' : Fin 4, r ≠ r' → e (some (some r)) ≠ e (some (some r')) :=
    fun r r' hr he' => hr (Option.some.inj (Option.some.inj (e.injective he')))
  have hH : ∀ j : SKCavityReplicaPair 4, |ν₆ (fun σ => (((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (σ (e (some (some a))) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (some (some c))) i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (e (skCavityReplicaPairMap j).1) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (skCavityReplicaPairMap j).2) i.castSucc : ℝ)) - q))) -
        ∫ g', ∫ ρ' : Fin (4 + 2) → Fin N → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ' (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin N => (ρ' (e (some (some c))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)| ≤
      2 * (((4 + 2 : ℕ) : ℝ)) ^ 2 * β ^ 2 * Real.exp (4 * (((4 + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
        (4 * (Δ + m ^ 3)) := fun j => by
    let G6 : (Fin (4 + 2) → Fin N → ℤˣ) → ℝ := fun ρ' =>
      Fab (fun r => ρ' (e (some (some r)))) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)
    have H := sk_old_spin_compare_three N (4 + 2) β q h hfix G6 ν₆ hν₆ Δ hDthree
    have hG := sk_row_Gb_three N β h q (4 + 2) ν₆ hν₆ ν₂ hν₂ (hso a c hac)
      (fun he' => skCavityReplicaPair_ne j (e.injective he'))
    have hGnn := sk_avg_nonneg N β h (4 + 2) ν₆ hν₆
      (fun σ => |G6 (fun r i => σ r i.castSucc)| ^ (3 / 2 : ℝ)) (fun σ => by positivity)
    have hG4 : ν₆ (fun σ => |G6 (fun r i => σ r i.castSucc)| ^ (3 / 2 : ℝ)) ≤
        4 * (Δ + m ^ 3) := hG.trans (by linarith only [hm34])
    have hEH := rpow_mul_rpow_le_of_le (s := 2 / 3) (t := 1 / 3) (by norm_num) (by norm_num)
      (by norm_num) hGnn hG4 hΔ0 hP (by norm_num : (1 : ℝ) ≤ 4)
    exact H.trans (mul_le_mul_of_nonneg_left hEH (by positivity))
  have key := sk_row_equation_of_bounds N 4 β q h hfix qhat hqhat hqhat01 (x := 0) (y := 1)
    (a := a) (b := c) (by decide) hac e ν₄ hν₄ ν₆ hν₆ ν₂ hν₂ _ _ Dabs hT' hH rfl
  refine key.trans ?_
  have hsum32 : ∑ j : SKCavityReplicaPair 4, |skCavityReplicaPairWeight 4 j| = 32 := by
    have hc : Fintype.card (FinPairs 4) = 6 := by
      unfold FinPairs; decide
    simp [Fintype.sum_sum_type, skCavityReplicaPairWeight, hc]
    norm_num
  rw [hsum32]
  have hX : 2 * Dabs / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) ^ 2 ≤ 3 * (Δ + m ^ 3) := by
    have e2 : 2 * Dabs / ((N : ℝ) + 1) = 2 * ((N + 1 : ℝ)⁻¹ * Dabs) := by
      rw [div_eq_mul_inv]; ring
    linarith only [e2, hDabP, hm4, hΔ0]
  have hL : (N + 1 : ℝ)⁻¹ * (4 * ((4 : ℕ) : ℝ) ^ 2 * β ^ 2 *
      Real.exp (4 * (((4 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) * Dabs) ≤
      4 * ((4 : ℕ) : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * (((4 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
        (Δ + m ^ 3) := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hDabP (by positivity)
  have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  have e6 : ((4 + 2 : ℕ) : ℝ) = 6 := by norm_num
  simp only [e4, e6] at hL ⊢
  rw [hE]
  have h1 : 32 * β ^ 2 * (2 * 6 ^ 2 * β ^ 2 * Real.exp (4 * (6 + 2) ^ 2 * β ^ 2) *
      (4 * (Δ + m ^ 3)) + (2 * Dabs / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) ^ 2)) ≤
      32 * β ^ 2 * (2 * 6 ^ 2 * β ^ 2 * Real.exp (4 * (6 + 2) ^ 2 * β ^ 2) *
      (4 * (Δ + m ^ 3)) + 3 * (Δ + m ^ 3)) := by
    gcongr
  norm_num at hL h1 ⊢
  linarith only [h1, hL]

end RowThree

end SpinGlasses
