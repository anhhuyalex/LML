/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalStep
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTTermI
public import LeanMachineLearning.SpinGlasses.SKCavityCovariance

/-!
# Term I for the global factors (Talagrand, Eq. (1.326))

The sum of the corrections `(N+1)⁻¹ ∑_u ν(ξ e_u ∏_{w ≠ p,u} U_w⁻)` of the last-site expansion of
`SKOverlapCLTGlobalStep.lean` equals `(k-1)/(N+1) (q̂ - q²) ν(T^{k-2})` up to `O(k+1)`. Each term
contracts the last-site factor `(ε^x ε^y - q) ε^{a_u} ε^{b_u}`, a product over four distinct
replicas, to the decoupled value `q̂ - q²`; the truncated products are then replaced by the full
ones, whose average is `𝔼 T^{k-2}` by the exact integration of the replicas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **A single term of the sum in Eq. (1.326).** -/
theorem sk_global_termI_term_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (e : V ⊕ V ≃ Fin n) (p : V) (u : {u // u ≠ p}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let νF : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    |νF (fun σ => (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
          (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
            ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))) -
      (qh - q ^ 2) * νF (fun σ => ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
          (σ (e (.inl w.1)) v : ℝ) * (σ (e (.inr w.1)) v : ℝ) - q))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2) := by
  classical
  let κ := {u : V // u ≠ p}
  have hpu : u.1 ≠ p := u.2
  have hxy : e (.inl p) ≠ e (.inr p) := e.injective.ne (by simp)
  have hab : e (.inl u.1) ≠ e (.inr u.1) := e.injective.ne (by simp)
  have hcard : (Finset.univ.erase u).card = Fintype.card V - 2 := by
    have h0 : 2 ≤ Fintype.card V := by
      have : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u.1, p, hpu⟩
      omega
    have : Fintype.card κ = Fintype.card V - 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, this]
    omega
  obtain ⟨C₀, hC₀0, hC₀⟩ := sk_cavity_prod_contraction_compare β₀ hβ₀ (R := Fin n) (κ := κ)
    (ι := fun _ => Unit) (Finset.univ.erase u) (fun _ _ => (1 : ℝ))
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_overlap_prod_sub_truncated_le β₀ hβ₀ (κ := {w // w ∈
      (Finset.univ.erase u : Finset κ)}) (ι := fun _ => Unit) (fun _ _ => (1 : ℝ)) 1
  refine ⟨C₀ + 2 * C₁, by positivity, fun β h q hfix hb N => ?_⟩
  intro Esk νF qh
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hqhat : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 4 ∂gaussianReal 0 1 = qh := by
    apply integral_congr_ae (ae_of_all _ fun t => ?_)
    congr 2
    ring
  obtain ⟨hdq, -, -, -⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
  have hcoef : |qh - q ^ 2| ≤ 2 := by
    have h1 : |q - qh| ≤ 1 := abs_sub_integral_tanh_fourth_le_one_of_fixedPoint hfix
    have h2 : |q - q ^ 2| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [hq.1, hq.2]
    calc |qh - q ^ 2| = |-(q - qh) + (q - q ^ 2)| := by ring_nf
      _ ≤ |q - qh| + |q - q ^ 2| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
      _ ≤ 2 := by linarith
  let A : κ → Unit → Fin n := fun j _ => e (.inl j.1)
  let B : κ → Unit → Fin n := fun j _ => e (.inr j.1)
  have hAB : ∀ j ∈ (Finset.univ.erase u : Finset κ), ∀ i, A j i ≠ B j i := fun j _ i =>
    e.injective.ne (by simp)
  let Wl : (Fin n → ℤˣ) → ℝ := fun ε =>
    (((ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ)) - q) *
      ((ε (e (.inl u.1)) : ℝ) * (ε (e (.inr u.1)) : ℝ))
  have hWl : ∀ ε, |Wl ε| ≤ 16 := fun ε => by
    dsimp only [Wl]
    rw [abs_mul]
    have h1 : |(ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_units_cast_le_one _) (abs_units_cast_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    have h2 : |(ε (e (.inl u.1)) : ℝ) * (ε (e (.inr u.1)) : ℝ)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_units_cast_le_one _) (abs_units_cast_le_one _) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    have h3 : |(ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ) - q| ≤ 2 := by
      have h4 : |q| ≤ 1 := by rw [abs_of_nonneg hq.1]; exact hq.2
      linarith [abs_sub ((ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ)) q]
    nlinarith [abs_nonneg ((ε (e (.inl p)) : ℝ) * (ε (e (.inr p)) : ℝ) - q),
      abs_nonneg ((ε (e (.inl u.1)) : ℝ) * (ε (e (.inr u.1)) : ℝ))]
  have key := hC₀ β h q hfix hb N A B hAB Wl hWl (qh - q ^ 2) hcoef
  have hexact := sk_cavity_decoupled_endpoint_pair_cov_combo N β q h hfix qh hqhat
    (R := Fin n) (ι := Unit) (fun _ => (1 : ℝ)) (x := fun _ => e (.inl p))
    (y := fun _ => e (.inr p)) (fun _ => hxy) (a := e (.inl u.1)) (b := e (.inr u.1)) hab
    (fun ρ => ∏ j ∈ (Finset.univ.erase u : Finset κ), ∑ i : Unit, (1 : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (A j i) v : ℝ)) ⬝ᵥ
        fun v : Fin N => (ρ (B j i) v : ℝ)) - q))
  have hco : skCavityCoincidences (e (.inl p)) (e (.inr p)) (e (.inl u.1)) (e (.inr u.1)) = 0 := by
    have h1 : e (.inl p) ≠ e (.inl u.1) := e.injective.ne (by simpa using hpu.symm)
    have h2 : e (.inl p) ≠ e (.inr u.1) := e.injective.ne (by simp)
    have h3 : e (.inr p) ≠ e (.inl u.1) := e.injective.ne (by simp)
    have h4 : e (.inr p) ≠ e (.inr u.1) := e.injective.ne (by simpa using hpu.symm)
    simp [skCavityCoincidences, h1, h2, h3, h4]
  have hbu : skCavityBUnscaled q qh 0 = qh - q ^ 2 := by simp [skCavityBUnscaled]
  rw [hco, hbu] at hexact
  have key' := key (by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using hexact)
  -- replace the truncated product by the full product
  let κ' := {w // w ∈ (Finset.univ.erase u : Finset κ)}
  let a : κ' → Unit → Fin n := fun w _ => e (.inl w.1.1)
  let b : κ' → Unit → Fin n := fun w _ => e (.inr w.1.1)
  have hab' : ∀ j i, a j i ≠ b j i := fun j i => e.injective.ne (by simp)
  let Uf : κ' → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun w σ => ∑ i : Unit, (1 : ℝ) *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin (N + 1) => (σ (a w i) v : ℝ)) ⬝ᵥ
      fun v : Fin (N + 1) => (σ (b w i) v : ℝ)) - q)
  let Um : κ' → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun w σ => ∑ i : Unit, (1 : ℝ) *
    ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (σ (a w i) v.castSucc : ℝ)) ⬝ᵥ
      fun v : Fin N => (σ (b w i) v.castSucc : ℝ)) - q)
  have hcmp := hC₁ β h q hfix hb N n a b hab' νF (fun _ => rfl) Uf Um
    (fun w σ => ∑ i : Unit, (1 : ℝ) * ((σ (a w i) (Fin.last N) : ℝ) * (σ (b w i) (Fin.last N) : ℝ)))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => 1) (fun _ => by norm_num)
  obtain ⟨hadd, hsmul, hmono, -⟩ := sk_replica_avg_calculus N n β h νF (fun _ => rfl)
  let Λ : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ := ⟨⟨νF, hadd⟩, hsmul⟩
  have hcard' : Fintype.card κ' = Fintype.card V - 2 := by
    rw [Fintype.card_coe, hcard]
  rw [hcard'] at hcmp
  have hfull : ∀ σ : Fin n → Fin (N + 1) → ℤˣ, ∏ w : κ', Uf w σ =
      ∏ w ∈ (Finset.univ.erase u : Finset κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (σ (e (.inl w.1)) v : ℝ) * (σ (e (.inr w.1)) v : ℝ) - q) := fun σ => by
    simp only [Uf, a, b, Finset.univ_unique, Finset.sum_singleton, one_mul, dotProduct]
    convert Finset.prod_coe_sort (Finset.univ.erase u : Finset κ) (fun w : κ => ((N + 1 : ℝ)⁻¹ *
      ∑ v : Fin (N + 1), (σ (e (.inl w.1)) v : ℝ) * (σ (e (.inr w.1)) v : ℝ) - q))
  have htr : ∀ σ : Fin n → Fin (N + 1) → ℤˣ, ∏ w : κ', Um w σ =
      ∏ w ∈ (Finset.univ.erase u : Finset κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q) := fun σ => by
    simp only [Um, a, b, Finset.univ_unique, Finset.sum_singleton, one_mul, dotProduct]
    convert Finset.prod_coe_sort (Finset.univ.erase u : Finset κ) (fun w : κ => ((N + 1 : ℝ)⁻¹ *
      ∑ v : Fin N, (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))
  have hdiff : |νF (fun σ => ∏ w : κ', Uf w σ) - νF (fun σ => ∏ w : κ', Um w σ)| ≤
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2) := by
    change |Λ (fun σ => ∏ w : κ', Uf w σ) - Λ (fun σ => ∏ w : κ', Um w σ)| ≤ _
    rw [← map_sub]
    refine (Λ.abs_apply_le_apply_abs hmono _).trans ?_
    simpa only [one_mul, Pi.sub_apply, Λ, LinearMap.coe_mk, AddHom.coe_mk] using hcmp
  simp only [hfull, htr] at hdiff
  rw [hcard] at key'
  have hpt : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
          (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
            ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q)) =
      (∏ w ∈ (Finset.univ.erase u : Finset κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q)) *
        Wl (fun r => σ r (Fin.last N)) := fun σ => by
    simp only [Wl]
    ring
  simp only [hpt]
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, dotProduct, A, B] at key'
  replace key' : |νF (fun σ => (∏ w ∈ (Finset.univ.erase u : Finset κ), ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin N, (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))
        * Wl (fun r => σ r (Fin.last N))) -
      (qh - q ^ 2) * νF (fun σ => ∏ w ∈ (Finset.univ.erase u : Finset κ),
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (.inl w.1)) v.castSucc : ℝ) *
          (σ (e (.inr w.1)) v.castSucc : ℝ) - q))| ≤
      C₀ / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2) := key'
  generalize νF (fun σ => (∏ w ∈ (Finset.univ.erase u : Finset κ), ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
        (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q)) *
        Wl (fun r => σ r (Fin.last N))) = X at key' ⊢
  generalize νF (fun σ => ∏ w ∈ (Finset.univ.erase u : Finset κ),
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N, (σ (e (.inl w.1)) v.castSucc : ℝ) *
          (σ (e (.inr w.1)) v.castSucc : ℝ) - q)) = Y at key' hdiff ⊢
  generalize νF (fun σ => ∏ w ∈ (Finset.univ.erase u : Finset κ),
        ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), (σ (e (.inl w.1)) v : ℝ) *
          (σ (e (.inr w.1)) v : ℝ) - q)) = Z at hdiff ⊢
  calc |X - (qh - q ^ 2) * Z|
      = |(X - (qh - q ^ 2) * Y) + (qh - q ^ 2) * (Y - Z)| := by ring_nf
    _ ≤ |X - (qh - q ^ 2) * Y| + |qh - q ^ 2| * |Y - Z| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
    _ ≤ C₀ / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2) +
        2 * (C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2)) := by
      refine add_le_add key' (mul_le_mul hcoef ?_ (abs_nonneg _) (by norm_num))
      rw [abs_sub_comm]
      exact hdiff
    _ = (C₀ + 2 * C₁) / ((N : ℝ) + 1) ^ (((Fintype.card V - 2 + 1 : ℕ) : ℝ) / 2) := by ring

/-- **The average of a product of block overlaps is a power of `T`.** -/
theorem sk_global_blocks_moment {ι : Type*} {n : ℕ} (ca da : ι → Fin n)
    (hinj : Function.Injective (Sum.elim ca da : ι ⊕ ι → Fin n)) (W : Finset ι)
    (N : ℕ) (β h q : ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    (∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, ∏ w ∈ W, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (σ (ca w) v : ℝ) * (σ (da w) v : ℝ) - q)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ W.card ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  classical
  intro Esk bmean Tg
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have := integral_pi_prod_overlap_blocks (Measure.count.tilted (Esk g))
    (fun σ i => (σ i : ℝ)) (bmean g) (fun i => rfl) ((N + 1 : ℝ)⁻¹) q
    (fun ρ a a' => ((N + 1 : ℝ)⁻¹ * ∑ i, (ρ a i : ℝ) * (ρ a' i : ℝ)) - q) (fun _ _ _ => rfl)
    (Tg g) rfl ca da hinj W (fun _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simpa using this

/-- **Term I of Eq. (1.325) (Eq. (1.326)).** -/
theorem sk_global_termI_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (e : V ⊕ V ≃ Fin n) (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let νF : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    |(N + 1 : ℝ)⁻¹ * ∑ u : {u // u ≠ p}, νF (fun σ =>
          (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
            (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
              ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
                (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))) -
      (((Fintype.card V - 1 : ℕ) : ℝ) * (qh - q ^ 2) / (N + 1 : ℝ)) *
        ∫ g, Tg g ^ (Fintype.card V - 2) ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)|
      ≤ C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  classical
  by_cases hV : Fintype.card V ≤ 1
  · refine ⟨1, one_pos, fun β h q hfix hb N => ?_⟩
    intro Esk νF bmean Tg qh
    have : IsEmpty {u : V // u ≠ p} := by
      refine ⟨fun u => ?_⟩
      have : 1 < Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u.1, p, u.2⟩
      omega
    have h0 : Fintype.card V - 1 = 0 := by omega
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, h0, Nat.cast_zero, zero_mul,
      zero_div, sub_zero, abs_zero]
    positivity
  push Not at hV
  choose C hC0 hC using fun u : {u // u ≠ p} => sk_global_termI_term_uniform β₀ hβ₀ e p u
  refine ⟨(∑ u, C u) + 1, by
    linarith only [Finset.sum_nonneg (fun u (_ : u ∈ Finset.univ) => (hC0 u).le)], ?_⟩
  intro β h q hfix hb N Esk νF bmean Tg qh
  have hcard : ∀ u : {u // u ≠ p}, ((Finset.univ.erase u : Finset {u // u ≠ p})).card =
      Fintype.card V - 2 := fun u => by
    have : Fintype.card {u : V // u ≠ p} = Fintype.card V - 1 := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
        Finset.card_univ]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, this]
    omega
  have hinjκ : Function.Injective (Sum.elim (fun w : {u // u ≠ p} => e (.inl w.1))
      (fun w : {u // u ≠ p} => e (.inr w.1)) : {u // u ≠ p} ⊕ {u // u ≠ p} → Fin n) := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
    · have := e.injective hab
      simp only [Sum.inl.injEq] at this
      exact congrArg Sum.inl (Subtype.ext this)
    · exact absurd (e.injective hab) (by simp)
    · exact absurd (e.injective hab) (by simp)
    · have := e.injective hab
      simp only [Sum.inr.injEq] at this
      exact congrArg Sum.inr (Subtype.ext this)
  have ht : ∀ u : {u // u ≠ p}, |νF (fun σ =>
          (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
            (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
              ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
                (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))) -
      (qh - q ^ 2) * ∫ g, Tg g ^ (Fintype.card V - 2)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C u / ((N : ℝ) + 1) ^ ((((Fintype.card V - 2) + 1 : ℕ) : ℝ) / 2) := fun u => by
    have h1 := hC u β h q hfix hb N
    have h2 := sk_global_blocks_moment (fun w : {u // u ≠ p} => e (.inl w.1))
      (fun w : {u // u ≠ p} => e (.inr w.1)) hinjκ (Finset.univ.erase u) N β h q
    rw [hcard u] at h2
    have h3 : νF (fun σ => ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (σ (e (.inl w.1)) v : ℝ) * (σ (e (.inr w.1)) v : ℝ) - q)) =
        ∫ g, Tg g ^ (Fintype.card V - 2) ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
        := h2
    have h1' : |νF (fun σ =>
          (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
            (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
              ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
                (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))) -
      (qh - q ^ 2) * νF (fun σ => ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ *
        ∑ v : Fin (N + 1), (σ (e (.inl w.1)) v : ℝ) * (σ (e (.inr w.1)) v : ℝ) - q))| ≤
      C u / ((N : ℝ) + 1) ^ ((((Fintype.card V - 2) + 1 : ℕ) : ℝ) / 2) := h1
    rw [h3] at h1'
    exact h1'
  have hsum := abs_inv_succ_mul_sum_sub_le (fun u : {u // u ≠ p} => νF (fun σ =>
          (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
            (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
              ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
                (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q))))
    (fun _ => (qh - q ^ 2) * ∫ g, Tg g ^ (Fintype.card V - 2)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) C (Fintype.card V - 2) N ht
  have hcards : Fintype.card {u : V // u ≠ p} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ p),
      Finset.card_univ]
  have hexp : Fintype.card V - 2 + 3 = Fintype.card V + 1 := by omega
  rw [hexp] at hsum
  have hsum2 : (N + 1 : ℝ)⁻¹ * ∑ _u : {u // u ≠ p}, ((qh - q ^ 2) * ∫ g, Tg g ^ (Fintype.card V - 2)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (((Fintype.card V - 1 : ℕ) : ℝ) * (qh - q ^ 2) / (N + 1 : ℝ)) *
        ∫ g, Tg g ^ (Fintype.card V - 2)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [Finset.sum_const, Finset.card_univ, hcards, nsmul_eq_mul]
    field_simp
  rw [hsum2] at hsum
  refine hsum.trans ?_
  refine div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
