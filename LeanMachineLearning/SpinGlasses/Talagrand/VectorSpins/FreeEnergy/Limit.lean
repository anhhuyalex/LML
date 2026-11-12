/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.PressureBound
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.DerivativeBound

/-!
# Theorem 1.12.3: the free energy of the vector SK model

For small `β` the free energies `p_N(β)` of the vector spin SK model converge to the
replica-symmetric pressure `G(β, (q, ρ))` evaluated at the unique solution of (1.372)--(1.373),
at the rate `O(N^{-1/2})`.

The proof follows the book: both `p_{N+1}` and `b ↦ G(b, z(b))` vanish at `b = 0`, and their
derivatives in `b` differ by at most `K b`, so `|p_{N+1}(β) - G(β, z(β))| ≤ K β²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology Set
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- **A mean value estimate near `0`.**  If `Δ = p - F` has derivative bounded by `K b` at each
`b ∈ (0, β₁)` and `p, F → 0` as `b → 0⁺`, then `|Δ(β)| ≤ K β²` for `0 < β < β₁`. -/
theorem abs_sub_le_of_deriv_bound {p F : ℝ → ℝ} {β β₁ K : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hββ₁ : β < β₁)
    (hΔ : ∀ b ∈ Ioo 0 β₁, ∃ W, HasDerivAt (fun b => p b - F b) W b ∧ |W| ≤ K * b)
    (hp : Tendsto p (𝓝[>] 0) (𝓝 0)) (hF : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    |p β - F β| ≤ K * β ^ 2 := by
  set Δ : ℝ → ℝ := fun b => p b - F b with hΔdef
  have hd : ∀ b ∈ Ioo 0 β₁, HasDerivAt Δ (deriv Δ b) b ∧ |deriv Δ b| ≤ K * b := fun b hb => by
    obtain ⟨W, hW, hWb⟩ := hΔ b hb
    rw [hW.deriv]
    exact ⟨hW, hWb⟩
  have hlim : Tendsto Δ (𝓝[>] 0) (𝓝 0) := by
    simpa using hp.sub hF
  have hev : ∀ᶠ b₀ in 𝓝[>] (0 : ℝ), b₀ ∈ Ioo 0 β := Ioo_mem_nhdsGT hβ
  have hbound : ∀ b₀ ∈ Ioo 0 β, |Δ β| ≤ K * β ^ 2 + |Δ b₀| := fun b₀ hb₀ => by
    have hsub : Icc b₀ β ⊆ Ioo 0 β₁ := fun x hx => ⟨hb₀.1.trans_le hx.1, hx.2.trans_lt hββ₁⟩
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Δ) (f' := deriv Δ)
      (s := Icc b₀ β) (C := K * β)
      (fun x hx => (hd x (hsub hx)).1.hasDerivWithinAt)
      (fun x hx => (hd x (hsub hx)).2.trans (mul_le_mul_of_nonneg_left hx.2 hK))
      (convex_Icc b₀ β) (left_mem_Icc.2 hb₀.2.le) (right_mem_Icc.2 hb₀.2.le)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have h1 : |β - b₀| ≤ β := by
      rw [abs_of_nonneg (by linarith [hb₀.2])]; linarith [hb₀.1]
    have h2 : |Δ β| ≤ |Δ β - Δ b₀| + |Δ b₀| := by
      simpa using abs_add_le (Δ β - Δ b₀) (Δ b₀)
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ K * β)]
  have hlimit : Tendsto (fun b₀ => K * β ^ 2 + |Δ b₀|) (𝓝[>] 0) (𝓝 (K * β ^ 2 + |0|)) :=
    tendsto_const_nhds.add hlim.abs
  rw [abs_zero, add_zero] at hlimit
  exact ge_of_tendsto hlimit (hev.mono fun b₀ hb₀ => hbound b₀ hb₀)

/-- The free energy vanishes at infinite temperature: `p_N(0) = 0`. -/
theorem skVectorFreeEnergy_zero {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (N : ℕ) : skVectorFreeEnergy μ ξ N 0 = 0 := by
  unfold skVectorFreeEnergy
  simp [skVectorEnergy]

/-- The replica-symmetric pressure along the branch of fixed points is small near `0`. -/
theorem tendsto_skVectorPressure_fixedPoint_zero {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β₁ : ℝ} (hβ₁ : 0 < β₁)
    (z : ℝ → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hz : ∀ b ∈ Ioo 0 β₁, z b ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ ξ b (z b) = z
      b) :
    Tendsto (fun b => skVectorPressure μ ξ b (z b)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun b : ℝ => b ^ 2 * (d : ℝ) ^ 2 / 2 + |b| * (d : ℝ) ^ 2 +
      b ^ 2 * (d : ℝ) ^ 3 := by fun_prop
  have h0 : Tendsto (fun b : ℝ => b ^ 2 * (d : ℝ) ^ 2 / 2 + |b| * (d : ℝ) ^ 2 +
      b ^ 2 * (d : ℝ) ^ 3) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [Ioo_mem_nhdsGT hβ₁] with b hb
  obtain ⟨hcone, hfix⟩ := hz b hb
  obtain ⟨h1, h2⟩ := skVectorFixedPoint_sum_sq_le μ ξ hξ hbound b hcone hfix
  rw [Real.norm_eq_abs]
  exact abs_skVectorPressure_le μ ξ hξ hbound b hcone.1 h1 h2

/-- **Theorem 1.12.3 (quantitative form).**  Let `0 < β < β₁` with `18 β₁² d² < 1` and
`β₁² d² ≤ 1/200`, and let `(q, ρ)` be the fixed point of `T` at `β`.  For every `s > 0` the free
energy `p_{N+1}(β)` of the vector SK model with `N + 1` sites satisfies
`|p_{N+1}(β) - G(β, (q, ρ))| ≤ β² (ε + d ε/s + 2 d s)/2 + β² d²/(2(N+1))`,
where `ε = (8 d⁴ + 2 d²)/(N+1)`. -/
theorem abs_skVectorFreeEnergy_sub_pressure_le_of_pos {d : ℕ} (μ : Measure α)
  [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (hκ : 18 * β₁ ^ 2 * (d : ℝ) ^ 2 < 1) (hβ₁ : β₁ ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200) (N : ℕ)
    {s : ℝ} (hs : 0 < s) {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) :
    |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
      β ^ 2 * (((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) +
        d * ((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1)) / s + 2 * d * s) / 2 +
        (d : ℝ) ^ 2 / (2 * ((N : ℝ) + 1))) := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hβ₁0 : 0 < β₁ := hβ.trans hββ₁
  have hsmall : ∀ b ∈ Ioo 0 β₁, 18 * b ^ 2 * (d : ℝ) ^ 2 < 1 := fun b hb => by
    have : b ^ 2 ≤ β₁ ^ 2 := by nlinarith [hb.1, hb.2]
    nlinarith [pow_nonneg hr 4]
  let z : ℝ → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) := fun b =>
    if h : 18 * b ^ 2 * (d : ℝ) ^ 2 < 1 then
      Classical.choose (exists_skVectorFixedPoint μ ξ hξ hbound b h) else 0
  have hz : ∀ b ∈ Ioo 0 β₁, z b ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ ξ b (z b) = z
    b :=
    fun b hb => by
      have hzb : z b = Classical.choose (exists_skVectorFixedPoint μ ξ hξ hbound b (hsmall b hb)) :=
        by simp [z, hsmall b hb]
      rw [hzb]
      exact Classical.choose_spec (exists_skVectorFixedPoint μ ξ hξ hbound b (hsmall b hb))
  set K : ℝ := ((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1) +
        d * ((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) / ((N : ℝ) + 1)) / s + 2 * d * s) / 2 +
        (d : ℝ) ^ 2 / (2 * ((N : ℝ) + 1)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hΔ : ∀ b ∈ Ioo 0 β₁, ∃ W, HasDerivAt (fun b => skVectorFreeEnergy μ ξ (N + 1) b -
      skVectorPressure μ ξ b (z b)) W b ∧ |W| ≤ K * b := fun b hb => by
    have hb2 : b ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200 := by
      have : b ^ 2 ≤ β₁ ^ 2 := by nlinarith [hb.1, hb.2]
      nlinarith [sq_nonneg (d : ℝ)]
    obtain ⟨V, hV, hVb⟩ := exists_hasDerivAt_skVectorFreeEnergy_abs_sub_le μ ξ hξ hbound b hb2 N
      (hz b hb).1 (hz b hb).2 hs
    have hF := hasDerivAt_skVectorPressure_fixedPoint μ ξ hξ hbound hb.1 hb.2 hκ z
      (fun b' hb' => hz b' ⟨(half_pos hb.1).trans hb'.1, hb'.2⟩)
    refine ⟨_, hV.sub hF, ?_⟩
    rw [abs_of_pos hb.1] at hVb
    refine hVb.trans (le_of_eq ?_)
    rw [hK]; ring
  have hp : Tendsto (skVectorFreeEnergy μ ξ (N + 1)) (𝓝[>] 0) (𝓝 0) := by
    have := (hasDerivAt_skVectorFreeEnergy μ ξ hξ hbound N 0).continuousAt.tendsto
    rw [skVectorFreeEnergy_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have key := abs_sub_le_of_deriv_bound hK0 hβ hββ₁ hΔ hp
    (tendsto_skVectorPressure_fixedPoint_zero μ ξ hξ hbound hβ₁0 z hz)
  have hxz : x = z β := skVectorFixedPoint_unique μ ξ hξ hbound β (hsmall β ⟨hβ, hββ₁⟩) hx
    (hz β ⟨hβ, hββ₁⟩).1 hxf (hz β ⟨hβ, hββ₁⟩).2
  rw [hxz]
  linarith [key, mul_comm K (β ^ 2)]

/-- Choosing `s = 1/r` with `r = √(N+1)` makes the error of the quantitative theorem `O(1/r)`. -/
theorem div_sq_add_div_le_div {c d r : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) :
    (c / (r * r) + d * (c / (r * r)) / (1 / r) + 2 * d * (1 / r)) / 2 + d ^ 2 / (2 * (r * r)) ≤
      ((c + d * c + 2 * d) / 2 + d ^ 2 / 2) / r := by
  have hr0 : 0 < r := by linarith
  have h1 : c / (r * r) ≤ c / r :=
    div_le_div_of_nonneg_left hc hr0 (by nlinarith)
  have h2 : d ^ 2 / (2 * (r * r)) ≤ d ^ 2 / (2 * r) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have h3 : d * (c / (r * r)) / (1 / r) = d * c / r := by field_simp
  have h4 : 2 * d * (1 / r) = 2 * d / r := by field_simp
  rw [h3, h4]
  have e : ((c + d * c + 2 * d) / 2 + d ^ 2 / 2) / r =
      (c / r + d * c / r + 2 * d / r) / 2 + d ^ 2 / (2 * r) := by field_simp
  rw [e]
  have h5 : c / (r * r) + d * c / r + 2 * d / r ≤ c / r + d * c / r + 2 * d / r := by linarith
  linarith

/-- **Theorem 1.12.3 with its explicit error constant.** The factor multiplying
`1 / √(N+1)` depends only on `β` and the dimension, not on the spin law. -/
theorem abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_pos {d : ℕ} (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (hκ : 18 * β₁ ^ 2 * (d : ℝ) ^ 2 < 1) (hβ₁ : β₁ ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) (N : ℕ) :
    |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
      β ^ 2 * (((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) +
        d * (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) + 2 * d) / 2 + (d : ℝ) ^ 2 / 2) /
        Real.sqrt ((N : ℝ) + 1) := by
  have hc : (0 : ℝ) ≤ 8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2 := by positivity
  set r : ℝ := Real.sqrt ((N : ℝ) + 1) with hr
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hr1 : 1 ≤ r := by
    rw [hr]; exact Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
  have hrr : r * r = (N : ℝ) + 1 := Real.mul_self_sqrt hN.le
  have h := abs_skVectorFreeEnergy_sub_pressure_le_of_pos μ ξ hξ hbound hβ hββ₁ hκ hβ₁ N
    (s := 1 / r) (by positivity) hx hxf
  rw [← hrr] at h
  exact h.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left (div_sq_add_div_le_div hc hr1)
    (sq_nonneg β))
    (mul_div_assoc _ _ _).symm)

/-- **Theorem 1.12.3 (rate of convergence).**  Under the smallness conditions
`18 β₁² d² < 1`, `β₁² d² ≤ 1/200` and for `0 < β < β₁`, the free energies of the vector SK model
satisfy `|p_{N+1}(β) - G(β, (q, ρ))| ≤ C/√(N+1)`, where `(q, ρ)` is the fixed point of `T`
at `β` and `G` the replica-symmetric pressure. -/
theorem exists_abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt {d : ℕ} (μ : Measure α)
  [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (hκ : 18 * β₁ ^ 2 * (d : ℝ) ^ 2 < 1) (hβ₁ : β₁ ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hxf : skVectorFixedPointMap μ ξ β x = x) :
    ∃ C : ℝ, ∀ N : ℕ, |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
      C / Real.sqrt ((N : ℝ) + 1) := by
  refine ⟨β ^ 2 * (((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) +
    d * (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) + 2 * d) / 2 + (d : ℝ) ^ 2 / 2), ?_⟩
  exact abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_pos μ ξ hξ hbound hβ hββ₁
    hκ hβ₁ hx hxf

/-- **Theorem 1.12.3 (limit).**  Under the same conditions the free energies of the vector SK
model converge to the replica-symmetric pressure at the fixed point of `T`. -/
theorem tendsto_skVectorFreeEnergy {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (hκ : 18 * β₁ ^ 2 * (d : ℝ) ^ 2 < 1) (hβ₁ : β₁ ^ 2 * (d : ℝ) ^ 2 ≤ 1 / 200)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hx : x ∈ skVectorFixedPointCone d)
    (hxf : skVectorFixedPointMap μ ξ β x = x) :
    Tendsto (fun N : ℕ => skVectorFreeEnergy μ ξ N β) atTop (𝓝 (skVectorPressure μ ξ β x)) := by
  obtain ⟨C, hC⟩ := exists_abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt μ ξ hξ hbound hβ hββ₁
    hκ hβ₁ hx hxf
  rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => C / Real.sqrt ((N : ℝ) + 1)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hlim
  rw [Real.dist_eq]; exact hC N

/-- **The book's hypothesis `L β d ≤ 1` with `L = 15` implies our two smallness conditions**
`18 β² d² < 1` (existence, uniqueness and the free energy) and `β² d² ≤ 1/200` (the overlap
estimates of Theorem 1.12.1). -/
theorem smallness_of_high_temperature {β d : ℝ} (hβ : 0 ≤ β) (hd : 0 ≤ d) (h : 15 * β * d ≤ 1) :
    18 * β ^ 2 * d ^ 2 < 1 ∧ β ^ 2 * d ^ 2 ≤ 1 / 200 := by
  have h0 : 0 ≤ β * d := mul_nonneg hβ hd
  have h1 : β * d ≤ 1 / 15 := by linarith
  have h2 : (β * d) ^ 2 ≤ (1 / 15) ^ 2 := pow_le_pow_left₀ h0 h1 2
  constructor <;> nlinarith [h2]

/-- The matrix fixed point is uniquely determined throughout the closed high-temperature range.
The conclusion requires no Gaussian realization or previously chosen solution. -/
theorem existsUnique_skVectorFixedPoint_of_high_temperature {d : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 15 * β * (d : ℝ) ≤ 1) :
    ∃! x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ),
      x ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ ξ β x = x := by
  have hκ := (smallness_of_high_temperature hβ (Nat.cast_nonneg d) hsmall).1
  obtain ⟨x, hx, hxf⟩ := exists_skVectorFixedPoint μ ξ hξ hbound β hκ
  refine ⟨x, ⟨hx, hxf⟩, ?_⟩
  intro y hy
  exact skVectorFixedPoint_unique μ ξ hξ hbound β hκ hy.1 hx hy.2 hxf

/-- **Theorem 1.12.3 in the book's range `L β d ≤ 1` (with `L = 15`)**: the free energies of the
vector SK model satisfy `|p_{N+1}(β) - G(β, (q, ρ))| ≤ C/√(N+1)`, where `(q, ρ)` is the solution
of (1.372)--(1.373) in the cone. -/
theorem exists_abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_high_temperature {d : ℕ} (μ :
  Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (h : 15 * β₁ * (d : ℝ) ≤ 1) {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) :
    ∃ C : ℝ, ∀ N : ℕ, |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
      C / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := smallness_of_high_temperature (hβ.trans hββ₁).le (Nat.cast_nonneg d) h
  exact exists_abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt μ ξ hξ hbound hβ hββ₁ h1 h2 hx hxf

/-- **Theorem 1.12.3 (limit) in the book's range `L β d ≤ 1` (with `L = 15`)**. -/
theorem tendsto_skVectorFreeEnergy_of_high_temperature {d : ℕ} (μ : Measure α)
  [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β β₁ : ℝ} (hβ : 0 < β) (hββ₁ : β < β₁)
    (h : 15 * β₁ * (d : ℝ) ≤ 1) {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) :
    Tendsto (fun N : ℕ => skVectorFreeEnergy μ ξ N β) atTop (𝓝 (skVectorPressure μ ξ β x)) := by
  obtain ⟨h1, h2⟩ := smallness_of_high_temperature (hβ.trans hββ₁).le (Nat.cast_nonneg d) h
  exact tendsto_skVectorFreeEnergy μ ξ hξ hbound hβ hββ₁ h1 h2 hx hxf


/-- The replica-symmetric pressure vanishes at zero inverse temperature for every matrix pair. -/
theorem skVectorPressure_zero {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    skVectorPressure μ ξ 0 x = 0 := by
  simp [skVectorPressure, skVectorGaussianFreeEnergy]

/-- The book's closed temperature range leaves room for the strict numerical hypotheses of
the pressure theorem. The rational choice avoids differentiating or estimating a square root. -/
theorem exists_gt_sq_mul_sq_bounds {β d : ℝ} (hd : 0 ≤ d) (h : 15 * β * d ≤ 1) :
    ∃ b : ℝ, β < b ∧ 18 * b ^ 2 * d ^ 2 < 1 ∧ b ^ 2 * d ^ 2 ≤ 1 / 200 := by
  by_cases hd0 : d = 0
  · subst d
    exact ⟨β + 1, by linarith, by norm_num, by norm_num⟩
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  refine ⟨(7 / 100) / d, (lt_div_iff₀ hdpos).2 ?_, ?_, ?_⟩
  · nlinarith
  · rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hd0]
    norm_num
  · rw [← mul_pow, div_mul_cancel₀ _ hd0]
    norm_num

/-- The explicit pressure error holds throughout the closed high-temperature range, including
zero inverse temperature and dimension zero. No auxiliary upper temperature is supplied. -/
theorem abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_high_temperature {d : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 15 * β * (d : ℝ) ≤ 1)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) (N : ℕ) :
    |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
      β ^ 2 * (((8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) +
        d * (8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2) + 2 * d) / 2 + (d : ℝ) ^ 2 / 2) /
        Real.sqrt ((N : ℝ) + 1) := by
  by_cases hβ0 : β = 0
  · subst β
    simp [skVectorFreeEnergy_zero, skVectorPressure_zero]
  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  obtain ⟨β₁, hββ₁, hκ, hβ₁⟩ := exists_gt_sq_mul_sq_bounds (Nat.cast_nonneg d) hsmall
  exact abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_pos μ ξ hξ hbound hβpos hββ₁
    hκ hβ₁ hx hxf N

/-- The pressure limit under the book's hypothesis, without an auxiliary upper temperature. -/
theorem tendsto_skVectorFreeEnergy_of_nonneg {d : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : 15 * β * (d : ℝ) ≤ 1)
    {x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hx : x ∈ skVectorFixedPointCone d) (hxf : skVectorFixedPointMap μ ξ β x = x) :
    Tendsto (fun N : ℕ => skVectorFreeEnergy μ ξ N β) atTop (𝓝 (skVectorPressure μ ξ β x)) := by
  by_cases hβ0 : β = 0
  · subst β
    simp [skVectorFreeEnergy_zero, skVectorPressure_zero]
  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  obtain ⟨β₁, hββ₁, hκ, hβ₁⟩ := exists_gt_sq_mul_sq_bounds (Nat.cast_nonneg d) hsmall
  exact tendsto_skVectorFreeEnergy μ ξ hξ hbound hβpos hββ₁ hκ hβ₁ hx hxf

/-- **Talagrand Theorems 1.12.1--1.12.3 under the book's hypotheses.** A dimension-only constant
works for every probability spin law and every nonnegative inverse temperature with `15 β d ≤ 1`.
There is one unique fixed point for all system sizes; both overlap errors and the pressure error
are bounded, and the free energies converge to the pressure. No margin or fixed point is input. -/
theorem existsUnique_skVectorFixedPoint_overlap_free_energy (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {S : Type*} [MeasurableSpace S] (μ : Measure S)
      [IsProbabilityMeasure μ] (ξ : S → Fin d → ℝ),
      (∀ u, Measurable (fun a => ξ a u)) → (∀ a, ∑ u, ξ a u ^ 2 ≤ d) →
      ∀ β : ℝ, 0 ≤ β → 15 * β * (d : ℝ) ≤ 1 →
      ∃! x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ),
        x ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ ξ β x = x ∧
        (∀ N : ℕ, skVectorReplicaAverage μ ξ N β (fun σ => ∑ u, ∑ v,
            skVectorOverlapDeviation ξ N 0 1 x.1 u v σ ^ 2) +
          skVectorReplicaAverage μ ξ N β (fun σ => ∑ u, ∑ v,
            skVectorOverlapDeviation ξ N 0 0 x.2 u v σ ^ 2) ≤ K / ((N : ℝ) + 1)) ∧
        (∀ N : ℕ, |skVectorFreeEnergy μ ξ (N + 1) β - skVectorPressure μ ξ β x| ≤
          K / Real.sqrt ((N : ℝ) + 1)) ∧
        Tendsto (fun N : ℕ => skVectorFreeEnergy μ ξ N β) atTop
          (𝓝 (skVectorPressure μ ξ β x)) := by
  let c : ℝ := 8 * (d : ℝ) ^ 4 + 2 * (d : ℝ) ^ 2
  let p : ℝ := (c + d * c + 2 * d) / 2 + (d : ℝ) ^ 2 / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  refine ⟨c + p, add_nonneg hc hp, ?_⟩
  intro S _ μ _ ξ hξ hbound β hβ hsmall
  obtain ⟨hκ, hβ2⟩ := smallness_of_high_temperature hβ (Nat.cast_nonneg d) hsmall
  obtain ⟨x, ⟨hx, hxf⟩, hunique⟩ :=
    existsUnique_skVectorFixedPoint_of_high_temperature μ ξ hξ hbound hβ hsmall
  refine ⟨x, ⟨hx, hxf, ?_, ?_, ?_⟩, ?_⟩
  · intro N
    have h := sum_sq_skVectorOverlapDeviation_average_le μ ξ hξ hbound N β hβ2 hx hxf
    exact h.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hp) (by positivity))
  · intro N
    have h := abs_skVectorFreeEnergy_sub_pressure_le_inv_sqrt_of_high_temperature μ ξ hξ
      hbound hβ hsmall hx hxf N
    have hcoef : β ^ 2 * p ≤ c + p := by
      by_cases hd0 : d = 0
      · simp [p, c, hd0]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
      have hβ1 : β ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_left hd1 hβ]
      have hβsq : β ^ 2 ≤ 1 := by nlinarith
      calc β ^ 2 * p ≤ p := by nlinarith [mul_nonneg (sub_nonneg.mpr hβsq) hp]
           _ ≤ c + p := le_add_of_nonneg_left hc
    exact h.trans (div_le_div_of_nonneg_right hcoef (Real.sqrt_nonneg _))
  · exact tendsto_skVectorFreeEnergy_of_nonneg μ ξ hξ hbound hβ hsmall hx hxf
  · intro y hy
    exact hunique y ⟨hy.1, hy.2.1⟩

end SpinGlasses
