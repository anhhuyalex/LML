/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.RSAccuracy

/-!
# The Shcherbina--Tirozzi model: continuity and existence for the soft RS equations

Talagrand, *Spin Glasses*, Vol. I, Section 3.2 (after Proposition 3.2.12): letting `N → ∞`, the
physical overlaps `(q, ρ)` of Proposition 3.2.12 yield an exact solution to the replica-symmetric
equations `(3.69)`, `(3.76)`, `(3.104)` with `0 ≤ q < ρ`. Moreover, for a fixed smooth concave
potential `u` and large `N`, the physical parameters `(M / (N + 1), κ, h, q, ρ)` are uniformly close
to exact solutions of the soft RS equations.

## Main declarations

* `SpinGlasses.continuous_shcherbinaTirozzi_rsParameters`: joint continuity of `(α, q, ρ) ↦ (r, r̄)`
  under `(3.69)`.
* `SpinGlasses.exists_shcherbinaTirozzi_rsEquations_subseq_limit`: compactness and passage to the
  limit along any sequence of sizes `(N k, M k)` with `N k → ∞`.
* `SpinGlasses.exists_shcherbinaTirozzi_rsEquations_solution`: existence of an exact solution to the
  soft RS equations `(3.69)`, `(3.76)`, `(3.104)` with `0 ≤ q < ρ` for any `0 ≤ α ≤ 10`, `0 < κ`.
* `SpinGlasses.exists_shcherbinaTirozzi_rsEquations_near_of_large`: uniform closeness of finite-size
  parameters `(M / (N + 1), κ, h, q, ρ)` to exact solutions for fixed `u` and large `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

section Continuity

/-- **Continuity of the RS parameters (3.69):** for `u ≤ 0` continuous with continuous bounded first
and second derivatives `|u'| ≤ D`, `|u''| ≤ D₂`, the maps `(α, q, ρ) ↦ r(α, q, ρ)` and
`(α, q, ρ) ↦ r̄(α, q, ρ)` are continuous on `ℝ × ℝ × ℝ`. -/
theorem continuous_shcherbinaTirozzi_rsParameters {u : ℝ → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, u x ≤ 0) (hu1c : Continuous (deriv u)) (hu2c : Continuous (deriv (deriv u)))
    {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
    let Z : ℝ → ℝ → ℝ := fun q ρ y =>
      ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
    let V : ℝ → ℝ → ℝ := fun q ρ y =>
      (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z q ρ y
    let W : ℝ → ℝ → ℝ := fun q ρ y =>
      (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
          deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z q ρ y
    Continuous (fun p : ℝ × ℝ × ℝ =>
      p.1 * ∫ z, V p.2.1 p.2.2 (Real.sqrt p.2.1 * z) ^ 2 ∂(gaussianReal 0 1)) ∧
    Continuous (fun p : ℝ × ℝ × ℝ =>
      p.1 * ∫ z, W p.2.1 p.2.2 (Real.sqrt p.2.1 * z) ∂(gaussianReal 0 1)) := by
  intro Z V W
  have harg_c : ∀ z ξ : ℝ,
      Continuous fun p : ℝ × ℝ × ℝ => Real.sqrt p.2.1 * z + Real.sqrt (p.2.2 - p.2.1) * ξ :=
    fun _ _ => by fun_prop
  have harg_m : ∀ p : ℝ × ℝ × ℝ,
      Measurable fun q : ℝ × ℝ => Real.sqrt p.2.1 * q.1 + Real.sqrt (p.2.2 - p.2.1) * q.2 :=
    fun _ => by fun_prop
  have hV_cont : Continuous fun p : ℝ × ℝ × ℝ =>
      ∫ z, V p.2.1 p.2.2 (Real.sqrt p.2.1 * z) ^ 2 ∂(gaussianReal 0 1) := by
    simpa only [V, Z] using continuous_integral_comp_ratio_of_isFiniteMeasure
      (ν := gaussianReal 0 1) (μ := gaussianReal 0 1)
      (arg := fun p : ℝ × ℝ × ℝ => fun z ξ => Real.sqrt p.2.1 * z + Real.sqrt (p.2.2 - p.2.1) * ξ)
      (f := deriv u) (u := u) (φ := fun t => t ^ 2) (B := D) (Bφ := D ^ 2)
      harg_c harg_m hu1c hu (continuous_pow 2) hD hu0 fun t ht => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hW_cont : Continuous fun p : ℝ × ℝ × ℝ =>
      ∫ z, W p.2.1 p.2.2 (Real.sqrt p.2.1 * z) ∂(gaussianReal 0 1) := by
    simpa only [W, Z] using continuous_integral_comp_ratio_of_isFiniteMeasure
      (ν := gaussianReal 0 1) (μ := gaussianReal 0 1)
      (arg := fun p : ℝ × ℝ × ℝ => fun z ξ => Real.sqrt p.2.1 * z + Real.sqrt (p.2.2 - p.2.1) * ξ)
      (f := fun x => deriv (deriv u) x + deriv u x ^ 2) (u := u) (φ := id)
      (B := D₂ + D ^ 2) (Bφ := D₂ + D ^ 2)
      harg_c harg_m (hu2c.add (hu1c.pow 2)) hu continuous_id
      (abs_deriv_deriv_add_sq_deriv_le hD hD₂) hu0 fun _ ht => ht
  exact ⟨continuous_fst.mul hV_cont, continuous_fst.mul hW_cont⟩

end Continuity

section Existence

/-- **Compactness and passage to the limit for finite-size physical RS parameters:** for a fixed
potential `u` satisfying the standing bounds, along any sequence of sizes `(N k, M k)` with
`N k → ∞`, `M k / (N k + 1) ≤ α₀ ≤ 10`, `κ₀ ≤ κ k ≤ κ₁`, and `|h k| ≤ h₀`, a subsequence converges
to `(α', κ', h', q', ρ')` with `0 ≤ q' < ρ'` solving the exact soft RS equations `(3.69)`,
`(3.76)`, `(3.104)`. -/
theorem exists_shcherbinaTirozzi_rsEquations_subseq_limit
    {κ₀ κ₁ α₀ h₀ D : ℝ} (hκ₀ : 0 < κ₀) (hα₀ : α₀ ≤ 10) {u : ℝ → ℝ}
    (huc : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (hgrow : ∀ x, -D * (1 + |x|) ≤ u x)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : Differentiable ℝ (deriv (deriv u)))
    (hu4 : Differentiable ℝ (deriv (deriv (deriv u))))
    (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ x, |deriv (deriv u) x| ≤ D)
    (hD3 : ∀ x, |deriv (deriv (deriv u)) x| ≤ D)
    (hD4 : ∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D)
    {N M : ℕ → ℕ} {κ h : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (hα_bd : ∀ k, (M k : ℝ) / ((N k : ℝ) + 1) ≤ α₀)
    (hκ_bd : ∀ k, κ₀ ≤ κ k ∧ κ k ≤ κ₁) (hh_bd : ∀ k, |h k| ≤ h₀) :
    let P_fn (N M : ℕ) : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :=
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    let G_fn (N M : ℕ) (κ h : ℝ) :
        (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)) := fun d =>
      volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ
    let ρ_fn (N M : ℕ) (κ h : ℝ) : ℝ :=
      ∫ d, ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(G_fn N M κ h d) ∂(P_fn N M)
    let q_fn (N M : ℕ) (κ h : ℝ) : ℝ :=
      ∫ d, ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G_fn N M κ h d)) ^ 2 ∂(P_fn N M)
    ∃ (φ : ℕ → ℕ) (α' κ' h' q' ρ' : ℝ), StrictMono φ ∧
      0 ≤ α' ∧ α' ≤ α₀ ∧ κ₀ ≤ κ' ∧ κ' ≤ κ₁ ∧ |h'| ≤ h₀ ∧ 0 ≤ q' ∧ q' < ρ' ∧
      Tendsto (fun k => (M (φ k) : ℝ) / ((N (φ k) : ℝ) + 1)) atTop (𝓝 α') ∧
      Tendsto (κ ∘ φ) atTop (𝓝 κ') ∧ Tendsto (h ∘ φ) atTop (𝓝 h') ∧
      Tendsto (fun k => q_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k))) atTop (𝓝 q') ∧
      Tendsto (fun k => ρ_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k))) atTop (𝓝 ρ') ∧
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ' - q') * ξ) *
        Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ' - q') * ξ) +
          deriv u (y + Real.sqrt (ρ' - q') * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α' * ∫ z, V (Real.sqrt q' * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α' * ∫ z, W (Real.sqrt q' * z) ∂(gaussianReal 0 1)
      0 < 2 * κ' + r - rBar ∧
        ρ' = (2 * κ' + r - rBar)⁻¹ + (r + h' ^ 2) / (2 * κ' + r - rBar) ^ 2 ∧
        q' = (r + h' ^ 2) / (2 * κ' + r - rBar) ^ 2 := by
  intro P_fn G_fn ρ_fn q_fn
  obtain ⟨Q, hQ0, hphys⟩ := exists_shcherbinaTirozzi_physical_parameter_bounds κ₀ h₀ D hκ₀
  obtain ⟨K, hK0, hacc⟩ := exists_shcherbinaTirozzi_rsEquations_accuracy κ₀ h₀ D hκ₀
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hκ₁ : κ₀ ≤ κ₁ := (hκ_bd 0).1.trans (hκ_bd 0).2
  have hh₀ : 0 ≤ h₀ := (abs_nonneg _).trans (hh_bd 0)
  let α : ℕ → ℝ := fun k => (M k : ℝ) / ((N k : ℝ) + 1)
  let q : ℕ → ℝ := fun k => q_fn (N k) (M k) (κ k) (h k)
  let ρ : ℕ → ℝ := fun k => ρ_fn (N k) (M k) (κ k) (h k)
  let V_k (k : ℕ) : ℝ → ℝ := fun y =>
    (∫ ξ, deriv u (y + Real.sqrt (ρ k - q k) * ξ) *
      Real.exp (u (y + Real.sqrt (ρ k - q k) * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u (y + Real.sqrt (ρ k - q k) * ξ)) ∂(gaussianReal 0 1)
  let W_k (k : ℕ) : ℝ → ℝ := fun y =>
    (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ k - q k) * ξ) +
        deriv u (y + Real.sqrt (ρ k - q k) * ξ) ^ 2) *
      Real.exp (u (y + Real.sqrt (ρ k - q k) * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u (y + Real.sqrt (ρ k - q k) * ξ)) ∂(gaussianReal 0 1)
  let r_k : ℕ → ℝ := fun k => α k * ∫ z, V_k k (Real.sqrt (q k) * z) ^ 2 ∂(gaussianReal 0 1)
  let rBar_k : ℕ → ℝ := fun k => α k * ∫ z, W_k k (Real.sqrt (q k) * z) ∂(gaussianReal 0 1)
  let a_k : ℕ → ℝ := fun k => 2 * κ k + r_k k - rBar_k k
  have hM_bd : ∀ k, M k ≤ 10 * (N k + 1) := fun k => by
    have h1 : (M k : ℝ) ≤ 10 * ((N k : ℝ) + 1) := by
      rw [← div_le_iff₀ (by positivity)]
      exact (hα_bd k).trans hα₀
    exact_mod_cast h1
  have hα_nonneg : ∀ k, 0 ≤ α k := fun k => by positivity
  have hα₀_nonneg : 0 ≤ α₀ := (hα_nonneg 0).trans (hα_bd 0)
  have hbd : ∀ k, 0 ≤ q k ∧ q k ≤ ρ k ∧ ρ k ≤ Q ∧
      r_k k - rBar_k k ≤ 10 * (2 * D ^ 2 + D) := fun k => by
    obtain ⟨hq0, hqρ, hρQ, _, _, _, hdiff⟩ := hphys (N k) (M k) (κ k) (h k) D u
      (hκ_bd k).1 (hh_bd k) (hM_bd k) huc hu0 hgrow hu1 hu2 hD1 hD2
    exact ⟨hq0, hqρ, hρQ, hdiff⟩
  have hres : ∀ k, 0 < a_k k ∧
      |ρ k - ((a_k k)⁻¹ + (r_k k + h k ^ 2) / a_k k ^ 2)| ≤ K / Real.sqrt ((N k : ℝ) + 1) ∧
      |q k - (r_k k + h k ^ 2) / a_k k ^ 2| ≤ K / Real.sqrt ((N k : ℝ) + 1) := fun k =>
    hacc (N k) (M k) (κ k) (h k) u (hκ_bd k).1 (hh_bd k) (hM_bd k) huc hu0 hgrow
      hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4
  let U : ℝ := 2 * κ₁ + 10 * (2 * D ^ 2 + D)
  have hU_pos : 0 < U := by positivity
  have ha_bounds : ∀ k, 2 * κ₀ ≤ a_k k ∧ a_k k ≤ U := fun k => by
    have hrr := (hbd k).2.2.2
    have h_a_lo : 2 * κ₀ ≤ a_k k := (hres k).1.le.trans' (by
      have := (hphys (N k) (M k) (κ k) (h k) D u (hκ_bd k).1 (hh_bd k) (hM_bd k)
        huc hu0 hgrow hu1 hu2 hD1 hD2).2.2.2.2.2.1
      dsimp only [a_k, r_k, rBar_k, α, V_k, W_k, q, ρ, q_fn, ρ_fn, G_fn, P_fn] at *
      linarith [(hκ_bd k).1])
    refine ⟨?_, ?_⟩
    · have := (hphys (N k) (M k) (κ k) (h k) D u (hκ_bd k).1 (hh_bd k) (hM_bd k)
        huc hu0 hgrow hu1 hu2 hD1 hD2).2.2.2.2.2.1
      dsimp only [a_k, r_k, rBar_k, α, V_k, W_k, q, ρ, q_fn, ρ_fn, G_fn, P_fn] at *
      linarith [(hκ_bd k).1]
    · dsimp only [a_k, U]; linarith [(hκ_bd k).2]
  -- Extract a converging subsequence in the compact box `[0, α₀] × [κ₀, κ₁] × [-h₀, h₀] × [0, Q]²`
  set K_box : Set ((ℝ × ℝ × ℝ) × (ℝ × ℝ)) :=
    (Icc 0 α₀ ×ˢ (Icc κ₀ κ₁ ×ˢ Icc (-h₀) h₀)) ×ˢ (Icc 0 Q ×ˢ Icc 0 Q)
  have hK_comp : IsCompact K_box :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod
      (isCompact_Icc.prod isCompact_Icc)
  have hmem : ∀ k, ((α k, κ k, h k), (q k, ρ k)) ∈ K_box := fun k =>
    ⟨⟨⟨hα_nonneg k, hα_bd k⟩, ⟨hκ_bd k, abs_le.1 (hh_bd k)⟩⟩,
      ⟨⟨(hbd k).1, (hbd k).2.1.trans (hbd k).2.2.1⟩,
        ⟨(hbd k).1.trans (hbd k).2.1, (hbd k).2.2.1⟩⟩⟩
  obtain ⟨⟨⟨α', κ', h'⟩, ⟨q', ρ'⟩⟩, hlim_mem, φ, hφ_mono, hφ_lim⟩ :=
    hK_comp.tendsto_subseq hmem
  have hα_l : Tendsto (α ∘ φ) atTop (𝓝 α') :=
    (continuous_fst.comp continuous_fst |>.tendsto _).comp hφ_lim
  have hκ_l : Tendsto (κ ∘ φ) atTop (𝓝 κ') :=
    (continuous_fst.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hh_l : Tendsto (h ∘ φ) atTop (𝓝 h') :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst) |>.tendsto _).comp hφ_lim
  have hq_l : Tendsto (q ∘ φ) atTop (𝓝 q') :=
    (continuous_fst.comp continuous_snd |>.tendsto _).comp hφ_lim
  have hρ_l : Tendsto (ρ ∘ φ) atTop (𝓝 ρ') :=
    (continuous_snd.comp continuous_snd |>.tendsto _).comp hφ_lim
  have hsqrt_atTop : Tendsto (fun k => Real.sqrt ((N (φ k) : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp (hN.comp hφ_mono.tendsto_atTop)).atTop_add
        tendsto_const_nhds)
  have herr_l : Tendsto (fun k => K / Real.sqrt ((N (φ k) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt_atTop
  -- Lower bound on `ρ' - q'`
  have hgap : U⁻¹ ≤ ρ' - q' := by
    have hlo : Tendsto (fun k => U⁻¹ - 2 * (K / Real.sqrt ((N (φ k) : ℝ) + 1))) atTop (𝓝 U⁻¹) := by
      simpa using (tendsto_const_nhds (x := U⁻¹)).sub (herr_l.const_mul 2)
    refine le_of_tendsto_of_tendsto' hlo (hρ_l.sub hq_l) fun k => ?_
    have ha_inv : U⁻¹ ≤ (a_k (φ k))⁻¹ :=
      inv_anti₀ (by linarith [(ha_bounds (φ k)).1]) (ha_bounds (φ k)).2
    have h1 := (abs_le.1 (hres (φ k)).2.1).1
    have h2 := (abs_le.1 (hres (φ k)).2.2).2
    linarith
  have hqρ' : q' < ρ' := by linarith [inv_pos.2 hU_pos]
  -- Continuity of `(α, q, ρ) ↦ (r, r̄)`
  obtain ⟨hr_cont, hrBar_cont⟩ := continuous_shcherbinaTirozzi_rsParameters
    hu1.continuous hu0 hu2.continuous hu3.continuous hD1 hD2
  have hp_l : Tendsto (fun k => (α (φ k), q (φ k), ρ (φ k))) atTop (𝓝 (α', q', ρ')) :=
    hα_l.prodMk (hq_l.prodMk hρ_l)
  have hr_l : Tendsto (r_k ∘ φ) atTop (𝓝 _) := (hr_cont.tendsto _).comp hp_l
  have hrBar_l : Tendsto (rBar_k ∘ φ) atTop (𝓝 _) := (hrBar_cont.tendsto _).comp hp_l
  have ha_l : Tendsto (a_k ∘ φ) atTop (𝓝 _) := ((hκ_l.const_mul 2).add hr_l).sub hrBar_l
  have ha'_ge : 2 * κ₀ ≤ 2 * κ' +
      (α' * ∫ z, ((∫ ξ, deriv u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ) *
        Real.exp (u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) ^ 2
        ∂(gaussianReal 0 1)) -
      (α' * ∫ z, ((∫ ξ, (deriv (deriv u) (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ) +
        deriv u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ) ^ 2) *
        Real.exp (u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (Real.sqrt q' * z + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1))
        ∂(gaussianReal 0 1)) :=
    ge_of_tendsto ha_l (Eventually.of_forall fun k => (ha_bounds (φ k)).1)
  have ha'_pos : 0 < _ := lt_of_lt_of_le (by positivity) ha'_ge
  have hq_rhs_l : Tendsto (fun k => (r_k (φ k) + h (φ k) ^ 2) / a_k (φ k) ^ 2) atTop (𝓝 _) :=
    (hr_l.add (hh_l.pow 2)).div (ha_l.pow 2) (ne_of_gt (pow_pos ha'_pos 2))
  have hρ_rhs_l : Tendsto
      (fun k => (a_k (φ k))⁻¹ + (r_k (φ k) + h (φ k) ^ 2) / a_k (φ k) ^ 2) atTop (𝓝 _) :=
    (ha_l.inv₀ (ne_of_gt ha'_pos)).add hq_rhs_l
  have hρ_diff_0 : Tendsto
      (fun k => ρ (φ k) - ((a_k (φ k))⁻¹ + (r_k (φ k) + h (φ k) ^ 2) / a_k (φ k) ^ 2))
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (Real.norm_eq_abs _).trans_le (hres (φ k)).2.1) herr_l
  have hq_diff_0 : Tendsto
      (fun k => q (φ k) - (r_k (φ k) + h (φ k) ^ 2) / a_k (φ k) ^ 2) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (Real.norm_eq_abs _).trans_le (hres (φ k)).2.2) herr_l
  have hρ_eq : ρ' = _ := sub_eq_zero.1 (tendsto_nhds_unique (hρ_l.sub hρ_rhs_l) hρ_diff_0)
  have hq_eq : q' = _ := sub_eq_zero.1 (tendsto_nhds_unique (hq_l.sub hq_rhs_l) hq_diff_0)
  refine ⟨φ, α', κ', h', q', ρ', hφ_mono, hlim_mem.1.1.1, hlim_mem.1.1.2, hlim_mem.1.2.1.1,
    hlim_mem.1.2.1.2, abs_le.2 hlim_mem.1.2.2, hlim_mem.2.1.1, hqρ', hα_l, hκ_l, hh_l,
    hq_l, hρ_l, ha'_pos, hρ_eq, hq_eq⟩

/-- **Existence of a solution to the soft RS equations (Talagrand, Section 3.2, after
Proposition 3.2.12):** for any `0 ≤ α ≤ 10`, `κ > 0`, `h : ℝ`, and `C^4` concave nonpositive
potential `u` with linear lower bound and bounded derivatives `|u^(j)| ≤ D` (`1 ≤ j ≤ 4`), there
exist `(q, ρ, r, r̄)` with `0 ≤ q < ρ` and `0 < 2κ + r - r̄` solving the exact replica-symmetric
equations `(3.69)`, `(3.76)`, `(3.104)`. -/
theorem exists_shcherbinaTirozzi_rsEquations_solution {α κ h D : ℝ} (hα0 : 0 ≤ α)
    (hα10 : α ≤ 10) (hκ : 0 < κ) {u : ℝ → ℝ} (huc : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (hgrow : ∀ x, -D * (1 + |x|) ≤ u x) (hu1 : Differentiable ℝ u)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : Differentiable ℝ (deriv (deriv u)))
    (hu4 : Differentiable ℝ (deriv (deriv (deriv u))))
    (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ x, |deriv (deriv u) x| ≤ D)
    (hD3 : ∀ x, |deriv (deriv (deriv u)) x| ≤ D)
    (hD4 : ∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) :
    ∃ q ρ : ℝ, 0 ≤ q ∧ q < ρ ∧
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ - q) * ξ) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ - q) * ξ) +
          deriv u (y + Real.sqrt (ρ - q) * ξ) ^ 2) *
        Real.exp (u (y + Real.sqrt (ρ - q) * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      0 < 2 * κ + r - rBar ∧
        ρ = (2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 ∧
        q = (r + h ^ 2) / (2 * κ + r - rBar) ^ 2 := by
  let M : ℕ → ℕ := fun k => Nat.floor (α * ((k : ℝ) + 1))
  have hα_bd : ∀ k, (M k : ℝ) / ((k : ℝ) + 1) ≤ α := fun k => by
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hα_tend : Tendsto (fun k => (M k : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 α) := by
    have hlo : Tendsto (fun k : ℕ => α - ((k : ℝ) + 1)⁻¹) atTop (𝓝 α) := by
      have h0 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using (tendsto_const_nhds (x := α)).sub h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun k => ?_) hα_bd
    have hlt : α * ((k : ℝ) + 1) - 1 < (M k : ℝ) := Nat.sub_one_lt_floor _
    rw [sub_lt_iff_lt_add, ← div_lt_iff₀ (by positivity)] at hlt
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    nlinarith [div_mul_cancel₀ (1 : ℝ) hk1.ne']
  obtain ⟨φ, α', κ', h', q', ρ', hφ_mono, _, _, hκ_lo, hκ_hi, _, hq0, hqρ, hα_sub, hκ_sub, hh_sub,
      _, _, ha_pos, hρ_eq, hq_eq⟩ :=
    exists_shcherbinaTirozzi_rsEquations_subseq_limit hκ hα10 huc hu0 hgrow hu1 hu2 hu3 hu4
      hD1 hD2 hD3 hD4 tendsto_id hα_bd (fun _ => ⟨le_rfl, le_rfl⟩) (fun _ => le_rfl)
  have hα'_eq : α' = α :=
    tendsto_nhds_unique hα_sub (hα_tend.comp hφ_mono.tendsto_atTop)
  have hκ'_eq : κ' = κ := tendsto_nhds_unique hκ_sub tendsto_const_nhds
  have hh'_eq : h' = h := tendsto_nhds_unique hh_sub tendsto_const_nhds
  subst hα'_eq hκ'_eq hh'_eq
  exact ⟨q', ρ', hq0, hqρ, ha_pos, hρ_eq, hq_eq⟩

/-- **Uniform closeness of finite-size RS parameters to exact solutions (Talagrand, Section 3.3,
proof of Theorem 3.3.2):** fix `0 < κ₀ ≤ κ₁`, `0 ≤ α₀ ≤ 10`, `0 ≤ h₀`, a potential `u` satisfying
the standing bounds, and a tolerance `δ > 0`. Then for all sufficiently large `N` and all
`M / (N + 1) ≤ α₀`, `κ ∈ [κ₀, κ₁]`, `|h| ≤ h₀`, the physical parameters
`(M / (N + 1), κ, h, q_{N+1,M}, ρ_{N+1,M})` lie within `δ` of an exact solution
`(α', κ', h', q', ρ')` to the soft RS equations `(3.69)`, `(3.76)`, `(3.104)` in
`[0, α₀] × [κ₀, κ₁] × [-h₀, h₀]`. -/
theorem exists_shcherbinaTirozzi_rsEquations_near_of_large
    {κ₀ κ₁ α₀ h₀ D δ : ℝ} (hκ₀ : 0 < κ₀) (hα₀ : α₀ ≤ 10) (hδ : 0 < δ) {u : ℝ → ℝ}
    (huc : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (hgrow : ∀ x, -D * (1 + |x|) ≤ u x)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : Differentiable ℝ (deriv (deriv u)))
    (hu4 : Differentiable ℝ (deriv (deriv (deriv u))))
    (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ x, |deriv (deriv u) x| ≤ D)
    (hD3 : ∀ x, |deriv (deriv (deriv u)) x| ≤ D)
    (hD4 : ∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) :
    let P_fn (N M : ℕ) : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :=
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    let G_fn (N M : ℕ) (κ h : ℝ) :
        (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)) := fun d =>
      volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ
    let ρ_fn (N M : ℕ) (κ h : ℝ) : ℝ :=
      ∫ d, ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(G_fn N M κ h d) ∂(P_fn N M)
    let q_fn (N M : ℕ) (κ h : ℝ) : ℝ :=
      ∫ d, ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G_fn N M κ h d)) ^ 2 ∂(P_fn N M)
    ∃ N₀ : ℕ, ∀ (N M : ℕ) (κ h : ℝ), N₀ ≤ N →
      (M : ℝ) / ((N : ℝ) + 1) ≤ α₀ → κ₀ ≤ κ → κ ≤ κ₁ → |h| ≤ h₀ →
      ∃ α' κ' h' q' ρ' : ℝ,
        0 ≤ α' ∧ α' ≤ α₀ ∧ κ₀ ≤ κ' ∧ κ' ≤ κ₁ ∧ |h'| ≤ h₀ ∧ 0 ≤ q' ∧ q' < ρ' ∧
        (let Z : ℝ → ℝ := fun y =>
          ∫ ξ, Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)
         let V : ℝ → ℝ := fun y => (∫ ξ, deriv u (y + Real.sqrt (ρ' - q') * ξ) *
           Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) / Z y
         let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + Real.sqrt (ρ' - q') * ξ) +
             deriv u (y + Real.sqrt (ρ' - q') * ξ) ^ 2) *
           Real.exp (u (y + Real.sqrt (ρ' - q') * ξ)) ∂(gaussianReal 0 1)) / Z y
         let r : ℝ := α' * ∫ z, V (Real.sqrt q' * z) ^ 2 ∂(gaussianReal 0 1)
         let rBar : ℝ := α' * ∫ z, W (Real.sqrt q' * z) ∂(gaussianReal 0 1)
         0 < 2 * κ' + r - rBar ∧
           ρ' = (2 * κ' + r - rBar)⁻¹ + (r + h' ^ 2) / (2 * κ' + r - rBar) ^ 2 ∧
           q' = (r + h' ^ 2) / (2 * κ' + r - rBar) ^ 2) ∧
        |(M : ℝ) / ((N : ℝ) + 1) - α'| ≤ δ ∧ |κ - κ'| ≤ δ ∧ |h - h'| ≤ δ ∧
        |q_fn N M κ h - q'| ≤ δ ∧ |ρ_fn N M κ h - ρ'| ≤ δ := by
  intro P_fn G_fn ρ_fn q_fn
  by_contra hcon
  push Not at hcon
  choose N M κ h hN_ge hα_bd hκ0 hκ1 hh_bd hbad using hcon
  have hN_atTop : Tendsto N atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => hk.trans (hN_ge k)⟩
  obtain ⟨φ, α', κ', h', q', ρ', _, hα'0, hα'1, hκ'0, hκ'1, hh', hq'0, hq'ρ',
      hα_l, hκ_l, hh_l, hq_l, hρ_l, ha'_pos, hρ_eq, hq_eq⟩ :=
    exists_shcherbinaTirozzi_rsEquations_subseq_limit hκ₀ hα₀ huc hu0 hgrow hu1 hu2 hu3 hu4
      hD1 hD2 hD3 hD4 hN_atTop hα_bd (fun k => ⟨hκ0 k, hκ1 k⟩) hh_bd
  have hev : ∀ᶠ k in atTop,
      |(M (φ k) : ℝ) / ((N (φ k) : ℝ) + 1) - α'| < δ ∧ |κ (φ k) - κ'| < δ ∧
        |h (φ k) - h'| < δ ∧ |q_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k)) - q'| < δ ∧
        |ρ_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k)) - ρ'| < δ := by
    have h1 : Tendsto (fun k => |(M (φ k) : ℝ) / ((N (φ k) : ℝ) + 1) - α'|) atTop (𝓝 0) := by
      have t := (hα_l.sub tendsto_const_nhds).abs; rwa [sub_self, abs_zero] at t
    have h2 : Tendsto (fun k => |κ (φ k) - κ'|) atTop (𝓝 0) := by
      have t := (hκ_l.sub tendsto_const_nhds).abs; rwa [sub_self, abs_zero] at t
    have h3 : Tendsto (fun k => |h (φ k) - h'|) atTop (𝓝 0) := by
      have t := (hh_l.sub tendsto_const_nhds).abs; rwa [sub_self, abs_zero] at t
    have h4 : Tendsto (fun k => |q_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k)) - q'|)
        atTop (𝓝 0) := by
      have t := (hq_l.sub tendsto_const_nhds).abs; rwa [sub_self, abs_zero] at t
    have h5 : Tendsto (fun k => |ρ_fn (N (φ k)) (M (φ k)) (κ (φ k)) (h (φ k)) - ρ'|)
        atTop (𝓝 0) := by
      have t := (hρ_l.sub tendsto_const_nhds).abs; rwa [sub_self, abs_zero] at t
    exact (h1.eventually (Iio_mem_nhds hδ)).and ((h2.eventually (Iio_mem_nhds hδ)).and
      ((h3.eventually (Iio_mem_nhds hδ)).and ((h4.eventually (Iio_mem_nhds hδ)).and
        (h5.eventually (Iio_mem_nhds hδ)))))
  obtain ⟨k, hk1, hk2, hk3, hk4, hk5⟩ := hev.exists
  have hcontra := hbad (φ k) α' κ' h' q' ρ' hα'0 hα'1 hκ'0 hκ'1 hh' hq'0 hq'ρ'
    ⟨ha'_pos, hρ_eq, hq_eq⟩ hk1.le hk2.le hk3.le hk4.le
  exact hk5.not_ge hcontra

end Existence

end SpinGlasses
