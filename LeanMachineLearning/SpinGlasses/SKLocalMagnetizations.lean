/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiSnoc
public import LeanMachineLearning.SpinGlasses.SKLastSpinGaussian
public import LeanMachineLearning.SpinGlasses.SKSiteSymmetry

/-!
# The local magnetizations are asymptotically i.i.d. (Talagrand, Theorem 1.7.1)

For `4 β² < 1` and `n` fixed, the Gibbs means `⟨σ_i⟩`, `i < n`, of the `N`-spin SK system are close
in `L²`, up to `K/N`, to `tanh(β √q z_i + h)` for i.i.d. standard Gaussians `z_i` that are
measurable functions of the couplings (`SpinGlasses.sk_local_magnetizations_gaussian`).

The proof is the book's induction on `n`, run in the uniform-in-`β` form (1.190): the step uses
Eq. (1.186), Lemma 1.7.6 and the fixed-point shift at `β_- = β √(N/(N+1))`, and finally exchanges
the last site with the new site.  The site exchange has to move the Gaussian vector as well, which
is done by composing it with the measure preserving relabelling of the couplings.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- **Site exchange for Gibbs means.**  For every relabelling `π` of the sites there is a measure
preserving map `φ` of the couplings with `⟨σ_i⟩_{φ g} = ⟨σ_{π⁻¹ i}⟩_g`. -/
theorem exists_sk_site_exchange (M : ℕ) (β h : ℝ) (π : Equiv.Perm (Fin M)) :
    ∃ φ : (FinPairs M → ℝ) → (FinPairs M → ℝ),
      MeasurePreserving φ (Measure.pi fun _ : FinPairs M => gaussianReal 0 1)
        (Measure.pi fun _ : FinPairs M => gaussianReal 0 1) ∧
      ∀ (g : FinPairs M → ℝ) (i : Fin M),
        ∫ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy M β h (φ g))) =
          ∫ σ : Fin M → ℤˣ, ((σ (π.symm i) : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy M β h g)) := by
  obtain ⟨φ, hφ, hw⟩ := exists_measurePreserving_sk_gibbsWeight β h π (skGibbsEnergy M β h)
    (fun _ _ => rfl)
  refine ⟨φ, hφ, fun g i => ?_⟩
  rw [integral_count_tilted, integral_count_tilted]
  simp_rw [hw g]
  have := Equiv.sum_comp (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ))
    (fun τ : Fin M → ℤˣ => Real.exp (skGibbsEnergy M β h g τ) /
      (∑ b, Real.exp (skGibbsEnergy M β h g b)) * ((τ (π.symm i) : ℤ) : ℝ))
  rw [← this]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- A real-analytic estimate for the passage from `(β_-, q_-)` to `(β, q)`:
`(β_- √q_- - β √q)² ≤ 1/(N+1)` when `|q - q_-| ≤ 1/(N+1)`, `β_- = β √(N/(N+1))` and
`4 β² < 1`. -/
theorem sq_cavity_param_le {β q qm : ℝ} {N : ℕ} (hβ4 : 4 * β ^ 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqm : qm ∈ Set.Icc (0 : ℝ) 1)
    (hshift : |q - qm| ≤ 1 / ((N : ℝ) + 1)) :
    (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm - β * Real.sqrt q) ^ 2 ≤
      1 / ((N : ℝ) + 1) := by
  set ε : ℝ := 1 / ((N : ℝ) + 1) with hε
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one hN1]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  set s : ℝ := Real.sqrt ((N : ℝ) / (N + 1)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hx : (N : ℝ) / (N + 1) = 1 - ε := by rw [hε]; field_simp; ring
  have hs1 : 1 - ε ≤ s := by
    rw [hs, hx]
    have h0 : 0 ≤ 1 - ε := by linarith
    calc 1 - ε = Real.sqrt ((1 - ε) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - ε) := Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : s ≤ 1 := by
    rw [hs, hx]; exact Real.sqrt_le_one.mpr (by linarith)
  have hd : (Real.sqrt qm - Real.sqrt q) ^ 2 ≤ ε := by
    have h1 : (Real.sqrt qm - Real.sqrt q) ^ 2 ≤ |qm - q| := by
      have hab : |Real.sqrt qm - Real.sqrt q| ≤ Real.sqrt qm + Real.sqrt q := by
        rw [abs_le]
        constructor <;> linarith [Real.sqrt_nonneg qm, Real.sqrt_nonneg q]
      have heq : |qm - q| = |Real.sqrt qm - Real.sqrt q| * (Real.sqrt qm + Real.sqrt q) := by
        rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg qm) (Real.sqrt_nonneg q)), ← abs_mul]
        congr 1
        have := Real.sq_sqrt hqm.1
        have := Real.sq_sqrt hq.1
        nlinarith
      rw [heq, ← sq_abs]
      calc |Real.sqrt qm - Real.sqrt q| ^ 2 =
            |Real.sqrt qm - Real.sqrt q| * |Real.sqrt qm - Real.sqrt q| := sq _
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    calc _ ≤ |qm - q| := h1
      _ = |q - qm| := abs_sub_comm _ _
      _ ≤ ε := hshift
  have hsq : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq.2
  have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hdec : β * s * Real.sqrt qm - β * Real.sqrt q =
      β * s * (Real.sqrt qm - Real.sqrt q) + β * ((s - 1) * Real.sqrt q) := by ring
  have hb2 : β ^ 2 ≤ 1 / 4 := by linarith
  have he2 : ((s - 1) * Real.sqrt q) ^ 2 ≤ ε := by
    rw [mul_pow]
    have : (s - 1) ^ 2 ≤ ε := by nlinarith
    have : Real.sqrt q ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (s - 1), sq_nonneg (Real.sqrt q)]
  rw [hdec]
  have h1 : (β * s * (Real.sqrt qm - Real.sqrt q)) ^ 2 ≤ β ^ 2 * ε := by
    have hs2' : s ^ 2 ≤ 1 := by nlinarith
    have h1a : s ^ 2 * (Real.sqrt qm - Real.sqrt q) ^ 2 ≤ ε :=
      (mul_le_of_le_one_left (sq_nonneg _) hs2').trans hd
    calc (β * s * (Real.sqrt qm - Real.sqrt q)) ^ 2 =
          β ^ 2 * (s ^ 2 * (Real.sqrt qm - Real.sqrt q) ^ 2) := by ring
      _ ≤ β ^ 2 * ε := mul_le_mul_of_nonneg_left h1a (sq_nonneg β)
  have h2 : (β * ((s - 1) * Real.sqrt q)) ^ 2 ≤ β ^ 2 * ε := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left he2 (sq_nonneg β)
  have h3 : β ^ 2 * ε ≤ ε / 4 := by nlinarith
  nlinarith [sq_nonneg (β * s * (Real.sqrt qm - Real.sqrt q) - β * ((s - 1) * Real.sqrt q))]

/-- Every coordinate of a vector with the i.i.d. standard Gaussian law has second moment `1`. -/
theorem integral_sq_coord_eq_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {z : Ω → Fin n → ℝ} (hz : Measurable z)
    (hl : P.map z = Measure.pi fun _ : Fin n => gaussianReal 0 1) (i : Fin n) :
    ∫ ω, z ω i ^ 2 ∂P = 1 := by
  have h1 : P.map (fun ω => z ω i) = gaussianReal 0 1 := by
    rw [show (fun ω => z ω i) = (fun x : Fin n → ℝ => x i) ∘ z from rfl,
      ← Measure.map_map (measurable_pi_apply i) hz, hl]
    exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
  have hm : Measurable fun ω => z ω i := (measurable_pi_apply i).comp hz
  rw [← integral_sq_gaussianReal_zero_one, ← h1, integral_map hm.aemeasurable (by fun_prop)]

/-- A coordinate of a vector with the i.i.d. standard Gaussian law has an integrable square. -/
theorem integrable_sq_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {z : Ω → Fin n → ℝ} (hz : Measurable z)
    (hl : P.map z = Measure.pi fun _ : Fin n => gaussianReal 0 1) (i : Fin n) :
    Integrable (fun ω => z ω i ^ 2) P := by
  by_contra hni
  have := integral_undef hni
  rw [integral_sq_coord_eq_one hz hl i] at this
  exact one_ne_zero this

/-- **The induction step of Theorem 1.7.1** (uniform form (1.190) from `n` to `n + 1`).  If the
statement holds for `n` sites (with constant `Kn`, uniformly in `0 ≤ β ≤ β₀` and the fixed point
`q`), then it holds for `n + 1` sites with an explicit constant. -/
theorem sk_local_magnetizations_step (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ)
    (n : ℕ) (Kn : ℝ) (hKn : 0 ≤ Kn)
    (ih : ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ (N : ℕ) (hN : n < N), ∃ z : (FinPairs N → ℝ) → Fin n → ℝ, Measurable z ∧
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).map z =
          Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
        ∑ i : Fin n, ∫ g : FinPairs N → ℝ,
          (∫ σ : Fin N → ℤˣ, ((σ (Fin.castLE hN.le i) : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)) -
            Real.tanh (β * Real.sqrt q * z g i + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ Kn / N) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ (N : ℕ) (hN : n + 1 < N), ∃ z : (FinPairs N → ℝ) → Fin (n + 1) → ℝ, Measurable z ∧
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).map z =
          Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) ∧
        ∑ i : Fin (n + 1), ∫ g : FinPairs N → ℝ,
          (∫ σ : Fin N → ℤˣ, ((σ (Fin.castLE hN.le i) : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)) -
            Real.tanh (β * Real.sqrt q * z g i + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / N := by
  obtain ⟨Kb, hKb0, hKb⟩ := sk_old_spin_cavity_approx β₀ hβ₀' h
  obtain ⟨Kc, hKc0, hKc⟩ := sk_last_spin_gaussian_approx β₀ hβ₀ hβ₀' h
  refine ⟨3 * n * Kb + 6 * Kn + 3 * n + Kc + 1, by positivity,
    fun β hβ0 hββ₀ q hq N' hN' => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, N' = N + 1 := ⟨N' - 1, by omega⟩
  have hnN : n < N := by omega
  have hNpos : 0 < N := by omega
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := pow_le_pow_left₀ hβ0 hββ₀ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hs1 : Real.sqrt ((N : ℝ) / (N + 1)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hN1).mpr (by linarith))
  have hβm0 : 0 ≤ β * Real.sqrt ((N : ℝ) / (N + 1)) := mul_nonneg hβ0 (Real.sqrt_nonneg _)
  have hβm : β * Real.sqrt ((N : ℝ) / (N + 1)) ≤ β₀ := (mul_le_of_le_one_right hβ0 hs1).trans hββ₀
  obtain ⟨qm, hqmI, hqm, hshift⟩ := exists_fixedPoint_cavity (N := N) h q hβ0 hβ4 hq
  have hcparam := sq_cavity_param_le (N := N) hβ4 (fixedPoint_mem_Icc hq) hqmI hshift
  obtain ⟨zm, hzm, hzml, hzms⟩ := ih _ hβm0 hβm qm hqm N hnN
  obtain ⟨znew, hznew, hznewl, hznewi, hznewb⟩ := hKc β hβ0 hββ₀ q hq N hNpos
  set P : Measure (FinPairs (N + 1) → ℝ) := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    with hP
  set P' : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP'
  have hem : Measurable (skCavityDisorderEquiv N) := (skCavityDisorderEquiv N).measurable
  have hfst : MeasurePreserving (fun g : FinPairs (N + 1) → ℝ => (skCavityDisorderEquiv N g).1)
      P P' := (Measure.measurePreserving_fst).comp (measurePreserving_skCavityDisorderEquiv N)
  -- the Gaussian vector for the sites `0, …, n - 1, last`
  obtain ⟨zp, hzp⟩ : ∃ zp : (FinPairs (N + 1) → ℝ) → Fin (n + 1) → ℝ, ∀ g, zp g =
      (MeasurableEquiv.finSuccProd ℝ n).symm (zm (skCavityDisorderEquiv N g).1, znew g) :=
    ⟨_, fun _ => rfl⟩
  have hzp_cs : ∀ g (j : Fin n), zp g (Fin.castSucc j) = zm (skCavityDisorderEquiv N g).1 j := by
    intro g j; rw [hzp]; simp
  have hzp_last : ∀ g, zp g (Fin.last n) = znew g := by
    intro g; rw [hzp]; simp
  have hY : Measurable fun g => zm (skCavityDisorderEquiv N g).1 := hzm.comp hfst.measurable
  have hzp_meas : Measurable zp := by
    rw [show zp = fun g => (MeasurableEquiv.finSuccProd ℝ n).symm
      (zm (skCavityDisorderEquiv N g).1, znew g) from funext hzp]
    exact (MeasurableEquiv.measurable _).comp (hY.prodMk hznew)
  have hzp_law : P.map zp = Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    have hind : IndepFun (fun g => zm (skCavityDisorderEquiv N g).1) znew P :=
      hznewi.symm.comp hzm measurable_id
    have hYl : P.map (fun g => zm (skCavityDisorderEquiv N g).1) =
        Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
      rw [show (fun g => zm (skCavityDisorderEquiv N g).1) =
        zm ∘ (fun g => (skCavityDisorderEquiv N g).1) from rfl,
        ← Measure.map_map hzm hfst.measurable, hfst.map_eq, hzml]
    have := map_finSuccProd_symm_eq_pi (P := P) hY hznew hind hYl hznewl
    rw [show zp = fun g => (MeasurableEquiv.finSuccProd ℝ n).symm
      (zm (skCavityDisorderEquiv N g).1, znew g) from funext hzp]
    exact this
  -- the site exchange of the new site `n` with the last site
  set π : Equiv.Perm (Fin (N + 1)) := Equiv.swap (⟨n, by omega⟩ : Fin (N + 1)) (Fin.last N)
    with hπ
  obtain ⟨φ, hφ, hφX⟩ := exists_sk_site_exchange (N + 1) β h π
  have hpi_old : ∀ j' : Fin n, π (Fin.castLE hN'.le (Fin.castSucc j')) =
      Fin.castSucc (Fin.castLE hnN.le j') := by
    intro j'
    rw [hπ, Equiv.swap_apply_of_ne_of_ne]
    · exact Fin.ext (by simp)
    · intro h1; have := congrArg Fin.val h1; simp at this; omega
    · intro h1; have := congrArg Fin.val h1; simp at this; omega
  have hpi_new : π (Fin.castLE hN'.le (Fin.last n)) = Fin.last N := by
    have : Fin.castLE hN'.le (Fin.last n) = (⟨n, by omega⟩ : Fin (N + 1)) := Fin.ext (by simp)
    rw [this, hπ, Equiv.swap_apply_left]
  sorry

end SpinGlasses
