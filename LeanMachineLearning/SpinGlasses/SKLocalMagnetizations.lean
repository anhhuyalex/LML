/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiSnoc
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
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

/-- **Site exchange for Gibbs means, explicit form.**  Relabelling the couplings by
`g ∘ (pairPerm π).symm` relabels the Gibbs means of the spins: `⟨σ_i⟩_{g ∘ (pairPerm π).symm} =
⟨σ_{π⁻¹ i}⟩_g`. -/
theorem integral_spin_comp_pairPerm (M : ℕ) (β h : ℝ) (π : Equiv.Perm (Fin M))
    (g : FinPairs M → ℝ) (i : Fin M) :
    ∫ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy M β h (g ∘ (pairPerm π).symm))) =
      ∫ σ : Fin M → ℤˣ, ((σ (π.symm i) : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy M β h g)) := by
  rw [integral_count_tilted, integral_count_tilted]
  simp_rw [gibbsWeight_comp_pairPerm β h π (skGibbsEnergy M β h) (fun _ _ => rfl) g]
  have := Equiv.sum_comp (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ))
    (fun τ : Fin M → ℤˣ => Real.exp (skGibbsEnergy M β h g τ) /
      (∑ b, Real.exp (skGibbsEnergy M β h g b)) * ((τ (π.symm i) : ℤ) : ℝ))
  rw [← this]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp

/-- **Site exchange for Gibbs means.**  For every relabelling `π` of the sites there is a measure
preserving map `φ` of the couplings with `⟨σ_i⟩_{φ g} = ⟨σ_{π⁻¹ i}⟩_g`. -/
theorem exists_sk_site_exchange (M : ℕ) (β h : ℝ) (π : Equiv.Perm (Fin M)) :
    ∃ φ : (FinPairs M → ℝ) → (FinPairs M → ℝ),
      MeasurePreserving φ (Measure.pi fun _ : FinPairs M => gaussianReal 0 1)
        (Measure.pi fun _ : FinPairs M => gaussianReal 0 1) ∧
      ∀ (g : FinPairs M → ℝ) (i : Fin M),
        ∫ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy M β h (φ g))) =
          ∫ σ : Fin M → ℤˣ, ((σ (π.symm i) : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy M β h g)) :=
  ⟨fun g => g ∘ (pairPerm π).symm, measurePreserving_comp_pairPerm (gaussianReal 0 1) π,
    integral_spin_comp_pairPerm M β h π⟩

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
    have h1 := Real.sq_sqrt_sub_le_abs_sub hqm.1 hq.1
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
  have h1 : P.map (fun ω => z ω i) = gaussianReal 0 1 :=
    Measure.map_apply_eq_of_map_eq_pi (μ := fun _ : Fin n => gaussianReal 0 1) hz hl i
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
      P P' := (measurePreserving_fst).comp (measurePreserving_skCavityDisorderEquiv N)
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
  -- Gibbs means as abstract measurable bounded functions
  obtain ⟨X, hX⟩ : ∃ X : Fin (N + 1) → (FinPairs (N + 1) → ℝ) → ℝ, ∀ i g, X i g =
      ∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) := ⟨fun i g => _, fun _ _ => rfl⟩
  obtain ⟨Xo, hXo⟩ : ∃ Xo : Fin N → (FinPairs N → ℝ) → ℝ, ∀ i g, Xo i g =
      ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted
        (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g)) := ⟨fun i g => _, fun _ _ => rfl⟩
  have hXm : ∀ i, Measurable (X i) := fun i => by
    rw [show X i = fun g => ∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
      ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) from funext (hX i)]
    exact measurable_integral_spin_skGibbsEnergy (N + 1) β h i
  have hXom : ∀ i, Measurable (Xo i) := fun i => by
    rw [show Xo i = fun g => ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted
      (skGibbsEnergy N (β * Real.sqrt ((N : ℝ) / (N + 1))) h g)) from funext (hXo i)]
    exact measurable_integral_spin_skGibbsEnergy N _ h i
  have hXb : ∀ i g, |X i g| ≤ 1 := fun i g => by rw [hX]; exact abs_integral_spin_le_one _ _
  have hXob : ∀ i g, |Xo i g| ≤ 1 := fun i g => by rw [hXo]; exact abs_integral_spin_le_one _ _
  -- the transported integrals
  obtain ⟨F, hF⟩ : ∃ F : Fin (n + 1) → (FinPairs (N + 1) → ℝ) → ℝ, ∀ j g,
      F j g = (X (π (Fin.castLE hN'.le j)) g - Real.tanh (β * Real.sqrt q * zp g j + h)) ^ 2 :=
    ⟨fun j g => _, fun _ _ => rfl⟩
  have hFm : ∀ j, Measurable (F j) := fun j => by
    rw [show F j = fun g => (X (π (Fin.castLE hN'.le j)) g -
      Real.tanh (β * Real.sqrt q * zp g j + h)) ^ 2 from funext (hF j)]
    exact ((hXm _).sub (Real.continuous_tanh.measurable.comp
      ((((measurable_pi_apply j).comp hzp_meas).const_mul _).add_const h))).pow_const 2
  have hterm : ∀ j : Fin (n + 1), ∫ g, (∫ σ : Fin (N + 1) → ℤˣ,
        ((σ (Fin.castLE hN'.le j) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
      Real.tanh (β * Real.sqrt q * zp (φ g) j + h)) ^ 2 ∂P = ∫ g, F j g ∂P := fun j => by
    have e1 : ∀ g, ∫ σ : Fin (N + 1) → ℤˣ, ((σ (Fin.castLE hN'.le j) : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) = X (π (Fin.castLE hN'.le j)) (φ g) :=
      fun g => by rw [hX, hφX g (π (Fin.castLE hN'.le j)), Equiv.symm_apply_apply]
    have e2 : ∀ g, (∫ σ : Fin (N + 1) → ℤˣ, ((σ (Fin.castLE hN'.le j) : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
        Real.tanh (β * Real.sqrt q * zp (φ g) j + h)) ^ 2 = F j (φ g) := fun g => by
      rw [e1, hF]
    simp_rw [e2]
    have := integral_map hφ.aemeasurable (hFm j).aestronglyMeasurable (μ := P)
    rw [hφ.map_eq] at this
    exact this.symm
  refine ⟨fun g => zp (φ g), hzp_meas.comp hφ.measurable, ?_, ?_⟩
  · rw [show (fun g => zp (φ g)) = zp ∘ φ from rfl, ← Measure.map_map hzp_meas hφ.measurable,
      hφ.map_eq]
    exact hzp_law
  simp_rw [hterm]
  rw [Fin.sum_univ_castSucc]
  -- the last site
  have hlast : ∫ g, F (Fin.last n) g ∂P ≤ Kc / ((N : ℝ) + 1) := by
    refine le_trans (le_of_eq ?_) hznewb
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    rw [hF, hpi_new, hX, hzp_last]
  -- the old sites
  obtain ⟨A, hA⟩ : ∃ A : Fin n → ℝ, ∀ j', A j' = ∫ g' : FinPairs N → ℝ,
      (Xo (Fin.castLE hnN.le j') g' - Real.tanh ((β * Real.sqrt ((N : ℝ) / (N + 1))) *
        Real.sqrt qm * zm g' j' + h)) ^ 2 ∂P' := ⟨fun j' => _, fun _ => rfl⟩
  have hAsum : ∑ j', A j' ≤ Kn / N := by simpa only [hA, hXo] using hzms
  have hgen : ∀ G : (FinPairs N → ℝ) → ℝ, Measurable G →
      ∫ g, G (skCavityDisorderEquiv N g).1 ∂P = ∫ g', G g' ∂P' := fun G hG => by
    rw [← hfst.map_eq, integral_map hfst.aemeasurable hG.aestronglyMeasurable]
  have hold : ∀ j' : Fin n, ∫ g, F (Fin.castSucc j') g ∂P ≤
      3 * (Kb / ((N : ℝ) + 1)) + 3 * A j' + 3 * (1 / ((N : ℝ) + 1)) := fun j' => by
    set c : Fin N := Fin.castLE hnN.le j' with hc
    have hzmj : Measurable fun g' => zm g' j' := (measurable_pi_apply j').comp hzm
    obtain ⟨Tm, hTm⟩ : ∃ Tm : (FinPairs N → ℝ) → ℝ, ∀ g', Tm g' =
        Real.tanh ((β * Real.sqrt ((N : ℝ) / (N + 1))) * Real.sqrt qm * zm g' j' + h) :=
      ⟨fun g' => _, fun _ => rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : (FinPairs N → ℝ) → ℝ, ∀ g', T g' =
        Real.tanh (β * Real.sqrt q * zm g' j' + h) := ⟨fun g' => _, fun _ => rfl⟩
    have hTmm : Measurable Tm := by
      rw [show Tm = fun g' => Real.tanh ((β * Real.sqrt ((N : ℝ) / (N + 1))) * Real.sqrt qm *
        zm g' j' + h) from funext hTm]
      exact Real.continuous_tanh.measurable.comp ((hzmj.const_mul _).add_const h)
    have hTmeas : Measurable T := by
      rw [show T = fun g' => Real.tanh (β * Real.sqrt q * zm g' j' + h) from funext hT]
      exact Real.continuous_tanh.measurable.comp ((hzmj.const_mul _).add_const h)
    have hTb : ∀ g', |T g'| ≤ 1 := fun g' => by rw [hT]; exact (Real.abs_tanh_lt_one _).le
    have hTmb : ∀ g', |Tm g'| ≤ 1 := fun g' => by rw [hTm]; exact (Real.abs_tanh_lt_one _).le
    have hfe : ∀ g, F (Fin.castSucc j') g =
        ((X (Fin.castSucc c) g - Xo c (skCavityDisorderEquiv N g).1) +
          (Xo c (skCavityDisorderEquiv N g).1 - Tm (skCavityDisorderEquiv N g).1) +
          (Tm (skCavityDisorderEquiv N g).1 - T (skCavityDisorderEquiv N g).1)) ^ 2 := fun g => by
      rw [hF, hpi_old, hzp_cs, hT]
      congr 1; ring
    have ha : Integrable (fun g => (X (Fin.castSucc c) g - Xo c (skCavityDisorderEquiv N g).1) ^ 2)
        P := integrable_sq_of_abs_le ((hXm _).sub ((hXom c).comp hfst.measurable)) (C := 2)
          fun g => by
            have := abs_sub (X (Fin.castSucc c) g) (Xo c (skCavityDisorderEquiv N g).1)
            linarith [hXb (Fin.castSucc c) g, hXob c (skCavityDisorderEquiv N g).1]
    have hb : Integrable (fun g => (Xo c (skCavityDisorderEquiv N g).1 -
        Tm (skCavityDisorderEquiv N g).1) ^ 2) P :=
      integrable_sq_of_abs_le (((hXom c).sub hTmm).comp hfst.measurable) (C := 2) fun g => by
        have := abs_sub (Xo c (skCavityDisorderEquiv N g).1) (Tm (skCavityDisorderEquiv N g).1)
        linarith [hXob c (skCavityDisorderEquiv N g).1, hTmb (skCavityDisorderEquiv N g).1]
    have hcc : Integrable (fun g => (Tm (skCavityDisorderEquiv N g).1 -
        T (skCavityDisorderEquiv N g).1) ^ 2) P :=
      integrable_sq_of_abs_le (((hTmm.sub hTmeas)).comp hfst.measurable) (C := 2) fun g => by
        have := abs_sub (Tm (skCavityDisorderEquiv N g).1) (T (skCavityDisorderEquiv N g).1)
        linarith [hTmb (skCavityDisorderEquiv N g).1, hTb (skCavityDisorderEquiv N g).1]
    simp_rw [hfe]
    refine (integral_sq_add_add_le ha hb hcc).trans ?_
    have h1 : ∫ g, (X (Fin.castSucc c) g - Xo c (skCavityDisorderEquiv N g).1) ^ 2 ∂P ≤
        Kb / ((N : ℝ) + 1) := by
      have := hKb β (by rw [abs_of_nonneg hβ0]; exact hββ₀) N hNpos c
      simpa only [hX, hXo] using this
    have h2 : ∫ g, (Xo c (skCavityDisorderEquiv N g).1 - Tm (skCavityDisorderEquiv N g).1) ^ 2
        ∂P = A j' := by
      have hm2 : Measurable fun g' => (Xo c g' - Tm g') ^ 2 := ((hXom c).sub hTmm).pow_const 2
      have := hgen _ hm2
      rw [hA]
      simp only [hTm] at this ⊢
      exact this
    have hzint : Integrable (fun g => zm (skCavityDisorderEquiv N g).1 j' ^ 2) P := by
      have := integrable_sq_coord hzm hzml j'
      exact (integrable_map_measure (hzmj.pow_const 2).aestronglyMeasurable
        hfst.aemeasurable).1 (by rw [hfst.map_eq]; exact this)
    have h3 : ∫ g, (Tm (skCavityDisorderEquiv N g).1 - T (skCavityDisorderEquiv N g).1) ^ 2 ∂P ≤
        1 / ((N : ℝ) + 1) := by
      calc _ ≤ ∫ g, (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm - β * Real.sqrt q) ^ 2 *
            zm (skCavityDisorderEquiv N g).1 j' ^ 2 ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun g => sq_nonneg _) (hzint.const_mul _)
            (ae_of_all _ fun g => by
              change (Tm _ - T _) ^ 2 ≤ _
              rw [hTm, hT]
              have := Real.abs_tanh_sub_tanh_le
                (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm *
                  zm (skCavityDisorderEquiv N g).1 j' + h)
                (β * Real.sqrt q * zm (skCavityDisorderEquiv N g).1 j' + h)
              calc _ ≤ ((β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm *
                    zm (skCavityDisorderEquiv N g).1 j' + h) -
                  (β * Real.sqrt q * zm (skCavityDisorderEquiv N g).1 j' + h)) ^ 2 :=
                  sq_le_sq.mpr (by simpa using this)
                _ = _ := by ring)
        _ = (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm - β * Real.sqrt q) ^ 2 *
            ∫ g, zm (skCavityDisorderEquiv N g).1 j' ^ 2 ∂P := integral_const_mul _ _
        _ = (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm - β * Real.sqrt q) ^ 2 := by
            rw [hgen (fun g' => zm g' j' ^ 2) (hzmj.pow_const 2),
              integral_sq_coord_eq_one hzm hzml j', mul_one]
        _ ≤ _ := hcparam
    rw [h2] at *
    linarith
  -- assemble
  have hsum_old : ∑ j' : Fin n, ∫ g, F (Fin.castSucc j') g ∂P ≤
      n * (3 * (Kb / ((N : ℝ) + 1))) + 3 * (Kn / N) + n * (3 * (1 / ((N : ℝ) + 1))) := by
    calc _ ≤ ∑ j' : Fin n, (3 * (Kb / ((N : ℝ) + 1)) + 3 * A j' + 3 * (1 / ((N : ℝ) + 1))) :=
          Finset.sum_le_sum fun j' _ => hold j'
      _ = n * (3 * (Kb / ((N : ℝ) + 1))) + 3 * ∑ j', A j' + n * (3 * (1 / ((N : ℝ) + 1))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring
      _ ≤ _ := by linarith
  have hKnN : Kn / N ≤ 2 * Kn / ((N : ℝ) + 1) := by
    simpa using div_pow_le_two_pow_mul_div_succ_pow hNpos 1 hKn
  calc _ ≤ (n * (3 * (Kb / ((N : ℝ) + 1))) + 3 * (Kn / N) + n * (3 * (1 / ((N : ℝ) + 1)))) +
        Kc / ((N : ℝ) + 1) := add_le_add hsum_old hlast
    _ ≤ (n * (3 * (Kb / ((N : ℝ) + 1))) + 3 * (2 * Kn / ((N : ℝ) + 1)) +
        n * (3 * (1 / ((N : ℝ) + 1)))) + Kc / ((N : ℝ) + 1) := by gcongr
    _ = (3 * n * Kb + 6 * Kn + 3 * n + Kc) / ((N : ℝ) + 1) := by
        field_simp
        ring
    _ ≤ (3 * n * Kb + 6 * Kn + 3 * n + Kc + 1) / (((N + 1 : ℕ) : ℝ)) := by
        push_cast
        exact div_le_div_of_nonneg_right (by linarith) hN1.le

/-- **Theorem 1.7.1, uniform form (1.190).**  Let `0 ≤ β₀` with `4 β₀² < 1`, `h ∈ ℝ` and `n ∈ ℕ`.
There is `K` (depending on `n, β₀, h` only) such that for all `0 ≤ β ≤ β₀`, every solution `q` of
`q = 𝔼 tanh²(β √q z + h)` and every `N > n` there is a measurable function
`z : (FinPairs N → ℝ) → (Fin n → ℝ)` of the couplings with the i.i.d. standard Gaussian law and
`∑_{i<n} 𝔼(⟨σ_i⟩ - tanh(β z_i √q + h))² ≤ K / N`. -/
theorem sk_local_magnetizations_uniform (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ)
    (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ (N : ℕ) (hN : n < N), ∃ z : (FinPairs N → ℝ) → Fin n → ℝ, Measurable z ∧
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).map z =
          Measure.pi (fun _ : Fin n => gaussianReal 0 1) ∧
        ∑ i : Fin n, ∫ g : FinPairs N → ℝ,
          (∫ σ : Fin N → ℤˣ, ((σ (Fin.castLE hN.le i) : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy N β h g)) -
            Real.tanh (β * Real.sqrt q * z g i + h)) ^ 2
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / N := by
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun β _ _ q _ N hN => ⟨fun _ i => i.elim0, measurable_const, ?_, ?_⟩⟩
    · rw [Measure.pi_of_empty (μ := fun _ : Fin 0 => gaussianReal 0 1), Measure.map_const,
        measure_univ, one_smul]
      congr 1
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      positivity
  | succ n ihn =>
    obtain ⟨Kn, hKn0, ih⟩ := ihn
    exact sk_local_magnetizations_step β₀ hβ₀ hβ₀' h n Kn hKn0.le ih

/-- **Theorem 1.7.1 (Talagrand).**  Let `0 ≤ β` with `4 β² < 1`, `h ∈ ℝ`, `n ∈ ℕ` and `q` a
solution of `q = 𝔼 tanh²(β √q z + h)`.  There is `K` (depending on `n, β, h` only) such that for
every `N > n` there are measurable functions `z_i` of the couplings, independent standard Gaussians,
with `∑_{i<n} 𝔼(⟨σ_i⟩ - tanh(β z_i √q + h))² ≤ K / N`. -/
theorem sk_local_magnetizations_gaussian (β : ℝ) (hβ0 : 0 ≤ β) (hβ : 4 * β ^ 2 < 1) (h q : ℝ)
    (hq : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (hN : n < N), ∃ z : (FinPairs N → ℝ) → Fin n → ℝ,
      Measurable z ∧
      iIndepFun (fun (i : Fin n) (g : FinPairs N → ℝ) => z g i)
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      (∀ i : Fin n, (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).map
        (fun g => z g i) = gaussianReal 0 1) ∧
      ∑ i : Fin n, ∫ g : FinPairs N → ℝ,
        (∫ σ : Fin N → ℤˣ, ((σ (Fin.castLE hN.le i) : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g)) -
          Real.tanh (β * Real.sqrt q * z g i + h)) ^ 2
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / N := by
  obtain ⟨K, hK0, hK⟩ := sk_local_magnetizations_uniform β hβ0 hβ h n
  refine ⟨K, hK0, fun N hN => ?_⟩
  obtain ⟨z, hz, hl, hs⟩ := hK β hβ0 le_rfl q hq N hN
  have hmarg : ∀ i : Fin n, (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).map
      (fun g => z g i) = gaussianReal 0 1 := fun i =>
    Measure.map_apply_eq_of_map_eq_pi (μ := fun _ : Fin n => gaussianReal 0 1) hz hl i
  refine ⟨z, hz, ?_, hmarg, hs⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) (g : FinPairs N → ℝ) => z g i)
    (fun i => ((measurable_pi_apply i).comp hz).aemeasurable)]
  simp_rw [hmarg]
  exact hl

end SpinGlasses
