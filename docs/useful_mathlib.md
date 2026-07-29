# Useful Mathlib Reference

A pedagogical guide to verified Mathlib lemmas and project-specific identities used in the formalization of the Prime Number Theorem. Organized by mathematical domain.

---

## 1. Fourier Analysis & Integration

Lemmas relating to the Fourier transform, measure theory, and the calculus of integrals.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `Real.fourier_real_eq` | `𝓕 f w = ∫ v, 𝐞 (-(v * w)) • f v` | Converting abstract `𝓕` to an explicit integral for calculation | `Mathlib/Analysis/Fourier/FourierTransform.lean` |
| `Circle.norm_smul` | `‖z • v‖ = ‖v‖` for `z ∈ Circle` | Normalizing Fourier transforms involving the circle group | `Mathlib/Analysis/Fourier/FourierTransform.lean` |
| `MeasureTheory.Integrable.fourierInv_fourier_eq` | `∫ 𝓕 f = f 0` | Fourier inversion formula at the origin | `Mathlib/Analysis/Fourier/Inversion.lean` |
| `MeasureTheory.setIntegral_univ` | `∫ x in univ, f x = ∫ x, f x` | Converting restricted integrals to whole-space integrals | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `Complex.norm_ofReal` | `‖↑r‖ = |r|` | Stripping complex norm from a coerced real value. | `Mathlib/Data/Complex/Basic.lean` |
| `Real.norm_of_nonneg` | `0 ≤ x → ‖x‖ = x` | Normalizing real norm to the value itself. | `Mathlib/Analysis/Normed/Field/Basic.lean` |
| `Real.fourierInv_eq` | `𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v` | Integral representation of the inverse Fourier transform on ℝ | `Mathlib/Analysis/Fourier/FourierTransform.lean` |
| `fourier_scale_div_noscalar` | `𝓕 (φ(·/T)) u = T * 𝓕 φ (Tu)` | Scaling property of the Fourier transform | `PrimeNumberTheoremAnd/CH2.lean` |
| `MeasureTheory.integral_Icc_eq_integral_Ioc` | `∫ t in Icc x y, f t = ∫ t in Ioc x y, f t` | Switching between closed and half-open intervals | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `intervalIntegral.integral_comp_div` | `∫ x in a..b, f (x / c) = c • ∫ x in a/c..b/c, f x` | Scaling change of variables in interval integrals | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `intervalIntegral.integral_nonneg` | `a ≤ b → (∀ x ∈ uIcc a b, 0 ≤ f x) → 0 ≤ ∫ x in a..b, f x` | Proving interval integral is non-negative | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` | `Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (𝓝 (∫ x in Ioi a, f x))` | Extending a finite integral to the half-line | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean` |
| `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` | `Tendsto (∫ F i) l (∫ f)` | Dominated Convergence Theorem for limits of integrals | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` |
| `ContinuousOn.aestronglyMeasurable` | `ContinuousOn f s → AEStronglyMeasurable f (μ.restrict s)` | Proving measurability from continuity on a set | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` |
| `Measure.integral_comp_div` | `(∫ x, f (x / a)) = |a| • ∫ y, f y` | Scaling integrals over the whole space | `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean` |
| `Integrable.comp_div` | `Integrable f volume → Integrable (fun x ↦ f (x / c)) volume` | Scaling integrability over the whole space. | `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean` |
| `Measure.setIntegral_comp_smul` | `∫ x in s, f (R • x) ∂μ = |R ^ finrank|⁻¹ • ∫ x in R • s, f x ∂μ` | Scaling restricted (set) integrals. | `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean` |
| `integral_indicator` | `(∫ x, s.indicator f x) = ∫ x in s, f x` | Converting between indicator integrals and set integrals | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `integral_const_mul` | `(∫ x, c * f x) = c * ∫ x, f x` | Factoring constants out of integrals | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.integral_map` | `∫ y, f y ∂ Measure.map φ μ = ∫ x, f (φ x) ∂μ` | Transporting integrals through pushforward measures; especially useful when two random variables have the same law via `Measure.map` equality | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.integral_sub` | `∫ x, (f x - g x) ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ` | Splitting integrals of centered expressions or norm expansions termwise | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.integral_const` | `∫ x, c ∂μ = μ.real Set.univ • c` | Evaluating Bochner integrals of constant functions; on probability measures this simplifies to `c` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.memLp_const` | `MemLp (fun _ ↦ c) p μ` | Supplying `L^p` facts for constant functions under finite/probability measures | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` |
| `MeasureTheory.MemLp.sub` | `MemLp f p μ → MemLp g p μ → MemLp (f - g) p μ` | Building centered `L^p` random variables from sample and mean terms | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` |
| `MeasureTheory.MemLp.integrable` | `1 ≤ q → MemLp f q μ → Integrable f μ` | Turning `L²` hypotheses into Bochner integrability for expectation manipulations | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` |
| `integral_inner` | `∫ x, inner 𝕜 c (f x) ∂μ = inner 𝕜 c (∫ x, f x ∂μ)` | Pulling a constant vector out of an inner-product integral; key in second-moment expansions | `Mathlib/MeasureTheory/Function/L2Space.lean` |
| `ProbabilityTheory.iIndepFun.indepFun` | `iIndepFun f μ → i ≠ j → IndepFun (f i) (f j) μ` | Extracting pairwise independence from an independent family | `Mathlib/Probability/Independence/Basic.lean` |
| `ProbabilityTheory.IndepFun.comp` | `IndepFun f g μ → Measurable φ → Measurable ψ → IndepFun (φ ∘ f) (ψ ∘ g) μ` | Preserving independence after centering, negating, or applying measurable transforms | `Mathlib/Probability/Independence/Basic.lean` |
| `ProbabilityTheory.IndepFun.integral_bilin` | `∫ ω, B (X ω) (Y ω) ∂μ = B (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ)` | Computing expectations of bilinear forms of independent random variables, such as inner products | `Mathlib/Probability/Independence/Integration.lean` |
| `ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` | `μ.real {ω \| ∑ i, X i ω ≥ ε} ≤ exp (-ε^2 / (2 * n * c))` | Hoeffding's inequality for sum of independent sub-Gaussian random variables | `LML/LeanMachineLearning/ForMathlib/Probability/Moments/SubGaussian.lean` |
| `ProbabilityTheory.gaussianReal` | `gaussianReal m v` | The 1D Gaussian measure; forms the marginals of `gaussianInit` | `Mathlib/Probability/Distributions/Gaussian/Basic.lean` |
| `ProbabilityTheory.stdGaussian` | `stdGaussian ℝ E` | The standard isotropic Gaussian measure on a finite-dimensional inner product space | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` |
| `IsGaussian.support` | `(stdGaussian ℝ E).support = univ` | Standard Gaussians have full support | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` |
| `ProbabilityTheory.IsGaussian.map_eq_gaussianReal` | `IsGaussian.map_eq_gaussianReal L` | Proving that the pushforward of a Gaussian measure under a continuous linear map is a 1D Gaussian | `Mathlib/Probability/Distributions/Gaussian/Basic.lean` |
| `ProbabilityTheory.iteratedDeriv_mgf_zero` | `iteratedDeriv n (mgf μ) 0 = moment μ n` | Connects statistical moments directly to the Taylor coefficients of the Moment Generating Function at zero. | `Mathlib/Probability/Moments/Basic.lean` |
| `ProbabilityTheory.mgf_fun_id_gaussianReal` | `mgf (gaussianReal μ v) t = exp (μ * t + v * t^2 / 2)` | Explicit moment generating function of a 1D real Gaussian. | `Mathlib/Probability/Distributions/Gaussian/Real.lean` |
| `jointCumulant_two_eq_covariance` | `jointCumulant μ X = covariance (X 0) (X 1) μ` | Reduces the second joint cumulant directly to the standard covariance definition. | `Project API` (`Cumulant.lean`) |
| `Finpartition.pairingSum_erase` | `∑ P, f P = ∑ B, ∑ P', f (insert B P')` | The crucial recursive step for Wick sums, cleanly separating a specific element and its partner from the rest of the partition sum. | `Project API` (`Finpartition.lean`) |
| `Finset.sum_pair` | `∑ x ∈ {a, b}, f x = f a + f b` | Manually unfolding sums over explicit 2-element sets (e.g. pairings) without Fintype machinery (requires `a ≠ b` via `erase_pair_of_ne`). | `Mathlib/Data/Finset/Basic.lean` |
| `MeasureTheory.measureReal_union_add_inter` | `μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t` | Splitting real-valued measures over sets (avoids dealing with `ENNReal` infinities) | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` |
| `variance_dual_stdGaussian` | `∫ x, ⟪x, w⟫^2 ∂stdGaussian ℝ E = ‖w‖^2` | Instantly computes the variance of a linear functional acting on a standard Gaussian vector, bypassing manual integration | `Project API` |
| `map_pi_eq_stdGaussian` | `Measure.map (EuclideanSpace.equiv ...) (Measure.pi ...) = stdGaussian ℝ E` | Converts a product of 1D independent Gaussians into the canonical `stdGaussian` on `EuclideanSpace` | `Project API` |
| `innerProduct_eq_inner_toLp` | `w ⊙ x = ⟪WithLp.toLp 2 x, WithLp.toLp 2 w⟫` | The critical bridge proving a custom `Finset.sum` inner product is equivalent to Mathlib's `Lp` inner product | `Project API` |
| `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` | `hasSubgaussianMGF_of_mem_Icc h` | Obtaining Hoeffding (sub-Gaussian) bounds for variables bounded in an interval | `Mathlib/Probability/Moments/SubGaussian.lean` |
| `MeasureTheory.measureReal_mono` | `s ⊆ t → μ t ≠ ∞ → μ.real s ≤ μ.real t` | Monotonicity of real-valued measures (unlike `ENNReal`, strictly requires a finiteness proof) | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| `integrableAtFilter_rpow_atTop_iff` | `{s : ℝ} : IntegrableAtFilter (fun x : ℝ ↦ x ^ s) atTop ↔ s < -1` | Characterizing integrability of power functions at infinity | `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` |
| `MeasureTheory.integral_union_ae` | `∫ x in s ∪ t, f x = ∫ x in s, f x + ∫ x in t, f x` | Splitting integrals over disjoint sets (requires AEDisjoint) | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `Set.Iic_union_Ici` | `Iic a ∪ Ici a = univ` | Partitioning the real line for integral decomposition | `Mathlib/Data/Set/Intervals/Basic.lean` |
| `Set.Icc_self` | `Icc a a = {a}` | Converting degenerate intervals to singletons for measure theory | `Mathlib/Data/Set/Intervals/Basic.lean` |
| `MeasureTheory.measure_singleton` | `μ {x} = 0` | Proving points have zero measure (requires `NoAtoms μ`) | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| `MeasureTheory.AEDisjoint` | `AEDisjoint μ s t ↔ μ (s ∩ t) = 0` | Definition of almost-everywhere disjointness | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| `Real.smul_map_volume_mul_left` | `ENNReal.ofReal |a| • map (a • ·) volume = volume` | Scaling of Lebesgue measure on ℝ. Used for negation invariance (a=-1). | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` |
| `MeasurableEquiv.neg` | `MeasurableEquiv Neg.neg` | Negation as a measurable automorphism of an additive group. | `Mathlib/MeasureTheory/Group/MeasurableEquiv.lean` |
| `Filter.map_neg_atTop` | `map neg atTop = atBot` | Relates atTop and atBot under the negation map. | `Mathlib/Order/Filter/AtTopBot/Basic.lean` |
| `MeasurableEmbedding.integrableAtFilter_iff_comap` | `IntegrableAtFilter (f ∘ e) l (μ.comap e)` | Bridge for integrability transfer under filter mapping. | `Mathlib/MeasureTheory/Measure/Comap.lean` |
| `VectorFourier.fourierIntegral_continuous` | `Continuous (𝓕 f)` | Continuity of the Fourier transform for integrable functions. | `Mathlib/Analysis/Fourier/FourierTransform.lean` |
| `Integrable.norm` | `Integrable f μ → Integrable (‖f‖) μ` | Proving integrability of the norm. Essential for ℝ/ℂ boundary. | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` |
| `Integrable.mono_measure` | `Integrable f ν → μ ≤ ν → Integrable f μ` | Transferring integrability to a smaller measure (e.g., restriction). | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` |
| `Measure.restrict_le_self` | `μ.restrict s ≤ μ` | Standard inequality for measure restrictions. | `Mathlib/MeasureTheory/Measure/Restrict.lean` |
| `MeasureTheory.ae_restrict_mem` | `s ∈ (μ.restrict s).ae` | Proof that the set `s` is almost everywhere true for `μ.restrict s`. | `Mathlib/MeasureTheory/Measure/Restrict.lean` |
| `Integrable.integrableOn` | `Integrable f μ → IntegrableOn f s μ` | Proving integrability on a set from global integrability. | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` |
| `MeasureTheory.integral_re` | `(∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ` | Projecting the real part out of an integral (requires integrability). | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.setIntegral_mono_on₀` | `f ≤ g on s → ∫ x in s, f x ≤ ∫ x in s, g x` | Monotonicity of integrals on restricted domains. | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `MeasureTheory.integrable_zero` | `Integrable (fun _ ↦ 0) μ` | Proving the zero function is integrable. | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` |
| `MeasureTheory.integrableOn_exp_mul_Iic` | `IntegrableAtFilter (exp (-λ·)) (Iic u0)` | Integrability of exponential decay on half-lines. | `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` |
| `MeasureTheory.integral_exp_mul_Iic` | `∫ x in Iic u0, exp(-λx) = exp(-λu0)/(-λ)` | Evaluation of the improper exponential integral. | `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` |
| `fourier_integrable_of_rpow_decay` | `Integrable f → Decay(f) → Integrable (𝓕 f)` | Global integrability of the Fourier transform from decay. | `PrimeNumberTheoremAnd/CH2alex.lean` |
| `Continuous.intervalIntegrable` | `Continuous f → ∀ a b, IntervalIntegrable f volume a b` | Proving interval integrability from global continuity **with explicit endpoints**. Unlike `ContinuousOn.intervalIntegrable`, this pins `a` and `b`. | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `intervalIntegral.integral_add_adjacent_intervals` | `IntervalIntegrable f a b → IntervalIntegrable f b c → ∫ x in a..c, f x = ∫ x in a..b, f x + ∫ x in b..c, f x` | Splitting an integral at an intermediate point | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `(∀ t ∈ uIcc a b, HasDerivAt F (f t) t) → IntervalIntegrable f volume a b → ∫ x in a..b, f x = F b - F a` | Fundamental Theorem of Calculus (evaluation form). Polymorphic in `E : CompleteSpace`; pin `E` via `(f := fun t : ℝ ↦ ...)`. **Trick**: to show a quantity `F` is invariant along a flow, it is often easier to show `HasDerivAt F 0 τ` everywhere and apply this lemma with `f' := fun _ => 0` (discharged by `intervalIntegrable_const`) than to compute and integrate `F`'s real, nonzero derivative. | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` |
| `intervalIntegral.integral_hasDerivAt_right` | `IntervalIntegrable f volume a b → StronglyMeasurableAtFilter f (𝓝 b) volume → ContinuousAt f b → HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b` | Fundamental Theorem of Calculus, differentiation-of-the-integral form; works for any Banach-space-valued `f`, not just `ℝ`-valued. | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` |
| `Continuous.stronglyMeasurableAtFilter` | `Continuous f → ∀ (μ : Measure α) (l : Filter α), StronglyMeasurableAtFilter f l μ` | Supplying the measurability side-condition of `intervalIntegral.integral_hasDerivAt_right` directly from continuity. | `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean` |
| `intervalIntegrable_const` | `IntervalIntegrable (fun x => c) μ a b` | Trivial interval-integrability of a constant function; use with `intervalIntegral.integral_eq_sub_of_hasDerivAt` and `f' := fun _ => 0` for the "prove `F` is constant via a zero derivative" pattern. | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `MeasureTheory.Measure.infinitePi` | `Measure (∀ i, α i)` | Constructing an infinite product measure (e.g. over `ℕ`), where standard `Measure.pi` fails due to `Fintype` constraints. | `Mathlib/Probability/ProductMeasure.lean` |
| `MeasurableEmbedding.integral_map` | `∫ x, f x ∂(μ.map g) = ∫ x, f (g x) ∂μ` | Pushing integration through a measurable embedding (cleaner than `MeasureTheory.integral_map`) | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasurableEmbedding.integrable_map_iff` | `Integrable f (Measure.map g μ) ↔ Integrable (f ∘ g) μ` | Proving integrability side-conditions for embeddings | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `MeasureTheory.integral_smul` | `∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ` | Factoring constants out of integrals (use `smul_eq_mul` to bridge real multiplication) | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| `ProbabilityTheory.strong_law_ae` | `Integrable (X 0) μ → Pairwise ((· ⟂ᵢ[μ] ·) on X) → (∀ i, IdentDistrib (X i) (X 0) μ μ) → ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (n:ℝ)⁻¹ • ∑ i ∈ range n, X i ω) atTop (𝓝 μ[X 0])` | Etemadi's strong law of large numbers: only **pairwise** independence needed; works for Banach-space-valued `X`. Conclusion uses `•` and `Finset.range` — bridge with `smul_eq_mul` and `Fin.sum_univ_eq_sum_range` | `Mathlib/Probability/StrongLaw.lean` |
| `ProbabilityTheory.iIndepFun_infinitePi` | `(∀ i, Measurable (X i)) → iIndepFun (fun i ω ↦ X i (ω i)) (Measure.infinitePi P)` | Independence of coordinate-wise functions under an infinite product measure. **Requires `import Mathlib.Probability.Independence.InfinitePi`** — not transitively available from `Mathlib.Probability.ProductMeasure` | `Mathlib/Probability/Independence/InfinitePi.lean` |
| `measurePreserving_eval_infinitePi` | `MeasurePreserving (Function.eval i) (infinitePi μ) (μ i)` | The `i`-th coordinate of an infinite product has law `μ i`. Root namespace; `μ` is an explicit argument | `Mathlib/Probability/ProductMeasure.lean` |
| `MeasureTheory.Measure.infinitePi_map_eval` | `(infinitePi μ).map (fun x ↦ x i) = μ i` | Pushforward form of the coordinate law; input for `IdentDistrib` of coordinates and `integral_map` expectation transfers. `μ` is explicit | `Mathlib/Probability/ProductMeasure.lean` |
| `instance : IsProbabilityMeasure (Measure.infinitePi μ)` | needs `[∀ i, IsProbabilityMeasure (μ i)]` | Infinite products of probability measures are probability measures | `Mathlib/Probability/ProductMeasure.lean` |
| `Measure.pi.instIsProbabilityMeasure` | `[∀ i, IsProbabilityMeasure (μ i)] → IsProbabilityMeasure (Measure.pi μ)` | Finite (Fintype) products of probability measures are probability measures | `Mathlib/MeasureTheory/Constructions/Pi.lean` |
| `instance : IsProbabilityMeasure (gaussianReal μ v)` | unconditional (even for `v = 0`) | Gaussian measures are probability measures | `Mathlib/Probability/Distributions/Gaussian/Real.lean` |
| `ProbabilityTheory.IdentDistrib` | structure with fields `aemeasurable_fst`, `aemeasurable_snd`, `map_eq : μ.map f = ν.map g` | "Same law" of two random variables; build directly via `refine ⟨hf.aemeasurable, hg.aemeasurable, ?_⟩` | `Mathlib/Probability/IdentDistrib.lean` |
| `ProbabilityTheory.IdentDistrib.comp` | `IdentDistrib f g μ ν → Measurable u → IdentDistrib (u ∘ f) (u ∘ g) μ ν` | Transferring identical distribution through a common measurable function (e.g. iid summands `Y (rows i)` built from iid rows) | `Mathlib/Probability/IdentDistrib.lean` |
| `ProbabilityTheory.IdentDistrib.integral_eq` | `IdentDistrib f g μ ν → ∫ x, f x ∂μ = ∫ x, g x ∂ν` | Equating expectations of identically distributed random variables | `Mathlib/Probability/IdentDistrib.lean` |
| `MeasureTheory.Integrable.of_bound` | `[IsFiniteMeasure μ] → AEStronglyMeasurable f μ → (C : ℝ) → (∀ᵐ x ∂μ, ‖f x‖ ≤ C) → Integrable f μ` | Integrability of bounded a.e.-measurable functions on finite/probability spaces; use `Filter.Eventually.of_forall` to supply a pointwise bound | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` |
| `Finset.measurable_sum` | `(∀ i ∈ s, Measurable (f i)) → Measurable fun a ↦ ∑ i ∈ s, f i a` | Measurability of finite sums, e.g. dot products `w ↦ ∑ k, w k * x k`. Generated by `to_additive` from `Finset.measurable_prod` | `Mathlib/MeasureTheory/Group/Arithmetic.lean` |
| `measurable_pi_apply` | `Measurable fun f : Π i, X i ↦ f i` | Coordinate evaluation on Pi types is measurable; base case for row/coordinate measurability | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` |
| `Measurable.indicator` | `Measurable f → MeasurableSet s → Measurable (s.indicator f)` | Measurability of indicator functions, e.g. the ReLU derivative `𝟏[0 ≤ ·]` via `Set.Ici 0` and `measurableSet_Ici` | `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` |
| `Real.norm_eq_abs` | `‖r‖ = \|r\|` for `r : ℝ` | Converting norm bounds into absolute-value bounds (e.g. for `Integrable.of_bound`) | `Mathlib/Analysis/Normed/Group/Real.lean` |

---

## 2. Complex & Meromorphic Analysis

Lemmas for complex-valued functions, analyticity, and pole orders.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `Complex.tanh_eq_sinh_div_cosh` | `tanh z = sinh z / cosh z` | Unfolding `coth z` or `tanh z` to hyperbolic forms | `Mathlib/Analysis/Complex/Trigonometric.lean` |
| `meromorphicOrderAt_mul` | `order (f * g) = order f + order g` | Computing pole/zero orders of products | `Mathlib/Analysis/Meromorphic/Order.lean` |
| `AnalyticAt.of_differentiable_on_punctured_nhds_of_continuousAt` | `DifferentiableOn f (𝓝[≠] z) → ContinuousAt f z → AnalyticAt ℂ f z` | Proving analyticity at a removable singularity | `Mathlib/Analysis/Complex/CauchyIntegral.lean` |
| `HolomorphicOn.vanishesOnRectangle` | `RectangleIntegral f z w = 0` | Establishing rectangle integrals vanish before shifting contours | `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` |
| `deriv_z_coth_z_bounded` | `‖deriv (z * coth z) z‖ ≤ C` | Uniform boundedness of a specific kernel on a strip | `PrimeNumberTheoremAnd/Utils.lean` |
| `analyticOn_deriv_z_coth_z_strip` | `AnalyticOn ℂ (deriv (z * coth z))` | Analyticity on closed strips for Phragmén–Lindelöf | `PrimeNumberTheoremAnd/Utils.lean` |
| `HasDerivAt.slope_tendsto` | `Tendsto (slope f x) (𝓝[≠] x) (𝓝 f')` | Connecting differentiability to difference-quotient limits | `Mathlib/Analysis/Calculus/Deriv/Slope.lean` |
| `ContinuousOn.integrableOn_compact` | `ContinuousOn f s → IsCompact s → IntegrableOn f s` | Proving integrability from continuity on compact domains | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `IsCompact.exists_bound_of_continuousOn` | `IsCompact s → ContinuousOn f s → ∃ M, ∀ x ∈ s, ‖f x‖ ≤ M` | Obtaining a uniform bound for DCT from continuity on a compact set | `Mathlib/Topology/ContinuousOn.lean` |
| `IsCompact.image` | `IsCompact s → Continuous f → IsCompact (f '' s)` | Proving a set is compact by showing it is the continuous image of another compact set | `Mathlib/Topology/IsCompact.lean` |
| `isCompact_Icc.prod` | `IsCompact (Icc a b ×ˢ Icc c d)` | Proving compactness of a product of intervals (e.g., a rectangle in ℂ) | `Mathlib/Topology/IsCompact.lean` |
| `ContinuousOn.mono` | `ContinuousOn f s → t ⊆ s → ContinuousOn f t` | Narrowing the domain of continuity to a subset | `Mathlib/Topology/ContinuousOn.lean` |
| `Complex.add_re` | `(z + w).re = z.re + w.re` | Distributing real-part projection over addition | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.sub_re` | `(z - w).re = z.re - w.re` | Distributing real-part projection over subtraction | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.re_ofReal_mul` | `(↑r * z).re = r * z.re` | Factoring real multipliers out of the real-part projection | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.ofReal_inv` | `↑(x⁻¹) = (↑x)⁻¹` | Moving inversion across the ℝ/ℂ boundary | `Mathlib/Data/Complex/Basic.lean` |
| `MeromorphicAt.fun_sum` | `MeromorphicAt (fun z ↦ ∑ n ∈ s, G n z) x` | Proving finite sum of meromorphic functions is meromorphic (lambda version) | `Mathlib/Analysis/Meromorphic/Basic.lean` |
| `Finset.analyticAt_fun_sum` | `AnalyticAt 𝕜 (fun z ↦ ∑ n ∈ N, f n z) c` | Proving finite sum of analytic functions is analytic (lambda version) | `Mathlib/Analysis/Analytic/Constructions.lean` |
| `starRingEnd_apply` | `starRingEnd ℂ z = conj z` | Unpacking the generic star involution to complex conjugation | `Mathlib/Data/Complex/Basic.lean` |
| `star_def` | `star z = conj z` | Unpacking star notation | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.conj_re` | `(conj z).re = z.re` | Real part of conjugate is unchanged | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.conj_im` | `(conj z).im = -z.im` | Imaginary part of conjugate is negated | `Mathlib/Data/Complex/Basic.lean` |


---

## 3. Limits, Filters & Topology

Filter basis operations, neighborhood properties, and standard limits at infinity.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `isMinOn_iff` | `IsMinOn f s a ↔ ∀ x ∈ s, f a ≤ f x` | Unfolding `IsMinOn` (defined via `IsMinFilter f (𝓟 s) a`) into a usable pointwise statement. **Caution**: `IsMinOn f s a` does *not* itself imply `a ∈ s` — a theorem claiming uniqueness of an "argmin" must add that membership hypothesis explicitly (`∀ y, y ∈ s → IsMinOn f s y → y = a₀`), or the claim can be vacuously/trivially false for a `y` outside `s`. | `Mathlib/Order/Filter/Extr.lean` |
| `EuclideanSpace.equiv` | `EuclideanSpace ℝ (Fin d) ≃ Fin d → ℝ` | Map between EuclideanSpace and functions to manually cast elements like `1` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |
| `WithLp.equiv` | `WithLp p α ≃ α` | Navigating between base types and their $L_p$ topological synonyms. Use `.symm` to cast into the $L_p$ space. | `Mathlib/Analysis/NormedSpace/LpSpace.lean` |
| `Pi.measurableSpace` | `MeasurableSpace (Π i, α i)` | The canonical measurable space on Pi types | `Mathlib/MeasureTheory/Measure/BorelSpace/Basic.lean` |
| `borel` | `[TopologicalSpace X] → MeasurableSpace X` | Generate a MeasurableSpace from a Topology | `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean` |
| `Real.tendsto_exp_atTop` | `Tendsto Real.exp atTop atTop` | Basic exponential limit at infinity | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Filter.tendsto_atTop_mono'` | `f₁ ≤ᶠ f₂ → Tendsto f₁ l atTop → Tendsto f₂ l atTop` | Comparison test for diverging limits | `Mathlib/Order/Filter/AtTopBot/Tendsto.lean` |
| `Filter.Tendsto.atTop_div_const` | `Tendsto f l atTop → Tendsto (f / r) l atTop` | Scaling infinite limits by constants | `Mathlib/Order/Filter/AtTopBot/Field.lean` |
| `Filter.tendsto_pow_atTop` | `n ≠ 0 → Tendsto (x ^ n) atTop atTop` | Divergence of power functions | `Mathlib/Order/Filter/AtTopBot/Field.lean` |
| `Filter.tendsto_atTop_add_const_right` | `Tendsto (f + c) atTop atTop` | Shifting infinite limits by constants | `Mathlib/Order/Filter/AtTopBot/Basic.lean` |
| `Filter.HasBasis.inf_principal` | `(f ⊓ principal s).HasBasis` | Intersecting a basis with a specific set (neighborhood within) | `Mathlib/Order/Filter/Basis.lean` |
| `Filter.HasBasis.comap` | `(comap f l).HasBasis` | Lifting neighborhood bases through functions | `Mathlib/Order/Filter/Basis.lean` |
| `Filter.Eventually.of_forall` | `(∀ x, P x) → ∀ᶠ x in l, P x` | Converting universal properties to filter eventually-true | `Mathlib/Order/Filter/Basic.lean` |
| `Metric.exists_isBounded_image_of_tendsto` | `Tendsto f l (nhds x) → ∃ S ∈ l, IsBounded (f '' S)` | Proving a function is eventually bounded near its limit | `Mathlib/Analysis/NormedSpace/Basic.lean` |
| `isBounded_iff_forall_norm_le` | `IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C` | Standard characterization of bounded sets | `Mathlib/Analysis/NormedSpace/Basic.lean` |
| `Complex.closure_preimage_im` | `closure (im ⁻¹' s) = im ⁻¹' closure s` | Relating strip closures to interval closures in ℝ | `Mathlib/Analysis/Complex/ReImTopology.lean` |
| `closure_Ioo` | `closure (Ioo a b) = Icc a b` | Closing open intervals in metric spaces | `Mathlib/Topology/MetricSpace/Basic.lean` |
| `isOpen_lt` | `IsOpen {x | f x < g x}` | Topology of regions defined by continuous inequalities | `Mathlib/Topology/MetricSpace/Basic.lean` |
| `Set.Ioo_subset_Icc_self` | `Ioo a b ⊆ Icc a b` | Basic interval containment | `Mathlib/Data/Set/Intervals/Basic.lean` |
| `Set.mem_Icc` | `x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b` | Unpacking interval membership to a conjunction for order tactics | `Mathlib/Data/Set/Intervals/Basic.lean` |
| `Icc_mem_nhdsGT` | `a < b → Icc a b ∈ 𝓝[>] a` | Constructing neighborhood bases for `nhdsWithin` | `Mathlib/Topology/Order/OrderClosed.lean` |
| `tendsto_nhdsWithin_of_tendsto_nhds` | `Tendsto f l (nhds x) → Tendsto f (nhdsWithin x s) (nhds x)` | Bridging restricted limits to full neighborhood limits | `Mathlib/Order/Filter/Basic.lean` |
| `tendsto_sub_nhds_zero_iff` | `Tendsto f l (nhds a) ↔ Tendsto (f - a) l (nhds 0)` | Centering a limit at zero for algebraic simplicity | `Mathlib/Topology/Algebra/Group/Basic.lean` |
| `Complex.continuous_ofReal` | `Continuous (ofReal : ℝ → ℂ)` | Essential bridge for coercions in continuity proofs | `Mathlib/Data/Complex/Basic.lean` |
| `Real.continuous_exp` | `Continuous Real.exp` | Continuity of the real exponential | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `continuous_finset_sum` | `(∀ i ∈ s, Continuous (f i)) → Continuous (fun x ↦ ∑ i ∈ s, f i x)` | Continuity of finite sums of functions | `Mathlib/Topology/Algebra/Group/Basic.lean` |
| `Continuous.log` | `Continuous f → (∀ x, f x ≠ 0) → Continuous (fun x ↦ log (f x))` | Continuity of compositions with `Real.log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Continuous.rpow` | `Continuous f → Continuous g → (∀ x, f x ≠ 0 ∨ 0 < g x) → Continuous (fun x ↦ f x ^ g x)` | Continuity of real power functions | `Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean` |
| `Filter.Eventually.exists` | `Eventually p f → [NeBot f] → ∃ x, p x` | Extracting a witness from an eventually-true predicate | `Mathlib/Order/Filter/Basic.lean` |
| `self_mem_nhdsWithin` | `s ∈ 𝓝[s] a` | Proving a set is a member of its own neighborhood-within filter | `Mathlib/Topology/NhdsWithin.lean` |
| `nhdsWithin_Ioi_neBot` | `a ≤ b → NeBot (𝓝[Ioi a] b)` | Proving that a right-neighborhood within filter is non-empty | `Mathlib/Topology/Order/DenselyOrdered.lean` |
| `LipschitzWith.dist_le_mul` | `LipschitzWith K f → dist (f x) (f y) ≤ K * dist x y` | Applying a Lipschitz bound to a distance metric | `Mathlib/Topology/MetricSpace/Lipschitz.lean` |
| `Real.dist_eq` | `dist x y = |x - y|` | Translating generic metric distance to real absolute values | `Mathlib/Data/Real/Basic.lean` |
| `Filter.Tendsto.const_mul` | `Tendsto f l (𝓝 a) → Tendsto (fun x ↦ b * f x) l (𝓝 (b * a))` | Multiplying a convergent sequence by a constant (e.g. the `xᵀx'` factor in kernel limits). **The constant `b` is the first explicit argument**: `h.const_mul b` | `Mathlib/Topology/Algebra/Monoid/Defs.lean` |


---

## 4. Asymptotics & Growth Bounds

Lemmas for `IsBigO` notation and analytic growth estimates.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `Asymptotics.isBigO_congr` | `f₁ =ᶠ f₂ → g₁ =ᶠ g₂ → (f₁ =O g₁ ↔ f₂ =O g₂)` | Substituting equivalent functions in asymptotic bounds | `Mathlib/Asymptotics/Asymptotics.lean` |
| `isBigO_refl` | `f =O f` | Trivial identity for asymptotic comparisons | `Mathlib/Asymptotics/Asymptotics.lean` |
| `Real.log_le_rpow_div` | `log n ≤ n^p / p` | Bounding logarithmic growth by polynomial growth | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |

---

## 5. Set Theory, Finiteness & Subtypes

Interop between `ℕ`, `ℕ+`, and other discrete types.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `OrderIso.pnatIsoNat` | `ℕ+ ≃o ℕ` | Transferring properties between positive and standard naturals | `Mathlib/Data/PNat/Basic.lean` |
| `Set.finite_lt_nat` | `{m | m < n}.Finite` | Proving finiteness of discrete intervals | `Mathlib/Data/Nat/Interval.lean` |
| `Set.injOn_subtype_val` | `InjOn Subtype.val s` | Injectivity of the coercion from subtypes | `Mathlib/Data/Set/Function.lean` |
| `Set.Finite.of_finite_image` | `(f '' s).Finite → InjOn f s → s.Finite` | Proving finiteness from an injective mapping | `Mathlib/Data/Set/Finite/Basic.lean` |
| `Nat.floor_lt` | `⌊x⌋₊ < n ↔ x < n` | Converting floor inequalities to real inequalities | `Mathlib/Analysis/Algebra/Floor.lean` |
| `PNat.lt_add_right` | `n < n + k` | Proving strict inequalities for shifted positive naturals | `Mathlib/Data/PNat/Basic.lean` |
| `not_le.mp` | `¬(n ≤ x) → x < n` | Logic for strict order from negated weak order | `Mathlib/Order/Basic.lean` |
| `Nat.floor_pos` | `0 < ⌊x⌋₊ ↔ 1 ≤ x` | Witnessing that a floor is positive if the real value is at least 1 | `Mathlib/Analysis/Algebra/Floor.lean` |
| `Nat.le_floor` | `n ≤ ⌊x⌋₊ ↔ n ≤ x` | Converting floor inequalities to real inequalities | `Mathlib/Analysis/Algebra/Floor.lean` |
| `LinearOrderedField.smul_Ici` | `r • Ici a = Ici (r * a)` | Scaling half-infinite intervals by a positive scalar | `Mathlib/Algebra/Order/Field/Pointwise.lean` |
| `finrank_self` | `finrank R R = 1` | Standard dimension of a field over itself | `Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean` |
| `Algebra.smul_def` | `r • x = algebraMap R A r * x` | Bridging scalar and field multiplication | `Mathlib/Algebra/Algebra/Basic.lean` |
| `Fin.ext_iff` | `i = j ↔ i.val = j.val` | Rewriting `Fin` equalities into arithmetic equalities, or proving index equality by value | `Mathlib/Data/Fin/Basic.lean` |
| `congrArg Fin.val` | `h : i = j ⟹ i.val = j.val` | Extracting a `Nat` equality from a `Fin` equality before feeding it to `omega` | `Lean Core (Init/Prelude)` |
| `List.getLast_mem` | `{l : List α} (h : l ≠ []) : l.getLast h ∈ l` | Proving that the last element of a non-empty list belongs to the list | `Lean Core (Init.Data.List.Basic)` |
| `List.getD_eq_getElem` | `as.getD n d = as[n]` | Rewriting `List.getD` to standard `List.getElem` when index is within bounds | `Mathlib/Data/List/Basic.lean` |
| `List.getElem_zero_cons` | `(x :: xs)[0] = x` | Evaluating standard list lookup at index 0 | `Lean Core (Init.Data.List.Basic)` |
| `List.getElem_succ_cons` | `(x :: xs)[i + 1] = xs[i]` | Evaluating standard list lookup at index i + 1 | `Lean Core (Init.Data.List.Basic)` |
| `List.cons_append` | `(x :: xs) ++ ys = x :: (xs ++ ys)` | Evaluating list concatenation recursively | `Lean Core (Init.Data.List.Basic)` |
| `Finset.sum_erase_add` | `∑ x ∈ s.erase k, f x + f k = ∑ x ∈ s, f x` | Isolating a specific term from a sum over a Finset | `Mathlib/Data/Finset/Basic.lean` |
| `Fintype.not_linearIndependent_iff` | `¬LinearIndependent ℝ f ↔ ∃ c, ∑ i, c i • f i = 0 ∧ ∃ i, c i ≠ 0` | Converting linear dependence to an explicit nontrivial sum | `Mathlib/LinearAlgebra/LinearIndependent.lean` |
| `List.nil_append` | `[] ++ ys = ys` | Evaluating list concatenation base case | `Lean Core (Init.Data.List.Basic)` |
| `Set.uIcc_of_le` | `a ≤ b → Set.uIcc a b = Set.Icc a b` | Normalizing `[[a, b]]` to `Icc a b` when the order is known. Essential before `Set.mem_Icc`. | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` |
| `Set.mem_uIcc` | `x ∈ Set.uIcc a b ↔ (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)` | Membership in `[[a, b]]`; note it gives a **disjunction**, not a conjunction. | `Mathlib/Order/Interval/Set/UnorderedInterval.lean` |
| `EReal.coe_le_coe_iff` | `((x : EReal) ≤ (y : EReal)) ↔ x ≤ y` | Moving inequalities back and forth between `ℝ` and `EReal` in partition arguments | `Mathlib/Data/EReal/Basic.lean` |
| `Finset.mem_coe` | `x ∈ ↑s ↔ x ∈ s` | Bridging set-coerced finset membership to standard finset membership | `Mathlib/Data/Finset/Basic.lean` |
| `Set.Finite.coe_toFinset` | `↑(hs.toFinset) = s` | Identifying the set-coerced finite-to-finset term with the original set | `Mathlib/Data/Set/Finite/Basic.lean` |
| `Set.Finite.mem_toFinset` | `x ∈ s.toFinset ↔ x ∈ s` | Converting membership in a finite-to-finset term to original set membership | `Mathlib/Data/Set/Finite/Basic.lean` |
| `Fin.addCases` | `induction j using Fin.addCases with | left i => ... | right i => ...` | The structural induction principle for case-splitting an index $j \in \text{Fin}(n_1 + n_2)$ into its left and right components | `Mathlib/Data/Fin/Basic.lean` |
| `measurableEmbedding_prod_mk_right` | `MeasurableEmbedding (fun x ↦ (x, c))` | Mapping between a space and a tagged disjoint space | `Mathlib/MeasureTheory/Constructions/Prod/Basic.lean` |
| `Measurable.prodMk` | `Measurable f → Measurable g → Measurable (fun x ↦ (f x, g x))` | Constructing a measurable tuple mapping (camelCase in Lean 4) | `Mathlib/MeasureTheory/Constructions/Prod/Basic.lean` |
| `Sum.elim` | `Sum.elim f g (Sum.inl x) = f x` | The canonical way to map over a disjoint union `ι ⊕ ι`. | `Lean Core (Init.Data.Sum.Basic)` |
| `Equiv.symm_apply_apply` | `e.symm (e x) = x` | The absolute core lemma for canceling nested equivalences (and its sibling `apply_symm_apply`). | `Mathlib/Logic/Equiv/Defs.lean` |
| `Equiv.toEmbedding_apply` | `e.toEmbedding x = e x` | Critical for reducing the `.toEmbedding` field back to standard function application so that equivalence lemmas can match. | `Mathlib/Logic/Equiv/Defs.lean` |
| `Equiv.finsetCongr_apply` | `e.finsetCongr s = s.map e.toEmbedding` | Bridges the gap between the `finsetCongr` equivalence and the underlying `Finset.map` operation. | `Mathlib/Data/Finset/Equiv.lean` |
| `Finset.prod_congr` | `s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → ∏ x ∈ s₁, f x = ∏ x ∈ s₂, g x` | Essential for rewriting terms inside the binders of product operators (and its sibling `sum_congr`). | `Mathlib/Algebra/BigOperators/Group/Finset.lean` |



---

## 6. Arithmetic, Inequalities & Powers

Core order lemmas and special function identities.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `Real.rpow_neg` | `x ^ (-y) = (x ^ y)⁻¹` | Bridging `field_simp` and real power functions | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.exp_le_one_iff` | `exp x ≤ 1 ↔ x ≤ 0` | Common bound for exponential terms | `Mathlib/Analysis/Complex/Exponential.lean` |
| `Real.sinh_eq` | `sinh x = (exp x - exp (-x)) / 2` | Unfolding hyperbolic sine | `Mathlib/Analysis/Complex/Trigonometric.lean` |
| `inner_sub_right` | `⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫` | Expanding inner products over subtraction | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `inner_add_left` | `⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫` | Expanding inner products over addition | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `real_inner_comm` | `⟪x, y⟫ = ⟪y, x⟫` | Commuting real inner products | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `add_sub_cancel_left` | `(x + y) - x = y` | Cancelling terms in vector spaces | `Mathlib/Algebra/Group/Basic.lean` |
| `mul_nonneg` | `0 ≤ x → 0 ≤ y → 0 ≤ x * y` | Proving product of non-negative reals is non-negative | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `Complex.sq_norm` | `‖z‖^2 = normSq z` | Relating complex norm to algebraic components | `Mathlib/Analysis/Complex/Basic.lean` |
| `div_le_iff₀` | `0 < c → (a / c ≤ b ↔ a ≤ b * c)` | Clearing positive denominators in inequalities (Mathlib4 standard) | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean` |
| `div_le_one₀` | `x / y ≤ 1 ↔ x ≤ y` | Order lemma for ratios (requires `0 < y`) | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean` |
| `div_le_one` | `x / y ≤ 1 ↔ x ≤ y` | Variant for non-zero denominators in fields | `Mathlib/Algebra/Order/Field/Basic.lean` |
| `norm_pos_iff` | `0 < ‖z‖ ↔ z ≠ 0` | Non-negativity of norms | `Mathlib/Analysis/Complex/Basic.lean` |
| `Complex.im_apply` | `im z = z.im` | Mapping complex field projections to dot notation | `Mathlib/Data/Complex/Basic.lean` |
| `Complex.abs_re_le_norm` | `|z.re| ≤ ‖z‖` | Estimating the size of real parts | `Mathlib/Analysis/Complex/Basic.lean` |
| `Real.pi_pos` | `0 < π` | Mandatory witness for order tactics with `π` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean` |
| `Real.exp_one_gt_two` | `2 < exp 1` | Proving exp 1 is greater than 2 | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `inv_le_inv₀` | `a⁻¹ ≤ b⁻¹ ↔ b ≤ a` | Inverting inequalities in ordered fields | `Mathlib/Algebra/Order/Field/Basic.lean` |
| `inv_nonneg` | `0 ≤ x⁻¹ ↔ 0 ≤ x` | Non-negativity of inverses | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean` |
| `mul_pos_iff_of_pos_left` | `0 < a → (0 < a * b ↔ 0 < b)` | Positivity of products with a known positive factor | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `pos_of_mul_pos_left` | `0 < a * b → 0 ≤ a → 0 < b` | Extracting positivity from product hypotheses | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `continuousAt_const_rpow` | `a ≠ 0 → ContinuousAt (a ^ ·) b` | Proving continuity of real power functions with constant base | `Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean` |
| `Real.rpow_nonneg` | `0 ≤ x → 0 ≤ x ^ y` | Non-negativity of real power functions | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_pos_of_pos` | `0 < x → 0 < x ^ y` | Strict positivity of real power functions | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `inv_rpow` | `(x⁻¹) ^ y = (x ^ y)⁻¹` | Moving inversion inside real power functions | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `mul_le_mul_of_nonneg_left` | `b ≤ c → 0 ≤ a → a * b ≤ a * c` | Explicit constant multiplication in inequalities | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `abs_one` | `|1| = 1` | Normalizing unit absolute values | `Mathlib/Analysis/NormedSpace/Basic.lean` |
| `one_rpow` | `1 ^ x = 1` | Simplifying real powers of 1 | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `div_one` | `x / 1 = x` | Standard field simplification | `Mathlib/Algebra/Field/Basic.lean` |
| `Complex.ofReal_inv` | `↑(x⁻¹) = (↑x)⁻¹` | Moving inversion across the ℝ/ℂ boundary | `Mathlib/Data/Complex/Basic.lean` |
| `Real.ofReal_inv` | `↑(x⁻¹) = (↑x)⁻¹` | Moving inversion across the ℝ/ℂ boundary | `Mathlib/Data/Complex/Basic.lean` |
| `neg_pos` | `0 < -a ↔ a < 0` | Lemma for sign-flipping inequalities. | `Mathlib/Algebra/Order/Group/Defs.lean` |
| `mul_nonpos_of_nonpos_of_nonneg` | `a ≤ 0 → 0 ≤ b → a * b ≤ 0` | Order lemma for products of mixed signs. | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `eq_sub_iff_add_eq` | `a = b - c ↔ a + c = b` | **Mandatory bridge** for `rw` when goal has subtraction but lemma has addition | `Mathlib.Algebra.Group.Basic` |
| `add_comm` | `a + b = b + a` | Commuting terms to match lemma patterns (Rule 207 bridge) | `Mathlib.Algebra.Group.Basic` |
| `add_div` | `(a + b) / c = a / c + b / c` | Distributing division over addition | `Mathlib/Algebra/Field/Basic.lean` |
| `Real.rpow_add` | `x ^ (a + b) = x ^ a * x ^ b` | Unifying real powers (requires `0 < x`) | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_sub_one` | `x ^ (a - 1) = x ^ a / x` | Shifting real powers by 1 | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_one` | `x ^ 1 = x` | Simplifying real power of 1 | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.exp_log` | `exp (log x) = x` | Bypassing transcendental functions (requires `0 < x`). | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.log_le_log` | `0 < x → x ≤ y → log x ≤ log y` | Turning a lower bound on positive reals into a lower bound on logarithms | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.exp_lt_exp` | `exp x < exp y ↔ x < y` | Converting strict exponential inequalities into linear inequalities on the exponents | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Real.exp_le_exp` | `exp x ≤ exp y ↔ x ≤ y` | Converting weak exponential inequalities into linear inequalities on the exponents | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Real.log_rpow` | `log (x ^ y) = y * log x` | Moving exponents out of logarithms (requires `0 < x`). | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `nonpos_of_mul_nonneg_right` | `0 ≤ a * b → a < 0 → b ≤ 0` | Deducing sign of the **right** factor when the **left** is negative | `Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean` |
| `log_le_log_iff` | `log x ≤ log y ↔ x ≤ y` | Equivalence for log inequalities (supports `.mp` projection) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.log_div` | `x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y` | Splitting a log-of-ratio into a difference of logs (needs both numerator and denominator nonzero — does **not** hold unconditionally since `Real.log 0 = 0` by junk-value convention) | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.log_le_sub_one_of_pos` | `0 < x → log x ≤ x - 1` | The standard log-concavity bound; the base case behind Gibbs'/relative-entropy inequalities | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.one_sub_inv_le_log_of_pos` | `0 < x → 1 - x⁻¹ ≤ log x` | Reciprocal-shifted form of `log_le_sub_one_of_pos`; setting `x := a / b` directly gives `a * log (a / b) ≥ a - b` after multiplying by `a > 0`, the core step of a Bregman-divergence-nonnegativity (Gibbs') proof | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `InformationTheory.klFun` | `klFun x = x * log x + 1 - x` | Mathlib's Kullback-Leibler generator function on `ℝ`; `a * log (a / b) - a + b = b * klFun (a / b)` for `b ≠ 0`, so any "unnormalized relative entropy" coordinate term can be reduced to `klFun` and reuse its ready-made nonnegativity/equality-case API instead of re-deriving Gibbs' inequality | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` |
| `InformationTheory.klFun_nonneg` | `0 ≤ x → 0 ≤ klFun x` | Nonnegativity of the KL generator, built from `strictConvexOn_klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` |
| `InformationTheory.klFun_eq_zero_iff` | `0 ≤ x → (klFun x = 0 ↔ x = 1)` | The equality case of `klFun_nonneg`; gives the "divergence is zero iff points coincide" direction of a Bregman/relative-entropy uniqueness argument for free | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` |
| `InformationTheory.strictConvexOn_klFun` | `StrictConvexOn ℝ (Set.Ici 0) klFun` | Strict convexity underlying `klFun_nonneg`/`klFun_eq_zero_iff`; rarely needed directly since the two consequences above already cover the common use cases | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` |
| `mul_pow_sub_one` | `y * y ^ (k - 1) = y ^ k` | Unifying powers for nat subtraction (requires `k ≠ 0` and real `y`) | `Mathlib/Algebra/GroupPower/Lemmas.lean` |
| `Nat.one_le_cast` | `1 ≤ (n : α) ↔ 1 ≤ n` | Casting integer/natural number inequalities to ordered semirings/fields | `Mathlib/Data/Nat/Cast/Order.lean` |
| `slope_pos_iff_of_le` | `x ≤ y → (0 < slope f x y ↔ f x < f y)` | Relating the positivity of a secant slope to strict function growth | `Mathlib/LinearAlgebra/AffineSpace/Slope.lean` |
| `Real.sqrt_one` | `Real.sqrt 1 = 1` | Simplifying `√1`; essential before `norm_num` or `interval_decide` on expressions containing `√1`. | `Mathlib/Data/Real/Sqrt.lean` |
| `Real.sqrt_nonneg` | `0 ≤ Real.sqrt x` | Non-negativity of real square root; needed as explicit side condition for `gcongr` on products involving `sqrt`. | `Mathlib/Data/Real/Sqrt.lean` |
| `Real.sqrt_le_sqrt` | `(h : x ≤ y) : Real.sqrt x ≤ Real.sqrt y` | Monotonicity of square root; used to chain `√(log 2) ≤ √u` from `log 2 ≤ u`. | `Mathlib/Data/Real/Sqrt.lean` |
| `intervalIntegral.integral_same` | `∫ x in a..a, f x = 0` | Integral over empty bounds is zero | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` |
| `Real.log_exp` | `log (exp x) = x` | Simplifying composite log-exp transcendental terms | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.exp_le_exp` | `exp x ≤ exp y ↔ x ≤ y` | Simplifying exponential weak inequalities | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Real.exp_lt_exp` | `exp x < exp y ↔ x < y` | Simplifying exponential strict inequalities | `Mathlib/Analysis/SpecialFunctions/Exp.lean` |
| `Real.sqrt_eq_rpow` | `Real.sqrt x = x ^ (1 / 2)` | Unconditionally converting square roots to real powers for algebraic unification | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_mul` | `(x ^ y) ^ z = x ^ (y * z)` | Unfolding nested exponents (strictly requires `0 ≤ x`) | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.mul_rpow` | `(x * y) ^ z = x ^ z * y ^ z` | Distributing powers over multiplication (requires `0 ≤ x` and `0 ≤ y`) | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_le_rpow_of_exponent_le` | `1 ≤ x → y ≤ z → x ^ y ≤ x ^ z` | Monotonicity of exponents | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `one_div` | `1 / x = x⁻¹` | Converting between fractions and inverses (often used backward `← one_div`) | `Mathlib/Algebra/Field/Basic.lean` |
| `Finset.sum_eq_zero_iff_of_nonneg` | `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)` | Deducing that individual terms are zero if a sum of non-negative terms is zero | `Mathlib/Algebra/BigOperators/Group/Finset.lean` |
| `add_le_add` | `a ≤ b → c ≤ d → a + c ≤ b + d` | Fundamental monotonicity for addition, much safer than directional variants | `Mathlib/Algebra/Order/Group/Defs.lean` |
| `Real.div_rpow` | `(x / y) ^ z = x ^ z / y ^ z` | Distributing powers over division | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.rpow_neg` | `x ^ (-y) = (x ^ y)⁻¹` | Rewriting negative exponents to division | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Real.sqrt_sq` | `0 ≤ x → √(x ^ 2) = x` | Simplifying square root of squares | `Mathlib/Data/Real/Sqrt.lean` |
| `not_lt` | `¬a < b ↔ b ≤ a` | Converting negated strict inequalities to weak inequalities (and vice-versa) for general orders | `Mathlib/Order/Basic.lean` |
| `not_le` | `¬a ≤ b ↔ b < a` | Converting negated weak inequalities to strict inequalities (and vice-versa) for general orders | `Mathlib/Order/Basic.lean` |
| `Real.lipschitzWith_cos` | `LipschitzWith 1 Real.cos` | Using the Lipschitz property of the cosine function | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean` |
| `abs_of_pos` | `0 < x → |x| = x` | Removing absolute value when the term is strictly positive | `Mathlib/Algebra/Order/Group/Abs.lean` |
| `lt_of_le_of_ne` | `a ≤ b → a ≠ b → a < b` | Proving strict inequality from weak inequality and non-equality | `Mathlib/Order/Basic.lean` |
| `LE.le.lt_or_eq` | `a ≤ b → a < b ∨ a = b` | Case-splitting a nonstrict inequality; disjunct order is `lt` first, `eq` second (the opposite of the tempting-but-nonexistent `eq_or_gt`) | `Mathlib/Order/Basic.lean` |
| `mul_self_nonneg` | `0 ≤ x * x` | Explicit proof that $x^2 \ge 0$ when written as a raw product, bypassing the syntactic limits of `positivity` | `Mathlib/Algebra/Order/Ring/Defs.lean` |
| `Real.arccos_le_pi` | `Real.arccos x ≤ π` | Standard upper bound on the arccosine function | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arccos.lean` |
| `innerₗ` | `innerₗ H : H →ₗ[ℝ] H →ₗ[ℝ] ℝ` | The real inner product bundled as a bilinear map; the right input to `ProbabilityTheory.IndepFun.integral_bilin` | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `innerSL` | `innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜` | The continuous sesquilinear inner-product map; useful when continuous linear-map structure is required | `Mathlib/Analysis/InnerProductSpace/LinearMap.lean` |
| `real_inner_self_eq_norm_sq` | `inner ℝ x x = ‖x‖ ^ 2` | Rewriting Hilbert-space norm squares into inner products for finite-sum expansions | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `real_inner_comm` | `inner x y = inner y x` | Commutativity of the real inner product (use via `rw` to avoid strict signature issues) | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `norm_sub_sq_real` | `‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2` | Expanding centered second moments in real inner-product spaces | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `inner_zero_right` | `inner 𝕜 x (0 : E) = 0` | Closing an inner product against the zero vector, e.g. after rewriting a feasibility constraint `matVec M z - matVec M x = 0` into an inner-product cross term | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `sum_inner` | `inner 𝕜 (∑ i ∈ s, f i) x = ∑ i ∈ s, inner 𝕜 (f i) x` | Expanding the left side of an inner product of a finite sum | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `inner_sum` | `inner 𝕜 x (∑ i ∈ s, f i) = ∑ i ∈ s, inner 𝕜 x (f i)` | Expanding the right side of an inner product of a finite sum | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `PiLp.inner_apply` | `inner x y = ∑ i, inner (x i) (y i)` | Expanding the inner product on `EuclideanSpace` or `PiLp` to a sum of component inner products | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |
| `Real.inner_apply` | `inner (a : ℝ) (b : ℝ) = a * b` | Converting generic component-wise inner products on reals to standard multiplication | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `EuclideanSpace.inner_eq_star_dotProduct` | `inner x y = star x ⬝ᵥ y` | Bridging functional inner products to matrix dot products | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |
| `inv_mul_cancel₀` | `a ≠ 0 → a⁻¹ * a = 1` | Elegantly cancelling multiplicative inverses | `Mathlib/Algebra/GroupWithZero/Basic.lean` |
| `neg_one_mul` | `-1 * a = -a` | Manipulating minus signs inside products or integrals | `Mathlib/Algebra/Ring/Basic.lean` |
| `neg_mul` | `-(a * b) = (-a) * b` | Moving negations inside products | `Mathlib/Algebra/Ring/Basic.lean` |
| `linear_combination` (tactic) | Closes a `CommRing`/`Field` goal that equals a scalar multiple/sum of known equality hypotheses, e.g. `linear_combination (1/4:ℝ) * h` closes `A/4 - B/4 - C/4 = D/4` given `h : A - B - C = D`. | More robust than `linarith [h]`/manual `rw` for "goal is `c` times a known nonlinear identity" situations, since it does not require the goal's subterms to already be syntactically bracketed to match `h`'s atoms — it normalizes both sides with `ring` after subtracting the linear combination. | `Mathlib/Tactic/LinearCombination.lean` |
| `exists_hasDerivAt_eq_slope` | `∃ c ∈ Ioo a b, HasDerivAt f (slope f a b) c` | The Mean Value Theorem for functions on ℝ; indispensable for avoiding integrals. | `Mathlib/Analysis/Calculus/MeanValue.lean` |
| `norm_le_pi_norm` | `‖f i‖ ≤ ‖f‖` | Bounding an individual coordinate by the full Lp norm (e.g. for EuclideanSpace) | `Mathlib/Analysis/NormedSpace/PiLp.lean` |
| `HasDerivAt.sub` | `HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (f - g) (f' - g') x` | Computing derivatives of differences term-by-term. Its conclusion is stated as `Pi.sub f g`, but this unfolds *definitionally* to `fun y => f y - g y`, so `exact`/`rw` still close goals stated in the eta-expanded lambda form — no `convert` needed when chaining `.sub`/`.add`. | `Mathlib/Analysis/Calculus/Deriv/Add.lean` |
| `HasDerivAt.smul_const` | `HasDerivAt f f' x → HasDerivAt (fun y => f y • c) (f' • c) x` | Differentiating a curve scaled by a constant vector, e.g. `fun τ => τ • r`. Applied to `hasDerivAt_id`, the result is stated through `id` and an unreduced `1 • c`/`0 • c`; wrap with `simpa using ...` rather than `exact`. | `Mathlib/Analysis/Calculus/Deriv/Mul.lean` |
| `HasDerivAt.const_mul` | `HasDerivAt f f' x → HasDerivAt (fun x ↦ c * f x) (c * f') x` | Factoring constants out of derivatives. | `Mathlib/Analysis/Calculus/Deriv/Mul.lean` |
| `hasDerivAt_pow` | `HasDerivAt (fun x ↦ x ^ n) (n * x ^ (n - 1)) x` | Computing derivatives of polynomial terms. | `Mathlib/Analysis/Calculus/Deriv/Pow.lean` |
| `HasGradientAt.hasFDerivAt` | `HasGradientAt f g x → HasFDerivAt f (InnerProductSpace.toDual 𝕜 F g) x` | Passing from a gradient certificate to the Fréchet-derivative API. | `Mathlib/Analysis/Calculus/Gradient/Basic.lean` |
| `HasGradientAt.differentiableAt` | `HasGradientAt f g x → DifferentiableAt 𝕜 f x` | Establishing differentiability directly from a computed gradient. | `Mathlib/Analysis/Calculus/Gradient/Basic.lean` |
| `HasGradientAt.gradient` | `HasGradientAt f g x → gradient f x = g` | Converting a pointwise gradient certificate into an equality for Mathlib's `gradient`. | `Mathlib/Analysis/Calculus/Gradient/Basic.lean` |
| `HasFDerivAt.comp_hasDerivAt` | `HasFDerivAt l l' (f x) → HasDerivAt f f' x → HasDerivAt (l ∘ f) (l' f') x` | Chain rule for a scalar-parameterized curve followed by a Fréchet-differentiable map. It preserves point-free composition syntax; hidden instance diamonds may require changing the proof boundary rather than `simpa`. | `Mathlib/Analysis/Calculus/Deriv/Comp.lean` |
| `hasDerivAt_pi` | `HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x` | Moving between a derivative of a product-valued function and coordinatewise derivative proofs. | `Mathlib/Analysis/Calculus/Deriv/Prod.lean` |
| `HasDerivAt.fun_sum` | `(∀ i ∈ u, HasDerivAt (A i) (A' i) x) → HasDerivAt (fun y ↦ ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x` | Differentiating a lambda whose value is a finite sum; use `.sum` for the point-free sum of functions. | `Mathlib/Analysis/Calculus/Deriv/Add.lean` |
| `antitone_of_hasDerivAt_nonpos` | `(∀ x, HasDerivAt f (f' x) x) → f' ≤ 0 → Antitone f` | Turning a global nonpositive derivative certificate into monotonic decrease. | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` |
| `InnerProductSpace.toDual_apply_apply` | `InnerProductSpace.toDual 𝕜 E x y = inner 𝕜 x y` | Evaluating the Riesz dual map after a chain rule, especially in gradient-flow energy identities. | `Mathlib/Analysis/InnerProductSpace/Dual.lean` |
| `ContinuousOn.sub` | `ContinuousOn f s → ContinuousOn g s → ContinuousOn (f - g) s` | Proving continuity for MVT preconditions. | `Mathlib/Topology/ContinuousOn.lean` |
| `ContinuousOn.mul` | `ContinuousOn f s → ContinuousOn g s → ContinuousOn (f * g) s` | Proving continuity for MVT preconditions. | `Mathlib/Topology/ContinuousOn.lean` |
| `Real.sq_sqrt` | `0 ≤ x → (√x)^2 = x` | Unraveling distance norms (like the Frobenius norm). | `Mathlib/Data/Real/Sqrt.lean` |
| `Real.sqrt_inv` | `Real.sqrt x⁻¹ = (Real.sqrt x)⁻¹` | Distributing square root over multiplicative inverse. | `Mathlib/Data/Real/Sqrt.lean` |
| `Real.sqrt_sq_eq_abs` | `√(x^2) = \|x\|` | Extracting absolute values from squared distances (e.g., in Cauchy-Schwarz). | `Mathlib/Data/Real/Sqrt.lean` |
| `sq_le_sq` | `0 ≤ a → 0 ≤ b → (a^2 ≤ b^2 ↔ a ≤ b)` | Equivalence of squares for non-negative real numbers. | `Mathlib/Algebra/Order/Ring/Abs.lean` |
| `Matrix.fromBlocks` | `Matrix.fromBlocks A B C D` | Cleanly constructing a $2d$ block matrix $\begin{bmatrix} A & B \\ C & D \end{bmatrix}$. | `Mathlib/Data/Matrix/Block.lean` |
| `Matrix.dotProduct` | `Matrix.dotProduct v w = ∑ i, v i * w i` | Definition of the algebraic dot product of vectors. | `Mathlib/Data/Matrix/Basic.lean` | w i` | Computes the dot product on standard functions `ι → ℝ` purely algebraically, without requiring an `InnerProductSpace` topology. | `Mathlib/Data/Matrix/Basic.lean` |
| `div_le_div_of_nonneg_right` | `a ≤ b → 0 ≤ c → a / c ≤ b / c` | Dividing inequalities by a non-negative denominator. | `Mathlib/Algebra/Order/Field/Basic.lean` |
| `innerProduct_self_eq_sum_sq` | `inner x x = ∑ i, x i ^ 2` | Linking Euclidean `x ⊙ x` to its component sum. | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |


---

## 7. Summability & Series

Infinite sums, p-series, and Tannery's Theorem.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `tsum_eq_add_tsum_ite` | `∑' n, f n = f i + ∑' n, ...` | Isolating a term from an infinite series | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` |
| `Real.summable_one_div_nat_rpow` | `Summable (1 / n^p) ↔ 1 < p` | Summability of p-series (Zeta values) | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` |
| `Summable.mul_left` | `Summable f → Summable (c * f)` | Scalar coefficients in series convergence | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` |
| `summable_subtype_iff_indicator` | `Summable f ↔ Summable (s.indicator f)` | Moving between subset sums and indicator sums | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` |
| `summable_pnat_iff_summable_nat` | `Summable (ℕ+) ↔ Summable (ℕ)` | Bridging series on positive and standard naturals | `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean` |
| `Summable.of_norm_bounded` | `Summable g → (∀ i, ‖f i‖ ≤ g i) → Summable f` | General comparison test for series in complete normed groups. | `Mathlib/Analysis/Normed/Group/InfiniteSum.lean` |
| `Summable.of_nonneg_of_le` | `(∀ b, 0 ≤ g b) → (∀ b, g b ≤ f b) → Summable f → Summable g` | Direct comparison test for non-negative real series. | `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` |
| `tendsto_tsum_of_dominated_convergence` | `Tendsto (∑' n, f i n) (∑' n, g n)` | Tannery's Theorem: DCT for infinite series | `Mathlib/Analysis/Normed/Group/Tannery.lean` |
| `Complex.re_tsum` | `(∑' n, f n).re = ∑' n, (f n).re` | Interchanging infinite sums and real-part projection | `PrimeNumberTheoremAnd/Wiener.lean` |
| `summable_complex_then_summable_real_part` | `Summable f → Summable (fun n ↦ (f n).re)` | Proving convergence of the real part of a complex series | `PrimeNumberTheoremAnd/ZetaBounds.lean` |
| `tsum_fintype` | `∑' x, f x = ∑ x, f x` | Converting infinite tsum to finite sum over a Fintype | `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` |
| `Finset.sum_coe_sort` | `∑ x : s, f x = ∑ x ∈ s, f x` | Relating a sum over a subtype to a sum over the finset | `Mathlib/Algebra/BigOperators/Basic.lean` |
| `Finset.sum_subset` | `s ⊆ t → (∀ x ∈ t \ s, f x = 0) → ∑ x ∈ s, f x = ∑ x ∈ t, f x` | Restricting or expanding finite sums when terms outside subset are zero | `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Finset.sum_sub_distrib` | `∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x` | Distributing subtraction over finite sums | `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Finset.sum_nonneg` | `(∀ i ∈ s, 0 ≤ f i) → 0 ≤ ∑ i ∈ s, f i` | The core lemma for proving a finite sum is non-negative | `Mathlib/Algebra/BigOperators/Order.lean` |
| `Finset.sum_nonpos` | `(∀ i ∈ s, f i ≤ 0) → ∑ i ∈ s, f i ≤ 0` | Proving a coordinatewise dissipation sum is nonpositive. | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` |
| `Finset.sum_mul_sq_le_sq_mul_sq` | `(∑ i ∈ s, f i * g i)^2 ≤ (∑ i ∈ s, f i^2) * (∑ i ∈ s, g i^2)` | The Cauchy-Schwarz inequality for finite sums. | `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Finset.abs_sum_le_sum_abs` | `|∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|` | The triangle inequality for finite sums. | `Mathlib/Algebra/BigOperators/Order.lean` |
| `Fin.sum_univ_eq_sum_range` | `(f : ℕ → M) (n : ℕ) : ∑ i : Fin n, f ↑i = ∑ i ∈ Finset.range n, f i` | Bridging `Fin n` sums and `Finset.range n` sums (e.g. matching `strong_law_ae`'s conclusion). Pass `f` explicitly in `rw` — higher-order matching fails otherwise. Generated by `to_additive` from `Fin.prod_univ_eq_prod_range` | `Mathlib/Data/Fintype/BigOperators.lean` |


---

## 8. Project Specific Identities

Identities derived or defined within this repository.

| Name | Description | Source File |
| :--- | :--- | :--- |
| `ConvexOpt.gf_monotone_decrease` | Along a `GFTrajectory f w₀ w`, certifies `HasDerivAt (f ∘ w) (-‖gradient f (w t)‖ ^ 2) t`. | `LeanMachineLearning/Optimization/ConvexOpt/Basic.lean` |
| `Lasso.hasGradientAt_posDlnObjective` | Computes the gradient certificate for the positive-DLN objective under matrix symmetry. Its Taylor-remainder subproof currently contains `sorry`, so downstream results still inherit that axiom. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.entropyBregman_nonneg_of_nonneg` | `Nonnegative x → Positive y → 0 ≤ entropyBregman x y`. Generalizes the blueprint's `entropyBregman_nonnegative` (which requires `Positive x`) to allow zero coordinates in `x`, matching the `docs/Lasso.md` continuity convention `0 log 0 = 0`; needed whenever `x` ranges over a `Nonnegative`-only feasible set (e.g. a Bregman projection). | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.entropyBregman_eq_zero_iff` | `Nonnegative x → Positive y → (entropyBregman x y = 0 ↔ x = y)`. The equality case of `entropyBregman_nonneg_of_nonneg`, giving the uniqueness half of a Bregman-projection argument. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.matVec_sub` / `Lasso.matVec_smul_eq` | `matVec M (x - y) = matVec M x - matVec M y` / `matVec M (c • x) = c • matVec M x`. The linearity API for the project's `EuclideanSpace`-wrapped matrix-vector product; combine with `Lasso.InMatrixSpan` to build "the difference of two matVec-images lies in the column span" witnesses. | `LeanMachineLearning/Optimization/Lasso/Basic.lean` |
| `Lasso.inner_matVec_comm_of_isSymm` | `M.IsSymm → inner ℝ x (matVec M y) = inner ℝ (matVec M x) y`. Self-adjointness of `matVec M` for symmetric `M`; the key step for moving a `Span M` witness across an inner product (e.g. showing a cross term vanishes because it factors through `ker M`). | `LeanMachineLearning/Optimization/Lasso/Basic.lean` |
| `Lasso.hasGradientAt_tiltedLoss` | Computes the tilted-loss gradient `Mx - r + lambda * 1` under matrix symmetry. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.inner_tiltedGradient_positiveEffectiveVectorField` | Exact coordinatewise energy identity `⟪∇L̃(x), V(x)⟫ = ∑ i, -4 * x i * (∂ᵢL̃(x))²`. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.inner_tiltedGradient_positiveEffectiveVectorField_nonpos` | The effective vector field is a tilted-loss descent direction when `x` is coordinatewise nonnegative. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.posEffectiveParameter_nonnegative` | The effective parameter `u(t)²` is coordinatewise nonnegative, without requiring a `Fintype` instance. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.tiltedLoss_coordinateSquare_eq_posDlnObjective` | Exact bridge `tiltedLoss M r lambda (u²) = posDlnObjective M r lambda u`. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |
| `Lasso.posDlnObjective_antitone_along_pos_flow` | The weight-space positive-DLN objective is antitone along its gradient flow. It currently depends on the incomplete Taylor-remainder proof in `hasGradientAt_posDlnObjective`. | `LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean` |

---

## 9. Algebraic Geometry & Category Theory (Schemes)

Lemmas for schemes, residue fields, stalks, morphism properties, and group schemes (used in `AlgebraicJacobian/Picard/*`). All verified against the pinned Mathlib checkout.

| Name | Statement | When to use | Mathlib File |
| :--- | :--- | :--- | :--- |
| `MorphismProperty.of_pullback_snd_of_descendsAlong` | `[P.DescendsAlong Q] [HasPullback f g] → Q g → P (pullback.snd f g) → P f` | Descend a morphism property `P` from a base change to the original morphism | `Mathlib/CategoryTheory/MorphismProperty/Descent.lean` |
| `AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact` | `DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` | fpqc descent of universal closedness (Stacks 02KS). With `of_pullback_snd_of_descendsAlong`, descends closedness/properness from `Spec k̄ → Spec k` | `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean` |
| `AlgebraicGeometry.smooth_of_grpObj` | `[LocallyOfFiniteType f] [GrpObj (Over.mk f)] [GeometricallyReduced f] → Smooth f` | A group scheme over a field that is LFT + geometrically reduced is smooth (subsumes the translation-propagation argument) | `Mathlib/AlgebraicGeometry/Group/Smooth.lean` |
| `AlgebraicGeometry.Scheme.Hom.residueFieldMap` | `(f : X ⟶ Y) (x : X) : Y.residueField (f x) ⟶ X.residueField x` | The (contravariant) residue-field map induced by a scheme morphism | `Mathlib/AlgebraicGeometry/ResidueField.lean` |
| `AlgebraicGeometry.residueFieldMap_comp` | `(f ≫ g).residueFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x` | Functoriality of `residueFieldMap` — **note the contravariant order** | `Mathlib/AlgebraicGeometry/ResidueField.lean` |
| `AlgebraicGeometry.residueFieldMap_id` | `(𝟙 X).residueFieldMap x = 𝟙 (X.residueField x)` | Identity case (write as `Hom.residueFieldMap (𝟙 X) x`, not dot-notation) | `Mathlib/AlgebraicGeometry/ResidueField.lean` |
| `instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x)` | residue map of an open immersion is an iso | **Key structural route**: if `f` is an iso/identity/open-immersion, get `IsIso (f.residueFieldMap x)` for free | `Mathlib/AlgebraicGeometry/ResidueField.lean` |
| `AlgebraicGeometry.residueFieldIsoBase` | `[IsAlgClosed K] [LocallyOfFiniteType f] (x) (hx : IsClosed {x}) : X.residueField x ≅ .of K` | Residue field of a **closed** point over an **algebraically closed** field is `K` | `Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean` |
| `AlgebraicGeometry.Spec.residueFieldIso` | `(Spec R).residueField x ≅ .of x.asIdeal.ResidueField` | Residue field of an affine-scheme point | `Mathlib/AlgebraicGeometry/ResidueField.lean` |
| `AlgebraicGeometry.SpecToEquivOfLocalRing` | `(Spec R ⟶ X) ≃ Σ x, {f : X.presheaf.stalk x ⟶ R // IsLocalHom f}` | Functor-of-points; substrate for dual-numbers / tangent-space API (Stacks 0B2C/0B2D) | `Mathlib/AlgebraicGeometry/Stalk.lean` |
| `AlgebraicGeometry.Scheme.stalkClosedPointTo` | `(f : Spec (.of K) ⟶ X) : X.presheaf.stalk (f (closedPoint K)) ⟶ .of K` | Ring map on stalks from a `K`-point; feeds `descResidueField` | `Mathlib/AlgebraicGeometry/Stalk.lean` |
| `CategoryTheory.isIso_of_mono_of_isSplitEpi` | `[Mono f] [IsSplitEpi f] → IsIso f` | A split epi that is also mono is an iso (dual: `isIso_of_epi_of_isSplitMono`) | `Mathlib/CategoryTheory/EpiMono.lean` |
| `CategoryTheory.ConcreteCategory.mono_of_injective` | `Function.Injective f → Mono f` | Mono from injectivity in a concrete category (e.g. a field hom in `CommRingCat`) | `Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean` |
| `CategoryTheory.ConcreteCategory.isIso_iff_bijective` | `IsIso f ↔ Function.Bijective f` | Iso from bijectivity (needs `(forget C).ReflectsIsomorphisms`) | `Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean` |
| `CategoryTheory.MorphismProperty.DescendsAlong` | `class DescendsAlong (P Q : MorphismProperty C)` | The descent typeclass; `.inf`, `.top`, `.of_le` combinators exist | `Mathlib/CategoryTheory/MorphismProperty/Descent.lean` |
| `AlgebraicGeometry.isProper_iff` | `IsProper f ↔ IsSeparated f ∧ UniversallyClosed f ∧ LocallyOfFiniteType f` | Assemble/destructure properness from its three conjuncts | `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` |
| `instance [Field R] : Unique (PrimeSpectrum R)` | `Spec` of a field is a single point (its `asIdeal = ⊥`) | Identifying the unique point / `default` of `Spec k` | `Mathlib/RingTheory/Spectrum/Prime/Basic.lean` |
| `AlgebraicGeometry.instance [GeometricallyIntegral f] : GeometricallyIrreducible f` | (and `→ GeometricallyReduced`) | Bridging `GeometricallyIntegral` hypotheses to the weaker properties (e.g. for `genus`) | `Mathlib/AlgebraicGeometry/Geometrically/Integral.lean` |
| `real_inner_self_eq_norm_sq` | `inner x x = ‖x‖^2` | Converting a squared norm to an inner product to allow component-wise expansion | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `PiLp.inner_apply` | `inner f g = ∑ i, inner (f i) (g i)` | Unfolding the inner product on `EuclideanSpace` or `PiLp` to a sum of scalar products | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |
| `Finset.sum_add_sum_compl` | `(∑ i ∈ s, f i) + (∑ i ∈ sᶜ, f i) = ∑ i, f i` | Splitting a sum over `univ` into a subset and its complement. Use `← Finset.sum_add_sum_compl` to avoid `.symm` on `Eq`. | `Mathlib/Algebra/BigOperators/Basic.lean` |
| `Finset.sum_attach` | `∑ i ∈ s, f i = ∑ i : {x // x ∈ s}, f (i.val)` | Converting a sum over a `Finset` to a sum over the subtype of elements in the `Finset`. | `Mathlib/Algebra/BigOperators/Basic.lean` |
| `Finset.sum_congr rfl` | `(∀ i ∈ s, f i = g i) → ∑ i ∈ s, f i = ∑ i ∈ s, g i` | Rewriting the body of a sum by providing an element-wise equality proof (via `intro i _`). | `Mathlib/Algebra/BigOperators/Basic.lean` |
| `RCLike.star_def` / `star_trivial` | `star x = x` for `x : ℝ` | Normalizing complex conjugation applied to real numbers (often introduced by `inner` on `ℝ`). | `Mathlib/Data/RCLike/Basic.lean` |
| `InformationTheory.klFun` / `klFun_nonneg` | `klFun x = x*log x + 1 - x`; `0 ≤ x → 0 ≤ klFun x` | Ready-made bound `x - 1 ≤ x * log x` for `x ≥ 0` (unfold `klFun` then `linarith`) — avoids reproving boundedness of `x ↦ x log x` from scratch. | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` |
| `Real.log_le_sub_one_of_pos` | `0 < x → log x ≤ x - 1` | Companion upper bound giving `x * log x ≤ x^2` for `x ≥ 0` (multiply by `x ≥ 0`, case-split `x = 0`). | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.log_le_log` | `0 < x → x ≤ y → log x ≤ log y` | Monotonicity of `log`, the non-`Iff` forward direction (see also `log_le_log_iff`, `log_lt_log`). | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |
| `Real.exp_le_one_iff` | `exp x ≤ 1 ↔ x ≤ 0` | Directly proving `exp` bounds by `1` instead of rewriting `1 = exp 0` and using `exp_le_exp` (which risks rewriting *every* literal `1` in the goal, not just the intended one). | `Mathlib/Analysis/Complex/Exponential.lean` |
| `real_inner_le_norm` | `⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖` | One-sided (non-`abs`) Cauchy–Schwarz; convenient when the sign of the inner product is already known/irrelevant. | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `abs_real_inner_le_norm` | `|⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖` | Two-sided Cauchy–Schwarz; combine with `neg_le_abs` to get `-⟪x,y⟫ ≤ ‖x‖‖y‖`. | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `Finset.single_le_sum` | `(∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ i ∈ s, f i` | Bounding a single nonnegative summand by the whole sum; key step in proving `‖x‖ ≤ ∑ i, x i` for `x ≥ 0` (ℓ² norm ≤ ℓ¹ norm). | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` |
| `le_of_mul_le_mul_left` | `a * b ≤ a * c → 0 < a → b ≤ c` | Division-free cancellation of a positive common left factor; preferred over introducing `/` when the rest of the proof is polynomial. | `Mathlib/Algebra/Order/GroupWithZero/Defs.lean` |
| `le_div_iff₀` | `0 < c → (a ≤ b / c ↔ a * c ≤ b)` | Clearing a positive denominator on the RHS of `≤` (dual of `div_le_iff₀`, which clears it on the LHS). | `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean` |
| `real_inner_smul_right` | `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ` | Real-scalar version of `inner_smul_right` (no `starRingEnd`/conjugate noise). | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| `EuclideanSpace.single` / `PiLp.single_apply` | `EuclideanSpace.single i a : EuclideanSpace 𝕜 ι`; `(PiLp.single p 𝕜 i a).ofLp j = if j = i then a else 0` | Standard basis vector in `EuclideanSpace`; needs `[DecidableEq ι]` (bring via `open Classical in` on **each** declaration that uses it — the modifier does not propagate to subsequent declarations). | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` |
| `map_sum` (via `(WithLp.linearEquiv p 𝕜 (ι → 𝕜)).toContinuousLinearEquiv`) | `e (∑ i, f i) = ∑ i, e (f i)` | Fallback for transporting a `Finset.sum` of `EuclideanSpace`/`WithLp` vectors through to the underlying `Π i, 𝕜` sum when plain `simp` doesn't already close the coordinatewise-evaluation goal. | `Mathlib/Analysis/Normed/Lp/PiLp.lean` (equiv), core `map_sum` |
| `Filter.Eventually.filter_upwards` | `filter_upwards [h1, h2] with x hx1 hx2` | The canonical way to combine multiple `∀ᶠ` (eventually) bounds into a single neighborhood for local reasoning. | `Mathlib/Order/Filter/Basic.lean` |
| `lt_max_of_lt_left` / `le_max_left` | `a < b → a < max b c` | Dismantling or bounding `max` operations directly without `split_ifs` | `Mathlib/Order/MinMax.lean` |
| `Matrix.isHermitian_iff_isSymm` | `M.IsHermitian ↔ M.IsSymm` | Bridging real symmetric matrices to Hermitian APIs (often required for spectral theorems) | `Mathlib/LinearAlgebra/Matrix/Hermitian.lean` |
| `OrthonormalBasis.sum_inner_mul_inner` | `∑ i, ⟪v, e i⟫ * ⟪e i, w⟫ = ⟪v, w⟫` | Expanding vectors in an orthonormal basis; essential for eigenvalue/PSD bounds | `Mathlib/Analysis/InnerProductSpace/Basis.lean` |
