# CH2 API Reference

Lean definitions, lemmas, and Mathlib pointers for the Beurling-Selberg approximant machinery in `PrimeNumberTheoremAnd/CH2.lean`.

---

## Glossary

Core symbols used throughout the file. `ε` always takes values in `{-1, 1}`, selecting the minorant (`-1`) or majorant (`+1`) variant.

| Symbol | Lean Type | Mathematical Definition | Notes |
| :--- | :--- | :--- | :--- |
| `Rectangle z w` | `Set ℂ` | `[[z.re, w.re]] ×ℂ [[z.im, w.im]]` | Axis-parallel rectangle with corners `z` and `w`. Defined in `Mathlib/Data/Complex/Basic.lean:796`. |
| `ν` | `ℝ` | Frequency shift parameter | Controls the pole location at $-i\nu/2\pi$. |
| `ε` | `ℝ` | `±1` offset | Selects minorant (`-1`) or majorant (`+1`). |
| `x` | `ℝ` | Frequency domain variable | Argument of the Fourier transform. |
| `𝓕 f` | `(ℝ → ℂ) → ℝ → ℂ` | $\int_{-\infty}^{\infty} f(t)\,e^{-2\pi itx}\,dt$ | Fourier transform via the Lebesgue integral. |
| `E z` | `ℂ → ℂ` | $e^{2\pi iz}$ | Complex exponential character; `E (-↑t * ↑x) = e^{-2\pi itx}`. |
| `↑t` | `ℝ → ℂ` | $t \mapsto t + 0i$ | Canonical real-to-complex coercion (`Complex.ofReal`). |
| `Phi_circ ν ε z` | `ℂ → ℂ` | $\tfrac{1}{2}(\coth(w/2) + \varepsilon)$, $w = -2\pi iz + \nu$ | Periodic oscillatory component of the approximant. |
| `Phi_star ν ε z` | `ℂ → ℂ` | $(B(w) - B(\nu))/(2\pi i)$ | Non-periodic component; vanishes at $z = 0$. |
| `ϕ_pm ν ε` | `ℝ → ℂ` | $\Phi^\circ + \operatorname{sgn}(t)\Phi^\star$ on $[-1,1]$, else $0$ | Compactly supported Beurling-Selberg kernel. |
| `B ε s` | `ℂ → ℂ` | `if s = 0 then 1 else s/2 * (coth(s/2) + ε)` | "Sinc-like" hyperbolic auxiliary; removable singularity at $s=0$. |
| `Inu ν x` | `ℝ → ℝ` | `if 0 ≤ x then exp(-νx) else 0` | Truncated exponential kernel that `ϕ_pm` approximates. |
| `S a s x` | | Partial/tail sum of a Dirichlet series | `if σ < 1` partial sum, else tail sum. |

---

## Main Results

| Name | Statement | Role |
| :--- | :--- | :--- |
| `CH2_lemma_4_2a` | `‖deriv (z ↦ z * coth z) (↑x + ↑(π/4) * I)‖ < 1` | Technical bound on the derivative of the cotangent kernel at the boundary ray. |
| `CH2_lemma_4_2b` | `‖deriv (z ↦ z * coth z) z‖ ≤ ‖z‖` | Growth estimate for the kernel derivative in the complex plane. |
| `cor_1_2_a/b` | Bounds on $\psi(x) - x$ | Relates the Chebyshev $\psi$ function to the Riemann Hypothesis up to height $T$. |
| `cor_1_3_a/b` | Estimates for $\sum_{n \leq x} \frac{\Lambda(n)}{n^\sigma}$ | Corollaries for weighted sums of the von Mangoldt function. |
| `prop_2_3` | Major identity for $\sum a_n \frac{x}{n} \hat{\varphi}(\cdots)$ | Expresses a weighted arithmetic sum via the integral of the $L$-series $G(s)$ along the critical line. |
| `prop_2_4_plus/minus` | $S_\sigma(x) \leq / \geq$ [Integral Expression] | Upper/lower bounds for the arithmetic sum via majorant/minorant Fourier transforms. |

---

## 1. Fourier-Analytic Foundations

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `summable_nterm_of_log_weight` | `Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)) → Summable (nterm a sig)` | If an arithmetic sequence decays logarithmically, its Dirichlet series converges for $\text{Re}(s) > 1$. |
| `fourier_scale_div_noscalar` | `𝓕 (fun t ↦ φ (t / T)) u = T * 𝓕 φ (T * u)` | Scaling: stretching in time compresses in frequency. |
| `prop_2_3_1` | Technical identity involving $a_n, G(s), x, \sigma, T$ | Bridge lemma for Prop 2.3, relating a discrete sum to a truncated contour integral. |

---

## 2. Summation Kernels ($S_\sigma(x)$ and $I_\nu$)

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `S` (def) | `if σ < 1 then ∑_{n ≤ x} a_n/n^σ else ∑_{n ≥ x} a_n/n^σ` | Partial sum ($\sigma < 1$) or tail sum ($\sigma > 1$) of a Dirichlet series. |
| `I'` (def) | `if 0 ≤ λ * u then exp(-λ * u) else 0` | Exponential kernel used to approximate summation weights. |
| `S_eq_I` | `S a s x = x⁻ˢ * ∑ a_n (x/n) I'(...)` | Converts $S$ into a form suitable for Fourier analysis. |

---

## 3. Hyperbolic Function Utilities

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `coth` (def) | `1 / tanh z` | Definition of the complex hyperbolic cotangent. |
| `sinh_add_pi_I` | `sinh (z + π * I) = -sinh z` | Anti-periodicity of $\sinh$ under $\pi i$ shift. |
| `cosh_add_pi_I` | `cosh (z + π * I) = -cosh z` | Anti-periodicity of $\cosh$ under $\pi i$ shift. |
| `tanh_add_pi_I` | `tanh (z + π * I) = tanh z` | Periodicity of $\tanh$ under $\pi i$ shift. |
| `coth_add_pi_mul_I` | `coth (z + π * I) = coth z` | Periodicity of $\coth$ under $\pi i$ shift. |
| `tanh_add_int_mul_pi_I` | `tanh (z + π * I * m) = tanh z` | Periodicity of $\tanh$ for any integer multiple of $\pi i$. |
| `sinh_zero_iff` | `sinh ζ = 0 ↔ ∃ k:ℤ, ζ = k * π * I` | All roots of complex $\sinh$. |
| `cosh_zero_iff` | `cosh ζ = 0 ↔ ∃ k:ℤ, ζ = (k + 1/2) * π * I` | All roots of complex $\cosh$. |
| `analyticAt_tanh` | `AnalyticAt ℂ Complex.tanh z` | $\tanh$ is analytic where $\cosh \neq 0$. |
| `continuousAt_tanh` | `ContinuousAt Complex.tanh z` | Continuity of $\tanh$ away from its poles. |
| `meromorphicAt_tanh/coth` | `MeromorphicAt ... z` | $\tanh$ and $\coth$ are meromorphic everywhere. |
| `sinh/cosh_ne_zero_of_re_ne_zero` | `z.re ≠ 0 → sinh/cosh z ≠ 0` | Hyperbolic functions don't vanish away from the imaginary axis. |
| `sinh_ne_zero_of_im` | `(∀ k : ℤ, z.im ≠ k * π) → sinh z ≠ 0` | Complement: $\sinh$ vanishes on the imaginary axis only at integer multiples of $\pi$. |
| `ContinuousAt.coth` | `ContinuousAt (fun t ↦ coth (f t)) s` | Composition rule for continuity of $\coth$. |
| `Complex.sinh_ne_zero_of_cosh_zero` | `cosh z = 0 → sinh z ≠ 0` | Roots of $\cosh$ and $\sinh$ are disjoint. |
| `meromorphicOrderAt_cosh/sinh_ne_top` | `meromorphicOrderAt ... z ≠ ⊤` | $\cosh$ and $\sinh$ are not identically zero near any point. |
| `meromorphicOrderAt_coth_lt_zero_iff` | `meromorphicOrderAt coth z < 0 ↔ sinh z = 0` | Poles of $\coth$ coincide exactly with roots of $\sinh$. |
| `sinh_ofReal_half_ne_zero` | `x ≠ 0 → sinh (x / 2) ≠ 0` | Real-valued $\sinh$ of non-zero arguments never vanishes. |
| `coth_conj` | `starRingEnd ℂ (coth z) = coth (starRingEnd ℂ z)` | Hermitian symmetry of $\coth$: conjugation commutes with the function. |

---

## 4. The Auxiliary Function $B^\pm(s)$

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `B` (def) | `if s = 0 then 1 else s/2 * (coth(s/2) + ε)` | A "sinc-like" hyperbolic auxiliary function used to build the extremal approximants. |
| `B.continuous_zero` | `ContinuousAt (B ε) 0` | Continuity at the removable singularity at the origin ($s \to 0$, $\coth \to \infty$, product $\to 1$). |
| `B.continuousAt_ofReal_ne_zero` | `ContinuousAt (fun t ↦ B ε t) s` | Continuity of the real-valued restriction away from zero. |
| `B.continuous_ofReal` | `Continuous (fun t:ℝ ↦ B ε t)` | Continuity on the entire real line (combines the two cases above). |
| `B_plus_mono` | `Monotone (fun t ↦ (B 1 t).re)` | $B^+$ is increasing on the real line. |
| `B_minus_mono` | `Antitone (fun t ↦ (B (-1) t).re)` | $B^-$ is decreasing on the real line. |
| `B_im_eq_zero` | `(B ε t).im = 0` for real `t` | $B$ maps real inputs to real outputs. |
| `B_plus/minus_real` | `(B (±1) t).im = 0` | Specializations of `B_im_eq_zero` for `ε = ±1`. |
| `B_ofReal_eq` | `B ε ν = ν * (coth(ν/2) + ε) / 2` | Explicit evaluation for real non-zero arguments. |
| `meromorphicAt_B` | `MeromorphicAt (B ε) z₀` | $B$ is meromorphic in the complex plane. |
| `analyticAt_B` | `AnalyticAt ℂ (B ε) z₀` | Specifies the region where $B$ is holomorphic (away from poles). |
| `B_conj` | `star (B ε z) = B ε (star z)` | Hermitian symmetry of $B$. |
| `meromorphic_tanh` | `Meromorphic Complex.tanh` | Global (pointwise) meromorphicity of $\tanh$; bundles `meromorphicAt_tanh`. |
| `meromorphic_coth` | `Meromorphic coth` | Global meromorphicity of $\coth$. |
| `meromorphic_coth'` | `Meromorphic (fun s ↦ cosh s / sinh s)` | Meromorphicity of the explicit quotient form; used inside `meromorphicAt_B`. |
| `meromorphic_coth''` | `Meromorphic (fun s ↦ cosh(s/2) / sinh(s/2))` | Half-argument quotient form used when unfolding $B$. |
| `h_B_rational` | `w ≠ 0 → B ε w = w * (cosh(w/2) / sinh(w/2) + ε) / 2` | Rational rewrite of $B$ as an explicit quotient; used to establish $C^2$ smoothness. |

---

## 5. The Approximants ($\Phi^\circ$, $\Phi^\ast$, $\varphi^{\pm}$)

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `Phi_circ` (def) | `(1/2) * (coth(w/2) + ε)`, $w = -2\pi iz + \nu$ | Periodic oscillatory component of the Beurling-Selberg approximant. |
| `Phi_star` (def) | `(B(w) - B(ν)) / (2πi)` | Non-periodic component capturing the main summation weight. |
| `Phi_cancel` | Residue cancellation at $z = \pm 1$ | $\Phi^\circ \pm \Phi^\ast$ is regular at points where individual terms have poles. |
| `ϕ_pm` (def) | `1_{[-1,1]} * (Phi_circ + sign(t) * Phi_star)` | The compactly supported kernel whose Fourier transform is studied. |
| `Phi_star_zero` | `Phi_star ν ε 0 = 0` | Value at the origin, confirming removal of the singularity. |
| `Phi_star.poles` | `z = n - I * ν / (2π), n ≠ 0` | Poles of $\Phi^\ast$ (exclude the origin). |
| `Phi_star.residue` | Residue is $-in/2\pi$ | Residue at each pole of $\Phi^\ast$. |
| `Phi_star.poles_simple` | `meromorphicOrderAt = -1` | All poles of $\Phi^\ast$ are simple. |
| `Phi_circ/star.meromorphic` | `MeromorphicAt (Phi_...) z` | Both components are meromorphic. |
| `ϕ_c2_left/right` | `ContDiffOn ℝ 2 ...` | $C^2$ smoothness on the left/right halves of the support. |
| `varphi_differentiableAt_left/right/out` | `DifferentiableAt ℝ ϕ_pm x` | Piecewise differentiability. |
| `ϕ_pm_zero_boundary` | `ϕ_pm ν ε (±1) = 0` | Vanishing at the support boundary. |
| `ϕ_continuous` | `Continuous (ϕ_pm ν ε)` | The spliced function is continuous on all of $\mathbb{R}$. |
| `h_comp` | `ContDiff ℝ 2 (t ↦ (-2πit + ν) * (cosh/sinh + ε) / 2)` | $C^2$ smoothness of the explicit composition used to build $\Phi^\ast$ on $\mathbb{R}$. |
| `Phi_star.contDiff_real` | `ContDiff ℝ 2 (fun t : ℝ ↦ Phi_star ν ε t)` | $C^2$ smoothness of $\Phi^\ast$ restricted to $\mathbb{R}$; feeds into `ϕ_c2_left/right`. |
| `Phi_circ.contDiff_real` | `ContDiff ℝ 2 (fun t : ℝ ↦ Phi_circ ν ε t)` | $C^2$ smoothness of $\Phi^\circ$ restricted to $\mathbb{R}$. |
| `Phi_circ_conj_symm` *(private)* | `Phi_circ ν ε (-(↑t)) = conj (Phi_circ ν ε (↑t))` | Conjugate-reflection symmetry of $\Phi^\circ$ on the real line; used in `fourier_real`. |
| `Phi_star_conj_symm` *(private)* | `Phi_star ν ε (-(↑t)) = -conj (Phi_star ν ε (↑t))` | Conjugate-reflection symmetry of $\Phi^\ast$ (anti-symmetric); used in `fourier_real`. |

---

## 6. Poles, Residues, and Analyticity

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `Phi_circ.poles` | `z = n - I * ν / (2π)` | Pole lattice of $\Phi^\circ$ (vertical lines at integer real parts). |
| `Phi_circ.residue` | Residue is $i/2\pi$ | Residue at each pole, used in the Residue Theorem. |
| `Phi_circ.poles_simple` | `meromorphicOrderAt = -1` | All poles of $\Phi^\circ$ are simple. |
| `pole_re/im` | `(iν/2π).re = 0`, `(-iν/2π).im = -ν/2π` | Coordinates of the critical poles. |
| `Phi_circ/star.analyticAt_of_not_pole` | `AnalyticAt ... z` | Analyticity away from the pole lattice. |
| `Phi_circ/star.analyticAt_of_im_ne_pole` | `z.im ≠ -ν/2π → AnalyticAt` | Analyticity in any region avoiding the pole line. |
| `Phi_circ/star.analyticAt_of_im_gt_pole` | `z.im > -ν/2π → AnalyticAt` | Analyticity in the upper half-plane (contains the real axis). |
| `Phi_circ/star.analyticAt_of_im_nonneg` | `hν : ν > 0 → 0 ≤ z.im → AnalyticAt` | Analyticity in the closed upper half-plane; specialises `of_im_gt_pole` using $\nu > 0$. |
| `Phi_star.analyticAt_of_not_pole_nz` | `(∀ n ≠ 0, z ≠ n - Iν/2π) → AnalyticAt ℂ (Phi_star ν ε) z` | Analyticity when $z$ avoids all non-zero poles; weaker than `of_not_pole` since the origin is a removable singularity. |
| `Phi_circ/star.analyticAt_of_re_ne_int` | `¬∃n:ℤ, z.re = n → AnalyticAt` | Analyticity away from integer vertical lines. |
| `ϕ_circ_bound_right/left` | `‖Phi_circ ν ε z‖ ≤ C` | Uniform bounds for the periodic component in upper/lower half-planes. |
| `ϕ_star_bound_right/left` | `‖Phi_star ν ε z‖ ≤ C(|z|+1)` | Growth bounds for the non-periodic component. |
| `z₀_pole` / `z₁_pole` | Specific pole locations | Labels for critical poles near the integration boundaries. |
| `Phi_fourier_holo_left/right` | `HolomorphicOn ...` | Patches removable singularities at cancelled poles to allow contour shifting. |
| `Phi_diff/add_bounded_near_pole` | Boundedness near critical poles | Necessary estimates for proving removable singularities. |

---

## 7. Contour Shifting and Fourier Identities

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `continuous_E` | `Continuous E` | Global continuity of the exponential character $E(z) = e^{2\pi iz}$. |
| `cont_E` | `Continuous (fun t : ℝ ↦ E (-t * x))` | Continuity of the Fourier kernel for fixed frequency $x$. |
| `E_conj_symm` *(private)* | `E (↑t * ↑x) = conj (E (-(↑t) * ↑x))` | Conjugate symmetry of the exponential character: $e^{2\pi itx} = \overline{e^{-2\pi itx}}$; used in `fourier_real`. |
| `Phi_circ_periodic` *(private)* | `Phi_circ ν ε (z + 1) = Phi_circ ν ε z` | Unit periodicity of $\Phi^\circ$; follows from $\coth$'s periodicity under $\pi i$ shift. |
| `tendsto_div_two_pi` *(private)* | `Tendsto (fun T ↦ T / (2π)) atTop atTop` | Auxiliary divergence lemma for the contour-shift rectangle height. |
| `two_sub_E_sq` *(private)* | `(2 : ℂ) - E ↑x - E (-↑x) = 4 * sin(πx)^2` | Trigonometric identity used to simplify the `shift_upwards_simplified` and `shift_downwards_simplified` formulas. |
| `unique_int_in_Icc` *(private)* | `n ∈ Icc a b ∧ k-1 < a ∧ b < k+1 → n = k` | There is at most one integer in any open unit interval; used to locate the unique pole inside a rectangle. |
| `meromorphicOrderAt_phi_diff_nonneg` *(private)* | `meromorphicOrderAt (Φ° - Φ*) (z₀_pole ν) ≥ 0` | The pole of $\Phi^\circ - \Phi^\ast$ at $z_0$ is removable; specialises `Phi_cancel` at $\sigma = -1$. |
| `meromorphicOrderAt_phi_add_nonneg` *(private)* | `meromorphicOrderAt (Φ° + Φ*) (z₁_pole ν) ≥ 0` | Same for $\Phi^\circ + \Phi^\ast$ at $z_1$; specialises `Phi_cancel` at $\sigma = 1$. |
| `analyticAt_removable_sing_mul_E` *(private)* | Analyticity of the patched function `if z = z_pole then c * E(-z_pole * x) else f z * E(-z * x)` | General removable-singularity lemma: if $f$ is meromorphic and has a limit $c$ at a pole, the function patched with $c \cdot E$ is analytic there. |
| `integral_neg_one_zero_eq_zero_one` *(private)* | `∫ t in [-1,0], f t = ∫ t in [0,1], f(-t)` | Symmetry integral: integral over the left half equals the integral of the reflected function over the right half. |
| `Complex.norm_le_abs_im_add_one` | `z.re ∈ [-1,1] → ‖z‖ ≤ |z.im| + 1` | Key norm estimate in the vertical strip: norm is controlled linearly by the imaginary part. |
| `phi_sum_norm_le_of_component_bounds` | `‖Φ°‖ ≤ C₁ ∧ ‖Φ*‖ ≤ C₂(‖z‖+1) → ‖Φ°‖+‖Φ*‖ ≤ (C₁+2C₂)(y+1)` | Combines individual component bounds into a single linear bound on the strip. |
| `integrableOn_Phi_circ/star_p12` | `IntegrableOn (Φ · * E) (Icc 0 T)` on the $+\tfrac{1}{2}$ ray | Integrability on the right half-integer contour segment (companion to `_m12` variants). |
| `tendsto_T_plus_one_mul_exp_atTop_nhds_zero` | `k < 0 → C * (T+1) * exp(kT) → 0` | Decay lemma: linear-times-exponential vanishes as $T \to \infty$; used to bound horizontal contour segments. |
| `integrable_fourier_path` | `ContinuousOn f [a,b] → Integrable (t ↦ f t * E(-p t * x))` | Integrability of Fourier-weighted continuous functions on compact intervals. |
| `first_contour_bottom_vanishes` | Bottom horizontal segment integral $= 0$ | The bottom horizontal segment of the first residue rectangle contributes nothing to the limit. |
| `varphi_fourier_ident` | Split integral formula for $\hat{\varphi}$ | Expresses $\hat{\varphi}$ as a sum of integrals over $[-1,0]$ and $[0,1]$. |
| `shift_upwards` | Fourier integral limit for $x < 0$ | Shifts the path to the upper half-plane, where the exponential term decays. |
| `shift_downwards` | Fourier integral limit for $x > 0$ | Shifts the path to the lower half-plane, picking up the residue at $-i\nu/2\pi$. |
| `shift_upwards_simplified` | $\hat{\varphi}(x) = \tfrac{\sin^2 \pi x}{\pi^2} \int \cdots$ | Explicit formula for $x < 0$. |
| `shift_downwards_simplified` | $\hat{\varphi}(x) - e^{-\nu x} = \cdots$ | Formula for $x > 0$, including the residue contribution $e^{-\nu x}$. |
| `fourier_formula_neg/pos` | Special cases of the above | Core Fourier-analytic bounds used for Chebyshev function estimates. |
| `fourier_real` | `(𝓕 ϕ).im = 0` | The Fourier transform of the real kernel is real-valued. |
| `varphi_integ` | `Integrable ϕ` | Prerequisite for the existence of the Fourier transform. |
| `RectangleIntegral_tendsTo_UpperU` | Limit of rectangle integrals | Foundation for shifting integration paths to infinity. |
| `tendsto_contour_shift(_downwards)` | Path shifting theorems | Moving integrals across regions of holomorphicity. |
| `phi_sum_norm_le_linear_halfplane` | `‖Phi‖ ≤ C(|z.im|+1)` | Bound ensuring convergence in half-planes. |
| `phi_bound_upwards/downwards` | Growth bounds as $\text{Im}(z) \to \pm\infty$ | Specific growth estimates for the approximants. |
| `phi_fourier_ray_bound` | `‖f‖ ≤ C(y+1) e^{2πxy}` | Decay estimate along vertical rays. |
| `integrable_phi_fourier_ray` | `IntegrableOn f (vertical ray)` | The integrand decays fast enough for convergence on vertical rays. |
| `horizontal_integral_phi_fourier_vanish` | $\int_a^b f(t+iT)\,dt \to 0$ | Horizontal segments vanish at infinity (upper half-plane). |
| `horizontal_integral_phi_fourier_vanish_downwards` | $\int_a^b f(t-iT)\,dt \to 0$ | Same, for the lower half-plane. |
| `first/second/third_contour_limit` | Residue calculation components | Evaluation of specific contour integrals in the lower half-plane limit. |
| `B/phi_star_affine_periodic` | `Phi_star(z+m) = Phi_star(z) + mε` | Quasi-periodicity used to handle summatory kernels. |

---

## 8. The $I_\nu$ Kernel and Error Estimates

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `Inu` (def) | `if 0 ≤ x then exp(-νx) else 0` | The truncated exponential kernel that `ϕ_pm` approximates. |
| `integral_re_B_mul_exp_add` *(private)* | `(∫ t, (B ε (ν+t) - B ε ν) * exp(ut)).re = ∫ t, ((B ε (ν+t)).re - (B ε ν).re) * exp(ut)` | Reduces the real part of a complex $B$-weighted integral to a real integral; used in `Inu_bounds_neg/pos`. |
| `integral_re_B_mul_exp_sub` *(private)* | Same with $\nu - t$ instead of $\nu + t$ | Subtraction variant; used in the positive-$x$ case of `Inu_bounds_pos`. |
| `integral_B_diff_mul_exp_nonneg` *(private)* | `(∀ t ∈ [0,T], B ε ν ≤ B ε (f t)) → 0 ≤ ∫ t, (B ε (f t) - B ε ν) * exp(ut)` | Sign lemma for the integral; nonnegativity follows from monotonicity of $B^+$. |
| `integral_B_diff_mul_exp_nonpos` *(private)* | Same with the inequality reversed | Nonpositivity variant for $B^-$. |
| `Inu_bounds_neg` | `x < 0 → 𝓕(ϕ⁻)(x).re ≤ Iν(x) ≤ 𝓕(ϕ⁺)(x).re` | Squeeze bound for $x < 0$ (both sides follow from monotonicity of $B^\pm$; $I_\nu = 0$ there). |
| `Inu_bounds_pos` | `x > 0 → 𝓕(ϕ⁻)(x).re ≤ Iν(x) ≤ 𝓕(ϕ⁺)(x).re` | Squeeze bound for $x > 0$ via the explicit Fourier formula. |
| `Inu_bounds_zero` | `𝓕(ϕ⁻)(0).re ≤ 1 ≤ 𝓕(ϕ⁺)(0).re` | Squeeze bound at $x = 0$, proved by continuity and taking $x \to 0^+$. |
| `Inu_bounds` | `𝓕(ϕ⁻)(x).re ≤ Iν(x) ≤ 𝓕(ϕ⁺)(x).re` for all $x$ | Full pointwise squeeze: the minorant and majorant Fourier transforms bracket $I_\nu$. Assembles the three cases above. |
| `varphi_fourier_minus_error` | $\int (I_\nu - \hat{\varphi}_\nu^-) = \cdots$ | Integrated error for the minorant kernel. |
| `varphi_fourier_plus_error` | $\int (I_\nu - \hat{\varphi}_\nu^+) = \cdots$ | Integrated error for the majorant kernel. |

---

## 9. Smoothness and Absolute Continuity

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `contDiffOn_Icc_deriv_integrableOn` *(private)* | `ContDiffOn ℝ 2 f [a,b] → IntegrableOn (deriv f) [a,b]` | A $C^2$ function on a compact interval has an integrable derivative; used in `varphi_deriv_integ`. |
| `varphi_ftc_aux` *(private)* | `x,y ∈ [a,b] ∧ diff on (a,b) → ∫ₓʸ deriv ϕ = ϕ(y) - ϕ(x)` | General FTC driver for $\varphi$ on any subinterval given interior differentiability. |
| `eVariationOn_add_jump_greatest` *(private)* | `eVariationOn f' s ≤ eVariationOn f s + edist (f' x) (f x)` when `x = max s` and `f = f'` off `{x}` | Variation bound when the function value at the greatest element of $s$ is changed; one-sided triangle inequality for variation. |
| `eVariationOn_add_jump_endpoint` *(private)* | Same for either endpoint (least or greatest) | Wraps `eVariationOn_add_jump_greatest` for both endpoint types; used in `varphi_deriv_bv_on_Icc`. |
| `varphi_deriv_bv_on_Icc` *(private)* | `ContDiffOn ℝ 2 (ϕ_pm ν ε) [a,b] → BoundedVariationOn (deriv ϕ_pm) [a,b]` | $C^2$ implies bounded variation of the derivative on a compact interval; used in `varphi_deriv_tv`. |
| `Inu_integral` *(private)* | `∫ x : ℝ, Inu ν x = 1/ν` | The total mass of the exponential kernel equals $1/\nu$; used in the error integrals. |
| `Inu_integrable` *(private)* | `Integrable (Inu ν)` | $I_\nu$ is integrable for $\nu > 0$; prerequisite for Fourier inversion. |
| `varphi_hat_integrable` *(private)* | `Integrable (𝓕 (ϕ_pm ν ε))` | The Fourier transform of $\varphi$ is integrable; follows from the $1/x^2$ decay. |
| `varphi_fourier_inversion_re` *(private)* | `∫ x, (𝓕 (ϕ_pm ν ε) x).re = (ϕ_pm ν ε 0).re` | Fourier inversion at $0$; the total integral of the Fourier transform equals the value of $\varphi$ at the origin. |
| `varphi_deriv_integ` | `Integrable (deriv ϕ)` | The derivative is integrable, enabling FTC. |
| `varphi_ftc_left` | `x,y ∈ [-1,0] → ∫ₓʸ deriv ϕ = ϕ(y) - ϕ(x)` | FTC on the left half of the support. |
| `varphi_ftc_right` | `x,y ∈ [0,1] → ∫ₓʸ deriv ϕ = ϕ(y) - ϕ(x)` | FTC on the right half of the support. |
| `varphi_ftc_out` | `x,y ≤ -1` or `x,y ≥ 1 → ∫ₓʸ deriv ϕ = 0` | FTC outside the support: both $\phi$ and its derivative are zero there. |
| `varphi_ftc` | $\int_a^b \phi' = \phi(b) - \phi(a)$ | The Fundamental Theorem of Calculus for the spliced kernel (assembles the three cases). |
| `varphi_abs` | `AbsolutelyContinuous ϕ` | $\phi$ is absolutely continuous on any interval. |
| `ϕ_pm_deriv_zero_outside` | `t ∉ [-1,1] → (ϕ_pm ν ε)' t = 0` | Derivative vanishes outside the support. |
| `ϕ_pm_deriv_Iic_finite` | `eVariationOn (deriv ϕ) (Iic(-1)) ≠ ⊤` | The variation of the derivative on the left tail is finite (derivative is zero except at $-1$). |
| `ϕ_pm_deriv_Ici_finite` | `eVariationOn (deriv ϕ) (Ici(1)) ≠ ⊤` | Same for the right tail. |
| `varphi_deriv_tv` | `BoundedVariation (deriv ϕ)` | The derivative has bounded variation, enabling higher-order Fourier decay. |
| `varphi_fourier_decay` | $\hat{\phi}(x) = O(1/x^2)$ | $1/x^2$ decay of the Fourier transform. |

---

## 10. Technical Utilities

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `Complex.ofRealCLM.contDiff2` | `ContDiff ℝ 2 ofReal` | Smoothness of the real-to-complex coercion. |
| `Complex.contDiff_normSq` | `ContDiff ℝ n normSq` | Smoothness of the complex norm-squared function. |
| `Complex.contDiff_sinh/cosh_real` | `ContDiff ℝ n sinh/cosh` | Smoothness of complex hyperbolic functions as functions of a real variable. |
| `ContDiff.div_real_complex` | Smoothness of complex quotients | Utility for $C^2$ regularity of kernel components. |
| `w_re` / `w_re_pos` | Real part of the auxiliary variable $w$ | Technical lemmas for the growth and location of poles. |
| `w_re_pos_gen` | `z.im > -ν/(2π) → 0 < (-2πiz + ν).re` | Positivity of $w$'s real part for any $z$ strictly above the pole line (more general than `w_re_pos`). |
| `w_re_ne` | `z.im ≠ -ν/(2π) → (-2πiz + ν).re ≠ 0` | Non-vanishing of $w$'s real part when $z$ is not on the pole line. |
| `w_ne_zero_of_not_pole` | `(∀ n, z ≠ n - iν/2π) → -2πiz + ν ≠ 0` | The auxiliary variable $w$ is nonzero when $z$ avoids all poles; needed for $B$ and $\coth$. |
| `sinh_ne_zero_of_not_pole` | `sinh(w/2) ≠ 0` away from poles | Foundational lemma for the analyticity of $\Phi^\circ$ and $\Phi^\ast$. |
| `Phi_circ/star.continuousAt_imag` | Continuity on the imaginary axis | Needed for shifting integrals along the imaginary axis. |
| `integrableOn_Phi_circ/star` | `IntegrableOn` for vertical segments | Kernel integrands are well-behaved on residue-calculus paths. |
| `first/second/third_contour_integrand_holomorphicOn` | Path holomorphicity | Integrands are analytic on the chosen paths for the Residue Theorem. |

---

---

## 14. Derivative of $z \cdot \coth(z)$ — Supporting Lemmas for CH2_lemma_4_2a/b

Intermediate results for bounding $\lVert \operatorname{deriv}(z \mapsto z \coth z) \rVert$, used in `CH2_lemma_4_2a` and `CH2_lemma_4_2b`.

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `differentiableAt_coth` *(private)* | `sinh z ≠ 0 → DifferentiableAt ℂ coth z` | Differentiability of $\coth$ away from its poles; foundational for the derivative formula. |
| `differentiableAt_z_coth_z` *(private)* | `sinh z ≠ 0 → DifferentiableAt ℂ (z * coth z) z` | Differentiability of the product $z \coth z$; uses `differentiableAt_coth`. |
| `deriv_z_coth_z_eq` *(private)* | `deriv (z * coth z) z = coth z - z / sinh(z)^2` | Explicit derivative formula via product rule. |
| `deriv_z_coth_z_eq_alt` *(private)* | `deriv (z * coth z) z = (sinh(2z)/2 - z) / sinh(z)^2` | Alternative form used in the norm-squared computation for the boundary bound. |
| `normSq_sinh` *(private)* | `‖sinh z‖^2 = sinh(z.re)^2 + sin(z.im)^2` | Norm-squared of complex $\sinh$ in terms of real $\sinh$ and $\sin$; angle-addition decomposition. |
| `normSq_cosh` *(private)* | `‖cosh z‖^2 = sinh(z.re)^2 + cos(z.im)^2` | Same for complex $\cosh$. |
| `normSq_coth_eq` *(private)* | `‖coth z‖^2 = 1 + cos(2 z.im) / (sinh(z.re)^2 + sin(z.im)^2)` | Exact formula for $\|\coth z\|^2$; used to prove `tendsto_norm_coth_atTop_strip`. |
| `pi_cosh_two_mul_sub_bounds` *(private)* | `0 < π * cosh(2x) - π^2/4 - 4x^2` for all $x : \mathbb{R}$ | Positivity of a key denominator term; used to establish $\|\operatorname{deriv}\| < 1$ on the boundary ray. |
| `deriv_z_coth_z_odd` | `deriv (z ↦ z * coth z) (-w) = -deriv (z ↦ z * coth z) w` | The derivative of $z \coth z$ is an odd function; allows extending the bound from a boundary ray to the full strip by symmetry. |
| `deriv_z_coth_z_bound_boundary` | `‖deriv (z ↦ z * coth z) (↑x + (π/4) * I)‖ < 1` | Explicit $< 1$ bound on the boundary ray $\operatorname{Im}(z) = \pi/4$; the core estimate used in `CH2_lemma_4_2a`. |
| `deriv_z_coth_z_at_zero` *(private)* | `deriv (z * coth z) 0 = 0` | The derivative at the origin is zero; follows from oddness. |
| `deriv_z_coth_z_eq_deriv_B` *(private)* | `deriv (z * coth z) = deriv (B 0 (2 * ·))` | Identifies the derivative of $z \coth z$ with that of $B^0$; used in `analyticOn_deriv_z_coth_z`. |
| `strip_filter_basis` *(private)* | Filter basis for $\{z \mid R \le |z.\text{re}|\} \cap \{z \mid |z.\text{im}| \le \pi/4\}$ | Provides a concrete filter basis for the horizontal strip needed in the asymptotic limit lemmas. |
| `tendsto_sinh_atTop` *(private)* | `Tendsto Real.sinh atTop atTop` | $\sinh(x) \to \infty$ as $x \to \infty$; proved via $(e^x - 1)/2$ lower bound. |
| `tendsto_norm_coth_atTop_strip` *(private)* | `‖coth z‖ → 1` as $|z.\text{re}| \to \infty$ in the strip $|z.\text{im}| \le \pi/4$ | The norm of $\coth$ tends to $1$ at the boundary at infinity; uses `normSq_coth_eq` and `tendsto_sinh_atTop`. |
| `tendsto_z_div_sinh_sq_atTop_strip` *(private)* | `z / sinh(z)^2 → 0` as $|z.\text{re}| \to \infty$ in the strip | The correction term in the derivative formula vanishes at infinity; used in `deriv_z_coth_z_growth_bound`. |
| `analyticOn_deriv_z_coth_z` *(private)* | `AnalyticOn ℂ (deriv (z * coth z)) {z | |z.im| < π}` | The derivative is analytic on the full horizontal strip $|\text{Im}| < \pi$; used by Phragmén–Lindelöf. |
| `deriv_z_coth_z_growth_bound` *(private)* | `IsBigO` subexponential growth on the strip $|\text{Im}| < \pi/4$ | Growth bound required by the Phragmén–Lindelöf principle to transfer the boundary estimate to the interior. |
| `deriv_z_coth_z_le_one` *(private)* | `|w.\text{im}| ≤ π/4 → ‖deriv (z * coth z) w‖ ≤ 1` | Interior bound via Phragmén–Lindelöf applied between the two boundary estimates; feeds directly into `CH2_lemma_4_2a`. |
| `strip_filter_basis_gen` | Filter basis for arbitrary width `c`. | Generalized version of `strip_filter_basis`. |
| `tendsto_norm_coth_atTop_strip_gen` | `‖coth z‖ → 1` for arbitrary strip width `c`. | Generalized version of the $\pi/4$ limit. |
| `tendsto_z_div_sinh_sq_atTop_strip_gen` | `z / sinh(z)^2 → 0` for arbitrary width `c`. | Generalized correction term limit. |
| `deriv_z_coth_z_bounded_gen` | Uniform boundedness on strip of width `c`. | The core boundedness lemma for Phragmén–Lindelöf. |
| `deriv_z_coth_z_growth_bound_half_pi` | Growth bound on the $\pi/2$ strip. | Resolves the final `sorry` for the growth requirement. |

---

## 11. Limit Analysis and Arithmetic Utilities

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `tendsto_tsum_of_dominated_convergence` | `(∀ n, Tendsto (f i n) l (nhds (g n))) ∧ (‖f i n‖ ≤ bound n) ∧ Summable bound → Tendsto (∑' n, f i n) l (nhds (∑' n, g n))` | Tannery's Theorem: the limit of a sum is the sum of the limits if the terms are dominated by a summable sequence. |
| `tendsto_integral_filter_of_dominated_convergence` | `(∀ᵐ t, Tendsto (f i t) l (nhds (g t))) ∧ (‖f i t‖ ≤ bound t) ∧ Integrable bound → Tendsto (∫ t, f i t) l (nhds (∫ t, g t))` | Dominated Convergence Theorem for filter-based limits of integrals. |
| `continuousAt_const_cpow` | `x ≠ 0 → ContinuousAt (fun s ↦ x ^ s) s` | Continuity of the complex power function with a constant base and variable exponent. |
| `Complex.cpow_one` | `x ^ 1 = x` | The complex power x^1 equals x. Note: this is a propositional equality, not definitional. |
| `tsum_subtype_eq_of_support_subset` | `support f ⊆ s → ∑' x : s, f x = ∑' x, f x` | Identity for shifting a sum from a subtype to the parent type given support constraints. |
| `Equiv.tsum_eq` | `e : α ≃ β → ∑' x : β, f x = ∑' x : α, f (e x)` | Change of variables for infinite sums via equivalence. |
| `PNat.val_range` | `Set.range PNat.val = {n | 0 < n}` | The range of the coercion from positive integers to natural numbers is the set of strictly positive naturals. |
| `Nat.not_mem_range_coe_pnat_iff` | `n ∉ range PNat.val ↔ n = 0` | A natural number is not a positive integer if and only if it is zero. |

---
