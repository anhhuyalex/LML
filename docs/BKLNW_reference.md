# BKLNW API Reference

Lean definitions, lemmas, and blueprint pointers for the logarithmic decay and interval bounds machinery in `PrimeNumberTheoremAnd/BKLNW.lean`.

---

## Glossary

Core symbols used throughout the file.

| Symbol | Lean Type | Mathematical Definition | Notes |
| :--- | :--- | :--- | :--- |
| `Inputs` | `Structure` | Parameter container for bounds | Stores $\alpha$, $x_1$, $\varepsilon(b)$ bounds, and handles $a_1$, $a_2$ parameters. |
| `a₁ b` | `ℝ → ℝ` | $a_1(b)$ parameter | Piecewise parameter depending on whether $b \le 2\log x_1$. |
| `a₂ b` | `ℝ → ℝ` | $a_2(b)$ parameter | Parameter defined as $(1 + \alpha) \max(f(e^b), f(2^{\lfloor b/\log 2 \rfloor + 1}))$. |
| `B k n a ε b b'` | `ℝ` | Supremum bound over $[e^b, e^{b'}]$ | Defined as $\sup_{x \in [e^b, e^{b'}]} \left( \sum_{\ell=1}^n a_{\ell} (\log x)^k x^{-\frac{\ell}{\ell+1}} + \varepsilon(b) (\log x)^k \right)$. |
| `Btilde k n a ε b b'` | `ℝ` | Bounding auxiliary constant | Defined as $b^k \sum_{\ell=1}^n a_{\ell} \exp\left(-\frac{\ell b}{\ell+1}\right) + \varepsilon(b) (b')^k$. |
| `B_8_1 k b b'` | `ℝ` | Explicit $B_k(b, b')$ bound | Defined as $a_1(b) b^k e^{-b/2} + a_2(b) b^k e^{-2b/3} + (b')^k \varepsilon(b)$. |
| `B_8_1' k b₀` | `ℝ` | Finite maximum over Grid | The supremum/maximum of $B_k(b, \text{next}(b))$ over Table 10 subintervals. |
| `C_bk b c C c₀ k` | `ℝ` | $\mathcal{C}_{b,k}$ constant | Bound constant for $\theta(x)$ at small-to-medium $x$. |
| `table_10_entries` | `Finset ℝ` | Grid of points in Table 10 | Real numbers indicating subinterval endpoints for numerical verification. |
| `table_10_next b` | `ℝ` | Step successor helper | Smallest table entry strictly greater than $b$. |

---

## Main Results

| Name | Statement | Role |
| :--- | :--- | :--- |
| `thm_5` | $\psi(x) - \theta(x) \le a_1 x^{1/2} + a_2 x^{1/3}$ | General difference bound between the Chebyshev functions under custom inputs. |
| `cor_5_1` | $\psi(x) - \theta(x) \le a_1 x^{1/2} + a_2 x^{1/3}$ | Difference bound using default parameters (inputs verified by LeanCert). |
| `lem_6` | $E_\theta(x) \le \mathcal{A}_k(b) / \log^k x$ | Logarithmic decay bound for large $x$ based on Lemma 6. |
| `cor_14_1` | Converts $E_\psi$ bound to $E_\theta$ bound | Propagates logarithmic error bounds from the $\psi$ function to the $\theta$ function. |
| `bklnw_lemma_8` | $\| \theta(x) - x \| \le B_k x / \log^k x$ on $[e^b, e^{b'}]$ | Interval-based error bounding using supremum calculations. |
| `bklnw_eq_3_11` | $B_k \le \tilde{B}_k$ | Auxiliary monotonicity inequality simplifying supremum calculations. |
| `bklnw_cor_8_1a` | Bounds $\| \theta(x) - x \|$ on subintervals | Squeezes the error on localized intervals via $B_k(b,b')$. |
| `bklnw_cor_8_1b` | Bounds $\| \theta(x) - x \|$ on global $[e^{b_0}, e^K]$ | Integrates local subintervals using a finite grid maximum to achieve global coverage. |
| `bklnw_lemma_9` | Lower bounds $\theta(x)$ using $\psi(x)$ at small $x$ | Prepares small-$x$ bounds based on a.e. Chebyshev difference constraints. |
| `bklnw_corollary_9_1` | Bounds $\theta(x)$ with $\mathcal{C}_{b,k}$ | Corollary giving explicit lower bounds for small-to-medium ranges. |

---

## 1. Chebyshev Difference and Default Inputs

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `thm_5` | `ψ x - θ x ≤ I.a₁ b * x^(1/2) + I.a₂ b * x^(1/3)` | Bounds the difference between $\psi$ and $\theta$ in terms of $x^{1/2}$ and $x^{1/3}$ under chosen scaling parameters. |
| `cor_5_1` | `ψ x - θ x ≤ a₁ b * x^(1/2) + a₂ b * x^(1/3)` | Specializes the difference theorem to default inputs verified by interval arithmetic. |
| `table_cor_5_1` (def) | `List (ℝ × ℝ × ℕ)` | Verification parameters for table entries. |

---

## 2. Logarithmic Decay at Large $x$

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `g_decreasing_interval` | `v ^ A * exp (-C * sqrt v) ≤ u ^ A * exp (-C * sqrt u)` | Proves that the auxiliary function $g(t) = t^A e^{-C\sqrt{t}}$ decreases beyond $t \ge 4A^2/C^2$. |
| `lem_6` | `Eθ x ≤ A / (log x) ^ k` | Establishes logarithmic decay bounds for $|\theta(x) - x|/x$ using the monotonicity of $g(t)$. |
| `cor_14_1` | `Eθ.classicalBound A' B C R (exp x₀)` | Transforms an asymptotic bound for $\psi$ into a corresponding asymptotic bound for $\theta$. |

---

## 3. Supremum Bounds on Intervals

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `B` (def) | `iSup (fun x ↦ ...)` | Computes the supremum of the scaled error terms on the interval $[e^b, e^{b'}]$. |
| `Btilde` (def) | `b^k * (∑ ...) + ε b * b'^k` | A simplified bounding constant for the supremum, avoiding pointwise calculation. |
| `bklnw_lemma_8` | `abs (θ x - x) ≤ B k n a ε b b' * x / (log x)^k` | Core interval-bounding result using local supremum bounds. |
| `bklnw_lemma_8_term_eq` | `a_ℓ * x^(1/(ℓ+1)) = a_ℓ * log x^k * x^(-ℓ/(ℓ+1)) * (x / log x^k)` | Helper lemma isolating the algebraic factorization. |
| `bklnw_lemma_8_bound_le_B` | `(∑ ...) + ε b * (log x)^k ≤ B k n a ε b b'` | Helper lemma demonstrating that interval evaluations are strictly bounded by the supremum. |
| `bklnw_eq_3_11` | `B k n a ε b b' ≤ Btilde k n a ε b b'` | Shows that the supremum $B_k$ is bounded by the monotonic auxiliary bound $\tilde{B}_k$. |
| `bklnw_eq_3_11_deriv_nonpos` | `deriv (fun y ↦ y ^ k * exp (- ((ℓ:ℝ) / (ℓ + 1)) * y)) y ≤ 0` | Pointwise derivative non-positivity bound for the term's exponent. |
| `bklnw_eq_3_11_antitone` | `AntitoneOn (fun y ↦ y ^ k * exp (- ((ℓ:ℝ) / (ℓ + 1)) * y)) (Set.Ici b)` | Proof of monotonicity for the exponent term. |
| `bklnw_eq_3_11_term_le` | `(log x)^k * x ^ (-(ℓ:ℝ) / (ℓ + 1)) ≤ b ^ k * exp (- (ℓ:ℝ) * b / (ℓ + 1))` | Pointwise bound for individual summation terms. |

---

## 4. Grid Subintervals and Numerical Bounds

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `B_8_1` (def) | `Inputs.default.a₁ b * b^k * exp (-b / 2) + ...` | Analytical expression for $B_k(b, b')$ inside subintervals. |
| `B_8_1'` (def) | `if S.Nonempty then S.sup' ... else 0` | Computes the finite grid supremum over the active subintervals of Table 10. |
| `bklnw_cor_8_1a` | `|θ x - x| ≤ (B_8_1 k b b') * x / (log x)^k` | Squeezes the localized error bounds inside any subinterval $[e^b, e^{b'}]$ on the grid. |
| `bklnw_cor_8_1b` | `|θ x - x| ≤ (B_8_1' k b₀) * x / (log x)^k` | Combines localized bounds on grid pieces to yield global error bounds up to $e^K$. |
| `table_10_coverage` | `∃ b ∈ table_10_entries, b₀ ≤ b ∧ b ≤ y ∧ y ≤ table_10_next b` | Technical lemma showing that any evaluation point on the log scale is covered by some grid subinterval. |

---

## 5. Small and Very Small $x$ Bounds

| Name | Lean Statement (Simplified) | Natural Language Explanation |
| :--- | :--- | :--- |
| `bklnw_eq_3_17` | `θ x < x - 0.05 * sqrt x` | Squeeze bounds on $\theta(x)$ for very small arguments $1 \le x \le 10^{19}$. |
| `bklnw_eq_3_18` | `θ x - x ≤ 0` | Establishes non-positivity of $\theta(x)-x$ for very small $x$. |
| `bklnw_lemma_9` | `θ x ≥ x - (C + 1) * x^(1/2) - ...` | Computes a lower bound for $\theta(x)$ using $\psi(x)$ bounds when $x \in [u^2, v]$. |
| `bklnw_corollary_9_1` | `θ x ≥ x - C_bk b c C RS_prime.c₀ k * x / (log x)^k` | Squeezes the lower bounds using the explicit parameter $\mathcal{C}_{b,k}$. |
