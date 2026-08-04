# Audit: Renormalization.md §§"Probability, Correlation and Statistics" and "Nearly-Gaussian Distributions" vs. the Lean formalization

This note records a statement-level comparison of `docs/Renormalization.md`
lines 352-981 — the two sections informally referred to as "chapters 2 and 3"
of the *Pretraining* chapter (`\section{Probability, Correlation and
Statistics, and All That}`, starting line 352, and `\section{Nearly-Gaussian
Distributions}`, starting line 582, running to the end of the file at line
981) — against every `.lean` file in
`LeanMachineLearning/Optimization/Renormalization/`, in two passes: first
`{Basic,Cumulant,Gaussian,Perturbation,Quartic,Finpartition}.lean` (the files
that directly formalize §§2-3's definitions), then the remaining
application/downstream files — `InducedLaw.lean`, `Initialization.lean`,
`MLPInitialization.lean`, `Network.lean`, `Convolution.lean`,
`ParameterizedMLP.lean`, `Activation.lean`, `DeepLinear.lean`, and
`DeepLinear/{Asymptotics,Basic,Fluctuations,GaussianLayer,Limits,Moments}.lean`
— checked in a second pass (see "Extended audit" below) specifically to make
sure none of §§2-3's still-missing items are hiding there instead, since
those files consume the Cumulant/Gaussian API to formalize later chapters
(deep linear networks, MLP initialization) and could plausibly contain a
restated or specialized version of a §§2-3 claim.

The tail of the document (lines 951-981, i.e. "after line 950") turns out to
contain no new equations — it is the closing paragraph of
`\subsubsection{Nearly-Gaussian actions}`, restating that the quartic action
(truncation at $k=2$) is the standard model for finite-width networks and that
truncating further ($k=2$ vs. $k=3$) is a quantitative, not qualitative,
difference. The substantive content to check against is therefore all of
§§2-3 (lines 352-950 hold essentially all the definitions/theorems; 951-981
is prose commentary with no independent formal content).

## Outcome

**Faithfully translated, sorry-free:** the moment/cumulant combinatorics.
`Finpartition.cumulantTransform` (`Finpartition.lean:72-74`) implements the
general Möbius/subdivision-sum definition of the $M$-th cumulant exactly as
in eq. "cumu" (line 479-483 of the doc), and `Cumulant.lean` derives the
$M=1$ case (`jointCumulant_one`, `Cumulant.lean:399-408` — mean, eq. C1),
$M=2$ case (`jointCumulant_two`, `Cumulant.lean:612-625`, tied to Mathlib's
`covariance` via `jointCumulant_two_eq_covariance`, `Cumulant.lean:630-634` —
eq. C2), and the centered $M=4$ case (`jointCumulant_four_of_centered`,
`Cumulant.lean:1087-1097` — eq. C4) from that single generic definition, sorry-free,
exactly mirroring the doc's own presentation (state the general inductive
definition, then specialize to $M=1,2,4$). The converse moment-in-terms-of-cumulants
direction is also proved sorry-free
(`jointMoment_eq_sum_partition_jointCumulant`, `Cumulant.lean:292-308`).
These results hold for a general `Fintype ι` index (not fixed dimension) and,
in the Gaussian case, for general Banach-space-valued observables via
`StrongDual ℝ E` (`Gaussian.lean:1433-1460`) — strictly more general than the
doc's finite-dimensional $\mathbb{R}^n$ setting.

**Faithfully translated as statements, but not yet proved (`sorry`):** the
main perturbative results of the quartic-action section. `Quartic.lean`
states, with hypotheses matching the doc's normalizability/integrability
needs, the first-order-in-$\epsilon$ partition function
(`partitionFunction_isBigO`, `Quartic.lean:163-171`, matching eq.
"first-order-perturbation-theory-partition-function" with the $1/8=3/4!$
coefficient), the shifted two-point correlator (`twoPoint_isBigO`,
`Quartic.lean:181-191`, matching eq. "second-moment-interaction"), and the
key connected four-point result (`fourthCumulant_isBigO`,
`Quartic.lean:204-219`, matching eq. "single-variable-connected-four-point":
$\langle z_1z_2z_3z_4\rangle_{\text{conn}} = -\epsilon\sum V K K K K + O(\epsilon^2)$).
All three carry `sorry`. Likewise, the doc's inductive claim that all
$M$-point connected correlators vanish for $M>2$ under a Gaussian
distribution is stated in full generality
(`jointCumulant_dual_eq_zero`/`jointCumulant_centered_dual_eq_zero`,
`Gaussian.lean:1518-1591`, for arbitrary $n\ne 2$) but the proof bottoms out
in two `sorry`s (`cumulantTransform_wick_eq_zero`, `Gaussian.lean:1502-1505`;
`jointCumulant_add_const`, `Gaussian.lean:1507-1516`).

**Missing entirely:** everything organized around the *action* $S(z)$ as an
explicit object, and everything about the general even-order coupling
hierarchy. `Perturbation.lean` reframes the doc's "deform the Gaussian action
by a small potential" idea as multiplicative tilting of an arbitrary base
measure (`deform μ V ε := μ.tilted (fun x ↦ -ε * V x)`,
`Perturbation.lean:43-44`) — mathematically the same construction, but there
is no Lean object corresponding to $S(z) = \tfrac12 K^{\mu\nu}z_\mu z_\nu +
\ldots$, no derivation that the quadratic action *is* the Gaussian
distribution with $Z=\sqrt{\det(2\pi K)}$ (the Gaussian measure is imported
wholesale from Mathlib and used as an opaque base measure), and no bra-ket
notation `⟨·⟩_K`. There is also no `NearlyGaussian` definition anywhere in
the directory (`grep -i nearlygaussian` returns nothing), no general
nearly-Gaussian action ansatz $S = \text{quadratic} + \sum_{m=2}^k
\frac{1}{(2m)!}s^{\mu_1\cdots\mu_{2m}}z_{\mu_1}\cdots z_{\mu_{2m}}$ (only the
$m=2$/quartic case is modeled, via the `QuarticCoupling` structure,
`Quartic.lean:42-46`), and — most notably — **no formalization of the
hierarchical-scaling claim** $\langle z_{\mu_1}\cdots z_{\mu_{2m}}\rangle_{\text{conn}}
= O(\epsilon^{m-1})$ (eq. "connected-correlator-hierarchy", doc line 940).
This is arguably the single most load-bearing claim in §3, since it is what
licenses truncating the action at fixed order and is explicitly what the
later neural-network chapters lean on. Nothing analogous to it exists in the
directory; a structurally similar but distinct hierarchy (in the
hidden-width expansion parameter of deep linear networks, not the
$\epsilon$-quartic-coupling expansion of this section) appears downstream in
`DeepLinear/Fluctuations.lean`, but that is chapter-specific content, not a
formalization of the general claim.

Also missing: the M=6 combinatorial decomposition example (eq.
"six-point-moment-in-terms-of-connected"/"C6", doc lines 513-529) — in
principle a direct instantiation of the already-proved general
`cumulantTransform` machinery at `Fin 6`, but no such specialization is
written; the parity-symmetry consequence that all odd moments and odd
connected correlators vanish (doc lines 457-459) — only the atomic building
block exists (`integral_eq_zero_of_odd`, `Basic.lean:114-129`, sorry-free,
an odd observable integrates to zero against a sign-flip-invariant measure),
but it is never applied to products of coordinates or to cumulants anywhere
in the directory; the statistical-independence-via-diagonalization argument
(doc lines 807-817) — independence itself is present via Mathlib's
`IndepFun`, and the converse direction (independence across a split implies
vanishing joint cumulant, `jointCumulant_eq_zero_of_indepFun_split`,
`Cumulant.lean:2070-2077`) is present but itself depends transitively on a
`sorry` (`cumulantTransform_split_trace_fiber_regrouping`,
`Cumulant.lean:1843-1870`), while the forward direction (nonzero quartic
coupling ⇒ non-factorization; orthogonal diagonalization of a Gaussian
covariance ⇒ product of independent single-variable Gaussians) has no
counterpart; and the $n=1$ self-interaction remark (doc lines 826-830) is
trivially derivable by specializing `twoPoint_isBigO` to a one-element index
type but is not written down anywhere.

The full four-point correlator (not just its connected combination) is also
never stated as its own lemma — the doc computes it explicitly (eq.
"full-four-point-intro", lines 741-752) as an intermediate step en route to
the connected result, but `Quartic.lean` jumps straight to the connected
four-point statement.

## Item-by-item map

Numbering follows my own enumeration of every definition/claim in lines
352-981 of the doc, grouped by section.

**§"Probability, Correlation and Statistics" (lines 352-581):**

1. General expectation `E[O(z)]` (line 375-378) — not reified as a named
   object; used inline via Mathlib's Bochner integral throughout.
2. $M$-point correlator/moment (line 396-399) — `blockMoment`/`jointMoment`,
   `Basic.lean:37,41`, sorry-free, general `Fintype ι`.
3. Taylor expansion of `E[O(z)]` in moments, eq. "observables-and-moments"
   (400-404) — not found.
4. First cumulant = mean, eq. C1 (444-448) — `jointCumulant_one`,
   `Cumulant.lean:399-408`, sorry-free.
5. Second cumulant = covariance, eq. C2 (449-454) — `jointCumulant_two`,
   `Cumulant.lean:612-625`, plus `jointCumulant_two_eq_covariance`,
   `Cumulant.lean:630-634`, both sorry-free.
6. Parity ⇒ odd moments/cumulants vanish (457-459) — only the atomic building
   block `integral_eq_zero_of_odd`, `Basic.lean:114-129` (sorry-free), never
   specialized to products of coordinates or to cumulants.
7. Fourth cumulant / connected 4-point, eq. C4 (462-467) —
   `jointCumulant_four_of_centered`, `Cumulant.lean:1087-1097`, sorry-free,
   for centered families (matches the doc's actual usage, which is always
   under the parity restriction).
8. Connected 4-point vanishes for Gaussian, eq. C4-gaussian (468-472) — an
   instance ($n=4$) of item 12's general theorem; inherits its `sorry`.
9. General inductive/Möbius definition of the $M$-th cumulant, eq. "cumu"
   (476-485) — `Finpartition.cumulantTransform`, `Finpartition.lean:72-74`,
   sorry-free; converse direction
   `jointMoment_eq_sum_partition_jointCumulant`, `Cumulant.lean:292-308`,
   sorry-free.
10. Recovering $M=2$ and parity-restricted $M=4$ from the general definition,
    eq. C4-reversed (491-511) — items 4/5/7 above are exactly these
    specializations, sorry-free.
11. $M=6$ combinatorial decomposition, eqs.
    "six-point-moment-in-terms-of-connected"/C6 (513-529) — not found; no
    `Fin 6` specialization of the general cumulant machinery exists (the only
    `Fin 6` hit is the unrelated raw-Gaussian-moment Wick theorem,
    `Gaussian.lean:1463-1467`).
12. All $M$-point connected correlators vanish for $M>2$, Gaussian, by
    induction (531-534) — stated in full generality
    (`jointCumulant_dual_eq_zero`/`_centered_dual_eq_zero`,
    `Gaussian.lean:1518-1591`, arbitrary `n ≠ 2`, works for
    Banach-space-valued observables), but proof-incomplete: depends on
    `cumulantTransform_wick_eq_zero` (`Gaussian.lean:1502-1505`, `sorry`) and
    `jointCumulant_add_const` (`Gaussian.lean:1507-1516`, `sorry`).
13. Definition of "nearly-Gaussian distribution" (537-542) — not found; no
    `nearlyGaussian` identifier anywhere in the directory.

**§"Nearly-Gaussian Distributions" (lines 582-981):**

14. Action representation $p\propto e^{-S}$, $S=-\log p$ up to constant
    (597-616) — not found as an explicit object; `Perturbation.lean` works
    one level down via multiplicative tilting of an arbitrary base measure
    (`deform`, `Perturbation.lean:43-44`) rather than an explicit $S(z)$.
15. Partition function / normalization, $p=e^{-S}/Z$ (607-616) — partially
    present via the generic-deformation vocabulary: `partitionFunction`,
    `Perturbation.lean:47-48`; `integral_deform`, `Perturbation.lean:69-75`,
    sorry-free, gives the corresponding normalized-expectation identity
    relative to an arbitrary base measure (not derived from an explicit
    quadratic+quartic $S$ built from scratch).
16. Quadratic action ≡ Gaussian, $Z=\sqrt{\det(2\pi K)}$ (635-645) — not
    found; `multivariateGaussian` is imported wholesale from Mathlib and used
    as an opaque base measure, its density/normalization never re-derived
    here.
17. Bra-ket notation $\langle O(z)\rangle_K$ (650-661) — not found; Gaussian
    expectations are written as plain integrals against
    `multivariateGaussian 0 K`.
18. Quartic action definition, totally symmetric $V$, $1/4!$ factor
    (676-690) — `QuarticCoupling` structure with `coeff_perm` symmetry axiom
    and `potential`, `Quartic.lean:42-54`, sorry-free as a definition (only
    the quartic potential half; the quadratic piece lives separately in the
    supplied covariance `K`).
19. First-order-in-$\epsilon$ partition function, eq.
    "first-order-perturbation-theory-partition-function" (707-723) —
    `partitionFunction_isBigO`, `Quartic.lean:163-171`, `sorry`; matches the
    doc's $1/8$ coefficient.
20. First-order-in-$\epsilon$ two-point correlator, eq.
    "second-moment-interaction" (725-736) — `twoPoint_isBigO`,
    `Quartic.lean:181-191`, `sorry`; matches the doc's shifted-covariance
    formula.
21. Full (not connected) four-point correlator to first order, eq.
    "full-four-point-intro" (741-752) — not found as a standalone statement;
    only the connected combination (item 22) is proved.
22. Connected 4-point $= -\epsilon\sum V K K K K + O(\epsilon^2)$, eq.
    "single-variable-connected-four-point" (766-774) —
    `fourthCumulant_isBigO`, `Quartic.lean:204-219`, `sorry`; exact match to
    the doc's formula via `fourPointContraction`, `Quartic.lean:75-77`.
23. Statistical independence $p(x,y)=p(x)p(y)$; diagonal-covariance Gaussian
    factorizes (807-817) — independence itself is Mathlib's `IndepFun`; the
    diagonalization-implies-factorization direction is not proved generically
    anywhere (the one instance, `map_evalBatch_layerGaussianInit`,
    `InducedLaw.lean:323-328`, is a downstream MLP-layer application whose
    independence comes from disjoint parameter rows by construction, not from
    diagonalizing a general covariance).
24. Nonzero coupling ⇒ non-factorization (819-825) — only the
    converse/contrapositive machinery is present
    (`jointCumulant_eq_zero_of_indepFun_split`, `Cumulant.lean:2070-2077`),
    itself depending transitively on a `sorry`
    (`cumulantTransform_split_trace_fiber_regrouping`,
    `Cumulant.lean:1843-1870`).
25. Self-interaction at $n=1$ (826-830) — not found; trivially derivable by
    specializing item 20 to a one-element index type but not written.
26. General nearly-Gaussian action ansatz, eq.
    "schematic-action-decomposition" (880-887) — not found; `QuarticCoupling`
    only covers the $m=2$ term, no general even-order-$2m$ coupling
    structure exists.
27. Definition: couplings parametrically small, eq. "parametrical-small-world"
    (902-905) — not found.
28. Dimensional-analysis footnote (906-913) — not found (expected; not the
    kind of claim that gets formalized).
29. Hierarchical scaling $O(\epsilon^{m-1})$, eq.
    "connected-correlator-hierarchy" (937-943) — **not found**. This is the
    most consequential gap: it is the claim that licenses truncating the
    action, and it is what the later neural-network chapters directly invoke.
    (Re-checked against `DeepLinear/*` in the extended audit below — a
    content-level $m=2,3$ special case exists there for deep linear
    networks specifically, but it is not a formal instance of any general
    theorem, since no such general theorem exists to specialize from.)
30. Truncation validity / quartic action as standard model, "quantitative not
    qualitative" remark (947-954, i.e. the material after line 950) — not
    found; a meta-level modeling claim with no Lean counterpart (reflected
    only implicitly by the fact that `Quartic.lean` exists and no
    `Sextic.lean` does).

## Material found beyond the doc's §§2-3

- A fully general, coordinate-free Wick/Isserlis theorem for
  Banach-space-valued Gaussian measures
  (`IsGaussian.integral_prod_centered_dual_eq_wick`, `Gaussian.lean:1433-1460`,
  sorry-free) — strictly more general than anything the doc states in this
  chapter (which stays in finite dimensions).
- A full recursive Wick-sum API (`wick`, `pairWeight`, `wick_erase`,
  `wick_eq_zero_of_odd_card`, `Gaussian.lean:43-111`, sorry-free) underlying
  items 8 and 12.
- Multilinearity/permutation-invariance of joint cumulants
  (`jointCumulant_add`, `jointCumulant_smul`, `jointCumulant_perm`,
  `Cumulant.lean:1136-1144,1299-1411`, sorry-free) — standard cumulant
  properties not spelled out in the doc's prose but implicitly used.
- An independent CGF-derivative-based definition of scalar cumulant
  (`cumulant`, `Cumulant.lean:2080`) with an equivalence theorem to
  `jointCumulant` (`cumulant_eq_jointCumulant`, `Cumulant.lean:2127-2130`,
  `sorry`).
- General "external legs + quartic vertex" Wick-contraction building blocks
  in `Quartic.lean` (`integral_coordinateProduct_mul_potential_eq_sum_wick`,
  `integral_potential`, `integral_coord_mul_potential`,
  `integral_fourCoords_mul_potential`, lines 105-151, all `sorry`) — a
  Feynman-diagram-style generalization (arbitrary number of external legs)
  beyond what the doc explicitly writes out for the four-point case.
- `DeepLinear/*` applies this API to deep linear networks (connected
  correlators in terms of hidden-width corrections, large-width limits) —
  downstream chapter content, not part of §§2-3, but the primary consumer of
  the machinery audited here.

## Extended audit: the remaining files (`InducedLaw.lean`, `Initialization.lean`, `MLPInitialization.lean`, `Network.lean`, `Convolution.lean`, `ParameterizedMLP.lean`, `Activation.lean`, `DeepLinear/*`)

Second pass, covering every `.lean` file in the directory not already audited
above, checked against the same 30-item list, again specifically re-checking
items 1, 3, 11, 13, 14, 16, 17, 21, 23-24 (forward direction), 25, 26, 27, 29,
30 (still "not found" after pass one) and items 6, 15, 23-24 (backward
direction) (marked "partially found" after pass one), in case they turn out
to be formalized here instead.

**Confirmed still not found anywhere in these 14 files, no new material:**
items 1 ($E[O(z)]$ as a named object), 3 (Taylor expansion in moments), 11
(M=6 combinatorics), 13 (`NearlyGaussian` definition — reconfirmed by a fresh
grep for `nearlygaussian|nearly_gaussian|isnearlygaussian|smallcoupling|weaklycoupled`
across the whole directory, zero hits), 14 (action $S(z)$ as an object), 16
(quadratic action $\equiv$ Gaussian with $Z=\sqrt{\det 2\pi K}$), 17
(bra-ket notation), 21 (full, non-connected, four-point correlator to
$O(\epsilon)$), 25 ($n=1$ self-interaction), 26 (general even-order-$2m$
action ansatz), 27 (parametric-smallness definition), 30 (truncation
validity / quartic-as-standard-model remark). `Network.lean`,
`Convolution.lean`, `ParameterizedMLP.lean`, `MLPInitialization.lean`,
`InducedLaw.lean`, and `Activation.lean` contribute nothing to any of these
items at all — they are pure architecture (typed MLP/`DenseLayer`/`Conv2D`
shapes), induced-law/kernel plumbing, and scalar-activation analysis
(smoothness, asymptotics, homogeneity), with no overlap with §§2-3's
probability-theory content.

**Item 6 (parity ⇒ vanishing, applied to products of coordinates) gains one
concrete instance:** `DeepLinear/Moments.lean:55-59`,
`jointMoment_outputLaw_odd` (`sorry`) states that a product of $2m+1$
output-coordinate factors integrates to zero against the deep-linear output
law — a genuine multi-coordinate odd-moment vanishing statement, unlike the
single-observable `integral_eq_zero_of_odd` in `Basic.lean`. It is
deep-linear-specific (proved, when the `sorry` is filled, via conditioning on
the penultimate layer, not via the general sign-flip argument) and doesn't
change the core verdict that the general statement (applied to an arbitrary
nearly-Gaussian $z_\mu$) is absent.

**Item 23 (statistical independence), backward/by-construction direction,
gains several more sorry-free instances**, all in `Initialization.lean`:
`iIndepFun_bias_layerGaussianInit` (201-221), `iIndepFun_weight_layerGaussianInit`
(229-277), `indepFun_weight_bias_layerGaussianInit` (285-295),
`iIndepFun_layerCoordinate_layerGaussianInit` (313-369) — joint independence
of every scalar weight/bias, all sorry-free. These are all "independence by
construction" (disjoint coordinate blocks of a product measure), the same
flavor as the one instance already noted in pass one
(`InducedLaw.lean:323-328`). None of this touches the still-missing
**forward** direction — an arbitrary Gaussian's covariance being
diagonal/diagonalizable implies it factors into independent single-variable
Gaussians — which remains genuinely unformalized anywhere in the directory.

**Item 24 (nonzero coupling ⇒ non-factorization):** no new material in these
14 files; `jointCumulant_eq_zero_of_indepFun_split` (`Cumulant.lean`) is not
referenced or extended here.

**Item 29 (hierarchical scaling $O(\epsilon^{m-1})$) — the critical item,
looked at closely:** `DeepLinear/Fluctuations.lean` has exact, sorry-free,
purely algebraic identities relating raw moments to connected correlators for
a deep linear network — `fourPointAmplitude_eq` (37-41),
`jointCumulant_four_outputLaw` (50-56, `sorry`),
`sixthCumulantAmplitude_eq` (122-129, sorry-free `ring` identity),
`correlatorAmplitude_append` (137-145, sorry-free). The actual
asymptotic/order-counting content lives in `DeepLinear/Asymptotics.lean` and
`DeepLinear/Limits.lean` (every non-algebraic lemma there is `sorry`):
`tendsto_fourthCumulantAmplitude_doubleScaling` (`Limits.lean:120-131`)
gives the connected 4-point coefficient $\to (e^{2r}-1)q^2$, i.e. leading
order $O(r)=O(\epsilon^{2-1})$, and
`tendsto_sixthCumulantAmplitude_doubleScaling` (`Limits.lean:133-140`) gives
the connected 6-point coefficient $\to (e^{6r}-3e^{2r}+2)q^3 = O(r^2) +
\ldots = O(\epsilon^{3-1})$, in the depth/width double-scaling limit $r =
\lim(\text{depth}/\text{width})$. So for the two concrete cases $m=2,3$ the
deep-linear connected-correlator coefficient genuinely does scale as the
$(m-1)$-th power of the network's own small parameter, the same shape as eq.
"connected-correlator-hierarchy" — a real, content-level instance of the
claim. **However this is not a formal instance/specialization of anything**:
it is derived from scratch by direct Gaussian-conditioning and Wick-theorem
computation on the deep-linear model specifically, only for $m=2,3$ (no
general-$m$ connected-scaling lemma exists), and there is no general §3
theorem, action-ansatz type, or `NearlyGaussian` definition anywhere in the
repository for it to specialize *from*. Every one of the order-counting
lemmas in this chain (`Asymptotics.lean`'s four lemmas,
`Limits.lean`'s `Tendsto` theorems) is `sorry`. Verdict: item 29 stays
**not found** as a general theorem; the closest thing to it is this
disconnected, `sorry`-heavy, $m\in\{2,3\}$-only structural analogue specific
to deep linear networks, which is consistent with (but not derived from) the
doc's general claim, and is itself sourced from a *later* chapter of the book
(the informal-proof comments in `Limits.lean`/`Moments.lean` cite
`docs/Renormalization.md` sections such as `sec:higher-point-functions_DLN`
and equation `eq:deep-linear-recursion-relation-2m`, which do not appear
anywhere in the lines 352-981 audited here — i.e. even the doc-side source
for this material lives past what this note covers).

No hidden general-$k$ nearly-Gaussian formalization, and no restatement of
any other still-missing item, was found anywhere in `Network.lean`,
`Activation.lean`, `ParameterizedMLP.lean`, `MLPInitialization.lean`,
`InducedLaw.lean`, or `Convolution.lean`.

## Bottom line

The **combinatorial skeleton** of §2 (moment-cumulant Möbius formula and its
$M=1,2,4$ specializations) is faithfully and completely translated,
sorry-free, and in fact generalized (arbitrary index type, Banach-valued
observables in the Gaussian case). The **perturbative content** of §3 (the
three key quartic-action formulas) is faithfully *stated*, with hypotheses
matching the doc's normalizability/integrability needs, but every one of
those proofs is a `sorry`. The **organizing "action" formalism** of §3 (the
functional $S(z)$, its identification with the Gaussian/quartic
distributions, bra-ket notation, and the general even-order coupling
hierarchy $s^{\mu_1\cdots\mu_{2m}}$) has no counterpart at all — the project
works one level down, directly with base measures and multiplicative
tiltings, which suffices for the quartic-specific results but leaves the
general nearly-Gaussian *definition* and its defining
hierarchical-scaling property ($O(\epsilon^{m-1})$, item 29) completely
unformalized. Having now also audited every downstream/application file
(`DeepLinear/*`, `InducedLaw.lean`, `Initialization.lean`,
`MLPInitialization.lean`, `Network.lean`, `Convolution.lean`,
`ParameterizedMLP.lean`, `Activation.lean`), this conclusion is unchanged: no
file in the directory contains a `NearlyGaussian` definition, a general
even-order action ansatz, or a general-$m$ hierarchical-scaling theorem.
`DeepLinear/Fluctuations.lean`+`Asymptotics.lean`+`Limits.lean` independently
re-derive the $m=2,3$ special cases of exactly this scaling law for deep
linear networks specifically (all `sorry`), which is reassuring evidence of
mathematical consistency across the project but does not close the gap —
there is still no Lean object representing §3's general claim for the
Pretraining chapter to formally connect to. Since that scaling property is
the technical content the rest of the book leans on to justify truncating at
the quartic order, it remains the highest-priority gap to close next; a
second, more tractable priority is discharging the three `Quartic.lean`
`sorry`s (items 19/20/22), since their statements are already faithful and
complete.

## To-do list: what still needs to be formalized

A quick note on vocabulary before the list: in Lean, when a theorem is
written down but its proof is replaced with the placeholder `sorry`, the
statement exists and compiles, but nobody has actually proved it — it's an
IOU. Below, "formalized" means "written down as a Lean definition or
theorem statement," and "proved" means the proof is complete, with no
`sorry` left in it (and no `sorry` in anything it depends on).

### High priority

1. **Write down what "nearly-Gaussian" means.** The book defines a
   nearly-Gaussian distribution as one where all the connected correlators
   (cumulants) beyond the second one are small. There is currently no Lean
   definition anywhere in the project that captures this — no structure or
   predicate saying "this distribution is nearly-Gaussian." This is the
   piece that everything else below is missing a home for.

2. **Prove the hierarchical scaling law.** This is the book's central claim
   in this chapter: the connected 2m-point correlator shrinks like
   epsilon^(m-1) as the network gets wide — so the four-point correlator is
   order epsilon, the six-point is order epsilon-squared, and so on. This is
   the fact that justifies keeping only the quartic term and dropping
   everything higher. Nothing in the project states or proves this in
   general.

   There is a related, narrower result specifically for deep linear
   networks, in `DeepLinear/Fluctuations.lean`, `Asymptotics.lean`, and
   `Limits.lean`. It shows the same epsilon-to-the-(m-1) pattern, but only
   works it out for m=2 and m=3 (not a general m), applies only to deep
   linear networks rather than nearly-Gaussian distributions in general, and
   every part of it that isn't pure algebra is currently a `sorry`. Once
   item 1 exists, this deep-linear result would be a good test case to
   generalize and connect back to the main claim.

3. **Prove the three quartic-action results that are currently just
   placeholders.** `Quartic.lean` already has the correct statements for:
   how the partition function changes to first order in epsilon; how the
   two-point correlator (covariance) shifts to first order; and the formula
   for the connected four-point correlator to first order. All three are
   marked `sorry` — the statements match the book, they just need actual
   proofs. Since the statements are already right, this is probably the
   easiest big win: finishing proofs of correct statements is usually less
   work than writing new statements from scratch.

### Medium priority

4. **Represent the action itself, S(z), as an explicit Lean object.** The
   book organizes this whole chapter around the "action" function S(z),
   where the probability distribution is proportional to e^(-S(z)). The
   project currently skips this and works one level down, directly
   perturbing a probability measure by a multiplicative factor. That's fine
   for what's already proved, but it means there's no Lean object matching
   what the book calls "the action," and nothing says explicitly that the
   quadratic action is the same thing as the Gaussian distribution (with
   normalization sqrt(det(2*pi*K))).

5. **Generalize from the quartic action to the full nearly-Gaussian
   action.** The book's action isn't limited to a quartic (fourth-order)
   term — it's a sum of terms of every even order up to some cutoff, each
   with its own coupling tensor. The project only has the quartic case so
   far (`QuarticCoupling` in `Quartic.lean`). Extending this to general even
   order would let items 1 and 2 above be stated in full generality instead
   of just for the quartic case.

6. **State the full (not just connected) four-point correlator formula.**
   The book computes the full four-point correlator to first order in
   epsilon as a stepping stone, then subtracts off the disconnected pieces
   to get the connected four-point correlator. The project jumps straight to
   the connected result and never writes down the full-correlator formula on
   its own.

### Lower priority (smaller gaps, more mechanical to close)

7. **Apply the existing odd-vanishing lemma to actual moments.** There's
   already a basic lemma (`integral_eq_zero_of_odd` in `Basic.lean`) showing
   that a single "odd" observable integrates to zero under a distribution
   that's symmetric under z -> -z. But nobody has used it to show that
   products of an odd number of coordinates — i.e. actual odd moments — 
   vanish, or that odd connected correlators vanish. This is a short step
   from what's already there.

8. **Write down the six-point (M=6) worked example.** The book works out
   the six-point correlator by hand, decomposing it into a sum of 15 + 15
   products of lower connected correlators, as a worked example. The general
   machinery needed to do this already exists and is fully proved (the
   partition-based definition of a cumulant), so this is just a matter of
   specializing it to six points and writing down the resulting identity.

9. **Prove that diagonalizing a Gaussian's covariance gives independent
   variables (and the converse: a nonzero quartic coupling breaks
   independence).** The book shows that if you diagonalize a Gaussian's
   covariance matrix, you get a product of independent single-variable
   Gaussians, and that a nonzero quartic coupling breaks this independence.
   What exists in the project so far only goes the other direction — cases
   where independence is already known by construction (e.g. because
   different variables come from disjoint blocks of a matrix), plus one
   lemma showing that independence implies a vanishing cumulant (and even
   that lemma still needs a proof: it depends on
   `cumulantTransform_split_trace_fiber_regrouping` in `Cumulant.lean`,
   which is a `sorry`). The "diagonalize a general covariance to get
   independence" direction doesn't exist yet.

10. **Add the single-variable (n=1) self-interaction remark as its own
    lemma.** The book points out that even with just one variable, the
    quartic coupling still shifts the variance away from its Gaussian
    value — a nice illustration of what "self-interaction" means even when
    there's nothing else to interact with. This follows immediately by
    specializing the two-point-correlator-shift result (item 3, second
    bullet) to a single-variable index, but nobody has written that
    specialization down.

11. **Give expectation value its own named definition, and state the
    Taylor-expansion identity.** The book explicitly defines E[O(z)] and
    shows it equals a Taylor series in the moments. The project uses plain
    integrals everywhere instead of a named `expectation` definition, and
    never states the Taylor-series identity. This is mostly bookkeeping
    rather than new math, so it's the lowest priority item here.
