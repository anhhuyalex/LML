# Proof Golfing: Simplifying Proofs After Compilation

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference Table

### Tier 1 — Performance (always apply)

| Pattern | Savings | Risk |
|---------|---------|------|
| Linter-guided simp cleanup | 2 lines | Zero |
| `simp` → `simp only` (non-terminal) | Perf | Zero |
| Direct lemma over automation in coercion-heavy goals | Perf | Zero |

**Terminal `simp only` caveat:** Do not narrow terminal `simp` → `simp only` or introduce new terminal `simp only` without user confirmation — some projects prefer terminal `simp` for resilience to simp-set changes (the converse of the [FlexibleLinter](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/FlexibleLinter.html) concern, which flags non-`only` simp in non-terminal positions). In non-interactive mode, skip terminal `simp only` changes unless project style already uses it nearby.

### Tier 2 — Directness (always apply)

| Pattern | Savings | Risk |
|---------|---------|------|
| `by exact t` → `t` | 1 line | Zero |
| `by rfl` → `rfl` | 1 line | Zero |
| Eta-reduction `fun x => f x` → `f` | Tokens | Zero |
| `.mpr`/`.mp` over `rwa` for trivial | 1 line | Zero |
| Dot notation `.rfl`/`.symm` | Tokens | Zero |
| `apply f; exact h` → `exact f h` | 1 line | Zero |
| `ext x; rfl` → `rfl` | 67% | Low |
| `constructor; exact; exact` → `exact ⟨_, _⟩` | 2 lines | Zero |
| `simpa using h` → `exact h` when no simplification occurs | Clarity | Zero |

### Tier 3 — Structural simplification (with verification)

| Pattern | Savings | Risk |
|---------|---------|------|
| Single-use `have` inline (term < 40 chars) | 30-50% | Low |
| let+have+exact inline | 60-80% | HIGH |
| intro-dsimp-exact → lambda | 75% | Low |
| Inline `show` in `rw` | 50-70% | Zero |

### Tier 4 — Conditional (only when net score improves)

| Pattern | Savings | Risk | Condition |
|---------|---------|------|-----------|
| `rw; exact` → `rwa` | 50% | Zero | Only when `rwa` genuinely deletes boilerplate, not as default |
| `rw; simp_rw` → `rw; simpa` | 1 line | Zero | Only when it deletes surrounding boilerplate; never to replace a working `exact` |
| apply/exact chain → `exact` | 30-60% | Low | Reject if >80 chars, >2 dot-chain depth, or removes meaningful names |
| Transport ▸ for rewrites | 1-2 lines | Zero | |
| calc → .trans chains | 2-3 lines | Low | |
| Symmetric `<;>` | Lines | Low | Only for single identical tactic on literally identical goals |

**Scoring order:** Among correct candidates, prefer: (1) more direct proof shape, (2) lower inference/search burden, (3) better perf/determinism, (4) shorter code. Inference and perf are judged heuristically by the tactic complexity ladder, not by measurement. Length is still a core goal — but a tiebreaker among acceptable proofs.

**ROI Strategy:** Tier 1 and 2 first (always safe), Tier 3 with verification, Tier 4 only when the scoring order clearly favors the replacement.

**Not golf** (use `/lean4:refactor` instead): extracting repeated patterns to helpers, consolidating duplicate proof structure, API surface redesign.

## Critical Safety Warnings

### The 93% False Positive Problem

**Key finding:** Without proper analysis, 93% of "optimization opportunities" are false positives that make code WORSE.

**The Multiple-Use Heuristic:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: 40% worth optimizing (check carefully)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Example - DON'T optimize:**
```lean
let μ_map := Measure.map (fun ω i => X (k i) ω) μ  -- 20 tokens
-- Used 7 times in proof
-- Current: 20 + (2 × 7) = 34 tokens
-- Inlined: 20 × 7 = 140 tokens (4× WORSE!)
```

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Let binding used ≥3 times
- ❌ Complex proof with case analysis
- ❌ Semantic naming aids understanding
- ❌ Would create deeply nested lambdas (>2 levels)
- ❌ Readability Cost = (nesting depth) × (complexity) × (repetition) > 5

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Most patterns are false positives
- ✋ Debating whether 2-token savings is worth it

**Benchmark:** Well-maintained codebases reach saturation after ~20-25 optimizations.

## Systematic Workflow

### Phase 0: Pre-Optimization Audit (2 min)

Before applying patterns:
1. Remove commented code and unused lemmas
2. Fix linter warnings
3. Run `lake build` for clean baseline

This cleanup often accounts for 60%+ of available savings.

### Phase 1: Pattern Discovery (5 min)

Use systematic search, not sequential reading:

```bash
# 1. Find by-exact wrappers (directness)
grep -B 1 "exact" file.lean | grep "by$"

# 2. Find apply-exact chains (directness)
grep -A 1 "apply " file.lean | grep "exact"

# 3. Find let+have+exact (structural — verify binding usage)
grep -A 10 "let .*:=" file.lean | grep -B 8 "exact"

# 4. Find rw+exact (conditional — see rwa direction rule)
grep -A 1 "rw \[" file.lean | grep "exact"
```

**Expected:** 10-15 targets per file

### Phase 2: Safety Verification (CRITICAL)

For each let+have+exact pattern:

1. Count let binding uses (or use `$LEAN4_SCRIPTS/analyze_let_usage.py`)
2. If used ≥3 times → SKIP (false positive)
3. If used ≤2 times → Proceed with optimization

**Other patterns:** Verify compilation test will catch issues.

### Phase 2.5: Lemma Replacement Safety

When search mode is enabled, replacement candidates follow the same safety rules:
- Only accept if `lean_multi_attempt` passes
- Only accept if the replacement scores better by the lexicographic order (directness → inference burden → perf → length)
- Max one new import per replacement
- If replacement type-mismatches or needs statement changes → skip (hand off to axiom-eliminator)

### Phase 2.6: Bulk Rewrite Context Safety

**Non-equivalent contexts:** Term-wrapper rewrites (`:= by exact t` → `:= t`) are not universally equivalent in all elaboration contexts. The `by` keyword switches to tactic mode; removing it changes how Lean elaborates the term. All rewrites are still validated against baseline diagnostics and auto-reverted on regression.

**Disallowed bulk contexts:**
- `calc` blocks — step terms have specialized elaboration
- Tactic blocks — `by exact t` inside a `by` block is not the same as `t`
- Ambiguous context — when surrounding syntax makes equivalence uncertain, skip

**Nested tactic-mode boundary:** Skip candidate when the replacement TERM introduces a nested `by` (tactic-mode boundary at non-top-level position). This is a syntax/context check — the surrounding AST structure determines whether the `by` is top-level (safe to remove) or nested (unsafe). A plain regex on `by` would produce false skips on identifiers like `standby` or comments.

### Phase 3: Apply with Testing (5 min per pattern)

1. Apply optimization
2. Run `lean_diagnostic_messages(file)` (per change); `lake build` for final verification only
3. If fails: revert immediately, move to next
4. If succeeds: continue

**Strategy:** Apply 3-5 optimizations, then batch test.

### Phase 3.5: Batch Rollback Protocol

For bulk rewrites (activates automatically when ≥4 whitelisted candidates found; user confirms preview):

1. **Pre-batch snapshot** — capture file content before each batch
2. **Apply batch** — effective per-run limit: min(10 replacements/file, 3 hunks × 60 lines); overflow recomputed on next invocation — no persistent queue
3. **Validate** — run `lean_diagnostic_messages(file)` and compare: new diagnostics vs pre-batch baseline + sorry-count delta
4. **Revert on regression** — if sorry count increases or new diagnostics appear, restore from pre-batch file snapshot immediately (full batch revert, not partial)

### Phase 4: Check Saturation

After 5-10 optimizations, check indicators:
- Success rate < 20% → Stop
- Time per optimization > 15 min → Stop
- Mostly false positives → Stop

**Recommendation:** Declare victory at saturation.

## Lemma Replacement

When `--search` is enabled, the golfer performs a bounded LSP search pass before syntactic golfing:

1. Search for mathlib equivalents of custom helpers/axioms
2. Test replacements with `lean_multi_attempt`
3. Accept only if: replacement passes, scores better by the lexicographic order, and at most one new import needed

**Budgets:** `quick` = 1 search, ≤2 candidates; `full` = 2 searches, ≤3 candidates. Max 3 search calls total, ≤60s.

**Handoff:** If replacement needs statement changes or multi-file refactor → hand off to axiom-eliminator.

## Bulk Rewrite Rules

Bulk mode activates automatically when ≥4 whitelisted candidates are found in a file; the preview step is the user confirmation gate:

| Context | Allowed | Notes |
|---------|---------|-------|
| Declaration RHS (`:= by exact t`) | Yes | Whitelisted; validated with baseline + revert |
| `have` / `let` body | Yes | Same wrapper position; validated with baseline + revert |
| Inside `calc` block | No | Specialized step elaboration |
| Inside tactic block | No | `by exact t` ≠ `t` in tactic mode |
| TERM has nested tactic-mode `by` | No | Ambiguous elaboration boundary |

**Pre-apply checklist:**
1. Context check — declaration RHS, `have`, or `let` body only
2. Nested-by check — skip if TERM introduces a nested tactic-mode boundary (syntax/context check, not raw substring)
3. Symbol/signature check — verify symbol resolves in current imports, argument order matches

**Post-apply checklist:**
1. Diagnostics delta — compare vs pre-batch baseline
2. Sorry delta — no new sorries
3. Optional `lake build` — when import-sensitive edits occur (e.g., lemma replacement added an import)

## Anti-Patterns

### Semicolon Policy

Never introduce naked `;` as a golfing transform. `<;>` may be introduced only when applying a single identical tactic to literally identical goals (its intended purpose — e.g., `constructor <;> simp`); do not use it to compress non-identical branches.

When counting line savings, each `;`-separated tactic counts as its own line — semicolons do not reduce line count. If existing code uses `;` or `<;>`, do not count those lines as savings and do not target rewrites that preserve or expand semicolon usage.

```lean
-- ❌ Never introduce as a golfing transform
intro x; exact proof

-- ❌ Don't compress non-identical branches
cases h <;> (first_tactic; second_different_tactic)

-- ✅ Allowed: single identical tactic on literally identical goals
constructor <;> simp
constructor <;> rfl
```

### Don't Over-Inline

If inlining creates unreadable proof, keep intermediate steps:

```lean
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)

-- ✅ Good - clear intent
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```

## Failed Optimizations (Learning)

### Not All `ext` Calls Are Redundant

```lean
-- Original (works)
ext x; simp [prefixCylinder]

-- Attempted (FAILS!)
simp [prefixCylinder]  -- simp alone didn't make progress
```

**Lesson:** Sometimes simp needs goal decomposed first. Always test.

### omega with Fin Coercions

```lean
-- Attempted (FAILS with counterexample!)
by omega

-- Correct (works)
Nat.add_lt_add_left hij k
```

**Lesson:** omega struggles with Fin coercions. Direct lemmas more reliable.

## Appendix

### Token Counting Quick Reference

```text
~1 token each:   let, have, exact, intro, by, fun
~2 tokens each:  :=, =>, (fun x => ...), StrictMono
~5-10 tokens:    let x : Type := definition
                 have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

### Saturation Metrics

**Session-by-session data:**
- Session 1-2: 60% of patterns worth optimizing
- Session 3: 20% worth optimizing
- Session 4: 6% worth optimizing (diminishing returns)

**Time efficiency:**
- First 15 optimizations: ~2 min each
- Next 7 optimizations: ~5 min each
- Last 3 optimizations: ~18 min each

**Point of diminishing returns:** Success rate < 20% and time > 15 min per optimization.

### Real-World Benchmarks

**Cumulative across sessions:**
- 23 proofs optimized
- ~108 lines removed
- ~34% token reduction average
- ~68% reduction per optimized proof
- 100% compilation success (with multi-candidate approach)

**Technique effectiveness:**
1. let+have+exact: 50% of all savings, 60-80% per instance
2. Smart ext: 50% reduction, no clarity loss
3. ext-simp chains: Saves ≥2 lines when natural
4. rwa: Conditional (only when it deletes boilerplate, not as default compression)
5. ext+rfl → rfl: High value when works

## Detailed References

**Pattern details:** [proof-golfing-patterns.md](proof-golfing-patterns.md) - Full explanations with examples for all patterns

## Related

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions

# Proof Golfing Patterns

**Detailed pattern explanations for proof optimization. For quick reference table and overview, see [proof-golfing.md](proof-golfing.md).**

## Contents
- [High-Priority Patterns (⭐⭐⭐⭐⭐)](#high-priority-patterns-)
- [Conditional Patterns](#conditional-patterns)
- [Medium-Priority Patterns (⭐⭐⭐⭐)](#medium-priority-patterns-)
- [Medium-Priority Patterns (⭐⭐⭐)](#medium-priority-patterns--1)
- [Documentation Quality Patterns (⭐⭐)](#documentation-quality-patterns-)

---

## Tactic Complexity Ladder

Heuristic for judging inference burden and readability (not a measured performance ordering — we use the tactic identity as a proxy, not benchmarks):

`rfl`/`exact` < `rw`/`apply` < `simp only` < `simpa`/`rwa` < broad `simp`/`decide`/`omega`/`grind`

This ladder feeds the golf scoring order: correctness → directness → inference burden → perf/determinism → length. A transform that moves UP the ladder requires more than a 1-line win. A transform that moves DOWN is preferred even if it doesn't save lines. Length remains a core golf goal — but a tiebreaker among acceptable proofs.

Separately, **performance wins** come from narrowing `simp` to `simp only`, using direct lemmas over automation, and avoiding search-heavy tactics in coercion-heavy goals — these are always worth pursuing regardless of line count. **Exception:** terminal `simp` → `simp only` is a style split (some prefer terminal `simp` for resilience to simp-set changes — the converse of the [FlexibleLinter](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/FlexibleLinter.html) concern). Requires user confirmation.

---

## High-Priority Patterns (⭐⭐⭐⭐⭐)

### Pattern -1: Linter-Guided simp Cleanup (Performance)

```lean
-- Before (linter warns: unused)
simp only [decide_eq_false_iff_not, decide_eq_true_eq]
-- After
simp only [decide_eq_true_eq]
```

Remove unused `simp` arguments flagged by linter. Zero risk (compiler-verified), faster elaboration. Note: this is about removing unused lemma arguments from `simp only [...]` calls, not about narrowing `simp` → `simp only` (see terminal `simp only` caveat in the ladder above).

### Pattern 0: `by rfl` → `rfl` (Directness)

```lean
-- Before
theorem tiling_count : allTilings.length = 11 := by rfl
-- After
theorem tiling_count : allTilings.length = 11 := rfl

-- Before
theorem count : a = 9 ∧ b = 2 := by constructor <;> rfl
-- After
theorem count : a = 9 ∧ b = 2 := ⟨rfl, rfl⟩
```

Term mode for definitional equalities. Use `⟨_, _⟩` instead of `constructor <;> rfl`. Zero risk.

### Pattern 2: `ext + rfl` → `rfl`

```lean
-- Before
have h : f = g := by ext x; rfl
-- After
have h : f = g := rfl
```

When terms are definitionally equal, `rfl` suffices. Low risk - test with build, revert if fails.

### Pattern 2B: Eta-Reduction (Simplicity)

```lean
-- Before
eq_empty_iff_forall_notMem.mpr (fun x hx => hU_sub_int hx)
-- After
eq_empty_iff_forall_notMem.mpr hU_sub_int
```

Pattern: `fun x => f x` is just `f`. Zero risk.

### Pattern 2C: Direct `.mpr`/`.mp` (Directness)

```lean
-- Before
have h : U.Nonempty := by rwa [nonempty_iff_ne_empty]
-- After
have h : U.Nonempty := nonempty_iff_ne_empty.mpr h_ne
```

When `rwa` does trivial work, use direct term application. Zero risk.

### Pattern 2D: `intro-dsimp-exact` → Lambda (Directness)

```lean
-- Before
have h : ∀ i : Fin m, p (ι i) := by intro i; dsimp [p, ι]; exact i.isLt
-- After
have h : ∀ i : Fin m, p (ι i) := fun i => i.isLt
```

Convert `intro x; dsimp; exact term` to direct lambda. 75% reduction.

### Pattern 3: let+have+exact Inline (Conciseness)

```lean
-- Before
lemma foo := by
  let k' := fun i => (k i).val
  have hk' : StrictMono k' := by ...
  exact hX m k' hk'
-- After
lemma foo := by exact hX m (fun i => (k i).val) (fun i j hij => ...)
```

**⚠️ HIGH RISK:** 60-80% reduction but 93% false positive rate! MUST verify let used ≤2 times.

### Pattern 3A: Single-Use `have` Inline (Clarity)

```lean
-- Before
have h_meas : Measurable f := measurable_pi_lambda _ ...
rw [← Measure.map_map hproj h_meas]
-- After
rw [← Measure.map_map hproj (measurable_pi_lambda _ ...)]
```

Inline `have` used once if term < 40 chars and no semantic value. 30-50% reduction.

### Pattern 3B: Remove `by exact` Wrapper (Directness)

```lean
-- Before
have hζ_compProd : ... := by exact compProd_map_condDistrib hξ.aemeasurable
-- After
have hζ_compProd : ... := compProd_map_condDistrib hξ.aemeasurable
```

`by exact foo` is redundant - use term mode directly. Zero risk.

### Pattern 3C: Dot Notation for Constructors (Conciseness)

```lean
-- Before
apply EventuallyEq.mul hIH
exact EventuallyEq.rfl
-- After
exact hIH.mul .rfl
```

Use `.rfl`, `.symm`, `.trans` instead of full constructor names. Zero risk.

### Pattern 3D: Calc Blocks → `.trans` Chains (Conciseness)

```lean
-- Before
calc ∫ ω, ... = ... := step1 _ = ... := step2
-- After
(step1.trans step2).symm
```

When calc chains are short (2-3 steps), `.trans` chains can be more concise. Low risk.

### Pattern 3E: Inline `show` in Rewrites (Conciseness)

```lean
-- Before (3 lines)
have h1 : (m + m) / 2 = m := by omega
rw [h1]
-- After (1 line)
rw [show (m + m) / 2 = m by omega, ...]
```

Combine `have` + `rw` into `rw [show ... by ...]`. 50-70% reduction for short proofs.

### Pattern 3F: Transport Operator ▸ (Conciseness)

```lean
-- Before
theorem count : ValidData.card = 11 := by rw [h_eq, all_card]
-- After
theorem count : ValidData.card = 11 := h_eq ▸ all_card
```

Pattern: `(eq : a = b) ▸ (proof_of_P_b) : P_a`. Zero risk.

### Pattern 3G: Exact-Collapse — apply/exact Chains

**Family 1: apply + exact → direct application**

```lean
-- Before (3 lines)
apply mul_lt_mul_of_pos_right
· exact h_bound
· exact h_pos
-- After (1 line)
exact mul_lt_mul_of_pos_right h_bound h_pos
```

**Family 2: chained apply → nested term with dot notation**

```lean
-- Before (5 lines)
apply HasDerivAt.div
· apply HasDerivAt.mul
  · exact hf.hasDerivAt
  · exact hg.hasDerivAt
· exact hden.hasDerivAt
-- After (1 line)
exact hf.hasDerivAt.mul hg.hasDerivAt |>.div hden.hasDerivAt
```

**Family 3: apply + intro + exact → lambda / eta**

```lean
-- Before (3 lines)
apply Continuous.comp
· exact continuous_neg
· intro x; exact hf x
-- After (1 line)
exact continuous_neg.comp hf
```

Typically 30–60% reduction. Low risk (same proof terms, reorganized).

**Detection & workflow:**

- **Anchors:** 2–7 tactic lines, starts with `apply`, contains `exact` on branches. Skip `calc`, `cases`/`induction`/`match` (multi-goal), blocks with `simp`/`omega`/`decide`/`norm_num` (non-collapsible), semicolon-heavy (>3), blocks with `have`/`refine` (too complex to collapse mechanically). `constructor`+`exact`+`exact` is already an instant win, handled separately.
- **Mechanical pass** (≤30 anchors/file): Construct collapsed `exact` from tactic structure → verify with `lean_multi_attempt` + `lean_diagnostic_messages` baseline check.
- **Exploratory pass** (when `--search≠off`): Build candidate `exact` terms from three sources: (1) chain lemmas with different argument order or dot notation, (2) local hypotheses that unify with the goal, (3) known dot-notation rewrites (`.comp`, `.trans`, `.symm`, `.mul`, etc.). Test via `lean_multi_attempt`.
- **Regression gate:** Every accepted collapse must pass `lean_diagnostic_messages` baseline check — no new diagnostics, no sorry increase. Not just "compiles in lean_multi_attempt."
- **Reject heuristics:**
  - Reject if collapse introduces `simpa`/`rwa` from a direct explicit proof (moves up the tactic complexity ladder)
  - Reject if collapsed term length > ~80 chars
  - Reject if dot-chain depth > 2
  - Reject if it removes meaningful intermediate names (named `have` with semantic value)
  - Reject if it only saves 1 line and raises inference burden
- **Processing order:** Bottom-up to avoid line drift.
- **Budget:** Mechanical ≤30 anchors/file. Exploratory per-anchor ≤2 probes, per-file: `quick` ≤5 probes/30s, `full` ≤15 probes/60s (shared with lemma replacement).

### Pattern 7A: `simpa using` → `exact` (Directness)

```lean
-- Before
simpa using h
-- After
exact h
```

When `simpa` does no simplification, prefer `exact` — it is lower on the tactic complexity ladder and makes intent explicit. Zero risk.

---

## Conditional Patterns

Patterns that improve code only in specific contexts. Apply only when the scoring order clearly favors the replacement.

### Pattern 1: `rw; exact` → `rwa` (Conditional)

```lean
-- Before
rw [h1, h2] at h; exact h
-- After
rwa [h1, h2] at h
```

**Conditional:** `rwa` is a standard mathlib idiom, but as a golfing transform it moves UP the tactic complexity ladder (`rw`+`exact` → `rwa`). Only apply when `rwa` genuinely deletes surrounding boilerplate (extra `simp`/`change` blocks), not as a default 1-line compression. See golf.md `simpa`/`rwa` direction rule.

### Pattern 2A: `rw; simp_rw` → `rw; simpa` (Conditional)

```lean
-- Before
have h := this.interior_compl
rw [compl_iInter] at h
simp_rw [compl_compl] at h
exact h
-- After
have h := this.interior_compl
rw [compl_iInter] at h
simpa [compl_compl] using h
```

**Conditional:** `simpa using` is only a win when it deletes surrounding boilerplate (an extra `rw`, `change`, or `simp` block). Never replace `exact t` with `simpa using t` unless `exact t` fails. In coercion-heavy or subtype-heavy proofs, test `exact` first; only fall back to `simpa using` if transport is actually needed. Note: `simp using` is NOT a drop-in for `simpa using` — they have different semantics.

---

## Medium-Priority Patterns (⭐⭐⭐⭐)

### Pattern 4: Redundant `ext` Before `simp` (Simplicity)

```lean
-- Before
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by apply Fin.ext; simp [ι]
-- After
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by simp [ι]
```

For Fin/Prod/Subtype, `simp` handles extensionality automatically. 50% reduction.

### Pattern 5: `congr; ext; rw` → `simp only` (Simplicity)

```lean
-- Before
lemma foo : Measure.map ... := by congr 1; ext ω i; rw [h]
-- After
lemma foo : Measure.map ... := by simp only [h]
```

`simp` handles congruence and extensionality automatically. 67% reduction. **Caveat:** If `simp only` would be terminal (closing the goal), this is subject to the terminal `simp only` style split — ask for user confirmation in interactive mode, skip in non-interactive unless project already uses terminal `simp only` nearby.

### Pattern 5A: Remove Redundant `show` Wrappers (Simplicity)

```lean
-- Before
rw [show X = Y by simp, other]; simp [...]
-- After
simp [...]
```

Remove `show X by simp` wrappers when simp handles the equality directly. 50-75% reduction.

### Pattern 5B: Convert-Based Helper Inlining (Directness)

```lean
-- Before
have hfun : f = g := by ext x; simp [...]
simpa [hfun] using main_proof
-- After
convert main_proof using 2; ext x; simp [...]
```

Inline helper equality used once with `convert ... using N`. 30-40% reduction.

### Pattern 5C: Inline Single-Use Definitions (Clarity)

```lean
-- Before
def allData := allTilings.map Tiling.data
def All := allData.toFinset
-- After
def All := (allTilings.map Tiling.data).toFinset
```

Inline definitions used exactly once. 3-4 lines saved.

### Pattern 6: Smart `ext` (Simplicity)

```lean
-- Before
apply Subtype.ext; apply Fin.ext; simp [ι]
-- After
ext; simp [ι]
```

`ext` handles multiple nested extensionality layers automatically. 50% reduction.

### Pattern 7: `simp` Closes Goals Directly (Simplicity)

```lean
-- Before
have h : a < b := by simp [defs]; exact lemma
-- After
have h : a < b := by simp [defs]
```

Skip explicit `exact` when simp makes goal trivial. 67% reduction.

---

## Medium-Priority Patterns (⭐⭐⭐)

### Pattern 7B: Unused Lambda Variable Cleanup (Quality)

```lean
-- Before (linter warns)
fun i j hij => proof_not_using_i_or_j
-- After
fun _ _ hij => proof_not_using_i_or_j
```

Replace unused lambda parameters with `_`. Zero risk.

### Pattern 7C: calc with rfl for Definitions (Performance)

```lean
calc (f b - f a) * g'
    = Δf * g' := rfl
  _ = Δg * f' := by simpa [Δf, Δg, ...] using h
  _ = (g b - g a) * f' := rfl
```

Use `rfl` for definitional unfolding steps - faster than proof search.

### Pattern 7D: refine with ?_ (Clarity)

```lean
-- Before
have eq : ... := by ...
exact ⟨c, hc, f', g', hf', hg', eq⟩
-- After
refine ⟨c, hc, f', g', hf', hg', ?_⟩
calc ... -- proof inline
```

Use `refine ... ?_` for term construction with one remaining proof.

### Pattern 7E: Named Arguments in obtain (Safety)

```lean
-- Before (type error!)
obtain ⟨c, hc, h⟩ := lemma hab hfc (toHasDerivAt hfd) ...
-- After (self-documenting)
obtain ⟨c, hc, h⟩ := lemma (f := f) (hab := hab) (hfc := hfc) ...
```

Use named arguments for complex `obtain` with implicit parameters.

### Pattern 8: have-calc Inline (Clarity)

```lean
-- Before
have h : sqrt x < sqrt y := Real.sqrt_lt_sqrt hn hlt
calc sqrt x < sqrt y := h
-- After
calc sqrt x < sqrt y := Real.sqrt_lt_sqrt hn hlt
```

Inline `have` used once in calc if term < 40 chars.

### Pattern 9: Inline Constructor Branches (Conciseness)

```lean
-- Before
constructor; · intro k hk; exact hX m k hk; · intro ν hν; have h := ...; exact h.symm
-- After
constructor; · intro k hk; exact hX m k hk; · intro ν hν; exact (...).symm
```

Inline simple constructor branches. 30-57% reduction.

### Pattern 10: Direct Lemma Over Automation (Simplicity)

```lean
-- Before (fails!)
by omega  -- Error with Fin coercions
-- After (works!)
Nat.add_lt_add_left hij k
```

Use direct mathlib lemmas over automation when available.

### Pattern 11: Multi-Pattern Match (Simplicity)

```lean
-- Before (nested cases)
cases n with | zero => ... | succ n' => cases n' with ...
-- After (flat match)
match n with | 0 | 1 | 2 => omega | _+3 => rfl
```

Replace nested cases with flat match. ~7 lines saved.

### Pattern 12: Successor Pattern (n+k) (Clarity)

```lean
-- Before (deeply nested)
cases i with | zero => ... | succ i' => cases i' with ...
-- After (direct offset)
match i with | 0 => omega | 1 | 2 => rfl | n+3 => [proof]
```

Use `| n+k =>` for "n ≥ k" range cases. ~25 lines saved.

### Pattern 13: Symmetric Cases with `<;>` (Conditional)

```lean
-- Before (duplicate structure, literally identical bodies)
cases h with | inl => simp | inr => simp
-- After (single identical tactic on identical goals)
cases h <;> simp
```

**Conditional:** `<;>` is allowed only when applying a single identical tactic to literally identical goals (its intended purpose). Do not introduce `<;>` to compress non-identical branches. When counting savings, each `;`-separated tactic counts as its own line.

### Pattern 14: Inline omega (Conciseness)

```lean
-- Before
have : 2 < n + 3 := by omega
exact hzero _ this
-- After
exact hzero _ (by omega)
```

Inline trivial arithmetic with `by omega` when used once as argument.

### Pattern 15: match After ext (Clarity)

```lean
-- Before
ext n; cases n with | zero => ... | succ n' => cases n' with ...
-- After
ext n; match n with | 0 => exact ha0 | 1 => ... | n+2 => ...
```

Use `match` after `ext` instead of nested `cases`. ~3 lines saved.

---

## Documentation Quality Patterns (⭐⭐)

### Remove Duplicate Inline Comments

```lean
-- Before (with comprehensive docstring above)
/-- Computes measure by factoring through permutation... -/
calc Measure.map ...
    -- Factor as permutation composed with identity
    = ... := by rw [...]

-- After (docstring is the single source of truth)
/-- Computes measure by factoring through permutation... -/
calc Measure.map ...
    = ... := by rw [...]
```

**When to apply:** Comprehensive docstring already explains the proof strategy.
**When NOT to apply:** Inline comments provide details NOT in docstring.

---

**Related:** [proof-golfing.md](proof-golfing.md) (quick reference, safety & workflow)

# Proof Simplification

Guide for simplifying Lean 4 proofs at the *strategy* level: finding fundamentally better proof approaches, leveraging mathlib, and extracting reusable helpers. Complements [proof-refactoring.md](proof-refactoring.md) (structural extraction) and [proof-golfing.md](proof-golfing.md) (tactic-level optimization).

## Quick Decision Tree

```
Proof seems too long or complex
├─ Is it doing something "basic" in 20+ lines?
│   ├─ Search mathlib — the lemma probably exists (→ Replace with Mathlib)
│   │   └─ Not found → State in mathlib-ready generality (→ Missing Lemmas)
│   └─ Still hard → Definition might be fighting you (→ Definition Problems)
├─ Same pattern appears 2+ times?
│   └─ Extract helper in maximum generality (→ Helper Extraction)
├─ Proof has a complex case split?
│   └─ Search for a congr/EqOn/EventuallyEq approach (→ Congr Lemmas)
├─ Proof manually threads through a definition?
│   └─ Search for a lemma about the definition (→ Replace with Mathlib)
└─ Proof is inherently complex, just long?
    └─ Use [proof-refactoring.md](proof-refactoring.md) instead
```

## Replace with Mathlib Lemmas

The single highest-impact simplification. For search protocol details, see [mathlib-guide.md](mathlib-guide.md) and [lean-lsp-tools-api.md](lean-lsp-tools-api.md).

### Common Patterns Worth Searching

| Proof Pattern | Mathlib Lemmas to Search |
|---------------|-----------|
| Continuity of piecewise function | `ContinuousOn.if`, `ContinuousOn.union_of_isClosed`, `LocallyFinite.continuousOn_iUnion` (→ [Congr Lemmas](#congr-lemmas)) |
| Property of a function that equals another on a set | `ContinuousOn.congr`, `HasDerivWithinAt.congr_of_eventuallyEq`, `Measurable.congr` (→ [Congr Lemmas](#congr-lemmas)) |
| Floor/ceil equals specific value | `Nat.floor_eq_on_Ico`, `Int.floor_eq_iff` |
| Lipschitz/bound transfer | `LipschitzWith.dist_le_mul`, `LipschitzOnWith` |
| Filter membership | `Ioo_mem_nhdsGT`, `Ico_mem_nhdsGE`, `filter_upwards` |
| Set equality on interval | `Set.EqOn`, `Set.EqOn.eventuallyEq_nhdsWithin` (→ [Congr Lemmas](#congr-lemmas)) |
| Finset induction over image/sum/card | `Finset.card_image_of_injective`, `Finset.sum_image`, `Finset.prod_image` (→ [Finset Patterns](#finset-patterns)) |
| Two morphisms equal by manual pointwise unfolding | `MonoidHom.ext`, `RingHom.ext`, `LinearMap.ext`, `AlgHom.ext` (→ [Ext Lemmas](#ext-lemmas)) |
| Monotonicity / sup-inf inequalities | `Monotone.comp`, `StrictMono.comp`, `sup_le_iff`, `le_inf_iff` (→ [Order/Lattice Patterns](#orderlattice-patterns)) |

## Congr Lemmas

Replace case splits where a `congr`-style lemma would be cleaner.

### Pattern: Transfer via `Set.EqOn`

**Before:** Prove continuity by case-splitting on endpoints and interior:
```lean
intro t ht
rcases eq_or_lt_of_le ht.2 with rfl | h_lt
· -- Right endpoint: [10 lines]
· rcases eq_or_lt_of_le ht.1 with rfl | h_gt
  · -- Left endpoint: [8 lines]
  · -- Interior: [5 lines]
```

**After:** Show function equals a known-continuous function on the set, transfer:
```lean
suffices h_eq : Set.EqOn f g s from (hg_cont.congr h_eq)
intro t ht
-- Unified proof (often much shorter)
```

`ContinuousOn.congr` takes `ContinuousOn f s` and `EqOn g f s` to give `ContinuousOn g s`. Direction matters: `EqOn` goes from the *new* function to the *known-continuous* function.

### Pattern: Transfer via `EventuallyEq`

When manually differentiating a complex function by unfolding and assembling, show it agrees with a known-differentiable function eventually instead:
```lean
have h_eq : f =ᶠ[nhdsWithin t s] g := by
  filter_upwards [some_neighborhood_lemma] with x hx
  exact function_agrees_on_interval x hx
exact h_deriv_g.congr_of_eventuallyEq h_eq h_val
```

### When Congr Lemmas Help

- Function is defined piecewise but equals something simpler on each piece
- You need continuity/differentiability/measurability of a complex function
- The complex function agrees with a simple one on the relevant set
- Case splits are about matching definitions, not about mathematical content

## Finset Patterns

Replace Finset induction with direct combinatorial lemmas when the inductive step is mostly `simp` with `insert`/`erase`/`mem_image`.

**Before:** Manual induction over a Finset with mechanical insert/erase bookkeeping:
```lean
apply Finset.induction_on s
· simp
· intro a s ha ih
  rw [Finset.image_insert, Finset.card_insert_of_not_mem]
  simp only [Finset.mem_image, not_exists] at ha ⊢
  constructor
  · intro h; exact absurd (hinj.eq_iff.mp h) (ha _ rfl)
  · rw [ih]
  -- ... more insert/erase/mem_image reasoning
```

**After:**
```lean
exact Finset.card_image_of_injective s hinj
-- or: Finset.sum_image fun x _ y _ h => hinj h
-- or: Finset.prod_image ...
```

Mathlib has pre-packaged lemmas for `card`, `sum`, `prod`, `sup`, and `inf` over `Finset.image`. If the induction step is mechanical bookkeeping, the lemma almost certainly exists.

## Ext Lemmas

Replace manual pointwise unfolding of morphism equality with `ext` lemmas. Applies when proofs coerce to bare functions and unfold with `map_add`/`map_mul`/`map_one` chains.

**Before:** Manual pointwise unfolding to show two ring homomorphisms are equal:
```lean
show (f.comp g : R →+* S) = h
apply DFunLike.ext
intro x
simp only [RingHom.comp_apply]
-- unfold (f ∘ g)(x) and h(x), then rewrite with map_* lemmas:
rw [map_add, map_mul, map_one]
-- ... repeat for each generator / case
```

**After:**
```lean
ext x <;> simp
-- or when simp needs guidance:
-- exact RingHom.ext fun x => by simp [h_comm]
```

`MonoidHom.ext`, `RingHom.ext`, `LinearMap.ext`, and `AlgHom.ext` reduce morphism equality to pointwise equality with the correct coercion context. Combined with `simp`, this eliminates manual `DFunLike.ext` + `map_*` chains.

## Order/Lattice Patterns

Replace manual monotonicity threading and `sup`/`inf` splitting with compositional lemmas.

### Pattern: Monotone composition

**Before:** Manual monotonicity through a multi-layer composition:
```lean
intro a b hab
apply hg
apply hf
exact hab
-- or for deeper compositions:
intro a b hab
have h1 := hf hab
have h2 := hg h1
have h3 := hk h2
exact h3
```

**After:**
```lean
exact hg.comp hf
-- deeper: exact (hk.comp hg).comp hf
```

`Monotone.comp`, `StrictMono.comp`, `Antitone.comp` handle arbitrary composition depth.

### Pattern: Lattice sup/inf splitting

**Before:** Manual splitting of a `sup_le` or `le_inf` goal:
```lean
refine sup_le ?_ ?_
· -- show a ≤ c
  calc a ≤ b := h₁
       _ ≤ c := h₂
· -- show a' ≤ c
  calc a' ≤ b' := h₃
        _ ≤ c  := h₄
```

**After:**
```lean
exact sup_le_iff.mpr ⟨h₁.trans h₂, h₃.trans h₄⟩
-- or: exact le_inf h_left h_right
-- these compose: sup_le_sup h₁ h₂
```

`sup_le_iff`, `le_inf_iff`, `sup_le_sup`, and `le_inf` handle lattice plumbing.

## Helper Extraction

Extract repeated proof patterns (same `rw`/`simp` chain 2+ times, same `nlinarith` structure, same definitional unfolding) as standalone lemmas.

### Extraction Protocol

1. **Find the common core** — what mathematical fact is being proved each time?
2. **State it as a standalone lemma** with the most general hypotheses
3. **Name it after what it proves**, not where it's used
4. **Place it before first use**

### Generalization Checklist

When extracting, ask:
- **Weaker hypotheses?** Can `=` become `≤`? Can `Fin n` become `ℕ`?
- **Fewer assumptions?** Does the proof actually use all hypotheses?
- **More general types?** Can `ℝ` become `[LinearOrderedField α]`?
- **Mathlib-ready?** Would this be useful in mathlib? If so, state it in mathlib conventions (see [mathlib-style.md](mathlib-style.md)).

## Missing Lemmas

Sometimes the right lemma doesn't exist in mathlib. Signs: 20+ lines to prove something "obvious", same proof repeated across projects, only basic library infrastructure needed, natural place in an existing module.

What to do:
1. State it in maximum generality (most general typeclasses)
2. Follow mathlib naming conventions (see [mathlib-style.md](mathlib-style.md))
3. Use a `private` version locally for now
4. Note it in the refactoring report for potential contribution

## Definition Problems

Sometimes the proof is hard because the definition is fighting you. Signs: every proof starts with `unfold foo; simp`, same definitional unfolding in every lemma, arithmetic computations dominate due to discretization.

What to do:
1. **Build the API** — prove key properties as standalone lemmas
2. **Consider alternative definitions** — would an equivalent definition be easier to work with?
3. **Use `simp` lemmas** — make key equalities available to `simp` so proofs don't need manual unfolding

## File-Level Audit Checklist

When analyzing a whole file:

1. **Repeated tactic sequences** — same `rw`/`simp` chain 2+ times → extract helper
2. **Proof lengths** — >30 lines for "basic" facts → search mathlib; >60 lines → strong candidate
3. **Hand-rolled basics** — continuity proofs not using `fun_prop`, derivatives not using `HasDerivAt` chains, arithmetic not using `omega`/`positivity`/`norm_num`
4. **Overly specific hypotheses** — can `=` become `≤`? Can `[NormedSpace ℝ E]` become `[Module ℝ E]`?
5. **API coverage** — is every proof unfolding a definition directly? Should there be intermediate API lemmas?

## See Also

- [proof-refactoring.md](proof-refactoring.md) — Structural refactoring (breaking proofs into helpers)
- [proof-golfing.md](proof-golfing.md) — Tactic-level optimization
- [mathlib-guide.md](mathlib-guide.md) — How to search mathlib
- [mathlib-style.md](mathlib-style.md) — Naming conventions for potential mathlib contributions
