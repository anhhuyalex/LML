/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment

/-!
# Notation for the SK energy, the cavity path and the `n`-replica average

Many statements about the SK model take a functional `ν` on observables of `n` replicas and the
hypothesis that `ν` is the disorder average of the Gibbs average
`ν Φ = 𝔼_g ∫ Φ d(Gibbs_{g}^{⊗n})`, where `Gibbs_g` is the tilted counting measure on
`Fin (N + 1) → ℤˣ` with the energy `skGibbsEnergy (N + 1) β h g` (written out).  The notation
`skReplicaAverage% ν n` expands to exactly that proposition, using the ambient variables
`N β h`; it is a macro, not a definition, so statements using it are syntactically the
expanded ones after elaboration.
-/

@[expose] public section

set_option hygiene false in
/-- `skReplicaAverage% ν n` is the statement that `ν` is the SK `n`-replica average at the
ambient `N β h`:
`∀ Φ, ν Φ = ∫ g, ∫ σ, Φ σ ∂(Measure.pi fun _ : Fin n => count.tilted (energy g))
  ∂(Gaussian disorder)`.
-/
macro "skReplicaAverage% " ν:term:max n:term:max : term =>
  `(∀ Φ, $ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin $n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(MeasureTheory.Measure.pi fun _ : Fin $n => MeasureTheory.Measure.count.tilted
        fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(MeasureTheory.Measure.pi fun _ : FinPairs (N + 1) => ProbabilityTheory.gaussianReal 0 1))

set_option hygiene false in
/-- `skEnergy%` is the SK energy `fun g a => (√(N+1))⁻¹ β ∑_{p} g_p a_{p₁} a_{p₂} + h ∑ᵢ aᵢ` of a
configuration `a : Fin (N + 1) → ℤˣ` for the pair disorder `g : FinPairs (N + 1) → ℝ`, with the
ambient `N β h` (the function `skGibbsEnergy (N + 1) β h`, written out). -/
macro "skEnergy%" : term =>
  `(fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ))

set_option hygiene false in
/-- `skCavityBase%` is the energy of the first `N` spins (the old couplings `g'`) and the field,
as a function of a configuration `a : Fin (N + 1) → ℤˣ`, with the ambient `N β h` (the
cavity-path notation of Eq. (1.151), the `B` of the statements). -/
macro "skCavityBase%" : term =>
  `(fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))

set_option hygiene false in
/-- `skCavityEnergy%` is the cavity-path energy `E s g' ω a` of Eq. (1.151): the angle `s`
interpolates between the new-coupling term (`cos s`, Gaussian `ω.1`) and the field term
(`sin s`, Gaussian `ω.2`) on top of the base `B g' a`. It refers to a surrounding `let B` and to
the ambient `N β q`. -/
macro "skCavityEnergy%" : term =>
  `(fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a)

set_option hygiene false in
/-- `skCavityKernel%` is the covariance kernel `K a b` of the cavity path (the `last`-spin
product times the overlap of the first `N` spins centred at `q`), with the ambient `N β q`. -/
macro "skCavityKernel%" : term =>
  `(fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N =>
            (b i.castSucc : ℝ)) - q))

set_option hygiene false in
/-- `skReplicaOverlapStat% K` is the centred overlap statistic of the pair `(a j, b j)` of
replicas against the fresh replicas `j`:
`fun j ρ => (N+1)⁻¹ ∑_{v : Fin K} X_L X_S - [¬ (L j ∨ S j)] q`, where `X_L = ρ(a j) v - ρ(j₁) v` if `L j` and `ρ(j₁) v` otherwise (similarly `X_S` with `b j`,
`j₂`). It uses the ambient `N q L S a b`; `K` is `N + 1` (all sites) or `N` (the first `N`
sites). -/
macro "skReplicaOverlapStat% " k:term:max : term =>
  `(fun j ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ v : Fin $k,
        (if L j then (ρ (.inl (a j)) v : ℝ) - (ρ (.inr (.inl j)) v : ℝ)
          else (ρ (.inr (.inl j)) v : ℝ)) *
        (if S j then (ρ (.inl (b j)) v : ℝ) - (ρ (.inr (.inr j)) v : ℝ)
          else (ρ (.inr (.inr j)) v : ℝ))) - (if L j || S j then 0 else q))
