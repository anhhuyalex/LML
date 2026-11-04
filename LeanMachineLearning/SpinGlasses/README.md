# SpinGlasses: directory layout

The directory is organized by topic. Lean namespaces (`SpinGlasses`) and declaration names did
not change when the files were moved; only module paths did
(for example `LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityFreeEnergy`).
A new file goes in the directory of the topic it treats, and must be added to
`LeanMachineLearning.lean` (run `lake exe mk_all`).

Blueprint chapters: `blueprint/src/chapters/spinglasses.tex` (Panchenko) and
`blueprint/src/chapters/spinglasses_talagrand.tex` (Talagrand, *Spin Glasses*, Vol. I).

## Shared tools

* `Basic.lean`: configurations, overlaps.
* `Gaussian/`: Gaussian integration by parts, comparison and the Gaussian interpolation engines
  (nonlinear, conditional, replica versions) used by both books.
* `Gibbs/`: finite Gibbs measures, nested Gibbs averages, replica marginals.

## `Panchenko/` (blueprint chapter `chap:sg`)

* `Foundations/`: SK Hamiltonian, free energy, mixed `p`-spin models, zero-temperature limit,
  Guerra-Toninelli theorem, concentration of the free energy.
* `AizenmanSimsStarr/`: the Aizenman-Sims-Starr scheme and Gram-matrix approximation.
* `AsymptoticGibbs/`: overlap exchangeability and the asymptotic Gibbs measure.
* `AldousHoover/`: Aldous-Hoover representation and de Finetti.
* `DovbyshSudakov/`: the Dovbysh-Sudakov representation.
* `Poisson/`: Poisson point processes.
* `PoissonDirichlet/`: the Poisson-Dirichlet process; `GhirlandaGuerra/` (the Ghirlanda-Guerra
  identities) and `Uniqueness/` (characterization by those identities).
* `Cascade/`: Ruelle probability cascades: `Tree/`, `Parisi/` (Parisi recursion),
  `BolthausenSznitman/` (invariance), `GhirlandaGuerra/`, `Coalescent/`.

## `Talagrand/` (blueprint chapter `chap:sg-talagrand`, high-temperature SK model)

* `DecoupledSystems/`: decoupled systems and first moments.
* `GuerraReplicaSymmetric/`: Guerra's smart path, the replica-symmetric bound, the fixed point
  `q` and its uniqueness (including the Latala-Guerra lemma).
* `OverlapConcentration/`: Latala's overlap concentration and the Aizenman-Lebowitz-Ruelle
  formula; `FreeEnergyCLT/` holds the central limit theorem for the free energy.
* `SpinDecorrelation/`: spin decorrelation, asymptotic product measures, random projections.
* `CavityMethod/`: the cavity method and the overlap contraction estimates.
* `GaussianFluctuation/`: the Gaussian fluctuation principle, local magnetizations, TAP equations.
* `OverlapSecondMoments/`: second moments of overlaps, the `T`-basis and the Almeida-Thouless line.
* `BeyondATLine/`: instability beyond the AT line, coupled replicas, non-differentiability.
* `OverlapCLT/`: the central limit theorem for the overlaps: `HigherOrderCavity/`, `Contractions/`,
  `GibbsMoments/`, and the three inductions `Pair/`, `Single/`, `Global/`.
