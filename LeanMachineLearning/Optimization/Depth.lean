/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Depth.Basic
public import LeanMachineLearning.Optimization.Depth.AffinePieces
public import LeanMachineLearning.Optimization.Depth.Separation
public import LeanMachineLearning.Optimization.Depth.SquareApprox
public import LeanMachineLearning.Optimization.Depth.Products
public import LeanMachineLearning.Optimization.Depth.Sobolev

/-!
# Benefits of depth for ReLU network approximation (Chapter 5)

This module formalizes the depth-separation results from Chapter 5 of the deep
learning theory notes (Telgarsky 2021), building on the approximation foundations
in `Approximation.*`.

## Overview

The central theme is that *depth creates exponential complexity cheaply*.
Specifically:

### The Δ tent function (`Depth.Basic`)
The function Δ(x) = 2σ(x) − 4σ(x − 1/2) + 2σ(x − 1) is a piecewise-linear "tent"
with peak at x = 1/2. Its L-fold composition Δ^L has 2^{L−1} equally-spaced copies
of itself on [0,1], achievable with O(L) nodes and O(L) layers.

### Affine piece counting (`Depth.AffinePieces`)
* **Lemma 5.2 (combination rules):** the number of affine pieces grows *additively*
  under linear combination and *multiplicatively* under composition.
* **Lemma 5.1 (depth-width tradeoff):** a network with L layers and m total nodes has at
  most (2m/L)^L affine pieces — polynomial in width, exponential in depth.

### Depth separation (`Depth.Separation`)
* **Theorem 5.1 (Telgarsky 2015, 2016):** f = Δ^{L²+2} is realized by a 3L²+6-node
  network, but any ReLU network with ≤ 2^L nodes and ≤ L layers has
  ∫_{[0,1]} |f − g| ≥ 1/32.

### Approximating x² (`Depth.SquareApprox`)
* **Theorem 5.2 (Yarotsky 2016):** x² can be approximated on [0,1] to error ε
  by a ReLU network with O(log(1/ε)) layers and O(log(1/ε)) nodes, via the
  piecewise-linear interpolation hᵢ = x − ∑_{j=1}^i Δʲ/4ʲ.
* From x², we get multiplication, monomials, polynomials, and Taylor expansions.

### Approximate multiplication (`Depth.Products`)
* **Lemma 5.3:** there exists a ReLU network prod_{k,l} with O(kl) layers and
  O(kl + l²) nodes such that |prod_{k,l}(x) − ∏ xⱼ| ≤ l · 4^{−k} for x ∈ [0,1]ˡ.
  Uses polarization: xy = ½((x+y)² − x² − y²).

### Sobolev ball approximation (`Depth.Sobolev`)
* **Lemma 5.4:** approximate monomials of degree ≤ r in d variables: O(kr) layers,
  O(d^r(kr + r²)) nodes.
* **Lemma 5.5:** approximate partition of unity on a grid: O(kd) layers,
  O((kd + d²) s^d) nodes.
* **Theorem 5.4 (Yarotsky 2016):** functions with bounded partial derivatives of
  order ≤ r can be approximated to error ε with O(log(1/ε)) layers and
  O(ε^{−d/r} log(1/ε)) nodes.

## Main results

| Name | Statement |
|------|-----------|
| `Depth.deltaTentIter_eq` | Δ^L(x) = Δ(⟨2^{L−1}x⟩) (Proposition 5.1) |
| `Depth.numAffinePieces_comp_le` | N_A(f ∘ g) ≤ N_A(f) · N_A(g) (Lemma 5.2) |
| `Depth.numAffinePieces_network_le` | N_A(f) ≤ (2m/L)^L (Lemma 5.1) |
| `Depth.depthSeparation` | ∫|Δ^{L²+2} − g| ≥ 1/32 (Theorem 5.1) |
| `Depth.squareInterp_error` | \|hᵢ(x) − x²\| ≤ 4^{−i−1} (Theorem 5.2) |
| `Depth.approxProdL_eval` | \|prod_{k,l}(x) − ∏xⱼ\| ≤ l·4^{−k} (Lemma 5.3) |
| `Depth.sobolevBallApprox` | Sobolev ball approximation (Theorem 5.4) |

-/
