/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph

/-!
# Lemma 5: local invariant graph

Paper label: `lem:graph-transform` in `main-new.tex`.

A finite-dimensional center-stable map fixing the origin, with derivative
`diag(1, L)` and complex spectral radius of `L` below one, admits a locally
forward-invariant `C^ν` graph tangent to the center axis, for `ν ≥ 2`.
Neither `L` nor the full derivative is required to be invertible.

The imported `LocalInvariantGraph` theorem assumes `C^ν` regularity of the
map, which is weaker than the paper's `C^(ν+1)` assumption. This file checks
that existing theorem for paper navigation.
-/

#check LocalInvariantGraph.existsOfComplexSpectralRadiusLtOne
