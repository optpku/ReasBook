/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.SecantDegeneration

/-!
# Lemma 11: planar secant degeneration

Paper label: `lem:planar-degeneration` in `main-new.tex`.

For a strongly convex `C²` planar objective, consider an infinite nonstationary
positive-step weak-Wolfe orbit with positive-definite search matrices satisfying
the secant equation. If it does not converge to the unique minimizer, then
`λₖ = κₖ₋₁ det Hₖ` is positive, is eventually bounded by
`C ‖sₖ₋₁‖ ‖sₖ‖`, and tends to zero. The matrices are uniformly bounded
and their smallest eigenvalues tend to zero. No DFP matrix update is assumed.

The proof is in `SecantDegeneration`. Lean indexes the free coefficient from
zero: its `lam k` is the paper's `λₖ₊₁`. This file checks the complete theorem.
-/

#check DFP.SecantIteration.planarDegeneration
