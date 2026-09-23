/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.WolfeCounterexample.Holder

/-!
# Corollary 2: identity initialization

Paper label: `cor:identity-initialization` in `main-new.tex`.

For the Wolfe parameters of Theorem 1 and every dimension at least two, there
is a `C²` objective with globally one-half Hölder Hessian and positive uniform
lower and upper Hessian bounds. Classical DFP initialized with `H₀ = I` has a
well-defined positive-step strong-Wolfe orbit with strictly positive gradient
norm liminf. The Hessian bounds may change under the coordinate transformation.

The proof is in the imported `Holder` module. This file checks the existing
declaration for paper navigation.
-/

#check DFP.existsMatrixIdentityLiminfStrongWolfeHolder
