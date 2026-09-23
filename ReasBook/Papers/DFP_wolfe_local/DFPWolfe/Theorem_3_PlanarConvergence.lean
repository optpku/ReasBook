/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.Main

/-!
# Theorem 3: planar convergence

Paper label: `thm:planar-convergence` in `main-new.tex`.

For a globally strongly convex `C²` objective on the plane, assume its Hessian
is locally Lipschitz on a neighborhood of the initial sublevel. From any
initial point and positive-definite initial matrix, classical DFP with positive
steps and fixed weak-Wolfe parameters `0 < c₁ < c₂ < 1` reaches the unique
minimizer in finitely many steps or converges to it with gradient norms tending
to zero. The Lean orbit represents finite termination by constant continuation
after the first stationary point.

The public interfaces are in `DFPWolfe.Main`; the underlying proofs are in
`ReasLib.Optimization.DFP.PlanarConvergence`. The second check records the
strong-Wolfe consequence of the same result.
-/

#check DFP.main_planarWeakWolfeConvergence
#check DFP.main_planarStrongWolfeConvergence
