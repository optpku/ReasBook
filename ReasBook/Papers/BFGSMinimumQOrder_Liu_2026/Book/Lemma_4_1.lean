/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

module

public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Interpolation

public section

open scoped EuclideanSpace Matrix.Norms.L2Operator

/- Lemma 4.1 (Compactly supported interpolation). For every ambient dimension at least
two, there is a positive dimension-dependent constant such that every embedded
alternating-scale sequence is interpolated by the gradient of a smooth function with a
compactly supported quadratic tail and a uniform operator-norm Hessian bound. -/
#check PlanarGradient.exists_compactlySupportedInterpolation
