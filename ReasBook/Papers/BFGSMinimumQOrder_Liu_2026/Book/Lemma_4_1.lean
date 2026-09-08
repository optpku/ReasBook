module

public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Interpolation

public section

open scoped EuclideanSpace Matrix.Norms.L2Operator

/- Lemma 4.1 (Compactly supported interpolation). For every ambient dimension at least
two, there is a positive dimension-dependent constant such that every embedded
alternating-scale sequence is interpolated by the gradient of a smooth function with a
compactly supported quadratic tail and a uniform operator-norm Hessian bound. -/
#check PlanarGradient.exists_compactlySupportedInterpolation
