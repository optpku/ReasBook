module

public import DFPWolfe.Latest.Main

/-!
# Corollary 11 — identity initialization

Source label: `cor:identity-initialization` in the manuscript `20251117-DFP/arXiv.tex`.
The positive square root of the actual planar initial matrix gives an
identity-initialized strong-Wolfe counterexample for every admissible Wolfe
pair and exponent. Its globally Hölder Hessian has positive global bounds,
its gradient norm has positive liminf, and its exact cluster set is a centered
ellipse. The quantitative entry retains the source's eigenvalue constants,
the lower bound `√λmin(H₀)`, and the identity-block extension to `n ≥ 2`.
-/

#check DFPWolfe.Latest.identityInitialization
#check DFPWolfe.Latest.identityInitializationQuantitative
