module

public import DFPWolfe.Latest.PlanarConvergence

/-!
# Theorem 13 — planar convergence with a locally Lipschitz Hessian

Source label: `thm:planar-convergence` in the manuscript `20251117-DFP/arXiv.tex`.
For an arbitrary initial point and positive definite initial matrix, a
globally strongly convex planar objective with Hessian locally Lipschitz
near the initial level set has finite stationary termination or convergence
of the iterates to its unique minimizer and of the gradients to zero.
The hypotheses allow the full weak-Wolfe parameter range. The unchanged
general planar proof is reused from the earlier revision.
-/

#check DFPWolfe.Latest.planarConvergenceCases
