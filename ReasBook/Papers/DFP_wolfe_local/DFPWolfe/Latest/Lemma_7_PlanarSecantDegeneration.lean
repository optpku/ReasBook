/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.Latest.SecantDegeneration

/-!
# Lemma 12 — degeneration of general planar secant sequences

Source label: `lem:planar-degeneration` in the manuscript `20251117-DFP/arXiv.tex`.
If a nonstationary weak-Wolfe planar sequence does not converge to its
strongly convex objective's minimizer, its free secant coefficient
`λₖ = κₖ₋₁ det Hₖ` is bounded by a constant times the product of consecutive
step norms and tends to zero. The matrices are bounded and their smallest
eigenvalues tend to zero. Only positive definiteness and the previous secant
equation are assumed; this general result reuses the earlier proof.
-/

#check DFPWolfe.Latest.planarDegeneration
