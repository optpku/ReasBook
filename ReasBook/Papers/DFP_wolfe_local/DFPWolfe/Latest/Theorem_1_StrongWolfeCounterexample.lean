module

public import DFPWolfe.Latest.Main

/-!
# Theorem 10 — arbitrary Wolfe parameters and Hessian Hölder exponent

Source label: `thm:main` in the manuscript `20251117-DFP/arXiv.tex`.
For every `0 < c1 < c2 < 1`, `0 < ε < 1`, `0 < β < 1` and `n ≥ 2`,
the prescribed polar construction gives a classical strong-Wolfe DFP orbit
whose gradient norms tend to one. The Hessian is globally within `ε` of
identity and globally `β`-Hölder, with every larger exponent failing on
the original initial level set. The origin is the unique minimizer and
the complete cluster set is a unit circle in an embedded plane.
-/

#check DFPWolfe.Latest.main
#check DFPWolfe.Latest.mainWithSource
#check DFPWolfe.Latest.not_globalWeakWolfeConvergenceAt
#check DFPWolfe.Latest.not_levelSetGlobalWeakWolfeConvergenceAt
