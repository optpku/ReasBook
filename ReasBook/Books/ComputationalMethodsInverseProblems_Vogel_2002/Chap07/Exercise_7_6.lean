/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_4

public section

/- Exercise 7.6. Main labeled source-facing canonical-reuse entry.

Equation `(7.31)` is already the Chapter 7 theorem
`Tikhonov.lCurveCurvature_eq_curvatureFromEnergies_of_solutionDeriv_pos`:
under the smoothness, positivity, and derivative identities collected in
`(7.30)`, it rewrites the deterministic Tikhonov L-curve curvature in the
energy form `LCurve.curvatureFromEnergies`.
-/

#check Tikhonov.lCurveCurvature_eq_curvatureFromEnergies_of_solutionDeriv_pos

end
