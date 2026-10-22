/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2

public section

namespace VariationalRegularization

/-!
Remark 8.1. Source-facing bridge for the checked clauses of the remark.

Clauses `(8.27)` and `(8.28)` reuse the checked unit-square owners already
introduced in `Exercise 8.2`: the boundary predicate
`hasVanishingNormalDerivativeOnUnitSquareBoundary`, the operator formula
`unitSquareWeightedDiffusion_apply`, and the first-variation theorem
`lineDeriv_unitSquareSmoothPenalty_eq_unitSquareL2Pairing_of_neumann`.
Clause `(8.29)` remains prose-only here: the repository does not yet expose a
chapter-specific owner for the discrete `L(f)` and `L'` appearing in the book,
so this file must not replace that concrete assertion by a generic wrapper
predicate on arbitrary matrices.
-/

/- Remark 8.1 (1). Main source-facing check-only entry for the weighted
diffusion operator formula `(8.27)` on the unit square.

The homogeneous-Neumann boundary condition remains ambient supporting prose
through the existing owner
`hasVanishingNormalDerivativeOnUnitSquareBoundary`, while the main labeled
entry below points directly to the displayed operator formula owner
`unitSquareWeightedDiffusion_apply`. -/
#check unitSquareWeightedDiffusion_apply

/- Remark 8.1 (2). Source-facing check-only entry for the first-variation
clause linking `(8.27)` and `(8.28)` through the canonical directional
derivative owner `lineDeriv`. -/
#check lineDeriv_unitSquareSmoothPenalty_eq_unitSquareL2Pairing_of_neumann

/- Remark 8.1. The alternative direct-discretization sentence between `(8.28)`
and `(8.29)` is explanatory prose only, so it remains undocumented by a Lean
declaration in statement stage. -/

/- Remark 8.1 (3). The displayed discrete block-matrix formula `(8.29)` for
`L' (f) f` remains prose-only until the repository has a chapter-specific owner
for the discrete penalty operator and its derivative. -/

end VariationalRegularization
