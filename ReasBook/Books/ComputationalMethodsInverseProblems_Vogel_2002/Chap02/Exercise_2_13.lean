/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_5.SmoothNegativeLaplacian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9.TestFields
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive

public section

/-!
Refine-stage source-facing blocker for Exercise 2.13.

Exercise 2.13 does not introduce a new negative-Laplacian owner. It asks for
three properties of the exact operator already introduced in `(2.10)`, namely:
* the unit `H¹(Ω) → L²(Ω)` bound on the stated `C¹(Ω)` core
* self-adjointness of that operator restricted to the same core
* positive semidefiniteness of that same restriction

The current repository now has the faithful smooth-core formula layer from
Example 2.5, namely `smoothNegativeLaplacianWithin`, but it still does not
expose the exact domain-local `H¹(Ω)` owner, the corresponding `L²(Ω)`
codomain packaged as the source uses it, or the named `C¹(Ω)` core as a
restricted operator domain. This file therefore remains blocked only on that
extension/restriction layer and reuses the existing Chapter 2 smooth owner
instead of keeping purely generic backend anchors.
-/

section

variable {d : ℕ}
variable (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))

/-
Exercise 2.13. Main labeled source-facing blocker entry.

The exact smooth negative-Laplacian formula from `(2.10)` is already owned by
`smoothNegativeLaplacianWithin Ω` and its evaluation lemma. What remains
unresolved here is the source's restriction/extension packaging: the faithful
`H¹(Ω)` domain, the `L²(Ω)` codomain, the `C¹(Ω)` core, and the resulting
operator on that core whose norm, self-adjointness, and positivity are claimed.
-/
#check smoothNegativeLaplacianWithin Ω
#check smoothNegativeLaplacianWithin_apply Ω

/- Verified source-facing ambient surfaces for the still-unresolved restriction
and codomain in Exercise 2.13. -/
#check (Set.contDiffOne (Ω : Set (EuclideanSpace ℝ (Fin d))))
#check (MeasureTheory.Lp ℝ 2 (VariationalRegularization.domainMeasure Ω))

end

/- Generic operator-theory anchors for the remaining restricted-operator layer. -/
#check ContinuousLinearMap.unit_le_opNorm
#check LinearPMap
#check IsSelfAdjoint.dense_domain
#check ContinuousLinearMap.IsPositive.isSelfAdjoint
#check ContinuousLinearMap.isPositive_iff'
