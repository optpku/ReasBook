/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2

/-
Domain sampling:
* primary domain: semismoothness of locally Lipschitz maps `F : ℝ^n → ℝ^n`
* inspected project owner: `Definition_14_8_extra_2`
* source/core/bridge triage:
  - source-facing: `LocallyLipschitzAt`, `generalizedJacobian`,
    `hasSemismoothLinearizationLimit`, `semismoothDifferenceQuotient`, `SemismoothAt`
  - bridge/view: `hasSemismoothLinearizationLimit_iff`, `semismoothAt_iff`
  - derived property: `SemismoothAt.existsCommonLimit`
* this exercise introduces no new owner
-/

/- Chapter14 Exercise 14.2 is already owned by the Chapter 14 semismoothness API in
`Definition_14_8_extra_2.lean`. This file therefore stays at the recall layer and reuses those
canonical source-facing declarations directly instead of restating their types through anonymous
function binders. -/

#check LocallyLipschitzAt
#check generalizedJacobian
#check hasSemismoothLinearizationLimit
#check hasSemismoothLinearizationLimit_iff
#check semismoothDifferenceQuotient
#check semismoothDifferenceQuotient_apply
#check SemismoothAt
#check semismoothAt_iff
#check SemismoothAt.existsCommonLimit
