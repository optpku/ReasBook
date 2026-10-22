/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1

noncomputable section

/-
Domain sampling:
* primary domain: nonsmooth directional-derivative / Clarke generalized directional-derivative
  API
* inspected ambient mathlib owners: `HasDerivWithinAt`, `derivWithin`, `Filter.limsup`
* inspected project owners: `HasDirectionalDerivWithinAt`, `directionalDerivWithin`,
  `upperDiniDirectionalDerivWithin`, `clarkeDirectionalDerivWithin`, `LocallyLipschitzWithinAt`
* source/core/bridge triage:
  - source-facing: the within-domain Chapter 14 owners from `Definition_14_1_extra_1`
  - core/canonical: the whole-space Chapter 14 owners from `Definition_14_1_2`
  - bridge/view: the whole-space property theorems from `Lemma_14_1_1`
  - this exercise introduces no new owner
* primitive data vs derived API:
  - primitive/source-facing owners: `HasDirectionalDerivWithinAt`, `directionalDerivWithin`,
    `upperDiniDirectionalDerivWithin`, `clarkeDirectionalDerivWithin`,
    `LocallyLipschitzWithinAt`
  - derived bridge/theorem API:
    `upperDiniDirectionalDerivWithin_eq_of_hasDirectionalDerivWithinAt`,
    `upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin`, and the whole-space
    properties from `Lemma_14_1_1`
-/

/- Chapter14 Exercise 14.1 is already owned by the Chapter 14 directional-derivative API in
`Definition_14_1_extra_1.lean` and `Lemma_14_1_1.lean`. This file therefore stays at the
recall layer and reuses those declarations directly instead of restating their types through
anonymous function binders. -/

#check LocallyLipschitzWithinAt
#check HasDirectionalDerivWithinAt
#check directionalDerivWithin
#check upperDiniDirectionalDerivWithin
#check clarkeDirectionalDerivWithin

#check upperDiniDirectionalDerivWithin_eq_of_hasDirectionalDerivWithinAt
#check upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin

#check clarkeDirectionalDerivative_posHomogeneous
#check clarkeDirectionalDerivative_subadditive
#check clarkeDirectionalDerivative_abs_le
#check clarkeDirectionalDerivative_lipschitz
#check clarkeDirectionalDerivative_upperSemicontinuousAt
#check clarkeDirectionalDerivative_neg_direction
