/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_6

-- Semantic recall: the primary domain here is smooth local optimality in finite-dimensional
-- Euclidean spaces. The canonical owner abstraction is the chapter's second-order local-minimum /
-- gradient / Hessian theorem API, built on mathlib's `IsLocalMin` derivative owners rather than
-- on exercise-local wrapper names.
--
-- Owner sampling for this refine pass:
-- * mathlib: `IsLocalMin.hasFDerivAt_eq_zero`
-- * mathlib: `IsLocalMin.fderiv_eq_zero`
-- * Chapter 1: `gradient_eq_zero_of_isLocalMinOn`
-- * Chapter 1: `iteratedFDeriv_nonneg_of_isLocalMinOn_secondOrderNecessary`
-- * Chapter 1: `isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos`
--
-- Primitive data vs derived API:
-- * primitive data: an open domain, a `C¹`/`C²` function, and a local minimizer hypothesis
-- * derived API: vanishing gradient, Hessian nonnegativity, and strict-local-minimum conclusion

/-
Chapter01 Exercise 1.20

This exercise adds no new primitive owner beyond the existing Chapter 1 local-optimality results.
Its three clauses are already recorded upstream by the canonical chapter theorems
`gradient_eq_zero_of_isLocalMinOn`,
`iteratedFDeriv_nonneg_of_isLocalMinOn_secondOrderNecessary`, and
`isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos`.

The refined file therefore stays at the recall layer and deletes the parallel exercise-local
theorem names.
-/
#check gradient_eq_zero_of_isLocalMinOn
#check iteratedFDeriv_nonneg_of_isLocalMinOn_secondOrderNecessary
#check isStrictLocalMin_of_isStationaryPoint_of_iteratedFDeriv_pos
