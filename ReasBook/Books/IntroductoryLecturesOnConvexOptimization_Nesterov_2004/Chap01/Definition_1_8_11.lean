/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 1.8.11 is a source-facing recall item in the quasi-Newton inverse-Hessian domain.

Source/core/bridge triage:
* source-facing: the textbook quasi-Newton rule for a candidate next inverse-Hessian matrix
* core/canonical: `Matrix.PosDef` and the matrix action `Matrix.toEuclideanLin`
* bridge/view: the direct proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
  `Matrix.PosDef` packages symmetry together with positive definiteness

Primary domain:
* positive-definite inverse-Hessian matrices and their Euclidean-space action in quasi-Newton
  methods

Sampled owner-style declarations:
* `Matrix.PosDef` in mathlib, the canonical owner for symmetry plus positive definiteness
* `Matrix.toEuclideanLin` in mathlib, the owner linear action of a matrix on Euclidean space
* `Definition_1_4_18` in this chapter, which already recalls `Matrix.PosDef` as the canonical
  owner for `H = Hᵀ > 0`
* `VariableMetricMethod.inverseMetric_posDef` in Algorithm 1.8.10, which records positive
  definiteness of quasi-Newton inverse-metric iterates through `Matrix.PosDef`

Owner abstraction:
* the canonical owner pair `Matrix.PosDef` and `Matrix.toEuclideanLin`

Primitive data:
* the candidate next inverse-Hessian matrix `HkNext`
* the gradient difference `γk`
* the step `δk`

Derived API:
* there is no additional wrapper predicate here; the textbook quasi-Newton rule is the direct
  conjunction of the canonical SPD owner `HkNext.PosDef` with the secant equation
  `HkNext.toEuclideanLin γk = δk`

This recall file intentionally introduces no parallel public wrapper. Downstream Chapter 1 files
should use `Matrix.PosDef` together with the secant equation directly, rather than rebuilding a
local quasi-Newton predicate.
-/

section

variable (HkNext : Mat) (γk δk : E)

/- Definition 1.8.11: a quasi-Newton inverse-Hessian approximation `Hₖ₊₁` is required to be
symmetric positive definite and to satisfy the secant equation `Hₖ₊₁ γₖ = δₖ`. Using the chapter's
canonical owners, this is the proposition `HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk`, where
`Matrix.PosDef` packages `Hₖ₊₁ = Hₖ₊₁ᵀ > 0`. -/
#check (HkNext.PosDef ∧ HkNext.toEuclideanLin γk = δk : Prop)

end
