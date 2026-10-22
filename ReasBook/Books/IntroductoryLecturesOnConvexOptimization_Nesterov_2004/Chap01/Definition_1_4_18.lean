/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ComplexOrder MatrixOrder

/- Definition 1.4.18 is a source-facing recall of positive semidefinite and positive definite real
square matrices, implemented by the generic matrix-positivity owners below and specialized in the
textbook to `ℝ`.

Primary domain:
- matrix positivity and the Loewner order on matrices over `ℝ` or `ℂ`.

Sampled owner-style declarations:
- `Matrix.PosSemidef`
- `Matrix.PosDef`
- `Matrix.nonneg_iff_posSemidef`
- `Matrix.isStrictlyPositive_iff_posDef`

Best owner abstraction:
- the canonical matrix-positivity owners `Matrix.PosSemidef` and `Matrix.PosDef`

Primitive data:
- a square matrix `B`

Derived API:
- the order-notation bridges `Matrix.nonneg_iff_posSemidef`
- the strict-positivity bridge `Matrix.isStrictlyPositive_iff_posDef`

Source/core/bridge triage:
- source-facing: the textbook notions `B ≥ 0` and the positive-definite shorthand `B > 0` for
  real square matrices
- core/canonical: `Matrix.PosSemidef` and `Matrix.PosDef`
- bridge/view: `Matrix.nonneg_iff_posSemidef` and the canonical strict-positivity bridge
  `Matrix.isStrictlyPositive_iff_posDef`

This file therefore recalls the owner predicates directly, keeping the order-notation lemmas only
as companion bridges for the textbook notation `B ≥ 0` and the positive-definite shorthand
`B > 0`; in mathlib, the latter is bridged by `IsStrictlyPositive B ↔ B.PosDef`, not by the plain
strict order relation `0 < B`.
-/

recall Matrix.PosSemidef
    {n : Type*} {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (B : Matrix n n R) :
    Prop

recall Matrix.PosDef
    {n : Type*} {R : Type*} [Ring R] [PartialOrder R] [StarRing R] (B : Matrix n n R) :
    Prop

recall Matrix.nonneg_iff_posSemidef
    {𝕜 : Type*} {n : Type*} [RCLike 𝕜] {B : Matrix n n 𝕜} :
    0 ≤ B ↔ B.PosSemidef

recall Matrix.isStrictlyPositive_iff_posDef
    {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {B : Matrix n n 𝕜} :
    IsStrictlyPositive B ↔ B.PosDef
