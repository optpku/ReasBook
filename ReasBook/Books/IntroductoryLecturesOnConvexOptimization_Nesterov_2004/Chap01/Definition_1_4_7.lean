/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open EuclideanSpace

noncomputable section

universe u v

/-
Definition 1.4.7 is a source-facing bridge in first-order differential calculus on Euclidean
space.

Source/core/bridge triage:
* source-facing: the coordinate formula for the gradient in the standard Euclidean basis
* core/canonical: mathlib's `gradient`
* bridge/view: identify each coordinate with the Fréchet derivative on the corresponding basis
  vector

Primary domain:
* first-order differential calculus on finite-dimensional Euclidean spaces

Relevant owner-style declarations sampled before refining:
* `gradient` from `Mathlib.Analysis.Calculus.Gradient.Basic`
* `inner_gradient_left`, which identifies `fderiv ℝ f xBar` with pairing against `∇ f xBar`
* `inner_basisFun_real`, which recovers standard coordinates from the Euclidean basis

Owner abstraction:
* the gradient vector `∇ f xBar`

Primitive data:
* a function `f`
* a point `xBar`

Derived API:
* the directional derivative along the `i`th standard basis vector
* the coordinate formula `gradient_eq_pi_fderiv_stdBasis` under differentiability at `xBar`

Accordingly, this file keeps the owner notion `gradient` and exposes only the thin Euclidean
coordinate bridge, rather than introducing any parallel local gradient definition.
-/
recall gradient {𝕜 : Type u} {F : Type v} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (f : F → 𝕜) (x : F) : F

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => basisFun (Fin n) ℝ

/-- At a differentiability point `xBar`, the `i`th coordinate of `∇ f xBar` in the standard
Euclidean basis is the directional derivative of `f` along the `i`th basis vector. -/
-- Proof sketch: rewrite the `i`th coordinate of `∇ f xBar` as the inner product against the
-- `i`th standard basis vector using `inner_basisFun_real`, then apply `inner_gradient_left`.
theorem gradient_eq_pi_fderiv_stdBasis
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    ∇ f xBar = fun i ↦ fderiv ℝ f xBar (e i) := by
  ext i
  rw [← inner_basisFun_real]
  exact inner_gradient_left hf
