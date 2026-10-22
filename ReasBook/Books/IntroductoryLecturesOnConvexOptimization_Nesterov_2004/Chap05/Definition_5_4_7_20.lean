/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open EuclideanSpace (positiveOrthant)

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

private def hypographGap (ξ : Xₙ → ℝ) : Xₙ × ℝ → ℝ :=
  fun xt ↦ xt.2 - ξ xt.1

/- Definition 5.4.7.20 lies in the Chapter 5 positive-orthant / logarithmic-sublevel-barrier
domain.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` from `Chap01/Definition_1_10_2`, the intrinsic owner for the
  strict positive orthant `ℝⁿ_{++}`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the earlier Chapter 5 barrier
  owner on the same orthant domain;
* `sublevelLogBarrier` and `sublevelLogBarrier_apply` from `Theorem_5_1_4`, the canonical Chapter
  5 owner for logarithmic barriers of strict sublevel sets;
* ordinary product-space function evaluation on `Xₙ × ℝ`, the ambient owner layer for the scalar
  gap map `(x, t) ↦ t - ξ(x)`.

Best owner abstraction:
* source-facing: the hypograph domain `𝒟 = {(x, t) ∈ ℝⁿ_{++} × ℝ | t < ξ(x)}` and the barrier
  `Ψ(x, t) = -log (ξ(x) - t) + F(x)`;
* core/canonical: `sublevelLogBarrier (fun xt : Xₙ × ℝ ↦ xt.2 - ξ xt.1) 0`;
* bridge/view: the textbook membership and evaluation lemmas below.

Primitive data:
* the positive-orthant function `ξ : Xₙ → ℝ`;
* the base barrier term `F : Xₙ → ℝ`.

Derived API:
* the source-facing hypograph domain, expressed as the strict sublevel set of the gap map
  `(x, t) ↦ t - ξ(x)`;
* the source-facing barrier `hypographBarrierPsi F ξ`, obtained by adding `F(x)` to the canonical
  strict-sublevel logarithmic barrier.

This refinement keeps the textbook domain and barrier names, but deletes the duplicate raw
logarithmic-barrier body in favor of the Chapter 5 owner `sublevelLogBarrier`. -/

/-- The domain `𝒟 = {(x, t) ∈ ℝ^n_{++} × ℝ : t < ξ(x)}` attached to a function
`ξ : ℝ^n_{++} → ℝ`. -/
def hypographBarrierDomain (ξ : Xₙ → ℝ) : Set (Xₙ × ℝ) :=
  {xt | hypographGap ξ xt < 0}

-- Proof sketch: unfold `hypographBarrierDomain`; membership is exactly the strict inequality
-- `t < ξ(x)` defining the hypograph of `ξ` over the positive orthant.
/-- Membership in `hypographBarrierDomain ξ` means exactly that the scalar coordinate lies below
the value of `ξ` at the positive-orthant point. -/
@[simp]
theorem mem_hypographBarrierDomain_iff
    (ξ : Xₙ → ℝ) (x : Xₙ) (t : ℝ) :
    (x, t) ∈ hypographBarrierDomain ξ ↔ t < ξ x := by
  simp [hypographBarrierDomain, hypographGap]

/-- Definition 5.4.7.20: for functions `F, ξ : ℝ^n_{++} → ℝ`, the associated barrier on
`𝒟 = {(x, t) : t < ξ(x)}` is `Ψ(x, t) = -log (ξ(x) - t) + F(x)`. -/
def hypographBarrierPsi (F ξ : Xₙ → ℝ) : hypographBarrierDomain ξ → ℝ :=
  fun xt ↦ sublevelLogBarrier (hypographGap ξ) 0 xt.1 + F xt.1.1

-- Proof sketch: unfold `hypographBarrierPsi`; the subtype argument carries a pair `(x, t)` in the
-- domain, and evaluation substitutes that pair into the defining formula.
/-- Evaluating `hypographBarrierPsi F ξ` recovers the formula
`Ψ(x, t) = -log (ξ(x) - t) + F(x)` for a domain point `(x, t)`. -/
@[simp]
theorem hypographBarrierPsi_apply
    (F ξ : Xₙ → ℝ) (xt : hypographBarrierDomain ξ) :
    hypographBarrierPsi F ξ xt =
      -Real.log (ξ xt.1.1 - xt.1.2) + F xt.1.1 := by
  simp [hypographBarrierPsi, hypographGap, sublevelLogBarrier]

end
