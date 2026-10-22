/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Algorithm 5.0.26 lies in the self-concordant damped-Newton domain.

Sampled owner-style declarations:
- `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the Chapter 5 owner of one-step
  self-concordant Newton updates;
- `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton owner;
- `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the canonical Chapter 5 owner for the
  Newton decrement at a domain point with nondegenerate Hessian;
- `DampedNewton.step` and `DampedNewton.Method` in Chapter 1, the general damped-Newton bridge
  owners.

Best owner abstraction:
- source-facing: the `.damped` specialization of `selfConcordantNewtonNextPoint` and
  `DampedNewton.Method.IsSelfConcordant`;
- core/canonical: the Chapter 5 owners `selfConcordantNewtonNextPoint`,
  `DampedNewton.Method.IsSelfConcordant`, `DampedNewton.Method`, and
  `NewtonDecrement.ofDetNeZero`;
- bridge/view: the explicit damped step-size formula inside the inherited Chapter 1 method owner.

Primitive data:
- an objective `f : E → ℝ`;
- a self-concordance parameter `Mf`;
- a self-concordant domain `dom`;
- a point `x ∈ dom` with nondegenerate Hessian.

Derived API:
- the Chapter 5 damped-step specialization
  `selfConcordantNewtonNextPoint f Mf SelfConcordantNewtonVariant.damped x hx hH`;
- the direct Chapter 1 bridge
  `DampedNewton.step f ⟨x, hH⟩ (1 / (1 + M_f λ_f(x)))`;
- the Chapter 1 damped-Newton method together with its Chapter 5 self-concordant refinement.

Source/core/bridge triage:
- source-facing: the `.damped` Chapter 5 specializations;
- core/canonical: the Chapter 5 self-concordant update and decrement owners;
- bridge/view: the conversion to the Chapter 1 damped-Newton owner layer.

Algorithm 5.0.26 is therefore centered on the Chapter 5 damped specialization itself. The
Chapter 1 damped-Newton owner appears directly as the canonical recursive owner layer. -/

recall selfConcordantNewtonNextPoint

recall selfConcordantNewtonNextPoint_def

recall selfConcordantNewtonStepSize

recall DampedNewton.Method.IsSelfConcordant

section

variable {f : E → ℝ} {Mf : NNReal} {x x0 : E} {dom : Set E}
variable [IsSelfConcordantOnWith dom Mf f]

/-- The damped self-concordant Newton update is the Chapter 1 damped Newton owner evaluated at
the specialized step size `(1 + M_f λ_f(x))⁻¹`. -/
theorem selfConcordantNewtonNextPoint_damped_eq_step
    (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    selfConcordantNewtonNextPoint f Mf .damped x hx hH =
      DampedNewton.step f ⟨x, hH⟩
        (1 / (1 + (Mf : ℝ) * NewtonDecrement.ofDetNeZero Mf f hx hH)) := by
  simp [selfConcordantNewtonNextPoint, selfConcordantNewtonStepSize,
    selfConcordantNewtonShift]

namespace DampedNewton.Method.IsSelfConcordant

/-- Along a damped self-concordant Newton method, the inherited Chapter 1 step size is the
canonical specialized value `(1 + M_f λ_f(x_k))⁻¹`. -/
theorem stepSize_eq_damped
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf .damped)
    (k : ℕ) :
    method.stepSize k =
      1 / (1 + (Mf : ℝ) *
        NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
          (method.hessian_nondegenerate k)) := by
  simpa [selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
    hmethod.stepSize_eq k

/-- Each step of a Chapter 5 damped self-concordant Newton method is the corresponding Chapter 1
damped Newton step with the specialized self-concordant step size. -/
theorem succ_eq_damped_step
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom Mf .damped)
    (k : ℕ) :
    method (k + 1) =
      DampedNewton.step f (method.x k)
        (1 / (1 + (Mf : ℝ) *
          NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
            (method.hessian_nondegenerate k))) := by
  rw [hmethod.succ_eq_nextPoint k]
  exact selfConcordantNewtonNextPoint_damped_eq_step
    (hmethod.iterates_mem k) (method.hessian_nondegenerate k)

end DampedNewton.Method.IsSelfConcordant

end

end
