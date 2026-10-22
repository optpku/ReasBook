/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module

universe u

/- Definition 6.1 lies in the chapter's Fenchel-conjugacy domain.

Relevant owner-style declarations sampled before refinement:
- `Dual ℝ E`, the canonical algebraic-dual owner notation for real linear functionals;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing inner-product-space bridge built
  from this owner by evaluation along `innerₗ`;
- `fenchelSmoothApproximation` in `Definition_6_2`, the immediate Chapter 6 downstream owner that
  consumes `fenchelConjugate` directly.

Best owner abstraction:
- core/canonical: `fenchelConjugate`;
- bridge/view: later specializations from `Dual ℝ E` to inner-product or continuous-dual surfaces.

Primitive data:
- `f : E → EReal`.

Derived API:
- `fenchelConjugate_apply`.

Source/core/bridge triage:
- core/canonical: the dual-space Fenchel supremum owner itself.

This file is the owner, not a bridge. The conjugate formula only needs the primitive module
structure needed to evaluate linear functionals, so the old `AddCommGroup` header was stronger
than necessary; the refined owner now lives over `AddCommMonoid E` and leaves stronger ambient
structures to downstream bridge files.
-/
variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Definition 6.1: the Fenchel conjugate of an extended-real function is the pointwise supremum
of the affine functionals `x ↦ ⟪s, x⟫ - f x`; for a proper convex function, this is the textbook
Fenchel conjugate. -/
def fenchelConjugate (f : E → EReal) : Dual ℝ E → EReal :=
  fun s ↦ ⨆ x : E, (s x : EReal) - f x

/-- Evaluating the Fenchel conjugate recovers its defining supremum formula. -/
@[simp] theorem fenchelConjugate_apply (f : E → EReal) (s : Dual ℝ E) :
    fenchelConjugate f s = ⨆ x : E, (s x : EReal) - f x :=
  rfl

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous-dual Fenchel conjugate of a real-valued function, obtained by evaluating the
core owner `fenchelConjugate` on `StrongDual ℝ E`. -/
abbrev strongFenchelConjugate (f : E → ℝ) : StrongDual ℝ E → EReal :=
  fun s ↦ fenchelConjugate (fun x ↦ (f x : EReal)) s

/-- Evaluating the continuous-dual Fenchel conjugate recovers the defining supremum formula. -/
@[simp] theorem strongFenchelConjugate_apply (f : E → ℝ) (s : StrongDual ℝ E) :
    strongFenchelConjugate f s = ⨆ x : E, (s x : EReal) - (f x : EReal) :=
  fenchelConjugate_apply (fun x ↦ (f x : EReal)) s
