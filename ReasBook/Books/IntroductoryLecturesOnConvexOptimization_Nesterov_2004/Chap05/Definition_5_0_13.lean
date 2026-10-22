/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Definition 5.0.13 lies in the Hessian-local-norm / Dikin-ellipsoid domain.

 Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian-induced local norm;
* the notation `‖u‖[f; x]`, the source-facing surface for that owner;
* `hessianLocalNorm_def`, the bridge back to the square-root Hessian quadratic form;
* the notational-owner precedent `W(G, v)` in `Definition_5_4_5_6`, showing that source-facing
  ellipsoid owners in this project should expose textbook notation on the theorem surface.

Best owner abstraction:
* source-facing: `openDikinEllipsoid f x r` and `dikinEllipsoid f x r`;
* core/canonical: `‖y - x‖[f; x]` for the local-norm quantity;
* bridge/view: the membership lemmas and `hessianLocalNorm_def`.

Primitive data:
* a function `f`;
* a center `x`;
* a radius `r`.

 Derived API:
* the open-ball owner `openDikinEllipsoid`;
* the closed-ball owner `dikinEllipsoid`;
* the textbook notations `W⁰[f; x](r)` and `W[f; x](r)`;
* membership lemmas stated first in local-norm form, then as raw square-root expansions, and
  finally in quadratic-form form under the Hessian-positivity regime.

This file owns the Dikin-ellipsoid layer directly rather than recalling it from a downstream
theorem file. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The open Dikin ellipsoid of `f` centered at `x` with radius `r` is the open ball in the
Hessian local norm at `x`. -/
def openDikinEllipsoid (f : E → ℝ) (x : E) (r : ℝ) : Set E :=
  {y | ‖y - x‖[f; x] < r}

/-- Definition 5.0.13: the Dikin ellipsoid of `f` at `x` with radius `r` is the closed ball in
the Hessian local norm at `x`. -/
def dikinEllipsoid (f : E → ℝ) (x : E) (r : ℝ) : Set E :=
  {y | ‖y - x‖[f; x] ≤ r}

namespace DikinEllipsoidNotation

/-- Textbook notation for the open Dikin ellipsoid centered at `x` with radius `r` for the
ambient objective `f`. -/
scoped notation:max "W⁰[" f "; " x "](" r ")" => openDikinEllipsoid f x r

/-- Textbook notation for the closed Dikin ellipsoid centered at `x` with radius `r` for the
ambient objective `f`. -/
scoped notation:max "W[" f "; " x "](" r ")" => dikinEllipsoid f x r

end DikinEllipsoidNotation

open scoped DikinEllipsoidNotation

/-- Membership in `W⁰[f; x](r)` is exactly the strict local-norm inequality
`‖y - x‖[f; x] < r`. -/
@[simp] theorem mem_openDikinEllipsoid_iff
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W⁰[f; x](r) ↔ ‖y - x‖[f; x] < r :=
  Iff.rfl

/-- Expanding membership in `W⁰[f; x](r)` gives the square root of the Hessian quadratic form.
The quadratic-form reformulation below is the source-facing ellipsoid API in the Hessian-positive
regime. -/
theorem mem_openDikinEllipsoid_iff_sqrt_hessian
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W⁰[f; x](r) ↔
      Real.sqrt (inner ℝ (y - x) (hessian f x (y - x))) < r := by
  simp [openDikinEllipsoid, hessianLocalNorm_def]

/-- In the Hessian-positive regime and for a nonnegative radius, membership in `W⁰[f; x](r)` is
equivalent to the strict quadratic bound `⟪∇² f(x) (y - x), y - x⟫ < r²`. -/
theorem mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
    (f : E → ℝ) (x y : E) {r : ℝ}
    (hquad_nonneg : 0 ≤ inner ℝ (y - x) (hessian f x (y - x))) (hr : 0 ≤ r) :
    y ∈ W⁰[f; x](r) ↔
      inner ℝ (y - x) (hessian f x (y - x)) < r ^ (2 : ℕ) := by
  rw [mem_openDikinEllipsoid_iff_sqrt_hessian]
  simpa using (Real.sqrt_lt hquad_nonneg hr)

/-- Membership in `W[f; x](r)` is exactly the closed local-norm inequality
`‖y - x‖[f; x] ≤ r`. -/
@[simp] theorem mem_dikinEllipsoid_iff
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W[f; x](r) ↔ ‖y - x‖[f; x] ≤ r :=
  Iff.rfl

/-- Expanding membership in `W[f; x](r)` gives the square root of the Hessian quadratic form.
The quadratic-form reformulation below is the source-facing ellipsoid API in the Hessian-positive
regime. -/
theorem mem_dikinEllipsoid_iff_sqrt_hessian
    (f : E → ℝ) (x y : E) (r : ℝ) :
    y ∈ W[f; x](r) ↔
      Real.sqrt (inner ℝ (y - x) (hessian f x (y - x))) ≤ r := by
  simp [dikinEllipsoid, hessianLocalNorm_def]

/-- For a nonnegative radius, membership in `W[f; x](r)` is equivalent to the quadratic bound
`⟪∇² f(x) (y - x), y - x⟫ ≤ r²`. The nonnegativity of the quadratic form is supplied
automatically by `Real.sqrt`. -/
theorem mem_dikinEllipsoid_iff_hessian_quadratic_le_sq
    (f : E → ℝ) (x y : E) {r : ℝ} (hr : 0 ≤ r) :
    y ∈ W[f; x](r) ↔
      inner ℝ (y - x) (hessian f x (y - x)) ≤ r ^ (2 : ℕ) := by
  rw [mem_dikinEllipsoid_iff_sqrt_hessian]
  constructor
  · intro hy
    exact (Real.sqrt_le_iff.mp (by simpa using hy)).2
  · intro hy
    exact (Real.sqrt_le_iff.mpr ⟨hr, by simpa using hy⟩)

end
