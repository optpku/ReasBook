/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Definition 2.39 is source-facing in the finite max-type affine-linearization domain on a real
Hilbert space.

Sampled owner-style declarations:
* `maxTypeObjective`, the canonical finite-max owner for a nonempty family;
* `maxTypeObjective_apply`, the pointwise bridge exposing that owner as a finite maximum;
* `firstOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical owner affine model of a
  single component at a base point;
* `firstOrderTaylorModelAt_apply`, the pointwise bridge exposing the textbook affine formula for
  that owner model;
* `ConvexOn.sup` in mathlib, the owner pattern behind convexity of finite maxima.

Best owner abstraction:
* core/canonical owner: the finite-max owner
  `maxTypeObjective (fun i ↦ firstOrderTaylorModelAt (fi i) xBar)`;
* primitive component owner: `firstOrderTaylorModelAt (fi i) xBar` for each component;
* source-facing owner: the finite maximum of those owner affine models,
  `maxTypeAffineApproximation fi xBar`.

Primitive data:
* a nonempty finite component family `fi : ι → E → ℝ`;
* a base point `xBar : E`.

Derived API:
* the pointwise finite-max formula in terms of `firstOrderTaylorModelAt`;
* the expanded gradient formula as a companion bridge theorem.

Source/core/bridge triage:
* source-facing/core: `maxTypeAffineApproximation fi xBar`;
* core/canonical: `firstOrderTaylorModelAt (fi i) xBar`;
* bridge/view: `maxTypeAffineApproximation_apply`.

The public owner here is therefore the max-type affine model itself, but its primitive body is
organized as the generic finite-max owner `maxTypeObjective` applied to the canonical component
owner `firstOrderTaylorModelAt`. No parallel local alias such as `maxTypeLinearization` or
`maxAffineModel` is introduced, and no second ad hoc `Finset.sup'` owner is kept beside
`maxTypeObjective`.
-/

/-- The pointwise maximum of a nonempty finite family of real-valued functions. -/
def maxTypeObjective {X : Type*} (fi : ι → X → ℝ) : X → ℝ :=
  fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i : ι ↦ fi i x

/-- Evaluating the max-type objective at `x` returns the finite maximum of the component values. -/
theorem maxTypeObjective_apply {X : Type*} (fi : ι → X → ℝ) (x : X) :
    maxTypeObjective fi x =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ fi i x) :=
  rfl

/-- The finite maximum is bounded above by `t` at `x` exactly when every component is. -/
theorem maxTypeObjective_le_iff {X : Type*} (fi : ι → X → ℝ) (x : X) (t : ℝ) :
    maxTypeObjective fi x ≤ t ↔ ∀ i : ι, fi i x ≤ t := by
  rw [maxTypeObjective_apply, Finset.sup'_le_iff]
  simp

section Convexity

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- A nonempty finite maximum of convex functions is convex on the same set. -/
theorem maxTypeObjective_convexOn
    (s : Set E) (fi : ι → E → ℝ) (hfi : ∀ i : ι, ConvexOn ℝ s (fi i)) :
    ConvexOn ℝ s (maxTypeObjective fi) := by
  classical
  have hdef : maxTypeObjective fi = Finset.univ.sup' Finset.univ_nonempty fi := by
    ext x
    simp [maxTypeObjective]
  rw [hdef]
  exact
    Finset.sup'_induction Finset.univ_nonempty fi
      (fun _ hg₁ _ hg₂ ↦ hg₁.sup hg₂)
      (fun i _ ↦ hfi i)

end Convexity

section AffineApproximation

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Definition 2.39: the affine approximation of a finite max-type objective at `xBar` is the
pointwise maximum of the canonical first-order Taylor models of its components at `xBar`. -/
def maxTypeAffineApproximation (fi : ι → E → ℝ) (xBar : E) : E → ℝ :=
  maxTypeObjective (fun i ↦ firstOrderTaylorModelAt (fi i) xBar)

/-- Evaluating the max-type affine approximation at `x` gives the finite maximum of the component
first-order Taylor models at `xBar`. -/
theorem maxTypeAffineApproximation_apply_firstOrderTaylorModelAt
    (fi : ι → E → ℝ) (xBar x : E) :
    maxTypeAffineApproximation fi xBar x =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : ι ↦ firstOrderTaylorModelAt (fi i) xBar x) :=
  maxTypeObjective_apply (fun i ↦ firstOrderTaylorModelAt (fi i) xBar) x

/- Evaluating the max-type affine approximation gives the textbook finite maximum of the
component affine models at `xBar`. -/
theorem maxTypeAffineApproximation_apply
    (fi : ι → E → ℝ) (xBar x : E) :
    maxTypeAffineApproximation fi xBar x =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : ι ↦ fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar)) := by
  simpa [firstOrderTaylorModelAt_apply] using
    maxTypeAffineApproximation_apply_firstOrderTaylorModelAt fi xBar x

/-- The affine max-type approximation is convex on every convex set. -/
theorem maxTypeAffineApproximation_convexOn
    (s : Set E) (hs : Convex ℝ s)
    (fi : ι → E → ℝ) (xBar : E) :
    ConvexOn ℝ s (maxTypeAffineApproximation fi xBar) := by
  refine maxTypeObjective_convexOn s (fun i ↦ firstOrderTaylorModelAt (fi i) xBar) ?_
  intro i
  exact firstOrderTaylorModelAt_convexOn s hs (fi i) xBar

end AffineApproximation
