/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_17

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap
open scoped BigOperators

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

noncomputable local instance instFintypeFinDefinition362 : Fintype (Fin m) :=
  Fintype.ofFinite (Fin m)

/- This item lies in the barrier-method / polyhedral optimization domain on real
inner-product spaces.

Sampled owner-style declarations:
* `constraintSet`, `strictConstraintSet`, and `logarithmicBarrier` in
  `Chap01/Proposition_1_10_17`;
* `IsMinOn` and `isMinOn_univ_iff` in `Chap02/Definition_2_1`, the chapter's owner style for
  whole-space minimizers;
* `IsMinOn` in mathlib, the canonical owner predicate behind that chapter-level recall.

Best owner abstraction:
* the source-facing polyhedron `innerLePolyhedron a b` in a real inner-product space;
* the strict positive-slack locus `analyticBarrierDomain a b`;
* the strict-domain logarithmic barrier `analyticBarrier a b :
    C(AnalyticBarrierPoint a b, ℝ)`;
* the owner minimizer predicate `IsMinOn (analyticBarrier a b) Set.univ y`.

Primitive data:
* the affine half-space presentation `a`, `b` in a real inner-product space;
* the source-facing polyhedron `innerLePolyhedron a b`.

Derived API:
* the internal owner constraint family attached to the half-space presentation `a`, `b`;
* the strict barrier domain and the barrier-point inclusion
  `AnalyticBarrierPoint a b → interior (innerLePolyhedron a b)`;
* the strict-domain point type `AnalyticBarrierPoint a b`;
* the strict-domain barrier `analyticBarrier a b`, defined by direct reuse of the Chapter 1 owner
  `logarithmicBarrier`;
* the ambient formula view `analyticBarrierAmbient a b`, used only as a bridge for later
  differential constructions.

Source/core/bridge triage:
* source-facing: `innerLePolyhedron`, `analyticBarrier`, and the textbook analytic-center condition
  `IsMinOn (analyticBarrier a b) Set.univ y`;
* core/canonical: `constraintSet`, `strictConstraintSet`, `logarithmicBarrier`, and `IsMinOn`;
* bridge/view: the internal constraint-family helper, `analyticBarrierAmbient`, and the
  barrier-point-to-interior bridge.

The textbook formula `-∑ log (b_j - ⟪a_j, x⟫)` is mathematically meaningful only when every slack
is strictly positive, so the public barrier is kept on that strict domain rather than on all of
`E`, and it reuses the Chapter 1 owner barrier directly. The ambient formula is retained only as a
bridge view for later Hessian-based constructions.
-/

-- Internal owner constraint family whose nonpositive locus is `innerLePolyhedron a b`.
private def polyhedronConstraints
    (a : Fin m → E) (b : Fin m → ℝ) : Fin m → C(E, ℝ) :=
  fun j ↦ ((innerSL ℝ (a j) : E →L[ℝ] ℝ) : C(E, ℝ)) - ContinuousMap.const E (b j)

/-- The polyhedron cut out by the affine inequalities `⟪aⱼ, x⟫ ≤ bⱼ`. -/
def innerLePolyhedron (a : Fin m → E) (b : Fin m → ℝ) : Set E :=
  constraintSet (polyhedronConstraints a b)

/-- Membership in `innerLePolyhedron a b` is exactly satisfaction of all defining inequalities. -/
@[simp] theorem mem_innerLePolyhedron_iff
    (a : Fin m → E) (b : Fin m → ℝ) {x : E} :
    x ∈ innerLePolyhedron a b ↔ ∀ j : Fin m, inner ℝ (a j) x ≤ b j := by
  simp [innerLePolyhedron, polyhedronConstraints]

/-- The owner half-space presentation `innerLePolyhedron a b` is a polyhedron in the chapter's
canonical sense. -/
theorem innerLePolyhedron_isPolyhedron (a : Fin m → E) (b : Fin m → ℝ) :
    Set.IsPolyhedron (innerLePolyhedron a b) := by
  refine ⟨
    m,
    fun j ↦ (innerSL ℝ (a j)).toLinearMap.toAffineMap - const ℝ E (b j),
    fun _ ↦ .le,
    ?_
  ⟩
  ext x
  simp [innerLePolyhedron, polyhedronConstraints, ConstraintSense.Holds]

/-- Any set identified with an owner half-space presentation `innerLePolyhedron a b` is a
polyhedron in the chapter's canonical sense. -/
theorem isPolyhedron_of_eq_innerLePolyhedron
    {Q : Set E} (a : Fin m → E) (b : Fin m → ℝ) (hQ : Q = innerLePolyhedron a b) :
    Set.IsPolyhedron Q := by
  simpa [hQ] using innerLePolyhedron_isPolyhedron a b

/-- The strict positive-slack locus on which the analytic barrier is defined. -/
def analyticBarrierDomain (a : Fin m → E) (b : Fin m → ℝ) : Set E :=
  strictConstraintSet (polyhedronConstraints a b)

/-- Membership in `analyticBarrierDomain a b` means that every slack `bⱼ - ⟪aⱼ, x⟫` is strictly
positive. -/
@[simp] theorem mem_analyticBarrierDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) {x : E} :
    x ∈ analyticBarrierDomain a b ↔ ∀ j : Fin m, inner ℝ (a j) x < b j := by
  simp [analyticBarrierDomain, polyhedronConstraints]

/-- The subtype of points in the strict barrier domain. This is the natural owner carrier for the
analytic barrier and its minimizers. -/
abbrev AnalyticBarrierPoint (a : Fin m → E) (b : Fin m → ℝ) :=
  {x : E // x ∈ analyticBarrierDomain a b}

/-- The analytic barrier on its strict domain, obtained by reusing the Chapter 1 logarithmic
slack formula. -/
def analyticBarrier
    (a : Fin m → E) (b : Fin m → ℝ) : C(AnalyticBarrierPoint a b, ℝ) :=
  logarithmicBarrier (polyhedronConstraints a b)

/-- The ambient formula underlying `analyticBarrier a b`. It is only a bridge view; the owner
barrier is `analyticBarrier a b` on `AnalyticBarrierPoint a b`. -/
def analyticBarrierAmbient (a : Fin m → E) (b : Fin m → ℝ) : E → ℝ :=
  fun x ↦ -∑ j : Fin m, Real.log (b j - inner ℝ (a j) x)

/-- Evaluating `analyticBarrier a b` gives the textbook sum of negative logarithms of the positive
slacks. -/
@[simp] theorem analyticBarrier_apply
    (a : Fin m → E) (b : Fin m → ℝ) (x : AnalyticBarrierPoint a b) :
    analyticBarrier a b x = -∑ j : Fin m, Real.log (b j - inner ℝ (a j) x) := by
  change (logarithmicBarrier (polyhedronConstraints a b)) x =
    -∑ j : Fin m, Real.log (b j - inner ℝ (a j) x)
  rw [logarithmicBarrier_apply]
  rw [neg_inj]
  simp [polyhedronConstraints, neg_sub]

/- The source-facing strict barrier domain is presentation-dependent. It agrees with the intrinsic
interior of the underlying polyhedron only when the chosen inequality presentation recovers that
interior. -/
/-- If the chosen affine-inequality presentation recovers the intrinsic interior of
`innerLePolyhedron a b`, then the strict positive-slack locus is exactly that interior. -/
theorem analyticBarrierDomain_eq_interior_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ)
    (hinterior : interior (innerLePolyhedron a b) ⊆ analyticBarrierDomain a b) :
    analyticBarrierDomain a b = interior (innerLePolyhedron a b) := by
  simpa [analyticBarrierDomain, innerLePolyhedron] using
    strictConstraintSet_eq_interior_constraintSet (polyhedronConstraints a b) hinterior

section

variable (a : Fin m → E) (b : Fin m → ℝ) (y : AnalyticBarrierPoint a b)

/- Definition 3.62: a point `y` of the strict positive-slack locus is an analytic center exactly
when it globally minimizes the analytic barrier
`x ↦ -∑ⱼ log (bⱼ - ⟪aⱼ, x⟫)` on that strict domain. If one additionally knows that the chosen
inequality presentation recovers `interior (innerLePolyhedron a b)`, the same minimizer condition
may be transported to that intrinsic interior by the bridge theorem above. The canonical owner is
`IsMinOn`. -/
recall IsMinOn

set_option linter.hashCommand false in
#check IsMinOn (analyticBarrier a b) Set.univ y

end

/-- Every point of the strict barrier domain lies in the interior of the underlying polyhedron. -/
theorem analyticBarrierPoint_mem_interior
    (a : Fin m → E) (b : Fin m → ℝ) (y : AnalyticBarrierPoint a b) :
    (y : E) ∈ interior (innerLePolyhedron a b) := by
  simpa [analyticBarrierDomain, innerLePolyhedron] using
    (strictConstraintSet_subset_interior_constraintSet (polyhedronConstraints a b) y.property)

end
