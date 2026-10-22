/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Example_2_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace

universe u

/- Example 2.18.1 lies in convex geometry on real inner-product spaces, with the quadratic
sublevel example specialized to the Euclidean matrix model.

Sampled owner-style declarations in this domain:
* mathlib `convex_halfSpace_le` for affine half-spaces;
* the project owner `innerLePolyhedron` and its bridge view `mem_innerLePolyhedron_iff`;
* the chapter owner `quadraticObjective`;
* the derived quadratic convexity theorem `Matrix.PosSemidef.convexOn_quadraticObjective`.

Best owner abstraction:
* intrinsic half-spaces and their finite intersections on a real inner-product space, with
  `innerLePolyhedron` as the project owner for the finite presentation;
* positive-semidefinite quadratic sublevel sets through `quadraticObjective` in the Euclidean
  matrix specialization.

Primitive data:
* the normal vector `a` and scalar threshold `β` for one half-space;
* the finite inequality data `a`, `b` for `innerLePolyhedron a b`;
* the matrix `A`, its positivity witness `hA`, and the radius `r`.

Derived API:
* half-space convexity from `convex_halfSpace_le`;
* the pointwise expansion `mem_innerLePolyhedron_iff`;
* quadratic sublevel convexity from `Matrix.PosSemidef.convexOn_quadraticObjective`.

Source/core/bridge triage:
* source-facing: the half-space and finite-intersection convexity examples, together with the
  Euclidean quadratic sublevel example;
* core/canonical: `convex_halfSpace_le`, `innerLePolyhedron`, `quadraticObjective`,
  `Matrix.PosSemidef`;
* bridge/view: the textbook specialization `E = EuclideanSpace ℝ (Fin n)`,
  `mem_innerLePolyhedron_iff`, and the sublevel-set reformulation of the quadratic example.
-/

section InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exmaple 2.18.1 (1): a half-space cut out by one affine linear inequality is convex on any
real inner-product space. The textbook `ℝ^n` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: specialize mathlib's owner theorem `convex_halfSpace_le` to the canonical
-- inner-product linear functional `innerₗ E a`.
theorem convex_halfspace_inner_le
    (a : E) (β : ℝ) :
    Convex ℝ {x : E | inner ℝ a x ≤ β} := by
  simpa [innerₗ_apply_apply] using
    (convex_halfSpace_le (LinearMap.isLinear (innerₗ E a)) β)

/-- Helper for Exmaple 2.18.1: part (2) shows that the region cut out by finitely many affine
inequalities is convex. The
project's owner declaration for this region is `innerLePolyhedron a b`. The textbook `ℝ^n`
statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: use the project owner set `innerLePolyhedron a b`, rewrite membership with
-- `mem_innerLePolyhedron_iff`, and apply `convex_iInter` using part (1).
theorem convex_innerLePolyhedron
    {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) :
    Convex ℝ (innerLePolyhedron a b) := by
  rw [show innerLePolyhedron a b =
      ⋂ j : Fin m, {x : E | inner ℝ (a j) x ≤ b j} by
    ext x
    simp [mem_innerLePolyhedron_iff]]
  exact convex_iInter fun j ↦ convex_halfspace_inner_le (a j) (b j)

end InnerProduct

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Helper for Exmaple 2.18.1: part (3) states that the sublevel set of a positive-semidefinite
quadratic form on `ℝ^n`
is convex. -/
-- Proof sketch: combine the upstream convexity result for positive-semidefinite quadratic
-- objectives with mathlib's owner theorem `ConvexOn.convex_le`, then simplify the owner
-- quadratic expression.
theorem convex_euclidean_posSemidef_quadratic_sublevelSet
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (r : ℝ) :
    Convex ℝ {x : E | inner ℝ (A.toEuclideanLin x) x ≤ r ^ 2} := by
  convert (hA.convexOn_quadraticObjective 0 0).convex_le (r ^ 2 / 2)
      using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, quadraticObjective, inner_zero_left,
    zero_add]
  constructor <;> intro hx <;> nlinarith

end Euclidean
