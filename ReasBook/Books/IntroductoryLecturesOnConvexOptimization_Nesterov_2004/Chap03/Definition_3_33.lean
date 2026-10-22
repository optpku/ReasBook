/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (f : E → ℝ) (xStar : E)

/- Definition 3.33 lies in the unconstrained convex minimization domain on `ℝⁿ`.

Sampled owner-style declarations:
* mathlib `ConvexOn`, the canonical owner predicate for convexity of a real-valued objective on a
  set, specialized here to `Set.univ`;
* `SetConstrainedMinimizationProblem.unconstrained` in `Chap01/Definition_1_3_3`, the project
  owner for whole-space minimization problems;
* mathlib `IsMinOn` and `isMinOn_univ_iff`, the canonical owner and textbook bridge for global
  minimizers on `Set.univ`;
* mathlib `IsMinOn.isGLB` and `IsGLB.csInf_eq`, the attained-infimum bridge for the minimum value
  over the whole range.

Best owner abstraction:
* source-facing: a whole-space convex objective on `ℝⁿ`;
* core/canonical: `ConvexOn ℝ Set.univ f` together with
  `SetConstrainedMinimizationProblem.unconstrained f`;
* bridge/view: the attained-infimum theorem `isMinOn_iff_eq_sInf_range`.

Primitive data:
* the ambient objective `f : E → ℝ` for the source-facing definition;
* for the bridge theorem, only a function into an order type.

Derived API:
* the whole-space convexity predicate `ConvexOn ℝ Set.univ f`;
* the ambient minimization-problem owner `SetConstrainedMinimizationProblem.unconstrained f`;
* the generic order-theoretic minimum-value identity on `Set.range f`.

This file therefore deletes the duplicate local wrapper
`UnconstrainedConvexMinimizationProblem`: its primitive objective data are already owned by the
Chapter 1 unconstrained minimization owner, while convexity itself is already owned canonically by
`ConvexOn`. The remaining theorem is a genuine bridge from whole-space minimality to the attained
infimum of the range, and it lives at the generic order owner layer because its proof does not use
Euclidean or real-specific structure. -/

/-- Definition 3.33: an unconstrained convex minimization problem on `ℝⁿ` is a real-valued
objective `f : ℝⁿ → ℝ` together with the canonical whole-space convexity predicate
`ConvexOn ℝ Set.univ f`. -/
abbrev IsUnconstrainedConvexMinimizationProblem (f : E → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f

/-- Helper for Definition 3.33: a point `x*` is an optimal solution exactly when it is a global
minimizer of the objective on the whole ambient space. -/
abbrev IsOptimalSolution (f : E → ℝ) (xStar : E) : Prop :=
  IsMinOn f Set.univ xStar

set_option linter.hashCommand false in
#check ConvexOn ℝ Set.univ f

/- The same objective is packaged by the Chapter 1 owner for whole-space minimization problems. -/
set_option linter.hashCommand false in
#check (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)

/- Global minimizers of the unconstrained objective are the canonical whole-space minimizers
`IsMinOn f Set.univ xStar`. -/
set_option linter.hashCommand false in
#check IsMinOn f Set.univ xStar

end

section

universe u v

variable {X : Type u} {Y : Type v} [ConditionallyCompleteLattice Y]

/-- If the objective values are bounded below, then a point `x*` is a global minimizer exactly
when its objective value equals the infimum of the values of the objective on the whole ambient
space. -/
theorem isMinOn_iff_eq_sInf_range {f : X → Y} {xStar : X}
    (hbelow : BddBelow (Set.range f)) :
    IsMinOn f Set.univ xStar ↔ f xStar = sInf (Set.range f) := by
  constructor
  · intro hxMin
    have hglb : IsGLB (Set.range f) (f xStar) := by
      have hglb_univ : IsGLB {y | ∃ z ∈ Set.univ, f z = y} (f xStar) :=
        hxMin.isGLB (Set.mem_univ xStar)
      have hset : ({y | ∃ z ∈ Set.univ, f z = y} : Set Y) = Set.range f := by
        ext y
        constructor
        · rintro ⟨z, -, rfl⟩
          exact ⟨z, rfl⟩
        · rintro ⟨z, rfl⟩
          exact ⟨z, Set.mem_univ z, rfl⟩
      exact hset ▸ hglb_univ
    exact (hglb.csInf_eq ⟨f xStar, ⟨xStar, rfl⟩⟩).symm
  · intro hx
    rw [isMinOn_univ_iff]
    intro x
    simpa [hx] using csInf_le hbelow (show f x ∈ Set.range f from ⟨x, rfl⟩)

end
