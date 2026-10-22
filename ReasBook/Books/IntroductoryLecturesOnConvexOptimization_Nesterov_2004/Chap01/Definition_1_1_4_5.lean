/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap

namespace Set

/-- A map on a subset is affine when it is the restriction of an ambient affine map. -/
def AffineOn {X Y : Type*} (Q : Set X) (k : Type*) [Ring k] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : Q → Y) : Prop :=
  ∃ g : X →ᵃ[k] Y, ∀ x (hx : x ∈ Q), f ⟨x, hx⟩ = g x

end Set

/- Definition 1.1.4.5 lies in the affine/polyhedral constrained-optimization domain.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` in `Chap01/Definition_1_1_3`, the project owner for
  finitely many scalar constraints on an ambient type
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Chap01/Definition_1_1_1`, the
  packaged finite constraint family
* `Set.AffineOn`
* `Set.SatisfiesInteriorBallCondition` in `Chap03/Definition_3_59`, a chapter-level set-owned
  predicate for an elementary property of subsets
* `AffineMap.pi`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m` for the constrained-problem owner
* `problem.constraintVector` for the packaged affine constraint family
* `Set.AffineOn` and `Set.IsPolyhedron` for affine/polyhedral data on the basic feasible set

Source/core/bridge triage:
* `source-facing`: `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `core/canonical`: `FunctionalConstraintsMinimizationProblem X m`, `Set.AffineOn`,
  `Set.IsPolyhedron`
* `bridge/view`: the Euclidean inner-product representation theorems in the
  `GeneralMinimizationProblem` specialization

Primitive data:
* `problem.basicFeasibleSet`
* `problem.senses`
* affine data of the packaged owner map `problem.constraintVector`

Derived API:
* coordinatewise affineness of the scalar constraint family
* Euclidean inner-product formulas for affine scalar constraints
-/

namespace Set

/-- Helper for Definition 1.1.4.5: a subset of a real module is polyhedral if it is cut out by
finitely many affine inequalities and equalities. -/
def IsPolyhedron {X : Type*} [AddCommGroup X] [Module ℝ X] (Q : Set X) : Prop :=
  ∃ k : ℕ, ∃ g : Fin k → X →ᵃ[ℝ] ℝ,
    ∃ senses : Fin k → ConstraintSense,
      Q = {x | ∀ i, (senses i).Holds (g i x)}

end Set

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-- Helper for Definition 1.1.4.5: the owner constraint vector is affine on the basic feasible
set exactly when each scalar constraint is affine there. -/
theorem constraintVector_affineOn_iff_forall_constraint_affineOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector ↔
      ∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  constructor
  · rintro ⟨g, hg⟩ j
    -- Project the ambient affine witness onto the `j`th coordinate.
    refine ⟨(EuclideanSpace.projₗ j).toAffineMap.comp g, ?_⟩
    intro x hx
    change problem.constraintVector ⟨x, hx⟩ j =
      ((EuclideanSpace.projₗ j).toAffineMap.comp g) x
    simpa using congrArg (fun y : F ↦ y j) (hg x hx)
  · intro h
    choose g hg using h
    -- Assemble the coordinatewise affine witnesses into one Euclidean-valued affine map.
    refine ⟨
      ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.toAffineMap).comp (pi g),
      ?_⟩
    intro x hx
    ext j
    change problem.constraintVector ⟨x, hx⟩ j = _
    simp [constraintVector, hg j x hx]

/-- Definition 1.1.4.5: A minimization problem is linearly constrained when its packaged owner
constraint family is affine on the basic feasible set and that basic feasible set is polyhedral. -/
def IsLinearlyConstrained (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector ∧
    problem.basicFeasibleSet.IsPolyhedron

/-- Helper for Definition 1.1.4.5: expanding the owner formulation recovers the textbook condition
that each scalar constraint is affine on the basic feasible set and that the basic feasible set is
polyhedral. -/
theorem isLinearlyConstrained_iff (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsLinearlyConstrained ↔
      (∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j)) ∧
        problem.basicFeasibleSet.IsPolyhedron := by
  constructor
  · rintro ⟨hconstraint, hpoly⟩
    -- Rewrite the packaged affine condition into the coordinatewise textbook formulation.
    exact ⟨problem.constraintVector_affineOn_iff_forall_constraint_affineOn.mp hconstraint, hpoly⟩
  · rintro ⟨hconstraint, hpoly⟩
    -- Repackage the scalar affine data into the owner-level affine constraint vector.
    exact ⟨problem.constraintVector_affineOn_iff_forall_constraint_affineOn.mpr hconstraint, hpoly⟩

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has affine functional
constraints. -/
theorem IsLinearlyConstrained.constraint_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearlyConstrained) (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  -- Read off the `j`th scalar affine constraint from the textbook reformulation.
  exact (problem.isLinearlyConstrained_iff.mp h).1 j

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has an affine packaged owner
constraint vector. -/
theorem IsLinearlyConstrained.constraintVector_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsLinearlyConstrained) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.constraintVector := by
  -- The packaged affine condition is the first field of the definition.
  exact h.1

/-- Helper for Definition 1.1.4.5: a linearly constrained problem has a polyhedral basic feasible
set. -/
theorem IsLinearlyConstrained.isPolyhedron {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearlyConstrained) :
    problem.basicFeasibleSet.IsPolyhedron := by
  -- The polyhedrality clause is the second field of the definition.
  exact h.2

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- An affine scalar function on `ℝⁿ` can be written as an inner product with a coefficient vector
plus a constant term. -/
-- Proof sketch: identify an affine functional with a linear functional plus a constant, then use
-- the finite-dimensional real Riesz representation theorem to write the linear part as an inner
-- product with a coefficient vector.
theorem functionIsAffine_iff_exists_inner_add (problem : GeneralMinimizationProblem n m)
    (f : problem.basicFeasibleSet → ℝ) :
    Set.AffineOn problem.basicFeasibleSet ℝ f ↔
      ∃ a : E, ∃ b : ℝ,
        ∀ x (hx : x ∈ problem.basicFeasibleSet),
          f ⟨x, hx⟩ = inner ℝ a x + b := by
  constructor
  · rintro ⟨g, hg⟩
    let L : E →L[ℝ] ℝ :=
      { toLinearMap := g.linear
        cont := g.linear.continuous_of_finiteDimensional }
    let a : E := (InnerProductSpace.toDual ℝ E).symm L
    refine ⟨a, g 0, ?_⟩
    intro x hx
    -- Decompose the ambient affine witness into its linear part and constant part.
    calc
      f ⟨x, hx⟩ = g x := hg x hx
      _ = g.linear x + g 0 := by simpa using congrFun g.decomp x
      _ = inner ℝ a x + g 0 := by
        congr 1
        change (L : E → ℝ) x = inner ℝ a x
        rw [InnerProductSpace.toDual_symm_apply (x := x) (y := L)]
  · rintro ⟨a, b, hf⟩
    let g : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E b + ((innerSL ℝ a).toLinearMap).toAffineMap
    refine ⟨g, ?_⟩
    intro x hx
    -- Repackage the textbook inner-product formula as an ambient affine map.
    exact by
      simp [g, hf x hx, add_comm]

/-- An affine scalar constraint on `ℝⁿ` can be written as an inner product with a coefficient
vector plus a constant term. -/
theorem constraintIsAffine_iff_exists_inner_add (problem : GeneralMinimizationProblem n m)
    (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) ↔
      ∃ a : E, ∃ b : ℝ,
        ∀ x (hx : x ∈ problem.basicFeasibleSet),
          problem.constraints j ⟨x, hx⟩ = inner ℝ a x + b := by
  simpa using functionIsAffine_iff_exists_inner_add problem (problem.constraints j)

/-- Every functional constraint of a linearly constrained Euclidean problem is given by an inner
product with a coefficient vector plus a constant term on the basic feasible set. -/
theorem IsLinearlyConstrained.constraint_eq_inner_add {problem : GeneralMinimizationProblem n m}
    (h : problem.IsLinearlyConstrained) (j : Fin m) :
    ∃ a : E, ∃ b : ℝ,
      ∀ x (hx : x ∈ problem.basicFeasibleSet),
        problem.constraints j ⟨x, hx⟩ = inner ℝ a x + b :=
  (constraintIsAffine_iff_exists_inner_add problem j).mp (h.constraint_isAffine j)

end GeneralMinimizationProblem
