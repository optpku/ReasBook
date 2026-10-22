/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/-
Definition 5.4.8.1 lies in the separable convex optimization domain.

Sampled owner-style declarations:
- `LagrangianProblem` and `LagrangianProblem.feasibleSet` in `Chap01/Definition_1_10_2`, the
  project owner for primitive objective-and-constraint data and the derived inequality feasible
  set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  ambient feasible-set / objective interface used by optimal-value statements;
- mathlib `ConvexOn.comp_affineMap`, the canonical affine-precomposition theorem for convex
  functions;
- mathlib `ConvexOn.smul` and `ConvexOn.add`, the canonical positive-scaling and sum operations
  used to build the block functions `qᵢ`.

Best owner abstraction:
- source-facing: `SeparableOptimizationProblem E m`, the textbook block data over an ambient real
  vector space `E`;
- core/canonical: `LagrangianProblem E m`, together with the inherited
  `SetConstrainedMinimizationProblem E` bridge;
- bridge/view: the Euclidean specialization
  `toConvexInequalityConstrainedMinimizationProblem`.

Primitive data:
- the block sizes;
- the positive weights;
- the affine functionals `E →ᵃ[ℝ] ℝ`;
- the scalar convex functions;
- the right-hand sides `β₁, …, βₘ`.

Derived API:
- the block functions `qFunction`;
- the textbook constraint family `constraintFunction`;
- the convexity lemmas for these derived functions;
- the canonical Chapter 1 bridge `toLagrangianProblem`, together with the inherited owner bridge
  `(problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem`;
- the Euclidean Chapter 5 specialization
  `toConvexInequalityConstrainedMinimizationProblem`.

The refinement therefore keeps the source-facing separable data, but replaces the coordinate
`ℝⁿ` presentation `(aᵢⱼ, bᵢⱼ)` by the intrinsic affine owner `E →ᵃ[ℝ] ℝ` and makes the generic
Chapter 1 problem owners primary. The Chapter 5 whole-space owner remains only as a Euclidean
specialization.
-/

/-- Definition 5.4.8.1: a separable optimization problem on a real vector space `E` is specified
by finite families of positive weights `αᵢⱼ`, affine functionals `ℓᵢⱼ : E →ᵃ[ℝ] ℝ`, convex
scalar functions `fᵢⱼ : ℝ → ℝ`, and right-hand sides `β₁, …, βₘ`, producing the functions
`qᵢ(x) = ∑ⱼ αᵢⱼ fᵢⱼ (ℓᵢⱼ(x))` and the problem of minimizing `q₀(x)` subject to
`qᵢ(x) ≤ βᵢ` for `i = 1, …, m`. -/
structure SeparableOptimizationProblem (E : Type u) [AddCommGroup E] [Module ℝ E] (m : ℕ) where
  /-- The number `mᵢ` of separable summands in `qᵢ`. -/
  blockSize : Fin (m + 1) → ℕ
  /-- The positive coefficients `αᵢⱼ` multiplying the scalar convex terms. -/
  weight (i : Fin (m + 1)) (j : Fin (blockSize i)) : ℝ
  /-- Each coefficient `αᵢⱼ` is positive. -/
  weight_pos (i : Fin (m + 1)) (j : Fin (blockSize i)) : 0 < weight i j
  /-- The affine functionals `ℓᵢⱼ : E →ᵃ[ℝ] ℝ`. -/
  affineMap (i : Fin (m + 1)) (j : Fin (blockSize i)) : E →ᵃ[ℝ] ℝ
  /-- The scalar convex functions `fᵢⱼ : ℝ → ℝ`. -/
  scalarFunction (i : Fin (m + 1)) (j : Fin (blockSize i)) : ℝ → ℝ
  /-- Each scalar function `fᵢⱼ` is convex on all of `ℝ`. -/
  scalarFunction_convex (i : Fin (m + 1)) (j : Fin (blockSize i)) :
      ConvexOn ℝ Set.univ (scalarFunction i j)
  /-- The right-hand sides `β₁, …, βₘ` of the inequality constraints. -/
  constraintBound : Fin m → ℝ

namespace SeparableOptimizationProblem

/-- The separable convex function `qᵢ(x) = ∑ⱼ αᵢⱼ fᵢⱼ (ℓᵢⱼ(x))`. -/
def qFunction (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) : E → ℝ :=
  fun x ↦
    ∑ j : Fin (problem.blockSize i),
      problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x)

/-- The `i`-th inequality constraint function `q_{i+1}`. -/
abbrev constraintFunction (problem : SeparableOptimizationProblem E m) (i : Fin m) : E → ℝ :=
  problem.qFunction i.succ

/-- Expanding `qFunction` recovers the defining finite sum of weighted scalar convex terms. -/
theorem qFunction_apply
    (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) (x : E) :
    problem.qFunction i x =
      ∑ j : Fin (problem.blockSize i),
        problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x) :=
  rfl

/-- Each block function `qᵢ` is convex on the whole ambient space. -/
theorem qFunction_convex
    (problem : SeparableOptimizationProblem E m) (i : Fin (m + 1)) :
    ConvexOn ℝ Set.univ (problem.qFunction i) := by
  classical
  let term : Fin (problem.blockSize i) → E → ℝ := fun j x ↦
    problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x)
  have hterm : ∀ j : Fin (problem.blockSize i), ConvexOn ℝ Set.univ (term j) := by
    intro j
    have hcomp : ConvexOn ℝ Set.univ
        (fun x ↦ problem.scalarFunction i j (problem.affineMap i j x)) := by
      simpa using (problem.scalarFunction_convex i j).comp_affineMap (problem.affineMap i j)
    simpa [term] using ConvexOn.smul (le_of_lt (problem.weight_pos i j)) hcomp
  have hsum :
      ∀ s : Finset (Fin (problem.blockSize i)),
        ConvexOn ℝ Set.univ (fun x ↦ s.sum (fun j ↦ term j x)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
    · intro j s hj hs
      simpa [Finset.sum_insert hj] using (hterm j).add hs
  simpa [qFunction, term] using hsum Finset.univ

/-- Each textbook constraint function `q_{i+1}` is convex on the whole ambient space. -/
theorem constraintFunction_convex
    (problem : SeparableOptimizationProblem E m) (i : Fin m) :
    ConvexOn ℝ Set.univ (problem.constraintFunction i) := by
  simpa [constraintFunction] using problem.qFunction_convex i.succ

/-- The canonical Chapter 1 Lagrangian problem attached to a separable optimization problem. -/
def toLagrangianProblem (problem : SeparableOptimizationProblem E m) : LagrangianProblem E m where
  objective := problem.qFunction 0
  constraints := fun i x ↦ problem.constraintFunction i x - problem.constraintBound i

/-- A separable optimization problem coerces to its canonical Chapter 1 Lagrangian owner. -/
instance : Coe (SeparableOptimizationProblem E m) (LagrangianProblem E m) where
  coe := toLagrangianProblem

/-- A separable optimization problem can be used as its objective function `q₀ : E → ℝ`. -/
instance : CoeFun (SeparableOptimizationProblem E m) (fun _ ↦ E → ℝ) where
  coe problem := problem.qFunction 0

/-- The Chapter 1 Lagrangian owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toLagrangianProblem_apply
    (problem : SeparableOptimizationProblem E m) (x : E) :
    problem.toLagrangianProblem x = problem.qFunction 0 x :=
  rfl

/-- Evaluating a separable optimization problem returns the source-facing objective `q₀`. -/
@[simp] theorem coe_apply (problem : SeparableOptimizationProblem E m) (x : E) :
    problem x = problem.qFunction 0 x :=
  rfl

@[simp] theorem toLagrangianProblem_constraints_apply
    (problem : SeparableOptimizationProblem E m) (i : Fin m) (x : E) :
    (problem : LagrangianProblem E m).constraints i x =
      problem.constraintFunction i x - problem.constraintBound i :=
  rfl

/-- The feasible set consists of those `x ∈ E` satisfying `qᵢ(x) ≤ βᵢ` for every
constraint index `i = 1, …, m`. -/
def feasibleSet (problem : SeparableOptimizationProblem E m) : Set E :=
  problem.toLagrangianProblem.feasibleSet

/-- Membership in the feasible set is equivalent to satisfying all separable inequality
constraints. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : SeparableOptimizationProblem E m) (x : E) :
    x ∈ problem.feasibleSet ↔
      ∀ i : Fin m, problem.qFunction i.succ x ≤ problem.constraintBound i := by
  rw [feasibleSet]
  constructor
  · intro hx i
    exact sub_nonpos.mp ((problem.toLagrangianProblem.mem_feasibleSet_iff).1 hx i)
  · intro hx
    exact (problem.toLagrangianProblem.mem_feasibleSet_iff).2
      (fun i ↦ sub_nonpos.mpr (hx i))

section Euclidean

variable {n : ℕ}

/-- The Euclidean Chapter 5 whole-space convex inequality owner attached to a separable
optimization problem. This is a specialization of the generic Chapter 1 bridge. -/
def toConvexInequalityConstrainedMinimizationProblem
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m) :
    ConvexInequalityConstrainedMinimizationProblem n m where
  objective := problem.qFunction 0
  constraints := fun i x ↦ problem.constraintFunction i x - problem.constraintBound i
  objective_convex := problem.qFunction_convex 0
  constraints_convex i := by
    simpa [sub_eq_add_neg] using
      (problem.constraintFunction_convex i).add_const (-problem.constraintBound i)

/-- A Euclidean separable optimization problem coerces to its Chapter 5 whole-space owner. -/
instance : Coe (SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (ConvexInequalityConstrainedMinimizationProblem n m) where
  coe := toConvexInequalityConstrainedMinimizationProblem

/-- The Chapter 5 owner evaluates to the source-facing objective `q₀`. -/
@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_apply
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem.toConvexInequalityConstrainedMinimizationProblem x = problem.qFunction 0 x :=
  rfl

@[simp] theorem toConvexInequalityConstrainedMinimizationProblem_constraints_apply
    (problem : SeparableOptimizationProblem (EuclideanSpace ℝ (Fin n)) m)
    (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    (problem : ConvexInequalityConstrainedMinimizationProblem n m).constraints i x =
      problem.constraintFunction i x - problem.constraintBound i :=
  rfl

end Euclidean

end SeparableOptimizationProblem

end
