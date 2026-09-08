module

public import ReasLib.Optimization.LineSearch
public import ReasLib.Optimization.QuasiNewton
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

universe u

namespace BFGS

section Step

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A selected exact-line-search BFGS step, including its observable step size. -/
structure Step (F : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (B : Matrix ι ι ℝ) where
  /-- The objective is differentiable. -/
  differentiable : Differentiable ℝ F
  /-- The current Hessian approximation is positive definite. -/
  posDef : B.PosDef
  /-- The selected nonnegative line-search parameter. -/
  stepSize : ℝ
  /-- The selected parameter is an exact line-search minimizer. -/
  exact : LineSearch.IsExact F x (searchDirection B (gradient F x)) stepSize

namespace Step

/-- Construct a BFGS step from an explicit exact line-search parameter and its certificates. -/
noncomputable def ofStepSize (F : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (B : Matrix ι ι ℝ) (hF : Differentiable ℝ F) (hB : B.PosDef) (α : ℝ)
    (hα : LineSearch.IsExact F x (searchDirection B (gradient F x)) α) : Step F x B :=
  { differentiable := hF, posDef := hB, stepSize := α, exact := hα }

/-- A step constructed from `α` retains `α` as its selected line-search parameter. -/
theorem ofStepSize_stepSize (F : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (B : Matrix ι ι ℝ) (hF : Differentiable ℝ F) (hB : B.PosDef) (α : ℝ)
    (hα : LineSearch.IsExact F x (searchDirection B (gradient F x)) α) :
    (ofStepSize F x B hF hB α hα).stepSize = α := by rfl

/-- The selected step size is nonnegative and minimizes the objective along the search ray. -/
theorem exact_spec {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    0 ≤ step.stepSize ∧
      IsMinOn (fun t : ℝ ↦ F (x + t • searchDirection B (gradient F x)))
        (Set.Ici 0) step.stepSize :=
  (LineSearch.isExact_iff F x (searchDirection B (gradient F x)) step.stepSize).mp step.exact

/-- The search direction associated with a selected BFGS step. -/
noncomputable def direction {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (_step : Step F x B) : EuclideanSpace ℝ ι :=
  searchDirection B (gradient F x)

/-- The direction accessor is the inverse-Hessian BFGS search direction. -/
theorem direction_def {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    step.direction = searchDirection B (gradient F x) := by rfl

/-- The Hessian approximation sends a selected step's direction to the negative gradient. -/
theorem direction_spec {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    Matrix.mulVec B ((EuclideanSpace.equiv ι ℝ) step.direction) =
      -(EuclideanSpace.equiv ι ℝ) (gradient F x) :=
  searchDirection_spec step.posDef (gradient F x)

/-- The next iterate selected by a BFGS step. -/
noncomputable def nextPoint {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) : EuclideanSpace ℝ ι :=
  x + step.stepSize • step.direction

/-- The next point is obtained by advancing along the selected search direction. -/
theorem nextPoint_def {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    step.nextPoint = x + step.stepSize • step.direction := by rfl

/-- The displacement produced by a BFGS step. -/
noncomputable def displacement {F : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} {B : Matrix ι ι ℝ} (step : Step F x B) :
    EuclideanSpace ℝ ι :=
  step.nextPoint - x

/-- The displacement is the difference between the next and current iterates. -/
theorem displacement_def {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    step.displacement = step.nextPoint - x := by rfl

/-- The change in the objective gradient across a BFGS step. -/
noncomputable def gradientChange {F : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} {B : Matrix ι ι ℝ} (step : Step F x B) :
    EuclideanSpace ℝ ι :=
  gradient F step.nextPoint - gradient F x

/-- The gradient change is the next gradient minus the current gradient. -/
theorem gradientChange_def {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    step.gradientChange = gradient F step.nextPoint - gradient F x := by rfl

/-- The next Hessian approximation produced by a selected BFGS step. -/
noncomputable def nextHessian {F : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} {B : Matrix ι ι ℝ} (step : Step F x B) :
    Matrix ι ι ℝ :=
  update B step.displacement step.gradientChange

/-- The next Hessian accessor applies the BFGS update to the step displacement and
gradient change. -/
theorem nextHessian_def {F : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    {B : Matrix ι ι ℝ} (step : Step F x B) :
    step.nextHessian = update B step.displacement step.gradientChange := by rfl

/-- Positive step curvature makes the next BFGS Hessian approximation positive definite. -/
theorem nextHessian_posDef {F : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} {B : Matrix ι ι ℝ} (step : Step F x B)
    (hsy : 0 < dotProduct step.displacement step.gradientChange) :
    step.nextHessian.PosDef := update_posDef step.posDef hsy

end Step

end Step

end BFGS
