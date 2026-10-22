/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace VariationalRegularization

universe u v

section Tikhonov

variable {m : Type u} [Fintype m]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The Tikhonov quadratic objective `‖K f - d‖ ^ 2 + α * ‖f‖ ^ 2`. -/
def tikhonovObjective (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (f : EuclideanSpace ℝ n) : ℝ :=
  ‖K.toEuclideanLin f - d‖ ^ 2 + α * ‖f‖ ^ 2

/-- The defining formula for `tikhonovObjective`. -/
theorem tikhonovObjective_def (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (f : EuclideanSpace ℝ n) :
    tikhonovObjective K d α f = ‖K.toEuclideanLin f - d‖ ^ 2 + α * ‖f‖ ^ 2 := by
  -- This companion theorem just unfolds the quadratic objective.
  rfl

/-- Definition 1.3-extra-1 (1). A vector is a variational Tikhonov solution when
it minimizes the Tikhonov objective on `Set.univ`. -/
def IsTikhonovMinimizer (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (f : EuclideanSpace ℝ n) : Prop :=
  IsMinOn (tikhonovObjective K d α) Set.univ f

/-- The defining characterization of `IsTikhonovMinimizer`. -/
theorem IsTikhonovMinimizer_iff (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (f : EuclideanSpace ℝ n) :
    IsTikhonovMinimizer K d α f ↔ IsMinOn (tikhonovObjective K d α) Set.univ f := by
  -- This iff is the proposition-valued definition written explicitly.
  rfl

end Tikhonov

end VariationalRegularization
