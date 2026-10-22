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

open scoped BigOperators

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

section TotalVariation

/-- Definition 1.3-extra-1 (2). The discrete one-dimensional total-variation
penalty is the sum of absolute adjacent differences of a finite real signal. -/
def discreteTotalVariation {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin (n - 1),
    let left : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩
    let hn : 1 ≤ n :=
      Nat.succ_le_of_lt (Nat.zero_lt_of_lt (lt_of_lt_of_le i.2 (Nat.sub_le n 1)))
    let right : Fin n := ⟨i.1 + 1,
      lt_of_lt_of_le (Nat.succ_lt_succ i.2) (le_of_eq (Nat.sub_add_cancel hn))⟩
    |f right - f left|

/-- The defining adjacent-difference formula for `discreteTotalVariation`. -/
theorem discreteTotalVariation_def {n : ℕ} (f : EuclideanSpace ℝ (Fin n)) :
    discreteTotalVariation f =
      ∑ i : Fin (n - 1),
        let left : Fin n := ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le n 1)⟩
        let hn : 1 ≤ n :=
          Nat.succ_le_of_lt (Nat.zero_lt_of_lt (lt_of_lt_of_le i.2 (Nat.sub_le n 1)))
        let right : Fin n := ⟨i.1 + 1,
          lt_of_lt_of_le (Nat.succ_lt_succ i.2) (le_of_eq (Nat.sub_add_cancel hn))⟩
        |f right - f left| := by
  -- This rewrite theorem repeats the defining adjacent-difference sum verbatim.
  rfl

end TotalVariation

end VariationalRegularization
