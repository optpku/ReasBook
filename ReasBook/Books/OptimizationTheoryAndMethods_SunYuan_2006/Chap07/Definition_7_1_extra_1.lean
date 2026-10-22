/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr

noncomputable section

open scoped BigOperators

-- Semantic recall: `lean_leansearch` surfaced the canonical `EuclideanSpace` owner and norm/sum
-- identities, while nearby Chapter 3 and 5 files already formalize optimization problems on
-- `EuclideanSpace ℝ (Fin n)` with `EuclideanSpace.equiv` for coordinate formulas. This file keeps
-- that ambient representation for the book's `ℝ^n` and `ℝ^m` least-squares setup.

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
local notation "residualCoords" => (EuclideanSpace.equiv (Fin m) ℝ)

/-- Chapter07 Definition 7.1-extra-1 (1): for a residual map `r : ℝ^n → ℝ^m`, the nonlinear
least-squares objective is `x ↦ (1 / 2) * r(x)ᵀ r(x)`. -/
def nonlinearLeastSquaresObjective (r : Point → Residual) (x : Point) : ℝ :=
  (1 / 2 : ℝ) * dotProduct (residualCoords (r x)) (residualCoords (r x))

/-- The nonlinear least-squares objective is the half sum of squared residual coordinates. -/
theorem nonlinearLeastSquaresObjective_eq_half_sum
    (r : Point → Residual) (x : Point) :
    nonlinearLeastSquaresObjective r x =
      (1 / 2 : ℝ) * ∑ i : Fin m, (residualCoords (r x) i) ^ (2 : ℕ) := by
  simp [nonlinearLeastSquaresObjective, dotProduct, pow_two]

/-- Canonical norm-square form of the nonlinear least-squares objective
`x ↦ (1 / 2) * ‖r(x)‖²`. -/
theorem nonlinearLeastSquaresObjective_eq_half_norm_sq
    (r : Point → Residual) (x : Point) :
    nonlinearLeastSquaresObjective r x = ((1 : ℝ) / 2) * ‖r x‖ ^ (2 : ℕ) := by
  calc
    nonlinearLeastSquaresObjective r x
        = (1 / 2 : ℝ) * ∑ i : Fin m, (residualCoords (r x) i) ^ (2 : ℕ) := by
            simpa using nonlinearLeastSquaresObjective_eq_half_sum r x
    _ = ((1 : ℝ) / 2) * ‖r x‖ ^ (2 : ℕ) := by
      simpa using
        congrArg (fun t : ℝ ↦ ((1 : ℝ) / 2) * t) (EuclideanSpace.real_norm_sq_eq (r x)).symm

/-- If the residual vanishes at `xStar`, then `xStar` is a global minimizer of the canonical
nonlinear least-squares objective on the whole space. -/
theorem nonlinearLeastSquaresObjective_isMinOn_univ_of_residual_eq_zero
    (r : Point → Residual) (xStar : Point) (hResidualZero : r xStar = 0) :
    IsMinOn (nonlinearLeastSquaresObjective r) Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro x
  have hxStar :
      nonlinearLeastSquaresObjective r xStar = 0 := by
    simp [nonlinearLeastSquaresObjective_eq_half_norm_sq, hResidualZero]
  have hnonneg : 0 ≤ nonlinearLeastSquaresObjective r x := by
    rw [nonlinearLeastSquaresObjective_eq_half_norm_sq]
    positivity
  simpa [hxStar] using hnonneg

/-- If the residual map `r` is `Cⁿ`, then the nonlinear least-squares objective
`nonlinearLeastSquaresObjective r` is also `Cⁿ`. -/
theorem ContDiff.nonlinearLeastSquaresObjective
    {k : WithTop ℕ∞} {r : Point → Residual} (hr : ContDiff ℝ k r) :
    ContDiff ℝ k (_root_.nonlinearLeastSquaresObjective r) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((contDiff_const.mul (hr.norm_sq (𝕜 := ℝ))).contDiffAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦
      _root_.nonlinearLeastSquaresObjective_eq_half_norm_sq r y)

/-- Chapter07 Definition 7.1-extra-1 (2): the associated nonlinear equation system is
`r_i(x) = 0` for every residual coordinate `i`. -/
def solvesResidualSystem (r : Point → Residual) (x : Point) : Prop :=
  ∀ i : Fin m, residualCoords (r x) i = 0

/-- Solving the residual system is equivalent to the residual vector being zero. -/
theorem solvesResidualSystem_iff_residualCoords_eq_zero
    (r : Point → Residual) (x : Point) :
    solvesResidualSystem r x ↔ residualCoords (r x) = 0 := by
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    simpa using congrFun h i

/-- Solving the residual system is equivalent to the residual vector being zero. -/
theorem solvesResidualSystem_iff_residual_eq_zero
    (r : Point → Residual) (x : Point) :
    solvesResidualSystem r x ↔ r x = 0 := by
  rw [solvesResidualSystem_iff_residualCoords_eq_zero]
  constructor
  · intro h
    apply (EuclideanSpace.equiv (Fin m) ℝ).injective
    simpa using h
  · intro h
    simp [h]

/-- Chapter07 Definition 7.1-extra-1 (3): in the data-fitting model with samples
`(t i, y i)`, the residual coordinates are `φ (t_i) x - y_i`. -/
def fittingResidual (φ : ℝ → Point → ℝ) (t y : Fin m → ℝ) (x : Point) : Residual :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ φ (t i) x - y i

/-- The coordinates of `fittingResidual φ t y x` are exactly the fitting errors
`φ (t_i) x - y_i`. -/
theorem fittingResidual_apply
    (φ : ℝ → Point → ℝ) (t y : Fin m → ℝ) (x : Point) (i : Fin m) :
    residualCoords (fittingResidual φ t y x) i = φ (t i) x - y i := by
  simp [fittingResidual]

end
