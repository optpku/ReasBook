/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic

public section

namespace Complex.FiniteDimensional

/-- Scoped notation for the textbook finite complex coordinate space `ℂ^n`. -/
scoped notation "ℂ^[" n "]" => EuclideanSpace ℂ (Fin n)

/-- Scoped notation for complex-valued `n_x × n_y` arrays with finite
coordinate sets. -/
scoped notation "ℂ^[" n_x ", " n_y "]" => Matrix (Fin n_x) (Fin n_y) ℂ

end Complex.FiniteDimensional
