/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Example_6_2.DiffusionMatrices
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Notation_6_1

public section

open OneDimensionalDiffusion
open OutputLeastSquares

namespace Exercise62

/-- Positive conductivity samples on the `n + 1` grid intervals of the one-dimensional
Figure 6.2 benchmark. -/
abbrev AdmissibleConductivity (n : ℕ) :=
  {κ : Fin (n + 1) → ℝ // ∀ i, 0 < κ i}

/-- The Figure 6.2 benchmark data: the exact discrete right-hand side, the observation matrix,
and the observed data vector used by the regularized output-least-squares objective. -/
structure Benchmark (n m : ℕ) where
  rhs : Fin n → ℝ
  observationMatrix : Matrix (Fin m) (Fin n) ℝ
  data : Fin m → ℝ

namespace Benchmark

variable {n m : ℕ}

/-- The benchmark observation operator is the matrix action on the discrete state. -/
@[expose] def observe (benchmark : Benchmark n m) : (Fin n → ℝ) → Fin m → ℝ :=
  fun u ↦ Matrix.mulVec benchmark.observationMatrix u

/-- The exact discrete state for a positive conductivity sample is obtained by inverting the
Chapter 6 stiffness matrix. -/
@[expose] noncomputable def exactState (benchmark : Benchmark n m) :
    AdmissibleConductivity n → Fin n → ℝ :=
  fun κ ↦ Matrix.mulVec (stiffnessMatrix n κ)⁻¹ benchmark.rhs

/-- The source parameter-to-observation map for the Figure 6.2 benchmark. -/
@[expose] noncomputable def parameterToObservation (benchmark : Benchmark n m) :
    AdmissibleConductivity n → Fin m → ℝ :=
  OutputLeastSquares.parameterToObservation benchmark.observe benchmark.exactState

/-- The regularized output-least-squares objective attached to the Figure 6.2 benchmark. -/
@[expose] noncomputable def objective (benchmark : Benchmark n m)
    (J : AdmissibleConductivity n → ℝ) (α : ℝ) :
    AdmissibleConductivity n → ℝ :=
  OutputLeastSquares.objective benchmark.parameterToObservation benchmark.data J α

/-- The benchmark observation operator is matrix multiplication by `observationMatrix`. -/
@[simp] theorem observe_apply (benchmark : Benchmark n m) (u : Fin n → ℝ) :
    benchmark.observe u = Matrix.mulVec benchmark.observationMatrix u :=
  rfl

/-- The exact discrete state is the inverse-stiffness action on the benchmark right-hand side. -/
@[simp] theorem exactState_apply (benchmark : Benchmark n m) (κ : AdmissibleConductivity n) :
    benchmark.exactState κ = Matrix.mulVec (stiffnessMatrix n κ)⁻¹ benchmark.rhs :=
  rfl

/-- The exact discrete state solves the benchmark stiffness equation. -/
theorem stiffnessMatrix_mulVec_exactState (benchmark : Benchmark n m)
    (κ : AdmissibleConductivity n) :
    Matrix.mulVec (stiffnessMatrix n κ) (benchmark.exactState κ) = benchmark.rhs := by
  have hdet : IsUnit (stiffnessMatrix n κ).det := by
    exact (stiffnessMatrix n κ).isUnit_iff_isUnit_det.mp
      ((stiffnessMatrix_posDefOfPos n κ κ.2).isUnit)
  rw [exactState_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The source parameter-to-observation map is the composition of the benchmark observation
operator with the exact discrete state map. -/
theorem parameterToObservation_eq_comp (benchmark : Benchmark n m) :
    benchmark.parameterToObservation = benchmark.observe ∘ benchmark.exactState :=
  OutputLeastSquares.parameterToObservation_eq_comp benchmark.observe benchmark.exactState

/-- The source parameter-to-observation map is the composition of the observation operator with
the exact discrete state map. -/
@[simp] theorem parameterToObservation_apply (benchmark : Benchmark n m)
    (κ : AdmissibleConductivity n) :
    benchmark.parameterToObservation κ = benchmark.observe (benchmark.exactState κ) :=
  OutputLeastSquares.parameterToObservation_apply benchmark.observe benchmark.exactState κ

/-- Pointwise formula for the benchmark objective. -/
@[simp] theorem objective_apply (benchmark : Benchmark n m) (J : AdmissibleConductivity n → ℝ)
    (α : ℝ) (κ : AdmissibleConductivity n) :
    benchmark.objective J α κ =
      (1 / 2 : ℝ) * ‖benchmark.parameterToObservation κ - benchmark.data‖ ^ 2 + α * J κ :=
  OutputLeastSquares.objective_def benchmark.parameterToObservation benchmark.data J α κ

end Benchmark

end Exercise62
