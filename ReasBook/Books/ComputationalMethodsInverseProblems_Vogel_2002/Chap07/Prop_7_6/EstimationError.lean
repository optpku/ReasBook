/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

noncomputable section

namespace FilterRegularization

universe u v w

section Error

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The estimation error is the reconstruction error produced by applying `R` to noisy data
`K fTrue + noise`. -/
def estimationError (R : F →L[ℝ] H) (K : H →L[ℝ] F) (fTrue : H) (noise : F) : H :=
  R (K fTrue + noise) - fTrue

/-- The defining formula for `estimationError`. -/
theorem estimationError_def (R : F →L[ℝ] H) (K : H →L[ℝ] F) (fTrue : H) (noise : F) :
    estimationError R K fTrue noise = R (K fTrue + noise) - fTrue := by
  rfl

end Error

section ExpectedError

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The expected squared estimation error is the expectation of
`‖estimationError R K fTrue (η ω)‖ ^ 2`. -/
def expectedSqEstimationError (μ : MeasureTheory.Measure Ω)
    (R : F →L[ℝ] H) (K : H →L[ℝ] F) (fTrue : H) (η : Ω → F) : ℝ :=
  ∫ ω, ‖estimationError R K fTrue (η ω)‖ ^ 2 ∂μ

/-- The defining formula for `expectedSqEstimationError`. -/
theorem expectedSqEstimationError_def (μ : MeasureTheory.Measure Ω)
    (R : F →L[ℝ] H) (K : H →L[ℝ] F) (fTrue : H) (η : Ω → F) :
    expectedSqEstimationError μ R K fTrue η =
      ∫ ω, ‖estimationError R K fTrue (η ω)‖ ^ 2 ∂μ := by
  rfl

end ExpectedError

section Nullspace

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The nullspace component of `fTrue` with respect to `K` is the orthogonal projection of `fTrue`
onto `K.ker`. -/
def nullspaceComponent (K : H →L[ℝ] F) (fTrue : H) : H :=
  K.ker.starProjection fTrue

/-- The nullspace component is the `K.ker`-projection `K.ker.starProjection fTrue`. -/
theorem nullspaceComponent_eq_starProjection (K : H →L[ℝ] F) (fTrue : H) :
    nullspaceComponent K fTrue = K.ker.starProjection fTrue := by
  rfl

/-- The nullspace component is `fTrue - P_n fTrue` when `P_n` is rendered by
`K.kerᗮ.starProjection`. -/
theorem nullspaceComponent_eq_sub_orthogonalProjection (K : H →L[ℝ] F) (fTrue : H) :
    nullspaceComponent K fTrue = fTrue - K.kerᗮ.starProjection fTrue := by
  -- Re-express the kernel projection using the standard orthogonal splitting.
  rw [nullspaceComponent_eq_starProjection]
  exact eq_sub_iff_add_eq.mpr (K.ker.starProjection_add_starProjection_orthogonal fTrue)

end Nullspace

section Trace

variable {ι : Type u} [Fintype ι]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The noise-amplification term attached to a reconstruction operator `R` is the finite-dimensional
trace `trace (R† ∘ R)` on the data space. -/
def noiseAmplificationTrace (R : EuclideanSpace ℝ ι →L[ℝ] H) : ℝ :=
  LinearMap.trace ℝ (EuclideanSpace ℝ ι) ((R.adjoint.comp R).toLinearMap)

/-- The defining trace formula for `noiseAmplificationTrace`. -/
theorem noiseAmplificationTrace_eq_trace_adjoint_comp
    (R : EuclideanSpace ℝ ι →L[ℝ] H) :
    noiseAmplificationTrace R =
      LinearMap.trace ℝ (EuclideanSpace ℝ ι) ((R.adjoint.comp R).toLinearMap) := by
  rfl

end Trace

end FilterRegularization
