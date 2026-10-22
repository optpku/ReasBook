/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic

public section

namespace FilterRegularization

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The truncation error is the reconstruction bias `((R ∘L K) - 1) fTrue`. -/
@[expose]
def truncationError (R : F →L[ℝ] E) (K : E →L[ℝ] F) (fTrue : E) : E :=
  (((R ∘L K) - (1 : E →L[ℝ] E)) fTrue)

/-- The defining formula for `truncationError`. -/
theorem truncationError_eq (R : F →L[ℝ] E) (K : E →L[ℝ] F) (fTrue : E) :
    truncationError R K fTrue = (((R ∘L K) - (1 : E →L[ℝ] E)) fTrue) := by
  unfold truncationError
  rfl

/-- The noise error is the propagated perturbation `R η`. -/
@[expose]
def noiseError (R : F →L[ℝ] E) (η : F) : E :=
  R η

/-- The defining formula for `noiseError`. -/
theorem noiseError_eq (R : F →L[ℝ] E) (η : F) :
    noiseError R η = R η := by
  unfold noiseError
  rfl

end FilterRegularization
