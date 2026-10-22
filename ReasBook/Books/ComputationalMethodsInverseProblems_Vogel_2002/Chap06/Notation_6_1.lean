/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Normed.Group.Basic

public section

namespace OutputLeastSquares

universe u v w

variable {Q : Type u} {U : Type v} {Y : Type w}

/-- Notation 6.1-extra-1 (1). Given a solved-state map `solve : Q → U`, where
`solve q` stands for the state `u = A(q)⁻¹ f` determined by the well-posed state
equation `(6.6)`, the source parameter-to-observation map `(6.10)` is the
composition `q ↦ C (solve q)`. -/
@[expose]
def parameterToObservation (C : U → Y) (solve : Q → U) : Q → Y :=
  C ∘ solve

/-- `parameterToObservation` is the canonical composition `C ∘ solve`. -/
theorem parameterToObservation_eq_comp (C : U → Y) (solve : Q → U) :
    parameterToObservation C solve = C ∘ solve :=
  rfl

/-- The pointwise defining equation for `parameterToObservation`. -/
@[simp] theorem parameterToObservation_apply (C : U → Y) (solve : Q → U) (q : Q) :
    parameterToObservation C solve q = C (solve q) :=
  rfl

/-- Notation 6.1-extra-1 (2). The regularized output-least-squares objective
from `(6.9)` is the function `T(q) = (1 / 2) * ‖F q - d‖^2 + α * J q`. The
unconstrained minimization problem is then expressed canonically by
`IsMinOn (objective F d J α) Set.univ q`. -/
@[expose] noncomputable def objective [NormedAddCommGroup Y]
    (F : Q → Y) (d : Y) (J : Q → ℝ) (α : ℝ) :
    Q → ℝ :=
  fun q ↦ (1 / 2 : ℝ) * ‖F q - d‖ ^ 2 + α * J q

/-- The pointwise defining equation for `objective`. -/
@[simp] theorem objective_def [NormedAddCommGroup Y] (F : Q → Y) (d : Y) (J : Q → ℝ)
    (α : ℝ) (q : Q) :
    objective F d J α q = (1 / 2 : ℝ) * ‖F q - d‖ ^ 2 + α * J q :=
  rfl

end OutputLeastSquares
