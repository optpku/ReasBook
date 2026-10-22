/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2

public section

noncomputable section

namespace GradientProjection

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The projected-gradient search direction at `f` is `-gradient J f`. -/
def direction (J : H → ℝ) (f : H) : H :=
  -gradient J f

/-- A single projected-gradient update from `f` with step size `τ` is
`P (f + τ • direction J f)`. -/
def update (P : H → H) (J : H → ℝ) (τ : ℝ) (f : H) : H :=
  P (f + τ • direction J f)

/-- The projected-gradient iterates generated from the projection `P`,
objective `J`, step-size sequence `τ`, and initial guess `f0`. -/
@[expose] def iterates (P : H → H) (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) : ℕ → H
  | 0 => f0
  | v + 1 => update P J (τ v) (iterates P J τ f0 v)

/-- A step-size sequence `τ` is an exact projected line search for
`iterates P J τ f0` when each `τ v` minimizes the line-search profile of the
projected objective `J ∘ P` over `Set.Ioi (0 : ℝ)`. -/
def IsExactLineSearch (P : H → H) (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) : Prop :=
  ∀ v,
    IsMinOn
      (LineSearch.profile (J ∘ P) (iterates P J τ f0 v)
        (direction J (iterates P J τ f0 v)))
      (Set.Ioi (0 : ℝ))
      (τ v)

/-- The zeroth projected-gradient iterate is the initial guess `f0`. -/
@[simp] theorem iterates_zero (P : H → H) (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) :
    iterates P J τ f0 0 = f0 := rfl

/-- A projected-gradient update is the projected forward-Euler step
`P (f - τ • gradient J f)`. -/
theorem update_eq_projector_sub_smul_gradient
    (P : H → H) (J : H → ℝ) (τ : ℝ) (f : H) :
    update P J τ f = P (f - τ • gradient J f) := by
  simp [update, direction, sub_eq_add_neg]

/-- Evaluating the projected line-search profile along the projected-gradient
direction recovers the objective at the algorithm update. -/
theorem profileDirection_apply_eq_update
    (P : H → H) (J : H → ℝ) (f : H) (τ : ℝ) :
    LineSearch.profile (J ∘ P) f (direction J f) τ =
      J (update P J τ f) := by
  -- Unfold the profile once in the owner module, where `direction` and `update`
  -- are definitionally transparent.
  rw [LineSearch.profile_apply]
  rfl

/-- The successor iterate is obtained by one projected-gradient update with
step size `τ v`. -/
@[simp] theorem iterates_succ (P : H → H) (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) (v : ℕ) :
    iterates P J τ f0 (v + 1) = update P J (τ v) (iterates P J τ f0 v) := rfl

/-- Characterization of exact projected line search as the pointwise minimizer
condition on the positive projected-search ray. -/
theorem isExactLineSearch_iff (P : H → H) (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) :
    IsExactLineSearch P J τ f0 ↔
      ∀ v,
        IsMinOn
          (LineSearch.profile (J ∘ P) (iterates P J τ f0 v)
            (direction J (iterates P J τ f0 v)))
          (Set.Ioi (0 : ℝ))
          (τ v) := Iff.rfl

end GradientProjection
