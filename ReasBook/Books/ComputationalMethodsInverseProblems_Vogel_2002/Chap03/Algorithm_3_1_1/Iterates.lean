/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.ExactStep
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

namespace SteepestDescent

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The steepest-descent search direction at `f` is `-gradient J f`. -/
def direction (J : H → ℝ) (f : H) : H :=
  -gradient J f

/-- A single steepest-descent update sends `f` to `f + τ • direction J f`. -/
def update (J : H → ℝ) (τ : ℝ) (f : H) : H :=
  f + τ • direction J f

/-- The steepest-descent iterates generated from the initial guess `f0` and the
step-size sequence `τ`. -/
@[expose] def iterates (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) : ℕ → H
  | 0 => f0
  | v + 1 => update J (τ v) (iterates J τ f0 v)

/-- A step-size sequence `τ` is an exact line search for the steepest-descent
iterates of `J` from `f0` when, at each iteration `v`, the value `τ v`
is positive and minimizes the line-search profile over `Set.Ioi (0 : ℝ)`. -/
def IsExactLineSearch (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) : Prop :=
  ∀ v,
    LineSearch.IsExactStep
      J
      (iterates J τ f0 v)
      (direction J (iterates J τ f0 v))
      (τ v)

/-- The zeroth steepest-descent iterate is the initial guess `f0`. -/
@[simp] theorem iterates_zero (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) :
    iterates J τ f0 0 = f0 := rfl

/-- A steepest-descent update is the forward-Euler step `f - τ • gradient J f`
for the gradient flow `df/dt = - gradient J f`. -/
theorem update_eq_sub_smul_gradient (J : H → ℝ) (τ : ℝ) (f : H) :
    update J τ f = f - τ • gradient J f := by
  simp [update, direction, sub_eq_add_neg]

/-- The successor iterate is obtained by applying the one-step steepest-descent
update with step size `τ v`. -/
@[simp] theorem iterates_succ (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) (v : ℕ) :
    iterates J τ f0 (v + 1) = update J (τ v) (iterates J τ f0 v) := rfl

/-- A sequence is the steepest-descent iterate sequence for `J`, step sizes
`τ`, and initial value `f0` exactly when it has the same initial value and
follows the steepest-descent update recurrence. -/
theorem recurrence_iff_eq_iterates
    (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) (f : ℕ → H) :
    ((f 0 = f0) ∧ ∀ v : ℕ, f (v + 1) = update J (τ v) (f v)) ↔
      f = iterates J τ f0 := by
  constructor
  · rintro ⟨h0, hsucc⟩
    funext v
    induction v with
    | zero =>
        exact h0
    | succ v hv =>
        rw [hsucc, iterates_succ, hv]
  · intro hf
    subst hf
    constructor
    · rfl
    · intro v
      rfl

/-- Characterization of exact line search as the pointwise minimizer condition
on the positive line-search ray. -/
theorem isExactLineSearch_iff (J : H → ℝ) (τ : ℕ → ℝ) (f0 : H) :
    IsExactLineSearch J τ f0 ↔
      ∀ v,
        LineSearch.IsExactStep
          J
          (iterates J τ f0 v)
          (direction J (iterates J τ f0 v))
          (τ v) :=
  Iff.rfl

end SteepestDescent
