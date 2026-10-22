/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2.Clauses

public section

universe u v

namespace TVNewton

/-
Algorithm 8.2.2. Newton's Method for Total Variation-Penalized Least Squares.

The current repository snapshot still lacks the checked Chapter 8 objective and
total-variation diffusion/Hessian owners needed for a direct Newton-method
formalization of the total-variation-penalized least-squares algorithm.
Accordingly, this target remains a thin labeled `#check` surface while the
reusable clause owners continue to live in
`Book.Ch8.Algorithm_8_2_2.Clauses`.

This first `#check` records the initialization clause `f 0 = f0`, and the
following checks record the displayed gradient and penalty-Hessian assignment,
the total-Hessian and Newton-step assignment, and the exact line-search and
iterate-update surface. -/

/-- Helper for Algorithm 8.2.2: a source-facing Newton run for the displayed
total-variation-penalized least-squares pseudocode consists of the
initialization clause `f 0 = f0`, the displayed gradient and penalty-Hessian
assignments, the total-Hessian and Newton-step assignments, and the exact
line-search and iterate-update clause. -/
abbrev IsRun {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (f0 : ι → ℝ) (K : Matrix κ ι ℝ) (d : κ → ℝ)
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (α : ℝ) (T : (ι → ℝ) → ℝ)
    (f g s : ℕ → ι → ℝ)
    (HJ H : ℕ → Matrix ι ι ℝ) (τ : ℕ → ℝ) : Prop :=
  IsInitialized f0 f ∧
    HasGradientAndPenaltyHessian K d α L L' f g HJ ∧
    HasHessianAndNewtonStep K α g s HJ H ∧
    HasLineSearchAndIterateUpdate T f s τ

/-- Algorithm 8.2.2. Source-facing surface checks for the displayed Newton
total-variation clauses.

This theorem packages the four displayed clause owners from
`Book.Ch8.Algorithm_8_2_2.Clauses` into the conservative Newton-run owner
without guessing the absent Chapter 8 objective and Hessian-identification
infrastructure needed for a stronger formalization. -/
theorem Algorithm_8_2_2_surface_checks {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {f0 : ι → ℝ} {K : Matrix κ ι ℝ} {d : κ → ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {α : ℝ} {T : (ι → ℝ) → ℝ}
    {f g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ} {τ : ℕ → ℝ}
    (h_init : TVNewton.IsInitialized f0 f)
    (h_gradientHessian : TVNewton.HasGradientAndPenaltyHessian K d α L L' f g HJ)
    (h_hessianStep : TVNewton.HasHessianAndNewtonStep K α g s HJ H)
    (h_lineSearchUpdate : TVNewton.HasLineSearchAndIterateUpdate T f s τ) :
    TVNewton.IsRun f0 K d L L' α T f g s HJ H τ := by
  -- Package the verified clause-level surface into the conservative Newton run owner.
  exact ⟨h_init, h_gradientHessian, h_hessianStep, h_lineSearchUpdate⟩

#check
  TVNewton.IsInitialized

/- Algorithm 8.2.2 (2). Source-facing blocker entry for the displayed gradient
and penalty-Hessian assignments
`g_v := Kᵀ (K f_v - d) + α • L(f_v) f_v` and
`H_J := L(f_v) + L' (f_v) (f_v)`. -/
#check
  TVNewton.HasGradientAndPenaltyHessian

/- Algorithm 8.2.2 (3). Source-facing blocker entry for the displayed total-
Hessian and Newton-step assignments
`H := Kᵀ K + α • H_J` and `s_v := -H⁻¹ g_v`.
-/
#check
  TVNewton.HasHessianAndNewtonStep

/- Algorithm 8.2.2 (4). Source-facing blocker entry for the exact line-search
and iterate-update clauses
`τ_v := arg min_(τ > 0) T (f_v + τ s_v)` and
`f_(v + 1) = f_v + τ_v • s_v`. -/
#check
  TVNewton.HasLineSearchAndIterateUpdate

end TVNewton
