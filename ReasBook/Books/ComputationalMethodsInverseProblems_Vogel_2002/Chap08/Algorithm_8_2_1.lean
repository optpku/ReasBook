/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_1.Clauses

public section

universe u v

namespace TVSteepestDescent

/-
Statement-stage blocker for the current source item.

The current repository snapshot still does not contain checked Chapter 8 owners
for the discrete total-variation-penalized least-squares objective `T`, the
source-specific matrix family `L(f)`, or a theorem identifying
`Kᵀ (K f - d) + α • L(f) f` with `gradient T f`.

Because those Chapter 8 anchors are still absent, this file must not guess a
new steepest-descent owner or present the pseudocode as an instance of
`SteepestDescent.iterates` or `SteepestDescent.IsExactLineSearch`. It therefore
keeps a conservative split check-only surface for the four displayed clauses of
the algorithm, with `T` and `L` explicit. The reusable clause owners themselves
live in `Book.Ch8.Algorithm_8_2_1.Clauses`.
-/
/- Algorithm 8.2.1. Main labeled source-facing blocker entry.

The current repository snapshot still lacks the checked Chapter 8 objective and
gradient-identification anchors needed for a direct steepest-descent
formalization of the total-variation-penalized least-squares algorithm.
Accordingly, this target stays a labeled check-only surface while the
clause-level source-facing owners continue to live in
`Book.Ch8.Algorithm_8_2_1.Clauses`. -/

/-- Helper for Algorithm 8.2.1: a source-facing steepest-descent run for the
displayed total-variation-penalized least-squares pseudocode consists of the
initialization clause `f 0 = f0`, the displayed gradient assignment
`g_v := Kᵀ (K f_v - d) + α • L(f_v) f_v`, the exact line-search clause
`τ_v := arg min_(τ > 0) T (f_v - τ g_v)`, and the iterate update
`f_(v + 1) = f_v - τ_v • g_v`. -/
abbrev IsRun {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f0 : n → ℝ) (K : Matrix m n ℝ) (d : m → ℝ)
    (L : (n → ℝ) → Matrix n n ℝ) (α : ℝ) (T : (n → ℝ) → ℝ)
    (f g : ℕ → n → ℝ) (τ : ℕ → ℝ) : Prop :=
  IsInitialized f0 f ∧
    HasGradientFormula K d L α f g ∧
    HasExactLineSearch T f g τ ∧
    HasIterateUpdate f g τ

/-- Algorithm 8.2.1. Source-facing surface checks for the displayed
steepest-descent clauses.

This theorem packages the four displayed clause owners from
`Book.Ch8.Algorithm_8_2_1.Clauses` without guessing the absent Chapter 8
objective/gradient-identification owners needed for a stronger run theorem. -/
theorem Algorithm_8_2_1_surface_checks {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {f0 : n → ℝ} {K : Matrix m n ℝ} {d : m → ℝ}
    {L : (n → ℝ) → Matrix n n ℝ} {α : ℝ} {T : (n → ℝ) → ℝ}
    {f g : ℕ → n → ℝ} {τ : ℕ → ℝ}
    (h_init : TVSteepestDescent.IsInitialized f0 f)
    (h_gradient : TVSteepestDescent.HasGradientFormula K d L α f g)
    (h_lineSearch : TVSteepestDescent.HasExactLineSearch T f g τ)
    (h_update : TVSteepestDescent.HasIterateUpdate f g τ) :
    TVSteepestDescent.IsRun f0 K d L α T f g τ := by
  -- Package the verified clause-level surface into the conservative run owner.
  exact ⟨h_init, h_gradient, h_lineSearch, h_update⟩

/- Algorithm 8.2.1 (1). Source-facing check for the initialization clause
`f 0 = f0`.

This first `#check` records the initialization clause `f 0 = f0`, and the
following checks record the displayed gradient assignment, exact line-search
clause, and iterate update. -/
#check
  TVSteepestDescent.IsInitialized

/-
Algorithm 8.2.1 (2). Source-facing check for the displayed gradient assignment
`g_v := Kᵀ (K f_v - d) + α L(f_v) f_v`.
-/
#check
  TVSteepestDescent.HasGradientFormula

/-
Algorithm 8.2.1 (3). Source-facing check for the exact line-search clause
`τ_v := arg min_(τ > 0) T(f_v - τ g_v)`.
-/
#check
  TVSteepestDescent.HasExactLineSearch

/-
Algorithm 8.2.1 (4). Source-facing check for the iterate update
`f_(v+1) = f_v - τ_v • g_v`.
-/
#check
  TVSteepestDescent.HasIterateUpdate

end TVSteepestDescent
