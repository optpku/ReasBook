/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_3.Clauses

public section

/-
Algorithm 8.2.3. Lagged Diffusivity Fixed Point Method for Total
Variation-Penalized Least Squares.

The reusable clause owners live in `Book.Ch8.Algorithm_8_2_3.Clauses`. The
printed pseudocode defines `s_(v + 1)` but updates with
`f_(v + 1) := f_v + s_v`, so the source-facing surface preserves that indexing
mismatch explicitly instead of guessing a corrected self-map or run owner.
-/

/-
Algorithm 8.2.3. Lagged Diffusivity Fixed Point Method for Total
Variation-Penalized Least Squares.

The current repository snapshot keeps this item at a thin source-facing
check-only surface: the reusable clause owners live in
`Book.Ch8.Algorithm_8_2_3.Clauses`, while the displayed pseudocode still has
the source indexing mismatch between `s_(v + 1)` and the update
`f_(v + 1) := f_v + s_v`. This main labeled `#check` records the
initialization clause `f 0 = f0`, and the following checks record the
displayed diffusion, gradient, approximate-Hessian, shifted-step, and
iterate-update clauses without inventing a stronger run owner than the checked
clause API supports.
-/
/-- Algorithm 8.2.3. Source-facing surface checks for the lagged-diffusivity
fixed-point clauses.

This theorem packages the six displayed clause owners from
`Book.Ch8.Algorithm_8_2_3.Clauses` without introducing a stronger iterate/run
owner than the source indexing supports. -/
theorem Algorithm_8_2_3_surface_checks {κ : Type*} {ι : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {f0 : ι → ℝ}
    {f g s : ℕ → ι → ℝ}
    {Lv H : ℕ → Matrix ι ι ℝ}
    (h_init : TVLaggedDiffusivity.IsInitialized f0 f)
    (h_diffusion : TVLaggedDiffusivity.HasDiffusionAssignment L f Lv)
    (h_gradient : TVLaggedDiffusivity.HasGradientFormula K d α f g Lv)
    (h_hessian : TVLaggedDiffusivity.HasApproximateHessianFormula K α Lv H)
    (h_step : TVLaggedDiffusivity.HasShiftedStepFormula g s H)
    (h_update : TVLaggedDiffusivity.HasIterateUpdate f s) :
    TVLaggedDiffusivity.IsInitialized f0 f ∧
      TVLaggedDiffusivity.HasDiffusionAssignment L f Lv ∧
      TVLaggedDiffusivity.HasGradientFormula K d α f g Lv ∧
      TVLaggedDiffusivity.HasApproximateHessianFormula K α Lv H ∧
      TVLaggedDiffusivity.HasShiftedStepFormula g s H ∧
      TVLaggedDiffusivity.HasIterateUpdate f s := by
  -- Package the verified clause-level surface without guessing a stronger owner.
  refine ⟨h_init, ?_⟩
  refine ⟨h_diffusion, ?_⟩
  refine ⟨h_gradient, ?_⟩
  refine ⟨h_hessian, ?_⟩
  exact ⟨h_step, h_update⟩

/- Algorithm 8.2.3 (1). Source-facing check for the initialization clause
`f 0 = f0`.

This first `#check` records the initialization clause `f 0 = f0`, and the
following checks record the displayed diffusion, gradient, approximate-
Hessian, shifted-step, and iterate-update clauses. -/
#check TVLaggedDiffusivity.IsInitialized

/-
Algorithm 8.2.3 (2). Source-facing diffusion-assignment clause
`L_v := L (f_v)`.
-/
#check
  TVLaggedDiffusivity.HasDiffusionAssignment

/-
Algorithm 8.2.3 (3). Source-facing gradient clause
`g_v := Kᵀ (K f_v - d) + α • L_v f_v`.
-/
#check
  TVLaggedDiffusivity.HasGradientFormula

/-
Algorithm 8.2.3 (4). Source-facing approximate-Hessian clause
`H := Kᵀ K + α • L_v`.
-/
#check
  TVLaggedDiffusivity.HasApproximateHessianFormula

/-
Algorithm 8.2.3 (5). Source-facing shifted-step clause
`s_(v + 1) := -H⁻¹ g_v`.
-/
#check
  TVLaggedDiffusivity.HasShiftedStepFormula

/-
Algorithm 8.2.3 (6). Source-facing iterate-update clause
`f_(v + 1) := f_v + s_v`.
-/
#check
  TVLaggedDiffusivity.HasIterateUpdate
