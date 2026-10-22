/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

open scoped Matrix

universe u v

namespace TVLaggedDiffusivity

/-- Algorithm 8.2.3 (1). The lagged-diffusivity iteration starts from `f0`. -/
abbrev IsInitialized {ι : Type u} (f0 : ι → ℝ) (f : ℕ → ι → ℝ) : Prop :=
  f 0 = f0

/-- Extracts the initialization equality from `TVLaggedDiffusivity.IsInitialized`.
-/
theorem IsInitialized.init_eq {ι : Type u} {f0 : ι → ℝ} {f : ℕ → ι → ℝ}
    (h : IsInitialized f0 f) :
    f 0 = f0 :=
  h

/-- Algorithm 8.2.3 (2). The displayed diffusion assignment
`L_v := L (f_v)`. -/
abbrev HasDiffusionAssignment {ι : Type u}
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (f : ℕ → ι → ℝ) (Lv : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, Lv v = L (f v)

/-- Extracts the displayed diffusion equality from
`TVLaggedDiffusivity.HasDiffusionAssignment`. -/
theorem HasDiffusionAssignment.eq {ι : Type u}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {f : ℕ → ι → ℝ} {Lv : ℕ → Matrix ι ι ℝ}
    (h : HasDiffusionAssignment L f Lv) (v : ℕ) :
    Lv v = L (f v) :=
  h v

/-- Algorithm 8.2.3 (3). The displayed gradient assignment
`g_v := Kᵀ (K f_v - d) + α • L_v f_v`. -/
abbrev HasGradientFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (d : κ → ℝ) (α : ℝ)
    (f g : ℕ → ι → ℝ) (Lv : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ,
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) - d) +
        α • Matrix.mulVec (Lv v) (f v)

/-- Extracts the displayed gradient equality from
`TVLaggedDiffusivity.HasGradientFormula`. -/
theorem HasGradientFormula.eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {f g : ℕ → ι → ℝ} {Lv : ℕ → Matrix ι ι ℝ}
    (h : HasGradientFormula K d α f g Lv) (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) - d) +
        α • Matrix.mulVec (Lv v) (f v) :=
  h v

/-- Helper for Algorithm 8.2.3: combining the lagged diffusion assignment with
the gradient clause recovers the textbook gradient formula written directly in
terms of `L (f_v)`. -/
theorem HasGradientFormula.eq_expanded {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {f g : ℕ → ι → ℝ} {Lv : ℕ → Matrix ι ι ℝ}
    (h_gradient : HasGradientFormula K d α f g Lv)
    (h_diffusion : HasDiffusionAssignment L f Lv) (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) - d) +
        α • Matrix.mulVec (L (f v)) (f v) := by
  -- First read off the stored gradient identity at iterate `v`.
  rw [HasGradientFormula.eq h_gradient v]
  -- Then replace the lagged diffusion operator by the displayed assignment.
  rw [HasDiffusionAssignment.eq h_diffusion v]

/-- Algorithm 8.2.3 (4). The displayed approximate Hessian assignment
`H := Kᵀ K + α • L_v`. -/
abbrev HasApproximateHessianFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (α : ℝ)
    (Lv H : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, H v = Kᵀ * K + α • Lv v

/-- Extracts the displayed approximate-Hessian equality from
`TVLaggedDiffusivity.HasApproximateHessianFormula`. -/
theorem HasApproximateHessianFormula.eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ}
    {Lv H : ℕ → Matrix ι ι ℝ}
    (h : HasApproximateHessianFormula K α Lv H) (v : ℕ) :
    H v = Kᵀ * K + α • Lv v :=
  h v

/-- Helper for Algorithm 8.2.3: combining the lagged diffusion assignment with
the approximate-Hessian clause recovers the textbook Hessian formula written
directly in terms of `L (f_v)`. -/
theorem HasApproximateHessianFormula.eq_expanded {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {K : Matrix κ ι ℝ} {α : ℝ}
    {f : ℕ → ι → ℝ} {Lv H : ℕ → Matrix ι ι ℝ}
    (h_hessian : HasApproximateHessianFormula K α Lv H)
    (h_diffusion : HasDiffusionAssignment L f Lv) (v : ℕ) :
    H v = Kᵀ * K + α • L (f v) := by
  -- First expose the stored Hessian identity at iterate `v`.
  rw [HasApproximateHessianFormula.eq h_hessian v]
  -- Then rewrite the lagged diffusion operator into the source-facing form.
  rw [HasDiffusionAssignment.eq h_diffusion v]

/-- Algorithm 8.2.3 (5). The displayed shifted-step assignment
`s_(v + 1) := -H⁻¹ g_v`. -/
abbrev HasShiftedStepFormula {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (g s : ℕ → ι → ℝ) (H : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ,
    s (v + 1) = -Matrix.mulVec ((H v)⁻¹) (g v)

/-- Extracts the displayed shifted-step equality from
`TVLaggedDiffusivity.HasShiftedStepFormula`. -/
theorem HasShiftedStepFormula.eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    {g s : ℕ → ι → ℝ} {H : ℕ → Matrix ι ι ℝ}
    (h : HasShiftedStepFormula g s H) (v : ℕ) :
    s (v + 1) = -Matrix.mulVec ((H v)⁻¹) (g v) :=
  h v

/-- Helper for Algorithm 8.2.3: substituting the approximate Hessian into the
shifted-step clause yields the quasi-Newton step written only in terms of the
displayed Hessian formula. -/
theorem HasShiftedStepFormula.eq_expanded {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ}
    {g s : ℕ → ι → ℝ} {Lv H : ℕ → Matrix ι ι ℝ}
    (h_step : HasShiftedStepFormula g s H)
    (h_hessian : HasApproximateHessianFormula K α Lv H) (v : ℕ) :
    s (v + 1) = -Matrix.mulVec ((Kᵀ * K + α • Lv v)⁻¹) (g v) := by
  -- Start from the stored shifted-step identity at iterate `v`.
  rw [HasShiftedStepFormula.eq h_step v]
  -- Then replace `H v` by the displayed approximate Hessian.
  rw [HasApproximateHessianFormula.eq h_hessian v]

/-- Algorithm 8.2.3 (6). The displayed iterate update
`f_(v + 1) := f_v + s_v`. -/
abbrev HasIterateUpdate {ι : Type u}
    (f s : ℕ → ι → ℝ) : Prop :=
  ∀ v : ℕ,
    f (v + 1) = f v + s v

/-- Extracts the iterate-update equality from
`TVLaggedDiffusivity.HasIterateUpdate`. -/
theorem HasIterateUpdate.iterate_eq {ι : Type u}
    {f s : ℕ → ι → ℝ}
    (h : HasIterateUpdate f s) (v : ℕ) :
    f (v + 1) = f v + s v :=
  h v

end TVLaggedDiffusivity
