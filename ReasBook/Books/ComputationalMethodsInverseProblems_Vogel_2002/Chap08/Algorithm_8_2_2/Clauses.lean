/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_1.Clauses
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

open scoped Matrix

universe u v

namespace TVNewton

/-- Algorithm 8.2.2 (1). The Newton run starts from `f0`.

This source-facing clause reuses the Chapter 8 initialization owner from
`TVSteepestDescent`. -/
abbrev IsInitialized {ι : Type u} (f0 : ι → ℝ) (f : ℕ → ι → ℝ) : Prop :=
  TVSteepestDescent.IsInitialized f0 f

/-- Extracts the initialization equality from `TVNewton.IsInitialized`. -/
theorem IsInitialized.init_eq {ι : Type u} {f0 : ι → ℝ} {f : ℕ → ι → ℝ}
    (h : IsInitialized f0 f) :
    f 0 = f0 :=
  TVSteepestDescent.IsInitialized.init_eq h

/-- The pair of displayed gradient and penalty-Hessian assignments at iterate
`v`. -/
structure GradientAndPenaltyHessianStep {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (d : κ → ℝ) (α : ℝ)
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (f g : ℕ → ι → ℝ) (HJ : ℕ → Matrix ι ι ℝ) (v : ℕ) : Prop where
  gradient_eq :
    g v = TVSteepestDescent.gradientAt K d L α (f v)
  penaltyHessian_eq : HJ v = L (f v) + L' (f v) (f v)

/-- Builds the iterate-`v` gradient and penalty-Hessian clause from its two
displayed equalities. -/
theorem GradientAndPenaltyHessianStep.ofEq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (d : κ → ℝ) (α : ℝ)
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (f g : ℕ → ι → ℝ) (HJ : ℕ → Matrix ι ι ℝ) (v : ℕ)
    (h_gradient : g v = TVSteepestDescent.gradientAt K d L α (f v))
    (h_penaltyHessian : HJ v = L (f v) + L' (f v) (f v)) :
    GradientAndPenaltyHessianStep K d α L L' f g HJ v :=
  { gradient_eq := h_gradient, penaltyHessian_eq := h_penaltyHessian }

/-- Algorithm 8.2.2 (2). The displayed gradient and penalty-Hessian assignments
`g_v := Kᵀ (K f_v - d) + α • L(f_v) f_v` and
`H_J := L(f_v) + L' (f_v) (f_v)`. -/
abbrev HasGradientAndPenaltyHessian {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (d : κ → ℝ) (α : ℝ)
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (f g : ℕ → ι → ℝ) (HJ : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, GradientAndPenaltyHessianStep K d α L L' f g HJ v

/-- The displayed penalty-Hessian assignment `H_J := L(f_v) + L' (f_v) (f_v)`.
-/
abbrev HasPenaltyHessianFormula {ι : Type u}
    (L : (ι → ℝ) → Matrix ι ι ℝ)
    (L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ)
    (f : ℕ → ι → ℝ) (HJ : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, HJ v = L (f v) + L' (f v) (f v)

/-- Extracts the displayed penalty-Hessian equality from
`TVNewton.HasPenaltyHessianFormula`. -/
theorem HasPenaltyHessianFormula.eq {ι : Type u}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasPenaltyHessianFormula L L' f HJ) (v : ℕ) :
    HJ v = L (f v) + L' (f v) (f v) :=
  h v

/-- Helper for Algorithm 8.2.2: combines the reusable gradient and
penalty-Hessian clause owners into the paired Newton clause. -/
theorem HasGradientAndPenaltyHessian.ofClauses {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h_gradient : TVSteepestDescent.HasGradientFormula K d L α f g)
    (h_penaltyHessian : HasPenaltyHessianFormula L L' f HJ) :
    HasGradientAndPenaltyHessian K d α L L' f g HJ := by
  intro v
  -- The iterate-wise Newton clause is exactly the pair of displayed formulas.
  refine GradientAndPenaltyHessianStep.ofEq K d α L L' f g HJ v ?_ ?_
  · -- Reuse the steepest-descent gradient owner for the gradient component.
    exact TVSteepestDescent.HasGradientFormula.eq h_gradient v
  · -- Reuse the standalone penalty-Hessian owner for the Hessian component.
    exact HasPenaltyHessianFormula.eq h_penaltyHessian v

/-- Helper for Algorithm 8.2.2: the paired Newton clause is equivalent to the
separate gradient and penalty-Hessian clause owners. -/
theorem hasGradientAndPenaltyHessian_iff {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ} :
    HasGradientAndPenaltyHessian K d α L L' f g HJ ↔
      TVSteepestDescent.HasGradientFormula K d L α f g ∧
        HasPenaltyHessianFormula L L' f HJ := by
  constructor
  · -- Split the paired clause into the two reusable clause owners.
    intro h
    exact ⟨
      (fun v ↦ (h v).gradient_eq),
      (fun v ↦ (h v).penaltyHessian_eq)
    ⟩
  · -- Reassemble the paired clause from the already separated owners.
    rintro ⟨h_gradient, h_penaltyHessian⟩
    exact HasGradientAndPenaltyHessian.ofClauses h_gradient h_penaltyHessian

/-- Extracts the displayed gradient equality from
`TVNewton.HasGradientAndPenaltyHessian`. -/
theorem HasGradientAndPenaltyHessian.gradientAt_eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasGradientAndPenaltyHessian K d α L L' f g HJ) (v : ℕ) :
    g v = TVSteepestDescent.gradientAt K d L α (f v) :=
  (h v).gradient_eq

/-- The gradient clause of `TVNewton.HasGradientAndPenaltyHessian` reuses the
Chapter 8 steepest-descent gradient owner. -/
theorem HasGradientAndPenaltyHessian.hasGradientFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasGradientAndPenaltyHessian K d α L L' f g HJ) :
    TVSteepestDescent.HasGradientFormula K d L α f g :=
  fun v ↦ HasGradientAndPenaltyHessian.gradientAt_eq h v

/-- Extracts the displayed gradient equality from
`TVNewton.HasGradientAndPenaltyHessian`. -/
theorem HasGradientAndPenaltyHessian.gradient_eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasGradientAndPenaltyHessian K d α L L' f g HJ) (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) - d) +
        α • Matrix.mulVec (L (f v)) (f v) :=
  TVSteepestDescent.HasGradientFormula.eq_expanded
    (HasGradientAndPenaltyHessian.hasGradientFormula h) v

/-- Extracts the displayed penalty-Hessian equality from
`TVNewton.HasGradientAndPenaltyHessian`. -/
theorem HasGradientAndPenaltyHessian.penaltyHessian_eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasGradientAndPenaltyHessian K d α L L' f g HJ) (v : ℕ) :
    HJ v = L (f v) + L' (f v) (f v) :=
  (h v).penaltyHessian_eq

/-- The penalty-Hessian clause of `TVNewton.HasGradientAndPenaltyHessian`
reuses `TVNewton.HasPenaltyHessianFormula`. -/
theorem HasGradientAndPenaltyHessian.hasPenaltyHessianFormula
    {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {d : κ → ℝ} {α : ℝ}
    {L : (ι → ℝ) → Matrix ι ι ℝ}
    {L' : (ι → ℝ) → (ι → ℝ) → Matrix ι ι ℝ}
    {f g : ℕ → ι → ℝ} {HJ : ℕ → Matrix ι ι ℝ}
    (h : HasGradientAndPenaltyHessian K d α L L' f g HJ) :
    HasPenaltyHessianFormula L L' f HJ :=
  fun v ↦ HasGradientAndPenaltyHessian.penaltyHessian_eq h v

/-- The pair of displayed total-Hessian and Newton-step assignments at iterate
`v`. -/
structure HessianAndNewtonStepStep {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (α : ℝ) (g s : ℕ → ι → ℝ)
    (HJ H : ℕ → Matrix ι ι ℝ) (v : ℕ) : Prop where
  hessian_eq : H v = Kᵀ * K + α • HJ v
  newtonStep_eq : s v = -Matrix.mulVec ((H v)⁻¹) (g v)

/-- Builds the iterate-`v` total-Hessian and Newton-step clause from its two
displayed equalities. -/
theorem HessianAndNewtonStepStep.ofEq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (α : ℝ) (g s : ℕ → ι → ℝ)
    (HJ H : ℕ → Matrix ι ι ℝ) (v : ℕ)
    (h_hessian : H v = Kᵀ * K + α • HJ v)
    (h_newtonStep : s v = -Matrix.mulVec ((H v)⁻¹) (g v)) :
    HessianAndNewtonStepStep K α g s HJ H v :=
  { hessian_eq := h_hessian, newtonStep_eq := h_newtonStep }

/-- Algorithm 8.2.2 (3). The displayed total-Hessian and Newton-step
assignments `H := Kᵀ K + α • H_J` and `s_v := -H⁻¹ g_v`. -/
abbrev HasHessianAndNewtonStep {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (α : ℝ) (g s : ℕ → ι → ℝ)
    (HJ H : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, HessianAndNewtonStepStep K α g s HJ H v

/-- The displayed exact Hessian assignment `H := Kᵀ K + α • H_J`. -/
abbrev HasHessianFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (K : Matrix κ ι ℝ) (α : ℝ)
    (HJ H : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, H v = Kᵀ * K + α • HJ v

/-- Extracts the displayed exact-Hessian equality from
`TVNewton.HasHessianFormula`. -/
theorem HasHessianFormula.eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h : HasHessianFormula K α HJ H) (v : ℕ) :
    H v = Kᵀ * K + α • HJ v :=
  h v

/-- The displayed Newton-step assignment `s_v := -H⁻¹ g_v`. -/
abbrev HasNewtonStepFormula {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (g s : ℕ → ι → ℝ) (H : ℕ → Matrix ι ι ℝ) : Prop :=
  ∀ v : ℕ, s v = -Matrix.mulVec ((H v)⁻¹) (g v)

/-- Extracts the displayed Newton-step equality from
`TVNewton.HasNewtonStepFormula`. -/
theorem HasNewtonStepFormula.eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    {g s : ℕ → ι → ℝ} {H : ℕ → Matrix ι ι ℝ}
    (h : HasNewtonStepFormula g s H) (v : ℕ) :
    s v = -Matrix.mulVec ((H v)⁻¹) (g v) :=
  h v

/-- Extracts the displayed total-Hessian equality from
`TVNewton.HasHessianAndNewtonStep`. -/
theorem HasHessianAndNewtonStep.hessian_eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h : HasHessianAndNewtonStep K α g s HJ H) (v : ℕ) :
    H v = Kᵀ * K + α • HJ v :=
  (h v).hessian_eq

/-- The exact-Hessian clause of `TVNewton.HasHessianAndNewtonStep` reuses
`TVNewton.HasHessianFormula`. -/
theorem HasHessianAndNewtonStep.hasHessianFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h : HasHessianAndNewtonStep K α g s HJ H) :
    HasHessianFormula K α HJ H :=
  fun v ↦ HasHessianAndNewtonStep.hessian_eq h v

/-- Extracts the displayed Newton-step equality from
`TVNewton.HasHessianAndNewtonStep`. -/
theorem HasHessianAndNewtonStep.newtonStep_eq {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h : HasHessianAndNewtonStep K α g s HJ H) (v : ℕ) :
    s v = -Matrix.mulVec ((H v)⁻¹) (g v) :=
  (h v).newtonStep_eq

/-- The Newton-step clause of `TVNewton.HasHessianAndNewtonStep` reuses
`TVNewton.HasNewtonStepFormula`. -/
theorem HasHessianAndNewtonStep.hasNewtonStepFormula {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h : HasHessianAndNewtonStep K α g s HJ H) :
    HasNewtonStepFormula g s H :=
  fun v ↦ HasHessianAndNewtonStep.newtonStep_eq h v

/-- Helper for Algorithm 8.2.2: combines the reusable total-Hessian and
Newton-step clause owners into the paired Newton clause. -/
theorem HasHessianAndNewtonStep.ofClauses {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ}
    (h_hessian : HasHessianFormula K α HJ H)
    (h_newtonStep : HasNewtonStepFormula g s H) :
    HasHessianAndNewtonStep K α g s HJ H := by
  intro v
  -- The iterate-wise Newton clause packages the Hessian and step formulas together.
  refine HessianAndNewtonStepStep.ofEq K α g s HJ H v ?_ ?_
  · -- The first component is the displayed total-Hessian identity.
    exact HasHessianFormula.eq h_hessian v
  · -- The second component is the displayed Newton-step identity.
    exact HasNewtonStepFormula.eq h_newtonStep v

/-- Helper for Algorithm 8.2.2: the paired Newton-step clause is equivalent to
the separate total-Hessian and Newton-step clause owners. -/
theorem hasHessianAndNewtonStep_iff {κ : Type u} {ι : Type v}
    [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {K : Matrix κ ι ℝ} {α : ℝ} {g s : ℕ → ι → ℝ}
    {HJ H : ℕ → Matrix ι ι ℝ} :
    HasHessianAndNewtonStep K α g s HJ H ↔
      HasHessianFormula K α HJ H ∧ HasNewtonStepFormula g s H := by
  constructor
  · -- Split the packaged iterate clause into its two reusable projections.
    intro h
    exact ⟨
      HasHessianAndNewtonStep.hasHessianFormula h,
      HasHessianAndNewtonStep.hasNewtonStepFormula h
    ⟩
  · -- Repackage the separate formulas into the paired iterate clause.
    rintro ⟨h_hessian, h_newtonStep⟩
    exact HasHessianAndNewtonStep.ofClauses h_hessian h_newtonStep

/-- The exact line-search and iterate-update clauses at iterate `v`. -/
structure LineSearchAndIterateUpdateStep {ι : Type u}
    (T : (ι → ℝ) → ℝ) (f s : ℕ → ι → ℝ) (τ : ℕ → ℝ) (v : ℕ) : Prop where
  lineSearch :
    IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v)
  iterate_eq : f (v + 1) = f v + τ v • s v

/-- Builds the iterate-`v` exact line-search and update clause from its two
displayed conditions. -/
theorem LineSearchAndIterateUpdateStep.ofClauses {ι : Type u}
    (T : (ι → ℝ) → ℝ) (f s : ℕ → ι → ℝ) (τ : ℕ → ℝ) (v : ℕ)
    (h_lineSearch :
      IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v))
    (h_iterate : f (v + 1) = f v + τ v • s v) :
    LineSearchAndIterateUpdateStep T f s τ v :=
  { lineSearch := h_lineSearch, iterate_eq := h_iterate }

/-- Algorithm 8.2.2 (4). The exact line-search and iterate-update clauses
`τ_v := arg min_(τ > 0) T (f_v + τ s_v)` and
`f_(v + 1) = f_v + τ_v • s_v`. -/
abbrev HasLineSearchAndIterateUpdate {ι : Type u}
    (T : (ι → ℝ) → ℝ) (f s : ℕ → ι → ℝ) (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, LineSearchAndIterateUpdateStep T f s τ v

/-- Extracts the exact line-search clause from
`TVNewton.HasLineSearchAndIterateUpdate`. -/
theorem HasLineSearchAndIterateUpdate.lineSearch {ι : Type u}
    {T : (ι → ℝ) → ℝ} {f s : ℕ → ι → ℝ} {τ : ℕ → ℝ}
    (h : HasLineSearchAndIterateUpdate T f s τ) (v : ℕ) :
    IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v) :=
  (h v).lineSearch

/-- Extracts the iterate-update clause from
`TVNewton.HasLineSearchAndIterateUpdate`. -/
theorem HasLineSearchAndIterateUpdate.iterate_eq {ι : Type u}
    {T : (ι → ℝ) → ℝ} {f s : ℕ → ι → ℝ} {τ : ℕ → ℝ}
    (h : HasLineSearchAndIterateUpdate T f s τ) (v : ℕ) :
    f (v + 1) = f v + τ v • s v :=
  (h v).iterate_eq

/-- Helper for Algorithm 8.2.2: combines the reusable exact line-search and
iterate-update clause owners into the paired closing clause. -/
theorem HasLineSearchAndIterateUpdate.ofClauses {ι : Type u}
    {T : (ι → ℝ) → ℝ} {f s : ℕ → ι → ℝ} {τ : ℕ → ℝ}
    (h_lineSearch :
      ∀ v : ℕ,
        IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v))
    (h_iterate : ∀ v : ℕ, f (v + 1) = f v + τ v • s v) :
    HasLineSearchAndIterateUpdate T f s τ := by
  intro v
  -- The closing Newton clause is obtained by pairing the two displayed conditions.
  exact LineSearchAndIterateUpdateStep.ofClauses T f s τ v
    (h_lineSearch v) (h_iterate v)

/-- Helper for Algorithm 8.2.2: the closing Newton clause is equivalent to the
separate exact line-search and iterate-update owners. -/
theorem hasLineSearchAndIterateUpdate_iff {ι : Type u}
    {T : (ι → ℝ) → ℝ} {f s : ℕ → ι → ℝ} {τ : ℕ → ℝ} :
    HasLineSearchAndIterateUpdate T f s τ ↔
      (∀ v : ℕ,
        IsMinOn (LineSearch.profile T (f v) (s v)) (Set.Ioi (0 : ℝ)) (τ v)) ∧
      (∀ v : ℕ, f (v + 1) = f v + τ v • s v) := by
  constructor
  · -- Project the paired closing clause to the two raw displayed conditions.
    intro h
    exact ⟨
      HasLineSearchAndIterateUpdate.lineSearch h,
      HasLineSearchAndIterateUpdate.iterate_eq h
    ⟩
  · -- Recombine the two displayed conditions into the packaged closing clause.
    rintro ⟨h_lineSearch, h_iterate⟩
    exact HasLineSearchAndIterateUpdate.ofClauses h_lineSearch h_iterate

end TVNewton
