/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.Profile
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr

public section

open scoped Matrix

universe u v

namespace TVSteepestDescent

/-- Algorithm 8.2.1. The steepest-descent run starts from the initial guess
`f0`. -/
abbrev IsInitialized {n : Type u} (f0 : n → ℝ) (f : ℕ → n → ℝ) : Prop :=
  f 0 = f0

/-- Characterization of the initialization clause. -/
theorem isInitialized_iff {n : Type u} {f0 : n → ℝ} {f : ℕ → n → ℝ} :
    IsInitialized f0 f ↔ f 0 = f0 := Iff.rfl

/-- Extracts the initialization equality from `TVSteepestDescent.IsInitialized`.
-/
theorem IsInitialized.init_eq {n : Type u} {f0 : n → ℝ} {f : ℕ → n → ℝ}
    (h : IsInitialized f0 f) :
    f 0 = f0 := h

/-- The displayed discrete gradient vector
`Kᵀ (K f - d) + α • L(f) f` at a current iterate `f`. -/
@[expose] def gradientAt {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℝ) (d : m → ℝ) (L : (n → ℝ) → Matrix n n ℝ) (α : ℝ)
    (f : n → ℝ) : n → ℝ :=
  Matrix.mulVec Kᵀ (Matrix.mulVec K f - d) +
    α • Matrix.mulVec (L f) f

/-- Evaluating `gradientAt` reproduces the displayed Chapter 8 gradient
expression. -/
theorem gradientAt_eq {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℝ) (d : m → ℝ) (L : (n → ℝ) → Matrix n n ℝ) (α : ℝ)
    (f : n → ℝ) :
    gradientAt K d L α f =
      Matrix.mulVec Kᵀ (Matrix.mulVec K f - d) +
        α • Matrix.mulVec (L f) f := rfl

/-- The displayed gradient assignment
`g_v := Kᵀ (K f_v - d) + α • L(f_v) f_v`. -/
abbrev HasGradientFormula {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : Matrix m n ℝ) (d : m → ℝ) (L : (n → ℝ) → Matrix n n ℝ) (α : ℝ)
    (f g : ℕ → n → ℝ) : Prop :=
  ∀ v : ℕ, g v = gradientAt K d L α (f v)

/-- Characterization of the displayed gradient assignment. -/
theorem hasGradientFormula_iff {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : Matrix m n ℝ} {d : m → ℝ} {L : (n → ℝ) → Matrix n n ℝ} {α : ℝ}
    {f g : ℕ → n → ℝ} :
    HasGradientFormula K d L α f g ↔
      ∀ v : ℕ, g v = gradientAt K d L α (f v) := Iff.rfl

/-- Extracts the displayed gradient equality from
`TVSteepestDescent.HasGradientFormula`. -/
theorem HasGradientFormula.eq {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : Matrix m n ℝ} {d : m → ℝ} {L : (n → ℝ) → Matrix n n ℝ} {α : ℝ}
    {f g : ℕ → n → ℝ}
    (h : HasGradientFormula K d L α f g) (v : ℕ) :
    g v = gradientAt K d L α (f v) := h v

/-- Expanded form of the displayed gradient equality at iterate `v`. -/
theorem HasGradientFormula.eq_expanded {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : Matrix m n ℝ} {d : m → ℝ} {L : (n → ℝ) → Matrix n n ℝ} {α : ℝ}
    {f g : ℕ → n → ℝ}
    (h : HasGradientFormula K d L α f g) (v : ℕ) :
    g v =
      Matrix.mulVec Kᵀ (Matrix.mulVec K (f v) - d) +
        α • Matrix.mulVec (L (f v)) (f v) := by
  simpa [gradientAt] using h v

/-- The exact line-search clause
`τ_v := arg min_(τ > 0) T(f_v - τ g_v)`. -/
abbrev HasExactLineSearch {n : Type u}
    (T : (n → ℝ) → ℝ) (f g : ℕ → n → ℝ) (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ,
    IsMinOn (LineSearch.profile T (f v) (-g v)) (Set.Ioi (0 : ℝ)) (τ v)

/-- Characterization of the exact line-search clause. -/
theorem hasExactLineSearch_iff {n : Type u}
    {T : (n → ℝ) → ℝ} {f g : ℕ → n → ℝ} {τ : ℕ → ℝ} :
    HasExactLineSearch T f g τ ↔
      ∀ v : ℕ,
        IsMinOn (LineSearch.profile T (f v) (-g v)) (Set.Ioi (0 : ℝ)) (τ v) := Iff.rfl

/-- Extracts the exact line-search condition at iterate `v` from
`TVSteepestDescent.HasExactLineSearch`. -/
theorem HasExactLineSearch.isMinOn {n : Type u}
    {T : (n → ℝ) → ℝ} {f g : ℕ → n → ℝ} {τ : ℕ → ℝ}
    (h : HasExactLineSearch T f g τ) (v : ℕ) :
    IsMinOn (LineSearch.profile T (f v) (-g v)) (Set.Ioi (0 : ℝ)) (τ v) := h v

/-- The iterate update `f_(v+1) = f_v - τ_v • g_v`. -/
abbrev HasIterateUpdate {n : Type u}
    (f g : ℕ → n → ℝ) (τ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ, f (v + 1) = f v - τ v • g v

/-- Characterization of the iterate-update clause. -/
theorem hasIterateUpdate_iff {n : Type u}
    {f g : ℕ → n → ℝ} {τ : ℕ → ℝ} :
    HasIterateUpdate f g τ ↔
      ∀ v : ℕ, f (v + 1) = f v - τ v • g v := Iff.rfl

/-- Extracts the iterate update equality from
`TVSteepestDescent.HasIterateUpdate`. -/
theorem HasIterateUpdate.iterate_eq {n : Type u}
    {f g : ℕ → n → ℝ} {τ : ℕ → ℝ}
    (h : HasIterateUpdate f g τ) (v : ℕ) :
    f (v + 1) = f v - τ v • g v := h v

/-- Helper for Algorithm 8.2.1: the first iterate is the initial guess minus
the first exact-line-search step in the displayed gradient direction. -/
theorem firstIterate_eq {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {f0 : n → ℝ} {K : Matrix m n ℝ} {d : m → ℝ}
    {L : (n → ℝ) → Matrix n n ℝ} {α : ℝ}
    {f g : ℕ → n → ℝ} {τ : ℕ → ℝ}
    (hinit : IsInitialized f0 f)
    (hgrad : HasGradientFormula K d L α f g)
    (hupdate : HasIterateUpdate f g τ) :
    f 1 = f0 - τ 0 • gradientAt K d L α f0 := by
  -- Start from the iterate-update clause at the initial index.
  rw [hupdate.iterate_eq 0]
  -- First expose the displayed gradient, then rewrite the initial iterate in both places.
  rw [hgrad.eq 0, hinit.init_eq]

end TVSteepestDescent
