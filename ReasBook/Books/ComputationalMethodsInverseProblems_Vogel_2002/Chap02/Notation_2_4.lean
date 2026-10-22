/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_4.Functional
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

universe u v

namespace ContinuousLinearMap

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- Notation 2.4.3-extra-1 (1). The quadratic Tikhonov functional
`T_α(f; g) = ‖K f - g‖ ^ 2 / 2 + α * inner ℝ (L f) f`. The source later uses this
notation in the regime `0 < α`. -/
def tikhonovFunctional
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (g : H₂) (α : ℝ) : H₁ → ℝ :=
  K.generalizedTikhonovFunctional g
    (fun p : H₂ × H₂ ↦ ‖p.1 - p.2‖ ^ 2 / 2)
    (fun f ↦ inner ℝ (L f) f)
    α

scoped notation "T[" K ", " L "]_" α "(" f "; " g ")" =>
  ContinuousLinearMap.tikhonovFunctional K L g α f

/-- `ContinuousLinearMap.tikhonovFunctional` is the specialization of
`ContinuousLinearMap.generalizedTikhonovFunctional` with quadratic discrepancy
`(x, y) ↦ ‖x - y‖ ^ 2 / 2` and penalty `f ↦ inner ℝ (L f) f`. -/
theorem tikhonovFunctional_eq_generalizedTikhonovFunctional
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (g : H₂) (α : ℝ) :
    K.tikhonovFunctional L g α =
      K.generalizedTikhonovFunctional g
        (fun p : H₂ × H₂ ↦ ‖p.1 - p.2‖ ^ 2 / 2)
        (fun f ↦ inner ℝ (L f) f)
        α := by
  -- Unfold the specialized objective; it is defined by this generalized functional.
  rfl

/-- The defining formula for `ContinuousLinearMap.tikhonovFunctional`. -/
theorem tikhonovFunctional_def
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (g : H₂) (α : ℝ) (f : H₁) :
    T[K, L]_α(f; g) = ‖K f - g‖ ^ 2 / 2 + α * inner ℝ (L f) f := by
  -- Reduce the specialized notation to the defining formula of the generalized objective.
  simpa [tikhonovFunctional] using
    K.generalizedTikhonovFunctional_def g
      (fun p : H₂ × H₂ ↦ ‖p.1 - p.2‖ ^ 2 / 2)
      (fun f ↦ inner ℝ (L f) f)
      α f

/-- Notation 2.4.3-extra-1 (2). The source notation `R_α(g)` is represented by
the predicate that `f ∈ C` and `IsMinOn (K.tikhonovFunctional L g α) C f`. The
source later uses this notation in the regime `0 < α`. -/
def IsTikhonovMinimizer
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) (α : ℝ)
    (f : H₁) : Prop :=
  f ∈ C ∧ IsMinOn (K.tikhonovFunctional L g α) C f

/-- The source set `R_α(g)` of Tikhonov minimizers on `C`. -/
def tikhonovMinimizers
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) (α : ℝ) : Set H₁ :=
  {f | K.IsTikhonovMinimizer L C g α f}

scoped notation "R[" K ", " L ", " C "]_" α "(" g ")" =>
  ContinuousLinearMap.tikhonovMinimizers K L C g α

namespace IsTikhonovMinimizer

/-- Constructs a Tikhonov minimizer from admissibility and minimality on `C`. -/
theorem ofMemAndIsMinOn
    {K : H₁ →L[ℝ] H₂} {L : H₁ →L[ℝ] H₁} {C : Set H₁} {g : H₂} {α : ℝ}
    {f : H₁} (hf_mem : f ∈ C)
    (hf_isMinOn : IsMinOn (K.tikhonovFunctional L g α) C f) :
    K.IsTikhonovMinimizer L C g α f := by
  -- The minimizer predicate is exactly admissibility together with minimality.
  exact ⟨hf_mem, hf_isMinOn⟩

/-- A Tikhonov minimizer is admissible. -/
theorem mem
    {K : H₁ →L[ℝ] H₂} {L : H₁ →L[ℝ] H₁} {C : Set H₁} {g : H₂} {α : ℝ}
    {f : H₁} (hf : K.IsTikhonovMinimizer L C g α f) :
    f ∈ C := by
  -- Project the admissibility component from the conjunction.
  exact hf.1

/-- A Tikhonov minimizer minimizes the Tikhonov functional on the constraint set. -/
theorem isMinOn
    {K : H₁ →L[ℝ] H₂} {L : H₁ →L[ℝ] H₁} {C : Set H₁} {g : H₂} {α : ℝ}
    {f : H₁} (hf : K.IsTikhonovMinimizer L C g α f) :
    IsMinOn (K.tikhonovFunctional L g α) C f := by
  -- Project the minimality component from the conjunction.
  exact hf.2

end IsTikhonovMinimizer

/-- Membership in `R[K, L, C]_α(g)` is exactly the Tikhonov minimizer predicate. -/
@[simp] theorem mem_tikhonovMinimizers_iff
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) (α : ℝ) (f : H₁) :
    f ∈ R[K, L, C]_α(g) ↔ K.IsTikhonovMinimizer L C g α f :=
  Iff.rfl

/-- Membership in `R[K, L, C]_α(g)` means admissibility and minimality on `C`. -/
theorem mem_tikhonovMinimizers_iff_mem_and_isMinOn
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) (α : ℝ) (f : H₁) :
    f ∈ R[K, L, C]_α(g) ↔ f ∈ C ∧ IsMinOn (fun x ↦ T[K, L]_α(x; g)) C f :=
  Iff.rfl

/-- The defining characterization of `ContinuousLinearMap.IsTikhonovMinimizer`. -/
theorem isTikhonovMinimizer_iff
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) (α : ℝ)
    (f : H₁) :
    K.IsTikhonovMinimizer L C g α f ↔
      f ∈ C ∧ IsMinOn (K.tikhonovFunctional L g α) C f := by
  -- Expose the predicate alias; the statement is definitionally the same conjunction.
  rfl

end ContinuousLinearMap
