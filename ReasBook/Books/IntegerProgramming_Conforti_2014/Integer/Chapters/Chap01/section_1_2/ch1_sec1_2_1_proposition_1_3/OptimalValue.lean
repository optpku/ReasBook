/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Order.Bounds.Defs

public section

universe u

/-- The lifted optimal value of a real objective `f` on a feasible set `S`, recorded in `EReal`
so that empty feasible regions have value `⊥ = -∞` and unbounded-above regions have value
`⊤ = +∞`. -/
@[expose] noncomputable def optimalValue {α : Type u} (f : α → ℝ) (S : Set α) : EReal :=
  sSup ((fun x ↦ ((f x : ℝ) : EReal)) '' S)

/-- `optimalValue f S` unfolds to the supremum of the lifted objective values attained on `S`. -/
theorem optimalValue_eq_sSup
    {α : Type u} (f : α → ℝ) (S : Set α) :
    optimalValue f S = sSup ((fun x ↦ ((f x : ℝ) : EReal)) '' S) :=
  rfl

/-- Every point of `S` contributes a candidate value bounded above by `optimalValue f S`. -/
theorem le_optimalValue_of_mem
    {α : Type u} (f : α → ℝ) {S : Set α} {x : α}
    (hx : x ∈ S) :
    ((f x : ℝ) : EReal) ≤ optimalValue f S := by
  rw [optimalValue_eq_sSup]
  exact le_sSup ⟨x, hx, rfl⟩

/-- The lifted optimal value on `S₁ ∪ S₂` is the maximum of the lifted optimal values on `S₁`
and `S₂`. -/
theorem optimalValue_union_eq_max
    {α : Type u} (f : α → ℝ) (S₁ S₂ : Set α) :
    optimalValue f (S₁ ∪ S₂) = max (optimalValue f S₁) (optimalValue f S₂) := by
  rw [optimalValue_eq_sSup, optimalValue_eq_sSup, optimalValue_eq_sSup, Set.image_union, sSup_union]
