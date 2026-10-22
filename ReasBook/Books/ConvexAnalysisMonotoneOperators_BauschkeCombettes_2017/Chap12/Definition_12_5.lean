/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section AffineMinorants

variable {H : Type u} [Inner ℝ H]

/-- Definition 12.5: `f` has a continuous affine minorant with slope `u` if it dominates a
function of the form `x ↦ ⟪x, u⟫ + η`. -/
def HasContinuousAffineMinorantWithSlope (f : H → EReal) (u : H) : Prop :=
  ∃ η : ℝ, ∀ x : H, (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ f x)

-- Proof sketch: expand `HasContinuousAffineMinorantWithSlope f u` using its defining real
-- constant `η`, then rearrange the inequality `⟪x,u⟫ + η ≤ f x` into
-- `η ≤ f x - ⟪x,u⟫`; the converse reverses the same algebra.
/-- The textbook bounded-below formulation says that `f` has a continuous affine minorant with
slope `u` exactly when the shifted function `x ↦ f x - ⟪x, u⟫` admits a real lower bound. -/
theorem hasContinuousAffineMinorantWithSlope_iff
    (f : H → EReal) (u : H) :
    HasContinuousAffineMinorantWithSlope f u ↔
      ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ f x - ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, fun x ↦ ?_⟩
    refine (EReal.le_sub_iff_add_le (.inl (by simp)) (.inl (by simp))).2 ?_
    simpa [EReal.coe_add, add_comm] using hη x
  · rintro ⟨η, hη⟩
    refine ⟨η, fun x ↦ ?_⟩
    have hx : (η : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x :=
      (EReal.le_sub_iff_add_le (.inl (by simp)) (.inl (by simp))).1 (hη x)
    simpa [EReal.coe_add, add_comm] using hx

end AffineMinorants

end ERealFunction
