/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Basic

-- Domain sampling for this file:
-- * primary domain: support functions of subsets of real normed spaces, formed from the
--   continuous-dual pairing;
-- * sampled core declarations: `EReal`, `sSup_empty`, and `le_sSup` give the canonical
--   complete-lattice API for taking suprema while retaining the empty-set value;
-- * sampled project precedent: `Chapter01/Definition_1_3_extra_3.lean` keeps a source-facing
--   owner as a thin bridge to canonical upstream structure rather than introducing a wrapper;
-- * triage for this file: `Set.supportFunction` is the source-facing owner, while its core data
--   is the `sSup` of the `EReal`-valued image of the dual pairing.

universe u

open Set

section Chapter14Definition141Extra3

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualSpace" => X →L[ℝ] ℝ

namespace Set

/-- Chapter14 Definition 14.1-extra-3: for a subset `Ω ⊆ X`, the support function is the
supremum of the continuous-dual pairing `ξ x` over `Ω`, viewed in `[-∞, ∞]`. This keeps the
textbook nonempty-set interpretation, while also giving the mathematically correct empty-set
value `⊥`. -/
noncomputable def supportFunction (Ω : Set X) : DualSpace → EReal :=
  fun ξ ↦ sSup ((fun x : X ↦ (ξ x : EReal)) '' Ω)

/-- Unfolding formula for `supportFunction`. -/
@[simp] theorem supportFunction_apply (Ω : Set X) (ξ : DualSpace) :
    Ω.supportFunction ξ = sSup ((fun x : X ↦ (ξ x : EReal)) '' Ω) := rfl

/-- The support function of the empty set is the empty supremum `⊥`. -/
@[simp] theorem supportFunction_empty (ξ : DualSpace) :
    (∅ : Set X).supportFunction ξ = ⊥ := by
  rw [supportFunction_apply, image_empty, sSup_empty]

/-- Every point of `Ω` contributes a value bounded above by the support function. -/
theorem le_supportFunction {Ω : Set X} (ξ : DualSpace) {x : X} (hx : x ∈ Ω) :
    (ξ x : EReal) ≤ Ω.supportFunction ξ :=
  le_sSup ⟨x, hx, rfl⟩

end Set

end Chapter14Definition141Extra3
