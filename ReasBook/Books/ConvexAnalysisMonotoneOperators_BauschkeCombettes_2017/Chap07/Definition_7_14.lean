/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Definition 7.14: the polar set `Cᵒ⊙` of `C` consists of the vectors `u` for which the
inner-product supremum of `C` at `u` is at most `1`, equivalently the lower level set at height
`1` of the support function of `C`. -/
def polarSet (C : Set 𝓗) : Set 𝓗 :=
  {u | sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1}

scoped postfix:100 "ᵒ⊙" => Set.polarSet

-- Proof sketch: unfold `Set.polarSet`.
/-- A vector belongs to the polar set of `C` exactly when the supremum of the inner products
`⟪x, u⟫` over `x ∈ C` is at most `1`. -/
theorem mem_polarSet_iff {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊙ ↔ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1 := by
  -- This is exactly the defining predicate of `Set.polarSet`.
  rfl

-- Proof sketch: use the defining property of `sSup`, noting that the upper bound `1` is
-- equivalent to the pointwise inequalities `⟪x, u⟫ ≤ 1` on `C`.
/-- The polar-set inequality is the pointwise bound `⟪x, u⟫ ≤ 1` for all `x ∈ C`. -/
theorem mem_polarSet_iff_forall_inner_le_one {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊙ ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1 := by
  -- Rewrite the polar-set condition as a supremum bound on the image set of inner products.
  rw [mem_polarSet_iff, sSup_le_iff]
  constructor
  · intro hu x hx
    -- The global supremum bound specializes to the image point coming from `x ∈ C`.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) :=
      hu _ (Set.mem_image_of_mem _ hx)
    exact_mod_cast hxu
  · intro hu a ha
    -- Conversely, it suffices to bound every point in the image set by `1`.
    rcases ha with ⟨x, hx, rfl⟩
    -- Each image point is controlled by the assumed pointwise bound on `C`.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) := by
      exact_mod_cast hu x hx
    simpa using hxu

-- Proof sketch: rewrite both sides using the pointwise characterization of polar-set membership.
/-- A vector lies in the polar set of `C` exactly when its inner product with every point of `C`
is at most `1`; equivalently, `Cᵒ⊙ = {u | ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1}`. -/
theorem polarSet_eq_setOf_forall_inner_le_one (C : Set 𝓗) :
    Cᵒ⊙ = {u : 𝓗 | ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1} := by
  ext u
  -- The set equality is exactly the pointwise membership characterization above.
  rw [mem_polarSet_iff_forall_inner_le_one]
  rfl

end

end Set
