/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Definition 6.22 (1): the polar cone `Cᵒ⊖` of `C` consists of the vectors `u` such that the
inner-product supremum of `C` at `u` is nonpositive. -/
def polarCone (C : Set 𝓗) : Set 𝓗 :=
  {u | sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 0}

scoped postfix:100 "ᵒ⊖" => Set.polarCone

-- Proof sketch: unfold `Set.polarCone`.
/-- Membership in the polar cone means that the supremum of the inner products `⟪x, u⟫` over
`x ∈ C` is nonpositive. -/
theorem mem_polarCone_iff {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊖ ↔ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 0 := by
  -- This is just the defining predicate of `Set.polarCone`.
  rfl

-- Proof sketch: combine `mem_polarCone_iff` with
-- the defining property of `sSup`, noting that the singleton upper bound `0` is equivalent to
-- pointwise nonpositivity of all inner products.
/-- A vector lies in the polar cone exactly when its inner products with all points of `C` are
nonpositive. -/
theorem mem_polarCone_iff_forall_inner_nonpos {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊖ ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0 := by
  rw [mem_polarCone_iff, sSup_le_iff]
  constructor
  · intro hu x hx
    -- The image-set bound specializes immediately to the point `x`.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (0 : EReal) :=
      hu _ (Set.mem_image_of_mem _ hx)
    exact_mod_cast hxu
  · intro hu a ha
    -- To bound the supremum by `0`, it suffices to bound every value in the image by `0`.
    rcases ha with ⟨x, hx, rfl⟩
    -- Each image point is controlled by the assumed pointwise nonpositivity.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (0 : EReal) := by
      exact_mod_cast hu x hx
    simpa using hxu

-- Proof sketch: rewrite membership in `ProperCone.innerDual (-C)` using `ProperCone.mem_innerDual`,
-- then translate membership in the negated set via `mem_polarCone_iff_forall_inner_nonpos`.
/-- Helper for Definition 6.22: membership in the inner dual of `-C` is the same as nonpositive
inner products against every element of `C`. -/
theorem mem_innerDual_neg_iff_forall_inner_nonpos [CompleteSpace 𝓗] {C : Set 𝓗} {u : 𝓗} :
    u ∈ (ProperCone.innerDual (-C) : Set 𝓗) ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hu x hx
    -- Evaluate the `innerDual` condition at the negated point coming from `C`.
    have hxneg : -(-x) ∈ C := by
      simpa using hx
    have hdual : 0 ≤ ⟪-x, u⟫_ℝ :=
      (ProperCone.mem_innerDual (s := -C) (y := u)).1 hu (Set.mem_neg.mpr hxneg)
    simpa [inner_neg_left] using hdual
  · intro hu
    -- Build `innerDual` membership by testing an arbitrary point of `-C`.
    exact (ProperCone.mem_innerDual (s := -C) (y := u)).2 <| by
      intro x hx
      have hxC : -x ∈ C := Set.mem_neg.mp hx
      have hneg : ⟪-x, u⟫_ℝ ≤ 0 := hu (-x) hxC
      simpa [inner_neg_left] using hneg

/-- In a real Hilbert space, the source-facing polar cone agrees with the negative-sign
reformulation of mathlib's inner dual cone. -/
theorem polarCone_eq_innerDual_neg [CompleteSpace 𝓗] (C : Set 𝓗) :
    Cᵒ⊖ = (ProperCone.innerDual (-C) : Set 𝓗) := by
  ext u
  -- Route correction: compare the two set memberships through the same pointwise inequality.
  rw [mem_polarCone_iff_forall_inner_nonpos, mem_innerDual_neg_iff_forall_inner_nonpos]

/-- Definition 6.22 (2): the dual cone `Cᵒ⊕` is the negative of the polar cone. -/
def dualCone (C : Set 𝓗) : Set 𝓗 :=
  -Cᵒ⊖

scoped postfix:100 "ᵒ⊕" => Set.dualCone

-- Proof sketch: unfold `Set.dualCone` and simplify pointwise negation membership.
/-- A vector lies in the dual cone exactly when its negation lies in the polar cone. -/
theorem mem_dualCone_iff {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊕ ↔ -u ∈ Cᵒ⊖ := by
  -- This is the pointwise-negation membership rule for the definition `Cᵒ⊕ = -Cᵒ⊖`.
  rw [dualCone]
  exact Set.mem_neg

-- Proof sketch: combine `dualCone = - polarCone`, `polarCone_eq_innerDual_neg`, and the sign change
-- from `-C` to `C` in the inner-dual description.
/-- Helper for Definition 6.22: negating the vector and the set cancels in the inner-dual
membership test. -/
theorem neg_mem_innerDual_neg_iff_mem_innerDual [CompleteSpace 𝓗] {C : Set 𝓗} {u : 𝓗} :
    -u ∈ (ProperCone.innerDual (-C) : Set 𝓗) ↔ u ∈ (ProperCone.innerDual C : Set 𝓗) := by
  constructor
  · intro hu
    -- Test the `-C` condition at `-x` to recover the positivity condition on `x`.
    exact (ProperCone.mem_innerDual (s := C) (y := u)).2 <| by
      intro x hx
      have hxneg : -(-x) ∈ C := by
        simpa using hx
      have hneg : 0 ≤ ⟪-x, -u⟫_ℝ :=
        (ProperCone.mem_innerDual (s := -C) (y := -u)).1 hu (Set.mem_neg.mpr hxneg)
      simpa [inner_neg_left, inner_neg_right] using hneg
  · intro hu
    -- Conversely, evaluate the `C` condition at `-x` to rebuild membership in `innerDual (-C)`.
    exact (ProperCone.mem_innerDual (s := -C) (y := -u)).2 <| by
      intro x hx
      have hxC : -x ∈ C := Set.mem_neg.mp hx
      have hpos : 0 ≤ ⟪-x, u⟫_ℝ :=
        (ProperCone.mem_innerDual (s := C) (y := u)).1 hu hxC
      simpa [inner_neg_left, inner_neg_right] using hpos

/-- In a real Hilbert space, the source-facing dual cone agrees with mathlib's inner dual cone. -/
theorem dualCone_eq_innerDual [CompleteSpace 𝓗] (C : Set 𝓗) :
    Cᵒ⊕ = (ProperCone.innerDual C : Set 𝓗) := by
  ext u
  constructor
  · intro hu
    -- Route correction: first rewrite dual-cone membership as a sign condition on the polar cone.
    rw [mem_dualCone_iff] at hu
    rw [polarCone_eq_innerDual_neg C] at hu
    simpa using neg_mem_innerDual_neg_iff_mem_innerDual.1 hu
  · intro hu
    -- Apply the same sign-cancellation lemma in reverse, then fold back to the source definition.
    rw [mem_dualCone_iff]
    rw [polarCone_eq_innerDual_neg C]
    simpa using neg_mem_innerDual_neg_iff_mem_innerDual.2 hu

/-- Definition 6.22 (3): a set is self-dual when it coincides with its dual cone. -/
def IsSelfDual (C : Set 𝓗) : Prop :=
  C = Cᵒ⊕

-- Proof sketch: unfold `Set.IsSelfDual`.
/-- The self-duality predicate is exactly the equality `C = Cᵒ⊕`. -/
theorem isSelfDual_iff {C : Set 𝓗} :
    C.IsSelfDual ↔ C = Cᵒ⊕ := by
  -- This theorem simply unfolds the definition introduced above.
  rfl

end

end Set
