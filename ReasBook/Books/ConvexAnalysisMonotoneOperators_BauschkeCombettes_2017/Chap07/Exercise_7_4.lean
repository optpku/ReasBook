/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Local abbreviation for the polar-set construction used in this exercise file. -/
private abbrev polarSet (C : Set 𝓗) : Set 𝓗 :=
  setOf fun u : 𝓗 ↦ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1

local postfix:100 "ᵒ⊙" => polarSet

/-- Helper for Exercise 7.4: membership in the local polar set is equivalent to the pointwise
inner-product bound `⟪x, u⟫ ≤ 1` on `C`. -/
private lemma mem_polarSet_iff_forall_inner_le_one {C : Set 𝓗} {u : 𝓗} :
    u ∈ Cᵒ⊙ ↔ ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1 := by
  -- Unfold the local `polarSet` abbreviation to express membership as a supremum bound.
  change sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) ≤ 1 ↔
      ∀ x ∈ C, ⟪x, u⟫_ℝ ≤ 1
  rw [sSup_le_iff]
  constructor
  · intro hu x hx
    -- The supremum bound specializes to the image point corresponding to `x ∈ C`.
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) :=
      hu _ (Set.mem_image_of_mem _ hx)
    exact_mod_cast hxu
  · intro hu a ha
    -- Conversely, every point of the image set comes from some `x ∈ C`.
    rcases ha with ⟨x, hx, rfl⟩
    have hxu : (⟪x, u⟫_ℝ : EReal) ≤ (1 : EReal) := by
      exact_mod_cast hu x hx
    simpa using hxu

/-- Helper for Exercise 7.4: dilating the primal set by `γ` is equivalent to dilating the test
vector by `γ` inside the polar-set membership condition. -/
private lemma mem_polarSet_smul_set_iff (C : Set 𝓗) (γ : ℝ) {u : 𝓗} :
    u ∈ (γ • C)ᵒ⊙ ↔ γ • u ∈ Cᵒ⊙ := by
  -- Rewrite both sides into the textbook pointwise inequality form.
  rw [mem_polarSet_iff_forall_inner_le_one, mem_polarSet_iff_forall_inner_le_one]
  constructor
  · intro hu x hx
    -- Testing the left-hand condition at `γ • x` transfers the scalar to the second slot.
    have hsmul : γ • x ∈ γ • C := Set.smul_mem_smul_set hx
    simpa [real_inner_smul_left, real_inner_smul_right, mul_comm] using hu (γ • x) hsmul
  · intro hu y hy
    -- Every point of `γ • C` has the form `γ • x` with `x ∈ C`.
    rcases Set.mem_smul_set.mp hy with ⟨x, hx, rfl⟩
    simpa [real_inner_smul_left, real_inner_smul_right, mul_comm] using hu x hx

-- Proof sketch: prove both inclusions by rewriting membership with
-- the defining inequality of the local notation `Cᵒ⊙`; for `u ∈ (γ • C)ᵒ⊙`,
-- the condition `⟪γ • x, u⟫ ≤ 1` is equivalent to `⟪x, γ • u⟫ ≤ 1`, and
-- positivity of `γ` identifies `u ∈ γ⁻¹ • Cᵒ⊙`.
/-- Exercise 7.4: for a positive scalar `γ`, the polar set of the dilation `γ • C` is the dilation
of the polar set by the reciprocal scalar `γ⁻¹`. -/
theorem polarSet_smul_eq_inv_smul_polarSet
    (C : Set 𝓗) {γ : ℝ} (hγ : 0 < γ) :
    (γ • C)ᵒ⊙ = γ⁻¹ • Cᵒ⊙ := by
  ext u
  -- Route correction: finish at the membership level, then rewrite inverse-scalar membership.
  rw [Set.mem_inv_smul_set_iff₀ (ne_of_gt hγ)]
  -- The core equivalence is exactly the scalar-transfer helper above.
  exact mem_polarSet_smul_set_iff (C := C) (γ := γ)
