/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 6.27: a cone is stable under positive scalar multiplication. -/
private lemma isCone_smul_mem_of_pos {K : Set 𝓗} (hK_cone : IsCone K) {x : 𝓗} (hx : x ∈ K)
    {a : ℝ} (ha : 0 < a) :
    a • x ∈ K := by
  -- Rewrite the cone hypothesis as the positive-scalar image description and exhibit the witness.
  rw [isCone_iff] at hK_cone
  rw [hK_cone]
  exact Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩

/-- Helper for Proposition 6.27: if `a + ε b ≤ 0` for every positive `ε`, then already `a ≤ 0`. -/
private lemma le_zero_of_forall_pos_add_mul_le_zero (a b : ℝ)
    (h : ∀ ε > 0, a + ε * b ≤ 0) :
    a ≤ 0 := by
  by_contra ha_nonpos
  have ha : 0 < a := by
    linarith
  by_cases hb : 0 ≤ b
  · -- If `b` is nonnegative, testing at `ε = 1` already contradicts `a > 0`.
    have hab : a + 1 * b ≤ 0 := h 1 (by norm_num)
    linarith
  · -- If `b` is negative, choose a small positive `ε` so that `a + ε b` stays positive.
    have hb_lt : b < 0 := by
      linarith
    let ε : ℝ := a / (-2 * b)
    have hden : 0 < -2 * b := by
      nlinarith
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos ha hden
    have hε_le : a + ε * b ≤ 0 := h ε hε
    have hb_ne : b ≠ 0 := by
      linarith
    have hhalf : a + ε * b = a / 2 := by
      dsimp [ε]
      field_simp [hb_ne]
      ring
    linarith

/-- Helper for Proposition 6.27: the polar cone of a sum of nonempty cones is contained in the
intersection of the two polar cones. -/
private theorem polarCone_add_subset_inter {K₁ K₂ : Set 𝓗}
    (hK₁_cone : IsCone K₁) (hK₁_nonempty : K₁.Nonempty)
    (hK₂_cone : IsCone K₂) (hK₂_nonempty : K₂.Nonempty) :
    (K₁ + K₂)ᵒ⊖ ⊆ K₁ᵒ⊖ ∩ K₂ᵒ⊖ := by
  intro u hu
  rcases hK₁_nonempty with ⟨y₁, hy₁⟩
  rcases hK₂_nonempty with ⟨y₂, hy₂⟩
  rw [Set.mem_inter_iff, Set.mem_polarCone_iff_forall_inner_nonpos,
    Set.mem_polarCone_iff_forall_inner_nonpos]
  constructor
  · intro x₁ hx₁
    -- Test the defining inequality on `x₁ + ε • y₂` and then let `ε ↓ 0`.
    have htest : ∀ ε > 0, ⟪x₁, u⟫_ℝ + ε * ⟪y₂, u⟫_ℝ ≤ 0 := by
      intro ε hε
      have hy₂ε : ε • y₂ ∈ K₂ := isCone_smul_mem_of_pos hK₂_cone hy₂ hε
      have hsum : x₁ + ε • y₂ ∈ K₁ + K₂ := by
        exact Set.mem_add.2 ⟨x₁, hx₁, ε • y₂, hy₂ε, rfl⟩
      have hinner : ⟪x₁ + ε • y₂, u⟫_ℝ ≤ 0 :=
        (Set.mem_polarCone_iff_forall_inner_nonpos.1 hu) (x₁ + ε • y₂) hsum
      simpa [inner_add_left, real_inner_smul_left] using hinner
    exact le_zero_of_forall_pos_add_mul_le_zero _ _ htest
  · intro x₂ hx₂
    -- Repeat the same squeezing argument with a fixed point of `K₁`.
    have htest : ∀ ε > 0, ⟪x₂, u⟫_ℝ + ε * ⟪y₁, u⟫_ℝ ≤ 0 := by
      intro ε hε
      have hy₁ε : ε • y₁ ∈ K₁ := isCone_smul_mem_of_pos hK₁_cone hy₁ hε
      have hsum : ε • y₁ + x₂ ∈ K₁ + K₂ := by
        exact Set.mem_add.2 ⟨ε • y₁, hy₁ε, x₂, hx₂, rfl⟩
      have hinner : ⟪ε • y₁ + x₂, u⟫_ℝ ≤ 0 :=
        (Set.mem_polarCone_iff_forall_inner_nonpos.1 hu) (ε • y₁ + x₂) hsum
      simpa [inner_add_left, real_inner_smul_left, add_comm] using hinner
    exact le_zero_of_forall_pos_add_mul_le_zero _ _ htest

/-- Helper for Proposition 6.27: the intersection of two polar cones is contained in the polar
cone of the pointwise sum. -/
private theorem inter_subset_polarCone_add {K₁ K₂ : Set 𝓗} :
    K₁ᵒ⊖ ∩ K₂ᵒ⊖ ⊆ (K₁ + K₂)ᵒ⊖ := by
  intro u hu
  rw [Set.mem_inter_iff, Set.mem_polarCone_iff_forall_inner_nonpos,
    Set.mem_polarCone_iff_forall_inner_nonpos] at hu
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro z hz
  rcases Set.mem_add.1 hz with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  -- Expand the inner product across the sum and combine the two nonpositivity bounds.
  have hx₁_nonpos : ⟪x₁, u⟫_ℝ ≤ 0 := hu.1 x₁ hx₁
  have hx₂_nonpos : ⟪x₂, u⟫_ℝ ≤ 0 := hu.2 x₂ hx₂
  simpa [inner_add_left] using add_nonpos hx₁_nonpos hx₂_nonpos

-- Proof sketch: use `mem_polarCone_iff_forall_inner_nonpos`. For the forward inclusion, fix
-- `u ∈ (K₁ + K₂)ᵒ⊖`, choose witnesses from the nonempty cones, and use the cone identities
-- `Kᵢ = (0, ∞) • Kᵢ` to test the defining inequality on `x₁ + ε • x₂` and `ε • x₁ + x₂`, then let
-- `ε ↓ 0` to recover the separate inequalities. For the reverse inclusion, add the two
-- nonpositive inner-product inequalities.
/-- Proposition 6.27 (1): if `K₁` and `K₂` are nonempty cones in a real inner product space, then
the polar cone of their pointwise sum is the intersection of their polar cones. -/
theorem polarCone_add_eq_inter {K₁ K₂ : Set 𝓗}
    (hK₁_cone : IsCone K₁) (hK₁_nonempty : K₁.Nonempty)
    (hK₂_cone : IsCone K₂) (hK₂_nonempty : K₂.Nonempty) :
    (K₁ + K₂)ᵒ⊖ = K₁ᵒ⊖ ∩ K₂ᵒ⊖ := by
  -- Package the textbook argument as the two natural set inclusions proved above.
  refine Set.Subset.antisymm ?_ ?_
  · exact polarCone_add_subset_inter hK₁_cone hK₁_nonempty hK₂_cone hK₂_nonempty
  · exact inter_subset_polarCone_add

end

end Set

namespace Submodule

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: this is the textbook equality written in the canonical submodule lattice language.
-- Apply `Submodule.inf_orthogonal` and reverse the resulting equality.
/-- Proposition 6.27 (2): for linear subspaces of a real inner product space, the orthogonal
complement of the sum is the intersection of the orthogonal complements. -/
theorem orthogonal_sup_eq_inf (K₁ K₂ : Submodule ℝ 𝓗) :
    (K₁ ⊔ K₂)ᗮ = K₁ᗮ ⊓ K₂ᗮ := by
  -- This is exactly mathlib's orthogonal-complement formula with the equality reversed.
  exact (Submodule.inf_orthogonal K₁ K₂).symm

end

end Submodule
