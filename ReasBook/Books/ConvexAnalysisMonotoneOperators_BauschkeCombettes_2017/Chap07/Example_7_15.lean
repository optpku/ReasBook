/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 7.15: for a cone, the polar-set bound can be rescaled along positive
multiples to force the sharper polar-cone inequality. -/
lemma polarSet_subset_polarCone_of_isCone {K : Set 𝓗} (hK : IsCone K) :
    Kᵒ⊙ ⊆ Kᵒ⊖ := by
  have hKeq : K = (Ioi (0 : ℝ) : Set ℝ) • K := isCone_iff.mp hK
  intro u hu
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  rw [Set.mem_polarSet_iff_forall_inner_le_one] at hu
  intro x hx
  -- If `⟪x, u⟫` were positive, scaling `x` by `2 / ⟪x, u⟫` would violate the polar-set bound.
  by_contra hx_nonpos
  have hx_pos : 0 < ⟪x, u⟫_ℝ := lt_of_not_ge hx_nonpos
  let t : ℝ := 2 / ⟪x, u⟫_ℝ
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have htx_image : t • x ∈ (Ioi (0 : ℝ) : Set ℝ) • K := by
    -- The cone representation supplies the required positive multiple of `x`.
    exact Set.mem_smul.mpr ⟨t, ht, x, hx, rfl⟩
  have htx : t • x ∈ K := by
    -- Reinterpret the scaled point using the cone equality.
    exact hKeq.symm ▸ htx_image
  have hbound : ⟪t • x, u⟫_ℝ ≤ 1 := hu (t • x) htx
  have htwo_le_one : (2 : ℝ) ≤ 1 := by
    -- The chosen normalization rewrites the inner product bound as `2 ≤ 1`.
    simp [t, real_inner_smul_left, hx_pos.ne'] at hbound
  linarith

-- Proof sketch: this is exactly the cone case already identified in Exercise 7.10.
/-- Example 7.15 (1): if `K` is a cone in a real Hilbert space, then its polar set agrees with its
polar cone. -/
theorem polarSet_eq_polarCone_of_isCone {K : Set 𝓗} (hK : IsCone K) :
    Kᵒ⊙ = Kᵒ⊖ := by
  apply Subset.antisymm
  · exact polarSet_subset_polarCone_of_isCone hK
  · intro u hu
    rw [Set.mem_polarSet_iff_forall_inner_le_one]
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    intro x hx
    -- The polar-cone estimate is stronger than the polar-set bound.
    linarith [hu x hx]

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 7.15: the underlying set of a submodule is a cone in the textbook positive
scaling sense. -/
lemma submodule_isCone (K : Submodule ℝ 𝓗) : IsCone (K : Set 𝓗) := by
  -- Rewrite the cone predicate to closure under positive scalar multiples.
  rw [isCone_iff]
  refine Subset.antisymm ?_ ?_
  · intro x hx
    -- The unit scalar exhibits every submodule point as a positive multiple of itself.
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · intro x hx
    -- A positive multiple of a submodule element stays in the submodule.
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    exact K.smul_mem a hy

-- Proof sketch: combine part (1), which identifies `Kᵒ⊙` with `Kᵒ⊖` for cones, with
-- Proposition 6.23, which identifies the negative polar cone of a submodule with its orthogonal
-- complement.
/-- Example 7.15 (2): if `K` is a linear subspace, then its polar set, its polar cone, and its
orthogonal complement coincide. -/
theorem polarSet_and_polarCone_eq_orthogonal_of_submodule (K : Submodule ℝ 𝓗) :
    (K : Set 𝓗)ᵒ⊙ = (K : Set 𝓗)ᵒ⊖ ∧ (K : Set 𝓗)ᵒ⊖ = (Kᗮ : Set 𝓗) := by
  -- Route correction: prove the first equality by the cone case, then rewrite polar-cone
  -- membership directly as the nonpositive inner-product condition from Proposition 6.23.
  have hpolarSet : (K : Set 𝓗)ᵒ⊙ = (K : Set 𝓗)ᵒ⊖ := by
    -- The cone part follows directly from part (1) and the submodule cone helper.
    exact polarSet_eq_polarCone_of_isCone (submodule_isCone K)
  have horthogonal : (K : Set 𝓗)ᵒ⊖ = (Kᗮ : Set 𝓗) := by
    ext u
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    simpa using (Set.forall_inner_nonpos_iff_mem_orthogonal K (u := u))
  exact ⟨hpolarSet, horthogonal⟩

end

end Set
