/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Exercise 7.10: for a cone, the polar-set inequality `⟪x, u⟫ ≤ 1` can be rescaled
along positive multiples to force the sharper polar-cone inequality `⟪x, u⟫ ≤ 0`. -/
lemma polarSet_subset_polarCone_of_isCone {C : Set 𝓗} (hC : IsCone C) :
    Cᵒ⊙ ⊆ Cᵒ⊖ := by
  have hCeq : C = (Ioi (0 : ℝ) : Set ℝ) • C := isCone_iff.mp hC
  intro u hu
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  rw [mem_polarSet_iff_forall_inner_le_one] at hu
  intro x hx
  -- Route correction: transport membership along the cone equality instead of rewriting inside
  -- the smul-set expression.
  -- If `⟪x, u⟫` were positive, scaling `x` by `2 / ⟪x, u⟫` would violate the polar-set bound.
  by_contra hx_nonpos
  have hx_pos : 0 < ⟪x, u⟫_ℝ := lt_of_not_ge hx_nonpos
  let t : ℝ := 2 / ⟪x, u⟫_ℝ
  have ht : 0 < t := by
    -- The chosen scale is positive because the denominator is positive.
    dsimp [t]
    positivity
  have htx_image : t • x ∈ (Ioi (0 : ℝ) : Set ℝ) • C := by
    -- The cone representation supplies the required positive multiple of `x`.
    exact Set.mem_smul.mpr ⟨t, ht, x, hx, rfl⟩
  have htx : t • x ∈ C := by
    -- Reinterpret the positive multiple back as an element of `C`.
    exact hCeq.symm ▸ htx_image
  have hbound : ⟪t • x, u⟫_ℝ ≤ 1 := hu (t • x) htx
  have htwo_le_one : (2 : ℝ) ≤ 1 := by
    -- After rewriting the scaled inner product, the chosen normalization collapses to `2 ≤ 1`.
    simp [t, real_inner_smul_left, hx_pos.ne'] at hbound
  linarith

-- Proof sketch: use the pointwise characterizations of `Cᵒ⊖` and `Cᵒ⊙`. If `u ∈ Cᵒ⊙`, then for
-- every `x ∈ C` and every positive scalar `t`, the cone property gives `t • x ∈ C`, so
-- `⟪t • x, u⟫ ≤ 1`; dividing by arbitrarily large `t` forces `⟪x, u⟫ ≤ 0`, hence `u ∈ Cᵒ⊖`. The
-- reverse inclusion is Proposition 7.16 (2).
/-- Exercise 7.10: if `C` is a cone, then its polar cone and its polar set coincide. -/
theorem polarCone_eq_polarSet_of_isCone {C : Set 𝓗} (hC : IsCone C) :
    Cᵒ⊖ = Cᵒ⊙ := by
  apply Subset.antisymm
  · intro u hu
    rw [mem_polarSet_iff_forall_inner_le_one]
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    intro x hx
    -- The polar-cone bound is already stronger than the polar-set bound.
    linarith [hu x hx]
  · -- The converse inclusion is exactly the rescaling argument isolated above.
    exact polarSet_subset_polarCone_of_isCone hC

end

/-- Helper for Exercise 7.10: in the one-dimensional real Hilbert space `ℝ`, the inner product
with `1` on the left returns the input. -/
lemma inner_one_left_real (u : ℝ) :
    ⟪(1 : ℝ), u⟫_ℝ = u := by
  -- Commute the real inner product, then expand `u` as the scalar multiple `u • 1`.
  calc
    ⟪(1 : ℝ), u⟫_ℝ = ⟪u, (1 : ℝ)⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪u • (1 : ℝ), (1 : ℝ)⟫_ℝ := by simp
    _ = u * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := by rw [real_inner_smul_left]
    _ = u := by norm_num [real_inner_self_eq_norm_sq]

/-- Helper for Exercise 7.10: the singleton `{1}` is not closed under positive rescaling, so it is
not a cone. -/
lemma singleton_one_not_isCone : ¬ IsCone ({1} : Set ℝ) := by
  intro hC
  have hCeq : ({1} : Set ℝ) = (Ioi (0 : ℝ) : Set ℝ) • ({1} : Set ℝ) := isCone_iff.mp hC
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have hone_mem : (1 : ℝ) ∈ ({1} : Set ℝ) := by
    simp
  have hsmul : (2 : ℝ) • (1 : ℝ) = (2 : ℝ) := by
    norm_num [smul_eq_mul]
  have htwo : (2 : ℝ) ∈ (Ioi (0 : ℝ) : Set ℝ) • ({1} : Set ℝ) := by
    -- The point `2` is the positive multiple `2 • 1`.
    exact Set.mem_smul.mpr ⟨2, htwo_pos, 1, hone_mem, hsmul⟩
  have htwo_singleton : (2 : ℝ) ∈ ({1} : Set ℝ) := by
    -- If `{1}` were a cone, the same point would have to lie back in the singleton.
    exact hCeq.symm ▸ htwo
  norm_num at htwo_singleton

/-- Helper for Exercise 7.10: membership in the polar cone of `{1}` is exactly the inequality
`u ≤ 0`. -/
lemma mem_polarCone_singleton_one_iff {u : ℝ} :
    u ∈ ({1} : Set ℝ)ᵒ⊖ ↔ u ≤ 0 := by
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  constructor
  · intro hu
    have hone_mem : (1 : ℝ) ∈ ({1} : Set ℝ) := by
      simp
    -- Testing the defining inequality at the unique point of the singleton gives the claim.
    simpa [inner_one_left_real] using hu 1 hone_mem
  · intro hu x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- Conversely, every point of the singleton is exactly `1`.
    simpa [inner_one_left_real] using hu

/-- Helper for Exercise 7.10: membership in the polar set of `{1}` is exactly the inequality
`u ≤ 1`. -/
lemma mem_polarSet_singleton_one_iff {u : ℝ} :
    u ∈ ({1} : Set ℝ)ᵒ⊙ ↔ u ≤ 1 := by
  rw [mem_polarSet_iff_forall_inner_le_one]
  constructor
  · intro hu
    have hone_mem : (1 : ℝ) ∈ ({1} : Set ℝ) := by
      simp
    -- Again, the singleton reduces the universal bound to the point `1`.
    simpa [inner_one_left_real] using hu 1 hone_mem
  · intro hu x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    -- Replacing `x` by `1` turns the pointwise bound into the desired singleton statement.
    simpa [inner_one_left_real] using hu

-- Proof sketch: take the singleton `{1}` in `ℝ`. It is not a cone, while its polar cone is
-- `Set.Iic 0` and its polar set is `Set.Iic 1`, so the two sets are different.
/-- A concrete one-dimensional counterexample showing that the equality `Cᵒ⊖ = Cᵒ⊙` can fail for
subsets that are not cones. -/
theorem exists_noncone_real_set_with_polarCone_ne_polarSet :
    ∃ C : Set ℝ, ¬ IsCone C ∧ Cᵒ⊖ ≠ Cᵒ⊙ := by
  refine ⟨({1} : Set ℝ), singleton_one_not_isCone, ?_⟩
  intro hEq
  have hone_mem_polarSet : (1 : ℝ) ∈ ({1} : Set ℝ)ᵒ⊙ := by
    -- The singleton polar-set description places `1` exactly on the boundary.
    exact (mem_polarSet_singleton_one_iff (u := (1 : ℝ))).2 le_rfl
  have hone_mem_polarCone : (1 : ℝ) ∈ ({1} : Set ℝ)ᵒ⊖ := by
    -- Equality of the two polars would force the same boundary point into the polar cone.
    exact hEq ▸ hone_mem_polarSet
  rw [mem_polarCone_singleton_one_iff] at hone_mem_polarCone
  norm_num at hone_mem_polarCone

end Set
