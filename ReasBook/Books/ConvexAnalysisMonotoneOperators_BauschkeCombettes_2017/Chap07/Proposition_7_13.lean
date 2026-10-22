/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 7.13: enlarging the set can only increase the support value. -/
private lemma innerSupremumOn_mono {A B : Set 𝓗} (hAB : A ⊆ B) (u : 𝓗) :
    innerSupremumOn A u ≤ innerSupremumOn B u := by
  -- Compare the two support values through the inclusion of the corresponding images.
  rw [innerSupremumOn_eq_sSup_image, innerSupremumOn_eq_sSup_image]
  exact sSup_le_sSup <| by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hAB hx, rfl⟩

/-- Helper for Proposition 7.13: a pointwise upper bound on `⟪x, u⟫` over `S` bounds the support
value of `S` at `u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {S : Set 𝓗} {u : 𝓗} {b : EReal}
    (hbound : ∀ x ∈ S, (⟪x, u⟫_ℝ : EReal) ≤ b) :
    innerSupremumOn S u ≤ b := by
  -- Show that `b` is an upper bound for the image whose supremum defines `σ[S] u`.
  rw [innerSupremumOn_eq_sSup_image]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hbound x hx

/-- Helper for Proposition 7.13: every evaluation on the convex hull is bounded by the support
value on the original set. -/
private lemma inner_le_innerSupremumOn_of_mem_convexHull {C : Set 𝓗} {u x : 𝓗}
    (hx : x ∈ convexHull ℝ C) :
    (⟪x, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
  -- A linear functional attains its convex-hull maximum on the original set.
  have hconvex :
      ConvexOn ℝ (Set.univ : Set 𝓗) (innerSLFlip ℝ u).toLinearMap :=
    (innerSLFlip ℝ u).toLinearMap.convexOn convex_univ
  have hsubset_univ : C ⊆ (Set.univ : Set 𝓗) := by
    intro y hy
    simp
  obtain ⟨y, hyC, hxy⟩ := hconvex.exists_ge_of_mem_convexHull hsubset_univ hx
  have hxy' : (⟪x, u⟫_ℝ : EReal) ≤ (⟪y, u⟫_ℝ : EReal) := by
    simpa [innerSLFlip_apply_apply] using hxy
  have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
    -- The value at `y ∈ C` is one of the terms dominated by the support supremum.
    rw [innerSupremumOn_eq_sSup_image]
    exact (isLUB_sSup _).1 ⟨y, hyC, rfl⟩
  exact le_trans hxy' hy_le

/-- Helper for Proposition 7.13: taking the closure of a set does not change its support
function. -/
private lemma innerSupremumOn_closure_eq (S : Set 𝓗) :
    innerSupremumOn (closure S) = innerSupremumOn S := by
  ext u
  apply le_antisymm
  · refine innerSupremumOn_le_of_forall_inner_le ?_
    intro x hx
    -- The closed halfspace `{z | ⟪z,u⟫ ≤ σ[S] u}` contains `S`, so it also contains `closure S`.
    have hclosed :
        IsClosed {z : 𝓗 | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      simpa [Set.preimage, Set.setOf_mem_eq] using
        (isClosed_Iic.preimage
          (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)))
    have hsubset :
        S ⊆ {z : 𝓗 | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      intro z hz
      rw [innerSupremumOn_eq_sSup_image]
      have hz_mem :
          (⟪z, u⟫_ℝ : EReal) ∈ ((fun y : 𝓗 ↦ (⟪y, u⟫_ℝ : EReal)) '' S) :=
        ⟨z, hz, rfl⟩
      exact (isLUB_sSup _).1 hz_mem
    exact closure_minimal hsubset hclosed hx
  · -- The reverse inequality is the immediate monotonicity coming from `S ⊆ closure S`.
    exact innerSupremumOn_mono subset_closure u

-- Proof sketch: for the convex-hull equality, use the convex-combination description of
-- `convexHull ℝ C` to show that every value `⟪x, u⟫` with `x ∈ convexHull ℝ C` is bounded by
-- `σ[C] u`, while monotonicity gives the reverse inequality from `C ⊆ convexHull ℝ C`. For the
-- closure equality, use continuity of `x ↦ ⟪x, u⟫` to pass the same upper bound from
-- `convexHull ℝ C` to `closure (convexHull ℝ C)`, and again use monotonicity for the opposite
-- inequality.
/-- Proposition 7.13: the support function is unchanged when `C` is replaced by its convex hull or
its closed convex hull. -/
theorem supportFunction_eq_convexHull_and_closure_convexHull (C : Set 𝓗) :
    σ[C] = σ[convexHull ℝ C] ∧
      σ[convexHull ℝ C] = σ[closure (convexHull ℝ C)] := by
  constructor
  · ext u
    apply le_antisymm
    · -- The original set sits inside its convex hull, so the support value can only increase.
      exact innerSupremumOn_mono (subset_convexHull ℝ C) u
    · -- Route correction: close the hard direction through the maximum principle for linear
      -- functionals on `convexHull ℝ C`, instead of expanding a convex combination by hand.
      refine innerSupremumOn_le_of_forall_inner_le ?_
      intro x hx
      exact inner_le_innerSupremumOn_of_mem_convexHull hx
  · -- After the convexification step, closure invariance is a closed-halfspace argument.
    simpa using (innerSupremumOn_closure_eq (S := convexHull ℝ C)).symm
