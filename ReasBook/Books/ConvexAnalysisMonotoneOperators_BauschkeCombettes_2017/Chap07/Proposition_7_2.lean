/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_1

open Set
open scoped InnerProductSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: enlarging the set can only increase the support value. -/
private lemma innerSupremumOn_mono {A B : Set E} (hAB : A ⊆ B) (u : E) :
    innerSupremumOn A u ≤ innerSupremumOn B u := by
  -- Compare the two support values through inclusion of the defining images.
  rw [innerSupremumOn_eq_sSup_image, innerSupremumOn_eq_sSup_image]
  exact sSup_le_sSup <| by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hAB hx, rfl⟩

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: a pointwise upper bound on `⟪x, u⟫` over `S` bounds the support
value of `S` at `u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {S : Set E} {u : E} {b : EReal}
    (hbound : ∀ x ∈ S, (⟪x, u⟫_ℝ : EReal) ≤ b) :
    innerSupremumOn S u ≤ b := by
  -- Show that `b` is an upper bound for every value in the image defining the support function.
  rw [innerSupremumOn_eq_sSup_image]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hbound x hx

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: taking the closure of a set does not change its support value. -/
private lemma innerSupremumOn_closure_eq (S : Set E) (u : E) :
    innerSupremumOn (closure S) u = innerSupremumOn S u := by
  apply le_antisymm
  · -- Every point of `closure S` still lies in the closed halfspace determined by `σ[S] u`.
    refine innerSupremumOn_le_of_forall_inner_le ?_
    intro x hx
    have hclosed :
        IsClosed {z : E | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      simpa [Set.preimage, Set.setOf_mem_eq] using
        (isClosed_Iic.preimage
          (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)))
    have hsubset :
        S ⊆ {z : E | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      intro z hz
      rw [innerSupremumOn_eq_sSup_image]
      have hz_mem :
          (⟪z, u⟫_ℝ : EReal) ∈ ((fun y : E ↦ (⟪y, u⟫_ℝ : EReal)) '' S) :=
        ⟨z, hz, rfl⟩
      exact (isLUB_sSup _).1 hz_mem
    exact closure_minimal hsubset hclosed hx
  · -- The reverse inequality is immediate from `S ⊆ closure S`.
    exact innerSupremumOn_mono subset_closure u

/-- Proposition 7.2 (1): if `C ⊆ D`, then every support point of `D` that lies in `C` is a
support point of `C`, expressed using the textbook `spts` notation. -/
theorem inter_exposedPoints_subset_of_subset
    (C D : Set E) (hCD : C ⊆ D) :
    C ∩ spts D ⊆ spts C := by
  intro x hx
  rcases hx with ⟨hxC, hxD⟩
  rw [Set.mem_supportPoints_iff] at hxD ⊢
  rcases hxD with ⟨_, u, hu0, hu_support⟩
  -- Reuse the exposing vector for `D` and restrict the support inequality along `C ⊆ D`.
  refine ⟨hxC, u, hu0, ?_⟩
  exact le_trans (innerSupremumOn_mono hCD u) hu_support

-- Proof sketch: one inclusion follows from the first clause applied to `C ⊆ closure C`.
-- For the reverse inclusion, an exposing functional for `C` extends to `closure C` by continuity,
-- and the point remains in `C` by definition.
/-- Proposition 7.2 (2): the support points of `C` are exactly the points of `C` that are support
points of `closure C`. -/
theorem exposedPoints_eq_inter_exposedPoints_closure
    (C : Set E) :
    spts C = C ∩ spts (closure C) := by
  -- Route correction: work directly with the textbook `spts` witness and closure invariance of
  -- `innerSupremumOn`, rather than with the earlier off-spec exposed-point formulation.
  ext x
  constructor
  · intro hx
    rw [Set.mem_supportPoints_iff] at hx
    rcases hx with ⟨hxC, u, hu0, hu_support⟩
    -- Keep the same exposing vector and move the support inequality from `C` to `closure C`.
    refine ⟨hxC, ?_⟩
    rw [Set.mem_supportPoints_iff]
    refine ⟨subset_closure hxC, u, hu0, ?_⟩
    simpa [innerSupremumOn_closure_eq (S := C) (u := u)] using hu_support
  · intro hx
    -- Apply the inclusion statement to `C ⊆ closure C`.
    exact inter_exposedPoints_subset_of_subset C (closure C) subset_closure hx

end
