/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: if `u ∈ orthogonalSet C`, then `⟪x, u⟫ = 0` for every `x ∈ C`, hence in particular
-- `⟪x, u⟫ ≤ 0`; rewriting with `mem_orthogonalSet` and `mem_polarCone_iff_forall_inner_nonpos`
-- yields the inclusion.
/-- Proposition 7.16 (1): textbook clause (i), first half. The orthogonal set of `C` is contained
in its polar cone. -/
theorem orthogonalSet_subset_polarCone (C : Set 𝓗) :
    orthogonalSet C ⊆ polarCone C := by
  intro u hu
  -- Rewrite both memberships pointwise so the orthogonality hypothesis becomes a nonpositivity
  -- bound.
  rw [mem_orthogonalSet] at hu
  rw [mem_polarCone_iff_forall_inner_nonpos]
  intro x hx
  exact (hu x hx).le

-- Proof sketch: every inequality `⟪x, u⟫ ≤ 0` required for `u ∈ Cᵒ⊖` is stronger than the
-- inequality `⟪x, u⟫ ≤ 1` required for `u ∈ Cᵒ⊙`; rewrite both sides by their pointwise
-- characterizations.
/-- Proposition 7.16 (2): textbook clause (i), second half. The polar cone of `C` is contained in
its polar set. -/
theorem polarCone_subset_polarSet (C : Set 𝓗) :
    polarCone C ⊆ polarSet C := by
  intro u hu
  -- Route correction: compare the pointwise inequalities directly, instead of unfolding the two
  -- `sSup` definitions separately.
  rw [mem_polarCone_iff_forall_inner_nonpos] at hu
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  linarith [hu x hx]

-- Proof sketch: for every `x ∈ C`, one has `⟪x, 0⟫ = 0 ≤ 1`, so the pointwise characterization of
-- the polar set places `0` in `Cᵒ⊙`.
/-- Proposition 7.16 (3): textbook clause (ii), first part. The origin belongs to the polar set of
every subset. -/
theorem zero_mem_polarSet (C : Set 𝓗) :
    (0 : 𝓗) ∈ polarSet C := by
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  -- The inner product with the origin vanishes, so the required bound is immediate.
  simp

-- Proof sketch: `Cᵒ⊙` is the intersection over `x ∈ C` of the closed halfspaces
-- `{u | ⟪x, u⟫ ≤ 1}`; each such halfspace is closed because `u ↦ ⟪x, u⟫` is continuous.
/-- Proposition 7.16 (4): textbook clause (ii), second part. The polar set of a subset is closed.
-/
theorem polarSet_isClosed (C : Set 𝓗) :
    IsClosed (polarSet C) := by
  have hrepr :
      polarSet C = ⋂ x : C, {u : 𝓗 | ⟪(x : 𝓗), u⟫_ℝ ≤ 1} := by
    -- Rewrite polar membership as the family of halfspace inequalities indexed by points of `C`.
    ext u
    simp [mem_polarSet_iff_forall_inner_le_one]
  rw [hrepr]
  -- Each defining halfspace is closed because `u ↦ ⟪x, u⟫` is continuous.
  refine isClosed_iInter fun x ↦ ?_
  simpa using isClosed_le (continuous_const.inner continuous_id) continuous_const

-- Proof sketch: the same halfspace description shows that `Cᵒ⊙` is an intersection of convex
-- sets, hence convex.
/-- Proposition 7.16 (5): textbook clause (ii), third part. The polar set of a subset is convex.
-/
theorem polarSet_convex (C : Set 𝓗) :
    Convex ℝ (polarSet C) := by
  have hrepr :
      polarSet C = ⋂ x : C, {u : 𝓗 | ⟪(x : 𝓗), u⟫_ℝ ≤ 1} := by
    -- The same halfspace representation used for closedness gives the convexity proof.
    ext u
    simp [mem_polarSet_iff_forall_inner_le_one]
  rw [hrepr]
  refine convex_iInter fun x ↦ ?_
  intro u hu v hv a b ha hb hab
  -- A convex combination preserves the affine upper bound on each halfspace.
  dsimp at hu hv ⊢
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith

-- Proof sketch: if `x ∈ C`, then every `u ∈ Cᵒ⊙` satisfies `⟪x, u⟫ ≤ 1`, so `x ∈ (Cᵒ⊙)ᵒ⊙`; the
-- origin lies in `(Cᵒ⊙)ᵒ⊙` by the previous clause applied to `Cᵒ⊙`, hence the union with `{0}` is
-- contained in the bipolar set.
/-- Proposition 7.16 (6): textbook clause (iii). Every point of `C`, and also the origin, belongs
to the bipolar polar set of `C`. -/
theorem union_singleton_zero_subset_polarSet_polarSet (C : Set 𝓗) :
    C ∪ ({0} : Set 𝓗) ⊆ polarSet (polarSet C) := by
  intro x hx
  rcases hx with hxC | hx0
  · rw [mem_polarSet_iff_forall_inner_le_one]
    -- If `x ∈ C`, every element of `Cᵒ⊙` already bounds `⟪x, ·⟫` by `1`.
    intro u hu
    rw [mem_polarSet_iff_forall_inner_le_one] at hu
    simpa [real_inner_comm] using hu x hxC
  · -- The origin case is exactly the previous clause applied to `Cᵒ⊙`.
    rcases Set.mem_singleton_iff.mp hx0 with rfl
    exact zero_mem_polarSet (C := polarSet C)

-- Proof sketch: if `C ⊆ D`, then every inequality defining membership in `Dᵒ⊙` is among the
-- inequalities defining membership in `Cᵒ⊙`, so the polar-set operation is antitone.
/-- Proposition 7.16 (7): textbook clause (iv), first half. Inclusion of sets reverses under the
polar-set operation. -/
theorem polarSet_subset_of_subset {C D : Set 𝓗} (hCD : C ⊆ D) :
    polarSet D ⊆ polarSet C := by
  intro u hu
  -- Antitonicity is just restriction of the defining inequalities along `C ⊆ D`.
  rw [mem_polarSet_iff_forall_inner_le_one] at hu
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  exact hu x (hCD hx)

-- Proof sketch: apply the previous antitonicity statement to the inclusion `Dᵒ⊙ ⊆ Cᵒ⊙` coming
-- from `C ⊆ D`; taking polars once more reverses that inclusion and yields monotonicity of the
-- bipolar operation.
/-- Proposition 7.16 (8): textbook clause (iv), second half. Inclusion of sets preserves bipolar
polar sets. -/
theorem polarSet_polarSet_subset_of_subset {C D : Set 𝓗} (hCD : C ⊆ D) :
    polarSet (polarSet C) ⊆ polarSet (polarSet D) := by
  -- Apply antitonicity twice: once to `C ⊆ D`, and once again to the resulting reverse inclusion.
  exact polarSet_subset_of_subset (C := polarSet D) (D := polarSet C)
    (polarSet_subset_of_subset hCD)

-- Proof sketch: clause (6) applied to `Cᵒ⊙` gives `Cᵒ⊙ ⊆ ((Cᵒ⊙)ᵒ⊙)ᵒ⊙`, while clause (7) applied to
-- `C ⊆ (Cᵒ⊙)ᵒ⊙` gives the reverse inclusion `((Cᵒ⊙)ᵒ⊙)ᵒ⊙ ⊆ Cᵒ⊙`.
/-- Proposition 7.16 (9): textbook clause (v). Taking the polar set three times gives the same set
as taking it once. -/
theorem polarSet_polarSet_polarSet_eq_polarSet (C : Set 𝓗) :
    polarSet (polarSet (polarSet C)) = polarSet C := by
  apply Subset.antisymm
  · have hC : C ⊆ polarSet (polarSet C) := by
      intro x hx
      exact union_singleton_zero_subset_polarSet_polarSet (C := C) (Or.inl hx)
    -- Antitonicity applied to `C ⊆ Cᵒ⊙ᵒ⊙` gives the reverse inclusion.
    exact polarSet_subset_of_subset hC
  · intro u hu
    -- Applying clause (iii) to `Cᵒ⊙` gives the forward inclusion.
    exact union_singleton_zero_subset_polarSet_polarSet (C := polarSet C) (Or.inl hu)

/-- Helper for Proposition 7.16: polar-set membership is exactly the support-function bound
`innerSupremumOn C u ≤ 1`. -/
theorem mem_polarSet_iff_innerSupremumOn_le_one {C : Set 𝓗} {u : 𝓗} :
    u ∈ polarSet C ↔ innerSupremumOn C u ≤ 1 := by
  -- This is just the polar-set definition rewritten through the project support-function notation.
  simpa [innerSupremumOn_eq_sSup_image] using (mem_polarSet_iff (C := C) (u := u))

-- Proof sketch: membership in a polar set is the inequality `σ[C] u ≤ 1`, and Proposition 7.13
-- identifies the support functions of `C` and `closure (convexHull ℝ C)`. Rewriting both polar
-- sets with that support-function criterion yields the equality.
/-- Proposition 7.16 (10): textbook clause (vi). Passing to the closed convex hull does not change
the polar set. -/
theorem closure_convexHull_polarSet_eq (C : Set 𝓗) :
    polarSet (closure (convexHull ℝ C)) = polarSet C := by
  ext u
  -- Rewrite both polar memberships as support-function inequalities and substitute Proposition
  -- 7.13.
  rw [mem_polarSet_iff_innerSupremumOn_le_one, mem_polarSet_iff_innerSupremumOn_le_one]
  obtain ⟨hconv, hclosure⟩ := supportFunction_eq_convexHull_and_closure_convexHull (C := C)
  have hsupport :
      innerSupremumOn C u = innerSupremumOn (closure (convexHull ℝ C)) u := by
    exact (congrFun hconv u).trans (congrFun hclosure u)
  simp [hsupport]

end

end Set
