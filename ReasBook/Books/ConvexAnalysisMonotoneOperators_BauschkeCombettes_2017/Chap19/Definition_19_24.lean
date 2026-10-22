/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Function

section

variable {𝕜 : Type*} {H : Type u} {E : Type v}
variable [Ring 𝕜] [Preorder 𝕜]
variable [AddCommMonoid H] [Module 𝕜 H] [AddCommGroup E] [Module 𝕜 E]

/-- Definition 19.24: a map `R : H → E` is convex with respect to `K` when, for every
`x, y ∈ H` and every `α ∈ ]0, 1[`, the strict Jensen defect
`R (α • x + (1 - α) • y) - α • R x - (1 - α) • R y` belongs to `K`. -/
def IsConvexWithRespectTo (𝕜 : Type*) [Ring 𝕜] [Preorder 𝕜] [Module 𝕜 H] [Module 𝕜 E]
    (R : H → E) (K : Set E) : Prop :=
  ∀ x y {α : 𝕜}, α ∈ Set.Ioo (0 : 𝕜) 1 →
    R (α • x + (1 - α) • y) - α • R x - (1 - α) • R y ∈ K

-- Proof sketch: unfold `IsConvexWithRespectTo` and apply the defining clause at the given
-- points `x`, `y`, and coefficient `α ∈ ]0, 1[`.
/-- A map that is convex with respect to `K` has every strict Jensen defect in `K`. -/
theorem IsConvexWithRespectTo.defect_mem
    {R : H → E} {K : Set E} (hR : R.IsConvexWithRespectTo 𝕜 K)
    {x y : H} {α : 𝕜} (hα : α ∈ Set.Ioo (0 : 𝕜) 1) :
    R (α • x + (1 - α) • y) - α • R x - (1 - α) • R y ∈ K :=
  hR x y hα

end

section OrderedCodomain

variable {𝕜 : Type*} {H : Type u} {E : Type v}
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid H] [Module 𝕜 H]
variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]

/-- For the positive cone, convexity with respect to `K` is exactly the standard concavity owner on
the whole space. This is the canonical bridge from the source-facing cone-defect formulation to the
ordered-codomain API. -/
theorem isConvexWithRespectTo_nonneg_iff_concaveOn_univ {R : H → E} :
    R.IsConvexWithRespectTo 𝕜 (Set.Ici (0 : E)) ↔ ConcaveOn 𝕜 Set.univ R := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · intro hR
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hb_eq : b = 1 - a := by
      rw [eq_sub_iff_add_eq]
      simpa [add_comm, add_left_comm, add_assoc] using hab
    have ha_mem : a ∈ Set.Ioo (0 : 𝕜) 1 := by
      refine ⟨ha, ?_⟩
      have hab' : a < a + b := lt_add_of_pos_right a hb
      simpa [hab] using hab'
    have hdef :
        0 ≤ R (a • x + b • y) - (a • R x + b • R y) := by
      simpa [hb_eq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hR x y ha_mem : R (a • x + (1 - a) • y) - a • R x - (1 - a) • R y ∈ Set.Ici (0 : E))
    exact sub_nonneg.mp hdef
  · rintro ⟨_, hR⟩ x y α hα
    change 0 ≤ R (α • x + (1 - α) • y) - α • R x - (1 - α) • R y
    exact sub_nonneg.mpr <| by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hR (by simp : x ∈ Set.univ) (by simp : y ∈ Set.univ)
          hα.1 (sub_pos.mpr hα.2) (by abel)

end OrderedCodomain

end Function
