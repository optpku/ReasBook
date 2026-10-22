/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section PointwiseSupremum

variable {H : Type u} {ι : Type v} [Nonempty ι]

-- Proof sketch: choose any index from `ι`; its value is one of the terms in the `iSup`, and each
-- family value lies strictly above `⊥` because the codomain is `Set.Ioi (⊥ : EReal)`.
/-- The pointwise supremum of a nonempty family of `]-∞,+∞]`-valued functions is still strictly
above `-∞`. -/
private theorem bot_lt_iSup_family_apply
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    (⊥ : EReal) < ⨆ i, (f i x : EReal) := sorry

/-- The pointwise supremum of a nonempty family of `]-∞,+∞]`-valued functions. -/
def pointwiseSup (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) : Set.Ioi (⊥ : EReal) :=
  ⟨⨆ i, (f i x : EReal), bot_lt_iSup_family_apply f x⟩

-- Proof sketch: unfold `pointwiseSup`; the subtype coercion forgets only the proof that the
-- supremum stays in `]-∞,+∞]`.
/-- Coercing `pointwiseSup f` to `EReal` recovers the defining indexed supremum. -/
@[simp] theorem pointwiseSup_apply
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    (pointwiseSup f x : EReal) = ⨆ i, (f i x : EReal) :=
  rfl

/-- The active indices at `x` are those where the family value reaches the pointwise supremum. -/
def activeIndices (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) : Set ι :=
  {i | (f i x : EReal) = (pointwiseSup f x : EReal)}

-- Proof sketch: unfold `activeIndices`.
/-- An index is active exactly when its value at `x` equals the pointwise supremum. -/
@[simp] theorem mem_activeIndices_iff
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) (i : ι) :
    i ∈ activeIndices f x ↔ (f i x : EReal) = (pointwiseSup f x : EReal) :=
  Iff.rfl

end PointwiseSupremum

section PointwiseSupremumSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type v} [Finite ι] [Nonempty ι]

-- Proof sketch: the pointwise supremum of finitely many convex functions is again convex, and at
-- a common point of the source continuity sets `cont (f i)` the directional derivative of the
-- supremum is the pointwise supremum of the directional derivatives of the active functions. Apply
-- Theorem 17.18 to the maximum and to each active summand, then identify support functions under
-- finite convex hull and weak compactness.
/-- Theorem 18.5: for a nonempty finite family of convex `]-∞,+∞]`-valued functions, the
subdifferential of the pointwise supremum at a common source continuity point is the convex hull
of the union of the subdifferentials of the active functions at that point. -/
theorem subdifferential_pointwiseSup_eq_convexHull_activeSubdifferentials
    (f : ι → H → Set.Ioi (⊥ : EReal))
    (hconv : ∀ i, ConvexOn (f i) (effectiveDomain (f i)))
    {x : H} (hxcont : ∀ i, x ∈ cont (f i)) :
    (∂ pointwiseSup f) x =
      convexHull ℝ (⋃ i ∈ activeIndices f x, (∂ f i) x) := sorry

end PointwiseSupremumSubdifferential

end

end ERealFunction
