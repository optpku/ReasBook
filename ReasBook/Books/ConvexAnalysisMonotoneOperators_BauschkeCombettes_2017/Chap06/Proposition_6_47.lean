/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
variable {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- Helper for Proposition 6.47: the support inequality on the translate `C - {p}` is equivalent
to the pointwise variational inequalities against all `y ∈ C`. -/
lemma innerSupremumOn_sub_singleton_le_zero_iff {u p : 𝓗} :
    innerSupremumOn (C - ({p} : Set 𝓗)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup y hy
    -- Compare the translate `C - {p}` against `{0}` to recover the pointwise inequalities.
    have hsep :
        innerSupremumOn (C - ({p} : Set 𝓗)) u ≤ innerInfimumOn ({0} : Set 𝓗) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set 𝓗)) ({0} : Set 𝓗) u).1 hsep
    have hy_sub : y - p ∈ C - ({p} : Set 𝓗) := by
      exact ⟨y, hy, p, by simp, rfl⟩
    simpa using hinner (y - p) hy_sub 0 (by simp)
  · intro hinner
    -- Every element of `C - {p}` is a difference `y - p`, so the pointwise family implies the
    -- support inequality against `{0}`.
    have hsep :
        innerSupremumOn (C - ({p} : Set 𝓗)) u ≤ innerInfimumOn ({0} : Set 𝓗) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set 𝓗)) ({0} : Set 𝓗) u).2
        (fun v hv z hz ↦ by
          have hz' : z = 0 := by simpa using hz
          subst hz'
          rcases hv with ⟨y, hy, w, hw, hv⟩
          have hw' : w = p := by simpa using hw
          have hv' : v = y - p := by
            simpa [hw'] using hv.symm
          simpa [hv'] using hinner y hy)
    simpa using hsep

/-- Helper for Proposition 6.47: membership in the normal cone at `p` is equivalent to the
variational inequality characterization with residual vector `x - p`. -/
lemma sub_mem_normalCone_iff_mem_and_inner_sub_right_nonpos {x p : 𝓗} :
    x - p ∈ Set.normalCone C p ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  constructor
  · intro hnormal
    -- Unfold the normal cone to isolate the support inequality at `p`.
    rcases hnormal with ⟨hp, hsup⟩
    refine ⟨hp, ?_⟩
    exact (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := x - p) (p := p)).1 hsup
  · rintro ⟨hp, hinner⟩
    -- Repackage the variational inequalities as the support inequality defining `N[C] p`.
    refine ⟨hp, ?_⟩
    exact (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := x - p) (p := p)).2 hinner

-- Proof sketch: rewrite `x - p ∈ N[C] p` using the definition of `Set.normalCone`, so the right
-- side becomes `p ∈ C ∧ innerSupremumOn (C - {p}) (x - p) ≤ 0`. Then identify that inequality
-- with the family of variational inequalities `⟪y - p, x - p⟫_ℝ ≤ 0` for all `y ∈ C`, and apply
-- `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex`.
variable [CompleteSpace 𝓗]

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Proposition 6.47: for a nonempty closed convex subset `C` of a real Hilbert space, a point `p`
is the metric projection of `x` onto `C` if and only if the residual vector `x - p` belongs to the
normal cone of `C` at `p`. -/
theorem eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex {x p : 𝓗} :
    p = P x ↔ x - p ∈ Set.normalCone C p := by
  -- Rewrite the projection statement into the Chapter 3 variational inequality.
  rw [eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex]
  -- Rewrite the normal-cone statement to the same middle characterization.
  simpa using
    (sub_mem_normalCone_iff_mem_and_inner_sub_right_nonpos (C := C) (x := x) (p := p)).symm

end
