/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_16

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

-- Proof sketch: apply the projection characterization from
-- `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` to `P x`
-- with test point `P y`, and to `P y` with test point `P x`; adding the resulting inequalities and
-- rearranging yields the displayed firm nonexpansiveness inequality.
/-- Text 4.21.1 (1): the metric projection onto a nonempty closed convex subset of a real Hilbert
space is firmly nonexpansive. -/
theorem firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex :
    FirmlyNonexpansive P := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  exact
    norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x y

/-- Helper for Text 4.21.1: every point of `C` is fixed by the metric projection onto `C`. -/
private theorem projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex {x : 𝓗} (hx : x ∈ C) :
    P x = x := by
  -- The projection characterization is realized by `x` itself because the residual vanishes.
  have hxproj : x = P x := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
  simpa using hxproj.symm

-- Proof sketch: if `x ∈ C`, then the projection of `x` onto `C` is `x` itself because the
-- distance is `0`; conversely, every fixed point of `P` lies in `C` since projection points lie in
-- the target set.
/-- Text 4.21.1 (2): the fixed point set of the metric projection onto `C` is exactly `C`. -/
theorem fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex :
    Function.fixedPoints P = C := by
  ext x
  constructor
  · intro hx
    -- Fixed points belong to `C` because every projection point lies in the target set.
    rw [Function.mem_fixedPoints_iff] at hx
    simpa [hx] using
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  · intro hx
    -- Points already in `C` are fixed by the projection by the helper lemma above.
    rw [Function.mem_fixedPoints_iff]
    exact
      projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex hx

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_closed`.
/-- Text 4.21.1 (3): the fixed point set of the metric projection onto `C` is closed. -/
theorem isClosed_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    IsClosed (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit closedness from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_closed

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_convex`.
/-- Text 4.21.1 (4): the fixed point set of the metric projection onto `C` is convex. -/
theorem convex_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    Convex ℝ (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit convexity from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_convex

end
