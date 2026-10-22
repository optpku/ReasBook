/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: let `p := projectionPoint C _ (x - y)` and `q := y + p`. Then `q ∈ y +ᵥ C`.
-- Use the Hilbert-space characterization of projections onto nonempty closed convex sets on `C`
-- and transport the variational inequality by translation to show that `q` is the projection of
-- `x` onto `y +ᵥ C`.
/-- Proposition 3.19: the metric projection onto the translate `y + C = {y + z | z ∈ C}` is the
translate of the metric projection onto `C`, namely
`P_{y+C}(x) = y + P_C(x - y)`. -/
theorem projectionPoint_vadd_set_eq_add_projectionPoint {C : Set 𝓗}
    (x y : 𝓗) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    projectionPoint (y +ᵥ C)
        (isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty.vadd_set)
          (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
          (hC_convex.vadd y))
        x =
      y + projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x - y) := by
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let hT_cheb : IsChebyshev (y +ᵥ C) :=
    isChebyshev_of_nonempty_isClosed_convex
      (hC_nonempty.vadd_set)
      (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
      (hC_convex.vadd y)
  let p := projectionPoint C hC_cheb (x - y)
  let q := y + p
  have hp_char :
      p ∈ C ∧ ∀ z ∈ C, ⟪z - p, (x - y) - p⟫_ℝ ≤ 0 := by
    -- Theorem 3.16.2 gives the variational characterization of `p = P_C (x - y)`.
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp rfl
  have hq_proj :
      q =
        projectionPoint (y +ᵥ C) hT_cheb x := by
    -- Prove that the translated candidate `q` satisfies the translated variational inequality.
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (hC_nonempty.vadd_set)
        (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
        (hC_convex.vadd y)).mpr ?_
    refine ⟨?_, ?_⟩
    · -- Membership is preserved by translation.
      change ∃ u ∈ C, y + u = q
      exact ⟨p, hp_char.1, by simp [q]⟩
    · intro w hw
      rcases (by simpa [Set.mem_vadd_set, vadd_eq_add] using hw : ∃ z ∈ C, y + z = w) with
        ⟨z, hz, rfl⟩
      -- The translated inner product is exactly the original one after substituting `w = y + z`.
      have hsub1 : (y + z) - (y + p) = z - p := by
        abel_nf
      have hsub2 : x - (y + p) = (x - y) - p := by
        abel_nf
      simpa [q, hsub1, hsub2] using hp_char.2 z hz
  -- The translated characterization identifies the canonical projection uniquely.
  simpa [q, p] using hq_proj.symm
