/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

-- Proof sketch: split on the sign of `ξ`. For `ξ > 0`, unfold both definitions and use
-- `ξ⁻¹ • (1 : ℝ) = 1 / ξ`; for `ξ ≤ 0`, both sides reduce to `⊤`.
/-- The adjoint is the perspective transform specialized to the second coordinate `1`. -/
theorem adjoint_eq_perspective_one (φ : ℝ → Set.Ioi (⊥ : EReal)) (ξ : ℝ) :
    (adjoint φ ξ : EReal) = perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)) := by
  by_cases hξ : 0 < ξ
  · -- On the positive branch, both formulas are `ξ` times the value of `φ` at the normalized point.
    rw [adjoint_apply_of_pos φ hξ, perspective_apply_of_pos _ hξ]
    simp [one_div, smul_eq_mul]
  · have hξ_nonpos : ξ ≤ 0 := le_of_not_gt hξ
    -- On the nonpositive branch, both definitions take the `⊤` case.
    rw [adjoint_apply_of_nonpos φ hξ_nonpos, perspective_apply_of_nonpos _ hξ_nonpos]

/-- Helper for Example 8.33: convexity on all of `ℝ` gives convexity of the real-height epigraph of
the coerced extended-real-valued function. -/
private theorem convex_epigraph_coe_of_convexOn_univ
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : ConvexOn φ Set.univ) :
    Convex ℝ (epigraph (fun x : ℝ ↦ (φ x : EReal))) := by
  -- Proposition 8.4 turns the epigraph goal into the Jensen inequality on the effective domain.
  refine (convex_epigraph_iff_jensen_on_dom (fun x : ℝ ↦ (φ x : EReal))).2 ?_
  intro x y _hx _hy α hα hα_lt_one
  -- Since the set is `univ`, the textbook convexity hypothesis applies to every pair of points.
  simpa using hφ.ineq (x := x) (y := y) (by simp) (by simp) hα hα_lt_one

/-- Helper for Example 8.33: slicing a convex perspective epigraph along the affine line
`ξ ↦ (ξ, 1)` preserves convexity. -/
private theorem convex_epigraph_perspective_one_slice
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hpersp :
      Convex ℝ (epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))))) :
    Convex ℝ (epigraph (fun ξ : ℝ ↦ perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)))) := by
  refine (convex_iff_forall_pos).2 ?_
  intro p hp q hq a b ha hb hab
  rcases p with ⟨ξ₁, η₁⟩
  rcases q with ⟨ξ₂, η₂⟩
  have hp' : (((ξ₁, (1 : ℝ)), η₁)) ∈ epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- The slice epigraph point is exactly the ambient perspective epigraph point at height `1`.
    simpa [mem_epigraph_iff] using hp
  have hq' : (((ξ₂, (1 : ℝ)), η₂)) ∈ epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- The second endpoint is lifted to the same ambient epigraph in the same way.
    simpa [mem_epigraph_iff] using hq
  have hcombo :
      a • (((ξ₁, (1 : ℝ)), η₁) : (ℝ × ℝ) × ℝ) +
          b • (((ξ₂, (1 : ℝ)), η₂) : (ℝ × ℝ) × ℝ) ∈
        epigraph (perspective (fun x : ℝ ↦ (φ x : EReal))) := by
    -- Convexity of the full perspective epigraph transfers the two lifted endpoints.
    exact (convex_iff_forall_pos.mp hpersp) hp' hq' ha hb hab
  -- Expanding the convex combination shows that the second coordinate stays fixed at `1`.
  simpa [mem_epigraph_iff, Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, hab]
    using hcombo

-- Proof sketch: identify `adjoint φ` with the affine slice `ξ ↦ perspective (fun x ↦ (φ x :
-- EReal)) (ξ, 1)` using `adjoint_eq_perspective_one`. Then apply Proposition 8.25 to the convex
-- epigraph of `φ` and restrict the resulting convexity of the perspective to the line
-- `ξ ↦ (ξ, 1)`.
/-- Example 8.33: if `φ : ℝ → ]-∞,+∞]` is convex, then the function `φ*` defined by
`φ*(ξ) = ξ φ(1 / ξ)` for `ξ > 0` and `φ*(ξ) = +∞` for `ξ ≤ 0` is convex in the extended-real
epigraph sense.  Its effective domain is generally not all of `ℝ`. -/
theorem adjoint_convexOn_univ (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : ConvexOn φ Set.univ) :
    Convex ℝ (epigraph (fun ξ : ℝ ↦ (adjoint φ ξ : EReal))) := by
  -- Route correction: the target is epigraph convexity, not `ConvexOn (adjoint φ) Set.univ`,
  -- because the adjoint equals `⊤` on `ξ ≤ 0`.
  have hφ_convex :
      Convex ℝ (epigraph (fun x : ℝ ↦ (φ x : EReal))) :=
    convex_epigraph_coe_of_convexOn_univ φ hφ
  have hpersp_convex :
      Convex ℝ (epigraph (perspective (fun x : ℝ ↦ (φ x : EReal)))) :=
    convex_epigraph_perspective _ hφ_convex
  have hslice_convex :
      Convex ℝ (epigraph (fun ξ : ℝ ↦ perspective (fun x : ℝ ↦ (φ x : EReal)) (ξ, (1 : ℝ)))) :=
    convex_epigraph_perspective_one_slice φ hpersp_convex
  -- Rewrite the slice back to the textbook adjoint formula.
  simpa [adjoint_eq_perspective_one] using hslice_convex

end ERealFunction
