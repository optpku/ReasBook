/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

-- Proof sketch: convert Jensen convexity of `φ` into convexity of its real-height epigraph using
-- Proposition 8.4. Proposition 8.25 packages the epigraph of `perspective φ` as both a cone and a
-- convex set. Proposition 10.2 turns that cone description into positive homogeneity, and
-- Proposition 10.3 upgrades positive homogeneity plus convex epigraph to sublinearity.
/-- Example 10.5: the perspective of a convex extended-real-valued function is sublinear. -/
theorem perspective_sublinear (φ : H → EReal) (hφ : IsConvex φ) :
    Sublinear (perspective φ) := by
  have hφ_epi : Convex ℝ (epigraph φ) := by
    refine (convex_epigraph_iff_jensen_on_dom φ).2 ?_
    intro x y hx hy α hα hα_lt_one
    exact hφ hα.le hα_lt_one.le
  rcases perspective_epigraph_eq_cone_and_convex φ hφ_epi with
    ⟨hperspective_epi, hperspective_convex⟩
  have hperspective_ph : PositivelyHomogeneous (perspective φ) := by
    rw [positivelyHomogeneous_iff_isCone_epigraph, hperspective_epi]
    ext x
    constructor
    · intro hx
      exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
    · intro hx
      rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
      simpa [Set.cone_def] using
        ConvexCone.smul_mem (ConvexCone.hull ℝ (perspectiveEpigraphSlice φ)) ha hy
  exact (sublinear_iff_convex_epigraph_of_positivelyHomogeneous (perspective φ)
    hperspective_ph).2 hperspective_convex

end RealVectorSpace
