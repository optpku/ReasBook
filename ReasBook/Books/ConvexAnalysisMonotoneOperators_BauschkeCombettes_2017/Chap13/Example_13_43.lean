/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Corollary_7_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: if `C = ∅`, then both sides are the constant function `⊤`. Otherwise apply the
-- Fenchel--Moreau theorem to the proper indicator of `C`, then use Example 13.3(i) and
-- Proposition 7.13 to identify the conjugate support function with the indicator of
-- `closedConvexHull ℝ C`.
/-- Example 13.43: the Fenchel biconjugate of the indicator of `C` is the indicator of the closed
convex hull of `C`. -/
theorem biconjugate_indicator_eq_indicator_closedConvexHull
    (C : Set H) :
    ((ι[C]).asEReal)∗∗ = (ι[closedConvexHull ℝ C]).asEReal := by
  by_cases hC : C.Nonempty
  · let D : Set H := closedConvexHull ℝ C
    have hD : D.Nonempty := hC.mono subset_closedConvexHull
    have hD_gamma : ι[D] ∈ Γ₀(H) :=
      indicator_mem_gammaZero_of_nonempty_isClosed_convex hD
        (by simpa [D] using (isClosed_closedConvexHull : IsClosed (closedConvexHull ℝ C)))
        (by simpa [D] using (convex_closedConvexHull : Convex ℝ (closedConvexHull ℝ C)))
    have hconj : ((ι[C]).asEReal)∗ = ((ι[D]).asEReal)∗ := by
      rw [conjugate_indicator_eq_supportFunction, conjugate_indicator_eq_supportFunction]
      obtain ⟨hconv, hclosure⟩ := supportFunction_eq_convexHull_and_closure_convexHull C
      simpa [D, closedConvexHull_eq_closure_convexHull] using hconv.trans hclosure
    calc
      ((ι[C]).asEReal)∗∗ = ((ι[D]).asEReal)∗∗ := by
        simpa using congrArg conjugate hconj
      _ = (ι[D]).asEReal := biconjugate_eq_of_mem_gammaZero hD_gamma
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    have hσ_empty : σ[(∅ : Set H)] = (fun _ : H ↦ (⊥ : EReal)) := by
      ext x
      simp [innerSupremumOn_eq_sSup_image]
    ext x
    rw [conjugate_indicator_eq_supportFunction]
    simp [hC_empty, hσ_empty, closedConvexHull_eq_closure_convexHull, ERealFunction.conjugate]

-- Proof sketch: the indicator of a closed linear subspace lies in `Γ(H)` and is proper because
-- the subspace is nonempty; Theorem 13.37 then gives `ι[V]** = ι[V]`.
/-- Clause (ii) of the current example: the indicator of a closed linear subspace is equal to its
Fenchel biconjugate. -/
theorem biconjugate_indicator_submodule_eq_indicator_of_isClosed
    (V : Submodule ℝ H) (hV_closed : IsClosed (V : Set H)) :
    ((ι[(V : Set H)]).asEReal)∗∗ = (ι[(V : Set H)]).asEReal := by
  have hV_gamma : ι[(V : Set H)] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      ⟨0, V.zero_mem⟩ hV_closed V.convex
  simpa using biconjugate_eq_of_mem_gammaZero hV_gamma

/- Clause (ii) of the current example is the forward direction of the canonical closed-subspace
criterion already proved in Corollary 7.19. -/
recall Set.isClosed_iff_orthogonal_orthogonal_eq

-- Proof sketch: if `K = ∅`, then both sides are the constant function `⊤`. Otherwise a nonempty
-- closed convex set has indicator in `Γ₀(H)`, so Corollary 13.38 yields `ι[K]** = ι[K]`; the
-- source cone case is the corresponding specialization.
/-- Clause (iii) of the current example follows from the closed-convex indicator theorem; in
particular, every closed convex cone has indicator equal to its Fenchel biconjugate. -/
theorem biconjugate_indicator_eq_indicator_of_isClosed_convex
    (K : Set H) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) :
    ((ι[K]).asEReal)∗∗ = (ι[K]).asEReal := by
  by_cases hK_nonempty : K.Nonempty
  · have hK_gamma : ι[K] ∈ Γ₀(H) :=
      indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
    simpa using biconjugate_eq_of_mem_gammaZero hK_gamma
  · have hK_empty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hK_nonempty
    have hσ_empty : σ[(∅ : Set H)] = (fun _ : H ↦ (⊥ : EReal)) := by
      ext x
      simp [innerSupremumOn_eq_sSup_image]
    ext x
    rw [conjugate_indicator_eq_supportFunction]
    simp [hK_empty, hσ_empty, ERealFunction.conjugate]

/- The source cone formulation in clause (iii) is governed geometrically by the
closed-cone bipolar theorem already proved in Corollary 7.19. -/
recall Set.polarCone_polarCone_eq_of_nonempty_of_isClosed_of_convex_of_isCone

end Conjugation

end ERealFunction
