/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Corollary_15_35

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Proof sketch: specialize Corollary 15.33 to `D = ⊥`, so closedness of `L(V)` is equivalent to
-- closedness of `Vᗮ + range L*`. For closed-range operators, the Chapter 3 bridge
-- `orthogonal_ker_eq_adjoint_range` identifies `range L*` with `(\ker L)ᗮ`. Corollary 15.35 then
-- converts closedness of `Vᗮ + (\ker L)ᗮ` to closedness of `V + \ker L`.
/-- Corollary 15.36: if `L` has closed range and `V` is a closed linear subspace, then `L(V)` is
closed if and only if `V + ker L` is closed. -/
theorem isClosed_map_iff_isClosed_sup_ker_of_isClosed_range
    (L : H →L[ℝ] K) (hL_range : IsClosed (L.range : Set K)) (V : Submodule ℝ H)
    (hV_closed : IsClosed (V : Set H)) :
    IsClosed ((V.map L.toLinearMap : Submodule ℝ K) : Set K) ↔
      IsClosed ((V ⊔ L.ker : Submodule ℝ H) : Set H) := by
  have hBot_closed : IsClosed ((⊥ : Submodule ℝ K) : Set K) := by
    rw [← Submodule.top_orthogonal_eq_bot]
    exact (⊤ : Submodule ℝ K).isClosed_orthogonal
  have h33 :
      IsClosed ((V.map L.toLinearMap : Submodule ℝ K) : Set K) ↔
        IsClosed (((Vᗮ) ⊔ (L.adjoint).range : Submodule ℝ H) : Set H) := by
    simpa using
      isClosed_map_sup_iff_isClosed_orthogonal_sup_adjoint_map_orthogonal
        V (⊥ : Submodule ℝ K) L hV_closed hBot_closed
  have hAdjointRange :
      (L.adjoint).range = L.kerᗮ := by
    simpa using (orthogonal_ker_eq_adjoint_range L hL_range).symm
  have h35 :
      IsClosed (((Vᗮ) ⊔ L.kerᗮ : Submodule ℝ H) : Set H) ↔
        IsClosed ((V ⊔ L.ker : Submodule ℝ H) : Set H) := by
    simpa using
      (isClosed_sup_iff_isClosed_orthogonal_sup_orthogonal V L.ker hV_closed L.isClosed_ker).symm
  exact h33.trans <| by simpa [hAdjointRange] using h35
