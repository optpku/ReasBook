/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_13

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 4.14: if `T : H → H` is firmly nonexpansive, then for every closed linear subspace
`V` the compressed operator `P_V ∘ T ∘ P_V` is firmly nonexpansive. -/
theorem orthogonal_projection_compression_firmly_nonexpansive
    (V : ClosedSubmodule ℝ H) {T : H → H}
    (hT : FirmlyNonexpansiveOn Set.univ (fun x ↦ T x)) :
    FirmlyNonexpansiveOn Set.univ
      (fun x ↦ (V.starProjection ∘ T ∘ V.starProjection) x) := by
  have hV : IsSelfAdjoint V.starProjection := isSelfAdjoint_starProjection (V : Submodule ℝ H)
  have h :=
    adjoint_comp_firmlyNonexpansive_of_norm_le_one T hT V.starProjection
      V.starProjection_norm_le
  simpa [Function.comp, hV.adjoint_eq] using h

end
