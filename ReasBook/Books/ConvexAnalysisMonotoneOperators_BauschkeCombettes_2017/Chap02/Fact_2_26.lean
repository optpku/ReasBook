/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProductSpace

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Fact 2.26: for a bounded operator between real Hilbert spaces, closedness of the ranges of
`T`, `T†`, and `T ∘L T†` is equivalent to a uniform lower bound for `‖T x‖` on `(ker T)ᗮ`. -/
-- Proof sketch: combine the orthogonal-kernel and orthogonal-range identities for adjoints with
-- the Banach closed-range criterion applied to the restriction of `T` to `(ker T)ᗮ`, and use the
-- standard `TFAE` package to organize the four equivalent clauses.
theorem continuousLinearMap_tfae_closed_range (T : H →L[ℝ] K) :
    List.TFAE
      [IsClosed (T.range : Set K),
        IsClosed ((adjoint T).range : Set H),
        IsClosed (((T ∘L adjoint T).range : Set K)),
        ∃ α > 0, ∀ x ∈ T.kerᗮ, α * ‖x‖ ≤ ‖T x‖] := sorry

namespace ContinuousLinearMap

/-- Closedness of `range (T ∘L T†)` is equivalent to closedness of `range T`. -/
theorem isClosed_range_comp_adjoint_iff (T : H →L[ℝ] K) :
    IsClosed (((T ∘L adjoint T).range : Set K)) ↔ IsClosed (T.range : Set K) := by
  have h₁ :
      [IsClosed (T.range : Set K),
        IsClosed ((adjoint T).range : Set H),
        IsClosed (((T ∘L adjoint T).range : Set K)),
        ∃ α > 0, ∀ x ∈ T.kerᗮ, α * ‖x‖ ≤ ‖T x‖][2]? =
        some (IsClosed (((T ∘L adjoint T).range : Set K))) := by
    rfl
  have h₂ :
      [IsClosed (T.range : Set K),
        IsClosed ((adjoint T).range : Set H),
        IsClosed (((T ∘L adjoint T).range : Set K)),
        ∃ α > 0, ∀ x ∈ T.kerᗮ, α * ‖x‖ ≤ ‖T x‖][0]? =
        some (IsClosed (T.range : Set K)) := by
    rfl
  exact List.TFAE.out (continuousLinearMap_tfae_closed_range T) 2 0 h₁ h₂

/-- Closedness of `range T` is equivalent to closedness of `range T†`. -/
theorem isClosed_range_iff_isClosed_range_adjoint (T : H →L[ℝ] K) :
    IsClosed (T.range : Set K) ↔ IsClosed ((adjoint T).range : Set H) := by
  simpa using (List.TFAE.out (continuousLinearMap_tfae_closed_range T) 0 1)

/-- Closedness of `range T` is equivalent to a uniform lower bound for `‖T x‖` on `(ker T)ᗮ`. -/
theorem isClosed_range_iff_exists_pos_le_norm_of_mem_orthogonal_ker (T : H →L[ℝ] K) :
    IsClosed (T.range : Set K) ↔ ∃ α > 0, ∀ x ∈ T.kerᗮ, α * ‖x‖ ≤ ‖T x‖ := by
  simpa using (List.TFAE.out (continuousLinearMap_tfae_closed_range T) 0 3)

end ContinuousLinearMap
