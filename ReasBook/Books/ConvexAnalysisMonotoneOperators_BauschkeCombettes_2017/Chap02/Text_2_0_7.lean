/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/- Text 2.0.7: for real Hilbert spaces `𝓗` and `𝓚` and a bounded linear operator
`T ∈ 𝓑(𝓗, 𝓚)`, the textbook adjoint operator `T*` is the canonical mathlib operator
`ContinuousLinearMap.adjoint T`, written `T†` in inner-product notation. -/
recall ContinuousLinearMap.adjoint

/- The defining identity of the adjoint is the standard inner-product identity
`⟪T x, y⟫ = ⟪x, T† y⟫`. -/
recall ContinuousLinearMap.adjoint_inner_right

/- The adjoint is uniquely characterized by the defining inner-product identity. -/
recall ContinuousLinearMap.eq_adjoint_iff
