/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 2.0.2: for a Hilbert space `𝓗`, the identity operator is the canonical identity map
`id : 𝓗 → 𝓗`. -/
recall id

/-- The identity operator sends every element to itself. -/
theorem identity_operator_apply {𝓗 : Type u} (x : 𝓗) :
    id x = x := rfl
