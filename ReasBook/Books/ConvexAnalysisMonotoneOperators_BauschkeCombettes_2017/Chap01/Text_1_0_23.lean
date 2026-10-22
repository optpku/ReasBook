/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (A : Type u) (X : Type v)

/- Text 1.0.23: once the directed-set structure on the index type is fixed in the ambient
context, a net in `X` indexed by `A` is formalized by the canonical function type `A → X`. The
textbook's nonemptiness assumption on `X` does not affect this underlying data. -/
#check A → X
