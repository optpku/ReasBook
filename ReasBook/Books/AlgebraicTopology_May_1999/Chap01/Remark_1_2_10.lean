/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

variable {X : Type u} [TopologicalSpace X] (x : X)

/- Remark 1.2.10: later homotopy groups are organized into the family `π_ n X x`; the
fundamental group is the first member of this family, so `π_ 1 X x` is canonically identified
with `FundamentalGroup X x`. -/
recall HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x
