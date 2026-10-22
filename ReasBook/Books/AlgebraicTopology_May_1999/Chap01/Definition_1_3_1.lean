/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open FundamentalGroup
open Path.Homotopic.Quotient
open scoped FundamentalGroup

/- Definition 1.3.1: for a path `a : Path x y`, the basepoint-change map
`γ[a] : π₁(X, x) → π₁(X, y)` is the canonical equivalence
`FundamentalGroup.fundamentalGroupMulEquivOfPath a`, acting by conjugation with `a`. -/
recall FundamentalGroup.fundamentalGroupMulEquivOfPath (a : Path x y) :
    FundamentalGroup X x ≃* FundamentalGroup X y

scoped[FundamentalGroup] notation "γ[" a "]" => fundamentalGroupMulEquivOfPath a

/-- The canonical basepoint-change equivalence sends a loop class to its conjugate by the given
path. -/
theorem fundamentalGroupMulEquivOfPath_apply_fromPath (a : Path x y) (f : Path x x) :
    γ[a] (fromPath ⟦f⟧) = fromPath ⟦(a.symm.trans f).trans a⟧ := by
  change mk (a.symm.trans (f.trans a)) = mk ((a.symm.trans f).trans a)
  rw [eq]
  exact (Path.Homotopic.trans_assoc a.symm f a).symm
