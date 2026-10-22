/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open scoped FundamentalGroup

/-- Remark 1.3.6: when `π₁(X, x)` is Abelian, all basepoints in the same path component are
canonically identified at the level of the fundamental group, since the basepoint-change
equivalence attached to `Joined x y` agrees with the one induced by any path from `x` to `y`. -/
-- Proof sketch: apply Lemma 1.3.5 to the two paths `h.somePath` and `a`, using commutativity of
-- `FundamentalGroup X x` to conclude that their induced basepoint-change equivalences coincide.
theorem fundamentalGroupMulEquivOfJoined_eq_of_path
    [Std.Commutative ((· * ·) : FundamentalGroup X x → FundamentalGroup X x → FundamentalGroup X x)]
    (h : Joined x y) (a : Path x y) :
    γ[h.somePath] = γ[a] :=
  fundamentalGroupMulEquivOfPath_eq_of_abelian h.somePath a
