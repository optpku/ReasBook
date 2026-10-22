/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open scoped ContinuousMap

noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Proposition 2.4.6: if `e : X ≃ₕ Y` is an unbased homotopy equivalence, then for every
basepoint `x : X` the induced map `e_* : π₁(X, x) → π₁(Y, e x)` is an isomorphism of groups. -/
-- Proof sketch: the equivalence of fundamental groupoids induced by `e` is fully faithful, so
-- on the vertex group at `x` it induces the corresponding multiplicative equivalence on
-- endomorphism groups.
def fundamentalGroupMulEquivOfHomotopyEquiv
    (e : X ≃ₕ Y)
    (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let F := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).functor
  let hF : F.FullyFaithful := .ofFullyFaithful F
  hF.mulEquivEnd (FundamentalGroupoid.mk x)

/-- The underlying homomorphism of `fundamentalGroupMulEquivOfHomotopyEquiv` is the usual map on
fundamental groups induced by the forward map of the homotopy equivalence. -/
@[simp] theorem fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom
    (e : X ≃ₕ Y)
    (x : X) :
    (fundamentalGroupMulEquivOfHomotopyEquiv e x).toMonoidHom = FundamentalGroup.map e.toFun x :=
  rfl
