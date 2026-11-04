/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

open scoped BigOperators

noncomputable section

universe u v w

/- Primitive flow totals on a finite directed network with arc set `A` and endpoint maps `head`
and `tail`. `NetworkFlow.incoming head x v` and `NetworkFlow.outgoing tail x v` sum arc values
over the arcs entering and leaving `v`. -/
namespace NetworkFlow

variable {N : Type u} {A : Type v} {M : Type w} [Fintype A] [AddCommMonoid M]

/-- The finite set of arcs entering the vertex `v`. -/
@[expose]
def incomingArcs (head : A → N) (v : N) : Finset A :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq N := Classical.decEq N
  Finset.univ.filter fun a ↦ head a = v

/-- The finite set of arcs leaving the vertex `v`. -/
@[expose]
def outgoingArcs (tail : A → N) (v : N) : Finset A :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq N := Classical.decEq N
  Finset.univ.filter fun a ↦ tail a = v

/-- The total flow on arcs entering the vertex `v`. -/
@[expose]
def incoming (head : A → N) (x : A → M) (v : N) : M :=
  Finset.sum (NetworkFlow.incomingArcs head v) x

/-- The total flow on arcs leaving the vertex `v`. -/
@[expose]
def outgoing (tail : A → N) (x : A → M) (v : N) : M :=
  Finset.sum (NetworkFlow.outgoingArcs tail v) x

/-- `NetworkFlow.incoming` is the sum over the incoming arc fiber of `v`. -/
theorem incoming_def (head : A → N) (x : A → M) (v : N) :
    NetworkFlow.incoming head x v = Finset.sum (NetworkFlow.incomingArcs head v) x := rfl

/-- `NetworkFlow.outgoing` is the sum over the outgoing arc fiber of `v`. -/
theorem outgoing_def (tail : A → N) (x : A → M) (v : N) :
    NetworkFlow.outgoing tail x v = Finset.sum (NetworkFlow.outgoingArcs tail v) x := rfl

end NetworkFlow
