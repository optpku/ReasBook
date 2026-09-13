/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Rel

/-!
# Set-valued operators

This module defines the graph, domain, and pointwise operations for
set-valued operators.
-/

public section

open scoped Pointwise

universe u v

/-- A set-valued operator from `X` to `Y` is a function assigning a set in `Y`
to each point of `X`. -/
abbrev SetValuedOperator (X : Type u) (Y : Type v) := X → Set Y

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- The relation whose pairs are the points and values of a set-valued operator. -/
def graph (A : SetValuedOperator X Y) : SetRel X Y :=
  {p | p.2 ∈ A p.1}

/-- A pair belongs to an operator's graph exactly when its second component is
a value of the operator at its first component. -/
@[simp]
lemma mem_graph (A : SetValuedOperator X Y) (x : X) (y : Y) :
    (x, y) ∈ A.graph ↔ y ∈ A x := by
  -- Unfolding the graph reads membership directly in the value set at `x`.
  rfl

/-- The domain of a set-valued operator is the domain of its graph relation. -/
def dom (A : SetValuedOperator X Y) : Set X :=
  A.graph.dom

/-- A point belongs to an operator's domain exactly when its value there is
nonempty. -/
@[simp]
lemma mem_dom (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.dom ↔ (A x).Nonempty := by
  -- Relational-domain membership is exactly the existence of a value at `x`.
  rfl

/-- Membership in the graph of a pointwise sum is witnessed by one value from
each summand whose sum is the given value. -/
@[simp]
theorem mem_graph_add [Add Y] (A B : SetValuedOperator X Y) (x : X) (y : Y) :
    (x, y) ∈ (A + B).graph ↔
      ∃ y₁ ∈ A x, ∃ y₂ ∈ B x, y₁ + y₂ = y := by
  -- Pointwise function and set addition unfold to the two required witnesses.
  rfl

end SetValuedOperator
