/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Matrix.Basic

public section

namespace Matrix

/-- Two columns of a `0`-`1` matrix intersect if some row contains `true` in both columns. -/
def columnsIntersect {R C : Type*} (A : Matrix R C Bool) (u v : C) : Prop :=
  ∃ i : R, A i u = true ∧ A i v = true

/-- The column-intersection relation is symmetric. -/
theorem columnsIntersect_symm
    {R C : Type*} (A : Matrix R C Bool) :
    Symmetric (columnsIntersect A) := by
  intro u v h
  rcases h with ⟨i, hiu, hiv⟩
  exact ⟨i, hiv, hiu⟩

/-- Two columns intersect in the same rows, regardless of their order. -/
theorem columnsIntersect_comm
    {R C : Type*} (A : Matrix R C Bool) {u v : C} :
    columnsIntersect A u v ↔ columnsIntersect A v u := by
  constructor
  · intro h
    exact (columnsIntersect_symm A) h
  · intro h
    exact (columnsIntersect_symm A) h

/-- The intersection graph of a `0`-`1` matrix `A` is the simple graph on the column index type
whose vertices are the columns of `A`, with distinct vertices `u` and `v` adjacent exactly when
the columns intersect. -/
def intersectionGraph {R C : Type*} (A : Matrix R C Bool) : SimpleGraph C :=
  SimpleGraph.fromRel (columnsIntersect A)

/-- Two vertices are adjacent in `intersectionGraph A` exactly when they are distinct intersecting
columns of `A`. -/
theorem intersectionGraph_adj_iff_columnsIntersect
    {R C : Type*} (A : Matrix R C Bool) {u v : C} :
    (intersectionGraph A).Adj u v ↔ u ≠ v ∧ columnsIntersect A u v := by
  rw [intersectionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, huv' | hvu'⟩
    · exact ⟨huv, huv'⟩
    · exact ⟨huv, (columnsIntersect_symm A) hvu'⟩
  · rintro ⟨huv, hrow⟩
    exact ⟨huv, Or.inl hrow⟩

/-- Two vertices are adjacent in `intersectionGraph A` exactly when they are distinct columns
that both contain `true` in some common row of `A`. -/
theorem intersectionGraph_adj_iff
    {R C : Type*} (A : Matrix R C Bool) {u v : C} :
    (intersectionGraph A).Adj u v ↔
      u ≠ v ∧ ∃ i : R, A i u = true ∧ A i v = true := by
  rw [intersectionGraph_adj_iff_columnsIntersect, columnsIntersect]

end Matrix
