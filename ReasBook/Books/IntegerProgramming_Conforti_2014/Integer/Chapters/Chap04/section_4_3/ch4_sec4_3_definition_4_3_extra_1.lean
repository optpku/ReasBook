import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- Semantic recall note: local repository inspection found no earlier Chapter 4 owner for directed
-- incidence matrices, so this file uses Mathlib's canonical `Matrix` API with explicit tail/head
-- maps, matching the owner shape of `SimpleGraph.incMatrix`. The equality decision on vertices is
-- an internal implementation detail rather than part of the public owner surface.

variable {V A : Type}

/-- Definition 4.3-extra-1 (1). The incidence matrix of a digraph with vertex set `V`, arc set
`A`, tail map `tail`, and head map `head` is the `V × A` matrix whose entry at row `w` and
column `e` is the head indicator minus the tail indicator. Thus non-loop arcs contribute `1` at
the head, `-1` at the tail, and `0` elsewhere, while loop columns cancel to `0`. The loopless
hypothesis `tail e ≠ head e` is needed only for later source-facing lemmas, not for the matrix
itself. -/
noncomputable def digraph_incidence_matrix
    (R : Type*) [AddGroup R] [One R] (tail head : A → V) : Matrix V A R :=
  let _ : DecidableEq V := Classical.decEq V
  fun w e ↦ (if w = head e then (1 : R) else 0) - (if w = tail e then 1 else 0)

/-- At the tail of a non-loop arc, the corresponding incidence-matrix entry is `-1`. -/
theorem digraph_incidence_matrix_tail
    (R : Type*) [AddGroup R] [One R] (tail head : A → V)
    (e : A)
    (tail_ne_head : tail e ≠ head e) :
    digraph_incidence_matrix R tail head (tail e) e = -1 := by
  classical
  by_cases h : tail e = head e
  · exact (tail_ne_head h).elim
  · simp [digraph_incidence_matrix, h]

/-- At the head of a non-loop arc, the corresponding incidence-matrix entry is `1`. -/
theorem digraph_incidence_matrix_head
    (R : Type*) [AddGroup R] [One R] (tail head : A → V)
    (e : A)
    (tail_ne_head : tail e ≠ head e) :
    digraph_incidence_matrix R tail head (head e) e = 1 := by
  classical
  by_cases h : head e = tail e
  · exact (tail_ne_head h.symm).elim
  · simp [digraph_incidence_matrix, h]

/-- Helper for Definition 4.3-extra-1: away from the tail and head of an arc, the incidence
matrix entry is `0`. -/
lemma digraph_incidence_matrix_eq_zero_of_ne_endpoints
    (R : Type*) [AddGroup R] [One R] (tail head : A → V)
    {w : V}
    {e : A}
    (hw_tail : w ≠ tail e)
    (hw_head : w ≠ head e) :
    digraph_incidence_matrix R tail head w e = 0 := by
  classical
  simp [digraph_incidence_matrix, hw_tail, hw_head]

/-- Definition 4.3-extra-1 (2). Every column of the incidence matrix has total sum `0`;
equivalently, the rows of the incidence matrix sum to the zero vector. -/
theorem sum_digraph_incidence_matrix_column
    (R : Type*) [AddCommGroup R] [One R]
    [Fintype V]
    (tail head : A → V)
    (e : A) :
    ∑ w, digraph_incidence_matrix R tail head w e = 0 := by
  classical
  simp [digraph_incidence_matrix, Finset.sum_sub_distrib]
