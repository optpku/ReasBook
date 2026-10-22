/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_41

open SimpleGraph

universe u

variable {Ω : Type u} {d : ℕ}

private def latticeAdj (d : ℕ) (x y : LatticePoint d) : Prop :=
  ∃ i : Fin d, Int.natAbs (x i - y i) = 1 ∧ ∀ j : Fin d, j ≠ i → x j = y j

private theorem latticeAdj_symm (d : ℕ) : Symmetric (latticeAdj d) := by
  intro x y hxy
  rcases hxy with ⟨i, hi, hxy⟩
  refine ⟨i, ?_, ?_⟩
  · have hneg : y i - x i = -(x i - y i) := by omega
    rw [hneg, Int.natAbs_neg]
    exact hi
  · intro j hj
    exact (hxy j hj).symm

private theorem latticeAdj_irrefl (d : ℕ) : Std.Irrefl (latticeAdj d) := by
  exact ⟨fun x ↦ by
    rintro ⟨i, hi, _⟩
    simp at hi⟩

/-- The nearest-neighbor graph on `ℤ^d`. Two lattice sites are adjacent exactly when they differ
by `1` in one coordinate and agree in all others. -/
def latticeGraph (d : ℕ) : SimpleGraph (LatticePoint d) where
  Adj := latticeAdj d
  symm := latticeAdj_symm d
  loopless := latticeAdj_irrefl d

/-- Adjacency in `latticeGraph d` is the nearest-neighbour relation on `ℤ^d`. -/
theorem latticeGraph_adj_iff (x y : LatticePoint d) :
    (latticeGraph d).Adj x y ↔
      ∃ i : Fin d, Int.natAbs (x i - y i) = 1 ∧ ∀ j : Fin d, j ≠ i → x j = y j :=
  Iff.rfl

/-- The open subgraph determined by a random set of lattice bonds. Intersecting with the edge set
of `latticeGraph d` keeps the construction pointwise faithful to bond percolation on `ℤ^d`. -/
def openBondGraph
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) : Ω → SimpleGraph (LatticePoint d) :=
  fun ω ↦ fromEdgeSet (openEdges ω ∩ (latticeGraph d).edgeSet)

/-- The connection event for bond percolation on `ℤ^d`: two sites are connected exactly when they
lie in the same connected component of the corresponding open subgraph. -/
def bondConnectionEvent
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) :
    LatticePoint d → LatticePoint d → Set Ω :=
  fun x y ↦ {ω | (openBondGraph openEdges ω).Reachable x y}

/-- The bond-percolation connection event is reachability in the open subgraph. -/
theorem bondConnectionEvent_eq_reachable
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) (x y : LatticePoint d) :
    bondConnectionEvent openEdges x y =
      {ω | (openBondGraph openEdges ω).Reachable x y} :=
  rfl
