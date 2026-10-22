/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Prod

public section

namespace Matrix

/-- Helper for Exercise 5.31: the interior `n_y × n_x` path-product grid graph shared by the
Dirichlet and Neumann discrete Laplacians. -/
abbrev gridGraph (n_x n_y : ℕ) : SimpleGraph (Fin n_y × Fin n_x) :=
  SimpleGraph.pathGraph n_y □ SimpleGraph.pathGraph n_x

/-- Helper for Exercise 5.31: adjacency on finite path graphs is decidable. -/
noncomputable instance instDecidableRelPathGraphAdj (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := by
  classical
  infer_instance

/-- Helper for Exercise 5.31: adjacency on the product grid graph is decidable. -/
noncomputable instance instDecidableRelGridGraphAdj (n_x n_y : ℕ) :
    DecidableRel (gridGraph n_x n_y).Adj := by
  classical
  infer_instance

/-- Helper for Exercise 5.31: the degree of a fixed vertex is independent of which finitely-many
neighbors witness the same neighbor-set type. -/
theorem degree_eq_of_neighborFintype {V : Type*} (G : SimpleGraph V) (v : V)
    (inst₁ inst₂ : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v inst₁ = @SimpleGraph.degree V G v inst₂ := by
  calc
    @SimpleGraph.degree V G v inst₁ = @Fintype.card (G.neighborSet v) inst₁ := by
      exact (@SimpleGraph.card_neighborSet_eq_degree V G v inst₁).symm
    _ = @Fintype.card (G.neighborSet v) inst₂ := by
      exact @Fintype.card_congr (G.neighborSet v) (G.neighborSet v) inst₁ inst₂ (Equiv.refl _)
    _ = @SimpleGraph.degree V G v inst₂ := by
      exact @SimpleGraph.card_neighborSet_eq_degree V G v inst₂

/-- Helper for Exercise 5.31: the degree of the product grid graph splits as the sum of the two
path-graph degrees. -/
theorem gridGraph_degree_boxProd (n_x n_y : ℕ) (j : Fin n_y) (i : Fin n_x) :
    (gridGraph n_x n_y).degree (j, i) =
      (SimpleGraph.pathGraph n_y).degree j + (SimpleGraph.pathGraph n_x).degree i := by
  simpa [gridGraph] using
    (SimpleGraph.degree_boxProd
      (G := SimpleGraph.pathGraph n_y)
      (H := SimpleGraph.pathGraph n_x)
      (x := (j, i)))

/-- Helper for Exercise 5.31: the product grid graph is connected when both side lengths are
positive. -/
theorem gridGraph_connected {n_x n_y : ℕ} (h_x : 0 < n_x) (h_y : 0 < n_y) :
    (gridGraph n_x n_y).Connected := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_x) with ⟨m, rfl⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_y) with ⟨n, rfl⟩
  exact (SimpleGraph.connected_boxProd).2
    ⟨SimpleGraph.pathGraph_connected n, SimpleGraph.pathGraph_connected m⟩

end Matrix
