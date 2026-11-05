/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Matrix.Basic

public section

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/-- The finite collection of all maximal cliques of a finite graph. -/
noncomputable def maximalCliques (G : SimpleGraph V) : Finset (Finset V) :=
  by
    classical
    exact Finset.univ.powerset.filter fun K ↦ Maximal G.IsClique (K : Set V)

/-- Membership in `maximalCliques G` means being a maximal clique of `G`. -/
@[simp] theorem mem_maximalCliques_iff
    (G : SimpleGraph V)
    (K : Finset V) :
    K ∈ G.maximalCliques ↔ Maximal G.IsClique (K : Set V) := by
  classical
  simp [SimpleGraph.maximalCliques]

/-- The clique matrix of a finite graph, with rows indexed by maximal cliques and entries given by
vertex membership. -/
noncomputable def cliqueMatrix (G : SimpleGraph V) :
    Matrix (G.maximalCliques) V ℤ :=
  by
    classical
    exact fun K v ↦ if v ∈ (K : Finset V) then 1 else 0

/-- Unfolding equation for `cliqueMatrix`. -/
@[simp] theorem cliqueMatrix_apply [DecidableEq V]
    (G : SimpleGraph V)
    (K : G.maximalCliques)
    (v : V) :
    G.cliqueMatrix K v = if v ∈ (K : Finset V) then 1 else 0 := by
  classical
  by_cases hv : v ∈ (K : Finset V) <;> simp [SimpleGraph.cliqueMatrix, hv]

end SimpleGraph
