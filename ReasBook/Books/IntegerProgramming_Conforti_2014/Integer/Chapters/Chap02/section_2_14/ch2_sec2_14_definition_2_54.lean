/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

/-- Definition 2.54 (Interference graph). For a frequency-assignment instance with transmitters
represented by `Fin n`, `interferenceGraph interferes` is the undirected graph on those
transmitters, with an edge exactly when the two transmitters interfere. -/
def interferenceGraph {n : ℕ} (interferes : Fin n → Fin n → Prop) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel interferes

/-- Two transmitters are adjacent in `interferenceGraph` exactly when they are distinct and the
interference relation holds in at least one order. -/
theorem interferenceGraph_adj_iff
    {n : ℕ} {interferes : Fin n → Fin n → Prop} {i j : Fin n} :
    (interferenceGraph interferes).Adj i j ↔ i ≠ j ∧ (interferes i j ∨ interferes j i) := by
  -- Unfold the project definition and use the canonical adjacency formula for `fromRel`.
  simpa only [interferenceGraph] using SimpleGraph.fromRel_adj interferes i j

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_54.lean.
If the interference relation is symmetric, adjacency in `interferenceGraph` is exactly
interference between distinct transmitters. -/
theorem interferenceGraph_adj_iff_of_symmetric
    {n : ℕ} {interferes : Fin n → Fin n → Prop} (h_symm : Symmetric interferes) {i j : Fin n} :
    (interferenceGraph interferes).Adj i j ↔ i ≠ j ∧ interferes i j := by
  -- Normalize adjacency, then use symmetry to fold the reverse interference case forward.
  rw [interferenceGraph_adj_iff]
  constructor
  · rintro ⟨hne, hij | hji⟩
    · exact ⟨hne, hij⟩
    · exact ⟨hne, h_symm hji⟩
  · rintro ⟨hne, hij⟩
    exact ⟨hne, Or.inl hij⟩

end
