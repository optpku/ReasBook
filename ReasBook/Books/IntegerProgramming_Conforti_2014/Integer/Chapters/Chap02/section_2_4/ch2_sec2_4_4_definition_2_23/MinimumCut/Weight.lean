module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Cuts
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Real.Basic

open scoped BigOperators

public section

namespace SimpleGraph

universe u

variable {V : Type u}

section MinimumCut

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The crossing ordered vertex pairs of the cut determined by `S`. -/
def crossingPairs (S : Finset V) : Finset (V × V) :=
  G.interedges S (SimpleGraph.cutComplement S)

/-- `crossingPairs S` is exactly `G.interedges S (cutComplement S)`. -/
theorem crossingPairs_eq_interedges
    (S : Finset V) :
    G.crossingPairs S = G.interedges S (SimpleGraph.cutComplement S) := by
  rfl

/-- The total weight of the cut determined by `S`, computed by summing the edge weights over the
crossing edges between `S` and its complement. -/
noncomputable def cutWeight (w : G.edgeSet → ℝ) (S : Finset V) : ℝ :=
  (G.crossingPairs S).sum fun uv ↦
    if h : G.Adj uv.1 uv.2 then
      w ⟨s(uv.1, uv.2), by simpa [SimpleGraph.mem_edgeSet] using h⟩
    else
      0

/-- `cutWeight G w S` expands as the sum of the edge weights over the crossing pairs in
`G.crossingPairs S`. -/
theorem cutWeight_eq_sum_interedges
    (w : G.edgeSet → ℝ) (S : Finset V) :
    G.cutWeight w S =
      (G.crossingPairs S).sum fun uv ↦
        if h : G.Adj uv.1 uv.2 then
          w ⟨s(uv.1, uv.2), by simpa [SimpleGraph.mem_edgeSet] using h⟩
        else
          0 := by
  rfl

/-- The cut determined by `S` has the same weight as the complementary cut side. -/
theorem cutWeight_compl
    (w : G.edgeSet → ℝ) (S : Finset V) :
    G.cutWeight w (SimpleGraph.cutComplement S) = G.cutWeight w S := by
  classical
  have hcompl : SimpleGraph.cutComplement (SimpleGraph.cutComplement S) = S := by
    ext v
    simp [SimpleGraph.cutComplement_eq_sdiff]
  rw [cutWeight_eq_sum_interedges, cutWeight_eq_sum_interedges]
  rw [crossingPairs_eq_interedges, crossingPairs_eq_interedges, hcompl]
  refine Finset.sum_equiv (Equiv.prodComm V V) ?_ ?_
  · intro uv
    exact G.swap_mem_interedges_iff.symm
  · intro uv huv
    by_cases hadj : G.Adj uv.1 uv.2
    · have hswap : G.Adj uv.2 uv.1 := by
        simpa [SimpleGraph.adj_comm] using hadj
      have hedge :
          (⟨s(uv.1, uv.2), by simpa [SimpleGraph.mem_edgeSet] using hadj⟩ : G.edgeSet) =
            ⟨s(uv.2, uv.1), by simpa [SimpleGraph.mem_edgeSet] using hswap⟩ := by
        apply Subtype.ext
        exact Sym2.eq_swap
      simp [Equiv.prodComm, Prod.swap, hadj, hswap, hedge]
    · have hswap : ¬ G.Adj uv.2 uv.1 := by
        simpa [SimpleGraph.adj_comm] using hadj
      simp [Equiv.prodComm, Prod.swap, hadj, hswap]

end MinimumCut

end SimpleGraph

end
