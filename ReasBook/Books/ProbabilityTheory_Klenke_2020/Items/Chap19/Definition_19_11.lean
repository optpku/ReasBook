/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

open scoped ENNReal

universe u

attribute [local instance] Classical.propDecidable

noncomputable section

namespace ProbabilityTheory

variable {E : Type u}

/-- The total outgoing conductance of the weight family `C` at the state `x`. -/
def conductance (C : E → E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∑' y : E, C x y

/-- Definition 19.11: a transition matrix `p` is the random walk on `E` with weights `C` when
`C` is symmetric and the transition probabilities are given by the normalization formula
`p (x, y) = C (x, y) / C (x)` from Example 19.10. The textbook finiteness condition on each
total conductance `C (x)` is recovered below from these axioms together with stochasticity. -/
class IsRandomWalkWithWeights (p C : E → E → ℝ≥0∞) : Prop where
  /-- The transition matrix is stochastic in the sense of Definition 17.16. -/
  isStochastic : IsStochasticMatrix p
  /-- The conductance weights are symmetric. -/
  symmetric : ∀ x y : E, C x y = C y x
  /-- The transition matrix is obtained by normalizing the conductances rowwise. -/
  transition_eq : ∀ x y : E, p x y = C x y / conductance C x

/-- A random walk with weights has a stochastic transition matrix. -/
theorem IsRandomWalkWithWeights.isStochasticMatrix
    {p C : E → E → ℝ≥0∞} (h : IsRandomWalkWithWeights p C) :
    IsStochasticMatrix p :=
  h.isStochastic

-- Proof sketch: if `conductance C x = ∞`, then `transition_eq` forces every entry in the `x`-row
-- of `p` to vanish, so its row sum is `0`, contradicting the stochasticity condition
-- `∑' y, p x y = 1`.
/-- In a random walk with weights, each total conductance is automatically finite. -/
theorem IsRandomWalkWithWeights.conductance_lt_top
    {p C : E → E → ℝ≥0∞} (h : IsRandomWalkWithWeights p C) (x : E) :
    conductance C x < ∞ := by
  rw [lt_top_iff_ne_top]
  intro hx
  have hp_zero : ∀ y : E, p x y = 0 := by
    intro y
    rw [h.transition_eq, hx]
    simp
  have hsum_zero : ∑' y : E, p x y = 0 := by
    simp [hp_zero]
  have hstochastic := h.isStochastic x
  rw [hsum_zero] at hstochastic
  simp at hstochastic

/-- The unit conductance family attached to a simple graph: adjacent vertices carry weight `1`,
and nonadjacent vertices carry weight `0`. -/
def simpleGraphWeights (G : SimpleGraph E) : E → E → ℝ≥0∞ :=
  fun x y ↦ if G.Adj x y then 1 else 0

-- Proof sketch: use symmetry of adjacency in a simple graph to rewrite
-- `G.Adj x y ↔ G.Adj y x`, then both indicator-style cases coincide.
/-- The unit edge weights of a simple graph are symmetric. -/
theorem simpleGraphWeights_symmetric (G : SimpleGraph E) :
    ∀ x y : E, simpleGraphWeights G x y = simpleGraphWeights G y x := by
  intro x y
  -- Rewrite the reversed adjacency test using symmetry of edges in a simple graph.
  -- Once both `if` conditions agree, the two weight expressions are definitionally identical.
  simp [simpleGraphWeights, G.adj_comm x y]

/-- A transition matrix is a simple random walk on `(E, K)` when its weights are the indicator of
the edge relation of the graph. -/
abbrev IsSimpleRandomWalk (p : E → E → ℝ≥0∞) (G : SimpleGraph E) : Prop :=
  IsRandomWalkWithWeights p (simpleGraphWeights G)

end ProbabilityTheory
