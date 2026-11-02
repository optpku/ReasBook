import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

section StableSetRelaxations

variable {V : Type}
variable (G : SimpleGraph V)

/-- The edge relaxation `Q(G)` consists of the nonnegative vectors satisfying
`x_u + x_v ≤ 1` on every graph edge. -/
def edge_relaxation : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1}

notation "Q(" G ")" => edge_relaxation G

/-- Membership in `Q(G)` is exactly nonnegativity together with the edge
inequalities of `G`. -/
theorem mem_edge_relaxation_iff
    (x : V → ℝ) :
    x ∈ Q(G) ↔
      (∀ v, 0 ≤ x v) ∧ ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1 :=
  Iff.rfl

/-- The fractional stable-set relaxation `FRAC(G)` is the unit cube cut out by the graph edge
inequalities. -/
def fractional_stable_set_polytope : Set (V → ℝ) :=
  {x | (∀ v : V, 0 ≤ x v ∧ x v ≤ 1) ∧
      ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1}

notation "FRAC(" G ")" => fractional_stable_set_polytope G

/-- Membership in `FRAC(G)` is exactly the box constraints
`0 ≤ x_v ≤ 1` together with the edge inequalities of `G`. -/
theorem mem_fractional_stable_set_polytope_iff
    (x : V → ℝ) :
    x ∈ FRAC(G) ↔
      (∀ v : V, 0 ≤ x v ∧ x v ≤ 1) ∧
        ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1 :=
  Iff.rfl

/-- The clique relaxation `K(G)` consists of the nonnegative vectors satisfying every clique
inequality of `G`. -/
def clique_relaxation : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∀ K : Finset V, G.IsClique K → K.sum x ≤ 1}

notation "K(" G ")" => clique_relaxation G

/-- Membership in `K(G)` is exactly nonnegativity together with all clique
inequalities of `G`. -/
theorem mem_clique_relaxation_iff
    (x : V → ℝ) :
    x ∈ K(G) ↔
      (∀ v, 0 ≤ x v) ∧
        ∀ K : Finset V, G.IsClique K → K.sum x ≤ 1 :=
  Iff.rfl

end StableSetRelaxations
