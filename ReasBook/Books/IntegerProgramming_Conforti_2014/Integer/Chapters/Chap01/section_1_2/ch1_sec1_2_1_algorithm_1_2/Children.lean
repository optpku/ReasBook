import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.Problem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

namespace MilpBranchAndBound

variable {m n p : ℕ}

/-- Helper for Algorithm 1.2: a child LP node is obtained from the parent node by intersecting it
with an explicitly witnessed family of added linear constraints on the flattened mixed space. -/
def linearConstraintChild
    (node child : Set (MixedRealPoint n p)) : Prop :=
  ∃ q : ℕ,
    ∃ A : Matrix (Fin q) (Fin (n + p)) ℝ,
      ∃ b : Fin q → ℝ,
        child = node ∩ ((Fin.appendEquiv n p).symm '' polyhedron_le_set A b)

/-- Helper for Algorithm 1.2: `linearConstraintChild` unfolds to the explicit matrix/vector
witness used to express the added linear constraints in Step 5(a). -/
theorem linearConstraintChild_iff
    (node child : Set (MixedRealPoint n p)) :
    linearConstraintChild node child ↔
      ∃ q : ℕ,
        ∃ A : Matrix (Fin q) (Fin (n + p)) ℝ,
          ∃ b : Fin q → ℝ,
            child = node ∩ ((Fin.appendEquiv n p).symm '' polyhedron_le_set A b) := by
  -- Unfold the named child predicate to recover the explicit linear-constraint witness.
  exact Iff.rfl

/-- Helper for Algorithm 1.2: the per-child branching clause can be rewritten between the named
`linearConstraintChild` predicate and the raw explicit witness tower from Step 5(a). -/
theorem forall_mem_linearConstraintChild_iff
    (node : Set (MixedRealPoint n p))
    (children : List (Set (MixedRealPoint n p))) :
    (∀ child ∈ children, linearConstraintChild node child) ↔
      (∀ child ∈ children,
        ∃ q : ℕ,
          ∃ A : Matrix (Fin q) (Fin (n + p)) ℝ,
            ∃ b : Fin q → ℝ,
              child = node ∩ ((Fin.appendEquiv n p).symm '' polyhedron_le_set A b)) := by
  -- Normalize only the per-child shape clause; the other branching data stays unchanged.
  constructor
  · intro hchild child hmem
    exact (linearConstraintChild_iff node child).1 (hchild child hmem)
  · intro hchild child hmem
    exact (linearConstraintChild_iff node child).2 (hchild child hmem)

end MilpBranchAndBound
