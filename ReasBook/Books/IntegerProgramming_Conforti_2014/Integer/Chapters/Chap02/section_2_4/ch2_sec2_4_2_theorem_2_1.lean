module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_theorem_2_1.MaximalCliqueConstraints

public section

namespace Matrix

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_theorem_2_1.lean.
Theorem 2.1. For a `0/1` matrix `A`, the set-packing family `S^P(A)` equals the stable-set family of
`Matrix.intersectionGraph A` if and only if it equals the binary family defined by the maximal-clique
inequalities of `Matrix.intersectionGraph A`. -/
theorem setPackingFamily_eq_stableSetFamily_iff_eq_maximalCliqueConstraintFamily
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) :
    A.setPackingFamily = (Matrix.intersectionGraph A).stableSetFamily ↔
      A.setPackingFamily =
        (Matrix.intersectionGraph A).maximalCliqueConstraintFamily := by
  -- Replace the stable-set family by the canonical maximal-clique description.
  rw [SimpleGraph.stableSetFamily_eq_maximalCliqueConstraintFamily]

end Matrix

#print axioms Matrix.setPackingFamily_eq_stableSetFamily_iff_eq_maximalCliqueConstraintFamily
