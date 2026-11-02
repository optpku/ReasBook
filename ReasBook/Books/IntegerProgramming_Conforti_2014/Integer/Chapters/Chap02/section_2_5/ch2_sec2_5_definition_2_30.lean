module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_30.ClauseMatrix

public section

/-- `SAT.ClauseMatrix m n` is the matrix `Matrix (Fin m) (Fin n) ℤ`, viewed as the owner
namespace for the CNF encoding API. The companion operations `hasSignedEntries`, `negativeCount`,
`rhs`, `clause`, and `toInstance` formalize the signed-entry condition, the rowwise count `n(A)`,
the right-hand side `1 - n(A)`, the clause attached to a row, and the resulting SAT instance. -/
abbrev SAT.ClauseMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ

/- Definition 2.30 [CNF as a `0, ±1` inequality system]: the source-facing owner is
`SAT.ClauseMatrix`, where `SAT.ClauseMatrix.hasSignedEntries` expresses the `0, ±1` condition,
`SAT.ClauseMatrix.clause` extracts the row clause, `SAT.ClauseMatrix.toInstance` assembles the
resulting SAT instance, and `SAT.ClauseMatrix.negativeCount` with `SAT.ClauseMatrix.rhs` gives the
source right-hand side `1 - n(A)`. The literal-membership semantics are exposed by the row-clause
bridge theorems. -/
#check SAT.ClauseMatrix

#check SAT.ClauseMatrix.hasSignedEntries
#check SAT.ClauseMatrix.clause
#check SAT.ClauseMatrix.toInstance
#check SAT.ClauseMatrix.negativeCount
#check SAT.ClauseMatrix.rhs
#check SAT.ClauseMatrix.pos_mem_clause_iff
#check SAT.ClauseMatrix.neg_mem_clause_iff
