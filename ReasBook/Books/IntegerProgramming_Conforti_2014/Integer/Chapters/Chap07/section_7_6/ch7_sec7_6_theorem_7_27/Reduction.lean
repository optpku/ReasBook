import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_6.ch7_sec7_6_theorem_7_27.OracleModel

section Theorem727

variable {n : ℕ}

/-- An oracle-polynomial-time reduction from weak separation to weak optimization on the same
circumscribed convex set records the induced optimization solver together with polynomial bounds
for oracle-query size, oracle-call count, and overhead. -/
structure WeakOptimizationFromWeakSeparation
    (K : CircumscribedConvexSet n) where
  solveWithOracle : WeakSeparationSolver K → WeakOptimizationSolver K
  oracleQueryBound : Polynomial ℕ
  oracleCallBound : Polynomial ℕ
  overhead : Polynomial ℕ
  runtime_le (oracle : WeakSeparationSolver K) (query : WeakOptimizationQuery n) :
    (solveWithOracle oracle).runtime query ≤
      overhead.eval (K.weakOptimizationEncodingSize query) +
        oracleCallBound.eval (K.weakOptimizationEncodingSize query) *
          oracle.time_bound.eval
            (oracleQueryBound.eval (K.weakOptimizationEncodingSize query))

/-- The weak optimization problem for a circumscribed convex set is oracle-polynomial-time
solvable from a weak separation oracle when such a reduction owner exists. -/
abbrev HasOraclePolynomialTimeWeakOptimizationProblem
    (K : CircumscribedConvexSet n) : Prop :=
  Nonempty (WeakOptimizationFromWeakSeparation K)

/-- Expanding `HasOraclePolynomialTimeWeakOptimizationProblem K` recalls the canonical weak
optimization-from-separation reduction owner. -/
theorem hasOraclePolynomialTimeWeakOptimizationProblem_iff
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakOptimizationProblem K ↔
      Nonempty (WeakOptimizationFromWeakSeparation K) := by
  rfl

/-- An oracle-polynomial-time reduction from weak optimization to weak separation on the same
circumscribed convex set records the induced separation solver together with polynomial bounds
for oracle-query size, oracle-call count, and overhead. -/
structure WeakSeparationFromWeakOptimization
    (K : CircumscribedConvexSet n) where
  solveWithOracle : WeakOptimizationSolver K → WeakSeparationSolver K
  oracleQueryBound : Polynomial ℕ
  oracleCallBound : Polynomial ℕ
  overhead : Polynomial ℕ
  runtime_le (oracle : WeakOptimizationSolver K) (query : WeakSeparationQuery n) :
    (solveWithOracle oracle).runtime query ≤
      overhead.eval (K.weakSeparationEncodingSize query) +
        oracleCallBound.eval (K.weakSeparationEncodingSize query) *
          oracle.time_bound.eval
            (oracleQueryBound.eval (K.weakSeparationEncodingSize query))

/-- The weak separation problem for a circumscribed convex set is oracle-polynomial-time solvable
from a weak optimization oracle when such a reduction owner exists. -/
abbrev HasOraclePolynomialTimeWeakSeparationProblem
    (K : CircumscribedConvexSet n) : Prop :=
  Nonempty (WeakSeparationFromWeakOptimization K)

/-- Expanding `HasOraclePolynomialTimeWeakSeparationProblem K` recalls the canonical weak
separation-from-optimization reduction owner. -/
theorem hasOraclePolynomialTimeWeakSeparationProblem_iff
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakSeparationProblem K ↔
      Nonempty (WeakSeparationFromWeakOptimization K) := by
  rfl

end Theorem727
