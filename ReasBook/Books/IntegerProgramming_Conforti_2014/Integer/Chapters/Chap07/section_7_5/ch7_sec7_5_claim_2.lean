import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_definition_3_16_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_26

open WithLp
open scoped Polar

section Claim2

variable {n : ℕ}

/-- The rational query vector `π` viewed as a point of `ℝ^n`. -/
def rationalLinearQueryPoint (π : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 fun i ↦ (π i : ℝ)

/-- The real linear objective defined by the rational coefficient vector `π` on `ℝ^n`. -/
def rationalLinearObjective
    (π : Fin n → ℚ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  rationalLinearQueryPoint π ⬝ᵥ x

/-- Expanding `rationalLinearObjective` yields the dot product with the coerced rational vector.
-/
theorem rationalLinearObjective_eq_dotProduct
    (π : Fin n → ℚ) (x : EuclideanSpace ℝ (Fin n)) :
    rationalLinearObjective π x = rationalLinearQueryPoint π ⬝ᵥ x := by
  rfl

/-- Membership of the rational query point `π` in the polar `P*` is the textbook inequality
`π · x ≤ 1` for all `x ∈ P`. -/
theorem rationalLinearQueryPoint_mem_polar_iff
    (P : Set (EuclideanSpace ℝ (Fin n))) (π : Fin n → ℚ) :
    rationalLinearQueryPoint π ∈ P* ↔
      ∀ x ∈ P, rationalLinearObjective π x ≤ 1 := by
  simpa [rationalLinearObjective, rationalLinearQueryPoint] using
    Set.mem_polar_iff_dotProduct P (rationalLinearQueryPoint π)

/-- A solution to the rational linear optimization query `π` over `P` consists of a feasible point
whose objective value dominates every other feasible point. -/
structure RationalLinearOptimizationSolution
    (P : Set (EuclideanSpace ℝ (Fin n))) (π : Fin n → ℚ) where
  point : EuclideanSpace ℝ (Fin n)
  point_mem : point ∈ P
  is_optimal {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ P → rationalLinearObjective π x ≤ rationalLinearObjective π point

/-- A polynomial-time optimization solver for `P` answers each rational objective query with an
optimal point, together with a polynomial runtime bound in the query encoding size. -/
abbrev PolynomialTimeOptimizationSolver (P : Set (EuclideanSpace ℝ (Fin n))) :=
  PolynomialTimeQuerySolver
    (Fin n → ℚ)
    (fun π ↦ RationalLinearOptimizationSolution P π)
    EncodingSize.rationalVector

/-- The point produced by a polynomial-time optimization solver lies in the feasible region. -/
theorem optimization_solver_apply_mem {P : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeOptimizationSolver P) (π : Fin n → ℚ) :
    (solver π).point ∈ P :=
  (solver π).point_mem

/-- The point produced by a polynomial-time optimization solver is optimal for the queried
rational objective over `P`. -/
theorem optimization_solver_is_optimal {P : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeOptimizationSolver P) (π : Fin n → ℚ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ P) :
    rationalLinearObjective π x ≤ rationalLinearObjective π (solver π).point :=
  (solver π).is_optimal hx

/-- The runtime recorded by a polynomial-time optimization solver is bounded by its polynomial
time bound evaluated on the query encoding size. -/
theorem optimization_solver_runtime_le {P : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeOptimizationSolver P) (π : Fin n → ℚ) :
    solver.runtime π ≤ solver.time_bound.eval (EncodingSize.rationalVector π) :=
  PolynomialTimeQuerySolver.runtime_le_eval solver π

/-- A separation result for a query `π` is either a proof that the query point lies in `S` or a
valid inequality `c ⬝ᵥ y ≤ 1` for `S` that is violated by `π`. -/
inductive SeparationResult (S : Set (EuclideanSpace ℝ (Fin n))) (π : Fin n → ℚ) : Type
  | inside (hmem : rationalLinearQueryPoint π ∈ S) : SeparationResult S π
  | cut (c : EuclideanSpace ℝ (Fin n))
      (hvalid : ∀ y ∈ S, c ⬝ᵥ y ≤ 1)
      (hseparates : 1 < c ⬝ᵥ rationalLinearQueryPoint π) : SeparationResult S π

/-- A polynomial-time separation solver for `S` answers each rational query by either certifying
membership or returning a separating inequality, together with a polynomial runtime bound in the
query encoding size. -/
abbrev PolynomialTimeSeparationSolver (S : Set (EuclideanSpace ℝ (Fin n))) :=
  PolynomialTimeQuerySolver
    (Fin n → ℚ)
    (fun π ↦ SeparationResult S π)
    EncodingSize.rationalVector

/-- The runtime recorded by a polynomial-time separation solver is bounded by its polynomial time
bound evaluated on the query encoding size. -/
theorem separation_solver_runtime_le {S : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeSeparationSolver S) (π : Fin n → ℚ) :
    solver.runtime π ≤ solver.time_bound.eval (EncodingSize.rationalVector π) :=
  PolynomialTimeQuerySolver.runtime_le_eval solver π

/-- From an optimization solver on `P`, one obtains a polynomial-time separation solver for the
polar `P*`. -/
noncomputable def separationSolverOnPolarOfOptimizationSolver
    {P : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeOptimizationSolver P) :
    PolynomialTimeSeparationSolver (P*) where
  solve π :=
    if hinside : rationalLinearObjective π (solver π).point ≤ 1 then
      SeparationResult.inside <| by
        rw [rationalLinearQueryPoint_mem_polar_iff]
        intro x hx
        exact le_trans (optimization_solver_is_optimal solver π hx) hinside
    else
      SeparationResult.cut (solver π).point
        (by
          intro y hy
          have hy' := (Set.mem_polar_iff_dotProduct P y).1 hy (solver π).point
            (optimization_solver_apply_mem solver π)
          simpa [dotProduct_comm] using hy')
        (by
          have hseparates : 1 < rationalLinearObjective π (solver π).point :=
            lt_of_not_ge hinside
          simpa [rationalLinearObjective, dotProduct_comm] using hseparates)
  runtime := solver.runtime
  time_bound := solver.time_bound
  runtime_le := solver.runtime_le

/-- From an optimization solver on `P`, one obtains polynomial-time separability of the
polar `P*`. -/
theorem nonempty_separation_solver_on_polar_of_optimization_solver
    {P : Set (EuclideanSpace ℝ (Fin n))}
    (solver : PolynomialTimeOptimizationSolver P) :
    Nonempty (PolynomialTimeSeparationSolver (P*)) := by
  exact ⟨separationSolverOnPolarOfOptimizationSolver solver⟩

/-- Claim 2: If Optimization can be solved in polynomial time on `P`, then Separation can be
solved in polynomial time on its polar `P*`. -/
theorem optimization_polynomial_time_implies_separation_polynomial_time_on_polar
    {P : Set (EuclideanSpace ℝ (Fin n))} :
    Nonempty (PolynomialTimeOptimizationSolver P) →
      Nonempty (PolynomialTimeSeparationSolver (P*)) := by
  intro hopt
  rcases hopt with ⟨solver⟩
  exact ⟨separationSolverOnPolarOfOptimizationSolver solver⟩

end Claim2
