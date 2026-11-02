import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: finite vectors over `ℕ` with the canonical mathlib dot product `⬝ᵥ`
-- * sampled owner declarations: `Matrix.dotProduct` from `Data/Matrix/Mul`,
--   `Matrix.vec3_dotProduct'` and the `![...]` vector notation from
--   `LinearAlgebra/Matrix/Notation`
-- * owner abstraction: the canonical `Fin n → α` vector literal together with `⬝ᵥ`
-- * primitive data: the explicit vectors themselves
-- * derived API: the displayed dot-product identity

/-- Exercise 9.12. The explicit nonnegative integer solution vector
`![32835, 12, 2258]` satisfies
`![243243, 244223, 243334] ⬝ᵥ x = 8539262753`. -/
theorem exercise_9_12_solution_spec :
    (![243243, 244223, 243334] : Fin 3 → ℕ) ⬝ᵥ ![32835, 12, 2258] = 8539262753 := by
  decide
