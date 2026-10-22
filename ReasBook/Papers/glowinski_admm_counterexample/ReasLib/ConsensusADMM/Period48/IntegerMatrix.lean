/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Circulant

@[expose] public section

namespace ConsensusADMM
namespace Period48

universe u

/-- The period-48 circulant matrix whose `(i, j)` entry is `t (j - i)`. -/
def circulant {α : Type u} (t : Fin 48 → α) : Matrix (Fin 48) (Fin 48) α :=
  (Matrix.circulant t).transpose

/-- Entrywise evaluation of the period-48 circulant convention. -/
theorem circulant_apply {α : Type u} (t : Fin 48 → α) (i j : Fin 48) :
    circulant t i j = t (j - i) := by
  -- Transposition reverses Mathlib's native circulant index order.
  rfl

/-- The first explicit integer row of the period-48 block matrix. -/
def p : Fin 48 → ℤ :=
  ![37932, -3601, 27699, -4385, 9569, -3965, 1106, -2310,
    515, -1598, -1960, -2426, -4551, -3342, -2551, -4148,
    -1242, -6080, -3938, -8642, -1703, -9814, 9564, -9524,
    16733, -9524, 9564, -9814, -1703, -8642, -3938, -6080,
    -1242, -4148, -2551, -3342, -4551, -2426, -1960, -1598,
    515, -2310, 1106, -3965, 9569, -4385, 27699, -3601]

/-- The second explicit integer row of the period-48 block matrix. -/
def q : Fin 48 → ℤ :=
  ![2045401, 1165055, 1802561, 1039586, 1317523, 820868, 930843, 542553,
    616940, 226876, 223093, -101483, -158712, -413039, -396472, -688635,
    -591694, -920015, -824567, -1095956, -922689, -1205432, -794050,
    -1253193, -685312, -1253193, -794050, -1205432, -922689, -1095956,
    -824567, -920015, -591694, -688635, -396472, -413039, -158712,
    -101483, 223093, 226876, 616940, 542553, 930843, 820868, 1317523,
    1039586, 1802561, 1165055]

/-- The explicit off-diagonal integer row of the period-48 block matrix. -/
def c : Fin 48 → ℤ :=
  ![-21558, 127272, -2356, 45407, -31559, -36058, -80712, -75520,
    -102235, -91104, -104379, -102662, -113814, -97761, -116938,
    -73446, -97040, -50608, -79134, -28632, -80884, 16153, -68998,
    72263, -19755, 93154, 27907, 70734, 34675, 50022, 25229, 56179,
    36347, 65451, 52479, 61808, 47034, 62637, 35599, 74150, 34345,
    80071, 18943, 86439, -21207, 116423, -43291, 148934]

/-- The row `p` is invariant under negation at phases from 1 through 23. -/
theorem p_reflect (i : Fin 48) (one_le : 1 ≤ i.val) (le_twentyThree : i.val ≤ 23) :
    p (-i) = p i := by
  -- Enumerate the bounded phases and evaluate the displayed row at each phase.
  fin_cases i <;> decide

/-- The row `q` is invariant under negation at phases from 1 through 23. -/
theorem q_reflect (i : Fin 48) (one_le : 1 ≤ i.val) (le_twentyThree : i.val ≤ 23) :
    q (-i) = q i := by
  -- Enumerate the bounded phases and evaluate the displayed row at each phase.
  fin_cases i <;> decide

/-- The unscaled integer matrix on two blocks of 48 phases, with circulant rows
`p`, `q`, and `c`. -/
def integerMatrix : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℤ :=
  fun a b ↦
    if a.1 = 0 then
      if b.1 = 0 then circulant p a.2 b.2 else circulant c a.2 b.2
    else if b.1 = 0 then circulant c b.2 a.2 else circulant q a.2 b.2

/-- Entrywise block formula for the unscaled period-48 integer matrix. -/
theorem integerMatrix_apply (a b : Fin 2) (i j : Fin 48) :
    integerMatrix (a, i) (b, j) =
      if a = 0 then
        if b = 0 then circulant p i j else circulant c i j
      else if b = 0 then circulant c j i else circulant q i j := by
  -- Pair projections expose exactly the four block choices in the definition.
  rfl

/-- The unscaled period-48 integer matrix is symmetric. -/
theorem integerMatrix_transpose : integerMatrix.transpose = integerMatrix := by
  -- First certify negation invariance for every phase of the two diagonal rows.
  have hp : ∀ k : Fin 48, p (-k) = p k := by
    intro k
    fin_cases k <;> decide
  have hq : ∀ k : Fin 48, q (-k) = q k := by
    intro k
    fin_cases k <;> decide
  -- Entrywise extensionality leaves the four block positions; the off-diagonal
  -- pair agrees definitionally, and negation invariance closes each diagonal.
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b
  · simpa [Matrix.transpose_apply, integerMatrix_apply, circulant_apply, neg_sub] using hp (j - i)
  · simp [Matrix.transpose_apply, integerMatrix_apply]
  · simp [Matrix.transpose_apply, integerMatrix_apply]
  · simpa [Matrix.transpose_apply, integerMatrix_apply, circulant_apply, neg_sub] using hq (j - i)

end Period48
end ConsensusADMM
