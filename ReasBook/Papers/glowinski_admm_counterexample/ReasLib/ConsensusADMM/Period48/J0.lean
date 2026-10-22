/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.IntegerMatrix
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace ConsensusADMM
namespace Period48

/-- The integer matrix `2K - I₉₆` on the flat scalar coordinates of `Fin 96`,
where `K` is the period-48 two-block integer matrix. -/
def j0 : Matrix (Fin 96) (Fin 96) ℤ := fun i j ↦
  2 * integerMatrix (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) -
    if i = j then 1 else 0

/-- Entrywise evaluation of the flat integer matrix `2K - I₉₆`. -/
theorem j0_apply (i j : Fin 96) :
    j0 i j =
      2 * integerMatrix (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) -
        if i = j then 1 else 0 := by
  -- The right-hand side is the defining body of `j0`, so evaluation is
  -- definitional: `j0` is a plain function on matrix entries.
  rfl

/-- Two-block evaluation of the flat integer matrix `2K - I₉₆` on `Fin 2 × Fin 48`
coordinates. -/
theorem j0_blocks (a b : Fin 2) (i j : Fin 48) :
    j0 (finProdFinEquiv (a, i)) (finProdFinEquiv (b, j)) =
      2 * integerMatrix (a, i) (b, j) -
        (if (a, i) = (b, j) then 1 else 0) := by
  -- Evaluate `j0` at the flat index and then normalize the composite index
  -- `finProdFinEquiv.symm (finProdFinEquiv _)` back to the block coordinates;
  -- the index equivalence also transports the diagonal `if` condition.
  rw [j0_apply]
  simp only [Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq]

/-- Entrywise commutativity of the unscaled period-48 integer matrix. -/
theorem integerMatrix_apply_comm (a b : Fin 2 × Fin 48) :
    integerMatrix a b = integerMatrix b a := by
  -- The transpose equality is definitionally the symmetry predicate, whose
  -- `apply` companion is exactly the entrywise commutation we need.
  exact Matrix.IsSymm.apply (show integerMatrix.IsSymm from integerMatrix_transpose) b a

/-- The integer matrix `2K - I₉₆` is symmetric. -/
theorem j0_isSymm : j0.IsSymm := by
  -- Reduction to entries: it suffices to compare `j0 j i` with `j0 i j`.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  -- Unfold both entries; the `integerMatrix` factor is commuted by symmetry of
  -- `integerMatrix`, leaving only the two diagonal `if` conditions.
  simp only [j0]
  rw [integerMatrix_apply_comm (finProdFinEquiv.symm j) (finProdFinEquiv.symm i)]
  -- The conditions `j = i` and `i = j` agree, by cases on `i = j`.
  by_cases h : i = j
  · rw [h]
  · rw [if_neg (Ne.symm h), if_neg h]

end Period48
end ConsensusADMM
