/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.Recurrence

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar

/-- A factored rank-one update of a real Hermitian matrix is Hermitian. -/
private lemma factoredUpdate_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℝ) (v w : n → ℝ) (σ : ℝ) (hZ : Z.IsHermitian) :
    ((1 - σ⁻¹ • Matrix.vecMulVec w v) * Z *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w).IsHermitian := by
  -- The two rank-one factors are adjoints, so the factored term is a congruence.
  have hfactor : (1 - σ⁻¹ • Matrix.vecMulVec w v)ᴴ =
      (1 - σ⁻¹ • Matrix.vecMulVec v w : Matrix n n ℝ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_trivial]
  have hcongruence := Matrix.isHermitian_mul_mul_conjTranspose
    (1 - σ⁻¹ • Matrix.vecMulVec w v) hZ
  rw [hfactor] at hcongruence
  -- The real scalar multiple of the self-outer-product supplies a Hermitian correction.
  have houter : (Matrix.vecMulVec w w).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.vecMulVec_apply, star_trivial, mul_comm]
  exact hcongruence.add (houter.smul (IsSelfAdjoint.all _))

/-- The factored polar matrix update preserves Hermitian matrices. -/
theorem matrixStep_isHermitian (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (δ ζ ζNext : ℝ) (hZ : Z.IsHermitian) :
    (matrixStep Z δ ζ ζNext).IsHermitian := by
  -- Apply rotation congruence to the Hermitian bracket without expanding its entries.
  rw [matrixStep_def]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul (rotationMatrix δ)
      (factoredUpdate_isHermitian Z (stepVOf Z) (stepWOf Z δ ζ ζNext)
        (sigmaOf Z δ ζ ζNext) hZ)

namespace Parameters

/-- The prescribed matrix `p.initialMatrix` is Hermitian
(`DFP.Polar.matrixStep_isHermitian`). -/
private lemma initialMatrix_isHermitian (p : Parameters) : p.initialMatrix.IsHermitian := by
  -- The explicit initial matrix has equal off-diagonal entries.
  rw [initialMatrix_def]
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i
  · fin_cases j
    · rfl
    · rfl
  · fin_cases j
    · rfl
    · rfl

/-- Hermitian symmetry is preserved by the two-stage map `p.nextEvenMatrix j`
(`DFP.Polar.matrixStep_isHermitian`). -/
private lemma nextEvenMatrix_isHermitian (p : Parameters) (j : ℕ)
    {Z : Matrix (Fin 2) (Fin 2) ℝ} (hZ : Z.IsHermitian) :
    (p.nextEvenMatrix j Z).IsHermitian := by
  -- Preserve the shared odd multiplier and propagate symmetry through both stages.
  rw [nextEvenMatrix_def]
  exact matrixStep_isHermitian _ _ _ _ (matrixStep_isHermitian _ _ _ _ hZ)

/-- Every recursively prescribed even matrix is Hermitian. -/
theorem evenMatrix_isHermitian (p : Parameters) (j : ℕ) :
    (p.evenMatrix j).IsHermitian := by
  induction j with
  | zero =>
      -- Start the invariant at the prescribed symmetric initial matrix.
      simpa only [evenMatrix_zero] using initialMatrix_isHermitian p
  | succ j hZ =>
      -- One complete cycle preserves the invariant at the next even index.
      simpa only [evenMatrix_succ] using nextEvenMatrix_isHermitian p j hZ

end Parameters

end DFP.Polar
