/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix

namespace Complex

/-- The scalar phase factor that splits `z : ℂ` into phase times modulus. -/
noncomputable def phaseFactor (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / ‖z‖

/-- `Complex.phaseFactor z` belongs to the scalar unitary group. -/
theorem phaseFactor_mem_unitary (z : ℂ) :
    phaseFactor z ∈ unitary ℂ := by
  by_cases hz : z = 0
  · -- In the zero case the phase factor is `1`, which is unitary.
    simp [phaseFactor, hz]
  · -- In the nonzero case `phaseFactor z = z / ‖z‖`, so the norm factors cancel.
    have hnorm : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    rw [Unitary.mem_iff_star_mul_self]
    have hphase : phaseFactor z = z / ‖z‖ := by
      simp [phaseFactor, hz]
    rw [hphase]
    rw [div_eq_mul_inv, star_mul, RCLike.star_def, map_inv₀, Complex.conj_ofReal]
    field_simp [hnorm]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using Complex.conj_mul' z

/-- Splitting `z` into its phase and modulus recovers `z`. -/
theorem phaseFactor_mul_norm (z : ℂ) :
    phaseFactor z * ‖z‖ = z := by
  by_cases hz : z = 0
  · -- The zero branch reduces to `1 * 0 = 0`.
    simp [phaseFactor, hz]
  · -- In the nonzero branch the denominator `‖z‖` cancels against the modulus factor.
    have hnorm : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    have hphase : phaseFactor z = z / ‖z‖ := by
      simp [phaseFactor, hz]
    rw [hphase]
    field_simp [hnorm]

end Complex

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal matrix of pointwise phases of `eigVals` belongs to
`Matrix.unitaryGroup n ℂ`. -/
theorem phaseDiagonal_mem_unitaryGroup (eigVals : n → ℂ) :
    diagonal (Complex.phaseFactor ∘ eigVals) ∈ unitaryGroup n ℂ := by
  -- It suffices to check the diagonal matrix has identity `star_mul_self`.
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    star (diagonal (Complex.phaseFactor ∘ eigVals)) * diagonal (Complex.phaseFactor ∘ eigVals) =
        diagonal
          (fun i ↦ star (Complex.phaseFactor (eigVals i)) * Complex.phaseFactor (eigVals i)) := by
          simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    _ = diagonal (fun _ ↦ (1 : ℂ)) := by
          congr with i
          exact Unitary.star_mul_self_of_mem (Complex.phaseFactor_mem_unitary (eigVals i))
    _ = 1 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            simp
          · simp [hij]

/-- The unitary diagonal phase correction extracted from `eigVals`. -/
noncomputable def phaseDiagonal (eigVals : n → ℂ) : unitaryGroup n ℂ :=
  ⟨diagonal (Complex.phaseFactor ∘ eigVals), phaseDiagonal_mem_unitaryGroup eigVals⟩

/-- Splitting each diagonal entry into its phase and modulus factors the diagonal matrix. -/
theorem diagonal_eq_phaseDiagonal_mul_diagonalNorm (eigVals : n → ℂ) :
    diagonal eigVals =
      phaseDiagonal eigVals * diagonal (fun i ↦ (‖eigVals i‖ : ℂ)) := by
  -- Compare diagonal entries directly after expanding the phase correction.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [phaseDiagonal, Complex.phaseFactor_mul_norm]
  · simp [phaseDiagonal, hij]

/-- Exercise 5.13. If `C` admits a unitary diagonalization, then writing each diagonal entry as
its phase times its modulus yields an SVD of `C`: the right singular vectors remain the
diagonalizing basis `U`, while the left singular vectors are obtained from `U` by the diagonal
phase correction `phaseDiagonal eigVals`. -/
theorem svdOfUnitaryDiagonalization
    (C : Matrix n n ℂ) (U : unitaryGroup n ℂ) (eigVals : n → ℂ)
    (hdiag : C = (U * diagonal eigVals) * (U : Matrix n n ℂ)ᴴ) :
    C =
      ((U * phaseDiagonal eigVals : unitaryGroup n ℂ) *
        diagonal (fun i ↦ (‖eigVals i‖ : ℂ))) *
      (U : Matrix n n ℂ)ᴴ := by
  -- Rewrite the diagonal factor into phase and modulus, then reassociate.
  calc
    C = (U * diagonal eigVals) * (U : Matrix n n ℂ)ᴴ := hdiag
    _ =
        (U * (phaseDiagonal eigVals * diagonal (fun i ↦ (‖eigVals i‖ : ℂ)))) *
          (U : Matrix n n ℂ)ᴴ := by
          rw [diagonal_eq_phaseDiagonal_mul_diagonalNorm]
    _ =
        ((U * phaseDiagonal eigVals : unitaryGroup n ℂ) *
          diagonal (fun i ↦ (‖eigVals i‖ : ℂ))) *
          (U : Matrix n n ℂ)ᴴ := by
          simp [Matrix.mul_assoc]

end Matrix
