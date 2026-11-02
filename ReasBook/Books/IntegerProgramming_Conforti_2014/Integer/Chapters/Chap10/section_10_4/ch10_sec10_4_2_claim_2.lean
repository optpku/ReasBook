import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain sampling for this claim:
-- * primary domain: positive semidefinite real matrices
-- * core/canonical owner: `Matrix.PosSemidef`
-- * inspected upstream derived API: `Matrix.PosSemidef.smul`, `Matrix.PosSemidef.submatrix`,
--   `Matrix.PosSemidef.det_nonneg`
-- * source-facing content kept here: the two Claim 2 scalar-rescaling consequences

section Claim2

variable {m : ℕ}

namespace Matrix.PosSemidef

/-- A matrix equal to a nonnegative scalar multiple of a positive semidefinite matrix is positive
semidefinite. -/
theorem of_eq_smul_nonneg
    {a : ℝ}
    {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A = a • B)
    (ha : 0 ≤ a)
    (hB : B.PosSemidef) :
    A.PosSemidef := by
  rw [hA]
  exact hB.smul ha

end Matrix.PosSemidef

/-- Claim 2 (1). If `M_t(bar y)` is the scalar multiple `yhat_h⁻¹ • barW` of a positive
semidefinite matrix `barW`, and `yhat_h` is nonnegative, then `M_t(bar y)` is positive
semidefinite. -/
theorem claim_2_bar_momentMatrix_posSemidef
    (yhat_h : ℝ)
    (Mbar barW : Matrix (Fin m) (Fin m) ℝ)
    (hyhat : 0 ≤ yhat_h)
    (hMbar : Mbar = yhat_h⁻¹ • barW)
    (hbarW : barW.PosSemidef) :
    Mbar.PosSemidef := by
  exact Matrix.PosSemidef.of_eq_smul_nonneg hMbar (inv_nonneg.mpr hyhat) hbarW

/-- Claim 2 (2). If `M_t(tilde y)` is the scalar multiple `(1 - yhat_h)⁻¹ • tildeW` of a positive
semidefinite matrix `tildeW`, and `yhat_h ≤ 1`, then `M_t(tilde y)` is positive semidefinite. -/
theorem claim_2_tilde_momentMatrix_posSemidef
    (yhat_h : ℝ)
    (Mtilde tildeW : Matrix (Fin m) (Fin m) ℝ)
    (hyhat : yhat_h ≤ 1)
    (hMtilde : Mtilde = (1 - yhat_h)⁻¹ • tildeW)
    (htildeW : tildeW.PosSemidef) :
    Mtilde.PosSemidef := by
  exact Matrix.PosSemidef.of_eq_smul_nonneg
    hMtilde
    (inv_nonneg.mpr (sub_nonneg.mpr hyhat))
    htildeW

end Claim2
