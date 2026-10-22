/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Matrix.Hermitian

-- Semantic recall: `ContinuousLinearMap.rayleighQuotient` in
-- `Mathlib.Analysis.InnerProductSpace.Rayleigh` is the Euclidean-space analogue. The declaration
-- below keeps the source's matrix-side complex quotient as the primary API.

/-- Chapter01 Definition 1.2.9: the matrix-side complex Rayleigh quotient is the quotient
`uᴴ A u / uᴴ u`, written in coordinates as
`(dotProduct (star u) (A.mulVec u)) / dotProduct (star u) u`.
The source's Hermitian and nonzero hypotheses are companion theorem assumptions rather than data of
the quotient itself. -/
noncomputable def rayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) : ℂ :=
  dotProduct (star u) (A.mulVec u) / dotProduct (star u) u

/-- Expands the matrix Rayleigh quotient as the quotient `uᴴ A u / uᴴ u`. -/
@[simp] theorem rayleighQuotient_def {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    rayleighQuotient A u =
      dotProduct (star u) (A.mulVec u) / dotProduct (star u) u := rfl

/-- For a Hermitian matrix, the matrix Rayleigh quotient has zero imaginary part. -/
theorem rayleighQuotient_im_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (u : Fin n → ℂ) :
    RCLike.im (rayleighQuotient A u) = 0 := by
  change Complex.im (dotProduct (star u) (A.mulVec u) / dotProduct (star u) u) = 0
  rw [Complex.div_im]
  have hnum_im : Complex.im (dotProduct (star u) (A.mulVec u)) = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self u
  have hden_im : Complex.im (dotProduct (star u) u) = 0 := by
    apply Complex.conj_eq_iff_im.mp
    simpa using (Matrix.star_dotProduct u u).symm
  rw [hnum_im, hden_im]
  simp

/-- For a Hermitian matrix, the matrix-side complex quotient is the complex coercion of the
real part of that quotient. -/
theorem rayleighQuotient_eq_ofReal_re {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (u : Fin n → ℂ) :
    rayleighQuotient A u = (Complex.re (rayleighQuotient A u) : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using rayleighQuotient_im_eq_zero A hA u
