/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_5.MatrixFamily
public import Mathlib.Analysis.Matrix.Spectrum

open Matrix

noncomputable section

@[expose] public section

variable {m n : ℕ}

/-- The largest ordered eigenvalue of a Hermitian real matrix. -/
def largestHermitianEigenvalue {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) : ℝ :=
  hA.eigenvalues₀ ⟨0, by simpa using hn⟩

/-- Expand the largest ordered Hermitian eigenvalue to the first ordered entry. -/
@[simp] theorem largestHermitianEigenvalue_eq
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) :
    largestHermitianEigenvalue hA hn = hA.eigenvalues₀ ⟨0, by simpa using hn⟩ :=
  rfl

/-- The smallest ordered eigenvalue of a Hermitian real matrix. -/
def smallestHermitianEigenvalue {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) : ℝ :=
  hA.eigenvalues₀ ⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩

/-- Expand the smallest ordered Hermitian eigenvalue to the last ordered entry. -/
@[simp] theorem smallestHermitianEigenvalue_eq
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) :
    smallestHermitianEigenvalue hA hn =
      hA.eigenvalues₀ ⟨n - 1, by simpa using Nat.sub_lt hn (Nat.succ_pos 0)⟩ :=
  rfl

/-- The spectral condition number of a Hermitian real matrix, expressed as the ratio of its
largest and smallest ordered eigenvalues. -/
def hermitianSpectralConditionNumber {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) : ℝ :=
  largestHermitianEigenvalue hA hn / smallestHermitianEigenvalue hA hn

/-- Expand the Hermitian spectral condition number into its endpoint ratio. -/
@[simp] theorem hermitianSpectralConditionNumber_eq
    {A : MatrixN n} (hA : A.IsHermitian) (hn : 0 < n) :
    hermitianSpectralConditionNumber hA hn =
      largestHermitianEigenvalue hA hn / smallestHermitianEigenvalue hA hn :=
  rfl

/-- The spectral condition number of a positive-definite real matrix, expressed as the ratio of
its largest and smallest ordered eigenvalues. -/
def posDefSpectralConditionNumber {A : MatrixN n} (hA : A.PosDef) (hn : 0 < n) : ℝ :=
  hermitianSpectralConditionNumber hA.1 hn

/-- Expand the positive-definite spectral condition number to the Hermitian owner. -/
@[simp] theorem posDefSpectralConditionNumber_eq
    {A : MatrixN n} (hA : A.PosDef) (hn : 0 < n) :
    posDefSpectralConditionNumber hA hn = hermitianSpectralConditionNumber hA.1 hn :=
  rfl

/-- The spectral condition number of `J(x)ᵀ * J(x) + μ • D(x)` on the positive damping domain
`Set.Ioi 0`. -/
def levenbergMarquardtConditionNumber
    (J : JacobianMatrix m n) (D : MatrixN n) (hD : IsPositiveDefiniteDiagonalMatrix D)
    (hn : 0 < n) (μ : Set.Ioi (0 : ℝ)) : ℝ :=
  hermitianSpectralConditionNumber
    (levenbergMarquardtRegularizedNormalMatrix_isHermitian J D hD μ)
    hn

/-- The spectral condition number of the source family
`J(x)ᵀ * J(x) + μ • diag (diag (J(x)ᵀ * J(x)))` on `Set.Ioi 0`. -/
def sourceLevenbergMarquardtConditionNumber
    (J : JacobianMatrix m n)
    (hPos : ∀ μ : Set.Ioi (0 : ℝ),
      (sourceLevenbergMarquardtRegularizedNormalMatrix J μ.1).PosDef)
    (hn : 0 < n) (μ : Set.Ioi (0 : ℝ)) : ℝ :=
  posDefSpectralConditionNumber (hPos μ) hn

end
