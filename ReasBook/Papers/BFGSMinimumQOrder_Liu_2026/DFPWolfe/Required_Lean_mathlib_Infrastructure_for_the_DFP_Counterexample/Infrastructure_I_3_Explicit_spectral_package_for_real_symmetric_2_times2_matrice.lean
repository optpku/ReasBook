module

public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_1_Euclidean_gradient_Hessian_and_matrix_operator_bridge
public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2

/- Infrastructure I.3 (Explicit spectral package for real symmetric $2\times2$ matrices) (1):
the symmetric matrix, spectral gap, ordered eigenvalues, and explicit normalization data. -/
#check (RealSymmetric2.matrix : ℝ → ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
#check (RealSymmetric2.gap : ℝ → ℝ → ℝ → ℝ)
#check (RealSymmetric2.low : ℝ → ℝ → ℝ → ℝ)
#check (RealSymmetric2.high : ℝ → ℝ → ℝ → ℝ)
#check (RealSymmetric2.lowRaw : ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2))
#check (RealSymmetric2.lowDenom : ℝ → ℝ → ℝ → ℝ)

/- Infrastructure I.3 (Explicit spectral package for real symmetric $2\times2$ matrices) (2):
Hermitianity, Vieta identities, and identification with the ordered Hermitian spectrum. -/
#check RealSymmetric2.matrix_isHermitian
#check RealSymmetric2.gap_sq
#check RealSymmetric2.low_add_high
#check RealSymmetric2.low_mul_high
#check RealSymmetric2.eigenvalues_zero
#check RealSymmetric2.eigenvalues_one

/- Infrastructure I.3 (Explicit spectral package for real symmetric $2\times2$ matrices) (3):
ordering and algebraic simplicity when the spectral gap is positive. -/
#check RealSymmetric2.low_le_high
#check RealSymmetric2.low_lt_high_iff_gap_pos
#check RealSymmetric2.low_ne_high
#check RealSymmetric2.rootMultiplicity_low
#check RealSymmetric2.rootMultiplicity_high

/- Infrastructure I.3 (Explicit spectral package for real symmetric $2\times2$ matrices) (4):
the explicit oriented eigenframe, eigenvalue equations, normalization, and orthogonality. -/
#check (RealSymmetric2.lowVector : ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2))
#check (RealSymmetric2.highVector : ℝ → ℝ → ℝ → EuclideanSpace ℝ (Fin 2))
#check RealSymmetric2.lowDenom_eq_norm_lowRaw
#check RealSymmetric2.lowVector_eigen
#check RealSymmetric2.lowVector_hasEigenvector
#check RealSymmetric2.norm_lowVector
#check RealSymmetric2.firstCoordinate_lowVector_pos
#check RealSymmetric2.highVector_eigen
#check RealSymmetric2.norm_highVector
#check RealSymmetric2.inner_lowVector_highVector

/- Infrastructure I.3 (Explicit spectral package for real symmetric $2\times2$ matrices) (5):
the analytic eigenframe chart containing `matrix 0 0 1` and its standard-basis value. -/
#check (RealSymmetric2.lowChart : Set (ℝ × ℝ × ℝ))
#check RealSymmetric2.mem_lowChart
#check RealSymmetric2.isOpen_lowChart
#check RealSymmetric2.diag_mem_lowChart
#check RealSymmetric2.analyticOnNhd_gap
#check RealSymmetric2.analyticOnNhd_low
#check RealSymmetric2.analyticOnNhd_high
#check RealSymmetric2.analyticOnNhd_lowVector
#check RealSymmetric2.analyticOnNhd_highVector
#check RealSymmetric2.lowVector_diag
