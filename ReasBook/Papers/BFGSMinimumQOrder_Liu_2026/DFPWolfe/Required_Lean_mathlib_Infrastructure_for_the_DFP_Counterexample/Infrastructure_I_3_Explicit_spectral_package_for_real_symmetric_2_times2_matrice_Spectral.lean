/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_3_Explicit_spectral_package_for_real_symmetric_2_times2_matrice_Spectral.lean
-/

module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2

/- The explicit low vector satisfies the low-eigenvalue equation for every real symmetric
`2 × 2` matrix. -/
#check (RealSymmetric2.lowVector_eigen : ∀ a b d : ℝ,
  (Matrix.toEuclideanCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (RealSymmetric2.matrix a b d) (RealSymmetric2.lowVector a b d) =
    RealSymmetric2.low a b d • RealSymmetric2.lowVector a b d)
