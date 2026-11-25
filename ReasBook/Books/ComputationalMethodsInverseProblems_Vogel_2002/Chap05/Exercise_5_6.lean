/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_4
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix BigOperators

noncomputable section


/-- The Chapter 5 discrete Fourier transform as a continuous linear endomorphism of
`EuclideanSpace ℂ (Fin n)`. -/
@[expose]
noncomputable def dftToEuclideanCLM (n : ℕ) [NeZero n] :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (Matrix.fourierMatrix n)

/-- The underlying linear map of `dftToEuclideanCLM n` is `Matrix.toEuclideanLin
  (Matrix.fourierMatrix n)`. -/
@[simp] theorem dftToEuclideanCLM_toLinearMap (n : ℕ) [NeZero n] :
    (dftToEuclideanCLM n).toLinearMap = Matrix.toEuclideanLin (Matrix.fourierMatrix n) :=
  rfl

/-- Helper for Exercise 5.6: applying `dftToEuclideanCLM n` agrees with the textbook
DFT operator `Matrix.toEuclideanLin (Matrix.fourierMatrix n)`. -/
@[simp] theorem dftToEuclideanCLM_apply (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℂ (Fin n)) :
    dftToEuclideanCLM n x = Matrix.toEuclideanLin (Matrix.fourierMatrix n) x :=
  rfl

/-- The Euclidean-space operator induced by `Matrix.fourierMatrix n` is unitary. -/
theorem dftToEuclideanCLM_mem_unitary (n : ℕ) [NeZero n] :
    dftToEuclideanCLM n ∈ unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
  -- Transport the Fourier-matrix unitary witness through the
  -- Euclidean-space star algebra equivalence.
  simpa [dftToEuclideanCLM] using
    Unitary.map_mem Matrix.toEuclideanCLM (Matrix.fourierMatrix_mem_unitaryGroup n)

/-- Helper for Exercise 5.6: the DFT continuous linear map preserves Euclidean inner
products. -/
theorem dftToEuclideanCLM_inner_preserving (n : ℕ) [NeZero n]
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (dftToEuclideanCLM n x) (dftToEuclideanCLM n y) = inner ℂ x y := by
  -- Apply the standard inner-product preservation theorem to the unitary DFT operator.
  simpa using
    ContinuousLinearMap.inner_map_map_of_mem_unitary (dftToEuclideanCLM_mem_unitary n) x y

/-- Helper for Exercise 5.6: the DFT continuous linear map preserves Euclidean norms. -/
theorem dftToEuclideanCLM_norm_preserving (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖dftToEuclideanCLM n x‖ = ‖x‖ := by
  -- The same unitary witness gives norm preservation immediately.
  simpa using
    ContinuousLinearMap.norm_map_of_mem_unitary (dftToEuclideanCLM_mem_unitary n) x

/-- Exercise 5.6. The Chapter 5 discrete Fourier transform `Matrix.fourierMatrix n`
preserves the Euclidean inner product on `EuclideanSpace ℂ (Fin n)` and hence preserves
the Euclidean norm. -/
theorem dftInnerNormPreserving (n : ℕ) [NeZero n] :
    (∀ x y : EuclideanSpace ℂ (Fin n),
      inner ℂ (Matrix.toEuclideanLin (Matrix.fourierMatrix n) x)
        (Matrix.toEuclideanLin (Matrix.fourierMatrix n) y) =
        inner ℂ x y) ∧
    (∀ x : EuclideanSpace ℂ (Fin n),
      ‖Matrix.toEuclideanLin (Matrix.fourierMatrix n) x‖ = ‖x‖) := by
  constructor
  · intro x y
    -- The CLM wrapper gives the textbook inner-product identity directly.
    simpa using dftToEuclideanCLM_inner_preserving n x y
  · intro x
    -- Norm preservation follows from the same unitary DFT operator.
    simpa using dftToEuclideanCLM_norm_preserving n x

/-- First conclusion of Exercise 5.6: the Chapter 5 discrete Fourier transform
`Matrix.fourierMatrix n` preserves the Euclidean inner product on `EuclideanSpace ℂ (Fin n)`. -/
theorem dftInnerPreserving (n : ℕ) [NeZero n]
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanLin (Matrix.fourierMatrix n) x)
      (Matrix.toEuclideanLin (Matrix.fourierMatrix n) y) =
      inner ℂ x y := by
  -- Rewrite the textbook matrix operator into the CLM wrapper and reuse the helper theorem.
  simpa using dftToEuclideanCLM_inner_preserving n x y

/-- Second conclusion of Exercise 5.6: the Chapter 5 discrete Fourier transform
`Matrix.fourierMatrix n` preserves the Euclidean norm on `EuclideanSpace ℂ (Fin n)`. -/
theorem dftNormPreserving (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin (Matrix.fourierMatrix n) x‖ = ‖x‖ := by
  -- Rewrite the textbook operator into the CLM wrapper and invoke the norm helper.
  simpa using dftToEuclideanCLM_norm_preserving n x
