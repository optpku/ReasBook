/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

/-- Helper for Exercise 5.6: the primitive Fourier root `w` used for the Chapter 5 normalized
Fourier matrix on `Fin n`. -/
@[expose] def fourierRoot (n : ℕ) [NeZero n] : ℂ :=
  ZMod.stdAddChar (-1 : ZMod n)

/-- `Matrix.fourierRoot` is the standard additive character on `ZMod n` evaluated at `-1`. -/
theorem fourierRoot_eq_stdAddChar (n : ℕ) [NeZero n] :
    Matrix.fourierRoot n = ZMod.stdAddChar (-1 : ZMod n) :=
  rfl

/-- Helper for Exercise 5.6: the Chapter 5 normalized Fourier matrix on `Fin n`. -/
@[expose] def fourierMatrix (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ Matrix.fourierRoot n ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n

/-- The entrywise formula for `Matrix.fourierMatrix`. -/
theorem fourierMatrix_apply (n : ℕ) [NeZero n] (i j : Fin n) :
    Matrix.fourierMatrix n i j =
      Matrix.fourierRoot n ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n :=
  rfl

/-- Helper for Exercise 5.6: the finite geometric sum attached to `Matrix.fourierRoot n` is `n`
at frequency `0` and vanishes at every nonzero frequency. -/
theorem fourierRoot_orthogonality (n : ℕ) [NeZero n] (k : Fin n) :
    ∑ j : Fin n, Matrix.fourierRoot n ^ ((j : ℕ) * (k : ℕ)) =
      if k = 0 then (n : ℂ) else 0 := by
  classical
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ n =>
      convert
        (AddChar.sum_mulShift (-(k : ZMod (n + 1)))
          (ZMod.isPrimitive_stdAddChar (n + 1))) using 1
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.fourierRoot_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow]
        congr 1
        rw [nsmul_eq_mul]
        change (((j : ZMod (n + 1)) * (k : ZMod (n + 1))) * (-1)) =
          (j : ZMod (n + 1)) * (-(k : ZMod (n + 1)))
        rw [← mul_neg_one (k : ZMod (n + 1)), ← mul_assoc]
      · by_cases hk : k = 0
        · subst hk
          rw [if_pos rfl]
          simp
        · have hkz : (-(k : ZMod (n + 1))) ≠ 0 := by
            intro hk0
            have : (k : ZMod (n + 1)) = 0 := by
              simpa using neg_eq_zero.mp hk0
            exact hk (by exact_mod_cast this)
          rw [if_neg hk]
          simp [hkz]

/-- Helper for Exercise 5.6: the Chapter 5 normalized Fourier matrix is unitary. -/
theorem fourierMatrix_mem_unitaryGroup (n : ℕ) [NeZero n] :
    Matrix.fourierMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  cases n with
  | zero =>
      cases NeZero.ne 0 rfl
  | succ n =>
      let t : ZMod (n + 1) := (((i : ℕ) : ZMod (n + 1))) - (((j : ℕ) : ZMod (n + 1)))
      have hsqrtR : Real.sqrt (n + 1) ≠ 0 := by
        exact Real.sqrt_ne_zero'.2 (by positivity : 0 < (n + 1 : ℝ))
      have hsqrtC : (Real.sqrt (n + 1) : ℂ) ≠ 0 := by
        exact_mod_cast hsqrtR
      have hsq : ((Real.sqrt (n + 1) : ℂ) * Real.sqrt (n + 1)) = (n + 1 : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
      have hinv :
          ((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹ = ((n + 1 : ℂ)⁻¹) := by
        simpa [mul_inv_rev] using congrArg Inv.inv hsq
      have hconj (a : ZMod (n + 1)) : star (ZMod.stdAddChar (-a)) = ZMod.stdAddChar a := by
        rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
        calc
          star (((ZMod.toCircle (-a) : Circle) : ℂ)) = (((ZMod.toCircle (-a) : Circle) : ℂ))⁻¹ := by
            simpa using (Circle.coe_inv_eq_conj (ZMod.toCircle (-a))).symm
          _ = ((ZMod.toCircle a : Circle) : ℂ) := by
            rw [show ZMod.toCircle (-a) = (ZMod.toCircle a)⁻¹ by
              simpa using AddChar.map_neg_eq_inv (ZMod.toCircle (N := n + 1)) a]
            simp
      have hterm (k : Fin (n + 1)) :
          star (Matrix.fourierMatrix (n + 1) k i) * Matrix.fourierMatrix (n + 1) k j =
            ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) := by
        suffices
            ZMod.stdAddChar 1 ^ ((k : ℕ) * (i : ℕ)) *
                (Real.sqrt (n + 1) : ℂ)⁻¹ *
                (ZMod.stdAddChar (-1) ^ ((k : ℕ) * (j : ℕ)) * (Real.sqrt (n + 1) : ℂ)⁻¹) =
              ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) by
          simpa [Matrix.fourierMatrix, Matrix.fourierRoot_eq_stdAddChar, hconj, div_eq_mul_inv]
        rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow]
        rw [nsmul_eq_mul, nsmul_eq_mul]
        have hmul :
            ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) *
                (Real.sqrt (n + 1) : ℂ)⁻¹ *
                (ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) *
                  (Real.sqrt (n + 1) : ℂ)⁻¹) =
              (((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹) *
                (ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) *
                  ZMod.stdAddChar
                    ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1)))) := by
          ring
        have harg :
            ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) +
                ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) =
              (((k : ℕ) : ZMod (n + 1)) * t) := by
          have harg0 :
              ((((k : ℕ) : ZMod (n + 1)) * (((i : ℕ) : ZMod (n + 1))) * 1)) +
                  ((((k : ℕ) : ZMod (n + 1)) * (((j : ℕ) : ZMod (n + 1))) * (-1))) =
                (((k : ℕ) : ZMod (n + 1)) *
                  ((((i : ℕ) : ZMod (n + 1))) - (((j : ℕ) : ZMod (n + 1))))) := by
            ring
          simpa [t] using harg0
        have hmul' :
            ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                (Real.sqrt (n + 1) : ℂ)⁻¹ *
                (ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1)) *
                  (Real.sqrt (n + 1) : ℂ)⁻¹) =
              (((Real.sqrt (n + 1) : ℂ)⁻¹) * (Real.sqrt (n + 1) : ℂ)⁻¹) *
                (ZMod.stdAddChar (((((k : ℕ) * (i : ℕ)) : ℕ) : ZMod (n + 1)) * 1) *
                  ZMod.stdAddChar (((((k : ℕ) * (j : ℕ)) : ℕ) : ZMod (n + 1)) * (-1))) := by
          simpa using hmul
        rw [hmul', hinv, ← AddChar.map_add_eq_mul]
        exact congrArg
          (fun z : ZMod (n + 1) ↦ ((n + 1 : ℂ)⁻¹) * ZMod.stdAddChar z)
          (by simpa [Nat.cast_mul] using harg)
      have hsum :
          ∑ k : Fin (n + 1), ZMod.stdAddChar ((((k : ℕ) : ZMod (n + 1)) * t)) =
            if t = 0 then (n + 1 : ℂ) else 0 := by
        convert (AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar (n + 1))) using 1
        · refine Finset.sum_congr rfl fun k _ ↦ ?_
          have hk : ((k : ℕ) : ZMod (n + 1)) = (k : ZMod (n + 1)) := by
            exact ZMod.natCast_zmod_val (a := (show ZMod (n + 1) from k))
          exact congrArg (fun z : ZMod (n + 1) ↦ ZMod.stdAddChar (z * t)) hk
        · by_cases ht0 : t = 0
          · simp [ht0]
          · simp [ht0]
      have ht0 : t = 0 ↔ i = j := by
        constructor
        · intro ht
          have hz : (((i : ℕ) : ZMod (n + 1))) - (((j : ℕ) : ZMod (n + 1)) : ZMod (n + 1)) = 0 := by
            simpa [t] using ht
          have hmod : (i : ℕ) % (n + 1) = (j : ℕ) % (n + 1) := by
            exact (ZMod.natCast_eq_natCast_iff' (i : ℕ) (j : ℕ) (n + 1)).mp (sub_eq_zero.mp hz)
          have hval : (i : ℕ) = (j : ℕ) := by
            rwa [Nat.mod_eq_of_lt i.is_lt, Nat.mod_eq_of_lt j.is_lt] at hmod
          exact Fin.ext hval
        · intro hij
          subst hij
          simp [t]
      rw [Matrix.mul_apply]
      simp_rw [Matrix.star_apply, hterm]
      rw [← Finset.mul_sum, hsum, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos (ht0.mpr hij)]
        have hcard : (n + 1 : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        field_simp [hcard]
      · rw [if_neg hij, if_neg (mt ht0.mp hij)]
        simp

end Matrix

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
