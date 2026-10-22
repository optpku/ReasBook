/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3.EnergyNorm
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum

public section

noncomputable section

open scoped Matrix.Energy

namespace Matrix

universe u

section CoreChecks

variable {n : Type u} [Fintype n] [DecidableEq n]

/- Definition 3.3 (1). The source `A`-inner product is realized by the canonical
induced structure `Matrix.toInnerProductSpace` for `hA : A.PosSemidef`, and for
`hA : A.PosDef` the source `A`-norm is realized by `Matrix.toNormedAddCommGroup`;
the source-facing bridge names are `Matrix.energyInner` and `Matrix.energyNorm`. -/
#check Matrix.toInnerProductSpace
#check Matrix.toNormedAddCommGroup
#check Matrix.energyInner
#check Matrix.energyNorm

end CoreChecks

section Bounds

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Definition 3.3 (2). For a positive-definite real matrix, the energy norm is
bounded below by the Euclidean norm scaled by the square root of the smallest
spectral value. -/
theorem energyNorm_lowerBound (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    Real.sqrt (sInf (spectrum ℝ A)) * ‖f‖ ≤ ‖f‖_[A, hA] := by
  classical
  obtain hempty | hnonempty := isEmpty_or_nonempty n
  · -- In the empty-index case every vector is zero, so both norms vanish.
    have hf : f = 0 := Subsingleton.elim _ _
    subst hf
    have hzero : ‖(0 : EuclideanSpace ℝ n)‖_[A, hA] = 0 := by
      rw [Matrix.energyNorm_eq_sqrt_energyInner, Matrix.energyInner_eq]
      simp
    simp [hzero]
  · -- In the nonempty case, compare squares using the positive-semidefinite spectral shift.
    have hsinf_nonneg : 0 ≤ sInf (spectrum ℝ A) := by
      simpa [Matrix.lambdaMin_eq_sInf_spectrum] using Matrix.spectralInf_nonneg_of_posDef A hA
    have hinner_nonneg : 0 ≤ inner ℝ (A.toEuclideanLin f) f :=
      Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef f
    have hquadratic :
        sInf (spectrum ℝ A) * ‖f‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin f) f :=
      by
        simpa [Matrix.lambdaMin_eq_sInf_spectrum] using
          Matrix.lambdaMin_mul_normSq_le_inner_toEuclideanLin A hA f
    have hnorm_sq :
        ‖f‖_[A, hA] ^ 2 = inner ℝ (A.toEuclideanLin f) f := by
      -- Rewrite the energy norm squared as the quadratic form defined by `A`.
      rw [Matrix.energyNorm_eq_sqrt_energyInner, Matrix.energyInner_eq, Real.sq_sqrt hinner_nonneg]
    have henergy_nonneg : 0 ≤ ‖f‖_[A, hA] := by
      rw [Matrix.energyNorm_eq_sqrt_energyInner]
      exact Real.sqrt_nonneg _
    have hsq :
        (Real.sqrt (sInf (spectrum ℝ A)) * ‖f‖) ^ 2 ≤ ‖f‖_[A, hA] ^ 2 := by
      calc
        (Real.sqrt (sInf (spectrum ℝ A)) * ‖f‖) ^ 2
            = (Real.sqrt (sInf (spectrum ℝ A))) ^ 2 * ‖f‖ ^ 2 := by ring
        _ = sInf (spectrum ℝ A) * ‖f‖ ^ 2 := by rw [Real.sq_sqrt hsinf_nonneg]
        _ ≤ inner ℝ (A.toEuclideanLin f) f := hquadratic
        _ = ‖f‖_[A, hA] ^ 2 := hnorm_sq.symm
    exact (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      henergy_nonneg).mp hsq

/-- Definition 3.3 (3). For a positive-definite real matrix, the energy norm is
bounded above by the Euclidean norm scaled by the square root of the largest
spectral value. -/
theorem energyNorm_upperBound (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    ‖f‖_[A, hA] ≤ Real.sqrt (sSup (spectrum ℝ A)) * ‖f‖ := by
  classical
  obtain hempty | hnonempty := isEmpty_or_nonempty n
  · -- In the empty-index case every vector is zero, so both norms vanish.
    have hf : f = 0 := Subsingleton.elim _ _
    subst hf
    have hzero : ‖(0 : EuclideanSpace ℝ n)‖_[A, hA] = 0 := by
      rw [Matrix.energyNorm_eq_sqrt_energyInner, Matrix.energyInner_eq]
      simp
    simp [hzero]
  · -- In the nonempty case, compare squares using the positive-semidefinite upper shift.
    have hsup_nonneg : 0 ≤ sSup (spectrum ℝ A) := by
      simpa [Matrix.lambdaMax_eq_sSup_spectrum] using Matrix.spectralSup_nonneg_of_posDef A hA
    have hinner_nonneg : 0 ≤ inner ℝ (A.toEuclideanLin f) f :=
      Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef f
    have hquadratic :
        inner ℝ (A.toEuclideanLin f) f ≤ sSup (spectrum ℝ A) * ‖f‖ ^ 2 :=
      by
        simpa [Matrix.lambdaMax_eq_sSup_spectrum] using
          Matrix.inner_toEuclideanLin_le_lambdaMax_mul_normSq A hA f
    have hnorm_sq :
        ‖f‖_[A, hA] ^ 2 = inner ℝ (A.toEuclideanLin f) f := by
      -- Rewrite the energy norm squared as the quadratic form defined by `A`.
      rw [Matrix.energyNorm_eq_sqrt_energyInner, Matrix.energyInner_eq, Real.sq_sqrt hinner_nonneg]
    have henergy_nonneg : 0 ≤ ‖f‖_[A, hA] := by
      rw [Matrix.energyNorm_eq_sqrt_energyInner]
      exact Real.sqrt_nonneg _
    have hsq :
        ‖f‖_[A, hA] ^ 2 ≤ (Real.sqrt (sSup (spectrum ℝ A)) * ‖f‖) ^ 2 := by
      calc
        ‖f‖_[A, hA] ^ 2 = inner ℝ (A.toEuclideanLin f) f := hnorm_sq
        _ ≤ sSup (spectrum ℝ A) * ‖f‖ ^ 2 := hquadratic
        _ = (Real.sqrt (sSup (spectrum ℝ A))) ^ 2 * ‖f‖ ^ 2 := by
              rw [Real.sq_sqrt hsup_nonneg]
        _ = (Real.sqrt (sSup (spectrum ℝ A)) * ‖f‖) ^ 2 := by ring
    exact (sq_le_sq₀
      henergy_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

end Bounds

end Matrix
