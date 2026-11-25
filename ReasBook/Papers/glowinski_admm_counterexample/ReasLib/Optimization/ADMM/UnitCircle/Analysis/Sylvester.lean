/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped ComplexOrder

namespace ADMM.UnitCircle

/-- Explicit Hermitian two-by-two matrix, with real diagonal coordinates. -/
noncomputable def hermitianTwoByTwo (a d : ℝ) (b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), b; star b, (d : ℂ)]

/-- Exact triangular factorization used in the two-dimensional Sylvester test. -/
theorem hermitianTwoByTwo_factorization {a d : ℝ} {b : ℂ} (ha : a ≠ 0) :
    hermitianTwoByTwo a d b =
      (!![(1 : ℂ), b / (a : ℂ); 0, 1]).conjTranspose *
        Matrix.diagonal ![(a : ℂ), (((a * d - Complex.normSq b) / a : ℝ) : ℂ)] *
        !![(1 : ℂ), b / (a : ℂ); 0, 1] := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTwoByTwo, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.star_def]
  · field_simp
  · field_simp
  · push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    field_simp
    ring

/-- Strict positivity of the first pivot and determinant proves positive
definiteness. This is the exact criterion used for the lower certificate. -/
theorem hermitianTwoByTwo_posDef {a d : ℝ} {b : ℂ}
    (ha : 0 < a) (hdet : 0 < a * d - Complex.normSq b) :
    (hermitianTwoByTwo a d b).PosDef := by
  let L : Matrix (Fin 2) (Fin 2) ℂ := !![1, b / (a : ℂ); 0, 1]
  have hD : (Matrix.diagonal
      ![(a : ℂ), (((a * d - Complex.normSq b) / a : ℝ) : ℂ)]).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact Complex.zero_lt_real.mpr ha
    · exact Complex.zero_lt_real.mpr (div_pos hdet ha)
  have hL : Function.Injective L.mulVec := by
    intro x y hxy
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 1
    simp [L, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    funext i
    fin_cases i
    · simpa [h1] using h0
    · exact h1
  rw [hermitianTwoByTwo_factorization ha.ne']
  exact hD.conjTranspose_mul_mul_same hL

/-- The determinant of the explicit Hermitian matrix is the real test polynomial. -/
theorem hermitianTwoByTwo_det (a d : ℝ) (b : ℂ) :
    (hermitianTwoByTwo a d b).det = ((a * d - Complex.normSq b : ℝ) : ℂ) := by
  simp [hermitianTwoByTwo, Matrix.det_fin_two, Complex.star_def]
  rw [Complex.normSq_eq_conj_mul_self]
  ring

/-- Every Hermitian matrix has the preceding explicit coordinate form. -/
theorem hermitian_eq_twoByTwo {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) :
    A = hermitianTwoByTwo (A 0 0).re (A 1 1).re (A 0 1) := by
  have hdiag (i : Fin 2) : A i i = ((A i i).re : ℂ) := by
    have h := congrArg Complex.im (hA.apply i i)
    have hi : (A i i).im = 0 := by simp [Complex.star_def] at h; linarith
    apply Complex.ext <;> simp [hi]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [hermitianTwoByTwo] using hdiag 0
  · simp [hermitianTwoByTwo]
  · simpa [hermitianTwoByTwo] using (hA.apply 1 0).symm
  · simpa [hermitianTwoByTwo] using hdiag 1

/-- Coordinate-free two-by-two Sylvester criterion with the actual determinant. -/
theorem posDef_of_sylvester {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian)
    (ha : 0 < (A 0 0).re) (hdet : 0 < A.det.re) : A.PosDef := by
  have hform := hermitian_eq_twoByTwo hA
  have hd : 0 < (A 0 0).re * (A 1 1).re - Complex.normSq (A 0 1) := by
    have h := congrArg Complex.re (hermitianTwoByTwo_det (A 0 0).re (A 1 1).re (A 0 1))
    rw [← hform] at h
    simpa only [Complex.ofReal_re] using hdet.trans_le h.le
  rw [hform]
  exact hermitianTwoByTwo_posDef ha hd

end ADMM.UnitCircle
