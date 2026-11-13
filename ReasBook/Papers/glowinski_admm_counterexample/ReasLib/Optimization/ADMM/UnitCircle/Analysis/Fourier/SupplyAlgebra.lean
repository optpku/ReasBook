/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Ring

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open scoped ComplexConjugate ComplexOrder

noncomputable section

/-- The real Hermitian quadratic form used in the frequency-domain estimate. -/
def quadratic (M : Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 2 → ℂ) : ℝ :=
  (star s ⬝ᵥ M.mulVec s).re

theorem quadratic_hermitianPart (M : Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 2 → ℂ) :
    quadratic (hermitianPart M) s = quadratic M s := by
  simp [quadratic, hermitianPart, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_re, Complex.mul_im]
  ring

/-- The raw symbol represents precisely the two normal/output pairings. -/
theorem rawSupplySymbol_quadratic {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ : ℝ) (z : ℂ) (s : Fin 2 → ℂ) :
    quadratic (rawSupplySymbol c α γ z) s =
      ∑ b : Fin 2, (conj (normalRow α γ z b ⬝ᵥ s) *
        lagMultiplier c α z b * (pointRow α z b ⬝ᵥ s)).re := by
  simp only [quadratic, rawSupplySymbol, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, Complex.star_def, map_add, map_mul]
  rw [← Complex.add_re]
  congr 1 <;> ring

/-- The algebraic identity behind discounted Parseval separation, for the actual
supply symbol and arbitrary state vector at each frequency. -/
theorem supplySymbol_quadratic {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ : ℝ) (z : ℂ) (s : Fin 2 → ℂ) :
    quadratic (supplySymbol c α γ z) s =
      -(∑ b : Fin 2, (conj (normalRow α γ z b ⬝ᵥ s) *
        lagMultiplier c α z b * (pointRow α z b ⬝ᵥ s)).re) -
        c.epsilon * Complex.normSq (delaySymbol α z * s 1) := by
  have hraw := rawSupplySymbol_quadratic c α γ z s
  have hherm := quadratic_hermitianPart (rawSupplySymbol c α γ z) s
  have hsplit : quadratic (supplySymbol c α γ z) s =
      -quadratic (hermitianPart (rawSupplySymbol c α γ z)) s -
        c.epsilon * Complex.normSq (delaySymbol α z * s 1) := by
    simp [quadratic, supplySymbol, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      residualCoordinateMatrix, Complex.star_def, Complex.normSq_mul,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [hsplit, hherm, hraw]

/-- A positive-semidefinite matrix lower bound implies its scalar quadratic estimate. -/
theorem quadratic_lower_bound {M : Matrix (Fin 2) (Fin 2) ℂ} {a : ℝ}
    (hM : (M - (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (s : Fin 2 → ℂ) :
    a * (Complex.normSq (s 0) + Complex.normSq (s 1)) ≤ quadratic M s := by
  have h := hM.dotProduct_mulVec_nonneg s
  have hre := (Complex.nonneg_iff.mp h).1
  simp [quadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.star_def, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] at hre ⊢
  nlinarith

end

end ADMM.UnitCircle.Fourier
