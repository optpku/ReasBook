/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle

/-- The two blocks are indexed by `0 = F` and `1 = J`. Index `i : Fin ℓ`
represents lag `i.val + 1`, so no unused zero-lag coefficient is included. -/
structure LagWeights (ℓ : ℕ) where
  backward : Fin 2 → Fin ℓ → ℝ
  forward : Fin 2 → Fin ℓ → ℝ
  omega : ℝ
  epsilon : ℝ
  backward_nonneg : ∀ b i, 0 ≤ backward b i
  forward_nonneg : ∀ b i, 0 ≤ forward b i
  omega_pos : 0 < omega
  epsilon_pos : 0 < epsilon

/-- The signed first moment in one block, with the convention of Appendix C.1. -/
noncomputable def firstMoment {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) : ℝ :=
  ∑ i : Fin ℓ, (i.val + 1 : ℝ) * (c.backward b i - c.forward b i)

/-- Equality of the two signed moments removes the first-order zero-frequency
term contributed by the lag multipliers. -/
def BalancedMoments {ℓ : ℕ} (c : LagWeights ℓ) : Prop :=
  firstMoment c 0 = firstMoment c 1

/-- `d_α = 1 - α z⁻¹`. -/
noncomputable def delaySymbol (α : ℝ) (z : ℂ) : ℂ :=
  1 - (α : ℂ) * z⁻¹

/-- `b_(α,γ) = 1 + (γ-1) α z⁻¹`. -/
noncomputable def multiplierSymbol (α γ : ℝ) (z : ℂ) : ℂ :=
  1 + ((γ : ℂ) - 1) * (α : ℂ) * z⁻¹

/-- The two point rows in discounted Fourier coordinates `(η,w)`. -/
noncomputable def pointRow (α : ℝ) (z : ℂ) (b : Fin 2) : Fin 2 → ℂ :=
  fun i ↦ if i = 0 then 1 else if b = 0 then delaySymbol α z else 0

/-- The two normal rows in the same coordinates and multiplier convention. -/
noncomputable def normalRow (α γ : ℝ) (z : ℂ) (b : Fin 2) : Fin 2 → ℂ :=
  fun i ↦ if b = 0 then
    (if i = 0 then -delaySymbol α z else -multiplierSymbol α γ z)
  else if i = 0 then 0 else multiplierSymbol α γ z

/-- The finite discounted multiplier `Λ_b(α,z)`, retaining both lag directions. -/
noncomputable def lagMultiplier {ℓ : ℕ} (c : LagWeights ℓ)
    (α : ℝ) (z : ℂ) (b : Fin 2) : ℂ :=
  (c.omega : ℂ) + ∑ i : Fin ℓ,
    ((c.backward b i : ℂ) *
      (1 - (α : ℂ) ^ (i.val + 1) * (z⁻¹) ^ (i.val + 1)) +
    (c.forward b i : ℂ) *
      ((α : ℂ) ^ (2 * (i.val + 1)) - (α : ℂ) ^ (i.val + 1) * z ^ (i.val + 1)))

/-- The unsymmetrized matrix `∑_b n_b* Λ_b p_b`. -/
noncomputable def rawSupplySymbol {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j ↦ ∑ b : Fin 2,
    star (normalRow α γ z b i) * lagMultiplier c α z b * pointRow α z b j

/-- The Hermitian part of a complex matrix. -/
noncomputable def hermitianPart (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (M + M.conjTranspose)

/-- The residual coordinate matrix `E₂₂ = diag(0,1)`. -/
noncomputable def residualCoordinateMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i : Fin 2 ↦ if i = 1 then 1 else 0)

/-- The actual supply symbol from equation (C.1), including the negative
residual-square term. No frequency positivity is built into this definition. -/
noncomputable def supplySymbol {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -hermitianPart (rawSupplySymbol c α γ z) -
    ((c.epsilon * Complex.normSq (delaySymbol α z) : ℝ) : ℂ) • residualCoordinateMatrix

/-- Taking the Hermitian part always produces a Hermitian matrix. -/
theorem hermitianPart_isHermitian (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (hermitianPart M).IsHermitian := by
  simp [Matrix.IsHermitian, hermitianPart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, add_comm]

/-- The residual coordinate correction is Hermitian. -/
theorem residualCoordinateMatrix_isHermitian : residualCoordinateMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [residualCoordinateMatrix]

/-- The supply symbol is Hermitian at every complex argument, not only on the
unit circle. This is the prerequisite for its matrix order comparisons. -/
theorem supplySymbol_isHermitian {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ) (z : ℂ) :
    (supplySymbol c α γ z).IsHermitian := by
  apply (hermitianPart_isHermitian _).neg.sub
  apply residualCoordinateMatrix_isHermitian.smul
  simp [isSelfAdjoint_iff]

@[simp] theorem delaySymbol_one_one : delaySymbol 1 1 = 0 := by
  simp [delaySymbol]

@[simp] theorem multiplierSymbol_one_one (γ : ℝ) : multiplierSymbol 1 γ 1 = γ := by
  simp [multiplierSymbol]

/-- At the undamped zero frequency, every lag term vanishes. -/
@[simp] theorem lagMultiplier_one_one {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) :
    lagMultiplier c 1 1 b = c.omega := by
  simp [lagMultiplier]

/-- The two origin-row contributions cancel exactly at zero frequency. -/
@[simp] theorem rawSupplySymbol_one_one {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) :
    rawSupplySymbol c 1 γ 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawSupplySymbol, normalRow, pointRow, Fin.sum_univ_two]

/-- The undamped supply vanishes at `z=1`, explaining why the convergence
argument must control this frequency through a positive time discount. -/
@[simp] theorem supplySymbol_one_one {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) :
    supplySymbol c 1 γ 1 = 0 := by
  simp [supplySymbol, hermitianPart]

/-- The normal rows depend affinely on the multiplier factor. -/
theorem normalRow_affine (α γ₀ γ₁ θ : ℝ) (z : ℂ) (b i : Fin 2) :
    normalRow α ((1 - θ) * γ₀ + θ * γ₁) z b i =
      ((1 - θ : ℝ) : ℂ) * normalRow α γ₀ z b i +
        (θ : ℂ) * normalRow α γ₁ z b i := by
  fin_cases b <;> fin_cases i <;>
    simp [normalRow, multiplierSymbol, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sub] <;> ring

/-- Multiplying by fixed lag and point rows preserves this affine dependence. -/
theorem rawSupplySymbol_affine {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ₀ γ₁ θ : ℝ) (z : ℂ) :
    rawSupplySymbol c α ((1 - θ) * γ₀ + θ * γ₁) z =
      ((1 - θ : ℝ) : ℂ) • rawSupplySymbol c α γ₀ z +
        (θ : ℂ) • rawSupplySymbol c α γ₁ z := by
  ext i j
  simp only [rawSupplySymbol, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    normalRow_affine, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Taking the Hermitian part is linear with respect to real coefficients. -/
theorem hermitianPart_real_combination (M N : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ) :
    hermitianPart ((a : ℂ) • M + (b : ℂ) • N) =
      (a : ℂ) • hermitianPart M + (b : ℂ) • hermitianPart N := by
  ext i j
  simp [hermitianPart, Matrix.conjTranspose_apply]
  ring

/-- The supply matrix is affine in the multiplier factor. Consequently,
verifying a fixed set of weights at the two endpoints covers the interval;
the residual penalty is unchanged by this interpolation. -/
theorem supplySymbol_affine {ℓ : ℕ} (c : LagWeights ℓ)
    (α γ₀ γ₁ θ : ℝ) (z : ℂ) :
    supplySymbol c α ((1 - θ) * γ₀ + θ * γ₁) z =
      ((1 - θ : ℝ) : ℂ) • supplySymbol c α γ₀ z +
        (θ : ℂ) • supplySymbol c α γ₁ z := by
  rw [supplySymbol, rawSupplySymbol_affine, hermitianPart_real_combination]
  ext i j
  simp [supplySymbol, Complex.ofReal_sub]
  ring

end ADMM.UnitCircle
