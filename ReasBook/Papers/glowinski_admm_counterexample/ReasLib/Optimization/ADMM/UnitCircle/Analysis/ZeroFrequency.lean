/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle

/-- At zero frequency the multiplier is a real polynomial in the discount. -/
noncomputable def realLagMultiplier {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) : ℝ :=
  c.omega + ∑ i : Fin ℓ,
    (c.backward b i * (1 - α ^ (i.val + 1)) +
      c.forward b i * (α ^ (2 * (i.val + 1)) - α ^ (i.val + 1)))

theorem lagMultiplier_at_one {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2) :
    lagMultiplier c α 1 b = (realLagMultiplier c α b : ℂ) := by
  simp [lagMultiplier, realLagMultiplier, Complex.ofReal_sum,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]

@[simp] theorem realLagMultiplier_one {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) :
    realLagMultiplier c 1 b = c.omega := by
  simp [realLagMultiplier]

/-- The signed first moment is precisely the negative radial derivative of
the real lag polynomial. This identity is needed to cancel the off-diagonal
first-order term, not merely to verify a finite data normalization. -/
theorem hasDerivAt_realLagMultiplier_one {ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2) :
    HasDerivAt (fun α : ℝ ↦ realLagMultiplier c α b) (-firstMoment c b) 1 := by
  have hp (n : ℕ) : HasDerivAt (fun α : ℝ ↦ α ^ n) (n : ℝ) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).fun_pow n
  have hterm (i : Fin ℓ) :
      HasDerivAt (fun α : ℝ ↦
        c.backward b i * (1 - α ^ (i.val + 1)) +
          c.forward b i * (α ^ (2 * (i.val + 1)) - α ^ (i.val + 1)))
        ((i.val + 1 : ℝ) * (c.forward b i - c.backward b i)) 1 := by
    have hback := ((hasDerivAt_const (1 : ℝ) 1).sub (hp (i.val + 1))).const_mul
      (c.backward b i)
    have hforward := ((hp (2 * (i.val + 1))).sub (hp (i.val + 1))).const_mul
      (c.forward b i)
    have h := hback.add hforward
    convert! h using 1
    push_cast
    ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hterm i)
  convert! (hasDerivAt_const (1 : ℝ) c.omega).add hs using 1
  simp only [zero_add, firstMoment, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual zero-frequency supply as a real symmetric two-by-two matrix. -/
noncomputable def zeroFrequencyMatrix {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let d := 1 - α
  let b := 1 + (γ - 1) * α
  let f := realLagMultiplier c α 0
  let j := realLagMultiplier c α 1
  fun i k ↦ if i = 0 then
    (if k = 0 then d * f else (d ^ 2 * f + b * (f - j)) / 2)
  else if k = 0 then (d ^ 2 * f + b * (f - j)) / 2
  else b * d * f - c.epsilon * d ^ 2

/-- The real formula is derived from the actual Hermitian supply, so the
subsequent derivative calculation is attached to equation (C.1). -/
theorem supplySymbol_zeroFrequency {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ) :
    supplySymbol c α γ 1 = (zeroFrequencyMatrix c α γ).map (algebraMap ℝ ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [supplySymbol, rawSupplySymbol, hermitianPart, residualCoordinateMatrix,
      normalRow, pointRow, delaySymbol, multiplierSymbol, lagMultiplier_at_one,
      zeroFrequencyMatrix, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.normSq_apply] <;> ring

/-- The first-order radial matrix at the zero frequency. -/
noncomputable def zeroFrequencyFirstOrder {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i : Fin 2 ↦ c.omega * if i = 0 then 1 else γ)

/-- Balanced moments cancel the full off-diagonal first-order term of the
actual supply. The remaining diagonal is strictly positive for `γ > 0`. -/
theorem hasDerivAt_zeroFrequencyMatrix {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (hbalance : BalancedMoments c) (i j : Fin 2) :
    HasDerivAt (fun α : ℝ ↦ zeroFrequencyMatrix c α γ i j)
      (-zeroFrequencyFirstOrder c γ i j) 1 := by
  have hd : HasDerivAt (fun α : ℝ ↦ 1 - α) (-1) 1 := by
    convert! (hasDerivAt_const (1 : ℝ) 1).sub (hasDerivAt_id 1) using 1
    simp
  have hb : HasDerivAt (fun α : ℝ ↦ 1 + (γ - 1) * α) (γ - 1) 1 := by
    convert! (hasDerivAt_const (1 : ℝ) 1).add
      ((hasDerivAt_id 1).const_mul (γ - 1)) using 1
    simp
  have hf := hasDerivAt_realLagMultiplier_one c 0
  have hj := hasDerivAt_realLagMultiplier_one c 1
  have hA := hd.mul hf
  have hB := (((hd.fun_pow 2).mul hf).add (hb.mul (hf.sub hj))).div_const 2
  have hC := ((hb.mul hd).mul hf).sub ((hd.fun_pow 2).const_mul c.epsilon)
  have heq : firstMoment c 0 = firstMoment c 1 := hbalance
  fin_cases i <;> fin_cases j
  · convert! hA using 1
    simp [zeroFrequencyFirstOrder]
  · convert! hB using 1
    simp [zeroFrequencyFirstOrder, heq]
  · convert! hB using 1
    simp [zeroFrequencyFirstOrder, heq]
  · convert! hC using 1
    simp [zeroFrequencyFirstOrder]
    ring

@[simp] theorem zeroFrequencyMatrix_one {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) :
    zeroFrequencyMatrix c 1 γ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zeroFrequencyMatrix]

/-- The zero-frequency radial quotient tends to the positive diagonal matrix.
No division is performed at the boundary point itself. -/
theorem tendsto_zeroFrequency_radial_quotient {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (hbalance : BalancedMoments c) (i j : Fin 2) :
    Filter.Tendsto (fun α : ℝ ↦ zeroFrequencyMatrix c α γ i j / (1 - α))
      (nhdsWithin 1 {1}ᶜ) (nhds (zeroFrequencyFirstOrder c γ i j)) := by
  have h := (hasDerivAt_zeroFrequencyMatrix c γ hbalance i j).tendsto_slope.neg
  simp only [neg_neg] at h
  convert! h using 1
  ext α
  simp only [slope_def_field, zeroFrequencyMatrix_one, Matrix.zero_apply, sub_zero]
  rw [show α - 1 = -(1 - α) by ring, div_neg, neg_neg]

/-- The quotient limit holds jointly in all four coordinates of the real matrix. -/
theorem tendsto_zeroFrequency_radial_matrix {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (hbalance : BalancedMoments c) :
    Filter.Tendsto (fun α : ℝ ↦ (1 - α)⁻¹ • zeroFrequencyMatrix c α γ)
      (nhdsWithin 1 {1}ᶜ) (nhds (zeroFrequencyFirstOrder c γ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    tendsto_zeroFrequency_radial_quotient c γ hbalance i j

/-- The radial limit is attached to the actual complex supply, not just to
the auxiliary real formula. This is `R(1,1)=ω diag(1,γ)` in the paper. -/
theorem tendsto_supplySymbol_zeroFrequency_quotient {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ)
    (hbalance : BalancedMoments c) (i j : Fin 2) :
    Filter.Tendsto (fun α : ℝ ↦ supplySymbol c α γ 1 i j / ((1 - α : ℝ) : ℂ))
      (nhdsWithin 1 {1}ᶜ) (nhds ((zeroFrequencyFirstOrder c γ i j : ℝ) : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_zeroFrequency_radial_quotient c γ hbalance i j)
  simpa [supplySymbol_zeroFrequency, Complex.ofReal_div, Function.comp_def] using h

/-- The radial limit matrix at the zero frequency is genuinely positive definite. -/
theorem zeroFrequencyFirstOrder_posDef {ℓ : ℕ} (c : LagWeights ℓ) {γ : ℝ}
    (hγ : 0 < γ) : (zeroFrequencyFirstOrder c γ).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · simpa using c.omega_pos
  · simpa using mul_pos c.omega_pos hγ

/-- Exact discount geometry on the unit circle. The additional squared
radial term is what permits a strictly positive discounted estimate at `z=1`. -/
theorem normSq_delaySymbol {α : ℝ} {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq (delaySymbol α z) =
      (1 - α) ^ 2 + α * Complex.normSq (delaySymbol 1 z) := by
  have hi : Complex.normSq z⁻¹ = 1 := by
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq, hz]
    norm_num
  simp [delaySymbol, Complex.normSq_sub, Complex.normSq_mul, hi, Complex.normSq_ofReal]
  ring

end ADMM.UnitCircle
