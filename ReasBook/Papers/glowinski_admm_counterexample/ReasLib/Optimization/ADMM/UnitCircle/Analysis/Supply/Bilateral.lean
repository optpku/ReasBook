/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Total
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open scoped BigOperators ComplexConjugate ENNReal
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- Zero extension from nonnegative integer times to all integer times. -/
def extendZero {X : Type*} [Zero X] (x : ℕ → X) (k : ℤ) : X :=
  if 0 ≤ k then x k.toNat else 0

@[simp] lemma extendZero_nat {X : Type*} [Zero X] (x : ℕ → X) (k : ℕ) :
    extendZero x k = x k := by simp [extendZero]

@[simp] lemma extendZero_negSucc {X : Type*} [Zero X] (x : ℕ → X) (k : ℕ) :
    extendZero x (-(k + 1 : ℤ)) = 0 := by
  have hneg : ¬ (0 : ℤ) ≤ -(k + 1 : ℤ) := by omega
  simp only [extendZero, if_neg hneg]

/-- Zero extension preserves summability and its total exactly. -/
theorem summable_extendZero {X : Type*} [NormedAddCommGroup X]
    {x : ℕ → X} (hx : Summable x) : Summable (extendZero x) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [extendZero_nat] using hx
  · simp only [extendZero_negSucc]
    exact summable_zero

theorem tsum_extendZero {X : Type*} [NormedAddCommGroup X]
    {x : ℕ → X} (hx : Summable x) : (∑' k : ℤ, extendZero x k) = ∑' k, x k := by
  rw [tsum_of_nat_of_neg_add_one]
  · simp only [extendZero_nat, extendZero_negSucc, tsum_zero, add_zero]
  · simpa only [extendZero_nat] using hx
  · simp only [extendZero_negSucc]
    exact summable_zero

/-- The bilateral delay restricts to the one-sided delay after zero extension. -/
lemma extendZero_delay {X : Type*} [Zero X] (x : ℕ → X) (j k : ℕ) :
    extendZero x ((k : ℤ) - j) = zeroDelay x j k := by
  by_cases hj : j ≤ k
  · have hkj : (0 : ℤ) ≤ (k : ℤ) - j := by omega
    simp only [extendZero, if_pos hkj, zeroDelay, if_pos hj]
    congr 1
    omega
  · have hkj : ¬ (0 : ℤ) ≤ (k : ℤ) - j := by omega
    simp only [extendZero, if_neg hkj, zeroDelay, if_neg hj]

/-- Discount and complexify one real coordinate before bilateral extension. -/
noncomputable def complexSequence {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (a : Fin m) : ℤ → ℂ :=
  extendZero (fun k ↦ ((α ^ k * x k a : ℝ) : ℂ))

@[simp] theorem complexSequence_nat {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (a : Fin m) (k : ℕ) : complexSequence α x a k = ((α ^ k * x k a : ℝ) : ℂ) :=
  extendZero_nat _ _

@[simp] theorem complexSequence_negSucc {m : ℕ} (α : ℝ)
    (x : ℕ → Fin m → ℝ) (a : Fin m) (k : ℕ) :
    complexSequence α x a (-(k + 1 : ℤ)) = 0 := extendZero_negSucc _ _

/-- Each individual coordinate inherits discounted square summability. -/
theorem summable_weighted_coordinate {m : ℕ} {α : ℝ} {x : ℕ → Fin m → ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k))) (a : Fin m) :
    Summable (fun k ↦ timeWeight α k * (x k a) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (timeWeight_nonneg α k) (sq_nonneg _))
    (fun k ↦ mul_le_mul_of_nonneg_left ?_ (timeWeight_nonneg α k)) hx
  simpa only [coordinateSquare, dotProduct, pow_two] using
    Finset.single_le_sum (fun i _ ↦ mul_self_nonneg (x k i)) (Finset.mem_univ a)

/-- The genuine bilateral sequence belongs to Hilbert sequence space. -/
theorem complexSequence_memℓp {m : ℕ} {α : ℝ} {x : ℕ → Fin m → ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k))) (a : Fin m) :
    Memℓp (complexSequence α x a) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  norm_num only [ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  apply Summable.of_nat_of_neg_add_one
  · apply (summable_weighted_coordinate hx a).congr
    intro k
    simp only [complexSequence_nat, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      mul_pow, timeWeight]
    simp only [← pow_mul, Nat.mul_comm]
  · simp only [complexSequence_negSucc, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact summable_zero

/-- The scalar sequence used in the bilateral Fourier transform. -/
noncomputable def complexLp {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (a : Fin m) : lp (fun _ : ℤ ↦ ℂ) 2 :=
  ⟨complexSequence α x a, complexSequence_memℓp hx a⟩

@[simp] theorem complexLp_apply {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (a : Fin m) (k : ℤ) : complexLp α x hx a k = complexSequence α x a k := rfl

end ADMM.UnitCircle.Supply
