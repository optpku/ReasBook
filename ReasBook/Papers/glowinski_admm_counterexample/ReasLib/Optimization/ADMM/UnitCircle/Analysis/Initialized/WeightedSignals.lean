/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Pairing
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Operators

@[expose] public section

open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Initialized

open Supply

noncomputable section

/-- Weighted square summability of a real finite-dimensional sequence. -/
abbrev SquareSummable {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ) : Prop :=
  Summable (fun k ↦ timeWeight α k * coordinateSquare (x k))

theorem coordinateSquare_add_le {m : ℕ} (x y : Fin m → ℝ) :
    coordinateSquare (x + y) ≤ 2 * (coordinateSquare x + coordinateSquare y) := by
  simp only [coordinateSquare, dotProduct, Pi.add_apply, mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i - y i)]

theorem coordinateSquare_smul {m : ℕ} (a : ℝ) (x : Fin m → ℝ) :
    coordinateSquare (a • x) = a ^ 2 * coordinateSquare x := by
  simp only [coordinateSquare, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem SquareSummable.add {m : ℕ} {α : ℝ} {x y : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) (hy : SquareSummable α y) : SquareSummable α (x + y) := by
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (timeWeight_nonneg α k) (coordinateSquare_nonneg _))
    (fun k ↦ ?_) ((Summable.add hx hy).mul_left 2)
  have h := mul_le_mul_of_nonneg_left (coordinateSquare_add_le (x k) (y k))
    (timeWeight_nonneg α k)
  change timeWeight α k * coordinateSquare (x k + y k) ≤ _
  nlinarith

theorem SquareSummable.smul {m : ℕ} {α : ℝ} {x : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) (a : ℝ) : SquareSummable α (a • x) := by
  apply (hx.mul_left (a ^ 2)).congr
  intro k
  change a ^ 2 * (timeWeight α k * coordinateSquare (x k)) =
    timeWeight α k * coordinateSquare (a • x k)
  rw [coordinateSquare_smul]
  ring

theorem SquareSummable.neg {m : ℕ} {α : ℝ} {x : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) : SquareSummable α (-x) := by
  simpa only [neg_one_smul] using hx.smul (-1)

theorem SquareSummable.sub {m : ℕ} {α : ℝ} {x y : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) (hy : SquareSummable α y) : SquareSummable α (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem SquareSummable.zeroDelay {m : ℕ} {α : ℝ} {x : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) (j : ℕ) : SquareSummable α (zeroDelay x j) := by
  simpa only [SquareSummable, coordinateSquare_zeroDelay, Function.comp_def] using
    (weighted_zeroDelay hx j).1

theorem complexLp_add {m : ℕ} (α : ℝ) (x y : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (hy : SquareSummable α y) (a : Fin m) :
    complexLp α (x + y) (hx.add hy) a = complexLp α x hx a + complexLp α y hy a := by
  ext k
  change complexSequence α (x + y) a k = complexSequence α x a k + complexSequence α y a k
  cases k with
  | ofNat k => simp [Pi.add_apply, mul_add]
  | negSucc k =>
    have hneg : ¬ (0 : ℤ) ≤ Int.negSucc k := by omega
    simp only [complexSequence, extendZero, if_neg hneg, add_zero]

theorem complexLp_sub {m : ℕ} (α : ℝ) (x y : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (hy : SquareSummable α y) (a : Fin m) :
    complexLp α (x - y) (hx.sub hy) a = complexLp α x hx a - complexLp α y hy a := by
  ext k
  change complexSequence α (x - y) a k = complexSequence α x a k - complexSequence α y a k
  cases k with
  | ofNat k => simp [Pi.sub_apply, mul_sub]
  | negSucc k =>
    have hneg : ¬ (0 : ℤ) ≤ Int.negSucc k := by omega
    simp only [complexSequence, extendZero, if_neg hneg, sub_zero]

theorem complexLp_smul {m : ℕ} (α c : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (a : Fin m) :
    complexLp α (c • x) (hx.smul c) a = (c : ℂ) • complexLp α x hx a := by
  ext k
  change complexSequence α (c • x) a k = (c : ℂ) * complexSequence α x a k
  cases k with
  | ofNat k =>
    change complexSequence α (c • x) a (k : ℤ) = (c : ℂ) * complexSequence α x a (k : ℤ)
    simp only [complexSequence_nat, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  | negSucc k =>
    have hneg : ¬ (0 : ℤ) ≤ Int.negSucc k := by omega
    simp only [complexSequence, extendZero, if_neg hneg, mul_zero]

/-- Discounting and zero extension turn a real one-sided delay into exactly
`α^j` times the true bilateral Hilbert-space delay. -/
theorem complexLp_zeroDelay {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (j : ℕ) (a : Fin m) :
    complexLp α (zeroDelay x j) (hx.zeroDelay j) a =
      ((α : ℂ) ^ j) • Fourier.delay (j : ℤ) (complexLp α x hx a) := by
  ext k
  change complexSequence α (zeroDelay x j) a k =
    ((α : ℂ) ^ j) * Fourier.delay (j : ℤ) (complexLp α x hx a) k
  rw [Fourier.delay_apply, complexLp_apply]
  cases k with
  | ofNat k =>
    change complexSequence α (zeroDelay x j) a (k : ℤ) =
      ((α : ℂ) ^ j) * complexSequence α x a ((k : ℤ) - j)
    rw [complexSequence_nat, complexSequence_delay_nat]
    by_cases hj : j ≤ k
    · simp only [zeroDelay, if_pos hj]
      have hpow : α ^ k = α ^ j * α ^ (k - j) := by
        rw [← pow_add, Nat.add_sub_of_le hj]
      rw [hpow]
      push_cast
      ring
    · simp [zeroDelay, hj]
  | negSucc k =>
    have hneg : ¬ (0 : ℤ) ≤ Int.negSucc k := by omega
    have hneg' : ¬ (0 : ℤ) ≤ Int.negSucc k - (j : ℤ) := by omega
    simp only [complexSequence, extendZero, if_neg hneg, if_neg hneg', mul_zero]

/-- The discounted difference of the actual state has exactly the actual
zero-extended real difference as its scalar-coordinate representative. -/
theorem complexLp_difference {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (a : Fin m) :
    complexLp α (x - zeroDelay x 1) (hx.sub (hx.zeroDelay 1)) a =
      Fourier.difference α (complexLp α x hx a) := by
  rw [complexLp_sub α x (zeroDelay x 1) hx (hx.zeroDelay 1) a,
    complexLp_zeroDelay α x hx 1 a]
  simp only [pow_one, Fourier.difference, Int.natCast_one]

end

end ADMM.UnitCircle.Initialized
