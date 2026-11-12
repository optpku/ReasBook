/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.WeightedSignals

@[expose] public section

open ADMM.ConvergenceProof
open scoped ENNReal BigOperators

namespace ADMM.UnitCircle.Initialized

open Supply

/-- Exact norm preservation for one discounted real coordinate and its bilateral complex copy. -/
theorem complexLp_norm_sq {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) (a : Fin m) :
    ‖complexLp α x hx a‖ ^ 2 = ∑' k, timeWeight α k * (x k a) ^ 2 := by
  have hnorm : ‖complexLp α x hx a‖ ^ 2 = ∑' k : ℤ, ‖complexLp α x hx a k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (complexLp α x hx a)
  rw [hnorm]
  have heq : (fun k : ℤ ↦ ‖complexLp α x hx a k‖ ^ 2) =
      extendZero (fun k ↦ timeWeight α k * (x k a) ^ 2) := by
    funext k
    cases k with
    | ofNat k =>
      change ‖complexLp α x hx a (k : ℤ)‖ ^ 2 =
        extendZero (fun j ↦ timeWeight α j * (x j a) ^ 2) (k : ℤ)
      simp only [complexLp_apply, complexSequence_nat, extendZero_nat,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, timeWeight, pow_mul]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    | negSucc k =>
      have hneg : ¬ (0 : ℤ) ≤ Int.negSucc k := by omega
      simp only [complexLp_apply, complexSequence, extendZero, if_neg hneg, norm_zero]
      norm_num
  rw [heq, tsum_extendZero (summable_weighted_coordinate hx a)]

/-- The sum of scalar Fourier-coordinate energies is exactly the weighted real vector energy. -/
theorem complexLp_coordinate_energy {m : ℕ} (α : ℝ) (x : ℕ → Fin m → ℝ)
    (hx : SquareSummable α x) :
    (∑ a : Fin m, ‖complexLp α x hx a‖ ^ 2) =
      ∑' k, timeWeight α k * coordinateSquare (x k) := by
  simp only [complexLp_norm_sq]
  rw [← Summable.tsum_finsetSum (fun a _ ↦ summable_weighted_coordinate hx a)]
  apply tsum_congr
  intro k
  simp only [coordinateSquare, dotProduct, pow_two, Finset.mul_sum]

/-- A finite initial change does not alter discounted square summability. -/
theorem SquareSummable.of_eq_after_zero {m : ℕ} {α : ℝ} {x y : ℕ → Fin m → ℝ}
    (hx : SquareSummable α x) (heq : ∀ k, 0 < k → y k = x k) : SquareSummable α y := by
  apply (summable_nat_add_iff 1).1
  apply ((summable_nat_add_iff 1).2 hx).congr
  intro k
  rw [heq (k + 1) (by omega)]

end ADMM.UnitCircle.Initialized
