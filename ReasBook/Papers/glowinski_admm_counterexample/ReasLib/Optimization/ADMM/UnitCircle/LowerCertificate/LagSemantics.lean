/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Laurent

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators
open ADMM.FiniteMemory ADMM.RefinedEndpoint.Data

/-- The finite two-sided lag basis selects a prescribed nonzero signed lag. -/
theorem lagFunction_single {n : ℕ} (j : ℤ) (a : ℂ) (φ : ℤ → ℂ)
    (hj : 0 < j.natAbs) (hn : j.natAbs ≤ n) :
    (∑ i : Fin n,
      ((if j = -(i.val + 1 : ℤ) then a else 0) * φ (-(i.val + 1 : ℤ)) +
      (if j = (i.val + 1 : ℤ) then a else 0) * φ (i.val + 1 : ℤ))) = a * φ j := by
  cases j with
  | ofNat k =>
    cases k with
    | zero => simp at hj
    | succ k =>
      have hk : k < n := by change k + 1 ≤ n at hn; omega
      let t : Fin n := ⟨k, hk⟩
      rw [Finset.sum_eq_single t]
      · have hneg : Int.ofNat (k + 1) ≠ -(t.val + 1 : ℤ) := by dsimp [t]; omega
        have hpos : Int.ofNat (k + 1) = (t.val + 1 : ℤ) := by
          simp [t, Int.natCast_add]
        rw [if_neg hneg, if_pos hpos, zero_mul, zero_add, ← hpos]
      · intro i _ hit
        have hpos : Int.ofNat (k + 1) ≠ (i.val + 1 : ℤ) := by
          intro h; apply hit; apply Fin.ext; change i.val = k
          change ((k + 1 : ℕ) : ℤ) = (i.val + 1 : ℤ) at h
          push_cast at h
          omega
        have hneg : Int.ofNat (k + 1) ≠ -(i.val + 1 : ℤ) := by
          change ((k + 1 : ℕ) : ℤ) ≠ -(i.val + 1 : ℤ)
          push_cast
          omega
        rw [if_neg hneg, if_neg hpos, zero_mul, zero_mul, add_zero]
      · simp
  | negSucc k =>
    have hk : k < n := by simpa using hn
    let t : Fin n := ⟨k, hk⟩
    rw [Finset.sum_eq_single t]
    · have hpos : Int.negSucc k ≠ (t.val + 1 : ℤ) := by dsimp [t]; omega
      have hneg : Int.negSucc k = -(t.val + 1 : ℤ) := by dsimp [t]; omega
      rw [if_pos hneg, if_neg hpos, zero_mul, add_zero, ← hneg]
    · intro i _ hit
      have hneg : Int.negSucc k ≠ -(i.val + 1 : ℤ) := by
        intro h; apply hit; apply Fin.ext; dsimp [t]; omega
      have hpos : Int.negSucc k ≠ (i.val + 1 : ℤ) := by omega
      rw [if_neg hneg, if_neg hpos, zero_mul, zero_mul, add_zero]
    · simp

/-- Reindex all raw input coefficients by signed lag, for an arbitrary test
function. This connects the rational input list to every Laurent evaluation. -/
theorem lookupFunction_eq_raw (n : ℕ) (xs : List LagWeight) (b : Block) (φ : ℤ → ℂ)
    (hrange : ∀ e ∈ xs, 0 < e.lag.natAbs ∧ e.lag.natAbs ≤ n) :
    (∑ i : Fin n,
      ((Concrete.coefficientFrom xs b (-(i.val + 1 : ℤ)) : ℂ) * φ (-(i.val + 1 : ℤ)) +
      (Concrete.coefficientFrom xs b (i.val + 1 : ℤ) : ℂ) * φ (i.val + 1 : ℤ))) =
      ((xs.filter (fun e ↦ decide (e.block = b))).map
        (fun e ↦ (e.coefficient : ℂ) * φ e.lag)).sum := by
  induction xs with
  | nil => simp [Concrete.coefficientFrom]
  | cons e xs ih =>
    have he := hrange e List.mem_cons_self
    have hxs : ∀ a ∈ xs, 0 < a.lag.natAbs ∧ a.lag.natAbs ≤ n :=
      fun a ha ↦ hrange a (List.mem_cons_of_mem e ha)
    have hsplit : (∑ i : Fin n,
        ((Concrete.coefficientFrom (e :: xs) b (-(i.val + 1 : ℤ)) : ℂ) * φ (-(i.val + 1 : ℤ)) +
        (Concrete.coefficientFrom (e :: xs) b (i.val + 1 : ℤ) : ℂ) * φ (i.val + 1 : ℤ))) =
      (∑ i : Fin n,
        (((if e.block = b ∧ e.lag = -(i.val + 1 : ℤ) then e.coefficient else 0 : ℚ) : ℂ) *
          φ (-(i.val + 1 : ℤ)) +
        ((if e.block = b ∧ e.lag = (i.val + 1 : ℤ) then e.coefficient else 0 : ℚ) : ℂ) *
          φ (i.val + 1 : ℤ))) +
        ∑ i : Fin n,
          ((Concrete.coefficientFrom xs b (-(i.val + 1 : ℤ)) : ℂ) * φ (-(i.val + 1 : ℤ)) +
          (Concrete.coefficientFrom xs b (i.val + 1 : ℤ) : ℂ) * φ (i.val + 1 : ℤ)) := by
      simp only [Concrete.coefficientFrom_cons, Rat.cast_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, ih hxs]
    by_cases hb : e.block = b
    · simp only [hb, true_and, apply_ite, Rat.cast_zero]
      rw [lagFunction_single e.lag (e.coefficient : ℂ) φ he.1 he.2]
      simp [hb]
    · simp [hb]

/-- The exact multiplier evaluated as the raw finite Laurent sum from JSON. -/
theorem paper_lagMultiplier_one (z : ℂ) (b : Fin 2) :
    lagMultiplier paperWeights 1 z b = (omega : ℂ) +
      ((lagWeights.filter (fun e ↦ decide (e.block = Concrete.blockOfIndex b))).map
        (fun e ↦ (e.coefficient : ℂ) * (1 - z ^ e.lag))).sum := by
  have h := lookupFunction_eq_raw historyLength lagWeights (Concrete.blockOfIndex b)
    (fun j ↦ 1 - z ^ j) (fun e he ↦ of_decide_eq_true
      ((List.all_eq_true.mp lagWeights_in_range) e he))
  unfold lagMultiplier
  simp only [one_pow, one_mul, paperWeights_backward, paperWeights_forward,
    paperWeights, Complex.ofReal_ratCast]
  congr 1
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Concrete.rationalLagCoefficient, Concrete.coefficientFrom,
    ← Int.natCast_add, ← Int.natCast_one, zpow_neg, zpow_natCast, inv_pow,
    Complex.ofReal_one, one_pow, one_mul]

/-- Laurent terms for the support weights in one block. -/
def lagTerms (xs : List LagWeight) (b : Block) : Laurent :=
  xs.flatMap (fun e ↦ if e.block = b then [(0, e.coefficient), (e.lag, -e.coefficient)] else [])

theorem evaluate_lagTerms (xs : List LagWeight) (b : Block) (z : ℂ) :
    evaluateLaurent (lagTerms xs b) z =
      ((xs.filter (fun e ↦ decide (e.block = b))).map
        (fun e ↦ (e.coefficient : ℂ) * (1 - z ^ e.lag))).sum := by
  induction xs with
  | nil => simp [lagTerms]
  | cons e xs ih =>
    by_cases hb : e.block = b
    · have h := congrArg (fun t : ℂ ↦ (e.coefficient : ℂ) * (1 - z ^ e.lag) + t) ih
      simpa [lagTerms, hb, evaluateLaurent_append, sub_eq_add_neg, mul_add, add_assoc] using h
    · simpa [lagTerms, hb] using ih

/-- Computational raw-input Laurent multiplier, including the common origin coefficient. -/
def lagLaurent (b : Fin 2) : Laurent :=
  (0, omega) :: lagTerms lagWeights (Concrete.blockOfIndex b)

/-- Source identity: the concrete analytic multiplier is the evaluation of
the exact rational Laurent expression, not an unrelated generated polynomial. -/
theorem evaluate_lagLaurent (z : ℂ) (b : Fin 2) :
    evaluateLaurent (lagLaurent b) z = lagMultiplier paperWeights 1 z b := by
  rw [lagLaurent, evaluateLaurent_cons, zpow_zero, mul_one, evaluate_lagTerms]
  exact (paper_lagMultiplier_one z b).symm

end ADMM.UnitCircle.LowerCertificate
