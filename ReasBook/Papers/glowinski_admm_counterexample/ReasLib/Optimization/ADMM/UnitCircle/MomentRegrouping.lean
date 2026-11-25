/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.ConcreteWeights

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle.Concrete

open ADMM.FiniteMemory
open ADMM.RefinedEndpoint.Data (LagWeight)

/-- A lookup on an arbitrary finite rational input list. -/
def coefficientFrom (xs : List LagWeight) (b : Block) (j : ℤ) : ℚ :=
  ((xs.filter (fun e ↦ decide (e.block = b ∧ e.lag = j))).map
    LagWeight.coefficient).sum

/-- The moment after collecting coefficients by their signed lag. -/
def firstMomentFrom (n : ℕ) (xs : List LagWeight) (b : Block) : ℚ :=
  ∑ i : Fin n, (i.val + 1 : ℚ) *
    (coefficientFrom xs b (-(i.val + 1 : ℤ)) - coefficientFrom xs b (i.val + 1 : ℤ))

/-- The signed moment before coefficients are collected. -/
def signedMomentFrom (xs : List LagWeight) (b : Block) : ℚ :=
  ((xs.filter (fun e ↦ decide (e.block = b))).map
    (fun e ↦ (e.lag : ℚ) * e.coefficient)).sum

theorem coefficientFrom_cons (e : LagWeight) (xs : List LagWeight) (b : Block) (j : ℤ) :
    coefficientFrom (e :: xs) b j =
      (if e.block = b ∧ e.lag = j then e.coefficient else 0) + coefficientFrom xs b j := by
  by_cases h : e.block = b ∧ e.lag = j <;> simp [coefficientFrom, h]

theorem signedMomentFrom_cons (e : LagWeight) (xs : List LagWeight) (b : Block) :
    signedMomentFrom (e :: xs) b =
      (if e.block = b then (e.lag : ℚ) * e.coefficient else 0) + signedMomentFrom xs b := by
  by_cases h : e.block = b <;> simp [signedMomentFrom, h]

/-- A negative lag contributes its positive distance times the coefficient. -/
theorem lagBasis_negative {n : ℕ} (j : Fin n) (c : ℚ) :
    (∑ i : Fin n, (i.val + 1 : ℚ) *
      ((if -(j.val + 1 : ℤ) = -(i.val + 1 : ℤ) then c else 0) -
        (if -(j.val + 1 : ℤ) = (i.val + 1 : ℤ) then c else 0))) =
      (j.val + 1 : ℚ) * c := by
  rw [Finset.sum_eq_single j]
  · have h : -(j.val + 1 : ℤ) ≠ (j.val + 1 : ℤ) := by omega
    rw [if_pos rfl, if_neg h, sub_zero]
  · intro i _ hij
    have hneg : -(j.val + 1 : ℤ) ≠ -(i.val + 1 : ℤ) := by
      intro h
      apply hij
      apply Fin.ext
      omega
    have hpos : -(j.val + 1 : ℤ) ≠ (i.val + 1 : ℤ) := by omega
    rw [if_neg hneg, if_neg hpos, sub_self, mul_zero]
  · simp

/-- A positive lag contributes minus its distance times the coefficient. -/
theorem lagBasis_positive {n : ℕ} (j : Fin n) (c : ℚ) :
    (∑ i : Fin n, (i.val + 1 : ℚ) *
      ((if (j.val + 1 : ℤ) = -(i.val + 1 : ℤ) then c else 0) -
        (if (j.val + 1 : ℤ) = (i.val + 1 : ℤ) then c else 0))) =
      -(j.val + 1 : ℚ) * c := by
  rw [Finset.sum_eq_single j]
  · have h : (j.val + 1 : ℤ) ≠ -(j.val + 1 : ℤ) := by omega
    rw [if_neg h, if_pos rfl]
    ring
  · intro i _ hij
    have hpos : (j.val + 1 : ℤ) ≠ (i.val + 1 : ℤ) := by
      intro h
      apply hij
      apply Fin.ext
      omega
    have hneg : (j.val + 1 : ℤ) ≠ -(i.val + 1 : ℤ) := by omega
    rw [if_neg hneg, if_neg hpos, sub_self, mul_zero]
  · simp

/-- Collecting one nonzero lag within the history range preserves its signed
moment, with the sign convention used by the manuscript. -/
theorem lagBasis_sum {n : ℕ} (j : ℤ) (c : ℚ)
    (hj : 0 < j.natAbs) (hn : j.natAbs ≤ n) :
    (∑ i : Fin n, (i.val + 1 : ℚ) *
      ((if j = -(i.val + 1 : ℤ) then c else 0) -
        (if j = (i.val + 1 : ℤ) then c else 0))) = -(j : ℚ) * c := by
  cases j with
  | ofNat k =>
    cases k with
    | zero => simp at hj
    | succ k =>
      change k + 1 ≤ n at hn
      have hk : k < n := by omega
      simpa using lagBasis_positive (⟨k, hk⟩ : Fin n) c
  | negSucc k =>
    have hk : k < n := by simpa using hn
    simpa [Int.negSucc_eq] using lagBasis_negative (⟨k, hk⟩ : Fin n) c

/-- The two moment computations agree for every input list supported on the
nonzero signed lags of the history. No numerical evaluation of all lookups is
needed: each list entry contributes through exactly one finite-sum index. -/
theorem firstMomentFrom_eq_neg_signedMomentFrom (n : ℕ) (xs : List LagWeight) (b : Block)
    (hrange : ∀ e ∈ xs, 0 < e.lag.natAbs ∧ e.lag.natAbs ≤ n) :
    firstMomentFrom n xs b = -signedMomentFrom xs b := by
  induction xs with
  | nil => simp [firstMomentFrom, signedMomentFrom, coefficientFrom]
  | cons e xs ih =>
    have he := hrange e (List.mem_cons_self)
    have hxs : ∀ a ∈ xs, 0 < a.lag.natAbs ∧ a.lag.natAbs ≤ n :=
      fun a ha ↦ hrange a (List.mem_cons_of_mem e ha)
    have hsplit : firstMomentFrom n (e :: xs) b =
        (∑ i : Fin n, (i.val + 1 : ℚ) *
          ((if e.block = b ∧ e.lag = -(i.val + 1 : ℤ) then e.coefficient else 0) -
            (if e.block = b ∧ e.lag = (i.val + 1 : ℤ) then e.coefficient else 0))) +
          firstMomentFrom n xs b := by
      simp only [firstMomentFrom, coefficientFrom_cons]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit, ih hxs, signedMomentFrom_cons]
    by_cases hb : e.block = b
    · simp only [hb, true_and, if_true]
      rw [lagBasis_sum e.lag e.coefficient he.1 he.2]
      ring
    · simp [hb]

/-- The collected rational moment is the negative of the already checked raw
signed moment. This connects the exact JSON certificate to the analytic API. -/
theorem rationalFirstMoment_eq_neg_signedMoment (b : Fin 2) :
    rationalFirstMoment b = -ADMM.RefinedEndpoint.Data.signedMoment (blockOfIndex b) := by
  change firstMomentFrom ADMM.RefinedEndpoint.Data.historyLength
    ADMM.RefinedEndpoint.Data.lagWeights (blockOfIndex b) =
      -signedMomentFrom ADMM.RefinedEndpoint.Data.lagWeights (blockOfIndex b)
  apply firstMomentFrom_eq_neg_signedMomentFrom
  intro e he
  exact of_decide_eq_true
    ((List.all_eq_true.mp ADMM.RefinedEndpoint.Data.lagWeights_in_range) e he)

end ADMM.UnitCircle.Concrete

namespace ADMM.UnitCircle

/-- The concrete real multiplier satisfies the equal-moment assumption in
Lemma C.1, using the kernel-checked rational certificate and generic regrouping. -/
theorem paperWeights_balancedMoments : BalancedMoments paperWeights := by
  unfold BalancedMoments
  rw [firstMoment_paperWeights, firstMoment_paperWeights,
    Concrete.rationalFirstMoment_eq_neg_signedMoment,
    Concrete.rationalFirstMoment_eq_neg_signedMoment]
  simp only [Concrete.blockOfIndex_zero, Concrete.blockOfIndex_one]
  rw [ADMM.RefinedEndpoint.Data.balanced_signed_moments]

end ADMM.UnitCircle
