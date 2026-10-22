/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

variable {E : Type u}

/-- A valid real logarithmic base: positive and different from `1`. -/
structure LogBase where
  val : ℝ
  pos : 0 < val
  ne_one : val ≠ 1

instance : CoeOut LogBase ℝ := ⟨LogBase.val⟩

namespace LogBase

/-- A valid logarithmic base has nonzero natural logarithm. -/
theorem log_ne_zero (b : LogBase) : Real.log (b : ℝ) ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one b.pos b.ne_one

end LogBase

/-- Definition 5.25: For a probability mass function `p` on a countable state space and a valid
logarithmic base `b > 0`, `b ≠ 1`, `entropyInBase b p` is the extended-real series
`-∑' e, p(e) * (log p(e) / log b)`, which allows the value `⊤` on countable alphabets. -/
noncomputable def entropyInBase (b : LogBase) (p : PMF E) : EReal :=
  -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)))

/-- The base-`b` entropy evaluates to its defining logarithmic series. -/
@[simp] theorem entropyInBase_def (b : LogBase) (p : PMF E) :
    entropyInBase b p =
      -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) :=
  rfl

-- Proof sketch: on a finite alphabet, rewrite the defining `tsum` as a finite sum and evaluate
-- each summand using `ENNReal.log_pos_real`, with the zero-weight terms handled separately.
/-- On a finite alphabet, the canonical `EReal` base-`b` entropy equals the usual finite Shannon
sum in logarithmic base `b`, viewed in `EReal`. -/
theorem entropyInBase_eq_sum [Fintype E] (b : LogBase) (p : PMF E) :
    entropyInBase b p =
      ((-∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal) := by
  have hterm : ∀ e : E,
      ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) =
        (((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal) := by
    intro e
    by_cases h : p e = 0
    · simp [h, Real.logb_zero]
    · rw [ENNReal.log_pos_real h (p.apply_ne_top e)]
      rw [← EReal.coe_ennreal_toReal (p.apply_ne_top e)]
      change (((p e).toReal * ((Real.log (b : ℝ))⁻¹ * Real.log (p e).toReal) : ℝ) : EReal) =
        (((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)
      exact_mod_cast (by
        simp [Real.logb, div_eq_mul_inv, mul_left_comm, mul_comm] :
          (p e).toReal * ((Real.log (b : ℝ))⁻¹ * Real.log (p e).toReal) =
            (p e).toReal * Real.logb (b : ℝ) (p e).toReal)
  calc
    entropyInBase b p =
        -∑ e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) := by
      rw [entropyInBase_def, tsum_fintype]
    _ = -∑ e : E, ((((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)) := by
      simp_rw [hterm]
    _ = ((-∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal) := by
      have hsum (s : Finset E) :
          Finset.sum s (fun e ↦ (((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)) =
            ((Finset.sum s fun e ↦ (p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal) := by
        induction s using Finset.cons_induction with
        | empty => simp
        | @cons a s ha ih =>
            calc
              Finset.sum (Finset.cons a s ha)
                  (fun e ↦ (((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)) =
                (((p a).toReal * Real.logb (b : ℝ) (p a).toReal : ℝ) : EReal) +
                  Finset.sum s
                    (fun e ↦ (((p e).toReal * Real.logb (b : ℝ) (p e).toReal : ℝ) : EReal)) := by
                simp
              _ = (((p a).toReal * Real.logb (b : ℝ) (p a).toReal : ℝ) : EReal) +
                    ((Finset.sum s
                        (fun e ↦ (p e).toReal * Real.logb (b : ℝ) (p e).toReal) : ℝ) : EReal) := by
                rw [ih]
              _ = ((((p a).toReal * Real.logb (b : ℝ) (p a).toReal) +
                      Finset.sum s
                        (fun e ↦ (p e).toReal * Real.logb (b : ℝ) (p e).toReal) : ℝ) : EReal) := by
                simp
              _ = ((Finset.sum (Finset.cons a s ha)
                      (fun e ↦ (p e).toReal * Real.logb (b : ℝ) (p e).toReal) : ℝ) : EReal) := by
                simp
      simpa using congrArg Neg.neg (hsum Finset.univ)

-- Proof sketch: apply `EReal.toReal` to `entropyInBase_eq_sum`.
/-- On a finite alphabet, the real value of the canonical base-`b` entropy is the usual finite
Shannon sum in logarithmic base `b`. -/
theorem entropyInBase_toReal_eq_sum [Fintype E] (b : LogBase) (p : PMF E) :
    (entropyInBase b p).toReal = -∑ e : E, (p e).toReal * Real.logb (b : ℝ) (p e).toReal := by
  rw [entropyInBase_eq_sum]
  simp

/-- The entropy of a probability mass function is its Shannon entropy, computed with the natural
logarithm and valued in `EReal`. -/
noncomputable def entropy (p : PMF E) : EReal :=
  entropyInBase
    ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩ p

/-- The entropy is the Shannon series `-∑' e, p(e) log p(e)` in `EReal`. -/
@[simp] theorem entropy_def (p : PMF E) :
    entropy p = -∑' e : E, ((p e : EReal) * ENNReal.log (p e)) := by
  simp [entropy, entropyInBase]

/-- The entropy is the base-`e` specialization of `entropyInBase`. -/
theorem entropy_eq_entropyInBase (p : PMF E) :
    entropy p =
      entropyInBase
        ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩ p :=
  rfl

-- Proof sketch: on a finite alphabet, rewrite the defining `tsum` as a finite sum and evaluate each
-- summand using `ENNReal.log_pos_real`, with the zero-weight terms handled separately.
/-- On a finite alphabet, the canonical `EReal` entropy equals the usual finite Shannon sum viewed
in `EReal`. -/
theorem entropy_eq_sum [Fintype E] (p : PMF E) :
    entropy p = ((-∑ e : E, (p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal) := by
  have hterm : ∀ e : E,
      ((p e : EReal) * ENNReal.log (p e)) =
        (((p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal) := by
    intro e
    by_cases h : p e = 0
    · simp [h]
    · rw [ENNReal.log_pos_real h (p.apply_ne_top e)]
      rw [← EReal.coe_ennreal_toReal (p.apply_ne_top e), ← EReal.coe_mul]
  calc
    entropy p = -∑ e : E, ((p e : EReal) * ENNReal.log (p e)) := by
      rw [entropy_def, tsum_fintype]
    _ = -∑ e : E, ((((p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal)) := by
      simp_rw [hterm]
    _ = ((-∑ e : E, (p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal) := by
      have hsum (s : Finset E) :
          Finset.sum s (fun e ↦ (((p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal)) =
            ((Finset.sum s fun e ↦ (p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal) := by
        induction s using Finset.cons_induction with
        | empty => simp
        | @cons a s ha ih =>
            calc
              Finset.sum (Finset.cons a s ha)
                  (fun e ↦ (((p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal)) =
                (((p a).toReal * Real.log ((p a).toReal) : ℝ) : EReal) +
                  Finset.sum s
                    (fun e ↦ (((p e).toReal * Real.log ((p e).toReal) : ℝ) : EReal)) := by
                simp
              _ = (((p a).toReal * Real.log ((p a).toReal) : ℝ) : EReal) +
                    ((Finset.sum s
                        (fun e ↦ (p e).toReal * Real.log ((p e).toReal)) : ℝ) : EReal) := by
                rw [ih]
              _ = ((((p a).toReal * Real.log ((p a).toReal)) +
                      Finset.sum s
                        (fun e ↦ (p e).toReal * Real.log ((p e).toReal)) : ℝ) : EReal) := by
                simp
              _ = ((Finset.sum (Finset.cons a s ha)
                      (fun e ↦ (p e).toReal * Real.log ((p e).toReal)) : ℝ) : EReal) := by
                simp
      simpa using congrArg Neg.neg (hsum Finset.univ)

-- Proof sketch: apply `EReal.toReal` to `entropy_eq_sum`.
/-- On a finite alphabet, the real value of `entropy p` is the usual finite Shannon sum. -/
theorem entropy_toReal_eq_sum [Fintype E] (p : PMF E) :
    (entropy p).toReal = -∑ e : E, (p e).toReal * Real.log ((p e).toReal) := by
  rw [entropy_eq_sum]
  simp

/-- The canonical logarithmic base `2`. -/
def binaryBase : LogBase :=
  ⟨2, by positivity, by norm_num⟩

/-- The binary entropy of a probability mass function is its base-`2` entropy. -/
noncomputable def binaryEntropy (p : PMF E) : EReal :=
  entropyInBase binaryBase p

/-- The binary entropy is the Shannon series in base `2`. -/
@[simp] theorem binaryEntropy_def (p : PMF E) :
    binaryEntropy p =
      -∑' e : E, ((p e : EReal) * (((Real.log (2 : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) :=
  rfl

/-- The binary entropy is the base-`2` specialization of `entropyInBase`. -/
theorem binaryEntropy_eq_entropyInBase (p : PMF E) :
    binaryEntropy p = entropyInBase binaryBase p :=
  rfl

-- Proof sketch: specialize `entropyInBase_toReal_eq_sum` to the canonical base `binaryBase`.
/-- On a finite alphabet, the real value of the canonical binary entropy is the usual finite
base-`2` Shannon sum. -/
theorem binaryEntropy_toReal_eq_sum [Fintype E] (p : PMF E) :
    (binaryEntropy p).toReal = -∑ e : E, (p e).toReal * Real.logb 2 (p e).toReal := by
  simpa [binaryEntropy_eq_entropyInBase] using entropyInBase_toReal_eq_sum binaryBase p
