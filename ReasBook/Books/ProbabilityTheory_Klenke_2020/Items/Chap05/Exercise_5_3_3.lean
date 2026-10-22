/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Lemma_5_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

variable {E : Type u}

/-- Helper for Exercise 5.3.3: each Shannon entropy summand `p(e) log p(e)` is nonpositive. -/
private theorem entropySummand_nonpos (p : PMF E) (e : E) :
    ((p e : EReal) * ENNReal.log (p e)) ≤ 0 := by
  -- A pmf value is nonnegative, while its logarithm is nonpositive because `p e ≤ 1`.
  have hp_nonneg : (0 : EReal) ≤ (p e : EReal) := by
    exact_mod_cast (show (0 : ENNReal) ≤ p e by simp)
  have hlog_nonpos : ENNReal.log (p e) ≤ 0 := by
    rw [ENNReal.log_le_zero_iff]
    exact p.coe_le_one e
  exact mul_nonpos_of_nonneg_of_nonpos hp_nonneg hlog_nonpos

-- Proof sketch: expand `entropy` as the Shannon sum `-∑ p(e) log p(e)` and use the standard
-- inequality `x * log x ≤ 0` on `[0,1]` for each probability weight; this does not use
-- finiteness.
/-- For Exercise 5.3.3, entropy is bounded below by `0`. -/
theorem entropy_nonneg (p : PMF E) :
    0 ≤ entropy p := by
  -- Expand `entropy` into its defining series and show that the series itself is nonpositive.
  rw [entropy_def]
  have hsum_nonpos : (∑' e : E, ((p e : EReal) * ENNReal.log (p e))) ≤ 0 := by
    refine tsum_nonpos ?_
    intro e
    exact entropySummand_nonpos p e
  -- Negating the nonpositive defining series gives the claimed lower bound.
  simpa using (EReal.neg_le_neg_iff.2 hsum_nonpos)

-- Proof sketch: evaluate the entropy of `PMF.pure e`; the pmf is `1` at `e` and `0` elsewhere, so
-- every summand vanishes; this does not use finiteness.
/-- For Exercise 5.3.3, a Dirac mass has entropy `0`. -/
theorem entropy_pure_eq_zero (e : E) :
    entropy (PMF.pure e) = 0 := by
  rw [entropy_def, tsum_eq_single e]
  · simp
  · intro e' he'
    simp [PMF.pure_apply, he']

section Fintype

variable [Fintype E]

/-- Helper for Exercise 5.3.3: on a finite alphabet, the real masses of a probability mass
function sum to `1`. -/
private theorem sumToRealPmf (p : PMF E) :
    ∑ e : E, (p e).toReal = 1 := by
  -- Rewrite the finite sum as a `tsum` and then apply `ENNReal.tsum_toReal_eq`.
  have htsum :
      (∑' e : E, p e).toReal = ∑' e : E, (p e).toReal :=
    ENNReal.tsum_toReal_eq fun e ↦ p.apply_ne_top e
  rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
  simpa using htsum.symm

/-- Helper for Exercise 5.3.3: the cross-entropy against the uniform pmf is exactly
`log (Fintype.card E)`. -/
private theorem crossEntropy_uniformOfFintype_eq_log_card [Nonempty E] (p : PMF E) :
    crossEntropyInBase
        ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
        p (PMF.uniformOfFintype E) =
      (Real.log (Fintype.card E) : EReal) := by
  have hcard_ne_zero_nat : Fintype.card E ≠ 0 := Fintype.card_ne_zero
  have hcard_ne_zero_real : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard_ne_zero_nat
  have huniform_ne_zero : ∀ e : E, PMF.uniformOfFintype E e ≠ 0 := by
    intro e
    simp [PMF.uniformOfFintype_apply]
  let g : E → ℝ := fun e ↦ (p e).toReal * Real.log ((PMF.uniformOfFintype E e).toReal)
  have hterm : ∀ e : E,
      ((p e : EReal) * ENNReal.log (PMF.uniformOfFintype E e)) =
        ((g e : ℝ) : EReal) := by
    intro e
    -- Convert the strictly positive uniform mass to an ordinary real logarithm.
    rw [ENNReal.log_pos_real (huniform_ne_zero e) ((PMF.uniformOfFintype E).apply_ne_top e)]
    rw [← EReal.coe_ennreal_toReal (p.apply_ne_top e), ← EReal.coe_mul]
  calc
    crossEntropyInBase
        ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
        p (PMF.uniformOfFintype E) =
        -∑ e : E, ((p e : EReal) * ENNReal.log (PMF.uniformOfFintype E e)) := by
      -- For the natural logarithm base, the base-change factor is `1`.
      rw [crossEntropyInBase_def, tsum_fintype]
      simp
    _ = -∑ e : E, (((g e : ℝ) : EReal)) := by
      simp_rw [hterm]
    _ = ((-∑ e : E, g e : ℝ) : EReal) := by
      -- Move the finite real sum through the `EReal` coercion once and for all.
      have hsum (s : Finset E) :
          Finset.sum s (fun e ↦ ((g e : ℝ) : EReal)) =
            ((Finset.sum s g : ℝ) : EReal) := by
        induction s using Finset.cons_induction with
        | empty => simp
        | @cons a s ha ih =>
            calc
              Finset.sum (Finset.cons a s ha) (fun e ↦ ((g e : ℝ) : EReal)) =
                ((g a : ℝ) : EReal) + Finset.sum s (fun e ↦ ((g e : ℝ) : EReal)) := by
                simp
              _ = ((g a : ℝ) : EReal) + ((Finset.sum s g : ℝ) : EReal) := by
                rw [ih]
              _ = (((g a + Finset.sum s g : ℝ)) : EReal) := by
                simp
              _ = ((Finset.sum (Finset.cons a s ha) g : ℝ) : EReal) := by
                simp
      simpa using congrArg Neg.neg (hsum Finset.univ)
    _ = ((-∑ e : E, (p e).toReal * Real.log ((Fintype.card E : ℝ)⁻¹) : ℝ) : EReal) := by
      simp [g, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    _ = (Real.log (Fintype.card E) : EReal) := by
      -- The logarithm is constant across the finite sum, and the total mass is `1`.
      congr 1
      calc
        -∑ e : E, (p e).toReal * Real.log ((Fintype.card E : ℝ)⁻¹) =
            -((∑ e : E, (p e).toReal) * Real.log ((Fintype.card E : ℝ)⁻¹)) := by
          rw [Finset.sum_mul]
        _ = -(1 * Real.log ((Fintype.card E : ℝ)⁻¹)) := by
          rw [sumToRealPmf p]
        _ = -Real.log ((Fintype.card E : ℝ)⁻¹) := by ring
        _ = Real.log (Fintype.card E) := by
          rw [Real.log_inv]
          ring

-- Proof sketch: apply the classical finite-alphabet entropy bound, for instance via Jensen's
-- inequality for the concave function `x ↦ -x log x` under the constraint `∑ p(e) = 1`.
/-- Exercise 5.3.3: on a finite set, entropy is bounded above by `log (#E)`. -/
theorem entropy_le_log_card (p : PMF E) :
    entropy p ≤ Real.log (Fintype.card E) := by
  letI : Nonempty E := ⟨p.support_nonempty.some⟩
  -- Route correction: use the existing cross-entropy inequality against the uniform pmf.
  have hq : (∑' e : E, PMF.uniformOfFintype E e) ≤ 1 := by
    exact le_of_eq (PMF.uniformOfFintype E).tsum_coe
  have hb : 1 <
      ((⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩ : LogBase) :
        ℝ) := by
    exact Real.one_lt_exp_iff.2 zero_lt_one
  calc
    entropy p =
        entropyInBase
          ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩ p := by
      exact entropy_eq_entropyInBase p
    _ ≤ crossEntropyInBase
          ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
          p (PMF.uniformOfFintype E) := by
      exact entropyInBase_le_crossEntropyInBase
        ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
        hb p (PMF.uniformOfFintype E) hq
    _ = (Real.log (Fintype.card E) : EReal) := by
      exact crossEntropy_uniformOfFintype_eq_log_card p

-- Proof sketch: compute the entropy of `PMF.uniformOfFintype E`; every atom has weight
-- `(Fintype.card E)⁻¹`, so the sum simplifies to `log (Fintype.card E)`.
/-- For Exercise 5.3.3, the uniform distribution on a finite nonempty set has entropy
`log (#E)`. -/
theorem entropy_uniformOfFintype_eq_log_card [Nonempty E] :
    entropy (PMF.uniformOfFintype E) = Real.log (Fintype.card E) := by
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_inv,
    Real.log_inv]

end Fintype
