/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_18.CirculantExtension
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_1
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6.Comparison

public section

/- Remark 5.18 records the standard circulant-extension realization of a
Toeplitz matrix and its FFT/ifft computational consequence. -/

open scoped Matrix

universe u

variable {α : Type u}

/-- The source compact Toeplitz vector
`(t 1, ..., t (n - 1), 0, t (1 - n), ..., t (-1))` translated into the
diagonal-indexed owner `Matrix.toeplitzByDiag n`. Negative diagonal indices
encode upper diagonals, while positive diagonal indices encode lower diagonals. -/
def circulantExtensionOffDiag [Zero α] (n : ℕ) (t : ℤ → α) : ℤ → α :=
  fun k ↦
    if k = 0 then
      0
    else if k < 0 then
      t (k + n)
    else
      t (k - n)

/-- Helper for Remark 5.18: the embedded left-half index has the same natural
value as its source index. -/
lemma circulantExtensionEmbeddedCastAddVal
    (n : ℕ) (i : Fin n) :
    (((finCongr (two_mul n)).symm (Fin.castAdd n i) : Fin (2 * n)) : ℕ) = i := by
  -- Rewrite the equivalence back to `Fin (n + n)` and read off the `castAdd` value.
  exact finCongr_symm_apply_coe (two_mul n) (Fin.castAdd n i)

/-- Helper for Remark 5.18: the embedded right-half index has natural value
`n + i`. -/
lemma circulantExtensionEmbeddedNatAddVal
    (n : ℕ) (i : Fin n) :
    (((finCongr (two_mul n)).symm (Fin.natAdd n i) : Fin (2 * n)) : ℕ) = n + i := by
  -- Rewrite the equivalence back to `Fin (n + n)` and read off the `natAdd` value.
  exact finCongr_symm_apply_coe (two_mul n) (Fin.natAdd n i)

/-- Helper for Remark 5.18: the two embedded halves compare exactly as their
natural values suggest. -/
lemma circulantExtensionEmbeddedOrderFacts
    (n : ℕ) (i j : Fin n) :
    ((((finCongr (two_mul n)).symm (Fin.castAdd n j) : Fin (2 * n)) ≤
        ((finCongr (two_mul n)).symm (Fin.castAdd n i) : Fin (2 * n))) ↔
      j ≤ i) ∧
    ((((finCongr (two_mul n)).symm (Fin.natAdd n j) : Fin (2 * n)) ≤
        ((finCongr (two_mul n)).symm (Fin.natAdd n i) : Fin (2 * n))) ↔
      j ≤ i) ∧
    ¬ ((finCongr (two_mul n)).symm (Fin.natAdd n j) : Fin (2 * n)) ≤
        ((finCongr (two_mul n)).symm (Fin.castAdd n i) : Fin (2 * n)) ∧
    ((finCongr (two_mul n)).symm (Fin.castAdd n j) : Fin (2 * n)) ≤
      ((finCongr (two_mul n)).symm (Fin.natAdd n i) : Fin (2 * n)) := by
  constructor
  · -- Left-half indices preserve the original `Fin n` order.
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val,
      circulantExtensionEmbeddedCastAddVal, circulantExtensionEmbeddedCastAddVal]
  constructor
  · -- Right-half indices preserve the original order after the common `n`-shift.
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val,
      circulantExtensionEmbeddedNatAddVal, circulantExtensionEmbeddedNatAddVal]
    omega
  constructor
  · -- Every right-half index is strictly larger than every left-half index.
    rw [Fin.le_iff_val_le_val, circulantExtensionEmbeddedNatAddVal,
      circulantExtensionEmbeddedCastAddVal]
    omega
  · -- Every left-half index lies weakly below every right-half index.
    rw [Fin.le_iff_val_le_val, circulantExtensionEmbeddedCastAddVal,
      circulantExtensionEmbeddedNatAddVal]
    omega

/-- Helper for Remark 5.18: subtracting two embedded indices from the same half
of `Fin (2 * n)` produces the wrapped difference determined by `i - j`. -/
lemma circulantExtensionEmbeddedSub_sameHalfVal
    (n : ℕ) (i j : Fin n) :
    (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
        ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ) =
      if j ≤ i then (i : ℕ) - (j : ℕ) else 2 * n + (i : ℕ) - (j : ℕ)) ∧
    (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
        ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ) =
      if j ≤ i then (i : ℕ) - (j : ℕ) else 2 * n + (i : ℕ) - (j : ℕ)) := by
  -- Route correction: discharge the wrapped-subtraction branch directly from the
  -- embedded order facts instead of normalizing transported comparisons further.
  constructor
  · -- Convert the left-half subtraction to the integer formula and then return to naturals.
    by_cases h : j ≤ i
    · let a : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.castAdd n i)
      let b : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.castAdd n j)
      have hsubZ : ((a - b).val : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) := by
        -- The same-half order facts force the nonwrapped branch.
        have hbase := Fin.intCast_val_sub_eq_sub_add_ite a b
        have hbranch : Fin.castAdd n j ≤ Fin.castAdd n i := by
          rw [Fin.le_iff_val_le_val]
          simpa using h
        simpa [a, b, circulantExtensionEmbeddedCastAddVal, hbranch] using hbase
      have hsub : (a - b).val = (i : ℕ) - (j : ℕ) := by
        omega
      simpa [a, b, h] using hsub
    · let a : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.castAdd n i)
      let b : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.castAdd n j)
      have hnot : ¬ Fin.castAdd n j ≤ Fin.castAdd n i := by
        -- The same order equivalence rules out the nonwrapped branch.
        intro hji
        apply h
        rw [Fin.le_iff_val_le_val] at hji
        exact hji
      have hsubZ : ((a - b).val : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) + 2 * n := by
        -- Once the wrapped branch is chosen, only plain arithmetic remains.
        have hbase := Fin.intCast_val_sub_eq_sub_add_ite a b
        simpa [a, b, circulantExtensionEmbeddedCastAddVal, hnot] using hbase
      have hsub : (a - b).val = 2 * n + (i : ℕ) - (j : ℕ) := by
        omega
      simpa [a, b, h] using hsub
  · -- The right-half subtraction has the same branch structure after the common shift by `n`.
    by_cases h : j ≤ i
    · let a : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.natAdd n i)
      let b : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.natAdd n j)
      have hsubZ : ((a - b).val : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) := by
        -- The order-preserving embedding cancels the common shift by `n`.
        have hbase := Fin.intCast_val_sub_eq_sub_add_ite a b
        simpa [a, b, circulantExtensionEmbeddedNatAddVal, h] using hbase
      have hsub : (a - b).val = (i : ℕ) - (j : ℕ) := by
        omega
      simpa [a, b, h] using hsub
    · let a : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.natAdd n i)
      let b : Fin (2 * n) := (finCongr (two_mul n)).symm (Fin.natAdd n j)
      have hnot : ¬ Fin.natAdd n j ≤ Fin.natAdd n i := by
        -- The shifted embedding reflects the original order, so `j > i` wraps here as well.
        intro hji
        exact h ((Fin.natAdd_le_natAdd_iff n).mp hji)
      have hsubZ : ((a - b).val : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) + 2 * n := by
        -- The wrapped branch again reduces to a plain integer identity.
        have hbase := Fin.intCast_val_sub_eq_sub_add_ite a b
        simpa [a, b, circulantExtensionEmbeddedNatAddVal, h] using hbase
      have hsub : (a - b).val = 2 * n + (i : ℕ) - (j : ℕ) := by
        omega
      simpa [a, b, h] using hsub

/-- Helper for Remark 5.18: subtracting embedded indices from opposite halves of
`Fin (2 * n)` always lands at the raw value `n + i - j`. -/
lemma circulantExtensionEmbeddedSub_crossHalfVal
    (n : ℕ) (i j : Fin n) :
    (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
        ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ) =
      n + (i : ℕ) - (j : ℕ)) ∧
    (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
        ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ) =
      n + (i : ℕ) - (j : ℕ)) := by
  -- Route correction: use the fixed opposite-half order facts to choose the
  -- correct subtraction branch immediately, then finish on plain arithmetic.
  constructor
  · -- Left-half minus right-half always wraps once around the length `2 * n`.
    have hcrossLeft :
        ¬ ((finCongr (two_mul n)).symm (Fin.natAdd n j) : Fin (2 * n)) ≤
            ((finCongr (two_mul n)).symm (Fin.castAdd n i) : Fin (2 * n)) := by
      -- Every right-half index is strictly larger than every left-half index.
      rw [Fin.le_iff_val_le_val, circulantExtensionEmbeddedCastAddVal,
        circulantExtensionEmbeddedNatAddVal]
      omega
    have hsubZ :
        (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℤ)) =
          (n + (i : ℕ) - (j : ℕ) : ℕ) := by
      -- Use the integer-coercion subtraction formula so the arithmetic stays on plain `ℤ`.
      have hbase := Fin.coe_int_sub_eq_ite
        ((finCongr (two_mul n)).symm (Fin.castAdd n i))
        ((finCongr (two_mul n)).symm (Fin.natAdd n j))
      rw [if_neg hcrossLeft, circulantExtensionEmbeddedCastAddVal,
        circulantExtensionEmbeddedNatAddVal] at hbase
      omega
    exact_mod_cast hsubZ
  · -- Right-half minus left-half never wraps because every right-half index is larger.
    have hcrossRight :
        ((finCongr (two_mul n)).symm (Fin.castAdd n j) : Fin (2 * n)) ≤
          ((finCongr (two_mul n)).symm (Fin.natAdd n i) : Fin (2 * n)) := by
      -- Every left-half index lies below every right-half index.
      rw [Fin.le_iff_val_le_val, circulantExtensionEmbeddedCastAddVal,
        circulantExtensionEmbeddedNatAddVal]
      omega
    have hsubZ :
        (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℤ)) =
          (n + (i : ℕ) - (j : ℕ) : ℕ) := by
      -- The nonwrapped branch is again a direct integer identity.
      have hbase := Fin.coe_int_sub_eq_ite
        ((finCongr (two_mul n)).symm (Fin.natAdd n i))
        ((finCongr (two_mul n)).symm (Fin.castAdd n j))
      rw [if_pos hcrossRight, circulantExtensionEmbeddedCastAddVal,
        circulantExtensionEmbeddedNatAddVal] at hbase
      omega
    exact_mod_cast hsubZ

/-- Helper for Remark 5.18: the left-left block of the circulant extension
recovers the original Toeplitz coefficients. -/
lemma circulantExtensionVector_castAdd_sub_castAdd [Zero α]
    (n : ℕ) (t : ℤ → α) (i j : Fin n) :
    circulantExtensionVector n t
        (((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
          ((finCongr (two_mul n)).symm (Fin.castAdd n j))) =
      t (((i : ℕ) : ℤ) - (j : ℕ)) := by
  -- Route correction: normalize the embedded subtraction first, then evaluate the piecewise vector.
  by_cases h : j ≤ i
  · -- In the nonwrapped case the subtraction stays in the leading half.
    have hval := (circulantExtensionEmbeddedSub_sameHalfVal n i j).1
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ)) =
          (i : ℕ) - (j : ℕ) := by
      simpa [h] using hval
    have hlt : ((i : ℕ) - (j : ℕ)) < n := by
      omega
    have harr : ((((i : ℕ) - (j : ℕ)) : ℕ) : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) := by
      omega
    rw [circulantExtensionVector_apply, hsub]
    simp [hlt, harr]
  · -- In the wrapped case the vector enters the trailing half and subtracts `2 * n`.
    have hval := (circulantExtensionEmbeddedSub_sameHalfVal n i j).1
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ)) =
          2 * n + (i : ℕ) - (j : ℕ) := by
      simpa [h] using hval
    have hlt : ¬ (2 * n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
      omega
    have hmid : ¬ (2 * n + (i : ℕ) - (j : ℕ) : ℕ) = n := by
      omega
    have harr :
        (((2 * n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) - (2 * n : ℤ)) =
          ((i : ℕ) : ℤ) - (j : ℕ) := by
      omega
    rw [circulantExtensionVector_apply, hsub]
    simp [hlt, hmid, harr]

/-- Helper for Remark 5.18: the right-right block of the circulant extension
matches the same Toeplitz coefficients as the left-left block. -/
lemma circulantExtensionVector_natAdd_sub_natAdd [Zero α]
    (n : ℕ) (t : ℤ → α) (i j : Fin n) :
    circulantExtensionVector n t
        (((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
          ((finCongr (two_mul n)).symm (Fin.natAdd n j))) =
      t (((i : ℕ) : ℤ) - (j : ℕ)) := by
  -- Evaluate the right-right block by the same wrapped subtraction formula as the left-left block.
  by_cases h : j ≤ i
  · -- When `j ≤ i`, the common `n`-shift cancels and the index stays in the leading half.
    have hval := (circulantExtensionEmbeddedSub_sameHalfVal n i j).2
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ)) =
          (i : ℕ) - (j : ℕ) := by
      simpa [h] using hval
    have hlt : ((i : ℕ) - (j : ℕ)) < n := by
      omega
    have harr : ((((i : ℕ) - (j : ℕ)) : ℕ) : ℤ) = ((i : ℕ) : ℤ) - (j : ℕ) := by
      omega
    rw [circulantExtensionVector_apply, hsub]
    simp [hlt, harr]
  · -- When `j > i`, the same wrapped branch appears as in the left-left block.
    have hval := (circulantExtensionEmbeddedSub_sameHalfVal n i j).2
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ)) =
          2 * n + (i : ℕ) - (j : ℕ) := by
      simpa [h] using hval
    have hlt : ¬ (2 * n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
      omega
    have hmid : ¬ (2 * n + (i : ℕ) - (j : ℕ) : ℕ) = n := by
      omega
    have harr :
        (((2 * n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) - (2 * n : ℤ)) =
          ((i : ℕ) : ℤ) - (j : ℕ) := by
      omega
    rw [circulantExtensionVector_apply, hsub]
    simp [hlt, hmid, harr]

/-- Helper for Remark 5.18: the left-right block of the circulant extension
matches the companion Toeplitz block `circulantExtensionOffDiag`. -/
lemma circulantExtensionVector_castAdd_sub_natAdd [Zero α]
    (n : ℕ) (t : ℤ → α) (i j : Fin n) :
    circulantExtensionVector n t
        (((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
          ((finCongr (two_mul n)).symm (Fin.natAdd n j))) =
      circulantExtensionOffDiag n t (((i : ℕ) : ℤ) - (j : ℕ)) := by
  -- Normalize the cross-half subtraction once, then match the three sign cases of `i - j`.
  have hval := (circulantExtensionEmbeddedSub_crossHalfVal n i j).1
  by_cases hij : i < j
  · -- A negative diagonal index lands in the leading half and matches the `k + n` branch.
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ)) =
          n + (i : ℕ) - (j : ℕ) := by
      simpa using hval
    have hlt : (n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
      omega
    have hkneg : ((i : ℕ) : ℤ) - (j : ℕ) < 0 := by
      omega
    have hkne : ((i : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
      omega
    have harr :
        ((n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) =
          (((i : ℕ) : ℤ) - (j : ℕ)) + n := by
      omega
    rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
    simp [hlt, hkneg, hkne, harr]
  · by_cases hji : j < i
    · -- A positive diagonal index lands in the trailing half and matches the `k - n` branch.
      have hsub :
          (((((finCongr (two_mul n)).symm (Fin.castAdd n i)) -
              ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ)) =
            n + (i : ℕ) - (j : ℕ) := by
        simpa using hval
      have hlt : ¬ (n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
        omega
      have hmid : ¬ (n + (i : ℕ) - (j : ℕ) : ℕ) = n := by
        omega
      have hkne : ((i : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
        omega
      have harr :
          (((n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) - (2 * n : ℤ)) =
            (((i : ℕ) : ℤ) - (j : ℕ)) - n := by
        omega
      rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
      simp [hlt, hmid, hkne, harr, hij]
    · -- The middle index `n` corresponds exactly to the zero diagonal coefficient.
      have hij_eq : i = j := by
        omega
      subst i
      have hsub :
          (((((finCongr (two_mul n)).symm (Fin.castAdd n j)) -
              ((finCongr (two_mul n)).symm (Fin.natAdd n j)) : Fin (2 * n)) : ℕ)) =
            n := by
        simpa using hval
      rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
      simp

/-- Helper for Remark 5.18: the right-left block of the circulant extension
matches the same companion Toeplitz block. -/
lemma circulantExtensionVector_natAdd_sub_castAdd [Zero α]
    (n : ℕ) (t : ℤ → α) (i j : Fin n) :
    circulantExtensionVector n t
        (((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
          ((finCongr (two_mul n)).symm (Fin.castAdd n j))) =
      circulantExtensionOffDiag n t (((i : ℕ) : ℤ) - (j : ℕ)) := by
  -- The symmetric cross-half block has the same three sign cases as the left-right block.
  have hval := (circulantExtensionEmbeddedSub_crossHalfVal n i j).2
  by_cases hij : i < j
  · -- Negative diagonals remain in the leading half and use the `k + n` branch.
    have hsub :
        (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
            ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ)) =
          n + (i : ℕ) - (j : ℕ) := by
      simpa using hval
    have hlt : (n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
      omega
    have hkneg : ((i : ℕ) : ℤ) - (j : ℕ) < 0 := by
      omega
    have hkne : ((i : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
      omega
    have harr :
        ((n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) =
          (((i : ℕ) : ℤ) - (j : ℕ)) + n := by
      omega
    rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
    simp [hlt, hkneg, hkne, harr]
  · by_cases hji : j < i
    · -- Positive diagonals land in the trailing half and use the `k - n` branch.
      have hsub :
          (((((finCongr (two_mul n)).symm (Fin.natAdd n i)) -
              ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ)) =
            n + (i : ℕ) - (j : ℕ) := by
        simpa using hval
      have hlt : ¬ (n + (i : ℕ) - (j : ℕ) : ℕ) < n := by
        omega
      have hmid : ¬ (n + (i : ℕ) - (j : ℕ) : ℕ) = n := by
        omega
      have hkne : ((i : ℕ) : ℤ) - (j : ℕ) ≠ 0 := by
        omega
      have harr :
          (((n + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) - (2 * n : ℤ)) =
            (((i : ℕ) : ℤ) - (j : ℕ)) - n := by
        omega
      rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
      simp [hlt, hmid, hkne, harr, hij]
    · -- Equality of indices gives the midpoint `n`, hence the zero off-diagonal coefficient.
      have hij_eq : i = j := by
        omega
      subst i
      have hsub :
          (((((finCongr (two_mul n)).symm (Fin.natAdd n j)) -
              ((finCongr (two_mul n)).symm (Fin.castAdd n j)) : Fin (2 * n)) : ℕ)) =
            n := by
        simpa using hval
      rw [circulantExtensionVector_apply, hsub, circulantExtensionOffDiag]
      simp

/-- Reindexing the circulant matrix generated by
`circulantExtensionVector n t` along `finSumFinEquiv.symm` yields the block
matrix `Matrix.fromBlocks T S S T`, where
`T = Matrix.toeplitzByDiag n t` and
the source block `S = toeplitz(s)` with
`s = (t 1, ..., t (n - 1), 0, t (1 - n), ..., t (-1))`
is represented by `Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t)`. -/
theorem circulantExtension_reindex_eq_fromBlocks [Zero α] (n : ℕ) (t : ℤ → α) :
    Matrix.reindex
        ((finCongr (two_mul n)).trans finSumFinEquiv.symm)
        ((finCongr (two_mul n)).trans finSumFinEquiv.symm)
        (Matrix.circulant (circulantExtensionVector n t)) =
      Matrix.fromBlocks
        (Matrix.toeplitzByDiag n t)
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n t) := by
  -- Compare the reindexed circulant entry-by-entry with the four block formulas.
  ext x y
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          -- Top-left block.
          simpa [Matrix.reindex_apply, Matrix.circulant_apply, Matrix.fromBlocks_apply₁₁,
            Matrix.toeplitzByDiag_apply] using
            circulantExtensionVector_castAdd_sub_castAdd n t i j
      | inr j =>
          -- Top-right block.
          simpa [Matrix.reindex_apply, Matrix.circulant_apply, Matrix.fromBlocks_apply₁₂,
            Matrix.toeplitzByDiag_apply] using
            circulantExtensionVector_castAdd_sub_natAdd n t i j
  | inr i =>
      cases y with
      | inl j =>
          -- Bottom-left block.
          simpa [Matrix.reindex_apply, Matrix.circulant_apply, Matrix.fromBlocks_apply₂₁,
            Matrix.toeplitzByDiag_apply] using
            circulantExtensionVector_natAdd_sub_castAdd n t i j
      | inr j =>
          -- Bottom-right block.
          simpa [Matrix.reindex_apply, Matrix.circulant_apply, Matrix.fromBlocks_apply₂₂,
            Matrix.toeplitzByDiag_apply] using
            circulantExtensionVector_natAdd_sub_natAdd n t i j

/-- Multiplying the block circulant extension
`Matrix.fromBlocks T S S T` by the zero-padded vector `Sum.elim v 0` yields the
block vector whose top half is `T *ᵥ v` and whose bottom half is `S *ᵥ v`. -/
theorem circulantExtension_mulVec_zeroPad [NonUnitalNonAssocSemiring α]
    (n : ℕ) (t : ℤ → α) (v : Fin n → α) :
    Matrix.fromBlocks
        (Matrix.toeplitzByDiag n t)
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n t) *ᵥ
          Sum.elim v 0 =
      Sum.elim
        ((Matrix.toeplitzByDiag n t) *ᵥ v)
        ((Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t)) *ᵥ v) := by
  -- Expand the block product and collapse every contribution coming from the zero-padded half.
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- Under the `finSumFinEquiv.symm` reindexing, the
zero-padded vector `zeroPadVector n v` is exactly the block vector
`Sum.elim v 0`. -/
theorem zeroPadVector_reindex_eq_sumElim [Zero α] (n : ℕ) (v : Fin n → α) :
    (fun x : Fin n ⊕ Fin n ↦
      zeroPadVector n v
        (((finCongr (two_mul n)).trans finSumFinEquiv.symm).symm x)) =
      Sum.elim v 0 := by
  -- Reindexing splits the padded vector into its original part and the zero tail.
  ext x
  cases x with
  | inl i =>
      simp [zeroPadVector_apply]
  | inr i =>
      simp [zeroPadVector_apply]

/-- After computing the circulant-extension product by the
source-facing FFT/ifft formula and reindexing by `finSumFinEquiv.symm`, one
recovers the block vector whose leading `n` entries are
`(Matrix.toeplitzByDiag n t) *ᵥ v` and whose trailing `n` entries are the
companion source block product. -/
theorem circulantExtension_circulant_mulVec_zeroPad_eq_ifft_mul_fft
    (n : ℕ) [NeZero n] (t : ℤ → ℂ) (v : Fin n → ℂ) :
    (fun x : Fin n ⊕ Fin n ↦
      Matrix.ifft (2 * n)
        (Matrix.fft (2 * n) (circulantExtensionVector n t) *
          Matrix.fft (2 * n) (zeroPadVector n v))
        (((finCongr (two_mul n)).trans finSumFinEquiv.symm).symm x)) =
      Sum.elim
        ((Matrix.toeplitzByDiag n t) *ᵥ v)
        ((Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t)) *ᵥ v) := by
  -- Keep the FFT identity in the original `Fin (2 * n)` coordinates before transporting it.
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (two_mul n)).trans finSumFinEquiv.symm
  have hcirculant :
      Matrix.circulant (circulantExtensionVector n t) *ᵥ zeroPadVector n v =
        Matrix.ifft (2 * n)
          (Matrix.fft (2 * n) (circulantExtensionVector n t) *
            Matrix.fft (2 * n) (zeroPadVector n v)) := by
    -- This is the standard circulant FFT/ifft identity specialized to the extension vector.
    simpa
      [Matrix.discreteConvolution_def,
        Matrix.toeplitzByDiag_periodicExtension_eq_circulant]
      using
      (Matrix.periodicExtension_discreteConvolution_eq_ifft_mul_fft (2 * n)
        (WithLp.toLp 2 (circulantExtensionVector n t))
        (WithLp.toLp 2 (zeroPadVector n v)))
  have hzeroPad :
      (Sum.elim v 0) ∘ e = zeroPadVector n v := by
    -- Reexpress the padded vector in the sum-indexed coordinates used by the block matrix.
    ext x
    simpa [e] using (congrArg
      (fun f : Fin n ⊕ Fin n → ℂ ↦ f (e x))
      (zeroPadVector_reindex_eq_sumElim n v)).symm
  have hreindexMul :
      Matrix.reindex e e (Matrix.circulant (circulantExtensionVector n t)) *ᵥ Sum.elim v 0 =
        (fun x : Fin n ⊕ Fin n ↦
          Matrix.ifft (2 * n)
            (Matrix.fft (2 * n) (circulantExtensionVector n t) *
              Matrix.fft (2 * n) (zeroPadVector n v))
            (e.symm x)) := by
    -- Transport the circulant-product identity through the same row/column equivalence.
    calc
      Matrix.reindex e e (Matrix.circulant (circulantExtensionVector n t)) *ᵥ Sum.elim v 0
          = (Matrix.circulant (circulantExtensionVector n t) *ᵥ ((Sum.elim v 0) ∘ e)) ∘ e.symm := by
              simpa [Matrix.reindex_apply, e] using
                (Matrix.submatrix_mulVec_equiv
                  (Matrix.circulant (circulantExtensionVector n t)) (Sum.elim v 0) e.symm e.symm)
      _ = (Matrix.circulant (circulantExtensionVector n t) *ᵥ zeroPadVector n v) ∘ e.symm := by
            rw [hzeroPad]
      _ = (fun x : Fin n ⊕ Fin n ↦
            Matrix.ifft (2 * n)
              (Matrix.fft (2 * n) (circulantExtensionVector n t) *
                Matrix.fft (2 * n) (zeroPadVector n v))
              (e.symm x)) := by
            ext x
            simpa [e] using congrArg
              (fun f : Fin (2 * n) → ℂ ↦ f (e.symm x))
              hcirculant
  -- Finish by replacing the reindexed circulant with its block form and then
  -- use the block mulVec calculation.
  calc
    (fun x : Fin n ⊕ Fin n ↦
      Matrix.ifft (2 * n)
        (Matrix.fft (2 * n) (circulantExtensionVector n t) *
          Matrix.fft (2 * n) (zeroPadVector n v))
        (((finCongr (two_mul n)).trans finSumFinEquiv.symm).symm x))
        =
      Matrix.reindex e e (Matrix.circulant (circulantExtensionVector n t)) *ᵥ Sum.elim v 0 := by
        simpa [e] using hreindexMul.symm
    _ =
      Matrix.fromBlocks
        (Matrix.toeplitzByDiag n t)
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t))
        (Matrix.toeplitzByDiag n t) *ᵥ Sum.elim v 0 := by
          rw [circulantExtension_reindex_eq_fromBlocks]
    _ =
      Sum.elim
        ((Matrix.toeplitzByDiag n t) *ᵥ v)
        ((Matrix.toeplitzByDiag n (circulantExtensionOffDiag n t)) *ᵥ v) := by
          exact circulantExtension_mulVec_zeroPad n t v

/-- Remark 5.18. Extracting the first `n` components of the
source-facing FFT/ifft circulant-extension product recovers the Toeplitz
matrix-vector product `(Matrix.toeplitzByDiag n t) *ᵥ v`. -/
theorem circulantExtension_ifft_mul_fft_leading_eq_toeplitz_mulVec
    (n : ℕ) [NeZero n] (t : ℤ → ℂ) (v : Fin n → ℂ) :
    (fun i : Fin n ↦
      Matrix.ifft (2 * n)
        (Matrix.fft (2 * n) (circulantExtensionVector n t) *
          Matrix.fft (2 * n) (zeroPadVector n v))
        (((finCongr (two_mul n)).trans finSumFinEquiv.symm).symm (Sum.inl i))) =
      (Matrix.toeplitzByDiag n t) *ᵥ v := by
  -- Evaluate the block-vector identity on the leading summand.
  ext i
  simpa using congrArg
    (fun f : Fin n ⊕ Fin n → ℂ ↦ f (Sum.inl i))
    (circulantExtension_circulant_mulVec_zeroPad_eq_ifft_mul_fft n t v)
