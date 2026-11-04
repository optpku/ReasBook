/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Lemmas

public section

/-- The least common multiple of the denominators of the coordinates of a rational vector. -/
def rational_vector_common_denominator {n : ℕ} (v : Fin n → ℚ) : ℕ :=
  Finset.univ.lcm fun i : Fin n ↦ (v i).den

/-- The integer vector obtained by scaling a rational vector by the least common multiple of its
coordinate denominators. -/
def common_denominator_scaled_vector {n : ℕ} (v : Fin n → ℚ) : Fin n → ℤ :=
  fun i ↦ (((rational_vector_common_denominator v : ℚ) * v i).num)

/-- Each coordinate denominator divides the common denominator of the whole vector. -/
theorem dvd_rational_vector_common_denominator {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    (v i).den ∣ rational_vector_common_denominator v := by
  -- Every coordinate denominator occurs in the finite lcm.
  unfold rational_vector_common_denominator
  exact Finset.dvd_lcm (Finset.mem_univ i)

/-- Casting the denominator-cleared integer vector back to `ℚ` recovers the scalar multiple by the
common denominator. -/
theorem common_denominator_scaled_vector_eq_smul {n : ℕ} (v : Fin n → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℚ)) =
      (rational_vector_common_denominator v : ℚ) • v := by
  -- Clear one coordinate at a time using its divisibility witness.
  funext i
  obtain ⟨k, hk⟩ := dvd_rational_vector_common_denominator v i
  simp only [common_denominator_scaled_vector, Pi.smul_apply, smul_eq_mul]
  rw [hk, Nat.cast_mul]
  rw [mul_comm ((v i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  norm_cast

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean: the binary size
of a product is at most the sum of the binary sizes of its factors. -/
private lemma natSizeMul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  -- Bound each factor by its defining strict power-of-two upper bound.
  refine Nat.size_le.2 ?_
  calc
    a * b < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (Nat.size a + Nat.size b) := by rw [pow_add]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean: the binary size
of a nonempty finite product is at most the sum of the factor sizes. -/
private lemma natSizeFinsetProd_le_sum {α : Type*} (s : Finset α) (f : α → ℕ)
    (hs : s.Nonempty) : Nat.size (∏ i ∈ s, f i) ≤ ∑ i ∈ s, Nat.size (f i) := by
  -- Induct on the product, using nonemptiness to exclude the exceptional empty product `1`.
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hNonempty : s.Nonempty
      · simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        exact
          (natSizeMul_le (f a) (∏ i ∈ s, f i)).trans
            (Nat.add_le_add_left (ih hNonempty) _)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hNonempty]
        simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean: the common
denominator's binary size is bounded by the sum of all denominator sizes. -/
private lemma commonDenominatorSize_le_sumDenSizes {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    Nat.size (rational_vector_common_denominator v) ≤
      ∑ j : Fin n, Nat.size (v j).den := by
  -- Compare the lcm with the nonzero product of all coordinate denominators.
  have hDvd : rational_vector_common_denominator v ∣ ∏ j : Fin n, (v j).den := by
    unfold rational_vector_common_denominator
    exact Finset.lcm_dvd fun j hj ↦ Finset.dvd_prod_of_mem (fun k ↦ (v k).den) hj
  have hProdPos : 0 < ∏ j : Fin n, (v j).den :=
    Finset.prod_pos fun j _ ↦ (v j).den_pos
  have hCommonLe : rational_vector_common_denominator v ≤ ∏ j : Fin n, (v j).den :=
    Nat.le_of_dvd hProdPos hDvd
  have hUnivNonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨i, Finset.mem_univ i⟩
  calc
    Nat.size (rational_vector_common_denominator v) ≤
        Nat.size (∏ j : Fin n, (v j).den) := Nat.size_le_size hCommonLe
    _ ≤ ∑ j : Fin n, Nat.size (v j).den :=
      natSizeFinsetProd_le_sum Finset.univ (fun j ↦ (v j).den) hUnivNonempty

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean: a
denominator-cleared coordinate is the local numerator times the denominator quotient. -/
private lemma commonDenominatorScaledCoordinate_eq_mulNum {n : ℕ} (v : Fin n → ℚ) (i : Fin n)
    (k : ℕ) (hk : rational_vector_common_denominator v = (v i).den * k) :
    common_denominator_scaled_vector v i = (k : ℤ) * (v i).num := by
  -- Cast to `ℚ`, where the existing scaling identity and denominator cancellation apply.
  apply Rat.intCast_injective
  calc
    (common_denominator_scaled_vector v i : ℚ) =
        (rational_vector_common_denominator v : ℚ) * v i :=
      congrFun (common_denominator_scaled_vector_eq_smul v) i
    _ = ((k : ℤ) * (v i).num : ℤ) := by
      rw [hk, Nat.cast_mul, mul_comm ((v i).den : ℚ) (k : ℚ), mul_assoc,
        Rat.den_mul_eq_num]
      norm_cast

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean: each cleared
coordinate costs at most the encoding budget of the whole rational vector. -/
private lemma scaledCoordinateEncoding_le_rationalVector {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    EncodingSize.integer (common_denominator_scaled_vector v i) ≤
      EncodingSize.rationalVector v := by
  -- Express the coordinate using the quotient of the common denominator by its local denominator.
  obtain ⟨k, hk⟩ := dvd_rational_vector_common_denominator v i
  have hCoordinate := commonDenominatorScaledCoordinate_eq_mulNum v i k hk
  have hQuotientLe : k ≤ rational_vector_common_denominator v := by
    rw [hk]
    exact Nat.le_mul_of_pos_left k (v i).den_pos
  have hQuotientSize : Nat.size k ≤ Nat.size (rational_vector_common_denominator v) :=
    Nat.size_le_size hQuotientLe
  have hNumTerm : Nat.size (v i).num.natAbs ≤ ∑ j : Fin n, Nat.size (v j).num.natAbs :=
    Finset.single_le_sum (f := fun j : Fin n ↦ Nat.size (v j).num.natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hOneTerm : 1 ≤ ∑ _j : Fin n, 1 :=
    Finset.single_le_sum (f := fun _j : Fin n ↦ 1) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
  have hDenSum := commonDenominatorSize_le_sumDenSizes v i
  have hProductSize : Nat.size (k * (v i).num.natAbs) ≤
      Nat.size k + Nat.size (v i).num.natAbs := natSizeMul_le _ _
  -- Combine the quotient, numerator, and sign-bit bounds in the expanded encoding formulas.
  simp only [EncodingSize.integer_eq, EncodingSize.rationalVector_eq_sum,
    EncodingSize.rational_eq, hCoordinate, Int.natAbs_mul, Int.natAbs_natCast,
    Finset.sum_add_distrib]
  omega

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_3/ch1_sec1_3_1_remark_1_1/CommonDenominator.lean -/
theorem common_denominator_scaled_vector_encoding_size_le {n : ℕ} (v : Fin n → ℚ) :
    EncodingSize.integerVector (common_denominator_scaled_vector v) ≤
      n * EncodingSize.rationalVector v := by
  -- Sum the coordinatewise budget and identify the resulting constant sum.
  rw [EncodingSize.integerVector_eq_sum]
  calc
    (∑ i : Fin n, EncodingSize.integer (common_denominator_scaled_vector v i)) ≤
        ∑ _i : Fin n, EncodingSize.rationalVector v :=
      Finset.sum_le_sum fun i _ ↦ scaledCoordinateEncoding_le_rationalVector v i
    _ = n * EncodingSize.rationalVector v := by simp

end
