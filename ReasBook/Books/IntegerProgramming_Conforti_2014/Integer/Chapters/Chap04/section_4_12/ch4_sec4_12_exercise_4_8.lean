/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_6

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise is source-facing through a matrix-owned consecutive-ones predicate, while its
-- `0,1`-matrix hypothesis reuses the Chapter 2 owner `IsZeroOneMatrix` and its totally
-- unimodular conclusion reuses mathlib's canonical `Matrix.IsTotallyUnimodular` owner.

section Exercise48

open scoped BigOperators

variable {m n : ℕ}

namespace Matrix

/-- An integer matrix has the consecutive `1`s property when, in every row, each entry between two
`1`s is again `1`. -/
def HasConsecutiveOnesProperty (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i j l, j < l → A i j = 1 → A i l = 1 →
    ∀ k, j ≤ k → k ≤ l → A i k = 1

/-- A Boolean tester for the consecutive `1`s property, implemented by exhaustive search over rows
and column triples. -/
def consecutiveOnesTest (A : Matrix (Fin m) (Fin n) ℤ) : Bool :=
  List.all (List.finRange m) fun i ↦
    List.all (List.finRange n) fun j ↦
      List.all (List.finRange n) fun l ↦
        if j < l ∧ A i j = 1 ∧ A i l = 1 then
          List.all (List.finRange n) fun k ↦
            if j ≤ k ∧ k ≤ l then
              decide (A i k = 1)
            else
              true
        else
          true

/-- The tester accepts exactly the matrices with the consecutive `1`s property. -/
theorem consecutiveOnesTest_spec
    (A : Matrix (Fin m) (Fin n) ℤ) :
    A.consecutiveOnesTest = true ↔ A.HasConsecutiveOnesProperty := by
  constructor
  · intro h i j l hj hAj hAl k hjk hkl
    -- Peel the exhaustive Boolean search one loop at a time until the guarded `k`-loop remains.
    unfold consecutiveOnesTest at h
    have hi := List.all_eq_true.mp h i (by simp)
    have hj' := List.all_eq_true.mp hi j (by simp)
    have hl := List.all_eq_true.mp hj' l (by simp)
    have hkLoop :
        (List.finRange n).all
            (fun k ↦ if j ≤ k ∧ k ≤ l then decide (A i k = 1) else true) = true := by
      simpa [hj, hAj, hAl] using hl
    have hk' := List.all_eq_true.mp hkLoop k (by simp)
    simpa [hjk, hkl] using hk'
  · intro h
    -- Build the nested Boolean certificate directly from the mathematical
    -- interval-closure property.
    unfold consecutiveOnesTest
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro j hj
    apply List.all_eq_true.mpr
    intro l hl
    by_cases hguard : j < l ∧ A i j = 1 ∧ A i l = 1
    · rcases hguard with ⟨hjl, hAj, hAl⟩
      have hkLoop :
          (List.finRange n).all
              (fun k ↦ if j ≤ k ∧ k ≤ l then decide (A i k = 1) else true) = true := by
        apply List.all_eq_true.mpr
        intro k hk
        by_cases hjk : j ≤ k ∧ k ≤ l
        · rcases hjk with ⟨hjk', hkl⟩
          simpa [hjk', hkl] using h i j l hjl hAj hAl k hjk' hkl
        · simp [hjk]
      simpa [hjl, hAj, hAl] using hkLoop
    · simp [hguard]

-- The next helper lemmas set up the Chapter 4.2 equitable-bicoloring route to total
-- unimodularity for consecutive-ones matrices.
/-- Helper for Exercise 4.8: taking a submatrix preserves the `0,1` condition. -/
lemma isZeroOneMatrix_submatrix
    {k l : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    (hA : IsZeroOneMatrix A)
    (row : Fin k → Fin m) (col : Fin l → Fin n) :
    IsZeroOneMatrix (A.submatrix row col) := by
  -- Each selected entry is literally an entry of the original `0,1` matrix.
  intro i j
  simpa [Matrix.submatrix_apply] using hA (row i) (col j)

/-- Helper for Exercise 4.8: a consecutive-ones matrix stays consecutive-ones after restricting to
its columns in increasing ambient order. -/
lemma hasConsecutiveOnesProperty_submatrix_orderEmbOfFin
    {k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hconsecutive : A.HasConsecutiveOnesProperty)
    (s : Finset (Fin n))
    (hs : s.card = k) :
    (A.submatrix id (s.orderEmbOfFin hs)).HasConsecutiveOnesProperty := by
  intro i j l hj hAj hAl t hjt htl
  -- The sorted column enumeration is increasing, so interval containment is preserved.
  have hjl :
      s.orderEmbOfFin hs j < s.orderEmbOfFin hs l :=
    (s.orderEmbOfFin hs).strictMono hj
  have hjt' :
      s.orderEmbOfFin hs j ≤ s.orderEmbOfFin hs t :=
    (s.orderEmbOfFin hs).monotone hjt
  have htl' :
      s.orderEmbOfFin hs t ≤ s.orderEmbOfFin hs l :=
    (s.orderEmbOfFin hs).monotone htl
  simpa [Matrix.submatrix_apply] using
    hconsecutive i (s.orderEmbOfFin hs j) (s.orderEmbOfFin hs l) hjl hAj hAl
      (s.orderEmbOfFin hs t) hjt' htl'

/-- Helper for Exercise 4.8: the parity-red columns are the even positions of `Fin k`. -/
def parity_red (k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun j ↦ j.1 % 2 = 0

/-- Helper for Exercise 4.8: the parity-blue columns are the odd positions of `Fin k`. -/
def parity_blue (k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun j ↦ j.1 % 2 = 1

/-- Helper for Exercise 4.8: the alternating `(-1)^j` sum on a natural interval depends only on the
starting parity and the interval length. -/
lemma nat_interval_alternating_sum
    (a b : ℕ) (hab : a ≤ b) :
    Finset.sum (Finset.Icc a b) (fun j ↦ (-1 : ℤ) ^ j) =
      (-1 : ℤ) ^ a * (if Even (b + 1 - a) then 0 else 1) := by
  let e : Fin (b + 1 - a) ↪ ℕ :=
    ⟨fun t ↦ a + t.1, by
      intro x y hxy
      exact Fin.ext (Nat.add_left_cancel hxy)⟩
  have hmap : Finset.univ.map e = Finset.Icc a b := by
    -- Enumerate the natural interval by shifting the canonical order on `Fin (b + 1 - a)`.
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨t, -, rfl⟩
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · change a ≤ a + t.1
        omega
      have ht : t.1 < b + 1 - a := t.2
      change a + t.1 ≤ b
      omega
    · intro hx
      rw [Finset.mem_map]
      refine ⟨⟨x - a, by
        have hx' := Finset.mem_Icc.mp hx
        omega⟩, by simp, ?_⟩
      have hx' := Finset.mem_Icc.mp hx
      change a + (x - a) = x
      omega
  rw [← hmap, Finset.sum_map]
  -- Factor out the fixed starting sign and then use the standard alternating sum on `Fin`.
  calc
    (∑ t : Fin (b + 1 - a), (-1 : ℤ) ^ (a + t.1))
        = ∑ t : Fin (b + 1 - a), ((-1 : ℤ) ^ a * (-1 : ℤ) ^ t.1) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [pow_add]
    _ = (-1 : ℤ) ^ a * ∑ t : Fin (b + 1 - a), (-1 : ℤ) ^ t.1 := by
          rw [Finset.mul_sum]
    _ = (-1 : ℤ) ^ a * (if Even (b + 1 - a) then 0 else 1) := by
          rw [Fin.sum_neg_one_pow]

/-- Helper for Exercise 4.8: on a natural interval, the even-minus-odd cardinality difference is
the same alternating sum, hence still a sign value. -/
lemma nat_interval_parity_balance
    (a b : ℕ) (hab : a ≤ b) :
    (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) -
      (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) =
        (-1 : ℤ) ^ a * (if Even (b + 1 - a) then 0 else 1) := by
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc a b) (fun j : ℕ ↦ j % 2 = 1)
      (fun j ↦ (-1 : ℤ) ^ j)).symm
  have hnotOdd :
      (Finset.Icc a b).filter (fun j : ℕ ↦ ¬ (j % 2 = 1)) =
        (Finset.Icc a b).filter (fun j : ℕ ↦ j % 2 = 0) := by
    -- Modulo `2`, “not odd” is exactly “even”.
    ext j
    simp
  have heven :
      Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0) (fun j ↦ (-1 : ℤ) ^ j) =
        (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) := by
    -- Every term on the even subinterval contributes `+1`.
    calc
      Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0) (fun j ↦ (-1 : ℤ) ^ j) =
          Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0) (fun _ ↦ (1 : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj0 : j % 2 = 0 := by simpa using (Finset.mem_filter.mp hj).2
            exact (Nat.even_iff.2 hj0).neg_one_pow
      _ = (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) := by
            simp
  have hodd :
      Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1) (fun j ↦ (-1 : ℤ) ^ j) =
        -(((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) := by
    -- Every term on the odd subinterval contributes `-1`.
    calc
      Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1) (fun j ↦ (-1 : ℤ) ^ j) =
          Finset.sum ((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1) (fun _ ↦ (-1 : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj1 : j % 2 = 1 := by simpa using (Finset.mem_filter.mp hj).2
            exact (Nat.odd_iff.2 hj1).neg_one_pow
      _ = -(((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) := by
            simp
  -- Split the interval sum into odd and even parts, then rewrite each part by its constant value.
  calc
    (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) -
        (((Finset.Icc a b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) =
          Finset.sum (Finset.Icc a b) (fun j ↦ (-1 : ℤ) ^ j) := by
            rw [hsplit, hnotOdd, heven, hodd]
            ring
    _ = (-1 : ℤ) ^ a * (if Even (b + 1 - a) then 0 else 1) :=
      nat_interval_alternating_sum a b hab

/-- Helper for Exercise 4.8: mapping the even part of a `Fin` interval along `Fin.valEmbedding`
gives the corresponding even natural interval. -/
lemma fin_even_filter_map_valEmbedding
    {k : ℕ} (a b : Fin k) :
    ((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).map Fin.valEmbedding =
      (Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 0 := by
  -- Membership is preserved because `Fin.valEmbedding` records exactly the underlying natural.
  ext j
  constructor
  · intro hj
    rcases Finset.mem_map.mp hj with ⟨x, hx, rfl⟩
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxEven⟩
    exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_Icc] using hxIcc, hxEven⟩
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjEven⟩
    rw [Finset.mem_map]
    have hjBounds := Finset.mem_Icc.mp hjIcc
    refine ⟨⟨j, lt_of_le_of_lt hjBounds.2 b.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_Icc] using hjBounds, hjEven⟩

/-- Helper for Exercise 4.8: mapping the odd part of a `Fin` interval along `Fin.valEmbedding`
gives the corresponding odd natural interval. -/
lemma fin_odd_filter_map_valEmbedding
    {k : ℕ} (a b : Fin k) :
    ((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).map Fin.valEmbedding =
      (Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 1 := by
  -- The same transport works verbatim for the odd subinterval.
  ext j
  constructor
  · intro hj
    rcases Finset.mem_map.mp hj with ⟨x, hx, rfl⟩
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxOdd⟩
    exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_Icc] using hxIcc, hxOdd⟩
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjOdd⟩
    rw [Finset.mem_map]
    have hjBounds := Finset.mem_Icc.mp hjIcc
    refine ⟨⟨j, lt_of_le_of_lt hjBounds.2 b.2⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨by simpa [Finset.mem_Icc] using hjBounds, hjOdd⟩

/-- Helper for Exercise 4.8: the alternating parity balance on any finite interval is a sign value.
-/
lemma alternating_parity_interval_balance_mem_signType_range
    {k : ℕ} {a b : Fin k} (hab : a ≤ b) :
    ((((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) -
      (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ))
      ∈ Set.range SignType.cast := by
  have hevenCard :
      (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) =
        (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) := by
    -- The even `Fin` interval and the even natural interval are related by an injective map.
    calc
      (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) =
          ((((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).map Fin.valEmbedding).card : ℤ) := by
            simp
      _ = (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) := by
            exact congrArg (fun n : ℕ ↦ (n : ℤ)) (congrArg Finset.card (fin_even_filter_map_valEmbedding a b))
  have hoddCard :
      (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ) =
        (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) := by
    -- The same cardinality transport holds for odd positions.
    calc
      (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ) =
          ((((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).map Fin.valEmbedding).card : ℤ) := by
            simp
      _ = (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) := by
            exact congrArg (fun n : ℕ ↦ (n : ℤ)) (congrArg Finset.card (fin_odd_filter_map_valEmbedding a b))
  have hnat :=
    nat_interval_parity_balance (a : ℕ) b (show (a : ℕ) ≤ b by exact hab)
  have hbalance :
      ((((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) -
        (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ)) =
          (-1 : ℤ) ^ (a : ℕ) * (if Even ((b : ℕ) + 1 - (a : ℕ)) then 0 else 1) := by
    calc
      ((((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) -
          (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ)) =
            (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 0).card : ℤ) -
              (((Finset.Icc (a : ℕ) b).filter fun j : ℕ ↦ j % 2 = 1).card : ℤ) := by
                rw [hevenCard, hoddCard]
      _ = (-1 : ℤ) ^ (a : ℕ) * (if Even ((b : ℕ) + 1 - (a : ℕ)) then 0 else 1) := hnat
  rcases Nat.even_or_odd ((b : ℕ) + 1 - (a : ℕ)) with hlenEven | hlenOdd
  · -- Even-length intervals contribute total sum `0`.
    rw [if_pos hlenEven] at hbalance
    refine ⟨0, ?_⟩
    simpa [hbalance] using hbalance
  · -- Odd-length intervals contribute the sign of the starting parity.
    rw [if_neg (Nat.not_even_iff_odd.2 hlenOdd)] at hbalance
    rcases Nat.even_or_odd (a : ℕ) with haEven | haOdd
    · refine ⟨1, ?_⟩
      rw [haEven.neg_one_pow] at hbalance
      simpa [hbalance] using hbalance
    · refine ⟨-1, ?_⟩
      rw [haOdd.neg_one_pow] at hbalance
      simpa [hbalance] using hbalance

/-- Helper for Exercise 4.8: a finite sum of `0,1`-valued integers is the cardinality of the
subsupport on which the value is `1`. -/
lemma zero_one_sum_eq_card_filter_eq_one
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, f x = 0 ∨ f x = 1) :
    s.sum f = ((s.filter fun x ↦ f x = 1).card : ℤ) := by
  have hsplit :=
    (Finset.sum_filter_add_sum_filter_not s (fun x ↦ f x = 1) f).symm
  have hones :
      Finset.sum (s.filter fun x ↦ f x = 1) f =
        ((s.filter fun x ↦ f x = 1).card : ℤ) := by
    -- On the `1`-support, every summand is literally `1`.
    calc
      Finset.sum (s.filter fun x ↦ f x = 1) f =
          Finset.sum (s.filter fun x ↦ f x = 1) (fun _ ↦ (1 : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact (Finset.mem_filter.mp hx).2
      _ = ((s.filter fun x ↦ f x = 1).card : ℤ) := by
            simp
  have hzeros :
      Finset.sum (s.filter fun x ↦ ¬ (f x = 1)) f = 0 := by
    -- Outside the `1`-support, the `0,1` hypothesis forces each summand to be `0`.
    refine Finset.sum_eq_zero ?_
    intro x hx
    rcases hf x (Finset.mem_filter.mp hx).1 with hx0 | hx1
    · exact hx0
    · exfalso
      exact (Finset.mem_filter.mp hx).2 hx1
  rw [hsplit, hones, hzeros, add_zero]

/-- Helper for Exercise 4.8: a nonempty row support in a consecutive-ones matrix is exactly the
interval between its minimum and maximum selected columns. -/
lemma row_support_eq_interval_of_consecutive_ones
    {k : ℕ}
    (B : Matrix (Fin m) (Fin k) ℤ)
    (hconsecutive : B.HasConsecutiveOnesProperty)
    (i : Fin m)
    (S : Finset (Fin k))
    (hS : S = Finset.univ.filter fun j : Fin k ↦ B i j = 1)
    (hNonempty : S.Nonempty) :
    S = Finset.Icc (S.min' hNonempty) (S.max' hNonempty) := by
  let a := S.min' hNonempty
  let b := S.max' hNonempty
  ext j
  constructor
  · intro hj
    -- Every support element lies between the support minimum and maximum.
    refine Finset.mem_Icc.mpr ?_
    constructor
    · simpa [a] using Finset.min'_le S j hj
    · simpa [b] using Finset.le_max' S j hj
  · intro hj
    rcases Finset.mem_Icc.mp hj with ⟨hjmin, hjmax⟩
    by_cases hab : a = b
    · -- In the singleton case, the interval point is forced to be the unique support element.
      have hEq : j = a := by
        apply le_antisymm
        · simpa [a, b, hab] using hjmax
        · simpa [a] using hjmin
      have haMem : a ∈ S := by
        simpa [a] using Finset.min'_mem S hNonempty
      simpa [hEq] using haMem
    · -- Otherwise the consecutive-ones property fills every point between the support endpoints.
      have hab_le : a ≤ b := by
        simpa [a, b] using Finset.min'_le_max' S hNonempty
      have hab_lt : a < b := lt_of_le_of_ne hab_le hab
      have haMem : a ∈ S := by
        simpa [a] using Finset.min'_mem S hNonempty
      have hbMem : b ∈ S := by
        simpa [b] using Finset.max'_mem S hNonempty
      have haOne : B i a = 1 := by
        rw [hS] at haMem
        exact (Finset.mem_filter.mp haMem).2
      have hbOne : B i b = 1 := by
        rw [hS] at hbMem
        exact (Finset.mem_filter.mp hbMem).2
      rw [hS]
      refine Finset.mem_filter.mpr ?_
      refine ⟨by simp, hconsecutive i a b hab_lt haOne hbOne j ?_ ?_⟩
      · simpa [a] using hjmin
      · simpa [b] using hjmax

/-- Helper for Exercise 4.8: reindexing the columns along an equivalence preserves the red-minus-
blue row difference when the red and blue sets are transported by the same equivalence. -/
lemma column_bicoloring_difference_reindex_columns
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (B : Matrix (Fin m) κ ℤ)
    (e : ι ≃ κ)
    (red blue : Finset κ)
    (i : Fin m) :
    column_bicoloring_difference
        (B.reindex (Equiv.refl _) e.symm)
        (red.map e.symm.toEmbedding)
        (blue.map e.symm.toEmbedding)
        i =
      column_bicoloring_difference B red blue i := by
  -- Both transported sums are just the original sums rewritten along the equivalence.
  rw [column_bicoloring_difference_apply, column_bicoloring_difference_apply]
  simp [Matrix.reindex_apply, Finset.sum_map]

/-- Helper for Exercise 4.8: an equitable bicoloring transports across a column reindexing
equivalence. -/
lemma is_equitable_bicoloring_reindex_columns
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (B : Matrix (Fin m) κ ℤ)
    (e : ι ≃ κ)
    (red blue : Finset κ)
    (hbalanced : is_equitable_bicoloring B red blue) :
    is_equitable_bicoloring
        (B.reindex (Equiv.refl _) e.symm)
        (red.map e.symm.toEmbedding)
        (blue.map e.symm.toEmbedding) := by
  -- Unfold the definition so each field transports separately along the same column equivalence.
  rw [is_equitable_bicoloring_iff] at hbalanced ⊢
  rcases hbalanced with ⟨hdisjoint, hcover, hrow⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Disjointness is preserved by injective maps of finite sets.
    exact (Finset.disjoint_map e.symm.toEmbedding).2 hdisjoint
  · -- Coverage transports because mapping along an equivalence sends `univ` to `univ`.
    calc
      red.map e.symm.toEmbedding ∪ blue.map e.symm.toEmbedding
          = (red ∪ blue).map e.symm.toEmbedding := by
              rw [Finset.map_union]
      _ = Finset.univ.map e.symm.toEmbedding := by rw [hcover]
      _ = Finset.univ := Finset.map_univ_equiv e.symm
  · intro i
    -- The row-balance equation was already proved invariant under the same reindexing.
    rw [column_bicoloring_difference_reindex_columns B e red blue i]
    exact hrow i

/-- Helper for Exercise 4.8: on a sorted consecutive-ones submatrix, coloring columns by parity of
their position gives an equitable bicoloring. -/
lemma alternating_parity_is_equitable_bicoloring_of_isZeroOne_of_hasConsecutiveOnesProperty
    {k : ℕ}
    (B : Matrix (Fin m) (Fin k) ℤ)
    (hB : IsZeroOneMatrix B)
    (hconsecutive : B.HasConsecutiveOnesProperty) :
    is_equitable_bicoloring B (parity_red k) (parity_blue k) := by
  rw [is_equitable_bicoloring_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- No column position can be both even and odd.
    rw [Finset.disjoint_left]
    intro j hjRed hjBlue
    rcases Finset.mem_filter.mp hjRed with ⟨_, hjRed'⟩
    rcases Finset.mem_filter.mp hjBlue with ⟨_, hjBlue'⟩
    omega
  · -- Every column position has parity `0` or `1` modulo `2`.
    ext j
    simp [parity_red, parity_blue]
    omega
  · intro i
    let S : Finset (Fin k) := Finset.univ.filter fun j : Fin k ↦ B i j = 1
    by_cases hS : S.Nonempty
    · let a := S.min' hS
      let b := S.max' hS
      have hS_eq : S = Finset.Icc a b :=
        row_support_eq_interval_of_consecutive_ones B hconsecutive i S rfl hS
      have hsupport :
          ∀ j : Fin k, B i j = 1 ↔ j ∈ Finset.Icc a b := by
        intro j
        constructor
        · intro hj
          have hjMem : j ∈ S := by
            simp [S, hj]
          rw [hS_eq] at hjMem
          exact hjMem
        · intro hj
          have hjMem : j ∈ S := by
            rw [hS_eq]
            exact hj
          exact (Finset.mem_filter.mp hjMem).2
      have hredFilter :
          (parity_red k).filter (fun j : Fin k ↦ B i j = 1) =
            (Finset.Icc a b).filter (fun j : Fin k ↦ j.1 % 2 = 0) := by
        -- On the red columns, the `1`-support is exactly the even part of the support interval.
        ext j
        constructor
        · intro hj
          rcases Finset.mem_filter.mp hj with ⟨hjRed, hjOne⟩
          rcases Finset.mem_filter.mp hjRed with ⟨_, hjEven⟩
          exact Finset.mem_filter.mpr ⟨(hsupport j).1 hjOne, hjEven⟩
        · intro hj
          rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjEven⟩
          refine Finset.mem_filter.mpr ⟨?_, (hsupport j).2 hjIcc⟩
          exact Finset.mem_filter.mpr ⟨by simp, hjEven⟩
      have hblueFilter :
          (parity_blue k).filter (fun j : Fin k ↦ B i j = 1) =
            (Finset.Icc a b).filter (fun j : Fin k ↦ j.1 % 2 = 1) := by
        -- On the blue columns, the `1`-support is exactly the odd part of the support interval.
        ext j
        constructor
        · intro hj
          rcases Finset.mem_filter.mp hj with ⟨hjBlue, hjOne⟩
          rcases Finset.mem_filter.mp hjBlue with ⟨_, hjOdd⟩
          exact Finset.mem_filter.mpr ⟨(hsupport j).1 hjOne, hjOdd⟩
        · intro hj
          rcases Finset.mem_filter.mp hj with ⟨hjIcc, hjOdd⟩
          refine Finset.mem_filter.mpr ⟨?_, (hsupport j).2 hjIcc⟩
          exact Finset.mem_filter.mpr ⟨by simp, hjOdd⟩
      have hredSum :
          (parity_red k).sum (fun j ↦ B i j) =
            (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 0).card : ℤ) := by
        -- The red sum counts exactly the red support columns because the matrix is `0,1`-valued.
        rw [zero_one_sum_eq_card_filter_eq_one (parity_red k) (fun j ↦ B i j)]
        · rw [hredFilter]
        · intro j hj
          exact hB i j
      have hblueSum :
          (parity_blue k).sum (fun j ↦ B i j) =
            (((Finset.Icc a b).filter fun j : Fin k ↦ j.1 % 2 = 1).card : ℤ) := by
        -- The blue sum is the corresponding odd support count.
        rw [zero_one_sum_eq_card_filter_eq_one (parity_blue k) (fun j ↦ B i j)]
        · rw [hblueFilter]
        · intro j hj
          exact hB i j
      have hab : a ≤ b := by
        simpa [a, b] using Finset.min'_le_max' S hS
      have hsign :=
        alternating_parity_interval_balance_mem_signType_range (a := a) (b := b) hab
      rcases hsign with ⟨s, hs⟩
      have hvalue :
          column_bicoloring_difference B (parity_red k) (parity_blue k) i = (s : ℤ) := by
        rw [column_bicoloring_difference_apply, hredSum, hblueSum]
        exact hs.symm
      rcases SignType.trichotomy s with hsNeg | hsZero | hsPos
      · right
        right
        simpa [column_bicoloring_difference_apply, hsNeg] using hvalue
      · left
        simpa [column_bicoloring_difference_apply, hsZero] using hvalue
      · right
        left
        simpa [column_bicoloring_difference_apply, hsPos] using hvalue
    · have hrowZero : ∀ j : Fin k, B i j = 0 := by
        -- If the support is empty, every entry in the row must be `0`.
        intro j
        rcases hB i j with hjZero | hjOne
        · exact hjZero
        · exfalso
          exact hS ⟨j, by simp [S, hjOne]⟩
      left
      -- With no `1`s in the row, both color sums vanish.
      rw [column_bicoloring_difference_apply]
      simp [hrowZero]

/-- Helper for Exercise 4.8: every column-embedded submatrix admits the parity equitable bicoloring
obtained after sorting the selected columns. -/
lemma exists_equitable_bicoloring_of_column_embedding_of_isZeroOne_of_hasConsecutiveOnesProperty
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : IsZeroOneMatrix A)
    (hconsecutive : A.HasConsecutiveOnesProperty)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (col : ι ↪ Fin n) :
    ∃ red blue : Finset ι,
      is_equitable_bicoloring (A.submatrix id col) red blue := by
  classical
  let s : Finset (Fin n) := Finset.univ.map col
  have hs : s.card = Fintype.card ι := by
    simp [s]
  let f : ι → Fin (Fintype.card ι) := fun x ↦
    (s.orderIsoOfFin hs).symm ⟨col x, by
      exact Finset.mem_map.mpr ⟨x, by simp, rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro x y hxy
    have hsub :
        (⟨col x, by exact Finset.mem_map.mpr ⟨x, by simp, rfl⟩⟩ : s) =
          ⟨col y, by exact Finset.mem_map.mpr ⟨y, by simp, rfl⟩⟩ := by
      have := congrArg (s.orderIsoOfFin hs) hxy
      simpa [f] using this
    exact col.injective (Subtype.ext_iff.mp hsub)
  have hfBij : Function.Bijective f := by
    exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfInj, by simp⟩
  let e : ι ≃ Fin (Fintype.card ι) := Equiv.ofBijective f hfBij
  have he : ∀ x : ι, s.orderEmbOfFin hs (e x) = col x := by
    intro x
    change ↑((s.orderIsoOfFin hs) (f x)) = col x
    simp [f]
  let sorted : Matrix (Fin m) (Fin (Fintype.card ι)) ℤ :=
    A.submatrix id (s.orderEmbOfFin hs)
  have hsortedZeroOne : IsZeroOneMatrix sorted := by
    exact isZeroOneMatrix_submatrix hA id (s.orderEmbOfFin hs)
  have hsortedConsecutive : sorted.HasConsecutiveOnesProperty := by
    exact hasConsecutiveOnesProperty_submatrix_orderEmbOfFin A hconsecutive s hs
  have hsortedColor :
      is_equitable_bicoloring sorted (parity_red (Fintype.card ι)) (parity_blue (Fintype.card ι)) := by
    exact
      alternating_parity_is_equitable_bicoloring_of_isZeroOne_of_hasConsecutiveOnesProperty
        sorted hsortedZeroOne hsortedConsecutive
  have htransport :
      is_equitable_bicoloring
          (sorted.reindex (Equiv.refl _) e.symm)
          ((parity_red (Fintype.card ι)).map e.symm.toEmbedding)
          ((parity_blue (Fintype.card ι)).map e.symm.toEmbedding) := by
    exact
      is_equitable_bicoloring_reindex_columns
        sorted e (parity_red (Fintype.card ι)) (parity_blue (Fintype.card ι)) hsortedColor
  have hmatrix :
      A.submatrix id col = sorted.reindex (Equiv.refl _) e.symm := by
    ext i j
    simp [sorted, Matrix.reindex_apply, he]
  refine ⟨(parity_red (Fintype.card ι)).map e.symm.toEmbedding,
    (parity_blue (Fintype.card ι)).map e.symm.toEmbedding, ?_⟩
  simpa [hmatrix] using htransport

/-- Helper for Exercise 4.8: the Chapter 4.2 column-bicoloring criterion yields total
unimodularity for a `0,1` matrix with the consecutive-ones property. -/
lemma isTotallyUnimodular_of_isZeroOne_of_hasConsecutiveOnesProperty_aux
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : IsZeroOneMatrix A)
    (hconsecutive : A.HasConsecutiveOnesProperty) :
    A.IsTotallyUnimodular := by
  -- Apply the Chapter 4.2 criterion once every column embedding has an equitable bicoloring.
  refine
    (totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring.{0, 0, 0} A).2 ?_
  intro ι _ _ col
  exact
    exists_equitable_bicoloring_of_column_embedding_of_isZeroOne_of_hasConsecutiveOnesProperty
      A hA hconsecutive col

/-- Bridge to `Matrix.isTotallyUnimodular_iff`: every square submatrix of a `0,1` matrix with the
consecutive `1`s property has determinant in the image of `SignType.cast`. -/
theorem square_submatrix_det_mem_signType_range_of_isZeroOne_of_hasConsecutiveOnesProperty
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : IsZeroOneMatrix A)
    (hconsecutive : A.HasConsecutiveOnesProperty) :
    ∀ k (row : Fin k → Fin m) (col : Fin k → Fin n),
      (A.submatrix row col).det ∈ Set.range SignType.cast := by
  intro k row col
  -- The source-faithful route first proves that the whole matrix is totally unimodular via the
  -- equitable-bicoloring criterion, then specializes to the chosen square submatrix.
  have hTU :
      A.IsTotallyUnimodular :=
    isTotallyUnimodular_of_isZeroOne_of_hasConsecutiveOnesProperty_aux A hA hconsecutive
  rw [Matrix.isTotallyUnimodular_iff] at hTU
  exact hTU k row col

/-- Exercise 4.8 (2). A `0,1`-matrix with the consecutive `1`s property is totally unimodular. -/
theorem isTotallyUnimodular_of_isZeroOne_of_hasConsecutiveOnesProperty
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : IsZeroOneMatrix A)
    (hconsecutive : A.HasConsecutiveOnesProperty) :
    A.IsTotallyUnimodular := by
  -- Reuse the Chapter 4.2 criterion packaged in the auxiliary theorem above.
  exact isTotallyUnimodular_of_isZeroOne_of_hasConsecutiveOnesProperty_aux A hA hconsecutive

end Matrix

/-- A crude row/column loop count for the direct exhaustive search tester. -/
def consecutiveOnesTestOperationCount (m n : ℕ) : ℕ :=
  m * n ^ 3

/-- Exercise 4.8 (1). The consecutive `1`s property admits a polynomial-time recognition
algorithm: the explicit tester `consecutiveOnesTest` recognizes the property, and its direct
row/column loop count is bounded above by a polynomial in the input dimensions. -/
theorem consecutive_ones_property_has_polynomial_time_tester :
    ∃ p : Polynomial ℕ,
      (∀ m n (A : Matrix (Fin m) (Fin n) ℤ),
        A.consecutiveOnesTest = true ↔ A.HasConsecutiveOnesProperty) ∧
      ∀ m n, consecutiveOnesTestOperationCount m n ≤ p.eval (m + n) := by
  -- Use the quartic polynomial `(X)^4` as a coarse upper bound on the triple loop count.
  refine Exists.intro (Polynomial.X ^ 4) ?_
  constructor
  · intro m n A
    exact A.consecutiveOnesTest_spec
  · intro m n
    -- Compare each factor with `m + n`, then evaluate `X ^ 4` at `m + n`.
    unfold consecutiveOnesTestOperationCount
    have hm : m ≤ m + n := Nat.le_add_right m n
    have hn : n ≤ m + n := Nat.le_add_left n m
    have hn2 : n ^ 2 ≤ (m + n) ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hn hn
    have hn3 : n ^ 3 ≤ (m + n) ^ 3 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul hn2 hn
    have hmul : m * n ^ 3 ≤ (m + n) * (m + n) ^ 3 :=
      Nat.mul_le_mul hm hn3
    have hpow : (m + n) * (m + n) ^ 3 = (m + n) ^ 4 := by
      simp [pow_succ, Nat.mul_comm]
    calc
      m * n ^ 3 ≤ (m + n) * (m + n) ^ 3 := hmul
      _ = (m + n) ^ 4 := hpow
      _ = (Polynomial.X ^ 4).eval (m + n) := by
        simp [Polynomial.eval_pow, Polynomial.eval_X]

end Exercise48
