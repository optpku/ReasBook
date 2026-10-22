/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section05_part1

section Chap04
section Section05

open scoped Topology

/-- Helper for Proposition 4.5.3: factorial tail denominator dominates a geometric factor. -/
lemma helperForProposition_4_5_3_factorial_lower_bound_nat
    (n k : ℕ) :
    (n + 1).factorial * 2 ^ k ≤ (n + (k + 1)).factorial := by
  have hpow : 2 ^ k ≤ (n + 2) ^ k := by
    exact Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))) k
  calc
    (n + 1).factorial * 2 ^ k ≤ (n + 1).factorial * (n + 2) ^ k :=
      Nat.mul_le_mul_left _ hpow
    _ ≤ (n + 1 + k).factorial := by
      simpa [Nat.add_assoc] using (Nat.factorial_mul_pow_le_factorial (m := n + 1) (n := k))
    _ = (n + (k + 1)).factorial := by
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Helper for Proposition 4.5.3: each factorial-tail term is bounded by a geometric term. -/
lemma helperForProposition_4_5_3_term_le_geometric
    (n k : ℕ) :
    (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)
      ≤ ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k) := by
  have hNat := helperForProposition_4_5_3_factorial_lower_bound_nat n k
  have hCast : (((n + 1).factorial : ℝ) * (2 : ℝ) ^ k)
      ≤ ((n + (k + 1)).factorial : ℝ) := by
    exact_mod_cast hNat
  have hpos : 0 < (((n + 1).factorial : ℝ) * (2 : ℝ) ^ k) := by
    positivity
  have hdiv : (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)
      ≤ (1 : ℝ) / (((n + 1).factorial : ℝ) * (2 : ℝ) ^ k) := by
    exact one_div_le_one_div_of_le hpos hCast
  have hrewrite :
      (1 : ℝ) / (((n + 1).factorial : ℝ) * (2 : ℝ) ^ k)
        = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k) := by
    calc
      (1 : ℝ) / (((n + 1).factorial : ℝ) * (2 : ℝ) ^ k)
          = (1 : ℝ) / ((n + 1).factorial : ℝ) * (1 / ((2 : ℝ) ^ k)) := by
              simp [mul_comm]
      _ = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k) := by
            simp [one_div, inv_pow]
  exact hdiv.trans (le_of_eq hrewrite)

/-- Helper for Proposition 4.5.3: the shifted factorial reciprocal tail is summable. -/
lemma helperForProposition_4_5_3_summable_tail
    (n : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) := by
  have hgeom :
      Summable (fun k : ℕ => ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k)) := by
    exact summable_geometric_two.mul_left ((1 : ℝ) / ((n + 1).factorial : ℝ))
  have hNonneg :
      ∀ k : ℕ, 0 ≤ (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) := by
    intro k
    positivity
  exact Summable.of_nonneg_of_le
    hNonneg
    (fun k => helperForProposition_4_5_3_term_le_geometric n k)
    hgeom

/-- Helper for Proposition 4.5.3: the shifted factorial reciprocal tail is bounded
by a geometric sum equal to `2 / (n+1)!`. -/
lemma helperForProposition_4_5_3_tsum_le_two_div_factorial_succ
    (n : ℕ) :
    (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ))
      ≤ (2 : ℝ) / ((n + 1).factorial : ℝ) := by
  let f : ℕ → ℝ := fun k => (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)
  let g : ℕ → ℝ := fun k => ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k)
  have hf : Summable f := by
    simpa [f] using helperForProposition_4_5_3_summable_tail n
  have hg : Summable g := by
    simpa [g] using (summable_geometric_two.mul_left ((1 : ℝ) / ((n + 1).factorial : ℝ)))
  have hfg : ∀ k : ℕ, f k ≤ g k := by
    intro k
    simpa [f, g] using helperForProposition_4_5_3_term_le_geometric n k
  have hle : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k := by
    exact Summable.tsum_le_tsum hfg hf hg
  have hgeomMul :
      (∑' k : ℕ, ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k))
        = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * (∑' k : ℕ, (1 / 2 : ℝ) ^ k) := by
    simpa using
      (tsum_mul_left :
        (∑' k : ℕ, ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k))
          = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * (∑' k : ℕ, (1 / 2 : ℝ) ^ k))
  have hgeomEval : (∑' k : ℕ, g k) = (2 : ℝ) / ((n + 1).factorial : ℝ) := by
    calc
      (∑' k : ℕ, g k)
          = (∑' k : ℕ, ((1 : ℝ) / ((n + 1).factorial : ℝ)) * ((1 / 2 : ℝ) ^ k)) := by
              rfl
      _ = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * (∑' k : ℕ, (1 / 2 : ℝ) ^ k) := hgeomMul
      _ = ((1 : ℝ) / ((n + 1).factorial : ℝ)) * 2 := by rw [tsum_geometric_two]
      _ = (2 : ℝ) / ((n + 1).factorial : ℝ) := by ring
  exact hle.trans_eq hgeomEval

/-- Helper for Proposition 4.5.3: the geometric upper bound is strictly below `1 / n!`
when `n ≥ 3`. -/
lemma helperForProposition_4_5_3_two_div_factorial_succ_lt_inv_factorial
    (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) / ((n + 1).factorial : ℝ) < (1 : ℝ) / (n.factorial : ℝ) := by
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenPos : (0 : ℝ) < n + 1 := by positivity
  have hnum_lt_den : (2 : ℝ) < n + 1 := by linarith
  have hlt : (2 : ℝ) / (n + 1 : ℝ) < 1 := (div_lt_one hdenPos).2 hnum_lt_den
  have hInvPos : 0 < (1 : ℝ) / (n.factorial : ℝ) := by positivity
  have hmul :
      ((2 : ℝ) / (n + 1 : ℝ)) * ((1 : ℝ) / (n.factorial : ℝ))
        < (1 : ℝ) * ((1 : ℝ) / (n.factorial : ℝ)) :=
    mul_lt_mul_of_pos_right hlt hInvPos
  have hdecomp :
      (2 : ℝ) / ((n + 1).factorial : ℝ)
        = ((2 : ℝ) / (n + 1 : ℝ)) * ((1 : ℝ) / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
    have h2 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [h1, h2]
    norm_num [Nat.cast_add]
  calc
    (2 : ℝ) / ((n + 1).factorial : ℝ)
        = ((2 : ℝ) / (n + 1 : ℝ)) * ((1 : ℝ) / (n.factorial : ℝ)) := hdecomp
    _ < (1 : ℝ) * ((1 : ℝ) / (n.factorial : ℝ)) := hmul
    _ = (1 : ℝ) / (n.factorial : ℝ) := by ring

/-- Proposition 4.5.3: for every integer `n ≥ 3`, the factorial tail sum satisfies
`0 < ∑' k : ℕ, 1 / (n + (k + 1))! < 1 / n!`. -/
theorem factorial_tail_sum_pos_and_lt_inv_factorial
    (n : ℕ) (hn : 3 ≤ n) :
    0 < ∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) ∧
      (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) < (1 : ℝ) / (n.factorial : ℝ) := by
  have hSummable :
      Summable (fun k : ℕ => (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) :=
    helperForProposition_4_5_3_summable_tail n
  have hNonneg :
      ∀ k : ℕ, 0 ≤ (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) := by
    intro k
    positivity
  have hTerm0Pos : 0 < (1 : ℝ) / ((n + (0 + 1)).factorial : ℝ) := by
    positivity
  have hTerm0Pos' : 0 < (1 : ℝ) / ((n + (0 + 1)).factorial : ℝ) := by
    simpa using hTerm0Pos
  have hPos :
      0 < ∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) := by
    exact Summable.tsum_pos hSummable hNonneg 0 hTerm0Pos'
  have hLe :
      (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ))
        ≤ (2 : ℝ) / ((n + 1).factorial : ℝ) :=
    helperForProposition_4_5_3_tsum_le_two_div_factorial_succ n
  have hLtBridge :
      (2 : ℝ) / ((n + 1).factorial : ℝ) < (1 : ℝ) / (n.factorial : ℝ) :=
    helperForProposition_4_5_3_two_div_factorial_succ_lt_inv_factorial n hn
  have hUpper :
      (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) < (1 : ℝ) / (n.factorial : ℝ) :=
    lt_of_le_of_lt hLe hLtBridge
  exact ⟨hPos, hUpper⟩

/-- Helper for Proposition 4.5.4: split the reciprocal-factorial series at index `n+1`. -/
lemma helperForProposition_4_5_4_tsum_split_at_factorial_index
    (n : ℕ) :
    (∑' j : ℕ, (1 : ℝ) / (j.factorial : ℝ))
      = (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (j.factorial : ℝ))
          + ∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) := by
  have hsplit := (Summable.sum_add_tsum_nat_add (n + 1) summable_one_div_factorial)
  have hsplit' :
      (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (j.factorial : ℝ))
        + ∑' k : ℕ, (1 : ℝ) / ((k + (n + 1)).factorial : ℝ)
        = ∑' j : ℕ, (1 : ℝ) / (j.factorial : ℝ) := by
    simpa using hsplit
  calc
    (∑' j : ℕ, (1 : ℝ) / (j.factorial : ℝ))
        = (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (j.factorial : ℝ))
            + ∑' k : ℕ, (1 : ℝ) / ((k + (n + 1)).factorial : ℝ) := hsplit'.symm
    _ = (∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (j.factorial : ℝ))
            + ∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ) := by
          congr
          funext k
          have hk : k + (n + 1) = n + (k + 1) := by omega
          rw [hk]

/-- Helper for Proposition 4.5.4: after scaling the finite prefix by `n!`, one gets a natural-number cast. -/
lemma helperForProposition_4_5_4_factorialScaledFinitePart_isNatCast
    (n : ℕ) :
    ∃ A : ℕ,
      (n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i.factorial : ℝ)) = (A : ℝ) := by
  refine ⟨(∑ i ∈ Finset.range (n + 1), n.factorial / i.factorial), ?_⟩
  calc
    (n.factorial : ℝ) * (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i.factorial : ℝ))
        = ∑ i ∈ Finset.range (n + 1), (n.factorial : ℝ) * ((1 : ℝ) / (i.factorial : ℝ)) := by
            rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), (((n.factorial / i.factorial : ℕ)) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hdiv : i.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hi_le
          have hfac_ne : ((i.factorial : ℝ) ≠ 0) := by positivity
          calc
            (n.factorial : ℝ) * ((1 : ℝ) / (i.factorial : ℝ))
                = (n.factorial : ℝ) / (i.factorial : ℝ) := by simp [div_eq_mul_inv]
            _ = (((n.factorial / i.factorial : ℕ)) : ℝ) := by
                symm
                exact Nat.cast_div hdiv hfac_ne
    _ = ((∑ i ∈ Finset.range (n + 1), n.factorial / i.factorial : ℕ) : ℝ) := by
          simpa using (Nat.cast_sum (Finset.range (n + 1)) (fun i => n.factorial / i.factorial)).symm

/-- Helper for Proposition 4.5.4: scaling the factorial tail by `n!` yields a remainder in `(0,1)`. -/
lemma helperForProposition_4_5_4_factorialScaledTail_between_zero_one
    (n : ℕ) (hn : 3 ≤ n) :
    0 < (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) ∧
      (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) < 1 := by
  have hTail := factorial_tail_sum_pos_and_lt_inv_factorial n hn
  rcases hTail with ⟨hTailPos, hTailLt⟩
  have hFacPos : 0 < (n.factorial : ℝ) := by positivity
  have hLeft :
      0 < (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) := by
    exact mul_pos hFacPos hTailPos
  have hRightMul :
      (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ))
        < (n.factorial : ℝ) * ((1 : ℝ) / (n.factorial : ℝ)) := by
    exact mul_lt_mul_of_pos_left hTailLt hFacPos
  have hFacNe : (n.factorial : ℝ) ≠ 0 := by positivity
  have hCancel : (n.factorial : ℝ) * ((1 : ℝ) / (n.factorial : ℝ)) = 1 := by
    field_simp [hFacNe]
  have hRight :
      (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)) < 1 := by
    calc
      (n.factorial : ℝ) * (∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ))
          < (n.factorial : ℝ) * ((1 : ℝ) / (n.factorial : ℝ)) := hRightMul
      _ = 1 := hCancel
  exact ⟨hLeft, hRight⟩

/-- Helper for Proposition 4.5.4: no integer cast lies strictly between two consecutive integer casts. -/
lemma helperForProposition_4_5_4_noInt_between_consecutiveIntCasts
    (z m : ℤ) :
    ¬ ((z : ℝ) < (m : ℝ) ∧ (m : ℝ) < ((z + 1 : ℤ) : ℝ)) := by
  intro h
  rcases h with ⟨hzm, hmz1⟩
  have hzmInt : z < m := by exact_mod_cast hzm
  have hmz1Int : m < z + 1 := by exact_mod_cast hmz1
  have hmle : m ≤ z := (Int.lt_add_one_iff).1 hmz1Int
  exact (not_lt_of_ge hmle) hzmInt

/-- Proposition 4.5.4: for every integer `n ≥ 3`, the real number `n! * e`
is not an integer. -/
theorem factorial_mul_e_not_integer
    (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ m : ℤ, (n.factorial : ℝ) * realEulerNumber = (m : ℝ) := by
  intro hm
  rcases hm with ⟨m, hm⟩
  let S : ℝ := ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i.factorial : ℝ)
  let T : ℝ := ∑' k : ℕ, (1 : ℝ) / ((n + (k + 1)).factorial : ℝ)
  have hSplitSeries : (∑' j : ℕ, (1 : ℝ) / (j.factorial : ℝ)) = S + T := by
    simpa [S, T] using helperForProposition_4_5_4_tsum_split_at_factorial_index n
  have hEulerSplit : realEulerNumber = S + T := by
    calc
      realEulerNumber = ∑' j : ℕ, (1 : ℝ) / (j.factorial : ℝ) := realEulerNumber_eq_tsum
      _ = S + T := hSplitSeries
  have hScaledSplit :
      (n.factorial : ℝ) * realEulerNumber = (n.factorial : ℝ) * S + (n.factorial : ℝ) * T := by
    calc
      (n.factorial : ℝ) * realEulerNumber = (n.factorial : ℝ) * (S + T) := by rw [hEulerSplit]
      _ = (n.factorial : ℝ) * S + (n.factorial : ℝ) * T := by ring
  rcases helperForProposition_4_5_4_factorialScaledFinitePart_isNatCast n with ⟨A, hA⟩
  have hTailBounds :
      0 < (n.factorial : ℝ) * T ∧ (n.factorial : ℝ) * T < 1 := by
    simpa [T] using helperForProposition_4_5_4_factorialScaledTail_between_zero_one n hn
  rcases hTailBounds with ⟨hTailPos, hTailLtOne⟩
  have hmEq : (m : ℝ) = (A : ℝ) + (n.factorial : ℝ) * T := by
    calc
      (m : ℝ) = (n.factorial : ℝ) * realEulerNumber := by simpa [hm] using hm.symm
      _ = (n.factorial : ℝ) * S + (n.factorial : ℝ) * T := hScaledSplit
      _ = (A : ℝ) + (n.factorial : ℝ) * T := by rw [hA]
  have hLower : (A : ℝ) < (m : ℝ) := by
    calc
      (A : ℝ) < (A : ℝ) + (n.factorial : ℝ) * T := by linarith [hTailPos]
      _ = (m : ℝ) := hmEq.symm
  have hUpper : (m : ℝ) < (A : ℝ) + 1 := by
    calc
      (m : ℝ) = (A : ℝ) + (n.factorial : ℝ) * T := hmEq
      _ < (A : ℝ) + 1 := by linarith [hTailLtOne]
  have hLowerInt : ((Int.ofNat A : ℤ) : ℝ) < (m : ℝ) := by
    simpa using hLower
  have hUpperInt : (m : ℝ) < (((Int.ofNat A : ℤ) + 1 : ℤ) : ℝ) := by
    simpa [Int.cast_add, Int.cast_one] using hUpper
  exact helperForProposition_4_5_4_noInt_between_consecutiveIntCasts (Int.ofNat A) m
    ⟨hLowerInt, hUpperInt⟩

/- Proposition 4.5.5 helper block. -/
/-- Helper for Proposition 4.5.5: the cutoff definition coincides with
`expNegInvGlue`. -/
lemma helperForProposition_4_5_5_cutoff_eq_expNegInvGlue :
    (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) = expNegInvGlue := by
  funext x
  by_cases hx : 0 < x
  · have hxle : ¬ x ≤ 0 := not_le.mpr hx
    have hnegdiv : (-1 / x : ℝ) = -x⁻¹ := by
      have hx0 : x ≠ 0 := ne_of_gt hx
      field_simp [one_div, hx0]
    simp [expNegInvGlue, hx, hxle, hnegdiv]
  · have hx' : x ≤ 0 := le_of_not_gt hx
    simp [expNegInvGlue, hx, hx']

/-- Helper for Proposition 4.5.5: `ContDiff ℝ ⊤` implies analyticity at `0`. -/
lemma helperForProposition_4_5_5_contDiffTop_implies_analyticAt_zero
    {f : ℝ → ℝ} (hcont : ContDiff ℝ ⊤ f) :
    AnalyticAt ℝ f 0 :=
  (hcont.contDiffAt).analyticAt

/-- Helper for Proposition 4.5.5: as currently encoded, the target conjunction is inconsistent. -/
lemma helperForProposition_4_5_5_target_conjunction_inconsistent :
    ¬ (let f : ℝ → ℝ := fun x => if 0 < x then Real.exp (-1 / x) else 0
      ContDiff ℝ ⊤ f ∧ (∀ k : ℕ, iteratedDeriv k f 0 = 0) ∧ ¬ AnalyticAt ℝ f 0) := by
  intro h
  dsimp at h
  exact h.2.2 (helperForProposition_4_5_5_contDiffTop_implies_analyticAt_zero h.1)

/-- Helper for Proposition 4.5.5: all iterated derivatives of the cutoff vanish
on the negative half-line. -/
lemma helperForProposition_4_5_5_iteratedDeriv_zero_on_Iio :
    ∀ k : ℕ,
      Set.EqOn
        (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        (fun _ => (0 : ℝ))
        (Set.Iio (0 : ℝ)) := by
  intro k
  have hEqOn :
      Set.EqOn
        (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0)
        (fun _ => (0 : ℝ))
        (Set.Iio (0 : ℝ)) := by
    intro x hx
    have hxle : x ≤ 0 := le_of_lt hx
    rw [helperForProposition_4_5_5_cutoff_eq_expNegInvGlue]
    exact expNegInvGlue.zero_of_nonpos hxle
  have hEqOnIter :
      Set.EqOn
        (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        (iteratedDeriv k (fun _ : ℝ => (0 : ℝ)))
        (Set.Iio (0 : ℝ)) :=
    Set.EqOn.iteratedDeriv_of_isOpen hEqOn isOpen_Iio k
  intro x hx
  have hxEq :
      iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) x
        = iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x :=
    hEqOnIter hx
  have hconst : iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) x = (if k = 0 then (0 : ℝ) else 0) := by
    simpa using (iteratedDeriv_const (n := k) (c := (0 : ℝ)) (x := x))
  by_cases hk : k = 0
  · subst hk
    simpa [hxEq] using hconst
  · simp [hk] at hconst
    simpa [hxEq, hconst]

/-- Helper for Proposition 4.5.5: smoothness forces every iterated derivative
of the cutoff to vanish at `0`. -/
lemma helperForProposition_4_5_5_iteratedDeriv_zero_at_zero
    (hcont : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0)) :
    ∀ k : ℕ,
      iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) 0 = 0 := by
  intro k
  have hEqOnLeft :
      Set.EqOn
        (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        (fun _ => (0 : ℝ))
        (Set.Iio (0 : ℝ)) :=
    helperForProposition_4_5_5_iteratedDeriv_zero_on_Iio k
  have hContIter :
      Continuous (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0)) :=
    by
      have hk' : (k : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      have hk : (↑k : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast hk'
      exact hcont.continuous_iteratedDeriv k hk
  have hTendstoValue :
      Filter.Tendsto
        (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        (𝓝[<] (0 : ℝ))
        (𝓝 (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) 0)) :=
    (hContIter.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hEventuallyEqLeft :
      (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        =ᶠ[𝓝[<] (0 : ℝ)]
          (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hEqOnLeft hx
  have hTendstoZero :
      Filter.Tendsto
        (iteratedDeriv k (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0))
        (𝓝[<] (0 : ℝ))
        (𝓝 (0 : ℝ)) := by
    have hConst :
        Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    exact Filter.Tendsto.congr' hEventuallyEqLeft.symm hConst
  have hNeBotLeft : (𝓝[<] (0 : ℝ)).NeBot :=
    nhdsWithin_Iio_neBot (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl
  haveI : (𝓝[<] (0 : ℝ)).NeBot := hNeBotLeft
  exact tendsto_nhds_unique hTendstoValue hTendstoZero

/-- Helper for Proposition 4.5.5: the cutoff is not analytic at `0`. -/
lemma helperForProposition_4_5_5_not_analytic_at_zero :
    ¬ AnalyticAt ℝ (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) 0 := by
  have hf : (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) = expNegInvGlue :=
    helperForProposition_4_5_5_cutoff_eq_expNegInvGlue
  intro hAnalytic
  rcases AnalyticAt.eventually_eq_zero_or_eventually_ne_zero hAnalytic with hZero | hNonzero
  · have hZeroRight :
        ∀ᶠ z in 𝓝[>] (0 : ℝ),
          (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) z = 0 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hZero
    have hNonzeroRight :
        ∀ᶠ z in 𝓝[>] (0 : ℝ),
          (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) z ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hpos : 0 < (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) z := by
        rw [hf]
        exact expNegInvGlue.pos_of_pos hz
      exact ne_of_gt hpos
    have hFalse : ∀ᶠ z in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hZeroRight, hNonzeroRight] with z hz0 hzn0
      exact hzn0 hz0
    have hEmpty : (∅ : Set ℝ) ∈ 𝓝[>] (0 : ℝ) := by
      simpa [Filter.eventually_iff] using hFalse
    have hBot : (𝓝[>] (0 : ℝ)) = ⊥ := (Filter.empty_mem_iff_bot).1 hEmpty
    have hNeBot : (𝓝[>] (0 : ℝ)).NeBot :=
      nhdsWithin_Ioi_neBot (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl
    exact hNeBot.ne hBot
  · have hSubset : Set.Iio (0 : ℝ) ⊆ ({(0 : ℝ)}ᶜ) := by
      intro z hz
      exact Set.mem_compl_singleton_iff.mpr (ne_of_lt hz)
    have hNonzeroLeft :
        ∀ᶠ z in 𝓝[<] (0 : ℝ),
          (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) z ≠ 0 :=
      Filter.Eventually.filter_mono (nhdsWithin_mono (0 : ℝ) hSubset) hNonzero
    have hZeroLeft :
        ∀ᶠ z in 𝓝[<] (0 : ℝ),
          (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) z = 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzle : z ≤ 0 := le_of_lt hz
      have hznot : ¬ 0 < z := not_lt.mpr hzle
      simp [hznot]
    have hFalse : ∀ᶠ z in 𝓝[<] (0 : ℝ), False := by
      filter_upwards [hZeroLeft, hNonzeroLeft] with z hz0 hzn0
      exact hzn0 hz0
    have hEmpty : (∅ : Set ℝ) ∈ 𝓝[<] (0 : ℝ) := by
      simpa [Filter.eventually_iff] using hFalse
    have hBot : (𝓝[<] (0 : ℝ)) = ⊥ := (Filter.empty_mem_iff_bot).1 hEmpty
    have hNeBot : (𝓝[<] (0 : ℝ)).NeBot :=
      nhdsWithin_Iio_neBot (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl
    exact hNeBot.ne hBot

/-- Proposition 4.5.5: define `f : ℝ → ℝ` by
`f x = exp (-1 / x)` for `x > 0` and `f x = 0` for `x ≤ 0`.
Then `f` is smooth on `ℝ`, all derivatives vanish at `0`
(equivalently, for every integer `k ≥ 0`, `f^(k)(0) = 0`),
and `f` is not real analytic at `0`. -/
theorem flat_exp_cutoff_smooth_all_derivs_zero_not_analytic_at_zero :
    let f : ℝ → ℝ := fun x => if 0 < x then Real.exp (-1 / x) else 0
    ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ (∀ k : ℕ, iteratedDeriv k f 0 = 0) ∧ ¬ AnalyticAt ℝ f 0 := by
  let f : ℝ → ℝ := fun x => if 0 < x then Real.exp (-1 / x) else 0
  have hf : f = expNegInvGlue := by
    simpa [f] using helperForProposition_4_5_5_cutoff_eq_expNegInvGlue
  have hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by
    rw [hf]
    exact expNegInvGlue.contDiff
  have hDerivsZero : ∀ k : ℕ, iteratedDeriv k f 0 = 0 := by
    simpa [f] using helperForProposition_4_5_5_iteratedDeriv_zero_at_zero hSmooth
  have hNotAnalytic : ¬ AnalyticAt ℝ f 0 := by
    simpa [f] using helperForProposition_4_5_5_not_analytic_at_zero
  exact ⟨hSmooth, hDerivsZero, hNotAnalytic⟩

/-- Helper for Proposition 4.5.6: analyticity on all of `ℝ` implies global differentiability. -/
lemma helperForProposition_4_5_6_differentiable_of_analyticOn_univ
    {f : ℝ → ℝ}
    (hf_analytic : AnalyticOn ℝ f Set.univ) :
    Differentiable ℝ f := by
  simpa [differentiableOn_univ] using hf_analytic.differentiableOn

/-- Helper for Proposition 4.5.6: the derivative of `log ∘ f` is constantly `1`. -/
lemma helperForProposition_4_5_6_deriv_log_eq_one
    {f : ℝ → ℝ}
    (hf_pos : ∀ x : ℝ, 0 < f x)
    (hf_diff : Differentiable ℝ f)
    (hf_deriv : ∀ x : ℝ, deriv f x = f x) :
    ∀ x : ℝ, deriv (fun y : ℝ => Real.log (f y)) x = 1 := by
  intro x
  have hf_ne : f x ≠ 0 := ne_of_gt (hf_pos x)
  have hHasDeriv : HasDerivAt f (deriv f x) x := (hf_diff x).hasDerivAt
  have hHasDerivLog :
      HasDerivAt (fun y : ℝ => Real.log (f y)) (deriv f x / f x) x :=
    hHasDeriv.log hf_ne
  calc
    deriv (fun y : ℝ => Real.log (f y)) x = deriv f x / f x := hHasDerivLog.deriv
    _ = f x / f x := by rw [hf_deriv x]
    _ = 1 := by simp [hf_ne]

/-- Helper for Proposition 4.5.6: `x ↦ log (f x) - x` is constant on `ℝ`. -/
lemma helperForProposition_4_5_6_log_sub_id_constant
    {f : ℝ → ℝ}
    (hf_pos : ∀ x : ℝ, 0 < f x)
    (hf_diff : Differentiable ℝ f)
    (hf_deriv : ∀ x : ℝ, deriv f x = f x) :
    ∀ x : ℝ, Real.log (f x) - x = Real.log (f 0) := by
  have hDerivLog :
      ∀ x : ℝ, deriv (fun y : ℝ => Real.log (f y)) x = 1 :=
    helperForProposition_4_5_6_deriv_log_eq_one hf_pos hf_diff hf_deriv
  have hDiffLog : Differentiable ℝ (fun y : ℝ => Real.log (f y)) := by
    intro x
    have hf_ne : f x ≠ 0 := ne_of_gt (hf_pos x)
    exact ((hf_diff x).hasDerivAt.log hf_ne).differentiableAt
  have hDiffSub : Differentiable ℝ (fun y : ℝ => Real.log (f y) - y) :=
    hDiffLog.sub differentiable_id
  have hDerivSubZero : ∀ x : ℝ, deriv (fun y : ℝ => Real.log (f y) - y) x = 0 := by
    intro x
    have hf_ne : f x ≠ 0 := ne_of_gt (hf_pos x)
    have hDiffLogAt : DifferentiableAt ℝ (fun y : ℝ => Real.log (f y)) x :=
      ((hf_diff x).hasDerivAt.log hf_ne).differentiableAt
    have hDerivId : deriv (fun y : ℝ => y) x = 1 := by
      simpa using (deriv_id (x := x) (𝕜 := ℝ))
    calc
      deriv (fun y : ℝ => Real.log (f y) - y) x
          = deriv (fun y : ℝ => Real.log (f y)) x - deriv (fun y : ℝ => y) x :=
            deriv_sub hDiffLogAt differentiableAt_id
      _ = 1 - 1 := by rw [hDerivLog x, hDerivId]
      _ = 0 := by ring
  intro x
  have hConst :
      (fun y : ℝ => Real.log (f y) - y) x = (fun y : ℝ => Real.log (f y) - y) 0 :=
    is_const_of_deriv_eq_zero hDiffSub hDerivSubZero x 0
  simpa using hConst

/-- Helper for Proposition 4.5.6: the solution has the form `f x = f 0 * exp x`. -/
lemma helperForProposition_4_5_6_exp_form
    {f : ℝ → ℝ}
    (hf_pos : ∀ x : ℝ, 0 < f x)
    (hlog_const : ∀ x : ℝ, Real.log (f x) - x = Real.log (f 0)) :
    ∀ x : ℝ, f x = f 0 * Real.exp x := by
  intro x
  have hLogEq : Real.log (f x) = x + Real.log (f 0) := by
    linarith [hlog_const x]
  calc
    f x = Real.exp (Real.log (f x)) := by rw [Real.exp_log (hf_pos x)]
    _ = Real.exp (x + Real.log (f 0)) := by rw [hLogEq]
    _ = Real.exp x * Real.exp (Real.log (f 0)) := by rw [Real.exp_add]
    _ = Real.exp x * f 0 := by rw [Real.exp_log (hf_pos 0)]
    _ = f 0 * Real.exp x := by ring

/-- Proposition 4.5.6: if `f : ℝ → (0, ∞)` is real analytic and satisfies
`f'(x) = f(x)` for all `x ∈ ℝ`, then there exists a constant `C > 0` such that
`f(x) = C e^x` for all `x ∈ ℝ`. -/
theorem analytic_deriv_eq_self_exists_pos_const_mul_exp
    {f : ℝ → ℝ}
    (hf_pos : ∀ x : ℝ, 0 < f x)
    (hf_analytic : AnalyticOn ℝ f Set.univ)
    (hf_deriv : ∀ x : ℝ, deriv f x = f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, f x = C * Real.exp x := by
  have hf_diff : Differentiable ℝ f :=
    helperForProposition_4_5_6_differentiable_of_analyticOn_univ hf_analytic
  have hLogConst : ∀ x : ℝ, Real.log (f x) - x = Real.log (f 0) :=
    helperForProposition_4_5_6_log_sub_id_constant hf_pos hf_diff hf_deriv
  have hExpForm : ∀ x : ℝ, f x = f 0 * Real.exp x :=
    helperForProposition_4_5_6_exp_form hf_pos hLogConst
  refine ⟨f 0, hf_pos 0, ?_⟩
  intro x
  exact hExpForm x

/-- Proposition 4.5.7: for every natural number `m ≥ 1`,
`lim_{x→+∞} (exp x / x^m) = +∞`. -/
theorem exp_div_pow_tendsto_atTop
    (m : ℕ) (hm : 1 ≤ m) :
    Filter.Tendsto (fun x : ℝ => Real.exp x / x ^ m) Filter.atTop Filter.atTop := by
  simpa using Real.tendsto_exp_div_pow_atTop m

/-- Helper for Proposition 4.5.8: rewriting the composed polynomial at a scaled input. -/
lemma helperForProposition_4_5_8_scaledEval_rewrite
    (P : Polynomial ℝ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    let Q : Polynomial ℝ := P.comp (Polynomial.C (1 / c) * Polynomial.X)
    Q.eval (c * x) = P.eval x := by
  let Q : Polynomial ℝ := P.comp (Polynomial.C (1 / c) * Polynomial.X)
  calc
    Q.eval (c * x)
        = P.eval (Polynomial.eval (c * x) (Polynomial.C (1 / c) * Polynomial.X)) := by
            simp [Q, Polynomial.eval_comp]
    _ = P.eval ((1 / c) * (c * x)) := by
          simp [Polynomial.eval_mul]
    _ = P.eval x := by
          congr 1
          field_simp [hc.ne']

/-- Helper for Proposition 4.5.8: the ratio `P(x) / exp(c x)` tends to `0` at `+∞`. -/
lemma helperForProposition_4_5_8_tendsto_div_exp_mul_atTop
    (P : Polynomial ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ => P.eval x / Real.exp (c * x)) Filter.atTop (nhds 0) := by
  let Q : Polynomial ℝ := P.comp (Polynomial.C (1 / c) * Polynomial.X)
  have hQ : Filter.Tendsto (fun y : ℝ => Q.eval y / Real.exp y) Filter.atTop (nhds 0) :=
    Polynomial.tendsto_div_exp_atTop Q
  have hScale : Filter.Tendsto (fun x : ℝ => c * x) Filter.atTop Filter.atTop := by
    refine (Filter.tendsto_const_mul_atTop_of_pos (f := fun x : ℝ => x) (r := c)
      (l := Filter.atTop) hc).2 ?_
    simpa using (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ => x) Filter.atTop Filter.atTop)
  have hComp : Filter.Tendsto (fun x : ℝ => Q.eval (c * x) / Real.exp (c * x))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp] using hQ.comp hScale
  have hEqFun :
      (fun x : ℝ => Q.eval (c * x) / Real.exp (c * x))
        = (fun x : ℝ => P.eval x / Real.exp (c * x)) := by
    funext x
    have hx : Q.eval (c * x) = P.eval x := by
      simpa [Q] using helperForProposition_4_5_8_scaledEval_rewrite P hc x
    simp [hx]
  simpa [hEqFun] using hComp

/-- Helper for Proposition 4.5.8: eventually, `|P(x)|` is strictly below `exp(c x)`. -/
lemma helperForProposition_4_5_8_eventually_abs_lt_exp_mul
    (P : Polynomial ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in Filter.atTop, |P.eval x| < Real.exp (c * x) := by
  have hTendsto :
      Filter.Tendsto (fun x : ℝ => P.eval x / Real.exp (c * x)) Filter.atTop (nhds 0) :=
    helperForProposition_4_5_8_tendsto_div_exp_mul_atTop P hc
  have hLeft : (-1 : ℝ) < 0 := by norm_num
  have hRight : (0 : ℝ) < 1 := by norm_num
  have hEventuallyIoo :
      ∀ᶠ x : ℝ in Filter.atTop, (P.eval x / Real.exp (c * x)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine hTendsto ?_
    exact Ioo_mem_nhds hLeft hRight
  filter_upwards [hEventuallyIoo] with x hx
  have hxAbs : |P.eval x / Real.exp (c * x)| < 1 := by
    exact (abs_lt).2 hx
  have hExpPos : 0 < Real.exp (c * x) := Real.exp_pos (c * x)
  have hDiv : |P.eval x| / Real.exp (c * x) < 1 := by
    simpa [abs_div, abs_of_pos hExpPos] using hxAbs
  have hMul : |P.eval x| < (1 : ℝ) * Real.exp (c * x) := by
    exact (div_lt_iff₀ hExpPos).1 hDiv
  simpa using hMul

/-- Helper for Proposition 4.5.8: convert an eventual `atTop` property into a threshold statement. -/
lemma helperForProposition_4_5_8_eventually_atTop_to_threshold
    {R : ℝ → Prop} (hR : ∀ᶠ x : ℝ in Filter.atTop, R x) :
    ∃ N : ℝ, ∀ x : ℝ, x > N → R x := by
  rcases (Filter.eventually_atTop.mp hR) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x hx
  exact hN x (le_of_lt hx)

/-- Proposition 4.5.8: if `P` is a real polynomial and `c > 0`, then there exists
`N : ℝ` such that for all real `x > N`, one has `exp (c x) > |P(x)|`. -/
theorem exp_mul_gt_abs_polynomial_eventually
    (P : Polynomial ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℝ, ∀ x : ℝ, x > N → Real.exp (c * x) > |P.eval x| := by
  have hEventual :
      ∀ᶠ x : ℝ in Filter.atTop, |P.eval x| < Real.exp (c * x) :=
    helperForProposition_4_5_8_eventually_abs_lt_exp_mul P hc
  exact helperForProposition_4_5_8_eventually_atTop_to_threshold hEventual

/-- Helper for Proposition 4.5.9: continuity of the positive-base coordinate map. -/
lemma helperForProposition_4_5_9_continuous_baseCoordinate :
    Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => ((p.1 : Set.Ioi (0 : ℝ)) : ℝ)) := by
  exact continuous_subtype_val.comp continuous_fst

/-- Helper for Proposition 4.5.9: the base in `(0,+∞)` is always nonzero. -/
lemma helperForProposition_4_5_9_rpow_sideCondition :
    ∀ p : Set.Ioi (0 : ℝ) × ℝ, ((p.1 : ℝ) ≠ 0 ∨ 0 < p.2) := by
  intro p
  exact Or.inl (ne_of_gt p.1.property)

/-- Proposition 4.5.9: define `f : (0,+∞) × ℝ → ℝ` by `f(x,y) = x^y`, where
`x^y = exp (y ln x)` for `x > 0` and `y ∈ ℝ`; then `f` is continuous on
`(0,+∞) × ℝ`. -/
theorem positive_rpow_map_continuous_on_Ioi_prod :
    Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => ((p.1 : ℝ) ^ p.2)) := by
  have hBase :
      Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => ((p.1 : Set.Ioi (0 : ℝ)) : ℝ)) :=
    helperForProposition_4_5_9_continuous_baseCoordinate
  have hExp : Continuous (fun p : Set.Ioi (0 : ℝ) × ℝ => p.2) :=
    continuous_snd
  have hSide : ∀ p : Set.Ioi (0 : ℝ) × ℝ, ((p.1 : ℝ) ≠ 0 ∨ 0 < p.2) :=
    helperForProposition_4_5_9_rpow_sideCondition
  simpa using hBase.rpow hExp hSide

/-- Helper for Theorem 4.5.12: the denominator of a rational divides
`(max 3 q.den)!`. -/
lemma helperForTheorem_4_5_12_factorialDenominator_dvd_factorialMax
    (q : ℚ) :
    q.den ∣ Nat.factorial (max 3 q.den) := by
  refine Nat.dvd_factorial ?_ ?_
  · exact Nat.pos_of_ne_zero q.den_nz
  · exact Nat.le_max_right 3 q.den

/-- Helper for Theorem 4.5.12: multiplying a rational by a suitable factorial
gives an integer cast in `ℝ`. -/
lemma helperForTheorem_4_5_12_factorialScaledRat_isIntCast
    (q : ℚ) :
    ∃ m : ℤ, (((max 3 q.den).factorial : ℝ) * (q : ℝ)) = (m : ℝ) := by
  let n : ℕ := (max 3 q.den).factorial
  have hden_dvd : q.den ∣ n := by
    change q.den ∣ Nat.factorial (max 3 q.den)
    exact helperForTheorem_4_5_12_factorialDenominator_dvd_factorialMax q
  rcases hden_dvd with ⟨k, hk⟩
  refine ⟨(Int.ofNat k) * q.num, ?_⟩
  have hqden_ne : (q.den : ℝ) ≠ 0 := by
    exact_mod_cast q.den_nz
  have hk_real : (n : ℝ) / (q.den : ℝ) = (k : ℝ) := by
    calc
      (n : ℝ) / (q.den : ℝ) = ((q.den * k : ℕ) : ℝ) / (q.den : ℝ) := by simpa [hk]
      _ = ((q.den : ℝ) * (k : ℝ)) / (q.den : ℝ) := by norm_num
      _ = (k : ℝ) := by field_simp [hqden_ne]
  calc
    (((max 3 q.den).factorial : ℝ) * (q : ℝ))
        = (n : ℝ) * ((q.num : ℝ) / (q.den : ℝ)) := by simp [n, Rat.cast_def]
    _ = ((n : ℝ) / (q.den : ℝ)) * (q.num : ℝ) := by ring_nf
    _ = (k : ℝ) * (q.num : ℝ) := by rw [hk_real]
    _ = (((Int.ofNat k) * q.num : ℤ) : ℝ) := by norm_num

/-- Helper for Theorem 4.5.12: `exp 1` is not equal to any rational cast. -/
lemma helperForTheorem_4_5_12_exp_one_ne_ratCast
    (q : ℚ) :
    Real.exp 1 ≠ (q : ℝ) := by
  intro hq
  rcases helperForTheorem_4_5_12_factorialScaledRat_isIntCast q with ⟨m, hm⟩
  have hIntWitness :
      ∃ z : ℤ, (((max 3 q.den).factorial : ℝ) * realEulerNumber) = (z : ℝ) := by
    refine ⟨m, ?_⟩
    calc
      (((max 3 q.den).factorial : ℝ) * realEulerNumber)
          = (((max 3 q.den).factorial : ℝ) * Real.exp 1) := by simp [realEulerNumber]
      _ = (((max 3 q.den).factorial : ℝ) * (q : ℝ)) := by rw [hq]
      _ = (m : ℝ) := hm
  exact (factorial_mul_e_not_integer (max 3 q.den) (Nat.le_max_left 3 q.den)) hIntWitness

/-- Theorem 4.5.12: The number `e` is irrational. -/
theorem realEulerNumber_irrational :
    Irrational (Real.exp 1) := by
  intro hRat
  rcases hRat with ⟨q, hq⟩
  exact (helperForTheorem_4_5_12_exp_one_ne_ratCast q) hq.symm

/-- Theorem 4.5.13: The natural logarithm function `ln : (0,+∞) → ℝ`
is real analytic on `(0,+∞)`. -/
theorem logarithm_real_analytic_on_Ioi :
    AnalyticOn ℝ Real.log (Set.Ioi (0 : ℝ)) := by
  simpa using analyticOn_log

end Section05
end Chap04
