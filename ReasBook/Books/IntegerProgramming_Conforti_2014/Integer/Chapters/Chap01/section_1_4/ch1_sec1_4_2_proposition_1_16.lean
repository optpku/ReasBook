module

public import Mathlib.Data.Nat.Log

public section

/-- A positive natural-number sequence that at least halves at every counted update has at most
`Nat.log2 (u 0)` counted updates. -/
theorem halvingStepCount_le_log2
    (u : ℕ → ℕ) (halvingCount : ℕ) (hu0 : 1 ≤ u 0)
    (hstep : ∀ i < halvingCount, 1 ≤ u (i + 1) ∧ 2 * u (i + 1) ≤ u i) :
    halvingCount ≤ Nat.log2 (u 0) := by
  -- Accumulate every doubling inequality into one bound at the initial value.
  have scaledHalvingBound : ∀ i ≤ halvingCount, 2 ^ i * u i ≤ u 0 := by
    intro i hi
    induction i with
    | zero =>
        simpa only [Nat.pow_zero, Nat.one_mul] using Nat.le_refl (u 0)
    | succ i ih =>
        have hi_lt : i < halvingCount := Nat.lt_of_succ_le hi
        calc
          2 ^ (i + 1) * u (i + 1) = 2 ^ i * (2 * u (i + 1)) := by
            simp only [Nat.pow_succ, Nat.mul_assoc]
          _ ≤ 2 ^ i * u i := Nat.mul_le_mul_left _ (hstep i hi_lt).2
          _ ≤ u 0 := ih (Nat.le_of_lt hi_lt)
  -- Positivity at the final step lets us discard the last sequence value.
  have hterminal : 1 ≤ u halvingCount := by
    cases halvingCount with
    | zero => simpa only using hu0
    | succ i => exact (hstep i (Nat.lt_succ_self i)).1
  have hpow : 2 ^ halvingCount ≤ u 0 := by
    calc
      2 ^ halvingCount = 2 ^ halvingCount * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ halvingCount * u halvingCount := Nat.mul_le_mul_left _ hterminal
      _ ≤ u 0 := scaledHalvingBound halvingCount (Nat.le_refl _)
  -- The standard characterization of `Nat.log2` now closes the count bound.
  have hu0_ne : u 0 ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hu0)
  exact (Nat.le_log2 hu0_ne).2 hpow

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_proposition_1_16.lean.
Proposition 1.16: if each non-horizontal and non-vertical boundary segment comes from an
iteration whose positive integer parameter drops to at most half its previous value, and there
are at most three additional horizontal or vertical boundary segments, then the total number of
boundary segments is at most `3 + Nat.log2 (u 0)`. -/
theorem boundarySegmentCount_le_three_add_log2
    (u : ℕ → ℕ) (nonAxisSegments axisSegments : ℕ) (hu0 : 1 ≤ u 0)
    (hstep : ∀ i < nonAxisSegments, 1 ≤ u (i + 1) ∧ u (i + 1) ≤ u i / 2)
    (haxis : axisSegments ≤ 3) :
    nonAxisSegments + axisSegments ≤ 3 + Nat.log2 (u 0) := by
  -- Rewrite floor division by two as the doubling inequality used above.
  have doubleStep : ∀ i < nonAxisSegments,
      1 ≤ u (i + 1) ∧ 2 * u (i + 1) ≤ u i := by
    intro i hi
    refine ⟨(hstep i hi).1, ?_⟩
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le Nat.zero_lt_two).1 (hstep i hi).2
  have hnonAxis : nonAxisSegments ≤ Nat.log2 (u 0) :=
    halvingStepCount_le_log2 u nonAxisSegments hu0 doubleStep
  -- Bound the two kinds of segments separately and then commute the final sum.
  calc
    nonAxisSegments + axisSegments ≤ nonAxisSegments + 3 :=
      Nat.add_le_add_left haxis nonAxisSegments
    _ ≤ Nat.log2 (u 0) + 3 := Nat.add_le_add_right hnonAxis 3
    _ = 3 + Nat.log2 (u 0) := Nat.add_comm _ _

end

#print axioms boundarySegmentCount_le_three_add_log2
