import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_17

open scoped BigOperators Matrix

-- This exercise reuses the Chapter 5 owner `mixed_integer_feasible_set` for pure-integer
-- feasibility of `A x ≤ b`; deleting one row is kept as the direct source-facing omission of that
-- single inequality rather than as a parallel wrapper predicate.

section Exercise615

variable {m n : ℕ}

/-- Helper for Exercise 6.15: an integer vector is deleted-feasible for row `i` when it satisfies
every inequality except possibly the `i`th one. -/
abbrev deletedFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  ∀ j : Fin m, j ≠ i → (A *ᵥ fun k ↦ (x k : ℚ)) j ≤ b j

/-- Helper for Exercise 6.15: the parity signature of an integral vector is its coordinatewise
reduction modulo `2`. -/
abbrev paritySignature
    (x : Fin n → ℤ) : Fin n → ZMod 2 :=
  fun k ↦ (x k : ZMod 2)

/-- Helper for Exercise 6.15: the finite set of parity signatures realized by deleted-feasible
witnesses for row `i`. -/
noncomputable def deletedFeasibleParitySet
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Finset (Fin n → ZMod 2) :=
  letI : DecidablePred
      (fun p : Fin n → ZMod 2 ↦
        ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p) :=
    Classical.decPred _
  Finset.univ.filter
    (fun p ↦ ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p)

/-- Helper for Exercise 6.15: membership in the parity-signature set is exactly realization by a
deleted-feasible witness. -/
lemma mem_deletedFeasibleParitySet_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    {p : Fin n → ZMod 2} :
    p ∈ deletedFeasibleParitySet A b i ↔
      ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = p := by
  classical
  -- Unfold the filtered finite parity universe once and read off the realizing witness.
  simp [deletedFeasibleParitySet]

/-- Helper for Exercise 6.15: every deleted row has at least one realized parity signature. -/
lemma deletedFeasibleParitySet_nonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (i : Fin m) :
    (deletedFeasibleParitySet A b i).Nonempty := by
  rcases hdeleted i with ⟨x, hx⟩
  -- Record the parity signature of an existing deleted-feasible witness.
  refine ⟨paritySignature x, ?_⟩
  exact (mem_deletedFeasibleParitySet_iff A b i).2 ⟨x, hx, rfl⟩

/-- Helper for Exercise 6.15: any integral point satisfying all rows except `i` must strictly
violate the omitted row, because otherwise its real cast would be a point of
`mixed_integer_feasible_set`. -/
lemma deletedIntegralPointStrictlyViolatesOmittedRow
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i : Fin m}
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  -- If the omitted row also held, the real cast of `x` would satisfy every inequality and every
  -- coordinate integrality constraint.
  by_contra hnot
  apply hinfeasible
  refine ⟨fun k ↦ (x k : ℝ), ?_⟩
  rw [mem_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst hji
      have hnotR : (((A *ᵥ fun k ↦ (x k : ℚ)) j : ℚ) : ℝ) ≤ (b j : ℝ) := by
        exact_mod_cast not_lt.mp hnot
      simpa [Matrix.mulVec, dotProduct] using hnotR
    · have hxR : (((A *ᵥ fun k ↦ (x k : ℚ)) j : ℚ) : ℝ) ≤ (b j : ℝ) := by
        exact_mod_cast hx j hji
      simpa [Matrix.mulVec, dotProduct] using hxR
  · intro j hj
    exact ⟨x j, rfl⟩

/-- Helper for Exercise 6.15: coordinatewise parity equality forces each coordinate sum
`x k + y k` to be even. -/
lemma sameParitySumEven
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ k : Fin n, Even (x k + y k) := by
  intro k
  -- Reduce evenness to a `ZMod 2` vanishing statement where subtraction and addition agree.
  rw [← ZMod.intCast_eq_zero_iff_even]
  calc
    ((x k + y k : ℤ) : ZMod 2) = ((x k : ZMod 2) + (y k : ZMod 2)) := by
      simp
    _ = ((x k : ZMod 2) - (y k : ZMod 2)) := by
      rw [sub_eq_add_neg]
      simp
    _ = ((x k - y k : ℤ) : ZMod 2) := by
      simp
    _ = 0 := by
      rw [Int.cast_sub, hparity k, sub_self]

/-- Helper for Exercise 6.15: the integral midpoint of two vectors with the same parity signature
has rational coordinates equal to the arithmetic midpoint of the endpoint casts. -/
lemma sameParityMidpointEqAverage
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ k : Fin n,
      (((x k + y k) / 2 : ℤ) : ℚ) = (((x k : ℚ) + (y k : ℚ)) / 2) := by
  intro k
  -- First record that the midpoint numerator is divisible by `2`.
  have hsumEven : Even (x k + y k) := sameParitySumEven x y hparity k
  rw [even_iff_two_dvd] at hsumEven
  have htwoQ : ((2 : ℤ) : ℚ) ≠ 0 := by
    norm_num
  -- Then move integer division across the rational cast using that divisibility witness.
  calc
    (((x k + y k) / 2 : ℤ) : ℚ) = ((x k + y k : ℤ) : ℚ) / 2 := by
      exact Int.cast_div hsumEven htwoQ
    _ = (((x k : ℚ) + (y k : ℚ)) / 2) := by
      simp

/-- Helper for Exercise 6.15: the integral midpoint attached to a same-parity pair of integer
vectors. -/
def sameParityMidpoint
    (x y : Fin n → ℤ) : Fin n → ℤ :=
  fun k ↦ (x k + y k) / 2

/-- Helper for Exercise 6.15: every row value at a same-parity midpoint is the arithmetic average
of the row values at the endpoints. -/
lemma sameParityMidpointRowEqAverage
    (A : Matrix (Fin m) (Fin n) ℚ)
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ i : Fin m,
      (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i =
        (((A *ᵥ fun k ↦ (x k : ℚ)) i) + ((A *ᵥ fun k ↦ (y k : ℚ)) i)) / 2 := by
  intro i
  -- Rewrite the midpoint coordinates first, then move the average through the finite row sum.
  calc
    (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i
        = ∑ k : Fin n, A i k * (sameParityMidpoint x y k : ℚ) := by
            simp [Matrix.mulVec, dotProduct]
    _ = ∑ k : Fin n, A i k * ((((x k : ℚ) + (y k : ℚ)) / 2)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [sameParityMidpoint, sameParityMidpointEqAverage x y hparity k]
    _ = ∑ k : Fin n, (A i k * (x k : ℚ) + A i k * (y k : ℚ)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (∑ k : Fin n, (A i k * (x k : ℚ) + A i k * (y k : ℚ))) / 2 := by
          rw [← Finset.sum_div]
    _ = ((∑ k : Fin n, A i k * (x k : ℚ)) + ∑ k : Fin n, A i k * (y k : ℚ)) / 2 := by
          rw [Finset.sum_add_distrib]
    _ = (((A *ᵥ fun k ↦ (x k : ℚ)) i) + ((A *ᵥ fun k ↦ (y k : ℚ)) i)) / 2 := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 6.15: a same-parity midpoint of two deleted-feasible witnesses satisfies
every row omitted by neither endpoint. -/
lemma sameParityMidpointSatisfiesNonendpointRows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {i j r : Fin m}
    (hri : r ≠ i)
    (hrj : r ≠ j)
    (x y : Fin n → ℤ)
    (hx : deletedFeasible A b i x)
    (hy : deletedFeasible A b j y)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r ≤ b r := by
  -- Both endpoints satisfy row `r`, so the midpoint satisfies it by the row-average identity.
  have hxRow : (A *ᵥ fun k ↦ (x k : ℚ)) r ≤ b r := hx r hri
  have hyRow : (A *ᵥ fun k ↦ (y k : ℚ)) r ≤ b r := hy r hrj
  rw [sameParityMidpointRowEqAverage A x y hparity r]
  linarith

/-- Helper for Exercise 6.15: if two deleted-feasible witnesses have the same parity signature,
their integral midpoint must violate at least one omitted row, otherwise it would solve the full
system integrally. -/
lemma sameParityMidpointViolatesAnEndpoint
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i j : Fin m}
    (hij : i ≠ j)
    (x y : Fin n → ℤ)
    (hx : deletedFeasible A b i x)
    (hy : deletedFeasible A b j y)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i ∨
      b j < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) j := by
  -- If both omitted rows also held at the midpoint, the midpoint would be an integral point of the
  -- full system.
  by_contra hmid
  push Not at hmid
  apply hinfeasible
  refine ⟨fun k ↦ (sameParityMidpoint x y k : ℝ), ?_⟩
  rw [mem_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hri : r = i
    · subst hri
      have hrow : (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
        exact_mod_cast hmid.1
      simpa [Matrix.mulVec, dotProduct] using hrow
    · by_cases hrj : r = j
      · subst hrj
        have hrow : (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
          exact_mod_cast hmid.2
        simpa [Matrix.mulVec, dotProduct] using hrow
      · have hrowMid :
          (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r ≤ b r :=
            sameParityMidpointSatisfiesNonendpointRows A b hri hrj x y hx hy hparity
        have hrow :
            (((A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
          exact_mod_cast hrowMid
        simpa [Matrix.mulVec, dotProduct] using hrow
  · intro r hr
    exact ⟨sameParityMidpoint x y r, rfl⟩

/-- Helper for Exercise 6.15: the augmented rational row `(A i, b i)` whose common denominator
clears the `i`th inequality. -/
def rowAugmentedData
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Fin (n + 1) → ℚ :=
  Fin.append (A i) (fun _ ↦ b i)

/-- Helper for Exercise 6.15: the common denominator attached to the augmented row
`(A i, b i)`. -/
def rowCommonDenominator
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : ℕ :=
  rational_vector_common_denominator (rowAugmentedData A b i)

/-- Helper for Exercise 6.15: the integral coefficient vector obtained by clearing denominators in
the `i`th row. -/
def rowScaledCoeff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : Fin n → ℤ :=
  fun j ↦ common_denominator_scaled_vector (rowAugmentedData A b i) (Fin.castAdd 1 j)

/-- Helper for Exercise 6.15: the integral right-hand side obtained by clearing denominators in
the `i`th inequality. -/
def rowScaledRhs
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) : ℤ :=
  common_denominator_scaled_vector (rowAugmentedData A b i) (Fin.natAdd n 0)

/-- Helper for Exercise 6.15: the denominator-cleared slack of row `i` at the integral vector
`x`. Positive slack means strict violation of the `i`th inequality. -/
def rowScaledSlack
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : ℤ :=
  ∑ j : Fin n, rowScaledCoeff A b i j * x j - rowScaledRhs A b i

/-- Helper for Exercise 6.15: the nonnegative part of the cleared `i`th slack. This is the
discrete row-violation objective used in the parity-counting argument. -/
def rowViolationNat
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : ℕ :=
  Int.toNat (rowScaledSlack A b i x)

/-- Helper for Exercise 6.15: a prefix competitor for row `i` satisfies every earlier inequality
and strictly violates the `i`th one. -/
def prefixCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  (∀ r : Fin m, r < i → (A *ᵥ fun k ↦ (x k : ℚ)) r ≤ b r) ∧
    b i < (A *ᵥ fun k ↦ (x k : ℚ)) i

/-- Helper for Exercise 6.15: the augmented row common denominator is always nonzero. -/
lemma rowCommonDenominator_ne_zero
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m) :
    rowCommonDenominator A b i ≠ 0 := by
  -- This is the rowwise specialization of the common-denominator nonvanishing fact.
  simpa [rowCommonDenominator, rowAugmentedData] using
    rationalVectorCommonDenominator_ne_zero (v := rowAugmentedData A b i)

/-- Helper for Exercise 6.15: the cleared row slack is exactly the common denominator times the
rational slack `(A x)_i - b_i`. -/
lemma rowScaledSlack_cast_eq
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    (((rowScaledSlack A b i x : ℤ) : ℚ)) =
      (rowCommonDenominator A b i : ℚ) *
        (((A *ᵥ fun k ↦ (x k : ℚ)) i) - b i) := by
  -- Clear denominators once on the augmented row, then collect the scaled row slack.
  have hcoeff :
      ∀ j : Fin n, ((rowScaledCoeff A b i j : ℤ) : ℚ) =
        (rowCommonDenominator A b i : ℚ) * A i j := by
    intro j
    have hscaled :=
      congrFun (common_denominator_scaled_vector_eq_smul (v := rowAugmentedData A b i))
        (Fin.castAdd 1 j)
    simpa [rowScaledCoeff, rowCommonDenominator, rowAugmentedData] using hscaled
  have hrhs : ((rowScaledRhs A b i : ℤ) : ℚ) =
      (rowCommonDenominator A b i : ℚ) * b i := by
    have hscaled :=
      congrFun (common_denominator_scaled_vector_eq_smul (v := rowAugmentedData A b i))
        (Fin.natAdd n 0)
    simpa [rowScaledRhs, rowCommonDenominator, rowAugmentedData] using hscaled
  calc
    (((rowScaledSlack A b i x : ℤ) : ℚ))
        = (∑ j : Fin n, ((rowScaledCoeff A b i j : ℤ) : ℚ) * (x j : ℚ)) -
            ((rowScaledRhs A b i : ℤ) : ℚ) := by
              simp [rowScaledSlack]
    _ = (∑ j : Fin n, ((rowCommonDenominator A b i : ℚ) * A i j) * (x j : ℚ)) -
          ((rowScaledRhs A b i : ℤ) : ℚ) := by
            refine congrArg (fun t : ℚ ↦ t - ((rowScaledRhs A b i : ℤ) : ℚ)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hcoeff j]
    _ = (∑ j : Fin n, ((rowCommonDenominator A b i : ℚ) * A i j) * (x j : ℚ)) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            rw [hrhs]
    _ = (∑ j : Fin n, (rowCommonDenominator A b i : ℚ) * (A i j * (x j : ℚ))) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            refine congrArg (fun t : ℚ ↦ t - ((rowCommonDenominator A b i : ℚ) * b i)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = (rowCommonDenominator A b i : ℚ) * (∑ j : Fin n, A i j * (x j : ℚ)) -
          ((rowCommonDenominator A b i : ℚ) * b i) := by
            rw [Finset.mul_sum]
    _ = (rowCommonDenominator A b i : ℚ) *
          ((∑ j : Fin n, A i j * (x j : ℚ)) - b i) := by
            ring
    _ = (rowCommonDenominator A b i : ℚ) *
          (((A *ᵥ fun k ↦ (x k : ℚ)) i) - b i) := by
            simp [Matrix.mulVec, dotProduct]

/-- Helper for Exercise 6.15: positive denominator-cleared slack is equivalent to strict
violation of the original rational row inequality. -/
lemma rowScaledSlack_pos_iff_rowViolation
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    0 < rowScaledSlack A b i x ↔ b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  have hden_pos : 0 < (rowCommonDenominator A b i : ℚ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (rowCommonDenominator_ne_zero A b i)
  constructor
  · intro hslack
    have hslackQ : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
      exact_mod_cast hslack
    rw [rowScaledSlack_cast_eq A b i x] at hslackQ
    have hdiff : (0 : ℚ) < ((A *ᵥ fun k ↦ (x k : ℚ)) i - b i) := by
      nlinarith
    linarith
  · intro hviol
    have hdiff : (0 : ℚ) < ((A *ᵥ fun k ↦ (x k : ℚ)) i - b i) := by
      linarith
    have hslackQ : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
      rw [rowScaledSlack_cast_eq A b i x]
      nlinarith
    exact_mod_cast hslackQ

/-- Helper for Exercise 6.15: the natural row-violation objective is positive exactly at strict
violations of the original rational row inequality. -/
lemma rowViolationNat_pos_iff_rowViolation
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    0 < rowViolationNat A b i x ↔ b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := by
  constructor
  · intro hpos
    have hslackPos : 0 < rowScaledSlack A b i x := by
      by_contra hnot
      have hnonpos : rowScaledSlack A b i x ≤ 0 := le_of_not_gt hnot
      have hzero : rowViolationNat A b i x = 0 := by
        simp [rowViolationNat, Int.toNat_of_nonpos hnonpos]
      omega
    exact (rowScaledSlack_pos_iff_rowViolation A b i x).1 hslackPos
  · intro hviol
    have hslackPos : 0 < rowScaledSlack A b i x :=
      (rowScaledSlack_pos_iff_rowViolation A b i x).2 hviol
    have hcast : (0 : ℤ) < ((rowViolationNat A b i x : ℕ) : ℤ) := by
      -- Once the cleared slack is positive, the `toNat` coercion is definitionally stable.
      unfold rowViolationNat
      simpa [Int.toNat_of_nonneg hslackPos.le] using hslackPos
    exact_mod_cast hcast

/-- Helper for Exercise 6.15: the natural row-violation objective vanishes exactly on points that
satisfy the corresponding rational row inequality. -/
lemma rowViolationNat_eq_zero_iff_rowSatisfied
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    rowViolationNat A b i x = 0 ↔ (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i := by
  constructor
  · intro hzero
    by_contra hviol
    have hviol' : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := lt_of_not_ge hviol
    have hpos : 0 < rowViolationNat A b i x :=
      (rowViolationNat_pos_iff_rowViolation A b i x).2 hviol'
    omega
  · intro hsatisfied
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hviol : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i :=
      (rowViolationNat_pos_iff_rowViolation A b i x).1 hpos
    linarith

/-- Helper for Exercise 6.15: a satisfied row has nonpositive denominator-cleared slack. -/
lemma rowScaledSlack_nonpos_of_rowSatisfied
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ)
    (hsatisfied : (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i) :
    rowScaledSlack A b i x ≤ 0 := by
  -- Positive cleared slack would contradict the assumed row satisfaction.
  by_contra hnot
  have hpos : 0 < rowScaledSlack A b i x := lt_of_not_ge hnot
  have hviol : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i :=
    (rowScaledSlack_pos_iff_rowViolation A b i x).1 hpos
  linarith

/-- Helper for Exercise 6.15: a denominator-cleared row slack is nonpositive exactly when the
corresponding rational row inequality is satisfied. -/
lemma rowScaledSlack_nonpos_iff_rowSatisfied
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x : Fin n → ℤ) :
    rowScaledSlack A b i x ≤ 0 ↔ (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i := by
  constructor
  · intro hslack
    -- A strict rational violation would give a positive integral slack.
    by_contra hrow
    have hviol : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i := lt_of_not_ge hrow
    have hpos : 0 < rowScaledSlack A b i x :=
      (rowScaledSlack_pos_iff_rowViolation A b i x).2 hviol
    omega
  · intro hrow
    -- Clearing the positive common denominator preserves the row inequality.
    exact rowScaledSlack_nonpos_of_rowSatisfied A b i x hrow

/-- Helper for Exercise 6.15: in an infeasible family of integral inequalities, a point satisfying
all rows other than `i` has strictly positive slack at `i`. -/
lemma omittedSlack_pos_of_other_slacks_nonpos
    {ι X : Type*}
    (slack : ι → X → ℤ)
    (hinfeasible : ¬ ∃ x : X, ∀ i : ι, slack i x ≤ 0)
    {i : ι}
    {x : X}
    (hx : ∀ j : ι, j ≠ i → slack j x ≤ 0) :
    0 < slack i x := by
  -- Otherwise this same point would satisfy every row, including the omitted one.
  by_contra hnot
  apply hinfeasible
  refine ⟨x, ?_⟩
  intro j
  by_cases hji : j = i
  · subst hji
    exact le_of_not_gt hnot
  · exact hx j hji

/-- Helper for Exercise 6.15: a finite minimally infeasible family of integer-valued slacks has a
maximal nonnegative infeasible relaxation and a witness exactly one unit beyond each owned row. -/
lemma existsMaximalInfeasibleRelaxationWithTightWitnesses
    {ι X : Type*}
    [Fintype ι]
    (slack : ι → X → ℤ)
    (hinfeasible : ¬ ∃ x : X, ∀ i : ι, slack i x ≤ 0)
    (hdeleted : ∀ i : ι, ∃ x : X, ∀ j : ι, j ≠ i → slack j x ≤ 0) :
    ∃ q : ι → ℕ,
      (¬ ∃ x : X, ∀ i : ι, slack i x ≤ (q i : ℤ)) ∧
        ∀ i : ι, ∃ x : X,
          slack i x = (q i : ℤ) + 1 ∧
            ∀ j : ι, j ≠ i → slack j x ≤ (q j : ℤ) := by
  classical
  choose w hw using hdeleted
  let cap : ι → ℕ := fun i ↦ Int.toNat (slack i (w i))
  have hcap (i : ι) : (cap i : ℤ) = slack i (w i) := by
    -- Deleted feasibility forces the owned slack to be positive, so `toNat` loses no data.
    have hpos : 0 < slack i (w i) :=
      omittedSlack_pos_of_other_slacks_nonpos slack hinfeasible (hw i)
    simp [cap, Int.toNat_of_nonneg hpos.le]
  let Relaxation := (i : ι) → Fin (cap i + 1)
  let relaxationInfeasible : Relaxation → Prop :=
    fun q ↦ ¬ ∃ x : X, ∀ i : ι, slack i x ≤ ((q i : ℕ) : ℤ)
  let boundedInfeasible : Finset Relaxation :=
    Finset.univ.filter relaxationInfeasible
  let zeroRelaxation : Relaxation :=
    fun i ↦ ⟨0, Nat.zero_lt_succ (cap i)⟩
  have hzeroInfeasible : relaxationInfeasible zeroRelaxation := by
    -- The zero relaxation is precisely the original infeasible system.
    intro hzeroFeasible
    apply hinfeasible
    rcases hzeroFeasible with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i
    simpa [zeroRelaxation] using hx i
  have hzeroMem : zeroRelaxation ∈ boundedInfeasible := by
    simp [boundedInfeasible, hzeroInfeasible]
  obtain ⟨q, hqMem, hqMax⟩ :=
    boundedInfeasible.exists_max_image
      (fun r : Relaxation ↦ ∑ i : ι, (r i : ℕ)) ⟨zeroRelaxation, hzeroMem⟩
  have hqInfeasible : relaxationInfeasible q := by
    simpa [boundedInfeasible] using hqMem
  have hq_lt_cap (i : ι) : (q i : ℕ) < cap i := by
    have hq_le : (q i : ℕ) ≤ cap i := Nat.le_of_lt_succ (q i).isLt
    by_contra hnot
    have hqi : (q i : ℕ) = cap i := Nat.le_antisymm hq_le (not_lt.mp hnot)
    apply hqInfeasible
    refine ⟨w i, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      have hiEq : slack i (w i) = ((q i : ℕ) : ℤ) := by
        calc
          slack i (w i) = (cap i : ℤ) := (hcap i).symm
          _ = ((q i : ℕ) : ℤ) := by rw [hqi]
      exact hiEq.le
    · have hjNonneg : (0 : ℤ) ≤ ((q j : ℕ) : ℤ) := by omega
      exact (hw i j hji).trans hjNonneg
  have htight :
      ∀ i : ι, ∃ x : X,
        slack i x = ((q i : ℕ) : ℤ) + 1 ∧
          ∀ j : ι, j ≠ i → slack j x ≤ ((q j : ℕ) : ℤ) := by
    intro i
    have hsuccBound : (q i : ℕ) + 1 < cap i + 1 := by
      exact Nat.add_lt_add_right (hq_lt_cap i) 1
    let qUp : Relaxation :=
      Function.update q i ⟨(q i : ℕ) + 1, hsuccBound⟩
    have hqUpNotInfeasible : ¬ relaxationInfeasible qUp := by
      intro hqUpInfeasible
      have hqUpMem : qUp ∈ boundedInfeasible := by
        simp [boundedInfeasible, hqUpInfeasible]
      have hsumLe := hqMax qUp hqUpMem
      have hsumLt :
          (∑ j : ι, (q j : ℕ)) < ∑ j : ι, (qUp j : ℕ) := by
        refine Finset.sum_lt_sum ?_ ?_
        · intro j hj
          by_cases hji : j = i
          · subst hji
            simp [qUp]
          · simp [qUp, hji]
        · refine ⟨i, Finset.mem_univ i, ?_⟩
          simp [qUp]
      exact (not_lt_of_ge hsumLe) hsumLt
    have hqUpFeasible :
        ∃ x : X, ∀ j : ι, slack j x ≤ ((qUp j : ℕ) : ℤ) := by
      by_contra hnot
      exact hqUpNotInfeasible hnot
    rcases hqUpFeasible with ⟨x, hx⟩
    have hiUpper : slack i x ≤ ((q i : ℕ) : ℤ) + 1 := by
      simpa [qUp] using hx i
    have hiNotLower : ¬ slack i x ≤ ((q i : ℕ) : ℤ) := by
      intro hiLower
      apply hqInfeasible
      refine ⟨x, ?_⟩
      intro j
      by_cases hji : j = i
      · subst hji
        exact hiLower
      · simpa [qUp, hji] using hx j
    refine ⟨x, ?_, ?_⟩
    · omega
    · intro j hji
      simpa [qUp, hji] using hx j
  refine ⟨fun i ↦ (q i : ℕ), ?_, ?_⟩
  · simpa [relaxationInfeasible] using hqInfeasible
  · exact htight

/-- Helper for Exercise 6.15: denominator-cleared row slack commutes with the same-parity
midpoint operation by taking arithmetic averages. -/
lemma sameParityMidpointRowScaledSlack_eq_average
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    (((rowScaledSlack A b i (sameParityMidpoint x y) : ℤ) : ℚ)) =
      ((((rowScaledSlack A b i x : ℤ) : ℚ)) + (((rowScaledSlack A b i y : ℤ) : ℚ))) / 2 := by
  -- Rewrite every cleared slack as the common denominator times a rational row slack, then use
  -- the midpoint row-average formula.
  rw [rowScaledSlack_cast_eq, rowScaledSlack_cast_eq, rowScaledSlack_cast_eq]
  rw [sameParityMidpointRowEqAverage A x y hparity i]
  ring

/-- Helper for Exercise 6.15: the midpoint of two distinct tight relaxation witnesses satisfies
every row at the original relaxation level when the witnesses have the same parity. -/
lemma sameParityMidpointRowScaledSlack_le_of_tightWitnesses
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (q : Fin m → ℕ)
    {i j : Fin m}
    (hij : i ≠ j)
    (x y : Fin n → ℤ)
    (hxTight : rowScaledSlack A b i x = (q i : ℤ) + 1)
    (hxBound : ∀ r : Fin m, r ≠ i → rowScaledSlack A b r x ≤ (q r : ℤ))
    (hyTight : rowScaledSlack A b j y = (q j : ℤ) + 1)
    (hyBound : ∀ r : Fin m, r ≠ j → rowScaledSlack A b r y ≤ (q r : ℤ))
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    ∀ r : Fin m, rowScaledSlack A b r (sameParityMidpoint x y) ≤ (q r : ℤ) := by
  intro r
  have haverage := sameParityMidpointRowScaledSlack_eq_average A b r x y hparity
  have hdoubleQ :
      (2 : ℚ) * (((rowScaledSlack A b r (sameParityMidpoint x y) : ℤ) : ℚ)) =
        (((rowScaledSlack A b r x : ℤ) : ℚ)) +
          (((rowScaledSlack A b r y : ℤ) : ℚ)) := by
    -- Clear the factor `2` in the rowwise midpoint identity before returning to integers.
    linarith
  have hdouble :
      2 * rowScaledSlack A b r (sameParityMidpoint x y) =
        rowScaledSlack A b r x + rowScaledSlack A b r y := by
    exact_mod_cast hdoubleQ
  by_cases hri : r = i
  · subst r
    have hyAtI : rowScaledSlack A b i y ≤ (q i : ℤ) := hyBound i hij
    -- At an owned row the average is at most `q_i + 1/2`, hence its integral value is at most
    -- `q_i`.
    omega
  · by_cases hrj : r = j
    · subst r
      have hxAtJ : rowScaledSlack A b j x ≤ (q j : ℤ) := hxBound j hij.symm
      omega
    · have hxAtR : rowScaledSlack A b r x ≤ (q r : ℤ) := hxBound r hri
      have hyAtR : rowScaledSlack A b r y ≤ (q r : ℤ) := hyBound r hrj
      -- Away from the two owned rows both endpoint slacks are already bounded by `q_r`.
      omega

/-- Helper for Exercise 6.15: tight witnesses for an infeasible integer relaxation have pairwise
distinct coordinatewise parity signatures. -/
lemma tightRelaxationWitnessParity_injective
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (q : Fin m → ℕ)
    (hinfeasible : ¬ ∃ x : Fin n → ℤ,
      ∀ r : Fin m, rowScaledSlack A b r x ≤ (q r : ℤ))
    (w : Fin m → (Fin n → ℤ))
    (hw : ∀ i : Fin m,
      rowScaledSlack A b i (w i) = (q i : ℤ) + 1 ∧
        ∀ r : Fin m, r ≠ i → rowScaledSlack A b r (w i) ≤ (q r : ℤ)) :
    Function.Injective (fun i : Fin m ↦ paritySignature (w i)) := by
  intro i j hparity
  by_contra hij
  apply hinfeasible
  refine ⟨sameParityMidpoint (w i) (w j), ?_⟩
  -- Equal parity would make the integral midpoint feasible for the supposedly infeasible
  -- relaxation, using the one-unit tightness at the two owned rows.
  exact sameParityMidpointRowScaledSlack_le_of_tightWitnesses A b q hij (w i) (w j)
    (hw i).1 (hw i).2 (hw j).1 (hw j).2 (fun k ↦ congrFun hparity k)

/-- Helper for Exercise 6.15: if the left endpoint strictly violates row `i`, the right endpoint
satisfies it, and the same-parity midpoint still violates row `i`, then the midpoint has strictly
smaller natural row violation on row `i`. -/
lemma sameParityMidpointRowViolation_lt_of_leftViolation_rightSatisfaction
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hleft : b i < (A *ᵥ fun k ↦ (x k : ℚ)) i)
    (hright : (A *ᵥ fun k ↦ (y k : ℚ)) i ≤ b i)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2))
    (hmid : b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i) :
    rowViolationNat A b i (sameParityMidpoint x y) < rowViolationNat A b i x := by
  -- Transport the midpoint row identity to cleared slacks, then compare the positive integer
  -- slacks through their rational casts before returning to `ℕ`.
  have hxSlackPos : 0 < rowScaledSlack A b i x :=
    (rowScaledSlack_pos_iff_rowViolation A b i x).2 hleft
  have hySlackNonpos : rowScaledSlack A b i y ≤ 0 :=
    rowScaledSlack_nonpos_of_rowSatisfied A b i y hright
  have hmidSlackPos : 0 < rowScaledSlack A b i (sameParityMidpoint x y) :=
    (rowScaledSlack_pos_iff_rowViolation A b i (sameParityMidpoint x y)).2 hmid
  have hxSlackQPos : (0 : ℚ) < (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
    exact_mod_cast hxSlackPos
  have hySlackQNonpos : (((rowScaledSlack A b i y : ℤ) : ℚ)) ≤ 0 := by
    exact_mod_cast hySlackNonpos
  have hmidAverage :=
    sameParityMidpointRowScaledSlack_eq_average A b i x y hparity
  have hmidSlackQLt : (((rowScaledSlack A b i (sameParityMidpoint x y) : ℤ) : ℚ)) <
      (((rowScaledSlack A b i x : ℤ) : ℚ)) := by
    rw [hmidAverage]
    linarith
  have hmidSlackLt : rowScaledSlack A b i (sameParityMidpoint x y) < rowScaledSlack A b i x := by
    exact_mod_cast hmidSlackQLt
  have hmidCast :
      (((rowViolationNat A b i (sameParityMidpoint x y) : ℕ) : ℤ)) =
        rowScaledSlack A b i (sameParityMidpoint x y) := by
    -- Positive midpoint slack keeps the `toNat` cast transparent.
    unfold rowViolationNat
    simp [Int.toNat_of_nonneg hmidSlackPos.le]
  have hxCast : (((rowViolationNat A b i x : ℕ) : ℤ)) = rowScaledSlack A b i x := by
    -- The left endpoint also has positive slack, so its `toNat` cast is transparent as well.
    unfold rowViolationNat
    simp [Int.toNat_of_nonneg hxSlackPos.le]
  have hnatCastLt :
      (((rowViolationNat A b i (sameParityMidpoint x y) : ℕ) : ℤ)) <
        (((rowViolationNat A b i x : ℕ) : ℤ)) := by
    simpa [hmidCast, hxCast] using hmidSlackLt
  exact_mod_cast hnatCastLt

/-- Helper for Exercise 6.15: if a same-parity donor satisfies row `i` and every earlier row,
then a midpoint that still violates row `i` is a strictly better prefix competitor for `i`. -/
lemma sameParityMidpointImprovesPrefixCompetitor_withDonor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hx : prefixCompetitor A b i x)
    (hyBefore : ∀ s : Fin m, s < i → (A *ᵥ fun k ↦ (y k : ℚ)) s ≤ b s)
    (hyi : (A *ᵥ fun k ↦ (y k : ℚ)) i ≤ b i)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2))
    (hmid : b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i) :
    prefixCompetitor A b i (sameParityMidpoint x y) ∧
      rowViolationNat A b i (sameParityMidpoint x y) < rowViolationNat A b i x := by
  rcases hx with ⟨hxBefore, hxi⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, hmid⟩
    intro s hs
    -- Both endpoints satisfy every row before `i`, so the midpoint keeps that prefix feasible.
    rw [sameParityMidpointRowEqAverage A x y hparity s]
    have hxS : (A *ᵥ fun k ↦ (x k : ℚ)) s ≤ b s := hxBefore s hs
    have hyS : (A *ᵥ fun k ↦ (y k : ℚ)) s ≤ b s := hyBefore s hs
    linarith
  · -- The donor already satisfies row `i`, so the midpoint strictly improves the owned-row slack.
    exact sameParityMidpointRowViolation_lt_of_leftViolation_rightSatisfaction
      A b i x y hxi hyi hparity hmid

/-- Helper for Exercise 6.15: a prefix-minimal witness cannot keep its owned row violated after
averaging with a same-parity donor that already satisfies the whole owned prefix. -/
lemma ownedBranchImpossible_ofPrefixMinimal_withDonor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (x y : Fin n → ℤ)
    (hx : prefixCompetitor A b i x)
    (hxmin :
      ∀ z : Fin n → ℤ,
        prefixCompetitor A b i z →
          rowViolationNat A b i x ≤ rowViolationNat A b i z)
    (hyBefore : ∀ s : Fin m, s < i → (A *ᵥ fun k ↦ (y k : ℚ)) s ≤ b s)
    (hyi : (A *ᵥ fun k ↦ (y k : ℚ)) i ≤ b i)
    (hparity : ∀ k : Fin n, (x k : ZMod 2) = (y k : ZMod 2)) :
    (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i ≤ b i := by
  by_contra hviol
  have hmid : b i < (A *ᵥ fun k ↦ (sameParityMidpoint x y k : ℚ)) i := lt_of_not_ge hviol
  rcases sameParityMidpointImprovesPrefixCompetitor_withDonor
      A b i x y hx hyBefore hyi hparity hmid with ⟨hmidPrefix, hbetter⟩
  -- Prefix minimality forbids a same-parity midpoint from strictly lowering the owned-row
  -- violation while remaining a prefix competitor.
  have hminimal :
      rowViolationNat A b i x ≤ rowViolationNat A b i (sameParityMidpoint x y) :=
    hxmin _ hmidPrefix
  exact Nat.not_lt_of_ge hminimal hbetter

/-- Helper for Exercise 6.15: every deleted-feasible witness is automatically a prefix competitor
for its omitted row. -/
lemma deletedFeasible_isPrefixCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {i : Fin m}
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    prefixCompetitor A b i x := by
  -- Deleted-feasibility gives all earlier rows, and infeasibility supplies the strict `i`th
  -- violation.
  refine ⟨?_, deletedIntegralPointStrictlyViolatesOmittedRow A b hinfeasible hx⟩
  intro r hri
  exact hx r (ne_of_lt hri)

/-- Helper for Exercise 6.15: every row already has a prefix competitor minimizing its owned-row
violation objective. -/
lemma existsPrefixMinimalCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (i : Fin m) :
    ∃ x : Fin n → ℤ,
      prefixCompetitor A b i x ∧
        ∀ y : Fin n → ℤ,
          prefixCompetitor A b i y →
            rowViolationNat A b i x ≤ rowViolationNat A b i y := by
  classical
  rcases hdeleted i with ⟨x₀, hx₀⟩
  have hx₀prefix : prefixCompetitor A b i x₀ :=
    deletedFeasible_isPrefixCompetitor A b hinfeasible hx₀
  let competitorAt : ℕ → Prop :=
    fun t ↦ ∃ x : Fin n → ℤ, prefixCompetitor A b i x ∧ rowViolationNat A b i x = t
  have hcompetitorAt : ∃ t : ℕ, competitorAt t := by
    -- A deleted-feasible witness for row `i` is already a prefix competitor, so the `ℕ`-valued
    -- row-violation objective attains some value on this nonempty class.
    refine ⟨rowViolationNat A b i x₀, x₀, hx₀prefix, rfl⟩
  let t₀ : ℕ := Nat.find hcompetitorAt
  have ht₀ : competitorAt t₀ := Nat.find_spec hcompetitorAt
  rcases ht₀ with ⟨x, hxPrefix, hxt₀⟩
  refine ⟨x, hxPrefix, ?_⟩
  intro y hy
  have hyCompetitor : competitorAt (rowViolationNat A b i y) := by
    exact ⟨y, hy, rfl⟩
  have hmin : t₀ ≤ rowViolationNat A b i y := Nat.find_min' hcompetitorAt hyCompetitor
  -- Rewriting the chosen witness objective through the minimizing value closes the comparison.
  calc
    rowViolationNat A b i x = t₀ := hxt₀
    _ ≤ rowViolationNat A b i y := hmin

/-- Helper for Exercise 6.15: with a fixed exempt row `k`, a witness for row `i` is admissible
when it satisfies every row except possibly `i` and `k`. -/
abbrev exemptRowFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  ∀ r : Fin m, r ≠ i → r ≠ k → (A *ᵥ fun j ↦ (x j : ℚ)) r ≤ b r

/-- Helper for Exercise 6.15: a fixed-exempt-row competitor is an admissible witness that still
strictly violates its owned row. -/
abbrev exemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    (x : Fin n → ℤ) : Prop :=
  exemptRowFeasible A b k i x ∧ b i < (A *ᵥ fun j ↦ (x j : ℚ)) i

/-- Helper for Exercise 6.15: every deleted-feasible witness is automatically admissible in every
fixed-exempt-row universe. -/
lemma deletedFeasible_toExemptRowFeasible
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    exemptRowFeasible A b k i x := by
  intro r hri _
  -- Forgetting one additional exempt row only weakens the deleted-feasibility requirements.
  exact hx r hri

/-- Helper for Exercise 6.15: every deleted-feasible witness is a fixed-exempt-row competitor for
its own row because infeasibility forces the omitted row to be strictly violated. -/
lemma deletedFeasible_toExemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (k i : Fin m)
    {x : Fin n → ℤ}
    (hx : deletedFeasible A b i x) :
    exemptRowCompetitor A b k i x := by
  refine ⟨deletedFeasible_toExemptRowFeasible A b k i hx, ?_⟩
  -- The owned row stays strictly violated for every deleted-feasible witness.
  exact deletedIntegralPointStrictlyViolatesOmittedRow A b hinfeasible hx

/-- Helper for Exercise 6.15: once a prefix competitor satisfies every intermediate row before the
maximal reserve row `k`, it is already admissible in the common reserve-row universe. -/
lemma prefixCompetitor_toExemptRowCompetitor_of_betweenRows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {i k : Fin m}
    (hik : i < k)
    (hkmax : ∀ r : Fin m, r ≤ k)
    {x : Fin n → ℤ}
    (hx : prefixCompetitor A b i x)
    (hbetween :
      ∀ r : Fin m, i < r → r < k → (A *ᵥ fun j ↦ (x j : ℚ)) r ≤ b r) :
    exemptRowCompetitor A b k i x := by
  rcases hx with ⟨hprefix, hviol⟩
  refine ⟨?_, hviol⟩
  intro r hri hrk
  have hrle : r ≤ k := hkmax r
  rcases lt_or_eq_of_le hrle with hrlt | rfl
  · rcases lt_or_gt_of_ne hri with hlt | hgt
    · -- Rows before `i` are already controlled by the prefix-competitor hypothesis.
      exact hprefix r hlt
    · -- Rows strictly between `i` and the reserve row are controlled by the extra hypothesis.
      exact hbetween r hgt hrlt
  · exact False.elim (hrk rfl)

/-- Helper for Exercise 6.15: a prefix competitor below the maximal reserve row either is already
reserve-admissible, or it has a first intermediate violated row before `k`. -/
lemma firstBadIntermediateRow_of_prefixCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {i k : Fin m}
    (hik : i < k)
    (hkmax : ∀ r : Fin m, r ≤ k)
    {x : Fin n → ℤ}
    (hx : prefixCompetitor A b i x) :
    exemptRowCompetitor A b k i x ∨
      ∃ r : Fin m,
        i < r ∧
          r < k ∧
          b r < (A *ᵥ fun j ↦ (x j : ℚ)) r ∧
          ∀ s : Fin m, i < s → s < r → (A *ᵥ fun j ↦ (x j : ℚ)) s ≤ b s := by
  classical
  by_cases hreserve : exemptRowCompetitor A b k i x
  · exact Or.inl hreserve
  · right
    rcases hx with ⟨hprefix, hviolI⟩
    have hnotFeasible : ¬ exemptRowFeasible A b k i x := by
      intro hfeasible
      exact hreserve ⟨hfeasible, hviolI⟩
    unfold exemptRowFeasible at hnotFeasible
    push Not at hnotFeasible
    rcases hnotFeasible with ⟨r, hri, hrk, hviolr⟩
    have hir : i < r := by
      rcases lt_or_gt_of_ne hri with hrlt | hilt
      · -- A bad row cannot lie below `i`, because prefix competitors satisfy every earlier row.
        have hsat : (A *ᵥ fun j ↦ (x j : ℚ)) r ≤ b r := hprefix r hrlt
        exact False.elim ((not_le_of_gt hviolr) hsat)
      · exact hilt
    have hrlt : r < k := lt_of_le_of_ne (hkmax r) hrk
    let badIndex : ℕ → Prop :=
      fun t ↦
        ∃ q : Fin m,
          i < q ∧
            q < k ∧
            b q < (A *ᵥ fun j ↦ (x j : ℚ)) q ∧
            q.1 = t
    have hbadIndex : ∃ t : ℕ, badIndex t := by
      exact ⟨r.1, r, hir, hrlt, hviolr, rfl⟩
    let t₀ : ℕ := Nat.find hbadIndex
    have ht₀ : badIndex t₀ := Nat.find_spec hbadIndex
    rcases ht₀ with ⟨r₀, hir₀, hr₀k, hviol₀, hr₀eq⟩
    refine ⟨r₀, hir₀, hr₀k, hviol₀, ?_⟩
    intro s his hsr
    by_contra hsat
    have hsviol : b s < (A *ᵥ fun j ↦ (x j : ℚ)) s := lt_of_not_ge hsat
    have hsIndex : badIndex s.1 := by
      refine ⟨s, his, lt_trans hsr hr₀k, hsviol, rfl⟩
    have hmin : t₀ ≤ s.1 := Nat.find_min' hbadIndex hsIndex
    have hslt : s.1 < t₀ := by
      calc
        s.1 < r₀.1 := hsr
        _ = t₀ := hr₀eq
    exact False.elim (Nat.not_lt_of_ge hmin hslt)

/-- Helper for Exercise 6.15: each deleted row already has a witness in every fixed-exempt-row
universe. -/
lemma existsExemptRowCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (k i : Fin m) :
    ∃ x : Fin n → ℤ, exemptRowCompetitor A b k i x := by
  rcases hdeleted i with ⟨x, hx⟩
  -- Reuse the deleted-feasible witness inside the weaker fixed-exempt-row admissible family.
  exact ⟨x, deletedFeasible_toExemptRowCompetitor A b hinfeasible k i hx⟩

/-- Helper for Exercise 6.15: every fixed-exempt-row universe contains a competitor minimizing the
owned-row violation objective. -/
lemma existsExemptRowMinimalCompetitor
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (k i : Fin m) :
    ∃ x : Fin n → ℤ,
      exemptRowCompetitor A b k i x ∧
        ∀ y : Fin n → ℤ,
          exemptRowCompetitor A b k i y →
            rowViolationNat A b i x ≤ rowViolationNat A b i y := by
  classical
  rcases existsExemptRowCompetitor A b hinfeasible hdeleted k i with ⟨x₀, hx₀⟩
  let competitorAt : ℕ → Prop :=
    fun t ↦ ∃ x : Fin n → ℤ, exemptRowCompetitor A b k i x ∧ rowViolationNat A b i x = t
  have hcompetitorAt : ∃ t : ℕ, competitorAt t := by
    -- The fixed-exempt-row universe is nonempty, so the `ℕ`-valued objective has a minimum.
    refine ⟨rowViolationNat A b i x₀, x₀, hx₀, rfl⟩
  let t₀ : ℕ := Nat.find hcompetitorAt
  have ht₀ : competitorAt t₀ := Nat.find_spec hcompetitorAt
  rcases ht₀ with ⟨x, hx, hxt₀⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hyCompetitor : competitorAt (rowViolationNat A b i y) := by
    exact ⟨y, hy, rfl⟩
  have hmin : t₀ ≤ rowViolationNat A b i y := Nat.find_min' hcompetitorAt hyCompetitor
  -- Rewriting the chosen witness objective through the minimizing value finishes the comparison.
  calc
    rowViolationNat A b i x = t₀ := hxt₀
    _ ≤ rowViolationNat A b i y := hmin

/-- Helper for Exercise 6.15: the finite set of parity signatures realized by fixed-exempt-row
competitors minimizing the owned-row violation objective. -/
noncomputable def exemptRowMinimalParitySet
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m) : Finset (Fin n → ZMod 2) :=
  letI : DecidablePred
      (fun p : Fin n → ZMod 2 ↦
        ∃ x : Fin n → ℤ,
          exemptRowCompetitor A b k i x ∧
            (∀ y : Fin n → ℤ,
              exemptRowCompetitor A b k i y →
                rowViolationNat A b i x ≤ rowViolationNat A b i y) ∧
            paritySignature x = p) :=
    Classical.decPred _
  Finset.univ.filter
    (fun p ↦
      ∃ x : Fin n → ℤ,
        exemptRowCompetitor A b k i x ∧
          (∀ y : Fin n → ℤ,
            exemptRowCompetitor A b k i y →
              rowViolationNat A b i x ≤ rowViolationNat A b i y) ∧
          paritySignature x = p)

/-- Helper for Exercise 6.15: membership in the fixed-exempt-row minimal parity set is exactly
realization by a minimizing fixed-exempt-row competitor. -/
lemma mem_exemptRowMinimalParitySet_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k i : Fin m)
    {p : Fin n → ZMod 2} :
    p ∈ exemptRowMinimalParitySet A b k i ↔
      ∃ x : Fin n → ℤ,
        exemptRowCompetitor A b k i x ∧
          (∀ y : Fin n → ℤ,
            exemptRowCompetitor A b k i y →
              rowViolationNat A b i x ≤ rowViolationNat A b i y) ∧
          paritySignature x = p := by
  classical
  -- Unfold the filtered finite parity universe once and read off the realizing minimizing witness.
  simp [exemptRowMinimalParitySet]

/-- Helper for Exercise 6.15: every fixed-exempt-row minimal parity set is nonempty. -/
lemma exemptRowMinimalParitySet_nonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (k i : Fin m) :
    (exemptRowMinimalParitySet A b k i).Nonempty := by
  rcases existsExemptRowMinimalCompetitor A b hinfeasible hdeleted k i with ⟨x, hx, hmin⟩
  -- The parity of a minimizing competitor is realized in the filtered finite parity universe.
  refine ⟨paritySignature x, ?_⟩
  exact (mem_exemptRowMinimalParitySet_iff A b k i).2 ⟨x, hx, hmin, rfl⟩

/-- Helper for Exercise 6.15: in a fixed-exempt-row universe, the midpoint of two same-parity
witnesses satisfies every row omitted by neither endpoint and by the exempt row. -/
lemma sameParityMidpointSatisfiesExemptRows
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    {k i j r : Fin m}
    (hri : r ≠ i)
    (hrj : r ≠ j)
    (hrk : r ≠ k)
    (x y : Fin n → ℤ)
    (hx : exemptRowFeasible A b k i x)
    (hy : exemptRowFeasible A b k j y)
    (hparity : ∀ t : Fin n, (x t : ZMod 2) = (y t : ZMod 2)) :
    (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r ≤ b r := by
  have hxRow : (A *ᵥ fun t ↦ (x t : ℚ)) r ≤ b r := hx r hri hrk
  have hyRow : (A *ᵥ fun t ↦ (y t : ℚ)) r ≤ b r := hy r hrj hrk
  -- The fixed exempt row stays outside the averaging step, so the original midpoint argument
  -- still proves every genuinely nonendpoint row.
  rw [sameParityMidpointRowEqAverage A x y hparity r]
  linarith

/-- Helper for Exercise 6.15: in a common fixed-exempt-row universe, a same-parity midpoint can
only violate one of the two owned rows or the common exempt row. -/
lemma sameParityMidpointViolatesOwnedOrExemptRow
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    {k i j : Fin m}
    (x y : Fin n → ℤ)
    (hx : exemptRowCompetitor A b k i x)
    (hy : exemptRowCompetitor A b k j y)
    (hparity : ∀ t : Fin n, (x t : ZMod 2) = (y t : ZMod 2)) :
    b i < (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) i ∨
      b j < (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) j ∨
      b k < (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) k := by
  rcases hx with ⟨hxFeasible, _hxViolates⟩
  rcases hy with ⟨hyFeasible, _hyViolates⟩
  -- If the midpoint satisfied the two owned rows and the common exempt row, it would satisfy every
  -- row of the original system and contradict infeasibility.
  by_contra hmid
  push Not at hmid
  apply hinfeasible
  refine ⟨fun t ↦ (sameParityMidpoint x y t : ℝ), ?_⟩
  rw [mem_mixed_integer_feasible_set_iff]
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hri : r = i
    · subst hri
      have hrow : (((A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
        exact_mod_cast hmid.1
      simpa [Matrix.mulVec, dotProduct] using hrow
    · by_cases hrj : r = j
      · subst hrj
        have hrow : (((A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
          exact_mod_cast hmid.2.1
        simpa [Matrix.mulVec, dotProduct] using hrow
      · by_cases hrk : r = k
        · subst hrk
          have hrow : (((A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
            exact_mod_cast hmid.2.2
          simpa [Matrix.mulVec, dotProduct] using hrow
        · have hrowMid :
            (A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r ≤ b r :=
              sameParityMidpointSatisfiesExemptRows A b hri hrj hrk x y hxFeasible hyFeasible
                hparity
          have hrow :
              (((A *ᵥ fun t ↦ (sameParityMidpoint x y t : ℚ)) r : ℚ) : ℝ) ≤ (b r : ℝ) := by
            exact_mod_cast hrowMid
          simpa [Matrix.mulVec, dotProduct] using hrow
  · intro r hr
    exact ⟨sameParityMidpoint x y r, rfl⟩

/-- Helper for Exercise 6.15: fix one reserve row `k` and package the reserve parity set together
with the nonreserve minimal fixed-exempt-row parity sets into one family. -/
noncomputable def starParityFamily
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (k : Fin m) : Fin m → Finset (Fin n → ZMod 2) :=
  fun i ↦ if i = k then deletedFeasibleParitySet A b k else exemptRowMinimalParitySet A b k i

/-- Helper for Exercise 6.15: every member of the reserve-row star family is nonempty. -/
lemma starParityFamily_nonempty
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hdeleted : ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x)
    (k i : Fin m) :
    (starParityFamily A b k i).Nonempty := by
  by_cases hik : i = k
  · -- The reserve row uses the deleted-feasible parity family.
    simpa [starParityFamily, hik] using deletedFeasibleParitySet_nonempty A b hdeleted k
  · -- Every nonreserve row uses the already nonempty minimizing fixed-exempt-row family.
    simp [starParityFamily, hik, exemptRowMinimalParitySet_nonempty A b hinfeasible hdeleted k i]

/-- Helper for Exercise 6.15: a minimal Hall counterexample cannot contain a parity that belongs
to only one row of the bad subset. -/
lemma minimalBadSubset_noUniqueParity
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]
    (t : α → Finset β)
    {S : Finset α}
    (hSbad : (S.biUnion t).card < S.card)
    (hSmin : ∀ T : Finset α, (T.biUnion t).card < T.card → S.card ≤ T.card)
    {i : α}
    (hiS : i ∈ S)
    {p : β}
    (hp : p ∈ t i) :
    ∃ j, j ∈ S ∧ j ≠ i ∧ p ∈ t j := by
  by_contra hNoCollision
  push Not at hNoCollision
  have hpUnion : p ∈ S.biUnion t := Finset.mem_biUnion.mpr ⟨i, hiS, hp⟩
  have hsubset :
      (S.erase i).biUnion t ⊆ (S.biUnion t).erase p := by
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨j, hjErase, hqj⟩
    have hjS : j ∈ S := Finset.mem_of_mem_erase hjErase
    have hji : j ≠ i := Finset.ne_of_mem_erase hjErase
    refine Finset.mem_erase.mpr ?_
    refine ⟨?_, Finset.mem_biUnion.mpr ⟨j, hjS, hqj⟩⟩
    intro hqp
    subst hqp
    exact hNoCollision j hjS hji hqj
  have hEraseBad : ((S.erase i).biUnion t).card < (S.erase i).card := by
    have hcardLe :
        ((S.erase i).biUnion t).card ≤ ((S.biUnion t).erase p).card :=
      Finset.card_le_card hsubset
    have hcardUnionErase :
        ((S.biUnion t).erase p).card = (S.biUnion t).card - 1 := by
      simpa using Finset.card_erase_of_mem hpUnion
    have hcardErase :
        (S.erase i).card = S.card - 1 := by
      simpa using Finset.card_erase_of_mem hiS
    have hUnionPos : 0 < (S.biUnion t).card := Finset.card_pos.mpr ⟨p, hpUnion⟩
    -- Removing the unique parity owner drops both the row count and the union count by one.
    omega
  have hminimalErase : S.card ≤ (S.erase i).card := hSmin (S.erase i) hEraseBad
  have hcardErase :
      (S.erase i).card = S.card - 1 := by
    simpa using Finset.card_erase_of_mem hiS
  omega

/-- Helper for Exercise 6.15: Hall's condition on a finite parity family chooses pairwise
distinct parities, one from each row-indexed set. -/
lemma existsInjectiveParityChoice_ofHall
    (t : Fin m → Finset (Fin n → ZMod 2))
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion t).card) :
    ∃ σ : Fin m → (Fin n → ZMod 2),
      Function.Injective σ ∧ ∀ i : Fin m, σ i ∈ t i := by
  classical
  -- Apply finite Hall directly to the row-indexed family of parity sets.
  simpa using (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall

/-- Helper for Exercise 6.15: an injective row-indexed choice of parity signatures yields the
cardinality bound `m ≤ 2^n`. -/
lemma rowCount_le_twoPow_of_injectiveParityChoice
    (σ : Fin m → (Fin n → ZMod 2))
    (hσinj : Function.Injective σ) :
    m ≤ 2 ^ n := by
  -- Compare the finite row type against the finite parity codomain by injectivity.
  calc
    m = Fintype.card (Fin m) := by simp
    _ ≤ Fintype.card (Fin n → ZMod 2) := Fintype.card_le_of_injective σ hσinj
    _ = 2 ^ n := by
          simpa using (Fintype.card_fun (α := Fin n) (β := ZMod 2))

/-- Helper for Exercise 6.15: once a row-indexed parity family satisfies Hall's condition, the
row count is bounded by the number of parity signatures. -/
lemma rowCount_le_twoPow_of_hallParityFamily
    (t : Fin m → Finset (Fin n → ZMod 2))
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion t).card) :
    m ≤ 2 ^ n := by
  classical
  rcases existsInjectiveParityChoice_ofHall (m := m) (n := n) t hHall with ⟨σ, hσinj, _hσmem⟩
  -- The Hall-selected injective parity choice immediately yields the numerical bound.
  exact rowCount_le_twoPow_of_injectiveParityChoice (m := m) (n := n) σ hσinj

/-- Helper for Exercise 6.15: Hall's theorem chooses pairwise distinct deleted-feasible parity
signatures, one for each row. -/
lemma existsInjectiveDeletedFeasibleParityChoice
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion (deletedFeasibleParitySet A b)).card) :
    ∃ σ : Fin m → (Fin n → ZMod 2),
      Function.Injective σ ∧ ∀ i : Fin m, σ i ∈ deletedFeasibleParitySet A b i := by
  classical
  -- Apply Hall directly to the row-indexed family of realized parity-signature sets.
  simpa using
    (Finset.all_card_le_biUnion_card_iff_exists_injective (deletedFeasibleParitySet A b)).1 hHall

/-- Helper for Exercise 6.15: an injective parity choice can be lifted back to actual
deleted-feasible integral witnesses. -/
lemma existsInjectiveDeletedFeasibleWitnessFamily
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hHall :
      ∀ S : Finset (Fin m),
        S.card ≤ (S.biUnion (deletedFeasibleParitySet A b)).card) :
    ∃ w : Fin m → (Fin n → ℤ),
      (∀ i : Fin m, deletedFeasible A b i (w i)) ∧
        Function.Injective (fun i : Fin m ↦ paritySignature (w i)) := by
  classical
  rcases existsInjectiveDeletedFeasibleParityChoice A b hHall with ⟨σ, hσinj, hσmem⟩
  have hwitness :
      ∀ i : Fin m, ∃ x : Fin n → ℤ, deletedFeasible A b i x ∧ paritySignature x = σ i := by
    intro i
    exact (mem_deletedFeasibleParitySet_iff A b i).1 (hσmem i)
  choose w hwDeleted hwParity using hwitness
  refine ⟨w, hwDeleted, ?_⟩
  intro i j hij
  -- Rewriting the chosen witness parities through the Hall-selected family restores injectivity.
  apply hσinj
  calc
    σ i = paritySignature (w i) := (hwParity i).symm
    _ = paritySignature (w j) := hij
    _ = σ j := hwParity j

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_15.lean

Exercise 6.15. Let `A ∈ ℚ^(m × n)` and `b ∈ ℚ^m` be such that the system `A x ≤ b` has no
integral solution, but deleting any one of the `m` inequalities yields a system with an integral
solution. Then `m ≤ 2^n`. -/
theorem minimal_integral_infeasible_rational_system_row_bound
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hinfeasible :
      ¬ (mixed_integer_feasible_set
          (A.map (Rat.castHom ℝ))
          (fun i : Fin m ↦ (b i : ℝ))
          Finset.univ).Nonempty)
    (hminimal :
      ∀ i : Fin m,
        ∃ x : Fin n → ℤ,
          ∀ j : Fin m, j ≠ i → (A *ᵥ fun k ↦ (x k : ℚ)) j ≤ b j) :
    m ≤ 2 ^ n := by
  classical
  -- Route correction: the previous route tried to prove a global Hall statement for
  -- `deletedFeasibleParitySet A b`, but that statement is false already for the one-dimensional
  -- system `x ≤ 0`, `x ≥ 2`. We instead maximize a bounded integral relaxation and use its tight
  -- witnesses, whose one-unit gaps are exactly what midpoint rounding needs.
  have hslackInfeasible :
      ¬ ∃ x : Fin n → ℤ,
        ∀ i : Fin m, rowScaledSlack A b i x ≤ 0 := by
    intro hfeasible
    rcases hfeasible with ⟨x, hx⟩
    apply hinfeasible
    refine ⟨fun k ↦ (x k : ℝ), ?_⟩
    rw [mem_mixed_integer_feasible_set_iff]
    refine ⟨?_, ?_⟩
    · intro i
      have hrowQ : (A *ᵥ fun k ↦ (x k : ℚ)) i ≤ b i :=
        (rowScaledSlack_nonpos_iff_rowSatisfied A b i x).1 (hx i)
      have hrowR :
          (((A *ᵥ fun k ↦ (x k : ℚ)) i : ℚ) : ℝ) ≤ (b i : ℝ) := by
        exact_mod_cast hrowQ
      simpa [Matrix.mulVec, dotProduct] using hrowR
    · intro k hk
      exact ⟨x k, rfl⟩
  have hslackDeleted :
      ∀ i : Fin m, ∃ x : Fin n → ℤ,
        ∀ j : Fin m, j ≠ i → rowScaledSlack A b j x ≤ 0 := by
    intro i
    rcases hminimal i with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro j hji
    -- Translate every retained rational inequality into its nonpositive integral slack form.
    exact rowScaledSlack_nonpos_of_rowSatisfied A b j x (hx j hji)
  obtain ⟨q, hqInfeasible, htight⟩ :=
    existsMaximalInfeasibleRelaxationWithTightWitnesses
      (fun i x ↦ rowScaledSlack A b i x) hslackInfeasible hslackDeleted
  choose w hwTight hwBound using htight
  have hwSpec :
      ∀ i : Fin m,
        rowScaledSlack A b i (w i) = (q i : ℤ) + 1 ∧
          ∀ r : Fin m, r ≠ i → rowScaledSlack A b r (w i) ≤ (q r : ℤ) := by
    intro i
    exact ⟨hwTight i, hwBound i⟩
  have hparityInjective :
      Function.Injective (fun i : Fin m ↦ paritySignature (w i)) :=
    tightRelaxationWitnessParity_injective A b q hqInfeasible w hwSpec
  -- Inject the rows into the `2^n` coordinatewise parity signatures.
  exact rowCount_le_twoPow_of_injectiveParityChoice
    (fun i : Fin m ↦ paritySignature (w i)) hparityInjective

end Exercise615

#print axioms minimal_integral_infeasible_rational_system_row_bound
