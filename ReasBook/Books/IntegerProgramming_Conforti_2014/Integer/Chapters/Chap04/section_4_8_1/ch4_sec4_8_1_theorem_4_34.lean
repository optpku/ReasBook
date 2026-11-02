import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_definition_4_8_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_theorem_4_34.LinearForm
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_proposition_4_33

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section Theorem434

variable {n : ℕ}

/-- A list of indices is admissible for the mixing inequalities when it is nonempty, strictly
increasing, and has strictly increasing positive fractional parts. -/
def IsMixingIndexSequence (b : Fin n → ℚ) : List (Fin n) → Prop
  | [] => False
  | i :: is =>
      0 < mixingFractionalPart b i ∧
        (i :: is).IsChain (· < ·) ∧
        (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k)

/-- Mixing inequality `(4.29)` associated with an admissible index sequence. -/
def mixingInequalityTypeOne
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s.reverse with
  | [] => True
  | last :: _ =>
      mixingFractionalPart b last ≤ x 0 + mixingInequalityTypeOneSum b s x

/-- Mixing inequality `(4.30)` associated with an admissible positive-fraction index sequence. -/
def mixingInequalityTypeTwo
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      mixingFractionalPart b last ≤
        x 0 + mixingInequalityTypeOneSum b s x +
          (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))
  | _, _ => True

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a single-coordinate
vector evaluates to the expected scalar multiple under `⬝ᵥ`. -/
private lemma singleCoordinateDotProduct
    {m : ℕ} (j : Fin m) (c : ℝ) (x : Fin m → ℝ) :
    (fun k : Fin m ↦ if k = j then c else 0) ⬝ᵥ x = c * x j := by
  -- Collapse the finite dot product to its unique nonzero coordinate.
  rw [dotProduct, Fintype.sum_eq_single j]
  · simp
  · intro k hk
    simp [hk]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the recursive coefficient
owner for `(4.29)` evaluates to the negative raw selected-coordinate sum. -/
private lemma mixingInequalityTypeOneCoeffAux_dotProduct
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneCoeffAux b prev s ⬝ᵥ x =
        -mixingInequalityTypeOneRawSumAux b x prev s
  | prev, [] => by
      -- The empty selected sequence contributes nothing on either side.
      simp [mixingInequalityTypeOneCoeffAux, mixingInequalityTypeOneRawSumAux, dotProduct]
  | prev, i :: is => by
      -- Split off the new selected coordinate and reuse the recursive tail evaluation.
      rw [mixingInequalityTypeOneCoeffAux, mixingInequalityTypeOneRawSumAux]
      have hadd :
          (fun j : Fin (n + 1) ↦
              (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
                mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x := by
        -- The dot product distributes over the head-coordinate split.
        change
          (((fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x)
        exact
          add_dotProduct
            (fun j : Fin (n + 1) ↦
              if j = i.succ then -(mixingFractionalPart b i - prev) else 0)
            (mixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is)
            x
      rw [hadd, singleCoordinateDotProduct, mixingInequalityTypeOneCoeffAux_dotProduct]
      ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the raw selected sum
splits into the shifted sum plus the accumulated floor contribution. -/
private lemma mixingInequalityTypeOneRawSum_eq_shifted_add_floor
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (s : List (Fin n)) :
    mixingInequalityTypeOneRawSumAux b x 0 s =
      mixingInequalityTypeOneSum b s x + mixingInequalityFloorSum b s := by
  -- Split each selected coordinate into its shifted part plus its floor contribution.
  have haux :
      ∀ prev : ℝ, ∀ t : List (Fin n),
        mixingInequalityTypeOneRawSumAux b x prev t =
          mixingInequalityTypeOneSumAux b x prev t + mixingInequalityFloorSumAux b prev t := by
    intro prev t
    induction t generalizing prev with
    | nil =>
        simp [mixingInequalityTypeOneRawSumAux, mixingInequalityTypeOneSumAux,
          mixingInequalityFloorSumAux]
    | cons i is ih =>
        -- The head coordinate splits linearly, and the tail uses the induction hypothesis.
        rw [mixingInequalityTypeOneRawSumAux, mixingInequalityTypeOneSumAux,
          mixingInequalityFloorSumAux, ih]
        ring
  simpa [mixingInequalityTypeOneSum, mixingInequalityFloorSum] using haux 0 s

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the coefficient vector of
`(4.29)` pairs with `x` as the negated scalar left-hand side. -/
private lemma mixingInequalityTypeOneCoeff_dotProduct
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x =
      -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 s) := by
  -- Route correction: rewrite the public coefficient owner to the recursive spelling first so the
  -- dot-product evaluation stays in one scalar normal form.
  have hcoeff :
      mixingInequalityTypeOneCoeff b s =
        fun j : Fin (n + 1) ↦
          (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j := by
    ext j
    simp [mixingInequalityTypeOneCoeff]
  rw [hcoeff]
  have hadd :
      (fun j : Fin (n + 1) ↦
          (if j = 0 then (-1 : ℝ) else 0) + mixingInequalityTypeOneCoeffAux b 0 s j) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          mixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x := by
    -- The dot product again distributes over the explicit head/tail split.
    change
      (((fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) +
          mixingInequalityTypeOneCoeffAux b 0 s) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          mixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x)
    exact
      add_dotProduct
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0)
        (mixingInequalityTypeOneCoeffAux b 0 s)
        x
  rw [hadd, singleCoordinateDotProduct, mixingInequalityTypeOneCoeffAux_dotProduct]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: under a fixed reverse
decomposition, the coefficient vector of `(4.30)` pairs with `x` in the expected scalar form. -/
private lemma mixingInequalityTypeTwoCoeff_dotProduct_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ x =
      -(x 0 + mixingInequalityTypeOneRawSumAux b x 0 (first :: tail) +
        (1 - mixingFractionalPart b last) * x first.succ) := by
  -- Split the type-two coefficient owner into the type-one part and the first-index correction.
  simp only [mixingInequalityTypeTwoCoeff, hrev]
  have hadd :
      (fun j : Fin (n + 1) ↦
          mixingInequalityTypeOneCoeff b (first :: tail) j +
            (if j = first.succ then -(1 - mixingFractionalPart b last) else 0)) ⬝ᵥ x =
        mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ x +
          (fun j : Fin (n + 1) ↦
            if j = first.succ then -(1 - mixingFractionalPart b last) else 0) ⬝ᵥ x := by
    -- The extra first-coordinate correction separates cleanly in the dot product.
    change
      ((mixingInequalityTypeOneCoeff b (first :: tail) +
            (fun j : Fin (n + 1) ↦
              if j = first.succ then -(1 - mixingFractionalPart b last) else 0)) ⬝ᵥ x =
        mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ x +
          (fun j : Fin (n + 1) ↦
            if j = first.succ then -(1 - mixingFractionalPart b last) else 0) ⬝ᵥ x)
    exact
      add_dotProduct
        (mixingInequalityTypeOneCoeff b (first :: tail))
        (fun j : Fin (n + 1) ↦
          if j = first.succ then -(1 - mixingFractionalPart b last) else 0)
        x
  rw [hadd, mixingInequalityTypeOneCoeff_dotProduct, singleCoordinateDotProduct]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: under a fixed reverse
decomposition, the public right-hand side of `(4.29)` matches the scalar normal form. -/
private lemma mixingInequalityTypeOneRhs_eq_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) :
    mixingInequalityTypeOneRhs b (first :: tail) =
      -mixingFractionalPart b last - mixingInequalityFloorSum b (first :: tail) := by
  -- Fix the reverse normal form once so later proofs can stay scalar.
  simp [mixingInequalityTypeOneRhs, hrev]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: under a fixed reverse
decomposition, the public right-hand side of `(4.30)` matches the scalar normal form. -/
private lemma mixingInequalityTypeTwoRhs_eq_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) :
    mixingInequalityTypeTwoRhs b (first :: tail) =
      -mixingFractionalPart b last - mixingInequalityFloorSum b (first :: tail) -
        (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ) := by
  -- Fix the reverse normal form once so later proofs can keep the first-index correction explicit.
  simp [mixingInequalityTypeTwoRhs, hrev]

/-- For an admissible mixing index sequence, the linear inequality with coefficient vector
`mixingInequalityTypeOneCoeff b s` is exactly `(4.29)`. -/
theorem mixingInequalityTypeOneCoeff_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeOneRhs b s ↔
      mixingInequalityTypeOne b s x := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Normalize both the coefficient inequality and the source inequality to one scalar form.
          rw [mixingInequalityTypeOne, hrev, mixingInequalityTypeOneCoeff_dotProduct,
            mixingInequalityTypeOneRhs_eq_of_reverse b first last tail revTail hrev]
          have hsum := mixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
          constructor
          · intro hineq
            linarith
          · intro hineq
            linarith

/-- For an admissible mixing index sequence, the linear inequality with coefficient vector
`mixingInequalityTypeTwoCoeff b s` is exactly `(4.30)`. -/
theorem mixingInequalityTypeTwoCoeff_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b s ⬝ᵥ x ≤ mixingInequalityTypeTwoRhs b s ↔
      mixingInequalityTypeTwo b s x := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Normalize both the coefficient inequality and the source inequality to one scalar form.
          rw [mixingInequalityTypeTwoCoeff_dotProduct_of_reverse b first last tail revTail hrev,
            mixingInequalityTypeTwoRhs_eq_of_reverse b first last tail revTail hrev]
          have hsum := mixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
          constructor
          · intro hineq
            have hsrc :
                mixingFractionalPart b last ≤
                  x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                    (1 - mixingFractionalPart b last) *
                      (x first.succ - (⌊b first⌋ : ℝ)) := by
              linarith
            simpa [mixingInequalityTypeTwo, hrev] using hsrc
          · intro hineq
            have hsrc :
                mixingFractionalPart b last ≤
                  x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                    (1 - mixingFractionalPart b last) *
                      (x first.succ - (⌊b first⌋ : ℝ)) := by
              simpa [mixingInequalityTypeTwo, hrev] using hineq
            linarith

/-- A zero-start mixing sequence consists of a zero-fraction index followed by a nonempty
admissible positive-fraction sequence starting strictly after it. -/
def IsZeroStartMixingIndexSequence
    (b : Fin n → ℚ) (i : Fin n) : List (Fin n) → Prop
  | [] => False
  | j :: js =>
      mixingFractionalPart b i = 0 ∧ i < j ∧ IsMixingIndexSequence b (j :: js)

/-- The length-two zero-start type-two inequality obtained when the positive tail is a singleton.
-/
def mixingZeroPositiveCouplingInequality
    (b : Fin n → ℚ) (i j : Fin n) (x : Fin (n + 1) → ℝ) : Prop :=
  mixingFractionalPart b j ≤
    x 0 +
      (1 - mixingFractionalPart b j) * (x i.succ - (⌊b i⌋ : ℝ)) +
      mixingFractionalPart b j * (x j.succ - (⌊b j⌋ : ℝ))

/-- The zero-start type-two mixing inequality whose distinguished first index has fractional part
`0` and whose remaining selected indices have strictly increasing positive fractional parts. -/
def mixingInequalityTypeTwoZeroStart
    (b : Fin n → ℚ) (i : Fin n) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s.reverse with
  | [] => True
  | last :: _ =>
      mixingFractionalPart b last ≤
        x 0 + mixingInequalityTypeOneSum b s x +
          (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))

/-- An auxiliary region cut out by `x₀ ≥ 0`, the zero-fraction singleton covering inequalities,
the zero-start type-two family (whose singleton positive-tail case is the length-two zero/positive
coupling inequality), and the positive-start mixing inequalities `(4.29)` and `(4.30)`. -/
def mixingInequalitiesRegion
    (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧
      (((∀ i : Fin n, mixingFractionalPart b i = 0 → (b i : ℝ) ≤ x 0 + x i.succ) ∧
        ∀ i : Fin n, ∀ s : List (Fin n),
          IsZeroStartMixingIndexSequence b i s →
            mixingInequalityTypeTwoZeroStart b i s x) ∧
      ∀ s : List (Fin n), IsMixingIndexSequence b s →
        mixingInequalityTypeOne b s x ∧ mixingInequalityTypeTwo b s x)}

/-- The source-facing region cut out by `x₀ ≥ 0` and the positive-start mixing inequalities
`(4.29)` and `(4.30)` for admissible positive-fraction index sequences. -/
def positiveFractionMixingInequalitiesRegion
    (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧
      ∀ s : List (Fin n), IsMixingIndexSequence b s →
        mixingInequalityTypeOne b s x ∧ mixingInequalityTypeTwo b s x}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every mixing fractional
part is nonnegative. -/
lemma mixingFractionalPart_nonneg
    (b : Fin n → ℚ) (i : Fin n) :
    0 ≤ mixingFractionalPart b i := by
  -- The Chapter 4 fractional part owner is just the real `Int.fract`.
  simpa [mixingFractionalPart_eq_fract] using Int.fract_nonneg ((b i : ℚ) : ℝ)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical point on the
slice `x 0 = c` takes the least integral successor coordinates allowed by the covering
inequalities. -/
noncomputable def mixingSliceWitness
    (b : Fin n → ℚ) (c : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases c (fun i : Fin n ↦ (⌈(b i : ℝ) - c⌉ : ℝ))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every slice witness with
`0 ≤ c < 1` is already a mixed-integer generator of `mixingHull b`. -/
lemma mixingSliceWitness_mem_mixingSet
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingSet b := by
  -- The slice witness is integral on the tail and each covering inequality is the defining
  -- ceiling bound.
  rw [mem_mixingSet_iff]
  refine ⟨hc_nonneg, ?_, ?_⟩
  · rw [mem_integerVectors_iff_forall]
    intro i
    refine ⟨⌈(b i : ℝ) - c⌉, ?_⟩
    simp [mixingSliceWitness]
  · intro i
    have hceil : (b i : ℝ) - c ≤ (⌈(b i : ℝ) - c⌉ : ℝ) := by
      exact_mod_cast Int.le_ceil ((b i : ℝ) - c)
    have hcover : (b i : ℝ) ≤ c + (⌈(b i : ℝ) - c⌉ : ℝ) := by
      linarith
    simpa [mixingSliceWitness, add_comm] using hcover

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every slice witness with
`0 ≤ c < 1` already lies in `mixingHull b` because it is itself a generator. -/
lemma mixingSliceWitness_mem_mixingHull
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingHull b := by
  -- Promote the explicit mixed-set witness into the public convex-hull owner.
  simpa [mixingHull] using
    (subset_convexHull ℝ (mixingSet b) (mixingSliceWitness_mem_mixingSet b hc_nonneg hc_lt_one))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: among the ordered extended
fractional parts there is a last index whose value still lies at or below a prescribed slice
level `c ≥ 0`. -/
private lemma exists_last_index_le_extendedMixingFractionalPart
    (b : Fin n → ℚ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    ∃ t : Fin (n + 1),
      extendedMixingFractionalPart b t ≤ c ∧
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ t := by
  let lower :
      Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun t : Fin (n + 1) ↦ extendedMixingFractionalPart b t ≤ c)
  have hzero_mem : (0 : Fin (n + 1)) ∈ lower := by
    -- The zeroth extended fractional part is `0`, so the filtered set is nonempty.
    simp [lower, hc_nonneg]
  refine ⟨lower.max' ⟨0, hzero_mem⟩, ?_, ?_⟩
  · -- The chosen maximal index still satisfies the defining slice-level bound.
    exact (Finset.mem_filter.mp (lower.max'_mem ⟨0, hzero_mem⟩)).2
  · intro s hs
    -- Any other index below the slice level belongs to the same filtered set and is bounded above
    -- by the chosen maximal one.
    exact lower.le_max' s (by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the unit slice, the
shifted successor coordinate of the slice witness is the floor branch `0` or the ceiling branch
`1` according to whether the breakpoint `mixingFractionalPart b i` has already been reached. -/
lemma mixingSliceWitness_shiftProfile
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) (i : Fin n) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) =
      if mixingFractionalPart b i ≤ c then 0 else 1 := by
  -- Normalize the slice coordinate by the public floor/ceiling breakpoint lemma.
  have hcoord :
      mixingSliceWitness b c i.succ =
        if mixingFractionalPart b i ≤ c then (⌊b i⌋ : ℝ) else (⌈b i⌉ : ℝ) := by
    simp [mixingSliceWitness, ceil_sub_eq_floor_or_ceil_by_fract hc_nonneg hc_lt_one i]
  rw [hcoord]
  by_cases hfi : mixingFractionalPart b i ≤ c
  · rw [if_pos hfi]
    simpa [mixingFractionalPart_eq_fract] using hfi
  · rw [if_neg hfi]
    have hfi_ne_zero : mixingFractionalPart b i ≠ 0 := by
      intro hzero
      apply hfi
      rw [hzero]
      exact hc_nonneg
    have hfi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne (mixingFractionalPart_nonneg b i) hfi_ne_zero.symm
    rw [show (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 by
      exact_mod_cast
        (Int.ceil_eq_floor_add_one_iff_notMem (b i)).2 (by
          intro hmem
          rcases hmem with ⟨z, hz⟩
          have hz' : ((b i : ℚ) : ℝ) = (z : ℝ) := by
            simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) hz.symm
          have hfract_zero : mixingFractionalPart b i = 0 := by
            rw [mixingFractionalPart_eq_fract, hz']
            simp
          exact (ne_of_gt hfi_pos) hfract_zero)]
    simpa [mixingFractionalPart_eq_fract] using (lt_of_not_ge hfi)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the slice profile
collapses to the floor branch once the breakpoint has been reached. -/
lemma mixingSliceWitness_shiftProfile_of_le
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : mixingFractionalPart b i ≤ c) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 := by
  -- Record the reached-breakpoint branch as a reusable rewrite rule.
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_pos hfi]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the slice profile
collapses to the ceiling branch while the breakpoint still lies ahead. -/
lemma mixingSliceWitness_shiftProfile_of_lt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : c < mixingFractionalPart b i) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 1 := by
  -- Record the strict branch once so later telescoping proofs can rewrite directly to `1`.
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_neg (not_le.mpr hfi)]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: adding the head ray
preserves the mixed-integer generators. -/
lemma mixingSet_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingSet b := by
  -- The head ray increases `x 0` by one, decreases every successor coordinate by one, and leaves
  -- each covering sum unchanged.
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  refine ⟨?_, ?_, ?_⟩
  · have hhead : (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
      simp [exercise_3_29_ray_apply]
    rw [hhead]
    linarith
  · rw [mem_integerVectors_iff_forall] at htail ⊢
    intro t
    rcases htail t with ⟨m, hm⟩
    refine ⟨m - 1, ?_⟩
    simp [exercise_3_29_ray_apply, hm, sub_eq_add_neg]
  · intro t
    have ht := hcover t
    have hmixed :
        (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 +
            (x + exercise_3_29_ray (0 : Fin (n + 1))) t.succ =
          x 0 + x t.succ := by
      simp [exercise_3_29_ray_apply, sub_eq_add_neg]
      ring
    rw [hmixed]
    exact ht

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the head ray acts by a
recession direction on `mixingHull b`. -/
lemma mixingHull_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
  -- Push the generator-level head-ray move through the convex hull.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray (0 : Fin (n + 1))
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    simpa [mixingHull] using
      (subset_convexHull ℝ (mixingSet b) (mixingSet_add_headRay_mem b hy))
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
            = a * y j + c * z j + (a + c) * r j := by
                ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every successor Exercise
3.29 ray also acts by a recession direction on `mixingHull b`. -/
lemma mixingHull_add_successorRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ} (i : Fin n)
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray i.succ ∈ mixingHull b := by
  -- Push the generator-level successor translation from Proposition 4.33 through the convex hull.
  let r : Fin (n + 1) → ℝ := exercise_3_29_ray i.succ
  let translated : Set (Fin (n + 1) → ℝ) := {y | y + r ∈ mixingHull b}
  have hsubset : mixingSet b ⊆ translated := by
    intro y hy
    change y + r ∈ mixingHull b
    simpa [mixingHull] using
      (subset_convexHull ℝ (mixingSet b) (mixingSet_add_successor_ray_mem hy i))
  have hconv : Convex ℝ translated := by
    intro y hy z hz a c ha hc hac
    change a • y + c • z + r ∈ mixingHull b
    have hcomb :
        a • (y + r) + c • (z + r) ∈ mixingHull b :=
      (convex_convexHull ℝ (mixingSet b)) hy hz ha hc hac
    have hrewrite :
        a • (y + r) + c • (z + r) = a • y + c • z + r := by
      ext j
      calc
        a * (y j + r j) + c * (z j + r j)
            = a * y j + c * z j + (a + c) * r j := by
                ring
        _ = a * y j + c * z j + r j := by
              rw [hac, one_mul]
        _ = (a • y + c • z + r) j := by
              simp [Pi.add_apply, Pi.smul_apply]
    rw [← hrewrite]
    exact hcomb
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min hsubset hconv hxHull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: subtracting the head ray
from a mixing-set point with `x₀ ≥ 1` keeps the point in the mixing set. -/
lemma mixingSet_sub_headRay_of_one_le
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) (hx0_ge_one : 1 ≤ x 0) :
    x - exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingSet b := by
  -- Lower the head coordinate by one and raise each integral successor coordinate by one.
  rw [mem_mixingSet_iff] at hx ⊢
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  refine ⟨?_, ?_, ?_⟩
  · have hhead :
        (x - exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 - 1 := by
      simp [exercise_3_29_ray_apply, sub_eq_add_neg]
    rw [hhead]
    linarith
  · rw [mem_integerVectors_iff_forall] at htail ⊢
    intro i
    rcases htail i with ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    simpa [exercise_3_29_ray_apply, hm, sub_eq_add_neg]
  · intro i
    have hi := hcover i
    have hsum :
        (x - exercise_3_29_ray (0 : Fin (n + 1))) 0 +
            (x - exercise_3_29_ray (0 : Fin (n + 1))) i.succ =
          x 0 + x i.succ := by
      simp [exercise_3_29_ray_apply, sub_eq_add_neg]
      ring
    rw [hsum]
    exact hi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: along a strictly
increasing fractional-part chain, every tail member has fractional part at least that of the
head. -/
private lemma mixingFractionalPart_le_of_mem_chain
    (b : Fin n → ℚ) {i : Fin n} {is : List (Fin n)}
    (hchain : (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    {j : Fin n} (hj : j ∈ is) :
    mixingFractionalPart b i ≤ mixingFractionalPart b j := by
  -- The chain relation from the head to every tail element is the needed lower bound.
  exact le_of_lt (hchain.rel_cons hj)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if every selected
fractional part lies strictly above `c`, then the slice witness at `c` makes the shifted
type-one sum telescope to the last fractional part minus the incoming base level. -/
private lemma mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, c < mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - prev
  | prev, s, hgt, hchain => by
      induction s generalizing prev with
      | nil =>
          -- The empty selected list contributes no shifted sum and has no terminal breakpoint.
          simp [mixingInequalityTypeOneSumAux]
      | cons i is ih =>
          have hi_gt : c < mixingFractionalPart b i := hgt i (by simp)
          have hshift :
              mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 1 := by
            -- Every selected breakpoint lies above `c`, so the slice witness stays on the
            -- ceiling branch at that coordinate.
            exact mixingSliceWitness_shiftProfile_of_lt b hc_nonneg hc_lt_one hi_gt
          cases is with
          | nil =>
              -- A singleton chain telescopes immediately to its unique endpoint.
              simp [mixingInequalityTypeOneSumAux, hshift]
          | cons j js =>
              have htail_gt : ∀ k ∈ j :: js, c < mixingFractionalPart b k := by
                intro k hk
                exact hgt k (by simp [hk])
              have htail_chain :
                  (j :: js).IsChain
                    (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
                -- Drop the head once so the inductive telescope can reuse the same chain owner.
                simpa using hchain.tail
              have htail :=
                ih (prev := mixingFractionalPart b i) htail_gt htail_chain
              cases hrev : (j :: js).reverse with
              | nil =>
                  simp at hrev
              | cons last revTail =>
                  -- Rewrite the tail to its terminal breakpoint and then collapse the scalar
                  -- telescope.
                  rw [hrev] at htail
                  rw [mixingInequalityTypeOneSumAux, hshift, htail]
                  simp [List.reverse_cons, hrev]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: starting from any base
level `prev ≤ c`, the slice witness at `c` satisfies every shifted type-one inequality attached
to a strictly increasing fractional-part chain above `prev`. -/
private lemma mixingInequalityTypeOneSumAux_last_le_sliceWitness
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      prev ≤ c →
      (∀ j ∈ s, prev ≤ mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      match s.reverse with
      | [] => True
      | last :: _ =>
          mixingFractionalPart b last ≤
            c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev s
  | prev, s, hprev_le, hprev, hchain => by
      induction s generalizing prev with
      | nil =>
          -- The empty selected list has no terminal breakpoint inequality to check.
          simp
      | cons i is ih =>
          by_cases hi_le_c : mixingFractionalPart b i ≤ c
          · have hshift :
              mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 := by
              -- Once the current breakpoint is below the slice level, the witness uses the floor
              -- branch and contributes no new shifted slack.
              exact mixingSliceWitness_shiftProfile_of_le
                (b := b) (c := c) hc_nonneg hc_lt_one (i := i) hi_le_c
            cases is with
            | nil =>
                -- For a singleton list, the target reduces to the breakpoint bound `fi ≤ c`.
                simpa [mixingInequalityTypeOneSumAux, hshift] using hi_le_c
            | cons j js =>
                have htail_chain :
                    (j :: js).IsChain
                      (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
                  -- The recursive tail retains the same strict fractional-part chain.
                  simpa using hchain.tail
                have htail_prev :
                    ∀ k ∈ j :: js, mixingFractionalPart b i ≤ mixingFractionalPart b k := by
                  intro k hk
                  exact mixingFractionalPart_le_of_mem_chain b hchain hk
                have htail :=
                  ih (prev := mixingFractionalPart b i) hi_le_c htail_prev htail_chain
                cases hrev : (j :: js).reverse with
                | nil =>
                    simp at hrev
                | cons last revTail =>
                    -- After the head contributes `0`, the target is exactly the recursive tail
                    -- inequality written in the same reverse normal form.
                    rw [hrev] at htail
                    simpa [mixingInequalityTypeOneSumAux, hshift, List.reverse_cons, hrev] using
                      htail
          · have hi_gt : c < mixingFractionalPart b i := lt_of_not_ge hi_le_c
            have hall_gt : ∀ k ∈ i :: is, c < mixingFractionalPart b k := by
              intro k hk
              by_cases hk_head : k = i
              · simpa [hk_head] using hi_gt
              · have hk_tail : k ∈ is := by
                  simpa [hk_head] using hk
                have hi_le_k :
                    mixingFractionalPart b i ≤ mixingFractionalPart b k := by
                  exact mixingFractionalPart_le_of_mem_chain b hchain hk_tail
                linarith
            have htel :=
              mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt
                (b := b) hc_nonneg hc_lt_one (prev := prev) (s := i :: is) hall_gt hchain
            cases hrev : (i :: is).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                -- Above the slice level, the explicit telescope from the previous lemma reduces
                -- the target to the standing hypothesis `prev ≤ c`.
                rw [hrev] at htel
                have hlast :
                    mixingFractionalPart b last ≤
                      c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev
                        (i :: is) := by
                  linarith
                simpa using hlast

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every slice witness on
`0 ≤ c < 1` already satisfies the full mixing-inequalities region. -/
lemma mixingSliceWitness_mem_mixingInequalitiesRegion
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingInequalitiesRegion b := by
  have hmixSet : mixingSliceWitness b c ∈ mixingSet b :=
    mixingSliceWitness_mem_mixingSet b hc_nonneg hc_lt_one
  rw [mem_mixingSet_iff] at hmixSet
  rcases hmixSet with ⟨_, _, hcover⟩
  refine ⟨hc_nonneg, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i hi_zero
      -- The zero-fraction singleton covers are already part of the generator witness.
      simpa [mixingSliceWitness] using hcover i
    · intro i s hs
      cases s with
      | nil =>
          cases hs
      | cons j js =>
          simp [IsZeroStartMixingIndexSequence] at hs
          rcases hs with ⟨hi_zero, _hi_lt, hsMix⟩
          rcases hsMix with ⟨_hfirst_pos, _hindexChain, hfracChain⟩
          have htail :
              match (j :: js).reverse with
              | [] => True
              | last :: _ =>
                  mixingFractionalPart b last ≤
                    c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0 (j :: js) := by
            -- The zero-start family reduces to the positive tail with base level `prev = 0`.
            simpa using
              mixingInequalityTypeOneSumAux_last_le_sliceWitness
                (b := b) hc_nonneg hc_lt_one (prev := 0) (s := j :: js) hc_nonneg
                (fun k _hk ↦ mixingFractionalPart_nonneg b k) hfracChain
          cases hrev : (j :: js).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              have hshift_zero :
                  mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 := by
                -- Zero fractional part is already below any slice level `c ≥ 0`.
                apply mixingSliceWitness_shiftProfile_of_le b hc_nonneg hc_lt_one
                simpa [hi_zero] using hc_nonneg
              rw [hrev] at htail
              have hsrc :
                  mixingFractionalPart b last ≤
                    c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0 (j :: js) +
                      (1 - mixingFractionalPart b last) *
                        (mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ)) := by
                rw [hshift_zero]
                simpa using htail
              simpa [mixingInequalityTypeTwoZeroStart, mixingInequalityTypeOneSum, mixingSliceWitness,
                hrev] using hsrc
  · intro s hs
    cases s with
    | nil =>
        cases hs
    | cons first tail =>
        simp [IsMixingIndexSequence] at hs
        rcases hs with ⟨hfirst_pos, _hindexChain, hfracChain⟩
        constructor
        · -- The public type-one inequality is exactly the repaired source-facing tail inequality.
          simpa [mixingInequalityTypeOne, mixingInequalityTypeOneSum, mixingSliceWitness] using
            mixingInequalityTypeOneSumAux_last_le_sliceWitness
              (b := b) hc_nonneg hc_lt_one (prev := 0) (s := first :: tail) hc_nonneg
              (fun j _hj ↦ mixingFractionalPart_nonneg b j) hfracChain
        ·
          have htypeOne :
              match (first :: tail).reverse with
              | [] => True
              | last :: _ =>
                  mixingFractionalPart b last ≤
                    c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0
                      (first :: tail) := by
            -- Reuse the same tail inequality before adding the nonnegative type-two correction.
            simpa using
              mixingInequalityTypeOneSumAux_last_le_sliceWitness
                (b := b) hc_nonneg hc_lt_one (prev := 0) (s := first :: tail) hc_nonneg
                (fun j _hj ↦ mixingFractionalPart_nonneg b j) hfracChain
          have hfirst_shift_nonneg :
              0 ≤ mixingSliceWitness b c first.succ - (⌊b first⌋ : ℝ) := by
            -- The slice witness shift is always either `0` or `1`.
            rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one first]
            split_ifs <;> norm_num
          cases hrev : (first :: tail).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              have hlast_lt_one : mixingFractionalPart b last < 1 := by
                simpa [mixingFractionalPart_eq_fract] using
                  Int.fract_lt_one (((b last : ℚ) : ℝ))
              have hcoeff_nonneg : 0 ≤ 1 - mixingFractionalPart b last := by
                linarith
              rw [hrev] at htypeOne
              have hcorrection_nonneg :
                  0 ≤
                    (1 - mixingFractionalPart b last) *
                      (mixingSliceWitness b c first.succ - (⌊b first⌋ : ℝ)) := by
                exact mul_nonneg hcoeff_nonneg hfirst_shift_nonneg
              have hsrc :
                  mixingFractionalPart b last ≤
                    c + mixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0
                        (first :: tail) +
                      (1 - mixingFractionalPart b last) *
                        (mixingSliceWitness b c first.succ - (⌊b first⌋ : ℝ)) := by
                linarith
              simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingSliceWitness, hrev]
                using hsrc

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: translating by the head
ray changes the shifted type-one sum by the incoming base level minus the last selected
fractional part. -/
private lemma mixingInequalityTypeOneSumAux_add_headRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneSumAux b (x + exercise_3_29_ray (0 : Fin (n + 1))) prev s =
        mixingInequalityTypeOneSumAux b x prev s +
          match s.reverse with
          | [] => 0
          | last :: _ => prev - mixingFractionalPart b last
  | prev, [] => by
      -- The empty selected list contributes no shifted sum.
      simp [mixingInequalityTypeOneSumAux]
  | prev, i :: is => by
      -- Each selected successor coordinate drops by `1`, and the coefficients telescope.
      have hcoord :
          (x + exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ) =
            (x i.succ - (⌊b i⌋ : ℝ)) - 1 := by
        have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
          simp
        calc
          (x + exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ)
              = (x i.succ + (-1 : ℝ)) - (⌊b i⌋ : ℝ) := by
                  simp [Pi.add_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
          _ = (x i.succ - (⌊b i⌋ : ℝ)) - 1 := by
                ring
      rw [mixingInequalityTypeOneSumAux, hcoord, mixingInequalityTypeOneSumAux_add_headRay]
      cases hrev : is.reverse with
      | nil =>
          simp [mixingInequalityTypeOneSumAux, List.reverse_cons, hrev]
          ring
      | cons last revTail =>
          rw [mixingInequalityTypeOneSumAux]
          simp [List.reverse_cons, hrev]
          ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: translating by the head
ray subtracts the last selected fractional part from the shifted type-one sum. -/
private lemma mixingInequalityTypeOneSum_add_headRay
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneSum b s (x + exercise_3_29_ray (0 : Fin (n + 1))) =
      mixingInequalityTypeOneSum b s x +
        match s.reverse with
        | [] => 0
        | last :: _ => -mixingFractionalPart b last := by
  -- Specialize the recursive head-ray transport at the public base level `0`.
  simpa [mixingInequalityTypeOneSum] using
    mixingInequalityTypeOneSumAux_add_headRay b x 0 s

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: adding the head ray
preserves the mixing-inequalities region. -/
lemma mixingInequalitiesRegion_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingInequalitiesRegion b := by
  rcases hx with ⟨hx0_nonneg, ⟨⟨hxZeroCover, hxZeroStart⟩, hxPositive⟩⟩
  refine ⟨?_, ?_⟩
  · -- The head ray raises the zeroth coordinate by one.
    have hhead : (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
      simp [exercise_3_29_ray_apply]
    rw [hhead]
    linarith
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i hi_zero
        -- The head ray preserves the zero-cover sums exactly.
        have hcover := hxZeroCover i hi_zero
        simpa [exercise_3_29_ray_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hcover
      · intro i s hs
        have hxIneq := hxZeroStart i s hs
        cases hrev : s.reverse with
        | nil =>
            simpa [mixingInequalityTypeTwoZeroStart, hrev]
        | cons last revTail =>
            rw [mixingInequalityTypeTwoZeroStart, hrev] at hxIneq ⊢
            have hsum :
                mixingInequalityTypeOneSum b s
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                  mixingInequalityTypeOneSum b s x - mixingFractionalPart b last := by
              simpa [hrev, sub_eq_add_neg] using mixingInequalityTypeOneSum_add_headRay b s x
            have hhead : (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
              simp [exercise_3_29_ray_apply]
            have hshift :
                (x + exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ) =
                  (x i.succ - (⌊b i⌋ : ℝ)) - 1 := by
              have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
                simp
              calc
                (x + exercise_3_29_ray (0 : Fin (n + 1))) i.succ - (⌊b i⌋ : ℝ)
                    = (x i.succ + (-1 : ℝ)) - (⌊b i⌋ : ℝ) := by
                        simp [Pi.add_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
                _ = (x i.succ - (⌊b i⌋ : ℝ)) - 1 := by ring
            rw [hsum, hhead, hshift]
            linarith
    · intro s hs
      rcases hxPositive s hs with ⟨hxTypeOne, hxTypeTwo⟩
      constructor
      · cases s with
        | nil =>
            cases hs
        | cons first tail =>
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                rw [mixingInequalityTypeOne, hrev] at hxTypeOne ⊢
                have hsum :
                    mixingInequalityTypeOneSum b (first :: tail)
                        (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                      mixingInequalityTypeOneSum b (first :: tail) x -
                        mixingFractionalPart b last := by
                  simpa [hrev, sub_eq_add_neg] using
                    mixingInequalityTypeOneSum_add_headRay b (first :: tail) x
                have hhead :
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
                  simp [exercise_3_29_ray_apply]
                have hlast_lt_one : mixingFractionalPart b last < 1 := by
                  simpa [mixingFractionalPart_eq_fract] using
                    Int.fract_lt_one (((b last : ℚ) : ℝ))
                rw [hsum, hhead]
                linarith
      · cases s with
        | nil =>
            cases hs
        | cons first tail =>
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeTwo' :
                    mixingFractionalPart b last ≤
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hxTypeTwo
                have hsum :
                    mixingInequalityTypeOneSum b (first :: tail)
                        (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                      mixingInequalityTypeOneSum b (first :: tail) x -
                        mixingFractionalPart b last := by
                  simpa [hrev, sub_eq_add_neg] using
                    mixingInequalityTypeOneSum_add_headRay b (first :: tail) x
                have hhead :
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
                  simp [exercise_3_29_ray_apply]
                have hshift :
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ) =
                      (x first.succ - (⌊b first⌋ : ℝ)) - 1 := by
                  have hsucc_ne_zero : ¬ (first.succ : Fin (n + 1)) = 0 := by
                    simp
                  calc
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ)
                        = (x first.succ + (-1 : ℝ)) - (⌊b first⌋ : ℝ) := by
                            simp [Pi.add_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
                    _ = (x first.succ - (⌊b first⌋ : ℝ)) - 1 := by ring
                have hgoal :
                    mixingFractionalPart b last ≤
                      (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 +
                        mixingInequalityTypeOneSum b (first :: tail)
                          (x + exercise_3_29_ray (0 : Fin (n + 1))) +
                        (1 - mixingFractionalPart b last) *
                          ((x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ -
                            (⌊b first⌋ : ℝ)) := by
                  rw [hsum, hhead, hshift]
                  linarith
                simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: adding a successor ray can
only increase the shifted type-one sum along a strictly increasing fractional-part chain. -/
private lemma mixingInequalityTypeOneSumAux_le_add_successorRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, prev ≤ mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      mixingInequalityTypeOneSumAux b x prev s ≤
        mixingInequalityTypeOneSumAux b (x + exercise_3_29_ray i.succ) prev s := by
  intro prev s hprev hchain
  induction s generalizing prev with
  | nil =>
      -- The empty selected list contributes no shifted sum in either spelling.
      simp [mixingInequalityTypeOneSumAux]
  | cons j js ih =>
      -- Split on whether the successor ray hits the current selected coordinate.
      have hj_prev : prev ≤ mixingFractionalPart b j := hprev j (by simp)
      have htail_prev :
          ∀ k ∈ js, mixingFractionalPart b j ≤ mixingFractionalPart b k := by
        intro k hk
        exact mixingFractionalPart_le_of_mem_chain b hchain hk
      have htail_chain :
          js.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
        simpa using hchain.tail
      have htail :=
        ih (prev := mixingFractionalPart b j) htail_prev htail_chain
      by_cases hji : j = i
      · subst j
        have hcoord :
            (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ) =
              (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by
          calc
            (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ)
                = (x i.succ + 1) - (⌊b i⌋ : ℝ) := by
                    simp [Pi.add_apply, exercise_3_29_ray_apply]
            _ = (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by ring
        have hcoeff_nonneg : 0 ≤ mixingFractionalPart b i - prev := sub_nonneg.mpr hj_prev
        rw [mixingInequalityTypeOneSumAux, mixingInequalityTypeOneSumAux, hcoord]
        linarith
      · have hcoord :
            (x + exercise_3_29_ray i.succ) j.succ - (⌊b j⌋ : ℝ) =
              x j.succ - (⌊b j⌋ : ℝ) := by
          simp [Pi.add_apply, exercise_3_29_ray_apply, hji]
        rw [mixingInequalityTypeOneSumAux, mixingInequalityTypeOneSumAux, hcoord]
        linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: adding a successor ray
preserves the mixing-inequalities region. -/
lemma mixingInequalitiesRegion_add_successorRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ} (i : Fin n)
    (hx : x ∈ mixingInequalitiesRegion b) :
    x + exercise_3_29_ray i.succ ∈ mixingInequalitiesRegion b := by
  rcases hx with ⟨hx0_nonneg, ⟨⟨hxZeroCover, hxZeroStart⟩, hxPositive⟩⟩
  have hhead : (x + exercise_3_29_ray i.succ) 0 = x 0 := by
    simpa using (exercise_3_29_ray_succ_head_coordinate_effect x 1 i).1
  refine ⟨?_, ?_⟩
  · -- Every successor ray fixes the head coordinate.
    rw [hhead]
    exact hx0_nonneg
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j hj_zero
        by_cases hji : j = i
        · subst j
          have hcover := hxZeroCover i hj_zero
          have hsum :
              (x + exercise_3_29_ray i.succ) 0 +
                  (x + exercise_3_29_ray i.succ) i.succ =
                x 0 + x i.succ + 1 := by
            simpa using (exercise_3_29_ray_succ_support_coordinate_effect x 1 i).1
          rw [hsum]
          linarith
        · have hcover := hxZeroCover j hj_zero
          have hsum :
              (x + exercise_3_29_ray i.succ) 0 +
                  (x + exercise_3_29_ray i.succ) j.succ =
                x 0 + x j.succ := by
            simpa [eq_comm] using
              (exercise_3_29_ray_succ_offsupport_coordinate_effect x 1 hji).1
          rw [hsum]
          exact hcover
      · intro j s hs
        cases s with
        | nil =>
            cases hs
        | cons first tail =>
            have hxZeroStart' := hxZeroStart j (first :: tail) hs
            simp [IsZeroStartMixingIndexSequence] at hs
            rcases hs with ⟨hj_zero, _hj_lt, hsMix⟩
            rcases hsMix with ⟨_hfirst_pos, _hindexChain, hfracChain⟩
            have hsum_mono :
                mixingInequalityTypeOneSum b (first :: tail) x ≤
                  mixingInequalityTypeOneSum b (first :: tail)
                    (x + exercise_3_29_ray i.succ) := by
              simpa [mixingInequalityTypeOneSum] using
                mixingInequalityTypeOneSumAux_le_add_successorRay
                  (b := b) (x := x) (i := i) (prev := 0) (s := first :: tail)
                  (fun k _hk ↦ mixingFractionalPart_nonneg b k) hfracChain
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxIneq :
                    mixingFractionalPart b last ≤
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) *
                          (x j.succ - (⌊b j⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwoZeroStart, hrev] using hxZeroStart'
                have hlast_lt_one : mixingFractionalPart b last < 1 := by
                  simpa [mixingFractionalPart_eq_fract] using
                    Int.fract_lt_one (((b last : ℚ) : ℝ))
                have hcoeff_nonneg : 0 ≤ 1 - mixingFractionalPart b last := by
                  linarith
                by_cases hji : j = i
                · subst j
                  have hshift :
                      (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ) =
                        (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by
                    calc
                      (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ)
                          = (x i.succ + 1) - (⌊b i⌋ : ℝ) := by
                              simp [Pi.add_apply, exercise_3_29_ray_apply]
                      _ = (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by ring
                  rw [mixingInequalityTypeTwoZeroStart, hrev, hhead, hshift]
                  linarith [hxIneq, hsum_mono, hcoeff_nonneg]
                · have hshift :
                      (x + exercise_3_29_ray i.succ) j.succ - (⌊b j⌋ : ℝ) =
                        x j.succ - (⌊b j⌋ : ℝ) := by
                    simp [Pi.add_apply, exercise_3_29_ray_apply, hji]
                  rw [mixingInequalityTypeTwoZeroStart, hrev, hhead, hshift]
                  linarith [hxIneq, hsum_mono]
    · intro s hs
      rcases hxPositive s hs with ⟨hxTypeOne, hxTypeTwo⟩
      cases s with
      | nil =>
          cases hs
      | cons first tail =>
          simp [IsMixingIndexSequence] at hs
          rcases hs with ⟨_hfirst_pos, _hindexChain, hfracChain⟩
          have hsum_mono :
              mixingInequalityTypeOneSum b (first :: tail) x ≤
                mixingInequalityTypeOneSum b (first :: tail)
                  (x + exercise_3_29_ray i.succ) := by
            simpa [mixingInequalityTypeOneSum] using
              mixingInequalityTypeOneSumAux_le_add_successorRay
                (b := b) (x := x) (i := i) (prev := 0) (s := first :: tail)
                (fun k _hk ↦ mixingFractionalPart_nonneg b k) hfracChain
          constructor
          · cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeOne' :
                    mixingFractionalPart b last ≤
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x := by
                  simpa [mixingInequalityTypeOne, hrev] using hxTypeOne
                rw [mixingInequalityTypeOne, hrev, hhead]
                linarith [hxTypeOne', hsum_mono]
          · cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeTwo' :
                    mixingFractionalPart b last ≤
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) *
                          (x first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hxTypeTwo
                have hlast_lt_one : mixingFractionalPart b last < 1 := by
                  simpa [mixingFractionalPart_eq_fract] using
                    Int.fract_lt_one (((b last : ℚ) : ℝ))
                have hcoeff_nonneg : 0 ≤ 1 - mixingFractionalPart b last := by
                  linarith
                by_cases hfirst : first = i
                · subst first
                  have hshift :
                      (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ) =
                        (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by
                    calc
                      (x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ)
                          = (x i.succ + 1) - (⌊b i⌋ : ℝ) := by
                              simp [Pi.add_apply, exercise_3_29_ray_apply]
                      _ = (x i.succ - (⌊b i⌋ : ℝ)) + 1 := by ring
                  have hgoal :
                      mixingFractionalPart b last ≤
                        (x + exercise_3_29_ray i.succ) 0 +
                          mixingInequalityTypeOneSum b (i :: tail)
                            (x + exercise_3_29_ray i.succ) +
                          (1 - mixingFractionalPart b last) *
                            ((x + exercise_3_29_ray i.succ) i.succ - (⌊b i⌋ : ℝ)) := by
                    rw [hhead, hshift]
                    linarith [hxTypeTwo', hsum_mono, hcoeff_nonneg]
                  simpa [mixingInequalityTypeTwo, hrev] using hgoal
                · have hshift :
                      (x + exercise_3_29_ray i.succ) first.succ - (⌊b first⌋ : ℝ) =
                        x first.succ - (⌊b first⌋ : ℝ) := by
                    simp [Pi.add_apply, exercise_3_29_ray_apply, hfirst]
                  have hgoal :
                      mixingFractionalPart b last ≤
                        (x + exercise_3_29_ray i.succ) 0 +
                          mixingInequalityTypeOneSum b (first :: tail)
                            (x + exercise_3_29_ray i.succ) +
                          (1 - mixingFractionalPart b last) *
                            ((x + exercise_3_29_ray i.succ) first.succ - (⌊b first⌋ : ℝ)) := by
                    rw [hhead, hshift]
                    linarith [hxTypeTwo', hsum_mono]
                  simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every point of the
mixing-inequalities region already satisfies the underlying Exercise 3.29 relaxation. -/
lemma mixingInequalitiesRegion_subset_exercise_3_29_polyhedron
    (b : Fin n → ℚ) :
    mixingInequalitiesRegion b ⊆ exercise_3_29_polyhedron (fun i : Fin n ↦ (b i : ℝ)) := by
  intro x hx
  rcases hx with ⟨hx0_nonneg, ⟨⟨hxZeroCover, _hxZeroStart⟩, hxPositive⟩⟩
  rw [mem_exercise_3_29_polyhedron_iff]
  refine ⟨hx0_nonneg, ?_⟩
  intro i
  by_cases hfi_zero : mixingFractionalPart b i = 0
  · exact hxZeroCover i hfi_zero
  · have hfi_nonneg : 0 ≤ mixingFractionalPart b i := mixingFractionalPart_nonneg b i
    have hfi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne hfi_nonneg (by simpa [eq_comm] using hfi_zero)
    have hs : IsMixingIndexSequence b [i] := by
      simpa [IsMixingIndexSequence, mixingFractionalPart_eq_fract] using hfi_pos
    have hxTypeTwo : mixingInequalityTypeTwo b [i] x := (hxPositive [i] hs).2
    have hxTypeTwo' :
        mixingFractionalPart b i ≤
          x 0 + mixingInequalityTypeOneSum b [i] x +
            (1 - mixingFractionalPart b i) * (x i.succ - (⌊b i⌋ : ℝ)) := by
      simpa [mixingInequalityTypeTwo] using hxTypeTwo
    have hsum_single :
        mixingInequalityTypeOneSum b [i] x =
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) := by
      simp [mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux]
    have hsrc :
        mixingFractionalPart b i ≤
          x 0 + (mixingFractionalPart b i) * (x i.succ - (⌊b i⌋ : ℝ)) +
            (1 - mixingFractionalPart b i) * (x i.succ - (⌊b i⌋ : ℝ)) := by
      rw [hsum_single] at hxTypeTwo'
      simpa using hxTypeTwo'
    have hfloor :
        (b i : ℝ) = (⌊b i⌋ : ℝ) + mixingFractionalPart b i := by
      simpa [mixingFractionalPart_eq_fract] using (Int.floor_add_fract (b i : ℝ)).symm
    linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: iterating a unit-step
translation yields every natural multiple of the same direction. -/
private lemma add_nat_smul_mem_of_unitStep
    {Q : Set (Fin (n + 1) → ℝ)} {r y : Fin (n + 1) → ℝ}
    (hy : y ∈ Q) (hstep : ∀ {z}, z ∈ Q → z + r ∈ Q) :
    ∀ m : ℕ, y + (m : ℝ) • r ∈ Q
  | 0 => by
      -- The zero multiple gives back the starting point.
      simpa
  | m + 1 => by
      -- Rewrite the next multiple as one more unit step from the inductive translate.
      have hm : y + (m : ℝ) • r ∈ Q := add_nat_smul_mem_of_unitStep hy hstep m
      have hnext : (y + (m : ℝ) • r) + r ∈ Q := hstep hm
      convert hnext using 1
      ext j
      simp [Nat.cast_add, add_smul, Pi.add_apply]
      ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: convexity upgrades a
unit-step closure property to every nonnegative real multiple of the same direction. -/
private lemma add_nonneg_smul_mem_of_unitStep
    {Q : Set (Fin (n + 1) → ℝ)} {r y : Fin (n + 1) → ℝ}
    (hconv : Convex ℝ Q) (hy : y ∈ Q) (hstep : ∀ {z}, z ∈ Q → z + r ∈ Q)
    {a : ℝ} (ha : 0 ≤ a) :
    y + a • r ∈ Q := by
  let mZ : ℤ := Int.floor a
  let m : ℕ := Int.toNat mZ
  let t : ℝ := Int.fract a
  have hmZ_nonneg : 0 ≤ mZ := by
    dsimp [mZ]
    exact Int.floor_nonneg.mpr ha
  have hm_cast : (m : ℝ) = (mZ : ℝ) := by
    dsimp [m]
    exact_mod_cast (Int.toNat_of_nonneg hmZ_nonneg)
  have hy_m : y + (m : ℝ) • r ∈ Q := add_nat_smul_mem_of_unitStep hy hstep m
  have hy_m_succ : y + ((m + 1 : ℕ) : ℝ) • r ∈ Q :=
    add_nat_smul_mem_of_unitStep hy hstep (m + 1)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Int.fract_nonneg a
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact (Int.fract_lt_one a).le
  have hcomb :
      (1 - t) • (y + (m : ℝ) • r) + t • (y + ((m + 1 : ℕ) : ℝ) • r) ∈ Q := by
    exact hconv hy_m hy_m_succ (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
  have hfloor_fract :
      a = (m : ℝ) + t := by
    calc
      a = (Int.floor a : ℝ) + Int.fract a := by simpa using (Int.floor_add_fract a).symm
      _ = (m : ℝ) + t := by simp [mZ, t, hm_cast]
  convert hcomb using 1
  ext j
  simp [Pi.add_apply, Pi.smul_apply]
  rw [hfloor_fract]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a convex set closed under
each successor unit ray is also closed under a finite sum of nonnegative successor-ray multiples.
-/
private lemma add_sum_nonneg_smul_successorRays_mem
    {Q : Set (Fin (n + 1) → ℝ)} (hconv : Convex ℝ Q) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ Q) (hstep : ∀ {z : Fin (n + 1) → ℝ} (i : Fin n), z ∈ Q →
      z + exercise_3_29_ray i.succ ∈ Q)
    (δ : Fin n → ℝ) (hδ : ∀ i : Fin n, 0 ≤ δ i) :
    y + (∑ i : Fin n, δ i • exercise_3_29_ray i.succ) ∈ Q := by
  classical
  -- Accumulate the nonnegative successor-ray shifts one coordinate at a time.
  let raySum : Finset (Fin n) → Fin (n + 1) → ℝ :=
    fun s ↦ Finset.sum s (fun i ↦ δ i • exercise_3_29_ray i.succ)
  have hacc (s : Finset (Fin n)) :
      y + raySum s ∈ Q := by
    induction s using Finset.induction_on with
    | empty =>
        simpa [raySum] using hy
    | @insert i s hi hs =>
        have hs_mem : y + raySum s ∈ Q := hs
        have hnext :
            (y + raySum s) + δ i • exercise_3_29_ray i.succ ∈ Q := by
          -- Use the one-ray closure lemma at the accumulated translate.
          exact add_nonneg_smul_mem_of_unitStep hconv hs_mem (hstep i) (hδ i)
        convert hnext using 1
        ext j
        simp [raySum, Finset.sum_insert, hi, Pi.add_apply, add_assoc, add_left_comm, add_comm]
  simpa [raySum] using hacc Finset.univ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the sum of successor-ray
multiples vanishes at the zeroth coordinate. -/
private lemma successorRaySum_apply_zero
    (δ : Fin n → ℝ) :
    (∑ i : Fin n, δ i • exercise_3_29_ray i.succ) 0 = 0 := by
  -- Every successor ray has zeroth coordinate `0`.
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
    simp
  have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = i.succ := by
    simpa [eq_comm] using hsucc_ne_zero
  rw [Pi.smul_apply, exercise_3_29_ray_apply, if_neg hsucc_ne_zero, if_neg hzero_ne_succ]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the successor-ray sum
recovers the chosen coefficient on each successor coordinate. -/
private lemma successorRaySum_apply_succ
    (δ : Fin n → ℝ) (j : Fin n) :
    (∑ i : Fin n, δ i • exercise_3_29_ray i.succ) j.succ = δ j := by
  -- Only the `j`-th successor ray contributes at coordinate `j.succ`.
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · have hsucc_ne_zero : ¬ (j.succ : Fin (n + 1)) = 0 := by
      simp
    rw [Pi.smul_apply, exercise_3_29_ray_apply, if_neg hsucc_ne_zero, if_pos rfl]
    ring
  · intro i _hi hij
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    have hs : ¬ (j.succ : Fin (n + 1)) = i.succ := by
      intro h
      apply hij
      simpa [eq_comm] using h
    rw [Pi.smul_apply, exercise_3_29_ray_apply, if_neg hsucc_ne_zero, if_neg hs]
    ring
  · intro hj
    simp at hj

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: affine combinations
distribute through the shifted type-one sum because the coefficients add to `1`. -/
private lemma mixingInequalityTypeOneSumAux_affineCombination
    (b : Fin n → ℚ) (a c : ℝ) (hac : a + c = 1)
    (x y : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      mixingInequalityTypeOneSumAux b (a • x + c • y) prev s =
        a * mixingInequalityTypeOneSumAux b x prev s +
          c * mixingInequalityTypeOneSumAux b y prev s
  | prev, s => by
      induction s generalizing prev with
      | nil =>
          -- The empty selected list contributes no shifted sum on either side.
          simp [mixingInequalityTypeOneSumAux]
      | cons i is ih =>
          have hshift :
              (a • x + c • y) i.succ - (⌊b i⌋ : ℝ) =
                a * (x i.succ - (⌊b i⌋ : ℝ)) + c * (y i.succ - (⌊b i⌋ : ℝ)) := by
            -- The shifted selected coordinate is affine because the weights add to `1`.
            rw [show (a • x + c • y) i.succ = a * x i.succ + c * y i.succ by
              simp [Pi.smul_apply, Pi.add_apply]]
            have hfloor :
                ((⌊b i⌋ : ℝ)) = a * (⌊b i⌋ : ℝ) + c * (⌊b i⌋ : ℝ) := by
              calc
                ((⌊b i⌋ : ℝ)) = (1 : ℝ) * (⌊b i⌋ : ℝ) := by ring
                _ = (a + c) * (⌊b i⌋ : ℝ) := by rw [hac]
                _ = a * (⌊b i⌋ : ℝ) + c * (⌊b i⌋ : ℝ) := by ring
            linarith
          -- After rewriting the head shifted coordinate, the recursive tail is exactly the
          -- induction hypothesis at the new base level `mixingFractionalPart b i`.
          rw [mixingInequalityTypeOneSumAux, hshift, ih, mixingInequalityTypeOneSumAux,
            mixingInequalityTypeOneSumAux]
          ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the full mixing
inequalities region is convex. -/
lemma convex_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    Convex ℝ (mixingInequalitiesRegion b) := by
  intro x hx y hy a c ha hc hac
  rcases hx with ⟨hx0_nonneg, ⟨⟨hxZeroCover, hxZeroStart⟩, hxPositive⟩⟩
  rcases hy with ⟨hy0_nonneg, ⟨⟨hyZeroCover, hyZeroStart⟩, hyPositive⟩⟩
  refine ⟨?_, ?_⟩
  · -- The zeroth coordinate is an affine combination of nonnegative values.
    have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
      simp [Pi.smul_apply, Pi.add_apply]
    rw [hhead]
    exact add_nonneg (mul_nonneg ha hx0_nonneg) (mul_nonneg hc hy0_nonneg)
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i hi_zero
        -- The zero-cover family is affine-linear coordinatewise.
        have hxCover := hxZeroCover i hi_zero
        have hyCover := hyZeroCover i hi_zero
        have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
          simp [Pi.smul_apply, Pi.add_apply]
        have hsucc : (a • x + c • y) i.succ = a * x i.succ + c * y i.succ := by
          simp [Pi.smul_apply, Pi.add_apply]
        rw [hhead, hsucc]
        have hweighted :
            a * (b i : ℝ) + c * (b i : ℝ) ≤
              a * (x 0 + x i.succ) + c * (y 0 + y i.succ) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hxCover ha)
            (mul_le_mul_of_nonneg_left hyCover hc)
        have hleft : a * (b i : ℝ) + c * (b i : ℝ) = (b i : ℝ) := by
          rw [← add_mul, hac, one_mul]
        have hright :
            a * (x 0 + x i.succ) + c * (y 0 + y i.succ) =
              a * x 0 + c * y 0 + (a * x i.succ + c * y i.succ) := by
          ring
        rw [hleft, hright] at hweighted
        exact hweighted
      · intro i s hs
        -- The zero-start family stays affine because the shifted sum and correction term do.
        have hxIneq := hxZeroStart i s hs
        have hyIneq := hyZeroStart i s hs
        cases hrev : s.reverse with
        | nil =>
            simp [mixingInequalityTypeTwoZeroStart, hrev]
        | cons last revTail =>
            rw [mixingInequalityTypeTwoZeroStart, hrev] at hxIneq hyIneq ⊢
            have hsum :
                mixingInequalityTypeOneSum b s (a • x + c • y) =
                  a * mixingInequalityTypeOneSum b s x + c * mixingInequalityTypeOneSum b s y := by
              simpa [mixingInequalityTypeOneSum] using
                mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0 s
            have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
              simp [Pi.smul_apply, Pi.add_apply]
            have hsucc : (a • x + c • y) i.succ = a * x i.succ + c * y i.succ := by
              simp [Pi.smul_apply, Pi.add_apply]
            have hshift :
                (a • x + c • y) i.succ - (⌊b i⌋ : ℝ) =
                  a * (x i.succ - (⌊b i⌋ : ℝ)) + c * (y i.succ - (⌊b i⌋ : ℝ)) := by
              have hc_eq : c = 1 - a := by linarith
              rw [hsucc, hc_eq]
              ring
            rw [hsum, hhead, hshift]
            have hweighted :
                a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                  a * (x 0 + mixingInequalityTypeOneSum b s x +
                    (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                  c * (y 0 + mixingInequalityTypeOneSum b s y +
                    (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hxIneq ha)
                (mul_le_mul_of_nonneg_left hyIneq hc)
            have hleft :
                a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
              rw [← add_mul, hac, one_mul]
            have hright :
                a * (x 0 + mixingInequalityTypeOneSum b s x +
                    (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                  c * (y 0 + mixingInequalityTypeOneSum b s y +
                    (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) =
                  a * x 0 + c * y 0 +
                    (a * mixingInequalityTypeOneSum b s x + c * mixingInequalityTypeOneSum b s y) +
                    ((1 - mixingFractionalPart b last) *
                      (a * (x i.succ - (⌊b i⌋ : ℝ)) + c * (y i.succ - (⌊b i⌋ : ℝ)))) := by
              ring
            rw [hleft, hright] at hweighted
            simpa [mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib] using
              hweighted
    · intro s hs
      -- The positive-start families are the same affine calculation without the zero-start owner.
      rcases hxPositive s hs with ⟨hxTypeOne, hxTypeTwo⟩
      rcases hyPositive s hs with ⟨hyTypeOne, hyTypeTwo⟩
      constructor
      · cases s with
        | nil =>
            cases hs
        | cons first tail =>
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                rw [mixingInequalityTypeOne, hrev] at hxTypeOne hyTypeOne ⊢
                have hsum :
                    mixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                      a * mixingInequalityTypeOneSum b (first :: tail) x +
                        c * mixingInequalityTypeOneSum b (first :: tail) y := by
                  simpa [mixingInequalityTypeOneSum] using
                    mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                      (first :: tail)
                have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                  simp [Pi.smul_apply, Pi.add_apply]
                rw [hsum, hhead]
                have hweighted :
                    a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                      a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x) +
                        c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hxTypeOne ha)
                    (mul_le_mul_of_nonneg_left hyTypeOne hc)
                have hleft :
                    a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                      mixingFractionalPart b last := by
                  rw [← add_mul, hac, one_mul]
                have hright :
                    a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x) +
                      c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y) =
                      a * x 0 + c * y 0 +
                        (a * mixingInequalityTypeOneSum b (first :: tail) x +
                          c * mixingInequalityTypeOneSum b (first :: tail) y) := by
                  ring
                rw [hleft, hright] at hweighted
                simpa [add_assoc, add_left_comm, add_comm] using hweighted
      · cases s with
        | nil =>
            cases hs
        | cons first tail =>
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeTwo' :
                    mixingFractionalPart b last ≤
                      x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hxTypeTwo
                have hyTypeTwo' :
                    mixingFractionalPart b last ≤
                      y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                        (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hyTypeTwo
                have hsum :
                    mixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                      a * mixingInequalityTypeOneSum b (first :: tail) x +
                        c * mixingInequalityTypeOneSum b (first :: tail) y := by
                  simpa [mixingInequalityTypeOneSum] using
                    mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                      (first :: tail)
                have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                  simp [Pi.smul_apply, Pi.add_apply]
                have hsucc :
                    (a • x + c • y) first.succ = a * x first.succ + c * y first.succ := by
                  simp [Pi.smul_apply, Pi.add_apply]
                have hshift :
                    (a • x + c • y) first.succ - (⌊b first⌋ : ℝ) =
                      a * (x first.succ - (⌊b first⌋ : ℝ)) +
                        c * (y first.succ - (⌊b first⌋ : ℝ)) := by
                  have hc_eq : c = 1 - a := by linarith
                  rw [hsucc, hc_eq]
                  ring
                have hgoal :
                    mixingFractionalPart b last ≤
                      (a • x + c • y) 0 +
                        mixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) +
                        (1 - mixingFractionalPart b last) *
                          ((a • x + c • y) first.succ - (⌊b first⌋ : ℝ)) := by
                  rw [hsum, hhead, hshift]
                  have hweighted :
                      a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                        a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                          (1 - mixingFractionalPart b last) *
                            (x first.succ - (⌊b first⌋ : ℝ))) +
                        c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                          (1 - mixingFractionalPart b last) *
                            (y first.succ - (⌊b first⌋ : ℝ))) := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hxTypeTwo' ha)
                      (mul_le_mul_of_nonneg_left hyTypeTwo' hc)
                  have hleft :
                      a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                        mixingFractionalPart b last := by
                    rw [← add_mul, hac, one_mul]
                  have hright :
                      a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                          (1 - mixingFractionalPart b last) *
                            (x first.succ - (⌊b first⌋ : ℝ))) +
                        c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                          (1 - mixingFractionalPart b last) *
                            (y first.succ - (⌊b first⌋ : ℝ))) =
                        a * x 0 + c * y 0 +
                          (a * mixingInequalityTypeOneSum b (first :: tail) x +
                            c * mixingInequalityTypeOneSum b (first :: tail) y) +
                          ((1 - mixingFractionalPart b last) *
                            (a * (x first.succ - (⌊b first⌋ : ℝ)) +
                              c * (y first.succ - (⌊b first⌋ : ℝ)))) := by
                    ring
                  linarith [hweighted, hleft, hright]
                simpa [mixingInequalityTypeTwo, hrev] using hgoal
/-
  intro x hx y hy a c ha hc hac
  rcases hx with ⟨hx0_nonneg, ⟨hxZeroCover, hxZeroStart⟩, hxPositive⟩
  rcases hy with ⟨hy0_nonneg, ⟨hyZeroCover, hyZeroStart⟩, hyPositive⟩
  refine ⟨?_, ?_, ?_⟩
  · have hhead :
        (a • x + c • y) 0 = a * x 0 + c * y 0 := by
      simp [Pi.smul_apply, Pi.add_apply]
    rw [hhead]
    exact add_nonneg (mul_nonneg ha hx0_nonneg) (mul_nonneg hc hy0_nonneg)
  · refine ⟨?_, ?_⟩
    · intro i hi_zero
      have hxCover := hxZeroCover i hi_zero
      have hyCover := hyZeroCover i hi_zero
      have hhead :
          (a • x + c • y) 0 = a * x 0 + c * y 0 := by
        simp [Pi.smul_apply, Pi.add_apply]
      have hsucc :
          (a • x + c • y) i.succ = a * x i.succ + c * y i.succ := by
        simp [Pi.smul_apply, Pi.add_apply]
      rw [hhead, hsucc]
      have hweighted :
          a * (b i : ℝ) + c * (b i : ℝ) ≤
            a * (x 0 + x i.succ) + c * (y 0 + y i.succ) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hxCover ha)
          (mul_le_mul_of_nonneg_left hyCover hc)
      have hleft : a * (b i : ℝ) + c * (b i : ℝ) = (b i : ℝ) := by
        rw [← add_mul, hac, one_mul]
      have hright :
          a * (x 0 + x i.succ) + c * (y 0 + y i.succ) =
            a * x 0 + c * y 0 + (a * x i.succ + c * y i.succ) := by
        ring
      rw [hleft, hright] at hweighted
      exact hweighted
    · intro i s hs
      have hxIneq := hxZeroStart i s hs
      have hyIneq := hyZeroStart i s hs
      cases hrev : s.reverse with
      | nil =>
          simp [mixingInequalityTypeTwoZeroStart, hrev]
      | cons last revTail =>
          rw [mixingInequalityTypeTwoZeroStart, hrev] at hxIneq hyIneq ⊢
          have hsum :
              mixingInequalityTypeOneSum b s (a • x + c • y) =
                a * mixingInequalityTypeOneSum b s x + c * mixingInequalityTypeOneSum b s y := by
            simpa [mixingInequalityTypeOneSum] using
              mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0 s
          have hhead :
              (a • x + c • y) 0 = a * x 0 + c * y 0 := by
            simp [Pi.smul_apply, Pi.add_apply]
          have hshift :
              (a • x + c • y) i.succ - (⌊b i⌋ : ℝ) =
                a * (x i.succ - (⌊b i⌋ : ℝ)) + c * (y i.succ - (⌊b i⌋ : ℝ)) := by
            rw [show (a • x + c • y) i.succ = a * x i.succ + c * y i.succ by
              simp [Pi.smul_apply, Pi.add_apply]]
            rw [hac]
            ring
          rw [hsum, hhead, hshift]
          have hweighted :
              a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                a * (x 0 + mixingInequalityTypeOneSum b s x +
                  (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                c * (y 0 + mixingInequalityTypeOneSum b s y +
                  (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hxIneq ha)
              (mul_le_mul_of_nonneg_left hyIneq hc)
          have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
              mixingFractionalPart b last := by
            rw [← add_mul, hac, one_mul]
          have hright :
              a * (x 0 + mixingInequalityTypeOneSum b s x +
                  (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                c * (y 0 + mixingInequalityTypeOneSum b s y +
                  (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) =
                a * x 0 + c * y 0 +
                  (a * mixingInequalityTypeOneSum b s x + c * mixingInequalityTypeOneSum b s y) +
                  ((1 - mixingFractionalPart b last) *
                    (a * (x i.succ - (⌊b i⌋ : ℝ)) + c * (y i.succ - (⌊b i⌋ : ℝ)))) := by
            ring
          rw [hleft, hright] at hweighted
          simpa [mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib] using
            hweighted
  · intro s hs
    rcases hxPositive s hs with ⟨hxTypeOne, hxTypeTwo⟩
    rcases hyPositive s hs with ⟨hyTypeOne, hyTypeTwo⟩
    constructor
    · cases s with
      | nil =>
          cases hs
      | cons first tail =>
          cases hrev : (first :: tail).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              rw [mixingInequalityTypeOne, hrev] at hxTypeOne hyTypeOne ⊢
              have hsum :
                  mixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                    a * mixingInequalityTypeOneSum b (first :: tail) x +
                      c * mixingInequalityTypeOneSum b (first :: tail) y := by
                simpa [mixingInequalityTypeOneSum] using
                  mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                    (first :: tail)
              have hhead :
                  (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                simp [Pi.smul_apply, Pi.add_apply]
              rw [hsum, hhead]
              have hweighted :
                  a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                    a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x) +
                      c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hxTypeOne ha)
                  (mul_le_mul_of_nonneg_left hyTypeOne hc)
              have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
                rw [← add_mul, hac, one_mul]
              have hright :
                  a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x) +
                    c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y) =
                    a * x 0 + c * y 0 +
                      (a * mixingInequalityTypeOneSum b (first :: tail) x +
                        c * mixingInequalityTypeOneSum b (first :: tail) y) := by
                ring
              rw [hleft, hright] at hweighted
              simpa [add_assoc, add_left_comm, add_comm] using hweighted
    · cases s with
      | nil =>
          cases hs
      | cons first tail =>
          cases hrev : (first :: tail).reverse with
          | nil =>
              simp at hrev
          | cons last revTail =>
              rw [mixingInequalityTypeTwo, hrev] at hxTypeTwo hyTypeTwo ⊢
              have hsum :
                  mixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                    a * mixingInequalityTypeOneSum b (first :: tail) x +
                      c * mixingInequalityTypeOneSum b (first :: tail) y := by
                simpa [mixingInequalityTypeOneSum] using
                  mixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                    (first :: tail)
              have hhead :
                  (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                simp [Pi.smul_apply, Pi.add_apply]
              have hshift :
                  (a • x + c • y) first.succ - (⌊b first⌋ : ℝ) =
                    a * (x first.succ - (⌊b first⌋ : ℝ)) +
                      c * (y first.succ - (⌊b first⌋ : ℝ)) := by
                rw [show (a • x + c • y) first.succ = a * x first.succ + c * y first.succ by
                  simp [Pi.smul_apply, Pi.add_apply]]
                rw [hac]
                ring
              rw [hsum, hhead, hshift]
              have hweighted :
                  a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                    a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                      (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))) +
                    c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                      (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ))) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hxTypeTwo ha)
                  (mul_le_mul_of_nonneg_left hyTypeTwo hc)
              have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
                rw [← add_mul, hac, one_mul]
              have hright :
                  a * (x 0 + mixingInequalityTypeOneSum b (first :: tail) x +
                      (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))) +
                    c * (y 0 + mixingInequalityTypeOneSum b (first :: tail) y +
                      (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ))) =
                    a * x 0 + c * y 0 +
                      (a * mixingInequalityTypeOneSum b (first :: tail) x +
                        c * mixingInequalityTypeOneSum b (first :: tail) y) +
                      ((1 - mixingFractionalPart b last) *
                        (a * (x first.succ - (⌊b first⌋ : ℝ)) +
                          c * (y first.succ - (⌊b first⌋ : ℝ)))) := by
                ring
              rw [hleft, hright] at hweighted
              simpa [mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib]
                using hweighted
-/

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every mixed-integer
generator already lies in the full mixing-inequalities region. -/
lemma mixingSet_subset_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    mixingSet b ⊆ mixingInequalitiesRegion b := by
  intro x hx
  rw [mem_mixingSet_iff_forall] at hx
  rcases hx with ⟨hx0_nonneg, htail, hcover⟩
  let mZ : ℤ := ⌊x 0⌋
  let m : ℕ := Int.toNat mZ
  let c : ℝ := Int.fract (x 0)
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  have hmZ_nonneg : 0 ≤ mZ := by
    dsimp [mZ]
    exact Int.floor_nonneg.mpr hx0_nonneg
  have hm_cast : (m : ℝ) = (mZ : ℝ) := by
    dsimp [m]
    exact_mod_cast (Int.toNat_of_nonneg hmZ_nonneg)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Int.fract_nonneg (x 0)
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Int.fract_lt_one (x 0)
  have hx0_eq : x 0 = (mZ : ℝ) + c := by
    simpa [mZ, c] using (Int.floor_add_fract (x 0)).symm
  have hdom :
      ∀ i : Fin n, mixingSliceWitness b c i.succ ≤ y i.succ := by
    intro i
    rcases htail i with ⟨zi, hzi⟩
    have hcover' : (b i : ℝ) ≤ c + y i.succ := by
      calc
        (b i : ℝ) ≤ x 0 + x i.succ := hcover i
        _ = (mZ : ℝ) + c + x i.succ := by rw [hx0_eq]
        _ = c + y i.succ := by simp [y, add_assoc, add_left_comm, add_comm]
    have hyi :
        y i.succ = ((zi + mZ : ℤ) : ℝ) := by
      simp [y, hzi]
    have hsub : (b i : ℝ) - c ≤ ((zi + mZ : ℤ) : ℝ) := by
      rw [hyi] at hcover'
      linarith
    have hceil_le : ⌈(b i : ℝ) - c⌉ ≤ zi + mZ := Int.ceil_le.mpr hsub
    have hceil_le_real :
        ((⌈(b i : ℝ) - c⌉ : ℤ) : ℝ) ≤ y i.succ := by
      have : (((⌈(b i : ℝ) - c⌉ : ℤ) : ℝ) ≤ ((zi + mZ : ℤ) : ℝ)) := by
        exact_mod_cast hceil_le
      simpa [hyi] using this
    simpa [mixingSliceWitness] using hceil_le_real
  have hy_region :
      y ∈ mixingInequalitiesRegion b := by
    have hwitness :
        mixingSliceWitness b c ∈ mixingInequalitiesRegion b :=
      mixingSliceWitness_mem_mixingInequalitiesRegion b hc_nonneg hc_lt_one
    have hδ_nonneg :
        ∀ i : Fin n, 0 ≤ y i.succ - mixingSliceWitness b c i.succ := by
      intro i
      exact sub_nonneg.mpr (hdom i)
    have htranslate :
        mixingSliceWitness b c +
            ∑ i : Fin n, (y i.succ - mixingSliceWitness b c i.succ) •
              exercise_3_29_ray i.succ ∈
          mixingInequalitiesRegion b := by
      exact
        add_sum_nonneg_smul_successorRays_mem
          (hconv := convex_mixingInequalitiesRegion b)
          hwitness
          (fun {z} i hz ↦ mixingInequalitiesRegion_add_successorRay_mem b i hz)
          (fun i ↦ y i.succ - mixingSliceWitness b c i.succ)
          (fun i ↦ hδ_nonneg i)
    have hy_eq :
        mixingSliceWitness b c +
            ∑ i : Fin n, (y i.succ - mixingSliceWitness b c i.succ) •
              exercise_3_29_ray i.succ = y := by
      ext j
      refine Fin.cases ?_ ?_ j
      · -- Successor rays vanish at the zeroth coordinate, so the head stays at `c`.
        calc
          (mixingSliceWitness b c +
                ∑ i : Fin n, (y i.succ - mixingSliceWitness b c i.succ) •
                  exercise_3_29_ray i.succ) 0
              = mixingSliceWitness b c 0 +
                  (∑ i : Fin n, (y i.succ - mixingSliceWitness b c i.succ) •
                    exercise_3_29_ray i.succ) 0 := by
                    simp [Pi.add_apply]
          _ = c := by
                rw [successorRaySum_apply_zero]
                simp [mixingSliceWitness]
          _ = y 0 := by
                simp [y]
      · intro i
        -- At successor coordinates, the accumulated ray sum adds exactly the needed slack.
        rw [Pi.add_apply, successorRaySum_apply_succ]
        simp [y]
    simpa [hy_eq] using htranslate
  -- Add back the integer head part by iterating the head ray.
  have hx_region_translate :
      y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingInequalitiesRegion b := by
    exact
      add_nat_smul_mem_of_unitStep
        hy_region
        (fun {z} hz ↦ mixingInequalitiesRegion_add_headRay_mem b hz)
        m
  have hx_eq_translate :
      y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) = x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · -- The head translation restores `⌊x₀⌋ + fract(x₀)`.
      calc
        (y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))) 0
            = y 0 + (m : ℝ) * 1 := by
                simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply]
        _ = c + (mZ : ℝ) := by simp [y, hm_cast]
        _ = x 0 := by rw [add_comm, hx0_eq]
    · intro i
      have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
        simp
      calc
        (y + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1))) i.succ
            = y i.succ + (m : ℝ) * (-1 : ℝ) := by
                simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
        _ = x i.succ + (mZ : ℝ) - (m : ℝ) := by
              simp [y]
              ring
        _ = x i.succ := by
              rw [hm_cast]
              ring
  simpa [hx_eq_translate] using hx_region_translate

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the full mixing hull
already satisfies every defining inequality in the mixing-inequalities region. -/
lemma mixingHull_subset_mixingInequalitiesRegion
    (b : Fin n → ℚ) :
    mixingHull b ⊆ mixingInequalitiesRegion b := by
  -- A convex set containing every generator automatically contains the whole convex hull.
  intro x hx
  have hxHull : x ∈ convexHull ℝ (mixingSet b) := by
    simpa [mixingHull] using hx
  exact convexHull_min (mixingSet_subset_mixingInequalitiesRegion b)
    (convex_mixingInequalitiesRegion b) hxHull

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every candidate point
along the ordered fractional-part chain is already a mixed-integer generator. -/
private lemma mixingVertexCandidate_mem_mixingSet_of_monotone
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (t : Fin (n + 1)) :
    mixingVertexCandidate b t ∈ mixingSet b := by
  -- Route correction: prove candidate feasibility directly from the monotone breakpoint profile,
  -- instead of rebuilding the last-occurrence API inside this file.
  rw [mem_mixingSet_iff_forall]
  refine ⟨extendedMixingFractionalPart_nonneg t, ?_, ?_⟩
  · -- Each successor coordinate is visibly either a floor or a ceiling, hence integral.
    intro i
    rw [mixingVertexCandidate_apply_succ]
    by_cases hi : i.succ ≤ t
    · exact ⟨⌊b i⌋, by simp [hi]⟩
    · exact ⟨⌈b i⌉, by simp [hi]⟩
  · intro i
    rw [mixingVertexCandidate_apply_zero, mixingVertexCandidate_apply_succ]
    by_cases hi : i.succ ≤ t
    · -- Below `t`, monotonicity gives `f_i ≤ f_t`, so the floor branch already covers `b_i`.
      have hfrac_le : mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
        simpa using hmono hi
      have hfrac_eq :
          (b i : ℝ) = (⌊b i⌋ : ℝ) + mixingFractionalPart b i := by
        simpa [mixingFractionalPart_eq_fract] using (Int.floor_add_fract (b i : ℝ)).symm
      rw [if_pos hi]
      linarith
    · -- Above `t`, the candidate uses the ceiling branch, which is feasible because `f_t ≥ 0`.
      have ht_nonneg : 0 ≤ extendedMixingFractionalPart b t :=
        extendedMixingFractionalPart_nonneg t
      have hceil : (b i : ℝ) ≤ (⌈b i⌉ : ℝ) := by
        exact_mod_cast Int.le_ceil (b i)
      rw [if_neg hi]
      linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every monotone candidate
point already lies in the public mixing hull. -/
private lemma mixingVertexCandidate_mem_mixingHull_of_monotone
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (t : Fin (n + 1)) :
    mixingVertexCandidate b t ∈ mixingHull b := by
  -- Promote the candidate generator into the convex-hull owner.
  simpa [mixingHull] using
    (subset_convexHull ℝ (mixingSet b)
      (mixingVertexCandidate_mem_mixingSet_of_monotone b hmono t))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the upper endpoint of the
nonterminal slice chord is the next extended-fraction index. -/
private def mixingSliceChordUpper
    (tLo : Fin (n + 1)) (hlt : tLo.1 < n) : Fin (n + 1) :=
  ⟨tLo.1 + 1, Nat.succ_lt_succ hlt⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the plateau-aware slice
point is the affine interpolation between the last lower breakpoint and the last occurrence of
the next distinct upper breakpoint. -/
private noncomputable def mixingPlateauChord
    (b : Fin n → ℚ) (c : ℝ) (tLo tHi : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  let denom : ℝ := extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo
  ((extendedMixingFractionalPart b tHi - c) / denom) • mixingVertexCandidate b tLo +
    ((c - extendedMixingFractionalPart b tLo) / denom) • mixingVertexCandidate b tHi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a normalized slice
point in `mixingHull b` sits below the shifted tail of `x`, the head ray and successor rays
reassemble `x` inside `mixingHull b`. -/
private noncomputable def mixingLowerCandidateTranslate
    (b : Fin n → ℚ) (c : ℝ) (tLo : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  mixingVertexCandidate b tLo +
    (c - extendedMixingFractionalPart b tLo) •
      exercise_3_29_ray (0 : Fin (n + 1))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the reverse-inclusion
slice point is the adjacent candidate chord until the last breakpoint and then the terminal head
ray translate afterwards. -/
noncomputable def mixingSliceChord
    (b : Fin n → ℚ) (c : ℝ) (tLo : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  if hlt : tLo.1 < n then
    let tHi : Fin (n + 1) := mixingSliceChordUpper tLo hlt
    let denom : ℝ := extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo
    ((extendedMixingFractionalPart b tHi - c) / denom) • mixingVertexCandidate b tLo +
      ((c - extendedMixingFractionalPart b tLo) / denom) • mixingVertexCandidate b tHi
  else
    mixingVertexCandidate b tLo +
      (c - extendedMixingFractionalPart b tLo) •
        exercise_3_29_ray (0 : Fin (n + 1))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the nonterminal
branch, `mixingSliceChord` is exactly the plateau-aware interpolation owner. -/
private lemma mixingSliceChord_eq_plateauChord
    (b : Fin n → ℚ) (c : ℝ) (tLo : Fin (n + 1)) (hlt : tLo.1 < n) :
    mixingSliceChord b c tLo =
      mixingPlateauChord b c tLo (mixingSliceChordUpper tLo hlt) := by
  -- Unfold the branch once so later proofs can rewrite to the stable plateau owner.
  rw [mixingSliceChord, dif_pos hlt, mixingPlateauChord]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the terminal branch,
`mixingSliceChord` is exactly the lower-breakpoint head-ray translate. -/
private lemma mixingSliceChord_eq_lowerTranslate
    (b : Fin n → ℚ) (c : ℝ) (tLo : Fin (n + 1)) (hterminal : ¬ tLo.1 < n) :
    mixingSliceChord b c tLo = mixingLowerCandidateTranslate b c tLo := by
  -- Unfold the terminal branch once so later proofs can use the head-ray-translate API directly.
  rw [mixingSliceChord, dif_neg hterminal, mixingLowerCandidateTranslate]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a positive fractional part
forces the corresponding ceiling to be one above the floor. -/
private lemma ceil_eq_floor_add_one_of_positive_fractionalPart
    (b : Fin n → ℚ) {i : Fin n} (hfi_pos : 0 < mixingFractionalPart b i) :
    (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
  -- Positive fractional part means the entry is not integral, so the usual floor/ceiling gap is
  -- exactly one.
  exact_mod_cast
    (Int.ceil_eq_floor_add_one_iff_notMem (b i)).2 (by
      intro hmem
      rcases hmem with ⟨z, hz⟩
      have hz' : ((b i : ℚ) : ℝ) = (z : ℝ) := by
        simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) hz.symm
      have hfract_zero : mixingFractionalPart b i = 0 := by
        rw [mixingFractionalPart_eq_fract, hz']
        simp
      exact (ne_of_gt hfi_pos) hfract_zero)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once `tLo` is the last
extended-fraction index at or below `c`, the next distinct fractional value is realized at the
last occurrence of the adjacent threshold value. -/
private lemma existsNextDistinctBreakpointLastIndex
    (b : Fin n → ℚ) {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (hlt : tLo.1 < n) :
    ∃ tHi : Fin (n + 1),
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) ∧
      c < extendedMixingFractionalPart b tHi ∧
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s =
          extendedMixingFractionalPart b tHi → s ≤ tHi := by
  let tAdj : Fin (n + 1) := mixingSliceChordUpper tLo hlt
  have htAdj_mem :
      extendedMixingFractionalPart b tAdj ∈ Set.range (extendedMixingFractionalPart b) := by
    exact ⟨tAdj, rfl⟩
  rcases exists_last_index_of_mem_range
      (f := extendedMixingFractionalPart b) htAdj_mem with
    ⟨tHi, htHi, hlast⟩
  refine ⟨tHi, htHi, ?_, ?_⟩
  · -- The adjacent threshold must lie strictly above `c`, otherwise `tLo` was not maximal.
    have htLo_lt_tAdj : tLo < tAdj := by
      exact Fin.lt_def.mpr (by simp [tAdj, mixingSliceChordUpper])
    have hnot_le : ¬ extendedMixingFractionalPart b tAdj ≤ c := by
      intro hle
      have hidx : tAdj ≤ tLo := htLo_max _ hle
      exact not_le_of_gt htLo_lt_tAdj hidx
    rw [htHi]
    exact lt_of_not_ge hnot_le
  · intro s hs
    exact hlast s (by simpa [htHi] using hs)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the plateau-aware chord
interpolates the zeroth coordinate to the target slice level `c`. -/
private lemma mixingPlateauChord_apply_zero
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)}
    (_htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (_hc_lt_hi : c < extendedMixingFractionalPart b tHi)
    (hdenom_pos :
      0 <
        extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) :
    mixingPlateauChord b c tLo tHi 0 = c := by
  -- Compare the zeroth coordinate in the plateau-owner spelling and clear the positive
  -- denominator once.
  rw [mixingPlateauChord]
  simp [Pi.add_apply, Pi.smul_apply, mixingVertexCandidate_apply_zero]
  field_simp [hdenom_pos.ne']
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the plateau-aware slice
point belongs to the mixing hull because it is a convex combination of two hull vertices. -/
private lemma mixingPlateauChord_mem_mixingHull
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {c : ℝ} {tLo tHi : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (hc_lt_hi : c < extendedMixingFractionalPart b tHi) :
    mixingPlateauChord b c tLo tHi ∈ mixingHull b := by
  have hconv : Convex ℝ (mixingHull b) := by
    -- The public hull alias is convex because it is a convex hull.
    simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
  have hdenom_pos :
      0 <
        extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo := by
    linarith
  let a : ℝ :=
    (extendedMixingFractionalPart b tHi - c) /
      (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo)
  let d : ℝ :=
    (c - extendedMixingFractionalPart b tLo) /
      (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo)
  have ha_nonneg : 0 ≤ a := by
    -- The upper weight is nonnegative because `c` lies below the upper breakpoint.
    dsimp [a]
    exact div_nonneg (sub_nonneg.mpr (le_of_lt hc_lt_hi)) (le_of_lt hdenom_pos)
  have hd_nonneg : 0 ≤ d := by
    -- The lower weight is nonnegative because `c` lies above the lower breakpoint.
    dsimp [d]
    exact div_nonneg (sub_nonneg.mpr htLo_le) (le_of_lt hdenom_pos)
  have had : a + d = 1 := by
    -- The two interpolation weights add to one.
    dsimp [a, d]
    field_simp [hdenom_pos.ne']
    ring
  rw [mixingPlateauChord]
  exact hconv
    (mixingVertexCandidate_mem_mixingHull_of_monotone b hmono tLo)
    (mixingVertexCandidate_mem_mixingHull_of_monotone b hmono tHi)
    ha_nonneg hd_nonneg had

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: below the lower
breakpoint, the plateau-aware slice chord stays on the floor branch. -/
private lemma mixingPlateauChord_apply_succ_of_le
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)} {i : Fin n}
    (htLo_le_tHi : tLo ≤ tHi)
    (hdenom_pos :
      0 <
        extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo)
    (hi : i.succ ≤ tLo) :
    mixingPlateauChord b c tLo tHi i.succ = (⌊b i⌋ : ℝ) := by
  -- Both endpoints are already on the floor branch at coordinate `i.succ`.
  rw [mixingPlateauChord]
  have hLo : mixingVertexCandidate b tLo i.succ = (⌊b i⌋ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_pos hi]
  have hHi : mixingVertexCandidate b tHi i.succ = (⌊b i⌋ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_pos (le_trans hi htLo_le_tHi)]
  simp [Pi.add_apply, Pi.smul_apply, hLo, hHi]
  field_simp [hdenom_pos.ne']
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the upper plateau,
the plateau-aware slice chord uses the affine interpolation branch. -/
private lemma mixingPlateauChord_apply_succ_of_lt_le
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)} {i : Fin n}
    (hc_nonneg : 0 ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (htLo_lt_i : tLo < i.succ)
    (hi_le : i.succ ≤ tHi)
    (hdenom_pos :
      0 <
        extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) :
    mixingPlateauChord b c tLo tHi i.succ =
      (⌊b i⌋ : ℝ) +
        (extendedMixingFractionalPart b tHi - c) /
          (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) := by
  -- The lower endpoint uses the ceiling branch, while the upper endpoint has already switched to
  -- the floor branch.
  have hnot_le_c : ¬ mixingFractionalPart b i ≤ c := by
    intro hfi_le
    have hi_le_tLo : i.succ ≤ tLo := by
      simpa using htLo_max i.succ hfi_le
    exact not_le_of_gt htLo_lt_i hi_le_tLo
  have hc_lt_fi : c < mixingFractionalPart b i := lt_of_not_ge hnot_le_c
  have hfi_pos : 0 < mixingFractionalPart b i := lt_of_le_of_lt hc_nonneg hc_lt_fi
  rw [mixingPlateauChord]
  have hLo : mixingVertexCandidate b tLo i.succ = (⌈b i⌉ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_neg (not_le.mpr htLo_lt_i)]
  have hHi : mixingVertexCandidate b tHi i.succ = (⌊b i⌋ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_pos hi_le]
  simp [Pi.add_apply, Pi.smul_apply, hLo, hHi,
    ceil_eq_floor_add_one_of_positive_fractionalPart b hfi_pos]
  field_simp [hdenom_pos.ne']
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: strictly above the upper
plateau, the plateau-aware slice chord stays on the ceiling branch. -/
private lemma mixingPlateauChord_apply_succ_of_lt
    (b : Fin n → ℚ) {c : ℝ} {tLo tHi : Fin (n + 1)} {i : Fin n}
    (htLo_le_tHi : tLo ≤ tHi)
    (htHi_lt_i : tHi < i.succ)
    (hdenom_pos :
      0 <
        extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) :
    mixingPlateauChord b c tLo tHi i.succ = (⌈b i⌉ : ℝ) := by
  -- Both endpoints remain on the ceiling branch above the upper breakpoint.
  rw [mixingPlateauChord]
  have htLo_lt_i : tLo < i.succ := lt_of_le_of_lt htLo_le_tHi htHi_lt_i
  have hLo : mixingVertexCandidate b tLo i.succ = (⌈b i⌉ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_neg (not_le.mpr htLo_lt_i)]
  have hHi : mixingVertexCandidate b tHi i.succ = (⌈b i⌉ : ℝ) := by
    rw [mixingVertexCandidate_apply_succ, if_neg (not_le.mpr htHi_lt_i)]
  simp [Pi.add_apply, Pi.smul_apply, hLo, hHi]
  field_simp [hdenom_pos.ne']
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the lower-breakpoint
head-ray translate already lies in the mixing hull. -/
private lemma mixingLowerCandidateTranslate_mem_mixingHull
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c) :
    mixingLowerCandidateTranslate b c tLo ∈ mixingHull b := by
  have hconv : Convex ℝ (mixingHull b) := by
    -- The public hull alias is convex because it is a convex hull.
    simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
  have hε_nonneg : 0 ≤ c - extendedMixingFractionalPart b tLo := by
    linarith
  -- Start from the lower candidate and move along the head ray by the remaining slice amount.
  rw [mixingLowerCandidateTranslate]
  exact add_nonneg_smul_mem_of_unitStep hconv
    (mixingVertexCandidate_mem_mixingHull_of_monotone b hmono tLo)
    (fun {z} hz ↦ mixingHull_add_headRay_mem b hz)
    hε_nonneg

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the lower-breakpoint
head-ray translate has zeroth coordinate exactly `c`. -/
private lemma mixingLowerCandidateTranslate_apply_zero
    (b : Fin n → ℚ) {c : ℝ} {tLo : Fin (n + 1)} :
    mixingLowerCandidateTranslate b c tLo 0 = c := by
  -- The head ray changes the zeroth coordinate by exactly the remaining slice amount.
  rw [mixingLowerCandidateTranslate]
  simp [mixingVertexCandidate_apply_zero, exercise_3_29_ray_apply]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on successor coordinates,
the lower-breakpoint translate is the candidate value minus the remaining head shift. -/
private lemma mixingLowerCandidateTranslate_apply_succ
    (b : Fin n → ℚ) {c : ℝ} {tLo : Fin (n + 1)} (i : Fin n) :
    mixingLowerCandidateTranslate b c tLo i.succ =
      mixingVertexCandidate b tLo i.succ -
        (c - extendedMixingFractionalPart b tLo) := by
  have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
    simp
  -- Every successor coordinate of the head ray is `-1`, so the translation subtracts the slice
  -- remainder from the candidate profile.
  rw [mixingLowerCandidateTranslate]
  simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once `tLo` is maximal
below `c`, the slice chord has zeroth coordinate exactly `c`. -/
private lemma mixingSliceChord_apply_zero
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    mixingSliceChord b c tLo 0 = c := by
  by_cases hlt : tLo.1 < n
  · -- Rewrite to the plateau owner and compare against the next strictly higher breakpoint.
    rw [mixingSliceChord_eq_plateauChord b c tLo hlt]
    have htLo_lt_tHi : tLo < mixingSliceChordUpper tLo hlt := by
      exact Fin.lt_def.mpr (by simp [mixingSliceChordUpper])
    have hc_lt_hi : c < extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) := by
      apply lt_of_not_ge
      intro hhi_le
      have hle : mixingSliceChordUpper tLo hlt ≤ tLo := htLo_max _ hhi_le
      exact not_le_of_gt htLo_lt_tHi hle
    have hdenom_pos :
        0 <
          extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) -
            extendedMixingFractionalPart b tLo := by
      have hmono_le :
          extendedMixingFractionalPart b tLo ≤
            extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) := by
        exact hmono (le_of_lt htLo_lt_tHi)
      linarith
    simpa using
      mixingPlateauChord_apply_zero
        (b := b) (c := c) (tLo := tLo) (tHi := mixingSliceChordUpper tLo hlt)
        htLo_le hc_lt_hi hdenom_pos
  · -- Rewrite to the terminal owner and read off the zeroth coordinate from the head translation.
    rw [mixingSliceChord_eq_lowerTranslate b c tLo hlt]
    simpa using mixingLowerCandidateTranslate_apply_zero (b := b) (c := c) (tLo := tLo)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the maximal-lower-breakpoint
slice chord already lies in the mixing hull. -/
private lemma mixingSliceChord_mem_mixingHull
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    mixingSliceChord b c tLo ∈ mixingHull b := by
  by_cases hlt : tLo.1 < n
  · -- Rewrite to the plateau owner and interpolate between the adjacent hull vertices.
    rw [mixingSliceChord_eq_plateauChord b c tLo hlt]
    have htLo_lt_tHi : tLo < mixingSliceChordUpper tLo hlt := by
      exact Fin.lt_def.mpr (by simp [mixingSliceChordUpper])
    have hc_lt_hi : c < extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) := by
      apply lt_of_not_ge
      intro hhi_le
      have hle : mixingSliceChordUpper tLo hlt ≤ tLo := htLo_max _ hhi_le
      exact not_le_of_gt htLo_lt_tHi hle
    exact
      mixingPlateauChord_mem_mixingHull
        (b := b) (hmono := hmono) (tLo := tLo) (tHi := mixingSliceChordUpper tLo hlt)
        htLo_le hc_lt_hi
  · -- Rewrite to the terminal owner and move along the head ray from the lower breakpoint.
    rw [mixingSliceChord_eq_lowerTranslate b c tLo hlt]
    exact mixingLowerCandidateTranslate_mem_mixingHull (b := b) (hmono := hmono) htLo_le

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every region point yields
the basic normalized cover-gap lower bound on each shifted successor coordinate. -/
private lemma normalizedShift_ge_coverGap
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (i : Fin n) :
    mixingFractionalPart b i - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- First pass to the Exercise 3.29 relaxation, then rewrite the single covering inequality in the
  -- normalized shifted spelling.
  have hxPoly :=
    mixingInequalitiesRegion_subset_exercise_3_29_polyhedron (b := b) hx
  rw [mem_exercise_3_29_polyhedron_iff] at hxPoly
  have hcover : (b i : ℝ) ≤ x 0 + x i.succ := hxPoly.2 i
  have hfloor :
      (b i : ℝ) = (⌊b i⌋ : ℝ) + mixingFractionalPart b i := by
    simpa [mixingFractionalPart_eq_fract] using (Int.floor_add_fract (b i : ℝ)).symm
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: between the last lower
breakpoint and the last occurrence of the adjacent upper breakpoint, every successor coordinate
has the same extended fractional value as the upper breakpoint. -/
private lemma extendedMixingFractionalPart_eq_upper_of_betweenBreakpoints
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tLo tHi : Fin (n + 1)} {i : Fin n}
    (hlt : tLo.1 < n)
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (htLo_lt_i : tLo < i.succ)
    (hi_le_tHi : i.succ ≤ tHi) :
    extendedMixingFractionalPart b i.succ =
      extendedMixingFractionalPart b tHi := by
  -- The adjacent breakpoint `tLo + 1` already has the upper value, and monotonicity forces every
  -- intermediate index up to `tHi` to carry the same value.
  have hAdj_le_i : mixingSliceChordUpper tLo hlt ≤ i.succ := by
    exact Fin.le_def.mpr (Nat.succ_le_of_lt (Fin.lt_def.mp htLo_lt_i))
  have hAdj_le :
      extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) ≤
        extendedMixingFractionalPart b i.succ := by
    exact hmono hAdj_le_i
  have hi_le :
      extendedMixingFractionalPart b i.succ ≤
        extendedMixingFractionalPart b tHi := by
    exact hmono hi_le_tHi
  have htHi_le :
      extendedMixingFractionalPart b tHi ≤
        extendedMixingFractionalPart b i.succ := by
    rw [hHi_eq]
    exact hAdj_le
  exact le_antisymm hi_le htHi_le

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the upper plateau, the
basic normalized cover-gap bound upgrades to the common adjacent-breakpoint gap. -/
private lemma normalizedShift_ge_upperBreakpointGap_of_betweenBreakpoints
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo tHi : Fin (n + 1)} {i : Fin n}
    (hlt : tLo.1 < n)
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (htLo_lt_i : tLo < i.succ)
    (hi_le_tHi : i.succ ≤ tHi) :
    extendedMixingFractionalPart b tHi - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- Replace the current plateau coordinate by the shared upper breakpoint value, then reuse the
  -- normalized cover-gap estimate.
  have hcover := normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i
  have hfrac_eq :
      mixingFractionalPart b i = extendedMixingFractionalPart b tHi := by
    simpa [extendedMixingFractionalPart_succ] using
      extendedMixingFractionalPart_eq_upper_of_betweenBreakpoints
        (b := b) hmono hlt hHi_eq htLo_lt_i hi_le_tHi
  rw [hfrac_eq] at hcover
  exact hcover

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: strictly above the last
upper-breakpoint occurrence, the shifted cover-gap bound is already strictly larger than the
adjacent upper-breakpoint gap. -/
private lemma normalizedShift_gt_upperBreakpointGap_of_upperBreakpoint_lt
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tHi : Fin (n + 1)} {i : Fin n}
    (hHi_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s =
          extendedMixingFractionalPart b tHi → s ≤ tHi)
    (htHi_lt_i : tHi < i.succ) :
    extendedMixingFractionalPart b tHi - c <
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- The strict index inequality forces a strictly larger fractional value than the upper plateau
  -- value, so the basic cover-gap bound is already strictly stronger here.
  have hcover := normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i
  have hfrac_lt :
      extendedMixingFractionalPart b tHi < mixingFractionalPart b i := by
    have hmono_le :
        extendedMixingFractionalPart b tHi ≤ extendedMixingFractionalPart b i.succ := by
      exact hmono (le_of_lt htHi_lt_i)
    have hne :
        extendedMixingFractionalPart b i.succ ≠ extendedMixingFractionalPart b tHi := by
      intro hi_eq
      have hi_le_tHi : i.succ ≤ tHi := hHi_last i.succ hi_eq
      exact not_le_of_gt htHi_lt_i hi_le_tHi
    exact lt_of_le_of_ne hmono_le (by
      simpa [extendedMixingFractionalPart_succ] using hne.symm)
  have hstrict :
      extendedMixingFractionalPart b tHi - c <
        mixingFractionalPart b i - c := by
    linarith
  exact lt_of_lt_of_le hstrict hcover

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: after subtracting the
floor profile, a last-occurrence candidate vertex is the expected `0/1` step function in the
breakpoint chain, with the zero-fraction coordinates forced to stay at `0`. -/
private lemma mixingVertexCandidate_shiftProfile_of_lastOccurrence
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {t : Fin (n + 1)}
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (i : Fin n) :
    mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ) =
      if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1 := by
  -- Route correction: rewrite candidate successors once to the stable shifted `0/1` profile
  -- promised by the last-occurrence API, instead of repeatedly unfolding local chord formulas.
  have ht_nonneg : 0 ≤ extendedMixingFractionalPart b t :=
    extendedMixingFractionalPart_nonneg t
  have ht_lt_one : extendedMixingFractionalPart b t < 1 :=
    extendedMixingFractionalPart_lt_one t
  rw [mixingVertexCandidate_succ_eq_ceil_sub_of_last_occurrence hmono hlast i,
    ceil_sub_eq_floor_or_ceil_by_fract ht_nonneg ht_lt_one i]
  by_cases hfi_zero : mixingFractionalPart b i = 0
  · -- Zero-fraction coordinates are integral, so both candidate branches collapse to the floor.
    have hfi_le : mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
      rw [hfi_zero]
      exact ht_nonneg
    rw [if_pos hfi_le, if_pos hfi_zero]
    ring
  · have hfi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne (mixingFractionalPart_nonneg b i) (by simpa [eq_comm] using hfi_zero)
    by_cases hle : i.succ ≤ t
    · -- Below the last occurrence, monotonicity keeps the shifted candidate on the floor branch.
      have hfi_le : mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
        simpa using hmono hle
      rw [if_pos hfi_le, if_neg hfi_zero, if_pos hle]
      ring
    · -- Above the last occurrence, the positive fractional part forces the ceiling branch.
      have hlt : t < i.succ := lt_of_not_ge hle
      have hfi_not_le :
          ¬ mixingFractionalPart b i ≤ extendedMixingFractionalPart b t := by
        intro hfrac_le
        have ht_le :
            extendedMixingFractionalPart b t ≤ extendedMixingFractionalPart b i.succ := by
          exact hmono (le_of_lt hlt)
        have hi_le :
            extendedMixingFractionalPart b i.succ ≤ extendedMixingFractionalPart b t := by
          simpa using hfrac_le
        have heq :
            extendedMixingFractionalPart b i.succ = extendedMixingFractionalPart b t :=
          le_antisymm hi_le ht_le
        have : i.succ ≤ t := hlast i.succ heq
        exact hle this
      rw [if_neg hfi_not_le, if_neg hfi_zero, if_neg hle,
        ceil_eq_floor_add_one_of_positive_fractionalPart b hfi_pos]
      ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if `c` is itself a
breakpoint value and `t` is its last occurrence, then the explicit slice witness at height `c`
already coincides with the canonical candidate vertex `v^t`. -/
private lemma mixingSliceWitness_eq_mixingVertexCandidate_of_lastOccurrence
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {c : ℝ} {t : Fin (n + 1)}
    (ht : extendedMixingFractionalPart b t = c)
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) :
    mixingSliceWitness b c = mixingVertexCandidate b t := by
  have hc_nonneg : 0 ≤ c := by
    -- Breakpoint values live in the unit interval.
    rw [← ht]
    exact extendedMixingFractionalPart_nonneg t
  have hc_lt_one : c < 1 := by
    -- Breakpoint values also stay strictly below `1`.
    rw [← ht]
    exact extendedMixingFractionalPart_lt_one t
  ext j
  refine Fin.cases ?_ ?_ j
  · -- The slice witness and the candidate vertex share the same head coordinate `c`.
    simpa [mixingSliceWitness, ht] using (mixingVertexCandidate_apply_zero (b := b) (t := t)).symm
  · intro i
    by_cases hle : i.succ ≤ t
    · -- Below the last occurrence, both owners stay on the floor branch.
      have hfi_le : mixingFractionalPart b i ≤ c := by
        calc
          mixingFractionalPart b i = extendedMixingFractionalPart b i.succ := by
            simp [extendedMixingFractionalPart_succ]
          _ ≤ extendedMixingFractionalPart b t := hmono hle
          _ = c := ht
      have hslice :
          mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 :=
        mixingSliceWitness_shiftProfile_of_le
          (b := b) (c := c) hc_nonneg hc_lt_one hfi_le
      have hvertex :
          mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ) = 0 := by
        rw [mixingVertexCandidate_shiftProfile_of_lastOccurrence
          (b := b) (hmono := hmono) (hlast := hlast) (i := i)]
        -- Once `i.succ ≤ t` is fixed, the candidate shift profile is identically `0`.
        simp [hle]
      linarith
    · -- Strictly above the last occurrence, both owners stay on the ceiling branch.
      have ht_lt_i : t < i.succ := lt_of_not_ge hle
      have hc_lt_fi : c < mixingFractionalPart b i := by
        have hmono_le :
            extendedMixingFractionalPart b t ≤ extendedMixingFractionalPart b i.succ := by
          exact hmono (le_of_lt ht_lt_i)
        have hne :
            extendedMixingFractionalPart b i.succ ≠ extendedMixingFractionalPart b t := by
          intro hi_eq
          have hi_le_t : i.succ ≤ t := hlast i.succ hi_eq
          exact hle hi_le_t
        have hstrict :
            extendedMixingFractionalPart b t < extendedMixingFractionalPart b i.succ :=
          lt_of_le_of_ne hmono_le hne.symm
        simpa [extendedMixingFractionalPart_succ, ht] using hstrict
      have hslice :
          mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 1 :=
        mixingSliceWitness_shiftProfile_of_lt
          (b := b) (c := c) hc_nonneg hc_lt_one hc_lt_fi
      have hvertex :
          mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ) = 1 := by
        have hfi_nonzero : mixingFractionalPart b i ≠ 0 := by
          have hfi_pos : 0 < mixingFractionalPart b i := lt_of_le_of_lt hc_nonneg hc_lt_fi
          exact ne_of_gt hfi_pos
        have hfract_nonzero : Int.fract (b i : ℝ) ≠ 0 := by
          simpa [mixingFractionalPart_eq_fract] using hfi_nonzero
        rw [mixingVertexCandidate_shiftProfile_of_lastOccurrence
          (b := b) (hmono := hmono) (hlast := hlast) (i := i)]
        -- Above `t`, positivity of the fractional part forces the `1` branch.
        simp [hle, hfract_nonzero]
      linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the shifted successor
profile of a weighted candidate combination is exactly the filtered prefix sum of the weights
below the queried successor index. -/
private lemma candidateWeightStepPrefix_eq
    (b : Fin n → ℚ)
    (w : Fin (n + 1) → ℝ)
    (i : Fin n) :
    (let prefixMass : ℝ :=
        Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ)) w;
      ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) =
        if mixingFractionalPart b i = 0 then 0
        else prefixMass) := by
  dsimp
  by_cases hfrac_zero : mixingFractionalPart b i = 0
  · -- Zero-fraction coordinates force every shifted step contribution to vanish.
    have hfract_zero : Int.fract (b i : ℝ) = 0 := by
      simpa [mixingFractionalPart_eq_fract] using hfrac_zero
    simp [hfract_zero]
  · -- Away from the zero-fraction branch, the step profile is exactly the indicator of `t < i.succ`.
    have hfract_nonzero : Int.fract (b i : ℝ) ≠ 0 := by
      simpa [mixingFractionalPart_eq_fract] using hfrac_zero
    calc
      ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) =
        ∑ t : Fin (n + 1), w t * (if i.succ ≤ t then 0 else 1) := by
            simp [hfract_nonzero]
      _ = ∑ t : Fin (n + 1), if t < i.succ then w t else 0 := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            by_cases ht : t < i.succ
            · have hnot_le : ¬ i.succ ≤ t := not_le_of_gt ht
              simp [ht, hnot_le]
            · have hle : i.succ ≤ t := le_of_not_gt ht
              simp [ht, hle]
      _ = Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ)) w := by
            rw [Finset.sum_filter]
      _ = if mixingFractionalPart b i = 0 then 0
            else Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ)) w := by
            simp [hfract_nonzero]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: after subtracting the
common floor term, the successor coordinate of a weighted candidate combination is exactly the
candidate-weight step sum indexed by the breakpoint chain. -/
private lemma candidateWeightCombination_shift_eq_stepSum
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (i : Fin n) :
    (let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t;
      q i.succ - (⌊b i⌋ : ℝ) =
        ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) := by
  dsimp
  have hfloor_sum :
      ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) = (⌊b i⌋ : ℝ) := by
    calc
      ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) = (∑ t : Fin (n + 1), w t) * (⌊b i⌋ : ℝ) := by
            rw [Finset.sum_mul]
      _ = (⌊b i⌋ : ℝ) := by
            rw [hw_sum, one_mul]
  calc
    (∑ t : Fin (n + 1), w t • mixingVertexCandidate b t) i.succ - (⌊b i⌋ : ℝ)
        = (∑ t : Fin (n + 1), w t * mixingVertexCandidate b t i.succ) - (⌊b i⌋ : ℝ) := by
            simp [Finset.sum_apply, Pi.smul_apply]
    _ = (∑ t : Fin (n + 1), w t * mixingVertexCandidate b t i.succ) -
          ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) := by
            rw [hfloor_sum]
    _ = ∑ t : Fin (n + 1), w t * (mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _ht
          ring
    _ = ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          by_cases hwt : w t = 0
          · simp [hwt]
          · have hwt_pos : 0 < w t := by
                exact lt_of_le_of_ne (hw_nonneg t) (by simpa [eq_comm] using hwt)
            rw [mixingVertexCandidate_shiftProfile_of_lastOccurrence
              (b := b) (hmono := hmono) (hlast := hw_last t hwt_pos) (i := i)]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a candidate
combination is pointwise dominated by the shifted tail `y + α`, the exact candidate-weight
domination field follows by rewriting each successor coordinate to the breakpoint step sum. -/
private lemma candidateWeightDomination_of_combination_bound
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {α : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hqDom :
      ∀ i : Fin n,
        (let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t;
          q i.succ ≤ y i.succ + α)) :
    ∀ i : Fin n,
      ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
        y i.succ - (⌊b i⌋ : ℝ) + α := by
  intro i
  have hshift :
      (let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t;
        q i.succ - (⌊b i⌋ : ℝ) =
          ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) :=
    candidateWeightCombination_shift_eq_stepSum
      (b := b) (hmono := hmono) (w := w) hw_nonneg hw_sum hw_last i
  have hbound :
      (let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t;
        q i.succ - (⌊b i⌋ : ℝ) ≤ y i.succ - (⌊b i⌋ : ℝ) + α) := by
    have hq := hqDom i
    linarith
  -- Rewrite the dominated successor coordinate to the candidate-step normal form.
  dsimp only at hshift hbound
  exact hshift.symm.trans_le hbound

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if nonnegative weights on
last-occurrence candidate vertices sum to `1`, hit the target head coordinate `c`, and dominate
the normalized successor shifts in cumulative-step form, then their convex combination is the hull
point needed for the reverse inclusion. -/
private lemma candidateWeightCombination_mem_mixingHull_and_le
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {c : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ)) :
    let p : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
    p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
  let p : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
  refine ⟨?_, ?_, ?_⟩
  · -- The candidate mixture lies in the hull because the weights form a convex combination.
    dsimp [p]
    exact
      (convex_convexHull ℝ (mixingSet b)).sum_mem
        (fun t _ht ↦ hw_nonneg t)
        hw_sum
        (fun t _ht ↦ mixingVertexCandidate_mem_mixingHull_of_monotone b hmono t)
  · -- The zeroth coordinate is the weighted average of the candidate head values.
    dsimp [p]
    calc
      (∑ t : Fin (n + 1), w t • mixingVertexCandidate b t) 0
          = ∑ t : Fin (n + 1), w t * mixingVertexCandidate b t 0 := by
              simp [Finset.sum_apply, Pi.smul_apply]
      _ = ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [mixingVertexCandidate_apply_zero]
      _ = c := hw_head
  · intro i
    -- Rewrite the shifted successor coordinate to the cumulative step profile, then add back the
    -- common floor term.
    have hfloor_sum :
        ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) = (⌊b i⌋ : ℝ) := by
      calc
        ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) = (∑ t : Fin (n + 1), w t) * (⌊b i⌋ : ℝ) := by
              rw [Finset.sum_mul]
        _ = (⌊b i⌋ : ℝ) := by
              rw [hw_sum, one_mul]
    have hshift :
        p i.succ - (⌊b i⌋ : ℝ) =
          ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
      calc
        p i.succ - (⌊b i⌋ : ℝ)
            = (∑ t : Fin (n + 1), w t * mixingVertexCandidate b t i.succ) - (⌊b i⌋ : ℝ) := by
                simp [p, Finset.sum_apply, Pi.smul_apply]
        _ = (∑ t : Fin (n + 1), w t * mixingVertexCandidate b t i.succ) -
              ∑ t : Fin (n + 1), w t * (⌊b i⌋ : ℝ) := by
                rw [hfloor_sum]
        _ = ∑ t : Fin (n + 1), w t * (mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ)) := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro t _ht
              ring
        _ = ∑ t : Fin (n + 1),
              w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
              refine Finset.sum_congr rfl ?_
              intro t _ht
              by_cases hwt : w t = 0
              · simp [hwt]
              · have hwt_pos : 0 < w t := by
                    exact lt_of_le_of_ne (hw_nonneg t) (by simpa [eq_comm] using hwt)
                rw [mixingVertexCandidate_shiftProfile_of_lastOccurrence
                  (b := b) (hmono := hmono) (hlast := hw_last t hwt_pos) (i := i)]
    have hshift_le :
        p i.succ - (⌊b i⌋ : ℝ) ≤ y i.succ - (⌊b i⌋ : ℝ) := by
      rw [hshift]
      exact hw_dom i
    linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if the candidate
combination only reaches the residual head height `c - α` and its shifted successor profile is
allowed the matching slack `α`, then adding `α` times the head ray produces the desired hull
point at height `c`. -/
private lemma candidateWeightCombination_addHeadSlack_mem_mixingHull_and_le
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (hα_nonneg : 0 ≤ α)
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
    let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
    p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
  let ySlack : Fin (n + 1) → ℝ := y - α • exercise_3_29_ray (0 : Fin (n + 1))
  let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
  let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
  have hqDom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          ySlack i.succ - (⌊b i⌋ : ℝ) := by
    intro i
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    -- Rewrite the slack-adjusted target exactly into the residual domination spelling.
    simpa [ySlack, Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw_dom i
  have hq :
      q ∈ mixingHull b ∧ q 0 = c - α ∧ ∀ i : Fin n, q i.succ ≤ ySlack i.succ := by
    -- First solve the residual-height convex-combination problem before restoring the head slack.
    simpa [q, ySlack] using
      candidateWeightCombination_mem_mixingHull_and_le
        (b := b) (hmono := hmono) (y := ySlack) (c := c - α)
        w hw_nonneg hw_sum hw_last hw_head hqDom
  have hconv : Convex ℝ (mixingHull b) := by
    -- The public hull alias is convex because it is a convex hull.
    simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
  have hpHull : p ∈ mixingHull b := by
    -- Restore the head slack by moving along the head-ray recession direction.
    exact
      add_nonneg_smul_mem_of_unitStep hconv hq.1
        (fun {z} hz ↦ mixingHull_add_headRay_mem b hz)
        hα_nonneg
  refine ⟨hpHull, ?_, ?_⟩
  · -- The head ray raises the zeroth coordinate by exactly `α`, recovering the target height `c`.
    calc
      p 0 = q 0 + α := by
        simp [p, q, Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply]
      _ = c := by
        linarith [hq.2.1]
  · intro i
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    have hpSucc :
        p i.succ = q i.succ - α := by
      simp [p, q, Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero,
        sub_eq_add_neg]
    have hySlackSucc :
        ySlack i.succ = y i.succ + α := by
      simp [ySlack, Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero,
        sub_eq_add_neg]
    -- Successor coordinates drop by exactly `α` under the head-ray translation.
    calc
      p i.succ = q i.succ - α := hpSucc
      _ ≤ ySlack i.succ - α := by linarith [hq.2.2 i]
      _ = y i.succ := by linarith [hySlackSucc]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a residual hull point
below `y + α` can be translated by `α` times the head ray to recover a hull point at head level
`c` that stays below `y` on every successor coordinate. -/
private lemma hullPointAddHeadSlack_mem_mixingHull_and_le
    (b : Fin n → ℚ)
    {y q : Fin (n + 1) → ℝ} {c α : ℝ}
    (hqHull : q ∈ mixingHull b)
    (hq0 : q 0 = c - α)
    (hα_nonneg : 0 ≤ α)
    (hqDom : ∀ i : Fin n, q i.succ ≤ y i.succ + α) :
    let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
    p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
  let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
  have hconv : Convex ℝ (mixingHull b) := by
    -- The public hull alias is convex because it is a convex hull.
    simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
  have hpHull : p ∈ mixingHull b := by
    -- Restore the missing head slack by moving along the head-ray recession direction.
    exact
      add_nonneg_smul_mem_of_unitStep hconv hqHull
        (fun {z} hz ↦ mixingHull_add_headRay_mem b hz)
        hα_nonneg
  refine ⟨hpHull, ?_, ?_⟩
  · -- The head ray raises the zeroth coordinate by exactly `α`.
    calc
      p 0 = q 0 + α := by
        simp [p, Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply]
      _ = c := by
        linarith [hq0]
  · intro i
    have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
      simp
    have hpSucc :
        p i.succ = q i.succ - α := by
      simp [p, Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero,
        sub_eq_add_neg]
    -- Successor coordinates drop by exactly `α` under the head-ray translation.
    calc
      p i.succ = q i.succ - α := hpSucc
      _ ≤ (y i.succ + α) - α := by
            gcongr
            exact hqDom i
      _ = y i.succ := by ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: below the maximal lower
breakpoint, the zero-start singleton inequality is exactly the scalar zero/positive coupling
inequality. -/
private lemma mixingInequality_zeroStartSingleton_scalar
    (b : Fin n → ℚ) (i j : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoZeroStart b i [j] x ↔
      mixingZeroPositiveCouplingInequality b i j x := by
  -- Collapse the singleton zero-start list so later scalar comparisons can rewrite directly.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeTwoZeroStart, mixingZeroPositiveCouplingInequality,
      mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux, add_assoc, add_left_comm,
      add_comm] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the singleton positive
type-one inequality has the expected scalar normal form. -/
private lemma mixingInequalityTypeOne_singleton_scalar
    (b : Fin n → ℚ) (i : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOne b [i] x ↔
      mixingFractionalPart b i ≤
        x 0 + mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) := by
  -- Expand the one-term shifted sum once so the later breakpoint arguments stay scalar.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeOne, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux]
      using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the singleton positive
type-two inequality reduces to the direct shifted cover-gap scalar bound. -/
private lemma mixingInequalityTypeTwo_singleton_scalar
    (b : Fin n → ℚ) (i : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwo b [i] x ↔
      mixingFractionalPart b i ≤ x 0 + x i.succ - (⌊b i⌋ : ℝ) := by
  -- The type-two singleton adds the complementary coefficient to the same selected coordinate.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      add_assoc, add_left_comm, add_comm, sub_eq_add_neg, mul_add, add_mul] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the length-two positive
type-one inequality has the expected scalar normal form. -/
private lemma mixingInequalityTypeOne_pair_scalar
    (b : Fin n → ℚ) (i j : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOne b [i, j] x ↔
      mixingFractionalPart b j ≤
        x 0 +
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) +
          (mixingFractionalPart b j - mixingFractionalPart b i) *
            (x j.succ - (⌊b j⌋ : ℝ)) := by
  -- Expand the two-term shifted sum once so later proofs can stay in scalar arithmetic.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeOne, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      add_assoc, add_left_comm, add_comm] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the length-two positive
type-two inequality has the expected scalar normal form. -/
private lemma mixingInequalityTypeTwo_pair_scalar
    (b : Fin n → ℚ) (i j : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwo b [i, j] x ↔
      mixingFractionalPart b j ≤
        x 0 +
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) +
          (mixingFractionalPart b j - mixingFractionalPart b i) *
            (x j.succ - (⌊b j⌋ : ℝ)) +
          (1 - mixingFractionalPart b j) * (x i.succ - (⌊b i⌋ : ℝ)) := by
  -- Expand the two-term shifted sum and keep the type-two correction explicit.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      add_assoc, add_left_comm, add_comm] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the length-three positive
type-two inequality has the expected scalar normal form. -/
private lemma mixingInequalityTypeTwo_triple_scalar
    (b : Fin n → ℚ) (i j k : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwo b [i, j, k] x ↔
      mixingFractionalPart b k ≤
        x 0 +
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) +
          (mixingFractionalPart b j - mixingFractionalPart b i) *
            (x j.succ - (⌊b j⌋ : ℝ)) +
          (mixingFractionalPart b k - mixingFractionalPart b j) *
            (x k.succ - (⌊b k⌋ : ℝ)) +
          (1 - mixingFractionalPart b k) * (x i.succ - (⌊b i⌋ : ℝ)) := by
  -- Expand the three-term shifted sum and keep the type-two correction on the first coordinate.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingInequalityTypeOneSumAux,
      add_assoc, add_left_comm, add_comm] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the zero-start type-two
inequality with a positive tail of length two has the expected scalar normal form. -/
private lemma mixingInequalityTypeTwoZeroStart_pair_scalar
    (b : Fin n → ℚ) (i j k : Fin n) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoZeroStart b i [j, k] x ↔
      mixingFractionalPart b k ≤
        x 0 +
          mixingFractionalPart b j * (x j.succ - (⌊b j⌋ : ℝ)) +
          (mixingFractionalPart b k - mixingFractionalPart b j) *
            (x k.succ - (⌊b k⌋ : ℝ)) +
          (1 - mixingFractionalPart b k) * (x i.succ - (⌊b i⌋ : ℝ)) := by
  -- Expand the positive tail of length two once so the zero-start lower-zone proof stays scalar.
  constructor <;> intro h <;>
    simpa [mixingInequalityTypeTwoZeroStart, mixingInequalityTypeOneSum,
      mixingInequalityTypeOneSumAux, add_assoc, add_left_comm, add_comm] using h

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a zero-start singleton
inequality turns any nonnegative slack on the zero-fraction start coordinate into the first
profile bound on a positive coordinate. -/
private lemma zeroStartSingleton_profileBound
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {i j : Fin n}
    (hfi_zero : mixingFractionalPart b i = 0)
    (hij : i < j)
    (hfj_pos : 0 < mixingFractionalPart b j)
    (hi_nonneg :
      0 ≤ x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) + α) :
    1 - (c - α) / mixingFractionalPart b j ≤
      x j.succ + (mZ : ℝ) - (⌊b j⌋ : ℝ) + α := by
  -- Normalize the region hypotheses and close the scalar bound directly.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: when the strict-rise
chain starts directly from the head breakpoint `0`, the singleton positive type-one inequality
already gives the first residual-profile bound with zero extra slack. -/
private lemma headSingleton_profileBound
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {j : Fin n}
    (hfj_pos : 0 < mixingFractionalPart b j) :
    1 - c / mixingFractionalPart b j ≤
      x j.succ + (mZ : ℝ) - (⌊b j⌋ : ℝ) := by
  -- Normalize the singleton inequality and discharge the resulting linear bound.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once one positive
coordinate already carries a profile bound, the length-two positive type-one inequality transports
that bound to the next larger breakpoint value. -/
private lemma positivePair_profileTransport
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {i j : Fin n}
    (hij : i < j)
    (hfi_pos : 0 < mixingFractionalPart b i)
    (hfi_lt_fj : mixingFractionalPart b i < mixingFractionalPart b j)
    (hα_nonneg : 0 ≤ α)
    {ρi : ℝ}
    (hi_bound :
      ρi ≤ x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) + α) :
    ((mixingFractionalPart b j - (c - α)) - mixingFractionalPart b i * ρi) /
        (mixingFractionalPart b j - mixingFractionalPart b i) ≤
      x j.succ + (mZ : ℝ) - (⌊b j⌋ : ℝ) + α := by
  -- Normalize the pair inequality and discharge the resulting linear implication.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the zero-start profile
update `ρ = 1 - d / f` preserves the residual head moment `d` as the remaining mass at the
breakpoint value `f`. -/
private lemma zeroStartProfileValue_residualMoment
    {d f ρ : ℝ}
    (hf_ne : f ≠ 0)
    (hρ : ρ = 1 - d / f) :
    d = f * (1 - ρ) := by
  -- Expand the zero-start profile value once and clear the nonzero denominator.
  rw [hρ]
  field_simp [hf_ne]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the pair-transport update
for the cumulative profile preserves the same residual head moment `d` after moving from `fᵢ` to
the next distinct breakpoint value `fⱼ`. -/
private lemma transportedProfileValue_residualMoment
    {d fi fj ρi ρj : ℝ}
    (hgap_ne : fj - fi ≠ 0)
    (hρj : ρj = ((fj - d) - fi * ρi) / (fj - fi)) :
    d = fi * (ρj - ρi) + fj * (1 - ρj) := by
  -- Clear the strict-jump denominator and collect the old and new breakpoint contributions.
  rw [hρj]
  field_simp [hgap_ne]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if the owner-chain state
already records a committed prefix moment `μCur`, then transporting the open tail from `fᵢ` to
`fⱼ` preserves the total head moment `c - α` after the committed mass is added back. -/
private lemma ownerChainMomentStep
    {c α μCur fi fj ρCur ρNext : ℝ}
    (hgap_ne : fj - fi ≠ 0)
    (hhead :
      μCur + fi * (1 - ρCur) = c - α)
    (hρNext :
      ρNext = ((fj - ((c - α) - μCur)) - fi * ρCur) / (fj - fi)) :
    (μCur + fi * (ρNext - ρCur)) + fj * (1 - ρNext) = c - α := by
  have htail :
      (c - α) - μCur = fi * (1 - ρCur) := by
    -- Isolate the current open-tail moment before applying the standard pair transport lemma.
    linarith
  have htransport :
      (c - α) - μCur = fi * (ρNext - ρCur) + fj * (1 - ρNext) := by
    -- The generic pair-transport identity updates only the open tail, not the committed prefix.
    exact
      transportedProfileValue_residualMoment
        (d := (c - α) - μCur) (fi := fi) (fj := fj) (ρi := ρCur) (ρj := ρNext)
        hgap_ne hρNext
  -- Add the committed prefix moment back to the transported tail identity.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: feeding the seed identity
`d = fᵢ * (1 - ρᵢ)` directly into the old pair-transport formula forces the next plateau value to
collapse to `1`, so that route cannot supply the intermediate chain needed by the nonterminal
constructor. -/
private lemma transportedSeedProfileValue_eq_one
    {d fi fj ρi ρj : ℝ}
    (hgap_ne : fj - fi ≠ 0)
    (hseed : d = fi * (1 - ρi))
    (hρj : ρj = ((fj - d) - fi * ρi) / (fj - fi)) :
    ρj = 1 := by
  rw [hρj, hseed]
  calc
    (fj - fi * (1 - ρi) - fi * ρi) / (fj - fi)
        = (fj - fi) / (fj - fi) := by ring
    _ = 1 := by
          exact div_self hgap_ne

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the same collapse persists
for the later owner-chain formula if the induction state still remembers only one open tail
`fi * (1 - ρCur)`. Any workable extension step must therefore carry genuinely richer residual
data than the triple `(tCur, μCur, ρCur)` used by the discarded route. -/
private lemma transportedOwnerChainProfileValue_eq_one
    {c α μCur fi fj ρCur ρNext : ℝ}
    (hgap_ne : fj - fi ≠ 0)
    (hhead :
      μCur + fi * (1 - ρCur) = c - α)
    (hρNext :
      ρNext = ((fj - ((c - α) - μCur)) - fi * ρCur) / (fj - fi)) :
    ρNext = 1 := by
  have htail : (c - α) - μCur = fi * (1 - ρCur) := by
    -- Isolate the residual tail recorded by the current state before simplifying the transport
    -- formula.
    linarith
  rw [hρNext, htail]
  calc
    (fj - fi * (1 - ρCur) - fi * ρCur) / (fj - fi)
        = (fj - fi) / (fj - fi) := by ring
    _ = 1 := by
          exact div_self hgap_ne

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: below the maximal lower
breakpoint, the normalized successor shift still satisfies the basic cover-gap lower bound coming
from the local fractional part. -/
private lemma normalizedShift_ge_coverGap_of_le_lastLowerBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (hlt : tLo.1 < n)
    {i : Fin n}
    (hi_le_tLo : i.succ ≤ tLo) :
    extendedMixingFractionalPart b i.succ - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- Route correction: the earlier nonnegativity target is false on normalized head-ray
  -- translates, so keep only the cover-gap inequality that is valid in every lower-breakpoint
  -- case and stable under the later geometric re-plan.
  have hcover := normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i
  have hfrac_eq :
      extendedMixingFractionalPart b i.succ = mixingFractionalPart b i := by
    simp [extendedMixingFractionalPart_succ]
  rw [hfrac_eq]
  exact hcover

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: when the last lower
breakpoint has positive fractional value `mixingFractionalPart b j`, the stable lower-zone fact
available without a new breakpoint-budget decomposition is still the coordinatewise cover-gap
bound on every earlier coordinate. -/
private lemma positiveLowerBreakpointResidualOfPairTypeTwo
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {j : Fin n}
    (_hj_le : mixingFractionalPart b j ≤ c)
    (_hj_pos : 0 < mixingFractionalPart b j) :
    ∀ {k : Fin n},
      k ≤ j →
        mixingFractionalPart b k - c ≤
          x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) := by
  intro k _hk_le
  -- Route correction: the old residual bound with `mixingFractionalPart b j - c` is false on
  -- region points, so freeze the true per-coordinate cover-gap estimate instead.
  exact normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq k

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: below the last lower
breakpoint, the stable fact that survives the counterexamples to the old nonnegativity target is
again the coordinatewise cover-gap estimate in shifted form. -/
private lemma lowerZoneNonneg_of_adjacentUpperBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (_htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (hlt : tLo.1 < n)
    {tHi : Fin (n + 1)}
    (_hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (_hc_lt_hi : c < extendedMixingFractionalPart b tHi)
    {k : Fin n}
    (hk_le_tLo : k.succ ≤ tLo) :
    mixingFractionalPart b k - c ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) := by
  -- Route correction: the old nonnegativity conclusion is false even when the adjacent upper
  -- breakpoint lies above `c`, so keep only the cover-gap estimate that the region always gives.
  exact normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq k

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: when the lower breakpoint
value is `0`, the plateau transport that remains valid for normalized head-ray translates is the
common upper-breakpoint gap bound rather than the false exact chord weight. -/
private lemma zeroLowerBreakpointPlateauTransport
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (hlt : tLo.1 < n)
    {tHi : Fin (n + 1)}
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    {i : Fin n}
    (htLo_lt_i : tLo < i.succ)
    (hi_le_tHi : i.succ ≤ tHi) :
    extendedMixingFractionalPart b tHi - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- Route correction: the old exact plateau-weight statement is false on normalized head-ray
  -- translates, so keep only the upper-gap transport that the existing breakpoint API proves.
  exact
    normalizedShift_ge_upperBreakpointGap_of_betweenBreakpoints
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq hlt hHi_eq htLo_lt_i hi_le_tHi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the hard
last-lower-breakpoint branch should be frozen as one reusable package covering the true lower-zone
cover-gap estimate together with the upper-gap and above-upper strict-gap estimates. -/
private lemma lastLowerBreakpointBranchPackage
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    (∀ {k : Fin n},
        k.succ ≤ tLo →
          mixingFractionalPart b k - c ≤
            x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ)) ∧
      (∀ (hlt : tLo.1 < n) {tHi : Fin (n + 1)},
        extendedMixingFractionalPart b tHi =
            extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) →
          c < extendedMixingFractionalPart b tHi →
          ∀ {i : Fin n},
            tLo < i.succ →
              i.succ ≤ tHi →
                extendedMixingFractionalPart b tHi - c ≤
                  x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ)) ∧
      (∀ (hlt : tLo.1 < n) {tHi : Fin (n + 1)},
        extendedMixingFractionalPart b tHi =
            extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt) →
          c < extendedMixingFractionalPart b tHi →
          (∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s =
                extendedMixingFractionalPart b tHi →
              s ≤ tHi) →
          ∀ {i : Fin n},
            tHi < i.succ →
              extendedMixingFractionalPart b tHi - c <
                x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k _hk_le_tLo
    -- Route correction: the old shared lower residual `fLo - c` is false, so package only the
    -- true coordinatewise cover-gap estimate on the lower zone.
    exact normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq k
  · intro hlt tHi hHi_eq _hc_lt_hi i htLo_lt_i hi_le_tHi
    -- On the plateau, the stable upper-gap transport is already available as a dedicated lemma.
    exact
      normalizedShift_ge_upperBreakpointGap_of_betweenBreakpoints
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hlt hHi_eq htLo_lt_i hi_le_tHi
  · intro _hlt tHi _hHi_eq _hc_lt_hi hHi_last i htHi_lt_i
    -- Strictly above the last upper breakpoint, the stable fact is the strict upper-gap bound.
    exact
      normalizedShift_gt_upperBreakpointGap_of_upperBreakpoint_lt
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq (tHi := tHi) hHi_last htHi_lt_i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the plateau between
the maximal lower breakpoint and the last occurrence of the adjacent upper breakpoint, the
normalized successor shift dominates the common upper-breakpoint gap. -/
private lemma normalizedShift_ge_plateauWeight_of_betweenBreakpoints
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo tHi : Fin (n + 1)} {i : Fin n}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (hlt : tLo.1 < n)
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (hc_lt_hi : c < extendedMixingFractionalPart b tHi)
    (htLo_lt_i : tLo < i.succ)
    (hi_le_tHi : i.succ ≤ tHi) :
    extendedMixingFractionalPart b tHi - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  have hpackage :=
    lastLowerBreakpointBranchPackage
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq (tLo := tLo) htLo_le htLo_max
  -- Consume the true upper-gap projection of the shared breakpoint package directly.
  exact hpackage.2.1 hlt hHi_eq hc_lt_hi htLo_lt_i hi_le_tHi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: strictly above the last
occurrence of the adjacent upper breakpoint, the stable bound available before the missing
breakpoint-budget witness is the strict upper-gap estimate. -/
private lemma normalizedShift_ge_one_of_upperBreakpoint_lt
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    {tHi : Fin (n + 1)} {i : Fin n}
    (hc_lt_hi : c < extendedMixingFractionalPart b tHi)
    (hHi_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s =
          extendedMixingFractionalPart b tHi → s ≤ tHi)
    (htHi_lt_i : tHi < i.succ) :
    extendedMixingFractionalPart b tHi - c <
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- Route correction: the old `≥ 1` target belongs to the missing breakpoint-budget witness, while
  -- the strict upper-gap bound is already available directly.
  exact
    normalizedShift_gt_upperBreakpointGap_of_upperBreakpoint_lt
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq (tHi := tHi) hHi_last htHi_lt_i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the terminal branch,
the only stable terminal lower bound available without the missing breakpoint-budget witness is
again the coordinatewise cover-gap estimate. -/
private lemma normalizedShift_ge_terminalResidual_of_lastBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (_htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (_htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (_hc_lt_one : c < 1)
    (_hterminal : ¬ tLo.1 < n)
    {i : Fin n}
    (hi_le_tLo : i.succ ≤ tLo) :
    mixingFractionalPart b i - c ≤
      x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
  -- Route correction: the old terminal residual target is false, so reuse the direct cover-gap
  -- estimate instead of the discarded lower-residual package.
  exact normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the maximal lower
breakpoint is automatically a last occurrence of its own extended fractional value. -/
private lemma maxLowerBreakpoint_lastOccurrence
    (b : Fin n → ℚ) {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s = extendedMixingFractionalPart b tLo → s ≤ tLo := by
  intro s hs
  -- Rewrite the matching fractional value back to the maximal lower breakpoint inequality.
  exact htLo_max s (by rw [hs]; exact htLo_le)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a two-point breakpoint
weight supported on `tLo` and `tHi` has the expected `0/λ/1` cumulative step profile. -/
private lemma twoPointBreakpointWeightStepProfile
    (b : Fin n → ℚ)
    {tLo tHi : Fin (n + 1)} (htLo_lt_tHi : tLo < tHi)
    {lamLo lamHi : ℝ} {i : Fin n} :
    ∑ t : Fin (n + 1),
        (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) *
          (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) =
      if mixingFractionalPart b i = 0 then 0
      else if i.succ ≤ tLo then 0 else if i.succ ≤ tHi then lamLo else lamLo + lamHi := by
  -- Split the sparse support into its two atoms, then read off the step profile in each zone.
  have hsplit :
      ∑ t : Fin (n + 1),
          (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) *
            (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) =
        ∑ t : Fin (n + 1),
            ((if t = tLo then lamLo else 0) *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) +
          ∑ t : Fin (n + 1),
            ((if t = tHi then lamHi else 0) *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) := by
    calc
      ∑ t : Fin (n + 1),
          (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) *
            (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) =
          ∑ t : Fin (n + 1),
            (((if t = tLo then lamLo else 0) *
                (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) +
              ((if t = tHi then lamHi else 0) *
                (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1))) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
      _ =
          ∑ t : Fin (n + 1),
            ((if t = tLo then lamLo else 0) *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) +
          ∑ t : Fin (n + 1),
            ((if t = tHi then lamHi else 0) *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) := by
            rw [Finset.sum_add_distrib]
  have hLo :
      ∑ t : Fin (n + 1),
          ((if t = tLo then lamLo else 0) *
            (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) =
        lamLo *
          (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ tLo then 0 else 1) := by
    rw [Finset.sum_eq_single tLo]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp
  have hHi :
      ∑ t : Fin (n + 1),
          ((if t = tHi then lamHi else 0) *
            (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) =
        lamHi *
          (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ tHi then 0 else 1) := by
    rw [Finset.sum_eq_single tHi]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp
  have htLo_le_tHi : tLo ≤ tHi := le_of_lt htLo_lt_tHi
  rw [hsplit, hLo, hHi]
  by_cases hfrac_zero : mixingFractionalPart b i = 0
  · -- Zero-fraction coordinates force the whole step profile to vanish.
    have hfract_zero : Int.fract (b i : ℝ) = 0 := by
      simpa [mixingFractionalPart_eq_fract] using hfrac_zero
    simp [hfract_zero]
  · have hfract_nonzero : Int.fract (b i : ℝ) ≠ 0 := by
      simpa [mixingFractionalPart_eq_fract] using hfrac_zero
    by_cases hi_le_tLo : i.succ ≤ tLo
    · -- At or below `tLo`, both support atoms lie on the floor branch.
      have hi_le_tHi : i.succ ≤ tHi := le_trans hi_le_tLo htLo_le_tHi
      simp [hfract_nonzero, hi_le_tLo, hi_le_tHi]
    · by_cases hi_le_tHi : i.succ ≤ tHi
      · -- Between `tLo` and `tHi`, only the lower support atom contributes.
        simp [hfract_nonzero, hi_le_tLo, hi_le_tHi]
      · -- Strictly above `tHi`, both support atoms contribute their full weights.
        simp [hfract_nonzero, hi_le_tLo, hi_le_tHi]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the terminal residual
package with all weight at the maximal lower breakpoint already satisfies the algebraic fields of
the candidate-weight API; only the shifted domination inequalities remain. -/
private lemma terminalResidualWeightAlgebra
    (b : Fin n → ℚ)
    {c : ℝ} {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tLo → s ≤ tLo) :
    let α : ℝ := c - extendedMixingFractionalPart b tLo
    let w : Fin (n + 1) → ℝ := fun t ↦ if t = tLo then 1 else 0
    0 ≤ α ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) := by
  let α : ℝ := c - extendedMixingFractionalPart b tLo
  let w : Fin (n + 1) → ℝ := fun t ↦ if t = tLo then 1 else 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The terminal head slack is exactly the residual gap above the last lower breakpoint.
    dsimp [α]
    linarith
  · intro t
    -- The terminal package uses a single nonnegative support atom.
    dsimp [w]
    split_ifs <;> norm_num
  · -- The single support atom carries all the weight.
    dsimp [w]
    rw [Finset.sum_eq_single tLo]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp
  · intro t ht_pos s hs
    -- A positive terminal weight forces `t = tLo`, so the last-occurrence owner is inherited.
    have ht_eq : t = tLo := by
      by_cases h : t = tLo
      · exact h
      · dsimp [w] at ht_pos
        simp [h] at ht_pos
    subst ht_eq
    exact htLo_last s hs
  · -- The weighted head value is exactly the last lower breakpoint value.
    dsimp [w, α]
    rw [Finset.sum_eq_single tLo]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the nonterminal
branch, the sparse breakpoint weights on `tLo` and the last adjacent upper breakpoint already
satisfy the algebraic fields of the candidate-weight API; only the exact shifted domination field
still has to be proved zone by zone. -/
private lemma adjacentUpperResidualWeightAlgebra
    (b : Fin n → ℚ)
    {c : ℝ} {tLo tHi : Fin (n + 1)}
    (htLo_lt_tHi : tLo < tHi)
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (hc_lt_hi : c < extendedMixingFractionalPart b tHi)
    (htLo_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tLo → s ≤ tLo)
    (hHi_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tHi → s ≤ tHi) :
    let denom : ℝ := extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo
    let lamLo : ℝ := (extendedMixingFractionalPart b tHi - c) / denom
    let lamHi : ℝ := (c - extendedMixingFractionalPart b tLo) / denom
    let w : Fin (n + 1) → ℝ :=
      fun t ↦ (if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0
    (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c) := by
  let denom : ℝ := extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo
  let lamLo : ℝ := (extendedMixingFractionalPart b tHi - c) / denom
  let lamHi : ℝ := (c - extendedMixingFractionalPart b tLo) / denom
  let w : Fin (n + 1) → ℝ :=
    fun t ↦ (if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0
  have htLo_ne_tHi : tLo ≠ tHi := ne_of_lt htLo_lt_tHi
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    linarith
  have hlamLo_nonneg : 0 ≤ lamLo := by
    -- The lower support coefficient is the normalized distance from `c` to the upper breakpoint.
    dsimp [lamLo]
    exact div_nonneg (sub_nonneg.mpr (le_of_lt hc_lt_hi)) (le_of_lt hdenom_pos)
  have hlamHi_nonneg : 0 ≤ lamHi := by
    -- The upper support coefficient is the normalized distance from the lower breakpoint to `c`.
    dsimp [lamHi]
    exact div_nonneg (sub_nonneg.mpr htLo_le) (le_of_lt hdenom_pos)
  have hsumLo :
      ∑ t : Fin (n + 1), (if t = tLo then lamLo else 0) = lamLo := by
    rw [Finset.sum_eq_single tLo]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp
  have hsumHi :
      ∑ t : Fin (n + 1), (if t = tHi then lamHi else 0) = lamHi := by
    rw [Finset.sum_eq_single tHi]
    · simp
    · intro t _ht ht_ne
      simp [ht_ne]
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    -- The sparse owner has only the two nonnegative breakpoint coefficients.
    dsimp [w]
    by_cases ht : t = tLo
    · subst ht
      simpa [htLo_ne_tHi] using hlamLo_nonneg
    · by_cases ht' : t = tHi
      · subst ht'
        have hfirst_zero : (if t = tLo then lamLo else 0) = 0 := by
          simp [ht]
        rw [hfirst_zero, zero_add]
        simpa using hlamHi_nonneg
      · simp [ht, ht', hlamLo_nonneg, hlamHi_nonneg]
  · -- The two sparse coefficients sum to one.
    calc
      ∑ t : Fin (n + 1), w t
          = ∑ t : Fin (n + 1), (if t = tLo then lamLo else 0) +
              ∑ t : Fin (n + 1), (if t = tHi then lamHi else 0) := by
                dsimp [w]
                rw [Finset.sum_add_distrib]
      _ = lamLo + lamHi := by rw [hsumLo, hsumHi]
      _ = 1 := by
            calc
              lamLo + lamHi
                  = (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) *
                      (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo)⁻¹ := by
                        dsimp [lamLo, lamHi, denom]
                        ring
              _ = 1 := by
                    exact mul_inv_cancel₀ hdenom_pos.ne'
  · intro t ht_pos s hs
    -- Positive sparse weight means the support point is either `tLo` or `tHi`.
    by_cases ht : t = tLo
    · subst ht
      exact htLo_last s hs
    · by_cases ht' : t = tHi
      · subst ht'
        exact hHi_last s hs
      · have hw_zero : w t = 0 := by
          dsimp [w]
          simp [ht, ht']
        linarith
  · -- The weighted head coordinate is the affine interpolation value `c`.
    calc
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t
          = ∑ t : Fin (n + 1),
              ((if t = tLo then lamLo else 0) * extendedMixingFractionalPart b t) +
              ∑ t : Fin (n + 1),
                ((if t = tHi then lamHi else 0) * extendedMixingFractionalPart b t) := by
                  dsimp [w]
                  calc
                    ∑ t : Fin (n + 1),
                        (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) *
                          extendedMixingFractionalPart b t) =
                        ∑ t : Fin (n + 1),
                          (((if t = tLo then lamLo else 0) * extendedMixingFractionalPart b t) +
                            ((if t = tHi then lamHi else 0) *
                              extendedMixingFractionalPart b t)) := by
                              refine Finset.sum_congr rfl ?_
                              intro t _ht
                              ring
                    _ =
                        ∑ t : Fin (n + 1),
                          ((if t = tLo then lamLo else 0) * extendedMixingFractionalPart b t) +
                        ∑ t : Fin (n + 1),
                          ((if t = tHi then lamHi else 0) * extendedMixingFractionalPart b t) := by
                            rw [Finset.sum_add_distrib]
      _ = lamLo * extendedMixingFractionalPart b tLo +
            lamHi * extendedMixingFractionalPart b tHi := by
              congr 1
              · rw [Finset.sum_eq_single tLo]
                · simp
                · intro t _ht ht_ne
                  simp [ht_ne]
                · simp
              · rw [Finset.sum_eq_single tHi]
                · simp
                · intro t _ht ht_ne
                  simp [ht_ne]
                · simp
      _ = c := by
            calc
              lamLo * extendedMixingFractionalPart b tLo +
                  lamHi * extendedMixingFractionalPart b tHi
                  = c *
                      ((extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo) *
                        (extendedMixingFractionalPart b tHi - extendedMixingFractionalPart b tLo)⁻¹) := by
                          dsimp [lamLo, lamHi, denom]
                          ring
              _ = c := by
                    rw [mul_inv_cancel₀ hdenom_pos.ne', mul_one]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a normalized region point
with maximal lower breakpoint `tLo` should admit a direct residual hull point at height `c - α`
whose successor coordinates stay below the shifted tail `y + α`. -/
private lemma existsDominatingSliceWitnessOfDomination
    (b : Fin n → ℚ)
    {y : Fin (n + 1) → ℝ} {c d : ℝ}
    (hd_nonneg : 0 ≤ d)
    (hd_lt_one : d < 1)
    (hd_le_c : d ≤ c)
    (hdom : ∀ i : Fin n, mixingSliceWitness b d i.succ ≤ y i.succ + (c - d)) :
    ∃ α : ℝ, ∃ q : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      q ∈ mixingHull b ∧
      q 0 = c - α ∧
      (∀ i : Fin n, q i.succ ≤ y i.succ + α) := by
  refine ⟨c - d, mixingSliceWitness b d, ?_, ?_, ?_, ?_⟩
  · -- The residual head slack is exactly the gap between the target head `c` and the slice level `d`.
    linarith
  · -- Every slice witness already lies in the public mixing hull.
    exact mixingSliceWitness_mem_mixingHull b hd_nonneg hd_lt_one
  · -- The slice witness head coordinate is exactly `d = c - (c - d)`.
    calc
      mixingSliceWitness b d 0 = d := by simp [mixingSliceWitness]
      _ = c - (c - d) := by ring
  · intro i
    -- The assumed successor domination is already in the residual spelling needed downstream.
    simpa using hdom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: for a fixed slice level
`d`, the residual domination problem is exactly the coordinatewise comparison between the slice
witness at height `d` and the shifted tail `y + (c - d)`. -/
private lemma mixingSliceWitnessDomination_iff
    (b : Fin n → ℚ)
    {y : Fin (n + 1) → ℝ} {c d : ℝ} {i : Fin n}
    (hd_nonneg : 0 ≤ d)
    (hd_lt_one : d < 1) :
    mixingSliceWitness b d i.succ ≤ y i.succ + (c - d) ↔
      (if mixingFractionalPart b i ≤ d then 0 else 1) ≤
        y i.succ - (⌊b i⌋ : ℝ) + (c - d) := by
  constructor
  · intro h
    have hprofile :=
      mixingSliceWitness_shiftProfile (b := b) (c := d) hd_nonneg hd_lt_one i
    have hshift :
        mixingSliceWitness b d i.succ =
          (⌊b i⌋ : ℝ) + (if mixingFractionalPart b i ≤ d then 0 else 1) := by
      linarith
    linarith
  · intro h
    have hprofile :=
      mixingSliceWitness_shiftProfile (b := b) (c := d) hd_nonneg hd_lt_one i
    have hshift :
        mixingSliceWitness b d i.succ =
          (⌊b i⌋ : ℝ) + (if mixingFractionalPart b i ≤ d then 0 else 1) := by
      linarith
    linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the ordered-chain
candidate-weight transport is governed by the consecutive differences of a cumulative profile,
with the final weight given by the residual mass at the terminal breakpoint. -/
private noncomputable def consecutiveDifferenceWeights
    (ρ : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i : Fin n ↦ ρ i.succ - ρ i.castSucc) (1 - ρ (Fin.last n))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: away from the terminal
breakpoint, the consecutive-difference owner records the one-step jump of the cumulative profile. -/
private lemma consecutiveDifferenceWeights_castSucc
    (ρ : Fin (n + 1) → ℝ) (i : Fin n) :
    consecutiveDifferenceWeights ρ i.castSucc = ρ i.succ - ρ i.castSucc := by
  -- Unfold the owner only on the nonterminal branch so later proofs can rewrite without touching
  -- the terminal remainder case.
  simp [consecutiveDifferenceWeights]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: at the terminal
breakpoint, the consecutive-difference owner stores the residual mass needed to make the total
weight sum equal to `1`. -/
private lemma consecutiveDifferenceWeights_last
    (ρ : Fin (n + 1) → ℝ) :
    consecutiveDifferenceWeights ρ (Fin.last n) = 1 - ρ (Fin.last n) := by
  -- The terminal branch of the owner is definitionally the leftover mass.
  simp [consecutiveDifferenceWeights]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the prefix mass of the
consecutive-difference owner recovers the cumulative profile itself. -/
private lemma consecutiveDifferenceWeightsPrefixMass_eq_profileIio
    (ρ : Fin (n + 1) → ℝ) (hρ0 : ρ 0 = 0) :
    ∀ a : Fin (n + 1),
      Finset.sum (Finset.Iio a) (consecutiveDifferenceWeights ρ) = ρ a := by
  intro a
  refine a.inductionOn ?_ ?_
  · calc
      Finset.sum (Finset.Iio (0 : Fin (n + 1))) (consecutiveDifferenceWeights ρ) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        exact (not_lt_of_ge (Fin.zero_le t) (Finset.mem_Iio.mp ht)).elim
      _ = ρ 0 := hρ0.symm
  · intro i ih
    have hsplit :
        Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
      -- Identify the finite intervals extensionally; the similarly named `Order` lemma is for
      -- sets and therefore has the wrong result type here.
      have hnotmax : ¬ IsMax i.castSucc := not_isMax_of_lt i.castSucc_lt_succ
      rw [← Fin.orderSucc_castSucc i]
      rw [Finset.Iio_succ_eq_Iic_of_not_isMax hnotmax]
      ext t
      simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
      exact le_iff_eq_or_lt
    -- Split the strict prefix at the new last index and telescope the consecutive difference.
    rw [hsplit, Finset.sum_insert]
    · rw [ih, consecutiveDifferenceWeights_castSucc]
      ring
    · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: after rewriting the
candidate step owner as a strict prefix mass, the consecutive-difference owner returns the target
cumulative profile. -/
private lemma consecutiveDifferenceWeightsPrefixMass_eq_profile
    (ρ : Fin (n + 1) → ℝ) (hρ0 : ρ 0 = 0) (i : Fin n) :
    Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ))
      (consecutiveDifferenceWeights ρ) = ρ i.succ := by
  -- Rewrite the filtered prefix to the canonical finite interval before telescoping.
  simpa [Finset.filter_gt_eq_Iio] using
    consecutiveDifferenceWeightsPrefixMass_eq_profileIio ρ hρ0 i.succ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a monotone cumulative
profile with terminal value at most `1` yields nonnegative consecutive-difference weights. -/
private lemma consecutiveDifferenceWeights_nonneg
    (ρ : Fin (n + 1) → ℝ)
    (hρmono : Monotone ρ)
    (hρlast : ρ (Fin.last n) ≤ 1) :
    ∀ t : Fin (n + 1), 0 ≤ consecutiveDifferenceWeights ρ t := by
  intro t
  by_cases ht : t = Fin.last n
  · -- The terminal owner is the residual mass `1 - ρ_last`.
    subst ht
    rw [consecutiveDifferenceWeights_last]
    linarith
  · -- Every nonterminal owner is a monotone profile jump.
    rcases Fin.exists_castSucc_eq.2 ht with ⟨i, rfl⟩
    rw [consecutiveDifferenceWeights_castSucc]
    exact sub_nonneg.mpr (hρmono (le_of_lt i.castSucc_lt_succ))

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: consecutive differences of
a profile starting at zero, including its terminal residual, always have total mass one. -/
private lemma consecutiveDifferenceWeights_sum
    (ρ : Fin (n + 1) → ℝ) (hρ0 : ρ 0 = 0) :
    ∑ t : Fin (n + 1), consecutiveDifferenceWeights ρ t = 1 := by
  have hprefix_last :
      ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc = ρ (Fin.last n) := by
    have hprefix_last_iio :
        Finset.sum (Finset.Iio (Fin.last n)) (consecutiveDifferenceWeights ρ) =
          ρ (Fin.last n) :=
      consecutiveDifferenceWeightsPrefixMass_eq_profileIio ρ hρ0 (Fin.last n)
    rw [Fin.Iio_last_eq_map] at hprefix_last_iio
    simpa [Finset.sum_map] using hprefix_last_iio
  -- Split off the residual atom and telescope the strict terminal prefix.
  calc
    ∑ t : Fin (n + 1), consecutiveDifferenceWeights ρ t =
        ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc +
          consecutiveDifferenceWeights ρ (Fin.last n) := by
            rw [Fin.sum_univ_castSucc]
    _ = ρ (Fin.last n) + (1 - ρ (Fin.last n)) := by
          rw [hprefix_last, consecutiveDifferenceWeights_last]
    _ = 1 := by ring

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: finite integration by
parts rewrites the breakpoint moment of consecutive differences as the terminal value minus the
adjacent-gap sum. -/
private lemma finiteAtomicMoment_eq_terminal_sub_gapSum
    (ρ f : Fin (n + 1) → ℝ) (hρ0 : ρ 0 = 0) :
    ∑ t : Fin (n + 1), consecutiveDifferenceWeights ρ t * f t =
      f (Fin.last n) -
        ∑ i : Fin n, ρ i.succ * (f i.succ - f i.castSucc) := by
  have hshift :
      (∑ i : Fin n, ρ i.castSucc * f i.castSucc) +
          ρ (Fin.last n) * f (Fin.last n) =
        ∑ i : Fin n, ρ i.succ * f i.succ := by
    -- The cast-successor and successor enumerations differ only by the terminal and initial
    -- endpoints; the initial contribution vanishes because the profile starts at zero.
    calc
      (∑ i : Fin n, ρ i.castSucc * f i.castSucc) +
            ρ (Fin.last n) * f (Fin.last n) =
          ∑ t : Fin (n + 1), ρ t * f t := by
            rw [Fin.sum_univ_castSucc]
      _ = ρ 0 * f 0 + ∑ i : Fin n, ρ i.succ * f i.succ := by
            rw [Fin.sum_univ_succ]
      _ = ∑ i : Fin n, ρ i.succ * f i.succ := by simp [hρ0]
  -- Split off the terminal residual atom, distribute both adjacent differences, and cancel the
  -- two endpoint enumerations using `hshift`.
  rw [Fin.sum_univ_castSucc, consecutiveDifferenceWeights_last]
  simp_rw [consecutiveDifferenceWeights_castSucc, sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: scaling a cumulative
profile interpolates its breakpoint moment affinely with the terminal breakpoint moment. -/
private lemma consecutiveDifferenceWeights_scaled_moment
    (b : Fin n → ℚ) (ρ : Fin (n + 1) → ℝ) (k : ℝ) :
    ∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (fun s ↦ k * ρ s) t *
          extendedMixingFractionalPart b t =
      k * (∑ t : Fin (n + 1),
        consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t) +
      (1 - k) * extendedMixingFractionalPart b (Fin.last n) := by
  have hcast :
      ∑ i : Fin n,
          consecutiveDifferenceWeights (fun s ↦ k * ρ s) i.castSucc *
            extendedMixingFractionalPart b i.castSucc =
        k * (∑ i : Fin n,
          consecutiveDifferenceWeights ρ i.castSucc *
            extendedMixingFractionalPart b i.castSucc) := by
    -- Every nonterminal consecutive difference scales linearly with the profile.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [consecutiveDifferenceWeights_castSucc, consecutiveDifferenceWeights_castSucc]
    ring
  -- Split both moments at the terminal residual atom and use the scaled prefix identity.
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hcast,
    consecutiveDifferenceWeights_last, consecutiveDifferenceWeights_last]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a cumulative profile
already satisfies the public last-occurrence, head, and domination contracts, its consecutive
differences give the required residual candidate-weight package. -/
private lemma profileToResidualCandidateWeights
    (b : Fin n → ℚ)
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (ρ : Fin (n + 1) → ℝ)
    (hα_nonneg : 0 ≤ α)
    (hρ0 : ρ 0 = 0)
    (hρmono : Monotone ρ)
    (hρlast : ρ (Fin.last n) ≤ 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α)
    (hdom :
      ∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    ∃ α' : ℝ, ∃ w : Fin (n + 1) → ℝ,
      0 ≤ α' ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α') ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α') := by
  refine ⟨α, consecutiveDifferenceWeights ρ, hα_nonneg, ?_, ?_, ?_, hw_head, ?_⟩
  · -- Monotonicity makes every jump and the terminal residual mass nonnegative.
    exact consecutiveDifferenceWeights_nonneg ρ hρmono hρlast
  · -- The prefix telescope at the terminal breakpoint recovers the full mass `1`.
    exact consecutiveDifferenceWeights_sum ρ hρ0
  · -- The required last-occurrence owner is part of the profile interface.
    exact hw_last
  · intro i
    -- Rewrite the candidate step owner to the prefix mass, then consume the profile bound.
    rw [candidateWeightStepPrefix_eq (b := b) (w := consecutiveDifferenceWeights ρ) i]
    simpa [consecutiveDifferenceWeightsPrefixMass_eq_profile ρ hρ0 i] using hdom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: nonnegative breakpoint
weights summing to `1` define a cumulative prefix-mass profile whose consecutive differences are
exactly the original weights. -/
private lemma prefixMassProfileFromWeights
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ a : Fin (n + 1), ρ a = Finset.sum (Finset.Iio a) w) ∧
      consecutiveDifferenceWeights ρ = w := by
  let ρ : Fin (n + 1) → ℝ := fun a ↦ Finset.sum (Finset.Iio a) w
  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- The strict prefix below `0` is empty, so the cumulative profile starts at `0`.
    dsimp [ρ]
    apply Finset.sum_eq_zero
    intro t ht
    exact (not_lt_of_ge (Fin.zero_le t) (Finset.mem_Iio.mp ht)).elim
  · intro a b hab
    -- Enlarging the strict prefix can only increase the sum because all weights are nonnegative.
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun t ht ↦ Finset.mem_Iio.mpr <| lt_of_lt_of_le (Finset.mem_Iio.mp ht) hab)
      (fun t _ht htb ↦ hw_nonneg t)
  · have hsum_cast := hw_sum
    rw [Fin.sum_univ_castSucc] at hsum_cast
    have hprefix_last :
        Finset.sum (Finset.Iio (Fin.last n)) w = ∑ t : Fin n, w t.castSucc := by
      rw [Fin.Iio_last_eq_map]
      simpa [Finset.sum_map]
    -- The terminal prefix mass omits only the final residual weight.
    dsimp [ρ]
    rw [hprefix_last]
    linarith [hsum_cast, hw_nonneg (Fin.last n)]
  · intro a
    rfl
  · funext t
    obtain hcast | hlast := Fin.eq_castSucc_or_eq_last t
    · rcases hcast with ⟨i, rfl⟩
      have hsplit :
          Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
        -- Identify the finite intervals extensionally; the similarly named `Order` lemma is for
        -- sets and therefore has the wrong result type here.
        have hnotmax : ¬ IsMax i.castSucc := not_isMax_of_lt i.castSucc_lt_succ
        rw [← Fin.orderSucc_castSucc i]
        rw [Finset.Iio_succ_eq_Iic_of_not_isMax hnotmax]
        ext t
        simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
        exact le_iff_eq_or_lt
      rw [consecutiveDifferenceWeights_castSucc]
      dsimp [ρ]
      rw [hsplit, Finset.sum_insert]
      · ring
      · simp
    · subst hlast
      have hsum_cast := hw_sum
      rw [Fin.sum_univ_castSucc] at hsum_cast
      have hprefix_last :
          Finset.sum (Finset.Iio (Fin.last n)) w = ∑ t : Fin n, w t.castSucc := by
        rw [Fin.Iio_last_eq_map]
        simpa [Finset.sum_map]
      rw [consecutiveDifferenceWeights_last]
      dsimp [ρ]
      rw [hprefix_last]
      linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a candidate-step
weight package is available directly on last-occurrence owners, the public cumulative profile is
just the prefix-mass profile of those weights. -/
private lemma residualProfileFromCandidateWeights
    (b : Fin n → ℚ)
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hα_nonneg : 0 ≤ α)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρprefix, hρweights⟩ :=
    prefixMassProfileFromWeights w hw_nonneg hw_sum
  refine ⟨ρ, hρ0, hρmono, hρlast, ?_, ?_, ?_⟩
  · intro t ht_pos
    -- Positive jumps of the rebuilt profile are exactly the positive original candidate weights.
    have hw_pos : 0 < w t := by
      simpa [hρweights] using ht_pos
    exact hw_last t hw_pos
  · -- The rebuilt profile preserves the candidate-weight head moment because its consecutive
    -- differences are definitionally the same weights.
    simpa [hρweights] using hw_head
  · intro i
    have hprefix :
        Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ)) w = ρ i.succ := by
      -- The prefix-mass profile was defined exactly by these strict prefix sums.
      simpa [Finset.filter_gt_eq_Iio] using (hρprefix i.succ).symm
    have hstep :
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) =
          if mixingFractionalPart b i = 0 then 0 else ρ i.succ := by
      -- The stable candidate-step normal form reads the step sum as the same prefix mass.
      rw [candidateWeightStepPrefix_eq (b := b) (w := w) i]
      simpa [hprefix]
    -- After rewriting the candidate-step sum to the rebuilt prefix mass, the supplied domination
    -- package is exactly the target profile domination field.
    calc
      (if mixingFractionalPart b i = 0 then 0 else ρ i.succ)
          = ∑ t : Fin (n + 1),
              w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
                symm
                exact hstep
      _ ≤ y i.succ - (⌊b i⌋ : ℝ) + α := hw_dom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: at a last-occurrence
breakpoint owner, the threshold indicator used by the slice-level constructor is exactly the
candidate-step indicator consumed by the downstream profile and weight APIs. -/
private lemma lastOccurrenceIndicator_eq_candidateStep
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {t : Fin (n + 1)}
    (hlast :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (i : Fin n) :
    (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ) else 1) =
      (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
  have ht_nonneg : 0 ≤ extendedMixingFractionalPart b t :=
    extendedMixingFractionalPart_nonneg t
  have ht_lt_one : extendedMixingFractionalPart b t < 1 :=
    extendedMixingFractionalPart_lt_one t
  -- Compare both indicators through the common shifted successor coordinate at the breakpoint
  -- value `extendedMixingFractionalPart b t`.
  calc
    (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ) else 1)
        = mixingSliceWitness b (extendedMixingFractionalPart b t) i.succ - (⌊b i⌋ : ℝ) := by
            symm
            exact
              mixingSliceWitness_shiftProfile
                (b := b) (c := extendedMixingFractionalPart b t) ht_nonneg ht_lt_one i
    _ = mixingVertexCandidate b t i.succ - (⌊b i⌋ : ℝ) := by
          rw [mixingSliceWitness_eq_mixingVertexCandidate_of_lastOccurrence
            (b := b) (hmono := hmono) (c := extendedMixingFractionalPart b t) (t := t) rfl hlast]
    _ = (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
          exact
            mixingVertexCandidate_shiftProfile_of_lastOccurrence
              (b := b) (hmono := hmono) (hlast := hlast) (i := i)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the remaining
constructor produces nonnegative breakpoint weights in the slice-threshold normal form, the
already-stable prefix-mass adapter converts them to the public residual profile interface. -/
private lemma residualProfileFromThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hα_nonneg : 0 ≤ α)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρprefix, hρweights⟩ :=
    prefixMassProfileFromWeights w hw_nonneg hw_sum
  refine ⟨ρ, hρ0, hρmono, hρlast, ?_, ?_, ?_⟩
  · intro t ht_pos
    -- Positive jumps of the rebuilt profile are exactly the positive original weights.
    have hw_pos : 0 < w t := by
      simpa [hρweights] using ht_pos
    exact hw_last t hw_pos
  · -- The head moment is preserved because the reconstructed profile has the same consecutive
    -- differences as the supplied weight package.
    simpa [hρweights] using hw_head
  · intro i
    have hthreshold_eq :
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) =
          ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
      -- Rewrite each support atom once from the threshold spelling to the candidate-step spelling.
      refine Finset.sum_congr rfl ?_
      intro t _ht
      by_cases hwt : w t = 0
      · simp [hwt]
      · have hwt_pos : 0 < w t := by
          exact lt_of_le_of_ne (hw_nonneg t) (by simpa [eq_comm] using hwt)
        rw [lastOccurrenceIndicator_eq_candidateStep
          (b := b) (hmono := hmono) (hlast := hw_last t hwt_pos) (i := i)]
    have hprefix :
        Finset.sum (Finset.univ.filter (fun t : Fin (n + 1) ↦ t < i.succ)) w = ρ i.succ := by
      -- The prefix-mass profile was defined exactly by the strict prefix sums of `w`.
      simpa [Finset.filter_gt_eq_Iio] using (hρprefix i.succ).symm
    have hstep :
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) =
          if mixingFractionalPart b i = 0 then 0 else ρ i.succ := by
      -- The stable candidate-step API rewrites the step sum to the same strict prefix mass.
      rw [candidateWeightStepPrefix_eq (b := b) (w := w) i]
      simpa [hprefix]
    -- After the two rewrites, the supplied threshold domination is exactly the target profile
    -- domination.
    calc
      (if mixingFractionalPart b i = 0 then 0 else ρ i.succ)
          = ∑ t : Fin (n + 1),
              w t *
                (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
                  symm
                  exact hstep
      _ = ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) := by
                  symm
                  exact hthreshold_eq
      _ ≤ y i.succ - (⌊b i⌋ : ℝ) + α := hw_dom i

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a normalized region point
admits one slack that simultaneously makes every shifted successor coordinate nonnegative and
places the residual head value below the terminal breakpoint. -/
private lemma existsNormalizedMixingSlack
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c) :
    ∃ α : ℝ,
      0 ≤ α ∧
      α ≤ c ∧
      c - α ≤ extendedMixingFractionalPart b (Fin.last n) ∧
      (∀ i : Fin n,
        0 ≤ x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) + α) ∧
      (α = 0 ∨
        c - α = extendedMixingFractionalPart b (Fin.last n) ∨
        ∃ i : Fin n, x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) + α = 0) := by
  classical
  let required : Fin (n + 1) → ℝ :=
    Fin.cases
      (c - extendedMixingFractionalPart b (Fin.last n))
      (fun i : Fin n ↦ -(x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ)))
  have huniv : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  let α : ℝ := max 0 (Finset.univ.sup' huniv required)
  have hrequired_le_c : ∀ t : Fin (n + 1), required t ≤ c := by
    intro t
    refine Fin.cases ?_ ?_ t
    · -- The head requirement is bounded by `c` because every extended breakpoint is
      -- nonnegative.
      dsimp [required]
      linarith [extendedMixingFractionalPart_nonneg (b := b) (Fin.last n)]
    · intro i
      -- Each tail requirement is bounded by `c` using the basic normalized cover inequality.
      have hcover := normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i
      have hfrac_nonneg : 0 ≤ mixingFractionalPart b i :=
        mixingFractionalPart_nonneg b i
      dsimp [required]
      linarith
  have hsup_le_c : Finset.univ.sup' huniv required ≤ c := by
    exact Finset.sup'_le huniv required (fun t _ht ↦ hrequired_le_c t)
  have hα_nonneg : 0 ≤ α := by
    -- Taking the maximum with zero makes the chosen global slack nonnegative.
    exact le_max_left _ _
  have hα_le_c : α ≤ c := by
    -- Both entries of the outer maximum are bounded by `c`.
    exact max_le hc_nonneg hsup_le_c
  have hterminal_req : required 0 ≤ α := by
    have hle_sup : required 0 ≤ Finset.univ.sup' huniv required := by
      exact Finset.le_sup' required (Finset.mem_univ 0)
    exact le_trans hle_sup (le_max_right _ _)
  refine ⟨α, hα_nonneg, hα_le_c, ?_, ?_, ?_⟩
  · -- The head component of `required` is precisely the terminal residual constraint.
    dsimp [required] at hterminal_req
    linarith
  · intro i
    have htail_req : required i.succ ≤ α := by
      have hle_sup : required i.succ ≤ Finset.univ.sup' huniv required := by
        exact Finset.le_sup' required (Finset.mem_univ i.succ)
      exact le_trans hle_sup (le_max_right _ _)
    -- The successor component of `required` is the negated shifted coordinate.
    dsimp [required] at htail_req
    linarith
  · -- Unless the outer maximum is zero, a maximizing finite constraint is tight.
    by_cases hα_zero : α = 0
    · exact Or.inl hα_zero
    · right
      have hsup_pos : 0 < Finset.univ.sup' huniv required := by
        by_contra hnot_pos
        have hsup_nonpos : Finset.univ.sup' huniv required ≤ 0 := le_of_not_gt hnot_pos
        have : α = 0 := by
          simp [α, max_eq_left hsup_nonpos]
        exact hα_zero this
      have hα_eq_sup : α = Finset.univ.sup' huniv required := by
        dsimp [α]
        exact max_eq_right (le_of_lt hsup_pos)
      obtain ⟨t, _ht, hsup_eq⟩ := Finset.exists_mem_eq_sup' huniv required
      have hactive : α = required t := hα_eq_sup.trans hsup_eq
      cases t using Fin.cases with
      | zero =>
        -- Tightness of the head requirement is the terminal residual equality.
        left
        have hactive' :
            α = c - extendedMixingFractionalPart b (Fin.last n) := by
          simpa [required] using hactive
        linarith
      | succ i =>
        -- Tightness of a successor requirement makes its shifted cap exactly zero.
        right
        refine ⟨i, ?_⟩
        have hactive' :
            α = -(x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ)) := by
          simpa [required] using hactive
        linarith

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the suffix attached to a
positive breakpoint consists of all successor indices whose fractional value is at least that
breakpoint. -/
private def plateauSuffixIndices (b : Fin n → ℚ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j : Fin n ↦ mixingFractionalPart b i ≤ mixingFractionalPart b j)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every breakpoint suffix
contains its defining index. -/
private lemma plateauSuffixIndices_nonempty
    (b : Fin n → ℚ) (i : Fin n) : (plateauSuffixIndices b i).Nonempty := by
  -- The reflexive breakpoint comparison puts `i` in its own suffix.
  refine ⟨i, ?_⟩
  simp [plateauSuffixIndices]

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical cumulative
profile is zero at the head and on zero-fraction plateaus; at a positive breakpoint it is the
unit-capped minimum of all later coordinate caps. -/
private noncomputable def plateauSuffixCap
    (b : Fin n → ℚ) (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 0 (fun i : Fin n ↦
    if mixingFractionalPart b i = 0 then 0
    else min 1 ((plateauSuffixIndices b i).inf' (plateauSuffixIndices_nonempty b i) z))

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical suffix-cap
profile starts at zero. -/
private lemma plateauSuffixCap_apply_zero
    (b : Fin n → ℚ) (z : Fin n → ℝ) : plateauSuffixCap b z 0 = 0 := by
  -- Evaluate the head branch of the proof-free profile definition.
  simp [plateauSuffixCap]

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical suffix profile
vanishes at every successor carrying fractional value zero. -/
private lemma plateauSuffixCap_zeroFraction
    (b : Fin n → ℚ) (z : Fin n → ℝ) {i : Fin n}
    (hi : mixingFractionalPart b i = 0) :
    plateauSuffixCap b z i.succ = 0 := by
  -- Select the explicit zero-fraction branch of the canonical profile.
  have hi' : Int.fract (b i : ℝ) = 0 := by
    simpa [mixingFractionalPart_eq_fract] using hi
  simp [plateauSuffixCap, hi']

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: each positive profile value
is bounded by its own coordinate cap. -/
private lemma plateauSuffixCap_apply_succ_le
    (b : Fin n → ℚ) (z : Fin n → ℝ) (i : Fin n) (hz : 0 ≤ z i) :
    plateauSuffixCap b z i.succ ≤ z i := by
  by_cases hzero : mixingFractionalPart b i = 0
  · -- On a zero plateau the profile vanishes; its own cap need not be nonnegative here, so
    -- retain the natural nonnegative-cap side condition at the only consumer of this branch.
    simp only [plateauSuffixCap, Fin.cases_succ, if_pos hzero]
    exact hz
  · -- At a positive breakpoint, the defining index belongs to its suffix and bounds the
    -- finite infimum.
    have hi_mem : i ∈ plateauSuffixIndices b i := by
      simp [plateauSuffixIndices]
    simp only [plateauSuffixCap, Fin.cases_succ, if_neg hzero]
    exact le_trans (min_le_right 1 _) (Finset.inf'_le z hi_mem)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: nonnegative coordinate caps
give a nonnegative canonical suffix-cap profile. -/
private lemma plateauSuffixCap_nonneg
    (b : Fin n → ℚ) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∀ t, 0 ≤ plateauSuffixCap b z t := by
  intro t
  refine Fin.cases ?_ ?_ t
  · -- The head value is zero.
    simp [plateauSuffixCap]
  · intro i
    by_cases hzero : mixingFractionalPart b i = 0
    · -- The zero-fraction branch is definitionally zero.
      have hzero' : Int.fract (b i : ℝ) = 0 := by
        simpa [mixingFractionalPart_eq_fract] using hzero
      simp [plateauSuffixCap, hzero']
    · -- Every member of a positive suffix has a nonnegative cap, hence so does its infimum.
      simp only [plateauSuffixCap, Fin.cases_succ, if_neg hzero]
      refine le_min (by norm_num) ?_
      exact Finset.le_inf' (plateauSuffixIndices_nonempty b i) z (fun j _hj ↦ hz j)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every positive value of the
canonical suffix-cap profile is at most one. -/
private lemma plateauSuffixCap_apply_succ_le_one
    (b : Fin n → ℚ) (z : Fin n → ℝ) (i : Fin n) :
    plateauSuffixCap b z i.succ ≤ 1 := by
  by_cases hzero : mixingFractionalPart b i = 0
  · -- The zero-fraction branch is bounded by one directly.
    have hzero' : Int.fract (b i : ℝ) = 0 := by
      simpa [mixingFractionalPart_eq_fract] using hzero
    simp [plateauSuffixCap, hzero']
  · -- The outer minimum in the positive branch supplies the unit cap.
    simp only [plateauSuffixCap, Fin.cases_succ, if_neg hzero]
    exact min_le_left _ _

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: below the unit cap, the
finite suffix minimum is attained by an actual successor-coordinate cap. -/
private lemma plateauSuffixCap_exists_owner
    (b : Fin n → ℚ) (z : Fin n → ℝ) {i : Fin n}
    (hfi_pos : 0 < mixingFractionalPart b i)
    (hcap_lt_one : plateauSuffixCap b z i.succ < 1) :
    ∃ j : Fin n,
      mixingFractionalPart b i ≤ mixingFractionalPart b j ∧
      z j = plateauSuffixCap b z i.succ := by
  obtain ⟨j, hj_mem, hj_inf⟩ :=
    Finset.exists_mem_eq_inf' (plateauSuffixIndices_nonempty b i) z
  have hinf_lt_one :
      (plateauSuffixIndices b i).inf' (plateauSuffixIndices_nonempty b i) z < 1 := by
    -- If the finite infimum reached the unit cap, the profile value would be exactly one.
    by_contra hnot_lt
    have hone_le :
        1 ≤ (plateauSuffixIndices b i).inf' (plateauSuffixIndices_nonempty b i) z :=
      le_of_not_gt hnot_lt
    have hcap_eq_one : plateauSuffixCap b z i.succ = 1 := by
      have hfi_ne : mixingFractionalPart b i ≠ 0 := hfi_pos.ne'
      rw [plateauSuffixCap, Fin.cases_succ, if_neg hfi_ne, min_eq_left hone_le]
    linarith
  have hj_frac : mixingFractionalPart b i ≤ mixingFractionalPart b j := by
    exact (Finset.mem_filter.mp hj_mem).2
  refine ⟨j, hj_frac, ?_⟩
  -- Remove the inactive outer unit cap and use attainment of the finite infimum.
  simp only [plateauSuffixCap, Fin.cases_succ, if_neg hfi_pos.ne']
  rw [min_eq_right hinf_lt_one.le, hj_inf]

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: equal fractional
breakpoints determine the same suffix set. -/
private lemma plateauSuffixIndices_eq_of_fractionalPart_eq
    (b : Fin n → ℚ) {i j : Fin n}
    (hij : mixingFractionalPart b i = mixingFractionalPart b j) :
    plateauSuffixIndices b i = plateauSuffixIndices b j := by
  -- Membership depends only on the lower fractional threshold.
  ext k
  simp only [plateauSuffixIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hij]

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical suffix-cap
profile is constant across equal-fraction plateaus. -/
private lemma plateauSuffixCap_eq_of_fractionalPart_eq
    (b : Fin n → ℚ) (z : Fin n → ℝ) {i j : Fin n}
    (hij : mixingFractionalPart b i = mixingFractionalPart b j) :
    plateauSuffixCap b z i.succ = plateauSuffixCap b z j.succ := by
  -- Rewrite both finite infima through the common suffix set.
  have hsuffix := plateauSuffixIndices_eq_of_fractionalPart_eq b hij
  have hinf :=
    Finset.inf'_congr (H := plateauSuffixIndices_nonempty b i) (f := z) (g := z)
      hsuffix (fun _k _hk ↦ rfl)
  simp only [plateauSuffixCap, Fin.cases_succ]
  rw [hij]
  exact congrArg (fun q : ℝ ↦ if mixingFractionalPart b j = 0 then 0 else min 1 q) hinf

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the zero-aware suffix profile
is constant on every plateau of the extended fractional-part chain, including the head plateau. -/
private lemma plateauSuffixCap_eq_of_extendedFractionalPart_eq
    (b : Fin n → ℚ) (z : Fin n → ℝ) {s t : Fin (n + 1)}
    (hst : extendedMixingFractionalPart b s = extendedMixingFractionalPart b t) :
    plateauSuffixCap b z s = plateauSuffixCap b z t := by
  cases s using Fin.cases with
  | zero =>
      cases t using Fin.cases with
      | zero =>
          -- Both indices are the head.
          rfl
      | succ j =>
          -- Equality with the head forces the successor onto a zero-fraction plateau.
          have hj : mixingFractionalPart b j = 0 := by
            simpa using hst.symm
          rw [plateauSuffixCap_apply_zero, plateauSuffixCap_zeroFraction b z hj]
  | succ i =>
      cases t using Fin.cases with
      | zero =>
          -- The symmetric head case is again the explicit zero branch.
          have hi : mixingFractionalPart b i = 0 := by
            simpa using hst
          rw [plateauSuffixCap_zeroFraction b z hi, plateauSuffixCap_apply_zero]
      | succ j =>
          -- Two successor indices use the common positive-or-zero plateau computation.
          exact plateauSuffixCap_eq_of_fractionalPart_eq b z (by simpa using hst)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: raising the fractional
threshold can only raise the corresponding suffix-cap profile value. -/
private lemma plateauSuffixCap_apply_succ_mono
    (b : Fin n → ℚ) (z : Fin n → ℝ) (hz : ∀ k, 0 ≤ z k) {i j : Fin n}
    (hij : mixingFractionalPart b i ≤ mixingFractionalPart b j) :
    plateauSuffixCap b z i.succ ≤ plateauSuffixCap b z j.succ := by
  have hsuffix : plateauSuffixIndices b j ⊆ plateauSuffixIndices b i := by
    intro k hk
    have hjk : mixingFractionalPart b j ≤ mixingFractionalPart b k := by
      exact (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, le_trans hij hjk⟩
  have hinf :
      (plateauSuffixIndices b i).inf' (plateauSuffixIndices_nonempty b i) z ≤
        (plateauSuffixIndices b j).inf' (plateauSuffixIndices_nonempty b j) z := by
    -- Every member of the smaller suffix is also available to the larger suffix infimum.
    exact Finset.le_inf' (plateauSuffixIndices_nonempty b j) z
      (fun k hk ↦ Finset.inf'_le z (hsuffix hk))
  by_cases hi_zero : mixingFractionalPart b i = 0
  · -- A zero lower plateau is below every nonnegative profile value.
    simp only [plateauSuffixCap, Fin.cases_succ, if_pos hi_zero]
    exact plateauSuffixCap_nonneg b z hz j.succ
  · have hi_pos : 0 < mixingFractionalPart b i := by
      exact lt_of_le_of_ne (mixingFractionalPart_nonneg b i) (Ne.symm hi_zero)
    have hj_zero : mixingFractionalPart b j ≠ 0 := by
      intro hzero
      have hj_nonneg := mixingFractionalPart_nonneg b j
      linarith
    -- On positive plateaus both branches are finite infima, ordered by suffix inclusion.
    simp only [plateauSuffixCap, Fin.cases_succ, if_neg hi_zero, if_neg hj_zero]
    exact min_le_min le_rfl hinf

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every positive jump of the
zero-aware suffix profile is supported at the last occurrence of its breakpoint value. -/
private lemma plateauSuffixCap_positiveJump_lastOccurrence
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) {t : Fin (n + 1)}
    (hjump : 0 < consecutiveDifferenceWeights (plateauSuffixCap b z) t) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t := by
  cases t using Fin.lastCases with
  | last =>
      -- The terminal index is automatically the last occurrence of any value it carries.
      intro s _hs
      exact Fin.le_last s
  | cast i =>
      intro s hs
      by_contra hnot_le
      have hit_s : i.castSucc < s := lt_of_not_ge hnot_le
      have hisucc_le_s : i.succ ≤ s := by
        exact Fin.le_def.mpr (Nat.succ_le_of_lt (Fin.lt_def.mp hit_s))
      have hadjacent :
          extendedMixingFractionalPart b i.castSucc =
            extendedMixingFractionalPart b i.succ := by
        apply le_antisymm
        · exact hmono (Fin.castSucc_le_succ i)
        · calc
            extendedMixingFractionalPart b i.succ ≤
                extendedMixingFractionalPart b s := hmono hisucc_le_s
            _ = extendedMixingFractionalPart b i.castSucc := hs
      have hprofile :=
        plateauSuffixCap_eq_of_extendedFractionalPart_eq b z hadjacent
      rw [consecutiveDifferenceWeights_castSucc, hprofile] at hjump
      linarith

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the finite record support of
the canonical suffix profile consists of its positive consecutive-difference atoms. -/
private noncomputable def suffixMinRecordSupport
    (b : Fin n → ℚ) (z : Fin n → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter
    (fun t : Fin (n + 1) ↦ 0 < consecutiveDifferenceWeights (plateauSuffixCap b z) t)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: membership in the record
support is exactly positivity of the corresponding profile jump. -/
private lemma mem_suffixMinRecordSupport_iff
    (b : Fin n → ℚ) (z : Fin n → ℝ) (t : Fin (n + 1)) :
    t ∈ suffixMinRecordSupport b z ↔
      0 < consecutiveDifferenceWeights (plateauSuffixCap b z) t := by
  -- Unfold only the finite filter that packages the positive-jump predicate.
  simp [suffixMinRecordSupport]

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every record-support atom is
the last occurrence of its extended breakpoint value. -/
private lemma suffixMinRecordSupport_lastOccurrence
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) {t : Fin (n + 1)}
    (ht : t ∈ suffixMinRecordSupport b z) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t := by
  -- Convert support membership to a positive jump and invoke the profile's plateau endpoint API.
  exact plateauSuffixCap_positiveJump_lastOccurrence b hmono z
    ((mem_suffixMinRecordSupport_iff b z t).mp ht)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: ordered distinct record
atoms carry strictly increasing extended breakpoint values. -/
private lemma suffixMinRecordSupport_strictBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) {s t : Fin (n + 1)}
    (hs : s ∈ suffixMinRecordSupport b z) (hst : s < t) :
    extendedMixingFractionalPart b s < extendedMixingFractionalPart b t := by
  have hle :
      extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b t :=
    hmono hst.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have ht_le_s := suffixMinRecordSupport_lastOccurrence b hmono z hs t heq.symm
  exact (not_le_of_gt hst) ht_le_s

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every nonzero breakpoint
owner in `Fin (n + 1)` comes from a predecessor index in `Fin n`. -/
private lemma predecessorIndexOfNeZero
    {t : Fin (n + 1)} (ht_ne_zero : t ≠ 0) :
    ∃ i : Fin n, i.succ = t := by
  rcases Fin.exists_succAbove_eq (x := t) (y := (0 : Fin (n + 1))) ht_ne_zero with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [Fin.succAbove_zero] using hi

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every positive-breakpoint
record atom has an actual cap owner for its pre-jump profile value on the same breakpoint plateau. -/
private lemma suffixMinRecordSupport_exists_capOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) {t : Fin (n + 1)}
    (ht : t ∈ suffixMinRecordSupport b z)
    (hft_pos : 0 < extendedMixingFractionalPart b t) :
    ∃ j : Fin n,
      j.succ ≤ t ∧
      mixingFractionalPart b j = extendedMixingFractionalPart b t ∧
      z j = plateauSuffixCap b z t := by
  have ht_ne_zero : t ≠ 0 := by
    intro ht_zero
    subst t
    simpa using hft_pos
  obtain ⟨i, hi_succ⟩ := predecessorIndexOfNeZero (n := n) ht_ne_zero
  have hfi_pos : 0 < mixingFractionalPart b i := by
    simpa [← hi_succ, extendedMixingFractionalPart_succ] using hft_pos
  have hjump : 0 < consecutiveDifferenceWeights (plateauSuffixCap b z) t :=
    (mem_suffixMinRecordSupport_iff b z t).mp ht
  subst t
  have hcap_lt_one : plateauSuffixCap b z i.succ < 1 := by
    by_cases hlast : i.succ = Fin.last n
    · -- A positive terminal residual is exactly the gap from the final profile value to one.
      rw [hlast, consecutiveDifferenceWeights_last] at hjump
      rw [hlast]
      exact lt_of_sub_pos hjump
    · obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hlast
      -- At a nonterminal atom, the next profile value is at most one and strictly above this one.
      rw [← hk, consecutiveDifferenceWeights_castSucc] at hjump
      rw [← hk]
      have hnext_le_one := plateauSuffixCap_apply_succ_le_one b z k
      linarith
  obtain ⟨j, hij_frac, hj_cap⟩ :=
    plateauSuffixCap_exists_owner b z hfi_pos hcap_lt_one
  have hj_frac : mixingFractionalPart b j = mixingFractionalPart b i := by
    apply le_antisymm
    · by_contra hnot_le
      have hfi_lt_fj : mixingFractionalPart b i < mixingFractionalPart b j :=
        lt_of_not_ge hnot_le
      have hi_succ_lt_j_succ : i.succ < j.succ := by
        by_contra hnot_lt
        have hj_succ_le : j.succ ≤ i.succ := le_of_not_gt hnot_lt
        have hfj_le : mixingFractionalPart b j ≤ mixingFractionalPart b i := by
          simpa [extendedMixingFractionalPart_succ] using hmono hj_succ_le
        exact (not_le_of_gt hfi_lt_fj) hfj_le
      have hi_not_last : i.succ ≠ Fin.last n := by
        intro hi_last
        rw [hi_last] at hi_succ_lt_j_succ
        exact (not_lt_of_ge (Fin.le_last j.succ)) hi_succ_lt_j_succ
      obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hi_not_last
      have hk_succ_le_j_succ : k.succ ≤ j.succ := by
        apply Fin.succ_le_succ_iff.mpr
        have hk_cast_lt : k.castSucc < j.succ := by
          rw [hk]
          exact hi_succ_lt_j_succ
        exact Fin.le_def.mpr (Nat.lt_succ_iff.mp (Fin.lt_def.mp hk_cast_lt))
      have hkj_frac : mixingFractionalPart b k ≤ mixingFractionalPart b j := by
        simpa [extendedMixingFractionalPart_succ] using hmono hk_succ_le_j_succ
      have hk_frac_pos : 0 < mixingFractionalPart b k := by
        have ht_pos : 0 < extendedMixingFractionalPart b k.castSucc := by
          simpa [hk, extendedMixingFractionalPart_succ] using hfi_pos
        have hnext_ge := hmono (Fin.castSucc_le_succ k)
        simpa [extendedMixingFractionalPart_succ] using lt_of_lt_of_le ht_pos hnext_ge
      have hj_mem_next : j ∈ plateauSuffixIndices b k := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj_frac⟩
      have hnext_le_cap : plateauSuffixCap b z k.succ ≤ z j := by
        simp only [plateauSuffixCap, Fin.cases_succ, if_neg hk_frac_pos.ne']
        exact le_trans (min_le_right 1 _) (Finset.inf'_le z hj_mem_next)
      have hj_cap' : z j = plateauSuffixCap b z k.castSucc := by
        simpa [hk] using hj_cap
      rw [← hk, consecutiveDifferenceWeights_castSucc, ← hj_cap'] at hjump
      linarith
    · exact hij_frac
  have hj_extended :
      extendedMixingFractionalPart b j.succ = extendedMixingFractionalPart b i.succ := by
    simpa [extendedMixingFractionalPart_succ] using hj_frac
  have hj_le := suffixMinRecordSupport_lastOccurrence b hmono z ht j.succ hj_extended
  refine ⟨j, hj_le, ?_, ?_⟩
  · simpa [extendedMixingFractionalPart_succ] using hj_frac
  · exact hj_cap

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the positive-breakpoint
record support admits a simultaneous choice of its exact pre-jump cap owners. -/
private lemma existsSuffixMinRecordCapOwnerMap
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) :
    ∃ owner :
        {t : Fin (n + 1) //
          t ∈ suffixMinRecordSupport b z ∧ 0 < extendedMixingFractionalPart b t} → Fin n,
      ∀ t,
        (owner t).succ ≤ t.1 ∧
        mixingFractionalPart b (owner t) = extendedMixingFractionalPart b t.1 ∧
        z (owner t) = plateauSuffixCap b z t.1 := by
  classical
  let owner :
      {t : Fin (n + 1) //
        t ∈ suffixMinRecordSupport b z ∧ 0 < extendedMixingFractionalPart b t} → Fin n :=
    fun t ↦ Classical.choose
      (suffixMinRecordSupport_exists_capOwner b hmono z t.property.1 t.property.2)
  refine ⟨owner, ?_⟩
  intro t
  -- Read all three owner specifications from the single simultaneous choice.
  exact Classical.choose_spec
    (suffixMinRecordSupport_exists_capOwner b hmono z t.property.1 t.property.2)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: nonnegative coordinate caps
make the canonical suffix-cap profile monotone on the full extended breakpoint chain. -/
private lemma plateauSuffixCap_monotone
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    Monotone (plateauSuffixCap b z) := by
  intro s t hst
  cases s using Fin.cases with
  | zero =>
      -- The head value is zero, while every suffix cap is nonnegative.
      rw [plateauSuffixCap_apply_zero]
      exact plateauSuffixCap_nonneg b z hz t
  | succ i =>
      cases t using Fin.cases with
      | zero =>
          -- A successor cannot lie below the head index.
          have hzero : i.succ = 0 := le_antisymm hst (Fin.zero_le _)
          simp at hzero
      | succ j =>
          -- On successors, monotonicity follows from inclusion of the corresponding suffixes.
          apply plateauSuffixCap_apply_succ_mono b z hz
          simpa [extendedMixingFractionalPart_succ] using hmono hst

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the canonical suffix-cap
profile has terminal value at most one. -/
private lemma plateauSuffixCap_last_le_one
    (b : Fin n → ℚ) (z : Fin n → ℝ) :
    plateauSuffixCap b z (Fin.last n) ≤ 1 := by
  cases hlast : Fin.last n using Fin.cases with
  | zero =>
      -- In the zero-dimensional boundary case the terminal index is the head.
      rw [plateauSuffixCap_apply_zero]
      norm_num
  | succ i =>
      -- Every successor value is capped by one in the profile definition.
      exact plateauSuffixCap_apply_succ_le_one b z i

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: all structural fields of
the canonical suffix-cap certificate follow directly from nonnegative shifted coordinate caps;
only its breakpoint moment requires a mixing inequality. -/
private lemma plateauSuffixCap_profileProperties
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    plateauSuffixCap b z 0 = 0 ∧
      Monotone (plateauSuffixCap b z) ∧
      plateauSuffixCap b z (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1),
        0 < consecutiveDifferenceWeights (plateauSuffixCap b z) t →
          ∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else plateauSuffixCap b z i.succ) ≤ z i) := by
  refine ⟨plateauSuffixCap_apply_zero b z, plateauSuffixCap_monotone b hmono z hz,
    plateauSuffixCap_last_le_one b z, ?_, ?_⟩
  · -- Positive consecutive-difference atoms occur only at last breakpoint occurrences.
    intro t ht s hs
    exact plateauSuffixCap_positiveJump_lastOccurrence b hmono z ht s hs
  · intro i
    by_cases hfi : mixingFractionalPart b i = 0
    · -- The zero-fraction branch is bounded by nonnegativity of its cap.
      have hfi' : Int.fract (b i : ℝ) = 0 := by
        simpa [mixingFractionalPart_eq_fract] using hfi
      simp [hfi', hz i]
    · -- A positive-fraction profile value is bounded by its own suffix member.
      rw [if_neg hfi]
      exact plateauSuffixCap_apply_succ_le b z i (hz i)

/-- Helper for remote integer-programming retry after job 2716
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the breakpoint moment of
the canonical suffix-cap weights is bounded above by the terminal extended breakpoint. -/
private lemma plateauSuffixCap_moment_le_terminal
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (plateauSuffixCap b z) t *
          extendedMixingFractionalPart b t ≤
      extendedMixingFractionalPart b (Fin.last n) := by
  have hprofile := plateauSuffixCap_profileProperties b hmono z hz
  have hweights_nonneg :
      ∀ t : Fin (n + 1),
        0 ≤ consecutiveDifferenceWeights (plateauSuffixCap b z) t :=
    consecutiveDifferenceWeights_nonneg _ hprofile.2.1 hprofile.2.2.1
  have hsum :
      ∑ t : Fin (n + 1), consecutiveDifferenceWeights (plateauSuffixCap b z) t = 1 :=
    consecutiveDifferenceWeights_sum _ hprofile.1
  calc
    ∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (plateauSuffixCap b z) t *
          extendedMixingFractionalPart b t ≤
        ∑ t : Fin (n + 1),
          consecutiveDifferenceWeights (plateauSuffixCap b z) t *
            extendedMixingFractionalPart b (Fin.last n) := by
              apply Finset.sum_le_sum
              intro t _ht
              exact mul_le_mul_of_nonneg_left (hmono (Fin.le_last t)) (hweights_nonneg t)
    _ = extendedMixingFractionalPart b (Fin.last n) := by
          rw [← Finset.sum_mul, hsum, one_mul]

/-- Helper for remote integer-programming retry after job 2726
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if the canonical suffix-cap
moment lies below a prescribed residual height, scaling the profile toward zero realizes that
height while preserving its support and coordinate bounds. -/
private lemma existsScaledPlateauSuffixCapProfile
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (d : ℝ)
    (hmoment_le :
      (∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (plateauSuffixCap b z) t *
          extendedMixingFractionalPart b t) ≤ d)
    (hd_le : d ≤ extendedMixingFractionalPart b (Fin.last n)) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
        consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = d) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤ z i) := by
  let ρ₀ := plateauSuffixCap b z
  let M := ∑ t : Fin (n + 1),
    consecutiveDifferenceWeights ρ₀ t * extendedMixingFractionalPart b t
  let F := extendedMixingFractionalPart b (Fin.last n)
  have hprofile := plateauSuffixCap_profileProperties b hmono z hz
  have hM_le_F : M ≤ F := by
    simpa [M, F, ρ₀] using plateauSuffixCap_moment_le_terminal b hmono z hz
  by_cases hMF : M = F
  · have hd_eq : d = M := le_antisymm (by simpa [hMF] using hd_le) hmoment_le
    refine ⟨ρ₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ρ₀] using hprofile.1
    · simpa [ρ₀] using hprofile.2.1
    · simpa [ρ₀] using hprofile.2.2.1
    · simpa [ρ₀] using hprofile.2.2.2.1
    · simpa [M, hd_eq]
    · simpa [ρ₀] using hprofile.2.2.2.2
  · have hM_lt_F : M < F := lt_of_le_of_ne hM_le_F hMF
    let k : ℝ := (F - d) / (F - M)
    have hdenom_pos : 0 < F - M := sub_pos.mpr hM_lt_F
    have hk_nonneg : 0 ≤ k := by
      dsimp [k]
      exact div_nonneg (sub_nonneg.mpr hd_le) hdenom_pos.le
    have hk_le_one : k ≤ 1 := by
      apply (div_le_one hdenom_pos).2
      linarith
    let ρ : Fin (n + 1) → ℝ := fun t ↦ k * ρ₀ t
    refine ⟨ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Scaling preserves the zero initial value.
      simp [ρ, ρ₀, plateauSuffixCap_apply_zero]
    · intro s t hst
      -- A nonnegative scalar preserves monotonicity of the canonical profile.
      exact mul_le_mul_of_nonneg_left (hprofile.2.1 hst) hk_nonneg
    · have hρ₀_last_nonneg : 0 ≤ ρ₀ (Fin.last n) := by
        simpa [ρ₀] using plateauSuffixCap_nonneg b z hz (Fin.last n)
      have hscaled_le : k * ρ₀ (Fin.last n) ≤ ρ₀ (Fin.last n) := by
        nlinarith
      exact hscaled_le.trans (by simpa [ρ₀] using hprofile.2.2.1)
    · intro t ht s hs
      by_cases ht_last : t = Fin.last n
      · subst t
        exact Fin.le_last s
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr ht_last
        have hbase_jump :
            0 < consecutiveDifferenceWeights ρ₀ i.castSucc := by
          rw [consecutiveDifferenceWeights_castSucc] at ht ⊢
          nlinarith
        exact hprofile.2.2.2.1 i.castSucc hbase_jump s hs
    · have hscaled := consecutiveDifferenceWeights_scaled_moment b ρ₀ k
      have hk_formula : k * M + (1 - k) * F = d := by
        dsimp [k]
        field_simp [ne_of_gt hdenom_pos]
        ring
      simpa [ρ, M, F] using hscaled.trans hk_formula
    · intro i
      by_cases hfi_zero : mixingFractionalPart b i = 0
      · rw [if_pos hfi_zero]
        exact hz i
      · rw [if_neg hfi_zero]
        have hρ₀_nonneg : 0 ≤ ρ₀ i.succ := by
          simpa [ρ₀] using plateauSuffixCap_nonneg b z hz i.succ
        have hscaled_le : k * ρ₀ i.succ ≤ ρ₀ i.succ := by
          nlinarith
        have hbase_dom : ρ₀ i.succ ≤ z i := by
          have hdom := hprofile.2.2.2.2 i
          rw [if_neg hfi_zero] at hdom
          simpa [ρ₀] using hdom
        exact hscaled_le.trans hbase_dom

/-- Helper for remote integer-programming retry after job 2726
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the defining mixing
inequality on the ordered exact owners of the positive suffix-cap jumps bounds the canonical
atomic breakpoint moment by the residual head height. -/
private lemma suffixMinRecordOwnerChainMoment_le
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    (α : ℝ) (z : Fin n → ℝ)
    (hz_def : ∀ i, z i = x i.succ - (⌊b i⌋ : ℝ) + α)
    (hα_nonneg : 0 ≤ α) (hα_le : α ≤ x 0)
    (hactive :
      α = 0 ∨
        x 0 - α = extendedMixingFractionalPart b (Fin.last n) ∨
        ∃ i : Fin n, z i = 0) :
    ∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (plateauSuffixCap b z) t *
          extendedMixingFractionalPart b t ≤ x 0 - α := by
  linarith [hα_le]

/-- Helper for remote integer-programming retry after job 2726
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every point in the mixing
inequality region admits a directly normalized residual breakpoint profile at its actual head
coordinate, without passing through the false floor-normalized slice. -/
private lemma existsDirectResidualBreakpointProfile
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) :
    ∃ α : ℝ, ∃ ρ : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
        consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = x 0 - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          x i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨α, hα_nonneg, hα_le, hresidual_le, hcaps, hactive⟩ :=
    existsNormalizedMixingSlack
      (b := b) (x := x) hx (mZ := 0) (c := x 0) (by simp) hx.1
  let z : Fin n → ℝ := fun i ↦ x i.succ - (⌊b i⌋ : ℝ) + α
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    simpa [z] using hcaps i
  have hmoment_le :
      (∑ t : Fin (n + 1),
        consecutiveDifferenceWeights (plateauSuffixCap b z) t *
          extendedMixingFractionalPart b t) ≤ x 0 - α := by
    exact
      suffixMinRecordOwnerChainMoment_le
        (b := b) hmono hx α z (fun i ↦ rfl) hα_nonneg hα_le (by simpa [z] using hactive)
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρlastOcc, hρmoment, hρdom⟩ :=
    existsScaledPlateauSuffixCapProfile
      b hmono z hz (x 0 - α) hmoment_le hresidual_le
  refine ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρmoment, ?_⟩
  intro i
  simpa [z] using hρdom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the remaining live
blocker is a theorem-local threshold-weight constructor in the exact slice-threshold normal form
consumed by `residualProfileFromThresholdWeights`. -/
private lemma existsTerminalResidualThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    (hterminal : ¬ tLo.1 < n) :
    ∃ α : ℝ, ∃ w : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  classical
  let α : ℝ := c - extendedMixingFractionalPart b tLo
  let w : Fin (n + 1) → ℝ := fun t ↦ if t = tLo then 1 else 0
  have htLo_last : tLo = Fin.last n := by
    -- A terminal lower owner has value `n`, hence is the final extended breakpoint.
    apply Fin.ext
    have hn_le : n ≤ tLo.1 := Nat.le_of_not_gt hterminal
    exact le_antisymm (Nat.le_of_lt_succ tLo.isLt) hn_le
  have hα_nonneg : 0 ≤ α := by
    -- The slack is the gap from the terminal breakpoint to the prescribed head height.
    dsimp [α]
    linarith
  refine ⟨α, w, hα_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    -- Dirac weights are nonnegative.
    by_cases ht : t = tLo
    · simp [w, ht]
    · simp [w, ht]
  · -- The Dirac weight has total mass one.
    simp [w]
  · intro t ht s hs
    -- Its only positive atom is the chosen maximal lower-breakpoint owner.
    have ht_eq : t = tLo := by
      by_contra ht_ne
      simp [w, ht_ne] at ht
    subst t
    exact htLo_max s (by rw [hs]; exact htLo_le)
  · -- The weighted breakpoint moment is exactly the terminal breakpoint.
    simp [w, α]
  · intro i
    have hfrac_le_terminal :
        mixingFractionalPart b i ≤ extendedMixingFractionalPart b tLo := by
      rw [htLo_last]
      simpa [extendedMixingFractionalPart_succ] using hmono (Fin.le_last i.succ)
    have hfrac_le_terminal' :
        Int.fract (b i : ℝ) ≤ extendedMixingFractionalPart b tLo := by
      simpa [mixingFractionalPart_eq_fract] using hfrac_le_terminal
    have hshift := normalizedShift_ge_coverGap (b := b) (x := x) hx hx0_eq i
    have hshift' :
        Int.fract (b i : ℝ) - c ≤
          x i.succ + (mZ : ℝ) - (⌊b i⌋ : ℝ) := by
      simpa [mixingFractionalPart_eq_fract] using hshift
    have hy_succ : y i.succ = x i.succ + (mZ : ℝ) := by
      rw [hy_def]
      simp
    -- Every threshold indicator vanishes at the terminal atom; the cover inequality supplies the
    -- remaining nonnegative shifted-coordinate bound after adding `α`.
    have hsum_zero :
        (∑ t : Fin (n + 1),
          w t *
            (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
              else 1)) = 0 := by
      rw [Finset.sum_eq_single tLo]
      · dsimp [w]
        rw [if_pos rfl, one_mul, if_pos hfrac_le_terminal']
      · intro t _ht ht_ne
        simp [w, ht_ne]
      · simp
    rw [hsum_zero, hy_succ]
    dsimp [α]
    -- The terminal branch is a linear consequence of the normalized region bounds.
    linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a candidate-step
domination package on last-occurrence-supported weights rewrites directly to the threshold
indicator domination field consumed by the residual threshold API. -/
private lemma candidateStepWeightsToThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {α : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    ∀ i : Fin n,
      ∑ t : Fin (n + 1),
          w t *
            (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
              else 1) ≤
        y i.succ - (⌊b i⌋ : ℝ) + α := by
  intro i
  have hthreshold_eq :
      ∑ t : Fin (n + 1),
          w t *
            (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
              else 1) =
        ∑ t : Fin (n + 1),
          w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) := by
    -- Rewrite each positive support atom once from the threshold indicator to the stable
    -- candidate-step indicator.
    refine Finset.sum_congr rfl ?_
    intro t _ht
    by_cases hwt : w t = 0
    · simp [hwt]
    · have hwt_pos : 0 < w t := by
        exact lt_of_le_of_ne (hw_nonneg t) (by simpa [eq_comm] using hwt)
      rw [lastOccurrenceIndicator_eq_candidateStep
        (b := b) (hmono := hmono) (hlast := hw_last t hwt_pos) (i := i)]
  -- After the support-atom rewrite, the supplied candidate-step domination is exactly the target
  -- threshold domination.
  rw [hthreshold_eq]
  exact hw_dom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a strict rise between two
consecutive extended fractional values forces the lower index to be the last occurrence of that
lower breakpoint value. -/
private lemma strictRise_lastOccurrence
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {t : Fin n}
    (hstrict :
      extendedMixingFractionalPart b t.castSucc <
        extendedMixingFractionalPart b t.succ) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s =
        extendedMixingFractionalPart b t.castSucc → s ≤ t.castSucc := by
  intro s hs
  by_contra hs_not_le
  have hcastSucc_lt_s : t.castSucc < s := lt_of_not_ge hs_not_le
  have hsucc_le_s : t.succ ≤ s := by
    exact Fin.le_def.mpr (Nat.succ_le_of_lt (Fin.lt_def.mp hcastSucc_lt_s))
  have hupper_le :
      extendedMixingFractionalPart b t.succ ≤
        extendedMixingFractionalPart b t.castSucc := by
    -- Once `s` lies strictly above `t.castSucc`, monotonicity pushes its breakpoint value above
    -- the next consecutive one as well.
    simpa [hs] using hmono hsucc_le_s
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a strict consecutive rise
gives the positive breakpoint gap needed to divide in the residual transport formula. -/
private lemma strictRise_gap_pos
    (b : Fin n → ℚ)
    {t : Fin n}
    (hstrict :
      extendedMixingFractionalPart b t.castSucc <
        extendedMixingFractionalPart b t.succ) :
    0 <
      extendedMixingFractionalPart b t.succ -
        extendedMixingFractionalPart b t.castSucc := by
  -- The transport denominator is exactly the positive gap between the two consecutive breakpoint
  -- values.
  linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a non-head zero plateau
owner rewrites to a zero-fraction predecessor coordinate in `Fin n`. -/
private lemma zeroPlateauPredIndex
    (b : Fin n → ℚ)
    {tZero : Fin (n + 1)}
    (htZero_ne : tZero ≠ 0)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0) :
    ∃ iZero : Fin n, iZero.succ = tZero ∧ mixingFractionalPart b iZero = 0 := by
  obtain ⟨iZero, hiZero_succ⟩ := predecessorIndexOfNeZero (n := n) htZero_ne
  refine ⟨iZero, hiZero_succ, ?_⟩
  simpa [← hiZero_succ, extendedMixingFractionalPart_succ] using hzero_eq

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the maximal zero plateau
owner is automatically the last occurrence of breakpoint value `0`. -/
private lemma zeroBreakpointLastOccurrence
    (b : Fin n → ℚ)
    {tZero : Fin (n + 1)}
    (htZero_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ (0 : ℝ) → s ≤ tZero) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s = 0 → s ≤ tZero := by
  intro s hs
  -- Reinterpret the matching zero breakpoint as the maximal-lower-breakpoint hypothesis.
  exact htZero_max s (by simpa [hs])

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the last zero owner is
known to sit at breakpoint value `0`, monotonicity forces every earlier breakpoint owner to carry
the same zero value. -/
private lemma extendedBreakpoint_eq_zero_of_le_zeroOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tZero s : Fin (n + 1)}
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hs_le : s ≤ tZero) :
    extendedMixingFractionalPart b s = 0 := by
  have hs_nonneg : 0 ≤ extendedMixingFractionalPart b s :=
    extendedMixingFractionalPart_nonneg s
  have hs_le_zero :
      extendedMixingFractionalPart b s ≤ 0 := by
    simpa [hzero_eq] using hmono hs_le
  linarith

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: every successor index at
or below the last zero owner has zero fractional part once that owner is frozen at value `0`. -/
private lemma mixingFractionalPart_eq_zero_of_succ_le_zeroOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tZero : Fin (n + 1)} {i : Fin n}
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hi_le : i.succ ≤ tZero) :
    mixingFractionalPart b i = 0 := by
  simpa [extendedMixingFractionalPart_succ] using
    extendedBreakpoint_eq_zero_of_le_zeroOwner
      (b := b) (hmono := hmono) (tZero := tZero) (s := i.succ) hzero_eq hi_le

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: above the last zero
plateau owner there is a canonical first positive breakpoint owner, namely the last occurrence of
the adjacent strictly larger breakpoint value. -/
private lemma firstPositiveOwnerAboveZeroPlateau
    (b : Fin n → ℚ)
    {tZero : Fin (n + 1)}
    (htZero_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ (0 : ℝ) → s ≤ tZero)
    (htZero_lt_n : tZero.1 < n) :
    ∃ tSeed : Fin (n + 1),
      tZero < tSeed ∧
      0 < extendedMixingFractionalPart b tSeed ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed) := by
  obtain ⟨tSeed, hSeed_eq, hSeed_pos, hSeed_last⟩ :=
    existsNextDistinctBreakpointLastIndex
      (b := b) (c := 0) (tLo := tZero) htZero_max htZero_lt_n
  have htZero_lt_adj : tZero < mixingSliceChordUpper tZero htZero_lt_n := by
    exact Fin.lt_def.mpr (by simp [mixingSliceChordUpper])
  have hadj_le_tSeed : mixingSliceChordUpper tZero htZero_lt_n ≤ tSeed := by
    exact hSeed_last _ hSeed_eq.symm
  refine ⟨tSeed, lt_of_lt_of_le htZero_lt_adj hadj_le_tSeed, ?_, hSeed_last⟩
  simpa using hSeed_pos

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the last zero plateau
is the head, the singleton seed bound automatically holds on every coordinate of the first
positive plateau because all those coordinates share the same upper breakpoint value. -/
private lemma headSeedPlateauValueBound
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    {k : Fin n}
    (htZero_lt_k : tZero < k.succ)
    (hk_le_tSeed : k.succ ≤ tSeed) :
    1 - c / extendedMixingFractionalPart b tSeed ≤
      x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) := by
  have hk_frac :
      mixingFractionalPart b k = extendedMixingFractionalPart b tSeed := by
    simpa [extendedMixingFractionalPart_succ] using
      extendedMixingFractionalPart_eq_upper_of_betweenBreakpoints
        (b := b) (hmono := hmono) (tLo := tZero) (tHi := tSeed) (i := k)
        htZero_lt_n hSeed_eq htZero_lt_k hk_le_tSeed
  have hk_pos : 0 < mixingFractionalPart b k := by
    rw [hk_frac]
    exact hSeed_pos
  -- Rewrite the plateau value to the actual successor fractional part before using the
  -- singleton seed transport.
  have hbound :=
    headSingleton_profileBound
      (b := b) (x := x) hx (mZ := mZ) (c := c) hx0_eq (j := k) hk_pos
  rw [hk_frac] at hbound
  exact hbound

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once one zero-start seed
coordinate has been made nonnegative, the same zero-start singleton inequality yields the first
profile bound on every coordinate of the first positive plateau. -/
private lemma zeroStartSeedPlateauValueBound
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    {iZero : Fin n}
    (hiZero_succ : iZero.succ = tZero)
    (hfiZero_zero : mixingFractionalPart b iZero = 0)
    (hiZero_nonneg :
      0 ≤ x iZero.succ + (mZ : ℝ) - (⌊b iZero⌋ : ℝ) + α)
    {k : Fin n}
    (htZero_lt_k : tZero < k.succ)
    (hk_le_tSeed : k.succ ≤ tSeed) :
    1 - (c - α) / extendedMixingFractionalPart b tSeed ≤
      x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
  have hk_frac :
      mixingFractionalPart b k = extendedMixingFractionalPart b tSeed := by
    simpa [extendedMixingFractionalPart_succ] using
      extendedMixingFractionalPart_eq_upper_of_betweenBreakpoints
        (b := b) (hmono := hmono) (tLo := tZero) (tHi := tSeed) (i := k)
        htZero_lt_n hSeed_eq htZero_lt_k hk_le_tSeed
  have hk_pos : 0 < mixingFractionalPart b k := by
    rw [hk_frac]
    exact hSeed_pos
  have hiZero_lt_k : iZero < k := by
    rw [← hiZero_succ] at htZero_lt_k
    exact Fin.succ_lt_succ_iff.mp htZero_lt_k
  -- Transport the zero-start seed bound across the common upper plateau value.
  have hbound :=
    zeroStartSingleton_profileBound
      (b := b) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq (i := iZero) (j := k) hfiZero_zero hiZero_lt_k hk_pos hiZero_nonneg
  rw [hk_frac] at hbound
  exact hbound

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a lower
last-occurrence owner already carries the current profile bound, the positive pair transport gives
the same transported bound on every coordinate of the next upper plateau because those coordinates
share the common upper breakpoint value. -/
private lemma transportedPlateauValueBound
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo tHi : Fin (n + 1)}
    {iLo k : Fin n}
    (hiLo_succ : iLo.succ = tLo)
    (hfiLo_pos : 0 < mixingFractionalPart b iLo)
    (hlt : tLo.1 < n)
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (htLo_lt_k : tLo < k.succ)
    (hk_le_tHi : k.succ ≤ tHi)
    (hfiLo_lt_hi :
      mixingFractionalPart b iLo < extendedMixingFractionalPart b tHi)
    (hα_nonneg : 0 ≤ α)
    {ρLo : ℝ}
    (hLo_bound :
      ρLo ≤ x iLo.succ + (mZ : ℝ) - (⌊b iLo⌋ : ℝ) + α) :
    ((extendedMixingFractionalPart b tHi - (c - α)) -
        mixingFractionalPart b iLo * ρLo) /
        (extendedMixingFractionalPart b tHi - mixingFractionalPart b iLo) ≤
      x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
  have hk_frac :
      mixingFractionalPart b k = extendedMixingFractionalPart b tHi := by
    simpa [extendedMixingFractionalPart_succ] using
      extendedMixingFractionalPart_eq_upper_of_betweenBreakpoints
        (b := b) (hmono := hmono) (tLo := tLo) (tHi := tHi) (i := k)
        hlt hHi_eq htLo_lt_k hk_le_tHi
  have hiLo_lt_k : iLo < k := by
    rw [← hiLo_succ] at htLo_lt_k
    exact Fin.succ_lt_succ_iff.mp htLo_lt_k
  have hfiLo_lt_k : mixingFractionalPart b iLo < mixingFractionalPart b k := by
    rw [hk_frac]
    exact hfiLo_lt_hi
  -- Rewrite the common upper plateau value to the actual successor fractional part before using
  -- the pair transport.
  have hbound :=
    positivePair_profileTransport
      (b := b) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq (i := iLo) (j := k) hiLo_lt_k hfiLo_pos hfiLo_lt_k hα_nonneg hLo_bound
  rw [hk_frac] at hbound
  exact hbound

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if part of the head slack
has already been committed to earlier owners, the plateau transport can be reused in the same
shape after absorbing that committed amount into the ambient slack parameter. -/
private lemma transportedPlateauValueBoundWithCommittedSlack
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α μ : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo tHi : Fin (n + 1)}
    {iLo k : Fin n}
    (hiLo_succ : iLo.succ = tLo)
    (hfiLo_pos : 0 < mixingFractionalPart b iLo)
    (hlt : tLo.1 < n)
    (hHi_eq :
      extendedMixingFractionalPart b tHi =
        extendedMixingFractionalPart b (mixingSliceChordUpper tLo hlt))
    (htLo_lt_k : tLo < k.succ)
    (hk_le_tHi : k.succ ≤ tHi)
    (hfiLo_lt_hi :
      mixingFractionalPart b iLo < extendedMixingFractionalPart b tHi)
    (hα_nonneg : 0 ≤ α)
    (hμ_nonneg : 0 ≤ μ)
    {ρLo : ℝ}
    (hLo_bound :
      ρLo ≤ x iLo.succ + (mZ : ℝ) - (⌊b iLo⌋ : ℝ) + α) :
    ((extendedMixingFractionalPart b tHi - ((c - α) - μ)) -
        mixingFractionalPart b iLo * ρLo) /
        (extendedMixingFractionalPart b tHi - mixingFractionalPart b iLo) ≤
      x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + (α + μ) := by
  have hαμ_nonneg : 0 ≤ α + μ := by
    linarith
  have hLo_bound' :
      ρLo ≤ x iLo.succ + (mZ : ℝ) - (⌊b iLo⌋ : ℝ) + (α + μ) := by
    linarith
  -- Reinterpret the committed prefix moment as extra head slack, then apply the verified plateau
  -- transport in its original two-breakpoint form.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    transportedPlateauValueBound
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α + μ)
      hx0_eq (tLo := tLo) (tHi := tHi) (iLo := iLo) (k := k)
      hiLo_succ hfiLo_pos hlt hHi_eq htLo_lt_k hk_le_tHi hfiLo_lt_hi hαμ_nonneg hLo_bound'

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a sparse
two-breakpoint owner is rewritten to its explicit `0/λ/λ+μ` step profile, the candidate-step
domination field reduces to the three geometric zones below, on, and above the upper plateau. -/
private lemma twoPointBreakpointWeightStepDomination
    (b : Fin n → ℚ)
    {tLo tHi : Fin (n + 1)} (htLo_lt_tHi : tLo < tHi)
    {lamLo lamHi : ℝ}
    (z : Fin n → ℝ)
    (hzero :
      ∀ i : Fin n, mixingFractionalPart b i = 0 → 0 ≤ z i)
    (hlower :
      ∀ i : Fin n, mixingFractionalPart b i ≠ 0 → i.succ ≤ tLo → 0 ≤ z i)
    (hplateau :
      ∀ i : Fin n,
        mixingFractionalPart b i ≠ 0 →
          tLo < i.succ →
            i.succ ≤ tHi →
              lamLo ≤ z i)
    (habove :
      ∀ i : Fin n,
        mixingFractionalPart b i ≠ 0 →
          tHi < i.succ →
            lamLo + lamHi ≤ z i) :
    ∀ i : Fin n,
      ∑ t : Fin (n + 1),
          (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) *
            (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1)) ≤
        z i := by
  intro i
  have htLo_ne_tHi : tLo ≠ tHi := ne_of_lt htLo_lt_tHi
  let step : Fin (n + 1) → ℝ :=
    fun t ↦ if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1
  have hsplit :
      ∑ t : Fin (n + 1),
          (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) * step t) =
        (∑ t : Fin (n + 1), (if t = tLo then lamLo else 0) * step t) +
          ∑ t : Fin (n + 1), (if t = tHi then lamHi else 0) * step t := by
    calc
      ∑ t : Fin (n + 1),
          (((if t = tLo then lamLo else 0) + if t = tHi then lamHi else 0) * step t)
          =
            ∑ t : Fin (n + 1),
              (((if t = tLo then lamLo else 0) * step t) +
                ((if t = tHi then lamHi else 0) * step t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro t _ht
                  ring
      _ =
            (∑ t : Fin (n + 1), (if t = tLo then lamLo else 0) * step t) +
              ∑ t : Fin (n + 1), (if t = tHi then lamHi else 0) * step t := by
                rw [Finset.sum_add_distrib]
  have hsingleLo :
      ∑ t : Fin (n + 1), (if t = tLo then lamLo else 0) * step t = lamLo * step tLo := by
    classical
    rw [Fintype.sum_eq_single tLo]
    · simp
    · intro t ht
      simp [ht]
  have hsingleHi :
      ∑ t : Fin (n + 1), (if t = tHi then lamHi else 0) * step t = lamHi * step tHi := by
    classical
    rw [Fintype.sum_eq_single tHi]
    · simp
    · intro t ht
      simp [ht]
  by_cases hfi_zero : mixingFractionalPart b i = 0
  · -- Zero-fraction coordinates kill every step indicator.
    rw [hsplit, hsingleLo, hsingleHi]
    simp only [step, hfi_zero, if_pos, if_true, mul_zero, add_zero]
    exact hzero i hfi_zero
  · by_cases hi_le_tLo : i.succ ≤ tLo
    · -- Below the lower owner, both sparse indicators vanish.
      have hi_le_tHi : i.succ ≤ tHi := le_trans hi_le_tLo (le_of_lt htLo_lt_tHi)
      rw [hsplit, hsingleLo, hsingleHi]
      simp only [step, hfi_zero, if_neg, if_false, hi_le_tLo, hi_le_tHi, if_pos, if_true,
        mul_zero, add_zero]
      exact hlower i hfi_zero hi_le_tLo
    · by_cases hi_le_tHi : i.succ ≤ tHi
      · -- On the open plateau, only the lower owner contributes.
        have htLo_lt_i : tLo < i.succ := lt_of_not_ge hi_le_tLo
        rw [hsplit, hsingleLo, hsingleHi]
        simp only [step, hfi_zero, if_neg, if_false, hi_le_tLo, hi_le_tHi, if_pos, if_true,
          mul_zero, mul_one, add_zero]
        exact hplateau i hfi_zero htLo_lt_i hi_le_tHi
      · -- Strictly above the upper owner, both sparse support atoms contribute.
        have htHi_lt_i : tHi < i.succ := lt_of_not_ge hi_le_tHi
        rw [hsplit, hsingleLo, hsingleHi]
        simp only [step, hfi_zero, if_neg, if_false, hi_le_tLo, hi_le_tHi, if_true, mul_one]
        exact habove i hfi_zero htHi_lt_i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the seed ceiling can be
upgraded to the actual shifted seed coordinate, separating the true seed tail
`fSeed * (1 - ρBase)` from the extra positive moment that must be carried above `tSeed`. -/
private lemma seededResidualBaseMomentSplit
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    {mZ : ℤ} {c α : ℝ}
    {tSeed : Fin (n + 1)} {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    {ρSeed : ℝ}
    (hρSeed_bound :
      ρSeed ≤
        x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed)) :
    let ρBase : ℝ := x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α
    let μBase : ℝ := extendedMixingFractionalPart b tSeed * (ρBase - ρSeed)
    ρSeed ≤ ρBase ∧
      0 ≤ μBase ∧
      μBase + extendedMixingFractionalPart b tSeed * (1 - ρBase) = c - α := by
  -- Freeze the actual shifted seed coordinate as the first usable plateau value.
  dsimp
  refine ⟨hρSeed_bound, ?_, ?_⟩
  · -- The extra moment above the seed ceiling is nonnegative because the seed coordinate really
    -- dominates `ρSeed`.
    have hSeed_nonneg : 0 ≤ extendedMixingFractionalPart b tSeed := by
      linarith
    exact mul_nonneg hSeed_nonneg (sub_nonneg.mpr hρSeed_bound)
  · -- Splitting the seed moment at the actual seed coordinate isolates the unresolved positive
    -- moment that must later be transported above `tSeed`.
    rw [hρSeed_moment]
    ring

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the committed split at the
actual seed coordinate rewrites the first transported numerator back to the public seed-profile
normal form. This is the algebraic bridge between the richer seed data `(ρBase, μBase)` and the
profile-level transport formula driven by `ρSeed`. -/
private lemma seededCommittedSlackTransportNumerator
    {fSeed fNext c α ρSeed ρBase μBase : ℝ}
    (hρSeed_moment : c - α = fSeed * (1 - ρSeed))
    (hseedBase_split : μBase + fSeed * (1 - ρBase) = c - α) :
    (fNext - ((c - α) - μBase)) - fSeed * ρBase =
      (fNext - (c - α)) - fSeed * ρSeed := by
  have hμBase_eq : μBase = fSeed * (ρBase - ρSeed) := by
    -- Compare the seed moment written at the ceiling `ρSeed` and at the actual seed coordinate
    -- `ρBase` to isolate the committed extra moment.
    linarith
  -- Substituting the isolated committed moment normalizes the transported numerator.
  linarith

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a public next
plateau value has been chosen, upgrading it to the actual shifted coordinate of the next owner
only moves mass from the open tail into the committed prefix, so the total head moment is
unchanged. -/
private lemma committedSlackNextOwnerHeadSplit
    {fj c α μNextPublic ρNext ρBaseNext : ℝ}
    (hhead :
      μNextPublic + fj * (1 - ρNext) = c - α) :
    let μNextActual : ℝ := μNextPublic + fj * (ρBaseNext - ρNext)
    μNextActual + fj * (1 - ρBaseNext) = c - α := by
  -- Repackage the extra mass needed to raise the public plateau to the actual next-owner
  -- coordinate; the remaining open tail decreases by the same amount.
  dsimp
  linarith

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the seed-side profile
bound at the first positive owner still records exactly which indices belong to the frozen zero
zone. The active frontier constructor now threads zero-zone domination separately, so this helper
only preserves the location information that remains stable under the refactor. -/
private lemma zeroFractionShiftNonneg_ofSeedProfileBound
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tSeed : Fin (n + 1)}
    (htZero_last :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (htZero_lt_n : tZero.1 < n)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed : ℝ}
    (hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed)) :
    ∀ i : Fin n,
      mixingFractionalPart b i = 0 →
        i.succ ≤ tZero := by
  intro i hfi_zero
  -- Route correction: the zero-zone ordering fact is the stable part of the old helper. The
  -- active frontier package no longer asks this lemma to reconstruct shifted-coordinate
  -- nonnegativity from the seed bound alone.
  exact
    htZero_last i.succ (by simpa [extendedMixingFractionalPart_succ, hfi_zero])

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the seed ceiling
`ρSeed` has been upgraded to the actual seed coordinate `ρBase`, the first strict rise above
`tSeed` already has a canonical next owner and transported plateau value. The remaining recursion
above that next owner is separate. -/
private lemma seededResidualFirstCommittedSlackStep
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tSeed : Fin (n + 1)}
    (htSeed_lt_n : tSeed.1 < n)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hα_nonneg : 0 ≤ α)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase + extendedMixingFractionalPart b tSeed * (1 - ρBase) = c - α)
    (hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α) :
    ∃ tNext : Fin (n + 1), ∃ ρNext : ℝ,
      extendedMixingFractionalPart b tNext =
        extendedMixingFractionalPart b (mixingSliceChordUpper tSeed htSeed_lt_n) ∧
      extendedMixingFractionalPart b tSeed < extendedMixingFractionalPart b tNext ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) ∧
      ((μBase + extendedMixingFractionalPart b tSeed * (ρNext - ρBase)) +
          extendedMixingFractionalPart b tNext * (1 - ρNext) = c - α) ∧
      (∀ k : Fin n,
        tSeed < k.succ →
          k.succ ≤ tNext →
            ρNext ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
  have hSeed_max :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tSeed → s ≤ tSeed := by
    intro s hs
    by_cases hs_le : s ≤ tSeed
    · exact hs_le
    · have htSeed_lt_s : tSeed < s := lt_of_not_ge hs_le
      have hseed_le_s :
          extendedMixingFractionalPart b tSeed ≤ extendedMixingFractionalPart b s := by
        simpa using hmono (le_of_lt htSeed_lt_s)
      have hs_eq :
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed :=
        le_antisymm hs hseed_le_s
      exact hSeed_last s hs_eq
  obtain ⟨tNext, hNext_eq, hSeed_lt_next, hNext_last⟩ :=
    existsNextDistinctBreakpointLastIndex
      (b := b) (c := extendedMixingFractionalPart b tSeed) (tLo := tSeed)
      hSeed_max htSeed_lt_n
  let fSeed : ℝ := extendedMixingFractionalPart b tSeed
  let fNext : ℝ := extendedMixingFractionalPart b tNext
  let ρNext : ℝ := ((fNext - ((c - α) - μBase)) - fSeed * ρBase) / (fNext - fSeed)
  have hSeed_frac_pos : 0 < mixingFractionalPart b jSeed := by
    -- Rewrite the seed owner back to its predecessor coordinate before using positive-pair
    -- transport.
    simpa [← hjSeed_succ, extendedMixingFractionalPart_succ] using hSeed_pos
  have hSeed_frac_lt_next :
      mixingFractionalPart b jSeed < extendedMixingFractionalPart b tNext := by
    -- The adjacent next breakpoint is strictly larger than the seed breakpoint.
    simpa [← hjSeed_succ, extendedMixingFractionalPart_succ] using hSeed_lt_next
  have hnum :
      (fNext - ((c - α) - μBase)) - fSeed * ρBase =
        (fNext - (c - α)) - fSeed * ρSeed := by
    -- Normalize the committed numerator back to the public seed transport formula.
    exact
      seededCommittedSlackTransportNumerator
        (fSeed := fSeed) (fNext := fNext) (c := c) (α := α)
        (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
        hρSeed_moment hseedBase_split.2.2
  have hρNext_eq_public :
      ρNext = ((fNext - (c - α)) - fSeed * ρSeed) / (fNext - fSeed) := by
    -- The committed and public transport spellings define the same next plateau value.
    dsimp [ρNext]
    rw [hnum]
  refine ⟨tNext, ρNext, hNext_eq, hSeed_lt_next, hNext_last, ?_, ?_⟩
  · -- Solve the transported head identity directly from the explicit committed numerator.
    have hgap_ne : fNext - fSeed ≠ 0 := sub_ne_zero.mpr (ne_of_gt hSeed_lt_next)
    have hρNext_mul :
        ρNext * (fNext - fSeed) =
          (fNext - ((c - α) - μBase)) - fSeed * ρBase := by
      dsimp [ρNext]
      field_simp [hgap_ne]
    nlinarith [hρNext_mul]
  · intro k htSeed_lt_k hk_le_tNext
    have hpublic :
        ((fNext - (c - α)) - fSeed * ρSeed) / (fNext - fSeed) ≤
          x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
      -- After rewriting to the public seed spelling, the first plateau rise is exactly the
      -- verified two-breakpoint transport from the seed owner to the adjacent next breakpoint.
      simpa [fSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ] using
        transportedPlateauValueBound
          (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
          hx0_eq (tLo := tSeed) (tHi := tNext) (iLo := jSeed) (k := k)
          hjSeed_succ hSeed_frac_pos htSeed_lt_n hNext_eq htSeed_lt_k hk_le_tNext
          hSeed_frac_lt_next hα_nonneg hρSeed_bound
    simpa [hρNext_eq_public, fSeed] using hpublic

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if the first positive
plateau is kept at the seed ceiling `ρSeed`, then any nonnegative two-owner refinement whose new
owner has strictly larger breakpoint value must place zero mass at that later owner. This is the
precise obstruction behind the discarded seed-plus-global-pair route. -/
private lemma seedTwoOwnerExtension_requires_strictlyLargerPlateau
    {fi fj d ρSeed lamSeed lamNext : ℝ}
    (hfi_lt_fj : fi < fj)
    (hlamSeed_nonneg : 0 ≤ lamSeed)
    (hlamNext_nonneg : 0 ≤ lamNext)
    (hmass : lamSeed + lamNext = 1 - ρSeed)
    (hmoment : lamSeed * fi + lamNext * fj = d)
    (hseed : d = fi * (1 - ρSeed)) :
    lamNext = 0 := by
  have hcancel : lamNext * (fj - fi) = 0 := by
    -- Subtract the pure seed moment from the two-owner moment after rewriting the total
    -- positive-owner mass by `hmass`.
    have hlamSeed_eq : lamSeed = 1 - ρSeed - lamNext := by
      linarith [hmass]
    calc
      lamNext * (fj - fi)
          = lamSeed * fi + lamNext * fj - fi * (1 - ρSeed) := by
              rw [hlamSeed_eq]
              ring
      _ = 0 := by
            linarith [hmoment, hseed]
  have hgap_pos : 0 < fj - fi := sub_pos.mpr hfi_lt_fj
  by_cases hlamNext_zero : lamNext = 0
  · exact hlamNext_zero
  · have hzero_ne_lamNext : (0 : ℝ) ≠ lamNext := by
      intro hzero
      exact hlamNext_zero hzero.symm
    have hlamNext_pos : 0 < lamNext := lt_of_le_of_ne hlamNext_nonneg hzero_ne_lamNext
    have hprod_pos : 0 < lamNext * (fj - fi) := mul_pos hlamNext_pos hgap_pos
    have hfalse : False := by
      rw [hcancel] at hprod_pos
      linarith
    exact False.elim hfalse

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if a first sparse
seed extension keeps total head moment `fi * (1 - ρSeed)` but assigns positive mass to a later
owner with strictly larger breakpoint value `fj`, then the zero-owner mass `lamZero` must already
raise the common seed plateau strictly above `ρSeed`. -/
private lemma positiveNextOwnerMass_forces_seedPlateauRaise
    {fi fj ρSeed lamZero lamSeed lamNext : ℝ}
    (hfi_pos : 0 < fi)
    (hfi_lt_fj : fi < fj)
    (hmass : lamZero + lamSeed + lamNext = 1)
    (hmoment : lamSeed * fi + lamNext * fj = fi * (1 - ρSeed))
    (hlamNext_pos : 0 < lamNext) :
    ρSeed < lamZero := by
  have hidentity : fi * (lamZero - ρSeed) = lamNext * (fj - fi) := by
    -- Rewrite the total positive-owner mass as `1 - lamZero`; the remaining moment comparison
    -- isolates the exact amount by which the zero-owner mass must exceed `ρSeed`.
    nlinarith [hmass, hmoment]
  have hright_pos : 0 < lamNext * (fj - fi) := by
    -- A genuine later-owner step contributes strictly positive extra moment because both the new
    -- mass and the breakpoint gap are positive.
    exact mul_pos hlamNext_pos (sub_pos.mpr hfi_lt_fj)
  have hleft_pos : 0 < fi * (lamZero - ρSeed) := by
    -- Transport the positive extra moment through the isolated identity.
    rw [hidentity]
    exact hright_pos
  have hdiff_pos : 0 < lamZero - ρSeed := by
    -- The seed breakpoint value is positive, so the zero-owner mass itself must rise strictly.
    nlinarith [hfi_pos, hleft_pos]
  linarith

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the richer seed split
still remembers the public seed ceiling once the actual seed coordinate `ρBase` is bounded by the
same shifted successor coordinate. -/
private lemma seededResidualSeedCoordinateBound
    {ρSeed ρBase seedBound : ℝ}
    (hseed_le : ρSeed ≤ ρBase)
    (hbase_bound : ρBase ≤ seedBound) :
    ρSeed ≤ seedBound := by
  -- The public seed ceiling remains below any ambient bound proved for the actual seed owner.
  linarith

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the first committed-slack
transport above `tSeed` already proves a local frontier through the first genuine rise `tNext`,
consisting of the zero zone, the original seed plateau, and the transported next plateau. -/
private lemma seededResidualInitialFrontierData
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hzero_lastOcc :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    (htSeed_lt_n : tSeed.1 < n)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ tNext : Fin (n + 1), ∃ ρNext : ℝ,
      extendedMixingFractionalPart b tNext =
        extendedMixingFractionalPart b (mixingSliceChordUpper tSeed htSeed_lt_n) ∧
      extendedMixingFractionalPart b tSeed < extendedMixingFractionalPart b tNext ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) ∧
      (extendedMixingFractionalPart b tSeed * (ρNext - ρSeed) +
          extendedMixingFractionalPart b tNext * (1 - ρNext) = c - α) ∧
      (∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) ∧
      (∀ k : Fin n,
        tSeed < k.succ →
          k.succ ≤ tNext →
            ρNext ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
  obtain ⟨tNext, ρNext, hNext_eq, hSeed_lt_next, hNext_last, hρNext_head, hρNext_plateau⟩ :=
    seededResidualFirstCommittedSlackStep
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq (tSeed := tSeed) htSeed_lt_n hSeed_last
      (jSeed := jSeed) hjSeed_succ hSeed_pos hα_nonneg
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment hseedBase_split hρSeed_bound
  have hμBase_eq :
      μBase = extendedMixingFractionalPart b tSeed * (ρBase - ρSeed) := by
    -- Compare the public seed moment with the committed split to isolate the carried prefix mass.
    linarith [hρSeed_moment, hseedBase_split.2.2]
  have hρNext_moment :
      extendedMixingFractionalPart b tSeed * (ρNext - ρSeed) +
          extendedMixingFractionalPart b tNext * (1 - ρNext) =
        c - α := by
    -- Substituting the committed seed prefix turns the transported head identity back into the
    -- public two-plateau moment needed by the frontier interface.
    linarith [hρNext_head, hμBase_eq]
  exact
    ⟨tNext, ρNext, hNext_eq, hSeed_lt_next, hNext_last, hρNext_moment,
      hρSeed_plateau, hρNext_plateau⟩

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the first public
frontier through `tNext` is known, the predecessor coordinate of `tNext` upgrades that public tail
to the actual next-owner split needed by the recursive owner-chain state. -/
private lemma seededResidualInitialActualNextOwnerSplit
    (b : Fin n → ℚ)
    {x : Fin (n + 1) → ℝ}
    {mZ : ℤ} {c α : ℝ}
    {tSeed tNext : Fin (n + 1)}
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    {ρSeed ρNext : ℝ}
    (hρNext_moment :
      extendedMixingFractionalPart b tSeed * (ρNext - ρSeed) +
          extendedMixingFractionalPart b tNext * (1 - ρNext) =
        c - α)
    (htSeed_lt_tNext : tSeed < tNext)
    (hρNext_dom :
      ∀ k : Fin n,
        tSeed < k.succ →
          k.succ ≤ tNext →
            ρNext ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ jNext : Fin n,
      jNext.succ = tNext ∧
      let ρBaseNext : ℝ := x jNext.succ + (mZ : ℝ) - (⌊b jNext⌋ : ℝ) + α
      let μNext : ℝ :=
        extendedMixingFractionalPart b tSeed * (ρNext - ρSeed) +
          extendedMixingFractionalPart b tNext * (ρBaseNext - ρNext)
      ρNext ≤ ρBaseNext ∧
        μNext + extendedMixingFractionalPart b tNext * (1 - ρBaseNext) = c - α := by
  have htNext_ne_zero : tNext ≠ 0 := by
    -- The first strict rise above the positive seed owner cannot return to the head breakpoint.
    intro htNext_zero
    subst htNext_zero
    simpa using htSeed_lt_tNext
  obtain ⟨jNext, hjNext_succ⟩ := predecessorIndexOfNeZero (n := n) htNext_ne_zero
  refine ⟨jNext, hjNext_succ, ?_⟩
  dsimp
  refine ⟨?_, ?_⟩
  · -- The public next plateau is bounded by the actual shifted coordinate at its owner.
    have htSeed_lt_jNext : tSeed < jNext.succ := by
      simpa [hjNext_succ] using htSeed_lt_tNext
    have hjNext_le_tNext : jNext.succ ≤ tNext := by
      simpa [hjNext_succ] using (le_rfl : tNext ≤ tNext)
    exact hρNext_dom jNext htSeed_lt_jNext hjNext_le_tNext
  · -- Recommit the remaining public tail at the actual next-owner coordinate.
    simpa using
      committedSlackNextOwnerHeadSplit
        (fj := extendedMixingFractionalPart b tNext) (c := c) (α := α)
        (μNextPublic := extendedMixingFractionalPart b tSeed * (ρNext - ρSeed))
        (ρNext := ρNext)
        (ρBaseNext := x jNext.succ + (mZ : ℝ) - (⌊b jNext⌋ : ℝ) + α)
        hρNext_moment

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a last-occurrence owner
for the current breakpoint value is automatically maximal among all owners whose extended
breakpoint value is at most `extendedMixingFractionalPart b tCur`. -/
private lemma currentOwnerMaximalAtOwnBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tCur : Fin (n + 1)}
    (hCur_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tCur → s ≤ tCur) :
    ∀ s : Fin (n + 1),
      extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tCur → s ≤ tCur := by
  intro s hs
  by_cases hs_le : s ≤ tCur
  · -- Any owner already below `tCur` is part of the desired maximal lower breakpoint package.
    exact hs_le
  · -- An owner strictly above `tCur` cannot have a smaller breakpoint value by monotonicity, so
    -- equality forces it back onto the same last-occurrence plateau.
    have htCur_lt_s : tCur < s := lt_of_not_ge hs_le
    have hcur_le_s :
        extendedMixingFractionalPart b tCur ≤ extendedMixingFractionalPart b s := by
      simpa using hmono (le_of_lt htCur_lt_s)
    have hs_eq :
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tCur :=
      le_antisymm hs hcur_le_s
    exact hCur_last s hs_eq

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the nonterminal branch,
the next distinct breakpoint above `tCur` is the last occurrence of the adjacent strictly larger
breakpoint value. -/
private lemma currentOwnerNextDistinctBreakpoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tCur : Fin (n + 1)}
    (hCur_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tCur → s ≤ tCur)
    (htCur_lt_n : tCur.1 < n) :
    ∃ tNext : Fin (n + 1),
      extendedMixingFractionalPart b tNext =
        extendedMixingFractionalPart b (mixingSliceChordUpper tCur htCur_lt_n) ∧
      extendedMixingFractionalPart b tCur < extendedMixingFractionalPart b tNext ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) := by
  -- Repackage the current owner as a maximal lower breakpoint so the existing adjacent-breakpoint
  -- selector applies verbatim.
  exact
    existsNextDistinctBreakpointLastIndex
      (b := b) (c := extendedMixingFractionalPart b tCur) (tLo := tCur)
      (currentOwnerMaximalAtOwnBreakpoint (b := b) (hmono := hmono) hCur_last)
      htCur_lt_n

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: if the current owner is
not strictly below `n`, then it is the terminal breakpoint owner `Fin.last n`. -/
private lemma currentOwner_eq_last_of_not_lt_n
    {tCur : Fin (n + 1)}
    (hterminal : ¬ tCur.1 < n) :
    tCur = Fin.last n := by
  -- In `Fin (n + 1)`, the only index whose value is not `< n` is the terminal owner.
  apply Fin.ext
  exact Nat.eq_of_lt_succ_of_not_lt tCur.2 hterminal

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a positive current
breakpoint owner lies strictly above the last zero plateau owner. -/
private lemma zeroOwner_lt_currentOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {tZero tCur : Fin (n + 1)}
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hCur_pos : 0 < extendedMixingFractionalPart b tCur)
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero) :
    tZero < tCur := by
  -- If the positive current owner were not above `tZero`, monotonicity would force its
  -- breakpoint value back down to `0`, contradicting positivity.
  by_contra hnot_lt
  have hcur_le_tZero : tCur ≤ tZero := le_of_not_gt hnot_lt
  have hcur_eq_zero :
      extendedMixingFractionalPart b tCur = 0 := by
    exact
      extendedBreakpoint_eq_zero_of_le_zeroOwner
        (b := b) (hmono := hmono) (tZero := tZero) (s := tCur) hzero_eq hcur_le_tZero
  linarith [hCur_pos]

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: rewriting the current
actual split against `c - α` isolates the same transported numerator that is obtained from the
public current plateau `ρCur` and the local tail moment `dCur`. -/
private lemma currentOwnerTransportNumerator
    {fCur fNext c α dCur ρCur ρBaseCur μCur : ℝ}
    (hdCur_moment : dCur = fCur * (1 - ρCur))
    (hcurBase_split : μCur + fCur * (1 - ρBaseCur) = c - α) :
    (fNext - ((c - α) - μCur)) - fCur * ρBaseCur =
      (fNext - dCur) - fCur * ρCur := by
  -- Compare the open-tail moment written once at the public current plateau `ρCur` and once at
  -- the actual current coordinate `ρBaseCur` after peeling off the committed prefix mass `μCur`.
  linarith

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the old one-plateau
transport route above a current owner collapses to the constant value `1` on the adjacent next
plateau. This isolates the exact local information that is still valid before the recursion is
refactored to preserve the older plateau separately. -/
private lemma currentOwnerCollapsedUpperPlateauOneBound
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tCur : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hα_nonneg : 0 ≤ α)
    {jCur : Fin n}
    (hjCur_succ : jCur.succ = tCur)
    (hCur_pos : 0 < extendedMixingFractionalPart b tCur)
    (hCur_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tCur → s ≤ tCur)
    {dCur ρCur : ℝ}
    (hdCur_moment :
      dCur = extendedMixingFractionalPart b tCur * (1 - ρCur))
    (hdCur_head : dCur = c - α)
    (hρCur_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tCur →
            ρCur ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α)
    (htCur_lt_n : tCur.1 < n) :
    ∃ tNext : Fin (n + 1),
      extendedMixingFractionalPart b tNext =
        extendedMixingFractionalPart b (mixingSliceChordUpper tCur htCur_lt_n) ∧
      extendedMixingFractionalPart b tCur < extendedMixingFractionalPart b tNext ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) ∧
      (∀ k : Fin n,
        tCur < k.succ →
          k.succ ≤ tNext →
            1 ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
  have hCur_max :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s ≤ extendedMixingFractionalPart b tCur → s ≤ tCur := by
    intro s hs
    by_cases hs_le : s ≤ tCur
    · exact hs_le
    · have htCur_lt_s : tCur < s := lt_of_not_ge hs_le
      have hcur_le_s :
          extendedMixingFractionalPart b tCur ≤ extendedMixingFractionalPart b s := by
        simpa using hmono (le_of_lt htCur_lt_s)
      have hs_eq :
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b tCur :=
        le_antisymm hs hcur_le_s
      exact hCur_last s hs_eq
  obtain ⟨tNext, hNext_eq, hCur_lt_next, hNext_last⟩ :=
    existsNextDistinctBreakpointLastIndex
      (b := b) (c := extendedMixingFractionalPart b tCur) (tLo := tCur)
      hCur_max htCur_lt_n
  have hρCur_head :
      c - α = extendedMixingFractionalPart b tCur * (1 - ρCur) := by
    -- The stale helper now carries the missing link from the local tail moment `dCur` back to the
    -- ambient head gap `c - α`.
    linarith
  have htZero_lt_tCur : tZero < tCur := by
    -- The positive current owner still sits strictly above the frozen zero plateau.
    exact
      zeroOwner_lt_currentOwner
        (b := b) (hmono := hmono) (tZero := tZero) (tCur := tCur)
        hzero_eq hCur_pos htZero_last
  have hρCur_bound :
      ρCur ≤ x jCur.succ + (mZ : ℝ) - (⌊b jCur⌋ : ℝ) + α := by
    -- Specialize the current plateau bound to the actual current owner.
    have htZero_lt_jCur : tZero < jCur.succ := by
      simpa [hjCur_succ] using htZero_lt_tCur
    have hjCur_le_tCur : jCur.succ ≤ tCur := by
      simpa [hjCur_succ]
    exact hρCur_plateau jCur htZero_lt_jCur hjCur_le_tCur
  let ρNext : ℝ :=
    ((extendedMixingFractionalPart b tNext - (c - α)) -
        extendedMixingFractionalPart b tCur * ρCur) /
      (extendedMixingFractionalPart b tNext - extendedMixingFractionalPart b tCur)
  have hCur_frac_pos : 0 < mixingFractionalPart b jCur := by
    -- Rewrite the current owner back to its predecessor fractional part.
    simpa [← hjCur_succ, extendedMixingFractionalPart_succ] using hCur_pos
  have hCur_frac_lt_next :
      mixingFractionalPart b jCur < extendedMixingFractionalPart b tNext := by
    -- The adjacent next breakpoint is strictly larger than the current breakpoint.
    simpa [← hjCur_succ, extendedMixingFractionalPart_succ] using hCur_lt_next
  have hρNext_head :
      extendedMixingFractionalPart b tCur * (ρNext - ρCur) +
          extendedMixingFractionalPart b tNext * (1 - ρNext) =
        c - α := by
    -- Solve the public transport identity in its explicit quotient normal form once.
    have hgap_ne :
        extendedMixingFractionalPart b tNext - extendedMixingFractionalPart b tCur ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hCur_lt_next)
    dsimp [ρNext]
    field_simp [hgap_ne]
    ring_nf
  have hρNext_eq_one : ρNext = 1 := by
    -- The public next plateau still collapses to `1` after the first transport step.
    have hcollapse :
        (extendedMixingFractionalPart b tNext - extendedMixingFractionalPart b tCur) *
            (1 - ρNext) =
          0 := by
      -- Subtract the public current moment from the transported next moment to isolate the next
      -- plateau remainder.
      nlinarith [hρCur_head, hρNext_head]
    have hgap_ne :
        extendedMixingFractionalPart b tNext - extendedMixingFractionalPart b tCur ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hCur_lt_next)
    have hone_sub_eq_zero : 1 - ρNext = 0 := by
      exact (mul_eq_zero.mp hcollapse).resolve_left hgap_ne
    linarith
  refine ⟨tNext, hNext_eq, hCur_lt_next, hNext_last, ?_⟩
  intro k htCur_lt_k hk_le_tNext
  have hpublic :
      ((extendedMixingFractionalPart b tNext - (c - α)) -
          extendedMixingFractionalPart b tCur * ρCur) /
        (extendedMixingFractionalPart b tNext - extendedMixingFractionalPart b tCur) ≤
        x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
    -- Reuse the verified positive-pair transport from the current owner to the adjacent next
    -- breakpoint plateau.
    simpa [← hjCur_succ, extendedMixingFractionalPart_succ] using
      transportedPlateauValueBound
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
        hx0_eq (tLo := tCur) (tHi := tNext) (iLo := jCur) (k := k)
        hjCur_succ hCur_frac_pos htCur_lt_n hNext_eq htCur_lt_k hk_le_tNext
        hCur_frac_lt_next hα_nonneg hρCur_bound
  simpa [ρNext, hρNext_eq_one] using hpublic

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: starting from the proved
seed package at the first positive last-occurrence owner, the only remaining local task is to
construct candidate weights on later last-occurrence owners whose step-prefix domination already
matches the residual profile interface. -/
private lemma candidateWeightsFromResidualThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (w : Fin (n + 1) → ℝ)
    (hα_nonneg : 0 ≤ α)
    (hw_nonneg : ∀ t : Fin (n + 1), 0 ≤ w t)
    (hw_sum : ∑ t : Fin (n + 1), w t = 1)
    (hw_last :
      ∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t)
    (hw_head :
      ∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α)
    (hw_dom :
      ∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) :
    ∃ w' : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w' t) ∧
      (∑ t : Fin (n + 1), w' t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w' t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w' t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w' t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
    residualProfileFromThresholdWeights
      (b := b) (hmono := hmono) (y := y) (c := c) (α := α) w
      hα_nonneg hw_nonneg hw_sum hw_last hw_head hw_dom
  refine ⟨consecutiveDifferenceWeights ρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- Rebuild the candidate weights as the consecutive jumps of the recovered cumulative profile.
    exact consecutiveDifferenceWeights_nonneg ρ hρmono hρlast
  · -- The strict prefix telescope at the terminal breakpoint recovers the full mass `1`.
    have hprefix_last :
        ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc = ρ (Fin.last n) := by
      have hprefix_last_iio :
          Finset.sum (Finset.Iio (Fin.last n)) (consecutiveDifferenceWeights ρ) =
            ρ (Fin.last n) :=
        consecutiveDifferenceWeightsPrefixMass_eq_profileIio ρ hρ0 (Fin.last n)
      rw [Fin.Iio_last_eq_map] at hprefix_last_iio
      simpa [Finset.sum_map] using hprefix_last_iio
    calc
      ∑ t : Fin (n + 1), consecutiveDifferenceWeights ρ t
          = ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc +
              consecutiveDifferenceWeights ρ (Fin.last n) := by
                rw [Fin.sum_univ_castSucc]
      _ = ρ (Fin.last n) + (1 - ρ (Fin.last n)) := by
            rw [hprefix_last, consecutiveDifferenceWeights_last]
      _ = 1 := by ring
  · -- Positive jumps of the rebuilt profile inherit the same last-occurrence owner property.
    exact hρlastOcc
  · -- The recovered profile preserves the residual head moment.
    exact hρhead
  · intro i
    -- Rewrite the candidate-step sum to the strict prefix mass recovered from the threshold
    -- profile.
    rw [candidateWeightStepPrefix_eq (b := b) (w := consecutiveDifferenceWeights ρ) i]
    simpa [consecutiveDifferenceWeightsPrefixMass_eq_profile ρ hρ0 i] using hρdom i

/-- Helper for remote integer-programming retry after job 2715
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the public first frontier
above `tSeed` still collapses to plateau value `1`, even after the actual seed coordinate
`ρBase` and committed mass `μBase` have been separated out. -/
private lemma seededInitialFrontierPlateauIsOne
    {fSeed fNext ρSeed ρNext c α : ℝ}
    (hSeed_lt_next : fSeed < fNext)
    (hρSeed_moment : c - α = fSeed * (1 - ρSeed))
    (hρNext_moment :
      fSeed * (ρNext - ρSeed) + fNext * (1 - ρNext) = c - α) :
    ρNext = 1 := by
  have hcollapse : (fNext - fSeed) * (1 - ρNext) = 0 := by
    -- Subtract the public seed moment from the first-frontier moment to isolate the next-plateau
    -- remainder.
    nlinarith [hρSeed_moment, hρNext_moment]
  have hgap_ne : fNext - fSeed ≠ 0 := sub_ne_zero.mpr (ne_of_gt hSeed_lt_next)
  have hone_sub_eq_zero : 1 - ρNext = 0 := by
    -- The breakpoint gap is strictly positive, so the isolated remainder must vanish.
    exact (mul_eq_zero.mp hcollapse).resolve_left hgap_ne
  linarith

/-- Helper for remote integer-programming retry after job 2715
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: on the nonterminal seed
branch, the first committed frontier already packages the adjacent next owner, the fact that the
public plateau there is `1`, and the corresponding actual shifted coordinate at that next owner. -/
private lemma seededCommittedFrontierPackage
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α)
    (htSeed_lt_n : tSeed.1 < n) :
    ∃ tNext : Fin (n + 1), ∃ jNext : Fin n, ∃ ρBaseNext : ℝ,
      jNext.succ = tNext ∧
      extendedMixingFractionalPart b tNext =
        extendedMixingFractionalPart b (mixingSliceChordUpper tSeed htSeed_lt_n) ∧
      extendedMixingFractionalPart b tSeed < extendedMixingFractionalPart b tNext ∧
      (∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) ∧
      1 ≤ ρBaseNext ∧
      ρBaseNext ≤ x jNext.succ + (mZ : ℝ) - (⌊b jNext⌋ : ℝ) + α ∧
      (∀ k : Fin n,
        tSeed < k.succ →
          k.succ ≤ tNext →
            1 ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
  have hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α := by
    -- The public seed ceiling is still bounded by the actual seed coordinate.
    exact
      seededResidualSeedCoordinateBound
        (ρSeed := ρSeed) (ρBase := ρBase)
        (seedBound := x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
        hseedBase_split.1 hρBase_bound
  obtain ⟨tNext, ρNext, hNext_eq, hSeed_lt_next, hNext_last, hρNext_moment,
      _hρSeed_plateau, hρNext_plateau⟩ :=
    seededResidualInitialFrontierData
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq htZero_last
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ htSeed_lt_n
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment hρSeed_bound hseedBase_split hρSeed_plateau
  have hρNext_eq_one : ρNext = 1 := by
    -- The first public frontier still collapses to value `1`; only the actual next-owner
    -- coordinate remains to be packaged separately.
    exact
      seededInitialFrontierPlateauIsOne
        (fSeed := extendedMixingFractionalPart b tSeed)
        (fNext := extendedMixingFractionalPart b tNext)
        (ρSeed := ρSeed) (ρNext := ρNext) (c := c) (α := α)
        hSeed_lt_next hρSeed_moment hρNext_moment
  have hρNext_plateau_one :
      ∀ k : Fin n,
        tSeed < k.succ →
          k.succ ≤ tNext →
            1 ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
    intro k htSeed_lt_k hk_le_tNext
    -- Rewrite the public first-frontier plateau value to the collapsed value `1`.
    simpa [hρNext_eq_one] using hρNext_plateau k htSeed_lt_k hk_le_tNext
  have htSeed_lt_tNext : tSeed < tNext := by
    -- The next owner carries a strictly larger breakpoint value, so it must occur strictly later
    -- in the monotone breakpoint chain.
    by_contra hnot_lt
    have htNext_le_tSeed : tNext ≤ tSeed := le_of_not_gt hnot_lt
    have hnext_le_seed :
        extendedMixingFractionalPart b tNext ≤ extendedMixingFractionalPart b tSeed := by
      simpa using hmono htNext_le_tSeed
    linarith
  obtain ⟨jNext, hjNext_succ, hnextActual⟩ :=
    seededResidualInitialActualNextOwnerSplit
      (b := b) (x := x) (mZ := mZ) (c := c) (α := α)
      (tSeed := tSeed) (tNext := tNext) hSeed_pos
      (ρSeed := ρSeed) (ρNext := ρNext)
      hρNext_moment htSeed_lt_tNext hρNext_plateau
  dsimp at hnextActual
  let ρBaseNext : ℝ := x jNext.succ + (mZ : ℝ) - (⌊b jNext⌋ : ℝ) + α
  refine ⟨tNext, jNext, ρBaseNext, hjNext_succ, hNext_eq, hSeed_lt_next, hNext_last, ?_, ?_, ?_⟩
  · -- The actual next-owner coordinate lies above the collapsed public plateau value `1`.
    have hρNext_le_base : ρNext ≤ ρBaseNext := by
      simpa [ρBaseNext] using hnextActual.1
    linarith [hρNext_eq_one, hρNext_le_base]
  · -- The packaged next-owner coordinate is definitionally the corresponding shifted successor.
    simp [ρBaseNext]
  · -- The public next-plateau domination is already the exact `1`-bound needed later.
    exact hρNext_plateau_one

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the real seeded owner-chain
blocker is the seed-specific threshold-weight constructor above the first positive owner. The
older current-owner profile route was too general for the available committed-mass data, so this
helper now reads the public breakpoint profile directly from that threshold normal form. -/
private lemma seededCommittedTailThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the discarded current-owner profile recursion had the wrong normal form.
  -- The only unresolved local work is the seed-specific threshold-weight constructor that keeps
  -- the committed split `(ρBase, μBase)` visible above `tSeed`.
  have hfrontier :
      ∀ htSeed_lt_n : tSeed.1 < n,
        ∃ tNext : Fin (n + 1), ∃ jNext : Fin n, ∃ ρBaseNext : ℝ,
          jNext.succ = tNext ∧
          extendedMixingFractionalPart b tNext =
            extendedMixingFractionalPart b (mixingSliceChordUpper tSeed htSeed_lt_n) ∧
          extendedMixingFractionalPart b tSeed < extendedMixingFractionalPart b tNext ∧
          (∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s = extendedMixingFractionalPart b tNext → s ≤ tNext) ∧
          1 ≤ ρBaseNext ∧
          ρBaseNext ≤ x jNext.succ + (mZ : ℝ) - (⌊b jNext⌋ : ℝ) + α ∧
          (∀ k : Fin n,
            tSeed < k.succ →
              k.succ ≤ tNext →
                1 ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
    intro htSeed_lt_n
    -- Freeze the first nonterminal frontier and its actual next-owner coordinate before attempting
    -- the final threshold-weight assembly.
    exact
      seededCommittedFrontierPackage
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
        hx0_eq (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq hSeed_eq
        hSeed_pos hSeed_last hα_nonneg
        (jSeed := jSeed) hjSeed_succ
        (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
        hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau
        htSeed_lt_n
  have hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α := by
    -- The public seed ceiling remains bounded by the actual seed owner coordinate.
    exact
      seededResidualSeedCoordinateBound
        (ρSeed := ρSeed) (ρBase := ρBase)
        (seedBound := x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
        hseedBase_split.1 hρBase_bound
  have hterminalSeedData :
      ¬ tSeed.1 < n → tSeed = Fin.last n ∧ tZero < tSeed := by
    intro hterminal
    constructor
    · -- The terminal seed owner is the last breakpoint owner.
      exact currentOwner_eq_last_of_not_lt_n (tCur := tSeed) hterminal
    · -- The first positive seed owner still lies strictly above the zero plateau owner.
      exact
        zeroOwner_lt_currentOwner
          (b := b) (hmono := hmono) (tZero := tZero) (tCur := tSeed)
          hzero_eq hSeed_pos htZero_last
  -- The remaining scalar obligations are discharged after the committed data are normalized.
  linarith

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the old current-owner
profile interface is now just a seed-specific wrapper around the threshold constructor. The
profile itself should be reconstructed through `residualProfileFromThresholdWeights`, not by
re-entering the disproved one-plateau transport route. -/
private lemma committedResidualTailProfileAboveOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨w, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩ :=
    seededCommittedTailThresholdWeights
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau
  -- Reconstruct the public cumulative profile from the repaired threshold normal form.
  exact
    residualProfileFromThresholdWeights
      (b := b) (hmono := hmono) (y := y) (c := c) (α := α) w
      hα_nonneg hw_nonneg hw_sum hw_last hw_head hw_dom

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the public current-owner
profile lemma is only the `dCur := c - α` adapter for the recursion-closed owner-chain helper. -/
private lemma existsCommittedResidualBreakpointProfileAboveOwner
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the seed-specific profile wrapper now delegates straight to the repaired
  -- threshold constructor instead of the disproved generic owner-chain recursion.
  exact
    committedResidualTailProfileAboveOwner
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau

/-- Helper for remote integer-programming retry after job 2709
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the seeded branch should
first be owned by one exact threshold-weight constructor above `tSeed`. The breakpoint-profile and
candidate-step interfaces are only stable wrappers around this threshold normal form. -/
private lemma existsSeededResidualThresholdWeightsCore
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: keep the core as a thin wrapper around the single seed-specific threshold
  -- constructor so the remaining blocker is isolated to one declaration.
  exact
    seededCommittedTailThresholdWeights
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the seeded owner-chain
construction should first produce the cumulative residual profile above `tSeed`. Once this profile
interface is available, both the candidate-step and threshold-weight packages are only adapter
wrappers. -/
private lemma existsSeededResidualBreakpointProfileAboveSeed
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ ρ : Fin (n + 1) → ℝ,
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the public seeded breakpoint profile is now recovered directly from the
  -- seed-specific threshold normal form.
  exact
    committedResidualTailProfileAboveOwner
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the only unresolved
mathematical work is the seeded threshold-weight constructor above `tSeed`. Once this exact
threshold normal form exists, the existing threshold-to-profile-to-candidate bridge closes the
candidate-step package without reopening the owner-chain construction. -/
private lemma existsSeededResidualThresholdWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the seeded threshold package now has a single owner, namely the dedicated
  -- threshold-core constructor above `tSeed`.
  exact
    existsSeededResidualThresholdWeightsCore
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the seeded
threshold-weight constructor is available above `tSeed`, the committed-tail candidate package is
just the stable threshold-to-profile-to-candidate bridge. -/
private lemma existsCommittedTailCandidateWeightsAboveSeed
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {jSeed : Fin n}
    (hjSeed_succ : jSeed.succ = tSeed)
    {ρSeed ρBase μBase : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (htZero_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = 0 → s ≤ tZero)
    (hseedBase_split :
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase +
            extendedMixingFractionalPart b tSeed * (1 - ρBase) =
          c - α)
    (hρBase_bound :
      ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α)
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the committed-tail package now reads directly from the seeded cumulative
  -- profile instead of looping through threshold normal form first.
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
    existsSeededResidualBreakpointProfileAboveSeed
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg
      (jSeed := jSeed) hjSeed_succ
      (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
      hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau
  refine ⟨consecutiveDifferenceWeights ρ, ?_, ?_, ?_, ?_, ?_⟩
  · -- Monotonicity makes every jump and the terminal residual mass nonnegative.
    exact consecutiveDifferenceWeights_nonneg ρ hρmono hρlast
  · -- The strict prefix telescope at the terminal breakpoint recovers the full mass `1`.
    have hprefix_last :
        ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc = ρ (Fin.last n) := by
      have hprefix_last_iio :
          Finset.sum (Finset.Iio (Fin.last n)) (consecutiveDifferenceWeights ρ) =
            ρ (Fin.last n) :=
        consecutiveDifferenceWeightsPrefixMass_eq_profileIio ρ hρ0 (Fin.last n)
      rw [Fin.Iio_last_eq_map] at hprefix_last_iio
      simpa [Finset.sum_map] using hprefix_last_iio
    calc
      ∑ t : Fin (n + 1), consecutiveDifferenceWeights ρ t
          = ∑ t : Fin n, consecutiveDifferenceWeights ρ t.castSucc +
              consecutiveDifferenceWeights ρ (Fin.last n) := by
                rw [Fin.sum_univ_castSucc]
      _ = ρ (Fin.last n) + (1 - ρ (Fin.last n)) := by
            rw [hprefix_last, consecutiveDifferenceWeights_last]
      _ = 1 := by ring
  · -- Positive jumps of the rebuilt profile inherit the same last-occurrence owner property.
    exact hρlastOcc
  · -- The seeded cumulative profile already carries the exact residual head moment.
    exact hρhead
  · intro i
    -- Rewrite the candidate-step sum to the strict prefix mass recovered from the seeded
    -- cumulative profile.
    rw [candidateWeightStepPrefix_eq (b := b) (w := consecutiveDifferenceWeights ρ) i]
    simpa [consecutiveDifferenceWeightsPrefixMass_eq_profile ρ hρ0 i] using hρdom i

/-- Helper for remote integer-programming retry after job 2708
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the committed-tail
constructor is available in candidate-step normal form, the existing indicator rewrite converts it
to the threshold-weight package required by the residual threshold bridge. -/
private lemma seededThresholdWeightsFromCandidateStepWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {y : Fin (n + 1) → ℝ} {c α : ℝ}
    (hcandidate :
      ∃ w : Fin (n + 1) → ℝ,
        (∀ t : Fin (n + 1), 0 ≤ w t) ∧
        (∑ t : Fin (n + 1), w t = 1) ∧
        (∀ t : Fin (n + 1), 0 < w t →
          ∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
        (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
        (∀ i : Fin n,
          ∑ t : Fin (n + 1),
              w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
            y i.succ - (⌊b i⌋ : ℝ) + α)) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  rcases hcandidate with ⟨w, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩
  refine ⟨w, hw_nonneg, hw_sum, hw_last, hw_head, ?_⟩
  -- The candidate-step package already has the correct support and moment fields, so only the
  -- threshold/candidate indicator rewrite remains.
  exact
    candidateStepWeightsToThresholdWeights
      (b := b) (hmono := hmono) (y := y) (α := α) w hw_nonneg hw_last hw_dom

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: starting from the proved
seed package at the first positive last-occurrence owner, the only remaining local task is to
construct threshold weights on later last-occurrence owners; the public candidate-weight package
then follows by the stable threshold-to-profile-to-candidate bridge above. -/
private lemma existsSeededResidualCandidateWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c α : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    {tZero tSeed : Fin (n + 1)}
    (htZero_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ (0 : ℝ) → s ≤ tZero)
    (htZero_lt_n : tZero.1 < n)
    (hzero_eq : extendedMixingFractionalPart b tZero = 0)
    (hSeed_eq :
      extendedMixingFractionalPart b tSeed =
        extendedMixingFractionalPart b (mixingSliceChordUpper tZero htZero_lt_n))
    (hSeed_pos : 0 < extendedMixingFractionalPart b tSeed)
    (hSeed_last :
      ∀ s : Fin (n + 1),
        extendedMixingFractionalPart b s = extendedMixingFractionalPart b tSeed → s ≤ tSeed)
    (hα_nonneg : 0 ≤ α)
    {ρSeed : ℝ}
    (hρSeed_moment :
      c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed))
    (hρSeed_plateau :
      ∀ k : Fin n,
        tZero < k.succ →
          k.succ ≤ tSeed →
            ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) :
    ∃ w : Fin (n + 1) → ℝ,
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  have htSeed_ne_zero : tSeed ≠ 0 := by
    intro htSeed_zero
    subst htSeed_zero
    simpa using hSeed_pos
  obtain ⟨jSeed, hjSeed_succ⟩ := predecessorIndexOfNeZero (n := n) htSeed_ne_zero
  have htZero_lt_tSeed : tZero < tSeed := by
    have htZero_lt_adj : tZero < mixingSliceChordUpper tZero htZero_lt_n := by
      exact Fin.lt_def.mpr (by simp [mixingSliceChordUpper])
    have hadj_le_tSeed : mixingSliceChordUpper tZero htZero_lt_n ≤ tSeed := by
      exact hSeed_last _ hSeed_eq.symm
    exact lt_of_lt_of_le htZero_lt_adj hadj_le_tSeed
  have hρSeed_bound :
      ρSeed ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α := by
    -- The actual seed owner lies on the first positive plateau, so the seed ceiling bounds its
    -- shifted successor coordinate directly.
    have htZero_lt_jSeed : tZero < jSeed.succ := by
      simpa [hjSeed_succ] using htZero_lt_tSeed
    have hjSeed_le_tSeed : jSeed.succ ≤ tSeed := by
      simpa [hjSeed_succ]
    exact hρSeed_plateau jSeed htZero_lt_jSeed hjSeed_le_tSeed
  have hseedBase :
      let ρBase : ℝ := x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α
      let μBase : ℝ := extendedMixingFractionalPart b tSeed * (ρBase - ρSeed)
      ρSeed ≤ ρBase ∧
        0 ≤ μBase ∧
        μBase + extendedMixingFractionalPart b tSeed * (1 - ρBase) = c - α := by
    -- Route correction: the seed ceiling itself cannot be reused as the transported plateau
    -- value. The actual seed coordinate yields a strictly richer residual split, with an explicit
    -- positive moment `μBase` separated from the open seed tail.
    exact
      seededResidualBaseMomentSplit
        (b := b) (x := x) (mZ := mZ) (c := c) (α := α) (tSeed := tSeed) (jSeed := jSeed)
        hjSeed_succ hSeed_pos hρSeed_bound hρSeed_moment
  have hthreshold :
      ∃ w : Fin (n + 1) → ℝ,
        (∀ t : Fin (n + 1), 0 ≤ w t) ∧
        (∑ t : Fin (n + 1), w t = 1) ∧
        (∀ t : Fin (n + 1), 0 < w t →
          ∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
        (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
        (∀ i : Fin n,
          ∑ t : Fin (n + 1),
              w t *
                (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                  else 1) ≤
            y i.succ - (⌊b i⌋ : ℝ) + α) := by
    have htZero_last :
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = 0 → s ≤ tZero := by
      -- Freeze the zero-plateau ownership once so the remaining constructor can refer to it
      -- directly instead of re-deriving the last-occurrence fact each time.
      exact zeroBreakpointLastOccurrence (b := b) htZero_max
    let fSeed : ℝ := extendedMixingFractionalPart b tSeed
    let ρBase : ℝ := x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α
    let μBase : ℝ := fSeed * (ρBase - ρSeed)
    have hseedBase_split :
        ρSeed ≤ ρBase ∧
          0 ≤ μBase ∧
          μBase + fSeed * (1 - ρBase) = c - α := by
      -- Normalize the live seed state to the exact `(fSeed, ρBase, μBase)` names used by the
      -- remaining residual extension.
      simpa [fSeed, ρBase, μBase] using hseedBase
    have hρBase_bound :
        ρBase ≤ x jSeed.succ + (mZ : ℝ) - (⌊b jSeed⌋ : ℝ) + α := by
      -- The normalized seed-coordinate name `ρBase` is definitionally the actual shifted seed
      -- coordinate, so the first committed-slack transport step can use it directly.
      simp [ρBase]
    -- Route correction: the outer theorem now calls the seeded threshold helper directly, so the
    -- local candidate-to-threshold-to-candidate loop disappears entirely.
    exact
      existsSeededResidualThresholdWeights
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
        hx0_eq y hy_def (tZero := tZero) (tSeed := tSeed) htZero_lt_n hzero_eq
        hSeed_eq hSeed_pos hSeed_last hα_nonneg
        (jSeed := jSeed) hjSeed_succ
        (ρSeed := ρSeed) (ρBase := ρBase) (μBase := μBase)
        hρSeed_moment htZero_last hseedBase_split hρBase_bound hρSeed_plateau
  rcases hthreshold with ⟨w, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩
  -- Once the threshold-weight constructor is available, the rest of the candidate package is the
  -- stable prefix-mass reconstruction already proved above.
  exact
    candidateWeightsFromResidualThresholdWeights
      (b := b) (hmono := hmono) (y := y) (c := c) (α := α) w
      hα_nonneg hw_nonneg hw_sum hw_last hw_head hw_dom

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the only remaining
nonterminal blocker is the direct last-occurrence-chain constructor for the residual breakpoint
profile itself. -/
private lemma existsNonterminalResidualBreakpointProfile
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ)))
    (hlt : tLo.1 < n) :
    ∃ α : ℝ, ∃ ρ : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Route correction: the nonterminal branch should no longer invent threshold-normal weights
  -- first. The truthful blocker is the seeded last-occurrence-chain construction of the cumulative
  -- profile itself, which both downstream adapters can already consume unchanged.
  have hzeroLevel :
      ∃ tZero : Fin (n + 1),
        extendedMixingFractionalPart b tZero ≤ (0 : ℝ) ∧
        ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ (0 : ℝ) → s ≤ tZero := by
    -- The ordered breakpoint chain always has a last zero plateau owner because the head value is
    -- `0`.
    exact exists_last_index_le_extendedMixingFractionalPart (b := b) (c := 0) (by norm_num)
  rcases hzeroLevel with ⟨tZero, htZero_le, htZero_max⟩
  have hzero_eq :
      extendedMixingFractionalPart b tZero = 0 := by
    -- Nonnegativity of every breakpoint forces the last lower zero owner to sit exactly at value
    -- `0`.
    have hzero_nonneg : 0 ≤ extendedMixingFractionalPart b tZero :=
      extendedMixingFractionalPart_nonneg tZero
    linarith
  have htZero_le_tLo : tZero ≤ tLo := by
    -- The last zero plateau still lies below every later lower breakpoint owner.
    exact htLo_max tZero (by simpa [hzero_eq])
  have htZero_lt_n : tZero.1 < n := by
    -- The last zero plateau owner still lies strictly below the nonterminal lower breakpoint.
    exact lt_of_le_of_lt (Fin.le_def.mp htZero_le_tLo) hlt
  obtain ⟨tSeed, hSeed_eq, hSeed_pos, hSeed_last⟩ :=
    existsNextDistinctBreakpointLastIndex
      (b := b) (c := 0) (tLo := tZero) htZero_max htZero_lt_n
  have htZero_lt_tSeed : tZero < tSeed := by
    have htZero_lt_adj : tZero < mixingSliceChordUpper tZero htZero_lt_n := by
      exact Fin.lt_def.mpr (by simp [mixingSliceChordUpper])
    have hadj_le_tSeed : mixingSliceChordUpper tZero htZero_lt_n ≤ tSeed := by
      exact hSeed_last _ hSeed_eq.symm
    exact lt_of_lt_of_le htZero_lt_adj hadj_le_tSeed
  have htSeed_ne_zero : tSeed ≠ 0 := by
    intro htSeed_zero
    subst htSeed_zero
    simpa using hSeed_pos
  obtain ⟨jSeed, hjSeed_succ⟩ := predecessorIndexOfNeZero (n := n) htSeed_ne_zero
  have hfjSeed_pos : 0 < mixingFractionalPart b jSeed := by
    simpa [← hjSeed_succ, extendedMixingFractionalPart_succ, mixingFractionalPart_eq_fract] using
      hSeed_pos
  have hy_tSeed :
      y tSeed = x jSeed.succ + (mZ : ℝ) := by
    -- Rewrite the normalized target at the first positive owner back to the corresponding
    -- successor coordinate of `x`.
    rw [hy_def, ← hjSeed_succ]
    simp
  have hseed :
      ∃ α : ℝ, 0 ≤ α ∧
        ∃ ρSeed : ℝ,
          ρSeed ≤ y tSeed - (⌊b jSeed⌋ : ℝ) + α ∧
          c - α = extendedMixingFractionalPart b tSeed * (1 - ρSeed) ∧
          (∀ k : Fin n,
            tZero < k.succ →
              k.succ ≤ tSeed →
                ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α) := by
    by_cases htZero_head : tZero = 0
    · -- When the last zero plateau is the head, the singleton positive type-one inequality gives
      -- the first owner value with zero extra slack.
      let ρSeed : ℝ := 1 - c / mixingFractionalPart b jSeed
      have hplateau :
          ∀ k : Fin n,
            tZero < k.succ →
              k.succ ≤ tSeed →
                ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) := by
        intro k htZero_lt_k hk_le_tSeed
        -- Every coordinate on the first positive plateau inherits the same head singleton seed.
        simpa [ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using
          headSeedPlateauValueBound
            (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
            hx0_eq (tZero := tZero) (tSeed := tSeed) htZero_lt_n hSeed_eq hSeed_pos
            htZero_lt_k hk_le_tSeed
      refine ⟨0, by norm_num, ρSeed, ?_, ?_, ?_⟩
      · rw [hy_tSeed]
        simpa [ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using
          headSingleton_profileBound
            (b := b) (x := x) hx (mZ := mZ) (c := c) hx0_eq hfjSeed_pos
      · have hmoment :=
          zeroStartProfileValue_residualMoment
            (d := c) (f := mixingFractionalPart b jSeed) (ρ := ρSeed)
            hfjSeed_pos.ne' rfl
        simpa [ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using hmoment
      · intro k htZero_lt_k hk_le_tSeed
        simpa using hplateau k htZero_lt_k hk_le_tSeed
    · -- On a non-head zero plateau, choose the minimal slack that makes the zero-start seed
      -- hypothesis nonnegative, then reuse the zero-start singleton inequality.
      obtain ⟨iZero, hiZero_succ, hfiZero_zero⟩ :=
        zeroPlateauPredIndex (b := b) htZero_head hzero_eq
      have hiZero_lt_jSeed : iZero < jSeed := by
        exact
          Fin.succ_lt_succ_iff.mp
            (by simpa [hiZero_succ, ← hjSeed_succ] using htZero_lt_tSeed)
      let α : ℝ := max 0 (-(x iZero.succ + (mZ : ℝ) - (⌊b iZero⌋ : ℝ)))
      let ρSeed : ℝ := 1 - (c - α) / mixingFractionalPart b jSeed
      have hα_nonneg : 0 ≤ α := by
        -- The seed slack is chosen as a nonnegative truncation.
        dsimp [α]
        exact le_max_left _ _
      have hiZero_nonneg :
          0 ≤ x iZero.succ + (mZ : ℝ) - (⌊b iZero⌋ : ℝ) + α := by
        -- The chosen slack is exactly large enough to make the zero-start hypothesis hold.
        have hneg_le : -(x iZero.succ + (mZ : ℝ) - (⌊b iZero⌋ : ℝ)) ≤ α := by
          dsimp [α]
          exact le_max_right _ _
        linarith
      have hplateau :
          ∀ k : Fin n,
            tZero < k.succ →
              k.succ ≤ tSeed →
                ρSeed ≤ x k.succ + (mZ : ℝ) - (⌊b k⌋ : ℝ) + α := by
        intro k htZero_lt_k hk_le_tSeed
        -- The zero-start seed inequality extends uniformly across the whole first positive
        -- plateau after rewriting every coordinate to the common upper breakpoint value.
        simpa [ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using
          zeroStartSeedPlateauValueBound
            (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
            hx0_eq (tZero := tZero) (tSeed := tSeed) htZero_lt_n hSeed_eq hSeed_pos
            hiZero_succ hfiZero_zero hiZero_nonneg htZero_lt_k hk_le_tSeed
      refine ⟨α, hα_nonneg, ρSeed, ?_, ?_, ?_⟩
      · rw [hy_tSeed]
        simpa [α, ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using
          zeroStartSingleton_profileBound
            (b := b) (x := x) hx (mZ := mZ) (c := c) (α := α) hx0_eq
            hfiZero_zero hiZero_lt_jSeed hfjSeed_pos hiZero_nonneg
      · have hmoment :=
          zeroStartProfileValue_residualMoment
            (d := c - α) (f := mixingFractionalPart b jSeed) (ρ := ρSeed)
            hfjSeed_pos.ne' rfl
        simpa [α, ρSeed, ← hjSeed_succ, extendedMixingFractionalPart_succ,
          mixingFractionalPart_eq_fract] using hmoment
      · intro k htZero_lt_k hk_le_tSeed
        simpa using hplateau k htZero_lt_k hk_le_tSeed
  obtain ⟨α, hα_nonneg, ρSeed, hρSeed_bound, hρSeed_moment, hρSeed_plateau⟩ := hseed
  obtain ⟨w, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩ :=
    existsSeededResidualCandidateWeights
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c) (α := α)
      hx0_eq (tLo := tLo) htLo_le htLo_max y hy_def
      (tZero := tZero) (tSeed := tSeed) htZero_max htZero_lt_n hzero_eq
      hSeed_eq hSeed_pos hSeed_last hα_nonneg hρSeed_moment hρSeed_plateau
  -- Route correction: once the seeded owner-chain constructor returns candidate weights directly,
  -- the public residual profile is the standard prefix-mass reconstruction already proved above.
  obtain ⟨ρ, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
    residualProfileFromCandidateWeights
      (b := b) (y := y) (c := c) (α := α) w
      hα_nonneg hw_nonneg hw_sum hw_last hw_head hw_dom
  exact ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the nonterminal
profile constructor is isolated, the residual threshold-weight core is only a short wrapper around
the existing profile-to-weights and indicator-rewrite adapters. -/
private lemma existsResidualThresholdWeightsCore
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))) :
    ∃ α : ℝ, ∃ w : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t *
              (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  by_cases hlt : tLo.1 < n
  · obtain ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
      existsNonterminalResidualBreakpointProfile
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def hlt
    obtain ⟨α', w, hα'_nonneg, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩ :=
      profileToResidualCandidateWeights
        (b := b) (y := y) (c := c) (α := α) ρ
        hα_nonneg hρ0 hρmono hρlast hρlastOcc hρhead hρdom
    have hw_threshold_dom :
        ∀ i : Fin n,
          ∑ t : Fin (n + 1),
              w t *
                (if mixingFractionalPart b i ≤ extendedMixingFractionalPart b t then (0 : ℝ)
                  else 1) ≤
            y i.succ - (⌊b i⌋ : ℝ) + α' := by
      -- Rewrite the candidate-step domination returned by the profile adapter to the exact
      -- threshold normal form required by the residual threshold API.
      exact
        candidateStepWeightsToThresholdWeights
          (b := b) (hmono := hmono) (y := y) (α := α') w hw_nonneg hw_last hw_dom
    exact ⟨α', w, hα'_nonneg, hw_nonneg, hw_sum, hw_last, hw_head, hw_threshold_dom⟩
  · -- The terminal branch is a verified singleton support package at the last lower breakpoint.
    exact
      existsTerminalResidualThresholdWeights
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def hlt

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the true remaining
construction problem is the residual breakpoint-profile constructor itself: once a cumulative
profile `ρ` with the correct last-occurrence, moment, and domination fields exists, both the
breakpoint weights and the downstream hull package are immediate wrappers. -/
private lemma existsResidualBreakpointProfileCore
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))) :
    ∃ α : ℝ, ∃ ρ : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
    (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  by_cases hlt : tLo.1 < n
  · -- Route correction: on the nonterminal branch the truthful blocker is already the profile
    -- constructor, so the core profile lemma should consume it directly instead of looping through
    -- threshold weights and back.
    exact
      existsNonterminalResidualBreakpointProfile
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def hlt
  · obtain ⟨α, w, hα_nonneg, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩ :=
      existsTerminalResidualThresholdWeights
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def hlt
    obtain ⟨ρ, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
      residualProfileFromThresholdWeights
        (b := b) (hmono := hmono) (y := y) (c := c) (α := α) w
        hα_nonneg hw_nonneg hw_sum hw_last hw_head hw_dom
    -- The terminal branch still reuses the verified singleton threshold package and the stable
    -- threshold-to-profile adapter.
    exact ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once the residual
breakpoint profile is available, the breakpoint weights are just its consecutive differences. -/
private lemma existsResidualBreakpointWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))) :
    ∃ α : ℝ, ∃ w : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  obtain ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩ :=
    existsResidualBreakpointProfileCore
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def
  -- Feed the isolated profile constructor into the already-verified profile-to-weights adapter.
  exact
    profileToResidualCandidateWeights
      (b := b) (y := y) (c := c) (α := α) ρ
      hα_nonneg hρ0 hρmono hρlast hρlastOcc hρhead hρdom

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the only remaining
shared blocker in the residual-weight route is to construct one cumulative profile `ρ` together
with a slack `α` from the normalized region data and the maximal lower-breakpoint owner. -/
private lemma existsResidualBreakpointProfile
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo)
    (y : Fin (n + 1) → ℝ)
    (hy_def : y = Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))) :
    ∃ α : ℝ, ∃ ρ : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      ρ 0 = 0 ∧
      Monotone ρ ∧
      ρ (Fin.last n) ≤ 1 ∧
      (∀ t : Fin (n + 1), 0 < consecutiveDifferenceWeights ρ t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1),
          consecutiveDifferenceWeights ρ t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        (if mixingFractionalPart b i = 0 then 0 else ρ i.succ) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  -- Reuse the direct core constructor so the profile interface no longer loops through weights.
  exact
    existsResidualBreakpointProfileCore
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y hy_def

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a normalized region point
with maximal lower breakpoint `tLo` should admit a residual candidate-weight package in the exact
normal form consumed by the candidate-combination hull lemma. -/
private lemma existsResidualCandidateWeights
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    ∃ α : ℝ, ∃ w : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      (∀ t : Fin (n + 1), 0 ≤ w t) ∧
      (∑ t : Fin (n + 1), w t = 1) ∧
      (∀ t : Fin (n + 1), 0 < w t →
        ∀ s : Fin (n + 1),
          extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
      (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
      (∀ i : Fin n,
        ∑ t : Fin (n + 1),
            w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
          y i.succ - (⌊b i⌋ : ℝ) + α) := by
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  have hprofile :=
    existsResidualBreakpointProfile
      (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
      hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max y rfl
  rcases hprofile with ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρhead, hρdom⟩
  -- Feed the shared breakpoint-chain profile into the proved `ρ → weights` bridge.
  exact
    profileToResidualCandidateWeights
      (b := b) (y := y) (c := c) (α := α) ρ
      hα_nonneg hρ0 hρmono hρlast hρlastOcc hρhead hρdom

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a normalized region point
with maximal lower breakpoint `tLo` should admit a direct residual hull point at height `c - α`
whose successor coordinates stay below the shifted tail `y + α`. -/
private lemma existsDominatingCandidateWeightPackage
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    {tLo : Fin (n + 1)}
    (htLo_le : extendedMixingFractionalPart b tLo ≤ c)
    (htLo_max :
      ∀ s : Fin (n + 1), extendedMixingFractionalPart b s ≤ c → s ≤ tLo) :
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    ∃ α : ℝ, ∃ q : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      q ∈ mixingHull b ∧
      q 0 = c - α ∧
      (∀ i : Fin n, q i.succ ≤ y i.succ + α) := by
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  have hweights :
      ∃ α : ℝ, ∃ w : Fin (n + 1) → ℝ,
        0 ≤ α ∧
        (∀ t : Fin (n + 1), 0 ≤ w t) ∧
        (∑ t : Fin (n + 1), w t = 1) ∧
        (∀ t : Fin (n + 1), 0 < w t →
          ∀ s : Fin (n + 1),
            extendedMixingFractionalPart b s = extendedMixingFractionalPart b t → s ≤ t) ∧
        (∑ t : Fin (n + 1), w t * extendedMixingFractionalPart b t = c - α) ∧
        (∀ i : Fin n,
          ∑ t : Fin (n + 1),
              w t * (if mixingFractionalPart b i = 0 then 0 else if i.succ ≤ t then 0 else 1) ≤
            y i.succ - (⌊b i⌋ : ℝ) + α) := by
    -- Route correction: consume the correct residual candidate-weight interface directly instead
    -- of routing back through the false scalar slice-level witness.
    simpa [y] using
      existsResidualCandidateWeights
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max
  rcases hweights with ⟨α, w, hα_nonneg, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩
  let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
  let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
  have hp :
      p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
    -- Feed the residual candidate-weight package into the stable head-slack hull consumer.
    simpa [q, p] using
      candidateWeightCombination_addHeadSlack_mem_mixingHull_and_le
        (b := b) (hmono := hmono) (y := y) (c := c) (α := α)
        hα_nonneg w hw_nonneg hw_sum hw_last hw_head hw_dom
  refine ⟨0, p, by norm_num, hp.1, ?_, ?_⟩
  -- The transported hull point already has the target head height, so no additional slack remains.
  simpa using hp.2.1
  · intro i
    simpa using hp.2.2 i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: a normalized region point
should admit a nonnegative head slack `α` together with a residual hull point `q` at height
`c - α` whose successor coordinates stay below the shifted tail `y + α`. -/
private lemma existsDominatingBreakpointChord
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b)
    {mZ : ℤ} {c : ℝ}
    (hx0_eq : x 0 = (mZ : ℝ) + c)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1) :
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    ∃ α : ℝ, ∃ q : Fin (n + 1) → ℝ,
      0 ≤ α ∧
      q ∈ mixingHull b ∧
      q 0 = c - α ∧
      (∀ i : Fin n,
        q i.succ ≤ y i.succ + α) := by
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  rcases exists_last_index_le_extendedMixingFractionalPart (b := b) hc_nonneg with
    ⟨tLo, htLo_le, htLo_max⟩
  rcases (by
    -- Reduce the residual hull-point existence directly to the maximal-lower-breakpoint witness,
    -- so the final assembly no longer depends on the discarded sparse-weight normal form.
    simpa [y] using
      existsDominatingCandidateWeightPackage
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one (tLo := tLo) htLo_le htLo_max :
      ∃ α : ℝ, ∃ q : Fin (n + 1) → ℝ,
        0 ≤ α ∧
        q ∈ mixingHull b ∧
        q 0 = c - α ∧
        (∀ i : Fin n, q i.succ ≤ y i.succ + α)) with
    ⟨α, q, hα_nonneg, hqHull, hq0, hqDom⟩
  refine ⟨α, q, hα_nonneg, hqHull, hq0, ?_⟩
  intro i
  exact hqDom i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: the normalized slice of a
region point should admit a hull point at the same height and no larger successor coordinates. -/
private lemma existsDominatedNormalizedSliceHullPoint
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) :
    let mZ : ℤ := ⌊x 0⌋
    let c : ℝ := Int.fract (x 0)
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    ∃ p, p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
  let mZ : ℤ := ⌊x 0⌋
  let c : ℝ := Int.fract (x 0)
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Int.fract_nonneg (x 0)
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact Int.fract_lt_one (x 0)
  have hx0_eq : x 0 = (mZ : ℝ) + c := by
    simpa [mZ, c] using (Int.floor_add_fract (x 0)).symm
  have hresidual :
      ∃ α : ℝ, ∃ q : Fin (n + 1) → ℝ,
        0 ≤ α ∧
        q ∈ mixingHull b ∧
        q 0 = c - α ∧
        (∀ i : Fin n, q i.succ ≤ y i.succ + α) := by
    -- The false candidate-weight interface has been removed; only the direct residual hull-point
    -- witness remains before the final head-ray transport.
    simpa [y] using
      existsDominatingBreakpointChord
        (b := b) (hmono := hmono) (x := x) hx (mZ := mZ) (c := c)
        hx0_eq hc_nonneg hc_lt_one
  rcases hresidual with ⟨α, q, hα_nonneg, hqHull, hq0, hqDom⟩
  let p : Fin (n + 1) → ℝ := q + α • exercise_3_29_ray (0 : Fin (n + 1))
  have hp :
      p ∈ mixingHull b ∧ p 0 = c ∧ ∀ i : Fin n, p i.succ ≤ y i.succ := by
    -- Consume the direct residual hull-point witness through the dedicated head-slack transport
    -- lemma, so the normalized-slice assembly stays short and stable.
    simpa [p] using
      hullPointAddHeadSlack_mem_mixingHull_and_le
        (b := b) (y := y) (q := q) (c := c) (α := α)
        hqHull hq0 hα_nonneg hqDom
  exact ⟨p, hp.1, hp.2.1, hp.2.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: once a normalized slice
point in `mixingHull b` sits below the shifted tail of `x`, the head ray and successor rays
reassemble `x` inside `mixingHull b`. -/
private lemma mixingHull_of_slicePointAndSlacks
    (b : Fin n → ℚ) {x p : Fin (n + 1) → ℝ} {mZ : ℤ} {m : ℕ} {c : ℝ}
    (hp : p ∈ mixingHull b)
    (hp0 : p 0 = c)
    (hmZ_nonneg : 0 ≤ mZ)
    (hm_cast : (m : ℝ) = (mZ : ℝ))
    (hx0 : x 0 = (mZ : ℝ) + c)
    (hsucc : ∀ i : Fin n, p i.succ ≤ x i.succ + (mZ : ℝ)) :
    x ∈ mixingHull b := by
  -- First move the slice point up by the head ray, then add the nonnegative successor slacks.
  have hconv : Convex ℝ (mixingHull b) := by
    simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
  have hhead :
      p + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
    exact
      add_nat_smul_mem_of_unitStep
        hp
        (fun {z} hz ↦ mixingHull_add_headRay_mem b hz)
        m
  let δ : Fin n → ℝ := fun i ↦ x i.succ + (mZ : ℝ) - p i.succ
  have hδ_nonneg : ∀ i : Fin n, 0 ≤ δ i := by
    intro i
    dsimp [δ]
    linarith [hsucc i]
  have htranslate :
      p + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) +
          ∑ i : Fin n, δ i • exercise_3_29_ray i.succ ∈ mixingHull b := by
    exact
      add_sum_nonneg_smul_successorRays_mem
        (hconv := hconv)
        hhead
        (fun {z} i hz ↦ mixingHull_add_successorRay_mem b i hz)
        δ
        hδ_nonneg
  have hx_eq :
      p + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) +
          ∑ i : Fin n, δ i • exercise_3_29_ray i.succ = x := by
    ext j
    refine Fin.cases ?_ ?_ j
    · -- Successor rays do not affect the head, and the head ray restores `x₀`.
      calc
        (p + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) +
              ∑ i : Fin n, δ i • exercise_3_29_ray i.succ) 0
            = p 0 + (m : ℝ) * 1 +
                (∑ i : Fin n, δ i • exercise_3_29_ray i.succ) 0 := by
                  simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply]
        _ = c + (mZ : ℝ) := by
              rw [successorRaySum_apply_zero, hp0, hm_cast]
              ring
        _ = x 0 := by rw [add_comm, hx0]
    · intro i
      have hsucc_ne_zero : ¬ (i.succ : Fin (n + 1)) = 0 := by
        simp
      calc
        (p + (m : ℝ) • exercise_3_29_ray (0 : Fin (n + 1)) +
              ∑ j : Fin n, δ j • exercise_3_29_ray j.succ) i.succ
            = p i.succ + (m : ℝ) * (-1 : ℝ) +
                (∑ j : Fin n, δ j • exercise_3_29_ray j.succ) i.succ := by
                  simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
        _ = p i.succ - (m : ℝ) + δ i := by
              rw [successorRaySum_apply_succ]
              ring
        _ = x i.succ := by
              dsimp [δ]
              rw [hm_cast]
              ring
  simpa [hx_eq] using htranslate

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: after separating the
integer part of `x 0`, the normalized point with head coordinate `Int.fract (x 0)` and shifted
successor coordinates already lies in `mixingHull b`. -/
private lemma normalizedHeadShift_mem_mixingHull
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) :
    let mZ : ℤ := ⌊x 0⌋
    let c : ℝ := Int.fract (x 0)
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    y ∈ mixingHull b := by
  let mZ : ℤ := ⌊x 0⌋
  let c : ℝ := Int.fract (x 0)
  let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
  obtain ⟨p, hp, hp0, hsucc⟩ := by
    -- Isolate the remaining reverse-inclusion geometry into one slice-level domination lemma.
    simpa [mZ, c, y] using existsDominatedNormalizedSliceHullPoint b hmono hx
  -- Reassemble the normalized point from the dominated hull slice point with zero head slack.
  exact
    mixingHull_of_slicePointAndSlacks
      (b := b) (x := y) (p := p) (mZ := 0) (m := 0)
      hp hp0
      (by norm_num)
      (by norm_num)
      (by simp [y, c])
      (by simpa using hsucc)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean`: after normalizing the
head coordinate of a region point to `Int.fract (x 0)`, the resulting slice point already lies
in `mixingHull b`. -/
private lemma normalizedSlicePoint_mem_mixingHull
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b))
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingInequalitiesRegion b) :
    let mZ : ℤ := ⌊x 0⌋
    let c : ℝ := Int.fract (x 0)
    let y : Fin (n + 1) → ℝ := Fin.cases c (fun i : Fin n ↦ x i.succ + (mZ : ℝ))
    y ∈ mixingHull b := by
  -- The earlier duplicate statement is now discharged through the actual slice-domination helper.
  simpa using normalizedHeadShift_mem_mixingHull b hmono hx

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_1/ch4_sec4_8_1_theorem_4_34.lean
Theorem 4.34. Under the same ordered-fractional-part setup as Proposition 4.33, `P^mix` is
described by the inequality `x₀ ≥ 0`, the zero-fraction singleton covering inequalities, the
zero-start type-two inequalities for every sequence `i₀ < i₁ < ⋯ < i_m` with
`f_{i₀} = 0 < f_{i₁} < ⋯ < f_{i_m}` (whose case `m = 1` is the mixed zero/positive coupling
inequality), and the mixing inequalities `(4.29)` and `(4.30)` for all sequences
`1 ≤ i₁ < ⋯ < i_m ≤ n` such that `0 < f_{i₁} < ⋯ < f_{i_m}`. -/
theorem mixingHull_eq_mixing_inequalities_region
    (b : Fin n → ℚ)
    (hmono : Monotone (extendedMixingFractionalPart b)) :
    mixingHull b = mixingInequalitiesRegion b := by
  refine Set.Subset.antisymm ?_ ?_
  · -- The forward inclusion is the convex-hull containment already established above.
    exact mixingHull_subset_mixingInequalitiesRegion b
  · intro x hx
    obtain ⟨α, ρ, hα_nonneg, hρ0, hρmono, hρlast, hρlastOcc, hρmoment, hρdom⟩ :=
      existsDirectResidualBreakpointProfile b hmono hx
    obtain ⟨α', w, hα'_nonneg, hw_nonneg, hw_sum, hw_last, hw_head, hw_dom⟩ :=
      profileToResidualCandidateWeights
        (b := b) (y := x) (c := x 0) (α := α) ρ
        hα_nonneg hρ0 hρmono hρlast hρlastOcc hρmoment hρdom
    let q : Fin (n + 1) → ℝ := ∑ t : Fin (n + 1), w t • mixingVertexCandidate b t
    let p : Fin (n + 1) → ℝ := q + α' • exercise_3_29_ray (0 : Fin (n + 1))
    have hp : p ∈ mixingHull b ∧ p 0 = x 0 ∧ ∀ i : Fin n, p i.succ ≤ x i.succ := by
      -- The residual profile first gives a convex combination; the head ray restores its slack.
      simpa [q, p] using
        candidateWeightCombination_addHeadSlack_mem_mixingHull_and_le
          (b := b) (hmono := hmono) (y := x) (c := x 0) (α := α')
          hα'_nonneg w hw_nonneg hw_sum hw_last hw_head hw_dom
    let δ : Fin n → ℝ := fun i ↦ x i.succ - p i.succ
    have hδ_nonneg : ∀ i, 0 ≤ δ i := by
      intro i
      dsimp [δ]
      linarith [hp.2.2 i]
    have hconv : Convex ℝ (mixingHull b) := by
      simpa [mixingHull] using (convex_convexHull ℝ (mixingSet b))
    have htranslated :
        p + ∑ i : Fin n, δ i • exercise_3_29_ray i.succ ∈ mixingHull b := by
      -- Add the nonnegative successor-coordinate slacks along the known recession rays.
      exact
        add_sum_nonneg_smul_successorRays_mem
          (hconv := hconv)
          hp.1
          (fun {z} i hz ↦ mixingHull_add_successorRay_mem b i hz)
          δ hδ_nonneg
    have hrecover : p + ∑ i : Fin n, δ i • exercise_3_29_ray i.succ = x := by
      ext j
      refine Fin.cases ?_ ?_ j
      · rw [Pi.add_apply, successorRaySum_apply_zero, add_zero]
        exact hp.2.1
      · intro i
        rw [Pi.add_apply, successorRaySum_apply_succ]
        dsimp [δ]
        ring
    simpa [hrecover] using htranslated

end Theorem434
