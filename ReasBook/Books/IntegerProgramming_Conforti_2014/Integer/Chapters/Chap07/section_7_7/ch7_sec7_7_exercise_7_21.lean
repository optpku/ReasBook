/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_theorem_4_34.LinearForm
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_proposition_4_33

open scoped BigOperators Matrix

-- Domain sampling for this exercise:
-- * primary domain: mixing inequalities for the mixing hull `P^mix`
-- * core/canonical owner: Chapter 3's `facet_defining_inequality`
-- * source-facing owner reused from Chapter 4: Theorem 4.34's mixing inequalities together with
--   their coefficient/rhs bridge to linear inequalities
-- * source/core/bridge triage: Exercise 7.21 is a facet statement about those already-owned
--   inequalities, so this file keeps only the facet layer

section Exercise721

variable {n : ℕ}

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the recursive floor
contribution in Chapter 4's shifted normal form for the mixing inequalities. -/
private noncomputable def chap4MixingInequalityFloorSumAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (⌊b i⌋ : ℝ) + chap4MixingInequalityFloorSumAux b fi is

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the accumulated floor
contribution in Chapter 4's shifted normal form for the mixing inequalities. -/
private noncomputable def chap4MixingInequalityFloorSum
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  chap4MixingInequalityFloorSumAux b 0 s

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the recursive raw
selected-coordinate sum before the floor-shift constants move to the right-hand side. -/
private noncomputable def chap4MixingInequalityTypeOneRawSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * x i.succ + chap4MixingInequalityTypeOneRawSumAux b x fi is

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the recursive shifted
selected-coordinate sum for mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneSumAux
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) : ℝ → List (Fin n) → ℝ
  | _, [] => 0
  | prev, i :: is =>
      let fi := mixingFractionalPart b i
      (fi - prev) * (x i.succ - (⌊b i⌋ : ℝ)) + chap4MixingInequalityTypeOneSumAux b x fi is

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the shifted-coordinate sum
on the left-hand side of mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneSum
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : ℝ :=
  chap4MixingInequalityTypeOneSumAux b x 0 s

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the recursive coefficient
contribution in Chapter 4's linear form for mixing inequality `(4.29)`. -/
private noncomputable def chap4MixingInequalityTypeOneCoeffAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → Fin (n + 1) → ℝ
  | _, [] => fun _ ↦ 0
  | prev, i :: is =>
      fun j ↦
        (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
          chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: a list of indices is
admissible for the mixing inequalities when it is nonempty, strictly increasing, and has strictly
increasing positive fractional parts. -/
def IsMixingIndexSequence (b : Fin n → ℚ) : List (Fin n) → Prop
  | [] => False
  | i :: is =>
      0 < mixingFractionalPart b i ∧
        (i :: is).IsChain (· < ·) ∧
        (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k)

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the source mixing
inequality `(4.29)` written in the local shifted normal form. -/
def mixingInequalityTypeOne
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s.reverse with
  | [] => True
  | last :: _ =>
      mixingFractionalPart b last ≤ x 0 + chap4MixingInequalityTypeOneSum b s x

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the source mixing
inequality `(4.30)` written in the local shifted normal form. -/
def mixingInequalityTypeTwo
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s, s.reverse with
  | first :: _, last :: _ =>
      mixingFractionalPart b last ≤
        x 0 + chap4MixingInequalityTypeOneSum b s x +
          (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))
  | _, _ => True

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: a zero-start mixing sequence
consists of a zero-fraction index followed by a nonempty admissible positive-fraction tail. -/
def IsZeroStartMixingIndexSequence
    (b : Fin n → ℚ) (i : Fin n) : List (Fin n) → Prop
  | [] => False
  | j :: js =>
      mixingFractionalPart b i = 0 ∧ i < j ∧ IsMixingIndexSequence b (j :: js)

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the zero-start type-two
mixing inequality in the local shifted normal form. -/
def mixingInequalityTypeTwoZeroStart
    (b : Fin n → ℚ) (i : Fin n) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) : Prop :=
  match s.reverse with
  | [] => True
  | last :: _ =>
      mixingFractionalPart b last ≤
        x 0 + chap4MixingInequalityTypeOneSum b s x +
          (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the auxiliary region cut out
by the zero-cover, zero-start, and positive-start mixing inequalities. -/
def mixingInequalitiesRegion
    (b : Fin n → ℚ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧
      (((∀ i : Fin n, mixingFractionalPart b i = 0 → (b i : ℝ) ≤ x 0 + x i.succ) ∧
        ∀ i : Fin n, ∀ s : List (Fin n),
          IsZeroStartMixingIndexSequence b i s →
            mixingInequalityTypeTwoZeroStart b i s x) ∧
      ∀ s : List (Fin n), IsMixingIndexSequence b s →
        mixingInequalityTypeOne b s x ∧ mixingInequalityTypeTwo b s x)}

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every mixing fractional part
is nonnegative. -/
lemma mixingFractionalPart_nonneg
    (b : Fin n → ℚ) (i : Fin n) :
    0 ≤ mixingFractionalPart b i := by
  simpa [mixingFractionalPart_eq_fract] using Int.fract_nonneg ((b i : ℚ) : ℝ)

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the canonical point on the
slice `x 0 = c` takes the least integral successor coordinates allowed by the covering
inequalities. -/
noncomputable def mixingSliceWitness
    (b : Fin n → ℚ) (c : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases c (fun i : Fin n ↦ (⌈(b i : ℝ) - c⌉ : ℝ))

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every slice witness with
`0 ≤ c < 1` is already a mixed-integer generator of `mixingHull b`. -/
lemma mixingSliceWitness_mem_mixingSet
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingSet b := by
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

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every slice witness with
`0 ≤ c < 1` already lies in `mixingHull b` because it is itself a generator. -/
lemma mixingSliceWitness_mem_mixingHull
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    mixingSliceWitness b c ∈ mixingHull b := by
  simpa [mixingHull] using
    (subset_convexHull ℝ (mixingSet b) (mixingSliceWitness_mem_mixingSet b hc_nonneg hc_lt_one))

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: on the unit slice, the
shifted successor coordinate of the slice witness is the floor branch `0` or the ceiling branch
`1` according to whether the breakpoint `mixingFractionalPart b i` has already been reached. -/
lemma mixingSliceWitness_shiftProfile
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) (i : Fin n) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) =
      if mixingFractionalPart b i ≤ c then 0 else 1 := by
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

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the slice profile collapses
to the floor branch once the breakpoint has been reached. -/
lemma mixingSliceWitness_shiftProfile_of_le
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : mixingFractionalPart b i ≤ c) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 0 := by
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_pos hfi]

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the slice profile collapses
to the ceiling branch while the breakpoint still lies ahead. -/
lemma mixingSliceWitness_shiftProfile_of_lt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) {i : Fin n}
    (hfi : c < mixingFractionalPart b i) :
    mixingSliceWitness b c i.succ - (⌊b i⌋ : ℝ) = 1 := by
  rw [mixingSliceWitness_shiftProfile b hc_nonneg hc_lt_one i, if_neg (not_le.mpr hfi)]

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: adding the head ray
preserves the mixed-integer generators. -/
lemma mixingSet_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingSet b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingSet b := by
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

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the head ray acts by a
recession direction on `mixingHull b`. -/
lemma mixingHull_add_headRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈ mixingHull b := by
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

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every successor Exercise
3.29 ray also acts by a recession direction on `mixingHull b`. -/
lemma mixingHull_add_successorRay_mem
    (b : Fin n → ℚ) {x : Fin (n + 1) → ℝ} (i : Fin n)
    (hx : x ∈ mixingHull b) :
    x + exercise_3_29_ray i.succ ∈ mixingHull b := by
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

/-- Helper for Exercise 7.21: every member of an admissible sequence has positive fractional part. -/
lemma mixingFractionalPart_pos_of_mem_isMixingIndexSequence
    (b : Fin n → ℚ) :
    ∀ {s : List (Fin n)}, IsMixingIndexSequence b s →
      ∀ {i : Fin n}, i ∈ s → 0 < mixingFractionalPart b i
  | [], hs, i, hi => False.elim hs
  | i0 :: is, hs, i, hi => by
      -- Positivity holds at the head by definition and propagates along the fractional-part chain.
      rcases hs with ⟨hi0_pos, -, hfracChain⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hi0_pos
      · exact lt_trans hi0_pos (hfracChain.rel_cons hi)

/-- Helper for Exercise 7.21: a positive mixing fractional part forces `⌈bᵢ⌉ = ⌊bᵢ⌋ + 1`. -/
lemma ceil_eq_floor_add_one_of_mixingFractionalPart_pos
    (b : Fin n → ℚ) {i : Fin n}
    (hi_pos : 0 < mixingFractionalPart b i) :
    (⌈b i⌉ : ℝ) = (⌊b i⌋ : ℝ) + 1 := by
  -- A positive fractional part means `bᵢ` is not integral, so the ceiling is the next integer.
  have hnot_int : b i ∉ Set.range (fun z : ℤ ↦ (z : ℚ)) := by
    intro hmem
    rcases hmem with ⟨z, hz⟩
    have hz' : ((b i : ℚ) : ℝ) = (z : ℝ) := by
      simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) hz.symm
    have hfract_zero : mixingFractionalPart b i = 0 := by
      rw [mixingFractionalPart_eq_fract, hz']
      simp
    exact (ne_of_gt hi_pos) hfract_zero
  exact_mod_cast (Int.ceil_eq_floor_add_one_iff_notMem (b i)).2 hnot_int

/-- Helper for Exercise 7.21: two points on the same equality face have zero dot product against
the exposing vector after subtraction. -/
lemma faceSet_dot_sub_eq_zero_of_two_mem
    {P : Set (Fin (n + 1) → ℝ)} {d x y : Fin (n + 1) → ℝ} {ε : ℝ}
    (hx : x ∈ face_set P d ε) (hy : y ∈ face_set P d ε) :
    d ⬝ᵥ (x - y) = 0 := by
  -- Unpack the two face equalities and subtract them once instead of repeating this algebra.
  have hx_eq : d ⬝ᵥ x = ε := (mem_face_set_iff.mp hx).2
  have hy_eq : d ⬝ᵥ y = ε := (mem_face_set_iff.mp hy).2
  rw [dotProduct_sub, hx_eq, hy_eq]
  simp

/-- Helper for Exercise 7.21: multiplying a defining inequality by a nonzero scalar does not
change its equality face. -/
lemma faceSet_eq_of_nonzero_smul
    {P : Set (Fin (n + 1) → ℝ)} {c : Fin (n + 1) → ℝ} {δ lam : ℝ}
    (hlam : lam ≠ 0) :
    face_set P (lam • c) (lam * δ) = face_set P c δ := by
  ext x
  rw [mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    have hscaled : lam * (c ⬝ᵥ x) = lam * δ := by
      calc
        lam * (c ⬝ᵥ x) = (lam • c) ⬝ᵥ x := by
          simpa [smul_eq_mul] using (smul_dotProduct lam c x).symm
        _ = lam * δ := hxEq
    exact mul_left_cancel₀ hlam hscaled
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, ?_⟩
    calc
      (lam • c) ⬝ᵥ x = lam * (c ⬝ᵥ x) := by
        simpa [smul_eq_mul] using (smul_dotProduct lam c x)
      _ = lam * δ := by rw [hxEq]


/-- Helper for Exercise 7.21: source-level alias for Theorem 4.34's floor-sum recursion. -/
private noncomputable abbrev importedChap4MixingInequalityFloorSumAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → ℝ :=
  mixingInequalityFloorSumAux b

/-- Helper for Exercise 7.21: source-level alias for Theorem 4.34's accumulated floor
contribution. -/
private noncomputable abbrev importedChap4MixingInequalityFloorSum
    (b : Fin n → ℚ) (s : List (Fin n)) : ℝ :=
  mixingInequalityFloorSum b s

/-- Helper for Exercise 7.21: source-level alias for Theorem 4.34's recursive coefficient owner
for mixing inequality `(4.29)`. -/
private noncomputable abbrev importedChap4MixingInequalityTypeOneCoeffAux
    (b : Fin n → ℚ) : ℝ → List (Fin n) → Fin (n + 1) → ℝ :=
  mixingInequalityTypeOneCoeffAux b

/-- Helper for Exercise 7.21: the imported Chapter 4 floor-sum recursion agrees with the local
copy used in this file. -/
private lemma importedChap4MixingInequalityFloorSumAux_eq_local
    (b : Fin n → ℚ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      importedChap4MixingInequalityFloorSumAux b prev s =
        chap4MixingInequalityFloorSumAux b prev s := by
  intro prev s
  induction s generalizing prev with
  | nil =>
      -- Both recursive owners are definitionally empty on the empty selected list.
      rfl
  | cons i is ih =>
      -- Peel off the new selected index and reuse the tail agreement at the updated base level.
      simpa [mixingInequalityFloorSumAux, chap4MixingInequalityFloorSumAux] using
        ih (mixingFractionalPart b i)

/-- Helper for Exercise 7.21: the imported Chapter 4 accumulated floor contribution agrees with
the local floor-sum owner. -/
private lemma importedChap4MixingInequalityFloorSum_eq_local
    (b : Fin n → ℚ) (s : List (Fin n)) :
    importedChap4MixingInequalityFloorSum b s = chap4MixingInequalityFloorSum b s := by
  -- Specialize the recursive owner agreement at the base level `0`.
  simpa [importedChap4MixingInequalityFloorSum, chap4MixingInequalityFloorSum] using
    importedChap4MixingInequalityFloorSumAux_eq_local b 0 s

/-- Helper for Exercise 7.21: the imported Chapter 4 recursive coefficient owner agrees with the
local copy used for the facet proof. -/
private lemma importedChap4MixingInequalityTypeOneCoeffAux_eq_local
    (b : Fin n → ℚ) :
    ∀ prev : ℝ, ∀ s : List (Fin n), ∀ j : Fin (n + 1),
      importedChap4MixingInequalityTypeOneCoeffAux b prev s j =
        chap4MixingInequalityTypeOneCoeffAux b prev s j := by
  intro prev s j
  induction s generalizing prev with
  | nil =>
      -- Both recursive owners vanish on every coordinate once the selected list is empty.
      rfl
  | cons i is ih =>
      -- The head coordinate contribution is identical, and the tail agrees by recursion.
      simpa [mixingInequalityTypeOneCoeffAux, chap4MixingInequalityTypeOneCoeffAux] using
        ih (mixingFractionalPart b i)

/-- Helper for Exercise 7.21: a single-coordinate vector evaluates to the expected scalar
multiple of that coordinate. -/
private lemma single_coordinate_dotProduct
    {m : ℕ} (j : Fin m) (c : ℝ) (x : Fin m → ℝ) :
    (fun k : Fin m ↦ if k = j then c else 0) ⬝ᵥ x = c * x j := by
  -- Collapse the finite dot product to its unique nonzero coordinate.
  rw [dotProduct, Fintype.sum_eq_single j]
  · simp
  · intro k hk
    simp [hk]

/-- Helper for Exercise 7.21: the local recursive coefficient vector for `(4.29)` evaluates to
the negative of the raw selected-coordinate sum. -/
private lemma chap4MixingInequalityTypeOneCoeffAux_dotProduct
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      chap4MixingInequalityTypeOneCoeffAux b prev s ⬝ᵥ x =
        -chap4MixingInequalityTypeOneRawSumAux b x prev s
  | prev, [] => by
      -- The empty sequence contributes no coefficients and no sum.
      simp [chap4MixingInequalityTypeOneCoeffAux, chap4MixingInequalityTypeOneRawSumAux,
        dotProduct]
  | prev, i :: is => by
      -- Split off the newly selected coordinate and reuse the recursive tail evaluation.
      rw [chap4MixingInequalityTypeOneCoeffAux, chap4MixingInequalityTypeOneRawSumAux]
      have hadd :
          (fun j : Fin (n + 1) ↦
              (if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
                chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is j) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x := by
        change
          (((fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) +
              chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is) ⬝ᵥ x =
            (fun j : Fin (n + 1) ↦
                if j = i.succ then -(mixingFractionalPart b i - prev) else 0) ⬝ᵥ x +
              chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is ⬝ᵥ x)
        exact
          add_dotProduct
            (fun j : Fin (n + 1) ↦
              if j = i.succ then -(mixingFractionalPart b i - prev) else 0)
            (chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i) is)
            x
      rw [hadd, single_coordinate_dotProduct, chap4MixingInequalityTypeOneCoeffAux_dotProduct]
      ring

/-- Helper for Exercise 7.21: a successor Exercise 3.29 ray pairs with a coefficient vector by
reading off the matching successor coordinate. -/
lemma dotProduct_exercise_3_29_ray_succ
    (c : Fin (n + 1) → ℝ) (i : Fin n) :
    c ⬝ᵥ exercise_3_29_ray i.succ = c i.succ := by
  have hray :
      exercise_3_29_ray i.succ =
        (fun j : Fin (n + 1) ↦ if j = i.succ then 1 else 0) := by
    ext j
    have hsucc_ne_zero : (i.succ : Fin (n + 1)) ≠ 0 := by
      simp
    simp [exercise_3_29_ray_apply, hsucc_ne_zero]
  rw [hray, dotProduct_comm, single_coordinate_dotProduct]
  simp

/-- Helper for Exercise 7.21: the head Exercise 3.29 ray pairs with a coefficient vector by
subtracting the successor coordinates from the head coordinate. -/
lemma dotProduct_exercise_3_29_ray_zero
    (c : Fin (n + 1) → ℝ) :
    c ⬝ᵥ exercise_3_29_ray (0 : Fin (n + 1)) = c 0 - ∑ i : Fin n, c i.succ := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp [exercise_3_29_ray_apply]
  ring

/-- Helper for Exercise 7.21: the recursive coefficient vector for `(4.29)` vanishes at every
successor coordinate whose index does not belong to the selected list. -/
lemma chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem
    (b : Fin n → ℚ) :
    ∀ {prev : ℝ} {s : List (Fin n)} {i : Fin n},
      i ∉ s →
      chap4MixingInequalityTypeOneCoeffAux b prev s i.succ = 0
  | _, [], _, _ => by
      simp [chap4MixingInequalityTypeOneCoeffAux]
  | prev, j :: js, i, hi => by
      have hij : i ≠ j := by
        intro hEq
        exact hi (by simp [hEq])
      have hsucc_ne : i.succ ≠ j.succ := fun hEq ↦ hij (by simpa using hEq)
      have htail : i ∉ js := by
        intro hmem
        exact hi (by simp [hmem])
      simp [chap4MixingInequalityTypeOneCoeffAux, hsucc_ne]
      exact chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b htail

/-- Helper for Exercise 7.21: Chapter 4 already identifies the raw left-hand side with the
shifted sum plus the accumulated floor contribution. -/
private lemma chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (s : List (Fin n)) :
    chap4MixingInequalityTypeOneRawSumAux b x 0 s =
      chap4MixingInequalityTypeOneSum b s x + chap4MixingInequalityFloorSum b s := by
  -- Split each selected coordinate into its shifted part plus the floor contribution.
  have haux :
      ∀ prev : ℝ, ∀ t : List (Fin n),
        chap4MixingInequalityTypeOneRawSumAux b x prev t =
          chap4MixingInequalityTypeOneSumAux b x prev t + chap4MixingInequalityFloorSumAux b prev t := by
    intro prev t
    induction t generalizing prev with
    | nil =>
        simp [chap4MixingInequalityTypeOneRawSumAux, chap4MixingInequalityTypeOneSumAux,
          chap4MixingInequalityFloorSumAux]
    | cons i is ih =>
        rw [chap4MixingInequalityTypeOneRawSumAux, chap4MixingInequalityTypeOneSumAux,
          chap4MixingInequalityFloorSumAux, ih]
        ring
  simpa [chap4MixingInequalityTypeOneSum, chap4MixingInequalityFloorSum] using haux 0 s

/-- Helper for Exercise 7.21: Chapter 4's exact dot-product formula for the coefficient vector of
`(4.29)`. -/
private lemma chap4MixingInequalityTypeOneCoeff_dotProduct
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeOneCoeff b s ⬝ᵥ x =
      -(x 0 + chap4MixingInequalityTypeOneRawSumAux b x 0 s) := by
  -- Route correction: rewrite the public coefficient owner to the local recursive copy before
  -- evaluating the dot product, so the rest of the proof stays in one scalar normal form.
  have hcoeff :
      mixingInequalityTypeOneCoeff b s =
        fun j : Fin (n + 1) ↦
          (if j = 0 then (-1 : ℝ) else 0) + chap4MixingInequalityTypeOneCoeffAux b 0 s j := by
    ext j
    simp [mixingInequalityTypeOneCoeff, importedChap4MixingInequalityTypeOneCoeffAux_eq_local]
  rw [hcoeff]
  have hadd :
      (fun j : Fin (n + 1) ↦
          (if j = 0 then (-1 : ℝ) else 0) + chap4MixingInequalityTypeOneCoeffAux b 0 s j) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          chap4MixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x := by
    change
      (((fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) +
          chap4MixingInequalityTypeOneCoeffAux b 0 s) ⬝ᵥ x =
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0) ⬝ᵥ x +
          chap4MixingInequalityTypeOneCoeffAux b 0 s ⬝ᵥ x)
    exact
      add_dotProduct
        (fun j : Fin (n + 1) ↦ if j = 0 then (-1 : ℝ) else 0)
        (chap4MixingInequalityTypeOneCoeffAux b 0 s)
        x
  rw [hadd, single_coordinate_dotProduct, chap4MixingInequalityTypeOneCoeffAux_dotProduct]
  ring

/-- Helper for Exercise 7.21: Chapter 4's exact dot-product formula for the coefficient vector of
`(4.30)` once the first and last selected indices are fixed. -/
private lemma chap4MixingInequalityTypeTwoCoeff_dotProduct_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ x =
      -(x 0 + chap4MixingInequalityTypeOneRawSumAux b x 0 (first :: tail) +
        (1 - mixingFractionalPart b last) * x first.succ) := by
  -- Split the type-two coefficient owner into the repaired type-one part and the first-index
  -- correction term.
  simp only [mixingInequalityTypeTwoCoeff, hrev]
  have hadd :
      (fun j : Fin (n + 1) ↦
          mixingInequalityTypeOneCoeff b (first :: tail) j +
            (if j = first.succ then -(1 - mixingFractionalPart b last) else 0)) ⬝ᵥ x =
        mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ x +
          (fun j : Fin (n + 1) ↦
            if j = first.succ then -(1 - mixingFractionalPart b last) else 0) ⬝ᵥ x := by
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
  rw [hadd, chap4MixingInequalityTypeOneCoeff_dotProduct, single_coordinate_dotProduct]
  ring

/-- Helper for Exercise 7.21: on successor coordinates, the public coefficient vector for
`(4.29)` agrees with the local recursive coefficient copy. -/
private lemma mixingInequalityTypeOneCoeff_apply_succ
    (b : Fin n → ℚ) (s : List (Fin n)) (i : Fin n) :
    mixingInequalityTypeOneCoeff b s i.succ =
      chap4MixingInequalityTypeOneCoeffAux b 0 s i.succ := by
  -- Successor coordinates see only the recursive selected-index contribution; the zeroth
  -- coefficient vanishes away from `0`.
  simpa [mixingInequalityTypeOneCoeff, importedChap4MixingInequalityTypeOneCoeffAux_eq_local]
    using (show mixingInequalityTypeOneCoeff b s i.succ =
      (if i.succ = 0 then (-1 : ℝ) else 0) + chap4MixingInequalityTypeOneCoeffAux b 0 s i.succ by
        simp [mixingInequalityTypeOneCoeff, importedChap4MixingInequalityTypeOneCoeffAux_eq_local])

/-- Helper for Exercise 7.21: the first selected successor coordinate of the type-one coefficient
vector is the negative first fractional part. -/
private lemma mixingInequalityTypeOneCoeff_apply_headSucc
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hs : IsMixingIndexSequence b (first :: tail)) :
    mixingInequalityTypeOneCoeff b (first :: tail) first.succ =
      -mixingFractionalPart b first := by
  rcases hs with ⟨_, hindexChain, _⟩
  have hfirst_not_mem_tail : first ∉ tail := by
    intro hmem
    exact (lt_irrefl first) (hindexChain.rel_cons hmem)
  -- Unfold only the head selected contribution; the recursive tail vanishes at `first.succ`.
  rw [mixingInequalityTypeOneCoeff_apply_succ]
  simp [chap4MixingInequalityTypeOneCoeffAux,
    chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b hfirst_not_mem_tail]

/-- Helper for Exercise 7.21: under a fixed reverse decomposition, the public right-hand side of
mixing inequality `(4.29)` agrees with the local shifted-floor normal form. -/
private lemma mixingInequalityTypeOneRhs_eq_local_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) :
    mixingInequalityTypeOneRhs b (first :: tail) =
      -mixingFractionalPart b last - chap4MixingInequalityFloorSum b (first :: tail) := by
  -- Rewrite the public rhs owner once to the local floor-sum copy and keep later proofs in that
  -- repaired normal form.
  calc
    mixingInequalityTypeOneRhs b (first :: tail)
        = -mixingFractionalPart b last -
            importedChap4MixingInequalityFloorSum b (first :: tail) := by
            simp [mixingInequalityTypeOneRhs, hrev, importedChap4MixingInequalityFloorSum]
    _ = -mixingFractionalPart b last - chap4MixingInequalityFloorSum b (first :: tail) := by
      rw [importedChap4MixingInequalityFloorSum_eq_local]

/-- Helper for Exercise 7.21: under a fixed reverse decomposition, the public right-hand side of
mixing inequality `(4.30)` agrees with the local shifted-floor normal form. -/
private lemma mixingInequalityTypeTwoRhs_eq_local_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) :
    mixingInequalityTypeTwoRhs b (first :: tail) =
      -mixingFractionalPart b last - chap4MixingInequalityFloorSum b (first :: tail) -
        (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ) := by
  -- Rewrite the public rhs owner once to the local floor-sum copy and keep the extra
  -- first-coordinate correction explicit.
  calc
    mixingInequalityTypeTwoRhs b (first :: tail)
        = -mixingFractionalPart b last -
            importedChap4MixingInequalityFloorSum b (first :: tail) -
              (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ) := by
            simp [mixingInequalityTypeTwoRhs, hrev, importedChap4MixingInequalityFloorSum]
    _ = -mixingFractionalPart b last - chap4MixingInequalityFloorSum b (first :: tail) -
          (1 - mixingFractionalPart b last) * (⌊b first⌋ : ℝ) := by
      rw [importedChap4MixingInequalityFloorSum_eq_local]

/-- Helper for Exercise 7.21: with a fixed reverse decomposition, the equality face of
`(4.29)` is exactly the local Chapter 4 scalar equality inside `mixingHull b`. -/
lemma mem_mixingInequalityTypeOne_face_iff_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeOneCoeff b (first :: tail))
        (mixingInequalityTypeOneRhs b (first :: tail)) ↔
      x ∈ mixingHull b ∧
        mixingFractionalPart b last =
          x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x := by
  -- Use the repaired coefficient and rhs bridges so the face condition becomes a single scalar
  -- equality in the local normal form.
  rw [mem_face_set_iff, chap4MixingInequalityTypeOneCoeff_dotProduct,
    mixingInequalityTypeOneRhs_eq_local_of_reverse b first last tail revTail hrev]
  constructor
  · rintro ⟨hxHull, hxEq⟩
    refine ⟨hxHull, ?_⟩
    have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
    linarith
  · rintro ⟨hxHull, hxEq⟩
    refine ⟨hxHull, ?_⟩
    have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
    linarith

/-- Helper for Exercise 7.21: target-face membership for `(4.29)` is exactly hull membership plus
equality in the source scalar form of the mixing inequality. -/
lemma mem_mixingInequalityTypeOne_face_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeOneCoeff b s)
        (mixingInequalityTypeOneRhs b s) ↔
      x ∈ mixingHull b ∧
        match s.reverse with
        | [] => False
        | last :: _ =>
            mixingFractionalPart b last = x 0 + chap4MixingInequalityTypeOneSum b s x := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Fix the reverse shape once and hand the face proof to the repaired adapter.
          simpa [hrev] using
            mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev x

/-- Helper for Exercise 7.21: with a fixed reverse decomposition, the equality face of
`(4.30)` is exactly the local Chapter 4 scalar equality inside `mixingHull b`. -/
lemma mem_mixingInequalityTypeTwo_face_iff_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeTwoCoeff b (first :: tail))
        (mixingInequalityTypeTwoRhs b (first :: tail)) ↔
      x ∈ mixingHull b ∧
        mixingFractionalPart b last =
          x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
            (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ)) := by
  -- Use the repaired coefficient and rhs bridges so the face condition becomes a single scalar
  -- equality in the local normal form with the first-coordinate correction explicit.
  rw [mem_face_set_iff,
    chap4MixingInequalityTypeTwoCoeff_dotProduct_of_reverse b first last tail revTail hrev,
    mixingInequalityTypeTwoRhs_eq_local_of_reverse b first last tail revTail hrev]
  constructor
  · rintro ⟨hxHull, hxEq⟩
    refine ⟨hxHull, ?_⟩
    have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
    linarith
  · rintro ⟨hxHull, hxEq⟩
    refine ⟨hxHull, ?_⟩
    have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
    linarith

/-- Helper for Exercise 7.21: target-face membership for `(4.30)` is exactly hull membership plus
equality in the source scalar form of the mixing inequality. -/
lemma mem_mixingInequalityTypeTwo_face_iff
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    (x : Fin (n + 1) → ℝ) :
    x ∈ face_set
        (mixingHull b)
        (mixingInequalityTypeTwoCoeff b s)
        (mixingInequalityTypeTwoRhs b s) ↔
      x ∈ mixingHull b ∧
        match s, s.reverse with
        | first :: _, last :: _ =>
            mixingFractionalPart b last =
              x 0 + chap4MixingInequalityTypeOneSum b s x +
                (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))
        | _, _ => False := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          -- Fix the reverse shape once and hand the face proof to the repaired adapter.
          simpa [hrev] using
            mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev x

/-- Helper for Exercise 7.21: along a strictly increasing fractional-part chain, every tail
member has fractional part at least that of the head. -/
lemma mixingFractionalPart_le_of_mem_chain
    (b : Fin n → ℚ) {i : Fin n} {is : List (Fin n)}
    (hchain : (i :: is).IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    {j : Fin n} (hj : j ∈ is) :
    mixingFractionalPart b i ≤ mixingFractionalPart b j := by
  exact le_of_lt (hchain.rel_cons hj)

/-- Helper for Exercise 7.21: if every selected fractional part lies strictly above `c`, then the
slice witness at `c` makes the shifted type-one sum telescope to the last fractional part minus the
incoming base level. -/
lemma mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt
    (b : Fin n → ℚ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, c < mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - prev
  | prev, [], hgt, hchain => by
      -- The empty selected list has no shifted contribution.
      simp [chap4MixingInequalityTypeOneSumAux]
  | prev, [i], hgt, hchain => by
      -- The unique selected coordinate stays on the `1` branch because its fractional part
      -- lies strictly above the slice level.
      have hi_gt : c < mixingFractionalPart b i := hgt i (by simp)
      rw [chap4MixingInequalityTypeOneSumAux,
        mixingSliceWitness_shiftProfile_of_lt b hc_nonneg hc_lt_one hi_gt]
      simp [chap4MixingInequalityTypeOneSumAux]
  | prev, i :: j :: is, hgt, hchain => by
      -- Every selected coordinate still lies above the slice level, so each contribution is `1`
      -- and the coefficients telescope along the tail.
      have hi_gt : c < mixingFractionalPart b i := hgt i (by simp)
      have htail_gt :
          ∀ k ∈ j :: is, c < mixingFractionalPart b k := by
        intro k hk
        exact hgt k (by simp [hk])
      rw [chap4MixingInequalityTypeOneSumAux,
        mixingSliceWitness_shiftProfile_of_lt b hc_nonneg hc_lt_one hi_gt]
      simp only [mul_one]
      rw [mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt b hc_nonneg hc_lt_one
        (prev := mixingFractionalPart b i) (s := j :: is) htail_gt hchain.tail]
      cases hrev : (j :: is).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          simp [List.reverse_cons, hrev]

/-- Helper for Exercise 7.21: at the slice level determined by a selected fractional part, the
shifted type-one sum telescopes to the last fractional part minus that selected level. -/
lemma mixingInequalityTypeOneSumAux_eq_last_sub_target_of_mem
    (b : Fin n → ℚ) {i : Fin n} {s : List (Fin n)}
    (hchain : s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k))
    (hi : i ∈ s) :
    ∀ {prev : ℝ}, prev ≤ mixingFractionalPart b i →
      chap4MixingInequalityTypeOneSumAux b
          (mixingSliceWitness b (mixingFractionalPart b i)) prev s =
        match s.reverse with
        | [] => 0
        | last :: _ => mixingFractionalPart b last - mixingFractionalPart b i
  | prev, hprev_le => by
      -- Terms at or below the selected breakpoint contribute `0`, and the strict tail above that
      -- breakpoint contributes the remaining telescoping gap.
      have hfrac_nonneg : 0 ≤ mixingFractionalPart b i :=
        mixingFractionalPart_nonneg b i
      have hfrac_lt_one : mixingFractionalPart b i < 1 := by
        rw [mixingFractionalPart_eq_fract]
        exact Int.fract_lt_one (((b i : ℚ) : ℝ))
      cases s with
      | nil =>
          cases hi
      | cons j js =>
          rcases List.mem_cons.mp hi with rfl | htail_mem
          · rw [chap4MixingInequalityTypeOneSumAux,
              mixingSliceWitness_shiftProfile_of_le b hfrac_nonneg hfrac_lt_one le_rfl]
            simp only [mul_zero, zero_add]
            have htail_gt :
                ∀ k ∈ js, mixingFractionalPart b i < mixingFractionalPart b k := by
              intro k hk
              exact hchain.rel_cons hk
            rw [mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt b hfrac_nonneg
              hfrac_lt_one (prev := mixingFractionalPart b i) (s := js) htail_gt hchain.tail]
            cases hrev : js.reverse with
            | nil =>
                simp [List.reverse_cons, hrev]
            | cons last revTail =>
                simp [List.reverse_cons, hrev]
          · have hj_le : mixingFractionalPart b j ≤ mixingFractionalPart b i :=
              mixingFractionalPart_le_of_mem_chain b hchain htail_mem
            rw [chap4MixingInequalityTypeOneSumAux,
              mixingSliceWitness_shiftProfile_of_le b hfrac_nonneg hfrac_lt_one hj_le]
            simp only [mul_zero, zero_add]
            have htail :
                chap4MixingInequalityTypeOneSumAux b
                    (mixingSliceWitness b (mixingFractionalPart b i))
                    (mixingFractionalPart b j) js =
                  match js.reverse with
                  | [] => 0
                  | last :: _ => mixingFractionalPart b last - mixingFractionalPart b i := by
              exact mixingInequalityTypeOneSumAux_eq_last_sub_target_of_mem b hchain.tail
                htail_mem (prev := mixingFractionalPart b j) hj_le
            cases hrev : js.reverse with
            | nil =>
                have hjs : js = [] := by
                  simpa using hrev
                subst hjs
                simp at htail_mem
            | cons last revTail =>
                simpa [List.reverse_cons, hrev] using htail

/-- Helper for Exercise 7.21: the slice witness at any selected fractional part lies on the face
of mixing inequality `(4.29)`. -/
lemma mixingSliceWitness_mem_mixingInequalityTypeOne_face_of_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {i : Fin n} (hi : i ∈ s) :
    mixingSliceWitness b (mixingFractionalPart b i) ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          have hfrac_nonneg : 0 ≤ mixingFractionalPart b i :=
            mixingFractionalPart_nonneg b i
          have hfrac_lt_one : mixingFractionalPart b i < 1 := by
            rw [mixingFractionalPart_eq_fract]
            exact Int.fract_lt_one (((b i : ℚ) : ℝ))
          have hwitnessHull :
              mixingSliceWitness b (mixingFractionalPart b i) ∈ mixingHull b :=
            mixingSliceWitness_mem_mixingHull b hfrac_nonneg hfrac_lt_one
          have hsum :
              chap4MixingInequalityTypeOneSum b (first :: tail)
                  (mixingSliceWitness b (mixingFractionalPart b i)) =
                mixingFractionalPart b last - mixingFractionalPart b i := by
            simpa [chap4MixingInequalityTypeOneSum, hrev] using
              mixingInequalityTypeOneSumAux_eq_last_sub_target_of_mem b hfracChain hi
                (prev := 0) hfrac_nonneg
          rw [mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨hwitnessHull, ?_⟩
          have hzero :
              mixingSliceWitness b (mixingFractionalPart b i) 0 =
                mixingFractionalPart b i := by
            simp [mixingSliceWitness]
          rw [hzero, hsum]
          ring

/-- Helper for Exercise 7.21: the zero-level slice witness lies on the face of mixing inequality
`(4.29)`. -/
lemma mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingSliceWitness b 0 ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          have hwitnessHull : mixingSliceWitness b 0 ∈ mixingHull b :=
            mixingSliceWitness_mem_mixingHull b (show 0 ≤ (0 : ℝ) by simp)
              (show (0 : ℝ) < 1 by norm_num)
          have hgt :
              ∀ j ∈ first :: tail, (0 : ℝ) < mixingFractionalPart b j := by
            have hsSeq : IsMixingIndexSequence b (first :: tail) := by
              exact ⟨hfirst_pos, hindexChain, hfracChain⟩
            intro j hj
            exact mixingFractionalPart_pos_of_mem_isMixingIndexSequence b hsSeq hj
          have hsum :
              chap4MixingInequalityTypeOneSum b (first :: tail) (mixingSliceWitness b 0) =
                mixingFractionalPart b last := by
            simpa [chap4MixingInequalityTypeOneSum, hrev] using
              mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt b
                (show 0 ≤ (0 : ℝ) by simp) (show (0 : ℝ) < 1 by norm_num)
                (prev := 0) (s := first :: tail) hgt hfracChain
          rw [mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨hwitnessHull, ?_⟩
          simp [mixingSliceWitness, hsum]

/-- Helper for Exercise 7.21: the slice witness at any selected fractional part lies on the face
of mixing inequality `(4.30)`. -/
lemma mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {i : Fin n} (hi : i ∈ s) :
    mixingSliceWitness b (mixingFractionalPart b i) ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          have hfrac_nonneg : 0 ≤ mixingFractionalPart b i :=
            mixingFractionalPart_nonneg b i
          have hfrac_lt_one : mixingFractionalPart b i < 1 := by
            rw [mixingFractionalPart_eq_fract]
            exact Int.fract_lt_one (((b i : ℚ) : ℝ))
          have hwitnessHull :
              mixingSliceWitness b (mixingFractionalPart b i) ∈ mixingHull b :=
            mixingSliceWitness_mem_mixingHull b hfrac_nonneg hfrac_lt_one
          have hsum :
              chap4MixingInequalityTypeOneSum b (first :: tail)
                  (mixingSliceWitness b (mixingFractionalPart b i)) =
                mixingFractionalPart b last - mixingFractionalPart b i := by
            simpa [chap4MixingInequalityTypeOneSum, hrev] using
              mixingInequalityTypeOneSumAux_eq_last_sub_target_of_mem b hfracChain hi
                (prev := 0) hfrac_nonneg
          have hfirst_le : mixingFractionalPart b first ≤ mixingFractionalPart b i := by
            rcases List.mem_cons.mp hi with rfl | hiTail
            · exact le_rfl
            · exact mixingFractionalPart_le_of_mem_chain b hfracChain hiTail
          have hfirst_shift :
              mixingSliceWitness b (mixingFractionalPart b i) first.succ - (⌊b first⌋ : ℝ) = 0 :=
            mixingSliceWitness_shiftProfile_of_le b hfrac_nonneg hfrac_lt_one hfirst_le
          rw [mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨hwitnessHull, ?_⟩
          have hzero :
              mixingSliceWitness b (mixingFractionalPart b i) 0 =
                mixingFractionalPart b i := by
            simp [mixingSliceWitness]
          rw [hzero, hsum, hfirst_shift]
          ring

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence leaves the shifted
type-one sum unchanged. -/
lemma mixingInequalityTypeOneSum_add_nonselected_successorRay
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) {i : Fin n}
    (hi : i ∉ s) :
    chap4MixingInequalityTypeOneSum b s (x + exercise_3_29_ray i.succ) =
      chap4MixingInequalityTypeOneSum b s x := by
  -- A nonselected successor ray changes none of the selected successor coordinates in the sum.
  have haux :
      ∀ prev : ℝ, ∀ t : List (Fin n), i ∉ t →
        chap4MixingInequalityTypeOneSumAux b (x + exercise_3_29_ray i.succ) prev t =
          chap4MixingInequalityTypeOneSumAux b x prev t := by
    intro prev t
    induction t generalizing prev with
    | nil =>
        intro hnot
        rfl
    | cons j js ih =>
        intro hnot
        have hij : i ≠ j := by
          intro hEq
          exact hnot (by simp [hEq])
        have hsucc_ne : i.succ ≠ j.succ := fun hEq ↦ hij (by simpa using hEq)
        have hsucc_ne' : j.succ ≠ i.succ := by
          intro hEq
          exact hsucc_ne hEq.symm
        have htail : i ∉ js := by
          intro hmem
          exact hnot (by simp [hmem])
        have hcoord :
            (x + exercise_3_29_ray i.succ) j.succ - (⌊b j⌋ : ℝ) =
              x j.succ - (⌊b j⌋ : ℝ) := by
          calc
              (x + exercise_3_29_ray i.succ) j.succ - (⌊b j⌋ : ℝ)
                  = (x j.succ + 0) - (⌊b j⌋ : ℝ) := by
                    simp [Pi.add_apply, exercise_3_29_ray_apply, hsucc_ne']
              _ = x j.succ - (⌊b j⌋ : ℝ) := by
                  ring
        rw [chap4MixingInequalityTypeOneSumAux, chap4MixingInequalityTypeOneSumAux, hcoord,
          ih _ htail]
  simpa [chap4MixingInequalityTypeOneSum] using haux 0 s hi

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence stays inside the face
of mixing inequality `(4.29)`. -/
lemma mixingInequalityTypeOneFace_add_nonselected_successorRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ} {i : Fin n}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s))
    (hi : i ∉ s) :
    x + exercise_3_29_ray i.succ ∈
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          rcases (mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev x).1 hx with
            ⟨hxHull, hxEq⟩
          rw [mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨mixingHull_add_successorRay_mem b i hxHull, ?_⟩
          rw [mixingInequalityTypeOneSum_add_nonselected_successorRay b (first :: tail) x hi]
          have hzero :
              (x + exercise_3_29_ray i.succ) 0 = x 0 := by
            have hzero_ray : exercise_3_29_ray i.succ 0 = 0 := by
              have hsucc_ne_zero : (i.succ : Fin (n + 1)) ≠ 0 := by
                simp
              have hzero_ne_succ : (0 : Fin (n + 1)) ≠ i.succ := by
                intro hEq
                exact hsucc_ne_zero hEq.symm
              simp [exercise_3_29_ray_apply, hzero_ne_succ]
            simp [Pi.add_apply, hzero_ray]
          simpa [hzero] using hxEq

/-- Helper for Exercise 7.21: a successor ray outside the selected sequence stays inside the face
of mixing inequality `(4.30)`. -/
lemma mixingInequalityTypeTwoFace_add_nonselected_successorRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ} {i : Fin n}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s))
    (hi : i ∉ s) :
    x + exercise_3_29_ray i.succ ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          rcases (mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev x).1 hx with
            ⟨hxHull, hxEq⟩
          have hif : i ≠ first := by
            intro hEq
            exact hi (by simp [hEq])
          rw [mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨mixingHull_add_successorRay_mem b i hxHull, ?_⟩
          rw [mixingInequalityTypeOneSum_add_nonselected_successorRay b (first :: tail) x hi]
          have hzero :
              (x + exercise_3_29_ray i.succ) 0 = x 0 := by
            have hzero_ray : exercise_3_29_ray i.succ 0 = 0 := by
              have hsucc_ne_zero : (i.succ : Fin (n + 1)) ≠ 0 := by
                simp
              have hzero_ne_succ : (0 : Fin (n + 1)) ≠ i.succ := by
                intro hEq
                exact hsucc_ne_zero hEq.symm
              simp [exercise_3_29_ray_apply, hzero_ne_succ]
            simp [Pi.add_apply, hzero_ray]
          have hfirst :
              (x + exercise_3_29_ray i.succ) first.succ - (⌊b first⌋ : ℝ) =
                x first.succ - (⌊b first⌋ : ℝ) := by
            have hfirst_succ_ne : first.succ ≠ i.succ := by
              intro hEq
              exact hif (by simpa using hEq.symm)
            have hfirst_ray : exercise_3_29_ray i.succ first.succ = 0 := by
              simp [exercise_3_29_ray_apply, hfirst_succ_ne]
            simp [Pi.add_apply, hfirst_ray]
          rw [hzero, hfirst]
          exact hxEq

/-- Helper for Exercise 7.21: translating by the head ray changes the shifted type-one sum by the
incoming base level minus the last selected fractional part. -/
lemma mixingInequalityTypeOneSumAux_add_headRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      chap4MixingInequalityTypeOneSumAux b (x + exercise_3_29_ray (0 : Fin (n + 1))) prev s =
        chap4MixingInequalityTypeOneSumAux b x prev s +
          match s.reverse with
          | [] => 0
          | last :: _ => prev - mixingFractionalPart b last
  | prev, [] => by
      -- The empty selected set contributes no shifted sum.
      simp [chap4MixingInequalityTypeOneSumAux]
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
      rw [chap4MixingInequalityTypeOneSumAux, hcoord, mixingInequalityTypeOneSumAux_add_headRay]
      cases hrev : is.reverse with
      | nil =>
          simp [chap4MixingInequalityTypeOneSumAux, List.reverse_cons, hrev]
          ring
      | cons last revTail =>
          rw [chap4MixingInequalityTypeOneSumAux]
          simp [List.reverse_cons, hrev]
          ring

/-- Helper for Exercise 7.21: translating by the head ray subtracts the last selected fractional
part from the shifted type-one sum. -/
lemma mixingInequalityTypeOneSum_add_headRay
    (b : Fin n → ℚ) (s : List (Fin n)) (x : Fin (n + 1) → ℝ) :
    chap4MixingInequalityTypeOneSum b s (x + exercise_3_29_ray (0 : Fin (n + 1))) =
      chap4MixingInequalityTypeOneSum b s x +
        match s.reverse with
        | [] => 0
        | last :: _ => -mixingFractionalPart b last := by
  -- Specialize the recursive head-ray transport at base level `0`.
  simpa [chap4MixingInequalityTypeOneSum] using
    mixingInequalityTypeOneSumAux_add_headRay b x 0 s

/-- Helper for Exercise 7.21: translating by the head ray stays inside the face of mixing
inequality `(4.30)`. -/
lemma mixingInequalityTypeTwoFace_add_headRay_mem
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {x : Fin (n + 1) → ℝ}
    (hx : x ∈ face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s)) :
    x + exercise_3_29_ray (0 : Fin (n + 1)) ∈
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          rcases (mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev x).1 hx with
            ⟨hxHull, hxEq⟩
          rw [mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev]
          refine ⟨mixingHull_add_headRay_mem b hxHull, ?_⟩
          rw [mixingInequalityTypeOneSum_add_headRay b (first :: tail) x]
          rw [hrev]
          have hzero :
              (x + exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + 1 := by
            simp [exercise_3_29_ray_apply]
          have hfirst :
              (x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ) =
                (x first.succ - (⌊b first⌋ : ℝ)) - 1 := by
            have hsucc_ne_zero : ¬ (first.succ : Fin (n + 1)) = 0 := by
              simp
            calc
              (x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ - (⌊b first⌋ : ℝ)
                  = (x first.succ + (-1 : ℝ)) - (⌊b first⌋ : ℝ) := by
                      simp [Pi.add_apply, exercise_3_29_ray_apply, hsucc_ne_zero]
              _ = (x first.succ - (⌊b first⌋ : ℝ)) - 1 := by
                    ring
          rw [hzero, hfirst]
          ring_nf at hxEq ⊢
          linarith

/-- Helper for Exercise 7.21: shifting the zero slice by the head ray stays in `mixingHull b`
but leaves the type-one equality face. -/
lemma mixingSliceWitness_zero_add_headRay_not_mem_mixingInequalityTypeOne_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1)) ∉
      face_set (mixingHull b) (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          have hzeroFace :
              mixingSliceWitness b 0 ∈
                face_set
                  (mixingHull b)
                  (mixingInequalityTypeOneCoeff b (first :: tail))
                  (mixingInequalityTypeOneRhs b (first :: tail)) := by
            simpa using
              mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face b (first :: tail)
                ⟨hfirst_pos, hindexChain, hfracChain⟩
          rcases
              (mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev
                (mixingSliceWitness b 0)).1 hzeroFace with
            ⟨hzeroHull, hzeroEq⟩
          have hsum_zero :
              chap4MixingInequalityTypeOneSum b (first :: tail) (mixingSliceWitness b 0) =
                mixingFractionalPart b last := by
            have hzero_coord : mixingSliceWitness b 0 0 = 0 := by
              simp [mixingSliceWitness]
            rw [hzero_coord] at hzeroEq
            simpa using hzeroEq.symm
          intro hmem
          rcases
              (mem_mixingInequalityTypeOne_face_iff_of_reverse b first last tail revTail hrev
                (mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1)))).1 hmem with
            ⟨-, hshiftEq⟩
          have hsum_shift :
              chap4MixingInequalityTypeOneSum b (first :: tail)
                  (mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1))) =
                chap4MixingInequalityTypeOneSum b (first :: tail) (mixingSliceWitness b 0) -
                  mixingFractionalPart b last := by
            simpa [hrev] using
              mixingInequalityTypeOneSum_add_headRay b (first :: tail) (mixingSliceWitness b 0)
          have hshift_zero :
              (mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1))) 0 = 1 := by
            simp [mixingSliceWitness, exercise_3_29_ray_apply]
          have hlast_lt_one : mixingFractionalPart b last < 1 := by
            rw [mixingFractionalPart_eq_fract]
            exact Int.fract_lt_one (((b last : ℚ) : ℝ))
          rw [hshift_zero, hsum_shift, hsum_zero] at hshiftEq
          linarith

/-- Helper for Exercise 7.21: split a list at a chosen member. -/
private lemma exists_append_cons_of_mem
    {α : Type*} {x : α} {l : List α} (hx : x ∈ l) :
    ∃ left right, l = left ++ x :: right := by
  induction l with
  | nil =>
      cases hx
  | cons a tail ih =>
      rcases List.mem_cons.mp hx with rfl | hxTail
      · exact ⟨[], tail, by simp⟩
      · rcases ih hxTail with ⟨left, right, hsplit⟩
        exact ⟨a :: left, right, by simpa [List.cons_append] using congrArg (List.cons a) hsplit⟩

/-- Helper for Exercise 7.21: any tail member of `first :: tail` occurs immediately after some
earlier selected index. -/
private lemma exists_adjacent_split_of_mem_tail
    {α : Type*} {first curr : α} {tail : List α} (hcurr : curr ∈ tail) :
    ∃ pre : List α, ∃ prev : α, ∃ suffix : List α,
      first :: tail = pre ++ prev :: curr :: suffix := by
  -- Recover the predecessor by walking down the tail until `curr` becomes the next entry.
  induction tail generalizing first with
  | nil =>
      cases hcurr
  | cons next tail ih =>
      rcases List.mem_cons.mp hcurr with rfl | hcurrTail
      · exact ⟨[], first, tail, by simp⟩
      · rcases ih (first := next) hcurrTail with ⟨pre, prev, suffix, hsplit⟩
        exact ⟨first :: pre, prev, suffix, by
          simpa [List.cons_append] using congrArg (List.cons first) hsplit⟩

/-- Helper for Exercise 7.21: on an adjacent selected pair in an index-increasing list, the
recursive type-one coefficient owner reads off the negative fractional-part gap at the later
successor coordinate. -/
private lemma chap4MixingInequalityTypeOneCoeffAux_apply_succ_of_adjacent
    (b : Fin n → ℚ) (base : ℝ) (pre : List (Fin n)) (prev curr : Fin n) (suffix : List (Fin n))
    (hindexChain : (pre ++ prev :: curr :: suffix).IsChain (· < ·)) :
    chap4MixingInequalityTypeOneCoeffAux b base (pre ++ prev :: curr :: suffix) curr.succ =
      -(mixingFractionalPart b curr - mixingFractionalPart b prev) := by
  -- Route correction: peel only the irrelevant prefix coordinates, so the proof reaches the
  -- adjacent `prev, curr` pair without reopening the full coefficient normal form.
  induction pre generalizing base with
  | nil =>
      have hprev_lt_curr : prev < curr := by
        simpa using hindexChain.rel_cons (by simp)
      have hprev_ne_curr : prev ≠ curr := ne_of_lt hprev_lt_curr
      have hsucc_ne : curr.succ ≠ prev.succ := fun hEq ↦ hprev_ne_curr (by simpa using hEq.symm)
      have hcurr_not_mem_suffix : curr ∉ suffix := by
        intro hmem
        exact (lt_irrefl curr) (hindexChain.tail.rel_cons hmem)
      -- Only the `curr` contribution survives once the tail coordinate is shown to vanish.
      simp [chap4MixingInequalityTypeOneCoeffAux, hsucc_ne,
        chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b hcurr_not_mem_suffix]
  | cons i pre ih =>
      have hi_lt_curr : i < curr := by
        simpa [List.cons_append] using hindexChain.rel_cons (by simp)
      have hi_ne_curr : i ≠ curr := ne_of_lt hi_lt_curr
      have hsucc_ne : curr.succ ≠ i.succ := fun hEq ↦ hi_ne_curr (by simpa using hEq.symm)
      -- The head prefix coordinate is not `curr`, so the recursive tail proof applies directly.
      calc
        chap4MixingInequalityTypeOneCoeffAux b base ((i :: pre) ++ prev :: curr :: suffix)
            curr.succ =
          chap4MixingInequalityTypeOneCoeffAux b (mixingFractionalPart b i)
            (pre ++ prev :: curr :: suffix) curr.succ := by
              simp [chap4MixingInequalityTypeOneCoeffAux, List.cons_append, hsucc_ne]
        _ = -(mixingFractionalPart b curr - mixingFractionalPart b prev) := by
              exact ih (base := mixingFractionalPart b i) hindexChain.tail

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the successor-coordinate
part of the first selected witness difference has only the head selected contribution. -/
private lemma mixingSliceWitnessFirstSelectedStep_succSum_eq_of_offSupportZero
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hs : IsMixingIndexSequence b (first :: tail))
    {d : Fin (n + 1) → ℝ}
    (hoff : ∀ i : Fin n, i ∉ first :: tail → d i.succ = 0) :
    ∑ i : Fin n,
        d i.succ * ((mixingSliceWitness b (mixingFractionalPart b first) -
          mixingSliceWitness b 0) i.succ) =
      -d first.succ := by
  rcases hs with ⟨hfirst_pos, _, hfracChain⟩
  have hfrac_nonneg : 0 ≤ mixingFractionalPart b first :=
    mixingFractionalPart_nonneg b first
  have hfrac_lt_one : mixingFractionalPart b first < 1 := by
    rw [mixingFractionalPart_eq_fract]
    exact Int.fract_lt_one (((b first : ℚ) : ℝ))
  -- Every successor contribution vanishes except the first selected coordinate.
  rw [Fintype.sum_eq_single first]
  · have hfirst_diff :
        (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) first.succ =
          -1 := by
      have htarget_zero :
          mixingSliceWitness b (mixingFractionalPart b first) first.succ - (⌊b first⌋ : ℝ) = 0 :=
        mixingSliceWitness_shiftProfile_of_le b hfrac_nonneg hfrac_lt_one le_rfl
      have hzero_one : mixingSliceWitness b 0 first.succ - (⌊b first⌋ : ℝ) = 1 :=
        mixingSliceWitness_shiftProfile_of_lt b (show 0 ≤ (0 : ℝ) by simp)
          (show (0 : ℝ) < 1 by norm_num) hfirst_pos
      have htarget_coord :
          mixingSliceWitness b (mixingFractionalPart b first) first.succ = (⌊b first⌋ : ℝ) := by
        linarith
      have hzero_coord : mixingSliceWitness b 0 first.succ = (⌊b first⌋ : ℝ) + 1 := by
        linarith
      calc
        (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) first.succ =
            mixingSliceWitness b (mixingFractionalPart b first) first.succ -
              mixingSliceWitness b 0 first.succ := by
                simp
        _ = (⌊b first⌋ : ℝ) - ((⌊b first⌋ : ℝ) + 1) := by
          rw [htarget_coord, hzero_coord]
        _ = -1 := by ring
    rw [hfirst_diff]
    ring
  · intro i hi
    by_cases hisel : i ∈ first :: tail
    · rcases List.mem_cons.mp hisel with rfl | hiTail
      · exact (hi rfl).elim
      · have hfirst_lt_i : mixingFractionalPart b first < mixingFractionalPart b i :=
          hfracChain.rel_cons hiTail
        have hi_pos : (0 : ℝ) < mixingFractionalPart b i := lt_trans hfirst_pos hfirst_lt_i
        have hdiff_zero :
            (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) i.succ =
              0 := by
          have htarget_one :
              mixingSliceWitness b (mixingFractionalPart b first) i.succ - (⌊b i⌋ : ℝ) = 1 :=
            mixingSliceWitness_shiftProfile_of_lt b hfrac_nonneg hfrac_lt_one hfirst_lt_i
          have hzero_one : mixingSliceWitness b 0 i.succ - (⌊b i⌋ : ℝ) = 1 :=
            mixingSliceWitness_shiftProfile_of_lt b (show 0 ≤ (0 : ℝ) by simp)
              (show (0 : ℝ) < 1 by norm_num) hi_pos
          have htarget_coord :
              mixingSliceWitness b (mixingFractionalPart b first) i.succ = (⌊b i⌋ : ℝ) + 1 := by
            linarith
          have hzero_coord : mixingSliceWitness b 0 i.succ = (⌊b i⌋ : ℝ) + 1 := by
            linarith
          calc
            (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) i.succ =
                mixingSliceWitness b (mixingFractionalPart b first) i.succ -
                  mixingSliceWitness b 0 i.succ := by
                    simp
            _ = ((⌊b i⌋ : ℝ) + 1) - ((⌊b i⌋ : ℝ) + 1) := by
              rw [htarget_coord, hzero_coord]
            _ = 0 := by ring
        rw [hdiff_zero]
        ring
    · rw [hoff i hisel]
      ring

/-- Helper for Exercise 7.21: the first selected witness difference exposes the first selected
successor coordinate once off-support coordinates are known to vanish. -/
lemma mixingSliceWitnessFirstSelectedStep_dot_eq_of_offSupportZero
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hs : IsMixingIndexSequence b (first :: tail))
    {d : Fin (n + 1) → ℝ}
    (hoff : ∀ i : Fin n, i ∉ first :: tail → d i.succ = 0) :
    d ⬝ᵥ (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) =
      mixingFractionalPart b first * d 0 - d first.succ := by
  have hhead :
      (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) 0 =
        mixingFractionalPart b first := by
    -- The witness head coordinate is exactly the slice level.
    simp [mixingSliceWitness]
  have hsum :
      ∑ i : Fin n,
          d i.succ * ((mixingSliceWitness b (mixingFractionalPart b first) -
            mixingSliceWitness b 0) i.succ) =
        -d first.succ := by
    exact mixingSliceWitnessFirstSelectedStep_succSum_eq_of_offSupportZero b first tail hs hoff
  -- Expand the dot product once, then combine the head coordinate with the single surviving tail
  -- term.
  rw [dotProduct, Fin.sum_univ_succ, hhead, hsum]
  ring

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the successor-coordinate
part of an adjacent selected witness difference has only the later selected contribution. -/
private lemma mixingSliceWitnessAdjacentSelectedStep_succSum_eq_of_offSupportZero
    (b : Fin n → ℚ) (pre : List (Fin n)) (prev curr : Fin n) (suffix : List (Fin n))
    (hs : IsMixingIndexSequence b (pre ++ prev :: curr :: suffix))
    {d : Fin (n + 1) → ℝ}
    (hoff : ∀ i : Fin n, i ∉ pre ++ prev :: curr :: suffix → d i.succ = 0) :
    ∑ i : Fin n,
        d i.succ * ((mixingSliceWitness b (mixingFractionalPart b curr) -
          mixingSliceWitness b (mixingFractionalPart b prev)) i.succ) =
      -d curr.succ := by
  have hfracChain :
      (pre ++ prev :: curr :: suffix).IsChain
        (fun i j ↦ mixingFractionalPart b i < mixingFractionalPart b j) := by
    cases pre with
    | nil =>
        rcases hs with ⟨_, _, hfracChain⟩
        exact hfracChain
    | cons i pre =>
        rcases hs with ⟨_, _, hfracChain⟩
        exact hfracChain
  have hprev_nonneg : 0 ≤ mixingFractionalPart b prev :=
    mixingFractionalPart_nonneg b prev
  have hcurr_nonneg : 0 ≤ mixingFractionalPart b curr :=
    mixingFractionalPart_nonneg b curr
  have hprev_lt_one : mixingFractionalPart b prev < 1 := by
    rw [mixingFractionalPart_eq_fract]
    exact Int.fract_lt_one (((b prev : ℚ) : ℝ))
  have hcurr_lt_one : mixingFractionalPart b curr < 1 := by
    rw [mixingFractionalPart_eq_fract]
    exact Int.fract_lt_one (((b curr : ℚ) : ℝ))
  have hdropFracChain :
      ∀ {left right : List (Fin n)},
        (left ++ right).IsChain (fun i j ↦ mixingFractionalPart b i < mixingFractionalPart b j) →
          right.IsChain (fun i j ↦ mixingFractionalPart b i < mixingFractionalPart b j) := by
    intro left
    induction left with
    | nil =>
        intro right hchain
        simpa using hchain
    | cons i left ih =>
        intro right hchain
        simpa [List.cons_append] using ih hchain.tail
  have hprevCurrChain :
      (prev :: curr :: suffix).IsChain
        (fun i j ↦ mixingFractionalPart b i < mixingFractionalPart b j) := by
    simpa using
      hdropFracChain (left := pre) (right := prev :: curr :: suffix) hfracChain
  have hcurrSuffixChain :
      (curr :: suffix).IsChain (fun i j ↦ mixingFractionalPart b i < mixingFractionalPart b j) := by
    exact hprevCurrChain.tail
  have hprev_lt_curr : mixingFractionalPart b prev < mixingFractionalPart b curr := by
    simpa using hprevCurrChain.rel_head
  -- Only the later selected coordinate `curr.succ` survives in the successor sum.
  rw [Fintype.sum_eq_single curr]
  · have hcurr_diff :
        (mixingSliceWitness b (mixingFractionalPart b curr) -
            mixingSliceWitness b (mixingFractionalPart b prev)) curr.succ =
          -1 := by
      have htarget_zero :
          mixingSliceWitness b (mixingFractionalPart b curr) curr.succ - (⌊b curr⌋ : ℝ) = 0 :=
        mixingSliceWitness_shiftProfile_of_le b hcurr_nonneg hcurr_lt_one le_rfl
      have hprev_one :
          mixingSliceWitness b (mixingFractionalPart b prev) curr.succ - (⌊b curr⌋ : ℝ) = 1 :=
        mixingSliceWitness_shiftProfile_of_lt b hprev_nonneg hprev_lt_one hprev_lt_curr
      have htarget_coord :
          mixingSliceWitness b (mixingFractionalPart b curr) curr.succ = (⌊b curr⌋ : ℝ) := by
        linarith
      have hprev_coord :
          mixingSliceWitness b (mixingFractionalPart b prev) curr.succ = (⌊b curr⌋ : ℝ) + 1 := by
        linarith
      calc
        (mixingSliceWitness b (mixingFractionalPart b curr) -
            mixingSliceWitness b (mixingFractionalPart b prev)) curr.succ =
            mixingSliceWitness b (mixingFractionalPart b curr) curr.succ -
              mixingSliceWitness b (mixingFractionalPart b prev) curr.succ := by
                simp
        _ = (⌊b curr⌋ : ℝ) - ((⌊b curr⌋ : ℝ) + 1) := by
          rw [htarget_coord, hprev_coord]
        _ = -1 := by ring
    rw [hcurr_diff]
    ring
  · intro i hi
    by_cases hisel : i ∈ pre ++ prev :: curr :: suffix
    · have hdiff_zero :
          (mixingSliceWitness b (mixingFractionalPart b curr) -
              mixingSliceWitness b (mixingFractionalPart b prev)) i.succ =
            0 := by
        rw [List.mem_append] at hisel
        rcases hisel with hiPre | hiRest
        · rcases exists_append_cons_of_mem hiPre with ⟨left, right, hsplitPre⟩
          have hchainAtI :
              (i :: right ++ prev :: curr :: suffix).IsChain
                  (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
            have hfull :
                (left ++ i :: right ++ prev :: curr :: suffix).IsChain
                    (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
              simpa [hsplitPre, List.append_assoc] using hfracChain
            have hfull' :
                (left ++ (i :: right ++ prev :: curr :: suffix)).IsChain
                    (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) := by
              simpa [List.append_assoc] using hfull
            exact hdropFracChain (left := left) (right := i :: right ++ prev :: curr :: suffix)
              hfull'
          have hi_le_prev : mixingFractionalPart b i ≤ mixingFractionalPart b prev := by
            simpa [List.append_assoc] using
              mixingFractionalPart_le_of_mem_chain b hchainAtI (j := prev) (by simp)
          have hi_le_curr : mixingFractionalPart b i ≤ mixingFractionalPart b curr :=
            le_trans hi_le_prev (le_of_lt hprev_lt_curr)
          have hcurr_zero :
              mixingSliceWitness b (mixingFractionalPart b curr) i.succ - (⌊b i⌋ : ℝ) = 0 :=
            mixingSliceWitness_shiftProfile_of_le b hcurr_nonneg hcurr_lt_one hi_le_curr
          have hprev_zero :
              mixingSliceWitness b (mixingFractionalPart b prev) i.succ - (⌊b i⌋ : ℝ) = 0 :=
            mixingSliceWitness_shiftProfile_of_le b hprev_nonneg hprev_lt_one hi_le_prev
          have hcurr_coord :
              mixingSliceWitness b (mixingFractionalPart b curr) i.succ = (⌊b i⌋ : ℝ) := by
            linarith
          have hprev_coord :
              mixingSliceWitness b (mixingFractionalPart b prev) i.succ = (⌊b i⌋ : ℝ) := by
            linarith
          calc
            (mixingSliceWitness b (mixingFractionalPart b curr) -
                mixingSliceWitness b (mixingFractionalPart b prev)) i.succ =
                mixingSliceWitness b (mixingFractionalPart b curr) i.succ -
                  mixingSliceWitness b (mixingFractionalPart b prev) i.succ := by
                    simp
            _ = (⌊b i⌋ : ℝ) - (⌊b i⌋ : ℝ) := by
              rw [hcurr_coord, hprev_coord]
            _ = 0 := by ring
        · rcases List.mem_cons.mp hiRest with hEqPrev | hiRest
          · have hcurr_zero :
              mixingSliceWitness b (mixingFractionalPart b curr) prev.succ - (⌊b prev⌋ : ℝ) = 0 :=
            mixingSliceWitness_shiftProfile_of_le b hcurr_nonneg hcurr_lt_one (le_of_lt hprev_lt_curr)
            have hprev_zero :
                mixingSliceWitness b (mixingFractionalPart b prev) prev.succ - (⌊b prev⌋ : ℝ) = 0 :=
              mixingSliceWitness_shiftProfile_of_le b hprev_nonneg hprev_lt_one le_rfl
            have hcurr_coord :
                mixingSliceWitness b (mixingFractionalPart b curr) prev.succ = (⌊b prev⌋ : ℝ) := by
              linarith
            have hprev_coord :
                mixingSliceWitness b (mixingFractionalPart b prev) prev.succ = (⌊b prev⌋ : ℝ) := by
              linarith
            have hprev_diff_zero :
                (mixingSliceWitness b (mixingFractionalPart b curr) -
                    mixingSliceWitness b (mixingFractionalPart b prev)) prev.succ =
                  0 := by
              calc
                (mixingSliceWitness b (mixingFractionalPart b curr) -
                    mixingSliceWitness b (mixingFractionalPart b prev)) prev.succ =
                    mixingSliceWitness b (mixingFractionalPart b curr) prev.succ -
                      mixingSliceWitness b (mixingFractionalPart b prev) prev.succ := by
                        simp
                _ = (⌊b prev⌋ : ℝ) - (⌊b prev⌋ : ℝ) := by
                  rw [hcurr_coord, hprev_coord]
                _ = 0 := by ring
            simpa [hEqPrev] using hprev_diff_zero
          · rcases List.mem_cons.mp hiRest with hEqCurr | hiSuffix
            · exact (hi hEqCurr).elim
            · have hcurr_lt_i : mixingFractionalPart b curr < mixingFractionalPart b i := by
                simpa using hcurrSuffixChain.rel_cons hiSuffix
              have hprev_lt_i : mixingFractionalPart b prev < mixingFractionalPart b i :=
                lt_trans hprev_lt_curr hcurr_lt_i
              have hcurr_one :
                  mixingSliceWitness b (mixingFractionalPart b curr) i.succ - (⌊b i⌋ : ℝ) = 1 :=
                mixingSliceWitness_shiftProfile_of_lt b hcurr_nonneg hcurr_lt_one hcurr_lt_i
              have hprev_one :
                  mixingSliceWitness b (mixingFractionalPart b prev) i.succ - (⌊b i⌋ : ℝ) = 1 :=
                mixingSliceWitness_shiftProfile_of_lt b hprev_nonneg hprev_lt_one hprev_lt_i
              have hcurr_coord :
                  mixingSliceWitness b (mixingFractionalPart b curr) i.succ = (⌊b i⌋ : ℝ) + 1 := by
                linarith
              have hprev_coord :
                  mixingSliceWitness b (mixingFractionalPart b prev) i.succ = (⌊b i⌋ : ℝ) + 1 := by
                linarith
              calc
                (mixingSliceWitness b (mixingFractionalPart b curr) -
                    mixingSliceWitness b (mixingFractionalPart b prev)) i.succ =
                    mixingSliceWitness b (mixingFractionalPart b curr) i.succ -
                      mixingSliceWitness b (mixingFractionalPart b prev) i.succ := by
                        simp
                _ = ((⌊b i⌋ : ℝ) + 1) - ((⌊b i⌋ : ℝ) + 1) := by
                  rw [hcurr_coord, hprev_coord]
                _ = 0 := by ring
      rw [hdiff_zero]
      ring
    · rw [hoff i hisel]
      ring

/-- Helper for Exercise 7.21: the difference of adjacent selected slice witnesses exposes the
later selected successor coordinate once off-support coordinates vanish. -/
lemma mixingSliceWitnessAdjacentSelectedStep_dot_eq_of_offSupportZero
    (b : Fin n → ℚ) (pre : List (Fin n)) (prev curr : Fin n) (suffix : List (Fin n))
    (hs : IsMixingIndexSequence b (pre ++ prev :: curr :: suffix))
    {d : Fin (n + 1) → ℝ}
    (hoff : ∀ i : Fin n, i ∉ pre ++ prev :: curr :: suffix → d i.succ = 0) :
    d ⬝ᵥ (mixingSliceWitness b (mixingFractionalPart b curr) -
      mixingSliceWitness b (mixingFractionalPart b prev)) =
      (mixingFractionalPart b curr - mixingFractionalPart b prev) * d 0 - d curr.succ := by
  have hhead :
      (mixingSliceWitness b (mixingFractionalPart b curr) -
          mixingSliceWitness b (mixingFractionalPart b prev)) 0 =
        mixingFractionalPart b curr - mixingFractionalPart b prev := by
    -- The witness head coordinate tracks the slice level exactly.
    simp [mixingSliceWitness]
  have hsum :
      ∑ i : Fin n,
          d i.succ * ((mixingSliceWitness b (mixingFractionalPart b curr) -
            mixingSliceWitness b (mixingFractionalPart b prev)) i.succ) =
        -d curr.succ := by
    exact
      mixingSliceWitnessAdjacentSelectedStep_succSum_eq_of_offSupportZero b pre prev curr suffix hs
        hoff
  -- Expand the dot product once and combine the head coordinate with the unique surviving
  -- `curr.succ` contribution.
  rw [dotProduct, Fin.sum_univ_succ, hhead, hsum]
  ring

/-- Helper for Exercise 7.21: the type-two coefficient vector differs from the type-one vector at
the first selected successor coordinate by exactly the head correction term. -/
lemma mixingInequalityTypeTwoCoeff_apply_headSucc_of_reverse
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail) :
    (mixingInequalityTypeTwoCoeff b (first :: tail)) first.succ =
      (mixingInequalityTypeOneCoeff b (first :: tail)) first.succ -
        (1 - mixingFractionalPart b last) := by
  -- Unfold only the one-coordinate correction at `first.succ`.
  simp [mixingInequalityTypeTwoCoeff, hrev]
  ring

/-- Helper for Exercise 7.21: on every tail successor coordinate, the type-two coefficient vector
agrees with the type-one vector. -/
lemma mixingInequalityTypeTwoCoeff_apply_succ_of_mem_tail
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hrev : (first :: tail).reverse = last :: revTail)
    (hindexChain : (first :: tail).IsChain (· < ·))
    {i : Fin n} (hi : i ∈ tail) :
    (mixingInequalityTypeTwoCoeff b (first :: tail)) i.succ =
      (mixingInequalityTypeOneCoeff b (first :: tail)) i.succ := by
  have hfirst_lt_i : first < i := hindexChain.rel_cons hi
  have hne : i ≠ first := ne_of_gt hfirst_lt_i
  -- Tail coordinates do not see the extra type-two correction.
  simp [mixingInequalityTypeTwoCoeff, hrev, hne]

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: any exposed face
containing the equality set of `(4.29)` has exposing functional proportional to the type-one
coefficient vector. -/
private lemma typeOneContainingFaceFunctional_eq_smulCoeff
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hsSeq : IsMixingIndexSequence b (first :: tail))
    {d : Fin (n + 1) → ℝ} {β : ℝ}
    (hsubsetFace :
      face_set
          (mixingHull b)
          (mixingInequalityTypeOneCoeff b (first :: tail))
          (mixingInequalityTypeOneRhs b (first :: tail)) ⊆
        face_set (mixingHull b) d β) :
    d = (-d 0) • mixingInequalityTypeOneCoeff b (first :: tail) := by
  rcases hsSeq with ⟨hfirst_pos, hindexChain, hfracChain⟩
  have hxZeroFace :
      mixingSliceWitness b 0 ∈
        face_set
          (mixingHull b)
          (mixingInequalityTypeOneCoeff b (first :: tail))
          (mixingInequalityTypeOneRhs b (first :: tail)) := by
    -- The zero slice witness is the anchor point for the type-one equality face.
    simpa using mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face b (first :: tail) hsSeq
  have hxZeroG : mixingSliceWitness b 0 ∈ face_set (mixingHull b) d β := hsubsetFace hxZeroFace
  have hoff : ∀ i : Fin n, i ∉ first :: tail → d i.succ = 0 := by
    intro i hi
    have hxRayFace :
        mixingSliceWitness b 0 + exercise_3_29_ray i.succ ∈
          face_set
            (mixingHull b)
            (mixingInequalityTypeOneCoeff b (first :: tail))
            (mixingInequalityTypeOneRhs b (first :: tail)) := by
      -- Nonselected successor rays stay inside the target equality face.
      simpa using
        mixingInequalityTypeOneFace_add_nonselected_successorRay_mem b (first :: tail) hsSeq
          hxZeroFace hi
    have hxRayG :
        mixingSliceWitness b 0 + exercise_3_29_ray i.succ ∈ face_set (mixingHull b) d β :=
      hsubsetFace hxRayFace
    have hdot_zero : d ⬝ᵥ exercise_3_29_ray i.succ = 0 := by
      -- Subtract the two points of the exposed face to isolate the ray direction.
      simpa [sub_eq_add_neg, Pi.add_apply] using faceSet_dot_sub_eq_zero_of_two_mem hxRayG hxZeroG
    simpa [dotProduct_exercise_3_29_ray_succ] using hdot_zero
  funext j
  refine Fin.cases ?_ ?_ j
  · -- The zeroth coordinate is always the scalar multiple of `-1`.
    symm
    calc
      ((-d 0) • mixingInequalityTypeOneCoeff b (first :: tail)) 0 = (-d 0) * (-1 : ℝ) := by
        simp [mixingInequalityTypeOneCoeff, smul_eq_mul]
      _ = d 0 := by ring
  · intro i
    by_cases his : i ∈ first :: tail
    · rcases List.mem_cons.mp his with rfl | hiTail
      · have hxFirstFace :
            mixingSliceWitness b (mixingFractionalPart b first) ∈
              face_set
                (mixingHull b)
                (mixingInequalityTypeOneCoeff b (first :: tail))
                (mixingInequalityTypeOneRhs b (first :: tail)) := by
          -- The first selected breakpoint witness also lies on the type-one face.
          simpa using
            mixingSliceWitness_mem_mixingInequalityTypeOne_face_of_mem b (first :: tail) hsSeq
              (by simp)
        have hxFirstG :
            mixingSliceWitness b (mixingFractionalPart b first) ∈ face_set (mixingHull b) d β :=
          hsubsetFace hxFirstFace
        have hfirst_step : mixingFractionalPart b first * d 0 - d first.succ = 0 := by
          -- The first selected witness difference exposes the first successor coordinate.
          calc
            mixingFractionalPart b first * d 0 - d first.succ =
                d ⬝ᵥ
                  (mixingSliceWitness b (mixingFractionalPart b first) - mixingSliceWitness b 0) := by
                    symm
                    exact
                      mixingSliceWitnessFirstSelectedStep_dot_eq_of_offSupportZero b first tail hsSeq
                        hoff
            _ = 0 := by
              simpa using faceSet_dot_sub_eq_zero_of_two_mem hxFirstG hxZeroG
        have hdFirst : d first.succ = mixingFractionalPart b first * d 0 := by
          linarith
        have hcoeffFirst :
            mixingInequalityTypeOneCoeff b (first :: tail) first.succ =
              -mixingFractionalPart b first := by
          simpa using mixingInequalityTypeOneCoeff_apply_headSucc b first tail hsSeq
        calc
          d first.succ = mixingFractionalPart b first * d 0 := hdFirst
          _ = (-d 0) * (-mixingFractionalPart b first) := by ring
          _ = ((-d 0) • mixingInequalityTypeOneCoeff b (first :: tail)) first.succ := by
            simp [hcoeffFirst, smul_eq_mul]
      · have hsplit := exists_adjacent_split_of_mem_tail (first := first) (curr := i) hiTail
        rcases hsplit with ⟨pre, prev, suffix, hsplit⟩
        have hsAdj : IsMixingIndexSequence b (pre ++ prev :: i :: suffix) := by
          simpa [hsplit] using hsSeq
        have hindexAdj : (pre ++ prev :: i :: suffix).IsChain (· < ·) := by
          simpa [hsplit] using hindexChain
        have hxPrevFace :
            mixingSliceWitness b (mixingFractionalPart b prev) ∈
              face_set
                (mixingHull b)
                (mixingInequalityTypeOneCoeff b (first :: tail))
                (mixingInequalityTypeOneRhs b (first :: tail)) := by
          -- Every selected breakpoint witness stays on the type-one face.
          simpa [hsplit] using
            mixingSliceWitness_mem_mixingInequalityTypeOne_face_of_mem b (first :: tail) hsSeq
              (by simp [hsplit])
        have hxCurrFace :
            mixingSliceWitness b (mixingFractionalPart b i) ∈
              face_set
                (mixingHull b)
                (mixingInequalityTypeOneCoeff b (first :: tail))
                (mixingInequalityTypeOneRhs b (first :: tail)) := by
          simpa using
            mixingSliceWitness_mem_mixingInequalityTypeOne_face_of_mem b (first :: tail) hsSeq
              (by simp)
        have hxPrevG :
            mixingSliceWitness b (mixingFractionalPart b prev) ∈ face_set (mixingHull b) d β :=
          hsubsetFace hxPrevFace
        have hxCurrG :
            mixingSliceWitness b (mixingFractionalPart b i) ∈ face_set (mixingHull b) d β :=
          hsubsetFace hxCurrFace
        have hadj_step :
            (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 - d i.succ = 0 := by
          -- Adjacent selected witnesses expose the next selected coefficient.
          calc
            (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 - d i.succ =
                d ⬝ᵥ
                  (mixingSliceWitness b (mixingFractionalPart b i) -
                    mixingSliceWitness b (mixingFractionalPart b prev)) := by
                    symm
                    simpa [hsplit] using
                      mixingSliceWitnessAdjacentSelectedStep_dot_eq_of_offSupportZero b pre prev i
                        suffix hsAdj hoff
            _ = 0 := by
              simpa using faceSet_dot_sub_eq_zero_of_two_mem hxCurrG hxPrevG
        have hdCurr :
            d i.succ = (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 := by
          linarith
        have hcoeffCurr :
            mixingInequalityTypeOneCoeff b (first :: tail) i.succ =
              -(mixingFractionalPart b i - mixingFractionalPart b prev) := by
          calc
            mixingInequalityTypeOneCoeff b (first :: tail) i.succ =
                chap4MixingInequalityTypeOneCoeffAux b 0 (first :: tail) i.succ := by
                  exact mixingInequalityTypeOneCoeff_apply_succ b (first :: tail) i
            _ = -(mixingFractionalPart b i - mixingFractionalPart b prev) := by
              simpa [hsplit] using
                chap4MixingInequalityTypeOneCoeffAux_apply_succ_of_adjacent b 0 pre prev i suffix
                  hindexAdj
        calc
          d i.succ = (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 := hdCurr
          _ = (-d 0) * (-(mixingFractionalPart b i - mixingFractionalPart b prev)) := by ring
          _ = ((-d 0) • mixingInequalityTypeOneCoeff b (first :: tail)) i.succ := by
            simp [hcoeffCurr, smul_eq_mul]
    · have hdOff : d i.succ = 0 := hoff i his
      have hcoeffOff : mixingInequalityTypeOneCoeff b (first :: tail) i.succ = 0 := by
        rw [mixingInequalityTypeOneCoeff_apply_succ]
        exact chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b his
      simp [hdOff, hcoeffOff, smul_eq_mul]

/-- Helper for Exercise 7.21: any proper face containing the equality set of mixing inequality
`(4.29)` already equals that face. -/
lemma mixingInequalityTypeOne_face_eq_of_subset_proper_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {G : Set (Fin (n + 1) → ℝ)}
    (hG : is_proper_face (mixingHull b) G)
    (hsubset :
      face_set
          (mixingHull b)
          (mixingInequalityTypeOneCoeff b s)
          (mixingInequalityTypeOneRhs b s) ⊆
        G) :
    G =
      face_set
        (mixingHull b)
        (mixingInequalityTypeOneCoeff b s)
        (mixingInequalityTypeOneRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      have hsSeq : IsMixingIndexSequence b (first :: tail) := by
        exact ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          rcases is_proper_face_iff.mp hG with ⟨hG_exposed, hG_nonempty, hG_ssubset⟩
          rcases isExposed_iff_eq_empty_or_eq_face_set.mp hG_exposed with hG_empty |
              ⟨d, β, _, hG_eq⟩
          · obtain ⟨x, hx⟩ := hG_nonempty
            simp [hG_empty] at hx
          · have hxZeroFace :
                mixingSliceWitness b 0 ∈
                  face_set
                    (mixingHull b)
                    (mixingInequalityTypeOneCoeff b (first :: tail))
                    (mixingInequalityTypeOneRhs b (first :: tail)) := by
              -- The zero slice witness is the anchor point for the type-one equality face.
              simpa using
                mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face b (first :: tail) hsSeq
            have hxZeroG :
                mixingSliceWitness b 0 ∈ face_set (mixingHull b) d β := by
              -- Push the anchor point through the containing-face hypothesis.
              simpa [hG_eq] using hsubset hxZeroFace
            have hsubsetFace :
                face_set
                    (mixingHull b)
                    (mixingInequalityTypeOneCoeff b (first :: tail))
                    (mixingInequalityTypeOneRhs b (first :: tail)) ⊆
                  face_set (mixingHull b) d β := by
              intro x hx
              simpa [hG_eq] using hsubset hx
            have hd_eq :
                d = (-d 0) • mixingInequalityTypeOneCoeff b (first :: tail) := by
              exact
                typeOneContainingFaceFunctional_eq_smulCoeff b first tail hsSeq
                  hsubsetFace
            have hlam_ne : -d 0 ≠ 0 := by
              intro hlam_zero
              have hd_zero : d = 0 := by
                simpa [hlam_zero] using hd_eq
              obtain ⟨x, hxGmem⟩ := hG_nonempty
              have hβ_zero : β = 0 := by
                -- Any point on the face forces the rhs to vanish once the exposing vector is zero.
                simpa [hd_zero] using ((mem_face_set_iff.mp (by simpa [hG_eq] using hxGmem)).2).symm
              have hG_all :
                  G = mixingHull b := by
                -- The zero functional cuts out the whole polyhedron.
                rw [hG_eq]
                ext x
                rw [mem_face_set_iff]
                simp [hd_zero, hβ_zero]
              exact hG_ssubset.ne hG_all
            have hβ_eq :
                β =
                  (-d 0) * mixingInequalityTypeOneRhs b (first :: tail) := by
              -- Evaluate the normalized exposing functional at the anchor point.
              calc
                β = d ⬝ᵥ mixingSliceWitness b 0 := ((mem_face_set_iff.mp hxZeroG).2).symm
                _ =
                    ((-d 0) • mixingInequalityTypeOneCoeff b (first :: tail)) ⬝ᵥ
                      mixingSliceWitness b 0 := by
                        rw [hd_eq]
                _ =
                    (-d 0) *
                      (mixingInequalityTypeOneCoeff b (first :: tail) ⬝ᵥ
                        mixingSliceWitness b 0) := by
                          simpa [smul_eq_mul] using
                            (smul_dotProduct (-d 0)
                              (mixingInequalityTypeOneCoeff b (first :: tail))
                              (mixingSliceWitness b 0))
                _ = (-d 0) * mixingInequalityTypeOneRhs b (first :: tail) := by
                      rw [(mem_face_set_iff.mp hxZeroFace).2]
            -- Repackage `G` as the same nonzero scaling of the target face.
            calc
              G = face_set (mixingHull b) d β := hG_eq
              _ =
                  face_set
                    (mixingHull b)
                    ((-d 0) • mixingInequalityTypeOneCoeff b (first :: tail))
                    ((-d 0) * mixingInequalityTypeOneRhs b (first :: tail)) := by
                      rw [hd_eq, hβ_eq]
              _ =
                  face_set
                    (mixingHull b)
                    (mixingInequalityTypeOneCoeff b (first :: tail))
                    (mixingInequalityTypeOneRhs b (first :: tail)) :=
                      faceSet_eq_of_nonzero_smul hlam_ne


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
          rw [mixingInequalityTypeOne, hrev, chap4MixingInequalityTypeOneCoeff_dotProduct,
            mixingInequalityTypeOneRhs_eq_local_of_reverse b first last tail revTail hrev]
          have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
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
          rw [chap4MixingInequalityTypeTwoCoeff_dotProduct_of_reverse b first last tail revTail hrev,
            mixingInequalityTypeTwoRhs_eq_local_of_reverse b first last tail revTail hrev]
          have hsum := chap4MixingInequalityTypeOneRawSum_eq_shifted_add_floor b x (first :: tail)
          constructor
          · intro hineq
            have hsrc :
                mixingFractionalPart b last ≤
                  x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                    (1 - mixingFractionalPart b last) *
                      (x first.succ - (⌊b first⌋ : ℝ)) := by
              linarith
            simpa [mixingInequalityTypeTwo, hrev] using hsrc
          · intro hineq
            have hsrc :
                mixingFractionalPart b last ≤
                  x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                    (1 - mixingFractionalPart b last) *
                      (x first.succ - (⌊b first⌋ : ℝ)) := by
              simpa [mixingInequalityTypeTwo, hrev] using hineq
            linarith

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: starting from any base
level `prev ≤ c`, the slice witness at `c` satisfies every shifted type-one inequality attached
to a strictly increasing fractional-part chain above `prev`. -/
private lemma chap4MixingInequalityTypeOneSumAux_last_le_sliceWitness
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
            c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev s
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
                simpa [chap4MixingInequalityTypeOneSumAux, hshift] using hi_le_c
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
                    simpa [chap4MixingInequalityTypeOneSumAux, hshift, List.reverse_cons, hrev] using
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
              chap4MixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt
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
                      c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) prev
                        (i :: is) := by
                  linarith
                simpa using hlast

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every slice witness on
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
                    c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0 (j :: js) := by
            -- The zero-start family reduces to the positive tail with base level `prev = 0`.
            simpa using
              chap4MixingInequalityTypeOneSumAux_last_le_sliceWitness
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
                    c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0 (j :: js) +
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
            chap4MixingInequalityTypeOneSumAux_last_le_sliceWitness
              (b := b) hc_nonneg hc_lt_one (prev := 0) (s := first :: tail) hc_nonneg
              (fun j _hj ↦ mixingFractionalPart_nonneg b j) hfracChain
        ·
          have htypeOne :
              match (first :: tail).reverse with
              | [] => True
              | last :: _ =>
                  mixingFractionalPart b last ≤
                    c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0
                      (first :: tail) := by
            -- Reuse the same tail inequality before adding the nonnegative type-two correction.
            simpa using
              chap4MixingInequalityTypeOneSumAux_last_le_sliceWitness
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
                    c + chap4MixingInequalityTypeOneSumAux b (mixingSliceWitness b c) 0
                        (first :: tail) +
                      (1 - mixingFractionalPart b last) *
                        (mixingSliceWitness b c first.succ - (⌊b first⌋ : ℝ)) := by
                linarith
              simpa [mixingInequalityTypeTwo, mixingInequalityTypeOneSum, mixingSliceWitness, hrev]
                using hsrc

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: adding the head ray
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
                chap4MixingInequalityTypeOneSum b s
                    (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                  chap4MixingInequalityTypeOneSum b s x - mixingFractionalPart b last := by
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
                    chap4MixingInequalityTypeOneSum b (first :: tail)
                        (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                      chap4MixingInequalityTypeOneSum b (first :: tail) x -
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
                      x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hxTypeTwo
                have hsum :
                    chap4MixingInequalityTypeOneSum b (first :: tail)
                        (x + exercise_3_29_ray (0 : Fin (n + 1))) =
                      chap4MixingInequalityTypeOneSum b (first :: tail) x -
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
                        chap4MixingInequalityTypeOneSum b (first :: tail)
                          (x + exercise_3_29_ray (0 : Fin (n + 1))) +
                        (1 - mixingFractionalPart b last) *
                          ((x + exercise_3_29_ray (0 : Fin (n + 1))) first.succ -
                            (⌊b first⌋ : ℝ)) := by
                  rw [hsum, hhead, hshift]
                  linarith
                simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: adding a successor ray can
only increase the shifted type-one sum along a strictly increasing fractional-part chain. -/
private lemma chap4MixingInequalityTypeOneSumAux_le_add_successorRay
    (b : Fin n → ℚ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    ∀ {prev : ℝ} {s : List (Fin n)},
      (∀ j ∈ s, prev ≤ mixingFractionalPart b j) →
      s.IsChain (fun j k ↦ mixingFractionalPart b j < mixingFractionalPart b k) →
      chap4MixingInequalityTypeOneSumAux b x prev s ≤
        chap4MixingInequalityTypeOneSumAux b (x + exercise_3_29_ray i.succ) prev s := by
  intro prev s hprev hchain
  induction s generalizing prev with
  | nil =>
      -- The empty selected list contributes no shifted sum in either spelling.
      simp [chap4MixingInequalityTypeOneSumAux]
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
        rw [chap4MixingInequalityTypeOneSumAux, chap4MixingInequalityTypeOneSumAux, hcoord]
        linarith
      · have hcoord :
            (x + exercise_3_29_ray i.succ) j.succ - (⌊b j⌋ : ℝ) =
              x j.succ - (⌊b j⌋ : ℝ) := by
          simp [Pi.add_apply, exercise_3_29_ray_apply, hji]
        rw [chap4MixingInequalityTypeOneSumAux, chap4MixingInequalityTypeOneSumAux, hcoord]
        linarith

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: adding a successor ray
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
                chap4MixingInequalityTypeOneSum b (first :: tail) x ≤
                  chap4MixingInequalityTypeOneSum b (first :: tail)
                    (x + exercise_3_29_ray i.succ) := by
              simpa [mixingInequalityTypeOneSum] using
                chap4MixingInequalityTypeOneSumAux_le_add_successorRay
                  (b := b) (x := x) (i := i) (prev := 0) (s := first :: tail)
                  (fun k _hk ↦ mixingFractionalPart_nonneg b k) hfracChain
            cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxIneq :
                    mixingFractionalPart b last ≤
                      x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
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
              chap4MixingInequalityTypeOneSum b (first :: tail) x ≤
                chap4MixingInequalityTypeOneSum b (first :: tail)
                  (x + exercise_3_29_ray i.succ) := by
            simpa [mixingInequalityTypeOneSum] using
              chap4MixingInequalityTypeOneSumAux_le_add_successorRay
                (b := b) (x := x) (i := i) (prev := 0) (s := first :: tail)
                (fun k _hk ↦ mixingFractionalPart_nonneg b k) hfracChain
          constructor
          · cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeOne' :
                    mixingFractionalPart b last ≤
                      x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x := by
                  simpa [mixingInequalityTypeOne, hrev] using hxTypeOne
                rw [mixingInequalityTypeOne, hrev, hhead]
                linarith [hxTypeOne', hsum_mono]
          · cases hrev : (first :: tail).reverse with
            | nil =>
                simp at hrev
            | cons last revTail =>
                have hxTypeTwo' :
                    mixingFractionalPart b last ≤
                      x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
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
                          chap4MixingInequalityTypeOneSum b (i :: tail)
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
                          chap4MixingInequalityTypeOneSum b (first :: tail)
                            (x + exercise_3_29_ray i.succ) +
                          (1 - mixingFractionalPart b last) *
                            ((x + exercise_3_29_ray i.succ) first.succ - (⌊b first⌋ : ℝ)) := by
                    rw [hhead, hshift]
                    linarith [hxTypeTwo', hsum_mono]
                  simpa [mixingInequalityTypeTwo, hrev] using hgoal

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every point of the
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
          x 0 + chap4MixingInequalityTypeOneSum b [i] x +
            (1 - mixingFractionalPart b i) * (x i.succ - (⌊b i⌋ : ℝ)) := by
      simpa [mixingInequalityTypeTwo] using hxTypeTwo
    have hsum_single :
        chap4MixingInequalityTypeOneSum b [i] x =
          mixingFractionalPart b i * (x i.succ - (⌊b i⌋ : ℝ)) := by
      simp [mixingInequalityTypeOneSum, chap4MixingInequalityTypeOneSumAux]
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: iterating a unit-step
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: convexity upgrades a
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: a convex set closed under
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the sum of successor-ray
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the successor-ray sum
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: affine combinations
distribute through the shifted type-one sum because the coefficients add to `1`. -/
private lemma chap4MixingInequalityTypeOneSumAux_affineCombination
    (b : Fin n → ℚ) (a c : ℝ) (hac : a + c = 1)
    (x y : Fin (n + 1) → ℝ) :
    ∀ prev : ℝ, ∀ s : List (Fin n),
      chap4MixingInequalityTypeOneSumAux b (a • x + c • y) prev s =
        a * chap4MixingInequalityTypeOneSumAux b x prev s +
          c * chap4MixingInequalityTypeOneSumAux b y prev s
  | prev, s => by
      induction s generalizing prev with
      | nil =>
          -- The empty selected list contributes no shifted sum on either side.
          simp [chap4MixingInequalityTypeOneSumAux]
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
          rw [chap4MixingInequalityTypeOneSumAux, hshift, ih, chap4MixingInequalityTypeOneSumAux,
            chap4MixingInequalityTypeOneSumAux]
          ring

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the full mixing
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
                chap4MixingInequalityTypeOneSum b s (a • x + c • y) =
                  a * chap4MixingInequalityTypeOneSum b s x + c * chap4MixingInequalityTypeOneSum b s y := by
              simpa [mixingInequalityTypeOneSum] using
                chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0 s
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
                  a * (x 0 + chap4MixingInequalityTypeOneSum b s x +
                    (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                  c * (y 0 + chap4MixingInequalityTypeOneSum b s y +
                    (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hxIneq ha)
                (mul_le_mul_of_nonneg_left hyIneq hc)
            have hleft :
                a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
              rw [← add_mul, hac, one_mul]
            have hright :
                a * (x 0 + chap4MixingInequalityTypeOneSum b s x +
                    (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                  c * (y 0 + chap4MixingInequalityTypeOneSum b s y +
                    (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) =
                  a * x 0 + c * y 0 +
                    (a * chap4MixingInequalityTypeOneSum b s x + c * chap4MixingInequalityTypeOneSum b s y) +
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
                    chap4MixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                      a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        c * chap4MixingInequalityTypeOneSum b (first :: tail) y := by
                  simpa [mixingInequalityTypeOneSum] using
                    chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                      (first :: tail)
                have hhead : (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                  simp [Pi.smul_apply, Pi.add_apply]
                rw [hsum, hhead]
                have hweighted :
                    a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                      a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x) +
                        c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hxTypeOne ha)
                    (mul_le_mul_of_nonneg_left hyTypeOne hc)
                have hleft :
                    a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                      mixingFractionalPart b last := by
                  rw [← add_mul, hac, one_mul]
                have hright :
                    a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x) +
                      c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y) =
                      a * x 0 + c * y 0 +
                        (a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                          c * chap4MixingInequalityTypeOneSum b (first :: tail) y) := by
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
                      x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hxTypeTwo
                have hyTypeTwo' :
                    mixingFractionalPart b last ≤
                      y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y +
                        (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ)) := by
                  simpa [mixingInequalityTypeTwo, hrev] using hyTypeTwo
                have hsum :
                    chap4MixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                      a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        c * chap4MixingInequalityTypeOneSum b (first :: tail) y := by
                  simpa [mixingInequalityTypeOneSum] using
                    chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
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
                        chap4MixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) +
                        (1 - mixingFractionalPart b last) *
                          ((a • x + c • y) first.succ - (⌊b first⌋ : ℝ)) := by
                  rw [hsum, hhead, hshift]
                  have hweighted :
                      a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                        a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                          (1 - mixingFractionalPart b last) *
                            (x first.succ - (⌊b first⌋ : ℝ))) +
                        c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y +
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
                      a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                          (1 - mixingFractionalPart b last) *
                            (x first.succ - (⌊b first⌋ : ℝ))) +
                        c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y +
                          (1 - mixingFractionalPart b last) *
                            (y first.succ - (⌊b first⌋ : ℝ))) =
                        a * x 0 + c * y 0 +
                          (a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                            c * chap4MixingInequalityTypeOneSum b (first :: tail) y) +
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
              chap4MixingInequalityTypeOneSum b s (a • x + c • y) =
                a * chap4MixingInequalityTypeOneSum b s x + c * chap4MixingInequalityTypeOneSum b s y := by
            simpa [mixingInequalityTypeOneSum] using
              chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0 s
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
                a * (x 0 + chap4MixingInequalityTypeOneSum b s x +
                  (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                c * (y 0 + chap4MixingInequalityTypeOneSum b s y +
                  (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hxIneq ha)
              (mul_le_mul_of_nonneg_left hyIneq hc)
          have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
              mixingFractionalPart b last := by
            rw [← add_mul, hac, one_mul]
          have hright :
              a * (x 0 + chap4MixingInequalityTypeOneSum b s x +
                  (1 - mixingFractionalPart b last) * (x i.succ - (⌊b i⌋ : ℝ))) +
                c * (y 0 + chap4MixingInequalityTypeOneSum b s y +
                  (1 - mixingFractionalPart b last) * (y i.succ - (⌊b i⌋ : ℝ))) =
                a * x 0 + c * y 0 +
                  (a * chap4MixingInequalityTypeOneSum b s x + c * chap4MixingInequalityTypeOneSum b s y) +
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
                  chap4MixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                    a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                      c * chap4MixingInequalityTypeOneSum b (first :: tail) y := by
                simpa [mixingInequalityTypeOneSum] using
                  chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
                    (first :: tail)
              have hhead :
                  (a • x + c • y) 0 = a * x 0 + c * y 0 := by
                simp [Pi.smul_apply, Pi.add_apply]
              rw [hsum, hhead]
              have hweighted :
                  a * mixingFractionalPart b last + c * mixingFractionalPart b last ≤
                    a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x) +
                      c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hxTypeOne ha)
                  (mul_le_mul_of_nonneg_left hyTypeOne hc)
              have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
                rw [← add_mul, hac, one_mul]
              have hright :
                  a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x) +
                    c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y) =
                    a * x 0 + c * y 0 +
                      (a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        c * chap4MixingInequalityTypeOneSum b (first :: tail) y) := by
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
                  chap4MixingInequalityTypeOneSum b (first :: tail) (a • x + c • y) =
                    a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                      c * chap4MixingInequalityTypeOneSum b (first :: tail) y := by
                simpa [mixingInequalityTypeOneSum] using
                  chap4MixingInequalityTypeOneSumAux_affineCombination b a c hac x y 0
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
                    a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                      (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))) +
                    c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y +
                      (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ))) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hxTypeTwo ha)
                  (mul_le_mul_of_nonneg_left hyTypeTwo hc)
              have hleft : a * mixingFractionalPart b last + c * mixingFractionalPart b last =
                  mixingFractionalPart b last := by
                rw [← add_mul, hac, one_mul]
              have hright :
                  a * (x 0 + chap4MixingInequalityTypeOneSum b (first :: tail) x +
                      (1 - mixingFractionalPart b last) * (x first.succ - (⌊b first⌋ : ℝ))) +
                    c * (y 0 + chap4MixingInequalityTypeOneSum b (first :: tail) y +
                      (1 - mixingFractionalPart b last) * (y first.succ - (⌊b first⌋ : ℝ))) =
                    a * x 0 + c * y 0 +
                      (a * chap4MixingInequalityTypeOneSum b (first :: tail) x +
                        c * chap4MixingInequalityTypeOneSum b (first :: tail) y) +
                      ((1 - mixingFractionalPart b last) *
                        (a * (x first.succ - (⌊b first⌋ : ℝ)) +
                          c * (y first.succ - (⌊b first⌋ : ℝ)))) := by
                ring
              rw [hleft, hright] at hweighted
              simpa [mul_add, add_assoc, add_left_comm, add_comm, left_distrib, right_distrib]
                using hweighted
-/

/-- Helper for remote integer-programming sorry cleanup
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: every mixed-integer
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
`remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: the full mixing hull
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


/-- Helper for Exercise 7.21: the zero-level slice witness is tight for the source mixing
inequality `(4.29)`. -/
lemma mixingInequalityTypeOne_on_sliceWitness_zero
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingInequalityTypeOne b s (mixingSliceWitness b 0) := by
  have hwitness :
      mixingSliceWitness b 0 ∈ mixingInequalitiesRegion b :=
    mixingSliceWitness_mem_mixingInequalitiesRegion b (show 0 ≤ (0 : ℝ) by simp)
      (show (0 : ℝ) < 1 by norm_num)
  exact (hwitness.2.2 s hs).1

/-- Helper for Exercise 7.21: the slice witness at the first selected fractional part is tight for
the source mixing inequality `(4.30)`. -/
lemma mixingInequalityTypeTwo_on_firstSliceWitness
    (b : Fin n → ℚ) (first : Fin n) (tail : List (Fin n))
    (hs : IsMixingIndexSequence b (first :: tail)) :
    mixingInequalityTypeTwo b (first :: tail)
      (mixingSliceWitness b (mixingFractionalPart b first)) := by
  have hfrac_nonneg : 0 ≤ mixingFractionalPart b first :=
    mixingFractionalPart_nonneg b first
  have hfrac_lt_one : mixingFractionalPart b first < 1 := by
    rw [mixingFractionalPart_eq_fract]
    exact Int.fract_lt_one (((b first : ℚ) : ℝ))
  have hwitness :
      mixingSliceWitness b (mixingFractionalPart b first) ∈ mixingInequalitiesRegion b :=
    mixingSliceWitness_mem_mixingInequalitiesRegion b hfrac_nonneg hfrac_lt_one
  exact (hwitness.2.2 (first :: tail) hs).2

/-- Helper for Exercise 7.21: the coefficient form of mixing inequality `(4.29)` is valid on
`mixingHull b` because the hull lies in the local mixing-inequalities region. -/
lemma mixingInequalityTypeOneCoeff_valid_on_mixingHull
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    is_valid_inequality
      (mixingHull b)
      (mixingInequalityTypeOneCoeff b s)
      (mixingInequalityTypeOneRhs b s) := by
  intro x hx
  have hxRegion : x ∈ mixingInequalitiesRegion b :=
    mixingHull_subset_mixingInequalitiesRegion b hx
  exact (mixingInequalityTypeOneCoeff_iff b s hs x).2 ((hxRegion.2.2 s hs).1)

/-- Helper for Exercise 7.21: the coefficient form of mixing inequality `(4.30)` is valid on
`mixingHull b` by the same local region description. -/
lemma mixingInequalityTypeTwoCoeff_valid_on_mixingHull
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    is_valid_inequality
      (mixingHull b)
      (mixingInequalityTypeTwoCoeff b s)
      (mixingInequalityTypeTwoRhs b s) := by
  intro x hx
  have hxRegion : x ∈ mixingInequalitiesRegion b :=
    mixingHull_subset_mixingInequalitiesRegion b hx
  exact (mixingInequalityTypeTwoCoeff_iff b s hs x).2 ((hxRegion.2.2 s hs).2)

/-- Exercise 7.21 (1). For every admissible index sequence
`1 ≤ i₁ < ⋯ < i_m ≤ n` with `0 < f_{i₁} < ⋯ < f_{i_m}`, the mixing inequality `(4.29)`
defines a facet of `P^mix`. -/
theorem exercise_7_21_mixing_inequality_4_29_facet_defining
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    facet_defining_inequality
      (mixingHull b)
      (mixingInequalityTypeOneCoeff b s)
      (mixingInequalityTypeOneRhs b s) := by
  let P := mixingHull b
  let F :=
    face_set P (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s)
  have hvalid :
      is_valid_inequality P (mixingInequalityTypeOneCoeff b s) (mixingInequalityTypeOneRhs b s) := by
    simpa [P] using mixingInequalityTypeOneCoeff_valid_on_mixingHull b s hs
  have hproper : is_proper_face P F := by
    rw [is_proper_face_iff]
    refine ⟨?_, ?_, ?_⟩
    · -- The equality set of a valid mixing inequality is exposed.
      simpa [P, F] using isExposed_face_set_of_valid_inequality hvalid
    · -- The zero slice witness is a tight point of the type-one face.
      exact ⟨mixingSliceWitness b 0, by
        simpa [P, F] using mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face b s hs⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        exact (mem_face_set_iff.mp (by simpa [F] using hx)).1
      · intro hFP
        have houtsideHull :
            mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1)) ∈ P := by
          have hzeroHull : mixingSliceWitness b 0 ∈ P := by
            exact (mem_face_set_iff.mp
              (mixingSliceWitness_zero_mem_mixingInequalityTypeOne_face b s hs)).1
          exact mixingHull_add_headRay_mem b hzeroHull
        have houtsideFace :
            mixingSliceWitness b 0 + exercise_3_29_ray (0 : Fin (n + 1)) ∈ F :=
          hFP houtsideHull
        exact
          mixingSliceWitness_zero_add_headRay_not_mem_mixingInequalityTypeOne_face b s hs
            houtsideFace
  rw [facet_defining_inequality_iff, is_facet_iff]
  refine ⟨hvalid, hproper, ?_⟩
  intro G hG hsubset
  -- Route correction: the facet assembly is complete; the remaining work is isolated in the
  -- maximal-face lemma for containing proper faces.
  simpa [P, F] using mixingInequalityTypeOne_face_eq_of_subset_proper_face b s hs hG hsubset

/-- Helper for Exercise 7.21: the zero-level slice witness satisfies the type-two inequality
strictly, so it does not lie on the equality face of `(4.30)`. -/
lemma mixingSliceWitness_zero_not_mem_mixingInequalityTypeTwo_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    mixingSliceWitness b 0 ∉
      face_set (mixingHull b) (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          intro hmem
          rcases (mem_mixingInequalityTypeTwo_face_iff_of_reverse b first last tail revTail hrev
            (mixingSliceWitness b 0)).1 hmem with ⟨hwitnessHull, hEq⟩
          have hgt :
              ∀ j ∈ first :: tail, (0 : ℝ) < mixingFractionalPart b j := by
            have hsSeq : IsMixingIndexSequence b (first :: tail) := by
              exact ⟨hfirst_pos, hindexChain, hfracChain⟩
            intro j hj
            exact mixingFractionalPart_pos_of_mem_isMixingIndexSequence b hsSeq hj
          have hsum :
              chap4MixingInequalityTypeOneSum b (first :: tail) (mixingSliceWitness b 0) =
                mixingFractionalPart b last := by
            simpa [chap4MixingInequalityTypeOneSum, hrev] using
              mixingInequalityTypeOneSumAux_eq_last_sub_prev_of_all_gt b
                (show 0 ≤ (0 : ℝ) by simp) (show (0 : ℝ) < 1 by norm_num)
                (prev := 0) (s := first :: tail) hgt hfracChain
          have hfirst_shift :
              mixingSliceWitness b 0 first.succ - (⌊b first⌋ : ℝ) = 1 :=
            mixingSliceWitness_shiftProfile_of_lt b (show 0 ≤ (0 : ℝ) by simp)
              (show (0 : ℝ) < 1 by norm_num) hfirst_pos
          have hlast_lt_one : mixingFractionalPart b last < 1 := by
            rw [mixingFractionalPart_eq_fract]
            exact Int.fract_lt_one (((b last : ℚ) : ℝ))
          have hceil_gap :
              (⌈b first⌉ : ℝ) - (⌊b first⌋ : ℝ) = 1 := by
            rw [ceil_eq_floor_add_one_of_mixingFractionalPart_pos b hfirst_pos]
            ring
          simp [mixingSliceWitness, hsum] at hEq
          cases hEq with
          | inl hgap =>
              have hlast_eq_one : mixingFractionalPart b last = 1 := by
                rw [mixingFractionalPart_eq_fract]
                nlinarith [hgap]
              linarith
          | inr hfloor =>
              linarith

/-- Helper for `remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_21.lean`: any exposed face
containing the equality set of `(4.30)` has exposing functional proportional to the type-two
coefficient vector. -/
private lemma typeTwoContainingFaceFunctional_eq_smulCoeff
    (b : Fin n → ℚ) (first last : Fin n) (tail revTail : List (Fin n))
    (hsSeq : IsMixingIndexSequence b (first :: tail))
    (hrev : (first :: tail).reverse = last :: revTail)
    {d : Fin (n + 1) → ℝ} {β : ℝ}
    (hsubsetFace :
      face_set
          (mixingHull b)
          (mixingInequalityTypeTwoCoeff b (first :: tail))
          (mixingInequalityTypeTwoRhs b (first :: tail)) ⊆
        face_set (mixingHull b) d β) :
    d = (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail) := by
  rcases hsSeq with ⟨hfirst_pos, hindexChain, hfracChain⟩
  have hxFirstFace :
      mixingSliceWitness b (mixingFractionalPart b first) ∈
        face_set
          (mixingHull b)
          (mixingInequalityTypeTwoCoeff b (first :: tail))
          (mixingInequalityTypeTwoRhs b (first :: tail)) := by
    -- The first selected breakpoint witness is the natural anchor point for type two.
    simpa using
      mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem b (first :: tail) hsSeq (by simp)
  have hxFirstG :
      mixingSliceWitness b (mixingFractionalPart b first) ∈ face_set (mixingHull b) d β :=
    hsubsetFace hxFirstFace
  have hoff : ∀ i : Fin n, i ∉ first :: tail → d i.succ = 0 := by
    intro i hi
    have hxRayFace :
        mixingSliceWitness b (mixingFractionalPart b first) + exercise_3_29_ray i.succ ∈
          face_set
            (mixingHull b)
            (mixingInequalityTypeTwoCoeff b (first :: tail))
            (mixingInequalityTypeTwoRhs b (first :: tail)) := by
      -- Nonselected successor rays preserve the type-two equality face.
      simpa using
        mixingInequalityTypeTwoFace_add_nonselected_successorRay_mem b (first :: tail) hsSeq
          hxFirstFace hi
    have hxRayG :
        mixingSliceWitness b (mixingFractionalPart b first) + exercise_3_29_ray i.succ ∈
          face_set (mixingHull b) d β := hsubsetFace hxRayFace
    have hdot_zero : d ⬝ᵥ exercise_3_29_ray i.succ = 0 := by
      -- Subtract the two points of the exposed face to isolate the ray direction.
      simpa [sub_eq_add_neg, Pi.add_apply] using faceSet_dot_sub_eq_zero_of_two_mem hxRayG hxFirstG
    simpa [dotProduct_exercise_3_29_ray_succ] using hdot_zero
  have hheadRayG :
      mixingSliceWitness b (mixingFractionalPart b first) + exercise_3_29_ray (0 : Fin (n + 1)) ∈
        face_set (mixingHull b) d β := by
    have hxHeadFace :
        mixingSliceWitness b (mixingFractionalPart b first) +
            exercise_3_29_ray (0 : Fin (n + 1)) ∈
          face_set
            (mixingHull b)
            (mixingInequalityTypeTwoCoeff b (first :: tail))
            (mixingInequalityTypeTwoRhs b (first :: tail)) := by
      -- The head ray is the extra face-stability direction for the type-two inequality.
      simpa using mixingInequalityTypeTwoFace_add_headRay_mem b (first :: tail) hsSeq hxFirstFace
    exact hsubsetFace hxHeadFace
  have hd_ray_zero : d ⬝ᵥ exercise_3_29_ray (0 : Fin (n + 1)) = 0 := by
    -- The containing exposed face has zero variation along the head ray as well.
    simpa [sub_eq_add_neg, Pi.add_apply] using faceSet_dot_sub_eq_zero_of_two_mem hheadRayG hxFirstG
  have hc_ray_zero :
      mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ exercise_3_29_ray (0 : Fin (n + 1)) = 0 := by
    have hxHeadFace :
        mixingSliceWitness b (mixingFractionalPart b first) +
            exercise_3_29_ray (0 : Fin (n + 1)) ∈
          face_set
            (mixingHull b)
            (mixingInequalityTypeTwoCoeff b (first :: tail))
            (mixingInequalityTypeTwoRhs b (first :: tail)) := by
      simpa using mixingInequalityTypeTwoFace_add_headRay_mem b (first :: tail) hsSeq hxFirstFace
    -- The target face itself has the same head-ray invariance.
    simpa [sub_eq_add_neg, Pi.add_apply] using faceSet_dot_sub_eq_zero_of_two_mem hxHeadFace hxFirstFace
  have hsucc_eq_of_ne_first :
      ∀ {i : Fin n},
        i ≠ first →
          d i.succ = ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) i.succ := by
    intro i hiFirst
    by_cases hiTail : i ∈ tail
    · rcases exists_adjacent_split_of_mem_tail (first := first) (curr := i) hiTail with
          ⟨pre, prev, suffix, hsplit⟩
      have hsAdj : IsMixingIndexSequence b (pre ++ prev :: i :: suffix) := by
        simpa [hsplit] using hsSeq
      have hxPrevFace :
          mixingSliceWitness b (mixingFractionalPart b prev) ∈
            face_set
              (mixingHull b)
              (mixingInequalityTypeTwoCoeff b (first :: tail))
              (mixingInequalityTypeTwoRhs b (first :: tail)) := by
        -- Selected breakpoint witnesses remain on the type-two face.
        simpa [hsplit] using
          mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem b (first :: tail) hsSeq
            (by simp [hsplit])
      have hxCurrFace :
          mixingSliceWitness b (mixingFractionalPart b i) ∈
            face_set
              (mixingHull b)
              (mixingInequalityTypeTwoCoeff b (first :: tail))
              (mixingInequalityTypeTwoRhs b (first :: tail)) := by
        simpa using
          mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem b (first :: tail) hsSeq
            (by simp)
      have hxPrevG :
          mixingSliceWitness b (mixingFractionalPart b prev) ∈ face_set (mixingHull b) d β :=
        hsubsetFace hxPrevFace
      have hxCurrG :
          mixingSliceWitness b (mixingFractionalPart b i) ∈ face_set (mixingHull b) d β :=
        hsubsetFace hxCurrFace
      have hadj_step :
          (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 - d i.succ = 0 := by
        -- Adjacent selected witnesses again isolate the later successor coordinate.
        calc
          (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 - d i.succ =
              d ⬝ᵥ
                (mixingSliceWitness b (mixingFractionalPart b i) -
                  mixingSliceWitness b (mixingFractionalPart b prev)) := by
                  symm
                  simpa [hsplit] using
                    mixingSliceWitnessAdjacentSelectedStep_dot_eq_of_offSupportZero b pre prev i
                      suffix hsAdj hoff
          _ = 0 := by
            simpa using faceSet_dot_sub_eq_zero_of_two_mem hxCurrG hxPrevG
      have hdCurr : d i.succ = (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 := by
        linarith
      have hcoeffCurr :
          mixingInequalityTypeTwoCoeff b (first :: tail) i.succ =
            -(mixingFractionalPart b i - mixingFractionalPart b prev) := by
        calc
          mixingInequalityTypeTwoCoeff b (first :: tail) i.succ =
              mixingInequalityTypeOneCoeff b (first :: tail) i.succ := by
                exact
                  mixingInequalityTypeTwoCoeff_apply_succ_of_mem_tail b first last tail revTail
                    hrev hindexChain hiTail
          _ = -(mixingFractionalPart b i - mixingFractionalPart b prev) := by
            calc
              mixingInequalityTypeOneCoeff b (first :: tail) i.succ =
                  chap4MixingInequalityTypeOneCoeffAux b 0 (first :: tail) i.succ := by
                    exact mixingInequalityTypeOneCoeff_apply_succ b (first :: tail) i
              _ = -(mixingFractionalPart b i - mixingFractionalPart b prev) := by
                have hindexAdj : (pre ++ prev :: i :: suffix).IsChain (· < ·) := by
                  simpa [hsplit] using hindexChain
                simpa [hsplit] using
                  chap4MixingInequalityTypeOneCoeffAux_apply_succ_of_adjacent b 0 pre prev i suffix
                    hindexAdj
      calc
        d i.succ = (mixingFractionalPart b i - mixingFractionalPart b prev) * d 0 := hdCurr
        _ = (-d 0) * (-(mixingFractionalPart b i - mixingFractionalPart b prev)) := by ring
        _ = ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) i.succ := by
          simp [hcoeffCurr, smul_eq_mul]
    · have his : i ∉ first :: tail := by
        intro his'
        rcases List.mem_cons.mp his' with hEq | hmem
        · exact hiFirst hEq
        · exact hiTail hmem
      have hdOff : d i.succ = 0 := hoff i his
      have hcoeffOff : mixingInequalityTypeTwoCoeff b (first :: tail) i.succ = 0 := by
        have htypeOneOff :
            mixingInequalityTypeOneCoeff b (first :: tail) i.succ = 0 := by
          rw [mixingInequalityTypeOneCoeff_apply_succ]
          exact chap4MixingInequalityTypeOneCoeffAux_eq_zero_of_not_mem b his
        simp [mixingInequalityTypeTwoCoeff, hrev, hiFirst, htypeOneOff]
      simp [hdOff, hcoeffOff, smul_eq_mul]
  funext j
  refine Fin.cases ?_ ?_ j
  · symm
    calc
      ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) 0 = (-d 0) * (-1 : ℝ) := by
        simp [mixingInequalityTypeTwoCoeff, hrev, mixingInequalityTypeOneCoeff, smul_eq_mul]
      _ = d 0 := by ring
  · intro i
    by_cases hiFirst : i = first
    · subst hiFirst
      have hscaled_ray_zero :
          ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) ⬝ᵥ
              exercise_3_29_ray (0 : Fin (n + 1)) = 0 := by
        -- Scaling preserves the head-ray vanishing of the target coefficient vector.
        calc
          ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) ⬝ᵥ
              exercise_3_29_ray (0 : Fin (n + 1)) =
              (-d 0) *
                (mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ
                  exercise_3_29_ray (0 : Fin (n + 1))) := by
                    simpa [smul_eq_mul] using
                      (smul_dotProduct (-d 0)
                        (mixingInequalityTypeTwoCoeff b (first :: tail))
                        (exercise_3_29_ray (0 : Fin (n + 1))))
          _ = 0 := by rw [hc_ray_zero, mul_zero]
      have hsum_rest :
          ∑ k : Fin n,
              (d - (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) k.succ =
            (d - (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) first.succ := by
        rw [Fintype.sum_eq_single first]
        · rfl
        · intro k hk
          have hk_eq :
              d k.succ = ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) k.succ :=
            hsucc_eq_of_ne_first hk
          simpa [hk_eq]
      have hfirst_zero :
          (d - (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) first.succ = 0 := by
        have hdiff_ray_zero :
            (d - (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) ⬝ᵥ
                exercise_3_29_ray (0 : Fin (n + 1)) = 0 := by
          rw [sub_dotProduct, hd_ray_zero, hscaled_ray_zero]
          ring
        have hhead_zero :
            (d - (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) 0 = 0 := by
          simp [mixingInequalityTypeTwoCoeff, hrev, mixingInequalityTypeOneCoeff, smul_eq_mul]
        rw [dotProduct_exercise_3_29_ray_zero, hsum_rest, hhead_zero] at hdiff_ray_zero
        linarith
      linarith
    · exact hsucc_eq_of_ne_first hiFirst

/-- Helper for Exercise 7.21: any proper face containing the equality set of mixing inequality
`(4.30)` already equals that face. -/
lemma mixingInequalityTypeTwo_face_eq_of_subset_proper_face
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s)
    {G : Set (Fin (n + 1) → ℝ)}
    (hG : is_proper_face (mixingHull b) G)
    (hsubset :
      face_set
          (mixingHull b)
          (mixingInequalityTypeTwoCoeff b s)
          (mixingInequalityTypeTwoRhs b s) ⊆
        G) :
    G =
      face_set
        (mixingHull b)
        (mixingInequalityTypeTwoCoeff b s)
        (mixingInequalityTypeTwoRhs b s) := by
  cases s with
  | nil =>
      cases hs
  | cons first tail =>
      rcases hs with ⟨hfirst_pos, hindexChain, hfracChain⟩
      have hsSeq : IsMixingIndexSequence b (first :: tail) := by
        exact ⟨hfirst_pos, hindexChain, hfracChain⟩
      cases hrev : (first :: tail).reverse with
      | nil =>
          simp at hrev
      | cons last revTail =>
          rcases is_proper_face_iff.mp hG with ⟨hG_exposed, hG_nonempty, hG_ssubset⟩
          rcases isExposed_iff_eq_empty_or_eq_face_set.mp hG_exposed with hG_empty |
              ⟨d, β, _, hG_eq⟩
          · obtain ⟨x, hx⟩ := hG_nonempty
            simp [hG_empty] at hx
          · have hxFirstFace :
                mixingSliceWitness b (mixingFractionalPart b first) ∈
                  face_set
                    (mixingHull b)
                    (mixingInequalityTypeTwoCoeff b (first :: tail))
                    (mixingInequalityTypeTwoRhs b (first :: tail)) := by
              -- The first selected breakpoint witness is the natural anchor point for type two.
              simpa using
                mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem b (first :: tail)
                  hsSeq (by simp)
            have hxFirstG :
                mixingSliceWitness b (mixingFractionalPart b first) ∈
                  face_set (mixingHull b) d β := by
              -- Push the anchor point through the containing-face hypothesis.
              simpa [hG_eq] using hsubset hxFirstFace
            have hsubsetFace :
                face_set
                    (mixingHull b)
                    (mixingInequalityTypeTwoCoeff b (first :: tail))
                    (mixingInequalityTypeTwoRhs b (first :: tail)) ⊆
                  face_set (mixingHull b) d β := by
              intro x hx
              simpa [hG_eq] using hsubset hx
            have hd_eq :
                d = (-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail) := by
              exact
                typeTwoContainingFaceFunctional_eq_smulCoeff b first last tail revTail hsSeq hrev
                  hsubsetFace
            have hlam_ne : -d 0 ≠ 0 := by
              intro hlam_zero
              have hd_zero : d = 0 := by
                simpa [hlam_zero] using hd_eq
              obtain ⟨x, hxGmem⟩ := hG_nonempty
              have hβ_zero : β = 0 := by
                -- Any point on the face forces the rhs to vanish once the exposing vector is zero.
                simpa [hd_zero] using ((mem_face_set_iff.mp (by simpa [hG_eq] using hxGmem)).2).symm
              have hG_all :
                  G = mixingHull b := by
                -- The zero functional cuts out the whole polyhedron.
                rw [hG_eq]
                ext x
                rw [mem_face_set_iff]
                simp [hd_zero, hβ_zero]
              exact hG_ssubset.ne hG_all
            have hβ_eq :
                β =
                  (-d 0) * mixingInequalityTypeTwoRhs b (first :: tail) := by
              -- Evaluate the normalized exposing functional at the type-two anchor point.
              calc
                β = d ⬝ᵥ mixingSliceWitness b (mixingFractionalPart b first) :=
                    ((mem_face_set_iff.mp hxFirstG).2).symm
                _ =
                    ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail)) ⬝ᵥ
                      mixingSliceWitness b (mixingFractionalPart b first) := by
                        rw [hd_eq]
                _ =
                    (-d 0) *
                      (mixingInequalityTypeTwoCoeff b (first :: tail) ⬝ᵥ
                        mixingSliceWitness b (mixingFractionalPart b first)) := by
                          simpa [smul_eq_mul] using
                            (smul_dotProduct (-d 0)
                              (mixingInequalityTypeTwoCoeff b (first :: tail))
                              (mixingSliceWitness b (mixingFractionalPart b first)))
                _ = (-d 0) * mixingInequalityTypeTwoRhs b (first :: tail) := by
                      rw [(mem_face_set_iff.mp hxFirstFace).2]
            -- Repackage `G` as the same nonzero scaling of the target face.
            calc
              G = face_set (mixingHull b) d β := hG_eq
              _ =
                  face_set
                    (mixingHull b)
                    ((-d 0) • mixingInequalityTypeTwoCoeff b (first :: tail))
                    ((-d 0) * mixingInequalityTypeTwoRhs b (first :: tail)) := by
                      rw [hd_eq, hβ_eq]
              _ =
                  face_set
                    (mixingHull b)
                    (mixingInequalityTypeTwoCoeff b (first :: tail))
                    (mixingInequalityTypeTwoRhs b (first :: tail)) :=
                      faceSet_eq_of_nonzero_smul hlam_ne

/-- Exercise 7.21 (2). For every admissible index sequence
`1 ≤ i₁ < ⋯ < i_m ≤ n` with `0 < f_{i₁} < ⋯ < f_{i_m}`, the mixing inequality `(4.30)`
defines a facet of `P^mix`. -/
theorem exercise_7_21_mixing_inequality_4_30_facet_defining
    (b : Fin n → ℚ) (s : List (Fin n)) (hs : IsMixingIndexSequence b s) :
    facet_defining_inequality
      (mixingHull b)
      (mixingInequalityTypeTwoCoeff b s)
      (mixingInequalityTypeTwoRhs b s) := by
  let P := mixingHull b
  let F :=
    face_set P (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s)
  have hvalid :
      is_valid_inequality P (mixingInequalityTypeTwoCoeff b s) (mixingInequalityTypeTwoRhs b s) := by
    simpa [P] using mixingInequalityTypeTwoCoeff_valid_on_mixingHull b s hs
  have hproper : is_proper_face P F := by
    rw [is_proper_face_iff]
    refine ⟨?_, ?_, ?_⟩
    · -- The equality set of a valid mixing inequality is exposed.
      simpa [P, F] using isExposed_face_set_of_valid_inequality hvalid
    · -- The first selected slice witness is tight for the type-two inequality.
      cases s with
      | nil =>
          cases hs
      | cons first tail =>
          exact ⟨mixingSliceWitness b (mixingFractionalPart b first), by
            simpa [P, F] using
              mixingSliceWitness_mem_mixingInequalityTypeTwo_face_of_mem b (first :: tail) hs
                (by simp)⟩
    · refine ⟨?_, ?_⟩
      · intro x hx
        exact (mem_face_set_iff.mp (by simpa [F] using hx)).1
      · intro hFP
        have hzeroHull : mixingSliceWitness b 0 ∈ P := by
          exact mixingSliceWitness_mem_mixingHull b (show 0 ≤ (0 : ℝ) by simp)
            (show (0 : ℝ) < 1 by norm_num)
        have hzeroFace : mixingSliceWitness b 0 ∈ F := hFP hzeroHull
        exact mixingSliceWitness_zero_not_mem_mixingInequalityTypeTwo_face b s hs hzeroFace
  rw [facet_defining_inequality_iff, is_facet_iff]
  refine ⟨hvalid, hproper, ?_⟩
  intro G hG hsubset
  -- Route correction: the facet assembly is complete; the remaining work is isolated in the
  -- maximal-face lemma for containing proper faces.
  simpa [P, F] using mixingInequalityTypeTwo_face_eq_of_subset_proper_face b s hs hG hsubset

end Exercise721
