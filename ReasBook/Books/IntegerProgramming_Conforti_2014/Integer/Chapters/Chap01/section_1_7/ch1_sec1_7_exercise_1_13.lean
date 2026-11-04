/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Semantic recall note: no `lean_leansearch` tool was available in this session.
-- Declarations for this item will be appended below by the statement pipeline.

/-- The first integer set from Exercise 1.13, viewed inside `ℝ × ℝ`. -/
def exercise_1_13_first_set : Set (ℝ × ℝ) :=
  { p | ∃ m n : ℤ,
      0 ≤ m ∧
      0 ≤ n ∧
      m + n ≤ 2 ∧
      m - n ≤ 1 ∧
      n - m ≤ 1 ∧
      p = ((m : ℝ), (n : ℝ)) }

/-- The second mixed-integer set from Exercise 1.13, viewed inside `ℝ × ℝ`. -/
def exercise_1_13_second_set : Set (ℝ × ℝ) :=
  { p | ∃ m : ℤ,
      0 ≤ m ∧
      (m : ℝ) + p.2 ≥ (8 : ℝ) / 5 ∧
      m ≤ 2 ∧
      0 ≤ p.2 ∧
      p.1 = m ∧
      p.2 ≤ 2 }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: the first
integer set consists of the four vertices of the unit square. -/
private lemma mem_exercise_1_13_first_set_iff (p : ℝ × ℝ) :
    p ∈ exercise_1_13_first_set ↔
      p = (0, 0) ∨ p = (1, 0) ∨ p = (0, 1) ∨ p = (1, 1) := by
  constructor
  · -- The integer inequalities force both coordinates to be zero or one.
    rintro ⟨m, n, hm, hn, hsum, hmn, hnm, rfl⟩
    have hm_upper : m ≤ 1 := by
      omega
    have hn_upper : n ≤ 1 := by
      omega
    interval_cases m
    · interval_cases n
      all_goals norm_num
    · interval_cases n
      all_goals norm_num
  · -- Each of the four vertices has the required integer witnesses.
    rintro (rfl | rfl | rfl | rfl)
    · refine ⟨0, 0, ?_⟩
      norm_num
    · refine ⟨1, 0, ?_⟩
      norm_num
    · refine ⟨0, 1, ?_⟩
      norm_num
    · refine ⟨1, 1, ?_⟩
      norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: the second
mixed-integer set is the union of three explicitly bounded vertical segments. -/
private lemma mem_exercise_1_13_second_set_iff (p : ℝ × ℝ) :
    p ∈ exercise_1_13_second_set ↔
      (p.1 = 0 ∧ (8 : ℝ) / 5 ≤ p.2 ∧ p.2 ≤ 2) ∨
      (p.1 = 1 ∧ (3 : ℝ) / 5 ≤ p.2 ∧ p.2 ≤ 2) ∨
      (p.1 = 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2) := by
  constructor
  · -- Enumerate the only possible integer first coordinates.
    rintro ⟨m, hm, hlower, hm_upper, hp_nonneg, hp_fst, hp_upper⟩
    have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 := by
      omega
    rcases hm_cases with rfl | rfl | rfl
    · left
      refine ⟨?_, ?_, hp_upper⟩
      · simpa using hp_fst
      · norm_num at hlower ⊢
        linarith
    · right
      left
      refine ⟨?_, ?_, hp_upper⟩
      · simpa using hp_fst
      · norm_num at hlower ⊢
        linarith
    · right
      right
      refine ⟨?_, hp_nonneg, hp_upper⟩
      simpa using hp_fst
  · -- Conversely, each vertical slice supplies its displayed integer witness.
    rintro (hzero | hone | htwo)
    · rcases hzero with ⟨hp_fst, hp_lower, hp_upper⟩
      refine ⟨0, ?_, ?_, ?_, ?_, ?_, hp_upper⟩
      · norm_num
      · norm_num at hp_lower ⊢
        linarith
      · norm_num
      · linarith
      · simpa using hp_fst
    · rcases hone with ⟨hp_fst, hp_lower, hp_upper⟩
      refine ⟨1, ?_, ?_, ?_, ?_, ?_, hp_upper⟩
      · norm_num
      · norm_num at hp_lower ⊢
        linarith
      · norm_num
      · linarith
      · simpa using hp_fst
    · rcases htwo with ⟨hp_fst, hp_nonneg, hp_upper⟩
      refine ⟨2, ?_, ?_, ?_, hp_nonneg, ?_, hp_upper⟩
      · norm_num
      · linarith
      · norm_num
      · simpa using hp_fst

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: a nonnegative
three-point affine combination of points of a set lies in its convex hull. -/
private lemma threePointCombination_mem_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {u v w p : E} {a b c : ℝ}
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) (hcomb : a • u + b • v + c • w = p) :
    p ∈ convexHull ℝ s := by
  -- Package the three weights as a finite convex combination.
  refine mem_convexHull_of_exists_fintype (ι := Fin 3) ![a, b, c] ![u, v, w] ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · simpa [Fin.sum_univ_three] using hsum
  · intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  · simpa [Fin.sum_univ_three] using hcomb

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean.
Exercise 1.13 (1): the convex hull of the first listed integer set is the unit square. -/
theorem exercise_1_13_first_convex_hull :
    convexHull ℝ exercise_1_13_first_set =
      { p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 } := by
  -- The target square is a coordinatewise closed interval, hence convex.
  have target_convex :
      Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} := by
    simpa [Set.Icc, Prod.le_def, and_assoc, and_left_comm, and_comm] using
      (convex_Icc ((0, 0) : ℝ × ℝ) ((1, 1) : ℝ × ℝ))
  apply Set.Subset.antisymm
  · -- Minimality of the convex hull gives containment in the square.
    refine convexHull_min ?_ target_convex
    intro p hp
    rw [mem_exercise_1_13_first_set_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals norm_num
  · -- Triangulate the square along the diagonal `p.1 + p.2 = 1`.
    intro p hp
    have h00 : (0, 0) ∈ exercise_1_13_first_set := by
      rw [mem_exercise_1_13_first_set_iff]
      left
      rfl
    have h10 : (1, 0) ∈ exercise_1_13_first_set := by
      rw [mem_exercise_1_13_first_set_iff]
      right
      left
      rfl
    have h01 : (0, 1) ∈ exercise_1_13_first_set := by
      rw [mem_exercise_1_13_first_set_iff]
      right
      right
      left
      rfl
    have h11 : (1, 1) ∈ exercise_1_13_first_set := by
      rw [mem_exercise_1_13_first_set_iff]
      right
      right
      right
      rfl
    by_cases hlower : p.1 + p.2 ≤ 1
    · refine threePointCombination_mem_convexHull (a := 1 - p.1 - p.2)
        (b := p.1) (c := p.2) h00 h10 h01 ?_ hp.1 hp.2.2.1 ?_ ?_
      · linarith [hp.1, hp.2.2.1]
      · ring
      · ext
        · dsimp
          ring
        · dsimp
          ring
    · refine threePointCombination_mem_convexHull (a := p.1 + p.2 - 1)
        (b := 1 - p.2) (c := 1 - p.1) h11 h10 h01 ?_ ?_ ?_ ?_ ?_
      · linarith
      · linarith [hp.2.2.2]
      · linarith [hp.2.1]
      · ring
      · ext
        · dsimp
          ring
        · dsimp
          ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: the six
facet inequalities of the second polygon define a convex set. -/
private lemma exercise_1_13_second_facets_convex :
    Convex ℝ {p : ℝ × ℝ |
      0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
      p.1 + p.2 ≥ (8 : ℝ) / 5 ∧ 3 * p.1 + 5 * p.2 ≥ (6 : ℝ)} := by
  -- Reduce convexity to preservation of the six scalar inequalities.
  rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy a b ha hb hab
  change 0 ≤ x₁ ∧ x₁ ≤ 2 ∧ 0 ≤ x₂ ∧ x₂ ≤ 2 ∧
    (8 : ℝ) / 5 ≤ x₁ + x₂ ∧ 6 ≤ 3 * x₁ + 5 * x₂ at hx
  change 0 ≤ y₁ ∧ y₁ ≤ 2 ∧ 0 ≤ y₂ ∧ y₂ ≤ 2 ∧
    (8 : ℝ) / 5 ≤ y₁ + y₂ ∧ 6 ≤ 3 * y₁ + 5 * y₂ at hy
  change 0 ≤ a * x₁ + b * y₁ ∧ a * x₁ + b * y₁ ≤ 2 ∧
    0 ≤ a * x₂ + b * y₂ ∧ a * x₂ + b * y₂ ≤ 2 ∧
    (8 : ℝ) / 5 ≤ (a * x₁ + b * y₁) + (a * x₂ + b * y₂) ∧
    6 ≤ 3 * (a * x₁ + b * y₁) + 5 * (a * x₂ + b * y₂)
  have hax₁ : 0 ≤ a * x₁ := mul_nonneg ha hx.1
  have hby₁ : 0 ≤ b * y₁ := mul_nonneg hb hy.1
  have hax₂ : 0 ≤ a * x₂ := mul_nonneg ha hx.2.2.1
  have hby₂ : 0 ≤ b * y₂ := mul_nonneg hb hy.2.2.1
  have hax₁_upper : a * x₁ ≤ a * 2 := mul_le_mul_of_nonneg_left hx.2.1 ha
  have hby₁_upper : b * y₁ ≤ b * 2 := mul_le_mul_of_nonneg_left hy.2.1 hb
  have hax₂_upper : a * x₂ ≤ a * 2 := mul_le_mul_of_nonneg_left hx.2.2.2.1 ha
  have hby₂_upper : b * y₂ ≤ b * 2 := mul_le_mul_of_nonneg_left hy.2.2.2.1 hb
  have hx_sum : a * ((8 : ℝ) / 5) ≤ a * (x₁ + x₂) :=
    mul_le_mul_of_nonneg_left hx.2.2.2.2.1 ha
  have hy_sum : b * ((8 : ℝ) / 5) ≤ b * (y₁ + y₂) :=
    mul_le_mul_of_nonneg_left hy.2.2.2.2.1 hb
  have hx_facet : a * 6 ≤ a * (3 * x₁ + 5 * x₂) :=
    mul_le_mul_of_nonneg_left hx.2.2.2.2.2 ha
  have hy_facet : b * 6 ≤ b * (3 * y₁ + 5 * y₂) :=
    mul_le_mul_of_nonneg_left hy.2.2.2.2.2 hb
  have htwo : a * 2 + b * 2 = 2 := by
    linarith
  constructor
  · exact add_nonneg hax₁ hby₁
  constructor
  · exact (add_le_add hax₁_upper hby₁_upper).trans_eq htwo
  constructor
  · exact add_nonneg hax₂ hby₂
  constructor
  · exact (add_le_add hax₂_upper hby₂_upper).trans_eq htwo
  constructor
  · linarith [add_le_add hx_sum hy_sum]
  · linarith [add_le_add hx_facet hy_facet]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: every point
of the second mixed-integer source satisfies the polygon facets. -/
private lemma exercise_1_13_second_set_subset_facets :
    exercise_1_13_second_set ⊆
      {p : ℝ × ℝ |
        0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
        p.1 + p.2 ≥ (8 : ℝ) / 5 ∧ 3 * p.1 + 5 * p.2 ≥ (6 : ℝ)} := by
  -- Check the facets separately on the three vertical source slices.
  intro p hp
  rw [mem_exercise_1_13_second_set_iff] at hp
  rcases hp with hzero | hone | htwo
  · rcases hzero with ⟨hfst, hlower, hupper⟩
    change 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
      (8 : ℝ) / 5 ≤ p.1 + p.2 ∧ 6 ≤ 3 * p.1 + 5 * p.2
    rw [hfst]
    norm_num at hlower ⊢
    constructor
    · linarith
    constructor
    · exact hupper
    constructor
    · linarith
    · linarith
  · rcases hone with ⟨hfst, hlower, hupper⟩
    change 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
      (8 : ℝ) / 5 ≤ p.1 + p.2 ∧ 6 ≤ 3 * p.1 + 5 * p.2
    rw [hfst]
    norm_num at hlower ⊢
    constructor
    · linarith
    constructor
    · exact hupper
    constructor
    · linarith
    · linarith
  · rcases htwo with ⟨hfst, hlower, hupper⟩
    change 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
      (8 : ℝ) / 5 ≤ p.1 + p.2 ∧ 6 ≤ 3 * p.1 + 5 * p.2
    rw [hfst]
    norm_num at hlower ⊢
    constructor
    · exact hlower
    constructor
    · exact hupper
    constructor
    · linarith
    · exact hlower

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_13.lean`: the facet
polygon is covered by three triangles whose vertices belong to the source. -/
private lemma exercise_1_13_second_facets_subset_convexHull :
    {p : ℝ × ℝ |
        0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 ∧
        p.1 + p.2 ≥ (8 : ℝ) / 5 ∧ 3 * p.1 + 5 * p.2 ≥ (6 : ℝ)} ⊆
      convexHull ℝ exercise_1_13_second_set := by
  intro p hp
  -- The five extreme points lie on the three source slices.
  have hA : ((0, (8 : ℝ) / 5) : ℝ × ℝ) ∈ exercise_1_13_second_set := by
    rw [mem_exercise_1_13_second_set_iff]
    left
    norm_num
  have hB : ((0, 2) : ℝ × ℝ) ∈ exercise_1_13_second_set := by
    rw [mem_exercise_1_13_second_set_iff]
    left
    norm_num
  have hC : ((1, (3 : ℝ) / 5) : ℝ × ℝ) ∈ exercise_1_13_second_set := by
    rw [mem_exercise_1_13_second_set_iff]
    right
    left
    norm_num
  have hE : ((2, 0) : ℝ × ℝ) ∈ exercise_1_13_second_set := by
    rw [mem_exercise_1_13_second_set_iff]
    right
    right
    norm_num
  have hF : ((2, 2) : ℝ × ℝ) ∈ exercise_1_13_second_set := by
    rw [mem_exercise_1_13_second_set_iff]
    right
    right
    norm_num
  -- The two extra diagonals partition the polygon into three triangles.
  by_cases htop : 8 + p.1 ≤ 5 * p.2
  · refine threePointCombination_mem_convexHull
      (a := (10 - 5 * p.2) / 2) (b := (5 * p.2 - p.1 - 8) / 2) (c := p.1 / 2)
      hA hB hF ?_ ?_ ?_ ?_ ?_
    · linarith [hp.2.2.2.1]
    · linarith
    · linarith [hp.1]
    · ring
    · ext
      · dsimp
        ring
      · dsimp
        ring
  · by_cases hmiddle : 8 ≤ 4 * p.1 + 5 * p.2
    · refine threePointCombination_mem_convexHull
        (a := (2 - p.1) / 2) (b := (5 * p.2 + 4 * p.1 - 8) / 10)
        (c := (p.1 - 5 * p.2 + 8) / 10) hA hF hE ?_ ?_ ?_ ?_ ?_
      · linarith [hp.2.1]
      · linarith
      · linarith
      · ring
      · ext
        · dsimp
          ring
        · dsimp
          ring
    · refine threePointCombination_mem_convexHull
        (a := (3 * p.1 + 5 * p.2 - 6) / 2) (b := (5 * p.1 + 5 * p.2 - 8) / 2)
        (c := 8 - 4 * p.1 - 5 * p.2) hA hE hC ?_ ?_ ?_ ?_ ?_
      · linarith [hp.2.2.2.2.2]
      · linarith [hp.2.2.2.2.1]
      · linarith
      · ring
      · ext
        · dsimp
          ring
        · dsimp
          ring

/-- Exercise 1.13 (2): the convex hull of the second listed mixed-integer
set is the polygon cut out by its facet inequalities. -/
theorem exercise_1_13_second_convex_hull :
    convexHull ℝ exercise_1_13_second_set =
      { p |
          0 ≤ p.1 ∧
          p.1 ≤ 2 ∧
          0 ≤ p.2 ∧
          p.2 ≤ 2 ∧
          p.1 + p.2 ≥ (8 : ℝ) / 5 ∧
          3 * p.1 + 5 * p.2 ≥ (6 : ℝ) } := by
  -- Assemble the two containments from convex-hull minimality and triangulation.
  apply Set.Subset.antisymm
  · exact convexHull_min exercise_1_13_second_set_subset_facets
      exercise_1_13_second_facets_convex
  · exact exercise_1_13_second_facets_subset_convexHull

#print axioms exercise_1_13_first_convex_hull
#print axioms exercise_1_13_second_convex_hull
