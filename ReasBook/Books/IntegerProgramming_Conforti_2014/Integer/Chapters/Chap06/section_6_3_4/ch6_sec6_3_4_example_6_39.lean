/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_theorem_6_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_11
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_lemma_6_38

open scoped Matrix Pointwise

noncomputable section

section Example639

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The triangle `B = conv((0,0), (2,0), (0,2))` from Example 6.39. -/
def example_6_39_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![2, 0]
      | _ => ![0, 2])

/-- `example_6_39_triangle` is exactly the triangle
`{x | 0 ≤ x₁, 0 ≤ x₂, x₁ + x₂ ≤ 2}`. -/
theorem example_6_39_triangle_eq :
    example_6_39_triangle =
      {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} := by
  -- The displayed convex hull is definitionally the triangle already computed in Example 6.11.
  exact example_6_11_triangle_eq_standard

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
membership in the interior of the triangle is equivalent to its three strict facet inequalities. -/
lemma example_6_39_mem_interior_triangle_iff (x : R2) :
    x ∈ interior example_6_39_triangle ↔
      0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < (2 : ℝ) := by
  -- Transport the strict-facet description along the definitional identification with Example 6.11.
  exact example_6_11_mem_interior_triangle_iff x

/-- The three boundary lattice points `(1,0)`, `(0,1)`, and `(1,1)` used in Example 6.39. -/
def example_6_39_boundary_point : Fin 3 → R2 :=
  fun i ↦
    match i.1 with
    | 0 => ![(1 : ℝ), 0]
    | 1 => ![0, (1 : ℝ)]
    | _ => ![(1 : ℝ), 1]

/-- Expanding `example_6_39_boundary_point` recovers the three displayed boundary lattice
points. -/
theorem example_6_39_boundary_point_apply
    (i : Fin 3) :
    example_6_39_boundary_point i =
      match i.1 with
      | 0 => ![(1 : ℝ), 0]
      | 1 => ![0, (1 : ℝ)]
      | _ => ![(1 : ℝ), 1] :=
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the three real boundary points have canonical representatives in `ℤ²`. -/
def example_6_39_boundary_integerPoint : Fin 3 → Z2 :=
  fun i ↦
    match i.1 with
    | 0 => ![1, 0]
    | 1 => ![0, 1]
    | _ => ![1, 1]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
casting a canonical integer representative gives the corresponding real boundary point. -/
lemma example_6_39_cast_boundary_integerPoint (i : Fin 3) :
    (Int.cast ∘ example_6_39_boundary_integerPoint i : R2) =
      example_6_39_boundary_point i := by
  -- Both coordinates agree in each of the three finite cases.
  ext j
  fin_cases i
  · fin_cases j
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]
    · norm_num [example_6_39_boundary_integerPoint,
        example_6_39_boundary_point, Function.comp_def, Matrix.vecHead, Matrix.vecTail]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
each displayed boundary point belongs to the triangle. -/
lemma example_6_39_boundaryPoint_mem_triangle (i : Fin 3) :
    example_6_39_boundary_point i ∈ example_6_39_triangle := by
  -- Substitute the three points into the facet description.
  rw [example_6_39_triangle_eq]
  fin_cases i
  · norm_num [example_6_39_boundary_point, Matrix.vecHead, Matrix.vecTail]
  · norm_num [example_6_39_boundary_point, Matrix.vecHead, Matrix.vecTail]
  · norm_num [example_6_39_boundary_point, Matrix.vecHead, Matrix.vecTail]

/-- The translate `B - f`, written as `{r | r + f ∈ B}`. -/
def example_6_39_shifted_triangle (f : R2) : Set R2 :=
  {r : R2 | r + f ∈ example_6_39_triangle}

/-- The source-facing translate `B - f` agrees with the canonical pointwise translate `(-f) +ᵥ B`.
-/
theorem example_6_39_shifted_triangle_eq_neg_vadd
    (f : R2) :
    example_6_39_shifted_triangle f = (-f) +ᵥ example_6_39_triangle := by
  rw [neg_vadd_set_eq_setOf_add_mem]
  ext r
  simp [example_6_39_shifted_triangle, add_comm]

/-- `example_6_39_shifted_triangle f` is the translate of the triangle by `-f`, written by its
three facet inequalities. -/
theorem example_6_39_shifted_triangle_eq
    (f : R2) :
    example_6_39_shifted_triangle f =
      {r : R2 |
        -(f 0) ≤ r 0 ∧
          -(f 1) ≤ r 1 ∧
            r 0 + r 1 ≤ (2 : ℝ) - (f 0 + f 1)} := by
  -- Translate each of the three facet inequalities coordinatewise.
  ext r
  rw [example_6_39_shifted_triangle, example_6_39_triangle_eq]
  simp only [Set.mem_setOf_eq, Pi.add_apply]
  constructor
  · rintro ⟨h0, h1, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨h0, h1, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith

/-- The function `ψ` of Example 6.39, defined as the gauge of `B - f`. -/
def example_6_39_psi (f : R2) : R2 → ℝ :=
  gauge (example_6_39_shifted_triangle f)

/-- Unfolding `example_6_39_psi f` recovers the gauge of the translated triangle `B - f`. -/
theorem example_6_39_psi_def
    (f : R2) :
    example_6_39_psi f = gauge (example_6_39_shifted_triangle f) :=
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the normalized maximum of the three translated facet functionals. -/
noncomputable def example_6_39_facetMax (f r : R2) : ℝ :=
  max (max (-r 0 / f 0) (-r 1 / f 1))
    ((r 0 + r 1) / (2 - (f 0 + f 1)))

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the normalized facet maximum is nonnegative when the center lies in the triangle interior. -/
lemma example_6_39_facetMax_nonnegative
    {f : R2} (hf : f ∈ interior example_6_39_triangle) (r : R2) :
    0 ≤ example_6_39_facetMax f r := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  by_contra hnonneg
  have hmax : example_6_39_facetMax f r < 0 := lt_of_not_ge hnonneg
  have h0 : -r 0 / f 0 < 0 :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have h1 : -r 1 / f 1 < 0 :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hsum : (r 0 + r 1) / (2 - (f 0 + f 1)) < 0 :=
    lt_of_le_of_lt (le_max_right _ _) hmax
  -- Positivity of the three denominators makes the three strict signs contradictory.
  have h0' : -r 0 < 0 := by
    simpa using (div_lt_iff₀ hf0).1 h0
  have h1' : -r 1 < 0 := by
    simpa using (div_lt_iff₀ hf1).1 h1
  have hdenom : 0 < 2 - (f 0 + f 1) := by
    linarith
  have hrsum : r 0 + r 1 < 0 := by
    simpa using (div_lt_iff₀ hdenom).1 hsum
  linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the normalized facet maximum is subadditive. -/
lemma example_6_39_facetMax_add_le (f r s : R2) :
    example_6_39_facetMax f (r + s) ≤
      example_6_39_facetMax f r + example_6_39_facetMax f s := by
  have hr0 : -r 0 / f 0 ≤ example_6_39_facetMax f r :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hr1 : -r 1 / f 1 ≤ example_6_39_facetMax f r :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hrsum : (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f r :=
    le_max_right _ _
  have hs0 : -s 0 / f 0 ≤ example_6_39_facetMax f s :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hs1 : -s 1 / f 1 ≤ example_6_39_facetMax f s :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hssum : (s 0 + s 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f s :=
    le_max_right _ _
  -- Bound each linear branch by the sum of its two pointwise maxima.
  unfold example_6_39_facetMax
  refine max_le (max_le ?_ ?_) ?_
  · calc
      -(r + s) 0 / f 0 = -r 0 / f 0 + -s 0 / f 0 := by
        simp only [Pi.add_apply]
        ring
      _ ≤ example_6_39_facetMax f r + example_6_39_facetMax f s := add_le_add hr0 hs0
  · calc
      -(r + s) 1 / f 1 = -r 1 / f 1 + -s 1 / f 1 := by
        simp only [Pi.add_apply]
        ring
      _ ≤ example_6_39_facetMax f r + example_6_39_facetMax f s := add_le_add hr1 hs1
  · calc
      ((r + s) 0 + (r + s) 1) / (2 - (f 0 + f 1)) =
          (r 0 + r 1) / (2 - (f 0 + f 1)) +
            (s 0 + s 1) / (2 - (f 0 + f 1)) := by
        simp only [Pi.add_apply]
        ring
      _ ≤ example_6_39_facetMax f r + example_6_39_facetMax f s :=
        add_le_add hrsum hssum

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
positive scalar multiplication commutes with the normalized facet maximum. -/
lemma example_6_39_facetMax_smul
    (f r : R2) (c : ℝ) (hc : 0 < c) :
    example_6_39_facetMax f (c • r) = c * example_6_39_facetMax f r := by
  have hbranch0 : -(c * r 0) / f 0 = c * (-r 0 / f 0) := by
    ring
  have hbranch1 : -(c * r 1) / f 1 = c * (-r 1 / f 1) := by
    ring
  have hbranchSum :
      (c * r 0 + c * r 1) / (2 - (f 0 + f 1)) =
        c * ((r 0 + r 1) / (2 - (f 0 + f 1))) := by
    ring
  -- Pull the nonnegative scalar through the two nested maxima.
  simp only [example_6_39_facetMax, Pi.smul_apply, smul_eq_mul,
    hbranch0, hbranch1, hbranchSum]
  rw [← mul_max_of_nonneg _ _ hc.le, ← mul_max_of_nonneg _ _ hc.le]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the normalized facet maximum is sublinear. -/
lemma example_6_39_facetMax_sublinear (f : R2) :
    (example_6_39_facetMax f).Sublinear := by
  -- Package subadditivity and positive homogeneity for the gauge reconstruction theorem.
  exact ⟨example_6_39_facetMax_add_le f, example_6_39_facetMax_smul f⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the shifted triangle is the unit sublevel set of its normalized facet maximum. -/
lemma example_6_39_shifted_triangle_eq_unitSublevel
    {f : R2} (hf : f ∈ interior example_6_39_triangle) :
    example_6_39_shifted_triangle f =
      sublinear_unit_sublevel_set (example_6_39_facetMax f) := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  have hdenom : 0 < 2 - (f 0 + f 1) := by
    linarith
  rw [example_6_39_shifted_triangle_eq]
  ext r
  simp only [Set.mem_setOf_eq, sublinear_unit_sublevel_set, example_6_39_facetMax,
    max_le_iff]
  -- Clearing the three positive denominators recovers the translated facet inequalities.
  constructor
  · rintro ⟨h0, h1, hsum⟩
    have hneg0 : -r 0 ≤ f 0 := by
      linarith
    have hneg1 : -r 1 ≤ f 1 := by
      linarith
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (div_le_one hf0).2 hneg0
    · exact (div_le_one hf1).2 hneg1
    · exact (div_le_one hdenom).2 hsum
  · rintro ⟨⟨h0, h1⟩, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · have := (div_le_one hf0).1 h0
      linarith
    · have := (div_le_one hf1).1 h1
      linarith
    · exact (div_le_one hdenom).1 hsum

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the gauge of the shifted triangle is its normalized three-facet maximum. -/
lemma example_6_39_psi_apply
    {f : R2} (hf : f ∈ interior example_6_39_triangle) (r : R2) :
    example_6_39_psi f r = example_6_39_facetMax f r := by
  -- Use the unit-sublevel interface so later proofs never unfold the gauge construction.
  rw [example_6_39_psi, example_6_39_shifted_triangle_eq_unitSublevel hf]
  exact gauge_sublinear_unit_sublevel_set_eq
    (example_6_39_facetMax_sublinear f) (example_6_39_facetMax_nonnegative hf) r

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the first-coordinate facet is active exactly on its two comparison halfspaces. -/
lemma example_6_39_facetMax_eq_first_iff
    {f : R2} (hf : f ∈ interior example_6_39_triangle) (r : R2) :
    example_6_39_facetMax f r = -r 0 / f 0 ↔
      f 1 * r 0 - f 0 * r 1 ≤ 0 ∧
        (2 - f 1) * r 0 + f 0 * r 1 ≤ 0 := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  have hc : 0 < 2 - (f 0 + f 1) := by
    linarith
  constructor
  · intro hactive
    have hsecond : -r 1 / f 1 ≤ -r 0 / f 0 := by
      calc
        -r 1 / f 1 ≤ example_6_39_facetMax f r :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        _ = -r 0 / f 0 := hactive
    have hthird : (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ -r 0 / f 0 := by
      calc
        (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f r :=
          le_max_right _ _
        _ = -r 0 / f 0 := hactive
    have hsecondCross := (div_le_div_iff₀ hf1 hf0).1 hsecond
    have hthirdCross := (div_le_div_iff₀ hc hf0).1 hthird
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hsecond, hthird⟩
    have hsecond' : -r 1 / f 1 ≤ -r 0 / f 0 := by
      apply (div_le_div_iff₀ hf1 hf0).2
      nlinarith
    have hthird' : (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ -r 0 / f 0 := by
      apply (div_le_div_iff₀ hc hf0).2
      nlinarith
    unfold example_6_39_facetMax
    rw [max_eq_left hsecond', max_eq_left hthird']

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the second-coordinate facet is active exactly on its two comparison halfspaces. -/
lemma example_6_39_facetMax_eq_second_iff
    {f : R2} (hf : f ∈ interior example_6_39_triangle) (r : R2) :
    example_6_39_facetMax f r = -r 1 / f 1 ↔
      0 ≤ f 1 * r 0 - f 0 * r 1 ∧
        f 1 * r 0 + (2 - f 0) * r 1 ≤ 0 := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  have hc : 0 < 2 - (f 0 + f 1) := by
    linarith
  constructor
  · intro hactive
    have hfirst : -r 0 / f 0 ≤ -r 1 / f 1 := by
      calc
        -r 0 / f 0 ≤ example_6_39_facetMax f r :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        _ = -r 1 / f 1 := hactive
    have hthird : (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ -r 1 / f 1 := by
      calc
        (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f r :=
          le_max_right _ _
        _ = -r 1 / f 1 := hactive
    have hfirstCross := (div_le_div_iff₀ hf0 hf1).1 hfirst
    have hthirdCross := (div_le_div_iff₀ hc hf1).1 hthird
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hfirst, hthird⟩
    have hfirst' : -r 0 / f 0 ≤ -r 1 / f 1 := by
      apply (div_le_div_iff₀ hf0 hf1).2
      nlinarith
    have hthird' : (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ -r 1 / f 1 := by
      apply (div_le_div_iff₀ hc hf1).2
      nlinarith
    unfold example_6_39_facetMax
    rw [max_eq_right hfirst', max_eq_left hthird']

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the diagonal facet is active exactly on its two comparison halfspaces. -/
lemma example_6_39_facetMax_eq_diagonal_iff
    {f : R2} (hf : f ∈ interior example_6_39_triangle) (r : R2) :
    example_6_39_facetMax f r = (r 0 + r 1) / (2 - (f 0 + f 1)) ↔
      0 ≤ f 1 * r 0 + (2 - f 0) * r 1 ∧
        0 ≤ (2 - f 1) * r 0 + f 0 * r 1 := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  have hc : 0 < 2 - (f 0 + f 1) := by
    linarith
  constructor
  · intro hactive
    have hfirst : -r 0 / f 0 ≤ (r 0 + r 1) / (2 - (f 0 + f 1)) := by
      calc
        -r 0 / f 0 ≤ example_6_39_facetMax f r :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        _ = (r 0 + r 1) / (2 - (f 0 + f 1)) := hactive
    have hsecond : -r 1 / f 1 ≤ (r 0 + r 1) / (2 - (f 0 + f 1)) := by
      calc
        -r 1 / f 1 ≤ example_6_39_facetMax f r :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        _ = (r 0 + r 1) / (2 - (f 0 + f 1)) := hactive
    have hfirstCross := (div_le_div_iff₀ hf0 hc).1 hfirst
    have hsecondCross := (div_le_div_iff₀ hf1 hc).1 hsecond
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hsecond, hfirst⟩
    have hfirst' : -r 0 / f 0 ≤ (r 0 + r 1) / (2 - (f 0 + f 1)) := by
      apply (div_le_div_iff₀ hf0 hc).2
      nlinarith
    have hsecond' : -r 1 / f 1 ≤ (r 0 + r 1) / (2 - (f 0 + f 1)) := by
      apply (div_le_div_iff₀ hf1 hc).2
      nlinarith
    unfold example_6_39_facetMax
    rw [max_eq_right (max_le hfirst' hsecond')]

/-- The region `R(z_i)` from Example 6.39 attached to the `i`-th boundary lattice point. -/
def example_6_39_lifting_region_at
    (f : R2) (i : Fin 3) : Set R2 :=
  {r : R2 |
    example_6_39_psi f r +
        example_6_39_psi f (example_6_39_boundary_point i - f - r) =
      1}

/-- Membership in `example_6_39_lifting_region_at f i` is exactly the displayed spindle equality
for the boundary point `z_i`. -/
theorem example_6_39_mem_lifting_region_at_iff
    {f r : R2} {i : Fin 3} :
    r ∈ example_6_39_lifting_region_at f i ↔
      example_6_39_psi f r +
          example_6_39_psi f (example_6_39_boundary_point i - f - r) =
        1 :=
  Iff.rfl

/-- The union `R = R(z₁) ∪ R(z₂) ∪ R(z₃)` from Example 6.39. -/
def example_6_39_lifting_region
    (f : R2) : Set R2 :=
  {r : R2 | ∃ i : Fin 3, r ∈ example_6_39_lifting_region_at f i}

/-- Membership in `example_6_39_lifting_region f` means membership in one of the three spindle
regions attached to the boundary lattice points. -/
theorem example_6_39_mem_lifting_region_iff
    {f r : R2} :
    r ∈ example_6_39_lifting_region f ↔
      ∃ i : Fin 3, r ∈ example_6_39_lifting_region_at f i :=
  Iff.rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the triangle contains no embedded integer vector in its interior. -/
lemma example_6_39_triangle_is_lattice_free :
    is_lattice_free example_6_39_triangle := by
  -- The triangle is definitionally the lattice-free triangle from Example 6.11.
  exact example_6_11_triangle_is_lattice_free

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
a positive push-off from a point of a convex set places the boundary point in its interior. -/
lemma convex_mem_interior_of_pushOff
    {L : Set R2} (hLconv : Convex ℝ L) {x z : R2} (hx : x ∈ L)
    {δ : ℝ} (hδ : 0 < δ)
    (hpush : z + δ • (z - x) ∈ interior L) :
    z ∈ interior L := by
  have hone : 0 < 1 + δ := by
    linarith
  have hweight0 : 0 < 1 / (1 + δ) := one_div_pos.mpr hone
  have hweight1 : 0 ≤ δ / (1 + δ) := div_nonneg hδ.le hone.le
  have hweights : 1 / (1 + δ) + δ / (1 + δ) = 1 := by
    field_simp [hone.ne']
  -- Express `z` as a strict convex combination of the pushed point and `x`.
  rw [eq_convexCombo_pushOff x z hδ]
  exact hLconv.combo_interior_self_mem_interior hpush hx hweight0 hweight1 hweights

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
crossing the first coordinate facet admits a positive push-off from `(0,1)` into the triangle. -/
lemma example_6_39_exists_firstFacet_pushOff_mem_interior
    (x : R2) (hx : x 0 < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (![0, 1] + δ • (![0, 1] - x) : R2) ∈ interior example_6_39_triangle := by
  let C : ℝ := |x 1 - 1| + |1 - x 0 - x 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (example_6_39_mem_interior_triangle_iff _).2 ?_⟩
  have hcoordBound : x 1 - 1 ≤ C := by
    have h := le_abs_self (x 1 - 1)
    have hnonneg := abs_nonneg (1 - x 0 - x 1)
    dsimp [C]
    linarith
  have hsumBound : 1 - x 0 - x 1 ≤ C := by
    have h := le_abs_self (1 - x 0 - x 1)
    have hnonneg := abs_nonneg (x 1 - 1)
    dsimp [C]
    linarith
  have hcoordSmall : δ * (x 1 - 1) < 1 := by
    calc
      δ * (x 1 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hcoordBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hsumSmall : δ * (1 - x 0 - x 1) < 1 := by
    calc
      δ * (1 - x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hsumBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The crossed facet is strict, and the small step preserves the other two strict margins.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
crossing the second coordinate facet admits a positive push-off from `(1,0)` into the triangle. -/
lemma example_6_39_exists_secondFacet_pushOff_mem_interior
    (x : R2) (hx : x 1 < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (![1, 0] + δ • (![1, 0] - x) : R2) ∈ interior example_6_39_triangle := by
  let C : ℝ := |x 0 - 1| + |1 - x 0 - x 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (example_6_39_mem_interior_triangle_iff _).2 ?_⟩
  have hcoordBound : x 0 - 1 ≤ C := by
    have h := le_abs_self (x 0 - 1)
    have hnonneg := abs_nonneg (1 - x 0 - x 1)
    dsimp [C]
    linarith
  have hsumBound : 1 - x 0 - x 1 ≤ C := by
    have h := le_abs_self (1 - x 0 - x 1)
    have hnonneg := abs_nonneg (x 0 - 1)
    dsimp [C]
    linarith
  have hcoordSmall : δ * (x 0 - 1) < 1 := by
    calc
      δ * (x 0 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hcoordBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hsumSmall : δ * (1 - x 0 - x 1) < 1 := by
    calc
      δ * (1 - x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hsumBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The crossed facet is strict, and the small step preserves the other two strict margins.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
crossing the diagonal facet admits a positive push-off from `(1,1)` into the triangle. -/
lemma example_6_39_exists_diagonalFacet_pushOff_mem_interior
    (x : R2) (hx : 2 < x 0 + x 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (![1, 1] + δ • (![1, 1] - x) : R2) ∈ interior example_6_39_triangle := by
  let C : ℝ := |x 0 - 1| + |x 1 - 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (example_6_39_mem_interior_triangle_iff _).2 ?_⟩
  have hfirstBound : x 0 - 1 ≤ C := by
    have h := le_abs_self (x 0 - 1)
    have hnonneg := abs_nonneg (x 1 - 1)
    dsimp [C]
    linarith
  have hsecondBound : x 1 - 1 ≤ C := by
    have h := le_abs_self (x 1 - 1)
    have hnonneg := abs_nonneg (x 0 - 1)
    dsimp [C]
    linarith
  have hfirstSmall : δ * (x 0 - 1) < 1 := by
    calc
      δ * (x 0 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hfirstBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hsecondSmall : δ * (x 1 - 1) < 1 := by
    calc
      δ * (x 1 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hsecondBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The diagonal inequality improves automatically; smallness keeps both coordinates positive.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- The fixed triangle of Example 6.39 is maximal lattice-free. -/
theorem example_6_39_triangle_is_maximal_lattice_free :
    is_maximal_lattice_free example_6_39_triangle := by
  rw [is_maximal_lattice_free_iff]
  refine ⟨convex_convexHull ℝ _, example_6_39_triangle_is_lattice_free, ?_⟩
  intro L hBL hLconv hLfree
  apply Set.Subset.antisymm
  · intro x hxL
    by_contra hxB
    rw [example_6_39_triangle_eq] at hxB
    by_cases hx0 : 0 ≤ x 0
    · by_cases hx1 : 0 ≤ x 1
      · have hxsum : 2 < x 0 + x 1 := by
          by_contra h
          exact hxB ⟨hx0, hx1, le_of_not_gt h⟩
        obtain ⟨δ, hδ, hpush⟩ :=
          example_6_39_exists_diagonalFacet_pushOff_mem_interior x hxsum
        have hpushL := interior_mono hBL hpush
        have hzL : (![1, 1] : R2) ∈ interior L :=
          convex_mem_interior_of_pushOff hLconv hxL hδ hpushL
        have hzNot := (is_lattice_free_iff.mp hLfree) (![1, 1] : Z2)
        have hcast : (Int.cast ∘ (![1, 1] : Z2) : R2) = (![1, 1] : R2) := by
          ext j
          fin_cases j
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        rw [hcast] at hzNot
        exact hzNot hzL
      · have hx1' : x 1 < 0 := lt_of_not_ge hx1
        obtain ⟨δ, hδ, hpush⟩ :=
          example_6_39_exists_secondFacet_pushOff_mem_interior x hx1'
        have hpushL := interior_mono hBL hpush
        have hzL : (![1, 0] : R2) ∈ interior L :=
          convex_mem_interior_of_pushOff hLconv hxL hδ hpushL
        have hzNot := (is_lattice_free_iff.mp hLfree) (![1, 0] : Z2)
        have hcast : (Int.cast ∘ (![1, 0] : Z2) : R2) = (![1, 0] : R2) := by
          ext j
          fin_cases j
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        rw [hcast] at hzNot
        exact hzNot hzL
    · have hx0' : x 0 < 0 := lt_of_not_ge hx0
      obtain ⟨δ, hδ, hpush⟩ :=
        example_6_39_exists_firstFacet_pushOff_mem_interior x hx0'
      have hpushL := interior_mono hBL hpush
      have hzL : (![0, 1] : R2) ∈ interior L :=
        convex_mem_interior_of_pushOff hLconv hxL hδ hpushL
      have hzNot := (is_lattice_free_iff.mp hLfree) (![0, 1] : Z2)
      have hcast : (Int.cast ∘ (![0, 1] : Z2) : R2) = (![0, 1] : R2) := by
        ext j
        fin_cases j
        · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
      rw [hcast] at hzNot
      exact hzNot hzL
  · exact hBL

/-- Example 6.39 (1). If `f` lies in the interior of the maximal lattice-free triangle `B`, then
the gauge `ψ` of `B - f` is a minimal valid function for `R_f`. -/
theorem example_6_39_psi_is_minimal_valid_function
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f (example_6_39_psi f) := by
  -- Apply the general maximal-lattice-free gauge theorem and align the addition convention.
  simpa [example_6_39_psi, example_6_39_shifted_triangle, add_comm] using
    gaugeTranslateIsMinimalOfMaximalLatticeFree
      example_6_39_triangle_is_maximal_lattice_free hf

/-- Under the interior-point hypothesis of Example 6.39, `example_6_39_psi f` is available
through the chapter's canonical minimal-valid-function instance. -/
instance instExample639PsiMinimalValidFunction
    {f : R2} [Fact (f ∈ interior example_6_39_triangle)] :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f (example_6_39_psi f) :=
  example_6_39_psi_is_minimal_valid_function ‹Fact (f ∈ interior example_6_39_triangle)›.out

/-- Example 6.39 (2). For each of the three boundary lattice points `z_i`, the gauge of `B - f`
evaluated at `z_i - f` is equal to `1`. -/
theorem example_6_39_boundary_points_gauge_eq_one
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (i : Fin 3) :
    example_6_39_psi f (example_6_39_boundary_point i - f) = 1 := by
  have hmem :
      example_6_39_boundary_point i - f ∈ example_6_39_shifted_triangle f := by
    -- Adding `f` back recovers the boundary point of the original triangle.
    simpa [example_6_39_shifted_triangle, sub_eq_add_neg, add_assoc] using
      example_6_39_boundaryPoint_mem_triangle i
  have hupper :
      example_6_39_psi f (example_6_39_boundary_point i - f) ≤ 1 := by
    exact gauge_le_one_of_mem hmem
  have hz : (Int.cast ∘ example_6_39_boundary_integerPoint i : R2) ∈ integerVectors 2 :=
    (mem_integerVectors_iff).2 ⟨example_6_39_boundary_integerPoint i, rfl⟩
  have hlower :
      1 ≤ example_6_39_psi f
        ((Int.cast ∘ example_6_39_boundary_integerPoint i : R2) - f) := by
    -- Lattice-freeness forces gauge at every translated integer point to be at least one.
    simpa [example_6_39_psi, example_6_39_shifted_triangle, add_comm] using
      one_le_gauge_sub_of_integerPoint
        (convex_convexHull ℝ _) example_6_39_triangle_is_lattice_free hf hz
  rw [example_6_39_cast_boundary_integerPoint] at hlower
  exact le_antisymm hupper hlower

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
membership in each spindle is equivalent to its four explicit facet-coordinate bounds. -/
lemma example_6_39_mem_lifting_region_at_iff_facetBounds
    {f r : R2} (hf : f ∈ interior example_6_39_triangle) (i : Fin 3) :
    r ∈ example_6_39_lifting_region_at f i ↔
      match i.1 with
      | 0 =>
          0 ≤ f 1 * r 0 - f 0 * r 1 ∧
            f 1 * r 0 - f 0 * r 1 ≤ f 1 ∧
              -f 1 ≤ f 1 * r 0 + (2 - f 0) * r 1 ∧
                f 1 * r 0 + (2 - f 0) * r 1 ≤ 0
      | 1 =>
          -f 0 ≤ f 1 * r 0 - f 0 * r 1 ∧
            f 1 * r 0 - f 0 * r 1 ≤ 0 ∧
              -f 0 ≤ (2 - f 1) * r 0 + f 0 * r 1 ∧
                (2 - f 1) * r 0 + f 0 * r 1 ≤ 0
      | _ =>
          0 ≤ f 1 * r 0 + (2 - f 0) * r 1 ∧
            f 1 * r 0 + (2 - f 0) * r 1 ≤ 2 - (f 0 + f 1) ∧
              0 ≤ (2 - f 1) * r 0 + f 0 * r 1 ∧
                (2 - f 1) * r 0 + f 0 * r 1 ≤ 2 - (f 0 + f 1) := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  have hc : 0 < 2 - (f 0 + f 1) := by
    linarith
  fin_cases i
  · let s : R2 := example_6_39_boundary_point 0 - f - r
    change example_6_39_psi f r + example_6_39_psi f s = 1 ↔ _
    rw [example_6_39_psi_apply hf, example_6_39_psi_apply hf]
    have hlinear : -r 1 / f 1 + -s 1 / f 1 = 1 := by
      dsimp [s, example_6_39_boundary_point]
      norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
      field_simp [hf1.ne']
      ring
    constructor
    · intro hsum
      have hrLower : -r 1 / f 1 ≤ example_6_39_facetMax f r :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hsLower : -s 1 / f 1 ≤ example_6_39_facetMax f s :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hrActive : example_6_39_facetMax f r = -r 1 / f 1 := by
        linarith
      have hsActive : example_6_39_facetMax f s = -s 1 / f 1 := by
        linarith
      rcases (example_6_39_facetMax_eq_second_iff hf r).1 hrActive with ⟨hrP, hrQ⟩
      rcases (example_6_39_facetMax_eq_second_iff hf s).1 hsActive with ⟨hsP, hsQ⟩
      dsimp [s, example_6_39_boundary_point] at hsP hsQ
      norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply] at hsP hsQ
      refine ⟨hrP, ?_, ?_, hrQ⟩
      · nlinarith
      · nlinarith
    · rintro ⟨hrP, hrP', hrQ', hrQ⟩
      have hrActive := (example_6_39_facetMax_eq_second_iff hf r).2 ⟨hrP, hrQ⟩
      have hsActive : example_6_39_facetMax f s = -s 1 / f 1 := by
        apply (example_6_39_facetMax_eq_second_iff hf s).2
        dsimp [s, example_6_39_boundary_point]
        norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
        constructor
        · nlinarith
        · nlinarith
      rw [hrActive, hsActive, hlinear]
  · let s : R2 := example_6_39_boundary_point 1 - f - r
    change example_6_39_psi f r + example_6_39_psi f s = 1 ↔ _
    rw [example_6_39_psi_apply hf, example_6_39_psi_apply hf]
    have hlinear : -r 0 / f 0 + -s 0 / f 0 = 1 := by
      dsimp [s, example_6_39_boundary_point]
      norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
      field_simp [hf0.ne']
      ring
    constructor
    · intro hsum
      have hrLower : -r 0 / f 0 ≤ example_6_39_facetMax f r :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hsLower : -s 0 / f 0 ≤ example_6_39_facetMax f s :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hrActive : example_6_39_facetMax f r = -r 0 / f 0 := by
        linarith
      have hsActive : example_6_39_facetMax f s = -s 0 / f 0 := by
        linarith
      rcases (example_6_39_facetMax_eq_first_iff hf r).1 hrActive with ⟨hrP, hrR⟩
      rcases (example_6_39_facetMax_eq_first_iff hf s).1 hsActive with ⟨hsP, hsR⟩
      dsimp [s, example_6_39_boundary_point] at hsP hsR
      norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply] at hsP hsR
      refine ⟨?_, hrP, ?_, hrR⟩
      · nlinarith
      · nlinarith
    · rintro ⟨hrP', hrP, hrR', hrR⟩
      have hrActive := (example_6_39_facetMax_eq_first_iff hf r).2 ⟨hrP, hrR⟩
      have hsActive : example_6_39_facetMax f s = -s 0 / f 0 := by
        apply (example_6_39_facetMax_eq_first_iff hf s).2
        dsimp [s, example_6_39_boundary_point]
        norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
        constructor
        · nlinarith
        · nlinarith
      rw [hrActive, hsActive, hlinear]
  · let s : R2 := example_6_39_boundary_point 2 - f - r
    change example_6_39_psi f r + example_6_39_psi f s = 1 ↔ _
    rw [example_6_39_psi_apply hf, example_6_39_psi_apply hf]
    have hlinear :
        (r 0 + r 1) / (2 - (f 0 + f 1)) +
          (s 0 + s 1) / (2 - (f 0 + f 1)) = 1 := by
      dsimp [s, example_6_39_boundary_point]
      field_simp [hc.ne']
      ring
    constructor
    · intro hsum
      have hrLower :
          (r 0 + r 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f r :=
        le_max_right _ _
      have hsLower :
          (s 0 + s 1) / (2 - (f 0 + f 1)) ≤ example_6_39_facetMax f s :=
        le_max_right _ _
      have hrActive :
          example_6_39_facetMax f r = (r 0 + r 1) / (2 - (f 0 + f 1)) := by
        linarith
      have hsActive :
          example_6_39_facetMax f s = (s 0 + s 1) / (2 - (f 0 + f 1)) := by
        linarith
      rcases (example_6_39_facetMax_eq_diagonal_iff hf r).1 hrActive with ⟨hrQ, hrR⟩
      rcases (example_6_39_facetMax_eq_diagonal_iff hf s).1 hsActive with ⟨hsQ, hsR⟩
      dsimp [s, example_6_39_boundary_point] at hsQ hsR
      refine ⟨hrQ, ?_, hrR, ?_⟩
      · nlinarith
      · nlinarith
    · rintro ⟨hrQ, hrQ', hrR, hrR'⟩
      have hrActive := (example_6_39_facetMax_eq_diagonal_iff hf r).2 ⟨hrQ, hrR⟩
      have hsActive :
          example_6_39_facetMax f s = (s 0 + s 1) / (2 - (f 0 + f 1)) := by
        apply (example_6_39_facetMax_eq_diagonal_iff hf s).2
        dsimp [s, example_6_39_boundary_point]
        constructor
        · nlinarith
        · nlinarith
      rw [hrActive, hsActive, hlinear]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the high-`Q`, high-`R` part of the low-`P` sector lies in one of two explicit spindle translates. -/
lemma example_6_39_unitSquareTranslateOfLowPHighQHighR
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hP : f 1 * x - f 0 * y ≤ f 1 - f 0)
    (hQ : 2 - f 0 ≤ f 1 * x + (2 - f 0) * y)
    (hR : 2 - f 1 ≤ (2 - f 1) * x + f 0 * y) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  by_cases hPleft : f 1 * x - f 0 * y ≤ f 1 - 2 * f 0
  · refine ⟨![0, -2], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨0, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 0).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hy0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]
  · have hPleft' : f 1 - 2 * f 0 < f 1 * x - f 0 * y := lt_of_not_ge hPleft
    refine ⟨![-1, -1], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨1, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 1).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hy0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the high-`Q`, low-`R` part of the low-`P` sector lies in one of two explicit spindle translates. -/
lemma example_6_39_unitSquareTranslateOfLowPHighQLowR
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hy1 : y < 1)
    (hP : f 1 * x - f 0 * y ≤ f 1 - f 0)
    (hQ : 2 - f 0 ≤ f 1 * x + (2 - f 0) * y)
    (hR : (2 - f 1) * x + f 0 * y < 2 - f 1) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  let c : ℝ := 2 - (f 0 + f 1)
  by_cases hQtop : 2 - f 0 + c ≤ f 1 * x + (2 - f 0) * y
  · refine ⟨![0, -2], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨0, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 0).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]
  · have hQtop' : f 1 * x + (2 - f 0) * y < 2 - f 0 + c := lt_of_not_ge hQtop
    refine ⟨![0, -1], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨2, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 2).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the low-`Q` part of the low-`P` sector lies in one of two explicit spindle translates. -/
lemma example_6_39_unitSquareTranslateOfLowPLowQ
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hP : f 1 * x - f 0 * y ≤ f 1 - f 0)
    (hQ : f 1 * x + (2 - f 0) * y < 2 - f 0) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  let c : ℝ := 2 - (f 0 + f 1)
  by_cases hQmiddle : c ≤ f 1 * x + (2 - f 0) * y
  · refine ⟨![0, -1], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨0, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 0).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hx0, mul_nonneg hf0.le hy0,
      mul_nonneg hf1.le hx0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]
  · have hQmiddle' : f 1 * x + (2 - f 0) * y < c := lt_of_not_ge hQmiddle
    refine ⟨![0, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨2, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 2).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hx0, mul_nonneg hf0.le hy0,
      mul_nonneg hf1.le hx0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the far-right part of the high-`P`, high-`R` sector lies in one of two spindle translates. -/
lemma example_6_39_unitSquareTranslateOfHighPHighRRight
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx1 : x < 1)
    (hP : f 1 - f 0 < f 1 * x - f 0 * y)
    (hR : 2 - f 1 ≤ (2 - f 1) * x + f 0 * y)
    (hPright : 2 * f 1 - f 0 ≤ f 1 * x - f 0 * y) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  let c : ℝ := 2 - (f 0 + f 1)
  by_cases hRtop : (2 - f 1) * x + f 0 * y ≤ 2 - f 1 + c
  · refine ⟨![-1, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨2, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 2).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le (sub_nonneg.mpr hx1.le)]
  · have hRtop' : 2 - f 1 + c < (2 - f 1) * x + f 0 * y := lt_of_not_ge hRtop
    refine ⟨![-2, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨1, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 1).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le (sub_nonneg.mpr hx1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the middle part of the high-`P`, high-`R` sector lies in one of two spindle translates. -/
lemma example_6_39_unitSquareTranslateOfHighPHighRMiddle
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx1 : x < 1) (hy1 : y < 1)
    (hP : f 1 - f 0 < f 1 * x - f 0 * y)
    (hR : 2 - f 1 ≤ (2 - f 1) * x + f 0 * y)
    (hPright : f 1 * x - f 0 * y < 2 * f 1 - f 0) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  by_cases hQmiddle : f 1 * x + (2 - f 0) * y ≤ 2 - f 0
  · refine ⟨![-1, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨2, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 2).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]
  · have hQmiddle' : 2 - f 0 < f 1 * x + (2 - f 0) * y := lt_of_not_ge hQmiddle
    refine ⟨![-1, -1], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨0, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 0).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
the low-`R` part of the high-`P` sector lies in one of two explicit spindle translates. -/
lemma example_6_39_unitSquareTranslateOfHighPLowR
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hP : f 1 - f 0 < f 1 * x - f 0 * y)
    (hR : (2 - f 1) * x + f 0 * y < 2 - f 1) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  rcases (example_6_39_mem_interior_triangle_iff f).1 hf with ⟨hf0, hf1, hfsum⟩
  let c : ℝ := 2 - (f 0 + f 1)
  by_cases hRmiddle : c ≤ (2 - f 1) * x + f 0 * y
  · refine ⟨![-1, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨1, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 1).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hx0, mul_nonneg hf0.le hy0,
      mul_nonneg hf1.le hx0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]
  · have hRmiddle' : (2 - f 1) * x + f 0 * y < c := lt_of_not_ge hRmiddle
    refine ⟨![0, 0], ?_⟩
    rw [example_6_39_mem_lifting_region_iff]
    refine ⟨2, (example_6_39_mem_lifting_region_at_iff_facetBounds hf 2).2 ?_⟩
    norm_num [Matrix.vecHead, Matrix.vecTail]
    dsimp [c] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals ring_nf
    all_goals nlinarith [mul_nonneg hf0.le hx0, mul_nonneg hf0.le hy0,
      mul_nonneg hf1.le hx0, mul_nonneg hf1.le hy0,
      mul_nonneg hf0.le (sub_nonneg.mpr hx1.le),
      mul_nonneg hf1.le (sub_nonneg.mpr hy1.le)]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
every point of the half-open unit square has an integer translate in one of the three spindles. -/
lemma example_6_39_unitSquare_has_translate_in_liftingRegion
    {f : R2} (hf : f ∈ interior example_6_39_triangle)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∃ w : Z2,
      (fun i : Fin 2 ↦ (![x, y] : R2) i + (w i : ℝ)) ∈
        example_6_39_lifting_region f := by
  let P : ℝ := f 1 * x - f 0 * y
  let Q : ℝ := f 1 * x + (2 - f 0) * y
  let R : ℝ := (2 - f 1) * x + f 0 * y
  -- The following facet-coordinate case split is a fundamental-domain decomposition.
  by_cases hP : P ≤ f 1 - f 0
  · by_cases hQhigh : 2 - f 0 ≤ Q
    · by_cases hRhigh : 2 - f 1 ≤ R
      · exact example_6_39_unitSquareTranslateOfLowPHighQHighR
          hf hx1 hy0 hy1 hP hQhigh hRhigh
      · have hRhigh' : R < 2 - f 1 := lt_of_not_ge hRhigh
        exact example_6_39_unitSquareTranslateOfLowPHighQLowR
          hf hy1 hP hQhigh hRhigh'
    · have hQhigh' : Q < 2 - f 0 := lt_of_not_ge hQhigh
      exact example_6_39_unitSquareTranslateOfLowPLowQ
        hf hx0 hx1 hy0 hy1 hP hQhigh'
  · have hP' : f 1 - f 0 < P := lt_of_not_ge hP
    by_cases hRhigh : 2 - f 1 ≤ R
    · by_cases hPright : 2 * f 1 - f 0 ≤ P
      · exact example_6_39_unitSquareTranslateOfHighPHighRRight
          hf hx1 hP' hRhigh hPright
      · have hPright' : P < 2 * f 1 - f 0 := lt_of_not_ge hPright
        exact example_6_39_unitSquareTranslateOfHighPHighRMiddle
          hf hx1 hy1 hP' hRhigh hPright'
    · have hRhigh' : R < 2 - f 1 := lt_of_not_ge hRhigh
      exact example_6_39_unitSquareTranslateOfHighPLowR
        hf hx0 hx1 hy0 hy1 hP' hRhigh'

/-- Example 6.39 (3). The integer translates of the lifting region
`R = R(z₁) ∪ R(z₂) ∪ R(z₃)` cover the whole plane. -/
theorem example_6_39_lifting_region_covers_plane
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (r : R2) :
    ∃ w : Z2, (fun i : Fin 2 ↦ r i + (w i : ℝ)) ∈ example_6_39_lifting_region f := by
    let m : ℤ := ⌊r 0⌋
    let n : ℤ := ⌊r 1⌋
    let x : ℝ := r 0 - (m : ℝ)
    let y : ℝ := r 1 - (n : ℝ)
    have hx0 : 0 ≤ x := by
      dsimp [x, m]
      exact sub_nonneg.mpr (Int.floor_le (r 0))
    have hx1 : x < 1 := by
      have h := Int.lt_floor_add_one (r 0)
      change r 0 < (m : ℝ) + 1 at h
      dsimp [x]
      linarith
    have hy0 : 0 ≤ y := by
      dsimp [y, n]
      exact sub_nonneg.mpr (Int.floor_le (r 1))
    have hy1 : y < 1 := by
      have h := Int.lt_floor_add_one (r 1)
      change r 1 < (n : ℝ) + 1 at h
      dsimp [y]
      linarith
    obtain ⟨v, hv⟩ :=
      example_6_39_unitSquare_has_translate_in_liftingRegion hf hx0 hx1 hy0 hy1
    let w : Z2 := v - ![m, n]
    refine ⟨w, ?_⟩
    have htranslate :
        (fun i : Fin 2 ↦ r i + (w i : ℝ)) =
          (fun i : Fin 2 ↦ (![x, y] : R2) i + (v i : ℝ)) := by
      -- Removing the coordinatewise floors and then adding `v` gives the same translated point.
      ext i
      fin_cases i
      · norm_num [w, x, m, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
        rw [Int.fract]
        ring
      · norm_num [w, y, n, Matrix.vecHead, Matrix.vecTail, Pi.sub_apply]
        rw [Int.fract]
        ring
    rw [htranslate]
    exact hv

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
shifting the continuous singleton by an integer vector preserves mixed-integer feasibility. -/
lemma example_6_39_integerTranslateTouching_mem_mixedIntegerRelaxation
    (f r : R2) (w z : Z2) :
    (Finsupp.single r 1,
        Finsupp.single
          ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) (1 : NNReal)) ∈
      mixed_integer_relaxation_set f := by
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨fun i ↦ z i - w i, ?_⟩
  -- Absorb the translate into the integral balance witness coordinatewise.
  ext i
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean:
a touching translated gauge value is bounded above by every valid lifting coefficient. -/
lemma example_6_39_psi_le_validLifting_of_integerTranslate_touching
    {f : R2} {ρ ψ : R2 → ℝ}
    (hρ : IsValidGomoryJohnsonPair f ρ ψ)
    (r : R2) (w z : Z2)
    (htouch :
      ψ (fun i ↦ r i + (w i : ℝ)) +
          ψ ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) = 1) :
    ψ (fun i ↦ r i + (w i : ℝ)) ≤ ρ r := by
  have hone :
      1 ≤ ρ r +
        ψ ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) := by
    simpa using hρ.one_le
      (example_6_39_integerTranslateTouching_mem_mixedIntegerRelaxation f r w z)
  -- Mixed validity and touching have the same complementary gauge term, so it cancels.
  linarith

/-- Example 6.39 (4). Because the lifting region covers `ℝ²` modulo integer translations, the
trivial lifting of `ψ` is a minimal lifting of `ψ`. -/
theorem example_6_39_trivial_lifting_is_minimal_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle) :
    IsMinimalLiftingOf f (trivial_lifting (example_6_39_psi f)) (example_6_39_psi f) := by
  refine
    { toIsValidGomoryJohnsonPair :=
        trivial_lifting_is_lifting f (example_6_39_psi f)
          (example_6_39_psi_is_minimal_valid_function hf).toIsValidFunctionForContinuousInfiniteRelaxation
      eq_of_le := ?_ }
  intro ρ hρ hρUpper
  funext r
  obtain ⟨w, hwRegion⟩ := example_6_39_lifting_region_covers_plane hf r
  rcases (example_6_39_mem_lifting_region_iff).1 hwRegion with ⟨i, hi⟩
  have hcast :
      (fun j ↦ ((example_6_39_boundary_integerPoint i) j : ℝ)) =
        example_6_39_boundary_point i := by
    simpa [Function.comp_def] using example_6_39_cast_boundary_integerPoint i
  have htouch :
      example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) +
          example_6_39_psi f
            ((fun j ↦ ((example_6_39_boundary_integerPoint i) j : ℝ)) - f -
              (fun j ↦ r j + (w j : ℝ))) = 1 := by
    -- The covering witness lies in a spindle whose defining equality is the touching equation.
    rw [hcast]
    exact hi
  have hpsiLower :
      example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) ≤ ρ r :=
    example_6_39_psi_le_validLifting_of_integerTranslate_touching hρ r w
      (example_6_39_boundary_integerPoint i) htouch
  have htrivialLower :
      trivial_lifting (example_6_39_psi f) r ≤
        example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) := by
    rw [trivial_lifting_apply]
    refine csInf_le ?_ ⟨w, rfl⟩
    use 0
    rintro _ ⟨v, rfl⟩
    exact continuousValidFunctionNonnegative
      (example_6_39_psi_is_minimal_valid_function hf).toIsValidFunctionForContinuousInfiniteRelaxation _
  -- The assumed upper bound and the selected touching translate squeeze the two liftings.
  exact le_antisymm (hρUpper r) (htrivialLower.trans hpsiLower)

/-- Under the interior-point hypothesis of Example 6.39, the trivial lifting is available
through the canonical minimal-lifting instance. -/
instance instExample639TrivialLiftingMinimalLifting
    {f : R2} [Fact (f ∈ interior example_6_39_triangle)] :
    IsMinimalLiftingOf f (trivial_lifting (example_6_39_psi f)) (example_6_39_psi f) :=
  example_6_39_trivial_lifting_is_minimal_lifting
    ‹Fact (f ∈ interior example_6_39_triangle)›.out

/-- Example 6.39 (5). Under the same hypotheses, every minimal lifting of `ψ` coincides with the
trivial lifting; equivalently, the trivial lifting is the unique minimal lifting of `ψ`. -/
theorem example_6_39_eq_trivial_lifting_of_minimal_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    {π : R2 → ℝ}
    (hπ : IsMinimalLiftingOf f π (example_6_39_psi f)) :
    π = trivial_lifting (example_6_39_psi f) := by
  -- Minimality of the trivial lifting upgrades the universal pointwise bound to equality.
  exact (example_6_39_trivial_lifting_is_minimal_lifting hf).eq_of_le
    hπ.toIsValidGomoryJohnsonPair
    (minimal_lifting_le_trivial_lifting f (example_6_39_psi f) π hπ)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_4/ch6_sec6_3_4_example_6_39.lean

Example 6.39 (6). For every `r ∈ ℝ²`, there is an integer vector `w̄` such that `r + w̄`
lies in the lifting region and realizes the trivial lifting value
`inf_{w ∈ ℤ²} ψ(r + w) = ψ(r + w̄)`. -/
theorem example_6_39_exists_translate_attaining_trivial_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (r : R2) :
    ∃ wbar : Z2,
      (fun i : Fin 2 ↦ r i + (wbar i : ℝ)) ∈ example_6_39_lifting_region f ∧
        trivial_lifting (example_6_39_psi f) r =
          example_6_39_psi f (fun i : Fin 2 ↦ r i + (wbar i : ℝ)) := by
  obtain ⟨w, hwRegion⟩ := example_6_39_lifting_region_covers_plane hf r
  refine ⟨w, hwRegion, ?_⟩
  rcases (example_6_39_mem_lifting_region_iff).1 hwRegion with ⟨i, hi⟩
  have hcast :
      (fun j ↦ ((example_6_39_boundary_integerPoint i) j : ℝ)) =
        example_6_39_boundary_point i := by
    simpa [Function.comp_def] using example_6_39_cast_boundary_integerPoint i
  have htouch :
      example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) +
          example_6_39_psi f
            ((fun j ↦ ((example_6_39_boundary_integerPoint i) j : ℝ)) - f -
              (fun j ↦ r j + (w j : ℝ))) = 1 := by
    -- The chosen spindle supplies the touching equation for its boundary lattice point.
    rw [hcast]
    exact hi
  have htrivialUpper :
      trivial_lifting (example_6_39_psi f) r ≤
        example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) := by
    rw [trivial_lifting_apply]
    refine csInf_le ?_ ⟨w, rfl⟩
    use 0
    rintro _ ⟨v, rfl⟩
    exact continuousValidFunctionNonnegative
      (example_6_39_psi_is_minimal_valid_function hf).toIsValidFunctionForContinuousInfiniteRelaxation _
  have hpsiUpper :
      example_6_39_psi f (fun j ↦ r j + (w j : ℝ)) ≤
        trivial_lifting (example_6_39_psi f) r :=
    example_6_39_psi_le_validLifting_of_integerTranslate_touching
      (example_6_39_trivial_lifting_is_minimal_lifting hf).toIsValidGomoryJohnsonPair r w
      (example_6_39_boundary_integerPoint i) htouch
  -- The infimum bound and mixed-validity bound meet at the selected translate.
  exact le_antisymm htrivialUpper hpsiUpper

end Example639

#print axioms example_6_39_exists_translate_attaining_trivial_lifting
