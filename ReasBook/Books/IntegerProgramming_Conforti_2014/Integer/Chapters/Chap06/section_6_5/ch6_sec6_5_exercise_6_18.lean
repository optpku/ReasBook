import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_example_6_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_17

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise618

/-- Helper for Exercise 6.18: the left interior breakpoint of `example_6_23_pi2`. -/
noncomputable abbrev pi2LeftBreakpoint (_t f : ℝ) : ℝ :=
  1 - f

/-- Helper for Exercise 6.18: the middle-left breakpoint of `example_6_23_pi2`. -/
noncomputable abbrev pi2MiddleLeftBreakpoint (t f : ℝ) : ℝ :=
  1 - f + t / (2 - f + t)

/-- Helper for Exercise 6.18: the middle-right breakpoint of `example_6_23_pi2`. -/
noncomputable abbrev pi2MiddleRightBreakpoint (t f : ℝ) : ℝ :=
  1 - t / (2 - f + t)

/-- Helper for Exercise 6.18: the parameter hypotheses force the positivity facts used by all
breakpoint and branch computations. -/
theorem pi2ParameterFacts
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    0 < f ∧ t < f ∧ 0 < 1 - f ∧ 0 < 2 - f ∧ 0 < 2 - f + t := by
  -- First isolate the scalar inequalities that recur throughout the four-cell geometry.
  have hf_pos : 0 < f := by
    linarith
  have htf : t < f := by
    linarith
  constructor
  · exact hf_pos
  constructor
  · exact htf
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Helper for Exercise 6.18: the three internal breakpoints of `example_6_23_pi2` are strictly
ordered inside `(0, 1)`. -/
theorem pi2BreakpointOrder
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    0 < pi2LeftBreakpoint t f ∧
      pi2LeftBreakpoint t f < pi2MiddleLeftBreakpoint t f ∧
        pi2MiddleLeftBreakpoint t f < pi2MiddleRightBreakpoint t f ∧
          pi2MiddleRightBreakpoint t f < 1 := by
  rcases pi2ParameterFacts ht hft hf with ⟨_, htf, h1f, h2f, hden⟩
  have hleft_lt_mid :
      pi2LeftBreakpoint t f < pi2MiddleLeftBreakpoint t f := by
    -- The second breakpoint is obtained by shifting the first by a positive fraction.
    dsimp [pi2LeftBreakpoint, pi2MiddleLeftBreakpoint]
    have hfrac : 0 < t / (2 - f + t) := by
      exact div_pos ht hden
    linarith
  have hmid_lt_right :
      pi2MiddleLeftBreakpoint t f < pi2MiddleRightBreakpoint t f := by
    -- The middle gap simplifies to a positive rational expression in `f - t` and `2 - f`.
    have hnum : 0 < (2 - f) * (f - t) := by
      positivity
    have hgap :
        pi2MiddleRightBreakpoint t f - pi2MiddleLeftBreakpoint t f =
          ((2 - f) * (f - t)) / (2 - f + t) := by
      dsimp [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
      field_simp [hden.ne']
      ring
    have hgap_pos :
        0 < pi2MiddleRightBreakpoint t f - pi2MiddleLeftBreakpoint t f := by
      rw [hgap]
      exact div_pos hnum hden
    linarith
  have hright_lt_one : pi2MiddleRightBreakpoint t f < 1 := by
    -- The last breakpoint lies one positive fraction below `1`.
    dsimp [pi2MiddleRightBreakpoint]
    have hfrac : 0 < t / (2 - f + t) := by
      exact div_pos ht hden
    linarith
  constructor
  · simpa [pi2LeftBreakpoint] using h1f
  constructor
  · exact hleft_lt_mid
  constructor
  · exact hmid_lt_right
  · exact hright_lt_one

/-- Helper for Exercise 6.18: the adjacent affine formulas for `example_6_23_pi2` match at the
left interior breakpoint. -/
theorem pi2LeftBreakpoint_branchMatch
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pi2LeftBreakpoint t f / (1 - f) =
      (1 - pi2LeftBreakpoint t f + t - f) / t := by
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, h1f, _, _⟩
  -- Both adjacent formulas evaluate to `1` at `1 - f`.
  dsimp [pi2LeftBreakpoint]
  field_simp [ht.ne', sub_ne_zero.mpr hf.ne]
  ring

/-- Helper for Exercise 6.18: the adjacent affine formulas for `example_6_23_pi2` match at the
middle-left breakpoint. -/
theorem pi2MiddleLeftBreakpoint_branchMatch
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    (1 - pi2MiddleLeftBreakpoint t f + t - f) / t =
      pi2MiddleLeftBreakpoint t f / (2 - f) := by
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, _, h2f, hden⟩
  -- The source formulas were designed so the descending and central affine pieces glue exactly.
  dsimp [pi2MiddleLeftBreakpoint]
  field_simp [ht.ne', h2f.ne', hden.ne']
  ring

/-- Helper for Exercise 6.18: the adjacent affine formulas for `example_6_23_pi2` match at the
middle-right breakpoint. -/
theorem pi2MiddleRightBreakpoint_branchMatch
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pi2MiddleRightBreakpoint t f / (2 - f) =
      (1 - pi2MiddleRightBreakpoint t f) / t := by
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, _, h2f, hden⟩
  -- The central and right affine pieces also meet without a jump.
  dsimp [pi2MiddleRightBreakpoint]
  field_simp [ht.ne', h2f.ne', hden.ne']
  ring

/-- Helper for Exercise 6.18: on the left cell, `example_6_23_pi2` is given by the slope
`1 / (1 - f)`. -/
theorem example_6_23_pi2_eq_on_leftCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f)) :
    example_6_23_pi2 t f u = u / (1 - f) := by
  -- On `[0, 1 - f]`, the first branch of the source formula is active.
  have hu_upper : u ≤ 1 - f := by
    simpa [pi2LeftBreakpoint] using hu.2
  have hu1 : u < 1 := by
    linarith
  have hformula := example_6_23_pi2_eq_on_Ico t f u hu.1 hu1
  simpa [hu_upper] using hformula

/-- Helper for Exercise 6.18: on the descending cell, `example_6_23_pi2` is given by the slope
`-1 / t`. -/
theorem example_6_23_pi2_eq_on_descendingCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Ioc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f)) :
    example_6_23_pi2 t f u = (1 - u + t - f) / t := by
  -- Between the first two breakpoints, the second branch is the unique active one.
  have hu0 : 0 ≤ u := by
    rcases pi2BreakpointOrder ht hft hf with ⟨hleft_pos, _, _, _⟩
    exact le_of_lt (lt_trans hleft_pos hu.1)
  have hu1 : u < 1 := by
    rcases pi2BreakpointOrder ht hft hf with ⟨_, _, hmid_lt_right, hright_lt_one⟩
    have hu_upper : u ≤ pi2MiddleLeftBreakpoint t f := hu.2
    exact lt_of_le_of_lt hu_upper (lt_trans hmid_lt_right hright_lt_one)
  have hformula := example_6_23_pi2_eq_on_Ico t f u hu0 hu1
  have hnot_left : ¬ u ≤ 1 - f := by
    simpa [pi2LeftBreakpoint] using not_le.mpr hu.1
  have hu_mid : u ≤ 1 - f + t / (2 - f + t) := by
    simpa [pi2MiddleLeftBreakpoint] using hu.2
  simpa [hnot_left, hu_mid] using hformula

/-- Helper for Exercise 6.18: on the central cell, `example_6_23_pi2` is given by the slope
`1 / (2 - f)`. -/
theorem example_6_23_pi2_eq_on_centralCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Ioc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f)) :
    example_6_23_pi2 t f u = u / (2 - f) := by
  -- Past the descending cell and before the last breakpoint, the third branch is active.
  have hu0 : 0 ≤ u := by
    rcases pi2BreakpointOrder ht hft hf with ⟨hleft_pos, hleft_lt_mid, _, _⟩
    exact le_of_lt (lt_trans (lt_trans hleft_pos hleft_lt_mid) hu.1)
  have hu1 : u < 1 := by
    rcases pi2BreakpointOrder ht hft hf with ⟨_, _, _, hright_lt_one⟩
    exact lt_of_le_of_lt hu.2 hright_lt_one
  have hformula := example_6_23_pi2_eq_on_Ico t f u hu0 hu1
  have hnot_left : ¬ u ≤ 1 - f := by
    have : pi2LeftBreakpoint t f < u := by
      rcases pi2BreakpointOrder ht hft hf with ⟨_, hleft_lt_mid, _, _⟩
      exact lt_trans hleft_lt_mid hu.1
    simpa [pi2LeftBreakpoint] using not_le.mpr this
  have hnot_mid : ¬ u ≤ 1 - f + t / (2 - f + t) := by
    simpa [pi2MiddleLeftBreakpoint] using not_le.mpr hu.1
  have hu_right : u ≤ 1 - t / (2 - f + t) := by
    simpa [pi2MiddleRightBreakpoint] using hu.2
  simpa [hnot_left, hnot_mid, hu_right] using hformula

/-- Helper for Exercise 6.18: on the right open cell, `example_6_23_pi2` is given by the slope
`-1 / t`. -/
theorem example_6_23_pi2_eq_on_rightOpenCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Ioo (pi2MiddleRightBreakpoint t f) 1) :
    example_6_23_pi2 t f u = (1 - u) / t := by
  -- Strictly past the last breakpoint and still below `1`, only the final branch remains.
  have hu0 : 0 ≤ u := by
    rcases pi2BreakpointOrder ht hft hf with ⟨hleft_pos, hleft_lt_mid, hmid_lt_right, _⟩
    exact le_of_lt (lt_trans (lt_trans (lt_trans hleft_pos hleft_lt_mid) hmid_lt_right) hu.1)
  have hformula := example_6_23_pi2_eq_on_Ico t f u hu0 hu.2
  have hnot_left : ¬ u ≤ 1 - f := by
    have : pi2LeftBreakpoint t f < u := by
      rcases pi2BreakpointOrder ht hft hf with ⟨_, hleft_lt_mid, hmid_lt_right, _⟩
      exact lt_trans (lt_trans hleft_lt_mid hmid_lt_right) hu.1
    simpa [pi2LeftBreakpoint] using not_le.mpr this
  have hnot_mid : ¬ u ≤ 1 - f + t / (2 - f + t) := by
    have : pi2MiddleLeftBreakpoint t f < u := by
      rcases pi2BreakpointOrder ht hft hf with ⟨_, _, hmid_lt_right, _⟩
      exact lt_trans hmid_lt_right hu.1
    simpa [pi2MiddleLeftBreakpoint] using not_le.mpr this
  have hnot_right : ¬ u ≤ 1 - t / (2 - f + t) := by
    simpa [pi2MiddleRightBreakpoint] using not_le.mpr hu.1
  simpa [hnot_left, hnot_mid, hnot_right] using hformula

/-- Helper for Exercise 6.18: `example_6_23_pi2` takes the source-normalized values at the key
distinguished points `0`, `1 - f`, and `1`. -/
theorem example_6_23_pi2_keyValues
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    example_6_23_pi2 t f 0 = 0 ∧
      example_6_23_pi2 t f (pi2LeftBreakpoint t f) = 1 ∧
        example_6_23_pi2 t f 1 = 0 := by
  -- These are the three endpoint values that the later minimality and rigidity proof will reuse.
  have hzero :
      example_6_23_pi2 t f 0 = 0 := by
    simpa using
      example_6_23_pi2_eq_on_leftCell ht hft hf
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f) by
          rcases pi2BreakpointOrder ht hft hf with ⟨hleft_pos, _, _, _⟩
          exact ⟨le_rfl, hleft_pos.le⟩)
  have hleft :
      example_6_23_pi2 t f (pi2LeftBreakpoint t f) = 1 := by
    have hval :=
      example_6_23_pi2_eq_on_leftCell ht hft hf
        (show pi2LeftBreakpoint t f ∈ Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f) by
          rcases pi2BreakpointOrder ht hft hf with ⟨hleft_pos, _, _, _⟩
          exact ⟨hleft_pos.le, le_rfl⟩)
    dsimp [pi2LeftBreakpoint] at hval ⊢
    rcases pi2ParameterFacts ht hft hf with ⟨_, _, h1f, _, _⟩
    field_simp [sub_ne_zero.mpr hf.ne] at hval
    linarith
  have hone :
      example_6_23_pi2 t f 1 = 0 := by
    have hperiodic := example_6_23_pi2_periodic t f
    calc
      example_6_23_pi2 t f 1 = example_6_23_pi2 t f 0 := by simpa using hperiodic 0
      _ = 0 := hzero
  exact ⟨hzero, hleft, hone⟩

/-- Helper for Exercise 6.18: the middle-left breakpoint lies on the common value of the
descending and central affine branches. -/
theorem example_6_23_pi2_value_at_middleLeft
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    example_6_23_pi2 t f (pi2MiddleLeftBreakpoint t f) =
      pi2MiddleLeftBreakpoint t f / (2 - f) := by
  -- Evaluate `π₂` at the right endpoint of the descending cell and rewrite through the branch
  -- match identity.
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  have hβ_formula :
      example_6_23_pi2 t f β = (1 - β + t - f) / t := by
    simpa [α, β] using
      example_6_23_pi2_eq_on_descendingCell ht hft hf
        (show β ∈ Set.Ioc α β by
          rcases pi2BreakpointOrder ht hft hf with ⟨_, hαβ, _, _⟩
          exact ⟨hαβ, le_rfl⟩)
  calc
    example_6_23_pi2 t f (pi2MiddleLeftBreakpoint t f)
        = (1 - β + t - f) / t := by simpa [β] using hβ_formula
    _ = pi2MiddleLeftBreakpoint t f / (2 - f) := by
      simpa [β] using pi2MiddleLeftBreakpoint_branchMatch ht hft hf

/-- Helper for Exercise 6.18: the middle-right breakpoint lies on the common value of the
central and right affine branches. -/
theorem example_6_23_pi2_value_at_middleRight
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    example_6_23_pi2 t f (pi2MiddleRightBreakpoint t f) =
      pi2MiddleRightBreakpoint t f / (2 - f) := by
  -- The central-cell formula already includes the right endpoint of that cell.
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  simpa [β, γ] using
    example_6_23_pi2_eq_on_centralCell ht hft hf
      (show γ ∈ Set.Ioc β γ by
        rcases pi2BreakpointOrder ht hft hf with ⟨_, _, hβγ, _⟩
        exact ⟨hβγ, le_rfl⟩)

/-- Helper for Exercise 6.18: the parameter inequality `1 / 2 + t ≤ f` is equivalent to the
central self-additivity window condition `2 * β ≤ γ`. -/
theorem pi2DoubleMiddleLeft_le_middleRight
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    2 * pi2MiddleLeftBreakpoint t f ≤ pi2MiddleRightBreakpoint t f := by
  -- Clearing the common denominator reduces the breakpoint comparison to the source hypothesis.
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, _, _, hden⟩
  dsimp [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
  field_simp [hden.ne']
  nlinarith

/-- Helper for Exercise 6.18: the two middle breakpoints of `example_6_23_pi2` add up to the
central source width `2 - f`. -/
theorem pi2MiddleBreakpoints_sum
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f = 2 - f := by
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, _, _, hden⟩
  -- Expanding the two breakpoint definitions makes the shared denominator cancel immediately.
  dsimp [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
  field_simp [hden.ne']
  ring

/-- Helper for Exercise 6.18: on the closed central cell, `example_6_23_pi2` is exactly the
affine branch `u ↦ u / (2 - f)`. -/
theorem example_6_23_pi2_eq_on_closedCentralCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f)) :
    example_6_23_pi2 t f u = u / (2 - f) := by
  -- At the left endpoint use the previously computed glued value; every other point lies in the
  -- half-open central cell handled by the branch formula.
  by_cases hu_left : u = pi2MiddleLeftBreakpoint t f
  · subst u
    exact example_6_23_pi2_value_at_middleLeft ht hft hf
  · exact example_6_23_pi2_eq_on_centralCell ht hft hf
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu_left), hu.2⟩

/-- Helper for Exercise 6.18: the periodic extension of `example_6_23_pi2` reduces every input
to its fractional part. -/
theorem example_6_23_pi2_eq_fract
    (t f r : ℝ) :
    example_6_23_pi2 t f r = example_6_23_pi2 t f (Int.fract r) := by
  -- Rewrite the input as an integer translate of its fractional part and remove that translate by
  -- periodicity.
  have hr : r = (Int.floor r : ℝ) + Int.fract r := by
    simpa [add_comm] using (Int.fract_add_floor r).symm
  rw [hr]
  simpa [one_mul, add_comm, add_left_comm, add_assoc] using
    (example_6_23_pi2_periodic t f).int_mul (Int.floor r) (Int.fract r)

/-- Helper for Exercise 6.18: on the fundamental interval `[0, 1)`, the source symmetry
equation for `example_6_23_pi2` holds. -/
theorem example_6_23_pi2_symmetryOnIco
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u) = 1 := by
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  rcases pi2BreakpointOrder ht hft hf with ⟨hα_pos, hαβ, hβγ, hγ_lt_one⟩
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, h1f, h2f, hden⟩
  by_cases hu_left : u ≤ α
  · -- On the left cell, the companion point is `α - u`, which remains on the same cell.
    have hu_formula :
        example_6_23_pi2 t f u = u / (1 - f) := by
      simpa [α] using
        example_6_23_pi2_eq_on_leftCell ht hft hf
          (show u ∈ Set.Icc (0 : ℝ) α by simpa [α] using ⟨hu0, hu_left⟩)
    have hshift :
        example_6_23_pi2 t f (-f - u) = example_6_23_pi2 t f (α - u) := by
      have hper := example_6_23_pi2_periodic t f (-f - u)
      simpa [α, pi2LeftBreakpoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hper.symm
    have hcomp_mem : α - u ∈ Set.Icc (0 : ℝ) α := by
      constructor <;> linarith
    have hcomp_formula :
        example_6_23_pi2 t f (α - u) = (α - u) / (1 - f) := by
      simpa [α] using example_6_23_pi2_eq_on_leftCell ht hft hf hcomp_mem
    calc
      example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
          = u / (1 - f) + (α - u) / (1 - f) := by
              rw [hu_formula, hshift, hcomp_formula]
      _ = 1 := by
        dsimp [α, pi2LeftBreakpoint]
        field_simp [sub_ne_zero.mpr hf.ne]
        ring
  · have hu_left' : α < u := lt_of_not_ge hu_left
    by_cases hu_desc : u ≤ β
    · -- On the descending cell, the companion point is `2 - f - u`, which lands on the final
      -- right branch or its shared breakpoint with the central cell.
      have hu_formula :
          example_6_23_pi2 t f u = (1 - u + t - f) / t := by
        simpa [α, β] using
          example_6_23_pi2_eq_on_descendingCell ht hft hf
            (show u ∈ Set.Ioc α β by simpa [α, β] using ⟨hu_left', hu_desc⟩)
      have hshift₁ :
          example_6_23_pi2 t f (-f - u) = example_6_23_pi2 t f (α - u) := by
        have hper := example_6_23_pi2_periodic t f (-f - u)
        simpa [α, pi2LeftBreakpoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          hper.symm
      have hshift₂ :
          example_6_23_pi2 t f (α - u) = example_6_23_pi2 t f (1 + α - u) := by
        have hper := example_6_23_pi2_periodic t f (α - u)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
      by_cases hu_atβ : u = β
      · have hcomp_eq : 1 + α - u = γ := by
          rw [hu_atβ]
          dsimp [α, β, γ, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
          field_simp [hden.ne']
          ring
        have hcomp_formula :
            example_6_23_pi2 t f (1 + α - u) = (1 + α - u) / (2 - f) := by
          rw [hcomp_eq]
          simpa [β, γ] using
            example_6_23_pi2_eq_on_centralCell ht hft hf
              (show γ ∈ Set.Ioc β γ by exact ⟨hβγ, le_rfl⟩)
        calc
          example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
              = (1 - u + t - f) / t + (1 + α - u) / (2 - f) := by
                  rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
          _ = 1 := by
            rw [hu_atβ]
            dsimp [α, β, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint]
            field_simp [ht.ne', h2f.ne', hden.ne']
            ring
      · have hu_ltβ : u < β := lt_of_le_of_ne hu_desc hu_atβ
        have hcomp0 : γ < 1 + α - u := by
          dsimp [α, β, γ, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at *
          linarith
        have hcomp1 : 1 + α - u < 1 := by
          linarith
        have hcomp_formula :
            example_6_23_pi2 t f (1 + α - u) = (1 - (1 + α - u)) / t := by
          simpa [γ] using
            example_6_23_pi2_eq_on_rightOpenCell ht hft hf
              (show 1 + α - u ∈ Set.Ioo γ 1 by simpa [γ] using ⟨hcomp0, hcomp1⟩)
        calc
          example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
              = (1 - u + t - f) / t + (1 - (1 + α - u)) / t := by
                  rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
          _ = 1 := by
            dsimp [α, pi2LeftBreakpoint]
            field_simp [ht.ne']
            ring
    · have hu_desc' : β < u := lt_of_not_ge hu_desc
      by_cases hu_central : u ≤ γ
      · -- The central cell is stable under the companion map `u ↦ 2 - f - u`.
        have hu_formula :
            example_6_23_pi2 t f u = u / (2 - f) := by
          simpa [β, γ] using
            example_6_23_pi2_eq_on_centralCell ht hft hf
              (show u ∈ Set.Ioc β γ by simpa [β, γ] using ⟨hu_desc', hu_central⟩)
        have hshift₁ :
            example_6_23_pi2 t f (-f - u) = example_6_23_pi2 t f (α - u) := by
          have hper := example_6_23_pi2_periodic t f (-f - u)
          simpa [α, pi2LeftBreakpoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hper.symm
        have hshift₂ :
            example_6_23_pi2 t f (α - u) = example_6_23_pi2 t f (1 + α - u) := by
          have hper := example_6_23_pi2_periodic t f (α - u)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
        by_cases hu_atγ : u = γ
        · have hcomp_eq : 1 + α - u = β := by
            rw [hu_atγ]
            dsimp [α, β, γ, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
            field_simp [hden.ne']
            ring
          have hcomp_formula :
              example_6_23_pi2 t f (1 + α - u) = (1 - (1 + α - u) + t - f) / t := by
            rw [hcomp_eq]
            simpa [α, β] using
              example_6_23_pi2_eq_on_descendingCell ht hft hf
                (show β ∈ Set.Ioc α β by exact ⟨hαβ, le_rfl⟩)
          calc
            example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
                = u / (2 - f) + (1 - (1 + α - u) + t - f) / t := by
                    rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
            _ = 1 := by
              rw [hu_atγ]
              dsimp [α, γ, pi2LeftBreakpoint, pi2MiddleRightBreakpoint]
              field_simp [ht.ne', h2f.ne', hden.ne']
              ring
        · have hu_ltγ : u < γ := lt_of_le_of_ne hu_central hu_atγ
          have hcomp_mem : 1 + α - u ∈ Set.Ioc β γ := by
            dsimp [α, β, γ, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at *
            constructor <;> linarith
          have hcomp_formula :
              example_6_23_pi2 t f (1 + α - u) = (1 + α - u) / (2 - f) := by
            simpa [β, γ] using example_6_23_pi2_eq_on_centralCell ht hft hf hcomp_mem
          calc
            example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
                = u / (2 - f) + (1 + α - u) / (2 - f) := by
                    rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
            _ = 1 := by
              dsimp [α, pi2LeftBreakpoint]
              field_simp [h2f.ne']
              ring
      · -- On the right cell, the companion point moves to the descending cell.
        have hu_formula :
            example_6_23_pi2 t f u = (1 - u) / t := by
          simpa [γ] using
            example_6_23_pi2_eq_on_rightOpenCell ht hft hf
              (show u ∈ Set.Ioo γ 1 by simpa [γ] using ⟨lt_of_not_ge hu_central, hu1⟩)
        have hshift₁ :
            example_6_23_pi2 t f (-f - u) = example_6_23_pi2 t f (α - u) := by
          have hper := example_6_23_pi2_periodic t f (-f - u)
          simpa [α, pi2LeftBreakpoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hper.symm
        have hshift₂ :
            example_6_23_pi2 t f (α - u) = example_6_23_pi2 t f (1 + α - u) := by
          have hper := example_6_23_pi2_periodic t f (α - u)
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
        have hcomp_mem : 1 + α - u ∈ Set.Ioc α β := by
          dsimp [α, β, γ, pi2LeftBreakpoint, pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at *
          constructor <;> linarith
        have hcomp_formula :
            example_6_23_pi2 t f (1 + α - u) = (1 - (1 + α - u) + t - f) / t := by
          simpa [α, β] using example_6_23_pi2_eq_on_descendingCell ht hft hf hcomp_mem
        calc
          example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u)
              = (1 - u) / t + (1 - (1 + α - u) + t - f) / t := by
                  rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
          _ = 1 := by
            dsimp [α, pi2LeftBreakpoint]
            field_simp [ht.ne']
            ring

/-- Helper for Exercise 6.18: the source symmetry equation extends from `[0, 1)` to all real
arguments by `1`-periodicity. -/
theorem example_6_23_pi2_symmetryReal
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ∀ r : ℝ, example_6_23_pi2 t f r + example_6_23_pi2 t f (-f - r) = 1 := by
  intro r
  let u : ℝ := Int.fract r
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Int.fract_nonneg r
  have hu1 : u < 1 := by
    dsimp [u]
    exact Int.fract_lt_one r
  have hr :
      example_6_23_pi2 t f r = example_6_23_pi2 t f u := by
    simpa [u] using example_6_23_pi2_eq_fract t f r
  have hcomp :
      example_6_23_pi2 t f (-f - r) = example_6_23_pi2 t f (-f - u) := by
    have hper := (example_6_23_pi2_periodic t f).int_mul (-Int.floor r) (-f - u)
    have hrewrite : (-Int.floor r : ℝ) + (-f - u) = -f - r := by
      dsimp [u]
      have hr' : r = Int.fract r + (Int.floor r : ℝ) := by
        simpa [add_comm] using (Int.fract_add_floor r).symm
      linarith
    calc
      example_6_23_pi2 t f (-f - r) = example_6_23_pi2 t f ((-Int.floor r : ℝ) + (-f - u)) := by
        rw [hrewrite]
      _ = example_6_23_pi2 t f (-f - u) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using hper
  calc
    example_6_23_pi2 t f r + example_6_23_pi2 t f (-f - r)
        = example_6_23_pi2 t f u + example_6_23_pi2 t f (-f - u) := by rw [hr, hcomp]
    _ = 1 := example_6_23_pi2_symmetryOnIco ht hft hf hu0 hu1

/-- Helper for Exercise 6.18: the source unit-interval formula for `π₂`, written with the
exercise-owned breakpoint names. -/
noncomputable abbrev example_6_23_pi2Raw (t f : ℝ) : ℝ → ℝ :=
  fun u ↦
    if u ≤ pi2LeftBreakpoint t f then
      u / (1 - f)
    else if u ≤ pi2MiddleLeftBreakpoint t f then
      (1 - u + t - f) / t
    else if u ≤ pi2MiddleRightBreakpoint t f then
      u / (2 - f)
    else
      (1 - u) / t

/-- Helper for Exercise 6.18: the raw unit-interval formula for `π₂` is globally continuous
because the adjacent affine branches match at each breakpoint. -/
theorem example_6_23_pi2Raw_continuous
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    Continuous (example_6_23_pi2Raw t f) := by
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  let g₁ : ℝ → ℝ := fun u ↦ u / (1 - f)
  let g₂ : ℝ → ℝ := fun u ↦ (1 - u + t - f) / t
  let g₃ : ℝ → ℝ := fun u ↦ u / (2 - f)
  let g₄ : ℝ → ℝ := fun u ↦ (1 - u) / t
  have hg₁ : Continuous g₁ := by
    fun_prop
  have hg₂ : Continuous g₂ := by
    fun_prop
  have hg₃ : Continuous g₃ := by
    fun_prop
  have hg₄ : Continuous g₄ := by
    fun_prop
  have h34 : Continuous (fun u : ℝ ↦ if u ≤ γ then g₃ u else g₄ u) := by
    -- The central and right affine models glue at `γ`.
    refine Continuous.if_le hg₃ hg₄ continuous_id continuous_const ?_
    intro u hu
    have huγ : u = γ := by
      simpa [γ] using hu
    subst huγ
    simpa [g₃, g₄, γ] using pi2MiddleRightBreakpoint_branchMatch ht hft hf
  have h23 :
      Continuous (fun u : ℝ ↦ if u ≤ β then g₂ u else if u ≤ γ then g₃ u else g₄ u) := by
    -- The descending and central affine models glue at `β`.
    refine Continuous.if_le hg₂ h34 continuous_id continuous_const ?_
    intro u hu
    have huβ : u = β := by
      simpa [β] using hu
    subst huβ
    have hβγ : β ≤ γ := (pi2BreakpointOrder ht hft hf).2.2.1.le
    simp [g₂, g₃, β, γ, hβγ, pi2MiddleLeftBreakpoint_branchMatch ht hft hf]
  -- The left and descending affine models glue at `α`.
  refine Continuous.if_le hg₁ h23 continuous_id continuous_const ?_
  intro u hu
  have huα : u = α := by
    simpa [α] using hu
  subst huα
  have hαβ : α ≤ β := (pi2BreakpointOrder ht hft hf).2.1.le
  simp [example_6_23_pi2Raw, g₁, g₂, α, β, hαβ, pi2LeftBreakpoint_branchMatch ht hft hf]

/-- Helper for Exercise 6.18: the raw unit-interval formula for `π₂` takes the expected endpoint
values `0` and `0`. -/
theorem example_6_23_pi2Raw_endpoints
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    example_6_23_pi2Raw t f 0 = 0 ∧ example_6_23_pi2Raw t f 1 = 0 := by
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  rcases pi2BreakpointOrder ht hft hf with ⟨hα_pos, hαβ, hβγ, hγ_lt_one⟩
  have hzero : example_6_23_pi2Raw t f 0 = 0 := by
    -- At `0`, the first affine branch is active.
    simp [example_6_23_pi2Raw, α, hα_pos.le]
  have h1α : ¬ (1 : ℝ) ≤ α := by
    exact not_le.mpr (lt_trans hαβ (lt_trans hβγ hγ_lt_one))
  have h1β : ¬ (1 : ℝ) ≤ β := by
    exact not_le.mpr (lt_trans hβγ hγ_lt_one)
  have h1γ : ¬ (1 : ℝ) ≤ γ := by
    exact not_le.mpr hγ_lt_one
  have hone : example_6_23_pi2Raw t f 1 = 0 := by
    -- At `1`, the last affine branch is active and vanishes.
    simp [example_6_23_pi2Raw, α, β, γ, h1α, h1β, h1γ]
  exact ⟨hzero, hone⟩

/-- Helper for Exercise 6.18: the `1`-periodic extension of the raw unit-interval formula is
exactly `example_6_23_pi2`. -/
theorem example_6_23_pi2_eq_raw_fract
    (t f r : ℝ) :
    example_6_23_pi2 t f r = example_6_23_pi2Raw t f (Int.fract r) := by
  -- This is just the imported `Int.fract` formula rewritten through the exercise-local owner.
  simpa [example_6_23_pi2Raw] using example_6_23_pi2_apply t f r

/-- Helper for Exercise 6.18: `π₂` is continuous because its raw unit-interval formula glues at
`0` and `1`, so the periodic extension through `Int.fract` is continuous. -/
theorem example_6_23_pi2_continuous
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    Continuous (example_6_23_pi2 t f) := by
  -- The raw formula is continuous on the unit interval and its endpoint values agree, so
  -- composition with fractional part gives a continuous periodic extension.
  have hendpoints := example_6_23_pi2Raw_endpoints ht hft hf
  have hraw : ContinuousOn (example_6_23_pi2Raw t f) (Set.Icc (0 : ℝ) 1) :=
    (example_6_23_pi2Raw_continuous ht hft hf).continuousOn
  have hcomp : Continuous (example_6_23_pi2Raw t f ∘ Int.fract) :=
    hraw.comp_fract'' (hendpoints.1.trans hendpoints.2.symm)
  have heq : example_6_23_pi2 t f = example_6_23_pi2Raw t f ∘ Int.fract := by
    funext r
    exact example_6_23_pi2_eq_raw_fract t f r
  rw [heq]
  exact hcomp

/-- Helper for Exercise 6.18: `π₂` is nonnegative on `ℝ`, which is one of the hypotheses needed
for the Exercise 6.17 breakpoint criterion. -/
theorem example_6_23_pi2_nonneg
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ∀ r : ℝ, 0 ≤ example_6_23_pi2 t f r := by
  intro r
  let u : ℝ := Int.fract r
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  have hu0 : 0 ≤ u := by
    simpa [u] using Int.fract_nonneg r
  have hu1 : u < 1 := by
    simpa [u] using Int.fract_lt_one r
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, h1f, h2f, _⟩
  rcases pi2BreakpointOrder ht hft hf with ⟨hα_pos, hαβ, hβγ, _⟩
  rw [example_6_23_pi2_eq_fract t f r]
  by_cases huα : u ≤ α
  · -- The left branch is a quotient of nonnegative quantities.
    rw [example_6_23_pi2_eq_on_leftCell ht hft hf
      (show u ∈ Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f) by
        simpa [α] using ⟨hu0, huα⟩)]
    exact div_nonneg hu0 h1f.le
  · by_cases huβ : u ≤ β
    · -- The descending numerator is bounded below by its positive value at `β`.
      have hβ_pos : 0 < β := lt_trans hα_pos hαβ
      have hquot_pos : 0 < (1 - β + t - f) / t := by
        have hmatch := pi2MiddleLeftBreakpoint_branchMatch ht hft hf
        rw [show (1 - β + t - f) / t = β / (2 - f) by simpa [β] using hmatch]
        exact div_pos hβ_pos h2f
      have hnum_pos : 0 < 1 - β + t - f := by
        rcases (div_pos_iff.mp hquot_pos) with hpos | hneg
        · exact hpos.1
        · exact (not_lt_of_ge ht.le hneg.2).elim
      rw [example_6_23_pi2_eq_on_descendingCell ht hft hf
        (show u ∈ Set.Ioc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f) by
          simpa [α, β] using ⟨lt_of_not_ge huα, huβ⟩)]
      exact div_nonneg (by linarith) ht.le
    · by_cases huγ : u ≤ γ
      · -- The central branch has positive denominator.
        rw [example_6_23_pi2_eq_on_centralCell ht hft hf
          (show u ∈ Set.Ioc (pi2MiddleLeftBreakpoint t f)
              (pi2MiddleRightBreakpoint t f) by
            simpa [β, γ] using ⟨lt_of_not_ge huβ, huγ⟩)]
        exact div_nonneg hu0 h2f.le
      · -- On the final branch, `u < 1` makes the numerator nonnegative.
        rw [example_6_23_pi2_eq_on_rightOpenCell ht hft hf
          (show u ∈ Set.Ioo (pi2MiddleRightBreakpoint t f) 1 by
            simpa [γ] using ⟨lt_of_not_ge huγ, hu1⟩)]
        exact div_nonneg (sub_nonneg.mpr hu1.le) ht.le

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the descending affine
formula extends to both endpoints of its cell. -/
theorem example_6_23_pi2_eq_on_closedDescendingCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Icc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f)) :
    example_6_23_pi2 t f u = (1 - u + t - f) / t := by
  -- Away from the left endpoint, the existing half-open branch formula applies directly.
  by_cases hu_left : u = pi2LeftBreakpoint t f
  · subst u
    calc
      example_6_23_pi2 t f (pi2LeftBreakpoint t f) =
          pi2LeftBreakpoint t f / (1 - f) :=
        example_6_23_pi2_eq_on_leftCell ht hft hf
          ⟨(pi2BreakpointOrder ht hft hf).1.le, le_rfl⟩
      _ = (1 - pi2LeftBreakpoint t f + t - f) / t :=
        pi2LeftBreakpoint_branchMatch ht hft hf
  · exact example_6_23_pi2_eq_on_descendingCell ht hft hf
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu_left), hu.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the final affine formula
extends to the closed right cell. -/
theorem example_6_23_pi2_eq_on_closedRightCell
    {t f u : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu : u ∈ Set.Icc (pi2MiddleRightBreakpoint t f) 1) :
    example_6_23_pi2 t f u = (1 - u) / t := by
  -- The shared breakpoint and periodic endpoint are handled by their named value formulas.
  by_cases hu_left : u = pi2MiddleRightBreakpoint t f
  · subst u
    calc
      example_6_23_pi2 t f (pi2MiddleRightBreakpoint t f) =
          pi2MiddleRightBreakpoint t f / (2 - f) :=
        example_6_23_pi2_value_at_middleRight ht hft hf
      _ = (1 - pi2MiddleRightBreakpoint t f) / t :=
        pi2MiddleRightBreakpoint_branchMatch ht hft hf
  · by_cases hu_right : u = 1
    · subst u
      simpa using (example_6_23_pi2_keyValues ht hft hf).2.2
    · exact example_6_23_pi2_eq_on_rightOpenCell ht hft hf
        ⟨lt_of_le_of_ne hu.1 (Ne.symm hu_left), lt_of_le_of_ne hu.2 hu_right⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the four explicit cells
have ordered endpoints. -/
theorem pi2PiecewiseLowerLeUpper
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ∀ j : Fin 4,
      (![(0 : ℝ), pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
          pi2MiddleRightBreakpoint t f] : Fin 4 → ℝ) j ≤
        (![pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
          pi2MiddleRightBreakpoint t f, (1 : ℝ)] : Fin 4 → ℝ) j := by
  -- Each finite case is one adjacent inequality from the breakpoint ordering.
  intro j
  rcases pi2BreakpointOrder ht hft hf with ⟨h0, h01, h12, h23⟩
  fin_cases j <;> simp <;> linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the four consecutive cells
cover the unit interval. -/
theorem pi2PiecewiseCover
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    Set.Icc (0 : ℝ) 1 ⊆
      ⋃ j : Fin 4,
        Set.Icc
          ((![(0 : ℝ), pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
              pi2MiddleRightBreakpoint t f] : Fin 4 → ℝ) j)
          ((![pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
              pi2MiddleRightBreakpoint t f, (1 : ℝ)] : Fin 4 → ℝ) j) := by
  intro x hx
  -- Choose the first cell whose upper endpoint contains `x`.
  by_cases hα : x ≤ pi2LeftBreakpoint t f
  · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    simpa using ⟨hx.1, hα⟩
  by_cases hβ : x ≤ pi2MiddleLeftBreakpoint t f
  · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    have hαx : pi2LeftBreakpoint t f ≤ x := (lt_of_not_ge hα).le
    change pi2LeftBreakpoint t f ≤ x ∧ x ≤ pi2MiddleLeftBreakpoint t f
    exact ⟨hαx, hβ⟩
  by_cases hγ : x ≤ pi2MiddleRightBreakpoint t f
  · refine Set.mem_iUnion.mpr ⟨2, ?_⟩
    simpa using ⟨le_of_not_ge hβ, hγ⟩
  · refine Set.mem_iUnion.mpr ⟨3, ?_⟩
    have hγx : pi2MiddleRightBreakpoint t f ≤ x := (lt_of_not_ge hγ).le
    change pi2MiddleRightBreakpoint t f ≤ x ∧ x ≤ 1
    exact ⟨hγx, hx.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: on each explicit cell,
`example_6_23_pi2` agrees with the recorded affine formula. -/
theorem pi2PiecewiseEqAffine
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ∀ (j : Fin 4) (x : ℝ),
      x ∈ Set.Icc
          ((![(0 : ℝ), pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
              pi2MiddleRightBreakpoint t f] : Fin 4 → ℝ) j)
          ((![pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
              pi2MiddleRightBreakpoint t f, (1 : ℝ)] : Fin 4 → ℝ) j) →
        example_6_23_pi2 t f x =
          (![(1 / (1 - f) : ℝ), -1 / t, 1 / (2 - f), -1 / t] : Fin 4 → ℝ) j * x +
            (![(0 : ℝ), (1 + t - f) / t, (0 : ℝ), 1 / t] : Fin 4 → ℝ) j := by
  intro j x hx
  -- Reduce the finite witness to the four already certified closed-cell formulas.
  fin_cases j
  · change x ∈ Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f) at hx
    simp at ⊢
    simpa [div_eq_mul_inv, mul_comm] using example_6_23_pi2_eq_on_leftCell ht hft hf hx
  · change x ∈ Set.Icc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f) at hx
    simp at ⊢
    rw [example_6_23_pi2_eq_on_closedDescendingCell ht hft hf hx]
    ring
  · change x ∈ Set.Icc (pi2MiddleLeftBreakpoint t f)
        (pi2MiddleRightBreakpoint t f) at hx
    simp at ⊢
    simpa [div_eq_mul_inv, mul_comm] using
      example_6_23_pi2_eq_on_closedCentralCell ht hft hf hx
  · change x ∈ Set.Icc (pi2MiddleRightBreakpoint t f) 1 at hx
    simp at ⊢
    rw [example_6_23_pi2_eq_on_closedRightCell ht hft hf hx]
    ring

/-- Helper for Exercise 6.18: the imported Exercise 6.17 breakpoint criterion is driven by the
explicit four-cell piecewise-linear witness for `π₂` on `[0, 1]`. -/
noncomputable abbrev example_6_23_pi2PiecewiseOnUnitInterval
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    PiecewiseLinearOnInterval 0 1 (example_6_23_pi2 t f) :=
  { pieces := 4
    lower := ![(0 : ℝ), pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
      pi2MiddleRightBreakpoint t f]
    upper := ![pi2LeftBreakpoint t f, pi2MiddleLeftBreakpoint t f,
      pi2MiddleRightBreakpoint t f, (1 : ℝ)]
    slope := ![1 / (1 - f), -1 / t, 1 / (2 - f), -1 / t]
    intercept := ![(0 : ℝ), (1 + t - f) / t, (0 : ℝ), 1 / t]
    lower_le_upper := pi2PiecewiseLowerLeUpper ht hft hf
    cover := pi2PiecewiseCover ht hft hf
    eq_affine := pi2PiecewiseEqAffine ht hft hf }

/-- Helper for Exercise 6.18: every breakpoint of the explicit four-cell witness is one of the
five source points `0`, `α`, `β`, `γ`, or `1`. -/
theorem example_6_23_pi2_breakpoint_cases
    {t f x : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hx : x ∈ (example_6_23_pi2PiecewiseOnUnitInterval ht hft hf).breakpoints) :
    x = 0 ∨ x = pi2LeftBreakpoint t f ∨ x = pi2MiddleLeftBreakpoint t f ∨
      x = pi2MiddleRightBreakpoint t f ∨ x = 1 := by
  classical
  -- Unfold the finite endpoint set and read off the five possible values.
  simp only [example_6_23_pi2PiecewiseOnUnitInterval,
    PiecewiseLinearOnInterval.breakpoints, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx.1 with ⟨j, hj⟩ | ⟨j, hj⟩
  · fin_cases j
    · have hx0 : x = 0 := by simpa using hj.symm
      exact Or.inl hx0
    · have hxα : x = pi2LeftBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inl hxα)
    · have hxβ : x = pi2MiddleLeftBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inr (Or.inl hxβ))
    · have hxγ : x = pi2MiddleRightBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inr (Or.inr (Or.inl hxγ)))
  · fin_cases j
    · have hxα : x = pi2LeftBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inl hxα)
    · have hxβ : x = pi2MiddleLeftBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inr (Or.inl hxβ))
    · have hxγ : x = pi2MiddleRightBreakpoint t f := by simpa using hj.symm
      exact Or.inr (Or.inr (Or.inr (Or.inl hxγ)))
    · have hx1 : x = 1 := by simpa using hj.symm
      exact Or.inr (Or.inr (Or.inr (Or.inr hx1)))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: a strict downward jump between
two adjacent affine slopes prevents local convexity at their common endpoint. -/
theorem notLocallyConvexAt_of_affineSlopeDrop
    {g : ℝ → ℝ} {a x b mLeft mRight cLeft cRight : ℝ}
    (hax : a < x) (hxb : x < b)
    (hleft : Set.EqOn g (fun r ↦ mLeft * r + cLeft) (Set.Icc a x))
    (hright : Set.EqOn g (fun r ↦ mRight * r + cRight) (Set.Icc x b))
    (hdrop : mRight < mLeft) :
    ¬ LocallyConvexAt g x := by
  intro hlocal
  rcases hlocal with ⟨s, hs_nhds, _hs_convex, hs⟩
  rcases Metric.mem_nhds_iff.mp hs_nhds with ⟨ε, hε, hball⟩
  let δ : ℝ := min (ε / 2) (min ((x - a) / 2) ((b - x) / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le_ε : δ < ε := by
    have hle : δ ≤ ε / 2 := min_le_left _ _
    linarith
  have hδ_le_left : δ ≤ (x - a) / 2 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_right : δ ≤ (b - x) / 2 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hleft_mem : x - δ ∈ s := by
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq]
    rw [show x - δ - x = -δ by ring, abs_neg, abs_of_pos hδ]
    exact hδ_le_ε
  have hright_mem : x + δ ∈ s := by
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq]
    rw [show x + δ - x = δ by ring, abs_of_pos hδ]
    exact hδ_le_ε
  have hleft_cell : x - δ ∈ Set.Icc a x := by
    constructor <;> linarith
  have hx_left : x ∈ Set.Icc a x := ⟨hax.le, le_rfl⟩
  have hx_right : x ∈ Set.Icc x b := ⟨le_rfl, hxb.le⟩
  have hright_cell : x + δ ∈ Set.Icc x b := by
    constructor <;> linarith
  have hmeet : mLeft * x + cLeft = mRight * x + cRight := by
    calc
      mLeft * x + cLeft = g x := (hleft hx_left).symm
      _ = mRight * x + cRight := hright hx_right
  have hleft_lt : x - δ < x := by linarith
  have hright_lt : x < x + δ := by linarith
  have hmono :=
    hs.slope_mono_adjacent (y := x) hleft_mem hright_mem hleft_lt hright_lt
  rw [hleft hleft_cell, hleft hx_left, hright hright_cell] at hmono
  have hδ_ne : δ ≠ 0 := hδ.ne'
  have hslope_left :
      (mLeft * x + cLeft - (mLeft * (x - δ) + cLeft)) / (x - (x - δ)) =
        mLeft := by
    field_simp [hδ_ne]
    ring
  have hslope_right :
      (mRight * (x + δ) + cRight - (mLeft * x + cLeft)) / (x + δ - x) =
        mRight := by
    rw [hmeet]
    field_simp [hδ_ne]
    ring
  rw [hslope_left, hslope_right] at hmono
  exact (not_le_of_gt hdrop hmono).elim

/-- Helper for Exercise 6.18: the left breakpoint `α` is a downward corner, so `π₂` cannot be
locally convex there. -/
theorem example_6_23_pi2_not_locallyConvexAt_leftBreakpoint
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ¬ LocallyConvexAt (example_6_23_pi2 t f) (pi2LeftBreakpoint t f) := by
  rcases pi2BreakpointOrder ht hft hf with ⟨h0α, hαβ, _, _⟩
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, h1f, _, _⟩
  -- The left positive slope is followed by the strictly negative descending slope.
  refine notLocallyConvexAt_of_affineSlopeDrop
    (mLeft := 1 / (1 - f)) (mRight := -1 / t)
    (cLeft := 0) (cRight := (1 + t - f) / t) h0α hαβ ?_ ?_ ?_
  · intro x hx
    rw [example_6_23_pi2_eq_on_leftCell ht hft hf hx]
    ring
  · intro x hx
    rw [example_6_23_pi2_eq_on_closedDescendingCell ht hft hf hx]
    ring
  · have hleftSlope : 0 < (1 / (1 - f) : ℝ) := one_div_pos.mpr h1f
    have ht_inv : 0 < (1 / t : ℝ) := one_div_pos.mpr ht
    have hrightSlope : (-1 / t : ℝ) < 0 := by
      calc
        (-1 / t : ℝ) = -(1 / t) := by ring
        _ < 0 := neg_lt_zero.mpr ht_inv
    linarith

/-- Helper for Exercise 6.18: the right breakpoint `γ` is also a downward corner, so `π₂`
cannot be locally convex there. -/
theorem example_6_23_pi2_not_locallyConvexAt_middleRightBreakpoint
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    ¬ LocallyConvexAt (example_6_23_pi2 t f) (pi2MiddleRightBreakpoint t f) := by
  rcases pi2BreakpointOrder ht hft hf with ⟨_, _, hβγ, hγ1⟩
  rcases pi2ParameterFacts ht hft hf with ⟨_, _, _, h2f, _⟩
  -- The positive central slope is followed by the strictly negative final slope.
  refine notLocallyConvexAt_of_affineSlopeDrop
    (mLeft := 1 / (2 - f)) (mRight := -1 / t)
    (cLeft := 0) (cRight := 1 / t) hβγ hγ1 ?_ ?_ ?_
  · intro x hx
    rw [example_6_23_pi2_eq_on_closedCentralCell ht hft hf hx]
    ring
  · intro x hx
    rw [example_6_23_pi2_eq_on_closedRightCell ht hft hf hx]
    ring
  · have hleftSlope : 0 < (1 / (2 - f) : ℝ) := one_div_pos.mpr h2f
    have ht_inv : 0 < (1 / t : ℝ) := one_div_pos.mpr ht
    have hrightSlope : (-1 / t : ℝ) < 0 := by
      calc
        (-1 / t : ℝ) = -(1 / t) := by ring
        _ < 0 := neg_lt_zero.mpr ht_inv
    linarith

/-- Helper for Exercise 6.18: among the source breakpoints, local convexity can only occur at
the endpoints `0`, `1`, or the middle-left breakpoint `β`. -/
theorem example_6_23_pi2_locallyConvexBreakpoint_cases
    {t f x : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hx : Exercise617Breakpoint (example_6_23_pi2 t f) x)
    (hconv : LocallyConvexAt (example_6_23_pi2 t f) x) :
    x = 0 ∨ x = 1 ∨ x = pi2MiddleLeftBreakpoint t f := by
  -- Every source-facing breakpoint occurs in the explicit witness; discard the two downward
  -- corners by their nonconvexity certificates.
  have hx_checkpoint :=
    exercise617Breakpoint_mem_breakpointCheckpoints
      (hpiece := example_6_23_pi2PiecewiseOnUnitInterval ht hft hf) hx
  have hx_cases :
      x = 0 ∨ x = 1 ∨
        x ∈ (example_6_23_pi2PiecewiseOnUnitInterval ht hft hf).breakpoints := by
    simpa [breakpointCheckpoints] using hx_checkpoint
  rcases hx_cases with hx0 | hx1 | hxraw
  · exact Or.inl hx0
  · exact Or.inr (Or.inl hx1)
  · rcases example_6_23_pi2_breakpoint_cases ht hft hf hxraw with
      hx0 | hxα | hxβ | hxγ | hx1
    · exact Or.inl hx0
    · subst x
      exact (example_6_23_pi2_not_locallyConvexAt_leftBreakpoint ht hft hf hconv).elim
    · exact Or.inr (Or.inr hxβ)
    · subst x
      exact
        (example_6_23_pi2_not_locallyConvexAt_middleRightBreakpoint ht hft hf hconv).elim
    · exact Or.inr (Or.inl hx1)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: subadditivity holds at every
pair of source-facing breakpoints where the source function is locally convex. -/
theorem example_6_23_pi2_subadditiveAtLocallyConvexBreakpoints
    {t f a b : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (ha : Exercise617Breakpoint (example_6_23_pi2 t f) a)
    (hb : Exercise617Breakpoint (example_6_23_pi2 t f) b)
    (hconv_a : LocallyConvexAt (example_6_23_pi2 t f) a)
    (hconv_b : LocallyConvexAt (example_6_23_pi2 t f) b) :
    example_6_23_pi2 t f (a + b) ≤
      example_6_23_pi2 t f a + example_6_23_pi2 t f b := by
  have hzero := (example_6_23_pi2_keyValues ht hft hf).1
  have hone := (example_6_23_pi2_keyValues ht hft hf).2.2
  have hperiodic := example_6_23_pi2_periodic t f
  rcases example_6_23_pi2_locallyConvexBreakpoint_cases ht hft hf ha hconv_a with
    rfl | rfl | rfl
  · simpa [hzero]
  · rcases example_6_23_pi2_locallyConvexBreakpoint_cases ht hft hf hb hconv_b with
      rfl | rfl | rfl
    · simpa [hzero] using le_of_eq (hperiodic 0)
    · simpa [hone] using le_of_eq (hperiodic 1)
    · simpa [add_comm, hone] using
        le_of_eq (hperiodic (pi2MiddleLeftBreakpoint t f))
  · rcases example_6_23_pi2_locallyConvexBreakpoint_cases ht hft hf hb hconv_b with
      rfl | rfl | rfl
    · simpa [hzero]
    · simpa [hone] using le_of_eq (hperiodic (pi2MiddleLeftBreakpoint t f))
    · have hβγ := pi2DoubleMiddleLeft_le_middleRight ht hft hf
      have hβ_nonneg : 0 ≤ pi2MiddleLeftBreakpoint t f :=
        (pi2BreakpointOrder ht hft hf).1.le.trans
          (pi2BreakpointOrder ht hft hf).2.1.le
      have hβ_mem :
          pi2MiddleLeftBreakpoint t f ∈
            Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) :=
        ⟨le_rfl, (pi2BreakpointOrder ht hft hf).2.2.1.le⟩
      have h2β_mem :
          pi2MiddleLeftBreakpoint t f + pi2MiddleLeftBreakpoint t f ∈
            Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
        constructor
        · linarith
        · simpa [two_mul] using hβγ
      rw [example_6_23_pi2_eq_on_closedCentralCell ht hft hf h2β_mem,
        example_6_23_pi2_eq_on_closedCentralCell ht hft hf hβ_mem]
      ring_nf
      exact le_rfl

/-- Helper for Exercise 6.18: the global breakpoint criterion from Exercise 6.17 reduces
subadditivity of `π₂` on `[0, 1)²` to the endpoint cases and the single central check
`(β, β)`. -/
theorem example_6_23_pi2_subadditiveOnIco
    {t f u v : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    example_6_23_pi2 t f (u + v) ≤ example_6_23_pi2 t f u + example_6_23_pi2 t f v := by
  -- Exercise 6.17 converts the finite locally-convex breakpoint check into global
  -- subadditivity; specialize that conclusion to `u` and `v`.
  have hsub : Function.Subadditive (example_6_23_pi2 t f) :=
    exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
      (example_6_23_pi2_periodic t f) (example_6_23_pi2_continuous ht hft hf)
      (example_6_23_pi2_nonneg ht hft hf) (example_6_23_pi2_keyValues ht hft hf).1
      (example_6_23_pi2PiecewiseOnUnitInterval ht hft hf)
      (example_6_23_pi2_symmetryReal ht hft hf)
      (fun {a b} ha hb hconv_a hconv_b ↦
        example_6_23_pi2_subadditiveAtLocallyConvexBreakpoints
          ht hft hf ha hb hconv_a hconv_b)
  exact hsub u v

/-- Helper for Exercise 6.18: once subadditivity is proved on `[0, 1) × [0, 1)`, the periodic
extension gives global subadditivity on `ℝ`. -/
theorem example_6_23_pi2_subadditive
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    Function.Subadditive (example_6_23_pi2 t f) := by
  intro r s
  let u : ℝ := Int.fract r
  let v : ℝ := Int.fract s
  have hu0 : 0 ≤ u := by simpa [u] using Int.fract_nonneg r
  have hu1 : u < 1 := by simpa [u] using Int.fract_lt_one r
  have hv0 : 0 ≤ v := by simpa [v] using Int.fract_nonneg s
  have hv1 : v < 1 := by simpa [v] using Int.fract_lt_one s
  have hsum :
      example_6_23_pi2 t f (r + s) = example_6_23_pi2 t f (u + v) := by
    have hper :=
      (example_6_23_pi2_periodic t f).int_mul
        (Int.floor r + Int.floor s) (u + v)
    have hrewrite :
        ((Int.floor r + Int.floor s : ℤ) : ℝ) * 1 + (u + v) = r + s := by
      dsimp [u, v]
      rw [Int.cast_add, mul_one]
      linarith [Int.fract_add_floor r, Int.fract_add_floor s]
    calc
      example_6_23_pi2 t f (r + s) =
          example_6_23_pi2 t f
            (((Int.floor r + Int.floor s : ℤ) : ℝ) * 1 + (u + v)) := by rw [hrewrite]
      _ = example_6_23_pi2 t f (u + v) := by
        simpa [add_comm, add_left_comm, add_assoc] using hper
  calc
    example_6_23_pi2 t f (r + s) = example_6_23_pi2 t f (u + v) := hsum
    _ ≤ example_6_23_pi2 t f u + example_6_23_pi2 t f v :=
      example_6_23_pi2_subadditiveOnIco ht hft hf hu0 hu1 hv0 hv1
    _ = example_6_23_pi2 t f r + example_6_23_pi2 t f s := by
      rw [← example_6_23_pi2_eq_fract t f r, ← example_6_23_pi2_eq_fract t f s]

/-- Helper for Exercise 6.18: under the parameter hypotheses, `example_6_23_pi2` is a minimal
valid function on `ℝ`. -/
theorem example623Pi2Minimal
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pure_integer_minimal_valid_function_on_R f (example_6_23_pi2 t f) := by
  -- Package the scalar facts through the canonical `Fin 1` criterion from Theorem 6.22.
  change pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ f)
    (fun r : Fin 1 → ℝ ↦ example_6_23_pi2 t f (r 0))
  refine pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry ?_ ?_ ?_ ?_ ?_
  · intro r
    simpa using example_6_23_pi2_nonneg ht hft hf (r 0)
  · simpa using (example_6_23_pi2_keyValues ht hft hf).1
  · intro r s
    simpa using example_6_23_pi2_subadditive ht hft hf (r 0) (s 0)
  · intro r w
    have hper := (example_6_23_pi2_periodic t f).int_mul (w 0) (r 0)
    simpa [one_mul, add_comm, add_left_comm, add_assoc] using hper.symm
  · intro r
    simpa using example_6_23_pi2_symmetryReal ht hft hf (r 0)

/-- Helper for Exercise 6.18: the midpoint components already agree with `π₂` on the left cell
`[0, 1 - f]`, where the source branch is the same steep affine segment used in Example 6.24. -/
theorem midpointComponentsEqOnLeftCellOfPi2
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_23_pi2 t f) π₁ (Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f)) ∧
      Set.EqOn (example_6_23_pi2 t f) π₂ (Set.Icc (0 : ℝ) (pi2LeftBreakpoint t f)) := by
  let α : ℝ := pi2LeftBreakpoint t f
  let π : ℝ → ℝ := example_6_23_pi2 t f
  have hα_pos : 0 < α := by
    simpa [α, pi2LeftBreakpoint] using (pi2ParameterFacts ht hft hf).2.2.1
  have hα_lt_one : α < 1 := by
    dsimp [α]
    linarith
  have hhalf_pos : 0 < α / 2 := by
    linarith
  have hπ : pure_integer_minimal_valid_function_on_R f π := example623Pi2Minimal ht hft hf
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨_, hπ₁_zero, _, hπ₁_alpha, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨_, hπ₂_zero, _, hπ₂_alpha, hπ₂_bdd⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π x + π y = π (x + y) := by
    intro x y hx hy
    have hx_lt_one : x < 1 := by
      linarith [hx.2, hα_lt_one]
    have hy_lt_one : y < 1 := by
      linarith [hy.2, hα_lt_one]
    have hx_le_alpha : x ≤ α := by
      linarith [hx.2]
    have hy_le_alpha : y ≤ α := by
      linarith [hy.2]
    have hxy_nonneg : 0 ≤ x + y := add_nonneg hx.1 hy.1
    have hxy_lt_one : x + y < 1 := by
      linarith [hx.2, hy.2, hα_lt_one]
    have hxy_le_alpha : x + y ≤ α := by
      linarith [hx.2, hy.2]
    -- On this left rectangle all three source values use the common affine branch `u ↦ u / (1-f)`.
    dsimp [π]
    rw [example_6_23_pi2_eq_on_leftCell ht hft hf
      (show x ∈ Set.Icc (0 : ℝ) α by simpa [α] using ⟨hx.1, hx_le_alpha⟩)]
    rw [example_6_23_pi2_eq_on_leftCell ht hft hf
      (show y ∈ Set.Icc (0 : ℝ) α by simpa [α] using ⟨hy.1, hy_le_alpha⟩)]
    rw [example_6_23_pi2_eq_on_leftCell ht hft hf
      (show x + y ∈ Set.Icc (0 : ℝ) α by simpa [α] using ⟨hxy_nonneg, hxy_le_alpha⟩)]
    have hα_ne : α ≠ 0 := by
      linarith
    field_simp [hα_ne]
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd hhalf_pos hhalf_pos
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨c₁, _gA₁, _gB₁, gAB₁, _hgA₁, _hgAeq₁, _hgB₁, _hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd hhalf_pos hhalf_pos
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨c₂, _gA₂, _gB₂, gAB₂, _hgA₂, _hgAeq₂, _hgB₂, _hgBeq₂, hgAB₂, hgABeq₂⟩
  have hsum_half : α / 2 + α / 2 = α := by
    ring
  have hπ₁_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc (0 : ℝ) α) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [hsum_half] using hgABeq₁
  have hπ₂_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc (0 : ℝ) α) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [hsum_half] using hgABeq₂
  have hπ₁_affine_intercept :
      ∃ d : ℝ, Set.EqOn π₁ (fun x ↦ c₁ * x + d) (Set.Icc (0 : ℝ) α) :=
    (exists_affineMap_eqOn_iff).1 hπ₁_affine_owner
  rcases hπ₁_affine_intercept with
    ⟨d₁, hd₁⟩
  have hπ₂_affine_intercept :
      ∃ d : ℝ, Set.EqOn π₂ (fun x ↦ c₂ * x + d) (Set.Icc (0 : ℝ) α) :=
    (exists_affineMap_eqOn_iff).1 hπ₂_affine_owner
  rcases hπ₂_affine_intercept with
    ⟨d₂, hd₂⟩
  have hd₁_zero : d₁ = 0 := by
    have h0 := hd₁ (by exact ⟨le_rfl, le_of_lt hα_pos⟩)
    rw [hπ₁_zero] at h0
    linarith
  have hd₂_zero : d₂ = 0 := by
    have h0 := hd₂ (by exact ⟨le_rfl, le_of_lt hα_pos⟩)
    rw [hπ₂_zero] at h0
    linarith
  have hc₁ : c₁ = 1 / α := by
    have hα_mem : α ∈ Set.Icc (0 : ℝ) α := by
      exact ⟨le_of_lt hα_pos, le_rfl⟩
    have hα_eq := hd₁ hα_mem
    rw [show π₁ α = 1 by simpa [α, pi2LeftBreakpoint] using hπ₁_alpha, hd₁_zero] at hα_eq
    have hα_ne : α ≠ 0 := by
      linarith
    apply (eq_div_iff hα_ne).2
    linarith
  have hc₂ : c₂ = 1 / α := by
    have hα_mem : α ∈ Set.Icc (0 : ℝ) α := by
      exact ⟨le_of_lt hα_pos, le_rfl⟩
    have hα_eq := hd₂ hα_mem
    rw [show π₂ α = 1 by simpa [α, pi2LeftBreakpoint] using hπ₂_alpha, hd₂_zero] at hα_eq
    have hα_ne : α ≠ 0 := by
      linarith
    apply (eq_div_iff hα_ne).2
    linarith
  constructor
  · intro x hx
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx.2 hα_lt_one
    have hπ_raw : π x = x / α := by
      simpa [π, α] using example_6_23_pi2_eq_on_leftCell ht hft hf hx
    have hα_ne : α ≠ 0 := by
      linarith
    calc
      π x = x / α := hπ_raw
      _ = c₁ * x + d₁ := by
        rw [hc₁, hd₁_zero]
        field_simp [hα_ne]
        ring
      _ = π₁ x := by
        symm
        exact hd₁ hx
  · intro x hx
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx.2 hα_lt_one
    have hπ_raw : π x = x / α := by
      simpa [π, α] using example_6_23_pi2_eq_on_leftCell ht hft hf hx
    have hα_ne : α ≠ 0 := by
      linarith
    calc
      π x = x / α := hπ_raw
      _ = c₂ * x + d₂ := by
        rw [hc₂, hd₂_zero]
        field_simp [hα_ne]
        ring
      _ = π₂ x := by
        symm
        exact hd₂ hx

/-- Helper for Exercise 6.18: the midpoint components already take the source values at the three
canonical central anchors `x`, `2 * x`, and `m`. -/
theorem midpointComponentsCentralSpecialValuesOfPi2
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    let x : ℝ := (pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f) / 3
    let y : ℝ := 2 * x
    let m : ℝ := (pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f) / 2
    π₁ x = example_6_23_pi2 t f x ∧
      π₂ x = example_6_23_pi2 t f x ∧
        π₁ y = example_6_23_pi2 t f y ∧
          π₂ y = example_6_23_pi2 t f y ∧
            π₁ m = example_6_23_pi2 t f m ∧
              π₂ m = example_6_23_pi2 t f m := by
  dsimp only
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  let x : ℝ := (β + γ) / 3
  let m : ℝ := (β + γ) / 2
  have hπ : pure_integer_minimal_valid_function_on_R f (example_6_23_pi2 t f) :=
    example623Pi2Minimal ht hft hf
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hsum : β + γ = 2 - f := by
    simpa [β, γ] using pi2MiddleBreakpoints_sum ht hft hf
  have hden : β + γ ≠ 0 := by
    have h2f := (pi2ParameterFacts ht hft hf).2.2.2.1
    linarith
  have hβγ : β < γ := by
    simpa [β, γ] using (pi2BreakpointOrder ht hft hf).2.2.1
  have hdouble : 2 * β ≤ γ := by
    simpa [β, γ] using pi2DoubleMiddleLeft_le_middleRight ht hft hf
  have hx_mem : x ∈ Set.Icc β γ := by
    dsimp [x]
    constructor <;> linarith
  have h2x_mem : 2 * x ∈ Set.Icc β γ := by
    dsimp [x]
    constructor <;> linarith
  have hm_mem : m ∈ Set.Icc β γ := by
    dsimp [m]
    constructor <;> linarith
  have hπx_raw : example_6_23_pi2 t f x = x / (β + γ) := by
    have hx_mem' :
        x ∈ Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
      simpa [β, γ] using hx_mem
    calc
      example_6_23_pi2 t f x = x / (2 - f) := by
        exact example_6_23_pi2_eq_on_closedCentralCell ht hft hf hx_mem'
      _ = x / (β + γ) := by rw [hsum]
  have hπ2x_raw : example_6_23_pi2 t f (2 * x) = (2 * x) / (β + γ) := by
    have h2x_mem' :
        2 * x ∈ Set.Icc (pi2MiddleLeftBreakpoint t f)
          (pi2MiddleRightBreakpoint t f) := by
      simpa [β, γ] using h2x_mem
    calc
      example_6_23_pi2 t f (2 * x) = (2 * x) / (2 - f) := by
        exact example_6_23_pi2_eq_on_closedCentralCell ht hft hf h2x_mem'
      _ = (2 * x) / (β + γ) := by rw [hsum]
  have hπm_raw : example_6_23_pi2 t f m = m / (β + γ) := by
    have hm_mem' :
        m ∈ Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
      simpa [β, γ] using hm_mem
    calc
      example_6_23_pi2 t f m = m / (2 - f) := by
        exact example_6_23_pi2_eq_on_closedCentralCell ht hft hf hm_mem'
      _ = m / (β + γ) := by rw [hsum]
  have hπx : example_6_23_pi2 t f x = 1 / 3 := by
    calc
      example_6_23_pi2 t f x = x / (β + γ) := hπx_raw
      _ = 1 / 3 := by
        dsimp [x]
        field_simp [hden]
  have hπ2x : example_6_23_pi2 t f (2 * x) = 2 / 3 := by
    calc
      example_6_23_pi2 t f (2 * x) = (2 * x) / (β + γ) := hπ2x_raw
      _ = 2 / 3 := by
        dsimp [x]
        field_simp [hden]
  have hπm : example_6_23_pi2 t f m = 1 / 2 := by
    calc
      example_6_23_pi2 t f m = m / (β + γ) := hπm_raw
      _ = 1 / 2 := by
        dsimp [m]
        field_simp [hden]
  have hπ_add_xx :
      example_6_23_pi2 t f x + example_6_23_pi2 t f x =
        example_6_23_pi2 t f (x + x) := by
    calc
      example_6_23_pi2 t f x + example_6_23_pi2 t f x =
          x / (β + γ) + x / (β + γ) := by rw [hπx_raw]
      _ = (2 * x) / (β + γ) := by
        field_simp [hden]
        ring
      _ = example_6_23_pi2 t f (2 * x) := hπ2x_raw.symm
      _ = example_6_23_pi2 t f (x + x) := by
        congr 1
        ring
  have hπ₁_add : π₁ x + π₁ x = π₁ (2 * x) := by
    -- Genuine source additivity at `x+x` transfers to each midpoint component.
    simpa [two_mul] using (hadd_transfer hπ_add_xx).1
  have hπ₂_add : π₂ x + π₂ x = π₂ (2 * x) := by
    simpa [two_mul] using (hadd_transfer hπ_add_xx).2
  have hπ₁_shift_x : π₁ (-f - x) = π₁ (2 * x) := by
    calc
      π₁ (-f - x) = π₁ (((2 : ℤ) : ℝ) * 1 + (-f - x)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₁_periodic.int_mul (2 : ℤ) (-f - x)).symm
      _ = π₁ (2 - f - x) := by ring_nf
      _ = π₁ (2 * x) := by
        congr 1
        dsimp [x]
        linarith
  have hπ₂_shift_x : π₂ (-f - x) = π₂ (2 * x) := by
    calc
      π₂ (-f - x) = π₂ (((2 : ℤ) : ℝ) * 1 + (-f - x)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₂_periodic.int_mul (2 : ℤ) (-f - x)).symm
      _ = π₂ (2 - f - x) := by ring_nf
      _ = π₂ (2 * x) := by
        congr 1
        dsimp [x]
        linarith
  have hπ₁_sym_x : π₁ x + π₁ (2 * x) = 1 := by
    calc
      π₁ x + π₁ (2 * x) = π₁ x + π₁ (-f - x) := by rw [hπ₁_shift_x]
      _ = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ x)
  have hπ₂_sym_x : π₂ x + π₂ (2 * x) = 1 := by
    calc
      π₂ x + π₂ (2 * x) = π₂ x + π₂ (-f - x) := by rw [hπ₂_shift_x]
      _ = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ x)
  have hπ₁_x : π₁ x = 1 / 3 := by linarith
  have hπ₂_x : π₂ x = 1 / 3 := by linarith
  have hπ₁_2x : π₁ (2 * x) = 2 / 3 := by linarith
  have hπ₂_2x : π₂ (2 * x) = 2 / 3 := by linarith
  have hπ₁_shift_m : π₁ (-f - m) = π₁ m := by
    calc
      π₁ (-f - m) = π₁ (((2 : ℤ) : ℝ) * 1 + (-f - m)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₁_periodic.int_mul (2 : ℤ) (-f - m)).symm
      _ = π₁ (2 - f - m) := by ring_nf
      _ = π₁ m := by
        congr 1
        dsimp [m]
        linarith
  have hπ₂_shift_m : π₂ (-f - m) = π₂ m := by
    calc
      π₂ (-f - m) = π₂ (((2 : ℤ) : ℝ) * 1 + (-f - m)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₂_periodic.int_mul (2 : ℤ) (-f - m)).symm
      _ = π₂ (2 - f - m) := by ring_nf
      _ = π₂ m := by
        congr 1
        dsimp [m]
        linarith
  have hπ₁_m : π₁ m = 1 / 2 := by
    have hsym : π₁ m + π₁ m = 1 := by
      calc
        π₁ m + π₁ m = π₁ m + π₁ (-f - m) := by rw [hπ₁_shift_m]
        _ = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ m)
    linarith
  have hπ₂_m : π₂ m = 1 / 2 := by
    have hsym : π₂ m + π₂ m = 1 := by
      calc
        π₂ m + π₂ m = π₂ m + π₂ (-f - m) := by rw [hπ₂_shift_m]
        _ = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ m)
    linarith
  -- The solved normalized values coincide with the three source values computed above.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hπ₁_x.trans hπx.symm
  · exact hπ₂_x.trans hπx.symm
  · exact hπ₁_2x.trans hπ2x.symm
  · exact hπ₂_2x.trans hπ2x.symm
  · exact hπ₁_m.trans hπm.symm
  · exact hπ₂_m.trans hπm.symm

/-- Helper for Exercise 6.18: two affine descriptions with the same slope agree on an interval as
soon as they agree at one anchor point. -/
theorem eqOn_ofSharedAffineSlopeAndPointValue
    {φ ψ : ℝ → ℝ} {a b anchor sigma dφ dψ : ℝ}
    (hanchor : anchor ∈ Set.Icc a b)
    (hφ : Set.EqOn φ (fun x ↦ sigma * x + dφ) (Set.Icc a b))
    (hψ : Set.EqOn ψ (fun x ↦ sigma * x + dψ) (Set.Icc a b))
    (hvalue : φ anchor = ψ anchor) :
    Set.EqOn φ ψ (Set.Icc a b) := by
  -- Matching the two affine models at the anchor identifies the intercept immediately.
  have hd : dφ = dψ := by
    have hφ_anchor := hφ hanchor
    have hψ_anchor := hψ hanchor
    linarith
  intro x hx
  -- Once the intercepts coincide, both affine descriptions are literally the same function.
  rw [hφ hx, hψ hx, hd]

/-- Helper for Exercise 6.18: after recentering the central cell at `β`, the source function `π₂`
is additive on the shifted rectangle `[0, (γ - β)/2] × [0, (γ - β)/2]`. -/
theorem centralShiftedAdditivityRectangleOfPi2
    {t f u v : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1)
    (hu :
      u ∈ Set.Icc (0 : ℝ)
        ((pi2MiddleRightBreakpoint t f - pi2MiddleLeftBreakpoint t f) / 2))
    (hv :
      v ∈ Set.Icc (0 : ℝ)
        ((pi2MiddleRightBreakpoint t f - pi2MiddleLeftBreakpoint t f) / 2)) :
    let β : ℝ := pi2MiddleLeftBreakpoint t f
    let γ : ℝ := pi2MiddleRightBreakpoint t f
    example_6_23_pi2 t f (β + u) + example_6_23_pi2 t f (β + v) =
      example_6_23_pi2 t f (β + u + v) + example_6_23_pi2 t f β := by
  dsimp only
  have hβγ := (pi2BreakpointOrder ht hft hf).2.2.1
  have hβu :
      pi2MiddleLeftBreakpoint t f + u ∈
        Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
    constructor <;> linarith [hu.1, hu.2]
  have hβv :
      pi2MiddleLeftBreakpoint t f + v ∈
        Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
    constructor <;> linarith [hv.1, hv.2]
  have hβuv :
      pi2MiddleLeftBreakpoint t f + u + v ∈
        Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) := by
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hβ :
      pi2MiddleLeftBreakpoint t f ∈
        Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f) :=
    ⟨le_rfl, hβγ.le⟩
  -- All four arguments lie in the same affine central cell, so the rectangle identity is
  -- ordinary cancellation of the common slope and intercept.
  rw [example_6_23_pi2_eq_on_closedCentralCell ht hft hf hβu,
    example_6_23_pi2_eq_on_closedCentralCell ht hft hf hβv,
    example_6_23_pi2_eq_on_closedCentralCell ht hft hf hβuv,
    example_6_23_pi2_eq_on_closedCentralCell ht hft hf hβ]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the central projection
coverage needed by the attempted rigidity proof is equivalent to the stronger parameter bound
`2 / 3 + t ≤ f`. -/
theorem pi2CentralCoverage_iff_strongerParameter
    {t f : ℝ} (ht : 0 < t) (hft : 1 / 2 + t ≤ f) (hf : f < 1) :
    pi2MiddleLeftBreakpoint t f ≤
        (pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f) / 4 ↔
      2 / 3 + t ≤ f := by
  have hden : 0 < 2 - f + t := (pi2ParameterFacts ht hft hf).2.2.2.2
  have htwo_sub_f : 0 < 2 - f := (pi2ParameterFacts ht hft hf).2.2.2.1
  have hgapIdentity :
      4 * pi2MiddleLeftBreakpoint t f -
          (pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f) =
        (2 - f) * (2 + 3 * t - 3 * f) / (2 - f + t) := by
    -- Clearing the positive common denominator exposes the exact missing parameter factor.
    dsimp [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]
    field_simp [hden.ne']
    ring
  constructor
  · intro hcoverage
    have hquotientNonpos :
        (2 - f) * (2 + 3 * t - 3 * f) / (2 - f + t) ≤ 0 := by
      rw [← hgapIdentity]
      linarith
    have hproductNonpos : (2 - f) * (2 + 3 * t - 3 * f) ≤ 0 := by
      rw [div_le_iff₀ hden] at hquotientNonpos
      simpa only [zero_mul] using hquotientNonpos
    -- The first factor is positive, so coverage forces the stronger parameter inequality.
    nlinarith
  · intro hstrong
    have hlinearNonpos : 2 + 3 * t - 3 * f ≤ 0 := by
      linarith
    have hproductNonpos : (2 - f) * (2 + 3 * t - 3 * f) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos htwo_sub_f.le hlinearNonpos
    have hquotientNonpos :
        (2 - f) * (2 + 3 * t - 3 * f) / (2 - f + t) ≤ 0 := by
      rw [div_le_iff₀ hden]
      simpa using hproductNonpos
    -- Reinsert the breakpoint identity and divide by the positive numeral `4`.
    rw [← hgapIdentity] at hquotientNonpos
    linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the admissible specialization
`t = 3/10`, `f = 9/10` has a genuine gap between the central coordinate and sum projections. -/
theorem pi2CentralCoverageFailsAtCounterexample :
    let t : ℝ := 3 / 10
    let f : ℝ := 9 / 10
    0 < t ∧ 1 / 2 + t ≤ f ∧ f < 1 ∧
      (pi2MiddleLeftBreakpoint t f + pi2MiddleRightBreakpoint t f) / 4 <
        pi2MiddleLeftBreakpoint t f := by
  -- Exact rational normalization verifies both admissibility and the uncovered central gap.
  norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the admissible
counterexample parameters do not satisfy the stronger inequality equivalent to central
projection coverage. -/
theorem pi2StrongerParameterFailsAtCounterexample :
    let t : ℝ := 3 / 10
    let f : ℝ := 9 / 10
    0 < t ∧ 1 / 2 + t ≤ f ∧ f < 1 ∧ ¬ (2 / 3 + t ≤ f) := by
  -- Normalize all four rational inequalities, separating the stated range from the missing bound.
  norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: at the admissible
specialization `t = 3/10`, `f = 9/10`, the central coordinate and sum projections leave the
explicit open gap `(33/70, 22/35)`. -/
theorem pi2CounterexampleCentralProjectionValues :
    let t : ℝ := 3 / 10
    let f : ℝ := 9 / 10
    let β : ℝ := pi2MiddleLeftBreakpoint t f
    let γ : ℝ := pi2MiddleRightBreakpoint t f
    β = 11 / 35 ∧ γ = 11 / 14 ∧ γ - β = 33 / 70 ∧
      2 * β = 22 / 35 ∧ γ - β < 2 * β := by
  -- Normalize the two breakpoints first; the projection endpoints and strict gap are then exact
  -- rational consequences.
  norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the raw effective
perturbation on one fundamental interval. -/
noncomputable def pi2CounterexamplePerturbationOnUnitInterval : ℝ → ℝ :=
  fun u ↦
    if _ : u ≤ (33 : ℝ) / 70 then
      0
    else if _ : u ≤ (143 : ℝ) / 280 then
      (u - 33 / 70) / (143 / 280 - 33 / 70)
    else if _ : u ≤ (33 : ℝ) / 56 then
      (11 / 20 - u) / (11 / 20 - 143 / 280)
    else if _ : u ≤ (22 : ℝ) / 35 then
      (u - 22 / 35) / (22 / 35 - 33 / 56)
    else
      0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: extend the raw perturbation
with period one. -/
noncomputable def pi2CounterexamplePerturbation : ℝ → ℝ :=
  onePeriodicExtension pi2CounterexamplePerturbationOnUnitInterval

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: add a signed twelfth of the
effective perturbation to the proposed extreme function. -/
noncomputable def pi2CounterexampleComponent (sigma : ℝ) : ℝ → ℝ :=
  fun r ↦
    example_6_23_pi2 (3 / 10) (9 / 10) r +
      (sigma / 12) * pi2CounterexamplePerturbation r

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation inherits
period one from the canonical extension. -/
theorem pi2CounterexamplePerturbation_periodic :
    Function.Periodic pi2CounterexamplePerturbation 1 := by
  -- Periodicity is supplied directly by the owner of the extension construction.
  exact onePeriodicExtension_periodic _

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: evaluation of the periodic
perturbation reduces to the fractional part. -/
theorem pi2CounterexamplePerturbation_eq_fract (r : ℝ) :
    pi2CounterexamplePerturbation r =
      pi2CounterexamplePerturbation (Int.fract r) := by
  -- Unfold both periodic extensions and use that a fractional part is already in `[0,1)`.
  rw [pi2CounterexamplePerturbation, onePeriodicExtension_apply,
    onePeriodicExtension_apply]
  exact congrArg pi2CounterexamplePerturbationOnUnitInterval
    (Int.fract_eq_self.2 ⟨Int.fract_nonneg r, Int.fract_lt_one r⟩).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: reflection about `11/20`
negates the raw perturbation on the relevant part of the fundamental interval. -/
theorem pi2CounterexamplePerturbationOnUnitInterval_reflection
    {u : ℝ} (hu0 : 1 / 10 ≤ u) (hu1 : u ≤ 1) :
    pi2CounterexamplePerturbationOnUnitInterval u +
      pi2CounterexamplePerturbationOnUnitInterval (11 / 10 - u) = 0 := by
  -- The paired affine pieces have opposite values; impossible branch combinations are removed
  -- by the ordered rational endpoints.
  dsimp [pi2CounterexamplePerturbationOnUnitInterval]
  split_ifs
  all_goals norm_num [div_eq_mul_inv] at *
  all_goals linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: reflection through the
symmetry center for `f = 9/10` negates the periodic perturbation. -/
theorem pi2CounterexamplePerturbation_reflection (r : ℝ) :
    pi2CounterexamplePerturbation r +
      pi2CounterexamplePerturbation (-9 / 10 - r) = 0 := by
  let u : ℝ := Int.fract r
  have hu0 : 0 ≤ u := by simpa [u] using Int.fract_nonneg r
  have hu1 : u < 1 := by simpa [u] using Int.fract_lt_one r
  have hfirst : pi2CounterexamplePerturbation r = pi2CounterexamplePerturbation u := by
    simpa [u] using pi2CounterexamplePerturbation_eq_fract r
  have hsecond :
      pi2CounterexamplePerturbation (-9 / 10 - r) =
        pi2CounterexamplePerturbation (-9 / 10 - u) := by
    have hperiod :=
      pi2CounterexamplePerturbation_periodic.int_mul
        (-(Int.floor r)) (-9 / 10 - u)
    have harg :
        (-9 / 10 - u) + (((-(Int.floor r) : ℤ) : ℝ) * 1) = -9 / 10 - r := by
      dsimp [u]
      norm_num
      linarith [Int.fract_add_floor r]
    calc
      pi2CounterexamplePerturbation (-9 / 10 - r) =
          pi2CounterexamplePerturbation
            ((-9 / 10 - u) + (((-(Int.floor r) : ℤ) : ℝ) * 1)) :=
        congrArg pi2CounterexamplePerturbation harg.symm
      _ = pi2CounterexamplePerturbation (-9 / 10 - u) := hperiod
  rw [hfirst, hsecond]
  by_cases hsmall : u ≤ 1 / 10
  · have hu_le_left : u ≤ (33 : ℝ) / 70 := by
      norm_num at hsmall ⊢
      linarith
    have hfirst_zero : pi2CounterexamplePerturbation u = 0 := by
      rw [pi2CounterexamplePerturbation,
        onePeriodicExtension_eq_on_Ico _ hu0 hu1]
      simp [pi2CounterexamplePerturbationOnUnitInterval, hu_le_left]
    have hv0 : 0 ≤ (1 : ℝ) / 10 - u := by linarith
    have hv1 : (1 : ℝ) / 10 - u < 1 := by linarith
    have hv_le_left : (1 : ℝ) / 10 - u ≤ 33 / 70 := by
      norm_num
      linarith
    have hreflect_zero : pi2CounterexamplePerturbation (1 / 10 - u) = 0 := by
      rw [pi2CounterexamplePerturbation,
        onePeriodicExtension_eq_on_Ico _ hv0 hv1]
      dsimp [pi2CounterexamplePerturbationOnUnitInterval]
      rw [if_pos hv_le_left]
    have hperiod :=
      pi2CounterexamplePerturbation_periodic.int_mul (1 : ℤ) (-9 / 10 - u)
    have hsecond_zero : pi2CounterexamplePerturbation (-9 / 10 - u) = 0 := by
      calc
        pi2CounterexamplePerturbation (-9 / 10 - u) =
            pi2CounterexamplePerturbation
              ((-9 / 10 - u) + (((1 : ℤ) : ℝ) * 1)) := hperiod.symm
        _ = pi2CounterexamplePerturbation (1 / 10 - u) := by
          congr 1
          norm_num
          ring
        _ = 0 := hreflect_zero
    rw [hfirst_zero, hsecond_zero, zero_add]
  · have hu_lower : 1 / 10 ≤ u := (lt_of_not_ge hsmall).le
    let v : ℝ := 11 / 10 - u
    have hv0 : 0 ≤ v := by
      dsimp [v]
      linarith
    have hv1 : v < 1 := by
      dsimp [v]
      linarith
    have hfirst_raw :
        pi2CounterexamplePerturbation u =
          pi2CounterexamplePerturbationOnUnitInterval u :=
      onePeriodicExtension_eq_on_Ico _ hu0 hu1
    have hsecond_raw :
        pi2CounterexamplePerturbation v =
          pi2CounterexamplePerturbationOnUnitInterval v :=
      onePeriodicExtension_eq_on_Ico _ hv0 hv1
    have hperiod :=
      pi2CounterexamplePerturbation_periodic.int_mul (2 : ℤ) (-9 / 10 - u)
    have hsecond_shift :
        pi2CounterexamplePerturbation (-9 / 10 - u) =
          pi2CounterexamplePerturbation v := by
      calc
        pi2CounterexamplePerturbation (-9 / 10 - u) =
            pi2CounterexamplePerturbation
              ((-9 / 10 - u) + (((2 : ℤ) : ℝ) * 1)) := hperiod.symm
        _ = pi2CounterexamplePerturbation v := by
          congr 1
          dsimp [v]
          norm_num
          ring
    rw [hfirst_raw, hsecond_shift, hsecond_raw]
    simpa [v] using
      pi2CounterexamplePerturbationOnUnitInterval_reflection hu_lower hu1.le

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation has the
prescribed values at its five interpolation knots. -/
theorem pi2CounterexamplePerturbation_knotValues :
    pi2CounterexamplePerturbation (33 / 70) = 0 ∧
      pi2CounterexamplePerturbation (143 / 280) = 1 ∧
        pi2CounterexamplePerturbation (11 / 20) = 0 ∧
          pi2CounterexamplePerturbation (33 / 56) = -1 ∧
            pi2CounterexamplePerturbation (22 / 35) = 0 := by
  -- All knots lie in `[0,1)`, so unfold the periodic extension and normalize its active branch.
  norm_num [pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
    onePeriodicExtension, Int.fract]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the raw perturbation is
continuous because its consecutive affine formulas agree at every knot. -/
theorem pi2CounterexamplePerturbationOnUnitInterval_continuous :
    Continuous pi2CounterexamplePerturbationOnUnitInterval := by
  let a : ℝ := 33 / 70
  let b : ℝ := 143 / 280
  let c : ℝ := 11 / 20
  let d : ℝ := 33 / 56
  let e : ℝ := 22 / 35
  let g₀ : ℝ → ℝ := fun _ ↦ 0
  let g₁ : ℝ → ℝ := fun u ↦ (u - a) / (b - a)
  let g₂ : ℝ → ℝ := fun u ↦ (c - u) / (c - b)
  let g₃ : ℝ → ℝ := fun u ↦ (u - e) / (e - d)
  have hg₀ : Continuous g₀ := by
    fun_prop
  have hg₁ : Continuous g₁ := by
    fun_prop
  have hg₂ : Continuous g₂ := by
    fun_prop
  have hg₃ : Continuous g₃ := by
    fun_prop
  have hright : Continuous (fun u : ℝ ↦ if u ≤ e then g₃ u else g₀ u) := by
    -- The final affine segment returns to zero at `e`.
    refine Continuous.if_le hg₃ hg₀ continuous_id continuous_const ?_
    intro u hu
    have hue : u = e := by simpa [e] using hu
    subst u
    norm_num [g₃, g₀, d, e]
  have hmiddleRight :
      Continuous (fun u : ℝ ↦ if u ≤ d then g₂ u else if u ≤ e then g₃ u else g₀ u) := by
    -- The descending middle segment and final rising segment both take value `-1` at `d`.
    refine Continuous.if_le hg₂ hright continuous_id continuous_const ?_
    intro u hu
    have hud : u = d := by simpa [d] using hu
    subst u
    have hde : d ≤ e := by norm_num [d, e]
    norm_num [g₂, g₃, b, c, d, e, hde]
  have hmiddleLeft :
      Continuous
        (fun u : ℝ ↦
          if u ≤ b then g₁ u else if u ≤ d then g₂ u else if u ≤ e then g₃ u else g₀ u) := by
    -- The rising segment and the long descending segment both take value `1` at `b`.
    refine Continuous.if_le hg₁ hmiddleRight continuous_id continuous_const ?_
    intro u hu
    have hub : u = b := by simpa [b] using hu
    subst u
    have hbd : b ≤ d := by norm_num [b, d]
    norm_num [g₁, g₂, a, b, c, d, hbd]
  have hall :
      Continuous
        (fun u : ℝ ↦
          if u ≤ a then g₀ u
          else if u ≤ b then g₁ u
          else if u ≤ d then g₂ u
          else if u ≤ e then g₃ u
          else g₀ u) := by
    -- The first rising segment starts from the zero branch at `a`.
    refine Continuous.if_le hg₀ hmiddleLeft continuous_id continuous_const ?_
    intro u hu
    have hua : u = a := by simpa [a] using hu
    subst u
    have hab : a ≤ b := by norm_num [a, b]
    norm_num [g₀, g₁, a, b, hab]
  simpa [pi2CounterexamplePerturbationOnUnitInterval, a, b, c, d, e, g₀, g₁, g₂, g₃]
    using hall

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the periodic perturbation is
continuous across the endpoints of its fundamental interval. -/
theorem pi2CounterexamplePerturbation_continuous :
    Continuous pi2CounterexamplePerturbation := by
  have hraw :
      ContinuousOn pi2CounterexamplePerturbationOnUnitInterval (Set.Icc (0 : ℝ) 1) :=
    pi2CounterexamplePerturbationOnUnitInterval_continuous.continuousOn
  have hendpoints :
      pi2CounterexamplePerturbationOnUnitInterval 0 =
        pi2CounterexamplePerturbationOnUnitInterval 1 := by
    -- Both endpoints use a zero branch of the raw formula.
    norm_num [pi2CounterexamplePerturbationOnUnitInterval]
  exact hraw.comp_fract'' hendpoints

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the effective perturbation
has absolute value at most one. -/
theorem pi2CounterexamplePerturbation_abs_le_one (r : ℝ) :
    |pi2CounterexamplePerturbation r| ≤ 1 := by
  have hfract_nonneg : 0 ≤ Int.fract r := Int.fract_nonneg r
  have hfract_lt_one : Int.fract r < 1 := Int.fract_lt_one r
  -- On every affine piece, endpoint monotonicity bounds the value between `-1` and `1`.
  rw [pi2CounterexamplePerturbation, onePeriodicExtension_apply]
  dsimp [pi2CounterexamplePerturbationOnUnitInterval]
  split_ifs with hleft hpeak htrough hright
  all_goals rw [abs_le]
  all_goals constructor <;> norm_num [div_eq_mul_inv] <;> linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: a nonzero perturbation value
can occur only over the explicit central support interval. -/
theorem pi2CounterexamplePerturbation_support {r : ℝ}
    (hne : pi2CounterexamplePerturbation r ≠ 0) :
    Int.fract r ∈ Set.Icc ((33 : ℝ) / 70) (22 / 35) := by
  constructor
  · -- Below the left support endpoint the first zero branch is active.
    by_contra hleft
    have hfract_le : Int.fract r ≤ (33 : ℝ) / 70 :=
      le_of_lt (lt_of_not_ge hleft)
    apply hne
    simp [pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
      hfract_le]
  · -- Above the right support endpoint every nonzero affine branch has already ended.
    by_contra hright
    have hright_lt : (22 : ℝ) / 35 < Int.fract r := lt_of_not_ge hright
    have hnot_left : ¬ Int.fract r ≤ (33 : ℝ) / 70 := by
      apply not_le.mpr
      have : (33 : ℝ) / 70 < 22 / 35 := by norm_num
      exact lt_trans this hright_lt
    have hnot_peak : ¬ Int.fract r ≤ (143 : ℝ) / 280 := by
      apply not_le.mpr
      have : (143 : ℝ) / 280 < 22 / 35 := by norm_num
      exact lt_trans this hright_lt
    have hnot_trough : ¬ Int.fract r ≤ (33 : ℝ) / 56 := by
      apply not_le.mpr
      have : (33 : ℝ) / 56 < 22 / 35 := by norm_num
      exact lt_trans this hright_lt
    have hnot_right : ¬ Int.fract r ≤ (22 : ℝ) / 35 := not_le.mpr hright_lt
    apply hne
    simp [pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
      hnot_left, hnot_peak, hnot_trough, hnot_right]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every signed component is
one-periodic. -/
theorem pi2CounterexampleComponent_periodic (sigma : ℝ) :
    Function.Periodic (pi2CounterexampleComponent sigma) 1 := by
  -- Periodicity is preserved by the pointwise linear combination defining the component.
  intro r
  dsimp [pi2CounterexampleComponent]
  rw [example_6_23_pi2_periodic, pi2CounterexamplePerturbation_periodic]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every signed component is
continuous. -/
theorem pi2CounterexampleComponent_continuous (sigma : ℝ) :
    Continuous (pi2CounterexampleComponent sigma) := by
  -- Continuity is preserved by the pointwise affine combination defining the component.
  simpa only [pi2CounterexampleComponent] using
    (example_6_23_pi2_continuous (by norm_num) (by norm_num) (by norm_num)).add
      (continuous_const.mul pi2CounterexamplePerturbation_continuous)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every signed component
vanishes at the origin. -/
theorem pi2CounterexampleComponent_zero (sigma : ℝ) :
    pi2CounterexampleComponent sigma 0 = 0 := by
  -- Both the source function and the supported perturbation vanish at `0`.
  dsimp [pi2CounterexampleComponent]
  rw [(example_6_23_pi2_keyValues (by norm_num) (by norm_num) (by norm_num)).1]
  norm_num [pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
    onePeriodicExtension, Int.fract]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every signed component obeys
the minimal-valid-function symmetry equation at `f = 9/10`. -/
theorem pi2CounterexampleComponent_symmetry (sigma r : ℝ) :
    pi2CounterexampleComponent sigma r +
      pi2CounterexampleComponent sigma (-9 / 10 - r) = 1 := by
  have hsource :=
    example_6_23_pi2_symmetryReal (t := 3 / 10) (f := 9 / 10)
      (by norm_num) (by norm_num) (by norm_num) r
  have hperturb := pi2CounterexamplePerturbation_reflection r
  -- Normalize the two equivalent spellings of the rational reflection center before rewriting.
  have hsource' :
      example_6_23_pi2 (3 / 10) (9 / 10) r +
          example_6_23_pi2 (3 / 10) (9 / 10) (-9 / 10 - r) = 1 := by
    convert hsource using 1 <;> ring
  have hperturb' :
      pi2CounterexamplePerturbation r +
          pi2CounterexamplePerturbation (-9 / 10 - r) = 0 := by
    convert hperturb using 1 <;> ring
  -- Regroup source and perturbation terms, then use their complementary symmetry identities.
  dsimp [pi2CounterexampleComponent]
  calc
    example_6_23_pi2 (3 / 10) (9 / 10) r +
          (sigma / 12) * pi2CounterexamplePerturbation r +
        (example_6_23_pi2 (3 / 10) (9 / 10) (-9 / 10 - r) +
          (sigma / 12) * pi2CounterexamplePerturbation (-9 / 10 - r)) =
        (example_6_23_pi2 (3 / 10) (9 / 10) r +
          example_6_23_pi2 (3 / 10) (9 / 10) (-9 / 10 - r)) +
          (sigma / 12) *
            (pi2CounterexamplePerturbation r +
              pi2CounterexamplePerturbation (-9 / 10 - r)) := by ring
    _ = 1 := by rw [hsource', hperturb']; ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: both signed midpoint
components are nonnegative. -/
theorem pi2CounterexampleComponent_nonneg {sigma : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) (r : ℝ) :
    0 ≤ pi2CounterexampleComponent sigma r := by
  by_cases hzero : pi2CounterexamplePerturbation r = 0
  · -- Off the support, the component is exactly the already-proved nonnegative source.
    dsimp [pi2CounterexampleComponent]
    rw [hzero]
    norm_num
    exact example_6_23_pi2_nonneg (by norm_num) (by norm_num) (by norm_num) r
  have hsupport := pi2CounterexamplePerturbation_support hzero
  have hcentral :
      Int.fract r ∈
        Set.Icc
          (pi2MiddleLeftBreakpoint (3 / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) := by
    constructor
    · norm_num [pi2MiddleLeftBreakpoint] at *
      linarith
    · norm_num [pi2MiddleRightBreakpoint] at *
      linarith
  have hsource :
      example_6_23_pi2 (3 / 10) (9 / 10) r =
        Int.fract r / (2 - 9 / 10) := by
    calc
      example_6_23_pi2 (3 / 10) (9 / 10) r =
          example_6_23_pi2 (3 / 10) (9 / 10) (Int.fract r) :=
        example_6_23_pi2_eq_fract _ _ _
      _ = Int.fract r / (2 - 9 / 10) :=
        example_6_23_pi2_eq_on_closedCentralCell
          (by norm_num) (by norm_num) (by norm_num) hcentral
  rcases abs_le.mp (pi2CounterexamplePerturbation_abs_le_one r) with
    ⟨hperturb_lower, hperturb_upper⟩
  dsimp [pi2CounterexampleComponent]
  rw [hsource]
  rcases hsigma with rfl | rfl
  · norm_num [div_eq_mul_inv]
    linarith [hsupport.1, hperturb_lower]
  · norm_num [div_eq_mul_inv]
    linarith [hsupport.1, hperturb_upper]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the two signed components
have midpoint exactly `example_6_23_pi2 (3/10) (9/10)`. -/
theorem pi2CounterexampleComponents_midpoint :
    example_6_23_pi2 (3 / 10) (9 / 10) =
      (1 / 2 : ℝ) • pi2CounterexampleComponent 1 +
        (1 / 2 : ℝ) • pi2CounterexampleComponent (-1) := by
  -- Pointwise expansion cancels the two opposite perturbation terms.
  ext r
  simp only [Pi.add_apply, Pi.smul_apply]
  dsimp [pi2CounterexampleComponent]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the two signed midpoint
components are distinct. -/
theorem pi2CounterexampleComponents_ne :
    pi2CounterexampleComponent 1 ≠ pi2CounterexampleComponent (-1) := by
  -- Equality at the positive peak would force the nonzero perturbation amplitude to vanish.
  intro hcomponents
  have hpeak := congrFun hcomponents (143 / 280)
  dsimp [pi2CounterexampleComponent] at hpeak
  rw [pi2CounterexamplePerturbation_knotValues.2.1] at hpeak
  norm_num at hpeak

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the five knots of the
proposed effective perturbation are strictly ordered in the unit interval. -/
theorem pi2CounterexamplePerturbationKnotOrder :
    (0 : ℝ) < (33 : ℝ) / 70 ∧ (33 : ℝ) / 70 < (143 : ℝ) / 280 ∧
      (143 : ℝ) / 280 < (11 : ℝ) / 20 ∧ (11 : ℝ) / 20 < (33 : ℝ) / 56 ∧
        (33 : ℝ) / 56 < (22 : ℝ) / 35 ∧ (22 : ℝ) / 35 < 1 := by
  -- Exact normalization certifies that the interpolation data define consecutive segments.
  norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation knots are
paired by reflection about the midpoint of the central source interval at `f = 9/10`. -/
theorem pi2CounterexamplePerturbationKnotReflection :
    let f : ℝ := 9 / 10
    33 / 70 + 22 / 35 = 2 - f ∧
      143 / 280 + 33 / 56 = 2 - f ∧ 2 * (11 / 20) = 2 - f := by
  -- The paired endpoint sums and the doubled center all equal the reflection width `2 - f`.
  norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: affine formulas agreeing at
two distinct points have the same slope. -/
theorem affineSlope_eq_of_eqAt_twoPoints
    {c d sigma e x y : ℝ} (hxy : x < y)
    (hx : c * x + d = sigma * x + e) (hy : c * y + d = sigma * y + e) :
    c = sigma := by
  -- Subtract the endpoint identities and cancel the nonzero point separation.
  have hmul : (c - sigma) * (y - x) = 0 := by
    linear_combination hy - hx
  have hsep : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsep)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: an affine formula on
`[a + 1, b + 1]` for a `1`-periodic function pulls back to `[a, b]`. -/
theorem periodicEqOn_untranslateUnit
    {φ : ℝ → ℝ} (hperiodic : Function.Periodic φ 1)
    {a b sigma d : ℝ}
    (hshift : Set.EqOn φ (fun x ↦ sigma * x + d) (Set.Icc (a + 1) (b + 1))) :
    Set.EqOn φ (fun x ↦ sigma * x + (sigma + d)) (Set.Icc a b) := by
  intro x hx
  have hx_shift : x + 1 ∈ Set.Icc (a + 1) (b + 1) := by
    constructor <;> linarith [hx.1, hx.2]
  -- Compare the base point with its unit translate before rewriting the translated affine model.
  calc
    φ x = φ (x + 1) := by
      simpa using (hperiodic x).symm
    _ = sigma * (x + 1) + d := hshift hx_shift
    _ = sigma * x + (sigma + d) := by ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: under the stronger
parameter range, both midpoint components agree with `π₂` on the full central cell. -/
theorem midpointComponentsEqOnCentralCellOfPi2
    {t f : ℝ} (ht : 0 < t) (hstrong : 2 / 3 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_23_pi2 t f) π₁
        (Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f)) ∧
      Set.EqOn (example_6_23_pi2 t f) π₂
        (Set.Icc (pi2MiddleLeftBreakpoint t f) (pi2MiddleRightBreakpoint t f)) := by
  have hft : 1 / 2 + t ≤ f := by
    linarith
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  let x : ℝ := (β + γ) / 3
  let y : ℝ := 2 * x
  let m : ℝ := (β + γ) / 2
  let π : ℝ → ℝ := example_6_23_pi2 t f
  have hπ : pure_integer_minimal_valid_function_on_R f π :=
    example623Pi2Minimal ht hft hf
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, hπ₂_bdd⟩
  rcases midpointComponentsCentralSpecialValuesOfPi2 ht hft hf hπ₁ hπ₂ hmid with
    ⟨hx₁, hx₂, hy₁, hy₂, hm₁, hm₂⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hβγ : β < γ := by
    simpa [β, γ] using (pi2BreakpointOrder ht hft hf).2.2.1
  have hcoverage : β ≤ (β + γ) / 4 := by
    exact (pi2CentralCoverage_iff_strongerParameter ht hft hf).2 hstrong
  have hsum : β + γ = 2 - f := by
    simpa [β, γ] using pi2MiddleBreakpoints_sum ht hft hf
  have h2f_pos : 0 < 2 - f := (pi2ParameterFacts ht hft hf).2.2.2.1
  have h2f_ne : 2 - f ≠ 0 := ne_of_gt h2f_pos
  have hβ_lt_x : β < x := by
    dsimp [x]
    linarith [hcoverage, hβγ]
  have hm_lt_y : m < y := by
    dsimp [m, y, x]
    linarith [hβγ]
  have hm_mem_AB : m ∈ Set.Icc (2 * β) y := by
    constructor
    · dsimp [m]
      linarith [hcoverage]
    · exact hm_lt_y.le
  have hy_mem_AB : y ∈ Set.Icc (2 * β) y := by
    constructor
    · dsimp [y, x]
      linarith [hcoverage]
    · exact le_rfl
  have hx_mem_A : x ∈ Set.Icc β x := by
    exact ⟨hβ_lt_x.le, le_rfl⟩
  have hπ_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc β x → v ∈ Set.Icc β x →
        π u + π v = π (u + v) := by
    intro u v hu hv
    have hu_central : u ∈ Set.Icc β γ := by
      constructor
      · exact hu.1
      · linarith [hu.2, hcoverage, hβγ]
    have hv_central : v ∈ Set.Icc β γ := by
      constructor
      · exact hv.1
      · linarith [hv.2, hcoverage, hβγ]
    have huv_central : u + v ∈ Set.Icc β γ := by
      constructor
      · linarith [hu.1, hv.1]
      · have huv_le_y : u + v ≤ y := by
          dsimp [y]
          linarith [hu.2, hv.2]
        linarith [huv_le_y, hcoverage]
    -- On this lower central rectangle, all three source points stay on the same central branch.
    rw [example_6_23_pi2_eq_on_closedCentralCell ht hft hf (by simpa [β, γ] using hu_central),
      example_6_23_pi2_eq_on_closedCentralCell ht hft hf (by simpa [β, γ] using hv_central),
      example_6_23_pi2_eq_on_closedCentralCell ht hft hf (by simpa [β, γ] using huv_central)]
    field_simp [h2f_ne]
    ring
  have hπ₁_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc β x → v ∈ Set.Icc β x →
        π₁ u + π₁ v = π₁ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).1
  have hπ₂_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc β x → v ∈ Set.Icc β x →
        π₂ u + π₂ v = π₂ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).2
  rcases interval_lemma_affine_with_common_slope
      (f := π₁) (a₁ := β) (a₂ := x) (b₁ := β) (b₂ := x)
      hπ₁_bdd hβ_lt_x hβ_lt_x
      (by
        intro u v hu hv
        exact hπ₁_add hu hv) with
    ⟨c₁, gA₁, _gB₁, gAB₁, hgA₁, hgAeq₁, _hgB₁, _hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope
      (f := π₂) (a₁ := β) (a₂ := x) (b₁ := β) (b₂ := x)
      hπ₂_bdd hβ_lt_x hβ_lt_x
      (by
        intro u v hu hv
        exact hπ₂_add hu hv) with
    ⟨c₂, gA₂, _gB₂, gAB₂, hgA₂, hgAeq₂, _hgB₂, _hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_affine_A :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc β x) := by
    exact ⟨gA₁, hgA₁, hgAeq₁⟩
  have hπ₂_affine_A :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc β x) := by
    exact ⟨gA₂, hgA₂, hgAeq₂⟩
  have hπ₁_affine_AB :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc (2 * β) y) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [y, x, two_mul, add_assoc, add_left_comm, add_comm] using hgABeq₁
  have hπ₂_affine_AB :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc (2 * β) y) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [y, x, two_mul, add_assoc, add_left_comm, add_comm] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc β x) (c := c₁)).1
      hπ₁_affine_A with ⟨d₁A, hd₁A⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc β x) (c := c₂)).1
      hπ₂_affine_A with ⟨d₂A, hd₂A⟩
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (2 * β) y) (c := c₁)).1
      hπ₁_affine_AB with ⟨d₁AB, hd₁AB⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (2 * β) y) (c := c₂)).1
      hπ₂_affine_AB with ⟨d₂AB, hd₂AB⟩
  have hπ_source_A :
      Set.EqOn π (fun u ↦ (1 / (2 - f)) * u + 0) (Set.Icc β x) := by
    intro u hu
    have hu_central : u ∈ Set.Icc β γ := by
      constructor
      · exact hu.1
      · linarith [hu.2, hcoverage, hβγ]
    calc
      π u = u / (2 - f) := by
        simpa [π, β, γ] using example_6_23_pi2_eq_on_closedCentralCell ht hft hf hu_central
      _ = (1 / (2 - f)) * u + 0 := by
        field_simp [h2f_ne]
        ring
  have hπ_source_AB :
      Set.EqOn π (fun u ↦ (1 / (2 - f)) * u + 0) (Set.Icc (2 * β) y) := by
    intro u hu
    have hu_central : u ∈ Set.Icc β γ := by
      constructor
      · linarith [hu.1]
      · linarith [hu.2, hcoverage]
    calc
      π u = u / (2 - f) := by
        simpa [π, β, γ] using example_6_23_pi2_eq_on_closedCentralCell ht hft hf hu_central
      _ = (1 / (2 - f)) * u + 0 := by
        field_simp [h2f_ne]
        ring
  have hc₁ : c₁ = 1 / (2 - f) := by
    have hm_compare : c₁ * m + d₁AB = (1 / (2 - f)) * m + 0 := by
      calc
        c₁ * m + d₁AB = π₁ m := (hd₁AB hm_mem_AB).symm
        _ = π m := hm₁
        _ = (1 / (2 - f)) * m + 0 := by
          simpa using hπ_source_AB hm_mem_AB
    have hy_compare : c₁ * y + d₁AB = (1 / (2 - f)) * y + 0 := by
      calc
        c₁ * y + d₁AB = π₁ y := (hd₁AB hy_mem_AB).symm
        _ = π y := hy₁
        _ = (1 / (2 - f)) * y + 0 := by
          simpa using hπ_source_AB hy_mem_AB
    exact affineSlope_eq_of_eqAt_twoPoints hm_lt_y hm_compare hy_compare
  have hc₂ : c₂ = 1 / (2 - f) := by
    have hm_compare : c₂ * m + d₂AB = (1 / (2 - f)) * m + 0 := by
      calc
        c₂ * m + d₂AB = π₂ m := (hd₂AB hm_mem_AB).symm
        _ = π m := hm₂
        _ = (1 / (2 - f)) * m + 0 := by
          simpa using hπ_source_AB hm_mem_AB
    have hy_compare : c₂ * y + d₂AB = (1 / (2 - f)) * y + 0 := by
      calc
        c₂ * y + d₂AB = π₂ y := (hd₂AB hy_mem_AB).symm
        _ = π y := hy₂
        _ = (1 / (2 - f)) * y + 0 := by
          simpa using hπ_source_AB hy_mem_AB
    exact affineSlope_eq_of_eqAt_twoPoints hm_lt_y hm_compare hy_compare
  have hπ₁_affine_A_fixed :
      Set.EqOn π₁ (fun u ↦ (1 / (2 - f)) * u + d₁A) (Set.Icc β x) := by
    intro u hu
    simpa [hc₁, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm] using
      hd₁A hu
  have hπ₂_affine_A_fixed :
      Set.EqOn π₂ (fun u ↦ (1 / (2 - f)) * u + d₂A) (Set.Icc β x) := by
    intro u hu
    simpa [hc₂, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm] using
      hd₂A hu
  have hπ₁_affine_AB_fixed :
      Set.EqOn π₁ (fun u ↦ (1 / (2 - f)) * u + d₁AB) (Set.Icc (2 * β) y) := by
    intro u hu
    simpa [hc₁, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm] using
      hd₁AB hu
  have hπ₂_affine_AB_fixed :
      Set.EqOn π₂ (fun u ↦ (1 / (2 - f)) * u + d₂AB) (Set.Icc (2 * β) y) := by
    intro u hu
    simpa [hc₂, add_assoc, add_left_comm, add_comm, mul_assoc, mul_comm, mul_left_comm] using
      hd₂AB hu
  have hA₁ : Set.EqOn π π₁ (Set.Icc β x) := by
    exact eqOn_ofSharedAffineSlopeAndPointValue hx_mem_A hπ_source_A hπ₁_affine_A_fixed hx₁.symm
  have hA₂ : Set.EqOn π π₂ (Set.Icc β x) := by
    exact eqOn_ofSharedAffineSlopeAndPointValue hx_mem_A hπ_source_A hπ₂_affine_A_fixed hx₂.symm
  have hAB₁ : Set.EqOn π π₁ (Set.Icc (2 * β) y) := by
    exact
      eqOn_ofSharedAffineSlopeAndPointValue hm_mem_AB hπ_source_AB hπ₁_affine_AB_fixed hm₁.symm
  have hAB₂ : Set.EqOn π π₂ (Set.Icc (2 * β) y) := by
    exact
      eqOn_ofSharedAffineSlopeAndPointValue hm_mem_AB hπ_source_AB hπ₂_affine_AB_fixed hm₂.symm
  have hπ_reflect (u : ℝ) : π u + π (β + γ - u) = 1 := by
    have hbase := example_6_23_pi2_symmetryReal ht hft hf u
    have hshift :
        π (-f - u) = π (β + γ - u) := by
      calc
        π (-f - u) = π ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [π, one_mul, add_assoc, add_left_comm, add_comm] using
            ((example_6_23_pi2_periodic t f).int_mul (2 : ℤ) (-f - u)).symm
        _ = π (2 - f - u) := by
          congr 1
          ring
        _ = π (β + γ - u) := by
          rw [hsum]
    rw [hshift] at hbase
    exact hbase
  have hπ₁_reflect (u : ℝ) : π₁ u + π₁ (β + γ - u) = 1 := by
    have hbase :
        π₁ u + π₁ (-f - u) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ u)
    have hshift :
        π₁ (-f - u) = π₁ (β + γ - u) := by
      calc
        π₁ (-f - u) = π₁ ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [one_mul, add_assoc, add_left_comm, add_comm] using
            (hπ₁_periodic.int_mul (2 : ℤ) (-f - u)).symm
        _ = π₁ (2 - f - u) := by
          congr 1
          ring
        _ = π₁ (β + γ - u) := by
          rw [hsum]
    rw [hshift] at hbase
    exact hbase
  have hπ₂_reflect (u : ℝ) : π₂ u + π₂ (β + γ - u) = 1 := by
    have hbase :
        π₂ u + π₂ (-f - u) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ u)
    have hshift :
        π₂ (-f - u) = π₂ (β + γ - u) := by
      calc
        π₂ (-f - u) = π₂ ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [one_mul, add_assoc, add_left_comm, add_comm] using
            (hπ₂_periodic.int_mul (2 : ℤ) (-f - u)).symm
        _ = π₂ (2 - f - u) := by
          congr 1
          ring
        _ = π₂ (β + γ - u) := by
          rw [hsum]
    rw [hshift] at hbase
    exact hbase
  constructor
  · intro u hu
    by_cases hu_lower : u ≤ x
    · exact hA₁ ⟨hu.1, hu_lower⟩
    · by_cases hu_upper : u ≤ y
      · by_cases hu_ab : 2 * β ≤ u
        · exact hAB₁ ⟨hu_ab, hu_upper⟩
        · let v : ℝ := β + γ - u
          have hv_mem : v ∈ Set.Icc (2 * β) y := by
            constructor
            · dsimp [v]
              have hu_lt : u < 2 * β := lt_of_not_ge hu_ab
              linarith [hcoverage, hu_lt]
            · dsimp [v, y, x]
              linarith [lt_of_not_ge hu_lower]
          have hv_eq : π v = π₁ v := by
            exact hAB₁ hv_mem
          have hsource := hπ_reflect u
          have hcomponent := hπ₁_reflect u
          dsimp [v] at hv_eq
          linarith
      · let v : ℝ := β + γ - u
        have hv_mem : v ∈ Set.Icc β x := by
          constructor
          · dsimp [v]
            linarith [hu.2]
          · dsimp [v, y, x]
            linarith [lt_of_not_ge hu_upper]
        have hv_eq : π v = π₁ v := by
          exact hA₁ hv_mem
        have hsource := hπ_reflect u
        have hcomponent := hπ₁_reflect u
        dsimp [v] at hv_eq
        linarith
  · intro u hu
    by_cases hu_lower : u ≤ x
    · exact hA₂ ⟨hu.1, hu_lower⟩
    · by_cases hu_upper : u ≤ y
      · by_cases hu_ab : 2 * β ≤ u
        · exact hAB₂ ⟨hu_ab, hu_upper⟩
        · let v : ℝ := β + γ - u
          have hv_mem : v ∈ Set.Icc (2 * β) y := by
            constructor
            · dsimp [v]
              have hu_lt : u < 2 * β := lt_of_not_ge hu_ab
              linarith [hcoverage, hu_lt]
            · dsimp [v, y, x]
              linarith [lt_of_not_ge hu_lower]
          have hv_eq : π v = π₂ v := by
            exact hAB₂ hv_mem
          have hsource := hπ_reflect u
          have hcomponent := hπ₂_reflect u
          dsimp [v] at hv_eq
          linarith
      · let v : ℝ := β + γ - u
        have hv_mem : v ∈ Set.Icc β x := by
          constructor
          · dsimp [v]
            linarith [hu.2]
          · dsimp [v, y, x]
            linarith [lt_of_not_ge hu_upper]
        have hv_eq : π v = π₂ v := by
          exact hA₂ hv_mem
        have hsource := hπ_reflect u
        have hcomponent := hπ₂_reflect u
        dsimp [v] at hv_eq
        linarith

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: once the central cell is
fixed, the common negative-slope branch forces both midpoint components to agree with `π₂` on the
closed right cell. -/
theorem midpointComponentsEqOnRightCellOfPi2
    {t f : ℝ} (ht : 0 < t) (hstrong : 2 / 3 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_23_pi2 t f) π₁ (Set.Icc (pi2MiddleRightBreakpoint t f) 1) ∧
      Set.EqOn (example_6_23_pi2 t f) π₂ (Set.Icc (pi2MiddleRightBreakpoint t f) 1) := by
  have hft : 1 / 2 + t ≤ f := by
    linarith
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  let q : ℝ := (γ + 1) / 2
  let π : ℝ → ℝ := example_6_23_pi2 t f
  have hπ : pure_integer_minimal_valid_function_on_R f π :=
    example623Pi2Minimal ht hft hf
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, hπ₁_one, _, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, hπ₂_one, _, hπ₂_bdd⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hγ_lt_one : γ < 1 := by
    simpa [γ] using (pi2BreakpointOrder ht hft hf).2.2.2
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have hγ_mem : γ ∈ Set.Icc γ 1 := by
    exact ⟨le_rfl, le_rfl⟩
  have hright := midpointComponentsEqOnCentralCellOfPi2 ht hstrong hf hπ₁ hπ₂ hmid
  have hγ_eq₁ : π γ = π₁ γ := by
    exact hright.1 hγ_mem
  have hγ_eq₂ : π γ = π₂ γ := by
    exact hright.2 hγ_mem
  have hone_source : π 1 = 0 := by
    simpa [π] using (example_6_23_pi2_keyValues ht hft hf).2.2
  have hπ_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc q 1 → v ∈ Set.Icc q 1 →
        π u + π v = π (u + v) := by
    intro u v hu hv
    have hu_right : u ∈ Set.Icc γ 1 := by
      constructor
      · dsimp [q] at hu
        linarith
      · exact hu.2
    have hv_right : v ∈ Set.Icc γ 1 := by
      constructor
      · dsimp [q] at hv
        linarith
      · exact hv.2
    have huv_right : u + v - 1 ∈ Set.Icc γ 1 := by
      constructor
      · dsimp [q] at hu hv
        linarith
      · linarith [hu.2, hv.2]
    -- High enough in the right cell, periodicity converts the sum back to the same negative slope.
    calc
      π u + π v = (1 - u) / t + (1 - v) / t := by
        rw [example_6_23_pi2_eq_on_closedRightCell ht hft hf (by simpa [γ] using hu_right),
          example_6_23_pi2_eq_on_closedRightCell ht hft hf (by simpa [γ] using hv_right)]
      _ = (1 - (u + v - 1)) / t := by ring
      _ = π (u + v - 1) := by
        symm
        simpa [γ] using example_6_23_pi2_eq_on_closedRightCell ht hft hf huv_right
      _ = π (u + v) := by
        simpa [π, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (example_6_23_pi2_periodic t f (u + v - 1))
  have hπ₁_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc q 1 → v ∈ Set.Icc q 1 →
        π₁ u + π₁ v = π₁ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).1
  have hπ₂_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc q 1 → v ∈ Set.Icc q 1 →
        π₂ u + π₂ v = π₂ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).2
  rcases interval_lemma_affine_with_common_slope
      (f := π₁) (a₁ := q) (a₂ := 1) (b₁ := q) (b₂ := 1)
      hπ₁_bdd hq_lt_one hq_lt_one
      (by
        intro u v hu hv
        exact hπ₁_add hu hv) with
    ⟨c₁, _gA₁, _gB₁, gAB₁, _hgA₁, _hgAeq₁, _hgB₁, _hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope
      (f := π₂) (a₁ := q) (a₂ := 1) (b₁ := q) (b₂ := 1)
      hπ₂_bdd hq_lt_one hq_lt_one
      (by
        intro u v hu hv
        exact hπ₂_add hu hv) with
    ⟨c₂, _gA₂, _gB₂, gAB₂, _hgA₂, _hgAeq₂, _hgB₂, _hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_affine_shift :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc (γ + 1) 2) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [γ, q, add_assoc, add_left_comm, add_comm] using hgABeq₁
  have hπ₂_affine_shift :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc (γ + 1) 2) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [γ, q, add_assoc, add_left_comm, add_comm] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (γ + 1) 2) (c := c₁)).1
      hπ₁_affine_shift with ⟨d₁', hd₁'⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (γ + 1) 2) (c := c₂)).1
      hπ₂_affine_shift with ⟨d₂', hd₂'⟩
  have hπ₁_affine_right :
      Set.EqOn π₁ (fun u ↦ c₁ * u + (c₁ + d₁')) (Set.Icc γ 1) :=
    periodicEqOn_untranslateUnit hπ₁_periodic hd₁'
  have hπ₂_affine_right :
      Set.EqOn π₂ (fun u ↦ c₂ * u + (c₂ + d₂')) (Set.Icc γ 1) :=
    periodicEqOn_untranslateUnit hπ₂_periodic hd₂'
  let sigma : ℝ := -1 / t
  have hπ_source_right :
      Set.EqOn π (fun u ↦ sigma * u - sigma) (Set.Icc γ 1) := by
    intro u hu
    calc
      π u = (1 - u) / t := by
        simpa [π, γ] using example_6_23_pi2_eq_on_closedRightCell ht hft hf hu
      _ = sigma * u - sigma := by
        dsimp [sigma]
        ring
  have hone_mem : (1 : ℝ) ∈ Set.Icc γ 1 := by
    exact ⟨hγ_lt_one.le, le_rfl⟩
  have hc₁ : c₁ = sigma := by
    have hγ_compare : c₁ * γ + (c₁ + d₁') = sigma * γ - sigma := by
      calc
        c₁ * γ + (c₁ + d₁') = π₁ γ := (hπ₁_affine_right hγ_mem).symm
        _ = π γ := hγ_eq₁.symm
        _ = sigma * γ - sigma := hπ_source_right hγ_mem
    have h1_compare : c₁ * 1 + (c₁ + d₁') = sigma * 1 - sigma := by
      calc
        c₁ * 1 + (c₁ + d₁') = π₁ 1 := (hπ₁_affine_right hone_mem).symm
        _ = 0 := hπ₁_one
        _ = π 1 := hone_source.symm
        _ = sigma * 1 - sigma := by
          dsimp [sigma]
          ring
    exact affineSlope_eq_of_eqAt_twoPoints hγ_lt_one hγ_compare h1_compare
  have hc₂ : c₂ = sigma := by
    have hγ_compare : c₂ * γ + (c₂ + d₂') = sigma * γ - sigma := by
      calc
        c₂ * γ + (c₂ + d₂') = π₂ γ := (hπ₂_affine_right hγ_mem).symm
        _ = π γ := hγ_eq₂.symm
        _ = sigma * γ - sigma := hπ_source_right hγ_mem
    have h1_compare : c₂ * 1 + (c₂ + d₂') = sigma * 1 - sigma := by
      calc
        c₂ * 1 + (c₂ + d₂') = π₂ 1 := (hπ₂_affine_right hone_mem).symm
        _ = 0 := hπ₂_one
        _ = π 1 := hone_source.symm
        _ = sigma * 1 - sigma := by
          dsimp [sigma]
          ring
    exact affineSlope_eq_of_eqAt_twoPoints hγ_lt_one hγ_compare h1_compare
  have hπ₁_right_fixed :
      Set.EqOn π₁ (fun u ↦ sigma * u + (c₁ + d₁')) (Set.Icc γ 1) := by
    intro u hu
    simpa [hc₁] using hπ₁_affine_right hu
  have hπ₂_right_fixed :
      Set.EqOn π₂ (fun u ↦ sigma * u + (c₂ + d₂')) (Set.Icc γ 1) := by
    intro u hu
    simpa [hc₂] using hπ₂_affine_right hu
  constructor
  · exact eqOn_ofSharedAffineSlopeAndPointValue hγ_mem hπ_source_right hπ₁_right_fixed hγ_eq₁
  · exact eqOn_ofSharedAffineSlopeAndPointValue hγ_mem hπ_source_right hπ₂_right_fixed hγ_eq₂

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: after the left and central
cells are rigid, symmetry transports equality to the descending cell and the right cell. -/
theorem midpointComponentsEqOnRemainingCellsOfPi2
    {t f : ℝ} (ht : 0 < t) (hstrong : 2 / 3 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_23_pi2 t f) π₁
        (Set.Icc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f)) ∧
      Set.EqOn (example_6_23_pi2 t f) π₂
        (Set.Icc (pi2LeftBreakpoint t f) (pi2MiddleLeftBreakpoint t f)) ∧
          Set.EqOn (example_6_23_pi2 t f) π₁
            (Set.Icc (pi2MiddleRightBreakpoint t f) 1) ∧
            Set.EqOn (example_6_23_pi2 t f) π₂
              (Set.Icc (pi2MiddleRightBreakpoint t f) 1) := by
  have hft : 1 / 2 + t ≤ f := by
    linarith
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  let π : ℝ → ℝ := example_6_23_pi2 t f
  have hπ : pure_integer_minimal_valid_function_on_R f π :=
    example623Pi2Minimal ht hft hf
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  have hright := midpointComponentsEqOnRightCellOfPi2 ht hstrong hf hπ₁ hπ₂ hmid
  have hsum : β + γ = 2 - f := by
    simpa [β, γ] using pi2MiddleBreakpoints_sum ht hft hf
  have hπ_reflect (u : ℝ) : π u + π (1 + α - u) = 1 := by
    have hbase := example_6_23_pi2_symmetryReal ht hft hf u
    have hshift :
        π (-f - u) = π (1 + α - u) := by
      calc
        π (-f - u) = π ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [π, one_mul, add_assoc, add_left_comm, add_comm] using
            ((example_6_23_pi2_periodic t f).int_mul (2 : ℤ) (-f - u)).symm
        _ = π (2 - f - u) := by
          congr 1
          ring
        _ = π (1 + α - u) := by
          dsimp [α, pi2LeftBreakpoint]
          ring
    rw [hshift] at hbase
    exact hbase
  have hπ₁_reflect (u : ℝ) : π₁ u + π₁ (1 + α - u) = 1 := by
    have hbase :
        π₁ u + π₁ (-f - u) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ u)
    have hshift :
        π₁ (-f - u) = π₁ (1 + α - u) := by
      calc
        π₁ (-f - u) = π₁ ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [one_mul, add_assoc, add_left_comm, add_comm] using
            (hπ₁_periodic.int_mul (2 : ℤ) (-f - u)).symm
        _ = π₁ (2 - f - u) := by
          congr 1
          ring
        _ = π₁ (1 + α - u) := by
          dsimp [α, pi2LeftBreakpoint]
          ring
    rw [hshift] at hbase
    exact hbase
  have hπ₂_reflect (u : ℝ) : π₂ u + π₂ (1 + α - u) = 1 := by
    have hbase :
        π₂ u + π₂ (-f - u) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ u)
    have hshift :
        π₂ (-f - u) = π₂ (1 + α - u) := by
      calc
        π₂ (-f - u) = π₂ ((((2 : ℤ) : ℝ) * 1) + (-f - u)) := by
          simpa [one_mul, add_assoc, add_left_comm, add_comm] using
            (hπ₂_periodic.int_mul (2 : ℤ) (-f - u)).symm
        _ = π₂ (2 - f - u) := by
          congr 1
          ring
        _ = π₂ (1 + α - u) := by
          dsimp [α, pi2LeftBreakpoint]
          ring
    rw [hshift] at hbase
    exact hbase
  have hdesc₁ :
      Set.EqOn π π₁ (Set.Icc α β) := by
    intro u hu
    let v : ℝ := 1 + α - u
    have hv_mem : v ∈ Set.Icc γ 1 := by
      constructor
      · dsimp [v]
        have hupper : u ≤ β := hu.2
        rw [← hsum]
        linarith
      · dsimp [v]
        have hlower : α ≤ u := hu.1
        linarith
    have hv_eq : π v = π₁ v := by
      exact hright.1 hv_mem
    have hsource := hπ_reflect u
    have hcomponent := hπ₁_reflect u
    dsimp [v] at hv_eq
    linarith
  have hdesc₂ :
      Set.EqOn π π₂ (Set.Icc α β) := by
    intro u hu
    let v : ℝ := 1 + α - u
    have hv_mem : v ∈ Set.Icc γ 1 := by
      constructor
      · dsimp [v]
        have hupper : u ≤ β := hu.2
        rw [← hsum]
        linarith
      · dsimp [v]
        have hlower : α ≤ u := hu.1
        linarith
    have hv_eq : π v = π₂ v := by
      exact hright.2 hv_mem
    have hsource := hπ_reflect u
    have hcomponent := hπ₂_reflect u
    dsimp [v] at hv_eq
    linarith
  exact ⟨hdesc₁, hdesc₂, hright.1, hright.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every scalar midpoint
component of `example_6_23_pi2` agrees with it throughout one fundamental interval. -/
theorem midpointComponentsEqOnUnitIntervalOfPi2
    {t f : ℝ} (ht : 0 < t) (hstrong : 2 / 3 + t ≤ f) (hf : f < 1)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_23_pi2 t f) π₁ (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn (example_6_23_pi2 t f) π₂ (Set.Icc (0 : ℝ) 1) := by
  have hft : 1 / 2 + t ≤ f := by
    linarith
  let α : ℝ := pi2LeftBreakpoint t f
  let β : ℝ := pi2MiddleLeftBreakpoint t f
  let γ : ℝ := pi2MiddleRightBreakpoint t f
  have hleft := midpointComponentsEqOnLeftCellOfPi2 ht hft hf hπ₁ hπ₂ hmid
  have hcentral := midpointComponentsEqOnCentralCellOfPi2 ht hstrong hf hπ₁ hπ₂ hmid
  have hremaining := midpointComponentsEqOnRemainingCellsOfPi2 ht hstrong hf hπ₁ hπ₂ hmid
  constructor
  · intro u hu
    by_cases hu_left : u ≤ α
    · exact hleft.1 (by simpa [α] using ⟨hu.1, hu_left⟩)
    · by_cases hu_desc : u ≤ β
      · exact hremaining.1 (by simpa [α, β] using ⟨le_of_lt (lt_of_not_ge hu_left), hu_desc⟩)
      · by_cases hu_central : u ≤ γ
        · exact hcentral.1 (by simpa [β, γ] using ⟨le_of_lt (lt_of_not_ge hu_desc), hu_central⟩)
        · exact hremaining.2.2.1 (by simpa [γ] using ⟨le_of_not_ge hu_central, hu.2⟩)
  · intro u hu
    by_cases hu_left : u ≤ α
    · exact hleft.2 (by simpa [α] using ⟨hu.1, hu_left⟩)
    · by_cases hu_desc : u ≤ β
      · exact hremaining.2.1 (by simpa [α, β] using ⟨le_of_lt (lt_of_not_ge hu_left), hu_desc⟩)
      · by_cases hu_central : u ≤ γ
        · exact hcentral.2 (by simpa [β, γ] using ⟨le_of_lt (lt_of_not_ge hu_desc), hu_central⟩)
        · exact hremaining.2.2.2 (by simpa [γ] using ⟨le_of_not_ge hu_central, hu.2⟩)

/-- Under the repaired parameter range `0 < t`, `2 / 3 + t ≤ f`, and `f < 1`, the function `π₂`
from Example 6.23 is an extreme valid function for the one-dimensional pure integer infinite
relaxation. -/
instance exercise_6_18_pi2_extreme
    {t f : ℝ} [ht : Fact (0 < t)] [hstrong : Fact (2 / 3 + t ≤ f)] [hf : Fact (f < 1)] :
    pure_integer_extreme_valid_function_on_R f
      (example_6_23_pi2 t f) := by
  have hft : 1 / 2 + t ≤ f := by
    linarith [hstrong.out]
  have hminimal := example623Pi2Minimal ht.out hft hf.out
  refine
    { nonneg := hminimal.nonneg
      one_le_sum := hminimal.one_le_sum
      eq_of_eq_midpoint := ?_ }
  intro π₁Vec π₂Vec hπ₁Vec hπ₂Vec hmidVec
  let π₁ : ℝ → ℝ := fun r ↦ π₁Vec (fun _ : Fin 1 ↦ r)
  let π₂ : ℝ → ℝ := fun r ↦ π₂Vec (fun _ : Fin 1 ↦ r)
  have hπ₁_vec_eq : π₁Vec = fun r : Fin 1 → ℝ ↦ π₁ (r 0) := by
    -- Scalarize the first component once, using that `Fin 1` has only coordinate `0`.
    ext r
    change π₁Vec r = π₁Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₂_vec_eq : π₂Vec = fun r : Fin 1 → ℝ ↦ π₂ (r 0) := by
    -- Apply the same scalarization to the second component.
    ext r
    change π₂Vec r = π₂Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₁ : pure_integer_valid_function_on_R f π₁ := by
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f)
      (fun r : Fin 1 → ℝ ↦ π₁ (r 0))
    simpa [hπ₁_vec_eq] using hπ₁Vec
  have hπ₂ : pure_integer_valid_function_on_R f π₂ := by
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f)
      (fun r : Fin 1 → ℝ ↦ π₂ (r 0))
    simpa [hπ₂_vec_eq] using hπ₂Vec
  have hmid :
      example_6_23_pi2 t f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂ := by
    -- Evaluate the vector midpoint identity on constant one-dimensional vectors.
    ext r
    have hpoint := congrFun hmidVec (fun _ : Fin 1 ↦ r)
    simpa [π₁, π₂, Pi.add_apply, Pi.smul_apply] using hpoint
  have hunit := midpointComponentsEqOnUnitIntervalOfPi2 ht.out hstrong.out hf.out hπ₁ hπ₂ hmid
  rcases midpointComponentsAreMinimalValidFunctionOnR hminimal hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hminimal with
    ⟨hsource_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  have hEq₁ : example_6_23_pi2 t f = π₁ :=
    eq_of_eqOn_unitInterval_of_onePeriodic hsource_periodic hπ₁_periodic hunit.1
  have hEq₂ : example_6_23_pi2 t f = π₂ :=
    eq_of_eqOn_unitInterval_of_onePeriodic hsource_periodic hπ₂_periodic hunit.2
  constructor
  · ext r
    simpa [hπ₁_vec_eq] using congrFun hEq₁ (r 0)
  · ext r
    simpa [hπ₂_vec_eq] using congrFun hEq₂ (r 0)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean

Exercise 6.18. Assume `t > 0`, `2 / 3 + t ≤ f`, and `f < 1`. Show that the function `π₂` in
Example 6.23 is extreme. -/
theorem exercise_6_18_pi2_is_extreme
    {t f : ℝ} (ht : 0 < t) (hstrong : 2 / 3 + t ≤ f) (hf : f < 1) :
    pure_integer_extreme_valid_function_on_R f
      (example_6_23_pi2 t f) := by
  -- Supply the three explicit hypotheses to the instance wrapper proved above.
  exact @exercise_6_18_pi2_extreme t f ⟨ht⟩ ⟨hstrong⟩ ⟨hf⟩

end Exercise618
