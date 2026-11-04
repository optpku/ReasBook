/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_18

section Exercise618Counterexample

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the lower endpoints of the
eight affine cells of a signed counterexample component. -/
noncomputable abbrev pi2CounterexamplePieceLower : Fin 8 → ℝ :=
  ![(0 : ℝ), 1 / 10, 11 / 35, 33 / 70, 143 / 280, 33 / 56, 22 / 35, 11 / 14]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the upper endpoints of the
eight affine cells of a signed counterexample component. -/
noncomputable abbrev pi2CounterexamplePieceUpper : Fin 8 → ℝ :=
  ![(1 / 10 : ℝ), 11 / 35, 33 / 70, 143 / 280, 33 / 56, 22 / 35, 11 / 14, 1]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the slopes of the eight
affine cells after adding `sigma / 12` times the perturbation. -/
noncomputable abbrev pi2CounterexamplePieceSlope (sigma : ℝ) : Fin 8 → ℝ :=
  ![(10 : ℝ), -10 / 3, 10 / 11, 10 / 11 + sigma * 70 / 33,
    10 / 11 - sigma * 70 / 33, 10 / 11 + sigma * 70 / 33, 10 / 11, -10 / 3]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the intercepts of the eight
affine cells after adding `sigma / 12` times the perturbation. -/
noncomputable abbrev pi2CounterexamplePieceIntercept (sigma : ℝ) : Fin 8 → ℝ :=
  ![(0 : ℝ), 4 / 3, 0, -sigma, sigma * 7 / 6, -sigma * 4 / 3, 0, 10 / 3]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation vanishes
before its support begins. -/
theorem pi2CounterexamplePerturbation_eq_zero_beforeSupport
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (33 / 70)) :
    pi2CounterexamplePerturbation u = 0 := by
  -- Reduce to the raw branch on `[0,1)` and select its initial zero piece.
  rw [pi2CounterexamplePerturbation,
    onePeriodicExtension_eq_on_Ico _ hu.1 (lt_of_le_of_lt hu.2 (by norm_num))]
  simp [pi2CounterexamplePerturbationOnUnitInterval, hu.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation uses its
first rising affine formula on the first support cell. -/
theorem pi2CounterexamplePerturbation_eq_on_firstRisingCell
    {u : ℝ} (hu : u ∈ Set.Icc ((33 : ℝ) / 70) (143 / 280)) :
    pi2CounterexamplePerturbation u =
      (u - 33 / 70) / (143 / 280 - 33 / 70) := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  -- At the left endpoint both adjacent formulas are zero; elsewhere the rising branch is active.
  rw [pi2CounterexamplePerturbation,
    onePeriodicExtension_eq_on_Ico _ hu0 hu1]
  by_cases hleft : u = 33 / 70
  · subst u
    norm_num [pi2CounterexamplePerturbationOnUnitInterval]
  · have hnot_left : ¬ u ≤ (33 : ℝ) / 70 := by
      exact not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hleft))
    simp [pi2CounterexamplePerturbationOnUnitInterval, hnot_left, hu.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation uses its
descending affine formula across the middle support cell. -/
theorem pi2CounterexamplePerturbation_eq_on_descendingCell
    {u : ℝ} (hu : u ∈ Set.Icc ((143 : ℝ) / 280) (33 / 56)) :
    pi2CounterexamplePerturbation u =
      (11 / 20 - u) / (11 / 20 - 143 / 280) := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  -- At the left endpoint the rising and descending formulas agree; afterwards use the latter.
  rw [pi2CounterexamplePerturbation,
    onePeriodicExtension_eq_on_Ico _ hu0 hu1]
  by_cases hleft : u = 143 / 280
  · subst u
    norm_num [pi2CounterexamplePerturbationOnUnitInterval]
  · have hnot_first : ¬ u ≤ (33 : ℝ) / 70 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_peak : ¬ u ≤ (143 : ℝ) / 280 := by
      exact not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hleft))
    simp [pi2CounterexamplePerturbationOnUnitInterval, hnot_first, hnot_peak, hu.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation uses its
last rising affine formula on the final support cell. -/
theorem pi2CounterexamplePerturbation_eq_on_lastRisingCell
    {u : ℝ} (hu : u ∈ Set.Icc ((33 : ℝ) / 56) (22 / 35)) :
    pi2CounterexamplePerturbation u =
      (u - 22 / 35) / (22 / 35 - 33 / 56) := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (by norm_num)
  -- At the left endpoint both nonzero affine formulas give `-1`; afterwards use the last one.
  rw [pi2CounterexamplePerturbation,
    onePeriodicExtension_eq_on_Ico _ hu0 hu1]
  by_cases hleft : u = 33 / 56
  · subst u
    norm_num [pi2CounterexamplePerturbationOnUnitInterval]
  · have hnot_first : ¬ u ≤ (33 : ℝ) / 70 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_peak : ¬ u ≤ (143 : ℝ) / 280 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_trough : ¬ u ≤ (33 : ℝ) / 56 := by
      exact not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hleft))
    simp [pi2CounterexamplePerturbationOnUnitInterval, hnot_first, hnot_peak,
      hnot_trough, hu.2]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the perturbation vanishes
after its support ends on the closed unit interval. -/
theorem pi2CounterexamplePerturbation_eq_zero_afterSupport
    {u : ℝ} (hu : u ∈ Set.Icc ((22 : ℝ) / 35) 1) :
    pi2CounterexamplePerturbation u = 0 := by
  by_cases hright : u = 1
  · subst u
    norm_num [pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
      onePeriodicExtension, Int.fract]
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hright
  -- At the support endpoint the last affine formula is zero; beyond it the zero branch is active.
  rw [pi2CounterexamplePerturbation,
    onePeriodicExtension_eq_on_Ico _ hu0 hu1]
  by_cases hleft : u = 22 / 35
  · subst u
    norm_num [pi2CounterexamplePerturbationOnUnitInterval]
  · have hnot_first : ¬ u ≤ (33 : ℝ) / 70 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_peak : ¬ u ≤ (143 : ℝ) / 280 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_trough : ¬ u ≤ (33 : ℝ) / 56 := by
      exact not_le.mpr (lt_of_lt_of_le (by norm_num) hu.1)
    have hnot_right : ¬ u ≤ (22 : ℝ) / 35 := by
      exact not_le.mpr (lt_of_le_of_ne hu.1 (Ne.symm hleft))
    simp [pi2CounterexamplePerturbationOnUnitInterval, hnot_first, hnot_peak,
      hnot_trough, hnot_right]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every one of the eight
counterexample cells has ordered endpoints. -/
theorem pi2CounterexamplePieceLowerLeUpper :
    ∀ j : Fin 8, pi2CounterexamplePieceLower j ≤ pi2CounterexamplePieceUpper j := by
  -- Each cell endpoint comparison is an exact rational inequality.
  intro j
  fin_cases j <;> norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the eight consecutive
counterexample cells cover `[0,1]`. -/
theorem pi2CounterexamplePieceCover :
    Set.Icc (0 : ℝ) 1 ⊆
      ⋃ j : Fin 8,
        Set.Icc (pi2CounterexamplePieceLower j) (pi2CounterexamplePieceUpper j) := by
  intro x hx
  -- Select the first rational upper endpoint containing `x`.
  by_cases h₀ : x ≤ (1 : ℝ) / 10
  · refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at ⊢ h₀
    exact ⟨hx.1, h₀⟩
  by_cases h₁ : x ≤ (11 : ℝ) / 35
  · refine Set.mem_iUnion.mpr ⟨1, ?_⟩
    norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at ⊢ h₀ h₁
    exact ⟨h₀.le, h₁⟩
  by_cases h₂ : x ≤ (33 : ℝ) / 70
  · refine Set.mem_iUnion.mpr ⟨2, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₁, h₂⟩
  by_cases h₃ : x ≤ (143 : ℝ) / 280
  · refine Set.mem_iUnion.mpr ⟨3, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₂, h₃⟩
  by_cases h₄ : x ≤ (33 : ℝ) / 56
  · refine Set.mem_iUnion.mpr ⟨4, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₃, h₄⟩
  by_cases h₅ : x ≤ (22 : ℝ) / 35
  · refine Set.mem_iUnion.mpr ⟨5, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₄, h₅⟩
  by_cases h₆ : x ≤ (11 : ℝ) / 14
  · refine Set.mem_iUnion.mpr ⟨6, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₅, h₆⟩
  · refine Set.mem_iUnion.mpr ⟨7, ?_⟩
    simpa [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] using
      ⟨le_of_not_ge h₆, hx.2⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: on each of its eight cells,
a signed counterexample component agrees with the recorded affine formula. -/
theorem pi2CounterexamplePieceEqAffine (sigma : ℝ) :
    ∀ (j : Fin 8) (x : ℝ),
      x ∈ Set.Icc (pi2CounterexamplePieceLower j) (pi2CounterexamplePieceUpper j) →
        pi2CounterexampleComponent sigma x =
          pi2CounterexamplePieceSlope sigma j * x +
            pi2CounterexamplePieceIntercept sigma j := by
  intro j x hx
  -- Each finite case combines one source affine formula with one perturbation affine formula.
  fin_cases j
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_leftCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc (0 : ℝ)
          (pi2LeftBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2LeftBreakpoint]
        exact hx)
    have hperturb := pi2CounterexamplePerturbation_eq_zero_beforeSupport
      (show x ∈ Set.Icc (0 : ℝ) (33 / 70) by constructor <;> linarith [hx.2])
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num [div_eq_mul_inv]
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedDescendingCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2LeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleLeftBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2LeftBreakpoint, pi2MiddleLeftBreakpoint] at ⊢ hx
        exact hx)
    have hperturb := pi2CounterexamplePerturbation_eq_zero_beforeSupport
      (show x ∈ Set.Icc (0 : ℝ) (33 / 70) by constructor <;> linarith [hx.1, hx.2])
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedCentralCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleLeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at ⊢ hx
        constructor <;> linarith [hx.1, hx.2])
    have hperturb := pi2CounterexamplePerturbation_eq_zero_beforeSupport
      (show x ∈ Set.Icc (0 : ℝ) (33 / 70) by
        exact ⟨by linarith [hx.1], hx.2⟩)
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedCentralCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleLeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at ⊢ hx
        constructor <;> linarith [hx.1, hx.2])
    have hperturb := pi2CounterexamplePerturbation_eq_on_firstRisingCell hx
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedCentralCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleLeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at ⊢ hx
        constructor <;> linarith [hx.1, hx.2])
    have hperturb := pi2CounterexamplePerturbation_eq_on_descendingCell hx
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedCentralCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleLeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at ⊢ hx
        constructor <;> linarith [hx.1, hx.2])
    have hperturb := pi2CounterexamplePerturbation_eq_on_lastRisingCell hx
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedCentralCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleLeftBreakpoint ((3 : ℝ) / 10) (9 / 10))
          (pi2MiddleRightBreakpoint (3 / 10) (9 / 10)) by
        norm_num [pi2MiddleLeftBreakpoint, pi2MiddleRightBreakpoint] at ⊢ hx
        constructor <;> linarith [hx.1, hx.2])
    have hperturb := pi2CounterexamplePerturbation_eq_zero_afterSupport
      (show x ∈ Set.Icc ((22 : ℝ) / 35) 1 by
        exact ⟨hx.1, by linarith [hx.2]⟩)
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring
  · norm_num [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper] at hx
    have hsource := example_6_23_pi2_eq_on_closedRightCell
      (t := (3 : ℝ) / 10) (f := (9 : ℝ) / 10) (u := x)
      (by norm_num) (by norm_num) (by norm_num)
      (show x ∈ Set.Icc
          (pi2MiddleRightBreakpoint ((3 : ℝ) / 10) (9 / 10)) 1 by
        norm_num [pi2MiddleRightBreakpoint] at ⊢ hx
        exact hx)
    have hperturb := pi2CounterexamplePerturbation_eq_zero_afterSupport
      (show x ∈ Set.Icc ((22 : ℝ) / 35) 1 by constructor <;> linarith [hx.1, hx.2])
    simp only [pi2CounterexamplePieceSlope, pi2CounterexamplePieceIntercept]
    dsimp [pi2CounterexampleComponent]
    rw [hsource, hperturb]
    norm_num
    ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the signed component has an
explicit eight-cell piecewise-linear witness on `[0,1]`. -/
noncomputable abbrev pi2CounterexampleComponentPiecewiseOnUnitInterval (sigma : ℝ) :
    PiecewiseLinearOnInterval 0 1 (pi2CounterexampleComponent sigma) :=
  { pieces := 8
    lower := pi2CounterexamplePieceLower
    upper := pi2CounterexamplePieceUpper
    slope := pi2CounterexamplePieceSlope sigma
    intercept := pi2CounterexamplePieceIntercept sigma
    lower_le_upper := pi2CounterexamplePieceLowerLeUpper
    cover := pi2CounterexamplePieceCover
    eq_affine := pi2CounterexamplePieceEqAffine sigma }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: every source-facing
breakpoint of a signed component is one of its nine rational cell endpoints. -/
theorem pi2CounterexampleComponent_breakpointCases
    {sigma x : ℝ} (hx : Exercise617Breakpoint (pi2CounterexampleComponent sigma) x) :
    x = 0 ∨ x = 1 / 10 ∨ x = 11 / 14 ∨ x = 11 / 35 ∨
      x = 22 / 35 ∨ x = 33 / 56 ∨ x = 33 / 70 ∨
        x = 143 / 280 ∨ x = 1 := by
  classical
  -- The witness-independent breakpoint belongs to the checkpoint set of the eight-cell model.
  have hxCheckpoint :=
    exercise617Breakpoint_mem_breakpointCheckpoints
      (hpiece := pi2CounterexampleComponentPiecewiseOnUnitInterval sigma) hx
  have hxCases :
      x = 0 ∨ x = 1 ∨
        x ∈ (pi2CounterexampleComponentPiecewiseOnUnitInterval sigma).breakpoints := by
    simpa [breakpointCheckpoints] using hxCheckpoint
  rcases hxCases with hxZero | hxOne | hxRaw
  · exact Or.inl hxZero
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr hxOne)))))))
  · -- Expanding the endpoint vectors leaves exactly the displayed rational points.
    simp only [pi2CounterexampleComponentPiecewiseOnUnitInterval,
      PiecewiseLinearOnInterval.breakpoints, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and] at hxRaw
    rcases hxRaw.1 with ⟨j, hj⟩ | ⟨j, hj⟩
    · fin_cases j <;>
        simp_all [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    · fin_cases j <;>
        simp_all [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: a strict slope drop between
two consecutive recorded cells prevents local convexity at their common endpoint. -/
theorem pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    {sigma : ℝ} {left right : Fin 8}
    (hmeet : pi2CounterexamplePieceUpper left = pi2CounterexamplePieceLower right)
    (hleft : pi2CounterexamplePieceLower left < pi2CounterexamplePieceUpper left)
    (hright : pi2CounterexamplePieceLower right < pi2CounterexamplePieceUpper right)
    (hdrop : pi2CounterexamplePieceSlope sigma right <
      pi2CounterexamplePieceSlope sigma left) :
    ¬ LocallyConvexAt (pi2CounterexampleComponent sigma)
      (pi2CounterexamplePieceUpper left) := by
  -- Feed the two adjacent affine cells to the general slope-drop obstruction.
  refine notLocallyConvexAt_of_affineSlopeDrop
    (a := pi2CounterexamplePieceLower left)
    (x := pi2CounterexamplePieceUpper left)
    (b := pi2CounterexamplePieceUpper right)
    (mLeft := pi2CounterexamplePieceSlope sigma left)
    (mRight := pi2CounterexamplePieceSlope sigma right)
    (cLeft := pi2CounterexamplePieceIntercept sigma left)
    (cRight := pi2CounterexamplePieceIntercept sigma right)
    hleft ?_ ?_ ?_ hdrop
  · simpa [hmeet] using hright
  · exact pi2CounterexamplePieceEqAffine sigma left
  · intro y hy
    have hyRight :
        y ∈ Set.Icc (pi2CounterexamplePieceLower right)
          (pi2CounterexamplePieceUpper right) := by
      simpa [hmeet] using hy
    exact pi2CounterexamplePieceEqAffine sigma right y hyRight

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: both signed components have
a strict downward corner at `1 / 10`. -/
theorem pi2CounterexampleComponent_notLocallyConvexAt_oneTenth (sigma : ℝ) :
    ¬ LocallyConvexAt (pi2CounterexampleComponent sigma) (1 / 10) := by
  have hmeet : pi2CounterexamplePieceUpper 0 = pi2CounterexamplePieceLower 1 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 0 < pi2CounterexamplePieceUpper 0 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hright : pi2CounterexamplePieceLower 1 < pi2CounterexamplePieceUpper 1 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope sigma 1 <
      pi2CounterexamplePieceSlope sigma 0 := by
    simp [pi2CounterexamplePieceSlope]
    all_goals norm_num
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: both signed components have
a strict downward corner at `11 / 14`. -/
theorem pi2CounterexampleComponent_notLocallyConvexAt_elevenFourteenths (sigma : ℝ) :
    ¬ LocallyConvexAt (pi2CounterexampleComponent sigma) (11 / 14) := by
  have hmeet : pi2CounterexamplePieceUpper 6 = pi2CounterexamplePieceLower 7 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 6 < pi2CounterexamplePieceUpper 6 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hright : pi2CounterexamplePieceLower 7 < pi2CounterexamplePieceUpper 7 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope sigma 7 <
      pi2CounterexamplePieceSlope sigma 6 := by
    simp [pi2CounterexamplePieceSlope]
    all_goals norm_num
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed component
has a strict downward corner at `22 / 35`. -/
theorem pi2CounterexampleComponent_one_notLocallyConvexAt_twentyTwoThirtyFifths :
    ¬ LocallyConvexAt (pi2CounterexampleComponent 1) (22 / 35) := by
  have hmeet : pi2CounterexamplePieceUpper 5 = pi2CounterexamplePieceLower 6 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 5 < pi2CounterexamplePieceUpper 5 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hright : pi2CounterexamplePieceLower 6 < pi2CounterexamplePieceUpper 6 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope 1 6 < pi2CounterexamplePieceSlope 1 5 := by
    simp [pi2CounterexamplePieceSlope]
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed component
has a strict downward corner at `143 / 280`. -/
theorem pi2CounterexampleComponent_one_notLocallyConvexAt_oneFortyThreeTwoEightieths :
    ¬ LocallyConvexAt (pi2CounterexampleComponent 1) (143 / 280) := by
  have hmeet : pi2CounterexamplePieceUpper 3 = pi2CounterexamplePieceLower 4 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 3 < pi2CounterexamplePieceUpper 3 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hright : pi2CounterexamplePieceLower 4 < pi2CounterexamplePieceUpper 4 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope 1 4 < pi2CounterexamplePieceSlope 1 3 := by
    simp [pi2CounterexamplePieceSlope]
    all_goals norm_num
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed component
has a strict downward corner at `33 / 56`. -/
theorem pi2CounterexampleComponent_negOne_notLocallyConvexAt_thirtyThreeFiftySixths :
    ¬ LocallyConvexAt (pi2CounterexampleComponent (-1)) (33 / 56) := by
  have hmeet : pi2CounterexamplePieceUpper 4 = pi2CounterexamplePieceLower 5 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 4 < pi2CounterexamplePieceUpper 4 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hright : pi2CounterexamplePieceLower 5 < pi2CounterexamplePieceUpper 5 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope (-1) 5 <
      pi2CounterexamplePieceSlope (-1) 4 := by
    simp [pi2CounterexamplePieceSlope]
    all_goals norm_num
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed component
has a strict downward corner at `33 / 70`. -/
theorem pi2CounterexampleComponent_negOne_notLocallyConvexAt_thirtyThreeSeventieths :
    ¬ LocallyConvexAt (pi2CounterexampleComponent (-1)) (33 / 70) := by
  have hmeet : pi2CounterexamplePieceUpper 2 = pi2CounterexamplePieceLower 3 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
  have hleft : pi2CounterexamplePieceLower 2 < pi2CounterexamplePieceUpper 2 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hright : pi2CounterexamplePieceLower 3 < pi2CounterexamplePieceUpper 3 := by
    simp [pi2CounterexamplePieceLower, pi2CounterexamplePieceUpper]
    all_goals norm_num
  have hdrop : pi2CounterexamplePieceSlope (-1) 3 <
      pi2CounterexamplePieceSlope (-1) 2 := by
    simp [pi2CounterexamplePieceSlope]
    all_goals norm_num
  have hnot := pi2CounterexampleComponent_notLocallyConvexAt_of_adjacentSlopeDrop
    hmeet hleft hright hdrop
  simpa [pi2CounterexamplePieceUpper, Matrix.cons_val_zero] using hnot

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: local convexity restricts
the positive signed component to five rational checkpoints. -/
theorem pi2CounterexampleComponent_one_locallyConvexBreakpointCases
    {x : ℝ} (hx : Exercise617Breakpoint (pi2CounterexampleComponent 1) x)
    (hconv : LocallyConvexAt (pi2CounterexampleComponent 1) x) :
    x = 0 ∨ x = 1 ∨ x = 11 / 35 ∨ x = 33 / 70 ∨ x = 33 / 56 := by
  -- Enumerate the nine endpoints and reject the four strict downward corners.
  rcases pi2CounterexampleComponent_breakpointCases hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (pi2CounterexampleComponent_notLocallyConvexAt_oneTenth 1 hconv).elim
  · exact
      (pi2CounterexampleComponent_notLocallyConvexAt_elevenFourteenths 1 hconv).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact
      (pi2CounterexampleComponent_one_notLocallyConvexAt_twentyTwoThirtyFifths hconv).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact
      (pi2CounterexampleComponent_one_notLocallyConvexAt_oneFortyThreeTwoEightieths
        hconv).elim
  · exact Or.inr (Or.inl rfl)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: local convexity restricts
the negative signed component to five rational checkpoints. -/
theorem pi2CounterexampleComponent_negOne_locallyConvexBreakpointCases
    {x : ℝ} (hx : Exercise617Breakpoint (pi2CounterexampleComponent (-1)) x)
    (hconv : LocallyConvexAt (pi2CounterexampleComponent (-1)) x) :
    x = 0 ∨ x = 1 ∨ x = 11 / 35 ∨ x = 143 / 280 ∨ x = 22 / 35 := by
  -- The opposite sign reverses the three perturbation corners that remain locally convex.
  rcases pi2CounterexampleComponent_breakpointCases hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (pi2CounterexampleComponent_notLocallyConvexAt_oneTenth (-1) hconv).elim
  · exact
      (pi2CounterexampleComponent_notLocallyConvexAt_elevenFourteenths (-1) hconv).elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exact
      (pi2CounterexampleComponent_negOne_notLocallyConvexAt_thirtyThreeFiftySixths
        hconv).elim
  · exact
      (pi2CounterexampleComponent_negOne_notLocallyConvexAt_thirtyThreeSeventieths
        hconv).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed component
is subadditive at every pair of locally convex source-facing breakpoints. -/
theorem pi2CounterexampleComponent_one_subadditiveAtLocallyConvexBreakpoints
    {a b : ℝ} (ha : Exercise617Breakpoint (pi2CounterexampleComponent 1) a)
    (hb : Exercise617Breakpoint (pi2CounterexampleComponent 1) b)
    (hconvA : LocallyConvexAt (pi2CounterexampleComponent 1) a)
    (hconvB : LocallyConvexAt (pi2CounterexampleComponent 1) b) :
    pi2CounterexampleComponent 1 (a + b) ≤
      pi2CounterexampleComponent 1 a + pi2CounterexampleComponent 1 b := by
  -- Reduce to the five-by-five rational table supplied by the slope-drop analysis.
  rcases pi2CounterexampleComponent_one_locallyConvexBreakpointCases ha hconvA with
    rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases pi2CounterexampleComponent_one_locallyConvexBreakpointCases hb hconvB with
      rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [pi2CounterexampleComponent, example_6_23_pi2_apply,
      pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
      onePeriodicExtension, Int.fract]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed component
is subadditive at every pair of locally convex source-facing breakpoints. -/
theorem pi2CounterexampleComponent_negOne_subadditiveAtLocallyConvexBreakpoints
    {a b : ℝ} (ha : Exercise617Breakpoint (pi2CounterexampleComponent (-1)) a)
    (hb : Exercise617Breakpoint (pi2CounterexampleComponent (-1)) b)
    (hconvA : LocallyConvexAt (pi2CounterexampleComponent (-1)) a)
    (hconvB : LocallyConvexAt (pi2CounterexampleComponent (-1)) b) :
    pi2CounterexampleComponent (-1) (a + b) ≤
      pi2CounterexampleComponent (-1) a + pi2CounterexampleComponent (-1) b := by
  -- The opposite sign has its own five-by-five rational checkpoint table.
  rcases pi2CounterexampleComponent_negOne_locallyConvexBreakpointCases ha hconvA with
    rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases pi2CounterexampleComponent_negOne_locallyConvexBreakpointCases hb hconvB with
      rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [pi2CounterexampleComponent, example_6_23_pi2_apply,
      pi2CounterexamplePerturbation, pi2CounterexamplePerturbationOnUnitInterval,
      onePeriodicExtension, Int.fract]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed component
is globally subadditive. -/
theorem pi2CounterexampleComponent_one_subadditive :
    Function.Subadditive (pi2CounterexampleComponent 1) := by
  -- Exercise 6.17 promotes the finite locally-convex checkpoint calculation globally.
  have hsymmetry :
      ∀ r : ℝ, pi2CounterexampleComponent 1 r +
        pi2CounterexampleComponent 1 (-(9 / 10) - r) = 1 := by
    intro r
    have hsym := pi2CounterexampleComponent_symmetry 1 r
    convert hsym using 1
    ring
  refine exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
    (f := (9 : ℝ) / 10) (pi2CounterexampleComponent_periodic 1)
    (pi2CounterexampleComponent_continuous 1)
    (pi2CounterexampleComponent_nonneg (Or.inl rfl))
    (pi2CounterexampleComponent_zero 1)
    (pi2CounterexampleComponentPiecewiseOnUnitInterval 1) hsymmetry ?_
  intro a b ha hb hconvA hconvB
  exact pi2CounterexampleComponent_one_subadditiveAtLocallyConvexBreakpoints
    ha hb hconvA hconvB

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed component
is globally subadditive. -/
theorem pi2CounterexampleComponent_negOne_subadditive :
    Function.Subadditive (pi2CounterexampleComponent (-1)) := by
  -- Apply the same global criterion to the mirrored finite checkpoint calculation.
  have hsymmetry :
      ∀ r : ℝ, pi2CounterexampleComponent (-1) r +
        pi2CounterexampleComponent (-1) (-(9 / 10) - r) = 1 := by
    intro r
    have hsym := pi2CounterexampleComponent_symmetry (-1) r
    convert hsym using 1
    ring
  refine exercise_6_17_subadditivity_check_on_locally_convex_breakpoints_suffices
    (f := (9 : ℝ) / 10) (pi2CounterexampleComponent_periodic (-1))
    (pi2CounterexampleComponent_continuous (-1))
    (pi2CounterexampleComponent_nonneg (Or.inr rfl))
    (pi2CounterexampleComponent_zero (-1))
    (pi2CounterexampleComponentPiecewiseOnUnitInterval (-1)) hsymmetry ?_
  intro a b ha hb hconvA hconvB
  exact pi2CounterexampleComponent_negOne_subadditiveAtLocallyConvexBreakpoints
    ha hb hconvA hconvB

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed component
is a minimal valid function for the counterexample right-hand side. -/
theorem pi2CounterexampleComponent_one_minimal :
    pure_integer_minimal_valid_function_on_R (9 / 10) (pi2CounterexampleComponent 1) := by
  -- Package nonnegativity, subadditivity, periodicity, and symmetry via Theorem 6.22.
  change pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ (9 : ℝ) / 10)
    (fun r : Fin 1 → ℝ ↦ pi2CounterexampleComponent 1 (r 0))
  refine pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry
    ?_ ?_ ?_ ?_ ?_
  · intro r
    exact pi2CounterexampleComponent_nonneg (Or.inl rfl) (r 0)
  · exact pi2CounterexampleComponent_zero 1
  · intro r s
    exact pi2CounterexampleComponent_one_subadditive (r 0) (s 0)
  · intro r w
    have hperiod := (pi2CounterexampleComponent_periodic 1).int_mul (w 0) (r 0)
    simpa [one_mul, add_comm, add_left_comm, add_assoc] using hperiod.symm
  · intro r
    have hsym := pi2CounterexampleComponent_symmetry 1 (r 0)
    simpa only [Pi.neg_apply, Pi.sub_apply, neg_div] using hsym

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed component
is a minimal valid function for the counterexample right-hand side. -/
theorem pi2CounterexampleComponent_negOne_minimal :
    pure_integer_minimal_valid_function_on_R (9 / 10) (pi2CounterexampleComponent (-1)) := by
  -- Package the mirrored component through the same canonical minimality criterion.
  change pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ (9 : ℝ) / 10)
    (fun r : Fin 1 → ℝ ↦ pi2CounterexampleComponent (-1) (r 0))
  refine pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry
    ?_ ?_ ?_ ?_ ?_
  · intro r
    exact pi2CounterexampleComponent_nonneg (Or.inr rfl) (r 0)
  · exact pi2CounterexampleComponent_zero (-1)
  · intro r s
    exact pi2CounterexampleComponent_negOne_subadditive (r 0) (s 0)
  · intro r w
    have hperiod := (pi2CounterexampleComponent_periodic (-1)).int_mul (w 0) (r 0)
    simpa [one_mul, add_comm, add_left_comm, add_assoc] using hperiod.symm
  · intro r
    have hsym := pi2CounterexampleComponent_symmetry (-1) (r 0)
    simpa only [Pi.neg_apply, Pi.sub_apply, neg_div] using hsym

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the positive signed minimal
component is in particular valid. -/
theorem pi2CounterexampleComponent_one_valid :
    pure_integer_valid_function_on_R (9 / 10) (pi2CounterexampleComponent 1) := by
  -- Project the two validity fields from the proved minimal-valid-function certificate.
  exact
    { nonneg := pi2CounterexampleComponent_one_minimal.nonneg
      one_le_sum := pi2CounterexampleComponent_one_minimal.one_le_sum }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the negative signed minimal
component is in particular valid. -/
theorem pi2CounterexampleComponent_negOne_valid :
    pure_integer_valid_function_on_R (9 / 10) (pi2CounterexampleComponent (-1)) := by
  -- Project the validity fields without installing either component as a local instance.
  exact
    { nonneg := pi2CounterexampleComponent_negOne_minimal.nonneg
      one_le_sum := pi2CounterexampleComponent_negOne_minimal.one_le_sum }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_18.lean`: the admissible specialization
`t = 3/10`, `f = 9/10` is not extreme. -/
theorem pi2NotExtremeAtCounterexample :
    ¬ pure_integer_extreme_valid_function_on_R (9 / 10)
      (example_6_23_pi2 (3 / 10) (9 / 10)) := by
  intro hExtreme
  have hMidpointVector :
      (fun r : Fin 1 → ℝ ↦ example_6_23_pi2 (3 / 10) (9 / 10) (r 0)) =
        (1 / 2 : ℝ) • (fun r : Fin 1 → ℝ ↦ pi2CounterexampleComponent 1 (r 0)) +
          (1 / 2 : ℝ) •
            (fun r : Fin 1 → ℝ ↦ pi2CounterexampleComponent (-1) (r 0)) := by
    -- Evaluate the already-proved scalar midpoint identity at the unique coordinate.
    ext r
    have hpoint := congrFun pi2CounterexampleComponents_midpoint (r 0)
    simpa only [Pi.add_apply, Pi.smul_apply] using hpoint
  have hComponentEqualities := hExtreme.eq_of_eq_midpoint
    pi2CounterexampleComponent_one_valid pi2CounterexampleComponent_negOne_valid
    hMidpointVector
  have hOne :
      example_6_23_pi2 (3 / 10) (9 / 10) = pi2CounterexampleComponent 1 := by
    ext r
    have hpoint := congrFun hComponentEqualities.1 (fun _ : Fin 1 ↦ r)
    simpa using hpoint
  have hNegOne :
      example_6_23_pi2 (3 / 10) (9 / 10) = pi2CounterexampleComponent (-1) := by
    ext r
    have hpoint := congrFun hComponentEqualities.2 (fun _ : Fin 1 ↦ r)
    simpa using hpoint
  -- Extremality would identify the two components, contradicting their peak values.
  exact pi2CounterexampleComponents_ne (hOne.symm.trans hNegOne)

end Exercise618Counterexample

#print axioms pi2NotExtremeAtCounterexample
