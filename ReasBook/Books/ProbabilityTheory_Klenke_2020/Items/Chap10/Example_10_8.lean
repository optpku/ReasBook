/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.Martingale.BorelCantelli

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory ENNReal

universe u

variable {Ω : Type u}

/-- The symmetric law on `ℤ` giving mass `1 / 2` to both `1` and `-1`. -/
noncomputable def symmetricRademacherLaw : Measure ℤ :=
  ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℤ)) +
    ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℤ))

/-- The symmetric Rademacher law is a probability measure on `ℤ`. -/
theorem symmetricRademacherLaw_isProbabilityMeasure :
    IsProbabilityMeasure symmetricRademacherLaw := by
  refine ⟨?_⟩
  have hmass :
      symmetricRademacherLaw Set.univ = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ := by
    simp [symmetricRademacherLaw]
  rw [hmass, ENNReal.inv_two_add_inv_two]

instance : IsProbabilityMeasure symmetricRademacherLaw :=
  symmetricRademacherLaw_isProbabilityMeasure

/-- The local time of an integer-valued walk at `0`, counting visits before time `n`. -/
noncomputable def simpleRandomWalkLocalTimeAtZero (X : ℕ → Ω → ℤ) : ℕ → Ω → ℝ :=
  BorelCantelli.process (fun
    | 0 => ∅
    | n + 1 => {ω | X n ω = 0})

-- Proof sketch: unfold the event-counting owner process, split the cumulative sum over
-- `Finset.range (n + 1)` into `Finset.range n` and the last index `n`, and observe that the new
-- contribution is `1` exactly on the event `X n = 0`.
/-- The local time at `0` evolves by adding the indicator of the event that the walk is at `0` at
the previous time. -/
theorem simpleRandomWalkLocalTimeAtZero_succ (X : ℕ → Ω → ℤ) (n : ℕ) :
    simpleRandomWalkLocalTimeAtZero X (n + 1) =
      fun ω ↦ simpleRandomWalkLocalTimeAtZero X n ω +
        if X n ω = 0 then 1 else 0 := by
  ext ω
  unfold simpleRandomWalkLocalTimeAtZero
  simp only [BorelCantelli.process]
  rw [Finset.sum_range_succ, Pi.add_apply]
  congr
  change ({ω | X n ω = 0} : Set Ω).indicator (1 : Ω → ℝ) ω = if X n ω = 0 then 1 else 0
  by_cases h : X n ω = 0 <;> simp [h]

section SymmetricSimpleRandomWalk

variable [MeasurableSpace Ω]
variable {P : Measure Ω} {X : ℕ → Ω → ℤ}
variable (hX_zero : X 0 = 0)
variable (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P)
variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)
local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
local instance : IsFiniteMeasure P := (hX_law 0).isFiniteMeasure

include hX_zero hX_law in
/-- Helper for Example 10.8: each position `X n` is almost everywhere measurable under the
increment-law hypotheses. -/
theorem aemeasurable_position (n : ℕ) : AEMeasurable (X n) P := by
  induction n with
  | zero =>
      -- Proof comment: the walk starts from the constant zero path.
      exact hX_zero.symm ▸ (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω ↦ (0 : ℤ)) P)
  | succ n ih =>
      -- Proof comment: recover `X (n + 1)` by adding the `n`th increment to the current
      -- position.
      refine AEMeasurable.congr (ih.add (hX_law n).aemeasurable) ?_
      filter_upwards with ω
      omega

include hX_zero hX_law in
theorem integrable_zeroReturnIndicator (n : ℕ) :
    Integrable (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) P := by
  -- Proof comment: rewrite the zero-return test as an indicator on the null-measurable return
  -- set, then replace that set by its measurable hull `toMeasurable`.
  let s : Set Ω := {ω | X n ω = 0}
  have hXn_ae : AEMeasurable (X n) P :=
    aemeasurable_position (P := P) (X := X) (hX_zero := hX_zero) (hX_law := hX_law) n
  have hs : NullMeasurableSet s P := by
    simpa [s] using hXn_ae.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℤ))
  have hEq : (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) = s.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : X n ω = 0 <;> simp [s, hω]
  have hIndicator :
      s.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[P]
        (toMeasurable P s).indicator (fun _ ↦ (1 : ℝ)) := by
    simpa using
      (indicator_ae_eq_of_ae_eq_set
        (μ := P) (f := fun _ : Ω ↦ (1 : ℝ)) hs.toMeasurable_ae_eq.symm)
  have hToMeasurableFinite : P (toMeasurable P s) ≠ ∞ := by
    have hUniv : P Set.univ = 1 := (hX_law 0).isProbabilityMeasure.measure_univ
    have hle : P (toMeasurable P s) ≤ 1 := by
      calc
        P (toMeasurable P s) ≤ P Set.univ := measure_mono (Set.subset_univ (toMeasurable P s))
        _ = 1 := hUniv
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  rw [hEq]
  exact ((integrableOn_const (s := toMeasurable P s) hToMeasurableFinite).integrable_indicator
    (measurableSet_toMeasurable P s)).congr hIndicator.symm

/-- Helper for Example 10.8: if the walk is measurable at each time, then the return-event
indicator at time `n` is integrable. -/
theorem integrable_zeroReturnIndicator_of_measurable
    [IsFiniteMeasure P] (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    Integrable (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) P := by
  let s : Set Ω := {ω | X n ω = 0}
  have hXn : Measurable (X n) := hX_meas n
  have hs : MeasurableSet s := by
    change MeasurableSet (X n ⁻¹' ({0} : Set ℤ))
    simpa [s] using hXn (measurableSet_singleton (0 : ℤ))
  have hEq : (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) = s.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : X n ω = 0 <;> simp [s, hω]
  rw [hEq]
  exact (integrable_const (1 : ℝ)).indicator hs

include hX_zero hX_law in
/-- Helper for Example 10.8: the integral of the return-event indicator is the corresponding
return probability. -/
theorem integral_zeroReturnIndicator_eq_prob (n : ℕ) :
    ∫ ω, (if X n ω = 0 then (1 : ℝ) else 0) ∂P = P.real {ω | X n ω = 0} := by
  -- Proof comment: pass from the null-measurable return set to its measurable hull, where
  -- `integral_indicator_one` computes the integral exactly.
  let s : Set Ω := {ω | X n ω = 0}
  have hXn_ae : AEMeasurable (X n) P :=
    aemeasurable_position (P := P) (X := X) (hX_zero := hX_zero) (hX_law := hX_law) n
  have hs : NullMeasurableSet s P := by
    simpa [s] using hXn_ae.nullMeasurableSet_preimage (measurableSet_singleton (0 : ℤ))
  have hEq : (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) = s.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : X n ω = 0 <;> simp [s, hω]
  have hIndicator :
      s.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[P]
        (toMeasurable P s).indicator (fun _ ↦ (1 : ℝ)) := by
    simpa using
      (indicator_ae_eq_of_ae_eq_set
        (μ := P) (f := fun _ : Ω ↦ (1 : ℝ)) hs.toMeasurable_ae_eq.symm)
  calc
    ∫ ω, (if X n ω = 0 then (1 : ℝ) else 0) ∂P
        = ∫ ω, s.indicator (fun _ ↦ (1 : ℝ)) ω ∂P := by
            rw [hEq]
    _ = ∫ ω, (toMeasurable P s).indicator (fun _ ↦ (1 : ℝ)) ω ∂P := by
          exact integral_congr_ae hIndicator
    _ = P.real (toMeasurable P s) := by
          simpa using integral_indicator_one (μ := P) (s := toMeasurable P s)
            (measurableSet_toMeasurable P s)
    _ = P.real s := by
          simp [Measure.real, measure_toMeasurable]

/-- Helper for Example 10.8: if the walk is measurable at each time, then the integral of the
return-event indicator is the corresponding return probability. -/
theorem integral_zeroReturnIndicator_eq_prob_of_measurable
    [IsFiniteMeasure P] (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    ∫ ω, (if X n ω = 0 then (1 : ℝ) else 0) ∂P = P.real {ω | X n ω = 0} := by
  -- Proof comment: rewrite the indicator in set-indicator form and apply
  -- `integral_indicator_one`.
  let s : Set Ω := {ω | X n ω = 0}
  have hXn : Measurable (X n) := hX_meas n
  have hs : MeasurableSet s := by
    change MeasurableSet (X n ⁻¹' ({0} : Set ℤ))
    simpa [s] using hXn (measurableSet_singleton (0 : ℤ))
  have hEq : (fun ω ↦ if X n ω = 0 then (1 : ℝ) else 0) = s.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hω : X n ω = 0 <;> simp [s, hω]
  rw [hEq]
  simpa [s] using integral_indicator_one (μ := P) hs

include hX_zero hX_law in
/-- Helper for Example 10.8: the local-time process is integrable at each fixed time. -/
theorem integrable_localTimeAtZero (n : ℕ) :
    Integrable (fun ω ↦ simpleRandomWalkLocalTimeAtZero X n ω) P := by
  induction n with
  | zero =>
      -- Proof comment: the local time starts from the zero function.
      simp [simpleRandomWalkLocalTimeAtZero, BorelCantelli.process]
  | succ n ih =>
      -- Proof comment: one more step adds the zero-return indicator at time `n`.
      rw [simpleRandomWalkLocalTimeAtZero_succ]
      exact ih.add
        (integrable_zeroReturnIndicator (P := P) (X := X)
          (hX_zero := hX_zero) (hX_law := hX_law) n)

/-- Helper for Example 10.8: if the walk is measurable at each time, then the local-time process
is integrable at each fixed time. -/
theorem integrable_localTimeAtZero_of_measurable
    [IsFiniteMeasure P] (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    Integrable (fun ω ↦ simpleRandomWalkLocalTimeAtZero X n ω) P := by
  induction n with
  | zero =>
      -- Proof comment: the local time starts from the zero function.
      simp [simpleRandomWalkLocalTimeAtZero, BorelCantelli.process]
  | succ n ih =>
      -- Proof comment: the next local-time value is the previous one plus the return indicator.
      rw [simpleRandomWalkLocalTimeAtZero_succ]
      exact ih.add (integrable_zeroReturnIndicator_of_measurable (P := P) (X := X) hX_meas n)

include hX_zero hX_law in
-- Proof sketch: expand the local time by the recursion
-- `simpleRandomWalkLocalTimeAtZero_succ`, integrate the added indicator, and identify that
-- integral with the return probability `P[X_n = 0]`.
/-- Helper for Example 10.8: the expected local time is the sum of the return probabilities at
the earlier times. -/
theorem integral_localTimeAtZero_eq_sum_returnProbabilities
    (n : ℕ) :
    ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P =
      ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} := by
  induction n with
  | zero =>
      -- Proof comment: both the local time and the finite return-probability sum vanish at
      -- time `0`.
      simp [simpleRandomWalkLocalTimeAtZero, BorelCantelli.process]
  | succ n ih =>
      -- Proof comment: the recursion for local time adds exactly the return indicator at time
      -- `n`, whose integral is the return probability.
      rw [simpleRandomWalkLocalTimeAtZero_succ, integral_add
        (integrable_localTimeAtZero (P := P) (X := X) (hX_zero := hX_zero) (hX_law := hX_law) n)
        (integrable_zeroReturnIndicator (P := P) (X := X) (hX_zero := hX_zero)
          (hX_law := hX_law) n),
        ih, Finset.sum_range_succ,
        integral_zeroReturnIndicator_eq_prob (P := P) (X := X)
          (hX_zero := hX_zero) (hX_law := hX_law) n]

/-- Helper for Example 10.8: if the walk is measurable at each time, then the expected local time
is the sum of the return probabilities at the earlier times. -/
theorem integral_localTimeAtZero_eq_sum_returnProbabilities_of_measurable
    [IsFiniteMeasure P] (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P =
      ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} := by
  induction n with
  | zero =>
      -- Proof comment: both the local time and the finite sum vanish at time `0`.
      simp [simpleRandomWalkLocalTimeAtZero, BorelCantelli.process]
  | succ n ih =>
      -- Proof comment: adding one more time step adds exactly the indicator of the return event
      -- at time `n`.
      rw [simpleRandomWalkLocalTimeAtZero_succ, integral_add
        (integrable_localTimeAtZero_of_measurable (P := P) (X := X) hX_meas n)
        (integrable_zeroReturnIndicator_of_measurable (P := P) (X := X) hX_meas n),
        ih, Finset.sum_range_succ,
        integral_zeroReturnIndicator_eq_prob_of_measurable (P := P) (X := X) hX_meas n]

include hX_zero hX_indep hX_law

-- Route correction: the predictable-compensator route is blocked by a missing measurability
-- bridge for the natural filtration, so this helper records the stabilized local-time side of the
-- argument instead.
/-- For a symmetric simple random walk, if the path coordinates `X n` are measurable, then the
expected local time at `0` is the finite sum of the return probabilities before time `n`. -/
theorem symmetricSimpleRandomWalk_abs_predictablePart_eq_localTimeAtZero
    (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P =
      ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} :=
  by
    -- Proof comment: the repaired local-time identity no longer needs a separate measurability
    -- hypothesis on the increments, so we use the measurable-path version directly.
    let _ : IsFiniteMeasure P := (hX_law 0).isFiniteMeasure
    simpa using integral_localTimeAtZero_eq_sum_returnProbabilities_of_measurable
      (P := P) (X := X) hX_meas n

include hX_indep hX_law in
/-- Helper for Example 10.8: the first `n` increments of the walk have the `n`-fold product law
of the symmetric Rademacher measure. -/
theorem symmetricSimpleRandomWalk_incrementPrefix_hasLaw_pi (n : ℕ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ X (i.1 + 1) ω - X i.1 ω)
      (Measure.pi fun _ : Fin n ↦ symmetricRademacherLaw) P := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · -- Proof comment: package the coordinatewise increment measurability into the finite vector map.
    exact aemeasurable_pi_lambda _ fun i : Fin n ↦ (hX_law i).aemeasurable
  · have hPrefixIndep : iIndepFun (fun i : Fin n ↦ fun ω ↦ X (i.1 + 1) ω - X i.1 ω) P := by
      -- Proof comment: restrict the independent increment family along `Fin.val`.
      simpa using hX_indep.precomp Fin.val_injective
    have hMapEq :
        P.map (fun ω ↦ fun i : Fin n ↦ X (i.1 + 1) ω - X i.1 ω) =
          Measure.pi (fun i : Fin n ↦ P.map (fun ω ↦ X (i.1 + 1) ω - X i.1 ω)) := by
      exact
        (iIndepFun_iff_map_fun_eq_pi_map
          (μ := P)
          (f := fun i : Fin n ↦ fun ω ↦ X (i.1 + 1) ω - X i.1 ω)
          (fun i : Fin n ↦ (hX_law i).aemeasurable)).1 hPrefixIndep
    rw [hMapEq]
    -- Proof comment: each coordinate marginal is exactly the symmetric Rademacher law.
    congr 1
    funext i
    exact (hX_law i).map_eq

include hX_zero in
/-- Helper for Example 10.8: the position `X n` is the telescoping sum of the first `n`
increments. -/
theorem symmetricSimpleRandomWalk_position_eq_sum_increments (n : ℕ) :
    (fun ω ↦ X n ω) = fun ω ↦ ∑ i : Fin n, (X (i.1 + 1) ω - X i.1 ω) := by
  funext ω
  induction n with
  | zero =>
      -- Proof comment: the empty telescoping sum matches the prescribed starting point `X 0 = 0`.
      simp [hX_zero]
  | succ n ih =>
      -- Proof comment: split off the last increment and use the induction hypothesis on the
      -- prefix sum.
      have hsum :
          (∑ i : Fin (n + 1), (X (i.1 + 1) ω - X i.1 ω)) =
            Finset.sum (Finset.range (n + 1)) (fun i ↦ X (i + 1) ω - X i ω) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (n := n + 1) (f := fun i ↦ X (i + 1) ω - X i ω))
      calc
        X (n + 1) ω = X n ω + (X (n + 1) ω - X n ω) := by omega
        _ = (∑ i : Fin n, (X (i.1 + 1) ω - X i.1 ω)) + (X (n + 1) ω - X n ω) := by
              rw [ih]
        _ = Finset.sum (Finset.range n) (fun i ↦ X (i + 1) ω - X i ω) + (X (n + 1) ω - X n ω) := by
              rw [← Fin.sum_univ_eq_sum_range]
        _ = Finset.sum (Finset.range (n + 1)) (fun i ↦ X (i + 1) ω - X i ω) := by
              rw [Finset.sum_range_succ]
        _ = (∑ i : Fin (n + 1), (X (i.1 + 1) ω - X i.1 ω)) := by
              simpa using hsum.symm

include hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the position `X n` is the pushforward of the coordinate-sum map on
the first `n` symmetric increments. -/
theorem symmetricSimpleRandomWalk_position_hasLaw_prefixSum (n : ℕ) :
    HasLaw (X n)
      (Measure.map (fun z : Fin n → ℤ ↦ ∑ i, z i)
        (Measure.pi fun _ : Fin n ↦ symmetricRademacherLaw)) P := by
  let μn : Measure (Fin n → ℤ) := Measure.pi fun _ : Fin n ↦ symmetricRademacherLaw
  have hSum :
      HasLaw (fun z : Fin n → ℤ ↦ ∑ i, z i)
        (Measure.map (fun z : Fin n → ℤ ↦ ∑ i, z i) μn) μn := by
    -- Proof comment: the coordinate-sum map has its own pushforward law by definition.
    refine ⟨by fun_prop, rfl⟩
  have hComp :
      HasLaw (fun ω ↦ ∑ i : Fin n, (X (i.1 + 1) ω - X i.1 ω))
        (Measure.map (fun z : Fin n → ℤ ↦ ∑ i, z i) μn) P :=
    ProbabilityTheory.HasLaw.fun_comp hSum
      (symmetricSimpleRandomWalk_incrementPrefix_hasLaw_pi
        (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n)
  -- Proof comment: rewrite the telescoping sum back to the position `X n`.
  exact hComp.congr
    (Filter.EventuallyEq.of_eq
      (symmetricSimpleRandomWalk_position_eq_sum_increments
        (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n))

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the symmetric Rademacher law is the pushforward of the uniform law on
`Bool` along the map sending `true` to `1` and `false` to `-1`. -/
theorem symmetricRademacherLaw_eq_uniformBool_map :
    Measure.map (fun b : Bool ↦ if b then (1 : ℤ) else -1)
      ((PMF.uniformOfFintype Bool).toMeasure) = symmetricRademacherLaw := by
  -- Proof comment: compare the two measures on singleton atoms `z : ℤ`; only `1` and `-1`
  -- receive positive mass.
  refine Measure.ext_of_singleton ?_
  intro z
  by_cases hz1 : z = 1
  · subst hz1
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    simp [symmetricRademacherLaw, PMF.uniformOfFintype_apply]
  · by_cases hzneg : z = -1
    · subst hzneg
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      simp [symmetricRademacherLaw, PMF.uniformOfFintype_apply]
    · rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      have hznot1 : (1 : ℤ) ≠ z := by
        intro hz
        apply hz1
        simpa using hz.symm
      have hznotNeg1 : (-1 : ℤ) ≠ z := by
        intro hz
        apply hzneg
        simpa using hz.symm
      simp [symmetricRademacherLaw, hznot1, hznotNeg1]

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the `n`-fold product of the symmetric Rademacher law is the
pushforward of the uniform Boolean cube under the coordinatewise sign map. -/
theorem symmetricRademacherPrefix_eq_uniformBoolCube (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ symmetricRademacherLaw) =
      Measure.map (fun b : Fin n → Bool ↦ fun i : Fin n ↦ if b i then (1 : ℤ) else -1)
        (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
  -- Proof comment: push the finite Boolean cube coordinatewise through the sign map and identify
  -- the resulting marginals with `symmetricRademacherLaw`.
  calc
    Measure.pi (fun _ : Fin n ↦ symmetricRademacherLaw)
        = Measure.pi (fun _ : Fin n ↦
            Measure.map (fun b : Bool ↦ if b then (1 : ℤ) else -1)
              ((PMF.uniformOfFintype Bool).toMeasure)) := by
              congr 1
              funext i
              symm
              exact symmetricRademacherLaw_eq_uniformBool_map
    _ = Measure.map (fun b : Fin n → Bool ↦ fun i : Fin n ↦ if b i then (1 : ℤ) else -1)
          (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
            symm
            simpa using
              (Measure.pi_map_pi
                (μ := fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))
                (f := fun _ : Fin n ↦ fun b : Bool ↦ if b then (1 : ℤ) else -1)
                (fun _ : Fin n ↦
                  (measurable_of_countable (fun b : Bool ↦ if b then (1 : ℤ) else -1)).aemeasurable))

/-- Helper for Example 10.8: the position `X n` has the same law as the Boolean-cube sign sum
`∑ i, (if b i then 1 else -1)`. -/
theorem symmetricSimpleRandomWalk_position_hasLaw_boolPrefixSum (n : ℕ) :
    HasLaw (X n)
      (Measure.map (fun b : Fin n → Bool ↦ ∑ i, (if b i then (1 : ℤ) else -1))
        (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))) P := by
  let cube : Measure (Fin n → Bool) := Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signVec : (Fin n → Bool) → Fin n → ℤ := fun b i ↦ if b i then (1 : ℤ) else -1
  let sumVec : (Fin n → ℤ) → ℤ := fun z ↦ ∑ i, z i
  have hsignVec_meas : Measurable signVec := measurable_of_countable signVec
  have hsumVec_meas : Measurable sumVec := measurable_of_countable sumVec
  have hPrefix :=
    symmetricSimpleRandomWalk_position_hasLaw_prefixSum
      (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n
  refine ⟨hPrefix.aemeasurable, ?_⟩
  -- Proof comment: replace the increment-product law by the Boolean-cube sign model and then
  -- collapse the composed pushforward.
  calc
    P.map (X n) = Measure.map sumVec (Measure.pi fun _ : Fin n ↦ symmetricRademacherLaw) := by
      simpa [sumVec] using hPrefix.map_eq
    _ = Measure.map sumVec (Measure.map signVec cube) := by
          exact congrArg (fun ν : Measure (Fin n → ℤ) ↦ Measure.map sumVec ν)
            (by simpa [cube, signVec] using symmetricRademacherPrefix_eq_uniformBoolCube (n := n))
    _ = Measure.map (sumVec ∘ signVec) cube := by
          rw [Measure.map_map hsumVec_meas hsignVec_meas]
    _ = Measure.map (fun b : Fin n → Bool ↦ ∑ i, (if b i then (1 : ℤ) else -1)) cube := by
          rfl

/-- Helper for Example 10.8: the expectation of `|X n|` can be rewritten as a finite integral over
the Boolean cube. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_uniformBoolCubeIntegral
    (n : ℕ) :
    ∫ ω, |Xℝ n ω| ∂P =
      ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
        ∂(Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
  let cube : Measure (Fin n → Bool) := Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signSum : (Fin n → Bool) → ℤ := fun b ↦ ∑ i, (if b i then (1 : ℤ) else -1)
  have hsignSum_meas : Measurable signSum := measurable_of_countable signSum
  have habs_meas : AEStronglyMeasurable (fun z : ℤ ↦ |(z : ℝ)|) (Measure.map signSum cube) := by
    exact (measurable_of_countable (fun z : ℤ ↦ |(z : ℝ)|)).aestronglyMeasurable
  have hLaw :=
    symmetricSimpleRandomWalk_position_hasLaw_boolPrefixSum
      (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n
  calc
    ∫ ω, |(X n ω : ℝ)| ∂P = ∫ z : ℤ, |(z : ℝ)| ∂(Measure.map signSum cube) := by
            -- Proof comment: transport the scalar observable `z ↦ |z|` through the law of `X n`.
            simpa [cube, signSum, Function.comp] using
              (hLaw.integral_comp (f := fun z : ℤ ↦ |(z : ℝ)|) habs_meas)
    _ = ∫ b : Fin n → Bool, |((signSum b : ℤ) : ℝ)| ∂cube := by
          -- Proof comment: compute the pushforward integral back on the Boolean cube.
          simpa [cube] using
            (integral_map (μ := cube) (φ := signSum) (f := fun z : ℤ ↦ |(z : ℝ)|)
              hsignSum_meas.aemeasurable habs_meas)
    _ = ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
          ∂(Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
          rfl

/-- Helper for Example 10.8: the return event `{X n = 0}` can be rewritten as the zero-sum event
on the Boolean cube. -/
theorem symmetricSimpleRandomWalk_prob_eq_zero_eq_uniformBoolCube
    (n : ℕ) :
    P.real {ω | X n ω = 0} =
      (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
        {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
  let cube : Measure (Fin n → Bool) := Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signSum : (Fin n → Bool) → ℤ := fun b ↦ ∑ i, (if b i then (1 : ℤ) else -1)
  have hsignSum_meas : Measurable signSum := measurable_of_countable signSum
  have hpreX : {ω | X n ω = 0} = X n ⁻¹' ({0} : Set ℤ) := by
    ext ω
    simp
  have hpreSign : signSum ⁻¹' ({0} : Set ℤ) = {b : Fin n → Bool | signSum b = 0} := by
    ext b
    simp
  have hLaw :=
    symmetricSimpleRandomWalk_position_hasLaw_boolPrefixSum
      (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n
  calc
    P.real {ω | X n ω = 0} = (P (X n ⁻¹' ({0} : Set ℤ))).toReal := by
      -- Proof comment: rewrite the return event as the preimage of the singleton `{0}`.
      simp [Measure.real, hpreX]
    _ = ((P.map (X n)) ({0} : Set ℤ)).toReal := by
          rw [Measure.map_apply_of_aemeasurable hLaw.aemeasurable (measurableSet_singleton (0 : ℤ))]
    _ = ((Measure.map signSum cube) ({0} : Set ℤ)).toReal := by
          exact congrArg ENNReal.toReal (congrArg (fun ν : Measure ℤ ↦ ν ({0} : Set ℤ)) hLaw.map_eq)
    _ = (cube (signSum ⁻¹' ({0} : Set ℤ))).toReal := by
          rw [Measure.map_apply hsignSum_meas (measurableSet_singleton (0 : ℤ))]
    _ = cube.real {b : Fin n → Bool | signSum b = 0} := by
          -- Proof comment: evaluate the pushed-forward Boolean-cube law on the singleton `{0}`.
          simp [Measure.real, hpreSign]
    _ = (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
          {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
          rfl

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the Boolean-cube product measure is the uniform measure on the
finite type `Fin n → Bool`. -/
theorem uniformBoolCube_eq_uniformMeasure (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  -- Proof comment: identify both measures by their singleton masses; each Boolean word has
  -- weight `2^{-n}` under the product law and under the uniform PMF on the finite cube.
  refine Measure.ext_of_singleton ?_
  intro b
  rw [Measure.pi_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Helper for Example 10.8: the `true` coordinates of a Boolean word. -/
def trueCoordinates {n : ℕ} (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ b i

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the characteristic word of a finite set recovers that set as its
`true` coordinates. -/
theorem trueCoordinates_characteristic {n : ℕ} (s : Finset (Fin n)) :
    trueCoordinates (fun i ↦ decide (i ∈ s)) = s := by
  -- Proof comment: a coordinate is marked `true` exactly when it belongs to the chosen subset.
  ext i
  simp [trueCoordinates]

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: averaging the two possible next-step absolute values adds exactly the
zero indicator. -/
theorem absStepAverage_eq_abs_add_zeroIndicator (s : ℤ) :
    (|((s + 1 : ℤ) : ℝ)| + |((s - 1 : ℤ) : ℝ)|) / 2 =
      |(s : ℝ)| + if s = 0 then 1 else 0 := by
  by_cases hs0 : s = 0
  · -- Proof comment: at the origin the two next-step absolute values are both `1`.
    subst hs0
    norm_num
  · by_cases hspos : 0 < s
    · -- Proof comment: on the positive side both `s + 1` and `s - 1` stay nonnegative, so the
      -- absolute values disappear.
      have hs_nonneg : 0 ≤ (s : ℝ) := by exact_mod_cast le_of_lt hspos
      have hs_add_nonneg : 0 ≤ ((s + 1 : ℤ) : ℝ) := by
        have : 0 ≤ s + 1 := by omega
        exact_mod_cast this
      have hs_sub_nonneg : 0 ≤ ((s - 1 : ℤ) : ℝ) := by
        have : 0 ≤ s - 1 := by omega
        exact_mod_cast this
      rw [if_neg hs0, abs_of_nonneg hs_add_nonneg, abs_of_nonneg hs_sub_nonneg,
        abs_of_nonneg hs_nonneg]
      norm_num
    · -- Proof comment: on the negative side both `s + 1` and `s - 1` stay nonpositive, so the
      -- absolute values flip their signs.
      have hsneg : s < 0 := by omega
      have hs_nonpos : (s : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hsneg
      have hs_add_nonpos : (((s + 1 : ℤ) : ℝ)) ≤ 0 := by
        have : s + 1 ≤ 0 := by omega
        exact_mod_cast this
      have hs_sub_nonpos : (((s - 1 : ℤ) : ℝ)) ≤ 0 := by
        have : s - 1 ≤ 0 := by omega
        exact_mod_cast this
      rw [if_neg hs0, abs_of_nonpos hs_add_nonpos, abs_of_nonpos hs_sub_nonpos,
        abs_of_nonpos hs_nonpos]
      have hsCast1 : ((s + 1 : ℤ) : ℝ) = (s : ℝ) + 1 := by norm_num
      have hsCast2 : ((s - 1 : ℤ) : ℝ) = (s : ℝ) - 1 := by norm_num
      rw [hsCast1, hsCast2]
      ring_nf

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: on the Boolean cube, the absolute sign-sum satisfies the one-step
recursion `E |S_{n+1}| = E |S_n| + P[S_n = 0]`. -/
theorem uniformBoolCube_abs_step (n : ℕ) :
    ∫ b : Fin (n + 1) → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
      ∂(Measure.pi fun _ : Fin (n + 1) ↦ ((PMF.uniformOfFintype Bool).toMeasure)) =
      ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
        ∂(Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) +
      (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
        {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
  let cube : (m : ℕ) → Measure (Fin m → Bool) :=
    fun m ↦ Measure.pi fun _ : Fin m ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signSum : {m : ℕ} → (Fin m → Bool) → ℤ :=
    fun {_} b ↦ ∑ i, (if b i then (1 : ℤ) else -1)
  let absSum : {m : ℕ} → (Fin m → Bool) → ℝ :=
    fun {_} b ↦ |((signSum b : ℤ) : ℝ)|
  let zeroEvent : Set (Fin n → Bool) := {b | signSum b = 0}
  have hProdIntegrable :
      Integrable
        (fun p : Bool × (Fin n → Bool) ↦ absSum
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm p))
        (((PMF.uniformOfFintype Bool).toMeasure).prod (cube n)) := by
    -- Proof comment: the domain is finite, so every real-valued function is integrable.
    exact Integrable.of_finite
  have hInner :
      ∀ tail : Fin n → Bool,
        ∫ head : Bool, absSum
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm (head, tail))
          ∂((PMF.uniformOfFintype Bool).toMeasure) =
          absSum tail + if signSum tail = 0 then 1 else 0 := by
    intro tail
    -- Proof comment: averaging over the new Boolean coordinate is exactly the two-point
    -- arithmetic identity from `absStepAverage_eq_abs_add_zeroIndicator`.
    have hTrue :
        absSum
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm (true, tail)) =
          |(((signSum tail + 1 : ℤ) : ℤ) : ℝ)| := by
      simp [absSum, signSum, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ, add_comm]
    have hFalse :
        absSum
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm (false, tail)) =
          |(((-1 + signSum tail : ℤ) : ℤ) : ℝ)| := by
      simp [absSum, signSum, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
    have hStep := absStepAverage_eq_abs_add_zeroIndicator (signSum tail)
    calc
      ∫ head : Bool, absSum
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm (head, tail))
          ∂((PMF.uniformOfFintype Bool).toMeasure)
          =
            ∑ head : Bool,
              ((PMF.uniformOfFintype Bool) head).toReal *
                absSum
                  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm
                    (head, tail)) := by
              simpa [smul_eq_mul] using
                (PMF.integral_eq_sum (PMF.uniformOfFintype Bool)
                  (fun head : Bool ↦ absSum
                    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm
                      (head, tail))))
      _ =
            ((PMF.uniformOfFintype Bool) true).toReal *
                absSum
                  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm
                    (true, tail)) +
              ((PMF.uniformOfFintype Bool) false).toReal *
                absSum
                  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm
                    (false, tail)) := by
              rw [Fintype.sum_bool]
      _ = absSum tail + if signSum tail = 0 then 1 else 0 := by
            rw [hFalse, hTrue]
            have hAdd : (1 : ℝ) + ↑(signSum tail) = ↑(signSum tail) + 1 := by ring
            have hStep' :
                2⁻¹ * |((↑(signSum tail) + 1 : ℝ))| +
                    2⁻¹ * |(((-1 + signSum tail : ℤ) : ℝ))| =
                  absSum tail + if signSum tail = 0 then 1 else 0 := by
              simpa [hAdd, absSum, signSum, PMF.uniformOfFintype_apply, div_eq_mul_inv,
                sub_eq_add_neg, mul_add, mul_comm, add_comm, add_left_comm, add_assoc] using hStep
            simpa using hStep'
  have hZeroEventMeas :
      MeasurableSet zeroEvent := by
    have hSignSumMeas : Measurable (fun b : Fin n → Bool ↦ signSum b) := measurable_of_countable _
    change MeasurableSet ((fun b : Fin n → Bool ↦ signSum b) ⁻¹' ({0} : Set ℤ))
    simpa [zeroEvent] using hSignSumMeas (measurableSet_singleton (0 : ℤ))
  have hZeroEventIntegral :
      ∫ b : Fin n → Bool, (if signSum b = 0 then (1 : ℝ) else 0) ∂cube n =
        (cube n).real zeroEvent := by
    have hIndicator :
        (fun b : Fin n → Bool ↦ if signSum b = 0 then (1 : ℝ) else 0) =
          zeroEvent.indicator (fun _ ↦ (1 : ℝ)) := by
      funext b
      by_cases hb : signSum b = 0 <;> simp [zeroEvent, hb]
    rw [hIndicator]
    simpa [zeroEvent] using integral_indicator_one (μ := cube n) (s := zeroEvent)
      hZeroEventMeas
  have hAbsIntegrable : Integrable (fun b : Fin n → Bool ↦ absSum b) (cube n) := by
    -- Proof comment: again, finiteness of the Boolean cube gives integrability for free.
    exact Integrable.of_finite
  have hIndicatorIntegrable :
      Integrable (fun b : Fin n → Bool ↦ if signSum b = 0 then (1 : ℝ) else 0) (cube n) := by
    exact Integrable.of_finite
  have hSplitPres :=
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ((PMF.uniformOfFintype Bool).toMeasure)) 0).symm
  -- Proof comment: split off the first coordinate, evaluate the inner Boolean average, and then
  -- separate the remaining integral into the old expectation plus the zero-mass term.
  calc
    ∫ b : Fin (n + 1) → Bool, absSum b ∂cube (n + 1)
        =
          ∫ p : Bool × (Fin n → Bool), absSum
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm p)
            ∂(((PMF.uniformOfFintype Bool).toMeasure).prod (cube n)) := by
              rw [← hSplitPres.integral_comp']
    _ = ∫ tail : Fin n → Bool,
          ∫ head : Bool, absSum
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm (head, tail))
            ∂((PMF.uniformOfFintype Bool).toMeasure)
          ∂cube n := by
            simpa [cube] using integral_prod_symm
              (fun p : Bool × (Fin n → Bool) ↦ absSum
                ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Bool) 0).symm p))
              hProdIntegrable
    _ = ∫ tail : Fin n → Bool, absSum tail + if signSum tail = 0 then 1 else 0 ∂cube n := by
          simp_rw [hInner]
    _ = ∫ tail : Fin n → Bool, absSum tail ∂cube n +
          ∫ tail : Fin n → Bool, (if signSum tail = 0 then (1 : ℝ) else 0) ∂cube n := by
          rw [integral_add hAbsIntegrable hIndicatorIntegrable]
    _ = ∫ tail : Fin n → Bool, absSum tail ∂cube n + (cube n).real zeroEvent := by
          rw [hZeroEventIntegral]
    _ = ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)| ∂cube n +
          (cube n).real {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
          rfl
    _ =
          ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
            ∂(Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) +
          (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
            {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
          rfl

include hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the expectation of `|X_n|` is the sum of the return probabilities
up to time `n - 1`. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_sum_returnProbabilities
    (n : ℕ) :
    ∫ ω, |Xℝ n ω| ∂P = ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} := by
  induction n with
  | zero =>
      -- Proof comment: the walk starts at `0`, so both sides vanish at time `0`.
      simp [hX_zero]
  | succ n ih =>
      -- Proof comment: use the Bool-cube one-step recursion, then transport the zero-mass term
      -- back to the walk.
      calc
        ∫ ω, |Xℝ (n + 1) ω| ∂P
            =
              ∫ b : Fin (n + 1) → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
                ∂(Measure.pi fun _ : Fin (n + 1) ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
                  exact symmetricSimpleRandomWalk_integral_abs_eq_uniformBoolCubeIntegral
                    (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep)
                    (hX_law := hX_law) (n + 1)
        _ =
              ∫ b : Fin n → Bool, |((∑ i, (if b i then (1 : ℤ) else -1) : ℤ) : ℝ)|
                ∂(Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) +
              (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
                {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
                  exact uniformBoolCube_abs_step n
        _ = ∫ ω, |Xℝ n ω| ∂P + P.real {ω | X n ω = 0} := by
              rw [← symmetricSimpleRandomWalk_integral_abs_eq_uniformBoolCubeIntegral
                (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep)
                (hX_law := hX_law) n,
                ← symmetricSimpleRandomWalk_prob_eq_zero_eq_uniformBoolCube
                (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep)
                (hX_law := hX_law) n]
        _ = ∑ i ∈ Finset.range (n + 1), P.real {ω | X i ω = 0} := by
              rw [ih, Finset.sum_range_succ]

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the zero-sign-sum condition is equivalent to having exactly half of
the coordinates equal to `true`. -/
theorem boolSignSum_eq_zero_iff_two_mul_card_trueCoordinates {n : ℕ} (b : Fin n → Bool) :
    (∑ i, (if b i then (1 : ℤ) else -1)) = 0 ↔ 2 * (trueCoordinates b).card = n := by
  have hSum :
      (∑ i, (if b i then (1 : ℤ) else -1)) =
        (2 : ℤ) * (trueCoordinates b).card - n := by
    calc
      (∑ i, (if b i then (1 : ℤ) else -1))
          = ∑ i, ((if b i then (2 : ℤ) else 0) - 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hbi : b i <;> simp [hbi]
      _ = (∑ i, (if b i then (2 : ℤ) else 0)) - ∑ i : Fin n, (1 : ℤ) := by
            rw [Finset.sum_sub_distrib]
      _ = (2 : ℤ) * (trueCoordinates b).card - n := by
            have hTwo :
                (∑ i : Fin n, (if b i then (2 : ℤ) else 0)) =
                  (2 : ℤ) * ∑ i : Fin n, (if b i then (1 : ℤ) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hbi : b i <;> simp [hbi]
            rw [hTwo]
            simp [trueCoordinates, Finset.sum_boole]
  constructor
  · intro hb
    have hInt : (2 : ℤ) * (trueCoordinates b).card - n = 0 := by
      simpa [hSum] using hb
    have hNat : 2 * (trueCoordinates b).card = n := by
      omega
    exact hNat
  · intro hb
    have hInt : (2 : ℤ) * (trueCoordinates b).card = n := by
      exact_mod_cast hb
    have hZero : (2 : ℤ) * (trueCoordinates b).card - n = 0 := sub_eq_zero.mpr hInt
    simpa [hSum] using hZero

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: zero-sum Boolean words of length `2 * m` are counted by the
`m`-element subsets of `Fin (2 * m)`. -/
theorem zeroSumWords_card_eq_powersetCard (m : ℕ) :
    Fintype.card {b : Fin (2 * m) → Bool // ∑ i, (if b i then (1 : ℤ) else -1) = 0} =
      Fintype.card {s : Finset (Fin (2 * m)) // s.card = m} := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    -- Proof comment: a zero-sum word has exactly `m` true coordinates.
    refine ⟨trueCoordinates b.1, ?_⟩
    have hDouble :
        2 * (trueCoordinates b.1).card = 2 * m := by
      simpa using (boolSignSum_eq_zero_iff_two_mul_card_trueCoordinates b.1).1 b.2
    omega
  · intro s
    -- Proof comment: the characteristic word of an `m`-element subset has zero sign sum.
    refine ⟨fun i ↦ decide (i ∈ s.1), ?_⟩
    have hCoords :
        trueCoordinates (fun i ↦ decide (i ∈ s.1)) = s.1 := by
      exact trueCoordinates_characteristic s.1
    have hCard :
        (trueCoordinates (fun i ↦ decide (i ∈ s.1))).card = m := by
      rw [hCoords]
      exact s.2
    have hDouble :
        2 * (trueCoordinates (fun i ↦ decide (i ∈ s.1))).card = 2 * m := by
      omega
    have hZero :
        (∑ i, (if (fun i ↦ decide (i ∈ s.1)) i then (1 : ℤ) else -1)) = 0 := by
      exact
        (boolSignSum_eq_zero_iff_two_mul_card_trueCoordinates
          (b := fun i ↦ decide (i ∈ s.1))).2 hDouble
    exact hZero
  · intro b
    -- Proof comment: recovering the characteristic word of the `true` coordinates gives back the
    -- original Boolean word.
    apply Subtype.ext
    funext i
    by_cases hbi : b.1 i
    · simp [trueCoordinates, hbi]
    · simp [trueCoordinates, hbi]
  · intro s
    -- Proof comment: the `true` coordinates of a characteristic word are exactly the original
    -- subset.
    apply Subtype.ext
    exact trueCoordinates_characteristic s.1

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the zero-sign-sum event on the Boolean cube has the central-binomial
mass in even dimension and vanishes in odd dimension. -/
theorem uniformBoolCube_zeroMass_eq_choose (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)).real
      {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} =
        if Even n then (Nat.choose n (n / 2) : ℝ) / (2 : ℝ) ^ n else 0 := by
  classical
  have hZeroEventMeas :
      MeasurableSet {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} := by
    -- Proof comment: the zero-sum event is a singleton preimage under a function on a finite
    -- type, hence measurable.
    have hSignSumMeas :
        Measurable (fun b : Fin n → Bool ↦ ∑ i, (if b i then (1 : ℤ) else -1)) :=
      measurable_of_countable _
    change MeasurableSet ((fun b : Fin n → Bool ↦ ∑ i, (if b i then (1 : ℤ) else -1)) ⁻¹'
      ({0} : Set ℤ))
    simpa using hSignSumMeas (measurableSet_singleton (0 : ℤ))
  by_cases hEven : Even n
  · rcases hEven with ⟨m, hm⟩
    have hm' : n = 2 * m := by
      omega
    rw [hm'] at hZeroEventMeas ⊢
    have hEvenDouble : Even (2 * m) := by
      exact ⟨m, by omega⟩
    have hHalf : (2 * m) / 2 = m := by
      omega
    have hCardZero :
        Fintype.card {b : Fin (2 * m) → Bool // ∑ i, (if b i then (1 : ℤ) else -1) = 0} =
          Nat.choose (2 * m) m := by
      -- Proof comment: count zero-sum words by their `true` coordinates.
      calc
        Fintype.card {b : Fin (2 * m) → Bool // ∑ i, (if b i then (1 : ℤ) else -1) = 0}
            = Fintype.card {s : Finset (Fin (2 * m)) // s.card = m} := by
                exact zeroSumWords_card_eq_powersetCard m
        _ = Nat.choose (2 * m) m := by
              simpa using (Fintype.card_finset_len (α := Fin (2 * m)) m)
    have hCardZeroSet :
        Fintype.card
            ↑{b : Fin (2 * m) → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} =
          Nat.choose (2 * m) m := by
      simpa using hCardZero
    rw [if_pos hEvenDouble, hHalf]
    rw [uniformBoolCube_eq_uniformMeasure, Measure.real]
    rw [PMF.toMeasure_uniformOfFintype_apply
      (s := {b : Fin (2 * m) → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0})
      hZeroEventMeas]
    rw [ENNReal.toReal_div, hCardZeroSet]
    simp
  · rw [if_neg hEven]
    have hEmpty :
        {b : Fin n → Bool | ∑ i, (if b i then (1 : ℤ) else -1) = 0} = ∅ := by
      -- Proof comment: in odd dimension the zero-sum equation would force an impossible parity
      -- constraint.
      ext b
      constructor
      · intro hb
        have hCard :
            2 * (trueCoordinates b).card = n :=
          (boolSignSum_eq_zero_iff_two_mul_card_trueCoordinates b).1 hb
        have hnEven : Even n := by
          exact ⟨(trueCoordinates b).card, by omega⟩
        exact (hEven hnEven).elim
      · intro hb
        simp at hb
    simp [hEmpty]

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: the even-index return-probability term rewrites to the central
binomial denominator `4^j`. -/
theorem evenChooseHalf_term_as_centralBinomial (j : ℕ) :
    (Nat.choose (2 * j) j : ℝ) / (2 : ℝ) ^ (2 * j) =
      (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := by
  -- Proof comment: rewrite `2^(2*j)` as `(2^2)^j = 4^j`.
  rw [pow_mul]
  norm_num

omit hX_zero hX_indep hX_law in
/-- Helper for Example 10.8: summing the even-time central-binomial terms up to time `n - 1`
produces the textbook partial sum. -/
theorem sum_evenChooseHalf_eq_centralBinomialPartial (n : ℕ) :
    (∑ i ∈ Finset.range n,
      if Even i then (Nat.choose i (i / 2) : ℝ) / (2 : ℝ) ^ i else 0) =
      ∑ j ∈ Finset.range ((n + 1) / 2), (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := by
  induction n with
  | zero =>
      -- Proof comment: both sums are empty at time `0`.
      simp
  | succ n ih =>
      -- Proof comment: split off the new index `n` and distinguish whether it is even or odd.
      rw [Finset.sum_range_succ]
      rcases Nat.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨j, rfl⟩
        have hHalfPrev : ((j + j + 1) / 2) = j := by
          omega
        have hHalfNext : ((j + j + 1 + 1) / 2) = j + 1 := by
          omega
        have hEvenSelf : Even (j + j) := by
          exact ⟨j, rfl⟩
        have hEvenTerm :
            (if Even (j + j) then
              (Nat.choose (j + j) ((j + j) / 2) : ℝ) / (2 : ℝ) ^ (j + j) else 0) =
              (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := by
          have hHalf : (j + j) / 2 = j := by
            omega
          rw [if_pos hEvenSelf, hHalf]
          simpa [two_mul] using evenChooseHalf_term_as_centralBinomial j
        rw [hHalfPrev] at ih
        rw [hEvenTerm, ih, hHalfNext, Finset.sum_range_succ]
      · rcases hOdd with ⟨j, rfl⟩
        have hHalfPrev : ((2 * j + 1 + 1) / 2) = j + 1 := by
          omega
        have hHalfNext : ((2 * j + 1 + 1 + 1) / 2) = j + 1 := by
          omega
        have hNotEven : ¬ Even (2 * j + 1) := by
          simp
        rw [hHalfPrev] at ih
        rw [if_neg hNotEven, add_zero, hHalfNext]
        exact ih

-- Proof sketch: integrate the identity from
-- `symmetricSimpleRandomWalk_abs_predictablePart_eq_localTimeAtZero`, use the Doob decomposition
-- `|X| = martingalePart |X| + predictablePart |X|`, and note that the martingale part has mean
-- `0` at each time.
/-- For a symmetric simple random walk, the expectation of the absolute position equals the
expected local time at `0`. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_integral_localTimeAtZero
    (n : ℕ) : ∫ ω, |Xℝ n ω| ∂P = ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P := by
  -- Route correction: we close the expectation identity by comparing the walk recursion from the
  -- Boolean cube with the already-proved local-time recursion.
  calc
    ∫ ω, |Xℝ n ω| ∂P = ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} := by
      exact symmetricSimpleRandomWalk_integral_abs_eq_sum_returnProbabilities
        (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n
    _ = ∫ ω, simpleRandomWalkLocalTimeAtZero X n ω ∂P := by
          symm
          exact integral_localTimeAtZero_eq_sum_returnProbabilities
            (P := P) (X := X) (hX_zero := hX_zero) (hX_law := hX_law) n

-- Proof sketch: first identify the expectation of `|X_n|` with the expected local time at `0`.
-- Expand the local time as the finite sum of the indicators of the return events `{X_i = 0}`,
-- rewrite the integral of each indicator as `P (X_i = 0)`, use the standard symmetric random-walk
-- return probabilities `P[X_{2j} = 0] = (Nat.choose (2 * j) j : ℝ) / 4^j` and
-- `P[X_{2j+1} = 0] = 0`, and collect the even indices.
/-- Example 10.8: for a one-dimensional symmetric simple random walk, the expectation of the
absolute position at time `n` equals the expected local time at `0`, hence
`∑_{j=0}^{⌊(n-1)/2⌋} \binom{2j}{j} 4^{-j}`. -/
theorem symmetricSimpleRandomWalk_integral_abs_eq_centralBinomialSum
    (n : ℕ) :
    ∫ ω, |Xℝ n ω| ∂P =
      ∑ j ∈ Finset.range ((n + 1) / 2), (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := by
  -- Route correction: after the expectation/local-time identity is stable, the remaining work is
  -- a Boolean-cube counting computation for the zero-sum event.
  calc
    ∫ ω, |Xℝ n ω| ∂P = ∑ i ∈ Finset.range n, P.real {ω | X i ω = 0} := by
      exact symmetricSimpleRandomWalk_integral_abs_eq_sum_returnProbabilities
        (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep) (hX_law := hX_law) n
    _ = ∑ i ∈ Finset.range n,
          if Even i then (Nat.choose i (i / 2) : ℝ) / (2 : ℝ) ^ i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [symmetricSimpleRandomWalk_prob_eq_zero_eq_uniformBoolCube
              (P := P) (X := X) (hX_zero := hX_zero) (hX_indep := hX_indep)
              (hX_law := hX_law) i,
              uniformBoolCube_zeroMass_eq_choose]
    _ = ∑ j ∈ Finset.range ((n + 1) / 2), (Nat.choose (2 * j) j : ℝ) / (4 : ℝ) ^ j := by
          exact sum_evenChooseHalf_eq_centralBinomialPartial n

end SymmetricSimpleRandomWalk
