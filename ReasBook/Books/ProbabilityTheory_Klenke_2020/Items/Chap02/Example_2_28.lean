/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_64

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Classical

universe u

/-- Helper for Example 2.28: the one-step Bernoulli law on `Bool` with parameter `p`. -/
noncomputable abbrev bernoulliBoolMeasure (p : NNReal) (hp_lt_one : p < 1) : Measure Bool :=
  (PMF.bernoulli p hp_lt_one.le).toMeasure

/-- Helper for Example 2.28: the canonical Bernoulli product law on `Bool^ℕ`. -/
noncomputable abbrev bernoulliSequenceMeasure (p : NNReal) (hp_lt_one : p < 1) :
    Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ ↦ bernoulliBoolMeasure p hp_lt_one)

/-- Helper for Example 2.28: the mass of an all-failure prefix of length `n`. -/
abbrev failurePrefixMass (p : NNReal) (n : ℕ) : NNReal :=
  (1 - p) ^ n

/-- Helper for Example 2.28: the geometric mass `p (1 - p)^n` on `ℕ`. -/
abbrev geometricMass (p : NNReal) (n : ℕ) : NNReal :=
  failurePrefixMass p n * p

/-- In Lean's `0`-based indexing, the waiting time to the first success in row `m` of a
Bernoulli matrix is the least column index at which a success occurs, equivalently the number of
initial failures before the first success. If row `m` has no success at all, the waiting time is
`⊤`. -/
noncomputable def rowFirstSuccessWaitingTime {Ω : Type u} (X : ℕ → ℕ → Ω → Bool) :
    ℕ → Ω → ℕ∞ :=
  fun m ω ↦
    if h : ∃ n : ℕ, X m n ω = true then (Nat.find h : ℕ∞) else ⊤

@[simp] theorem rowFirstSuccessWaitingTime_eq_top_iff {Ω : Type u} (X : ℕ → ℕ → Ω → Bool)
    {m : ℕ}
    {ω : Ω} :
    rowFirstSuccessWaitingTime X m ω = ⊤ ↔ ¬ ∃ n : ℕ, X m n ω = true := by
  by_cases h : ∃ n : ℕ, X m n ω = true
  · simp [rowFirstSuccessWaitingTime, h]
  · simp [rowFirstSuccessWaitingTime, h]

@[simp] theorem rowFirstSuccessWaitingTime_ne_top_iff {Ω : Type u} (X : ℕ → ℕ → Ω → Bool)
    {m : ℕ} {ω : Ω} :
    rowFirstSuccessWaitingTime X m ω ≠ ⊤ ↔ ∃ n : ℕ, X m n ω = true := by
  constructor
  · intro h
    by_contra hX
    exact h ((rowFirstSuccessWaitingTime_eq_top_iff X).2 hX)
  · intro h
    exact fun htop ↦ ((rowFirstSuccessWaitingTime_eq_top_iff X).1 htop) h

/-- The finite value `n` of the canonical waiting time means exactly that the first success in
row `m` occurs at column `n`. -/
@[simp] theorem rowFirstSuccessWaitingTime_eq_coe_iff {Ω : Type u} (X : ℕ → ℕ → Ω → Bool)
    {m n : ℕ} {ω : Ω} :
    rowFirstSuccessWaitingTime X m ω = (n : ℕ∞) ↔
      X m n ω = true ∧ ∀ k < n, X m k ω = false := by
  by_cases h : ∃ k : ℕ, X m k ω = true
  · simp [rowFirstSuccessWaitingTime, h, Nat.find_eq_iff]
  · have hn : X m n ω ≠ true := fun hn ↦ h ⟨n, hn⟩
    simp [rowFirstSuccessWaitingTime, h, hn]

/-- Helper for Example 2.28: the `m`th row of the Bernoulli matrix viewed as a sequence in
`Bool^ℕ`. -/
abbrev rowProcess {Ω : Type u} (X : ℕ → ℕ → Ω → Bool) (m : ℕ) : Ω → (ℕ → Bool) :=
  fun ω n ↦ X m n ω

/-- Helper for Example 2.28: the canonical first-success waiting-time functional on `Bool^ℕ`. -/
noncomputable abbrev rowSequenceWaitingTime : (ℕ → Bool) → ℕ∞ :=
  rowFirstSuccessWaitingTime (fun _ n ω ↦ ω n) 0

/-- Helper for Example 2.28: the matrix-level waiting time is the canonical sequence waiting time
applied to the corresponding row. -/
theorem rowFirstSuccessWaitingTime_eq_rowSequenceWaitingTime {Ω : Type u}
    (X : ℕ → ℕ → Ω → Bool) (m : ℕ) :
    rowFirstSuccessWaitingTime X m = fun ω ↦ rowSequenceWaitingTime (rowProcess X m ω) := by
  rfl

/-- Helper for Example 2.28: the `⊤` value means that every entry in the sequence is `false`. -/
@[simp] theorem rowSequenceWaitingTime_eq_top_iff {ω : ℕ → Bool} :
    rowSequenceWaitingTime ω = ⊤ ↔ ∀ n, ω n = false := by
  -- Translate the top fiber into the absence of any success in the sequence.
  rw [rowSequenceWaitingTime, rowFirstSuccessWaitingTime_eq_top_iff]
  constructor
  · intro h n
    by_contra hn
    cases hω : ω n <;> simp [hω] at hn
    exact h ⟨n, hω⟩
  · intro h hω
    rcases hω with ⟨n, hn⟩
    simp [h n] at hn

/-- Helper for Example 2.28: the finite value `n` means exactly `n` initial failures followed by a
success at time `n`. -/
@[simp] theorem rowSequenceWaitingTime_eq_coe_iff {ω : ℕ → Bool} {n : ℕ} :
    rowSequenceWaitingTime ω = (n : ℕ∞) ↔ ω n = true ∧ ∀ k < n, ω k = false := by
  simpa [rowSequenceWaitingTime, rowProcess] using
    (rowFirstSuccessWaitingTime_eq_coe_iff (X := fun _ n ω ↦ ω n) (m := 0) (ω := ω) (n := n))

/-- Helper for Example 2.28: the event that the first `n` entries in a Bernoulli sequence are all
`false`. -/
def rowFailurePrefixEvent (n : ℕ) : Set (ℕ → Bool) :=
  {ω | ∀ i : Fin n, ω i = false}

/-- Helper for Example 2.28: each finite all-failure prefix event is measurable. -/
theorem measurableSet_rowFailurePrefixEvent (n : ℕ) :
    MeasurableSet (rowFailurePrefixEvent n) := by
  -- View the first `n` coordinates as a finite-dimensional measurable projection.
  let prefixMap : (ℕ → Bool) → Fin n → Bool := fun ω i ↦ ω i
  have hprefix : Measurable prefixMap := by
    fun_prop
  have hset :
      rowFailurePrefixEvent n =
        {ω : ℕ → Bool | prefixMap ω = fun _ : Fin n ↦ false} := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congr_fun h i
  rw [hset]
  exact hprefix (measurableSet_singleton (fun _ : Fin n ↦ false))

/-- Helper for Example 2.28: the length-`n + 1` cylinder with `n` failures followed by one
success. -/
def firstSuccessPattern (n : ℕ) : Fin (n + 1) → Bool :=
  fun i ↦ if i = Fin.last n then true else false

/-- Helper for Example 2.28: the finite waiting-time fiber is the cylinder with `n` initial
failures and a success at time `n`. -/
theorem rowSequenceWaitingTime_preimage_singleton_coe (n : ℕ) :
    {ω : ℕ → Bool | rowSequenceWaitingTime ω = (n : ℕ∞)} =
      {ω : ℕ → Bool | ∀ i : Fin (n + 1), ω i = firstSuccessPattern n i} := by
  ext ω
  constructor
  · intro hω i
    change rowSequenceWaitingTime ω = (n : ℕ∞) at hω
    rw [rowSequenceWaitingTime_eq_coe_iff] at hω
    refine Fin.lastCases ?_ ?_ i
    · simp [firstSuccessPattern, hω.1]
    · intro j
      simp [firstSuccessPattern, Fin.castSucc_ne_last, hω.2 j j.is_lt]
  · intro hω
    change rowSequenceWaitingTime ω = (n : ℕ∞)
    rw [rowSequenceWaitingTime_eq_coe_iff]
    constructor
    · simpa [firstSuccessPattern] using hω (Fin.last n)
    · intro k hk
      let j : Fin n := ⟨k, hk⟩
      have hj : firstSuccessPattern n j.castSucc = false := by
        simp [firstSuccessPattern, Fin.castSucc_ne_last]
      have hωj := hω j.castSucc
      rwa [hj] at hωj

/-- Helper for Example 2.28: the `⊤` fiber is the intersection of the finite all-failure prefix
events. -/
theorem rowSequenceWaitingTime_preimage_top :
    {ω : ℕ → Bool | rowSequenceWaitingTime ω = ⊤} = ⋂ n, rowFailurePrefixEvent n := by
  ext ω
  simp [rowFailurePrefixEvent]
  constructor
  · intro h n i
    exact h i
  · intro h n
    exact h (n + 1) (Fin.last n)

/-- Helper for Example 2.28: each finite singleton fiber of the canonical waiting-time functional
is measurable. -/
theorem measurableSet_rowSequenceWaitingTime_preimage_singleton (n : ℕ) :
    MeasurableSet {ω : ℕ → Bool | rowSequenceWaitingTime ω = (n : ℕ∞)} := by
  rw [rowSequenceWaitingTime_preimage_singleton_coe]
  let prefixMap : (ℕ → Bool) → Fin (n + 1) → Bool := fun ω i ↦ ω i
  have hprefix : Measurable prefixMap := by
    fun_prop
  have hset :
      {ω : ℕ → Bool | ∀ i : Fin (n + 1), ω i = firstSuccessPattern n i} =
        {ω : ℕ → Bool | prefixMap ω = firstSuccessPattern n} := by
    ext ω
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congr_fun h i
  rw [hset]
  exact hprefix (measurableSet_singleton _)

/-- Helper for Example 2.28: the canonical waiting-time functional on `Bool^ℕ` is measurable. -/
theorem measurable_rowSequenceWaitingTime : Measurable rowSequenceWaitingTime := by
  refine (ENat.measurable_iff).2 ?_
  intro n
  exact measurableSet_rowSequenceWaitingTime_preimage_singleton n

/-- Helper for Example 2.28: under the Bernoulli product law, an all-false prefix of length `n`
has mass `(1 - p)^n`. -/
theorem bernoulliSequenceMeasure_rowFailurePrefixEvent {p : NNReal} (hp_lt_one : p < 1) (n : ℕ) :
    (bernoulliSequenceMeasure p hp_lt_one) (rowFailurePrefixEvent n) =
      ENNReal.ofReal (failurePrefixMass p n) := by
  -- Apply the initial-cylinder formula to the constant all-false pattern.
  simpa [bernoulliSequenceMeasure, bernoulliBoolMeasure, rowFailurePrefixEvent,
    PMF.bernoulli_apply] using
    (bernoulliMeasure_apply_initialCylinder (PMF.bernoulli p hp_lt_one.le) n
      (fun _ : Fin n ↦ false))

/-- Helper for Example 2.28: under the Bernoulli product law, the finite waiting-time fiber at `n`
has mass `p (1 - p)^n`. -/
theorem bernoulliSequenceMeasure_rowSequenceWaitingTime_singleton {p : NNReal}
    (hp_lt_one : p < 1) (n : ℕ) :
    (bernoulliSequenceMeasure p hp_lt_one)
      {ω : ℕ → Bool | rowSequenceWaitingTime ω = (n : ℕ∞)} =
      ENNReal.ofReal (geometricMass p n) := by
  -- Rewrite the fiber as the initial cylinder with `n` failures followed by one success.
  rw [rowSequenceWaitingTime_preimage_singleton_coe]
  calc
    (bernoulliSequenceMeasure p hp_lt_one)
        {ω : ℕ → Bool | ∀ i : Fin (n + 1), ω i = firstSuccessPattern n i}
        = ∏ i : Fin (n + 1), PMF.bernoulli p hp_lt_one.le (firstSuccessPattern n i) := by
            simpa [bernoulliSequenceMeasure, bernoulliBoolMeasure] using
              (bernoulliMeasure_apply_initialCylinder (PMF.bernoulli p hp_lt_one.le) (n + 1)
                (firstSuccessPattern n))
    _ = ENNReal.ofReal (geometricMass p n) := by
          rw [Fin.prod_univ_castSucc]
          simp [firstSuccessPattern, geometricMass, failurePrefixMass, PMF.bernoulli_apply,
            Fin.castSucc_ne_last, ENNReal.ofReal_coe_nnreal]

/-- Helper for Example 2.28: the geometric law on `ℕ` assigns mass `p (1 - p)^n` to `{n}`. -/
theorem geometricMeasure_apply_singleton {p : NNReal} (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (n : ℕ) :
    geometricMeasure
      (show 0 < (p : ℝ) from hp_pos)
      (show (p : ℝ) ≤ 1 from hp_lt_one.le)
      ({n} : Set ℕ) =
        ENNReal.ofReal (geometricMass p n) := by
  -- Evaluate the singleton mass of the geometric PMF and then unfold the closed form.
  calc
    geometricMeasure
        (show 0 < (p : ℝ) from hp_pos)
        (show (p : ℝ) ≤ 1 from hp_lt_one.le)
        ({n} : Set ℕ)
        = geometricPMF (show 0 < (p : ℝ) from hp_pos) (show (p : ℝ) ≤ 1 from hp_lt_one.le) n := by
            rw [geometricMeasure]
            exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)
    _ = ENNReal.ofReal (geometricMass p n) := by
          change ENNReal.ofReal (((1 - (p : ℝ)) ^ n) * (p : ℝ)) =
            ENNReal.ofReal (geometricMass p n)
          congr 1
          rw [geometricMass, failurePrefixMass, NNReal.coe_mul, NNReal.coe_pow,
            NNReal.coe_sub hp_lt_one.le]
          norm_num

/-- Helper for Example 2.28: the all-failure path has Bernoulli-product mass `0` when
`0 < p < 1`. -/
theorem bernoulliSequenceMeasure_rowSequenceWaitingTime_top {p : NNReal} (hp_pos : 0 < p)
    (hp_lt_one : p < 1) :
    (bernoulliSequenceMeasure p hp_lt_one) {ω : ℕ → Bool | rowSequenceWaitingTime ω = ⊤} = 0 := by
  have hmono : Antitone rowFailurePrefixEvent := by
    intro m n hmn ω hω i
    exact hω ⟨i, lt_of_lt_of_le i.is_lt hmn⟩
  have hfinite :
      ∃ n, (bernoulliSequenceMeasure p hp_lt_one) (rowFailurePrefixEvent n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    simpa [rowFailurePrefixEvent] using
      (show (bernoulliSequenceMeasure p hp_lt_one) Set.univ ≠ ⊤ by simp)
  have hlt : (1 - p : NNReal) < 1 := by
    have hlt_real : (((1 - p : NNReal) : ℝ) < 1) := by
      rw [NNReal.coe_sub hp_lt_one.le]
      simpa using sub_lt_self (1 : ℝ) (show (0 : ℝ) < p from hp_pos)
    exact_mod_cast hlt_real
  have hpow : Tendsto (fun n : ℕ ↦ failurePrefixMass p n) atTop (nhds (0 : NNReal)) := by
    simpa [failurePrefixMass] using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - p) hlt)
  have hprefix_tendsto :
      Tendsto
        (fun n : ℕ ↦ (bernoulliSequenceMeasure p hp_lt_one) (rowFailurePrefixEvent n))
        atTop
        (nhds (0 : ENNReal)) := by
    have hpow_enn :
        Tendsto (fun n : ℕ ↦ ((failurePrefixMass p n : NNReal) : ENNReal)) atTop
          (nhds (0 : ENNReal)) :=
      (ENNReal.continuous_coe.tendsto (0 : NNReal)).comp hpow
    have hpow_enn' :
        Tendsto (fun n : ℕ ↦ ENNReal.ofReal (failurePrefixMass p n)) atTop
          (nhds (0 : ENNReal)) := by
      simpa [ENNReal.ofReal_coe_nnreal] using hpow_enn
    have hrewrite :
        (fun n : ℕ ↦ (bernoulliSequenceMeasure p hp_lt_one) (rowFailurePrefixEvent n)) =
          fun n : ℕ ↦ ENNReal.ofReal (failurePrefixMass p n) := by
      funext n
      exact bernoulliSequenceMeasure_rowFailurePrefixEvent hp_lt_one n
    simpa [hrewrite] using hpow_enn'
  have hinter_tendsto :
      Tendsto
        (fun n : ℕ ↦ (bernoulliSequenceMeasure p hp_lt_one) (rowFailurePrefixEvent n))
        atTop
        (nhds ((bernoulliSequenceMeasure p hp_lt_one) (⋂ n, rowFailurePrefixEvent n))) :=
    tendsto_measure_iInter_atTop
      (μ := bernoulliSequenceMeasure p hp_lt_one)
      (s := rowFailurePrefixEvent)
      (fun n ↦ (measurableSet_rowFailurePrefixEvent n).nullMeasurableSet)
      hmono
      hfinite
  have hinter :
      (bernoulliSequenceMeasure p hp_lt_one) (⋂ n, rowFailurePrefixEvent n) = 0 :=
    tendsto_nhds_unique hinter_tendsto hprefix_tendsto
  -- Rewrite the top fiber as the decreasing intersection of all-failure prefix events.
  rw [rowSequenceWaitingTime_preimage_top, hinter]

/-- Helper for Example 2.28: on the canonical Bernoulli product space, the first-success waiting
time has the geometric law pushed forward from `ℕ` to `ℕ∞`. -/
theorem hasLaw_rowSequenceWaitingTime_bernoulliProduct {p : NNReal} (hp_pos : 0 < p)
    (hp_lt_one : p < 1) :
    HasLaw rowSequenceWaitingTime
      (Measure.map (fun n : ℕ ↦ (n : ℕ∞))
        (geometricMeasure
          (show 0 < (p : ℝ) from hp_pos)
          (show (p : ℝ) ≤ 1 from hp_lt_one.le)))
      (bernoulliSequenceMeasure p hp_lt_one) := by
  refine ⟨measurable_rowSequenceWaitingTime.aemeasurable, ?_⟩
  let hcoe : Measurable (fun n : ℕ ↦ (n : ℕ∞)) := measurable_of_countable _
  -- Both laws are discrete on `ℕ∞`, so singleton fibers determine the whole measure.
  refine Measure.ext_of_singleton ?_
  intro x
  refine ENat.recTopCoe ?_ ?_ x
  · rw [Measure.map_apply measurable_rowSequenceWaitingTime (measurableSet_singleton ⊤)]
    rw [Measure.map_apply hcoe (measurableSet_singleton ⊤)]
    change (bernoulliSequenceMeasure p hp_lt_one) {ω : ℕ → Bool | rowSequenceWaitingTime ω = ⊤} =
      geometricMeasure
        (show 0 < (p : ℝ) from hp_pos)
        (show (p : ℝ) ≤ 1 from hp_lt_one.le)
        (((fun n : ℕ ↦ (n : ℕ∞)) ⁻¹' ({⊤} : Set ℕ∞)))
    rw [bernoulliSequenceMeasure_rowSequenceWaitingTime_top (hp_pos := hp_pos) (hp_lt_one := hp_lt_one)]
    have hpreimageTop :
        ((fun n : ℕ ↦ (n : ℕ∞)) ⁻¹' ({⊤} : Set ℕ∞)) = (∅ : Set ℕ) := by
      ext m
      simp
    rw [hpreimageTop]
    simp
  · intro n
    rw [Measure.map_apply measurable_rowSequenceWaitingTime (measurableSet_singleton (n : ℕ∞))]
    rw [Measure.map_apply hcoe (measurableSet_singleton (n : ℕ∞))]
    change (bernoulliSequenceMeasure p hp_lt_one)
      {ω : ℕ → Bool | rowSequenceWaitingTime ω = (n : ℕ∞)} =
        geometricMeasure
          (show 0 < (p : ℝ) from hp_pos)
          (show (p : ℝ) ≤ 1 from hp_lt_one.le)
          (((fun m : ℕ ↦ (m : ℕ∞)) ⁻¹' ({(n : ℕ∞)} : Set ℕ∞)))
    rw [bernoulliSequenceMeasure_rowSequenceWaitingTime_singleton (hp_lt_one := hp_lt_one) (n := n)]
    have hpreimageCoe :
        ((fun m : ℕ ↦ (m : ℕ∞)) ⁻¹' ({(n : ℕ∞)} : Set ℕ∞)) = ({n} : Set ℕ) := by
      ext m
      simp
    rw [hpreimageCoe]
    rw [geometricMeasure_apply_singleton (hp_pos := hp_pos) (hp_lt_one := hp_lt_one) (n := n)]

/-- Helper for Example 2.28: the full matrix law curries to the product law of the row process
family. -/
theorem hasLaw_rowProcessFamily_of_iIndepFun_bernoulliMatrix
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_lt_one : p < 1)
    (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) (bernoulliBoolMeasure p hp_lt_one) P) :
    HasLaw (fun ω m ↦ rowProcess X m ω)
      (Measure.infinitePi fun _ : ℕ ↦ bernoulliSequenceMeasure p hp_lt_one)
      P := by
  letI : IsProbabilityMeasure P := (h_bernoulli 0 0).isProbabilityMeasure
  have hpair :
      HasLaw (fun ω : Ω ↦ fun mn : ℕ × ℕ ↦ X mn.1 mn.2 ω)
        (Measure.infinitePi fun _ : ℕ × ℕ ↦ bernoulliBoolMeasure p hp_lt_one)
        P := by
    refine ⟨aemeasurable_pi_iff.2 (fun mn ↦ (h_bernoulli mn.1 mn.2).aemeasurable), ?_⟩
    -- Identify the joint law of the matrix with the Bernoulli product law on `Bool^(ℕ×ℕ)`.
    calc
      P.map (fun ω : Ω ↦ fun mn : ℕ × ℕ ↦ X mn.1 mn.2 ω)
          = Measure.infinitePi (fun mn : ℕ × ℕ ↦ P.map (X mn.1 mn.2)) := by
            exact
              (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
                (P := P)
                (X := fun mn : ℕ × ℕ ↦ X mn.1 mn.2)
                (fun mn ↦ (h_bernoulli mn.1 mn.2).aemeasurable)).1 h_indep
      _ = Measure.infinitePi (fun _ : ℕ × ℕ ↦ bernoulliBoolMeasure p hp_lt_one) := by
            congr 1
            funext mn
            exact (h_bernoulli mn.1 mn.2).map_eq
  have hcurry :
      HasLaw (MeasurableEquiv.curry ℕ ℕ Bool)
        (Measure.infinitePi fun _ : ℕ ↦ bernoulliSequenceMeasure p hp_lt_one)
        (Measure.infinitePi fun _ : ℕ × ℕ ↦ bernoulliBoolMeasure p hp_lt_one) := by
    refine ⟨(MeasurableEquiv.curry ℕ ℕ Bool).measurable.aemeasurable, ?_⟩
    simpa [bernoulliSequenceMeasure] using
      (Measure.infinitePi_map_curry (μ := fun _ _ : ℕ ↦ bernoulliBoolMeasure p hp_lt_one))
  -- Curry the pair-indexed law into a product law for the row process family.
  simpa [rowProcess, Function.comp] using hcurry.comp hpair

/-- Helper for Example 2.28: each row process has the canonical Bernoulli product law. -/
theorem hasLaw_rowProcess_of_iIndepFun_bernoulliMatrix
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_lt_one : p < 1)
    (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) (bernoulliBoolMeasure p hp_lt_one) P)
    (m : ℕ) :
    HasLaw (rowProcess X m) (bernoulliSequenceMeasure p hp_lt_one) P := by
  have hfamily :=
    hasLaw_rowProcessFamily_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli
  have heval :
      HasLaw (Function.eval m) (bernoulliSequenceMeasure p hp_lt_one)
        (Measure.infinitePi fun _ : ℕ ↦ bernoulliSequenceMeasure p hp_lt_one) := by
    simpa using
      (MeasurePreserving.hasLaw
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ bernoulliSequenceMeasure p hp_lt_one) m))
  -- Extract the `m`th row from the joint row-process law.
  simpa [rowProcess, Function.comp] using heval.comp hfamily

/-- Helper for Example 2.28: the row processes are independent. -/
theorem iIndepFun_rowProcess_of_iIndepFun_bernoulliMatrix
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_lt_one : p < 1)
    (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) (bernoulliBoolMeasure p hp_lt_one) P) :
    iIndepFun (rowProcess X) P := by
  letI : IsProbabilityMeasure P := (h_bernoulli 0 0).isProbabilityMeasure
  have hfamily :=
    hasLaw_rowProcessFamily_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli
  have hrow : ∀ m, HasLaw (rowProcess X m) (bernoulliSequenceMeasure p hp_lt_one) P := by
    intro m
    exact hasLaw_rowProcess_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli m
  -- Compare the joint row law with the product of the row marginals.
  refine
    (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
      (P := P)
      (X := rowProcess X)
      (fun m ↦ (hrow m).aemeasurable)).2 ?_
  calc
    P.map (fun ω m ↦ rowProcess X m ω)
        = Measure.infinitePi (fun _ : ℕ ↦ bernoulliSequenceMeasure p hp_lt_one) := by
          exact hfamily.map_eq
    _ = Measure.infinitePi (fun m : ℕ ↦ P.map (rowProcess X m)) := by
          congr 1
          funext m
          symm
          exact (hrow m).map_eq

-- Proof sketch: each row waiting time is measurable with respect to the `σ`-algebra generated by
-- that row, so independence follows from the independence of disjoint rows. For the law, compute
-- the tail event `rowFirstSuccessWaitingTime X m > k` as the event that the first `k + 1`
-- Bernoulli entries in row `m` are all `false`, then identify the resulting mass function with
-- `geometricMeasure`; the canonical `ℕ∞`-valued waiting time is the pushforward of this
-- geometric law along the inclusion `ℕ ↪ ℕ∞`.
/-- If the entries of a Boolean matrix are independent Bernoulli random variables with parameter
`p ∈ (0,1)`, then the canonical waiting times for the first success in each row form an
independent family. -/
theorem iIndepFun_rowFirstSuccessWaitingTime_of_iIndepFun_bernoulliMatrix
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_pos : 0 < p)
    (hp_lt_one : p < 1) (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) ((PMF.bernoulli p hp_lt_one.le).toMeasure) P) :
    iIndepFun (rowFirstSuccessWaitingTime X) P := by
  letI : IsProbabilityMeasure P := (h_bernoulli 0 0).isProbabilityMeasure
  have hrow :
      iIndepFun (rowProcess X) P :=
    iIndepFun_rowProcess_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli
  have hrowLaw : ∀ m, HasLaw (rowProcess X m) (bernoulliSequenceMeasure p hp_lt_one) P := by
    intro m
    exact hasLaw_rowProcess_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli m
  have hwaiting :
      ∀ m, AEMeasurable rowSequenceWaitingTime (P.map (rowProcess X m)) := by
    intro m
    rw [(hrowLaw m).map_eq]
    exact (hasLaw_rowSequenceWaitingTime_bernoulliProduct hp_pos hp_lt_one).aemeasurable
  -- Compose the independent row processes with the canonical waiting-time functional.
  have hcomp :=
    hrow.comp₀ (fun _ ↦ rowSequenceWaitingTime) (fun m ↦ (hrowLaw m).aemeasurable) hwaiting
  have hEq : (fun m ↦ rowSequenceWaitingTime ∘ rowProcess X m) = rowFirstSuccessWaitingTime X := by
    funext m
    exact rowFirstSuccessWaitingTime_eq_rowSequenceWaitingTime X m
  exact hEq ▸ hcomp

/-- If the entries of a Boolean matrix are independent Bernoulli random variables with parameter
`p ∈ (0,1)`, then each canonical waiting time to the first success has the geometric law with
parameter `p`, pushed forward along the inclusion `ℕ ↪ ℕ∞`. With Lean's `0`-based
indexing, the finite values still count the number of failures before the first success. -/
theorem hasLaw_rowFirstSuccessWaitingTime_of_iIndepFun_bernoulliMatrix
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_pos : 0 < p)
    (hp_lt_one : p < 1) (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) ((PMF.bernoulli p hp_lt_one.le).toMeasure) P) :
    ∀ m,
      HasLaw (rowFirstSuccessWaitingTime X m)
        (Measure.map (fun n : ℕ ↦ (n : ℕ∞))
          (geometricMeasure
            (show 0 < (p : ℝ) from hp_pos)
            (show (p : ℝ) ≤ 1 from hp_lt_one.le)))
        P := by
  intro m
  have hrow :
      HasLaw (rowProcess X m) (bernoulliSequenceMeasure p hp_lt_one) P :=
    hasLaw_rowProcess_of_iIndepFun_bernoulliMatrix P hp_lt_one X h_indep h_bernoulli m
  -- Transport the canonical Bernoulli-sequence waiting-time law to the `m`th row.
  have hcomp := (hasLaw_rowSequenceWaitingTime_bernoulliProduct hp_pos hp_lt_one).comp hrow
  have hEq : rowSequenceWaitingTime ∘ rowProcess X m = rowFirstSuccessWaitingTime X m :=
    rowFirstSuccessWaitingTime_eq_rowSequenceWaitingTime X m
  exact hEq ▸ hcomp

/-- Example 2.28: if the entries of a Boolean matrix are independent Bernoulli random variables
with parameter `p ∈ (0,1)`, then the canonical waiting times for the first success in each row
form an independent family, and each row waiting time has the geometric law with parameter `p`,
transported along `ℕ ↪ ℕ∞`. -/
theorem example_2_28
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : NNReal} (hp_pos : 0 < p)
    (hp_lt_one : p < 1) (X : ℕ → ℕ → Ω → Bool)
    (h_indep : iIndepFun (fun mn : ℕ × ℕ ↦ X mn.1 mn.2) P)
    (h_bernoulli : ∀ m n, HasLaw (X m n) ((PMF.bernoulli p hp_lt_one.le).toMeasure) P) :
    iIndepFun (rowFirstSuccessWaitingTime X) P ∧
      ∀ m,
        HasLaw (rowFirstSuccessWaitingTime X m)
          (Measure.map (fun n : ℕ ↦ (n : ℕ∞))
            (geometricMeasure
              (show 0 < (p : ℝ) from hp_pos)
              (show (p : ℝ) ≤ 1 from hp_lt_one.le)))
          P := by
  exact
    ⟨iIndepFun_rowFirstSuccessWaitingTime_of_iIndepFun_bernoulliMatrix P hp_pos hp_lt_one X
        h_indep h_bernoulli,
      hasLaw_rowFirstSuccessWaitingTime_of_iIndepFun_bernoulliMatrix P hp_pos hp_lt_one X
        h_indep h_bernoulli⟩
