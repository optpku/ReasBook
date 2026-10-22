/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section

variable {Ω : Type u}

/-- The source-facing path from Remark 17.26, written with the chapter owner `arrivalTime`: at
time `t`, the state is the largest level `n + 1` whose arrival time is at most `t`; if infinitely
many levels have already been reached by time `t`, the path takes the cemetery value `⊤`. -/
def squareRatePureBirthPath (T : ℕ → Ω → ℝ) (t : NNReal) : Ω → WithTop ℕ :=
  fun ω ↦
    sSup {m | ∃ n : ℕ, m = (n + 1 : WithTop ℕ) ∧ arrivalTime T n ω ≤ (t : ℝ)}

/-- Helper for Remark 17.26: the total waiting time of the pure-birth path, written as the
`ℝ≥0∞` sum of all interarrival times. -/
def squareRatePureBirthTotalTime (T : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω ↦ ∑' n : ℕ, ENNReal.ofReal (T n ω)

end

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (T : ℕ → Ω → ℝ)

omit [IsProbabilityMeasure P] in
/-- Helper for Remark 17.26: each exponential waiting time has mean the reciprocal of its rate. -/
lemma squareRatePureBirthInterarrivalExpectation
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) (n : ℕ) :
    P[T n] = 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hrate : 0 < ((n + 1 : ℝ)^2) := by
    positivity
  -- Proof comment: move the expectation to the exponential reference law and use its mean
  -- formula.
  rw [(hT_law n).integral_eq]
  simpa using integral_id_expMeasure_eq_inv hrate

/-- Helper for Remark 17.26: every finite arrival time is integrable under the exponential waiting
time laws. -/
lemma squareRatePureBirthArrivalTimeIntegrable
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∀ n : ℕ, Integrable (arrivalTime T n) P
  | 0 => by
      -- Proof comment: the zeroth arrival time is the constant zero function.
      rw [arrivalTime_zero]
      exact integrable_zero Ω ℝ P
  | n + 1 => by
      -- Proof comment: split the next arrival time into the previous partial sum and the next
      -- waiting time.
      simpa [arrivalTime_succ] using
        (squareRatePureBirthArrivalTimeIntegrable hT_law n).add
          (integrableOfHasLawExp (hT_law n))

/-- Helper for Remark 17.26: the finite arrival times have the expected reciprocal-square means. -/
lemma squareRatePureBirthArrivalTimeExpectation
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∀ n : ℕ, P[arrivalTime T n] =
      ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)
  | 0 => by
      -- Proof comment: the zeroth arrival time is the empty partial sum.
      simp [arrivalTime]
  | n + 1 => by
      -- Proof comment: use the additive recursion for arrival times and insert the explicit mean
      -- of the `(n + 1)`st exponential waiting time.
      calc
        P[arrivalTime T (n + 1)]
          = P[arrivalTime T n] + P[T n] := by
              simpa [arrivalTime_succ] using
                integral_add
                  (squareRatePureBirthArrivalTimeIntegrable (P := P) (T := T) hT_law n)
                  (integrableOfHasLawExp (hT_law n))
        _ = (∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) + 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
              rw [squareRatePureBirthArrivalTimeExpectation hT_law n,
                squareRatePureBirthInterarrivalExpectation (P := P) (T := T) hT_law n]
        _ = ∑ k ∈ Finset.range (n + 1), 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
              simp [Finset.sum_range_succ]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Helper for Remark 17.26: if all waiting times on one path are nonnegative, then the
`ℝ≥0∞`-valued image of a finite arrival time is the corresponding finite partial sum of the total
time series. -/
lemma squareRatePureBirthArrivalTime_toENNReal
    {ω : Ω} (hω_nonneg : ∀ n : ℕ, 0 ≤ T n ω) (n : ℕ) :
    ENNReal.ofReal (arrivalTime T n ω) =
      ∑ i ∈ Finset.range n, ENNReal.ofReal (T i ω) := by
  -- Proof comment: `arrivalTime` is already the finite partial sum, so `ofReal` distributes over
  -- the sum once the pathwise nonnegativity is available.
  simpa [arrivalTime] using
    (ENNReal.ofReal_sum_of_nonneg (s := Finset.range n) (f := fun i ↦ T i ω)
      (fun i _ ↦ hω_nonneg i))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Helper for Remark 17.26: on every nonnegative sample path, the total waiting time is the
supremum of the finite arrival times viewed in `ℝ≥0∞`. -/
lemma squareRatePureBirthTotalTime_eq_iSup_arrivalTime_of_nonneg
    {ω : Ω} (hω_nonneg : ∀ n : ℕ, 0 ≤ T n ω) :
    squareRatePureBirthTotalTime T ω = ⨆ n : ℕ, ENNReal.ofReal (arrivalTime T n ω) := by
  -- Proof comment: rewrite the infinite `ℝ≥0∞` series as the supremum of its finite partial
  -- sums, then identify each partial sum with the corresponding arrival time.
  rw [squareRatePureBirthTotalTime, ENNReal.tsum_eq_iSup_nat]
  congr with n
  exact (squareRatePureBirthArrivalTime_toENNReal (T := T) hω_nonneg n).symm

/-- Helper for Remark 17.26: the `ℝ≥0∞`-valued total waiting time is almost surely finite under
the exponential waiting-time laws. -/
lemma squareRatePureBirthTotalTime_ae_lt_top
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∀ᵐ ω ∂P, squareRatePureBirthTotalTime T ω < ∞ := by
  have hT_nonneg : ∀ n : ℕ, 0 ≤ᵐ[P] T n := fun n ↦ aeNonnegOfHasLawExp (hT_law n)
  have hT_int : ∀ n : ℕ, Integrable (T n) P := fun n ↦ integrableOfHasLawExp (hT_law n)
  have h_meas : AEMeasurable (squareRatePureBirthTotalTime T) P := by
    -- Proof comment: the total time is the `ℝ≥0∞` series of the measurable interarrival times.
    simpa [squareRatePureBirthTotalTime] using
      (AEMeasurable.ennreal_tsum fun n ↦ (hT_law n).aemeasurable.ennreal_ofReal)
  have h_lintegral :
      ∫⁻ ω, squareRatePureBirthTotalTime T ω ∂P =
        ∑' n : ℕ, ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    calc
      ∫⁻ ω, squareRatePureBirthTotalTime T ω ∂P
          = ∑' n : ℕ, ENNReal.ofReal (∫ ω, T n ω ∂P) := by
              simpa [squareRatePureBirthTotalTime] using
                lintegral_tsum_of_nonnegative_integrable_sequence
                  (μ := P) (X := T) hT_int hT_nonneg
      _ = ∑' n : ℕ, ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
            congr with n
            rw [(hT_law n).integral_eq]
            have hrate : 0 < ((n + 1 : ℝ)^2) := by
              positivity
            simpa [Nat.cast_add, Nat.cast_one] using
              congrArg ENNReal.ofReal (integral_id_expMeasure_eq_inv hrate)
  have hsummable :
      Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).congr ?_
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      positivity
    simp [abs_of_nonneg hn]
  have h_ne_top :
      ∫⁻ ω, squareRatePureBirthTotalTime T ω ∂P ≠ ∞ := by
    rw [h_lintegral]
    exact hsummable.tsum_ofReal_lt_top.ne
  -- Proof comment: finite lower integral forces almost-sure finiteness of the `ℝ≥0∞`-valued
  -- total-time series.
  exact ae_lt_top' h_meas h_ne_top

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Helper for Remark 17.26: if every arrival time is already at most `t`, then the path has
reached the cemetery state `⊤` by time `t`. -/
lemma squareRatePureBirthPath_eq_top_of_bddArrivalTimes
    {t : NNReal} {ω : Ω}
    (harr : ∀ n : ℕ, arrivalTime T n ω ≤ (t : ℝ)) :
    squareRatePureBirthPath T t ω = ⊤ := by
  let S : Set (WithTop ℕ) :=
    {m | ∃ n : ℕ, m = (n + 1 : WithTop ℕ) ∧ arrivalTime T n ω ≤ (t : ℝ)}
  have hmem : ∀ n : ℕ, ((n + 1 : ℕ) : WithTop ℕ) ∈ S := by
    intro n
    exact ⟨n, rfl, harr n⟩
  -- Proof comment: every positive level belongs to the defining set, so the supremum cannot be a
  -- finite natural number.
  rw [squareRatePureBirthPath]
  refine WithTop.eq_top_iff_forall_ge.2 ?_
  intro N
  have hle_succ : ((N : ℕ) : WithTop ℕ) ≤ ((N + 1 : ℕ) : WithTop ℕ) :=
    WithTop.coe_le_coe.2 (Nat.le_succ N)
  exact le_trans hle_succ (le_sSup (hmem N))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Helper for Remark 17.26: a finite total waiting time bounds every arrival time by its
`toReal`, so the explicit path has already reached `⊤` by that time. -/
lemma squareRatePureBirthPath_eq_top_of_totalTime_lt_top
    {ω : Ω}
    (hω_nonneg : ∀ n : ℕ, 0 ≤ T n ω)
    (hω_fin : squareRatePureBirthTotalTime T ω < ∞) :
    let t : NNReal := ⟨(squareRatePureBirthTotalTime T ω).toReal, ENNReal.toReal_nonneg⟩
    squareRatePureBirthPath T t ω = ⊤ := by
  dsimp
  refine squareRatePureBirthPath_eq_top_of_bddArrivalTimes
      (T := T)
      (ω := ω)
      (t := ⟨(squareRatePureBirthTotalTime T ω).toReal, ENNReal.toReal_nonneg⟩) ?_
  intro n
  have hle_enn :
      ENNReal.ofReal (arrivalTime T n ω) ≤ squareRatePureBirthTotalTime T ω := by
    -- Proof comment: every finite arrival time is one term of the supremum describing the total
    -- waiting time.
    rw [squareRatePureBirthTotalTime_eq_iSup_arrivalTime_of_nonneg (T := T) hω_nonneg]
    exact le_iSup (fun m : ℕ ↦ ENNReal.ofReal (arrivalTime T m ω)) n
  -- Proof comment: the finite `ℝ≥0∞` total time can be transported back to a real bound via
  -- `toReal`.
  exact (ENNReal.ofReal_le_iff_le_toReal hω_fin.ne).1 hle_enn

/-- Helper for Remark 17.26: under the exponential waiting-time laws, the explicit square-rate
pure-birth path reaches `⊤` almost surely in finite time. -/
lemma squareRatePureBirth_ae_explosion
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    ∀ᵐ ω ∂P, ∃ t : NNReal, squareRatePureBirthPath T t ω = ⊤ := by
  have h_nonneg : ∀ n : ℕ, 0 ≤ᵐ[P] T n := fun n ↦ aeNonnegOfHasLawExp (hT_law n)
  have h_all_nonneg : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 ≤ T n ω := ae_all_iff.2 h_nonneg
  -- Proof comment: on the full-measure event where every waiting time is nonnegative and the
  -- total time is finite, the total time itself supplies the exploding horizon.
  filter_upwards
      [h_all_nonneg, squareRatePureBirthTotalTime_ae_lt_top (P := P) (T := T) hT_law]
      with ω hω_nonneg hω_fin
  refine ⟨⟨(squareRatePureBirthTotalTime T ω).toReal, ENNReal.toReal_nonneg⟩, ?_⟩
  exact squareRatePureBirthPath_eq_top_of_totalTime_lt_top
    (T := T) (ω := ω) hω_nonneg hω_fin

-- Proof sketch: each level time is a finite sum of waiting times, so its expectation is the sum
-- of the exponential means `1 / (k + 1)^2`; the total waiting-time series is almost surely
-- finite, and its `toReal` therefore bounds every arrival time and forces explosion.
/-- Remark 17.26: if the waiting times `T n` have the laws `Exp((n + 1)^2)`, then the arrival time
of level `n + 1` has expectation `∑_{k=1}^n 1 / k^2`, and the associated explicit square-rate
pure-birth path explodes almost surely in finite time. -/
theorem squareRatePureBirth_expectedLevelTime_and_ae_explosion
    (hT_law : ∀ n : ℕ, HasLaw (T n) (expMeasure ((n + 1 : ℝ)^2)) P) :
    (∀ n : ℕ, P[arrivalTime T n] =
      ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) ∧
    ∀ᵐ ω ∂P, ∃ t : NNReal, squareRatePureBirthPath T t ω = ⊤ := by
  -- Proof comment: the first component is the arrival-time expectation recursion, and the second
  -- component is the almost-sure explosion obtained from the finite total waiting time.
  exact ⟨squareRatePureBirthArrivalTimeExpectation (P := P) (T := T) hT_law,
    squareRatePureBirth_ae_explosion (P := P) (T := T) hT_law⟩

end

end ProbabilityTheory
