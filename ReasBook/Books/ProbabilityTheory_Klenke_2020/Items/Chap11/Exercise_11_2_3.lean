/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Exercise_10_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Corollary_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Exercise 11.2.3 is `source-facing`: it asserts the existence of a filtered probability space
carrying a square-integrable martingale that converges almost surely to its canonical limit process
without converging in `L²`. Its `core/canonical` owner layer is the chapter API around
`Martingale`, `Filtration.limitProcess`, and `TendstoInLp`; the `eLpNorm` formulation is only the
derived `bridge/view` from `tendstoInLp_iff_tendsto_eLpNorm`, so the main declaration stays owner-
shaped instead of exposing a parallel bridge-level interface. -/

-- Proof sketch: use a standard square-integrable martingale with almost-sure limit whose second
-- moments are not uniformly bounded, so Corollary 11.11 does not apply; then identify the almost-
-- sure limit with the canonical `limitProcess` and show that the `L²` distance to that limit does
-- not tend to `0`.

section Counterexample

/-- Helper for Exercise 11.2.3: the witness sample space is `ULift ℕ`, viewed in universe `u`. -/
private abbrev Omega0 : Type u := ULift ℕ

/-- Helper for Exercise 11.2.3: the geometric parameter `1 / 2` is positive. -/
private theorem halfPos : 0 < (1 / 2 : ℝ) := by
  norm_num

/-- Helper for Exercise 11.2.3: the geometric parameter `1 / 2` is at most `1`. -/
private theorem halfLeOne : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

/-- Helper for Exercise 11.2.3: the `NNReal` parameter `1 / 2` is strictly less than `1`. -/
private theorem halfLtOne : (1 / 2 : NNReal) < 1 := by
  norm_num

/-- Helper for Exercise 11.2.3: the imported counterexample law is the geometric law with
parameter `1 / 2`, rewritten using the local positivity proofs. -/
private theorem counterexampleMeasure_eq_geometricMeasure :
    counterexampleMeasure = ProbabilityTheory.geometricMeasure halfPos halfLeOne := by
  -- The measure expression depends only on proof arguments, so proof irrelevance identifies them.
  change ProbabilityTheory.geometricMeasure _ _ = ProbabilityTheory.geometricMeasure _ _
  congr <;> exact Subsingleton.elim _ _

/-- Helper for Exercise 11.2.3: the lifted geometric law on `ULift ℕ`. -/
noncomputable def liftedGeometricMeasure : Measure Omega0 :=
  counterexampleMeasure.map ULift.up

/-- Helper for Exercise 11.2.3: the lifted geometric law is a probability measure. -/
instance liftedGeometricMeasure_isProbabilityMeasure : IsProbabilityMeasure liftedGeometricMeasure :=
  by
    change IsProbabilityMeasure (counterexampleMeasure.map ULift.up)
    infer_instance

/-- Helper for Exercise 11.2.3: the lifted filtration reveals the truncated waiting time
`ω ↦ min (ULift.down ω) n`. -/
noncomputable def liftedGeometricFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace Omega0) :=
  { seq := fun n ↦ MeasurableSpace.comap ULift.down (counterexampleFiltration n)
    mono' := by
      intro n m hnm s hs
      rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
      exact MeasurableSpace.measurableSet_comap.2 ⟨t, counterexampleFiltration.mono hnm t ht, rfl⟩
    le' := by
      intro n s hs
      rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
      exact measurable_down (counterexampleFiltration.le n t ht) }

/-- Helper for Exercise 11.2.3: the lifted geometric counterexample process. -/
def liftedGeometricProcess : ℕ → Omega0 → ℝ :=
  fun n ω ↦ counterexampleProcess n (ULift.down ω)

/-- Helper for Exercise 11.2.3: the geometric singleton masses equal `(1 / 2)^(n + 1)`. -/
private theorem counterexampleMeasure_apply_singleton (n : ℕ) :
    counterexampleMeasure ({n} : Set ℕ) = (1 / 2 : ENNReal) ^ (n + 1) := by
  have hhalf : (1 - (1 / 2 : NNReal)) = (1 / 2 : NNReal) := by
    apply NNReal.coe_injective
    norm_num [NNReal.coe_sub halfLtOne.le]
  have hhalfENN : ((1 / 2 : NNReal) : ENNReal) = (1 / 2 : ENNReal) := by
    norm_num
  -- Specialize the standard geometric-mass formula to the parameter `1 / 2`.
  calc
    counterexampleMeasure ({n} : Set ℕ) =
        ProbabilityTheory.geometricMeasure halfPos halfLeOne ({n} : Set ℕ) := by
          rw [counterexampleMeasure_eq_geometricMeasure]
    _ = ENNReal.ofReal (geometricMass (1 / 2 : NNReal) n) := by
          simpa using geometricMeasure_apply_singleton halfPos halfLtOne n
    _ = ENNReal.ofReal (((1 / 2 : NNReal) ^ n * (1 / 2 : NNReal) : NNReal)) := by
          rw [geometricMass, failurePrefixMass, hhalf]
    _ = ENNReal.ofReal (((1 / 2 : NNReal) ^ (n + 1) : NNReal)) := by
          rw [pow_succ]
    _ = (((1 / 2 : NNReal) ^ (n + 1) : NNReal) : ENNReal) := by
          simp
    _ = (((1 / 2 : NNReal) : ENNReal) ^ (n + 1)) := by
          rfl
    _ = (1 / 2 : ENNReal) ^ (n + 1) := by
          exact congrArg (fun z : ENNReal ↦ z ^ (n + 1)) hhalfENN

/-- Helper for Exercise 11.2.3: the real-valued singleton masses of the geometric law. -/
private theorem counterexampleMeasureReal_singleton (n : ℕ) :
    counterexampleMeasure.real ({n} : Set ℕ) = (1 / 2 : ℝ) ^ (n + 1) := by
  -- Convert the explicit `ENNReal` mass to the real-valued measure.
  rw [Measure.real_def, counterexampleMeasure_apply_singleton]
  norm_num

/-- Helper for Exercise 11.2.3: the geometric upper tail on `ℕ` has mass `(1 / 2)^n`. -/
private theorem counterexampleMeasure_Ici (n : ℕ) :
    counterexampleMeasure (Set.Ici n) = (1 / 2 : ENNReal) ^ n := by
  have hsum :
      counterexampleMeasure.real (Set.Iio n) =
        ∑ k ∈ Finset.range n, counterexampleMeasure.real ({k} : Set ℕ) := by
    symm
    simpa using
      (sum_measureReal_singleton (Finset.range n) :
        (∑ k ∈ Finset.range n, counterexampleMeasure.real ({k} : Set ℕ)) =
          counterexampleMeasure.real (Finset.range n))
  have hsum' :
      counterexampleMeasure.real (Set.Iio n) =
        ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) := by
    rw [hsum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    exact counterexampleMeasureReal_singleton k
  have hIio :
      counterexampleMeasure.real (Set.Iio n) = 1 - (1 / 2 : ℝ) ^ n := by
    have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    rw [hsum']
    calc
      ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) =
          (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            rw [pow_succ', mul_comm]
      _ = (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) * (1 - (1 / 2 : ℝ)) := by
            rw [hhalf]
      _ = 1 - (1 / 2 : ℝ) ^ n := by
            simpa using (geom_sum_mul_neg (1 / 2 : ℝ) n)
  have hreal :
      counterexampleMeasure.real (Set.Ici n) = (1 / 2 : ℝ) ^ n := by
    rw [show Set.Ici n = (Set.Iio n)ᶜ by
          ext ω
          simp,
      measureReal_compl measurableSet_Iio, probReal_univ, hIio]
    ring
  exact
    (ENNReal.toReal_eq_toReal_iff'
      (ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by simp))) (by simp)).mp <| by
        simpa [Measure.real_def] using hreal

/-- Helper for Exercise 11.2.3: the lifted upper tail `{ω | n ≤ ω.down}` has mass `(1 / 2)^n`.
-/
private theorem liftedGeometricMeasure_Ici (n : ℕ) :
    liftedGeometricMeasure {ω : Omega0 | n ≤ ULift.down ω} = (1 / 2 : ENNReal) ^ n := by
  -- Push the tail event back to `ℕ` along `ULift.up`.
  rw [show liftedGeometricMeasure =
      counterexampleMeasure.map ULift.up by rfl]
  rw [Measure.map_apply measurable_up]
  · simpa using counterexampleMeasure_Ici n
  · exact measurable_down measurableSet_Ici

/-- Helper for Exercise 11.2.3: the lifted strict tail `{ω | n < ω.down}` has mass
`(1 / 2)^(n + 1)`. -/
private theorem liftedGeometricMeasure_Ioi (n : ℕ) :
    liftedGeometricMeasure {ω : Omega0 | n < ULift.down ω} = (1 / 2 : ENNReal) ^ (n + 1) := by
  simpa [Set.Ioi, Nat.succ_eq_add_one] using liftedGeometricMeasure_Ici (n + 1)

/-- Helper for Exercise 11.2.3: the lifted singleton `{ULift.up n}` has mass `(1 / 2)^(n + 1)`.
-/
private theorem liftedGeometricMeasure_singleton (n : ℕ) :
    liftedGeometricMeasure ({ULift.up n} : Set Omega0) = (1 / 2 : ENNReal) ^ (n + 1) := by
  -- Push the singleton back to the corresponding atom of the base law.
  rw [show liftedGeometricMeasure =
      counterexampleMeasure.map ULift.up by rfl]
  rw [Measure.map_apply measurable_up]
  · have hpre :
        ULift.up ⁻¹' ({ULift.up n} : Set Omega0) = ({n} : Set ℕ) := by
          ext x
          simp
    rw [hpre]
    exact counterexampleMeasure_apply_singleton n
  · exact measurableSet_singleton (ULift.up n)

/-- Helper for Exercise 11.2.3: the lifted tail masses expressed as real-valued measures. -/
private theorem liftedGeometricMeasureReal_Ici (n : ℕ) :
    liftedGeometricMeasure.real {ω : Omega0 | n ≤ ULift.down ω} = (1 / 2 : ℝ) ^ n := by
  rw [Measure.real_def, liftedGeometricMeasure_Ici]
  norm_num

/-- Helper for Exercise 11.2.3: the lifted strict tail masses expressed as real-valued measures.
-/
private theorem liftedGeometricMeasureReal_Ioi (n : ℕ) :
    liftedGeometricMeasure.real {ω : Omega0 | n < ULift.down ω} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [Measure.real_def, liftedGeometricMeasure_Ioi]
  norm_num

/-- Helper for Exercise 11.2.3: the lifted singleton masses expressed as real-valued measures. -/
private theorem liftedGeometricMeasureReal_singleton (n : ℕ) :
    liftedGeometricMeasure.real ({ULift.up n} : Set Omega0) = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [Measure.real_def, liftedGeometricMeasure_singleton]
  norm_num

/-- Helper for Exercise 11.2.3: each lifted time slice is strongly measurable with respect to the
lifted filtration. -/
private theorem liftedGeometricProcess_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable[liftedGeometricFiltration n] (liftedGeometricProcess n) := by
  -- Pull the base strong measurability back along the defining comap map `ULift.down`.
  have hdown :
      @Measurable Omega0 ℕ (liftedGeometricFiltration n) (counterexampleFiltration n) ULift.down := by
    change @Measurable Omega0 ℕ
      (MeasurableSpace.comap ULift.down (counterexampleFiltration n))
      (counterexampleFiltration n) ULift.down
    exact comap_measurable ULift.down
  simpa [liftedGeometricProcess] using
    (counterexampleProcess_martingale.stronglyMeasurable n).comp_measurable hdown

/-- Helper for Exercise 11.2.3: the lifted process is strongly adapted to the lifted filtration.
-/
private theorem liftedGeometricProcess_stronglyAdapted :
    StronglyAdapted liftedGeometricFiltration liftedGeometricProcess := by
  intro n
  exact liftedGeometricProcess_stronglyMeasurable n

/-- Helper for Exercise 11.2.3: each lifted time slice is integrable. -/
private theorem liftedGeometricProcess_integrable (n : ℕ) :
    Integrable (liftedGeometricProcess n) liftedGeometricMeasure := by
  let A : Set Omega0 := {ω | ULift.down ω < n}
  have hEq :
      liftedGeometricProcess n =
        A.piecewise (fun _ : Omega0 ↦ (1 : ℝ)) (fun _ ↦ 1 - (2 : ℝ) ^ n) := by
    funext ω
    by_cases hω : ULift.down ω < n
    · simp [liftedGeometricProcess, counterexampleProcess, A, Set.piecewise, hω]
    · simp [liftedGeometricProcess, counterexampleProcess, A, Set.piecewise, hω]
  have hleft :
      IntegrableOn (fun _ : Omega0 ↦ (1 : ℝ)) A liftedGeometricMeasure :=
    integrableOn_const (measure_ne_top liftedGeometricMeasure A) (by simp)
  have hright :
      IntegrableOn (fun _ : Omega0 ↦ 1 - (2 : ℝ) ^ n) Aᶜ liftedGeometricMeasure :=
    integrableOn_const (measure_ne_top liftedGeometricMeasure Aᶜ) (by simp)
  rw [hEq]
  exact Integrable.piecewise (measurable_down measurableSet_Iio) hleft hright

/-- Helper for Exercise 11.2.3: the lifted geometric process is a martingale. -/
private theorem liftedGeometricProcess_martingale :
    Martingale liftedGeometricProcess liftedGeometricFiltration liftedGeometricMeasure := by
  -- Transport the deterministic-time set-integral martingale identity along the canonical
  -- measurable equivalence `ℕ ≃ ULift ℕ`.
  refine martingale_of_setIntegral_eq_succ liftedGeometricProcess_stronglyAdapted
    liftedGeometricProcess_integrable ?_
  intro n s hs
  rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
  -- Rewrite both lifted set integrals back on `ℕ`, apply the base martingale identity there, and
  -- then push the result forward again to `ULift`.
  calc
    ∫ ω in ULift.down ⁻¹' t, liftedGeometricProcess n ω ∂liftedGeometricMeasure =
        ∫ x in t, counterexampleProcess n x ∂counterexampleMeasure := by
          simpa [liftedGeometricMeasure, liftedGeometricProcess] using
            (setIntegral_map_equiv MeasurableEquiv.ulift.symm (liftedGeometricProcess n)
              (ULift.down ⁻¹' t))
    _ = ∫ x in t, counterexampleProcess (n + 1) x ∂counterexampleMeasure := by
          simpa using
            (counterexampleProcess_martingale.setIntegral_eq (show n ≤ n + 1 by omega) ht)
    _ = ∫ ω in ULift.down ⁻¹' t, liftedGeometricProcess (n + 1) ω ∂liftedGeometricMeasure := by
          simpa [liftedGeometricMeasure, liftedGeometricProcess] using
            (setIntegral_map_equiv MeasurableEquiv.ulift.symm (liftedGeometricProcess (n + 1))
              (ULift.down ⁻¹' t)).symm

/-- Helper for Exercise 11.2.3: every time slice of the lifted process is square-integrable. -/
private theorem liftedGeometricProcess_integrable_sq (n : ℕ) :
    Integrable (fun ω ↦ (liftedGeometricProcess n ω) ^ 2) liftedGeometricMeasure := by
  let A : Set Omega0 := {ω | ULift.down ω < n}
  have hEq :
      (fun ω ↦ (liftedGeometricProcess n ω) ^ 2) =
        A.piecewise (fun _ : Omega0 ↦ (1 : ℝ)) (fun _ ↦ (1 - (2 : ℝ) ^ n) ^ 2) := by
    funext ω
    by_cases hω : ULift.down ω < n
    · simp [liftedGeometricProcess, counterexampleProcess, A, Set.piecewise, hω]
    · simp [liftedGeometricProcess, counterexampleProcess, A, Set.piecewise, hω]
  have hleft :
      IntegrableOn (fun _ : Omega0 ↦ (1 : ℝ)) A liftedGeometricMeasure :=
    integrableOn_const (measure_ne_top liftedGeometricMeasure A) (by simp)
  have hright :
      IntegrableOn (fun _ : Omega0 ↦ (1 - (2 : ℝ) ^ n) ^ 2) Aᶜ liftedGeometricMeasure :=
    integrableOn_const (measure_ne_top liftedGeometricMeasure Aᶜ) (by simp)
  rw [hEq]
  exact Integrable.piecewise (measurable_down measurableSet_Iio) hleft hright

/-- Helper for Exercise 11.2.3: along every sample path the lifted process is eventually constant
equal to `1`. -/
private theorem liftedGeometricProcess_tendsto_one (ω : Omega0) :
    Tendsto (fun n ↦ liftedGeometricProcess n ω) atTop (𝓝 (1 : ℝ)) := by
  have hEventually :
      (fun n ↦ liftedGeometricProcess n ω) =ᶠ[atTop] fun _ : ℕ ↦ (1 : ℝ) := by
    refine Filter.eventually_atTop.2 ⟨ULift.down ω + 1, ?_⟩
    intro n hn
    have hlt : ULift.down ω < n := lt_of_lt_of_le (Nat.lt_succ_self _) hn
    simp [liftedGeometricProcess, counterexampleProcess, hlt]
  -- After time `ULift.down ω + 1`, the path has stabilized at the constant value `1`.
  exact Tendsto.congr' hEventually.symm (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) from
    tendsto_const_nhds)

/-- Helper for Exercise 11.2.3: the pathwise convergence to `1` holds almost surely. -/
private theorem liftedGeometricProcess_ae_tendsto_one :
    ∀ᵐ ω ∂liftedGeometricMeasure, Tendsto (fun n ↦ liftedGeometricProcess n ω) atTop (𝓝 (1 : ℝ)) :=
  Filter.Eventually.of_forall liftedGeometricProcess_tendsto_one

/-- Helper for Exercise 11.2.3: the absolute difference `|Xₙ - 1|` is the tail indicator
`2^n 𝟙_{ω.down ≥ n}`. -/
private theorem liftedGeometricProcess_norm_sub_one_eq_indicator (n : ℕ) :
    (fun ω ↦ ‖liftedGeometricProcess n ω - 1‖) =
      Set.indicator {ω : Omega0 | n ≤ ULift.down ω} (fun _ : Omega0 ↦ (2 : ℝ) ^ n) := by
  funext ω
  by_cases hω : ULift.down ω < n
  · have hnot : ¬ n ≤ ULift.down ω := Nat.not_le.mpr hω
    have hvalue : liftedGeometricProcess n ω - 1 = 0 := by
      simp [liftedGeometricProcess, counterexampleProcess, hω]
    rw [hvalue]
    simp [Set.indicator, Set.mem_setOf_eq, hnot]
  · have hle : n ≤ ULift.down ω := Nat.not_lt.mp hω
    have hvalue : liftedGeometricProcess n ω - 1 = -((2 : ℝ) ^ n) := by
      simp [liftedGeometricProcess, counterexampleProcess, hω]
    rw [hvalue]
    simp [Set.indicator, Set.mem_setOf_eq, hle]

/-- Helper for Exercise 11.2.3: the `L¹` norm of `Xₙ - 1` is exactly `1`. -/
private theorem liftedGeometricProcess_sub_one_eLpNorm_one (n : ℕ) :
    eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 1 liftedGeometricMeasure = 1 := by
  have hInt :
      Integrable (fun ω ↦ liftedGeometricProcess n ω - 1) liftedGeometricMeasure := by
    have hconst : Integrable (fun _ : Omega0 ↦ (1 : ℝ)) liftedGeometricMeasure := by
      simpa using (integrable_const (1 : ℝ))
    exact (liftedGeometricProcess_integrable n).sub hconst
  -- Rewrite the `L¹` seminorm as the integral of the absolute value and evaluate it on the tail.
  calc
    eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 1 liftedGeometricMeasure =
        ENNReal.ofReal (∫ ω, ‖liftedGeometricProcess n ω - 1‖ ∂liftedGeometricMeasure) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          exact (ofReal_integral_norm_eq_lintegral_enorm hInt).symm
    _ = ENNReal.ofReal
          (liftedGeometricMeasure.real {ω : Omega0 | n ≤ ULift.down ω} * (2 : ℝ) ^ n) := by
          refine congrArg ENNReal.ofReal ?_
          rw [liftedGeometricProcess_norm_sub_one_eq_indicator]
          have hSet : {ω : Omega0 | n ≤ ULift.down ω} = ULift.down ⁻¹' Set.Ici n := by
            ext ω
            simp [Set.mem_Ici]
          rw [hSet]
          rw [integral_indicator_const ((2 : ℝ) ^ n) (measurable_down measurableSet_Ici)
            (μ := liftedGeometricMeasure)]
          rw [smul_eq_mul]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
          rw [liftedGeometricMeasureReal_Ici]
    _ = 1 := by
          have hpow : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
            rw [← mul_pow]
            norm_num
          rw [hpow]
          norm_num

/-- Helper for Exercise 11.2.3: the lifted process is uniformly bounded in `L¹` by `2`. -/
private theorem liftedGeometricProcess_eLpNorm_one_le_two (n : ℕ) :
    eLpNorm (liftedGeometricProcess n) 1 liftedGeometricMeasure ≤ 2 := by
  have hMeasSub :
      AEStronglyMeasurable (fun ω ↦ liftedGeometricProcess n ω - 1) liftedGeometricMeasure := by
    fun_prop
  have hMeasConst :
      AEStronglyMeasurable (fun _ : Omega0 ↦ (1 : ℝ)) liftedGeometricMeasure := by
    fun_prop
  -- Bound `‖Xₙ‖₁` by the triangle inequality around the constant limit candidate `1`.
  calc
    eLpNorm (liftedGeometricProcess n) 1 liftedGeometricMeasure =
        eLpNorm ((fun ω ↦ liftedGeometricProcess n ω - 1) + fun _ : Omega0 ↦ (1 : ℝ))
          1 liftedGeometricMeasure := by
            refine eLpNorm_congr_ae (.of_forall fun ω ↦ ?_)
            change liftedGeometricProcess n ω = (liftedGeometricProcess n ω - 1) + 1
            ring
    _ ≤ eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 1 liftedGeometricMeasure +
          eLpNorm (fun _ : Omega0 ↦ (1 : ℝ)) 1 liftedGeometricMeasure := by
            exact eLpNorm_add_le hMeasSub hMeasConst le_rfl
    _ = 1 + 1 := by
          rw [liftedGeometricProcess_sub_one_eLpNorm_one]
          simp [eLpNorm_one_eq_lintegral_enorm]
    _ = 2 := by norm_num

/-- Helper for Exercise 11.2.3: squaring `Xₙ - 1` produces the tail indicator `4^n
𝟙_{ω.down ≥ n}`. -/
private theorem liftedGeometricProcess_sub_one_sq_eq_indicator (n : ℕ) :
    (fun ω ↦ (liftedGeometricProcess n ω - 1) ^ 2) =
      Set.indicator {ω : Omega0 | n ≤ ULift.down ω} (fun _ : Omega0 ↦ (4 : ℝ) ^ n) := by
  funext ω
  by_cases hω : ULift.down ω < n
  · have hnot : ¬ n ≤ ULift.down ω := Nat.not_le.mpr hω
    have hvalue : liftedGeometricProcess n ω - 1 = 0 := by
      simp [liftedGeometricProcess, counterexampleProcess, hω]
    rw [hvalue]
    simp [Set.indicator, Set.mem_setOf_eq, hnot]
  · have hle : n ≤ ULift.down ω := Nat.not_lt.mp hω
    have hvalue : liftedGeometricProcess n ω - 1 = -((2 : ℝ) ^ n) := by
      simp [liftedGeometricProcess, counterexampleProcess, hω]
    rw [hvalue]
    have hsquare : (-((2 : ℝ) ^ n)) ^ 2 = (4 : ℝ) ^ n := by
      calc
        (-((2 : ℝ) ^ n)) ^ 2 = (((2 : ℝ) ^ n) ^ 2) := by ring
        _ = (4 : ℝ) ^ n := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
    simpa [Set.indicator, Set.mem_setOf_eq, hle] using hsquare

/-- Helper for Exercise 11.2.3: the squared `L²` distance from `Xₙ` to `1` is exactly `2^n`. -/
private theorem liftedGeometricProcess_sub_one_secondMoment (n : ℕ) :
    liftedGeometricMeasure[fun ω ↦ (liftedGeometricProcess n ω - 1) ^ 2] = (2 : ℝ) ^ n := by
  -- Evaluate the squared tail indicator on the tail event.
  calc
    liftedGeometricMeasure[fun ω ↦ (liftedGeometricProcess n ω - 1) ^ 2] =
        liftedGeometricMeasure.real {ω : Omega0 | n ≤ ULift.down ω} * (4 : ℝ) ^ n := by
          rw [liftedGeometricProcess_sub_one_sq_eq_indicator]
          have hSet : {ω : Omega0 | n ≤ ULift.down ω} = ULift.down ⁻¹' Set.Ici n := by
            ext ω
            simp [Set.mem_Ici]
          rw [hSet]
          rw [integral_indicator_const ((4 : ℝ) ^ n) (measurable_down measurableSet_Ici)
            (μ := liftedGeometricMeasure)]
          rw [smul_eq_mul]
    _ = (1 / 2 : ℝ) ^ n * (4 : ℝ) ^ n := by
          rw [liftedGeometricMeasureReal_Ici]
    _ = (2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num

/-- Helper for Exercise 11.2.3: the `L²` distance from `Xₙ` to `1` is bounded below by `1`. -/
private theorem liftedGeometricProcess_sub_one_eLpNorm_two_ge_one (n : ℕ) :
    (1 : ℝ≥0∞) ≤ eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure := by
  have hInt :
      Integrable (fun ω ↦ (liftedGeometricProcess n ω - 1) ^ 2) liftedGeometricMeasure := by
    rw [liftedGeometricProcess_sub_one_sq_eq_indicator]
    exact
      ((integrable_const ((4 : ℝ) ^ n)).indicator (measurable_down measurableSet_Ici)).congr <|
        Filter.Eventually.of_forall fun _ ↦ rfl
  have hMem :
      MemLp (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure := by
    exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hInt
  have hNorm :
      eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure =
        ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ n)) := by
    calc
      eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure =
          ENNReal.ofReal
            (ENNReal.toReal
              (eLpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure)) := by
            exact (ENNReal.ofReal_toReal hMem.eLpNorm_ne_top).symm
      _ = ENNReal.ofReal
            (lpNorm (fun ω ↦ liftedGeometricProcess n ω - 1) 2 liftedGeometricMeasure) := by
            rw [toReal_eLpNorm hMem.aestronglyMeasurable]
      _ = ENNReal.ofReal
            (Real.sqrt
              (liftedGeometricMeasure[fun ω ↦ (liftedGeometricProcess n ω - 1) ^ 2])) := by
            rw [lpNorm_two_eq_sqrt_integral_sq hMem]
      _ = ENNReal.ofReal (Real.sqrt ((2 : ℝ) ^ n)) := by
            rw [liftedGeometricProcess_sub_one_secondMoment]
  rw [hNorm]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num]
  exact ENNReal.ofReal_le_ofReal <| by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hsqrt : 1 ≤ Real.sqrt ((2 : ℝ) ^ n) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hpow
    simpa using hsqrt

end Counterexample

/-- Exercise 11.2.3: there exists a square-integrable martingale that converges almost surely to
its canonical limit process but does not converge to that limit in `L²`. -/
theorem exists_square_integrable_martingale_ae_tendsto_limitProcess_not_tendstoInLp_two :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∀ n, MemLp (X n) 2 μ) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ TendstoInLp 2 μ X (ℱ.limitProcess X μ) := by
  let μ := liftedGeometricMeasure
  let ℱ := liftedGeometricFiltration
  let X := liftedGeometricProcess
  have hX : Martingale X ℱ μ := liftedGeometricProcess_martingale
  have hX_memLp_two_base : ∀ n, MemLp (liftedGeometricProcess n) 2 liftedGeometricMeasure := by
    intro n
    -- Each time slice is square-integrable because its square has finite integral.
    exact
      (memLp_two_iff_integrable_sq (μ := liftedGeometricMeasure)
        ((liftedGeometricProcess_integrable n).aestronglyMeasurable)).2
        (liftedGeometricProcess_integrable_sq n)
  have hX_memLp_two : ∀ n, MemLp (X n) 2 μ := by
    simpa [X, μ] using hX_memLp_two_base
  have h_ae_tendsto_limit :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) := by
    -- The owner convergence theorem applies because the process is uniformly bounded in `L¹`.
    exact hX.submartingale.ae_tendsto_limitProcess liftedGeometricProcess_eLpNorm_one_le_two
  have h_limit_one : ℱ.limitProcess X μ =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
    -- Route correction: instead of extracting nonconvergence from Corollary 11.11, identify the
    -- canonical limit with the explicit pathwise limit `1` and use the direct `L²` lower bound.
    filter_upwards [liftedGeometricProcess_ae_tendsto_one, h_ae_tendsto_limit] with ω hω_one
        hω_limit
    exact tendsto_nhds_unique hω_limit hω_one
  have h_not_tendsto :
      ¬ Tendsto (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) 2 μ) atTop (𝓝 0) := by
    have h_dist_eq (n : ℕ) :
        eLpNorm (X n - ℱ.limitProcess X μ) 2 μ =
          eLpNorm (fun ω ↦ X n ω - 1) 2 μ := by
      -- Replace the canonical limit process by its almost-sure representative `1`.
      refine eLpNorm_congr_ae ?_
      exact EventuallyEq.sub EventuallyEq.rfl h_limit_one
    have h_dist_ge_one :
        ∀ n, (1 : ℝ≥0∞) ≤ eLpNorm (X n - ℱ.limitProcess X μ) 2 μ := by
      intro n
      calc
        (1 : ℝ≥0∞) ≤ eLpNorm (fun ω ↦ X n ω - 1) 2 μ :=
          liftedGeometricProcess_sub_one_eLpNorm_two_ge_one n
        _ = eLpNorm (X n - ℱ.limitProcess X μ) 2 μ := (h_dist_eq n).symm
    intro h_tendsto
    have h_eventually_lt_one :
        ∀ᶠ n in atTop, eLpNorm (X n - ℱ.limitProcess X μ) 2 μ < 1 := by
      exact h_tendsto (Iio_mem_nhds (by simp : (0 : ℝ≥0∞) < 1))
    have h_eventually_ge_one :
        ∀ᶠ n in atTop, (1 : ℝ≥0∞) ≤ eLpNorm (X n - ℱ.limitProcess X μ) 2 μ :=
      Filter.Eventually.of_forall h_dist_ge_one
    have hFalse : ∀ᶠ n : ℕ in atTop, False := by
      filter_upwards [h_eventually_lt_one, h_eventually_ge_one] with n hn_lt hn_ge
      exact (not_lt_of_ge hn_ge) hn_lt
    rcases (show ∃ a : ℕ, ∀ b : ℕ, b < a from by simpa using hFalse) with ⟨a, ha⟩
    exact (Nat.lt_irrefl a) (ha a)
  have h_not_tendstoInLp : ¬ TendstoInLp 2 μ X (ℱ.limitProcess X μ) := by
    intro h_tendsto
    exact h_not_tendsto h_tendsto.tendsto_eLpNorm
  exact ⟨Omega0, inferInstance, μ, inferInstance, ℱ, X, hX, hX_memLp_two, h_ae_tendsto_limit,
    h_not_tendstoInLp⟩

end MeasureTheory
