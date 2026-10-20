module

public import ReasLib.Optimization.DFP.Polar.SlowCoupling
public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import ReasLib.Optimization.DFP.Polar.StageFeasibility

/-!
# Continuation of the actual polar recurrence

The accepted fast and slow estimates are integrated for the prescribed
`Parameters.normalizedEvenState` sequence, with widths and a natural starting
index threshold chosen independently of every subsequent larger start index.
-/

public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace DFP.Polar.Continuation

/-- Helper for lem:polar-continuation: every normalized state reconstructs
from its own first coordinate and its exact fast error relative to the source
even cycle curve. -/
theorem perturbedState_fastError (x : ℝ × ℝ × ℝ) :
    FastRemainder.perturbedState x.1 (FastContraction.fastError x) = x := by
  rw [FastRemainder.perturbedState_apply, FastContraction.fastError_def]
  simp only [FastContraction.fastCoordinates_apply,
    Pi.sub_apply, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · dsimp only
      ring
    · dsimp only
      ring

/-- Helper for lem:polar-continuation: the prescribed normalized recurrence
with explicit original starting index and cycle parameter. -/
theorem normalizedEvenState_of_succ (j₀ : ℕ) (νStar : ℝ) (j : ℕ) (hstart : 0 < j₀) :
    (Parameters.of j₀ νStar).normalizedEvenState (j + 1) =
      Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar)
        ((Parameters.of j₀ νStar).scale j)
        ((Parameters.of j₀ νStar).normalizedEvenState j) := by
  have hpositive : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hstart
  simpa only [Parameters.feedbackRate_def, Parameters.kStar_def,
    Parameters.of_cycleParameter] using
    Parameters.normalizedEvenState_succ (Parameters.of j₀ νStar) j hpositive

/-- Helper for lem:polar-continuation: a scale cutoff yields a single natural
starting-index cutoff for every larger starting index and every cycle parameter,
using the original prescribed power scale. -/
theorem existsStartThreshold (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∀ νStar : ℝ, ∀ j₀ ≥ J,
      (Parameters.of j₀ νStar).scale 0 < ε := by
  have heventually := (ScaleTails.scale_tendsto_zero (Parameters.of 0 baseAngle)).eventually
    (Iio_mem_nhds hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp heventually
  refine ⟨max J 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), ?_⟩
  intro νStar j₀ hj₀
  have hbound := hJ j₀ ((le_max_left J 1).trans hj₀)
  simpa only [Parameters.scale_def, Parameters.of_startIndex, Nat.zero_add,
    Nat.add_zero] using hbound

/-- Helper for lem:polar-continuation: the actual accepted slow and fast
estimates hold on one closed slow interval and one strictly interior fast
tolerance, with a finite two-sided drift derivative bound. -/
theorem existsActualEstimateNeighborhood :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧
      ∃ rate > (1 / 3 : ℝ), ∃ r > 0, ∃ ρ > 0,
      ∃ Cfast > 0, ∃ Ccross > 0, ∃ Cslow > 0, ∃ D > 0, ∃ δ > 0,
        TwoCycle.restoringDrift νStar (cycleK νStar) = 0 ∧
        (∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
          ContDiffAt ℝ ω TwoCycle.inverseParameter A ∧
            A ∈ TwoCycle.normalizationSet ∧ 0 < A ∧
            -D ≤ deriv (TwoCycle.restoringDrift νStar) A ∧
              deriv (TwoCycle.restoringDrift νStar) A ≤ -rate) ∧
        ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
          ∀ u : Fin 2 → ℝ, FastContraction.fixedNorm u ≤ ρ →
            ∀ t : ℝ, 0 ≤ t → t < δ →
              FastContraction.fixedNorm (FastContraction.fastError
                (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
                  (FastRemainder.perturbedState A u))) ≤
                    (3 / 4 : ℝ) * FastContraction.fixedNorm u + Cfast * t ^ 3 ∧
              |(Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
                (FastRemainder.perturbedState A u)).1 -
                  (A + t ^ 3 * TwoCycle.restoringDrift νStar A)| ≤
                    Ccross * t ^ 3 * FastContraction.fixedNorm u + Cslow * t ^ 4 := by
  obtain ⟨rSlow, hrSlow, rate, hrate, ηSlow, hηSlow, hslow⟩ := SlowCoupling.polarSlowBound
  obtain ⟨rFast, hrFast, hfast⟩ := FastRemainder.polarFastBound
  obtain ⟨ηFast, hηFast, hfastNear⟩ := Metric.eventually_nhds_iff.mp hfast
  refine ⟨min ηSlow ηFast, lt_min hηSlow hηFast, ?_⟩
  intro νStar hνStar
  have hνSlow : νStar ∈ Set.Ioo baseAngle (baseAngle + ηSlow) := by
    refine ⟨hνStar.1, ?_⟩
    exact hνStar.2.trans_le (add_le_add le_rfl (min_le_left ηSlow ηFast))
  have hνFast : dist νStar baseAngle < ηFast := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hνStar.1)]
    linarith [hνStar.2, min_le_right ηSlow ηFast]
  obtain ⟨hparameter, s, hs, Ccross, hCcross, Cslow, hCslow, δSlow, hδSlow,
    heq, hslowBranch⟩ := hslow νStar hνSlow
  obtain ⟨_, Cfast, hCfast, δFast, hδFast, U, hU, hfastBranch⟩ := hfastNear hνFast
  obtain ⟨rU, hrU, hUball⟩ := Metric.mem_nhds_iff.mp hU
  let r := min s (rU / 2)
  let ρ := min rSlow rFast / 2
  have hr : 0 < r := lt_min hs (half_pos hrU)
  have hρ : 0 < ρ := half_pos (lt_min hrSlow hrFast)
  have hρSlow : ρ < rSlow :=
    (half_lt_self (lt_min hrSlow hrFast)).trans_le (min_le_left _ _)
  have hρFast : ρ < rFast :=
    (half_lt_self (lt_min hrSlow hrFast)).trans_le (min_le_right _ _)
  have hslowInterval : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
      A ∈ Set.Icc (cycleK νStar - s) (cycleK νStar + s) := by
    intro A hA
    have hrs : r ≤ s := min_le_left _ _
    constructor
    · linarith [hA.1]
    · linarith [hA.2]
  have hfastNeighborhood : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r), A ∈ U := by
    intro A hA
    apply hUball
    rw [Metric.mem_ball, Real.dist_eq]
    have hAr : |A - cycleK νStar| ≤ r := by
      apply abs_le.mpr
      constructor
      · linarith [hA.1]
      · linarith [hA.2]
    exact hAr.trans_lt ((min_le_right s (rU / 2)).trans_lt (half_lt_self hrU))
  have hregular : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
      A ≠ 0 ∧ ContDiffAt ℝ ω TwoCycle.inverseParameter A := by
    intro A hA
    have hproperties := hslowBranch A (hslowInterval A hA)
    exact ⟨hproperties.2.2.1.ne', hproperties.1⟩
  obtain ⟨D, hD, hlower⟩ := TubeBounds.restoringDrift_compact_deriv_lower νStar
    (Set.Icc (cycleK νStar - r) (cycleK νStar + r)) isCompact_Icc hregular
  refine ⟨hparameter, rate, hrate, r, hr, ρ, hρ, Cfast, hCfast,
    Ccross, hCcross, Cslow, hCslow, D, hD, min δSlow δFast,
    lt_min hδSlow hδFast, heq, ?_, ?_⟩
  · intro A hA
    have hproperties := hslowBranch A (hslowInterval A hA)
    exact ⟨hproperties.1, hproperties.2.1, hproperties.2.2.1,
      hlower A hA, hproperties.2.2.2.1⟩
  · intro A hA u hu t ht htδ
    have hfastEstimate := (hfastBranch A (hfastNeighborhood A hA)).2 u
      (hu.trans_lt hρFast) t ht (htδ.trans_le (min_le_right _ _))
    have hslowEstimate := (hslowBranch A (hslowInterval A hA)).2.2.2.2 u
      (hu.trans_lt hρSlow) t ht (htδ.trans_le (min_le_left _ _))
    exact ⟨hfastEstimate, hslowEstimate⟩

/-- Helper for lem:polar-continuation: the actual prescribed normalized
trajectory obeys the source slow and fast tube estimates uniformly for every
subsequently larger starting index. Every update premise is discharged by the
actual map estimates and exact recurrence. -/
theorem actualTube :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧
      ContDiffAt ℝ ω TwoCycle.inverseParameter (cycleK νStar) ∧
      ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, ∀ j : ℕ,
          |((Parameters.of j₀ νStar).normalizedEvenState j).1 -
            (Parameters.of j₀ νStar).kStar| ≤ M * (Parameters.of j₀ νStar).scale j ∧
          FastContraction.fixedNorm (FastContraction.fastError
            ((Parameters.of j₀ νStar).normalizedEvenState j)) ≤
              N * (Parameters.of j₀ νStar).scale j ^ 3 ∧
          ((Parameters.of j₀ νStar).normalizedEvenState j).1 ∈ TwoCycle.normalizationSet ∧
            0 < ((Parameters.of j₀ νStar).normalizedEvenState j).1 := by
  obtain ⟨η, hη, hestimates⟩ := existsActualEstimateNeighborhood
  refine ⟨η, hη, ?_⟩
  intro νStar hνStar
  obtain ⟨hparameter, rate, hrate, r, hr, ρ, hρ, Cfast, hCfast, Ccross, hCcross,
    Cslow, hCslow, D, hD, δ, hδ, heq, hbranch, hstep⟩ := hestimates νStar hνStar
  have hγnonnegative : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hγ : (3 / 4 : ℝ) < 1 := by norm_num
  have hdiff : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
      DifferentiableAt ℝ (TwoCycle.restoringDrift νStar) A := by
    intro A hA
    have hregular := hbranch A hA
    exact (TwoCycle.restoringDrift_analyticAt νStar A
      hregular.2.2.1.ne' hregular.1).differentiableAt
  have hderiv : ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
      -D ≤ deriv (TwoCycle.restoringDrift νStar) A ∧
        deriv (TwoCycle.restoringDrift νStar) A ≤ -rate := by
    intro A hA
    exact ⟨(hbranch A hA).2.2.2.1, (hbranch A hA).2.2.2.2⟩
  obtain ⟨N, hN, hNmargin, M, hM, hMmargin, εTube, hεTube, _, hTube⟩ :=
    TubeBounds.existsFixedNormTube_of_estimates (TwoCycle.restoringDrift νStar)
      (cycleK νStar) (3 / 4) Cfast Ccross Cslow rate D r ρ hγnonnegative hγ
      hCfast.le hCcross.le hCslow.le hrate hr hρ heq hdiff hderiv
  have hfastMargin : 0 < N - (3 / 4 : ℝ) * N - Cfast := by linarith
  have hslowMargin : 0 < (rate - 1 / 3) * M - Cslow := sub_pos.mpr hMmargin
  obtain ⟨εGeometry, hεGeometry, _, hgeometry⟩ :=
    TubeBounds.existsScaleThreshold N M Cfast Ccross D r ρ
      (N - (3 / 4 : ℝ) * N - Cfast) ((rate - 1 / 3) * M - Cslow)
      hr hρ hfastMargin hslowMargin
  let ε := min εTube (min εGeometry (δ / 2))
  have hε : 0 < ε := lt_min hεTube (lt_min hεGeometry (half_pos hδ))
  obtain ⟨J, hJ, hstartBound⟩ := existsStartThreshold ε hε
  have hcenter : cycleK νStar ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r) := by
    constructor
    · linarith
    · linarith
  refine ⟨hparameter, (hbranch _ hcenter).1, N, hN, M, hM, J, hJ, ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  let u : ℕ → Fin 2 → ℝ := fun j ↦ FastContraction.fastError (p.normalizedEvenState j)
  let b : ℕ → ℝ := fun j ↦ (p.normalizedEvenState j).1 - cycleK νStar
  have hstart : 0 < j₀ := hJ.trans_le hj₀
  have hpstart : 0 < p.startIndex := by simpa only [p, Parameters.of_startIndex] using hstart
  have hsmall : p.scale 0 < ε := hstartBound νStar j₀ hj₀
  have hscales : ∀ j, p.scale j ≤ ε := by
    intro j
    exact ((ScaleTails.scale_antitone p hpstart) (Nat.zero_le j)).trans hsmall.le
  have hsmallTube : p.scale 0 ≤ εTube := hsmall.le.trans (min_le_left _ _)
  have hpν : p.cycleParameter ∈ TwoCycle.parameterSet := by
    simpa only [p, Parameters.of_cycleParameter] using hparameter
  have hpk : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def]
    simp only [p, Parameters.of_cycleParameter]
  have hinitial := StageFeasibility.initial_errors_zero p hpstart hpν
  have huzero : u 0 = 0 := hinitial.2
  have hbzero : b 0 = 0 := by simpa only [b, hpk] using hinitial.1
  have hupdates : ∀ j, 0 < p.scale j → p.scale j ≤ εTube →
      FastContraction.fixedNorm (u j) ≤ N * p.scale j ^ 3 → |b j| ≤ M * p.scale j →
      FastContraction.fixedNorm (u (j + 1)) ≤
        (3 / 4 : ℝ) * FastContraction.fixedNorm (u j) + Cfast * p.scale j ^ 3 +
          Cfast * FastContraction.fixedNorm (u j) ^ 2 ∧
      |b (j + 1) - TubeBounds.scalarStep (TwoCycle.restoringDrift νStar)
        (cycleK νStar) (p.scale j) (b j)| ≤
          Ccross * p.scale j ^ 3 * FastContraction.fixedNorm (u j) +
            Cslow * p.scale j ^ 4 := by
    intro j ht _ hqin hbin
    have htGeometry : p.scale j ≤ εGeometry :=
      ((hscales j).trans (min_le_right _ _)).trans (min_le_left _ _)
    have htδ : p.scale j < δ :=
      (((hscales j).trans (min_le_right _ _)).trans
        (min_le_right εGeometry (δ / 2))).trans_lt (half_lt_self hδ)
    have hregion := hgeometry (p.scale j) ht htGeometry
    have hslowRadius : |(p.normalizedEvenState j).1 - cycleK νStar| ≤ r :=
      hbin.trans hregion.1
    have hA : (p.normalizedEvenState j).1 ∈
        Set.Icc (cycleK νStar - r) (cycleK νStar + r) := by
      have habs := abs_le.mp hslowRadius
      constructor
      · linarith [habs.1]
      · linarith [habs.2]
    have hfastRadius : FastContraction.fixedNorm (u j) ≤ ρ := hqin.trans hregion.2.1
    have hactual := hstep (p.normalizedEvenState j).1 hA (u j) hfastRadius
      (p.scale j) ht.le htδ
    dsimp only [u] at hactual
    rw [perturbedState_fastError] at hactual
    have hrec : p.normalizedEvenState (j + 1) =
        Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar)
          (p.scale j) (p.normalizedEvenState j) :=
      normalizedEvenState_of_succ j₀ νStar j hstart
    rw [← hrec] at hactual
    constructor
    · have hquadratic : 0 ≤ Cfast * FastContraction.fixedNorm (u j) ^ 2 :=
        mul_nonneg hCfast.le (sq_nonneg _)
      exact hactual.1.trans (le_add_of_nonneg_right hquadratic)
    · have hslow := hactual.2
      rw [← SlowCoupling.slowStepError_eq (TwoCycle.restoringDrift νStar) (cycleK νStar)
        (p.normalizedEvenState j).1 (p.normalizedEvenState (j + 1)).1 (p.scale j)] at hslow
      exact hslow
  have hall := hTube p hpstart hsmallTube u b huzero hbzero hupdates
  intro j
  obtain ⟨_, _, hfastBound, hslowBound, _, hslowRadius⟩ := hall j
  have hA : (p.normalizedEvenState j).1 ∈
      Set.Icc (cycleK νStar - r) (cycleK νStar + r) := by
    have habs := abs_le.mp hslowRadius
    dsimp only [b] at habs
    constructor
    · linarith [habs.1]
    · linarith [habs.2]
  refine ⟨?_, hfastBound, (hbranch _ hA).2.1, (hbranch _ hA).2.2.1⟩
  simpa only [b, p, Parameters.kStar_def, Parameters.of_cycleParameter] using hslowBound

/-- Helper for lem:polar-continuation: the source perturbed state is
continuous at every regular point of its original even cycle curve. -/
theorem continuousAt_perturbedState (A : ℝ) (hA : A ∈ TwoCycle.normalizationSet)
    (hν : ContDiffAt ℝ ω TwoCycle.inverseParameter A) :
    ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ FastRemainder.perturbedState z.1 z.2)
      (A, 0) := by
  have hcurve : ContinuousAt
      (fun z : ℝ × (Fin 2 → ℝ) ↦ TwoCycle.evenState z.1) (A, 0) :=
    (TwoCycle.evenState_analyticAt A hA hν).continuousAt.comp_of_eq continuousAt_fst rfl
  have hC := hcurve.snd.fst
  have hV := hcurve.snd.snd
  have hu0 : ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ z.2 0) (A, 0) :=
    (continuous_apply 0).continuousAt.comp continuousAt_snd
  have hu1 : ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ z.2 1) (A, 0) :=
    (continuous_apply 1).continuousAt.comp continuousAt_snd
  simp only [FastRemainder.perturbedState_apply, FastContraction.fastCoordinates_apply,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop

/-- Helper for lem:polar-continuation: the actual uniform tube enters every
fixed neighborhood of the selected even cycle state after one common natural
starting-index threshold, valid for every later starting index and cycle. -/
theorem statesNearCycle_of_uniformTube (νStar : ℝ)
    (hparameter : νStar ∈ TwoCycle.parameterSet)
    (hν : ContDiffAt ℝ ω TwoCycle.inverseParameter (cycleK νStar))
    (N M : ℝ) (hN : 0 < N) (hM : 0 < M) (J : ℕ) (hJ : 0 < J)
    (htube : ∀ j₀ ≥ J, ∀ j : ℕ,
      |((Parameters.of j₀ νStar).normalizedEvenState j).1 -
        (Parameters.of j₀ νStar).kStar| ≤ M * (Parameters.of j₀ νStar).scale j ∧
      FastContraction.fixedNorm (FastContraction.fastError
        ((Parameters.of j₀ νStar).normalizedEvenState j)) ≤
          N * (Parameters.of j₀ νStar).scale j ^ 3)
    (R : ℝ) (hR : 0 < R) :
    ∃ J' : ℕ, J ≤ J' ∧ ∀ j₀ ≥ J', ∀ j : ℕ,
      (Parameters.of j₀ νStar).normalizedEvenState j ∈
        Metric.closedBall (TwoCycle.evenState (cycleK νStar)) R := by
  have hK : cycleK νStar ∈ TwoCycle.normalizationSet :=
    TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  have hcurve := continuousAt_perturbedState (cycleK νStar) hK hν
  have hball : Metric.ball (TwoCycle.evenState (cycleK νStar)) R ∈
      𝓝 (FastRemainder.perturbedState (cycleK νStar) 0) := by
    rw [FastRemainder.perturbedState_zero]
    exact Metric.ball_mem_nhds _ hR
  obtain ⟨a, ha, hnear⟩ := Metric.eventually_nhds_iff.mp (hcurve.eventually hball)
  let B := ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hbase := ScaleTails.scale_tendsto_zero (Parameters.of 0 baseAngle)
  have hslowLimit : Tendsto
      (fun n : ℕ ↦ M * (Parameters.of 0 baseAngle).scale n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul M
  have hfastLimit : Tendsto
      (fun n : ℕ ↦ B * N * (Parameters.of 0 baseAngle).scale n ^ 3) atTop (𝓝 0) := by
    simpa using (hbase.pow 3).const_mul (B * N)
  have heventually : ∀ᶠ n : ℕ in atTop,
      M * (Parameters.of 0 baseAngle).scale n < a ∧
        B * N * (Parameters.of 0 baseAngle).scale n ^ 3 < a := by
    filter_upwards [hslowLimit.eventually (Iio_mem_nhds ha),
      hfastLimit.eventually (Iio_mem_nhds ha)] with n hslow hfast
    exact ⟨hslow, hfast⟩
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp heventually
  refine ⟨max J J₀, le_max_left _ _, ?_⟩
  intro j₀ hj₀ j
  have hjTube : J ≤ j₀ := (le_max_left J J₀).trans hj₀
  have hjTail : J₀ ≤ j₀ := (le_max_right J J₀).trans hj₀
  have hstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ.trans_le hjTube
  have hscale : (Parameters.of j₀ νStar).scale j ≤ (Parameters.of 0 baseAngle).scale j₀ := by
    have hmonotone := (ScaleTails.scale_antitone (Parameters.of j₀ νStar) hstart) (Nat.zero_le j)
    simpa only [Parameters.scale_def, Parameters.of_startIndex,
      Nat.zero_add, Nat.add_zero] using hmonotone
  have htail := hJ₀ j₀ hjTail
  have hbounds := htube j₀ hjTube j
  let x := (Parameters.of j₀ νStar).normalizedEvenState j
  let u := FastContraction.fastError x
  have hslow : |x.1 - cycleK νStar| < a := by
    have hbound : |x.1 - cycleK νStar| ≤ M * (Parameters.of j₀ νStar).scale j := by
      simpa only [x, Parameters.kStar_def, Parameters.of_cycleParameter] using hbounds.1
    exact (hbound.trans (mul_le_mul_of_nonneg_left hscale hM.le)).trans_lt htail.1
  have hfast : ‖u‖ < a := by
    have hnorm : ‖u‖ ≤ B * FastContraction.fixedNorm u := by
      have hraw := FastContraction.norm_le_basisOperator_mul_fixedNorm u
      have hnonnegative := FastContraction.fixedNorm_nonneg u
      dsimp only [B]
      nlinarith
    have hpowers : (Parameters.of j₀ νStar).scale j ^ 3 ≤
        (Parameters.of 0 baseAngle).scale j₀ ^ 3 :=
      pow_le_pow_left₀ (ScaleTails.scale_nonneg _ _) hscale 3
    calc
      ‖u‖ ≤ B * FastContraction.fixedNorm u := hnorm
      _ ≤ B * (N * (Parameters.of j₀ νStar).scale j ^ 3) :=
        mul_le_mul_of_nonneg_left hbounds.2 hB.le
      _ ≤ B * (N * (Parameters.of 0 baseAngle).scale j₀ ^ 3) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowers hN.le) hB.le
      _ = B * N * (Parameters.of 0 baseAngle).scale j₀ ^ 3 := by ring
      _ < a := htail.2
  have hinput : dist (x.1, u) (cycleK νStar, (0 : Fin 2 → ℝ)) < a := by
    rw [Prod.dist_eq, Real.dist_eq, dist_zero_right]
    exact max_lt hslow hfast
  have hstate := hnear hinput
  rw [perturbedState_fastError] at hstate
  exact Metric.mem_closedBall.mpr hstate.le

/-- Helper for lem:polar-continuation: one fixed neighborhood and scale
cutoff give feasibility of the actual prescribed even and odd stages, with
uniform lower bounds for their original secant and radius factors. -/
theorem existsPrescribedCycleFeasibility (νStar : ℝ)
    (hparameter : νStar ∈ TwoCycle.parameterSet) :
    ∃ R > 0, ∃ δ > 0, ∀ j₀ : ℕ, 0 < j₀ → ∀ j : ℕ,
      (Parameters.of j₀ νStar).scale j ≤ δ →
      (Parameters.of j₀ νStar).normalizedEvenState j ∈
        Metric.closedBall (TwoCycle.evenState (cycleK νStar)) R →
        ((Parameters.of j₀ νStar).evenMatrix j).PosDef ∧
          0 < (Parameters.of j₀ νStar).evenMatrix j 0 1 ∧
        ((Parameters.of j₀ νStar).oddMatrix j).PosDef ∧
          0 < (Parameters.of j₀ νStar).oddMatrix j 0 1 ∧
        (1 / 2 : ℝ) ≤ (Parameters.of j₀ νStar).sigma (2 * j) ∧
        (1 / 2 : ℝ) ≤ (Parameters.of j₀ νStar).sigma (2 * j + 1) ∧
        (1 / 2 : ℝ) ≤ (Parameters.of j₀ νStar).radiusRatio (2 * j) ∧
        (1 / 2 : ℝ) ≤ (Parameters.of j₀ νStar).radiusRatio (2 * j + 1) := by
  have hK : cycleK νStar ∈ TwoCycle.normalizationSet :=
    TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  obtain ⟨R, hR, δ, hδ, _, _, hfeasible⟩ :=
    StageFeasibility.exists_uniform_rawCycleFeasibility
      (4 * baseAngle / (9 * νStar)) (cycleK νStar) (cycleK νStar) hK
  refine ⟨R, hR, δ, hδ, ?_⟩
  intro j₀ hstart j htδ hx
  let p := Parameters.of j₀ νStar
  have hpstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hstart
  have ht := ScaleTails.scale_pos p hpstart j
  have hZ := Parameters.evenMatrix_isHermitian p j
  have hL : p.feedbackRate = 4 * baseAngle / (9 * νStar) := by
    rw [Parameters.feedbackRate_def]
    simp only [p, Parameters.of_cycleParameter]
  have hKp : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def]
    simp only [p, Parameters.of_cycleParameter]
  have hcoordinates : Normalized.coordinates (p.scale j) (p.evenMatrix j) ∈
      Metric.closedBall (TwoCycle.evenState (cycleK νStar)) R := by
    rw [← StageFeasibility.normalizedEvenState_eq_coordinates]
    exact hx
  have hraw := hfeasible (p.scale j) ⟨ht, htδ⟩ (p.evenMatrix j) hZ hcoordinates
  rw [← hL, ← hKp] at hraw
  obtain ⟨hPE, hCE, hPO, hCO, _, _, hσE, hσO, hWE, hWO, _⟩ := hraw
  rw [StageFeasibility.rawFirstStage_prescribed p j (p.evenMatrix j) hpstart,
    ← Parameters.oddMatrix_def p j] at hPO hCO
  rw [← StageFeasibility.cycleSecant_zero_eq_sigmaOf p.feedbackRate p.kStar
    (p.scale j) (p.evenMatrix j) ht,
    ← StageFeasibility.normalizedEvenState_eq_coordinates p j,
    StageFeasibility.cycleSecant_even_prescribed p j hpstart] at hσE
  rw [← StageFeasibility.cycleSecant_one_eq_sigmaOf p.feedbackRate p.kStar
    (p.scale j) (p.evenMatrix j) hZ ht,
    ← StageFeasibility.normalizedEvenState_eq_coordinates p j,
    StageFeasibility.cycleSecant_odd_prescribed p j hpstart] at hσO
  rw [← StageFeasibility.cycleRadius_zero_eq_radiusRatioOf p.feedbackRate p.kStar
    (p.scale j) (p.evenMatrix j) ht,
    ← StageFeasibility.normalizedEvenState_eq_coordinates p j,
    StageFeasibility.cycleRadius_even_prescribed p j hpstart] at hWE
  rw [← StageFeasibility.cycleRadius_one_eq_radiusRatioOf p.feedbackRate p.kStar
    (p.scale j) (p.evenMatrix j) hZ ht,
    ← StageFeasibility.normalizedEvenState_eq_coordinates p j,
    StageFeasibility.cycleRadius_odd_prescribed p j hpstart] at hWO
  exact ⟨hPE, hCE, hPO, hCO, hσE, hσO, hWE, hWO⟩

/-- lem:polar-continuation: for every cycle parameter sufficiently close to
`baseAngle` from above, the original prescribed trajectory stays in its slow
and fast tube for every sufficiently large natural starting index. Every raw
matrix is positive definite with positive off-diagonal entry, secant scalar,
and radius factor. The widths and threshold precede every subsequent choice
of starting index. -/
theorem polarContinuation :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ N > 0, ∃ M > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          (∀ j : ℕ,
            |((Parameters.of j₀ νStar).normalizedEvenState j).1 -
              (Parameters.of j₀ νStar).kStar| ≤ M * (Parameters.of j₀ νStar).scale j ∧
            FastContraction.fixedNorm (FastContraction.fastError
              ((Parameters.of j₀ νStar).normalizedEvenState j)) ≤
                N * (Parameters.of j₀ νStar).scale j ^ 3 ∧
            ((Parameters.of j₀ νStar).normalizedEvenState j).1 ∈ TwoCycle.normalizationSet ∧
              0 < ((Parameters.of j₀ νStar).normalizedEvenState j).1) ∧
          ∀ k : ℕ,
            ((Parameters.of j₀ νStar).matrix k).PosDef ∧
              0 < (Parameters.of j₀ νStar).matrix k 0 1 ∧
              0 < (Parameters.of j₀ νStar).sigma k ∧
              0 < (Parameters.of j₀ νStar).radiusRatio k := by
  obtain ⟨η, hη, hTube⟩ := actualTube
  refine ⟨η, hη, ?_⟩
  intro νStar hνStar
  have hparameter := (hTube νStar hνStar).1
  obtain ⟨R, hR, δ, hδ, hfeasible⟩ := existsPrescribedCycleFeasibility νStar hparameter
  obtain ⟨_, hν, N, hN, M, hM, J, hJ, htube⟩ := hTube νStar hνStar
  have hscaledTube : ∀ j₀ ≥ J, ∀ j : ℕ,
      |((Parameters.of j₀ νStar).normalizedEvenState j).1 -
        (Parameters.of j₀ νStar).kStar| ≤ M * (Parameters.of j₀ νStar).scale j ∧
      FastContraction.fixedNorm (FastContraction.fastError
        ((Parameters.of j₀ νStar).normalizedEvenState j)) ≤
          N * (Parameters.of j₀ νStar).scale j ^ 3 := by
    intro j₀ hj₀ j
    exact ⟨(htube j₀ hj₀ j).1, (htube j₀ hj₀ j).2.1⟩
  obtain ⟨Jnear, hJnear, hnear⟩ := statesNearCycle_of_uniformTube νStar hparameter hν
    N M hN hM J hJ hscaledTube R hR
  obtain ⟨Jscale, _, hscaleCutoff⟩ := existsStartThreshold δ hδ
  have hJfinal : 0 < max Jnear Jscale := hJ.trans_le (hJnear.trans (le_max_left _ _))
  refine ⟨hparameter, N, hN, M, hM, max Jnear Jscale, hJfinal, ?_⟩
  intro j₀ hj₀
  have hjNear : Jnear ≤ j₀ := (le_max_left Jnear Jscale).trans hj₀
  have hjScale : Jscale ≤ j₀ := (le_max_right Jnear Jscale).trans hj₀
  have hjTube : J ≤ j₀ := hJnear.trans hjNear
  have hstart : 0 < j₀ := hJ.trans_le hjTube
  have hpstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hstart
  have hscaleAll : ∀ j, (Parameters.of j₀ νStar).scale j ≤ δ := by
    intro j
    exact ((ScaleTails.scale_antitone (Parameters.of j₀ νStar) hpstart)
      (Nat.zero_le j)).trans (hscaleCutoff νStar j₀ hjScale).le
  have hcyclic := fun j ↦ hfeasible j₀ hstart j (hscaleAll j) (hnear j₀ hjNear j)
  refine ⟨htube j₀ hjTube, ?_⟩
  intro k
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨hPE, hCE, _, _, hσE, _, hWE, _⟩ := hcyclic j
    refine ⟨?_, ?_, hhalf.trans_le hσE, hhalf.trans_le hWE⟩
    · simpa only [Parameters.matrix_even] using hPE
    · simpa only [Parameters.matrix_even] using hCE
  · obtain ⟨_, _, hPO, hCO, _, hσO, _, hWO⟩ := hcyclic j
    refine ⟨?_, ?_, hhalf.trans_le hσO, hhalf.trans_le hWO⟩
    · simpa only [Parameters.matrix_odd] using hPO
    · simpa only [Parameters.matrix_odd] using hCO

/-- Helper for lem:polar-continuation: along every sufficiently late actual
source trajectory, the first diagonal coordinate tends to `KStar` and the
original fast-coordinate displacement tends to zero, so the full normalized
state tends to the source even cycle state. -/
theorem polarLimits :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        Tendsto (fun j : ℕ ↦ ((Parameters.of j₀ νStar).normalizedEvenState j).1)
          atTop (𝓝 (cycleK νStar)) ∧
        Tendsto (fun j : ℕ ↦ FastContraction.fastError
          ((Parameters.of j₀ νStar).normalizedEvenState j)) atTop (𝓝 0) ∧
        Tendsto (fun j : ℕ ↦ (Parameters.of j₀ νStar).normalizedEvenState j)
          atTop (𝓝 (TwoCycle.evenState (cycleK νStar))) := by
  obtain ⟨η, hη, hcontinuation⟩ := actualTube
  refine ⟨η, hη, ?_⟩
  intro νStar hνStar
  obtain ⟨hparameter, hν, N, hN, M, hM, J, hJ, hall⟩ := hcontinuation νStar hνStar
  refine ⟨J, hJ, ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hbounds := hall j₀ hj₀
  have hscale := ScaleTails.scale_tendsto_zero p
  have hslowLimit : Tendsto (fun j : ℕ ↦ M * p.scale j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hscale.const_mul M
  have hslowBound : ∀ j : ℕ, ‖(p.normalizedEvenState j).1 - cycleK νStar‖ ≤ M * p.scale j := by
    intro j
    simpa only [p, Real.norm_eq_abs, Parameters.kStar_def,
      Parameters.of_cycleParameter] using (hbounds j).1
  have hslowZero := squeeze_zero_norm hslowBound hslowLimit
  let B := ‖FastContraction.matrixOperator FastContraction.basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hfastLimit : Tendsto (fun j : ℕ ↦ (B * N) * p.scale j ^ 3) atTop (𝓝 0) := by
    simpa using (hscale.pow 3).const_mul (B * N)
  have hfastBound : ∀ j : ℕ, ‖FastContraction.fastError (p.normalizedEvenState j)‖ ≤
      (B * N) * p.scale j ^ 3 := by
    intro j
    let u := FastContraction.fastError (p.normalizedEvenState j)
    have hnorm : ‖u‖ ≤ B * FastContraction.fixedNorm u := by
      have hraw := FastContraction.norm_le_basisOperator_mul_fixedNorm u
      have hnonnegative := FastContraction.fixedNorm_nonneg u
      dsimp only [B]
      nlinarith
    calc
      ‖u‖ ≤ B * FastContraction.fixedNorm u := hnorm
      _ ≤ B * (N * p.scale j ^ 3) :=
        mul_le_mul_of_nonneg_left (hbounds j).2.1 hB.le
      _ = (B * N) * p.scale j ^ 3 := by ring
  have hslow : Tendsto (fun j : ℕ ↦ (p.normalizedEvenState j).1)
      atTop (𝓝 (cycleK νStar)) := tendsto_sub_nhds_zero_iff.mp hslowZero
  have hfast : Tendsto (fun j : ℕ ↦ FastContraction.fastError (p.normalizedEvenState j))
      atTop (𝓝 0) := squeeze_zero_norm hfastBound hfastLimit
  have hK : cycleK νStar ∈ TwoCycle.normalizationSet :=
    TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  have hinput := hslow.prodMk_nhds hfast
  have hstate := (continuousAt_perturbedState (cycleK νStar) hK hν).tendsto.comp hinput
  refine ⟨hslow, hfast, ?_⟩
  simpa only [Function.comp_def, FastRemainder.perturbedState_zero,
    perturbedState_fastError] using hstate

end DFP.Polar.Continuation
