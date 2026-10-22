/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_60
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology

noncomputable section

/- Source-facing layer: the Lévy distance on real distribution functions.
Core owner layer: the Lévy-Prokhorov metric on `ProbabilityMeasure ℝ`.
Bridge layer: pull the owner metric back along the canonical cdf/distribution-function
equivalence `probabilityMeasureEquivDistributionFunction`. -/
private noncomputable def distributionFunctionProbabilityMeasure
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] : ProbabilityMeasure ℝ :=
  probabilityMeasureEquivDistributionFunction.symm ⟨F, inferInstance⟩

/-- The Lévy distance on real distribution functions is the infimum of the nonnegative radii
`ε` for which `F x` stays between `G (x - ε) - ε` and `G (x + ε) + ε` for every `x`. -/
def levyDistance (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    ℝ :=
  sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}

/-- Unfolding `levyDistance F G` gives the textbook infimum formula for the Lévy distance. -/
theorem levyDistance_def
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G =
      sInf {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε} := rfl

/-- Helper for Exercise 13.2.6: the canonical probability measure attached to a distribution
function is its Lebesgue--Stieltjes measure. -/
private theorem distributionFunctionProbabilityMeasure_toMeasure
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    (distributionFunctionProbabilityMeasure F : Measure ℝ) = F.measure := by
  rfl

/-- Helper for Exercise 13.2.6: evaluating the attached probability measure on `(-∞, x]`
recovers the distribution function value `F x`. -/
private theorem distributionFunctionProbabilityMeasure_apply_Iic
    (F : StieltjesFunction ℝ) [hF : IsDistributionFunction F] (x : ℝ) :
    (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Iic x) = ENNReal.ofReal (F x) := by
  -- Proof comment: `distributionFunctionProbabilityMeasure F` is definitionally `F.measure`, and
  -- `StieltjesFunction.measure_Iic` turns the ray mass into the cdf increment from `-∞`.
  rw [distributionFunctionProbabilityMeasure_toMeasure]
  simpa using StieltjesFunction.measure_Iic F hF.tendsto_atBot_zero x

/-- Helper for Exercise 13.2.6: the mass of an interval `(a, b]` under the attached probability
measure is the corresponding Stieltjes increment `F b - F a`. -/
private theorem distributionFunctionProbabilityMeasure_apply_Ioc
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] (a b : ℝ) :
    (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Ioc a b) =
      ENNReal.ofReal (F b - F a) := by
  -- Proof comment: after identifying the owner measure with `F.measure`, the interval formula is
  -- exactly the defining Stieltjes increment computation.
  rw [distributionFunctionProbabilityMeasure_toMeasure]
  exact StieltjesFunction.measure_Ioc F a b

/-- Helper for Exercise 13.2.6: any strict upper bound on `levyDistance F G` contains an
admissible textbook Lévy window radius. -/
private theorem exists_levyWindow_of_lt_levyDistance
    (F G : StieltjesFunction ℝ) [hF : IsDistributionFunction F] [hG : IsDistributionFunction G]
    {η : ℝ} (hη : levyDistance F G < η) :
    ∃ ε, 0 ≤ ε ∧ ε < η ∧
      ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε := by
  let S : Set ℝ :=
    {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}
  have hS_nonempty : S.Nonempty := by
    refine ⟨1, ?_⟩
    refine ⟨by norm_num, ?_⟩
    intro x
    constructor
    · -- Proof comment: the unit radius dominates the lower tail because cdf values lie in `[0, 1]`.
      linarith [hF.nonneg x, hG.le_one (x - 1)]
    · -- Proof comment: the same unit radius dominates the upper tail by the symmetric
      -- `[0, 1]` bounds on distribution-function values.
      linarith [hF.le_one x, hG.nonneg (x + 1)]
  have hsInf_lt : sInf S < η := by
    simpa [levyDistance_def, S] using hη
  obtain ⟨ε, hεS, hεlt⟩ := exists_lt_of_csInf_lt hS_nonempty hsInf_lt
  exact ⟨ε, hεS.1, hεlt, hεS.2⟩

/-- Helper for Exercise 13.2.6: convergence of the Lévy distances to `0` forces weak convergence
of the underlying distribution functions in the source-facing sense. -/
private theorem eventually_lt_value_of_tendstoLevyDistanceZero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDistributionFunction F) (hFs : ∀ n, IsDistributionFunction (Fs n))
    (hlevy : Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0))
    {x a : ℝ} (hx : ContinuousAt F x) (ha : a < F x) :
    ∀ᶠ n in atTop, a < Fs n x := by
  -- Proof comment: choose a Lévy radius smaller than both the continuity modulus at `x` and the
  -- error budget `F x - a`; the left inequality in the textbook window then forces `Fs n x > a`.
  let ε : ℝ := (F x - a) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hx ε hε
  let η : ℝ := min (δ / 2) ε
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hdist :
      ∀ᶠ n in atTop, levyDistance (Fs n) F < η :=
    (tendsto_order.1 hlevy).2 η hη
  filter_upwards [hdist] with n hn
  letI : IsDistributionFunction (Fs n) := hFs n
  obtain ⟨r, hr_nonneg, hr_lt, hrwindow⟩ :=
    exists_levyWindow_of_lt_levyDistance (Fs n) F hn
  have hr_lt_δ : r < δ := by
    have hr_lt_halfδ : r < δ / 2 := lt_of_lt_of_le hr_lt (min_le_left _ _)
    linarith
  have hr_lt_ε : r < ε := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hdistLeft : dist (x - r) x < δ := by
    have hdistEq : dist (x - r) x = r := by
      rw [Real.dist_eq]
      ring_nf
      rw [abs_of_nonpos (neg_nonpos.mpr hr_nonneg), neg_neg]
    rw [hdistEq]
    exact hr_lt_δ
  have hleftClose : dist (F (x - r)) (F x) < ε := hδ hdistLeft
  have hwindowLower : F (x - r) - r ≤ Fs n x := (hrwindow x).1
  have hleftLower : F x - ε < F (x - r) := by
    have hleftClose' : |F (x - r) - F x| < ε := by
      simpa [Real.dist_eq] using hleftClose
    have habs := abs_lt.mp hleftClose'
    linarith
  dsimp [ε] at hε hr_lt_ε
  have hlower : F x - ε - r < Fs n x := by
    linarith
  have ha_lt : a < F x - ε - r := by
    dsimp [ε]
    nlinarith [ha, hr_lt_ε]
  exact lt_of_lt_of_le ha_lt hlower.le

/-- Helper for Exercise 13.2.6: convergence of the Lévy distances to `0` also yields eventual
upper bounds at continuity points of the limit distribution function. -/
private theorem eventually_gt_value_of_tendstoLevyDistanceZero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDistributionFunction F) (hFs : ∀ n, IsDistributionFunction (Fs n))
    (hlevy : Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0))
    {x b : ℝ} (hx : ContinuousAt F x) (hb : F x < b) :
    ∀ᶠ n in atTop, Fs n x < b := by
  -- Proof comment: use a Lévy radius smaller than both the continuity modulus at `x` and the
  -- gap `b - F x`; then the right inequality in the textbook window bounds `Fs n x` by `b`.
  let ε : ℝ := (b - F x) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.1 hx ε hε
  let η : ℝ := min (δ / 2) ε
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hdist :
      ∀ᶠ n in atTop, levyDistance (Fs n) F < η :=
    (tendsto_order.1 hlevy).2 η hη
  filter_upwards [hdist] with n hn
  letI : IsDistributionFunction (Fs n) := hFs n
  obtain ⟨r, hr_nonneg, hr_lt, hrwindow⟩ :=
    exists_levyWindow_of_lt_levyDistance (Fs n) F hn
  have hr_lt_δ : r < δ := by
    have hr_lt_halfδ : r < δ / 2 := lt_of_lt_of_le hr_lt (min_le_left _ _)
    linarith
  have hr_lt_ε : r < ε := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hdistRight : dist (x + r) x < δ := by
    have hdistEq : dist (x + r) x = r := by
      rw [Real.dist_eq]
      ring_nf
      rw [abs_of_nonneg hr_nonneg]
    rw [hdistEq]
    exact hr_lt_δ
  have hrightClose : dist (F (x + r)) (F x) < ε := hδ hdistRight
  have hrightUpper : F (x + r) < F x + ε := by
    have hrightClose' : |F (x + r) - F x| < ε := by
      simpa [Real.dist_eq] using hrightClose
    have habs := abs_lt.mp hrightClose'
    linarith
  have hwindowUpper : Fs n x ≤ F (x + r) + r := (hrwindow x).2
  dsimp [ε] at hε hr_lt_ε
  have hupper : Fs n x < F x + ε + r := lt_of_le_of_lt hwindowUpper <| by linarith
  have hb_gt : F x + ε + r < b := by
    dsimp [ε]
    nlinarith [hb, hr_lt_ε]
  exact lt_trans hupper hb_gt

/-- Helper for Exercise 13.2.6: convergence of the Lévy distances to `0` forces weak convergence
of the underlying distribution functions in the source-facing sense. -/
private theorem distributionFunctionWeaklyConvergesTo_of_tendstoLevyDistanceZero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDistributionFunction F) (hFs : ∀ n, IsDistributionFunction (Fs n))
    (hlevy : Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0)) :
    distribution_function_weakly_converges_to Fs F := by
  refine ⟨hF.toIsDefectiveDistributionFunction, ?_, ?_, ?_⟩
  · -- Proof comment: every approximating distribution function is also defective after
    -- forgetting that the endpoint value equals `1`.
    intro n
    exact (hFs n).toIsDefectiveDistributionFunction
  · intro x hx
    -- Proof comment: squeeze `Fs n x` between nearby values of `F` using a Lévy window radius
    -- that is both smaller than the continuity modulus at `x` and smaller than the target error.
    rw [tendsto_order]
    constructor
    · intro a ha
      exact eventually_lt_value_of_tendstoLevyDistanceZero Fs F hF hFs hlevy hx ha
    · intro b hb
      exact eventually_gt_value_of_tendstoLevyDistanceZero Fs F hF hFs hlevy hx hb
  · -- Proof comment: the endpoint condition remains automatic because all endpoint masses equal
    -- `1` for honest distribution functions.
    have hFmass : (F.measure Set.univ).toReal = 1 := by
      rw [StieltjesFunction.measure_univ F hF.tendsto_atBot_zero hF.tendsto_atTop_one]
      simp
    have hFsmass : ∀ n, (((Fs n).measure Set.univ).toReal) = 1 := by
      intro n
      rw [StieltjesFunction.measure_univ (Fs n) (hFs n).tendsto_atBot_zero
        (hFs n).tendsto_atTop_one]
      simp
    have hFsOne :
        (fun n ↦ (((Fs n).measure Set.univ).toReal)) = fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      exact hFsmass n
    rw [hFmass, hFsOne]
    simp

/-- Helper for Exercise 13.2.6: thickening a closed left ray by a positive radius stays inside the
corresponding shifted closed left ray. -/
private theorem thickening_Iic_subset_shifted_Iic
    (x ε : ℝ) (_hε : 0 < ε) :
    Metric.thickening ε (Set.Iic x) ⊆ Set.Iic (x + ε) := by
  -- Proof comment: every point in the thickening lies within distance `< ε` of some `z ≤ x`, so
  -- it must lie below `z + ε`, hence below the shifted endpoint `x + ε`.
  intro y hy
  rcases Metric.mem_thickening_iff.mp hy with ⟨z, hz, hyz⟩
  have hy_lt : y < z + ε := by
    have hyz' : |y - z| < ε := by
      simpa [Real.dist_eq] using hyz
    exact sub_lt_iff_lt_add'.mp (abs_lt.mp hyz').2
  exact (lt_of_lt_of_le hy_lt <| by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hz ε).le

/-- Helper for Exercise 13.2.6: the textbook Lévy window follows from any strict upper bound on
the owner Lévy-Prokhorov distance. -/
private theorem lower_levyWindow_of_lt_levyProkhorovEDist
    (F G : StieltjesFunction ℝ) [hF : IsDistributionFunction F] [hG : IsDistributionFunction G]
    {c : ℝ}
    (hc : 0 < c)
    (hlt :
      MeasureTheory.levyProkhorovEDist
          (distributionFunctionProbabilityMeasure F : Measure ℝ)
          (distributionFunctionProbabilityMeasure G : Measure ℝ) <
        ENNReal.ofReal c)
    (x : ℝ) :
    G (x - c) - c ≤ F x := by
  -- Proof comment: apply the right-hand Lévy-Prokhorov set inequality to `(-∞, x - c]` and then
  -- bound its thickening by `(-∞, x]`.
  have hraw :
      (distributionFunctionProbabilityMeasure G : Measure ℝ) (Set.Iic (x - c)) ≤
        (distributionFunctionProbabilityMeasure F : Measure ℝ)
            (thickening c (Set.Iic (x - c))) +
          ENNReal.ofReal c := by
    simpa [ENNReal.toReal_ofReal hc.le] using
      (MeasureTheory.right_measure_le_of_levyProkhorovEDist_lt
        (μ := (distributionFunctionProbabilityMeasure F : Measure ℝ))
        (ν := (distributionFunctionProbabilityMeasure G : Measure ℝ))
        hlt measurableSet_Iic)
  have hsubset : thickening c (Set.Iic (x - c)) ⊆ Set.Iic x := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      thickening_Iic_subset_shifted_Iic (x - c) c hc
  have henn :
      ENNReal.ofReal (G (x - c)) ≤ ENNReal.ofReal (F x) + ENNReal.ofReal c := by
    calc
      ENNReal.ofReal (G (x - c)) =
          (distributionFunctionProbabilityMeasure G : Measure ℝ) (Set.Iic (x - c)) := by
        rw [distributionFunctionProbabilityMeasure_apply_Iic]
      _ ≤ (distributionFunctionProbabilityMeasure F : Measure ℝ)
            (thickening c (Set.Iic (x - c))) +
          ENNReal.ofReal c := hraw
      _ ≤ (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Iic x) +
          ENNReal.ofReal c := by
        exact add_le_add (measure_mono hsubset) le_rfl
      _ = ENNReal.ofReal (F x) + ENNReal.ofReal c := by
        rw [distributionFunctionProbabilityMeasure_apply_Iic]
  have hreal : G (x - c) ≤ F x + c := by
    have henn' : ENNReal.ofReal (G (x - c)) ≤ ENNReal.ofReal (F x + c) := by
      simpa [ENNReal.ofReal_add, hF.nonneg x, hc.le] using henn
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hF.nonneg x) hc.le)).mp henn'
  linarith

/-- Helper for Exercise 13.2.6: a strict owner-distance bound also gives the upper textbook Lévy
window inequality. -/
private theorem upper_levyWindow_of_lt_levyProkhorovEDist
    (F G : StieltjesFunction ℝ) [hF : IsDistributionFunction F] [hG : IsDistributionFunction G]
    {c : ℝ}
    (hc : 0 < c)
    (hlt :
      MeasureTheory.levyProkhorovEDist
          (distributionFunctionProbabilityMeasure F : Measure ℝ)
          (distributionFunctionProbabilityMeasure G : Measure ℝ) <
        ENNReal.ofReal c)
    (x : ℝ) :
    F x ≤ G (x + c) + c := by
  -- Proof comment: apply the left-hand Lévy-Prokhorov set inequality to `(-∞, x]` and then
  -- bound its thickening by the shifted ray `(-∞, x + c]`.
  have hraw :
      (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Iic x) ≤
        (distributionFunctionProbabilityMeasure G : Measure ℝ) (thickening c (Set.Iic x)) +
          ENNReal.ofReal c := by
    simpa [ENNReal.toReal_ofReal hc.le] using
      (MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt
        (μ := (distributionFunctionProbabilityMeasure F : Measure ℝ))
        (ν := (distributionFunctionProbabilityMeasure G : Measure ℝ))
        hlt measurableSet_Iic)
  have hsubset : thickening c (Set.Iic x) ⊆ Set.Iic (x + c) :=
    thickening_Iic_subset_shifted_Iic x c hc
  have henn :
      ENNReal.ofReal (F x) ≤ ENNReal.ofReal (G (x + c)) + ENNReal.ofReal c := by
    calc
      ENNReal.ofReal (F x) =
          (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Iic x) := by
        rw [distributionFunctionProbabilityMeasure_apply_Iic]
      _ ≤ (distributionFunctionProbabilityMeasure G : Measure ℝ) (thickening c (Set.Iic x)) +
          ENNReal.ofReal c := hraw
      _ ≤ (distributionFunctionProbabilityMeasure G : Measure ℝ) (Set.Iic (x + c)) +
          ENNReal.ofReal c := by
        exact add_le_add (measure_mono hsubset) le_rfl
      _ = ENNReal.ofReal (G (x + c)) + ENNReal.ofReal c := by
        rw [distributionFunctionProbabilityMeasure_apply_Iic]
  have henn' : ENNReal.ofReal (F x) ≤ ENNReal.ofReal (G (x + c) + c) := by
    simpa [ENNReal.ofReal_add, hG.nonneg (x + c), hc.le] using henn
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hG.nonneg (x + c)) hc.le)).mp henn'

/-- Helper for Exercise 13.2.6: the textbook Lévy window follows from any strict upper bound on
the owner Lévy-Prokhorov distance. -/
private theorem levyDistance_le_distributionFunctionProbabilityMeasure_levyProkhorovDist
    (F G : StieltjesFunction ℝ) [hF : IsDistributionFunction F] [hG : IsDistributionFunction G] :
    levyDistance F G ≤
      MeasureTheory.levyProkhorovDist
        (distributionFunctionProbabilityMeasure F : Measure ℝ)
        (distributionFunctionProbabilityMeasure G : Measure ℝ) := by
  let d : ℝ :=
    MeasureTheory.levyProkhorovDist
      (distributionFunctionProbabilityMeasure F : Measure ℝ)
      (distributionFunctionProbabilityMeasure G : Measure ℝ)
  change levyDistance F G ≤ d
  -- Proof comment: for every positive slack `η`, the strict owner bound `d < d + η` yields the
  -- textbook two-sided cdf window with radius `d + η`; then `sInf` gives the desired inequality.
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hd_nonneg : 0 ≤ d := by
    simp [d, MeasureTheory.levyProkhorovDist]
  have hdη_pos : 0 < d + η := by
    linarith
  have hdist_lt : d < d + η := lt_add_of_pos_right d hη
  have hlt :
      MeasureTheory.levyProkhorovEDist
          (distributionFunctionProbabilityMeasure F : Measure ℝ)
          (distributionFunctionProbabilityMeasure G : Measure ℝ) <
        ENNReal.ofReal (d + η) := by
    exact
      (ENNReal.lt_ofReal_iff_toReal_lt (MeasureTheory.levyProkhorovEDist_ne_top _ _)).2 <| by
        simpa [d, MeasureTheory.levyProkhorovDist] using hdist_lt
  let S : Set ℝ :=
    {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}
  have hS_bdd : BddBelow S := ⟨0, fun ε hε ↦ hε.1⟩
  rw [levyDistance_def]
  refine csInf_le hS_bdd ?_
  refine ⟨by positivity, ?_⟩
  intro x
  exact ⟨lower_levyWindow_of_lt_levyProkhorovEDist F G hdη_pos hlt x,
    upper_levyWindow_of_lt_levyProkhorovEDist F G hdη_pos hlt x⟩

/-- Helper for Exercise 13.2.6: a textbook Lévy window for `(F, G)` automatically gives the
reversed window for `(G, F)` with the same radius. -/
private theorem levyWindow_symm
    (F G : StieltjesFunction ℝ) {ε : ℝ}
    (hwindow : ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε) :
    ∀ x : ℝ, F (x - ε) - ε ≤ G x ∧ G x ≤ F (x + ε) + ε := by
  -- Proof comment: evaluate the original two-sided window at `x - ε` and `x + ε` and then
  -- rearrange the resulting inequalities.
  intro x
  constructor
  · have hleft : F (x - ε) ≤ G ((x - ε) + ε) + ε := (hwindow (x - ε)).2
    have hleft' : F (x - ε) ≤ G x + ε := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft
    linarith
  · have hright : G ((x + ε) - ε) - ε ≤ F (x + ε) := (hwindow (x + ε)).1
    have hright' : G x - ε ≤ F (x + ε) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hright
    linarith

/-- Helper for Exercise 13.2.6: composing textbook Lévy windows adds their radii. -/
private theorem levyWindow_add
    (F G H : StieltjesFunction ℝ) {ε δ : ℝ}
    (hFG : ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε)
    (hGH : ∀ x : ℝ, H (x - δ) - δ ≤ G x ∧ G x ≤ H (x + δ) + δ) :
    ∀ x : ℝ, H (x - (ε + δ)) - (ε + δ) ≤ F x ∧ F x ≤ H (x + (ε + δ)) + (ε + δ) := by
  -- Proof comment: first move from `H` to `G` using radius `δ`, then from `G` to `F` using
  -- radius `ε`; the error terms add linearly.
  intro x
  constructor
  · have hGH_left : H (x - (ε + δ)) - δ ≤ G (x - ε) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hGH (x - ε)).1
    have hFG_left : G (x - ε) - ε ≤ F x := (hFG x).1
    linarith
  · have hFG_right : F x ≤ G (x + ε) + ε := (hFG x).2
    have hGH_right : G (x + ε) ≤ H (x + (ε + δ)) + δ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hGH (x + ε)).2
    linarith

/-- Helper for Exercise 13.2.6: if the Lévy distance vanishes, then `F` lies pointwise below `G`.
-/
private theorem pointwise_le_of_levyDistance_eq_zero
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G]
    (hzero : levyDistance F G = 0) (x : ℝ) :
    F x ≤ G x := by
  -- Route correction: instead of passing through the unresolved owner-space equality theorem, use
  -- arbitrarily small textbook windows together with right continuity of `G` at `x`.
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hcont : ContinuousWithinAt G (Set.Ici x) x := G.right_continuous x
  rw [Metric.continuousWithinAt_iff] at hcont
  rcases hcont (η / 2) (by positivity) with ⟨δ, hδpos, hδ⟩
  have hsmall : levyDistance F G < min δ (η / 2) := by
    simpa [hzero] using (lt_min hδpos (by positivity) : (0 : ℝ) < min δ (η / 2))
  obtain ⟨ε, hεnn, hεlt, hεwindow⟩ := exists_levyWindow_of_lt_levyDistance F G hsmall
  have hεδ : ε < δ := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεη : ε < η / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hx_mem : x + ε ∈ Set.Ici x := by
    simp [Set.mem_Ici]
    nlinarith
  have hx_dist : dist (x + ε) x < δ := by
    rw [Real.dist_eq]
    have : x + ε - x = ε := by ring
    rw [this, abs_of_nonneg hεnn]
    exact hεδ
  have hclose : dist (G (x + ε)) (G x) < η / 2 := hδ hx_mem hx_dist
  have hG_upper : G (x + ε) < G x + η / 2 := by
    have hclose' : |G (x + ε) - G x| < η / 2 := by
      simpa [Real.dist_eq] using hclose
    linarith [abs_lt.mp hclose']
  have hwindowUpper : F x ≤ G (x + ε) + ε := (hεwindow x).2
  linarith

/-- Helper for Exercise 13.2.6: weak convergence in the source-facing sense gives convergence of
the attached interval masses on `Ioc` intervals whose endpoints are continuity points of the
limit distribution function. -/
private theorem tendsto_distributionFunctionProbabilityMeasure_apply_Ioc_of_weakConvergence
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDistributionFunction F) (hFs : ∀ n, IsDistributionFunction (Fs n))
    (h : distribution_function_weakly_converges_to Fs F) {a b : ℝ}
    (ha : ContinuousAt F a) (hb : ContinuousAt F b) :
    Tendsto
      (fun n ↦
        letI : IsDistributionFunction (Fs n) := hFs n
        distributionFunctionProbabilityMeasure (Fs n) (Set.Ioc a b))
      atTop
      (𝓝 (distributionFunctionProbabilityMeasure F (Set.Ioc a b))) := by
  rcases h with ⟨_, _, hpointwise, _⟩
  have ha_tendsto : Tendsto (fun n ↦ Fs n a) atTop (𝓝 (F a)) := hpointwise ha
  have hb_tendsto : Tendsto (fun n ↦ Fs n b) atTop (𝓝 (F b)) := hpointwise hb
  -- Proof comment: rewrite each interval mass as the Stieltjes increment `F b - F a`, so the
  -- convergence follows from subtraction of the endpoint limits.
  have hdiff :
      Tendsto (fun n ↦ Fs n b - Fs n a) atTop (𝓝 (F b - F a)) := hb_tendsto.sub ha_tendsto
  let μs : ℕ → ENNReal := fun n ↦
    (letI : IsDistributionFunction (Fs n) := hFs n;
      ((distributionFunctionProbabilityMeasure (Fs n) : Measure ℝ) (Set.Ioc a b)))
  have hEqF :
      (distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Ioc a b) =
        ENNReal.ofReal (F b - F a) := by
    rw [distributionFunctionProbabilityMeasure_apply_Ioc]
  have hEq :
      ∀ n,
        μs n = ENNReal.ofReal (Fs n b - Fs n a) := by
    intro n
    letI : IsDistributionFunction (Fs n) := hFs n
    dsimp [μs]
    exact distributionFunctionProbabilityMeasure_apply_Ioc (Fs n) a b
  have hIoc :
      Tendsto (fun n ↦ ENNReal.ofReal (Fs n b - Fs n a)) atTop
        (𝓝 (ENNReal.ofReal (F b - F a))) := by
    simpa using ENNReal.tendsto_ofReal hdiff
  have hμs :
      Tendsto μs atTop
        (𝓝 ((distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Ioc a b))) := by
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hEq n).symm) <| by
      simpa [hEqF] using hIoc
  have hμsNNReal :
      Tendsto (fun n ↦ (μs n).toNNReal) atTop
        (𝓝 (((distributionFunctionProbabilityMeasure F : Measure ℝ) (Set.Ioc a b)).toNNReal)) := by
    exact
      (ENNReal.tendsto_toNNReal
        (measure_ne_top ((distributionFunctionProbabilityMeasure F : Measure ℝ)) _)).comp hμs
  simpa [μs, ProbabilityMeasure.coeFn_def] using hμsNNReal

/-- Helper for Exercise 13.2.6: every open neighborhood contains an `Ioc` interval with
continuity endpoints of the limiting distribution function. -/
private theorem exists_continuityIoc_mem_nhds_subset
    (F : StieltjesFunction ℝ) [IsDefectiveDistributionFunction F] {G : Set ℝ}
    (hG : IsOpen G) {x : ℝ} (hx : x ∈ G) :
    ∃ a b : ℝ, ContinuousAt F a ∧ ContinuousAt F b ∧ a < b ∧
      Set.Ioc a b ∈ 𝓝 x ∧ Set.Ioc a b ⊆ G := by
  let C : Set ℝ := {y | ContinuousAt F y}
  have hC_dense : Dense C := by
    let D : Set ℝ := {y | ¬ ContinuousAt F y}
    have hD_countable : D.Countable := F.mono.countable_not_continuousAt
    have hD_dense : Dense Dᶜ := hD_countable.dense_compl ℝ
    simpa [C, D, Set.compl_setOf] using hD_dense
  -- Proof comment: shrink to an open interval around `x`, then choose continuity points on the
  -- left and right using density of the continuity set.
  rcases mem_nhds_iff_exists_Ioo_subset.1 (hG.mem_nhds hx) with ⟨l, r, hxIoo, hsubset⟩
  obtain ⟨a, haC, ha_between⟩ := hC_dense.exists_between hxIoo.1
  obtain ⟨b, hbC, hb_between⟩ := hC_dense.exists_between hxIoo.2
  refine ⟨a, b, haC, hbC, ha_between.2.trans hb_between.1,
    Ioc_mem_nhds ha_between.2 hb_between.1, ?_⟩
  intro y hy
  have hy_left : l < y := lt_trans ha_between.1 hy.1
  have hy_right : y < r := lt_of_le_of_lt hy.2 hb_between.2
  exact hsubset ⟨hy_left, hy_right⟩

/-- Helper for Exercise 13.2.6: source-facing weak convergence of distribution functions induces
weak convergence of the attached probability measures. -/
private theorem tendstoProbabilityMeasure_of_distributionFunctionWeaklyConvergesTo
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDistributionFunction F) (hFs : ∀ n, IsDistributionFunction (Fs n))
    (h : distribution_function_weakly_converges_to Fs F) :
    Tendsto
      (fun n ↦
        letI : IsDistributionFunction (Fs n) := hFs n
        distributionFunctionProbabilityMeasure (Fs n))
      atTop (𝓝 (distributionFunctionProbabilityMeasure F)) := by
  let C : Set ℝ := {x | ContinuousAt F x}
  let S : Set (Set ℝ) := {s | ∃ a ∈ C, ∃ b ∈ C, a < b ∧ Set.Ioc a b = s}
  have hS : IsPiSystem S := by
    simpa [S] using isPiSystem_Ioc_mem C C
  letI : IsDefectiveDistributionFunction F := hF.toIsDefectiveDistributionFunction
  -- Route correction: use the continuity-endpoint `Ioc` π-system instead of the earlier
  -- open-set/compact-approximation detour.
  refine hS.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · intro s hs
    rcases hs with ⟨a, _, b, _, _, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a, b, ha, hb, hab, hnhds, hsub⟩ := exists_continuityIoc_mem_nhds_subset F hu hx
    refine ⟨Set.Ioc a b, ?_, hnhds, hsub⟩
    exact ⟨a, by simpa [C] using ha, b, by simpa [C] using hb, hab, rfl⟩
  · intro s hs
    rcases hs with ⟨a, haC, b, hbC, _hab, rfl⟩
    exact tendsto_distributionFunctionProbabilityMeasure_apply_Ioc_of_weakConvergence
      Fs F hF hFs h (by simpa [C] using haC) (by simpa [C] using hbC)

/-- Item (i) of Exercise 13.2.6: the Lévy distance is nonnegative on real distribution
functions. -/
theorem levyDistance_nonneg
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    0 ≤ levyDistance F G := by
  -- Proof comment: every admissible Lévy radius is nonnegative by definition, so its infimum is
  -- also nonnegative.
  rw [levyDistance_def]
  exact Real.sInf_nonneg fun ε hε ↦ hε.1

/-- Item (i) of Exercise 13.2.6: the Lévy distance is symmetric on real distribution
functions. -/
theorem levyDistance_comm
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = levyDistance G F := by
  -- Proof comment: the admissible radii are identical after swapping `F` and `G`, because the
  -- textbook window is symmetric up to shifting the evaluation point by `± ε`.
  let SFG : Set ℝ :=
    {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, G (x - ε) - ε ≤ F x ∧ F x ≤ G (x + ε) + ε}
  let SGF : Set ℝ :=
    {ε : ℝ | 0 ≤ ε ∧ ∀ x : ℝ, F (x - ε) - ε ≤ G x ∧ G x ≤ F (x + ε) + ε}
  have hEq : SFG = SGF := by
    ext ε
    constructor
    · intro hε
      exact ⟨hε.1, levyWindow_symm F G hε.2⟩
    · intro hε
      exact ⟨hε.1, levyWindow_symm G F hε.2⟩
  simpa [levyDistance_def, SFG, SGF] using congrArg sInf hEq

-- Proof sketch: if the distance is zero, arbitrarily small textbook windows and right continuity
-- force pointwise equality in both directions.
/-- Item (i) of Exercise 13.2.6: on distribution functions, the Lévy distance vanishes exactly
when the two functions are equal. -/
theorem levyDistance_eq_zero_iff
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    levyDistance F G = 0 ↔ F = G := by
  constructor
  · intro h
    ext x
    apply le_antisymm
    · exact pointwise_le_of_levyDistance_eq_zero F G h x
    · have hsymm : levyDistance G F = 0 := by
        simpa [levyDistance_comm] using h
      exact pointwise_le_of_levyDistance_eq_zero G F hsymm x
  · intro h
    subst h
    apply le_antisymm
    · rw [levyDistance_def]
      refine csInf_le ?_ ?_
      · exact ⟨0, fun ε hε ↦ hε.1⟩
      · refine ⟨le_rfl, ?_⟩
        intro x
        constructor <;> simp
    · exact levyDistance_nonneg

/-- Item (i) of Exercise 13.2.6: the Lévy distance satisfies the triangle inequality on real
distribution functions. -/
theorem levyDistance_triangle
    {F G H : StieltjesFunction ℝ}
    [IsDistributionFunction F] [IsDistributionFunction G] [IsDistributionFunction H] :
    levyDistance F H ≤ levyDistance F G + levyDistance G H := by
  -- Proof comment: compose an `ε`-window from `F` to `G` with a `δ`-window from `G` to `H`;
  -- the resulting radius is `ε + δ`, so the infimum satisfies the triangle inequality.
  refine le_of_forall_pos_le_add ?_
  intro η hη
  obtain ⟨ε, hεnn, hεlt, hεwindow⟩ :=
    exists_levyWindow_of_lt_levyDistance F G
      (lt_add_of_pos_right (levyDistance F G) (half_pos hη))
  obtain ⟨δ, hδnn, hδlt, hδwindow⟩ :=
    exists_levyWindow_of_lt_levyDistance G H
      (lt_add_of_pos_right (levyDistance G H) (half_pos hη))
  have hsum_window :
      ∀ x : ℝ, H (x - (ε + δ)) - (ε + δ) ≤ F x ∧ F x ≤ H (x + (ε + δ)) + (ε + δ) :=
    levyWindow_add F G H hεwindow hδwindow
  have hsum_mem :
      ε + δ ∈
        {ρ : ℝ | 0 ≤ ρ ∧ ∀ x : ℝ, H (x - ρ) - ρ ≤ F x ∧ F x ≤ H (x + ρ) + ρ} := by
    exact ⟨add_nonneg hεnn hδnn, hsum_window⟩
  have hsum_lt : ε + δ < levyDistance F G + levyDistance G H + η := by
    linarith
  rw [levyDistance_def]
  refine le_trans ?_ hsum_lt.le
  refine csInf_le ?_ hsum_mem
  exact ⟨0, fun ρ hρ ↦ hρ.1⟩

-- Proof sketch: transport source-facing weak convergence to the owner probability measures on
-- `ℝ`, use the Lévy-Prokhorov topology to get owner-distance convergence, and then bound the
-- source-facing Lévy distance above by that owner distance. The converse direction is already a
-- direct continuity-point argument from the textbook window definition.
/-- Exercise 13.2.6 (5): Item (ii). A sequence of real distribution functions converges weakly to
`F` exactly when its Lévy distances to `F` converge to `0`. -/
theorem distribution_function_convergence_iff_levyDistance_tendsto_zero
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) :
    Π _hF : IsDistributionFunction F,
      Π _hFs : ∀ n, IsDistributionFunction (Fs n),
        distribution_function_weakly_converges_to Fs F ↔
      Tendsto (fun n ↦ levyDistance (Fs n) F) atTop (𝓝 0) := by
  intro hF hFs
  constructor
  · intro hconv
    have hμ :
        Tendsto
          (fun n ↦
            letI : IsDistributionFunction (Fs n) := hFs n
            distributionFunctionProbabilityMeasure (Fs n))
          atTop (𝓝 (distributionFunctionProbabilityMeasure F)) :=
      tendstoProbabilityMeasure_of_distributionFunctionWeaklyConvergesTo Fs F hF hFs hconv
    have hLP :
        Tendsto
          (fun n ↦
            letI : IsDistributionFunction (Fs n) := hFs n
            MeasureTheory.LevyProkhorov.ofMeasure
              (distributionFunctionProbabilityMeasure (Fs n)))
          atTop
          (𝓝 (MeasureTheory.LevyProkhorov.ofMeasure
            (distributionFunctionProbabilityMeasure F))) := by
      have hofMeasure :
          Tendsto MeasureTheory.LevyProkhorov.ofMeasure
            (𝓝 (distributionFunctionProbabilityMeasure F))
            (𝓝 (MeasureTheory.LevyProkhorov.ofMeasure
              (distributionFunctionProbabilityMeasure F))) :=
        MeasureTheory.LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto
      simpa using hofMeasure.comp hμ
    have hdist :
        Tendsto
          (fun n ↦
            letI : IsDistributionFunction (Fs n) := hFs n
            MeasureTheory.levyProkhorovDist
              (distributionFunctionProbabilityMeasure (Fs n) : Measure ℝ)
              (distributionFunctionProbabilityMeasure F : Measure ℝ))
          atTop (𝓝 0) := by
      simpa [MeasureTheory.LevyProkhorov.dist_probabilityMeasure_def] using
        (tendsto_iff_dist_tendsto_zero.1 hLP)
    have hnonneg : ∀ n, 0 ≤ levyDistance (Fs n) F := by
      intro n
      letI : IsDistributionFunction (Fs n) := hFs n
      exact levyDistance_nonneg
    have hbound :
        ∀ n,
          levyDistance (Fs n) F ≤
            MeasureTheory.levyProkhorovDist
              (distributionFunctionProbabilityMeasure (Fs n) : Measure ℝ)
              (distributionFunctionProbabilityMeasure F : Measure ℝ) := by
      intro n
      letI : IsDistributionFunction (Fs n) := hFs n
      exact levyDistance_le_distributionFunctionProbabilityMeasure_levyProkhorovDist (Fs n) F
    -- Proof comment: weak convergence transfers to the owner probability measures, hence to the
    -- Lévy-Prokhorov metric model; the source-facing Lévy distance is pointwise bounded above by
    -- that owner distance, so it also tends to `0`.
    exact squeeze_zero hnonneg hbound hdist
  · intro hlevy
    exact distributionFunctionWeaklyConvergesTo_of_tendstoLevyDistanceZero Fs F hF hFs hlevy

/-- Helper for Exercise 13.2.6: `gridQuantizer n` rounds points inside `[-(n + 1), n + 1]` down
to the mesh `(n + 1)⁻¹` and sends the outside tail to `0`. -/
private def gridQuantizer (n : ℕ) : ℝ → ℝ :=
  let m : ℕ := n + 1
  Set.piecewise {x : ℝ | |x| ≤ m}
    (fun x => ((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) / m - m)
    (fun _ => 0)

/-- Helper for Exercise 13.2.6: the quantizer `gridQuantizer n` is measurable. -/
private theorem gridQuantizer_measurable (n : ℕ) : Measurable (gridQuantizer n) := by
  let m : ℕ := n + 1
  have hfloor : Measurable fun x : ℝ => ⌊(m : ℝ) * (x + m)⌋₊ :=
    Nat.measurable_floor.comp (measurable_const.mul (measurable_id.add measurable_const))
  have hcore : Measurable fun x : ℝ => ((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) / m - m := by
    -- Proof comment: the floor term is measurable, and casting/countable codomains preserve
    -- measurability before the final affine rescaling.
    exact (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hfloor).div_const m).sub
      measurable_const
  have hset : MeasurableSet {x : ℝ | |x| ≤ m} :=
    measurableSet_le continuous_abs.measurable measurable_const
  simpa [gridQuantizer, m] using hcore.piecewise hset measurable_const

/-- Helper for Exercise 13.2.6: the quantizer `gridQuantizer n` has finite image. -/
private theorem gridQuantizer_range_finite (n : ℕ) : (Set.range (gridQuantizer n)).Finite := by
  let m : ℕ := n + 1
  refine Set.Finite.subset
    ((Set.finite_singleton 0).union
      (Set.Finite.image (fun k : ℕ => (k : ℝ) / m - m) (Set.finite_Icc 0 (2 * m ^ 2)))) ?_
  intro y hy
  rcases hy with ⟨x, rfl⟩
  by_cases hx : |x| ≤ n + 1
  · right
    refine ⟨⌊(m : ℝ) * (x + m)⌋₊, ?_, ?_⟩
    · -- Proof comment: inside the truncation window the floor index stays between `0` and
      -- the endpoint `2 * (n + 1)^2`.
      refine Set.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
      have hx_left : -(m : ℝ) ≤ x := by
        simpa [m] using (abs_le.mp hx).1
      have hx_right : x ≤ m := by
        simpa [m] using (abs_le.mp hx).2
      have hxm_nonneg : 0 ≤ x + m := by
        linarith
      have hbound : (m : ℝ) * (x + m) ≤ (2 * m ^ 2 : ℕ) := by
        have hxm_le : x + m ≤ 2 * m := by
          linarith
        have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
        calc
          (m : ℝ) * (x + m) ≤ (m : ℝ) * (2 * m) := by
            exact mul_le_mul_of_nonneg_left hxm_le hm_nonneg
          _ = (2 * m ^ 2 : ℕ) := by
            norm_num [pow_two, mul_assoc, mul_left_comm, mul_comm]
      exact Nat.floor_le_of_le hbound
    · have hxmem : x ∈ {x : ℝ | |x| ≤ m} := by
        simpa [m] using hx
      rw [gridQuantizer]
      rw [Set.piecewise_eq_of_mem _ _ _ hxmem]
  · have hxmem : x ∉ {x : ℝ | |x| ≤ m} := by
      simpa [m] using hx
    left
    rw [gridQuantizer]
    rw [Set.piecewise_eq_of_notMem _ _ _ hxmem]
    simp

/-- Helper for Exercise 13.2.6: inside the truncation window, `gridQuantizer n` moves points by at
most the mesh size `(n + 1)⁻¹`. -/
private theorem gridQuantizer_dist_le (n : ℕ) {x : ℝ} (hx : |x| ≤ n + 1) :
    dist (gridQuantizer n x) x ≤ 1 / (n + 1 : ℝ) := by
  let m : ℕ := n + 1
  have hm : (0 : ℝ) < m := by
    exact_mod_cast Nat.succ_pos n
  have h_nonneg : 0 ≤ (m : ℝ) * (x + m) := by
    have hx_left : -(m : ℝ) ≤ x := by
      simpa [m] using (abs_le.mp hx).1
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by exact Nat.cast_nonneg m]
  have h_floor :
      |((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) - (m : ℝ) * (x + m)| ≤ 1 := by
    -- Proof comment: the floor coordinate differs from its real input by at most one unit.
    simpa using (Nat.abs_floor_sub_le h_nonneg)
  have h_div :
      |(((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) - (m : ℝ) * (x + m)) / m| ≤ 1 / (m : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := hm.le
    have := div_le_div_of_nonneg_right h_floor hm_nonneg
    simpa [abs_div, abs_of_nonneg hm_nonneg, abs_of_pos hm] using this
  have hxmem : x ∈ {x : ℝ | |x| ≤ m} := by
    simpa [m] using hx
  have h_eq :
      (((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) - (m : ℝ) * (x + m)) / m =
        gridQuantizer n x - x := by
    have hm_ne : (m : ℝ) ≠ 0 := by
      positivity
    have hgrid :
        gridQuantizer n x = ((⌊(m : ℝ) * (x + m)⌋₊ : ℕ) : ℝ) / m - m := by
      rw [gridQuantizer]
      rw [Set.piecewise_eq_of_mem _ _ _ hxmem]
    -- Proof comment: after expanding the quantizer formula, the difference is exactly the scaled
    -- floor error from the previous step.
    rw [hgrid]
    field_simp [hm_ne]
    ring
  rw [Real.dist_eq, ← h_eq]
  simpa [m] using h_div

/-- Helper for Exercise 13.2.6: pushing a probability measure forward by `gridQuantizer n`
produces a finitely supported measure. -/
private theorem support_map_gridQuantizer_finite (P : ProbabilityMeasure ℝ) (n : ℕ) :
    (((ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ).support).Finite := by
  let q := gridQuantizer n
  have hfinite : (Set.range q).Finite := gridQuantizer_range_finite n
  have hclosed : IsClosed (Set.range q) := hfinite.isClosed
  have hae :
      Set.range q ∈
        ae ((ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable :
          ProbabilityMeasure ℝ) : Measure ℝ) := by
    -- Proof comment: the pushforward is carried entirely by the finite image of the quantizer.
    rw [mem_ae_iff]
    rw [ProbabilityMeasure.map_apply' _ (gridQuantizer_measurable n).aemeasurable
      hclosed.measurableSet.compl]
    simp [q]
  exact hfinite.subset
    (((ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable :
        ProbabilityMeasure ℝ) : Measure ℝ).support_subset_of_isClosed hclosed hae)

/-- Helper for Exercise 13.2.6: if a measurable map moves points by at most `δ` outside a set of
`P`-mass at most `δ`, then its pushforward law stays within Lévy-Prokhorov distance `δ` of `P`. -/
private theorem levyProkhorovDist_map_le_of_close
    (P : ProbabilityMeasure ℝ) {q : ℝ → ℝ} (hq : Measurable q)
    {δ : ℝ} (hδ : 0 ≤ δ) {s : Set ℝ} (_hs : MeasurableSet s)
    (hclose : ∀ x, x ∉ s → dist (q x) x ≤ δ)
    (hsmall : (P : Measure ℝ) s ≤ ENNReal.ofReal δ) :
    levyProkhorovDist
      (((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ))
      (P : Measure ℝ) ≤ δ := by
  refine levyProkhorovDist_le_of_forall_le
    (μ := ((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ))
    (ν := (P : Measure ℝ)) hδ ?_
  intro ε B hεδ hB
  have hsle : (P : Measure ℝ) s ≤ ENNReal.ofReal ε :=
    hsmall.trans (ENNReal.ofReal_le_ofReal hεδ.le)
  have hsubset : q ⁻¹' B ⊆ Metric.thickening ε B ∪ s := by
    -- Proof comment: away from the bad set `s`, every preimage point lands inside the
    -- `ε`-thickening because the map is `δ`-close to the identity and `δ < ε`.
    intro x hxB
    by_cases hx : x ∈ s
    · exact Or.inr hx
    · left
      refine Metric.mem_thickening_iff.mpr ⟨q x, hxB, ?_⟩
      simpa [dist_comm] using lt_of_le_of_lt (hclose x hx) hεδ
  calc
    (((ProbabilityMeasure.map P hq.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ)) B
        = (P : Measure ℝ) (q ⁻¹' B) := by
      rw [ProbabilityMeasure.map_apply' _ hq.aemeasurable hB]
    _ ≤ (P : Measure ℝ) (Metric.thickening ε B ∪ s) := measure_mono hsubset
    _ ≤ (P : Measure ℝ) (Metric.thickening ε B) + (P : Measure ℝ) s := measure_union_le _ _
    _ ≤ (P : Measure ℝ) (Metric.thickening ε B) + ENNReal.ofReal ε := by
      exact add_le_add le_rfl hsle

/-- Helper for Exercise 13.2.6: the tail masses `P {x | n < ‖x‖}` vanish along `n → ∞`. -/
private theorem tendsto_tailMass_toReal_zero (P : ProbabilityMeasure ℝ) :
    Tendsto (fun n : ℕ ↦ ((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal) atTop (𝓝 0) := by
  have htight : IsTightMeasureSet ({(P : Measure ℝ)} : Set (Measure ℝ)) :=
    MeasureTheory.isTightMeasureSet_singleton
  have htail : Tendsto (fun r : ℝ ↦ (P : Measure ℝ) {x : ℝ | r < ‖x‖}) atTop (𝓝 0) := by
    -- Proof comment: a singleton of probability measures is tight, so the tail masses decay to
    -- zero along expanding norm thresholds.
    simpa using (MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet htight)
  have htailSeq :
      Tendsto (fun n : ℕ ↦ (P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}) atTop (𝓝 0) := by
    simpa using htail.comp tendsto_natCast_atTop_atTop
  rw [← ENNReal.toReal_zero]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htailSeq

/-- Helper for Exercise 13.2.6: the quantized pushforward measure is close to `P` in
Lévy-Prokhorov distance, with error controlled by the mesh size and the discarded tail mass. -/
private theorem dist_map_gridQuantizer_le
    (P : ProbabilityMeasure ℝ) (n : ℕ) :
    dist
        (LevyProkhorov.ofMeasure
          (ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable))
        (LevyProkhorov.ofMeasure P) ≤
      max (1 / (n + 1 : ℝ)) (((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal) := by
  have hsmall :
      (P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖} ≤
        ENNReal.ofReal
          (max (1 / (n + 1 : ℝ)) (((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal)) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hdist :
      levyProkhorovDist
          (((ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable :
              ProbabilityMeasure ℝ) : Measure ℝ))
          (P : Measure ℝ) ≤
        max (1 / (n + 1 : ℝ)) (((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal) := by
    refine levyProkhorovDist_map_le_of_close P (gridQuantizer_measurable n) ?_
      (show MeasurableSet {x : ℝ | (n : ℝ) < ‖x‖} from
        measurableSet_lt measurable_const measurable_norm)
      ?_ hsmall
    · positivity
    · intro x hx
      have hx' : |x| ≤ n + 1 := by
        by_contra h'
        exact hx (show (n : ℝ) < ‖x‖ by
          linarith [show (n + 1 : ℝ) < ‖x‖ by simpa [not_le] using h'])
      exact le_trans (gridQuantizer_dist_le n hx') (le_max_left _ _)
  simpa [LevyProkhorov.dist_probabilityMeasure_def] using hdist

-- Proof sketch: approximate `P` by discrete probability measures obtained from quantizing the
-- real line into finer and finer partitions, then show their laws converge weakly to `P`.
/-- Item (iii) of Exercise 13.2.6: every probability measure on `ℝ` is the weak limit of a
sequence of finitely supported probability measures. -/
theorem exists_tendsto_probabilityMeasure_with_finite_support
    (P : ProbabilityMeasure ℝ) :
    ∃ Ps : ℕ → ProbabilityMeasure ℝ,
      (∀ n, ((Ps n : Measure ℝ).support).Finite) ∧
      Tendsto Ps atTop (𝓝 P) := by
  let Ps : ℕ → ProbabilityMeasure ℝ :=
    fun n ↦ ProbabilityMeasure.map P (gridQuantizer_measurable n).aemeasurable
  refine ⟨Ps, ?_, ?_⟩
  · -- Proof comment: each quantizer has finite image, so the pushforward support is finite.
    intro n
    exact support_map_gridQuantizer_finite P n
  · have htailReal : Tendsto
        (fun n : ℕ ↦ ((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal) atTop (𝓝 0) :=
      tendsto_tailMass_toReal_zero P
    have hbound :
        ∀ n,
          dist (LevyProkhorov.ofMeasure (Ps n)) (LevyProkhorov.ofMeasure P) ≤
            max (1 / (n + 1 : ℝ)) (((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal) := by
      intro n
      simpa [Ps] using dist_map_gridQuantizer_le P n
    have hstep : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmax :
        Tendsto
          (fun n : ℕ ↦ max (1 / (n + 1 : ℝ)) (((P : Measure ℝ) {x : ℝ | (n : ℝ) < ‖x‖}).toReal))
          atTop (𝓝 0) := by
      simpa using hstep.max htailReal
    have hdist0 :
        Tendsto (fun n ↦ dist (LevyProkhorov.ofMeasure (Ps n)) (LevyProkhorov.ofMeasure P))
          atTop (𝓝 0) := by
      -- Proof comment: the Lévy-Prokhorov distance is squeezed by the mesh size and the tail mass.
      refine squeeze_zero (fun n ↦ dist_nonneg) hbound hmax
    have hLP : Tendsto (fun n ↦ LevyProkhorov.ofMeasure (Ps n)) atTop
        (𝓝 (LevyProkhorov.ofMeasure P)) :=
      tendsto_iff_dist_tendsto_zero.2 hdist0
    -- Proof comment: transport the metric convergence on the Lévy-Prokhorov model back to the
    -- usual topology on `ProbabilityMeasure ℝ`.
    simpa [Ps] using
      (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
        (LevyProkhorov.ofMeasure P)).comp hLP
