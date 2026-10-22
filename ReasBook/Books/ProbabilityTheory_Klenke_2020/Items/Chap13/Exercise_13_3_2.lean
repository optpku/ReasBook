/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

-- Proof sketch: for the forward implication, tightness gives uniform control of Gaussian tails,
-- which forces uniform bounds on both the means and variances. For the reverse implication, a
-- bounded parameter set yields a common compact interval capturing arbitrarily large mass for all
-- Gaussian laws in the family.
/- Exercise 13.3.2 is `source-facing` in the tightness/weak-convergence domain. Its primitive
data are the Gaussian mean and strictly positive variance parameters, while the `core/canonical`
owner abstractions are `ProbabilityTheory.gaussianReal` for the laws and
`MeasureTheory.IsTightMeasureSet` for family tightness. Using `Set.Ioi (0 : ℝ≥0)` keeps strict
positivity as primitive data in the owner parameter type, so the family can be expressed directly
as `p ↦ gaussianReal p.1 p.2` instead of via the bridge `Real.toNNReal`. -/
/-- Helper for Exercise 13.3.2: if a probability measure assigns less than `1/4` mass to the
complement of a centered closed ball, then that ball already carries more than `1/2` of the mass.
-/
private lemma one_half_lt_measure_closedBall_of_measure_norm_gt_lt_quarter
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {R : ℝ}
    (hR : μ {x : ℝ | R < ‖x‖} ≤ (1 / 4 : ℝ≥0∞)) :
    (1 / 2 : ℝ≥0∞) < μ (Metric.closedBall (0 : ℝ) R) := by
  have hmeas : MeasurableSet (Metric.closedBall (0 : ℝ) R) :=
    Metric.isClosed_closedBall.measurableSet
  have hcomplset : (Metric.closedBall (0 : ℝ) R)ᶜ = {x : ℝ | R < ‖x‖} := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hcompl : μ (Metric.closedBall (0 : ℝ) R)ᶜ ≤ (1 / 4 : ℝ≥0∞) := by
    rw [hcomplset]
    exact hR
  -- Proof comment: tight tail control turns into a quantitative lower bound on the ball mass.
  have hsum : μ (Metric.closedBall (0 : ℝ) R) + μ (Metric.closedBall (0 : ℝ) R)ᶜ = 1 := by
    simpa using prob_add_prob_compl (μ := μ) hmeas
  have hsum_real :
      (μ (Metric.closedBall (0 : ℝ) R)).toReal + (μ (Metric.closedBall (0 : ℝ) R)ᶜ).toReal = 1 := by
    simpa [ENNReal.toReal_add, measure_ne_top μ _] using congrArg ENNReal.toReal hsum
  have hcompl_real : (μ (Metric.closedBall (0 : ℝ) R)ᶜ).toReal ≤ 1 / 4 := by
    simpa using ENNReal.toReal_mono (by simp) hcompl
  have hball_real : 1 / 2 < (μ (Metric.closedBall (0 : ℝ) R)).toReal := by
    linarith
  exact
    (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top μ _)).mp <| by
      simpa using hball_real

/-- Helper for Exercise 13.3.2: the Gaussian law assigns mass `1/2` to the left half-line ending
at its mean. -/
private lemma gaussianReal_Iic_mean {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v (Set.Iic μ) = (1 / 2 : ℝ≥0∞) := by
  have hcentered :
      gaussianReal (0 : ℝ) v (Set.Iic 0) = (1 / 2 : ℝ≥0∞) := by
    let ν : Measure ℝ := gaussianReal (0 : ℝ) v
    have hsymm :
        ν.map (fun x : ℝ ↦ -x) = ν := by
      simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
    have hIci :
        ν (Set.Ici 0) = ν (Set.Iic 0) := by
      calc
        ν (Set.Ici 0) = ν.map (fun x : ℝ ↦ -x) (Set.Ici 0) := by
          rw [hsymm]
        _ = ν (Set.Iic 0) := by
              rw [Measure.map_apply measurable_neg measurableSet_Ici]
              congr 1
              ext x
              simp
    have hnoAtoms : NoAtoms ν := noAtoms_gaussianReal hv
    have hIci_eq_Ioi :
        ν (Set.Ici 0) = ν (Set.Ioi 0) := by
      have hunion : Set.Ioi (0 : ℝ) ∪ ({(0 : ℝ)} : Set ℝ) = Set.Ici 0 := by
        ext x
        simp
      have hdisj : Disjoint (Set.Ioi (0 : ℝ)) ({(0 : ℝ)} : Set ℝ) := by
        rw [Set.disjoint_singleton_right]
        simp
      calc
        ν (Set.Ici 0) = ν (Set.Ioi 0 ∪ ({(0 : ℝ)} : Set ℝ)) := by
                rw [hunion]
        _ = ν (Set.Ioi 0) + ν ({(0 : ℝ)} : Set ℝ) := by
              rw [measure_union hdisj (measurableSet_singleton (x := (0 : ℝ)))]
        _ = ν (Set.Ioi 0) := by
              simp [hnoAtoms.measure_singleton]
    have hsum :
        ν (Set.Iic 0) + ν (Set.Ioi 0) = 1 := by
      simpa using prob_add_prob_compl (μ := ν) measurableSet_Iic
    have htwice :
        ν (Set.Iic 0) + ν (Set.Iic 0) = 1 := by
      calc
        ν (Set.Iic 0) + ν (Set.Iic 0)
            = ν (Set.Ici 0) + ν (Set.Iic 0) := by rw [hIci]
        _ = ν (Set.Ioi 0) + ν (Set.Iic 0) := by rw [hIci_eq_Ioi]
        _ = 1 := by simpa [add_comm] using hsum
    have htwice_real :
        2 * (ν (Set.Iic 0)).toReal = 1 := by
      have htmp :=
        congrArg ENNReal.toReal htwice
      simpa [ν, ENNReal.toReal_add, measure_ne_top (ν) _, two_mul] using htmp
    have hreal : (ν (Set.Iic 0)).toReal = 1 / 2 := by
      linarith
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν _) (by simp)).mp
      <| by
        simpa using hreal
  -- Shift the centered half-line statement from `0` to the mean `μ`.
  calc
    gaussianReal μ v (Set.Iic μ)
        = (gaussianReal μ v).map (fun x : ℝ ↦ x - μ) (Set.Iic 0) := by
            rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
            congr 1
            ext x
            simp
    _ = gaussianReal 0 v (Set.Iic 0) := by
          simpa using congrArg (fun ν : Measure ℝ ↦ ν (Set.Iic 0))
            (gaussianReal_map_sub_const (μ := μ) (v := v) μ)
    _ = (1 / 2 : ℝ≥0∞) := hcentered

/-- Helper for Exercise 13.3.2: on a centered interval of radius `R`, a Gaussian mass is bounded by
the interval length times the maximal height of its density. -/
private lemma gaussianReal_closedBall_mass_le_densityHeight {μ : ℝ} {v : ℝ≥0} {R : ℝ}
    (hR : 0 ≤ R) (hv : v ≠ 0) :
    gaussianReal μ v (Metric.closedBall (0 : ℝ) R) ≤
      ENNReal.ofReal (2 * R * (Real.sqrt (2 * Real.pi * v))⁻¹) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹
  have hpoint :
      ∀ x : ℝ, gaussianPDF μ v x ≤ ENNReal.ofReal c := by
    intro x
    rw [gaussianPDF_def, gaussianPDFReal_def]
    refine ENNReal.ofReal_le_ofReal ?_
    have hvpos : 0 < (v : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.mpr hv
    have hneg : -(x - μ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
      have hnum : -(x - μ) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (x - μ)]
      have hden : 0 ≤ 2 * (v : ℝ) := by
        positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum hden
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hexp : Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr hneg
    have hmul : c * Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ c * 1 := by
      exact mul_le_mul_of_nonneg_left hexp hc_nonneg
    simpa [c] using hmul
  -- Bound the Gaussian mass by a constant density over the enclosing interval.
  have htwoR_nonneg : 0 ≤ 2 * R := by
    nlinarith
  rw [Real.closedBall_zero_eq_Icc, gaussianReal_apply _ hv]
  calc
    ∫⁻ x in Set.Icc (-R) R, gaussianPDF μ v x ≤ ∫⁻ _ in Set.Icc (-R) R, ENNReal.ofReal c := by
      refine lintegral_mono fun x ↦ hpoint x
    _ = ENNReal.ofReal c * volume (Set.Icc (-R) R) := setLIntegral_const _ _
    _ = ENNReal.ofReal c * ENNReal.ofReal (2 * R) := by
          rw [Real.volume_Icc]
          congr 1
          ring_nf
    _ = ENNReal.ofReal (c * (2 * R)) := by
          rw [mul_comm c (2 * R), ENNReal.ofReal_mul htwoR_nonneg, mul_comm]
    _ = ENNReal.ofReal (2 * R * (Real.sqrt (2 * Real.pi * v))⁻¹) := by
          congr 1
          simp [c, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 13.3.2: the Gaussian second moment in `ENNReal` is `μ^2 + v`. -/
private lemma gaussianReal_lintegral_sq {μ : ℝ} {v : ℝ≥0} :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂gaussianReal μ v = ENNReal.ofReal (μ ^ 2 + v) := by
  have hmem : MemLp id 2 (gaussianReal μ v) :=
    memLp_id_gaussianReal' (μ := μ) (v := v) 2 (by simp)
  have hint : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal μ v) := hmem.integrable_sq
  have hsecond :
      ∫ x, x ^ 2 ∂gaussianReal μ v = μ ^ 2 + v := by
    have hvar :
        Var[id; gaussianReal μ v] =
          ∫ x, x ^ 2 ∂gaussianReal μ v - (∫ x, x ∂gaussianReal μ v) ^ 2 := by
      simpa using (variance_eq_sub (μ := gaussianReal μ v) (X := id) hmem)
    have hrewrite :
        ∫ x, x ^ 2 ∂gaussianReal μ v =
          Var[id; gaussianReal μ v] + (∫ x, x ∂gaussianReal μ v) ^ 2 := by
      linarith
    calc
      ∫ x, x ^ 2 ∂gaussianReal μ v
          = Var[id; gaussianReal μ v] + (∫ x, x ∂gaussianReal μ v) ^ 2 := hrewrite
      _ = v + μ ^ 2 := by rw [variance_id_gaussianReal, integral_id_gaussianReal]
      _ = μ ^ 2 + v := by ring_nf
  -- Rewrite the nonnegative real integral as a `lintegral` of `ENNReal.ofReal`.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
  · simpa using congrArg ENNReal.ofReal hsecond
  · exact ae_of_all _ fun x ↦ sq_nonneg x

/-- Helper for Exercise 13.3.2: Markov's inequality and the Gaussian second moment control the
norm tail of `gaussianReal μ v`. -/
private lemma gaussianReal_norm_tail_le_secondMoment {μ : ℝ} {v : ℝ≥0} {r : ℝ}
    (hr : 0 < r) :
    gaussianReal μ v {x : ℝ | r < ‖x‖} ≤ ENNReal.ofReal ((μ ^ 2 + v) / r ^ 2) := by
  have hsq_meas :
      AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ 2)) (gaussianReal μ v) := by
    fun_prop
  have hmarkov :
      gaussianReal μ v {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (x ^ 2)} ≤
        (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂gaussianReal μ v) / ENNReal.ofReal (r ^ 2) := by
    exact
      MeasureTheory.meas_ge_le_lintegral_div hsq_meas
        (by positivity)
        ENNReal.ofReal_ne_top
  have hsubset :
      {x : ℝ | r < ‖x‖} ⊆ {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (x ^ 2)} := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hnorm : r < |x| := by
      simpa [Real.norm_eq_abs] using hx
    have hsq : r ^ 2 < |x| ^ 2 := by
      nlinarith [hr.le, abs_nonneg x, hnorm]
    simpa [sq_abs] using le_of_lt hsq
  -- Proof comment: the tail event sits inside the quadratic superlevel set used by Markov.
  calc
    gaussianReal μ v {x : ℝ | r < ‖x‖}
        ≤ gaussianReal μ v {x : ℝ | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (x ^ 2)} :=
          measure_mono hsubset
    _ ≤ (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂gaussianReal μ v) / ENNReal.ofReal (r ^ 2) := hmarkov
    _ = ENNReal.ofReal ((μ ^ 2 + v) / r ^ 2) := by
          rw [gaussianReal_lintegral_sq, ENNReal.ofReal_div_of_pos]
          positivity

/-- Helper for Exercise 13.3.2: tightness of the Gaussian image family yields one positive radius
with uniform `1/4` tail control. -/
private lemma existsUniformQuarterTailRadius
    {L : Set (ℝ × Set.Ioi (0 : ℝ≥0))}
    (htight : IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L)) :
    ∃ R > 0, ∀ p ∈ L, gaussianReal p.1 p.2 {x : ℝ | R < ‖x‖} ≤ (1 / 4 : ℝ≥0∞) := by
  have htail :
      Tendsto
        (fun r : ℝ ↦
          ⨆ ν ∈ ((fun p ↦ gaussianReal p.1 p.2) '' L), ν {x : ℝ | r < ‖x‖})
        atTop (𝓝 0) :=
    (MeasureTheory.isTightMeasureSet_iff_tendsto_measure_norm_gt).mp htight
  rw [ENNReal.tendsto_atTop_zero] at htail
  obtain ⟨R0, hR0⟩ := htail (1 / 4 : ℝ≥0∞) (by norm_num)
  refine ⟨max 1 R0, by positivity, ?_⟩
  intro p hp
  -- Proof comment: monotonicity in the radius transfers the witness from `R0` to `max 1 R0`.
  refine le_trans ?_ (hR0 (max 1 R0) (le_max_right _ _))
  exact le_iSup_of_le (gaussianReal p.1 p.2) <| le_iSup_of_le ⟨p, hp, rfl⟩ le_rfl

/-- Helper for Exercise 13.3.2: if more than half of a Gaussian mass lies in
`Metric.closedBall 0 R`, then its mean must also lie in that ball. -/
private lemma abs_mean_le_radius_of_closedBallMass_gt_half {μ : ℝ} {v : ℝ≥0} {R : ℝ}
    (hv : v ≠ 0)
    (hmass : (1 / 2 : ℝ≥0∞) < gaussianReal μ v (Metric.closedBall (0 : ℝ) R)) :
    |μ| ≤ R := by
  have hμ_le : μ ≤ R := by
    by_contra hgt
    have hμ_gt : R < μ := lt_of_not_ge hgt
    have hsubset : Metric.closedBall (0 : ℝ) R ⊆ Set.Iic μ := by
      intro x hx
      have hxabs : |x| ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hxle : x ≤ R := (abs_le.mp hxabs).2
      exact le_trans hxle hμ_gt.le
    have hle :
        gaussianReal μ v (Metric.closedBall (0 : ℝ) R) ≤ gaussianReal μ v (Set.Iic μ) :=
      measure_mono hsubset
    exact not_lt_of_ge (le_trans hle (le_of_eq (gaussianReal_Iic_mean hv))) hmass
  have hμ_ge : -R ≤ μ := by
    by_contra hlt
    have hμ_lt : μ < -R := lt_of_not_ge hlt
    have hsubset : Metric.closedBall (0 : ℝ) R ⊆ (Set.Iic μ)ᶜ := by
      intro x hx
      have hxabs : |x| ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hxge : -R ≤ x := (abs_le.mp hxabs).1
      have hxgt : μ < x := lt_of_lt_of_le hμ_lt hxge
      exact fun hxIic ↦ not_lt_of_ge hxIic hxgt
    have hIoi :
        gaussianReal μ v (Set.Iic μ)ᶜ = (1 / 2 : ℝ≥0∞) := by
      rw [
        measure_compl measurableSet_Iic (measure_ne_top (gaussianReal μ v) _),
        gaussianReal_Iic_mean hv
      ]
      norm_num
    have hle :
        gaussianReal μ v (Metric.closedBall (0 : ℝ) R) ≤ gaussianReal μ v (Set.Iic μ)ᶜ :=
      measure_mono hsubset
    exact not_lt_of_ge (le_trans hle (le_of_eq hIoi)) hmass
  -- Proof comment: combining the two one-sided bounds yields the desired absolute-value estimate.
  exact abs_le.mpr ⟨hμ_ge, hμ_le⟩

/-- Helper for Exercise 13.3.2: if more than half of a Gaussian mass lies in
`Metric.closedBall 0 R`, then the variance parameter is bounded in terms of `R`. -/
private lemma variance_le_of_closedBallMass_gt_half {μ : ℝ} {v : ℝ≥0} {R : ℝ}
    (hR : 0 < R) (hv : v ≠ 0)
    (hmass : (1 / 2 : ℝ≥0∞) < gaussianReal μ v (Metric.closedBall (0 : ℝ) R)) :
    (v : ℝ) ≤ (8 / Real.pi) * R ^ 2 := by
  have hupper :=
    gaussianReal_closedBall_mass_le_densityHeight (μ := μ) (v := v) hR.le hv
  have hmass_real : (1 / 2 : ℝ) < (gaussianReal μ v (Metric.closedBall (0 : ℝ) R)).toReal := by
    simpa using
      (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top (gaussianReal μ v) _)).2 hmass
  have hupper_real :
      (gaussianReal μ v (Metric.closedBall (0 : ℝ) R)).toReal ≤
        2 * R / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    have hdensity_nonneg : 0 ≤ 2 * R * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
      positivity
    have hupper_toReal :
        (gaussianReal μ v (Metric.closedBall (0 : ℝ) R)).toReal ≤
          (ENNReal.ofReal (2 * R * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    rw [ENNReal.toReal_ofReal hdensity_nonneg] at hupper_toReal
    simpa [div_eq_mul_inv] using hupper_toReal
  have hineq : (1 / 2 : ℝ) < 2 * R / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    exact lt_of_lt_of_le hmass_real hupper_real
  have hsqrt_sq : Real.sqrt (2 * Real.pi * (v : ℝ)) ^ 2 = 2 * Real.pi * (v : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    positivity
  have hmul : Real.sqrt (2 * Real.pi * (v : ℝ)) < 4 * R := by
    have htmp : (1 / 2 : ℝ) * Real.sqrt (2 * Real.pi * (v : ℝ)) < 2 * R := by
      exact (lt_div_iff₀ hsqrt_pos).mp hineq
    nlinarith
  -- Proof comment: square the density-height inequality once and solve the
  -- remaining real arithmetic.
  have hsq_lt : 2 * Real.pi * (v : ℝ) < 16 * R ^ 2 := by
    nlinarith [hsqrt_sq, hsqrt_pos, hR, hmul]
  by_contra hgt
  have hgt' : (8 / Real.pi) * R ^ 2 < (v : ℝ) := lt_of_not_ge hgt
  have hscaled :
      16 * R ^ 2 < 2 * Real.pi * (v : ℝ) := by
    have hmul_lt := mul_lt_mul_of_pos_left hgt' (show 0 < 2 * Real.pi by positivity)
    have hcoeff : 2 * Real.pi * ((8 / Real.pi) * R ^ 2) = 16 * R ^ 2 := by
      field_simp [Real.pi_ne_zero]
      ring_nf
    calc
      16 * R ^ 2 = 2 * Real.pi * ((8 / Real.pi) * R ^ 2) := by
        rw [hcoeff]
      _ < 2 * Real.pi * (v : ℝ) := hmul_lt
  exact (not_lt_of_ge hsq_lt.le) hscaled

/-- Helper for Exercise 13.3.2: bounds on the mean and variance coordinates give a uniform bound
for the Gaussian second moment. -/
private lemma parameterSecondMoment_le_of_memClosedBalls
    {μ M : ℝ} {v : ℝ≥0} {V : ℝ}
    (hμ : μ ∈ Metric.closedBall (0 : ℝ) M)
    (hv : v ∈ Metric.closedBall (0 : ℝ≥0) V) :
    μ ^ 2 + (v : ℝ) ≤ M ^ 2 + V := by
  have habs : |μ| ≤ M := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hμ
  have hMnonneg : 0 ≤ M := le_trans (abs_nonneg μ) habs
  have hμsq : μ ^ 2 ≤ M ^ 2 := by
    exact sq_le_sq.mpr <| by simpa [abs_of_nonneg hMnonneg] using habs
  have hVnonneg : 0 ≤ V := by
    have hdist_nonneg : 0 ≤ dist v 0 := dist_nonneg
    have hdist_le : dist v 0 ≤ V := by
      simpa [Metric.mem_closedBall] using hv
    exact le_trans hdist_nonneg hdist_le
  have hv_le : (v : ℝ) ≤ V := by
    have hdist_le : dist v 0 ≤ V := by
      simpa [Metric.mem_closedBall] using hv
    simpa [NNReal.dist_eq, abs_of_nonneg v.2] using hdist_le
  -- Proof comment: after normalizing both coordinates to real inequalities, the
  -- second-moment bound is a single arithmetic step.
  nlinarith

/-- Helper for Exercise 13.3.2: coordinate bounds give a uniform Gaussian norm-tail estimate via
the second-moment bound. -/
private lemma gaussianReal_normTail_le_of_coordinateBounds
    {μ M : ℝ} {v : ℝ≥0} {V r : ℝ}
    (hr : 0 < r)
    (hμ : μ ∈ Metric.closedBall (0 : ℝ) M)
    (hv : v ∈ Metric.closedBall (0 : ℝ≥0) V) :
    gaussianReal μ v {x : ℝ | r < ‖x‖} ≤ ENNReal.ofReal ((M ^ 2 + V) / r ^ 2) := by
  have hsecond :
      μ ^ 2 + (v : ℝ) ≤ M ^ 2 + V :=
    parameterSecondMoment_le_of_memClosedBalls hμ hv
  -- Proof comment: the parameter-wise Markov bound becomes uniform once the
  -- second moments are all controlled by the same envelope.
  calc
    gaussianReal μ v {x : ℝ | r < ‖x‖}
        ≤ ENNReal.ofReal ((μ ^ 2 + v) / r ^ 2) :=
          gaussianReal_norm_tail_le_secondMoment hr
    _ ≤ ENNReal.ofReal ((M ^ 2 + V) / r ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact div_le_div_of_nonneg_right hsecond (sq_nonneg r)

/-- Helper for Exercise 13.3.2: bounded Gaussian parameters yield an eventual uniform bound on the
supremum of the norm tails of the family. -/
private lemma eventually_uniformGaussianTailSup_le_of_isBounded
    {L : Set (ℝ × Set.Ioi (0 : ℝ≥0))} {M V : ℝ}
    (hM : Prod.fst '' L ⊆ Metric.closedBall (0 : ℝ) M)
    (hV : Subtype.val '' (Prod.snd '' L) ⊆ Metric.closedBall (0 : ℝ≥0) V) :
    ∀ᶠ r : ℝ in atTop,
      (⨆ ν ∈ ((fun p ↦ gaussianReal p.1 p.2) '' L), ν {x : ℝ | r < ‖x‖})
        ≤ ENNReal.ofReal ((M ^ 2 + V) / r ^ 2) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := by
    linarith
  refine iSup₂_le fun ν hν ↦ ?_
  rcases hν with ⟨p, hp, rfl⟩
  have hμ_mem : p.1 ∈ Metric.closedBall (0 : ℝ) M :=
    hM ⟨p, hp, rfl⟩
  have hσ_mem : ((p.2 : Set.Ioi (0 : ℝ≥0)) : ℝ≥0) ∈ Metric.closedBall (0 : ℝ≥0) V :=
    hV ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩
  -- Proof comment: each measure in the image family inherits the same
  -- coordinate bounds, so the pointwise tail estimate upgrades to the supremum.
  exact gaussianReal_normTail_le_of_coordinateBounds hrpos hμ_mem hσ_mem

/-- Helper for Exercise 13.3.2: tightness of the Gaussian image family forces the parameter set to
be bounded. -/
private lemma gaussianRealImage_isBounded_of_isTightMeasureSet
    {L : Set (ℝ × Set.Ioi (0 : ℝ≥0))}
    (htight : IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L)) :
    Bornology.IsBounded L := by
  obtain ⟨R, hRpos, htailR⟩ := existsUniformQuarterTailRadius (L := L) htight
  have hmeanBound :
      Bornology.IsBounded (Prod.fst '' L) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).2 ⟨R, ?_⟩
    intro μ hμ
    rcases hμ with ⟨p, hp, rfl⟩
    have hmass :
        (1 / 2 : ℝ≥0∞) < gaussianReal p.1 p.2 (Metric.closedBall (0 : ℝ) R) :=
      one_half_lt_measure_closedBall_of_measure_norm_gt_lt_quarter
        (μ := gaussianReal p.1 p.2) (htailR p hp)
    -- Proof comment: the separate mean-control helper removes both contradiction branches
    -- from the theorem body.
    have habs : |p.1| ≤ R :=
      abs_mean_le_radius_of_closedBallMass_gt_half (μ := p.1) (v := p.2) p.2.2.ne' hmass
    simpa [Metric.mem_closedBall, dist_zero_right] using habs
  have hvarianceBound :
      Bornology.IsBounded (Subtype.val '' (Prod.snd '' L)) := by
    let V : ℝ := (8 / Real.pi) * R ^ 2
    have hVnonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ≥0)).2 ⟨V, ?_⟩
    intro σ2 hσ2
    rcases hσ2 with ⟨σ, hσ, rfl⟩
    rcases hσ with ⟨p, hp, rfl⟩
    have hmass :
        (1 / 2 : ℝ≥0∞) < gaussianReal p.1 p.2 (Metric.closedBall (0 : ℝ) R) :=
      one_half_lt_measure_closedBall_of_measure_norm_gt_lt_quarter
        (μ := gaussianReal p.1 p.2) (htailR p hp)
    have hvar_le : (p.2 : ℝ) ≤ V := by
      simpa [V] using
        variance_le_of_closedBallMass_gt_half (μ := p.1) (v := p.2) hRpos p.2.2.ne' hmass
    have hmem : (p.2 : ℝ≥0) ∈ Metric.closedBall (0 : ℝ≥0) V := by
      rw [NNReal.closedBall_zero_eq_Icc hVnonneg]
      · refine ⟨by simp, ?_⟩
        simpa [Real.toNNReal, hVnonneg] using hvar_le
    simpa using hmem
  have hvarianceSubtype : Bornology.IsBounded (Prod.snd '' L) :=
    (Bornology.isBounded_image_subtype_val).1 hvarianceBound
  exact (Bornology.isBounded_image_fst_and_snd).1 ⟨hmeanBound, hvarianceSubtype⟩

/-- Helper for Exercise 13.3.2: bounded Gaussian parameters yield a tight image family. -/
private lemma isTightMeasureSet_gaussianReal_image_of_isBounded
    {L : Set (ℝ × Set.Ioi (0 : ℝ≥0))}
    (hbounded : Bornology.IsBounded L) :
    IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L) := by
  have hcoords := (Bornology.isBounded_image_fst_and_snd).2 hbounded
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcoords.1
  have hsndBounded :
      Bornology.IsBounded (Subtype.val '' (Prod.snd '' L)) :=
    (Bornology.isBounded_image_subtype_val).2 hcoords.2
  obtain ⟨V, hV⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ≥0)).1 hsndBounded
  -- Proof comment: use the tightness criterion via norm tails, with the
  -- uniform second-moment bound supplied by the coordinate estimates.
  have hupper_tendsto :
      Tendsto (fun r : ℝ ↦ ENNReal.ofReal ((M ^ 2 + V) / r ^ 2)) atTop (𝓝 0) := by
    have hreal :
        Tendsto (fun r : ℝ ↦ (M ^ 2 + V) / r ^ 2) atTop (𝓝 0) := by
      simpa using
        (Tendsto.div_atTop tendsto_const_nhds
          (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
    simpa using ENNReal.tendsto_ofReal hreal
  refine MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto ?_ ?_
  · exact Filter.Eventually.of_forall fun r ↦ by positivity
  -- Proof comment: the helper turns coordinate boundedness into the uniform
  -- eventual tail bound required by the tightness criterion.
  · exact eventually_uniformGaussianTailSup_le_of_isBounded hM hV

/-- Exercise 13.3.2: the family of normal distributions with parameter set `L ⊆ ℝ × (0, ∞)` is
tight if and only if the parameter set `L` is bounded. -/
theorem isTightMeasureSet_gaussianReal_image_iff_isBounded
    (L : Set (ℝ × Set.Ioi (0 : ℝ≥0))) :
    IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L) ↔
      Bornology.IsBounded L := by
  constructor
  · exact gaussianRealImage_isBounded_of_isTightMeasureSet
  · exact isTightMeasureSet_gaussianReal_image_of_isBounded
