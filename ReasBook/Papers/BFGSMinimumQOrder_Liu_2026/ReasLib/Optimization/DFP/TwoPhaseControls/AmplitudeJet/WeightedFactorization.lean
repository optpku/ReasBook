module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.WeightedStability
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.WeightedPerturbation
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseNormBoundFinal
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseNormBoundFinal
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Analytic coordinate factorization for the second-leg amplitude. -/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- The second-leg low gradient factor, viewed as a scalar function on parameter triples. -/
def secondLegAmplitude (x : ℝ × ℝ × ℝ) : ℝ :=
  (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).1

/-- The named amplitude function is definitionally the public low gradient factor. -/
theorem secondLegAmplitude_eq_gradientFactor (ε p h : ℝ) :
    secondLegAmplitude (ε, p, h) =
      (DFP.SecondLeg.gradientFactors ε p h).1 := by
  rfl

/-- The second-leg amplitude is real analytic at the canceled base point `(0, 2, 1)`. -/
theorem secondLegAmplitude_analyticAt :
    AnalyticAt ℝ secondLegAmplitude (0, 2, 1) := by
  have hgradientRaw : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
    have h := (analyticAt_fst.comp analyticAt_snd).comp DFP.SecondLeg.factorsAnalytic
    have heq :
        ((fun x : ℝ × ℝ × ℝ ↦
          (DFP.SecondLeg.factors x.1 x.2.1 x.2.2).2.1)) =ᶠ[𝓝 (0, 2, 1)]
          (fun x : ℝ × ℝ × ℝ ↦
            DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2) := by
      filter_upwards [] with x
      rfl
    exact h.congr heq
  have hgradient := hgradientRaw
  have hlow := analyticAt_fst.comp hgradient
  have heqLow :
      ((fun x : ℝ × ℝ × ℝ ↦
        (DFP.SecondLeg.gradientFactors x.1 x.2.1 x.2.2).1)) =ᶠ[𝓝 (0, 2, 1)]
        secondLegAmplitude := by
    filter_upwards [] with x
    rfl
  exact hlow.congr heqLow

/-- The second-leg amplitude has normalized base value one. -/
theorem secondLegAmplitude_base : secondLegAmplitude (0, 2, 1) = 1 := by
  have hbase := congrArg (fun z ↦ z.2.1.1) DFP.SecondLeg.factorsBase
  simpa only [secondLegAmplitude, DFP.SecondLeg.factors] using hbase

/-- At zero signed scale, the second-leg amplitude is constant on the positive slice. -/
private theorem secondLegAmplitude_zeroScale (p h : ℝ) (hp : 0 < p) :
    secondLegAmplitude (0, p, h) = 1 := by
  -- Reuse the owner-level zero-scale cancellation rather than expanding the update here.
  rw [secondLegAmplitude_eq_gradientFactor]
  exact DFP.SecondLeg.gradientFactors_low_zeroScale p h hp

/-- The low gradient factor is nonzero on some neighborhood of the canceled base point. -/
theorem eventually_secondLegAmplitude_ne_zero :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), secondLegAmplitude x ≠ 0 := by
  apply secondLegAmplitude_analyticAt.continuousAt.eventually_ne
  simpa only [secondLegAmplitude_base] using (one_ne_zero : (1 : ℝ) ≠ 0)

/-- Along a path converging to `(0, 2, 1)`, the observable amplitude is the named low factor. -/
theorem observableMap_amplitude_eq_secondLegAmplitude_eventually
    (p h : ℝ → ℝ)
    (hpath : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ))) :
    ∀ᶠ ε in 𝓝 0,
      (observableMap (ε, p ε, h ε)).amplitudeRatio =
        secondLegAmplitude (ε, p ε, h ε) := by
  have hfactorization := hpath.eventually DFP.SecondLeg.gradientFactorization
  filter_upwards [hfactorization] with ε hε
  rw [observableMap_amplitudeRatio]
  have hv := hε 1
  simp only [one_smul] at hv
  unfold DFP.SecondLeg.coordinates
  exact congrArg (fun v : Fin 2 → ℝ ↦ v 0) hv

/-- The shape coordinate of the polynomial slow graph. -/
def slowGraphAmplitudeP (ε : ℝ) : ℝ := (slowGraphJetPath ε).2.1

/-- The shape coordinate of the slow graph is the cubic-quartic polynomial shown by its path. -/
theorem slowGraphAmplitudeP_apply (ε : ℝ) :
    slowGraphAmplitudeP ε = 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4 := by
  simp only [slowGraphAmplitudeP, slowGraphJetPath_apply]

/-- The high coordinate of the polynomial slow graph. -/
def slowGraphAmplitudeH (ε : ℝ) : ℝ := (slowGraphJetPath ε).2.2

/-- The high coordinate of the slow graph is the cubic polynomial shown by its path. -/
theorem slowGraphAmplitudeH_apply (ε : ℝ) :
    slowGraphAmplitudeH ε = 1 + 8 * ε ^ 3 := by
  simp only [slowGraphAmplitudeH, slowGraphJetPath_apply]

/-- The shape divided difference records the amplitude change in the shape coordinate. -/
def secondLegAmplitudeShapeCoefficient (p h : ℝ → ℝ) (ε : ℝ) : ℝ :=
  if ε = 0 then 0 else
    (secondLegAmplitude (ε, p ε, h ε) -
      secondLegAmplitude (slowGraphJetPath ε)) *
      (p ε - slowGraphAmplitudeP ε) /
      (ε ^ 3 * ((p ε - slowGraphAmplitudeP ε) ^ 2 +
        (h ε - slowGraphAmplitudeH ε) ^ 2))

/-- The high-coordinate divided difference records the amplitude change in the high coordinate. -/
def secondLegAmplitudeHighCoefficient (p h : ℝ → ℝ) (ε : ℝ) : ℝ :=
  if ε = 0 then 0 else
    (secondLegAmplitude (ε, p ε, h ε) -
      secondLegAmplitude (slowGraphJetPath ε)) *
      (h ε - slowGraphAmplitudeH ε) /
      (ε ^ 3 * ((p ε - slowGraphAmplitudeP ε) ^ 2 +
        (h ε - slowGraphAmplitudeH ε) ^ 2))

/-- The two divided differences reconstruct the amplitude change along a fifth-order path. -/
theorem secondLegAmplitude_coordinateEquality (p h : ℝ → ℝ)
    (hp0 : p 0 = 2) (hh0 : h 0 = 1) :
    ∀ ε, secondLegAmplitude (ε, p ε, h ε) -
      secondLegAmplitude (slowGraphJetPath ε) =
        ε ^ 3 * (secondLegAmplitudeShapeCoefficient p h ε *
          (p ε - slowGraphAmplitudeP ε) +
          secondLegAmplitudeHighCoefficient p h ε *
          (h ε - slowGraphAmplitudeH ε)) := by
  intro ε
  by_cases hε : ε = 0
  · subst ε
    have hP : slowGraphAmplitudeP 0 = 2 := by
      rw [slowGraphAmplitudeP_apply]
      norm_num
    have hH : slowGraphAmplitudeH 0 = 1 := by
      rw [slowGraphAmplitudeH_apply]
      norm_num
    have hpath : slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      rw [slowGraphJetPath_apply]
      norm_num
    rw [hpath, hP, hH, hp0, hh0]
    simp [secondLegAmplitudeShapeCoefficient, secondLegAmplitudeHighCoefficient]
  · let dp : ℝ := p ε - slowGraphAmplitudeP ε
    let dh : ℝ := h ε - slowGraphAmplitudeH ε
    let δ : ℝ := secondLegAmplitude (ε, p ε, h ε) -
      secondLegAmplitude (slowGraphJetPath ε)
    by_cases hsum : dp ^ 2 + dh ^ 2 = 0
    · have hdp : dp = 0 := by nlinarith [sq_nonneg dp, sq_nonneg dh]
      have hdh : dh = 0 := by nlinarith [sq_nonneg dp, sq_nonneg dh]
      have hpeq : p ε = slowGraphAmplitudeP ε := sub_eq_zero.mp hdp
      have hheq : h ε = slowGraphAmplitudeH ε := sub_eq_zero.mp hdh
      have hpath : slowGraphJetPath ε =
          (ε, slowGraphAmplitudeP ε, slowGraphAmplitudeH ε) := by
        rw [slowGraphJetPath_apply]
        simp only [slowGraphAmplitudeP_apply, slowGraphAmplitudeH_apply]
      rw [hpath, hpeq, hheq]
      simp only [sub_self, mul_zero, add_zero]
    · have hformula : δ = ε ^ 3 *
          (δ * dp / (ε ^ 3 * (dp ^ 2 + dh ^ 2)) * dp +
            δ * dh / (ε ^ 3 * (dp ^ 2 + dh ^ 2)) * dh) := by
        field_simp [hε, hsum]
      simpa only [secondLegAmplitudeShapeCoefficient,
        secondLegAmplitudeHighCoefficient, if_neg hε, dp, dh, δ] using hformula

/-- The product norm times the shape defect is controlled by the quadratic defect energy. -/
private lemma max_abs_mul_left_le_sq_add_sq (a b : ℝ) :
    max |a| |b| * |a| ≤ a ^ 2 + b ^ 2 := by
  by_cases hab : |a| ≤ |b|
  · -- When the high defect dominates, the cross term is controlled by `( |a| - |b| )²`.
    rw [max_eq_right hab]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  · -- When the shape defect dominates, the left-hand side is exactly `a²`.
    have hba : |b| ≤ |a| := le_of_not_ge hab
    rw [max_eq_left hba]
    nlinarith [sq_nonneg b, sq_abs a]

/-- The product norm times the high defect is controlled by the quadratic defect energy. -/
private lemma max_abs_mul_right_le_sq_add_sq (a b : ℝ) :
    max |a| |b| * |b| ≤ a ^ 2 + b ^ 2 := by
  by_cases hab : |b| ≤ |a|
  · -- When the shape defect dominates, the cross term is controlled by `( |a| - |b| )²`.
    rw [max_eq_left hab]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  · -- When the high defect dominates, the left-hand side is exactly `b²`.
    have hba : |a| ≤ |b| := le_of_not_ge hab
    rw [max_eq_right hba]
    nlinarith [sq_nonneg a, sq_abs b]

/-- At zero scale, the amplitude has vanishing transverse derivative at every point
of the positive slice. -/
private lemma secondLegAmplitudeZeroScaleTransverseFDeriv (p h : ℝ) (hp : 0 < p) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ secondLegAmplitude (0, z.1, z.2)) (p, h) = 0 := by
  -- Positivity of the first transverse coordinate persists on a neighborhood.
  have hpos : ∀ᶠ z : ℝ × ℝ in 𝓝 (p, h), 0 < z.1 := by
    have hc : ContinuousAt (fun z : ℝ × ℝ ↦ z.1) (p, h) := continuousAt_fst
    exact hc.eventually (Ioi_mem_nhds hp)
  have hconst :
      (fun z : ℝ × ℝ ↦ secondLegAmplitude (0, z.1, z.2)) =ᶠ[𝓝 (p, h)]
        (fun _ : ℝ × ℝ ↦ (1 : ℝ)) := by
    filter_upwards [hpos] with z hz
    exact secondLegAmplitude_zeroScale z.1 z.2 hz
  rw [hconst.fderiv_eq]
  simp

/-- Lemma 4.15 (Near-return winding number is nonzero): the amplitude defect is cubic in the
signed scale and linear in the transverse defect. -/
private theorem secondLegAmplitude_sub_slowGraph_isBigO_weightedTransverse
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦ p ε - slowGraphAmplitudeP ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - slowGraphAmplitudeH ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3 *
        ‖(p ε - slowGraphAmplitudeP ε, h ε - slowGraphAmplitudeH ε)‖) := by
  -- Route correction: expose the transverse endpoint paths first, so the final
  -- weighted estimate can consume the actual product-space norm in the target.
  let u : ℝ → ℝ × ℝ := fun ε ↦ (p ε, h ε)
  let v : ℝ → ℝ × ℝ := fun ε ↦
    (slowGraphAmplitudeP ε, slowGraphAmplitudeH ε)
  have huv : (fun ε ↦ u ε - v ε) =O[𝓝 0]
      (fun ε ↦ ‖u ε - v ε‖) := by
    exact Asymptotics.isBigO_norm_right.mpr
      (Asymptotics.isBigO_refl (fun ε ↦ u ε - v ε) (𝓝 0))
  -- The analytic slice supplies differentiability on the joining segment.  The
  -- quantitative `ε ^ 3` derivative bound is the missing owner-level bridge.
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    simpa using hcont.tendsto
  have hPcont : ContinuousAt slowGraphAmplitudeP 0 := by
    have hpoly : ContinuousAt
        (fun ε : ℝ ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4) 0 := by
      fun_prop
    apply hpoly.congr_of_eventuallyEq
    filter_upwards [] with ε
    exact slowGraphAmplitudeP_apply ε
  have hHcont : ContinuousAt slowGraphAmplitudeH 0 := by
    have hpoly : ContinuousAt (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) 0 := by
      fun_prop
    apply hpoly.congr_of_eventuallyEq
    filter_upwards [] with ε
    exact slowGraphAmplitudeH_apply ε
  have hP0 : slowGraphAmplitudeP 0 = 2 := by
    rw [slowGraphAmplitudeP_apply]
    norm_num
  have hH0 : slowGraphAmplitudeH 0 = 1 := by
    rw [slowGraphAmplitudeH_apply]
    norm_num
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add, hP0] using
      (hp.trans_tendsto hpowFive).add hPcont.tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add, hH0] using
      (hh.trans_tendsto hpowFive).add hHcont.tendsto
  have huTendsto : Tendsto u (𝓝 0) (𝓝 (2, 1)) := by
    simpa only [u, nhds_prod_eq] using hpTendsto.prodMk hhTendsto
  have hvTendsto : Tendsto v (𝓝 0) (𝓝 (2, 1)) := by
    simpa only [v, hP0, hH0, nhds_prod_eq] using
      hPcont.tendsto.prodMk hHcont.tendsto
  obtain ⟨r, hr, hball⟩ :=
    secondLegAmplitude_analyticAt.exists_ball_analyticOnNhd
  have hu3 : Tendsto (fun ε : ℝ ↦ (ε, (u ε).1, (u ε).2)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [id_eq, nhds_prod_eq] using tendsto_id.prodMk huTendsto
  have hv3 : Tendsto (fun ε : ℝ ↦ (ε, (v ε).1, (v ε).2)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [id_eq, nhds_prod_eq] using tendsto_id.prodMk hvTendsto
  have huBall : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (ε, (u ε).1, (u ε).2) ∈ Metric.ball (0, 2, 1) r := by
    exact hu3.eventually (Metric.ball_mem_nhds _ hr)
  have hvBall : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (ε, (v ε).1, (v ε).2) ∈ Metric.ball (0, 2, 1) r := by
    exact hv3.eventually (Metric.ball_mem_nhds _ hr)
  have hdiff : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ z ∈ segment ℝ (v ε) (u ε),
        DifferentiableAt ℝ
          (fun z : ℝ × ℝ ↦ secondLegAmplitude (ε, z.1, z.2)) z := by
    filter_upwards [huBall, hvBall] with ε hu hv z hz
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, htz⟩
    subst z
    have hline := lineMap_mem_segment ℝ
      ((ε, (v ε).1, (v ε).2)) ((ε, (u ε).1, (u ε).2)) ht
    have hline' :
        ((1 - t) • (ε, (v ε).1, (v ε).2) +
          t • (ε, (u ε).1, (u ε).2)) ∈
          segment ℝ ((ε, (v ε).1, (v ε).2))
            ((ε, (u ε).1, (u ε).2)) := by
      simpa only [AffineMap.lineMap_apply_module] using hline
    have hzBall :
        ((1 - t) • (ε, (v ε).1, (v ε).2) +
          t • (ε, (u ε).1, (u ε).2)) ∈ Metric.ball (0, 2, 1) r :=
      (convex_ball _ _).segment_subset hv hu hline'
    have hpoint :
        (ε, ((1 - t) • v ε + t • u ε).1,
          ((1 - t) • v ε + t • u ε).2) =
          ((1 - t) • (ε, (v ε).1, (v ε).2) +
            t • (ε, (u ε).1, (u ε).2)) := by
      ext
      · simp
        ring
      · simp
      · simp
    have hballz : AnalyticAt ℝ secondLegAmplitude
        (ε, ((1 - t) • v ε + t • u ε).1,
          ((1 - t) • v ε + t • u ε).2) := by
      rw [hpoint]
      exact hball _ hzBall
    have hins : AnalyticAt ℝ
        (fun z : ℝ × ℝ ↦ (ε, z.1, z.2))
        ((1 - t) • v ε + t • u ε) :=
      (analyticAt_const (v := ε)
        (x := (1 - t) • v ε + t • u ε)).prod
        (analyticAt_fst.prod analyticAt_snd)
    have hcomp := hballz.comp hins
    have hcomp' : AnalyticAt ℝ
        (fun z : ℝ × ℝ ↦ secondLegAmplitude (ε, z.1, z.2))
        ((1 - t) • v ε + t • u ε) := by
      apply hcomp.congr
      filter_upwards [] with z
      rfl
    exact hcomp'.differentiableAt
  have hderiv : ∃ C > 0, ∀ᶠ ε in 𝓝 (0 : ℝ),
      ∀ z ∈ segment ℝ (v ε) (u ε),
        ‖fderiv ℝ (fun z : ℝ × ℝ ↦
          secondLegAmplitude (ε, z.1, z.2)) z‖ ≤ C * ‖ε ^ 3‖ := by
    -- The owner theorem supplies a neighborhood in the full parameter space.
    obtain ⟨C, hCpos, howner⟩ :=
      DFP.SecondLeg.lowGradientFactorTransverseFDeriv_norm_bound
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp howner
    have huρ : ∀ᶠ ε in 𝓝 (0 : ℝ),
        (ε, (u ε).1, (u ε).2) ∈ Metric.ball (0, 2, 1) ρ := by
      exact hu3.eventually (Metric.ball_mem_nhds _ hρpos)
    have hvρ : ∀ᶠ ε in 𝓝 (0 : ℝ),
        (ε, (v ε).1, (v ε).2) ∈ Metric.ball (0, 2, 1) ρ := by
      exact hv3.eventually (Metric.ball_mem_nhds _ hρpos)
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [huρ, hvρ] with ε hu hv z hz
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, htz⟩
    subst z
    have hline := lineMap_mem_segment ℝ
      ((ε, (v ε).1, (v ε).2)) ((ε, (u ε).1, (u ε).2)) ht
    have hline' :
        ((1 - t) • (ε, (v ε).1, (v ε).2) +
          t • (ε, (u ε).1, (u ε).2)) ∈
          segment ℝ ((ε, (v ε).1, (v ε).2))
            ((ε, (u ε).1, (u ε).2)) := by
      simpa only [AffineMap.lineMap_apply_module] using hline
    have hzBall :
        ((1 - t) • (ε, (v ε).1, (v ε).2) +
          t • (ε, (u ε).1, (u ε).2)) ∈ Metric.ball (0, 2, 1) ρ :=
      (convex_ball _ _).segment_subset hv hu hline'
    have hpoint :
        (ε, ((1 - t) • v ε + t • u ε).1,
          ((1 - t) • v ε + t • u ε).2) =
          ((1 - t) • (ε, (v ε).1, (v ε).2) +
            t • (ε, (u ε).1, (u ε).2)) := by
      ext
      · simp
        ring
      · simp
      · simp
    have hbound := hρsub hzBall
    rw [← hpoint] at hbound
    change ‖fderiv ℝ (fun z : ℝ × ℝ ↦
      (DFP.SecondLeg.gradientFactors ε z.1 z.2).1)
      (((1 - t) • v ε + t • u ε))‖ ≤ C * ‖ε ^ 3‖ at hbound
    simpa only [secondLegAmplitude] using hbound
  have hweighted := FiniteTaylorJet.weighted_transverse_isBigO
    (g := fun ε z ↦ secondLegAmplitude (ε, z.1, z.2))
    (u := u) (v := v) (a := fun ε ↦ ‖u ε - v ε‖)
    (b := fun ε ↦ ε ^ 3) huv hdiff hderiv
  have hleft :
      (fun ε ↦ secondLegAmplitude (ε, (u ε).1, (u ε).2) -
        secondLegAmplitude (ε, (v ε).1, (v ε).2)) =ᶠ[𝓝 0]
      (fun ε ↦ secondLegAmplitude (ε, p ε, h ε) -
        secondLegAmplitude
          (ε, slowGraphAmplitudeP ε, slowGraphAmplitudeH ε)) :=
    Filter.Eventually.of_forall fun ε ↦ rfl
  have hpath :
      (fun ε ↦ secondLegAmplitude (ε, p ε, h ε) -
        secondLegAmplitude
          (ε, slowGraphAmplitudeP ε, slowGraphAmplitudeH ε)) =ᶠ[𝓝 0]
        (fun ε ↦ secondLegAmplitude (ε, p ε, h ε) -
          secondLegAmplitude (slowGraphJetPath ε)) := by
    filter_upwards [] with ε
    rw [slowGraphJetPath_apply, slowGraphAmplitudeP_apply,
      slowGraphAmplitudeH_apply]
  have hright :
      (fun ε ↦ ‖u ε - v ε‖ * ε ^ 3) =ᶠ[𝓝 0]
        (fun ε ↦ ε ^ 3 *
          ‖(p ε - slowGraphAmplitudeP ε,
            h ε - slowGraphAmplitudeH ε)‖) := by
    filter_upwards [] with ε
    dsimp [u, v]
    rw [mul_comm]
  exact hweighted.congr' (hleft.trans hpath) hright

/-- The two divided differences are bounded at the base point for fifth-order graph paths. -/
theorem secondLegAmplitudeCoordinateCoefficients_isBigO
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦ p ε - slowGraphAmplitudeP ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - slowGraphAmplitudeH ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    secondLegAmplitudeShapeCoefficient p h =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) ∧
      secondLegAmplitudeHighCoefficient p h =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) := by
  have hweighted :=
    secondLegAmplitude_sub_slowGraph_isBigO_weightedTransverse p h hp hh
  obtain ⟨C, hC, hbound⟩ := (Asymptotics.isBigO_iff').mp hweighted
  constructor
  · refine (Asymptotics.isBigO_iff').mpr ?_
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with ε hε
    by_cases hε0 : ε = 0
    · -- At the base point the coefficient is defined to be zero.
      simp [secondLegAmplitudeShapeCoefficient, hε0, hC.le]
    · let dp : ℝ := p ε - slowGraphAmplitudeP ε
      let dh : ℝ := h ε - slowGraphAmplitudeH ε
      let δ : ℝ := secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε)
      have hδ : ‖δ‖ ≤ C * ‖ε ^ 3 * ‖(dp, dh)‖‖ := by
        simpa only [dp, dh, δ] using hε
      by_cases hsum : dp ^ 2 + dh ^ 2 = 0
      · -- If the quadratic defect energy vanishes, the shape numerator carries a zero factor.
        have hdp : dp = 0 := by
          nlinarith [sq_nonneg dp, sq_nonneg dh]
        simp [secondLegAmplitudeShapeCoefficient, hε0, dp, hdp, hC.le]
      · -- Otherwise divide the weighted amplitude bound by the positive quadratic energy.
        have hsum_nonneg : 0 ≤ dp ^ 2 + dh ^ 2 := by
          nlinarith [sq_nonneg dp, sq_nonneg dh]
        have hsum_pos : 0 < dp ^ 2 + dh ^ 2 := by
          exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum)
        have hεpow : ε ^ 3 ≠ 0 := pow_ne_zero 3 hε0
        have hεnorm : ‖ε ^ 3‖ ≠ 0 := by
          exact norm_ne_zero_iff.mpr hεpow
        have hδ' : ‖δ‖ ≤ C * (‖ε ^ 3‖ * ‖(dp, dh)‖) := by
          simpa only [norm_mul, norm_norm] using hδ
        have hδmul :
            ‖δ‖ * ‖dp‖ ≤ C * (‖ε ^ 3‖ * ‖(dp, dh)‖) * ‖dp‖ := by
          exact mul_le_mul_of_nonneg_right hδ' (norm_nonneg dp)
        have hratio :
            (‖(dp, dh)‖ * ‖dp‖) / (dp ^ 2 + dh ^ 2) ≤ 1 := by
          have hquad :
              ‖(dp, dh)‖ * ‖dp‖ ≤ dp ^ 2 + dh ^ 2 := by
            simpa only [Prod.norm_mk, Real.norm_eq_abs] using
              max_abs_mul_left_le_sq_add_sq dp dh
          exact (div_le_iff₀ hsum_pos).2 (by simpa only [one_mul] using hquad)
        have hcoeff :
            ‖δ * dp / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖ ≤
              C * ((‖(dp, dh)‖ * ‖dp‖) / (dp ^ 2 + dh ^ 2)) := by
          calc
            ‖δ * dp / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖
                = (‖δ‖ * ‖dp‖) / (‖ε ^ 3‖ * (dp ^ 2 + dh ^ 2)) := by
                    simp only [norm_div, norm_mul, Real.norm_eq_abs,
                      abs_of_nonneg hsum_nonneg]
            _ ≤ (C * (‖ε ^ 3‖ * ‖(dp, dh)‖) * ‖dp‖) /
                  (‖ε ^ 3‖ * (dp ^ 2 + dh ^ 2)) := by
                    exact div_le_div_of_nonneg_right hδmul
                      (mul_nonneg (norm_nonneg _) hsum_nonneg)
            _ = C * ((‖(dp, dh)‖ * ‖dp‖) / (dp ^ 2 + dh ^ 2)) := by
                  field_simp [hεnorm, hsum]
        calc
          ‖secondLegAmplitudeShapeCoefficient p h ε‖
              = ‖δ * dp / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖ := by
                  simp [secondLegAmplitudeShapeCoefficient, hε0, dp, dh, δ]
          _ ≤ C * ((‖(dp, dh)‖ * ‖dp‖) / (dp ^ 2 + dh ^ 2)) := hcoeff
          _ ≤ C * 1 := by
                exact mul_le_mul_of_nonneg_left hratio hC.le
          _ = C * ‖(1 : ℝ)‖ := by norm_num
  · refine (Asymptotics.isBigO_iff').mpr ?_
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with ε hε
    by_cases hε0 : ε = 0
    · -- At the base point the coefficient is defined to be zero.
      simp [secondLegAmplitudeHighCoefficient, hε0, hC.le]
    · let dp : ℝ := p ε - slowGraphAmplitudeP ε
      let dh : ℝ := h ε - slowGraphAmplitudeH ε
      let δ : ℝ := secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε)
      have hδ : ‖δ‖ ≤ C * ‖ε ^ 3 * ‖(dp, dh)‖‖ := by
        simpa only [dp, dh, δ] using hε
      by_cases hsum : dp ^ 2 + dh ^ 2 = 0
      · -- If the quadratic defect energy vanishes, the high numerator carries a zero factor.
        have hdh : dh = 0 := by
          nlinarith [sq_nonneg dp, sq_nonneg dh]
        simp [secondLegAmplitudeHighCoefficient, hε0, dh, hdh, hC.le]
      · -- Otherwise divide the weighted amplitude bound by the positive quadratic energy.
        have hsum_nonneg : 0 ≤ dp ^ 2 + dh ^ 2 := by
          nlinarith [sq_nonneg dp, sq_nonneg dh]
        have hsum_pos : 0 < dp ^ 2 + dh ^ 2 := by
          exact lt_of_le_of_ne hsum_nonneg (Ne.symm hsum)
        have hεpow : ε ^ 3 ≠ 0 := pow_ne_zero 3 hε0
        have hεnorm : ‖ε ^ 3‖ ≠ 0 := by
          exact norm_ne_zero_iff.mpr hεpow
        have hδ' : ‖δ‖ ≤ C * (‖ε ^ 3‖ * ‖(dp, dh)‖) := by
          simpa only [norm_mul, norm_norm] using hδ
        have hδmul :
            ‖δ‖ * ‖dh‖ ≤ C * (‖ε ^ 3‖ * ‖(dp, dh)‖) * ‖dh‖ := by
          exact mul_le_mul_of_nonneg_right hδ' (norm_nonneg dh)
        have hratio :
            (‖(dp, dh)‖ * ‖dh‖) / (dp ^ 2 + dh ^ 2) ≤ 1 := by
          have hquad :
              ‖(dp, dh)‖ * ‖dh‖ ≤ dp ^ 2 + dh ^ 2 := by
            simpa only [Prod.norm_mk, Real.norm_eq_abs] using
              max_abs_mul_right_le_sq_add_sq dp dh
          exact (div_le_iff₀ hsum_pos).2 (by simpa only [one_mul] using hquad)
        have hcoeff :
            ‖δ * dh / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖ ≤
              C * ((‖(dp, dh)‖ * ‖dh‖) / (dp ^ 2 + dh ^ 2)) := by
          calc
            ‖δ * dh / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖
                = (‖δ‖ * ‖dh‖) / (‖ε ^ 3‖ * (dp ^ 2 + dh ^ 2)) := by
                    simp only [norm_div, norm_mul, Real.norm_eq_abs,
                      abs_of_nonneg hsum_nonneg]
            _ ≤ (C * (‖ε ^ 3‖ * ‖(dp, dh)‖) * ‖dh‖) /
                  (‖ε ^ 3‖ * (dp ^ 2 + dh ^ 2)) := by
                    exact div_le_div_of_nonneg_right hδmul
                      (mul_nonneg (norm_nonneg _) hsum_nonneg)
            _ = C * ((‖(dp, dh)‖ * ‖dh‖) / (dp ^ 2 + dh ^ 2)) := by
                  field_simp [hεnorm, hsum]
        calc
          ‖secondLegAmplitudeHighCoefficient p h ε‖
              = ‖δ * dh / (ε ^ 3 * (dp ^ 2 + dh ^ 2))‖ := by
                  simp [secondLegAmplitudeHighCoefficient, hε0, dp, dh, δ]
          _ ≤ C * ((‖(dp, dh)‖ * ‖dh‖) / (dp ^ 2 + dh ^ 2)) := hcoeff
          _ ≤ C * 1 := by
                exact mul_le_mul_of_nonneg_left hratio hC.le
          _ = C * ‖(1 : ℝ)‖ := by norm_num

set_option maxHeartbeats 10000000 in
-- The explicit divided-difference normalization requires extra elaboration heartbeats.
/-- The concrete cubic factorization and its bounded coefficient estimates hold for fifth-order
perturbations of the polynomial slow graph. -/
theorem secondLegAmplitude_cubicCoordinateFactorization
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦ p ε - slowGraphAmplitudeP ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - slowGraphAmplitudeH ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (∀ᶠ ε in 𝓝 0,
      secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε) =
        ε ^ 3 * (secondLegAmplitudeShapeCoefficient p h ε *
          (p ε - slowGraphAmplitudeP ε) +
          secondLegAmplitudeHighCoefficient p h ε *
          (h ε - slowGraphAmplitudeH ε))) ∧
      secondLegAmplitudeShapeCoefficient p h =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) ∧
      secondLegAmplitudeHighCoefficient p h =O[𝓝 0]
        (fun _ : ℝ ↦ (1 : ℝ)) := by
  have hp0 : p 0 = 2 := by
    obtain ⟨C, hC, hbound⟩ := (Asymptotics.isBigO_iff').mp hp
    have hzero := mem_of_mem_nhds hbound
    have hnorm : ‖p 0 - slowGraphAmplitudeP 0‖ ≤ C * ‖(0 : ℝ) ^ 5‖ := hzero
    rw [slowGraphAmplitudeP_apply] at hnorm
    norm_num at hnorm ⊢
    linarith
  have hh0 : h 0 = 1 := by
    obtain ⟨C, hC, hbound⟩ := (Asymptotics.isBigO_iff').mp hh
    have hzero := mem_of_mem_nhds hbound
    have hnorm : ‖h 0 - slowGraphAmplitudeH 0‖ ≤ C * ‖(0 : ℝ) ^ 5‖ := hzero
    rw [slowGraphAmplitudeH_apply] at hnorm
    norm_num at hnorm ⊢
    linarith
  have heq := secondLegAmplitude_coordinateEquality p h hp0 hh0
  have hcoeff := secondLegAmplitudeCoordinateCoefficients_isBigO p h hp hh
  exact ⟨Filter.Eventually.of_forall heq, hcoeff.1, hcoeff.2⟩

set_option maxHeartbeats 10000000 in
-- The generic adapter expands the explicit coordinate terms during elaboration.
/-- The bounded-coefficient factorization implies the eighth-order amplitude residual. -/
theorem secondLegAmplitude_isBigO_of_cubicCoordinateFactorization
    {p h : ℝ → ℝ}
    (hfactor : ∀ᶠ ε in 𝓝 0,
      secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε) =
        ε ^ 3 * (secondLegAmplitudeShapeCoefficient p h ε *
          (p ε - slowGraphAmplitudeP ε) +
          secondLegAmplitudeHighCoefficient p h ε *
          (h ε - slowGraphAmplitudeH ε)))
    (hA : secondLegAmplitudeShapeCoefficient p h =O[𝓝 0]
      (fun _ : ℝ ↦ (1 : ℝ)))
    (hB : secondLegAmplitudeHighCoefficient p h =O[𝓝 0]
      (fun _ : ℝ ↦ (1 : ℝ)))
    (hp : (fun ε : ℝ ↦ p ε - slowGraphAmplitudeP ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - slowGraphAmplitudeH ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ secondLegAmplitude (ε, p ε, h ε) -
      secondLegAmplitude (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hfactor' : ∀ᶠ ε in 𝓝 0,
      secondLegAmplitude (ε, p ε, h ε) - secondLegAmplitude (slowGraphJetPath ε) =
        ε ^ 3 * (secondLegAmplitudeShapeCoefficient p h ε *
          (p ε - slowGraphAmplitudeP ε) +
          secondLegAmplitudeHighCoefficient p h ε *
          (h ε - slowGraphAmplitudeH ε)) := by
    filter_upwards [hfactor] with ε hε
    exact hε
  have hfactor'' : ∀ᶠ ε in 𝓝 0,
      secondLegAmplitude (ε, p ε, h ε) -
          secondLegAmplitude (ε, slowGraphAmplitudeP ε, slowGraphAmplitudeH ε) =
        ε ^ 3 * (secondLegAmplitudeShapeCoefficient p h ε *
          (p ε - slowGraphAmplitudeP ε) +
          secondLegAmplitudeHighCoefficient p h ε *
          (h ε - slowGraphAmplitudeH ε)) := by
    filter_upwards [hfactor'] with ε hε
    rw [slowGraphJetPath_apply] at hε
    simpa only [slowGraphAmplitudeP_apply, slowGraphAmplitudeH_apply] using hε
  simpa only [slowGraphJetPath_apply, slowGraphAmplitudeP_apply,
    slowGraphAmplitudeH_apply] using
    (isBigO_of_cubic_coordinate_factorization
      (F := secondLegAmplitude) (p₀ := slowGraphAmplitudeP)
      (h₀ := slowGraphAmplitudeH)
      (A := fun ε ↦ secondLegAmplitudeShapeCoefficient p h ε)
      (B := fun ε ↦ secondLegAmplitudeHighCoefficient p h ε)
      hfactor'' hA hB hp hh)

end DFP.TwoLeg
