module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderOneHolonomicity
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricOrderTwoHolonomicity
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricHigherOrderHolonomicity
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicBridge
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSection
import all ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16a: a fixed metric graph has compactly supported stable
components. -/
theorem metricFixedGraph_hasCompactSupport
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) :
    HasCompactSupport (ζ : ℝ → X) := by
  have hinverse_def : d.inverseCenter ζ = Function.invFun (d.centerMap ζ) := by
    exact d.inverseCenter_eq ζ
  have hcenter_def : d.centerMap ζ =
      fun u ↦ u + (d.R (u, ζ u)).1 := by
    exact d.centerMap_eq ζ
  -- Evaluate the fixed-point equation at the inverse center and cancel the center map.
  have hfixed_apply (u : ℝ) :
      ζ u = d.L (ζ (d.inverseCenter ζ u)) +
        (d.R (d.inverseCenter ζ u, ζ (d.inverseCenter ζ u))).2 := by
    have hpoint := d.fixedGraph_equation ζ hfixed (d.inverseCenter ζ u)
    have hright : d.centerMap ζ (Function.invFun (d.centerMap ζ) u) = u :=
      Function.rightInverse_invFun (d.centerMap_bijective ζ).2 u
    rw [hinverse_def] at hpoint
    rw [hright] at hpoint
    simpa only [hinverse_def] using hpoint
  obtain ⟨Rr, hRr_nonneg, hRr⟩ := d.hR_support.isBounded.subset_ball_lt
    0 (0 : ℝ × X)
  let R : ℝ := Rr
  have hR_nonneg : 0 ≤ R := by
    dsimp only [R]
    exact hRr_nonneg.le
  -- Outside the support ball, the remainder vanishes and the center coordinate is the identity.
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
  intro u hu
  have hR_le : R ≤ |u| := by
    have hR_lt : R < |u| := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] using hu
    exact hR_lt.le
  have hR_point : R ≤ ‖(u, ζ u)‖ := by
    calc
      R ≤ |u| := hR_le
      _ = ‖u‖ := (Real.norm_eq_abs u).symm
      _ ≤ ‖(u, ζ u)‖ := by
        simpa only [Prod.fst] using (norm_fst_le (u, ζ u))
  have hR_zero_at_u : d.R (u, ζ u) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hmem_ball := hRr hmem
    have hpoint_lt : ‖(u, ζ u)‖ < Rr := by
      simpa only [Metric.mem_ball, dist_zero_right] using hmem_ball
    have hpoint_lt_R : ‖(u, ζ u)‖ < R := by
      simpa only [R] using hpoint_lt
    exact (not_lt_of_ge hR_point) hpoint_lt_R
  have hcenter_id : d.centerMap ζ u = u := by
    rw [hcenter_def]
    dsimp only
    rw [hR_zero_at_u]
    simp only [Prod.fst_zero, add_zero]
  have hinverse : d.inverseCenter ζ u = u := by
    apply (d.centerMap_bijective ζ).1
    have hright : d.centerMap ζ (Function.invFun (d.centerMap ζ) u) = u :=
      Function.rightInverse_invFun (d.centerMap_bijective ζ).2 u
    rw [hinverse_def, hright, hcenter_id]
  have hR_zero : d.R (d.inverseCenter ζ u, ζ (d.inverseCenter ζ u)) = 0 := by
    rw [hinverse]
    exact hR_zero_at_u
  have hnorm : ‖ζ u‖ ≤ (d.linearRate : ℝ) * ‖ζ u‖ := by
    have hfixed_u := hfixed_apply u
    rw [hinverse] at hfixed_u
    calc
      ‖ζ u‖ = ‖d.L (ζ u) + (d.R (u, ζ u)).2‖ := by
        exact congrArg norm hfixed_u
      _ = ‖d.L (ζ u)‖ := by rw [hR_zero_at_u, Prod.snd_zero, add_zero]
      _ ≤ ‖d.L‖ * ‖ζ u‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * ‖ζ u‖ :=
        mul_le_mul_of_nonneg_right d.hL (norm_nonneg _)
  -- Strict contraction of the stable linear block forces the exterior graph value to be zero.
  have hlinearRate_real : (d.linearRate : ℝ) < 1 := by
    exact_mod_cast d.hlinearRate
  have hnorm_zero : ‖ζ u‖ = 0 := by
    nlinarith [hlinearRate_real, norm_nonneg (ζ u)]
  exact norm_eq_zero.mp hnorm_zero

/-- Helper for Infrastructure I.16a: a holonomic certificate supplies, at every positive
order, a continuous top section whose predecessor Taylor coefficient has the required
derivative.  This is the precise regularity datum missing from a metric fixed-point equation. -/
structure MetricFixedGraphHolonomicCertificate
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Prop where
  topSection : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
    ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
      Continuous a ∧
        ∀ u, HasFDerivAt
          (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
          ((a u).curryLeft) u

/-- Helper for Infrastructure I.16a: a holonomic top-section certificate upgrades a metric fixed
graph to the declared finite smoothness order.  The proof uses the scalar successor criterion at
each order and does not infer holonomicity from metric contraction alone. -/
theorem metricFixedGraph_contDiff_of_holonomicCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (certificate : MetricFixedGraphHolonomicCertificate d ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  have hall : ∀ r : ℕ, r ≤ d.nu → ContDiff ℝ r (ζ : ℝ → X) := by
    intro r hrν
    induction r with
    | zero =>
        exact contDiff_zero.mpr ζ.1.continuous
    | succ r hprevious =>
        -- The holonomic top section supplies the derivative needed for the successor criterion.
        have hr_pos : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
        have hr_le : r ≤ d.nu := (Nat.le_succ r).trans hrν
        have hprev : ContDiff ℝ ((r + 1) - 1) (ζ : ℝ → X) := by
          have hprev' : ContDiff ℝ ((r : WithTop ℕ∞) + 1 - 1) (ζ : ℝ → X) := by
            rw [withTopNatCast_add_sub_one r]
            exact hprevious hr_le
          exact hprev'
        obtain ⟨a, ha, hderiv⟩ := certificate.topSection (r + 1) hr_pos hrν
        exact LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection
          hr_pos hprev a ha hderiv
  exact hall d.nu le_rfl

/-- Infrastructure I.16a (Finite-smooth invariant graph under an explicit stable contraction):
for every finite order satisfying the metric bunching inequalities, the
fixed graph has the continuous holonomic top sections required by the finite-jet successor
argument. -/
theorem metricFixedGraph_holonomicCertificate_of_bunching
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) : MetricFixedGraphHolonomicCertificate d ζ := by
  -- Build regularity and its holonomic witness together, so the source theorem at order `r`
  -- receives the already established `C^(r - 1)` graph as in the paper's induction.
  have hregular : ∀ r : ℕ, r ≤ d.nu →
      ContDiff ℝ r (ζ : ℝ → X) ∧
        (1 ≤ r → ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
          Continuous a ∧
            ∀ u, HasFDerivAt
              (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
              ((a u).curryLeft) u) := by
    intro r hrν
    induction r with
    | zero =>
        constructor
        · exact contDiff_zero.mpr ζ.1.continuous
        · intro hr
          omega
    | succ m hprevious =>
        have hmν : m ≤ d.nu := (Nat.le_succ m).trans hrν
        have hpreviousResult := hprevious hmν
        have hprev : ContDiff ℝ m (ζ : ℝ → X) := hpreviousResult.1
        have hr_pos : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
        by_cases hm_zero : m = 0
        · subst m
          have h1_pos : 1 ≤ 1 := le_rfl
          have h1_raw := h_bunching 1 h1_pos hrν
          have h1 :
              (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
                  (d.lower : ℝ)⁻¹ < 1 := by
            simpa only [pow_one] using h1_raw
          have hderiv : ∀ u : ℝ, HasDerivAt (iteratedDeriv 0 (ζ : ℝ → X))
              ((metricOrderOneFixedSlope d ζ h1).1 u) u := by
            intro u
            simpa only [iteratedDeriv_zero] using
              metricFixedGraph_hasDerivAt_orderOne d ζ hfixed h1 u
          have hcontinuous : Continuous ((metricOrderOneFixedSlope d ζ h1).1) :=
            (metricOrderOneFixedSlope d ζ h1).1.continuous
          have hwitness := topSection_of_scalar_core (ζ : ℝ → X) 0
            ((metricOrderOneFixedSlope d ζ h1).1) hcontinuous hderiv
          obtain ⟨a, ha, htop⟩ := hwitness
          have hprev_zero : ContDiff ℝ (1 - 1) (ζ : ℝ → X) := by
            have horder_zero : (0 : WithTop ℕ∞) + 1 - 1 = 0 := by
              simpa only [Nat.cast_zero] using (withTopNatCast_add_sub_one 0)
            have hprev_zero' :
                ContDiff ℝ ((0 : WithTop ℕ∞) + 1 - 1) (ζ : ℝ → X) := by
              rw [horder_zero]
              exact hprev
            simpa only [Nat.cast_zero, zero_add] using hprev_zero'
          have hcontDiffOne : ContDiff ℝ 1 (ζ : ℝ → X) :=
            LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection
              h1_pos hprev_zero a ha htop
          exact ⟨hcontDiffOne, fun _ ↦ ⟨a, ha, htop⟩⟩
        · have hr_two : 2 ≤ m + 1 := by
            omega
          have hscalarDerivative :
              ∃ v : ℝ → X, Continuous v ∧
                ∀ u, HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) (v u) u := by
            by_cases hm_one : m = 1
            · subst m
              have h1_pos : 1 ≤ (1 : ℕ) := le_rfl
              have h2_pos : 1 ≤ (2 : ℕ) := by norm_num
              have h1ν : 1 ≤ d.nu := by omega
              have h2ν : 2 ≤ d.nu := by omega
              have h_bunching_one_raw := h_bunching 1 h1_pos h1ν
              have h_bunching_one :
                  (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
                      (d.lower : ℝ)⁻¹ < 1 := by
                simpa only [pow_one] using h_bunching_one_raw
              have h_bunching_two := h_bunching 2 h2_pos h2ν
              exact metricFixedGraph_orderTwoDerivativeSection
                d ζ hfixed hprev h_bunching_one h_bunching_two
            · have hm_two : 2 ≤ m := by omega
              let h_bunching_m := h_bunching (m + 1) hr_pos hrν
              exact metricFixedGraph_higherOrderDerivativeSection
                d ζ hfixed hm_two hrν hprev h_bunching_m
          obtain ⟨v, hv, hderiv⟩ := hscalarDerivative
          have hwitness := topSection_of_scalar_core (ζ : ℝ → X) m v hv hderiv
          obtain ⟨a, ha, htop⟩ := hwitness
          have hprev_successor : ContDiff ℝ ((m + 1) - 1) (ζ : ℝ → X) := by
            have hprev_successor' :
                ContDiff ℝ ((m : WithTop ℕ∞) + 1 - 1) (ζ : ℝ → X) := by
              rw [withTopNatCast_add_sub_one m]
              exact hprev
            exact hprev_successor'
          have hcontDiffSuccessor : ContDiff ℝ (m + 1) (ζ : ℝ → X) :=
            LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection
              hr_pos hprev_successor a ha htop
          have htopSuccessor :
              ∃ a : ℝ → (ℝ [×((m + 1) - 1 + 1)]→L[ℝ] X),
                Continuous a ∧
                  ∀ u, HasFDerivAt
                    (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) ((m + 1) - 1))
                    ((a u).curryLeft) u := by
            simpa only [Nat.add_sub_cancel] using ⟨a, ha, htop⟩
          simpa only [Nat.succ_eq_add_one] using
            ⟨hcontDiffSuccessor, fun _ ↦ htopSuccessor⟩
  refine ⟨?_⟩
  intro r hr hrν
  exact (hregular r hrν).2 hr

/-- Helper for Infrastructure I.16a: a fixed metric graph is finite-smooth when the metric
transform satisfies finite-order bunching at every order through its declared smoothness. -/
theorem metricFixedGraph_contDiff_of_bunching
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : MetricGraphTransformData X)
    (h_bunching : ∀ r : ℕ, 1 ≤ r → r ≤ d.nu →
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        (d.lower : ℝ)⁻¹ ^ r < 1)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ) :
    ContDiff ℝ d.nu (ζ : ℝ → X) := by
  have certificate := metricFixedGraph_holonomicCertificate_of_bunching d h_bunching ζ hfixed
  exact metricFixedGraph_contDiff_of_holonomicCertificate d ζ certificate

end LocalInvariantGraph
