/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Exercise_25_3_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.UpperHalfSpace
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Topology Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "State" => EuclideanSpace ℝ (Fin 2)
local notation "VectorProcess" => NNReal → Ω → State
local notation "upperHalfPlane" => upperHalfSpace 1

/-- Membership in the open upper half-plane `ℝ × (0, ∞)` is positivity of the second coordinate.
-/
theorem mem_upperHalfPlane_iff (x : State) :
    x ∈ upperHalfPlane ↔ 0 < x 1 := by
  simp [upperHalfSpace]

/-- Helper for Exercise 25.4.1: an interior point of the upper half-plane has positive second
coordinate. -/
theorem second_pos_of_mem_upperHalfPlane {x : State} (hx : x ∈ upperHalfPlane) :
    0 < x 1 := by
  -- Proof comment: unfold upper-half-plane membership and read off the second-coordinate
  -- inequality.
  simpa using (mem_upperHalfPlane_iff x).1 hx

/-- The frontier of the open upper half-plane is the horizontal axis. -/
theorem mem_frontier_upperHalfPlane_iff (x : State) :
    x ∈ frontier upperHalfPlane ↔ x 1 = 0 := by
  simpa using mem_frontier_upperHalfSpace_iff 1 x

/-- Pushing the canonical harmonic measure on `frontier (upperHalfSpace 1)` forward along the
textbook boundary coordinate `z ↦ z₁` gives the real-valued boundary law of the given
frontier-valued exit map. -/
theorem map_upperHalfPlaneBoundary_harmonicMeasure
    (P : ProbabilityMeasure Ω) {x : State} (hx : x ∈ upperHalfPlane)
    (exitValue : Ω → frontier upperHalfPlane) (hExitMeas : Measurable exitValue) :
    Measure.map (fun z : frontier upperHalfPlane ↦ (z : State) 0)
        (harmonicMeasure
          (fun _ : State ↦ P)
          upperHalfPlane
          exitValue
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier upperHalfPlane)) =
      Measure.map (fun ω ↦ (exitValue ω : State) 0) (P : Measure Ω) := by
  -- Proof comment: push the harmonic measure back to the underlying starting law and then
  -- compose the boundary-coordinate map with the exit-value map.
  have hBoundaryCoordMeas : Measurable (fun z : frontier upperHalfPlane ↦ (z : State) 0) := by
    fun_prop
  simpa [harmonicMeasure] using
    (Measure.map_map hBoundaryCoordMeas hExitMeas : _)

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 25.4.1: pointwise equality of two sample paths at `ω` preserves their
singleton level-hitting times at `ω`. -/
lemma brownianLevelHittingTime_eq_of_pathEq
    {X Y : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (hω : ∀ t : NNReal, X t ω = Y t ω) :
    brownianLevelHittingTime X b ω = brownianLevelHittingTime Y b ω := by
  -- Proof comment: unfolding `hittingAfter` reduces the claim to equality of the defining
  -- existential witness and infimum set, both of which depend only on the path values at `ω`.
  rw [brownianLevelHittingTime_eq_hittingAfter, brownianLevelHittingTime_eq_hittingAfter]
  classical
  rw [hittingAfter_def, hittingAfter_def]
  change
    (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({b} : Set ℝ)} : NNReal) : ENNReal)
      else ⊤) =
      (if ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({b} : Set ℝ) then
        ((sInf {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω ∈ ({b} : Set ℝ)} : NNReal) : ENNReal)
      else ⊤)
  have hExists :
      (∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({b} : Set ℝ)) ↔
        ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({b} : Set ℝ) := by
    constructor
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
    · rintro ⟨j, hj0, hj⟩
      exact ⟨j, hj0, by simpa [hω j] using hj⟩
  have hSet :
      {i : NNReal | (0 : NNReal) ≤ i ∧ X i ω ∈ ({b} : Set ℝ)} =
        {i : NNReal | (0 : NNReal) ≤ i ∧ Y i ω ∈ ({b} : Set ℝ)} := by
    ext i
    simp [hω i]
  by_cases hX : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ X j ω ∈ ({b} : Set ℝ)
  · have hY : ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({b} : Set ℝ) := hExists.mp hX
    rw [if_pos hX, if_pos hY]
    simpa using congrArg (fun s : Set NNReal ↦ ((sInf s : NNReal) : ENNReal)) hSet
  · have hY : ¬ ∃ j : NNReal, (0 : NNReal) ≤ j ∧ Y j ω ∈ ({b} : Set ℝ) := mt hExists.mpr hX
    rw [if_neg hX, if_neg hY]

/-- Helper for Exercise 25.4.1: for `b > 0`, a one-dimensional Brownian motion hits the level `b`
in finite time almost surely. -/
lemma positiveLevelHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂μ, brownianLevelHittingTime B b ω ≠ ⊤ := by
  -- Proof comment: use the canonical one-sided Chapter 21 hitting-time theorem instead of the
  -- broken two-sided detour from the previous local fork.
  simpa using brownianLevelHittingTime_ae_ne_top (μ := μ) (B := B) hB hb

/-- Helper for Exercise 25.4.1: the real-valued level-hitting clock is `AEMeasurable`. -/
lemma aemeasurable_levelHittingTime_toReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (b : ℝ) :
    AEMeasurable (fun ω ↦ (brownianLevelHittingTime B b ω).toReal) μ := by
  -- Proof comment: this is just the imported Chapter 21 measurability statement under the local
  -- Chapter 25 compatibility name.
  simpa using aemeasurable_brownianLevelHittingTime_toReal (μ := μ) (B := B) hB b

/-- Helper for Exercise 25.4.1: the `NNReal` model of the Brownian level-hitting clock is
`AEMeasurable`. -/
lemma aemeasurable_levelHittingTime_toNNReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (b : ℝ) :
    AEMeasurable (fun ω ↦ (brownianLevelHittingTime B b ω).toNNReal) μ := by
  -- Proof comment: compose the measurable real-valued clock with `Real.toNNReal`.
  simpa using (aemeasurable_levelHittingTime_toReal (μ := μ) (B := B) hB b).real_toNNReal

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 25.4.1: coercing the `NNReal` clock representative back to `ℝ` recovers
the real-valued clock. -/
lemma brownianLevelHittingTime_toNNReal_coe_eq_toReal
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω} :
    ((brownianLevelHittingTime B b ω).toNNReal : ℝ) =
      (brownianLevelHittingTime B b ω).toReal := by
  by_cases htop : brownianLevelHittingTime B b ω = ⊤
  · simp [htop]
  · simpa using congrArg ENNReal.toReal (ENNReal.coe_toNNReal htop)

/-- Helper for Exercise 25.4.1: a continuous path that starts below a positive level is still
strictly below that level at every time strictly before the first hit. -/
lemma brownianLevelValue_lt_level_of_lt_hittingTime
    {B : NNReal → Ω → ℝ} {b : ℝ} {ω : Ω}
    (hcont : Continuous fun t : NNReal ↦ B t ω)
    (hzero : B 0 ω = 0) (hb : 0 < b)
    {T : NNReal}
    (hT : (T : ENNReal) < brownianLevelHittingTime B b ω) :
    B T ω < b := by
  -- Proof comment: if the value at `T` were at least `b`, continuity on `[0, T]` would produce
  -- an exact hit at some earlier time, contradicting the strict inequality `T < τ_b`.
  by_contra hnot
  have hle : b ≤ B T ω := le_of_not_gt hnot
  have hlevel : b ∈ Set.Icc (B 0 ω) (B T ω) := by
    refine ⟨?_, hle⟩
    simpa [hzero] using hb.le
  obtain ⟨s, hsIcc, hs_eq⟩ :=
    (intermediate_value_Icc
      (a := (0 : NNReal))
      (b := T)
      (by simp)
      hcont.continuousOn) hlevel
  have hs_le_T : (s : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast hsIcc.2
  have hτ_le_T : brownianLevelHittingTime B b ω ≤ (T : ENNReal) := by
    exact le_trans
      (brownianLevelHittingTime_le_of_eq (B := B) (b := b) (ω := ω) (t := s) hs_eq)
      hs_le_T
  exact (not_le_of_gt hT) hτ_le_T

/-- Helper for Exercise 25.4.1: a volume-preserving measurable equivalence transports a
`withDensity` law by precomposing the density with the inverse equivalence. -/
private lemma mapWithDensityOfVolumePreserving {α β : Type*}
    [MeasureSpace α] [MeasureSpace β]
    (e : α ≃ᵐ β) (hpres : MeasurePreserving e volume volume)
    (g : α → ENNReal) (hg : Measurable g) :
    Measure.map e (volume.withDensity g) =
      volume.withDensity (fun y : β ↦ g (e.symm y)) := by
  -- Proof comment: compare both measures on measurable sets and move the set integral through the
  -- volume-preserving equivalence.
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ hs,
    withDensity_apply _ (e.measurable hs)]
  simpa using hpres.setLIntegral_comp_preimage hs (hg.comp e.symm.measurable)

/-- Helper for Exercise 25.4.1: shifting the centered Cauchy density by `x₀` produces the Cauchy
density with location parameter `x₀`. -/
private lemma cauchyPDF_centered_sub_right (x₀ : ℝ) (γ : ℝ≥0) :
    (fun y : ℝ ↦ cauchyPDF 0 γ (y - x₀)) = cauchyPDF x₀ γ := by
  -- Proof comment: after unfolding the density, both sides are the same rational function in
  -- `y - x₀`.
  funext y
  rw [cauchyPDF_def, cauchyPDF_def, cauchyPDFReal_def, cauchyPDFReal_def]
  congr 1
  ring_nf

/-- Helper for Exercise 25.4.1: translating the centered Cauchy law by `x₀` yields the Cauchy law
with location parameter `x₀`. -/
private lemma map_add_const_centeredCauchyMeasure (x₀ a : ℝ) (ha : 0 < a) :
    Measure.map (fun y : ℝ ↦ y + x₀) (cauchyMeasure 0 (Real.toNNReal a)) =
      cauchyMeasure x₀ (Real.toNNReal a) := by
  have hγ : Real.toNNReal a ≠ 0 := (Real.toNNReal_pos.mpr ha).ne'
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight x₀
  have hpres : MeasurePreserving e (volume : Measure ℝ) volume := by
    -- Proof comment: Lebesgue measure is translation invariant.
    refine ⟨e.measurable, ?_⟩
    simpa [e, MeasurableEquiv.addRight] using
      (map_add_right_eq_self (volume : Measure ℝ) x₀)
  rw [cauchyMeasure_of_scale_ne_zero 0 hγ, cauchyMeasure_of_scale_ne_zero x₀ hγ]
  -- Proof comment: transport the centered density through the translation equivalence and then
  -- rewrite the transported density to the shifted Cauchy density.
  calc
    Measure.map (fun y : ℝ ↦ y + x₀) (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) =
        Measure.map e (volume.withDensity (cauchyPDF 0 (Real.toNNReal a))) := by
          rfl
    _ = volume.withDensity (fun y : ℝ ↦ cauchyPDF 0 (Real.toNNReal a) (e.symm y)) := by
          exact
            mapWithDensityOfVolumePreserving
              (e := e) (hpres := hpres) (g := cauchyPDF 0 (Real.toNNReal a))
              (hg := measurable_cauchyPDF 0 (Real.toNNReal a))
    _ = volume.withDensity (cauchyPDF x₀ (Real.toNNReal a)) := by
          congr 1
          funext y
          simpa [e, MeasurableEquiv.addRight] using
            congrFun (cauchyPDF_centered_sub_right x₀ (Real.toNNReal a)) y

-- Proof sketch: only the second coordinate `t ↦ W t ω 1` matters, since exiting `ℝ × (0, ∞)` is
-- equivalent to the last coordinate of `x + W` hitting `(-∞, 0]`.
/-- The exit time from the upper half-plane is almost surely finite for planar Brownian motion
started at an interior point, assuming only that the second coordinate is a Brownian motion. -/
theorem upperHalfPlaneExitTime_ae_lt_top
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsBrownianMotion μ (fun t ω ↦ W t ω 1))
    {x : State} (hx : x ∈ upperHalfPlane) :
    ∀ᵐ ω ∂μ,
      hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω < ⊤ := by
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: this is the canonical reflection of the vertical Brownian coordinate.
    simpa [Bminus, brownianScaling] using
      (IsBrownianMotion.scaling hW (K := (-1 : ℝ)) (by norm_num))
  filter_upwards [positiveLevelHittingTime_ae_ne_top hBminus hx_second] with ω hω
  obtain ⟨t, ht_hit⟩ :=
    (brownianLevelHittingTime_ne_top_iff_exists_eq
      (B := Bminus) (b := x 1) (ω := ω)).1 hω
  have ht_exit_mem : x + W t ω ∈ upperHalfPlaneᶜ := by
    -- Proof comment: at the hitting time, the translated path has vertical coordinate `0`, so it
    -- lies on the boundary and hence outside the open upper half-plane.
    have hHitCoord : x 1 + W t ω 1 = 0 := by
      have hneg : -W t ω 1 = x 1 := by
        simpa [Bminus, brownianScaling, hscaleTime] using ht_hit
      linarith
    simp [hHitCoord]
  have hExit_le :
      hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω ≤ (t : ENNReal) :=
    hittingAfter_le_of_mem
      (u := fun t ω ↦ x + W t ω)
      (s := upperHalfPlaneᶜ)
      (n := (0 : NNReal))
      (ω := ω)
      (by simp)
      ht_exit_mem
  exact lt_of_le_of_lt hExit_le ENNReal.coe_lt_top

/-- Helper for Exercise 25.4.1: the upper-half-plane exit time is almost surely finite, written in
the `≠ ⊤` form that is convenient for stopping-value rewrites. -/
theorem upperHalfPlaneExitTime_ae_ne_top
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsBrownianMotion μ (fun t ω ↦ W t ω 1))
    {x : State} (hx : x ∈ upperHalfPlane) :
    ∀ᵐ ω ∂μ,
      hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω ≠ ⊤ := by
  -- Proof comment: repackage the already proved strict finiteness statement in the equivalent
  -- non-top form used by the later stopping-time identities.
  filter_upwards [upperHalfPlaneExitTime_ae_lt_top (μ := μ) (W := W) hW hx] with ω hω
  exact hω.ne

/-- Helper for Exercise 25.4.1: along a continuous vertical sample path starting at `0`, the first
exit time from `ℝ × (0, ∞)` is exactly the first time the reflected vertical coordinate reaches
the height `x 1`. -/
lemma upperHalfPlaneExitTime_eq_reflectedVerticalHittingTime_of_continuous
    {W : VectorProcess} {x : State} {Bminus : NNReal → Ω → ℝ}
    (hx : x ∈ upperHalfPlane) {ω : Ω}
    (hpath : ∀ t : NNReal, Bminus t ω = -W t ω 1)
    (hzero : W 0 ω 1 = 0)
    (hcont : Continuous fun t : NNReal ↦ W t ω 1)
    (hτhit : brownianLevelHittingTime Bminus (x 1) ω ≠ ⊤) :
    hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω =
      brownianLevelHittingTime Bminus (x 1) ω := by
  let τexit : ENNReal := hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω
  let τhit : ENNReal := brownianLevelHittingTime Bminus (x 1) ω
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hBminus_zero : Bminus 0 ω = 0 := by
    -- Proof comment: the reflected vertical path still starts from `0`.
    simpa [hzero] using hpath 0
  have hBminus_cont : Continuous fun t : NNReal ↦ Bminus t ω := by
    -- Proof comment: the reflected vertical path is just the negation of the vertical coordinate.
    have hEq : (fun t : NNReal ↦ Bminus t ω) = fun t ↦ -W t ω 1 := by
      funext t
      exact hpath t
    rw [hEq]
    exact hcont.neg
  have hhit_value :
      stoppedValue Bminus (brownianLevelHittingTime Bminus (x 1)) ω = x 1 :=
    brownianLevelHittingTime_stoppedValue_eq_level hBminus_cont hτhit
  have hboundary : x 1 + W τhit.untopA ω 1 = 0 := by
    have hneg : -W τhit.untopA ω 1 = x 1 := by
      simpa [τhit, stoppedValue, hpath τhit.untopA] using hhit_value
    linarith
  have hExitHit : x + W τhit.untopA ω ∈ upperHalfPlaneᶜ := by
    simp [hboundary]
  have hτexit_le : τexit ≤ τhit := by
    -- Proof comment: at the reflected level-hitting time, the translated vertical coordinate is
    -- exactly `0`, so the planar path has already reached the complement of the open half-plane.
    calc
      τexit ≤ ((τhit.untopA : NNReal) : ENNReal) := by
        exact
          hittingAfter_le_of_mem
          (u := fun t ω ↦ x + W t ω)
          (s := upperHalfPlaneᶜ)
          (n := (0 : NNReal))
          (ω := ω)
          (by simp)
          hExitHit
      _ ≤ τhit := by
        rw [WithTop.untopA_eq_untop hτhit]
        exact le_of_eq (WithTop.coe_untop τhit hτhit)
  have hτexit_ne_top : τexit ≠ ⊤ := ne_top_of_le_ne_top hτhit hτexit_le
  have hτhit_le : τhit ≤ τexit := by
    by_contra hnot
    have hbefore : (τexit.untopA : ENNReal) < τhit := by
      -- Proof comment: if `τexit < τhit`, then the finite exit time lies strictly before the
      -- reflected level-hitting time.
      have hτexit_coe : ((τexit.untopA : NNReal) : ENNReal) = τexit := by
        rw [WithTop.untopA_eq_untop hτexit_ne_top]
        exact WithTop.coe_untop τexit hτexit_ne_top
      have hlt : τexit < τhit := lt_of_not_ge hnot
      exact hτexit_coe ▸ hlt
    have hbelow : Bminus τexit.untopA ω < x 1 :=
      brownianLevelValue_lt_level_of_lt_hittingTime hBminus_cont hBminus_zero hx_second hbefore
    have hExitMem : x + W τexit.untopA ω ∈ upperHalfPlaneᶜ := by
      let exitSet : Set NNReal := {t | x + W t ω ∈ upperHalfPlaneᶜ}
      have hnonempty : exitSet.Nonempty := by
        refine ⟨τhit.untopA, ?_⟩
        simpa [exitSet] using hExitHit
      have hclosed : IsClosed exitSet := by
        -- Proof comment: the exit set is the preimage of the closed ray `(-∞, 0]` under the
        -- continuous translated vertical coordinate.
        have hcoordCont : Continuous fun t : NNReal ↦ x 1 + W t ω 1 :=
          continuous_const.add hcont
        simpa [exitSet, Set.preimage, Set.mem_setOf_eq, Set.mem_compl, mem_upperHalfPlane_iff] using
          (isClosed_Iic.preimage hcoordCont)
      have hbddBelow : BddBelow exitSet := by
        refine ⟨0, ?_⟩
        intro t ht
        exact bot_le
      have hτexit_eq : τexit.untopA = sInf exitSet := by
        -- Proof comment: since the exit set is nonempty, `hittingAfter` is its infimum.
        rw [show τexit = hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω by
          rfl]
        rw [hittingAfter]
        rw [if_pos]
        · rw [show {i : NNReal | (0 : NNReal) ≤ i ∧ x + W i ω ∈ upperHalfPlaneᶜ} = exitSet by
            ext t
            simp [exitSet]]
          simpa using (WithTop.untopD_coe (d := Classical.arbitrary NNReal) (x := sInf exitSet))
        · rcases hnonempty with ⟨t, ht⟩
          exact ⟨t, bot_le, ht⟩
      have hmem : sInf exitSet ∈ exitSet := hclosed.csInf_mem hnonempty hbddBelow
      simpa [exitSet, hτexit_eq] using hmem
    have hInside : x + W τexit.untopA ω ∈ upperHalfPlane := by
      -- Proof comment: strict inequality before the reflected hit keeps the translated vertical
      -- coordinate strictly positive.
      have hcoord_pos : 0 < x 1 + W τexit.untopA ω 1 := by
        have hneg : -W τexit.untopA ω 1 < x 1 := by
          simpa [hpath τexit.untopA] using hbelow
        linarith
      simpa [mem_upperHalfPlane_iff] using hcoord_pos
    have hNotInside : x + W τexit.untopA ω ∉ upperHalfPlane := by
      simpa [τexit, Set.mem_compl] using hExitMem
    exact hNotInside hInside
  -- Proof comment: the exit time and the reflected one-dimensional hitting time bound each other,
  -- hence they coincide.
  exact le_antisymm hτexit_le hτhit_le

/-- Helper for Exercise 25.4.1: almost surely, the upper-half-plane exit clock equals the
reflected vertical one-sided Brownian hitting time. -/
lemma upperHalfPlaneExitTime_ae_eq_reflectedVerticalHittingTime
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    ∀ᵐ ω ∂μ,
      hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω =
        brownianLevelHittingTime Bminus (x 1) ω := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: reflecting the vertical coordinate is the Brownian scaling theorem at
    -- factor `-1`.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hzero : ∀ ω : Ω, W 0 ω 1 = 0 := by
    -- Proof comment: every Brownian coordinate starts from `0`.
    intro ω
    simpa using congrFun (hW.isBrownianMotion 1).zero ω
  have hcont :
      ∀ᵐ ω ∂μ, Continuous fun t : NNReal ↦ W t ω 1 := by
    -- Proof comment: the vertical coordinate inherits almost-sure continuity from Brownian paths.
    simpa [HasAlmostSurelyContinuousPaths, processPath] using
      (hW.isBrownianMotion 1).continuous_paths
  filter_upwards [hcont, positiveLevelHittingTime_ae_ne_top hBminus hx_second] with ω hωcont hωhit
  -- Proof comment: apply the pathwise clock-identification lemma on the full-measure event where
  -- the reflected vertical path is continuous and hits the level `x 1` in finite time.
  exact
    upperHalfPlaneExitTime_eq_reflectedVerticalHittingTime_of_continuous
      (hx := hx)
      (Bminus := Bminus)
      (ω := ω)
      (hpath := fun t ↦ by simp [Bminus, hscaleTime])
      (hzero := hzero ω)
      (hcont := hωcont)
      (hτhit := hωhit)

/-- Helper for Exercise 25.4.1: the finite-time representatives chosen by `untopA` still agree
almost surely for the upper-half-plane exit clock and the reflected vertical hitting clock. -/
lemma upperHalfPlaneExitTime_untopA_ae_eq_reflectedVerticalHittingTime_untopA
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    (fun ω ↦
      (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω).untopA) =ᵐ[μ]
      (fun ω ↦ (brownianLevelHittingTime Bminus (x 1) ω).untopA) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  filter_upwards [upperHalfPlaneExitTime_ae_eq_reflectedVerticalHittingTime
    (μ := μ) (W := W) hW hx] with ω hω
  -- Proof comment: once the two clocks agree in `WithTop NNReal`, their `untopA` representatives
  -- agree pointwise as well.
  simp [hω]

/-- Helper for Exercise 25.4.1: the horizontal Brownian path is independent of the reflected
vertical Brownian path. -/
lemma horizontalBrownian_indep_reflectedVerticalPath
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦ W t ω 0)
      (fun ω ↦ fun t : NNReal ↦ -W t ω 1)
      μ := by
  have hIndep :
      IndepFun
        (fun ω ↦ fun t : NNReal ↦ W t ω 0)
        (fun ω ↦ fun t : NNReal ↦ W t ω 1)
        μ :=
    hW.iIndepFun.indepFun (i := 0) (j := 1) (by decide)
  have hNegPathMeas : Measurable (fun f : NNReal → ℝ ↦ fun t : NNReal ↦ -f t) := by
    -- Proof comment: pathwise reflection is the ordinary negation map on the function space.
    simpa using (measurable_neg : Measurable (fun f : NNReal → ℝ ↦ -f))
  -- Proof comment: reflect only the vertical coordinate process; independence is preserved under
  -- measurable postcomposition of one component.
  simpa [Function.comp] using hIndep.comp measurable_id hNegPathMeas

/-- Helper for Exercise 25.4.1: almost surely, the sampled horizontal coordinate at the exit time
can be rewritten using the reflected vertical hitting clock. -/
lemma upperHalfPlaneExitHorizontal_ae_eq_reflectedVerticalSample
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    (fun ω ↦
      W
        (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω).untopA
        ω 0) =ᵐ[μ]
      (fun ω ↦ W (brownianLevelHittingTime Bminus (x 1) ω).untopA ω 0) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  filter_upwards [upperHalfPlaneExitTime_ae_eq_reflectedVerticalHittingTime
    (μ := μ) (W := W) hW hx] with ω hω
  -- Proof comment: once the two clocks agree, the sampled horizontal coordinate is literally the
  -- same pointwise random variable.
  simp [hω]

/-- Helper for Exercise 25.4.1: the reflected vertical level-hitting clock factors measurably
through the reflected vertical path. -/
lemma exists_measurable_reflectedVerticalClockFactor
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State} :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    ∃ ψ : (NNReal → ℝ) → ℝ,
      Measurable ψ ∧
        (fun ω ↦ (τ ω).toReal) =ᵐ[μ] ψ ∘ (fun ω ↦ fun t : NNReal ↦ -W t ω 1) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: `Bminus` is the reflected vertical Brownian coordinate.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling
        (hW.isBrownianMotion 1)
        (K := (-1 : ℝ)) (by norm_num))
  let Bc : NNReal → Ω → ℝ := brownianContinuousVersion (μ := μ) (B := Bminus) hBminus
  have hBc : IsBrownianMotion μ Bc := by
    exact brownianContinuousVersion_isBrownianMotion (μ := μ) (B := Bminus) hBminus
  have hPastMeas (s : NNReal) :
      Measurable[MeasurableSpace.comap (processPath Bc) MeasurableSpace.pi]
        (fun ω (u : Set.Iic s) ↦ Bc u ω) := by
    -- Proof comment: every past-path coordinate is obtained from the full path by deterministic
    -- evaluation at `u`.
    have hRestrict : Measurable (fun y : NNReal → ℝ ↦ fun u : Set.Iic s ↦ y u) := by
      refine measurable_pi_lambda _ fun u ↦ ?_
      exact measurable_pi_apply (u : NNReal)
    have hproc :
        Measurable[MeasurableSpace.comap (processPath Bc) MeasurableSpace.pi]
          (processPath Bc) :=
      measurable_iff_comap_le.2 le_rfl
    simpa [Function.comp, processPath] using hRestrict.comp hproc
  have hNatLe (s : NNReal) :
      Filtration.natural Bc hBc.stronglyMeasurable s ≤
        MeasurableSpace.comap (processPath Bc) MeasurableSpace.pi := by
    rw [naturalFiltration_eq_pastPath hBc s]
    exact measurable_iff_comap_le.1 (hPastMeas s)
  have hτstop :
      IsStoppingTime (Filtration.natural Bc hBc.stronglyMeasurable)
        (brownianLevelHittingTime Bc (x 1)) := by
    exact
      brownianLevelHittingTime_isStoppingTime
        (hBsm := hBc.stronglyMeasurable)
        (hcont := brownianContinuousVersion_continuous (μ := μ) (B := Bminus) hBminus)
        (x 1)
  have hτPath :
      Measurable[MeasurableSpace.comap (processPath Bc) MeasurableSpace.pi]
        (fun ω ↦ (brownianLevelHittingTime Bc (x 1) ω).toReal) := by
    have hτPathENN :
        Measurable[MeasurableSpace.comap (processPath Bc) MeasurableSpace.pi]
          (brownianLevelHittingTime Bc (x 1)) := by
      refine measurable_of_Iic ?_
      intro i
      cases i with
      | top =>
          simp
      | coe s =>
          exact hNatLe s _ (hτstop.measurableSet_le s)
    exact ENNReal.measurable_toReal.comp hτPathENN
  obtain ⟨ψ, hψmeas, hψeq⟩ := hτPath.exists_eq_measurable_comp
  have hτeq :
      (fun ω ↦ (τ ω).toReal) =ᵐ[μ]
        (fun ω ↦ (brownianLevelHittingTime Bc (x 1) ω).toReal) := by
    filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := Bminus) hBminus] with ω hω
    have hωeq :
        brownianLevelHittingTime Bminus (x 1) ω =
          brownianLevelHittingTime Bc (x 1) ω :=
      brownianLevelHittingTime_eq_of_pathEq (b := x 1) (ω := ω) (fun t ↦ (hω t).symm)
    simpa [τ, Bc] using congrArg ENNReal.toReal hωeq
  have hprocEq :
      processPath Bminus = fun ω ↦ fun t : NNReal ↦ -W t ω 1 := by
    funext ω
    funext t
    simp [Bminus, hscaleTime, processPath]
  have hprocEqAe :
      processPath Bc =ᵐ[μ] fun ω ↦ fun t : NNReal ↦ -W t ω 1 := by
    filter_upwards [brownianContinuousVersion_ae_eq (μ := μ) (B := Bminus) hBminus] with ω hω
    funext t
    calc
      processPath Bc ω t = Bc t ω := by rfl
      _ = Bminus t ω := hω t
      _ = -W t ω 1 := by
            simp [Bminus, hscaleTime]
  refine ⟨ψ, hψmeas, ?_⟩
  have hψeqAe :
      (fun ω ↦ (brownianLevelHittingTime Bc (x 1) ω).toReal) =ᵐ[μ] ψ ∘ processPath Bc :=
    Filter.Eventually.of_forall fun ω ↦ congrFun hψeq ω
  exact hτeq.trans <| hψeqAe.trans (hprocEqAe.fun_comp ψ)

/-- Helper for Exercise 25.4.1: the horizontal Brownian path is independent of the reflected
vertical hitting clock. -/
lemma horizontalBrownianPath_indep_reflectedVerticalClock
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State} :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    IndepFun
      (fun ω ↦ fun t : NNReal ↦ W t ω 0)
      (fun ω ↦ (τ ω).toReal)
      μ := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  rcases exists_measurable_reflectedVerticalClockFactor (μ := μ) (W := W) hW (x := x) with
    ⟨ψ, hψmeas, hψeq⟩
  have hClockIndep :
      IndepFun
        (fun ω ↦ fun t : NNReal ↦ W t ω 0)
        (fun ω ↦ (τ ω).toReal)
        μ := by
    have hPathIndep := horizontalBrownian_indep_reflectedVerticalPath (μ := μ) (W := W) hW
    refine (hPathIndep.comp measurable_id hψmeas).congr (ae_eq_refl _) ?_
    simpa [Function.comp] using hψeq.symm
  simpa using hClockIndep

/-- Helper for Exercise 25.4.1: on the almost-sure finite-hit event, the reflected hitting clock
`untopA` agrees with the `Real.toNNReal` image of the real-valued clock. -/
lemma reflectedVerticalClock_untopA_ae_eq_toReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b) :
    (fun ω ↦ (brownianLevelHittingTime B b ω).untopA) =ᵐ[μ]
      (fun ω ↦ (brownianLevelHittingTime B b ω).toNNReal) := by
  filter_upwards [positiveLevelHittingTime_ae_ne_top hB hb] with ω hω
  -- Proof comment: on the almost-sure finite-hit event, `untopA` becomes the genuine `untop`,
  -- and both finite clock representatives have the same `ENNReal` coercion.
  rw [WithTop.untopA_eq_untop hω]
  apply ENNReal.coe_injective
  calc
    (((brownianLevelHittingTime B b ω).untop hω : NNReal) : ENNReal) =
        brownianLevelHittingTime B b ω := by
          exact WithTop.coe_untop _ hω
    _ = ↑((brownianLevelHittingTime B b ω).toNNReal) := by
          symm
          exact ENNReal.coe_toNNReal hω

/-- Helper for Exercise 25.4.1: every deterministic-time horizontal Brownian coordinate has the
centered Gaussian law with variance equal to that time. -/
lemma horizontalCoordinate_hasLaw
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) (s : ℝ) :
    HasLaw (fun ω ↦ W (Real.toNNReal s) ω 0) (gaussianReal 0 (Real.toNNReal s)) μ := by
  letI : IsProbabilityMeasure μ := (hW.isBrownianMotion 0).isProbabilityMeasure
  by_cases hs0 : Real.toNNReal s = 0
  · refine
      { aemeasurable := ?_
        map_eq := ?_ }
    · -- Proof comment: deterministic-time Brownian coordinates are measurable, so the zero-time
      -- specialization is still measurable.
      simpa using
        ((hW.isBrownianMotion 0).stronglyMeasurable (Real.toNNReal s)).measurable.aemeasurable
    · -- Proof comment: when the time parameter vanishes, the horizontal coordinate is constant
      -- `0`, hence its law is `gaussianReal 0 0 = dirac 0`.
      rw [hs0, gaussianReal_zero_var]
      have hzero : (fun ω ↦ W 0 ω 0) = fun _ : Ω ↦ (0 : ℝ) := by
        funext ω
        simpa using congrFun (hW.isBrownianMotion 0).zero ω
      rw [hzero, Measure.map_const]
      simp
  · -- Proof comment: for positive time, this is the Brownian marginal axiom.
    exact (hW.isBrownianMotion 0).gaussian_marginal (pos_iff_ne_zero.mpr hs0)

/-- Helper for Exercise 25.4.1: the reflected-clock horizontal sample is almost surely the
evaluation of the horizontal Brownian path at the real-valued reflected clock. -/
lemma horizontalSampleAtReflectedClock_ae_eq_clockPathEval
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
    let evalClockPath : ℝ × (NNReal → ℝ) → ℝ := fun q ↦ q.2 (Real.toNNReal q.1)
    (fun ω ↦ W (τ ω).untopA ω 0) =ᵐ[μ]
      (fun ω ↦ evalClockPath ((τ ω).toReal, processPath X ω)) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  let evalClockPath : ℝ × (NNReal → ℝ) → ℝ := fun q ↦ q.2 (Real.toNNReal q.1)
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: reflecting the vertical coordinate is the Brownian scaling theorem at
    -- factor `-1`.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  filter_upwards [reflectedVerticalClock_untopA_ae_eq_toReal
    (μ := μ) (B := Bminus) (b := x 1) hBminus hx_second] with ω hω
  -- Proof comment: on the finite-hit event, rewrite the stopping time from `untopA` to
  -- `toNNReal`, then unfold `processPath` so the right-hand side becomes ordinary path
  -- evaluation at that same deterministic time.
  have htime :
      W (τ ω).untopA ω 0 = W (τ ω).toNNReal ω 0 := by
    simpa [τ] using congrArg (fun t : NNReal ↦ W t ω 0) hω
  simpa [evalClockPath, X, processPath_apply, ENNReal.coe_toNNReal_eq_toReal] using htime

/-- Helper for Exercise 25.4.1: the reflected vertical real clock and the horizontal Brownian path
have the product law of their marginals. -/
lemma horizontalPathReflectedClockToRealPairMap_eq_prod
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) (x : State) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
    μ.map (fun ω ↦ ((τ ω).toReal, processPath X ω)) =
      (μ.map fun ω ↦ (τ ω).toReal).prod (μ.map (processPath X)) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  letI : IsProbabilityMeasure μ := (hW.isBrownianMotion 0).isProbabilityMeasure
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the reflected vertical coordinate is Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hClockAemeas : AEMeasurable (fun ω ↦ (τ ω).toReal) μ := by
    -- Proof comment: the reflected hitting clock is measurable after passing to `toReal`.
    simpa [τ] using aemeasurable_levelHittingTime_toReal (μ := μ) (B := Bminus) hBminus (x 1)
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: Brownian paths are measurable as maps into the full path space.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hIndep :
      IndepFun (fun ω ↦ (τ ω).toReal) (processPath X) μ := by
    -- Proof comment: symmetry turns the previously proved path/clock independence into the
    -- clock/path order required by the product-map criterion.
    simpa [τ, X, processPath] using
      (horizontalBrownianPath_indep_reflectedVerticalClock
        (μ := μ) (W := W) hW (x := x)).symm
  -- Proof comment: independence of the real-valued clock and the horizontal path is exactly the
  -- standard criterion that the joint pushforward is the product of the marginals.
  exact
    (indepFun_iff_map_prod_eq_prod_map_map hClockAemeas hPathMeas.aemeasurable).1 hIndep

/-- Helper for Exercise 25.4.1: under the horizontal path law, evaluating the path at a
deterministic real time produces the corresponding Gaussian marginal. -/
lemma horizontalPathLaw_eval_hasLaw
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) (s : ℝ) :
    let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
    let pathLaw : Measure (NNReal → ℝ) := μ.map (processPath X)
    HasLaw (fun p : NNReal → ℝ ↦ p (Real.toNNReal s))
      (gaussianReal 0 (Real.toNNReal s)) pathLaw := by
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  let pathLaw : Measure (NNReal → ℝ) := μ.map (processPath X)
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: the horizontal Brownian coordinate has a measurable full path map.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  refine
    { aemeasurable := (measurable_pi_apply (Real.toNNReal s)).aemeasurable
      map_eq := ?_ }
  -- Proof comment: push the deterministic-time evaluation through the path map and then reuse
  -- the ordinary Brownian marginal law at time `Real.toNNReal s`.
  change
    Measure.map (fun p : NNReal → ℝ ↦ p (Real.toNNReal s)) (μ.map (processPath X)) =
      gaussianReal 0 (Real.toNNReal s)
  rw [Measure.map_map (measurable_pi_apply (Real.toNNReal s)) hPathMeas]
  simpa [X, processPath_apply] using
    (horizontalCoordinate_hasLaw (μ := μ) (W := W) hW s).map_eq

/-- Helper for Exercise 25.4.1: the reflected-clock horizontal sample is almost surely the
canonical `NNReal`-time evaluation of the horizontal Brownian path. -/
lemma horizontalSampleAtReflectedClock_ae_eq_processPathEvalToNNReal
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
    (fun ω ↦ W (τ ω).untopA ω 0) =ᵐ[μ]
      (fun ω ↦ processPath X ω ((τ ω).toNNReal)) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: reflecting the vertical coordinate is again Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  filter_upwards [reflectedVerticalClock_untopA_ae_eq_toReal
    (μ := μ) (B := Bminus) (b := x 1) hBminus hx_second] with ω hω
  -- Proof comment: once the stopping clock is rewritten from `untopA` to `toNNReal`, the target
  -- is just the definition of `processPath` evaluated at that same deterministic time.
  have htime :
      W (τ ω).untopA ω 0 = W (τ ω).toNNReal ω 0 := by
    simpa [τ] using congrArg (fun t : NNReal ↦ W t ω 0) hω
  simpa [X, processPath_apply] using htime

/-- Helper for Exercise 25.4.1: the reflected `NNReal` clock and the horizontal Brownian path have
the product law of their marginals. -/
lemma horizontalPathReflectedClockToNNRealPairMap_eq_prod
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) (x : State) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    let τNN : Ω → NNReal := fun ω ↦ (τ ω).toNNReal
    let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
    μ.map (fun ω ↦ (τNN ω, processPath X ω)) =
      (μ.map τNN).prod (μ.map (processPath X)) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let τNN : Ω → NNReal := fun ω ↦ (τ ω).toNNReal
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  letI : IsProbabilityMeasure μ := (hW.isBrownianMotion 0).isProbabilityMeasure
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the reflected vertical coordinate is Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hτNNAemeas : AEMeasurable τNN μ := by
    -- Proof comment: the reflected `NNReal` clock is the measurable image of the real-valued
    -- hitting clock.
    simpa [τNN] using aemeasurable_levelHittingTime_toNNReal (μ := μ) (B := Bminus) hBminus (x 1)
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: Brownian paths are measurable as maps into the full path space.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hIndep :
      IndepFun τNN (processPath X) μ := by
    have hIndepReal :
        IndepFun (processPath X) (fun ω ↦ (τ ω).toReal) μ := by
      -- Proof comment: reuse the earlier independence result before changing the clock owner.
      simpa [τ, X, processPath] using
        (horizontalBrownianPath_indep_reflectedVerticalClock
          (μ := μ) (W := W) hW (x := x))
    have hIndepNN :
        IndepFun (processPath X) τNN μ := by
      -- Proof comment: independence is stable under measurable postcomposition of the clock.
      refine
        (hIndepReal.comp measurable_id measurable_real_toNNReal).congr
          (ae_eq_refl _) ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp [τNN, Function.comp]
    exact hIndepNN.symm
  -- Proof comment: independence of the `NNReal` clock and the horizontal path is exactly the
  -- criterion that the joint pushforward equals the product of the marginals.
  exact
    (indepFun_iff_map_prod_eq_prod_map_map hτNNAemeas hPathMeas.aemeasurable).1 hIndep

/-- Helper for Exercise 25.4.1: the reflected `NNReal` hitting clock contributes the textbook
Laplace factor `exp (-(x₂)|u|)`. -/
lemma reflectedClockToNNReal_laplaceFactor
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) (u : ℝ) :
    let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
    let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
    let τNN : Ω → NNReal := fun ω ↦ (τ ω).toNNReal
    ∫ s : NNReal, Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) ∂(μ.map τNN) =
      Complex.exp (-(x 1) * |u|) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let τNN : Ω → NNReal := fun ω ↦ (τ ω).toNNReal
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the reflected vertical coordinate is Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hτNNAemeas : AEMeasurable τNN μ := by
    -- Proof comment: the reflected `NNReal` clock is the measurable image of the real-valued
    -- hitting clock.
    simpa [τNN] using aemeasurable_levelHittingTime_toNNReal (μ := μ) (B := Bminus) hBminus (x 1)
  let τNNm : Ω → NNReal := hτNNAemeas.mk τNN
  have hτNNae : τNN =ᵐ[μ] τNNm := hτNNAemeas.ae_eq_mk
  have hτNNMeas : Measurable τNNm := hτNNAemeas.measurable_mk
  have hτRealAemeas : AEMeasurable (fun ω ↦ (τ ω).toReal) μ := by
    -- Proof comment: the real-valued hitting-time law is the imported Chapter 21 measurable
    -- object.
    simpa [τ] using
      aemeasurable_levelHittingTime_toReal (μ := μ) (B := Bminus) hBminus (x 1)
  have hu_nonneg : 0 ≤ (u ^ 2 / 2 : ℝ) := by
    positivity
  have hLaplace :
      ∫ r : ℝ, Real.exp (-(max (u ^ 2 / 2) 0 * r)) ∂
          (brownianLevelHittingTimeLaw hBminus (x 1) : Measure ℝ) =
        Real.exp (-(x 1) * (Real.sqrt 2 * Real.sqrt (max (u ^ 2 / 2) 0))) := by
    -- Proof comment: specialize the one-dimensional hitting-time Laplace transform at
    -- `l = u² / 2`.
    simpa using
      (brownianLevelHittingTime_laplaceTransform
        (hB := hBminus) hx_second (l := Real.toNNReal (u ^ 2 / 2)))
  calc
    ∫ s : NNReal, Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) ∂(μ.map τNN) =
        ∫ s : NNReal, Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) ∂(μ.map τNNm) := by
          rw [Measure.map_congr hτNNae]
    _ = ∫ ω, Complex.exp (-((u ^ 2 / 2 : ℝ) * ((τNNm ω : NNReal) : ℝ))) ∂μ := by
          -- Proof comment: pull the `NNReal` clock integral back to the underlying probability
          -- space.
          have hfm :
              AEStronglyMeasurable
                (fun s : NNReal ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))))
                (μ.map τNNm) := by
            fun_prop
          simpa [τNNm, Function.comp] using
            (integral_map (μ := μ) (φ := τNNm) hτNNMeas.aemeasurable (f := fun s : NNReal ↦
              Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) hfm)
    _ = ∫ ω, Complex.exp (-((u ^ 2 / 2 : ℝ) * (τ ω).toReal)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hτNNae] with ω hω
          rw [← hω]
          rw [brownianLevelHittingTime_toNNReal_coe_eq_toReal (B := Bminus) (b := x 1) (ω := ω)]
    _ = ∫ r : ℝ, Complex.exp (-((u ^ 2 / 2 : ℝ) * r)) ∂
          (μ.map fun ω ↦ (τ ω).toReal) := by
          -- Proof comment: rewrite the same integral through the real-valued clock map.
          have hfm :
              AEStronglyMeasurable
                (fun r : ℝ ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * r)))
                (μ.map fun ω ↦ (τ ω).toReal) := by
            fun_prop
          simpa [Function.comp] using
            (integral_map
              (μ := μ)
              (φ := fun ω ↦ (τ ω).toReal)
              hτRealAemeas
              (f := fun r : ℝ ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * r)))
              hfm).symm
    _ = ∫ r : ℝ, Complex.exp (-((u ^ 2 / 2 : ℝ) * r)) ∂
          (brownianLevelHittingTimeLaw hBminus (x 1) : Measure ℝ) := by
          rw [brownianLevelHittingTimeLaw_toMeasure (hB := hBminus) (b := x 1)]
    _ = ∫ r : ℝ, (Real.exp (-((u ^ 2 / 2 : ℝ) * r)) : ℂ) ∂
          (brownianLevelHittingTimeLaw hBminus (x 1) : Measure ℝ) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun r ↦ by simp
    _ = ∫ r : ℝ, (Real.exp (-(max (u ^ 2 / 2) 0 * r)) : ℂ) ∂
          (brownianLevelHittingTimeLaw hBminus (x 1) : Measure ℝ) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun r ↦ by simp [max_eq_left hu_nonneg]
    _ = (Real.exp (-(x 1) * (Real.sqrt 2 * Real.sqrt (u ^ 2 / 2))) : ℂ) := by
          -- Proof comment: now apply the one-dimensional Brownian hitting-time Laplace transform.
          rw [integral_complex_ofReal]
          have hLaplace' :=
            congrArg (fun r : ℝ ↦ (r : ℂ)) hLaplace
          simpa [max_eq_left hu_nonneg] using hLaplace'
    _ = Complex.exp (-(x 1) * |u|) := by
          -- Proof comment: the Laplace exponent simplifies because `sqrt (u^2) = |u|`.
          have hsqrt : Real.sqrt 2 * Real.sqrt (u ^ 2 / 2) = |u| := by
            rw [← Real.sqrt_mul (by positivity) (u ^ 2 / 2)]
            have htwo : (2 * (u ^ 2 / 2 : ℝ)) = u ^ 2 := by ring
            rw [htwo, Real.sqrt_sq_eq_abs]
          rw [hsqrt]
          simp

/-- Helper for Exercise 25.4.1: a simple clock partitions any sampled quantity into the sum of
its singleton fibers. -/
lemma simpleFunc_apply_eq_sum_indicator
    {β : Type*} [AddCommMonoid β]
    (σ : MeasureTheory.SimpleFunc Ω NNReal) (g : NNReal → Ω → β) :
    (fun ω ↦ g (σ ω) ω) =
      fun ω ↦
        Finset.sum σ.range (fun s ↦ Set.indicator {ω' | σ ω' = s} (g s) ω) := by
  funext ω
  -- Proof comment: only the unique active fiber `σ ω` contributes to the finite partition sum.
  have hsum :
      Finset.sum σ.range (fun s ↦ Set.indicator {ω' | σ ω' = s} (g s) ω) =
        g (σ ω) ω := by
    calc
      Finset.sum σ.range (fun s ↦ Set.indicator {ω' | σ ω' = s} (g s) ω) =
          Set.indicator {ω' | σ ω' = σ ω} (g (σ ω)) ω := by
            refine Finset.sum_eq_single_of_mem (σ ω) (σ.mem_range_self ω) ?_
            intro s hs hs_ne
            have hnot : ω ∉ {ω' | σ ω' = s} := by
              intro hEq
              exact hs_ne hEq.symm
            simp [Set.indicator_of_notMem, hnot]
      _ = g (σ ω) ω := by
            simp [Set.indicator_of_mem, Set.mem_setOf_eq]
  exact hsum.symm

/-- Helper for Exercise 25.4.1: evaluating a measurable path at a simple `NNReal` clock is
measurable. -/
lemma measurable_processPathEval_simpleClock
    {β : Type*} [MeasurableSpace β]
    {path : Ω → NNReal → β} (hPath : Measurable path)
    (σ : MeasureTheory.SimpleFunc Ω NNReal) :
    Measurable (fun ω ↦ path ω (σ ω)) := by
  induction σ using MeasureTheory.SimpleFunc.induction' with
  | const c =>
      -- Proof comment: a deterministic clock reduces evaluation to an ordinary coordinate map.
      simpa using (measurable_pi_apply c).comp hPath
  | @pcw f g s hs hf hg =>
      -- Proof comment: on a piecewise simple clock, evaluate on each measurable branch
      -- separately and recombine by `Measurable.piecewise`.
      classical
      have hpiece :
          Measurable (s.piecewise (fun ω ↦ path ω (f ω)) fun ω ↦ path ω (g ω)) :=
        hf.piecewise hs hg
      convert hpiece using 1
      ext ω
      by_cases hω : ω ∈ s <;> simp [MeasureTheory.SimpleFunc.coe_piecewise, Set.piecewise, hω]

/-- Helper for Exercise 25.4.1: one fiber of a simple clock contributes its clock mass times the
deterministic Gaussian characteristic factor at that time. -/
lemma simpleClockFiber_charIntegral
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (σ : MeasureTheory.SimpleFunc Ω NNReal)
    (hIndep :
      IndepFun (fun ω ↦ σ ω) (processPath (fun t ω ↦ W t ω 0)) μ)
    (s : NNReal) (u : ℝ) :
    ∫ ω,
        Set.indicator {ω' | σ ω' = s}
          (fun ω ↦ Complex.exp (u * processPath (fun t ω ↦ W t ω 0) ω s * Complex.I)) ω ∂μ =
      (μ.real {ω | σ ω = s} : ℂ) * Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) := by
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  let A : Set Ω := {ω | σ ω = s}
  let clockIndicator : NNReal → ℂ := Set.indicator ({s} : Set NNReal) fun _ ↦ (1 : ℂ)
  let pathExp : (NNReal → ℝ) → ℂ := fun p ↦ Complex.exp (u * p s * Complex.I)
  have hA : MeasurableSet A := by
    -- Proof comment: the `σ = s` fiber is measurable because simple functions are measurable.
    change MeasurableSet ((fun ω ↦ σ ω) ⁻¹' {s})
    exact σ.measurable (measurableSet_singleton s)
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: the horizontal Brownian coordinate has a measurable full path map.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hClockIndicatorMeas : Measurable clockIndicator := by
    -- Proof comment: the clock-side fiber weight is the indicator of the singleton `{s}`.
    exact measurable_const.indicator (measurableSet_singleton s)
  have hPathExpMeas : Measurable pathExp := by
    -- Proof comment: deterministic evaluation at time `s` is measurable on the path space, and
    -- the complex exponential preserves measurability.
    fun_prop
  have hIndepComp :
      IndepFun
        (fun ω ↦ clockIndicator (σ ω))
        (fun ω ↦ pathExp (processPath X ω))
        μ := by
    -- Proof comment: compose the independent clock/path pair with the fiber indicator on the
    -- clock side and deterministic evaluation on the path side.
    simpa [clockIndicator, pathExp, Function.comp] using
      hIndep.comp hClockIndicatorMeas hPathExpMeas
  have hClockAesm :
      AEStronglyMeasurable (fun ω ↦ clockIndicator (σ ω)) μ := by
    exact (hClockIndicatorMeas.comp σ.measurable).aestronglyMeasurable
  have hPathAesm :
      AEStronglyMeasurable (fun ω ↦ pathExp (processPath X ω)) μ := by
    exact (hPathExpMeas.comp hPathMeas).aestronglyMeasurable
  have hFiberMul :
      (fun ω ↦
        Set.indicator A
          (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) ω) =
        fun ω ↦ clockIndicator (σ ω) * pathExp (processPath X ω) := by
    -- Proof comment: on the fiber `{σ = s}` the clock indicator is `1`, and off the fiber it is
    -- `0`, so the product matches the indicator form pointwise.
    funext ω
    by_cases hω : σ ω = s
    · simp [A, clockIndicator, pathExp, hω]
    · simp [A, clockIndicator, pathExp, hω]
  have hClockIntegral :
      ∫ ω, clockIndicator (σ ω) ∂μ = (μ.real A : ℂ) := by
    -- Proof comment: integrating the clock-side indicator just records the mass of the fiber.
    calc
      ∫ ω, clockIndicator (σ ω) ∂μ =
          ∫ ω, Set.indicator A (fun _ ↦ (1 : ℂ)) ω ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω ↦ by
              by_cases hω : σ ω = s <;> simp [A, clockIndicator, hω]
      _ = (μ.real A : ℂ) := by
            rw [integral_indicator_const (μ := μ) (s := A) (e := (1 : ℂ)) hA]
            change (μ.real A : ℂ) * 1 = (μ.real A : ℂ)
            ring
  have hPathIntegral :
      ∫ ω, pathExp (processPath X ω) ∂μ =
        Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) := by
    have hEvalAemeas : AEMeasurable (fun ω ↦ processPath X ω s) μ :=
      ((measurable_pi_apply s).comp hPathMeas).aemeasurable
    calc
      ∫ ω, pathExp (processPath X ω) ∂μ =
          ∫ y, Complex.exp (u * y * Complex.I) ∂(μ.map fun ω ↦ processPath X ω s) := by
            have hIntegrandAesm :
                AEStronglyMeasurable (fun y : ℝ ↦ Complex.exp (u * y * Complex.I))
                  (μ.map fun ω ↦ processPath X ω s) := by
              fun_prop
            simpa [pathExp, Function.comp] using
              (integral_map
                (μ := μ)
                (φ := fun ω ↦ processPath X ω s)
                hEvalAemeas
                (f := fun y : ℝ ↦ Complex.exp (u * y * Complex.I))
                hIntegrandAesm).symm
      _ = charFun (μ.map fun ω ↦ processPath X ω s) u := by
            rw [MeasureTheory.charFun_apply_real]
      _ = charFun (gaussianReal 0 s) u := by
            congr 1
            simpa [X, processPath_apply] using
              (horizontalCoordinate_hasLaw (μ := μ) (W := W) hW (s : ℝ)).map_eq
      _ = Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) := by
            rw [ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := s) u]
            congr 1
            norm_num
            ring
  -- Proof comment: factor the fiber integral into the fiber mass and the deterministic-time
  -- Gaussian characteristic function.
  calc
    ∫ ω,
        Set.indicator {ω' | σ ω' = s}
          (fun ω ↦ Complex.exp (u * processPath (fun t ω ↦ W t ω 0) ω s * Complex.I)) ω ∂μ =
        ∫ ω, clockIndicator (σ ω) * pathExp (processPath X ω) ∂μ := by
          rw [hFiberMul]
    _ =
        (∫ ω, clockIndicator (σ ω) ∂μ) *
          ∫ ω, pathExp (processPath X ω) ∂μ := by
            exact hIndepComp.integral_fun_mul_eq_mul_integral hClockAesm hPathAesm
    _ = (μ.real A : ℂ) * Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) := by
          rw [hClockIntegral, hPathIntegral]

/-- Helper for Exercise 25.4.1: a finite-valued random `NNReal` clock independent of the
horizontal Brownian path yields the Gaussian-mixture characteristic function obtained by averaging
the deterministic-time marginals over the clock law. -/
lemma charFun_horizontalSampleAtIndependentSimpleClock
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W)
    (σ : MeasureTheory.SimpleFunc Ω NNReal)
    (hIndep :
      IndepFun (fun ω ↦ σ ω) (processPath (fun t ω ↦ W t ω 0)) μ)
    (u : ℝ) :
    charFun (μ.map (fun ω ↦ processPath (fun t ω ↦ W t ω 0) ω (σ ω))) u =
      ∫ s : NNReal, Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) ∂(μ.map fun ω ↦ σ ω) := by
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: the horizontal Brownian coordinate has a measurable full path map.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hSampleMeas : Measurable (fun ω ↦ processPath X ω (σ ω)) := by
    -- Proof comment: evaluating a measurable path at a simple clock is measurable by induction on
    -- the clock.
    exact measurable_processPathEval_simpleClock hPathMeas σ
  have hFiberIntegrable :
      ∀ s ∈ σ.range,
        Integrable
          (fun ω ↦
            Set.indicator {ω' | σ ω' = s}
              (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) ω)
          μ := by
    intro s hs
    have hFiberSet : MeasurableSet {ω : Ω | σ ω = s} := by
      change MeasurableSet ((fun ω ↦ σ ω) ⁻¹' {s})
      exact σ.measurable (measurableSet_singleton s)
    have hFiberMeas :
        Measurable
          (fun ω ↦
            Set.indicator {ω' | σ ω' = s}
              (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) ω) := by
      have hBaseMeas :
          Measurable (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) := by
        fun_prop
      exact hBaseMeas.indicator hFiberSet
    refine Integrable.mono' (integrable_const 1) hFiberMeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : σ ω = s
      · simpa [hω, mul_assoc] using
          (Complex.norm_exp_ofReal_mul_I (u * processPath X ω s)).le
      · simp [hω]
  have hClockFiberIntegrable :
      ∀ s ∈ σ.range,
        Integrable
          (fun ω ↦
            Set.indicator {ω' | σ ω' = s}
              (fun _ : Ω ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) ω)
          μ := by
    intro s hs
    have hFiberSet : MeasurableSet {ω : Ω | σ ω = s} := by
      change MeasurableSet ((fun ω ↦ σ ω) ⁻¹' {s})
      exact σ.measurable (measurableSet_singleton s)
    have hFiberMeas :
        Measurable
          (fun ω ↦
            Set.indicator {ω' | σ ω' = s}
              (fun _ : Ω ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) ω) := by
      exact measurable_const.indicator hFiberSet
    refine Integrable.mono' (integrable_const 1) hFiberMeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : σ ω = s
      · have hs_nonneg : 0 ≤ (s : ℝ) := by exact s.2
        have hu_nonneg : 0 ≤ (u ^ 2 / 2 : ℝ) := by positivity
        have hmem : ω ∈ {ω' : Ω | σ ω' = s} := by simpa [Set.mem_setOf_eq] using hω
        simp [Set.indicator_of_mem, hmem, Complex.norm_exp]
        have hReSq : (↑u ^ 2 : ℂ).re = u ^ 2 := by
          simp [pow_two]
        have hRe : ((↑u ^ 2 : ℂ).re / 2) = (u ^ 2 / 2 : ℝ) := by
          rw [hReSq]
        rw [hRe]
        nlinarith
      · simp [hω]
  rw [MeasureTheory.charFun_apply_real]
  calc
    ∫ r, Complex.exp (u * r * Complex.I) ∂(μ.map fun ω ↦ processPath X ω (σ ω)) =
        ∫ ω, Complex.exp (u * processPath X ω (σ ω) * Complex.I) ∂μ := by
          -- Proof comment: pull the characteristic-function integral back to the base probability
          -- space.
          have hIntegrandAesm :
              AEStronglyMeasurable (fun r : ℝ ↦ Complex.exp (u * r * Complex.I))
                (μ.map fun ω ↦ processPath X ω (σ ω)) := by
            fun_prop
          simpa [Function.comp] using
            (integral_map
              (μ := μ)
              (φ := fun ω ↦ processPath X ω (σ ω))
              hSampleMeas.aemeasurable
              (f := fun r : ℝ ↦ Complex.exp (u * r * Complex.I))
              hIntegrandAesm)
    _ =
        Finset.sum σ.range
          (fun s ↦
            ∫ ω,
              Set.indicator {ω' | σ ω' = s}
                (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) ω ∂μ) := by
          -- Proof comment: expand the simple-clock sample into the sum over its singleton fibers.
          rw [show (fun ω ↦ Complex.exp (u * processPath X ω (σ ω) * Complex.I)) =
              (fun ω ↦
                Finset.sum σ.range
                  (fun s ↦
                    Set.indicator {ω' | σ ω' = s}
                      (fun ω ↦ Complex.exp (u * processPath X ω s * Complex.I)) ω)) by
                simpa using
                  (simpleFunc_apply_eq_sum_indicator σ
                    (fun s ω ↦ Complex.exp (u * processPath X ω s * Complex.I)))]
          rw [MeasureTheory.integral_finset_sum _ hFiberIntegrable]
    _ =
        Finset.sum σ.range
          (fun s ↦
            (μ.real {ω | σ ω = s} : ℂ) *
              Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) := by
          -- Proof comment: each fiber integral factors into its mass and the deterministic-time
          -- Gaussian characteristic factor.
          refine Finset.sum_congr rfl ?_
          intro s hs
          simpa [X] using
            (simpleClockFiber_charIntegral (μ := μ) (W := W) hW σ hIndep s u)
    _ =
        ∫ ω, Complex.exp (-((u ^ 2 / 2 : ℝ) * (σ ω : ℝ))) ∂μ := by
          -- Proof comment: reassemble the same finite partition for the clock-side integral.
          calc
            Finset.sum σ.range
              (fun s ↦
                (μ.real {ω | σ ω = s} : ℂ) *
                  Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) =
                Finset.sum σ.range
                  (fun s ↦
                    ∫ ω,
                      Set.indicator {ω' | σ ω' = s}
                        (fun _ : Ω ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) ω ∂μ) := by
                          refine Finset.sum_congr rfl ?_
                          intro s hs
                          rw [integral_indicator_const (μ := μ) (s := {ω' | σ ω' = s})
                            (e := Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))))
                            (σ.measurable (measurableSet_singleton s))]
                          change
                            ((μ.real {ω | σ ω = s} : ℂ) *
                                Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) =
                              ((μ.real {ω | σ ω = s} : ℂ) *
                                Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))))
                          simp
            _ =
                ∫ ω,
                  Finset.sum σ.range
                    (fun s ↦
                      Set.indicator {ω' | σ ω' = s}
                        (fun _ : Ω ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ)))) ω) ∂μ := by
                          symm
                          rw [MeasureTheory.integral_finset_sum _ hClockFiberIntegrable]
            _ = ∫ ω, Complex.exp (-((u ^ 2 / 2 : ℝ) * (σ ω : ℝ))) ∂μ := by
                  congr 1
                  funext ω
                  simpa using
                    (congrFun
                      (simpleFunc_apply_eq_sum_indicator σ
                        (fun s : NNReal => fun _ : Ω ↦
                          Complex.exp (-(↑u ^ 2 / 2 * (s : ℝ)))))
                      ω).symm
    _ =
        ∫ s : NNReal, Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) ∂(μ.map fun ω ↦ σ ω) := by
          -- Proof comment: push the clock-side integral back to the simple clock law.
          have hIntegrandAesm :
              AEStronglyMeasurable
                (fun s : NNReal ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))))
                (μ.map fun ω ↦ σ ω) := by
            fun_prop
          simpa [Function.comp] using
            (integral_map
              (μ := μ)
              (φ := fun ω ↦ σ ω)
              σ.measurable.aemeasurable
              (f := fun s : NNReal ↦ Complex.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))))
              hIntegrandAesm).symm

/-- Helper for Exercise 25.4.1: the horizontal coordinate sampled at the reflected vertical
hitting clock is almost everywhere measurable. -/
lemma aemeasurable_horizontalSampleAtReflectedVerticalClock
    {μ : Measure Ω} {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    AEMeasurable
      (fun ω ↦
        W
          (brownianLevelHittingTime
            (brownianScaling (fun t ω ↦ W t ω 1) (-1)) (x 1) ω).untopA
          ω 0) μ := by
  -- Route correction: the earlier stopped-value owner route still needs a progressively
  -- measurable continuous version. Here we approximate the measurable `untopA` clock itself, so
  -- no upper-half-plane finiteness rewrite is needed in this standalone measurability lemma.
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let τA : Ω → NNReal := fun ω ↦ (τ ω).untopA
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the reflected vertical coordinate is Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hx_second : 0 < x 1 := by
    exact second_pos_of_mem_upperHalfPlane hx
  have hτNNAemeas : AEMeasurable (fun ω ↦ (τ ω).toNNReal) μ := by
    simpa [τ] using aemeasurable_levelHittingTime_toNNReal (μ := μ) (B := Bminus) hBminus (x 1)
  let τAm : Ω → NNReal := hτNNAemeas.mk (fun ω ↦ (τ ω).toNNReal)
  have hτAMeas : Measurable τAm := hτNNAemeas.measurable_mk
  have hτAae :
      τA =ᵐ[μ] τAm := by
    exact
      (reflectedVerticalClock_untopA_ae_eq_toReal (μ := μ) (B := Bminus) (b := x 1)
        hBminus hx_second).trans hτNNAemeas.ae_eq_mk
  let σ : ℕ → MeasureTheory.SimpleFunc Ω NNReal := fun n ↦
    MeasureTheory.SimpleFunc.approxOn τAm hτAMeas (Set.range τAm ∪ {0}) 0 (by simp) n
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: the horizontal Brownian coordinate has a measurable full path map.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hApproxMeas :
      ∀ n, AEMeasurable (fun ω ↦ processPath X ω (σ n ω)) μ := by
    intro n
    -- Proof comment: each simple-clock evaluation is measurable by induction on the simple clock.
    exact (measurable_processPathEval_simpleClock hPathMeas (σ n)).aemeasurable
  have hApproxClock :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τA ω)) := by
    -- Proof comment: the theorem-local simple clocks converge pointwise to the reflected
    -- `untopA`-clock through the measurable `NNReal` representative.
    have hApproxClockRep :
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τAm ω)) := by
      exact Filter.Eventually.of_forall fun ω ↦
        MeasureTheory.SimpleFunc.tendsto_approxOn hτAMeas (by simp)
          (subset_closure (Or.inl ⟨ω, rfl⟩))
    filter_upwards [hApproxClockRep, hτAae] with ω hωapprox hωeq
    rw [hωeq]
    exact hωapprox
  have hContAE :
      ∀ᵐ ω ∂μ, Continuous (processPath X ω) := by
    -- Proof comment: the horizontal Brownian coordinate has almost surely continuous sample
    -- paths.
    simpa [HasAlmostSurelyContinuousPaths, processPath, X] using
      (hW.isBrownianMotion 0).continuous_paths
  have hSampleEvalAemeas :
      AEMeasurable (fun ω ↦ processPath X ω (τA ω)) μ := by
    -- Proof comment: the exact reflected-clock evaluation is the a.e. limit of the measurable
    -- simple-clock samples at the same `untopA` clock.
    refine aemeasurable_of_tendsto_metrizable_ae' hApproxMeas ?_
    filter_upwards [hContAE, hApproxClock] with ω hωcont hωapprox
    exact hωcont.continuousAt.tendsto.comp hωapprox
  -- Proof comment: after unfolding `processPath`, the sampled horizontal coordinate is exactly
  -- evaluation of the horizontal path at the measurable `untopA` clock.
  simpa [τ, τA, X, Bminus, processPath_apply] using hSampleEvalAemeas

/-- Helper for Exercise 25.4.1: the sampled horizontal coordinate at the reflected vertical
hitting clock has characteristic function `u ↦ exp (-(x₂) |u|)`. -/
lemma charFun_horizontalSampleAtReflectedVerticalClock
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) (u : ℝ) :
    charFun
      (Measure.map
        (fun ω ↦
          W
            (brownianLevelHittingTime
              (brownianScaling (fun t ω ↦ W t ω 1) (-1)) (x 1) ω).untopA
            ω 0) μ) u =
      Complex.exp (-(x 1) * |u|) := by
  -- Route correction: the failed product-space owner route asked Lean to understand the raw
  -- variable-time evaluation map on path space. The closing proof now stays on `Ω`, first for
  -- finite-valued simple clocks and then by dominated convergence along simple approximants of the
  -- reflected clock.
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  let τ : Ω → ENNReal := brownianLevelHittingTime Bminus (x 1)
  let τNN : Ω → NNReal := fun ω ↦ (τ ω).toNNReal
  let X : NNReal → Ω → ℝ := fun t ω ↦ W t ω 0
  let sample : Ω → ℝ := fun ω ↦ W (τ ω).untopA ω 0
  have hscaleTime : brownianScalingTime (-1 : ℝ) = 1 := by
    apply NNReal.coe_injective
    change (-1 : ℝ) ^ 2 = 1
    norm_num
  have hBminus : IsBrownianMotion μ Bminus := by
    -- Proof comment: the reflected vertical coordinate is Brownian by the scaling theorem.
    simpa [Bminus, brownianScaling, hscaleTime] using
      (IsBrownianMotion.scaling (hW.isBrownianMotion 1) (K := (-1 : ℝ)) (by norm_num))
  have hτNNAemeas : AEMeasurable τNN μ := by
    -- Proof comment: the reflected `NNReal` clock is the measurable image of the real-valued
    -- hitting clock.
    simpa [τNN] using aemeasurable_levelHittingTime_toNNReal (μ := μ) (B := Bminus) hBminus (x 1)
  let τNNm : Ω → NNReal := hτNNAemeas.mk τNN
  have hτNNae : τNN =ᵐ[μ] τNNm := hτNNAemeas.ae_eq_mk
  have hτNNMeas : Measurable τNNm := hτNNAemeas.measurable_mk
  let σ : ℕ → MeasureTheory.SimpleFunc Ω NNReal := fun n ↦
    MeasureTheory.SimpleFunc.approxOn τNNm hτNNMeas (Set.range τNNm ∪ {0}) 0 (by simp) n
  have hPathMeas : Measurable (processPath X) := by
    -- Proof comment: the horizontal Brownian coordinate has a measurable full path map.
    exact
      (IsBrownianMotionStartedAt.measurable_processPath
        (show IsBrownianMotionStartedAt μ X 0 from inferInstance))
  have hActualAemeas : AEMeasurable sample μ := by
    -- Proof comment: move measurability to a continuous modification of the two coordinates, then
    -- transport it back to the exact reflected-clock sample by pathwise equality on a full-measure
    -- set.
    simpa [sample, τ, Bminus] using
      aemeasurable_horizontalSampleAtReflectedVerticalClock
        (μ := μ) (W := W) hW hx
  have hClockIndep :
      IndepFun τNN (processPath X) μ := by
    have hIndepReal :
        IndepFun (processPath X) (fun ω ↦ (τ ω).toReal) μ := by
      -- Proof comment: reuse the already-established independence of the horizontal Brownian path
      -- and the reflected vertical hitting clock.
      simpa [τ, X, processPath] using
        (horizontalBrownianPath_indep_reflectedVerticalClock
          (μ := μ) (W := W) hW (x := x))
    have hIndepNN :
        IndepFun (processPath X) τNN μ := by
      -- Proof comment: postcompose the real-valued reflected clock with `Real.toNNReal`.
      refine
        (hIndepReal.comp measurable_id measurable_real_toNNReal).congr
          (ae_eq_refl _) ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simp [τNN, Function.comp]
    exact hIndepNN.symm
  have hClockIndepRep :
      IndepFun τNNm (processPath X) μ :=
    hClockIndep.congr hτNNae (ae_eq_refl _)
  have hApproxIndep :
      ∀ n, IndepFun (fun ω ↦ σ n ω) (processPath X) μ := by
    intro n
    let φ : MeasureTheory.SimpleFunc NNReal NNReal :=
      MeasureTheory.SimpleFunc.approxOn
        (fun s : NNReal ↦ s)
        measurable_id
        (Set.range τNNm ∪ {0})
        0
        (by simp)
        n
    -- Proof comment: the simple-clock approximants are measurable postcompositions of the
    -- reflected clock, so independence survives the approximation step.
    have hComp :
        IndepFun (φ ∘ τNNm) (processPath X) μ := by
      simpa [Function.comp] using hClockIndepRep.comp φ.measurable measurable_id
    simpa [σ, φ, Function.comp] using hComp
  have hApproxClock :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τNNm ω)) := by
    exact Filter.Eventually.of_forall fun ω ↦
      MeasureTheory.SimpleFunc.tendsto_approxOn hτNNMeas (by simp)
        (subset_closure (Or.inl ⟨ω, rfl⟩))
  have hContAE :
      ∀ᵐ ω ∂μ, Continuous (processPath X ω) := by
    -- Proof comment: the horizontal Brownian coordinate has almost surely continuous paths.
    simpa [HasAlmostSurelyContinuousPaths, processPath, X] using
      (hW.isBrownianMotion 0).continuous_paths
  have hSampleAE :
      sample =ᵐ[μ] fun ω ↦ processPath X ω (τNNm ω) := by
    -- Proof comment: this is the fixed `τNN/processPath` normal form used to pass from simple
    -- clocks to the exact reflected clock.
    have hSampleAE0 :
        sample =ᵐ[μ] fun ω ↦ processPath X ω (τNN ω) := by
      simpa [sample, τ, τNN, X, Bminus] using
        horizontalSampleAtReflectedClock_ae_eq_processPathEvalToNNReal
          (μ := μ) (W := W) hW hx
    refine hSampleAE0.trans ?_
    filter_upwards [hτNNae] with ω hω
    simp [hω]
  let charKernel : ℝ → ℂ := fun r ↦ Complex.exp (u * r * Complex.I)
  have hCharKernelCont : Continuous charKernel := by
    -- Proof comment: the real characteristic-function kernel is continuous in the sampled value.
    fun_prop
  let charIntegrand : ℕ → Ω → ℂ := fun n ω ↦
    charKernel (processPath X ω (σ n ω))
  let sampleIntegrand : Ω → ℂ := fun ω ↦ charKernel (sample ω)
  have hCharMeas :
      ∀ n, AEStronglyMeasurable (charIntegrand n) μ := by
    intro n
    -- Proof comment: each approximating sample is measurable because the clock is simple.
    have hSampleMeas : Measurable (fun ω ↦ processPath X ω (σ n ω)) := by
      exact measurable_processPathEval_simpleClock hPathMeas (σ n)
    simpa [charIntegrand] using
      (hCharKernelCont.measurable.comp hSampleMeas).aestronglyMeasurable
  have hCharBound :
      ∀ n, ∀ᵐ ω ∂μ, ‖charIntegrand n ω‖ ≤ (1 : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [charIntegrand, charKernel, mul_assoc] using
        (Complex.norm_exp_ofReal_mul_I (u * processPath X ω (σ n ω))).le
  have hCharPointwise :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ charIntegrand n ω) atTop (𝓝 (sampleIntegrand ω)) := by
    filter_upwards [hContAE, hApproxClock, hSampleAE] with ω hωcont hωapprox hωsample
    have hEval :
        Tendsto (fun n ↦ processPath X ω (σ n ω)) atTop
          (𝓝 (processPath X ω (τNNm ω))) := by
      exact hωcont.continuousAt.tendsto.comp hωapprox
    -- Proof comment: continuity of the complex exponential transfers the pathwise convergence of
    -- the sampled horizontal coordinate to the characteristic-function integrand.
    simpa [charIntegrand, sampleIntegrand, charKernel, hωsample] using
      (hCharKernelCont.continuousAt.tendsto.comp hEval)
  have hCharIntegralLimit :
      Tendsto (fun n ↦ ∫ ω, charIntegrand n ω ∂μ) atTop (𝓝 (∫ ω, sampleIntegrand ω ∂μ)) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ ↦ (1 : ℝ))
        hCharMeas
        (integrable_const 1)
        hCharBound
        hCharPointwise
  have hTargetIntegral :
      charFun (Measure.map sample μ) u = ∫ ω, sampleIntegrand ω ∂μ := by
    rw [MeasureTheory.charFun_apply_real]
    have hIntegrandAesm :
        AEStronglyMeasurable charKernel
          (Measure.map sample μ) := by
      exact hCharKernelCont.measurable.aestronglyMeasurable
    -- Proof comment: the exact reflected-clock sample is `AEMeasurable`, so its characteristic
    -- function may be pulled back to the base space.
    simpa [sampleIntegrand, charKernel, sample, Function.comp] using
      (integral_map
        (μ := μ)
        (φ := sample)
        hActualAemeas
        (f := charKernel)
        hIntegrandAesm)
  have hLeftLimit :
      Tendsto
        (fun n ↦ charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u)
        atTop
        (𝓝 (charFun (Measure.map sample μ) u)) := by
    have hApproxCharEq :
        ∀ n,
          charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u =
            ∫ ω, charIntegrand n ω ∂μ := by
      intro n
      rw [MeasureTheory.charFun_apply_real]
      have hSampleMeas : Measurable (fun ω ↦ processPath X ω (σ n ω)) := by
        exact measurable_processPathEval_simpleClock hPathMeas (σ n)
      have hIntegrandAesm :
          AEStronglyMeasurable charKernel
            (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) := by
        exact hCharKernelCont.measurable.aestronglyMeasurable
      simpa [charIntegrand, charKernel, Function.comp] using
        (integral_map
          (μ := μ)
          (φ := fun ω ↦ processPath X ω (σ n ω))
          hSampleMeas.aemeasurable
          (f := charKernel)
          hIntegrandAesm)
    -- Proof comment: the left-hand characteristic functions inherit the dominated-convergence
    -- limit after each stage is rewritten as an integral over `Ω`.
    have hApproxCharSeq :
        (fun n ↦ charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u) =
          fun n ↦ ∫ ω, charIntegrand n ω ∂μ := by
      funext n
      exact hApproxCharEq n
    simpa [hApproxCharSeq, hTargetIntegral] using hCharIntegralLimit
  let laplaceIntegrand : NNReal → ℂ := fun s ↦
    (Real.exp (-((u ^ 2 / 2 : ℝ) * (s : ℝ))) : ℂ)
  have hLaplaceCont : Continuous laplaceIntegrand := by
    -- Proof comment: the Laplace integrand is a continuous function of the `NNReal` clock.
    fun_prop
  have hLaplacePointwise :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ laplaceIntegrand (σ n ω)) atTop (𝓝 (laplaceIntegrand (τNN ω))) := by
    filter_upwards [hApproxClock, hτNNae] with ω hωapprox hωτ
    simpa [hωτ] using hLaplaceCont.continuousAt.tendsto.comp hωapprox
  have hLaplaceBound :
      ∀ n, ∀ᵐ ω ∂μ, ‖laplaceIntegrand (σ n ω)‖ ≤ (1 : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hs_nonneg : 0 ≤ ((σ n ω : NNReal) : ℝ) := (σ n ω).2
      have hu_nonneg : 0 ≤ (u ^ 2 / 2 : ℝ) := by positivity
      have hle : -((u ^ 2 / 2 : ℝ) * ((σ n ω : NNReal) : ℝ)) ≤ 0 := by
        nlinarith
      have hExpLe : Real.exp (-((u ^ 2 / 2 : ℝ) * ((σ n ω : NNReal) : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr hle
      change ‖(Real.exp (-((u ^ 2 / 2 : ℝ) * ((σ n ω : NNReal) : ℝ))) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hExpLe
  have hLaplaceMeas :
      ∀ n, AEStronglyMeasurable (fun ω ↦ laplaceIntegrand (σ n ω)) μ := by
    intro n
    exact (hLaplaceCont.measurable.comp (σ n).measurable).aestronglyMeasurable
  have hLaplaceIntegralLimit :
      Tendsto (fun n ↦ ∫ ω, laplaceIntegrand (σ n ω) ∂μ)
        atTop
        (𝓝 (∫ ω, laplaceIntegrand (τNN ω) ∂μ)) := by
    exact
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ ↦ (1 : ℝ))
        hLaplaceMeas
        (integrable_const 1)
        hLaplaceBound
        hLaplacePointwise
  have hLaplaceFactor :
      ∫ ω, laplaceIntegrand (τNN ω) ∂μ = Complex.exp (-(x 1) * |u|) := by
    have hIntegrandAesm :
        AEStronglyMeasurable laplaceIntegrand (Measure.map τNN μ) := by
      exact hLaplaceCont.measurable.aestronglyMeasurable
    calc
      ∫ ω, laplaceIntegrand (τNN ω) ∂μ =
          ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map τNN μ) := by
            simpa [laplaceIntegrand, Function.comp] using
              (integral_map
                (μ := μ)
                (φ := τNN)
                hτNNAemeas
                (f := laplaceIntegrand)
                hIntegrandAesm).symm
      _ = Complex.exp (-(x 1) * |u|) := by
            simpa [laplaceIntegrand, τNN, τ, Bminus] using
              reflectedClockToNNReal_laplaceFactor
                (μ := μ) (W := W) hW (x := x) hx u
  have hRightLimit :
      Tendsto
        (fun n ↦
          ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map (fun ω ↦ σ n ω) μ))
        atTop
        (𝓝 (Complex.exp (-(x 1) * |u|))) := by
    have hApproxLaplaceEq :
        ∀ n,
          ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map (fun ω ↦ σ n ω) μ) =
            ∫ ω, laplaceIntegrand (σ n ω) ∂μ := by
      intro n
      have hIntegrandAesm :
          AEStronglyMeasurable laplaceIntegrand (Measure.map (fun ω ↦ σ n ω) μ) := by
        exact hLaplaceCont.measurable.aestronglyMeasurable
      simpa [laplaceIntegrand, Function.comp] using
        (integral_map
          (μ := μ)
          (φ := fun ω ↦ σ n ω)
          (σ n).measurable.aemeasurable
          (f := laplaceIntegrand)
          hIntegrandAesm)
    -- Proof comment: the clock-side Gaussian mixture integral converges to the reflected-clock
    -- Laplace factor by dominated convergence and the one-dimensional hitting-time transform.
    have hApproxLaplaceSeq :
        (fun n ↦ ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map (fun ω ↦ σ n ω) μ)) =
          fun n ↦ ∫ ω, laplaceIntegrand (σ n ω) ∂μ := by
      funext n
      exact hApproxLaplaceEq n
    simpa [hApproxLaplaceSeq, hLaplaceFactor] using hLaplaceIntegralLimit
  have hApproxFormula :
      ∀ n,
        charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u =
          ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map (fun ω ↦ σ n ω) μ) := by
    intro n
    simpa [X, laplaceIntegrand] using
      charFun_horizontalSampleAtIndependentSimpleClock
        (μ := μ) (W := W) hW (σ n) (hApproxIndep n) u
  have hLeftToLaplace :
      Tendsto
        (fun n ↦ charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u)
        atTop
        (𝓝 (Complex.exp (-(x 1) * |u|))) := by
    have hApproxFormulaSeq :
        (fun n ↦ charFun (Measure.map (fun ω ↦ processPath X ω (σ n ω)) μ) u) =
          fun n ↦ ∫ s : NNReal, laplaceIntegrand s ∂(Measure.map (fun ω ↦ σ n ω) μ) := by
      funext n
      exact hApproxFormula n
    simpa [hApproxFormulaSeq] using hRightLimit
  -- Proof comment: the simple-clock characteristic functions have only one limit, so the exact
  -- reflected-clock characteristic function must equal the reflected-clock Laplace factor.
  have hLimitEq :
      charFun (Measure.map sample μ) u = Complex.exp (-(x 1) * |u|) :=
    tendsto_nhds_unique hLeftLimit hLeftToLaplace
  simpa [sample, τ, Bminus] using hLimitEq
/-- Helper for Exercise 25.4.1: the centered horizontal coordinate at the upper-half-plane exit
time has the centered Cauchy law with scale `x₂`. -/
theorem upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    Measure.map
        (fun ω ↦
          W
            (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω).untopA
            ω 0)
        μ =
      cauchyMeasure 0 (Real.toNNReal (x 1)) := by
  let Bminus : NNReal → Ω → ℝ := brownianScaling (fun t ω ↦ W t ω 1) (-1)
  have hRewrite :
      Measure.map
          (fun ω ↦
            W
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω).untopA
              ω 0)
          μ =
        Measure.map (fun ω ↦ W (brownianLevelHittingTime Bminus (x 1) ω).untopA ω 0) μ := by
    -- Proof comment: replace the planar exit clock by the already-proved reflected vertical
    -- hitting clock.
    exact Measure.map_congr <|
      upperHalfPlaneExitHorizontal_ae_eq_reflectedVerticalSample
        (μ := μ) (W := W) hW hx
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  -- Proof comment: the centered exit law is determined by its characteristic function, and the
  -- previous theorem computes exactly the Cauchy characteristic function at every frequency.
  apply Measure.ext_of_charFun
  ext u
  rw [hRewrite]
  rw [charFun_horizontalSampleAtReflectedVerticalClock (μ := μ) (W := W) hW hx u]
  simpa using (charFun_centeredCauchyMeasure (x 1) hx_second u).symm

-- TODO for Exercise 25.4.1: once the centered exit law is restored, translate it by the
-- deterministic first coordinate `x₁` to recover the stopped-coordinate law.
/-- The first coordinate of the stopped planar Brownian path at the first exit time from the upper
half-plane has the Cauchy law with location parameter `x₁` and scale parameter `x₂`. -/
theorem upperHalfPlaneStoppedFirstCoordinate_eq_cauchyMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : VectorProcess}
    (hW : IsStandardBrownianMotionVector μ W) {x : State}
    (hx : x ∈ upperHalfPlane) :
    Measure.map
        (fun ω ↦
          stoppedValue
              (fun t ω ↦ x + W t ω)
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal)) ω
            0)
        μ =
      cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
  let τ : Ω → ENNReal := hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal)
  have hx_second : 0 < x 1 := second_pos_of_mem_upperHalfPlane hx
  have hcenteredAemeas :
      AEMeasurable (fun ω ↦ W (τ ω).untopA ω 0) μ := by
    -- Proof comment: the centered exit law is a genuine probability measure, so its sampled
    -- horizontal coordinate cannot be nonmeasurable, because `Measure.map` would then collapse to
    -- `0`.
    by_contra hnot
    have hmap_zero : Measure.map (fun ω ↦ W (τ ω).untopA ω 0) μ = 0 := by
      simp [hnot]
    have hcauchy_ne_zero : cauchyMeasure 0 (Real.toNNReal (x 1)) ≠ 0 := by
      intro hzero
      have huniv : (cauchyMeasure 0 (Real.toNNReal (x 1)) : Measure ℝ) Set.univ = 0 := by
        simp [hzero]
      simp at huniv
    exact
      hcauchy_ne_zero <|
        by
          simpa [τ] using
            (upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure
              (μ := μ) (W := W) hW hx).symm.trans hmap_zero
  have hstopped_eq :
      (fun ω ↦
        stoppedValue
          (fun t ω ↦ x + W t ω)
          τ ω 0) =
        (fun ω ↦ x 0 + W (τ ω).untopA ω 0) := by
    -- Proof comment: the first coordinate of the stopped translated path is the fixed shift `x₁`
    -- plus the stopped horizontal Brownian coordinate.
    funext ω
    simp [τ, stoppedValue]
  calc
    Measure.map
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ x + W t ω)
            τ ω 0)
        μ =
      Measure.map (fun ω ↦ x 0 + W (τ ω).untopA ω 0) μ := by
        exact Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ by
          simpa [hstopped_eq] using congrFun hstopped_eq ω
    _ =
      Measure.map (fun y : ℝ ↦ y + x 0)
        (Measure.map (fun ω ↦ W (τ ω).untopA ω 0) μ) := by
          rw [show (fun ω ↦ x 0 + W (τ ω).untopA ω 0) =
              (fun y : ℝ ↦ y + x 0) ∘ (fun ω ↦ W (τ ω).untopA ω 0) by
                funext ω
                simp [Function.comp, add_comm]]
          exact
            (AEMeasurable.map_map_of_aemeasurable
              (μ := μ) (f := fun ω ↦ W (τ ω).untopA ω 0)
              (g := fun y : ℝ ↦ y + x 0) (by fun_prop) hcenteredAemeas).symm
    _ = Measure.map (fun y : ℝ ↦ y + x 0) (cauchyMeasure 0 (Real.toNNReal (x 1))) := by
          rw [upperHalfPlaneExitHorizontal_eq_centeredCauchyMeasure
            (μ := μ) (W := W) hW hx]
    _ = cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
          simpa [add_comm] using
            map_add_const_centeredCauchyMeasure (x 0) (x 1) hx_second

-- TODO for Exercise 25.4.1: finish the harmonic-measure identification by transporting the
-- frontier-valued exit map to the stopped planar Brownian path on the finite-exit event and then
-- apply the stopped-coordinate Cauchy law above.
/-- Exercise 25.4.1: for planar Brownian motion started at `x = (x₁, x₂)` in the open upper
half-plane `G = ℝ × (0, ∞)`, the harmonic measure on the textbook boundary line `ℝ`, viewed
through the coordinate map `z ↦ z₁` on `frontier G`, is the Cauchy distribution with location
parameter `x₁` and scale parameter `x₂`, provided `exitValue` is a measurable frontier-valued exit
map that agrees with the stopped Brownian path whenever the exit time is finite. -/
theorem upperHalfPlaneHarmonicMeasure_eq_cauchyMeasure
    {P : ProbabilityMeasure Ω} {W : VectorProcess}
    {x : State} (hx : x ∈ upperHalfPlane)
    (exitValue : Ω → frontier upperHalfPlane)
    (hExitMeas : Measurable exitValue)
    (hExit :
      ∀ ω : Ω,
        hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω < ⊤ →
          (exitValue ω : State) =
            stoppedValue
              (fun t ω ↦ x + W t ω)
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal))
              ω)
    (hW : IsStandardBrownianMotionVector (P : Measure Ω) W) :
    Measure.map (fun z : frontier upperHalfPlane ↦ (z : State) 0)
      (harmonicMeasure
        (fun _ : State ↦ P)
        upperHalfPlane
        exitValue
        hExitMeas
        ⟨x, hx⟩ : Measure (frontier upperHalfPlane)) =
      cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
  have hExitTimeAe :
      ∀ᵐ ω ∂(P : Measure Ω),
        hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal) ω < ⊤ :=
    upperHalfPlaneExitTime_ae_lt_top
      (μ := (P : Measure Ω)) (W := W) (hW := hW.isBrownianMotion 1) hx
  have hFirstCoordAe :
      (fun ω ↦ (exitValue ω : State) 0) =ᵐ[(P : Measure Ω)]
        (fun ω ↦
          stoppedValue
            (fun t ω ↦ x + W t ω)
            (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal))
            ω 0) := by
    -- Proof comment: on the almost-sure finite-exit event, the prescribed boundary exit map
    -- agrees with the stopped planar Brownian path, so their first coordinates agree as well.
    filter_upwards [hExitTimeAe] with ω hω
    exact congrArg (fun z : State ↦ z 0) (hExit ω hω)
  calc
    Measure.map (fun z : frontier upperHalfPlane ↦ (z : State) 0)
        (harmonicMeasure
          (fun _ : State ↦ P)
          upperHalfPlane
          exitValue
          hExitMeas
          ⟨x, hx⟩ : Measure (frontier upperHalfPlane)) =
      Measure.map (fun ω ↦ (exitValue ω : State) 0) (P : Measure Ω) := by
          exact
            map_upperHalfPlaneBoundary_harmonicMeasure
              (P := P) hx exitValue hExitMeas
    _ = Measure.map
          (fun ω ↦
            stoppedValue
              (fun t ω ↦ x + W t ω)
              (hittingAfter (fun t ω ↦ x + W t ω) upperHalfPlaneᶜ (0 : NNReal))
              ω 0)
          (P : Measure Ω) := by
            exact Measure.map_congr hFirstCoordAe
    _ = cauchyMeasure (x 0) (Real.toNNReal (x 1)) := by
          exact upperHalfPlaneStoppedFirstCoordinate_eq_cauchyMeasure
            (μ := (P : Measure Ω)) (W := W) hW hx

end ProbabilityTheory
