module

public import ReasLib.Analysis.Asymptotics.PositiveProduct
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeLimit

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- A positive sequence starting at one stays in a common interval when its absolute successive
ratio deviations have small total mass. -/
private lemma amplitude_mem_uniform_interval_of_ratio_deviation
    {a d : ℕ → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_zero : a 0 = 1)
    (hd_nonneg : ∀ j, 0 ≤ d j) (hd_le_one : ∀ j, d j ≤ 1)
    (hdev : ∀ j, |a (j + 1) / a j - 1| ≤ d j)
    (hd_summable : Summable d) (hd_tsum : (∑' j, d j) ≤ 1 / 4) :
    ∀ j, a j ∈ Set.Icc (3 / 4 : ℝ) (Real.exp (1 / 4)) := by
  have hprod (n : ℕ) : a n = ∏ i ∈ Finset.range n, (a (i + 1) / a i) := by
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.prod_empty, ha_zero]
    | succ n ih =>
        rw [Finset.prod_range_succ, ← ih]
        have hne : a n ≠ 0 := ne_of_gt (ha_pos n)
        field_simp [hne]
  have hsum_range (n : ℕ) : (∑ i ∈ Finset.range n, d i) ≤ 1 / 4 := by
    exact (hd_summable.sum_le_tsum (Finset.range n)
      (fun i _ ↦ hd_nonneg i)).trans hd_tsum
  have hprod_one_sub_ge (s : Finset ℕ) :
      1 - (∑ i ∈ s, d i) ≤ ∏ i ∈ s, (1 - d i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx]
        have hsum_nonneg : 0 ≤ ∑ i ∈ s, d i :=
          Finset.sum_nonneg (fun i hi ↦ hd_nonneg i)
        have hfactor_nonneg : 0 ≤ 1 - d x := sub_nonneg.mpr (hd_le_one x)
        have hmul := mul_le_mul_of_nonneg_right ih hfactor_nonneg
        have hcross : 0 ≤ d x * (∑ i ∈ s, d i) :=
          mul_nonneg (hd_nonneg x) hsum_nonneg
        nlinarith
  intro n
  have hratio_pos (i : ℕ) : 0 < a (i + 1) / a i :=
    div_pos (ha_pos (i + 1)) (ha_pos i)
  have hratio_bounds (i : ℕ) :
      1 - d i ≤ a (i + 1) / a i ∧ a (i + 1) / a i ≤ 1 + d i := by
    have habs := (abs_le.mp (hdev i))
    constructor
    · linarith
    · linarith
  have hupper_prod :
      (∏ i ∈ Finset.range n, (a (i + 1) / a i)) ≤
        ∏ i ∈ Finset.range n, (1 + d i) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (hratio_pos i).le
    · intro i hi
      exact (hratio_bounds i).2
  have hupper_exp :
      (∏ i ∈ Finset.range n, (1 + d i)) ≤
        Real.exp (∑ i ∈ Finset.range n, d i) := by
    exact Real.prod_one_add_le_exp_sum (Finset.range n) (fun i ↦ hd_nonneg i)
  have hupper : a n ≤ Real.exp (1 / 4) := by
    rw [hprod]
    exact hupper_prod.trans (hupper_exp.trans
      (Real.exp_le_exp.mpr (hsum_range n)))
  have hlower_prod :
      (∏ i ∈ Finset.range n, (1 - d i)) ≤
        ∏ i ∈ Finset.range n, (a (i + 1) / a i) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact sub_nonneg.mpr (hd_le_one i)
    · intro i hi
      exact (hratio_bounds i).1
  have hlower : (3 / 4 : ℝ) ≤ a n := by
    rw [hprod]
    have hsum_lower : (3 / 4 : ℝ) ≤ 1 - (∑ i ∈ Finset.range n, d i) := by
      linarith [hsum_range n]
    exact hsum_lower.trans ((hprod_one_sub_ge (Finset.range n)).trans hlower_prod)
  exact ⟨hlower, hupper⟩

/-- A common positive interval contains every amplitude and its limit on each sufficiently
small invariant slow-curve orbit with the prescribed jets. -/
theorem slowCurveAmplitudeUniformBounds (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Gmin > 0, ∃ Gmax, Gmin ≤ Gmax ∧
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∃ Glim ∈ Set.Icc Gmin Gmax,
          Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
            ∀ j : ℕ, (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
  obtain ⟨ηDrift, hηDrift, hDriftMod, hDrift⟩ :=
    slowCurveAmplitudeDriftModulus p h h_invariant h_pJet h_hJet
  obtain ⟨ηTail, hηTail, C₄, hC₄, C₆, hC₆, hTail⟩ :=
    DFP.TwoLeg.slowCurvePowerTailBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      ηGraph hηGraph
  obtain ⟨ηLimit, hηLimit, hLimit⟩ :=
    slowCurveAmplitudeExistsPositiveLimit p h h_invariant h_pJet h_hJet
  let ωA : ℝ → ℝ := Asymptotics.uniformRemainderModulus
    (fun _ : Unit ↦ fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) Set.univ 4
  have hDriftSpec :=
    (Asymptotics.IsUniformRemainderModulusOn.spec _ _ _ _ _).mp hDriftMod
  have hωsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωA η < (1 / 2 : ℝ) := by
    have hhalfpos : 0 < (1 / 2 : ℝ) := by norm_num
    exact (tendsto_order.1 hDriftSpec.2.2.1).2 _ hhalfpos
  have hηsmall : ∃ η ∈ Set.Ioc (0 : ℝ) ηDrift, ωA η < (1 / 2 : ℝ) := by
    have hmem : Set.Ioc (0 : ℝ) ηDrift ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT hηDrift.1
    have hinter : ∀ᶠ η in 𝓝[>] (0 : ℝ),
        ωA η < (1 / 2 : ℝ) ∧ η ∈ Set.Ioc 0 ηDrift := by
      filter_upwards [hωsmall, hmem] with η hω hη
      exact ⟨hω, hη⟩
    obtain ⟨η, hη⟩ := Filter.Eventually.exists hinter
    refine ⟨η, hη.2, ?_⟩
    exact hη.1
  obtain ⟨ηω, hηω, hωη⟩ := hηsmall
  let ηMass := (28 * C₄)⁻¹
  let εbar := min (min (min (min ηω ηTail) ηValid) ηLimit) ηMass
  have hηMass_pos : 0 < ηMass := by
    dsimp [ηMass]
    positivity
  have hεbar_pos : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (lt_min (lt_min (lt_min hηω.1 hηTail) hηValid.1) hηLimit) hηMass_pos
  have hεbar_le_ηω : εbar ≤ ηω := by
    dsimp [εbar]
    calc
      min (min (min (min ηω ηTail) ηValid) ηLimit) ηMass ≤
          min (min (min ηω ηTail) ηValid) ηLimit := min_le_left _ _
      _ ≤ min (min ηω ηTail) ηValid := min_le_left _ _
      _ ≤ min ηω ηTail := min_le_left _ _
      _ ≤ ηω := min_le_left _ _
  have hεbar_le_tail : εbar ≤ ηTail := by
    dsimp [εbar]
    calc
      min (min (min (min ηω ηTail) ηValid) ηLimit) ηMass ≤
          min (min (min ηω ηTail) ηValid) ηLimit := min_le_left _ _
      _ ≤ min (min ηω ηTail) ηValid := min_le_left _ _
      _ ≤ min ηω ηTail := min_le_left _ _
      _ ≤ ηTail := min_le_right _ _
  have hεbar_le_valid : εbar ≤ ηValid := by
    dsimp [εbar]
    calc
      min (min (min (min ηω ηTail) ηValid) ηLimit) ηMass ≤
          min (min (min ηω ηTail) ηValid) ηLimit := min_le_left _ _
      _ ≤ min (min ηω ηTail) ηValid := min_le_left _ _
      _ ≤ ηValid := min_le_right _ _
  have hεbar_le_limit : εbar ≤ ηLimit := by
    dsimp [εbar]
    calc
      min (min (min (min ηω ηTail) ηValid) ηLimit) ηMass ≤
          min (min (min ηω ηTail) ηValid) ηLimit := min_le_left _ _
      _ ≤ ηLimit := min_le_right _ _
  have hεbar_le_mass : εbar ≤ ηMass := by
    dsimp [εbar]
    exact min_le_right _ _
  have hεbar_lt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt (hεbar_le_ηω.trans hηω.2) hηDrift.2
  refine ⟨εbar, ⟨hεbar_pos, hεbar_lt⟩, (3 / 4 : ℝ), ?_,
    Real.exp (1 / 4), ?_, ?_⟩
  · norm_num
  · have hexp := Real.add_one_le_exp (1 / 4 : ℝ)
    linarith
  · intro ε₀ hε₀
    dsimp
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    have hε₀ω : ε₀ ∈ Set.Ioc 0 ηω :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_ηω⟩
    have hε₀Tail : ε₀ ∈ Set.Ioc 0 ηTail :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_tail⟩
    have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_valid⟩
    have hε₀Limit : ε₀ ∈ Set.Ioc 0 ηLimit :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_limit⟩
    obtain ⟨Glim, hGlim_pos, hGlim_tendsto⟩ := hLimit ε₀ hε₀Limit
    have hvalid (j : ℕ) : State.PhaseValidity (orbit.state j) := by
      simpa [orbit] using hValid ε₀ hε₀Valid j
    let a : ℕ → ℝ := fun j ↦ (orbit.state j).amplitude
    let u : ℕ → ℝ := fun j ↦ (orbit.state j).ε ^ 4
    let d : ℕ → ℝ := fun j ↦ |a (j + 1) / a j - 1|
    have ha_pos : ∀ j, 0 < a j := by
      intro j
      exact (hvalid j).amplitude_pos
    have ha_zero : a 0 = 1 := by
      dsimp [a, orbit]
      rw [ofSlowCurve_zero, State.initial_amplitude]
    have hεeq (j : ℕ) :
        (orbit.state j).ε = (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      have hcoord' :
          (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
        simpa [orbit] using hcoord
      have hcoord_fst :
          ((orbit.state j).ε, (orbit.state j).p, (orbit.state j).h) =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
        simpa only [State.coordinates_def] using hcoord'
      exact congrArg Prod.fst hcoord_fst
    have hu_nonneg : ∀ j, 0 ≤ u j := by
      intro j
      exact pow_nonneg (le_of_lt (hvalid j).ε_pos) 4
    have htail0 := hTail ε₀ hε₀Tail 0
    have hεsummable :
        Summable (fun k : ℕ ↦
          (DFP.TwoLeg.stateMap^[0 + k] (ε₀, p ε₀, h ε₀)).1 ^ 4) := htail0.1.1
    have husummable : Summable u := by
      refine hεsummable.congr ?_
      intro k
      dsimp only [u]
      rw [hεeq k]
      simp only [zero_add]
    have htail_le :
        (∑' k : ℕ, (DFP.TwoLeg.stateMap^[0 + k]
          (ε₀, p ε₀, h ε₀)).1 ^ 4) ≤
          C₄ * (DFP.TwoLeg.stateMap^[0] (ε₀, p ε₀, h ε₀)).1 := htail0.1.2
    have husum_le : (∑' k : ℕ, u k) ≤ C₄ * ε₀ := by
      calc
        ∑' k : ℕ, u k =
            ∑' k : ℕ, (DFP.TwoLeg.stateMap^[0 + k]
              (ε₀, p ε₀, h ε₀)).1 ^ 4 := by
                apply tsum_congr
                intro k
                dsimp only [u]
                rw [hεeq k]
                simp only [zero_add]
        _ ≤ C₄ * (DFP.TwoLeg.stateMap^[0] (ε₀, p ε₀, h ε₀)).1 := htail_le
        _ = C₄ * ε₀ := by simp
    have hmass : 7 * (C₄ * ε₀) ≤ (1 / 4 : ℝ) := by
      have hscale : ε₀ ≤ (28 * C₄)⁻¹ := hε₀.2.trans hεbar_le_mass
      have hmul : C₄ * ε₀ ≤ C₄ * (28 * C₄)⁻¹ :=
        mul_le_mul_of_nonneg_left hscale hC₄.le
      have hseven_nonneg : 0 ≤ (7 : ℝ) := by norm_num
      calc
        7 * (C₄ * ε₀) ≤ 7 * (C₄ * (28 * C₄)⁻¹) :=
          mul_le_mul_of_nonneg_left hmul hseven_nonneg
        _ = (1 / 4 : ℝ) := by
          field_simp [ne_of_gt hC₄]
          ring
    have hdev_bound (j : ℕ) : d j ≤ 7 * u j := by
      have hratio := hDrift ηω hηω ε₀ hε₀ω j
      have hratio' :
          |a (j + 1) / a j - (1 - (13 / 2) * u j)| ≤ ωA ηω * u j := by
        simpa [a, u, orbit, ωA] using hratio
      have hu_pos : 0 < u j := pow_pos (hvalid j).ε_pos 4
      have hωmul : ωA ηω * u j ≤ (1 / 2 : ℝ) * u j :=
        mul_le_mul_of_nonneg_right hωη.le hu_pos.le
      have h13_nonneg : 0 ≤ (13 / 2 : ℝ) := by norm_num
      have hcenter :
          |(1 - (13 / 2) * u j) - 1| = (13 / 2 : ℝ) * u j := by
        have hcenter_arg : (1 - (13 / 2) * u j) - 1 = -(13 / 2) * u j := by
          ring
        rw [hcenter_arg, abs_mul, abs_neg, abs_of_nonneg h13_nonneg,
          abs_of_nonneg (hu_nonneg j)]
      dsimp [d]
      calc
        |a (j + 1) / a j - 1| =
            |(a (j + 1) / a j - (1 - (13 / 2) * u j)) +
              ((1 - (13 / 2) * u j) - 1)| := by
                congr 1
                ring
        _ ≤ |a (j + 1) / a j - (1 - (13 / 2) * u j)| +
            |(1 - (13 / 2) * u j) - 1| := abs_add_le _ _
        _ ≤ ωA ηω * u j + (13 / 2 : ℝ) * u j :=
          add_le_add hratio' (le_of_eq hcenter)
        _ ≤ 7 * u j := by nlinarith [hωmul]
    have hdu_summable : Summable d := by
      exact (husummable.mul_left 7).of_nonneg_of_le
        (fun j ↦ abs_nonneg _) hdev_bound
    have hdu_tsum : (∑' j : ℕ, d j) ≤ (1 / 4 : ℝ) := by
      have hcomp : (∑' j : ℕ, d j) ≤ 7 * (∑' j : ℕ, u j) := by
        have hseven_nonneg : 0 ≤ (7 : ℝ) := by norm_num
        calc
          ∑' j : ℕ, d j ≤ ∑' j : ℕ, 7 * u j :=
            hdu_summable.tsum_le_tsum hdev_bound (husummable.mul_left 7)
          _ = 7 * (∑' j : ℕ, u j) := by rw [husummable.tsum_mul_left]
      have hmass_u : 7 * (∑' j : ℕ, u j) ≤ (1 / 4 : ℝ) := by
        have hseven_nonneg : 0 ≤ (7 : ℝ) := by norm_num
        calc
          7 * (∑' j : ℕ, u j) ≤ 7 * (C₄ * ε₀) :=
            mul_le_mul_of_nonneg_left husum_le hseven_nonneg
          _ ≤ (1 / 4 : ℝ) := hmass
      exact hcomp.trans hmass_u
    have hd_nonneg : ∀ j, 0 ≤ d j := by
      intro j
      exact abs_nonneg _
    have hd_le_one : ∀ j, d j ≤ 1 := by
      intro j
      have hfour_ne : (4 : ℕ) ≠ 0 := by norm_num
      have hu_lt : u j < (1 / 4 : ℝ) ^ 4 := by
        dsimp only [u]
        exact pow_lt_pow_left₀ (hvalid j).ε_lt_quarter (hvalid j).ε_pos.le hfour_ne
      have hseven : 7 * u j ≤ (1 : ℝ) := by
        nlinarith [hu_lt]
      have hdev_one : 7 * u j ≤ 1 := by linarith
      exact (hdev_bound j).trans hdev_one
    have hdev_self : ∀ j, |a (j + 1) / a j - 1| ≤ d j := by
      intro j
      exact le_rfl
    have hAmpBounds : ∀ j, a j ∈ Set.Icc (3 / 4 : ℝ) (Real.exp (1 / 4)) :=
      amplitude_mem_uniform_interval_of_ratio_deviation ha_pos ha_zero hd_nonneg hd_le_one
        hdev_self hdu_summable hdu_tsum
    have hGmin_le : (3 / 4 : ℝ) ≤ Glim := by
      exact ge_of_tendsto hGlim_tendsto (Eventually.of_forall fun j ↦ (hAmpBounds j).1)
    have hGmax_le : Glim ≤ Real.exp (1 / 4) := by
      exact le_of_tendsto hGlim_tendsto (Eventually.of_forall fun j ↦ (hAmpBounds j).2)
    refine ⟨Glim, ⟨hGmin_le, hGmax_le⟩, ?_, ?_⟩
    · simpa [a, orbit] using hGlim_tendsto
    · intro j
      simpa [a, orbit] using hAmpBounds j

end DFP.TwoPhaseOrbit
