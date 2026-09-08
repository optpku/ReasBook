module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointNonzero
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability
public import ReasLib.Topology.Real.VanishingStepModulo
public import ReasLib.Analysis.Asymptotics.PartialSumDivergence.Eventual

public section

open Filter
open scoped Asymptotics EuclideanSpace Matrix Topology

namespace DFP.TwoPhaseOrbit

/-- The endpoint cluster set of a sufficiently small invariant slow-curve orbit
is the affine unit circle determined by its limiting center and amplitude. -/
theorem slowCurveEndpointClusterSet_eq_limitCircle (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
                DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨ηGap, hηGap, cθ, hcθ, Cθ, hCθ, hGap⟩ :=
    slowCurveEndpointPolarAngleGapUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηScale, hηScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨ηDiv, hηDiv, hDiv⟩ :=
    DFP.TwoLeg.slowCurveScaleSquareNotSummable p h h_invariant h_pJet h_hJet
  obtain ⟨ηNonzero, hηNonzero, hNonzero⟩ :=
    slowCurveEndpointSubCenterLimit_ne_zero p h h_invariant h_pJet h_hJet
  obtain ⟨ηR, hηR, hR⟩ :=
    slowCurvePhaseRadiusErrorIsBigO p h h_invariant h_pJet h_hJet
  let η := min ηGap (min ηScale (min ηDiv (min ηNonzero ηR)))
  have hηpos : 0 < η := by
    dsimp only [η]
    exact lt_min hηGap.1
      (lt_min hηScale (lt_min hηDiv (lt_min hηNonzero.1 hηR.1)))
  have hηlt : η < 1 / 4 := (min_le_left _ _).trans_lt hηGap.2
  refine ⟨η, ⟨hηpos, hηlt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεGap : ε₀ ∈ Set.Ioc 0 ηGap :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεDiv : ε₀ ∈ Set.Ioc 0 ηDiv := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεNonzero : ε₀ ∈ Set.Ioc 0 ηNonzero := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    simpa only [State.coordinates_def] using congrArg Prod.fst hc'
  have hscaleZero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) := by
    have hs := hScale ε₀ hεScale
    have hbase : Tendsto
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      have hb : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
      convert (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 3)).comp hb using 1
      funext j
      simp only [Function.comp_apply]
      norm_num
    have hs' := hs.congr_left (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
    exact hs'.symm.tendsto_nhds hbase
  have hflatScaleZero : Tendsto
      (fun k : ℕ ↦ (orbit.state (k / 2)).ε) atTop (𝓝 0) := by
    exact hscaleZero.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hradialPhase (σ : Fin 2) :
      Tendsto (fun j : ℕ ↦ ‖orbit.endpoint (2 * j + σ.val) - Clim‖)
        atTop (𝓝 Glim) := by
    have hεR : ε₀ ∈ Set.Ioc 0 ηR := by
      refine ⟨hε₀.1, hε₀.2.trans ?_⟩
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))
    have herr := hR ε₀ hεR Clim hClim σ
    have hscaleZero3 : Tendsto
        (fun j : ℕ ↦ ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε ^ 3)
        atTop (𝓝 0) := by
      convert hscaleZero.pow 3 using 1 <;> norm_num [orbit]
    have herr0 : Tendsto
        (fun j : ℕ ↦ ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          (orbit.state j).amplitude) atTop (𝓝 0) :=
      herr.trans_tendsto hscaleZero3
    have hGlimTendsto' : Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude)
        atTop (𝓝 Glim) := by
      simpa only [orbit] using hGlimTendsto
    have hamp := hGlimTendsto'.sub (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim))
    have hsum := (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim)).add (herr0.add hamp)
    convert hsum using 1
    · funext j
      ring
    · ring
  have hradial : Tendsto
      (fun k : ℕ ↦ ‖orbit.endpoint k - Clim‖) atTop (𝓝 Glim) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have he := (Metric.tendsto_nhds.1 (hradialPhase (0 : Fin 2))) δ hδ
    have ho := (Metric.tendsto_nhds.1 (hradialPhase (1 : Fin 2))) δ hδ
    rcases eventually_atTop.1 he with ⟨Ne, he⟩
    rcases eventually_atTop.1 ho with ⟨No, ho⟩
    filter_upwards [eventually_ge_atTop (2 * max Ne No)] with k hk
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hj : Ne ≤ j := by omega
      simpa using he j hj
    · have hj : No ≤ j := by omega
      simpa using ho j hj
  ext x <;> constructor
  · intro hx
    obtain ⟨ψ, hψ, hxlim⟩ := hx.tendsto_subseq
    have hψtop := hψ.tendsto_atTop
    let φ : ℕ → ℝ := orbit.endpointPolarAngleLift Clim
    let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.basisFun (Fin 2) ℝ 0
    let r : ℕ → ℝ := fun k ↦ ‖orbit.endpoint k - Clim‖
    have hradial0 : Tendsto r atTop (𝓝 Glim) := by simpa only [r] using hradial
    have hrep (k : ℕ) : orbit.endpoint k - Clim =
        r k • EuclideanPlane.rotation (φ k) e := by
      have hs := orbit.endpointPolarAngle_spec Clim k
        (by simpa only [orbit] using hNonzero ε₀ hεNonzero Clim hClim k)
      simpa only [φ, r, e, orbit.endpointPolarAngleLift_coe] using hs
    have hq : Tendsto (fun k ↦ orbit.endpoint k -
        (Clim + Glim • EuclideanPlane.rotation (φ k) e)) atTop (𝓝 0) := by
      have hrotBound : ∀ k, ‖EuclideanPlane.rotation (φ k) e‖ = 1 := by
        intro k
        simpa [e] using (EuclideanPlane.rotation (φ k)).norm_map
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      have hradialSub : Tendsto (fun k ↦ r k - Glim) atTop (𝓝 0) := by
        simpa using hradial0.sub (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim))
      apply Metric.tendsto_nhds.2
      intro δ hδ
      have hsmall := (Metric.tendsto_nhds.1 hradialSub) δ hδ
      filter_upwards [hsmall] with k hk
      rw [sub_add_eq_sub_sub, hrep k]
      rw [← sub_smul]
      simpa only [dist_zero_right, norm_smul, hrotBound k, mul_one] using hk
    let q : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦ orbit.endpoint k -
      (Clim + Glim • EuclideanPlane.rotation (φ k) e)
    have hqsub := (show Tendsto q atTop (𝓝 0) by simpa only [q] using hq).comp hψtop
    have hxendpoint : Tendsto (orbit.endpoint ∘ ψ) atTop (𝓝 x) := hxlim
    have hsub : Tendsto (fun n ↦ orbit.endpoint (ψ n) - q (ψ n)) atTop (𝓝 x) := by
      have hqsub' : Tendsto (fun n ↦ q (ψ n)) atTop (nhds 0) := by
        simpa only [Function.comp_def] using hqsub
      have hxendpoint' : Tendsto (fun n ↦ orbit.endpoint (ψ n)) atTop (nhds x) := by
        simpa only [Function.comp_def] using hxendpoint
      simpa only [sub_zero] using hxendpoint'.sub hqsub'
    have hz : Tendsto (fun n ↦ Clim + Glim • EuclideanPlane.rotation
        (φ (ψ n)) e) atTop (𝓝 x) := by
      convert hsub using 1 <;> simp only [q, sub_sub_cancel]
    exact (isClosed_limitCircle Clim Glim hGlim).mem_of_tendsto hz
      (Eventually.of_forall (fun n ↦ by
        rw [mem_limitCircle]
        refine ⟨EuclideanPlane.rotation (φ (ψ n)) e, ?_, rfl⟩
        simpa [e] using (EuclideanPlane.rotation (φ (ψ n))).norm_map
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)))
  · intro hx
    let φ : ℕ → ℝ := orbit.endpointPolarAngleLift Clim
    let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.basisFun (Fin 2) ℝ 0
    let r : ℕ → ℝ := fun k ↦ ‖orbit.endpoint k - Clim‖
    have hGapOrbit := hGap ε₀ hεGap Clim hClim
    have hstrict : StrictAnti φ := by
      simpa only [φ, orbit] using hGapOrbit.1
    let v : ℕ → ℝ := fun n ↦ (orbit.state (n / 2)).ε ^ 2
    have hv_nonneg : ∀ n, 0 ≤ v n := by
      intro n
      exact sq_nonneg _
    have hscaleNotSummable : ¬ Summable
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
      simpa only [hεcoord] using hDiv ε₀ hεDiv
    have hv_notSummable : ¬ Summable v := by
      intro hv
      have heven := hv.comp_injective (i := fun j : ℕ ↦ 2 * j) (by
        intro i j hij
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) hij)
      have heven_eq :
          v ∘ (fun j : ℕ ↦ 2 * j) = fun j : ℕ ↦ (orbit.state j).ε ^ 2 := by
        funext j
        simp only [v, Function.comp_apply]
        rw [Nat.mul_div_cancel_left j (by norm_num : 0 < 2)]
      rw [heven_eq] at heven
      exact hscaleNotSummable heven
    have hdrop_nonneg : ∀ n, 0 ≤ φ n - φ (n + 1) := by
      intro n
      exact sub_nonneg.mpr (hstrict (Nat.lt_succ_self n)).le
    have hdrop_lower : ∀ n, cθ * v n ≤ φ n - φ (n + 1) := by
      intro n
      rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
      · simpa [φ, v, orbit] using (hGapOrbit.2 j 0).1
      · have hidx : (2 * j + 1) / 2 = j := by omega
        simpa [φ, v, orbit, hidx] using (hGapOrbit.2 j 1).1
    have hdrop : ∀ n, cθ * v n ≤ φ n - φ (n + 1) := by
      intro n
      exact hdrop_lower n
    have hdrop_zero : Tendsto
        (fun n ↦ φ n - φ (n + 1)) atTop (𝓝 0) := by
      have hupper : ∀ n, φ n - φ (n + 1) ≤ Cθ * v n := by
        intro n
        rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
        · simpa [φ, v, orbit] using (hGapOrbit.2 j 0).2
        · have hidx : (2 * j + 1) / 2 = j := by omega
          simpa [φ, v, orbit, hidx] using (hGapOrbit.2 j 1).2
      have hvzero : Tendsto v atTop (𝓝 0) := by
        convert hflatScaleZero.pow 2 using 1 <;> norm_num [v]
      have hupperZero : Tendsto (fun n ↦ Cθ * v n) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hvzero)
      exact squeeze_zero (fun n ↦ hdrop_nonneg n) hupper hupperZero
    have hbot : Tendsto φ atTop atBot := by
      exact tendsto_atBot_of_eventually_le_decrement_of_not_summable
        hcθ hv_nonneg (Eventually.of_forall hdrop) hv_notSummable
    obtain ⟨unit, hunit, hθ⟩ := mem_limitCircle.mp hx
    let θ' : ℝ :=
      (EuclideanPlane.orientation.oangle e unit).toReal
    obtain ⟨j, m, hj, hangle⟩ :=
      Real.existsSubseqAddIntMulTendsto (2 * Real.pi) Real.two_pi_pos
        hstrict hbot hdrop_zero θ'
    have hθrot : EuclideanPlane.rotation (θ' : Real.Angle) e = unit := by
      have heStd :
          e = (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
        ext i
        fin_cases i <;> simp [e]
      have hθcoe : (θ' : Real.Angle) =
          EuclideanPlane.orientation.oangle e unit := by
        simpa only [θ'] using
          Real.Angle.coe_toReal (EuclideanPlane.orientation.oangle e unit)
      have hframe : EuclideanPlane.frame unit =
          EuclideanPlane.rotationMatrix (θ' : Real.Angle) := by
        rw [hθcoe, heStd]
        exact EuclideanPlane.frame_eq_rotationMatrix_oangle unit hunit
      have hecoord : (EuclideanSpace.equiv (Fin 2) ℝ) e = ![(1 : ℝ), 0] := by
        rw [heStd]
        ext i
        fin_cases i <;> rfl
      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      calc
        (EuclideanSpace.equiv (Fin 2) ℝ)
            (EuclideanPlane.rotation (θ' : Real.Angle) e) =
            EuclideanPlane.rotationMatrix (θ' : Real.Angle) *ᵥ
              (EuclideanSpace.equiv (Fin 2) ℝ) e :=
          (EuclideanPlane.rotationMatrix_mulVec (θ' : Real.Angle) e).symm
        _ = EuclideanPlane.rotationMatrix (θ' : Real.Angle) *ᵥ ![(1 : ℝ), 0] := by
          rw [hecoord]
        _ = EuclideanPlane.frame unit *ᵥ ![(1 : ℝ), 0] := by
          rw [hframe]
        _ = (EuclideanSpace.equiv (Fin 2) ℝ)
            ((1 : ℝ) • unit + 0 • EuclideanPlane.perp unit) :=
          EuclideanPlane.frame_mulVec unit 1 0
        _ = (EuclideanSpace.equiv (Fin 2) ℝ) unit := by simp
    have hangle' : Tendsto
        (fun i ↦ φ (j i) + (m i : ℝ) * (2 * Real.pi)) atTop (𝓝 θ') := by
      simpa only [θ'] using hangle
    have hangle_coe (i : ℕ) :
        ((φ (j i) + (m i : ℝ) * (2 * Real.pi) : ℝ) : Real.Angle) =
          (φ (j i) : Real.Angle) := by
      rw [Real.Angle.coe_add, Real.Angle.intCast_mul_eq_zsmul]
      simp only [Real.Angle.coe_two_pi, smul_zero, add_zero]
    have hrot_cont : Continuous
        (fun t : Real.Angle ↦ EuclideanPlane.rotation t e) := by
      simp only [EuclideanPlane.rotation_apply]
      exact Real.Angle.continuous_cos.smul continuous_const |>.add
        (Real.Angle.continuous_sin.smul continuous_const)
    have hrot_tendsto : Tendsto
        (fun i ↦ EuclideanPlane.rotation
          ((φ (j i) + (m i : ℝ) * (2 * Real.pi) : ℝ) : Real.Angle) e)
        atTop (𝓝 (EuclideanPlane.rotation (θ' : Real.Angle) e)) := by
      exact ((hrot_cont.comp Real.Angle.continuous_coe).tendsto θ').comp hangle'
    have hrot_tendsto' : Tendsto
        (fun i ↦ EuclideanPlane.rotation (φ (j i)) e) atTop (𝓝 unit) := by
      rw [← hθrot]
      exact hrot_tendsto.congr' (Eventually.of_forall (fun i ↦
        congrArg (fun t : Real.Angle ↦ EuclideanPlane.rotation t e) (hangle_coe i)))
    have hradialSub : Tendsto (fun k ↦ r k - Glim) atTop (𝓝 0) := by
      simpa using hradial.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim))
    have hrj : Tendsto (fun i ↦ r (j i)) atTop (𝓝 Glim) :=
      hradial.comp hj.tendsto_atTop
    have hsmul : Tendsto (fun i ↦ r (j i) • EuclideanPlane.rotation
        (φ (j i)) e) atTop (𝓝 (Glim • unit)) :=
      hrj.smul hrot_tendsto'
    have hpoint : Tendsto (fun i ↦ orbit.endpoint (j i)) atTop
        (𝓝 (Clim + Glim • unit)) := by
      have hrepr (k : ℕ) : orbit.endpoint k - Clim =
          r k • EuclideanPlane.rotation (φ k) e := by
        have hs := orbit.endpointPolarAngle_spec Clim k
          (by simpa only [orbit] using hNonzero ε₀ hεNonzero Clim hClim k)
        simpa only [φ, r, e, orbit.endpointPolarAngleLift_coe] using hs
      have hadd := (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ Clim) atTop (𝓝 Clim)).add hsmul
      have hpoint_eq (i : ℕ) :
          orbit.endpoint (j i) =
            Clim + r (j i) • EuclideanPlane.rotation (φ (j i)) e := by
        calc
          orbit.endpoint (j i) = (orbit.endpoint (j i) - Clim) + Clim :=
            (sub_add_cancel _ _).symm
          _ = r (j i) • EuclideanPlane.rotation (φ (j i)) e + Clim := by
            rw [hrepr (j i)]
          _ = Clim + r (j i) • EuclideanPlane.rotation (φ (j i)) e := add_comm _ _
      exact hadd.congr' (Eventually.of_forall (fun i ↦ (hpoint_eq i).symm))
    have hcluster : MapClusterPt (Clim + Glim • unit) atTop orbit.endpoint := by
      exact hpoint.mapClusterPt.of_comp hj.tendsto_atTop
    change MapClusterPt x atTop orbit.endpoint
    simpa only [hθ] using hcluster

end DFP.TwoPhaseOrbit
