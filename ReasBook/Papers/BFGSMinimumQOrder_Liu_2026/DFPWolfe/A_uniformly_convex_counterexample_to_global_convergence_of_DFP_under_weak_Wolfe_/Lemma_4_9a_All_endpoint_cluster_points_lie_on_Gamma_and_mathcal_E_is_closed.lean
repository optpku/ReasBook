module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_8b1_The_limiting_circle_is_compact_and_closed
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_8c_Two_phase_endpoint_polar_representation

public section

noncomputable section

open Filter
open scoped Asymptotics EuclideanSpace Topology

/-- Lemma 4.9a (All endpoint cluster points lie on $\Gamma$ and $\mathcal E$ is closed) (1):
every `atTop` cluster point of the endpoint sequence of a sufficiently small
slow-curve orbit belongs to its limiting circle `Γ`. -/
theorem slowCurveEndpointClusterPt_mem_limitCircle (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ x, MapClusterPt x atTop orbit.endpoint →
                x ∈ DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
  obtain ⟨ηPolar, hηPolar, hPolar⟩ :=
    slowCurveEndpointPolarRepresentation p h h_invariant h_pJet h_hJet
  obtain ⟨ηScale, hηScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  let εbar := min ηPolar ηScale
  have hεbar_pos : 0 < εbar := lt_min hηPolar.1 hηScale
  have hεbar_lt : εbar < 1 / 4 := (min_le_left _ _).trans_lt hηPolar.2
  refine ⟨εbar, ⟨hεbar_pos, hεbar_lt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Polar : ε₀ ∈ Set.Ioc 0 ηPolar :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _ )⟩
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 ηScale :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _ )⟩
  intro Clim hClim Glim hGlim hGlim_tendsto x hx
  have hPolarOrbit : ∀ σ : Fin 2,
      (fun j : ℕ ↦ orbit.endpoint (2 * j + σ.val) - Clim -
          (orbit.state j).amplitude •
            EuclideanPlane.rotation
              (orbit.endpointPolarAngle Clim (2 * j + σ.val))
              (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =o[atTop]
      (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
    intro σ
    simpa only [orbit] using
      (hPolar ε₀ hε₀Polar Clim hClim Glim hGlim hGlim_tendsto σ).1
  have hεcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hcoord' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoord
    have hfst := congrArg Prod.fst hcoord'
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using hfst
  have hscaleOrbit :
      (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
    have hs := hScale ε₀ hε₀Scale
    exact hs.congr_left (Eventually.of_forall (fun j ↦ (hεcoord j).symm))
  have hmodelZero : Tendsto
      (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
      atTop (𝓝 0) := by
    have hbase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
    convert (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 3)).comp hbase using 1
    · funext j
      dsimp only [Function.comp_apply]
      congr 1
      ring
  have hεzero : Tendsto (fun j : ℕ ↦ (orbit.state j).ε) atTop (𝓝 0) :=
    hscaleOrbit.symm.tendsto_nhds hmodelZero
  have hεsquare : Tendsto (fun j : ℕ ↦ (orbit.state j).ε ^ 2) atTop (𝓝 0) :=
    by simpa using hεzero.pow 2
  have hphase (σ : Fin 2) :
      Tendsto
        (fun j : ℕ ↦ orbit.endpoint (2 * j + σ.val) -
          (Clim + Glim • EuclideanPlane.rotation
            (orbit.endpointPolarAngle Clim (2 * j + σ.val))
            (EuclideanSpace.basisFun (Fin 2) ℝ 0)))
        atTop (𝓝 0) := by
    have hrem := (hPolarOrbit σ).tendsto_zero_of_tendsto hεsquare
    have hamp : Tendsto
      (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) atTop (𝓝 0) := by
      simpa only [orbit, sub_self] using
        hGlim_tendsto.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Glim) atTop (𝓝 Glim))
    have hsmul : Tendsto
        (fun j : ℕ ↦ ((orbit.state j).amplitude - Glim) •
          EuclideanPlane.rotation
            (orbit.endpointPolarAngle Clim (2 * j + σ.val))
            (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        atTop (𝓝 0) := by
      apply Filter.Tendsto.zero_smul_isBoundedUnder_le hamp
      apply isBoundedUnder_of
      refine ⟨1, ?_⟩
      intro j
      have hnorm : ‖EuclideanPlane.rotation
          (orbit.endpointPolarAngle Clim (2 * j + σ.val))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ = 1 := by
        simpa using (EuclideanPlane.rotation
          (orbit.endpointPolarAngle Clim (2 * j + σ.val))).norm_map
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      exact hnorm.le
    have hadd := hrem.add hsmul
    have hadd0 : Tendsto (fun j ↦
        orbit.endpoint (2 * j + σ.val) - Clim -
            (orbit.state j).amplitude •
              EuclideanPlane.rotation
                (orbit.endpointPolarAngle Clim (2 * j + σ.val))
                (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
          ((orbit.state j).amplitude - Glim) •
            EuclideanPlane.rotation
              (orbit.endpointPolarAngle Clim (2 * j + σ.val))
              (EuclideanSpace.basisFun (Fin 2) ℝ 0)) atTop (𝓝 0) := by
      simpa only [zero_add, add_zero] using hadd
    refine hadd0.congr' (Eventually.of_forall (fun j ↦ ?_))
    module
  let q : ℕ → EuclideanSpace ℝ (Fin 2) := fun k ↦
    orbit.endpoint k -
      (Clim + Glim • EuclideanPlane.rotation
        (orbit.endpointPolarAngle Clim k)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0))
  have hq : Tendsto q atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hEven := (Metric.tendsto_nhds.1 (by simpa only [q] using hphase (0 : Fin 2))) δ hδ
    have hOdd := (Metric.tendsto_nhds.1 (by simpa only [q] using hphase (1 : Fin 2))) δ hδ
    rcases (eventually_atTop.1 hEven) with ⟨N₀, hN₀⟩
    rcases (eventually_atTop.1 hOdd) with ⟨N₁, hN₁⟩
    filter_upwards [eventually_ge_atTop (2 * max N₀ N₁)] with k hk
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hj : N₀ ≤ j := by omega
      simpa [q] using hN₀ j hj
    · have hj : N₁ ≤ j := by omega
      simpa [q] using hN₁ j hj
  obtain ⟨ψ, hψmono, hendpoint⟩ := hx.tendsto_subseq
  have hψ_atTop : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
  have hq_sub : Tendsto (q ∘ ψ) atTop (𝓝 0) := hq.comp hψ_atTop
  have hendpointOrbit : Tendsto (orbit.endpoint ∘ ψ) atTop (𝓝 x) := by
    simpa only [orbit] using hendpoint
  have hsub : Tendsto
      (fun n : ℕ ↦ orbit.endpoint (ψ n) - q (ψ n)) atTop (𝓝 x) := by
    simpa only [Function.comp_apply, Pi.sub_apply, sub_zero] using
      hendpointOrbit.sub hq_sub
  have hz : Tendsto
      (fun n : ℕ ↦ Clim + Glim • EuclideanPlane.rotation
      (orbit.endpointPolarAngle Clim (ψ n))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) atTop (𝓝 x) := by
    convert hsub using 1 <;>
      simp only [q, Function.comp_apply, sub_sub_cancel, sub_zero]
  have hz_mem (n : ℕ) :
      Clim + Glim • EuclideanPlane.rotation
        (orbit.endpointPolarAngle Clim (ψ n))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ∈
        DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
    rw [DFP.TwoPhaseOrbit.mem_limitCircle]
    refine ⟨EuclideanPlane.rotation
      (orbit.endpointPolarAngle Clim (ψ n))
      (EuclideanSpace.basisFun (Fin 2) ℝ 0), ?_, rfl⟩
    simpa using (EuclideanPlane.rotation
      (orbit.endpointPolarAngle Clim (ψ n))).norm_map
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  exact (DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim).mem_of_tendsto hz
    (Eventually.of_forall hz_mem)

/-- Lemma 4.9a (All endpoint cluster points lie on $\Gamma$ and $\mathcal E$ is closed) (2):
the union `𝓔` of the limiting circle and the endpoint range of a sufficiently
small slow-curve orbit is closed. -/
theorem isClosed_slowCurveClosedSetCandidate (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              IsClosed (orbit.closedSetCandidate Clim Glim) := by
  obtain ⟨εbar, hεbar, hcluster⟩ :=
    slowCurveEndpointClusterPt_mem_limitCircle p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  intro Clim hClim Glim hGlim hGlim_tendsto
  apply DFP.TwoPhaseOrbit.isClosed_closedSetCandidate orbit Clim Glim hGlim
  intro x hx
  simpa only [orbit] using
    hcluster ε₀ hε₀ Clim hClim Glim hGlim hGlim_tendsto x hx
