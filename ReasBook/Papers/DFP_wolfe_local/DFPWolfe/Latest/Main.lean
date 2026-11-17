module

public import ReasLib.Optimization.DFP.Polar.General.Continuation
public import ReasLib.Optimization.DFP.Polar.General.PlanarCounterexample
public import ReasLib.Optimization.DFP.Polar.General.Objective
public import ReasLib.Optimization.DFP.Polar.General.RadiusBounds
public import ReasLib.Optimization.DFP.Polar.General.WolfeRatios
public import ReasLib.Optimization.DFP.Polar.General.IdentityQuantitative

public section

noncomputable section

open Filter
open scoped Topology

namespace DFPWolfe.Latest

open DFP.Polar.General
open DFPWolfe.V21.IdentityQuantitative (initialMinEigenvalue initialMaxEigenvalue)

/-- Helper for thm:main: the actual source parameters obtained from a strict stable
two-cycle and a prescribed Hessian exponent and Wolfe pair. -/
def sourceParameters (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : Parameters where
  beta := β
  c1 := c1
  c2 := c2
  ell := ell
  z := z
  base := hbase
  startIndex := j0

/-- Helper for thm:main: source parameters retain the prescribed Hölder exponent. -/
theorem sourceParameters_beta (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).beta = β := by
  rfl

/-- Helper for thm:main: source parameters retain the prescribed Armijo parameter. -/
theorem sourceParameters_c1 (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).c1 = c1 := by
  rfl

/-- Helper for thm:main: source parameters retain the prescribed curvature parameter. -/
theorem sourceParameters_c2 (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).c2 = c2 := by
  rfl

/-- Helper for thm:main: source parameters retain the selected even base coefficient. -/
theorem sourceParameters_ell (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).ell = ell := by
  rfl

/-- Helper for thm:main: source parameters retain the selected normalization parameter. -/
theorem sourceParameters_z (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).z = z := by
  rfl

/-- Helper for thm:main: source parameters retain the chosen starting index. -/
theorem sourceParameters_startIndex (β c1 c2 ell z : ℝ) (hbase : StrictWolfeBase c1 c2 ell z)
    (j0 : ℕ) : (sourceParameters β c1 c2 ell z hbase j0).startIndex = j0 := by
  rfl

/-- Helper for thm:main: the canonical certificate and its actual explicit source have the
same initial sublevel set. -/
theorem sourceInitialLevelSet_eq {p : Parameters} {κ : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ c) :
    DFP.Polar.OrthogonalExtension.initialLevelSet c.iteration = Objective.initialLevelSet p κ := by
  ext x
  rw [DFP.Polar.OrthogonalExtension.initialLevelSet_def, Objective.mem_initialLevelSet]
  simp only [Set.mem_setOf_eq, hsource.objective, hsource.point]

/-- Helper for eq:counterexample-nonlipschitz: the canonical secant residual function is
the same actual explicit source residual function. -/
theorem sourceResidualRatio_eq {p : Parameters} {κ : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ c)
    (hgeometry : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (β' : ℝ) :
    DFP.Polar.OrthogonalExtension.secantResidualRatio c.iteration β' =
      Objective.evenResidualRatio p κ β' := by
  funext j
  rw [hsource.secantResidualRatio_eq hgeometry,
    Objective.evenResidualRatio_eq_coefficient p κ β' hgeometry]

/-- Helper for thm:main: all objective, cluster and sharpness properties transfer along
the exact source identities of the canonical planar DFP certificate. -/
theorem sourceCertificateProperties {p : Parameters} {κ δ ε H : ℝ}
    {c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : PlanarCounterexample.SourceIdentity p κ c) (hlimit : c.gradientLimit = 1)
    (hobjective : Objective.ObjectiveEstimates p κ δ H) (hδε : δ ≤ ε)
    (hcluster : {x | MapClusterPt x atTop p.point} = Metric.sphere 0 1)
    (hno : ∀ β' ∈ Set.Ioc p.beta 1,
      ¬ ∃ L ≥ 0, ∀ x ∈ Objective.initialLevelSet p κ, ∀ y ∈ Objective.initialLevelSet p κ,
        ‖hessian (p.objective κ) x - hessian (p.objective κ) y‖ ≤ L * ‖x - y‖ ^ β')
    (hresidual : ∀ β' ∈ Set.Ioc p.beta 1,
      Tendsto (Objective.evenResidualRatio p κ β') atTop atTop) :
    Transport.CounterexampleProperties p.beta ε c LinearIsometry.id := by
  have hnear : ∀ x, ‖hessian (p.objective κ) x - 1‖ ≤ ε :=
    fun x ↦ (hobjective.hessian_near_identity x).trans hδε
  constructor
  · exact hlimit
  · intro x
    rw [hsource.objective]
    exact hnear x
  · rw [hsource.objective]
    exact Objective.hessianBounds_of_identity_norm hobjective.contDiff hnear
  · refine ⟨H, hobjective.holder_nonneg, ?_⟩
    intro x y
    rw [hsource.objective]
    exact hobjective.hessian_holder x y
  · rw [hsource.objective]
    exact hobjective.origin
  · rw [hsource.objective]
    exact hobjective.unique_minimizer
  · simpa only [hsource.point, LinearIsometry.coe_id, Set.image_id] using hcluster
  · intro β' hβ'
    rw [hsource.objective, sourceInitialLevelSet_eq hsource]
    exact hno β' hβ'
  · intro β' hβ'
    rw [sourceResidualRatio_eq hsource hobjective.geometry]
    exact hresidual β' hβ'


/-- Helper for cor:identity-initialization: normalize the actual planar certificate by its
positive square root first, then extend that identity-initialized iteration to dimension `n`. -/
theorem identityExtensionOfPlanar (n : ℕ) (hn : 2 ≤ n) {β ε c1 c2 : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c1 c2)
    (h : Transport.CounterexampleProperties β ε c LinearIsometry.id) (hβ : 0 ≤ β) :
    ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) (m M : ℝ)
      (planar : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c1 c2)
      (result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
        (min m 1) (max M 1) c1 c2),
      P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
        DFP.Polar.IdentityInitialization.PullbackData c.iteration planar.iteration P ∧
          DFP.Polar.IdentityInitialization.DimensionExtensionData n hn
            planar.iteration result.iteration ∧
            Transport.EllipseObjectiveProperties β result.iteration
              ((DFP.Polar.OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp
                P.symm.toLinearMap) := by
  obtain ⟨P, m, M, planar, hP, hPullback, hEllipse⟩ :=
    Transport.normalizeCertificateWithProperties le_rfl c LinearIsometry.id h hβ
  have hPlanar : Transport.EllipseObjectiveProperties β planar.iteration P.symm.toLinearMap := by
    simpa only [LinearIsometry.id_toLinearMap, LinearMap.comp_id] using hEllipse
  obtain ⟨result, hExtended, hFinal⟩ :=
    Transport.extendNormalizedPlanar n hn planar P.symm.toLinearMap hPlanar hβ
  exact ⟨P, m, M, planar, result, hP, hPullback, hExtended, hFinal⟩

/-- Helper for thm:main: the full actual planar construction, retaining the static source
parameters, chosen starting index, trajectory, radial and interpolation estimates, and
the exact source identities of the canonical DFP certificate. -/
structure PlanarConstruction (c1 c2 β ε : ℝ) where
  parameters : Parameters
  beta_eq : parameters.beta = β
  c1_eq : parameters.c1 = c1
  c2_eq : parameters.c2 = c2
  startIndex : ℕ
  startIndex_pos : 0 < startIndex
  fastWidth : ℝ
  fastWidth_pos : 0 < fastWidth
  slowWidth : ℝ
  slowWidth_pos : 0 < slowWidth
  supportScale : ℝ
  supportScale_pos : 0 < supportScale
  hessianError : ℝ
  hessianError_pos : 0 < hessianError
  hessianError_le : hessianError ≤ ε
  hessianError_le_half : hessianError ≤ 1 / 2
  holderConstant : ℝ
  holderConstant_nonneg : 0 ≤ holderConstant
  sourceData : Objective.SourceObjectiveData parameters startIndex fastWidth slowWidth
    supportScale hessianError holderConstant
  certificate : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2)
    (parameters.withStartIndex startIndex).c1 (parameters.withStartIndex startIndex).c2
  sourceIdentity : PlanarCounterexample.SourceIdentity (parameters.withStartIndex startIndex)
    supportScale certificate
  properties : Transport.CounterexampleProperties parameters.beta ε certificate LinearIsometry.id

/-- Helper for thm:main: every admissible Wolfe pair and prescribed exponent admits the
fully proved actual planar source construction. -/
theorem planarSource (c1 c2 ε β : ℝ) (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    Nonempty (PlanarConstruction c1 c2 β ε) := by
  obtain ⟨ell, z, hbase⟩ := strictWolfeBaseExists hc1 hc12 hc2
  let p0 := sourceParameters β c1 c2 ell z hbase 0
  have hpβ : p0.beta = β := sourceParameters_beta β c1 c2 ell z hbase 0
  have hp1 : p0.c1 = c1 := sourceParameters_c1 β c1 c2 ell z hbase 0
  have hp2 : p0.c2 = c2 := sourceParameters_c2 β c1 c2 ell z hbase 0
  have hβ0 : 0 < p0.beta := by
    rw [hpβ]
    exact hβ.1
  have hβone : p0.beta < 1 := by
    rw [hpβ]
    exact hβ.2
  let δ := min ε (1 / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hδ : 0 < δ := lt_min hε.1 hhalf
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ < 1 := by linarith
  obtain ⟨N, hN, M, hM, κ, hκ, H, hH, s, hs, U, hU, Cobj, hCobj, J0, hJ0, hObjective⟩ :=
    Objective.existsSourceObjectiveData p0 hβ0 hβone δ hδ hδone
  obtain ⟨δW, hδW, hWolfe⟩ := RadiusBounds.wolfeBoundsOfActualTube p0 hβ0 hβone hM.le hN.le
  obtain ⟨J1, hJ1⟩ := eventually_atTop.mp
    ((Objective.scale_start_rpow_tendsto_zero hβ0 (sub_pos.mpr hβone)).eventually
      (Iio_mem_nhds hδW))
  let j0 := max J0 J1
  have hj0 : 0 < j0 := hJ0.trans_le (le_max_left _ _)
  have hdata := (hObjective j0 (le_max_left _ _)).1
  let q := p0.withStartIndex j0
  have hqβ : 0 < q.beta := by simpa only [q, p0.withStartIndex_beta] using hβ0
  have hqstart : 0 < q.startIndex := by simpa only [q, p0.withStartIndex_startIndex] using hj0
  have hq1 : q.c1 = c1 := (p0.withStartIndex_c1 j0).trans hp1
  have hq2 : q.c2 = c2 := (p0.withStartIndex_c2 j0).trans hp2
  have hqc1 : 0 < q.c1 := by rwa [hq1]
  have hqc12 : q.c1 < q.c2 := by rwa [hq1, hq2]
  have hqc2 : q.c2 < 1 := by rwa [hq2]
  have hZ : ∀ k, (q.matrix k).PosDef := fun k ↦ (hdata.feasible k).posDef
  have hC : ∀ k, 0 < q.matrix k 0 1 := fun k ↦ (hdata.feasible k).offDiagonal_pos
  have hSigma : ∀ k, 0 < DFP.Polar.sigmaOf (q.matrix k) (q.angleIncrement k)
      (q.zeta k) (q.zeta (k + 1)) := fun k ↦ (hdata.feasible k).secant_pos
  have hW : ∀ k, 0 < q.radiusRatio k := fun k ↦ zero_lt_one.trans (hdata.factors k)
  have hr : ∀ k, 0 < q.radius k :=
    fun k ↦ zero_lt_one.trans (q.radius_gt_one hdata.factors hdata.logarithms k)
  have hslow (j : ℕ) : |(q.normalizedEvenState j).1 - p0.gammaStar| ≤
      M * scale p0.beta j0 j ^ (1 - p0.beta) := by
    simpa only [Continuation.slowError_def, Continuation.stateAt_def]
      using hdata.trajectory.slow_bound j
  have hfast (j : ℕ) : FastContraction.fixedNorm p0.ell p0.z
      (DFP.Polar.FastContraction.fastCoordinates (q.normalizedEvenState j) -
        FastContraction.evenFastReference p0 (q.normalizedEvenState j).1) ≤
      N * scale p0.beta j0 j ^ (1 + p0.beta) := by
    simpa only [Continuation.fastSize_def, Continuation.fastError_def, Continuation.stateAt_def,
      scale_rpow_one_add hβ0, div_eq_mul_inv] using hdata.trajectory.fast_bound j
  have hphase : ∀ j : ℕ, ∀ i : Fin 2,
      q.c1 < RadiusBounds.phaseArmijo q i (q.scale j) (q.inverseIndex j) (q.normalizedEvenState j) ∧
        RadiusBounds.phaseCurvature q i (q.scale j) (q.inverseIndex j)
          (q.normalizedEvenState j) < q.c2 := by
    intro j i
    have h := hWolfe j0 hj0 (hJ1 j0 (le_max_right _ _)) hslow hfast j i
    simpa only [q, p0.withStartIndex_c1, p0.withStartIndex_c2] using h
  have hstrong := WolfeRatios.sourceStrongWolfe_of_phaseMargins q κ δ H hqβ hqstart
    hqc1 hqc12 hqc2 hdata.objectiveEstimates hZ hC hdata.sine_pos hW hr hdata.logarithms hphase
  have horbit := q.sourceOrbit κ hqβ hqstart hdata.objectiveEstimates.geometry
    hZ hC hdata.sine_pos hdata.factors hSigma hdata.logarithms
  have hpos : ∀ k, (q.inverseHessian k).PosDef := fun k ↦ q.inverseHessian_posDef k (hZ k)
  have hden := q.sourceSecantDenominator_ne hZ hC hdata.sine_pos hdata.factors hSigma
    hdata.logarithms
  have hhalfBounds : HasHessianBounds (1 / 2) (3 / 2) (q.objective κ) := by
    have h := Objective.hessianBounds_of_identity_norm hdata.objectiveEstimates.contDiff
      (fun x ↦ (hdata.objectiveEstimates.hessian_near_identity x).trans hδhalf)
    norm_num at h
    exact h
  have hgradLimit : Tendsto (fun k ↦ ‖q.gradients k‖) atTop (𝓝 1) := by
    have hnorm (k : ℕ) : ‖gradient (q.objective κ) (q.point k)‖ = ‖q.gradients k‖ :=
      congrArg norm (hdata.objectiveEstimates.endpoints k).2.1
    have h : Tendsto (fun k ↦ ‖gradient (q.objective κ) (q.point k)‖) atTop (𝓝 1) :=
      hdata.gradientNorm_tendsto
    rw [funext hnorm] at h
    exact h
  obtain ⟨c, hsource, hlimit⟩ := PlanarCounterexample.existsSourceCertificate q κ horbit hpos hden
    hdata.objectiveEstimates.contDiff hhalfBounds hstrong hgradLimit
  have hno : ∀ β' ∈ Set.Ioc q.beta 1,
      ¬ ∃ L ≥ 0, ∀ x ∈ Objective.initialLevelSet q κ, ∀ y ∈ Objective.initialLevelSet q κ,
        ‖hessian (q.objective κ) x - hessian (q.objective κ) y‖ ≤ L * ‖x - y‖ ^ β' := by
    intro β' hβ'
    apply hdata.no_higherHolder_initialLevelSet β'
    simpa only [q, p0.withStartIndex_beta] using hβ'.1
  have hresidual : ∀ β' ∈ Set.Ioc q.beta 1,
      Tendsto (Objective.evenResidualRatio q κ β') atTop atTop := by
    intro β' hβ'
    apply hdata.residual_tendsto β'
    simpa only [q, p0.withStartIndex_beta] using hβ'.1
  have hpropertiesQ := sourceCertificateProperties hsource hlimit hdata.objectiveEstimates hδε
    hdata.clusterSet hno hresidual
  have hproperties : Transport.CounterexampleProperties p0.beta ε c LinearIsometry.id := by
    simpa only [q, p0.withStartIndex_beta] using hpropertiesQ
  exact ⟨{
    parameters := p0
    beta_eq := hpβ
    c1_eq := hp1
    c2_eq := hp2
    startIndex := j0
    startIndex_pos := hj0
    fastWidth := N
    fastWidth_pos := hN
    slowWidth := M
    slowWidth_pos := hM
    supportScale := κ
    supportScale_pos := hκ
    hessianError := δ
    hessianError_pos := hδ
    hessianError_le := hδε
    hessianError_le_half := hδhalf
    holderConstant := H
    holderConstant_nonneg := hH
    sourceData := hdata
    certificate := c
    sourceIdentity := hsource
    properties := hproperties
  }⟩

/-- Helper for thm:main: equality of the Wolfe parameters transports existence of a
planar certificate and all its objective and geometric properties. -/
theorem existsPlanarCertificate_congr {a1 a2 b1 b2 β ε : ℝ}
    (h1 : a1 = b1) (h2 : a2 = b2)
    (h : ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) a1 a2,
      Transport.CounterexampleProperties β ε c LinearIsometry.id) :
    ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) b1 b2,
      Transport.CounterexampleProperties β ε c LinearIsometry.id := by
  cases h1
  cases h2
  exact h

/-- Helper for thm:main: the retained source certificate has the originally prescribed
Wolfe pair and Hölder exponent. -/
theorem PlanarConstruction.existsPlanarCertificate {c1 c2 β ε : ℝ}
    (s : PlanarConstruction c1 c2 β ε) :
    ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c1 c2,
      Transport.CounterexampleProperties β ε c LinearIsometry.id := by
  have hc1 : (s.parameters.withStartIndex s.startIndex).c1 = c1 :=
    (s.parameters.withStartIndex_c1 s.startIndex).trans s.c1_eq
  have hc2 : (s.parameters.withStartIndex s.startIndex).c2 = c2 :=
    (s.parameters.withStartIndex_c2 s.startIndex).trans s.c2_eq
  have h : ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2)
        (s.parameters.withStartIndex s.startIndex).c1 (s.parameters.withStartIndex s.startIndex).c2,
      Transport.CounterexampleProperties s.parameters.beta ε c LinearIsometry.id :=
    ⟨s.certificate, s.properties⟩
  have hβ : ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2)
        (s.parameters.withStartIndex s.startIndex).c1 (s.parameters.withStartIndex s.startIndex).c2,
      Transport.CounterexampleProperties β ε c LinearIsometry.id := by
    simpa only [s.beta_eq] using h
  exact existsPlanarCertificate_congr hc1 hc2 hβ

/-- thm:main. For every `n ≥ 2`, `0 < c1 < c2 < 1`, `0 < ε < 1` and `0 < β < 1`,
the actual general polar construction gives an infinite classical DFP sequence with
strong Wolfe steps and gradient norms tending to one. Its global Hessian is within `ε`
of identity and is globally `β`-Hölder, with every higher exponent failing on the original
initial level set. The origin is
the unique minimizer and the complete cluster set is the unit circle in an embedded plane. -/
theorem main (n : ℕ) (hn : 2 ≤ n) (c1 c2 ε β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c1 c2,
      Transport.CounterexampleProperties β ε w
        (DFP.Polar.OrthogonalExtension.planeEmbedding n hn) := by
  obtain ⟨s⟩ := planarSource c1 c2 ε β hc1 hc12 hc2 hε hβ
  obtain ⟨c, hproperties⟩ := s.existsPlanarCertificate
  obtain ⟨w, hsource, hfinal⟩ :=
    Transport.extendPlanarCertificate n hn c hproperties hβ.1.le hε.1.le
  exact ⟨w, hfinal⟩

/-- Helper for thm:main: the same arbitrary-dimensional witness retains its complete
actual planar construction and literal identity-block extension, for source sequence comparisons. -/
theorem mainWithSource (n : ℕ) (hn : 2 ≤ n) (c1 c2 ε β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ s : PlanarConstruction c1 c2 β ε,
      ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2)
        (s.parameters.withStartIndex s.startIndex).c1 (s.parameters.withStartIndex s.startIndex).c2,
        DFP.Polar.OrthogonalExtension.FinExtensionIdentity n hn s.certificate w ∧
          Transport.CounterexampleProperties s.parameters.beta ε w
            (DFP.Polar.OrthogonalExtension.planeEmbedding n hn) := by
  obtain ⟨s⟩ := planarSource c1 c2 ε β hc1 hc12 hc2 hε hβ
  have hβp : 0 ≤ s.parameters.beta := by
    rw [s.beta_eq]
    exact hβ.1.le
  obtain ⟨w, hsource, hproperties⟩ :=
    Transport.extendPlanarCertificate n hn s.certificate s.properties hβp hε.1.le
  exact ⟨s, w, hsource, hproperties⟩

/-- cor:identity-initialization. Every admissible Wolfe pair and exponent admits an
identity-initialized classical DFP counterexample in every dimension at least two.
The globally Hölder Hessian has positive global bounds, the gradient norm has positive
liminf, and the exact cluster set is a centered ellipse in a two-dimensional subspace. -/
theorem identityInitialization (n : ℕ) (hn : 2 ≤ n) (c1 c2 β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ m > 0, ∃ M ≥ m,
      ∃ result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c1 c2,
        StrongConvexOn Set.univ m result.iteration.objective ∧
          ∃ i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
            Transport.EllipseObjectiveProperties β result.iteration i := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  obtain ⟨s⟩ := planarSource c1 c2 (1 / 2) β hc1 hc12 hc2 hhalf hβ
  obtain ⟨c, hproperties⟩ := s.existsPlanarCertificate
  obtain ⟨P, m, M, planar, result, hP, hPullback, hExtended, hEllipse⟩ :=
    identityExtensionOfPlanar n hn c hproperties hβ.1.le
  exact ⟨min m 1, result.hessianLowerPos, max M 1, result.hessianLowerLeUpper, result,
    DFPWolfe.V21.identityCertificateStrongConvexOn result,
    (DFP.Polar.OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp P.symm.toLinearMap,
    hEllipse⟩

/-- Helper for cor:identity-initialization: the same actual planar source has the exact
square-root spectral Hessian and gradient-liminf bounds, before and after its identity-block
extension, with the literal source step lengths and planar gradient norms retained. -/
theorem identityInitializationQuantitative (n : ℕ) (hn : 2 ≤ n) (c1 c2 β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c1 c2,
      Transport.CounterexampleProperties β (1 / 2) source LinearIsometry.id ∧
        0 < initialMinEigenvalue source ∧ 0 < initialMaxEigenvalue source ∧
          ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) (m M : ℝ)
            (planar : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
              2 m M c1 c2)
            (result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
              (min m 1) (max M 1) c1 c2),
            P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
              DFP.Polar.IdentityInitialization.PullbackData source.iteration planar.iteration P ∧
              DFP.Polar.IdentityInitialization.DimensionExtensionData n hn
                planar.iteration result.iteration ∧
              Transport.EllipseObjectiveProperties β result.iteration
                ((DFP.Polar.OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp
                  P.symm.toLinearMap) ∧
              HasHessianBounds (initialMinEigenvalue source / 2)
                (3 * initialMaxEigenvalue source / 2) planar.iteration.objective ∧
              Real.sqrt (initialMinEigenvalue source) ≤
                liminf (fun k ↦ ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖)
                  atTop ∧
              HasHessianBounds (min (initialMinEigenvalue source / 2) 1)
                (max (3 * initialMaxEigenvalue source / 2) 1) result.iteration.objective ∧
              Real.sqrt (initialMinEigenvalue source) ≤
                liminf (fun k ↦ ‖DFP.gradients result.iteration.objective result.iteration.point k‖)
                  atTop ∧
              result.iteration.stepLength = source.iteration.stepLength ∧
              ∀ k, ‖DFP.gradients result.iteration.objective result.iteration.point k‖ =
                ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖ := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  obtain ⟨s⟩ := planarSource c1 c2 (1 / 2) β hc1 hc12 hc2 hhalf hβ
  obtain ⟨source, hproperties⟩ := s.existsPlanarCertificate
  exact ⟨source, hproperties,
    IdentityQuantitative.quantitativeIdentityExtension n hn source hproperties hβ.1.le⟩

/-- Helper for thm:main and eq:open-question: the actual latest source counterexample
disproves global weak-Wolfe convergence for every admissible Wolfe pair. -/
theorem not_globalWeakWolfeConvergenceAt (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1) :
    ¬ DFP.GlobalWeakWolfeConvergenceAt c1 c2 := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hbounds : (1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨w, hproperties⟩ := main 2 le_rfl c1 c2 (1 / 2) (1 / 2) hc1 hc12 hc2 hhalf hhalf
  exact DFP.not_globalWeakWolfeConvergenceAt_of_counterexample
    w.toWolfeCounterexample le_rfl hhalf.1 hbounds

/-- Helper for thm:main and eq:open-question: the same source witness disproves the
initial-level-set formulation of ordinary weak-Wolfe DFP convergence. -/
theorem not_levelSetGlobalWeakWolfeConvergenceAt (c1 c2 : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1) :
    ¬ DFP.LevelSetGlobalWeakWolfeConvergenceAt c1 c2 := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hbounds : (1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨w, hproperties⟩ := main 2 le_rfl c1 c2 (1 / 2) (1 / 2) hc1 hc12 hc2 hhalf hhalf
  exact DFP.not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    w.toWolfeCounterexample le_rfl hhalf.1 hbounds

end DFPWolfe.Latest
