module

public import ReasLib.Optimization.DFP.Polar.OrthogonalExtension
public import ReasLib.Optimization.DFP.Polar.IdentityInitialization

/-!
# Transport of an arbitrary-Hölder polar counterexample

These lemmas reuse the exact previously verified direct-sum and linear-coordinate
DFP transports. The input is a supplied planar certificate with the requested
Hölder exponent. No old fixed-exponent counterexample existence theorem is used.
-/

public section

noncomputable section

open Filter
open DFP.Polar.OrthogonalExtension
open DFP.Polar.IdentityInitialization
open scoped Topology

namespace DFP.Polar.General.Transport

/-- Helper for thm:main: the complete source properties attached to one actual DFP certificate and
the same embedded plane, for a prescribed exponent. -/
structure CounterexampleProperties {ι : Type*} [Fintype ι] (β ε : ℝ) {c₁ c₂ : ℝ}
    (w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂)
    (i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι) : Prop where
  /-- Helper for thm:main: the gradient-norm limit is exactly one. -/
  gradientLimit : w.gradientLimit = 1
  /-- Helper for thm:main: the global Hessian is at most ε from identity. -/
  near_identity : ∀ x, ‖hessian w.iteration.objective x - 1‖ ≤ ε
  /-- Helper for thm:main: the requested spectral interval is global. -/
  accuracy_bounds : HasHessianBounds (1 - ε) (1 + ε) w.iteration.objective
  /-- Helper for thm:main: the prescribed exponent controls the global Hessian modulus. -/
  holder : ∃ H ≥ 0, ∀ x y,
    ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
      H * ‖x - y‖ ^ β
  /-- Helper for thm:main: the value at the origin is normalized to zero. -/
  origin : w.iteration.objective 0 = 0
  /-- Helper for thm:main: the origin is the unique global minimizer. -/
  unique_minimizer : ∀ x,
    (∀ y, w.iteration.objective x ≤ w.iteration.objective y) ↔ x = 0
  /-- Helper for thm:main: the complete cluster set is the unit circle in the source plane. -/
  cluster : {x | MapClusterPt x atTop w.iteration.point} = i '' Metric.sphere 0 1
  /-- Helper for thm:main: every larger exponent fails on the actual initial sublevel. -/
  no_holder_initial : ∀ β' ∈ Set.Ioc β 1,
    ¬ ∃ L ≥ 0, ∀ x ∈ initialLevelSet w.iteration, ∀ y ∈ initialLevelSet w.iteration,
      ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
        L * ‖x - y‖ ^ β'
  /-- Helper for eq:counterexample-nonlipschitz: the same actual residual ratios diverge. -/
  residual_diverges : ∀ β' ∈ Set.Ioc β 1,
    Tendsto (secantResidualRatio w.iteration β') atTop atTop

/-- Helper for thm:main: the source limit field gives the exact gradient-norm limit one. -/
theorem CounterexampleProperties.gradientNorm_tendsto_one {ι : Type*} [Fintype ι]
    {β ε c₁ c₂ : ℝ} {w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties β ε w i) :
    Tendsto (fun k ↦ ‖DFP.gradients w.iteration.objective w.iteration.point k‖)
      atTop (𝓝 1) := by
  simpa only [h.gradientLimit] using w.gradientNormTendsto

/-- Helper for thm:main: the exact source direct sum transports all analytic, cluster, and
initial-level sharpness properties of the supplied certificate. -/
theorem CounterexampleProperties.orthogonalSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {β ε c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {d : DFP.StrongWolfeCounterexample (ι ⊕ κ) (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties β ε c i) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hd : d.iteration = c.iteration.orthogonalSum (κ := κ) c.stepLengthPos)
    (hlimit : d.gradientLimit = c.gradientLimit) :
    CounterexampleProperties β ε d ((leftEmbedding (κ := κ)).comp i) := by
  have hobjective : d.iteration.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := κ) c.iteration.objective := by
    rw [hd, DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hpoint : d.iteration.point = leftEmbedding (κ := κ) ∘ c.iteration.point := by
    funext k
    rw [hd, DFP.InverseIteration.orthogonalSum_point, embed_eq_leftEmbedding]
    rfl
  have hlower : 1 - ε ≤ 1 := by linarith
  have hupper : 1 ≤ 1 + ε := by linarith
  have horigin := objective_orthogonal_unique_origin (κ := κ) h.origin h.unique_minimizer
  constructor
  · exact hlimit.trans h.gradientLimit
  · intro x
    rw [hobjective]
    exact (hessian_orthogonal_sub_identity_norm_le c.objectiveContDiff x).trans
      (h.near_identity _)
  · rw [hobjective]
    exact EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective
      c.objectiveContDiff h.accuracy_bounds hlower hupper
  · obtain ⟨H, hH, hholder⟩ := h.holder
    refine ⟨H, hH, ?_⟩
    rw [hobjective]
    exact EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      c.objectiveContDiff hH hβ hholder
  · rw [hobjective]
    exact horigin.1
  · rw [hobjective]
    exact horigin.2
  · rw [hpoint, clusterSet_isometric_embedding, h.cluster, Set.image_image]
    rfl
  · intro β' hβ'
    have hno := h.no_holder_initial β' hβ'
    rw [initialLevelSet_def] at hno
    rw [initialLevelSet_def, hobjective, hpoint, Function.comp_apply]
    exact no_holder_initial_orthogonalSum (κ := κ) c.objectiveContDiff
      (c.iteration.point 0) β' hno
  · intro β' hβ'
    rw [hd, secantResidualRatio_orthogonalSum _ _ c.objectiveContDiff]
    exact h.residual_diverges β' hβ'

/-- Helper for thm:main: the exact isometric reindexing transports all source properties,
retaining the same Hölder constant and the same initial-level obstruction. -/
theorem CounterexampleProperties.pullback {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {β ε c₁ c₂ : ℝ}
    {c : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {d : DFP.StrongWolfeCounterexample κ (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties β ε c i)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hd : d.iteration = c.iteration.pullback_linearIsometryEquiv c.stepLengthPos Q)
    (hlimit : d.gradientLimit = c.gradientLimit) :
    CounterexampleProperties β ε d (Q.symm.toLinearIsometry.comp i) := by
  have hobjective : d.iteration.objective = c.iteration.objective ∘ Q := by
    rw [hd, DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
  have hpoint : d.iteration.point = Q.symm ∘ c.iteration.point := by
    funext k
    rw [hd, DFP.InverseIteration.pullback_linearIsometryEquiv_point]
    rfl
  have horigin := objective_isometric_unique_origin Q h.origin h.unique_minimizer
  constructor
  · exact hlimit.trans h.gradientLimit
  · intro x
    rw [hobjective, hessian_isometric_sub_identity_norm c.objectiveContDiff Q]
    exact h.near_identity _
  · rw [hobjective]
    exact hessianBounds_isometric c.objectiveContDiff Q h.accuracy_bounds
  · obtain ⟨H, hH, hholder⟩ := h.holder
    refine ⟨H, hH, ?_⟩
    rw [hobjective]
    exact hessian_holder_isometric c.objectiveContDiff Q hholder
  · rw [hobjective]
    exact horigin.1
  · rw [hobjective]
    exact horigin.2
  · have hcluster := clusterSet_isometric_embedding Q.symm.toLinearIsometry c.iteration.point
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hcluster
    rw [hpoint, hcluster, h.cluster, Set.image_image]
    rfl
  · intro β' hβ'
    have hno := h.no_holder_initial β' hβ'
    rw [initialLevelSet_def] at hno
    rw [initialLevelSet_def, hobjective, hpoint, Function.comp_apply]
    exact no_holder_initial_isometric c.objectiveContDiff Q (c.iteration.point 0) β' hno
  · intro β' hβ'
    rw [hd, secantResidualRatio_isometric _ _ c.objectiveContDiff Q]
    exact h.residual_diverges β' hβ'

/-- Helper for thm:main: all dimensions `n≥2` admit the exact source orthogonal extension of any
supplied planar certificate with all its source properties preserved. -/
theorem extendPlanarCertificate (n : ℕ) (hn : 2 ≤ n) {β ε c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂)
    (h : CounterexampleProperties β ε c LinearIsometry.id)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      FinExtensionIdentity n hn c w ∧ CounterexampleProperties β ε w (planeEmbedding n hn) := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hlower : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hupper : (1 : ℝ) ≤ 3 / 2 := by norm_num
  have hthree : (0 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨d, hd, hlimit⟩ := orthogonalSumWithIteration (κ := Fin (n - 2)) c hlower hupper
  have hdProperties := h.orthogonalSum hβ hε hd hlimit
  let Q := coordinateEquiv n hn
  obtain ⟨w, hw, hwlimit⟩ := pullbackWithIteration d Q hhalf hthree
  have hwProperties := hdProperties.pullback Q hw hwlimit
  have hproperties : CounterexampleProperties β ε w (planeEmbedding n hn) := by
    rw [planeEmbedding_def]
    simpa only [Q, LinearIsometry.comp_id] using hwProperties
  have hobjective : w.iteration.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2)) c.iteration.objective ∘
        coordinateEquiv n hn := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_objective, hd,
      DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hpoint (k : ℕ) : w.iteration.point k = planeEmbedding n hn (c.iteration.point k) := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_point, hd,
      DFP.InverseIteration.orthogonalSum_point, embed_eq_leftEmbedding, planeEmbedding_apply]
  have hstep : w.iteration.stepLength = c.iteration.stepLength := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength, hd,
      DFP.InverseIteration.orthogonalSum_stepLength]
  have hmatrix (k : ℕ) :
      w.iteration.inverseHessian k = extendedMatrix n hn (c.iteration.inverseHessian k) := by
    rw [hw, DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian, hd,
      DFP.InverseIteration.orthogonalSum_inverseHessian, extendedMatrix_def]
  have hplane (x : EuclideanSpace ℝ (Fin 2)) :
      w.iteration.objective (planeEmbedding n hn x) = c.iteration.objective x := by
    rw [hobjective, Function.comp_apply, planeEmbedding_apply,
      (coordinateEquiv n hn).apply_symm_apply, leftEmbedding_apply,
      EuclideanSpace.OrthogonalSum.Gradient.objective_inl]
  exact ⟨w, ⟨hobjective, hpoint, hstep, hmatrix, hplane⟩, hproperties⟩



/-- Helper for cor:identity-initialization: all geometric and regularity conclusions of the source
identity initialization for the prescribed exponent. -/
structure EllipseObjectiveProperties {ι : Type*} [Fintype ι] (β : ℝ)
    (it : DFP.InverseIteration ι)
    (i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ ι) : Prop where
  /-- Helper for cor:identity-initialization: the ellipse is the injective image of the circle. -/
  injective : Function.Injective i
  /-- Helper for cor:identity-initialization: its linear span is two dimensional. -/
  range_finrank : Module.finrank ℝ (LinearMap.range i) = 2
  /-- Helper for cor:identity-initialization: the full cluster set is the centered ellipse. -/
  cluster : {x | MapClusterPt x atTop it.point} = i '' Metric.sphere 0 1
  /-- Helper for cor:identity-initialization: the transformed objective retains global β-Hölder
Hessian. -/
  holder : ∃ C ≥ 0, ∀ x y, ‖hessian it.objective x - hessian it.objective y‖ ≤
    C * ‖x - y‖ ^ β
  /-- Helper for cor:identity-initialization: the origin value remains zero. -/
  origin : it.objective 0 = 0
  /-- Helper for cor:identity-initialization: the origin remains the unique minimizer. -/
  unique_minimizer : ∀ x, (∀ y, it.objective x ≤ it.objective y) ↔ x = 0

/-- Helper for cor:identity-initialization: the exact positive square-root coordinate change
normalizes any supplied general-exponent certificate to initial matrix identity. Its complete
circle becomes a centered ellipse and its Hessian retains the prescribed global exponent. -/
theorem normalizeCertificateWithProperties {n : ℕ} (hn : 2 ≤ n) {β ε c₁ c₂ : ℝ}
    (c : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (h : CounterexampleProperties β ε c i) (hβ : 0 ≤ β) :
    ∃ (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (m M : ℝ) (d : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
        n m M c₁ c₂),
      P = (c.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
        DFP.Polar.IdentityInitialization.PullbackData c.iteration d.iteration P ∧
          EllipseObjectiveProperties β d.iteration (P.symm.toLinearMap.comp i.toLinearMap) := by
  obtain ⟨P, m, M, d, hP, hdata⟩ :=
    DFP.Polar.IdentityInitialization.existsNormalizedCertificate hn c
  have hobjective : d.iteration.objective = c.iteration.objective ∘ P :=
    hdata.objective.trans (DFP.Polar.IdentityInitialization.pulledObjective_def c.iteration P)
  have horigin := DFP.Polar.IdentityInitialization.origin_unique_pullback
    c.iteration.objective P h.origin h.unique_minimizer
  have hinjective : Function.Injective (P.symm.toLinearMap.comp i.toLinearMap) :=
    P.symm.injective.comp i.injective
  have hcluster : {x | MapClusterPt x atTop d.iteration.point} =
      (P.symm.toLinearMap.comp i.toLinearMap) '' Metric.sphere 0 1 := by
    rw [hdata.point, DFP.Polar.IdentityInitialization.pulledPoints_def,
      DFP.Polar.IdentityInitialization.clusterSet_pullback, h.cluster, Set.image_image]
    rfl
  obtain ⟨C, hC, hholder⟩ := h.holder
  let B := ‖P.toContinuousLinearMap‖ ^ 2 * C * ‖P.toContinuousLinearMap‖ ^ β
  have hB : 0 ≤ B := by positivity
  have hHolder : ∀ x y, ‖hessian d.iteration.objective x - hessian d.iteration.objective y‖ ≤
      B * ‖x - y‖ ^ β := by
    rw [hobjective]
    exact hessianHolder_comp_continuousLinearEquiv c.objectiveContDiff P hC hβ hholder
  have hzero : d.iteration.objective 0 = 0 := by
    rw [hobjective]
    exact horigin.1
  have hunique : ∀ x, (∀ y, d.iteration.objective x ≤ d.iteration.objective y) ↔ x = 0 := by
    rw [hobjective]
    exact horigin.2
  have hproperties : EllipseObjectiveProperties β d.iteration
      (P.symm.toLinearMap.comp i.toLinearMap) :=
    ⟨hinjective, DFP.Polar.IdentityInitialization.ellipse_range_finrank _ hinjective,
      hcluster, ⟨B, hB, hHolder⟩, hzero, hunique⟩
  exact ⟨P, m, M, d, hP, hdata, hproperties⟩

/-- Helper for cor:identity-initialization: normalization is performed in the source plane first,
then its actual identity-initialized matrix iteration extends to every larger dimension, with
the full ellipse and positive liminf preserved. -/
theorem extendNormalizedPlanar (n : ℕ) (hn : 2 ≤ n) {β m M c₁ c₂ : ℝ}
    (d : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c₁ c₂)
    (i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hproperties : EllipseObjectiveProperties β d.iteration i) (hβ : 0 ≤ β) :
    ∃ result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
        (min m 1) (max M 1) c₁ c₂,
      DimensionExtensionData n hn d.iteration result.iteration ∧
        EllipseObjectiveProperties β result.iteration
          ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) := by
  let Q := OrthogonalExtension.coordinateEquiv n hn
  let itSum := d.iteration.orthogonalSum (κ := Fin (n - 2)) d.stepLengthPos
  have hStepSum : ∀ k, 0 < itSum.stepLength k := by
    simpa only [itSum, DFP.InverseIteration.orthogonalSum_stepLength] using d.stepLengthPos
  let it := itSum.pullback_linearIsometryEquiv hStepSum Q
  have hObjective : it.objective =
      EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
        d.iteration.objective ∘ Q := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_objective, itSum,
      DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
  have hPoint (k : ℕ) : it.point k =
      OrthogonalExtension.planeEmbedding n hn (d.iteration.point k) := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_point, itSum,
      DFP.InverseIteration.orthogonalSum_point, OrthogonalExtension.embed_eq_leftEmbedding,
      OrthogonalExtension.planeEmbedding_apply, Q]
  have hAlpha : it.stepLength = d.iteration.stepLength := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_stepLength, itSum,
      DFP.InverseIteration.orthogonalSum_stepLength]
  have hMatrix (k : ℕ) : it.inverseHessian k =
      OrthogonalExtension.extendedMatrix n hn (d.iteration.inverseHessian k) := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian, itSum,
      DFP.InverseIteration.orthogonalSum_inverseHessian, OrthogonalExtension.extendedMatrix_def, Q]
  have hm : 0 < min m 1 := lt_min d.hessianLowerPos zero_lt_one
  have hmM : min m 1 ≤ max M 1 := (min_le_left _ _).trans
    (d.hessianLowerLeUpper.trans (le_max_left _ _))
  have hC2Sum : ContDiff ℝ 2 itSum.objective := by
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective d.objectiveContDiff
  have hC2 : ContDiff ℝ 2 it.objective := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
    exact hC2Sum.comp Q.contDiff
  have hStep : ∀ k, 0 < it.stepLength k := by
    rw [hAlpha]
    exact d.stepLengthPos
  have hWide : HasHessianBounds (min m 1) (max M 1) d.iteration.objective :=
    PlanarCounterexample.hessianBounds_mono d.objectiveContDiff d.hessianBounds
      (min_le_left _ _) (le_max_left _ _)
  have hBoundsSum : HasHessianBounds (min m 1) (max M 1) itSum.objective := by
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_objective, DFP.OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.hasHessianBounds_objective
      d.objectiveContDiff hWide (min_le_right _ _) (le_max_right _ _)
  have hGradientDiffSum : Differentiable ℝ (gradient itSum.objective) :=
    (hC2Sum.gradient_succ (n := 1)).differentiable_one
  have hMnonneg : 0 ≤ max M 1 := zero_le_one.trans (le_max_right _ _)
  have hBounds : HasHessianBounds (min m 1) (max M 1) it.objective := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_objective]
    exact hBoundsSum.comp_linearIsometryEquiv Q hGradientDiffSum hm.le hMnonneg
  have hStrongSum (k : ℕ) : LineSearch.IsStrongWolfe c₁ c₂ itSum.objective
      (itSum.point k) (itSum.point (k + 1) - itSum.point k) := by
    have h := (LineSearch.IsStrongWolfe.orthogonalSum_iff (κ := Fin (n - 2))).mpr
      (d.strongWolfe k)
    simpa only [itSum, DFP.InverseIteration.orthogonalSum_objective,
      DFP.InverseIteration.orthogonalSum_point, DFP.OrthogonalSum.objective_eq,
      OrthogonalExtension.embed_eq_leftEmbedding, OrthogonalExtension.leftEmbedding_apply,
      map_sub] using h
  have hStrong (k : ℕ) : LineSearch.IsStrongWolfe c₁ c₂ it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    have h := (hStrongSum k).comp_linearIsometryEquiv Q
    simpa only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_objective,
      DFP.InverseIteration.pullback_linearIsometryEquiv_point, map_sub] using h
  have hInitial : it.inverseHessian 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    dsimp only [it]
    rw [DFP.InverseIteration.pullback_linearIsometryEquiv_inverseHessian]
    dsimp only [itSum]
    rw [DFP.InverseIteration.orthogonalSum_inverseHessian, d.initialInverseHessian_eq_one,
      orthogonal_matrix_one, map_one]
    exact isometric_matrix_one Q
  have hNorm (k : ℕ) : ‖DFP.gradients it.objective it.point k‖ =
      ‖DFP.gradients d.iteration.objective d.iteration.point k‖ := by
    simp only [it, DFP.InverseIteration.pullback_linearIsometryEquiv_gradients,
      Q.symm.norm_map, itSum, DFP.InverseIteration.orthogonalSum_gradients,
      DFP.OrthogonalSum.norm_embed]
  have hLiminf : 0 < liminf (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop := by
    simpa only [hNorm] using d.gradientNormLiminfPos
  have hTail : ∃ δ > 0, ∀ᶠ k in atTop, δ ≤ ‖DFP.gradients it.objective it.point k‖ := by
    simpa only [hNorm] using d.gradientNormEventuallyPositive
  have hPointFun : it.point = OrthogonalExtension.planeEmbedding n hn ∘ d.iteration.point := by
    funext k
    exact hPoint k
  have hCluster : {z | MapClusterPt z atTop it.point} =
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) '' Metric.sphere 0 1 := by
    rw [hPointFun, OrthogonalExtension.clusterSet_isometric_embedding,
      hproperties.cluster, Set.image_image]
    rfl
  have hInjective : Function.Injective
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) :=
    (OrthogonalExtension.planeEmbedding n hn).injective.comp hproperties.injective
  have hOriginSum := OrthogonalExtension.objective_orthogonal_unique_origin
    (κ := Fin (n - 2)) hproperties.origin hproperties.unique_minimizer
  have hOrigin := OrthogonalExtension.objective_isometric_unique_origin Q
    hOriginSum.1 hOriginSum.2
  have hZero : it.objective 0 = 0 := by
    rw [hObjective]
    exact hOrigin.1
  have hUnique : ∀ x, (∀ y, it.objective x ≤ it.objective y) ↔ x = 0 := by
    rw [hObjective]
    exact hOrigin.2
  obtain ⟨C, hC, hHolder⟩ := hproperties.holder
  have hHolderSum : ∀ x y,
      ‖hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
        d.iteration.objective) x -
        hessian (EuclideanSpace.OrthogonalSum.Gradient.objective (κ := Fin (n - 2))
          d.iteration.objective) y‖ ≤ C * ‖x - y‖ ^ β :=
    EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      d.objectiveContDiff hC hβ hHolder
  have hHolderFinal : ∀ x y, ‖hessian it.objective x - hessian it.objective y‖ ≤
      C * ‖x - y‖ ^ β := by
    rw [hObjective]
    exact OrthogonalExtension.hessian_holder_isometric
      (EuclideanSpace.OrthogonalSum.Gradient.contDiff_objective d.objectiveContDiff) Q hHolderSum
  have hHolderPackage : ∃ C ≥ 0, ∀ x y,
      ‖hessian it.objective x - hessian it.objective y‖ ≤ C * ‖x - y‖ ^ β :=
    ⟨C, hC, hHolderFinal⟩
  have hProperties : EllipseObjectiveProperties β it
      ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp i) :=
    ⟨hInjective, ellipse_range_finrank _ hInjective, hCluster, hHolderPackage, hZero, hUnique⟩
  let result : WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
      (min m 1) (max M 1) c₁ c₂ := {
    iteration := it
    c₁_pos := d.c₁_pos
    c₁_lt_c₂ := d.c₁_lt_c₂
    c₂_lt_one := d.c₂_lt_one
    hessianLowerPos := hm
    hessianLowerLeUpper := hmM
    objectiveContDiff := hC2
    stepLengthPos := hStep
    hessianBounds := hBounds
    strongWolfe := hStrong
    initialInverseHessian_eq_one := hInitial
    gradientNormLiminfPos := hLiminf
    gradientNormEventuallyPositive := hTail
  }
  have hIt : result.iteration = it := rfl
  refine ⟨result, ?_, ?_⟩
  · rw [hIt]
    exact ⟨hObjective, hPoint, hAlpha, hMatrix⟩
  · rw [hIt]
    exact hProperties



/-- Helper for thm:main: the same source witness meeting a smaller global near-identity tolerance
also meets every larger requested tolerance. -/
theorem CounterexampleProperties.mono {ι : Type*} [Fintype ι] {β δ ε c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample ι (1 / 2) (3 / 2) c₁ c₂}
    {i : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ ι}
    (h : CounterexampleProperties β δ w i) (hδε : δ ≤ ε) :
    CounterexampleProperties β ε w i := by
  have hnear (x) : ‖hessian w.iteration.objective x - 1‖ ≤ ε :=
    (h.near_identity x).trans hδε
  have hlower : 1 - ε ≤ 1 - δ := by linarith
  have hupper : 1 + δ ≤ 1 + ε := by linarith
  have hbounds := hessianBounds_mono w.objectiveContDiff h.accuracy_bounds hlower hupper
  exact ⟨h.gradientLimit, hnear, hbounds, h.holder, h.origin, h.unique_minimizer,
    h.cluster, h.no_holder_initial, h.residual_diverges⟩

end DFP.Polar.General.Transport
