/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.Latest.Main
public import DFPWolfe.Latest.PlanarConvergence
public import DFPWolfe.Latest.SecantDegeneration
public import DFPWolfe.Latest.Lemma_PolarDirectionUpdate
public import DFPWolfe.Latest.Lemma_PolarLimitingCycle
public import DFPWolfe.Latest.Lemma_PolarParameterChoice
public import DFPWolfe.Latest.Lemma_PolarCycleEstimates
public import DFPWolfe.Latest.Lemma_4_PolarContinuation
public import DFPWolfe.Latest.Lemma_5_PolarGeometry
public import DFPWolfe.Latest.Lemma_6_PolarInterpolation

public section

noncomputable section

open Filter
open scoped Topology

namespace DFPWolfe.MP20251124

open DFP.Polar.General

/-- Theorem 1 of `20251124-DFP/MP.zip`: the general polar counterexample
certificate, including the sharp initial-level-set Hölder obstruction. -/
theorem theorem1 (n : ℕ) (hn : 2 ≤ n) (c1 c2 ε β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c1 c2,
      Transport.CounterexampleProperties β ε w
        (DFP.Polar.OrthogonalExtension.planeEmbedding n hn) := by
  exact DFPWolfe.Latest.main n hn c1 c2 ε β hc1 hc12 hc2 hε hβ

/-- Theorem 2 of `20251124-DFP/MP.zip`: planar weak-Wolfe convergence
under local Lipschitz continuity of the Hessian. -/
theorem theorem2
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧ (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧
      ((∃ K : ℕ, gradient f (x K) = 0 ∧ x K = xstar ∧ ∀ k, K ≤ k → x k = xstar) ∨
        ((∀ k, gradient f (x k) ≠ 0) ∧ Tendsto x atTop (𝓝 xstar) ∧
          Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0))) := by
  exact DFPWolfe.Latest.planarConvergenceCases orbit hf hμ hHessian hH₀ hWolfe hNeighborhood

/-- Lemma 3 of `20251124-DFP/MP.zip`: the exact polar step interface.
The source search step, positive step length, inverse DFP update, and raw
matrix recurrence are exposed on one actual `Parameters` orbit. -/
theorem lemma3_matrixStep (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1)
    (hsin : 0 < Real.sin (p.angleIncrement k))
    (hr : 0 < p.radiusRatio k)
    (hbalance : p.radius k = p.radiusRatio k * p.radius (k + 1))
    (hrNext : 0 < p.radius (k + 1))
    (hσ : 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1))) :
    p.matrix (k + 1) = DFP.Polar.matrixStep (p.matrix k) (p.angleIncrement k)
        (p.zeta k) (p.zeta (k + 1)) ∧
      0 < p.stepLength k ∧
      WithLp.ofLp (p.point (k + 1) - p.point k) =
        (-p.stepLength k) •
          (p.inverseHessian k *ᵥ WithLp.ofLp (p.gradients k)) ∧
      0 < WithLp.ofLp (p.point (k + 1) - p.point k) ⬝ᵥ
        WithLp.ofLp (p.gradients (k + 1) - p.gradients k) ∧
      p.inverseHessian (k + 1) = Matrix.inverseDFPUpdate (p.inverseHessian k)
        (WithLp.ofLp (p.point (k + 1) - p.point k))
        (WithLp.ofLp (p.gradients (k + 1) - p.gradients k)) := by
  refine ⟨Parameters.matrix_step p hβ hstart k, ?_, ?_, ?_, ?_⟩
  · exact p.stepLength_pos k hZ hC hsin hr
  · exact p.chord_search k hZ hC hr hbalance
  · exact p.secant_pairing_pos k hbalance hrNext hsin hσ
  · exact p.inverseHessian_step k hβ hstart hbalance hZ
      hrNext hsin hσ

 /-- Helper for `lem:polar-dfp`: the explicit polar search step and its
 positive coefficient for one feasible source stage. -/
 theorem lemma3_polarSearchStep (Z : Matrix (Fin 2) (Fin 2) ℝ)
     (θ δ r rNext ζ : ℝ) (hZ : Z.PosDef) (hC : 0 < Z 0 1)
     (hζ : 0 < ζ) (hsin : 0 < Real.sin δ) (hW : 0 < DFP.Polar.radiusRatioOf Z δ)
     (hr : rNext * DFP.Polar.radiusRatioOf Z δ = r) :
     0 < Z.det * Real.sin δ / (ζ * Z 0 1 * DFP.Polar.radiusRatioOf Z δ) ∧
       WithLp.ofLp (rNext • DFP.Polar.polarUnit (θ + δ) -
         r • DFP.Polar.polarUnit θ) =
         (-(Z.det * Real.sin δ /
           (ζ * Z 0 1 * DFP.Polar.radiusRatioOf Z δ))) •
           ((DFP.Polar.rotationMatrix θ * Z⁻¹ *
             (DFP.Polar.rotationMatrix θ).transpose) *ᵥ
             WithLp.ofLp (ζ • (r • DFP.Polar.polarUnit θ))) := by
   constructor
   · exact DFP.Polar.PhysicalRealization.stepLength_pos Z δ ζ hZ hC hζ hsin hW
   · exact DFP.Polar.PhysicalRealization.search_step Z θ δ r rNext ζ hr
       hZ.isHermitian hC.ne' hZ.det_pos.ne' hζ.ne' hW.ne'

 /-- Theorem 4 of `20251124-DFP/MP.zip`: the fixed `(1/4,1/2)` and
`beta=1/2` construction exposes its actual objective, Wolfe orbit, and
regularity certificate. -/
theorem theorem4_concrete :
    ∃ s : DFPWolfe.Latest.PlanarConstruction (1 / 4) (1 / 2) (1 / 2) (1 / 2),
      0 < s.supportScale ∧
        s.sourceData.objectiveEstimates.contDiff ∧
        s.sourceData.objectiveEstimates.hessian_bounds ∧
        s.sourceData.objectiveEstimates.strongConvex ∧
        s.sourceData.objectiveEstimates.hessian_holder ∧
        (∀ k, s.sourceData.objectiveEstimates.endpoints k) ∧
        (∀ x, ‖x‖ ≤ 1 → s.sourceData.objectiveEstimates.disk x) ∧
        (∀ x, s.sourceData.objectiveEstimates.hessian_near_identity x) ∧
        s.sourceData.clusterSet = Metric.sphere 0 1 ∧
        s.sourceData.gradientNorm_tendsto ∧
        s.sourceIdentity ∧
        (∀ k, LineSearch.IsStrongWolfe (1 / 4) (1 / 2)
          ((s.parameters.withStartIndex s.startIndex).objective s.supportScale)
          ((s.parameters.withStartIndex s.startIndex).point k)
          ((s.parameters.withStartIndex s.startIndex).point (k + 1) -
            (s.parameters.withStartIndex s.startIndex).point k) := by
  obtain ⟨s⟩ := DFPWolfe.Latest.planarSource (1 / 4) (1 / 2) (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨s, s.supportScale_pos, s.sourceData.objectiveEstimates.contDiff,
    s.sourceData.objectiveEstimates.hessian_bounds,
    s.sourceData.objectiveEstimates.strongConvex,
    s.sourceData.objectiveEstimates.hessian_holder,
    s.sourceData.objectiveEstimates.endpoints,
    s.sourceData.objectiveEstimates.disk,
    s.sourceData.objectiveEstimates.hessian_near_identity,
    s.sourceData.clusterSet,
    s.sourceData.gradientNorm_tendsto,
    s.sourceIdentity, ?_⟩
  intro k
  have hc1 := s.parameters.withStartIndex_c1 s.startIndex
  have hc2 := s.parameters.withStartIndex_c2 s.startIndex
  simpa only [hc1, hc2, s.c1_eq, s.c2_eq,
    s.sourceIdentity.objective, s.sourceIdentity.point] using
    s.certificate.strongWolfe k

/-- Lemma 5 of `20251124-DFP/MP.zip`: the fixed limiting polar stages close
the explicit even and odd reference states. -/
theorem lemma5_fixedSingleLimit :
    Normalized.leadingStage (1 : ℝ) (evenState 1 1 (1 / 3)) =
        oddState 1 1 (1 / 3) ∧
      Normalized.leadingStage (1 : ℝ) (oddState 1 1 (1 / 3)) =
        evenState 1 1 (1 / 3) := by
  have hcycle : CycleDomain (1 : ℝ) 1 (1 / 3) := by
    constructor <;> norm_num
  have hmatch := And.intro (evenToOdd hcycle) (oddToEven hcycle)
  simpa only [Parameters.leadingStage_eq_original] using hmatch

/-- Lemma 5 of `20251124-DFP/MP.zip`: the one-step normalized map has the
explicit limiting formula for every nonzero angular coefficient and regular
positive off-diagonal state. -/
theorem lemma5_fixedSingleLimit_general (a : ℝ) (x : ℝ × ℝ × ℝ)
    (ha : a ≠ 0) (hC : x.2.1 ≠ 0) :
    Tendsto (fun t : ℝ ↦ Normalized.stage a t x 1 1) (𝓝 0)
      (𝓝 (Normalized.leadingStage a x)) := by
  have hAnalytic : AnalyticAt ℝ (fun t : ℝ ↦ Normalized.stage a t x 1 1) 0 := by
    have h := Normalized.stageAlong_analyticAt
      (a := fun _ : ℝ ↦ a) (t := fun y : ℝ ↦ y) (X := fun _ : ℝ ↦ x)
      (ζ := fun _ : ℝ ↦ 1) (η := fun _ : ℝ ↦ 1) (z := 0)
      analyticAt_const analyticAt_id analyticAt_const analyticAt_const
      analyticAt_const ha rfl hC (by
        simp [Normalized.stageSigma_def, Normalized.stepV_def,
          Normalized.stepW_def])
    simpa only using h
  have hcont : Tendsto (fun t : ℝ ↦ Normalized.stage a t x 1 1) (𝓝 0)
      (𝓝 (Normalized.stage a 0 x 1 1)) := hAnalytic.continuousAt
  simpa only [Normalized.stage_zero] using hcont

/-- Helper for lem:fixed-single-limit: the canceled normalized stage at zero
scale is the explicit limiting map used in the manuscript. -/
theorem lemma5_limitingStage (a : ℝ) (x : ℝ × ℝ × ℝ) :
    Normalized.stage a 0 x 1 1 = Normalized.leadingStage a x := by
  exact Normalized.stage_zero a x

/-- Helper for lem:fixed-cycle: the two-stage normalized source map has the
analytic interface used for the fixed-cycle perturbation argument. -/
theorem lemma6_cycleAnalytic (p : Parameters) (hβ : 0 < p.beta)
    (x : ℝ × ℝ × ℝ) (hφ : AnalyticAt ℝ p.feedbackPotential x.1)
    (hC : x.2.1 ≠ 0)
    (hCNext : (Normalized.leadingStage (p.evenAngleFactor 0) x).2.1 ≠ 0) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
        Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor
          p.feedbackPotential z.1.1 z.1.2 z.2)
      ((0, 0), x) := by
  apply Normalized.map_analyticAt p.beta p.evenAngleFactor p.oddAngleFactor
    p.feedbackPotential x
  · exact p.evenAngleFactor_analyticAt
  · exact p.oddAngleFactor_analyticAt
  · exact hφ
  · rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  · rw [p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos.ne'
  · exact hC
  · exact hCNext

/-- Lemma 6 of `20251124-DFP/MP.zip`: the normalized recurrence has a
uniform trajectory bound before the starting index is chosen. -/
theorem lemma6_fixedCycle (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧
      ∀ j0 : ℕ, J ≤ j0 → Continuation.TrajectoryBounds p j0 N M := by
  exact Continuation.existsTrajectoryBounds p hβ hβone

/-- Lemma 7 of `20251124-DFP/MP.zip`: the actual recurrence remains feasible
for every later index and its odd phase has a uniform transverse estimate. -/
theorem lemma7_fixedContinuation (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ K : ℝ, 0 < K ∧ ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      Continuation.TrajectoryBounds p j0 N M ∧
        (∀ j : ℕ,
          Continuation.fastSize p (Continuation.stateAt p j0 j) ≤
              N / ((j0 + j : ℕ) : ℝ) ∧
            |Continuation.slowError p (Continuation.stateAt p j0 j)| ≤
              M * scale p.beta j0 j ^ (1 - p.beta)) ∧
        (∀ k : ℕ, Continuation.RawFeasible (p.withStartIndex j0) k) ∧
        ∀ j : ℕ,
          ‖(p.withStartIndex j0).normalizedOddState j -
              p.oddReference (Continuation.stateAt p j0 j).1‖ ≤
            K / ((j0 + j : ℕ) : ℝ) := by
  obtain ⟨N, hN, M, hM, K, hK, J, hJ, h⟩ :=
    Continuation.existsContinuationEstimates p hβ hβone
  refine ⟨N, hN, M, hM, K, hK, J, hJ, ?_⟩
  intro j0 hj0
  obtain ⟨htrajectory, hraw, hodd⟩ := h j0 hj0
  refine ⟨htrajectory, ?_, hraw, hodd⟩
  intro j
  exact ⟨htrajectory.fast_bound j, htrajectory.slow_bound j⟩

/-- Lemma 8 of `20251124-DFP/MP.zip`: the actual points have uniform
separation, linear step bounds and the complete unit-circle cluster set. -/
theorem lemma8_fixedGeometry (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
      ∃ a > 0, ∃ b > 0, ∃ s > 0, ∃ V > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j0 : ℕ, J ≤ j0 →
          ActualGeometry.SourceGeometricData p j0 N M B K c U a b s V := by
  exact ActualGeometry.existsSourceGeometry p hβ hβone

/-- Lemma 9 of `20251124-DFP/MP.zip`: the explicit cutoff sum realizes
all endpoint jets and the requested global Hessian bounds. -/
theorem lemma9_fixedRealization (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (ε : ℝ) (hεpos : 0 < ε) (hε : ε < 1) :
    ∃ N > 0, ∃ M > 0, ∃ κ > 0, ∃ H ≥ 0, ∃ s > 0, ∃ Ustep > 0, ∃ Cobj ≥ 0,
      ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
        Objective.SourceObjectiveData p j0 N M κ ε H ∧
          Objective.SourceGeometricData (p.withStartIndex j0) κ s Ustep Cobj := by
  exact Objective.existsSourceObjectiveData p hβ hβone ε hεpos hε

/-- Lemma 10 of `20251124-DFP/MP.zip`: every admissible Wolfe pair
admits the strict stable reference parameters used by the general family. -/
theorem lemma10_generalReference {c1 c2 : ℝ} (hc1 : 0 < c1)
    (hc12 : c1 < c2) (hc2 : c2 < 1) :
    ∃ ell z : ℝ, StrictWolfeBase c1 c2 ell z := by
  exact strictWolfeBaseExists hc1 hc12 hc2

/-- Lemma 11 of `20251124-DFP/MP.zip`: the general continuation interface
is available for every admissible exponent. -/
theorem lemma11_generalContinuation (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ K : ℝ, 0 < K ∧ ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      Continuation.TrajectoryBounds p j0 N M ∧
        (∀ j : ℕ,
          Continuation.fastSize p (Continuation.stateAt p j0 j) ≤
              N / ((j0 + j : ℕ) : ℝ) ∧
            |Continuation.slowError p (Continuation.stateAt p j0 j)| ≤
              M * scale p.beta j0 j ^ (1 - p.beta)) ∧
        (∀ k : ℕ, Continuation.RawFeasible (p.withStartIndex j0) k) := by
  obtain ⟨N, hN, M, hM, K, hK, J, hJ, h⟩ :=
    Continuation.existsContinuationEstimates p hβ hβone
  refine ⟨N, hN, M, hM, K, hK, J, hJ, ?_⟩
  intro j0 hj0
  have hdata := h j0 hj0
  refine ⟨hdata.1, ?_, hdata.2.1⟩
  intro j
  exact ⟨hdata.1.fast_bound j, hdata.1.slow_bound j⟩

/-- Corollary 12 of `20251124-DFP/MP.zip`: identity initialization in every
finite dimension at least two. -/
theorem corollary12_identityInitialization (n : ℕ) (hn : 2 ≤ n) (c1 c2 β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ m > 0, ∃ M ≥ m,
      ∃ result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n m M c1 c2,
        StrongConvexOn Set.univ m result.iteration.objective ∧
          ∃ i : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
            Transport.EllipseObjectiveProperties β result.iteration i := by
  exact DFPWolfe.Latest.identityInitialization n hn c1 c2 β hc1 hc12 hc2 hβ

/-- Lemma 13 of `20251124-DFP/MP.zip`: nonconvergence forces the planar
DFP secant coefficient and the smallest inverse-Hessian eigenvalue to vanish. -/
theorem lemma13_planarDegeneration (iteration : DFP.SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective)
    (hstrong : StrongConvexOn Set.univ μ iteration.objective)
    (hμ : 0 < μ) (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃! xstar : EuclideanSpace ℝ (Fin 2),
      (∀ z, iteration.objective xstar ≤ iteration.objective z) ∧
        (¬ Tendsto iteration.point atTop (𝓝 xstar) →
          DFP.PlanarConvergence.SecantDegeneration.DegenerationEstimates iteration) := by
  exact DFPWolfe.Latest.planarDegeneration iteration hf hstrong hμ hStep hw

end DFPWolfe.MP20251124
