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

/-- Lemma 3 of `20251124-DFP/MP.zip`: the exact raw matrix recurrence
used by the fixed and general polar constructions. -/
theorem lemma3_matrixStep (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (k : ℕ) :
    p.matrix (k + 1) = DFP.Polar.matrixStep (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1)) := by
  exact Parameters.matrix_step p hβ hstart k

/-- Theorem 4 of `20251124-DFP/MP.zip`: the fixed `(1/4,1/2)` and
`beta=1/2` construction is an instance of the fully retained planar source. -/
theorem theorem4_concrete :
    Nonempty (DFPWolfe.Latest.PlanarConstruction (1 / 4) (1 / 2) (1 / 2) (1 / 2)) := by
  apply DFPWolfe.Latest.planarSource
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Lemma 5 of `20251124-DFP/MP.zip`: the fixed limiting polar stages close
the explicit even and odd reference states. -/
theorem lemma5_fixedSingleLimit :
    Normalized.leadingStage (1 : ℝ) (cycleState (9 / 4) (2 / 3)) =
        cycleState (9 / 4) (1 / 3) ∧
      Normalized.leadingStage (1 : ℝ) (cycleState (9 / 4) (1 / 3)) =
        cycleState (9 / 4) (2 / 3) := by
  have hcycle : CycleDomain (1 : ℝ) 1 (1 / 3) := by
    constructor <;> norm_num
  have hmatch := And.intro (evenToOdd hcycle) (oddToEven hcycle)
  simpa [evenState, oddState, cycleState, cycleGamma, cycleLambdaEven,
    cycleLambdaOdd] using hmatch

/-- Lemma 6 of `20251124-DFP/MP.zip`: the normalized recurrence has a
uniform trajectory bound before the starting index is chosen. -/
theorem lemma6_fixedCycle (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧
      ∀ j0 : ℕ, J ≤ j0 → Continuation.TrajectoryBounds p j0 N M := by
  exact Continuation.existsTrajectoryBounds p hβ hβone

/-- Lemma 7 of `20251124-DFP/MP.zip`: the actual recurrence remains feasible
for every later index and its odd phase has a uniform transverse estimate. -/
theorem lemma7_fixedContinuation (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ K > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      Continuation.TrajectoryBounds p j0 N M ∧
        (∀ k : ℕ, Continuation.RawFeasible (p.withStartIndex j0) k) ∧
        ∀ j : ℕ,
          ‖(p.withStartIndex j0).normalizedOddState j -
              p.oddReference (Continuation.stateAt p j0 j).1‖ ≤
            K / ((j0 + j : ℕ) : ℝ) := by
  exact Continuation.existsContinuationEstimates p hβ hβone

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
    ∃ N > 0, ∃ M > 0, ∃ K > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      Continuation.TrajectoryBounds p j0 N M ∧
        (∀ k : ℕ, Continuation.RawFeasible (p.withStartIndex j0) k) := by
  obtain ⟨N, hN, M, hM, K, hK, J, hJ, h⟩ :=
    Continuation.existsContinuationEstimates p hβ hβone
  refine ⟨N, hN, M, hM, K, hK, J, hJ, ?_⟩
  intro j0 hj0
  have hdata := h j0 hj0
  exact ⟨hdata.1, hdata.2.1⟩

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
