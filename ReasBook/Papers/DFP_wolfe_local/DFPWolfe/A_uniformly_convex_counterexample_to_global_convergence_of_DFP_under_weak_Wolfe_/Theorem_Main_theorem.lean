/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_4_Counterexample_in_every_dimension_n_ge2
public import ReasLib.Optimization.DFP.GlobalConvergence
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedTransport
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticMatrixIdentityLiminf
public import ReasLib.Optimization.DFP.PlanarConvergence
public import ReasLib.Optimization.DFP.SecantDegeneration
public import ReasLib.Optimization.DFP.WolfeCounterexample.HolderSharpness

/-!
# Main DFP counterexample and planar convergence statements

The counterexample interfaces cover the paper's Wolfe parameter range.
The planar convergence interfaces apply to arbitrary fixed admissible Wolfe
coefficients under local Hessian Lipschitz regularity near the initial sublevel.

The strengthened counterexample is exported as
`existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two`: its single
objective has a globally one-half Hölder Hessian, and no greater exponent works
on its initial sublevel. `existsMatrixIdentityLiminfStrongWolfeHolder` preserves
the Hölder bound with identity initialization.
`SecantIteration.planarDegeneration` requires only a positive-definite search
sequence and the secant equation, and includes vanishing of the smallest eigenvalue.
-/

public section

open Filter
open scoped Topology

namespace DFP

/-- TASK-11: The paper-range strong-Wolfe counterexample is available in every
finite dimension `n` with `2 ≤ n`, while retaining the exact Hessian bounds
`(1 / 2, 3 / 2)`. -/
theorem existsStrongWolfeCounterexample_of_parameterRange
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    Nonempty (StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂) := by
  exact existsStrongWolfeCounterexample_of_dimension_ge_two n hn
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-11 Main theorem: for every pair in the paper's Wolfe range, the
global weak-Wolfe convergence predicate is false. -/
theorem main_not_globalWeakWolfeConvergence_of_parameterRange
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁)
    (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ¬ GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange 2 hdimension
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_globalWeakWolfeConvergenceAt_of_counterexample
    counterexample.toWolfeCounterexample hdimension hlower hupper

/-- TASK-11: The preceding negative convergence theorem is uniform over all
coefficient pairs satisfying `0 < c₁ < 2 / 3` and `2 / 3 ≤ c₂ < 1`. -/
theorem main_not_globalWeakWolfeConvergence_forall_parameterRange :
    ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
      (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
      ¬ GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro c₁ c₂ hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact main_not_globalWeakWolfeConvergence_of_parameterRange
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-15: The same paper-range counterexample refutes the level-set version
of the fixed-coefficient global-convergence predicate.  The explicit
containment field is supplied by the Armijo/DFP descent bridge. -/
theorem main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁)
    (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ¬ LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange 2 hdimension
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    counterexample.toWolfeCounterexample hdimension hlower hupper

/-- TASK-15: The level-set global-convergence predicate is false for every
coefficient pair in the paper's stated range. -/
theorem main_not_levelSetGlobalWeakWolfeConvergence_forall_parameterRange :
    ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
      (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
      ¬ LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro c₁ c₂ hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-15: A named positive predicate for convergence under the paper's
coefficient range, included so the final theorem can be checked directly in
the same negation form as the mathematical question. -/
def PaperRangeGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
    (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
    GlobalWeakWolfeConvergenceAt c₁ c₂

/-- TASK-15: A direct negation of the positive convergence predicate
quantified over the paper's coefficient range. -/
theorem not_PaperRangeGlobalWeakWolfeConvergence :
    ¬ PaperRangeGlobalWeakWolfeConvergence := by
  intro hGlobal
  have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁Upper : (1 / 4 : ℝ) < 2 / 3 := by norm_num
  have hc₂Lower : (2 / 3 : ℝ) ≤ 3 / 4 := by norm_num
  have hc₂Upper : (3 / 4 : ℝ) < 1 := by norm_num
  exact main_not_globalWeakWolfeConvergence_of_parameterRange
    hc₁ hc₁Upper hc₂Lower hc₂Upper (hGlobal _ _ hc₁ hc₁Upper hc₂Lower hc₂Upper)

/-- TASK-15: The level-set formulation also has a direct paper-range
negation predicate. -/
def PaperRangeLevelSetGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
    (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
    LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂

/-- TASK-15: The level-set paper-range convergence predicate is false. -/
theorem not_PaperRangeLevelSetGlobalWeakWolfeConvergence :
    ¬ PaperRangeLevelSetGlobalWeakWolfeConvergence := by
  intro hGlobal
  have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁Upper : (1 / 4 : ℝ) < 2 / 3 := by norm_num
  have hc₂Lower : (2 / 3 : ℝ) ≤ 3 / 4 := by norm_num
  have hc₂Upper : (3 / 4 : ℝ) < 1 := by norm_num
  exact main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    hc₁ hc₁Upper hc₂Lower hc₂Upper
    (hGlobal _ _ hc₁ hc₁Upper hc₂Lower hc₂Upper)

/-- TASK-11: The identity-initialized strong-Wolfe corollary is exposed with
the explicit witness, factorization, and Loewner/gradient bounds required by
the operator-level normalization theorem. -/
theorem identityInitializedStrongWolfe_of_parameterRange
    (n : ℕ) {c₁ c₂ a b q : ℝ}
    (counterexample : StrongWolfeCounterexample
      (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (factor : (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (counterexample.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pushforward 1) :
    Nonempty (WolfeCounterexample.IdentityInitializedStrongWolfeOperatorCertificate
      (Fin n) ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂) := by
  exact WolfeCounterexample.identityInitializedStrongWolfe_of_dimension_ge_two
    n counterexample hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
    L factor lowerMap upperMap hq gradientMapLower

/-- TASK-15: For every pair in the paper's coefficient range and every
dimension `n ≥ 2`, the identity-initialization corollary has a genuine
matrix `InverseIteration` presentation.  The positive ordered Hessian bounds
and the `liminf` conclusion are generated automatically from the initial
positive-definite matrix. -/
theorem existsMatrixIdentityLiminfStrongWolfe_of_parameterRange
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      Nonempty (WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
        n m M c₁ c₂) := by
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange n hn
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact WolfeCounterexample.exists_matrixIdentityLiminfStrongWolfe_of_initialPosDef
    hn counterexample hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/- Legacy fixed-parameter weak-Wolfe aliases below remain available for
compatibility; the released paper-range statements are declared above. -/
/-- TASK-06 helper: the fixed-parameter weak-Wolfe certificate is available in
every finite dimension `n` with `2 ≤ n`. -/
theorem existsWeakWolfeCounterexample_fixedParameters (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WeakWolfeCounterexample (Fin n)) :=
  existsWeakWolfeCounterexample n hn

/-- TASK-06 Main theorem: at the fixed weak-Wolfe coefficients `(1 / 4, 3 / 4)`,
the global convergence predicate is false. -/
theorem main_not_globalWeakWolfeConvergence_fixedParameters :
    ¬ GlobalWeakWolfeConvergenceAt (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ := existsWeakWolfeCounterexample 2 hdimension
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_globalWeakWolfeConvergenceAt_of_counterexample
    counterexample hdimension hlower hupper

/-- TASK-06 corollary: one fixed weak-Wolfe counterexample refutes the universal
global convergence claim over all admissible coefficient pairs. -/
theorem not_universalGlobalWeakWolfeConvergence_fixedParameters :
    ¬ UniversalGlobalWeakWolfeConvergence := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ := existsWeakWolfeCounterexample 2 hdimension
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  have hc₁ : (0 : ℝ) < 1 / 4 := by
    norm_num
  have hc₁₂ : (1 / 4 : ℝ) < 3 / 4 := by
    norm_num
  have hc₂ : (3 / 4 : ℝ) < 1 := by
    norm_num
  exact not_universalGlobalWeakWolfeConvergence_of_counterexample
    counterexample hdimension hlower hupper hc₁ hc₁₂ hc₂

/-- Paper-facing form of thm:planar-convergence: arbitrary initial
positive-definite planar DFP data converge under the full fixed weak-Wolfe
range when the globally strongly convex C2 objective has locally Lipschitz
Hessian near its initial sublevel. Stationary termination is included through
constant continuation of the point sequence. -/
theorem main_planarWeakWolfeConvergence
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧ (∀ z, f z ≤ f xstar → z = xstar) ∧
      Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  obtain ⟨xstar, hresult, _⟩ := PlanarConvergence.rawOrbitConvergenceOfNeighborhood
    orbit hf hμ hHessian hH₀ hWolfe hNeighborhood
  obtain ⟨y, _, hunique⟩ := PlanarConvergence.existsUniqueGlobalMinimizerOfHessian hf hμ hHessian
  refine ⟨xstar, hresult.1, ?_, hresult.2⟩
  intro z hz
  have hminz : ∀ w, f z ≤ f w := fun w ↦ hz.trans (hresult.1 w)
  exact (hunique z hminz).trans (hunique xstar hresult.1).symm

/-- Paper-facing strong-Wolfe consequence of thm:planar-convergence:
strong curvature implies weak curvature after the descent property is
derived from Armijo and strong convexity. -/
theorem main_planarStrongWolfeConvergence
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧ (∀ z, f z ≤ f xstar → z = xstar) ∧
      Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  have hWeak (k : ℕ) : LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k) := by
    apply (hWolfe k).toWeakWolfe
    exact PlanarConvergence.armijoDescentOfHessianLowerBound hf hμ hHessian
      ((hWolfe k).c₁_lt_c₂.trans (hWolfe k).c₂_lt_one) (hWolfe k).armijo
  exact main_planarWeakWolfeConvergence orbit hf hμ hHessian hH₀ hWeak hNeighborhood

end DFP
