/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_5_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1

noncomputable section

open Filter

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling pass:
-- Primary domain: smooth unconstrained optimization with inexact line search on the canonical
-- steepest-descent ray.
-- Sampled owner declarations:
-- * `IsStationaryPoint` in Chapter01 Definition 1.4.7;
-- * `InexactLineSearchMethod` in Chapter02 Algorithm 2.5.3;
-- * `initialSublevelSet` in Chapter02 InitialSublevelSet;
-- * `steepestDescentDirection` and `steepestDescentStep` in Chapter03 Definition 3.1-extra-1;
-- Triage:
-- * source-facing: accumulation-point stationarity for steepest descent with inexact
--   line search;
-- * core/canonical: `InexactLineSearchMethod`, `initialSublevelSet`,
--   `steepestDescentDirection`, `steepestDescentStep`, and the Chapter 1
--   stationary-point owner `IsStationaryPoint`;
-- * bridge/view added here: `InexactLineSearchMethod.IsSteepestDescent`, which records the
--   zero-tolerance steepest-descent specialization of the generic Chapter 2 owner together with
--   the standard infinite-sequence stuttering convention after termination; the stronger local
--   Wolfe-Powell specialization remains available as auxiliary support API.
-- Primitive data for Theorem 3.1.4 are therefore the canonical Chapter 2 run owner together
-- with the Chapter 3 steepest-descent bridge and the Chapter 1 stationary-point owner. The
-- source-explicit `C¹` hypothesis remains on the labeled theorem surface, while the inherited
-- Chapter 2 gradient regularity on `initialSublevelSet f A.x0` is packaged in the local support
-- owner `SteepestDescentGlobalConvergenceSetup`.

namespace InexactLineSearchMethod

/-- A zero-tolerance inexact-line-search run is a steepest-descent method in the sense of
Chapter03 Theorem 3.1.4 when every nonstationary search direction is the canonical
steepest-descent direction and, once a stationary iterate is reached, the infinite-sequence
encoding remains constant afterwards. The generic Chapter 2 Step-3 inexact line-search
acceptance condition remains on the owner `InexactLineSearchMethod f (gradient f)`. -/
def IsSteepestDescent
    (f : E → ℝ) (A : InexactLineSearchMethod f (gradient f)) : Prop :=
  A.ε = 0 ∧
    (∀ k : ℕ, gradient f (A k) ≠ 0 → A.d k = steepestDescentDirection f (A k)) ∧
    ∀ k : ℕ, gradient f (A k) = 0 → ∀ m : ℕ, k ≤ m → A m = A k

namespace IsSteepestDescent

variable {f : E → ℝ} {A : InexactLineSearchMethod f (gradient f)}

/-- A steepest-descent inexact-line-search run uses zero stopping tolerance. -/
theorem epsilon_eq_zero
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A) :
    A.ε = 0 :=
  hMethod.1

/-- On each nonstationary iterate, the search direction is the canonical steepest-descent
direction. -/
theorem direction_eq
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A.d k = steepestDescentDirection f (A k) :=
  hMethod.2.1 k hk

/-- Once a steepest-descent inexact-line-search run reaches a stationary iterate, the
infinite-sequence encoding remains at that iterate for all later indices. -/
theorem stationary_tail
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (k m : ℕ)
    (hk : gradient f (A k) = 0)
    (hkm : k ≤ m) :
    A m = A k :=
  hMethod.2.2 k hk m hkm

/-- In particular, the iterate sequence stutters at the step immediately after any stationary
iterate. -/
theorem stutter_of_stationary
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (k : ℕ)
    (hk : gradient f (A k) = 0) :
    A (k + 1) = A k :=
  hMethod.stationary_tail k (k + 1) hk (Nat.le_succ k)

/-- On a steepest-descent inexact-line-search run, every nonstationary step updates by the
canonical steepest-descent step. -/
theorem update_eq_steepestDescentStep
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A (k + 1) = steepestDescentStep f (A k) (A.α k) := by
  have hContinue : A.ε < ‖gradient f (A k)‖ := by
    simpa [hMethod.epsilon_eq_zero, norm_eq_zero] using hk
  rw [A.update k hContinue, steepestDescentStep, hMethod.direction_eq k hk]

/-- The canonical steepest-descent update has the source-facing form
`x_(k+1) = x_k - α_k • gradient f (x_k)`. -/
theorem update_eq_sub
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A (k + 1) = A k - A.α k • gradient f (A k) := by
  simpa [steepestDescentStep_eq] using hMethod.update_eq_steepestDescentStep k hk

end IsSteepestDescent

/-- A zero-tolerance inexact-line-search method satisfies the steepest-descent/Wolfe-Powell
setup of Theorem 3.1.4 when fixed parameters `ρ, σ` satisfy the chapter Wolfe-Powell
constraints, each nonstationary search direction is the canonical steepest-descent direction,
each accepted step satisfies the Wolfe-Powell rule on the canonical steepest-descent
objective, and once the run reaches a stationary iterate it remains constant afterwards.
This is a Prop-valued bridge from the generic Chapter 2 run owner
`InexactLineSearchMethod f (gradient f)` to the method-specific Chapter 3 setup. -/
def IsSteepestDescentWolfePowell
    (f : E → ℝ) (A : InexactLineSearchMethod f (gradient f)) (ρ σ : ℝ) : Prop :=
  WolfePowellParameters ρ σ ∧
    (∀ k : ℕ, gradient f (A k) ≠ 0 →
      A.d k = steepestDescentDirection f (A k) ∧
        WolfePowellCondition
          (steepestDescentObjective f (A k))
          (deriv (steepestDescentObjective f (A k)))
          ρ σ (A.α k)) ∧
    ∀ k : ℕ, gradient f (A k) = 0 → ∀ m : ℕ, k ≤ m → A m = A k

namespace IsSteepestDescentWolfePowell

variable {f : E → ℝ} {A : InexactLineSearchMethod f (gradient f)} {ρ σ : ℝ}

/-- A steepest-descent/Wolfe-Powell run carries admissible Wolfe-Powell parameters. -/
theorem parameters
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ) :
    WolfePowellParameters ρ σ :=
  hMethod.1

/-- On each nonstationary iterate, the search direction is the canonical steepest-descent
direction. -/
theorem direction_eq
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A.d k = steepestDescentDirection f (A k) :=
  (hMethod.2.1 k hk).1

/-- On each nonstationary iterate, the accepted step satisfies the Wolfe-Powell rule on the
canonical steepest-descent objective. -/
theorem wolfe
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    WolfePowellCondition
      (steepestDescentObjective f (A k))
      (deriv (steepestDescentObjective f (A k)))
      ρ σ (A.α k) :=
  (hMethod.2.1 k hk).2

/-- Once a steepest-descent/Wolfe-Powell run reaches a stationary iterate, the infinite-sequence
encoding remains at that iterate for all later indices. -/
theorem stationary_tail
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (k m : ℕ)
    (hk : gradient f (A k) = 0)
    (hkm : k ≤ m) :
    A m = A k :=
  hMethod.2.2 k hk m hkm

/-- In particular, the iterate sequence stutters at the step immediately after any stationary
iterate. -/
theorem stutter_of_stationary
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (k : ℕ)
    (hk : gradient f (A k) = 0) :
    A (k + 1) = A k :=
  hMethod.stationary_tail k (k + 1) hk (Nat.le_succ k)

/-- Every nonstationary steepest-descent/Wolfe-Powell step has positive steplength. -/
theorem alpha_pos
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ) (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    0 < A.α k :=
  (hMethod.wolfe k hk).step_pos

/-- On a zero-tolerance steepest-descent/Wolfe-Powell run, every nonstationary step updates by
the canonical steepest-descent step. -/
theorem update_eq_steepestDescentStep
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (hε : A.ε = 0)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A (k + 1) = steepestDescentStep f (A k) (A.α k) := by
  have hContinue : A.ε < ‖gradient f (A k)‖ := by
    simpa [hε, norm_eq_zero] using hk
  rw [A.update k hContinue, steepestDescentStep, hMethod.direction_eq k hk]

/-- Any nonstationary zero-tolerance steepest-descent/Wolfe-Powell step yields the positive-step,
canonical-update, Armijo, and curvature data on the canonical steepest-descent ray. -/
theorem stepSpec
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (hε : A.ε = 0)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    0 < A.α k ∧
      A (k + 1) = steepestDescentStep f (A k) (A.α k) ∧
      f (steepestDescentStep f (A k) (A.α k)) ≤
        f (A k) +
          ρ * A.α k *
            inner ℝ (gradient f (A k)) (steepestDescentDirection f (A k)) ∧
      σ *
          inner ℝ (gradient f (A k)) (steepestDescentDirection f (A k)) ≤
        inner ℝ (gradient f (A (k + 1))) (steepestDescentDirection f (A k)) := by
  have hGrad :
      HasGradientAt f (gradient f (A k)) (A k) := by
    exact (hasGradientVectorAt_iff_hasGradientAt).mp <| by
      simpa using A.gradientAt k
  have hUpdate :
      A (k + 1) = steepestDescentStep f (A k) (A.α k) :=
    hMethod.update_eq_steepestDescentStep hε k hk
  have hGradNext :
      HasGradientAt f (gradient f (A (k + 1)))
        (A k + A.α k • steepestDescentDirection f (A k)) := by
    exact (hasGradientVectorAt_iff_hasGradientAt).mp <| by
      simpa [hUpdate, steepestDescentStep] using A.gradientAt (k + 1)
  have hDerivZero :
      deriv (steepestDescentObjective f (A k)) 0 =
        inner ℝ (gradient f (A k)) (steepestDescentDirection f (A k)) := by
    have hGradZero :
        HasGradientAt f (gradient f (A k))
          (A k + (0 : ℝ) • steepestDescentDirection f (A k)) := by
      simpa using hGrad
    simpa [steepestDescentObjective] using
      hGradZero.deriv_lineSearchObjective_apply
  have hDerivStep :
      deriv (steepestDescentObjective f (A k)) (A.α k) =
        inner ℝ (gradient f (A (k + 1))) (steepestDescentDirection f (A k)) := by
    simpa [steepestDescentObjective] using
      hGradNext.deriv_lineSearchObjective_apply
  have hArmijo :
      steepestDescentObjective f (A k) (A.α k) ≤
        steepestDescentObjective f (A k) 0 +
          ρ * A.α k *
            inner ℝ (gradient f (A k)) (steepestDescentDirection f (A k)) := by
    simpa [hDerivZero] using (hMethod.wolfe k hk).sufficientDecrease
  refine ⟨hMethod.alpha_pos k hk, hUpdate, ?_, ?_⟩
  · simpa [steepestDescentObjective, steepestDescentStep,
      lineSearchObjective_apply, lineSearchObjective_zero] using hArmijo
  · simpa [hDerivZero, hDerivStep] using (hMethod.wolfe k hk).curvature

/-- Companion lemma for Theorem 3.1.4: the canonical steepest-descent update on a
zero-tolerance steepest-descent/Wolfe-Powell run has the source-facing form
`x_(k+1) = x_k - α_k • gradient f (x_k)`. -/
theorem update_eq_sub
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (hε : A.ε = 0)
    (k : ℕ)
    (hk : gradient f (A k) ≠ 0) :
    A (k + 1) = A k - A.α k • gradient f (A k) := by
  simpa [steepestDescentStep_eq] using hMethod.update_eq_steepestDescentStep hε k hk

/-- A Wolfe-Powell steepest-descent run is, in particular, a steepest-descent inexact-line-search
run in the generic sense of Theorem 3.1.4. -/
theorem toIsSteepestDescent
    (hMethod : InexactLineSearchMethod.IsSteepestDescentWolfePowell f A ρ σ)
    (hε : A.ε = 0) :
    InexactLineSearchMethod.IsSteepestDescent f A := by
  refine ⟨hε, ?_, ?_⟩
  · intro k hk
    exact hMethod.direction_eq k hk
  · intro k hk m hkm
    exact hMethod.stationary_tail k m hk hkm

end IsSteepestDescentWolfePowell

end InexactLineSearchMethod

/-- Local support owner for Chapter03 Theorem 3.1.4: besides the source-explicit `C¹` and
steepest-descent/stuttering hypotheses, the direct Chapter02 Theorem 2.5.4 dependency also uses
uniform continuity of `gradient f` on the initial sublevel set. This Prop-valued owner packages
exactly that inherited Chapter 2 regularity input without hiding the source-facing method
hypothesis. -/
structure SteepestDescentGlobalConvergenceSetup
    (f : E → ℝ) (A : InexactLineSearchMethod f (gradient f)) : Prop where
  gradientUniformContinuous :
    UniformContinuousOn (gradient f) (initialSublevelSet f A.x0)

namespace SteepestDescentGlobalConvergenceSetup

variable {f : E → ℝ} {A : InexactLineSearchMethod f (gradient f)}

/-- The inherited Chapter 2 global-convergence setup for Theorem 3.1.4 is proof-irrelevant. -/
instance : Subsingleton (SteepestDescentGlobalConvergenceSetup f A) := inferInstance

/-- The packaged Chapter 2 regularity field is exactly the uniform-continuity hypothesis used by
Chapter02 Theorem 2.5.4. -/
theorem gradient_uniformContinuousOn
    (hSetup : SteepestDescentGlobalConvergenceSetup f A) :
    UniformContinuousOn (gradient f) (initialSublevelSet f A.x0) :=
  hSetup.gradientUniformContinuous

end SteepestDescentGlobalConvergenceSetup

/-- Helper for Chapter03 Theorem 3.1.4: on a nonstationary iterate of a steepest-descent
inexact-line-search run, the Chapter 2 angle condition holds with the fixed gap `π / 4`. -/
lemma isSteepestDescent_angle_bound_piQuarter
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A) :
    ∀ k : ℕ, gradient f (A k) ≠ 0 →
      InnerProductGeometry.angle (A.d k) (-(gradient f (A k))) ≤
        Real.pi / 2 - Real.pi / 4 := by
  intro k hk
  -- Replace the recorded direction by the canonical steepest-descent direction.
  rw [hMethod.direction_eq k hk]
  have hNegGradNe : -(gradient f (A k)) ≠ 0 := by
    simpa using neg_ne_zero.mpr hk
  have hAngleZero :
      InnerProductGeometry.angle
          (steepestDescentDirection f (A k))
          (-(gradient f (A k))) = 0 := by
    simpa [steepestDescentDirection] using InnerProductGeometry.angle_self hNegGradNe
  -- The exact angle `0` is certainly below the fixed right-angle margin `π / 4`.
  rw [hAngleZero]
  nlinarith [Real.pi_pos]

/-- Helper for Chapter03 Theorem 3.1.4: if a steepest-descent inexact-line-search run reaches a
zero-gradient iterate, then every accumulation point of the whole run is that iterate and hence
is stationary. -/
lemma steepestDescent_stationary_of_zero_iterate_gradient
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (hC1 : ContDiff ℝ 1 f)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar))
    {k0 : ℕ}
    (hk0 : gradient f (A k0) = 0) :
    IsStationaryPoint f xStar := by
  rw [isStationaryPoint_iff]
  refine ⟨?_, ?_⟩
  · -- The stuttering-tail hypothesis makes the convergent subsequence eventually constant.
    have hSubseqConst :
        Tendsto (A ∘ φ) atTop (nhds (A k0)) := by
      have hEventuallyEq :
          (fun _ : ℕ ↦ A k0) =ᶠ[atTop] A ∘ φ := by
        filter_upwards [Filter.eventually_ge_atTop k0] with i hi
        symm
        exact hMethod.stationary_tail k0 (φ i) hk0 (le_trans hi (hφ.id_le i))
      exact Tendsto.congr' hEventuallyEq tendsto_const_nhds
    have hxStar_eq : xStar = A k0 :=
      tendsto_nhds_unique hTendsto hSubseqConst
    simpa [hxStar_eq] using hk0
  · -- `C¹` regularity gives differentiability at the limit point.
    exact hC1.contDiffAt.differentiableAt_one

/-- Helper for Chapter03 Theorem 3.1.4: if the full gradient sequence tends to `0`, then every
accumulation point of the iterate sequence has zero gradient. -/
lemma gradient_eq_zero_of_accumulationPoint_of_gradientTendstoZero
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hC1 : ContDiff ℝ 1 f)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar))
    (hGradTendsto : Tendsto (fun k ↦ gradient f (A k)) atTop (nhds 0)) :
    gradient f xStar = 0 := by
  -- Continuity of `gradient` follows from the continuous Fréchet derivative and the Riesz map.
  have hGradAux :
      Continuous (fun y : E ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hC1.continuous_fderiv one_ne_zero)
  have hGrad : Continuous (gradient f) := by
    change Continuous (fun y : E ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y))
    exact hGradAux
  have hGradSubseq :
      Tendsto (fun k ↦ gradient f (A (φ k))) atTop (nhds 0) :=
    hGradTendsto.comp hφ.tendsto_atTop
  have hGradAtLimit :
      Tendsto (fun k ↦ gradient f (A (φ k))) atTop (nhds (gradient f xStar)) := by
    -- Sending the convergent subsequence through the continuous gradient fixes the limit value.
    exact hGrad.continuousAt.tendsto.comp hTendsto
  exact tendsto_nhds_unique hGradAtLimit hGradSubseq

/-- Local support form of Chapter03 Theorem 3.1.4: under the inherited Chapter 2 global
convergence setup on the initial sublevel set, every accumulation point of a steepest-descent
inexact-line-search run is a stationary point. This theorem keeps the inherited uniform
continuity hypothesis off the main labeled source-facing statement. -/
theorem steepestDescent_accumulationPoint_stationary_of_globalConvergenceSetup
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hSetup : SteepestDescentGlobalConvergenceSetup f A)
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    (hC1 : ContDiff ℝ 1 f)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := by
  -- Package the Chapter 2 gradient witness using the `C¹` hypothesis on `f`.
  have hHasGradient :
      ∀ y ∈ initialSublevelSet f A.x0, HasGradientVectorAt f (gradient f y) y := by
    intro y hy
    exact (hasGradientVectorAt_iff_hasGradientAt).2 <|
      hC1.contDiffAt.differentiableAt_one.hasGradientAt
  have hMu : 0 < Real.pi / 4 := by
    positivity
  rcases
      inexactLineSearch_globalConvergence
        A
        (Real.pi / 4)
        hMethod.epsilon_eq_zero
        hHasGradient
        hSetup.gradient_uniformContinuousOn
        hMu
        (isSteepestDescent_angle_bound_piQuarter f A hMethod) with
    hZero | hObjOrGrad
  · rcases hZero with ⟨k0, hk0⟩
    -- A zero-gradient iterate forces a constant tail, so the subsequential limit is stationary.
    exact
      steepestDescent_stationary_of_zero_iterate_gradient
        f A hMethod hC1 hφ hTendsto hk0
  · rcases hObjOrGrad with hObjAtBot | hGradTendsto
    · -- The objective cannot converge both to `-∞` and to the finite value `f xStar`.
      have hObjSubseqAtBot : Tendsto (fun k ↦ f (A (φ k))) atTop atBot :=
        hObjAtBot.comp hφ.tendsto_atTop
      have hObjSubseqNhds :
          Tendsto (fun k ↦ f (A (φ k))) atTop (nhds (f xStar)) := by
        exact hC1.continuous.continuousAt.tendsto.comp hTendsto
      exact False.elim <|
        (not_tendsto_nhds_of_tendsto_atBot hObjSubseqAtBot (f xStar)) hObjSubseqNhds
    · -- In the remaining branch, continuity of `gradient` transfers the zero limit to `xStar`.
      rw [isStationaryPoint_iff]
      refine ⟨?_, ?_⟩
      · exact
          gradient_eq_zero_of_accumulationPoint_of_gradientTendstoZero
            f A hC1 hφ hTendsto hGradTendsto
      · exact hC1.contDiffAt.differentiableAt_one

/-- Chapter03 Theorem 3.1.4 (Convergence theorem of the steepest descent method with inexact
line search): if `f : E → ℝ` is `C¹`, `A : InexactLineSearchMethod f (gradient f)` is a
steepest-descent run with inexact line search in the Chapter 2 sense, and a subsequence of the
iterate sequence converges to `xStar`, then `xStar` is a stationary point of `f`, formalized by
the Chapter 1 owner `IsStationaryPoint f xStar`. The zero-tolerance stopping rule and the
standard stuttering-tail convention after termination are part of the bridge hypothesis
`hMethod : InexactLineSearchMethod.IsSteepestDescent f A`, while the inherited Chapter 2
built-in initial-sublevel-set gradient regularity hypothesis is packaged in
`hSetup : SteepestDescentGlobalConvergenceSetup f A`. -/
theorem steepestDescent_accumulationPoint_stationary
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hC1 : ContDiff ℝ 1 f)
    (hSetup : SteepestDescentGlobalConvergenceSetup f A)
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := by
  -- The labeled theorem is the source-facing wrapper around the local Chapter 2 setup theorem.
  exact
    steepestDescent_accumulationPoint_stationary_of_globalConvergenceSetup
      f A hSetup hMethod hC1 hφ hTendsto

/-- Companion form of Theorem 3.1.4: the stationary accumulation-point conclusion can
be read as the vanishing Fréchet derivative `HasFDerivAt f 0 xStar`. -/
theorem steepestDescent_accumulationPoint_hasFDerivAt_zero
    (f : E → ℝ)
    (A : InexactLineSearchMethod f (gradient f))
    (hC1 : ContDiff ℝ 1 f)
    (hSetup : SteepestDescentGlobalConvergenceSetup f A)
    (hMethod : InexactLineSearchMethod.IsSteepestDescent f A)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar)) :
    HasFDerivAt f (0 : E →L[ℝ] ℝ) xStar := by
  -- Read the stationary-point conclusion in the equivalent Fréchet-derivative form.
  exact
    (steepestDescent_accumulationPoint_stationary
      f A hC1 hSetup hMethod hφ hTendsto).hasFDerivAt

end
