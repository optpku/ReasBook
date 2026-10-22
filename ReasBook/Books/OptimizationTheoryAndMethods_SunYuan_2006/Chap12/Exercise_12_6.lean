/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_5_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.EqualityConstrainedProblem
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Remark_12_4_extra_1

noncomputable section

-- Semantic recall:
-- * `Algorithm_12_5_1` already owns the source-facing watchdog API for Algorithm 12.5.1.
-- * Definition 12.5-extra-1 already owns the Chapter 12 watchdog merit/model and sufficient-
--   reduction API under `StandardPenaltyProblem`.
-- * `EqualityConstrainedProblem` already owns the canonical equality-only bridge
--   `EqualityConstrainedProblem.toStandardPenaltyProblem`.
-- * `Remark_12_4_extra_1` already owns the concrete Maratos example data
--   `maratosObjective`, `maratosConstraint`, `maratosPath`, `maratosStep`,
--   `maratosTrialPoint`, `maratosProblem`, and the Maratos exact-penalty increase theorem.
-- * This file therefore keeps only the exercise-specific watchdog specialization and a thin
--   bridge from the watchdog merit owner to the chapter-level Maratos exact-penalty owner
--   through `maratosProblem.toStandardPenaltyProblem`.

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "PenaltyWeights" => EuclideanSpace ℝ (Fin 1)
local notation "Matrix2" => Matrix (Fin 2) (Fin 2) ℝ

open scoped StandardPenaltyProblem

/-- The single watchdog penalty weight for the Maratos equality constraint is the scalar `σ`. -/
def maratosPenaltyWeights (σ : ℝ) : PenaltyWeights :=
  EuclideanSpace.single 0 σ

local notation:max "P_" σ =>
  P_[maratosProblem.toStandardPenaltyProblem] (maratosPenaltyWeights σ)

/-- For the Maratos example, the Chapter 12 watchdog merit function for the equality-only bridge
`maratosProblem.toStandardPenaltyProblem` agrees with the chapter's canonical `L₁` exact-penalty
function with parameter `σ`. -/
theorem maratosWatchdogMeritFunction_eq_l1ExactPenalty
    (σ : ℝ) (x : Point) :
    (P_ σ) x =
      maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ x := by
  rw [StandardPenaltyProblem.watchdogMeritFunction_apply, maratosL1ExactPenalty_eq]
  simp [maratosProblem, maratosPenaltyWeights, EqualityConstrainedProblem.toStandardPenaltyProblem,
    StandardPenaltyProblem.watchdogPenaltyTerm, StandardPenaltyProblem.constraintViolation]

#print axioms maratosPenaltyWeights

local notation:max "SR_[" σ ", " β ", " iterate ", " hessianApprox "]" =>
  StandardPenaltyProblem.IsWatchdogSufficientReduction
    maratosProblem.toStandardPenaltyProblem
    (maratosPenaltyWeights σ)
    β
    iterate
    hessianApprox
    1
    1

/-- `maratosWatchdogRunAt σ β ε method hessianApprox` records the stage-`1` Maratos data for a
Chapter 12 watchdog method and requires its relaxed Step-3 test to be exactly the specialized
watchdog sufficient-reduction condition `SR_[σ, β, method.iterate, hessianApprox]` for the
canonical merit function `P_ σ`. -/
def maratosWatchdogRunAt
    (σ β ε : ℝ)
    (method : WatchdogMethod 2)
    (hessianApprox : ℕ → Matrix2) : Prop :=
  method.penaltyFunction = (P_ σ) ∧
    method.iterate 1 = maratosPath ε ∧
    method.direction 1 = maratosStep ε ∧
    method.stepSize 1 = 1 ∧
    method.trialPointAt 1 = maratosTrialPoint ε ∧
    (method.relaxedCriterion 1 ↔ SR_[σ, β, method.iterate, hessianApprox])

/-- Unfolding `maratosWatchdogRunAt σ β ε method hessianApprox` gives the concrete Maratos
stage-`1` watchdog data together with the specialized Step-3 sufficient-reduction test. -/
theorem maratosWatchdogRunAt_iff
    (σ β ε : ℝ)
    (method : WatchdogMethod 2)
    (hessianApprox : ℕ → Matrix2) :
    maratosWatchdogRunAt σ β ε method hessianApprox ↔
      method.penaltyFunction = (P_ σ) ∧
        method.iterate 1 = maratosPath ε ∧
        method.direction 1 = maratosStep ε ∧
        method.stepSize 1 = 1 ∧
        method.trialPointAt 1 = maratosTrialPoint ε ∧
        (method.relaxedCriterion 1 ↔ SR_[σ, β, method.iterate, hessianApprox]) :=
  Iff.rfl

/-- A Maratos watchdog run records the concrete stage-`1` trial point as `maratosTrialPoint ε`.
-/
theorem maratosWatchdogRunAt_trialPointAt_one_eq
    {σ β ε : ℝ}
    {method : WatchdogMethod 2}
    {hessianApprox : ℕ → Matrix2}
    (hRun : maratosWatchdogRunAt σ β ε method hessianApprox) :
    method.trialPointAt 1 = maratosTrialPoint ε :=
  hRun.2.2.2.2.1

/-- A Maratos watchdog run identifies the Step-3 relaxed test with the specialized watchdog
sufficient-reduction condition at stage `1`. -/
theorem maratosWatchdogRunAt_relaxedCriterion_iff
    (σ β ε : ℝ)
    (method : WatchdogMethod 2)
    (hessianApprox : ℕ → Matrix2)
    (hRun : maratosWatchdogRunAt σ β ε method hessianApprox) :
    method.relaxedCriterion 1 ↔ SR_[σ, β, method.iterate, hessianApprox] :=
  hRun.2.2.2.2.2

/-- Under a Maratos watchdog run, the specialized sufficient-reduction condition implies the
relaxed Step-3 criterion at stage `1`. -/
theorem maratosWatchdogRunAt_relaxedCriterion
    {σ β ε : ℝ}
    {method : WatchdogMethod 2}
    {hessianApprox : ℕ → Matrix2}
    (hRun : maratosWatchdogRunAt σ β ε method hessianApprox)
    (hSufficient : SR_[σ, β, method.iterate, hessianApprox]) :
    method.relaxedCriterion 1 :=
  (maratosWatchdogRunAt_relaxedCriterion_iff σ β ε method hessianApprox hRun).2 hSufficient

/-- Under a Maratos watchdog run, the relaxed Step-3 criterion at stage `1` is equivalent to
the specialized sufficient-reduction condition. -/
theorem maratosWatchdogRunAt_sufficientReduction
    {σ β ε : ℝ}
    {method : WatchdogMethod 2}
    {hessianApprox : ℕ → Matrix2}
    (hRun : maratosWatchdogRunAt σ β ε method hessianApprox)
    (hRelaxed : method.relaxedCriterion 1) :
    SR_[σ, β, method.iterate, hessianApprox] :=
  (maratosWatchdogRunAt_relaxedCriterion_iff σ β ε method hessianApprox hRun).1 hRelaxed

/-- `WatchdogOvercomesMaratosEffectAt σ ε method` packages the three stage-`2` conclusions
used in Exercise 12.6: the watchdog switches to relaxed mode, keeps the Maratos trial point
as the next iterate, and the usual `L₁` exact penalty function still increases there. -/
class WatchdogOvercomesMaratosEffectAt
    (σ ε : ℝ)
    (method : WatchdogMethod 2) : Prop where
  relaxedMode :
    method.lineSearchType 2 = WatchdogLineSearchType.relaxed
  nextIterate_eq :
    method.iterate 2 = maratosTrialPoint ε
  l1Penalty_increases :
    maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosTrialPoint ε) >
      maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosPath ε)

/-- Unfolding `WatchdogOvercomesMaratosEffectAt σ ε method` gives the three source-facing stage-`2`
Maratos conclusions. -/
theorem watchdogOvercomesMaratosEffectAt_iff
    (σ ε : ℝ)
    (method : WatchdogMethod 2) :
    WatchdogOvercomesMaratosEffectAt σ ε method ↔
      method.lineSearchType 2 = WatchdogLineSearchType.relaxed ∧
        method.iterate 2 = maratosTrialPoint ε ∧
          maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosTrialPoint ε) >
            maratosProblem.toStandardPenaltyProblem.l1ExactPenalty σ (maratosPath ε) := by
  constructor
  · intro h
    exact ⟨h.relaxedMode, h.nextIterate_eq, h.l1Penalty_increases⟩
  · rintro ⟨hRelaxed, hNext, hIncrease⟩
    exact ⟨hRelaxed, hNext, hIncrease⟩

/-- If the stage-`1` Maratos data are recorded and the specialized sufficient-reduction test
holds, then the algorithm-level watchdog update yields the stage-`2` Maratos conclusion of
Exercise 12.6. This is the bridge from the canonical Chapter 12 watchdog API to the
source-facing statement. -/
theorem maratosWatchdogRunAt_watchdogOvercomesMaratosEffectAt
    {σ β ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {method : WatchdogMethod 2}
    {hessianApprox : ℕ → Matrix2}
    (hRun : maratosWatchdogRunAt σ β ε method hessianApprox)
    (hSufficient : SR_[σ, β, method.iterate, hessianApprox]) :
    WatchdogOvercomesMaratosEffectAt σ ε method := by
  sorry

/-- The Exercise 12.6 watchdog conclusion is available to typeclass search from the recorded
Maratos stage-`1` data and the specialized sufficient-reduction test. -/
instance instWatchdogOvercomesMaratosEffectAtOfMaratosWatchdogRunAt
    {σ ε : ℝ}
    {method : WatchdogMethod 2}
    [hData : Fact
      (∃ (β : ℝ) (hessianApprox : ℕ → Matrix2),
        0 < σ ∧
          0 < ε ∧
          maratosWatchdogRunAt σ β ε method hessianApprox ∧
          SR_[σ, β, method.iterate, hessianApprox])] :
    WatchdogOvercomesMaratosEffectAt σ ε method := by
  rcases hData.out with ⟨β, hessianApprox, hσ, hε, hRun, hSufficient⟩
  exact maratosWatchdogRunAt_watchdogOvercomesMaratosEffectAt hσ hε hRun hSufficient

/-- Chapter12 Exercise 12.6: for every positive penalty parameter `σ`, every
`β ∈ (0, 1 / 2)`, every fixed Chapter 12 watchdog method `method`, and every fixed stage-`1`
model sequence `hessianApprox`, there is a threshold `δ > 0` such that whenever `0 < ε < δ`,
that watchdog run with Maratos data `x₁ = maratosPath ε`, `d₁ = maratosStep ε`, `α₁ = 1`, and
`x₁ + α₁ d₁ = maratosTrialPoint ε` satisfies the specialized Step-3 sufficient-reduction
condition `SR_[σ, β, method.iterate, hessianApprox]`,
and therefore switches to relaxed mode at stage `2` and keeps `maratosTrialPoint ε` as the next
iterate, even though the usual `L₁` exact penalty function increases there. In this sense the
watchdog technique can overcome the Maratos effect. -/
theorem watchdogTechnique_overcomesMaratosEffect
    {σ β : ℝ} (hσ : 0 < σ) (hβ : β ∈ Set.Ioo (0 : ℝ) ((1 / 2 : ℝ)))
    (method : WatchdogMethod 2)
    (hessianApprox : ℕ → Matrix2) :
    ∃ δ > 0, ∀ {ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
        (hRun : maratosWatchdogRunAt σ β ε method hessianApprox),
        SR_[σ, β, method.iterate, hessianApprox] ∧
          WatchdogOvercomesMaratosEffectAt σ ε method := sorry

end
