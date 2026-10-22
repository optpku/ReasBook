/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1

-- Semantic recall: Chapter 2 already owns source-facing exact line search on the nonnegative
-- ray as `IsExactLineSearchStepOnNonnegativeRay`, and `Algorithm_4_2_extra_1` already owns the
-- Euclidean-space ambient point type `ConjugateGradientPoint` together with the canonical
-- Fletcher-Reeves coefficient `fletcherReevesCoefficient`. This file keeps only the
-- restart-specific run/state/branch formalization explicit.

/-- The Fletcher-Reeves candidate direction before the restart test. -/
noncomputable def restartFRCandidateDirection {n : ℕ}
    (gPrev gNext dPrev : ConjugateGradientPoint n) :
    ConjugateGradientPoint n :=
  -gNext + fletcherReevesCoefficient gPrev gNext • dPrev

/-- A single state of the restart Fletcher-Reeves method records the local
iteration counter together with the current point, gradient, and search
direction. -/
structure RestartFRConjugateGradientState (n : ℕ) where
  iteration : ℕ
  x : ConjugateGradientPoint n
  g : ConjugateGradientPoint n
  d : ConjugateGradientPoint n

/-- A restart branch resets the local counter and chooses the steepest-descent
direction at the next state. -/
structure RestartFRRestartStep {n : ℕ}
    (sNext : RestartFRConjugateGradientState n) : Prop where
  iteration_eq_zero : sNext.iteration = 0
  direction_eq : sNext.d = -sNext.g

/-- A continuation branch increments the local counter and keeps the
Fletcher-Reeves candidate direction. -/
structure RestartFRContinueStep {n : ℕ}
    (s t : RestartFRConjugateGradientState n) : Prop where
  iteration_eq_succ : t.iteration = s.iteration + 1
  direction_eq :
    t.d = restartFRCandidateDirection s.g t.g s.d

namespace RestartFRRestartStep

/-- Unfolding formula for a restart branch. -/
theorem iff {n : ℕ} (sNext : RestartFRConjugateGradientState n) :
    RestartFRRestartStep sNext ↔ sNext.iteration = 0 ∧ sNext.d = -sNext.g := by
  constructor
  · intro h
    exact ⟨h.iteration_eq_zero, h.direction_eq⟩
  · rintro ⟨hIteration, hDirection⟩
    exact ⟨hIteration, hDirection⟩

end RestartFRRestartStep

namespace RestartFRContinueStep

/-- Unfolding formula for a continuation branch. -/
theorem iff {n : ℕ} (s t : RestartFRConjugateGradientState n) :
    RestartFRContinueStep s t ↔
      t.iteration = s.iteration + 1 ∧
        t.d = restartFRCandidateDirection s.g t.g s.d := by
  constructor
  · intro h
    exact ⟨h.iteration_eq_succ, h.direction_eq⟩
  · rintro ⟨hIteration, hDirection⟩
    exact ⟨hIteration, hDirection⟩

end RestartFRContinueStep

/-- A restart Fletcher-Reeves conjugate-gradient method on `ℝ^n` with restart
period `r`. The local state data and branch conditions are the same as in
Algorithm 4.2.2; only the restart threshold is abstracted from the source
specialization `r = n` to a reusable period parameter. -/
structure PeriodicRestartFRConjugateGradientMethod (n r : ℕ)
    (f : ConjugateGradientPoint n → ℝ) where
  ε : ℝ
  x0 : ConjugateGradientPoint n
  α : ℕ → ℝ
  state : ℕ → RestartFRConjugateGradientState n
  epsPos : 0 < ε
  initialPoint : (state 0).x = x0
  initialIndex : (state 0).iteration = 0
  initialGradient : HasGradientAt f (state 0).g x0
  initialDirection :
    ε < ‖(state 0).g‖ → (state 0).d = -(state 0).g
  exactLineSearch :
    ∀ t : ℕ, ε < ‖(state t).g‖ →
      IsExactLineSearchStepOnNonnegativeRay f (state t).x (state t).d (α t)
  nextPoint :
    ∀ t : ℕ, ε < ‖(state t).g‖ →
      (state (t + 1)).x = (state t).x + α t • (state t).d
  nextGradient :
    ∀ t : ℕ, ε < ‖(state t).g‖ →
      HasGradientAt f (state (t + 1)).g ((state (t + 1)).x)
  terminalStep :
    ∀ t : ℕ, ε < ‖(state t).g‖ → ‖(state (t + 1)).g‖ ≤ ε →
      (state (t + 1)).iteration = (state t).iteration + 1
  restartAtPeriod :
    ∀ t : ℕ, ε < ‖(state t).g‖ → ε < ‖(state (t + 1)).g‖ →
      (state t).iteration + 1 = r →
      RestartFRRestartStep (state (t + 1))
  restartAtAscent :
    ∀ t : ℕ, ε < ‖(state t).g‖ → ε < ‖(state (t + 1)).g‖ →
      (state t).iteration + 1 ≠ r →
      0 < dotProduct
        (restartFRCandidateDirection (state t).g (state (t + 1)).g (state t).d)
        ((state (t + 1)).g) →
      RestartFRRestartStep (state (t + 1))
  continueStep :
    ∀ t : ℕ, ε < ‖(state t).g‖ → ε < ‖(state (t + 1)).g‖ →
      (state t).iteration + 1 ≠ r →
      dotProduct
        (restartFRCandidateDirection (state t).g (state (t + 1)).g (state t).d)
        ((state (t + 1)).g) ≤ 0 →
      RestartFRContinueStep (state t) (state (t + 1))

/-- Chapter04 Algorithm 4.2.2 is the `r = n` specialization of the reusable
restart-period owner `PeriodicRestartFRConjugateGradientMethod`. -/
abbrev RestartFRConjugateGradientMethod (n : ℕ)
    (f : ConjugateGradientPoint n → ℝ) :=
  PeriodicRestartFRConjugateGradientMethod n n f

/-- A restart Fletcher-Reeves method can be used as its sequence of local
states. -/
instance {n r : ℕ} {f : ConjugateGradientPoint n → ℝ} :
    CoeFun (PeriodicRestartFRConjugateGradientMethod n r f)
      (fun _ ↦ ℕ → RestartFRConjugateGradientState n) where
  coe A := A.state

/-- Evaluating a restart Fletcher-Reeves method as a function returns its state sequence. -/
theorem PeriodicRestartFRConjugateGradientMethod.coe_apply {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) (t : ℕ) :
    A t = A.state t :=
  rfl

/-- The iterate sequence carried by a periodic restart Fletcher-Reeves method. -/
abbrev PeriodicRestartFRConjugateGradientMethod.x {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) :
    ℕ → ConjugateGradientPoint n :=
  fun t ↦ (A t).x

/-- Evaluating the iterate sequence projection returns the iterate component of the state. -/
theorem PeriodicRestartFRConjugateGradientMethod.x_apply {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) (t : ℕ) :
    A.x t = (A t).x :=
  rfl

/-- The stopping condition at stage `t` is `‖g_t‖ ≤ ε`. -/
def PeriodicRestartFRConjugateGradientMethod.terminatedAt {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) (t : ℕ) : Prop :=
  ‖(A t).g‖ ≤ A.ε

/-- `terminatedAt` unfolds to the gradient-norm stopping test from Algorithm 4.2.2. -/
theorem PeriodicRestartFRConjugateGradientMethod.terminatedAt_iff {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) (t : ℕ) :
    A.terminatedAt t ↔ ‖(A t).g‖ ≤ A.ε :=
  Iff.rfl

/-- At every nonterminal stage, the recorded exact line-search step is nonnegative. -/
theorem PeriodicRestartFRConjugateGradientMethod.stepSize_nonneg {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) {t : ℕ}
    (hNotStopped : A.ε < ‖(A t).g‖) :
    0 ≤ A.α t :=
  (A.exactLineSearch t hNotStopped).nonneg

/-- A nonterminal stage performs exact line search, updates the point and
gradient, and then either stops, restarts, or accepts the Fletcher-Reeves
candidate direction. -/
theorem PeriodicRestartFRConjugateGradientMethod.nonterminalStepSpec {n r : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : PeriodicRestartFRConjugateGradientMethod n r f) {t : ℕ}
    (hNotStopped : A.ε < ‖(A t).g‖) :
    IsExactLineSearchStepOnNonnegativeRay f (A t).x (A t).d (A.α t) ∧
      (A (t + 1)).x = (A t).x + A.α t • (A t).d ∧
      HasGradientAt f (A (t + 1)).g (A (t + 1)).x ∧
      ((A.terminatedAt (t + 1) ∧
          (A (t + 1)).iteration = (A t).iteration + 1) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 = r ∧
          RestartFRRestartStep (A (t + 1))) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 ≠ r ∧
          0 < dotProduct
            (restartFRCandidateDirection
              (A t).g (A (t + 1)).g (A t).d)
            (A (t + 1)).g ∧
          RestartFRRestartStep (A (t + 1))) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 ≠ r ∧
          dotProduct
            (restartFRCandidateDirection
              (A t).g (A (t + 1)).g (A t).d)
            (A (t + 1)).g ≤ 0 ∧
          RestartFRContinueStep (A t) (A (t + 1)))) := sorry

/-- Evaluating a Chapter 4.2.2 restart Fletcher-Reeves method as a function
returns its state sequence. -/
theorem RestartFRConjugateGradientMethod.coe_apply {n : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : RestartFRConjugateGradientMethod n f) (t : ℕ) :
    A t = A.state t :=
  PeriodicRestartFRConjugateGradientMethod.coe_apply A t

/-- The stopping condition at stage `t` is `‖g_t‖ ≤ ε`. -/
def RestartFRConjugateGradientMethod.terminatedAt {n : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : RestartFRConjugateGradientMethod n f) (t : ℕ) : Prop :=
  PeriodicRestartFRConjugateGradientMethod.terminatedAt A t

/-- `terminatedAt` unfolds to the gradient-norm stopping test from Algorithm 4.2.2. -/
theorem RestartFRConjugateGradientMethod.terminatedAt_iff {n : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : RestartFRConjugateGradientMethod n f) (t : ℕ) :
    A.terminatedAt t ↔ ‖(A t).g‖ ≤ A.ε :=
  Iff.rfl

/-- At every nonterminal stage, the recorded exact line-search step is nonnegative. -/
theorem RestartFRConjugateGradientMethod.stepSize_nonneg {n : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : RestartFRConjugateGradientMethod n f) {t : ℕ}
    (hNotStopped : A.ε < ‖(A t).g‖) :
    0 ≤ A.α t :=
  PeriodicRestartFRConjugateGradientMethod.stepSize_nonneg A hNotStopped

/-- A nonterminal stage performs exact line search, updates the point and
gradient, and then either stops, restarts, or accepts the Fletcher-Reeves
candidate direction. -/
theorem RestartFRConjugateGradientMethod.nonterminalStepSpec {n : ℕ}
    {f : ConjugateGradientPoint n → ℝ}
    (A : RestartFRConjugateGradientMethod n f) {t : ℕ}
    (hNotStopped : A.ε < ‖(A t).g‖) :
    IsExactLineSearchStepOnNonnegativeRay f (A t).x (A t).d (A.α t) ∧
      (A (t + 1)).x = (A t).x + A.α t • (A t).d ∧
      HasGradientAt f (A (t + 1)).g (A (t + 1)).x ∧
      ((A.terminatedAt (t + 1) ∧
          (A (t + 1)).iteration = (A t).iteration + 1) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 = n ∧
          RestartFRRestartStep (A (t + 1))) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 ≠ n ∧
          0 < dotProduct
            (restartFRCandidateDirection
              (A t).g (A (t + 1)).g (A t).d)
            (A (t + 1)).g ∧
          RestartFRRestartStep (A (t + 1))) ∨
        (A.ε < ‖(A (t + 1)).g‖ ∧
          (A t).iteration + 1 ≠ n ∧
          dotProduct
            (restartFRCandidateDirection
              (A t).g (A (t + 1)).g (A t).d)
            (A (t + 1)).g ≤ 0 ∧
          RestartFRContinueStep (A t) (A (t + 1)))) :=
  PeriodicRestartFRConjugateGradientMethod.nonterminalStepSpec A hNotStopped
