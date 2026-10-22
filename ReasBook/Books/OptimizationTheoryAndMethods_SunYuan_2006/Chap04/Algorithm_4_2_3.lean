/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1

-- Semantic recall: Chapter 4 already owns the ambient Euclidean-space point type
-- `ConjugateGradientPoint` and the common nonlinear conjugate-gradient run data as
-- `ConjugateGradientRun`. This file keeps only Beale-specific restart and coefficient data on
-- top of that owner, while Chapter 2 still owns source-facing exact line search on the
-- nonnegative ray as `IsExactLineSearchStepOnNonnegativeRay`.

/-- The Powell-Beale inequality and restart-window condition from Step 5. -/
def BealeThreeTermRestartTrigger {n : ℕ}
    (g : ℕ → ConjugateGradientPoint n) (t : ℕ → ℕ) (k : ℕ) : Prop :=
  0.2 * ‖g k‖ ^ 2 ≤ |dotProduct (g (k - 1)) (g k)| ∧
    n - 1 ≤ k - t (k - 1)

/-- The Step 5 Powell-Beale restart test at iterate `k`. -/
def BealeThreeTermRestartCriterion {n : ℕ}
    (g : ℕ → ConjugateGradientPoint n) (t : ℕ → ℕ) (k : ℕ) : Prop :=
  0 < k ∧ BealeThreeTermRestartTrigger g t k

/-- The Step 9 descent test for an accepted search direction at iterate `k`. -/
def BealeThreeTermAcceptedDirectionTest {n : ℕ}
    (g d : ℕ → ConjugateGradientPoint n) (k : ℕ) : Prop :=
  (-1.2) * ‖g k‖ ^ 2 ≤ dotProduct (d k) (g k) ∧
    dotProduct (d k) (g k) ≤ (-0.8) * ‖g k‖ ^ 2

/-- The Beale coefficient `β_k` from formula `(4.2.38)`. -/
noncomputable def bealeThreeTermBeta {n : ℕ}
    (gPrev gNext dPrev : ConjugateGradientPoint n) : ℝ :=
  dotProduct gNext (gNext - gPrev) /
    dotProduct dPrev (gNext - gPrev)

/-- The denominator in Beale's formula `(4.2.38)` is nonzero at iterate `k`. -/
def BealeThreeTermBetaDenominatorNonzero {n : ℕ}
    (g d : ℕ → ConjugateGradientPoint n) (k : ℕ) : Prop :=
  dotProduct (d (k - 1)) (g k - g (k - 1)) ≠ 0

/-- The Beale coefficient `γ_k` from formula `(4.2.39)`, which vanishes immediately after a
restart. -/
noncomputable def bealeThreeTermGamma {n : ℕ}
    (g d : ℕ → ConjugateGradientPoint n) (t k : ℕ) : ℝ :=
  if k = t + 1 then 0
  else
    dotProduct (g k) (g (t + 1) - g t) /
      dotProduct (d t) (g (t + 1) - g t)

/-- The denominator in the nontrivial branch of Beale's formula `(4.2.39)` is nonzero at
restart index `t`. -/
def BealeThreeTermGammaDenominatorNonzero {n : ℕ}
    (g d : ℕ → ConjugateGradientPoint n) (t : ℕ) : Prop :=
  dotProduct (d t) (g (t + 1) - g t) ≠ 0

/-- Chapter04 Algorithm 4.2.3: Beale's three-term conjugate-gradient method on `ℝ^n` extends the
generic nonlinear conjugate-gradient run data in `ConjugateGradientRun` by adding the stopping
tolerance `ε`, the Beale coefficients `β` and `γ`, the tentative Step 7 directions, and the
restart bookkeeping from Steps 5, 8, and 9. The inherited fields provide the common initial
point, iterates, explicit gradients, search directions, step sizes, and gradient-at-iterate
specification. The Beale-specific fields record that the initialization satisfies `d 0 = -g 0`
whenever the initial gradient is nonterminal, every nonterminal step uses exact line search and
the iterate update, the Step 5 restart test chooses `restartIndexBeforeFallback`, Step 7 forms
`directionBeforeFallback` using `(4.2.37)`, Step 8 preserves a recent restart, Step 9 either
accepts that tentative direction or falls back to `d k = -g k + β k • d (k - 1)`, and the
textbook formulas `(4.2.38)` and `(4.2.39)` hold whenever their denominators are required. -/
structure BealeThreeTermConjugateGradientMethod (n : ℕ)
    (f : ConjugateGradientPoint n → ℝ)
    extends ConjugateGradientRun n f where
  ε : ℝ
  β : ℕ → ℝ
  γ : ℕ → ℝ
  directionBeforeFallback : ℕ → ConjugateGradientPoint n
  restartIndexBeforeFallback : ℕ → ℕ
  t : ℕ → ℕ
  eps_pos : 0 < ε
  restartIndexBeforeFallback_zero : restartIndexBeforeFallback 0 = 0
  t_zero : t 0 = 0
  initialDirection (hactive : ε < ‖g 0‖) : d 0 = -g 0
  exactLineSearch (k : ℕ) (hactive : ε < ‖g k‖) :
    IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  update (k : ℕ) (hactive : ε < ‖g k‖) : x (k + 1) = x k + α k • d k
  restartIndexBeforeFallback_of_restartCriterion
      (k : ℕ) (hactive : ε < ‖g k‖)
      (hrestart : BealeThreeTermRestartCriterion g t k) :
      restartIndexBeforeFallback k = k - 1
  restartIndexBeforeFallback_of_not_restartCriterion
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hnotRestart : ¬ BealeThreeTermRestartCriterion g t k) :
      restartIndexBeforeFallback k = t (k - 1)
  directionBeforeFallbackFormula
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖) :
      directionBeforeFallback k = -g k + β k • d (k - 1) +
        γ k • d (restartIndexBeforeFallback k)
  finalRestartIndex_of_recentRestart
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hrecent : k ≤ restartIndexBeforeFallback k + 1) :
      t k = restartIndexBeforeFallback k
  finalRestartIndex_of_acceptedDirection
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k)
      (haccepted : BealeThreeTermAcceptedDirectionTest g directionBeforeFallback k) :
      t k = restartIndexBeforeFallback k
  finalRestartIndex_of_stepNineFallback
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k)
      (hreject : ¬ BealeThreeTermAcceptedDirectionTest g directionBeforeFallback k) :
      t k = k - 1
  finalDirection_of_recentRestart
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hrecent : k ≤ restartIndexBeforeFallback k + 1) :
      d k = directionBeforeFallback k
  finalDirection_of_acceptedDirection
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k)
      (haccepted : BealeThreeTermAcceptedDirectionTest g directionBeforeFallback k) :
      d k = directionBeforeFallback k
  finalDirection_of_stepNineFallback
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k)
      (hreject : ¬ BealeThreeTermAcceptedDirectionTest g directionBeforeFallback k) :
      d k = -g k + β k • d (k - 1)
  betaDenominatorNonzero
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖) :
      BealeThreeTermBetaDenominatorNonzero g d k
  betaFormula
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖) :
      β k = bealeThreeTermBeta (g (k - 1)) (g k) (d (k - 1))
  gammaFormula_of_recentRestart
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hrecent : k = restartIndexBeforeFallback k + 1) :
      γ k = 0
  gammaDenominatorNonzero
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k) :
      BealeThreeTermGammaDenominatorNonzero g d (restartIndexBeforeFallback k)
  gammaFormula
      (k : ℕ) (hk : 0 < k) (hactive : ε < ‖g k‖)
      (hstrict : restartIndexBeforeFallback k + 1 < k) :
      γ k = bealeThreeTermGamma g d (restartIndexBeforeFallback k) k

namespace BealeThreeTermConjugateGradientMethod

variable {n : ℕ} {f : ConjugateGradientPoint n → ℝ}

/-- A Beale three-term conjugate gradient method can be used as its iterate sequence. -/
instance : CoeFun (BealeThreeTermConjugateGradientMethod n f)
    (fun _ ↦ ℕ → ConjugateGradientPoint n) where
  coe A := A.x

/-- The stopping condition for a Beale three-term conjugate-gradient iterate is `‖g k‖ ≤ ε`. -/
def terminatedAt (A : BealeThreeTermConjugateGradientMethod n f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

end BealeThreeTermConjugateGradientMethod
