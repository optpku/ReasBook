/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Algorithm_11_3_1

noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius

section Chapter11Theorem1132

variable {basicDim nonbasicDim : ℕ}

/-- Under the modified Step 7 rule `(11.3.5)`, a Step 5 residual-acceptable trial point is
accepted exactly when it satisfies the source sufficient-decrease inequality. -/
def generalizedReducedGradientSufficientDecreaseAccepts
    (objective :
      (EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim)) → ℝ)
    (iterate : ℕ → (EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim)))
    (trialBasic : ℕ → ℕ → ℕ → EuclideanSpace ℝ (Fin basicDim))
    (trialNonbasic : ℕ → ℕ → EuclideanSpace ℝ (Fin nonbasicDim))
    (reducedGradient : ℕ → EuclideanSpace ℝ (Fin nonbasicDim))
    (initialStepSize : ℕ → ℝ)
    (β : ℝ)
    (k l j : ℕ) : Prop :=
  objective (generalizedReducedGradientTrialPoint trialBasic trialNonbasic k l j) ≤
    objective (iterate k) -
      (generalizedReducedGradientTrialStepSize (initialStepSize k) l * β *
        ‖reducedGradient k‖ ^ (2 : ℕ)) / 2

/-- The modified Step 6/Step 7 search at stage `k` and backtracking count `l` returns the first
residual-acceptable correction count only when that first residual-acceptable correction
satisfies the sufficient-decrease test `(11.3.5)`. -/
def generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
    (objective :
      (EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim)) → ℝ)
    (constraint :
      (EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim)) →
        EuclideanSpace ℝ (Fin basicDim))
    (basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : ℕ → EuclideanSpace ℝ (Fin nonbasicDim))
    (initialStepSize : ℕ → ℝ)
    (β εBar : ℝ) (maxCorrections : ℕ)
    (iterate : ℕ → (EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim)))
    (k l : ℕ) : Option ℕ := by
  classical
  exact
    match generalizedReducedGradientStageFirstResidualAcceptedCorrection
        constraint
        εBar
        basicJacobian
        reducedGradient
        initialStepSize
        maxCorrections
        iterate
        k
        l with
    | some j =>
        if generalizedReducedGradientSufficientDecreaseAccepts
            objective
            iterate
            (generalizedReducedGradientStageTrialBasic
              constraint
              basicJacobian
              reducedGradient
              initialStepSize
              iterate)
            (generalizedReducedGradientStageTrialNonbasic
              iterate
              reducedGradient
              initialStepSize)
            reducedGradient
            initialStepSize
            β
            k
            l
            j then
          some j
        else
          none
    | none => none

/-- A generalized reduced-gradient run equipped with the Step 6 backtracking and Step 7
sufficient-decrease search data used in Theorem 11.3.2. This owner replaces the original
strict-decrease Step 7 test of Algorithm 11.3.1 by the modified search rule `(11.3.5)`,
while retaining the Step 3 positivity of the initial steplengths `α_k⁽⁰⁾` on continuing
stages and the source equality-feasibility invariant `c(xₖ) = 0` along active iterates. -/
structure GeneralizedReducedGradientSufficientDecreaseMethod
    (β : ℝ) extends @_root_.GeneralizedReducedGradientRun basicDim nonbasicDim where
  εBar : ℝ
  maxCorrections : ℕ
  acceptedBacktrack : ℕ → ℕ
  acceptedCorrection : ℕ → ℕ
  epsilonBar_pos : 0 < εBar
  maxCorrections_pos : 0 < maxCorrections
  initialStepSize_pos :
    ∀ k, 1 ≤ k → active (k + 1) → 0 < initialStepSize k
  constraint_iterate_eq_zero_of_active :
    ∀ k, 1 ≤ k → active k → constraint (iterate k) = 0
  earlierBacktrackingRejected :
    ∀ k, 1 ≤ k → active (k + 1) →
      ∀ l, l < acceptedBacktrack k →
        generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
            objective
            constraint
            basicJacobian
            reducedGradient
            initialStepSize
            β
            εBar
            maxCorrections
            iterate
            k
            l =
          none
  acceptedCorrectionAt_eq_some :
    ∀ k, 1 ≤ k → active (k + 1) →
      generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
          objective
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          β
          εBar
          maxCorrections
          iterate
          k
          (acceptedBacktrack k) =
        some (acceptedCorrection k)
  iterate_succ_eq_acceptedTrialPoint :
    ∀ k, 1 ≤ k → active (k + 1) →
      iterate (k + 1) =
        generalizedReducedGradientStageTrialPoint
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          iterate
          k
          (acceptedBacktrack k)
          (acceptedCorrection k)

variable {β : ℝ}

/-- Forget the Step 6 backtracking counters and retain only the underlying generalized
reduced-gradient run. -/
abbrev GeneralizedReducedGradientSufficientDecreaseMethod.toRun
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β) :
    @_root_.GeneralizedReducedGradientRun basicDim nonbasicDim :=
  method.toGeneralizedReducedGradientRun

/-- The accepted Step 6 steplength at a continuing stage is the initial steplength `α_k⁽⁰⁾`
after the recorded number of halvings. -/
def GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialStepSize
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k : ℕ) : ℝ :=
  generalizedReducedGradientTrialStepSize
    (method.initialStepSize k)
    (method.acceptedBacktrack k)

/-- The accepted Step 4/Step 5 trial point at a continuing stage is the point determined by the
accepted Step 6 backtracking count and the accepted correction count returned by the modified
Step 7 sufficient-decrease search. -/
def GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialPoint
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k : ℕ) : EuclideanSpace ℝ (Fin basicDim) × EuclideanSpace ℝ (Fin nonbasicDim) :=
  generalizedReducedGradientStageTrialPoint
    method.constraint
    method.basicJacobian
    method.reducedGradient
    method.initialStepSize
    method.iterate
    k
    (method.acceptedBacktrack k)
    (method.acceptedCorrection k)

/-- A modified-Step-7 generalized reduced-gradient run has a uniform acceptance threshold if one
positive constant `η` forces the sufficient-decrease search to accept every continuing stage
whose trial-step product `αₖ,ₗ * ‖g̃ₖ‖` is at most `η`. This packages the stage-uniform
small-step side condition used by Chapter11 Theorem 11.3.2. -/
def GeneralizedReducedGradientSufficientDecreaseMethod.HasUniformAcceptanceThreshold
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β) :
    Prop :=
  ∃ η ∈ Set.Ioi (0 : ℝ),
    ∀ k l, 1 ≤ k → method.active (k + 1) →
      generalizedReducedGradientTrialStepSize (method.initialStepSize k) l *
          ‖method.reducedGradient k‖ ≤
        η →
      ∃ j,
        generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
            method.objective
            method.constraint
            method.basicJacobian
            method.reducedGradient
            method.initialStepSize
            β
            method.εBar
            method.maxCorrections
            method.iterate
            k
            l =
          some j

namespace GeneralizedReducedGradientMethod

/-- Helper for Chapter11 Theorem 11.3.2: the recorded accepted Step 6 steplength is positive on
continuing stages. -/
lemma acceptedTrialStepSize_pos_of_continue
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    0 < method.acceptedTrialStepSize k := by
  -- The accepted steplength is the positive initial steplength divided by a positive dyadic
  -- factor.
  change
    0 <
      method.initialStepSize k / ((2 : ℝ) ^ method.acceptedBacktrack k)
  exact div_pos
    (method.initialStepSize_pos k hk hnext)
    (pow_pos (by norm_num) _)

/-- Helper for Chapter11 Theorem 11.3.2: the accepted trial point satisfies the modified Step 7
sufficient-decrease inequality `(11.3.5)` at every continuing stage. -/
lemma acceptedTrialPoint_sufficientDecrease
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    method.objective (method.acceptedTrialPoint k) ≤
      method.objective (method.iterate k) -
        (method.acceptedTrialStepSize k * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 := by
  have hAccepted := method.acceptedCorrectionAt_eq_some k hk hnext
  -- Unfold the accepted search and read off the true sufficient-decrease branch.
  rw [generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease] at hAccepted
  classical
  cases
      hFirst :
        generalizedReducedGradientStageFirstResidualAcceptedCorrection
          method.constraint
          method.εBar
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.maxCorrections
          method.iterate
          k
          (method.acceptedBacktrack k)
    with
  | none =>
      simp [hFirst] at hAccepted
  | some j =>
      by_cases hDecrease :
          generalizedReducedGradientSufficientDecreaseAccepts
            method.objective
            method.iterate
            (generalizedReducedGradientStageTrialBasic
              method.constraint
              method.basicJacobian
              method.reducedGradient
              method.initialStepSize
              method.iterate)
            (generalizedReducedGradientStageTrialNonbasic
              method.iterate
              method.reducedGradient
              method.initialStepSize)
            method.reducedGradient
            method.initialStepSize
            β
            k
            (method.acceptedBacktrack k)
            j
      · have hj :
          j = method.acceptedCorrection k := by
            have hSome : some j = some (method.acceptedCorrection k) := by
              simpa [hFirst, hDecrease] using hAccepted
            exact Option.some.inj hSome
        subst hj
        -- Normalize the public accepted-point aliases only after extracting the search witness.
        simpa [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialPoint,
          GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialStepSize,
          generalizedReducedGradientSufficientDecreaseAccepts,
          generalizedReducedGradientStageTrialPoint,
          generalizedReducedGradientTrialPoint] using hDecrease
      · simp [hFirst, hDecrease] at hAccepted

/-- Helper for Chapter11 Theorem 11.3.2: on every continuing stage, the accepted Step 4/Step 5
trial point remains feasible for the equality constraints `c(x) = 0`. -/
lemma acceptedTrialPoint_constraint_eq_zero_of_continue
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    method.constraint (method.acceptedTrialPoint k) = 0 := by
  have hZero :
      method.constraint (method.iterate (k + 1)) = 0 :=
    method.constraint_iterate_eq_zero_of_active
      (k + 1)
      (Nat.succ_le_succ (Nat.zero_le k))
      hnext
  rw [method.iterate_succ_eq_acceptedTrialPoint k hk hnext] at hZero
  simpa [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialPoint] using hZero

/-- Helper for Chapter11 Theorem 11.3.2: a fixed accepted correction at depth `L` forces the
recorded accepted backtracking count to be at most `L`. -/
private lemma acceptedBacktrack_le_of_existsAcceptedCorrection
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    {k L : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1))
    (hAcceptedAtL :
      ∃ j,
        generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
            method.objective
            method.constraint
            method.basicJacobian
            method.reducedGradient
            method.initialStepSize
            β
            method.εBar
            method.maxCorrections
            method.iterate
            k
            L =
          some j) :
    method.acceptedBacktrack k ≤ L := by
  by_contra hNotLe
  have hEarlier :
      generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
          method.objective
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          β
          method.εBar
          method.maxCorrections
          method.iterate
          k
          L =
        none :=
    method.earlierBacktrackingRejected k hk hnext L (Nat.lt_of_not_ge hNotLe)
  rcases hAcceptedAtL with ⟨j, hj⟩
  rw [hEarlier] at hj
  simp at hj

/-- Helper for Chapter11 Theorem 11.3.2: a uniform reciprocal bound on the Step 3 initial
steplengths yields a uniform positive lower bound on those steplengths along continuing stages. -/
lemma initialStepSize_ge_uniform_of_boundedInverseNorm
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hBoundedAlpha0Inv :
      ∃ C ∈ Set.Ici (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) → ‖(method.initialStepSize k)⁻¹‖ ≤ C) :
    ∃ a ∈ Set.Ioi (0 : ℝ),
      ∀ k, 1 ≤ k → method.active (k + 1) → a ≤ method.initialStepSize k := by
  rcases hBoundedAlpha0Inv with ⟨C, hCnonneg, hCbound⟩
  refine ⟨(max C 1)⁻¹, by
    have hMaxPos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    exact inv_pos.mpr hMaxPos, ?_⟩
  intro k hk hnext
  have hαpos : 0 < method.initialStepSize k := method.initialStepSize_pos k hk hnext
  have hInvLeC : (method.initialStepSize k)⁻¹ ≤ C := by
    have hNorm := hCbound k hk hnext
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hαpos] at hNorm
    exact hNorm
  have hInvLeMax : (method.initialStepSize k)⁻¹ ≤ max C 1 :=
    le_trans hInvLeC (le_max_left _ _)
  have hMul : 1 ≤ method.initialStepSize k * max C 1 :=
    (inv_le_iff_one_le_mul₀' hαpos).1 hInvLeMax
  have hMaxPos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  exact (inv_le_iff_one_le_mul₀ hMaxPos).2 (by simpa [mul_comm] using hMul)

/-- Helper for Chapter11 Theorem 11.3.2: a uniform accepted backtracking depth together with a
uniform lower bound on the initial steplengths gives a uniform lower bound on the accepted
steplengths. -/
lemma acceptedTrialStepSize_ge_uniform_of_uniformAcceptedDepth
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hBoundedAlpha0Inv :
      ∃ C ∈ Set.Ici (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) → ‖(method.initialStepSize k)⁻¹‖ ≤ C)
    (hUniformAcceptedDepth :
      ∃ L : ℕ,
        ∀ k, 1 ≤ k → method.active (k + 1) →
          ∃ j,
            generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
                method.objective
                method.constraint
                method.basicJacobian
                method.reducedGradient
                method.initialStepSize
                β
                method.εBar
                method.maxCorrections
                method.iterate
                k
                L =
              some j) :
    ∃ a ∈ Set.Ioi (0 : ℝ),
      ∀ k, 1 ≤ k → method.active (k + 1) → a ≤ method.acceptedTrialStepSize k := by
  rcases initialStepSize_ge_uniform_of_boundedInverseNorm
      method hBoundedAlpha0Inv with
    ⟨a0, ha0pos, hInitLower⟩
  rcases hUniformAcceptedDepth with ⟨L, hL⟩
  refine ⟨a0 / ((2 : ℝ) ^ L), by
    exact div_pos (show 0 < a0 from ha0pos) (pow_pos (by norm_num) _), ?_⟩
  intro k hk hnext
  have hBacktrackLe :
      method.acceptedBacktrack k ≤ L :=
    acceptedBacktrack_le_of_existsAcceptedCorrection method hk hnext (hL k hk hnext)
  have hInitPos : 0 < method.initialStepSize k := method.initialStepSize_pos k hk hnext
  have hInitLower' : a0 ≤ method.initialStepSize k := hInitLower k hk hnext
  have hInvPow :
      (1 : ℝ) / ((2 : ℝ) ^ L) ≤ (1 : ℝ) / ((2 : ℝ) ^ method.acceptedBacktrack k) := by
    have hPowLe :
        ((2 : ℝ) ^ method.acceptedBacktrack k) ≤ ((2 : ℝ) ^ L) := by
      exact pow_le_pow_right₀ (by norm_num) hBacktrackLe
    exact one_div_le_one_div_of_le (pow_pos (by norm_num) _) hPowLe
  have hScaledInv :
      method.initialStepSize k * ((1 : ℝ) / ((2 : ℝ) ^ L)) ≤
        method.initialStepSize k * ((1 : ℝ) / ((2 : ℝ) ^ method.acceptedBacktrack k)) :=
    mul_le_mul_of_nonneg_left hInvPow hInitPos.le
  have hScaledBase :
      a0 * ((1 : ℝ) / ((2 : ℝ) ^ L)) ≤
        method.initialStepSize k * ((1 : ℝ) / ((2 : ℝ) ^ L)) :=
    mul_le_mul_of_nonneg_right hInitLower' (by positivity)
  -- First lower the numerator using the uniform initial-step bound, then enlarge the reciprocal
  -- factor using `acceptedBacktrack k ≤ L`.
  calc
    a0 / ((2 : ℝ) ^ L) = a0 * ((1 : ℝ) / ((2 : ℝ) ^ L)) := by ring
    _ ≤ method.initialStepSize k * ((1 : ℝ) / ((2 : ℝ) ^ L)) := hScaledBase
    _ ≤ method.initialStepSize k * ((1 : ℝ) / ((2 : ℝ) ^ method.acceptedBacktrack k)) :=
      hScaledInv
    _ = method.acceptedTrialStepSize k := by
      simp [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialStepSize,
        generalizedReducedGradientTrialStepSize, div_eq_mul_inv]

/-- Helper for Chapter11 Theorem 11.3.2: once the accepted steplengths are uniformly bounded
below, the modified Step 7 sufficient-decrease inequality yields a uniform quadratic lower bound
on each recorded objective drop. -/
lemma acceptedObjectiveDrop_ge_reducedGradientNormSq_of_uniformAcceptedDepth
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hBoundedAlpha0Inv :
      ∃ C ∈ Set.Ici (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) → ‖(method.initialStepSize k)⁻¹‖ ≤ C)
    (hUniformAcceptedDepth :
      ∃ L : ℕ,
        ∀ k, 1 ≤ k → method.active (k + 1) →
          ∃ j,
            generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
                method.objective
                method.constraint
                method.basicJacobian
                method.reducedGradient
                method.initialStepSize
                β
                method.εBar
                method.maxCorrections
                method.iterate
                k
                L =
              some j)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ A ∈ Set.Ioi (0 : ℝ),
      ∀ k, 1 ≤ k → method.active (k + 1) →
        A * ‖method.reducedGradient k‖ ^ (2 : ℕ) ≤
          method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := by
  rcases
      acceptedTrialStepSize_ge_uniform_of_uniformAcceptedDepth
        method hBoundedAlpha0Inv hUniformAcceptedDepth with
    ⟨a, hapos, hStepLower⟩
  refine ⟨a * β / 2, by
    have ha : 0 < a := hapos
    exact div_pos (mul_pos ha hβ.1) (by norm_num), ?_⟩
  intro k hk hnext
  have hSuff := acceptedTrialPoint_sufficientDecrease method hk hnext
  have hStepLe :
      (a * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 ≤
        (method.acceptedTrialStepSize k * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 := by
    have hCore :
        a * β * ‖method.reducedGradient k‖ ^ (2 : ℕ) ≤
          method.acceptedTrialStepSize k * β * ‖method.reducedGradient k‖ ^ (2 : ℕ) := by
      have hStepScaled :
          a * (β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) ≤
            method.acceptedTrialStepSize k * (β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right
          (hStepLower k hk hnext)
          (mul_nonneg hβ.1.le (by positivity))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hStepScaled
    exact div_le_div_of_nonneg_right hCore (by norm_num : (0 : ℝ) ≤ 2)
  have hIterateEq :
      method.iterate (k + 1) = method.acceptedTrialPoint k :=
    method.iterate_succ_eq_acceptedTrialPoint k hk hnext
  -- Rewrite the next iterate as the accepted trial point and compare the guaranteed drop.
  have hDrop :
      (method.acceptedTrialStepSize k * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 ≤
        method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := by
    rw [hIterateEq]
    linarith
  calc
    (a * β / 2) * ‖method.reducedGradient k‖ ^ (2 : ℕ)
        = (a * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 := by ring
    _ ≤ (method.acceptedTrialStepSize k * β * ‖method.reducedGradient k‖ ^ (2 : ℕ)) / 2 := hStepLe
    _ ≤ method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := hDrop

/-- Helper for Chapter11 Theorem 11.3.2: the continuing zero-tolerance regime forces each
accepted sufficient-decrease step to lower the objective strictly along the shifted tail. -/
lemma objectiveStrictDecrease_succ
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : method.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → method.active k) :
    ∀ k : ℕ, method.objective (method.iterate (k + 2)) <
      method.objective (method.iterate (k + 1)) := by
  intro k
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hnext : method.active (k + 2) :=
    hNonterminating (k + 2) (Nat.succ_le_succ (Nat.zero_le (k + 1)))
  have hSuff := acceptedTrialPoint_sufficientDecrease method hk hnext
  have hStepPos : 0 < method.acceptedTrialStepSize (k + 1) :=
    acceptedTrialStepSize_pos_of_continue method hk hnext
  have hGradPos : 0 < ‖method.reducedGradient (k + 1)‖ := by
    have hActiveSucc :
        (1 ≤ k + 1 → method.active (k + 2)) ↔
          method.active (k + 1) ∧ method.ε < ‖method.reducedGradient (k + 1)‖ := by
      simpa using method.active_succ_iff (k + 1)
    have hContinue := hActiveSucc.mp (fun _ ↦ hnext)
    rw [hε] at hContinue
    exact hContinue.2
  have hPenaltyPos :
      0 <
        (method.acceptedTrialStepSize (k + 1) * β *
            ‖method.reducedGradient (k + 1)‖ ^ (2 : ℕ)) / 2 := by
    have hNormSqPos : 0 < ‖method.reducedGradient (k + 1)‖ ^ (2 : ℕ) := by
      positivity
    exact div_pos (mul_pos (mul_pos hStepPos hβ.1) hNormSqPos) (by norm_num)
  -- Replace the next iterate by the accepted trial point and use positivity of the
  -- sufficient-decrease penalty.
  calc
    method.objective (method.iterate (k + 2))
        = method.objective (method.acceptedTrialPoint (k + 1)) := by
            simpa [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialPoint] using
              congrArg method.objective
                (method.iterate_succ_eq_acceptedTrialPoint (k + 1) hk hnext)
    _ < method.objective (method.iterate (k + 1)) := by
      linarith

/-- Helper for Chapter11 Theorem 11.3.2: if the objective values do not tend to `-∞`, then the
shifted sufficient-decrease objective tail converges to a finite lower bound. -/
lemma objectiveTailConverges_of_notAtBot
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : method.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → method.active k)
    (hObjective :
      ¬ Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot) :
    ∃ l : ℝ,
      Tendsto (fun k : ℕ ↦ method.objective (method.iterate (k + 1))) atTop (nhds l) ∧
        ∀ k : ℕ, l ≤ method.objective (method.iterate (k + 1)) := by
  have hanti : Antitone (fun k : ℕ ↦ method.objective (method.iterate (k + 1))) := by
    -- Convert one-step strict decrease into an antitone shifted tail.
    refine antitone_nat_of_succ_le fun k ↦ ?_
    exact (objectiveStrictDecrease_succ method hβ hε hNonterminating k).le
  rcases tendsto_atTop_of_antitone hanti with hbot | ⟨l, hl⟩
  · exact False.elim <| hObjective <| (Filter.tendsto_add_atTop_iff_nat 1).mp hbot
  · refine ⟨l, hl, ?_⟩
    intro N
    by_contra hLower
    let m : ℝ := (method.objective (method.iterate (N + 1)) + l) / 2
    have hObj_lt_m : method.objective (method.iterate (N + 1)) < m := by
      dsimp [m]
      linarith
    have hm_lt_l : m < l := by
      dsimp [m]
      linarith
    have hEventuallyUpper :
        ∀ᶠ k : ℕ in atTop, method.objective (method.iterate (k + 1)) < m := by
      -- Once the antitone tail drops below `m`, it stays below `m`.
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro k hk
      exact lt_of_le_of_lt (hanti hk) hObj_lt_m
    have hEventuallyLower :
        ∀ᶠ k : ℕ in atTop, m < method.objective (method.iterate (k + 1)) := by
      -- The tail limit lies in every right neighborhood of `l`.
      exact hl.eventually (Ioi_mem_nhds hm_lt_l)
    rcases Filter.eventually_atTop.1 hEventuallyUpper with ⟨K₁, hK₁⟩
    rcases Filter.eventually_atTop.1 hEventuallyLower with ⟨K₂, hK₂⟩
    have hUpperAtMax :
        method.objective (method.iterate (max K₁ K₂ + 1)) < m :=
      hK₁ (max K₁ K₂) (le_max_left _ _)
    have hLowerAtMax :
        m < method.objective (method.iterate (max K₁ K₂ + 1)) :=
      hK₂ (max K₁ K₂) (le_max_right _ _)
    exact (not_lt_of_ge hUpperAtMax.le) hLowerAtMax

/-- Helper for Chapter11 Theorem 11.3.2: the shifted sufficient-decrease objective drops
telescope exactly over `Finset.range (N + 1)`. -/
lemma objectiveDropSum_range_eq
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β) :
    ∀ N : ℕ,
      Finset.sum (Finset.range (N + 1))
        (fun i ↦ method.objective (method.iterate (i + 1)) -
          method.objective (method.iterate (i + 2))) =
        method.objective (method.iterate 1) - method.objective (method.iterate (N + 2)) := by
  intro N
  induction N with
  | zero =>
      -- The first partial sum contains only the initial objective drop.
      simp
  | succ N ih =>
      -- Append the next tail drop and cancel the middle objective value.
      calc
        Finset.sum (Finset.range (N + 1 + 1))
            (fun i ↦ method.objective (method.iterate (i + 1)) -
              method.objective (method.iterate (i + 2))) =
          Finset.sum (Finset.range (N + 1))
            (fun i ↦ method.objective (method.iterate (i + 1)) -
              method.objective (method.iterate (i + 2))) +
                (method.objective (method.iterate (N + 2)) -
                  method.objective (method.iterate (N + 3))) := by
                rw [Finset.sum_range_succ]
        _ = (method.objective (method.iterate 1) - method.objective (method.iterate (N + 2))) +
              (method.objective (method.iterate (N + 2)) -
                method.objective (method.iterate (N + 3))) := by
                  rw [ih]
        _ = method.objective (method.iterate 1) - method.objective (method.iterate (N + 3)) := by
              ring

/-- Helper for Chapter11 Theorem 11.3.2: a uniform quadratic lower bound on the objective drops
forces the shifted reduced-gradient norms to converge to `0` on the non-`atBot` branch. -/
lemma tendsto_shiftedReducedGradientNorm_zero_of_objectiveDropLower
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : method.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → method.active k)
    (hObjective :
      ¬ Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot)
    (hDropLower :
      ∃ A ∈ Set.Ioi (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) →
          A * ‖method.reducedGradient k‖ ^ (2 : ℕ) ≤
            method.objective (method.iterate k) - method.objective (method.iterate (k + 1))) :
    Tendsto (fun i : ℕ ↦ ‖method.reducedGradient (i + 1)‖) atTop (nhds (0 : ℝ)) := by
  rcases objectiveTailConverges_of_notAtBot
      method hβ hε hNonterminating hObjective with
    ⟨l, hl, _hlower⟩
  rcases hDropLower with ⟨A, hApos, hDropLower⟩
  let drop : ℕ → ℝ := fun i ↦
    method.objective (method.iterate (i + 1)) - method.objective (method.iterate (i + 2))
  have hDropNonneg : ∀ i, 0 ≤ drop i := by
    intro i
    dsimp [drop]
    exact sub_nonneg.mpr
      (objectiveStrictDecrease_succ method hβ hε hNonterminating i).le
  have hTailObjective :
      Tendsto (fun N : ℕ ↦ method.objective (method.iterate (N + 2))) atTop (nhds l) := by
    -- Shift the convergent tail once more to match the telescoping identity.
    refine Tendsto.congr' ?_ (hl.comp (Filter.tendsto_add_atTop_nat 1))
    exact Filter.Eventually.of_forall fun N ↦ by simp [Nat.add_assoc]
  have hDropSumsShifted :
      Tendsto (fun N : ℕ ↦ Finset.sum (Finset.range (N + 1)) drop) atTop
        (nhds (method.objective (method.iterate 1) - l)) := by
    -- Telescope the finite sums and pass to the limit of the shifted tail objective values.
    have hGapTendsto :
        Tendsto
            (fun N : ℕ ↦
              method.objective (method.iterate 1) -
                method.objective (method.iterate (N + 2)))
            atTop
            (nhds (method.objective (method.iterate 1) - l)) :=
      tendsto_const_nhds.sub hTailObjective
    refine Tendsto.congr' ?_ hGapTendsto
    exact Filter.Eventually.of_forall fun N ↦
      (objectiveDropSum_range_eq method N).symm
  have hDropSums :
      Tendsto (fun N : ℕ ↦ Finset.sum (Finset.range N) drop) atTop
        (nhds (method.objective (method.iterate 1) - l)) := by
    -- Remove the harmless one-step shift so `hasSum_iff_tendsto_nat_of_nonneg` applies
    -- directly.
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hDropSumsShifted
  have hDropSummable : Summable drop := by
    exact
      ((hasSum_iff_tendsto_nat_of_nonneg hDropNonneg
        (method.objective (method.iterate 1) - l)).2 hDropSums).summable
  let scaledSq : ℕ → ℝ := fun i ↦ A * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ)
  have hScaledSqNonneg : ∀ i, 0 ≤ scaledSq i := by
    intro i
    dsimp [scaledSq]
    exact mul_nonneg (show 0 ≤ A from (show 0 < A from hApos).le) (by positivity)
  have hScaledSqLe : ∀ i, scaledSq i ≤ drop i := by
    intro i
    have hi : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
    have hnext : method.active (i + 2) :=
      hNonterminating (i + 2) (Nat.succ_le_succ (Nat.zero_le (i + 1)))
    simpa [scaledSq, drop] using hDropLower (i + 1) hi hnext
  have hScaledSqSummable : Summable scaledSq := by
    exact Summable.of_nonneg_of_le hScaledSqNonneg hScaledSqLe hDropSummable
  have hAne : A ≠ 0 := (show 0 < A from hApos).ne'
  have hSqSummable :
      Summable (fun i ↦ ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ)) := by
    simpa [scaledSq] using (summable_mul_left_iff hAne).1 hScaledSqSummable
  have hSqTendstoZero :
      Tendsto (fun i ↦ ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ)) atTop (nhds (0 : ℝ)) := by
    exact Summable.tendsto_atTop_zero hSqSummable
  -- Recover the norm from its square by composing with `Real.sqrt`.
  have hSqrt :
      Tendsto
          ((fun x : ℝ ↦ Real.sqrt x) ∘ fun i ↦ ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
          atTop
          (nhds (0 : ℝ)) := by
    have hCont : ContinuousAt (fun x : ℝ ↦ Real.sqrt x) 0 :=
      Real.continuous_sqrt.continuousAt
    simpa using hCont.tendsto.comp hSqTendstoZero
  refine Tendsto.congr' ?_ hSqrt
  exact Filter.Eventually.of_forall fun i ↦ by
    rw [Function.comp]
    simpa [pow_two] using
      (Real.sqrt_sq_eq_abs ‖method.reducedGradient (i + 1)‖)

/-- Helper for Chapter11 Theorem 11.3.2: relate the stage-local residual-acceptance predicate to
the search-level residual-acceptance predicate used by the modified sufficient-decrease method. -/
private lemma residualAcceptsAt_iff_stageResidualAccepts
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k l j : ℕ) :
    generalizedReducedGradientResidualAcceptsAt
        method.constraint
        method.εBar
        (fun _ ↦ method.basicJacobian k)
        (fun _ ↦ method.reducedGradient k)
        (fun _ ↦ method.initialStepSize k)
        (method.iterate k)
        l
        j ↔
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        j := by
  -- Normalize the stage aliases so both residual tests talk about the same trial point.
  simp [generalizedReducedGradientResidualAccepts, generalizedReducedGradientResidualAcceptsAt,
    generalizedReducedGradientTrialPointAt, generalizedReducedGradientTrialPoint,
    generalizedReducedGradientStageTrialBasic, generalizedReducedGradientStageTrialNonbasic,
    generalizedReducedGradientTrialNonbasicAt, generalizedReducedGradientTrialStepSize]

/-- Helper for Chapter11 Theorem 11.3.2: if `j` is the first residual-acceptable correction in
the auxiliary Step 5 window `jStart, ..., jStart + remaining - 1`, then the auxiliary search
returns exactly `some j`. -/
private lemma firstResidualAcceptedCorrectionAux_eq_some_of_firstResidual
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k l : ℕ) :
    ∀ jStart remaining j : ℕ,
      jStart ≤ j →
      j < jStart + remaining →
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        j →
      (∀ i, jStart ≤ i → i < j →
        ¬ generalizedReducedGradientResidualAccepts
            method.constraint
            method.εBar
            (generalizedReducedGradientStageTrialBasic
              method.constraint
              method.basicJacobian
              method.reducedGradient
              method.initialStepSize
              method.iterate)
            (generalizedReducedGradientStageTrialNonbasic
              method.iterate
              method.reducedGradient
              method.initialStepSize)
            k
            l
            i) →
      generalizedReducedGradientFirstResidualAcceptedCorrectionAux
          method.constraint
          method.εBar
          (fun _ ↦ method.basicJacobian k)
          (fun _ ↦ method.reducedGradient k)
          (fun _ ↦ method.initialStepSize k)
          (method.iterate k)
          l
          jStart
          remaining =
        some j := by
  intro jStart remaining j
  induction remaining generalizing jStart j with
  | zero =>
      intro hjLower hjUpper _hResidual _hEarlier
      have hjUpper' : j < jStart := by
        simpa using hjUpper
      exact (not_lt_of_ge hjLower hjUpper').elim
  | succ remaining ih =>
      intro hjLower hjUpper hResidual hEarlier
      by_cases hCurrent :
          generalizedReducedGradientResidualAccepts
            method.constraint
            method.εBar
            (generalizedReducedGradientStageTrialBasic
              method.constraint
              method.basicJacobian
              method.reducedGradient
              method.initialStepSize
              method.iterate)
            (generalizedReducedGradientStageTrialNonbasic
              method.iterate
              method.reducedGradient
              method.initialStepSize)
            k
            l
            jStart
      · -- If the current correction already passes the residual test, minimality forces
        -- `j = jStart`.
        have hEq : j = jStart := by
          by_contra hEq
          have hjStart_lt_j : jStart < j := lt_of_le_of_ne hjLower (Ne.symm hEq)
          exact (hEarlier jStart le_rfl hjStart_lt_j hCurrent).elim
        subst hEq
        have hCurrentAt :
            generalizedReducedGradientResidualAcceptsAt
              method.constraint
              method.εBar
              (fun _ ↦ method.basicJacobian k)
              (fun _ ↦ method.reducedGradient k)
              (fun _ ↦ method.initialStepSize k)
              (method.iterate k)
              l
              j := (residualAcceptsAt_iff_stageResidualAccepts method k l j).2 hCurrent
        simp [generalizedReducedGradientFirstResidualAcceptedCorrectionAux, hCurrentAt]
      · -- Otherwise the auxiliary search skips `jStart` and recurses to `jStart + 1`.
        have hjStart_lt_j : jStart < j := by
          by_contra hNotLt
          have hj_le_jStart : j ≤ jStart := Nat.not_lt.mp hNotLt
          have hEq : j = jStart := le_antisymm hj_le_jStart hjLower
          subst hEq
          exact hCurrent hResidual
        have hjLower' : jStart + 1 ≤ j := Nat.succ_le_of_lt hjStart_lt_j
        have hjUpper' : j < (jStart + 1) + remaining := by
          omega
        have hEarlier' :
            ∀ i, jStart + 1 ≤ i → i < j →
              ¬ generalizedReducedGradientResidualAccepts
                  method.constraint
                  method.εBar
                  (generalizedReducedGradientStageTrialBasic
                    method.constraint
                    method.basicJacobian
                    method.reducedGradient
                    method.initialStepSize
                    method.iterate)
                  (generalizedReducedGradientStageTrialNonbasic
                    method.iterate
                    method.reducedGradient
                    method.initialStepSize)
                  k
                  l
                  i := by
          intro i hiLower hiLt
          exact hEarlier i (le_trans (Nat.le_succ _) hiLower) hiLt
        have hTail :=
          ih (jStart + 1) j hjLower' hjUpper' hResidual hEarlier'
        have hCurrentAt :
            ¬ generalizedReducedGradientResidualAcceptsAt
                method.constraint
                method.εBar
                (fun _ ↦ method.basicJacobian k)
                (fun _ ↦ method.reducedGradient k)
                (fun _ ↦ method.initialStepSize k)
                (method.iterate k)
                l
                jStart := by
          simpa [residualAcceptsAt_iff_stageResidualAccepts method k l jStart] using hCurrent
        simp [generalizedReducedGradientFirstResidualAcceptedCorrectionAux, hCurrentAt, hTail]

/-- Helper for Chapter11 Theorem 11.3.2: any residual-acceptable Step 5 correction in the
public window `1, ..., method.maxCorrections` forces the public Step 5 search to return some
correction count. -/
lemma firstResidualAcceptedCorrection_eq_some_of_exists_residualAccepts
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    {k l j : ℕ}
    (hjLower : 1 ≤ j)
    (hjUpper : j ≤ method.maxCorrections)
    (hResidual :
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        j) :
    ∃ j0,
      generalizedReducedGradientStageFirstResidualAcceptedCorrection
          method.constraint
          method.εBar
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.maxCorrections
          method.iterate
          k
          l =
        some j0 := by
  classical
  let P : ℕ → Prop := fun j0 ↦
    1 ≤ j0 ∧
      j0 ≤ method.maxCorrections ∧
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        j0
  have hExists : ∃ j0, P j0 := ⟨j, hjLower, hjUpper, hResidual⟩
  let j0 := Nat.find hExists
  have hj0Spec : P j0 := Nat.find_spec hExists
  refine ⟨j0, ?_⟩
  -- Pick the minimal residual-acceptable correction so the exact auxiliary-search lemma applies.
  have hEarlier :
      ∀ i, 1 ≤ i → i < j0 →
        ¬ generalizedReducedGradientResidualAccepts
            method.constraint
            method.εBar
            (generalizedReducedGradientStageTrialBasic
              method.constraint
              method.basicJacobian
              method.reducedGradient
              method.initialStepSize
              method.iterate)
            (generalizedReducedGradientStageTrialNonbasic
              method.iterate
              method.reducedGradient
              method.initialStepSize)
            k
            l
            i := by
    intro i hiLower hiLt hResidualI
    have hiMem : P i := ⟨hiLower, le_trans (Nat.le_of_lt hiLt) hj0Spec.2.1, hResidualI⟩
    exact (not_le_of_gt hiLt) (Nat.find_min' hExists hiMem)
  have hj0Upper' : j0 < 1 + method.maxCorrections := by
    omega
  have hAux :=
    firstResidualAcceptedCorrectionAux_eq_some_of_firstResidual method k l
      1
      method.maxCorrections
      j0
      hj0Spec.1
      hj0Upper'
      hj0Spec.2.2
      hEarlier
  simpa [generalizedReducedGradientStageFirstResidualAcceptedCorrection,
    generalizedReducedGradientFirstResidualAcceptedCorrection] using hAux

/-- Helper for Chapter11 Theorem 11.3.2: if the very first public Step 5 correction `j = 1`
already satisfies the residual test, then the public Step 5 search returns `some 1`. -/
private lemma firstResidualAcceptedCorrection_eq_some_one_of_residualAccepts_one
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k l : ℕ)
    (hResidual :
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        1) :
    generalizedReducedGradientStageFirstResidualAcceptedCorrection
        method.constraint
        method.εBar
        method.basicJacobian
        method.reducedGradient
        method.initialStepSize
        method.maxCorrections
        method.iterate
        k
        l =
      some 1 := by
  -- Start the auxiliary Step 5 search at `jStart = 1`; there are no earlier positive
  -- corrections to rule out.
  have hUpper : 1 < 1 + method.maxCorrections := by
    simpa using method.maxCorrections_pos
  have hAux :=
    firstResidualAcceptedCorrectionAux_eq_some_of_firstResidual method k l
      1
      method.maxCorrections
      1
      le_rfl
      hUpper
      hResidual
      (by
        intro i hiLower hiLt
        omega)
  simpa [generalizedReducedGradientStageFirstResidualAcceptedCorrection,
    generalizedReducedGradientFirstResidualAcceptedCorrection] using hAux

/-- Helper for Chapter11 Theorem 11.3.2: if `j = 1` is already the first residual-acceptable
Step 5 correction and it satisfies the modified Step 7 sufficient-decrease inequality, then the
modified Step 6/Step 7 search accepts `j = 1`. -/
private lemma acceptedCorrection_eq_some_one_of_step5_one_and_sufficientDecrease
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (k l : ℕ)
    (hResidual :
      generalizedReducedGradientResidualAccepts
        method.constraint
        method.εBar
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        k
        l
        1)
    (hDecrease :
      generalizedReducedGradientSufficientDecreaseAccepts
        method.objective
        method.iterate
        (generalizedReducedGradientStageTrialBasic
          method.constraint
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.iterate)
        (generalizedReducedGradientStageTrialNonbasic
          method.iterate
          method.reducedGradient
          method.initialStepSize)
        method.reducedGradient
        method.initialStepSize
        β
        k
        l
        1) :
    generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
        method.objective
        method.constraint
        method.basicJacobian
        method.reducedGradient
        method.initialStepSize
        β
        method.εBar
        method.maxCorrections
        method.iterate
        k
        l =
      some 1 := by
  have hFirst :
      generalizedReducedGradientStageFirstResidualAcceptedCorrection
          method.constraint
          method.εBar
          method.basicJacobian
          method.reducedGradient
          method.initialStepSize
          method.maxCorrections
          method.iterate
          k
          l =
        some 1 :=
    firstResidualAcceptedCorrection_eq_some_one_of_residualAccepts_one method k l hResidual
  -- Once the Step 5 search returns `1`, the modified Step 7 branch accepts exactly when the
  -- sufficient-decrease predicate is true at that same witness.
  rw [generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease, hFirst]
  simp [hDecrease]

/-- Helper for Chapter11 Theorem 11.3.2: the analytic threshold on
`generalizedReducedGradientTrialStepSize (αₖ⁽⁰⁾) l * ‖g̃ₖ‖` forces the recorded accepted
steplength product to dominate `min (αₖ⁽⁰⁾ * ‖g̃ₖ‖) (η / 2)`. -/
lemma
    GeneralizedReducedGradientSufficientDecreaseMethod.acceptedStepMulNorm_ge_min_initial_or_threshold
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hThreshold : method.HasUniformAcceptanceThreshold) :
    ∃ η ∈ Set.Ioi (0 : ℝ),
      ∀ k, 1 ≤ k → method.active (k + 1) →
        min (method.initialStepSize k * ‖method.reducedGradient k‖) (η / 2) ≤
          method.acceptedTrialStepSize k * ‖method.reducedGradient k‖ := by
  rcases hThreshold with ⟨η, hηpos, hThreshold⟩
  refine ⟨η, hηpos, ?_⟩
  intro k hk hnext
  by_cases hBacktrackZero : method.acceptedBacktrack k = 0
  · -- If the accepted depth is `0`, the accepted steplength is the initial steplength itself.
    simpa [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialStepSize,
      generalizedReducedGradientTrialStepSize, hBacktrackZero] using
      (min_le_left
        (method.initialStepSize k * ‖method.reducedGradient k‖)
        (η / 2))
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hBacktrackZero
    have hRejected :
        generalizedReducedGradientStageAcceptedCorrectionBySufficientDecrease
            method.objective
            method.constraint
            method.basicJacobian
            method.reducedGradient
            method.initialStepSize
            β
            method.εBar
            method.maxCorrections
            method.iterate
            k
            m =
          none := by
      have hmLt : m < method.acceptedBacktrack k := by
        rw [hm]
        exact Nat.lt_succ_self m
      exact method.earlierBacktrackingRejected k hk hnext m hmLt
    have hEtaHalfLe :
        η / 2 ≤ method.acceptedTrialStepSize k * ‖method.reducedGradient k‖ := by
      by_contra hNotLe
      have hAcceptedLt : method.acceptedTrialStepSize k * ‖method.reducedGradient k‖ < η / 2 :=
        lt_of_not_ge hNotLe
      have hPrevLt :
          generalizedReducedGradientTrialStepSize (method.initialStepSize k) m *
              ‖method.reducedGradient k‖ <
            η := by
        have hRewrite :
            generalizedReducedGradientTrialStepSize (method.initialStepSize k) m *
                ‖method.reducedGradient k‖ =
              2 * (method.acceptedTrialStepSize k * ‖method.reducedGradient k‖) := by
          -- One less backtracking step doubles the recorded accepted steplength.
          simp [GeneralizedReducedGradientSufficientDecreaseMethod.acceptedTrialStepSize,
            generalizedReducedGradientTrialStepSize, hm]
          ring
        rw [hRewrite]
        nlinarith
      rcases hThreshold k m hk hnext hPrevLt.le with ⟨j, hj⟩
      rw [hRejected] at hj
      simp at hj
    calc
      min (method.initialStepSize k * ‖method.reducedGradient k‖) (η / 2)
          ≤ η / 2 := min_le_right _ _
      _ ≤ method.acceptedTrialStepSize k * ‖method.reducedGradient k‖ := hEtaHalfLe

/-- Helper for Chapter11 Theorem 11.3.2: the threshold acceptance bridge and the modified Step 7
sufficient-decrease inequality give a mixed lower bound on each recorded objective drop. -/
lemma
    GeneralizedReducedGradientSufficientDecreaseMethod.acceptedObjectiveDrop_ge_min_initialMulSq_or_norm
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hThreshold : method.HasUniformAcceptanceThreshold)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C ∈ Set.Ioi (0 : ℝ),
      ∀ k, 1 ≤ k → method.active (k + 1) →
        C *
            min
              (method.initialStepSize k * ‖method.reducedGradient k‖ ^ (2 : ℕ))
              (‖method.reducedGradient k‖) ≤
          method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := by
  -- Route correction: the old fixed-depth route was too strong. The stable owner-level target
  -- is the mixed drop estimate that only depends on `min (αₖ⁽⁰⁾ * ‖g̃ₖ‖²) ‖g̃ₖ‖`.
  rcases
      acceptedStepMulNorm_ge_min_initial_or_threshold method
        hThreshold with
    ⟨η, hηpos, hStepLower⟩
  have hEtaPos : 0 < η := hηpos
  let t : ℝ := min (1 : ℝ) (η / 2)
  have hcNonneg : 0 ≤ η / 2 := by
    nlinarith [hEtaPos]
  refine ⟨β * t / 2, by
    have htpos : 0 < t := by
      dsimp [t]
      exact lt_min zero_lt_one (by nlinarith [hEtaPos])
    exact div_pos (mul_pos hβ.1 htpos) (by norm_num), ?_⟩
  intro k hk hnext
  have hSuff := acceptedTrialPoint_sufficientDecrease method hk hnext
  have hStepPos : 0 < method.initialStepSize k := method.initialStepSize_pos k hk hnext
  have hNormNonneg : 0 ≤ ‖method.reducedGradient k‖ := norm_nonneg _
  let g : ℝ := ‖method.reducedGradient k‖
  let α : ℝ := method.initialStepSize k
  let c : ℝ := η / 2
  let s : ℝ := method.acceptedTrialStepSize k
  have hProdLower : min (α * g) c ≤ s * g := by
    simpa [g, α, c, s] using hStepLower k hk hnext
  have hProdScaled :
      (β / 2) * (g * min (α * g) c) ≤ (s * β * g ^ (2 : ℕ)) / 2 := by
    have hMul :
        g * min (α * g) c ≤ g * (s * g) := by
      exact mul_le_mul_of_nonneg_left hProdLower hNormNonneg
    have hβhalfNonneg : 0 ≤ β / 2 := by
      nlinarith [hβ.1]
    have hScaled :
        (β / 2) * (g * min (α * g) c) ≤
          (β / 2) * (g * (s * g)) :=
      mul_le_mul_of_nonneg_left hMul hβhalfNonneg
    calc
      (β / 2) * (g * min (α * g) c)
          ≤ (β / 2) * (g * (s * g)) := hScaled
      _ = (s * β * g ^ (2 : ℕ)) / 2 := by
        dsimp [g]
        ring
  have hDrop :
      (s * β * g ^ (2 : ℕ)) / 2 ≤
        method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := by
    have hIterateEq :
        method.iterate (k + 1) = method.acceptedTrialPoint k :=
      method.iterate_succ_eq_acceptedTrialPoint k hk hnext
    rw [← hIterateEq] at hSuff
    nlinarith
  have hMinNonneg :
      0 ≤ min (α * g ^ (2 : ℕ)) g := by
    exact le_min (mul_nonneg hStepPos.le (pow_nonneg hNormNonneg _)) hNormNonneg
  have htNonneg : 0 ≤ t := by
    dsimp [t]
    exact le_min (show (0 : ℝ) ≤ 1 by norm_num) hcNonneg
  have htLeOne : t ≤ 1 := by
    dsimp [t]
    exact min_le_left _ _
  have htLeC : t ≤ c := by
    dsimp [t]
    exact min_le_right _ _
  have hMixedLe :
      t * min (α * g ^ (2 : ℕ)) g ≤
        min (α * g ^ (2 : ℕ)) (c * g) := by
    apply le_min
    · calc
        t * min (α * g ^ (2 : ℕ)) g
            ≤ 1 * min (α * g ^ (2 : ℕ)) g := by
              gcongr
        _ = min (α * g ^ (2 : ℕ)) g := by ring
        _ ≤ α * g ^ (2 : ℕ) := min_le_left _ _
    · calc
        t * min (α * g ^ (2 : ℕ)) g
            ≤ c * min (α * g ^ (2 : ℕ)) g := by
              gcongr
        _ ≤ c * g := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) hcNonneg
  have hRewriteMin :
      min (α * g ^ (2 : ℕ)) (c * g) = g * min (α * g) c := by
    rw [mul_min_of_nonneg _ _ hNormNonneg]
    have hLeft : α * g ^ (2 : ℕ) = g * (α * g) := by ring
    have hRight : c * g = g * c := by ring
    rw [hLeft, hRight]
  calc
    (β * t / 2) * min (method.initialStepSize k * ‖method.reducedGradient k‖ ^ (2 : ℕ))
        (‖method.reducedGradient k‖)
        = (β / 2) * (t * min (α * g ^ (2 : ℕ)) g) := by
            dsimp [t, α, g]
            ring
    _ ≤ (β / 2) * min (α * g ^ (2 : ℕ)) (c * g) := by
      exact mul_le_mul_of_nonneg_left hMixedLe (by nlinarith [hβ.1])
    _ = (β / 2) * (g * min (α * g) c) := by rw [hRewriteMin]
    _ ≤ (s * β * g ^ (2 : ℕ)) / 2 := hProdScaled
    _ ≤ method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := hDrop

/-- Helper for Chapter11 Theorem 11.3.2: if the shifted reduced-gradient norms fail to converge
to `0`, then some positive lower bound occurs frequently along the shifted tail. -/
private lemma frequently_shiftedReducedGradientNorm_ge_of_not_tendsto_zero
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hNot :
      ¬ Tendsto (fun i : ℕ ↦ ‖method.reducedGradient (i + 1)‖) atTop (nhds (0 : ℝ))) :
    ∃ ε > 0, ∃ᶠ i : ℕ in atTop, ε ≤ ‖method.reducedGradient (i + 1)‖ := by
  -- Failure of metric convergence to `0` yields a positive lower bound infinitely often.
  rw [Metric.tendsto_nhds] at hNot
  push Not at hNot
  rcases hNot with ⟨ε, hε, hFreq⟩
  refine ⟨ε, hε, ?_⟩
  exact hFreq.mono fun i hi ↦ by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hi

/-- Helper for Chapter11 Theorem 11.3.2: a mixed lower bound
`C * min (a * ‖g̃ₖ‖²) ‖g̃ₖ‖ ≤ f(xₖ) - f(xₖ₊₁)` on the shifted tail forces
`‖g̃ₖ‖ → 0` on the non-`atBot` branch. -/
lemma tendsto_shiftedReducedGradientNorm_zero_of_mixedObjectiveDropLower
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (a : ℝ)
    (ha : a ∈ Set.Ioi (0 : ℝ))
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : method.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → method.active k)
    (hObjective :
      ¬ Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot)
    (hDropLower :
      ∃ C ∈ Set.Ioi (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) →
          C *
              min
                (a * ‖method.reducedGradient k‖ ^ (2 : ℕ))
                (‖method.reducedGradient k‖) ≤
            method.objective (method.iterate k) - method.objective (method.iterate (k + 1))) :
    Tendsto (fun i : ℕ ↦ ‖method.reducedGradient (i + 1)‖) atTop (nhds (0 : ℝ)) := by
  rcases objectiveTailConverges_of_notAtBot
      method hβ hε hNonterminating hObjective with
    ⟨l, hl, _hlower⟩
  rcases hDropLower with ⟨C, hCpos, hDropLower⟩
  let drop : ℕ → ℝ := fun i ↦
    method.objective (method.iterate (i + 1)) - method.objective (method.iterate (i + 2))
  have hDropNonneg : ∀ i, 0 ≤ drop i := by
    intro i
    dsimp [drop]
    exact sub_nonneg.mpr
      (objectiveStrictDecrease_succ method hβ hε hNonterminating i).le
  have hTailObjective :
      Tendsto (fun N : ℕ ↦ method.objective (method.iterate (N + 2))) atTop (nhds l) := by
    -- Shift the convergent tail once more to match the telescoping identity.
    refine Tendsto.congr' ?_ (hl.comp (Filter.tendsto_add_atTop_nat 1))
    exact Filter.Eventually.of_forall fun N ↦ by simp [Nat.add_assoc]
  have hDropSumsShifted :
      Tendsto (fun N : ℕ ↦ Finset.sum (Finset.range (N + 1)) drop) atTop
        (nhds (method.objective (method.iterate 1) - l)) := by
    -- Telescope the shifted finite sums and pass to the limit of the tail objective values.
    have hGapTendsto :
        Tendsto
            (fun N : ℕ ↦
              method.objective (method.iterate 1) -
                method.objective (method.iterate (N + 2)))
            atTop
            (nhds (method.objective (method.iterate 1) - l)) :=
      tendsto_const_nhds.sub hTailObjective
    refine Tendsto.congr' ?_ hGapTendsto
    exact Filter.Eventually.of_forall fun N ↦ (objectiveDropSum_range_eq method N).symm
  have hDropSums :
      Tendsto (fun N : ℕ ↦ Finset.sum (Finset.range N) drop) atTop
        (nhds (method.objective (method.iterate 1) - l)) := by
    -- Remove the harmless one-step shift so `hasSum_iff_tendsto_nat_of_nonneg` applies directly.
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hDropSumsShifted
  have hDropSummable : Summable drop := by
    exact
      ((hasSum_iff_tendsto_nat_of_nonneg hDropNonneg
        (method.objective (method.iterate 1) - l)).2 hDropSums).summable
  let mixedTerm : ℕ → ℝ := fun i ↦
    C *
      min
        (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
        (‖method.reducedGradient (i + 1)‖)
  have hMixedTermNonneg : ∀ i, 0 ≤ mixedTerm i := by
    intro i
    dsimp [mixedTerm]
    have hMinNonneg :
        0 ≤
          min
            (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
            (‖method.reducedGradient (i + 1)‖) := by
      exact le_min
        (mul_nonneg (show 0 ≤ a from (show 0 < a from ha).le) (pow_nonneg (norm_nonneg _) _))
        (norm_nonneg _)
    exact mul_nonneg (show 0 ≤ C from (show 0 < C from hCpos).le) hMinNonneg
  have hMixedTermLe : ∀ i, mixedTerm i ≤ drop i := by
    intro i
    have hi : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
    have hnext : method.active (i + 2) :=
      hNonterminating (i + 2) (Nat.succ_le_succ (Nat.zero_le (i + 1)))
    simpa [mixedTerm, drop] using hDropLower (i + 1) hi hnext
  have hMixedTermSummable : Summable mixedTerm := by
    exact Summable.of_nonneg_of_le hMixedTermNonneg hMixedTermLe hDropSummable
  have hCne : C ≠ 0 := (show 0 < C from hCpos).ne'
  have hMinTermSummable :
      Summable
        (fun i ↦
          min
            (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
            (‖method.reducedGradient (i + 1)‖)) := by
    simpa [mixedTerm, mul_assoc] using
      (summable_mul_left_iff hCne).1 hMixedTermSummable
  have hMinTermTendstoZero :
      Tendsto
          (fun i ↦
            min
              (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
              (‖method.reducedGradient (i + 1)‖))
          atTop
          (nhds (0 : ℝ)) := by
    exact Summable.tendsto_atTop_zero hMinTermSummable
  have hShiftedNorm :
      Tendsto (fun i : ℕ ↦ ‖method.reducedGradient (i + 1)‖) atTop (nhds (0 : ℝ)) := by
    by_contra hNotShifted
    obtain ⟨ε, hεpos, hFreq⟩ :=
      frequently_shiftedReducedGradientNorm_ge_of_not_tendsto_zero method hNotShifted
    let lowerBound : ℝ := min (a * ε ^ (2 : ℕ)) ε
    have hLowerBoundPos : 0 < lowerBound := by
      dsimp [lowerBound]
      exact lt_min (mul_pos (show 0 < a from ha) (pow_pos hεpos _)) hεpos
    have hFreqLower :
        ∃ᶠ i : ℕ in atTop,
          lowerBound ≤
            min
              (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
              (‖method.reducedGradient (i + 1)‖) := by
      refine hFreq.mono fun i hi ↦ ?_
      dsimp [lowerBound]
      have hSqLe :
          a * ε ^ (2 : ℕ) ≤
            a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ) := by
        gcongr
        exact (show 0 ≤ a from (show 0 < a from ha).le)
      exact min_le_min hSqLe hi
    have hEventuallySmall :
        ∀ᶠ i : ℕ in atTop,
          min
              (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
              (‖method.reducedGradient (i + 1)‖) < lowerBound := by
      rw [Metric.tendsto_atTop] at hMinTermTendstoZero
      rcases hMinTermTendstoZero lowerBound hLowerBoundPos with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ⟨N, fun i hi ↦ ?_⟩
      have hNonneg :
          0 ≤
            min
              (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
              (‖method.reducedGradient (i + 1)‖) := by
        exact le_min
          (mul_nonneg (show 0 ≤ a from (show 0 < a from ha).le) (pow_nonneg (norm_nonneg _) _))
          (norm_nonneg _)
      simpa [Real.dist_eq, abs_of_nonneg hNonneg] using hN i hi
    have hEventuallyNotGe :
        ∀ᶠ i : ℕ in atTop,
          ¬ lowerBound ≤
            min
              (a * ‖method.reducedGradient (i + 1)‖ ^ (2 : ℕ))
              (‖method.reducedGradient (i + 1)‖) := by
      exact hEventuallySmall.mono fun i hi hge ↦ not_le.mpr hi hge
    exact hFreqLower hEventuallyNotGe
  exact hShiftedNorm

/-- Chapter11 Theorem 11.3.2: assume that the objective `f(x)` and constraint map `c(x)` of a
generalized reduced-gradient run equipped with the modified Step 7 sufficient-decrease search
data on equality-feasible iterates are twice
continuously differentiable, that the inherited Step 2 inverse-block bound of
`GeneralizedReducedGradientRun.uniformlyBoundedBasicJacobianInverse` holds, and that the Step 3
initial steplengths `α_k⁽⁰⁾` stay positive and have reciprocals `(α_k⁽⁰⁾)⁻¹` uniformly bounded
above on continuing stages, and that the modified Step 7 rule `(11.3.5)` admits one positive
stage-uniform acceptance threshold for sufficiently small products `αₖ,ₗ * ‖g̃ₖ‖`. This
source-facing method owner keeps the Step 6 backtracking data tying the accepted steplength to
`α_k⁽⁰⁾`, and it records the replacement of Step 7 by `(11.3.5)` at the search level rather than
only as an extra inequality on the already accepted trial point. If `method.ε = 0` and the
algorithm does not terminate, then either the reduced-gradient norms satisfy `‖g̃_k‖ → 0` or the
objective values satisfy `f(x_k) → -∞`. -/
theorem tendsto_reducedGradientNorm_zero_or_objective_tendsto_atBot
    (β : ℝ)
    (method : @_root_.GeneralizedReducedGradientSufficientDecreaseMethod basicDim nonbasicDim β)
    (hC2f : ContDiff ℝ 2 method.objective)
    (hC2c : ContDiff ℝ 2 method.constraint)
    (hBoundedABInv :
      GeneralizedReducedGradientRun.uniformlyBoundedBasicJacobianInverse
        (GeneralizedReducedGradientSufficientDecreaseMethod.toRun method))
    (hBoundedAlpha0Inv :
      ∃ C ∈ Set.Ici (0 : ℝ),
        ∀ k, 1 ≤ k → method.active (k + 1) → ‖(method.initialStepSize k)⁻¹‖ ≤ C)
    (hUniformAcceptanceThreshold : method.HasUniformAcceptanceThreshold)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hε : method.ε = 0)
    (hNonterminating : ∀ k, 1 ≤ k → method.active k) :
    Tendsto (fun k : ℕ ↦ ‖method.reducedGradient k‖) atTop (nhds (0 : ℝ)) ∨
      Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot := by
  by_cases hObjective :
      Tendsto (fun k : ℕ ↦ method.objective (method.iterate k)) atTop atBot
  · -- The second alternative is exactly the `atBot` branch.
    exact Or.inr hObjective
  · -- Route correction: use the mixed-drop bridge already proved in this file rather than the
    -- abandoned uniform-accepted-depth route.
    rcases initialStepSize_ge_uniform_of_boundedInverseNorm method hBoundedAlpha0Inv with
      ⟨a, ha, hInitialLower⟩
    have hMixedDrop :=
      GeneralizedReducedGradientSufficientDecreaseMethod.acceptedObjectiveDrop_ge_min_initialMulSq_or_norm
        method hUniformAcceptanceThreshold hβ
    rcases hMixedDrop with
      ⟨C, hCpos, hDropVar⟩
    have hDropFixed :
        ∃ C ∈ Set.Ioi (0 : ℝ),
          ∀ k, 1 ≤ k → method.active (k + 1) →
            C *
                min
                  (a * ‖method.reducedGradient k‖ ^ (2 : ℕ))
                  (‖method.reducedGradient k‖) ≤
              method.objective (method.iterate k) - method.objective (method.iterate (k + 1)) := by
      refine ⟨C, hCpos, ?_⟩
      intro k hk hnext
      -- Freeze the varying Step 3 steplength from the mixed estimate to the fixed lower bound
      -- provided by the reciprocal bound.
      have hMinMono :
          min
              (a * ‖method.reducedGradient k‖ ^ (2 : ℕ))
              (‖method.reducedGradient k‖) ≤
            min
              (method.initialStepSize k * ‖method.reducedGradient k‖ ^ (2 : ℕ))
              (‖method.reducedGradient k‖) := by
        apply min_le_min
        · exact mul_le_mul_of_nonneg_right
            (hInitialLower k hk hnext)
            (pow_nonneg (norm_nonneg _) _)
        · exact le_rfl
      have hScaled :
          C *
              min
                (a * ‖method.reducedGradient k‖ ^ (2 : ℕ))
                (‖method.reducedGradient k‖) ≤
            C *
              min
                (method.initialStepSize k * ‖method.reducedGradient k‖ ^ (2 : ℕ))
                (‖method.reducedGradient k‖) := by
        exact mul_le_mul_of_nonneg_left hMinMono (show 0 ≤ C from hCpos.le)
      exact le_trans hScaled (hDropVar k hk hnext)
    have hShifted :
        Tendsto (fun i : ℕ ↦ ‖method.reducedGradient (i + 1)‖) atTop (nhds (0 : ℝ)) :=
      tendsto_shiftedReducedGradientNorm_zero_of_mixedObjectiveDropLower
        method a ha hβ hε hNonterminating hObjective hDropFixed
    -- Remove the harmless one-step shift to recover the theorem's exact conclusion.
    exact Or.inl ((Filter.tendsto_add_atTop_iff_nat 1).mp hShifted)

end GeneralizedReducedGradientMethod

end Chapter11Theorem1132
