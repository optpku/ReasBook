/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

section

variable {n : ℕ}

/-- The ambient space `ℝ^n` used by the watchdog method. -/
abbrev WatchdogPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

local notation "Point" => WatchdogPoint n

-- Semantic recall: `lean_leansearch` did not surface a canonical mathlib owner for the SQP
-- watchdog loop in this item. Nearby Chapter 12 algorithm files package such methods as
-- explicit iterate, line-search, and update data, so this file follows the same owner shape.

/-- The watchdog method alternates between the standard line search and the relaxed line
search. -/
inductive WatchdogLineSearchType
  | standard
  | relaxed
  deriving DecidableEq, Repr

/-- Step 3 selects the relaxed line search exactly when the source criterion `(12.5.6)` holds,
and otherwise selects the standard line search. -/
noncomputable def watchdogNextLineSearchType
    (relaxedCriterion : Prop) : WatchdogLineSearchType := by
  classical
  exact if relaxedCriterion then .relaxed else .standard

/-- If the Step-3 relaxed criterion holds, then the next line-search type is `relaxed`. -/
theorem watchdogNextLineSearchType_eq_relaxed
    {relaxedCriterion : Prop} (hrelaxed : relaxedCriterion) :
    watchdogNextLineSearchType relaxedCriterion = WatchdogLineSearchType.relaxed := by
  classical
  simp [watchdogNextLineSearchType, hrelaxed]

/-- If the Step-3 relaxed criterion fails, then the next line-search type is `standard`. -/
theorem watchdogNextLineSearchType_eq_standard
    {relaxedCriterion : Prop} (hstandard : ¬ relaxedCriterion) :
    watchdogNextLineSearchType relaxedCriterion = WatchdogLineSearchType.standard := by
  classical
  simp [watchdogNextLineSearchType, hstandard]

/-- The Step-2 trial point obtained from the current iterate `x`, direction `d`, and accepted
step size `α` is `x + α d`. -/
def watchdogTrialPoint
    (x d : Point) (α : ℝ) : Point :=
  x + α • d

/-- Unfolding `watchdogTrialPoint x d α` gives the Step-2 formula `x + α d`. -/
theorem watchdogTrialPoint_eq
    (x d : Point) (α : ℝ) :
    watchdogTrialPoint x d α = x + α • d := rfl

/-- Step 4 updates the watchdog index `l` to `k + 1` exactly when the trial point improves the
penalty value `Pσ`; otherwise the current index `l` is kept. -/
noncomputable def watchdogCandidateIndex
    (penaltyFunction : Point → ℝ) (iterate : ℕ → Point)
    (l k : ℕ) (trialPoint : Point) : ℕ :=
  if penaltyFunction trialPoint ≤ penaltyFunction (iterate l) then k + 1 else l

/-- Unfolding `watchdogCandidateIndex penaltyFunction iterate l k trialPoint` gives the Step-4
watchdog-index update rule. -/
theorem watchdogCandidateIndex_eq
    (penaltyFunction : Point → ℝ) (iterate : ℕ → Point)
    (l k : ℕ) (trialPoint : Point) :
    watchdogCandidateIndex penaltyFunction iterate l k trialPoint =
      if penaltyFunction trialPoint ≤ penaltyFunction (iterate l) then k + 1 else l := rfl

/-- Step 5 keeps the trial point when the watchdog window has not expired and otherwise resets
`x_(k + 1)` to the stored watchdog iterate `x_l`. -/
def watchdogNextIterate
    (iterate : ℕ → Point) (trialPoint : Point)
    (candidateIndex watchdogWindow k : ℕ) : Point :=
  if k < candidateIndex + watchdogWindow then trialPoint else iterate candidateIndex

/-- Unfolding `watchdogNextIterate iterate trialPoint candidateIndex watchdogWindow k` gives the
Step-5 iterate update rule. -/
theorem watchdogNextIterate_eq
    (iterate : ℕ → Point) (trialPoint : Point)
    (candidateIndex watchdogWindow k : ℕ) :
    watchdogNextIterate iterate trialPoint candidateIndex watchdogWindow k =
      if k < candidateIndex + watchdogWindow then trialPoint else iterate candidateIndex := rfl

/-- Step 5 keeps the updated watchdog index from Step 4 when the watchdog window has not
expired and otherwise resets `l` to `k + 1`. -/
def watchdogNextIndex
    (candidateIndex watchdogWindow k : ℕ) : ℕ :=
  if k < candidateIndex + watchdogWindow then candidateIndex else k + 1

/-- Unfolding `watchdogNextIndex candidateIndex watchdogWindow k` gives the Step-5
watchdog-index update rule. -/
theorem watchdogNextIndex_eq
    (candidateIndex watchdogWindow k : ℕ) :
    watchdogNextIndex candidateIndex watchdogWindow k =
      if k < candidateIndex + watchdogWindow then candidateIndex else k + 1 := rfl

/-- Chapter12 Algorithm 12.5.1: the watchdog method records a penalty function `Pσ`, an initial
point `x₁ : ℝ^n`, a positive watchdog window `n̄`, the current iterate sequence `x_k`, trial
points `x_k + α_k d_k`, search directions `d_k`, step sizes `α_k > 0`, the line-search type
(`standard` or `relaxed`), and the watchdog index `l`. Step 1 starts with standard line search
and `k = l = 1`. At each stage `k ≥ 1`, Step 2 chooses `d_k`, carries out the selected line
search to obtain `α_k > 0`, and forms the trial point `x_k + α_k d_k`. Step 3 sets the next
line-search type to `relaxed` when `(12.5.6)` holds and to `standard` otherwise. Step 4 updates
`l` to `k + 1` when `Pσ (x_(k + 1)) ≤ Pσ (x_l)`. Step 5 keeps the trial point while
`k < l + n̄` and otherwise resets `x_(k + 1)` to `x_l` and `l` to `k + 1`. Step 6 stops when
the chosen convergence criterion is satisfied. -/
structure WatchdogMethod (n : ℕ) where
  penaltyFunction : WatchdogPoint n → ℝ
  lineSearch (searchType : WatchdogLineSearchType)
      (x d : WatchdogPoint n) (α : ℝ) : Prop
  relaxedCriterion : ℕ → Prop
  terminationCriterion : ℕ → Prop
  watchdogWindow : ℕ
  initialPoint : WatchdogPoint n
  iterate : ℕ → WatchdogPoint n
  trialIterate : ℕ → WatchdogPoint n
  direction : ℕ → WatchdogPoint n
  stepSize : ℕ → ℝ
  lineSearchType : ℕ → WatchdogLineSearchType
  watchdogIndex : ℕ → ℕ
  candidateWatchdogIndex : ℕ → ℕ
  watchdogWindow_pos : 0 < watchdogWindow
  iterate_one : iterate 1 = initialPoint
  lineSearchType_one : lineSearchType 1 = WatchdogLineSearchType.standard
  watchdogIndex_one : watchdogIndex 1 = 1
  stepSize_pos (k : ℕ) (hk : 1 ≤ k) : 0 < stepSize k
  lineSearch_spec (k : ℕ) (hk : 1 ≤ k) :
    lineSearch (lineSearchType k) (iterate k) (direction k) (stepSize k)
  trialIterate_eq (k : ℕ) (hk : 1 ≤ k) :
    trialIterate k = watchdogTrialPoint (iterate k) (direction k) (stepSize k)
  lineSearchType_succ_relaxed (k : ℕ) (hk : 1 ≤ k) (hrelaxed : relaxedCriterion k) :
    lineSearchType (k + 1) = WatchdogLineSearchType.relaxed
  lineSearchType_succ_standard (k : ℕ) (hk : 1 ≤ k) (hstandard : ¬ relaxedCriterion k) :
    lineSearchType (k + 1) = WatchdogLineSearchType.standard
  candidateWatchdogIndex_eq (k : ℕ) (hk : 1 ≤ k) :
    candidateWatchdogIndex k =
      watchdogCandidateIndex
        penaltyFunction
        iterate
        (watchdogIndex k)
        k
        (trialIterate k)
  iterate_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    iterate (k + 1) =
      watchdogNextIterate
        iterate
        (trialIterate k)
        (candidateWatchdogIndex k)
        watchdogWindow
        k
  watchdogIndex_succ_eq (k : ℕ) (hk : 1 ≤ k) :
    watchdogIndex (k + 1) =
      watchdogNextIndex
        (candidateWatchdogIndex k)
        watchdogWindow
        k

namespace WatchdogMethod

/-- A `WatchdogMethod` coerces to its recorded iterate sequence `k ↦ x_k`. -/
instance : CoeFun (WatchdogMethod n) (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- The recorded Step-2 trial point at stage `k` is `method.trialIterate k`. -/
def trialPointAt
    (method : WatchdogMethod n) (k : ℕ) : Point :=
  method.trialIterate k

/-- The stored watchdog iterate at stage `k` is the iterate indexed by the current watchdog
index `l`. -/
def storedIterateAt
    (method : WatchdogMethod n) (k : ℕ) : Point :=
  method.iterate (method.watchdogIndex k)

/-- The recorded Step-2 line-search acceptance test at stage `k` uses the current line-search
type, iterate, direction, and step size. -/
def lineSearchAcceptedAt
    (method : WatchdogMethod n) (k : ℕ) : Prop :=
  method.lineSearch
    (method.lineSearchType k)
    (method.iterate k)
    (method.direction k)
    (method.stepSize k)

/-- The Step-6 stopping test at stage `k` is the recorded convergence criterion. -/
def terminatedAt
    (method : WatchdogMethod n) (k : ℕ) : Prop :=
  method.terminationCriterion k

/-- If `k ≥ 1`, the recorded Step-2 trial point is `x_k + α_k d_k`. -/
theorem trialPointAt_eq
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.trialPointAt k =
      watchdogTrialPoint (method.iterate k) (method.direction k) (method.stepSize k) :=
  method.trialIterate_eq k hk

/-- Unfolding `method.storedIterateAt k` gives the iterate `x_l` at the current watchdog
index `l = method.watchdogIndex k`. -/
theorem storedIterateAt_eq
    (method : WatchdogMethod n) (k : ℕ) :
    method.storedIterateAt k = method.iterate (method.watchdogIndex k) := rfl

/-- Unfolding `method.lineSearchAcceptedAt k` gives the recorded Step-2 line-search acceptance
test. -/
theorem lineSearchAcceptedAt_iff
    (method : WatchdogMethod n) (k : ℕ) :
    method.lineSearchAcceptedAt k ↔
      method.lineSearch
        (method.lineSearchType k)
        (method.iterate k)
        (method.direction k)
        (method.stepSize k) := Iff.rfl

/-- If `k ≥ 1`, the recorded Step-2 line search accepts the current step size `α_k` using the
current line-search type. -/
theorem lineSearchAt
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.lineSearchAcceptedAt k :=
  method.lineSearch_spec k hk

/-- If `k ≥ 1`, Step 3 sets the next line-search type by the source update rule attached to
`(12.5.6)`. -/
theorem lineSearchType_succ_eq
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.lineSearchType (k + 1) =
      watchdogNextLineSearchType (method.relaxedCriterion k) := by
  by_cases hrelaxed : method.relaxedCriterion k
  · rw [method.lineSearchType_succ_relaxed k hk hrelaxed]
    exact (watchdogNextLineSearchType_eq_relaxed hrelaxed).symm
  · rw [method.lineSearchType_succ_standard k hk hrelaxed]
    exact (watchdogNextLineSearchType_eq_standard hrelaxed).symm

/-- If `k ≥ 1` and `(12.5.6)` holds at stage `k`, then the next line-search type is
`relaxed`. -/
theorem lineSearchType_succ_eq_relaxed
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hrelaxed : method.relaxedCriterion k) :
    method.lineSearchType (k + 1) = WatchdogLineSearchType.relaxed :=
  method.lineSearchType_succ_relaxed k hk hrelaxed

/-- If `k ≥ 1` and `(12.5.6)` fails at stage `k`, then the next line-search type is
`standard`. -/
theorem lineSearchType_succ_eq_standard
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hstandard : ¬ method.relaxedCriterion k) :
    method.lineSearchType (k + 1) = WatchdogLineSearchType.standard :=
  method.lineSearchType_succ_standard k hk hstandard

/-- If `k ≥ 1`, the Step-4 watchdog-index update is given by the penalty comparison with the
current stored watchdog iterate. -/
theorem candidateWatchdogIndexAt_eq
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.candidateWatchdogIndex k =
      watchdogCandidateIndex
        method.penaltyFunction
        method.iterate
        (method.watchdogIndex k)
        k
        (method.trialPointAt k) :=
  method.candidateWatchdogIndex_eq k hk

/-- If `k ≥ 1`, Step 4 updates the candidate watchdog index by the textbook penalty-test
comparison. -/
theorem candidateWatchdogIndexAt_eq_ite
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.candidateWatchdogIndex k =
      if method.penaltyFunction (method.trialPointAt k) ≤
          method.penaltyFunction (method.storedIterateAt k) then
        k + 1
      else
        method.watchdogIndex k := by
  rw [method.candidateWatchdogIndexAt_eq k hk, watchdogCandidateIndex_eq]
  simp [WatchdogMethod.storedIterateAt]

/-- If `k ≥ 1` and the Step-4 penalty test succeeds, then the candidate watchdog index is
updated to `k + 1`. -/
theorem candidateWatchdogIndex_eq_succ_of_penalty_le
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hpenalty :
      method.penaltyFunction (method.trialPointAt k) ≤
        method.penaltyFunction (method.storedIterateAt k)) :
    method.candidateWatchdogIndex k = k + 1 := by
  rw [method.candidateWatchdogIndexAt_eq_ite k hk]
  simp [hpenalty]

/-- If `k ≥ 1` and the Step-4 penalty test fails, then the current watchdog index is kept. -/
theorem candidateWatchdogIndex_eq_watchdogIndex_of_not_penalty_le
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hpenalty :
      ¬ method.penaltyFunction (method.trialPointAt k) ≤
        method.penaltyFunction (method.storedIterateAt k)) :
    method.candidateWatchdogIndex k = method.watchdogIndex k := by
  rw [method.candidateWatchdogIndexAt_eq_ite k hk]
  simp [hpenalty]

/-- If `k ≥ 1`, the final iterate update after Step 5 is given by the watchdog acceptance or
reset rule. -/
theorem iterate_succ_eq_watchdogNextIterate
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.iterate (k + 1) =
      watchdogNextIterate
        method.iterate
        (method.trialPointAt k)
        (method.candidateWatchdogIndex k)
        method.watchdogWindow
        k :=
  method.iterate_succ_eq k hk

/-- If `k ≥ 1`, Step 5 updates `x_(k + 1)` by the textbook watchdog-window `if` rule. -/
theorem iterate_succ_eq_ite
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.iterate (k + 1) =
      if k < method.candidateWatchdogIndex k + method.watchdogWindow then
        method.trialPointAt k
      else
        method.iterate (method.candidateWatchdogIndex k) := by
  rw [method.iterate_succ_eq_watchdogNextIterate k hk, watchdogNextIterate_eq]

/-- If `k ≥ 1` and the Step-5 watchdog window has not expired, then the next iterate keeps the
trial point. -/
theorem iterate_succ_eq_trialPointAt_of_lt_watchdogWindow
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hwindow : k < method.candidateWatchdogIndex k + method.watchdogWindow) :
    method.iterate (k + 1) = method.trialPointAt k := by
  rw [method.iterate_succ_eq_ite k hk]
  simp [hwindow]

/-- If `k ≥ 1`, Step 5 updates the stored watchdog index by the textbook watchdog-window
`if` rule. -/
theorem watchdogIndex_succ_eq_ite
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k) :
    method.watchdogIndex (k + 1) =
      if k < method.candidateWatchdogIndex k + method.watchdogWindow then
        method.candidateWatchdogIndex k
      else
        k + 1 := by
  rw [method.watchdogIndex_succ_eq k hk, watchdogNextIndex_eq]

/-- If `k ≥ 1` and the Step-5 watchdog window has not expired, then the watchdog index keeps
the Step-4 update. -/
theorem watchdogIndex_succ_eq_candidateWatchdogIndex_of_lt_watchdogWindow
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hwindow : k < method.candidateWatchdogIndex k + method.watchdogWindow) :
    method.watchdogIndex (k + 1) = method.candidateWatchdogIndex k := by
  rw [method.watchdogIndex_succ_eq_ite k hk]
  simp [hwindow]

/-- If `k ≥ 1` and the Step-5 watchdog window has expired, then the next iterate resets to the
stored watchdog iterate indexed by the Step-4 candidate. -/
theorem iterate_succ_eq_iterate_candidateWatchdogIndex_of_not_lt_watchdogWindow
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hwindow : ¬ k < method.candidateWatchdogIndex k + method.watchdogWindow) :
    method.iterate (k + 1) = method.iterate (method.candidateWatchdogIndex k) := by
  rw [method.iterate_succ_eq_ite k hk]
  simp [hwindow]

/-- If `k ≥ 1` and the Step-5 watchdog window has expired, then the watchdog index resets to
`k + 1`. -/
theorem watchdogIndex_succ_eq_succ_of_not_lt_watchdogWindow
    (method : WatchdogMethod n) (k : ℕ) (hk : 1 ≤ k)
    (hwindow : ¬ k < method.candidateWatchdogIndex k + method.watchdogWindow) :
    method.watchdogIndex (k + 1) = k + 1 := by
  rw [method.watchdogIndex_succ_eq_ite k hk]
  simp [hwindow]

/-- Unfolding `method.terminatedAt k` gives the recorded Step-6 convergence test. -/
theorem terminatedAt_iff
    (method : WatchdogMethod n) (k : ℕ) :
    method.terminatedAt k ↔ method.terminationCriterion k := Iff.rfl

end WatchdogMethod

end
