/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_49
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_51
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

local notation "E(" n ")" => EuclideanSpace ℝ (Fin n)

/- Primary domain: iterative midpoint-bisection feasibility oracles with stored separating cuts.

Relevant owner-style declarations sampled before refinement:
- `zeroOneBox` in `Definition_1_3_1`, which uses the chapter's canonical owner presentation of a
  Euclidean coordinate box through intrinsic coordinatewise interval conditions;
- `cuttingHalfspace` in `Definition_3_49` and `SeparatesByCuttingVector.subset_affineSublevelSet`
  in `Definition_3_51` for the chapter's retained half-space cut `0 ≤ ⟪g, x̄ - z⟫`;
- `IsMidpointCoordinateBisectionStep` in `Proposition_3_43` for midpoint box-splitting geometry.

Source/core/bridge triage:
- `source-facing`: the resisting-oracle transcript and the step relation of Algorithm 3.5;
- `core/canonical`: the intrinsic coordinate-box owner
  `∀ i, a i ≤ x i ∧ x i ≤ b i`,
  `SeparatesByCuttingVector` / `cuttingHalfspace` for outside-box feasibility separation, and
  `IsMidpointCoordinateBisectionStep` for current-box refinement;
- `bridge/view`: the derived accessors for realized boxes, centers, and stored separators, together
  with the strict-cutting companion implication from `SeparatesByCuttingVector`.

Primitive data:
- only the realized recursive split transcript.

Derived API:
- the realized boxes `B₀, …, B_m`, centers, stored separators `g₀, …, g_{m-1}`, the current split
  coordinate, the outside-box retained half-space condition, and the midpoint-bisection bridge
  theorems.

Accordingly, this file keeps the source-facing recursive oracle transcript and derives all box and
separator data from it, while representing each realized box through the chapter's intrinsic
coordinatewise interval owner rather than a parallel transport-based box API. -/

/-- The initial box `[-R \bar e_n, R \bar e_n]`. -/
def initialFeasibilityBox (n : ℕ) (R : ℝ) : Set (E(n)) :=
  {x | ∀ i : Fin n, x i ∈ Set.Icc (-R) R}

/-- The recursively generated transcript of midpoint-split choices made by the resisting
feasibility oracle. All realized boxes and stored separators are derived from this transcript. -/
inductive FeasibilityResistingOracleState (n : ℕ) where
  /-- The initial transcript, containing only the initial box `[-R \bar e_n, R \bar e_n]`. -/
  | initial : FeasibilityResistingOracleState n
  /-- The transcript extended by the branch that keeps the lower half of the current coordinate
  interval. -/
  | keepLowerHalf : FeasibilityResistingOracleState n → FeasibilityResistingOracleState n
  /-- The transcript extended by the branch that keeps the upper half of the current coordinate
  interval. -/
  | keepUpperHalf : FeasibilityResistingOracleState n → FeasibilityResistingOracleState n

namespace FeasibilityResistingOracleState

variable {n : ℕ}

/-- The number `m` of realized midpoint splits stored in the transcript. -/
def depth : FeasibilityResistingOracleState n → ℕ
  | .initial => 0
  | .keepLowerHalf state => state.depth + 1
  | .keepUpperHalf state => state.depth + 1

/-- The cyclic coordinate update `i := i + 1`, resetting to the first coordinate after the last
one. The textbook's one-based counter is represented here by zero-based `Fin n` indices. -/
def nextCoordinateIndex (hn : 0 < n) (i : Fin n) : Fin n :=
  by
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact i + 1

/-- The coordinate selected for the next midpoint split. -/
def nextCoord (hn : 0 < n) : FeasibilityResistingOracleState n → Fin n
  | .initial => ⟨0, hn⟩
  | .keepLowerHalf state => nextCoordinateIndex hn (state.nextCoord hn)
  | .keepUpperHalf state => nextCoordinateIndex hn (state.nextCoord hn)

/-- The currently stored cutting vector, namely the selected coordinate direction. -/
def splitDirection (hn : 0 < n) (state : FeasibilityResistingOracleState n) : E(n) :=
  EuclideanSpace.single (state.nextCoord hn) 1

private structure BoxBounds (n : ℕ) where
  lower : Fin n → ℝ
  upper : Fin n → ℝ

/-- The current lower and upper corners of the realized box `B_m`. -/
private def currentBounds (R : ℝ) (hn : 0 < n) : FeasibilityResistingOracleState n → BoxBounds n
  | .initial =>
      { lower := fun _ ↦ -R
        upper := fun _ ↦ R }
  | .keepLowerHalf state =>
      let bounds := state.currentBounds R hn
      let splitCoord := state.nextCoord hn
      let splitMidpoint := midpoint ℝ bounds.lower bounds.upper splitCoord
      { lower := bounds.lower
        upper := Function.update bounds.upper splitCoord splitMidpoint }
  | .keepUpperHalf state =>
      let bounds := state.currentBounds R hn
      let splitCoord := state.nextCoord hn
      let splitMidpoint := midpoint ℝ bounds.lower bounds.upper splitCoord
      { lower := Function.update bounds.lower splitCoord splitMidpoint
        upper := bounds.upper }

/-- The lower corner of the current box `B_m`. -/
def currentLower
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) : Fin n → ℝ :=
  (state.currentBounds R hn).lower

/-- The upper corner of the current box `B_m`. -/
def currentUpper
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) : Fin n → ℝ :=
  (state.currentBounds R hn).upper

/-- The realized coordinate bounds of each stored box in the transcript. -/
private def realizedBounds (R : ℝ) (hn : 0 < n) :
    (state : FeasibilityResistingOracleState n) → Fin (state.depth + 1) → BoxBounds n
  | .initial => fun _ ↦
      { lower := fun _ ↦ -R
        upper := fun _ ↦ R }
  | .keepLowerHalf state =>
      Fin.lastCases ((keepLowerHalf state).currentBounds R hn) (fun k ↦ state.realizedBounds R hn k)
  | .keepUpperHalf state =>
      Fin.lastCases ((keepUpperHalf state).currentBounds R hn) (fun k ↦ state.realizedBounds R hn k)

/-- The `k`-th realized lower corner stored in the transcript. -/
def lower (R : ℝ) (hn : 0 < n) :
    (state : FeasibilityResistingOracleState n) → Fin (state.depth + 1) → Fin n → ℝ
  | state, k => (state.realizedBounds R hn k).lower

/-- The `k`-th realized upper corner stored in the transcript. -/
def upper (R : ℝ) (hn : 0 < n) :
    (state : FeasibilityResistingOracleState n) → Fin (state.depth + 1) → Fin n → ℝ
  | state, k => (state.realizedBounds R hn k).upper

/-- The `k`-th realized box stored by the oracle transcript. -/
def box (R : ℝ) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) (k : Fin (state.depth + 1)) : Set (E(n)) :=
  {x | ∀ i : Fin n, state.lower R hn k i ≤ x i ∧ x i ≤ state.upper R hn k i}

/-- The center of the `k`-th realized box stored by the oracle transcript. -/
def center (R : ℝ) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) (k : Fin (state.depth + 1)) : E(n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm <| midpoint ℝ (state.lower R hn k) (state.upper R hn k)

/-- The current box `B_m`. -/
def currentBox (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) : Set (E(n)) :=
  state.box R hn (Fin.last state.depth)

/-- The center of the current box `B_m`. -/
def currentCenter
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) : E(n) :=
  state.center R hn (Fin.last state.depth)

/-- The stored separating vector `g_k` associated to the `k`-th midpoint split. -/
def separator (hn : 0 < n) :
    (state : FeasibilityResistingOracleState n) → Fin state.depth → E(n)
  | .initial => Fin.elim0
  | .keepLowerHalf state =>
      Fin.lastCases (state.splitDirection hn) (fun k ↦ state.separator hn k)
  | .keepUpperHalf state =>
      Fin.lastCases (-state.splitDirection hn) (fun k ↦ state.separator hn k)

/-- The index `k` is maximal active when `x` lies in `B_k` and in no later realized box. -/
def maximalActiveBoxIndex
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    (x : E(n)) (k : Fin (state.depth + 1)) : Prop :=
  x ∈ state.box R hn k ∧ ∀ l : Fin (state.depth + 1), k < l → x ∉ state.box R hn l

/-- The initial transcript starts with depth `m = 0`. -/
theorem initial_depth :
    (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n).depth = 0 := rfl

/-- Extending the transcript by the lower-half branch produces exactly the canonical midpoint
coordinate bisection step on the current box. -/
theorem keepLowerHalf_isMidpointCoordinateBisectionStep
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    IsMidpointCoordinateBisectionStep
      (state.currentLower R hn) (state.currentUpper R hn)
      ((keepLowerHalf state).currentLower R hn) ((keepLowerHalf state).currentUpper R hn)
      (state.nextCoord hn) := by
  left
  constructor
  · rfl
  · ext j
    by_cases hj : j = state.nextCoord hn
    · subst j
      simp [currentLower, currentUpper, currentBounds, pi_midpoint_apply, midpoint_eq_smul_add,
        invOf_eq_inv, smul_eq_mul, mul_add]
    · simp [currentLower, currentUpper, currentBounds, hj]

/-- Extending the transcript by the upper-half branch produces exactly the canonical midpoint
coordinate bisection step on the current box. -/
theorem keepUpperHalf_isMidpointCoordinateBisectionStep
    (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    IsMidpointCoordinateBisectionStep
      (state.currentLower R hn) (state.currentUpper R hn)
      ((keepUpperHalf state).currentLower R hn) ((keepUpperHalf state).currentUpper R hn)
      (state.nextCoord hn) := by
  right
  constructor
  · ext j
    by_cases hj : j = state.nextCoord hn
    · subst j
      simp [currentLower, currentUpper, currentBounds, pi_midpoint_apply, midpoint_eq_smul_add,
        invOf_eq_inv, smul_eq_mul, mul_add]
    · simp [currentLower, currentUpper, currentBounds, hj]
  · rfl

end FeasibilityResistingOracleState

open FeasibilityResistingOracleState

/-- Algorithm 3.5: the resisting oracle for the feasibility problem starts from the initialized box
`[-R \bar e_n, R \bar e_n]`, returns any feasibility separator `g` satisfying
`⟪g, x - z⟫ ≥ 0` for all `z ∈ B₀` when the query point `x` lies outside that box, reuses the
stored separator `g_k` for the maximal active box `B_k` with `k < m`, and otherwise splits the
current box `B_m` at the midpoint of the selected coordinate, returning `e_i` when the query lies
in the upper half and `-e_i` when it lies in the lower half, then retaining the opposite half-box
and updating the state by incrementing `m` and cycling the coordinate index. -/
def FeasibilityResistingOracleStep
    {n : ℕ} (R : ℝ) (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    (x g : E(n)) (state' : FeasibilityResistingOracleState n) : Prop :=
  let initialBox := initialFeasibilityBox n R
  let currentBox := state.currentBox R hn
  let splitCoord := state.nextCoord hn
  let splitDirection : E(n) := state.splitDirection hn
  let splitMidpoint := (state.currentCenter R hn) splitCoord
  (x ∉ initialBox ∧
      initialBox ⊆ cuttingHalfspace x g ∧
      state' = state) ∨
    (∃ k : Fin state.depth,
      state.maximalActiveBoxIndex R hn x (Fin.castSucc k) ∧
        g = state.separator hn k ∧
        state' = state) ∨
    (x ∈ currentBox ∧
      splitMidpoint ≤ x splitCoord ∧
      g = splitDirection ∧
      state' = keepLowerHalf state) ∨
    (x ∈ currentBox ∧
      x splitCoord < splitMidpoint ∧
      g = -splitDirection ∧
      state' = keepUpperHalf state)

/-- If the query point lies outside the initial box and that box lies in the retained half-space
`cuttingHalfspace x g` determined by `g`, then Algorithm 3.5 allows the oracle to return
`(g, state)` without changing the state. -/
-- Proof sketch: choose the first disjunct in `FeasibilityResistingOracleStep`.
theorem FeasibilityResistingOracleStep.of_outside_initialBox
    {n : ℕ} {R : ℝ} {hn : 0 < n} {state : FeasibilityResistingOracleState n}
    {x g : E(n)}
    (hx : x ∉ initialFeasibilityBox n R)
    (hg : initialFeasibilityBox n R ⊆ cuttingHalfspace x g) :
    FeasibilityResistingOracleStep R hn state x g state :=
  Or.inl ⟨hx, hg, rfl⟩

/-- The stronger strict cutting-vector predicate from `Definition_3_51` also justifies the
outside-`B₀` branch of Algorithm 3.5. -/
theorem FeasibilityResistingOracleStep.of_outside_initialBox_of_strictCuttingVector
    {n : ℕ} {R : ℝ} {hn : 0 < n} {state : FeasibilityResistingOracleState n}
    {x g : E(n)}
    (hx : x ∉ initialFeasibilityBox n R)
    (hg : SeparatesByCuttingVector (initialFeasibilityBox n R) x g) :
    FeasibilityResistingOracleStep R hn state x g state :=
  FeasibilityResistingOracleStep.of_outside_initialBox hx <|
    hg.subset_cuttingHalfspace
