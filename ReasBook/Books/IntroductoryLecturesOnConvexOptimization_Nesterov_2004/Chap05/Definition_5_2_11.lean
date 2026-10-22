/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.2.11 lies in the Chapter 5 strongly-convex multistage-acceleration domain.

Sampled owner declarations:
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the chapter owner for the source
  threshold index `k_p`;
* `conjugateGradientTrajectory` in `Chap01/Definition_1_9_3`, the chapter pattern where a
  recursive orbit is the owner and pointwise formulas are derived API;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern for first natural-number stopping stages expressed through `IsLeast`;
* `IsFirstStrongConvexAcceleratedCubicNewtonQuadraticRegionIndex` in `Chap04/Text_4_2_13`, the
  nearby Chapter 4 first-entry predicate for a multistage orbit.

Best owner abstraction:
* source-facing: the recursive outer-stage orbit `(y_k)` together with the source predicate that
  `T` is the first stage whose output lies in `Q_f`;
* core/canonical: the recursive orbit and `IsLeast` on the hit set `{n | y_n ∈ Q_f}`;
* bridge/view: the pointwise recursion formulas and the unpacking of the first-entry predicate as
  membership at `T` plus failure at all earlier stages.

Primitive data:
* the stage-length schedule `t_{k+1}`;
* the recursive outer orbit generated from `x₀` by the prescribed stage lengths.

Derived API:
* the total number of lower-level iterations performed through a given number of stages;
* the source first-stopping-stage predicate;
* entry at the stopping stage and non-entry at all earlier stages;
* positivity of the stopping stage when `x₀ ∉ Q_f`.

The previous bundled `StronglyConvexMultiStageAccelerationScheme` stored both the orbit and the
least stopping index as primitive public data. Those are canonical from the schedule and `IsLeast`
view, so this refinement keeps the recursive orbit as the owner and moves the first-entry notion
to the canonical least-stage predicate. -/

/-- The stage length `t_{k+1}` used at zero-based outer stage `k` in the multistage acceleration
schedule, namely `⌈k_p / 2^{k / (2p)}⌉`. -/
def stronglyConvexMultiStageAccelerationStageLength
    (kp : ℕ) (p : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))

namespace StronglyConvexMultiStageAccelerationNotation

/- Source-facing notation for the textbook stage length `t_k`, with the ambient threshold index
`k_p` and exponent `p` explicit because they are not inferable from `k` alone. -/
scoped notation:max "t[" kp:arg "; " p:arg "]" =>
  stronglyConvexMultiStageAccelerationStageLength kp p

end StronglyConvexMultiStageAccelerationNotation

open scoped StronglyConvexMultiStageAccelerationNotation

-- Proof sketch: if `kp ≥ 1`, then the real-valued stage-length expression is strictly positive,
-- so its ceiling is at least `1`.
/-- Positive threshold indices produce positive stage lengths throughout the multistage schedule. -/
theorem one_le_stronglyConvexMultiStageAccelerationStageLength
    {kp : ℕ} (hkp : 1 ≤ kp) (p : ℝ) (k : ℕ) :
    1 ≤ t[kp; p] k := by
  change 1 ≤ Nat.ceil ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))
  rw [Nat.one_le_ceil_iff]
  have hkp' : (0 : ℝ) < kp := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hkp
  have hrpow : 0 < Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)) :=
    Real.rpow_pos_of_pos zero_lt_two _
  exact div_pos hkp' hrpow

/-- The total number of lower-level iterations performed during the first `T` stages of the
multistage strategy. -/
def stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
    (kp : ℕ) (p : ℝ) (T : ℕ) : ℕ :=
  Finset.sum (Finset.range T) fun k ↦ t[kp; p] k

/-- The outer-stage orbit `(y_k)` of the multistage strategy `(5.2.28)`, started at `x₀` and
updated by running the inner method for the scheduled stage length
`⌈k_p / 2^{k / (2p)}⌉` at each stage. -/
def stronglyConvexMultiStageAccelerationOrbit
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      innerIterate (t[kp; p] k)
        (stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0 k)

namespace StronglyConvexMultiStageAccelerationNotation

/-- Source-facing notation for the textbook outer-stage iterate `y_k` of the multistage strategy
`(5.2.28)`, with the ambient update map and schedule parameters explicit because they are not
inferable from `k` alone. -/
scoped notation:max "y[" innerIterate:arg " | " kp:arg "; " p:arg "; " x0:arg "]" =>
  stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0

end StronglyConvexMultiStageAccelerationNotation

/-- The multistage outer orbit starts at the prescribed point `x₀`. -/
@[simp] theorem stronglyConvexMultiStageAccelerationOrbit_zero
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) :
    y[innerIterate | kp; p; x0] 0 = x0 :=
  rfl

/-- The successor stage output is obtained by applying the prescribed
`⌈k_p / 2^{k / (2p)}⌉`-step inner run to the previous stage output. -/
@[simp] theorem stronglyConvexMultiStageAccelerationOrbit_succ
    (innerIterate : ℕ → E → E) (kp : ℕ) (p : ℝ) (x0 : E) (k : ℕ) :
    y[innerIterate | kp; p; x0] (k + 1) =
      innerIterate (t[kp; p] k) (y[innerIterate | kp; p; x0] k) :=
  rfl

/-- Definition 5.2.11: `T` is the stopping stage of the multistage acceleration strategy
`(5.2.28)` when `T` is the first outer-stage index whose output lies in the terminal region
`Q_f`. -/
def IsStronglyConvexMultiStageAccelerationStoppingStage
    (innerIterate : ℕ → E → E) (Qf : Set E) (kp : ℕ) (p : ℝ) (x0 : E) (T : ℕ) : Prop :=
  IsLeast {n : ℕ | y[innerIterate | kp; p; x0] n ∈ Qf} T

/-- Expanding `IsStronglyConvexMultiStageAccelerationStoppingStage ... T` says exactly that the
outer orbit enters `Q_f` at stage `T` and not at any earlier stage. -/
@[simp] theorem isStronglyConvexMultiStageAccelerationStoppingStage_iff
    (innerIterate : ℕ → E → E) (Qf : Set E) (kp : ℕ) (p : ℝ) (x0 : E) (T : ℕ) :
    IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T ↔
      y[innerIterate | kp; p; x0] T ∈ Qf ∧
        ∀ m : ℕ, m < T → y[innerIterate | kp; p; x0] m ∉ Qf := by
  change
    IsLeast
      {n : ℕ | y[innerIterate | kp; p; x0] n ∈ Qf}
      T ↔
        y[innerIterate | kp; p; x0] T ∈ Qf ∧
          ∀ m : ℕ, m < T → y[innerIterate | kp; p; x0] m ∉ Qf
  constructor
  · rintro ⟨hT, hleast⟩
    refine ⟨hT, fun m hm hmQf ↦ ?_⟩
    exact (not_le_of_gt hm) (hleast hmQf)
  · rintro ⟨hT, hlt⟩
    refine ⟨hT, fun m hm ↦ le_of_not_gt fun hmT ↦ ?_⟩
    exact hlt m hmT hm

/-- The stopping-stage output lies in the terminal region `Q_f`. -/
theorem stronglyConvexMultiStageAccelerationStoppingStage_mem
    {innerIterate : ℕ → E → E} {Qf : Set E} {kp : ℕ} {p : ℝ} {x0 : E} {T : ℕ}
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T) :
    y[innerIterate | kp; p; x0] T ∈ Qf :=
  hT.1

section

variable {innerIterate : ℕ → E → E} {Qf : Set E} {kp T k : ℕ} {p : ℝ} {x0 : E}

/-- Every stage strictly before a stopping stage lies outside the terminal region `Q_f`. -/
theorem stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T)
    (hk : k < T) :
    y[innerIterate | kp; p; x0] k ∉ Qf := by
  intro hkQf
  exact Nat.not_le_of_lt hk <| hT.2 hkQf

/-- If the initial point lies outside `Q_f`, then every stopping stage is positive. -/
theorem one_le_of_isStronglyConvexMultiStageAccelerationStoppingStage_of_initial_not_mem
    (hT : IsStronglyConvexMultiStageAccelerationStoppingStage innerIterate Qf kp p x0 T)
    (hx0 : x0 ∉ Qf) :
    1 ≤ T := by
  refine Nat.succ_le_of_lt <| Nat.pos_of_ne_zero fun hzero ↦ ?_
  have hmem : y[innerIterate | kp; p; x0] 0 ∈ Qf := by
    simpa [hzero] using stronglyConvexMultiStageAccelerationStoppingStage_mem hT
  exact hx0 <| by simpa using hmem

end
