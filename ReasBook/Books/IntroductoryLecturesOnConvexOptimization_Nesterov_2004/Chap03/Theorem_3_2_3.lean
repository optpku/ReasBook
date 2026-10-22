/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open scoped ConstrainedArgmin WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Theorem 3.2.3 lies in the chapter's whole-space multi-constraint first-order method domain.

Sampled owner declarations:
* `MultipleConstraintFirstOrderProblem` in `Algorithm_3_4`, the chapter owner for a convex
  objective, a finite constraint family, and chosen first-order oracles;
* `FirstOrderOracle.correctionStepsize` in `Definition_3_40`, the canonical owner-derived scalar
  `f_j(x) / ‖g_j(x)‖²` for a violated-constraint correction;
* `MultipleConstraintFirstOrderProblem.iterates` in `Algorithm_3_4`, the canonical owner-level
  recursion for the whole-space method `(3.2.24)`;
* `FunctionalConstraintSubgradientMethod.iterates` in `Algorithm_3_3` and
  `ProjectedMultipleConstraintFirstOrderProblem.switchingIterates` in `Algorithm_3_4`, the nearby
  chapter pattern that keeps the recursive iterate family public instead of packaging it behind a
  second owner;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the Chapter 1
  owner for intrinsic minimum values over a sampled feasible set.

Best owner abstraction:
* source-facing: the recursive iterate family
  `problem.iterates ε x₀ selectedConstraintAt : ℕ → E` for method `(3.2.24)`;
* core/canonical: `MultipleConstraintFirstOrderProblem`,
  `FirstOrderOracle.correctionStepsize`, `NormedSpace.normalize`, and
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: the branch-validity predicate for the chosen indices, the admissible index family
  `𝒜(N)`, the sampled iterate set `𝓕_A(N)`, and the sampled optimal value.

Primitive data:
* the multi-constraint first-order owner `problem`;
* the initial point `x₀`;
* the tolerance `ε`;
* the stepwise branch choices `selectedConstraintAt : ℕ → Option (Fin m)`.

Derived API:
* the recursive iterate family `x₀, x₁, ...`;
* the admissibility predicate `∀ j, f_j(x) ≤ ε`;
* the validity condition saying `none` occurs exactly on admissible iterates and `some j`
  records a violated constraint;
* the textbook admissible family `𝒜(N)`, sampled iterate set `𝓕_A(N)`, and sampled minimum.

This refinement removes the public packaged-method owner entirely. The owner-derived whole-space
step and iterate recursion now live in `Algorithm_3_4`, and the theorem surface here works
directly with that canonical run data to derive the branch equations, `𝒜(N)`, `𝓕_A(N)`, and the
sampled minimum. -/

namespace MultipleConstraintFirstOrderProblem

/-- The admissibility predicate at a point: all constraint inequalities satisfy `f_j(x) ≤ ε`. -/
def IsAdmissible
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x : E) : Prop :=
  ∀ j : Fin m, problem.constraints j x ≤ ε

/-- The chosen branch sequence is valid for method `(3.2.24)` exactly when `none` occurs on
admissible iterates and `some j` records a violated constraint. -/
def IsValidSelection
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) : Prop :=
  ∀ k,
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k)

section Iterates

variable {problem : MultipleConstraintFirstOrderProblem E m}
variable {ε : ℝ} {x0 : E} {selectedConstraintAt : ℕ → Option (Fin m)}

/-- The chosen branch sequence is valid along the recursively generated run. -/
theorem selectedConstraintAt_spec
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) :=
  hvalid k

/-- The branch choice is `none` exactly on admissible iterates. -/
theorem selectedConstraintAt_eq_none_iff
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    selectedConstraintAt k = none ↔
      problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k) := by
  constructor
  · intro hk
    simpa [hk] using problem.selectedConstraintAt_spec hvalid k
  · intro hk
    cases hsel : selectedConstraintAt k with
    | none =>
        rfl
    | some j =>
        have hviol : ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) := by
          simpa [hsel] using problem.selectedConstraintAt_spec hvalid k
        exact (not_lt_of_ge (hk j) hviol).elim

/-- The zeroth iterate is the prescribed initial point `x₀`. -/
@[simp] theorem iterates_zero :
    problem.iterates ε x0 selectedConstraintAt 0 = x0 := by
  rfl

/-- Each successor iterate is obtained from the previous one by the branch rule of
method `(3.2.24)`. -/
@[simp] theorem iterates_succ (k : ℕ) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.step ε (problem.iterates ε x0 selectedConstraintAt k)
        (selectedConstraintAt k) := by
  rfl

/-- At admissible iterates, the successor iterate is the objective step. -/
theorem iterates_succ_eq_objective
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) {k : ℕ}
    (hk : problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.objectiveStep ε (problem.iterates ε x0 selectedConstraintAt k) := by
  have hsel : selectedConstraintAt k = none :=
    (problem.selectedConstraintAt_eq_none_iff hvalid k).2 hk
  rw [iterates_succ, hsel]
  rfl

/-- If the run selects the violated constraint `j` at time `k`, the successor iterate is the
corresponding correction step. -/
theorem iterates_succ_eq_constraint
    {k : ℕ} {j : Fin m} (hsel : selectedConstraintAt k = some j) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.constraintStep j (problem.iterates ε x0 selectedConstraintAt k) := by
  rw [iterates_succ, hsel]
  rfl

/-- The textbook index set `𝒜(N)` of admissible iterates among `x₀, ..., x_N`. -/
def admissibleIndices
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun k ↦
    problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝒜[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIndices problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

open scoped MultipleConstraintFirstOrderProblemNotation

/-- Membership in `𝒜(N)` is equivalent to satisfying all constraint inequalities
`f_j(x_k) ≤ ε`. -/
@[simp] theorem mem_admissibleIndices_iff
    (N : ℕ) {k : Fin (N + 1)} :
    k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ↔
      ∀ j, problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) ≤ ε := by
  simp [admissibleIndices, IsAdmissible]

/-- The textbook set `𝓕_A(N)` of iterates whose indices belong to `𝒜(N)`. -/
def admissibleIterateSet
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Set E :=
  Set.range fun k : {i : Fin (N + 1) // i ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N)} ↦
    problem.iterates ε x0 selectedConstraintAt k.1

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝓕_A[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIterateSet problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

/-- The sampled minimum on `𝓕_A(N)`, expressed through the Chapter 1 constrained optimal-value
owner. -/
def sampledOptimalValue
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) : EReal :=
  (SetConstrainedMinimizationProblem.mk
      (𝓕_A[problem, ε, x0, selectedConstraintAt](N))
      problem.objective).optimalValue

/-- Membership in `𝓕_A(N)` means that the point is one of the iterates `x_k` with
`k ∈ 𝒜(N)`. -/
theorem mem_admissibleIterateSet_iff
    (N : ℕ) {x : E} :
    x ∈ 𝓕_A[problem, ε, x0, selectedConstraintAt](N) ↔
      ∃ k : Fin (N + 1),
        k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ∧
          problem.iterates ε x0 selectedConstraintAt k = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- Any constrained minimizer of the sampled iterate set realizes the owner-level sampled minimum
`f_N^*`. -/
theorem sampledOptimalValue_eq_of_mem_argmin
    (N : ℕ) {x : E}
    (hx : x ∈ argmin[𝓕_A[problem, ε, x0, selectedConstraintAt](N)] problem.objective) :
    problem.sampledOptimalValue ε x0 selectedConstraintAt N = (problem.objective x : EReal) := by
  let sampledProblem : SetConstrainedMinimizationProblem E :=
    .mk (𝓕_A[problem, ε, x0, selectedConstraintAt](N)) problem.objective
  simpa [sampledOptimalValue, sampledProblem] using
    sampledProblem.optimalValue_eq_of_mem_argmin hx

/-- The admissible iterate set is nonempty exactly when the admissible index family `𝒜(N)` is
nonempty. -/
theorem admissibleIterateSet_nonempty_iff
    (N : ℕ) :
    𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ↔
      (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty := by
  constructor
  · intro hSet
    rcases Set.range_nonempty_iff_nonempty.mp
        (Set.nonempty_iff_ne_empty.mpr hSet) with ⟨k⟩
    exact ⟨k.1, k.2⟩
  · rintro ⟨k, hk⟩ hEmpty
    have hx : problem.iterates ε x0 selectedConstraintAt k ∈
        𝓕_A[problem, ε, x0, selectedConstraintAt](N) := by
      exact Set.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    rw [hEmpty] at hx
    exact hx

/-- Helper for Theorem 3.2.3: a canonical constrained argmin witness recovers feasibility of the
comparison point `x*`. -/
theorem feasible_of_mem_constrainedArgmin
    {xStar : E}
    (hxStar :
      xStar ∈ argmin[{x | ∀ j, problem.constraints j x ≤ 0}] problem.objective) :
    ∀ j, problem.constraints j xStar ≤ 0 :=
  (mem_constrainedArgmin_iff.mp hxStar).1

/-- Helper for Theorem 3.2.3: a canonical constrained argmin witness supplies the objective
comparison on all feasible points. -/
theorem objective_le_of_mem_constrainedArgmin
    {xStar x : E}
    (hxStar :
      xStar ∈ argmin[{y | ∀ j, problem.constraints j y ≤ 0}] problem.objective)
    (hx_feasible : ∀ j, problem.constraints j x ≤ 0) :
    problem.objective xStar ≤ problem.objective x := by
  exact (isMinOn_iff.mp (mem_constrainedArgmin_iff.mp hxStar).2) x hx_feasible

/-- Helper for Theorem 3.2.3: the affine support inequality from an oracle-selected subgradient
controls the value gap against any comparison point. -/
lemma value_gap_le_inner_subgradient
    {f : E → ℝ} (oracle : FirstOrderOracle f) {x y : E} :
    f x - f y ≤ inner ℝ (oracle.subgradient x) (x - y) := by
  -- Rewrite the oracle certificate into the real-valued affine support inequality at `x`.
  have hsub := oracle.subgradient_spec x
  rw [IsSubgradientAt.coe_real_iff] at hsub
  have hsuby := hsub y
  have hinner :
      inner ℝ (oracle.subgradient x) (y - x) =
        -inner ℝ (oracle.subgradient x) (x - y) := by
    rw [show y - x = -(x - y) by abel_nf, inner_neg_right]
  rw [hinner] at hsuby
  linarith

/-- Helper for Theorem 3.2.3: a strict interior point of the reference ball has a smaller open
ball neighborhood still contained in the original closed ball. -/
lemma ball_subset_closedBall_of_mem_ball
    {x y : E} {R : ℝ} (hx : x ∈ Metric.ball y R) :
    Metric.ball x (R - dist x y) ⊆ Metric.closedBall y R := by
  intro z hz
  -- Use the triangle inequality with the slack `R - dist x y` coming from strict interiority.
  rw [Metric.mem_closedBall]
  have hx' : dist x y < R := by
    simpa [Metric.mem_ball] using hx
  have hz' : dist z x < R - dist x y := by
    simpa [Metric.mem_ball] using hz
  have htriangle := dist_triangle z x y
  linarith

/-- Helper for Theorem 3.2.3: a strict squared-distance improvement moves the iterate into the
open reference ball. -/
lemma mem_ball_of_norm_sq_lt_norm_sq
    {x0 xStar y : E}
    (hbound : ‖y - xStar‖ ^ (2 : ℕ) < ‖x0 - xStar‖ ^ (2 : ℕ)) :
    y ∈ Metric.ball xStar ‖x0 - xStar‖ := by
  -- Convert the strict squared-norm comparison into the metric open-ball inequality.
  have hnorm_lt : ‖y - xStar‖ < ‖x0 - xStar‖ := by
    nlinarith [hbound, norm_nonneg (y - xStar), norm_nonneg (x0 - xStar)]
  rw [Metric.mem_ball, dist_eq_norm]
  simpa using hnorm_lt

/-- Helper for Theorem 3.2.3: a strict interior iterate inherits the objective-oracle norm bound
from the closed-ball Lipschitz hypothesis. -/
lemma objectiveOracleNorm_le_of_mem_ball
    (xStar : E) (M : NNReal)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    {x : E} (hx : x ∈ Metric.ball xStar ‖x0 - xStar‖) :
    ‖problem.oracle.subgradient x‖ ≤ M := by
  let r : ℝ := ‖x0 - xStar‖ - dist x xStar
  have hr : 0 < r := by
    have hx' : dist x xStar < ‖x0 - xStar‖ := by
      simpa [Metric.mem_ball] using hx
    linarith
  have hsubset :
      Metric.ball x r ⊆ Metric.closedBall xStar ‖x0 - xStar‖ :=
    ball_subset_closedBall_of_mem_ball (x := x) (y := xStar) (R := ‖x0 - xStar‖) hx
  have hdom :
      Metric.ball x r ⊆ dom (fun y : E ↦ (problem.objective y : WithTop ℝ)) := by
    intro y hy
    simp
  have hK :
      LipschitzOnWith M
        (withTopRealPart (fun y : E ↦ (problem.objective y : WithTop ℝ)))
        (Metric.ball x r) := by
    simpa using hf_lipschitz.mono hsubset
  have hsub :
      problem.oracle.subgradient x ∈
        ∂ (fun y : E ↦ (problem.objective y : WithTop ℝ))(x) := by
    simpa using problem.oracle.subgradient_spec x
  -- Apply the chapter-local Lipschitz-ball estimate to the chosen objective subgradient.
  simpa [r] using
    norm_le_of_mem_subdifferential_of_lipschitz_ball hr hdom hK hsub

/-- Helper for Theorem 3.2.3: a strict interior iterate inherits the selected-constraint oracle
norm bound from the closed-ball Lipschitz hypothesis. -/
lemma constraintOracleNorm_le_of_mem_ball
    (xStar : E) (M : NNReal)
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    {j : Fin m} {x : E} (hx : x ∈ Metric.ball xStar ‖x0 - xStar‖) :
    ‖(problem.constraintOracle j).subgradient x‖ ≤ M := by
  let r : ℝ := ‖x0 - xStar‖ - dist x xStar
  have hr : 0 < r := by
    have hx' : dist x xStar < ‖x0 - xStar‖ := by
      simpa [Metric.mem_ball] using hx
    linarith
  have hsubset :
      Metric.ball x r ⊆ Metric.closedBall xStar ‖x0 - xStar‖ :=
    ball_subset_closedBall_of_mem_ball (x := x) (y := xStar) (R := ‖x0 - xStar‖) hx
  have hdom :
      Metric.ball x r ⊆ dom (fun y : E ↦ (problem.constraints j y : WithTop ℝ)) := by
    intro y hy
    simp
  have hK :
      LipschitzOnWith M
        (withTopRealPart (fun y : E ↦ (problem.constraints j y : WithTop ℝ)))
        (Metric.ball x r) := by
    simpa using (hconstraints_lipschitz j).mono hsubset
  have hsub :
      (problem.constraintOracle j).subgradient x ∈
        ∂ (fun y : E ↦ (problem.constraints j y : WithTop ℝ))(x) := by
    simpa using (problem.constraintOracle j).subgradient_spec x
  -- Apply the same local Lipschitz-ball bound to the chosen constraint subgradient.
  simpa [r] using
    norm_le_of_mem_subdifferential_of_lipschitz_ball hr hdom hK hsub

/-- Helper for Theorem 3.2.3: any update of the form `x - (β / ‖g‖²) • g` decreases the squared
distance to `xStar` by at least `β² / ‖g‖²` once `β ≤ ⟪g, x - xStar⟫`. -/
lemma sqDistDrop_of_gap_le_inner
    {x xStar g : E} {β : ℝ} (hβ : 0 ≤ β) (hg_ne : g ≠ 0)
    (hgap : β ≤ inner ℝ g (x - xStar)) :
    ‖(x - (β / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) ≤
      ‖x - xStar‖ ^ (2 : ℕ) - β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
  have hnorm_sq_ne : ‖g‖ ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg_ne)
  have hexpand :
      ‖(x - (β / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) =
        ‖x - xStar‖ ^ (2 : ℕ) -
          2 * (β / ‖g‖ ^ (2 : ℕ)) * inner ℝ (x - xStar) g +
          (β / ‖g‖ ^ (2 : ℕ)) ^ 2 * ‖g‖ ^ (2 : ℕ) := by
    have hfirst :
        (x - (β / ‖g‖ ^ (2 : ℕ)) • g) - xStar =
          (x - xStar) - (β / ‖g‖ ^ (2 : ℕ)) • g := by
      abel
    rw [hfirst, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    by_cases hβnorm : 0 ≤ β / ‖g‖ ^ (2 : ℕ)
    · rw [abs_of_nonneg hβnorm]
      ring
    · rw [abs_of_neg (lt_of_not_ge hβnorm)]
      ring
  rw [hexpand]
  have hcoef_nonneg : 0 ≤ β / ‖g‖ ^ (2 : ℕ) := by
    positivity
  have hcross : β ≤ inner ℝ (x - xStar) g := by
    simpa [real_inner_comm] using hgap
  have hterm :
      (β / ‖g‖ ^ (2 : ℕ)) ^ 2 * ‖g‖ ^ (2 : ℕ) =
        β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    field_simp [hnorm_sq_ne]
  rw [hterm]
  have hbeta_sq :
      β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) ≤
        (β / ‖g‖ ^ (2 : ℕ)) * inner ℝ (x - xStar) g := by
    have hmul := mul_le_mul_of_nonneg_left hcross hcoef_nonneg
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  linarith

/-- Helper for Theorem 3.2.3: the same explicit correction gives a strict squared-distance drop
whenever the gap parameter `β` is positive. -/
lemma sqDistStrictDrop_of_gap_le_inner
    {x xStar g : E} {β : ℝ} (hβ : 0 < β) (hg_ne : g ≠ 0)
    (hgap : β ≤ inner ℝ g (x - xStar)) :
    ‖(x - (β / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) <
      ‖x - xStar‖ ^ (2 : ℕ) := by
  have hdrop := sqDistDrop_of_gap_le_inner (x := x) (xStar := xStar) (g := g) (β := β)
    hβ.le hg_ne hgap
  have hpos : 0 < β ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    positivity
  linarith

/-- Helper for Theorem 3.2.3: on an admissible interior iterate with objective gap larger than
`ε`, the objective branch decreases the squared distance to `xStar` by at least `ε² / M²`. -/
lemma sqDistDrop_of_badObjectiveBranch
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    {k : ℕ}
    (hk_ball :
      problem.iterates ε x0 selectedConstraintAt k ∈ Metric.ball xStar ‖x0 - xStar‖)
    (hk_adm :
      problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k))
    (hk_obj :
      problem.objective (problem.iterates ε x0 selectedConstraintAt k) >
        problem.objective xStar + ε) :
    ‖problem.iterates ε x0 selectedConstraintAt (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖problem.iterates ε x0 selectedConstraintAt k - xStar‖ ^ (2 : ℕ) -
        (ε : ℝ) ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) := by
  let xk := problem.iterates ε x0 selectedConstraintAt k
  let g := problem.oracle.subgradient xk
  -- Turn the objective gap into the affine-support lower bound against `xStar`.
  have hgap_val :
      problem.objective xk - problem.objective xStar ≤ inner ℝ g (xk - xStar) := by
    simpa [xk, g] using value_gap_le_inner_subgradient (oracle := problem.oracle) (x := xk)
      (y := xStar)
  have hgap : ε ≤ inner ℝ g (xk - xStar) := by
    linarith
  have hg_ne : g ≠ 0 := by
    intro hg0
    rw [hg0, inner_zero_left] at hgap
    linarith
  have hnorm_le : ‖g‖ ≤ M := objectiveOracleNorm_le_of_mem_ball
    (problem := problem) (x0 := x0) xStar M hf_lipschitz hk_ball
  have hM_pos : 0 < (M : ℝ) := by
    have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
    linarith
  have hnorm_sq_le : ‖g‖ ^ (2 : ℕ) ≤ (M : ℝ) ^ (2 : ℕ) := by
    have hM_nonneg : 0 ≤ (M : ℝ) := by exact_mod_cast M.2
    nlinarith [hnorm_le, norm_nonneg g, hM_nonneg]
  have hdrop :
      ‖(xk - (ε / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) ≤
        ‖xk - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) :=
    sqDistDrop_of_gap_le_inner (x := xk) (xStar := xStar) (g := g) (β := ε)
      hε.le hg_ne hgap
  have hfrac_le :
      ε ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnorm_sq_le
  have hdrop' :
      ‖(xk - (ε / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) ≤
        ‖xk - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) := by
    linarith
  -- Rewrite the owner objective step to the explicit correction form used in the generic lemma.
  rw [problem.iterates_succ_eq_objective hvalid hk_adm]
  simpa [MultipleConstraintFirstOrderProblem.objectiveStep, xk, g, NormedSpace.normalize, hg_ne,
    div_eq_mul_inv, smul_smul, mul_assoc, mul_left_comm, mul_comm, pow_two] using hdrop'

/-- Helper for Theorem 3.2.3: on an interior violated-constraint branch, the correction step
decreases the squared distance to `xStar` by at least `ε² / M²`. -/
lemma sqDistDrop_of_selectedConstraintBranch
    (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hfeas_xStar : ∀ j, problem.constraints j xStar ≤ 0)
    {k : ℕ} {j : Fin m}
    (hk_ball :
      problem.iterates ε x0 selectedConstraintAt k ∈ Metric.ball xStar ‖x0 - xStar‖)
    (hsel : selectedConstraintAt k = some j)
    (hviol :
      ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k)) :
    ‖problem.iterates ε x0 selectedConstraintAt (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖problem.iterates ε x0 selectedConstraintAt k - xStar‖ ^ (2 : ℕ) -
        (ε : ℝ) ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) := by
  let xk := problem.iterates ε x0 selectedConstraintAt k
  let g := (problem.constraintOracle j).subgradient xk
  -- Compare the violated constraint value with its feasible value at `xStar`.
  have hgap_val :
      problem.constraints j xk - problem.constraints j xStar ≤ inner ℝ g (xk - xStar) := by
    simpa [xk, g] using
      value_gap_le_inner_subgradient (oracle := problem.constraintOracle j) (x := xk) (y := xStar)
  have hgap : problem.constraints j xk ≤ inner ℝ g (xk - xStar) := by
    have hgap' :
        problem.constraints j xk ≤ inner ℝ g (xk - xStar) + problem.constraints j xStar := by
      linarith
    linarith [hgap', hfeas_xStar j]
  have hg_ne : g ≠ 0 := by
    intro hg0
    rw [hg0, inner_zero_left] at hgap
    linarith [hviol]
  have hnorm_le : ‖g‖ ≤ M := constraintOracleNorm_le_of_mem_ball
    (problem := problem) (x0 := x0) xStar M hconstraints_lipschitz hk_ball
  have hM_pos : 0 < (M : ℝ) := by
    have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_ne
    linarith
  have hnorm_sq_le : ‖g‖ ^ (2 : ℕ) ≤ (M : ℝ) ^ (2 : ℕ) := by
    have hM_nonneg : 0 ≤ (M : ℝ) := by exact_mod_cast M.2
    nlinarith [hnorm_le, norm_nonneg g, hM_nonneg]
  have hdrop :
      ‖(xk - (problem.constraints j xk / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) ≤
        ‖xk - xStar‖ ^ (2 : ℕ) -
          (problem.constraints j xk) ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) :=
    sqDistDrop_of_gap_le_inner (x := xk) (xStar := xStar) (g := g)
      (β := problem.constraints j xk) (show 0 ≤ problem.constraints j xk by linarith [hε, hviol])
      hg_ne hgap
  have hfracM_le :
      ε ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnorm_sq_le
  have hfracε_le :
      ε ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) ≤
        (problem.constraints j xk) ^ (2 : ℕ) / ‖g‖ ^ (2 : ℕ) := by
    have hsq : ε ^ (2 : ℕ) ≤ (problem.constraints j xk) ^ (2 : ℕ) := by
      nlinarith [hviol]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hdrop' :
      ‖(xk - (problem.constraints j xk / ‖g‖ ^ (2 : ℕ)) • g) - xStar‖ ^ (2 : ℕ) ≤
        ‖xk - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) := by
    linarith
  -- Rewrite the owner correction step to the explicit `f_j(x_k) / ‖g_j(x_k)‖²` form.
  rw [problem.iterates_succ_eq_constraint hsel]
  simpa [MultipleConstraintFirstOrderProblem.constraintStep, xk, g,
    FirstOrderOracle.correctionStepsize] using hdrop'

/-- Helper for Theorem 3.2.3: if the starting branch is already bad, then the first iterate enters
the open reference ball around `xStar`. -/
lemma firstIterate_mem_ball_of_badStart
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (hε : 0 < ε)
    (hfeas_xStar : ∀ j, problem.constraints j xStar ≤ 0)
    (hbadStart :
      (problem.IsAdmissible ε x0 ∧ problem.objective x0 > problem.objective xStar + ε) ∨
        ∃ j : Fin m, selectedConstraintAt 0 = some j ∧ ε < problem.constraints j x0) :
    problem.iterates ε x0 selectedConstraintAt 1 ∈ Metric.ball xStar ‖x0 - xStar‖ := by
  rcases hbadStart with hbadObj | hbadConstraint
  · rcases hbadObj with ⟨hx0_adm, hobj⟩
    let g := problem.oracle.subgradient x0
    -- The bad objective gap at the admissible start forces a strict decrease in squared distance.
    have hx0_adm_iter :
        problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt 0) := by
      simpa [problem.iterates_zero] using hx0_adm
    have hgap_val :
        problem.objective x0 - problem.objective xStar ≤ inner ℝ g (x0 - xStar) := by
      simpa [g] using
        value_gap_le_inner_subgradient (oracle := problem.oracle) (x := x0) (y := xStar)
    have hgap : ε ≤ inner ℝ g (x0 - xStar) := by
      linarith
    have hg_ne : g ≠ 0 := by
      intro hg0
      rw [hg0, inner_zero_left] at hgap
      linarith
    have hdrop :
        ‖problem.iterates ε x0 selectedConstraintAt 1 - xStar‖ ^ (2 : ℕ) <
          ‖x0 - xStar‖ ^ (2 : ℕ) := by
      rw [problem.iterates_succ_eq_objective (k := 0) hvalid hx0_adm_iter]
      simpa [MultipleConstraintFirstOrderProblem.objectiveStep, g, NormedSpace.normalize, hg_ne,
        div_eq_mul_inv, smul_smul, mul_assoc, mul_left_comm, mul_comm, pow_two] using
        sqDistStrictDrop_of_gap_le_inner (x := x0) (xStar := xStar) (g := g) (β := ε)
          hε hg_ne hgap
    exact mem_ball_of_norm_sq_lt_norm_sq hdrop
  · rcases hbadConstraint with ⟨j, hsel, hviol⟩
    let g := (problem.constraintOracle j).subgradient x0
    -- The violated selected constraint yields the same strict drop at the first correction step.
    have hgap_val :
        problem.constraints j x0 - problem.constraints j xStar ≤ inner ℝ g (x0 - xStar) := by
      simpa [g] using
        value_gap_le_inner_subgradient (oracle := problem.constraintOracle j) (x := x0)
          (y := xStar)
    have hgap : problem.constraints j x0 ≤ inner ℝ g (x0 - xStar) := by
      have hgap' :
          problem.constraints j x0 ≤ inner ℝ g (x0 - xStar) + problem.constraints j xStar := by
        linarith
      linarith [hgap', hfeas_xStar j]
    have hg_ne : g ≠ 0 := by
      intro hg0
      rw [hg0, inner_zero_left] at hgap
      linarith [hviol]
    have hdrop :
        ‖problem.iterates ε x0 selectedConstraintAt 1 - xStar‖ ^ (2 : ℕ) <
          ‖x0 - xStar‖ ^ (2 : ℕ) := by
      rw [problem.iterates_succ_eq_constraint hsel]
      simpa [MultipleConstraintFirstOrderProblem.constraintStep, g,
        FirstOrderOracle.correctionStepsize] using
        sqDistStrictDrop_of_gap_le_inner (x := x0) (xStar := xStar) (g := g)
          (β := problem.constraints j x0)
          (show 0 < problem.constraints j x0 by linarith [hε, hviol]) hg_ne hgap
    exact mem_ball_of_norm_sq_lt_norm_sq hdrop

/-- Helper for Theorem 3.2.3: once an iterate is already inside the open reference ball, every
bad branch gives the same quantitative squared-distance decrease. -/
lemma sqDistDrop_of_badInteriorStep
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hfeas_xStar : ∀ j, problem.constraints j xStar ≤ 0)
    {k : ℕ}
    (hk_ball :
      problem.iterates ε x0 selectedConstraintAt k ∈ Metric.ball xStar ‖x0 - xStar‖)
    (hbad :
      (problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k) ∧
          problem.objective (problem.iterates ε x0 selectedConstraintAt k) >
            problem.objective xStar + ε) ∨
        ∃ j : Fin m, selectedConstraintAt k = some j ∧
          ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k)) :
    ‖problem.iterates ε x0 selectedConstraintAt (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ‖problem.iterates ε x0 selectedConstraintAt k - xStar‖ ^ (2 : ℕ) -
        (ε : ℝ) ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ) := by
  rcases hbad with hbadObj | hbadConstraint
  · rcases hbadObj with ⟨hk_adm, hk_obj⟩
    -- On the admissible objective branch, reuse the already proved objective-drop lemma.
    exact sqDistDrop_of_badObjectiveBranch (problem := problem) (ε := ε) (x0 := x0)
      (selectedConstraintAt := selectedConstraintAt) hvalid xStar M hε hf_lipschitz hk_ball hk_adm
      hk_obj
  · rcases hbadConstraint with ⟨j, hsel, hviol⟩
    -- On a violated selected constraint branch, reuse the companion correction-drop lemma.
    exact sqDistDrop_of_selectedConstraintBranch (problem := problem) (ε := ε) (x0 := x0)
      (selectedConstraintAt := selectedConstraintAt) xStar M hε hconstraints_lipschitz
      hfeas_xStar hk_ball hsel hviol

/-- Helper for Theorem 3.2.3: a good admissible index directly yields nonemptiness of `𝓕_A(N)`
and the sampled minimum bound. -/
lemma sampledBound_of_goodAdmissibleIndex
    (xStar : E) (N : ℕ) {k : Fin (N + 1)}
    (hk : k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N))
    (hobj :
      problem.objective (problem.iterates ε x0 selectedConstraintAt k) ≤
        problem.objective xStar + ε) :
    𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ∧
      problem.sampledOptimalValue ε x0 selectedConstraintAt N ≤
        problem.objective xStar + ε := by
  let xk := problem.iterates ε x0 selectedConstraintAt k
  -- First package the witness iterate as a point of the sampled feasible set.
  have hxFA : xk ∈ 𝓕_A[problem, ε, x0, selectedConstraintAt](N) := by
    rw [problem.mem_admissibleIterateSet_iff]
    exact ⟨k, hk, rfl⟩
  have hnonempty : (𝓕_A[problem, ε, x0, selectedConstraintAt](N)).Nonempty := ⟨xk, hxFA⟩
  refine ⟨Set.nonempty_iff_ne_empty.mp hnonempty, ?_⟩
  -- Then compare the sampled optimal value against the objective value at that feasible witness.
  have hopt :
      problem.sampledOptimalValue ε x0 selectedConstraintAt N ≤
        (problem.objective xk : EReal) := by
    simpa [sampledOptimalValue, xk] using
      (SetConstrainedMinimizationProblem.mk
        (𝓕_A[problem, ε, x0, selectedConstraintAt](N))
        problem.objective).optimalValue_le_of_mem_feasibleSet hxFA
  exact hopt.trans (by
    change ((problem.objective xk : ℝ) : EReal) ≤
      ((problem.objective xStar + ε : ℝ) : EReal)
    exact_mod_cast hobj)

/-- Helper for Theorem 3.2.3: if no good admissible witness appears up to time `N`, then the
uniform distance decrease contradicts the step budget bound. -/
lemma existsGoodAdmissibleIndexUpTo
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hxStar :
      xStar ∈ argmin[{x | ∀ j, problem.constraints j x ≤ 0}] problem.objective)
    (N : ℕ)
    (hN :
      (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        (N : ℝ)) :
    ∃ k : Fin (N + 1),
      k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ∧
        problem.objective (problem.iterates ε x0 selectedConstraintAt k) ≤
          problem.objective xStar + ε := by
  classical
  let x := problem.iterates ε x0 selectedConstraintAt
  let δ : ℝ := (ε : ℝ) ^ (2 : ℕ) / (M : ℝ) ^ (2 : ℕ)
  have hfeas_xStar : ∀ j, problem.constraints j xStar ≤ 0 :=
    problem.feasible_of_mem_constrainedArgmin hxStar
  have hx0_mem_closedBall : x0 ∈ Metric.closedBall xStar ‖x0 - xStar‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have hxStar_mem_closedBall : xStar ∈ Metric.closedBall xStar ‖x0 - xStar‖ := by
    simp [Metric.mem_closedBall]
  by_cases hMzero : (M : ℝ) = 0
  · let k0 : Fin (N + 1) := 0
    -- Route correction: handle the degenerate `M = 0` case directly at the start instead of
    -- forcing the contradiction induction through a vanishing decrement.
    have hk0 : k0 ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) := by
      rw [problem.mem_admissibleIndices_iff (N := N) (k := k0)]
      intro j
      have hdist :
          dist (problem.constraints j x0) (problem.constraints j xStar) ≤
            (M : ℝ) * dist x0 xStar :=
        (hconstraints_lipschitz j).dist_le_mul x0 hx0_mem_closedBall xStar hxStar_mem_closedBall
      have heq : problem.constraints j x0 = problem.constraints j xStar := by
        rw [hMzero, zero_mul] at hdist
        exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)
      calc
        problem.constraints j x0 = problem.constraints j xStar := heq
        _ ≤ 0 := hfeas_xStar j
        _ ≤ ε := by linarith
    have hobj_eq : problem.objective x0 = problem.objective xStar := by
      have hdist :
          dist (problem.objective x0) (problem.objective xStar) ≤
            (M : ℝ) * dist x0 xStar :=
        hf_lipschitz.dist_le_mul x0 hx0_mem_closedBall xStar hxStar_mem_closedBall
      rw [hMzero, zero_mul] at hdist
      exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)
    refine ⟨k0, hk0, ?_⟩
    calc
      problem.objective (x k0) = problem.objective x0 := by simp [x, k0]
      _ = problem.objective xStar := hobj_eq
      _ ≤ problem.objective xStar + ε := by linarith
  · have hM_pos : 0 < (M : ℝ) := by
      have hM_nonneg : 0 ≤ (M : ℝ) := by exact_mod_cast M.2
      exact lt_of_le_of_ne hM_nonneg (Ne.symm hMzero)
    by_cases hgood :
        ∃ k : Fin (N + 1),
          k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ∧
            problem.objective (x k) ≤ problem.objective xStar + ε
    · exact hgood
    · have hbadStart :
          (problem.IsAdmissible ε x0 ∧ problem.objective x0 > problem.objective xStar + ε) ∨
            ∃ j : Fin m, selectedConstraintAt 0 = some j ∧ ε < problem.constraints j x0 := by
        cases hsel0 : selectedConstraintAt 0 with
        | none =>
            left
            have hx0_adm : problem.IsAdmissible ε x0 := by
              simpa [x, problem.iterates_zero, hsel0] using
                problem.selectedConstraintAt_spec hvalid 0
            have hk0 : (0 : Fin (N + 1)) ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) := by
              refine (problem.mem_admissibleIndices_iff
                (ε := ε) (x0 := x0) (selectedConstraintAt := selectedConstraintAt)
                (N := N) (k := (0 : Fin (N + 1)))).2 ?_
              simpa [x, problem.iterates_zero] using hx0_adm
            refine ⟨hx0_adm, ?_⟩
            by_contra hobj
            apply hgood
            exact ⟨0, hk0, by simpa [x, problem.iterates_zero] using le_of_not_gt hobj⟩
        | some j =>
            right
            refine ⟨j, rfl, ?_⟩
            simpa [x, problem.iterates_zero, hsel0] using
              problem.selectedConstraintAt_spec hvalid 0
      have hx1_ball : x 1 ∈ Metric.ball xStar ‖x0 - xStar‖ :=
        problem.firstIterate_mem_ball_of_badStart (ε := ε) (x0 := x0)
          (selectedConstraintAt := selectedConstraintAt) hvalid xStar hε hfeas_xStar hbadStart
      have hx1_lt :
          ‖x 1 - xStar‖ ^ (2 : ℕ) < ‖x0 - xStar‖ ^ (2 : ℕ) := by
        have hnorm_lt : ‖x 1 - xStar‖ < ‖x0 - xStar‖ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hx1_ball
        nlinarith [hnorm_lt, norm_nonneg (x 1 - xStar), norm_nonneg (x0 - xStar)]
      have hδ_nonneg : 0 ≤ δ := by
        positivity
      have hprefix :
          ∀ t : ℕ, t ≤ N →
            ‖x (t + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖x 1 - xStar‖ ^ (2 : ℕ) - (t : ℝ) * δ ∧
              x (t + 1) ∈ Metric.ball xStar ‖x0 - xStar‖ := by
        intro t
        induction t with
        | zero =>
            intro _
            refine ⟨by simp [δ], hx1_ball⟩
        | succ t iht =>
            intro ht
            have ht_prev : t ≤ N := Nat.le_trans (Nat.le_succ t) ht
            rcases iht ht_prev with ⟨hbound_t, hball_t⟩
            have hbad_t :
                (problem.IsAdmissible ε (x (t + 1)) ∧
                    problem.objective (x (t + 1)) > problem.objective xStar + ε) ∨
                  ∃ j : Fin m, selectedConstraintAt (t + 1) = some j ∧
                    ε < problem.constraints j (x (t + 1)) := by
              cases hsel : selectedConstraintAt (t + 1) with
              | none =>
                  left
                  have hadm : problem.IsAdmissible ε (x (t + 1)) := by
                    simpa [x, hsel] using problem.selectedConstraintAt_spec hvalid (t + 1)
                  refine ⟨hadm, ?_⟩
                  by_contra hobj
                  apply hgood
                  refine ⟨⟨t + 1, Nat.lt_succ_of_le ht⟩, ?_, ?_⟩
                  · simpa [x] using
                      (problem.mem_admissibleIndices_iff (N := N)
                        (k := ⟨t + 1, Nat.lt_succ_of_le ht⟩)).2 hadm
                  · simpa [x] using le_of_not_gt hobj
              | some j =>
                  right
                  refine ⟨j, rfl, ?_⟩
                  simpa [x, hsel] using problem.selectedConstraintAt_spec hvalid (t + 1)
            have hdrop :
                ‖x (t + 2) - xStar‖ ^ (2 : ℕ) ≤
                  ‖x (t + 1) - xStar‖ ^ (2 : ℕ) - δ := by
              simpa [x, δ] using
                problem.sqDistDrop_of_badInteriorStep (ε := ε) (x0 := x0)
                  (selectedConstraintAt := selectedConstraintAt) hvalid xStar M hε hf_lipschitz
                  hconstraints_lipschitz hfeas_xStar hball_t hbad_t
            have hbound_next :
                ‖x (t + 2) - xStar‖ ^ (2 : ℕ) ≤
                  ‖x 1 - xStar‖ ^ (2 : ℕ) - ((t + 1 : ℕ) : ℝ) * δ := by
              rw [Nat.cast_add, Nat.cast_one]
              linarith
            have hlt_next :
                ‖x (t + 2) - xStar‖ ^ (2 : ℕ) < ‖x0 - xStar‖ ^ (2 : ℕ) := by
              have hstep_nonneg : 0 ≤ ((t + 1 : ℕ) : ℝ) * δ := by positivity
              have haux :
                  ‖x 1 - xStar‖ ^ (2 : ℕ) - ((t + 1 : ℕ) : ℝ) * δ <
                    ‖x0 - xStar‖ ^ (2 : ℕ) := by
                linarith
              exact lt_of_le_of_lt hbound_next haux
            have hball_next : x (t + 2) ∈ Metric.ball xStar ‖x0 - xStar‖ :=
              mem_ball_of_norm_sq_lt_norm_sq hlt_next
            exact ⟨hbound_next, hball_next⟩
      have hradius_le :
          ‖x0 - xStar‖ ^ (2 : ℕ) ≤ (N : ℝ) * δ := by
        have hscaled :
            ((((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ)) * δ ≤
              (N : ℝ) * δ :=
          mul_le_mul_of_nonneg_right hN hδ_nonneg
        have hratio_mul_delta :
            (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * δ = 1 := by
          have hε_ne : (ε : ℝ) ≠ 0 := by linarith
          dsimp [δ]
          field_simp [hM_pos.ne', hε_ne]
        have hcancel :
            ((((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ)) * δ =
              ‖x0 - xStar‖ ^ (2 : ℕ) := by
          calc
            ((((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ)) * δ =
                ‖x0 - xStar‖ ^ (2 : ℕ) *
                  ((((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * δ) := by ring
            _ = ‖x0 - xStar‖ ^ (2 : ℕ) * 1 := by rw [hratio_mul_delta]
            _ = ‖x0 - xStar‖ ^ (2 : ℕ) := by ring
        rw [hcancel] at hscaled
        exact hscaled
      have hfinal_bound :
          ‖x (N + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖x 1 - xStar‖ ^ (2 : ℕ) - (N : ℝ) * δ :=
        (hprefix N le_rfl).1
      have hfinal_lt : ‖x (N + 1) - xStar‖ ^ (2 : ℕ) < 0 := by
        have haux : ‖x 1 - xStar‖ ^ (2 : ℕ) - (N : ℝ) * δ < 0 := by
          linarith
        exact lt_of_le_of_lt hfinal_bound haux
      have hnonneg : 0 ≤ ‖x (N + 1) - xStar‖ ^ (2 : ℕ) := by
        positivity
      linarith

-- Proof sketch: argue by contradiction. If every iterate up to time `N` either violates a
-- constraint by more than `ε` or has objective gap larger than `ε`, then each step of method
-- `(3.2.24)` decreases `‖x_k - x*‖²` by at least `ε² / M²`. Summing the drop over
-- `k = 0, ..., N` contradicts the bound `N ≥ (M² / ε²) ‖x₀ - x*‖²`, so some admissible iterate
-- must satisfy the desired objective estimate, which then bounds the sampled minimum.
/-- Theorem 3.2.3: let `x_k = problem.iterates ε x₀ selectedConstraintAt k` be the recursively
generated run of method `(3.2.24)`. If the branch choices are valid, if the objective `f` and
the constraint functions `f_j`, `j = 1, ..., m`, are `M`-Lipschitz on the ball
`B₂(x*, ‖x₀ - x*‖)`, if `x*` belongs to the canonical constrained argmin set
`argmin[{x | ∀ j, f_j(x) ≤ 0}] f`, and if the number of steps satisfies
`N ≥ (M² / ε²) ‖x₀ - x*‖²`, then the admissible iterate set `𝓕_A(N)` is nonempty and the sampled
minimum on `𝓕_A(N)` satisfies `f_N^* ≤ f(x*) + ε`. The index-form consequence
`(𝒜(N)).Nonempty` is a separate corollary via `admissibleIterateSet_nonempty_iff`. -/
theorem admissibleIterateSet_nonempty_and_sampledMinimum_le_optimal_add_eps
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hxStar :
      xStar ∈ argmin[{x | ∀ j, problem.constraints j x ≤ 0}] problem.objective)
    (N : ℕ)
    (hN :
      (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        (N : ℝ)) :
    𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ∧
      problem.sampledOptimalValue ε x0 selectedConstraintAt N ≤
        problem.objective xStar + ε := by
  -- Route correction: extract the good index first, then convert it to the sampled-set
  -- conclusions instead of inlining the full contradiction induction in the main theorem.
  rcases problem.existsGoodAdmissibleIndexUpTo (ε := ε) (x0 := x0)
      (selectedConstraintAt := selectedConstraintAt) hvalid xStar M hε hf_lipschitz
      hconstraints_lipschitz hxStar N hN with ⟨k, hk, hobj⟩
  -- The witness index immediately gives both nonemptiness and the sampled minimum bound.
  exact problem.sampledBound_of_goodAdmissibleIndex (ε := ε) (x0 := x0)
    (selectedConstraintAt := selectedConstraintAt) xStar N hk hobj

/-- Helper for Theorem 3.2.3: the repaired main theorem immediately yields the index-form
nonemptiness conclusion `(𝒜(N)).Nonempty`. -/
theorem admissibleIndices_nonempty_of_admissibleIterateSet_nonempty
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hxStar :
      xStar ∈ argmin[{x | ∀ j, problem.constraints j x ≤ 0}] problem.objective)
    (N : ℕ)
    (hN :
      (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        (N : ℝ)) :
    (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty := by
  -- Read the main theorem first, then translate set nonemptiness back to index nonemptiness.
  have hmain := problem.admissibleIterateSet_nonempty_and_sampledMinimum_le_optimal_add_eps
    hvalid xStar M hε hf_lipschitz hconstraints_lipschitz hxStar N hN
  exact (problem.admissibleIterateSet_nonempty_iff (ε := ε) (x0 := x0)
    (selectedConstraintAt := selectedConstraintAt) N).1 hmain.1

end Iterates

end MultipleConstraintFirstOrderProblem

end
