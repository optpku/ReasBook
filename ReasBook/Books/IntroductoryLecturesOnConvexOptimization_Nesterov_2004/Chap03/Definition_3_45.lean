/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators EuclideanOrthant

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

/- Primary domain: approximate Lagrange multipliers attached to a run of the switching method in
Algorithm 3.4.

Relevant owner-style declarations sampled before refining:
- `ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet`
- `ApproximateLagrangeMultiplierSwitchingMethod.selectedIndexAt`
- `FirstOrderOracle.correctionStepsize`
- `EuclideanSpace.nonnegativeOrthant`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`

Best owner abstraction:
- `source-facing`: the textbook objects `A₀(t)`, `Aⱼ(t)`, `N(t)`, `S_t`, `σ_t`, and `λ_t`
- `core/canonical`: a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`
  together with the chapter's canonical multiplier carrier `EuclideanSpace ℝ (Fin m)`
- `bridge/view`: coordinate and orthant lemmas for `λ_t`

Primitive data:
- the switching-method run `method`

Derived API:
- the iterate sequence `x_k`, active sets `𝒥_k`, chosen indices `j_k`, and selected branch
  scalars `h_k` already exposed by Algorithm 3.4 through `selectedIndexAt` and the owner
  correction scalar `(problem.constraintOracle j).correctionStepsize (method k)` on each selected
  branch
- the finite index sets `A₀(t)` and `Aⱼ(t)`, stored intrinsically as `Finset`s in
  `Fin (t + 1)`
- the direct finite sums over `A₀(t)` and `Aⱼ(t)` for `S_t` and `λ_t`, using the chapter owner
  reciprocal and correction scalars without a parallel wrapper API, but only under the explicit
  denominator regime that makes those ratios genuine textbook ratios rather than totalized values;
  the later normalized primal average is delegated downstream to the canonical `Finset.centerMass`
  owner on `A₀(t)` with those same weights
- the count `N(t)`
- the normalization sum `S_t`, defined under the explicit objective-denominator regime by the
  textbook finite reciprocal formula
- the scalar `σ_t = h S_t`, kept in its source-facing real form under that same regime
- positivity consequences such as `N(t) > 0 → S_t > 0`, recorded only as downstream lemmas with
  explicit nonvanishing hypotheses on the sampled objective subgradients
- the canonical multiplier vector `approximateDualMultiplier t : EuclideanSpace ℝ (Fin m)`,
  whose coordinates are the textbook real ratios `σ_t⁻¹ ∑_{k ∈ A_j(t)} h_k` under the full
  denominator regime for Definition 3.45
- its coordinate formula and positivity / orthant bridge lemmas under the textbook positivity
  regime

Accordingly this file keeps the source-facing objects of Definition 3.45, but derives them
directly from the switching-method owner data, uses the finite interval `Fin (t + 1)` and its
canonical finite-set API instead of a filtered `range` subset of `ℕ`, reuses the chapter owner
`FirstOrderOracle.correctionStepsize` rather than a parallel local stepsize wrapper, and makes
the denominator regime explicit in the public semantics of `S_t`, `σ_t`, and `λ_t` instead of
silently totalizing undefined textbook ratios to zero.
-/

/-- The index set `A₀(t) = {k ∈ {0, ..., t} : 𝒥_k = ∅}`. -/
def inactiveConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) :
    Finset (Fin (t + 1)) :=
  Finset.univ.filter fun k ↦ method.activeSet k = ∅

/-- The index set `A_j(t) = {k ∈ {0, ..., t} : j_k = j}` for a fixed constraint coordinate `j`.
The chosen indices `j_k` are the ones produced by Algorithm 3.4 itself. -/
def selectedConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) (j : Fin m) :
    Finset (Fin (t + 1)) :=
  Finset.univ.filter fun k ↦ method.selectedIndexAt k = some j

/- Source-facing Lean notation for the textbook index sets `A₀(t)` and `A_j(t)`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "A₀[" method:arg "](" t:arg ")" =>
  inactiveConstraintIndices method t

scoped notation:max "A[" method:arg "](" t:arg ", " j:arg ")" =>
  selectedConstraintIndices method t j

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Membership in `A₀(t)` is exactly the source condition `𝒥_k = ∅`. -/
@[simp]
theorem mem_inactiveConstraintIndices_iff
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {k : Fin (t + 1)} :
    k ∈ A₀[method](t) ↔ method.activeSet k = ∅ := by
  simp [inactiveConstraintIndices]

/-- Membership in `A_j(t)` is exactly the source condition `j_k = j`. -/
@[simp]
theorem mem_selectedConstraintIndices_iff
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) (j : Fin m)
    {k : Fin (t + 1)} :
    k ∈ A[method](t, j) ↔ method.selectedIndexAt k = some j := by
  simp [selectedConstraintIndices]

/-- The counting function `N(t) = |A₀(t)|`. -/
def inactiveConstraintCount
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : ℕ :=
  (A₀[method](t)).card

/- Source-facing Lean notation for the textbook count `N(t)`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "N[" method:arg "](" t:arg ")" =>
  inactiveConstraintCount method t

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- The textbook denominator regime on `A₀(t)`: every sampled objective subgradient is nonzero,
so the reciprocal norms in `S_t` are genuine reciprocals rather than totalized values. -/
def HasObjectiveDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  ∀ ⦃k : Fin (t + 1)⦄, k ∈ A₀[method](t) → method.objectiveSubgradient k ≠ 0

/-- The textbook denominator regime on the selected-constraint side: every sampled selected
constraint subgradient is nonzero, so each correction scalar `h_k` is the genuine textbook ratio
`f_j(x_k) / ‖g_j(x_k)‖²`. -/
def HasSelectedConstraintDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  ∀ ⦃j : Fin m⦄ ⦃k : Fin (t + 1)⦄, k ∈ A[method](t, j) →
    (problem.constraintOracle j).subgradient (method k) ≠ 0

/-- The full denominator regime needed for the textbook multiplier `λ_t`: the reciprocal weights
on `A₀(t)` and the correction scalars on the selected-constraint indices are genuine ratios,
`h > 0`, and `N(t) > 0` so the normalizing factor `σ_t = h S_t` is nonzero. -/
def HasApproximateDualMultiplierDenominators
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : Prop :=
  method.HasObjectiveDenominators t ∧
    method.HasSelectedConstraintDenominators t ∧
    0 < method.h ∧
    0 < N[method](t)

theorem HasApproximateDualMultiplierDenominators.objective
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    method.HasObjectiveDenominators t :=
  hdenom.1

theorem HasApproximateDualMultiplierDenominators.selected
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    method.HasSelectedConstraintDenominators t := by
  rcases hdenom with ⟨_, hselected, _, _⟩
  exact hselected

theorem HasApproximateDualMultiplierDenominators.h_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < method.h := by
  rcases hdenom with ⟨_, _, hh, _⟩
  exact hh

theorem HasApproximateDualMultiplierDenominators.inactiveConstraintCount_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < N[method](t) := by
  rcases hdenom with ⟨_, _, _, hN⟩
  exact hN

private def objectiveReciprocalWeight
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (k : {k : Fin (t + 1) // k ∈ A₀[method](t)}) : ℝ :=
  ↑((Units.mk0 ‖method.objectiveSubgradient k.1‖
      (norm_ne_zero_iff.mpr (hobjective k.2)))⁻¹ : ℝˣ)

private theorem objectiveReciprocalWeight_eq_inv_norm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (k : {k : Fin (t + 1) // k ∈ A₀[method](t)}) :
    objectiveReciprocalWeight method t hobjective k = ‖method.objectiveSubgradient k.1‖⁻¹ := by
  simp [objectiveReciprocalWeight, Units.val_mk0]

/-- The normalization sum `S_t = ∑_{k ∈ A₀(t)} 1 / ‖g(x_k)‖`, defined under the textbook
nonvanishing regime `hobjective` so that each reciprocal is a genuine reciprocal norm. -/
def inverseSubgradientNormSum
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) : ℝ :=
  Finset.sum (A₀[method](t)).attach (objectiveReciprocalWeight method t hobjective)

/-- A nonzero objective subgradient gives a strictly positive reciprocal norm weight. -/
theorem inv_norm_objectiveSubgradient_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (k : ℕ)
    (hgrad_ne : method.objectiveSubgradient k ≠ 0) :
    0 < ‖method.objectiveSubgradient k‖⁻¹ := by
  simp [inv_pos, norm_pos_iff, hgrad_ne]

/- Source-facing Lean notation for the textbook normalization sum `S_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "S[" method:arg "](" t:arg "; " hobjective:arg ")" =>
  inverseSubgradientNormSum method t hobjective

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- If no objective-step index occurs up to time `t`, then the reciprocal-norm sum `S_t`
vanishes. -/
theorem inverseSubgradientNormSum_eq_zero_of_inactiveConstraintCount_eq_zero
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hN : N[method](t) = 0) :
    S[method](t; hobjective) = 0 := by
  have hcard : (A₀[method](t)).card = 0 := by
    simpa [inactiveConstraintCount] using hN
  have hattach : (A₀[method](t)).attach = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [Finset.card_attach] using hcard
  rw [inverseSubgradientNormSum, hattach]
  simp

/-- If `N(t) > 0`, then the reciprocal-norm sum `S_t` is strictly positive. -/
theorem inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hN : 0 < N[method](t)) :
    0 < S[method](t; hobjective) := by
  have hcard : 0 < (A₀[method](t)).card := by
    simpa [inactiveConstraintCount] using hN
  rw [inverseSubgradientNormSum]
  refine Finset.sum_pos' ?_ ?_
  · intro k hk
    exact le_of_lt <| by
      simpa [objectiveReciprocalWeight_eq_inv_norm] using
        method.inv_norm_objectiveSubgradient_pos k.1 (hobjective k.2)
  · rcases Finset.card_pos.mp hcard with ⟨k, hk⟩
    refine ⟨⟨k, hk⟩, by simp, ?_⟩
    simpa [objectiveReciprocalWeight_eq_inv_norm] using
      method.inv_norm_objectiveSubgradient_pos k (hobjective hk)

/-- The reciprocal-norm sum `S_t` is always nonnegative. -/
theorem inverseSubgradientNormSum_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) :
    0 ≤ S[method](t; hobjective) := by
  rw [inverseSubgradientNormSum]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  exact le_of_lt <| by
    simpa [objectiveReciprocalWeight_eq_inv_norm] using
      method.inv_norm_objectiveSubgradient_pos k.1 (hobjective k.2)

/-- For Definition 3.45, the textbook gates `N(t) > 0` and `S_t > 0` are equivalent once the
objective-step denominators are known to be nonzero. -/
theorem inactiveConstraintCount_pos_iff_inverseSubgradientNormSum_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) :
    0 < N[method](t) ↔ 0 < S[method](t; hobjective) := by
  constructor
  · exact method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos t hobjective
  · intro hS
    by_contra hN
    have hN0 : method.inactiveConstraintCount t = 0 := Nat.eq_zero_of_not_pos hN
    have hS0 := method.inverseSubgradientNormSum_eq_zero_of_inactiveConstraintCount_eq_zero
      t hobjective hN0
    rw [hS0] at hS
    exact (lt_irrefl (0 : ℝ)) hS

/-- On a selected-constraint index, the chapter owner correction scalar is strictly positive. -/
theorem correctionStepsize_pos_of_selectedIndexAt_eq_some
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ} {j : Fin m}
    (hh : 0 < method.h)
    (hsel : method.selectedIndexAt k = some j)
    (hgrad_ne : (problem.constraintOracle j).subgradient (method k) ≠ 0) :
    0 < (problem.constraintOracle j).correctionStepsize (method k) := by
  have hj : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hnorm_pos : 0 < ‖(problem.constraintOracle j).subgradient (method k)‖ :=
    norm_pos_iff.mpr hgrad_ne
  have hthreshold :
      method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ <
        problem.constraints j (method k) := by
    simpa [activeSet, ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet] using hj
  have hconstraint_pos : 0 < problem.constraints j (method k) :=
    lt_trans (mul_pos hh hnorm_pos) hthreshold
  simpa [FirstOrderOracle.correctionStepsize] using
    div_pos hconstraint_pos (pow_pos hnorm_pos _)

/-- The scalar `σ_t = h S_t`, kept in the textbook real-valued form under the objective
denominator regime `hobjective`. -/
def normalizingFactor
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t) : ℝ :=
  method.h * S[method](t; hobjective)

/- Source-facing Lean notation for the textbook normalizing factor `σ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "σ[" method:arg "](" t:arg "; " hobjective:arg ")" =>
  normalizingFactor method t hobjective

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Positive `N(t)` forces the normalizing factor `σ_t = h S_t` to be positive. -/
theorem normalizingFactor_pos_of_inactiveConstraintCount_pos
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hh : 0 < method.h)
    (hN : 0 < N[method](t)) :
    0 < σ[method](t; hobjective) := by
  rw [normalizingFactor]
  have hS : 0 < S[method](t; hobjective) :=
    method.inverseSubgradientNormSum_pos_of_inactiveConstraintCount_pos t hobjective hN
  exact mul_pos hh hS

/-- If `h > 0`, then the normalizing factor `σ_t = h S_t` is nonnegative. -/
theorem normalizingFactor_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hobjective : method.HasObjectiveDenominators t)
    (hh : 0 < method.h) :
    0 ≤ σ[method](t; hobjective) := by
  rw [normalizingFactor]
  exact mul_nonneg hh.le (method.inverseSubgradientNormSum_nonneg t hobjective)

/-- Under the full denominator regime for Definition 3.45, the normalizing factor `σ_t` is
strictly positive. -/
theorem HasApproximateDualMultiplierDenominators.normalizingFactor_pos
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    0 < σ[method](t; hdenom.objective) :=
  method.normalizingFactor_pos_of_inactiveConstraintCount_pos t hdenom.objective
    hdenom.h_pos hdenom.inactiveConstraintCount_pos

theorem HasApproximateDualMultiplierDenominators.normalizingFactor_ne_zero
    {method : ApproximateLagrangeMultiplierSwitchingMethod problem} {t : ℕ}
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    σ[method](t; hdenom.objective) ≠ 0 :=
  ne_of_gt hdenom.normalizingFactor_pos

private def selectedCorrectionWeight
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hselected : method.HasSelectedConstraintDenominators t) (j : Fin m)
    (k : {k : Fin (t + 1) // k ∈ A[method](t, j)}) : ℝ :=
  problem.constraints j (method k.1) /
    ↑(Units.mk0 (‖(problem.constraintOracle j).subgradient (method k.1)‖ ^ (2 : ℕ))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (hselected k.2))) : ℝˣ)

private theorem selectedCorrectionWeight_eq_correctionStepsize
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hselected : method.HasSelectedConstraintDenominators t) (j : Fin m)
    (k : {k : Fin (t + 1) // k ∈ A[method](t, j)}) :
    selectedCorrectionWeight method t hselected j k =
      (problem.constraintOracle j).correctionStepsize (method k.1) := by
  simp [selectedCorrectionWeight, FirstOrderOracle.correctionStepsize, Units.val_mk0]

/-- Definition 3.45: for a run of Algorithm 3.4, the approximate dual multiplier vector
`λ_t` is the canonical multiplier vector in `EuclideanSpace ℝ (Fin m)` whose `j`th
coordinate is the textbook real ratio `λ_t^{(j)} = σ_t⁻¹ ∑_{k ∈ A_j(t)} h_k`, where
`A₀(t) = {k ≤ t : 𝒥_k = ∅}`,
`A_j(t) = {k ≤ t : j_k = j}`, `N(t) = |A₀(t)|`, `S_t = ∑_{k ∈ A₀(t)} 1 / ‖g(x_k)‖`, and
`σ_t = h S_t`. On `A_j(t)`, the chapter owner scalar
`(problem.constraintOracle j).correctionStepsize (method k)` is exactly the textbook `h_k`.
The owner is defined only under the full denominator regime `hdenom`, so all ratios are genuine
textbook ratios rather than totalized zero-division artifacts. Orthant membership and positivity
consequences belong to separate companion theorems. -/
def approximateDualMultiplier
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j ↦
    (Finset.sum (A[method](t, j)).attach
      (selectedCorrectionWeight method t hdenom.selected j)) /
      ↑(Units.mk0 (σ[method](t; hdenom.objective))
        hdenom.normalizingFactor_ne_zero : ℝˣ)

/- Source-facing Lean notation for the textbook approximate multiplier `λ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "λ[" method:arg "](" t:arg "; " hdenom:arg ")" =>
  approximateDualMultiplier method t hdenom

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/-- Evaluating `λ[method](t; hdenom)` at coordinate `j` recovers the normalized finite sum over
`A_j(t)`. -/
@[simp]
theorem approximateDualMultiplier_apply
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (j : Fin m) :
    λ[method](t; hdenom) j =
      (Finset.sum (A[method](t, j)).attach fun k ↦
        (problem.constraintOracle j).correctionStepsize (method k.1)) /
        σ[method](t; hdenom.objective) :=
  by
    simp [approximateDualMultiplier, selectedCorrectionWeight_eq_correctionStepsize, Units.val_mk0]

/-- On a selected-constraint index, the chapter owner correction scalar `h_k` is nonnegative. -/
theorem correctionStepsize_nonneg_of_selectedIndexAt_eq_some
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {k : ℕ} {j : Fin m}
    (hh : 0 < method.h)
    (hsel : method.selectedIndexAt k = some j) :
    0 ≤ (problem.constraintOracle j).correctionStepsize (method k) := by
  have hj : j ∈ method.activeSet k := by
    simpa [hsel] using method.selectedIndexAt_spec k
  have hthreshold :
      method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ <
        problem.constraints j (method k) := by
    simpa [activeSet, ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet] using hj
  have hconstraint_pos : 0 < problem.constraints j (method k) := by
    have hmul_nonneg :
        0 ≤ method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := by
      positivity
    exact lt_of_le_of_lt hmul_nonneg hthreshold
  have hdenom_nonneg :
      0 ≤ ‖(problem.constraintOracle j).subgradient (method k)‖ ^ (2 : ℕ) := by
    positivity
  simpa [FirstOrderOracle.correctionStepsize] using
    div_nonneg (le_of_lt hconstraint_pos) hdenom_nonneg

/-- On a selected-constraint index, the chapter owner correction scalar `h_k` is nonnegative. -/
theorem correctionStepsize_nonneg_of_mem_selectedConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    {j : Fin m} {k : Fin (t + 1)} (hk : k ∈ A[method](t, j)) (hh : 0 < method.h) :
    0 ≤ (problem.constraintOracle j).correctionStepsize (method k) := by
  exact method.correctionStepsize_nonneg_of_selectedIndexAt_eq_some hh
    ((mem_selectedConstraintIndices_iff method t j).1 hk)

/-- If `h > 0`, then every coordinate of `λ_t` is nonnegative. -/
theorem approximateDualMultiplier_nonneg
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t)
    (j : Fin m) :
    0 ≤ λ[method](t; hdenom) j := by
  rw [approximateDualMultiplier_apply]
  change 0 ≤
    (Finset.sum (A[method](t, j)).attach fun k ↦
      (problem.constraintOracle j).correctionStepsize (method k.1)) /
        σ[method](t; hdenom.objective)
  refine div_nonneg ?_ (le_of_lt hdenom.normalizingFactor_pos)
  refine Finset.sum_nonneg fun k hk ↦ ?_
  exact method.correctionStepsize_nonneg_of_mem_selectedConstraintIndices t k.2 hdenom.h_pos

/-- Under the full denominator regime for Definition 3.45, the approximate multiplier vector
`λ_t` lies in the nonnegative orthant `ℝ₊^m`. -/
theorem approximateDualMultiplier_mem_nonnegativeOrthant
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) :
    (λ[method](t; hdenom)) ∈ ℝ₊^m := by
  simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
    fun j ↦ method.approximateDualMultiplier_nonneg t hdenom j

end ApproximateLagrangeMultiplierSwitchingMethod
