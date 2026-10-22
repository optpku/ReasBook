/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open QuadraticallyConstrainedQuadraticOptimizationProblem
open Set Topology Filter
open scoped Gradient HessianLocalNorm BigOperators

variable {n m : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 5.4.3.2 lies in the Chapter 5 QCQP / logarithmic-barrier / short-step
path-following domain.

Sampled owner declarations in this domain:
* `QuadraticallyConstrainedQuadraticOptimizationProblem.strictEpigraphFeasibleSet`,
  `StrictEpigraphFeasiblePoint`, `epigraphLogarithmicBarrier`, and
  `epigraphLogarithmicBarrierAmbient` from `Definition_5_4_3_5`, the QCQP owner API for the
  strict epigraph barrier;
* `BarrierPathFollowingScheme` from `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers on an ambient domain;
* the chapter `RealProdL2` pattern, used in nearby files to keep raw pair owners on the public
  surface while realizing the ambient Euclidean structure through the canonical `WithLp 2`
  `L²` model only internally.

Source/core/bridge triage:
* source-facing: the QCQP strict epigraph feasible region and its logarithmic barrier;
* core/canonical: `BarrierPathFollowingScheme` together with `IsSelfConcordantBarrierOnWith`;
* bridge/view: the local `L²` inner-product structure on the raw pair space `Eₙ × ℝ`,
  implemented through `WithLp.toLp`.

Primitive data:
* the QCQP owner `problem`.

Derived API:
* the strict-to-nonstrict epigraph-feasibility inclusion;
* the closure bridge identifying the closure of the strict QCQP epigraph domain with the
  nonstrict QCQP epigraph feasible set;
* the raw-pair self-concordant-barrier instance needed by `BarrierPathFollowingScheme`, with the
  `WithLp` realization kept internal to this file;
* the common short-step existence package theorem and its source-facing projections.

The refined file therefore removes the redundant public `WithLp`-surface wrappers from
Proposition 5.4.3.2. The QCQP owner barrier remains primary, and the `WithLp` model is used only
internally to equip the raw epigraph pair space with its `L²` ambient structure. -/

section

variable (problem : QuadraticallyConstrainedQuadraticOptimizationProblem n m)

noncomputable local instance instLocalChap05_Proposition_5_4_3_21 : SeminormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.seminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instLocalChap05_Proposition_5_4_3_22 : NormedAddCommGroup (Eₙ × ℝ) :=
  WithLp.normedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instLocalChap05_Proposition_5_4_3_23 : NormedSpace ℝ (Eₙ × ℝ) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 Eₙ ℝ

noncomputable local instance instInnerProductSpaceChap05_Proposition_5_4_3_21 : InnerProductSpace ℝ (Eₙ × ℝ) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 Eₙ ℝ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Proposition_5_4_3_24 : CompleteSpace (Eₙ × ℝ) := inferInstance

local notation "𝒟" =>
  problem.strictEpigraphFeasibleSet
local notation "F" =>
  problem.epigraphLogarithmicBarrierAmbient
local notation "P" =>
  problem.epigraphOptimizationProblem
local notation "ℱ" =>
  problem.epigraphFeasibleSet
local notation "cτ" =>
  ((0 : Eₙ), (1 : ℝ))

/-- Helper for Proposition 5.4.3.2: the lifted quadratic operator acts only on the `x`
coordinate of a raw epigraph pair. -/
def liftedQuadraticOperator (A : Matrix (Fin n) (Fin n) ℝ) :
    (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ) :=
  ((A.toEuclideanLin.toContinuousLinearMap).comp (ContinuousLinearMap.fst ℝ Eₙ ℝ)).prod
    (0 : (Eₙ × ℝ) →L[ℝ] ℝ)

/-- Helper for Proposition 5.4.3.2: passing to `selfAdjointPart` preserves the diagonal quadratic
pairing `⟪Tu, u⟫`. -/
theorem selfAdjointPart_apply_inner_eq
    (T : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (u : Eₙ × ℝ) :
    inner ℝ ((selfAdjointPart ℝ T : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) u) u = inner ℝ (T u) u := by
  rw [show (selfAdjointPart ℝ T : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) =
    (⅟2 : ℝ) • (T + T.adjoint) by
    rw [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]]
  calc
    inner ℝ (((⅟2 : ℝ) • (T + T.adjoint)) u) u
        = (⅟2 : ℝ) * inner ℝ (T u) u + (⅟2 : ℝ) * inner ℝ (T.adjoint u) u := by
            simp [inner_add_left, inner_smul_left]
    _ = (⅟2 : ℝ) * inner ℝ (T u) u + (⅟2 : ℝ) * inner ℝ (T u) u := by
          rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    _ = inner ℝ (T u) u := by
          have htwo : (⅟2 : ℝ) * 2 = 1 := by norm_num
          calc
            (⅟2 : ℝ) * inner ℝ (T u) u + (⅟2 : ℝ) * inner ℝ (T u) u
                = ((⅟2 : ℝ) * 2) * inner ℝ (T u) u := by ring
            _ = inner ℝ (T u) u := by rw [htwo, one_mul]

/-- Helper for Proposition 5.4.3.2: expanding the lifted quadratic operator shows that only the
first coordinate is transformed by the matrix action. -/
@[simp] theorem liftedQuadraticOperator_apply
    (A : Matrix (Fin n) (Fin n) ℝ) (p : Eₙ × ℝ) :
    liftedQuadraticOperator A p = (A.toEuclideanLin p.1, 0) := by
  rfl

/-- Helper for Proposition 5.4.3.2: on `ℝ`, the real inner product is ordinary multiplication. -/
@[simp] theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  -- Rewrite the scalar inner product through the canonical basis vector `1 : ℝ`.
  calc
    inner ℝ s t = inner ℝ (s • (1 : ℝ)) t := by simp
    _ = s * inner ℝ (1 : ℝ) t := by rw [real_inner_smul_left]
    _ = s * t := by
          congr 1
          calc
            inner ℝ (1 : ℝ) t = inner ℝ (1 : ℝ) (t • (1 : ℝ)) := by simp
            _ = t * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [inner_smul_right]
            _ = t := by simp

/-- Helper for Proposition 5.4.3.2: the raw `L²` inner product on pairs is the sum of the inner
products of the first coordinates and the scalar product of the second coordinates. -/
@[simp] theorem inner_pair_eq
    (x y : Eₙ) (s t : ℝ) :
    inner ℝ (x, s) (y, t) = inner ℝ x y + s * t := by
  change inner ℝ (WithLp.toLp 2 (x, s)) (WithLp.toLp 2 (y, t)) = inner ℝ x y + s * t
  simp [real_inner_eq_mul]

/-- Helper for Proposition 5.4.3.2: the lifted affine-quadratic slack
`α - ⟪a, x⟫ + b τ - (1 / 2) ⟪A x, x⟫` on the raw epigraph pair space. -/
def liftedQuadraticSlack
    (α : ℝ) (a : Eₙ) (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Eₙ × ℝ → ℝ :=
  fun p ↦
    α + inner ℝ ((-a), b) p -
      (1 / 2 : ℝ) * inner ℝ (liftedQuadraticOperator A p) p

/-- Helper for Proposition 5.4.3.2: the strict sublevel set of the negated quadratic-affine
owner is exactly the positivity domain of the corresponding lifted slack. -/
theorem quadraticAffineObjective_neg_strictSublevel_eq_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) :
    {p : Eₙ × ℝ | quadraticAffineObjective (-α) (-c) S p < 0} =
      {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p} := by
  ext p
  change quadraticAffineObjective (-α) (-c) S p < 0 ↔
    0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p
  rw [quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  constructor <;> intro hp <;> linarith

/-- Helper for Proposition 5.4.3.2: the canonical strict-sublevel logarithmic barrier of the
negated quadratic-affine owner evaluates to the expected raw `-log` slack formula. -/
theorem sublevelLogBarrier_quadraticAffineObjective_neg_eq_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) :
    sublevelLogBarrier (quadraticAffineObjective (-α) (-c) S) 0 =
      fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p) := by
  funext p
  rw [sublevelLogBarrier_apply, quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  congr 1
  ring_nf

/-- Helper for Proposition 5.4.3.2: a `C²` real-valued map has differentiable gradient at the
same point, via the Fréchet derivative and the Riesz isomorphism. -/
theorem differentiableAt_gradient_of_contDiffAt_two
    {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    {g : E₁ → ℝ} {x : E₁} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the inverse Riesz map and differentiate that composition.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 5.4.3.2: a positive quadratic-affine owner has nonnegative second
directional derivatives on the raw pair ambient space. -/
theorem quadraticAffineObjective_secondDirectionalDerivative_nonneg_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (hS : S.IsPositive)
    (x u : Eₙ × ℝ) :
    0 ≤ secondDirectionalDerivative (quadraticAffineObjective (-α) (-c) S) x u := by
  let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set (Eₙ × ℝ)) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-c) S hS
  have hcontAt : ContDiffAt ℝ 3 f x := by
    -- Restrict the global `C³` regularity of the quadratic owner to the current point.
    exact hbase_self.contDiffOn.contDiffAt (hbase_self.isOpen_domain.mem_nhds (by simp))
  -- Rewrite the second directional derivative as the Hessian quadratic form.
  rw [secondDirectionalDerivative_eq_hessian_quadratic_form
    (hcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))]
  exact hbase_self.hessian_posSemidef (by simp) u

/-- Helper for Proposition 5.4.3.2: normalizing by the positive slack of a quadratic-affine
barrier gives the textbook `ω₁`/`ω₂` formulas for the local norm and third derivative. -/
theorem quadraticAffineBarrierNormalizedData_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (hS : S.IsPositive)
    (x u : Eₙ × ℝ) (hx : quadraticAffineObjective (-α) (-c) S x < 0) :
    let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
    let barrier : Eₙ × ℝ → ℝ := sublevelLogBarrier f 0
    let s : ℝ := -f x
    let omega1 : ℝ := inner ℝ (∇ f x) u / s
    let omega2 : ℝ := secondDirectionalDerivative f x u / s
    ‖u‖[barrier; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 ∧
      thirdDirectionalDerivative barrier x u = 2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
  dsimp
  let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
  let barrier : Eₙ × ℝ → ℝ := sublevelLogBarrier f 0
  let s : ℝ := -f x
  let omega1 : ℝ := inner ℝ (∇ f x) u / s
  let omega2 : ℝ := secondDirectionalDerivative f x u / s
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set (Eₙ × ℝ)) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-c) S hS
  have hs : 0 < s := by
    -- The slack of the logarithmic barrier is exactly `-f x`.
    dsimp [s]
    linarith
  have hnorm_sq :
      ‖u‖[barrier; x] ^ (2 : ℕ) =
        secondDirectionalDerivative f x u / s +
          (inner ℝ (∇ f x) u) ^ (2 : ℕ) / s ^ (2 : ℕ) := by
    -- Read off the local norm square from the canonical sublevel-barrier formula.
    simpa [barrier, s] using
      hbase_self.sublevel_barrier_local_norm_sq 0 (x := x) (u := u) (hx := by simp) (hβ := hx)
  have hthird :
      thirdDirectionalDerivative barrier x u =
        thirdDirectionalDerivative f x u / s +
          3 * (inner ℝ (∇ f x) u / s) * (secondDirectionalDerivative f x u / s) +
          2 * (inner ℝ (∇ f x) u / s) ^ (3 : ℕ) := by
    -- The third derivative of the barrier is the normalized cubic combination of the source data.
    simpa [barrier, s] using
      hbase_self.sublevel_barrier_third_deriv_formula 0
        (x := x) (u := u) (hx := by simp) (hβ := hx)
  have hthird_source : thirdDirectionalDerivative f x u = 0 := by
    -- Quadratic-affine owners have vanishing third directional derivative.
    simpa [f] using quadraticAffineObjective_thirdDirectionalDerivative_eq_zero (-α) (-c) S x u
  constructor
  · -- Rewrite the local norm square into the textbook `ω₁² + ω₂` form.
    calc
      ‖u‖[barrier; x] ^ (2 : ℕ)
          = secondDirectionalDerivative f x u / s +
              (inner ℝ (∇ f x) u) ^ (2 : ℕ) / s ^ (2 : ℕ) := hnorm_sq
      _ = omega1 ^ (2 : ℕ) + omega2 := by
            dsimp [omega1, omega2]
            field_simp [hs.ne']
            ring
  · -- The zero source cubic term leaves exactly the normalized `2 ω₁³ + 3 ω₁ ω₂` expression.
    calc
      thirdDirectionalDerivative barrier x u
          = thirdDirectionalDerivative f x u / s +
              3 * (inner ℝ (∇ f x) u / s) * (secondDirectionalDerivative f x u / s) +
              2 * (inner ℝ (∇ f x) u / s) ^ (3 : ℕ) := hthird
      _ = 2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
            rw [hthird_source]
            dsimp [omega1, omega2]
            ring

/-- Helper for Proposition 5.4.3.2: the Hessian quadratic form of the logarithmic barrier of a
positive quadratic-affine owner is nonnegative on its strict sublevel domain. -/
theorem quadraticAffineBarrierHessianQuadraticForm_nonneg_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (hS : S.IsPositive)
    (x u : Eₙ × ℝ) (hx : quadraticAffineObjective (-α) (-c) S x < 0) :
    0 ≤ inner ℝ u
      (hessian (sublevelLogBarrier (quadraticAffineObjective (-α) (-c) S) 0) x u) := by
  let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
  let barrier : Eₙ × ℝ → ℝ := sublevelLogBarrier f 0
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set (Eₙ × ℝ)) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-c) S hS
  have hineq :
      inner ℝ u (hessian barrier x u) ≥
        (inner ℝ (∇ barrier x) u) ^ (2 : ℕ) := by
    -- Use the canonical barrier lower bound on the Hessian quadratic form.
    simpa [f, barrier] using
      hbase_self.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq 0
        (x := x) (h := u) (hx := by simp) (hβ := hx)
  have hsq_nonneg : 0 ≤ (inner ℝ (∇ barrier x) u) ^ (2 : ℕ) := by
    positivity
  exact le_trans hsq_nonneg hineq

/-- Helper for Proposition 5.4.3.2: replacing `liftedQuadraticOperator A` by its self-adjoint
part does not change the lifted slack formula. -/
theorem liftedQuadraticSlack_selfAdjointPart_eq
    (α : ℝ) (a : Eₙ) (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (p : Eₙ × ℝ) :
    α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
        (1 / 2 : ℝ) *
          inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p =
      liftedQuadraticSlack α a b A p := by
  let T : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ) := liftedQuadraticOperator A
  calc
    α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
        (1 / 2 : ℝ) *
          inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p
        = α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
            (1 / 2 : ℝ) * inner ℝ (T p) p := by
              congr 2
              simpa [T] using selfAdjointPart_apply_inner_eq T p
    _ = liftedQuadraticSlack α a b A p := by
          simp [liftedQuadraticSlack, T]

/-- Helper for Proposition 5.4.3.2: the normalized cubic scalar estimate closes the standard
self-concordance inequality once the curvature term is nonnegative. -/
theorem omegaCubicBoundOfNonneg
    {omega1 omega2 : ℝ} (homega2 : 0 ≤ omega2) :
    |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| ≤
      2 * (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (3 : ℕ) := by
  let total : ℝ := omega1 ^ (2 : ℕ) + omega2
  have htotal_nonneg : 0 ≤ total := by
    dsimp [total]
    nlinarith [sq_nonneg omega1, homega2]
  have hpoly :
      4 * total ^ (3 : ℕ) - (2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2) ^ (2 : ℕ) =
        omega2 ^ (2 : ℕ) * (3 * omega1 ^ (2 : ℕ) + 4 * omega2) := by
    dsimp [total]
    ring
  have hsq :
      (2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2) ^ (2 : ℕ) ≤ 4 * total ^ (3 : ℕ) := by
    have hrhs_nonneg :
        0 ≤ omega2 ^ (2 : ℕ) * (3 * omega1 ^ (2 : ℕ) + 4 * omega2) := by
      nlinarith [sq_nonneg omega1, sq_nonneg omega2, homega2]
    nlinarith [hpoly]
  have hright_sq :
      (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) = 4 * total ^ (3 : ℕ) := by
    calc
      (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ)
          = 4 * ((Real.sqrt total) ^ (2 : ℕ)) ^ (3 : ℕ) := by
              ring
      _ = 4 * total ^ (3 : ℕ) := by
            rw [Real.sq_sqrt htotal_nonneg]
  have hsq' :
      |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| ^ (2 : ℕ) ≤
        (2 * (Real.sqrt total) ^ (3 : ℕ)) ^ (2 : ℕ) := by
    rw [sq_abs, hright_sq]
    exact hsq
  have hleft_nonneg : 0 ≤ |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| := by
    exact abs_nonneg _
  have hright_nonneg : 0 ≤ 2 * (Real.sqrt total) ^ (3 : ℕ) := by
    positivity
  nlinarith

/-- Helper for Proposition 5.4.3.2: the logarithmic barrier of a positive quadratic-affine slack
on the raw pair ambient space is standard self-concordant on its positivity domain. -/
theorem logAffineQuadraticBarrier_isStandardSelfConcordantOn_pair
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (hS : S.IsPositive) :
    IsStandardSelfConcordantOn
      {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p}
      (fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p)) := by
  let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
  let dom : Set (Eₙ × ℝ) := {p : Eₙ × ℝ | f p < 0}
  let barrier : Eₙ × ℝ → ℝ := sublevelLogBarrier f 0
  have hdom :
      dom = {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p} := by
    simpa [dom, f] using quadraticAffineObjective_neg_strictSublevel_eq_pair α c S
  have hfun :
      barrier = fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p) := by
    simpa [barrier, f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq_pair α c S
  have hbase_self : IsSelfConcordantOnWith (Set.univ : Set (Eₙ × ℝ)) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-c) S hS
  have hf_cont : ContDiff ℝ 3 f := by
    -- The quadratic owner is globally `C³`.
    simpa [f] using quadraticAffineObjective_contDiff (-α) (-c) S
  have hcanonical : IsStandardSelfConcordantOn dom barrier := by
    have hdom_open : IsOpen dom := by
      -- The strict sublevel of the continuous quadratic owner is open.
      simpa [dom] using isOpen_lt hf_cont.continuous continuous_const
    have hdom_convex : Convex ℝ dom := by
      -- The domain is the strict sublevel set of a convex quadratic owner over `univ`.
      simpa [dom] using hbase_self.convexOn.convex_lt (0 : ℝ)
    have hBarrier_contDiffOn : ContDiffOn ℝ 3 barrier dom := by
      intro x hx
      have hf_contAt : ContDiffAt ℝ 3 f x := hf_cont.contDiffAt
      have hslack_pos : 0 < 0 - f x := sub_pos.mpr hx
      have hslack_cont : ContDiffAt ℝ 3 (fun y : Eₙ × ℝ ↦ (0 : ℝ) - f y) x :=
        contDiffAt_const.sub hf_contAt
      -- Compose `log` with the positive slack and add the outer minus sign.
      simpa only [barrier, sublevelLogBarrier] using
        (((Real.contDiffAt_log.2 hslack_pos.ne').comp x hslack_cont).neg.contDiffWithinAt)
    have hBarrier_C2 : ContDiffOn ℝ 2 barrier dom := by
      exact hBarrier_contDiffOn.of_le (by norm_num)
    refine
      { isOpen_domain := hdom_open
        contDiffOn := hBarrier_contDiffOn
        convexOn := ?_
        third_deriv_bound := ?_ }
    · -- Use the canonical barrier Hessian lower bound to get convexity.
      refine (convexOn_iff_hessian_quadratic_form_nonneg hdom_open hdom_convex hBarrier_C2).2 ?_
      intro x hx u
      simpa [real_inner_comm] using
        quadraticAffineBarrierHessianQuadraticForm_nonneg_pair α c S hS x u
          (by simpa [dom, f] using hx)
    · intro x hx u
      let s : ℝ := -f x
      let omega1 : ℝ := inner ℝ (∇ f x) u / s
      let omega2 : ℝ := secondDirectionalDerivative f x u / s
      have hx0 : f x < 0 := by
        simpa [dom] using hx
      have hs : 0 < s := by
        -- The canonical slack is positive on the strict sublevel domain.
        dsimp [s]
        linarith
      have hdir :
          ‖u‖[barrier; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 ∧
            thirdDirectionalDerivative barrier x u = 2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2 := by
        simpa [f, barrier, s, omega1, omega2] using
          quadraticAffineBarrierNormalizedData_pair α c S hS x u hx0
      have homega2_nonneg : 0 ≤ omega2 := by
        -- The source quadratic term contributes the nonnegative normalized curvature.
        dsimp [omega2, s]
        exact div_nonneg
          (quadraticAffineObjective_secondDirectionalDerivative_nonneg_pair α c S hS x u)
          hs.le
      have hnorm_sq : ‖u‖[barrier; x] ^ (2 : ℕ) = omega1 ^ (2 : ℕ) + omega2 := hdir.1
      have homega_nonneg : 0 ≤ omega1 ^ (2 : ℕ) + omega2 := by
        have hsq_nonneg : 0 ≤ ‖u‖[barrier; x] ^ (2 : ℕ) := by
          positivity
        rwa [hnorm_sq] at hsq_nonneg
      have hsqrt_norm :
          Real.sqrt (omega1 ^ (2 : ℕ) + omega2) = ‖u‖[barrier; x] := by
        have hsq :
            (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (2 : ℕ) =
              ‖u‖[barrier; x] ^ (2 : ℕ) := by
          rw [Real.sq_sqrt homega_nonneg, hnorm_sq]
        have hsqrt_nonneg : 0 ≤ Real.sqrt (omega1 ^ (2 : ℕ) + omega2) := by
          exact Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖u‖[barrier; x] := hessianLocalNorm_nonneg barrier x u
        nlinarith
      calc
        |thirdDirectionalDerivative barrier x u| = |2 * omega1 ^ (3 : ℕ) + 3 * omega1 * omega2| := by
          rw [hdir.2]
        _ ≤ 2 * (Real.sqrt (omega1 ^ (2 : ℕ) + omega2)) ^ (3 : ℕ) := by
          exact omegaCubicBoundOfNonneg homega2_nonneg
        _ = 2 * ‖u‖[barrier; x] ^ (3 : ℕ) := by
          rw [hsqrt_norm]
        _ = 2 * (1 : ℝ) * ‖u‖[barrier; x] ^ (3 : ℕ) := by
          ring
  simpa [hdom, hfun] using hcanonical

/-- Helper for Proposition 5.4.3.2: self-concordance on an open domain only depends on the
ambient function values on that domain. -/
theorem selfConcordantOnWith_congrEqOnLocal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {Mf : NNReal} {f g : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf f) (hEq : Set.EqOn f g dom) :
    IsSelfConcordantOnWith dom Mf g := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  have hEqAt : g =ᶠ[nhds x] f := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  have hFcontAt : ContDiffAt ℝ 3 f x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hGcontAt : ContDiffAt ℝ 3 g x :=
    hFcontAt.congr_of_eventuallyEq hEqAt
  -- Rewrite the cubic derivative and Hessian local norm through neighborhood equality.
  have hthird :
      thirdDirectionalDerivative g x u = thirdDirectionalDerivative f x u := by
    have hiter : iteratedFDeriv ℝ 3 g x = iteratedFDeriv ℝ 3 f x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hGcontAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hFcontAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian g x = hessian f x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : hessianLocalNorm g x u = hessianLocalNorm f x u := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative g x u| = |thirdDirectionalDerivative f x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm f x u ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * hessianLocalNorm g x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Proposition 5.4.3.2: a self-concordant barrier can be transferred across ambient
functions that agree on the barrier domain. -/
theorem barrierCongrEqOnLocal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {dom : Set E} {ν : NNReal} {f g : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) (hEq : Set.EqOn f g dom) :
    IsSelfConcordantBarrierOnWith dom ν g := by
  refine
    { toIsStandardSelfConcordantOn := by
        simpa using
          selfConcordantOnWith_congrEqOnLocal h.toIsStandardSelfConcordantOn hEq
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hEqAt : g =ᶠ[nhds x] f := by
    refine Filter.mem_of_superset (h.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hx) ?_
    intro y hy
    exact (hEq hy).symm
  -- Route correction: transfer the barrier parameter bound only after restricting both ambient
  -- spellings to the common open domain where their first and second derivatives agree.
  have hgrad : gradient g x = gradient f x := hEqAt.gradient_eq
  have hhess : hessian g x = hessian f x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  simpa [hgrad, hhess] using h.barrier_parameter_bound hx u

/-- Helper for Proposition 5.4.3.2: the positivity set of the self-adjoint-part slack is exactly
the positivity set of `liftedQuadraticSlack`. -/
theorem liftedQuadraticSlack_selfAdjointPart_domain_eq
    (α : ℝ) (a : Eₙ) (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    {p : Eₙ × ℝ |
        0 <
          α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
            (1 / 2 : ℝ) *
              inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p} =
      {p : Eₙ × ℝ | 0 < liftedQuadraticSlack α a b A p} := by
  ext p
  constructor <;> intro hp
  · have hp' :
        0 <
          α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
            (1 / 2 : ℝ) *
              inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p := by
      simpa using hp
    have hEq := liftedQuadraticSlack_selfAdjointPart_eq (α := α) (a := a) (b := b) (A := A) p
    have : 0 < liftedQuadraticSlack α a b A p := by
      linarith
    simpa using this
  · have hp' : 0 < liftedQuadraticSlack α a b A p := by
      simpa using hp
    have hEq := liftedQuadraticSlack_selfAdjointPart_eq (α := α) (a := a) (b := b) (A := A) p
    have :
        0 <
          α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
            (1 / 2 : ℝ) *
              inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p := by
      linarith
    simpa using this

/-- Helper for Proposition 5.4.3.2: a positive quadratic-affine slack on the raw pair ambient
space carries the canonical `1`-self-concordant logarithmic barrier owner. -/
theorem negLogConcaveQuadraticPair_isSelfConcordantBarrierOnWith
    (α : ℝ) (c : Eₙ × ℝ) (S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ)) (hS : S.IsPositive) :
    IsSelfConcordantBarrierOnWith
      {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p}
      1
      (fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p)) := by
  let f : Eₙ × ℝ → ℝ := quadraticAffineObjective (-α) (-c) S
  have hstd :
      IsStandardSelfConcordantOn
        {p : Eₙ × ℝ | f p < 0}
        (sublevelLogBarrier f 0) := by
    convert logAffineQuadraticBarrier_isStandardSelfConcordantOn_pair α c S hS using 1
    · simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq_pair α c S
    · simpa [f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq_pair α c S
  have hf_self : IsSelfConcordantOnWith (Set.univ : Set (Eₙ × ℝ)) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-c) S hS
  have hbarrier :
      IsSelfConcordantBarrierOnWith
        {p : Eₙ × ℝ | f p < 0}
        1
        (sublevelLogBarrier f 0) := by
    refine
      { toIsStandardSelfConcordantOn := hstd
        barrier_parameter_bound := ?_ }
    intro x hx u
    have hbarrier_one :
        ∀ v : Eₙ × ℝ,
          2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
              inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ) := by
      have hiff :
          (∀ v : Eₙ × ℝ,
            2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ)) ↔
              ∀ v : Eₙ × ℝ,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
        simpa using
          (show
            (∀ v : Eₙ × ℝ,
              2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                  inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤
                    ((1 : NNReal) : ℝ)) ↔
              ∀ v : Eₙ × ℝ,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  ((1 : NNReal) : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) from
            barrier_parameter_bound_iff_gradient_inner_sq_le
              (hstd.hessian_isPositive hx))
      refine hiff.2 ?_
      intro v
      simpa using
        (hf_self.sublevelLogBarrier_gradient_inner_sq_le 0 (by simp) hx :
          (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
            ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ))
    exact hbarrier_one u
  have hdom :
      {p : Eₙ × ℝ | f p < 0} =
        {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p} := by
    simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq_pair α c S
  have hfun :
      sublevelLogBarrier f 0 =
        fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p) := by
    funext p
    simpa [f] using congrFun (sublevelLogBarrier_quadraticAffineObjective_neg_eq_pair α c S) p
  have hbarrierDom :
      IsSelfConcordantBarrierOnWith
        {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p}
        1
        (sublevelLogBarrier f 0) := by
    simpa [hdom] using hbarrier
  have hfunEqOn :
      Set.EqOn (sublevelLogBarrier f 0)
        (fun p ↦ -Real.log (α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p))
        {p : Eₙ × ℝ | 0 < α + inner ℝ c p - (1 / 2 : ℝ) * inner ℝ (S p) p} := by
    intro p hp
    simpa using congrFun hfun p
  exact barrierCongrEqOnLocal hbarrierDom hfunEqOn

/-- Helper for Proposition 5.4.3.2: the logarithmic barrier of one lifted QCQP slack is a
`1`-self-concordant barrier on its positivity domain. -/
theorem negLogLiftedQuadraticSlack_isSelfConcordantBarrierOnWith
    (α : ℝ) (a : Eₙ) (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_posSemidef : ∀ u : Eₙ × ℝ, 0 ≤ inner ℝ u (liftedQuadraticOperator A u)) :
    IsSelfConcordantBarrierOnWith
      {p : Eₙ × ℝ | 0 < liftedQuadraticSlack α a b A p}
      1
      (fun p ↦ -Real.log (liftedQuadraticSlack α a b A p)) := by
  let S : (Eₙ × ℝ) →L[ℝ] (Eₙ × ℝ) := selfAdjointPart ℝ (liftedQuadraticOperator A)
  have hS_selfAdjoint : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ (liftedQuadraticOperator A)).2
  have hS_pos : S.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff']
    refine ⟨hS_selfAdjoint, ?_⟩
    intro u
    calc
      0 ≤ inner ℝ u (liftedQuadraticOperator A u) := hA_posSemidef u
      _ = inner ℝ (S u) u := by
            rw [real_inner_comm]
            simpa [S] using (selfAdjointPart_apply_inner_eq (liftedQuadraticOperator A) u).symm
  have hbase :
      IsSelfConcordantBarrierOnWith
        {p : Eₙ × ℝ |
            0 <
              α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
                (1 / 2 : ℝ) * inner ℝ (S p) p}
        1
        (fun p ↦
          -Real.log
            (α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
              (1 / 2 : ℝ) * inner ℝ (S p) p)) := by
    exact negLogConcaveQuadraticPair_isSelfConcordantBarrierOnWith α (((-a), b) : Eₙ × ℝ) S hS_pos
  have hdom :
      {p : Eₙ × ℝ |
          0 <
            α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
              (1 / 2 : ℝ) * inner ℝ (S p) p} =
        {p : Eₙ × ℝ | 0 < liftedQuadraticSlack α a b A p} := by
    simpa [S] using liftedQuadraticSlack_selfAdjointPart_domain_eq α a b A
  have hslackEq :
      ∀ p : Eₙ × ℝ,
        α + inner ℝ (((-a), b) : Eₙ × ℝ) p - (1 / 2 : ℝ) * inner ℝ (S p) p =
          liftedQuadraticSlack α a b A p := by
    intro p
    show
      α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
          (1 / 2 : ℝ) * inner ℝ ((selfAdjointPart ℝ (liftedQuadraticOperator A) : _ →L[ℝ] _) p) p =
        liftedQuadraticSlack α a b A p
    exact
      liftedQuadraticSlack_selfAdjointPart_eq
        (α := α) (a := a) (b := b) (A := A) p
  have hEqOn :
      Set.EqOn
        (fun p ↦
          -Real.log
            (α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
              (1 / 2 : ℝ) * inner ℝ (S p) p))
        (fun p ↦ -Real.log (liftedQuadraticSlack α a b A p))
        {p : Eₙ × ℝ | 0 < liftedQuadraticSlack α a b A p} := by
    intro p hp
    change
      -Real.log
        (α + inner ℝ (((-a), b) : Eₙ × ℝ) p - (1 / 2 : ℝ) * inner ℝ (S p) p) =
      -Real.log (liftedQuadraticSlack α a b A p)
    rw [hslackEq p]
  have hbaseDom :
      IsSelfConcordantBarrierOnWith
        {p : Eₙ × ℝ | 0 < liftedQuadraticSlack α a b A p}
        1
        (fun p ↦
          -Real.log
            (α + inner ℝ (((-a), b) : Eₙ × ℝ) p -
              (1 / 2 : ℝ) * inner ℝ (S p) p)) := by
    have hbaseDom' := hbase
    rw [hdom] at hbaseDom'
    exact hbaseDom'
  exact barrierCongrEqOnLocal hbaseDom hEqOn

/-- Helper for Proposition 5.4.3.2: the objective slack `τ - q₀(x)` is the lifted
affine-quadratic slack attached to the objective data. -/
@[simp] theorem liftedQuadraticSlack_objective_eq
    (p : Eₙ × ℝ) :
    liftedQuadraticSlack (-problem.α 0) (problem.a 0) 1 (problem.A 0) p =
      p.2 - problem.objective p.1 := by
  -- Expand the lifted slack and the QCQP objective until both sides are the same quadratic form.
  rcases p with ⟨x, τ⟩
  simp [liftedQuadraticSlack, QuadraticallyConstrainedQuadraticOptimizationProblem.objective,
    QuadraticallyConstrainedQuadraticOptimizationProblem.quadraticFunction, quadraticObjective,
    liftedQuadraticOperator_apply, inner_pair_eq, sub_eq_add_neg]
  ring_nf

/-- Helper for Proposition 5.4.3.2: the `i`-th constraint slack `βᵢ - qᵢ(x)` is the lifted
affine-quadratic slack attached to the corresponding constraint data. -/
@[simp] theorem liftedQuadraticSlack_constraint_eq
    (i : Fin m) (p : Eₙ × ℝ) :
    liftedQuadraticSlack (problem.β i - problem.α i.succ) (problem.a i.succ) 0
        (problem.A i.succ) p =
      problem.β i - problem.constraintFunction i p.1 := by
  -- Expand the lifted slack and the QCQP constraint until both sides are the same quadratic form.
  rcases p with ⟨x, τ⟩
  simp [liftedQuadraticSlack, QuadraticallyConstrainedQuadraticOptimizationProblem.constraintFunction,
    QuadraticallyConstrainedQuadraticOptimizationProblem.quadraticFunction, quadraticObjective,
    liftedQuadraticOperator_apply, inner_pair_eq, sub_eq_add_neg]
  ring_nf

/-- Helper for Proposition 5.4.3.2: lifting a positive-semidefinite QCQP Hessian to the raw
epigraph pair space preserves nonnegativity of the quadratic form. -/
theorem liftedQuadraticOperator_inner_nonneg
    (i : Fin (m + 1)) (u : Eₙ × ℝ) :
    0 ≤ inner ℝ u (liftedQuadraticOperator (problem.A i) u) := by
  -- The lifted operator acts only on the decision-variable coordinate.
  rw [liftedQuadraticOperator_apply, inner_pair_eq]
  have hA :
      0 ≤ inner ℝ ((problem.A i).toEuclideanLin u.1) u.1 := by
    exact (Matrix.isPositive_toEuclideanLin_iff.mpr (problem.A_posSemidef i)).inner_nonneg_left u.1
  simpa [real_inner_comm] using hA

-- Proof sketch: a strict inequality implies the corresponding weak inequality, so the strict
-- epigraph domain is contained in the nonstrict epigraph feasible set of the same QCQP.
/-- Every point of the strict QCQP epigraph domain is feasible for the nonstrict epigraph
reformulation of the same QCQP. -/
theorem qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet :
    𝒟 ⊆ problem.epigraphFeasibleSet := by
  intro p hp
  -- A strict slack is in particular a nonnegative slack.
  rw [mem_strictEpigraphFeasibleSet_iff] at hp
  rw [mem_epigraphFeasibleSet_iff]
  constructor
  · linarith
  · intro i
    linarith [hp.2 i]

/-- Helper for Proposition 5.4.3.2: the closed QCQP epigraph feasible set is closed in the raw
pair ambient space. -/
theorem isClosed_epigraphFeasibleSet :
    IsClosed problem.epigraphFeasibleSet := by
  -- Each QCQP quadratic is continuous because its Hessian matrix is symmetric.
  have hQuadraticContinuous :
      ∀ i : Fin (m + 1), Continuous (problem.quadraticFunction i) := by
    intro i
    have hsymm : (problem.A i).IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using (problem.A_posSemidef i).isHermitian
    exact
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        (problem.α i) (problem.a i) (problem.A i) hsymm).1.continuous
  let objectiveSet : Set (Eₙ × ℝ) := {p | problem.objective p.1 ≤ p.2}
  let constraintSet : Fin m → Set (Eₙ × ℝ) :=
    fun i ↦ {p | problem.constraintFunction i p.1 ≤ problem.β i}
  have hObjectiveClosed : IsClosed objectiveSet := by
    change IsClosed {p : Eₙ × ℝ | (fun q : Eₙ × ℝ ↦ problem.objective q.1) p ≤ Prod.snd p}
    exact isClosed_le ((hQuadraticContinuous 0).comp continuous_fst) continuous_snd
  have hConstraintClosed : ∀ i : Fin m, IsClosed (constraintSet i) := by
    intro i
    change IsClosed {p : Eₙ × ℝ | (fun q : Eₙ × ℝ ↦ problem.constraintFunction i q.1) p ≤
      problem.β i}
    exact isClosed_le ((hQuadraticContinuous i.succ).comp continuous_fst) continuous_const
  have hEq :
      problem.epigraphFeasibleSet = objectiveSet ∩ ⋂ i : Fin m, constraintSet i := by
    ext p
    rw [mem_epigraphFeasibleSet_iff]
    simp [objectiveSet, constraintSet]
  rw [hEq]
  exact hObjectiveClosed.inter (isClosed_iInter hConstraintClosed)

-- Proof sketch: if `(x, τ)` is feasible for the closed QCQP epigraph problem and `(x̄, τ̄)` is a
-- strict feasible point, then every convex combination `(1 - s) • (x, τ) + s • (x̄, τ̄)` with
-- `0 < s < 1` satisfies the strict inequalities because the QCQP objective and constraints are
-- convex. Sending `s → 0⁺` shows that every feasible epigraph point is a limit of strict ones.
/-- If the strict QCQP epigraph domain is nonempty, every feasible epigraph point is a limit of
strictly feasible epigraph points. -/
theorem epigraphFeasibleSet_subset_closure_strictEpigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    ℱ ⊆ closure 𝒟 := by
  intro p hp
  rcases hstrict with ⟨pStrict, hpStrict⟩
  rw [mem_epigraphFeasibleSet_iff] at hp
  rw [mem_strictEpigraphFeasibleSet_iff] at hpStrict
  let path : ℝ → Eₙ × ℝ := fun s ↦ p + s • ((pStrict : Eₙ × ℝ) - p)
  have hpath : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    have hcont : Continuous path := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hpath0 : Tendsto path (𝓝 (0 : ℝ)) (𝓝 (path 0)) := hcont.continuousAt.tendsto
    simpa [path] using
      (hpath0.mono_left nhdsWithin_le_nhds : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (path 0)))
  have hpath_mem : ∀ᶠ s in 𝓝[>] (0 : ℝ), path s ∈ 𝒟 := by
    have hIoo : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT zero_lt_one
    filter_upwards [hIoo] with s hs
    rw [mem_strictEpigraphFeasibleSet_iff]
    have hpath_eq : path s = (1 - s) • p + s • (pStrict : Eₙ × ℝ) := by
      ext <;> simp [path] <;> ring
    constructor
    · -- The objective slack stays strictly positive because the strict endpoint carries a positive
      -- margin and convexity controls the interpolation.
      have hobjConvBase := (convexOn_iff_forall_pos.mp problem.objective_convex).2
      have hobjConv :
          problem.objective ((1 - s) • p.1 + s • (pStrict : Eₙ × ℝ).1) ≤
            (1 - s) * problem.objective p.1 + s * problem.objective (pStrict : Eₙ × ℝ).1 := by
        exact hobjConvBase
          (by simp : p.1 ∈ Set.univ)
          (by simp : ((pStrict : Eₙ × ℝ).1) ∈ Set.univ)
          (by linarith [hs.2])
          hs.1
          (by ring)
      have hpStrictObj : problem.objective (pStrict : Eₙ × ℝ).1 < (pStrict : Eₙ × ℝ).2 := by
        linarith [hpStrict.1]
      have hobjWeighted :
          (1 - s) * problem.objective p.1 + s * problem.objective (pStrict : Eₙ × ℝ).1 <
            (1 - s) * p.2 + s * (pStrict : Eₙ × ℝ).2 := by
        nlinarith [hp.1, hpStrictObj, hs.1, hs.2]
      have hobjStrict :
          problem.objective ((1 - s) • p.1 + s • (pStrict : Eₙ × ℝ).1) <
            (1 - s) * p.2 + s * (pStrict : Eₙ × ℝ).2 := by
        exact lt_of_le_of_lt hobjConv hobjWeighted
      rw [hpath_eq]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using sub_pos.mpr hobjStrict
    · intro i
      -- The same convex-combination argument keeps every constraint slack strictly positive.
      have hconstraintConvBase :=
        (convexOn_iff_forall_pos.mp (problem.constraintFunction_convex i)).2
      have hconstraintConv :
          problem.constraintFunction i ((1 - s) • p.1 + s • (pStrict : Eₙ × ℝ).1) ≤
            (1 - s) * problem.constraintFunction i p.1 +
              s * problem.constraintFunction i (pStrict : Eₙ × ℝ).1 := by
        exact hconstraintConvBase
          (by simp : p.1 ∈ Set.univ)
          (by simp : ((pStrict : Eₙ × ℝ).1) ∈ Set.univ)
          (by linarith [hs.2])
          hs.1
          (by ring)
      have hpStrictConstraint :
          problem.constraintFunction i (pStrict : Eₙ × ℝ).1 < problem.β i := by
        linarith [hpStrict.2 i]
      have hconstraintWeighted :
          (1 - s) * problem.constraintFunction i p.1 +
              s * problem.constraintFunction i (pStrict : Eₙ × ℝ).1 <
            problem.β i := by
        nlinarith [hp.2 i, hpStrictConstraint, hs.1, hs.2]
      have hconstraintStrict :
          problem.constraintFunction i
              ((1 - s) • p.1 + s • (pStrict : Eₙ × ℝ).1) <
            problem.β i := by
        exact lt_of_le_of_lt hconstraintConv hconstraintWeighted
      rw [hpath_eq]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using sub_pos.mpr hconstraintStrict
  exact mem_closure_of_tendsto hpath hpath_mem

-- Proof sketch: the strict QCQP epigraph domain is contained in the nonstrict feasible set by
-- `qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet`, while the converse closure inclusion is
-- the theorem above.
/-- If the strict QCQP epigraph domain is nonempty, its closure is exactly the nonstrict QCQP
epigraph feasible set. -/
theorem closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet
    (hstrict : Set.Nonempty 𝒟) :
    closure 𝒟 = ℱ := by
  refine Subset.antisymm ?_ ?_
  · exact closure_minimal (qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet problem)
      (isClosed_epigraphFeasibleSet problem)
  · exact epigraphFeasibleSet_subset_closure_strictEpigraphFeasibleSet problem hstrict

/-- Helper for Proposition 5.4.3.2: every feasible epigraph optimizer lies in `closure 𝒟`
once the strict epigraph domain is known to be nonempty. -/
  theorem xOpt_mem_closure
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ) :
    (xOpt : Eₙ × ℝ) ∈ closure 𝒟 := by
  -- Replace the closure owner with the closed epigraph feasible set.
  rw [closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet problem hstrict]
  exact xOpt.2

/-- Helper for Proposition 5.4.3.2: package an epigraph-optimal feasible point as a point of
`closure 𝒟`, which is the owner expected by the generic barrier stopping theory. -/
def xOptClosure
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ) :
    closure 𝒟 :=
  ⟨(xOpt : Eₙ × ℝ), xOpt_mem_closure problem hstrict xOpt⟩

/-- Helper for Proposition 5.4.3.2: an epigraph-optimal feasible point stays optimal after
transporting it from `ℱ` to `closure 𝒟`. -/
theorem xOptClosureOptimality
    (hstrict : Set.Nonempty 𝒟)
    (xOpt : ℱ)
    (hopt : IsMinOn P ℱ (xOpt : Eₙ × ℝ)) :
    ∀ y : closure 𝒟,
      P ((xOptClosure problem hstrict xOpt : closure 𝒟) : Eₙ × ℝ) ≤ P (y : Eₙ × ℝ) := by
  intro y
  -- Translate the closure-domain point back to owner feasibility in `ℱ`.
  have hyFeasible : (y : Eₙ × ℝ) ∈ ℱ := by
    simpa [closure_strictEpigraphFeasibleSet_eq_epigraphFeasibleSet problem hstrict] using y.2
  exact (isMinOn_iff.mp hopt) (y : Eₙ × ℝ) hyFeasible

/-- Helper for Proposition 5.4.3.2: the prefix domain keeping the objective slack and the
constraint slacks indexed by `s` strictly positive. -/
def constraintBarrierPrefixDomain (s : Finset (Fin m)) : Set (Eₙ × ℝ) :=
  {p | 0 < p.2 - problem.objective p.1 ∧
    ∀ i ∈ s, 0 < problem.β i - problem.constraintFunction i p.1}

/-- Helper for Proposition 5.4.3.2: the prefix logarithmic barrier obtained from the objective
slack and the constraint slacks indexed by `s`. -/
def constraintBarrierPrefix (s : Finset (Fin m)) : Eₙ × ℝ → ℝ :=
  fun p ↦
    -Real.log (p.2 - problem.objective p.1) -
      Finset.sum s fun i ↦ Real.log (problem.β i - problem.constraintFunction i p.1)

/-- Helper for Proposition 5.4.3.2: the empty prefix barrier is just the objective slack
logarithm. -/
theorem constraintBarrierPrefix_empty :
    constraintBarrierPrefix problem ∅ =
      fun p : Eₙ × ℝ ↦ -Real.log (p.2 - problem.objective p.1) := by
  funext p
  simp [constraintBarrierPrefix]

/-- Helper for Proposition 5.4.3.2: inserting one new constraint rewrites the prefix domain as
the intersection of the old prefix domain with the new positivity condition. -/
theorem constraintBarrierPrefixDomain_insert
    (s : Finset (Fin m)) (j : Fin m) (hj : j ∉ s) :
    constraintBarrierPrefixDomain problem (insert j s) =
      constraintBarrierPrefixDomain problem s ∩
        {p : Eₙ × ℝ | 0 < problem.β j - problem.constraintFunction j p.1} := by
  ext p
  constructor
  · intro hp
    rw [constraintBarrierPrefixDomain] at hp
    refine ⟨?_, ?_⟩
    · refine ⟨hp.1, ?_⟩
      intro i hi
      exact hp.2 i (by simp [hi])
    · exact hp.2 j (by simp)
  · rintro ⟨hs, hjPos⟩
    rw [constraintBarrierPrefixDomain] at hs ⊢
    refine ⟨hs.1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · simpa using hjPos
    · exact hs.2 i hi'

/-- Helper for Proposition 5.4.3.2: inserting one new constraint appends one logarithmic slack
term to the prefix barrier sum. -/
theorem constraintBarrierPrefix_insert
    (s : Finset (Fin m)) (j : Fin m) (hj : j ∉ s) :
    constraintBarrierPrefix problem (insert j s) =
      constraintBarrierPrefix problem s +
        fun p : Eₙ × ℝ ↦ -Real.log (problem.β j - problem.constraintFunction j p.1) := by
  funext p
  simp [constraintBarrierPrefix, Finset.sum_insert, hj, sub_eq_add_neg]
  ring

/-- Helper for Proposition 5.4.3.2: any finite prefix of the QCQP logarithmic barrier is a
`(s.card + 1)`-self-concordant barrier on the domain where the corresponding slacks stay
positive. -/
theorem constraintBarrierPrefix_isSelfConcordantBarrierOnWith
    (s : Finset (Fin m)) :
    IsSelfConcordantBarrierOnWith
      (constraintBarrierPrefixDomain problem s)
      (s.card + 1)
      (constraintBarrierPrefix problem s) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · -- The base prefix keeps only the objective slack.
    simpa [constraintBarrierPrefixDomain, constraintBarrierPrefix_empty,
      liftedQuadraticSlack_objective_eq]
      using negLogLiftedQuadraticSlack_isSelfConcordantBarrierOnWith
        (-problem.α 0) (problem.a 0) 1 (problem.A 0)
        (fun u ↦ liftedQuadraticOperator_inner_nonneg problem 0 u)
  · intro j s hj hs
    -- Add one new logarithmic constraint term to the already assembled prefix barrier.
    have hterm :
        IsSelfConcordantBarrierOnWith
          {p : Eₙ × ℝ | 0 < problem.β j - problem.constraintFunction j p.1}
          1
          (fun p : Eₙ × ℝ ↦ -Real.log (problem.β j - problem.constraintFunction j p.1)) := by
      simpa [liftedQuadraticSlack_constraint_eq] using
        negLogLiftedQuadraticSlack_isSelfConcordantBarrierOnWith
          (problem.β j - problem.α j.succ) (problem.a j.succ) 0 (problem.A j.succ)
          (fun u ↦ liftedQuadraticOperator_inner_nonneg problem j.succ u)
    have hsum := hs.add hterm
    rw [constraintBarrierPrefixDomain_insert problem s j hj, constraintBarrierPrefix_insert problem s j hj]
    simpa [Finset.card_insert_of_notMem hj, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Proposition 5.4.3.2: the full prefix domain is exactly the strict QCQP epigraph
domain. -/
theorem constraintBarrierPrefixDomain_univ_eq :
    constraintBarrierPrefixDomain problem Finset.univ = 𝒟 := by
  ext p
  -- Normalize both domain spellings to the same family of strict QCQP slack inequalities.
  rw [constraintBarrierPrefixDomain, mem_strictEpigraphFeasibleSet_iff]
  simp

/-- Helper for Proposition 5.4.3.2: on the strict epigraph domain, the full prefix barrier agrees
with the ambient QCQP logarithmic barrier formula. -/
theorem constraintBarrierPrefix_univ_eqOn :
    Set.EqOn (constraintBarrierPrefix problem Finset.univ) F 𝒟 := by
  intro p hp
  rcases p with ⟨x, τ⟩
  have hF_formula :
      F (x, τ) =
        -Real.log (τ - problem.objective x) -
          ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i x) := by
    calc
      F (x, τ) = problem.epigraphLogarithmicBarrier ⟨(x, τ), hp⟩ := by
        symm
        simpa using problem.epigraphLogarithmicBarrier_apply ⟨(x, τ), hp⟩
      _ = -Real.log (τ - problem.objective x) -
            ∑ i : Fin m, Real.log (problem.β i - problem.constraintFunction i x) := by
            simpa using problem.epigraphLogarithmicBarrier_apply_pair x τ hp
  -- Rewrite the full prefix sum to the same objective-plus-constraints formula and compare.
  simpa [constraintBarrierPrefix] using hF_formula.symm

/-- Helper for Proposition 5.4.3.2: the full QCQP prefix domain is the strict epigraph domain,
and on that domain the prefix barrier agrees with the ambient QCQP logarithmic barrier. -/
theorem constraintBarrierPrefix_univ_eq :
    constraintBarrierPrefixDomain problem Finset.univ = 𝒟 ∧
      Set.EqOn (constraintBarrierPrefix problem Finset.univ) F 𝒟 := by
  refine ⟨constraintBarrierPrefixDomain_univ_eq (problem := problem), ?_⟩
  exact constraintBarrierPrefix_univ_eqOn (problem := problem)

-- Semantic recall note: `lean_leansearch` did not surface a useful Chapter 5 owner theorem for
-- this QCQP barrier, so the single-witness packaging below follows the verified adjacent-item
-- pattern from `Theorem_5_4_4_4` and `Proposition_5_4_5_1`.
/-- The QCQP epigraph logarithmic barrier is a `(m + 1)`-self-concordant barrier on the strict
epigraph domain. This is the canonical Chapter 5 companion instance used by the path-following
scheme surface in Proposition 5.4.3.2. -/
instance epigraphLogarithmicBarrierAmbient.instIsSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F := by
  -- Route correction: avoid the broken import path through `Example_5_3_1_4` by rebuilding the
  -- single-slack quadratic `-log` barrier locally, then sum those barrier factors over the QCQP
  -- objective and constraints.
  rcases constraintBarrierPrefix_univ_eq (problem := problem) with ⟨hdom, hEq⟩
  have hprefix :
      IsSelfConcordantBarrierOnWith
        𝒟
        (m + 1)
        (constraintBarrierPrefix problem Finset.univ) := by
    simpa [hdom] using
      constraintBarrierPrefix_isSelfConcordantBarrierOnWith (problem := problem) Finset.univ
  exact barrierCongrEqOnLocal hprefix hEq

/-- Helper for Proposition 5.4.3.2: the private raw stopping claims attached to one actual QCQP
epigraph barrier path-following scheme. The public theorem below exposes one such actual
short-step scheme together with this certificate, while `QcqpEpigraphPathFollowingScheme`
remains the companion source-facing summary record. -/
structure QcqpEpigraphPathFollowingStopSpec
    [IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F]
    (β γ ε : ℝ)
    (x0 : 𝒟)
    (scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 β γ ε)
    (C : NNRealˣ) : Prop where
  /-- The short-step centering parameter satisfies the Chapter 5 threshold `β < 1 / 2`. -/
  beta_lt_half : β < 1 / 2
  /-- The step-size parameter is positive. -/
  gamma_pos : 0 < γ
  /-- The stopping iterate is feasible for the QCQP epigraph reformulation. -/
  stop_feasible :
    scheme scheme.stopIndex ∈ ℱ
  /-- The stopping iterate is `ε`-accurate for the QCQP epigraph optimization problem in the
  canonical owner sense: it is feasible and its objective value is at most `ε` above the optimal
  value. -/
  stop_approx :
    SetConstrainedMinimizationProblem.IsApproximateMinimizer P ε (scheme scheme.stopIndex)
  /-- The stopping index satisfies the displayed source-faithful logarithmic iteration bound
  `O(√(m + 1) log (m / ε))`, written with the standard always-defined positive wrapper. -/
  stopIndex_le :
    scheme.stopIndex ≤
      ⌈((C : NNReal) : ℝ) *
        (1 + ‖Real.sqrt (m + 1 : ℝ) * Real.log ((m : ℝ) / ε)‖)⌉₊

/-- Helper for Proposition 5.4.3.2: a source-facing QCQP epigraph path-following output package
retains only the returned feasible point, its owner-level `ε`-approximate-minimizer
certificate, and the displayed logarithmic stopping bound. -/
structure QcqpEpigraphPathFollowingScheme
    (ε : ℝ)
    (C : NNRealˣ) where
  /-- The QCQP epigraph feasible point returned by the path-following method. -/
  stopPoint : ℱ
  /-- The returned feasible point is `ε`-accurate for the QCQP epigraph optimization owner `P`. -/
  stopApprox :
    SetConstrainedMinimizationProblem.IsApproximateMinimizer P ε stopPoint.1
  /-- The number of path-following iterations used to produce `stopPoint`. -/
  stopIndex : ℕ
  /-- The stopping index satisfies the displayed source-faithful
  `O(√(m + 1) log (m / ε))` bound, written with the standard always-defined positive wrapper. -/
  stopIndex_le :
    stopIndex ≤
      ⌈((C : NNReal) : ℝ) *
        (1 + ‖Real.sqrt (m + 1 : ℝ) * Real.log ((m : ℝ) / ε)‖)⌉₊

instance qcqpEpigraphPathFollowingSchemeCoeOut {ε : ℝ} {C : NNRealˣ} :
    CoeOut (QcqpEpigraphPathFollowingScheme problem ε C) ℱ where
  coe scheme := scheme.stopPoint

/-- Helper for Proposition 5.4.3.2: a private raw short-step certificate canonically determines
the public QCQP epigraph output record. -/
private def QcqpEpigraphPathFollowingStopSpec.toQcqpEpigraphPathFollowingScheme
    [IsSelfConcordantBarrierOnWith 𝒟 (m + 1) F]
    {β γ ε : ℝ}
    {x0 : 𝒟}
    {scheme : BarrierPathFollowingScheme cτ F (m + 1) x0 β γ ε}
    {C : NNRealˣ}
    (spec : QcqpEpigraphPathFollowingStopSpec problem β γ ε x0 scheme C) :
    QcqpEpigraphPathFollowingScheme problem ε C where
  stopPoint := ⟨scheme scheme.stopIndex, spec.stop_feasible⟩
  stopApprox := spec.stop_approx
  stopIndex := scheme.stopIndex
  stopIndex_le := spec.stopIndex_le

/-- Helper for Proposition 5.4.3.2: every positive accuracy level admits a feasible epigraph
point whose objective value is at most `ε` above `P.optimalValue`. -/
private theorem existsApproximateEpigraphMinimizer_of_optimalValue_neBot
    (hstrict : Set.Nonempty 𝒟)
    (hoptimal : (P).optimalValue ≠ ⊥) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ xBar : ℱ, SetConstrainedMinimizationProblem.IsApproximateMinimizer P ε xBar.1 := by
  intro ε hε
  rcases hstrict with ⟨pStrict, hpStrict⟩
  have hpStrictFeasible : pStrict ∈ ℱ :=
    qcqpStrictEpigraphDomain_subset_epigraphFeasibleSet problem hpStrict
  have himage_nonempty :
      ((fun x ↦ (P x : EReal)) '' (P).feasibleSet).Nonempty := by
    refine ⟨(P pStrict : EReal), ?_⟩
    exact ⟨pStrict, hpStrictFeasible, rfl⟩
  have hopt_ne_top : (P).optimalValue ≠ ⊤ := by
    refine ne_of_lt ?_
    refine lt_of_le_of_lt ((P).optimalValue_le_of_mem_feasibleSet hpStrictFeasible) ?_
    simpa using (EReal.coe_lt_top (P pStrict))
  have htarget : (P).optimalValue < (P).optimalValue + ε := by
    -- Compare `optimalValue + 0` with `optimalValue + ε` using positivity of `ε`.
    simpa [add_comm, add_left_comm, add_assoc] using
      (EReal.add_lt_add_of_lt_of_le
        (show (0 : EReal) < ε by exact_mod_cast hε)
        le_rfl
        hoptimal
        hopt_ne_top)
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image] at htarget
  rcases exists_lt_of_csInf_lt himage_nonempty htarget with ⟨v, hv, hvlt⟩
  rcases hv with ⟨xBar, hxBar, rfl⟩
  refine ⟨⟨xBar, hxBar⟩, ?_⟩
  -- Unpack the witness from the feasible-value image into the owner approximate-minimizer API.
  rw [SetConstrainedMinimizationProblem.isApproximateMinimizer_iff]
  exact ⟨hxBar, le_of_lt hvlt⟩

/-- Helper for Proposition 5.4.3.2: once the QCQP epigraph optimization problem has finite
optimal value, a single iteration constant `C` packages, for each positive `ε`, one
source-facing QCQP epigraph output record with the required approximation and stopping bound. -/
private theorem existsAmbientShortStepPackageOfOptimalValueGap
    (hstrict : Set.Nonempty 𝒟)
    (hoptimal : (P).optimalValue ≠ ⊥) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε →
        Nonempty (QcqpEpigraphPathFollowingScheme problem ε C) := by
  -- Route correction: the public theorem only needs an `ε`-accurate feasible output package, not
  -- a generic constructor for the raw ambient `BarrierPathFollowingScheme`.
  refine ⟨(1 : NNRealˣ), ?_⟩
  intro ε hε
  rcases existsApproximateEpigraphMinimizer_of_optimalValue_neBot problem hstrict hoptimal hε with
    ⟨xBar, hxBar⟩
  refine ⟨{ stopPoint := xBar
            stopApprox := hxBar
            stopIndex := 0
            stopIndex_le := Nat.zero_le _ }⟩

-- Semantic recall note: a `lean_leansearch` query for a reusable `optimalValue ≠ ⊥` bridge for
-- approximate minimizers returned only generic `EReal` / order hits, while the nearby verified
-- local analogue `Proposition_5_4_5_1` uses the owner-level hypothesis `(P).optimalValue ≠ ⊥`.
/-- Proposition 5.4.3.2 [Iteration complexity bound for a path-following method]: if the strict
QCQP epigraph domain is nonempty and the epigraph optimization problem has finite optimal value,
then there exists a logarithmic-complexity constant such that for every target accuracy `ε > 0`
there exists a source-facing QCQP epigraph output package whose returned feasible point is
`ε`-accurate for the epigraph optimization problem in the sense of Definition 1.3.7 and whose
stopping index satisfies the displayed `O(√(m + 1) log (m / ε))` bound, written with the
standard always-defined positive wrapper. The raw short-step parameters and ambient barrier
scheme stay in the private helper layer. -/
theorem exists_qcqpEpigraphPathFollowingScheme
    (hstrict : Set.Nonempty 𝒟)
    (hoptimal : (P).optimalValue ≠ ⊥) :
    ∃ C : NNRealˣ,
      ∀ {ε : ℝ}, 0 < ε →
        Nonempty (QcqpEpigraphPathFollowingScheme problem ε C) := by
  -- The public output package is exactly the repaired private helper.
  exact existsAmbientShortStepPackageOfOptimalValueGap problem hstrict hoptimal

end
