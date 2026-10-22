/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The scalar epigraph Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic model. -/
def cubicRegularizedQuadraticScalarLagrangian
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) : ℝ :=
  dotProduct g h +
    (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) +
        lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ)

/-- The scalar dual function `ψ(λ)` obtained by infimizing the epigraph Lagrangian over
`(h, τ) ∈ ℝⁿ × ℝ`. -/
def cubicRegularizedQuadraticDualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (lam : ℝ) : EReal :=
  sInf (Set.range fun z : E × ℝ ↦
    (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal))

/-- Expanding `cubicRegularizedQuadraticDualFunction g H M lam` gives the infimum definition of
`ψ(λ)`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      sInf (Set.range fun z : E × ℝ ↦
        (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal)) :=
  rfl

/-- The effective domain `dom ψ = {λ | ψ(λ) > -∞}` of the scalar dual function. -/
def cubicRegularizedQuadraticDualDomain
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Set ℝ :=
  { lam | ⊥ < cubicRegularizedQuadraticDualFunction g H M lam }

/-- The explicit slack-variable minimizer `τ(λ) = 4 λ |λ| / M²`. -/
def cubicRegularizedQuadraticTauMinimizer
    (M lam : ℝ) : ℝ :=
  (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ)

/-- Helper for Proposition 4.1.8: the zero-offset quadratic owner agrees with the displayed
coordinate formula `⟪g, h⟫ + (1 / 2) ⟪Ah, h⟫`. -/
lemma quadraticObjective_zero_eq_dotProduct
    (g : E) (A : Matrix (Fin n) (Fin n) ℝ) (h : E) :
    quadraticObjective 0 g A h =
      dotProduct g h + (1 / 2 : ℝ) * dotProduct (A.mulVec h) h := by
  -- Convert the abstract inner products in `quadraticObjective` to the coordinate `dotProduct`
  -- form used by the scalar Lagrangian.
  rw [quadraticObjective]
  have hg : inner ℝ g h = dotProduct g h := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct g h)
  have hA : inner ℝ (A.toEuclideanLin h) h = dotProduct (A.mulVec h) h := by
    simpa [Matrix.toLpLin_apply, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin h) h)
  rw [hg, hA]
  ring

/-- Helper for Proposition 4.1.8: the scalar Lagrangian splits into the shifted quadratic
`q_λ(h)` plus the pure slack-variable objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
      quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Separate the `h`-dependent quadratic part from the scalar `τ`-objective.
  rw [cubicRegularizedQuadraticScalarLagrangian, quadraticObjective_zero_eq_dotProduct]
  have hnorm : dotProduct h h = ‖h‖ ^ (2 : ℕ) := by
    -- The identity-matrix contribution is exactly the Euclidean norm square.
    have hdot := (EuclideanSpace.inner_eq_star_dotProduct h h).symm
    simp at hdot
    exact hdot.trans (real_inner_self_eq_norm_sq h)
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hnorm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, mul_add]
  ring

/-- Helper for Proposition 4.1.8: the slack objective is bounded below by the explicit cubic
penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_ge_minValue
    (M : ℝ) (lam : ℝ) (hM : 0 < M) (τ : ℝ) :
    -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
  -- First dominate the linear term by replacing `lam * τ` with `|lam| * |τ|`.
  have hlin : -(|lam| / 2 : ℝ) * |τ| ≤ -(lam / 2 : ℝ) * τ := by
    have hmul : lam * τ ≤ |lam| * |τ| := by
      calc
        lam * τ ≤ |lam * τ| := le_abs_self _
        _ = |lam| * |τ| := by rw [abs_mul]
    nlinarith
  let s : ℝ := Real.sqrt |τ|
  have hpow : |τ| ^ (3 / 2 : ℝ) = s ^ (3 : ℕ) := by
    -- Rewrite the `3 / 2` power as a cubic in `sqrt |τ|`.
    calc
      |τ| ^ (3 / 2 : ℝ) = (|τ| ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num, Real.rpow_mul (abs_nonneg τ)]
      _ = s ^ (3 : ℕ) := by
        simp [s, Real.sqrt_eq_rpow]
  have hs_sq : s ^ (2 : ℕ) = |τ| := by
    -- `s = sqrt |τ|` was chosen precisely so that its square recovers `|τ|`.
    dsimp [s]
    exact Real.sq_sqrt (abs_nonneg τ)
  have hpoly :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) := by
    -- The remaining inequality is the nonnegativity of a factored cubic polynomial.
    have hnonneg : 0 ≤ (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) := by
      positivity
    have hidentity :
        (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) =
          (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) +
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      field_simp [hM.ne']
      ring
    nlinarith
  have hpoly' :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (|lam| / 2 : ℝ) * |τ| := by
    rw [hpow, ← hs_sq]
    exact hpoly
  nlinarith

/-- Helper for Proposition 4.1.8: the explicit slack minimizer attains the lower-bound value
`-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer
    (M : ℝ) (lam : ℝ) (hM : 0 < M) :
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
  have habs :
      |cubicRegularizedQuadraticTauMinimizer M lam| = ((2 : ℝ) * |lam| / M) ^ (2 : ℕ) := by
    -- The minimizer has squared magnitude `(2 |λ| / M)²`.
    rw [cubicRegularizedQuadraticTauMinimizer, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by positivity), abs_abs, abs_of_pos (pow_pos hM 2)]
    field_simp [hM.ne']
    ring_nf
  have hpow :
      |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) =
        ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by
    -- Raising that squared magnitude to `3 / 2` gives the expected cubic term.
    rw [habs]
    calc
      (((2 : ℝ) * |lam| / M) ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
          (((2 : ℝ) * |lam| / M) ^ (1 : ℕ) : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) * |lam| / M) 2 (3 / 2 : ℝ)]
        norm_num
      _ = ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by ring
  have hlamtau :
      lam * cubicRegularizedQuadraticTauMinimizer M lam =
        |lam| * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    -- The minimizer has the same sign as `lam`, so the linear term also depends only on `|lam|`.
    rw [cubicRegularizedQuadraticTauMinimizer]
    field_simp [hM.ne']
    ring_nf
    rw [← sq_abs lam]
    ring
  have hlinterm :
      (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        (|lam| / 2 : ℝ) * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    nlinarith [hlamtau]
  rw [hpow, hlinterm]
  field_simp [hM.ne']
  ring

-- Proof sketch: minimize the scalar function
-- `τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` directly; the critical point is the explicit owner
-- `cubicRegularizedQuadraticTauMinimizer M lam`, and convexity yields global minimality.
/-- For `M > 0`, the scalar function
`τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` is minimized at
`cubicRegularizedQuadraticTauMinimizer M lam`. -/
theorem cubicRegularizedQuadraticTauMinimizer_isMinOn
    (M : ℝ) (hM : 0 < M) (lam : ℝ) :
    IsMinOn
      (fun τ : ℝ ↦
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ)
      Set.univ
      (cubicRegularizedQuadraticTauMinimizer M lam) := by
  rw [isMinOn_univ_iff]
  intro τ
  -- Compare every slack value with the explicit minimum value attained at `τ(λ)`.
  calc
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) :=
      cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM
    _ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ :=
      cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ

/- Proposition 4.1.8 lies in the Chapter 4 cubic-regularized quadratic / epigraph-duality
domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticTauMinimizer` and
  `cubicRegularizedQuadraticTauMinimizer_isMinOn` in `Definition_4_1_14`, the chapter owner and
  owner minimization theorem for the scalar `τ`-subproblem;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction` in
  `Definition_4_1_13`, the bridge from the source-facing dual owner to the generic Chapter 1
  `LagrangianProblem.dualFunction`;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the source-facing owner of
  the one-constraint epigraph reformulation.

Best owner abstraction:
* source-facing: eliminate the slack variable `τ` from the epigraph Lagrangian and characterize
  the resulting scalar dual domain;
* core/canonical: `cubicRegularizedQuadraticTauMinimizer`,
  `cubicRegularizedQuadraticDualFunction`, `cubicRegularizedQuadraticDualDomain`, and
  `cubicRegularizedQuadraticEpigraphProblem`;
* bridge/view: the two source-facing bridge theorems below together with the recalled upstream
  domain theorem, which express the source proposition in terms of those established owners.

Primitive data:
* the cubic-regularized quadratic data `g`, `H`, and `M`;
* the shifted quadratic owner `quadraticObjective 0 g (H + λ I)`.

Derived API:
* the explicit slack minimizer `cubicRegularizedQuadraticTauMinimizer M λ`;
* the dual value `cubicRegularizedQuadraticDualFunction g H M λ`;
* the domain `cubicRegularizedQuadraticDualDomain g H M`.

This file therefore stays at the source-facing bridge layer and reuses the existing owner
abstractions instead of introducing a parallel local scalar-dual or `τ`-minimizer owner. -/

section

/-- Helper for Proposition 4.1.8: splitting the scalar epigraph Lagrangian isolates the shifted
quadratic `q_λ(h)` and the one-dimensional `τ`-objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
      quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Reuse the owner-side split with the shifted matrix written explicitly.
  simpa using
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term g Hmat M h τ lam

/-- Helper for Proposition 4.1.8: the explicit slack minimizer satisfies the displayed
first-order stationarity equation. -/
lemma cubicRegularizedQuadraticTauMinimizer_stationary_eq
    (hM : 0 < M) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) := by
  -- Evaluate the explicit formula `τ(λ) = 4 λ |λ| / M²` branchwise in the sign of `λ`.
  rcases lt_trichotomy lam 0 with hlam | rfl | hlam
  · dsimp [cubicRegularizedQuadraticTauMinimizer]
    rw [abs_of_neg hlam]
    have htau_neg : (4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ) < 0 := by
      have hnum_neg : (4 : ℝ) * lam * (-lam) < 0 := by
        nlinarith
      have hden_pos : 0 < M ^ (2 : ℕ) := by
        positivity
      exact div_neg_of_neg_of_pos hnum_neg hden_pos
    rw [abs_of_neg htau_neg, Real.sign_of_neg htau_neg]
    -- On the negative branch, `|τ|^(1/2)` reduces to `2 (-λ) / M`.
    have hsqrt : ((-((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ))) ^ (1 / 2 : ℝ)) = 2 * (-lam) / M := by
      have hsq : -((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ)) = ((2 * (-lam) / M : ℝ) ^ (2 : ℕ)) := by
        field_simp [hM.ne']
        ring
      rw [hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · have hnum_nonneg : 0 ≤ 2 * (-lam) := by
          nlinarith
        exact div_nonneg hnum_nonneg hM.le
    calc
      (M / 4 : ℝ) * (-((4 : ℝ) * lam * (-lam) / M ^ (2 : ℕ))) ^ (1 / 2 : ℝ) * (-1 : ℝ)
          = (M / 4 : ℝ) * (2 * (-lam) / M) * (-1 : ℝ) := by
              rw [hsqrt]
      _ = (lam / 2 : ℝ) := by
            field_simp [hM.ne']
            ring
  · simp [cubicRegularizedQuadraticTauMinimizer]
  · dsimp [cubicRegularizedQuadraticTauMinimizer]
    rw [abs_of_pos hlam]
    have htau_pos : 0 < (4 : ℝ) * lam * lam / M ^ (2 : ℕ) := by
      positivity
    rw [abs_of_pos htau_pos, Real.sign_of_pos htau_pos]
    -- On the positive branch, `|τ|^(1/2)` reduces to `2 λ / M`.
    have hsqrt : (((4 : ℝ) * lam * lam / M ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) = 2 * lam / M := by
      have hsq : (4 : ℝ) * lam * lam / M ^ (2 : ℕ) = ((2 * lam / M : ℝ) ^ (2 : ℕ)) := by
        field_simp [hM.ne']
        ring
      rw [hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg]
      · have hnum_nonneg : 0 ≤ 2 * lam := by
          nlinarith
        exact div_nonneg hnum_nonneg hM.le
    calc
      (M / 4 : ℝ) * ((4 : ℝ) * lam * lam / M ^ (2 : ℕ)) ^ (1 / 2 : ℝ) * (1 : ℝ)
          = (M / 4 : ℝ) * (2 * lam / M) * (1 : ℝ) := by
              rw [hsqrt]
      _ = (lam / 2 : ℝ) := by
            field_simp [hM.ne']
            ring

/-- Helper for Proposition 4.1.8: substituting the explicit slack minimizer evaluates the scalar
`τ`-objective to the cubic penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_at_minimizer
    (hM : 0 < M) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) =
      - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
  -- Reuse the owner-side evaluation of the minimized scalar objective.
  simpa using cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM

-- Proof sketch: differentiate the scalar `τ`-objective, solve the first-order equation
-- `(M / 4) |τ|^(1/2) sign(τ) = λ / 2`, and use convexity of `τ ↦ |τ|^(3/2)` to conclude that the
-- explicit critical point is the global minimizer of the `τ`-subproblem. This is a source-facing
-- bridge built on the owner theorem `cubicRegularizedQuadraticTauMinimizer_isMinOn`.
/-- Proposition 4.1.8 (1): for `M > 0`, minimizing the epigraph Lagrangian with respect to `τ`
at fixed `h` and `λ` is attained at `τ(λ) = 4 λ |λ| / M²`, equivalently at the point satisfying
`(M / 4) |τ|^(1/2) sign(τ) = λ / 2`. -/
theorem cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) (h : E) (lam : ℝ) :
    let τ := cubicRegularizedQuadraticTauMinimizer M lam
    (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) ∧
      IsMinOn
        (fun τ' : ℝ ↦ cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam)
        Set.univ
        τ := by
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  refine ⟨?_, ?_⟩
  · -- The displayed stationarity identity is the explicit scalar minimizer formula.
    simpa [τ] using cubicRegularizedQuadraticTauMinimizer_stationary_eq (M := M) hM lam
  · rw [isMinOn_univ_iff]
    intro τ'
    have hscalar :
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ ≤
          (M / 6 : ℝ) * |τ'| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ' := by
      -- The owner theorem already minimizes the one-dimensional slack objective.
      simpa [τ] using
        (isMinOn_univ_iff.mp (cubicRegularizedQuadraticTauMinimizer_isMinOn M hM lam)) τ'
    have hsum :
        quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
            ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) ≤
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
            ((M / 6 : ℝ) * |τ'| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ') :=
      by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right hscalar
            (quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h)
    -- Adding the constant quadratic term transports the scalar minimum to the full Lagrangian.
    simpa [τ, cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective]
      using hsum

-- Proof sketch: split the epigraph Lagrangian into the `h`-dependent quadratic part and the
-- scalar `τ`-objective, substitute the explicit minimizer from
-- `cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn`, and simplify the resulting minimum
-- value of the `τ`-term to `-(2 / (3 M²)) |λ|³`.
/-- Proposition 4.1.8 (2): after eliminating `τ`, the scalar dual function is the infimum over
`h : ℝⁿ` of the quadratic objective `q_λ(h)` minus the cubic penalty `(2 / (3 M²)) |λ|³`. -/
theorem cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) (lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g Hmat M lam =
      sInf (Set.range fun h : E ↦
        ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal)) := by
  rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  have hτvalue :
      ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) =
        - (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
    -- Evaluate the scalar objective at the explicit minimizer once and reuse it on every fiber.
    simpa [τ] using cubicRegularizedQuadraticTauObjective_at_minimizer (M := M) hM lam
  apply le_antisymm
  · refine le_sInf ?_
    rintro y ⟨h, rfl⟩
    have hsInf :
        sInf
            (Set.range
              (fun z : E × ℝ ↦
                (cubicRegularizedQuadraticScalarLagrangian g Hmat M z.1 z.2 lam : EReal))) ≤
          (cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam : EReal) := by
      -- Insert the explicit minimizing slack value as a witness in the product-space infimum.
      exact sInf_le ⟨(h, τ), rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- Substituting the minimized slack term leaves only the shifted quadratic in `h`.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective, hτvalue]
      ring
    simpa [hvalue] using hsInf
  · refine le_sInf ?_
    rintro y ⟨⟨h, τ'⟩, rfl⟩
    have hfiber :
        (M / 4 : ℝ) * |τ| ^ (1 / 2 : ℝ) * Real.sign τ = (lam / 2 : ℝ) ∧
          IsMinOn
            (fun u : ℝ ↦ cubicRegularizedQuadraticScalarLagrangian g Hmat M h u lam)
            Set.univ
            τ := by
      -- Route correction: use the proposition-local fiberwise minimizer theorem instead of
      -- rebuilding the shifted-matrix bridge inside this `sInf` comparison.
      simpa [τ] using
        cubicRegularizedQuadraticEpigraphLagrangian_tau_isMinOn
          g Hmat hM h lam
    have hsInf :
        sInf
            (Set.range
              (fun h : E ↦
                ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
                    (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal))) ≤
          ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
              (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal) := by
      -- The reduced infimum is bounded above by the value on the current `h`-fiber.
      exact sInf_le ⟨h, rfl⟩
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      -- The minimizing point on the fiber has exactly the reduced objective value.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tauObjective, hτvalue]
      ring
    have hmin_real :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam ≤
          cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam := by
      -- Fiberwise minimality compares the chosen slack minimizer with every other slack value.
      exact (isMinOn_univ_iff.mp hfiber.2) τ'
    have hmin :
        ((quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) : EReal) ≤
          (cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ' lam : EReal) := by
      -- Rewrite the minimizing-fiber value into the reduced quadratic form before coercing.
      rw [hvalue] at hmin_real
      exact EReal.coe_le_coe_iff.2 hmin_real
    exact le_trans hsInf hmin

-- Proof sketch: use
-- `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` and observe that subtracting
-- the finite constant `(2 / (3 M²)) |λ|³` does not change whether the infimum is strictly above
-- `-∞`; equivalently, the domain is determined exactly by boundedness below of the quadratic
-- objective `q_λ`.
/-- Proposition 4.1.8 (3): the effective domain consists exactly of those multipliers `λ` for
which the shifted quadratic objective `q_λ` is bounded below. -/
theorem cubicRegularizedQuadraticScalarDualDomain_eq
    (g : E) (Hmat : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) :
    cubicRegularizedQuadraticDualDomain g Hmat M =
      { lam |
        BddBelow
          (Set.range
            (quadraticObjective 0 g
              (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) } := by
  ext lam
  constructor
  · intro hdom
    change ⊥ < cubicRegularizedQuadraticDualFunction g Hmat M lam at hdom
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine ⟨(cubicRegularizedQuadraticDualFunction g Hmat M lam).toReal + κ, ?_⟩
    rintro y ⟨h, rfl⟩
    have hsle : cubicRegularizedQuadraticDualFunction g Hmat M lam ≤
        (cubicRegularizedQuadraticScalarLagrangian g Hmat M h
          (cubicRegularizedQuadraticTauMinimizer M lam) lam : EReal) := by
      -- Evaluate the infimum at the explicit slack minimizer.
      rw [cubicRegularizedQuadraticDualFunction]
      exact sInf_le ⟨(h, cubicRegularizedQuadraticTauMinimizer M lam), rfl⟩
    have hsle_real :
        (cubicRegularizedQuadraticDualFunction g Hmat M lam).toReal ≤
          cubicRegularizedQuadraticScalarLagrangian g Hmat M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam :=
      EReal.toReal_le_toReal hsle (ne_of_gt hdom) (EReal.coe_ne_top _)
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g Hmat M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam =
          quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h - κ := by
      -- After minimizing over `τ`, only the shifted quadratic in `h` remains.
      dsimp [κ]
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
        cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM]
      ring
    rw [hvalue] at hsle_real
    dsimp [κ]
    nlinarith
  · rintro ⟨b, hb⟩
    change ⊥ < cubicRegularizedQuadraticDualFunction g Hmat M lam
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine lt_of_lt_of_le (EReal.bot_lt_coe (b - κ)) ?_
    rw [cubicRegularizedQuadraticDualFunction]
    refine le_sInf ?_
    rintro y ⟨⟨h, τ⟩, rfl⟩
    have hq : b ≤ quadraticObjective 0 g (Hmat + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h :=
      hb ⟨h, rfl⟩
    have hτ : -κ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
      -- The slack-variable objective is always at least the explicit minimum value.
      dsimp [κ]
      simpa using cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ
    have hsum : b - κ ≤ cubicRegularizedQuadraticScalarLagrangian g Hmat M h τ lam := by
      -- Combine the quadratic lower bound with the universal scalar lower bound.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
      nlinarith
    exact EReal.coe_le_coe_iff.2 hsum

end
