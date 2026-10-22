/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_10_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open Filter
open scoped ConstrainedArgmin CubicRegularizedDiagonalInvariants EuclideanOrthant

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner for the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners for the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualDomain_eq` in `Definition_4_1_14`, the bridge from
  `dom ψ` to the bounded-below shifted quadratic form;
* `cubicRegularizedQuadraticTauMinimizer` and `cubicRegularizedQuadraticTauMinimizer_def` in
  `Definition_4_1_14`, the owner and defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² = 0` strong-duality and primal-minimizer theorems from the
  source;
* core/canonical: the primal objective, scalar dual function/domain, and the owner-level slack
  minimizer `cubicRegularizedQuadraticTauMinimizer`;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* `g`, `Hdiag`, `M`, and the induced diagonal matrix `H = Matrix.diagonal Hdiag`;
* the diagonal invariant `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `cubicRegularizedQuadraticTauMinimizer M lam` together with
  `cubicRegularizedQuadraticTauMinimizer_def`.

This file therefore keeps the source-facing diagonal theorem family and records the `τ(λ*)`
clause by a labeled recall of the existing owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`, rather than by a duplicate specialized wrapper. -/

/- The cubic objective, scalar dual owner, dual-domain owner, and slack minimizer are already the
upstream declarations from `Definition_4_1_14`. -/
recall cubicRegularizedQuadraticObjective
recall cubicRegularizedQuadraticObjective_apply
recall cubicRegularizedQuadraticScalarLagrangian
recall cubicRegularizedQuadraticDualFunction
recall cubicRegularizedQuadraticDualFunction_eq_sInf
recall cubicRegularizedQuadraticDualDomain
recall mem_cubicRegularizedQuadraticDualDomain_iff
recall cubicRegularizedQuadraticTauMinimizer
recall cubicRegularizedQuadraticTauMinimizer_isMinOn

variable [NeZero n]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "v" => cubicRegularizedQuadraticObjective g H M
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "Λ" => EuclideanSpace ℝ (Fin 1)

variable {lamStar : ℝ}
variable (hM : 0 < M)
variable (hGzero : G²[g;Hdiag] = 0)
variable (hmax : IsMaxOn ψ Dplus lamStar)
variable (hlam : -H_min[Hdiag] < lamStar)

/-- Helper for Theorem 4.1.11: the packaged one-constraint epigraph problem for the diagonal
model. -/
def diagonalEpigraphProblem : LagrangianProblem (E × ℝ) 1 :=
  cubicRegularizedQuadraticEpigraphProblem g H M

/-- Helper for Theorem 4.1.11: the explicit diagonal certificate vector at multiplier `μ`. -/
def zeroMinimalGradientSquareCertificateVector
    (g : E) (Hdiag : Fin n → ℝ) (μ : ℝ) : E :=
  WithLp.toLp 2
    (fun i : Fin n ↦ if i ∈ I*[Hdiag] then 0 else -g i / (Hdiag i + μ))

/-- Helper for Theorem 4.1.11: the epigraph certificate point pairing the explicit diagonal
vector with the slack minimizer `τ(μ)`. -/
def zeroMinimalGradientSquareCertificatePoint
    (g : E) (Hdiag : Fin n → ℝ) (M μ : ℝ) : E × ℝ :=
  (zeroMinimalGradientSquareCertificateVector g Hdiag μ,
    cubicRegularizedQuadraticTauMinimizer M μ)

/-- Helper for Theorem 4.1.11: in `ℝ^1`, a multiplier is determined by its only coordinate. -/
lemma one_dim_multiplier_eq_single
    (lam : Λ) :
    lam = EuclideanSpace.single 0 (lam 0) := by
  -- Collapse the one-dimensional multiplier to its single coordinate.
  ext i
  fin_cases i
  rfl

/-- Helper for Theorem 4.1.11: the explicit diagonal certificate minimizes the packaged
Lagrangian subproblem at every multiplier `μ > -H_min`. -/
lemma zero_minimal_gradient_square_scalar_certificate_mem_lagrangianMinimizers
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    {μ : ℝ} (hμ : -H_min[Hdiag] < μ) :
    zeroMinimalGradientSquareCertificatePoint g Hdiag M μ ∈
      (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 μ) := by
  -- Split the packaged Lagrangian into the shifted quadratic in `h` and the scalar `τ`-term.
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_univ_iff]
  intro y
  have hquad_min :
      IsMinOn
        (quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)))
        Set.univ
        (zeroMinimalGradientSquareCertificateVector g Hdiag μ) := by
    -- Proposition 4.1.10 identifies the certificate vector with the diagonal quadratic minimizer.
    refine
      (cubicRegularizedDiagonal_isMinOn_iff
        (g := g) (Hdiag := Hdiag) (lam := μ) hGzero hμ
        (zeroMinimalGradientSquareCertificateVector g Hdiag μ)).2 ?_
    intro i
    simp [zeroMinimalGradientSquareCertificateVector]
  have htau_min :
      IsMinOn
        (fun τ : ℝ ↦
          (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * τ)
        Set.univ
        (cubicRegularizedQuadraticTauMinimizer M μ) :=
    cubicRegularizedQuadraticTauMinimizer_isMinOn M hM μ
  have hquad_le :
      quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))
          (zeroMinimalGradientSquareCertificateVector g Hdiag μ) ≤
        quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) y.1 :=
    (isMinOn_univ_iff.mp hquad_min) y.1
  have htau_le :
      (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M μ| ^ (3 / 2 : ℝ) -
          (μ / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M μ ≤
        (M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * y.2 :=
    (isMinOn_univ_iff.mp htau_min) y.2
  have hsum :
      quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))
          (zeroMinimalGradientSquareCertificateVector g Hdiag μ) +
          ((M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M μ| ^ (3 / 2 : ℝ) -
            (μ / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M μ) ≤
        quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) y.1 +
          ((M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * y.2) :=
    add_le_add hquad_le htau_le
  -- Reassemble those two one-variable minima into the packaged Lagrangian inequality.
  simpa [zeroMinimalGradientSquareCertificatePoint,
    cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq,
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term] using hsum

/-- Helper for Theorem 4.1.11: a scalar dual maximizer over `dom ψ ∩ ℝ₊` is automatically
nonnegative. -/
lemma scalar_dual_maximizer_nonneg
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar) :
    0 ≤ lamStar := by
  by_contra hneg
  have hlam0 : -H_min[Hdiag] < (0 : ℝ) := by
    linarith
  let h0 : E := zeroMinimalGradientSquareCertificateVector g Hdiag 0
  let x0 : E × ℝ := zeroMinimalGradientSquareCertificatePoint g Hdiag M 0
  have hx0 :
      x0 ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
          (EuclideanSpace.single 0 0) := by
    simpa [x0] using
      zero_minimal_gradient_square_scalar_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero) (μ := 0) hlam0
  have hzero_dom : 0 ∈ cubicRegularizedQuadraticDualDomain g H M := by
    rw [mem_cubicRegularizedQuadraticDualDomain_iff,
      cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    rw [(cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction_eq_lagrangian hx0]
    exact EReal.bot_lt_coe _
  have hmax0 : ψ 0 ≤ ψ lamStar := by
    rw [isMaxOn_iff] at hmax
    exact hmax 0 ⟨hzero_dom, le_rfl⟩
  let c : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lamStar| ^ (3 : ℕ)
  have hc_pos : 0 < c := by
    dsimp [c]
    have hlam_ne : lamStar ≠ 0 := by
      linarith
    have habs_pos : 0 < |lamStar| := abs_pos.mpr hlam_ne
    positivity
  have hzero_value :
      ψ 0 = (quadraticObjective 0 g H h0 : EReal) := by
    calc
      ψ 0 =
          ((cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian x0
            (EuclideanSpace.single 0 0) : EReal) := by
              rw [cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
              simpa [x0] using
                (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction_eq_lagrangian hx0
      _ = (quadraticObjective 0 g H h0 : EReal) := by
              dsimp [x0, h0, zeroMinimalGradientSquareCertificatePoint]
              rw [cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq,
                cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
              simp [cubicRegularizedQuadraticTauMinimizer]
  have hquad_le :
      quadraticObjective 0 g (H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ)) h0 ≤
        quadraticObjective 0 g H h0 := by
    rw [quadraticObjective_zero_eq_dotProduct, quadraticObjective_zero_eq_dotProduct]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    have hdot_nonneg : 0 ≤ dotProduct h0 h0 := by
      simpa [EuclideanSpace.real_norm_sq_eq] using sq_nonneg ‖h0‖
    nlinarith
  let τStar := cubicRegularizedQuadraticTauMinimizer M lamStar
  have hlam_eval :
      ψ lamStar ≤
        (cubicRegularizedQuadraticScalarLagrangian g H M h0 τStar lamStar : EReal) := by
    rw [cubicRegularizedQuadraticDualFunction_eq_sInf]
    exact sInf_le ⟨(h0, τStar), rfl⟩
  have hlam_value :
      (cubicRegularizedQuadraticScalarLagrangian g H M h0 τStar lamStar : EReal) =
        ((quadraticObjective 0 g (H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ)) h0 : ℝ) :
          EReal) - c := by
    dsimp [τStar, c]
    rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
      cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lamStar hM]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hlam_le :
      ψ lamStar ≤ ((quadraticObjective 0 g H h0 : ℝ) : EReal) - c := by
    calc
      ψ lamStar ≤
          (cubicRegularizedQuadraticScalarLagrangian g H M h0 τStar lamStar : EReal) :=
        hlam_eval
      _ = ((quadraticObjective 0 g (H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ)) h0 : ℝ) :
          EReal) - c := hlam_value
      _ ≤ ((quadraticObjective 0 g H h0 : ℝ) : EReal) - c := by
        exact_mod_cast sub_le_sub_right hquad_le c
  have hcontr : ψ 0 ≤ ψ 0 - c := by
    calc
      ψ 0 ≤ ψ lamStar := hmax0
      _ ≤ ((quadraticObjective 0 g H h0 : ℝ) : EReal) - c := hlam_le
      _ = ψ 0 - c := by
        rw [hzero_value]
  have : ¬ ψ 0 ≤ ψ 0 - c := by
    rw [hzero_value]
    intro hle
    exact
      (not_le_of_gt hc_pos)
        (by exact_mod_cast hle : quadraticObjective 0 g H h0 ≤ quadraticObjective 0 g H h0 - c)
  exact this hcontr

/-- Helper for Theorem 4.1.11: the maximizing scalar multiplier is dual feasible. -/
lemma scalar_dual_maximizer_mem_Dplus
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar) :
    lamStar ∈ Dplus := by
  have hxStar :
      zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
          (EuclideanSpace.single 0 lamStar) := by
    exact
      zero_minimal_gradient_square_scalar_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero) (μ := lamStar) hlam
  have hdom : lamStar ∈ cubicRegularizedQuadraticDualDomain g H M := by
    rw [mem_cubicRegularizedQuadraticDualDomain_iff,
      cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    rw [(cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction_eq_lagrangian hxStar]
    exact EReal.bot_lt_coe _
  exact ⟨hdom, scalar_dual_maximizer_nonneg
    (hM := hM) (hGzero := hGzero)
    (hmax := hmax) (hlam := hlam)⟩

/-- Helper for Theorem 4.1.11: an epigraph-dual-feasible multiplier has scalar coordinate in
`dom ψ ∩ ℝ₊`. -/
lemma scalar_coordinate_mem_Dplus_of_epigraph_dualFeasible
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)
    {lam : Λ}
    (hlam :
      lam ∈
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFeasibleSet) :
    lam 0 ∈ cubicRegularizedQuadraticDualDomain g (Matrix.diagonal Hdiag) M ∩ Set.Ici (0 : ℝ) := by
  -- Read dual feasibility on the unique scalar coordinate of `Λ = ℝ^1`.
  rcases (LagrangianProblem.mem_dualFeasibleSet_iff
    (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M)).mp hlam with
    ⟨hdual, hnonneg⟩
  have hsingle : lam = EuclideanSpace.single 0 (lam 0) :=
    one_dim_multiplier_eq_single (lam := lam)
  have hdual_lt :
      ⊥ <
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction lam :=
    (LagrangianProblem.mem_dualDomain_iff
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M)).mp hdual
  have hdual_eq :
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction lam =
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
          (EuclideanSpace.single 0 (lam 0)) :=
    congrArg
      (fun l ↦
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction l)
      hsingle
  have hdual_single_lt :
      ⊥ <
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
          (EuclideanSpace.single 0 (lam 0)) := by
    rw [← hdual_eq]
    exact hdual_lt
  have hscalar_dom :
      lam 0 ∈ cubicRegularizedQuadraticDualDomain g (Matrix.diagonal Hdiag) M := by
    rw [mem_cubicRegularizedQuadraticDualDomain_iff,
      cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    exact hdual_single_lt
  exact ⟨hscalar_dom, hnonneg 0⟩

/-- Helper for Theorem 4.1.11: the scalar dual maximizer induces the corresponding maximizer for
the packaged one-constraint epigraph dual problem. -/
lemma epigraph_dual_maximizer_of_scalar_dual_maximizer
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) {lamStar : ℝ} :
    IsMaxOn
      (cubicRegularizedQuadraticDualFunction g (Matrix.diagonal Hdiag) M)
      (cubicRegularizedQuadraticDualDomain g (Matrix.diagonal Hdiag) M ∩ Set.Ici (0 : ℝ))
      lamStar →
    IsMaxOn
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFeasibleSet
      (EuclideanSpace.single 0 lamStar) := by
  intro hmax
  -- Move epigraph-feasible multipliers back to the scalar feasible set via the unique coordinate.
  rw [isMaxOn_iff]
  intro lam hlam
  have hlam_scalar :
      lam 0 ∈ cubicRegularizedQuadraticDualDomain g (Matrix.diagonal Hdiag) M ∩ Set.Ici (0 : ℝ) :=
    scalar_coordinate_mem_Dplus_of_epigraph_dualFeasible
      (g := g) (Hdiag := Hdiag) (M := M) (lam := lam) hlam
  have hle_scalar :
      cubicRegularizedQuadraticDualFunction g (Matrix.diagonal Hdiag) M (lam 0) ≤
        cubicRegularizedQuadraticDualFunction g (Matrix.diagonal Hdiag) M lamStar :=
    (isMaxOn_iff.mp hmax) (lam 0) hlam_scalar
  have hsingle : lam = EuclideanSpace.single 0 (lam 0) :=
    one_dim_multiplier_eq_single (lam := lam)
  have hdual_eq :
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction lam =
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
          (EuclideanSpace.single 0 (lam 0)) :=
    congrArg
      (fun l ↦
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction l)
      hsingle
  -- Collapse the one-dimensional multiplier comparison back to the scalar dual function.
  calc
    (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction lam =
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
          (EuclideanSpace.single 0 (lam 0)) := hdual_eq
    _ = cubicRegularizedQuadraticDualFunction g (Matrix.diagonal Hdiag) M (lam 0) := by
          rw [← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    _ ≤ cubicRegularizedQuadraticDualFunction g (Matrix.diagonal Hdiag) M lamStar := hle_scalar
    _ = (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).dualFunction
          (EuclideanSpace.single 0 lamStar) := by
          rw [cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]

/-- Helper for Theorem 4.1.11: every multiplier in the one-dimensional certificate ball stays in
the interior half-line `(-H_min, ∞)`. -/
lemma multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
    (hlam : -H_min[Hdiag] < lamStar)
    {lam : Λ}
    (hmem :
      lam ∈
        Metric.closedBall (EuclideanSpace.single 0 lamStar)
          ((lamStar + H_min[Hdiag]) / 2) ∩ ℝ₊^1) :
    -H_min[Hdiag] < lam 0 := by
  rcases hmem with ⟨hball, _⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  -- In `ℝ^1`, the ball condition is exactly an absolute-value bound on the only coordinate.
  have habs : |lam 0 - lamStar| ≤ (lamStar + H_min[Hdiag]) / 2 := by
    simpa [show lam - EuclideanSpace.single 0 lamStar =
        EuclideanSpace.single 0 (lam 0 - lamStar) by
          ext i
          fin_cases i
          rfl, PiLp.norm_single, Real.norm_eq_abs] using hball
  have hlower : -((lamStar + H_min[Hdiag]) / 2) ≤ lam 0 - lamStar :=
    (abs_le.mp habs).1
  linarith [hlam]

/-- Helper for Theorem 4.1.11: the explicit certificate path varies continuously at the dual
maximizer. -/
lemma zero_minimal_gradient_square_certificate_point_continuousAt :
    (-H_min[Hdiag] < lamStar) →
    ContinuousAt
      (fun lam : Λ ↦ zeroMinimalGradientSquareCertificatePoint g Hdiag M (lam 0))
      (EuclideanSpace.single 0 lamStar) := by
  -- First expose the unique scalar coordinate of `Λ = ℝ^1`.
  intro hlam
  have hcoord0 :
      ContinuousAt (fun lam : Λ ↦ lam 0)
        (EuclideanSpace.single 0 lamStar) := by
    have hofLp :
        ContinuousAt (fun lam : Λ ↦ WithLp.ofLp lam)
          (EuclideanSpace.single 0 lamStar) := by
      simpa [Function.comp] using
        (PiLp.continuous_ofLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt
    simpa [Function.comp] using
      ((continuous_apply 0).continuousAt.comp hofLp)
  have hvector :
      ContinuousAt
        (fun lam : Λ ↦ zeroMinimalGradientSquareCertificateVector g Hdiag (lam 0))
        (EuclideanSpace.single 0 lamStar) := by
    -- Each certificate coordinate is either constantly zero or a rational function in `lam 0`.
    change ContinuousAt
      (fun lam : Λ ↦
        WithLp.toLp 2
          (fun i : Fin n ↦ if i ∈ I*[Hdiag] then 0 else -g i / (Hdiag i + lam 0)))
      (EuclideanSpace.single 0 lamStar)
    refine (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp ?_
    rw [continuousAt_pi]
    intro i
    by_cases hi : i ∈ I*[Hdiag]
    · simpa [zeroMinimalGradientSquareCertificateVector, hi]
    · have hdenom_pos : 0 < Hdiag i + lamStar := by
        have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
          diagonalMinimum_le_entry (Hdiag := Hdiag) i
        linarith
      have hdenom : Hdiag i + lamStar ≠ 0 := ne_of_gt hdenom_pos
      simpa [zeroMinimalGradientSquareCertificateVector, hi, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm] using
        (continuousAt_const.mul ((continuousAt_const.add hcoord0).inv₀ hdenom))
  have htau :
      ContinuousAt
        (fun lam : Λ ↦ cubicRegularizedQuadraticTauMinimizer M (lam 0))
        (EuclideanSpace.single 0 lamStar) := by
    -- The slack coordinate is the explicit continuous formula `4 λ |λ| / M²`.
    have hbase :
        ContinuousAt (fun lam : Λ ↦ (4 : ℝ) * (lam 0 * |lam 0|))
          (EuclideanSpace.single 0 lamStar) := by
      exact continuousAt_const.mul (hcoord0.mul hcoord0.abs)
    simpa [cubicRegularizedQuadraticTauMinimizer, pow_two, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using hbase.const_mul ((M ^ (2 : ℕ))⁻¹)
  -- Package the continuous vector and slack coordinates back into the certificate point.
  simpa [zeroMinimalGradientSquareCertificatePoint] using hvector.prodMk htau

/-- Helper for Theorem 4.1.11: on the `h`-fiber, epigraph feasibility is exactly the inequality
`‖h‖² ≤ τ`. -/
lemma diagonalEpigraphFeasibleFiber_iff
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)
    {h : E} {τ : ℝ} :
    (h, τ) ∈ (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).feasibleSet ↔
      ‖h‖ ^ (2 : ℕ) ≤ τ := by
  constructor
  · intro hz
    -- Rewrite the unique scalar constraint and clear the harmless factor `1 / 2`.
    have hconstraint :
        (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 := by
      simpa [cubicRegularizedQuadraticEpigraphProblem] using
        ((LagrangianProblem.mem_feasibleSet_iff
          (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M)).1 hz 0)
    nlinarith
  · intro hτ
    -- Package the scalar inequality back into the owner feasible set.
    refine (LagrangianProblem.mem_feasibleSet_iff
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M)).2 ?_
    intro j
    fin_cases j
    simpa [cubicRegularizedQuadraticEpigraphProblem] using
      (show (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 by nlinarith)

/-- Helper for Theorem 4.1.11: the tight slack `τ = ‖h‖²` is always feasible above `h`. -/
lemma diagonalNormSq_memEpigraphFeasibleFiber
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)
    (h : E) :
    (h, ‖h‖ ^ (2 : ℕ)) ∈
      (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).feasibleSet := by
  -- The tight slack saturates the unique epigraph inequality.
  exact (diagonalEpigraphFeasibleFiber_iff (g := g) (Hdiag := Hdiag) (M := M)).2 le_rfl

/-- Helper for Theorem 4.1.11: along a feasible epigraph fiber, replacing `τ` by the tight slack
`‖h‖²` can only decrease the epigraph objective. -/
lemma diagonal_epigraphObjective_tightSlack_le_of_feasible
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)
    (hM : 0 < M)
    {h : E} {τ : ℝ}
    (hτ :
      (h, τ) ∈
        (cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M).feasibleSet) :
    cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M (h, ‖h‖ ^ (2 : ℕ)) ≤
      cubicRegularizedQuadraticEpigraphProblem g (Matrix.diagonal Hdiag) M (h, τ) := by
  have hnorm_sq_le : ‖h‖ ^ (2 : ℕ) ≤ τ :=
    (diagonalEpigraphFeasibleFiber_iff (g := g) (Hdiag := Hdiag) (M := M)).1 hτ
  have hnorm_sq_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by
    positivity
  have hτ_nonneg : 0 ≤ τ := le_trans hnorm_sq_nonneg hnorm_sq_le
  have hrpow :
      (‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ τ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hnorm_sq_nonneg hnorm_sq_le (by norm_num)
  have hM_div_six_nonneg : 0 ≤ M / 6 := by
    nlinarith
  have hcubic :
      (M / 6 : ℝ) * ((‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) ≤
        (M / 6 : ℝ) * (τ ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hrpow hM_div_six_nonneg
  have hsum :=
    add_le_add_left hcubic
      (dotProduct g h +
        (1 / 2 : ℝ) * dotProduct (Matrix.mulVec (Matrix.diagonal Hdiag) h) h)
  -- Only the cubic slack term changes along the fiber; the quadratic part is fixed in `h`.
  simpa [cubicRegularizedQuadraticEpigraphProblem, abs_of_nonneg hnorm_sq_nonneg,
    abs_of_nonneg hτ_nonneg, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Theorem 4.1.11: the explicit diagonal certificate at the maximizing multiplier
attains the dual value, and its `h`-coordinate is a global primal minimizer. -/
lemma zero_minimal_gradient_square_certificate_value_and_isMinOn
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    ψ lamStar =
      (v (zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar).1 : EReal) ∧
      IsMinOn v Set.univ
        (zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar).1 := by
  let xPath : Λ → E × ℝ :=
    fun lam ↦ zeroMinimalGradientSquareCertificatePoint g Hdiag M (lam 0)
  let xStar : E × ℝ :=
    zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar
  let hStar : E :=
    zeroMinimalGradientSquareCertificateVector g Hdiag lamStar
  let ε : ℝ := (lamStar + H_min[Hdiag]) / 2
  have hDplus : lamStar ∈ Dplus := by
    exact
      scalar_dual_maximizer_mem_Dplus
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero)
        (hmax := hmax) (hlam := hlam)
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hxStar :
      xStar ∈ (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 lamStar) := by
    -- The explicit diagonal certificate minimizes the Lagrangian at the maximizing multiplier.
    simpa [xStar] using
      zero_minimal_gradient_square_scalar_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero)
        (μ := lamStar) hlam
  have hepigraph_max :
      IsMaxOn
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet
        (EuclideanSpace.single 0 lamStar) := by
    exact
      epigraph_dual_maximizer_of_scalar_dual_maximizer
        g Hdiag M hmax
  have hlamStar :
      EuclideanSpace.single 0 lamStar ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet := by
    -- Package scalar dual feasibility as dual feasibility for the one-constraint epigraph owner.
    rw [(cubicRegularizedQuadraticEpigraphProblem g H M).mem_dualFeasibleSet_iff]
    constructor
    · rw [(cubicRegularizedQuadraticEpigraphProblem g H M).mem_dualDomain_iff,
        ← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
      exact (mem_cubicRegularizedQuadraticDualDomain_iff g H M lamStar).mp hDplus.1
    · intro j
      fin_cases j
      simpa using hDplus.2
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈
            Metric.closedBall (EuclideanSpace.single 0 lamStar) ε ∩ ℝ₊^1 →
          lam ≠ EuclideanSpace.single 0 lamStar →
          xPath lam ∈
            (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers lam := by
    intro lam hmem _
    have hlam_mem : -H_min[Hdiag] < lam 0 := by
      simpa [ε] using
        multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
          (Hdiag := Hdiag) (lamStar := lamStar) hlam hmem
    rw [one_dim_multiplier_eq_single (lam := lam)]
    -- The pointwise certificate remains a Lagrangian minimizer throughout the punctured ball.
    simpa [xPath] using
      zero_minimal_gradient_square_scalar_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero)
        (μ := lam 0) hlam_mem
  have hlim :
      Tendsto xPath
        (nhdsWithin (EuclideanSpace.single 0 lamStar)
          ((Metric.closedBall (EuclideanSpace.single 0 lamStar) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 lamStar}))
        (nhds xStar) := by
    -- The punctured-neighborhood limit follows from continuity of the explicit certificate path.
    have hcontPath :
        ContinuousAt xPath (EuclideanSpace.single 0 lamStar) := by
      simpa [xPath] using
        zero_minimal_gradient_square_certificate_point_continuousAt
          (g := g) (Hdiag := Hdiag) (M := M) hlam
    simpa [xPath, xStar] using hcontPath.tendsto.mono_left
      (show
        nhdsWithin (EuclideanSpace.single 0 lamStar)
          ((Metric.closedBall (EuclideanSpace.single 0 lamStar) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 lamStar}) ≤
          nhds (EuclideanSpace.single 0 lamStar) from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt
        (cubicRegularizedQuadraticEpigraphProblem g H M).constraintVector
        xStar := by
    -- The single constraint coordinate is a polynomial in `(h, τ)`, hence continuous.
    change ContinuousAt
      (fun z : E × ℝ ↦
        WithLp.toLp 2
          (fun _ : Fin 1 ↦ (1 / 2 : ℝ) * ‖z.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * z.2))
      xStar
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).continuousAt.comp ?_
    rw [continuousAt_pi]
    intro j
    fin_cases j
    exact ((continuous_const.mul (continuous_fst.norm.pow 2)).sub
      (continuous_const.mul continuous_snd)).continuousAt
  have hoptimal :
      xStar ∈
        argmin[(cubicRegularizedQuadraticEpigraphProblem g H M).feasibleSet]
          (cubicRegularizedQuadraticEpigraphProblem g H M) := by
    -- Apply the generic Chapter 1 dual-certificate theorem to the explicit diagonal path.
    simpa [xPath, xStar, ε] using
      (cubicRegularizedQuadraticEpigraphProblem g H M).globalOptimality_of_dualCertificate
        xPath xStar hlamStar hepigraph_max hε hxPath hlim hcont hxStar
  rw [mem_constrainedArgmin_iff] at hoptimal
  rcases hoptimal with ⟨hxfeas, hxmin⟩
  have hcomp0 :
      lamStar *
          ((1 / 2 : ℝ) * ‖xStar.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * xStar.2) = 0 := by
    -- Complementary slackness collapses the Lagrangian back to the epigraph objective.
    simpa [xPath, xStar, cubicRegularizedQuadraticEpigraphProblem] using
      (cubicRegularizedQuadraticEpigraphProblem g H M).complementary_slackness_at_limit
        xPath xStar hlamStar hepigraph_max hε hxPath hlim hcont 0
  have hlagrangian_eq :
      (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian xStar
          (EuclideanSpace.single 0 lamStar) =
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar := by
    rw [LagrangianProblem.lagrangian_single_eq, hcomp0, add_zero]
  have hdual_eq_epigraph :
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 lamStar) =
        ((cubicRegularizedQuadraticEpigraphProblem g H M) xStar : EReal) := by
    calc
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 lamStar) =
          ((cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian xStar
            (EuclideanSpace.single 0 lamStar) : EReal) :=
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction_eq_lagrangian hxStar
      _ = ((cubicRegularizedQuadraticEpigraphProblem g H M) xStar : EReal) := by
        exact_mod_cast hlagrangian_eq
  have htight_feas_star :
      (hStar, ‖hStar‖ ^ (2 : ℕ)) ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).feasibleSet := by
    exact diagonalNormSq_memEpigraphFeasibleFiber (g := g) (Hdiag := Hdiag) (M := M) hStar
  have hopt_le_tight :
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar ≤
        (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
    (isMinOn_iff.mp hxmin) _ htight_feas_star
  have htight_le_opt :
      (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) ≤
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar := by
    -- Tightening the slack can only decrease the epigraph objective on a feasible fiber.
    simpa [xStar, hStar, zeroMinimalGradientSquareCertificatePoint] using
      diagonal_epigraphObjective_tightSlack_le_of_feasible
        g Hdiag M hM hxfeas
  have hxStar_eq_objective :
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar = v hStar := by
    have htight_eq :
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar =
          (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
      le_antisymm hopt_le_tight htight_le_opt
    -- At the tight slack, the epigraph objective becomes the original cubic objective.
    calc
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar =
          (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
        htight_eq
      _ = v hStar :=
        cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M hStar
  have hvalue :
      ψ lamStar = (v hStar : EReal) := by
    -- Evaluate the scalar dual value through the packaged dual owner and the tight-slack formula.
    calc
      ψ lamStar =
          (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
            (EuclideanSpace.single 0 lamStar) :=
        cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction g H M lamStar
      _ = ((cubicRegularizedQuadraticEpigraphProblem g H M) xStar : EReal) :=
        hdual_eq_epigraph
      _ = (v hStar : EReal) := by
        exact_mod_cast hxStar_eq_objective
  have hmin :
      IsMinOn v Set.univ hStar := by
    -- Compare the epigraph minimizer with every tight feasible point `(h, ‖h‖²)`.
    rw [isMinOn_univ_iff]
    intro h
    have hfeas_h :
        (h, ‖h‖ ^ (2 : ℕ)) ∈
          (cubicRegularizedQuadraticEpigraphProblem g H M).feasibleSet := by
      exact diagonalNormSq_memEpigraphFeasibleFiber (g := g) (Hdiag := Hdiag) (M := M) h
    have hopt_le_h :
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar ≤
          (cubicRegularizedQuadraticEpigraphProblem g H M) (h, ‖h‖ ^ (2 : ℕ)) :=
      (isMinOn_iff.mp hxmin) _ hfeas_h
    calc
      v hStar = (cubicRegularizedQuadraticEpigraphProblem g H M) xStar :=
        hxStar_eq_objective.symm
      _ ≤ (cubicRegularizedQuadraticEpigraphProblem g H M) (h, ‖h‖ ^ (2 : ℕ)) :=
        hopt_le_h
      _ = v h :=
        cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M h
  simpa [hStar, zeroMinimalGradientSquareCertificatePoint] using And.intro hvalue hmin

-- Proof sketch: combine the assumption `G² = 0` with the diagonal analysis of the shifted
-- quadratic subproblem to identify the minimizing `h`-variable for every `λ > -H_min`. Then use
-- the assumed maximality of `λ*` on `dom ψ ∩ ℝ₊` to identify the primal infimum with the dual
-- value `ψ(λ*)`; the auxiliary supremum step is the generic order-theoretic fact obtained from
-- `hmax.isLUB` and `IsLUB.csSup_eq`.
/-- Theorem 4.1.11 (1): for the diagonal cubic-regularized quadratic model with `H = diag(Hdiag)`,
if `G² = 0` and the dual problem admits a maximizer `λ* > -H_min`, then strong duality holds at
that maximizer:
the minimum of the primal objective `v(h)` equals the dual value `ψ(λ*)`. -/
theorem cubicRegularizedQuadraticDiagonal_strongDuality_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    sInf (Set.range fun h : E ↦
      (v h : EReal)) =
      ψ lamStar := by
  let hStar : E :=
    (zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar).1
  have hcert :
      ψ lamStar = (v hStar : EReal) ∧ IsMinOn v Set.univ hStar := by
    simpa [hStar] using
      zero_minimal_gradient_square_certificate_value_and_isMinOn
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero)
        (hmax := hmax) (hlam := hlam)
  rcases hcert with ⟨hvalue_eq, hmin⟩
  -- The attained primal minimum identifies the infimum of the full range.
  refine le_antisymm ?_ ?_
  · calc
      sInf (Set.range fun h : E ↦ (v h : EReal)) ≤ (v hStar : EReal) :=
        sInf_le ⟨hStar, rfl⟩
      _ = ψ lamStar := hvalue_eq.symm
  · refine le_sInf ?_
    rintro y ⟨h, rfl⟩
    have hle : v hStar ≤ v h :=
      (isMinOn_univ_iff.mp hmin) h
    calc
      ψ lamStar = (v hStar : EReal) := hvalue_eq
      _ ≤ (v h : EReal) := by
        exact_mod_cast hle

-- Proof sketch: solve the quadratic `h`-subproblem at the dual maximizer `λ*` using the
-- `G² = 0` diagonal case, and then use the primal-dual optimality relations at the maximizing
-- multiplier `λ*` to show that the resulting resolvent point minimizes the original cubic
-- objective.
/-- Theorem 4.1.11 (2): under the same hypotheses, the primal problem admits the explicit global
minimizer `h* = -(H + λ* I)⁻¹ g`. -/
theorem cubicRegularizedQuadraticDiagonal_primalMinimizer_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    IsMinOn v Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := by
  let hStar : E :=
    (zeroMinimalGradientSquareCertificatePoint g Hdiag M lamStar).1
  have hcert :
      ψ lamStar = (v hStar : EReal) ∧ IsMinOn v Set.univ hStar := by
    simpa [hStar] using
      zero_minimal_gradient_square_certificate_value_and_isMinOn
        (g := g) (Hdiag := Hdiag) (M := M)
        (hM := hM) (hGzero := hGzero)
        (hmax := hmax) (hlam := hlam)
  have hmin : IsMinOn v Set.univ hStar :=
    hcert.2
  have hres :
      hStar = -((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g := by
    -- Proposition 4.1.10 rewrites the explicit diagonal certificate as the resolvent point.
    refine
      (displayed_coordinate_formula_iff_eq_resolvent
        (g := g) (Hdiag := Hdiag) (lam := lamStar) hGzero hlam hStar).mp ?_
    intro i
    simp [hStar, zeroMinimalGradientSquareCertificatePoint,
      zeroMinimalGradientSquareCertificateVector]
  simpa [hres] using hmin

/- Theorem 4.1.11 (3): the associated slack minimizer satisfies
`τ(λ*) = 4 λ* |λ*| / M²`; this is exactly the owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end
