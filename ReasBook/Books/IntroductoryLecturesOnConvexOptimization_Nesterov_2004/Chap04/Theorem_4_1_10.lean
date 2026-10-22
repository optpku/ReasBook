/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_10_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open Filter
open scoped ConstrainedArgmin CubicRegularizedDiagonalInvariants EuclideanOrthant

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Domain/API note for this item: the theorem lies in the diagonal cubic-regularized quadratic /
scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner of the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the existing source-facing domain identity in the nondegenerate diagonal
  case;
* `cubicRegularizedDiagonalMinimum` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal owners of
  `H_min` and `G²`;
* `cubicRegularizedQuadraticTauMinimizer` and
  `cubicRegularizedQuadraticTauMinimizer_def` in `Definition_4_1_14`, the chapter owner and
  defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² > 0` strong-duality and minimizer statements from the source;
* core/canonical: the generic cubic-regularized quadratic objective, dual function, dual domain,
  and tau minimizer together with the diagonal bounded-below-domain owner;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* the gradient `g`, diagonal data `Hdiag`, cubic parameter `M`, and the diagonal matrix
  `H = Matrix.diagonal Hdiag`;
* the canonical diagonal invariants `H_min` and `G²`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `IsMaxOn (cubicRegularizedQuadraticDualFunction g H M)
    (cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)) lam`;
* `cubicRegularizedQuadraticTauMinimizer M lam`.

This file therefore keeps the source-facing diagonal theorem family, but removes duplicate local
owners for the primal objective, shifted quadratic form, and dual function. The source domain
clause is reused directly from `Proposition_4_1_9`, while the explicit `τ(λ*)` formula is
reused from the existing owner theorem `cubicRegularizedQuadraticTauMinimizer_def`. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "v" => cubicRegularizedQuadraticObjective g H M
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "P" => cubicRegularizedQuadraticEpigraphProblem g H M
local notation "Λ" => EuclideanSpace ℝ (Fin 1)

include Hdiag

/- The nondegenerate diagonal domain identity is already the source-facing proposition
`cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos`. -/
recall cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos

/-- Helper for Theorem 4.1.10: in `ℝ¹`, a multiplier is determined by its unique coordinate. -/
lemma dual_certificate_multiplier_eq_single
    (lam : Λ) :
    lam = EuclideanSpace.single 0 (lam 0) := by
  -- Collapse the one-dimensional multiplier to its single coordinate.
  ext i
  fin_cases i
  rfl

/-- Helper for Theorem 4.1.10: the explicit diagonal resolvent vector written coordinatewise. -/
def resolventCertificateVector
    (g : E) (Hdiag : Fin n → ℝ) (μ : ℝ) : E :=
  WithLp.toLp 2 (fun i : Fin n ↦ -g i / (Hdiag i + μ))

/-- Helper for Theorem 4.1.10: the epigraph certificate point pairing the resolvent vector with
the slack minimizer `τ(μ)`. -/
def resolventTauCertificatePoint
    (g : E) (Hdiag : Fin n → ℝ) (M μ : ℝ) : E × ℝ :=
  (resolventCertificateVector g Hdiag μ,
    cubicRegularizedQuadraticTauMinimizer M μ)

/-- Helper for Theorem 4.1.10: on the interior half-line `(-H_min, ∞)`, the coordinatewise
certificate vector is exactly the matrix-resolvent point `-(H + μ I)⁻¹ g`. -/
lemma resolventCertificateVector_eq_explicit
    {μ : ℝ} (hμ : -H_min[Hdiag] < μ) :
    resolventCertificateVector g Hdiag μ =
      -((H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g := by
  -- Compare coordinates with the owner-level diagonal resolvent formula.
  ext i
  simpa [resolventCertificateVector, diagonalResolventPoint, shiftedDiagonalMatrix,
    Matrix.toEuclideanLin_apply] using
    (diagonalResolventPoint_apply (g := g) (Hdiag := Hdiag) (lam := μ) hμ i).symm

/-- Helper for Theorem 4.1.10: for every interior multiplier `μ > -H_min`, the resolvent point
and the slack minimizer solve the epigraph Lagrangian subproblem at `μ`. -/
lemma resolvent_tau_certificate_mem_lagrangianMinimizers
    (hM : 0 < M)
    {μ : ℝ} (hμ : -H_min[Hdiag] < μ) :
    resolventTauCertificatePoint g Hdiag M μ ∈
      (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 μ) := by
  -- Split the packaged Lagrangian into the shifted quadratic term and the scalar `τ`-term.
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_univ_iff]
  intro y
  have hquad_min :
      IsMinOn
        (quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)))
        Set.univ
        (resolventCertificateVector g Hdiag μ) := by
    -- The `h`-coordinate is the owner resolvent minimizer rewritten in coordinate form.
    have hres :
        resolventCertificateVector g Hdiag μ =
          -((H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g := by
      simpa using
        (resolventCertificateVector_eq_explicit g Hdiag (μ := μ) hμ)
    rw [hres]
    simpa using
      (cubicRegularizedDiagonalResolvent_isMinOn
        (g := g) (Hdiag := Hdiag) (lam := μ) hμ)
  have htau_min :
      IsMinOn
        (fun τ : ℝ ↦
          (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * τ)
        Set.univ
        (cubicRegularizedQuadraticTauMinimizer M μ) :=
    cubicRegularizedQuadraticTauMinimizer_isMinOn M hM μ
  have hquad_le :
      quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))
          (resolventCertificateVector g Hdiag μ) ≤
        quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) y.1 :=
    (isMinOn_univ_iff.mp hquad_min) y.1
  have htau_le :
      (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M μ| ^ (3 / 2 : ℝ) -
          (μ / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M μ ≤
        (M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * y.2 :=
    (isMinOn_univ_iff.mp htau_min) y.2
  have hsum :
      quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ))
          (resolventCertificateVector g Hdiag μ) +
          ((M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M μ| ^ (3 / 2 : ℝ) -
            (μ / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M μ) ≤
        quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) y.1 +
          ((M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (μ / 2 : ℝ) * y.2) :=
    add_le_add hquad_le htau_le
  -- Reassemble the two one-variable minima into the packaged Lagrangian inequality.
  simpa [resolventTauCertificatePoint,
    cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq,
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term] using hsum

/-- Helper for Theorem 4.1.10: an epigraph-dual-feasible multiplier has a scalar coordinate in
`dom ψ ∩ ℝ₊`. -/
lemma scalar_coordinate_mem_Dplus_of_epigraph_dualFeasible
    {μ : Λ}
    (hμ : μ ∈ (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet) :
    μ 0 ∈ Dplus := by
  simpa [Dplus, Set.mem_Ici,
    LagrangianProblem.mem_dualFeasibleSet_iff,
    LagrangianProblem.mem_dualDomain_iff,
    cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction,
    dual_certificate_multiplier_eq_single (lam := μ)] using hμ

/-- Helper for Theorem 4.1.10: in the nondegenerate diagonal case, any scalar dual maximizer over
`dom ψ ∩ ℝ₊` is itself dual feasible. -/
lemma scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn ψ Dplus lamStar) :
    lamStar ∈ Dplus := by
  let lam0 : ℝ := max (0 : ℝ) (-H_min[Hdiag] + 1)
  have hlam0_nonneg : 0 ≤ lam0 := by
    dsimp [lam0]
    exact le_max_left 0 (-H_min[Hdiag] + 1)
  have hlam0_dom : lam0 ∈ cubicRegularizedQuadraticDualDomain g H M := by
    have hlam0 : -H_min[Hdiag] < lam0 := by
      dsimp [lam0]
      have hlt : -H_min[Hdiag] < -H_min[Hdiag] + 1 := by
        linarith
      exact lt_of_lt_of_le hlt (le_max_right 0 (-H_min[Hdiag] + 1))
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hlam0
  have hlam0_le : ψ lam0 ≤ ψ lamStar := by
    exact (isMaxOn_iff.mp hmax) lam0 ⟨hlam0_dom, hlam0_nonneg⟩
  have hdom : lamStar ∈ cubicRegularizedQuadraticDualDomain g H M := by
    rw [mem_cubicRegularizedQuadraticDualDomain_iff]
    exact lt_of_lt_of_le
      ((mem_cubicRegularizedQuadraticDualDomain_iff g H M lam0).mp hlam0_dom)
      hlam0_le
  have hnonneg : 0 ≤ lamStar := by
    by_contra hneg
    have hlam : -H_min[Hdiag] < lamStar := by
      simpa [Set.mem_Ioi,
        cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
          (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hdom
    have hHmin_pos : 0 < H_min[Hdiag] := by
      linarith
    have hzero_dom : 0 ∈ cubicRegularizedQuadraticDualDomain g H M := by
      have hzero : -H_min[Hdiag] < (0 : ℝ) := by
        linarith
      simpa [Set.mem_Ioi,
        cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
          (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hzero
    have hmax0 : ψ 0 ≤ ψ lamStar := by
      exact (isMaxOn_iff.mp hmax) 0 ⟨hzero_dom, le_rfl⟩
    have hclosedStar :
        ψ lamStar =
          ((-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lamStar) -
            (1 / 2 : ℝ) *
              Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
                (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamStar)) -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lamStar| ^ (3 : ℕ) : ℝ) : EReal) := by
      exact cubicRegularizedQuadraticDualFunction_eq_closedForm_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos lamStar hdom
    have hclosedZero :
        ψ 0 =
          ((-(1 / 2 : ℝ) * G²[g;Hdiag] / H_min[Hdiag] -
            (1 / 2 : ℝ) *
              Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
                (fun i ↦ (g i) ^ (2 : ℕ) / Hdiag i) : ℝ) : EReal) := by
      simpa using
        (cubicRegularizedQuadraticDualFunction_eq_closedForm_of_activeGradientSquare_pos
          (g := g) (Hdiag := Hdiag) (M := M) hM hGpos 0 hzero_dom)
    have hactive_strict :
        -(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lamStar) <
          -(1 / 2 : ℝ) * G²[g;Hdiag] / H_min[Hdiag] := by
      have hshift_pos : 0 < H_min[Hdiag] + lamStar := by
        linarith
      field_simp [hshift_pos.ne', hHmin_pos.ne']
      nlinarith
    have hinactive_le :
        -(1 / 2 : ℝ) *
            Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
              (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamStar)) ≤
          -(1 / 2 : ℝ) *
            Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
              (fun i ↦ (g i) ^ (2 : ℕ) / Hdiag i) := by
      have hsum :
          Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
              (fun i ↦ (g i) ^ (2 : ℕ) / Hdiag i) ≤
            Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
              (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamStar)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
          diagonalMinimum_le_entry (Hdiag := Hdiag) i
        have hdiag_pos : 0 < Hdiag i := by
          linarith
        have hshift_pos : 0 < Hdiag i + lamStar := by
          linarith
        field_simp [hdiag_pos.ne', hshift_pos.ne']
        nlinarith [sq_nonneg (g i)]
      nlinarith
    have hcubic_strict :
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lamStar| ^ (3 : ℕ)) < 0 := by
      have hcoeff_pos : 0 < (2 / (3 * M ^ (2 : ℕ)) : ℝ) := by
        positivity
      have hlam_ne : lamStar ≠ 0 := by
        linarith
      have habs_pos : 0 < |lamStar| := abs_pos.mpr hlam_ne
      have hpow_pos : 0 < |lamStar| ^ (3 : ℕ) := by
        positivity
      nlinarith
    have hstar_lt_zero :
        (-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lamStar) -
            (1 / 2 : ℝ) *
              Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
                (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamStar)) -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lamStar| ^ (3 : ℕ)) <
          (-(1 / 2 : ℝ) * G²[g;Hdiag] / H_min[Hdiag] -
            (1 / 2 : ℝ) *
              Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
                (fun i ↦ (g i) ^ (2 : ℕ) / Hdiag i)) := by
      nlinarith
    have hlt : ψ lamStar < ψ 0 := by
      rw [hclosedStar, hclosedZero]
      exact EReal.coe_lt_coe_iff.2 hstar_lt_zero
    exact (not_le_of_gt hlt) hmax0
  exact ⟨hdom, hnonneg⟩

/-- Helper for Theorem 4.1.10: a scalar dual maximizer over `dom ψ ∩ ℝ₊` induces the
corresponding maximizer of the packaged one-constraint epigraph dual problem. -/
lemma resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag])
    {lamStar : ℝ}
    (hmax : IsMaxOn ψ Dplus lamStar) :
    IsMaxOn
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet
      (EuclideanSpace.single 0 lamStar) := by
  -- Move epigraph-feasible multipliers back to the scalar feasible set via the unique coordinate.
  rw [isMaxOn_iff]
  intro μ hμ
  have hμ_scalar : μ 0 ∈ Dplus :=
    scalar_coordinate_mem_Dplus_of_epigraph_dualFeasible
      (g := g) (Hdiag := Hdiag) (M := M) hμ
  have hle_scalar :
      ψ (μ 0) ≤ ψ lamStar :=
    (isMaxOn_iff.mp hmax) (μ 0) hμ_scalar
  -- Collapse the one-dimensional multiplier comparison back to the scalar dual function.
  simpa [dual_certificate_multiplier_eq_single (lam := μ),
    cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction] using hle_scalar

/-- Helper for Theorem 4.1.10: evaluating the scalar Lagrangian at the tight slack
`τ = ‖h‖²` recovers the primal cubic objective. -/
lemma resolvent_scalar_lagrangian_at_norm_sq_eq_objective
    (h : E) (lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h (‖h‖ ^ (2 : ℕ)) lam =
      v h := by
  -- At tight slack, the multiplier term vanishes and only the cubic objective remains.
  have hpow : ((‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) = ‖h‖ ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg h) 2 (3 / 2 : ℝ)]
    norm_num
  rw [cubicRegularizedQuadraticScalarLagrangian, cubicRegularizedQuadraticObjective_apply]
  have hlin :
      lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) = 0 := by
    ring
  rw [hlin]
  simp [hpow]

/-- Helper for Theorem 4.1.10: every multiplier in the certificate ball stays in the interior
domain half-line `(-H_min, ∞)`. -/
lemma resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
    {lamStar : ℝ}
    (hlam : -H_min[Hdiag] < lamStar)
    {lam : Λ}
    (hmem :
      lam ∈
        Metric.closedBall (EuclideanSpace.single 0 lamStar)
          ((lamStar + H_min[Hdiag]) / 2) ∩ ℝ₊^1) :
    -H_min[Hdiag] < lam 0 := by
  rcases hmem with ⟨hball, _⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  -- In `ℝ¹`, the closed-ball condition is exactly an absolute-value bound on the unique
  -- coordinate.
  have habs : |lam 0 - lamStar| ≤ (lamStar + H_min[Hdiag]) / 2 := by
    simpa [show lam - EuclideanSpace.single 0 lamStar =
        EuclideanSpace.single 0 (lam 0 - lamStar) by
          ext i
          fin_cases i
          rfl, PiLp.norm_single, Real.norm_eq_abs] using hball
  have hlower : -((lamStar + H_min[Hdiag]) / 2) ≤ lam 0 - lamStar :=
    (abs_le.mp habs).1
  linarith [hlam]

/-- Helper for Theorem 4.1.10: the certificate path varies continuously at the maximizing
multiplier. -/
lemma resolvent_tau_certificate_continuousAt
    {lamStar : ℝ}
    (hlam : -H_min[Hdiag] < lamStar) :
    ContinuousAt
      (fun lam : Λ ↦ resolventTauCertificatePoint g Hdiag M (lam 0))
      (EuclideanSpace.single 0 lamStar) := by
  -- First expose the unique scalar coordinate of the multiplier space `Λ = ℝ¹`.
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
        (fun lam : Λ ↦ resolventCertificateVector g Hdiag (lam 0))
        (EuclideanSpace.single 0 lamStar) := by
    -- Each coordinate is a rational function in the unique scalar coordinate `lam 0`.
    change ContinuousAt
      (fun lam : Λ ↦
        WithLp.toLp 2 (fun i : Fin n ↦ -g i / (Hdiag i + lam 0)))
      (EuclideanSpace.single 0 lamStar)
    refine (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp ?_
    rw [continuousAt_pi]
    intro i
    have hdenom_pos : 0 < Hdiag i + lamStar := by
      have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
        diagonalMinimum_le_entry (Hdiag := Hdiag) i
      linarith
    have hdenom : Hdiag i + lamStar ≠ 0 := ne_of_gt hdenom_pos
    simpa [resolventCertificateVector, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (continuousAt_const.mul ((continuousAt_const.add hcoord0).inv₀ hdenom))
  have htau :
      ContinuousAt
        (fun lam : Λ ↦ cubicRegularizedQuadraticTauMinimizer M (lam 0))
        (EuclideanSpace.single 0 lamStar) := by
    -- The slack coordinate uses the explicit polynomial-absolute-value formula for `τ(λ)`.
    have hbase :
        ContinuousAt (fun lam : Λ ↦ (4 : ℝ) * (lam 0 * |lam 0|))
          (EuclideanSpace.single 0 lamStar) := by
      exact continuousAt_const.mul (hcoord0.mul hcoord0.abs)
    simpa [cubicRegularizedQuadraticTauMinimizer, pow_two, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using hbase.const_mul ((M ^ (2 : ℕ))⁻¹)
  -- Package the continuous vector and slack coordinates back into the certificate point.
  simpa [resolventTauCertificatePoint] using hvector.prodMk htau

/-- Helper for Theorem 4.1.10: the explicit resolvent certificate at a maximizing multiplier
attains the dual value, and its `h`-coordinate is a global minimizer of the primal objective. -/
lemma resolvent_certificate_value_and_isMinOn
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn ψ Dplus lamStar) :
    ψ lamStar =
      (v (resolventCertificateVector g Hdiag lamStar) : EReal) ∧
      IsMinOn v Set.univ (resolventCertificateVector g Hdiag lamStar) := by
  let xPath : Λ → E × ℝ :=
    fun lam ↦ resolventTauCertificatePoint g Hdiag M (lam 0)
  let xStar : E × ℝ :=
    resolventTauCertificatePoint g Hdiag M lamStar
  let hStar : E :=
    resolventCertificateVector g Hdiag lamStar
  let ε : ℝ := (lamStar + H_min[Hdiag]) / 2
  have hDplus : lamStar ∈ Dplus := by
    exact scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
      (g := g) (Hdiag := Hdiag) (M := M) hM hGpos hmax
  have hlam : -H_min[Hdiag] < lamStar := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hxStar :
      xStar ∈ (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 lamStar) := by
    -- The source certificate point minimizes the Lagrangian at the maximizing multiplier.
    simpa [xStar] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M) hM
        (μ := lamStar) hlam
  have hepigraph_max :
      IsMaxOn
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet
        (EuclideanSpace.single 0 lamStar) := by
    exact
      resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos hmax
  have hlamStar :
      EuclideanSpace.single 0 lamStar ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet :=
    by
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
        resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
          (Hdiag := Hdiag) (lamStar := lamStar) hlam hmem
    rw [dual_certificate_multiplier_eq_single (lam := lam)]
    simpa [xPath] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := g) (Hdiag := Hdiag) (M := M) hM
        (μ := lam 0) hlam_mem
  have hlim :
      Tendsto xPath
        (nhdsWithin (EuclideanSpace.single 0 lamStar)
          ((Metric.closedBall (EuclideanSpace.single 0 lamStar) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 lamStar}))
        (nhds xStar) := by
    -- The punctured-neighborhood limit follows from ordinary continuity of the certificate path.
    have hcontPath :
        ContinuousAt xPath (EuclideanSpace.single 0 lamStar) := by
      simpa [xPath] using
        resolvent_tau_certificate_continuousAt
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
    -- The packaged constraint map is continuous because its single coordinate is polynomial.
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
    -- Apply the Chapter 1 dual-certificate theorem to the source-faithful certificate path.
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
    exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber g H M hStar
  have hopt_le_tight :
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar ≤
        (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
    (isMinOn_iff.mp hxmin) _ htight_feas_star
  have htight_le_opt :
      (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) ≤
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar := by
    simpa [xStar, hStar] using
      cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible
        g H M (le_of_lt hM) hxfeas
  have hxStar_eq_objective :
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar = v hStar := by
    have htight_eq :
        (cubicRegularizedQuadraticEpigraphProblem g H M) xStar =
          (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
      le_antisymm hopt_le_tight htight_le_opt
    calc
      (cubicRegularizedQuadraticEpigraphProblem g H M) xStar =
          (cubicRegularizedQuadraticEpigraphProblem g H M) (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
        htight_eq
      _ = v hStar :=
        cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M hStar
  have hvalue :
      ψ lamStar = (v hStar : EReal) := by
    -- Evaluate the scalar dual value through the epigraph dual owner and the tight-slack equality.
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
    -- Compare the epigraph optimum with every tight feasible slack point `(h, ‖h‖²)`.
    rw [isMinOn_univ_iff]
    intro h
    have hfeas_h :
        (h, ‖h‖ ^ (2 : ℕ)) ∈
          (cubicRegularizedQuadraticEpigraphProblem g H M).feasibleSet := by
      exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber g H M h
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
  simpa [hStar] using And.intro hvalue hmin

-- Proof sketch: combine the positivity assumption `G² > 0` with the diagonal analysis of the
-- shifted quadratic subproblem to identify the maximizing dual parameter range. Then apply strong
-- duality for the epigraph reformulation to identify the primal infimum with the dual value at a
-- nonnegative dual maximizer.
/-- Strong-duality consequence of Theorem 4.1.10: for the diagonal cubic-regularized quadratic
model with `H = diag(Hdiag)`,
if `G² = ∑_{i : Hdiag i = H_min} (g i)^2` is positive, then every nonnegative dual maximizer on
`cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici 0` yields strong duality:
the minimum of the primal objective equals the dual value `ψ(λ*)`.
The companion entries in this file record the strong-duality consequences, the explicit primal
minimizer, and the owner-level formula
`cubicRegularizedQuadraticTauMinimizer_def` for the associated slack minimizer `τ(λ*)`. -/
theorem
    cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    sInf (Set.range fun h : E ↦
      (cubicRegularizedQuadraticObjective g H M h : EReal)) =
        cubicRegularizedQuadraticDualFunction g H M lamStar := by
  let hStar : E := resolventCertificateVector g Hdiag lamStar
  have hcert :
      ψ lamStar = (v hStar : EReal) ∧ IsMinOn v Set.univ hStar := by
    simpa [hStar] using
      resolvent_certificate_value_and_isMinOn
        hM hGpos hmax
  rcases hcert with ⟨hvalue, hmin⟩
  -- The attained primal minimum identifies the infimum of the whole objective range.
  refine le_antisymm ?_ ?_
  · calc
      sInf (Set.range fun h : E ↦ (v h : EReal)) ≤ (v hStar : EReal) :=
        sInf_le ⟨hStar, rfl⟩
      _ = ψ lamStar := hvalue.symm
  · refine le_sInf ?_
    rintro y ⟨h, rfl⟩
    have hle : v hStar ≤ v h :=
      (isMinOn_univ_iff.mp hmin) h
    calc
      ψ lamStar = (v hStar : EReal) := hvalue
      _ ≤ (v h : EReal) := by
        exact_mod_cast hle

-- Proof sketch: solve the shifted quadratic subproblem at the maximizing multiplier `λ*`, using
-- the positivity assumption `G² > 0` and the optimality relations from the strong-duality
-- statement to show that the resolvent point minimizes the primal cubic objective.
/-- Under the hypotheses of
`cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos`,
the primal problem admits the explicit global minimizer
`h* = -(H + λ* I)⁻¹ g`. -/
theorem
    cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := by
  have hDplus : lamStar ∈ Dplus := by
    exact scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
      (g := g) (Hdiag := Hdiag) (M := M) hM hGpos hmax
  have hlam : -H_min[Hdiag] < lamStar := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  let hStar : E := resolventCertificateVector g Hdiag lamStar
  have hcert :
      ψ lamStar = (v hStar : EReal) ∧ IsMinOn v Set.univ hStar := by
    simpa [hStar] using
      resolvent_certificate_value_and_isMinOn
        hM hGpos hmax
  have hmin : IsMinOn v Set.univ hStar :=
    hcert.2
  have hres :
      hStar = -((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g := by
    -- Rewrite the coordinatewise certificate as the explicit matrix resolvent point.
    simpa [hStar] using
      resolventCertificateVector_eq_explicit g Hdiag (μ := lamStar) hlam
  simpa [hres] using hmin

-- Proof sketch: bundle the already-established domain identity, strong-duality identity,
-- explicit primal minimizer, and `τ(λ*)` formula into the source-facing entry theorem.
/-- Theorem 4.1.10: assume `G²[g; Hdiag] > 0`. Then
`cubicRegularizedQuadraticDualDomain g H M = Set.Ioi (-H_min[Hdiag])`. Moreover, for every
maximizer `lamStar` of `ψ` on `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici 0`, strong
duality holds, the explicit resolvent point `-((H + lamStar I)⁻¹) g` is a global minimizer of
the primal objective, and `cubicRegularizedQuadraticTauMinimizer M lamStar = 4 lamStar |lamStar| /
M²`. -/
theorem cubicRegularizedQuadraticDiagonal_dualMaximizer_consequences_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    cubicRegularizedQuadraticDualDomain g H M = Set.Ioi (-H_min[Hdiag]) ∧
      sInf (Set.range fun h : E ↦
        (cubicRegularizedQuadraticObjective g H M h : EReal)) =
          cubicRegularizedQuadraticDualFunction g H M lamStar ∧
      IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
        (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) ∧
      cubicRegularizedQuadraticTauMinimizer M lamStar =
        (4 : ℝ) * lamStar * |lamStar| / M ^ (2 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos
  · exact
      cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos hmax
  · have hprimal :
        IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
          (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) :=
    cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos
      (g := g) (Hdiag := Hdiag) (M := M) hM hGpos hmax
    exact hprimal
  · exact cubicRegularizedQuadraticTauMinimizer_def M lamStar

/- The source formula `τ(λ*) = 4 λ* |λ*| / M²` is already the exact owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end
