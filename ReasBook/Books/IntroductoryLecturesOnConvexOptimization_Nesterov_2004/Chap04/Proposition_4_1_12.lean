/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_10_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology ConstrainedArgmin EuclideanOrthant
open scoped CubicRegularizedDiagonalInvariants

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.12 lies in the diagonal cubic-regularized quadratic / boundary-degeneration
domain.

Sampled owner declarations:
* `cubicRegularizedDiagonalPerturbedGradient` in `Proposition_4_1_11`, the source-facing owner of
  the perturbation `g + δ e_k`;
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the nondegenerate dual-domain owner for `G² > 0`;
* `cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos`
  in `Theorem_4_1_10`, the diagonal owner theorem sending a nondegenerate dual maximizer to the
  corresponding primal minimizer;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the coordinate bridge for
  the canonical diagonal resolvent point;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_10`, the owner-level minimizer
  theorem for that same resolvent point.

Best owner abstraction:
* source-facing: the explicit boundary limit point in the degenerate case;
* core/canonical: the diagonal resolvent point
  `-((Matrix.diagonal fun i ↦ Hdiag i + lam)⁻¹).mulVec g'`;
* bridge/view: the coordinate formulas identifying that resolvent with the textbook entrywise
  description.

Primitive data:
* `g`, `Hdiag`, `M`, the active index `k`, and the perturbed gradient
  `cubicRegularizedDiagonalPerturbedGradient g k δ`.

Derived API:
* the canonical diagonal resolvent expression above, already supported upstream by the existing
  owner-level minimizer theorems;
* the strict interior fact `-H_min < λ_δ*`, derived upstream from perturbed dual optimality in the
  nondegenerate `G² > 0` regime;
* the source-facing boundary limit point `cubicRegularizedDiagonalBoundaryMinimizer`.

This file therefore keeps the boundary-point owner, records the corrected boundary-feasible
canonical resolvent-branch statement as auxiliary API, and avoids presenting that strengthened
statement as the verbatim textbook proposition when the quoted source context is insufficient. -/

/-- The boundary point obtained by letting the perturbed minimizers approach the degenerate dual
boundary `λ = -H_min` while keeping the `k`-th active coordinate negative. -/
def cubicRegularizedDiagonalBoundaryMinimizer
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n) : E :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦
    if i = k then
      -Real.sqrt
        ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    else if i ∈ I*[Hdiag] then
      0
    else
      -g i / (Hdiag i - H_min[Hdiag])

/-- Evaluating `cubicRegularizedDiagonalBoundaryMinimizer` gives the inactive-coordinate formula
`-g^(i) / (H_i - H_min)`, the zero coordinates on `I* \\ {k}`, and the negative square-root value
for the distinguished active coordinate `k`. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalBoundaryMinimizer`.
theorem cubicRegularizedDiagonalBoundaryMinimizer_apply
    (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k i : Fin n) :
    cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k i =
      if i = k then
        -Real.sqrt
          ((4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
            Finset.sum
              (Finset.univ.filter fun j : Fin n ↦
                j ∉ I*[Hdiag])
              (fun j ↦
                (g j) ^ (2 : ℕ) /
                  (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
      else if i ∈ I*[Hdiag] then
        0
      else
        -g i / (Hdiag i - H_min[Hdiag]) := by
  simp [cubicRegularizedDiagonalBoundaryMinimizer]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ) (k : Fin n)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
local notation "gδ(" δ ")" => (g + EuclideanSpace.single k δ : E)
local notation "Aδ(" lamDelta "," δ ")" => Matrix.diagonal fun i ↦ Hdiag i + lamDelta δ
local notation "hδ(" lamDelta "," δ ")" => -Matrix.mulVec ((Aδ(lamDelta, δ))⁻¹) (gδ(δ))
local notation "Λ" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Proposition 4.1.12: a multiplier in `ℝ¹` is determined by its unique coordinate. -/
private lemma prop412DualCertificateMultiplier_eq_single
    (lam : Λ) :
    lam = EuclideanSpace.single 0 (lam 0) := by
  ext i
  fin_cases i
  rfl

/-- Helper for Proposition 4.1.12: the coordinatewise resolvent certificate
`i ↦ -g i / (Hdiag i + μ)`. -/
private def prop412ResolventCertificateVector
    (g : E) (Hdiag : Fin n → ℝ) (μ : ℝ) : E :=
  WithLp.toLp 2 (fun i : Fin n ↦ -g i / (Hdiag i + μ))

/-- Helper for Proposition 4.1.12: on `(-H_min[Hdiag], ∞)`, the coordinatewise resolvent
certificate agrees with the canonical matrix resolvent point. -/
private lemma prop412ResolventCertificateVector_eq_explicit
    (g : E) {μ : ℝ} (hμ : -H_min[Hdiag] < μ) :
    prop412ResolventCertificateVector g Hdiag μ =
      diagonalResolventPoint (g := g) (Hdiag := Hdiag) μ := by
  -- Compare coordinates against the owner-level diagonal resolvent formula.
  ext i
  simpa [prop412ResolventCertificateVector, diagonalResolventPoint, shiftedDiagonalMatrix,
    Matrix.toLpLin_apply] using
    (diagonalResolventPoint_apply (g := g) (Hdiag := Hdiag) (lam := μ) hμ i).symm

/-- Helper for Proposition 4.1.12: the epigraph certificate point pairing the resolvent vector
with the slack minimizer `τ(μ)`. -/
private def prop412ResolventTauCertificatePoint
    (g : E) (Hdiag : Fin n → ℝ) (M μ : ℝ) : E × ℝ :=
  (prop412ResolventCertificateVector g Hdiag μ,
    cubicRegularizedQuadraticTauMinimizer M μ)

local notation "dual_certificate_multiplier_eq_single" =>
  prop412DualCertificateMultiplier_eq_single
local notation "resolventCertificateVector" =>
  prop412ResolventCertificateVector
local notation "resolventTauCertificatePoint" =>
  prop412ResolventTauCertificatePoint

/-- Helper for Proposition 4.1.12: every interior resolvent certificate minimizes the epigraph
Lagrangian at the corresponding multiplier. -/
private lemma prop412ResolventTauCertificate_mem_lagrangianMinimizers
    (g : E) [NeZero n] (hM : 0 < M)
    {μ : ℝ} (hμ : -H_min[Hdiag] < μ) :
    resolventTauCertificatePoint g Hdiag M μ ∈
      (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 μ) := by
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_univ_iff]
  intro y
  have hquad_min :
      IsMinOn
        (quadraticObjective 0 g (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)))
        Set.univ
        (resolventCertificateVector g Hdiag μ) := by
    -- Rewrite the certificate vector to the owner-level resolvent point before applying its
    -- minimizer theorem.
    have hres :
        resolventCertificateVector g Hdiag μ =
          diagonalResolventPoint (g := g) (Hdiag := Hdiag) μ := by
      simpa using
        (prop412ResolventCertificateVector_eq_explicit
          (g := g) (Hdiag := Hdiag) (μ := μ) hμ)
    simpa [hres, shiftedQuadraticObjective, shiftedDiagonalMatrix, diagonalResolventPoint,
      diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag)] using
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
  rw [cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq,
    cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq]
  simpa [prop412ResolventTauCertificatePoint,
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term] using hsum

/-- Helper for Proposition 4.1.12: an epigraph-dual-feasible multiplier has scalar coordinate in
`dom ψ ∩ ℝ₊`. -/
private lemma prop412ScalarCoordinate_mem_Dplus_ofEpigraphDualFeasible
    (g : E) {μ : Λ}
    (hμ : μ ∈ (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet) :
    μ 0 ∈ Dplus(g) := by
  rw [(cubicRegularizedQuadraticEpigraphProblem g H M).mem_dualFeasibleSet_iff] at hμ
  rcases hμ with ⟨hdom, hnonneg⟩
  have hdual_lt :
      ⊥ <
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction μ := by
    rw [(cubicRegularizedQuadraticEpigraphProblem g H M).mem_dualDomain_iff] at hdom
    exact hdom
  have hdual_eq :
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction μ =
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 (μ 0)) :=
    congrArg
      (fun lam ↦
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction lam)
      (dual_certificate_multiplier_eq_single (lam := μ))
  have hscalar_dom :
      μ 0 ∈ cubicRegularizedQuadraticDualDomain g H M := by
    rw [mem_cubicRegularizedQuadraticDualDomain_iff,
      cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    rw [← hdual_eq]
    exact hdual_lt
  exact ⟨hscalar_dom, hnonneg 0⟩

/-- Helper for Proposition 4.1.12: in the positive-`G²` regime, any scalar dual maximizer is
itself a point of `dom ψ ∩ ℝ₊`. -/
private lemma prop412ScalarDualMaximizer_mem_Dplus_of_activeGradientSquare_pos
    (g : E) (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax :
      IsMaxOn
        (cubicRegularizedQuadraticDualFunction g H M)
        Dplus(g)
        lamStar) :
    lamStar ∈ Dplus(g) := by
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
  have hlam0_le :
      cubicRegularizedQuadraticDualFunction g H M lam0 ≤
        cubicRegularizedQuadraticDualFunction g H M lamStar :=
    (isMaxOn_iff.mp hmax) lam0 ⟨hlam0_dom, hlam0_nonneg⟩
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
    have hmax0 :
        cubicRegularizedQuadraticDualFunction g H M 0 ≤
          cubicRegularizedQuadraticDualFunction g H M lamStar :=
      (isMaxOn_iff.mp hmax) 0 ⟨hzero_dom, by simpa using (show (0 : ℝ) ≤ 0 by rfl)⟩
    have hclosedStar :
        cubicRegularizedQuadraticDualFunction g H M lamStar =
          ((-(1 / 2 : ℝ) * G²[g;Hdiag] / (H_min[Hdiag] + lamStar) -
            (1 / 2 : ℝ) *
              Finset.sum (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
                (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamStar)) -
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lamStar| ^ (3 : ℕ) : ℝ) : EReal) := by
      exact cubicRegularizedQuadraticDualFunction_eq_closedForm_of_activeGradientSquare_pos
        (g := g) (Hdiag := Hdiag) (M := M) hM hGpos lamStar hdom
    have hclosedZero :
        cubicRegularizedQuadraticDualFunction g H M 0 =
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
    have hlt :
        cubicRegularizedQuadraticDualFunction g H M lamStar <
          cubicRegularizedQuadraticDualFunction g H M 0 := by
      rw [hclosedStar, hclosedZero]
      exact EReal.coe_lt_coe_iff.2 hstar_lt_zero
    exact (not_le_of_gt hlt) hmax0
  exact ⟨hdom, hnonneg⟩

local notation "scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos" =>
  prop412ScalarDualMaximizer_mem_Dplus_of_activeGradientSquare_pos

/-- Helper for Proposition 4.1.12: a scalar dual maximizer induces the corresponding epigraph dual
maximizer in the one-constraint packaging. -/
private lemma prop412ResolventEpigraphDualMaximizer_of_scalarDualMaximizer
    (g : E) (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag])
    {lamStar : ℝ}
    (hmax :
      IsMaxOn
        (cubicRegularizedQuadraticDualFunction g H M)
        Dplus(g)
        lamStar) :
    IsMaxOn
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFeasibleSet
      (EuclideanSpace.single 0 lamStar) := by
  rw [isMaxOn_iff]
  intro μ hμ
  have hμ_scalar : μ 0 ∈ Dplus(g) :=
    prop412ScalarCoordinate_mem_Dplus_ofEpigraphDualFeasible
      (g := g) (hμ := hμ)
  have hle_scalar :
      cubicRegularizedQuadraticDualFunction g H M (μ 0) ≤
        cubicRegularizedQuadraticDualFunction g H M lamStar :=
    (isMaxOn_iff.mp hmax) (μ 0) hμ_scalar
  have hμ_eq : μ = EuclideanSpace.single 0 (μ 0) :=
    dual_certificate_multiplier_eq_single (lam := μ)
  have hdual_eq :
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction μ =
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 (μ 0)) :=
    congrArg
      (fun l ↦
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction l)
      hμ_eq
  calc
    (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction μ =
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 (μ 0)) := hdual_eq
    _ = cubicRegularizedQuadraticDualFunction g H M (μ 0) := by
          rw [← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    _ ≤ cubicRegularizedQuadraticDualFunction g H M lamStar := hle_scalar
    _ = (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 lamStar) := by
            rw [cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]

local notation "resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer" =>
  prop412ResolventEpigraphDualMaximizer_of_scalarDualMaximizer

/-- Helper for Proposition 4.1.12: every multiplier in the certificate ball stays in the interior
half-line `(-H_min[Hdiag], ∞)`. -/
private lemma prop412ResolventMultiplierCoord_gt_negDiagonalMinimum_of_mem_certificate_ball
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
  have habs : |lam 0 - lamStar| ≤ (lamStar + H_min[Hdiag]) / 2 := by
    simpa [show lam - EuclideanSpace.single 0 lamStar =
        EuclideanSpace.single 0 (lam 0 - lamStar) by
          ext i
          fin_cases i
          rfl, PiLp.norm_single, Real.norm_eq_abs] using hball
  have hlower : -((lamStar + H_min[Hdiag]) / 2) ≤ lam 0 - lamStar :=
    (abs_le.mp habs).1
  linarith [hlam]

local notation "resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball" =>
  prop412ResolventMultiplierCoord_gt_negDiagonalMinimum_of_mem_certificate_ball

/-- Helper for Proposition 4.1.12: the certificate path depends continuously on the multiplier. -/
private lemma prop412ResolventTauCertificate_continuousAt
    (g : E) [NeZero n] {lamStar : ℝ}
    (hlam : -H_min[Hdiag] < lamStar) :
    ContinuousAt
      (fun lam : Λ ↦ resolventTauCertificatePoint g Hdiag M (lam 0))
      (EuclideanSpace.single 0 lamStar) := by
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
    simpa [prop412ResolventCertificateVector] using
      (continuousAt_const.neg.div (continuousAt_const.add hcoord0) hdenom)
  have htau :
      ContinuousAt
        (fun lam : Λ ↦ cubicRegularizedQuadraticTauMinimizer M (lam 0))
        (EuclideanSpace.single 0 lamStar) := by
    have hbase :
        ContinuousAt (fun lam : Λ ↦ (4 : ℝ) * (lam 0 * |lam 0|))
          (EuclideanSpace.single 0 lamStar) := by
      exact continuousAt_const.mul (hcoord0.mul hcoord0.abs)
    simpa [cubicRegularizedQuadraticTauMinimizer, pow_two, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using hbase.const_mul ((M ^ (2 : ℕ))⁻¹)
  simpa [prop412ResolventTauCertificatePoint] using hvector.prodMk htau

local notation "resolvent_tau_certificate_continuousAt" =>
  prop412ResolventTauCertificate_continuousAt
local notation "resolvent_tau_certificate_mem_lagrangianMinimizers" =>
  prop412ResolventTauCertificate_mem_lagrangianMinimizers

/-- Helper for Proposition 4.1.12: if the active gradient mass `G²[g; Hdiag]` vanishes, then
every active coordinate of `g` must itself vanish. -/
private lemma active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
    (hGzero : G²[g;Hdiag] = 0)
    {i : Fin n} (hi : i ∈ I*[Hdiag]) :
    g i = 0 := by
  -- The active squared mass is a sum of nonnegative squares, so a zero sum kills each term.
  have hsum_zero :
      ∀ j ∈ I*[Hdiag], (g j) ^ (2 : ℕ) = 0 := by
    have hzero :
        Finset.sum (I*[Hdiag]) (fun j ↦ (g j) ^ (2 : ℕ)) = 0 := by
      simpa [cubicRegularizedMinimalDiagonalGradientSquare] using hGzero
    exact (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hzero
  have hi_sq : (g i) ^ (2 : ℕ) = 0 :=
    hsum_zero i hi
  exact sq_eq_zero_iff.mp <| by simpa [pow_two] using hi_sq

/-- Helper for Proposition 4.1.12: perturbing an active coordinate `k ∈ I*` by `δ` turns the
degenerate active squared mass `G² = 0` into the nondegenerate value `δ²`. -/
private lemma perturbed_activeGradientSquare_eq_delta_sq_prop412
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (δ : ℝ) :
    G²[gδ(δ);Hdiag] = δ ^ (2 : ℕ) := by
  -- On `I* \ {k}` the perturbed gradient still vanishes, while the `k`-coordinate becomes `δ`.
  rw [cubicRegularizedMinimalDiagonalGradientSquare]
  rw [Finset.sum_eq_single k]
  · have hgk_zero : g k = 0 :=
      active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
        hGzero hk
    simp [hgk_zero]
  · intro i hi hik
    have hgi_zero : g i = 0 :=
      active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
        hGzero hi
    simp [hgi_zero, hik]
  · simp [hk]

/-- Helper for Proposition 4.1.12: an index outside the minimal set `I*` has strictly larger
diagonal entry than `H_min`. -/
lemma inactive_diagonal_gap_pos
    {i : Fin n} (hi : i ∉ I*[Hdiag]) :
    0 < Hdiag i - H_min[Hdiag] := by
  -- Inactivity means `Hdiag i ≠ H_min`, and diagonal minimality gives the opposite inequality.
  have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
    diagonalMinimum_le_entry Hdiag i
  have hne : Hdiag i ≠ H_min[Hdiag] := by
    intro hi_eq
    exact hi ((mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).2 hi_eq)
  have hlt : H_min[Hdiag] < Hdiag i :=
    lt_of_le_of_ne hmin_le (Ne.symm hne)
  exact sub_pos.mpr hlt

/-- Helper for Proposition 4.1.12: every perturbed dual maximizer lies in the strict interior
region `-H_min < λ_δ*`. -/
lemma perturbed_dualMaximizer_gt_boundary
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    -H_min[Hdiag] < lamDelta δ := by
  -- The perturbed active mass is positive, so the nondegenerate dual domain is `(-H_min, ∞)`.
  have hGpos : 0 < G²[gδ(δ);Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq_prop412
      hk hGzero δ]
    positivity
  have hdom_eq :
      cubicRegularizedQuadraticDualDomain (gδ(δ)) H M = Set.Ioi (-H_min[Hdiag]) :=
    cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
      (gδ(δ)) Hdiag M hM hGpos
  have hlam_mem : lamDelta δ ∈ Dplus(gδ(δ)) := (hopt_max hδ).1
  -- Membership in `Dplus` immediately places the maximizer inside the interior dual domain.
  rw [hdom_eq] at hlam_mem
  exact hlam_mem.1

/-- Helper for Proposition 4.1.12: the distinguished denominator
`H_min + λ_δ*` is strictly positive for every perturbed dual maximizer. -/
lemma perturbed_dualMaximizer_denominator_pos
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    0 < H_min[Hdiag] + lamDelta δ := by
  have hlam : -H_min[Hdiag] < lamDelta δ :=
    perturbed_dualMaximizer_gt_boundary
      lamDelta hM hk hGzero hopt_max hδ
  -- Rearranging the strict boundary inequality gives the denominator positivity.
  linarith

/-- Helper for Proposition 4.1.12: the distinguished perturbed resolvent coordinate is the
explicit negative fraction `-δ / (H_min + λ_δ*)`. -/
lemma distinguished_coordinate_eq_neg_div
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    hδ(lamDelta, δ) k = -δ / (H_min[Hdiag] + lamDelta δ) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hlam : -H_min[Hdiag] < lamDelta δ :=
    perturbed_dualMaximizer_gt_boundary
      lamDelta hM hk hGzero hopt_max hδ
  have hgk_zero : g k = 0 :=
    active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
      hGzero hk
  have hk_min : Hdiag k = H_min[Hdiag] :=
    (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag k).mp hk
  -- Evaluate the perturbed resolvent at the distinguished active coordinate and simplify.
  have hcoord :
      hδ(lamDelta, δ) k =
        -((g + EuclideanSpace.single k δ : E) k) / (Hdiag k + lamDelta δ) := by
    simpa using
      (cubicRegularizedDiagonalResolvent_apply
        (g + EuclideanSpace.single k δ : E) Hdiag (lamDelta δ) hlam k)
  rw [hcoord]
  change -((g k + if k = k then δ else 0)) / (Hdiag k + lamDelta δ) =
    -δ / (H_min[Hdiag] + lamDelta δ)
  simp [hgk_zero, hk_min]

/-- Helper for Proposition 4.1.12: the squared norm of the perturbed resolvent splits into the
distinguished active contribution `δ² / (H_min + λ_δ*)²` and the unchanged inactive terms. -/
private lemma perturbedResolventNormSq_eq_boundaryLhs
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    ‖hδ(lamDelta, δ)‖ ^ (2 : ℕ) =
      δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦
            (g i) ^ (2 : ℕ) /
              (Hdiag i + lamDelta δ) ^ (2 : ℕ)) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hlam : -H_min[Hdiag] < lamDelta δ :=
    perturbed_dualMaximizer_gt_boundary
      lamDelta hM hk hGzero hopt_max hδ
  have hdenom_k_pos : 0 < H_min[Hdiag] + lamDelta δ :=
    perturbed_dualMaximizer_denominator_pos
      lamDelta hM hk hGzero hopt_max hδ
  have hgk_zero : g k = 0 :=
    active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
      hGzero hk
  have hk_min : Hdiag k = H_min[Hdiag] :=
    (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag k).mp hk
  have hactive_sum :
      Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∈ I*[Hdiag])
          (fun i ↦ (hδ(lamDelta, δ) i) ^ (2 : ℕ)) =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) := by
    -- Every active coordinate vanishes except the distinguished one `k`.
    rw [Finset.sum_eq_single k]
    · have hcoord_k :
          hδ(lamDelta, δ) k = -δ / (H_min[Hdiag] + lamDelta δ) :=
        distinguished_coordinate_eq_neg_div
          lamDelta hM hk hGzero hopt_max hδ
      rw [hcoord_k]
      field_simp [hdenom_k_pos.ne']
    · intro i hi hik
      have hi_active : i ∈ I*[Hdiag] := by
        simpa [Finset.mem_filter] using hi
      have hgi_zero : g i = 0 :=
        active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
          hGzero hi_active
      have hi_min : Hdiag i = H_min[Hdiag] :=
        (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).mp hi_active
      have hgrad_i : (gδ(δ)) i = 0 := by
        change g i + (if i = k then δ else 0) = 0
        simp [hgi_zero, hik]
      have hcoord_i :
          hδ(lamDelta, δ) i = 0 := by
        have hcoord_i' :
            hδ(lamDelta, δ) i =
              -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
          simpa using
            (cubicRegularizedDiagonalResolvent_apply
              (gδ(δ)) Hdiag (lamDelta δ) hlam i)
        rw [hcoord_i', hgrad_i]
        simp [hi_min]
      simp [hcoord_i]
    · simp [hk]
  have hinactive_sum :
      Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hδ(lamDelta, δ) i) ^ (2 : ℕ)) =
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦
            (g i) ^ (2 : ℕ) /
              (Hdiag i + lamDelta δ) ^ (2 : ℕ)) := by
    -- Off the active set, the perturbation disappears and only the original inactive entries stay.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_inactive : i ∉ I*[Hdiag] := by
      simpa [Finset.mem_filter] using hi
    have hdenom_i_pos : 0 < Hdiag i + lamDelta δ := by
      have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
        diagonalMinimum_le_entry Hdiag i
      linarith
    have hik : i ≠ k := by
      intro hik
      subst hik
      exact hi_inactive hk
    have hgrad_i : (gδ(δ)) i = g i := by
      change g i + (if i = k then δ else 0) = g i
      simp [hik]
    have hcoord_i :
        hδ(lamDelta, δ) i = -g i / (Hdiag i + lamDelta δ) := by
      have hcoord_i' :
          hδ(lamDelta, δ) i =
            -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
        simpa using
          (cubicRegularizedDiagonalResolvent_apply
            (gδ(δ)) Hdiag (lamDelta δ) hlam i)
      rw [hcoord_i', hgrad_i]
    rw [hcoord_i]
    field_simp [hdenom_i_pos.ne']
  -- Expand the Euclidean norm square and split the active and inactive contributions.
  calc
    ‖hδ(lamDelta, δ)‖ ^ (2 : ℕ) =
        ∑ i : Fin n, (hδ(lamDelta, δ) i) ^ (2 : ℕ) := by
          simpa using EuclideanSpace.real_norm_sq_eq (hδ(lamDelta, δ))
    _ =
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∈ I*[Hdiag])
          (fun i ↦ (hδ(lamDelta, δ) i) ^ (2 : ℕ)) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hδ(lamDelta, δ) i) ^ (2 : ℕ)) := by
            rw [← Finset.sum_filter_add_sum_filter_not
              Finset.univ (fun i : Fin n ↦ i ∈ I*[Hdiag])]
    _ =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hδ(lamDelta, δ) i) ^ (2 : ℕ)) := by
            rw [hactive_sum]
    _ =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦
            (g i) ^ (2 : ℕ) /
              (Hdiag i + lamDelta δ) ^ (2 : ℕ)) := by
            rw [hinactive_sum]

-- Semantic recall found no pre-existing mathlib owner for this boundary-degenerate limit
-- statement, so this item stays on the Chapter 4 diagonal dual-domain/resolvent API.
-- For the square-root coordinate, the only generic mathlib recall needed is `Real.sqrt_nonneg`;
-- the radicand sign is now kept as an explicit boundary-feasibility hypothesis.
--
-- Proof sketch: for each `δ > 0`, perturbed optimality gives the scalar boundary equation from
-- `Proposition_4_1_11` and places `λ_δ*` in the strict interior region `-H_min < λ_δ*`. The
-- proposition records that for the corresponding optimal dual branch the perturbed minimizers
-- converge to the displayed boundary point. For global minimality, route each perturbed dual
-- maximizer through the existing Chapter 4 owner theorem to identify the same resolvent point as
-- a global minimizer of the perturbed objective, then compare with the unperturbed objective and
-- pass to the limit as `δ → 0+`.
/-- Helper for Proposition 4.1.12: perturbing the gradient by `δ e_k` changes the cubic objective
only by the linear term `δ * h k`. -/
private lemma perturbedObjective_eq_objective_add_kCoordinate
    (δ : ℝ) (h : E) :
    cubicRegularizedQuadraticObjective (gδ(δ)) H M h =
      cubicRegularizedQuadraticObjective g H M h + δ * h k := by
  -- Expand the objective and isolate the contribution of the single perturbed coordinate.
  rw [cubicRegularizedQuadraticObjective_apply, cubicRegularizedQuadraticObjective_apply,
    add_dotProduct]
  simpa using (single_dotProduct δ k h)

/-- Helper for Proposition 4.1.12: the normalized scalar gap obtained by rewriting the perturbed
boundary equation in terms of the shifted denominator `s = H_min[Hdiag] + λ`. -/
private def normalizedBoundaryGap
    (s : ℝ) : ℝ :=
  (4 : ℝ) * (s - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ) -
    Finset.sum
      (Finset.univ.filter fun j : Fin n ↦
        j ∉ I*[Hdiag])
      (fun j ↦
        (g j) ^ (2 : ℕ) /
          (Hdiag j - H_min[Hdiag] + s) ^ (2 : ℕ))

/-- Helper for Proposition 4.1.12: evaluating the normalized boundary gap at `s = 0` recovers
the displayed boundary radicand. -/
@[simp] private lemma normalizedBoundaryGap_zero :
    normalizedBoundaryGap g Hdiag M 0 =
      (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
        Finset.sum
          (Finset.univ.filter fun j : Fin n ↦
            j ∉ I*[Hdiag])
          (fun j ↦
            (g j) ^ (2 : ℕ) /
              (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)) := by
  -- The shifted denominator formula specializes to the boundary radicand at `s = 0`.
  simp [normalizedBoundaryGap]

/-- Helper for Proposition 4.1.12: the perturbed certificate point has tight slack, so its
`τ`-coordinate equals the squared norm of the perturbed resolvent branch. -/
private lemma perturbedTauEqNormSqForDualMaximizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    cubicRegularizedQuadraticTauMinimizer M (lamDelta δ) =
      ‖hδ(lamDelta, δ)‖ ^ (2 : ℕ) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ_ne]
  have hGpos : 0 < G²[gδ(δ);Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq_prop412
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  let xPath : Λ → E × ℝ :=
    fun lam ↦ resolventTauCertificatePoint (gδ(δ)) Hdiag M (lam 0)
  let xStar : E × ℝ :=
    resolventTauCertificatePoint (gδ(δ)) Hdiag M (lamDelta δ)
  let hStar : E :=
    resolventCertificateVector (gδ(δ)) Hdiag (lamDelta δ)
  let ε : ℝ := (lamDelta δ + H_min[Hdiag]) / 2
  have hDplus : lamDelta δ ∈ Dplus(gδ(δ)) := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos (hopt_max hδ)
  have hlam : -H_min[Hdiag] < lamDelta δ := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hxStar :
      xStar ∈ (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).lagrangianMinimizers
        (EuclideanSpace.single 0 (lamDelta δ)) := by
    -- The perturbed resolvent certificate minimizes the Lagrangian at the maximizing multiplier.
    simpa [xStar] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM
        (μ := lamDelta δ) hlam
  have hepigraph_max :
      IsMaxOn
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFunction
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFeasibleSet
        (EuclideanSpace.single 0 (lamDelta δ)) := by
    -- Move the perturbed scalar maximizer to the one-constraint epigraph dual problem.
    exact
      resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos (hopt_max hδ)
  have hlamDelta :
      EuclideanSpace.single 0 (lamDelta δ) ∈
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFeasibleSet := by
    -- Dual feasibility is scalar dual-domain membership together with nonnegativity.
    rw [(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).mem_dualFeasibleSet_iff]
    constructor
    · rw [(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).mem_dualDomain_iff,
        ← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
      exact (mem_cubicRegularizedQuadraticDualDomain_iff (gδ(δ)) H M (lamDelta δ)).mp hDplus.1
    · intro j
      fin_cases j
      simpa using hDplus.2
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈
            Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1 →
          lam ≠ EuclideanSpace.single 0 (lamDelta δ) →
          xPath lam ∈
            (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).lagrangianMinimizers lam := by
    intro lam hmem _
    have hlam_mem : -H_min[Hdiag] < lam 0 := by
      simpa [ε] using
        resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
          (Hdiag := Hdiag) (lamStar := lamDelta δ) hlam hmem
    -- Nearby feasible multipliers stay in the same resolvent-certificate family.
    rw [dual_certificate_multiplier_eq_single (lam := lam)]
    simpa [xPath] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM
        (μ := lam 0) hlam_mem
  have hlim :
      Filter.Tendsto xPath
        (nhdsWithin (EuclideanSpace.single 0 (lamDelta δ))
          ((Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 (lamDelta δ)}))
        (𝓝 xStar) := by
    -- The perturbed certificate path varies continuously at the maximizing multiplier.
    have hcontPath :
        ContinuousAt xPath (EuclideanSpace.single 0 (lamDelta δ)) := by
      simpa [xPath] using
        resolvent_tau_certificate_continuousAt
          (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hlam
    simpa [xPath, xStar] using hcontPath.tendsto.mono_left
      (show
        nhdsWithin (EuclideanSpace.single 0 (lamDelta δ))
          ((Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 (lamDelta δ)}) ≤
          𝓝 (EuclideanSpace.single 0 (lamDelta δ)) from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).constraintVector
        xStar := by
    -- The single epigraph constraint is polynomial in `(h, τ)`.
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
        argmin[(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).feasibleSet]
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) := by
    -- Apply the global optimality theorem to the perturbed certificate path.
    simpa [xPath, xStar, ε] using
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).globalOptimality_of_dualCertificate
        xPath xStar hlamDelta hepigraph_max hε hxPath hlim hcont hxStar
  rw [mem_constrainedArgmin_iff] at hoptimal
  rcases hoptimal with ⟨hxfeas, _⟩
  have hcomp0 :
      lamDelta δ *
          ((1 / 2 : ℝ) * ‖xStar.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * xStar.2) = 0 := by
    -- Complementary slackness forces the unique epigraph constraint to be tight at the limit.
    simpa [xPath, xStar, cubicRegularizedQuadraticEpigraphProblem] using
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).complementary_slackness_at_limit
        xPath xStar hlamDelta hepigraph_max hε hxPath hlim hcont 0
  have hfeas_ineq :
      ‖hStar‖ ^ (2 : ℕ) ≤ cubicRegularizedQuadraticTauMinimizer M (lamDelta δ) := by
    -- Feasibility of the certificate point is exactly the tight-slack inequality.
    simpa [xStar, hStar, prop412ResolventTauCertificatePoint] using
      (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
        (gδ(δ)) H M
        (h := hStar) (τ := cubicRegularizedQuadraticTauMinimizer M (lamDelta δ))).mp hxfeas
  have hlam_ne_zero : lamDelta δ ≠ 0 := by
    intro hlam_zero
    have hHmin_pos : 0 < H_min[Hdiag] := by
      have h0_dom : -H_min[Hdiag] < (0 : ℝ) := by
        simpa [hlam_zero] using hlam
      linarith
    have htau_zero :
        cubicRegularizedQuadraticTauMinimizer M (lamDelta δ) = 0 := by
      rw [hlam_zero, cubicRegularizedQuadraticTauMinimizer_def]
      simp
    have hnorm_sq_zero : ‖hStar‖ ^ (2 : ℕ) = 0 := by
      rw [htau_zero] at hfeas_ineq
      have hnorm_sq_nonneg : 0 ≤ ‖hStar‖ ^ (2 : ℕ) := by positivity
      linarith
    have hnorm_zero : ‖hStar‖ = 0 := by
      exact sq_eq_zero_iff.mp <| by simpa [pow_two] using hnorm_sq_zero
    have hzero_vec : hStar = 0 := norm_eq_zero.mp hnorm_zero
    have hgk_zero : g k = 0 :=
      active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
        (g := g) (Hdiag := Hdiag) hGzero hk
    have hk_min : Hdiag k = H_min[Hdiag] :=
      (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag k).mp hk
    have hcoord_k :
        hStar k = -δ / H_min[Hdiag] := by
      -- Route correction: evaluate the perturbed resolvent on the distinguished coordinate.
      change -((gδ(δ)) k) / (Hdiag k + lamDelta δ) = -δ / H_min[Hdiag]
      rw [show lamDelta δ = 0 by exact hlam_zero]
      change -(g k + if k = k then δ else 0) / Hdiag k = -δ / H_min[Hdiag]
      simp [hgk_zero, hk_min]
    have hk_zero : hStar k = 0 := by
      simpa [hzero_vec]
    have hdelta_zero : δ = 0 := by
      rw [hcoord_k] at hk_zero
      field_simp [hHmin_pos.ne'] at hk_zero
      linarith
    exact hδ_ne hdelta_zero
  have hlam_pos : 0 < lamDelta δ := by
    have hnonneg : 0 ≤ lamDelta δ := hDplus.2
    exact lt_of_le_of_ne hnonneg (Ne.symm hlam_ne_zero)
  have htight :
      ‖xStar.1‖ ^ (2 : ℕ) = xStar.2 := by
    -- Positive multiplier plus complementary slackness forces equality in the epigraph slack.
    nlinarith [hcomp0, hlam_pos]
  have hrepr :
      hδ(lamDelta, δ) = hStar := by
    ext i
    have hcoord :
        hδ(lamDelta, δ) i =
          -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
      simpa using
        (cubicRegularizedDiagonalResolvent_apply
          (gδ(δ)) Hdiag (lamDelta δ) hlam i)
    simpa [hStar, prop412ResolventCertificateVector] using hcoord
  simpa [xStar, prop412ResolventTauCertificatePoint, hrepr] using htight.symm

/-- Helper for Proposition 4.1.12: rewriting the perturbed boundary equation in terms of
`s = H_min[Hdiag] + λ_δ*` isolates the scalar factor `normalizedBoundaryGap g Hdiag M s`. -/
private lemma perturbedBoundaryEquation_eq_shiftSq_mulGap
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    δ ^ (2 : ℕ) =
      (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) *
        normalizedBoundaryGap g Hdiag M (H_min[Hdiag] + lamDelta δ) := by
  let s : ℝ := H_min[Hdiag] + lamDelta δ
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ_ne]
  have hGpos : 0 < G²[gδ(δ);Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq_prop412
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  have hDplus : lamDelta δ ∈ Dplus(gδ(δ)) := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos (hopt_max hδ)
  have hs_pos : 0 < s := by
    simpa [s] using
      perturbed_dualMaximizer_denominator_pos
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        lamDelta hM hk hGzero hopt_max hδ
  have hboundary :
      δ ^ (2 : ℕ) / s ^ (2 : ℕ) +
          Finset.sum
            (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
            (fun i ↦
              (g i) ^ (2 : ℕ) /
                (Hdiag i - H_min[Hdiag] + s) ^ (2 : ℕ)) =
        (4 : ℝ) * (s - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ) := by
    -- Route correction: first identify the perturbed slack minimizer with the resolvent norm.
    calc
      δ ^ (2 : ℕ) / s ^ (2 : ℕ) +
          Finset.sum
            (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
            (fun i ↦
              (g i) ^ (2 : ℕ) /
                (Hdiag i - H_min[Hdiag] + s) ^ (2 : ℕ)) =
          ‖hδ(lamDelta, δ)‖ ^ (2 : ℕ) := by
            simpa [s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (perturbedResolventNormSq_eq_boundaryLhs
                (g := g) (Hdiag := Hdiag) (M := M) (k := k)
                lamDelta hM hk hGzero hopt_max hδ).symm
      _ = cubicRegularizedQuadraticTauMinimizer M (lamDelta δ) := by
            symm
            exact perturbedTauEqNormSqForDualMaximizer
              (g := g) (Hdiag := Hdiag) (M := M) (k := k)
              lamDelta hM hk hGzero hopt_max hδ
      _ = (4 : ℝ) * (s - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ) := by
            rw [cubicRegularizedQuadraticTauMinimizer_def, abs_of_nonneg hDplus.2]
            simp [s]
            ring
  have hratio :
      δ ^ (2 : ℕ) / s ^ (2 : ℕ) = normalizedBoundaryGap g Hdiag M s := by
    -- After rewriting the denominator by `s = H_min + λ_δ*`, the remaining term is exactly the
    -- normalized boundary gap.
    dsimp [normalizedBoundaryGap, s] at *
    linarith
  have hs_sq_ne : s ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 hs_pos.ne'
  have hmain :
      δ ^ (2 : ℕ) =
        normalizedBoundaryGap g Hdiag M s * s ^ (2 : ℕ) :=
    (div_eq_iff hs_sq_ne).mp hratio
  simpa [s, mul_comm] using hmain

/-- Helper for Proposition 4.1.12: every perturbed dual maximizer yields the canonical resolvent
point as a global minimizer of the corresponding perturbed objective. -/
private lemma perturbedResolventIsMinOnOfDualMaximizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    IsMinOn
      (cubicRegularizedQuadraticObjective (gδ(δ)) H M)
      Set.univ
      (hδ(lamDelta, δ)) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ_ne]
  have hGpos : 0 < G²[gδ(δ);Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq_prop412
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  let xPath : Λ → E × ℝ :=
    fun lam ↦ resolventTauCertificatePoint (gδ(δ)) Hdiag M (lam 0)
  let xStar : E × ℝ :=
    resolventTauCertificatePoint (gδ(δ)) Hdiag M (lamDelta δ)
  let hStar : E :=
    resolventCertificateVector (gδ(δ)) Hdiag (lamDelta δ)
  let ε : ℝ := (lamDelta δ + H_min[Hdiag]) / 2
  have hDplus : lamDelta δ ∈ Dplus(gδ(δ)) := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos (hopt_max hδ)
  have hlam : -H_min[Hdiag] < lamDelta δ := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hxStar :
      xStar ∈ (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).lagrangianMinimizers
        (EuclideanSpace.single 0 (lamDelta δ)) := by
    -- The perturbed resolvent certificate minimizes the Lagrangian at the maximizing multiplier.
    simpa [xStar] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM
        (μ := lamDelta δ) hlam
  have hepigraph_max :
      IsMaxOn
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFunction
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFeasibleSet
        (EuclideanSpace.single 0 (lamDelta δ)) := by
    exact
      resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM hGpos (hopt_max hδ)
  have hlamDelta :
      EuclideanSpace.single 0 (lamDelta δ) ∈
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).dualFeasibleSet := by
    rw [(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).mem_dualFeasibleSet_iff]
    constructor
    · rw [(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).mem_dualDomain_iff,
        ← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
      exact (mem_cubicRegularizedQuadraticDualDomain_iff (gδ(δ)) H M (lamDelta δ)).mp hDplus.1
    · intro j
      fin_cases j
      simpa using hDplus.2
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈
            Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1 →
          lam ≠ EuclideanSpace.single 0 (lamDelta δ) →
          xPath lam ∈
            (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).lagrangianMinimizers lam := by
    intro lam hmem _
    have hlam_mem : -H_min[Hdiag] < lam 0 := by
      simpa [ε] using
        resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
          (Hdiag := Hdiag) (lamStar := lamDelta δ) hlam hmem
    rw [dual_certificate_multiplier_eq_single (lam := lam)]
    simpa [xPath] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hM
        (μ := lam 0) hlam_mem
  have hlim :
      Filter.Tendsto xPath
        (nhdsWithin (EuclideanSpace.single 0 (lamDelta δ))
          ((Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 (lamDelta δ)}))
        (𝓝 xStar) := by
    have hcontPath :
        ContinuousAt xPath (EuclideanSpace.single 0 (lamDelta δ)) := by
      simpa [xPath] using
        resolvent_tau_certificate_continuousAt
          (g := gδ(δ)) (Hdiag := Hdiag) (M := M) hlam
    simpa [xPath, xStar] using hcontPath.tendsto.mono_left
      (show
        nhdsWithin (EuclideanSpace.single 0 (lamDelta δ))
          ((Metric.closedBall (EuclideanSpace.single 0 (lamDelta δ)) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 (lamDelta δ)}) ≤
          𝓝 (EuclideanSpace.single 0 (lamDelta δ)) from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).constraintVector
        xStar := by
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
        argmin[(cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).feasibleSet]
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) := by
    simpa [xPath, xStar, ε] using
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).globalOptimality_of_dualCertificate
        xPath xStar hlamDelta hepigraph_max hε hxPath hlim hcont hxStar
  rw [mem_constrainedArgmin_iff] at hoptimal
  rcases hoptimal with ⟨hxfeas, hxmin⟩
  have hrepr :
      hδ(lamDelta, δ) = hStar := by
    ext i
    have hcoord :
        hδ(lamDelta, δ) i =
          -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
      simpa using
        (cubicRegularizedDiagonalResolvent_apply
          (gδ(δ)) Hdiag (lamDelta δ) hlam i)
    simpa [hStar, prop412ResolventCertificateVector] using hcoord
  have hxStar_eq_objective :
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar =
        cubicRegularizedQuadraticObjective (gδ(δ)) H M hStar := by
    have htight_feas_star :
        (hStar, ‖hStar‖ ^ (2 : ℕ)) ∈
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).feasibleSet := by
      exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber (gδ(δ)) H M hStar
    have hopt_le_tight :
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar ≤
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M)
            (hStar, ‖hStar‖ ^ (2 : ℕ)) :=
      (isMinOn_iff.mp hxmin) _ htight_feas_star
    have htight_le_opt :
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M)
            (hStar, ‖hStar‖ ^ (2 : ℕ)) ≤
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar := by
      simpa [xStar, hStar] using
        cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible
          (gδ(δ)) H M (le_of_lt hM) hxfeas
    calc
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar =
          (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M)
            (hStar, ‖hStar‖ ^ (2 : ℕ)) := by
        exact le_antisymm hopt_le_tight htight_le_opt
      _ = cubicRegularizedQuadraticObjective (gδ(δ)) H M hStar :=
        cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq (gδ(δ)) H M hStar
  rw [isMinOn_univ_iff]
  intro h
  have hfeas_h :
      (h, ‖h‖ ^ (2 : ℕ)) ∈
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M).feasibleSet := by
    exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber (gδ(δ)) H M h
  have hopt_le_h :
      (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar ≤
        (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) (h, ‖h‖ ^ (2 : ℕ)) :=
    (isMinOn_iff.mp hxmin) _ hfeas_h
  calc
    cubicRegularizedQuadraticObjective (gδ(δ)) H M (hδ(lamDelta, δ)) =
        cubicRegularizedQuadraticObjective (gδ(δ)) H M hStar := by
          have hreprE : (WithLp.toLp 2 (hδ(lamDelta, δ)) : E) = hStar := by
            simpa using hrepr
          simpa using congrArg (cubicRegularizedQuadraticObjective (gδ(δ)) H M) hreprE
    _ = (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) xStar := by
          exact hxStar_eq_objective.symm
    _ ≤ (cubicRegularizedQuadraticEpigraphProblem (gδ(δ)) H M) (h, ‖h‖ ^ (2 : ℕ)) :=
          hopt_le_h
    _ = cubicRegularizedQuadraticObjective (gδ(δ)) H M h :=
          cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq (gδ(δ)) H M h

/-- Helper for Proposition 4.1.12: the normalized boundary gap dominates the pure quadratic term
`4 s² / M²` on the nonnegative half-line. -/
private lemma normalizedBoundaryGap_lower_bound_quadratic
    (hM : 0 < M)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible : 0 ≤ normalizedBoundaryGap g Hdiag M 0)
    {s : ℝ} (hs : 0 ≤ s) :
    (4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ) ≤
      normalizedBoundaryGap g Hdiag M s := by
  let inactive : Finset (Fin n) :=
    Finset.univ.filter fun j : Fin n ↦ j ∉ I*[Hdiag]
  let sumAt : ℝ → ℝ :=
    fun t : ℝ ↦
      Finset.sum inactive
        (fun j ↦
          (g j) ^ (2 : ℕ) /
            (Hdiag j - H_min[Hdiag] + t) ^ (2 : ℕ))
  have hsum_mono : sumAt s ≤ sumAt 0 := by
    -- Each inactive denominator increases with `s`, so each reciprocal-square term decreases.
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_inactive : i ∉ I*[Hdiag] := by
      simpa [inactive, Finset.mem_filter] using hi
    have hgap_pos :
        0 < Hdiag i - H_min[Hdiag] :=
      inactive_diagonal_gap_pos (Hdiag := Hdiag) hi_inactive
    have hpow_le :
        (Hdiag i - H_min[Hdiag]) ^ (2 : ℕ) ≤
          (Hdiag i - H_min[Hdiag] + s) ^ (2 : ℕ) := by
      nlinarith [hgap_pos, hs]
    have hpow_pos :
        0 < (Hdiag i - H_min[Hdiag]) ^ (2 : ℕ) :=
      pow_pos hgap_pos 2
    have hrecip :
        1 / (Hdiag i - H_min[Hdiag] + s) ^ (2 : ℕ) ≤
          1 / (Hdiag i - H_min[Hdiag]) ^ (2 : ℕ) :=
      one_div_le_one_div_of_le hpow_pos hpow_le
    have hnum_nonneg : 0 ≤ (g i) ^ (2 : ℕ) := by
      positivity
    simpa [sumAt, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hrecip hnum_nonneg
  have hsum0_le :
      sumAt 0 ≤ (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) := by
    -- Boundary feasibility is exactly the nonnegativity of the boundary gap.
    have hgap0 :
        0 ≤
          (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
            sumAt 0 := by
      simpa [normalizedBoundaryGap_zero, sumAt, inactive] using hboundary_feasible
    exact sub_nonneg.mp hgap0
  let c : ℝ := (4 : ℝ) / M ^ (2 : ℕ)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpoly :
      c * s ^ (2 : ℕ) ≤
        c * ((s - H_min[Hdiag]) ^ (2 : ℕ) - H_min[Hdiag] ^ (2 : ℕ)) := by
    -- The sign assumption `H_min[Hdiag] ≤ 0` gives the quadratic improvement away from zero.
    have hpoly_base :
        s ^ (2 : ℕ) ≤
          (s - H_min[Hdiag]) ^ (2 : ℕ) - H_min[Hdiag] ^ (2 : ℕ) := by
      nlinarith [hHmin_nonpos, hs]
    exact mul_le_mul_of_nonneg_left hpoly_base hc_nonneg
  have hsum_le_first :
      sumAt s ≤ (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) :=
    le_trans hsum_mono hsum0_le
  have hquad :
      (4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ) ≤
        (4 : ℝ) * (s - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ) -
          (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) := by
    simpa [c, div_eq_mul_inv, sub_eq_add_neg, left_distrib, right_distrib, mul_assoc,
      mul_left_comm, mul_comm] using hpoly
  -- Combine the sum monotonicity with the quadratic lower bound on the leading term.
  have hmain :
      (4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ) ≤
        (4 : ℝ) * (s - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ) -
          sumAt s := by
    linarith
  simpa [normalizedBoundaryGap, sumAt, inactive] using hmain

/-- Helper for Proposition 4.1.12: the shifted denominator `H_min[Hdiag] + λ_δ*` satisfies the
uniform bound `sδ² ≤ (M / 2) δ`, hence tends to zero with `δ`. -/
private lemma dualShift_sq_le_linear_of_boundaryEquation
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible : 0 ≤ normalizedBoundaryGap g Hdiag M 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) ≤ (M / 2 : ℝ) * δ := by
  let s : ℝ := H_min[Hdiag] + lamDelta δ
  have hs_nonneg : 0 ≤ s := by
    exact le_of_lt <| perturbed_dualMaximizer_denominator_pos
      (g := g) (Hdiag := Hdiag) (M := M) (k := k)
      lamDelta hM hk hGzero hopt_max hδ
  have hgap_lb :
      (4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ) ≤
        normalizedBoundaryGap g Hdiag M s :=
    normalizedBoundaryGap_lower_bound_quadratic
      (g := g) (Hdiag := Hdiag) (M := M) hM hHmin_nonpos hboundary_feasible hs_nonneg
  have hEq :
      δ ^ (2 : ℕ) = s ^ (2 : ℕ) * normalizedBoundaryGap g Hdiag M s := by
    simpa [s] using
      perturbedBoundaryEquation_eq_shiftSq_mulGap
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        lamDelta hM hk hGzero hopt_max hδ
  have hquartic :
      s ^ (2 : ℕ) * ((4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ)) ≤
        δ ^ (2 : ℕ) := by
    rw [hEq]
    exact mul_le_mul_of_nonneg_left hgap_lb (by positivity)
  -- The quartic estimate collapses to the linear bound `s² ≤ (M / 2) δ`.
  have hquartic' := hquartic
  have hM_sq_ne : M ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 hM.ne'
  field_simp [hM_sq_ne] at hquartic'
  dsimp [s] at hquartic' ⊢
  have hs_sq_nonneg : 0 ≤ (H_min[Hdiag] + lamDelta δ) ^ (2 : ℕ) := by
    positivity
  have hright_nonneg : 0 ≤ (M / 2 : ℝ) * δ := by
    positivity
  nlinarith [hquartic', hs_sq_nonneg, hright_nonneg]

/-- Helper for Proposition 4.1.12: the shifted denominator `H_min[Hdiag] + λ_δ*` tends to the
boundary value `0` as `δ → 0+`. -/
private lemma dualShift_tendsto_zero_of_boundaryEquation
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible : 0 ≤ normalizedBoundaryGap g Hdiag M 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto
      (fun δ : ℝ ↦ H_min[Hdiag] + lamDelta δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
  let s : ℝ → ℝ := fun δ : ℝ ↦ H_min[Hdiag] + lamDelta δ
  have hs_sq_nonneg :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ s δ ^ (2 : ℕ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    positivity
  have hs_sq_le :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), s δ ^ (2 : ℕ) ≤ (M / 2 : ℝ) * δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact dualShift_sq_le_linear_of_boundaryEquation
      (g := g) (Hdiag := Hdiag) (M := M) (k := k)
      lamDelta hM hk hGzero hHmin_nonpos hboundary_feasible hopt_max hδ
  have hright :
      Filter.Tendsto (fun δ : ℝ ↦ (M / 2 : ℝ) * δ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- The linear comparison term vanishes with `δ`.
    have hcont :
        ContinuousAt (fun δ : ℝ ↦ (M / 2 : ℝ) * δ) 0 :=
      continuousAt_const.mul continuousAt_id
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hs_sq_tendsto :
      Filter.Tendsto (fun δ : ℝ ↦ s δ ^ (2 : ℕ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' hs_sq_nonneg hs_sq_le hright
  have hs_as_sqrt :
      (fun δ : ℝ ↦ s δ) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun δ : ℝ ↦ Real.sqrt (s δ ^ (2 : ℕ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hs_nonneg : 0 ≤ s δ := by
      exact le_of_lt <| perturbed_dualMaximizer_denominator_pos
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        lamDelta hM hk hGzero hopt_max hδ
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
  have hsqrt_tendsto :
      Filter.Tendsto (fun δ : ℝ ↦ Real.sqrt (s δ ^ (2 : ℕ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- Route correction: pass through `sδ² → 0` and the continuity of `Real.sqrt` at zero.
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hs_sq_tendsto)
  exact Filter.Tendsto.congr' hs_as_sqrt.symm hsqrt_tendsto

/-- Helper for Proposition 4.1.12: every active coordinate other than the distinguished index
`k` vanishes identically along the perturbed resolvent branch. -/
private lemma perturbedActiveOtherCoordinate_eq_zero
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ)
    {i : Fin n} (hi : i ∈ I*[Hdiag]) (hik : i ≠ k) :
    hδ(lamDelta, δ) i = 0 := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 i
  letI : NeZero n := ⟨hn⟩
  have hlam : -H_min[Hdiag] < lamDelta δ :=
    perturbed_dualMaximizer_gt_boundary
      (g := g) (Hdiag := Hdiag) (M := M) (k := k)
      lamDelta hM hk hGzero hopt_max hδ
  have hgi_zero : g i = 0 :=
    active_coordinates_vanish_of_zeroMinimalGradientSquare_prop412
      (g := g) (Hdiag := Hdiag) hGzero hi
  have hcoord :
      hδ(lamDelta, δ) i =
        -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
    simpa using
      (cubicRegularizedDiagonalResolvent_apply
        (gδ(δ)) Hdiag (lamDelta δ) hlam i)
  -- The perturbation leaves every active coordinate other than `k` equal to zero.
  rw [hcoord]
  change -(g i + if i = k then δ else 0) / (Hdiag i + lamDelta δ) = 0
  simp [hgi_zero, hik]

/-- Helper for Proposition 4.1.12: the distinguished perturbed resolvent coordinate is the
negative square root of the normalized boundary gap. -/
private lemma distinguishedCoordinate_eq_negSqrtBoundaryGap
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible : 0 ≤ normalizedBoundaryGap g Hdiag M 0)
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ))
    {δ : ℝ} (hδ : 0 < δ) :
    hδ(lamDelta, δ) k =
      -Real.sqrt
        (normalizedBoundaryGap g Hdiag M
          (H_min[Hdiag] + lamDelta δ)) := by
  let s : ℝ := H_min[Hdiag] + lamDelta δ
  have hs_pos : 0 < s := by
    simpa [s] using
      perturbed_dualMaximizer_denominator_pos
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        lamDelta hM hk hGzero hopt_max hδ
  have hcoord_div :
      hδ(lamDelta, δ) k = -δ / s := by
    simpa [s] using
      distinguished_coordinate_eq_neg_div
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        lamDelta hM hk hGzero hopt_max hδ
  have hgap_nonneg :
      0 ≤ normalizedBoundaryGap g Hdiag M s := by
    have hgap_lb :
        (4 : ℝ) * s ^ (2 : ℕ) / M ^ (2 : ℕ) ≤
          normalizedBoundaryGap g Hdiag M s :=
      normalizedBoundaryGap_lower_bound_quadratic
        (g := g) (Hdiag := Hdiag) (M := M)
        hM hHmin_nonpos hboundary_feasible (le_of_lt hs_pos)
    exact le_trans (by positivity) hgap_lb
  have hsq :
      (δ / s) ^ (2 : ℕ) = normalizedBoundaryGap g Hdiag M s := by
    have hEq :
        δ ^ (2 : ℕ) = s ^ (2 : ℕ) * normalizedBoundaryGap g Hdiag M s := by
      simpa [s] using
        perturbedBoundaryEquation_eq_shiftSq_mulGap
          (g := g) (Hdiag := Hdiag) (M := M) (k := k)
          lamDelta hM hk hGzero hopt_max hδ
    have hs_sq_ne : s ^ (2 : ℕ) ≠ 0 :=
      pow_ne_zero 2 hs_pos.ne'
    have hratio :
        δ ^ (2 : ℕ) / s ^ (2 : ℕ) =
          normalizedBoundaryGap g Hdiag M s := by
      exact (div_eq_iff hs_sq_ne).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hEq
    have hpow_div :
        (δ / s) ^ (2 : ℕ) = δ ^ (2 : ℕ) / s ^ (2 : ℕ) := by
      field_simp [pow_two, hs_pos.ne']
    exact hpow_div.trans hratio
  have hdiv_nonneg : 0 ≤ δ / s := by
    exact div_nonneg (le_of_lt hδ) (le_of_lt hs_pos)
  have hdiv_eq_sqrt :
      δ / s = Real.sqrt (normalizedBoundaryGap g Hdiag M s) := by
    -- Nonnegativity selects the positive square root of the normalized gap.
    have hsqrt_eq :
        Real.sqrt ((δ / s) ^ (2 : ℕ)) =
          Real.sqrt (normalizedBoundaryGap g Hdiag M s) := by
      rw [hsq]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdiv_nonneg] at hsqrt_eq
    exact hsqrt_eq
  have hneg_div : -δ / s = -(δ / s) := by
    ring
  rw [hcoord_div, hneg_div, hdiv_eq_sqrt]

/-- Helper for Proposition 4.1.12: under the repaired boundary-feasibility hypothesis
given by the displayed square-root radicand, `cubicRegularizedDiagonalBoundaryMinimizer` is
indeed defined using a real square root. -/
theorem cubicRegularizedDiagonalBoundaryMinimizer_radicand_nonneg
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible :
      0 ≤
        (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    0 ≤
      (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
        Finset.sum
          (Finset.univ.filter fun j : Fin n ↦
            j ∉ I*[Hdiag])
          (fun j ↦
            (g j) ^ (2 : ℕ) /
              (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)) := by
  -- The repaired proposition carries the radicand nonnegativity as a hypothesis already.
  exact hboundary_feasible

/-- Proposition 4.1.12.

In this formalization, the quoted textbook statement is not source-faithful without an extra
boundary-feasibility hypothesis, so the main labeled result keeps only the corrected boundary
branch. Under the additional sign and radicand hypotheses selecting that branch, the canonical
perturbed resolvent branch `-(H + lamDelta δ • I)⁻¹ (g + δ e_k)` converges to the displayed
boundary point, which is then a global minimizer of the original objective. -/
theorem cubicRegularizedDiagonalPerturbedResolvent_tendsto_boundary_and_isMinimizer_of_boundaryFeasible
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible :
      0 ≤
        (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) ∧
      IsMinOn
        (cubicRegularizedQuadraticObjective g H M)
        Set.univ
        (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  let s : ℝ → ℝ := fun δ : ℝ ↦ H_min[Hdiag] + lamDelta δ
  let hStar : E := cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k
  have hboundary_gap0 : 0 ≤ normalizedBoundaryGap g Hdiag M 0 := by
    simpa [normalizedBoundaryGap_zero] using hboundary_feasible
  have hs_tendsto :
      Filter.Tendsto s (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact dualShift_tendsto_zero_of_boundaryEquation
      (g := g) (Hdiag := Hdiag) (M := M) (k := k)
      lamDelta hM hk hGzero hHmin_nonpos hboundary_gap0 hopt_max
  have hgap_tendsto :
      Filter.Tendsto
        (fun δ : ℝ ↦ normalizedBoundaryGap g Hdiag M (s δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (normalizedBoundaryGap g Hdiag M 0)) := by
    let inactive : Finset (Fin n) :=
      Finset.univ.filter fun j : Fin n ↦ j ∉ I*[Hdiag]
    have hquad_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ (4 : ℝ) * (s δ - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ))
          (𝓝[>] (0 : ℝ))
          (𝓝 ((4 : ℝ) * (0 - H_min[Hdiag]) ^ (2 : ℕ) / M ^ (2 : ℕ))) := by
      -- The shifted variable `sδ = H_min + λδ` tends to `0`, so `λδ` tends to `-H_min`.
      have hlam_tendsto :
          Filter.Tendsto (fun δ : ℝ ↦ lamDelta δ)
            (𝓝[>] (0 : ℝ))
            (𝓝 (-H_min[Hdiag])) := by
        have hcont :
            ContinuousAt (fun x : ℝ ↦ x - H_min[Hdiag]) 0 :=
          continuousAt_id.sub continuousAt_const
        have hcomp := hcont.tendsto.comp hs_tendsto
        convert hcomp using 1
        · ext δ
          dsimp [s]
          ring
        · ring
      have hcont :
          ContinuousAt
            (fun x : ℝ ↦ (4 : ℝ) * x ^ (2 : ℕ) / M ^ (2 : ℕ))
            (-H_min[Hdiag]) := by
        have hbase :
            ContinuousAt
              (fun x : ℝ ↦ x ^ (2 : ℕ) * ((M ^ (2 : ℕ))⁻¹ * 4))
              (-H_min[Hdiag]) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (continuousAt_id.pow 2).const_mul (((M ^ (2 : ℕ))⁻¹) * 4)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
      simpa [s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hcont.tendsto.comp hlam_tendsto
    have hsum_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦
            Finset.sum inactive
              (fun j ↦
                (g j) ^ (2 : ℕ) /
                  (Hdiag j - H_min[Hdiag] + s δ) ^ (2 : ℕ)))
          (𝓝[>] (0 : ℝ))
          (𝓝
            (Finset.sum inactive
              (fun j ↦
                (g j) ^ (2 : ℕ) /
                  (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))) := by
      -- Every inactive reciprocal-square term is continuous at `s = 0`.
      refine tendsto_finset_sum inactive ?_
      intro j hj
      have hj_inactive : j ∉ I*[Hdiag] := by
        simpa [inactive, Finset.mem_filter] using hj
      have hgap_pos :
          0 < Hdiag j - H_min[Hdiag] :=
        inactive_diagonal_gap_pos (Hdiag := Hdiag) hj_inactive
      have hcont :
          ContinuousAt
            (fun x : ℝ ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag] + x) ^ (2 : ℕ))
            0 := by
        have hdenom_ne :
            (Hdiag j - H_min[Hdiag] + (0 : ℝ)) ^ (2 : ℕ) ≠ 0 := by
          simpa using pow_ne_zero 2 hgap_pos.ne'
        exact
          (continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2) hdenom_ne)
      simpa [s] using hcont.tendsto.comp hs_tendsto
    -- Assemble the quadratic and inactive-sum limits into the normalized gap limit.
    simpa [normalizedBoundaryGap, normalizedBoundaryGap_zero, inactive] using
      hquad_tendsto.sub hsum_tendsto
  have hcoord_tendsto :
      ∀ i : Fin n,
        Filter.Tendsto
          (fun δ : ℝ ↦ hδ(lamDelta, δ) i)
          (𝓝[>] (0 : ℝ))
          (𝓝 (hStar i)) := by
    intro i
    by_cases hik : i = k
    · subst i
      have hkcoord_eq :
          (fun δ : ℝ ↦ hδ(lamDelta, δ) k) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun δ : ℝ ↦ -Real.sqrt (normalizedBoundaryGap g Hdiag M (s δ))) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact distinguishedCoordinate_eq_negSqrtBoundaryGap
          (g := g) (Hdiag := Hdiag) (M := M) (k := k)
          lamDelta hM hk hGzero hHmin_nonpos hboundary_gap0 hopt_max hδ
      have hsqrt_tendsto :
          Filter.Tendsto
            (fun δ : ℝ ↦ -Real.sqrt (normalizedBoundaryGap g Hdiag M (s δ)))
            (𝓝[>] (0 : ℝ))
            (𝓝 (-Real.sqrt (normalizedBoundaryGap g Hdiag M 0))) := by
        exact (Real.continuous_sqrt.continuousAt.tendsto.comp hgap_tendsto).neg
      have hkstar :
          hStar k = -Real.sqrt (normalizedBoundaryGap g Hdiag M 0) := by
        dsimp [hStar]
        simpa [normalizedBoundaryGap_zero] using
          (cubicRegularizedDiagonalBoundaryMinimizer_apply
            (g := g) (Hdiag := Hdiag) (M := M) (k := k) (i := k))
      simpa [hkstar] using Filter.Tendsto.congr' hkcoord_eq hsqrt_tendsto
    · by_cases hi_active : i ∈ I*[Hdiag]
      · have hzero_eq :
            (fun δ : ℝ ↦ hδ(lamDelta, δ) i) =ᶠ[𝓝[>] (0 : ℝ)] fun _ : ℝ ↦ 0 := by
          filter_upwards [self_mem_nhdsWithin] with δ hδ
          exact perturbedActiveOtherCoordinate_eq_zero
            (g := g) (Hdiag := Hdiag) (M := M) (k := k)
            lamDelta hM hk hGzero hopt_max hδ hi_active hik
        have histar :
            hStar i = 0 := by
          dsimp [hStar]
          simpa [hik, hi_active] using
            (cubicRegularizedDiagonalBoundaryMinimizer_apply
              (g := g) (Hdiag := Hdiag) (M := M) (k := k) (i := i))
        simpa [histar] using Filter.Tendsto.congr' hzero_eq tendsto_const_nhds
      · have hi_inactive : i ∉ I*[Hdiag] := hi_active
        have hcoord_eq :
            (fun δ : ℝ ↦ hδ(lamDelta, δ) i) =ᶠ[𝓝[>] (0 : ℝ)]
              (fun δ : ℝ ↦ -g i / (Hdiag i - H_min[Hdiag] + s δ)) := by
          filter_upwards [self_mem_nhdsWithin] with δ hδ
          have hlam : -H_min[Hdiag] < lamDelta δ := by
            exact
              perturbed_dualMaximizer_gt_boundary
                (g := g) (Hdiag := Hdiag) (M := M) (k := k)
                lamDelta hM hk hGzero hopt_max hδ
          have hcoord :
              hδ(lamDelta, δ) i =
                -((gδ(δ)) i) / (Hdiag i + lamDelta δ) := by
            simpa using
              (cubicRegularizedDiagonalResolvent_apply
                (gδ(δ)) Hdiag (lamDelta δ) hlam i)
          rw [hcoord]
          change -(g i + if i = k then δ else 0) / (Hdiag i + lamDelta δ) =
            -g i / (Hdiag i - H_min[Hdiag] + s δ)
          simp [hik, s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        have hinactive_tendsto :
            Filter.Tendsto
              (fun δ : ℝ ↦ -g i / (Hdiag i - H_min[Hdiag] + s δ))
              (𝓝[>] (0 : ℝ))
              (𝓝 (-g i / (Hdiag i - H_min[Hdiag]))) := by
          have hgap_pos :
              0 < Hdiag i - H_min[Hdiag] :=
            inactive_diagonal_gap_pos (Hdiag := Hdiag) hi_inactive
          have hcont :
              ContinuousAt
                (fun x : ℝ ↦ -g i / (Hdiag i - H_min[Hdiag] + x))
                0 := by
            have hdenom_ne : Hdiag i - H_min[Hdiag] + (0 : ℝ) ≠ 0 := by
              linarith
            exact
              (continuousAt_const.div (continuousAt_const.add continuousAt_id) hdenom_ne)
          simpa [s] using hcont.tendsto.comp hs_tendsto
        have histar :
            hStar i = -g i / (Hdiag i - H_min[Hdiag]) := by
          dsimp [hStar]
          simpa [hik, hi_inactive] using
            (cubicRegularizedDiagonalBoundaryMinimizer_apply
              (g := g) (Hdiag := Hdiag) (M := M) (k := k) (i := i))
        simpa [histar] using Filter.Tendsto.congr' hcoord_eq hinactive_tendsto
  have hbranch_tendsto_raw :
      Filter.Tendsto
        (fun δ : ℝ ↦ hδ(lamDelta, δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 hStar) := by
    rw [tendsto_pi_nhds]
    intro i
    simpa using hcoord_tendsto i
  have hbranch_tendsto :
      Filter.Tendsto
        (fun δ : ℝ ↦ WithLp.toLp 2 (hδ(lamDelta, δ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 hStar) := by
    simpa using
      ((PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.tendsto.comp hbranch_tendsto_raw)
  have hδ_tendsto_zero :
      Filter.Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hobjective_cont :
      Continuous (cubicRegularizedQuadraticObjective g H M) := by
    -- The objective is built from continuous linear algebra and the cubic norm term.
    have hlinear : Continuous fun h : E ↦ dotProduct g h :=
      continuous_const.dotProduct continuous_id
    have hquadratic : Continuous fun h : E ↦ (1 / 2 : ℝ) * dotProduct (H.mulVec h) h := by
      have hmulVec : Continuous fun h : E ↦ H.mulVec h :=
        continuous_const.mulVec continuous_id
      exact continuous_const.mul (hmulVec.dotProduct continuous_id)
    have hcubic : Continuous fun h : E ↦ (M / 6 : ℝ) * ‖h‖ ^ (3 : ℕ) := by
      exact continuous_const.mul (continuous_norm.pow 3)
    simpa [cubicRegularizedQuadraticObjective_apply] using
      hlinear.add (hquadratic.add hcubic)
  have hmin :
      IsMinOn
        (cubicRegularizedQuadraticObjective g H M)
        Set.univ
        hStar := by
    rw [isMinOn_univ_iff]
    intro h
    have hineq_eventually :
        ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
          cubicRegularizedQuadraticObjective g H M (hδ(lamDelta, δ)) +
              δ * hδ(lamDelta, δ) k ≤
            cubicRegularizedQuadraticObjective g H M h + δ * h k := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hminδ :
          IsMinOn
            (cubicRegularizedQuadraticObjective (gδ(δ)) H M)
            Set.univ
            (hδ(lamDelta, δ)) :=
        perturbedResolventIsMinOnOfDualMaximizer
          (g := g) (Hdiag := Hdiag) (M := M) (k := k)
          lamDelta hM hk hGzero hopt_max hδ
      have hle :
          cubicRegularizedQuadraticObjective (gδ(δ)) H M (hδ(lamDelta, δ)) ≤
            cubicRegularizedQuadraticObjective (gδ(δ)) H M h :=
        (isMinOn_univ_iff.mp hminδ) h
      simpa [perturbedObjective_eq_objective_add_kCoordinate] using hle
    have hobj_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ cubicRegularizedQuadraticObjective g H M (hδ(lamDelta, δ)))
          (𝓝[>] (0 : ℝ))
          (𝓝 (cubicRegularizedQuadraticObjective g H M hStar)) := by
      exact hobjective_cont.continuousAt.tendsto.comp hbranch_tendsto
    have hkcoord_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ hδ(lamDelta, δ) k)
          (𝓝[>] (0 : ℝ))
          (𝓝 (hStar k)) :=
      hcoord_tendsto k
    have hleft_linear_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ δ * hδ(lamDelta, δ) k)
          (𝓝[>] (0 : ℝ))
          (𝓝 0) := by
      simpa using hδ_tendsto_zero.mul hkcoord_tendsto
    have hright_linear_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ δ * h k)
          (𝓝[>] (0 : ℝ))
          (𝓝 0) := by
      simpa [mul_comm] using hδ_tendsto_zero.const_mul (h k)
    have hleft_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦
            cubicRegularizedQuadraticObjective g H M (hδ(lamDelta, δ)) +
              δ * hδ(lamDelta, δ) k)
          (𝓝[>] (0 : ℝ))
          (𝓝 (cubicRegularizedQuadraticObjective g H M hStar)) := by
      simpa using hobj_tendsto.add hleft_linear_tendsto
    have hright_tendsto :
        Filter.Tendsto
          (fun δ : ℝ ↦ cubicRegularizedQuadraticObjective g H M h + δ * h k)
          (𝓝[>] (0 : ℝ))
          (𝓝 (cubicRegularizedQuadraticObjective g H M h)) := by
      simpa using tendsto_const_nhds.add hright_linear_tendsto
    exact le_of_tendsto_of_tendsto' hleft_tendsto hright_tendsto hineq_eventually
  exact ⟨by simpa [hStar] using hbranch_tendsto_raw, by simpa [hStar] using hmin⟩

/-- Auxiliary bridge theorem for Proposition 4.1.12: if a chosen perturbed minimizer family
`hStarDelta` is represented by the canonical resolvent branch on `δ > 0`, then the auxiliary
boundary-feasible conclusion transports to `hStarDelta`. -/
theorem
    cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundary_and_isMinimizer_of_boundaryFeasible
    (lamDelta : ℝ → ℝ)
    (hStarDelta : ℝ → E)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible :
      0 ≤
        (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    (hmin :
      ∀ {δ : ℝ}, 0 < δ →
        IsMinOn
          (cubicRegularizedQuadraticObjective (gδ(δ)) H M)
          Set.univ
          (hStarDelta δ))
    (hrepr :
      ∀ {δ : ℝ}, 0 < δ →
        hStarDelta δ = hδ(lamDelta,δ))
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto hStarDelta
        (𝓝[>] (0 : ℝ))
        (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) ∧
      IsMinOn
        (cubicRegularizedQuadraticObjective g H M)
        Set.univ
        (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := by
  -- Transport the boundary-feasible conclusion along the eventual equality `hStarDelta = hδ`.
  have hmain :=
    cubicRegularizedDiagonalPerturbedResolvent_tendsto_boundary_and_isMinimizer_of_boundaryFeasible
      g Hdiag M k lamDelta hM hk hGzero hHmin_nonpos hboundary_feasible hopt_max
  have hrepr_eventually :
      hStarDelta =ᶠ[𝓝[>] (0 : ℝ)] (fun δ : ℝ ↦ hδ(lamDelta, δ)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hrepr hδ
  refine ⟨Filter.Tendsto.congr' hrepr_eventually hmain.1, hmain.2⟩

/-- Consequence of the auxiliary boundary-feasible branch theorem for Proposition 4.1.12:
assuming the boundary-feasible regime
`H_min[Hdiag] ≤ 0` together with the displayed radicand nonnegativity, the perturbed minimizers
attached to the corresponding dual branch `λ_δ* = lamDelta δ` converge as `δ → 0+` to the
displayed boundary point. -/
theorem cubicRegularizedDiagonalPerturbedMinimizer_tendsto_boundaryMinimizer
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible :
      0 ≤
        (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    Filter.Tendsto (fun δ : ℝ ↦ hδ(lamDelta, δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k)) := by
  exact
    (cubicRegularizedDiagonalPerturbedResolvent_tendsto_boundary_and_isMinimizer_of_boundaryFeasible
      g Hdiag M k lamDelta hM hk hGzero hHmin_nonpos hboundary_feasible hopt_max).1

/-- Consequence of the auxiliary boundary-feasible branch theorem for Proposition 4.1.12:
assuming the boundary-feasible regime
`H_min[Hdiag] ≤ 0` together with the displayed radicand nonnegativity, the boundary limit point
coming from the corresponding perturbed dual branch is a global minimizer of the original
cubic-regularized quadratic problem. -/
theorem cubicRegularizedDiagonalBoundaryMinimizer_isMinimizer_of_perturbedMinimizers
    (lamDelta : ℝ → ℝ)
    (hM : 0 < M)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (hHmin_nonpos : H_min[Hdiag] ≤ 0)
    (hboundary_feasible :
      0 ≤
        (4 : ℝ) * H_min[Hdiag] ^ (2 : ℕ) / M ^ (2 : ℕ) -
          Finset.sum
            (Finset.univ.filter fun j : Fin n ↦
              j ∉ I*[Hdiag])
            (fun j ↦
              (g j) ^ (2 : ℕ) /
                (Hdiag j - H_min[Hdiag]) ^ (2 : ℕ)))
    (hopt_max :
      ∀ {δ : ℝ}, 0 < δ →
        IsMaxOn
          (cubicRegularizedQuadraticDualFunction (gδ(δ)) H M)
          Dplus(gδ(δ))
          (lamDelta δ)) :
    IsMinOn
      (cubicRegularizedQuadraticObjective g H M)
      Set.univ
      (cubicRegularizedDiagonalBoundaryMinimizer g Hdiag M k) := by
  exact
    (cubicRegularizedDiagonalPerturbedResolvent_tendsto_boundary_and_isMinimizer_of_boundaryFeasible
      g Hdiag M k lamDelta hM hk hGzero hHmin_nonpos hboundary_feasible hopt_max).2

end
