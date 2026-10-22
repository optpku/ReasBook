/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped ConstrainedArgmin CubicRegularizedDiagonalInvariants EuclideanOrthant

noncomputable section

open Filter

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalResolvent_apply` in `Proposition_4_1_10`, the diagonal coordinate
  formula for the canonical resolvent point;
* `resolvent_tau_certificate_mem_lagrangianMinimizers` and
  `resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer` in `Theorem_4_1_10`, the earlier
  certificate machinery for the positive-`G²` regime;
* `cubicRegularizedMinimalDiagonalIndices` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal source
  invariants `I*` and `G²`.

Best owner abstraction:
* source-facing: the perturbed diagonal model `v_δ(h) = v(h) + δ h^(k)` and the resulting
  boundary equation for an optimal perturbed dual point;
* core/canonical: `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, and `IsMaxOn` for the perturbed dual problem;
* bridge/view: the earlier epigraph certificate route from `Theorem_4_1_10`, followed by the
  diagonal resolvent coordinate formula.

Primitive data:
* the diagonal data `Hdiag`, the gradient `g`, the cubic parameter `M`, and the active index
  `k ∈ I*`;
* the source-facing perturbed gradient `g + δ e_k`.

Derived API:
* the scalar dual function and dual domain, already owned upstream;
* the positive-`G²` certificate machinery from `Theorem_4_1_10`;
* dual optimality on the nonnegative feasible set `dom ψ ∩ ℝ₊`, reused through the chapter owner
  `IsMaxOn`.

This file therefore keeps the perturbation owner `cubicRegularizedDiagonalPerturbedGradient`, but
proves Proposition 4.1.11 by moving the perturbed problem into the earlier positive-`G²`
certificate framework and then expanding the resulting resolvent norm coordinatewise. -/

/-- The perturbed linear term obtained from `g` by adding `δ` to the coordinate `k`, encoding
the textbook objective perturbation `v_δ(h) = v(h) + δ h^(k)`. -/
def cubicRegularizedDiagonalPerturbedGradient
    (g : E) (k : Fin n) (δ : ℝ) : E :=
  g + EuclideanSpace.single k δ

/-- Expanding `cubicRegularizedDiagonalPerturbedGradient` gives the coordinatewise perturbation
`g^(i) + δ` at `i = k` and `g^(i)` elsewhere. -/
-- Proof sketch: unfold `cubicRegularizedDiagonalPerturbedGradient` and split on `i = k`.
@[simp]
theorem cubicRegularizedDiagonalPerturbedGradient_apply
    (g : E) (k i : Fin n) (δ : ℝ) :
    cubicRegularizedDiagonalPerturbedGradient g k δ i =
      g i + if i = k then δ else 0 := by
  simp [cubicRegularizedDiagonalPerturbedGradient]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus(" g' ")" =>
  cubicRegularizedQuadraticDualDomain g' H M ∩ Set.Ici (0 : ℝ)
variable {δ : ℝ} {k : Fin n}
local notation "gδ" => cubicRegularizedDiagonalPerturbedGradient g k δ
local notation "ψδ" => cubicRegularizedQuadraticDualFunction gδ H M
local notation "Dplusδ" => Dplus(gδ)
local notation "Λ" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Proposition 4.1.11: perturbing an active coordinate `k ∈ I*` by `δ` turns the
degenerate active squared mass `G² = 0` into the positive value `δ²`. -/
lemma perturbed_activeGradientSquare_eq_delta_sq
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    (δ : ℝ) :
    G²[gδ;Hdiag] = δ ^ (2 : ℕ) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  -- On `I* \ {k}` the perturbed gradient still vanishes, while the `k`-coordinate becomes `δ`.
  rw [cubicRegularizedMinimalDiagonalGradientSquare]
  rw [Finset.sum_eq_single k]
  · have hgk_zero : g k = 0 :=
      active_coordinates_vanish_of_zeroMinimalGradientSquare
        (g := g) (Hdiag := Hdiag) hGzero hk
    rw [cubicRegularizedDiagonalPerturbedGradient_apply]
    simp [hgk_zero]
  · intro i hi hik
    have hgi_zero : g i = 0 :=
      active_coordinates_vanish_of_zeroMinimalGradientSquare
        (g := g) (Hdiag := Hdiag) hGzero hi
    rw [cubicRegularizedDiagonalPerturbedGradient_apply]
    simp [hgi_zero, hik]
  · simp [hk]

/-- Helper for Proposition 4.1.11: the perturbed certificate point has tight slack, so its
`τ`-coordinate equals the norm square of the perturbed resolvent vector. -/
lemma perturbed_certificate_tau_eq_norm_sq
    (hM : 0 < M) (hδ : δ ≠ 0)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    {lamDelta : ℝ}
    (hopt_max : IsMaxOn ψδ Dplusδ lamDelta) :
    cubicRegularizedQuadraticTauMinimizer M lamDelta =
      ‖resolventCertificateVector gδ Hdiag lamDelta‖ ^ (2 : ℕ) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ]
  have hGpos : 0 < G²[gδ;Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  let xPath : Λ → E × ℝ :=
    fun lam ↦ resolventTauCertificatePoint gδ Hdiag M (lam 0)
  let xStar : E × ℝ :=
    resolventTauCertificatePoint gδ Hdiag M lamDelta
  let hStar : E :=
    resolventCertificateVector gδ Hdiag lamDelta
  let ε : ℝ := (lamDelta + H_min[Hdiag]) / 2
  have hDplus : lamDelta ∈ Dplusδ := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := gδ) (Hdiag := Hdiag) (M := M) hM hGpos hopt_max
  have hlam : -H_min[Hdiag] < lamDelta := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := gδ) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hxStar :
      xStar ∈ (cubicRegularizedQuadraticEpigraphProblem gδ H M).lagrangianMinimizers
        (EuclideanSpace.single 0 lamDelta) := by
    -- The perturbed resolvent certificate minimizes the Lagrangian at the maximizing multiplier.
    simpa [xStar] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ) (Hdiag := Hdiag) (M := M) hM
        (μ := lamDelta) hlam
  have hepigraph_max :
      IsMaxOn
        (cubicRegularizedQuadraticEpigraphProblem gδ H M).dualFunction
        (cubicRegularizedQuadraticEpigraphProblem gδ H M).dualFeasibleSet
        (EuclideanSpace.single 0 lamDelta) := by
    -- Move the perturbed scalar maximizer to the one-constraint epigraph dual problem.
    exact
      resolvent_epigraph_dual_maximizer_of_scalar_dual_maximizer
        (g := gδ) (Hdiag := Hdiag) (M := M) hM hGpos hopt_max
  have hlamDelta :
      EuclideanSpace.single 0 lamDelta ∈
        (cubicRegularizedQuadraticEpigraphProblem gδ H M).dualFeasibleSet := by
    -- Dual feasibility is scalar dual-domain membership together with nonnegativity.
    rw [(cubicRegularizedQuadraticEpigraphProblem gδ H M).mem_dualFeasibleSet_iff]
    constructor
    · rw [(cubicRegularizedQuadraticEpigraphProblem gδ H M).mem_dualDomain_iff,
        ← cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
      exact (mem_cubicRegularizedQuadraticDualDomain_iff gδ H M lamDelta).mp hDplus.1
    · intro j
      fin_cases j
      simpa using hDplus.2
  have hxPath :
      ∀ ⦃lam : Λ⦄,
        lam ∈
            Metric.closedBall (EuclideanSpace.single 0 lamDelta) ε ∩ ℝ₊^1 →
          lam ≠ EuclideanSpace.single 0 lamDelta →
          xPath lam ∈
            (cubicRegularizedQuadraticEpigraphProblem gδ H M).lagrangianMinimizers lam := by
    intro lam hmem _
    have hlam_mem : -H_min[Hdiag] < lam 0 := by
      simpa [ε] using
        resolvent_multiplier_coord_gt_negDiagonalMinimum_of_mem_certificate_ball
          (Hdiag := Hdiag) (lamStar := lamDelta) hlam hmem
    -- Nearby feasible multipliers stay in the same resolvent-certificate family.
    rw [dual_certificate_multiplier_eq_single (lam := lam)]
    simpa [xPath] using
      resolvent_tau_certificate_mem_lagrangianMinimizers
        (g := gδ) (Hdiag := Hdiag) (M := M) hM
        (μ := lam 0) hlam_mem
  have hlim :
      Tendsto xPath
        (nhdsWithin (EuclideanSpace.single 0 lamDelta)
          ((Metric.closedBall (EuclideanSpace.single 0 lamDelta) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 lamDelta}))
        (nhds xStar) := by
    -- The perturbed certificate path varies continuously at the maximizing multiplier.
    have hcontPath :
        ContinuousAt xPath (EuclideanSpace.single 0 lamDelta) := by
      simpa [xPath] using
        resolvent_tau_certificate_continuousAt
          (g := gδ) (Hdiag := Hdiag) (M := M) hlam
    simpa [xPath, xStar] using hcontPath.tendsto.mono_left
      (show
        nhdsWithin (EuclideanSpace.single 0 lamDelta)
          ((Metric.closedBall (EuclideanSpace.single 0 lamDelta) ε ∩ ℝ₊^1) \
            {EuclideanSpace.single 0 lamDelta}) ≤
          nhds (EuclideanSpace.single 0 lamDelta) from
        nhdsWithin_le_nhds)
  have hcont :
      ContinuousAt
        (cubicRegularizedQuadraticEpigraphProblem gδ H M).constraintVector
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
        argmin[(cubicRegularizedQuadraticEpigraphProblem gδ H M).feasibleSet]
          (cubicRegularizedQuadraticEpigraphProblem gδ H M) := by
    -- Apply the Chapter 1 dual-certificate theorem to the perturbed certificate path.
    simpa [xPath, xStar, ε] using
      (cubicRegularizedQuadraticEpigraphProblem gδ H M).globalOptimality_of_dualCertificate
        xPath xStar hlamDelta hepigraph_max hε hxPath hlim hcont hxStar
  rw [mem_constrainedArgmin_iff] at hoptimal
  rcases hoptimal with ⟨hxfeas, _⟩
  have hcomp0 :
      lamDelta *
          ((1 / 2 : ℝ) * ‖xStar.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * xStar.2) = 0 := by
    -- Complementary slackness forces the unique epigraph constraint to be tight in the limit.
    simpa [xPath, xStar, cubicRegularizedQuadraticEpigraphProblem] using
      (cubicRegularizedQuadraticEpigraphProblem gδ H M).complementary_slackness_at_limit
        xPath xStar hlamDelta hepigraph_max hε hxPath hlim hcont 0
  have hfeas_ineq :
      ‖hStar‖ ^ (2 : ℕ) ≤ cubicRegularizedQuadraticTauMinimizer M lamDelta := by
    -- Feasibility of the certificate point is exactly the tight-slack inequality.
    simpa [xStar, hStar, resolventTauCertificatePoint] using
      (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
        gδ H M
        (h := hStar) (τ := cubicRegularizedQuadraticTauMinimizer M lamDelta)).mp hxfeas
  have hlam_ne_zero : lamDelta ≠ 0 := by
    intro hlam_zero
    have hHmin_pos : 0 < H_min[Hdiag] := by
      have h0_dom : -H_min[Hdiag] < (0 : ℝ) := by
        simpa [hlam_zero] using hlam
      linarith
    have htau_zero :
        cubicRegularizedQuadraticTauMinimizer M lamDelta = 0 := by
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
      active_coordinates_vanish_of_zeroMinimalGradientSquare
        (g := g) (Hdiag := Hdiag) hGzero hk
    have hk_min : Hdiag k = H_min[Hdiag] :=
      (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag k).mp hk
    have hcoord_k :
        hStar k = -δ / H_min[Hdiag] := by
      -- Route correction: evaluate the resolvent on the distinguished active coordinate instead
      -- of importing the later generic norm identity.
      simp [hStar, resolventCertificateVector, cubicRegularizedDiagonalPerturbedGradient_apply,
        hgk_zero, hk_min, hlam_zero]
    have hk_zero : hStar k = 0 := by
      simpa [hzero_vec]
    have hdelta_zero : δ = 0 := by
      rw [hcoord_k] at hk_zero
      field_simp [hHmin_pos.ne'] at hk_zero
      linarith
    exact hδ hdelta_zero
  have hlam_pos : 0 < lamDelta := by
    have hnonneg : 0 ≤ lamDelta := hDplus.2
    exact lt_of_le_of_ne hnonneg (Ne.symm hlam_ne_zero)
  -- Positive multiplier plus complementary slackness gives the tight-slack identity directly.
  have htight :
      ‖xStar.1‖ ^ (2 : ℕ) = xStar.2 := by
    nlinarith [hcomp0, hlam_pos]
  simpa [xStar, resolventTauCertificatePoint] using htight.symm

/-- Helper for Proposition 4.1.11: the squared norm of the perturbed resolvent splits into the
distinguished active contribution `δ² / (H_min + λ_δ*)²` and the unchanged inactive terms. -/
lemma perturbed_resolvent_norm_sq_eq_boundary_lhs
    (hM : 0 < M) (hδ : δ ≠ 0)
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    {lamDelta : ℝ}
    (hopt_max : IsMaxOn ψδ Dplusδ lamDelta) :
    ‖resolventCertificateVector gδ Hdiag lamDelta‖ ^ (2 : ℕ) =
      δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ]
  have hGpos : 0 < G²[gδ;Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  have hDplus : lamDelta ∈ Dplusδ := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := gδ) (Hdiag := Hdiag) (M := M) hM hGpos hopt_max
  have hlam : -H_min[Hdiag] < lamDelta := by
    simpa [Set.mem_Ioi,
      cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos
        (g := gδ) (Hdiag := Hdiag) (M := M) hM hGpos] using hDplus.1
  let hStar : E := resolventCertificateVector gδ Hdiag lamDelta
  have hgk_zero : g k = 0 :=
    active_coordinates_vanish_of_zeroMinimalGradientSquare
      (g := g) (Hdiag := Hdiag) hGzero hk
  have hk_min : Hdiag k = H_min[Hdiag] :=
    (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag k).mp hk
  have hdenom_k_pos : 0 < H_min[Hdiag] + lamDelta := by
    linarith
  have hactive_sum :
      Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∈ I*[Hdiag])
          (fun i ↦ (hStar i) ^ (2 : ℕ)) =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) := by
    -- Every active term vanishes except the distinguished index `k`, whose numerator is `δ`.
    rw [Finset.sum_eq_single k]
    · have hcoord_k :
          hStar k = -δ / (H_min[Hdiag] + lamDelta) := by
        change -(gδ k) / (Hdiag k + lamDelta) = -δ / (H_min[Hdiag] + lamDelta)
        rw [cubicRegularizedDiagonalPerturbedGradient_apply]
        simp [hgk_zero, hk_min]
      rw [hcoord_k]
      field_simp [hdenom_k_pos.ne']
    · intro i hi hik
      have hi_active : i ∈ I*[Hdiag] := by
        simpa [Finset.mem_filter] using hi
      have hgi_zero : g i = 0 :=
        active_coordinates_vanish_of_zeroMinimalGradientSquare
          (g := g) (Hdiag := Hdiag) hGzero hi_active
      have hi_min : Hdiag i = H_min[Hdiag] :=
        (mem_cubicRegularizedMinimalDiagonalIndices_iff Hdiag i).mp hi_active
      have hgrad_i : gδ i = 0 := by
        change g i + (if i = k then δ else 0) = 0
        simp [hgi_zero, hik]
      have hcoord_i : hStar i = 0 := by
        change -(gδ i) / (Hdiag i + lamDelta) = 0
        rw [hgrad_i]
        simp [hi_min]
      simp [hcoord_i]
    · simp [hk]
  have hinactive_sum :
      Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hStar i) ^ (2 : ℕ)) =
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) := by
    -- Off the active set, the perturbation disappears and the resolvent numerator stays `g i`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_inactive : i ∉ I*[Hdiag] := by
      simpa [Finset.mem_filter] using hi
    have hdenom_i_pos : 0 < Hdiag i + lamDelta := by
      have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
        diagonalMinimum_le_entry (Hdiag := Hdiag) i
      linarith
    have hik : i ≠ k := by
      intro hik
      subst hik
      exact hi_inactive hk
    have hgrad_i : gδ i = g i := by
      change g i + (if i = k then δ else 0) = g i
      simp [hik]
    have hcoord_i :
        hStar i = -g i / (Hdiag i + lamDelta) := by
      change -(gδ i) / (Hdiag i + lamDelta) = -g i / (Hdiag i + lamDelta)
      rw [hgrad_i]
    rw [hcoord_i]
    field_simp [hdenom_i_pos.ne']
  -- Expand the Euclidean norm square and split the active and inactive contributions.
  calc
    ‖hStar‖ ^ (2 : ℕ) = ∑ i : Fin n, (hStar i) ^ (2 : ℕ) := by
      simpa using EuclideanSpace.real_norm_sq_eq hStar
    _ =
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∈ I*[Hdiag])
          (fun i ↦ (hStar i) ^ (2 : ℕ)) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hStar i) ^ (2 : ℕ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i : Fin n ↦ i ∈ I*[Hdiag])]
    _ =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (hStar i) ^ (2 : ℕ)) := by
      rw [hactive_sum]
    _ =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) := by
      rw [hinactive_sum]

/-- Proposition 4.1.11: in the degenerate case `G² = 0`, perturbing the objective by `δ h^(k)`
for `k ∈ I*` and `δ ≠ 0` forces every optimal dual maximizer `λ_δ*` on `dom ψ_δ ∩ ℝ₊` to satisfy
`δ² / (H_min + λ_δ*)² + ∑_{i ∉ I*} (g^(i))² / (H_i + λ_δ*)² = 4 (λ_δ*)² / M²`. -/
theorem perturbedDiagonalDualMaximizer_satisfies_boundaryEquation
    {δ : ℝ} (hM : 0 < M) (hδ : δ ≠ 0) {k : Fin n}
    (hk : k ∈ I*[Hdiag])
    (hGzero : G²[g;Hdiag] = 0)
    {lamDelta : ℝ}
    (hopt_max :
      IsMaxOn
        (cubicRegularizedQuadraticDualFunction
          (cubicRegularizedDiagonalPerturbedGradient g k δ) H M)
        (cubicRegularizedQuadraticDualDomain
            (cubicRegularizedDiagonalPerturbedGradient g k δ) H M ∩
          Set.Ici (0 : ℝ))
        lamDelta) :
    δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦
            i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) =
      (4 : ℝ) * lamDelta ^ (2 : ℕ) / M ^ (2 : ℕ) := by
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    exact Fin.elim0 k
  letI : NeZero n := ⟨hn⟩
  have hδsq_pos : 0 < δ ^ (2 : ℕ) := by
    nlinarith [sq_pos_iff.mpr hδ]
  have hGpos :
      0 < G²[cubicRegularizedDiagonalPerturbedGradient g k δ;Hdiag] := by
    rw [perturbed_activeGradientSquare_eq_delta_sq
      (g := g) (Hdiag := Hdiag) (k := k) hk hGzero δ]
    exact hδsq_pos
  have hDplus :
      lamDelta ∈
        cubicRegularizedQuadraticDualDomain
            (cubicRegularizedDiagonalPerturbedGradient g k δ) H M ∩
          Set.Ici (0 : ℝ) := by
    exact
      scalar_dual_maximizer_mem_Dplus_of_activeGradientSquare_pos
        (g := cubicRegularizedDiagonalPerturbedGradient g k δ)
        (Hdiag := Hdiag) (M := M) hM hGpos hopt_max
  have hnorm :
      ‖resolventCertificateVector
          (cubicRegularizedDiagonalPerturbedGradient g k δ) Hdiag lamDelta‖ ^ (2 : ℕ) =
        δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
          Finset.sum
            (Finset.univ.filter fun i : Fin n ↦ i ∉ I*[Hdiag])
            (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) := by
    exact
      perturbed_resolvent_norm_sq_eq_boundary_lhs
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        hM hδ hk hGzero hopt_max
  have htau :
      cubicRegularizedQuadraticTauMinimizer M lamDelta =
        ‖resolventCertificateVector
            (cubicRegularizedDiagonalPerturbedGradient g k δ) Hdiag lamDelta‖ ^ (2 : ℕ) := by
    exact
      perturbed_certificate_tau_eq_norm_sq
        (g := g) (Hdiag := Hdiag) (M := M) (k := k)
        hM hδ hk hGzero hopt_max
  -- Route correction: use the earlier Theorem 4.1.10 certificate framework, not the later
  -- Proposition 4.1.13 norm-identity API.
  calc
    δ ^ (2 : ℕ) / (H_min[Hdiag] + lamDelta) ^ (2 : ℕ) +
        Finset.sum
          (Finset.univ.filter fun i : Fin n ↦
            i ∉ I*[Hdiag])
          (fun i ↦ (g i) ^ (2 : ℕ) / (Hdiag i + lamDelta) ^ (2 : ℕ)) =
        ‖resolventCertificateVector
            (cubicRegularizedDiagonalPerturbedGradient g k δ) Hdiag lamDelta‖ ^ (2 : ℕ) := by
          exact hnorm.symm
    _ = cubicRegularizedQuadraticTauMinimizer M lamDelta := by
      exact htau.symm
    _ = (4 : ℝ) * lamDelta ^ (2 : ℕ) / M ^ (2 : ℕ) := by
      rw [cubicRegularizedQuadraticTauMinimizer_def, abs_of_nonneg hDplus.2]
      ring

end
