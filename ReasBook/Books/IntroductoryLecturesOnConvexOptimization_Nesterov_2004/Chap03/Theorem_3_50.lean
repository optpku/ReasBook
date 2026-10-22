/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_64
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open EuclideanSpace
open scoped ConvexLipschitz

/- Primary domain: value-oracle lower bounds for constrained convex minimization on `ℓ∞`-balls.

Relevant owner-style declarations sampled before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3` for the primitive feasible-set
  and objective data of a constrained minimization problem;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7` for the
  derived optimal-value and `ε`-accuracy API;
- `ConvexLipschitzOn` and the Lean notation `𝓕⁰⁰[M](Q)` for the textbook class
  `𝓕_M^{0,0}(Q)` in `Chap03/Definition_3_64`, the
  source-facing Chapter 3 owner of fixed-parameter convex Lipschitz objectives on a feasible set;
- `DeterministicValueOracleMethod` and
  `DeterministicValueOracleMethod.oracleTranscript` in `Chap01/Theorem_1_3_9`, the chapter owner
  for ordered deterministic value-oracle methods;
- `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Chap01/Theorem_1_3_9`, the closest upstream owner-pattern for bounded-budget oracle
  correctness on a source-facing problem class;
- `linftyLipschitzClass` and `mem_linftyLipschitzClass_iff_lipschitzOnWith` in
  `Chap01/Definition_1_3_4`, the chapter owner and canonical bridge for `ℓ∞`-Lipschitz
  objectives;
- `EuclideanSpace.linftyClosedBall` in `Chap01/Definition_1_3_2` for the source-facing
  `ℓ∞`-ball owner built from the chapter's `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)`.

Source/core/bridge triage:
- source-facing: the Theorem 3.50 problem-class predicate on
  `SetConstrainedMinimizationProblem`, adding the textbook `ℓ∞`-ball and Lipschitz/convex
  hypotheses without strengthening the source assumptions;
- core/canonical: `SetConstrainedMinimizationProblem`, the source-facing class
  `𝓕⁰⁰[M](B∞(0, R))`, its derived optimal-value and approximate-minimizer API, and
  `DeterministicValueOracleMethod`;
- bridge/view: the source-facing `EuclideanSpace.linftyClosedBall` owner from
  `Definition_1_3_2`, the Chapter 1 coordinate-transport bridge to `LipschitzOnWith`, and the
  canonical feasible-set-indexed method type `Set E → DeterministicValueOracleMethod E`, which
  reuses the Chapter 1 transcript recursion while exposing the constrained problem's feasible set
  to the algorithm.

Primitive data:
- for problems: only the feasible set and objective, owned by
  `SetConstrainedMinimizationProblem`;
- for algorithms: a feasible-set-indexed family `Set E → DeterministicValueOracleMethod E` of
  deterministic query and output rules, each already owned by
  `DeterministicValueOracleMethod`.

Derived API:
- `optimalValue` and `IsApproximateMinimizer` from the Chapter 1 owner abstraction;
- the source-facing Theorem 3.50 class predicate adding nonempty/convex and `Q ⊆ B∞(0, R)` to
  the Chapter 3 function-class owner `problem.objective ∈ 𝓕⁰⁰[M](B∞(0, R))`;
- the companion bridge
  `linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage`, which recovers the canonical
  coordinate-transported `LipschitzOnWith` view without making it the main owner;
- the uniform-accuracy predicate phrased through the Chapter 1 derived API `queryAfter` and
  `outputAfter` after specializing the feasible-set-indexed owner at `problem.feasibleSet`. -/

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/-- Helper for Theorem 3.50: membership in the coordinate image of `B∞(0, R)` is exactly
membership of the transported point in `B∞(0, R)`. -/
private theorem mem_coordImage_linftyClosedBall_iff
    {R : NNReal} {x : Fin n → ℝ} :
    x ∈ coordEquiv '' (linftyClosedBall R : Set E) ↔
      (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈ linftyClosedBall R := by
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm x, hx, ?_⟩
    simpa using (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply x

/-- On `B∞(0, R)`, the textbook `ℓ∞`-Lipschitz estimate is equivalent to the Chapter 1
coordinate-transported `LipschitzOnWith` bridge. The source-facing Theorem 3.50 class keeps the
`‖·‖∞` surface and uses this theorem only as a companion view. -/
theorem linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage
    {f : E → ℝ} {R M : NNReal} :
    (∀ x ∈ linftyClosedBall R, ∀ y ∈ linftyClosedBall R,
      |f x - f y| ≤ (M : ℝ) * ‖x - y‖∞) ↔
      LipschitzOnWith M (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
        (coordEquiv '' (linftyClosedBall R : Set E)) := by
  -- Rewrite the canonical `LipschitzOnWith` owner into the source-facing `ℓ∞` inequality.
  rw [lipschitzOnWith_iff_dist_le_mul]
  constructor
  · intro hf x hx y hy
    have hx' : (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈ linftyClosedBall R :=
      mem_coordImage_linftyClosedBall_iff.mp hx
    have hy' : (EuclideanSpace.equiv (Fin n) ℝ).symm y ∈ linftyClosedBall R :=
      mem_coordImage_linftyClosedBall_iff.mp hy
    -- Transport the pointwise bound back from coordinates to the original `ℓ∞` surface.
    simpa [Function.comp, Real.dist_eq, linftyNorm_eq_coordNorm] using
      hf ((EuclideanSpace.equiv (Fin n) ℝ).symm x) hx'
        ((EuclideanSpace.equiv (Fin n) ℝ).symm y) hy'
  · intro hf x hx y hy
    have hx' : coordEquiv x ∈ coordEquiv '' (linftyClosedBall R : Set E) := by
      exact ⟨x, hx, rfl⟩
    have hy' : coordEquiv y ∈ coordEquiv '' (linftyClosedBall R : Set E) := by
      exact ⟨y, hy, rfl⟩
    -- The coordinate-image Lipschitz estimate is exactly the source-facing one after rewriting.
    simpa [Function.comp, Real.dist_eq, linftyNorm_eq_coordNorm] using
      hf (coordEquiv x) hx' (coordEquiv y) hy'

namespace SetConstrainedMinimizationProblem

/-- The constrained problem class used in Theorem 3.50 is the Chapter 1 owner
`SetConstrainedMinimizationProblem` together with the textbook hypotheses that the feasible set is
nonempty and convex, lies in the ambient closed `ℓ∞`-ball `B∞(0, R)`, and belongs to the
source-facing Chapter 3 class `𝓕_{M}^{0,0}(B∞(0, R))`. The ball radius is carried on the canonical
nonnegative owner `R : NNReal`, rather than as a raw real plus a separate positivity guard. -/
class IsInLinftyConstrainedProblemClass
    (problem : SetConstrainedMinimizationProblem E) (R M : NNReal) : Prop where
  feasibleSet_nonempty : problem.feasibleSet.Nonempty
  feasibleSet_convex : Convex ℝ problem.feasibleSet
  feasibleSet_subset_linftyClosedBall : problem.feasibleSet ⊆ linftyClosedBall R
  objective_mem_F00 : problem.objective ∈ 𝓕⁰⁰[M](linftyClosedBall R)

theorem isInLinftyConstrainedProblemClass_iff
    (problem : SetConstrainedMinimizationProblem E) (R M : NNReal) :
    problem.IsInLinftyConstrainedProblemClass R M ↔
      problem.feasibleSet.Nonempty ∧
        Convex ℝ problem.feasibleSet ∧
        problem.feasibleSet ⊆ linftyClosedBall R ∧
        problem.objective ∈ 𝓕⁰⁰[M](linftyClosedBall R) := by
  constructor
  · intro h
    exact ⟨h.feasibleSet_nonempty, h.feasibleSet_convex,
      h.feasibleSet_subset_linftyClosedBall, h.objective_mem_F00⟩
  · rintro ⟨h_nonempty, h_convex, h_subset, h_mem⟩
    exact ⟨h_nonempty, h_convex, h_subset, h_mem⟩

end SetConstrainedMinimizationProblem

namespace DeterministicValueOracleMethod

/-- A deterministic value-oracle method solves the constrained problem class from Theorem 3.50
within `T` calls when, for every admissible constrained problem, the feasible-set-specialized
method queries only inside `B∞(0, R)` and its transcript-based output is an `ε`-approximate
minimizer in the canonical Chapter 1 sense. -/
def SolvesLinftyConstrainedProblemClassWithin
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ problem : SetConstrainedMinimizationProblem E,
    problem.IsInLinftyConstrainedProblemClass R M →
      (∀ t : ℕ, t < T → (method problem.feasibleSet).queryAfter problem t ∈ linftyClosedBall R) ∧
        problem.IsApproximateMinimizer ε ((method problem.feasibleSet).outputAfter problem T)

end DeterministicValueOracleMethod

/-- Helper for Theorem 3.50: the ambient Euclidean norm dominates the source-facing `ℓ∞` norm. -/
private theorem linftyNorm_le_norm (x : E) :
    ‖x‖∞ ≤ ‖x‖ := by
  rw [linftyNorm_eq_coordNorm]
  refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
  · positivity
  · intro i
    simpa using (PiLp.norm_apply_le x i)

/-- Helper for Theorem 3.50: the coordinate sup-metric is dominated by the ambient Euclidean
metric. -/
private theorem coord_dist_le_dist (x y : E) :
    dist (coordEquiv x) (coordEquiv y) ≤ dist x y := by
  -- Rewrite both metrics through the corresponding norms of the difference.
  simpa [dist_eq_norm, linftyNorm_eq_coordNorm] using linftyNorm_le_norm (x - y)

/-- Helper for Theorem 3.50: the ambient closed `ℓ∞`-ball is convex. -/
private theorem linftyClosedBall_convex (R : NNReal) :
    Convex ℝ (linftyClosedBall R : Set E) := by
  -- The ball is the closed ball of the chapter's `ℓ∞` seminorm owner.
  simpa [EuclideanSpace.linftyClosedBall] using
    (EuclideanSpace.linftySeminorm n).convex_closedBall (0 : E) (R : ℝ)

/-- Helper for Theorem 3.50: the hard objective centered at `u` is `M`-Lipschitz on the ambient
ball in the Euclidean metric. -/
private theorem hard_point_objective_lipschitzOnWith
    {R M : NNReal} (u : E) :
    LipschitzOnWith M (fun x : E ↦ (M : ℝ) * ‖x - u‖∞) (linftyClosedBall R : Set E) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  -- First control the distance-to-center profile in the coordinate sup metric.
  have hbase :
      |dist (coordEquiv x) (coordEquiv u) - dist (coordEquiv y) (coordEquiv u)| ≤
        dist (coordEquiv x) (coordEquiv y) := by
    exact abs_dist_sub_le (coordEquiv x) (coordEquiv y) (coordEquiv u)
  have hscaled :
      |(M : ℝ) * dist (coordEquiv x) (coordEquiv u) -
          (M : ℝ) * dist (coordEquiv y) (coordEquiv u)| ≤
        (M : ℝ) * dist (coordEquiv x) (coordEquiv y) := by
    have hmul :
        (M : ℝ) *
            |dist (coordEquiv x) (coordEquiv u) - dist (coordEquiv y) (coordEquiv u)| ≤
          (M : ℝ) * dist (coordEquiv x) (coordEquiv y) :=
      mul_le_mul_of_nonneg_left hbase M.2
    calc
      |(M : ℝ) * dist (coordEquiv x) (coordEquiv u) -
          (M : ℝ) * dist (coordEquiv y) (coordEquiv u)| =
          |(M : ℝ) *
            (dist (coordEquiv x) (coordEquiv u) - dist (coordEquiv y) (coordEquiv u))| := by
            ring_nf
      _ = |(M : ℝ)| *
          |dist (coordEquiv x) (coordEquiv u) - dist (coordEquiv y) (coordEquiv u)| := by
            rw [abs_mul]
      _ = (M : ℝ) *
          |dist (coordEquiv x) (coordEquiv u) - dist (coordEquiv y) (coordEquiv u)| := by
            simp
      _ ≤ (M : ℝ) * dist (coordEquiv x) (coordEquiv y) := hmul
  have hcoord :
      (M : ℝ) * dist (coordEquiv x) (coordEquiv y) ≤ (M : ℝ) * dist x y :=
    mul_le_mul_of_nonneg_left (coord_dist_le_dist x y) M.2
  -- Then compare the coordinate metric with the ambient Euclidean metric.
  exact le_trans (by simpa [Real.dist_eq, dist_eq_norm, linftyNorm_eq_coordNorm] using hscaled) hcoord

/-- Helper for Theorem 3.50: each hard objective `x ↦ M ‖x - u‖∞` belongs to the admissible
convex-Lipschitz class on `B∞(0, R)`. -/
private theorem hard_point_objective_mem_F00
    {R M : NNReal} {u : E} (_hu : u ∈ linftyClosedBall R) :
    (fun x : E ↦ (M : ℝ) * ‖x - u‖∞) ∈ 𝓕⁰⁰[M](linftyClosedBall R) := by
  refine ConvexLipschitzOn.mem_F00 ?_ ?_
  · have hconv_univ :
        ConvexOn ℝ Set.univ (fun x : E ↦ (M : ℝ) * ‖x - u‖∞) := by
      have hshift :
          ConvexOn ℝ Set.univ (fun x : E ↦ EuclideanSpace.linftySeminorm n (x - u)) := by
        -- Translate the seminorm convexity from the origin to the chosen hard point `u`.
        simpa [sub_eq_add_neg] using
          (EuclideanSpace.linftySeminorm n).convexOn.translate_left (-u)
      -- Scaling by the nonnegative Lipschitz parameter preserves convexity.
      simpa [linftyNorm_eq_linftySeminorm, smul_eq_mul] using hshift.smul M.2
    -- Restrict the global convexity statement to the ambient `ℓ∞`-ball.
    exact hconv_univ.subset (by intro x hx; simp) (linftyClosedBall_convex R)
  · -- The same hard objective is globally Lipschitz, hence also Lipschitz on the ball.
    exact hard_point_objective_lipschitzOnWith u

/-- Helper for Theorem 3.50: the hard objective centered at `u` has optimal value `0` on the
ambient `ℓ∞`-ball, attained exactly at the center. -/
private theorem hard_point_problem_optimalValue_eq_zero
    {R M : NNReal} {u : E} (hu : u ∈ linftyClosedBall R) :
    (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
      (fun x : E ↦ (M : ℝ) * ‖x - u‖∞)).optimalValue = 0 := by
  let problem : SetConstrainedMinimizationProblem E :=
    SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
      (fun x : E ↦ (M : ℝ) * ‖x - u‖∞)
  have hmin : IsMinOn problem problem.feasibleSet u := by
    -- The center `u` is feasible and the hard objective is nonnegative everywhere.
    refine isMinOn_iff.mpr ?_
    intro x hx
    simpa [problem] using (show (0 : ℝ) ≤ (M : ℝ) * ‖x - u‖∞ by positivity)
  -- Evaluating the attained minimum at the center reduces the optimal value to `0`.
  simpa [problem] using problem.optimalValue_eq_of_isMinOn hu hmin

/-- Helper for Theorem 3.50: one common point cannot be `ε`-accurate for two sufficiently
separated hard instances. -/
private theorem common_output_not_accurate_for_both_separated_hard_points
    {M : NNReal} {ε : ℝ} {xBar u v : E}
    (hsep : 8 * ε < (M : ℝ) * ‖u - v‖∞) :
    ¬ (((M : ℝ) * ‖xBar - u‖∞ ≤ ε) ∧ ((M : ℝ) * ‖xBar - v‖∞ ≤ ε)) := by
  intro hboth
  rcases hboth with ⟨hu, hv⟩
  have hε_nonneg : 0 ≤ ε := by
    have hleft_nonneg : 0 ≤ (M : ℝ) * ‖xBar - u‖∞ := by positivity
    exact hleft_nonneg.trans hu
  have htriangle : ‖u - v‖∞ ≤ ‖xBar - u‖∞ + ‖xBar - v‖∞ := by
    simpa [Real.dist_eq, dist_comm, linftyNorm_eq_coordNorm] using
      (dist_triangle (coordEquiv u) (coordEquiv xBar) (coordEquiv v))
  have hmul :
      (M : ℝ) * ‖u - v‖∞ ≤
        (M : ℝ) * ‖xBar - u‖∞ + (M : ℝ) * ‖xBar - v‖∞ := by
    nlinarith [htriangle, M.2]
  have hsmall : (M : ℝ) * ‖u - v‖∞ ≤ 2 * ε := by
    nlinarith
  nlinarith

/-- Helper for Theorem 3.50: the scaled distance-to-set objective is `M`-Lipschitz on the ambient
ball. -/
private theorem scaled_infDist_objective_lipschitzOnWith
    {R M : NNReal} {K : Set E} :
    LipschitzOnWith M (fun x : E ↦ (M : ℝ) * Metric.infDist x K) (linftyClosedBall R : Set E) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  -- The distance-to-set map is globally `1`-Lipschitz, so scaling by `M` gives the desired bound.
  have hbase :
      |Metric.infDist x K - Metric.infDist y K| ≤ dist x y := by
    simpa [Real.dist_eq] using (Metric.lipschitz_infDist_pt K).dist_le_mul x y
  have hmul :
      (M : ℝ) * |Metric.infDist x K - Metric.infDist y K| ≤ (M : ℝ) * dist x y :=
    mul_le_mul_of_nonneg_left hbase M.2
  calc
    dist ((M : ℝ) * Metric.infDist x K) ((M : ℝ) * Metric.infDist y K) =
        |(M : ℝ) * Metric.infDist x K - (M : ℝ) * Metric.infDist y K| := by
          rw [Real.dist_eq]
    _ = |(M : ℝ) * (Metric.infDist x K - Metric.infDist y K)| := by
          ring_nf
    _ = (M : ℝ) * |Metric.infDist x K - Metric.infDist y K| := by
          rw [abs_mul]
          simp
    _ ≤ (M : ℝ) * dist x y := hmul

/-- Helper for Theorem 3.50: if the hard set `K` is nonempty and feasible, then the scaled
distance-to-set objective has optimal value `0`. -/
private theorem scaled_infDist_problem_optimalValue_eq_zero
    {Q K : Set E} {M : NNReal}
    (hKQ : K ⊆ Q) (hK_nonempty : K.Nonempty) :
    (SetConstrainedMinimizationProblem.mk Q
      (fun x : E ↦ (M : ℝ) * Metric.infDist x K)).optimalValue = 0 := by
  let problem : SetConstrainedMinimizationProblem E :=
    SetConstrainedMinimizationProblem.mk Q
      (fun x : E ↦ (M : ℝ) * Metric.infDist x K)
  rcases hK_nonempty with ⟨u, huK⟩
  have huQ : u ∈ problem.feasibleSet := hKQ huK
  have hmin : IsMinOn problem problem.feasibleSet u := by
    -- Any point of `K` is feasible and gives the minimum possible value `0`.
    refine isMinOn_iff.mpr ?_
    intro x hx
    simpa [problem, Metric.infDist_zero_of_mem huK] using
      (show (0 : ℝ) ≤ (M : ℝ) * Metric.infDist x K by
        exact mul_nonneg M.2 Metric.infDist_nonneg)
  -- Evaluating the attained minimum at a point of `K` rewrites the owner optimal value to `0`.
  simpa [problem, Metric.infDist_zero_of_mem huK] using problem.optimalValue_eq_of_isMinOn huQ hmin

/-- Helper for Theorem 3.50: on a hard distance-to-set instance, `ε`-approximate optimality
reduces to the scalar inequality `(M : ℝ) * infDist x̄ K ≤ ε`. -/
private theorem scaled_infDist_le_eps_of_isApproximateMinimizer
    {Q K : Set E} {M : NNReal} {ε : ℝ} {xBar : E}
    (hKQ : K ⊆ Q) (hK_nonempty : K.Nonempty)
    (happrox :
      (SetConstrainedMinimizationProblem.mk Q
        (fun x : E ↦ (M : ℝ) * Metric.infDist x K)).IsApproximateMinimizer ε xBar) :
    (M : ℝ) * Metric.infDist xBar K ≤ ε := by
  -- Rewrite the owner optimal value through the exact minimizer value `0` attained on `K`.
  have hineq := happrox.2
  have hineq' :
      ((((M : ℝ) * Metric.infDist xBar K : ℝ) : EReal) ≤ (ε : EReal)) := by
    simpa [scaled_infDist_problem_optimalValue_eq_zero hKQ hK_nonempty] using hineq
  exact_mod_cast hineq'

/-- Helper for Theorem 3.50: the distance to a nonempty closed convex set is convex. -/
private theorem convexOn_infDist_of_nonempty_isClosed
    {K : Set E} (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) :
    ConvexOn ℝ Set.univ (fun x : E ↦ Metric.infDist x K) := by
  rw [convexOn_iff_forall_pos]
  constructor
  · simpa using (convex_univ : Convex ℝ (Set.univ : Set E))
  · intro x hx y hy a b ha hb hab
    rcases hK_closed.exists_infDist_eq_dist hK_nonempty x with ⟨u, huK, hu_eq⟩
    rcases hK_closed.exists_infDist_eq_dist hK_nonempty y with ⟨v, hvK, hv_eq⟩
    have huvK : a • u + b • v ∈ K := hK_convex huK hvK ha.le hb.le hab
    have hdist_to_K :
        Metric.infDist (a • x + b • y) K ≤
          dist (a • x + b • y) (a • x + b • v) +
            dist (a • x + b • v) (a • u + b • v) := by
      calc
        Metric.infDist (a • x + b • y) K ≤ dist (a • x + b • y) (a • u + b • v) :=
          Metric.infDist_le_dist_of_mem huvK
        _ ≤
            dist (a • x + b • y) (a • x + b • v) +
              dist (a • x + b • v) (a • u + b • v) := by
            simpa [dist_comm] using
              dist_triangle (a • x + b • y) (a • x + b • v) (a • u + b • v)
    have hdist_y : dist (a • x + b • y) (a • x + b • v) = b * dist y v := by
      rw [dist_eq_norm]
      calc
        ‖a • x + b • y - (a • x + b • v)‖ = ‖b • y - b • v‖ := by
          congr 1
          abel_nf
        _ = ‖b • (y - v)‖ := by rw [← smul_sub]
        _ = ‖b‖ * ‖y - v‖ := norm_smul _ _
        _ = b * dist y v := by
          simp [hb.le, dist_eq_norm]
    have hdist_x : dist (a • x + b • v) (a • u + b • v) = a * dist x u := by
      rw [dist_eq_norm]
      calc
        ‖a • x + b • v - (a • u + b • v)‖ = ‖a • x - a • u‖ := by
          congr 1
          abel_nf
        _ = ‖a • (x - u)‖ := by rw [← smul_sub]
        _ = ‖a‖ * ‖x - u‖ := norm_smul _ _
        _ = a * dist x u := by
          simp [ha.le, dist_eq_norm]
    calc
      Metric.infDist (a • x + b • y) K ≤
          dist (a • x + b • y) (a • x + b • v) +
            dist (a • x + b • v) (a • u + b • v) := hdist_to_K
      _ = b * dist y v + a * dist x u := by rw [hdist_y, hdist_x]
      _ = a * Metric.infDist x K + b * Metric.infDist y K := by
        rw [hu_eq, hv_eq]
        ring

/-- Helper for Theorem 3.50: a nonempty closed convex hard set inside `B∞(0, R)` yields an
admissible scaled distance objective in `𝓕⁰⁰[M](B∞(0, R))`. -/
private theorem linfty_axis_box_distance_mem_F00
    {R M : NNReal} {K : Set E}
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (_hK_subset : K ⊆ linftyClosedBall R) :
    (fun x : E ↦ (M : ℝ) * Metric.infDist x K) ∈ 𝓕⁰⁰[M](linftyClosedBall R) := by
  refine ConvexLipschitzOn.mem_F00 ?_ ?_
  · -- Restrict the global convexity of the distance-to-set profile to the ambient `ℓ∞`-ball.
    exact
      (convexOn_infDist_of_nonempty_isClosed hK_nonempty hK_closed hK_convex).smul M.2 |>.subset
        (by intro x hx; simp)
        (linftyClosedBall_convex R)
  · -- The distance-to-set map is globally `1`-Lipschitz, so the scaled objective is admissible.
    exact scaled_infDist_objective_lipschitzOnWith

/-- Helper for Theorem 3.50: a point cannot simultaneously lie within `ε / M` of two nonempty
closed hard sets whose pairwise distance is everywhere larger than `2 ε / M`. -/
private theorem common_output_not_close_to_both_separated_axis_boxes
    {K₁ K₂ : Set E} {M : NNReal} {ε : ℝ} {x : E}
    (hM : 0 < (M : ℝ))
    (hK₁_nonempty : K₁.Nonempty) (hK₁_closed : IsClosed K₁)
    (hK₂_nonempty : K₂.Nonempty) (hK₂_closed : IsClosed K₂)
    (hsep : ∀ u ∈ K₁, ∀ v ∈ K₂, 2 * ε / (M : ℝ) < dist u v) :
    ¬ (((M : ℝ) * Metric.infDist x K₁ ≤ ε) ∧ ((M : ℝ) * Metric.infDist x K₂ ≤ ε)) := by
  intro hboth
  rcases hboth with ⟨hxK₁, hxK₂⟩
  rcases hK₁_closed.exists_infDist_eq_dist hK₁_nonempty x with ⟨u, huK, hu_eq⟩
  rcases hK₂_closed.exists_infDist_eq_dist hK₂_nonempty x with ⟨v, hvK, hv_eq⟩
  have hu_le : dist x u ≤ ε / (M : ℝ) := by
    rw [← hu_eq]
    exact (le_div_iff₀ hM).2 (by simpa [mul_comm] using hxK₁)
  have hv_le : dist x v ≤ ε / (M : ℝ) := by
    rw [← hv_eq]
    exact (le_div_iff₀ hM).2 (by simpa [mul_comm] using hxK₂)
  have huv_lt : 2 * ε / (M : ℝ) < dist u v := hsep u huK v hvK
  have huv_le : dist u v ≤ 2 * ε / (M : ℝ) := by
    have htriangle : dist u v ≤ dist u x + dist x v := by
      simpa [dist_comm] using dist_triangle u x v
    have hsum : dist u x + dist x v ≤ 2 * ε / (M : ℝ) := by
      have hu_le' : dist u x ≤ ε / (M : ℝ) := by simpa [dist_comm] using hu_le
      have hsum' :
          dist u x + dist x v ≤ ε / (M : ℝ) + ε / (M : ℝ) :=
        add_le_add hu_le' hv_le
      calc
        dist u x + dist x v ≤ ε / (M : ℝ) + ε / (M : ℝ) := hsum'
        _ = 2 * ε / (M : ℝ) := by
          ring
    exact htriangle.trans hsum
  exact (not_lt_of_ge huv_le) huv_lt

/-- Helper for Theorem 3.50: once each packaged hard objective has a small-value-to-distance
bridge, the final contradiction reduces to the separated hard-set estimate already proved for the
canonical scaled distance objectives. -/
private theorem common_output_not_small_for_both_separated_hard_instances
    {K₁ K₂ : Set E} {φ₁ φ₂ : E → ℝ} {M : NNReal} {ε : ℝ} {x : E}
    (hM : 0 < (M : ℝ))
    (hK₁_nonempty : K₁.Nonempty) (hK₁_closed : IsClosed K₁)
    (hK₂_nonempty : K₂.Nonempty) (hK₂_closed : IsClosed K₂)
    (hφ₁_bridge : φ₁ x ≤ ε → (M : ℝ) * Metric.infDist x K₁ ≤ ε)
    (hφ₂_bridge : φ₂ x ≤ ε → (M : ℝ) * Metric.infDist x K₂ ≤ ε)
    (hsep : ∀ u ∈ K₁, ∀ v ∈ K₂, 2 * ε / (M : ℝ) < dist u v) :
    ¬ (φ₁ x ≤ ε ∧ φ₂ x ≤ ε) := by
  intro hsmall
  rcases hsmall with ⟨hφ₁_small, hφ₂_small⟩
  -- Convert the packaged objectives to the canonical scaled-distance inequalities.
  have hdist₁ : (M : ℝ) * Metric.infDist x K₁ ≤ ε := hφ₁_bridge hφ₁_small
  have hdist₂ : (M : ℝ) * Metric.infDist x K₂ ≤ ε := hφ₂_bridge hφ₂_small
  -- The existing separated-set contradiction then rules out a common `ε`-small point.
  exact
    common_output_not_close_to_both_separated_axis_boxes
      hM hK₁_nonempty hK₁_closed hK₂_nonempty hK₂_closed hsep ⟨hdist₁, hdist₂⟩

/-- Helper for Theorem 3.50: once two feasible hard sets inside `B∞(0, R)` are nonempty, closed,
convex, and pairwise separated, the canonical scaled distance objectives package them into the
full hard-instance tuple used by the final lower-bound contradiction. -/
private theorem package_separated_axis_box_hard_instances
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hM : 0 < (M : ℝ))
    {K₁ K₂ : Set E}
    (hK₁_nonempty : K₁.Nonempty) (hK₁_closed : IsClosed K₁) (hK₁_convex : Convex ℝ K₁)
    (hK₁_subset : K₁ ⊆ linftyClosedBall R)
    (hK₂_nonempty : K₂.Nonempty) (hK₂_closed : IsClosed K₂) (hK₂_convex : Convex ℝ K₂)
    (hK₂_subset : K₂ ⊆ linftyClosedBall R)
    (hsame_query : ∀ j : ℕ, j < T →
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x K₁)
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x K₁) j)) =
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x K₂)
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x K₁) j)))
    (hsep : ∀ u ∈ K₁, ∀ v ∈ K₂, 2 * ε / (M : ℝ) < dist u v) :
    ∃ φ₁ φ₂ : E → ℝ, ∃ K₁ K₂ : Set E,
      K₁.Nonempty ∧
      IsClosed K₁ ∧
      Convex ℝ K₁ ∧
      K₁ ⊆ linftyClosedBall R ∧
      K₂.Nonempty ∧
      IsClosed K₂ ∧
      Convex ℝ K₂ ∧
      K₂ ⊆ linftyClosedBall R ∧
      φ₁ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
      φ₂ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
      (∀ x ∈ K₁, φ₁ x = 0) ∧
      (∀ x ∈ K₂, φ₂ x = 0) ∧
      (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E) φ₁).optimalValue = 0 ∧
      (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E) φ₂).optimalValue = 0 ∧
      (∀ j : ℕ, j < T →
        φ₁ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j) =
          φ₂ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j)) ∧
        (∀ x : E, ¬ (φ₁ x ≤ ε ∧ φ₂ x ≤ ε)) := by
  -- Package the two hard objectives as the canonical scaled distance-to-set instances.
  let φ₁ : E → ℝ := fun x : E ↦ (M : ℝ) * Metric.infDist x K₁
  let φ₂ : E → ℝ := fun x : E ↦ (M : ℝ) * Metric.infDist x K₂
  refine ⟨φ₁, φ₂, K₁, K₂, hK₁_nonempty, hK₁_closed, hK₁_convex, hK₁_subset,
    hK₂_nonempty, hK₂_closed, hK₂_convex, hK₂_subset, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Each scaled distance objective belongs to the admissible convex-Lipschitz class.
    simpa [φ₁] using linfty_axis_box_distance_mem_F00 hK₁_nonempty hK₁_closed hK₁_convex hK₁_subset
  · -- The second hard instance is packaged in the same canonical way.
    simpa [φ₂] using linfty_axis_box_distance_mem_F00 hK₂_nonempty hK₂_closed hK₂_convex hK₂_subset
  · intro x hx
    -- On the hard set itself, the distance-to-set objective vanishes.
    simp [φ₁, Metric.infDist_zero_of_mem hx]
  · intro x hx
    -- The second hard set has the same zero-on-the-set normalization.
    simp [φ₂, Metric.infDist_zero_of_mem hx]
  · -- Any feasible point of `K₁` attains the exact optimal value `0`.
    simpa [φ₁] using
      (scaled_infDist_problem_optimalValue_eq_zero hK₁_subset hK₁_nonempty)
  · -- Likewise for `K₂`.
    simpa [φ₂] using
      (scaled_infDist_problem_optimalValue_eq_zero hK₂_subset hK₂_nonempty)
  · -- The final pair of goals is the transcript equality together with the separated-set contradiction.
    constructor
    · -- The transcript-equality hypothesis is already stated for the canonical hard objectives.
      simpa [φ₁, φ₂] using hsame_query
    · intro x
      -- The final contradiction is the separated-set estimate for the two distance objectives.
      exact
        common_output_not_small_for_both_separated_hard_instances
          hM hK₁_nonempty hK₁_closed hK₂_nonempty hK₂_closed
          (by intro hx; simpa [φ₁] using hx)
          (by intro hx; simpa [φ₂] using hx)
          hsep

/-- Helper for Theorem 3.50: the source-faithful midpoint response keeps the current uncertainty
box unchanged for queries outside it, and otherwise retains the half-box opposite the queried
midpoint side. -/
private def resistingSuccessor
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (x : E) :
    FeasibilityResistingOracleState n := by
  classical
  exact
    if hx : x ∈ state.currentBox (R : ℝ) hn then
      if hmid : (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn) then
        FeasibilityResistingOracleState.keepLowerHalf state
      else
        FeasibilityResistingOracleState.keepUpperHalf state
    else
      state

/-- Helper for Theorem 3.50: when the query misses the current uncertainty box, the source route
records no midpoint cut and the resisting state is unchanged. -/
private theorem resistingSuccessor_eq_self_of_not_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∉ state.currentBox (R : ℝ) hn) :
    resistingSuccessor R hn state x = state := by
  -- The outside-box branch of the source construction leaves the midpoint transcript unchanged.
  simp [resistingSuccessor, hx]

/-- Helper for Theorem 3.50: for a query in the upper half of the selected coordinate interval,
the source route keeps the lower descendant box. -/
private theorem resistingSuccessor_eq_keepLowerHalf_of_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∈ state.currentBox (R : ℝ) hn)
    (hmid : (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn)) :
    resistingSuccessor R hn state x = FeasibilityResistingOracleState.keepLowerHalf state := by
  -- The midpoint comparison chooses the lower descendant exactly as in Algorithm 3.5.
  simp [resistingSuccessor, hx, hmid]

/-- Helper for Theorem 3.50: for a query in the lower half of the selected coordinate interval,
the source route keeps the upper descendant box. -/
private theorem resistingSuccessor_eq_keepUpperHalf_of_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∈ state.currentBox (R : ℝ) hn)
    (hmid : x (state.nextCoord hn) < (state.currentCenter (R : ℝ) hn) (state.nextCoord hn)) :
    resistingSuccessor R hn state x = FeasibilityResistingOracleState.keepUpperHalf state := by
  -- The strict opposite-side inequality forces the upper descendant branch.
  have hnot : ¬ (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn) :=
    not_le_of_gt hmid
  simp [resistingSuccessor, hx, hnot]

/-- Helper for Theorem 3.50: each source-faithful resisting update increases the midpoint-depth by
at most one. -/
private theorem resistingSuccessor_depth_le_succ
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (x : E) :
    (resistingSuccessor R hn state x).depth ≤ state.depth + 1 := by
  -- A query either leaves the state unchanged or appends exactly one midpoint split.
  by_cases hx : x ∈ state.currentBox (R : ℝ) hn
  · by_cases hmid :
      (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn)
    · simp [resistingSuccessor, hx, hmid, FeasibilityResistingOracleState.depth]
    · simp [resistingSuccessor, hx, hmid, FeasibilityResistingOracleState.depth]
  · simp [resistingSuccessor, hx, Nat.le_succ]

/-- Helper for Theorem 3.50: every query that still lies in the current uncertainty box appends
exactly one midpoint split to the source transcript. -/
private theorem resistingSuccessor_depth_eq_succ_of_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∈ state.currentBox (R : ℝ) hn) :
    (resistingSuccessor R hn state x).depth = state.depth + 1 := by
  -- Inside the current box, the source route always picks one of the two midpoint descendants.
  by_cases hmid :
      (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn)
  · simp [resistingSuccessor, hx, hmid, FeasibilityResistingOracleState.depth]
  · simp [resistingSuccessor, hx, hmid, FeasibilityResistingOracleState.depth]

/-- Helper for Theorem 3.50: the resisting-prefix recursion records the source midpoint choices
made against the first `t` value queries of a fixed deterministic algorithm. -/
private def resistingPrefixState
    (R : NNReal) (hn : 0 < n) (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    ℕ → FeasibilityResistingOracleState n
  | 0 => FeasibilityResistingOracleState.initial
  | t + 1 =>
      resistingSuccessor R hn (resistingPrefixState R hn algorithm oracle t)
        (algorithm.queryAfter oracle t)

/-- Helper for Theorem 3.50: the resisting-prefix recursion starts from the initial uncertainty
box. -/
@[simp] private theorem resistingPrefixState_zero
    (R : NNReal) (hn : 0 < n) (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    resistingPrefixState R hn algorithm oracle 0 = FeasibilityResistingOracleState.initial := by
  -- This is the base case of the source midpoint transcript.
  simp [resistingPrefixState]

/-- Helper for Theorem 3.50: the next resisting-prefix state is obtained by applying the
source-faithful one-step midpoint response to the current query point. -/
@[simp] private theorem resistingPrefixState_succ
    (R : NNReal) (hn : 0 < n) (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ)
    (t : ℕ) :
    resistingPrefixState R hn algorithm oracle (t + 1) =
      resistingSuccessor R hn (resistingPrefixState R hn algorithm oracle t)
        (algorithm.queryAfter oracle t) := by
  -- The recursive clause is definitionally the one-step source update.
  simp [resistingPrefixState]

/-- Helper for Theorem 3.50: after `t` value queries, the source midpoint transcript has depth at
most `t`. -/
private theorem resistingPrefixState_depth_le
    (R : NNReal) (hn : 0 < n) (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    ∀ t : ℕ, (resistingPrefixState R hn algorithm oracle t).depth ≤ t
  | 0 => by
      -- The initial uncertainty box has depth `0`.
      simp [resistingPrefixState, FeasibilityResistingOracleState.depth]
  | t + 1 => by
      -- Each query contributes at most one midpoint split to the resisting transcript.
      have hstep :
          (resistingPrefixState R hn algorithm oracle (t + 1)).depth ≤
            (resistingPrefixState R hn algorithm oracle t).depth + 1 := by
        simpa [resistingPrefixState] using
          resistingSuccessor_depth_le_succ R hn
            (resistingPrefixState R hn algorithm oracle t)
            (algorithm.queryAfter oracle t)
      exact
        le_trans hstep
          (Nat.succ_le_succ (resistingPrefixState_depth_le R hn algorithm oracle t))

/-- Helper for Theorem 3.50: the midpoint of the current coordinate interval lies between the
current lower and upper bounds. -/
private theorem midpoint_currentBounds_mem_interval
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    state.currentLower (R : ℝ) hn i ≤
        midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn) i ∧
      midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn) i ≤
        state.currentUpper (R : ℝ) hn i := by
  have hcenter_mem : state.currentCenter (R : ℝ) hn ∈ state.currentBox (R : ℝ) hn := by
    -- The inradius theorem contains the center in the current box.
    have hsubset :=
      FeasibilityResistingOracleState.closedBall_subset_currentBox (R : ℝ) hn state
    have hrad_nonneg :
        0 ≤ (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) := by
      exact mul_nonneg (by positivity : 0 ≤ (R : ℝ) / 2) (Real.rpow_nonneg (by norm_num) _)
    exact hsubset <| by
      change dist (state.currentCenter (R : ℝ) hn) (state.currentCenter (R : ℝ) hn) ≤
        (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n)
      simpa using hrad_nonneg
  -- Rewriting the center through the midpoint formula exposes the desired interval bounds.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state,
    currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state] at hcenter_mem
  simpa using hcenter_mem i

/-- Helper for Theorem 3.50: each current lower bound is at most the corresponding current upper
bound. -/
private theorem currentLower_le_currentUpper
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (i : Fin n) :
    state.currentLower (R : ℝ) hn i ≤ state.currentUpper (R : ℝ) hn i := by
  -- The midpoint lies in the interval, so the interval endpoints are ordered.
  exact
    le_trans
      (midpoint_currentBounds_mem_interval R hn state i).1
      (midpoint_currentBounds_mem_interval R hn state i).2

/-- Helper for Theorem 3.50: any midpoint coordinate bisection step refines the original
coordinate box whenever the original endpoints are ordered. -/
private theorem midpointCoordinateBisectionStep_box_subset
    {a b a' b' : Fin n → ℝ} {i : Fin n}
    (hab : ∀ j : Fin n, a j ≤ b j)
    (hstep : IsMidpointCoordinateBisectionStep a b a' b' i) :
    {x : E | ∀ j : Fin n, a' j ≤ x j ∧ x j ≤ b' j} ⊆
      {x : E | ∀ j : Fin n, a j ≤ x j ∧ x j ≤ b j} := by
  intro x hx j
  rcases hstep with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  ·
    by_cases hj : j = i
    · subst hj
      constructor
      · simpa [ha'] using (hx j).1
      · have hmid_upper : midpoint ℝ a b j ≤ b j := by
          simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
          nlinarith [hab j]
        exact (show x j ≤ midpoint ℝ a b j from by simpa [hb'] using (hx j).2).trans hmid_upper
    · constructor
      · simpa [ha'] using (hx j).1
      · simpa [hb', hj] using (hx j).2
  ·
    by_cases hj : j = i
    · subst hj
      constructor
      · have ha_mid : a j ≤ midpoint ℝ a b j := by
          simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul]
          nlinarith [hab j]
        exact ha_mid.trans (show midpoint ℝ a b j ≤ x j from by simpa [ha'] using (hx j).1)
      · simpa [hb'] using (hx j).2
    · constructor
      · simpa [ha', hj] using (hx j).1
      · simpa [hb'] using (hx j).2

/-- Helper for Theorem 3.50: keeping the lower half refines the current uncertainty box. -/
private theorem keepLowerHalf_currentBox_subset_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentBox (R : ℝ) hn ⊆
      state.currentBox (R : ℝ) hn := by
  -- Repackage the keep-lower refinement as a generic midpoint-bisection box inclusion.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn
      (FeasibilityResistingOracleState.keepLowerHalf state),
    currentBox_eq_currentBounds_set (R : ℝ) hn state]
  exact
    midpointCoordinateBisectionStep_box_subset
      (fun i ↦ currentLower_le_currentUpper R hn state i)
      (state.keepLowerHalf_isMidpointCoordinateBisectionStep (R : ℝ) hn)

/-- Helper for Theorem 3.50: keeping the upper half refines the current uncertainty box. -/
private theorem keepUpperHalf_currentBox_subset_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentBox (R : ℝ) hn ⊆
      state.currentBox (R : ℝ) hn := by
  -- The upper-half refinement is the second branch of the same generic bisection inclusion.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn
      (FeasibilityResistingOracleState.keepUpperHalf state),
    currentBox_eq_currentBounds_set (R : ℝ) hn state]
  exact
    midpointCoordinateBisectionStep_box_subset
      (fun i ↦ currentLower_le_currentUpper R hn state i)
      (state.keepUpperHalf_isMidpointCoordinateBisectionStep (R : ℝ) hn)

/-- Helper for Theorem 3.50: every realized uncertainty box stays inside the ambient closed
`ℓ∞`-ball `B∞(0, R)`. -/
private theorem currentBox_subset_linftyClosedBall
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentBox (R : ℝ) hn ⊆ linftyClosedBall R := by
  induction state with
  | initial =>
      intro x hx
      rw [currentBox_eq_currentBounds_set (R : ℝ) hn
          (FeasibilityResistingOracleState.initial : FeasibilityResistingOracleState n)] at hx
      rw [mem_linftyClosedBall_iff, linftyNorm_eq_coordNorm]
      refine (pi_norm_le_iff_of_nonneg R.2).2 ?_
      intro i
      rcases hx i with ⟨hlo, hhi⟩
      exact abs_le.2 ⟨by simpa using hlo, by simpa using hhi⟩
  | keepLowerHalf state ih =>
      -- Refinement of the current box preserves the ambient `ℓ∞`-ball containment.
      exact Set.Subset.trans (keepLowerHalf_currentBox_subset_currentBox R hn state) ih
  | keepUpperHalf state ih =>
      -- The same monotonicity holds for the upper-half refinement.
      exact Set.Subset.trans (keepUpperHalf_currentBox_subset_currentBox R hn state) ih

/-- Helper for Theorem 3.50: every realized current box is a nonempty closed convex set. This is
the admissibility package needed before using distance-to-set identities on descendant boxes. -/
private theorem currentBox_nonempty_isClosed_convex
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (state.currentBox (R : ℝ) hn).Nonempty ∧
      IsClosed (state.currentBox (R : ℝ) hn) ∧
      Convex ℝ (state.currentBox (R : ℝ) hn) := by
  have hcenter_mem : state.currentCenter (R : ℝ) hn ∈ state.currentBox (R : ℝ) hn := by
    -- Rewrite the current center through the midpoint formula so each coordinate lands in bounds.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state,
      currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state]
    intro i
    exact midpoint_currentBounds_mem_interval R hn state i
  refine ⟨⟨_, hcenter_mem⟩, ?_, ?_⟩
  · -- The coordinate box is an intersection of closed coordinate slabs.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
    have hclosed_coord (i : Fin n) :
        IsClosed
          {x : E |
            state.currentLower (R : ℝ) hn i ≤ x i ∧
              x i ≤ state.currentUpper (R : ℝ) hn i} := by
      have hcont_apply : Continuous fun x : E ↦ x i := by
        simpa using
          (continuous_apply i).comp ((EuclideanSpace.equiv (Fin n) ℝ).continuous)
      exact
        (isClosed_le continuous_const hcont_apply).inter
          (isClosed_le hcont_apply continuous_const)
    simpa [Set.setOf_forall] using isClosed_iInter hclosed_coord
  · -- Convexity is coordinatewise because affine combinations preserve each interval bound.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
    intro x hx y hy a b ha hb hab i
    constructor
    · have hx_lower := (hx i).1
      have hy_lower := (hy i).1
      have hx_scaled :
          a * state.currentLower (R : ℝ) hn i ≤ a * x i :=
        mul_le_mul_of_nonneg_left hx_lower ha
      have hy_scaled :
          b * state.currentLower (R : ℝ) hn i ≤ b * y i :=
        mul_le_mul_of_nonneg_left hy_lower hb
      have hsum :
          (a + b) * state.currentLower (R : ℝ) hn i ≤ a * x i + b * y i := by
        nlinarith
      simpa [smul_eq_mul, hab] using hsum
    · have hx_upper := (hx i).2
      have hy_upper := (hy i).2
      have hx_scaled :
          a * x i ≤ a * state.currentUpper (R : ℝ) hn i :=
        mul_le_mul_of_nonneg_left hx_upper ha
      have hy_scaled :
          b * y i ≤ b * state.currentUpper (R : ℝ) hn i :=
        mul_le_mul_of_nonneg_left hy_upper hb
      have hsum :
          a * x i + b * y i ≤ (a + b) * state.currentUpper (R : ℝ) hn i := by
        nlinarith
      simpa [smul_eq_mul, hab] using hsum

/-- Helper for Theorem 3.50: coordinatewise clamping sends any query point to the nearest point of
the current box. This stable owner-level projection is the right bridge for later descendant-box
compatibility arguments. -/
private def currentBoxProjection
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (q : E) : E :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i =>
    if _hlow : q i ≤ state.currentLower (R : ℝ) hn i then
      state.currentLower (R : ℝ) hn i
    else if _hupp : state.currentUpper (R : ℝ) hn i ≤ q i then
      state.currentUpper (R : ℝ) hn i
    else
      q i

/-- Helper for Theorem 3.50: the coordinatewise clamp indeed lands in the current box. -/
private theorem currentBoxProjection_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (q : E) :
    currentBoxProjection R hn state q ∈ state.currentBox (R : ℝ) hn := by
  -- Check membership coordinatewise by splitting according to which current-box face clamps `q`.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
  intro i
  by_cases hlow : q i ≤ state.currentLower (R : ℝ) hn i
  · constructor
    · simp [currentBoxProjection, hlow]
    · simpa [currentBoxProjection, hlow] using currentLower_le_currentUpper R hn state i
  · by_cases hupp : state.currentUpper (R : ℝ) hn i ≤ q i
    · constructor
      · have hle :
          state.currentLower (R : ℝ) hn i ≤ state.currentUpper (R : ℝ) hn i :=
          currentLower_le_currentUpper R hn state i
        simpa [currentBoxProjection, hlow, hupp] using hle
      · simp [currentBoxProjection, hlow, hupp]
    · constructor
      · have hle : state.currentLower (R : ℝ) hn i ≤ q i := by
          exact le_of_not_ge hlow
        simpa [currentBoxProjection, hlow, hupp] using hle
      · have hle : q i ≤ state.currentUpper (R : ℝ) hn i := by
          exact le_of_not_ge hupp
        simpa [currentBoxProjection, hlow, hupp] using hle

/-- Helper for Theorem 3.50: the coordinatewise clamp minimizes Euclidean distance among all
points of the current box. -/
private theorem currentBoxProjection_dist_le_dist_of_mem_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {q y : E}
    (hy : y ∈ state.currentBox (R : ℝ) hn) :
    dist q (currentBoxProjection R hn state q) ≤ dist q y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hcoord :
      ∀ i : Fin n,
        ‖(q - currentBoxProjection R hn state q) i‖ ≤ ‖(q - y) i‖ := by
    intro i
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hy
    have hyi := hy i
    by_cases hlow : q i ≤ state.currentLower (R : ℝ) hn i
    · have hqy : q i ≤ y i := le_trans hlow hyi.1
      have habs :
          |q i - state.currentLower (R : ℝ) hn i| ≤ |q i - y i| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hlow), abs_of_nonpos (sub_nonpos.mpr hqy)]
        linarith
      simpa [Real.norm_eq_abs, currentBoxProjection, hlow]
        using habs
    · by_cases hupp : state.currentUpper (R : ℝ) hn i ≤ q i
      · have hyq : y i ≤ q i := le_trans hyi.2 hupp
        have habs :
            |q i - state.currentUpper (R : ℝ) hn i| ≤ |q i - y i| := by
          rw [abs_of_nonneg (sub_nonneg.mpr hupp), abs_of_nonneg (sub_nonneg.mpr hyq)]
          linarith
        simpa [Real.norm_eq_abs, currentBoxProjection, hlow, hupp]
          using habs
      · have hnonneg : 0 ≤ ‖(q - y) i‖ := norm_nonneg _
        simpa [currentBoxProjection, hlow, hupp] using hnonneg
  -- Pointwise control of the coordinate errors gives the Euclidean norm comparison.
  have hnorm :
      ‖q - currentBoxProjection R hn state q‖ ≤ ‖q - y‖ := by
    have hsq :
        ‖q - currentBoxProjection R hn state q‖ ^ 2 ≤ ‖q - y‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) (q - currentBoxProjection R hn state q),
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) (q - y)]
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi' := hcoord i
      exact (sq_le_sq).2 <| by simpa using hi'
    -- Since both Euclidean norms are nonnegative, the squared inequality descends to the norms.
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  exact hnorm

/-- Helper for Theorem 3.50: the Euclidean distance to the current box is realized by the
coordinatewise clamp. This packages the multi-face `infDist` geometry into a reusable bridge. -/
private theorem infDist_eq_dist_currentBoxProjection
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (q : E) :
    Metric.infDist q (state.currentBox (R : ℝ) hn) =
      dist q (currentBoxProjection R hn state q) := by
  have hproj_mem :
      currentBoxProjection R hn state q ∈ state.currentBox (R : ℝ) hn :=
    currentBoxProjection_mem_currentBox R hn state q
  have hupper :
      Metric.infDist q (state.currentBox (R : ℝ) hn) ≤
        dist q (currentBoxProjection R hn state q) := by
    exact Metric.infDist_le_dist_of_mem hproj_mem
  have hnonempty : (state.currentBox (R : ℝ) hn).Nonempty :=
    (currentBox_nonempty_isClosed_convex R hn state).1
  have hlower :
      dist q (currentBoxProjection R hn state q) ≤
        Metric.infDist q (state.currentBox (R : ℝ) hn) := by
    -- Every box point is at least as far as the coordinatewise clamp.
    rw [Metric.le_infDist hnonempty]
    intro y hy
    exact currentBoxProjection_dist_le_dist_of_mem_currentBox R hn state hy
  exact le_antisymm hupper hlower

/-- Helper for Theorem 3.50: if two current boxes have the same coordinatewise clamp of a query,
then their scaled distance-to-box values agree. This isolates future transport arguments from the
full `infDist` geometry. -/
private theorem scaledInfDist_eq_of_same_currentBoxProjection
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n) (q : E)
    (hproj :
      currentBoxProjection R hn state₁ q =
        currentBoxProjection R hn state₂ q) :
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
  -- Normalize both distances to the same clamped point and compare there.
  calc
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
        (M : ℝ) * dist q (currentBoxProjection R hn state₁ q) := by
          rw [infDist_eq_dist_currentBoxProjection R hn state₁ q]
    _ = (M : ℝ) * dist q (currentBoxProjection R hn state₂ q) := by
          rw [hproj]
    _ = (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
          rw [infDist_eq_dist_currentBoxProjection R hn state₂ q]

/-- Helper for Theorem 3.50: preserving all parent-box clamped coordinates keeps the whole
distance-to-box value unchanged. This is the projection-level version of the planned descendant
compatibility bridge. -/
private theorem currentBoxProjection_eq_of_queryCompatibleCurrentBoxes
    (R : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E)
    (hlower :
      ∀ i : Fin n,
        q i ≤ parent.currentLower (R : ℝ) hn i →
          child.currentLower (R : ℝ) hn i = parent.currentLower (R : ℝ) hn i)
    (hupper :
      ∀ i : Fin n,
        parent.currentUpper (R : ℝ) hn i ≤ q i →
          child.currentUpper (R : ℝ) hn i = parent.currentUpper (R : ℝ) hn i)
    (hinside :
      ∀ i : Fin n,
        ¬ q i ≤ parent.currentLower (R : ℝ) hn i →
          ¬ parent.currentUpper (R : ℝ) hn i ≤ q i →
            child.currentLower (R : ℝ) hn i ≤ q i ∧
              q i ≤ child.currentUpper (R : ℝ) hn i) :
    currentBoxProjection R hn child q =
      currentBoxProjection R hn parent q := by
  -- Compare the clamp coordinatewise, splitting by how `q` sits relative to the parent box.
  ext i
  by_cases hlow : q i ≤ parent.currentLower (R : ℝ) hn i
  · have hchild :
        child.currentLower (R : ℝ) hn i =
          parent.currentLower (R : ℝ) hn i :=
      hlower i hlow
    have hlow_child : q i ≤ child.currentLower (R : ℝ) hn i := by
      simpa [hchild] using hlow
    simp [currentBoxProjection, hlow, hlow_child, hchild]
  · by_cases hupp : parent.currentUpper (R : ℝ) hn i ≤ q i
    · have hchild :
          child.currentUpper (R : ℝ) hn i =
            parent.currentUpper (R : ℝ) hn i :=
        hupper i hupp
      have hupp_child : child.currentUpper (R : ℝ) hn i ≤ q i := by
        simpa [hchild] using hupp
      by_cases hlow_child : q i ≤ child.currentLower (R : ℝ) hn i
      · have hchild_lower :
            child.currentLower (R : ℝ) hn i =
              parent.currentUpper (R : ℝ) hn i := by
          apply le_antisymm
          · calc
              child.currentLower (R : ℝ) hn i ≤ child.currentUpper (R : ℝ) hn i :=
                currentLower_le_currentUpper R hn child i
              _ = parent.currentUpper (R : ℝ) hn i := hchild
          · calc
              parent.currentUpper (R : ℝ) hn i ≤ q i := hupp
              _ ≤ child.currentLower (R : ℝ) hn i := hlow_child
        simp [currentBoxProjection, hlow, hupp, hlow_child, hchild, hchild_lower]
      · simp [currentBoxProjection, hlow, hupp, hlow_child, hchild, hupp_child]
    · have hchild_inside := hinside i hlow hupp
      by_cases hlow_child : q i ≤ child.currentLower (R : ℝ) hn i
      · have hqeq : q i = child.currentLower (R : ℝ) hn i :=
          le_antisymm hlow_child hchild_inside.1
        have hchild_proj :
            currentBoxProjection R hn child q i = q i := by
          simp [currentBoxProjection, hlow_child, hqeq]
        have hparent_proj :
            currentBoxProjection R hn parent q i = q i := by
          simp [currentBoxProjection, hlow, hupp]
        exact hchild_proj.trans hparent_proj.symm
      · by_cases hupp_child : child.currentUpper (R : ℝ) hn i ≤ q i
        · have hqeq : q i = child.currentUpper (R : ℝ) hn i :=
            le_antisymm hchild_inside.2 hupp_child
          have hchild_not_lower :
              ¬ child.currentUpper (R : ℝ) hn i ≤ child.currentLower (R : ℝ) hn i := by
            intro hle
            exact hlow_child (by simpa [hqeq] using hle)
          have hchild_proj :
              currentBoxProjection R hn child q i = q i := by
            simp [currentBoxProjection, hqeq, hchild_not_lower, hupp_child]
          have hparent_proj :
              currentBoxProjection R hn parent q i = q i := by
            simp [currentBoxProjection, hlow, hupp]
          exact hchild_proj.trans hparent_proj.symm
        · simp [currentBoxProjection, hlow, hupp, hlow_child, hupp_child]

/-- Helper for Theorem 3.50: a descendant current box with the same parent-box clamp as the
parent itself has the same scaled distance value on that query. -/
private theorem scaledInfDist_eq_parent_of_queryCompatibleDescendantCurrentBox
    (R M : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E)
    (hlower :
      ∀ i : Fin n,
        q i ≤ parent.currentLower (R : ℝ) hn i →
          child.currentLower (R : ℝ) hn i = parent.currentLower (R : ℝ) hn i)
    (hupper :
      ∀ i : Fin n,
        parent.currentUpper (R : ℝ) hn i ≤ q i →
          child.currentUpper (R : ℝ) hn i = parent.currentUpper (R : ℝ) hn i)
    (hinside :
      ∀ i : Fin n,
        ¬ q i ≤ parent.currentLower (R : ℝ) hn i →
          ¬ parent.currentUpper (R : ℝ) hn i ≤ q i →
            child.currentLower (R : ℝ) hn i ≤ q i ∧
              q i ≤ child.currentUpper (R : ℝ) hn i) :
    (M : ℝ) * Metric.infDist q (child.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (parent.currentBox (R : ℝ) hn) := by
  -- Route correction: compare each descendant box to the parent clamp, not to another child box.
  refine (scaledInfDist_eq_of_same_currentBoxProjection R M hn child parent q ?_).trans ?_
  · exact
      (currentBoxProjection_eq_of_queryCompatibleCurrentBoxes
        R hn parent child q hlower hupper hinside)
  · rfl

/-- Helper for Theorem 3.50: `queryCompatibleCurrentBox R hn parent child q` packages the three
coordinatewise clauses saying that `child` preserves the parent clamp of `q`. This is the natural
recorded-constraint surface for the transcript-first route. -/
private def queryCompatibleCurrentBox
    (R : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E) : Prop :=
  (∀ i : Fin n,
      q i ≤ parent.currentLower (R : ℝ) hn i →
        child.currentLower (R : ℝ) hn i = parent.currentLower (R : ℝ) hn i) ∧
    (∀ i : Fin n,
      parent.currentUpper (R : ℝ) hn i ≤ q i →
        child.currentUpper (R : ℝ) hn i = parent.currentUpper (R : ℝ) hn i) ∧
      (∀ i : Fin n,
        ¬ q i ≤ parent.currentLower (R : ℝ) hn i →
          ¬ parent.currentUpper (R : ℝ) hn i ≤ q i →
            child.currentLower (R : ℝ) hn i ≤ q i ∧
              q i ≤ child.currentUpper (R : ℝ) hn i)

/-- Helper for Theorem 3.50: the packaged compatibility predicate rewrites the child clamp back to
the parent clamp of the same query. -/
private theorem currentBoxProjection_eq_of_queryCompatible
    (R : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E)
    (hcompat : queryCompatibleCurrentBox R hn parent child q) :
    currentBoxProjection R hn child q =
      currentBoxProjection R hn parent q := by
  rcases hcompat with ⟨hlower, hupper, hinside⟩
  -- Unpack the recorded compatibility clauses and apply the existing projection bridge once.
  exact
    currentBoxProjection_eq_of_queryCompatibleCurrentBoxes
      R hn parent child q hlower hupper hinside

/-- Helper for Theorem 3.50: two descendants that are both `queryCompatibleCurrentBox` with the
same parent/query already share the parent's clamp point. This is the exact obstruction showing
why the old shared-projection successor route cannot coexist with positive separation. -/
private theorem commonPoint_of_twoQueryCompatibleCurrentBoxes
    (R : NNReal) (hn : 0 < n)
    (parent child₁ child₂ : FeasibilityResistingOracleState n) (q : E)
    (hcompat₁ : queryCompatibleCurrentBox R hn parent child₁ q)
    (hcompat₂ : queryCompatibleCurrentBox R hn parent child₂ q) :
    ∃ p : E,
      p ∈ child₁.currentBox (R : ℝ) hn ∧
        p ∈ child₂.currentBox (R : ℝ) hn := by
  refine ⟨currentBoxProjection R hn parent q, ?_, ?_⟩
  · -- The first child contains the common clamp point because its clamp matches the parent's.
    have hproj_eq :
        currentBoxProjection R hn child₁ q =
          currentBoxProjection R hn parent q :=
      currentBoxProjection_eq_of_queryCompatible R hn parent child₁ q hcompat₁
    simpa [hproj_eq] using currentBoxProjection_mem_currentBox R hn child₁ q
  · -- The same argument puts the common clamp point inside the second child box as well.
    have hproj_eq :
        currentBoxProjection R hn child₂ q =
          currentBoxProjection R hn parent q :=
      currentBoxProjection_eq_of_queryCompatible R hn parent child₂ q hcompat₂
    simpa [hproj_eq] using currentBoxProjection_mem_currentBox R hn child₂ q

/-- Helper for Theorem 3.50: any recorded compatibility package transports the scaled
distance-to-current-box value from the parent state to the compatible child state. -/
private theorem projectedValueStable_ofRecordedConstraint
    (R M : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E)
    (hcompat : queryCompatibleCurrentBox R hn parent child q) :
    (M : ℝ) * Metric.infDist q (child.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (parent.currentBox (R : ℝ) hn) := by
  rcases hcompat with ⟨hlower, hupper, hinside⟩
  -- The projection-level compatibility already packages the whole `infDist` transport.
  exact
    scaledInfDist_eq_parent_of_queryCompatibleDescendantCurrentBox
      R M hn parent child q hlower hupper hinside

/-- Helper for Theorem 3.50: if two descendant current boxes are both compatible with the same
recorded parent/query pair, then they admit a common step value given by the parent-box
distance. This isolates the remaining blocker to constructing compatible descendants. -/
private theorem commonStepValue_of_queryCompatibleCurrentBoxes
    (R M : NNReal) (hn : 0 < n)
    (parent child₁ child₂ : FeasibilityResistingOracleState n) (q : E)
    (hcompat₁ : queryCompatibleCurrentBox R hn parent child₁ q)
    (hcompat₂ : queryCompatibleCurrentBox R hn parent child₂ q) :
    ∃ v,
      (M : ℝ) * Metric.infDist q (child₁.currentBox (R : ℝ) hn) = v ∧
        (M : ℝ) * Metric.infDist q (child₂.currentBox (R : ℝ) hn) = v := by
  refine ⟨(M : ℝ) * Metric.infDist q (parent.currentBox (R : ℝ) hn), ?_, ?_⟩
  · -- Choose the parent-box value as the common recorded transcript value for the first child.
    exact projectedValueStable_ofRecordedConstraint R M hn parent child₁ q hcompat₁
  · -- The same parent-box value works for the second compatible child as well.
    exact projectedValueStable_ofRecordedConstraint R M hn parent child₂ q hcompat₂

/-- Helper for Theorem 3.50: a vector supported on one coordinate has Euclidean norm equal to the
absolute value of that coordinate. -/
private theorem norm_single_eq_abs (i : Fin n) (a : ℝ) :
    ‖(EuclideanSpace.single i a : E)‖ = |a| := by
  simpa [EuclideanSpace.single] using
    (PiLp.norm_single (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ) i a)

/-- Helper for Theorem 3.50: if a point leaves the current box only through the lower face of one
coordinate, its Euclidean distance to the current box is exactly that lower-face gap. -/
private theorem infDist_eq_lowerFaceGap_of_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hqi : q i ≤ state.currentLower (R : ℝ) hn i)
    (hinside :
      ∀ j : Fin n, j ≠ i →
        state.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state.currentUpper (R : ℝ) hn j) :
    Metric.infDist q (state.currentBox (R : ℝ) hn) =
      state.currentLower (R : ℝ) hn i - q i := by
  let p : E :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (Function.update (EuclideanSpace.equiv (Fin n) ℝ q) i (state.currentLower (R : ℝ) hn i))
  have hp_mem : p ∈ state.currentBox (R : ℝ) hn := by
    -- Project `q` to the lower face by clamping only the exposed coordinate.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
    intro j
    by_cases hj : j = i
    · subst j
      constructor
      · simp [p, Function.update]
      · simpa [p, Function.update] using currentLower_le_currentUpper R hn state i
    · simpa [p, Function.update, hj] using hinside j hj
  have hp_dist :
      dist q p = state.currentLower (R : ℝ) hn i - q i := by
    -- The projection changes only coordinate `i`, so the norm is a one-coordinate norm.
    rw [dist_eq_norm]
    have hsub :
        q - p =
          (EuclideanSpace.single i (q i - state.currentLower (R : ℝ) hn i) : E) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [p, Function.update]
      · simp [p, Function.update, hj]
    rw [hsub, norm_single_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hqi)]
    ring
  have hupper :
      Metric.infDist q (state.currentBox (R : ℝ) hn) ≤
        state.currentLower (R : ℝ) hn i - q i := by
    -- The explicit projection point gives the upper bound on the infimum distance.
    rw [← hp_dist]
    exact Metric.infDist_le_dist_of_mem hp_mem
  have hnonempty : (state.currentBox (R : ℝ) hn).Nonempty :=
    (currentBox_nonempty_isClosed_convex R hn state).1
  have hlower :
      state.currentLower (R : ℝ) hn i - q i ≤
        Metric.infDist q (state.currentBox (R : ℝ) hn) := by
    -- Every box point stays at least the face gap away in coordinate `i`.
    rw [Metric.le_infDist hnonempty]
    intro y hy
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hy
    have hyi : state.currentLower (R : ℝ) hn i ≤ y i := (hy i).1
    have hgap_le_abs :
        state.currentLower (R : ℝ) hn i - q i ≤ |q i - y i| := by
      have hqy : q i ≤ y i := le_trans hqi hyi
      rw [abs_of_nonpos (sub_nonpos.mpr hqy)]
      linarith
    have hcoord :
        |q i - y i| ≤ dist q y := by
      simpa [dist_eq_norm] using (PiLp.norm_apply_le (q - y) i)
    exact le_trans hgap_le_abs hcoord
  exact le_antisymm hupper hlower

/-- Helper for Theorem 3.50: if a point leaves the current box only through the upper face of one
coordinate, its Euclidean distance to the current box is exactly that upper-face gap. -/
private theorem infDist_eq_upperFaceGap_of_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hqi : state.currentUpper (R : ℝ) hn i ≤ q i)
    (hinside :
      ∀ j : Fin n, j ≠ i →
        state.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state.currentUpper (R : ℝ) hn j) :
    Metric.infDist q (state.currentBox (R : ℝ) hn) =
      q i - state.currentUpper (R : ℝ) hn i := by
  let p : E :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (Function.update (EuclideanSpace.equiv (Fin n) ℝ q) i (state.currentUpper (R : ℝ) hn i))
  have hp_mem : p ∈ state.currentBox (R : ℝ) hn := by
    -- Project `q` to the upper face by clamping only the exposed coordinate.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
    intro j
    by_cases hj : j = i
    · subst j
      constructor
      · simpa [p, Function.update] using currentLower_le_currentUpper R hn state i
      · simp [p, Function.update]
    · simpa [p, Function.update, hj] using hinside j hj
  have hp_dist :
      dist q p = q i - state.currentUpper (R : ℝ) hn i := by
    -- Again only coordinate `i` changes, so the distance is the exposed face gap.
    rw [dist_eq_norm]
    have hsub :
        q - p =
          (EuclideanSpace.single i (q i - state.currentUpper (R : ℝ) hn i) : E) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [p, Function.update]
      · simp [p, Function.update, hj]
    rw [hsub, norm_single_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr hqi)]
  have hupper :
      Metric.infDist q (state.currentBox (R : ℝ) hn) ≤
        q i - state.currentUpper (R : ℝ) hn i := by
    -- The explicit upper-face projection gives the matching upper bound.
    rw [← hp_dist]
    exact Metric.infDist_le_dist_of_mem hp_mem
  have hnonempty : (state.currentBox (R : ℝ) hn).Nonempty :=
    (currentBox_nonempty_isClosed_convex R hn state).1
  have hlower :
      q i - state.currentUpper (R : ℝ) hn i ≤
        Metric.infDist q (state.currentBox (R : ℝ) hn) := by
    -- Every box point stays at least the upper-face gap away in coordinate `i`.
    rw [Metric.le_infDist hnonempty]
    intro y hy
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hy
    have hyi : y i ≤ state.currentUpper (R : ℝ) hn i := (hy i).2
    have hgap_le_abs :
        q i - state.currentUpper (R : ℝ) hn i ≤ |q i - y i| := by
      have hyq : y i ≤ q i := le_trans hyi hqi
      rw [abs_of_nonneg (sub_nonneg.mpr hyq)]
      linarith
    have hcoord :
        |q i - y i| ≤ dist q y := by
      simpa [dist_eq_norm] using (PiLp.norm_apply_le (q - y) i)
    exact le_trans hgap_le_abs hcoord
  exact le_antisymm hupper hlower

/-- Helper for Theorem 3.50: if two current boxes share the same exposed lower face in one
coordinate and the query stays inside both boxes elsewhere, then their scaled distance objectives
agree by rewriting to the same lower-face gap. -/
private theorem sharedLowerFaceGap_eq_scaledInfDist_of_currentBoxes
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      state₁.currentLower (R : ℝ) hn i =
        state₂.currentLower (R : ℝ) hn i)
    (hqi : q i ≤ state₁.currentLower (R : ℝ) hn i)
    (hinside₁ :
      ∀ j : Fin n, j ≠ i →
        state₁.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₁.currentUpper (R : ℝ) hn j)
    (hinside₂ :
      ∀ j : Fin n, j ≠ i →
        state₂.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₂.currentUpper (R : ℝ) hn j) :
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
  have hqi₂ : q i ≤ state₂.currentLower (R : ℝ) hn i := by
    simpa [hface] using hqi
  -- Normalize both distance terms to the same lower-face gap before comparing them.
  calc
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
        (M : ℝ) * (state₁.currentLower (R : ℝ) hn i - q i) := by
          rw [infDist_eq_lowerFaceGap_of_currentBox R hn state₁ hqi hinside₁]
    _ = (M : ℝ) * (state₂.currentLower (R : ℝ) hn i - q i) := by
          rw [hface]
    _ = (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
          rw [infDist_eq_lowerFaceGap_of_currentBox R hn state₂ hqi₂ hinside₂]

/-- Helper for Theorem 3.50: if two current boxes share the same exposed upper face in one
coordinate and the query stays inside both boxes elsewhere, then their scaled distance objectives
agree by rewriting to the same upper-face gap. -/
private theorem sharedUpperFaceGap_eq_scaledInfDist_of_currentBoxes
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      state₁.currentUpper (R : ℝ) hn i =
        state₂.currentUpper (R : ℝ) hn i)
    (hqi : state₁.currentUpper (R : ℝ) hn i ≤ q i)
    (hinside₁ :
      ∀ j : Fin n, j ≠ i →
        state₁.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₁.currentUpper (R : ℝ) hn j)
    (hinside₂ :
      ∀ j : Fin n, j ≠ i →
        state₂.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₂.currentUpper (R : ℝ) hn j) :
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
  have hqi₂ : state₂.currentUpper (R : ℝ) hn i ≤ q i := by
    simpa [hface] using hqi
  -- The upper-face formulas reduce both sides to the same shared gap as well.
  calc
    (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
        (M : ℝ) * (q i - state₁.currentUpper (R : ℝ) hn i) := by
          rw [infDist_eq_upperFaceGap_of_currentBox R hn state₁ hqi hinside₁]
    _ = (M : ℝ) * (q i - state₂.currentUpper (R : ℝ) hn i) := by
          rw [hface]
    _ = (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) := by
          rw [infDist_eq_upperFaceGap_of_currentBox R hn state₂ hqi₂ hinside₂]

/-- Helper for Theorem 3.50: if a child current box preserves a recorded lower boundary face of
its parent and still contains the query on all other coordinates, then the scaled distance value at
that query is unchanged. -/
private theorem scaledInfDist_eq_of_preservedLowerBoundaryFace
    (R M : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      child.currentLower (R : ℝ) hn i =
        parent.currentLower (R : ℝ) hn i)
    (hqi : q i ≤ parent.currentLower (R : ℝ) hn i)
    (hinside_parent :
      ∀ j : Fin n, j ≠ i →
        parent.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ parent.currentUpper (R : ℝ) hn j)
    (hinside_child :
      ∀ j : Fin n, j ≠ i →
        child.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ child.currentUpper (R : ℝ) hn j) :
    (M : ℝ) * Metric.infDist q (child.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (parent.currentBox (R : ℝ) hn) := by
  have hqi_child : q i ≤ child.currentLower (R : ℝ) hn i := by
    simpa [hface] using hqi
  -- Reduce both distances to the same preserved lower-face gap.
  exact
    sharedLowerFaceGap_eq_scaledInfDist_of_currentBoxes
      R M hn child parent hface hqi_child hinside_child hinside_parent

/-- Helper for Theorem 3.50: if a child current box preserves a recorded upper boundary face of
its parent and still contains the query on all other coordinates, then the scaled distance value at
that query is unchanged. -/
private theorem scaledInfDist_eq_of_preservedUpperBoundaryFace
    (R M : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      child.currentUpper (R : ℝ) hn i =
        parent.currentUpper (R : ℝ) hn i)
    (hqi : parent.currentUpper (R : ℝ) hn i ≤ q i)
    (hinside_parent :
      ∀ j : Fin n, j ≠ i →
        parent.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ parent.currentUpper (R : ℝ) hn j)
    (hinside_child :
      ∀ j : Fin n, j ≠ i →
        child.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ child.currentUpper (R : ℝ) hn j) :
    (M : ℝ) * Metric.infDist q (child.currentBox (R : ℝ) hn) =
      (M : ℝ) * Metric.infDist q (parent.currentBox (R : ℝ) hn) := by
  have hqi_child : child.currentUpper (R : ℝ) hn i ≤ q i := by
    simpa [hface] using hqi
  -- The same normalization works for an exposed upper face.
  exact
    sharedUpperFaceGap_eq_scaledInfDist_of_currentBoxes
      R M hn child parent hface hqi_child hinside_child hinside_parent

/-- Helper for Theorem 3.50: if two current boxes share an exposed lower face for the same query,
then that shared face gap produces one common scaled distance value. -/
private theorem commonLowerFaceStepValue_of_currentBoxes
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      state₁.currentLower (R : ℝ) hn i =
        state₂.currentLower (R : ℝ) hn i)
    (hqi : q i ≤ state₁.currentLower (R : ℝ) hn i)
    (hinside₁ :
      ∀ j : Fin n, j ≠ i →
        state₁.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₁.currentUpper (R : ℝ) hn j)
    (hinside₂ :
      ∀ j : Fin n, j ≠ i →
        state₂.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₂.currentUpper (R : ℝ) hn j) :
    ∃ v,
      (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v ∧
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
  refine ⟨(M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn), rfl, ?_⟩
  -- Rewrite the second distance to the same lower-face gap value.
  symm
  exact
    sharedLowerFaceGap_eq_scaledInfDist_of_currentBoxes
      R M hn state₁ state₂ hface hqi hinside₁ hinside₂

/-- Helper for Theorem 3.50: if two current boxes share an exposed upper face for the same query,
then that shared face gap produces one common scaled distance value. -/
private theorem commonUpperFaceStepValue_of_currentBoxes
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hface :
      state₁.currentUpper (R : ℝ) hn i =
        state₂.currentUpper (R : ℝ) hn i)
    (hqi : state₁.currentUpper (R : ℝ) hn i ≤ q i)
    (hinside₁ :
      ∀ j : Fin n, j ≠ i →
        state₁.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₁.currentUpper (R : ℝ) hn j)
    (hinside₂ :
      ∀ j : Fin n, j ≠ i →
        state₂.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state₂.currentUpper (R : ℝ) hn j) :
    ∃ v,
      (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v ∧
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
  refine ⟨(M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn), rfl, ?_⟩
  -- The upper-face formulas give the same common value.
  symm
  exact
    sharedUpperFaceGap_eq_scaledInfDist_of_currentBoxes
      R M hn state₁ state₂ hface hqi hinside₁ hinside₂

/-- Helper for Theorem 3.50: a shared lower-or-upper boundary witness packages the one-step common
value needed by the transcript construction. -/
private theorem commonStepValue_of_boundaryWitness
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {i : Fin n}
    (hboundary :
      (state₁.currentLower (R : ℝ) hn i = state₂.currentLower (R : ℝ) hn i ∧
        q i ≤ state₁.currentLower (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j)) ∨
      (state₁.currentUpper (R : ℝ) hn i = state₂.currentUpper (R : ℝ) hn i ∧
        state₁.currentUpper (R : ℝ) hn i ≤ q i ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j))) :
    ∃ v,
      (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v ∧
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
  rcases hboundary with
    ⟨hface, hqi, hinside₁, hinside₂⟩ |
    ⟨hface, hqi, hinside₁, hinside₂⟩
  · -- Lower-face witnesses close the step through the lower-gap normalization.
    exact
      commonLowerFaceStepValue_of_currentBoxes
        R M hn state₁ state₂ hface hqi hinside₁ hinside₂
  · -- The upper-face branch is identical after switching to the upper-gap formula.
    exact
      commonUpperFaceStepValue_of_currentBoxes
        R M hn state₁ state₂ hface hqi hinside₁ hinside₂

/-- Helper for Theorem 3.50: the current midpoint lies in the box retained by the lower-half
branch. This is the public-facing witness that midpoint ties survive a closed-box bisection. -/
private theorem currentCenter_mem_keepLowerHalf_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentCenter (R : ℝ) hn ∈
      (FeasibilityResistingOracleState.keepLowerHalf state).currentBox (R : ℝ) hn := by
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn
      (FeasibilityResistingOracleState.keepLowerHalf state),
    currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state]
  intro i
  have hmid_mem := midpoint_currentBounds_mem_interval R hn state i
  rcases state.keepLowerHalf_isMidpointCoordinateBisectionStep (R : ℝ) hn with
    ⟨hlower, hupper⟩ | ⟨hlower, hupper⟩
  · by_cases hi : i = state.nextCoord hn
    · subst hi
      constructor
      · simpa [hlower] using
          (midpoint_currentBounds_mem_interval R hn state (state.nextCoord hn)).1
      · simpa [hupper, Function.update_self]
    · constructor
      · simpa [hlower] using hmid_mem.1
      · simpa [hupper, Function.update, hi] using hmid_mem.2
  · by_cases hi : i = state.nextCoord hn
    · subst hi
      constructor
      · simpa [hlower, Function.update_self]
      · simpa [hupper] using
          (midpoint_currentBounds_mem_interval R hn state (state.nextCoord hn)).2
    · constructor
      · simpa [hlower, Function.update, hi] using hmid_mem.1
      · simpa [hupper] using hmid_mem.2

/-- Helper for Theorem 3.50: the proposed one-step exclusion route fails on midpoint ties, since
querying the current midpoint leaves that point inside the successor box. -/
private theorem currentCenter_mem_resistingSuccessorCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    state.currentCenter (R : ℝ) hn ∈
      (resistingSuccessor R hn state (state.currentCenter (R : ℝ) hn)).currentBox
        (R : ℝ) hn := by
  have hcenter_mem :
      state.currentCenter (R : ℝ) hn ∈ state.currentBox (R : ℝ) hn := by
    -- The midpoint description of the current center places it inside the current coordinate box.
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state,
      currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state]
    intro i
    exact midpoint_currentBounds_mem_interval R hn state i
  have hmid :
      (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤
        (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) := le_rfl
  -- Route correction: the closed-box successor keeps midpoint ties on the retained face.
  rw [resistingSuccessor_eq_keepLowerHalf_of_mem_currentBox R hn state hcenter_mem hmid]
  exact currentCenter_mem_keepLowerHalf_currentBox R hn state

/-- Helper for Theorem 3.50: the strict current box is the open coordinate box cut out by the
realized lower and upper bounds. This is the corrected protection region that excludes midpoint
ties left inside the closed `currentBox`. -/
private def strictCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) : Set E :=
  {x : E | ∀ i : Fin n,
      state.currentLower (R : ℝ) hn i < x i ∧ x i < state.currentUpper (R : ℝ) hn i}

/-- Helper for Theorem 3.50: on the lower-half child, the lower bounds are unchanged. -/
private theorem keepLowerHalf_currentLower_eq
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentLower (R : ℝ) hn =
      state.currentLower (R : ℝ) hn := by
  rfl

/-- Helper for Theorem 3.50: on the lower-half child, the upper bounds are updated only at the
active midpoint coordinate. -/
private theorem keepLowerHalf_currentUpper_eq_update
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepLowerHalf state).currentUpper (R : ℝ) hn =
      Function.update
        (state.currentUpper (R : ℝ) hn)
        (state.nextCoord hn)
        (midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
          (state.nextCoord hn)) := by
  rfl

/-- Helper for Theorem 3.50: on the upper-half child, the lower bounds are updated only at the
active midpoint coordinate. -/
private theorem keepUpperHalf_currentLower_eq_update
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentLower (R : ℝ) hn =
      Function.update
        (state.currentLower (R : ℝ) hn)
        (state.nextCoord hn)
        (midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
          (state.nextCoord hn)) := by
  rfl

/-- Helper for Theorem 3.50: on the upper-half child, the upper bounds are unchanged. -/
private theorem keepUpperHalf_currentUpper_eq
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    (FeasibilityResistingOracleState.keepUpperHalf state).currentUpper (R : ℝ) hn =
      state.currentUpper (R : ℝ) hn := by
  rfl

/-- Helper for Theorem 3.50: a point of the current box that lies on or below the active midpoint
stays inside the lower-half child. This is the containment step needed for later fixed-child
geometry. -/
private theorem mem_keepLowerHalf_currentBox_of_mem_currentBox_of_le_center
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∈ state.currentBox (R : ℝ) hn)
    (hside :
      x (state.nextCoord hn) ≤
        (state.currentCenter (R : ℝ) hn) (state.nextCoord hn)) :
    x ∈ (FeasibilityResistingOracleState.keepLowerHalf state).currentBox (R : ℝ) hn := by
  -- Rewrite both boxes to coordinate intervals and check the active and inactive coordinates
  -- separately.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hx
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn (FeasibilityResistingOracleState.keepLowerHalf state)]
  intro i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    constructor
    · simpa [keepLowerHalf_currentLower_eq R hn state] using
        (hx (state.nextCoord hn)).1
    · have hmid :
          x (state.nextCoord hn) ≤
            midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) := by
        simpa [currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state] using hside
      simpa [keepLowerHalf_currentUpper_eq_update R hn state, Function.update_self] using hmid
  · constructor
    · simpa [keepLowerHalf_currentLower_eq R hn state] using (hx i).1
    · simpa [keepLowerHalf_currentUpper_eq_update R hn state, Function.update, hi] using (hx i).2

/-- Helper for Theorem 3.50: a point of the current box that lies on or above the active midpoint
stays inside the upper-half child. This is the symmetric containment step for the upper strip
descendant. -/
private theorem mem_keepUpperHalf_currentBox_of_mem_currentBox_of_center_le
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {x : E}
    (hx : x ∈ state.currentBox (R : ℝ) hn)
    (hside :
      (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤
        x (state.nextCoord hn)) :
    x ∈ (FeasibilityResistingOracleState.keepUpperHalf state).currentBox (R : ℝ) hn := by
  -- The upper-half child keeps the same inactive-coordinate bounds and raises only the active
  -- lower bound to the midpoint.
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hx
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn (FeasibilityResistingOracleState.keepUpperHalf state)]
  intro i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    constructor
    · have hmid :
          midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) ≤
            x (state.nextCoord hn) := by
        simpa [currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state] using hside
      simpa [keepUpperHalf_currentLower_eq_update R hn state, Function.update_self] using hmid
    · simpa [keepUpperHalf_currentUpper_eq R hn state] using
        (hx (state.nextCoord hn)).2
  · constructor
    · simpa [keepUpperHalf_currentLower_eq_update R hn state, Function.update, hi] using (hx i).1
    · simpa [keepUpperHalf_currentUpper_eq R hn state] using (hx i).2

/-- Helper for Theorem 3.50: the strict current box is contained in the closed current box. -/
private theorem strictCurrentBox_subset_currentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    strictCurrentBox R hn state ⊆ state.currentBox (R : ℝ) hn := by
  intro x hx
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state]
  intro i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

/-- Helper for Theorem 3.50: a query outside the strict current box exposes a concrete boundary
face witness in some coordinate. -/
private theorem existsBoundaryWitness_of_not_mem_strictCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {q : E}
    (hq : q ∉ strictCurrentBox R hn state) :
    ∃ i : Fin n,
      q i ≤ state.currentLower (R : ℝ) hn i ∨
        state.currentUpper (R : ℝ) hn i ≤ q i := by
  classical
  by_contra hno
  apply hq
  intro i
  have hi :
      ¬ (q i ≤ state.currentLower (R : ℝ) hn i ∨
          state.currentUpper (R : ℝ) hn i ≤ q i) := by
    intro hface
    exact hno ⟨i, hface⟩
  constructor
  · -- If the lower-face alternative is impossible, `q` lies strictly above the lower bound.
    exact lt_of_not_ge (fun hle ↦ hi (Or.inl hle))
  · -- If the upper-face alternative is impossible, `q` lies strictly below the upper bound.
    exact lt_of_not_ge (fun hge ↦ hi (Or.inr hge))

/-- Helper for Theorem 3.50: if a query lies in the closed current box but not in the strict one,
then some coordinate hits a boundary face while every other coordinate remains inside the same
closed bounds. -/
private theorem existsBoundaryWitness_with_otherCoordsInside_of_mem_currentBox_not_mem_strictCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) {q : E}
    (hq_box : q ∈ state.currentBox (R : ℝ) hn)
    (hq_strict : q ∉ strictCurrentBox R hn state) :
    ∃ i : Fin n,
      (q i ≤ state.currentLower (R : ℝ) hn i ∨
        state.currentUpper (R : ℝ) hn i ≤ q i) ∧
      ∀ j : Fin n, j ≠ i →
        state.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state.currentUpper (R : ℝ) hn j := by
  obtain ⟨i, hface⟩ :=
    existsBoundaryWitness_of_not_mem_strictCurrentBox R hn state hq_strict
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hq_box
  refine ⟨i, hface, ?_⟩
  intro j hj
  -- Once the exposed coordinate is chosen, the closed-box membership keeps every other coordinate
  -- inside the matching bounds needed by the face-gap formulas.
  exact hq_box j

/-- Helper for Theorem 3.50: the lower-half successor's strict box still lies in the parent's
strict box. -/
private theorem keepLowerHalf_strictCurrentBox_subset_strictCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    strictCurrentBox R hn (FeasibilityResistingOracleState.keepLowerHalf state) ⊆
      strictCurrentBox R hn state := by
  intro x hx i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    constructor
    · -- The lower bound is unchanged on the retained lower-half child.
      simpa [keepLowerHalf_currentLower_eq R hn state] using
        (hx (state.nextCoord hn)).1
    · -- The child midpoint upper bound still lies below the parent's upper bound.
      have hupper_mid :
          x (state.nextCoord hn) <
            midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) := by
        simpa [keepLowerHalf_currentUpper_eq_update R hn state, Function.update_self] using
          (hx (state.nextCoord hn)).2
      exact lt_of_lt_of_le hupper_mid
        (midpoint_currentBounds_mem_interval R hn state (state.nextCoord hn)).2
  · constructor
    · -- Away from the active coordinate, the child bounds are unchanged.
      simpa [keepLowerHalf_currentLower_eq R hn state] using
        (hx i).1
    · -- The same unchanged-coordinate argument handles the upper bounds.
      simpa [keepLowerHalf_currentUpper_eq_update R hn state, Function.update, hi] using
        (hx i).2

/-- Helper for Theorem 3.50: the upper-half successor's strict box still lies in the parent's
strict box. -/
private theorem keepUpperHalf_strictCurrentBox_subset_strictCurrentBox
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) :
    strictCurrentBox R hn (FeasibilityResistingOracleState.keepUpperHalf state) ⊆
      strictCurrentBox R hn state := by
  intro x hx i
  by_cases hi : i = state.nextCoord hn
  · subst hi
    constructor
    · -- The child midpoint lower bound still lies above the parent's lower bound.
      have hmid_lower :
          midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) <
            x (state.nextCoord hn) := by
        simpa [keepUpperHalf_currentLower_eq_update R hn state, Function.update_self] using
          (hx (state.nextCoord hn)).1
      exact lt_of_le_of_lt
        (midpoint_currentBounds_mem_interval R hn state (state.nextCoord hn)).1
        hmid_lower
    · -- The upper bound is unchanged on the retained upper-half child.
      simpa [keepUpperHalf_currentUpper_eq R hn state] using
        (hx (state.nextCoord hn)).2
  · constructor
    · -- Away from the active coordinate, the lower bounds are unchanged.
      simpa [keepUpperHalf_currentLower_eq_update R hn state, Function.update, hi] using
        (hx i).1
    · -- And so are the upper bounds.
      simpa [keepUpperHalf_currentUpper_eq R hn state] using
        (hx i).2

/-- Helper for Theorem 3.50: each queried point lies outside the strict/open successor box cut out
by the realized midpoint update. This is the corrected one-step exclusion statement. -/
private theorem query_not_mem_strictCurrentBox_of_resistingSuccessor
    (R : NNReal) (hn : 0 < n) (state : FeasibilityResistingOracleState n) (x : E) :
    x ∉ strictCurrentBox R hn (resistingSuccessor R hn state x) := by
  by_cases hx : x ∈ state.currentBox (R : ℝ) hn
  · by_cases hmid :
      (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤ x (state.nextCoord hn)
    · rw [resistingSuccessor_eq_keepLowerHalf_of_mem_currentBox R hn state hx hmid]
      intro hxstrict
      -- On the retained lower-half child, the query cannot satisfy the strict upper bound.
      have hupper_mid :
          x (state.nextCoord hn) <
            midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) := by
        simpa [keepLowerHalf_currentUpper_eq_update R hn state, Function.update_self] using
          (hxstrict (state.nextCoord hn)).2
      have hmid' :
          midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) ≤
            x (state.nextCoord hn) := by
        simpa [currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state] using hmid
      exact (not_lt_of_ge hmid') hupper_mid
    · have hlt :
        x (state.nextCoord hn) <
          (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) := lt_of_not_ge hmid
      rw [resistingSuccessor_eq_keepUpperHalf_of_mem_currentBox R hn state hx hlt]
      intro hxstrict
      -- On the retained upper-half child, the query cannot satisfy the strict lower bound.
      have hmid_lower :
          midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) <
            x (state.nextCoord hn) := by
        simpa [keepUpperHalf_currentLower_eq_update R hn state, Function.update_self] using
          (hxstrict (state.nextCoord hn)).1
      have hmid' :
          x (state.nextCoord hn) <
            midpoint ℝ (state.currentLower (R : ℝ) hn) (state.currentUpper (R : ℝ) hn)
              (state.nextCoord hn) := by
        simpa [currentCenter_eq_midpoint_currentBounds (R : ℝ) hn state] using hlt
      exact (not_lt_of_ge hmid'.le) hmid_lower
  · rw [resistingSuccessor_eq_self_of_not_mem_currentBox R hn state hx]
    intro hxstrict
    -- Outside the closed box, the query is automatically outside the stricter open box.
    exact hx (strictCurrentBox_subset_currentBox R hn state hxstrict)

/-- Helper for Theorem 3.50: if a query already lies outside the strict current box, then its
coordinatewise projection to the closed current box lands on an exposed boundary face while every
other coordinate stays inside the same bounds. -/
private theorem projectedBoundaryWitnessOfQuery
    (R : NNReal) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) {q : E}
    (hq_strict : q ∉ strictCurrentBox R hn state) :
    ∃ i : Fin n,
      ((currentBoxProjection R hn state q) i ≤ state.currentLower (R : ℝ) hn i ∨
        state.currentUpper (R : ℝ) hn i ≤ (currentBoxProjection R hn state q) i) ∧
      ∀ j : Fin n, j ≠ i →
        state.currentLower (R : ℝ) hn j ≤ (currentBoxProjection R hn state q) j ∧
          (currentBoxProjection R hn state q) j ≤ state.currentUpper (R : ℝ) hn j := by
  obtain ⟨i, hface⟩ :=
    existsBoundaryWitness_of_not_mem_strictCurrentBox R hn state hq_strict
  refine ⟨i, ?_, ?_⟩
  · -- Clamp the exposed coordinate to the corresponding closed-box face.
    rcases hface with hlow | hupp
    · left
      simp [currentBoxProjection, hlow]
    · by_cases hlow : q i ≤ state.currentLower (R : ℝ) hn i
      · left
        simpa [currentBoxProjection, hlow] using hlow
      · right
        simp [currentBoxProjection, hlow, hupp]
  · -- The projection theorem already keeps every coordinate inside the same box.
    have hproj_mem := currentBoxProjection_mem_currentBox R hn state q
    rw [currentBox_eq_currentBounds_set (R : ℝ) hn state] at hproj_mem
    intro j _
    exact hproj_mem j

/-- Helper for Theorem 3.50: projecting the next query onto the source-faithful successor box
produces the concrete boundary witness needed by the boundary-face common-step API. -/
private theorem projectedBoundaryWitnessOfResistingSuccessorQuery
    (R : NNReal) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) (q : E) :
    ∃ i : Fin n,
      ((currentBoxProjection R hn (resistingSuccessor R hn state q) q) i ≤
          (resistingSuccessor R hn state q).currentLower (R : ℝ) hn i ∨
        (resistingSuccessor R hn state q).currentUpper (R : ℝ) hn i ≤
          (currentBoxProjection R hn (resistingSuccessor R hn state q) q) i) ∧
      ∀ j : Fin n, j ≠ i →
        (resistingSuccessor R hn state q).currentLower (R : ℝ) hn j ≤
            (currentBoxProjection R hn (resistingSuccessor R hn state q) q) j ∧
          (currentBoxProjection R hn (resistingSuccessor R hn state q) q) j ≤
            (resistingSuccessor R hn state q).currentUpper (R : ℝ) hn j := by
  -- The one-step exclusion lemma supplies exactly the strict-box hypothesis needed above.
  exact
    projectedBoundaryWitnessOfQuery
      R hn (resistingSuccessor R hn state q)
      (q := q)
      (query_not_mem_strictCurrentBox_of_resistingSuccessor R hn state q)

/-- Helper for Theorem 3.50: any query outside the strict box can be normalized to its
closed-box projection, which already lies on one boundary face, keeps all other coordinates inside
the same closed bounds, and realizes the exact scaled distance to the box. -/
private theorem normalizedBoundaryProjectionOfQueryOutsideStrictCurrentBox
    (R M : NNReal) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) {q : E}
    (hq_strict : q ∉ strictCurrentBox R hn state) :
    ∃ p : E,
      p ∈ state.currentBox (R : ℝ) hn ∧
      (M : ℝ) * dist q p = (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) ∧
      ∃ i : Fin n,
        ((p i ≤ state.currentLower (R : ℝ) hn i ∨
            state.currentUpper (R : ℝ) hn i ≤ p i) ∧
          ∀ j : Fin n, j ≠ i →
            state.currentLower (R : ℝ) hn j ≤ p j ∧
              p j ≤ state.currentUpper (R : ℝ) hn j) := by
  refine ⟨currentBoxProjection R hn state q, ?_, ?_, ?_⟩
  · -- The canonical projection already lands back in the closed current box.
    exact currentBoxProjection_mem_currentBox R hn state q
  · -- The projection theorem identifies the exact distance-to-box value.
    rw [infDist_eq_dist_currentBoxProjection R hn state q]
  · -- The same projection point hits one boundary face and stays inside everywhere else.
    exact projectedBoundaryWitnessOfQuery R hn state (q := q) hq_strict

/-- Helper for Theorem 3.50: later resisting-prefix strict boxes only refine earlier ones, so the
strict/open protection regions are antitone in time. -/
private theorem strictCurrentBox_antitone_along_resistingPrefix
    (R : NNReal) (hn : 0 < n)
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    ∀ {s t : ℕ}, s ≤ t →
      strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle t) ⊆
        strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle s)
  | s, 0, hst => by
      -- At time `0`, only the initial strict box is present.
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst hs
      intro x hx
      exact hx
  | s, t + 1, hst => by
      by_cases hs : s = t + 1
      · -- The endpoint case is the identity inclusion.
        subst hs
        intro x hx
        exact hx
      · have hle : s ≤ t := Nat.le_of_lt_succ (lt_of_le_of_ne hst hs)
        have hstep :
            strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle (t + 1)) ⊆
              strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle t) := by
          let state := resistingPrefixState R hn algorithm oracle t
          let query := algorithm.queryAfter oracle t
          -- One resisting update either keeps the same strict box or chooses one midpoint descendant.
          rw [resistingPrefixState_succ R]
          by_cases hx : query ∈ state.currentBox (R : ℝ) hn
          · by_cases hmid :
              (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤
                query (state.nextCoord hn)
            · simpa [state, query,
                resistingSuccessor_eq_keepLowerHalf_of_mem_currentBox R hn state hx hmid] using
                keepLowerHalf_strictCurrentBox_subset_strictCurrentBox R hn state
            · have hlt :
                query (state.nextCoord hn) <
                  (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) :=
                lt_of_not_ge hmid
              simpa [state, query,
                resistingSuccessor_eq_keepUpperHalf_of_mem_currentBox R hn state hx hlt] using
                keepUpperHalf_strictCurrentBox_subset_strictCurrentBox R hn state
          · simpa [state, query,
              resistingSuccessor_eq_self_of_not_mem_currentBox R hn state hx] using
              (Set.Subset.rfl : strictCurrentBox R hn state ⊆ strictCurrentBox R hn state)
        -- Compose the one-step refinement with the inductive prefix refinement.
        exact Set.Subset.trans hstep
          (strictCurrentBox_antitone_along_resistingPrefix R hn algorithm oracle hle)

/-- Helper for Theorem 3.50: every realized query lies outside the final strict/open protection
region attached to the same resisting-prefix path. -/
private theorem queryAfter_not_mem_final_strictCurrentBox_of_lt
    (R : NNReal) (hn : 0 < n)
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ)
    {j T : ℕ} (hj : j < T) :
    algorithm.queryAfter oracle j ∉
      strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle T) := by
  have hstep :
      algorithm.queryAfter oracle j ∉
        strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle (j + 1)) := by
    simpa [resistingPrefixState_succ R] using
      query_not_mem_strictCurrentBox_of_resistingSuccessor R hn
        (resistingPrefixState R hn algorithm oracle j)
        (algorithm.queryAfter oracle j)
  intro hxfinal
  have hsubset :
      strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle T) ⊆
        strictCurrentBox R hn (resistingPrefixState R hn algorithm oracle (j + 1)) :=
    strictCurrentBox_antitone_along_resistingPrefix R hn algorithm oracle
      (Nat.succ_le_of_lt hj)
  exact hstep (hsubset hxfinal)

/-- Helper for Theorem 3.50: every realized query before time `T` admits a concrete boundary-face
witness in the final strict current box. -/
private theorem existsBoundaryWitness_for_queryAfter_of_lt
    (R : NNReal) (hn : 0 < n)
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ)
    {j T : ℕ} (hj : j < T) :
    ∃ i : Fin n,
      algorithm.queryAfter oracle j i ≤
          (resistingPrefixState R hn algorithm oracle T).currentLower (R : ℝ) hn i ∨
        (resistingPrefixState R hn algorithm oracle T).currentUpper (R : ℝ) hn i ≤
          algorithm.queryAfter oracle j i := by
  -- Combine the final strict-box exclusion with the coordinate witness extraction.
  exact
    existsBoundaryWitness_of_not_mem_strictCurrentBox
      R hn (resistingPrefixState R hn algorithm oracle T)
      (queryAfter_not_mem_final_strictCurrentBox_of_lt R hn algorithm oracle hj)

/-- Helper for Theorem 3.50: later resisting-prefix states only refine the current uncertainty
box, so the realized boxes are antitone in the time index. -/
private theorem resistingPrefixCurrentBoxAntitone
    (R : NNReal) (hn : 0 < n)
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    ∀ {s t : ℕ}, s ≤ t →
      (resistingPrefixState R hn algorithm oracle t).currentBox (R : ℝ) hn ⊆
        (resistingPrefixState R hn algorithm oracle s).currentBox (R : ℝ) hn
  | s, 0, hst => by
      -- At time `0`, only the initial box is present.
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst hs
      intro x hx
      exact hx
  | s, t + 1, hst => by
      by_cases hs : s = t + 1
      · -- The endpoint case is the identity inclusion.
        subst hs
        intro x hx
        exact hx
      · have hle : s ≤ t := Nat.le_of_lt_succ (lt_of_le_of_ne hst hs)
        have hstep :
            (resistingPrefixState R hn algorithm oracle (t + 1)).currentBox (R : ℝ) hn ⊆
              (resistingPrefixState R hn algorithm oracle t).currentBox (R : ℝ) hn := by
          let state := resistingPrefixState R hn algorithm oracle t
          let query := algorithm.queryAfter oracle t
          -- One resisting update either keeps the same box or chooses one midpoint descendant.
          rw [resistingPrefixState_succ R]
          by_cases hx : query ∈ state.currentBox (R : ℝ) hn
          · by_cases hmid :
              (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) ≤
                query (state.nextCoord hn)
            · simpa [state, query,
                resistingSuccessor_eq_keepLowerHalf_of_mem_currentBox R hn state hx hmid] using
                keepLowerHalf_currentBox_subset_currentBox R hn state
            · have hlt :
                query (state.nextCoord hn) <
                  (state.currentCenter (R : ℝ) hn) (state.nextCoord hn) :=
                lt_of_not_ge hmid
              simpa [state, query,
                resistingSuccessor_eq_keepUpperHalf_of_mem_currentBox R hn state hx hlt] using
                keepUpperHalf_currentBox_subset_currentBox R hn state
          · simpa [state, query,
              resistingSuccessor_eq_self_of_not_mem_currentBox R hn state hx] using
              (Set.Subset.rfl : state.currentBox (R : ℝ) hn ⊆ state.currentBox (R : ℝ) hn)
        -- Compose the one-step refinement with the inductive prefix refinement.
        exact Set.Subset.trans hstep
          (resistingPrefixCurrentBoxAntitone R hn algorithm oracle hle)

/-- Helper for Theorem 3.50: the common resisting-prefix state after `T` queries still contains
the Euclidean closed ball of textbook radius `(R / 2) * (1 / 2)^(T / n)`. -/
private theorem commonPrefixClosedBallSubset_currentBox
    {T : ℕ} (R : NNReal)
    (hn : 0 < n) (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ) :
    Metric.closedBall
        ((resistingPrefixState R hn algorithm oracle T).currentCenter (R : ℝ) hn)
        ((R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n)) ⊆
      (resistingPrefixState R hn algorithm oracle T).currentBox (R : ℝ) hn := by
  let state := resistingPrefixState R hn algorithm oracle T
  have hdepth : state.depth ≤ T := by
    simpa [state] using resistingPrefixState_depth_le R hn algorithm oracle T
  have hdepth_div :
      ((state.depth : ℝ) / n) ≤ ((T : ℝ) / n) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hdepth) (by positivity : 0 ≤ (n : ℝ))
  have hrpow :
      Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n) ≤
        Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) := by
    refine Real.rpow_le_rpow_of_exponent_ge' ?_ ?_ ?_ hdepth_div
    · norm_num
    · norm_num
    · positivity
  have hrad :
      (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n) ≤
        (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((state.depth : ℝ) / n) := by
    exact mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (R : ℝ) / 2)
  -- Compare the requested radius with the inradius already supplied by Lemma 3.2.4.
  exact Set.Subset.trans
    (Metric.closedBall_subset_closedBall hrad)
    (FeasibilityResistingOracleState.closedBall_subset_currentBox (R : ℝ) hn state)

/-- Helper for Theorem 3.50: a large enough common Euclidean ball inside the current uncertainty
box contains two disjoint sibling closed balls that remain feasible in `B∞(0, R)`. -/
private theorem existsSeparatedSiblingClosedBallsInCurrentBox
    {R : NNReal} {ρ δ : ℝ}
    (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hball :
      Metric.closedBall (state.currentCenter (R : ℝ) hn) ρ ⊆ state.currentBox (R : ℝ) hn)
    (hroom : 4 * δ < ρ) :
    ∃ K₁ K₂ : Set E,
      K₁.Nonempty ∧
      IsClosed K₁ ∧
      Convex ℝ K₁ ∧
      K₁ ⊆ linftyClosedBall R ∧
      K₂.Nonempty ∧
      IsClosed K₂ ∧
      Convex ℝ K₂ ∧
      K₂ ⊆ linftyClosedBall R ∧
      (∀ u ∈ K₁, ∀ v ∈ K₂, 2 * δ < dist u v) := by
  let center := state.currentCenter (R : ℝ) hn
  let direction : E := EuclideanSpace.single (state.nextCoord hn) (1 : ℝ)
  let c₁ : E := center - (3 * δ) • direction
  let c₂ : E := center + (3 * δ) • direction
  let K₁ : Set E := Metric.closedBall c₁ δ
  let K₂ : Set E := Metric.closedBall c₂ δ
  have hdir_norm : ‖direction‖ = 1 := by
    simp [direction, EuclideanSpace.single]
  have hc₁_center : dist c₁ center = 3 * δ := by
    -- The first center is shifted by exactly `3δ` along a unit coordinate direction.
    rw [dist_eq_norm]
    calc
      ‖c₁ - center‖ = ‖-(((3 * δ : ℝ)) • direction)‖ := by
        congr 1
        simp [c₁]
      _ = ‖(3 * δ : ℝ) • direction‖ := by rw [norm_neg]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have hc₂_center : dist c₂ center = 3 * δ := by
    -- The second center is the symmetric shift on the opposite side.
    rw [dist_eq_norm]
    calc
      ‖c₂ - center‖ = ‖(3 * δ : ℝ) • direction‖ := by
        congr 1
        simp [c₂]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have hcenters : dist c₁ c₂ = 6 * δ := by
    -- The two centers are separated by `6δ` along the same unit direction.
    have hc₁₂ : c₁ - c₂ = -(((6 * δ : ℝ)) • direction) := by
      ext k
      by_cases hk : k = state.nextCoord hn
      · subst hk
        simp [c₁, c₂, direction, EuclideanSpace.single, sub_eq_add_neg]
        ring
      · simp [c₁, c₂, direction, EuclideanSpace.single, sub_eq_add_neg, hk]
    rw [dist_eq_norm]
    calc
      ‖c₁ - c₂‖ = ‖-(((6 * δ : ℝ)) • direction)‖ := by rw [hc₁₂]
      _ = ‖((6 * δ : ℝ)) • direction‖ := by rw [norm_neg]
      _ = |6 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 6 * δ := by simp [hdir_norm, hδ.le]
  have hK₁_subset_box : K₁ ⊆ state.currentBox (R : ℝ) hn := by
    intro x hx
    have hdist : dist x center < ρ := by
      have hxδ : dist x c₁ ≤ δ := by simpa [K₁, Metric.mem_closedBall] using hx
      calc
        dist x center ≤ dist x c₁ + dist c₁ center := dist_triangle _ _ _
        _ ≤ δ + 3 * δ := by
          nlinarith [hxδ, hc₁_center]
        _ < ρ := by nlinarith [hroom]
    exact hball <| by
      exact Metric.mem_closedBall.mpr (le_of_lt hdist)
  have hK₂_subset_box : K₂ ⊆ state.currentBox (R : ℝ) hn := by
    intro x hx
    have hdist : dist x center < ρ := by
      have hxδ : dist x c₂ ≤ δ := by simpa [K₂, Metric.mem_closedBall] using hx
      calc
        dist x center ≤ dist x c₂ + dist c₂ center := dist_triangle _ _ _
        _ ≤ δ + 3 * δ := by
          nlinarith [hxδ, hc₂_center]
        _ < ρ := by nlinarith [hroom]
    exact hball <| by
      exact Metric.mem_closedBall.mpr (le_of_lt hdist)
  have hstate_subset : state.currentBox (R : ℝ) hn ⊆ linftyClosedBall R :=
    currentBox_subset_linftyClosedBall R hn state
  refine ⟨K₁, K₂, ?_, Metric.isClosed_closedBall, convex_closedBall _ _, ?_,
    ?_, Metric.isClosed_closedBall, convex_closedBall _ _, ?_, ?_⟩
  · -- Each closed ball contains its own center.
    exact ⟨c₁, Metric.mem_closedBall_self hδ.le⟩
  · -- Feasibility follows from the current-box containment already proved.
    exact Set.Subset.trans hK₁_subset_box hstate_subset
  · -- The second sibling ball is nonempty for the same reason.
    exact ⟨c₂, Metric.mem_closedBall_self hδ.le⟩
  · -- And it stays feasible inside the ambient `ℓ∞` ball as well.
    exact Set.Subset.trans hK₂_subset_box hstate_subset
  · intro u hu v hv
    have huδ : dist u c₁ ≤ δ := by simpa [K₁, Metric.mem_closedBall] using hu
    have hvδ : dist v c₂ ≤ δ := by simpa [K₂, Metric.mem_closedBall] using hv
    have htri₁ : dist c₁ c₂ ≤ dist c₁ u + dist u c₂ := dist_triangle _ _ _
    have htri₂ : dist u c₂ ≤ dist u v + dist v c₂ := dist_triangle _ _ _
    have huc₂ : dist u c₂ ≤ dist u v + δ := by
      nlinarith [htri₂, hvδ]
    have hsum : dist c₁ c₂ ≤ δ + (dist u v + δ) := by
      have huδ' : dist c₁ u ≤ δ := by simpa [dist_comm] using huδ
      have hstep : dist c₁ u + dist u c₂ ≤ δ + (dist u v + δ) :=
        add_le_add huδ' huc₂
      exact le_trans htri₁ hstep
    have huv : 4 * δ ≤ dist u v := by
      rw [hcenters] at hsum
      nlinarith
    -- The `6δ` center separation leaves a gap of more than `2δ` between the sibling balls.
    have htwo_lt_four : 2 * δ < 4 * δ := by nlinarith
    exact lt_of_lt_of_le htwo_lt_four huv

/-- Helper for Theorem 3.50: the same sibling-ball construction can be kept in the stronger
normal form needed by the repaired successor route, namely with each sibling neighborhood still
explicitly contained in the current uncertainty box. -/
private theorem existsSeparatedSiblingClosedBallsRefiningCurrentBox
    {R : NNReal} {ρ δ : ℝ}
    (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hball :
      Metric.closedBall (state.currentCenter (R : ℝ) hn) ρ ⊆ state.currentBox (R : ℝ) hn)
    (hroom : 4 * δ < ρ) :
    ∃ K₁ K₂ : Set E,
      K₁.Nonempty ∧
      IsClosed K₁ ∧
      Convex ℝ K₁ ∧
      K₁ ⊆ state.currentBox (R : ℝ) hn ∧
      K₂.Nonempty ∧
      IsClosed K₂ ∧
      Convex ℝ K₂ ∧
      K₂ ⊆ state.currentBox (R : ℝ) hn ∧
      (∀ u ∈ K₁, ∀ v ∈ K₂, 2 * δ < dist u v) := by
  let center := state.currentCenter (R : ℝ) hn
  let direction : E := EuclideanSpace.single (state.nextCoord hn) (1 : ℝ)
  let c₁ : E := center - (3 * δ) • direction
  let c₂ : E := center + (3 * δ) • direction
  let K₁ : Set E := Metric.closedBall c₁ δ
  let K₂ : Set E := Metric.closedBall c₂ δ
  have hdir_norm : ‖direction‖ = 1 := by
    simp [direction, EuclideanSpace.single]
  have hc₁_center : dist c₁ center = 3 * δ := by
    -- The first center is shifted by exactly `3δ` along a unit coordinate direction.
    rw [dist_eq_norm]
    calc
      ‖c₁ - center‖ = ‖-(((3 * δ : ℝ)) • direction)‖ := by
        congr 1
        simp [c₁]
      _ = ‖(3 * δ : ℝ) • direction‖ := by rw [norm_neg]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have hc₂_center : dist c₂ center = 3 * δ := by
    -- The second center is the symmetric shift on the opposite side.
    rw [dist_eq_norm]
    calc
      ‖c₂ - center‖ = ‖(3 * δ : ℝ) • direction‖ := by
        congr 1
        simp [c₂]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have hcenters : dist c₁ c₂ = 6 * δ := by
    -- The two centers are separated by `6δ` along the same unit direction.
    have hc₁₂ : c₁ - c₂ = -(((6 * δ : ℝ)) • direction) := by
      ext k
      by_cases hk : k = state.nextCoord hn
      · subst hk
        simp [c₁, c₂, direction, EuclideanSpace.single, sub_eq_add_neg]
        ring
      · simp [c₁, c₂, direction, EuclideanSpace.single, sub_eq_add_neg, hk]
    rw [dist_eq_norm]
    calc
      ‖c₁ - c₂‖ = ‖-(((6 * δ : ℝ)) • direction)‖ := by rw [hc₁₂]
      _ = ‖((6 * δ : ℝ)) • direction‖ := by rw [norm_neg]
      _ = |6 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 6 * δ := by simp [hdir_norm, hδ.le]
  have hK₁_subset_box : K₁ ⊆ state.currentBox (R : ℝ) hn := by
    intro x hx
    have hdist : dist x center < ρ := by
      have hxδ : dist x c₁ ≤ δ := by simpa [K₁, Metric.mem_closedBall] using hx
      calc
        dist x center ≤ dist x c₁ + dist c₁ center := dist_triangle _ _ _
        _ ≤ δ + 3 * δ := by
          nlinarith [hxδ, hc₁_center]
        _ < ρ := by nlinarith [hroom]
    exact hball <| by
      exact Metric.mem_closedBall.mpr (le_of_lt hdist)
  have hK₂_subset_box : K₂ ⊆ state.currentBox (R : ℝ) hn := by
    intro x hx
    have hdist : dist x center < ρ := by
      have hxδ : dist x c₂ ≤ δ := by simpa [K₂, Metric.mem_closedBall] using hx
      calc
        dist x center ≤ dist x c₂ + dist c₂ center := dist_triangle _ _ _
        _ ≤ δ + 3 * δ := by
          nlinarith [hxδ, hc₂_center]
        _ < ρ := by nlinarith [hroom]
    exact hball <| by
      exact Metric.mem_closedBall.mpr (le_of_lt hdist)
  refine ⟨K₁, K₂, ?_, Metric.isClosed_closedBall, convex_closedBall _ _, hK₁_subset_box,
    ?_, Metric.isClosed_closedBall, convex_closedBall _ _, hK₂_subset_box, ?_⟩
  · -- Each sibling neighborhood contains its own shifted center.
    exact ⟨c₁, Metric.mem_closedBall_self hδ.le⟩
  · -- The second sibling neighborhood is nonempty for the same reason.
    exact ⟨c₂, Metric.mem_closedBall_self hδ.le⟩
  · intro u hu v hv
    have huδ : dist u c₁ ≤ δ := by simpa [K₁, Metric.mem_closedBall] using hu
    have hvδ : dist v c₂ ≤ δ := by simpa [K₂, Metric.mem_closedBall] using hv
    have htri₁ : dist c₁ c₂ ≤ dist c₁ u + dist u c₂ := dist_triangle _ _ _
    have htri₂ : dist u c₂ ≤ dist u v + dist v c₂ := dist_triangle _ _ _
    have huc₂ : dist u c₂ ≤ dist u v + δ := by
      nlinarith [htri₂, hvδ]
    have hsum : dist c₁ c₂ ≤ δ + (dist u v + δ) := by
      have huδ' : dist c₁ u ≤ δ := by simpa [dist_comm] using huδ
      have hstep : dist c₁ u + dist u c₂ ≤ δ + (dist u v + δ) :=
        add_le_add huδ' huc₂
      exact le_trans htri₁ hstep
    have huv : 4 * δ ≤ dist u v := by
      rw [hcenters] at hsum
      nlinarith
    -- The `6δ` center separation leaves a gap of more than `2δ` between the sibling balls.
    have htwo_lt_four : 2 * δ < 4 * δ := by nlinarith
    exact lt_of_lt_of_le htwo_lt_four huv

/-- Helper for Theorem 3.50: a large enough common Euclidean ball inside the current uncertainty
box also contains two separated singleton hard sets on the next-coordinate axis. -/
private theorem existsSeparatedPointHardSetsInCurrentBox
    {R : NNReal} {ρ δ : ℝ}
    (hn : 0 < n) (state : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hball :
      Metric.closedBall (state.currentCenter (R : ℝ) hn) ρ ⊆ state.currentBox (R : ℝ) hn)
    (hroom : 4 * δ < ρ) :
    ∃ K₁ K₂ : Set E,
      K₁.Nonempty ∧
      IsClosed K₁ ∧
      Convex ℝ K₁ ∧
      K₁ ⊆ linftyClosedBall R ∧
      K₂.Nonempty ∧
      IsClosed K₂ ∧
      Convex ℝ K₂ ∧
      K₂ ⊆ linftyClosedBall R ∧
      (∀ u ∈ K₁, ∀ v ∈ K₂, 2 * δ < dist u v) := by
  let center := state.currentCenter (R : ℝ) hn
  let direction : E := EuclideanSpace.single (state.nextCoord hn) (1 : ℝ)
  let u : E := center - (3 * δ) • direction
  let v : E := center + (3 * δ) • direction
  let K₁ : Set E := {u}
  let K₂ : Set E := {v}
  have hdir_norm : ‖direction‖ = 1 := by
    simp [direction, EuclideanSpace.single]
  have hu_center : dist u center = 3 * δ := by
    -- The first hard point is shifted by exactly `3δ` along a unit coordinate direction.
    rw [dist_eq_norm]
    calc
      ‖u - center‖ = ‖-(((3 * δ : ℝ)) • direction)‖ := by
        congr 1
        simp [u]
      _ = ‖((3 * δ : ℝ)) • direction‖ := by rw [norm_neg]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have hv_center : dist v center = 3 * δ := by
    -- The second hard point is the symmetric shift on the opposite side.
    rw [dist_eq_norm]
    calc
      ‖v - center‖ = ‖((3 * δ : ℝ)) • direction‖ := by
        congr 1
        simp [v]
      _ = |3 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 3 * δ := by simp [hdir_norm, hδ.le]
  have huv_dist : dist u v = 6 * δ := by
    -- The two hard points are separated by `6δ` along the same unit axis direction.
    rw [dist_eq_norm]
    calc
      ‖u - v‖ = ‖-(((6 * δ : ℝ)) • direction)‖ := by
        congr 1
        ext i
        by_cases hi : i = state.nextCoord hn
        · subst hi
          simp [u, v, direction, EuclideanSpace.single, sub_eq_add_neg]
          ring
        · simp [u, v, direction, EuclideanSpace.single, sub_eq_add_neg, hi]
      _ = ‖((6 * δ : ℝ)) • direction‖ := by rw [norm_neg]
      _ = |6 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 6 * δ := by simp [hdir_norm, hδ.le]
  have hu_mem_box : u ∈ state.currentBox (R : ℝ) hn := by
    -- The first hard point stays inside the protected radius-`ρ` Euclidean ball.
    refine hball ?_
    rw [Metric.mem_closedBall]
    have hu_lt : 3 * δ < ρ := by nlinarith [hroom]
    exact le_of_lt (hu_center.trans_lt hu_lt)
  have hv_mem_box : v ∈ state.currentBox (R : ℝ) hn := by
    -- The second hard point satisfies the same protected-radius estimate.
    refine hball ?_
    rw [Metric.mem_closedBall]
    have hv_lt : 3 * δ < ρ := by nlinarith [hroom]
    exact le_of_lt (hv_center.trans_lt hv_lt)
  have hstate_subset : state.currentBox (R : ℝ) hn ⊆ linftyClosedBall R :=
    currentBox_subset_linftyClosedBall R hn state
  refine ⟨K₁, K₂, ?_, isClosed_singleton, convex_singleton u, ?_,
    ?_, isClosed_singleton, convex_singleton v, ?_, ?_⟩
  · exact ⟨u, by simp [K₁]⟩
  · intro x hx
    have hx' : x = u := by simpa [K₁] using hx
    simpa [hx'] using hstate_subset hu_mem_box
  · exact ⟨v, by simp [K₂]⟩
  · intro x hx
    have hx' : x = v := by simpa [K₂] using hx
    simpa [hx'] using hstate_subset hv_mem_box
  · intro x hx y hy
    have hx' : x = u := by simpa [K₁] using hx
    have hy' : y = v := by simpa [K₂] using hy
    subst x
    subst y
    have htwo_lt_six : 2 * δ < 6 * δ := by nlinarith [hδ]
    exact lt_of_lt_of_eq htwo_lt_six huv_dist.symm

/-- Helper for Theorem 3.50: a budget below `n * log (M R / (8 ε))` leaves radius room strictly
larger than `4 ε / M` inside the common resisting-prefix Euclidean ball. -/
private theorem shortBudgetRadius_gt_fourEpsOverM
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    4 * ε / (M : ℝ) < (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlog_pos : 0 < Real.log ((M : ℝ) * R / (8 * ε)) := by
    -- The short-budget hypothesis forces the logarithmic ratio itself to be positive.
    have hmul_pos :
        0 < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) := by
      exact lt_of_le_of_lt (by positivity : 0 ≤ (T : ℝ)) hbudget
    nlinarith
  have hratio_gt_one : 1 < (M : ℝ) * R / (8 * ε) := by
    have hratio_nonneg : 0 ≤ (M : ℝ) * R / (8 * ε) := by
      positivity
    exact (Real.log_pos_iff hratio_nonneg).mp hlog_pos
  have hratio_pos : 0 < (M : ℝ) * R / (8 * ε) := by
    linarith
  have hR_pos : 0 < (R : ℝ) := by
    -- Positive ratio and positive `M, ε` force the radius `R` itself to be positive.
    have hMR_pos : 0 < (M : ℝ) * R := by
      exact (div_pos_iff_of_pos_right (by positivity : 0 < 8 * ε)).mp hratio_pos
    nlinarith
  have hdiv :
      (T : ℝ) / n < Real.log ((M : ℝ) * R / (8 * ε)) := by
    exact (div_lt_iff₀ hnR).2 (by simpa [mul_comm] using hbudget)
  have hdiv_log_two :
      ((T : ℝ) / n) * Real.log 2 < Real.log ((M : ℝ) * R / (8 * ε)) := by
    have hlog_two_lt_one : Real.log (2 : ℝ) < 1 := by
      exact Real.log_two_lt_d9.trans (by norm_num)
    have hmul_le_self : ((T : ℝ) / n) * Real.log 2 ≤ (T : ℝ) / n := by
      exact mul_le_of_le_one_right (by positivity : 0 ≤ (T : ℝ) / n) hlog_two_lt_one.le
    exact lt_of_le_of_lt hmul_le_self hdiv
  have hpow_two_lt :
      Real.rpow (2 : ℝ) ((T : ℝ) / n) < (M : ℝ) * R / (8 * ε) := by
    -- Converting the logarithmic budget bound to `2 ^ (T / n) < M R / (8 ε)`.
    exact
      (Real.rpow_lt_iff_lt_log (by norm_num : 0 < (2 : ℝ)) hratio_pos).2 <| by
        simpa [mul_comm] using hdiv_log_two
  have hrecip :
      ((M : ℝ) * R / (8 * ε))⁻¹ < (Real.rpow (2 : ℝ) ((T : ℝ) / n))⁻¹ := by
    simpa [one_div] using
      one_div_lt_one_div_of_lt
        (Real.rpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _)
        hpow_two_lt
  have hscaled :
      4 * ε / (M : ℝ) <
        (R : ℝ) / 2 * (Real.rpow (2 : ℝ) ((T : ℝ) / n))⁻¹ := by
    -- Multiplying the reciprocal inequality by `R / 2` recovers the desired scale.
    have hmul :
        (R : ℝ) / 2 * (((M : ℝ) * R / (8 * ε))⁻¹) <
          (R : ℝ) / 2 * (Real.rpow (2 : ℝ) ((T : ℝ) / n))⁻¹ := by
      exact mul_lt_mul_of_pos_left hrecip (by positivity : 0 < (R : ℝ) / 2)
    calc
      4 * ε / (M : ℝ) = (R : ℝ) / 2 * (((M : ℝ) * R / (8 * ε))⁻¹) := by
        field_simp [hM.ne', hR_pos.ne', hε.ne']
        ring
      _ < (R : ℝ) / 2 * (Real.rpow (2 : ℝ) ((T : ℝ) / n))⁻¹ := hmul
  -- Rewrite the reciprocal power as `(1 / 2) ^ (T / n)` to match the textbook radius.
  simpa [one_div] using
    (show
      4 * ε / (M : ℝ) <
        (R : ℝ) / 2 * (Real.rpow ((2 : ℝ)⁻¹) ((T : ℝ) / n))
      from by
        simpa [Real.inv_rpow (show 0 ≤ (2 : ℝ) by positivity) ((T : ℝ) / n)] using hscaled)

/-- Helper for Theorem 3.50: if two value oracles agree on every previously queried value along
the first oracle path, then the next query point is the same for both oracles. -/
private theorem queryAfter_eq_of_same_query_values
    (algorithm : DeterministicValueOracleMethod E) (oracle₁ oracle₂ : E → ℝ)
    {j : ℕ}
    (hquery :
      ∀ m < j,
        oracle₁ (algorithm.queryAfter oracle₁ m) =
          oracle₂ (algorithm.queryAfter oracle₁ m)) :
    algorithm.queryAfter oracle₁ j = algorithm.queryAfter oracle₂ j := by
  -- The next query depends only on the prefix transcript, so transcript equality synchronizes it.
  have htrans :
      algorithm.oracleTranscript oracle₁ j = algorithm.oracleTranscript oracle₂ j :=
    DeterministicValueOracleMethod.oracleTranscript_eq_of_same_query_values
      algorithm oracle₁ oracle₂ hquery
  simp [DeterministicValueOracleMethod.queryAfter, htrans]

/-- Helper for Theorem 3.50: updating a value oracle at `q` does not change any query up to time
`t` provided every earlier occurrence of `q` already carried the same value `v`. This is the
value-oracle replay step needed for the common-reference prefix construction. -/
private theorem queryAfter_eq_of_update_value_on_prefix
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ)
    {q : E} {v : ℝ} {t j : ℕ}
    (hstable :
      ∀ s < t, algorithm.queryAfter oracle s = q → oracle q = v)
    (hj : j ≤ t) :
    algorithm.queryAfter (Function.update oracle q v) j =
      algorithm.queryAfter oracle j := by
  classical
  have hsync :
      ∀ u : ℕ, u ≤ t →
        algorithm.queryAfter (Function.update oracle q v) u =
          algorithm.queryAfter oracle u := by
    intro u
    refine Nat.strong_induction_on u ?_
    intro u ih hu_le
    -- Synchronize the next query by checking that the `Function.update` leaves every earlier
    -- queried value unchanged on the already-fixed prefix.
    refine queryAfter_eq_of_same_query_values algorithm
      (Function.update oracle q v) oracle ?_
    intro s hs
    have hs_le_t : s ≤ t := Nat.le_trans (Nat.le_of_lt hs) hu_le
    have hquery_eq :
        algorithm.queryAfter (Function.update oracle q v) s =
          algorithm.queryAfter oracle s :=
      ih s hs hs_le_t
    -- Rewriting through the synchronized query reduces the value comparison to a single update
    -- hit-or-miss on `q`.
    rw [hquery_eq]
    by_cases hq : algorithm.queryAfter oracle s = q
    · rw [hq, Function.update_self]
      exact (hstable s (lt_of_lt_of_le hs hu_le) hq).symm
    · simp [Function.update, hq]
  exact hsync j hj

/-- Helper for Theorem 3.50: a fresh `Function.update` at a query point that has not appeared
before time `t` preserves the entire query prefix up to `t`. -/
private theorem queryAfter_eq_of_update_value_on_freshPrefix
    (algorithm : DeterministicValueOracleMethod E) (oracle : E → ℝ)
    {q : E} {v : ℝ} {t j : ℕ}
    (hfresh : ∀ s < t, algorithm.queryAfter oracle s ≠ q)
    (hj : j ≤ t) :
    algorithm.queryAfter (Function.update oracle q v) j =
      algorithm.queryAfter oracle j := by
  -- The general replay lemma applies because a fresh point vacuously satisfies the same-value
  -- condition on the answered prefix.
  refine queryAfter_eq_of_update_value_on_prefix algorithm oracle ?_ hj
  intro s hs hq
  exact False.elim <| hfresh s hs hq

/-- Helper for Theorem 3.50: folding a finite transcript of query-value pairs into a base value
oracle by repeated `Function.update` gives the explicit common-reference oracle used by the final
transcript-matching step. -/
private def referenceOracleOfTranscript
    (oracleBase : E → ℝ) (tr : List (E × ℝ)) : E → ℝ :=
  tr.foldl (fun oracle qv ↦ Function.update oracle qv.1 qv.2) oracleBase

/-- Helper for Theorem 3.50: appending one final query-value pair to a transcript folds to one
more `Function.update` on the already-folded reference oracle. -/
private theorem referenceOracleOfTranscript_append_singleton
    (oracleBase : E → ℝ) (tr : List (E × ℝ)) (qv : E × ℝ) :
    referenceOracleOfTranscript oracleBase (tr ++ [qv]) =
      Function.update (referenceOracleOfTranscript oracleBase tr) qv.1 qv.2 := by
  -- Unfold the transcript fold once at the tail so later induction steps can append one query.
  simp [referenceOracleOfTranscript, List.foldl_append]

/-- Helper for Theorem 3.50: appending one query-value pair to a folded reference transcript does
not change any query up to time `t` when every earlier reoccurrence of that query already carried
the appended value. -/
private theorem queryAfter_eq_of_referenceOracle_append_singleton_prefix
    (algorithm : DeterministicValueOracleMethod E)
    (oracleBase : E → ℝ) (tr : List (E × ℝ))
    {q : E} {v : ℝ} {t j : ℕ}
    (hstable :
      ∀ s < t,
        algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr) s = q →
          referenceOracleOfTranscript oracleBase tr q = v)
    (hj : j ≤ t) :
    algorithm.queryAfter (referenceOracleOfTranscript oracleBase (tr ++ [(q, v)])) j =
      algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr) j := by
  -- Rewrite the appended transcript to one `Function.update`, then use the generic prefix replay
  -- lemma already proved for single query-value updates.
  rw [referenceOracleOfTranscript_append_singleton]
  exact
    queryAfter_eq_of_update_value_on_prefix
      algorithm (referenceOracleOfTranscript oracleBase tr) hstable hj

/-- Helper for Theorem 3.50: once every reference-path query admits a common hard-oracle value
that is stable under repeated occurrences on the answered prefix, the entire reference transcript
can be built by induction. This isolates the remaining work to the geometric step-value lemma. -/
private theorem existsReferenceTranscript_of_commonStepValues
    (algorithm : DeterministicValueOracleMethod E)
    (oracleBase φ₁ φ₂ : E → ℝ) (T : ℕ)
    (hstep :
      ∀ tr : List (E × ℝ), tr.length < T →
        let oracleRef := referenceOracleOfTranscript oracleBase tr
        let q := algorithm.queryAfter oracleRef tr.length
        ∃ v,
          (∀ s (hs : s < tr.length),
            algorithm.queryAfter oracleRef s = q →
              oracleRef q = v) ∧
            φ₁ q = v ∧
            φ₂ q = v) :
    ∃ tr : List (E × ℝ),
      tr.length = T ∧
        (∀ j (hj : j < tr.length),
          algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr) j =
            (tr.get ⟨j, hj⟩).1) ∧
          (∀ j (hj : j < tr.length),
            referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
              (tr.get ⟨j, hj⟩).2) ∧
            (∀ j (hj : j < tr.length),
              φ₁ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2) ∧
            (∀ j (hj : j < tr.length),
              φ₂ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2) := by
  classical
  have hbuild :
      ∀ t : ℕ, t ≤ T →
        ∃ tr : List (E × ℝ),
          tr.length = t ∧
            (∀ j (hj : j < tr.length),
              algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr) j =
                (tr.get ⟨j, hj⟩).1) ∧
              (∀ j (hj : j < tr.length),
                referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
                  (tr.get ⟨j, hj⟩).2) ∧
                (∀ j (hj : j < tr.length),
                  φ₁ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2) ∧
                (∀ j (hj : j < tr.length),
                  φ₂ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2) := by
    intro t
    induction t with
    | zero =>
        intro hT
        refine ⟨[], rfl, ?_, ?_, ?_, ?_⟩
        · intro j hj
          exact False.elim (Nat.not_lt_zero _ hj)
        · intro j hj
          exact False.elim (Nat.not_lt_zero _ hj)
        · intro j hj
          exact False.elim (Nat.not_lt_zero _ hj)
        · intro j hj
          exact False.elim (Nat.not_lt_zero _ hj)
    | succ t iht =>
        intro hT
        have ht_le : t ≤ T := Nat.le_of_succ_le hT
        rcases iht ht_le with
          ⟨tr, htr_len, hquery, href, hφ₁_ref, hφ₂_ref⟩
        have htr_lt : tr.length < T := by
          simpa [htr_len] using Nat.lt_of_succ_le hT
        obtain ⟨v, hstable, hφ₁_q, hφ₂_q⟩ := hstep tr htr_lt
        let oracleRef := referenceOracleOfTranscript oracleBase tr
        let q := algorithm.queryAfter oracleRef tr.length
        let tr' : List (E × ℝ) := tr ++ [(q, v)]
        have hprefix :
            ∀ j : ℕ, j ≤ tr.length →
              algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr') j =
                algorithm.queryAfter oracleRef j := by
          intro j hj
          -- The inductive replay invariant already gives the exact prefix-stability needed for the
          -- appended reference query-value pair.
          exact
            queryAfter_eq_of_referenceOracle_append_singleton_prefix
              algorithm oracleBase tr hstable hj
        refine ⟨tr', by simp [tr', htr_len], ?_, ?_, ?_, ?_⟩
        · intro j hj
          have hj_split : j < tr.length ∨ j = tr.length := by
            have hj' : j < tr.length + 1 := by simpa [tr', htr_len] using hj
            exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj')
          rcases hj_split with hj_old | rfl
          · -- Earlier query points are unchanged because the appended transcript preserves the
            -- whole prefix and the old entries sit on the left side of the append.
            calc
              algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr') j =
                  algorithm.queryAfter oracleRef j :=
                    hprefix j (Nat.le_of_lt hj_old)
              _ = (tr.get ⟨j, hj_old⟩).1 := hquery j hj_old
              _ = (tr'.get ⟨j, hj⟩).1 := by
                    simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
          · -- At the new final index, the query is exactly the freshly appended point.
            calc
              algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr') tr.length =
                  algorithm.queryAfter oracleRef tr.length :=
                    hprefix tr.length le_rfl
              _ = q := by rfl
              _ = (tr'.get ⟨tr.length, hj⟩).1 := by
                    simp [tr', List.get_eq_getElem]
        · intro j hj
          have hj_split : j < tr.length ∨ j = tr.length := by
            have hj' : j < tr.length + 1 := by simpa [tr', htr_len] using hj
            exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj')
          rcases hj_split with hj_old | rfl
          · have hget_old :
                tr'.get ⟨j, hj⟩ = tr.get ⟨j, hj_old⟩ := by
              simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
            rw [hget_old]
            rw [referenceOracleOfTranscript_append_singleton]
            by_cases hsame : (tr.get ⟨j, hj_old⟩).1 = q
            · -- If the appended query repeats an earlier one, the step hypothesis forces the old
              -- stored value to coincide with the new appended value.
              have hquery_old : algorithm.queryAfter oracleRef j = q := by
                rw [hquery j hj_old]
                exact hsame
              have hstored_eq_v : (tr.get ⟨j, hj_old⟩).2 = v := by
                calc
                  (tr.get ⟨j, hj_old⟩).2 =
                      oracleRef ((tr.get ⟨j, hj_old⟩).1) := by
                        symm
                        exact href j hj_old
                  _ = oracleRef q := by rw [hsame]
                  _ = v := hstable j hj_old hquery_old
              have hsame_elem : tr[j].1 = q := by
                simpa [List.get_eq_getElem] using hsame
              have hstored_eq_v_elem : tr[j].2 = v := by
                simpa [List.get_eq_getElem] using hstored_eq_v
              simpa [Function.update, hsame_elem, hstored_eq_v_elem]
            · -- Otherwise the fresh update misses this older query point.
              have hsame_elem : ¬ tr[j].1 = q := by
                simpa [List.get_eq_getElem] using hsame
              simpa [Function.update, hsame_elem] using href j hj_old
          · -- The newly appended entry evaluates by `Function.update_self`.
            simp [tr', referenceOracleOfTranscript_append_singleton, List.get_eq_getElem]
        · intro j hj
          have hj_split : j < tr.length ∨ j = tr.length := by
            have hj' : j < tr.length + 1 := by simpa [tr', htr_len] using hj
            exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj')
          rcases hj_split with hj_old | rfl
          · -- The hard objectives on older stored queries are unchanged by the append.
            calc
              φ₁ ((tr'.get ⟨j, hj⟩).1) = φ₁ ((tr.get ⟨j, hj_old⟩).1) := by
                  simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
              _ = (tr.get ⟨j, hj_old⟩).2 := hφ₁_ref j hj_old
              _ = (tr'.get ⟨j, hj⟩).2 := by
                  simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
          · -- The new stored value is the common hard value supplied by the step hypothesis.
            calc
              φ₁ ((tr'.get ⟨tr.length, hj⟩).1) = φ₁ q := by
                  simp [tr', List.get_eq_getElem]
              _ = v := hφ₁_q
              _ = (tr'.get ⟨tr.length, hj⟩).2 := by
                  simp [tr', List.get_eq_getElem]
        · intro j hj
          have hj_split : j < tr.length ∨ j = tr.length := by
            have hj' : j < tr.length + 1 := by simpa [tr', htr_len] using hj
            exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj')
          rcases hj_split with hj_old | rfl
          · -- The same left-append argument handles the second hard objective.
            calc
              φ₂ ((tr'.get ⟨j, hj⟩).1) = φ₂ ((tr.get ⟨j, hj_old⟩).1) := by
                  simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
              _ = (tr.get ⟨j, hj_old⟩).2 := hφ₂_ref j hj_old
              _ = (tr'.get ⟨j, hj⟩).2 := by
                  simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
          · -- And the new endpoint is exactly the second common value returned by `hstep`.
            calc
              φ₂ ((tr'.get ⟨tr.length, hj⟩).1) = φ₂ q := by
                  simp [tr', List.get_eq_getElem]
              _ = v := hφ₂_q
              _ = (tr'.get ⟨tr.length, hj⟩).2 := by
                  simp [tr', List.get_eq_getElem]
  exact hbuild T le_rfl

/-- Helper for Theorem 3.50: if two hard oracles both reproduce a common reference transcript on
the reference-path queries, then they have identical queried values along the first hard path. -/
private theorem same_query_values_of_common_reference
    (algorithm : DeterministicValueOracleMethod E)
    (oracleRef oracle₁ oracle₂ : E → ℝ) {T : ℕ}
    (h₁ :
      ∀ j < T,
        oracle₁ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j))
    (h₂ :
      ∀ j < T,
        oracle₂ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j)) :
    ∀ j < T,
      oracle₁ (algorithm.queryAfter oracle₁ j) =
        oracle₂ (algorithm.queryAfter oracle₁ j) := by
  intro j hj
  have hsync₁ :
      ∀ t, t ≤ j → algorithm.queryAfter oracle₁ t = algorithm.queryAfter oracleRef t := by
    intro t
    refine Nat.strong_induction_on t ?_
    intro s ih hs_le_j
    -- Rebuild the prefix transcript recursively from the common reference values.
    refine queryAfter_eq_of_same_query_values algorithm oracle₁ oracleRef ?_
    intro m hm
    have hmj : m ≤ j := Nat.le_trans (Nat.le_of_lt hm) hs_le_j
    have hquery_eq :
        algorithm.queryAfter oracle₁ m = algorithm.queryAfter oracleRef m :=
      ih m hm hmj
    have hmT : m < T := lt_of_lt_of_le hm (Nat.le_trans hs_le_j (Nat.le_of_lt hj))
    -- Rewrite the hard-oracle value through the synchronized query point and then use the
    -- reference-path hypothesis.
    rw [hquery_eq]
    exact h₁ m hmT
  have hquery_eq :
      algorithm.queryAfter oracle₁ j = algorithm.queryAfter oracleRef j :=
    hsync₁ j le_rfl
  -- Both hard oracles now evaluate at the same reference-path query, so the reference equalities
  -- identify their returned values.
  calc
    oracle₁ (algorithm.queryAfter oracle₁ j) =
        oracleRef (algorithm.queryAfter oracleRef j) := by
          rw [hquery_eq]
          exact h₁ j hj
    _ = oracle₂ (algorithm.queryAfter oracleRef j) := by
          symm
          exact h₂ j hj
    _ = oracle₂ (algorithm.queryAfter oracle₁ j) := by
          rw [hquery_eq]

/-- Helper for Theorem 3.50: once the hard objectives are known to match a common reference
oracle on that reference path, the queried values along the first hard transcript are already
synchronized. This isolates the remaining work to constructing a transcript-compatible reference
surface for the chosen hard sets. -/
private theorem sameQueryValues_forReferenceMatchedObjectives
    (algorithm : DeterministicValueOracleMethod E)
    (oracleRef φ₁ φ₂ : E → ℝ) {T : ℕ}
    (hφ₁_ref :
      ∀ j < T,
        φ₁ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j))
    (hφ₂_ref :
      ∀ j < T,
        φ₂ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j)) :
    ∀ j < T,
      φ₁ (algorithm.queryAfter φ₁ j) =
        φ₂ (algorithm.queryAfter φ₁ j) := by
  -- The generic common-reference transport lemma already converts reference-path agreement into
  -- equality of queried values along the first hard transcript.
  exact same_query_values_of_common_reference algorithm oracleRef φ₁ φ₂ hφ₁_ref hφ₂_ref

/-- Helper for Theorem 3.50: once an explicit finite transcript is folded into a reference oracle
and both hard objectives realize the stored query values along that folded path, the generic
common-reference transport lemma synchronizes the queried values along the first hard transcript. -/
private theorem sameQueryValues_forTranscriptReferenceMatchedObjectives
    (algorithm : DeterministicValueOracleMethod E)
    (oracleBase φ₁ φ₂ : E → ℝ) (tr : List (E × ℝ))
    (hquery :
      ∀ j (hj : j < tr.length),
        algorithm.queryAfter (referenceOracleOfTranscript oracleBase tr) j =
          (tr.get ⟨j, hj⟩).1)
    (href :
      ∀ j (hj : j < tr.length),
        referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
          (tr.get ⟨j, hj⟩).2)
    (hφ₁_ref :
      ∀ j (hj : j < tr.length),
        φ₁ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2)
    (hφ₂_ref :
      ∀ j (hj : j < tr.length),
        φ₂ ((tr.get ⟨j, hj⟩).1) = (tr.get ⟨j, hj⟩).2) :
    ∀ j : ℕ, j < tr.length →
      φ₁ (algorithm.queryAfter φ₁ j) =
        φ₂ (algorithm.queryAfter φ₁ j) := by
  let oracleRef := referenceOracleOfTranscript oracleBase tr
  have hφ₁_ref' :
      ∀ j < tr.length,
        φ₁ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j) := by
    intro j hj
    -- Rewrite the folded-oracle query to the stored transcript query and compare values there.
    rw [hquery j hj]
    rw [hφ₁_ref j hj]
    simpa [oracleRef] using (href j hj).symm
  have hφ₂_ref' :
      ∀ j < tr.length,
        φ₂ (algorithm.queryAfter oracleRef j) =
          oracleRef (algorithm.queryAfter oracleRef j) := by
    intro j hj
    -- The second hard objective matches the same folded transcript values on the same path.
    rw [hquery j hj]
    rw [hφ₂_ref j hj]
    simpa [oracleRef] using (href j hj).symm
  -- The existing common-reference lemma now converts the explicit transcript data into the
  -- queried-value equality needed by the hard-instance package.
  exact
    sameQueryValues_forReferenceMatchedObjectives
      algorithm oracleRef φ₁ φ₂ hφ₁_ref' hφ₂_ref'

/-- Helper for Theorem 3.50: once two descendant current boxes already realize one common query
transcript and stay pairwise separated, the generic scaled-distance package turns them into the
final hard instances. -/
private theorem descendantCurrentBoxesPackageShortBudgetCounterexample
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hM : 0 < (M : ℝ))
    (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    (hsame_query :
      ∀ j : ℕ, j < T →
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j)) =
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j)))
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    ∃ φ₁ φ₂ K₁ K₂,
      K₁.Nonempty ∧
        IsClosed K₁ ∧
          Convex ℝ K₁ ∧
            K₁ ⊆ linftyClosedBall R ∧
              K₂.Nonempty ∧
                IsClosed K₂ ∧
                  Convex ℝ K₂ ∧
                    K₂ ⊆ linftyClosedBall R ∧
                      φ₁ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
                        φ₂ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
                          (∀ x ∈ K₁, φ₁ x = 0) ∧
                            (∀ x ∈ K₂, φ₂ x = 0) ∧
                              (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
                                φ₁).optimalValue = 0 ∧
                                (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
                                  φ₂).optimalValue = 0 ∧
                                  (∀ j : ℕ, j < T →
                                    φ₁ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j) =
                                      φ₂ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j)) ∧
                                    (∀ x : E, ¬ (φ₁ x ≤ ε ∧ φ₂ x ≤ ε)) := by
  let K₁ : Set E := state₁.currentBox (R : ℝ) hn
  let K₂ : Set E := state₂.currentBox (R : ℝ) hn
  obtain ⟨hK₁_nonempty, hK₁_closed, hK₁_convex⟩ :=
    currentBox_nonempty_isClosed_convex R hn state₁
  obtain ⟨hK₂_nonempty, hK₂_closed, hK₂_convex⟩ :=
    currentBox_nonempty_isClosed_convex R hn state₂
  have hK₁_subset : K₁ ⊆ linftyClosedBall R :=
    currentBox_subset_linftyClosedBall R hn state₁
  have hK₂_subset : K₂ ⊆ linftyClosedBall R :=
    currentBox_subset_linftyClosedBall R hn state₂
  -- Repackage the descendant current boxes directly as the two hard-set owners.
  exact
    package_separated_axis_box_hard_instances
      method hM
      hK₁_nonempty hK₁_closed hK₁_convex hK₁_subset
      hK₂_nonempty hK₂_closed hK₂_convex hK₂_subset
      (by simpa [K₁, K₂] using hsame_query)
      (by simpa [K₁, K₂] using hsep)

/-- Helper for Theorem 3.50: every resisting-prefix state before the budget horizon still contains
the textbook-radius Euclidean ball, and that radius remains strictly larger than `4 * (ε / M)`.
-/
private theorem shortBudgetRoomInPrefixState
    {R M : NNReal} {ε : ℝ} {T t : ℕ}
    (algorithm : DeterministicValueOracleMethod E)
    (oracle : E → ℝ)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (ht : t ≤ T)
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∃ ρ : ℝ,
      4 * (ε / (M : ℝ)) < ρ ∧
        Metric.closedBall
            ((resistingPrefixState R hn algorithm oracle t).currentCenter (R : ℝ) hn)
            ρ ⊆
          (resistingPrefixState R hn algorithm oracle t).currentBox (R : ℝ) hn := by
  let ρt : ℝ := (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((t : ℝ) / n)
  let ρT : ℝ := (R : ℝ) / 2 * Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n)
  have hball :
      Metric.closedBall
          ((resistingPrefixState R hn algorithm oracle t).currentCenter (R : ℝ) hn)
          ρt ⊆
        (resistingPrefixState R hn algorithm oracle t).currentBox (R : ℝ) hn := by
    -- The prefix-state inradius control is already available as the common protected-ball lemma.
    simpa [ρt] using commonPrefixClosedBallSubset_currentBox (T := t) R hn algorithm oracle
  have hroomT : 4 * ε / (M : ℝ) < ρT := by
    -- The global short-budget inequality gives the radius lower bound at the horizon `T`.
    simpa [ρT] using shortBudgetRadius_gt_fourEpsOverM hn hε hM hbudget
  have hdiv :
      ((t : ℝ) / n) ≤ ((T : ℝ) / n) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ht) (by positivity : 0 ≤ (n : ℝ))
  have hrpow :
      Real.rpow (1 / 2 : ℝ) ((T : ℝ) / n) ≤
        Real.rpow (1 / 2 : ℝ) ((t : ℝ) / n) := by
    -- Earlier prefixes have larger protected radii because the base `1 / 2` lies in `(0, 1)`.
    refine Real.rpow_le_rpow_of_exponent_ge' ?_ ?_ ?_ hdiv
    · norm_num
    · norm_num
    · positivity
  have hρmono : ρT ≤ ρt := by
    -- Multiplying by the nonnegative scale `R / 2` preserves the monotonicity.
    exact mul_le_mul_of_nonneg_left hrpow (by positivity : 0 ≤ (R : ℝ) / 2)
  have hroomT' : 4 * (ε / (M : ℝ)) < ρT := by
    -- Normalize the scalar factor to match the statement surface of this helper.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hroomT
  refine ⟨ρt, ?_, hball⟩
  -- The earlier protected radius is at least as large as the horizon radius.
  exact lt_of_lt_of_le hroomT' hρmono

/-- Helper for Theorem 3.50: `StoredBoundaryWitness R hn state₁ state₂ q` records that the query
`q` meets a common exposed lower or upper face of the two current boxes, while staying inside both
boxes on every other coordinate. -/
private def StoredBoundaryWitness
    (R : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n) (q : E) : Prop :=
  ∃ i : Fin n,
    ((state₁.currentLower (R : ℝ) hn i = state₂.currentLower (R : ℝ) hn i ∧
        q i ≤ state₁.currentLower (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j)) ∨
      (state₁.currentUpper (R : ℝ) hn i = state₂.currentUpper (R : ℝ) hn i ∧
        state₁.currentUpper (R : ℝ) hn i ≤ q i ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j)))

/-- Helper for Theorem 3.50: a one-box exposed-face witness already gives the package-level
stored witness for the pair `(state, state)`. This is the minimal normalization step from a
single-box face certificate to the later two-state witness API. -/
private theorem storedBoundaryWitnessSelfOfBoundaryFace
    (R : NNReal) (hn : 0 < n)
    (state : FeasibilityResistingOracleState n) {q : E}
    (hboundary :
      ∃ i : Fin n,
        ((q i ≤ state.currentLower (R : ℝ) hn i ∨
            state.currentUpper (R : ℝ) hn i ≤ q i) ∧
          ∀ j : Fin n, j ≠ i →
            state.currentLower (R : ℝ) hn j ≤ q j ∧
              q j ≤ state.currentUpper (R : ℝ) hn j)) :
    StoredBoundaryWitness R hn state state q := by
  rcases hboundary with ⟨i, hface, hinside⟩
  refine ⟨i, ?_⟩
  rcases hface with hlow | hupp
  · -- The lower-face branch keeps the same boundary data on both copies of the state.
    left
    refine ⟨rfl, hlow, ?_, ?_⟩
    · intro j hj
      exact hinside j hj
    · intro j hj
      exact hinside j hj
  · -- The upper-face branch is identical after switching to the upper-bound clause.
    right
    refine ⟨rfl, hupp, ?_, ?_⟩
    · intro j hj
      exact hinside j hj
    · intro j hj
      exact hinside j hj

/-- Helper for Theorem 3.50: if a query is coordinatewise inside a parent box, then any
`queryCompatibleCurrentBox` descendant still contains that query in the corresponding coordinate
interval. -/
private theorem queryCompatibleCurrentBox_coordinate_mem
    (R : NNReal) (hn : 0 < n)
    (parent child : FeasibilityResistingOracleState n) (q : E)
    (hcompat : queryCompatibleCurrentBox R hn parent child q)
    {j : Fin n}
    (hinside_parent :
      parent.currentLower (R : ℝ) hn j ≤ q j ∧
        q j ≤ parent.currentUpper (R : ℝ) hn j) :
    child.currentLower (R : ℝ) hn j ≤ q j ∧
      q j ≤ child.currentUpper (R : ℝ) hn j := by
  rcases hcompat with ⟨hlower, hupper, hinside⟩
  by_cases hlow : q j ≤ parent.currentLower (R : ℝ) hn j
  · have hchild_lower :
        child.currentLower (R : ℝ) hn j =
          parent.currentLower (R : ℝ) hn j :=
      hlower j hlow
    have hq_eq :
        q j = parent.currentLower (R : ℝ) hn j :=
      le_antisymm hlow hinside_parent.1
    constructor
    · simpa [hchild_lower, hq_eq]
    · calc
        q j = child.currentLower (R : ℝ) hn j := by
          simpa [hchild_lower] using hq_eq
        _ ≤ child.currentUpper (R : ℝ) hn j := currentLower_le_currentUpper R hn child j
  · by_cases hupp : parent.currentUpper (R : ℝ) hn j ≤ q j
    · have hchild_upper :
          child.currentUpper (R : ℝ) hn j =
            parent.currentUpper (R : ℝ) hn j :=
        hupper j hupp
      have hq_eq :
          q j = parent.currentUpper (R : ℝ) hn j :=
        le_antisymm hinside_parent.2 hupp
      constructor
      · calc
          child.currentLower (R : ℝ) hn j ≤ child.currentUpper (R : ℝ) hn j :=
            currentLower_le_currentUpper R hn child j
          _ = q j := by simpa [hchild_upper] using hq_eq.symm
      · simpa [hchild_upper, hq_eq]
    · exact hinside j hlow hupp

/-- Helper for Theorem 3.50: a stored boundary witness survives along two
`queryCompatibleCurrentBox` descendants of the same query. -/
private theorem storedBoundaryWitness_of_queryCompatible
    (R : NNReal) (hn : 0 < n)
    (parent₁ parent₂ child₁ child₂ : FeasibilityResistingOracleState n)
    {q : E}
    (hwitness : StoredBoundaryWitness R hn parent₁ parent₂ q)
    (hcompat₁ : queryCompatibleCurrentBox R hn parent₁ child₁ q)
    (hcompat₂ : queryCompatibleCurrentBox R hn parent₂ child₂ q) :
    StoredBoundaryWitness R hn child₁ child₂ q := by
  rcases hcompat₁ with ⟨hlower₁, hupper₁, hinside₁⟩
  rcases hcompat₂ with ⟨hlower₂, hupper₂, hinside₂⟩
  rcases hwitness with ⟨i, hboundary⟩
  refine ⟨i, ?_⟩
  rcases hboundary with
    ⟨hface, hqi, hinside_parent₁, hinside_parent₂⟩ |
    ⟨hface, hqi, hinside_parent₁, hinside_parent₂⟩
  · left
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Transport the shared lower face through both compatible descendants.
      calc
        child₁.currentLower (R : ℝ) hn i =
            parent₁.currentLower (R : ℝ) hn i := hlower₁ i hqi
        _ = parent₂.currentLower (R : ℝ) hn i := hface
        _ = child₂.currentLower (R : ℝ) hn i := by
            symm
            exact hlower₂ i (by simpa [hface] using hqi)
    · -- The exposed lower-face inequality is preserved on the first child.
      simpa [hlower₁ i hqi] using hqi
    · -- Every other coordinate stays inside the first child box.
      intro j hj
      exact
        queryCompatibleCurrentBox_coordinate_mem
          R hn parent₁ child₁ q
          ⟨hlower₁, hupper₁, hinside₁⟩
          (hinside_parent₁ j hj)
    · -- The same coordinatewise containment holds for the second child.
      intro j hj
      exact
        queryCompatibleCurrentBox_coordinate_mem
          R hn parent₂ child₂ q
          ⟨hlower₂, hupper₂, hinside₂⟩
          (hinside_parent₂ j hj)
  · right
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Transport the shared upper face through both compatible descendants.
      calc
        child₁.currentUpper (R : ℝ) hn i =
            parent₁.currentUpper (R : ℝ) hn i := hupper₁ i hqi
        _ = parent₂.currentUpper (R : ℝ) hn i := hface
        _ = child₂.currentUpper (R : ℝ) hn i := by
            symm
            exact hupper₂ i (by simpa [hface] using hqi)
    · -- The exposed upper-face inequality is preserved on the first child.
      simpa [hupper₁ i hqi] using hqi
    · -- Every other coordinate stays inside the first child box.
      intro j hj
      exact
        queryCompatibleCurrentBox_coordinate_mem
          R hn parent₁ child₁ q
          ⟨hlower₁, hupper₁, hinside₁⟩
          (hinside_parent₁ j hj)
    · -- And likewise for the second child.
      intro j hj
      exact
        queryCompatibleCurrentBox_coordinate_mem
          R hn parent₂ child₂ q
          ⟨hlower₂, hupper₂, hinside₂⟩
          (hinside_parent₂ j hj)

/-- Helper for Theorem 3.50: every stored boundary witness determines an explicit point in the
intersection of the two current boxes, obtained by clamping the exposed coordinate to the shared
boundary value and leaving all other coordinates equal to the query. -/
private theorem commonPoint_ofStoredBoundaryWitness
    (R : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E}
    (hwitness : StoredBoundaryWitness R hn state₁ state₂ q) :
    ∃ p : E,
      p ∈ state₁.currentBox (R : ℝ) hn ∧
        p ∈ state₂.currentBox (R : ℝ) hn := by
  rcases hwitness with ⟨k, hboundary⟩
  rcases hboundary with
    ⟨hface, hqi, hinside₁, hinside₂⟩ |
    ⟨hface, hqi, hinside₁, hinside₂⟩
  · let p : E :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (Function.update (EuclideanSpace.equiv (Fin n) ℝ q) k
          (state₁.currentLower (R : ℝ) hn k))
    refine ⟨p, ?_, ?_⟩
    · -- The shared lower face gives one coordinate exactly on the boundary and keeps the others.
      rw [currentBox_eq_currentBounds_set (R : ℝ) hn state₁]
      intro j
      by_cases hj : j = k
      · subst hj
        constructor
        · simp [p, Function.update_self]
        · simpa [p, Function.update_self] using
            currentLower_le_currentUpper R hn state₁ j
      · have hinside := hinside₁ j hj
        simpa [p, hj] using hinside
    · -- The same clamped point lies in the second box because the face value is shared.
      rw [currentBox_eq_currentBounds_set (R : ℝ) hn state₂]
      intro j
      by_cases hj : j = k
      · subst hj
        constructor
        · calc
            state₂.currentLower (R : ℝ) hn j =
                state₁.currentLower (R : ℝ) hn j := hface.symm
            _ ≤ p j := by simp [p, Function.update_self]
        · simpa [p, hface, Function.update_self] using
            currentLower_le_currentUpper R hn state₂ j
      · have hinside := hinside₂ j hj
        simpa [p, hj] using hinside
  · let p : E :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (Function.update (EuclideanSpace.equiv (Fin n) ℝ q) k
          (state₁.currentUpper (R : ℝ) hn k))
    refine ⟨p, ?_, ?_⟩
    · -- In the upper-face branch the clamped coordinate lands on the shared upper boundary.
      rw [currentBox_eq_currentBounds_set (R : ℝ) hn state₁]
      intro j
      by_cases hj : j = k
      · subst hj
        constructor
        · simpa [p, Function.update_self] using
            currentLower_le_currentUpper R hn state₁ j
        · simp [p, Function.update_self]
      · have hinside := hinside₁ j hj
        simpa [p, hj] using hinside
    · -- The second box contains the same upper-face clamp because the upper bound is shared.
      rw [currentBox_eq_currentBounds_set (R : ℝ) hn state₂]
      intro j
      by_cases hj : j = k
      · subst hj
        constructor
        · simpa [p, hface, Function.update_self] using
            currentLower_le_currentUpper R hn state₂ j
        · simpa [p, hface, Function.update_self]
      · have hinside := hinside₂ j hj
        simpa [p, hj] using hinside

/-- Helper for Theorem 3.50: a stored boundary witness immediately produces the common step value
used by the reference-transcript construction. -/
private theorem commonValueOfStoredBoundaryWitness
    (R M : NNReal) (hn : 0 < n)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E}
    (hwitness : StoredBoundaryWitness R hn state₁ state₂ q) :
    ∃ v,
      (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v ∧
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
  rcases hwitness with ⟨i, hwitness⟩
  -- Unpack the stored witness and hand it to the one-step boundary-face API.
  exact commonStepValue_of_boundaryWitness R M hn state₁ state₂ (i := i) hwitness

/-- Helper for Theorem 3.50: a transcript-compatible separated package records one common
reference transcript together with two descendant states whose hard objectives realize the stored
transcript values and whose current boxes stay separated at the target scale. -/
private structure TranscriptCompatibleSeparatedPairPackage
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (hn : 0 < n) (t : ℕ) where
  oracleBase : E → ℝ
  tr : List (E × ℝ)
  state₁ : FeasibilityResistingOracleState n
  state₂ : FeasibilityResistingOracleState n
  hlen : tr.length = t
  hquery :
    ∀ j (hj : j < tr.length),
      (method (linftyClosedBall R : Set E)).queryAfter
          (referenceOracleOfTranscript oracleBase tr) j =
        (tr.get ⟨j, hj⟩).1
  href :
    ∀ j (hj : j < tr.length),
      referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
        (tr.get ⟨j, hj⟩).2
  hstate₁_ref :
    ∀ j (hj : j < tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
          ((tr.get ⟨j, hj⟩).1)) =
        (tr.get ⟨j, hj⟩).2
  hstate₂_ref :
    ∀ j (hj : j < tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
          ((tr.get ⟨j, hj⟩).1)) =
        (tr.get ⟨j, hj⟩).2
  hwitness :
    ∀ j (hj : j < tr.length),
      StoredBoundaryWitness R hn state₁ state₂ ((tr.get ⟨j, hj⟩).1)
  hsep :
    ∀ u ∈ state₁.currentBox (R : ℝ) hn,
      ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v

/-- Helper for Theorem 3.50: an empty transcript together with any separated pair of current boxes
already forms the length-`0` package. This isolates the geometric base case from the transcript
bookkeeping. -/
private def emptyTranscriptCompatibleSeparatedPairPackage
    {R M : NNReal} {ε : ℝ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    TranscriptCompatibleSeparatedPairPackage method R M ε hn 0 where
  oracleBase := oracleBase
  tr := []
  state₁ := state₁
  state₂ := state₂
  hlen := rfl
  hquery := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  href := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hstate₁_ref := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hstate₂_ref := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hwitness := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hsep := hsep

/-- Helper for Theorem 3.50: once the successor geometry provides a new separated pair of current
boxes that already realizes the old transcript and one fresh common witness for the new query,
appending that one query-value pair upgrades the package length by one. This keeps the remaining
frontier purely geometric. -/
private def appendTranscriptCompatibleSeparatedPairPackage
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn t)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E}
    (hq :
      q = (method (linftyClosedBall R : Set E)).queryAfter
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) t)
    (hstate₁_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hstate₂_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hwitness_old :
      ∀ j (hj : j < pkg.tr.length),
        StoredBoundaryWitness R hn state₁ state₂ ((pkg.tr.get ⟨j, hj⟩).1))
    (hwitness_new : StoredBoundaryWitness R hn state₁ state₂ q)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    TranscriptCompatibleSeparatedPairPackage method R M ε hn (t + 1) := by
  classical
  let hvalue :
      ∃ v,
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v ∧
          (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v :=
    commonValueOfStoredBoundaryWitness R M hn state₁ state₂ hwitness_new
  let v : ℝ := Classical.choose hvalue
  have hvalue₁ :
      (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v :=
    (Classical.choose_spec hvalue).1
  have hvalue₂ :
      (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v :=
    (Classical.choose_spec hvalue).2
  let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
  let tr' : List (E × ℝ) := pkg.tr ++ [(q, v)]
  have hstable :
      ∀ s < pkg.tr.length,
        (method (linftyClosedBall R : Set E)).queryAfter oracleRef s = q →
          oracleRef q = v := by
    intro s hs hsq
    have hquery_old :
        (method (linftyClosedBall R : Set E)).queryAfter oracleRef s =
          (pkg.tr.get ⟨s, hs⟩).1 :=
      pkg.hquery s hs
    have hquery_eq :
        (pkg.tr.get ⟨s, hs⟩).1 = q := by
      rw [← hquery_old]
      exact hsq
    have horacle_eq_old :
        oracleRef q = (pkg.tr.get ⟨s, hs⟩).2 := by
      rw [← hquery_eq]
      exact pkg.href s hs
    have hnew_eq_old :
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
          (pkg.tr.get ⟨s, hs⟩).2 := by
      rw [← hquery_eq]
      exact hstate₁_old s hs
    -- Compare the old transcript value at the repeated query with the fresh witness value.
    exact horacle_eq_old.trans (hnew_eq_old.symm.trans hvalue₁)
  refine
    { oracleBase := pkg.oracleBase
      tr := tr'
      state₁ := state₁
      state₂ := state₂
      hlen := by
        -- The appended singleton is the only new transcript entry.
        simpa [tr', pkg.hlen]
      hquery := ?_
      href := ?_
      hstate₁_ref := ?_
      hstate₂_ref := ?_
      hwitness := ?_
      hsep := hsep }
  · intro j hj
    have hj_le : j ≤ pkg.tr.length := by
      have : j < pkg.tr.length + 1 := by simpa [tr', pkg.hlen] using hj
      omega
    by_cases hj_old : j < pkg.tr.length
    · -- Old transcript queries replay unchanged after appending a consistent repeated value.
      calc
        (method (linftyClosedBall R : Set E)).queryAfter
            (referenceOracleOfTranscript pkg.oracleBase tr') j =
            (method (linftyClosedBall R : Set E)).queryAfter oracleRef j := by
              exact
                queryAfter_eq_of_referenceOracle_append_singleton_prefix
                  (method (linftyClosedBall R : Set E))
                  pkg.oracleBase pkg.tr hstable hj_le
        _ = (pkg.tr.get ⟨j, hj_old⟩).1 := pkg.hquery j hj_old
        _ = (tr'.get ⟨j, hj⟩).1 := by
              simp [tr', List.get_eq_getElem, hj_old]
    · have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The new transcript entry records exactly the next query chosen from the old reference path.
      calc
        (method (linftyClosedBall R : Set E)).queryAfter
            (referenceOracleOfTranscript pkg.oracleBase tr') pkg.tr.length =
            (method (linftyClosedBall R : Set E)).queryAfter oracleRef pkg.tr.length := by
              exact
                queryAfter_eq_of_referenceOracle_append_singleton_prefix
                  (method (linftyClosedBall R : Set E))
                  pkg.oracleBase pkg.tr hstable le_rfl
        _ = q := by simpa [oracleRef, pkg.hlen] using hq.symm
        _ = (tr'.get ⟨pkg.tr.length, hj⟩).1 := by
              simp [tr', List.get_eq_getElem]
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · have hget_old :
          tr'.get ⟨j, hj⟩ = pkg.tr.get ⟨j, hj_old⟩ := by
          simp [tr', List.get_eq_getElem, hj_old]
      by_cases hsameq : (pkg.tr.get ⟨j, hj_old⟩).1 = q
      · -- Repeated queries are stable because the old transcript already stored the same value.
        have horacle_eq_v : oracleRef q = v := by
          exact hstable j hj_old (by rw [pkg.hquery j hj_old, hsameq])
        have hstored_eq_v : (pkg.tr.get ⟨j, hj_old⟩).2 = v := by
          calc
            (pkg.tr.get ⟨j, hj_old⟩).2 =
                oracleRef ((pkg.tr.get ⟨j, hj_old⟩).1) := by
                  symm
                  exact pkg.href j hj_old
            _ = oracleRef q := by rw [hsameq]
            _ = v := horacle_eq_v
        rw [hget_old, referenceOracleOfTranscript_append_singleton, hsameq]
        simpa [Function.update] using hstored_eq_v.symm
      · -- Fresh old queries are untouched by the appended singleton update.
        have hsameq_elem : ¬ pkg.tr[j].1 = q := by
          simpa [List.get_eq_getElem] using hsameq
        rw [hget_old, referenceOracleOfTranscript_append_singleton]
        simpa [Function.update, hsameq_elem] using pkg.href j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The appended singleton answers the new query by construction.
      simp [referenceOracleOfTranscript_append_singleton, tr', List.get_eq_getElem]
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- The new state pair already realizes every old transcript value by hypothesis.
      simpa [tr', List.get_eq_getElem, hj_old] using hstate₁_old j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The fresh witness gives the value stored at the appended query.
      simpa [tr', List.get_eq_getElem] using hvalue₁
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- The second hard state carries the same old transcript values as well.
      simpa [tr', List.get_eq_getElem, hj_old] using hstate₂_old j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The appended value is also realized by the second state through the same witness.
      simpa [tr', List.get_eq_getElem] using hvalue₂
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- The old witness family is carried over unchanged in the upgraded package.
      simpa [tr', List.get_eq_getElem, hj_old] using hwitness_old j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The new transcript entry stores the fresh witness for the actual query.
      simpa [tr', List.get_eq_getElem] using hwitness_new

/-- Helper for Theorem 3.50: once a transcript-compatible separated package reaches length `T`,
the generic transcript/reference bridge already yields the queried-value equality along the first
hard transcript, and the package carries the final separation invariant verbatim. -/
private theorem sameQueryOfFinalTranscriptCompatiblePair
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn T) :
    (∀ j : ℕ, j < T →
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) j)) =
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) j))) ∧
      (∀ u ∈ pkg.state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ pkg.state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) := by
  constructor
  · -- The recorded transcript already matches both hard objectives on the same reference path.
    have hsame :=
      sameQueryValues_forTranscriptReferenceMatchedObjectives
        (method (linftyClosedBall R : Set E))
        pkg.oracleBase
        (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
        (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
        pkg.tr
        pkg.hquery
        pkg.href
        pkg.hstate₁_ref
        pkg.hstate₂_ref
    intro j hj
    have hj' : j < pkg.tr.length := by simpa [pkg.hlen] using hj
    simpa [pkg.hlen] using hsame j hj'
  · -- The package stores the final box separation directly.
    exact pkg.hsep

/-- Helper for Theorem 3.50: the repaired private geometric input is just the existence of one
length-`T` transcript-compatible separated package over the chosen reference oracle. This removes
the previous false quantification over arbitrary transcript/value lists and keeps the downstream
public route unchanged. -/
private def GeometricPackageInput
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (hn : 0 < n) (T : ℕ) (oracleBase : E → ℝ) : Prop :=
  ∃ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn T,
    pkg.oracleBase = oracleBase

/-- Helper for Theorem 3.50: after repairing the private surface, extracting the transcript
package is immediate because the geometric input already stores exactly that package. -/
private def existsTranscriptCompatibleSeparatedPairPackage_ofGeometricInput
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (hinput : GeometricPackageInput method R M ε hn T oracleBase) :
    TranscriptCompatibleSeparatedPairPackage method R M ε hn T := by
  classical
  -- The repaired input surface already stores the final package, so no extra recursion remains.
  exact Classical.choose hinput

/-- Helper for Theorem 3.50: any pair of separated current boxes already seeds the repaired
transcript package at length `0`, because the empty transcript carries no compatibility
constraints. -/
private theorem existsInitialTranscriptCompatibleSeparatedPairPackage_ofSeparatedStates
    {R M : NNReal} {ε : ℝ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    ∃ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn 0,
      pkg.oracleBase = oracleBase := by
  -- The empty-package constructor already packages the seed pair of separated states.
  refine ⟨emptyTranscriptCompatibleSeparatedPairPackage method hn oracleBase state₁ state₂ hsep, rfl⟩

/-- Helper for Theorem 3.50: once the geometric seed package at time `0` and every append-ready
successor step are available over a fixed reference oracle, the final repaired package follows by
plain induction on the transcript length. -/
private theorem existsTranscriptCompatibleSeparatedPairPackage_ofSeededSuccessor
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (hseededStep :
      (∃ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn 0,
          pkg.oracleBase = oracleBase) ∧
        (∀ {t : ℕ}, t < T →
          ∀ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn t,
            pkg.oracleBase = oracleBase →
            ∃ pkg' : TranscriptCompatibleSeparatedPairPackage method R M ε hn (t + 1),
              pkg'.oracleBase = oracleBase)) :
    ∃ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn T,
      pkg.oracleBase = oracleBase := by
  rcases hseededStep with ⟨hseed, hstep⟩
  have hbuild :
      ∀ t ≤ T,
        ∃ pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn t,
          pkg.oracleBase = oracleBase := by
    intro t ht
    induction t with
    | zero =>
        -- The seed package is exactly the length-`0` case.
        exact hseed
    | succ t iht =>
        -- Apply the geometric successor step to the already-built prefix package.
        have ht_lt : t < T := by omega
        rcases iht (Nat.le_of_succ_le ht) with ⟨pkg, hpkg⟩
        exact hstep ht_lt pkg hpkg
  -- Evaluate the inductive builder at the target horizon.
  exact hbuild T le_rfl

/-- Helper for Theorem 3.50: `AnchoredBoundaryFaceData R M hn anchor state₁ state₂ q v` records
just the shared exposed face of the common prefix anchor needed to recover both the old stored
boundary witness and the exact stored transcript value on the two final states. This is the
minimal anchored replacement for the previous over-strong `queryCompatibleCurrentBox` route. -/
private def AnchoredBoundaryFaceData
    (R M : NNReal) (hn : 0 < n)
    (anchor state₁ state₂ : FeasibilityResistingOracleState n)
    (q : E) (v : ℝ) : Prop :=
  ∃ i : Fin n,
    ((q i ≤ anchor.currentLower (R : ℝ) hn i ∧
        state₁.currentLower (R : ℝ) hn i = anchor.currentLower (R : ℝ) hn i ∧
        state₂.currentLower (R : ℝ) hn i = anchor.currentLower (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          anchor.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ anchor.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j) ∧
        (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v) ∨
      (anchor.currentUpper (R : ℝ) hn i ≤ q i ∧
        state₁.currentUpper (R : ℝ) hn i = anchor.currentUpper (R : ℝ) hn i ∧
        state₂.currentUpper (R : ℝ) hn i = anchor.currentUpper (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          anchor.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ anchor.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₁.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₁.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state₂.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state₂.currentUpper (R : ℝ) hn j) ∧
        (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v))

/-- Helper for Theorem 3.50: one anchored face/value record is already enough to recover the old
package-level witness and both exact stored transcript values on the final two states. -/
private theorem storedBoundaryWitnessAndValues_ofAnchoredBoundaryFaceData
    {R M : NNReal} (hn : 0 < n)
    (anchor state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ}
    (hface : AnchoredBoundaryFaceData R M hn anchor state₁ state₂ q v) :
    StoredBoundaryWitness R hn state₁ state₂ q ∧
      ((M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v) ∧
      ((M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v) := by
  rcases hface with ⟨i, hlower | hupper⟩
  · rcases hlower with ⟨hqi, hface₁, hface₂, hinside_anchor, hinside₁, hinside₂, hv_anchor⟩
    have hshared :
        state₁.currentLower (R : ℝ) hn i =
          state₂.currentLower (R : ℝ) hn i := by
      calc
        state₁.currentLower (R : ℝ) hn i = anchor.currentLower (R : ℝ) hn i := hface₁
        _ = state₂.currentLower (R : ℝ) hn i := hface₂.symm
    have hvalue₁ :
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v := by
      calc
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
            (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
              exact
                scaledInfDist_eq_of_preservedLowerBoundaryFace
                  R M hn anchor state₁ hface₁ hqi hinside_anchor
                  hinside₁
        _ = v := hv_anchor
    have hvalue₂ :
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
      calc
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) =
            (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
              exact
                scaledInfDist_eq_of_preservedLowerBoundaryFace
                  R M hn anchor state₂ hface₂ hqi hinside_anchor
                  hinside₂
        _ = v := hv_anchor
    constructor
    · -- The two final states share the same anchored lower face and contain the query elsewhere.
      refine ⟨i, Or.inl ?_⟩
      refine ⟨hshared, ?_, hinside₁, hinside₂⟩
      simpa [hface₁] using hqi
    · exact ⟨hvalue₁, hvalue₂⟩
  · rcases hupper with ⟨hqi, hface₁, hface₂, hinside_anchor, hinside₁, hinside₂, hv_anchor⟩
    have hshared :
        state₁.currentUpper (R : ℝ) hn i =
          state₂.currentUpper (R : ℝ) hn i := by
      calc
        state₁.currentUpper (R : ℝ) hn i = anchor.currentUpper (R : ℝ) hn i := hface₁
        _ = state₂.currentUpper (R : ℝ) hn i := hface₂.symm
    have hvalue₁ :
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) = v := by
      calc
        (M : ℝ) * Metric.infDist q (state₁.currentBox (R : ℝ) hn) =
            (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
              exact
                scaledInfDist_eq_of_preservedUpperBoundaryFace
                  R M hn anchor state₁ hface₁ hqi hinside_anchor
                  hinside₁
        _ = v := hv_anchor
    have hvalue₂ :
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) = v := by
      calc
        (M : ℝ) * Metric.infDist q (state₂.currentBox (R : ℝ) hn) =
            (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
              exact
                scaledInfDist_eq_of_preservedUpperBoundaryFace
                  R M hn anchor state₂ hface₂ hqi hinside_anchor
                  hinside₂
        _ = v := hv_anchor
    constructor
    · -- The upper-face branch is identical after switching to the shared anchored upper face.
      refine ⟨i, Or.inr ?_⟩
      refine ⟨hshared, ?_, hinside₁, hinside₂⟩
      simpa [hface₁] using hqi
    · exact ⟨hvalue₁, hvalue₂⟩

/-- Helper for Theorem 3.50: every anchored face/value record inherits the same common-point
obstruction as the underlying stored boundary witness. -/
private theorem commonPoint_ofAnchoredBoundaryFaceData
    {R M : NNReal} (hn : 0 < n)
    (anchor state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ}
    (hface : AnchoredBoundaryFaceData R M hn anchor state₁ state₂ q v) :
    ∃ p : E,
      p ∈ state₁.currentBox (R : ℝ) hn ∧
        p ∈ state₂.currentBox (R : ℝ) hn := by
  -- Reduce the anchored surface to the stored witness surface, then reuse the common-point lemma.
  exact
    commonPoint_ofStoredBoundaryWitness R hn state₁ state₂
      (storedBoundaryWitnessAndValues_ofAnchoredBoundaryFaceData
        (R := R) (M := M) hn anchor state₁ state₂ hface).1

/-- Helper for Theorem 3.50: an anchored prefix package remembers the common resisting-prefix
anchor together with only the face/value data actually needed later for each recorded query. -/
private structure AnchoredSeparatedPrefixPackage
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (hn : 0 < n) (t : ℕ) where
  oracleBase : E → ℝ
  tr : List (E × ℝ)
  state₁ : FeasibilityResistingOracleState n
  state₂ : FeasibilityResistingOracleState n
  hlen : tr.length = t
  hquery :
    ∀ j (hj : j < tr.length),
      (method (linftyClosedBall R : Set E)).queryAfter
          (referenceOracleOfTranscript oracleBase tr) j =
        (tr.get ⟨j, hj⟩).1
  href :
    ∀ j (hj : j < tr.length),
      referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
        (tr.get ⟨j, hj⟩).2
  hanchored :
    ∀ j (hj : j < tr.length),
      AnchoredBoundaryFaceData R M hn
        (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
          (referenceOracleOfTranscript oracleBase tr) tr.length)
        state₁ state₂ ((tr.get ⟨j, hj⟩).1) ((tr.get ⟨j, hj⟩).2)
  hsep :
    ∀ u ∈ state₁.currentBox (R : ℝ) hn,
      ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v

/-- Helper for Theorem 3.50: each anchored face/value record already gives the exact stored value
for the first hard state in the old package surface. -/
private theorem anchoredState₁Ref
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : AnchoredSeparatedPrefixPackage method R M ε hn t) :
    ∀ j (hj : j < pkg.tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
          ((pkg.tr.get ⟨j, hj⟩).1)) =
        (pkg.tr.get ⟨j, hj⟩).2 := by
  intro j hj
  -- The anchored face/value record already gives the exact stored value on the first state.
  exact
    (storedBoundaryWitnessAndValues_ofAnchoredBoundaryFaceData
      (R := R) (M := M) hn
      (anchor := resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) pkg.tr.length)
      (state₁ := pkg.state₁) (state₂ := pkg.state₂)
      (q := (pkg.tr.get ⟨j, hj⟩).1) (v := (pkg.tr.get ⟨j, hj⟩).2)
      (pkg.hanchored j hj)).2.1

/-- Helper for Theorem 3.50: each anchored face/value record also gives the exact stored value
for the second hard state in the old package surface. -/
private theorem anchoredState₂Ref
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : AnchoredSeparatedPrefixPackage method R M ε hn t) :
    ∀ j (hj : j < pkg.tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
          ((pkg.tr.get ⟨j, hj⟩).1)) =
        (pkg.tr.get ⟨j, hj⟩).2 := by
  intro j hj
  -- The same anchored record gives the stored value on the second state as well.
  exact
    (storedBoundaryWitnessAndValues_ofAnchoredBoundaryFaceData
      (R := R) (M := M) hn
      (anchor := resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) pkg.tr.length)
      (state₁ := pkg.state₁) (state₂ := pkg.state₂)
      (q := (pkg.tr.get ⟨j, hj⟩).1) (v := (pkg.tr.get ⟨j, hj⟩).2)
      (pkg.hanchored j hj)).2.2

/-- Helper for Theorem 3.50: each anchored face/value record reconstructs the old
`StoredBoundaryWitness` required by the transcript-compatible pair package. -/
private theorem anchoredStoredBoundaryWitness
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : AnchoredSeparatedPrefixPackage method R M ε hn t) :
    ∀ j (hj : j < pkg.tr.length),
      StoredBoundaryWitness R hn pkg.state₁ pkg.state₂ ((pkg.tr.get ⟨j, hj⟩).1) := by
  intro j hj
  -- The witness component is the first projection of the same adapter theorem.
  exact
    (storedBoundaryWitnessAndValues_ofAnchoredBoundaryFaceData
      (R := R) (M := M) hn
      (anchor := resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) pkg.tr.length)
      (state₁ := pkg.state₁) (state₂ := pkg.state₂)
      (q := (pkg.tr.get ⟨j, hj⟩).1) (v := (pkg.tr.get ⟨j, hj⟩).2)
      (pkg.hanchored j hj)).1

/-- Helper for Theorem 3.50: once the anchored package is built, the original
`TranscriptCompatibleSeparatedPairPackage` is recovered by converting each anchored face/value
record through the adapter lemma above. -/
private def toTranscriptCompatibleSeparatedPairPackage
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : AnchoredSeparatedPrefixPackage method R M ε hn t) :
    TranscriptCompatibleSeparatedPairPackage method R M ε hn t :=
  { oracleBase := pkg.oracleBase
    tr := pkg.tr
    state₁ := pkg.state₁
    state₂ := pkg.state₂
    hlen := pkg.hlen
    hquery := pkg.hquery
    href := pkg.href
    hstate₁_ref := anchoredState₁Ref method hn pkg
    hstate₂_ref := anchoredState₂Ref method hn pkg
    hwitness := anchoredStoredBoundaryWitness method hn pkg
    hsep := pkg.hsep }

/-- Helper for Theorem 3.50: positive separation rules out any nonempty transcript-compatible
pair package, because its first stored witness would already force a common point of the two
current boxes. -/
private theorem transcriptCompatibleSeparatedPairPackage_length_eq_zero
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n) (hε : 0 < ε) (hM : 0 < (M : ℝ))
    (pkg : TranscriptCompatibleSeparatedPairPackage method R M ε hn t) :
    pkg.tr.length = 0 := by
  by_contra hlen_ne
  have hj : 0 < pkg.tr.length := Nat.pos_of_ne_zero hlen_ne
  obtain ⟨p, hp₁, hp₂⟩ :=
    commonPoint_ofStoredBoundaryWitness R hn pkg.state₁ pkg.state₂ (pkg.hwitness 0 hj)
  have hsep_at_p :
      2 * ε / (M : ℝ) < dist p p :=
    pkg.hsep p hp₁ p hp₂
  have hnot_lt : ¬ 2 * ε / (M : ℝ) < 0 := by
    exact not_lt_of_ge (by positivity)
  exact hnot_lt (by simpa using hsep_at_p)

/-- Helper for Theorem 3.50: the anchored package is also forced to have empty transcript under
positive separation, because every anchored entry induces the same common-point contradiction. -/
private theorem anchoredSeparatedPrefixPackage_length_eq_zero
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n) (hε : 0 < ε) (hM : 0 < (M : ℝ))
    (pkg : AnchoredSeparatedPrefixPackage method R M ε hn t) :
    pkg.tr.length = 0 := by
  by_contra hlen_ne
  have hj : 0 < pkg.tr.length := Nat.pos_of_ne_zero hlen_ne
  obtain ⟨p, hp₁, hp₂⟩ :=
    commonPoint_ofAnchoredBoundaryFaceData
      (R := R) (M := M) hn
      (anchor := resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) pkg.tr.length)
      (state₁ := pkg.state₁) (state₂ := pkg.state₂)
      (q := (pkg.tr.get ⟨0, hj⟩).1) (v := (pkg.tr.get ⟨0, hj⟩).2)
      (pkg.hanchored 0 hj)
  have hsep_at_p :
      2 * ε / (M : ℝ) < dist p p :=
    pkg.hsep p hp₁ p hp₂
  have hnot_lt : ¬ 2 * ε / (M : ℝ) < 0 := by
    exact not_lt_of_ge (by positivity)
  exact hnot_lt (by simpa using hsep_at_p)

/-- Helper for Theorem 3.50: the repaired private invariant keeps only the common reference
transcript, the exact stored hard values on the two final descendant boxes, and the final
separation hypothesis. This removes the false witness-carrying fields from the live route. -/
private structure TranscriptCompatibleSeparatedValuePackage
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (hn : 0 < n) (t : ℕ) where
  oracleBase : E → ℝ
  tr : List (E × ℝ)
  state₁ : FeasibilityResistingOracleState n
  state₂ : FeasibilityResistingOracleState n
  hlen : tr.length = t
  hquery :
    ∀ j (hj : j < tr.length),
      (method (linftyClosedBall R : Set E)).queryAfter
          (referenceOracleOfTranscript oracleBase tr) j =
        (tr.get ⟨j, hj⟩).1
  href :
    ∀ j (hj : j < tr.length),
      referenceOracleOfTranscript oracleBase tr ((tr.get ⟨j, hj⟩).1) =
        (tr.get ⟨j, hj⟩).2
  hstate₁_ref :
    ∀ j (hj : j < tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
          ((tr.get ⟨j, hj⟩).1)) =
        (tr.get ⟨j, hj⟩).2
  hstate₂_ref :
    ∀ j (hj : j < tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
          ((tr.get ⟨j, hj⟩).1)) =
        (tr.get ⟨j, hj⟩).2
  hsep :
    ∀ u ∈ state₁.currentBox (R : ℝ) hn,
      ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v

/-- Helper for Theorem 3.50: an empty transcript and any separated pair of descendant current
boxes already form the length-`0` value package, because there are no stored values to replay. -/
private def emptyTranscriptCompatibleSeparatedValuePackage
    {R M : NNReal} {ε : ℝ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    TranscriptCompatibleSeparatedValuePackage method R M ε hn 0 where
  oracleBase := oracleBase
  tr := []
  state₁ := state₁
  state₂ := state₂
  hlen := rfl
  hquery := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  href := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hstate₁_ref := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hstate₂_ref := by
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  hsep := hsep

/-- Helper for Theorem 3.50: once the geometric step supplies the old transcript values on two
new separated states together with one fresh common value at the appended query, the transcript
bookkeeping upgrades the value package by one step, while keeping the base oracle unchanged. -/
private theorem appendTranscriptCompatibleSeparatedValuePackage_nonempty
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ}
    (hq :
      q = (method (linftyClosedBall R : Set E)).queryAfter
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) t)
    (hstate₁_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hstate₂_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hvalue₁ :
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) q) = v)
    (hvalue₂ :
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn)) q) = v)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v' ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v') :
    ∃ pkg' : TranscriptCompatibleSeparatedValuePackage method R M ε hn (t + 1),
      pkg'.oracleBase = pkg.oracleBase := by
  classical
  let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
  let tr' : List (E × ℝ) := pkg.tr ++ [(q, v)]
  have hq_len :
      q = (method (linftyClosedBall R : Set E)).queryAfter oracleRef pkg.tr.length := by
    simpa [oracleRef, pkg.hlen] using hq
  have hstable :
      ∀ s < pkg.tr.length,
        (method (linftyClosedBall R : Set E)).queryAfter oracleRef s = q →
          oracleRef q = v := by
    intro s hs hsq
    have hquery_old :
        (method (linftyClosedBall R : Set E)).queryAfter oracleRef s =
          (pkg.tr.get ⟨s, hs⟩).1 :=
      pkg.hquery s hs
    have hquery_eq :
        (pkg.tr.get ⟨s, hs⟩).1 = q := by
      rw [← hquery_old]
      exact hsq
    have horacle_eq_old :
        oracleRef q = (pkg.tr.get ⟨s, hs⟩).2 := by
      rw [← hquery_eq]
      exact pkg.href s hs
    have hnew_eq_old :
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) q) =
          (pkg.tr.get ⟨s, hs⟩).2 := by
      rw [← hquery_eq]
      exact hstate₁_old s hs
    -- The old transcript already records the same value whenever the fresh query repeats.
    exact horacle_eq_old.trans (hnew_eq_old.symm.trans hvalue₁)
  refine
    ⟨({ oracleBase := pkg.oracleBase
        tr := tr'
        state₁ := state₁
        state₂ := state₂
        hlen := by
          -- The appended singleton is the only new transcript entry.
          simpa [tr', pkg.hlen]
        hquery := ?_
        href := ?_
        hstate₁_ref := ?_
        hstate₂_ref := ?_
        hsep := hsep } :
        TranscriptCompatibleSeparatedValuePackage method R M ε hn (t + 1)), rfl⟩
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- Earlier reference-path queries are unchanged on the left part of the append.
      have hprefix :
          (method (linftyClosedBall R : Set E)).queryAfter
              (referenceOracleOfTranscript pkg.oracleBase tr') j =
            (method (linftyClosedBall R : Set E)).queryAfter
              (referenceOracleOfTranscript pkg.oracleBase pkg.tr) j := by
        exact
          queryAfter_eq_of_referenceOracle_append_singleton_prefix
            (method (linftyClosedBall R : Set E)) pkg.oracleBase pkg.tr hstable
            (Nat.le_of_lt hj_old)
      calc
        (method (linftyClosedBall R : Set E)).queryAfter
            (referenceOracleOfTranscript pkg.oracleBase tr') j =
          (method (linftyClosedBall R : Set E)).queryAfter
            (referenceOracleOfTranscript pkg.oracleBase pkg.tr) j := hprefix
        _ = (pkg.tr.get ⟨j, hj_old⟩).1 := pkg.hquery j hj_old
        _ = (tr'.get ⟨j, hj⟩).1 := by
              simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The appended endpoint stores the actual fresh query point.
      have hprefix_last :
          (method (linftyClosedBall R : Set E)).queryAfter
              (referenceOracleOfTranscript pkg.oracleBase tr') pkg.tr.length =
            (method (linftyClosedBall R : Set E)).queryAfter oracleRef pkg.tr.length := by
        exact
          queryAfter_eq_of_referenceOracle_append_singleton_prefix
            (method (linftyClosedBall R : Set E)) pkg.oracleBase pkg.tr hstable le_rfl
      calc
        (method (linftyClosedBall R : Set E)).queryAfter
            (referenceOracleOfTranscript pkg.oracleBase tr') pkg.tr.length =
          (method (linftyClosedBall R : Set E)).queryAfter oracleRef pkg.tr.length := hprefix_last
        _ = q := hq_len.symm
        _ = (tr'.get ⟨pkg.tr.length, hj⟩).1 := by
              simp [tr', List.get_eq_getElem]
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · have hget_old :
          tr'.get ⟨j, hj⟩ = pkg.tr.get ⟨j, hj_old⟩ := by
        simp [tr', List.get_eq_getElem, List.getElem_append_left, hj_old]
      rw [hget_old]
      rw [referenceOracleOfTranscript_append_singleton]
      by_cases hsameq : (pkg.tr.get ⟨j, hj_old⟩).1 = q
      · have hquery_old :
            (method (linftyClosedBall R : Set E)).queryAfter
                (referenceOracleOfTranscript pkg.oracleBase pkg.tr) j = q := by
          rw [pkg.hquery j hj_old]
          exact hsameq
        have hstored_eq :
            (pkg.tr.get ⟨j, hj_old⟩).2 = v := by
          calc
            (pkg.tr.get ⟨j, hj_old⟩).2 =
                referenceOracleOfTranscript pkg.oracleBase pkg.tr
                  ((pkg.tr.get ⟨j, hj_old⟩).1) := by
                    symm
                    exact pkg.href j hj_old
            _ = referenceOracleOfTranscript pkg.oracleBase pkg.tr q := by rw [hsameq]
            _ = v := hstable j hj_old hquery_old
        have hsameq_elem : pkg.tr[j].1 = q := by
          simpa [List.get_eq_getElem] using hsameq
        have hstored_eq_elem : pkg.tr[j].2 = v := by
          simpa [List.get_eq_getElem] using hstored_eq
        simpa [Function.update, hsameq_elem, hstored_eq_elem]
      · have hsameq_elem : ¬ pkg.tr[j].1 = q := by
          simpa [List.get_eq_getElem] using hsameq
        simpa [Function.update, hsameq_elem] using pkg.href j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The appended singleton answers the new query by construction.
      simp [referenceOracleOfTranscript_append_singleton, tr', List.get_eq_getElem]
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- The new first state carries every old stored value unchanged.
      simpa [tr', List.get_eq_getElem, hj_old] using hstate₁_old j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- The fresh step records the new common value on the first state.
      simpa [tr', List.get_eq_getElem] using hvalue₁
  · intro j hj
    by_cases hj_old : j < pkg.tr.length
    · -- The second state realizes the same old transcript values as well.
      simpa [tr', List.get_eq_getElem, hj_old] using hstate₂_old j hj_old
    · have hj_bound : j < pkg.tr.length + 1 := by
        simpa [tr', pkg.hlen] using hj
      have hj_last : j = pkg.tr.length := by omega
      subst hj_last
      -- And it realizes the appended common value at the fresh query.
      simpa [tr', List.get_eq_getElem] using hvalue₂

/-- Helper for Theorem 3.50: choose the appended value package produced by the transcript
bookkeeping theorem above. The choice is harmless because the constructor theorem is already
deterministic up to the supplied data. -/
private noncomputable def appendTranscriptCompatibleSeparatedValuePackage
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ}
    (hq :
      q = (method (linftyClosedBall R : Set E)).queryAfter
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) t)
    (hstate₁_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hstate₂_old :
      ∀ j (hj : j < pkg.tr.length),
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) =
          (pkg.tr.get ⟨j, hj⟩).2)
    (hvalue₁ :
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) q) = v)
    (hvalue₂ :
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn)) q) = v)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v' ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v') :
    TranscriptCompatibleSeparatedValuePackage method R M ε hn (t + 1) :=
  Classical.choose <|
    appendTranscriptCompatibleSeparatedValuePackage_nonempty
      method hn pkg state₁ state₂ hq hstate₁_old hstate₂_old hvalue₁ hvalue₂ hsep

/-- Helper for Theorem 3.50: once a value package reaches length `T`, the generic
transcript/reference bridge already yields the queried-value equality on the first hard
transcript, and the package carries the final separation invariant directly. -/
private theorem sameQueryOfFinalTranscriptCompatibleValuePackage
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn T) :
    (∀ j : ℕ, j < T →
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) j)) =
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
          ((method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) j))) ∧
      (∀ u ∈ pkg.state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ pkg.state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) := by
  constructor
  · -- The value package keeps exactly the data consumed by the common-reference bridge.
    have hsame :=
      sameQueryValues_forTranscriptReferenceMatchedObjectives
        (method (linftyClosedBall R : Set E))
        pkg.oracleBase
        (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
        (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
        pkg.tr
        pkg.hquery
        pkg.href
        pkg.hstate₁_ref
        pkg.hstate₂_ref
    intro j hj
    have hj' : j < pkg.tr.length := by simpa [pkg.hlen] using hj
    simpa [pkg.hlen] using hsame j hj'
  · -- The package stores the final box separation verbatim.
    exact pkg.hsep

/-- Helper for Theorem 3.50: any separated pair of descendant current boxes seeds the repaired
value-only package at time `0`. -/
private theorem existsInitialTranscriptCompatibleSeparatedValuePackage_ofSeparatedStates
    {R M : NNReal} {ε : ℝ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (state₁ state₂ : FeasibilityResistingOracleState n)
    (hsep :
      ∀ u ∈ state₁.currentBox (R : ℝ) hn,
        ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) :
    ∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn 0,
      pkg.oracleBase = oracleBase := by
  -- The empty-package constructor already packages the seed pair.
  refine
    ⟨emptyTranscriptCompatibleSeparatedValuePackage
      method hn oracleBase state₁ state₂ hsep, rfl⟩

/-- Helper for Theorem 3.50: once a zero-length seed package and append-ready successor packages
are available over one fixed reference oracle, plain induction on the transcript length builds the
final value-only package. -/
private theorem existsTranscriptCompatibleSeparatedValuePackage_ofSeededSuccessor
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (oracleBase : E → ℝ)
    (hseededStep :
      (∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn 0,
          pkg.oracleBase = oracleBase) ∧
        (∀ {t : ℕ}, t < T →
          ∀ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t,
            pkg.oracleBase = oracleBase →
            ∃ pkg' : TranscriptCompatibleSeparatedValuePackage method R M ε hn (t + 1),
              pkg'.oracleBase = oracleBase)) :
    ∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn T,
      pkg.oracleBase = oracleBase := by
  rcases hseededStep with ⟨hseed, hstep⟩
  have hbuild :
      ∀ t ≤ T,
        ∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t,
          pkg.oracleBase = oracleBase := by
    intro t ht
    induction t with
    | zero =>
        -- The seed package is exactly the empty-transcript case.
        exact hseed
    | succ t iht =>
        -- Apply the append-ready successor theorem to the already-built prefix package.
        have ht_lt : t < T := by omega
        rcases iht (Nat.le_of_succ_le ht) with ⟨pkg, hpkg⟩
        exact hstep ht_lt pkg hpkg
  -- Evaluate the inductive builder at the target horizon.
  exact hbuild T le_rfl

/-- Helper for Theorem 3.50: the all-lower branch chain follows the lower-half successor for
exactly `k` consecutive midpoint splits, starting from the initial uncertainty box. -/
private def lowerHalfChain : ℕ → FeasibilityResistingOracleState n
  | 0 => FeasibilityResistingOracleState.initial
  | k + 1 => FeasibilityResistingOracleState.keepLowerHalf (lowerHalfChain k)

/-- Helper for Theorem 3.50: the all-upper branch chain follows the upper-half successor for
exactly `k` consecutive midpoint splits, starting from the same initial uncertainty box. -/
private def upperHalfChain : ℕ → FeasibilityResistingOracleState n
  | 0 => FeasibilityResistingOracleState.initial
  | k + 1 => FeasibilityResistingOracleState.keepUpperHalf (upperHalfChain k)

/-- Helper for Theorem 3.50: the lower-half chain records exactly one split at each recursive
step, so its depth is the chain length. -/
private theorem lowerHalfChain_depth
    (k : ℕ) :
    (lowerHalfChain (n := n) k).depth = k := by
  induction k with
  | zero =>
      -- The empty chain is the initial depth-`0` state.
      rfl
  | succ k ih =>
      -- Each lower-half extension increments the depth by one.
      simpa [lowerHalfChain, FeasibilityResistingOracleState.depth] using congrArg Nat.succ ih

/-- Helper for Theorem 3.50: the upper-half chain has the same depth profile as the lower-half
chain. -/
private theorem upperHalfChain_depth
    (k : ℕ) :
    (upperHalfChain (n := n) k).depth = k := by
  induction k with
  | zero =>
      -- The empty upper-chain is the same initial state.
      rfl
  | succ k ih =>
      -- Each upper-half extension also increments the depth by one.
      simpa [upperHalfChain, FeasibilityResistingOracleState.depth] using congrArg Nat.succ ih

/-- Helper for Theorem 3.50: along the all-lower chain, the lower bounds never move away from the
initial value `-R`. -/
private theorem lowerHalfChain_currentLower_eq
    (R : NNReal) (hn : 0 < n) (k : ℕ) (i : Fin n) :
    (lowerHalfChain (n := n) k).currentLower (R : ℝ) hn i = -(R : ℝ) := by
  induction k with
  | zero =>
      -- The initial box starts at `-R` in every coordinate.
      rfl
  | succ k ih =>
      -- The lower-half branch preserves the lower corner coordinatewise.
      simpa [lowerHalfChain] using ih

/-- Helper for Theorem 3.50: along the all-upper chain, the upper bounds never move away from the
initial value `R`. -/
private theorem upperHalfChain_currentUpper_eq
    (R : NNReal) (hn : 0 < n) (k : ℕ) (i : Fin n) :
    (upperHalfChain (n := n) k).currentUpper (R : ℝ) hn i = (R : ℝ) := by
  induction k with
  | zero =>
      -- The initial box starts at `R` in every coordinate.
      rfl
  | succ k ih =>
      -- The upper-half branch preserves the upper corner coordinatewise.
      simpa [upperHalfChain] using ih

/-- Helper for Theorem 3.50: the short-budget route first needs one empty-transcript separated
value package over the zero reference oracle. This isolates the seed geometry from the later
prefix-preserving successor construction. -/
private theorem lowerUpperHalfChainSeparatedAtZero
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∀ u ∈ (lowerHalfChain (n := n) (n + 1)).currentBox (R : ℝ) hn,
      ∀ v ∈ (upperHalfChain (n := n) (n + 1)).currentBox (R : ℝ) hn,
        2 * ε / (M : ℝ) < dist u v := by
  let i0 : Fin n := ⟨0, hn⟩
  have hbudget0 : (0 : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) := by
    -- The short-budget hypothesis already forces the logarithmic lower bound to be positive.
    exact lt_of_le_of_lt (by positivity : 0 ≤ (T : ℝ)) hbudget
  have hscale0 :
      4 * ε / (M : ℝ) < (R : ℝ) / 2 := by
    -- Specializing the radius lower bound at time `0` removes the `rpow` factor entirely.
    simpa using
      shortBudgetRadius_gt_fourEpsOverM
        (R := R) (M := M) (ε := ε) (T := 0) hn hε hM (by simpa using hbudget0)
  have hscale0' : 4 * ε < (R : ℝ) / 2 * (M : ℝ) := by
    -- Clear the positive denominator before comparing with the full coordinate gap `R`.
    exact (div_lt_iff₀ hM).mp hscale0
  have hstrong_gap : 8 * ε < (R : ℝ) * (M : ℝ) := by
    -- Doubling the radius estimate recovers a stronger inequality than the target gap needs.
    nlinarith
  have htarget_gap : 2 * ε / (M : ℝ) < (R : ℝ) := by
    -- The seed boxes are separated by a full gap of size `R` on coordinate `0`.
    exact (div_lt_iff₀ hM).2 <| by
      nlinarith [hstrong_gap]
  have hlower_width :
      (lowerHalfChain (n := n) (n + 1)).currentUpper (R : ℝ) hn i0 -
          (lowerHalfChain (n := n) (n + 1)).currentLower (R : ℝ) hn i0 =
        (R : ℝ) / 2 := by
    -- The coordinate-`0` width after one full cycle plus one extra lower split is exactly `R / 2`.
    have hprofile :=
      current_side_length_profile
        (R := (R : ℝ)) (hn := hn)
        (state := lowerHalfChain (n := n) (n + 1)) (i := i0)
    by_cases h1 : n = 1
    · -- In dimension `1`, the extra split completes a second full cycle.
      subst h1
      norm_num [i0, lowerHalfChain_depth] at hprofile
      ring_nf at hprofile ⊢
      exact hprofile
    · -- In higher dimensions, depth `n + 1` has quotient `1` and remainder `1`.
      have hn2 : 1 < n := by omega
      have hdiv : (n + 1) / n = 1 := by
        calc
          (n + 1) / n = 1 + 1 / n := by
            simpa [Nat.add_comm] using (Nat.add_mul_div_right 1 1 hn)
          _ = 1 := by simp [Nat.div_eq_of_lt hn2]
      have hmod : (n + 1) % n = 1 := by
        calc
          (n + 1) % n = 1 % n := by
            simpa [Nat.add_comm] using (Nat.add_mul_mod_self_left 1 1 n)
          _ = 1 := Nat.mod_eq_of_lt hn2
      simpa [i0, lowerHalfChain_depth, hdiv, hmod] using hprofile
  have hupper_width :
      (upperHalfChain (n := n) (n + 1)).currentUpper (R : ℝ) hn i0 -
          (upperHalfChain (n := n) (n + 1)).currentLower (R : ℝ) hn i0 =
        (R : ℝ) / 2 := by
    -- The upper-only chain has the same cyclic side-length profile.
    have hprofile :=
      current_side_length_profile
        (R := (R : ℝ)) (hn := hn)
        (state := upperHalfChain (n := n) (n + 1)) (i := i0)
    by_cases h1 : n = 1
    · -- The one-dimensional upper chain has the same second-cycle width.
      subst h1
      norm_num [i0, upperHalfChain_depth] at hprofile
      ring_nf at hprofile ⊢
      exact hprofile
    · -- The higher-dimensional case uses the same quotient/remainder calculation.
      have hn2 : 1 < n := by omega
      have hdiv : (n + 1) / n = 1 := by
        calc
          (n + 1) / n = 1 + 1 / n := by
            simpa [Nat.add_comm] using (Nat.add_mul_div_right 1 1 hn)
          _ = 1 := by simp [Nat.div_eq_of_lt hn2]
      have hmod : (n + 1) % n = 1 := by
        calc
          (n + 1) % n = 1 % n := by
            simpa [Nat.add_comm] using (Nat.add_mul_mod_self_left 1 1 n)
          _ = 1 := Nat.mod_eq_of_lt hn2
      simpa [i0, upperHalfChain_depth, hdiv, hmod] using hprofile
  have hlower_upper :
      (lowerHalfChain (n := n) (n + 1)).currentUpper (R : ℝ) hn i0 = -(R : ℝ) / 2 := by
    -- Combine the fixed lower corner with the width formula to identify the upper endpoint.
    have hlower_lower :=
      lowerHalfChain_currentLower_eq R hn (n + 1) i0
    nlinarith
  have hupper_lower :
      (upperHalfChain (n := n) (n + 1)).currentLower (R : ℝ) hn i0 = (R : ℝ) / 2 := by
    -- The upper chain keeps the top corner fixed, so its lower endpoint is `R / 2`.
    have hupper_upper :=
      upperHalfChain_currentUpper_eq R hn (n + 1) i0
    nlinarith
  intro u hu v hv
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn (lowerHalfChain (n := n) (n + 1))] at hu
  rw [currentBox_eq_currentBounds_set (R : ℝ) hn (upperHalfChain (n := n) (n + 1))] at hv
  have hu_le : u i0 ≤ -(R : ℝ) / 2 := by
    -- Every point in the lower-chain box lies below `-R / 2` on coordinate `0`.
    simpa [hlower_upper] using (hu i0).2
  have hv_ge : (R : ℝ) / 2 ≤ v i0 := by
    -- Every point in the upper-chain box lies above `R / 2` on coordinate `0`.
    simpa [hupper_lower] using (hv i0).1
  have hcoord_sep : (R : ℝ) ≤ |v i0 - u i0| := by
    -- The coordinate-`0` gap between the two boxes is at least `R`.
    have hnonneg : 0 ≤ v i0 - u i0 := by
      nlinarith
    rw [abs_of_nonneg hnonneg]
    nlinarith
  have hcoord_dist : |v i0 - u i0| ≤ dist u v := by
    -- One coordinate difference is bounded by the ambient Euclidean distance.
    calc
      |v i0 - u i0| = |(v - u) i0| := by simp
      _ ≤ ‖v - u‖ := abs_coordinate_le_norm (v - u) i0
      _ = dist v u := by rw [dist_eq_norm]
      _ = dist u v := dist_comm _ _
  calc
    2 * ε / (M : ℝ) < (R : ℝ) := htarget_gap
    _ ≤ |v i0 - u i0| := hcoord_sep
    _ ≤ dist u v := hcoord_dist

/-- Helper for Theorem 3.50: the short-budget route first needs one empty-transcript separated
value package over the zero reference oracle. This isolates the seed geometry from the later
prefix-preserving successor construction. -/
private theorem existsInitialTranscriptCompatibleSeparatedValuePackage_ofShortBudget
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn 0,
      pkg.oracleBase = fun _ : E ↦ 0 := by
  -- Seed the empty transcript with the two explicit branch chains whose current boxes are already
  -- separated on coordinate `0`.
  refine
    existsInitialTranscriptCompatibleSeparatedValuePackage_ofSeparatedStates
      method hn (fun _ : E ↦ 0)
      (lowerHalfChain (n := n) (n + 1))
      (upperHalfChain (n := n) (n + 1)) ?_
  -- The dedicated half-chain separation lemma supplies the required empty-transcript geometry.
  exact lowerUpperHalfChainSeparatedAtZero hn hε hM hbudget

/-- Helper for Theorem 3.50: `AnchorFaceValueOnState R M hn anchor state q v` records that one
state preserves one exposed lower or upper face of the anchor box for `q`, keeps every other
coordinate of `q` inside its current box, and stores the anchor-side scaled distance value `v`. -/
private def AnchorFaceValueOnState
    (R M : NNReal) (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    (q : E) (v : ℝ) : Prop :=
  ∃ i : Fin n,
    ((q i ≤ anchor.currentLower (R : ℝ) hn i ∧
        state.currentLower (R : ℝ) hn i = anchor.currentLower (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          anchor.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ anchor.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state.currentUpper (R : ℝ) hn j) ∧
        (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v) ∨
      (anchor.currentUpper (R : ℝ) hn i ≤ q i ∧
        state.currentUpper (R : ℝ) hn i = anchor.currentUpper (R : ℝ) hn i ∧
        (∀ j : Fin n, j ≠ i →
          anchor.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ anchor.currentUpper (R : ℝ) hn j) ∧
        (∀ j : Fin n, j ≠ i →
          state.currentLower (R : ℝ) hn j ≤ q j ∧
            q j ≤ state.currentUpper (R : ℝ) hn j) ∧
        (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v))

/-- Helper for Theorem 3.50: direct boundary data for one query on an anchor box, together with
the matching preserved face and coordinate containment on one child box, packages immediately into
`AnchorFaceValueOnState`. -/
private theorem anchorFaceValueOnState_ofBoundaryData
    {R M : NNReal} (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ} {i : Fin n}
    (hboundary :
      q i ≤ anchor.currentLower (R : ℝ) hn i ∨
        anchor.currentUpper (R : ℝ) hn i ≤ q i)
    (hinside_anchor :
      ∀ j : Fin n, j ≠ i →
        anchor.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ anchor.currentUpper (R : ℝ) hn j)
    (hinside_state :
      ∀ j : Fin n, j ≠ i →
        state.currentLower (R : ℝ) hn j ≤ q j ∧
          q j ≤ state.currentUpper (R : ℝ) hn j)
    (hvalue :
      (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v)
    (hlower :
      q i ≤ anchor.currentLower (R : ℝ) hn i →
        state.currentLower (R : ℝ) hn i =
          anchor.currentLower (R : ℝ) hn i)
    (hupper :
      anchor.currentUpper (R : ℝ) hn i ≤ q i →
        state.currentUpper (R : ℝ) hn i =
          anchor.currentUpper (R : ℝ) hn i) :
    AnchorFaceValueOnState R M hn anchor state q v := by
  rcases hboundary with hlower_q | hupper_q
  · -- The lower-face branch keeps the anchored lower value and all other coordinates inside.
    refine ⟨i, Or.inl ?_⟩
    exact ⟨hlower_q, hlower hlower_q, hinside_anchor, hinside_state, hvalue⟩
  · -- The upper-face branch is identical after switching to the preserved upper face.
    refine ⟨i, Or.inr ?_⟩
    exact ⟨hupper_q, hupper hupper_q, hinside_anchor, hinside_state, hvalue⟩

/-- Helper for Theorem 3.50: a one-state anchor-face certificate immediately transports the
anchor-side scaled distance value to the child state. -/
private theorem stateValue_eq_ofAnchorFaceValueOnState
    {R M : NNReal} (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    {q : E} {v : ℝ}
    (hface : AnchorFaceValueOnState R M hn anchor state q v) :
    ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state.currentBox (R : ℝ) hn)) q) = v := by
  rcases hface with ⟨i, hlower | hupper⟩
  · rcases hlower with ⟨hqi, hface_state, hinside_anchor, hinside_state, hv_anchor⟩
    -- Rewrite the child value through the preserved lower anchor face.
    calc
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state.currentBox (R : ℝ) hn)) q) =
          (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
            exact
              scaledInfDist_eq_of_preservedLowerBoundaryFace
                R M hn anchor state hface_state hqi hinside_anchor hinside_state
      _ = v := hv_anchor
  · rcases hupper with ⟨hqi, hface_state, hinside_anchor, hinside_state, hv_anchor⟩
    -- The upper-face branch is identical after switching to the upper-gap transport lemma.
    calc
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state.currentBox (R : ℝ) hn)) q) =
          (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := by
            exact
              scaledInfDist_eq_of_preservedUpperBoundaryFace
                R M hn anchor state hface_state hqi hinside_anchor hinside_state
      _ = v := hv_anchor

/-- Helper for Theorem 3.50: an anchor-face replay family records that one state carries
anchor-face certificates for every stored transcript entry relative to the same anchor. -/
private def anchorFaceReplayFamily
    (R M : NNReal) (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    (tr : List (E × ℝ)) : Prop :=
  ∀ j (hj : j < tr.length),
    AnchorFaceValueOnState R M hn anchor state
      ((tr.get ⟨j, hj⟩).1) ((tr.get ⟨j, hj⟩).2)

/-- Helper for Theorem 3.50: once one state carries the anchored replay family, every stored
transcript value is recovered on that state by the existing one-query transport lemma. -/
private theorem stateValueReplay_of_anchorFaceReplayFamily
    {R M : NNReal} (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    {tr : List (E × ℝ)}
    (hfamily : anchorFaceReplayFamily R M hn anchor state tr) :
    ∀ j (hj : j < tr.length),
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state.currentBox (R : ℝ) hn))
          ((tr.get ⟨j, hj⟩).1)) =
        (tr.get ⟨j, hj⟩).2 := by
  intro j hj
  -- Apply the one-query anchor-face transport to the `j`th stored transcript entry.
  exact
    stateValue_eq_ofAnchorFaceValueOnState
      (R := R) (M := M) hn anchor state
      (q := (tr.get ⟨j, hj⟩).1) (v := (tr.get ⟨j, hj⟩).2)
      (hfamily j hj)

/-- Helper for Theorem 3.50: the lower side strip keeps the anchor current box and moves strictly
below the active midpoint coordinate by `δ`. -/
private def lowerSideStrip
    (R : NNReal) (hn : 0 < n) (anchor : FeasibilityResistingOracleState n) (δ : ℝ) : Set E :=
  {x : E |
    x ∈ anchor.currentBox (R : ℝ) hn ∧
      x (anchor.nextCoord hn) <
        (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) - δ}

/-- Helper for Theorem 3.50: the upper side strip keeps the anchor current box and moves strictly
above the active midpoint coordinate by `δ`. -/
private def upperSideStrip
    (R : NNReal) (hn : 0 < n) (anchor : FeasibilityResistingOracleState n) (δ : ℝ) : Set E :=
  {x : E |
    x ∈ anchor.currentBox (R : ℝ) hn ∧
      (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) + δ <
        x (anchor.nextCoord hn)}

/-- Helper for Theorem 3.50: a protected Euclidean ball around the anchor center already contains
one point in the lower side strip. -/
private theorem lowerSideStrip_nonempty_of_room
    {R : NNReal} {ρ δ : ℝ}
    (hn : 0 < n) (anchor : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hball :
      Metric.closedBall (anchor.currentCenter (R : ℝ) hn) ρ ⊆ anchor.currentBox (R : ℝ) hn)
    (hroom : 2 * δ < ρ) :
    (lowerSideStrip R hn anchor δ).Nonempty := by
  let center := anchor.currentCenter (R : ℝ) hn
  let direction : E := EuclideanSpace.single (anchor.nextCoord hn) (1 : ℝ)
  let x : E := center - (2 * δ) • direction
  have hdir_norm : ‖direction‖ = 1 := by
    simp [direction, EuclideanSpace.single]
  have hdist : dist x center = 2 * δ := by
    -- The witness point is shifted by exactly `2δ` on the active coordinate axis.
    rw [dist_eq_norm]
    calc
      ‖x - center‖ = ‖-((2 * δ : ℝ) • direction)‖ := by
        congr 1
        simp [x, center, sub_eq_add_neg]
      _ = ‖(2 * δ : ℝ) • direction‖ := by rw [norm_neg]
      _ = |2 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 2 * δ := by simp [hdir_norm, hδ.le]
  have hx_box : x ∈ anchor.currentBox (R : ℝ) hn := by
    -- The protected-ball hypothesis puts the shifted point back inside the anchor box.
    refine hball ?_
    rw [Metric.mem_closedBall, hdist]
    exact le_of_lt hroom
  have hx_strip :
      x (anchor.nextCoord hn) <
        (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) - δ := by
    -- On the active coordinate, the shift lands strictly below the midpoint by `δ`.
    simp [x, center, direction, EuclideanSpace.single]
    nlinarith
  exact ⟨x, hx_box, hx_strip⟩

/-- Helper for Theorem 3.50: the same protected ball also contains one point in the upper side
strip. -/
private theorem upperSideStrip_nonempty_of_room
    {R : NNReal} {ρ δ : ℝ}
    (hn : 0 < n) (anchor : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hball :
      Metric.closedBall (anchor.currentCenter (R : ℝ) hn) ρ ⊆ anchor.currentBox (R : ℝ) hn)
    (hroom : 2 * δ < ρ) :
    (upperSideStrip R hn anchor δ).Nonempty := by
  let center := anchor.currentCenter (R : ℝ) hn
  let direction : E := EuclideanSpace.single (anchor.nextCoord hn) (1 : ℝ)
  let x : E := center + (2 * δ) • direction
  have hdir_norm : ‖direction‖ = 1 := by
    simp [direction, EuclideanSpace.single]
  have hdist : dist x center = 2 * δ := by
    -- The upper witness is the symmetric `2δ` shift on the same unit axis.
    rw [dist_eq_norm]
    calc
      ‖x - center‖ = ‖(2 * δ : ℝ) • direction‖ := by
        congr 1
        simp [x, center]
      _ = |2 * δ| * ‖direction‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = 2 * δ := by simp [hdir_norm, hδ.le]
  have hx_box : x ∈ anchor.currentBox (R : ℝ) hn := by
    -- The same protected-ball argument handles the symmetric upper witness.
    refine hball ?_
    rw [Metric.mem_closedBall, hdist]
    exact le_of_lt hroom
  have hx_strip :
      (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) + δ <
        x (anchor.nextCoord hn) := by
    -- The active coordinate now lies strictly above the midpoint by `δ`.
    simp [x, center, direction, EuclideanSpace.single]
    nlinarith
  exact ⟨x, hx_box, hx_strip⟩

/-- Helper for Theorem 3.50: points in opposite side strips are already separated by the target
coordinate gap. -/
private theorem separated_of_mem_oppositeSideStrips
    {R : NNReal} {δ : ℝ}
    (hn : 0 < n) (anchor : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    {u v : E}
    (hu : u ∈ lowerSideStrip R hn anchor δ)
    (hv : v ∈ upperSideStrip R hn anchor δ) :
    2 * δ < dist u v := by
  rcases hu with ⟨_, hu_coord⟩
  rcases hv with ⟨_, hv_coord⟩
  let i : Fin n := anchor.nextCoord hn
  have hcoord_gap : 2 * δ < v i - u i := by
    -- The midpoint gap on the active coordinate already exceeds `2δ`.
    nlinarith
  have hcoord_abs : 2 * δ < |v i - u i| := by
    have hnonneg : 0 ≤ v i - u i := by
      nlinarith
    rwa [abs_of_nonneg hnonneg]
  have hcoord_dist : |v i - u i| ≤ dist u v := by
    -- One coordinate difference is bounded by the ambient Euclidean distance.
    calc
      |v i - u i| = |(v - u) i| := by simp
      _ ≤ ‖v - u‖ := abs_coordinate_le_norm (v - u) i
      _ = dist v u := by rw [dist_eq_norm]
      _ = dist u v := dist_comm _ _
  exact lt_of_lt_of_le hcoord_abs hcoord_dist

/-- Helper for Theorem 3.50: if two descendant current boxes lie in opposite side strips of the
same anchor, their points are uniformly separated by more than `2δ`. -/
private theorem separated_of_oppositeSideStripDescendants
    {R : NNReal} {δ : ℝ}
    (hn : 0 < n)
    (anchor state₁ state₂ : FeasibilityResistingOracleState n)
    (hδ : 0 < δ)
    (hstate₁ :
      state₁.currentBox (R : ℝ) hn ⊆ lowerSideStrip R hn anchor δ)
    (hstate₂ :
      state₂.currentBox (R : ℝ) hn ⊆ upperSideStrip R hn anchor δ) :
    ∀ u ∈ state₁.currentBox (R : ℝ) hn,
      ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * δ < dist u v := by
  intro u hu v hv
  -- Push both box points to the strip surface and reuse the pointwise separation lemma.
  exact
    separated_of_mem_oppositeSideStrips
      (R := R) (δ := δ) hn anchor hδ (hstate₁ hu) (hstate₂ hv)

/-- Helper for Theorem 3.50: every point in the lower side strip already lies in the immediate
lower-half child of the anchor. This is the first containment step toward a stricter lower-strip
descendant. -/
private theorem lowerSideStrip_subset_keepLowerHalf_currentBox
    {R : NNReal} {δ : ℝ}
    (hn : 0 < n) (anchor : FeasibilityResistingOracleState n)
    (hδ : 0 ≤ δ) :
    lowerSideStrip R hn anchor δ ⊆
      (FeasibilityResistingOracleState.keepLowerHalf anchor).currentBox (R : ℝ) hn := by
  intro x hx
  rcases hx with ⟨hx_box, hx_strip⟩
  have hside :
      x (anchor.nextCoord hn) ≤
        (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) := by
    nlinarith
  -- The side-strip inequality is stronger than the midpoint inequality required by the fixed
  -- lower-half containment lemma.
  exact
    mem_keepLowerHalf_currentBox_of_mem_currentBox_of_le_center
      R hn anchor hx_box hside

/-- Helper for Theorem 3.50: every point in the upper side strip already lies in the immediate
upper-half child of the anchor. This is the symmetric first containment step for the upper side.
-/
private theorem upperSideStrip_subset_keepUpperHalf_currentBox
    {R : NNReal} {δ : ℝ}
    (hn : 0 < n) (anchor : FeasibilityResistingOracleState n)
    (hδ : 0 ≤ δ) :
    upperSideStrip R hn anchor δ ⊆
      (FeasibilityResistingOracleState.keepUpperHalf anchor).currentBox (R : ℝ) hn := by
  intro x hx
  rcases hx with ⟨hx_box, hx_strip⟩
  have hside :
      (anchor.currentCenter (R : ℝ) hn) (anchor.nextCoord hn) ≤
        x (anchor.nextCoord hn) := by
    nlinarith
  -- The upper strip likewise strengthens the midpoint inequality needed by the upper-half child.
  exact
    mem_keepUpperHalf_currentBox_of_mem_currentBox_of_center_le
      R hn anchor hx_box hside

/-- Helper for Theorem 3.50: if a descendant current box sits inside an anchor box and already
contains a replay witness realizing the anchor-side value, then the descendant realizes the same
exact value as well. -/
private theorem stateValue_eq_ofReplayWitnessAndSubset
    {R M : NNReal} (hn : 0 < n)
    (anchor state : FeasibilityResistingOracleState n)
    {q p : E} {v : ℝ}
    (hsubset :
      state.currentBox (R : ℝ) hn ⊆ anchor.currentBox (R : ℝ) hn)
    (hp_mem : p ∈ state.currentBox (R : ℝ) hn)
    (hp_value : (M : ℝ) * dist q p = v)
    (hv_anchor :
      (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) = v) :
    ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state.currentBox (R : ℝ) hn)) q) = v := by
  have hstate_nonempty : (state.currentBox (R : ℝ) hn).Nonempty :=
    (currentBox_nonempty_isClosed_convex R hn state).1
  have hanchor_le_state :
      Metric.infDist q (anchor.currentBox (R : ℝ) hn) ≤
        Metric.infDist q (state.currentBox (R : ℝ) hn) := by
    -- Any point of the descendant box is also a point of the anchor box, so the anchor infimum
    -- distance is a lower bound for the descendant infimum distance.
    rw [Metric.le_infDist hstate_nonempty]
    intro y hy
    exact Metric.infDist_le_dist_of_mem (hsubset hy)
  have hstate_le_witness :
      Metric.infDist q (state.currentBox (R : ℝ) hn) ≤ dist q p :=
    Metric.infDist_le_dist_of_mem hp_mem
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  have hscaled_anchor_le_state :
      (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) ≤
        (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) :=
    mul_le_mul_of_nonneg_left hanchor_le_state hM_nonneg
  have hscaled_state_le_v :
      (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) ≤ v := by
    calc
      (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) ≤
          (M : ℝ) * dist q p :=
        mul_le_mul_of_nonneg_left hstate_le_witness hM_nonneg
      _ = v := hp_value
  have hv_le_state :
      v ≤ (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) := by
    calc
      v = (M : ℝ) * Metric.infDist q (anchor.currentBox (R : ℝ) hn) := hv_anchor.symm
      _ ≤ (M : ℝ) * Metric.infDist q (state.currentBox (R : ℝ) hn) :=
        hscaled_anchor_le_state
  -- The witness gives the upper bound and box inclusion gives the lower bound, so the descendant
  -- value is pinned down exactly.
  exact le_antisymm hscaled_state_le_v hv_le_state

/-- Helper for Theorem 3.50: the fresh query at time `t` already has a normalized boundary
projection in the next common resisting-prefix anchor. -/
private theorem freshQueryNormalizedAtNextAnchor
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    ∃ p : E,
      p ∈ anchorNext.currentBox (R : ℝ) hn ∧
      (M : ℝ) * dist q p = (M : ℝ) * Metric.infDist q (anchorNext.currentBox (R : ℝ) hn) ∧
      ∃ i : Fin n,
        ((p i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
            anchorNext.currentUpper (R : ℝ) hn i ≤ p i) ∧
          ∀ j : Fin n, j ≠ i →
            anchorNext.currentLower (R : ℝ) hn j ≤ p j ∧
              p j ≤ anchorNext.currentUpper (R : ℝ) hn j) := by
  dsimp
  have hq_strict :
      (method (linftyClosedBall R : Set E)).queryAfter
          (referenceOracleOfTranscript pkg.oracleBase pkg.tr) t ∉
        strictCurrentBox R hn
          (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
            (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1)) := by
    -- The generic prefix lemma excludes the fresh query from the next strict current box.
    simpa using
      queryAfter_not_mem_final_strictCurrentBox_of_lt
        (R := R) (hn := hn)
        (algorithm := method (linftyClosedBall R : Set E))
        (oracle := referenceOracleOfTranscript pkg.oracleBase pkg.tr)
        (j := t) (T := t + 1)
        (by omega)
  -- Normalize the fresh query by projecting it to the exposed face of the next anchor box.
  exact
    normalizedBoundaryProjectionOfQueryOutsideStrictCurrentBox
      (R := R) (M := M) hn
      (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1))
      hq_strict

/-- Helper for Theorem 3.50: every previously recorded query also has a normalized boundary
projection in the same next anchor box. -/
private theorem recordedQueryNormalizedAtNextAnchor
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    ∀ j (hj : j < pkg.tr.length),
      ∃ p : E,
        p ∈ anchorNext.currentBox (R : ℝ) hn ∧
        (M : ℝ) * dist ((pkg.tr.get ⟨j, hj⟩).1) p =
            (M : ℝ) *
              Metric.infDist ((pkg.tr.get ⟨j, hj⟩).1) (anchorNext.currentBox (R : ℝ) hn) ∧
        ∃ i : Fin n,
          ((p i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
              anchorNext.currentUpper (R : ℝ) hn i ≤ p i) ∧
            ∀ k : Fin n, k ≠ i →
              anchorNext.currentLower (R : ℝ) hn k ≤ p k ∧
                p k ≤ anchorNext.currentUpper (R : ℝ) hn k) := by
  dsimp
  intro j hj
  have hj_succ : j < t + 1 := by
    have hj_t : j < t := by simpa [pkg.hlen] using hj
    omega
  have hquery_strict :
      (pkg.tr.get ⟨j, hj⟩).1 ∉
        strictCurrentBox R hn
          (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
            (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1)) := by
    -- Every old query stays outside all later strict prefix boxes, including the next anchor.
    rw [← pkg.hquery j hj]
    simpa using
      queryAfter_not_mem_final_strictCurrentBox_of_lt
        (R := R) (hn := hn)
        (algorithm := method (linftyClosedBall R : Set E))
        (oracle := referenceOracleOfTranscript pkg.oracleBase pkg.tr)
        (j := j) (T := t + 1)
        hj_succ
  -- Normalize the recorded query in the same way as the fresh query.
  exact
    normalizedBoundaryProjectionOfQueryOutsideStrictCurrentBox
      (R := R) (M := M) hn
      (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
        (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1))
      hquery_strict

/-- Helper for Theorem 3.50: the fresh next query already has a direct exposed-face witness in
the next common anchor box. At this stage only the exposed coordinate is needed; the stronger
all-other-coordinates-inside package is not yet available on the live route. -/
private theorem freshQueryBoundaryAtNextAnchor
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    ∃ i : Fin n,
      (q i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
        anchorNext.currentUpper (R : ℝ) hn i ≤ q i) := by
  dsimp
  -- The generic prefix witness theorem applies directly to the fresh query at index `t`.
  simpa using
    existsBoundaryWitness_for_queryAfter_of_lt
      (R := R) hn
      (method (linftyClosedBall R : Set E))
      (referenceOracleOfTranscript pkg.oracleBase pkg.tr)
      (j := t) (T := t + 1)
      (by omega)

/-- Helper for Theorem 3.50: every recorded query also keeps a direct exposed-face witness in the
same next anchor box. This is the transcript-level boundary surface currently justified by the
prefix recursion. -/
private theorem recordedQueryBoundaryAtNextAnchor
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    ∀ j (hj : j < pkg.tr.length),
      ∃ i : Fin n,
        (((pkg.tr.get ⟨j, hj⟩).1) i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
          anchorNext.currentUpper (R : ℝ) hn i ≤ ((pkg.tr.get ⟨j, hj⟩).1) i) := by
  dsimp
  intro j hj
  have hj_succ : j < t + 1 := by
    have hj_t : j < t := by simpa [pkg.hlen] using hj
    omega
  -- Rewriting the recorded transcript query back to its realized query index exposes the generic
  -- boundary witness theorem on the same next prefix anchor.
  simpa [pkg.hquery j hj] using
    existsBoundaryWitness_for_queryAfter_of_lt
      (R := R) hn
      (method (linftyClosedBall R : Set E))
      (referenceOracleOfTranscript pkg.oracleBase pkg.tr)
      (j := j) (T := t + 1)
      hj_succ

/-- Helper for Theorem 3.50: the short-budget room inside the next anchor yields nonempty lower
and upper side strips that are already quantitatively separated. -/
private theorem nextAnchorSideStripData
    {R M : NNReal} {ε : ℝ} {T t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)))
    (ht_succ : t + 1 ≤ T)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    let lowerStrip := lowerSideStrip R hn anchorNext (ε / (M : ℝ))
    let upperStrip := upperSideStrip R hn anchorNext (ε / (M : ℝ))
    lowerStrip.Nonempty ∧
      upperStrip.Nonempty ∧
        (∀ u ∈ lowerStrip, ∀ v ∈ upperStrip, 2 * ε / (M : ℝ) < dist u v) := by
  dsimp
  obtain ⟨ρ, hroom, hball⟩ :=
    shortBudgetRoomInPrefixState
      (R := R) (M := M) (ε := ε) (T := T) (t := t + 1)
      (algorithm := method (linftyClosedBall R : Set E))
      (oracle := referenceOracleOfTranscript pkg.oracleBase pkg.tr)
      hn hε hM ht_succ hbudget
  have hδ : 0 < ε / (M : ℝ) := by positivity
  constructor
  · -- The protected ball reaches a point strictly below the active midpoint.
    exact
      lowerSideStrip_nonempty_of_room
        (R := R) (ρ := ρ) (δ := ε / (M : ℝ))
        hn
        (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
          (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1))
        hδ hball (by nlinarith [hroom])
  constructor
  · -- The same room also reaches a symmetric point above the active midpoint.
    exact
      upperSideStrip_nonempty_of_room
        (R := R) (ρ := ρ) (δ := ε / (M : ℝ))
        hn
        (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
          (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1))
        hδ hball (by nlinarith [hroom])
  · intro u hu v hv
    -- Opposite strips are already separated on the active coordinate by more than `2 ε / M`.
    have hsep :
        2 * (ε / (M : ℝ)) < dist u v :=
      separated_of_mem_oppositeSideStrips
        (R := R) (δ := ε / (M : ℝ)) hn
        (resistingPrefixState R hn (method (linftyClosedBall R : Set E))
          (referenceOracleOfTranscript pkg.oracleBase pkg.tr) (t + 1))
        hδ hu hv
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsep

/-- Helper for Theorem 3.50: any hard objective that realizes the stored values of a
`TranscriptCompatibleSeparatedValuePackage` follows the same reference-query prefix as the folded
reference oracle. -/
private theorem queryAfter_eq_reference_ofTranscriptCompatibleValuePackageObjective
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    {φ : E → ℝ}
    (hφ_ref :
      ∀ j (hj : j < pkg.tr.length), φ ((pkg.tr.get ⟨j, hj⟩).1) = (pkg.tr.get ⟨j, hj⟩).2) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    ∀ j : ℕ, j ≤ pkg.tr.length →
      (method (linftyClosedBall R : Set E)).queryAfter φ j =
        (method (linftyClosedBall R : Set E)).queryAfter oracleRef j := by
  dsimp
  intro j hj
  -- Rebuild the whole query prefix from equality of oracle values on the realized hard path.
  refine
    queryAfter_eq_of_same_query_values
      (method (linftyClosedBall R : Set E))
      φ
      (referenceOracleOfTranscript pkg.oracleBase pkg.tr)
      (j := j) ?_
  intro m hm
  have hm_len : m < pkg.tr.length := lt_of_lt_of_le hm hj
  have hsame :
      φ
          ((method (linftyClosedBall R : Set E)).queryAfter
            φ m) =
        referenceOracleOfTranscript pkg.oracleBase pkg.tr
          ((method (linftyClosedBall R : Set E)).queryAfter φ m) :=
    sameQueryValues_forTranscriptReferenceMatchedObjectives
      (method (linftyClosedBall R : Set E))
      pkg.oracleBase
      φ
      (referenceOracleOfTranscript pkg.oracleBase pkg.tr)
      pkg.tr
      pkg.hquery
      pkg.href
      hφ_ref
      pkg.href
      m
      hm_len
  simpa using hsame

/-- Helper for Theorem 3.50: once an objective realizes the stored transcript values, it induces
the same next resisting-prefix anchor as the folded reference oracle. -/
private theorem resistingPrefixState_eq_of_same_queryPrefix
    {R : NNReal} {T : ℕ}
    (hn : 0 < n)
    (algorithm : DeterministicValueOracleMethod E)
    (oracle₁ oracle₂ : E → ℝ)
    (hquery :
      ∀ j : ℕ, j < T → algorithm.queryAfter oracle₁ j = algorithm.queryAfter oracle₂ j) :
    resistingPrefixState R hn algorithm oracle₁ T =
      resistingPrefixState R hn algorithm oracle₂ T := by
  induction T with
  | zero =>
      -- The empty prefix anchor is the initial state for both oracles.
      simp [resistingPrefixState]
  | succ T ih =>
      -- The successor anchors coincide once the shorter prefix anchors and the fresh queries agree.
      rw [resistingPrefixState_succ, resistingPrefixState_succ]
      have hprefix :
          ∀ j : ℕ, j < T → algorithm.queryAfter oracle₁ j = algorithm.queryAfter oracle₂ j := by
        intro j hj
        exact hquery j (Nat.lt_trans hj (Nat.lt_succ_self T))
      rw [ih hprefix]
      rw [hquery T (Nat.lt_succ_self T)]

/-- Helper for Theorem 3.50: any objective that realizes the stored transcript values already
shares both the next query and the next resisting-prefix anchor with the folded reference oracle.
This packages the solved prefix-synchronization step once so the final hole only sees the fresh
descendant geometry. -/
private theorem nextQueryAndAnchor_eq_ofTranscriptCompatibleValuePackageObjective
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    {φ : E → ℝ}
    (hφ_ref :
      ∀ j (hj : j < pkg.tr.length), φ ((pkg.tr.get ⟨j, hj⟩).1) = (pkg.tr.get ⟨j, hj⟩).2) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let q :=
      (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
    let anchorNext :=
      resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
    (method (linftyClosedBall R : Set E)).queryAfter φ t = q ∧
      resistingPrefixState R hn
          (method (linftyClosedBall R : Set E))
          φ
          (t + 1) =
        anchorNext := by
  dsimp
  constructor
  · -- The whole realized prefix forces the next query point to match the reference one.
    have ht_len : t ≤ pkg.tr.length := by simpa [pkg.hlen]
    have hquery_sync :=
      queryAfter_eq_reference_ofTranscriptCompatibleValuePackageObjective
        (R := R) (M := M) (ε := ε) (method := method) hn pkg
        (φ := φ) hφ_ref
    simpa using hquery_sync t ht_len
  · -- The synchronized prefix also determines the next resisting-prefix anchor uniquely.
    apply resistingPrefixState_eq_of_same_queryPrefix (R := R) (hn := hn)
    intro j hj
    have hj_len : j ≤ pkg.tr.length := by
      simpa [pkg.hlen] using Nat.le_of_lt_succ hj
    have hquery_sync :=
      queryAfter_eq_reference_ofTranscriptCompatibleValuePackageObjective
        (R := R) (M := M) (ε := ε) (method := method) hn pkg
        (φ := φ) hφ_ref
    simpa using hquery_sync j hj_len

/-- Helper for Theorem 3.50: if the next reference query is already present in the stored
transcript, then the existing separated package states already provide the append-ready replay
data. This isolates the nontrivial work to the genuinely fresh-query branch. -/
private theorem existsSeparatedNextStatesWithValueReplay_ofRepeatedQuery
    {R M : NNReal} {ε : ℝ} {t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
    (∃ j, ∃ hj : j < pkg.tr.length, (pkg.tr.get ⟨j, hj⟩).1 = q) →
      ∃ state₁ state₂ : FeasibilityResistingOracleState n,
        ∃ v : ℝ,
          (∀ j (hj : j < pkg.tr.length),
            ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
                ((pkg.tr.get ⟨j, hj⟩).1)) =
              ((pkg.tr.get ⟨j, hj⟩).2)) ∧
          (∀ j (hj : j < pkg.tr.length),
            ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
                ((pkg.tr.get ⟨j, hj⟩).1)) =
              ((pkg.tr.get ⟨j, hj⟩).2)) ∧
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) q) = v ∧
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn)) q) = v ∧
          (∀ u ∈ state₁.currentBox (R : ℝ) hn,
            ∀ v' ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v') := by
  let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
  let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
  dsimp [oracleRef, q]
  intro hrepeat
  rcases hrepeat with ⟨j, hj, hqj⟩
  have hqj_get : q = (pkg.tr.get ⟨j, hj⟩).1 := by
    simpa [q, List.get_eq_getElem] using hqj.symm
  -- The stored transcript value at the repeated query already synchronizes both package states.
  refine ⟨pkg.state₁, pkg.state₂, (pkg.tr.get ⟨j, hj⟩).2, ?_⟩
  refine ⟨pkg.hstate₁_ref, pkg.hstate₂_ref, ?_, ?_, pkg.hsep⟩
  · -- Rewrite the fresh target query back to the earlier stored transcript point on the first side.
    calc
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) q) =
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) := by
              exact
                congrArg
                  (fun x : E ↦
                    (fun y : E ↦
                      (M : ℝ) * Metric.infDist y (pkg.state₁.currentBox (R : ℝ) hn)) x)
                  hqj_get
      _ = (pkg.tr.get ⟨j, hj⟩).2 := pkg.hstate₁_ref j hj
  · -- The same repeated-query rewrite works for the second separated package state.
    calc
      ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn)) q) =
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
            ((pkg.tr.get ⟨j, hj⟩).1)) := by
              exact
                congrArg
                  (fun x : E ↦
                    (fun y : E ↦
                      (M : ℝ) * Metric.infDist y (pkg.state₂.currentBox (R : ℝ) hn)) x)
                  hqj_get
      _ = (pkg.tr.get ⟨j, hj⟩).2 := pkg.hstate₂_ref j hj

/-- Helper for Theorem 3.50: the remaining private blocker is now the minimal append-ready
geometric step. It must choose two separated descendant states that keep every old transcript
value exact and realize one fresh common value at the next reference query. -/
private theorem existsSeparatedNextStatesWithValueReplay
    {R M : NNReal} {ε : ℝ} {T t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)))
    (ht : t < T)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    (hpkg : pkg.oracleBase = fun _ : E ↦ 0) :
    let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
    let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
    ∃ state₁ state₂ : FeasibilityResistingOracleState n,
      ∃ v : ℝ,
        (∀ j (hj : j < pkg.tr.length),
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
              ((pkg.tr.get ⟨j, hj⟩).1)) =
            ((pkg.tr.get ⟨j, hj⟩).2)) ∧
        (∀ j (hj : j < pkg.tr.length),
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
              ((pkg.tr.get ⟨j, hj⟩).1)) =
            ((pkg.tr.get ⟨j, hj⟩).2)) ∧
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) q) = v ∧
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn)) q) = v ∧
        (∀ u ∈ state₁.currentBox (R : ℝ) hn,
          ∀ v' ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v') := by
  -- Route correction: the stale anchor-face surface was stronger than the append step needs.
  -- First normalize the anchor-side data: every recorded query and the fresh query already admit
  -- concrete boundary projections in the next common prefix box.
  dsimp
  let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
  let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
  let anchorNext :=
    resistingPrefixState R hn (method (linftyClosedBall R : Set E)) oracleRef (t + 1)
  by_cases hrepeat :
      ∃ j, ∃ hj : j < pkg.tr.length, (pkg.tr.get ⟨j, hj⟩).1 = q
  · rcases hrepeat with ⟨j, hj, hqj⟩
    -- The repeated-query branch is now a standalone append-ready helper.
    exact
      existsSeparatedNextStatesWithValueReplay_ofRepeatedQuery
        (R := R) (M := M) (ε := ε) (method := method) hn pkg
        ⟨j, hj, hqj⟩
  · have hq_boundary :
        ∃ i : Fin n,
          (q i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
            anchorNext.currentUpper (R : ℝ) hn i ≤ q i) :=
      freshQueryBoundaryAtNextAnchor
        (R := R) (M := M) (ε := ε) (method := method) hn pkg
    have hrecorded_boundary :
        ∀ j (hj : j < pkg.tr.length),
          ∃ i : Fin n,
            (((pkg.tr.get ⟨j, hj⟩).1) i ≤ anchorNext.currentLower (R : ℝ) hn i ∨
              anchorNext.currentUpper (R : ℝ) hn i ≤ ((pkg.tr.get ⟨j, hj⟩).1) i) :=
      recordedQueryBoundaryAtNextAnchor
        (R := R) (M := M) (ε := ε) (method := method) hn pkg
    have ht_succ : t + 1 ≤ T := Nat.succ_le_of_lt ht
    let lowerStrip := lowerSideStrip R hn anchorNext (ε / (M : ℝ))
    let upperStrip := upperSideStrip R hn anchorNext (ε / (M : ℝ))
    obtain ⟨hlower_nonempty, hupper_nonempty, hstrip_sep_raw⟩ :=
      nextAnchorSideStripData
        (R := R) (M := M) (ε := ε) (T := T) (t := t)
        (method := method) hn hε hM hbudget ht_succ pkg
    have hδ_nonneg : 0 ≤ ε / (M : ℝ) := by positivity
    have hstrip_sep :
        ∀ u ∈ lowerStrip, ∀ v ∈ upperStrip, 2 * ε / (M : ℝ) < dist u v := by
      simpa [lowerStrip, upperStrip, anchorNext, oracleRef] using hstrip_sep_raw
    have hlower_to_child :
        lowerStrip ⊆
          (FeasibilityResistingOracleState.keepLowerHalf anchorNext).currentBox (R : ℝ) hn := by
      simpa [lowerStrip] using
        lowerSideStrip_subset_keepLowerHalf_currentBox
          (R := R) (δ := ε / (M : ℝ)) hn anchorNext hδ_nonneg
    have hupper_to_child :
        upperStrip ⊆
          (FeasibilityResistingOracleState.keepUpperHalf anchorNext).currentBox (R : ℝ) hn := by
      simpa [upperStrip] using
        upperSideStrip_subset_keepUpperHalf_currentBox
          (R := R) (δ := ε / (M : ℝ)) hn anchorNext hδ_nonneg
    have hq_state₁ :
        (method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn)) t = q := by
      -- Reuse the packaged prefix-synchronization theorem for the first package objective.
      exact
        (nextQueryAndAnchor_eq_ofTranscriptCompatibleValuePackageObjective
          (R := R) (M := M) (ε := ε) (method := method) hn pkg
          (φ := fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
          pkg.hstate₁_ref).1
    have hq_state₂ :
        (method (linftyClosedBall R : Set E)).queryAfter
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn)) t = q := by
      -- The second package objective has the same synchronized next query.
      exact
        (nextQueryAndAnchor_eq_ofTranscriptCompatibleValuePackageObjective
          (R := R) (M := M) (ε := ε) (method := method) hn pkg
          (φ := fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
          pkg.hstate₂_ref).1
    have hanchor_state₁ :
        resistingPrefixState R hn
            (method (linftyClosedBall R : Set E))
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
            (t + 1) =
          anchorNext := by
      -- The same packaged synchronization gives the next common anchor immediately.
      exact
        (nextQueryAndAnchor_eq_ofTranscriptCompatibleValuePackageObjective
          (R := R) (M := M) (ε := ε) (method := method) hn pkg
          (φ := fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₁.currentBox (R : ℝ) hn))
          pkg.hstate₁_ref).2
    have hanchor_state₂ :
        resistingPrefixState R hn
            (method (linftyClosedBall R : Set E))
            (fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
            (t + 1) =
          anchorNext := by
      -- And again for the second package objective.
      exact
        (nextQueryAndAnchor_eq_ofTranscriptCompatibleValuePackageObjective
          (R := R) (M := M) (ε := ε) (method := method) hn pkg
          (φ := fun x : E ↦ (M : ℝ) * Metric.infDist x (pkg.state₂.currentBox (R : ℝ) hn))
          pkg.hstate₂_ref).2
    -- The remaining frontier is now only the genuinely fresh-query descendant construction.
    -- TODO: build one lower-strip and one upper-strip descendant of `anchorNext` together with
    -- single-state replay families, or equivalently explicit replay witnesses that can be fed to
    -- `stateValue_eq_ofReplayWitnessAndSubset`.
    -- The easy prefix work is finished: the two strips are nonempty, their points are separated,
    -- and each strip already injects into the corresponding immediate midpoint child via
    -- `hlower_to_child` and `hupper_to_child`.
    -- The first genuinely open step is stronger: for each old transcript value we still need a
    -- same-value witness inside a lower-strip descendant and inside an upper-strip descendant.
    -- Those witnesses are not recoverable from the current exact-value-only package fields.
    let _ := hlower_nonempty
    let _ := hupper_nonempty
    let _ := hstrip_sep
    let _ := hlower_to_child
    let _ := hupper_to_child
    let _ := hq_boundary
    let _ := hrecorded_boundary
    let _ := hq_state₁
    let _ := hq_state₂
    let _ := hanchor_state₁
    let _ := hanchor_state₂
    sorry

/-- Helper for Theorem 3.50: once a prefix value package over the zero reference oracle is fixed,
the remaining geometric step is to append one fresh query-value pair while preserving all earlier
recorded values on two separated descendants. -/
private theorem existsSeparatedSuccessorPreservingRecordedValues
    {R M : NNReal} {ε : ℝ} {T t : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)))
    (ht : t < T)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn t)
    (hpkg : pkg.oracleBase = fun _ : E ↦ 0) :
    ∃ pkg' : TranscriptCompatibleSeparatedValuePackage method R M ε hn (t + 1),
      pkg'.oracleBase = fun _ : E ↦ 0 := by
  let oracleRef := referenceOracleOfTranscript pkg.oracleBase pkg.tr
  let q := (method (linftyClosedBall R : Set E)).queryAfter oracleRef t
  -- Route correction: the successor step now consumes only the exact old values, one fresh common
  -- value, and the final separation certificate needed by the append constructor.
  obtain ⟨state₁, state₂, v, hstate₁_old, hstate₂_old, hvalue₁, hvalue₂, hsep⟩ :=
    existsSeparatedNextStatesWithValueReplay
      (method := method) (hn := hn) (hε := hε) (hM := hM)
      (hbudget := hbudget) (ht := ht) pkg hpkg
  refine
    ⟨appendTranscriptCompatibleSeparatedValuePackage
      method hn pkg state₁ state₂ (q := q) (v := v) rfl
      hstate₁_old hstate₂_old hvalue₁ hvalue₂ hsep, ?_⟩
  -- The append constructor keeps the base oracle unchanged.
  simpa [appendTranscriptCompatibleSeparatedValuePackage] using
    (Classical.choose_spec <|
      appendTranscriptCompatibleSeparatedValuePackage_nonempty
        method hn pkg state₁ state₂ rfl
        hstate₁_old hstate₂_old hvalue₁ hvalue₂ hsep).trans hpkg

/-- Helper for Theorem 3.50: under the short-budget hypothesis, the live private task is now to
build one final value-only package over the zero reference oracle. The old anchored and
stored-witness routes are intentionally off the live path because they force box intersection. -/
private theorem existsTranscriptCompatibleSeparatedValuePackageOfShortBudget
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∃ pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn T,
      pkg.oracleBase = fun _ : E ↦ 0 := by
  -- Route correction: after removing the false witness-carrying layers, the private proof now
  -- factors into one short-budget seed package and one append-ready successor theorem.
  refine
    existsTranscriptCompatibleSeparatedValuePackage_ofSeededSuccessor
      method hn (fun _ : E ↦ 0) ?_
  constructor
  · -- The empty transcript case is the geometric seed over the zero reference oracle.
    exact
      existsInitialTranscriptCompatibleSeparatedValuePackage_ofShortBudget
        method hn hε hM hbudget
  · intro t ht pkg hpkg
    -- Each prefix package is extended by the remaining value-preserving separated successor step.
    exact
      existsSeparatedSuccessorPreservingRecordedValues
        method hn hε hM hbudget ht pkg hpkg

/-- Helper for Theorem 3.50: once the short-budget builder produces one final value-only package,
the public descendant-current-box theorem is just an unpacking step followed by the generic
transcript/reference bridge. -/
private theorem existsTranscriptCompatibleSeparatedDescendantCurrentBoxes_ofValuePackage
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (pkg : TranscriptCompatibleSeparatedValuePackage method R M ε hn T) :
    ∃ state₁ state₂ : FeasibilityResistingOracleState n,
      (∀ j : ℕ, j < T →
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j)) =
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j))) ∧
        (∀ u ∈ state₁.currentBox (R : ℝ) hn,
          ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) := by
  -- Unpack the final value package and apply the common-reference bridge once.
  refine ⟨pkg.state₁, pkg.state₂, ?_⟩
  simpa using sameQueryOfFinalTranscriptCompatibleValuePackage method hn pkg

/-- Helper for Theorem 3.50: a short oracle budget admits two separated descendant current boxes
whose scaled-distance objectives agree on every query of the first hard transcript. -/
private theorem existsTranscriptCompatibleSeparatedDescendantCurrentBoxes
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∃ state₁ state₂ : FeasibilityResistingOracleState n,
      (∀ j : ℕ, j < T →
        ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j)) =
          ((fun x : E ↦ (M : ℝ) * Metric.infDist x (state₂.currentBox (R : ℝ) hn))
            ((method (linftyClosedBall R : Set E)).queryAfter
              (fun x : E ↦ (M : ℝ) * Metric.infDist x (state₁.currentBox (R : ℝ) hn)) j))) ∧
      (∀ u ∈ state₁.currentBox (R : ℝ) hn,
          ∀ v ∈ state₂.currentBox (R : ℝ) hn, 2 * ε / (M : ℝ) < dist u v) := by
  -- Route correction: the public theorem now factors through one explicit value-only package.
  obtain ⟨pkg, hpkg⟩ :=
    existsTranscriptCompatibleSeparatedValuePackageOfShortBudget
      (method := method) (hn := hn) (hε := hε) (hM := hM) (hbudget := hbudget)
  -- The zero-base witness is not needed after the final package has been produced.
  exact existsTranscriptCompatibleSeparatedDescendantCurrentBoxes_ofValuePackage method hn pkg

/-- Helper for Theorem 3.50: a short oracle budget yields two feasible hard instances with
separated zero-sets and identical queried values along the first hard transcript. -/
private theorem exists_separated_transcript_equivalent_descendant_axis_boxes_of_short_budget
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hn : 0 < n)
    (hε : 0 < ε)
    (hM : 0 < (M : ℝ))
    (hbudget : (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε))) :
    ∃ φ₁ φ₂ K₁ K₂,
      K₁.Nonempty ∧
        IsClosed K₁ ∧
          Convex ℝ K₁ ∧
            K₁ ⊆ linftyClosedBall R ∧
              K₂.Nonempty ∧
                IsClosed K₂ ∧
                  Convex ℝ K₂ ∧
                    K₂ ⊆ linftyClosedBall R ∧
                      φ₁ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
                        φ₂ ∈ 𝓕⁰⁰[M](linftyClosedBall R) ∧
                          (∀ x ∈ K₁, φ₁ x = 0) ∧
                            (∀ x ∈ K₂, φ₂ x = 0) ∧
                              (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
                                φ₁).optimalValue = 0 ∧
                                (SetConstrainedMinimizationProblem.mk (linftyClosedBall R : Set E)
                                  φ₂).optimalValue = 0 ∧
                                  (∀ j : ℕ, j < T →
                                    φ₁ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j) =
                                      φ₂ ((method (linftyClosedBall R : Set E)).queryAfter φ₁ j)) ∧
                                    (∀ x : E, ¬ (φ₁ x ≤ ε ∧ φ₂ x ≤ ε)) := by
  -- Route correction: the fixed sibling-ball replay has been replaced by a single structural
  -- descendant-current-box theorem. The main theorem now only packages that stronger invariant.
  obtain ⟨state₁, state₂, hsame_query, hsep⟩ :=
    existsTranscriptCompatibleSeparatedDescendantCurrentBoxes
      method hn hε hM hbudget
  -- The generic descendant-current-box package already converts the structural invariant into the
  -- final hard instances.
  exact
    package_separated_axis_box_hard_instances
      method hM
      ((currentBox_nonempty_isClosed_convex R hn state₁).1)
      ((currentBox_nonempty_isClosed_convex R hn state₁).2.1)
      ((currentBox_nonempty_isClosed_convex R hn state₁).2.2)
      (currentBox_subset_linftyClosedBall R hn state₁)
      ((currentBox_nonempty_isClosed_convex R hn state₂).1)
      ((currentBox_nonempty_isClosed_convex R hn state₂).2.1)
      ((currentBox_nonempty_isClosed_convex R hn state₂).2.2)
      (currentBox_subset_linftyClosedBall R hn state₂)
      (by simpa using hsame_query)
      (by simpa using hsep)

/-- Deterministic specialization of the Chapter 3 value-oracle lower bound: if the target accuracy
satisfies `0 < ε` and a
feasible-set-aware deterministic
value-oracle method with at most `T` oracle calls uniformly guarantees, for every nonempty convex
`Q ⊆ B∞(0, R)` and every `f ∈ 𝓕_{M}^{0,0}(B∞(0, R))`, an `ε`-approximate minimizer of the induced
set-constrained problem, then the query budget satisfies the lower bound
`n * log (M R / (8 ε)) ≤ T`. -/
-- Proof sketch: specialize to the finite hard family `u ↦ f_u` on the uniform grid inside
-- `B∞(0, R)`, where `f_u(x) = M * ‖x - u‖∞` and `Q = B∞(0, R)`. A depth-`T` value-query
-- transcript leaves exponentially many candidate minimizers consistent with the observed values,
-- so if `T < n * log (M R / (8 ε))` then two separated hard instances remain indistinguishable.
-- Any single feasible output is therefore `ε`-suboptimal on at least one of them.
theorem deterministic_value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hε : 0 < ε)
    (hmethod : DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin
      method R M ε T) :
    (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) ≤ (T : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · by_cases hsmall : (M : ℝ) * R ≤ 8 * ε
    · have hratio_nonneg : 0 ≤ (M : ℝ) * R / (8 * ε) := by
        positivity
      have hratio_le_one : (M : ℝ) * R / (8 * ε) ≤ 1 := by
        have hden : 0 < 8 * ε := by positivity
        exact (div_le_iff₀ hden).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hsmall
      have hlog_nonpos : Real.log ((M : ℝ) * R / (8 * ε)) ≤ 0 :=
        Real.log_nonpos hratio_nonneg hratio_le_one
      nlinarith
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hMR_gt : 8 * ε < (M : ℝ) * R := by
        have hle : ¬ (M : ℝ) * R ≤ 8 * ε := hsmall
        linarith
      have hM_pos : 0 < (M : ℝ) := by
        have hMR_pos : 0 < (M : ℝ) * R := lt_trans (by positivity) hMR_gt
        by_contra hM_nonpos
        have hR_nonneg : 0 ≤ (R : ℝ) := R.2
        have hMR_nonpos : (M : ℝ) * R ≤ 0 := by nlinarith
        linarith
      have hbudget :
          ¬ (T : ℝ) < (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) := by
        intro hlt
        let Q : Set E := linftyClosedBall R
        have hhard :=
          exists_separated_transcript_equivalent_descendant_axis_boxes_of_short_budget
            method hn_pos hε hM_pos hlt
        obtain ⟨objective₁, objective₂, K₁, K₂, hK₁_nonempty, hK₁_closed, hK₁_convex, hK₁_subset,
            hK₂_nonempty, hK₂_closed, hK₂_convex, hK₂_subset,
            hobjective₁_memF00, hobjective₂_memF00, hobjective₁_zero, hobjective₂_zero,
            hopt₁, hopt₂, hsame_query, hnot_small⟩ :=
          hhard
        let problem₁ : SetConstrainedMinimizationProblem E :=
          SetConstrainedMinimizationProblem.mk Q objective₁
        let problem₂ : SetConstrainedMinimizationProblem E :=
          SetConstrainedMinimizationProblem.mk Q objective₂
        let algorithm := method Q
        have hQ_nonempty : Q.Nonempty := by
          refine ⟨0, ?_⟩
          simp [Q]
        have hQ_convex : Convex ℝ Q := by
          simpa [Q] using linftyClosedBall_convex R
        have hproblem₁_class : problem₁.IsInLinftyConstrainedProblemClass R M := by
          refine ⟨hQ_nonempty, hQ_convex, ?_, ?_⟩
          · simpa [problem₁, Q]
          · simpa [problem₁, Q] using hobjective₁_memF00
        have hproblem₂_class : problem₂.IsInLinftyConstrainedProblemClass R M := by
          refine ⟨hQ_nonempty, hQ_convex, ?_, ?_⟩
          · simpa [problem₂, Q]
          · simpa [problem₂, Q] using hobjective₂_memF00
        have hsolve₁ := hmethod problem₁ hproblem₁_class
        have hsolve₂ := hmethod problem₂ hproblem₂_class
        have houtput_eq :
            algorithm.outputAfter objective₁ T =
              algorithm.outputAfter objective₂ T := by
          -- Matching queried values on the first hard instance synchronizes the whole transcript.
          refine DeterministicValueOracleMethod.outputAfter_eq_of_same_query_values
            algorithm objective₁ objective₂ ?_
          intro j hj
          simpa using hsame_query j hj
        have happrox₁ :
            problem₁.IsApproximateMinimizer ε (algorithm.outputAfter objective₁ T) := by
          simpa [DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin,
            Q, problem₁, algorithm] using hsolve₁.2
        have happrox₂ :
            problem₂.IsApproximateMinimizer ε (algorithm.outputAfter objective₂ T) := by
          simpa [DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin,
            Q, problem₂, algorithm] using hsolve₂.2
        have hsmall₁ :
            objective₁ (algorithm.outputAfter objective₁ T) ≤ ε := by
          -- The packaged hard instance records exact optimum value `0`, so the owner
          -- approximate-minimizer inequality becomes a direct upper bound on `objective₁`.
          have hineq := happrox₁.2
          have hineq' :
              (((objective₁ (algorithm.outputAfter objective₁ T) : ℝ) : EReal) ≤
                (ε : EReal)) := by
            simpa [problem₁, Q, hopt₁] using hineq
          exact_mod_cast hineq'
        have hsmall₂_raw :
            objective₂ (algorithm.outputAfter objective₂ T) ≤ ε := by
          -- The second packaged instance uses the same optimal-value normalization.
          have hineq := happrox₂.2
          have hineq' :
              (((objective₂ (algorithm.outputAfter objective₂ T) : ℝ) : EReal) ≤
                (ε : EReal)) := by
            simpa [problem₂, Q, hopt₂] using hineq
          exact_mod_cast hineq'
        have hsmall₂ :
            objective₂ (algorithm.outputAfter objective₁ T) ≤ ε := by
          simpa [houtput_eq] using hsmall₂_raw
        exact hnot_small (algorithm.outputAfter objective₁ T) ⟨hsmall₁, hsmall₂⟩
      exact le_of_not_gt hbudget

namespace DeterministicValueOracleMethod

/-- A nonempty seed-indexed family of deterministic value-oracle methods is the source-faithful
statement surface for a possibly randomized algorithm in Theorem 3.50: because the source asks
for a uniform worst-case guarantee with no success-probability qualifier, each seed must realize
its own deterministic `T`-query method solving the constrained class. -/
def SeededSolvesLinftyConstrainedProblemClassWithin
    {Ω : Type v} [Nonempty Ω]
    (method : Ω → Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ ω : Ω, SolvesLinftyConstrainedProblemClassWithin (method ω) R M ε T

@[simp] theorem seededSolvesLinftyConstrainedProblemClassWithin_iff
    {Ω : Type v} [Nonempty Ω]
    (method : Ω → Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (T : ℕ) :
    SeededSolvesLinftyConstrainedProblemClassWithin method R M ε T ↔
      ∀ ω : Ω, SolvesLinftyConstrainedProblemClassWithin (method ω) R M ε T :=
  Iff.rfl

end DeterministicValueOracleMethod

/-- Theorem 3.50: let `n ≥ 1`, `R > 0`, `M > 0`, and `ε > 0`. If a possibly randomized
value-oracle method with at most `T` oracle calls uniformly guarantees, for every nonempty convex
`Q ⊆ B∞(0, R)` and every `f ∈ 𝓕_{M}^{0,0}(B∞(0, R))`, an `ε`-approximate minimizer of the induced
set-constrained problem, then the query budget satisfies the lower bound
`n * log (M R / (8 ε)) ≤ T`. Here the possible randomization is represented by a nonempty family
of deterministic transcript rules indexed by an internal seed. -/
theorem value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
    (hn : 1 ≤ n) {Ω : Type v} [Nonempty Ω]
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Ω → Set E → DeterministicValueOracleMethod E)
    (hR : 0 < (R : ℝ)) (hM : 0 < (M : ℝ)) (hε : 0 < ε)
    (hmethod :
      DeterministicValueOracleMethod.SeededSolvesLinftyConstrainedProblemClassWithin
        method R M ε T) :
    (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) ≤ (T : ℝ) := by
  classical
  let ω : Ω := Classical.choice ‹Nonempty Ω›
  have hdet :
      DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin
        (method ω) R M ε T :=
    hmethod ω
  simpa using
    deterministic_value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
      (method ω) hε hdet

end
