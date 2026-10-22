/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_13
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.17 is `source-facing`: it is the convergence theorem for the concrete projected
subgradient iterates generated under Polyak's stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the standing
problem package `IsConstrainedConvexProblem`, the subgradient bound package
`SubgradientNormBoundOn`, and the Fejér-convergence criterion
`tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo`. To keep the textbook meaning faithful,
the Euclidean finite-dimensional hypothesis from Definition 8.1 is made explicit here: it is the
hidden input that supplies a sequential cluster point of the bounded Fejér-monotone trajectory. -/

-- Proof sketch: rewrite `h_subgrad` through `mem_strongDualSubdifferential` and apply
-- Theorem 8.13(a) to get Fejér monotonicity of `x` with respect to `XStar`, and Theorem 8.13(b)
-- to get convergence of `(f (x[k] : E)).toReal` to `fOpt`. Finite dimensionality and Fejér
-- monotonicity provide a cluster point of the iterate sequence. Any cluster point lies in `C`
-- because `C` is closed, hence in `interior (effective_domain f)` by Assumption 8.7, so the
-- continuity theorem for convex functions on interior points upgrades the limit
-- `(f (x[k] : E)).toReal → fOpt` to optimality of the cluster point. Therefore every cluster point
-- belongs to `XStar`, and Theorem 8.16 yields convergence of the whole sequence to a point of
-- `XStar`.
/-- Helper for Theorem 8.17: Polyak's stepsize rule makes the distance from the projected
subgradient iterates to each optimal point nonincreasing. -/
lemma projected_subgradient_method_dist_mono_of_polyak_stepsize
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n])))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    dist (x[k + 1] : E) xStar ≤ dist (x[k] : E) xStar := by
  -- Rewrite the strong-dual selections into the owner interface used by Theorem 8.13.
  have h_subgrad' :
      ∀ n,
        (toDualMap ℝ E (g n (x[n])) : Module.Dual ℝ E) ∈ subdifferential f (x[n] : E) := by
    intro n
    simpa [mem_strongDualSubdifferential] using h_subgrad n
  have hsq :=
    projected_subgradient_method_sqdist_mono_of_polyak_stepsize
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_bound h_subgrad' h_polyak hxStar k
  -- The squared-distance inequality is exactly the Fejer step after removing the squares.
  have hnorm : ‖(x[k + 1] : E) - xStar‖ ≤ ‖(x[k] : E) - xStar‖ := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq
    exact hsq
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 8.17: finite-dimensional compactness provides a sequential cluster point for
the Polyak trajectory. -/
lemma projected_subgradient_method_has_mapClusterPt_of_polyak_stepsize
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n]))) :
    ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let r : ℝ := dist (x[0] : E) xStar
  have hball : ∀ n : ℕ, (x[n] : E) ∈ Metric.closedBall xStar r := by
    intro n
    have hdist : dist (x[n] : E) xStar ≤ dist (x[0] : E) xStar := by
      induction n with
      | zero =>
          exact le_rfl
      | succ n ih =>
          exact le_trans
            (projected_subgradient_method_dist_mono_of_polyak_stepsize
              (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
              (h_subgrad := h_subgrad) (h_polyak := h_polyak) hxStar n)
            ih
    simpa [r, Metric.mem_closedBall] using hdist
  have hfreq :
      ∃ᶠ n in Filter.atTop, (x[n] : E) ∈ Metric.closedBall xStar r :=
    (Filter.Eventually.of_forall hball).frequently
  rcases (isCompact_closedBall xStar r).exists_mapClusterPt_of_frequently hfreq with
    ⟨y, -, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Theorem 8.17: interior feasibility makes `x ↦ (f x).toReal` continuous at that
point. -/
lemma toReal_continuousAt_of_mem_interior_effective_domain
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) {y : E}
    (hy : y ∈ interior (effective_domain f)) :
    ContinuousAt (fun z : E ↦ (f z).toReal) y := by
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function h_problem.convex
      (fun z hz ↦ h_problem.ne_bot z)
  have hcontOn :
      ContinuousOn (fun z : E ↦ (f z).toReal) (interior (effective_domain f)) :=
    hconv.continuousOn_interior
  -- The interior of a convex domain is open, so continuity within the interior is ordinary
  -- continuity at the chosen point.
  exact (hcontOn y hy).continuousAt (isOpen_interior.mem_nhds hy)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 8.17: a feasible point whose objective value equals `fOpt` belongs to the
optimal set `XStar`. -/
lemma mem_optimal_set_of_mem_C_of_toReal_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) {y : E}
    (hyC : y ∈ C) (hyOpt : (f y).toReal = fOpt) :
    y ∈ XStar := by
  have hyDom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hyC)
  have hyTop : f y ≠ ⊤ := ne_of_lt hyDom
  have hyBot : f y ≠ ⊥ := h_problem.ne_bot y
  have hyEq : f y = (fOpt : EReal) := by
    calc
      f y = (((f y).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hyTop hyBot
      _ = (fOpt : EReal) := by
        simp [hyOpt]
  rw [h_problem.optimal_set_eq]
  refine ⟨hyC, ?_⟩
  rw [isMinOn_iff]
  intro z hzC
  have hzImage : f z ∈ f '' C := ⟨z, hzC, rfl⟩
  have hglb : (fOpt : EReal) ≤ f z := h_problem.optimal_value_isGLB.left hzImage
  simpa [hyEq] using hglb

/-- Helper for Theorem 8.17: every sequential cluster point of the Polyak trajectory is an optimal
solution. -/
lemma cluster_point_mem_optimal_set_of_polyak_stepsize {y : E}
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n])))
    (hyCluster : MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))) :
    y ∈ XStar := by
  have h_subgrad' :
      ∀ n,
        (toDualMap ℝ E (g n (x[n])) : Module.Dual ℝ E) ∈ subdifferential f (x[n] : E) := by
    intro n
    simpa [mem_strongDualSubdifferential] using h_subgrad n
  have hyC : y ∈ C := by
    -- Closedness of the feasible set transfers feasibility from the whole trajectory to the
    -- cluster point.
    refine h_problem.feasible_closed.mem_of_mapClusterPt hyCluster ?_
    exact Filter.Eventually.of_forall fun n => (x[n]).property
  have hyInterior : y ∈ interior (effective_domain f) :=
    h_problem.feasible_subset_interior_effective_domain hyC
  have hcont :
      ContinuousAt (fun z : E ↦ (f z).toReal) y :=
    toReal_continuousAt_of_mem_interior_effective_domain
      (h_problem := h_problem) hyInterior
  have hobj :
      Filter.Tendsto (fun n ↦ (f (x[n] : E)).toReal) Filter.atTop (nhds fOpt) :=
    projected_subgradient_method_objective_tendsto_of_polyak_stepsize
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_bound h_subgrad' h_polyak
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hyCluster
  have hsubseq_obj :
      Filter.Tendsto (fun n ↦ (f (x[ψ n] : E)).toReal) Filter.atTop (nhds fOpt) :=
    hobj.comp hψmono.tendsto_atTop
  have hsubseq_cont :
      Filter.Tendsto (fun n ↦ (f (x[ψ n] : E)).toReal) Filter.atTop (nhds ((f y).toReal)) := by
    -- The subsequence converges to `y`, so continuity identifies the objective limit there.
    simpa [Function.comp] using hcont.tendsto.comp hψtendsto
  have hyOpt : (f y).toReal = fOpt :=
    tendsto_nhds_unique hsubseq_cont hsubseq_obj
  exact mem_optimal_set_of_mem_C_of_toReal_eq_fOpt
    (h_problem := h_problem) hyC hyOpt

include h_bound
/-- Theorem 8.17: under Assumptions 8.7 and 8.12, the projected subgradient sequence generated
with Polyak's stepsize rule converges to a point of the optimal set `XStar = X^*`. -/
theorem projected_subgradient_method_tendsto_point_in_optimal_set_of_polyak_stepsize
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_polyak :
      ∀ n,
        t n = polyak_stepsize f fOpt (x[n] : E) (g n (x[n]))) :
    ∃ xStar : E,
      xStar ∈ XStar ∧
        Filter.Tendsto (fun n ↦ (x[n] : E)) Filter.atTop (nhds xStar) := by
  have hFejer : ∀ y ∈ XStar, ∀ k : ℕ, dist (x[k + 1] : E) y ≤ dist (x[k] : E) y := by
    intro y hy k
    -- Theorem 8.13(a) is the source-faithful Fejer monotonicity input for Theorem 8.16.
    exact projected_subgradient_method_dist_mono_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak) hy k
  have hlimitPoints_subset :
      {y : E | MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E))} ⊆ XStar := by
    intro y hy
    -- Every cluster point is feasible, continuity transfers the objective limit, and the
    -- resulting feasible minimizer lies in `XStar`.
    exact cluster_point_mem_optimal_set_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak) hy
  have hlimitPoint : ∃ y : E, MapClusterPt y Filter.atTop (fun n ↦ (x[n] : E)) :=
    projected_subgradient_method_has_mapClusterPt_of_polyak_stepsize
      (h_problem := h_problem) (h_bound := h_bound) (g := g) (t := t) (x0 := x0)
      (h_subgrad := h_subgrad) (h_polyak := h_polyak)
  obtain ⟨xStar, hxStarCluster, hxStarTendsto⟩ :=
    tendsto_to_limitPoint_of_isFejerMonotoneWithRespectTo hFejer hlimitPoints_subset hlimitPoint
  exact ⟨xStar, hlimitPoints_subset hxStarCluster, hxStarTendsto⟩

end
