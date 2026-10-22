/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2

noncomputable section

section Chapter08Theorem8214

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

open Filter
open scoped Pointwise Topology

/-- Helper for Chapter08 Theorem 8.2.14: negating strict local minimality produces a sequence of
distinct feasible points whose objective values do not exceed `f xStar` and whose distances to
`xStar` shrink like `1 / (k + 1)`. -/
lemma existsCounterexampleSequence_of_not_isStrictLocalMinOn
    {f : Point → ℝ} {s : Set Point} {xStar : Point}
    (hxStar : xStar ∈ s) (h_not : ¬ IsStrictLocalMinOn f s xStar) :
    ∃ xSeq : ℕ → Point,
      ∀ k,
        xSeq k ∈ s ∧
          xSeq k ≠ xStar ∧
          ‖xSeq k - xStar‖ ≤ 1 / ((k : ℝ) + 1) ∧
          f (xSeq k) ≤ f xStar := by
  classical
  have h_no_ball :
      ¬ ∃ δ > 0,
          ∀ x : Point,
            x ∈ s ∩ Metric.closedBall xStar δ → x ≠ xStar → f xStar < f x := by
    intro h_ball
    exact h_not ((isStrictLocalMinOn_iff_exists_forall_mem_closedBall f s xStar).2 ⟨hxStar, h_ball⟩)
  push Not at h_no_ball
  have h_choose :
      ∀ k : ℕ,
        ∃ x : Point,
          x ∈ s ∩ Metric.closedBall xStar (1 / ((k : ℝ) + 1)) ∧
            x ≠ xStar ∧
            f x ≤ f xStar := by
    intro k
    have hk_pos : 0 < 1 / ((k : ℝ) + 1) := by
      positivity
    simpa [not_lt] using h_no_ball (1 / ((k : ℝ) + 1)) hk_pos
  choose xSeq hxSeq using h_choose
  refine ⟨xSeq, ?_⟩
  intro k
  rcases hxSeq k with ⟨hx_mem, hx_ne, hx_le⟩
  refine ⟨hx_mem.1, hx_ne, ?_, hx_le⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx_mem.2

/-- Helper for Chapter08 Theorem 8.2.14: a sequence of normalized nonzero displacements has a
convergent subsequence on the unit sphere. -/
lemma existsTendstoNormalizedDisplacementSubseq
    {xSeq : ℕ → Point} {xStar : Point} (h_ne : ∀ k, xSeq k ≠ xStar) :
    ∃ d : Point,
      d ∈ Metric.sphere (0 : Point) 1 ∧
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto
            (fun k ↦ ‖xSeq (φ k) - xStar‖⁻¹ • (xSeq (φ k) - xStar))
            atTop (nhds d) := by
  let u : ℕ → Point := fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)
  have hu_sphere : ∀ k, u k ∈ Metric.sphere (0 : Point) 1 := by
    intro k
    have hk_norm_ne : ‖xSeq k - xStar‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 ?_
      exact sub_ne_zero.2 (h_ne k)
    -- Each normalized displacement has unit norm, so it lies on the unit sphere.
    rw [Metric.mem_sphere, dist_eq_norm]
    simp only [sub_zero]
    dsimp [u]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    exact inv_mul_cancel₀ hk_norm_ne
  rcases (isCompact_sphere (0 : Point) 1).tendsto_subseq hu_sphere with ⟨d, hd, φ, hφ, hlim⟩
  exact ⟨d, hd, φ, hφ, hlim⟩

/-- Helper for Chapter08 Theorem 8.2.14: if a feasible sequence converges to `xStar` and its
normalized displacements converge to `d`, then `d` lies in `posTangentConeAt X xStar`. -/
lemma memPosTangentConeAt_of_tendstoNormalizedDisplacement
    {X : Set Point} {xSeq : ℕ → Point} {xStar d : Point}
    (h_mem : ∀ k, xSeq k ∈ X)
    (h_ne : ∀ k, xSeq k ≠ xStar)
    (hx_tendsto : Tendsto xSeq atTop (nhds xStar))
    (h_dir :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) atTop (nhds d)) :
    d ∈ posTangentConeAt X xStar := by
  refine (mem_posTangentConeAt_iff_exists_seq_pos).2 ?_
  refine
    ⟨fun k ↦ ‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar), fun k ↦ ‖xSeq k - xStar‖, ?_, ?_, h_dir, ?_⟩
  · intro k
    -- Distinct points give strictly positive step sizes.
    refine norm_pos_iff.2 ?_
    exact sub_ne_zero.2 (h_ne k)
  · intro k
    have hk_norm_ne : ‖xSeq k - xStar‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 ?_
      exact sub_ne_zero.2 (h_ne k)
    -- Cancelling the norm recovers the original feasible point.
    have hstep :
        xStar +
            ‖xSeq k - xStar‖ •
      (‖xSeq k - xStar‖⁻¹ • (xSeq k - xStar)) =
          xSeq k := by
      rw [smul_smul, mul_inv_cancel₀ hk_norm_ne, one_smul]
      simp [sub_eq_add_neg]
    simpa [hstep] using h_mem k
  · -- The displacement norms tend to zero because the base sequence tends to `xStar`.
    have hdiff :
        Tendsto (fun k ↦ xSeq k - xStar) atTop (nhds (0 : Point)) := by
      simpa using
        hx_tendsto.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ xStar) atTop (nhds xStar))
    simpa using hdiff.norm

-- Source-facing theorem reusing the Chapter 8 owners for constrained problems, sequential
-- feasible directions, and strict local minima. The companion below bridges to the canonical
-- mathlib local-minimum predicate.

/-- Chapter08 Theorem 8.2.14: let `xStar` be a feasible point of a constrained optimization
problem. If the objective is differentiable at `xStar`, and every nonzero sequential feasible
direction `d ∈ posTangentConeAt problem.feasibleSet xStar` has strictly positive directional
derivative `fderiv ℝ problem.objective xStar d`, then `xStar` is a strict local minimizer of the
constrained problem on `X = problem.feasibleSet`. -/
theorem isStrictLocalMinOn_of_positive_pairing_on_sequentialFeasibleDirections
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_positive :
      ∀ d ∈ posTangentConeAt problem.feasibleSet xStar,
        d ≠ 0 → 0 < fderiv ℝ problem.objective xStar d) :
    IsStrictLocalMinOn problem.objective problem.feasibleSet xStar := by
  by_contra h_not
  rcases existsCounterexampleSequence_of_not_isStrictLocalMinOn hxStar h_not with ⟨xSeq, hxSeq⟩
  let badSet : Set Point :=
    problem.feasibleSet ∩ {x : Point | problem.objective x ≤ problem.objective xStar}
  have hxSeq_mem : ∀ k, xSeq k ∈ problem.feasibleSet := fun k ↦ (hxSeq k).1
  have hxSeq_ne : ∀ k, xSeq k ≠ xStar := fun k ↦ (hxSeq k).2.1
  have hxSeq_bound :
      ∀ k, ‖xSeq k - xStar‖ ≤ 1 / ((k : ℝ) + 1) := fun k ↦ (hxSeq k).2.2.1
  have hxSeq_le :
      ∀ k, problem.objective (xSeq k) ≤ problem.objective xStar := fun k ↦ (hxSeq k).2.2.2
  have hxSeq_bad : ∀ k, xSeq k ∈ badSet := fun k ↦ ⟨hxSeq_mem k, hxSeq_le k⟩
  have hxSeq_norm_tendsto :
      Tendsto (fun k ↦ ‖xSeq k - xStar‖) atTop (nhds (0 : ℝ)) := by
    -- The closed-ball counterexamples converge to `xStar` by the prescribed radius bound.
    refine squeeze_zero (fun k ↦ norm_nonneg _) hxSeq_bound tendsto_one_div_add_atTop_nhds_zero_nat
  have hxSeq_tendsto : Tendsto xSeq atTop (nhds xStar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hxSeq_norm_tendsto
  rcases existsTendstoNormalizedDisplacementSubseq hxSeq_ne with ⟨d, hd_sphere, φ, hφ, hd_tendsto⟩
  have hsubseq_tendsto : Tendsto (xSeq ∘ φ) atTop (nhds xStar) :=
    hxSeq_tendsto.comp hφ.tendsto_atTop
  have hd_bad :
      d ∈ posTangentConeAt badSet xStar := by
    -- The convergent normalized subsequence gives a positive tangent-cone direction.
    refine memPosTangentConeAt_of_tendstoNormalizedDisplacement ?_ ?_ hsubseq_tendsto hd_tendsto
    · intro k
      exact hxSeq_bad (φ k)
    · intro k
      exact hxSeq_ne (φ k)
  have hd_feasible :
      d ∈ posTangentConeAt problem.feasibleSet xStar :=
    tangentConeAt_mono (fun x hx ↦ hx.1) hd_bad
  have hd_nonzero : d ≠ 0 := by
    -- A point on the unit sphere cannot vanish.
    have hd_norm : ‖d‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_sphere
    intro hd_zero
    simp [hd_zero] at hd_norm
  have h_localMax_bad : IsLocalMaxOn problem.objective badSet xStar := by
    -- On the bad set, the objective is globally bounded above by `problem.objective xStar`.
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx.2
  have h_nonpos :
      fderiv ℝ problem.objective xStar d ≤ 0 := by
    -- The bad set turns `xStar` into a local maximum, forcing a nonpositive directional derivative.
    exact h_localMax_bad.hasFDerivWithinAt_nonpos
      (h_objective.hasFDerivAt.hasFDerivWithinAt) hd_bad
  exact (not_le_of_gt (h_positive d hd_feasible hd_nonzero)) h_nonpos

/-- Companion bridge: Theorem 8.2.14 also yields the canonical constrained local-minimum
predicate `IsLocalMinOn`. -/
theorem isLocalMinOn_of_positive_pairing_on_sequentialFeasibleDirections
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_positive :
      ∀ d ∈ posTangentConeAt problem.feasibleSet xStar,
        d ≠ 0 → 0 < fderiv ℝ problem.objective xStar d) :
    IsLocalMinOn problem.objective problem.feasibleSet xStar :=
  (isStrictLocalMinOn_of_positive_pairing_on_sequentialFeasibleDirections
      problem xStar hxStar h_objective h_positive).isLocalMinOn

end Chapter08Theorem8214
