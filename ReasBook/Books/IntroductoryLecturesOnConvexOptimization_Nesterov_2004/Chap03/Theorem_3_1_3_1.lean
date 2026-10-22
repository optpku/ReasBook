/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis
open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace ConvexOn

/-- Helper for Theorem 3.1.3.1: an interior effective-domain point admits a metric ball on which
the finite-value representative is Lipschitz and which stays inside the effective domain. -/
-- Proof sketch: apply the owner theorem `hf.locallyLipschitzOn_interior` to get a neighborhood
-- within `interior (dom f)`, then shrink simultaneously inside that neighborhood and inside an
-- explicit metric ball contained in `interior (dom f)`.
private theorem exists_metric_ball_lipschitzOnWith_of_mem_interior_local
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 ht with ⟨r₁, hr₁, hr₁sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r₂, hr₂, hr₂sub⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, K, hK.mono ?_⟩
  · -- The smaller ball stays inside `interior (dom f)`, hence inside `dom f)`.
    intro y hy
    exact interior_subset <|
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · -- The same smaller ball also lies in the neighborhood supporting the Lipschitz estimate.
    intro y hy
    exact hr₁sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- Helper for Theorem 3.1.3.1: on `ℝⁿ`, the Euclidean norm is bounded above by the chapter's
canonical `ℓ₁` seminorm. -/
-- Proof sketch: rewrite both norms by their coordinate formulas and compare
-- `√(∑ ‖v i‖²)` with `∑ ‖v i‖` using `Finset.sum_sq_le_sq_sum_of_nonneg`.
private theorem norm_le_l1Seminorm (v : E) :
    ‖v‖ ≤ l1Seminorm n v := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.l1Seminorm_apply]
  refine (Real.sqrt_le_iff).2 ?_
  constructor
  · -- The right-hand side is a sum of nonnegative coordinate norms.
    exact Finset.sum_nonneg fun i _ ↦ norm_nonneg (v i)
  · -- Squaring both sides reduces the comparison to the standard finite-sum inequality.
    simpa [sq] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin n ↦ ‖v i‖) (fun i _ ↦ norm_nonneg (v i))

/-- Helper for Theorem 3.1.3.1: every `ℓ₁`-ball is contained in the metric ball of the same
radius. -/
-- Proof sketch: membership in the seminorm ball gives `l1Seminorm n (y - x₀) < r`; the previous
-- norm comparison turns this into the metric-ball inequality `dist y x₀ < r`.
private theorem l1_ball_subset_metric_ball {x0 : E} {r : ℝ} :
    (l1Seminorm n).ball x0 r ⊆ Metric.ball x0 r := by
  intro y hy
  refine Metric.mem_ball.2 ?_
  have hy' : l1Seminorm n (y - x0) < r := (Seminorm.mem_ball _).1 hy
  exact lt_of_le_of_lt (norm_le_l1Seminorm (n := n) (y - x0)) <| by
    simpa [dist_eq_norm] using hy'

/-
Theorem 3.1.3.1 lies in the chapter's local regularity domain for convex `WithTop ℝ`-valued
functions on Euclidean space.

Sampled owner-style declarations:
- `ConvexOn.locallyLipschitzOn_interior` in mathlib;
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real part;
- `EuclideanSpace.l1Seminorm` in `Definition_3_7`, the chapter owner for `ℓ₁` geometry;
- `Seminorm.ball`, the canonical owner for open seminorm balls.

Best owner abstraction:
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- source-facing: a local `ℓ₁`-ball estimate on `(l1Seminorm n).ball x0 ε`;
- bridge/view: the metric-ball regularity theorem from `Theorem_3_1_11` together with the
  coordinate identity `l1Seminorm_apply`.

Primitive data:
- the convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior point `hx0 : x0 ∈ interior (dom f)`.

Derived API:
- the `ℓ₁`-ball inclusion into `dom f`;
- the local `ℓ₁`-Lipschitz estimate for `withTopRealPart f`.

This theorem remains source-facing because the textbook statement is explicitly an `ℓ₁`-ball local
estimate, but its ambient convex-analysis and `ℓ₁`-geometry data are already owned upstream. The
refinement therefore deletes the parallel inline effective-domain and coordinate-ball encodings and
states the theorem directly on those owner abstractions.
-/

/-- Theorem 3.1.3.1: if a convex `ℝ ∪ {+∞}`-valued function has `x₀` in the interior of its
effective domain, then some `ℓ₁`-ball about `x₀` stays inside the effective domain and the
finite-value part of the function satisfies a local `ℓ₁`-Lipschitz estimate there. The bounded
image consequence is recorded separately downstream. -/
-- Proof sketch: apply mathlib's local regularity theorem
-- `ConvexOn.locallyLipschitzOn_interior` to the convex real-valued representative
-- `withTopRealPart f` on the effective domain `dom f`. Then pass from the ambient Euclidean norm
-- to the chapter owner `ℓ₁` seminorm `l1Seminorm n`, and shrink the neighborhood
-- to an `ℓ₁`-ball contained in `dom f`.
theorem exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ ε > 0, ∃ L > 0,
      (l1Seminorm n).ball x0 ε ⊆ dom f ∧
        ∀ ⦃y : E⦄, y ∈ (l1Seminorm n).ball x0 ε →
          |withTopRealPart f y - withTopRealPart f x0| ≤
            L * l1Seminorm n (y - x0) := by
  obtain ⟨ε, hε, hmetric, K, hK⟩ :=
    exists_metric_ball_lipschitzOnWith_of_mem_interior_local (n := n) hf hx0
  refine ⟨ε, hε, (K : ℝ) + 1, by positivity, ?_, ?_⟩
  · -- Transport the effective-domain inclusion from the metric ball to the `ℓ₁` ball.
    exact Set.Subset.trans (l1_ball_subset_metric_ball (n := n)) hmetric
  · intro y hy
    have hyMetric : y ∈ Metric.ball x0 ε := l1_ball_subset_metric_ball (n := n) hy
    have hx0Metric : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
    have hdist := hK.dist_le_mul y hyMetric x0 hx0Metric
    rw [Real.dist_eq] at hdist
    -- First use the metric-ball Lipschitz estimate, then compare the ambient norm with `‖·‖₁`.
    calc
      |withTopRealPart f y - withTopRealPart f x0|
          ≤ (K : ℝ) * dist y x0 := hdist
      _ = (K : ℝ) * ‖y - x0‖ := by rw [dist_eq_norm]
      _ ≤ (K : ℝ) * l1Seminorm n (y - x0) := by
        gcongr
        exact norm_le_l1Seminorm (n := n) (y - x0)
      _ ≤ ((K : ℝ) + 1) * l1Seminorm n (y - x0) := by
        -- Enlarging the constant by `1` only needs the nonnegativity of the `ℓ₁` seminorm.
        have hnonneg : 0 ≤ l1Seminorm n (y - x0) := by
          rw [EuclideanSpace.l1Seminorm_apply]
          exact Finset.sum_nonneg fun i _ ↦ norm_nonneg ((y - x0) i)
        nlinarith [hnonneg]

end ConvexOn
