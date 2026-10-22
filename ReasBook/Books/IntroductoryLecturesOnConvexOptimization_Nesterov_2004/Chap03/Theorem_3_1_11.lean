/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.11 lies in the chapter's extended-valued convex local-regularity domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions, together with the metric-topological bridge
  from interior membership to contained balls.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative;
- `Set.interior` and `Metric.mem_nhds_iff`, the canonical topological owners turning interior
  membership into an explicit contained ball;
- `ConvexOn.locallyLipschitzOn_interior` in mathlib, the canonical local-regularity owner for
  convex real-valued functions on the interior of a convex set;
- `LipschitzWith.isBounded_image`, the canonical bounded-image theorem used after obtaining a
  Lipschitz ball.

Best owner abstraction:
- core/canonical: the topological interior owner `interior (dom f)` for the contained-ball
  bridge, together with `ConvexOn.locallyLipschitzOn_interior` on
  `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- source-facing: an explicit metric ball in `dom f`, then Lipschitz and bounded-image
  consequences around interior points of `dom f`;
- bridge/view: the passage from neighborhood statements to concrete metric balls via
  `Metric.mem_nhds_iff` and `Metric.mem_nhdsWithin_iff`.

Primitive data:
- for the source-facing ball-existence bridge: only the interior-point witness
  `hx0 : x0 ∈ interior (dom f)`;
- for the convex-analytic consequences: the convexity witness
  `hf : ConvexOn ℝ (dom f) (withTopRealPart f)` together with the same interior-point witness.

Derived API:
- a metric ball around `x0` contained in `dom f`;
- a common metric ball contained in `dom f` on which `withTopRealPart f` is Lipschitz;
- boundedness of the image of that same ball under `withTopRealPart f`.

Source/core/bridge triage:
- source-facing: the explicit-ball statements recorded below;
- core/canonical: `interior (dom f)` for the purely topological bridge, and
  `ConvexOn.locallyLipschitzOn_interior` for the convex local-regularity owner;
- bridge/view: shrinking neighborhood conclusions to explicit balls.

The previous version kept the raw set `{x | f x < ⊤}`, the ad hoc representative
`fun x ↦ (f x).untopD 0`, a renamed local copy of the mathlib owner theorem, and a purely
topological interior-ball bridge inside the unrelated `ConvexOn` namespace. This refinement
reuses the chapter owners `dom` and `withTopRealPart`, drops the duplicate theorem shell in favor
of a direct recall, weakens the convex-analytic consequences from the concrete model
`EuclideanSpace ℝ (Fin n)` to the canonical finite-dimensional real normed-space layer actually
used by the owner theorem, and places the interior-ball bridge on the weaker `dom`/topological
owner surface it genuinely belongs to.
-/

/- Theorem 3.1.11's main owner is mathlib's `ConvexOn.locallyLipschitzOn_interior`; in the
chapter, it is applied to `C = dom f` and `f = withTopRealPart f`. -/
recall ConvexOn.locallyLipschitzOn_interior

variable {E : Type u}

/-- An interior point of the effective domain admits a metric ball contained in the effective
domain. -/
-- Proof sketch: `x₀ ∈ interior (dom f)` means exactly that `dom f` is a neighborhood of `x₀`;
-- `Metric.mem_nhds_iff` then produces a metric ball contained in `dom f`.
theorem exists_ball_subset_effectiveDomain_of_mem_interior
    [PseudoMetricSpace E] {f : E → WithTop ℝ} {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f := by
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r, hr, hrsub⟩
  exact ⟨r, hr, hrsub.trans interior_subset⟩

namespace ConvexOn

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- At an interior point of the effective domain, the finite-value representative is Lipschitz on
some metric ball around that point, and that ball stays inside the effective domain. -/
-- Proof sketch: apply the owner theorem `hf.locallyLipschitzOn_interior` at `x₀`, then use
-- `Metric.mem_nhdsWithin_iff` to shrink the neighborhood within `interior (dom f)` to a metric
-- ball. Since that smaller ball still lies in `interior (dom f)`, it is also contained in
-- `dom f`.
theorem exists_ball_lipschitzOnWith_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  obtain ⟨K, t, ht, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 ht with ⟨r₁, hr₁, hr₁sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r₂, hr₂, hr₂sub⟩
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, K, hK.mono ?_⟩
  · intro y hy
    exact interior_subset <|
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro y hy
    exact hr₁sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- A convex extended-real-valued function has bounded finite-value image on some ball around any
interior point of its effective domain. -/
-- Proof sketch: obtain a Lipschitz ball from
-- `exists_ball_lipschitzOnWith_of_mem_interior`; that same ball is already known to lie in
-- `dom f`. In a finite-dimensional real normed space, metric balls are bounded, and
-- `LipschitzWith.isBounded_image` bounds the image of that ball under `withTopRealPart f`.
theorem exists_ball_isBounded_image_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      Bornology.IsBounded (withTopRealPart f '' Metric.ball x0 r) := by
  obtain ⟨r, hr, hball, K, hK⟩ := exists_ball_lipschitzOnWith_of_mem_interior hf hx0
  have hclosed :
      Bornology.IsBounded (Metric.closedBall (withTopRealPart f x0) (K * r)) :=
    Metric.isBounded_closedBall
  refine ⟨r, hr, hball, hclosed.subset ?_⟩
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall]
  exact (hK.dist_le_mul y hy x0 (Metric.mem_ball_self hr)).trans <|
    mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le K.coe_nonneg

end ConvexOn
