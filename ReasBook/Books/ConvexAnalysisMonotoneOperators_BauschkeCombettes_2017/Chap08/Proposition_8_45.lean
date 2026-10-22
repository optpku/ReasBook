/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Theorem_8_38

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Proposition 8.45: a real upper bound on an open ball already makes the center value
finite, so the center lies in the effective domain. -/
private lemma center_mem_effectiveDomain_of_boundedAbove_ball
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {δ M : ℝ}
    (hδ : 0 < δ)
    (hM : ∀ y ∈ Metric.ball x δ, (f y : EReal) ≤ (M : EReal)) :
    x ∈ effectiveDomain f := by
  -- Evaluate the upper bound at the center point, which lies in the ball by positive radius.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hM x (Metric.mem_ball_self hδ)) (EReal.coe_lt_top M)

/-- Helper for Proposition 8.45: a real upper bound on a ball gives a finite `EReal` supremum for
the image of that ball. -/
private lemma finite_sup_ball_lt_top_of_boundedAbove_ball
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {δ M : ℝ}
    (hM : ∀ y ∈ Metric.ball x δ, (f y : EReal) ≤ (M : EReal)) :
    sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x δ) < ⊤ := by
  -- Every image value is bounded by the same real number `M`, so the supremum stays finite.
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_top M)
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hM y hy

/-- Helper for Proposition 8.45: a local Lipschitz bound for the real-valued representative gives
an open product ball contained in the real-height epigraph. -/
private lemma interior_epigraph_nonempty_of_local_lipschitz
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {β : NNReal} {r : ℝ}
    (hr : 0 < r)
    (hball_dom : Metric.ball x r ⊆ effectiveDomain f)
    (hLip : LipschitzOnWith β (fun y ↦ (f y : EReal).toReal) (Metric.ball x r)) :
    (interior (epigraph (fun y : H ↦ (f y : EReal)))).Nonempty := by
  let σ : ℝ := 2 * (β : ℝ) * r + 1
  let γ : ℝ := min r (σ / 2)
  have hβ_nonneg : 0 ≤ (β : ℝ) := β.2
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    exact lt_min hr (half_pos hσ_pos)
  have hγ_le_r : γ ≤ r := by
    dsimp [γ]
    exact min_le_left _ _
  have hγ_le_halfσ : γ ≤ σ / 2 := by
    dsimp [γ]
    exact min_le_right _ _
  have hβr_lt_halfσ : (β : ℝ) * r < σ / 2 := by
    dsimp [σ]
    linarith
  refine ⟨(x, (f x : EReal).toReal + σ), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  -- It is enough to exhibit one metric ball around the chosen point that stays in the epigraph.
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ hγ_pos) ?_
  intro p hp
  rcases p with ⟨y, η⟩
  rw [Metric.mem_ball, Prod.dist_eq] at hp
  rw [mem_epigraph_iff]
  rcases max_lt_iff.mp hp with ⟨hy_dist, hη_dist⟩
  have hy_ball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hy_dist hγ_le_r
  have hy_dom : y ∈ effectiveDomain f := hball_dom hy_ball
  have hx_ball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hdist_le :
      dist ((f y : EReal).toReal) ((f x : EReal).toReal) ≤ (β : ℝ) * dist y x := by
    simpa using hLip.dist_le_mul y hy_ball x hx_ball
  have hvalue_sub_le :
      (f y : EReal).toReal - (f x : EReal).toReal ≤ (β : ℝ) * dist y x := by
    have habs_le :
        |(f y : EReal).toReal - (f x : EReal).toReal| ≤ (β : ℝ) * dist y x := by
      simpa [Real.dist_eq] using hdist_le
    exact (abs_le.mp habs_le).2
  have hvalue_lt : (f y : EReal).toReal < (f x : EReal).toReal + σ / 2 := by
    have hy_dist_lt_r : dist y x < r := lt_of_lt_of_le hy_dist hγ_le_r
    have hmul_le : (β : ℝ) * dist y x ≤ (β : ℝ) * r := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hy_dist_lt_r) hβ_nonneg
    have hvalue_sub_lt : (f y : EReal).toReal - (f x : EReal).toReal < σ / 2 := by
      exact lt_of_le_of_lt (le_trans hvalue_sub_le hmul_le) hβr_lt_halfσ
    linarith
  have hη_gt : (f x : EReal).toReal + σ / 2 < η := by
    have hη_abs :
        |η - ((f x : EReal).toReal + σ)| < γ := by
      simpa [Real.dist_eq] using hη_dist
    have hlower : -γ < η - ((f x : EReal).toReal + σ) := (abs_lt.mp hη_abs).1
    linarith
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hfy_eq : (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) := by
    symm
    exact EReal.coe_toReal hfy_top hfy_bot
  have hcast_le : (((f y : EReal).toReal : ℝ) : EReal) ≤ (η : EReal) := by
    exact EReal.coe_le_coe (le_of_lt (lt_trans hvalue_lt hη_gt))
  -- Rewrite the finite function value through `toReal`, then compare with the real ordinate `η`.
  rw [hfy_eq]
  exact hcast_le

-- Proof sketch: the upper bound on `Metric.ball x δ` gives a finite real value at the center and a
-- finite supremum on that ball. Apply Theorem 8.38 to obtain a local Lipschitz bound near `x`,
-- then choose a point strictly above the graph at height `f x + ρ` and show that a small product
-- ball around it stays inside the epigraph.
/-- Proposition 8.45: if a convex `]-∞,+∞]`-valued function is bounded above on some open ball,
then its real-height epigraph has nonempty interior. -/
theorem interior_epigraph_nonempty_of_convexOn_of_boundedAbove_ball
    [NormedSpace ℝ H]
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {δ M : ℝ}
    (hconv : ConvexOn f (effectiveDomain f)) (hδ : 0 < δ)
    (hM : ∀ y ∈ Metric.ball x δ, (f y : EReal) ≤ (M : EReal)) :
    (interior (epigraph (fun y : H ↦ (f y : EReal)))).Nonempty := by
  have hx : x ∈ effectiveDomain f :=
    center_mem_effectiveDomain_of_boundedAbove_ball hδ hM
  have htfae :=
    convex_tfae_locallyLipschitzNear_continuousAt_boundedBall_finiteSupBall
      f hconv (x₀ := x) hx
  have hfour : ∃ ρ > 0, sSup ((fun y ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤ := by
    -- The bounded-above hypothesis provides the clause-(4) input at the same center and radius.
    exact ⟨δ, hδ, finite_sup_ball_lt_top_of_boundedAbove_ball hM⟩
  obtain ⟨β, r, hr, hball_dom, hLip⟩ := (List.TFAE.out htfae 3 0).mp hfour
  -- The local Lipschitz estimate creates a full product ball above the graph.
  exact interior_epigraph_nonempty_of_local_lipschitz hr hball_dom hLip

end ERealFunction
