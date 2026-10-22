/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall convexOn_toReal_of_is_convex_function
recall ConvexOn.locallyLipschitzOn_interior
recall LocallyLipschitzOn.exists_lipschitzOnWith_of_compact

-- Proof sketch: the Chapter 2 bridge converts convexity of `f : E → EReal` into convexity of the
-- finite-valued restriction `x ↦ (f x).toReal` on `effective_domain f`, and mathlib's canonical
-- owner theorem then gives local Lipschitz continuity on the interior of that domain.
/-- Companion bridge for Theorem 2.9: if a convex extended-real-valued function never takes the
value `⊥` on its effective domain, then its finite-valued restriction
`x ↦ (f x).toReal` is locally Lipschitz on `interior (effective_domain f)`. -/
theorem convex_function_toReal_locallyLipschitzOn_interior
    (f : E → EReal) (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    LocallyLipschitzOn (interior (effective_domain f)) (fun x ↦ (f x).toReal) :=
  (convexOn_toReal_of_is_convex_function hf h_ne_bot).locallyLipschitzOn_interior

-- Proof sketch: use the interior assumption to choose a closed ball contained in
-- `effective_domain f`. The hypothesis `h_ne_bot` supplies the exact codomain restriction needed
-- for the chapter bridge `convexOn_toReal_of_is_convex_function`, so that `x ↦ (f x).toReal` is a
-- genuine real-valued convex function on `effective_domain f`. Apply the finite-dimensional theorem
-- that convex functions are locally Lipschitz on the interior of their domain, then shrink to a
-- closed ball and rewrite the resulting Lipschitz estimate as the displayed bound at `x0`.
/-- Companion bridge for Theorem 2.9: an interior point of `effective_domain f` admits a closed
ball neighborhood contained in `interior (effective_domain f)` on which `x ↦ (f x).toReal` is
Lipschitz. -/
theorem exists_closedBall_lipschitzOnWith_toReal_of_mem_interior
    (f : E → EReal) (x0 : E) (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥)
    (hx0 : x0 ∈ interior (effective_domain f)) :
    ∃ ε > 0, ∃ L : NNReal,
      Metric.closedBall x0 ε ⊆ interior (effective_domain f) ∧
      LipschitzOnWith L (fun x ↦ (f x).toReal) (Metric.closedBall x0 ε) := by
  have hloc :
      LocallyLipschitzOn (interior (effective_domain f)) (fun x ↦ (f x).toReal) :=
    convex_function_toReal_locallyLipschitzOn_interior f hf h_ne_bot
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨R, hR_pos, hR_subset⟩
  let ε : ℝ := R / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hclosed_subset : Metric.closedBall x0 ε ⊆ interior (effective_domain f) := by
    intro x hx
    exact hR_subset ((Metric.closedBall_subset_ball (half_lt_self hR_pos)) hx)
  have hcompact : IsCompact (Metric.closedBall x0 ε) := isCompact_closedBall x0 ε
  obtain ⟨L, hL⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact (hloc.mono hclosed_subset)
  exact ⟨ε, hε_pos, L, hclosed_subset, hL⟩

/-- Theorem 2.9: a convex extended-real-valued function is locally Lipschitz at every point of the
interior of its effective domain, in the sense that some closed ball around the point is contained
in the domain and satisfies the estimate `|(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖`. -/
theorem convex_function_exists_closedBall_lipschitz_bound_at_interior_point
    (f : E → EReal) (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) (x0 : E)
    (hx0 : x0 ∈ interior (effective_domain f)) :
    ∃ ε > 0, ∃ L > 0,
      Metric.closedBall x0 ε ⊆ effective_domain f ∧
        ∀ x ∈ Metric.closedBall x0 ε,
          |(f x).toReal - (f x0).toReal| ≤ L * ‖x - x0‖ := by
  obtain ⟨ε, hε_pos, L, hclosed_subset, hLip⟩ :=
    exists_closedBall_lipschitzOnWith_toReal_of_mem_interior f x0 hf h_ne_bot hx0
  have hx0_closed : x0 ∈ Metric.closedBall x0 ε := by
    simp [Metric.mem_closedBall, hε_pos.le]
  refine ⟨ε, hε_pos, (L : ℝ) + 1, by positivity, ?_⟩
  constructor
  · intro x hx
    exact interior_subset (hclosed_subset hx)
  · intro x hx
    calc
      |(f x).toReal - (f x0).toReal| ≤ (L : ℝ) * ‖x - x0‖ := by
        simpa [Real.dist_eq, dist_eq_norm] using hLip.dist_le_mul x hx x0 hx0_closed
      _ ≤ ((L : ℝ) + 1) * ‖x - x0‖ := by
        nlinarith [norm_nonneg (x - x0)]

end
