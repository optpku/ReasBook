/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 8.2 is `source-facing`: the textbook hypothesis is that `d` is a descent direction of
`f` at `x` in the sense of Definition 8.3, namely that the right directional difference quotient
has a negative limit. -/

/-- Helper for Lemma 8.2: a short ray from an interior point stays inside `effective_domain f`. -/
lemma exists_smallRightInterval_ray_subset_effectiveDomain
    (f : E → EReal) {x d : E} (hx : x ∈ interior (effective_domain f)) (hd : d ≠ 0) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) ε → x + t • d ∈ effective_domain f := by
  -- Choose a ball around `x` inside the effective domain, then shrink the ray so the whole
  -- interval `t ∈ (0, ε]` stays strictly inside that ball.
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨R, hR_pos, hR_subset⟩
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let ε : ℝ := R / (2 * ‖d‖)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε_pos, ?_⟩
  intro t ht
  have ht_mul : t * ‖d‖ ≤ ε * ‖d‖ := by
    exact mul_le_mul_of_nonneg_right ht.2 hnorm.le
  have htwo_norm : 2 * ‖d‖ ≠ 0 := by
    positivity
  have hε_mul : ε * ‖d‖ = R / 2 := by
    dsimp [ε]
    field_simp [htwo_norm]
  have hdist : dist (x + t • d) x < R := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
    nlinarith [ht_mul, hR_pos]
  exact interior_subset (hR_subset (by simpa [Metric.mem_ball] using hdist))

/-- Helper for Lemma 8.2: a negative directional difference quotient forces strict decrease of the
function value at that step. -/
lemma lt_of_diffQuotient_neg
    (f : E → EReal) {x d : E} {t : ℝ}
    (hfx_bot : f x ≠ ⊥) (hfx_top : f x ≠ ⊤) (ht : 0 < t)
    (hq : (f (x + t • d) - f x) / (t : EReal) < 0) :
    f (x + t • d) < f x := by
  -- Multiply the quotient inequality by the positive step, then rewrite the negative difference as
  -- a strict comparison of the two function values.
  have htE : (0 : EReal) < (t : EReal) := by
    exact_mod_cast ht
  have hdiff : f (x + t • d) - f x < (0 : EReal) := by
    rw [EReal.div_lt_iff htE (by simp)] at hq
    simpa using hq
  have hlt : f (x + t • d) < (0 : EReal) + f x := by
    exact (EReal.sub_lt_iff (.inl hfx_bot) (.inl hfx_top)).1 hdiff
  simpa using hlt

-- Proof sketch: unfold the descent-direction hypothesis to get a negative right-limit `ℓ < 0`
-- for the directional difference quotient. Then the quotient is negative on some right interval,
-- which yields `f (x + t • d) < f x` for all sufficiently small `t > 0`. Since
-- `x ∈ interior (effective_domain f)`, a small ball around `x` lies in `effective_domain f`;
-- because `d ≠ 0` is built into the descent-direction predicate, shrinking the interval keeps
-- `x + t • d` inside that ball.
/-- Lemma 8.2: if `f : E → (-∞, ∞]` is represented by an `EReal`-valued function with no `⊥`
values, `x` lies in the interior of `dom(f)`, and `d` is a descent direction of `f` at `x`, then
`f` strictly decreases along the ray `x + t • d` for all sufficiently small `t > 0`, and those
nearby points remain in `dom(f)`. -/
theorem exists_strict_decrease_along_descent_direction
    (f : E → EReal) (x d : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hx : x ∈ interior (effective_domain f))
    (hd : is_descent_direction_at f x d) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) ε →
      x + t • d ∈ effective_domain f ∧ f (x + t • d) < f x := by
  -- Unpack the descent-direction hypothesis into a negative right-limit for the quotient.
  rw [is_descent_direction_at_iff] at hd
  rcases hd with ⟨hd0, ℓ, hqTendsto, hℓneg⟩
  -- Record the endpoint side conditions needed for the quotient-to-value comparison.
  have hx_dom : x ∈ effective_domain f := interior_subset hx
  have hfx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx_dom).ne
  have hfx_bot : f x ≠ ⊥ := h_ne_bot x
  -- Keep a short ray inside the effective domain using interior membership at `x`.
  obtain ⟨εdom, hεdom_pos, hεdom⟩ :=
    exists_smallRightInterval_ray_subset_effectiveDomain (f := f) (x := x) (d := d) hx hd0
  let q : ℝ → EReal := fun t ↦ (f (x + t • d) - f x) / (t : EReal)
  -- The quotient stays negative on some punctured right-neighborhood of `0`.
  have hnegEvent : ∀ᶠ t in 𝓝[>] (0 : ℝ), q t < 0 := by
    simpa [q] using hqTendsto.eventually (isOpen_Iio.mem_nhds hℓneg)
  have hnegMem : {t : ℝ | q t < 0} ∈ 𝓝[>] (0 : ℝ) := by
    simpa [q] using hnegEvent
  obtain ⟨εq, hεq_pos, hεq⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hnegMem
  refine ⟨min εq εdom, lt_min hεq_pos hεdom_pos, ?_⟩
  intro t ht
  -- Intersect the two right-neighborhood controls and finish with the quotient comparison lemma.
  have htq : q t < 0 := by
    exact hεq ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have htdom : x + t • d ∈ effective_domain f := by
    exact hεdom t ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  refine ⟨htdom, ?_⟩
  exact lt_of_diffQuotient_neg (f := f) (x := x) (d := d) hfx_bot hfx_top ht.1 htq

/-- Any Chapter 8 descent direction yields the local strict decrease conclusion of Lemma 8.2. -/
theorem exists_strict_decrease_of_is_descent_direction_at
    (f : E → EReal) (x d : E) (h_ne_bot : ∀ y, f y ≠ ⊥)
    (hx : x ∈ interior (effective_domain f))
    (hd : is_descent_direction_at f x d) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) ε →
      x + t • d ∈ effective_domain f ∧ f (x + t • d) < f x := by
  -- Reuse the source-facing theorem so the file has a single canonical proof owner.
  exact exists_strict_decrease_along_descent_direction f x d h_ne_bot hx hd

end
