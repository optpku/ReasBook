/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Bornology
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (f : E → EReal) (X : Set E)

/- Theorem 3.5 is `source-facing` in the Chapter 3 convex-analysis API. Its owner declarations are
 already the project primitives `effective_domain`, `is_convex_function`, and the continuous-dual
 bridge `∂ₛ f(x)` from Theorem 3.1; this file keeps the textbook compact-union boundedness
statement directly on that owner API instead of introducing any parallel wrapper. The ambient
properness hypotheses are split according to the two source conclusions: part (1) uses
`is_convex_function f`, `X.Nonempty`, and `X ⊆ interior (effective_domain f)`, while part (2)
uses `∀ y ∈ effective_domain f, f y ≠ ⊥`, `is_convex_function f`, `IsCompact X`, and
`X ⊆ interior (effective_domain f)`. In both cases, `effective_domain f` is derived rather than
kept as a primitive public binder. -/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential

open Metric

/-- Helper for Theorem 3.5: interior points of `effective_domain f` have a nonempty
strong-dual subdifferential. -/
lemma strongDualSubdifferential_nonempty_at_interior_point
    (hconvex : is_convex_function f) {x : E} (hx : x ∈ interior (effective_domain f)) :
    Set.Nonempty (∂ₛ f(x)) := by
  -- Move from ordinary interior to the relative-interior theorem already available in Chapter 3.
  have hx_rel : x ∈ intrinsicInterior ℝ (effective_domain f) :=
    interior_subset_intrinsicInterior hx
  rcases subdifferential_nonempty_at_relativeInterior_point f x hconvex hx_rel with ⟨g, hg⟩
  -- Finite dimensionality upgrades the algebraic subgradient witness to the strong dual.
  exact ⟨LinearMap.toContinuousLinearMap g, by simpa using hg⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.5: a Lipschitz bound on `closure U` bounds every subgradient over the
open set `U` by the same dual closed ball. -/
lemma strongDualSubdifferential_subset_closedBall_of_lipschitzOnWith_closure
    (h_ne_bot : ∀ y ∈ effective_domain f, f y ≠ ⊥) {U : Set E}
    (hU_open : IsOpen U) (hU_closure_subset : closure U ⊆ interior (effective_domain f))
    {L : NNReal} (hLip : LipschitzOnWith L (fun y ↦ (f y).toReal) (closure U)) :
    ∀ ⦃x : E⦄, x ∈ U → ∂ₛ f(x) ⊆ Metric.closedBall (0 : StrongDual ℝ E) L := by
  intro x hx g hg
  have hx_closure : x ∈ closure U := subset_closure hx
  have hx_int : x ∈ interior (effective_domain f) := hU_closure_subset hx_closure
  have hx_dom : x ∈ effective_domain f := interior_subset hx_int
  have hx_ne_bot : f x ≠ ⊥ := h_ne_bot x hx_dom
  have hx_ne_top : f x ≠ ⊤ := ne_of_lt hx_dom
  have hg_sub : (g : Module.Dual ℝ E) ∈ ∂ f(x) := by
    simpa using hg
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [ContinuousLinearMap.opNorm_le_iff]
  · intro u
    -- Bound the evaluation of `g` in one direction using a short segment that stays in `U`.
    have hupper : ∀ v : E, g v ≤ (L : ℝ) * ‖v‖ := by
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · rcases Metric.mem_nhds_iff.1 (hU_open.mem_nhds hx) with ⟨ε, hε, hεU⟩
        let t : ℝ := ε / (‖v‖ + 1)
        have ht_pos : 0 < t := by
          dsimp [t]
          positivity
        have ht_nonneg : 0 ≤ t := ht_pos.le
        have htv : t * ‖v‖ < ε := by
          have hmul_lt : t * ‖v‖ < t * (‖v‖ + 1) := by
            nlinarith [ht_pos]
          have hmul_eq : t * (‖v‖ + 1) = ε := by
            dsimp [t]
            field_simp
          exact hmul_lt.trans_eq hmul_eq
        have hnorm_tv : ‖t • v‖ < ε := by
          simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using htv
        have hxt_mem : x + t • v ∈ U := by
          apply hεU
          simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using hnorm_tv
        have hxt_closure : x + t • v ∈ closure U := subset_closure hxt_mem
        have hxt_int : x + t • v ∈ interior (effective_domain f) := hU_closure_subset hxt_closure
        have hxt_dom : x + t • v ∈ effective_domain f := interior_subset hxt_int
        have hxt_ne_bot : f (x + t • v) ≠ ⊥ := h_ne_bot _ hxt_dom
        have hxt_ne_top : f (x + t • v) ≠ ⊤ := ne_of_lt hxt_dom
        have hsub :
            f x + (g ((x + t • v) - x) : EReal) ≤ f (x + t • v) := by
          simpa [ge_iff_le] using (mem_subdifferential.mp hg_sub).2 (x + t • v)
        have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal hx_ne_top hx_ne_bot).symm
        have hxt_eq : f (x + t • v) = ((((f (x + t • v)).toReal : ℝ) : EReal)) :=
          (EReal.coe_toReal hxt_ne_top hxt_ne_bot).symm
        have hsub_ereal :
            (((f x).toReal : ℝ) : EReal) + (((t * g v : ℝ) : EReal)) ≤
              (((f (x + t • v)).toReal : ℝ) : EReal) := by
          calc
            (((f x).toReal : ℝ) : EReal) + (((t * g v : ℝ) : EReal)) =
                f x + (g ((x + t • v) - x) : EReal) := by
                  rw [hfx_eq, EReal.toReal_coe]
                  simp [sub_eq_add_neg, add_left_comm, add_comm, smul_eq_mul]
            _ ≤ f (x + t • v) := hsub
            _ = (((f (x + t • v)).toReal : ℝ) : EReal) := hxt_eq
        have hsub_real : (f x).toReal + t * g v ≤ (f (x + t • v)).toReal := by
          exact_mod_cast hsub_ereal
        have hLip_le :
            (f (x + t • v)).toReal ≤ (f x).toReal + (L : ℝ) * dist (x + t • v) x := by
          exact (LipschitzOnWith.iff_le_add_mul.mp hLip) _ hxt_closure _ hx_closure
        have hdist_eq : dist (x + t • v) x = t * ‖v‖ := by
          calc
            dist (x + t • v) x = ‖t • v‖ := by
              simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
            _ = t * ‖v‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
        have hscaled : t * g v ≤ t * ((L : ℝ) * ‖v‖) := by
          have hdist_le : t * g v ≤ (L : ℝ) * dist (x + t • v) x := by
            linarith
          calc
            t * g v ≤ (L : ℝ) * dist (x + t • v) x := hdist_le
            _ = t * ((L : ℝ) * ‖v‖) := by
              rw [hdist_eq]
              ring
        nlinarith [hscaled, ht_pos]
    -- Apply the one-sided estimate to `u` and `-u` to control the absolute value.
    have hupper_neg : g (-u) ≤ (L : ℝ) * ‖u‖ := by
      simpa [norm_neg] using hupper (-u)
    have hlower : -((L : ℝ) * ‖u‖) ≤ g u := by
      have hneg : -g u ≤ (L : ℝ) * ‖u‖ := by
        simpa using hupper_neg
      linarith
    have habs : |g u| ≤ (L : ℝ) * ‖u‖ := abs_le.2 ⟨hlower, hupper u⟩
    simpa [Real.norm_eq_abs] using habs
  · exact_mod_cast L.2

-- Proof sketch: choose `x ∈ X` and apply the interior-point existence theorem to the
-- continuous-dual bridge `∂ₛ f(x)`.
/-- Nonemptiness part of Theorem 3.5: if `f` is a convex extended-real-valued function and the
source text assumes
that `X` is a nonempty compact subset of `interior (dom(f))`, then the union
`⋃ x ∈ X, ∂ₛ f(x)` is nonempty. Compactness and any separate no-`⊥` hypothesis are not used for
this existence conclusion: Chapter 3 already provides subdifferential nonemptiness at interior
points from convexity alone, so the public API keeps only the source-facing assumptions that
change the statement. -/
theorem subdifferential_biUnion_nonempty_of_nonempty_subset_interior
    (hconvex : is_convex_function f) (hX_nonempty : X.Nonempty)
    (hX_subset : X ⊆ interior (effective_domain f)) :
    Set.Nonempty (⋃ x ∈ X, ∂ₛ f(x)) := by
  -- Pick one point of `X` and one strong-dual subgradient at that interior point.
  rcases hX_nonempty with ⟨x, hxX⟩
  rcases
      strongDualSubdifferential_nonempty_at_interior_point
        (f := f) hconvex (hX_subset hxX) with
    ⟨g, hg⟩
  refine ⟨g, ?_⟩
  refine Set.mem_iUnion.2 ⟨x, ?_⟩
  refine Set.mem_iUnion.2 ⟨hxX, ?_⟩
  exact hg

-- Proof sketch: argue by contradiction: choose `x_k ∈ X` and `g_k ∈ ∂f(x_k)` with unbounded dual
-- norm, use compactness of `X` and a positive distance from `X` to the complement of
-- `interior (effective_domain f)`, and combine the subgradient inequality with continuity of `f`
-- on the interior of its effective domain to obtain a uniform contradiction.
/-- Theorem 3.5 (2): if `f` is a convex extended-real-valued function that never takes the value
`⊥` on `effective_domain f`, and `X` is a compact subset of `interior (dom(f))`, then the union
`⋃ x ∈ X, ∂ₛ f(x)` is bounded in the dual norm. The boundedness conclusion does not use
`X.Nonempty`, so the public API omits that redundant source-side binder. The source text packages
this statement under the stronger properness and nonempty-compactness hypotheses; the boundedness
argument used here depends only on the displayed Chapter 3 Lipschitz/boundedness assumptions. -/
theorem subdifferential_biUnion_isBounded_of_isCompact_subset_interior
    (h_ne_bot : ∀ y ∈ effective_domain f, f y ≠ ⊥) (hconvex : is_convex_function f)
    (hX_compact : IsCompact X) (hX_subset : X ⊆ interior (effective_domain f)) :
    IsBounded (⋃ x ∈ X, ∂ₛ f(x)) := by
  -- Thicken `X` to one open neighborhood with compact closure still inside `interior (dom(f))`.
  obtain ⟨U, hU_open, hX_subsetU, hU_closure_subset, hU_closure_compact⟩ :=
    exists_open_between_and_isCompact_closure hX_compact isOpen_interior hX_subset
  have hconvex_toReal :
      ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
    convexOn_toReal_of_is_convex_function hconvex h_ne_bot
  have hloc :
      LocallyLipschitzOn (interior (effective_domain f)) (fun x ↦ (f x).toReal) :=
    hconvex_toReal.locallyLipschitzOn_interior
  obtain ⟨L, hLip⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hU_closure_compact
      (hloc.mono hU_closure_subset)
  -- The Lipschitz control on `closure U` gives one closed ball containing every subgradient above
  -- `X`, so the whole biunion is bounded.
  refine (Metric.isBounded_iff_subset_closedBall (0 : StrongDual ℝ E)).2 ⟨L, ?_⟩
  intro g hg
  rcases Set.mem_iUnion.1 hg with ⟨x, hxg⟩
  rcases Set.mem_iUnion.1 hxg with ⟨hxX, hgx⟩
  exact
    strongDualSubdifferential_subset_closedBall_of_lipschitzOnWith_closure
      (f := f) h_ne_bot hU_open hU_closure_subset hLip (hX_subsetU hxX) hgx

end
