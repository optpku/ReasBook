/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.27 is `source-facing` in the Chapter 3 convex-analysis API. Its owner declarations
are already the project primitives `effective_domain`, `is_convex_function`, and the
continuous-dual bridge `strongDualSubdifferential`, together with mathlib's owner
`LipschitzOnWith`. The textbook hypothesis is the pointwise norm bound
`∀ g ∈ ∂ₛ f(x), ‖g‖ ≤ L`; the closed-ball reformulation is kept only as a thin companion bridge
for metric-owner API. -/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (f : E → EReal) (X : Set E) (L : NNReal)

omit [FiniteDimensional ℝ E] in
/-- Companion bridge for Theorem 3.27: at a fixed point, bounding every strong-dual subgradient
by `L` is equivalent to placing `∂ₛf(x)` inside the dual closed ball of radius `L`. -/
lemma strongDualSubdifferential_subset_closedBall_iff_norm_le {x : E} :
    ∂ₛf(x) ⊆ closedBall (0 : StrongDual ℝ E) L ↔
      ∀ ⦃g : StrongDual ℝ E⦄, g ∈ ∂ₛf(x) → ‖g‖ ≤ L := by
  constructor
  · intro h g hg
    simpa [Metric.mem_closedBall, dist_eq_norm] using h hg
  · intro h g hg
    simpa [Metric.mem_closedBall, dist_eq_norm] using h hg

-- Proof sketch: for `x, y ∈ X`, use `hX_subset` and the interior-point existence theorem to choose
-- subgradients `gₓ ∈ ∂ f(x)` and `gᵧ ∈ ∂ f(y)`. Apply the subgradient inequalities in both
-- directions and bound the pairings by `ContinuousLinearMap.le_opNorm`, using `hbound` to control
-- the norms of `gₓ` and `gᵧ`; this gives the two one-sided estimates needed for
-- `LipschitzOnWith L (fun x ↦ (f x).toReal) X`.
/-- Helper for Theorem 3.27: if `f` never takes the value `-∞` on its effective domain and every
subgradient at a point of `X` has norm at most `L`, then the finite-valued restriction
`x ↦ (f x).toReal` is `L`-Lipschitz on `X`. -/
theorem lipschitzOnWith_toReal_of_subdifferential_norm_le_on
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) (hf_convex : is_convex_function f)
    (hX_subset : X ⊆ interior (effective_domain f))
    (hbound : ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
      x ∈ X → g ∈ ∂ₛf(x) → ‖g‖ ≤ L) :
    LipschitzOnWith L (fun x ↦ (f x).toReal) X := by
  -- Build the Lipschitz estimate from the one-sided inequality `f x ≤ f y + L * dist x y`.
  refine LipschitzOnWith.of_le_add_mul L fun x hx y hy ↦ ?_
  have hx_int : x ∈ interior (effective_domain f) := hX_subset hx
  have hx_dom : x ∈ effective_domain f := interior_subset hx_int
  have hy_dom : y ∈ effective_domain f := interior_subset (hX_subset hy)
  rcases subdifferential_nonempty_at_interior_point f x hf_convex hx_int with ⟨g₀, hg₀⟩
  let g : StrongDual ℝ E := LinearMap.toContinuousLinearMap g₀
  have hg : g ∈ ∂ₛf(x) := by
    simpa [g] using hg₀
  have hsub : g (y - x) ≤ (f y).toReal - (f x).toReal := by
    simpa [g] using
      subgradient_eval_le_toReal_sub f x y h_ne_bot hx_dom hy_dom hg₀
  have hsub' : (f x).toReal - (f y).toReal ≤ g (x - y) := by
    have hneg := neg_le_neg hsub
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, map_neg] using hneg
  have hpair : g (x - y) ≤ (L : ℝ) * dist x y := by
    calc
      g (x - y) ≤ |g (x - y)| := le_abs_self _
      _ = ‖g (x - y)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖g‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm g (x - y)
      _ ≤ (L : ℝ) * dist x y := by
        simpa [dist_eq_norm] using
          mul_le_mul_of_nonneg_right (hbound hx hg) (norm_nonneg _)
  -- Rearranging the subgradient inequality gives the required one-sided Lipschitz estimate.
  exact sub_le_iff_le_add'.1 (le_trans hsub' hpair)

/-- Helper for Theorem 3.27: on an open set, an `L`-Lipschitz bound for `x ↦ (f x).toReal`
restricts to every sufficiently small closed ball around `x`, so every strong-dual subgradient at
`x` lies in the closed dual ball of radius `L`. -/
lemma strongDualSubdifferential_subset_closedBall_of_lipschitzOnWith_open
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) (hX_open : IsOpen X)
    (hX_subset : X ⊆ effective_domain f)
    (hLip : LipschitzOnWith L (fun z ↦ (f z).toReal) X) :
    ∀ ⦃x : E⦄, x ∈ X → ∂ₛf(x) ⊆ closedBall (0 : StrongDual ℝ E) L := by
  intro x hx g hg
  rcases Metric.mem_nhds_iff.1 (hX_open.mem_nhds hx) with ⟨ε, hε_pos, hball_subset⟩
  have hclosed_subset : Metric.closedBall x (ε / 2) ⊆ X := by
    intro y hy
    exact hball_subset <| Metric.closedBall_subset_ball (half_lt_self hε_pos) hy
  have hdom : Metric.closedBall x (ε / 2) ⊆ effective_domain f := by
    intro y hy
    exact hX_subset (hclosed_subset hy)
  have hLip_closed :
      LipschitzOnWith L (fun z ↦ (f z).toReal) (Metric.closedBall x (ε / 2)) :=
    hLip.mono hclosed_subset
  -- Apply the closed-ball estimate from Theorem 3.3 on the localized Lipschitz neighborhood.
  exact
    mem_closedBall_of_mem_strongDualSubdifferential_of_lipschitzOnWith
      f x h_ne_bot (half_pos hε_pos) hdom hLip_closed hg

-- Proof sketch: the implication from bounded subgradients to Lipschitz continuity is part (1).
-- Conversely, assume `LipschitzOnWith L (fun x ↦ (f x).toReal) X`, fix `x ∈ X` and
-- `g ∈ ∂ f(x)`, and use `hX_open` to choose a small segment `x + εu ⊆ X` in a unit direction `u`
-- that realizes the dual norm of `g`. Combining the subgradient inequality with the Lipschitz
-- bound along that segment yields `g u ≤ L`, hence `‖g‖ ≤ L`.
/-- Theorem 3.27 (2): if `X` is open, then the finite-valued restriction
`x ↦ (f x).toReal` is `L`-Lipschitz on `X` if and only if every subgradient at a point of `X` has
norm at most `L`, provided `f` never takes the value `-∞` on its effective domain and
`X ⊆ effective_domain f`. -/
theorem lipschitzOnWith_toReal_iff_subdifferential_norm_le_on_of_isOpen
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) (hf_convex : is_convex_function f)
    (hX_open : IsOpen X) (hX_subset : X ⊆ effective_domain f) :
    LipschitzOnWith L (fun x ↦ (f x).toReal) X ↔
      ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
        x ∈ X → g ∈ ∂ₛf(x) → ‖g‖ ≤ L := by
  constructor
  · intro hLip x g hx hg
    have hclosed :
        ∂ₛf(x) ⊆ closedBall (0 : StrongDual ℝ E) L :=
      strongDualSubdifferential_subset_closedBall_of_lipschitzOnWith_open
        (f := f) (X := X) (L := L) h_ne_bot hX_open hX_subset hLip hx
    exact
      (strongDualSubdifferential_subset_closedBall_iff_norm_le
        (f := f) (L := L) (x := x)).1 hclosed hg
  · intro hbound
    have hX_interior : X ⊆ interior (effective_domain f) := by
      intro x hx
      exact mem_interior_iff_mem_nhds.2 <|
        Filter.mem_of_superset (hX_open.mem_nhds hx) hX_subset
    -- Reuse part (1) once openness upgrades `X ⊆ effective_domain f` to interior containment.
    exact
      lipschitzOnWith_toReal_of_subdifferential_norm_le_on
        (f := f) (X := X) (L := L) h_ne_bot hf_convex hX_interior hbound

end
