/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 13.22 is `source-facing`: the source definition is a positive-modulus, nonempty
strongly convex set. Domain sampling against Chapter 5's function-side owner `StrongConvexOn`,
Chapter 2's set-side owner `IsCone`, and mathlib's `StrongConvexOn` shows that the primitive set
data is only the closed-ball inclusion property itself. The canonical owner in this chapter is
therefore `Set.StrongConvex`, while positivity and nonemptiness remain in the source-facing
wrapper `Set.StronglyConvexWith`. -/

namespace Set

/- Definition 13.22 (1), core/canonical owner: the primitive geometric data is the closed-ball
inclusion along each chord of the set. -/
/-- A set is `σ`-strongly convex when every point of each chord carries the closed ball of radius
`(σ / 2) t (1 - t) ‖x - y‖²` inside the set. -/
def StrongConvex (C : Set E) (σ : ℝ) : Prop :=
  ∀ ⦃x : E⦄, x ∈ C → ∀ ⦃y : E⦄, y ∈ C → ∀ ⦃t : ℝ⦄, t ∈ Icc (0 : ℝ) 1 →
    Metric.closedBall (t • x + (1 - t) • y)
      ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) ⊆ C

/-- Helper for Definition 13.22: the strong-convexity radius is nonnegative when the modulus is
nonnegative and the interpolation weight lies in `[0, 1]`. -/
lemma strong_convex_radius_nonneg {σ t : ℝ} {x y : E} (hσ : 0 ≤ σ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) := by
  -- Each factor in the radius formula is nonnegative on `[0, 1]`.
  have hσ_half : 0 ≤ σ / 2 := by
    nlinarith
  have h_one_sub_t : 0 ≤ 1 - t := by
    linarith [ht.2]
  have hnorm_sq : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
    positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hσ_half ht.1) h_one_sub_t) hnorm_sq

/-- Helper for Definition 13.22: increasing the modulus increases the closed-ball radius in the
strong-convexity inclusion. -/
lemma strong_convex_radius_mono {σ τ t : ℝ} {x y : E} (hστ : σ ≤ τ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) ≤
      ((τ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) := by
  -- Separate the modulus from the nonnegative geometric factor and compare only the modulus term.
  have hgeom : 0 ≤ t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by
    have h_one_sub_t : 0 ≤ 1 - t := by
      linarith [ht.2]
    have hnorm_sq : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
      positivity
    exact mul_nonneg (mul_nonneg ht.1 h_one_sub_t) hnorm_sq
  have hhalf : σ / 2 ≤ τ / 2 := by
    nlinarith
  calc
    (σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)
        = (σ / 2) * (t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) := by ring
    _ ≤ (τ / 2) * (t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hhalf hgeom
    _ = (τ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) := by ring

/-- Lowering the modulus preserves strong convexity of sets. -/
theorem StrongConvex.mono {C : Set E} {σ τ : ℝ} (hστ : σ ≤ τ) (hC : StrongConvex C τ) :
    StrongConvex C σ := by
  intro x hx y hy t ht
  -- The smaller-radius closed ball sits inside the larger-radius ball furnished by `hC`.
  refine (Metric.closedBall_subset_closedBall (strong_convex_radius_mono hστ ht)).trans ?_
  exact hC hx hy ht

/-- Definition 13.22 (1): a nonempty set `C` is `σ`-strongly convex when `σ > 0`; for every
`x, y ∈ C` plus every `t ∈ [0, 1]`, the closed ball centered at the convex combination
`t • x + (1 - t) • y`, with radius `(σ / 2) * t * (1 - t) * ‖x - y‖²`, is contained in `C`. -/
class StronglyConvexWith (C : Set E) (σ : ℝ) : Prop where
  sigma_pos : 0 < σ
  nonempty : C.Nonempty
  strongConvex : StrongConvex C σ

/-- The source-facing strong-convexity owner exposes the primitive closed-ball inclusion owner to
typeclass search. -/
instance instFactStrongConvexOfStronglyConvexWith {C : Set E} {σ : ℝ}
    [hC : StronglyConvexWith C σ] : Fact (StrongConvex C σ) where
  out := hC.strongConvex

/-- Expanding `StronglyConvexWith C σ` gives the defining closed-ball inclusion of
`Set.StrongConvex C σ`. -/
theorem StronglyConvexWith.segment_closedBall_subset {C : Set E} {σ : ℝ}
    (hC : StronglyConvexWith C σ) {x y : E} (hx : x ∈ C) (hy : y ∈ C) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Metric.closedBall (t • x + (1 - t) • y)
      ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ)) ⊆ C :=
  hC.strongConvex hx hy ht

-- Proof sketch: for `x, y ∈ C` and `t ∈ [0, 1]`, the center
-- `t • x + (1 - t) • y` belongs to the closed ball appearing in
-- `segment_closedBall_subset` because its distance to the center is `0` and the radius is
-- nonnegative. Applying the inclusion yields closure under convex combinations.
/-- A `σ`-strongly convex set is convex whenever `σ ≥ 0`. -/
theorem StrongConvex.convex {C : Set E} {σ : ℝ} (hC : StrongConvex C σ) (hσ : 0 ≤ σ) :
    Convex ℝ C := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  -- Re-express the second coefficient as `1 - a` so the point matches the strong-convex center.
  have hb_eq : b = 1 - a := by
    linarith
  have haIcc : a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact ha
    · linarith
  have hradius :
      0 ≤ ((σ / 2) * a * (1 - a) * ‖x - y‖ ^ (2 : ℕ)) :=
    strong_convex_radius_nonneg hσ haIcc
  have hcenter :
      a • x + b • y ∈
        Metric.closedBall (a • x + (1 - a) • y)
          ((σ / 2) * a * (1 - a) * ‖x - y‖ ^ (2 : ℕ)) := by
    -- The center belongs to its own closed ball once the radius is nonnegative.
    simpa [hb_eq] using
      (Metric.mem_closedBall_self (x := (a • x + (1 - a) • y)) hradius)
  exact hC hx hy haIcc hcenter

/-- A `σ`-strongly convex set in the source-facing sense is convex. -/
theorem StronglyConvexWith.convex {C : Set E} {σ : ℝ} (hC : StronglyConvexWith C σ) :
    Convex ℝ C :=
  hC.strongConvex.convex hC.sigma_pos.le

/-- The whole space satisfies the primitive strong-convexity owner for every modulus. -/
theorem strongConvex_univ {σ : ℝ} : StrongConvex (univ : Set E) σ := by
  intro x _ y _ t ht
  exact subset_univ _

/-- The whole space is `σ`-strongly convex in the source-facing sense for every positive
modulus. -/
instance {σ : ℝ} [Fact (0 < σ)] : StronglyConvexWith (univ : Set E) σ where
  sigma_pos := Fact.out
  nonempty := univ_nonempty
  strongConvex := strongConvex_univ

/-- Definition 13.22 (2): a set is strongly convex if it is `σ`-strongly convex for some positive
modulus `σ`. -/
abbrev StronglyConvex (C : Set E) : Prop :=
  ∃ σ : ℝ, StronglyConvexWith C σ

end Set

end
