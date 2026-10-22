/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
Theorem 3.3 is `source-facing` at the chapter owner `subdifferential : Set (Module.Dual ℝ E)`.
Its boundedness conclusion lives naturally on the normed continuous-dual view, so the file reuses
the existing bridge `strongDualSubdifferential` instead of introducing a second `StrongDual`-valued
owner. Domain sampling shows that the stronger chapter existence theorem is
`subdifferential_nonempty_at_relativeInterior_point`; part (1) below is only its finite-dimensional
interior specialization, while part (2) stays on the same owner/bridge surface.
-/
recall effective_domain
recall is_convex_function
recall subdifferential
recall strongDualSubdifferential
recall subdifferential_nonempty_at_relativeInterior_point
recall convexOn_toReal_of_is_convex_function
recall dualNorm
recall dualNorm_eq_toContinuousLinearMap_norm
recall exists_dualNorm_eq_apply

/-- Helper for Theorem 3.3: the Chapter 1 dual norm of the algebraic-dual view of a strong-dual
vector agrees with its operator norm. -/
lemma dualNorm_coeStrongDual_eq_norm (g : StrongDual ℝ E) :
    dualNorm ((g : Module.Dual ℝ E)) = ‖g‖ := by
  -- The finite-dimensional coercion `StrongDual → Module.Dual` forgets no norm information.
  rw [dualNorm_eq_toContinuousLinearMap_norm]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.3: at effective-domain points where `f` is finite from below, the
owner subgradient inequality can be read in `ℝ`. -/
lemma subgradient_eval_le_toReal_sub
    (f : E → EReal) (x y : E) (h_ne_bot : ∀ z ∈ effective_domain f, f z ≠ ⊥)
    (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    g (y - x) ≤ (f y).toReal - (f x).toReal := by
  have hfx_ne_bot : f x ≠ ⊥ := h_ne_bot x hx
  have hfy_ne_bot : f y ≠ ⊥ := h_ne_bot y hy
  have hfx_ne_top : f x ≠ ⊤ := ne_of_lt hx
  have hfy_ne_top : f y ≠ ⊤ := ne_of_lt hy
  -- Rewrite owner membership to the domain-restricted subgradient inequality and then convert the
  -- resulting `EReal` inequality to an inequality of real numbers.
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hg
  have hsub_ereal : f x + (g (y - x) : EReal) ≤ f y := by
    simpa [ge_iff_le] using hg.2 y hy
  have hsub_ereal' := hsub_ereal
  have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
  have hfy_eq : f y = (((f y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hfy_ne_top hfy_ne_bot).symm
  rw [hfx_eq, hfy_eq] at hsub_ereal'
  have hsub_real' : (f x).toReal + g (y - x) ≤ (f y).toReal :=
    by
      exact_mod_cast hsub_ereal'
  linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.3: a Lipschitz constant on a set bounds the real difference quotient
between any two points of that set. -/
lemma abs_toReal_sub_le_mul_dist_of_lipschitzOnWith
    (f : E → EReal) {s : Set E} {L : NNReal}
    (hLip : LipschitzOnWith L (fun z ↦ (f z).toReal) s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) :
    |(f y).toReal - (f x).toReal| ≤ (L : ℝ) * dist y x := by
  -- This is the metric reformulation of `LipschitzOnWith` for a real-valued codomain.
  simpa [Real.dist_eq] using hLip.dist_le_mul y hy x hx

/-- Helper for Theorem 3.3: a Lipschitz bound on a closed ball around `x` bounds every
strong-dual subgradient at `x` by the same dual-ball radius. -/
lemma mem_closedBall_of_mem_strongDualSubdifferential_of_lipschitzOnWith
    (f : E → EReal) (x : E) (h_ne_bot : ∀ y ∈ effective_domain f, f y ≠ ⊥)
    {r : ℝ} (hr_pos : 0 < r) {L : NNReal}
    (hdom : Metric.closedBall x r ⊆ effective_domain f)
    (hLip : LipschitzOnWith L (fun y ↦ (f y).toReal) (Metric.closedBall x r))
    {g : StrongDual ℝ E} (hg : g ∈ ∂ₛf(x)) :
    g ∈ Metric.closedBall (0 : StrongDual ℝ E) L := by
  let g₀ : Module.Dual ℝ E := (g : Module.Dual ℝ E)
  have hx_ball : x ∈ Metric.closedBall x r := by
    simp [Metric.mem_closedBall, hr_pos.le]
  have hx_dom : x ∈ effective_domain f := hdom hx_ball
  obtain ⟨u, hu_norm, hu_dual⟩ := exists_dualNorm_eq_apply g₀
  let y : E := x + r • u
  have hy_sub : y - x = r • u := by
    simp [y, sub_eq_add_neg, add_assoc]
  have hy_ball : y ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall]
    calc
      dist y x = ‖r • u‖ := by
        simp [y, dist_eq_norm, sub_eq_add_neg, add_assoc]
      _ = |r| * ‖u‖ := norm_smul _ _
      _ ≤ |r| * 1 := by
        gcongr
      _ = r := by
        rw [abs_of_nonneg hr_pos.le, mul_one]
  have hy_dom : y ∈ effective_domain f := hdom hy_ball
  have hg_owner : g₀ ∈ ∂ f(x) := by
    simpa using hg
  have hsub_real :
      g₀ (y - x) ≤ (f y).toReal - (f x).toReal :=
    subgradient_eval_le_toReal_sub f x y h_ne_bot hx_dom hy_dom hg_owner
  have hLip_real :
      |(f y).toReal - (f x).toReal| ≤ (L : ℝ) * r := by
    calc
      |(f y).toReal - (f x).toReal| ≤ (L : ℝ) * dist y x :=
        abs_toReal_sub_le_mul_dist_of_lipschitzOnWith f hLip hx_ball hy_ball
      _ ≤ (L : ℝ) * r := by
        gcongr
        have hy_dist : dist y x ≤ r := by
          simpa [Metric.mem_closedBall] using hy_ball
        exact hy_dist
  have hdual_nonneg : 0 ≤ dualNorm g₀ := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg _
  have hscaled_dual :
      r * dualNorm g₀ ≤ (L : ℝ) * r := by
    calc
      r * dualNorm g₀ = g₀ (y - x) := by
        rw [hy_sub, map_smul, hu_dual, smul_eq_mul]
      _ ≤ (f y).toReal - (f x).toReal := hsub_real
      _ ≤ |(f y).toReal - (f x).toReal| := le_abs_self _
      _ ≤ (L : ℝ) * r := hLip_real
  have hdual_le : dualNorm g₀ ≤ (L : ℝ) := by
    nlinarith [hscaled_dual, hr_pos]
  -- The closed-ball conclusion is exactly the dual-norm bound after rewriting the bridge norm.
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa [dualNorm_coeStrongDual_eq_norm] using hdual_le

-- Proof sketch: this is the finite-dimensional interior specialization of the stronger owner
-- theorem `subdifferential_nonempty_at_relativeInterior_point`, using the canonical inclusion
-- `interior (effective_domain f) ⊆ intrinsicInterior ℝ (effective_domain f)`.
/-- Interior-point existence companion for Theorem 3.3 (1): for a convex extended-real-valued
function, the subdifferential at an
interior point of the effective domain is nonempty. -/
theorem subdifferential_nonempty_at_interior_point
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    (∂ f(x)).Nonempty := by
  -- Convert ordinary interior membership to the relative-interior surface used by Theorem 3.6.
  exact subdifferential_nonempty_at_relativeInterior_point f x hconvex
    (interior_subset_intrinsicInterior hx)

-- Proof sketch: use local Lipschitz continuity on a closed ball centered at `x` and contained in
-- `effective_domain f`. For any `g ∈ ∂ f(x)`, evaluate the subgradient inequality at a point of
-- the form `x + εu`, where `u` is a unit vector realizing the dual norm of `g`, to obtain a
-- uniform norm bound `‖g‖ ≤ L`; hence `∂ f(x)` is contained in a closed ball of the dual space.
/-- Theorem 3.3 (2): for a convex extended-real-valued function that never takes the value `⊥` on
its effective domain, the continuous-dual view of the subdifferential at an interior point of the
effective domain is bounded in the dual norm. -/
theorem subdifferential_bounded_at_interior_point
    (f : E → EReal) (x : E) (h_ne_bot : ∀ y ∈ effective_domain f, f y ≠ ⊥)
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    IsBounded (∂ₛ f(x)) := by
  obtain ⟨r, hr_pos, L, hclosed_subset, hLip⟩ :=
    exists_closedBall_lipschitzOnWith_toReal_of_mem_interior f x hconvex h_ne_bot hx
  have hdom : Metric.closedBall x r ⊆ effective_domain f := by
    intro y hy
    exact interior_subset (hclosed_subset hy)
  have hsubset : ∂ₛ f(x) ⊆ Metric.closedBall (0 : StrongDual ℝ E) L := by
    intro g hg
    -- Apply the quantitative helper to each strong-dual subgradient on the chosen closed ball.
    exact
      mem_closedBall_of_mem_strongDualSubdifferential_of_lipschitzOnWith
        f x h_ne_bot hr_pos hdom hLip hg
  exact Metric.isBounded_closedBall.subset hsubset

/-- Bridge companion: the strong-dual subdifferential at an interior point lies in some closed
dual ball. -/
theorem strongDualSubdifferential_subset_closedBall_at_interior_point
    (f : E → EReal) (x : E) (h_ne_bot : ∀ y ∈ effective_domain f, f y ≠ ⊥)
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    ∃ R : ℝ, ∂ₛ f(x) ⊆ Metric.closedBall (0 : StrongDual ℝ E) R :=
  (subdifferential_bounded_at_interior_point f x h_ne_bot hconvex hx).subset_closedBall
    (0 : StrongDual ℝ E)

end
