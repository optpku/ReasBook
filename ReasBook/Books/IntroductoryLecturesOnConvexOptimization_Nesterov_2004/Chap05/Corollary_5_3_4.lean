/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_9

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/-
Corollary 5.3.4 lies in the Chapter 5 self-concordant-barrier / analytic-center / dual-local-norm
domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsMinOn` in `Definition_5_3_3`, the canonical analytic-center owner;
* `IsSelfConcordantBarrierOnWith.subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn`
  in `Theorem_5_3_9`, the owner-level analytic-center inclusion theorem upstream in the same
  chapter;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for domain-level
  Hessian nondegeneracy;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical bridge from
  `HasPositiveDefiniteHessianOn` to the Chapter 5 Hessian-metric dual local norm.

Best owner abstraction:
* source-facing: the analytic-center Hessian and dual-local-norm comparison bounds;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`, which derives the local Hessian data needed to
  evaluate the dual norm from the positive-definite-Hessian owner.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* the analytic-center witness `hcenter : IsMinOn F dom (xStar : E)`;
* for the dual-norm comparison only, the domain-level positive-definite-Hessian owner
  `HasPositiveDefiniteHessianOn dom F`.

Derived API:
* the Loewner lower bound comparing `hessian F x` to the Hessian at the analytic center;
* the corresponding comparison of Hessian dual local norms, stated through the canonical
  domain-level bridge `HessianDualLocalNorm.ofPosDefMem`.

Source/core/bridge triage:
* source-facing: the textbook analytic-center comparison corollaries;
* core/canonical: the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `HessianDualLocalNorm.ofPosDefMem`.

These corollaries carry genuine source-facing content, so they should remain theorem-shaped rather
than a pure recall. Their public surface is nevertheless barrier-owner based: the surrounding
Chapter 5 API already organizes barrier consequences under `IsSelfConcordantBarrierOnWith`, and
the dual-norm comparison should use the domain-level dual-norm bridge instead of exposing raw
determinant witnesses in the public statement. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Corollary 5.3.4: the unit open Dikin ellipsoid centered at `x` is contained in the
radius-`ν + 2 √ν` Dikin ellipsoid centered at an analytic center `xStar`. -/
theorem unit_openDikinEllipsoid_subset_analytic_center_dikin
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) :
    W⁰[F; (x : E)](1) ⊆ W[F; (xStar : E)]((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
  let hstd : IsStandardSelfConcordantOn dom F := hF.toIsStandardSelfConcordantOn
  -- The unit Dikin ball at `x` stays in the domain, and the whole domain already lies in the
  -- analytic-center Dikin ellipsoid from Theorem 5.3.9.
  exact Set.Subset.trans
    (by
      intro y hy
      simpa using
        IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
          (domain := dom) (Mf := (1 : NNRealˣ)) (f := F) hstd x.2 hy)
    (hF.subset_dikinEllipsoid_barrierParameter_add_two_sqrt_of_isMinOn xStar hcenter)

/-- Helper for Corollary 5.3.4: at a domain point of a self-concordant barrier, the Hessian local
norm is homogeneous for nonnegative scalar dilations. -/
theorem hessianLocalNorm_smul_nonneg_of_mem
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (x : dom) {a : ℝ} (ha : 0 ≤ a) (u : E) :
    ‖a • u‖[F; (x : E)] = a * ‖u‖[F; (x : E)] := by
  have hquad : 0 ≤ inner ℝ u (hessian F (x : E) u) :=
    (hF.toIsStandardSelfConcordantOn.hessian_isPositive x.2).inner_nonneg_right u
  -- Rewrite both sides to square roots of the same scaled quadratic form.
  calc
    ‖a • u‖[F; (x : E)] =
        Real.sqrt ((a * a) * inner ℝ u (hessian F (x : E) u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, mul_assoc,
        mul_left_comm, mul_comm]
    _ =
        Real.sqrt (a * a) * Real.sqrt (inner ℝ u (hessian F (x : E) u)) := by
      rw [Real.sqrt_mul (mul_nonneg ha ha)]
    _ = a * ‖u‖[F; (x : E)] := by
      rw [Real.sqrt_mul_self ha, hessianLocalNorm_def]

/-- Helper for Corollary 5.3.4: every unit `x`-local direction has analytic-center local norm at
most `ν + 2 √ν`. -/
theorem hessianLocalNorm_at_analytic_center_le_radius_of_lt_one
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) {u : E}
    (hu : ‖u‖[F; (x : E)] < 1) :
    ‖u‖[F; (xStar : E)] ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
  let R : ℝ := (ν : ℝ) + 2 * Real.sqrt (ν : ℝ)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hsubset :=
    hF.unit_openDikinEllipsoid_subset_analytic_center_dikin xStar hcenter x
  have hx_plus_mem : (x : E) + u ∈ W[F; (xStar : E)](R) := by
    have hx_plus_open : (x : E) + u ∈ W⁰[F; (x : E)](1) := by
      rw [mem_openDikinEllipsoid_iff]
      simpa using hu
    exact hsubset hx_plus_open
  have hx_minus_mem : (x : E) - u ∈ W[F; (xStar : E)](R) := by
    have hx_minus_open : (x : E) - u ∈ W⁰[F; (x : E)](1) := by
      rw [mem_openDikinEllipsoid_iff]
      simpa [sub_eq_add_neg] using (show ‖-u‖[F; (x : E)] < 1 by simpa using hu)
    exact hsubset hx_minus_open
  have hPosStar : (hessian F (xStar : E)).IsPositive :=
    hF.toIsStandardSelfConcordantOn.hessian_isPositive xStar.2
  let a : E := (x : E) - (xStar : E)
  let H := hessian F (xStar : E)
  have hplus_sq :
      inner ℝ ((x : E) + u - (xStar : E)) (H (((x : E) + u) - (xStar : E))) ≤ R ^ (2 : ℕ) := by
    exact (mem_dikinEllipsoid_iff_hessian_quadratic_le_sq F (xStar : E) ((x : E) + u) hR_nonneg).1
      hx_plus_mem
  have hminus_sq :
      inner ℝ ((x : E) - u - (xStar : E)) (H (((x : E) - u) - (xStar : E))) ≤ R ^ (2 : ℕ) := by
    exact (mem_dikinEllipsoid_iff_hessian_quadratic_le_sq F (xStar : E) ((x : E) - u) hR_nonneg).1
      hx_minus_mem
  have hcross :
      inner ℝ a (H u) = inner ℝ u (H a) := by
    simpa [a, H, real_inner_comm] using (hPosStar.isSymmetric a u).symm
  have hplus_expand :
      inner ℝ (a + u) (H (a + u)) =
        inner ℝ a (H a) + inner ℝ a (H u) + inner ℝ u (H a) + inner ℝ u (H u) := by
    -- Expand the quadratic form on `a + u` into diagonal and mixed terms.
    rw [map_add, inner_add_left, inner_add_right, inner_add_right]
    ring_nf
  have hminus_expand :
      inner ℝ (a - u) (H (a - u)) =
        inner ℝ a (H a) - inner ℝ a (H u) - inner ℝ u (H a) + inner ℝ u (H u) := by
    -- Expand the quadratic form on `a - u` with the expected sign changes.
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
    ring_nf
  have hsum_core :
      inner ℝ (a + u) (H (a + u)) + inner ℝ (a - u) (H (a - u)) =
        2 * inner ℝ a (H a) + 2 * inner ℝ u (H u) := by
    -- The mixed terms cancel after rewriting both expansions with Hessian symmetry.
    rw [hplus_expand, hminus_expand, hcross]
    ring_nf
  have hsum :
      inner ℝ ((x : E) + u - (xStar : E)) (H (((x : E) + u) - (xStar : E))) +
          inner ℝ ((x : E) - u - (xStar : E)) (H (((x : E) - u) - (xStar : E))) =
        2 * inner ℝ a (H a) + 2 * inner ℝ u (H u) := by
    simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum_core
  have ha_nonneg : 0 ≤ inner ℝ a (H a) := hPosStar.inner_nonneg_right a
  have hu_quad :
      inner ℝ u (H u) ≤ R ^ (2 : ℕ) := by
    nlinarith [hplus_sq, hminus_sq, hsum, ha_nonneg]
  have hu_mem : (xStar : E) + u ∈ W[F; (xStar : E)](R) := by
    -- The previous quadratic estimate is exactly the analytic-center Dikin-ball condition for `u`.
    refine (mem_dikinEllipsoid_iff_hessian_quadratic_le_sq F (xStar : E) ((xStar : E) + u)
      hR_nonneg).2 ?_
    simpa using hu_quad
  simpa [mem_dikinEllipsoid_iff] using hu_mem

/-- Helper for Corollary 5.3.4: every direction has analytic-center local norm bounded by
`(ν + 2 √ν)` times its local norm at `x`. -/
theorem hessianLocalNorm_at_analytic_center_le_radius_mul
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) (u : E) :
    ‖u‖[F; (xStar : E)] ≤
      ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * ‖u‖[F; (x : E)] := by
  let R : ℝ := (ν : ℝ) + 2 * Real.sqrt (ν : ℝ)
  let a : ℝ := ‖u‖[F; (x : E)]
  let b : ℝ := ‖u‖[F; (xStar : E)]
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact hessianLocalNorm_nonneg F (x : E) u
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact hessianLocalNorm_nonneg F (xStar : E) u
  by_cases ha_zero : a = 0
  · by_cases hb_zero : b = 0
    · simp [a, b, ha_zero, hb_zero]
    · have hb_pos : 0 < b := lt_of_le_of_ne hb_nonneg (by simpa [eq_comm] using hb_zero)
      let t : ℝ := (R + 1) / b
      have ht_nonneg : 0 ≤ t := by
        dsimp [t]
        positivity
      have ht_local_eq : ‖t • u‖[F; (x : E)] = t * a := by
        -- Rewrite the scaled `x`-local norm using nonnegative homogeneity.
        simpa [a] using hF.hessianLocalNorm_smul_nonneg_of_mem x ht_nonneg u
      have ht_unit : ‖t • u‖[F; (x : E)] < 1 := by
        rw [ht_local_eq, ha_zero]
        simp [t]
      have hscaled :=
        hF.hessianLocalNorm_at_analytic_center_le_radius_of_lt_one xStar hcenter x ht_unit
      have hb_scaled :
          ‖t • u‖[F; (xStar : E)] = t * b := by
        -- Rewrite the scaled analytic-center local norm in the same scalar form.
        simpa [b] using hF.hessianLocalNorm_smul_nonneg_of_mem xStar ht_nonneg u
      have ht_mul_b : t * b = R + 1 := by
        dsimp [t]
        field_simp [hb_zero]
      rw [hb_scaled, ht_mul_b] at hscaled
      linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by simpa [eq_comm] using ha_zero)
    by_contra hfail
    have hstrict : R * a < b := lt_of_not_ge hfail
    have hb_pos : 0 < b := lt_of_le_of_lt (mul_nonneg hR_nonneg ha_nonneg) hstrict
    let t : ℝ := (R / b + 1 / a) / 2
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      positivity
    have hleft : R / b < 1 / a := by
      -- Route correction: clear denominators once, then reuse this midpoint inequality twice.
      field_simp [ha_pos.ne', hb_pos.ne']
      nlinarith [hstrict]
    have ht_lt_inv_a : t < 1 / a := by
      dsimp [t]
      nlinarith
    have ht_mul_a_lt_one : t * a < 1 := by
      have hmul := mul_lt_mul_of_pos_right ht_lt_inv_a ha_pos
      simpa [div_eq_mul_inv, ha_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hR_div_b_lt_t : R / b < t := by
      dsimp [t]
      nlinarith
    have hR_lt_ht_mul_b : R < t * b := by
      have hmul := mul_lt_mul_of_pos_right hR_div_b_lt_t hb_pos
      simpa [div_eq_mul_inv, hb_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    have ht_local_eq : ‖t • u‖[F; (x : E)] = t * a := by
      -- Rewrite the scaled `x`-local norm before comparing it to the unit radius.
      simpa [a] using hF.hessianLocalNorm_smul_nonneg_of_mem x ht_nonneg u
    have ht_unit : ‖t • u‖[F; (x : E)] < 1 := by
      rw [ht_local_eq]
      simpa using ht_mul_a_lt_one
    have hscaled :=
      hF.hessianLocalNorm_at_analytic_center_le_radius_of_lt_one xStar hcenter x ht_unit
    have hb_scaled :
        ‖t • u‖[F; (xStar : E)] = t * b := by
      -- Rewrite the scaled analytic-center local norm before comparing to the radius `R`.
      simpa [b] using hF.hessianLocalNorm_smul_nonneg_of_mem xStar ht_nonneg u
    rw [hb_scaled] at hscaled
    linarith

-- Proof sketch: for a chosen analytic center `xStar`, Theorem 5.3.9 bounds the
-- `xStar`-local distance of every `x ∈ dom`, and Theorem 5.1.5 then turns the inclusion of the
-- unit Dikin ball at `x` into the larger Dikin ball at `xStar` of radius `ν + 2 √ν`. Rewriting
-- that ellipsoid inclusion in Loewner order gives the displayed Hessian comparison.
/-- Corollary 5.3.4: if `xStar` is an analytic center of a `ν`-self-concordant barrier on `dom`,
then for every `x ∈ dom` the Hessian at `x` dominates the Hessian at `xStar` in Loewner order by
the factor `(ν + 2 √ν)⁻²`. -/
theorem hessian_loewner_lower_bound_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom) :
    (1 / (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ^ (2 : ℕ))) •
        hessian F (xStar : E) ≤
      hessian F x := by
  let R : ℝ := (ν : ℝ) + 2 * Real.sqrt (ν : ℝ)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hPosX : (hessian F (x : E)).IsPositive :=
    hF.toIsStandardSelfConcordantOn.hessian_isPositive x.2
  have hPosStar : (hessian F (xStar : E)).IsPositive :=
    hF.toIsStandardSelfConcordantOn.hessian_isPositive xStar.2
  by_cases hR_zero : R = 0
  · -- When `R = 0`, the left-hand side is the zero operator, so positivity of `∇²F(x)` closes
    -- the Loewner bound immediately.
    simpa [R, hR_zero] using
      (ContinuousLinearMap.nonneg_iff_isPositive (hessian F (x : E))).2 hPosX
  · have hR_sq_pos : 0 < R ^ (2 : ℕ) := by
      have hR_pos : 0 < R := lt_of_le_of_ne hR_nonneg (by simpa [eq_comm] using hR_zero)
      positivity
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · -- Both Hessians are symmetric because barrier self-concordance gives pointwise positivity.
      intro u v
      have hxSymm : inner ℝ (hessian F (x : E) u) v = inner ℝ u (hessian F (x : E) v) := by
        simpa using hPosX.isSymmetric u v
      have hstarSymm :
          inner ℝ (hessian F (xStar : E) u) v = inner ℝ u (hessian F (xStar : E) v) := by
        simpa using hPosStar.isSymmetric u v
      calc
        inner ℝ (((hessian F (x : E)) - (1 / (R ^ (2 : ℕ))) • hessian F (xStar : E)) u) v =
            inner ℝ (hessian F (x : E) u) v -
              (1 / (R ^ (2 : ℕ))) * inner ℝ (hessian F (xStar : E) u) v := by
          simp [inner_sub_left, inner_smul_left]
        _ =
            inner ℝ u (hessian F (x : E) v) -
              (1 / (R ^ (2 : ℕ))) * inner ℝ u (hessian F (xStar : E) v) := by
          rw [hxSymm, hstarSymm]
        _ =
            inner ℝ u
              (((hessian F (x : E)) - (1 / (R ^ (2 : ℕ))) • hessian F (xStar : E)) v) := by
          simp [inner_sub_right, inner_smul_right]
    · intro u
      have hcmp :=
        hF.hessianLocalNorm_at_analytic_center_le_radius_mul xStar hcenter x u
      have hquad_x :
          0 ≤ inner ℝ u (hessian F (x : E) u) := hPosX.inner_nonneg_right u
      have hquad_star :
          0 ≤ inner ℝ u (hessian F (xStar : E) u) := hPosStar.inner_nonneg_right u
      have hxSymm : inner ℝ (hessian F (x : E) u) u = inner ℝ u (hessian F (x : E) u) := by
        simpa using hPosX.isSymmetric u u
      have hstarSymm :
          inner ℝ (hessian F (xStar : E) u) u = inner ℝ u (hessian F (xStar : E) u) := by
        simpa using hPosStar.isSymmetric u u
      have hsq :
          inner ℝ u (hessian F (xStar : E) u) ≤
            R ^ (2 : ℕ) * inner ℝ u (hessian F (x : E) u) := by
        rw [hessianLocalNorm_def, hessianLocalNorm_def] at hcmp
        have hcmp_nonneg :
            0 ≤ R * Real.sqrt (inner ℝ u (hessian F (x : E) u)) := by
          exact mul_nonneg hR_nonneg (Real.sqrt_nonneg _)
        have hsq' :
            (Real.sqrt (inner ℝ u (hessian F (xStar : E) u))) ^ (2 : ℕ) ≤
              (R * Real.sqrt (inner ℝ u (hessian F (x : E) u))) ^ (2 : ℕ) := by
          exact (sq_le_sq₀ (Real.sqrt_nonneg _) hcmp_nonneg).2 hcmp
        nlinarith [hsq', Real.sq_sqrt hquad_star, Real.sq_sqrt hquad_x]
      have hscaled :
          inner ℝ u (hessian F (xStar : E) u) / (R ^ (2 : ℕ)) ≤
            inner ℝ u (hessian F (x : E) u) := by
        exact (div_le_iff₀ hR_sq_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsq)
      have hscaled' :
          (1 / (R ^ (2 : ℕ))) * inner ℝ (hessian F (xStar : E) u) u ≤
            inner ℝ (hessian F (x : E) u) u := by
        simpa [div_eq_mul_inv, real_inner_comm, mul_assoc, mul_left_comm, mul_comm, hxSymm,
          hstarSymm] using hscaled
      have hrewrite :
          inner ℝ (((hessian F (x : E)) - (1 / (R ^ (2 : ℕ))) • hessian F (xStar : E)) u) u =
            inner ℝ (hessian F (x : E) u) u -
              (1 / (R ^ (2 : ℕ))) * inner ℝ (hessian F (xStar : E) u) u := by
        simp [inner_sub_left, inner_smul_left]
      -- Recast the gap operator on `u` as the scalar inequality already proved.
      have hgap_nonneg :
          0 ≤ inner ℝ (hessian F (x : E) u) u -
            (1 / (R ^ (2 : ℕ))) * inner ℝ (hessian F (xStar : E) u) u := by
        linarith [hscaled']
      rw [hrewrite]
      simpa [R] using hgap_nonneg

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Corollary 5.3.4: a quadratic family bounded above by `c` forces the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Route correction: follow the stable discriminant proof already used for Theorem 5.2.2.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have htest := hline ((|c| + 1) / a)
      have hcontr : 2 * (|c| + 1) ≤ c := by
        have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
          simpa [hb_zero] using htest
        field_simp [ha_zero] at hrew
        linarith
      nlinarith [hcontr, le_abs_self c, abs_nonneg c]
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Corollary 5.3.4: the Euclidean pairing is bounded by the Hessian dual local norm
times the Hessian local norm at a domain point. -/
theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
    {dom : Set E} {F : E → ℝ} [HasPositiveDefiniteHessianOn dom F]
    (y : dom) (v z : E) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v) * ‖z‖[F; (y : E)] := by
  let H := hessian F (y : E)
  let w := H.inverse v
  have hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem y.2
  have hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem y.2)
  have hHw : H w = v := by
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    -- The inverse-Hessian pairing is a positive quadratic form at `w`.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      -- Expand the quadratic form and rewrite the mixed terms using `H w = v`.
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    have hsq :=
      sq_le_mul_of_quadratic_family (a := inner ℝ v z) (b := inner ℝ z (H z))
        (c := inner ℝ v w) hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[F; (y : E)] ^ (2 : ℕ) = inner ℝ z (H z) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v) * ‖z‖[F; (y : E)]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[F; (y : E)] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v) * ‖z‖[F; (y : E)]) ^ (2 : ℕ) := by
        ring
  have hdual_nonneg : 0 ≤ HessianDualLocalNorm.ofPosDefMem F y.2 (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg F (y : E) z))

-- Proof sketch: use the support-function representation of the dual local norm as the supremum
-- of the pairing over the corresponding Dikin ellipsoid. The Loewner comparison from
-- `IsSelfConcordantBarrierOnWith.hessian_loewner_lower_bound_of_isMinOn` is equivalent to
-- inclusion of these ellipsoids,
-- which yields the stated comparison of inverse-Hessian dual norms after identifying vectors with
-- covectors through the Riesz map.
/-- The dual local norm of the covector corresponding to `v` at any point of a self-concordant
barrier domain is controlled by the corresponding dual local norm at an analytic center with
factor `ν + 2 √ν`. -/
theorem dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [HasPositiveDefiniteHessianOn dom F]
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (xStar : dom) (hcenter : IsMinOn F dom (xStar : E))
    (x : dom)
    (v : E) :
    HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) ≤
      ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
        HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) := by
  let R : ℝ := (ν : ℝ) + 2 * Real.sqrt (ν : ℝ)
  let Hx := hessian F (x : E)
  let w := Hx.inverse v
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hInvX : Hx.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem x.2)
  have hHxw : Hx w = v := by
    dsimp [w, Hx]
    exact hInvX.self_apply_inverse v
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    have hPosX : Hx.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem x.2
    calc
      0 ≤ inner ℝ w (Hx w) := hPosX.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHxw, real_inner_comm]
  have hw_local_eq :
      ‖w‖[F; (x : E)] =
        HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) := by
    -- Route correction: compare the two square-root radicands explicitly via `H_x w = v`.
    rw [hessianLocalNorm_def, HessianDualLocalNorm.ofPosDefMem_def]
    have hinner : inner ℝ w (Hx w) = inner ℝ v w := by
      rw [hHxw, real_inner_comm]
    simpa [w, Hx, InnerProductSpace.toDual_apply_apply] using congrArg Real.sqrt hinner
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, Hx, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hpair_bound :
      |inner ℝ v w| ≤
        HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) * ‖w‖[F; (xStar : E)] :=
    abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm (F := F) xStar v w
  have hw_star_le :
      ‖w‖[F; (xStar : E)] ≤ R * ‖w‖[F; (x : E)] :=
    hF.hessianLocalNorm_at_analytic_center_le_radius_mul xStar hcenter x w
  have hdual_star_nonneg :
      0 ≤ HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  have hmain :
      (HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v)) ^ (2 : ℕ) ≤
        R * HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) *
          HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) := by
    -- First compare `|⟪v, w⟫|` by the analytic-center dual norm, then rewrite `‖w‖_x`.
    have hpair_step :
        inner ℝ v w ≤
          HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) * ‖w‖[F; (xStar : E)] := by
      simpa [abs_of_nonneg hpair_nonneg] using hpair_bound
    have hpair_step' :
        inner ℝ v w ≤
          HessianDualLocalNorm.ofPosDefMem F xStar.2 (toDual ℝ E v) *
            (R * ‖w‖[F; (x : E)]) := by
      exact le_trans hpair_step <| by
        gcongr
    rw [hw_local_eq] at hpair_step'
    rw [hdual_sq]
    ring_nf
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpair_step'
  by_cases hzero :
      HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) = 0
  · rw [hzero]
    exact mul_nonneg hR_nonneg hdual_star_nonneg
  · have hpos :
        0 < HessianDualLocalNorm.ofPosDefMem F x.2 (toDual ℝ E v) :=
      lt_of_le_of_ne (by
        rw [HessianDualLocalNorm.ofPosDefMem_def]
        exact Real.sqrt_nonneg _) (by simpa [eq_comm] using hzero)
    nlinarith [hmain, hpos, hR_nonneg, hdual_star_nonneg]

end

end IsSelfConcordantBarrierOnWith

end
