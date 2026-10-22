/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped Gradient HessianDualLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Lemma 7.13 lies in the Chapter 7 barrier-subgradient / self-concordant local-dual-norm domain.

Mandatory domain-style sampling before refinement:
- `IsSelfConcordantBarrierOnWith (interior Q) ν F` in `Chap05/Definition_5_3_2`, the Chapter 5
  owner for the barrier structure on the intrinsic strict feasible region;
- `dualLocalNorm` together with the determinant bridge `HessianDualLocalNorm.ofDetNeZero` in
  `Chap05/Definition_5_0_20`, the owner of the Hessian dual local norm and its determinant-based
  source-facing bridge;
- `IsSelfConcordantOnWith.hessian_isPositive` in `Chap05/Definition_5_1_1`, inherited from the
  barrier owner and supplying the local Hessian positivity needed by `dualLocalNorm`;
- mathlib `ConcaveOn`, the canonical owner for the concavity hypothesis on `interior Q`.

Best owner abstraction:
- source-facing: the dual-local-norm bound on `∇ ψ x` for a positive concave function on
  `interior Q`;
- core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`, `ConcaveOn`, and
  `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`;
- bridge/view: the supporting-nesterovHyperplane inequality for `ψ` along the inverse-Hessian direction.

Primitive data:
- the barrier owner on `interior Q`;
- the point `x ∈ interior Q`;
- the gradient witness for `ψ` at `x`;
- concavity and positivity of `ψ` on `interior Q`;
- Hessian nondegeneracy at `x`.

Derived API:
- local Hessian positivity at `x`, derived from the barrier owner;
- the dual local norm of the gradient covector, expressed through the Chapter 5 determinant
  bridge.

The previous statement kept both Hessian positivity and Hessian nondegeneracy as primitive public
inputs, even though positivity is already derived canonically from the barrier owner. This
refinement keeps the source-facing theorem, but moves it onto the chapter owner surface on
`interior Q` and leaves only the genuinely independent nondegeneracy witness explicit.
-/

-- Proof sketch: move from `x` in the inverse-Hessian direction of `∇ ψ x` by any local-norm
-- radius `r < 1`, use the self-concordant barrier inclusion to stay inside `interior Q`, apply
-- positivity of `ψ` at the new point, and then use the supporting-nesterovHyperplane inequality from
-- concavity together with the explicit choice of direction. Letting `r ↑ 1` yields the bound.
/-- Helper for Lemma 7.13: concavity on `interior Q` bounds `ψ` above by its tangent plane at an
interior base point with an ambient gradient witness. -/
private lemma concaveOn_le_tangent_of_hasGradientAt
    {Q : Set E} {ψ : E → ℝ} {x y : E}
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hx : x ∈ interior Q) (hy : y ∈ interior Q)
    (hgrad : HasGradientAt ψ (∇ ψ x) x) :
    ψ y ≤ ψ x + inner ℝ (∇ ψ x) (y - x) := by
  -- Negating the concave function turns the claim into the standard convex lower-tangent bound.
  have hgradNeg : HasGradientAt (-ψ) (-∇ ψ x) x := by
    rw [hasGradientAt_iff_hasFDerivAt] at hgrad ⊢
    simpa using hgrad.neg
  have hnegWithin :
      HasGradientWithinAt (-ψ) (-∇ ψ x) (interior Q) x := by
    simpa [InnerProductSpace.toDual_symm_apply] using
      hgradNeg.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  have hsupport :
      -ψ y ≥ -ψ x + inner ℝ (-∇ ψ x) (y - x) := by
    simpa using
      (hψ_concave.neg).lower_tangent_plane_of_hasGradientWithinAt
        x hx (-∇ ψ x) hnegWithin y hy
  have hsupport' :
      -ψ y ≥ -ψ x - inner ℝ (∇ ψ x) (y - x) := by
    simpa using hsupport
  linarith

/-- Helper for Lemma 7.13: the inverse-Hessian pairing of `∇ ψ x` with itself is the square of
the local dual norm from the Chapter 5 determinant bridge. -/
private lemma gradient_inverse_hessian_pairing_eq_dualLocalNorm_sq
    {F ψ : E → ℝ} {x : E}
    (hPos : (hessian F x).IsPositive) (hH : (hessian F x).det ≠ 0) :
    let δ := HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x))
    inner ℝ (∇ ψ x) ((hessian F x).inverse (∇ ψ x)) = δ ^ (2 : ℕ) := by
  dsimp
  let v := (hessian F x).inverse (∇ ψ x)
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hquad : 0 ≤ inner ℝ v (hessian F x v) := hPos.inner_nonneg_right v
  have hHv : hessian F x v = ∇ ψ x := hInv.self_apply_inverse (∇ ψ x)
  have hpair_nonneg :
      0 ≤ inner ℝ (∇ ψ x) ((hessian F x).inverse (∇ ψ x)) := by
    -- Rewrite the positive Hessian quadratic form of the inverse-Hessian direction.
    calc
      0 ≤ inner ℝ v (hessian F x v) := hquad
      _ = inner ℝ (∇ ψ x) v := by rw [hHv, real_inner_comm]
      _ = inner ℝ (∇ ψ x) ((hessian F x).inverse (∇ ψ x)) := by
            rfl
  rw [HessianDualLocalNorm.ofDetNeZero_def]
  simpa [pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
    (Real.sq_sqrt hpair_nonneg).symm

/-- Helper for Lemma 7.13: any inverse-Hessian gradient step of local radius `r < 1` stays in
`interior Q`. -/
private lemma inverse_hessian_step_mem_interior
    {Q : Set E} {ν : NNReal} {F ψ : E → ℝ} {x : E}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hx : x ∈ interior Q)
    (hH : (hessian F x).det ≠ 0)
    {δ r : ℝ}
    (hδ_def :
      δ = HessianDualLocalNorm.ofDetNeZero F x
        (hF.toIsStandardSelfConcordantOn.hessian_isPositive hx) hH ((toDual ℝ E) (∇ ψ x)))
    (hδ_pos : 0 < δ)
    (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    let v := (hessian F x).inverse (∇ ψ x)
    let y := x - (r / δ) • v
    y ∈ interior Q := by
  let hPos : (hessian F x).IsPositive := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
  let v : E := (hessian F x).inverse (∇ ψ x)
  let y : E := x - (r / δ) • v
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hHv : hessian F x v = ∇ ψ x := hInv.self_apply_inverse (∇ ψ x)
  have hv_quad :
      inner ℝ v (hessian F x v) = δ ^ (2 : ℕ) := by
    -- The quadratic form of the inverse-Hessian gradient direction is exactly `δ²`.
    calc
      inner ℝ v (hessian F x v) = inner ℝ (∇ ψ x) v := by rw [hHv, real_inner_comm]
      _ = inner ℝ (∇ ψ x) ((hessian F x).inverse (∇ ψ x)) := by
            rfl
      _ = δ ^ (2 : ℕ) := by
            rw [hδ_def]
            exact gradient_inverse_hessian_pairing_eq_dualLocalNorm_sq hPos hH
  have hy_quad_nonneg :
      0 ≤ inner ℝ (y - x) (hessian F x (y - x)) := by
    -- Hessian positivity gives the quadratic-form nonnegativity required by the Dikin bridge.
    exact hPos.inner_nonneg_right (y - x)
  have hy_memW :
      y ∈ W⁰[F; x](1) := by
    refine
      (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq F x y hy_quad_nonneg
        (by norm_num : 0 ≤ (1 : ℝ))).2 ?_
    have hy_quad :
        inner ℝ (y - x) (hessian F x (y - x)) = r ^ (2 : ℕ) := by
      calc
        inner ℝ (y - x) (hessian F x (y - x))
            = (r / δ) ^ (2 : ℕ) * inner ℝ v (hessian F x v) := by
              simp [y, v, pow_two, inner_smul_left, inner_smul_right, mul_assoc]
        _ = (r / δ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by rw [hv_quad]
        _ = r ^ (2 : ℕ) := by
              field_simp [pow_two, hδ_ne]
    rw [hy_quad]
    nlinarith
  have hy_memW_inv :
      y ∈ W⁰[F; x](1 / (1 : ℝ)) := by
    simpa using hy_memW
  -- Standard self-concordance puts the unit Dikin ellipsoid inside the interior domain.
  exact hF.toIsStandardSelfConcordantOn.openDikinEllipsoid_inv_constant_subset hx hy_memW_inv

/-- Helper for Lemma 7.13: evaluating `ψ` on a feasible inverse-Hessian gradient step yields the
family of inequalities `r * δ ≤ ψ x` for every `0 < r < 1`. -/
private lemma scaled_dual_step_le_value
    {Q : Set E} {ν : NNReal} {F ψ : E → ℝ} {x : E}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hx : x ∈ interior Q)
    (hgrad : HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ ⦃y : E⦄, y ∈ interior Q → 0 < ψ y)
    (hH : (hessian F x).det ≠ 0)
    {δ r : ℝ}
    (hδ_def :
      δ = HessianDualLocalNorm.ofDetNeZero F x
        (hF.toIsStandardSelfConcordantOn.hessian_isPositive hx) hH ((toDual ℝ E) (∇ ψ x)))
    (hδ_pos : 0 < δ)
    (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    r * δ ≤ ψ x := by
  let hPos : (hessian F x).IsPositive := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
  let v : E := (hessian F x).inverse (∇ ψ x)
  let y : E := x - (r / δ) • v
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hy : y ∈ interior Q :=
    inverse_hessian_step_mem_interior hF hx hH hδ_def hδ_pos hr_pos hr_lt_one
  have hsupport :
      ψ y ≤ ψ x + inner ℝ (∇ ψ x) (y - x) :=
    concaveOn_le_tangent_of_hasGradientAt hψ_concave hx hy hgrad
  have hinner_eq :
      inner ℝ (∇ ψ x) (y - x) = -(r * δ) := by
    -- The chosen direction was scaled so the tangent-plane drop is exactly `r * δ`.
    calc
      inner ℝ (∇ ψ x) (y - x)
          = -(r / δ) * inner ℝ (∇ ψ x) v := by
              simp [y, v, real_inner_smul_right]
      _ = -(r / δ) * δ ^ (2 : ℕ) := by
            rw [show inner ℝ (∇ ψ x) v = δ ^ (2 : ℕ) by
              rw [hδ_def]
              exact gradient_inverse_hessian_pairing_eq_dualLocalNorm_sq hPos hH]
      _ = -(r * δ) := by
            field_simp [pow_two, hδ_ne]
  have hy_pos : 0 < ψ y := hψ_pos hy
  have hupper : ψ y ≤ ψ x - r * δ := by
    calc
      ψ y ≤ ψ x + inner ℝ (∇ ψ x) (y - x) := hsupport
      _ = ψ x - r * δ := by rw [hinner_eq]; ring
  linarith

/-- Lemma 7.13: if `F` is a `ν`-self-concordant barrier on `interior Q` and `ψ` is a positive
concave function there, then at every interior point `x` where `ψ` has gradient `∇ ψ x`, the
dual local norm of that gradient with respect to the barrier Hessian of `F` is bounded by the
value `ψ x`. -/
theorem dualLocalNorm_gradient_le_value_of_concaveOn_pos
    {Q : Set E} {ν : NNReal} {F ψ : E → ℝ} {x : E}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hx : x ∈ interior Q)
    (hgrad : HasGradientAt ψ (∇ ψ x) x)
    (hψ_concave : ConcaveOn ℝ (interior Q) ψ)
    (hψ_pos : ∀ ⦃y : E⦄, y ∈ interior Q → 0 < ψ y)
    (hH : (hessian F x).det ≠ 0) :
    let hPos := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
    HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x)) ≤ ψ x := by
  let hPos : (hessian F x).IsPositive := hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
  let δ :=
    HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x))
  change δ ≤ ψ x
  -- First record that the dual local norm is nonnegative, then split into the trivial and
  -- nontrivial branches according to whether `δ` vanishes.
  have hδ_nonneg : 0 ≤ δ := by
    rw [show δ =
      HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x)) by rfl]
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  by_cases hδ_zero : δ = 0
  · -- When the dual norm vanishes, positivity of `ψ x` immediately gives the desired bound.
    have hx_pos : 0 < ψ x := hψ_pos hx
    simpa [hδ_zero] using hx_pos.le
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    by_contra hnot
    have hψ_lt_δ : ψ x < δ := lt_of_not_ge hnot
    let r : ℝ := (ψ x + δ) / (2 * δ)
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
    have hr_pos : 0 < r := by
      -- The midpoint ratio is positive because both `ψ x` and `δ` are positive.
      dsimp [r]
      have hψ_pos_x : 0 < ψ x := hψ_pos hx
      have hden_pos : 0 < 2 * δ := by positivity
      exact div_pos (by linarith) hden_pos
    have hr_lt_one : r < 1 := by
      -- The strict hypothesis `ψ x < δ` makes the midpoint ratio strictly smaller than `1`.
      have hr_eq : r * (2 * δ) = ψ x + δ := by
        dsimp [r]
        field_simp [hδ_ne]
      have hden_pos : 0 < 2 * δ := by positivity
      nlinarith
    have hscaled :
        r * δ ≤ ψ x :=
      scaled_dual_step_le_value hF hx hgrad hψ_concave hψ_pos hH
        (show δ =
          HessianDualLocalNorm.ofDetNeZero F x hPos hH ((toDual ℝ E) (∇ ψ x)) by rfl)
        hδ_pos hr_pos hr_lt_one
    have hψ_lt_scaled : ψ x < r * δ := by
      -- This specific midpoint choice makes `r * δ = (ψ x + δ) / 2`, which exceeds `ψ x`.
      dsimp [r]
      have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
      have hrewrite : ((ψ x + δ) / (2 * δ)) * δ = (ψ x + δ) / 2 := by
        field_simp [hδ_ne, htwo_ne]
      rw [hrewrite]
      linarith
    linarith

end
