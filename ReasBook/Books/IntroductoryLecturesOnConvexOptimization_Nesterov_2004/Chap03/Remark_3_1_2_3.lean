/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "P" => ℝ × E

/- Remark 3.1.2.3 lies in the convex-perspective / positive-homogeneity domain.

Sampled owner-style declarations:
- mathlib `ConvexCone`
- mathlib `ConvexOn`
- project `IsPositivelyHomogeneousOn`

Best owner abstraction:
- source-facing data: `perspectiveCone` and `perspectiveTransform`
- core/canonical owner for the domain: `ConvexCone ℝ (ℝ × E)`
- canonical owner predicates on that data: `ConvexOn` and `IsPositivelyHomogeneousOn`

Primitive data:
- a real `ℝ`-module `E`
- the cone owner `perspectiveCone E : ConvexCone ℝ (ℝ × E)`
- the transform `perspectiveTransform : (E → ℝ) → P → ℝ`

Derived API:
- `mem_perspectiveCone_iff`
- `perspectiveTransform_apply_of_pos`
- `perspectiveTransform_zero`
- the positive-homogeneity and convexity theorems for the perspective transform

Source/core/bridge triage:
- source-facing: `perspectiveCone`, `perspectiveTransform`
- core/canonical: `ConvexCone`, `ConvexOn`, `IsPositivelyHomogeneousOn`
- bridge/view: the small membership and evaluation lemmas relating the source-facing construction
  to those owner predicates

There is no upstream perspective-transform owner in the chapter or in mathlib, so this file keeps
the source-facing construction itself. The domain, however, is genuinely a convex cone, so the
refined file uses the canonical cone owner instead of a parallel bare-set definition.
-/

/-- The cone consisting of pairs `(τ, x)` with `τ > 0`, together with the origin. -/
def perspectiveCone (E : Type u) [AddCommMonoid E] [Module ℝ E] : ConvexCone ℝ (ℝ × E) where
  carrier := {z : ℝ × E | 0 < z.1 ∨ z = 0}
  smul_mem' := fun c hc z hz ↦ by
    rcases hz with hz | rfl
    · left
      change 0 < c * z.1
      simpa [smul_eq_mul] using mul_pos hc hz
    · right
      simp
  add_mem' := fun x hx y hy ↦ by
    rcases hx with hx | rfl
    · rcases hy with hy | rfl
      · left
        change 0 < x.1 + y.1
        exact add_pos hx hy
      · left
        simpa using hx
    · simpa using hy

/-- Membership in `perspectiveCone` means either strictly positive first coordinate or the
point is the origin. -/
@[simp]
theorem mem_perspectiveCone_iff
    {z : P} :
    z ∈ perspectiveCone E ↔ 0 < z.1 ∨ z = 0 :=
  Iff.rfl

/-- The perspective transform of a function `f : E → ℝ`, extended by the value `0` away from the
region `τ > 0`. On `perspectiveCone`, this agrees with the usual formula
`(τ, x) ↦ τ f (τ⁻¹ • x)` together with the value `0` at the origin. In the textbook case
`E = ℝⁿ`, this is the usual perspective transform. -/
def perspectiveTransform
    (f : E → ℝ) :
    P → ℝ :=
  fun z ↦
    if _ : 0 < z.1 then
      z.1 * f (z.1⁻¹ • z.2)
    else
      0

/-- On pairs with positive first coordinate, `perspectiveTransform f` is given by the usual
perspective formula. -/
theorem perspectiveTransform_apply_of_pos
    (f : E → ℝ)
    {z : P} (hz : 0 < z.1) :
    perspectiveTransform f z = z.1 * f (z.1⁻¹ • z.2) := by
  simp [perspectiveTransform, hz]

/-- At the origin, `perspectiveTransform f` takes the prescribed value `0`. -/
@[simp] theorem perspectiveTransform_zero
    (f : E → ℝ) :
    perspectiveTransform f 0 = 0 := by
  simp [perspectiveTransform]

/-- Helper for Remark 3.1.2.3: a point of `perspectiveCone` with nonpositive first coordinate is
the origin. -/
theorem eq_zero_of_mem_perspectiveCone_of_not_pos
    {z : P} (hz : z ∈ perspectiveCone E) (hzpos : ¬ 0 < z.1) :
    z = 0 := by
  -- A cone point is either strictly positive in the first coordinate or already the origin.
  rcases mem_perspectiveCone_iff.mp hz with hz' | hz'
  · exact (hzpos hz').elim
  · exact hz'

/-- Helper for Remark 3.1.2.3: the normalized perspective weights are nonnegative and sum to
`1`. -/
theorem perspective_weights_nonneg_sum_one
    {a b τ₁ τ₂ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    0 < a * τ₁ + b * τ₂ ∧
      0 ≤ a * τ₁ / (a * τ₁ + b * τ₂) ∧
      0 ≤ b * τ₂ / (a * τ₁ + b * τ₂) ∧
      a * τ₁ / (a * τ₁ + b * τ₂) + b * τ₂ / (a * τ₁ + b * τ₂) = 1 := by
  -- One coefficient is positive because `a + b = 1`; the corresponding term makes the sum
  -- strictly positive.
  have hτ : 0 < a * τ₁ + b * τ₂ := by
    have hab_pos : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        nlinarith [hb, hab]
      · left
        exact lt_of_le_of_ne ha fun h => ha0 h.symm
    rcases hab_pos with ha_pos | hb_pos
    · exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hτ₁) (mul_nonneg hb hτ₂.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hτ₁.le) (mul_pos hb_pos hτ₂)
  refine ⟨hτ, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg ha hτ₁.le) hτ.le
  · exact div_nonneg (mul_nonneg hb hτ₂.le) hτ.le
  · -- After combining the fractions, the numerator is exactly the denominator.
    rw [← add_div]
    field_simp [hτ.ne']

/-- Helper for Remark 3.1.2.3: the normalized point of the convex combination is the same convex
combination of the normalized points. -/
theorem perspective_normalized_combination_eq
    {a b τ₁ τ₂ : ℝ} {x₁ x₂ : E}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    (a * τ₁ + b * τ₂)⁻¹ • (a • x₁ + b • x₂) =
      (a * τ₁ / (a * τ₁ + b * τ₂)) • (τ₁⁻¹ • x₁) +
        (b * τ₂ / (a * τ₁ + b * τ₂)) • (τ₂⁻¹ • x₂) := by
  -- Distribute the outer normalization, then match the scalar coefficients term by term.
  rw [smul_add, smul_smul, smul_smul]
  rw [smul_smul, smul_smul]
  congr 1 <;> rw [div_eq_mul_inv] <;> field_simp [hτ₁.ne', hτ₂.ne']

/-- The perspective transform is positively homogeneous of degree `1` on `perspectiveCone` for
every `f : E → ℝ`. In the textbook case `E = ℝⁿ`, this is exactly the same perspective
homogeneity statement. -/
theorem perspectiveTransform_isPositivelyHomogeneousOn
    {f : E → ℝ} :
    IsPositivelyHomogeneousOn 1 (perspectiveCone E) (perspectiveTransform f) := by
  refine ⟨?_, ?_⟩
  · intro x hx τ
    by_cases hτ : τ = 0
    · -- Zero scaling sends every point to the origin, which lies in the cone.
      rw [hτ]
      simp [mem_perspectiveCone_iff]
    · -- Positive scaling preserves positivity of the first coordinate.
      have hτ_pos : 0 < (τ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
      rcases mem_perspectiveCone_iff.mp hx with hx_pos | hx_zero
      · refine mem_perspectiveCone_iff.mpr (Or.inl ?_)
        change 0 < (τ : ℝ) * x.1
        simpa using mul_pos hτ_pos hx_pos
      · refine mem_perspectiveCone_iff.mpr (Or.inr ?_)
        subst hx_zero
        simp
  · intro x hx τ
    by_cases hτ : τ = 0
    · -- The `τ = 0` branch is exactly the prescribed value at the origin.
      simp [hτ, perspectiveTransform_zero, Real.rpow_one]
    · have hτ_pos : 0 < (τ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hτ)
      by_cases hx_pos : 0 < x.1
      · -- In the positive branch, expand the perspective formula and cancel the extra scalar.
        have hsmul_pos : 0 < (τ • x : P).1 := by
          change 0 < (τ : ℝ) * x.1
          simpa using mul_pos hτ_pos hx_pos
        have hmul_ne : (τ : ℝ) * x.1 ≠ 0 := by
          exact mul_ne_zero (show (τ : ℝ) ≠ 0 from by exact_mod_cast hτ) hx_pos.ne'
        have hcancel :
            (((τ : ℝ) * x.1)⁻¹ : ℝ) * (τ : ℝ) = x.1⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul₀ hmul_ne]
          rw [mul_assoc, mul_inv_cancel₀ hx_pos.ne', mul_one]
        calc
          perspectiveTransform f (τ • x)
              = (τ • x).1 * f (((τ • x).1)⁻¹ • (τ • x).2) :=
                  perspectiveTransform_apply_of_pos f hsmul_pos
          _ = ((τ : ℝ) * x.1) * f ((((τ : ℝ) * x.1)⁻¹ : ℝ) • ((τ : ℝ) • x.2)) := by
                rfl
          _ = ((τ : ℝ) * x.1) * f (x.1⁻¹ • x.2) := by
                rw [show ((((τ : ℝ) * x.1)⁻¹ : ℝ) • ((τ : ℝ) • x.2)) =
                    x.1⁻¹ • x.2 by
                    rw [smul_smul, hcancel]]
          _ = (τ : ℝ) * (x.1 * f (x.1⁻¹ • x.2)) := by ring
          _ = Real.rpow (τ : ℝ) 1 • perspectiveTransform f x := by
                rw [perspectiveTransform_apply_of_pos f hx_pos]
                simp [Real.rpow_one, smul_eq_mul]
      · -- A nonpositive cone point is the origin, so both sides vanish.
        have hx_zero : x = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hx hx_pos
        subst hx_zero
        simp [perspectiveTransform_zero, Real.rpow_one]

/-- If `f` is convex on `E`, then its perspective transform is convex on `perspectiveCone`. In
the textbook case `E = ℝⁿ`, this is exactly the same perspective-convexity statement. -/
theorem perspectiveTransform_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ (perspectiveCone E) (perspectiveTransform f) := by
  refine ⟨(perspectiveCone E).convex, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases hx_pos : 0 < x.1
  · by_cases hy_pos : 0 < y.1
    · -- Route correction: keep the source proof's normalized-weight argument on the strictly
      -- positive branch instead of switching to an ad hoc concrete recursion.
      have hweights := perspective_weights_nonneg_sum_one ha hb hab hx_pos hy_pos
      rcases hweights with ⟨hτ_pos, hw₁_nonneg, hw₂_nonneg, hw_sum⟩
      set τ : ℝ := a * x.1 + b * y.1
      have hτ_pos' : 0 < τ := by simpa [τ] using hτ_pos
      have hjensen :
          f (τ⁻¹ • (a • x.2 + b • y.2)) ≤
            (a * x.1 / τ) * f (x.1⁻¹ • x.2) +
              (b * y.1 / τ) * f (y.1⁻¹ • y.2) := by
        -- Apply convexity of `f` to the normalized points with the normalized perspective weights.
        simpa [τ, smul_eq_mul, perspective_normalized_combination_eq hx_pos hy_pos] using
          hf.2 (by simp : x.1⁻¹ • x.2 ∈ Set.univ) (by simp : y.1⁻¹ • y.2 ∈ Set.univ)
            hw₁_nonneg hw₂_nonneg hw_sum
      have hscaled := mul_le_mul_of_nonneg_left hjensen hτ_pos'.le
      have hcomb_pos : 0 < (a • x + b • y : P).1 := by
        change 0 < a * x.1 + b * y.1
        simpa [τ] using hτ_pos'
      calc
        perspectiveTransform f (a • x + b • y)
            = τ * f (τ⁻¹ • (a • x.2 + b • y.2)) := by
                -- Expanding the perspective transform on the positive combined first coordinate
                -- recovers the normalized source-proof expression.
                simpa [τ] using perspectiveTransform_apply_of_pos f hcomb_pos
        _ ≤ τ *
              ((a * x.1 / τ) * f (x.1⁻¹ • x.2) +
                (b * y.1 / τ) * f (y.1⁻¹ • y.2)) := hscaled
        _ = a * perspectiveTransform f x + b * perspectiveTransform f y := by
              rw [perspectiveTransform_apply_of_pos f hx_pos, perspectiveTransform_apply_of_pos f hy_pos]
              field_simp [hτ_pos'.ne']
        _ = a • perspectiveTransform f x + b • perspectiveTransform f y := by
              simp [smul_eq_mul]
    · -- If `y` is not positive, membership forces `y = 0`, so homogeneity handles the branch.
      have hy_zero : y = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hy hy_pos
      subst hy_zero
      have hmap :=
        (perspectiveTransform_isPositivelyHomogeneousOn (f := f)).map_smul hx
          ⟨a, ha⟩
      exact le_of_eq <| by
        simpa [Real.rpow_one, smul_eq_mul, perspectiveTransform_zero, hab] using hmap
  · -- If `x` is not positive, membership forces `x = 0`, and we reduce to the other branch.
    have hx_zero : x = 0 := eq_zero_of_mem_perspectiveCone_of_not_pos hx hx_pos
    subst hx_zero
    have hmap :=
      (perspectiveTransform_isPositivelyHomogeneousOn (f := f)).map_smul hy
        ⟨b, hb⟩
    exact le_of_eq <| by
      simpa [Real.rpow_one, smul_eq_mul, perspectiveTransform_zero, hab, add_comm] using hmap

/-- Remark 3.1.2.3: if `f` is convex on `E`, then its perspective transform
`(τ, x) ↦ τ f (τ⁻¹ • x)` is positively homogeneous on the cone `τ > 0` together with the origin,
and it is convex on that same domain. For the source statement, take `E = ℝⁿ`. -/
-- Proof sketch: for positive homogeneity, expand the definition and rewrite
-- `(c * τ)⁻¹ • (c • x) = τ⁻¹ • x` for `c ≥ 0`; the case `c = 0` reduces to the value at the
-- origin. For convexity, apply convexity of `f` to the normalized points
-- `x₁ / τ₁` and `x₂ / τ₂` with weights proportional to `τ₁` and `τ₂`.
theorem perspectiveTransform_posHomogeneous_and_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    IsPositivelyHomogeneousOn 1 (perspectiveCone E) (perspectiveTransform f) ∧
      ConvexOn ℝ (perspectiveCone E) (perspectiveTransform f) := by
  exact ⟨perspectiveTransform_isPositivelyHomogeneousOn, perspectiveTransform_convexOn hf⟩

end
