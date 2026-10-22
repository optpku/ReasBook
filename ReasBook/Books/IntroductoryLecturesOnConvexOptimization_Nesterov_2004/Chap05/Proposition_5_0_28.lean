/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Remark_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient WithTopConvexAnalysis

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

local notation "P" => ℝ × ℝ
local notation "Q" => (perspectiveCone ℝ : Set P)
local notation "perspectiveSquare" =>
  perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ))

/- Proposition 5.0.28 lies in the chapter's perspective-transform / effective-domain /
explicit-gradient-image domain.

Primary domain:
- the perspective transform of the scalar square function, viewed through the chapter's canonical
  `+∞`-extension owner, and the explicit image of its gradient.

Relevant owner-style declarations sampled before refinement:
- `perspectiveCone` in `Remark_3_1_2_3`, the chapter owner for the cone `τ > 0` together with the
  origin;
- `mem_perspectiveCone_iff`, the canonical membership bridge for that owner;
- `perspectiveTransform`, the chapter owner for the perspective transform on `ℝ × E`;
- `fenchelPrimalExtension` in `Chap05/FenchelPrimalExtension`, the chapter owner for extending a
  real-valued function by `⊤` away from a feasible set;
- `dom` / `withTopRealPart` from `Definition_3_3`, the chapter owners for the finite-value domain
  and its real representative;
- `Chap05RealProdL2.instInnerProductSpaceRealProd`, the chapter owner bridge that equips the raw
  pair model `ℝ × ℝ` with the canonical `L²` inner-product structure;
- mathlib `∇` / `HasGradientAt`, the canonical ambient gradient owner on the genuine
  differentiability region.

Best owner abstraction:
- source-facing: the specific perspective-square specialization of the chapter owner
  `fenchelPrimalExtension` and the explicit parabola theorem for its gradient image;
- core/canonical: `fenchelPrimalExtension`, `perspectiveCone ℝ`, `perspectiveTransform`, `dom`,
  `withTopRealPart`, and the ambient gradient on the raw pair owner `P` equipped with the
  chapter `RealProdL2` structure;
- bridge/view: the pointwise formulas on the positive cone and the effective-domain
  identification carrying the origin.

Primitive data:
- the chapter owner cone `perspectiveCone ℝ : ConvexCone ℝ P`;
- the chapter owner perspective transform specialized to `fun y : ℝ ↦ y ^ (2 : ℕ)`.

Derived API:
- the specialization `F := fenchelPrimalExtension (perspectiveCone ℝ)
    (perspectiveTransform (fun y : ℝ ↦ y ^ (2 : ℕ)))`;
- the effective-domain identification `dom F = perspectiveCone ℝ`;
- the interior-domain bridge `interior (dom F) = {z | 0 < z.1}`;
- the displayed formula for the ambient gradient on the raw pair owner `P`;
- the parabola image theorem for that actual gradient on the positive cone.

The previous version exposed a bespoke local `+∞`-extension and a totalized gradient map,
assigning an arbitrary value at the origin. That is not mathematically faithful because the origin
belongs to the effective domain but not to the differentiability region. This refinement keeps the
same textbook semantics, deletes the redundant local wrapper, reuses the chapter owners
`fenchelPrimalExtension`, `perspectiveCone`, `perspectiveTransform`, `dom`, and
`withTopRealPart`, and states the source-facing gradient theorems directly on the raw pair owner
`P` via the chapter `RealProdL2` bridge instead of exposing explicit `WithLp` transport, with the
origin appearing only in the effective-domain bridge. -/

local notation "F" =>
  fenchelPrimalExtension Q perspectiveSquare

/-- The origin belongs to the effective domain of the perspective-square extension. -/
theorem zero_mem_dom_perspectiveSquare : (0 : P) ∈ dom F := by
  exact
    ((mem_dom_fenchelPrimalExtension_iff :
      (0 : P) ∈ dom F ↔ (0 : P) ∈ Q).2 ((mem_perspectiveCone_iff).2 (Or.inr rfl)))

/-- On pairs with positive first coordinate, the canonical perspective-square extension is given
by the usual perspective formula `y² / τ`. -/
theorem perspectiveSquare_apply_of_positive_fst {z : P} (hz : 0 < z.1) :
    F z = (((z.2 ^ (2 : ℕ) / z.1 : ℝ)) : WithTop ℝ) := by
  rw [fenchelPrimalExtension_apply_of_mem]
  · have hsq :
        perspectiveSquare z = z.2 ^ (2 : ℕ) / z.1 := by
      have hz0 : z.1 ≠ 0 := hz.ne'
      rw [perspectiveTransform_apply_of_pos _ hz]
      calc
        z.1 * ((z.1⁻¹ • z.2) ^ (2 : ℕ))
            = z.1 * ((z.1⁻¹ * z.2) ^ (2 : ℕ)) := by rfl
        _ = z.1 * (z.1⁻¹ ^ (2 : ℕ) * z.2 ^ (2 : ℕ)) := by rw [mul_pow]
        _ = (z.1 * z.1⁻¹ ^ (2 : ℕ)) * z.2 ^ (2 : ℕ) := by ring
        _ = z.1⁻¹ * z.2 ^ (2 : ℕ) := by
          congr 1
          calc
            z.1 * z.1⁻¹ ^ (2 : ℕ) = (z.1 * z.1⁻¹) * z.1⁻¹ := by
              simp [pow_two]
              ring
            _ = z.1⁻¹ := by simp [hz0]
        _ = z.2 ^ (2 : ℕ) / z.1 := by rw [div_eq_mul_inv, mul_comm]
    simp [hsq]
  · exact (mem_perspectiveCone_iff).2 (Or.inl hz)

/-- The finite-value domain of the canonical perspective-square extension is exactly the chapter
owner cone `perspectiveCone ℝ`. -/
theorem perspectiveSquare_effectiveDomain :
    dom F = perspectiveCone ℝ := by
  change dom F = Q
  exact dom_fenchelPrimalExtension

/-- The differentiability region of the finite real part of the canonical perspective-square
extension is exactly the open positive cone `τ > 0`. The origin remains in `dom F`, but only as a
boundary point of the effective domain. -/
theorem perspectiveSquare_interior_effectiveDomain :
    interior (dom F) = {z : P | 0 < z.1} := by
  rw [perspectiveSquare_effectiveDomain]
  have hzero_not_mem :
      (0 : P) ∉ interior (perspectiveCone ℝ : Set P) := by
    intro hzero
    have himage :
        Prod.fst '' (perspectiveCone ℝ : Set P) = Set.Ici (0 : ℝ) := by
      ext τ
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases z with ⟨τ, x⟩
        rcases (mem_perspectiveCone_iff).1 hz with hτ | hz0
        · exact le_of_lt hτ
        · cases hz0
          have h0 : (0 : ℝ) ≤ 0 := le_rfl
          exact h0
      · intro hτ
        by_cases hτ0 : τ = 0
        · refine ⟨0, (mem_perspectiveCone_iff).2 (Or.inr rfl), ?_⟩
          simp [hτ0]
        · have hτ_pos : 0 < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
          refine ⟨(τ, 0), (mem_perspectiveCone_iff).2 (Or.inl hτ_pos), ?_⟩
          simp
    have hzero_image :
        (0 : ℝ) ∈ interior (Prod.fst '' (perspectiveCone ℝ : Set P)) :=
      isOpenMap_fst.image_interior_subset (perspectiveCone ℝ : Set P) ⟨0, hzero, rfl⟩
    rw [himage] at hzero_image
    simp at hzero_image
  have hpos_mem :
      {z : P | 0 < z.1} ⊆ interior (perspectiveCone ℝ : Set P) := by
    refine (isOpen_lt continuous_const continuous_fst).subset_interior_iff.2 ?_
    intro z hz
    exact (mem_perspectiveCone_iff).2 (Or.inl hz)
  refine subset_antisymm ?_ hpos_mem
  intro z hz
  rcases (mem_perspectiveCone_iff).1 (interior_subset hz) with hz1 | hz0
  · exact hz1
  · subst z
    exact (hzero_not_mem hz).elim

/-- On pairs with positive first coordinate, the canonical ambient gradient of the finite real
part of the perspective-square extension on the raw pair owner `P` is given by the displayed
rational formula. -/
theorem perspectiveSquare_gradient_eq_formula_of_positive_fst
    {z : P} (hz : 0 < z.1) :
    ∇ (withTopRealPart F) z =
      (-((z.2 / z.1) ^ (2 : ℕ)), (2 : ℝ) * (z.2 / z.1)) := by
  let rationalBranch : P → ℝ := fun w ↦ w.2 ^ (2 : ℕ) / w.1
  let gradVec : P :=
    (-(z.2 ^ (2 : ℕ)) * (z.1 ^ (2 : ℕ))⁻¹, ((2 : ℝ) * z.2) * z.1⁻¹)
  have hpairinner : ∀ a b c d : ℝ, inner ℝ ((a, b) : P) (c, d) = a * c + b * d := by
    intro a b c d
    -- Expand the raw-product inner product through the chapter's `WithLp` owner.
    change inner ℝ (WithLp.toLp 2 ((a, b) : P)) (WithLp.toLp 2 (c, d)) = a * c + b * d
    rw [WithLp.prod_inner_apply]
    simp
    change c * a + d * b = a * c + b * d
    ring
  have hEventual :
      Filter.EventuallyEq (nhds z) (withTopRealPart F) rationalBranch := by
    -- Near a positive point we stay inside the positive cone, so the extension is the rational
    -- branch `w₂² / w₁`.
    have hopen : IsOpen {w : P | 0 < w.1} := isOpen_lt continuous_const continuous_fst
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [withTopRealPart_fenchelPrimalExtension_apply_of_mem]
    · rw [perspectiveTransform_apply_of_pos _ hw]
      calc
        w.1 * ((w.1⁻¹ • w.2) ^ (2 : ℕ)) = w.1 * ((w.1⁻¹ * w.2) ^ (2 : ℕ)) := by rfl
        _ = w.1 * (w.1⁻¹ ^ (2 : ℕ) * w.2 ^ (2 : ℕ)) := by rw [mul_pow]
        _ = (w.1 * w.1⁻¹ ^ (2 : ℕ)) * w.2 ^ (2 : ℕ) := by ring
        _ = w.1⁻¹ * w.2 ^ (2 : ℕ) := by
          congr 1
          calc
            w.1 * w.1⁻¹ ^ (2 : ℕ) = (w.1 * w.1⁻¹) * w.1⁻¹ := by
              simp [pow_two]
              ring
            _ = w.1⁻¹ := by simp [hw.ne']
        _ = w.2 ^ (2 : ℕ) / w.1 := by rw [div_eq_mul_inv, mul_comm]
    · exact (mem_perspectiveCone_iff).2 (Or.inl hw)
  have hfst : HasFDerivAt (fun w : P ↦ w.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun w : P ↦ w.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
    simpa using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hsq0 := hsnd.pow 2
  have hsq :
      HasFDerivAt (fun w : P ↦ w.2 ^ (2 : ℕ))
        (((2 : ℝ) * z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
    -- Rewrite the generic power-rule output into the coordinate-linear-map form we want.
    convert hsq0 using 1
    show (((2 : ℝ) * z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ : P →L[ℝ] ℝ) =
        (2 • z.2 ^ (2 - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ
    exact ContinuousLinearMap.ext fun w => by simp
  have hinv0 := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z hfst
  have hinv :
      HasFDerivAt (fun w : P ↦ (w.1)⁻¹)
        ((-((z.1 ^ (2 : ℕ))⁻¹)) • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
    -- The first-coordinate inverse differentiates by the scalar inverse rule.
    convert hinv0 using 1 <;> funext w <;> rfl
  have hmul :
      HasFDerivAt (fun w : P ↦ (w.2 ^ (2 : ℕ)) * (w.1)⁻¹)
        (z.2 ^ (2 : ℕ) • (-((z.1 ^ (2 : ℕ))⁻¹)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          z.1⁻¹ • (((2 : ℝ) * z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) z := by
    -- Product rule for `w₂² * w₁⁻¹`.
    simpa using hsq.mul hinv
  have hderiv : HasFDerivAt rationalBranch (innerSL ℝ gradVec) z := by
    -- Translate the product-rule derivative into the Riesz functional of the candidate gradient.
    convert hmul using 1
    show (innerSL ℝ gradVec : P →L[ℝ] ℝ) =
        z.2 ^ (2 : ℕ) • (-((z.1 ^ (2 : ℕ))⁻¹)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          z.1⁻¹ • (((2 : ℝ) * z.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    exact ContinuousLinearMap.ext fun w => by
      rcases w with ⟨w1, w2⟩
      rw [innerSL_apply_apply, hpairinner]
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, gradVec]
      ring
  have hdual_fun :
      innerSL ℝ ((InnerProductSpace.toDual ℝ P).symm (innerSL ℝ gradVec)) = innerSL ℝ gradVec := by
    exact ContinuousLinearMap.ext fun w => by
      simp [InnerProductSpace.toDual_symm_apply, innerSL_apply_apply]
  have hdual : (InnerProductSpace.toDual ℝ P).symm (innerSL ℝ gradVec) = gradVec := by
    exact (innerSL_inj).mp hdual_fun
  have hgrad_rational : HasGradientAt rationalBranch gradVec z := by
    -- Convert the Fréchet-derivative computation into a gradient statement.
    simpa [hdual] using hderiv.hasGradientAt
  have hgrad_extension : HasGradientAt (withTopRealPart F) gradVec z := by
    -- The extension and the rational branch agree near `z`, so they have the same gradient there.
    exact hgrad_rational.congr_of_eventuallyEq hEventual
  calc
    ∇ (withTopRealPart F) z = gradVec := hgrad_extension.gradient
    _ = (-((z.2 / z.1) ^ (2 : ℕ)), (2 : ℝ) * (z.2 / z.1)) := by
      ext <;> simp [gradVec, pow_two, div_eq_mul_inv] <;> ring

/-- Proposition 5.0.28: the image of the gradient of the perspective-square function is the
parabola in `ℝ × ℝ` cut out by `g₁ = -(g₂)² / 4`, where the gradient is taken on the genuine
differentiability region `τ > 0`. -/
theorem perspectiveSquare_gradient_image_eq_parabola :
    (fun z : P ↦ ∇ (withTopRealPart F) z) '' {z : P | 0 < z.1} =
      {g : P | g.1 = -(g.2 ^ (2 : ℕ)) / 4} := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    -- Every gradient point is parametrized by the slope ratio `z₂ / z₁`, hence lies on the
    -- parabola.
    change (∇ (withTopRealPart F) z).1 = -((∇ (withTopRealPart F) z).2 ^ (2 : ℕ)) / 4
    rw [perspectiveSquare_gradient_eq_formula_of_positive_fst hz]
    simp [pow_two, div_eq_mul_inv]
    ring
  · intro hg
    refine ⟨(1, g.2 / 2), by norm_num, ?_⟩
    have hz : 0 < ((1, g.2 / 2) : P).1 := by norm_num
    -- Route correction: use the canonical witness `(1, g₂ / 2)` so the ratio parameter is
    -- exactly `g₂ / 2`.
    change ∇ (withTopRealPart F) (1, g.2 / 2) = g
    rw [perspectiveSquare_gradient_eq_formula_of_positive_fst hz]
    ext
    · calc
        -((((g.2 / 2) / 1) ^ (2 : ℕ))) = -(g.2 ^ (2 : ℕ)) / 4 := by
          ring_nf
        _ = g.1 := by simpa [hg] using hg.symm
    · ring_nf

end
