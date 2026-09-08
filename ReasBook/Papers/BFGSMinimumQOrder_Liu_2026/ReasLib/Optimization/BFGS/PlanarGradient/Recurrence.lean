module

public import ReasLib.Optimization.BFGS.PlanarGradient

public section

noncomputable section

universe u

namespace PlanarGradient

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Under the pre-step relation, the parallel coefficient is the scaled oriented area
of the normalized adjacent gradients. -/
theorem parallelCoefficient_eq_of_preStep (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev)) :
    parallelCoefficient gPrev g =
      δPrev * ‖g‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
        ‖g - gPrev‖ := by
  -- First rewrite the pre-step relation as an oriented-area identity for the raw secant.
  have hNumerator : inner ℝ (g - gPrev) g =
      δPrev * ‖g‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) := by
    calc
      inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev) := hPre
      _ = δPrev * inner ℝ g (tangent o gPrev) := by
        rw [perturbation_apply, inner_smul_right]
      _ = δPrev * (-o.areaForm g (NormedSpace.normalize gPrev)) := by
        rw [tangent_apply, o.inner_rightAngleRotation_right]
      _ = δPrev * o.areaForm (NormedSpace.normalize gPrev) g := by
        rw [o.areaForm_swap]
        ring
      _ = δPrev * o.areaForm (NormedSpace.normalize gPrev)
          (‖g‖ • NormedSpace.normalize g) := by
        rw [NormedSpace.norm_smul_normalize]
      _ = δPrev * ‖g‖ *
          o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) := by
        rw [map_smul]
        ring
  -- Normalizing the secant introduces precisely the denominator in the formula.
  rw [parallelCoefficient_apply, stepDirection_apply, NormedSpace.normalize,
    inner_smul_left, hNumerator]
  simp only [conj_trivial, div_eq_mul_inv]
  ring

/-- The tangent coefficient is the previous gradient norm times the oriented area of
the normalized adjacent gradients, divided by their difference norm. -/
theorem tangentCoefficient_eq_areaForm (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev)) :
    tangentCoefficient o gPrev g =
      ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
        ‖g - gPrev‖ := by
  -- Alternation removes the radial part of the secant and retains the previous gradient.
  have hCurrentArea :
      o.areaForm g (NormedSpace.normalize g) = 0 := by
    calc
      o.areaForm g (NormedSpace.normalize g) =
          o.areaForm (‖g‖ • NormedSpace.normalize g) (NormedSpace.normalize g) := by
        rw [NormedSpace.norm_smul_normalize]
      _ = 0 := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
          o.areaForm_apply_self, mul_zero]
  have hPreviousArea :
      o.areaForm gPrev (NormedSpace.normalize g) =
        ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) := by
    calc
      o.areaForm gPrev (NormedSpace.normalize g) =
          o.areaForm (‖gPrev‖ • NormedSpace.normalize gPrev)
            (NormedSpace.normalize g) := by
        rw [NormedSpace.norm_smul_normalize]
      _ = ‖gPrev‖ *
          o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hSecantArea :
      -o.areaForm (g - gPrev) (NormedSpace.normalize g) =
        ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) := by
    rw [map_sub, LinearMap.sub_apply, hCurrentArea, hPreviousArea]
    ring
  -- The inner-product/area bridge and secant normalization now give the quotient.
  rw [tangentCoefficient_apply, stepDirection_apply, tangent_apply,
    o.inner_rightAngleRotation_right, NormedSpace.normalize, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  calc
    -(‖g - gPrev‖⁻¹ * o.areaForm (g - gPrev) (NormedSpace.normalize g)) =
        ‖g - gPrev‖⁻¹ *
          (-o.areaForm (g - gPrev) (NormedSpace.normalize g)) := by ring
    _ = ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev)
        (NormedSpace.normalize g) / ‖g - gPrev‖ := by
      rw [hSecantArea]
      simp only [div_eq_mul_inv]
      ring

/-- Positive angular separation makes the tangent coefficient nonzero. -/
theorem tangentCoefficient_ne_zero (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hSeparation : 0 < angularSeparation o gPrev g) :
    tangentCoefficient o gPrev g ≠ 0 := by
  -- Positivity of angular separation says that the normalized oriented area is nonzero.
  have hArea : o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) ≠ 0 := by
    rw [angularSeparation_apply] at hSeparation
    exact (abs_pos.mp hSeparation)
  have hPrevNorm : ‖gPrev‖ ≠ 0 := norm_ne_zero_iff.mpr hPrev
  have hSecantNorm : ‖g - gPrev‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hDistinct)
  -- The area formula is a quotient of three nonzero factors.
  rw [tangentCoefficient_eq_areaForm o gPrev g δPrev hPrev hg hDistinct hPre]
  exact div_ne_zero (mul_ne_zero hPrevNorm hArea) hSecantNorm

/-- Under positive angular separation, the absolute ratio of the parallel and tangent
coefficients is the absolute perturbation scale times the ratio of gradient norms. -/
theorem abs_coefficientRatio (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hSeparation : 0 < angularSeparation o gPrev g) :
    |parallelCoefficient gPrev g / tangentCoefficient o gPrev g| =
      |δPrev| * ‖g‖ / ‖gPrev‖ := by
  -- Record the nonzero common factors before cancelling the two coefficient formulas.
  have hArea : o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) ≠ 0 := by
    rw [angularSeparation_apply] at hSeparation
    exact abs_pos.mp hSeparation
  have hPrevNorm : ‖gPrev‖ ≠ 0 := norm_ne_zero_iff.mpr hPrev
  have hSecantNorm : ‖g - gPrev‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hDistinct)
  have hRatio :
      (δPrev * ‖g‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
          ‖g - gPrev‖) /
        (‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
          ‖g - gPrev‖) = δPrev * ‖g‖ / ‖gPrev‖ := by
    field_simp
  -- Substitute the formulas, cancel algebraically, and distribute the absolute value.
  rw [parallelCoefficient_eq_of_preStep o gPrev g δPrev hPrev hg hDistinct hPre,
    tangentCoefficient_eq_areaForm o gPrev g δPrev hPrev hg hDistinct hPre, hRatio]
  simp only [abs_div, abs_mul, abs_norm]

/-- Every tangential choice at a nondegenerate next gradient satisfies the post-step
orthogonality relation with the current candidate. -/
theorem next_candidate_orthogonal (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (ΔNext : E) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0)
    (hTangent : inner ℝ (next o gPrev g δ) ΔNext = 0) :
    inner ℝ (next o gPrev g δ)
      ((next o gPrev g δ + ΔNext) - candidate o g δ) = 0 := by
  -- Split the displacement so the assumed tangential inner product vanishes directly.
  rw [inner_sub_right, inner_add_right, hTangent, add_zero]
  have hDirectionInner :
      inner ℝ (stepDirection gPrev g) (stepDirection gPrev g) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_stepDirection hDistinct]
    norm_num
  -- Both remaining projections are the two summands defining the recurrence scale.
  rw [next_apply, candidate_apply, perturbation_apply]
  simp only [inner_smul_left, inner_smul_right, inner_add_right, conj_trivial]
  rw [hDirectionInner, ← parallelCoefficient_apply, ← tangentCoefficient_apply, scale_apply]
  ring

/-- The next gradient lies in the span of the difference of the adjacent gradients. -/
theorem next_mem_span (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    next o gPrev g δ ∈ Submodule.span ℝ {g - gPrev} := by
  -- Expand the normalized secant as a scalar multiple of the spanning generator.
  rw [next_apply, stepDirection_apply, NormedSpace.normalize, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- A nonzero recurrence scale and distinct adjacent gradients produce a nonzero next
gradient. -/
theorem next_ne_zero (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    next o gPrev g δ ≠ 0 := by
  -- Distinct gradients give a unit, hence nonzero, normalized secant direction.
  have hDirection : stepDirection gPrev g ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_stepDirection hDistinct]
    norm_num
  -- A nonzero scalar multiple of that direction is nonzero.
  rw [next_apply]
  exact smul_ne_zero hScale hDirection

/-- Angular separation after a nondegenerate recurrence step is the previous separation
scaled by the ratio of the previous gradient norm to the gradient-difference norm. -/
theorem angularSeparation_next (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    angularSeparation o g (next o gPrev g δ) =
      ‖gPrev‖ * angularSeparation o gPrev g / ‖g - gPrev‖ := by
  -- The tangent-coefficient formula identifies the oriented area of the new direction.
  have hArea :
      o.areaForm (NormedSpace.normalize g) (stepDirection gPrev g) =
        ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g) /
          ‖g - gPrev‖ := by
    calc
      o.areaForm (NormedSpace.normalize g) (stepDirection gPrev g) =
          -o.areaForm (stepDirection gPrev g) (NormedSpace.normalize g) := by
        rw [o.areaForm_swap]
      _ = inner ℝ (stepDirection gPrev g)
          (o.rightAngleRotation (NormedSpace.normalize g)) := by
        rw [o.inner_rightAngleRotation_right]
      _ = tangentCoefficient o gPrev g := by
        rw [tangentCoefficient_apply, tangent_apply]
      _ = ‖gPrev‖ * o.areaForm (NormedSpace.normalize gPrev)
          (NormedSpace.normalize g) / ‖g - gPrev‖ :=
        tangentCoefficient_eq_areaForm o gPrev g δPrev hPrev hg hDistinct hPre
  have hDirectionNormalize :
      NormedSpace.normalize (stepDirection gPrev g) = stepDirection gPrev g :=
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_stepDirection hDistinct)
  -- Normalize the signed recurrence scale; its sign disappears under absolute value.
  rcases lt_or_gt_of_ne hScale with hNegative | hPositive
  · rw [angularSeparation_apply, next_apply,
      NormedSpace.normalize_smul_of_neg hNegative, hDirectionNormalize, map_neg, abs_neg,
      hArea, angularSeparation_apply]
    simp only [abs_div, abs_mul, abs_norm]
  · rw [angularSeparation_apply, next_apply,
      NormedSpace.normalize_smul_of_pos hPositive, hDirectionNormalize, hArea,
      angularSeparation_apply]
    simp only [abs_div, abs_mul, abs_norm]

/-- The absolute tangent coefficient equals the angular separation after a nondegenerate
recurrence step. -/
theorem abs_tangentCoefficient_eq_next (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    |tangentCoefficient o gPrev g| = angularSeparation o g (next o gPrev g δ) := by
  -- Rewrite both sides to the common normalized oriented-area expression.
  rw [tangentCoefficient_eq_areaForm o gPrev g δPrev hPrev hg hDistinct hPre,
    angularSeparation_next o gPrev g δPrev δ hPrev hg hDistinct hPre hScale,
    angularSeparation_apply]
  simp only [abs_div, abs_mul, abs_norm]

end OrientedPlane

end PlanarGradient
