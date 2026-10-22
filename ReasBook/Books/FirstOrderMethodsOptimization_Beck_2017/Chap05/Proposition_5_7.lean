/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Proposition 5.7: the radial map underlying the derivative of
`x ↦ √(1 + ‖x‖²)`. -/
private def radialUnitBallMap (x : E) : E :=
  (Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)))⁻¹ • x

/-- Helper for Proposition 5.7: the Fréchet derivative of `x ↦ √(1 + ‖x‖²)` is the inner-product
functional associated to `radialUnitBallMap x`. -/
private lemma hasFDerivAt_sqrtOneAddSqNorm (x : E) :
    HasFDerivAt
      (fun y : E ↦ Real.sqrt (1 + ‖y‖ ^ (2 : ℕ)))
      ((innerSL ℝ) (radialUnitBallMap x))
      x := by
  -- Differentiate the positive scalar profile `1 + ‖x‖²`.
  have hsq : HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x :=
    hasStrictFDerivAt_norm_sq x |>.hasFDerivAt
  have hbase : HasFDerivAt (fun y : E ↦ 1 + ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x := by
    convert (hasFDerivAt_const (1 : ℝ) x).add hsq using 1
    ext y
    simp
  have hpos : (1 + ‖x‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hsqrt : Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)) ≠ 0 := by
    positivity
  -- Then apply the scalar square-root chain rule and simplify the coefficient.
  convert hbase.sqrt hpos using 1
  ext y
  field_simp [hsqrt]
  simp [radialUnitBallMap, ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  ring_nf

/-- Helper for Proposition 5.7: the bundled derivative field of `x ↦ √(1 + ‖x‖²)` is exactly the
`innerSL` image of `radialUnitBallMap`. -/
private lemma fderiv_sqrtOneAddSqNorm_eq (x : E) :
    fderiv ℝ (fun y : E ↦ Real.sqrt (1 + ‖y‖ ^ (2 : ℕ))) x = (innerSL ℝ) (radialUnitBallMap x) := by
  -- Unbundle the explicit derivative witness from `hasFDerivAt_sqrtOneAddSqNorm`.
  simpa using (hasFDerivAt_sqrtOneAddSqNorm x).fderiv

/-- Helper for Proposition 5.7: the affine line `s ↦ x + s • d` has derivative `d`. -/
private lemma hasDerivAt_affineLine (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the identity and then scale by the fixed direction `d`.
  simpa [one_smul] using ((hasDerivAt_id' t).smul_const d).const_add x

/-- Helper for Proposition 5.7: normalize the inverse-square-root line coefficient into the cubic
inverse form used by the radial derivative estimate. -/
private lemma radialLineInvCoeff_eq (z d : E) :
    -(inner ℝ (radialUnitBallMap z) d) / Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
      -(((Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) ^ (3 : ℕ))⁻¹ : ℝ) * inner ℝ z d) := by
  have hsqrt_ne : Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) ≠ 0 := by
    positivity
  -- Expand the radial map once and clear the denominator in a single spelling world.
  simp only [radialUnitBallMap, real_inner_smul_left]
  field_simp [hsqrt_ne]

/-- Helper for Proposition 5.7: along an affine line, the inverse radial denominator has the
expected cubic-inverse derivative. -/
private lemma hasDerivAt_invSqrtOneAddSqNormAlongLine (x d : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (Real.sqrt (1 + ‖x + s • d‖ ^ (2 : ℕ)))⁻¹)
      (-(((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)) ^ (3 : ℕ))⁻¹ : ℝ) *
        inner ℝ (x + t • d) d))
      t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • d) d t :=
    hasDerivAt_affineLine (x := x) (d := d) (t := t)
  have hsqrt :
      HasDerivAt
        (fun s : ℝ ↦ Real.sqrt (1 + ‖x + s • d‖ ^ (2 : ℕ)))
        ((innerSL ℝ (radialUnitBallMap (x + t • d))) d)
        t := by
    -- Compose the Fréchet derivative of `√(1 + ‖·‖²)` with the affine line.
    simpa [Function.comp] using
      (hasFDerivAt_sqrtOneAddSqNorm (x := x + t • d)).comp_hasDerivAt t hline
  have hsqrt_ne : Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)) ≠ 0 := by
    positivity
  -- Normalize the inverse derivative before reusing it in the vector-valued product rule.
  simpa [radialLineInvCoeff_eq] using hsqrt.inv hsqrt_ne

/-- Helper for Proposition 5.7: along an affine line, differentiating the radial map produces the
expected tangential term minus the radial correction term. -/
private lemma hasDerivAt_radialUnitBallMapAlongLine (x d : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ radialUnitBallMap (x + s • d))
      (((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)))⁻¹ : ℝ) • d -
        ((((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)))⁻¹) ^ (3 : ℕ) : ℝ) *
          inner ℝ (x + t • d) d) • (x + t • d))
      t := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • d) d t :=
    hasDerivAt_affineLine (x := x) (d := d) (t := t)
  have hinv :
      HasDerivAt
        (fun s : ℝ ↦ (Real.sqrt (1 + ‖x + s • d‖ ^ (2 : ℕ)))⁻¹)
        (-(((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)) ^ (3 : ℕ))⁻¹ : ℝ) *
          inner ℝ (x + t • d) d))
        t :=
    hasDerivAt_invSqrtOneAddSqNormAlongLine (x := x) (d := d) (t := t)
  -- Route correction: normalize the scalar inverse derivative first, then apply the product rule.
  convert hinv.smul hline using 1
  rw [sub_eq_add_neg, neg_smul, inv_pow]

/-- Helper for Proposition 5.7: the derivative of the radial map along any affine line has norm at
most the norm of the line direction. -/
private lemma norm_deriv_radialUnitBallMapAlongLine_le (x d : E) (t : ℝ) :
    ‖(((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)))⁻¹ : ℝ) • d -
        ((((Real.sqrt (1 + ‖x + t • d‖ ^ (2 : ℕ)))⁻¹) ^ (3 : ℕ) : ℝ) *
          inner ℝ (x + t • d) d) • (x + t • d))‖ ≤ ‖d‖ := by
  let z : E := x + t • d
  let a : ℝ := (Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)))⁻¹
  let v : E := a • d - ((a ^ (3 : ℕ) : ℝ) * inner ℝ z d) • z
  let c : ℝ := a ^ (3 : ℕ) * inner ℝ z d
  suffices hv_le : ‖v‖ ≤ ‖d‖ by
    simpa [z, a, v, c] using hv_le
  have hsq_unfactored :
      ‖v‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) - 2 * (a * c * inner ℝ d z) +
          c ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := by
    -- Expand the squared norm of the explicit derivative vector.
    have ha_nonneg : 0 ≤ a := by
      positivity
    dsimp [v, c]
    rw [norm_sub_sq_real]
    simp [norm_smul, ha_nonneg, real_inner_smul_left, real_inner_smul_right, abs_of_nonneg]
    ring_nf
    rw [sq_abs]
  have hsq_expansion :
      ‖v‖ ^ (2 : ℕ) =
        a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) -
          (a ^ (4 : ℕ) * (2 - a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ))) * (inner ℝ z d) ^ (2 : ℕ) := by
    have hcomm : inner ℝ d z = inner ℝ z d := by
      simpa using (real_inner_comm z d)
    calc
      ‖v‖ ^ (2 : ℕ) = a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) - 2 * (a * c * inner ℝ d z) +
          c ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := hsq_unfactored
      _ = a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) -
          (a ^ (4 : ℕ) * (2 - a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ))) * (inner ℝ z d) ^ (2 : ℕ) := by
            simp [c, hcomm]
            ring
  have hsqrt_ne : Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)) ≠ 0 := by
    positivity
  have hscale_eq_one : a ^ (2 : ℕ) * (1 + ‖z‖ ^ (2 : ℕ)) = 1 := by
    -- Record the normalization identity `a² (1 + ‖z‖²) = 1`.
    dsimp [a]
    field_simp [hsqrt_ne]
    rw [sq, Real.sq_sqrt (by positivity)]
  have hradial_le_one : a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) ≤ 1 := by
    -- The normalized radial factor is bounded by `1`.
    have ha_nonneg : 0 ≤ a ^ (2 : ℕ) := by positivity
    have hnorm_nonneg : 0 ≤ ‖z‖ ^ (2 : ℕ) := by positivity
    nlinarith [hscale_eq_one]
  have ha_sq_le_one : a ^ (2 : ℕ) ≤ 1 := by
    -- The scalar coefficient itself has absolute value at most `1`.
    have ha_nonneg : 0 ≤ a ^ (2 : ℕ) := by positivity
    have hsum_nonneg : 0 ≤ ‖z‖ ^ (2 : ℕ) := by positivity
    nlinarith [hscale_eq_one]
  have hcorrection_nonneg : 0 ≤ a ^ (4 : ℕ) * (2 - a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ)) := by
    -- The correction term has nonnegative coefficient, so subtracting it
    -- can only decrease the norm.
    have hfactor_nonneg : 0 ≤ 2 - a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := by
      nlinarith [hradial_le_one]
    positivity
  have hsq_le_scaled : ‖v‖ ^ (2 : ℕ) ≤ a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
    rw [hsq_expansion]
    nlinarith [sq_nonneg (inner ℝ z d), hcorrection_nonneg]
  have hsq_le : ‖v‖ ^ (2 : ℕ) ≤ ‖d‖ ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖d‖ ^ (2 : ℕ) := by positivity
    nlinarith [hsq_le_scaled, ha_sq_le_one]
  -- Compare nonnegative square roots to finish the norm estimate.
  nlinarith [hsq_le, norm_nonneg v, norm_nonneg d]

/-- Helper for Proposition 5.7: the radial map `x ↦ x / √(1 + ‖x‖²)` is nonexpansive on the whole
space. -/
private lemma radialUnitBallMap_lipschitzOnWith :
    LipschitzOnWith (1 : NNReal) (fun x : E ↦ radialUnitBallMap x) Set.univ := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x _ y _
  let φ : ℝ → E := fun t ↦ radialUnitBallMap (y + t • (x - y))
  let φ' : ℝ → E := fun t ↦
    (((Real.sqrt (1 + ‖y + t • (x - y)‖ ^ (2 : ℕ)))⁻¹ : ℝ) • (x - y) -
      ((((Real.sqrt (1 + ‖y + t • (x - y)‖ ^ (2 : ℕ)))⁻¹) ^ (3 : ℕ) : ℝ) *
        inner ℝ (y + t • (x - y)) (x - y)) • (y + t • (x - y)))
  have hdiff :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Restrict the explicit line derivative to the segment `[0, 1]`.
    simpa [φ, φ'] using
      (hasDerivAt_radialUnitBallMapAlongLine (x := y) (d := x - y) (t := t)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖φ' t‖ ≤ ‖x - y‖ := by
    intro t ht
    -- The derivative bound is uniform along the segment.
    simpa [φ'] using norm_deriv_radialUnitBallMapAlongLine_le (x := y) (d := x - y) (t := t)
  -- Route correction: use the one-dimensional mean-value estimate on the segment instead of the
  -- heavier bundled-operator normalization route.
  simpa [φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    norm_image_sub_le_of_norm_deriv_le_segment_01' hdiff hbound

/-- Proposition 5.7: on any real inner-product space, the radial function
`x ↦ √(1 + ‖x‖²)` is globally `1`-smooth. This is the reusable owner-level estimate behind the
Euclidean textbook statement. -/
theorem sqrt_one_add_sq_norm_is_l_smooth_innerProductSpace :
    is_l_smooth_on
      (fun x : E ↦ Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)))
      Set.univ
      1 := by
  -- Route correction: avoid the completeness-dependent gradient route and work directly with the
  -- derivative field encoded by `is_l_smooth_on`.
  rw [is_l_smooth_on]
  refine ⟨?_, ?_⟩
  · -- Differentiability follows from the explicit Fréchet derivative formula.
    intro x _
    exact (hasFDerivAt_sqrtOneAddSqNorm x).differentiableAt
  · -- The derivative field is the `innerSL` image of the radial map, so its Lipschitz estimate
    -- reduces to the nonexpansiveness of `radialUnitBallMap`.
    have hRadial := radialUnitBallMap_lipschitzOnWith (E := E)
    rw [lipschitzOnWith_iff_norm_sub_le] at hRadial ⊢
    intro x hx y hy
    calc
      ‖fderiv ℝ (fun z : E ↦ Real.sqrt (1 + ‖z‖ ^ (2 : ℕ))) x
          - fderiv ℝ (fun z : E ↦ Real.sqrt (1 + ‖z‖ ^ (2 : ℕ))) y‖
        = ‖(innerSL ℝ) (radialUnitBallMap x) - (innerSL ℝ) (radialUnitBallMap y)‖ := by
            simp [fderiv_sqrtOneAddSqNorm_eq]
      _ = ‖(innerSL ℝ) (radialUnitBallMap x - radialUnitBallMap y)‖ := by
            rw [← map_sub]
      _ = ‖radialUnitBallMap x - radialUnitBallMap y‖ := by
            simpa using
              (innerSL_apply_norm (𝕜 := ℝ) (E := E) (radialUnitBallMap x - radialUnitBallMap y))
      _ ≤ (1 : ℝ) * ‖x - y‖ := hRadial hx hy

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 5.7 is `source-facing`: it records the textbook smoothness estimate for the radial
function `x ↦ √(1 + ‖x‖²)` on Euclidean `ℝ^n`. Domain sampling in the Chapter 5 neighborhood
points to `is_l_smooth_on` as the owner abstraction for the conclusion, so this file keeps the
chapter's concrete Euclidean model on the public labeled surface.
-/

-- Proof sketch: `φ` is `C²` because `contDiff_norm_sq` and `ContDiffAt.sqrt` give smoothness for
-- the everywhere-positive scalar profile `x ↦ 1 + ‖x‖²`. Apply the owner-level Hessian criterion
-- from Theorem 5.12 after specializing to the Euclidean case. The remaining pointwise estimate is
-- the explicit Hessian computation
-- `D²φ(x) = (1 + ‖x‖²)^(-1/2) I - (1 + ‖x‖²)^(-3/2) (x ⊗ x)`, whose operator norm is at most `1`.
/-- Euclidean specialization of Proposition 5.7: the function `x ↦ √(1 + ‖x‖²)` on Euclidean
`ℝ^n` is globally `1`-smooth with respect to the `l₂` norm. -/
theorem sqrt_one_add_sq_norm_is_l_smooth :
    is_l_smooth_on
      (fun x : E ↦ Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)))
      Set.univ
      1 := by
  simpa using
    (sqrt_one_add_sq_norm_is_l_smooth_innerProductSpace :
      is_l_smooth_on
        (fun x : E ↦ Real.sqrt (1 + ‖x‖ ^ (2 : ℕ)))
        Set.univ
        1)

end
