module

public import ReasLib.Analysis.Calculus.LocalCutoff.CenterProjection
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.Transform

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-- The unbundled graph transform obtained by evaluating the stable coordinate at the
inverse center parameter. -/
noncomputable def raw (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) : ℝ → X :=
  fun ū ↦
    let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū
    (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).2

/-- The raw graph transform evaluates to the stable coordinate at the inverse center
parameter. -/
theorem raw_apply (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) (ū : ℝ) :
    let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū
    raw χ ρ L N ζ ū = (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).2 := by
  rfl

/-- The quantitative graph-transform contraction coefficient. -/
noncomputable def rate (lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ≥0 :=
  (linearRate + stableFiber) +
    (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber

/-- The contraction coefficient is the sum of the direct stable term and the term caused
by variation of the inverse center parameter. -/
theorem rate_def (lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) :
    rate lower linearRate stableCenter stableFiber centerFiber slope =
      (linearRate + stableFiber) +
        (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber := by
  rfl

/-- The inverse-center formula obeys the prescribed graph Lipschitz constant under the
split stable estimate. -/
theorem raw_lipschitzWith (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower linearRate stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) :
    LipschitzWith slope (raw χ ρ L N ζ) := by
  have hν_one : 1 ≤ ν := by
    omega
  have hν_ne : ν ≠ 0 := Nat.ne_of_gt hν_one
  have hcenter_differentiable : Differentiable ℝ
      (LocalCutoff.CenterProjection.map χ ρ L N ζ) := by
    apply (h_center_smooth ζ).differentiable
    exact Nat.cast_ne_zero.mpr hν_ne
  have hinverse : LipschitzWith lower⁻¹
      (LocalCutoff.CenterProjection.inverse χ ρ L N ζ) := by
    rw [LocalCutoff.CenterProjection.inverse_def]
    exact Real.lipschitzWith_invFun_of_pos_le_deriv
      hcenter_differentiable h_lower_pos (h_lower ζ)
  apply LipschitzWith.of_dist_le_mul
  intro ubar vbar
  let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ubar
  let v := LocalCutoff.CenterProjection.inverse χ ρ L N ζ vbar
  have hraw_u : raw χ ρ L N ζ ubar =
      L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2 := by
    rw [raw_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (ζ u) + (χ (ρ⁻¹ • (u, ζ u)) • N (u, ζ u)).2 =
      L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2
    rw [LocalCutoff.remainder_apply]
  have hraw_v : raw χ ρ L N ζ vbar =
      L (ζ v) + (LocalCutoff.remainder χ ρ N (v, ζ v)).2 := by
    rw [raw_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (ζ v) + (χ (ρ⁻¹ • (v, ζ v)) • N (v, ζ v)).2 =
      L (ζ v) + (LocalCutoff.remainder χ ρ N (v, ζ v)).2
    rw [LocalCutoff.remainder_apply]
  have hinverse_dist : |u - v| ≤ (lower⁻¹ : ℝ) * |ubar - vbar| := by
    simpa only [u, v, Real.dist_eq, NNReal.coe_inv] using hinverse.dist_le_mul ubar vbar
  have hgraph_dist : ‖ζ u - ζ v‖ ≤ (slope : ℝ) * |u - v| := by
    simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using
      (SmallLipschitzGraph.lipschitzWith ζ).dist_le_mul u v
  have hlinear : ‖L (ζ u) - L (ζ v)‖ ≤
      (linearRate : ℝ) * ‖ζ u - ζ v‖ := by
    calc
      ‖L (ζ u) - L (ζ v)‖ = ‖L (ζ u - ζ v)‖ := by rw [map_sub]
      _ ≤ ‖L‖ * ‖ζ u - ζ v‖ := L.le_opNorm _
      _ ≤ (linearRate : ℝ) * ‖ζ u - ζ v‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  have hstable := h_stable_lipschitz u v (ζ u) (ζ v)
  have hcoefficient_nonneg :
      0 ≤ (linearRate : ℝ) + (stableFiber : ℝ) := by
    positivity
  have hscaled_graph :
      ((linearRate : ℝ) + (stableFiber : ℝ)) * ‖ζ u - ζ v‖ ≤
        ((linearRate : ℝ) + (stableFiber : ℝ)) * ((slope : ℝ) * |u - v|) :=
    mul_le_mul_of_nonneg_left hgraph_dist hcoefficient_nonneg
  have hinverse_coefficient_nonneg :
      0 ≤ (stableCenter : ℝ) +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ) := by
    positivity
  have hslope_real :
      ((stableCenter : ℝ) + ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) *
          (lower⁻¹ : ℝ) ≤ (slope : ℝ) := by
    exact_mod_cast h_slope
  rw [dist_eq_norm, hraw_u, hraw_v]
  calc
    ‖(L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2) -
        (L (ζ v) + (LocalCutoff.remainder χ ρ N (v, ζ v)).2)‖ ≤
        ‖L (ζ u) - L (ζ v)‖ +
          ‖(LocalCutoff.remainder χ ρ N (u, ζ u)).2 -
            (LocalCutoff.remainder χ ρ N (v, ζ v)).2‖ := by
      rw [add_sub_add_comm]
      exact norm_add_le _ _
    _ ≤ (linearRate : ℝ) * ‖ζ u - ζ v‖ +
        ((stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖ζ u - ζ v‖) :=
      add_le_add hlinear hstable
    _ = (stableCenter : ℝ) * |u - v| +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * ‖ζ u - ζ v‖ := by
      ring
    _ ≤ (stableCenter : ℝ) * |u - v| +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * ((slope : ℝ) * |u - v|) :=
      add_le_add_right hscaled_graph _
    _ = ((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) * |u - v| := by
      ring
    _ ≤ ((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) *
          ((lower⁻¹ : ℝ) * |ubar - vbar|) :=
      mul_le_mul_of_nonneg_left hinverse_dist hinverse_coefficient_nonneg
    _ = (((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) *
          (lower⁻¹ : ℝ)) * |ubar - vbar| := by
      ring
    _ ≤ (slope : ℝ) * |ubar - vbar| :=
      mul_le_mul_of_nonneg_right hslope_real (abs_nonneg _)
    _ = (slope : ℝ) * dist ubar vbar := by
      rw [Real.dist_eq]

/-- The inverse-center graph-transform formula is continuous under the quantitative
Lipschitz hypotheses. -/
theorem raw_continuous (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower linearRate stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) :
    Continuous (raw χ ρ L N ζ) := by
  exact (raw_lipschitzWith ν χ ρ L N lower linearRate stableCenter stableFiber hν
    h_center_smooth h_lower_pos h_lower hL h_stable_lipschitz h_slope ζ).continuous

/-- If the nonlinear term fixes the origin, then the raw graph transform fixes the
origin. -/
theorem raw_zero (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (ζ : SmallLipschitzGraph X radius slope) :
    raw χ ρ L N ζ 0 = 0 := by
  have hν_one : 1 ≤ ν := by
    omega
  have hν_ne : ν ≠ 0 := Nat.ne_of_gt hν_one
  have hcenter_differentiable : Differentiable ℝ
      (LocalCutoff.CenterProjection.map χ ρ L N ζ) := by
    apply (h_center_smooth ζ).differentiable
    exact Nat.cast_ne_zero.mpr hν_ne
  have hbijective : Function.Bijective
      (LocalCutoff.CenterProjection.map χ ρ L N ζ) :=
    Real.bijective_of_pos_le_deriv
      hcenter_differentiable h_lower_pos (h_lower ζ)
  have hmap_zero : LocalCutoff.CenterProjection.map χ ρ L N ζ 0 = 0 := by
    rw [LocalCutoff.CenterProjection.map_apply, SmallLipschitzGraph.zero_apply]
    change (LocalCutoff.centerStableLinearize χ ρ L N (0 : ℝ × X)).1 = 0
    rw [LocalCutoff.centerStableLinearize_apply, hN_zero, smul_zero, add_zero, map_zero]
    rfl
  have hinverse_zero : LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0 = 0 := by
    apply hbijective.1
    rw [hmap_zero, LocalCutoff.CenterProjection.inverse_def]
    exact Function.rightInverse_invFun hbijective.2 0
  have hraw : raw χ ρ L N ζ 0 =
      L (ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0)) +
        (LocalCutoff.remainder χ ρ N
          (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0,
            ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0))).2 := by
    rw [raw_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0)) +
        (χ (ρ⁻¹ • (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0,
          ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0))) •
            N (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0,
              ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0))).2 =
      L (ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0)) +
        (LocalCutoff.remainder χ ρ N
          (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0,
            ζ (LocalCutoff.CenterProjection.inverse χ ρ L N ζ 0))).2
    rw [LocalCutoff.remainder_apply]
  rw [hraw, hinverse_zero]
  rw [SmallLipschitzGraph.zero_apply]
  change L 0 + (LocalCutoff.remainder χ ρ N (0 : ℝ × X)).2 = 0
  rw [map_zero, zero_add, LocalCutoff.remainder_apply, hN_zero, smul_zero]
  rfl

/-- The stable block bound, the stable remainder bound, and the radius inequality give
the pointwise radius estimate for the raw graph transform. -/
theorem raw_norm_le (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (linearRate stableBound : ℝ≥0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (ζ : SmallLipschitzGraph X radius slope) (ū : ℝ) :
    ‖raw χ ρ L N ζ ū‖ ≤ (radius : ℝ) := by
  let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū
  have hraw : raw χ ρ L N ζ ū =
      L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2 := by
    rw [raw_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (ζ u) + (χ (ρ⁻¹ • (u, ζ u)) • N (u, ζ u)).2 =
      L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2
    rw [LocalCutoff.remainder_apply]
  have hgraph_norm : ‖ζ u‖ ≤ (radius : ℝ) :=
    (BoundedContinuousFunction.norm_coe_le_norm
      (ζ : BoundedContinuousFunction ℝ X) u).trans (SmallLipschitzGraph.norm_le ζ)
  have hlinear : ‖L (ζ u)‖ ≤ (linearRate : ℝ) * (radius : ℝ) := by
    calc
      ‖L (ζ u)‖ ≤ ‖L‖ * ‖ζ u‖ := L.le_opNorm _
      _ ≤ (linearRate : ℝ) * (radius : ℝ) :=
        mul_le_mul hL hgraph_norm (norm_nonneg _) linearRate.coe_nonneg
  have hradius_real :
      (linearRate : ℝ) * (radius : ℝ) + (stableBound : ℝ) ≤ (radius : ℝ) := by
    exact_mod_cast h_radius
  rw [hraw]
  calc
    ‖L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2‖ ≤
        ‖L (ζ u)‖ + ‖(LocalCutoff.remainder χ ρ N (u, ζ u)).2‖ := norm_add_le _ _
    _ ≤ (linearRate : ℝ) * (radius : ℝ) + (stableBound : ℝ) :=
      add_le_add hlinear (h_stable_bound (u, ζ u))
    _ ≤ (radius : ℝ) := hradius_real

/-- The raw graph transform, bundled as a bounded continuous function. -/
noncomputable def toBoundedContinuousFunction (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) : BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup (raw χ ρ L N ζ)
    (raw_continuous ν χ ρ L N lower linearRate stableCenter stableFiber hν h_center_smooth
      h_lower_pos h_lower hL h_stable_lipschitz h_slope ζ)
    (radius : ℝ) (raw_norm_le χ ρ L N linearRate stableBound hL h_stable_bound h_radius ζ)

/-- The bounded continuous graph transform evaluates to the raw graph-transform
formula. -/
theorem toBoundedContinuousFunction_apply (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) (ū : ℝ) :
    toBoundedContinuousFunction ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hL h_stable_bound h_stable_lipschitz h_radius
      h_slope ζ ū = raw χ ρ L N ζ ū := by
  rfl

/-- The bounded continuous graph transform has norm at most the cone radius. -/
theorem toBoundedContinuousFunction_norm_le (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ)
    (L : X →L[ℝ] X) (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) :
    ‖toBoundedContinuousFunction ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hL h_stable_bound h_stable_lipschitz h_radius
      h_slope ζ‖ ≤ (radius : ℝ) := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (raw_continuous ν χ ρ L N lower linearRate stableCenter stableFiber hν h_center_smooth
      h_lower_pos h_lower hL h_stable_lipschitz h_slope ζ)
    radius.coe_nonneg (raw_norm_le χ ρ L N linearRate stableBound hL h_stable_bound h_radius ζ)

/-- The inverse-center formula defines a self-map of the cone of bounded Lipschitz
graphs. -/
noncomputable def map (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower linearRate stableBound stableCenter stableFiber : ℝ≥0)
    (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) : SmallLipschitzGraph X radius slope :=
  SmallLipschitzGraph.of
    (toBoundedContinuousFunction ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hL h_stable_bound h_stable_lipschitz h_radius
      h_slope ζ)
    (raw_zero ν χ ρ L N lower hν h_center_smooth h_lower_pos h_lower hN_zero ζ)
    (toBoundedContinuousFunction_norm_le ν χ ρ L N lower linearRate stableBound stableCenter
      stableFiber hν h_center_smooth h_lower_pos h_lower hL h_stable_bound
      h_stable_lipschitz h_radius h_slope ζ)
    (raw_lipschitzWith ν χ ρ L N lower linearRate stableCenter stableFiber hν h_center_smooth
      h_lower_pos h_lower hL h_stable_lipschitz h_slope ζ)

/-- The cone-valued graph transform evaluates to the inverse-center pointwise formula. -/
theorem map_apply (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower linearRate stableBound stableCenter stableFiber : ℝ≥0)
    (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) (ū : ℝ) :
    let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū
    map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν h_center_smooth
      h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz h_radius h_slope ζ ū =
        (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).2 := by
  rw [map, SmallLipschitzGraph.coe_of,
    toBoundedContinuousFunction_apply, raw_apply]

/-- The cone-valued graph transform satisfies the origin, radius, and Lipschitz
constraints. -/
theorem map_spec (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (lower linearRate stableBound stableCenter stableFiber : ℝ≥0)
    (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ : SmallLipschitzGraph X radius slope) :
    let T := map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
      h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz
      h_radius h_slope ζ
    T 0 = 0 ∧ ‖(T : BoundedContinuousFunction ℝ X)‖ ≤ (radius : ℝ) ∧
      LipschitzWith slope T := by
  exact SmallLipschitzGraph.spec _

/-- The center coordinates of two graph transforms differ by the center-fiber
estimate when their graph values are evaluated at one common parameter. -/
private theorem centerProjection_dist_apply_le_of_center_fiber
    (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (centerFiber : ℝ≥0)
    (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
      |(LocalCutoff.remainder χ ρ N (u, z)).1 -
          (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
        (centerFiber : ℝ) * ‖z - w‖)
    (ζ η : SmallLipschitzGraph X radius slope) (u : ℝ) :
    dist (LocalCutoff.CenterProjection.map χ ρ L N ζ u)
      (LocalCutoff.CenterProjection.map χ ρ L N η u) ≤
      (centerFiber : ℝ) * dist ζ η := by
  rw [LocalCutoff.CenterProjection.map_apply,
    LocalCutoff.CenterProjection.map_apply,
    LocalCutoff.centerStableLinearize_apply,
    LocalCutoff.centerStableLinearize_apply,
    LocalCutoff.centerStable_apply,
    LocalCutoff.centerStable_apply]
  have hgraph : ‖ζ u - η u‖ ≤ dist ζ η := by
    simpa only [dist_eq_norm] using SmallLipschitzGraph.dist_apply_le ζ η u
  have hfiber := h_center_fiber u (ζ u) (η u)
  have hscaled :
      (centerFiber : ℝ) * ‖ζ u - η u‖ ≤ (centerFiber : ℝ) * dist ζ η :=
    mul_le_mul_of_nonneg_left hgraph centerFiber.coe_nonneg
  simpa [LocalCutoff.remainder_apply, Real.dist_eq, Real.norm_eq_abs,
    sub_eq_add_neg, add_sub_add_comm] using hfiber.trans hscaled

/-- The stable output estimate for two graph transforms, assuming the inverse
center parameters already satisfy the quantitative distance bound. -/
private theorem map_dist_apply_le_of_inverse_dist
    (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0)
    (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ))
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (ζ η : SmallLipschitzGraph X radius slope) (ū : ℝ)
    (h_inverse :
      |LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū -
          LocalCutoff.CenterProjection.inverse χ ρ L N η ū| ≤
        (lower⁻¹ : ℝ) * (centerFiber : ℝ) * dist ζ η) :
    dist
        (map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
          h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
          h_stable_lipschitz h_radius h_slope ζ ū)
        (map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
          h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
          h_stable_lipschitz h_radius h_slope η ū) ≤
      (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) * dist ζ η := by
  let u := LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū
  let v := LocalCutoff.CenterProjection.inverse χ ρ L N η ū
  have hmapζ :
      map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
          h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
          h_stable_lipschitz h_radius h_slope ζ ū =
        L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2 := by
    rw [map_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (ζ u) + (χ (ρ⁻¹ • (u, ζ u)) • N (u, ζ u)).2 =
      L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2
    rw [LocalCutoff.remainder_apply]
  have hmapη :
      map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
          h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
          h_stable_lipschitz h_radius h_slope η ū =
        L (η v) + (LocalCutoff.remainder χ ρ N (v, η v)).2 := by
    rw [map_apply, LocalCutoff.centerStableLinearize_apply,
      LocalCutoff.centerStable_apply]
    change L (η v) + (χ (ρ⁻¹ • (v, η v)) • N (v, η v)).2 =
      L (η v) + (LocalCutoff.remainder χ ρ N (v, η v)).2
    rw [LocalCutoff.remainder_apply]
  have hgraph_cross : ‖ζ u - η v‖ ≤
      (slope : ℝ) * |u - v| + dist ζ η := by
    calc
      ‖ζ u - η v‖ ≤ ‖ζ u - ζ v‖ + ‖ζ v - η v‖ := by
        have hdecomp : ζ u - η v = (ζ u - ζ v) + (ζ v - η v) := by
          abel
        rw [hdecomp]
        exact norm_add_le _ _
      _ ≤ (slope : ℝ) * |u - v| + dist ζ η := by
        have hζ := (SmallLipschitzGraph.lipschitzWith ζ).dist_le_mul u v
        have hη := SmallLipschitzGraph.dist_apply_le ζ η v
        simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using
          add_le_add hζ hη
  have hlinear : ‖L (ζ u) - L (η v)‖ ≤
      (linearRate : ℝ) * ‖ζ u - η v‖ := by
    calc
      ‖L (ζ u) - L (η v)‖ = ‖L (ζ u - η v)‖ := by rw [map_sub]
      _ ≤ ‖L‖ * ‖ζ u - η v‖ := L.le_opNorm _
      _ ≤ (linearRate : ℝ) * ‖ζ u - η v‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  have hstable := h_stable_lipschitz u v (ζ u) (η v)
  have hcoef_nonneg :
      0 ≤ (linearRate : ℝ) + (stableFiber : ℝ) := by positivity
  have hcross_scaled :
      ((linearRate : ℝ) + (stableFiber : ℝ)) * ‖ζ u - η v‖ ≤
        ((linearRate : ℝ) + (stableFiber : ℝ)) *
          ((slope : ℝ) * |u - v| + dist ζ η) :=
    mul_le_mul_of_nonneg_left hgraph_cross hcoef_nonneg
  have hcoef_center_nonneg :
      0 ≤ (stableCenter : ℝ) +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ) := by positivity
  have hlower_inv_nonneg : 0 ≤ (lower⁻¹ : ℝ) := by positivity
  have hrate_real :
      ((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) *
          (lower⁻¹ : ℝ) ≤ (slope : ℝ) := by
    exact_mod_cast h_slope
  rw [hmapζ, hmapη, dist_eq_norm]
  calc
    ‖(L (ζ u) + (LocalCutoff.remainder χ ρ N (u, ζ u)).2) -
        (L (η v) + (LocalCutoff.remainder χ ρ N (v, η v)).2)‖ ≤
        ‖L (ζ u) - L (η v)‖ +
          ‖(LocalCutoff.remainder χ ρ N (u, ζ u)).2 -
            (LocalCutoff.remainder χ ρ N (v, η v)).2‖ := by
      rw [add_sub_add_comm]
      exact norm_add_le _ _
    _ ≤ (linearRate : ℝ) * ‖ζ u - η v‖ +
        ((stableCenter : ℝ) * |u - v| +
          (stableFiber : ℝ) * ‖ζ u - η v‖) :=
      add_le_add hlinear hstable
    _ = (stableCenter : ℝ) * |u - v| +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * ‖ζ u - η v‖ := by ring
    _ ≤ (stableCenter : ℝ) * |u - v| +
        ((linearRate : ℝ) + (stableFiber : ℝ)) *
          ((slope : ℝ) * |u - v| + dist ζ η) :=
      add_le_add_right hcross_scaled _
    _ = ((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) * |u - v| +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * dist ζ η := by ring
    _ ≤ ((stableCenter : ℝ) +
          ((linearRate : ℝ) + (stableFiber : ℝ)) * (slope : ℝ)) *
          ((lower⁻¹ : ℝ) * (centerFiber : ℝ) * dist ζ η) +
        ((linearRate : ℝ) + (stableFiber : ℝ)) * dist ζ η := by
      gcongr
    _ = (rate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) *
        dist ζ η := by
      rw [rate_def]
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_inv]
      ring

/-- Under the center-fiber estimate and strict rate inequality, the graph transform is a
strict contraction of the cone of bounded Lipschitz graphs. -/
theorem contractingWith (ν : ℕ) (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X)
    (lower linearRate stableBound stableCenter stableFiber centerFiber : ℝ≥0) (hν : 2 ≤ ν)
    (h_center_smooth : ∀ ζ : SmallLipschitzGraph X radius slope,
      ContDiff ℝ ν (LocalCutoff.CenterProjection.map χ ρ L N ζ))
    (h_lower_pos : 0 < lower)
    (h_lower : ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      (lower : ℝ) ≤ deriv (LocalCutoff.CenterProjection.map χ ρ L N ζ) u)
    (hN_zero : N 0 = 0) (hL : ‖L‖ ≤ (linearRate : ℝ)) (h_linearRate : linearRate < 1)
    (h_stable_bound : ∀ p : ℝ × X,
      ‖(LocalCutoff.remainder χ ρ N p).2‖ ≤ (stableBound : ℝ))
    (h_stable_lipschitz : ∀ u v : ℝ, ∀ z w : X,
      ‖(LocalCutoff.remainder χ ρ N (u, z)).2 -
          (LocalCutoff.remainder χ ρ N (v, w)).2‖ ≤
        (stableCenter : ℝ) * |u - v| + (stableFiber : ℝ) * ‖z - w‖)
    (h_center_fiber : ∀ u : ℝ, ∀ z w : X,
      |(LocalCutoff.remainder χ ρ N (u, z)).1 -
          (LocalCutoff.remainder χ ρ N (u, w)).1| ≤
        (centerFiber : ℝ) * ‖z - w‖)
    (h_radius : linearRate * radius + stableBound ≤ radius)
    (h_slope : (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ ≤ slope)
    (h_rate : rate lower linearRate stableCenter stableFiber centerFiber slope < 1) :
    ContractingWith (rate lower linearRate stableCenter stableFiber centerFiber slope)
      (map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν h_center_smooth
        h_lower_pos h_lower hN_zero hL h_stable_bound h_stable_lipschitz h_radius h_slope) := by
  have hν_one : 1 ≤ ν := by omega
  have hν_ne : ν ≠ 0 := Nat.ne_of_gt hν_one
  have hdiff : ∀ ζ : SmallLipschitzGraph X radius slope,
      Differentiable ℝ (LocalCutoff.CenterProjection.map χ ρ L N ζ) := by
    intro ζ
    apply (h_center_smooth ζ).differentiable
    exact Nat.cast_ne_zero.mpr hν_ne
  have hright : ∀ ζ : SmallLipschitzGraph X radius slope,
      Function.RightInverse (LocalCutoff.CenterProjection.inverse χ ρ L N ζ)
        (LocalCutoff.CenterProjection.map χ ρ L N ζ) := by
    intro ζ
    rw [LocalCutoff.CenterProjection.inverse_def]
    exact Function.rightInverse_invFun
      (Real.surjective_of_pos_le_deriv (hdiff ζ) h_lower_pos (h_lower ζ))
  have hcenter_bound (ζ η : SmallLipschitzGraph X radius slope) (u : ℝ) :
      dist (LocalCutoff.CenterProjection.map χ ρ L N ζ u)
          (LocalCutoff.CenterProjection.map χ ρ L N η u) ≤
        (centerFiber : ℝ) * dist ζ η :=
    centerProjection_dist_apply_le_of_center_fiber χ ρ L N centerFiber
      h_center_fiber ζ η u
  refine SmallLipschitzGraph.contractingWith_of_dist_apply_le_mul h_rate ?_
  intro ζ η ū
  have hinverse_raw :=
    AntilipschitzWith.dist_rightInverse_rightInverse_le
      (Real.antilipschitzWith_inv_of_pos_le_deriv (hdiff ζ) h_lower_pos (h_lower ζ))
      (hright ζ) (hright η) (hcenter_bound ζ η) ū
  have hinverse :
      |LocalCutoff.CenterProjection.inverse χ ρ L N ζ ū -
          LocalCutoff.CenterProjection.inverse χ ρ L N η ū| ≤
        (lower⁻¹ : ℝ) * (centerFiber : ℝ) * dist ζ η := by
    simpa only [Real.dist_eq, NNReal.coe_inv, NNReal.coe_mul, mul_assoc] using hinverse_raw
  exact map_dist_apply_le_of_inverse_dist ν χ ρ L N lower linearRate stableBound
    stableCenter stableFiber centerFiber hν h_center_smooth h_lower_pos h_lower hN_zero hL
    h_stable_bound h_stable_lipschitz h_radius h_slope ζ η ū hinverse

end LocalCutoff.GraphTransform
