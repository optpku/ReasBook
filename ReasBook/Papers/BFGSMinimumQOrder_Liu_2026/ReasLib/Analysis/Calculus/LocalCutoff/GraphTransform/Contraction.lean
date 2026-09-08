module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphTransform

public section

open scoped NNReal

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-- The center coordinate maps of two small graphs differ by the center-fiber bound
when their graph values are compared at the same parameter. -/
theorem centerProjection_dist_apply_le_of_center_fiber
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

/-- The stable output of the graph transform satisfies the quantitative distance estimate
once the two inverse center parameters have a uniform distance bound. -/
theorem map_dist_apply_le_of_inverse_dist
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

/-- The graph transform is a strict contraction when the center-fiber estimate controls
the inverse center parameters. -/
theorem contractingWith_of_center_fiber
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
    (_h_linearRate : linearRate < 1)
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
      (map ν χ ρ L N lower linearRate stableBound stableCenter stableFiber hν
        h_center_smooth h_lower_pos h_lower hN_zero hL h_stable_bound
        h_stable_lipschitz h_radius h_slope) := by
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
