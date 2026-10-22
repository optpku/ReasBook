/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Set AffineMap
open scoped Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 3.2.3 lies in the real normed-space strong-convexity / one-sided directional-derivative
domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `strongConvexOn_iff_convex`
- mathlib `ConvexOn.rightDeriv_le_slope_of_mem_interior`
- chapter `StrongConvexOnWith.lower_tangent_quadratic` in `Chap02/Definition_2_14`

Best owner abstraction:
- `StrongConvexOn Q μ f`

Primitive data:
- the ambient real normed space `E`
- the feasible set `Q`, modulus `μ`, objective `f`, and points `x`, `y`

Derived API:
- the affine line slice `t ↦ f (x + t • (y - x))`
- the induced one-dimensional strong-convexity owner on `((lineMap x y) ⁻¹' Q)`
- the quadratic-corrected convex slice on `((lineMap x y) ⁻¹' Q)`, derived through
  `strongConvexOn_iff_convex`
- the lower-support estimate at the right derivative `derivWithin ... (Set.Ici 0) 0`

Source/core/bridge triage:
- source-facing: Lemma 3.2.3, the interior-point quadratic lower-support estimate
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: the affine line map `lineMap x y : ℝ →ᵃ[ℝ] E`

The source statement is kept, but its owner is the intrinsic theorem of `StrongConvexOn` on an
arbitrary real normed space; the line slice is only the bridge used to apply the canonical
one-variable convex-derivative theorem.
-/

namespace StrongConvexOn

/-- Lemma 3.2.3: if `f` is `μ`-strongly convex on `Q`, then every interior point `x` of `Q`
supports the quadratic lower bound
`f y ≥ f x + f'(x; y - x) + (μ / 2) * ‖x - y‖^2`
at every `y ∈ Q`, where `f'(x; y - x)` is the one-sided directional derivative of the line
restriction `t ↦ f (x + t • (y - x))` at `t = 0`. -/
-- Proof sketch: restrict `f` to the affine line from `x` to `y`, subtract the quadratic term
-- `((μ / 2) * ‖y - x‖²) t²`, identify the sliced function as one-dimensional strongly convex, and
-- recover convexity of the corrected slice from `strongConvexOn_iff_convex`. The one-variable
-- theorem
-- `ConvexOn.rightDeriv_le_slope_of_mem_interior` applied at `0` then bounds the right derivative
-- by the secant slope at `1`, and the quadratic correction contributes exactly
-- `(μ / 2) * ‖x - y‖²`.
theorem lower_tangent_derivWithin_of_mem_interior
    {Q : Set E} {μ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Q μ f)
    {x y : E} (hx : x ∈ interior Q) (hy : y ∈ Q) :
    f y ≥
      f x +
        derivWithin (fun t : ℝ ↦ f (x + t • (y - x))) (Set.Ici (0 : ℝ)) 0 +
        (μ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  let γ : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap x y
  let S : Set ℝ := γ ⁻¹' Q
  let m : ℝ := μ * ‖y - x‖ ^ (2 : ℕ)
  let g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  let h : ℝ → ℝ := fun t ↦ g t - (m / 2) * t ^ (2 : ℕ)
  have hγ_apply (t : ℝ) : γ t = x + t • (y - x) := by
    change (AffineMap.lineMap x y) t = x + t • (y - x)
    rw [lineMap_apply_module']
    simp [add_comm]
  have hnorm {u v : ℝ} :
      ‖γ u - γ v‖ ^ (2 : ℕ) = ‖u - v‖ ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
    change ‖(AffineMap.lineMap x y) u - (AffineMap.lineMap x y) v‖ ^ (2 : ℕ) =
      ‖u - v‖ ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ)
    rw [← dist_eq_norm, dist_lineMap_lineMap, Real.dist_eq, dist_eq_norm, mul_pow, sq_abs]
    rw [show (u - v) ^ (2 : ℕ) = ‖u - v‖ ^ (2 : ℕ) by
      rw [Real.norm_eq_abs, sq_abs]]
    rw [show ‖x - y‖ ^ (2 : ℕ) = ‖y - x‖ ^ (2 : ℕ) by
      simpa using congrArg (fun r : ℝ ↦ r ^ (2 : ℕ)) (norm_sub_rev x y)]
  have hg_strong : StrongConvexOn S m g := by
    refine ⟨hf.1.affine_preimage γ.toAffineMap, ?_⟩
    intro u hu v hv a b ha hb hab
    have hstrong := hf.2 hu hv ha hb hab
    change
      f (a • γ.toAffineMap u + b • γ.toAffineMap v) ≤
        a • f (γ.toAffineMap u) + b • f (γ.toAffineMap v) -
          a * b * ((μ / 2) * ‖γ.toAffineMap u - γ.toAffineMap v‖ ^ (2 : ℕ)) at hstrong
    rw [← Convex.combo_affine_apply hab] at hstrong
    change
      f (γ (a • u + b • v)) ≤
        a • f (γ u) + b • f (γ v) - a * b * ((μ / 2) * ‖γ u - γ v‖ ^ (2 : ℕ)) at hstrong
    have hstrong' :
        f (γ (a • u + b • v)) ≤
          a • f (γ u) + b • f (γ v) - a * b * ((m / 2) * ‖u - v‖ ^ (2 : ℕ)) := by
      rw [hnorm] at hstrong
      dsimp [m] at hstrong ⊢
      ring_nf at hstrong ⊢
      simpa [smul_eq_mul] using hstrong
    simpa [g, hγ_apply] using hstrong'
  have hconv : ConvexOn ℝ S h := by
    simpa [h, g, m, Real.norm_eq_abs, sq_abs, mul_assoc, mul_left_comm, mul_comm] using
      (strongConvexOn_iff_convex.mp hg_strong)
  have h0 : (0 : ℝ) ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have hxQ : Q ∈ 𝓝 (γ (0 : ℝ)) := by
      simpa [hγ_apply] using (mem_interior_iff_mem_nhds.mp hx)
    simpa [S] using γ.continuous.continuousAt.preimage_mem_nhds hxQ
  have h1 : (1 : ℝ) ∈ S := by
    simpa [S, hγ_apply] using hy
  have hderiv_h_le : derivWithin h (Set.Ioi (0 : ℝ)) 0 ≤ slope h 0 1 :=
    hconv.rightDeriv_le_slope_of_mem_interior h0 h1 zero_lt_one
  have hq' : HasDerivWithinAt (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) (0 : ℝ) (Set.Ioi (0 : ℝ)) 0 := by
    have hq : HasDerivAt (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) 0 0 := by
      simpa [pow_two] using ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (m / 2)
    exact hq.hasDerivWithinAt
  have hh : DifferentiableWithinAt ℝ h (Set.Ioi (0 : ℝ)) 0 :=
    hconv.differentiableWithinAt_Ioi_of_mem_interior h0
  have hq : DifferentiableWithinAt ℝ (fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) (Set.Ioi (0 : ℝ)) 0 :=
    hq'.differentiableWithinAt
  have hderiv_g_eq_h : derivWithin g (Set.Ioi (0 : ℝ)) 0 = derivWithin h (Set.Ioi (0 : ℝ)) 0 := by
    have hadd := derivWithin_add hq hh
    rw [hq'.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))] at hadd
    have hsumfun : ((fun t : ℝ ↦ (m / 2) * t ^ (2 : ℕ)) + h) = g := by
      funext t
      simp [h, g]
    rw [hsumfun] at hadd
    simpa using hadd
  have hslope : slope h 0 1 = f y - f x - m / 2 := by
    simp [h, g, slope_def_field]
    ring
  have hmain :
      derivWithin (fun t : ℝ ↦ f (x + t • (y - x))) (Set.Ici (0 : ℝ)) 0 ≤
        f y - f x - m / 2 := by
    calc
      derivWithin g (Set.Ici (0 : ℝ)) 0 = derivWithin g (Set.Ioi (0 : ℝ)) 0 := by
        symm
        simpa using derivWithin_Ioi_eq_Ici g (0 : ℝ)
      _ = derivWithin h (Set.Ioi (0 : ℝ)) 0 := hderiv_g_eq_h
      _ ≤ slope h 0 1 := hderiv_h_le
      _ = f y - f x - m / 2 := hslope
  have hm : m / 2 = (μ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    dsimp [m]
    rw [show ‖y - x‖ ^ (2 : ℕ) = ‖x - y‖ ^ (2 : ℕ) by
      simpa using congrArg (fun r : ℝ ↦ r ^ (2 : ℕ)) (norm_sub_rev y x)]
    ring
  linarith [hmain, hm]

end StrongConvexOn
