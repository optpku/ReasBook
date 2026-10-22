/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open ConditionalGradientContraction

/- Proposition 6.39 lies in the convex first-order upper-model / Hölder-gradient domain.

Sampled owner-style declarations:
- chapter `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the Chapter 6
  owner predicate for Hölder-continuous chosen within-derivative fields on the feasible set;
- chapter
  `ConditionalGradientContraction.weighted_objective_le_estimatingFunction_add_contractionError`,
  a downstream consumer that already uses that owner directly;
- chapter `HasHolderLowerModelAt` in `Proposition_6_42`, the companion source-facing lower-model
  predicate built from the same Hölder remainder scale;
- mathlib `ConvexOn`, the canonical convexity owner on a feasible set.

Best owner abstraction:
- source-facing: Proposition 6.39's first-order upper model on a convex feasible set;
- core/canonical: `ConditionalGradientContraction.HolderGradientOn`;
- bridge/view: the upper-model consequence below, obtained from the owner plus convexity of the
  feasible set, stated with the same chosen dual field as the owner.

Primitive data:
- the feasible set `Q`, objective `f`, chosen dual field `g`, Hölder exponent `v`, and Hölder
  constant `Gv`;
- convexity of `Q`;
- the owner hypothesis `HolderGradientOn v Gv Q f g`.

Derived API:
- the upper-model inequality below.

The previous file added local projection lemmas for the conjunction-based owner and then exposed
the proposition through a `ConvexOn`-branded theorem surface. This refinement keeps the
source-facing upper-model statement but moves it to the owner namespace, uses only the convexity
of the feasible set needed to keep the segment in `Q`, removes the redundant `v ≤ 1` guard from
the public API, and now matches the repaired owner exactly by expressing both the hypothesis and
the linearization term through the same chosen dual first-order field `g`.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ConditionalGradientContraction.HolderGradientOn

/-- Helper for Proposition 6.39: points on the line segment between two feasible points stay in
the convex feasible set. -/
lemma lineMap_mem_feasible
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ Q := by
  -- Convexity keeps the whole segment between feasible endpoints inside `Q`.
  exact hQ_convex.lineMap_mem hx hy ht

/-- Helper for Proposition 6.39: the linearization remainder along the segment from `x` to `y`
is exactly the integral of the derivative-field remainder. -/
lemma increment_eq_linearization_add_integral_remainder
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q) (hv : 0 < (v : ℝ))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y =
      f x + g x (y - x) +
        ∫ t : ℝ in 0..1, (g (AffineMap.lineMap x y t) - g x) (y - x) := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let remainder : ℝ → ℝ := fun t ↦ (g (seg t) - g x) (y - x)
  let ψ : ℝ → ℝ := fun t ↦ f (seg t) - t * g x (y - x)
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact lineMap_mem_feasible hQ_convex hx hy ht
  have hseg_deriv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ f (seg s)) (g (seg t) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Compose the within-derivative of `f` on `Q` with the segment parametrization.
    simpa [seg] using
      (hf.hasFDerivWithinAt (hseg ht)).comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hseg
  have hseg_cont : ContinuousOn (fun t ↦ f (seg t)) (Set.Icc (0 : ℝ) 1) := by
    -- The segment restriction of `f` is continuous because it is differentiable on `[0, 1]`.
    refine fun t ht ↦ (hseg_deriv t ht).continuousWithinAt
  have hg_cont : ContinuousOn g Q := hf.holderOn.continuousOn hv
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    -- Continuity of the derivative field turns the remainder integrand
    -- into a continuous scalar map.
    have hgrad_cont : ContinuousOn (fun t ↦ g (seg t)) (Set.Icc (0 : ℝ) 1) :=
      hg_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
    have hsub_cont : ContinuousOn (fun t ↦ g (seg t) - g x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    simpa [remainder] using
      hsub_cont.clm_apply
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    -- The auxiliary one-variable function is continuous on the whole unit interval.
    have hlin_cont : ContinuousOn (fun t : ℝ ↦ t * g x (y - x)) (Set.Icc (0 : ℝ) 1) :=
      (continuous_id'.mul continuous_const).continuousOn
    simpa [ψ] using hseg_cont.sub hlin_cont
  have hψ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt ψ (remainder t) (Set.Ioi t) t := by
    intro t ht
    -- Route correction: work with right derivatives on `(t, +∞)` so the interval FTC applies
    -- directly on `[0, 1]` without needing an ambient derivative outside the feasible segment.
    have hseg_deriv_right :
        HasDerivWithinAt (fun s ↦ f (seg s)) (g (seg t) (y - x)) (Set.Ioi t) t :=
      (hseg_deriv t (Set.mem_Icc_of_Ioo ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGT ht.2)
          (by
            intro s hs
            exact ⟨ht.1.le.trans hs.1, hs.2⟩))
    have hlin_deriv :
        HasDerivWithinAt (fun s : ℝ ↦ s * g x (y - x)) (g x (y - x)) (Set.Ioi t) t := by
      simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (g x (y - x))).hasDerivWithinAt
    simpa [ψ, remainder, sub_eq_add_neg, sub_mul] using hseg_deriv_right.sub hlin_deriv
  have hftc :
      ∫ t : ℝ in 0..1, remainder t = ψ 1 - ψ 0 := by
    -- Apply the one-dimensional fundamental theorem of calculus to the remainder function.
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      zero_le_one hψ_cont hψ_deriv hremainder_int
  have hftc' :
      ∫ t : ℝ in 0..1, remainder t = f y - f x - g x (y - x) := by
    simpa [ψ, remainder, seg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hftc
  linarith

/-- Helper for Proposition 6.39: the segment remainder is pointwise bounded by the Hölder
kernel `Gᵥ t^v ‖y - x‖^(1 + v)`. -/
lemma segment_remainder_abs_le_holder_kernel
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |((g (AffineMap.lineMap x y t) - g x) (y - x) : ℝ)| ≤
      (Gv : ℝ) * Real.rpow t (v : ℝ) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
  let d : E := y - x
  have ht_nonneg : 0 ≤ t := ht.1
  have hv_nonneg : 0 ≤ (v : ℝ) := by
    exact_mod_cast v.2
  have hline_mem : AffineMap.lineMap x y t ∈ Q :=
    lineMap_mem_feasible hQ_convex hx hy ht
  have hnorm_sub :
      ‖g (AffineMap.lineMap x y t) - g x‖ ≤
        (Gv : ℝ) * Real.rpow ‖AffineMap.lineMap x y t - x‖ (v : ℝ) :=
    hf.norm_sub_le hline_mem hx
  have hdist :
      ‖AffineMap.lineMap x y t - x‖ = t * ‖d‖ := by
    -- Along the line segment, the distance to `x` is exactly `t ‖y - x‖`.
    calc
      ‖AffineMap.lineMap x y t - x‖ = ‖t • d‖ := by
        simp [d, AffineMap.lineMap_apply_module']
      _ = |t| * ‖d‖ := norm_smul t d
      _ = t * ‖d‖ := by simp [abs_of_nonneg ht_nonneg]
  have hd_rpow :
      Real.rpow ‖d‖ (1 + (v : ℝ)) = Real.rpow ‖d‖ (v : ℝ) * ‖d‖ := by
    simpa [Real.rpow_one, add_comm] using
      (Real.rpow_add_of_nonneg (x := ‖d‖) (y := (v : ℝ)) (z := (1 : ℝ))
        (norm_nonneg d) hv_nonneg zero_le_one)
  -- Estimate the scalar remainder by the operator norm of the derivative-field difference.
  calc
    |((g (AffineMap.lineMap x y t) - g x) d : ℝ)| =
        ‖(g (AffineMap.lineMap x y t) - g x) d‖ := rfl
    _ ≤ ‖g (AffineMap.lineMap x y t) - g x‖ * ‖d‖ :=
      (g (AffineMap.lineMap x y t) - g x).le_opNorm d
    _ ≤ ((Gv : ℝ) * Real.rpow ‖AffineMap.lineMap x y t - x‖ (v : ℝ)) * ‖d‖ := by
      exact mul_le_mul_of_nonneg_right hnorm_sub (norm_nonneg d)
    _ = ((Gv : ℝ) * Real.rpow (t * ‖d‖) (v : ℝ)) * ‖d‖ := by
      rw [hdist]
    _ = ((Gv : ℝ) * (Real.rpow t (v : ℝ) * Real.rpow ‖d‖ (v : ℝ))) * ‖d‖ := by
      congr 2
      simpa using
        (Real.mul_rpow (x := t) (y := ‖d‖) (z := (v : ℝ)) ht_nonneg (norm_nonneg d))
    _ = (Gv : ℝ) * Real.rpow t (v : ℝ) * Real.rpow ‖d‖ (1 + (v : ℝ)) := by
      rw [mul_assoc, mul_assoc, ← hd_rpow]
      ring

/-- Helper for Proposition 6.39: the unit-interval integral of `t^v` is `(1 + v)⁻¹` when
`v > 0`. -/
lemma integral_unitInterval_rpow_eq_inv_add
    {v : NNReal} (hv : 0 < (v : ℝ)) :
    ∫ t : ℝ in 0..1, Real.rpow t (v : ℝ) = 1 / (1 + (v : ℝ)) := by
  have hv' : -1 < (v : ℝ) := by linarith
  have hpow_ne : (v : ℝ) + 1 ≠ 0 := by linarith
  -- Evaluate the primitive explicitly and simplify the endpoint terms at `0` and `1`.
  simpa [Real.zero_rpow hpow_ne, add_comm] using
    (integral_rpow (a := (0 : ℝ)) (b := 1) (r := (v : ℝ)) (Or.inl hv'))

-- Proof sketch: use convexity of `Q` to keep the segment from `x` to `y` inside `Q`, apply the
-- fundamental theorem of calculus to `t ↦ f (x + t • (y - x))`, estimate the remainder term with
-- the Hölder bound on `g`, and integrate `t^v` over `[0, 1]`.
/-- Proposition 6.39: if a chosen within-derivative field `g` for `f` on a convex feasible set
`Q` is `v`-Hölder continuous with constant `Gv` for some `0 < v`, then `f` satisfies the
first-order upper model
`f y ≤ f x + g x (y - x) + (Gv / (1 + v)) * ‖y - x‖^(1 + v)` on `Q`. -/
theorem upper_model
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q) (hv : 0 < (v : ℝ))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + g x (y - x) +
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
  let remainder : ℝ → ℝ := fun t ↦ (g (AffineMap.lineMap x y t) - g x) (y - x)
  let A : ℝ := Real.rpow ‖y - x‖ (1 + (v : ℝ))
  let kernel : ℝ → ℝ := fun t ↦ ((Gv : ℝ) * A) * Real.rpow t (v : ℝ)
  have hincrement :
      f y = f x + g x (y - x) + ∫ t : ℝ in 0..1, remainder t := by
    -- First isolate the exact integral remainder along the feasible segment.
    simpa [remainder] using
      increment_eq_linearization_add_integral_remainder hf hQ_convex hv hx hy
  have hg_cont : ContinuousOn g Q := hf.holderOn.continuousOn hv
  have hseg : Set.MapsTo (AffineMap.lineMap x y) (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact lineMap_mem_feasible hQ_convex hx hy ht
  have hgrad_cont :
      ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t)) (Set.Icc (0 : ℝ) 1) :=
    hg_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    -- The remainder integrand is continuous, hence interval integrable.
    have hsub_cont :
        ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t) - g x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    simpa [remainder] using
      hsub_cont.clm_apply
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hkernel_int : IntervalIntegrable kernel MeasureTheory.volume 0 1 := by
    -- The comparison kernel is a constant multiple of `t ↦ t^v` on `[0, 1]`.
    have hrpow_int :
        IntervalIntegrable (fun t : ℝ ↦ Real.rpow t (v : ℝ)) MeasureTheory.volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa [kernel, A, mul_assoc, mul_left_comm, mul_comm] using
      hrpow_int.const_mul ((Gv : ℝ) * A)
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, remainder t ≤ kernel t := by
    intro t ht
    -- Bound the scalar remainder by its absolute value, then use the Hölder kernel estimate.
    exact le_trans (le_abs_self (remainder t)) <| by
      simpa [remainder, kernel, A, mul_assoc, mul_left_comm, mul_comm] using
        segment_remainder_abs_le_holder_kernel hf hQ_convex hx hy ht
  have hmono :
      ∫ t : ℝ in 0..1, remainder t ≤ ∫ t : ℝ in 0..1, kernel t := by
    exact intervalIntegral.integral_mono_on
      (hf := hremainder_int) (hg := hkernel_int) (hab := zero_le_one) hpoint
  -- Combine the exact increment identity with the integral comparison and evaluate `∫_0^1 t^v`.
  calc
    f y = f x + g x (y - x) + ∫ t : ℝ in 0..1, remainder t := hincrement
    _ ≤ f x + g x (y - x) + ∫ t : ℝ in 0..1, kernel t := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hmono (f x + g x (y - x))
    _ = f x + g x (y - x) + ((Gv : ℝ) * A) * (∫ t : ℝ in 0..1, Real.rpow t (v : ℝ)) := by
      simp [kernel, intervalIntegral.integral_const_mul]
    _ = f x + g x (y - x) + ((Gv : ℝ) * A) * (1 / (1 + (v : ℝ))) := by
      rw [integral_unitInterval_rpow_eq_inv_add hv]
    _ = f x + g x (y - x) + ((Gv : ℝ) / (1 + (v : ℝ))) * A := by
      simp [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = f x + g x (y - x) + ((Gv : ℝ) / (1 + (v : ℝ))) *
        Real.rpow ‖y - x‖ (1 + (v : ℝ)) := by
      simp [A]

end ConditionalGradientContraction.HolderGradientOn

end
