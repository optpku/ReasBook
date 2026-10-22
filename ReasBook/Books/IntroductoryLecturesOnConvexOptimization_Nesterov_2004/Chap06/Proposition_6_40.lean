/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open ConditionalGradientContraction

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Proposition 6.40: the scalar field obtained by freezing the displacement slot in
the canonical within derivative of `f`. -/
private abbrev directional_derivative_field
    (f : E → ℝ) (Q : Set E) (d : E) : E → ℝ :=
  fun z ↦ fderivWithin ℝ f Q z d

/-- Helper for Proposition 6.40: the first derivative of the frozen-direction scalar field,
written as the within derivative of `fderivWithin ℝ f Q` with the displacement slot frozen at
`d`. -/
private abbrev directional_hessian_field
    (f : E → ℝ) (Q : Set E) (d : E) : E → StrongDual ℝ E :=
  fun z ↦ (fderivWithin ℝ (fderivWithin ℝ f Q) Q z).flip d

/-- Helper for Proposition 6.40: freezing the second slot of the canonical within Hessian agrees
with the derivative field of the frozen directional derivative. -/
private lemma directional_hessian_field_apply
    {Q : Set E} {f : E → ℝ} (hQ_unique : UniqueDiffOn ℝ Q)
    {d z w : E} (hz : z ∈ Q) :
    directional_hessian_field f Q d z w =
      iteratedFDerivWithin ℝ 2 f Q z ![w, d] := by
  -- Rewrite the derivative of the frozen scalar field through the canonical second within
  -- derivative.
  simpa [directional_hessian_field] using
    (iteratedFDerivWithin_two_apply' (f := f) (z := z) hQ_unique hz w d).symm

/-- Helper for Proposition 6.40: the frozen-direction second-derivative field inherits the
Hölder bound from the full within Hessian after one operator-norm evaluation in the fixed slot
`d`. -/
private lemma directional_hessian_field_norm_sub_le
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    {d x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖directional_hessian_field f Q d x - directional_hessian_field f Q d y‖ ≤
      ((H : ℝ) * ‖d‖) * Real.rpow ‖x - y‖ (v : ℝ) := by
  let A := iteratedFDerivWithin ℝ 2 f Q x
  let B := iteratedFDerivWithin ℝ 2 f Q y
  let L : E →L[ℝ] ℝ := directional_hessian_field f Q d x - directional_hessian_field f Q d y
  have hAB : ‖A - B‖ ≤ (H : ℝ) * Real.rpow ‖x - y‖ (v : ℝ) := by
    simpa [A, B, dist_eq_norm, sub_eq_add_neg] using hH.dist_le hx hy
  refine (L.opNorm_le_bound
    (mul_nonneg (norm_nonneg (A - B)) (norm_nonneg d)) ?_).trans ?_
  · intro w
    have hw : ‖(A - B) ![w, d]‖ ≤ ‖A - B‖ * (‖w‖ * ‖d‖) := by
      simpa using (ContinuousMultilinearMap.le_opNorm (A - B) ![w, d])
    have hEq :
        L w =
          (A - B) ![w, d] := by
      calc
        L w =
            directional_hessian_field f Q d x w - directional_hessian_field f Q d y w := by
              simp [L]
        _ = iteratedFDerivWithin ℝ 2 f Q x ![w, d] -
              iteratedFDerivWithin ℝ 2 f Q y ![w, d] := by
              rw [directional_hessian_field_apply hQ_unique (d := d) (z := x) (w := w) hx,
                directional_hessian_field_apply hQ_unique (d := d) (z := y) (w := w) hy]
        _ = (A - B) ![w, d] := by
              simp [A, B]
    calc
      ‖L w‖
          = ‖(A - B) ![w, d]‖ := by rw [hEq]
      _ ≤ ‖A - B‖ * (‖w‖ * ‖d‖) := hw
      _ = (‖A - B‖ * ‖d‖) * ‖w‖ := by ring
  · have hscaled :
        ‖A - B‖ * ‖d‖ ≤ ((H : ℝ) * Real.rpow ‖x - y‖ (v : ℝ)) * ‖d‖ := by
      exact mul_le_mul_of_nonneg_right hAB (norm_nonneg d)
    exact hscaled.trans_eq (by ring)

/-- Helper for Proposition 6.40: the frozen directional derivative field satisfies the Chapter 6
first-order Hölder-gradient owner with constant `H * ‖d‖`. -/
private lemma displacement_pair_holder_gradient_on
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    (d : E) :
    ConditionalGradientContraction.HolderGradientOn v (H * ‖d‖₊) Q
      (directional_derivative_field f Q d)
      (directional_hessian_field f Q d) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    -- Differentiate the scalar directional derivative by applying the derivative of
    -- `fderivWithin ℝ f Q` to the fixed displacement `d`.
    simpa [directional_derivative_field, directional_hessian_field] using
      (hf' z hz).hasFDerivWithinAt.clm_apply (hasFDerivWithinAt_const (s := Q) d z)
  · intro x hx y hy
    -- The full Hessian Hölder estimate loses one factor of `‖d‖` after freezing the second slot.
    have hdist :
        dist (directional_hessian_field f Q d x) (directional_hessian_field f Q d y) ≤
          (H : ℝ) * ‖d‖ * dist x y ^ (v : ℝ) := by
      simpa [dist_eq_norm, mul_assoc, mul_left_comm, mul_comm] using
        (directional_hessian_field_norm_sub_le hQ_unique hH (d := d) hx hy)
    have hnn :
        nndist (directional_hessian_field f Q d x) (directional_hessian_field f Q d y) ≤
          (H * ‖d‖₊) * nndist x y ^ (v : ℝ) := by
      rw [dist_nndist, dist_nndist] at hdist
      norm_cast at hdist ⊢
    rw [edist_nndist, edist_nndist, ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_nonneg _ (by exact_mod_cast v.2)]
    exact ENNReal.coe_le_coe.2 hnn

/-- Helper for Proposition 6.40: along the segment from `x` to `y`, the exact first-order
remainder of `f` is the integral of the directional-derivative increment. -/
private lemma segment_increment_eq_linearization_add_integral_gradient_remainder
    {Q : Set E} {f : E → ℝ}
    (hf : DifferentiableOn ℝ f Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y =
      f x + fderivWithin ℝ f Q x (y - x) +
        ∫ t : ℝ in 0..1,
          (fderivWithin ℝ f Q (AffineMap.lineMap x y t) (y - x) -
            fderivWithin ℝ f Q x (y - x)) := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let remainder : ℝ → ℝ := fun t ↦
    directional_derivative_field f Q (y - x) (seg t) -
      directional_derivative_field f Q (y - x) x
  let ψ : ℝ → ℝ := fun t ↦ f (seg t) - t * directional_derivative_field f Q (y - x) x
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy ht
  have hseg_deriv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ f (seg s))
          (directional_derivative_field f Q (y - x) (seg t)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Compose the within derivative of `f` with the affine segment parametrization.
    simpa [seg, directional_derivative_field] using
      (hf _ (hseg ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hseg
  have hseg_cont : ContinuousOn (fun t ↦ f (seg t)) (Set.Icc (0 : ℝ) 1) := by
    -- Differentiability of the segment restriction of `f` gives continuity on the whole unit
    -- interval.
    intro t ht
    exact (hseg_deriv t ht).continuousWithinAt
  have hgrad_cont :
      ContinuousOn (directional_derivative_field f Q (y - x)) Q := by
    -- The directional derivative field is continuous because `fderivWithin ℝ f Q` is
    -- differentiable on `Q`.
    simpa [directional_derivative_field] using
      (hf'.continuousOn.clm_apply continuousOn_const)
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    -- Continuity of the directional derivative field makes the remainder integrand continuous.
    have hdir_cont : ContinuousOn (fun t ↦ directional_derivative_field f Q (y - x) (seg t))
        (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
    simpa [remainder] using hdir_cont.sub continuousOn_const
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hlin_cont : ContinuousOn
        (fun t : ℝ ↦ t * directional_derivative_field f Q (y - x) x) (Set.Icc (0 : ℝ) 1) :=
      (continuous_id'.mul continuous_const).continuousOn
    simpa [ψ] using hseg_cont.sub hlin_cont
  have hψ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt ψ (remainder t) (Set.Ioi t) t := by
    intro t ht
    have hseg_deriv_right :
        HasDerivWithinAt (fun s ↦ f (seg s))
          (directional_derivative_field f Q (y - x) (seg t)) (Set.Ioi t) t :=
      (hseg_deriv t (Set.mem_Icc_of_Ioo ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGT ht.2) (by
          intro s hs
          exact ⟨ht.1.le.trans hs.1, hs.2⟩))
    have hlin_deriv :
        HasDerivWithinAt
          (fun s : ℝ ↦ s * directional_derivative_field f Q (y - x) x)
          (directional_derivative_field f Q (y - x) x) (Set.Ioi t) t := by
      simpa using
        (HasDerivAt.hasDerivWithinAt
          ((hasDerivAt_id' t).mul_const (directional_derivative_field f Q (y - x) x)))
    convert hseg_deriv_right.sub hlin_deriv using 1
  have hftc :
      ∫ t : ℝ in 0..1, remainder t = ψ 1 - ψ 0 := by
    -- Apply the one-dimensional FTC to the corrected segment remainder.
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      zero_le_one hψ_cont hψ_deriv hremainder_int
  have hftc' :
      ∫ t : ℝ in 0..1, remainder t =
        f y - f x - directional_derivative_field f Q (y - x) x := by
    simpa [ψ, remainder, seg, directional_derivative_field, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hftc
  linarith

/-- Helper for Proposition 6.40: the linear term in the upper model for the frozen directional
derivative field is exactly `t` times the quadratic Hessian term at `x`. -/
private lemma lineMap_directional_hessian_rewrite
    {Q : Set E} {f : E → ℝ}
    (hQ_unique : UniqueDiffOn ℝ Q)
    {x y d : E} (hx : x ∈ Q) {t : ℝ} :
    directional_hessian_field f Q d x (AffineMap.lineMap x y t - x) =
      t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, d] := by
  -- Rewrite the segment displacement as a scalar multiple of `y - x` and pull that scalar out of
  -- the frozen Hessian field.
  calc
    directional_hessian_field f Q d x (AffineMap.lineMap x y t - x)
        = directional_hessian_field f Q d x (t • (y - x)) := by
            simp [AffineMap.lineMap_apply_module']
    _ = t * directional_hessian_field f Q d x (y - x) := by
          simp [map_smul]
    _ = t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, d] := by
          rw [directional_hessian_field_apply hQ_unique (d := d) hx]

/-- Helper for Proposition 6.40: along the segment from `x` to `y`, the distance to `x` is
`t ‖y - x‖` for `t ∈ [0, 1]`. -/
private lemma lineMap_norm_sub_left
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
  -- Rewrite the segment displacement as the scalar multiple `t • (y - x)`.
  calc
    ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
      simp [AffineMap.lineMap_apply_module']
    _ = |t| * ‖y - x‖ := norm_smul t (y - x)
    _ = t * ‖y - x‖ := by simp [abs_of_nonneg ht.1]

/-- Helper for Proposition 6.40: for positive Hölder exponent, the frozen directional derivative
along the segment satisfies the first-order upper model with the expected quadratic-plus-Hölder
kernel. -/
private lemma segment_gradient_pair_upper_model
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hv : 0 < (v : ℝ)) :
    directional_derivative_field f Q (y - x) (AffineMap.lineMap x y t) -
      directional_derivative_field f Q (y - x) x ≤
      t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
        ((H : ℝ) / (1 + (v : ℝ))) *
          Real.rpow t (1 + (v : ℝ)) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) := by
  let d : E := y - x
  have hholder :
      ConditionalGradientContraction.HolderGradientOn v (H * ‖d‖₊) Q
        (directional_derivative_field f Q d)
        (directional_hessian_field f Q d) :=
    displacement_pair_holder_gradient_on hQ_unique hf' hH d
  have hline : AffineMap.lineMap x y t ∈ Q :=
    ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy ht
  have hupper :=
    ConditionalGradientContraction.HolderGradientOn.upper_model
      hholder hQ_convex hv hx hline
  have hv_nonneg : 0 ≤ (v : ℝ) := by
    exact_mod_cast v.2
  have hpow_d :
      Real.rpow ‖d‖ (2 + (v : ℝ)) =
        Real.rpow ‖d‖ (1 + (v : ℝ)) * ‖d‖ := by
    -- Split the exponent `2 + v` as `(1 + v) + 1` to isolate one factor of `‖d‖`.
    rw [show (2 + (v : ℝ)) = (1 + (v : ℝ)) + 1 by ring]
    simpa [Real.rpow_one, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Real.rpow_add_of_nonneg (x := ‖d‖) (y := 1 + (v : ℝ)) (z := (1 : ℝ))
        (norm_nonneg d) (by linarith) zero_le_one)
  have hkernel :
      (((H * ‖d‖₊ : NNReal) : ℝ) / (1 + (v : ℝ))) *
          Real.rpow ‖AffineMap.lineMap x y t - x‖ (1 + (v : ℝ)) =
        ((H : ℝ) / (1 + (v : ℝ))) *
          Real.rpow t (1 + (v : ℝ)) * Real.rpow ‖d‖ (2 + (v : ℝ)) := by
    -- Normalize the segment length and separate the powers of `t` and `‖d‖`.
    rw [lineMap_norm_sub_left (x := x) (y := y) ht]
    simp_rw [show ‖y - x‖ = ‖d‖ by simp [d]]
    rw [show Real.rpow (t * ‖d‖) (1 + (v : ℝ)) =
        Real.rpow t (1 + (v : ℝ)) * Real.rpow ‖d‖ (1 + (v : ℝ)) by
          simpa using
            (Real.mul_rpow (x := t) (y := ‖d‖) (z := 1 + (v : ℝ))
              ht.1 (norm_nonneg d))]
    rw [hpow_d]
    norm_num
    ring
  have hlinear :
      directional_hessian_field f Q d x (AffineMap.lineMap x y t - x) =
        t * iteratedFDerivWithin ℝ 2 f Q x ![d, d] := by
    simpa [d] using
      lineMap_directional_hessian_rewrite (hQ_unique := hQ_unique) (hx := hx)
        (x := x) (y := y) (d := d) (t := t)
  -- Apply Proposition 6.39 to the frozen scalar field, then normalize the segment geometry.
  have hupper' :
      directional_derivative_field f Q d (AffineMap.lineMap x y t) -
          directional_derivative_field f Q d x ≤
        directional_hessian_field f Q d x (AffineMap.lineMap x y t - x) +
          (((H * ‖d‖₊ : NNReal) : ℝ) / (1 + (v : ℝ))) *
            Real.rpow ‖AffineMap.lineMap x y t - x‖ (1 + (v : ℝ)) := by
    simpa [d, sub_le_iff_le_add, add_assoc, add_left_comm, add_comm] using hupper
  calc
    directional_derivative_field f Q d (AffineMap.lineMap x y t) -
        directional_derivative_field f Q d x ≤
      directional_hessian_field f Q d x (AffineMap.lineMap x y t - x) +
        (((H * ‖d‖₊ : NNReal) : ℝ) / (1 + (v : ℝ))) *
          Real.rpow ‖AffineMap.lineMap x y t - x‖ (1 + (v : ℝ)) := hupper'
    _ = t * iteratedFDerivWithin ℝ 2 f Q x ![d, d] +
        ((H : ℝ) / (1 + (v : ℝ))) *
          Real.rpow t (1 + (v : ℝ)) * Real.rpow ‖d‖ (2 + (v : ℝ)) := by
        rw [hlinear, hkernel]

/-- Helper for Proposition 6.40: on the open subsegment `(0,t)`, the corrected frozen-direction
remainder has derivative equal to the oscillation of the frozen Hessian field against the fixed
displacement. -/
private lemma segment_gradient_pair_corrected_remainder_hasDerivWithin
    {Q : Set E} {f : E → ℝ}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) t) :
    HasDerivWithinAt
      (fun s : ℝ ↦
        directional_derivative_field f Q (y - x) (AffineMap.lineMap x y s) -
          directional_derivative_field f Q (y - x) x -
            s * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x])
      ((directional_hessian_field f Q (y - x) (AffineMap.lineMap x y u) -
          directional_hessian_field f Q (y - x) x) (y - x))
      (Set.Ioo (0 : ℝ) t) u := by
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  have hseg_maps : Set.MapsTo seg (Set.Ioo (0 : ℝ) t) Q := by
    intro s hs
    exact
      ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy
        ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hseg_mem : seg u ∈ Q := hseg_maps hu
  have hdir :
      HasDerivWithinAt (fun s : ℝ ↦ directional_derivative_field f Q d (seg s))
        (directional_hessian_field f Q d (seg u) d) (Set.Ioo (0 : ℝ) t) u := by
    -- Route correction: differentiate the segment restriction through the packaged
    -- `directional_hessian_field` instead of expanding the nested second derivative first.
    simpa [seg, d, directional_derivative_field, directional_hessian_field] using
      ((hf' (seg u) hseg_mem).hasFDerivWithinAt.clm_apply
        (hasFDerivWithinAt_const (s := Q) d (seg u))).comp_hasDerivWithinAt u
        AffineMap.hasDerivWithinAt_lineMap hseg_maps
  have hlin :
      HasDerivWithinAt
        (fun s : ℝ ↦ s * iteratedFDerivWithin ℝ 2 f Q x ![d, d])
        (iteratedFDerivWithin ℝ 2 f Q x ![d, d]) (Set.Ioo (0 : ℝ) t) u := by
    -- The linear correction contributes the frozen quadratic term at `x`.
    simpa only [one_mul] using
      ((hasDerivAt_id' u).mul_const (iteratedFDerivWithin ℝ 2 f Q x ![d, d])).hasDerivWithinAt
  have hx_hessian :
      directional_hessian_field f Q d x d =
        iteratedFDerivWithin ℝ 2 f Q x ![d, d] := by
    rw [directional_hessian_field_apply hQ_unique (d := d) (z := x) (w := d) hx]
  have hcorrected :
      HasDerivWithinAt
        (fun s : ℝ ↦
          directional_derivative_field f Q d (seg s) -
            directional_derivative_field f Q d x -
              s * iteratedFDerivWithin ℝ 2 f Q x ![d, d])
        (directional_hessian_field f Q d (seg u) d -
          iteratedFDerivWithin ℝ 2 f Q x ![d, d])
        (Set.Ioo (0 : ℝ) t) u := by
    -- Differentiate the three scalar terms separately before any Hessian-oscillation rewrite.
    convert (hdir.sub_const (directional_derivative_field f Q d x)).sub hlin using 1
  have hoscillation :
      HasDerivWithinAt
        (fun s : ℝ ↦
          directional_derivative_field f Q d (seg s) -
            directional_derivative_field f Q d x -
              s * iteratedFDerivWithin ℝ 2 f Q x ![d, d])
        ((directional_hessian_field f Q d (seg u) - directional_hessian_field f Q d x) d)
        (Set.Ioo (0 : ℝ) t) u := by
    -- Rewrite the frozen quadratic term as the `x`-evaluation of the Hessian field.
    convert hcorrected using 1
    rw [ContinuousLinearMap.sub_apply, ← hx_hessian]
  -- Differentiate the three scalar pieces and rewrite the frozen `x` term into the target
  -- Hessian-oscillation form.
  simpa [d, seg] using hoscillation

/-- Helper for Proposition 6.40: in the zero-Hölder branch, the derivative of the corrected
remainder is bounded by the constant kernel `(H : ℝ) * ‖y - x‖²`. -/
private lemma segment_gradient_pair_corrected_remainder_deriv_norm_le_zero
    {Q : Set E} {f : E → ℝ} {H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hH0 : HolderOnWith H 0 (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) t) :
    ‖(directional_hessian_field f Q (y - x) (AffineMap.lineMap x y u) -
        directional_hessian_field f Q (y - x) x) (y - x)‖ ≤
      (H : ℝ) * Real.rpow ‖y - x‖ 2 := by
  let d : E := y - x
  have hseg_mem :
      AffineMap.lineMap x y u ∈ Q := by
    exact
      ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy
        ⟨hu.1.le, hu.2.le.trans ht.2⟩
  have hnorm :
      ‖directional_hessian_field f Q d (AffineMap.lineMap x y u) -
          directional_hessian_field f Q d x‖ ≤
        ((H : ℝ) * ‖d‖) * Real.rpow ‖AffineMap.lineMap x y u - x‖ 0 := by
    simpa [d] using
      directional_hessian_field_norm_sub_le (hQ_unique := hQ_unique) (hH := hH0)
        (d := d) (x := AffineMap.lineMap x y u) (y := x) hseg_mem hx
  -- Evaluate the operator-norm estimate on the frozen displacement.
  calc
    ‖(directional_hessian_field f Q d (AffineMap.lineMap x y u) -
        directional_hessian_field f Q d x) d‖ ≤
      ‖directional_hessian_field f Q d (AffineMap.lineMap x y u) -
          directional_hessian_field f Q d x‖ * ‖d‖ := by
        exact
          (directional_hessian_field f Q d (AffineMap.lineMap x y u) -
            directional_hessian_field f Q d x).le_opNorm d
    _ ≤ (((H : ℝ) * ‖d‖) * Real.rpow ‖AffineMap.lineMap x y u - x‖ 0) * ‖d‖ := by
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
    _ = (H : ℝ) * ‖d‖ ^ (2 : ℕ) := by
        simp [Real.rpow_zero]
        ring
    _ = (H : ℝ) * Real.rpow ‖d‖ 2 := by
        simpa using congrArg (fun z : ℝ ↦ (H : ℝ) * z) (Real.rpow_natCast ‖d‖ 2).symm
    _ = (H : ℝ) * Real.rpow ‖y - x‖ 2 := by simp [d]

/-- Helper for Proposition 6.40: when `v = 0`, the corrected remainder of the frozen directional
derivative along the segment is bounded by the constant Hessian-oscillation kernel integrated over
`[0, t]`. -/
private lemma segment_gradient_pair_remainder_abs_le_zero_kernel
    {Q : Set E} {f : E → ℝ} {H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH0 : HolderOnWith H 0 (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |directional_derivative_field f Q (y - x) (AffineMap.lineMap x y t) -
        directional_derivative_field f Q (y - x) x -
        t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x]| ≤
      (H : ℝ) * t * Real.rpow ‖y - x‖ 2 := by
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let R : ℝ → ℝ := fun s ↦
    directional_derivative_field f Q d (seg s) -
      directional_derivative_field f Q d x -
        s * iteratedFDerivWithin ℝ 2 f Q x ![d, d]
  let B : ℝ → ℝ := fun _ : ℝ ↦ (H : ℝ) * Real.rpow ‖d‖ 2
  have hseg_maps :
      Set.MapsTo seg (Set.Icc (0 : ℝ) t) Q := by
    intro s hs
    exact
      ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy
        ⟨hs.1, hs.2.trans ht.2⟩
  have hgrad_cont :
      ContinuousOn (directional_derivative_field f Q d) Q := by
    -- Continuity of the chosen within derivative follows from differentiability of `fderivWithin`.
    simpa [directional_derivative_field] using
      (hf'.continuousOn.clm_apply continuousOn_const)
  have hcont : ContinuousOn R (Set.Icc (0 : ℝ) t) := by
    have hdir_cont :
        ContinuousOn (fun s ↦ directional_derivative_field f Q d (seg s)) (Set.Icc (0 : ℝ) t) :=
      hgrad_cont.comp AffineMap.lineMap_continuous.continuousOn hseg_maps
    have hlin_cont :
        ContinuousOn (fun s : ℝ ↦ s * iteratedFDerivWithin ℝ 2 f Q x ![d, d])
          (Set.Icc (0 : ℝ) t) :=
      (continuous_id'.mul continuous_const).continuousOn
    -- The corrected remainder is the segment field minus its frozen linearization at `x`.
    simpa [R] using (hdir_cont.sub continuousOn_const).sub hlin_cont
  have hdiff : DifferentiableOn ℝ R (Set.Ioo (0 : ℝ) t) := by
    intro u hu
    exact
      (segment_gradient_pair_corrected_remainder_hasDerivWithin
        (hQ_unique := hQ_unique) (hf' := hf') (hQ_convex := hQ_convex)
        (hx := hx) (hy := hy) (ht := ht) (hu := hu)).differentiableWithinAt
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 t := by
    simpa [B, Set.uIcc_of_le ht.1] using
      (continuousOn_const : ContinuousOn B (Set.uIcc (0 : ℝ) t)).intervalIntegrable
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := R) (B := B) (a := (0 : ℝ)) (b := t) ht.1 hcont hdiff
      (Filter.Eventually.of_forall fun u hu ↦ by
        have hderiv :
            deriv R u =
              ((directional_hessian_field f Q d (seg u) - directional_hessian_field f Q d x) d) := by
          simpa [R, d, seg] using
            (segment_gradient_pair_corrected_remainder_hasDerivWithin
              (hQ_unique := hQ_unique) (hf' := hf') (hQ_convex := hQ_convex)
              (hx := hx) (hy := hy) (ht := ht) (hu := hu)).hasDerivAt
                (isOpen_Ioo.mem_nhds hu)
              |>.deriv
        rw [hderiv]
        simpa [B, d] using
          segment_gradient_pair_corrected_remainder_deriv_norm_le_zero
            (hQ_unique := hQ_unique) (hH0 := hH0) (hQ_convex := hQ_convex)
            (hx := hx) (hy := hy) (ht := ht) (hu := hu))
      hBi
  have hR0 : R 0 = 0 := by
    simp [R, d, seg]
  have hRt :
      R t =
        directional_derivative_field f Q d (seg t) -
          directional_derivative_field f Q d x -
            t * iteratedFDerivWithin ℝ 2 f Q x ![d, d] := by
    simp [R]
  rw [hRt, hR0, sub_zero, Real.norm_eq_abs] at hbound
  calc
    |directional_derivative_field f Q d (seg t) -
        directional_derivative_field f Q d x -
          t * iteratedFDerivWithin ℝ 2 f Q x ![d, d]| ≤
      ∫ s in (0 : ℝ)..t, B s := hbound
    _ = (H : ℝ) * t * Real.rpow ‖d‖ 2 := by
      rw [intervalIntegral.integral_const]
      simp [B, ht.1, mul_assoc, mul_left_comm, mul_comm]
    _ = (H : ℝ) * t * Real.rpow ‖y - x‖ 2 := by simp [d]

/-- Helper for Proposition 6.40: when `v = 0`, the absolute corrected-remainder estimate yields
the one-sided segment upper model needed for the final integral comparison. -/
private lemma segment_gradient_pair_upper_model_zero
    {Q : Set E} {f : E → ℝ} {H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH0 : HolderOnWith H 0 (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    directional_derivative_field f Q (y - x) (AffineMap.lineMap x y t) -
      directional_derivative_field f Q (y - x) x ≤
      t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
        (H : ℝ) * t * Real.rpow ‖y - x‖ 2 := by
  have hrem :=
    segment_gradient_pair_remainder_abs_le_zero_kernel
      (hQ_unique := hQ_unique) (hf' := hf') (hH0 := hH0) (hQ_convex := hQ_convex)
      (hx := hx) (hy := hy) (ht := ht)
  -- Drop the absolute value and move the linearization term back to the right-hand side.
  linarith [le_abs_self
    (directional_derivative_field f Q (y - x) (AffineMap.lineMap x y t) -
      directional_derivative_field f Q (y - x) x -
        t * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x])]

/-
Proposition 6.40 lies in the second-order Hölder upper-model domain on real normed spaces.

Sampled owner-style declarations:
- mathlib `HolderOnWith`, the canonical on-set owner for Hölder continuity of a map;
- mathlib `DifferentiableOn`, the canonical on-set owner for Fréchet differentiability;
- mathlib `UniqueDiffOn`, the canonical hypothesis ensuring that higher within derivatives are
  intrinsic on a feasible set;
- mathlib `iteratedFDerivWithin`, the canonical higher-order owner for within-set Fréchet
  derivatives;
- Chapter 6 `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the first-order
  chapter owner for Hölder regularity of the canonical within derivative on a convex feasible set;
- mathlib `contDiffOn_succ_iff_fderivWithin`, the owner equivalence showing that on a
  `UniqueDiffOn` set the canonical higher differential layer is organized around `fderivWithin`;
- mathlib `iteratedFDerivWithin_two_apply'`, the bridge identifying the second iterated within
  derivative with the nested `fderivWithin` formula on uniquely differentiable sets.

Source/core/bridge triage:
- source-facing: Proposition 6.40's quadratic upper model under Hölder continuity of the second
  derivative;
- core/canonical: `DifferentiableOn ℝ f Q`, `DifferentiableOn ℝ (fderivWithin ℝ f Q) Q`, and
  `HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q`;
- bridge/view: the pointwise quadratic-model inequality below.

Primitive data:
- the feasible set `Q`, objective `f`, Hölder exponent `v`, and Hölder constant `H`;
- convexity of `Q`;
- unique differentiability of `Q`, making the within-derivative layers intrinsic;
- differentiability on `Q` of `f` and of its canonical within derivative;
- Hölder continuity on `Q` of the canonical iterated within second-derivative map.

Derived API:
- the quadratic upper-model inequality below.

The previous file used ambient derivatives `fderiv ℝ f` and `fderiv ℝ (fderiv ℝ f)` on an
arbitrary convex set `Q`, which over-specialized the statement to neighborhood differentiability
at boundary points. This refinement keeps the source-facing proposition but moves its primitive
data to the canonical within-set layer: `fderivWithin` for first-derivative existence and
`iteratedFDerivWithin ℝ 2 f Q` for the public second-derivative owner. Because higher within
derivatives are only intrinsic on uniquely differentiable sets, the public API now records
`UniqueDiffOn ℝ Q` explicitly instead of treating convexity alone as sufficient. The nested
`fderivWithin` formula survives only as an internal bridge via
`iteratedFDerivWithin_two_apply'`. This matches the Chapter 6 owner style on feasible sets while
remaining faithful for lower-dimensional convex sets, and removes the redundant positivity guard
on `v`. -/

/-- Proposition 6.40: if the canonical iterated within second Fréchet derivative of `f` is
`v`-Hölder on the convex set `Q`, then `f` admits the quadratic upper model with Hölder
remainder `H * ‖y - x‖^(2 + v) / ((1 + v) * (2 + v))`. -/
-- Proof sketch: restrict `f` to the line segment `t ↦ x + t • (y - x)`, apply the
-- one-dimensional second-order Taylor formula with integral remainder, and bound the remainder
-- using the Hölder estimate on `iteratedFDerivWithin ℝ 2 f Q`; when one needs the nested
-- derivative formula inside the proof, recover it from `iteratedFDerivWithin_two_apply'`
-- together with `UniqueDiffOn ℝ Q` and convexity of `Q`.
theorem holder_hessian_upper_model
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf : DifferentiableOn ℝ f Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + fderivWithin ℝ f Q x (y - x) +
        (1 / 2 : ℝ) * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
          (H : ℝ) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) /
            ((1 + (v : ℝ)) * (2 + (v : ℝ))) := by
  let d : E := y - x
  let A : ℝ := iteratedFDerivWithin ℝ 2 f Q x ![d, d]
  let remainder : ℝ → ℝ := fun t ↦
    directional_derivative_field f Q d (AffineMap.lineMap x y t) -
      directional_derivative_field f Q d x
  have hincrement :
      f y = f x + fderivWithin ℝ f Q x d + ∫ t : ℝ in 0..1, remainder t := by
    -- Start from the exact segment integral remainder identity.
    simpa [d, remainder, directional_derivative_field] using
      segment_increment_eq_linearization_add_integral_gradient_remainder
        (hf := hf) (hf' := hf') (hQ_convex := hQ_convex) (hx := hx) (hy := hy)
  have hseg :
      Set.MapsTo (AffineMap.lineMap x y) (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact ConditionalGradientContraction.HolderGradientOn.lineMap_mem_feasible hQ_convex hx hy ht
  have hgrad_cont :
      ContinuousOn (directional_derivative_field f Q d) Q := by
    simpa [directional_derivative_field] using
      (hf'.continuousOn.clm_apply continuousOn_const)
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    have hdir_cont :
        ContinuousOn (fun t ↦ directional_derivative_field f Q d (AffineMap.lineMap x y t))
          (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
    simpa [remainder] using hdir_cont.sub continuousOn_const
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 := by
    exact hremainder_cont_uIcc.intervalIntegrable
  by_cases hv : 0 < (v : ℝ)
  · let B : ℝ := ((H : ℝ) / (1 + (v : ℝ))) * Real.rpow ‖d‖ (2 + (v : ℝ))
    let kernel : ℝ → ℝ := fun t ↦ A * t + B * Real.rpow t (1 + (v : ℝ))
    have hv_nonneg : 0 ≤ (v : ℝ) := by
      exact_mod_cast v.2
    have hint_id : IntervalIntegrable (fun t : ℝ ↦ A * t) MeasureTheory.volume 0 1 := by
      simpa using ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
        Continuous.intervalIntegrable continuous_id 0 1).const_mul A)
    have hint_rpow_base :
        IntervalIntegrable (fun t : ℝ ↦ Real.rpow t (1 + (v : ℝ)))
          MeasureTheory.volume 0 1 := by
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1 + (v : ℝ))
    have hint_rpow :
        IntervalIntegrable (fun t : ℝ ↦ B * Real.rpow t (1 + (v : ℝ)))
          MeasureTheory.volume 0 1 := by
      simpa using hint_rpow_base.const_mul B
    have hkernel_int :
        IntervalIntegrable kernel MeasureTheory.volume 0 1 := by
      simpa [kernel] using hint_id.add hint_rpow
    have hpoint :
        ∀ t ∈ Set.Icc (0 : ℝ) 1, remainder t ≤ kernel t := by
      intro t ht
      -- Use the already-stable positive branch pointwise upper model.
      simpa [remainder, kernel, A, B, d, mul_assoc, mul_left_comm, mul_comm] using
        segment_gradient_pair_upper_model
          (hQ_unique := hQ_unique) (hf' := hf') (hH := hH) (hQ_convex := hQ_convex)
          (hx := hx) (hy := hy) (ht := ht) hv
    have hmono :
        ∫ t : ℝ in 0..1, remainder t ≤ ∫ t : ℝ in 0..1, kernel t := by
      exact intervalIntegral.integral_mono_on
        (hf := hremainder_int) (hg := hkernel_int) (hab := zero_le_one) hpoint
    have hv_one : 0 < ((v + 1 : NNReal) : ℝ) := by
      exact add_pos_of_nonneg_of_pos (by exact_mod_cast v.2) zero_lt_one
    have hInt_rpow :
        ∫ t : ℝ in 0..1, Real.rpow t (1 + (v : ℝ)) = 1 / (2 + (v : ℝ)) := by
      have hdenom : (2 + (v : ℝ)) = 1 + ((v + 1 : NNReal) : ℝ) := by
        simp [NNReal.coe_add]
        ring
      calc
        ∫ t : ℝ in 0..1, Real.rpow t (1 + (v : ℝ)) =
            ∫ t : ℝ in 0..1, Real.rpow t ((v : ℝ) + 1) := by
              refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro t ht
              ring_nf
        _ = 1 / (1 + ((v + 1 : NNReal) : ℝ)) := by
              simpa [NNReal.coe_add] using
                (ConditionalGradientContraction.HolderGradientOn.integral_unitInterval_rpow_eq_inv_add
                  (v := v + 1) hv_one)
        _ = 1 / (2 + (v : ℝ)) := by rw [hdenom]
    calc
      f y = f x + fderivWithin ℝ f Q x d + ∫ t : ℝ in 0..1, remainder t := hincrement
      _ ≤ f x + fderivWithin ℝ f Q x d + ∫ t : ℝ in 0..1, kernel t := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hmono (f x + fderivWithin ℝ f Q x d)
      _ = f x + fderivWithin ℝ f Q x d +
            A * (∫ t : ℝ in 0..1, t) +
              B * (∫ t : ℝ in 0..1, Real.rpow t (1 + (v : ℝ))) := by
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
              ring
            · exact (show IntervalIntegrable (fun t : ℝ ↦ A * t) MeasureTheory.volume 0 1 from
                ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
                  Continuous.intervalIntegrable continuous_id 0 1).const_mul A))
            · exact (show IntervalIntegrable
                (fun t : ℝ ↦ B * Real.rpow t (1 + (v : ℝ))) MeasureTheory.volume 0 1 from
                (hint_rpow_base.const_mul B))
      _ = f x + fderivWithin ℝ f Q x d +
            A * (1 / 2 : ℝ) +
              B * (1 / (2 + (v : ℝ))) := by
            rw [integral_id, hInt_rpow]
            norm_num
      _ = f x + fderivWithin ℝ f Q x d +
            (1 / 2 : ℝ) * A +
              (H : ℝ) * Real.rpow ‖d‖ (2 + (v : ℝ)) /
                ((1 + (v : ℝ)) * (2 + (v : ℝ))) := by
            simp [A, B, div_eq_mul_inv]
            ring
      _ = f x + fderivWithin ℝ f Q x (y - x) +
            (1 / 2 : ℝ) * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
              (H : ℝ) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) /
                ((1 + (v : ℝ)) * (2 + (v : ℝ))) := by
            simp [A, d]
  · have hv0_real : (v : ℝ) = 0 := by
      exact le_antisymm (le_of_not_gt hv) (by exact_mod_cast v.2)
    have hH0 : HolderOnWith H 0 (iteratedFDerivWithin ℝ 2 f Q) Q := by
      simpa [HolderOnWith, hv0_real] using hH
    let B : ℝ := (H : ℝ) * Real.rpow ‖d‖ 2
    let kernel : ℝ → ℝ := fun t ↦ A * t + B * t
    have hkernel_int :
        IntervalIntegrable kernel MeasureTheory.volume 0 1 := by
      have hint_left : IntervalIntegrable (fun t : ℝ ↦ A * t) MeasureTheory.volume 0 1 := by
        simpa using ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
          Continuous.intervalIntegrable continuous_id 0 1).const_mul A)
      have hint_right : IntervalIntegrable (fun t : ℝ ↦ B * t) MeasureTheory.volume 0 1 := by
        simpa using ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
          Continuous.intervalIntegrable continuous_id 0 1).const_mul B)
      simpa [kernel] using hint_left.add hint_right
    have hpoint :
        ∀ t ∈ Set.Icc (0 : ℝ) 1, remainder t ≤ kernel t := by
      intro t ht
      -- The zero branch uses the corrected-remainder integral estimate proved just above.
      simpa [remainder, kernel, A, B, d, mul_assoc, mul_left_comm, mul_comm] using
        segment_gradient_pair_upper_model_zero
          (hQ_unique := hQ_unique) (hf' := hf') (hH0 := hH0) (hQ_convex := hQ_convex)
          (hx := hx) (hy := hy) (ht := ht)
    have hmono :
        ∫ t : ℝ in 0..1, remainder t ≤ ∫ t : ℝ in 0..1, kernel t := by
      exact intervalIntegral.integral_mono_on
        (hf := hremainder_int) (hg := hkernel_int) (hab := zero_le_one) hpoint
    calc
      f y = f x + fderivWithin ℝ f Q x d + ∫ t : ℝ in 0..1, remainder t := hincrement
      _ ≤ f x + fderivWithin ℝ f Q x d + ∫ t : ℝ in 0..1, kernel t := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hmono (f x + fderivWithin ℝ f Q x d)
      _ = f x + fderivWithin ℝ f Q x d +
            A * (∫ t : ℝ in 0..1, t) +
              B * (∫ t : ℝ in 0..1, t) := by
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
              ring
            · exact (show IntervalIntegrable (fun t : ℝ ↦ A * t) MeasureTheory.volume 0 1 from
                ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
                  Continuous.intervalIntegrable continuous_id 0 1).const_mul A))
            · exact (show IntervalIntegrable (fun t : ℝ ↦ B * t) MeasureTheory.volume 0 1 from
                ((show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
                  Continuous.intervalIntegrable continuous_id 0 1).const_mul B))
      _ = f x + fderivWithin ℝ f Q x d + A * (1 / 2 : ℝ) + B * (1 / 2 : ℝ) := by
            rw [integral_id]
            norm_num
      _ = f x + fderivWithin ℝ f Q x d +
            (1 / 2 : ℝ) * A +
              (H : ℝ) * Real.rpow ‖d‖ (2 + (v : ℝ)) /
                ((1 + (v : ℝ)) * (2 + (v : ℝ))) := by
            rw [hv0_real]
            simp [A, B, div_eq_mul_inv]
            ring
      _ = f x + fderivWithin ℝ f Q x (y - x) +
            (1 / 2 : ℝ) * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
              (H : ℝ) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) /
                ((1 + (v : ℝ)) * (2 + (v : ℝ))) := by
            simp [A, d, hv0_real]
