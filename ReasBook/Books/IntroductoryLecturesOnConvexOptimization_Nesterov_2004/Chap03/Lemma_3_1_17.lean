/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient Pointwise SupportFunction WithTopConvexAnalysis

universe u

variable {m : ℕ}

local notation "Y" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.1.17 lies in the chapter's local convex-composition / constrained-subdifferential
chain-rule domain.

Sampled owner-style declarations:
- `vectorMap` in `Lemma_3_1_16`, the chapter's existing owner for the coordinate vector
  `x ↦ (f₁(x), ..., fₘ(x))`;
- `constrainedSubdifferential` in `Definition_3_1_5`, the earlier chapter owner for local
  subgradient inequalities on a feasible set;
- `subdifferentialWithin` in `Theorem_3_44`, the later real-valued bridge/view of the same local
  notion at feasible points;
- mathlib `Monotone` and `HasGradientAt` on the coordinatewise ordered product `Fin m → ℝ`;
- the canonical finite weighted set sum `∑ i, a i • S i`.

Best owner abstractions:
- source-facing: Lemma 3.1.17's convex-composition and subdifferential chain rule;
- core/canonical: `constrainedSubdifferential`, `vectorMap`, and the full-domain coordinatewise
  monotonicity owner `Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`;
- bridge/view: the later `subdifferentialWithin` view.

Primitive data:
- the convex set `Q` in a finite-dimensional real inner-product space `E`;
- the outer function `F : Y → ℝ`;
- the coordinate family `f : Fin m → E → ℝ`.

Derived API:
- convexity of `F ∘ vectorMap f`;
- the weighted constrained-subdifferential identity at interior points of `Q`.

This file therefore deletes the duplicate global subgradient formulation and keeps the statement at
the correct local owner layer. The public API now uses the earlier chapter owner
`constrainedSubdifferential`, the existing coordinate-vector owner `vectorMap`, and the canonical
full-domain coordinatewise monotonicity hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on the product space `Fin m → ℝ`. The
textbook input model `ℝⁿ` is source-essential for the subdifferential identity, so the owner
theorem keeps the ambient space `E` finite-dimensional rather than extending to arbitrary real
inner-product spaces. The later `subdifferentialWithin` view should be derived from this owner
statement at feasible points rather than maintained as a parallel root theorem here.
-/

section Convexity

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- Helper for Lemma 3.1.17: if `F` is convex and coordinatewise monotone on `ℝ^m`, and
each component function `f i` is convex on the convex set `Q`, then the composition
`x ↦ F (f₁(x), ..., fₘ(x))` is convex on `Q`; coordinatewise monotonicity is recorded by the
canonical full-domain product-order hypothesis
`Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)` on `Fin m → ℝ`. -/
-- Proof sketch: combine convexity of each `f i` with coordinatewise monotonicity and convexity
-- of `F`.
theorem convexOn_comp_coordinatewiseMonotone
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm)) :
    ConvexOn ℝ Q (F ∘ vectorMap f) := by
  refine ⟨hQ_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First compare the coordinate vector at the convex combination point componentwise.
  have hcoord :
      (EuclideanSpace.equiv (Fin m) ℝ) (vectorMap f (a • x + b • y)) ≤
        (EuclideanSpace.equiv (Fin m) ℝ) (a • vectorMap f x + b • vectorMap f y) := by
    intro i
    simpa [vectorMap_apply] using (hf_conv i).2 hx hy ha hb hab
  have hmono :
      F (vectorMap f (a • x + b • y)) ≤ F (a • vectorMap f x + b • vectorMap f y) :=
    by simpa using hF_mono hcoord
  -- Then use the convexity inequality for `F` at the two endpoint coordinate vectors.
  have houter :
      F (a • vectorMap f x + b • vectorMap f y) ≤
        a * F (vectorMap f x) + b * F (vectorMap f y) := by
    simpa [Function.comp] using hF_conv.2 (by simp) (by simp) ha hb hab
  exact hmono.trans houter

end Convexity

section Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 3.1.17: the gradient of the outer convex function provides the global affine
support inequality at the linearization point. -/
private theorem outer_gradient_support_inequality
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F) {u z : Y} {g : Y}
    (hF_grad : HasGradientAt F g u) :
    F z ≥ F u + inner ℝ g (z - u) := by
  -- Lift `F` to the chapter's `WithTop` owner, where gradients of convex functions are
  -- subgradients on the full domain.
  have hdom : dom (fun y : Y ↦ (F y : WithTop ℝ)) = Set.univ := by
    ext y
    simp
  have hpart : withTopRealPart (fun y : Y ↦ (F y : WithTop ℝ)) = F := by
    funext y
    simp [withTopRealPart]
  have hF_conv_withTop :
      ConvexOn ℝ (dom (fun y : Y ↦ (F y : WithTop ℝ)))
        (withTopRealPart (fun y : Y ↦ (F y : WithTop ℝ))) := by
    simpa [hdom, hpart] using hF_conv
  have hu : u ∈ interior (dom (fun y : Y ↦ (F y : WithTop ℝ))) := by
    simp [hdom]
  have hsub :
      g ∈ ∂ (fun y : Y ↦ (F y : WithTop ℝ))(u) :=
    gradient_mem_subdifferential_of_hasGradientAt hF_conv_withTop hu hF_grad
  exact (mem_subdifferential_coe_real_iff.mp hsub) z

/-- Helper for Lemma 3.1.17: coordinatewise monotonicity forces every coordinate of the outer
gradient to be nonnegative. -/
private theorem gradient_nonneg_of_coordinatewise_monotone
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    {u : Y} {g : Y} (hF_grad : HasGradientAt F g u) :
    ∀ i : Fin m, 0 ≤ g i := by
  intro i
  let e : Y := EuclideanSpace.single i (1 : ℝ)
  have hmono :
      F (u - e) ≤ F u := by
    -- Move one unit in the negative `i`-th coordinate and apply monotonicity.
    have hle :
        (EuclideanSpace.equiv (Fin m) ℝ) (u - e) ≤
          (EuclideanSpace.equiv (Fin m) ℝ) u := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [e]
      · simp [e, hji]
    simpa [Function.comp] using hF_mono hle
  have hsupport :
      F (u - e) ≥ F u + inner ℝ g ((u - e) - u) := by
    -- Apply the global affine support inequality at the negatively shifted point.
    exact outer_gradient_support_inequality hF_conv hF_grad
  have hsingle :
      inner ℝ g e = g i := by
    -- Evaluate the Euclidean-space basis vector pairing in the `i`-th coordinate.
    simpa [e] using (EuclideanSpace.inner_single_right i (1 : ℝ) g)
  have hinner :
      inner ℝ g ((u - e) - u) = -g i := by
    -- The displacement `((u - e) - u)` is exactly `-e`, so the pairing is `-g i`.
    calc
      inner ℝ g ((u - e) - u) = inner ℝ g (-e) := by abel_nf
      _ = -inner ℝ g e := by simp
      _ = -g i := by rw [hsingle]
  rw [hinner] at hsupport
  linarith

/-- Helper for Lemma 3.1.17: a constrained subgradient controls every forward secant quotient
along feasible directions. -/
private theorem constrained_pairing_le_secant_quotient
    {Q : Set E} {u : E → ℝ} {x p h : E} {α : ℝ}
    (hh : h ∈ ∂[Q] (fun y ↦ (u y : WithTop ℝ))(x))
    (hα : 0 < α) (hy : x + α • p ∈ Q) :
    inner ℝ h p ≤ (u (x + α • p) - u x) / α := by
  rcases (mem_constrainedSubdifferential_iff.mp hh) with ⟨_, _, hminorant⟩
  have hineq :
      u (x + α • p) ≥ u x + inner ℝ h ((x + α • p) - x) := by
    exact_mod_cast hminorant hy
  have hinner :
      inner ℝ h ((x + α • p) - x) = α * inner ℝ h p := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (inner_smul_right h p α)
  rw [hinner] at hineq
  have hscaled : α * inner ℝ h p ≤ u (x + α • p) - u x := by
    linarith
  -- Divide the affine minorant by the positive step size.
  exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hscaled)

/-- Helper for Lemma 3.1.17: if every forward secant quotient at an interior point converges to a
directional bound `d p`, then any vector whose pairings are bounded by `d p` is a constrained
subgradient. -/
private theorem mem_constrainedSubdifferential_of_secant_limit_upper_bound
    {Q : Set E} {u : E → ℝ}
    (hu_conv : ConvexOn ℝ Q u) {x : E} (hx : x ∈ interior Q)
    {d : E → ℝ} {z : E}
    (hsecant :
      ∀ p : E,
        Filter.Tendsto (fun α : ℝ ↦ (u (x + α • p) - u x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)))
    (hpair : ∀ p : E, inner ℝ z p ≤ d p) :
    z ∈ ∂[Q] (fun y ↦ (u y : WithTop ℝ))(x) := by
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨interior_subset hx, by simp, ?_⟩
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    simp
  let p : E := y - x
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' Q
  let g : ℝ → ℝ := u ∘ line
  have hline_apply (α : ℝ) : line α = x + α • p := by
    -- Rewrite the affine line through `x` and `y` in displacement form.
    simpa [line, p, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict `u` to the scalar segment joining `x` and `y`.
    simpa [S, g] using hu_conv.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply, p] using hy
  have hderiv_Ioi : HasDerivWithinAt g (d p) (Set.Ioi (0 : ℝ)) 0 := by
    -- Read the secant-limit hypothesis as the right derivative of the scalar slice.
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
    simpa [g, hline_apply, slope_fun_def_field] using hsecant p
  have hslope :
      d p ≤ u y - u x := by
    -- The right derivative of a convex scalar slice is bounded by the endpoint secant slope.
    simpa [g, hline_apply, p, slope_def_field] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
  have hreal :
      u y ≥ u x + inner ℝ z (y - x) := by
    have hpair' : inner ℝ z (y - x) ≤ d (y - x) := hpair (y - x)
    linarith
  exact_mod_cast hreal

/-- Helper for Lemma 3.1.17: at an interior feasible point, the constrained subdifferential of the
zero function is the singleton `{0}`. -/
private theorem constrainedSubdifferential_zero_eq_singleton_zero
    {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    ∂[Q] (fun _ : E ↦ ((0 : ℝ) : WithTop ℝ))(x) = ({(0 : E)} : Set E) := by
  ext g
  constructor
  · intro hg
    by_cases hg_zero : g = 0
    · simp [hg_zero]
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨r, hr, hrsub⟩
    let α : ℝ := r / (2 * ‖g‖)
    have hnorm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg_zero
    have hα : 0 < α := by
      dsimp [α]
      exact div_pos hr (mul_pos zero_lt_two hnorm_pos)
    have hy_norm : ‖x + α • g - x‖ < r := by
      have hnorm_eq : ‖x + α • g - x‖ = α * ‖g‖ := by
        calc
          ‖x + α • g - x‖ = ‖α • g‖ := by
            abel_nf
          _ = α * ‖g‖ := by
            rw [norm_smul, Real.norm_of_nonneg hα.le]
      rw [hnorm_eq]
      dsimp [α]
      have hcalc : (r / (2 * ‖g‖)) * ‖g‖ = r / 2 := by
        field_simp [hnorm_pos.ne']
      rw [hcalc]
      linarith
    have hy_ball : x + α • g ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_assoc] using hy_norm
    have hyQ : x + α • g ∈ Q := interior_subset (hrsub hy_ball)
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, _, hminorant⟩
    have hineq :
        (((0 : ℝ) : WithTop ℝ)) ≥
          ((inner ℝ g ((x + α • g) - x) : ℝ) : WithTop ℝ) := by
      simpa using hminorant hyQ
    have hreal : 0 ≥ α * ‖g‖ ^ 2 := by
      have hineq' : (0 : ℝ) ≥ inner ℝ g ((x + α • g) - x) := by
        exact_mod_cast hineq
      simpa [sub_eq_add_neg, real_inner_smul_right, real_inner_self_eq_norm_sq, α,
        mul_assoc] using hineq'
    have hpos : 0 < α * ‖g‖ ^ 2 := by
      positivity
    linarith
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨interior_subset hx, by simp, ?_⟩
    intro y hy
    simp

/-- Helper for Lemma 3.1.17: the `WithTop` closed-ball extension of a real-valued function agrees
with the original function on the ball and is infinite outside it. -/
private def closedBallExtension (u : E → ℝ) (x : E) (r : ℝ)
    [DecidablePred fun y : E ↦ y ∈ Metric.closedBall x r] : E → WithTop ℝ :=
  fun y ↦ if y ∈ Metric.closedBall x r then (u y : WithTop ℝ) else ⊤

/-
The next two closed-ball helper lemmas only use the normed additive structure on `E`.
-/
omit [InnerProductSpace ℝ E] in
/-- Helper for Lemma 3.1.17: the effective domain of the closed-ball extension is exactly the
chosen closed ball. -/
private theorem mem_dom_closedBallExtension_iff
    {u : E → ℝ} {x y : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r] :
    y ∈ dom (closedBallExtension u x r) ↔ y ∈ Metric.closedBall x r := by
  change closedBallExtension u x r y < ⊤ ↔ y ∈ Metric.closedBall x r
  by_cases hy : y ∈ Metric.closedBall x r
  · simp [closedBallExtension, hy]
  · simp [closedBallExtension, hy]

omit [InnerProductSpace ℝ E] in
/-- Helper for Lemma 3.1.17: the center point lies in the interior of the effective domain of any
closed-ball extension. -/
private theorem closedBallExtension_mem_interior_dom
    {u : E → ℝ} {x : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hr : 0 < r) :
    x ∈ interior (dom (closedBallExtension u x r)) := by
  -- The effective domain is exactly the chosen closed ball, and the center lies in its interior.
  rw [show dom (closedBallExtension u x r) = Metric.closedBall x r by
    ext y
    exact mem_dom_closedBallExtension_iff]
  rw [mem_interior_iff_mem_nhds]
  exact Metric.closedBall_mem_nhds x hr

/-- Helper for Lemma 3.1.17: local subgradients on a closed ball coincide with constrained
subgradients on the ambient convex set once the ball stays inside that set. -/
private theorem subdifferential_closedBallExtension_eq_constrainedSubdifferential
    {Q : Set E} (hQ_convex : Convex ℝ Q) {u : E → ℝ}
    (hu_conv : ConvexOn ℝ Q u) {x : E} {r : ℝ} (hr : 0 < r)
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hball : Metric.closedBall x r ⊆ Q) :
    ∂ (closedBallExtension u x r)(x) =
      ∂[Q] (fun y ↦ (u y : WithTop ℝ))(x) := by
  ext g
  constructor
  · intro hg
    rw [mem_subdifferential_iff] at hg
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨hball (Metric.mem_closedBall_self hr.le), by simp, ?_⟩
    have hx_ball : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
    have hlocal :
        ∀ ⦃y : E⦄, y ∈ Metric.closedBall x r →
          u x + inner ℝ g (y - x) ≤ u y := by
      intro y hy
      have hy_dom : y ∈ dom (closedBallExtension u x r) :=
        (mem_dom_closedBallExtension_iff).2 hy
      have hineq := hg.2 hy_dom
      have hineq' :
          ((u y : WithTop ℝ)) ≥ ((u x : WithTop ℝ)) + (inner ℝ g (y - x) : WithTop ℝ) := by
        simpa [closedBallExtension, hy, hx_ball] using hineq
      exact_mod_cast hineq'
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp
    let t : ℝ := min 1 (r / ‖y - x‖)
    let z : E := (1 - t) • x + t • y
    have hy_sub_ne : y - x ≠ 0 := sub_ne_zero.mpr hyx
    have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr hy_sub_ne
    have ht_pos : 0 < t := by
      exact lt_min zero_lt_one (div_pos hr hnorm_pos)
    have ht_le_one : t ≤ 1 := min_le_left _ _
    have hz_eq : z - x = t • (y - x) := by
      dsimp [z, t]
      simp [sub_eq_add_neg, add_comm, add_left_comm, smul_add, add_smul]
    have hzQ : z ∈ Q := by
      -- The segment from `x` to `y` stays inside `Q`.
      dsimp [z, t]
      exact hQ_convex (hball (Metric.mem_closedBall_self hr.le)) hy
        (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hz_closedBall : z ∈ Metric.closedBall x r := by
      -- Choose `t` so the segment point remains in the closed ball.
      rw [Metric.mem_closedBall, dist_eq_norm, hz_eq, norm_smul, Real.norm_of_nonneg ht_pos.le]
      have ht_mul : t * ‖y - x‖ ≤ r := by
        have hmul :
            t * ‖y - x‖ ≤ (r / ‖y - x‖) * ‖y - x‖ :=
          mul_le_mul_of_nonneg_right (min_le_right 1 (r / ‖y - x‖)) hnorm_pos.le
        have hrewrite : (r / ‖y - x‖) * ‖y - x‖ = r := by
          field_simp [hnorm_pos.ne']
        simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa using ht_mul
    have hlocal_z : u x + inner ℝ g (z - x) ≤ u z := hlocal hz_closedBall
    have hconv_z :
        u z ≤ (1 - t) * u x + t * u y := by
      -- Convexity bounds the interior point `z` by the endpoint values.
      dsimp [z, t]
      exact hu_conv.2 (hball (Metric.mem_closedBall_self hr.le)) hy
        (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hlocal_y :
        u x + t * inner ℝ g (y - x) ≤ u z := by
      simpa [hz_eq, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hlocal_z
    have hscaled :
        t * (u x + inner ℝ g (y - x)) ≤ t * u y := by
      nlinarith
    have hreal : u x + inner ℝ g (y - x) ≤ u y := by
      nlinarith
    exact_mod_cast hreal
  · intro hg
    rw [mem_subdifferential_iff]
    have hx_ball : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
    refine ⟨(mem_dom_closedBallExtension_iff).2 hx_ball, ?_⟩
    intro y hy
    have hy_ball :
        y ∈ Metric.closedBall x r :=
      (mem_dom_closedBallExtension_iff).1 hy
    have hyQ : y ∈ Q := hball hy_ball
    have hineq := (mem_constrainedSubdifferential_iff.mp hg).2.2 hyQ
    simpa [closedBallExtension, hy_ball, hx_ball] using hineq

/-- Helper for Lemma 3.1.17: restricting a convex function to a closed ball gives a convex
`WithTop` lift on the effective domain of that restriction. -/
private theorem convexOn_closedBallExtension
    {Q : Set E} {u : E → ℝ} (hu_conv : ConvexOn ℝ Q u)
    {x : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hball : Metric.closedBall x r ⊆ Q) :
    ConvexOn ℝ (dom (closedBallExtension u x r))
      (withTopRealPart (closedBallExtension u x r)) := by
  have hdom :
      dom (closedBallExtension u x r) = Metric.closedBall x r := by
    ext y
    exact mem_dom_closedBallExtension_iff
  refine ⟨by simpa [hdom] using convex_closedBall x r, ?_⟩
  intro y hy z hz a b ha hb hab
  have hy_ball : y ∈ Metric.closedBall x r := by
    simpa [hdom] using hy
  have hz_ball : z ∈ Metric.closedBall x r := by
    simpa [hdom] using hz
  have hyQ : y ∈ Q := hball hy_ball
  have hzQ : z ∈ Q := hball hz_ball
  have hcomb_ball : a • y + b • z ∈ Metric.closedBall x r :=
    convex_closedBall x r hy_ball hz_ball ha hb hab
  -- On the closed ball, the `WithTop` extension simply evaluates to the original real function.
  simpa [withTopRealPart, closedBallExtension, hy_ball, hz_ball, hcomb_ball] using
    hu_conv.2 hyQ hzQ ha hb hab

/-- Helper for Lemma 3.1.17: a continuous convex real function on a closed ball yields a closed
convex `WithTop` extension that is finite exactly on that ball. -/
private theorem closedBallExtension_closedConvexFunction
    {Q : Set E} {u : E → ℝ} (hu_conv : ConvexOn ℝ Q u)
    {x : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hball : Metric.closedBall x r ⊆ Q)
    (hcont_closedBall : ContinuousOn u (Metric.closedBall x r)) :
    ClosedConvexFunction (closedBallExtension u x r) := by
  let fTop : E → WithTop ℝ := closedBallExtension u x r
  have hdom :
      dom fTop = Metric.closedBall x r := by
    ext y
    simpa [fTop] using
      (mem_dom_closedBallExtension_iff : y ∈ dom (closedBallExtension u x r) ↔
        y ∈ Metric.closedBall x r)
  have hconvTop :
      ConvexOn ℝ (dom fTop) (withTopRealPart fTop) := by
    simpa [fTop] using
      convexOn_closedBallExtension hu_conv hball
  have hcontTopBall : ContinuousOn (withTopRealPart fTop) (Metric.closedBall x r) := by
    refine ContinuousOn.congr hcont_closedBall ?_
    intro y hy
    simp [fTop, withTopRealPart, closedBallExtension, hy]
  refine ⟨subset_rfl, ?_, ?_⟩
  · rw [constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom fTop ⊆ dom fTop)]
    rw [hdom]
    exact IsClosed.epigraph Metric.isClosed_closedBall hcontTopBall
  · rw [constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom fTop ⊆ dom fTop)]
    exact (convexOn_iff_convex_epigraph).1 hconvTop

/-- Helper for Lemma 3.1.17: every convex component has a finite right secant limit along feasible
directions once we localize to one closed ball around the interior point. -/
private theorem directionalSecantQuotient_tendsto_of_convexOn_mem_interior
    {Q : Set E} {u : E → ℝ} (hu_conv : ConvexOn ℝ Q u)
    {x : E} (hx : x ∈ interior Q) (p : E) :
    ∃ d : ℝ,
      Filter.Tendsto (fun α : ℝ ↦ (u (x + α • p) - u x) / α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d) := by
  classical
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨r0, hr0, hr0sub⟩
  let r : ℝ := r0 / 2
  have hr : 0 < r := half_pos hr0
  have hball : Metric.closedBall x r ⊆ Q := by
    intro y hy
    exact interior_subset (hr0sub (Metric.closedBall_subset_ball (half_lt_self hr0) hy))
  let fTop : E → WithTop ℝ := closedBallExtension u x r
  have hconvTop :
      ConvexOn ℝ (dom fTop) (withTopRealPart fTop) := by
    simpa [fTop] using convexOn_closedBallExtension (u := u) hu_conv (x := x) (r := r) hball
  have hxDom : x ∈ interior (dom fTop) := by
    have hdom : dom fTop = Metric.closedBall x r := by
      ext y
      simpa [fTop] using mem_dom_closedBallExtension_iff (u := u) (x := x) (y := y) (r := r)
    rw [hdom]
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds x hr
  rcases
      exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
        (f := fTop) hconvTop (x := x) (p := p) hxDom with
    ⟨d, hdom_eventually, htendsto⟩
  refine ⟨d, ?_⟩
  -- Near `0` from the right, staying in the effective domain means the localized lift matches `u`.
  refine htendsto.congr' ?_
  filter_upwards [hdom_eventually] with α hα
  have hα_ball : x + α • p ∈ Metric.closedBall x r := by
    simpa [fTop] using
      (mem_dom_closedBallExtension_iff
        (u := u) (x := x) (y := x + α • p) (r := r)).1 hα
  have hx_ball : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hpartα : withTopRealPart fTop (x + α • p) = u (x + α • p) := by
    simp [withTopRealPart, fTop, closedBallExtension, hα_ball]
  have hpartx : withTopRealPart fTop x = u x := by
    simp [withTopRealPart, fTop, closedBallExtension, hx_ball]
  rw [hpartα, hpartx]

/-- Helper for Lemma 3.1.17: convexity on `Q` gives continuity on every closed ball contained in
`interior Q`. -/
private theorem continuousOn_closedBall_of_convexOn_interior
    [FiniteDimensional ℝ E]
    {Q : Set E} {u : E → ℝ} (hu_conv : ConvexOn ℝ Q u)
    {x : E} {r : ℝ} (hball : Metric.closedBall x r ⊆ interior Q) :
    ContinuousOn u (Metric.closedBall x r) := by
  -- Restrict the interior continuity of a finite-dimensional convex function to the chosen ball.
  exact hu_conv.continuousOn_interior.mono hball

/-- Helper for Lemma 3.1.17: along the right ray from `x`, sufficiently small steps remain inside
the chosen closed ball. -/
private theorem eventually_mem_closedBall_along
    {x p : E} {r : ℝ} (hr : 0 < r) :
    ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • p ∈ Metric.closedBall x r := by
  have hcont : Continuous fun α : ℝ ↦ x + α • p := by
    continuity
  have hball_mem : Metric.closedBall x r ∈ nhds (x + (0 : ℝ) • p) := by
    simpa using (Metric.closedBall_mem_nhds x hr)
  have hball :
      ∀ᶠ α : ℝ in nhds (0 : ℝ), x + α • p ∈ Metric.closedBall x r :=
    hcont.continuousAt.eventually_mem hball_mem
  exact nhdsWithin_le_nhds hball

/-- Helper for Lemma 3.1.17: at any finite base point, the whole-space subdifferential is closed
in the subgradient variable. -/
private theorem isClosed_subdifferentialAt_of_mem_dom
    {f : E → WithTop ℝ} {x : E} (hx : x ∈ dom f) :
    IsClosed (∂ f(x) : Set E) := by
  let H : dom f → Set E := fun y ↦
    {g : E | withTopRealPart f x + inner ℝ g (y.1 - x) ≤ withTopRealPart f y}
  have hclosedH : ∀ y : dom f, IsClosed (H y) := by
    intro y
    refine isClosed_le ?_ continuous_const
    -- Each support inequality cuts out a closed affine half-space in the subgradient variable.
    have hcont : Continuous fun g : E ↦ withTopRealPart f x + inner ℝ g (y.1 - x) := by
      continuity
    simpa [H] using hcont
  have hrepr : (∂ f(x) : Set E) = ⋂ y : dom f, H y := by
    ext g
    rw [mem_subdifferential_iff]
    constructor
    · rintro ⟨hx', hminorant⟩
      rw [Set.mem_iInter]
      intro y
      have hineq :
          f y.1 ≥ f x + (inner ℝ g (y.1 - x) : WithTop ℝ) :=
        hminorant y.2
      rw [← coe_withTopRealPart y.2, ← coe_withTopRealPart hx] at hineq
      exact_mod_cast hineq
    · intro hg
      refine ⟨hx, ?_⟩
      intro y hy
      have hineq : withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
        simpa [H] using (Set.mem_iInter.mp hg ⟨y, hy⟩)
      -- Move back from the finite real representative to the original `WithTop` values.
      rw [← coe_withTopRealPart hx, ← coe_withTopRealPart hy]
      exact_mod_cast hineq
  rw [hrepr]
  exact isClosed_iInter hclosedH

/-- Helper for Lemma 3.1.17: at an interior feasible point, the constrained subdifferential of a
convex real-valued function is compact. -/
private theorem isCompact_constrainedSubdifferential_of_convexOn_mem_interior
    [FiniteDimensional ℝ E]
    {Q : Set E} (hQ_convex : Convex ℝ Q) {u : E → ℝ}
    (hu_conv : ConvexOn ℝ Q u) {x : E} (hx : x ∈ interior Q) :
    IsCompact (∂[Q] (fun y ↦ (u y : WithTop ℝ))(x) : Set E) := by
  classical
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨r0, hr0, hr0sub⟩
  let r : ℝ := r0 / 2
  have hr : 0 < r := half_pos hr0
  have hball_int : Metric.closedBall x r ⊆ interior Q := by
    intro y hy
    exact hr0sub (Metric.closedBall_subset_ball (half_lt_self hr0) hy)
  have hball : Metric.closedBall x r ⊆ Q := by
    intro y hy
    exact interior_subset (hball_int hy)
  let fTop : E → WithTop ℝ := closedBallExtension u x r
  have hcont_closedBall : ContinuousOn u (Metric.closedBall x r) :=
    continuousOn_closedBall_of_convexOn_interior hu_conv hball_int
  have hclosedConvex : ClosedConvexFunction fTop := by
    -- Local continuity on the closed ball upgrades the localized extension to a closed convex
    -- function on the ambient space.
    simpa [fTop] using
      closedBallExtension_closedConvexFunction (u := u) hu_conv (x := x) (r := r) hball
        hcont_closedBall
  have hxDom : x ∈ interior (dom fTop) := by
    -- The effective domain of the localized extension is the chosen closed ball.
    rw [show dom fTop = Metric.closedBall x r by
      ext y
      simpa [fTop] using
        (mem_dom_closedBallExtension_iff (u := u) (x := x) (y := y) (r := r))]
    rw [mem_interior_iff_mem_nhds]
    exact Metric.closedBall_mem_nhds x hr
  have hbounded :
      Bornology.IsBounded (∂ fTop(x) : Set E) :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hclosedConvex.convexOn_withTopRealPart hxDom).2
  have hclosed :
      IsClosed (∂ fTop(x) : Set E) :=
    isClosed_subdifferentialAt_of_mem_dom (f := fTop) (x := x) (interior_subset hxDom)
  have hcompact_top : IsCompact (∂ fTop(x) : Set E) :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have htransport :
      ∂ fTop(x) = ∂[Q] (fun y ↦ (u y : WithTop ℝ))(x) := by
    simpa [fTop] using
      subdifferential_closedBallExtension_eq_constrainedSubdifferential
        hQ_convex hu_conv (x := x) (r := r) hr hball
  simpa [htransport] using hcompact_top

/-- Helper for Lemma 3.1.17: a vector whose pairings are bounded by the support function of a
closed convex set already lies in that set. -/
private theorem mem_of_pairing_le_supportFunction_of_isClosed_convex
    [FiniteDimensional ℝ E]
    {Q : Set E} (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) {z : E}
    (hz : ∀ p : E, ((inner ℝ z p : ℝ) : EReal) ≤ ξ[Q] p) :
    z ∈ Q := by
  by_contra hzQ
  obtain ⟨f, u, hQ_lt_raw, huz_raw⟩ :=
    geometric_hahn_banach_closed_point hQ_convex hQ_closed hzQ
  let p : E := (InnerProductSpace.toDual ℝ E).symm f
  have hQ_lt :
      ∀ y ∈ Q, inner ℝ y p < u := by
    intro y hy
    have :
        inner ℝ p y < u := by
      simpa [p] using hQ_lt_raw y hy
    simpa [real_inner_comm] using this
  have huz : u < inner ℝ z p := by
    have : u < inner ℝ p z := by
      simpa [p] using huz_raw
    simpa [real_inner_comm] using this
  have hξ_le : ξ[Q] p ≤ (u : EReal) := by
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    change (((inner ℝ y p : ℝ) : EReal) ≤ (u : EReal))
    exact_mod_cast (hQ_lt y hy).le
  have huzE : (u : EReal) < ((inner ℝ z p : ℝ) : EReal) := by
    exact_mod_cast huz
  exact (not_le_of_gt huzE) ((hz p).trans hξ_le)

/-- Helper for Lemma 3.1.17: a right secant limit for an inner path transports through a
gradient-supported outer function. -/
private theorem compositeSecantQuotient_tendsto_hasGradientAtAlong
    {F : Y → ℝ} {γ : ℝ → Y} {u g d : Y}
    (hγ0 : γ 0 = u)
    (hγ :
      Filter.Tendsto (fun α : ℝ ↦ α⁻¹ • (γ α - u))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d))
    (hF_grad : HasGradientAt F g u) :
    Filter.Tendsto (fun α : ℝ ↦ (F (γ α) - F u) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (inner ℝ g d)) := by
  have hγ_deriv : HasDerivWithinAt γ d (Set.Ioi (0 : ℝ)) 0 := by
    -- Repackage the secant-limit hypothesis as the right derivative of the vector-valued path.
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
    refine hγ.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα0 : α ≠ 0 := by
      exact ne_of_gt hα
    simp [slope_def_module, hγ0]
  have hF_deriv_at_zero :
      HasFDerivAt F ((InnerProductSpace.toDual ℝ Y) g) (γ 0) := by
    simpa [hγ0, HasGradientAt] using hF_grad.hasFDerivAt
  have hcomp_deriv :
      HasDerivWithinAt (F ∘ γ) (inner ℝ g d) (Set.Ioi (0 : ℝ)) 0 := by
    -- The ordinary chain rule now turns the path derivative into the scalar composite derivative.
    simpa using hF_deriv_at_zero.comp_hasDerivWithinAt (x := (0 : ℝ)) hγ_deriv
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)] at hcomp_deriv
  simpa [Function.comp, hγ0, slope_fun_def_field] using hcomp_deriv

/-- Helper for Lemma 3.1.17: the localized directional derivative of the `i`-th component along
`p`, viewed through the closed-ball extension around `x`. -/
private abbrev localizedComponentDirectionalDerivative
    {f : Fin m → E → ℝ} {x p : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (i : Fin m) (hxTop : x ∈ interior (dom (closedBallExtension (f i) x r))) : ℝ :=
  (closedBallExtension (f i) x r)′[hxTop] p

/-- Helper for Lemma 3.1.17: the tuple of localized component directional derivatives packaged as
an element of `Y`. -/
private abbrev localizedDirectionalDerivativeTuple
    {f : Fin m → E → ℝ} {x p : E} {r : ℝ}
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hxTop : ∀ i : Fin m, x ∈ interior (dom (closedBallExtension (f i) x r))) : Y :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm
    (fun i ↦
      localizedComponentDirectionalDerivative
        (f := f) (x := x) (p := p) (r := r) i (hxTop i))

/-- Helper for Lemma 3.1.17: every localized component directional derivative is attained by some
constrained component subgradient after transporting through the closed-ball extension. -/
private theorem localizedComponentMaximizer_exists
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    {x p : E} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Q)
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    [FiniteDimensional ℝ E]
    (i : Fin m) (hxTop : x ∈ interior (dom (closedBallExtension (f i) x r))) :
    ∃ s : E,
      s ∈ ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) ∧
        inner ℝ s p =
          localizedComponentDirectionalDerivative (f := f) (x := x) (p := p) (r := r) i hxTop := by
  have hconvTop :
      ConvexOn ℝ (dom (closedBallExtension (f i) x r))
        (withTopRealPart (closedBallExtension (f i) x r)) := by
    -- The localized closed-ball extension inherits convexity from the original component.
    simpa using
      convexOn_closedBallExtension (u := f i) (hu_conv := hf_conv i) (x := x) (r := r) hball
  have hgreatest :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior hconvTop hxTop p
  rcases hgreatest.1 with ⟨s, hsTop, hsPair⟩
  have hsubEq :
      ∂ (closedBallExtension (f i) x r)(x) = ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) := by
    -- The closed-ball extension and the constrained owner have the same subgradients at `x`.
    simpa using
      subdifferential_closedBallExtension_eq_constrainedSubdifferential
        hQ_convex (hf_conv i) (x := x) (r := r) hr hball
  refine ⟨s, ?_, hsPair⟩
  rwa [← hsubEq]

/-- Helper for Lemma 3.1.17: the secant quotient of `vectorMap f` along a feasible ray converges
to the tuple of localized component directional derivatives. -/
private theorem localizedVectorMapSecant_tendsto
    {Q : Set E} {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    {x p : E} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Q)
    [DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r]
    (hxTop : ∀ i : Fin m, x ∈ interior (dom (closedBallExtension (f i) x r))) :
    Filter.Tendsto
      (fun α : ℝ ↦ α⁻¹ • (vectorMap f (x + α • p) - vectorMap f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (localizedDirectionalDerivativeTuple (f := f) (x := x) (p := p) (r := r) hxTop)) := by
  let e : Y ≃ₜ (Fin m → ℝ) := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  have hpi :
      Filter.Tendsto
        (fun α : ℝ ↦ e (α⁻¹ • (vectorMap f (x + α • p) - vectorMap f x)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds fun i ↦
          localizedComponentDirectionalDerivative
            (f := f) (x := x) (p := p) (r := r) i (hxTop i)) := by
    -- Prove convergence coordinatewise, then repackage the coordinates back into `Y`.
    refine tendsto_pi_nhds.mpr ?_
    intro i
    let fiTop : E → WithTop ℝ := closedBallExtension (f i) x r
    have hconvTop :
        ConvexOn ℝ (dom fiTop) (withTopRealPart fiTop) := by
      -- Each localized component inherits convexity on its effective domain.
      simpa [fiTop] using
        convexOn_closedBallExtension (u := f i) (hu_conv := hf_conv i) (x := x) (r := r) hball
    have hxiTop : x ∈ interior (dom fiTop) := by
      -- The center remains interior to the localized effective domain.
      simpa [fiTop] using hxTop i
    have hsecant :
        Filter.Tendsto
          (fun α : ℝ ↦ (withTopRealPart fiTop (x + α • p) - withTopRealPart fiTop x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds
            (localizedComponentDirectionalDerivative
              (f := f) (x := x) (p := p) (r := r) i (hxTop i))) :=
      tendsto_directionalSecantQuotient_of_mem_interior hconvTop hxiTop p
    have hsecant' :
        Filter.Tendsto
          (fun α : ℝ ↦ (f i (x + α • p) - f i x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds
            (localizedComponentDirectionalDerivative
              (f := f) (x := x) (p := p) (r := r) i (hxTop i))) := by
      refine hsecant.congr' ?_
      filter_upwards [eventually_mem_closedBall_along (x := x) (p := p) (r := r) hr] with α hα_ball
      have hx_ball : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
      -- On the eventual closed-ball ray, the localized extension agrees with the original
      -- component.
      simp [fiTop, withTopRealPart, closedBallExtension, hα_ball, hx_ball]
    simpa [e, vectorMap_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsecant'
  -- Move back from coordinatewise convergence to the Euclidean-space limit.
  simpa [e] using
    (e.symm.continuous.tendsto
      (fun i ↦
        localizedComponentDirectionalDerivative
          (f := f) (x := x) (p := p) (r := r) i (hxTop i))).comp
      hpi

/-- Helper for Lemma 3.1.17: finite sums of nonnegative multiples of the component functions stay
convex on `Q`. -/
private theorem convexOn_weightedRealSum
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    {g : Y} (hgrad_nonneg : ∀ i : Fin m, 0 ≤ g i) :
    ConvexOn ℝ Q (fun y ↦ ∑ i : Fin m, g i * f i y) := by
  -- Build the weighted sum inductively from convex scalar multiples of each component.
  classical
  have hsum_conv :
      ∀ s : Finset (Fin m),
        (∀ i ∈ s, 0 ≤ g i) →
        ConvexOn ℝ Q (fun y ↦ Finset.sum s fun i ↦ g i * f i y) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using (convexOn_const (0 : ℝ) hQ_convex)
    · intro i s hi hs hnonneg
      have hi_nonneg : 0 ≤ g i := hnonneg i (Finset.mem_insert_self i s)
      have hi_conv : ConvexOn ℝ Q (fun y ↦ g i * f i y) :=
        (hf_conv i).smul hi_nonneg
      have hs_nonneg : ∀ j ∈ s, 0 ≤ g j := by
        intro j hj
        exact hnonneg j (Finset.mem_insert_of_mem hj)
      have hs_conv : ConvexOn ℝ Q (fun y ↦ Finset.sum s fun j ↦ g j * f j y) := hs hs_nonneg
      -- Add the new weighted component to the convex tail sum.
      simpa [Finset.sum_insert hi, add_comm, add_left_comm, add_assoc] using hi_conv.add hs_conv
  simpa using hsum_conv Finset.univ (fun i _ ↦ hgrad_nonneg i)

/-- Helper for Lemma 3.1.17: any choice of coordinate constrained subgradients yields a feasible
subgradient of the composite function. -/
private theorem weighted_sum_mem_constrainedSubdifferential_comp_coordinatewiseMonotone
    {Q : Set E} {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ}
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    {x : E} (hx : x ∈ Q) {g : Y}
    (hF_grad : HasGradientAt F g (vectorMap f x))
    {gs : Fin m → E}
    (hgs : ∀ i, gs i ∈ ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)) :
    (∑ i, (g i) • gs i) ∈
      ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) := by
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hx, by simp, ?_⟩
  intro y hy
  let w : Y :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ inner ℝ (gs i) (y - x)
  have hcoord :
      (EuclideanSpace.equiv (Fin m) ℝ) (vectorMap f x + w) ≤
        (EuclideanSpace.equiv (Fin m) ℝ) (vectorMap f y) := by
    intro i
    have hi :
        f i y ≥ f i x + inner ℝ (gs i) (y - x) := by
      exact_mod_cast (mem_constrainedSubdifferential_iff.mp (hgs i)).2.2 hy
    simpa [w, vectorMap_apply] using hi
  have hmono :
      F (vectorMap f x + w) ≤ F (vectorMap f y) := by
    simpa [w] using hF_mono hcoord
  have houter :
      F (vectorMap f x) + inner ℝ g w ≤ F (vectorMap f x + w) := by
    simpa [w] using
      (outer_gradient_support_inequality hF_conv (u := vectorMap f x)
        (z := vectorMap f x + w) hF_grad)
  have hinner_coords :
      inner ℝ g w = ∑ i, g i * inner ℝ (gs i) (y - x) := by
    -- Rewrite the Euclidean inner product as the finite coordinate sum coming from `w`.
    calc
      inner ℝ g w = ∑ i, inner ℝ (g i) (inner ℝ (gs i) (y - x)) := by
        simp [w, PiLp.inner_apply]
      _ = ∑ i, g i * inner ℝ (gs i) (y - x) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          inner ℝ (g i) (inner ℝ (gs i) (y - x)) =
              inner ℝ (gs i) (y - x) * g i := by
                calc
                  inner ℝ (g i) (inner ℝ (gs i) (y - x)) =
                      inner ℝ (gs i) (y - x) * star (g i) := by
                        exact RCLike.inner_apply (g i) (inner ℝ (gs i) (y - x))
                  _ = inner ℝ (gs i) (y - x) * g i := by
                        simp
          _ = g i * inner ℝ (gs i) (y - x) := by ring
  have hinner_sum :
      inner ℝ (∑ i, (g i) • gs i) (y - x) =
        ∑ i, g i * inner ℝ (gs i) (y - x) := by
    simp [sum_inner, real_inner_smul_left, mul_comm]
  -- Combine the coordinate subgradient inequalities with the outer affine support inequality.
  have hsupport :
      F (vectorMap f y) ≥
        F (vectorMap f x) + inner ℝ (∑ i, (g i) • gs i) (y - x) := by
    calc
      F (vectorMap f y) ≥ F (vectorMap f x) + inner ℝ g w := by
        exact le_trans houter hmono
      _ = F (vectorMap f x) + inner ℝ (∑ i, (g i) • gs i) (y - x) := by
        rw [hinner_coords, ← hinner_sum]
  exact_mod_cast hsupport

/-- Helper for Lemma 3.1.17: the weighted Minkowski sum of the coordinate constrained
subdifferentials is always contained in the constrained subdifferential of the composite. -/
private theorem weighted_sum_subset_constrainedSubdifferential_comp_coordinatewiseMonotone
    {Q : Set E} {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ}
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    {x : E} (hx : x ∈ interior Q) {g : Y}
    (hF_grad : HasGradientAt F g (vectorMap f x)) :
    (∑ i, (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)) ⊆
      ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) := by
  classical
  intro z hz
  rcases
      (Set.mem_finset_sum
        (t := Finset.univ)
        (f := fun i : Fin m ↦ (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x))
        (a := z)).mp hz with
    ⟨pieces, hpieces, hsum⟩
  choose gs hgs_mem hgs_eq using
    fun i ↦ Set.mem_smul_set.mp (hpieces (i := i) (by simp))
  -- Expand a point in the weighted Minkowski sum into coordinate subgradients and apply the
  -- pointwise inclusion proved above.
  have hmem :
      (∑ i, (g i) • gs i) ∈
        ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) :=
    weighted_sum_mem_constrainedSubdifferential_comp_coordinatewiseMonotone
      hF_conv hF_mono (interior_subset hx) hF_grad hgs_mem
  simpa [hsum, hgs_eq] using hmem

/-- Helper for Lemma 3.1.17: every constrained composite subgradient pairing is bounded by the
support function of the weighted candidate set obtained from the component subdifferentials. -/
private theorem compositeSubgradient_pairing_le_supportFunctionWeightedCandidate
    [FiniteDimensional ℝ E]
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} {f : Fin m → E → ℝ}
    (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    {x : E} {g : Y} (hF_grad : HasGradientAt F g (vectorMap f x))
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Q)
    {S : Set E}
    (hS_def : S = ∑ i : Fin m, (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x))
    {h : E}
    (hh : h ∈ ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x)) :
    ∀ p : E, ((inner ℝ h p : ℝ) : EReal) ≤ ξ[S] p := by
  intro p
  classical
  letI : DecidablePred fun z : E ↦ z ∈ Metric.closedBall x r := Classical.decPred _
  have hxTop :
      ∀ i : Fin m, x ∈ interior (dom (closedBallExtension (f i) x r)) := by
    intro i
    exact closedBallExtension_mem_interior_dom (u := f i) (x := x) (r := r) hr
  choose s hs_mem hs_pair using
    fun i : Fin m ↦ localizedComponentMaximizer_exists
      hQ_convex hf_conv (x := x) (p := p) (r := r) hr hball i (hxTop i)
  let q : E := ∑ i : Fin m, (g i) • s i
  let d : Y := localizedDirectionalDerivativeTuple (f := f) (x := x) (p := p) (r := r) hxTop
  have hqS : q ∈ S := by
    -- Assemble the chosen component subgradients into a point of the weighted candidate set.
    rw [hS_def]
    refine (Set.mem_finset_sum
      (t := Finset.univ)
      (f := fun i : Fin m ↦ (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x))
      (a := q)).2 ?_
    refine ⟨fun i ↦ (g i) • s i, ?_, by simp [q]⟩
    intro i hi
    exact Set.mem_smul_set.mpr ⟨s i, hs_mem i, rfl⟩
  have hd_apply :
      ∀ i : Fin m,
        d i =
          localizedComponentDirectionalDerivative
            (f := f) (x := x) (p := p) (r := r) i (hxTop i) := by
    intro i
    simp [d]
  have hq_inner :
      inner ℝ q p = inner ℝ g d := by
    -- The weighted witness pairing matches the outer gradient paired with the limit vector `d`.
    calc
      inner ℝ q p = ∑ i : Fin m, g i * inner ℝ (s i) p := by
        simp [q, sum_inner, real_inner_smul_left, mul_comm]
      _ = ∑ i : Fin m, g i * d i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hs_pair i, hd_apply i]
      _ = inner ℝ g d := by
        symm
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          inner ℝ (g i) (d i) = d i * star (g i) := by
            exact RCLike.inner_apply (g i) (d i)
          _ = d i * g i := by simp
          _ = g i * d i := by ring
  have hvector_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦ α⁻¹ • (vectorMap f (x + α • p) - vectorMap f x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds d) :=
    localizedVectorMapSecant_tendsto hf_conv (x := x) (p := p) (r := r) hr hball hxTop
  have hcomp_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦ (F (vectorMap f (x + α • p)) - F (vectorMap f x)) / α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (inner ℝ g d)) := by
    -- Transport the vector secant limit through the outer gradient witness.
    simpa using
      compositeSecantQuotient_tendsto_hasGradientAtAlong
        (γ := fun α : ℝ ↦ vectorMap f (x + α • p))
        (u := vectorMap f x) (g := g) (d := d)
        (hγ0 := by simp) hvector_tendsto hF_grad
  have hpair_eventually :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        inner ℝ h p ≤ (F (vectorMap f (x + α • p)) - F (vectorMap f x)) / α := by
    -- Feasible forward secants dominate the pairing of every constrained composite subgradient.
    filter_upwards [eventually_mem_closedBall_along (x := x) (p := p) (r := r) hr,
      self_mem_nhdsWithin] with α hα_ball hαpos
    exact constrained_pairing_le_secant_quotient hh hαpos (hball hα_ball)
  have hpair_le_q : inner ℝ h p ≤ inner ℝ q p := by
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ inner ℝ h p)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (inner ℝ h p)) :=
      tendsto_const_nhds
    have hpair_le_d : inner ℝ h p ≤ inner ℝ g d :=
      le_of_tendsto_of_tendsto hconst hcomp_tendsto hpair_eventually
    simpa [hq_inner] using hpair_le_d
  have hq_support : ((inner ℝ q p : ℝ) : EReal) ≤ ξ[S] p := by
    -- The explicit witness `q ∈ S` bounds the support function from below in direction `p`.
    rw [supportFunction_apply]
    exact le_csSup (by exact ⟨⊤, fun _ _ ↦ le_top⟩) ⟨q, hqS, rfl⟩
  have hpair_ereal :
      ((inner ℝ h p : ℝ) : EReal) ≤ ((inner ℝ q p : ℝ) : EReal) := by
    exact_mod_cast hpair_le_q
  exact hpair_ereal.trans hq_support

/-- Helper for Lemma 3.1.17: the constrained subdifferential of the composite is contained in the
weighted Minkowski sum of the component constrained subdifferentials. -/
private theorem localizedCompositeSubdifferential_subset_weightedSum
    [FiniteDimensional ℝ E]
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} {f : Fin m → E → ℝ}
    (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    {x : E} {g : Y} (hF_grad : HasGradientAt F g (vectorMap f x))
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Q)
    {S : Set E}
    (hS_def : S = ∑ i : Fin m, (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x))
    (hclosedS : IsClosed S) (hconvexS : Convex ℝ S) :
    ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) ⊆ S := by
  intro h hh
  -- Use the closed-convex support-function criterion once every pairing is bounded.
  exact mem_of_pairing_le_supportFunction_of_isClosed_convex hclosedS hconvexS
    (compositeSubgradient_pairing_le_supportFunctionWeightedCandidate
      hQ_convex hf_conv hF_grad hr hball hS_def hh)

/-- Lemma 3.1.17 (subdifferential part): in a finite-dimensional real inner-product space `E`, if
`F` is convex and coordinatewise monotone on `ℝ^m`, and each component function `f i` is convex
on the convex set `Q`, then at every interior feasible point `x ∈ interior Q` and for every
gradient witness `g = ∇F (f₁(x), ..., fₘ(x))`, the constrained subdifferential
`∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x)` equals the weighted sum
`∑ᵢ gᵢ • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`. This keeps the owner notation `∂[Q]` on the
public theorem surface instead of unpacking it back to the raw set builder. -/
-- Semantic recall check: `lean_leansearch` surfaced only generic calculus lemmas, so the chapter
-- owner theorem here remains the right source-facing place for this finite-dimensional chain rule.
-- Proof sketch: compute the directional derivative of the composition using the pointwise
-- gradient witness `HasGradientAt F g (vectorMap f x)`, identify each directional
-- derivative of `f i` with its support function on
-- `∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)`, and then apply the
-- support-function characterization of convex sets from Corollary 3.1.5 inside the feasible set
-- `Q`.
theorem constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {F : Y → ℝ} (hF_conv : ConvexOn ℝ Set.univ F)
    {f : Fin m → E → ℝ} (hf_conv : ∀ i, ConvexOn ℝ Q (f i))
    (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))
    [FiniteDimensional ℝ E]
    {x : E} (hx : x ∈ interior Q) {g : Y}
    (hF_grad : HasGradientAt F g (vectorMap f x)) :
    ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) =
      ∑ i : Fin m,
        (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) := by
  have hsubset :
      (∑ i : Fin m,
          (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)) ⊆
        ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) :=
    weighted_sum_subset_constrainedSubdifferential_comp_coordinatewiseMonotone
      hF_conv hF_mono hx hF_grad
  classical
  -- Route correction: avoid the unavailable complete-space support-function comparison theorem by
  -- localizing to a closed ball and turning directional secant bounds directly into constrained
  -- subgradient membership.
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨r0, hr0, hr0sub⟩
  let r : ℝ := r0 / 2
  have hr : 0 < r := half_pos hr0
  have hball : Metric.closedBall x r ⊆ Q := by
    intro y hy
    exact interior_subset (hr0sub (Metric.closedBall_subset_ball (half_lt_self hr0) hy))
  have hcompact_component :
      ∀ i : Fin m,
        IsCompact (∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) : Set E) := by
    -- Each constrained component subdifferential is compact by local closed-ball transport.
    intro i
    exact
      isCompact_constrainedSubdifferential_of_convexOn_mem_interior
        hQ_convex (hf_conv i) hx
  let S : Set E := ∑ i : Fin m, (g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x)
  have hcompactS : IsCompact S := by
    -- The weighted candidate set is a finite Minkowski sum of compact scaled component
    -- subdifferentials, hence compact.
    have hcompact_sum :
        ∀ s : Finset (Fin m),
          IsCompact ((Finset.sum s fun i ↦
            ((g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) : Set E)) : Set E) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp
      | @insert i s hi ih =>
          simpa [Finset.sum_insert hi] using ((hcompact_component i).smul (g i)).add ih
    simpa [S] using hcompact_sum Finset.univ
  have hconvexS : Convex ℝ S := by
    -- Convexity is preserved by scalar multiplication and Minkowski sums.
    have hconvex_sum :
        ∀ s : Finset (Fin m),
          Convex ℝ ((Finset.sum s fun i ↦
            ((g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) : Set E)) : Set E) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using (convex_zero : Convex ℝ (0 : Set E))
      | @insert i s hi ih =>
          have hi_base :
              Convex ℝ (∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) : Set E) :=
            convex_constrainedSubdifferential (Q := Q)
              (f := fun y ↦ (f i y : WithTop ℝ)) (x := x)
          have hi_conv :
              Convex ℝ ((g i) • ∂[Q] (fun y ↦ (f i y : WithTop ℝ))(x) : Set E) :=
            Convex.smul (𝕜 := ℝ) hi_base (g i)
          simpa [Finset.sum_insert hi] using hi_conv.add ih
    simpa [S] using hconvex_sum Finset.univ
  have hclosedS : IsClosed S := hcompactS.isClosed
  have hsubsetS :
      S ⊆ ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) := by
    simpa [S] using hsubset
  have hreverse :
      ∂[Q] (fun y ↦ ((F ∘ vectorMap f) y : WithTop ℝ))(x) ⊆ S := by
    -- Apply the isolated reverse-inclusion lemma so this theorem only assembles the main pieces.
    exact
      localizedCompositeSubdifferential_subset_weightedSum
        hQ_convex hf_conv hF_grad (r := r) hr hball rfl hclosedS hconvexS
  simpa [S] using Set.Subset.antisymm hreverse hsubsetS

end Gradient

end
