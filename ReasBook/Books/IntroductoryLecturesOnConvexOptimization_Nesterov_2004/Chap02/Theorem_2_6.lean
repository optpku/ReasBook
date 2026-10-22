/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Primary domain: twice continuously differentiable smooth convex analysis on finite-dimensional
real inner-product spaces with seminorm-controlled gradient smoothness.

Relevant owner-style declarations sampled before refining this file:
* `ConvexC1On` in `Definition_2_4`
* `𝓕[L, p]¹¹` in `Theorem_2_5`
* `convexOn_iff_hessian_quadratic_form_nonneg` in `Theorem_2_4`

Source/core/bridge triage:
* source-facing: `f ∈ 𝓕[L, p]¹¹`
* core/canonical: `ConvexOn ℝ Set.univ f` together with the upper Hessian quadratic-form bound
* bridge/view: the owner theorem
  `ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound` and the explicit lower-and-upper
  Hessian quadratic-form inequalities in
  `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`

The owner abstraction here is `f ∈ 𝓕[L, p]¹¹`.
Primitive data: the whole-space `C¹` convexity owner `ConvexC1On Set.univ f` and the defining
dual-norm Lipschitz bound for `∇ f`.
Derived API: `hf.contDiff`, `hf.convexOn`, `hf.dualNorm_gradient_sub_le`, and via Theorem 2.4 the
nonnegativity of the Hessian quadratic form. The only genuinely new second-order ingredient here
is the upper bound `inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2`. This matches the textbook
`ℝⁿ` setting through the chapter owner `𝓕[L, p]¹¹`, rather than over-generalizing beyond the
available first-order owner layer. -/

section

variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal} {f : E → ℝ}

open scoped SeminormDualNorm

open InnerProductSpace

/-- Helper for Theorem 2.6: the dual pairing with `x` is controlled in absolute value by the
dual seminorm of `g` times `p x`. -/
private theorem abs_inner_le_dualNorm_mul (x g : E) :
    |inner ℝ g x| ≤ ‖g‖[p,*] * p x := by
  -- Bound the positive and negative parts separately using the dual Cauchy--Schwarz inequality.
  refine abs_le.mpr ?_
  constructor
  · have hneg : -inner ℝ g x ≤ ‖g‖[p,*] * p x := by
      simpa using (Seminorm.inner_le_dualNorm_mul p (-x) g)
    nlinarith
  · exact Seminorm.inner_le_dualNorm_mul p x g

/-- Helper for Theorem 2.6: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 2.6: scalarizing the gradient along a line differentiates to the Hessian
pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hf_C2 : ContDiff ℝ 2 f) (x d u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    -- A `C²` function has a differentiable Fréchet derivative field.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      (hf_C2.contDiffAt (x := x + t • d)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map to differentiate it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the derivative of the affine line.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 2.6: a positive operator with a diagonal quadratic-form bound also controls
mixed pairings. -/
private theorem mixed_pairing_le_of_isPositive_and_quadratic_form_bound
    {A : E →L[ℝ] E}
    (hApos : A.IsPositive)
    (hAupper : ∀ v : E, inner ℝ (A v) v ≤ (L : ℝ) * (p v) ^ 2) :
    ∀ d u : E, |inner ℝ (A d) u| ≤ (L : ℝ) * p d * p u := by
  intro d u
  let a : ℝ := inner ℝ (A u) u
  let b : ℝ := 2 * inner ℝ (A d) u
  let c : ℝ := inner ℝ (A d) d
  have hpoly : ∀ α : ℝ, 0 ≤ a * (α * α) + b * α + c := by
    intro α
    have hnonneg := hApos.inner_nonneg_left (d + α • u)
    -- Expand the positive quadratic form on `d + α u` to a scalar quadratic in `α`.
    rw [show inner ℝ (A (d + α • u)) (d + α • u) = a * (α * α) + b * α + c by
      dsimp [a, b, c]
      calc
        inner ℝ (A (d + α • u)) (d + α • u)
            = inner ℝ (A d + α • A u) (d + α • u) := by simp [map_add, map_smul]
        _ = (inner ℝ (A d) d + inner ℝ (A d) (α • u)) +
              (inner ℝ (α • A u) d + inner ℝ (α • A u) (α • u)) := by
              rw [inner_add_right, inner_add_left, inner_add_left]
              ring
        _ = inner ℝ (A d) d + inner ℝ (A d) (α • u) +
              inner ℝ (α • A u) d + inner ℝ (α • A u) (α • u) := by
              ring_nf
        _ = inner ℝ (A d) d + α * inner ℝ (A d) u + α * inner ℝ (A u) d +
              (α * α) * inner ℝ (A u) u := by
              simp [real_inner_smul_right, real_inner_smul_left, mul_assoc]
        _ = inner ℝ (A d) d + α * inner ℝ (A d) u + α * inner ℝ (A d) u +
              (α * α) * inner ℝ (A u) u := by
              rw [show inner ℝ (A u) d = inner ℝ (A d) u by
                calc
                  inner ℝ (A u) d = inner ℝ u (A d) := hApos.inner_left_eq_inner_right _ _
                  _ = inner ℝ (A d) u := by simpa [real_inner_comm]]
        _ = a * (α * α) + b * α + c := by
              dsimp [a, b, c]
              ring] at hnonneg
    exact hnonneg
  have hdiscr : discrim a b c ≤ 0 := discrim_le_zero hpoly
  have hsq : (inner ℝ (A d) u) ^ 2 ≤ a * c := by
    -- Nonpositive discriminant gives the Cauchy--Schwarz bound for the positive form.
    rw [discrim, sq] at hdiscr
    dsimp [b] at hdiscr
    nlinarith
  have hbound_sq : (inner ℝ (A d) u) ^ 2 ≤ ((L : ℝ) * p d * p u) ^ 2 := by
    have hd : c ≤ (L : ℝ) * (p d) ^ 2 := by
      simpa [c] using hAupper d
    have hu : a ≤ (L : ℝ) * (p u) ^ 2 := by
      simpa [a] using hAupper u
    have ha_nonneg : 0 ≤ a := by
      simpa [a] using hApos.inner_nonneg_left u
    have hc_nonneg : 0 ≤ c := by
      simpa [c] using hApos.inner_nonneg_left d
    nlinarith
  have habs_sq : |inner ℝ (A d) u| ^ 2 ≤ ((L : ℝ) * p d * p u) ^ 2 := by
    simpa [sq_abs] using hbound_sq
  have hRnonneg : 0 ≤ (L : ℝ) * p d * p u := by positivity
  -- Take square roots in the ordered-field sense to recover the absolute-value estimate.
  nlinarith [abs_nonneg (inner ℝ (A d) u), hRnonneg, habs_sq]

/-- Helper for Theorem 2.6: a uniform pairing bound on the `p`-unit ball gives the dual-norm
bound. -/
private theorem dualNorm_le_of_unit_ball_pairing_bound {g : E} {C : ℝ}
    (hC : ∀ u : E, p u ≤ 1 → inner ℝ g u ≤ C) :
    ‖g‖[p,*] ≤ C := by
  -- Unfold the dual norm as the support function of the closed `p`-unit ball.
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · refine ⟨(0 : ℝ), ?_⟩
    refine ⟨(0 : E), ?_⟩
    constructor <;> simp
  · rintro y ⟨u, hu, rfl⟩
    exact hC u hu

/- Core/canonical layer: after Theorem 2.4 identifies convexity on the ambient real
finite-dimensional inner-product space with nonnegativity of the Hessian quadratic form, the only
extra second-order content of Theorem 2.6 is the upper quadratic bound. -/
namespace ConvexC1SeminormSmooth

/-- For a twice continuously differentiable smooth-convex objective, every Hessian quadratic form
is bounded above by the smoothness constant times `p(h)^2`. -/
theorem hessian_quadratic_form_upper_bound
    (hf : f ∈ 𝓕[L, p]¹¹) (hf_C2 : ContDiff ℝ 2 f) (x h : E) :
    inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ z ∈ Set.univ, ∀ v : E, 0 ≤ inner ℝ (hessian f z v) v :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  have hnonneg : 0 ≤ inner ℝ (hessian f x h) h := by
    -- The lower bound is exactly the Theorem 2.4 convexity-to-Hessian bridge.
    exact (hconvex_iff.mp hf.convexOn) x (Set.mem_univ x) h
  let φ : ℝ → ℝ := fun s ↦ inner ℝ (∇ f (x + s • h)) h
  have hφ_lip : LipschitzWith ⟨(L : ℝ) * (p h) ^ 2, by positivity⟩ φ := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro s t
    have hpair :=
      abs_inner_le_dualNorm_mul (p := p) h (∇ f (x + s • h) - ∇ f (x + t • h))
    have hgrad := hf.dualNorm_gradient_sub_le (x + s • h) (x + t • h)
    -- The defining gradient-Lipschitz inequality makes the scalarized line restriction Lipschitz.
    calc
      dist (φ s) (φ t)
          = |inner ℝ (∇ f (x + s • h) - ∇ f (x + t • h)) h| := by
              simp [φ, dist_eq_norm, inner_sub_left]
      _ ≤ ‖∇ f (x + s • h) - ∇ f (x + t • h)‖[p,*] * p h := hpair
      _ ≤ ((L : ℝ) * p ((x + s • h) - (x + t • h))) * p h := by
            gcongr
      _ = ((L : ℝ) * (|s - t| * p h)) * p h := by
            rw [show p ((x + s • h) - (x + t • h)) = |s - t| * p h by
              calc
                p ((x + s • h) - (x + t • h)) = p ((s - t) • h) := by
                  congr
                  calc
                    (x + s • h) - (x + t • h) = s • h - t • h := by abel_nf
                    _ = (s - t) • h := by rw [sub_smul]
                _ = |s - t| * p h := by simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (s - t) h)]
      _ = ((L : ℝ) * (p h) ^ 2) * dist s t := by
            rw [Real.dist_eq]
            ring_nf
  have hderiv := scalarized_gradient_line_hasDerivAt (f := f) hf_C2 x h h 0
  have hderiv_bound : |deriv φ 0| ≤ (L : ℝ) * (p h) ^ 2 := by
    -- A Lipschitz scalar function has derivative bounded by the same Lipschitz constant.
    simpa [φ, Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := 0) hφ_lip
  have hderiv_eq : deriv φ 0 = inner ℝ (hessian f x h) h := by
    -- Identify the derivative of the line restriction with the Hessian quadratic form.
    simpa [φ] using hderiv.deriv
  rw [hderiv_eq] at hderiv_bound
  exact (abs_le.mp hderiv_bound).2

/-- Conversely, a twice continuously differentiable convex objective whose Hessian quadratic form
is bounded above by `L * p(h)^2` belongs to `𝓕[L, p]¹¹`. -/
theorem of_convexOn_hessian_quadratic_form_upper_bound
    (hf_C2 : ContDiff ℝ 2 f) (hconvex : ConvexOn ℝ Set.univ f)
    (hupper : ∀ x h : E,
      inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2) :
    f ∈ 𝓕[L, p]¹¹ := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ z ∈ Set.univ, ∀ v : E, 0 ≤ inner ℝ (hessian f z v) v :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  have hnonneg : ∀ z v : E, 0 ≤ inner ℝ (hessian f z v) v := by
    -- Convexity gives pointwise positivity of the Hessian quadratic form.
    intro z v
    exact (hconvex_iff.mp hconvex) z (Set.mem_univ z) v
  have hpos : ∀ z : E, (hessian f z).IsPositive := by
    intro z
    -- Package the quadratic-form nonnegativity as positivity of the Hessian operator.
    exact (ContinuousLinearMap.isPositive_iff _).2
      ⟨fderiv_gradient_isSymmetric_of_contDiffAt (hf_C2.contDiffAt (x := z)), hnonneg z⟩
  let hf_C1 : ContDiff ℝ 1 f := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  refine ⟨⟨hf_C1.contDiffOn, hconvex⟩, ?_, ?_⟩
  · intro x hx
    -- The `C²` hypothesis supplies the ambient gradient witness required by `𝓕[L, p]¹¹`.
    exact (hf_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x).hasGradientAt
  · intro x hx y hy
    let d : E := x - y
    have hpair_bound :
        ∀ u : E, p u ≤ 1 → inner ℝ (∇ f x - ∇ f y) u ≤ (L : ℝ) * p d := by
      intro u hu
      let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (y + t • d)) u
      have hψ_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt ψ (inner ℝ (hessian f (y + t • d) d) u) (Set.Icc (0 : ℝ) 1) t := by
        intro t ht
        -- Differentiate the scalarized gradient along the segment from `x` to `y`.
        exact (scalarized_gradient_line_hasDerivAt (f := f) hf_C2 y d u t).hasDerivWithinAt
      have hψ_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
          ‖inner ℝ (hessian f (y + t • d) d) u‖ ≤ (L : ℝ) * p d := by
        intro t ht
        have hmixed := mixed_pairing_le_of_isPositive_and_quadratic_form_bound (p := p) (L := L)
          (hpos (y + t • d)) (hupper (y + t • d)) d u
        have hpu_le : (L : ℝ) * p d * p u ≤ (L : ℝ) * p d := by
          have hd_nonneg : 0 ≤ p d := by positivity
          have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
          have hmul : p d * p u ≤ p d := by
            calc
              p d * p u ≤ p d * 1 := by
                gcongr
              _ = p d := by ring
          nlinarith
        exact hmixed.trans hpu_le
      have hsegment := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ) hψ_deriv hψ_bound
      have hrewrite : ψ 1 - ψ 0 = inner ℝ (∇ f x - ∇ f y) u := by
        simp [ψ, d, inner_sub_left]
      have habs : |inner ℝ (∇ f x - ∇ f y) u| ≤ (L : ℝ) * p d := by
        -- Integrate the derivative bound along the segment to control the endpoint pairing.
        simpa [Real.dist_eq, dist_eq_norm, hrewrite] using hsegment
      exact (abs_le.mp habs).2
    -- Convert the unit-ball pairing bound into the dual-norm Lipschitz estimate.
    simpa [d] using dualNorm_le_of_unit_ball_pairing_bound (p := p) hpair_bound

end ConvexC1SeminormSmooth

/-- Theorem 2.6: for a twice continuously differentiable function on a finite-dimensional real
inner-product space,
belonging to `𝓕[L, p]¹¹` is equivalent to the Hessian quadratic form being
nonnegative and bounded above by `L * p(h)^2` in every direction. The textbook `ℝⁿ` statement is
the finite-dimensional specialization. -/
-- Proof sketch: the owner theorem
-- `ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound` isolates the genuinely new
-- second-order content, namely the upper Hessian quadratic-form bound. The lower bound is
-- exactly the Theorem 2.4 bridge from convexity of `f` on `Set.univ` to nonnegativity of the
-- Hessian quadratic form.
theorem convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
    (hf_C2 : ContDiff ℝ 2 f) :
    f ∈ 𝓕[L, p]¹¹ ↔
      ∀ x h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ x ∈ Set.univ, ∀ h : E, 0 ≤ inner ℝ (hessian f x h) h :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  constructor
  · intro hf x h
    exact
      ⟨(hconvex_iff.mp hf.convexOn) x (Set.mem_univ x) h,
        ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound hf hf_C2 x h⟩
  · intro hquad
    have hconvex : ConvexOn ℝ Set.univ f := by
      refine hconvex_iff.mpr ?_
      intro x hx h'
      simpa using (hquad x h').1
    exact
      ConvexC1SeminormSmooth.of_convexOn_hessian_quadratic_form_upper_bound
        hf_C2 hconvex (fun x h ↦ (hquad x h).2)

end

end
