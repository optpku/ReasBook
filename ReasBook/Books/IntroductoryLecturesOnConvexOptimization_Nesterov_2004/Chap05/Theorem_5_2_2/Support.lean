/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped DikinEllipsoidNotation Gradient HessianLocalNorm NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section CommonHelpers

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

/-- Helper for Theorem 5.2.2: nonnegative scalar dilations scale the Hessian local norm at a
point with positive Hessian. -/
theorem hessianLocalNorm_smul_of_nonneg
    {x u : E} (hPos : (hessian f x).IsPositive) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; x] = τ * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hPos.inner_nonneg_right u
  -- Expand the local norm and pull the nonnegative scalar through the square root.
  calc
    ‖τ • u‖[f; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.2.2: the inverse-Hessian gradient pairing is nonnegative at a
self-concordant domain point. -/
theorem inverse_hessian_gradient_pairing_nonneg
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    0 ≤ inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
  let v := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hquad : 0 ≤ inner ℝ v (hessian f x v) := hPos.inner_nonneg_right v
  have hHv : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  -- Rewrite the positive quadratic form of the Newton direction back to the gradient pairing.
  calc
    0 ≤ inner ℝ v (hessian f x v) := hquad
    _ = inner ℝ (∇ f x) v := by rw [hHv, real_inner_comm]
    _ = inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
      rfl

/-- Helper for Theorem 5.2.2: the Newton displacement is exactly the negative step size times the
inverse-Hessian gradient direction. -/
theorem next_point_sub_eq_neg_stepSize_smul_inverse_gradient
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let α := selfConcordantNewtonStepSize f Mf variant x hx hH
    selfConcordantNewtonNextPoint f Mf variant x hx hH - x =
      -(α • (hessian f x).inverse (∇ f x)) := by
  dsimp [selfConcordantNewtonStepSize]
  -- Subtract the base point from the explicit one-step Newton formula.
  rw [selfConcordantNewtonNextPoint_def]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Theorem 5.2.2: the base local norm of the Newton displacement equals the step
size times the Newton decrement. -/
theorem next_point_sub_localNorm_eq_stepSize_mul_ndec
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let δ := ndec(f, x, Mf, hx, hH)
    let α := selfConcordantNewtonStepSize f Mf variant x hx hH
    ‖selfConcordantNewtonNextPoint f Mf variant x hx hH - x‖[f; x] = α * δ := by
  let δ := ndec(f, x, Mf, hx, hH)
  let α := selfConcordantNewtonStepSize f Mf variant x hx hH
  let v : E := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hα_nonneg : 0 ≤ α := le_of_lt (selfConcordantNewtonStepSize_pos f Mf variant x hx hH)
  have hv_eq : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  have hv_norm : ‖v‖[f; x] = δ := by
    -- The local norm of the Newton direction is exactly the Newton decrement.
    rw [hessianLocalNorm_def]
    calc
      Real.sqrt (inner ℝ v (hessian f x v))
          = Real.sqrt (inner ℝ (∇ f x) v) := by rw [hv_eq, real_inner_comm]
      _ = δ := by
        simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm
  -- Rewrite the displacement and scale the local norm by the positive step size.
  calc
    ‖selfConcordantNewtonNextPoint f Mf variant x hx hH - x‖[f; x]
        = ‖α • v‖[f; x] := by
            rw [next_point_sub_eq_neg_stepSize_smul_inverse_gradient (Mf := Mf) (f := f)
              variant hx hH]
            rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[f; x] := hessianLocalNorm_smul_of_nonneg (f := f) hPos hα_nonneg
    _ = α * δ := by rw [hv_norm]

/-- Helper for Theorem 5.2.2: a quadratic family bounded above by `c` forces the discriminant
estimate `a² ≤ b c`. -/
theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Split on the degenerate quadratic coefficient and test the family at the critical point.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have ha_eq_zero : a = 0 := by
        by_contra ha_ne
        have htest := hline ((|c| + 1) / a)
        have hcontr : 2 * (|c| + 1) ≤ c := by
          have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
            simpa [hb_zero] using htest
          field_simp [ha_ne] at hrew
          linarith
        have habs : c ≤ |c| := le_abs_self c
        have hbad : |c| + 2 ≤ 0 := by
          nlinarith
        have hpos : 0 < |c| + 2 := by
          nlinarith [abs_nonneg c]
        exact (not_le_of_gt hpos) hbad
      exact (ha_zero ha_eq_zero).elim
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Theorem 5.2.2: squaring the Hessian local norm recovers the underlying quadratic
form. -/
theorem sq_hessianLocalNorm_eq_inner_hessian
    {x u : E} (hPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
  -- The positivity of `∇²f(x)` makes the square-root definition exact after squaring.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt (hPos.inner_nonneg_right u)

/-- Helper for Theorem 5.2.2: the square of the Hessian local norm satisfies the parallelogram
identity induced by the Hessian quadratic form. -/
theorem hessianLocalNorm_parallelogram_sq
    {x u v : E} (hPos : (hessian f x).IsPositive) :
    ‖u + v‖[f; x] ^ (2 : ℕ) + ‖u - v‖[f; x] ^ (2 : ℕ) =
      2 * (‖u‖[f; x] ^ (2 : ℕ) + ‖v‖[f; x] ^ (2 : ℕ)) := by
  have hsymm :
      inner ℝ u (hessian f x v) = inner ℝ v (hessian f x u) := by
    simpa [real_inner_comm] using hPos.isSymmetric v u
  -- Expand the Hessian-local quadratic form on `u ± v` and cancel the mixed terms by symmetry.
  rw [sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) (u := u + v) hPos]
  rw [sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) (u := u - v) hPos]
  rw [sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) (u := u) hPos]
  rw [sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) (u := v) hPos]
  simp [ContinuousLinearMap.map_add, sub_eq_add_neg, inner_add_left, inner_add_right, hsymm]
  ring

/-- Helper for Theorem 5.2.2: affine lines have the expected derivative. -/
theorem line_hasDerivAt
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar parameter while keeping the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.2.2: every affine parameter `t ∈ [0, 1]` produces the corresponding
point on `segment ℝ x y`. -/
theorem segment_point_mem_segment
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine interpolation point into the canonical line-map description of the
  -- segment.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 5.2.2: every point on the segment from `x` to `y` stays in the convex
self-concordant domain. -/
theorem segment_point_mem
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the segment point as a convex combination and use domain convexity.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have hconv := hself.convex_domain
  have h1t : 0 ≤ 1 - t := by
    linarith
  have hsum : (1 - t) + t = 1 := by
    ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5.2.2: the Hessian is continuous on the self-concordant domain. -/
theorem hessian_continuousOn :
    IsSelfConcordantOnWith dom Mf f → ContinuousOn (hessian f) dom := by
  intro hself
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the gradient once more on the open domain to reach the Hessian.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5.2.2: scalarizing the gradient along an affine segment differentiates to
the corresponding Hessian pairing. -/
theorem scalarized_gradient_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxt)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional to obtain the one-dimensional derivative.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.2.2: each affine segment point inherits the pointwise Hessian comparison
with the base point Hessian. -/
theorem segment_point_hessian_bounds
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ((1 - τ * a) ^ (2 : ℕ)) • hessian f x ≤ hessian f z ∧
      hessian f z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hy : y ∈ dom :=
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset hself hx hxy
  have hz : z ∈ dom := by
    exact segment_point_mem (hself := hself) hx hy hτ.1 hτ.2
  have hxPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  have hz_norm : ‖z - x‖[f; x] = τ * r := by
    calc
      ‖z - x‖[f; x] = ‖τ • (y - x)‖[f; x] := by
        have hz_sub : z - x = τ • (y - x) := by
          dsimp [z]
          abel
        rw [hz_sub]
      _ = τ * ‖y - x‖[f; x] := hessianLocalNorm_smul_of_nonneg (f := f) hxPos hτ_nonneg
      _ = τ * r := by rfl
  have hτr_le : τ * r ≤ r := by
    have hmul_le : τ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    simpa using hmul_le
  let rmid : ℝ := (r + 1 / (Mf : ℝ)) / 2
  have hr_lt_rmid : r < rmid := by
    dsimp [rmid]
    linarith
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[f; x](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    have hz_norm_le_r : ‖z - x‖[f; x] ≤ r := by
      rw [hz_norm]
      simpa using hτr_le
    exact lt_of_le_of_lt hz_norm_le_r hr_lt_rmid
  -- Compare `∇²f(z)` to `∇²f(x)` at the exact segment radius, using `rmid` only to discharge
  -- the strict Dikin-radius side condition.
  simpa [a, hz_norm, mul_assoc, mul_left_comm, mul_comm] using
    IsSelfConcordantOnWith.hessian_loewner_bounds_of_exact_local_radius
      (dom := dom) (Mf := Mf) (f := f) hself (x := x) (y := z) (r := rmid) hx hz hrmid_lt
      hz_mem_rmid

/-- Helper for Theorem 5.2.2: a Loewner upper bound on Hessians yields the corresponding local
norm comparison after taking square roots. -/
theorem hessianLocalNorm_le_mul_of_loewner_upper_early
    {x y v : E} {c : ℝ} (hc : 0 ≤ c) (hcmp : hessian f y ≤ c • hessian f x) :
    ‖v‖[f; y] ≤ Real.sqrt c * ‖v‖[f; x] := by
  have hgap_pos :
      (c • hessian f x - hessian f y).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hcmp
  have hinner_le :
      inner ℝ v (hessian f y v) ≤ c * inner ℝ v (hessian f x v) := by
    have hquad_gap :
        0 ≤ inner ℝ v ((c • hessian f x - hessian f y) v) :=
      hgap_pos.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right] using hquad_gap
  -- Scalarize the Loewner comparison on the test vector and then take square roots.
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  calc
    Real.sqrt (inner ℝ v (hessian f y v))
        ≤ Real.sqrt (c * inner ℝ v (hessian f x v)) := by
          exact Real.sqrt_le_sqrt hinner_le
    _ = Real.sqrt c * Real.sqrt (inner ℝ v (hessian f x v)) := by
          rw [Real.sqrt_mul hc]

/-- Helper for Theorem 5.2.2: subtracting symmetric Hessian-type operators preserves symmetry. -/
theorem hessianDifference_isSymmetricPairing
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (A - B).IsSymmetric := by
  -- Rewrite the pairing of the difference termwise and use symmetry on each summand.
  have hA' : ∀ s t : E, inner ℝ (A s) t = inner ℝ s (A t) := by
    intro s t
    simpa using hA s t
  have hB' : ∀ s t : E, inner ℝ (B s) t = inner ℝ s (B t) := by
    intro s t
    simpa using hB s t
  intro s t
  calc
    inner ℝ ((A - B) s) t = inner ℝ (A s) t - inner ℝ (B s) t := by
      simp [inner_sub_left]
    _ = inner ℝ s (A t) - inner ℝ s (B t) := by
      rw [hA' s t, hB' s t]
    _ = inner ℝ s ((A - B) t) := by
      simp [inner_sub_right]

/-- Helper for Theorem 5.2.2: Loewner order is preserved after adding a fixed operator on the
right. -/
theorem loewnerAddRight_bridge
    {A B C : E →L[ℝ] E} (h : A ≤ B) :
    A + C ≤ B + C := by
  -- Move to the positivity definition and simplify the common right summand away.
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change ((B + C) - (A + C)).IsPositive
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

/-- Helper for Theorem 5.2.2: Loewner order is preserved after adding a fixed operator on the
left. -/
theorem loewnerAddLeft_bridge
    {A B C : E →L[ℝ] E} (h : A ≤ B) :
    C + A ≤ C + B := by
  -- The common left summand cancels after rewriting the order as positivity of a difference.
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change ((C + B) - (C + A)).IsPositive
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

/-- Helper for Theorem 5.2.2: a nonnegative scalar preserves Loewner order on Hessian-type
operators. -/
theorem loewnerSmul_mono_of_nonneg
    {A : E →L[ℝ] E} (hA : 0 ≤ A) {a b : ℝ} (hab : a ≤ b) :
    a • A ≤ b • A := by
  have hA' : A.IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hA
  have hba_nonneg : 0 ≤ b - a := by
    linarith
  -- Scale the positive operator `A` by the nonnegative gap `b - a`.
  rw [ContinuousLinearMap.le_def]
  simpa [sub_smul] using hA'.smul_of_nonneg hba_nonneg

/-- Helper for Theorem 5.2.2: scaling both sides of a Loewner inequality by the same nonnegative
scalar preserves the inequality. -/
theorem loewnerSmul_bridge
    {A B : E →L[ℝ] E} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change (c • B - c • A).IsPositive
  simpa [smul_sub] using h'.smul_of_nonneg hc

/-- Helper for Theorem 5.2.2: the tail of an admissible Dikin segment has the transported local
norm bound at the intermediate point. -/
theorem segment_tail_localNorm_le
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖y - z‖[f; z] ≤ ((1 - τ) * r) / (1 - τ * a) := by
  dsimp
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have h1τ_nonneg : 0 ≤ 1 - τ := by
    linarith [hτ.2]
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - τ * a := by
    have hτa_le_a : τ * a ≤ a := by
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        exact mul_nonneg Mf.2 (hessianLocalNorm_nonneg f x (y - x))
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hz_norm : ‖y - z‖[f; x] = (1 - τ) * r := by
    -- Rewrite the tail displacement as the remaining scalar multiple of `y - x`.
    have hyz :
        y - z = (1 - τ) • (y - x) := by
      calc
        y - z = y - (x + τ • (y - x)) := by rfl
        _ = y - x - τ • (y - x) := by abel
        _ = (1 - τ) • (y - x) := by
              rw [sub_smul, one_smul]
    rw [hyz, hessianLocalNorm_smul_of_nonneg
      ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx) h1τ_nonneg]
  have hz_bound :
      hessian f z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
    simpa [r, a, z] using
      (segment_point_hessian_bounds (hself := hself) (x := x) (y := y) hx hxy
        (τ := τ) hτ).2
  have hsqrt :
      Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) = 1 / (1 - τ * a) := by
    have hfactor_nonneg : 0 ≤ 1 / (1 - τ * a) := by
      positivity
    rw [show (((1 - τ * a) ^ (2 : ℕ))⁻¹ : ℝ) = (1 / (1 - τ * a)) ^ (2 : ℕ) by
      field_simp [hfactor_pos.ne']]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
  -- Compare the tail displacement in the intermediate and base metrics, then rewrite the base
  -- metric using the scalar tail factor `1 - τ`.
  calc
    ‖y - z‖[f; z] ≤ Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖y - z‖[f; x] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper_early (f := f) (x := x) (y := z)
        (v := y - z) (by positivity) hz_bound
    _ = (1 / (1 - τ * a)) * ‖y - z‖[f; x] := by
      rw [hsqrt]
    _ = ((1 - τ) * r) / (1 - τ * a) := by
      rw [hz_norm]
      field_simp [hfactor_pos.ne']

/-- Helper for Theorem 5.2.2: an intermediate segment point compares to the endpoint Hessian
metric with the exact transport factor `((1 - τ * a) / (1 - a))`. -/
theorem segment_point_localNorm_le_endpointFactor
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (v : E) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[f; z] ≤ ((1 - τ * a) / (1 - a)) * ‖v‖[f; y] := by
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hτ)
  have htail :
      ‖y - z‖[f; z] ≤ ((1 - τ) * r) / (1 - τ * a) := by
    simpa [r, a, z] using
      segment_tail_localNorm_le (Mf := Mf) (f := f) hx hy hxy (τ := τ) hτ
  let ρ : ℝ := ‖y - z‖[f; z]
  let rmid : ℝ := (ρ + 1 / (Mf : ℝ)) / 2
  have hρ_lt : ρ < 1 / (Mf : ℝ) := by
    have htail_lt : ((1 - τ) * r) / (1 - τ * a) < 1 / (Mf : ℝ) := by
      have hτa_le_a : τ * a ≤ a := by
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mul_nonneg Mf.2 (hessianLocalNorm_nonneg f x (y - x))
        simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
      have hfactor_posτ : 0 < 1 - τ * a := by
        linarith
      have hmul :
          (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) < 1 := by
        have hrew :
            (Mf : ℝ) * (((1 - τ) * r) / (1 - τ * a)) =
              ((1 - τ) * a) / (1 - τ * a) := by
          dsimp [a]
          field_simp [hfactor_posτ.ne']
        rw [hrew]
        have hnum_lt_den : (1 - τ) * a < 1 - τ * a := by
          linarith
        exact (div_lt_iff₀ hfactor_posτ).2 (by simpa using hnum_lt_den)
      exact (lt_div_iff₀ hMf_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    exact lt_of_le_of_lt htail htail_lt
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hy_mem_rmid : y ∈ W⁰[f; z](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    dsimp [rmid, ρ]
    linarith
  have hloewner :
      ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) • hessian f z ≤ hessian f y := by
    simpa [ρ] using
      (hself.hessian_loewner_bounds_of_exact_local_radius
        (x := z) (y := y) (r := rmid) hz hy hrmid_lt hy_mem_rmid).1
  have hcmp : hessian f z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian f y := by
    have hcoeff_nonneg : 0 ≤ (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ) := by positivity
    have hscaled := loewnerSmul_bridge hloewner hcoeff_nonneg
    have hpow_ne : (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) ≠ 0 := by
      have hfac : 0 < 1 - (Mf : ℝ) * ρ := by
        have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
          simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
        linarith
      exact pow_ne_zero 2 hfac.ne'
    have hone :
        ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) = 1 := by
      exact inv_mul_cancel₀ hpow_ne
    calc
      hessian f z =
          ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) •
            hessian f z := by
              simp [hone]
      _ ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian f y := by
            simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hρ_factor :
      1 / (1 - (Mf : ℝ) * ρ) ≤ (1 - τ * a) / (1 - a) := by
    have hden_posρ : 0 < 1 - (Mf : ℝ) * ρ := by
      have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
        simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
      linarith
    have hτa_factor_pos : 0 < 1 - τ * a := by
      have hτa_le_a : τ * a ≤ a := by
        have ha_nonneg : 0 ≤ a := by
          dsimp [a]
          exact mul_nonneg Mf.2 (hessianLocalNorm_nonneg f x (y - x))
        simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
      linarith
    have hρ_upper : (Mf : ℝ) * ρ ≤ ((1 - τ) * a) / (1 - τ * a) := by
      have hMf_nonneg : 0 ≤ (Mf : ℝ) := le_of_lt hMf_pos
      have hρ_upper_raw := mul_le_mul_of_nonneg_left htail hMf_nonneg
      dsimp [ρ, a] at hρ_upper_raw ⊢
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hρ_upper_raw
    have hfactor_lower :
        (1 - a) / (1 - τ * a) ≤ 1 - (Mf : ℝ) * ρ := by
      have hrewrite :
          1 - ((1 - τ) * a) / (1 - τ * a) = (1 - a) / (1 - τ * a) := by
        field_simp [hτa_factor_pos.ne']
        ring
      rw [← hrewrite]
      linarith
    have hleft_pos : 0 < (1 - a) / (1 - τ * a) := by
      positivity
    have hrecip :
        1 / (1 - (Mf : ℝ) * ρ) ≤ 1 / ((1 - a) / (1 - τ * a)) := by
      exact (one_div_le_one_div hden_posρ hleft_pos).2 hfactor_lower
    simpa [div_eq_mul_inv] using hrecip
  have hsqrt :
      Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) ≤ (1 - τ * a) / (1 - a) := by
    have hden_posρ : 0 < 1 - (Mf : ℝ) * ρ := by
      have hmul_lt_one : (Mf : ℝ) * ρ < 1 := by
        simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
      linarith
    have hsqrt_eq :
        Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) = 1 / (1 - (Mf : ℝ) * ρ) := by
      have hfactor_nonneg : 0 ≤ 1 / (1 - (Mf : ℝ) * ρ) := by positivity
      rw [show ((((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ : ℝ)) =
          (1 / (1 - (Mf : ℝ) * ρ)) ^ (2 : ℕ) by
            field_simp [hden_posρ.ne']
            ]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
    rw [hsqrt_eq]
    exact hρ_factor
  -- Route correction: reuse the exact-tail-radius comparison at `(z,y)` so the endpoint metric
  -- is reached directly in the primal norm, instead of reopening the coarse residual branch.
  calc
    ‖v‖[f; z] ≤ Real.sqrt (((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹) * ‖v‖[f; y] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper_early
        (f := f) (x := y) (y := z) (v := v) (by positivity) hcmp
    _ ≤ ((1 - τ * a) / (1 - a)) * ‖v‖[f; y] := by
      exact mul_le_mul_of_nonneg_right hsqrt (hessianLocalNorm_nonneg f y v)

/-- Helper for Theorem 5.2.2: integrating the Hessian along the segment from `x` to `y`
recovers the gradient increment when paired against any fixed direction. -/
theorem gradient_difference_pairing_eq_average_hessian_step
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let d := y - x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • d)
    inner ℝ (∇ f y - ∇ f x) u = inner ℝ (G d) u := by
  let d : E := y - x
  let H : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, H τ
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
  have hH_cont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment joining `x` and `y`.
    simpa [H, d] using
      (hessian_continuousOn (dom := dom) (Mf := Mf) (f := f) hself).comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hline_maps
  have hH_int : IntervalIntegrable H MeasureTheory.volume 0 1 :=
    hH_cont.intervalIntegrable_of_Icc (by norm_num)
  have hH_apply_cont (v : E) : ContinuousOn (fun τ : ℝ ↦ H τ v) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    simpa [H, ev] using ev.continuous.comp_continuousOn hH_cont
  have hH_apply_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ H τ v) MeasureTheory.volume 0 1 :=
    (hH_apply_cont v).intervalIntegrable_of_Icc (by norm_num)
  let g : ℝ → ℝ := fun τ ↦ inner ℝ (∇ f (x + τ • d)) u
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ (H τ d) u
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact
      (scalarized_gradient_line_hasDerivAt (hself := hself)
        (x := x) (d := d) (u := u) (hxt := hline_maps hτ)).continuousAt.continuousWithinAt
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 := by
    have hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) 1) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
      simpa [θ, H, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        φ.continuous.comp_continuousOn (hH_apply_cont d)
    exact hθ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (θ τ) τ := by
    intro τ hτ
    simpa [g, θ, H] using
      scalarized_gradient_line_hasDerivAt (hself := hself)
        (x := x) (d := d) (u := u) (hxt := hline_maps (Set.mem_Icc_of_Ioo hτ))
  have hftc : ∫ τ in (0 : ℝ)..1, θ τ = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hθ_int
  have hpair_integral : ∫ τ in (0 : ℝ)..1, θ τ = inner ℝ u (G d) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
    calc
      ∫ τ in (0 : ℝ)..1, θ τ = ∫ τ in (0 : ℝ)..1, φ (H τ d) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro τ
        simp [θ, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm]
      _ = φ (∫ τ in (0 : ℝ)..1, H τ d) := by
        exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hH_apply_int d)
      _ = inner ℝ u (∫ τ in (0 : ℝ)..1, H τ d) := by
        simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ u (G d) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hH_int d]
  -- The scalar fundamental theorem of calculus turns the gradient increment into the segment
  -- average Hessian applied to the displacement.
  calc
    inner ℝ (∇ f y - ∇ f x) u = g 1 - g 0 := by
      rw [inner_sub_left]
      simp [g, d]
    _ = ∫ τ in (0 : ℝ)..1, θ τ := by
      symm
      exact hftc
    _ = inner ℝ u (G d) := hpair_integral
    _ = inner ℝ (G d) u := real_inner_comm _ _

/-- Helper for Theorem 5.2.2: a symmetric operator bounded between `-c ∇²f(x)` and
`c ∇²f(x)` has Hessian-metric operator norm at most `c`. -/
theorem abs_inner_le_mul_localNorm_of_operator_sandwich
    {x u v : E} (hPos : (hessian f x).IsPositive) (K : E →L[ℝ] E) {c : ℝ}
    (hc : 0 ≤ c) (hK_symm : K.IsSymmetric)
    (hlower : -(c • hessian f x) ≤ K) (hupper : K ≤ c • hessian f x) :
    |inner ℝ v (K u)| ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
  let H := hessian f x
  have hH_symm : H.IsSymmetric := hPos.isSymmetric
  have hminus_pos : (c • H - K).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hupper
  have hplus_pos : (c • H + K).IsPositive := by
    have htmp : (K - -(c • H)).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hlower
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
  have hu_quad_nonneg : 0 ≤ c * inner ℝ u (H u) := by
    exact mul_nonneg hc (hPos.inner_nonneg_right u)
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v (K u) - t ^ (2 : ℕ) * (c * inner ℝ u (H u)) ≤
          c * inner ℝ v (H v) := by
    intro t
    have hsum_nonneg :
        0 ≤
          inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) := by
      exact add_nonneg (hplus_pos.inner_nonneg_right (v - t • u))
        (hminus_pos.inner_nonneg_right (v + t • u))
    have hHu : inner ℝ u (H v) = inner ℝ v (H u) := by
      simpa [real_inner_comm] using hH_symm v u
    have hKu : inner ℝ u (K v) = inner ℝ v (K u) := by
      simpa [real_inner_comm] using hK_symm v u
    have hsum_formula :
        inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) =
          2 * c * inner ℝ v (H v) - 4 * t * inner ℝ v (K u) +
            2 * t ^ (2 : ℕ) * (c * inner ℝ u (H u)) := by
      simp [H, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_sub, hHu, hKu, pow_two]
      ring
    rw [hsum_formula] at hsum_nonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v (K u)) ^ (2 : ℕ) ≤
        (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := by
    have hsq :=
      sq_le_mul_of_quadratic_family
        (a := inner ℝ v (K u))
        (b := c * inner ℝ u (H u))
        (c := c * inner ℝ v (H v))
        hu_quad_nonneg hline
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
  have hu_sq : ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (H u) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right u)
  have hv_sq : ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ v (H v) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right v)
  have hsq_abs :
      |inner ℝ v (K u)| ^ (2 : ℕ) ≤
        (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v (K u)| ^ (2 : ℕ) = (inner ℝ v (K u)) ^ (2 : ℕ) := by
        rw [sq_abs]
      _ ≤ (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := hsq_raw
      _ = c ^ (2 : ℕ) * (‖v‖[f; x] ^ (2 : ℕ) * ‖u‖[f; x] ^ (2 : ℕ)) := by
        rw [hu_sq, hv_sq]
        ring
      _ = (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hright_nonneg : 0 ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
    exact mul_nonneg (mul_nonneg hc (hessianLocalNorm_nonneg f x v))
      (hessianLocalNorm_nonneg f x u)
  exact le_of_sq_le_sq hsq_abs hright_nonneg

/-- Helper for Theorem 5.2.2: a symmetric operator whose quadratic form is bounded by
`c ‖·‖[f; x]^2` also satisfies the corresponding mixed Hessian-local pairing bound. -/
theorem abs_inner_le_mul_localNorm_of_symmetric_quadratic_bound
    {x u v : E} (hPos : (hessian f x).IsPositive) (L : E →L[ℝ] E) {c : ℝ}
    (hc : 0 ≤ c) (hL_symm : L.IsSymmetric)
    (hdiag : ∀ w : E, |inner ℝ w (L w)| ≤ c * ‖w‖[f; x] ^ (2 : ℕ)) :
    |inner ℝ v (L u)| ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
  have hsmul_sq (t : ℝ) :
      ‖t • v‖[f; x] ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
    -- Expand the scaled Hessian quadratic form before simplifying the scalar factor.
    calc
      ‖t • v‖[f; x] ^ (2 : ℕ) = inner ℝ (t • v) (hessian f x (t • v)) := by
        exact sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) hPos
      _ = t ^ (2 : ℕ) * inner ℝ v (hessian f x v) := by
        simp [pow_two, inner_smul_left, inner_smul_right, mul_assoc]
      _ = t ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
        rw [← sq_hessianLocalNorm_eq_inner_hessian (f := f) (x := x) (u := v) hPos]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v (L u) - t ^ (2 : ℕ) * (c * ‖v‖[f; x] ^ (2 : ℕ)) ≤
          c * ‖u‖[f; x] ^ (2 : ℕ) := by
    intro t
    have hcross :
        inner ℝ u (L v) = inner ℝ v (L u) := by
      simpa [real_inner_comm] using hL_symm v u
    have hpolar :
        inner ℝ (t • v + u) (L (t • v + u)) -
            inner ℝ (t • v - u) (L (t • v - u)) =
          4 * t * inner ℝ v (L u) := by
      -- Polarize the symmetric quadratic form in the `v/u` directions.
      simp [ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        hcross]
      ring
    have hplus :
        inner ℝ (t • v + u) (L (t • v + u)) ≤
          c * ‖t • v + u‖[f; x] ^ (2 : ℕ) := by
      exact le_trans (le_abs_self _) (hdiag (t • v + u))
    have hminus :
        -inner ℝ (t • v - u) (L (t • v - u)) ≤
          c * ‖t • v - u‖[f; x] ^ (2 : ℕ) := by
      exact le_trans (neg_le_abs _) (hdiag (t • v - u))
    have hquad :
        4 * t * inner ℝ v (L u) ≤
          c * ‖t • v + u‖[f; x] ^ (2 : ℕ) + c * ‖t • v - u‖[f; x] ^ (2 : ℕ) := by
      rw [← hpolar]
      linarith
    have hpar :
        ‖t • v + u‖[f; x] ^ (2 : ℕ) + ‖t • v - u‖[f; x] ^ (2 : ℕ) =
          2 * (t ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) + ‖u‖[f; x] ^ (2 : ℕ)) := by
      calc
        ‖t • v + u‖[f; x] ^ (2 : ℕ) + ‖t • v - u‖[f; x] ^ (2 : ℕ) =
            2 * (‖t • v‖[f; x] ^ (2 : ℕ) + ‖u‖[f; x] ^ (2 : ℕ)) := by
              simpa using
                hessianLocalNorm_parallelogram_sq (f := f) (x := x) (u := t • v) (v := u) hPos
        _ = 2 * (t ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) + ‖u‖[f; x] ^ (2 : ℕ)) := by
              rw [hsmul_sq]
    -- Combine the polarized quadratic estimate with the parallelogram identity.
    nlinarith [hquad, hpar]
  have hv_nonneg : 0 ≤ c * ‖v‖[f; x] ^ (2 : ℕ) := by
    exact mul_nonneg hc (sq_nonneg ‖v‖[f; x])
  have hsq_raw :
      (inner ℝ v (L u)) ^ (2 : ℕ) ≤
        (c * ‖v‖[f; x] ^ (2 : ℕ)) * (c * ‖u‖[f; x] ^ (2 : ℕ)) := by
    exact
      sq_le_mul_of_quadratic_family
        (a := inner ℝ v (L u))
        (b := c * ‖v‖[f; x] ^ (2 : ℕ))
        (c := c * ‖u‖[f; x] ^ (2 : ℕ))
        hv_nonneg hline
  have hsq_abs :
      |inner ℝ v (L u)| ^ (2 : ℕ) ≤
        (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v (L u)| ^ (2 : ℕ) = (inner ℝ v (L u)) ^ (2 : ℕ) := by
        rw [sq_abs]
      _ ≤ (c * ‖v‖[f; x] ^ (2 : ℕ)) * (c * ‖u‖[f; x] ^ (2 : ℕ)) := hsq_raw
      _ = (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hright_nonneg : 0 ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
    exact mul_nonneg (mul_nonneg hc (hessianLocalNorm_nonneg f x v))
      (hessianLocalNorm_nonneg f x u)
  exact le_of_sq_le_sq hsq_abs hright_nonneg

/-- Helper for Theorem 5.2.2: pairing a vector with an arbitrary direction is controlled by the
dual local norm at the base point times the local norm of the direction. -/
theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
    {x v z : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx) hH
        (toDual ℝ E v) * ‖z‖[f; x] := by
  let H := hessian f x
  let w := H.inverse v
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hHw : H w = v := by
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    -- Rewrite the positive Hessian quadratic form of `w` as the inverse-Hessian pairing.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      -- Expand the quadratic form and rewrite the mixed terms using `H w = v`.
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    have hsq :=
      sq_le_mul_of_quadratic_family (a := inner ℝ v z) (b := inner ℝ z (H z))
        (c := inner ℝ v w) hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[f; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    exact sq_hessianLocalNorm_eq_inner_hessian (f := f) hPos
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) * ‖z‖[f; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[f; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) * ‖z‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hdual_nonneg : 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg f x z))

/-- Helper for Theorem 5.2.2: the Chapter 2 dual norm of a separated seminorm is bounded above on
the image of the closed primal unit ball, so `le_csSup` can be applied pointwise. -/
theorem seminorm_dualNorm_bddAbove_innerImage_closedBall
    (p : Seminorm ℝ E) [p.IsNorm] (g : E) :
    BddAbove ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖g‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  -- The ambient Cauchy inequality turns the unit-ball bound into a uniform bound on the image.
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr

/-- Helper for Theorem 5.2.2: the Chapter 2 dual norm is subadditive after passing through the
Riesz identification. -/
theorem seminorm_dualNorm_add_le
    (p : Seminorm ℝ E) [p.IsNorm] (g h : E) :
    Seminorm.dualNorm p (g + h) ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := by
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu_ball : u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    have hg_le : inner ℝ g u ≤ Seminorm.dualNorm p g := by
      have hmem : inner ℝ g u ∈ ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p g) hmem
    have hh_le : inner ℝ h u ≤ Seminorm.dualNorm p h := by
      have hmem : inner ℝ h u ∈ ((fun y : E ↦ inner ℝ h y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p h) hmem
    -- Evaluate both covectors on the same primal unit-ball witness and bound each term separately.
    calc
      inner ℝ (g + h) u = inner ℝ g u + inner ℝ h u := by
        rw [inner_add_left]
      _ ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := add_le_add hg_le hh_le

/-- Helper for Theorem 5.2.2: the Hessian at a fixed point induces the positive-definite bilinear
form underlying the Hessian dual local norm. -/
theorem hessian_bilin_posDef_of_isPositive_of_isInvertible
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    ((((innerSL ℝ).comp (hessian F x)).toBilinForm).toQuadraticMap).PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro u
    change 0 ≤ inner ℝ (hessian F x u) u
    simpa [real_inner_comm] using hPos.inner_nonneg_right u
  · intro u hu
    change inner ℝ (hessian F x u) u = 0 at hu
    have hHu : hessian F x u = 0 := by
      obtain ⟨m, w, hA⟩ := (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hPos
      rw [hA] at hu ⊢
      have hsum : ∑ j : Fin m, (inner ℝ (w j) u) ^ (2 : ℕ) = 0 := by
        simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
          pow_two] using hu
      have hw : ∀ i : Fin m, inner ℝ (w i) u = 0 := by
        intro i
        exact sq_eq_zero_iff.mp <|
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ ↦ sq_nonneg (inner ℝ (w j) u))).mp hsum i (by simp)
      simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
    apply hInv.injective
    simpa using hHu

/-- Helper for Theorem 5.2.2: at a fixed point, the determinant-based Hessian dual local norm is
subadditive on covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_add_le
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g₁ g₂ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) ≤
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
        HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  let B : LinearMap.BilinForm ℝ E := ((innerSL ℝ).comp (hessian F x)).toBilinForm
  let hBPos : B.toQuadraticMap.PosDef :=
    hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let p : Seminorm ℝ E := B.primalSeminorm hBPos
  let v₁ : E := (InnerProductSpace.toDual ℝ E).symm g₁
  let v₂ : E := (InnerProductSpace.toDual ℝ E).symm g₂
  have hBPos_eq :
      hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv = hBPos :=
    Subsingleton.elim _ _
  have hsum :
      Seminorm.dualNorm p (v₁ + v₂) ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ :=
    seminorm_dualNorm_add_le p v₁ v₂
  have hleft :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := by
    trans B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv)
            ((g₁ + g₂).toLinearMap) =
          B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
      rw [hBPos_eq]
    · symm
      simpa [p, v₁, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos (v₁ + v₂))
  have hg₁ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ =
        Seminorm.dualNorm p v₁ := by
    trans B.dualNorm hBPos g₁.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) g₁.toLinearMap =
          B.dualNorm hBPos g₁.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₁] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₁)
  have hg₂ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ =
        Seminorm.dualNorm p v₂ := by
    trans B.dualNorm hBPos g₂.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) g₂.toLinearMap =
          B.dualNorm hBPos g₂.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₂)
  -- Move to the Chapter 2 dual norm, apply the triangle inequality there, and move back.
  calc
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := hleft
    _ ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ := hsum
    _ = HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
          HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
      rw [← hg₁, ← hg₂]

/-- Helper for Theorem 5.2.2: the fixed-point determinant-based Hessian dual local norm is even
on covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_neg
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (-g) =
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
  -- Expanding both sides shows that the minus signs cancel inside the inverse-Hessian pairing.
  rw [HessianDualLocalNorm.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
  simp

/-- Helper for Theorem 5.2.2: the fixed-point determinant-based Hessian dual local norm pulls out
absolute scalar factors from covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_smul
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g : StrongDual ℝ E) (a : ℝ) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (a • g) =
      |a| * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  by_cases ha : 0 ≤ a
  · -- Nonnegative scalars pull out directly by positive homogeneity of the dual local norm.
    simpa [HessianDualLocalNorm.ofDetNeZero, smul_eq_mul, abs_of_nonneg ha] using
      dualLocalNorm_smul_nonneg F x hPos hInv g ha
  · have ha_lt : a < 0 := lt_of_not_ge ha
    have hneg_nonneg : 0 ≤ -a := by linarith
    calc
      HessianDualLocalNorm.ofDetNeZero F x hPos hH (a • g) =
          HessianDualLocalNorm.ofDetNeZero F x hPos hH ((-a : ℝ) • (-g)) := by
        simp
      _ = (-a) * HessianDualLocalNorm.ofDetNeZero F x hPos hH (-g) := by
        simpa [HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
          dualLocalNorm_smul_nonneg F x hPos hInv (-g) hneg_nonneg
      _ = (-a) * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
        rw [hessianDualLocalNorm_ofDetNeZero_neg hPos hH]
      _ = |a| * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
        rw [abs_of_neg ha_lt]

/-- Helper for Theorem 5.2.2: the endpoint inverse-Hessian witness simultaneously realizes the
endpoint local norm and the squared endpoint dual norm of a covector. -/
theorem endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (k : E) :
    let H := hessian f x
    let w := H.inverse k
    ‖w‖[f; x] =
        HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx) hH
          (toDual ℝ E k) ∧
      inner ℝ k w =
        (HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx) hH
          (toDual ℝ E k)) ^ (2 : ℕ) := by
  let H := hessian f x
  let w := H.inverse k
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hHw : H w = k := by
    dsimp [H, w]
    exact hInv.self_apply_inverse k
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    -- Rewrite the positive endpoint Hessian quadratic form of `w` as the inverse-Hessian pairing.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ k w := by
        rw [hHw, real_inner_comm]
  refine ⟨?_, ?_⟩
  · -- The endpoint local norm of `w` is the endpoint dual norm of the residual covector.
    rw [hessianLocalNorm_def, HessianDualLocalNorm.ofDetNeZero_def]
    have hinner : inner ℝ w (H w) = inner ℝ k w := by
      rw [hHw, real_inner_comm]
    simpa [H, w, InnerProductSpace.toDual_apply_apply] using congrArg Real.sqrt hinner
  · -- Squaring the endpoint dual norm recovers the same inverse-Hessian pairing.
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [H, w, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      (Real.sq_sqrt hpair_nonneg).symm

/-- Helper for Theorem 5.2.2: a Loewner upper bound on Hessians yields the corresponding local
norm comparison after taking square roots. -/
theorem hessianLocalNorm_le_mul_of_loewner_upper
    {x y v : E} {c : ℝ} (hc : 0 ≤ c) (hcmp : hessian f y ≤ c • hessian f x) :
    ‖v‖[f; y] ≤ Real.sqrt c * ‖v‖[f; x] := by
  have hgap_pos :
      (c • hessian f x - hessian f y).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hcmp
  have hinner_le :
      inner ℝ v (hessian f y v) ≤ c * inner ℝ v (hessian f x v) := by
    have hquad_gap :
        0 ≤ inner ℝ v ((c • hessian f x - hessian f y) v) :=
      hgap_pos.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right] using hquad_gap
  -- Scalarize the Loewner comparison on the test vector and then take square roots.
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  calc
    Real.sqrt (inner ℝ v (hessian f y v))
        ≤ Real.sqrt (c * inner ℝ v (hessian f x v)) := by
          exact Real.sqrt_le_sqrt hinner_le
    _ = Real.sqrt c * Real.sqrt (inner ℝ v (hessian f x v)) := by
          rw [Real.sqrt_mul hc]

/-- Helper for Theorem 5.2.2: a primal local-norm comparison from `x` to `y` reverses to the
same factor on determinant-based Hessian dual local norms. -/
theorem hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le_common
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {c : ℝ} (hc : 0 ≤ c)
    (hnorm : ∀ z : E, ‖z‖[f; x] ≤ c * ‖z‖[f; y])
    (hHx : (hessian f x).det ≠ 0) (hHy : (hessian f y).det ≠ 0) (v : E) :
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hy)
        hHy (toDual ℝ E v) ≤
      c * HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx)
        hHx (toDual ℝ E v) := by
  let hPosX : (hessian f x).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hy
  let δx : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPosX hHx (toDual ℝ E v)
  let δy : ℝ := HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E v)
  let Hy : E →L[ℝ] E := hessian f y
  let w : E := Hy.inverse v
  have hw_realize : ‖w‖[f; y] = δy ∧ inner ℝ v w = δy ^ (2 : ℕ) := by
    -- Use the inverse-Hessian witness at `y` so the source dual norm appears as a squared pairing.
    simpa [δy, Hy, w] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := y) hy hHy v
  have hw_norm : ‖w‖[f; y] = δy := hw_realize.1
  have hpair_sq : inner ℝ v w = δy ^ (2 : ℕ) := hw_realize.2
  have hδx_nonneg : 0 ≤ δx := by
    change
      0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPosX hHx (toDual ℝ E v)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hδy_nonneg : 0 ≤ δy := by
    change
      0 ≤ HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E v)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_bound : |inner ℝ v w| ≤ δx * ‖w‖[f; x] := by
    -- Test the covector `toDual v` against the witness `w` in the base metric at `x`.
    simpa [δx] using
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
        (Mf := Mf) (f := f) (x := x) (v := v) (z := w) hx hHx
  have hw_transport : ‖w‖[f; x] ≤ c * δy := by
    simpa [hw_norm] using hnorm w
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    rw [hpair_sq]
    positivity
  have hsq_bound : δy ^ (2 : ℕ) ≤ δx * (c * δy) := by
    calc
      δy ^ (2 : ℕ) = inner ℝ v w := by symm; exact hpair_sq
      _ = |inner ℝ v w| := by rw [abs_of_nonneg hpair_nonneg]
      _ ≤ δx * ‖w‖[f; x] := hpair_bound
      _ ≤ δx * (c * δy) := by
            exact mul_le_mul_of_nonneg_left hw_transport hδx_nonneg
  by_cases hzero : δy = 0
  · change δy ≤ c * δx
    simpa [hzero] using mul_nonneg hc hδx_nonneg
  · have hδy_pos : 0 < δy := lt_of_le_of_ne hδy_nonneg (by simpa [eq_comm] using hzero)
    have hsq_bound' : δy ^ (2 : ℕ) ≤ c * δx * δy := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsq_bound
    nlinarith

/-- Helper for Theorem 5.2.2: the endpoint dual local norm is controlled by the base dual local
norm through the Dikin transport factor `(1 - M_f ‖y - x‖_x)⁻¹`. -/
theorem dualLocalNorm_transport_to_endpoint
    {x y v : E} (hx : x ∈ dom) (hHx : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) (hHy : (hessian f y).det ≠ 0) :
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive
          ((inferInstance : IsSelfConcordantOnWith dom Mf f).openDikinEllipsoid_inv_constant_subset
            hx hxy))
        hHy (toDual ℝ E v) ≤
      (1 / (1 - (Mf : ℝ) * ‖y - x‖[f; x])) *
        HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx)
          hHx (toDual ℝ E v) := by
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let c : ℝ := 1 / (1 - a)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hlower :
      ((1 - a) ^ (2 : ℕ)) • hessian f x ≤ hessian f y := by
    -- Specialize the exact segment-point Hessian comparison to the endpoint `τ = 1`.
    simpa [r, a] using
      (segment_point_hessian_bounds (hself := hself) (x := x) (y := y) hx hxy
        (τ := 1) (by constructor <;> norm_num)).1
  have hcmp : hessian f x ≤ (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) • hessian f y := by
    have hscaled :
        ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - a) ^ (2 : ℕ)) • hessian f x ≤
          (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) • hessian f y := by
      simpa [smul_smul] using
        loewnerSmul_bridge hlower
          (c := (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) (by positivity)
    have hone : ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - a) ^ (2 : ℕ)) = 1 := by
      field_simp [pow_ne_zero 2 hfactor_pos.ne']
    simpa [hone] using hscaled
  have hsqrt : Real.sqrt ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) = c := by
    have hpow : ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) = c ^ (2 : ℕ)) := by
      dsimp [c]
      field_simp [hfactor_pos.ne']
    rw [hpow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc_nonneg]
  have hnorm : ∀ z : E, ‖z‖[f; x] ≤ c * ‖z‖[f; y] := by
    intro z
    calc
      ‖z‖[f; x] ≤ Real.sqrt ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) * ‖z‖[f; y] := by
        exact hessianLocalNorm_le_mul_of_loewner_upper
          (f := f) (x := y) (y := x) (v := z) (by positivity) hcmp
      _ = c * ‖z‖[f; y] := by
        rw [hsqrt]
  -- Convert the primal comparison into the reversed endpoint dual comparison via the generic
  -- determinant-based inverse-witness bridge.
  simpa [hy, r, a, c] using
    hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le_common
      (Mf := Mf) (f := f) (x := x) (y := y) hx hy hc_nonneg hnorm hHx hHy v

/-- Helper for Theorem 5.2.2: the averaged-Hessian residual along an admissible Dikin segment is
controlled by the factor `a / (1 - a)`, where `a = M_f ‖y - x‖_x`. -/
theorem average_hessian_residual_pairing_bound
    {x y u v : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    |inner ℝ v ((hessian f x - G) u)| ≤
      (a / (1 - a)) * ‖v‖[f; x] * ‖u‖[f; x] := by
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let K : E →L[ℝ] E := H - G
  let c : ℝ := a / (1 - a)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hH_nonneg : 0 ≤ H := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive H).2 (hself.hessian_isPositive hx)
  have hG_lower :
      (1 - a + a ^ (2 : ℕ) / 3) • H ≤ G := by
    -- Rewrite the averaged-Hessian lower bound into the fixed `H/G/a` spelling.
    simpa [a, r, G, H, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_lower_bound
        (hself := hself) (x := x) (y := y) hx hxy
  have hG_upper : G ≤ (1 / (1 - a)) • H := by
    -- Rewrite the averaged-Hessian upper bound into the same normal form.
    simpa [a, r, G, H, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_upper_bound
        (hself := hself) (x := x) (y := y) hx hxy
  have hG_symm : G.IsSymmetric := by
    let d : E := y - x
    let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
    have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
    have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
      intro τ hτ
      exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
    have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
      -- Restrict the continuous Hessian field to the affine segment used in the average.
      simpa [Hτ, d] using
        (hessian_continuousOn (dom := dom) (Mf := Mf) (f := f) hself).comp
          (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
          hHτ_maps
    have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
      hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
    have hHτ_apply_cont (w : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ w) (Set.Icc (0 : ℝ) 1) := by
      let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E w
      simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
    have hHτ_apply_int (w : E) :
        IntervalIntegrable (fun τ : ℝ ↦ Hτ τ w) MeasureTheory.volume 0 1 :=
      (hHτ_apply_cont w).intervalIntegrable_of_Icc (by norm_num)
    have hpair_integral (s t : E) :
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) = inner ℝ s (G t) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) s
      calc
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t)
            = ∫ τ in (0 : ℝ)..1, φ (Hτ τ t) := by
                refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro τ
                simp [φ, Hτ, InnerProductSpace.toDual_apply_apply]
        _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hHτ_apply_int t)
        _ = inner ℝ s (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              simp [φ, InnerProductSpace.toDual_apply_apply]
        _ = inner ℝ s (G t) := by
              rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int t]
    intro s t
    calc
      inner ℝ (G s) t = inner ℝ t (G s) := real_inner_comm _ _
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ t (Hτ τ s) := (hpair_integral t s).symm
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro τ hτ
            have hτIoc : τ ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
            have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
              exact ⟨le_of_lt hτIoc.1, hτIoc.2⟩
            have hz : x + τ • d ∈ dom := hHτ_maps hτ'
            have hzPos : (Hτ τ).IsPositive := by
              simpa [Hτ] using hself.hessian_isPositive hz
            simpa [Hτ, real_inner_comm] using hzPos.isSymmetric s t
      _ = inner ℝ s (G t) := hpair_integral s t
  have hK_symm : K.IsSymmetric := by
    -- Symmetry is preserved when the symmetric Hessian average is subtracted from the symmetric
    -- base Hessian.
    exact hessianDifference_isSymmetricPairing (hself.hessian_isPositive hx).isSymmetric hG_symm
  have hlower : -(c • H) ≤ K := by
    -- The upper averaged-Hessian bound supplies the negative side of the symmetric sandwich.
    have hsum : H + c • H = (1 / (1 - a)) • H := by
      have hscalar : (1 : ℝ) + c = 1 / (1 - a) := by
        dsimp [c]
        field_simp [hfactor_pos.ne']
        ring
      calc
        H + c • H = ((1 : ℝ) + c) • H := by
          rw [add_smul, one_smul]
        _ = (1 / (1 - a)) • H := by
          rw [hscalar]
    have hmain : G ≤ H + c • H := by
      rw [hsum]
      exact hG_upper
    rw [ContinuousLinearMap.le_def]
    have hmain' : ((H + c • H) - G).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  have hupper : K ≤ c • H := by
    -- The lower averaged-Hessian bound controls the positive side after one scalar comparison.
    have hscalar_le : (1 : ℝ) ≤ (1 - a + a ^ (2 : ℕ) / 3) + c := by
      dsimp [c]
      field_simp [hfactor_pos.ne']
      nlinarith [ha_nonneg, ha_lt_one]
    have hstep1 :
        (1 : ℝ) • H ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := by
      exact loewnerSmul_mono_of_nonneg hH_nonneg hscalar_le
    have hstep2 :
        ((1 - a + a ^ (2 : ℕ) / 3) + c) • H =
          (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := by
      rw [add_smul]
    have hstep3 :
        (1 - a + a ^ (2 : ℕ) / 3) • H + c • H ≤ G + c • H := by
      exact loewnerAddRight_bridge hG_lower
    have hmain : H ≤ G + c • H := by
      calc
      H = (1 : ℝ) • H := by simp
      _ ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := hstep1
      _ = (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := hstep2
      _ ≤ G + c • H := hstep3
    rw [ContinuousLinearMap.le_def]
    have hmain' : (G + c • H - H).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  -- Route correction: the standard branch should close from the averaged-Hessian Loewner
  -- sandwich alone, without reopening the endpoint-witness transport route.
  simpa [a, r, G, H, K, c] using
    abs_inner_le_mul_localNorm_of_operator_sandwich
      (f := f) (x := x) (u := u) (v := v) (hself.hessian_isPositive hx)
      K hc_nonneg hK_symm hlower hupper

/-- Helper for Theorem 5.2.2: the averaged-Hessian residual is controlled in the base dual local
norm by the same `a / (1 - a)` factor as in the scalar pairing estimate. -/
theorem average_hessian_residual_baseDualBound
    {x y u : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    HessianDualLocalNorm.ofDetNeZero f x
      ((inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx) hH
      (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let k : E := (H - G) u
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom Mf f).hessian_isPositive hx
  let δ : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
  let w : E := H.inverse k
  have hw_realize : ‖w‖[f; x] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian witness at `x` realizes both the base dual norm and its square.
    simpa [H, w, k, δ] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := x) hx hH k
  have hw_norm : ‖w‖[f; x] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ (a / (1 - a)) * ‖w‖[f; x] * ‖u‖[f; x] := by
    -- Apply the averaged-Hessian residual pairing estimate to the inverse-Hessian witness `w`.
    simpa [H, G, k, real_inner_comm] using
      average_hessian_residual_pairing_bound
        (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (v := w) hx hxy
  by_cases hδ_zero : δ = 0
  · -- If the base dual norm vanishes, the desired bound is immediate.
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg hMf_nonneg (hessianLocalNorm_nonneg f x (y - x))
    have ha_lt_one : a < 1 := by
      by_cases hMf_zero : (Mf : ℝ) = 0
      · simp [a, hMf_zero]
      · have hMf_pos : 0 < (Mf : ℝ) :=
          lt_of_le_of_ne hMf_nonneg (by simpa [eq_comm] using hMf_zero)
        dsimp [a]
        simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
    have hfactor_nonneg : 0 ≤ (a / (1 - a)) * ‖u‖[f; x] := by
      have hden_pos : 0 < 1 - a := by
        linarith
      have hratio_nonneg : 0 ≤ a / (1 - a) := by
        exact div_nonneg ha_nonneg (le_of_lt hden_pos)
      exact mul_nonneg hratio_nonneg (hessianLocalNorm_nonneg f x u)
    change δ ≤ (a / (1 - a)) * ‖u‖[f; x]
    simpa [hδ_zero] using hfactor_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ (a / (1 - a)) * (δ * ‖u‖[f; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by symm; exact hpair_sq
        _ = |inner ℝ k w| := by rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by rw [real_inner_comm]
        _ ≤ (a / (1 - a)) * ‖w‖[f; x] * ‖u‖[f; x] := hpair_bound
        _ = (a / (1 - a)) * (δ * ‖u‖[f; x]) := by rw [hw_norm]; ring
    -- Cancel the positive witness norm `δ` from the squared bound.
    nlinarith

/-- Helper for Theorem 5.2.2: once the next point stays in the domain, the new gradient splits
into the transported old gradient plus the averaged-Hessian residual. -/
theorem nextGradient_eq_oldGradient_plus_averageResidual
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf variant x hx hH
      xPlus ∈ dom) :
    let α := selfConcordantNewtonStepSize f Mf variant x hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf variant x hx hH
    let H := hessian f x
    let u := H.inverse (∇ f x)
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
    ∇ f xPlus = (1 - α) • ∇ f x + α • ((H - G) u) := by
  let α := selfConcordantNewtonStepSize f Mf variant x hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf variant x hx hH
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  have hxPlus' : xPlus ∈ dom := by
    simpa [xPlus] using hxPlus
  have hu : H u = ∇ f x := by
    -- The Newton direction is defined by the inverse Hessian at `x`.
    let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
    exact hInv.self_apply_inverse (∇ f x)
  have hsub :
      xPlus - x = -(α • u) := by
    -- Rewrite the canonical next point into the standard Newton displacement form.
    simpa [α, xPlus, H, u] using
      next_point_sub_eq_neg_stepSize_smul_inverse_gradient
        (Mf := Mf) (f := f) variant hx hH
  -- Prove the vector identity by testing against arbitrary inner-product directions.
  apply (InnerProductSpace.toDual ℝ E).injective
  ext v
  have hpair :
      inner ℝ (∇ f xPlus - ∇ f x) v = inner ℝ (G (xPlus - x)) v := by
    simpa [xPlus, G] using
      gradient_difference_pairing_eq_average_hessian_step
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (y := xPlus) (u := v) hx hxPlus'
  have hpair' :
      inner ℝ (∇ f xPlus) v = inner ℝ (∇ f x - α • (G u)) v := by
    have hpair_eq :
        inner ℝ (∇ f xPlus) v =
          inner ℝ (∇ f x) v + inner ℝ (G (xPlus - x)) v := by
      have hpair_expanded : inner ℝ (∇ f xPlus) v - inner ℝ (∇ f x) v =
          inner ℝ (G (xPlus - x)) v := by
        simpa [inner_sub_left] using hpair
      linarith
    -- Expand the gradient increment and replace the displacement by `-α • u`.
    calc
      inner ℝ (∇ f xPlus) v
          = inner ℝ (∇ f x) v + inner ℝ (G (xPlus - x)) v := hpair_eq
      _ = inner ℝ (∇ f x) v + inner ℝ (G (-(α • u))) v := by rw [hsub]
      _ = inner ℝ (∇ f x) v + inner ℝ (-α • (G u)) v := by
            simp
      _ = inner ℝ (∇ f x - α • (G u)) v := by
            simp [sub_eq_add_neg, inner_add_left, inner_smul_left]
  -- Normalize `H u = ∇ f x` to recover the stable `α/H/u/G` decomposition.
  calc
    inner ℝ (∇ f xPlus) v = inner ℝ (∇ f x - α • (G u)) v := hpair'
    _ = inner ℝ ((1 - α) • ∇ f x + α • ((H - G) u)) v := by
          rw [ContinuousLinearMap.sub_apply, hu]
          simp [sub_eq_add_neg, inner_add_left, inner_smul_left]
          ring

end CommonHelpers
section PositiveVariants

variable {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]

theorem average_hessian_residual_endpoint_witness_integral_rewrite
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    let k := (H - G) u
    inner ℝ w k =
      ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - hessian f (x + τ • (y - x))) u) := by
  let d : E := y - x
  let H : E →L[ℝ] E := hessian f x
  let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, Hτ τ
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ w (Hτ τ u)
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
  have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment from `x` to `y`.
    simpa [Hτ, d] using
      (hessian_continuousOn (dom := dom) (Mf := (Mf : NNReal)) (f := f) hself).comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hHτ_maps
  have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
    hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hHτ_apply_cont (v : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ v) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
  have hHτ_apply_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ Hτ τ v) MeasureTheory.volume 0 1 :=
    (hHτ_apply_cont v).intervalIntegrable_of_Icc (by norm_num)
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 := by
    -- Evaluating the Hessian field on `u` and then pairing with `w` preserves integrability.
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    simpa [θ, φ, InnerProductSpace.toDual_apply_apply] using
      φ.continuous.comp_continuousOn (hHτ_apply_cont u) |>.intervalIntegrable_of_Icc (by norm_num)
  have hpair_integral : ∫ τ in (0 : ℝ)..1, θ τ = inner ℝ w (G u) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    calc
      ∫ τ in (0 : ℝ)..1, θ τ = ∫ τ in (0 : ℝ)..1, φ (Hτ τ u) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro τ
        simp [θ, φ, InnerProductSpace.toDual_apply_apply]
      _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ u) := by
        exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hHτ_apply_int u)
      _ = inner ℝ w (∫ τ in (0 : ℝ)..1, Hτ τ u) := by
        simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ w (G u) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int u]
  -- Expand the residual once so the endpoint witness pairing becomes a scalar integral.
  calc
    inner ℝ w ((H - G) u) = inner ℝ w (H u) - inner ℝ w (G u) := by
      simp [ContinuousLinearMap.sub_apply, inner_sub_right]
    _ = inner ℝ w (H u) - ∫ τ in (0 : ℝ)..1, θ τ := by
      rw [hpair_integral]
    _ = ∫ τ in (0 : ℝ)..1, (inner ℝ w (H u) - θ τ) := by
      symm
      simpa using
        intervalIntegral.integral_sub intervalIntegrable_const hθ_int
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - Hτ τ) u) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro τ
      simp [θ, ContinuousLinearMap.sub_apply, inner_sub_right]
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - hessian f (x + τ • d)) u) := by
      rfl
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ w ((H - hessian f (x + τ • (y - x))) u) := by
      simp [d]

/-- Helper for Theorem 5.2.2: every intermediate point of an admissible segment still belongs to
the base Dikin ellipsoid of radius `1 / M_f`. -/
theorem short_segmentEndpoint_mem_openDikinEllipsoid
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let z := x + τ • (y - x)
    z ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)) := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (((Mf : NNReal)) : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (((Mf : NNReal)) : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (((Mf : NNReal)) : ℝ))).1 hxy
  have hz_norm : ‖z - x‖[f; x] = τ * r := by
    have hz_sub : z - x = τ • (y - x) := by
      dsimp [z]
      abel
    -- Rewrite the intermediate displacement as the scalar multiple `τ • (y - x)`.
    rw [hz_sub]
    simpa [r] using
      hessianLocalNorm_smul_of_nonneg (f := f) (hself.hessian_isPositive hx) hτ.1
  have hτr_le_r : τ * r ≤ r := by
    have hr_nonneg : 0 ≤ r := by
      simpa [r] using hessianLocalNorm_nonneg f x (y - x)
    simpa using (show τ * r ≤ (1 : ℝ) * r from mul_le_mul_of_nonneg_right hτ.2 hr_nonneg)
  -- The whole short segment stays inside the original admissible Dikin ellipsoid.
  rw [mem_openDikinEllipsoid_iff, hz_norm]
  exact lt_of_le_of_lt hτr_le_r hr_lt

/-- Helper for Theorem 5.2.2: an admissible segment point compares back to the base metric at
`x` with the standard factor `(1 - τ * a)⁻¹`. -/
theorem segment_point_localNorm_le_baseFactor
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (v : E) :
    let r := ‖y - x‖[f; x]
    let a := (((Mf : NNReal)) : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[f; z] ≤ (1 / (1 - τ * a)) * ‖v‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (((Mf : NNReal)) : ℝ) * r
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (((Mf : NNReal)) : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (((Mf : NNReal)) : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (((Mf : NNReal)) : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    have hr_nonneg : 0 ≤ r := by
      simpa [r] using hessianLocalNorm_nonneg f x (y - x)
    have ha_nonneg : 0 ≤ a := by
      exact mul_nonneg (show 0 ≤ (((Mf : NNReal)) : ℝ) from ((Mf : NNReal)).2) hr_nonneg
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hz_bound :
      hessian f z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
    -- Rewrite the segment-point Hessian comparison into the local `r/a/z` spelling.
    simpa [r, a, z] using
      (segment_point_hessian_bounds
        (hself := (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f))
        (x := x) (y := y) hx hxy (τ := τ) hτ).2
  have hsqrt :
      Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) = 1 / (1 - τ * a) := by
    have hfactor_nonneg : 0 ≤ 1 / (1 - τ * a) := by positivity
    rw [show (((1 - τ * a) ^ (2 : ℕ))⁻¹ : ℝ) = (1 / (1 - τ * a)) ^ (2 : ℕ) by
      field_simp [hfactor_pos.ne']]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfactor_nonneg]
  -- Compare the segment-point metric to the base metric using the upper Hessian Loewner bound.
  calc
    ‖v‖[f; z] ≤ Real.sqrt (((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖v‖[f; x] := by
      exact hessianLocalNorm_le_mul_of_loewner_upper
        (f := f) (x := x) (y := z) (v := v) (c := ((1 - τ * a) ^ (2 : ℕ))⁻¹)
        (by positivity) hz_bound
    _ = (1 / (1 - τ * a)) * ‖v‖[f; x] := by
      rw [hsqrt]

/-- Helper for Theorem 5.2.2: scalarizing the Hessian along an affine line differentiates to the
corresponding third-derivative pairing. -/
theorem hessianHasFDerivAtOfContDiffAt
    {x : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := by
    -- First differentiate `f` once and keep the two remaining derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Theorem 5.2.2: scalarizing the Hessian along an affine line differentiates to the
corresponding third-derivative pairing. -/
theorem scalarized_hessian_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x d u w : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ w (hessian f (x + s • d) u))
      (inner ℝ w ((fderiv ℝ (hessian f) (x + t • d) d) u)) t := by
  have hcontAt : ContDiffAt ℝ 3 f (x + t • d) := by
    exact hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxt)
  have hhessianDeriv :
      HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (x + t • d)) (x + t • d) := by
    -- Upgrade the pointwise `C³` regularity of `f` to a derivative of the Hessian field.
    exact hessianHasFDerivAtOfContDiffAt (f := f) (x := x + t • d) hcontAt
  have happly :
      HasDerivAt (fun s : ℝ ↦ hessian f (x + s • d) u)
        ((fderiv ℝ (hessian f) (x + t • d) d) u) t := by
    -- Differentiate the Hessian field along the affine line and then evaluate it on `u`.
    have happlyF :
        HasFDerivAt (fun z : E ↦ hessian f z u)
          ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (hessian f) (x + t • d)))
          (x + t • d) := by
      exact (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp (x + t • d) hhessianDeriv
    simpa using happlyF.comp_hasDerivAt t (line_hasDerivAt x d t)
  have hinnerF :
      HasFDerivAt (fun z : E ↦ inner ℝ w z) ((innerSL ℝ) w) (hessian f (x + t • d) u) := by
    -- Postcompose the vector-valued Hessian slice with the fixed linear functional `inner w`.
    simpa using ((innerSL ℝ) w).hasFDerivAt
  simpa using hinnerF.comp_hasDerivAt t happly

/-- Helper for Theorem 5.2.2: the scalar Hessian-direction pairing is the corresponding
evaluation of the third iterated derivative. -/
theorem hessian_direction_pairing_eq_iteratedFDeriv
    {x d w v : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    inner ℝ v ((fderiv ℝ (hessian f) x d) w) = iteratedFDeriv ℝ 3 f x ![d, w, v] := by
  let line : ℝ → E := fun s ↦ x + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) w)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![w, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ y ∈ s, inner ℝ v (hessian f y w) = iteratedFDeriv ℝ 2 f y ![w, v] := by
    intro y hy
    -- Rewrite the Hessian pairing through the second iterated derivative on a local `C³`
    -- neighborhood of `x`.
    have hy_cont : ContDiffAt ℝ 3 f y := hs_contOn.contDiffAt (hs_open.mem_nhds hy)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := by
      exact hy_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) y := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f)
          (D.comp (fderiv ℝ (fderiv ℝ f) y)) y := by
      simpa [gradient, D] using D.hasFDerivAt.comp y hfderiv_diff.hasFDerivAt
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) y) w)) v
          = ((fderiv ℝ (fderiv ℝ f) y) w) v := by
              simp [InnerProductSpace.toDual_symm_apply]
      _ = iteratedFDeriv ℝ 2 f y ![w, v] := by
            simp [iteratedFDeriv_two_apply]
  have hline_mem : ∀ᶠ t in nhds (0 : ℝ), line t ∈ s := by
    let hline0 : ContinuousAt line 0 :=
      (line_hasDerivAt (x := x) (d := d) 0).continuousAt
    exact hline0.tendsto.eventually (hs_open.mem_nhds (by simpa [line] using hxs))
  have hEq : ψ =ᶠ[nhds (0 : ℝ)] φ := by
    filter_upwards [hline_mem] with t ht
    simp [ψ, φ, line, hEqOn _ ht]
  have hφ :
      HasDerivAt φ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 := by
    have hxLine : HasDerivAt line d 0 := by
      simpa [line] using line_hasDerivAt (x := x) (d := d) 0
    have hhessianDeriv :
        HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (line 0)) (line 0) := by
      simpa [line] using hessianHasFDerivAtOfContDiffAt (f := f) (x := x) hcontAt
    have happly :
        HasDerivAt (fun t : ℝ ↦ hessian f (line t) w)
          ((fderiv ℝ (hessian f) (line 0) d) w) 0 := by
      -- Differentiate the Hessian map along the affine line and then evaluate it on `w`.
      have happlyF :
          HasFDerivAt (fun y : E ↦ hessian f y w)
            ((ContinuousLinearMap.apply ℝ E w).comp (fderiv ℝ (hessian f) (line 0))) (line 0) := by
        exact (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp (line 0) hhessianDeriv
      simpa using happlyF.comp_hasDerivAt 0 hxLine
    have hinnerF :
        HasFDerivAt (fun y : E ↦ inner ℝ v y) ((innerSL ℝ) v) (hessian f (line 0) w) := by
      simpa using ((innerSL ℝ) v).hasFDerivAt
    -- The scalar pairing is the composition of the Hessian line with the fixed inner-product
    -- functional against `v`.
    simpa [φ, line] using hinnerF.comp_hasDerivAt 0 happly
  have hiter2_C1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 f) x := by
    exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
  have hiter2_deriv :
      HasFDerivAt (iteratedFDeriv ℝ 2 f) (fderiv ℝ (iteratedFDeriv ℝ 2 f) x) x := by
    exact (hiter2_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hψ :
      HasDerivAt ψ (((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v]) 0 := by
    have hline0 : HasDerivAt line d 0 := by
      simpa [line] using line_hasDerivAt (x := x) (d := d) 0
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ 2 f (line t))
          ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) 0 := by
      simpa [line] using hiter2_deriv.comp_hasDerivAt_of_eq 0 hline0 (by simp [line])
    -- Evaluate the derivative of the bilinear iterated derivative on the ordered pair `(w, v)`.
    simpa [ψ] using
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![w, v]).hasFDerivAt.comp_hasDerivAt
        0 hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 :=
    hφ.congr_of_eventuallyEq hEq
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) x d) w) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the derivative of the second iterated derivative back to the canonical third-order
  -- owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

/-- Helper for Theorem 5.2.2: under `C³` regularity, the third iterated derivative is symmetric
in its last two arguments. -/
theorem iteratedFDeriv_three_swap23_at
    {x u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] := by
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  let c : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := iteratedFDeriv ℝ 2 f
  have hvanish :
      (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hs_open.mem_nhds hxs] with y hy
    -- Nearby second derivatives are symmetric, so the antisymmetric part vanishes.
    have hycont : ContDiffAt ℝ 2 f y := by
      exact (hs_contOn.of_le (by norm_num)).contDiffAt (hs_open.mem_nhds hy)
    have hysymm : IsSymmSndFDerivAt ℝ f y := hycont.isSymmSndFDerivAt (by norm_num)
    have hyEq : iteratedFDeriv ℝ 2 f y ![u₂, u₃] = iteratedFDeriv ℝ 2 f y ![u₃, u₂] :=
      hysymm.iteratedFDeriv_cons
    simp [c, hyEq]
  have hc_diff : DifferentiableAt ℝ c x := by
    have hc_contDiff : ContDiffAt ℝ 1 c x := by
      exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
        (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
    exact hc_contDiff.differentiableAt one_ne_zero
  have hderivZero :
      fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x = 0 := by
    -- Replace the function by the eventually equal constant zero function.
    rw [hvanish.fderiv_eq]
    simp
  have hderivEval :
      ((fderiv ℝ c x).flipMultilinear ![u₂, u₃]) u₁ =
        ((fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁ := by
    have hzeroApplied :
        (fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x) u₁ = 0 := by
      simpa using congrArg (fun L : E →L[ℝ] ℝ => L u₁) hderivZero
    have h23diff : DifferentiableAt ℝ (fun y ↦ c y ![u₂, u₃]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₂, u₃]
    have h32diff : DifferentiableAt ℝ (fun y ↦ c y ![u₃, u₂]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₃, u₂]
    have hzeroApplied' :
        (((fderiv ℝ c x).flipMultilinear ![u₂, u₃] -
            (fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁) = 0 := by
      rw [← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_sub h23diff h32diff]
      exact hzeroApplied
    exact sub_eq_zero.mp hzeroApplied'
  simpa [c, iteratedFDeriv_succ_apply_left] using hderivEval

/-- Helper for Theorem 5.2.2: reparameterizing a short subsegment transports the live point metric
directly to the fixed endpoint metric. -/
theorem subsegment_point_localNorm_le_endpointFactor
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ s : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (v : E) :
    let r := ‖y - x‖[f; x]
    let a := (((Mf : NNReal)) : ℝ) * r
    let z := x + τ • (y - x)
    ‖v‖[f; x + s • (y - x)] ≤ ((1 - s * a) / (1 - τ * a)) * ‖v‖[f; z] := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  have hz_mem : z ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
    -- Keep the shorter endpoint inside the original Dikin ellipsoid before reparameterizing.
    simpa [r, z] using
      short_segmentEndpoint_mem_openDikinEllipsoid
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) hx hy hxy (τ := τ) hτ
  have hz : z ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hz_mem
  by_cases hτ0 : τ = 0
  · have hs0 : s = 0 := by linarith [hs.1, hs.2, hτ0]
    subst hτ0
    subst hs0
    -- When `τ = 0`, the shorter segment degenerates to the base point.
    simp [z, d, a]
  · let σ : ℝ := s / τ
    have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (by simpa [eq_comm] using hτ0)
    have hσ : σ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · dsimp [σ]
        exact div_nonneg hs.1 hτ.1
      · dsimp [σ]
        exact (div_le_iff₀ hτpos).2 (by simpa using hs.2)
    have hz_norm : ‖z - x‖[f; x] = τ * r := by
      have hz_sub : z - x = τ • d := by
        dsimp [z, d]
        abel
      rw [hz_sub, hessianLocalNorm_smul_of_nonneg (f := f)
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hτ.1]
    have hs_point : x + σ • (z - x) = x + s • d := by
      have hz_sub : z - x = τ • d := by
        dsimp [z, d]
        abel
      dsimp [σ]
      rw [hz_sub, smul_smul]
      congr 1
      field_simp [hτ0]
    have hcoeff :
        (1 - σ * ((Mf : ℝ) * ‖z - x‖[f; x])) / (1 - (Mf : ℝ) * ‖z - x‖[f; x]) =
          (1 - s * a) / (1 - τ * a) := by
      dsimp [σ, a]
      rw [hz_norm]
      field_simp [hτ0]
    -- Apply the already-proved endpoint transport formula to the shorter segment `x → z`.
    have htransport :
        ‖v‖[f; x + σ • (z - x)] ≤
          (1 - σ * ((Mf : ℝ) * ‖z - x‖[f; x])) / (1 - (Mf : ℝ) * ‖z - x‖[f; x]) *
            ‖v‖[f; z] := by
      simpa using
        segment_point_localNorm_le_endpointFactor
          (dom := dom) (Mf := Mf) (f := f) (x := x) (y := z)
          hx hz hz_mem (τ := σ) hσ v
    calc
      ‖v‖[f; x + s • (y - x)] = ‖v‖[f; x + σ • (z - x)] := by
        rw [hs_point.symm]
      _ ≤ (1 - σ * ((Mf : ℝ) * ‖z - x‖[f; x])) / (1 - (Mf : ℝ) * ‖z - x‖[f; x]) *
            ‖v‖[f; z] := htransport
      _ = ((1 - s * a) / (1 - τ * a)) * ‖v‖[f; z] := by
        rw [hcoeff]
      _ = ((1 - s * a) / (1 - τ * a)) * ‖v‖[f; x + τ • (y - x)] := by
        rfl

/-- Helper for Theorem 5.2.2: a primal local-norm comparison from `x` to `y` reverses to the
same factor on determinant-based Hessian dual local norms. -/
theorem hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {c : ℝ} (hc : 0 ≤ c)
    (hnorm : ∀ z : E, ‖z‖[f; x] ≤ c * ‖z‖[f; y])
    (hHx : (hessian f x).det ≠ 0) (hHy : (hessian f y).det ≠ 0) (v : E) :
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy)
        hHy (toDual ℝ E v) ≤
      c * HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
        hHx (toDual ℝ E v) := by
  -- Route correction: reuse the stabilized common inverse-witness bridge instead of reproving
  -- the same determinant-based transport inside the positive-parameter branch.
  simpa using
    hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le_common
      (Mf := (Mf : NNReal)) (f := f) (x := x) (y := y) hx hy hc hnorm hHx hHy v

/-- Helper for Theorem 5.2.2: the exact segment-point-to-endpoint primal transport factor also
controls the determinant-based endpoint dual norm in the reverse direction. -/
theorem segmentPointDualLocalNorm_le_endpointFactor_ofDetNeZero
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hHy : (hessian f y).det ≠ 0)
    (hHz : (hessian f (x + τ • (y - x))).det ≠ 0)
    (v : E) :
    let r := ‖y - x‖[f; x]
    let a := ((Mf : NNReal) : ℝ) * r
    let z := x + τ • (y - x)
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy)
        hHy (toDual ℝ E v) ≤
      ((1 - τ * a) / (1 - a)) *
        HessianDualLocalNorm.ofDetNeZero f z
          ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive
            (show z ∈ dom from
              segment_point_mem
                (hself := (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f))
                hx hy hτ.1 hτ.2))
          hHz (toDual ℝ E v) := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hz : z ∈ dom := by
    exact segment_point_mem (hself := hself) hx hy hτ.1 hτ.2
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hfactor_nonneg : 0 ≤ (1 - τ * a) / (1 - a) := by
    have hnum_nonneg : 0 ≤ 1 - τ * a := by linarith
    have hden_pos : 0 < 1 - a := by linarith
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hnorm :
      ∀ w : E, ‖w‖[f; z] ≤ ((1 - τ * a) / (1 - a)) * ‖w‖[f; y] := by
    intro w
    -- Reuse the exact segment-point transport factor already proved for primal local norms.
    simpa [r, a, z] using
      segment_point_localNorm_le_endpointFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := τ) hτ w
  -- Apply the generic determinant-based primal-to-dual transport bridge with `x := z`.
  simpa [r, a, z] using
    hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le
      (dom := dom) (Mf := Mf) (f := f) (x := z) (y := y) hz hy hfactor_nonneg hnorm hHz hHy v

/-- Helper for Theorem 5.2.2: differentiating the weighted scalar gap
`((1 - τ * a) / (1 - s * a)) * (ψ 0 - ψ s)` produces the normalized numerator used by the
fixed-`τ` endpoint-witness route. -/
theorem weightedEndpointWitnessGapHasDerivAt
    {a τ s : ℝ} {ψ : ℝ → ℝ} {ψ' : ℝ}
    (hden : 1 - s * a ≠ 0)
    (hψ : HasDerivAt ψ ψ' s) :
    HasDerivAt
      (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)) * (ψ 0 - ψ t))
      (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
        (a * (ψ 0 - ψ s) - (1 - s * a) * ψ')) s := by
  have hnum_deriv : HasDerivAt (fun t : ℝ ↦ (1 - τ * a)) 0 s := by
    -- The numerator of the rational weight is constant in the differentiation variable.
    simpa using (hasDerivAt_const s (1 - τ * a))
  have hden_deriv : HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
    -- Differentiate the affine denominator before applying the quotient rule once.
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
    ring
  have hweight :
      HasDerivAt (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)))
        (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) s := by
    have hquot := hnum_deriv.div hden_deriv hden
    have hslope :
        (0 * (1 - s * a) - (1 - τ * a) * (-a)) / (1 - s * a) ^ (2 : ℕ) =
          (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden]
      ring
    exact hquot.congr_deriv hslope
  have hgap :
      HasDerivAt (fun t : ℝ ↦ ψ 0 - ψ t) (-ψ') s := by
    -- The scalar gap is the difference between the fixed endpoint value and the live value.
    simpa using (hasDerivAt_const s (ψ 0)).sub hψ
  have hmul := hweight.mul hgap
  have hslope :
      (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ 0 - ψ s) +
          ((1 - τ * a) / (1 - s * a)) * (-ψ') =
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
          (a * (ψ 0 - ψ s) - (1 - s * a) * ψ')) := by
    field_simp [hden]
    ring
  -- Rewrite the product-rule slope into the single weighted numerator used downstream.
  exact hmul.congr_deriv hslope

/-- Helper for Theorem 5.2.2: the directional derivative of the Hessian is symmetric in its two
operator slots. -/
theorem third_derivative_operator_isSymmetric
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x d : E} (hx : x ∈ dom) :
    (fderiv ℝ (hessian f) x d).IsSymmetric := by
  have hcontAt : ContDiffAt ℝ 3 f x := by
    exact hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  intro v w
  -- Normalize both pairings to the third iterated derivative and swap the last two slots.
  calc
    inner ℝ ((fderiv ℝ (hessian f) x d) v) w
        = inner ℝ w ((fderiv ℝ (hessian f) x d) v) := by
            rw [real_inner_comm]
    _ = iteratedFDeriv ℝ 3 f x ![d, v, w] :=
          hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := d) (w := v) (v := w) hcontAt
    _ = iteratedFDeriv ℝ 3 f x ![d, w, v] :=
          iteratedFDeriv_three_swap23_at
            (f := f) (x := x) (u₁ := d) (u₂ := v) (u₃ := w) hcontAt
    _ = inner ℝ v ((fderiv ℝ (hessian f) x d) w) :=
          (hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := d) (w := w) (v := v) hcontAt).symm

/-- Helper for Theorem 5.2.2: at a live segment point, the scalar third-derivative pairing is
controlled in the fixed endpoint metric at `z = x + τ • (y - x)`. -/
theorem pointwiseSegmentHessianDerivPairingBoundAtSegmentPoint
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (((Mf : NNReal)) : ℝ) * r
    let z := x + τ • (y - x)
    |inner ℝ w ((fderiv ℝ (hessian f) (x + s • (y - x)) (y - x)) u)| ≤
      ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x] := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  let p : E := x + s • d
  let K : E →L[ℝ] E := fderiv ℝ (hessian f) p d
  let c : ℝ := 2 * (Mf : ℝ) * ‖d‖[f; p]
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hz_mem : z ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
    -- Keep the fixed short-segment endpoint inside the original Dikin ellipsoid before
    -- transporting the witness norm to it.
    simpa [r, z] using
      short_segmentEndpoint_mem_openDikinEllipsoid
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) hx hy hxy (τ := τ) hτ
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hp : p ∈ dom := by
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hs01)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hsa_le_ta : s * a ≤ τ * a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hsfactor_pos : 0 < 1 - s * a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (by positivity : 0 ≤ (Mf : ℝ)))
      (hessianLocalNorm_nonneg f p d)
  have hK_symm : K.IsSymmetric := by
    -- The directional Hessian derivative is symmetric in its remaining two slots.
    simpa [K, p, d] using third_derivative_operator_isSymmetric
      (dom := dom) (Mf := Mf) (f := f) hself (x := p) (d := d) hp
  have hupper : K ≤ c • hessian f p := by
    -- Apply the operator third-derivative bound in the live metric at `p`.
    simpa [K, c] using hself.thirdDerivative_operator_le hp d
  have hneg_upper : -K ≤ c • hessian f p := by
    -- Replacing `d` by `-d` gives the opposite side of the symmetric sandwich.
    simpa [K, c, map_neg, hessianLocalNorm_neg] using hself.thirdDerivative_operator_le hp (-d)
  have hlower : -(c • hessian f p) ≤ K := by
    rw [ContinuousLinearMap.le_def]
    rw [ContinuousLinearMap.le_def] at hneg_upper
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg_upper
  have hpair :
      |inner ℝ w (K u)| ≤ c * ‖w‖[f; p] * ‖u‖[f; p] := by
    -- Package the live-point third-derivative control as a scalar pairing estimate.
    simpa [K, c] using
      abs_inner_le_mul_localNorm_of_operator_sandwich
        (f := f) (x := p) (u := u) (v := w) (hself.hessian_isPositive hp)
        K hc_nonneg hK_symm hlower hupper
  have hd_transport :
      ‖d‖[f; p] ≤ (1 / (1 - s * a)) * ‖d‖[f; x] := by
    -- Compare the full segment direction back to the base metric at `x`.
    simpa [r, a, p, d] using
      segment_point_localNorm_le_baseFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := s) hs01 d
  have hw_transport :
      ‖w‖[f; p] ≤ ((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z] := by
    -- Transport the witness from the live point `p` to the fixed endpoint `z`.
    simpa [r, a, z, p, d] using
      subsegment_point_localNorm_le_endpointFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := τ) hτ (s := s) hs w
  have hu_transport :
      ‖u‖[f; p] ≤ (1 / (1 - s * a)) * ‖u‖[f; x] := by
    -- Compare the test direction back to the base metric at `x`.
    simpa [r, a, p, d] using
      segment_point_localNorm_le_baseFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := s) hs01 u
  have hc_le :
      c ≤ (2 * a) / (1 - s * a) := by
    have hscaled := mul_le_mul_of_nonneg_left hd_transport (by positivity : 0 ≤ 2 * (Mf : ℝ))
    simpa [c, a, r, d, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
  have htransport_step :
      c * ‖w‖[f; p] * ‖u‖[f; p] ≤
        ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x] := by
    have hw_bound_nonneg : 0 ≤ ((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z] := by
      exact mul_nonneg (div_nonneg (le_of_lt hsfactor_pos) (le_of_lt hτfactor_pos))
        (hessianLocalNorm_nonneg f z w)
    have hwu :
        ‖w‖[f; p] * ‖u‖[f; p] ≤
          (((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
            ((1 / (1 - s * a)) * ‖u‖[f; x]) := by
      exact mul_le_mul hw_transport hu_transport
        (hessianLocalNorm_nonneg f p u) hw_bound_nonneg
    have hscaled :
        c * (‖w‖[f; p] * ‖u‖[f; p]) ≤
          c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
            ((1 / (1 - s * a)) * ‖u‖[f; x])) := by
      exact mul_le_mul_of_nonneg_left hwu hc_nonneg
    have htransport_nonneg :
        0 ≤
          (((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
            ((1 / (1 - s * a)) * ‖u‖[f; x]) := by
      exact mul_nonneg hw_bound_nonneg
        (mul_nonneg (by positivity) (hessianLocalNorm_nonneg f x u))
    have hmono :
        c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
            ((1 / (1 - s * a)) * ‖u‖[f; x])) ≤
          ((2 * a) / (1 - s * a)) *
            ((((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
              ((1 / (1 - s * a)) * ‖u‖[f; x])) := by
      exact mul_le_mul_of_nonneg_right hc_le htransport_nonneg
    calc
      c * ‖w‖[f; p] * ‖u‖[f; p] = c * (‖w‖[f; p] * ‖u‖[f; p]) := by ring
      _ ≤ c * ((((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
            ((1 / (1 - s * a)) * ‖u‖[f; x])) := hscaled
      _ ≤ ((2 * a) / (1 - s * a)) *
            ((((1 - s * a) / (1 - τ * a)) * ‖w‖[f; z]) *
              ((1 / (1 - s * a)) * ‖u‖[f; x])) := hmono
      _ = ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x] := by
        field_simp [hτfactor_pos.ne', hsfactor_pos.ne']
  -- Combine the live-point third-derivative sandwich with the two transport estimates.
  calc
    |inner ℝ w ((fderiv ℝ (hessian f) p d) u)| ≤ c * ‖w‖[f; p] * ‖u‖[f; p] := hpair
    _ ≤ ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x] :=
      htransport_step

/-- Helper for Theorem 5.2.2: the normalized weighted-gap numerator is the one remaining local
scalar estimate in the fixed-`τ` endpoint-witness route. -/
theorem weightedEndpointWitnessNumerator_eq_pairing
    {x y u w : E} {τ s : ℝ} :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian f (x + t • d) u)
    (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
      (a * (ψ 0 - ψ s) -
        (1 - s * a) * inner ℝ w ((fderiv ℝ (hessian f) p d) u))) =
      inner ℝ w
        ((((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) •
            (a • (hessian f x - hessian f p) - (1 - s * a) • fderiv ℝ (hessian f) p d)) u) := by
  -- Rewrite the scalar numerator as one pairing against the weighted Hessian-gap operator.
  dsimp
  simp [ContinuousLinearMap.sub_apply, inner_sub_right, inner_smul_right]

/-- Helper for Theorem 5.2.2: the weighted Hessian-gap operator in the endpoint-witness
numerator stays symmetric at the live segment point. -/
theorem weightedEndpointWitnessNumeratorOperator_isSymmetric
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let d := y - x
    let p := x + s • d
    let a := (Mf : ℝ) * ‖y - x‖[f; x]
    (a • (hessian f x - hessian f p) - (1 - s * a) • fderiv ℝ (hessian f) p d).IsSymmetric := by
  -- Route correction: isolate the weighted operator first, so the remaining blocker is only the
  -- missing Loewner sandwich for this symmetric live-point operator.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let d : E := y - x
  let p : E := x + s • d
  let a : ℝ := (Mf : ℝ) * ‖y - x‖[f; x]
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hs)
  have hHp_symm : (hessian f p).IsSymmetric := (hself.hessian_isPositive hp).isSymmetric
  have hHx_symm : (hessian f x).IsSymmetric := (hself.hessian_isPositive hx).isSymmetric
  have hgap_symm : (hessian f x - hessian f p).IsSymmetric := by
    exact hessianDifference_isSymmetricPairing hHx_symm hHp_symm
  have hderiv_symm : (fderiv ℝ (hessian f) p d).IsSymmetric := by
    simpa [d, p] using third_derivative_operator_isSymmetric
      (dom := dom) (Mf := Mf) (f := f) hself (x := p) (d := d) hp
  have hweighted_gap_symm : (a • (hessian f x - hessian f p)).IsSymmetric := by
    intro u v
    simpa [inner_smul_left, inner_smul_right] using
      congrArg (fun t : ℝ ↦ a * t) (hgap_symm u v)
  have hweighted_deriv_symm : ((1 - s * a) • fderiv ℝ (hessian f) p d).IsSymmetric := by
    intro u v
    simpa [inner_smul_left, inner_smul_right] using
      congrArg (fun t : ℝ ↦ (1 - s * a) * t) (hderiv_symm u v)
  exact hessianDifference_isSymmetricPairing hweighted_gap_symm hweighted_deriv_symm

/-- Helper for Theorem 5.2.2: the live weighted-gap numerator splits into the explicit endpoint
residual `k = (H - G) u` plus the tail comparing the averaged Hessian `G` to the live Hessian at
`p = x + s • (y - x)`. -/
theorem weightedEndpointWitnessGapNumerator_splitByResidual
    {x y u w : E} {a s : ℝ} {G : E →L[ℝ] E} :
    let d := y - x
    let p := x + s • d
    let k := (hessian f x - G) u
    let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian f (x + t • d) u)
    a * (ψ 0 - ψ s) -
        (1 - s * a) * inner ℝ w ((fderiv ℝ (hessian f) p d) u) =
      a * inner ℝ w k +
        (a * inner ℝ w ((G - hessian f p) u) -
          (1 - s * a) * inner ℝ w ((fderiv ℝ (hessian f) p d) u)) := by
  let d : E := y - x
  let p : E := x + s • d
  let k : E := (hessian f x - G) u
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian f (x + t • d) u)
  -- Keep `d` and `p` opaque so the derivative term stays in the intended normal form.
  change a * (ψ 0 - ψ s) - (1 - s * a) * inner ℝ w ((fderiv ℝ (hessian f) p d) u) =
    a * inner ℝ w k +
      (a * inner ℝ w ((G - hessian f p) u) -
        (1 - s * a) * inner ℝ w ((fderiv ℝ (hessian f) p d) u))
  dsimp [ψ, k, p]
  simp [inner_sub_right]
  ring

/-- Helper for Theorem 5.2.2: the endpoint witness is defined by applying the inverse endpoint
Hessian to the averaged-Hessian residual. -/
theorem endpointWitness_apply_eq_averageResidual
    {x y u : E} (hy : y ∈ dom) (hHy : (hessian f y).det ≠ 0) :
    let H := hessian f x
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    He w = k := by
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  have hHe_inv : He.IsInvertible := hessian_isInvertible_of_det_ne_zero hHy
  -- Unfold the endpoint witness once so the inverse-Hessian equation becomes definitional.
  change He w = k
  simpa [w, He] using hHe_inv.self_apply_inverse k

/-- Helper for Theorem 5.2.2: after fixing the endpoint witness metric at `z`, the scaled
third-derivative contribution already has the reciprocal-square denominator required by the
short-segment integration route. -/
theorem weightedEndpointWitnessScaledDerivPairingBound
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    let d := y - x
    let p := x + s • d
    |(((1 - τ * a) / (1 - s * a)) * inner ℝ w ((fderiv ℝ (hessian f) p d) u))| ≤
      ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let d : E := y - x
  let p : E := x + s • d
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsa_le_ta : s * a ≤ τ * a := by
    simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hsfactor_pos : 0 < 1 - s * a := by
    linarith
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hraw :
      |inner ℝ w ((fderiv ℝ (hessian f) p d) u)| ≤
        ((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x] := by
    simpa [r, a, z, d, p] using
      pointwiseSegmentHessianDerivPairingBoundAtSegmentPoint
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (w := w)
      hx hy hxy (τ := τ) (s := s) hτ hs
  have hcoeff_nonneg : 0 ≤ (1 - τ * a) / (1 - s * a) := by
    exact div_nonneg (le_of_lt hτfactor_pos) (le_of_lt hsfactor_pos)
  -- Scale the fixed-`z` pairing estimate by the positive short-segment weight.
  have hscaled := mul_le_mul_of_nonneg_left hraw hcoeff_nonneg
  have habs :
      |((1 - τ * a) / (1 - s * a))| *
          |inner ℝ w ((fderiv ℝ (hessian f) p d) u)| ≤
        ((1 - τ * a) / (1 - s * a)) *
          (((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x]) := by
    simpa [abs_of_nonneg hcoeff_nonneg] using hscaled
  -- Route correction: keep the derivative estimate in the fixed `z` metric and collapse the
  -- scalar weights separately, instead of mixing that transport into the later weighted-gap step.
  calc
    |(((1 - τ * a) / (1 - s * a)) * inner ℝ w ((fderiv ℝ (hessian f) p d) u))|
        = |((1 - τ * a) / (1 - s * a))| *
            |inner ℝ w ((fderiv ℝ (hessian f) p d) u)| := by
              rw [abs_mul]
    _ ≤ ((1 - τ * a) / (1 - s * a)) *
          (((2 * a) / ((1 - τ * a) * (1 - s * a))) * ‖w‖[f; z] * ‖u‖[f; x]) := habs
    _ = ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] := by
      field_simp [hτfactor_pos.ne', hsfactor_pos.ne']

/-- Helper for Theorem 5.2.2: differentiating the fixed-endpoint weighted tail gap produces the
normalized numerator that the fixed-`τ` endpoint route still needs to bound. -/
theorem weightedEndpointWitnessTailGapHasDerivAt
    {a τ s : ℝ} {ψ : ℝ → ℝ} {ψ' : ℝ}
    (hden : 1 - s * a ≠ 0)
    (hψ : HasDerivAt ψ ψ' s) :
    HasDerivAt
      (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)) * (ψ t - ψ τ))
      (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
        (a * (ψ s - ψ τ) + (1 - s * a) * ψ')) s := by
  have hnum_deriv : HasDerivAt (fun t : ℝ ↦ (1 - τ * a)) 0 s := by
    -- The numerator of the rational weight is constant in the differentiation variable.
    simpa using (hasDerivAt_const s (1 - τ * a))
  have hden_deriv : HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
    -- Differentiate the affine denominator before the single quotient-rule step.
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
    ring
  have hweight :
      HasDerivAt (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a)))
        (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) s := by
    have hquot := hnum_deriv.div hden_deriv hden
    have hslope :
        (0 * (1 - s * a) - (1 - τ * a) * (-a)) / (1 - s * a) ^ (2 : ℕ) =
          (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden]
      ring
    exact hquot.congr_deriv hslope
  have hgap :
      HasDerivAt (fun t : ℝ ↦ ψ t - ψ τ) ψ' s := by
    -- The weighted tail gap subtracts a fixed endpoint value.
    exact (hψ.sub_const (ψ τ))
  have hmul := hweight.mul hgap
  have hslope :
      (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ s - ψ τ) +
          ((1 - τ * a) / (1 - s * a)) * ψ' =
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
          (a * (ψ s - ψ τ) + (1 - s * a) * ψ')) := by
    field_simp [hden]
  -- Rewrite the product-rule slope into the single weighted tail-gap numerator.
  exact hmul.congr_deriv hslope

/-- Helper for Theorem 5.2.2: integrating the derivative of the scalar weight
`((1 - τ * a) * (s * a)) / (1 - s * a)` against a tail-gap primitive collapses to a single live
integrand on `[0, τ]`. -/
theorem scalarTailKernelByParts
    {a τ : ℝ} {Θ J : ℝ → ℝ} (hτ : 0 ≤ τ)
    (hJ_cont : ContinuousOn J (Set.Icc (0 : ℝ) τ))
    (hJ_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt J (-Θ s) s)
    (hJτ : J τ = 0)
    (hΘ_int : IntervalIntegrable Θ MeasureTheory.volume 0 τ)
    (hden : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a) :
    ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
      =
        ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * (s * a)) / (1 - s * a)) * Θ s := by
  let g : ℝ → ℝ := fun s ↦ (((1 - τ * a) * (s * a)) / (1 - s * a))
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) τ) := by
    refine ((continuous_const.mul (continuous_id.mul_const a)).continuousOn).div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden s hs).ne'
  have hg_deriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo hs
    have hden_ne : 1 - s * a ≠ 0 := (hden s hs').ne'
    have hnum_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - τ * a) * (t * a)) ((1 - τ * a) * a) s := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        ((hasDerivAt_id s).mul_const a).const_mul (1 - τ * a)
    have hden_deriv : HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
      -- Differentiate the affine denominator before the single quotient-rule step.
      convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (((1 - τ * a) * a) * (1 - s * a) - ((1 - τ * a) * (s * a)) * (-a)) /
            (1 - s * a) ^ (2 : ℕ)
          =
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      field_simp [hden_ne]
      ring
    -- Collapse the quotient-rule numerator to the reciprocal-square scalar kernel.
    exact hquot.congr_deriv hslope
  have hkernel_int :
      IntervalIntegrable
        (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s)
        MeasureTheory.volume 0 τ := by
    have hcont :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s)
          (Set.Icc (0 : ℝ) τ) := by
      have hinv :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc (0 : ℝ) τ) := by
        have hpow_inv :
            ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
          have hbase :
              ContinuousOn (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
            refine continuousOn_const.div ?_ ?_
            · exact (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
            · intro s hs
              exact pow_ne_zero 2 ((hden s hs).ne')
          simpa [one_div] using hbase
        simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
      exact hinv.mul hJ_cont
    exact hcont.intervalIntegrable_of_Icc hτ
  have hJ_deriv' :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) τ) (max (0 : ℝ) τ), HasDerivAt J (-Θ s) s := by
    simpa [min_eq_left hτ, max_eq_right hτ] using hJ_deriv
  have hg_cont' : ContinuousOn g (Set.uIcc (0 : ℝ) τ) := by
    simpa [Set.uIcc_of_le hτ] using hg_cont
  have hJ_cont' : ContinuousOn J (Set.uIcc (0 : ℝ) τ) := by
    simpa [Set.uIcc_of_le hτ] using hJ_cont
  have hg_deriv' :
      ∀ s ∈ Set.Ioo (min (0 : ℝ) τ) (max (0 : ℝ) τ),
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    simpa [min_eq_left hτ, max_eq_right hτ] using hg_deriv
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hg_cont' hJ_cont' hg_deriv' hJ_deriv'
      (by
        have hcont :
            ContinuousOn (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
              (Set.Icc (0 : ℝ) τ) := by
          have hpow_inv :
              ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
            have hbase :
                ContinuousOn
                  (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
              refine continuousOn_const.div ?_ ?_
              · exact
                  (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
              · intro s hs
                exact pow_ne_zero 2 ((hden s hs).ne')
            simpa [one_div] using hbase
          simpa [mul_assoc] using
            ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
        exact (hcont.intervalIntegrable_of_Icc hτ))
      hΘ_int.neg
  have hg0 : g 0 = 0 := by
    simp [g]
  have hparts' :
      ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        =
          -∫ s in (0 : ℝ)..τ, g s * (-Θ s) := by
    -- The boundary terms vanish because the scalar weight is zero at `0` and the tail gap is
    -- zero at the fixed endpoint `τ`.
    have hτterm : g τ * J τ = 0 := by
      simp [g, hJτ]
    have hparts_zero :
        ∫ s in (0 : ℝ)..τ, g s * (-Θ s) =
          -∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s := by
      simpa [g, hg0, hτterm] using hparts
    simpa using (congrArg Neg.neg hparts_zero).symm
  calc
    ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        = -∫ s in (0 : ℝ)..τ, g s * (-Θ s) := hparts'
    _ = ∫ s in (0 : ℝ)..τ, g s * Θ s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in (0 : ℝ)..τ, (((1 - τ * a) * (s * a)) / (1 - s * a)) * Θ s := by
      rfl

/-- Helper for Theorem 5.2.2: the reciprocal-square scalar majorant integrates exactly to the
short-segment coefficient `τ * a / (1 - τ * a)`. -/
theorem segmentReciprocalSquareIntegral_upto
    {a τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ha : a < 1) :
    ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ = (τ * a) / (1 - τ * a) := by
  have hden : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a := by
    intro s hs
    by_cases ha_nonneg : 0 ≤ a
    · have hsa_le_ta : s * a ≤ τ * a := mul_le_mul_of_nonneg_right hs.2 ha_nonneg
      have hta_le_a : τ * a ≤ a := by
        simpa using (show τ * a ≤ 1 * a from mul_le_mul_of_nonneg_right hτ.2 ha_nonneg)
      linarith
    · have hsa_le_zero : s * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.1 (le_of_not_ge ha_nonneg)
      linarith
  have hnum :
      ContinuousOn (fun s : ℝ ↦ (s * a) / (1 - s * a)) (Set.Icc (0 : ℝ) τ) := by
    refine (show ContinuousOn (fun s : ℝ ↦ s * a) (Set.Icc (0 : ℝ) τ) by
      exact (show Continuous (fun s : ℝ ↦ s * a) by continuity).continuousOn).div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden s hs).ne'
  have hint :
      IntervalIntegrable (fun s : ℝ ↦ a * ((1 - s * a) ^ (2 : ℕ))⁻¹)
        MeasureTheory.volume 0 τ := by
    have hcontInv :
        ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
      have hbase :
          ContinuousOn (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro s hs
          exact pow_ne_zero 2 (hden s hs).ne'
      simpa [one_div] using hbase
    have hcont :
        ContinuousOn (fun s : ℝ ↦ a * ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
      simpa [mul_assoc] using continuous_const.continuousOn.mul hcontInv
    exact hcont.intervalIntegrable_of_Icc hτ.1
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) τ,
        HasDerivAt (fun s : ℝ ↦ (s * a) / (1 - s * a))
          (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden t ht').ne'
    have hnum_deriv : HasDerivAt (fun s : ℝ ↦ s * a) a t := by
      simpa [mul_comm] using (hasDerivAt_id t).mul_const a
    have hden_deriv : HasDerivAt (fun s : ℝ ↦ 1 - s * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (a * (1 - t * a) - (t * a) * (-a)) / (1 - t * a) ^ (2 : ℕ) =
          a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
      rw [show a * (1 - t * a) - (t * a) * (-a) = a by ring]
      rw [div_eq_mul_inv]
    exact hquot.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 hnum hderiv hint
  calc
    ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹
        = ((τ * a) / (1 - τ * a)) - ((0 : ℝ) * a / (1 - 0 * a)) := by
            simpa using hftc
    _ = (τ * a) / (1 - τ * a) := by ring

/-- Helper for Theorem 5.2.2: the same reciprocal-square kernel integrates explicitly on a short
interval `[s, τ]`, which is the scalar normalization needed by the primitive-drop route. -/
theorem segmentReciprocalSquareIntegral_between
    {a τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (ha : a < 1) :
    ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ =
      ((τ - s) * a) / ((1 - τ * a) * (1 - s * a)) := by
  have hden : ∀ t ∈ Set.Icc s τ, 0 < 1 - t * a := by
    intro t ht
    by_cases ha_nonneg : 0 ≤ a
    · have hta_le_τa : t * a ≤ τ * a := mul_le_mul_of_nonneg_right ht.2 ha_nonneg
      have hτa_le_a : τ * a ≤ a := by
        simpa using (show τ * a ≤ 1 * a from mul_le_mul_of_nonneg_right hτ.2 ha_nonneg)
      linarith
    · have hta_le_zero : t * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_trans hs.1 ht.1)
        (le_of_not_ge ha_nonneg)
      linarith
  have hnum :
      ContinuousOn (fun t : ℝ ↦ (t * a) / (1 - t * a)) (Set.Icc s τ) := by
    refine
      (show ContinuousOn (fun t : ℝ ↦ t * a) (Set.Icc s τ) by
        exact (show Continuous (fun t : ℝ ↦ t * a) by continuity).continuousOn).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ a * ((1 - t * a) ^ (2 : ℕ))⁻¹)
        MeasureTheory.volume s τ := by
    have hcontInv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      have hbase :
          ContinuousOn (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc s τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 (hden t ht).ne'
      simpa [one_div] using hbase
    have hcont :
        ContinuousOn (fun t : ℝ ↦ a * ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      simpa [mul_assoc] using continuous_const.continuousOn.mul hcontInv
    exact hcont.intervalIntegrable_of_Icc hs.2
  have hderiv :
      ∀ t ∈ Set.Ioo s τ,
        HasDerivAt (fun t : ℝ ↦ (t * a) / (1 - t * a))
          (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) t := by
    intro t ht
    have ht' : t ∈ Set.Icc s τ := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden t ht').ne'
    have hnum_deriv : HasDerivAt (fun x : ℝ ↦ x * a) a t := by
      simpa [mul_comm] using (hasDerivAt_id t).mul_const a
    have hden_deriv : HasDerivAt (fun x : ℝ ↦ 1 - x * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot := hnum_deriv.div hden_deriv hden_ne
    have hslope :
        (a * (1 - t * a) - (t * a) * (-a)) / (1 - t * a) ^ (2 : ℕ) =
          a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
      field_simp [hden_ne]
      ring
    exact hquot.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2 hnum hderiv hint
  have hτden : 1 - τ * a ≠ 0 := (hden τ ⟨hs.2, le_rfl⟩).ne'
  have hsden : 1 - s * a ≠ 0 := (hden s ⟨le_rfl, hs.2⟩).ne'
  have hsden' : 1 - a * s ≠ 0 := by
    simpa [mul_comm] using hsden
  calc
    ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ =
        (τ * a) / (1 - τ * a) - (s * a) / (1 - s * a) := by
          simpa using hftc
    _ = ((τ - s) * a) / ((1 - τ * a) * (1 - s * a)) := by
          field_simp [hτden, hsden, hsden']
          ring

/-- Helper for Theorem 5.2.2: the single transport from the segment point back to the endpoint
collapses the short-segment residual coefficient to the final endpoint denominator. -/
theorem segmentPointResidualTransportCoefficient_eq
    {a τ : ℝ} (hτfactor_pos : 0 < 1 - τ * a) (hfactor_pos : 0 < 1 - a) :
    ((1 - τ * a) / (1 - a)) * ((2 * τ * a) / (1 - τ * a)) = (2 * τ * a) / (1 - a) := by
  -- Cancel the shared factor `1 - τ * a` before the last endpoint comparison.
  field_simp [hτfactor_pos.ne', hfactor_pos.ne']

/-- Helper for Theorem 5.2.2: after transporting the witness norm from the fixed segment point
`z` to the endpoint `y`, the weighted live integrand keeps the same reciprocal-square kernel. -/
theorem endpointWitnessWeightedIntegrandBoundAtEndpoint
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    let ω : ℝ → ℝ :=
      fun t ↦ ((1 - τ * a) / (1 - t * a)) *
        inner ℝ w ((fderiv ℝ (hessian f) (x + t • (y - x)) (y - x)) u)
    |ω s| ≤
      ((((1 - τ * a) / (1 - a)) * (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) *
        ‖w‖[f; y]) * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  let ω : ℝ → ℝ :=
    fun t ↦ ((1 - τ * a) / (1 - t * a)) *
      inner ℝ w ((fderiv ℝ (hessian f) (x + t • (y - x)) (y - x)) u)
  have hlive :
      |ω s| ≤ ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] := by
    -- Start from the already-closed live-metric reciprocal-square bound at the fixed point `z`.
    simpa [r, a, z, ω] using
      weightedEndpointWitnessScaledDerivPairingBound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (w := w)
        hx hy hxy (τ := τ) (s := s) hτ hs
  have hw_transport :
      ‖w‖[f; z] ≤ ((1 - τ * a) / (1 - a)) * ‖w‖[f; y] := by
    -- Perform the endpoint transport exactly once, after the live integrand is already scalarized.
    simpa [r, a, z] using
      segment_point_localNorm_le_endpointFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := τ) hτ w
  have hcoeff_nonneg : 0 ≤ (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) ha_nonneg) (by positivity)
  have hu_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
  have hscaled :
      ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] ≤
        ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) *
          (((1 - τ * a) / (1 - a)) * ‖w‖[f; y]) * ‖u‖[f; x] := by
    exact
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw_transport hcoeff_nonneg) hu_nonneg
  -- Reassociate the scalar factors so the endpoint metric is in the final theorem's normal form.
  calc
    |ω s| ≤ ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] := hlive
    _ ≤ ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) *
          (((1 - τ * a) / (1 - a)) * ‖w‖[f; y]) * ‖u‖[f; x] := hscaled
    _ = ((((1 - τ * a) / (1 - a)) * (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) *
          ‖w‖[f; y]) * ‖u‖[f; x] := by ring

/-- Helper for Theorem 5.2.2: evaluating the weighted tail gap at `s = 0` rewrites the fixed
endpoint residual as one explicit integral shell before any absolute-value estimates are applied. -/
theorem weightedTailGapEndpointIdentityAtZero
    {a τ : ℝ} {ψ θ : ℝ → ℝ}
    (hτ : 0 ≤ τ)
    (hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) τ))
    (hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) τ))
    (hψ_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt ψ (θ s) s)
    (hden_pos : ∀ s ∈ Set.Icc (0 : ℝ) τ, 0 < 1 - s * a) :
    let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
    (1 - τ * a) * (ψ 0 - ψ τ) =
      ∫ s in (0 : ℝ)..τ,
        ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
  dsimp
  let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
  let F : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ)
  let integrand : ℝ → ℝ := fun s ↦
    ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s
  have hweight_cont :
      ContinuousOn (fun s : ℝ ↦ ((1 - τ * a) / (1 - s * a))) (Set.Icc (0 : ℝ) τ) := by
    -- The rational weight is continuous on the closed interval because the affine denominator
    -- never vanishes there.
    refine continuousOn_const.div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden_pos s hs).ne'
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) τ) := by
    -- Multiply the continuous weight by the continuous tail gap `ψ s - ψ τ`.
    exact hweight_cont.mul (hψ_cont.sub continuous_const.continuousOn)
  have hintegrand_cont : ContinuousOn integrand (Set.Icc (0 : ℝ) τ) := by
    have hkernel_cont :
        ContinuousOn
          (fun s : ℝ ↦
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s))
          (Set.Icc (0 : ℝ) τ) := by
      have hpow_inv :
          ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc (0 : ℝ) τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden_pos s hs).ne')
        simpa [one_div] using hbase
      have hkernel_weight :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc (0 : ℝ) τ) := by
        simpa [mul_assoc] using
          (show ContinuousOn
            (fun s : ℝ ↦ ((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
              (Set.Icc (0 : ℝ) τ) from continuous_const.continuousOn.mul hpow_inv)
      exact hkernel_weight.mul (continuous_const.continuousOn.sub hψ_cont)
    have hω_cont : ContinuousOn ω (Set.Icc (0 : ℝ) τ) := by
      -- The weighted derivative shell uses the same denominator control as `F`.
      exact hweight_cont.mul hθ_cont
    exact hkernel_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume 0 τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hτ
  have hF_deriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt F (-integrand s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) τ := Set.mem_Icc_of_Ioo hs
    have hbase :
        HasDerivAt F
          ((((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s))) s := by
      simpa [F] using
        weightedEndpointWitnessTailGapHasDerivAt
          (a := a) (τ := τ) (s := s) (ψ := ψ) (ψ' := θ s)
          (hden_pos s hs').ne' (hψ_deriv s hs)
    have hslope :
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s)) =
          -integrand s := by
      dsimp [integrand, ω]
      field_simp [(hden_pos s hs').ne']
      ring
    exact hbase.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ hF_cont hF_deriv hintegrand_int.neg
  -- Evaluate `F` at the endpoints `0` and `τ` so the weighted tail gap becomes the desired
  -- residual identity at `s = 0`.
  calc
    (1 - τ * a) * (ψ 0 - ψ τ) = F 0 := by
      simp [F]
    _ = F 0 - F τ := by
      simp [F]
    _ = -∫ s in (0 : ℝ)..τ, -integrand s := by
      linarith [hftc]
    _ = ∫ s in (0 : ℝ)..τ, integrand s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in (0 : ℝ)..τ,
          ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
      rfl

/-- Helper for Theorem 5.2.2: the same weighted tail-gap identity holds on an arbitrary short
interval `[s0, τ]`, so the primitive drop from `s0` to the fixed endpoint `τ` stays in the same
scalar normal form as the basepoint case. -/
theorem weightedTailGapEndpointIdentityOnIcc
    {a τ s0 : ℝ} {ψ θ : ℝ → ℝ}
    (hsτ : s0 ≤ τ)
    (hψ_cont : ContinuousOn ψ (Set.Icc s0 τ))
    (hθ_cont : ContinuousOn θ (Set.Icc s0 τ))
    (hψ_deriv : ∀ s ∈ Set.Ioo s0 τ, HasDerivAt ψ (θ s) s)
    (hden_pos : ∀ s ∈ Set.Icc s0 τ, 0 < 1 - s * a) :
    let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
    ((1 - τ * a) / (1 - s0 * a)) * (ψ s0 - ψ τ) =
      ∫ s in s0..τ,
        ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
  dsimp
  let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
  let F : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ)
  let integrand : ℝ → ℝ := fun s ↦
    ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s
  have hweight_cont :
      ContinuousOn (fun s : ℝ ↦ ((1 - τ * a) / (1 - s * a))) (Set.Icc s0 τ) := by
    -- The rational weight is continuous on `[s0, τ]` because the affine denominator never
    -- vanishes there.
    refine continuousOn_const.div ?_ ?_
    · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
    · intro s hs
      exact (hden_pos s hs).ne'
  have hF_cont : ContinuousOn F (Set.Icc s0 τ) := by
    -- Multiply the continuous weight by the continuous tail gap `ψ s - ψ τ`.
    exact hweight_cont.mul (hψ_cont.sub continuous_const.continuousOn)
  have hintegrand_cont : ContinuousOn integrand (Set.Icc s0 τ) := by
    have hkernel_cont :
        ContinuousOn
          (fun s : ℝ ↦
            ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)))
          (Set.Icc s0 τ) := by
      have hpow_inv :
          ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc s0 τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc s0 τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden_pos s hs).ne')
        simpa [one_div] using hbase
      have hkernel_weight :
          ContinuousOn
            (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
            (Set.Icc s0 τ) := by
        simpa [mul_assoc] using
          (show ContinuousOn
            (fun s : ℝ ↦ ((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
              (Set.Icc s0 τ) from continuous_const.continuousOn.mul hpow_inv)
      exact hkernel_weight.mul (continuous_const.continuousOn.sub hψ_cont)
    have hω_cont : ContinuousOn ω (Set.Icc s0 τ) := by
      -- The weighted derivative shell uses the same denominator control as `F`.
      exact hweight_cont.mul hθ_cont
    exact hkernel_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume s0 τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hsτ
  have hF_deriv :
      ∀ s ∈ Set.Ioo s0 τ, HasDerivAt F (-integrand s) s := by
    intro s hs
    have hs' : s ∈ Set.Icc s0 τ := Set.mem_Icc_of_Ioo hs
    have hbase :
        HasDerivAt F
          ((((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s))) s := by
      simpa [F] using
        weightedEndpointWitnessTailGapHasDerivAt
          (a := a) (τ := τ) (s := s) (ψ := ψ) (ψ' := θ s)
          (hden_pos s hs').ne' (hψ_deriv s hs)
    have hslope :
        (((1 - τ * a) / (1 - s * a) ^ (2 : ℕ)) *
            (a * (ψ s - ψ τ) + (1 - s * a) * θ s)) =
          -integrand s := by
      dsimp [integrand, ω]
      field_simp [(hden_pos s hs').ne']
      ring
    exact hbase.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsτ hF_cont hF_deriv hintegrand_int.neg
  -- Evaluate `F` at `s0` and at `τ` so the weighted short-interval tail gap becomes the desired
  -- primitive identity.
  calc
    ((1 - τ * a) / (1 - s0 * a)) * (ψ s0 - ψ τ) = F s0 := by
      simp [F]
    _ = F s0 - F τ := by
      simp [F]
    _ = -∫ s in s0..τ, -integrand s := by
      linarith [hftc]
    _ = ∫ s in s0..τ, integrand s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ = ∫ s in s0..τ,
          ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s)) - ω s := by
      rfl

/-- Helper for Theorem 5.2.2: integrating the reciprocal-square tail kernel by parts on an
arbitrary short interval `[s0, τ]` collapses the tail primitive to the live scalar shell at the
same endpoint `τ`. -/
theorem scalarTailKernelByPartsOnIcc
    {a τ s0 : ℝ} {Θ J : ℝ → ℝ} (hsτ : s0 ≤ τ)
    (hJ_cont : ContinuousOn J (Set.Icc s0 τ))
    (hJ_deriv : ∀ s ∈ Set.Ioo s0 τ, HasDerivAt J (-Θ s) s)
    (hJτ : J τ = 0)
    (hΘ_int : IntervalIntegrable Θ MeasureTheory.volume s0 τ)
    (hden : ∀ s ∈ Set.Icc s0 τ, 0 < 1 - s * a) :
    ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
      =
        ∫ s in s0..τ,
          ((((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a))) * Θ s) := by
  let g : ℝ → ℝ := fun s ↦
    (((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a)))
  have hg_cont : ContinuousOn g (Set.Icc s0 τ) := by
    refine
      ((continuous_const.mul (((continuous_id.sub continuous_const).mul_const a))).continuousOn).div
        ?_ ?_
    · exact
        (show Continuous (fun s : ℝ ↦ (1 - s0 * a) * (1 - s * a)) by continuity).continuousOn
    · intro s hs
      exact mul_ne_zero ((hden s0 ⟨le_rfl, hsτ⟩).ne') ((hden s hs).ne')
  have hg_deriv :
      ∀ s ∈ Set.Ioo s0 τ,
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    intro s hs
    have hs' : s ∈ Set.Icc s0 τ := Set.mem_Icc_of_Ioo hs
    have hs0' : s0 ∈ Set.Icc s0 τ := ⟨le_rfl, hsτ⟩
    have hden_s0_ne : 1 - s0 * a ≠ 0 := (hden s0 hs0').ne'
    have hden_s_ne : 1 - s * a ≠ 0 := (hden s hs').ne'
    have hnum_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - τ * a) * ((t - s0) * a)) (((1 - τ * a) * a)) s := by
      -- Differentiate the affine numerator once before the quotient-rule simplification.
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_id s).sub_const s0).mul_const a).const_mul (1 - τ * a)
    have hbase_den :
        HasDerivAt (fun t : ℝ ↦ 1 - t * a) (-a) s := by
      -- Differentiate the affine denominator factor.
      convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).mul_const a) using 1
      ring
    have hden_deriv :
        HasDerivAt (fun t : ℝ ↦ (1 - s0 * a) * (1 - t * a)) (-(1 - s0 * a) * a) s := by
      -- Keep the constant live-endpoint factor outside the affine denominator derivative.
      convert hbase_den.const_mul (1 - s0 * a) using 1 <;> ring
    have hquot := hnum_deriv.div hden_deriv (mul_ne_zero hden_s0_ne hden_s_ne)
    have hslope :
        (((1 - τ * a) * a) * ((1 - s0 * a) * (1 - s * a)) -
            ((1 - τ * a) * ((s - s0) * a)) * (-(1 - s0 * a) * a)) /
            (((1 - s0 * a) * (1 - s * a)) ^ (2 : ℕ))
          =
            (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
      -- Cancel the fixed factor `1 - s0 * a` from the quotient-rule expression to recover the
      -- reciprocal-square kernel.
      have hnum :
          ((1 - τ * a) * a) * ((1 - s0 * a) * (1 - s * a)) -
              ((1 - τ * a) * ((s - s0) * a)) * (-(1 - s0 * a) * a) =
            ((1 - τ * a) * a) * ((1 - s0 * a) ^ (2 : ℕ)) := by
        ring_nf
      rw [hnum, mul_pow, div_eq_mul_inv, mul_inv_rev]
      have hs0_sq_ne : (1 - s0 * a) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hden_s0_ne
      calc
        ((1 - τ * a) * a) * (1 - s0 * a) ^ (2 : ℕ) *
            (((1 - s * a) ^ (2 : ℕ))⁻¹ * ((1 - s0 * a) ^ (2 : ℕ))⁻¹)
            =
          ((1 - τ * a) * a) *
            ((((1 - s0 * a) ^ (2 : ℕ)) * ((1 - s0 * a) ^ (2 : ℕ))⁻¹) *
              ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
                ring
        _ = (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
              rw [mul_inv_cancel₀ hs0_sq_ne, one_mul]
    -- Collapse the quotient-rule numerator to the reciprocal-square kernel on `[s0, τ]`.
    exact hquot.congr_deriv hslope
  have hkernel_int :
      IntervalIntegrable
        (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
        MeasureTheory.volume s0 τ := by
    have hcont :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s0 τ) := by
      have hpow_inv :
          ContinuousOn
            (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹)
            (Set.Icc s0 τ) := by
        have hbase :
            ContinuousOn
              (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ))
              (Set.Icc s0 τ) := by
          refine continuousOn_const.div ?_ ?_
          · exact
              (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
          · intro s hs
            exact pow_ne_zero 2 ((hden s hs).ne')
        simpa [one_div] using hbase
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    exact hcont.intervalIntegrable_of_Icc hsτ
  have hJ_deriv' :
      ∀ s ∈ Set.Ioo (min s0 τ) (max s0 τ), HasDerivAt J (-Θ s) s := by
    simpa [min_eq_left hsτ, max_eq_right hsτ] using hJ_deriv
  have hg_cont' : ContinuousOn g (Set.uIcc s0 τ) := by
    simpa [Set.uIcc_of_le hsτ] using hg_cont
  have hJ_cont' : ContinuousOn J (Set.uIcc s0 τ) := by
    simpa [Set.uIcc_of_le hsτ] using hJ_cont
  have hg_deriv' :
      ∀ s ∈ Set.Ioo (min s0 τ) (max s0 τ),
        HasDerivAt g ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) s := by
    simpa [min_eq_left hsτ, max_eq_right hsτ] using hg_deriv
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hg_cont' hJ_cont' hg_deriv' hJ_deriv'
      hkernel_int hΘ_int.neg
  have hg_s0 : g s0 = 0 := by
    simp [g]
  have hparts' :
      ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        =
          -∫ s in s0..τ, g s * (-Θ s) := by
    -- The boundary terms vanish because `g s0 = 0` and the tail primitive itself vanishes at
    -- the fixed endpoint `τ`.
    have hτterm : g τ * J τ = 0 := by
      simp [g, hJτ]
    have hs0term : g s0 * J s0 = 0 := by
      simp [hg_s0]
    have hparts_zero :
        ∫ s in s0..τ, g s * (-Θ s) =
          -∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s := by
      simpa [hτterm, hs0term] using hparts
    simpa using (congrArg Neg.neg hparts_zero).symm
  calc
    ∫ s in s0..τ, (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * J s
        = -∫ s in s0..τ, g s * (-Θ s) := hparts'
    _ = ∫ s in s0..τ, g s * Θ s := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr ?_
      intro s hs
      ring
    _ =
        ∫ s in s0..τ,
          ((((1 - τ * a) * ((s - s0) * a)) / ((1 - s0 * a) * (1 - s * a))) * Θ s) := by
      rfl

/-- Helper for Theorem 5.2.2: the fixed-`τ` endpoint-witness residual estimate first closes with
an unsimplified reciprocal-square kernel before the scalar integral is evaluated explicitly. -/
theorem shortSubsegmentEndpoint_localNorm_le_liveFactor
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    ‖z - p‖[f; p] ≤ ((τ - s) * r) / (1 - s * a) := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hs01)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsfactor_pos : 0 < 1 - s * a := by
    have hsa_le_a : s * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hs01.2 ha_nonneg
    linarith
  by_cases hs1 : s = 1
  · have hτ1 : τ = 1 := by linarith [hs.2, hτ.2, hs1]
    subst hs1
    subst hτ1
    -- The short subsegment degenerates at the endpoint, so the local displacement vanishes.
    simpa [p, z, d, hessianLocalNorm_def] using (le_rfl : (0 : ℝ) ≤ 0)
  · let η : ℝ := (τ - s) / (1 - s)
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs01.2 (by simpa [eq_comm] using hs1)
    have hone_sub_s_pos : 0 < 1 - s := by linarith
    have hone_sub_s_ne : 1 - s ≠ 0 := hone_sub_s_pos.ne'
    have hη : η ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · dsimp [η]
        exact div_nonneg (sub_nonneg.mpr hs.2) (le_of_lt hone_sub_s_pos)
      · dsimp [η]
        have hnum_le : τ - s ≤ 1 - s := by
          linarith [hτ.2]
        exact (div_le_iff₀ hone_sub_s_pos).2 (by simpa [one_mul] using hnum_le)
    have hy_tail :
        ‖y - p‖[f; p] ≤ ((1 - s) * r) / (1 - s * a) := by
      -- Transport the remaining tail of the original segment to the live point `p`.
      simpa [r, a, p, d] using
        segment_tail_localNorm_le
          (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
          hx hy hxy (τ := s) hs01
    have hzp_eq : z - p = η • (y - p) := by
      have hy_tail_eq : y - p = (1 - s) • d := by
        calc
          y - p = y - (x + s • d) := by rfl
          _ = y - x - s • d := by abel
          _ = d - s • d := by simp [d]
          _ = (1 - s) • d := by rw [sub_smul, one_smul]
      have hz_tail_eq : z - p = (τ - s) • d := by
        calc
          z - p = (x + τ • d) - (x + s • d) := by rfl
          _ = τ • d - s • d := by abel
          _ = (τ - s) • d := by rw [sub_smul]
      rw [hz_tail_eq, hy_tail_eq, smul_smul]
      dsimp [η]
      have hη_mul : ((τ - s) / (1 - s)) * (1 - s) = τ - s := by
        field_simp [hone_sub_s_ne]
      rw [hη_mul]
    have hη_nonneg : 0 ≤ η := hη.1
    have hscale :
        ‖z - p‖[f; p] = η * ‖y - p‖[f; p] := by
      rw [hzp_eq]
      exact hessianLocalNorm_smul_of_nonneg
        (f := f) (hself.hessian_isPositive hp) hη_nonneg
    have hscaled :
        η * ‖y - p‖[f; p] ≤ η * (((1 - s) * r) / (1 - s * a)) := by
      exact mul_le_mul_of_nonneg_left hy_tail hη_nonneg
    calc
      ‖z - p‖[f; p] = η * ‖y - p‖[f; p] := hscale
      _ ≤ η * (((1 - s) * r) / (1 - s * a)) := hscaled
      _ = ((τ - s) * r) / (1 - s * a) := by
        have hη_mul :
            η * (((1 - s) * r) / (1 - s * a)) = ((τ - s) * r) / (1 - s * a) := by
          dsimp [η]
          field_simp [hone_sub_s_ne, hsfactor_pos.ne']
        simpa using hη_mul

/-- Helper for Theorem 5.2.2: the short subsegment from the live point
`p = x + s • (y - x)` to the fixed endpoint `z = x + τ • (y - x)` satisfies the same exact
Hessian comparison as an admissible Dikin segment, with factor `((1 - τ * a) / (1 - s * a))²`
in the live metric at `p`. -/
theorem shortSubsegmentEndpoint_hessian_bounds_fromLivePoint
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    (((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ)) • hessian f p ≤ hessian f z ∧
      hessian f z ≤
        ((((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹) • hessian f p := by
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let ρ : ℝ := ‖z - p‖[f; p]
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans hs.2 hτ.2⟩
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hs01)
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hτ)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsfactor_pos : 0 < 1 - s * a := by
    have hsa_le_a : s * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hs01.2 ha_nonneg
    linarith
  have hzp_le :
      ρ ≤ ((τ - s) * r) / (1 - s * a) := by
    simpa [ρ, r, a, d, p, z] using
      shortSubsegmentEndpoint_localNorm_le_liveFactor
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := τ) (s := s) hτ hs
  have hρ_lt : ρ < 1 / (Mf : ℝ) := by
    have hupper_lt :
        ((τ - s) * r) / (1 - s * a) < 1 / (Mf : ℝ) := by
      have hβ_lt_one :
          ((τ - s) * a) / (1 - s * a) < 1 := by
        have hτsa_lt_one_minus_sa : (τ - s) * a < 1 - s * a := by
          have hτa_le_a : τ * a ≤ a := by
            simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
          linarith
        exact (div_lt_iff₀ hsfactor_pos).2 (by simpa [one_mul] using hτsa_lt_one_minus_sa)
      have hrew :
          (Mf : ℝ) * (((τ - s) * r) / (1 - s * a)) =
            ((τ - s) * a) / (1 - s * a) := by
        dsimp [a]
        field_simp [hsfactor_pos.ne']
      have hscaled_lt :
          (((τ - s) * r) / (1 - s * a)) * (Mf : ℝ) < 1 := by
        calc
          (((τ - s) * r) / (1 - s * a)) * (Mf : ℝ)
              = (Mf : ℝ) * (((τ - s) * r) / (1 - s * a)) := by ring
          _ = ((τ - s) * a) / (1 - s * a) := hrew
          _ < 1 := hβ_lt_one
      exact (lt_div_iff₀ hMf_pos).2 hscaled_lt
    exact lt_of_le_of_lt hzp_le hupper_lt
  let rmid : ℝ := (ρ + 1 / (Mf : ℝ)) / 2
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[f; p](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    dsimp [rmid, ρ]
    linarith
  have hloewner :
      ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) • hessian f p ≤ hessian f z ∧
        hessian f z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian f p := by
    simpa [ρ] using
      hself.hessian_loewner_bounds_of_exact_local_radius
        (x := p) (y := z) (r := rmid) hp hz hrmid_lt hz_mem_rmid
  have hβ_bound :
      (Mf : ℝ) * ρ ≤ ((τ - s) * a) / (1 - s * a) := by
    have hscaled := mul_le_mul_of_nonneg_left hzp_le (le_of_lt hMf_pos)
    dsimp [ρ, a] at hscaled ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
  have hratio_nonneg : 0 ≤ (1 - τ * a) / (1 - s * a) := by
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    exact div_nonneg (by linarith) (le_of_lt hsfactor_pos)
  have hratio_sq_nonneg : 0 ≤ ((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ) := by positivity
  have hratio_sq_le :
      ((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ) ≤ (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) := by
    have hsfactor_pos' : 0 < 1 - a * s := by
      simpa [mul_comm] using hsfactor_pos
    have hratio_le :
        (1 - τ * a) / (1 - s * a) ≤ 1 - (Mf : ℝ) * ρ := by
      have hrewrite :
          (1 - τ * a) / (1 - s * a) = 1 - (((τ - s) * a) / (1 - s * a)) := by
        field_simp [hsfactor_pos.ne', hsfactor_pos'.ne']
        ring
      rw [hrewrite]
      linarith
    have hρfactor_nonneg : 0 ≤ 1 - (Mf : ℝ) * ρ := by
      have hρfactor_pos : 0 < 1 - (Mf : ℝ) * ρ := by
        have hscaled_lt : (Mf : ℝ) * ρ < 1 := by
          simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
        linarith
      exact le_of_lt hρfactor_pos
    nlinarith [hratio_le, hratio_nonneg, hρfactor_nonneg]
  have hρfactor_pos : 0 < 1 - (Mf : ℝ) * ρ := by
    have hscaled_lt : (Mf : ℝ) * ρ < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hρ_lt
    linarith
  have hρfactor_sq_nonneg : 0 ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ := by positivity
  have hupper_scalar :
      ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ ≤
        (((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹ := by
    have hratio_pos : 0 < (1 - τ * a) / (1 - s * a) := by
      have hτfactor_pos : 0 < 1 - τ * a := by
        have hτa_lt_one : τ * a < 1 := by
          have hτa_le_a : τ * a ≤ a := by
            simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
          linarith
        linarith
      exact div_pos hτfactor_pos hsfactor_pos
    exact
      (inv_le_inv₀
        (show 0 < (1 - (Mf : ℝ) * ρ) ^ (2 : ℕ) by positivity)
        (show 0 < ((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ) by
          exact pow_pos hratio_pos _)).2
        hratio_sq_le
  have hp_nonneg : 0 ≤ hessian f p := by
    simpa [ContinuousLinearMap.le_def] using (hself.hessian_isPositive hp)
  constructor
  · -- Weaken the exact-radius lower Loewner bound to the explicit subsegment factor.
    calc
      (((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ)) • hessian f p
          ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ)) • hessian f p := by
              exact loewnerSmul_mono_of_nonneg hp_nonneg hratio_sq_le
      _ ≤ hessian f z := hloewner.1
  · -- Compare the inverse-square upper factor using monotonicity of reciprocal on `(0, ∞)`.
    calc
      hessian f z ≤ ((1 - (Mf : ℝ) * ρ) ^ (2 : ℕ))⁻¹ • hessian f p := hloewner.2
      _ ≤ ((((1 - τ * a) / (1 - s * a)) ^ (2 : ℕ))⁻¹) • hessian f p := by
            exact loewnerSmul_mono_of_nonneg hp_nonneg hupper_scalar

/-- Helper for Theorem 5.2.2: the weighted primitive vanishes at the fixed endpoint `τ`, and at
`0` it is exactly `(1 - τ * a)` times the residual pairing `⟪w, (∇²f(x) - ∇²f(z)) u⟫`. -/
theorem weightedTailGapPrimitive_endpointValues
    {x y u w : E} {τ : ℝ} :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let Φ : ℝ → ℝ := fun t ↦
      inner ℝ w ((((1 - τ * a) / (1 - t * a)) • (hessian f (x + t • d) - hessian f z)) u)
    Φ τ = 0 ∧ Φ 0 = (1 - τ * a) * inner ℝ w ((hessian f x - hessian f z) u) := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let Φ : ℝ → ℝ := fun t ↦
    inner ℝ w ((((1 - τ * a) / (1 - t * a)) • (hessian f (x + t • d) - hessian f z)) u)
  constructor
  · -- At `t = τ`, the Hessian gap itself vanishes.
    simp
  · -- At `t = 0`, only the explicit numerator `(1 - τ * a)` remains.
    simp [inner_sub_right, inner_smul_right]

/-- Helper for Theorem 5.2.2: the weighted primitive pairing can be rewritten as pairing the
endpoint residual image `q` against the averaged-Hessian residual `k`. -/
theorem weightedTailGapPrimitive_pairing_eq_averageResidualImage
    {x y u : E} (hy : y ∈ dom) (hHy : (hessian f y).det ≠ 0) {τ s : ℝ} :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let H := hessian f x
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • d)
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u
    let q := He.inverse v
    inner ℝ w v = inner ℝ q k := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • d)
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u
  let q : E := He.inverse v
  let hPosY : He.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  let hHeInv : He.IsInvertible := hessian_isInvertible_of_det_ne_zero hHy
  have hw_apply : He w = k := by
    -- The endpoint witness `w` is the inverse-Hessian image of the averaged residual.
    simpa [He, w, k] using hHeInv.self_apply_inverse k
  have hq_apply : He q = v := by
    -- The auxiliary endpoint image `q` is the inverse-Hessian image of the primitive vector.
    simpa [He, q, v] using hHeInv.self_apply_inverse v
  have hHe_symm : He.IsSymmetric := hPosY.isSymmetric
  -- Move the endpoint Hessian across the pairing and unfold both inverse-Hessian witnesses once.
  calc
    inner ℝ w v = inner ℝ w (He q) := by rw [hq_apply]
    _ = inner ℝ (He w) q := by
          simpa [real_inner_comm] using hHe_symm q w
    _ = inner ℝ k q := by rw [hw_apply]
    _ = inner ℝ q k := by rw [real_inner_comm]

/-- Helper for Theorem 5.2.2: once an inverse-Hessian witness controls its own pairing with a
covector at a fixed point, the corresponding determinant-based dual norm follows by cancelling the
realized witness norm. -/
theorem dualLocalNorm_bound_of_inverseWitness_pairing
    {x k : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) {B C : ℝ}
    (hC_nonneg : 0 ≤ C) (hB_nonneg : 0 ≤ B)
    (hpair :
      let H := hessian f x
      let w := H.inverse k
      |inner ℝ w k| ≤ C * ‖w‖[f; x] * B) :
    HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
        hH (toDual ℝ E k) ≤
      C * B := by
  let H : E →L[ℝ] E := hessian f x
  let w : E := H.inverse k
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let δ : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
  have hw_realize : ‖w‖[f; x] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- Rewrite the inverse-Hessian witness as the realization of the determinant-based dual norm.
    simpa [H, w, δ] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := x) hx hH k
  have hw_norm : ‖w‖[f; x] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hkw_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair' : |inner ℝ w k| ≤ C * ‖w‖[f; x] * B := by
    simpa [H, w] using hpair
  change δ ≤ C * B
  by_cases hzero : δ = 0
  · have hrhs_nonneg : 0 ≤ C * B := by
      exact mul_nonneg hC_nonneg hB_nonneg
    rw [hzero]
    exact hrhs_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hzero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ C * (δ * B) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by symm; exact hpair_sq
        _ = |inner ℝ k w| := by rw [abs_of_nonneg hkw_nonneg]
        _ = |inner ℝ w k| := by rw [real_inner_comm]
        _ ≤ C * ‖w‖[f; x] * B := hpair'
        _ = C * (δ * B) := by rw [hw_norm]; ring
    -- Cancel the positive realized witness norm from the squared dual-norm bound.
    nlinarith

/-- Helper for Theorem 5.2.2: scalarizing the Hessian along an affine segment is continuous on
every closed subinterval of that segment. -/
theorem scalarizedHessianLineContinuousOn
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let d := y - x
    let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian f (x + t • d) u)
    ContinuousOn ψ (Set.Icc s τ) := by
  dsimp
  let d : E := y - x
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ w (hessian f (x + t • d) u)
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc s τ) dom := by
    intro t ht
    exact hsegment_dom <|
      segment_point_mem_segment (x := x) (y := y)
        ⟨le_trans hs.1 ht.1, le_trans ht.2 hτ.2⟩
  let Hs : ℝ → E →L[ℝ] E := fun t ↦ hessian f (x + t • d)
  have hHs_cont : ContinuousOn Hs (Set.Icc s τ) := by
    -- Restrict the continuous Hessian field to the affine tail segment.
    simpa [Hs, d] using
      (hessian_continuousOn (dom := dom) (Mf := (Mf : NNReal)) (f := f) hself).comp
        (show Continuous (fun t : ℝ ↦ x + t • d) by continuity).continuousOn
        hline_maps
  let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  -- Evaluating at `u` and pairing with the fixed witness preserves continuity.
  simpa [ψ, Hs, ev, φ, InnerProductSpace.toDual_apply_apply] using
    φ.continuous.comp_continuousOn (ev.continuous.comp_continuousOn hHs_cont)

/-- Helper for Theorem 5.2.2: scalarizing the third-derivative line along an affine segment is
continuous on every closed subinterval of that segment. -/
theorem scalarizedHessianLineDerivContinuousOn
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let d := y - x
    let θ : ℝ → ℝ := fun t ↦ inner ℝ w ((fderiv ℝ (hessian f) (x + t • d) d) u)
    ContinuousOn θ (Set.Icc s τ) := by
  dsimp
  let d : E := y - x
  let θ : ℝ → ℝ := fun t ↦ inner ℝ w ((fderiv ℝ (hessian f) (x + t • d) d) u)
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc s τ) dom := by
    intro t ht
    exact hsegment_dom <|
      segment_point_mem_segment (x := x) (y := y)
        ⟨le_trans hs.1 ht.1, le_trans ht.2 hτ.2⟩
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd_C2 : ContDiffOn ℝ 2 (fderiv ℝ f) dom :=
    hself.contDiffOn.fderiv_of_isOpen
      (IsSelfConcordantOnWith.isOpen_domain (dom := dom) (Mf := (Mf : NNReal)) (f := f))
      (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffOn ℝ 2 (∇ f) dom := by
    -- Rewrite the gradient through the Riesz map before differentiating again on `dom`.
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd_C2
  have hhessian_C1 : ContDiffOn ℝ 1 (hessian f) dom := by
    -- One more derivative produces a `C¹` Hessian field on the self-concordant domain.
    simpa [hessian] using
      hgrad_C2.fderiv_of_isOpen
        (IsSelfConcordantOnWith.isOpen_domain (dom := dom) (Mf := (Mf : NNReal)) (f := f))
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hhessianDeriv_cont : ContinuousOn (fderiv ℝ (hessian f)) dom := by
    -- The derivative of the Hessian field is continuous because the Hessian is `C¹`.
    exact
      (hhessian_C1.fderiv_of_isOpen
        (IsSelfConcordantOnWith.isOpen_domain (dom := dom) (Mf := (Mf : NNReal)) (f := f))
        (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have hlineDeriv_cont :
      ContinuousOn (fun t : ℝ ↦ fderiv ℝ (hessian f) (x + t • d)) (Set.Icc s τ) := by
    -- Pull the continuous Hessian derivative back to the same affine tail segment.
    simpa [d] using
      hhessianDeriv_cont.comp
        (show Continuous (fun t : ℝ ↦ x + t • d) by continuity).continuousOn
        hline_maps
  let evd : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ (E →L[ℝ] E) d
  let evu : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  -- Evaluate the third-derivative operator on `d`, then on `u`, then pair with `w`.
  change
    ContinuousOn
      (fun t : ℝ ↦ inner ℝ w ((fderiv ℝ (hessian f) (x + t • d) d) u))
      (Set.Icc s τ)
  simpa [θ, evd, evu, φ, InnerProductSpace.toDual_apply_apply] using
    φ.continuous.comp_continuousOn
      (evu.continuous.comp_continuousOn (evd.continuous.comp_continuousOn hlineDeriv_cont))

/-- Helper for Theorem 5.2.2: on the short interval `[s, τ]`, the additional normalized factor
`(t - s) * a` stays in `[0, 1]`. -/
theorem shortIntervalTailCoefficient_bounds
    {x y : E} (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ s t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (ht : t ∈ Set.Icc s τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    0 ≤ (t - s) * a ∧ (t - s) * a ≤ 1 := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hts_nonneg : 0 ≤ t - s := sub_nonneg.mpr ht.1
  have hts_le_one : t - s ≤ 1 := by
    have ht_le_one : t ≤ 1 := le_trans ht.2 hτ.2
    linarith [hs.1, ht_le_one]
  constructor
  · exact mul_nonneg hts_nonneg ha_nonneg
  · calc
      (t - s) * a ≤ 1 * a := by
        exact mul_le_mul_of_nonneg_right hts_le_one ha_nonneg
      _ ≤ 1 := by
        linarith

/-- Helper for Theorem 5.2.2: the weighted live integrand is exactly the existing
reciprocal-square endpoint-witness derivative bound in the local `θ` spelling. -/
theorem endpointWitnessWeightedLiveIntegrandAbsBound
    {x y u w : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ s : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    let d := y - x
    let θ : ℝ → ℝ := fun t ↦ inner ℝ w ((fderiv ℝ (hessian f) (x + t • d) d) u)
    |(((1 - τ * a) / (1 - s * a)) * θ s)| ≤
      ((2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖w‖[f; z] * ‖u‖[f; x] := by
  -- Package the weighted live integrand directly so later proofs can reuse the reciprocal-square
  -- estimate without reopening the derivative transport.
  simpa using
    weightedEndpointWitnessScaledDerivPairingBound
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (w := w)
      hx hy hxy (τ := τ) (s := s) hτ hs

/-- Helper for Theorem 5.2.2: the direct short-interval weighted tail-gap integrand rewrites as
one negative pairing against the combined live operator. -/
theorem weightedTailGapScalarShell_eq_neg
    {a τ t hp hz dy dx : ℝ} :
    (1 - τ * a) * a * ((1 - t * a) ^ (2 : ℕ))⁻¹ * (hz - hp) -
        (1 - τ * a) * ((1 - t * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (dy - dx) =
      -((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹ *
        (a * (hp - hz) + (1 - t * a) * (dy - dx))) := by
  ring

/-- Helper for Theorem 5.2.2: the direct short-interval weighted tail-gap integrand rewrites as
one negative pairing against the combined live operator. -/
theorem weightedTailGapPrimitiveIntegrand_eq_negCombinedPairing
    {x y u wz : E} {τ t : ℝ} :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
    let K : E →L[ℝ] E :=
      a • (hessian f (x + t • d) - hessian f z) +
        (1 - t * a) • fderiv ℝ (hessian f) (x + t • d) d
    ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
        (((1 - τ * a) / (1 - t * a)) * θ t) =
      -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
  -- Expand the direct short-interval integrand once so the unresolved content becomes a single
  -- pairing against the combined live operator `K`.
  dsimp
  let a : ℝ := (Mf : ℝ) * ‖y - x‖[f; x]
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let K : E →L[ℝ] E :=
    a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
  have htheta :
      inner ℝ wz ((fderiv ℝ (hessian f) p d) u) =
        inner ℝ wz (((fderiv ℝ (hessian f) p) y) u) -
          inner ℝ wz (((fderiv ℝ (hessian f) p) x) u) := by
    simp [d, ContinuousLinearMap.map_sub, inner_sub_right]
  have hpair :
      inner ℝ wz (K u) =
        a * (inner ℝ wz (hessian f p u) - inner ℝ wz (hessian f z u)) +
          (1 - t * a) *
            (inner ℝ wz (((fderiv ℝ (hessian f) p) y) u) -
              inner ℝ wz (((fderiv ℝ (hessian f) p) x) u)) := by
    simp [K, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, inner_add_right, inner_smul_right, inner_sub_right,
      htheta]
  change
    ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) *
        (inner ℝ wz (hessian f z u) - inner ℝ wz (hessian f p u))) -
      (((1 - τ * a) / (1 - t * a)) * inner ℝ wz (((fderiv ℝ (hessian f) p) d) u)) =
      -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))
  rw [htheta]
  have hmain :
      ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) *
          (inner ℝ wz (hessian f z u) - inner ℝ wz (hessian f p u))) -
        (((1 - τ * a) / (1 - t * a)) *
          (inner ℝ wz (((fderiv ℝ (hessian f) p) y) u) -
            inner ℝ wz (((fderiv ℝ (hessian f) p) x) u))) =
        -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
    rw [hpair]
    by_cases hta : 1 - t * a = 0
    · simp [hta]
    · have hinv :
          (1 - t * a)⁻¹ = (1 - t * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
        field_simp [hta]
      rw [div_eq_mul_inv, hinv]
      generalize hhp : inner ℝ wz (hessian f p u) = hp
      generalize hhz : inner ℝ wz (hessian f z u) = hz
      generalize hdy : inner ℝ wz (((fderiv ℝ (hessian f) p) y) u) = dy
      generalize hdx : inner ℝ wz (((fderiv ℝ (hessian f) p) x) u) = dx
      have hclosed :
          (1 - τ * a) * a * ((1 - t * a) ^ (2 : ℕ))⁻¹ * (hz - hp) -
              (1 - τ * a) * ((1 - t * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (dy - dx) =
            -((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹ *
              (a * (hp - hz) + (1 - t * a) * (dy - dx))) := by
        simpa using
          (weightedTailGapScalarShell_eq_neg
            (a := a) (τ := τ) (t := t) (hp := hp) (hz := hz) (dy := dy) (dx := dx))
      exact hclosed
  have hgoal :
      (1 - τ * a) * a * ((1 - t * a) ^ (2 : ℕ))⁻¹ * (inner ℝ wz (hessian f z u) - inner ℝ wz (hessian f p u)) -
          (1 - τ * a) / (1 - t * a) *
            (inner ℝ wz (((fderiv ℝ (hessian f) p) y) u) -
              inner ℝ wz (((fderiv ℝ (hessian f) p) x) u)) =
        -((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹ * inner ℝ wz (K u)) := by
    exact hmain
  exact hgoal

/-- Helper for Theorem 5.2.2: the combined short-interval Hessian-gap-plus-derivative operator is
symmetric at the live point. -/
theorem weightedTailGapPrimitiveCombinedOperator_isSymmetric
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {τ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + t • d
    (a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d).IsSymmetric := by
  -- Keep the Hessian-gap term and the live third-derivative term bundled together; only the
  -- Loewner sandwich for this symmetric operator is still missing afterwards.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let a : ℝ := (Mf : ℝ) * ‖y - x‖[f; x]
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) ⟨ht.1, le_trans ht.2 hτ.2⟩)
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hτ)
  have hHp_symm : (hessian f p).IsSymmetric := (hself.hessian_isPositive hp).isSymmetric
  have hHz_symm : (hessian f z).IsSymmetric := (hself.hessian_isPositive hz).isSymmetric
  have hgap_symm : (hessian f p - hessian f z).IsSymmetric := by
    exact hessianDifference_isSymmetricPairing hHp_symm hHz_symm
  have hderiv_symm : (fderiv ℝ (hessian f) p d).IsSymmetric := by
    simpa [p, d] using third_derivative_operator_isSymmetric
      (dom := dom) (Mf := Mf) (f := f) hself (x := p) (d := d) hp
  have hweighted_gap_symm : (a • (hessian f p - hessian f z)).IsSymmetric := by
    intro u v
    simpa [inner_smul_left, inner_smul_right] using
      congrArg (fun s : ℝ ↦ a * s) (hgap_symm u v)
  have hweighted_deriv_symm : ((1 - t * a) • fderiv ℝ (hessian f) p d).IsSymmetric := by
    intro u v
    simpa [inner_smul_left, inner_smul_right] using
      congrArg (fun s : ℝ ↦ (1 - t * a) * s) (hderiv_symm u v)
  intro u v
  calc
    inner ℝ
        ((a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d) u) v
        =
          inner ℝ ((a • (hessian f p - hessian f z)) u) v +
            inner ℝ (((1 - t * a) • fderiv ℝ (hessian f) p d) u) v := by
              simp [inner_add_left]
    _ =
        inner ℝ u ((a • (hessian f p - hessian f z)) v) +
          inner ℝ u (((1 - t * a) • fderiv ℝ (hessian f) p d) v) := by
            simpa using
              congrArg₂ (fun s₁ s₂ : ℝ ↦ s₁ + s₂) (hweighted_gap_symm u v)
                (hweighted_deriv_symm u v)
    _ = inner ℝ u
        ((a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d) v) := by
          simp [inner_add_right]

/-- Helper for Theorem 5.2.2: differentiating the weighted Hessian-gap scalar path on a short
interval produces the scaled combined live pairing that the direct integrand uses. -/
theorem weightedTailGapPrimitiveWeightedGapScalar_hasDerivAt
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + t • d
    let Φ : ℝ → ℝ := fun q ↦
      inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
    HasDerivAt Φ
      ((((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))) t := by
  -- Route correction: package the short-interval frontier as the derivative of the weighted-gap
  -- path itself, so later bounds can target the exact scaled spelling consumed by the integrand.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let Φ : ℝ → ℝ := fun q ↦
    inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
  let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
  let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
  let K : E →L[ℝ] E :=
    a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, le_trans ht.2 hτ.2⟩
  have hp : p ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) ht01)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have hta_le_a : t * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right ht01.2 ha_nonneg
  have htfactor_pos : 0 < 1 - t * a := by
    linarith
  have hden : 1 - t * a ≠ 0 := htfactor_pos.ne'
  have hψ :
      HasDerivAt ψ (θ t) t := by
    -- Differentiate the scalarized Hessian slice first; the weighted-gap rule then packages the
    -- derivative into the combined operator spelling.
    simpa [ψ, θ, d] using
      scalarized_hessian_line_hasDerivAt
        (dom := dom) (Mf := Mf) (f := f) (hself := hself)
        (x := x) (d := d) (u := u) (w := wz) (t := t) hp
  have hweighted :
      HasDerivAt
        (fun q : ℝ ↦ ((1 - τ * a) / (1 - q * a)) * (ψ q - ψ τ))
        ((((1 - τ * a) / (1 - t * a) ^ (2 : ℕ)) *
          (a * (ψ t - ψ τ) + (1 - t * a) * θ t))) t := by
    exact weightedEndpointWitnessTailGapHasDerivAt (a := a) (τ := τ) (s := t) hden hψ
  have hslope :
      (((1 - τ * a) / (1 - t * a) ^ (2 : ℕ)) *
        (a * (ψ t - ψ τ) + (1 - t * a) * θ t)) =
        (((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
    have hKu :
        inner ℝ wz (K u) = a * (ψ t - ψ τ) + (1 - t * a) * θ t := by
      simp [K, ψ, θ, p, z, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, inner_add_right, inner_sub_right, inner_smul_right]
    rw [hKu, div_eq_mul_inv]
  have hΦ_eq :
      Φ = fun q : ℝ ↦ ((1 - τ * a) / (1 - q * a)) * (ψ q - ψ τ) := by
    funext q
    simp [Φ, ψ, z, inner_sub_right, inner_smul_right]
  convert hweighted.congr_deriv hslope using 1

/-- Helper for Theorem 5.2.2: after rewriting the direct short-interval integrand as one pairing,
the remaining missing step is the scaled same-metric pairing bound for the combined live
operator. -/
theorem weightedTailGapPrimitiveIncrementMixedPairingBoundOnIcc
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t q : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) (hq : q ∈ Set.Icc t τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let Φ : ℝ → ℝ := fun s ↦
      inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
    |Φ q - Φ t| ≤
      (((q - t) * (((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a)))) *
          ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  -- Route correction: control the weighted-gap derivative frontier by integrating the already
  -- proved direct integrand bound on the short subinterval `[t, q]`.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ wz (hessian f (x + s • d) u)
  let θ : ℝ → ℝ := fun s ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + s • d) d) u)
  let Φ : ℝ → ℝ := fun s ↦
    inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
  let ω : ℝ → ℝ := fun s ↦ ((1 - τ * a) / (1 - s * a)) * θ s
  let K : ℝ → ℝ := fun s ↦
    ((((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ s))
  let integrand : ℝ → ℝ := fun s ↦ K s - ω s
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hq0τ : q ∈ Set.Icc (0 : ℝ) τ := ⟨le_trans ht.1 hq.1, hq.2⟩
  have hden_pos : ∀ s ∈ Set.Icc t τ, 0 < 1 - s * a := by
    intro s hs
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    have hsa_le_τa : s * a ≤ τ * a := by
      simpa using mul_le_mul_of_nonneg_right hs.2 ha_nonneg
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    have hsa_lt_one : s * a < 1 := by
      linarith [ha_lt_one, hsa_le_τa, hτa_le_a]
    linarith
  have hψ_cont : ContinuousOn ψ (Set.Icc t τ) := by
    -- Keep the scalarized Hessian line on the whole short interval `[t, τ]`.
    simpa [ψ, d] using
      scalarizedHessianLineContinuousOn
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (y := y) (u := u) (w := wz) hx hy hτ ht
  have hθ_cont : ContinuousOn θ (Set.Icc t τ) := by
    -- The scalarized third-derivative line is continuous on the same interval.
    simpa [θ, d] using
      scalarizedHessianLineDerivContinuousOn
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (y := y) (u := u) (w := wz) hx hy hτ ht
  have hψ_deriv :
      ∀ s ∈ Set.Ioo t τ, HasDerivAt ψ (θ s) s := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans ht.1 (le_of_lt hs.1), le_trans (le_of_lt hs.2) hτ.2⟩
    have hxs : x + s • d ∈ dom := by
      exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hs01)
    -- Differentiate the scalarized Hessian line at the live short-subsegment point.
    simpa [ψ, θ, d] using
      scalarized_hessian_line_hasDerivAt
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (d := d) (u := u) (w := wz) (t := s) hxs
  have hψ_cont_q : ContinuousOn ψ (Set.Icc q τ) := by
    exact hψ_cont.mono <| by
      intro s hs
      exact ⟨le_trans hq.1 hs.1, hs.2⟩
  have hθ_cont_q : ContinuousOn θ (Set.Icc q τ) := by
    exact hθ_cont.mono <| by
      intro s hs
      exact ⟨le_trans hq.1 hs.1, hs.2⟩
  have hψ_deriv_q :
      ∀ s ∈ Set.Ioo q τ, HasDerivAt ψ (θ s) s := by
    intro s hs
    exact hψ_deriv s ⟨lt_of_le_of_lt hq.1 hs.1, hs.2⟩
  have hden_pos_q : ∀ s ∈ Set.Icc q τ, 0 < 1 - s * a := by
    intro s hs
    exact hden_pos s ⟨le_trans hq.1 hs.1, hs.2⟩
  have hω_cont : ContinuousOn ω (Set.Icc t τ) := by
    have hweight_cont :
        ContinuousOn (fun s : ℝ ↦ ((1 - τ * a) / (1 - s * a))) (Set.Icc t τ) := by
      -- The fixed-endpoint rational weight stays continuous because its denominator is positive.
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun s : ℝ ↦ 1 - s * a) by continuity).continuousOn
      · intro s hs
        exact (hden_pos s hs).ne'
    exact hweight_cont.mul hθ_cont
  have hK_cont : ContinuousOn K (Set.Icc t τ) := by
    have hpow_inv :
        ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc t τ) := by
      have hbase :
          ContinuousOn
            (fun s : ℝ ↦ (1 : ℝ) / (1 - s * a) ^ (2 : ℕ)) (Set.Icc t τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact
            (show Continuous (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro s hs
          exact pow_ne_zero 2 ((hden_pos s hs).ne')
      simpa [one_div] using hbase
    have hkernel_weight :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc t τ) := by
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    have hgap_cont : ContinuousOn (fun s : ℝ ↦ ψ τ - ψ s) (Set.Icc t τ) := by
      exact continuous_const.continuousOn.sub hψ_cont
    exact hkernel_weight.mul hgap_cont
  have hintegrand_cont : ContinuousOn integrand (Set.Icc t τ) := hK_cont.sub hω_cont
  have hintegrand_cont_tq : ContinuousOn integrand (Set.Icc t q) := by
    exact hintegrand_cont.mono <| by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 hq.2⟩
  have hintegrand_int_tq : IntervalIntegrable integrand MeasureTheory.volume t q := by
    exact hintegrand_cont_tq.intervalIntegrable_of_Icc hq.1
  have habs_integrand_int_tq :
      IntervalIntegrable (fun s : ℝ ↦ |integrand s|) MeasureTheory.volume t q := by
    simpa [Real.norm_eq_abs] using hintegrand_int_tq.norm
  have hΦτ : Φ τ = 0 := by
    -- The weighted primitive vanishes at its fixed endpoint.
    simp [Φ, z]
  have htail_identity_t :
      Φ t - Φ τ = ∫ s in t..τ, integrand s := by
    -- Evaluate the weighted tail-gap identity on `[t, τ]`.
    calc
      Φ t - Φ τ = Φ t := by
        rw [hΦτ]
        ring
      _ = ((1 - τ * a) / (1 - t * a)) * (ψ t - ψ τ) := by
        simp [Φ, ψ, z, ContinuousLinearMap.sub_apply, inner_sub_right, inner_smul_right]
      _ = ∫ s in t..τ, K s - ω s := by
        simpa [K, ω] using
          weightedTailGapEndpointIdentityOnIcc
            (a := a) (τ := τ) (s0 := t) (ψ := ψ) (θ := θ)
            ht.2 hψ_cont hθ_cont hψ_deriv hden_pos
      _ = ∫ s in t..τ, integrand s := by
        rfl
  have htail_identity_q :
      Φ q - Φ τ = ∫ s in q..τ, integrand s := by
    -- Evaluate the same identity on `[q, τ]`.
    calc
      Φ q - Φ τ = Φ q := by
        rw [hΦτ]
        ring
      _ = ((1 - τ * a) / (1 - q * a)) * (ψ q - ψ τ) := by
        simp [Φ, ψ, z, ContinuousLinearMap.sub_apply, inner_sub_right, inner_smul_right]
      _ = ∫ s in q..τ, K s - ω s := by
        simpa [K, ω] using
          weightedTailGapEndpointIdentityOnIcc
            (a := a) (τ := τ) (s0 := q) (ψ := ψ) (θ := θ)
            hq.2 hψ_cont_q hθ_cont_q hψ_deriv_q hden_pos_q
      _ = ∫ s in q..τ, integrand s := by
        rfl
  have htail_increment :
      Φ q - Φ t = -∫ s in t..q, integrand s := by
    have hintegrand_cont_qτ : ContinuousOn integrand (Set.Icc q τ) := by
      exact hintegrand_cont.mono <| by
        intro s hs
        exact ⟨le_trans hq.1 hs.1, hs.2⟩
    have hintegrand_int_qτ : IntervalIntegrable integrand MeasureTheory.volume q τ := by
      exact hintegrand_cont_qτ.intervalIntegrable_of_Icc hq.2
    have hadd :
        (∫ s in t..q, integrand s) + ∫ s in q..τ, integrand s = ∫ s in t..τ, integrand s := by
      exact
        intervalIntegral.integral_add_adjacent_intervals
          (f := integrand) (μ := MeasureTheory.volume) hintegrand_int_tq hintegrand_int_qτ
    -- Subtract the two FTC identities to isolate the short increment on `[t, q]`.
    calc
      Φ q - Φ t = (Φ q - Φ τ) - (Φ t - Φ τ) := by
        ring_nf
      _ = (∫ s in q..τ, integrand s) - (∫ s in t..τ, integrand s) := by
        rw [htail_identity_q, htail_identity_t]
      _ = -∫ s in t..q, integrand s := by
        rw [← hadd]
        ring
  have hmajorant_cont_tq :
      ContinuousOn
        (fun s : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x])
        (Set.Icc t q) := by
    have hpow_inv :
        ContinuousOn (fun s : ℝ ↦ ((1 - s * a) ^ (2 : ℕ))⁻¹) (Set.Icc t q) := by
      have hbase :
          ContinuousOn (fun s : ℝ ↦ (1 - s * a) ^ (2 : ℕ)) (Set.Icc t q) := by
        exact ((continuous_const.sub (continuous_id'.mul continuous_const)).continuousOn).pow 2
      exact hbase.inv₀ (by
        intro s hs
        exact pow_ne_zero 2 ((hden_pos s ⟨hs.1, le_trans hs.2 hq.2⟩).ne'))
    have hkernel_cont :
        ContinuousOn
          (fun s : ℝ ↦ (((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc t q) := by
      exact continuous_const.continuousOn.mul hpow_inv
    exact (hkernel_cont.mul continuous_const.continuousOn).mul continuous_const.continuousOn
  have hmajorant_int_tq :
      IntervalIntegrable
        (fun s : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x])
        MeasureTheory.volume t q := by
    exact hmajorant_cont_tq.intervalIntegrable_of_Icc hq.1
  have hintegrand_pointwise_tq :
      ∀ s ∈ Set.Icc t q,
        |integrand s| ≤
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
    intro s hs
    have hsτ : s ∈ Set.Icc t τ := ⟨hs.1, le_trans hs.2 hq.2⟩
    -- Reuse the direct short-interval integrand estimate on each point of `[t, q]`.
    simpa [integrand, K, ω, r, a, d, z, ψ, θ] using
      weightedTailGapPrimitiveIntegrandBoundOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (s := t) (t := s) hτ ht hsτ
  have hfactor :
      ∫ s in t..q,
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x]
        =
          (((1 - τ * a) * (∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
              ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
    -- Factor the endpoint norms and the fixed outer weight out of the short-subsegment integral.
    calc
      ∫ s in t..q,
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x]
          =
            (∫ s in t..q,
              (((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
              ‖u‖[f; x] := by
              rw [intervalIntegral.integral_mul_const]
      _ =
          ((∫ s in t..q,
            ((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
              rw [intervalIntegral.integral_mul_const]
      _ =
          (((1 - τ * a) * (∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
              ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
              congr 2
              simpa [mul_assoc] using
                (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
                  (a := (1 - τ * a))
                  (f := fun s : ℝ ↦ (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
                  (a := t) (b := q))
  have hkernel :
      (1 - τ * a) * (∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹) =
        (q - t) * (((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) := by
    have htfactor_ne : 1 - t * a ≠ 0 := (hden_pos t ⟨le_rfl, ht.2⟩).ne'
    have hqfactor_ne : 1 - q * a ≠ 0 := (hden_pos q ⟨hq.1, hq.2⟩).ne'
    have hq01 : q ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ht.1 hq.1, le_trans hq.2 hτ.2⟩
    have htq : t ∈ Set.Icc (0 : ℝ) q := ⟨ht.1, hq.1⟩
    calc
      (1 - τ * a) * (∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)
          = (1 - τ * a) * (2 * ∫ s in t..q, a * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
              congr 1
              calc
                ∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹
                    = ∫ s in t..q, 2 * (a * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
                        refine intervalIntegral.integral_congr ?_
                        intro s hs
                        ring
                _ = 2 * ∫ s in t..q, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ := by
                        rw [intervalIntegral.integral_const_mul]
      _ = (1 - τ * a) * (2 * (((q - t) * a) / ((1 - q * a) * (1 - t * a)))) := by
            rw [segmentReciprocalSquareIntegral_between (τ := q) (s := t) hq01 htq
              ha_lt_one]
      _ = (q - t) * (((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) := by
            field_simp [htfactor_ne, hqfactor_ne]
  calc
    |Φ q - Φ t| = |∫ s in t..q, integrand s| := by
      rw [htail_increment, abs_neg]
    _ ≤ ∫ s in t..q, |integrand s| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm
              (f := integrand) (μ := MeasureTheory.volume) (a := t) (b := q) hq.1)
    _ ≤
        ∫ s in t..q,
          ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
          exact intervalIntegral.integral_mono_on
            (μ := MeasureTheory.volume) (a := t) (b := q)
            (f := fun s : ℝ ↦ |integrand s|)
            (g := fun s : ℝ ↦
              ((((1 - τ * a) * (2 * a)) * ((1 - s * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
                ‖u‖[f; x])
            hq.1 habs_integrand_int_tq hmajorant_int_tq hintegrand_pointwise_tq
    _ =
        (((1 - τ * a) * (∫ s in t..q, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := hfactor
    _ =
        (((q - t) * (((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a)))) *
            ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
            rw [hkernel]

/-- Helper for Theorem 5.2.2: dividing the short-interval increment bound by the positive gap
`q - t` produces the exact right-difference-quotient estimate used in the derivative step. -/
theorem weightedTailGapPrimitiveDifferenceQuotientBoundOnIoo
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t q : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) (hq : q ∈ Set.Ioo t τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let Φ : ℝ → ℝ := fun s ↦
      inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
    |((Φ q - Φ t) / (q - t))| ≤
      ((((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  -- Normalize the proved increment estimate by the positive denominator `q - t`.
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let Φ : ℝ → ℝ := fun s ↦
    inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
  have hqt_pos : 0 < q - t := sub_pos.mpr hq.1
  have hinc :
      |Φ q - Φ t| ≤
        (((q - t) * (((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a)))) *
          ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
    exact
      weightedTailGapPrimitiveIncrementMixedPairingBoundOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := t) (q := q) hτ ht ⟨le_of_lt hq.1, le_of_lt hq.2⟩
  have hdiv :
      |Φ q - Φ t| / (q - t) ≤
        ((((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    have hinc' :
        |Φ q - Φ t| ≤
          (((((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) * ‖wz‖[f; z]) *
              ‖u‖[f; x]) *
            (q - t) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hinc
    exact (div_le_iff₀ hqt_pos).2 hinc'
  simpa [abs_div, abs_of_pos hqt_pos] using hdiv

/-- Helper for Theorem 5.2.2: the proved right secant quotient estimate is exactly the matching
right-slope bound for the weighted tail-gap path `Φ`. -/
theorem weightedTailGapPrimitiveSlopeBoundOnIoo
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t q : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) (hq : q ∈ Set.Ioo t τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let Φ : ℝ → ℝ := fun s ↦
      inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
    |slope Φ t q| ≤
      ((((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  -- Rewrite the proved right secant quotient bound into the `slope` API consumed by
  -- `HasDerivAt`.
  dsimp
  simpa [slope_def_field] using
    weightedTailGapPrimitiveDifferenceQuotientBoundOnIoo
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
      hx hy hxy (τ := τ) (t := t) (q := q) hτ ht hq

/-- Helper for Theorem 5.2.2: at the fixed endpoint `τ`, the short-interval increment estimate on
`[q, τ]` gives the sharp left-slope majorant. -/
theorem weightedTailGapPrimitiveEndpointSlopeBoundOnIio
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ q : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hτpos : 0 < τ) (hq : q ∈ Set.Ioo (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let Φ : ℝ → ℝ := fun s ↦
      inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
    |slope Φ τ q| ≤
      (((2 * a) / (1 - q * a)) * ‖wz‖[f; z]) * ‖u‖[f; x] := by
  -- Apply the increment bound to `[q, τ]`, divide by `τ - q`, and cancel the fixed endpoint
  -- factor in the denominator.
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let Φ : ℝ → ℝ := fun s ↦
    inner ℝ wz ((((1 - τ * a) / (1 - s * a)) • (hessian f (x + s • d) - hessian f z)) u)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hτfactor_pos : 0 < 1 - τ * a := by
    linarith
  have hτfactor_ne : 1 - τ * a ≠ 0 := hτfactor_pos.ne'
  have hqτ_pos : 0 < τ - q := sub_pos.mpr hq.2
  have hinc :
      |Φ τ - Φ q| ≤
        (((τ - q) * (((1 - τ * a) * (2 * a)) / ((1 - q * a) * (1 - τ * a)))) *
          ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
    exact
      weightedTailGapPrimitiveIncrementMixedPairingBoundOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := q) (q := τ) hτ ⟨le_of_lt hq.1, le_of_lt hq.2⟩
        ⟨le_of_lt hq.2, le_rfl⟩
  have hdiv :
      |Φ τ - Φ q| / (τ - q) ≤
        ((((1 - τ * a) * (2 * a)) / ((1 - q * a) * (1 - τ * a))) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    have hinc' :
        |Φ τ - Φ q| ≤
          (((((1 - τ * a) * (2 * a)) / ((1 - q * a) * (1 - τ * a))) * ‖wz‖[f; z]) *
              ‖u‖[f; x]) *
            (τ - q) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hinc
    exact (div_le_iff₀ hqτ_pos).2 hinc'
  have hcoeff :
      (((1 - τ * a) * (2 * a)) / ((1 - q * a) * (1 - τ * a))) = (2 * a) / (1 - q * a) := by
    field_simp [hτfactor_ne]
  simpa [r, a, d, z, Φ, slope_comm, slope_def_field, abs_div, abs_of_pos hqτ_pos,
    abs_sub_comm, hcoeff] using hdiv

/-- Helper for Theorem 5.2.2: a continuous majorant on one-sided secant slopes passes to the
actual derivative at the endpoint. -/
theorem abs_deriv_le_of_eventually_slope_bound
    {L : Filter ℝ} [L.NeBot] {Φ m : ℝ → ℝ} {t B : ℝ}
    (hL_ne : L ≤ nhdsWithin t ({t}ᶜ)) (hL : L ≤ nhds t) (hderiv : HasDerivAt Φ B t)
    (hm_cont : ContinuousAt m t)
    (hbound : ∀ᶠ q in L, |slope Φ t q| ≤ m q) :
    |B| ≤ m t := by
  have hslope :
      Filter.Tendsto (fun q : ℝ ↦ |slope Φ t q|) L (nhds |B|) := by
    simpa [Real.norm_eq_abs] using (hderiv.tendsto_slope.mono_left hL_ne).norm
  have hmajorant : Filter.Tendsto m L (nhds (m t)) := hm_cont.tendsto.mono_left hL
  exact le_of_tendsto_of_tendsto hslope hmajorant hbound

/-- Helper for Theorem 5.2.2: at the endpoint `t = τ`, the weighted combined pairing bound
follows from the left-slope estimate for the normalized tail-gap path. -/
theorem weightedTailGapPrimitiveScaledCombinedPairingBoundAtEndpointZero
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + (0 : ℝ) • d
    let p := x + (0 : ℝ) • d
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - (0 : ℝ) * a) • fderiv ℝ (hessian f) p d
    |(((1 - (0 : ℝ) * a) * ((1 - (0 : ℝ) * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - (0 : ℝ) * a) * (2 * a)) * ((1 - (0 : ℝ) * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  dsimp
  have hs0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := by simp
  simpa using
    weightedEndpointWitnessScaledDerivPairingBound
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (w := wz)
      hx hy hxy (τ := (0 : ℝ)) (s := (0 : ℝ)) (by simp) hs0

/-- Helper for Theorem 5.2.2: at a positive endpoint `τ > 0`, the weighted combined pairing
bound follows from the left-slope estimate for the normalized tail-gap path. -/
theorem weightedTailGapPrimitiveScaledCombinedPairingBoundAtPositiveEndpoint
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hτpos : 0 < τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + τ • d
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - τ * a) • fderiv ℝ (hessian f) p d
    |(((1 - τ * a) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + τ • d
  let Φ : ℝ → ℝ := fun q ↦
    inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
  let K : E →L[ℝ] E :=
    a • (hessian f p - hessian f z) + (1 - τ * a) • fderiv ℝ (hessian f) p d
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have htfactor_pos : 0 < 1 - τ * a := by
    linarith [show a < 1 by
      dsimp [a]
      simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt]
  have htfactor_ne : 1 - τ * a ≠ 0 := htfactor_pos.ne'
  have hΦderiv :
      HasDerivAt Φ
        ((((1 - τ * a) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))) τ := by
    simpa [r, a, d, z, p, Φ, K] using
      weightedTailGapPrimitiveWeightedGapScalar_hasDerivAt
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := τ) hτ ⟨hτ.1, le_rfl⟩
  let mLeft : ℝ → ℝ := fun q ↦
    (((2 * a) / (1 - q * a)) * ‖wz‖[f; z]) * ‖u‖[f; x]
  have hmLeft_cont : ContinuousAt mLeft τ := by
    have hline :
        ContinuousAt (fun q : ℝ ↦ 1 - q * a) τ := by
      simpa using (continuous_const.sub (continuous_id'.mul continuous_const)).continuousAt
    dsimp [mLeft]
    exact (continuousAt_const.div hline htfactor_ne).mul continuousAt_const |>.mul
      continuousAt_const
  have hq_mem : Set.Ioo (0 : ℝ) τ ∈ nhdsWithin τ (Set.Iio τ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (0 : ℝ), Ioi_mem_nhds hτpos, ?_⟩
    intro q hq
    exact hq
  have hbound :
      ∀ᶠ q in nhdsWithin τ (Set.Iio τ),
        |slope Φ τ q| ≤ mLeft q := by
    refine Filter.mem_of_superset hq_mem ?_
    intro q hq
    simpa [r, a, d, z, Φ] using
      weightedTailGapPrimitiveEndpointSlopeBoundOnIio
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (q := q) hτ hτpos hq
  have hle :
      |(((1 - τ * a) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤ mLeft τ := by
    exact
      abs_deriv_le_of_eventually_slope_bound
        (L := nhdsWithin τ (Set.Iio τ))
        (show nhdsWithin τ (Set.Iio τ) ≤ nhdsWithin τ ({τ}ᶜ) from
          nhdsWithin_mono τ (by
            intro q hq
            simpa using hq.ne))
        nhdsWithin_le_nhds hΦderiv hmLeft_cont hbound
  have hcoeff :
      mLeft τ =
        ((((1 - τ * a) * (2 * a)) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    dsimp [mLeft]
    field_simp [htfactor_ne]
  simpa [r, a, d, z, p, K, mLeft] using
    (calc
      |(((1 - τ * a) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤ mLeft τ := hle
      _ = ((((1 - τ * a) * (2 * a)) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := hcoeff)

/-- Helper for Theorem 5.2.2: at the endpoint `t = τ`, the weighted combined pairing bound
follows from the left-slope estimate for the normalized tail-gap path. -/
theorem weightedTailGapPrimitiveScaledCombinedPairingBoundAtEndpoint
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + τ • d
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - τ * a) • fderiv ℝ (hessian f) p d
    |(((1 - τ * a) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - τ * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  by_cases hτzero : τ = 0
  · subst hτzero
    simpa using
      weightedTailGapPrimitiveScaledCombinedPairingBoundAtEndpointZero
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy
  · have hτpos : 0 < τ := by
      exact lt_of_le_of_ne hτ.1 (Ne.symm hτzero)
    simpa using
      weightedTailGapPrimitiveScaledCombinedPairingBoundAtPositiveEndpoint
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) hτ hτpos

/-- Helper for Theorem 5.2.2: at an interior point `t < τ`, the weighted combined pairing bound
comes from the right-slope estimate for the normalized tail-gap path. -/
theorem weightedTailGapPrimitiveScaledCombinedPairingBoundBeforeEndpoint
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) (htt : t < τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + t • d
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
    |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let Φ : ℝ → ℝ := fun q ↦
    inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
  let K : E →L[ℝ] E :=
    a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hta_le_a : t * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right (le_trans ht.2 hτ.2) ha_nonneg
  have htfactor_pos : 0 < 1 - t * a := by
    linarith
  have htfactor_ne : 1 - t * a ≠ 0 := htfactor_pos.ne'
  have hΦderiv :
      HasDerivAt Φ
        ((((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))) t := by
    -- Import the exact derivative spelling of the weighted tail-gap path before comparing it to
    -- slope bounds.
    simpa [r, a, d, z, p, Φ, K] using
      weightedTailGapPrimitiveWeightedGapScalar_hasDerivAt
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := t) hτ ht
  let mRight : ℝ → ℝ := fun q ↦
      ((((1 - τ * a) * (2 * a)) / ((1 - t * a) * (1 - q * a))) * ‖wz‖[f; z]) *
        ‖u‖[f; x]
  have hmRight_cont : ContinuousAt mRight t := by
    have hline :
        ContinuousAt (fun q : ℝ ↦ 1 - q * a) t := by
      simpa using (continuous_const.sub (continuous_id'.mul continuous_const)).continuousAt
    have hden :
        ContinuousAt (fun q : ℝ ↦ (1 - t * a) * (1 - q * a)) t := by
      exact continuousAt_const.mul hline
    dsimp [mRight]
    exact (continuousAt_const.div hden (mul_ne_zero htfactor_ne htfactor_ne)).mul
      continuousAt_const |>.mul continuousAt_const
  have hq_mem : Set.Ioo t τ ∈ nhdsWithin t (Set.Ioi t) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio τ, Iio_mem_nhds htt, ?_⟩
    intro q hq
    exact hq
  have hbound :
      ∀ᶠ q in nhdsWithin t (Set.Ioi t),
        |slope Φ t q| ≤ mRight q := by
    refine Filter.mem_of_superset hq_mem ?_
    intro q hq
    -- On the right of `t`, the existing quotient theorem is already the needed slope bound.
    simpa [r, a, d, z, Φ] using
      weightedTailGapPrimitiveSlopeBoundOnIoo
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := t) (q := q) hτ ht hq
  have hle :
      |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤ mRight t := by
    exact
      abs_deriv_le_of_eventually_slope_bound
        (L := nhdsWithin t (Set.Ioi t))
        (show nhdsWithin t (Set.Ioi t) ≤ nhdsWithin t ({t}ᶜ) from
          nhdsWithin_mono t (by
            intro q hq
            exact ne_of_gt hq))
        nhdsWithin_le_nhds hΦderiv hmRight_cont hbound
  have hcoeff :
      mRight t =
        ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    dsimp [mRight]
    field_simp [htfactor_ne]
  simpa [r, a, d, z, p, K, mRight] using
    (calc
      |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤ mRight t := hle
      _ = ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := hcoeff)

/-- Helper for Theorem 5.2.2: the normalized weighted-gap derivative satisfies the sharp
endpoint-metric bound on every short interval point. Splitting the endpoint and interior cases
keeps the elaboration budget local. -/
theorem weightedTailGapPrimitiveScaledCombinedPairingBoundOnIcc
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let p := x + t • d
    let K : E →L[ℝ] E :=
      a • (hessian f p - hessian f z) + (1 - t * a) • fderiv ℝ (hessian f) p d
    |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  -- Route correction: the proved polarization helper reduces any future same-metric quadratic
  -- estimate to a bilinear one, but using it naively here still loses one factor of
  -- `(1 - τ * a)` when `‖u‖[f; z]` is transported back to `‖u‖[f; x]`. The increment theorem
  -- above now isolates the real frontier: converting the right/left slope bounds for `Φ` into the
  -- exact mixed-metric derivative bound at `t`, including the endpoint branch `t = τ`.
  by_cases hEq : t = τ
  · -- Keep the rewrite local: normalizing the whole context via `subst` is needlessly expensive.
    simpa [hEq] using
      weightedTailGapPrimitiveScaledCombinedPairingBoundAtEndpoint
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) hτ
  · have htt : t < τ := lt_of_le_of_ne ht.2 hEq
    simpa [hEq] using
      weightedTailGapPrimitiveScaledCombinedPairingBoundBeforeEndpoint
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := t) hτ ht htt

/-- Helper for Theorem 5.2.2: on a short interval `[s, τ]`, the direct weighted tail-gap
integrand admits the sharp reciprocal-square endpoint-witness majorant in the fixed metric at
`z = x + τ • (y - x)`. -/
theorem weightedTailGapPrimitiveIntegrandBoundOnIcc
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) {τ s t : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) (ht : t ∈ Set.Icc s τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
    |((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
        (((1 - τ * a) / (1 - t * a)) * θ t)| ≤
      ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
        ‖u‖[f; x] :=
      by
  -- Route correction: rewrite the direct short-interval integrand as one pairing, then isolate
  -- the remaining blocker as the same-metric combined-operator estimate at the fixed endpoint.
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let p : E := x + t • d
  let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
  let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
  let K : E →L[ℝ] E :=
    a • (hessian f p - hessian f z) +
      (1 - t * a) • fderiv ℝ (hessian f) p d
  have ht0τ : t ∈ Set.Icc (0 : ℝ) τ := ⟨le_trans hs.1 ht.1, ht.2⟩
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hτfactor_nonneg : 0 ≤ 1 - τ * a := by
    linarith
  have hrewrite :
      ((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
          (((1 - τ * a) / (1 - t * a)) * θ t) =
        -(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u)) := by
    simpa [r, a, d, z, ψ, θ, K] using
      weightedTailGapPrimitiveIntegrand_eq_negCombinedPairing
        (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz) (τ := τ) (t := t)
  have hpair :
      |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| ≤
        ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    -- The only remaining missing ingredient is now the fixed-`z` scaled bound on the weighted-gap
    -- derivative frontier.
    simpa [r, a, d, z, p, K] using
      weightedTailGapPrimitiveScaledCombinedPairingBoundOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (t := t) hτ ht0τ
  calc
    |((((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ t)) -
          (((1 - τ * a) / (1 - t * a)) * θ t)|
        = |(((1 - τ * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * inner ℝ wz (K u))| := by
            rw [hrewrite, abs_neg]
    _ ≤
        ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := hpair

/-- Helper for Theorem 5.2.2: the kernel majorant factors the endpoint norms completely out of
the interval integral. -/
theorem weightedTailGapMajorantIntegralFactor
    {a τ s C B : ℝ} :
    ∫ t in s..τ, ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B
      =
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * C) * B := by
  -- Pull the constant endpoint norms out of the majorant before evaluating the reciprocal-square
  -- kernel.
  calc
    ∫ t in s..τ, ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B
        =
          (∫ t in s..τ,
            (((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B := by
              rw [intervalIntegral.integral_mul_const]
    _ =
        ((∫ t in s..τ,
          ((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * C) * B := by
            rw [intervalIntegral.integral_mul_const]
    _ =
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * C) * B := by
          congr 2
          simpa [mul_assoc] using
            (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (1 - τ * a))
              (f := fun t : ℝ ↦ (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)
              (a := s) (b := τ))

/-- Helper for Theorem 5.2.2: on a short interval `[s, τ]`, the fixed-endpoint primitive drop is
bounded by the reciprocal-square kernel after the by-parts normalization keeps only the weighted
live integrand. -/
theorem weightedTailGapPrimitiveIntegralMajorantOnIcc
    {x y u wz : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let z := x + τ • d
    let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
    let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
    let Φ : ℝ → ℝ := fun q ↦
      inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
    |Φ s - Φ τ| ≤
      (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[f; z]) *
        ‖u‖[f; x] := by
  -- Route correction: keep the original short-interval identity `Φ s - Φ τ = ∫ (K - ω)` and
  -- integrate the direct `K - ω` majorant, instead of reopening the by-parts shell route.
  dsimp
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let z : E := x + τ • d
  let ψ : ℝ → ℝ := fun q ↦ inner ℝ wz (hessian f (x + q • d) u)
  let θ : ℝ → ℝ := fun q ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + q • d) d) u)
  let Φ : ℝ → ℝ := fun q ↦
    inner ℝ wz ((((1 - τ * a) / (1 - q * a)) • (hessian f (x + q • d) - hessian f z)) u)
  let ω : ℝ → ℝ := fun q ↦ ((1 - τ * a) / (1 - q * a)) * θ q
  let K : ℝ → ℝ := fun q ↦
    ((((1 - τ * a) * a) * ((1 - q * a) ^ (2 : ℕ))⁻¹) * (ψ τ - ψ q))
  let integrand : ℝ → ℝ := fun q ↦ K q - ω q
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hden_pos : ∀ t ∈ Set.Icc s τ, 0 < 1 - t * a := by
    intro t ht
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    have hta_le_τa : t * a ≤ τ * a := by
      simpa using mul_le_mul_of_nonneg_right ht.2 ha_nonneg
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    have hta_lt_one : t * a < 1 := by
      linarith [ha_lt_one, hta_le_τa, hτa_le_a]
    linarith
  have hψ_cont : ContinuousOn ψ (Set.Icc s τ) := by
    -- The scalarized Hessian line stays continuous on the short interval.
    simpa [ψ, d] using
      scalarizedHessianLineContinuousOn
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (y := y) (u := u) (w := wz) hx hy hτ hs
  have hθ_cont : ContinuousOn θ (Set.Icc s τ) := by
    -- The scalarized third-derivative line is continuous on the same interval.
    simpa [θ, d] using
      scalarizedHessianLineDerivContinuousOn
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (y := y) (u := u) (w := wz) hx hy hτ hs
  have hψ_deriv :
      ∀ t ∈ Set.Ioo s τ, HasDerivAt ψ (θ t) t := by
    intro t ht
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans hs.1 (le_of_lt ht.1), le_trans (le_of_lt ht.2) hτ.2⟩
    have hxt : x + t • d ∈ dom := by
      exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) ht01)
    -- Differentiate the scalarized Hessian line at the live tail-segment point.
    simpa [ψ, θ, d] using
      scalarized_hessian_line_hasDerivAt
        (dom := dom) (Mf := Mf) (f := f) hself
        (x := x) (d := d) (u := u) (w := wz) (t := t) hxt
  have hω_cont : ContinuousOn ω (Set.Icc s τ) := by
    have hweight_cont :
        ContinuousOn (fun t : ℝ ↦ ((1 - τ * a) / (1 - t * a))) (Set.Icc s τ) := by
      -- The fixed-endpoint rational weight is continuous because its denominator stays positive.
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
      · intro t ht
        exact (hden_pos t ht).ne'
    exact hweight_cont.mul hθ_cont
  have hω_int : IntervalIntegrable ω MeasureTheory.volume s τ :=
    hω_cont.intervalIntegrable_of_Icc hs.2
  have hK_cont : ContinuousOn K (Set.Icc s τ) := by
    have hpow_inv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      have hbase :
          ContinuousOn
            (fun t : ℝ ↦ (1 : ℝ) / (1 - t * a) ^ (2 : ℕ)) (Set.Icc s τ) := by
        refine continuousOn_const.div ?_ ?_
        · exact
            (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
        · intro t ht
          exact pow_ne_zero 2 ((hden_pos t ht).ne')
      simpa [one_div] using hbase
    have hkernel_weight :
        ContinuousOn
          (fun t : ℝ ↦ (((1 - τ * a) * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s τ) := by
      simpa [mul_assoc] using ((continuous_const.mul continuous_const).continuousOn.mul hpow_inv)
    have hgap_cont : ContinuousOn (fun t : ℝ ↦ ψ τ - ψ t) (Set.Icc s τ) := by
      exact continuous_const.continuousOn.sub hψ_cont
    exact hkernel_weight.mul hgap_cont
  have hintegrand_cont : ContinuousOn integrand (Set.Icc s τ) := hK_cont.sub hω_cont
  have hintegrand_int : IntervalIntegrable integrand MeasureTheory.volume s τ :=
    hintegrand_cont.intervalIntegrable_of_Icc hs.2
  have habs_integrand_int :
      IntervalIntegrable (fun t : ℝ ↦ |integrand t|) MeasureTheory.volume s τ := by
    simpa [Real.norm_eq_abs] using hintegrand_int.norm
  have hΦτ : Φ τ = 0 := by
    -- At the fixed endpoint `τ`, the primitive vanishes because the Hessian gap is zero.
    simp [Φ, z]
  have htail_identity :
      Φ s - Φ τ = ∫ t in s..τ, K t - ω t := by
    -- Evaluate the weighted tail-gap identity on `[s, τ]` in the primitive spelling.
    calc
      Φ s - Φ τ = Φ s := by
        rw [hΦτ]
        ring
      _ = ((1 - τ * a) / (1 - s * a)) * (ψ s - ψ τ) := by
        simp [Φ, ψ, z, ContinuousLinearMap.sub_apply, inner_sub_right, inner_smul_right]
      _ = ∫ t in s..τ, K t - ω t := by
        simpa [K, ω] using
          weightedTailGapEndpointIdentityOnIcc
            (a := a) (τ := τ) (s0 := s) (ψ := ψ) (θ := θ)
            hs.2 hψ_cont hθ_cont hψ_deriv hden_pos
  have htail_integrand :
      Φ s - Φ τ = ∫ t in s..τ, integrand t := by
    -- Keep the original `K - ω` integrand from the tail-gap identity and bound it directly.
    simpa [integrand] using htail_identity
  have hmajorant_cont :
      ContinuousOn
        (fun t : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x])
        (Set.Icc s τ) := by
    have hpow_inv :
        ContinuousOn (fun t : ℝ ↦ ((1 - t * a) ^ (2 : ℕ))⁻¹) (Set.Icc s τ) := by
      intro t ht'
      have hpoly : ContinuousAt (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) t := by
        simpa using
          ((continuous_const.sub (continuous_id'.mul continuous_const)).continuousAt.pow 2)
      exact (hpoly.inv₀ (pow_ne_zero 2 ((hden_pos t ht').ne'))).continuousWithinAt
    have hkernel_cont :
        ContinuousOn
          (fun t : ℝ ↦ (((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹))
          (Set.Icc s τ) := by
      exact continuous_const.continuousOn.mul hpow_inv
    exact (hkernel_cont.mul continuous_const.continuousOn).mul continuous_const.continuousOn
  have hmajorant_int :
      IntervalIntegrable
        (fun t : ℝ ↦
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x])
        MeasureTheory.volume s τ := by
    exact hmajorant_cont.intervalIntegrable_of_Icc hs.2
  have hintegrand_pointwise :
      ∀ t ∈ Set.Icc s τ,
        |integrand t| ≤
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
    intro t ht
    -- Route correction: consume the direct short-interval integrand estimate, without reopening
    -- the by-parts shell normalization.
    simpa [integrand, K, ω, r, a, d, z, ψ, θ] using
      weightedTailGapPrimitiveIntegrandBoundOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (s := s) (t := t) hτ hs ht
  -- Integrate the pointwise direct-integrand bound on `[s, τ]`, keeping the outer factor
  -- `(1 - τ * a)` outside the final kernel exactly as in the target statement.
  calc
    |Φ s - Φ τ| = |∫ t in s..τ, integrand t| := by
      rw [htail_integrand]
    _ ≤ ∫ t in s..τ, |integrand t| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm
              (f := integrand) (μ := MeasureTheory.volume) (a := s) (b := τ) hs.2)
    _ ≤
        ∫ t in s..τ,
          ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
            ‖u‖[f; x] := by
          exact intervalIntegral.integral_mono_on
            (μ := MeasureTheory.volume) (a := s) (b := τ)
            (f := fun t : ℝ ↦ |integrand t|)
            (g := fun t : ℝ ↦
              ((((1 - τ * a) * (2 * a)) * ((1 - t * a) ^ (2 : ℕ))⁻¹) * ‖wz‖[f; z]) *
                ‖u‖[f; x])
            hs.2 habs_integrand_int hmajorant_int hintegrand_pointwise
    _ = (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) *
          ‖wz‖[f; z]) * ‖u‖[f; x] := by
          simpa [z] using
            weightedTailGapMajorantIntegralFactor
              (a := a) (τ := τ) (s := s) (C := ‖wz‖[f; z]) (B := ‖u‖[f; x])


/-- Helper for Theorem 5.2.2: before transporting the primitive image from `z` to `y`, the
inverse-Hessian witness at the fixed endpoint `z` should already satisfy the sharp pairing bound
against the weighted primitive covector. -/
theorem weightedTailGapPrimitiveSegmentEndpointWitnessBoundAtZ
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ)
    (hz : x + τ • (y - x) ∈ dom) (hHz : (hessian f (x + τ • (y - x))).det ≠ 0) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let Hz := hessian f z
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian f p - Hz)) u
    let wz := Hz.inverse v
    |inner ℝ wz v| ≤
      (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[f; z]) * ‖u‖[f; x] := by
  -- Route correction: the remaining frontier is now the witness-specific pairing estimate at the
  -- fixed endpoint `z`; the dual-norm cancellation and the later `z → y` transport are separate.
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let Hz : E →L[ℝ] E := hessian f z
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian f p - Hz)) u
  let wz : E := Hz.inverse v
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ wz (hessian f (x + t • d) u)
  let θ : ℝ → ℝ := fun t ↦ inner ℝ wz ((fderiv ℝ (hessian f) (x + t • d) d) u)
  let Φ : ℝ → ℝ := fun t ↦
    inner ℝ wz ((((1 - τ * a) / (1 - t * a)) • (hessian f (x + t • d) - Hz)) u)
  let Ψ : ℝ → ℝ := fun t ↦
    (((1 - τ * a) / (1 - t * a) ^ (2 : ℕ)) *
      (a * (ψ t - ψ τ) + (1 - t * a) * θ t))
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hΦτ : Φ τ = 0 := by
    -- At the fixed endpoint `τ`, the weighted primitive vanishes because the Hessian gap is zero.
    simp [Φ, z, Hz]
  have hΦs : Φ s = inner ℝ wz v := by
    -- At the left endpoint `s`, the weighted primitive is exactly the target witness pairing.
    simp [Φ, p, z, Hz, v]
  have hprimitive_rewrite : |inner ℝ wz v| = |Φ s - Φ τ| := by
    -- Rewrite the target pairing as the primitive drop on `[s, τ]`.
    rw [hΦs, hΦτ]
    simp
  have hkernel :
      (1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹) =
        (2 * (τ - s) * a) / (1 - s * a) := by
    -- Evaluate the short-interval reciprocal-square kernel before the final FTC bound.
    calc
      (1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)
          = (1 - τ * a) * (2 * ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹) := by
              congr 1
              calc
                ∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹
                    = ∫ t in s..τ, 2 * (a * ((1 - t * a) ^ (2 : ℕ))⁻¹) := by
                        refine intervalIntegral.integral_congr ?_
                        intro t ht
                        ring
                _ = 2 * ∫ t in s..τ, a * ((1 - t * a) ^ (2 : ℕ))⁻¹ := by
                        rw [intervalIntegral.integral_const_mul]
      _ = (1 - τ * a) *
            (2 * (((τ - s) * a) / ((1 - τ * a) * (1 - s * a)))) := by
              rw [segmentReciprocalSquareIntegral_between (τ := τ) (s := s) hτ hs ha_lt_one]
      _ = (2 * (τ - s) * a) / (1 - s * a) := by
              have hτfactor_ne : 1 - τ * a ≠ 0 := by
                have ha_nonneg : 0 ≤ a := by
                  dsimp [a]
                  exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
                    (hessianLocalNorm_nonneg f x (y - x))
                have hτa_le_a : τ * a ≤ a := by
                  simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
                linarith
              have hsfactor_ne : 1 - s * a ≠ 0 := by
                have ha_nonneg : 0 ≤ a := by
                  dsimp [a]
                  exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
                    (hessianLocalNorm_nonneg f x (y - x))
                have hsa_le_a : s * a ≤ a := by
                  simpa using mul_le_mul_of_nonneg_right (le_trans hs.2 hτ.2) ha_nonneg
                linarith
              field_simp [hτfactor_ne, hsfactor_ne]
  have hprimitive_bound :
      |Φ s - Φ τ| ≤
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := by
    -- The primitive drop is now handled directly by the short-interval by-parts estimate.
    have hraw :=
      weightedTailGapPrimitiveIntegralMajorantOnIcc
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (wz := wz)
        hx hy hxy (τ := τ) (s := s) hτ hs
    simpa [r, a, d, p, z, Hz, Φ] using hraw
  calc
    |inner ℝ wz v| = |Φ s - Φ τ| := hprimitive_rewrite
    _ ≤
        (((1 - τ * a) * (∫ t in s..τ, (2 * a) * ((1 - t * a) ^ (2 : ℕ))⁻¹)) * ‖wz‖[f; z]) *
          ‖u‖[f; x] := hprimitive_bound
    _ = (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[f; z]) * ‖u‖[f; x] := by
          rw [hkernel]


/-- Helper for Theorem 5.2.2: at the fixed endpoint
`z = x + τ • (y - x)`, the weighted primitive covector should already satisfy the sharp short-
subsegment dual-norm bound before any `z → y` transport is applied. -/
theorem weightedTailGapPrimitiveSegmentDualBound
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ)))
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ)
    (hz : x + τ • (y - x) ∈ dom) (hHz : (hessian f (x + τ • (y - x))).det ≠ 0) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    HessianDualLocalNorm.ofDetNeZero f z
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hz)
        hHz
        (toDual ℝ E ((((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u)) ≤
      ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[f; x] := by
  -- Realize the fixed-endpoint dual norm by its inverse-Hessian witness and delegate the only
  -- remaining work to the witness-specific pairing estimate at `z`.
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let Hz : E →L[ℝ] E := hessian f z
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian f p - Hz)) u
  let wz : E := Hz.inverse v
  have hsfactor_pos : 0 < 1 - s * a := by
    have hMf_pos : 0 < (Mf : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
        (hessianLocalNorm_nonneg f x (y - x))
    have hsa_le_a : s * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right (le_trans hs.2 hτ.2) ha_nonneg
    have ha_lt_one : a < 1 := by
      dsimp [a]
      simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
    linarith
  have hcoeff_nonneg : 0 ≤ ((2 * (τ - s) * a) / (1 - s * a)) := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
        (hessianLocalNorm_nonneg f x (y - x))
    have hnum_nonneg : 0 ≤ 2 * (τ - s) * a := by
      exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) (sub_nonneg.mpr hs.2)) ha_nonneg
    exact div_nonneg hnum_nonneg (le_of_lt hsfactor_pos)
  have hpair :
      |inner ℝ wz v| ≤
        (((2 * (τ - s) * a) / (1 - s * a)) * ‖wz‖[f; z]) * ‖u‖[f; x] := by
    -- The remaining blocker is the fixed-endpoint witness pairing estimate in the same metric.
    simpa [r, a, d, p, z, Hz, v, wz] using
      weightedTailGapPrimitiveSegmentEndpointWitnessBoundAtZ
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy (τ := τ) (s := s) hτ hs hz hHz
  simpa [z, v] using
    dualLocalNorm_bound_of_inverseWitness_pairing
      (dom := dom) (Mf := Mf) (f := f) (x := z) (k := v)
      hz hHz hcoeff_nonneg (hessianLocalNorm_nonneg f x u) hpair

/-- Helper for Theorem 5.2.2: the endpoint image of the weighted primitive should satisfy the
sharp endpoint-metric local-norm bound coming from the short-subsegment dual estimate. -/
theorem weightedTailGapPrimitiveEndpointImage_localNorm_bound
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let He := hessian f y
    let q := He.inverse ((((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u)
    ‖q‖[f; y] ≤
      (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[f; x] := by
  -- Transport the primitive covector from the fixed metric at `z` to the endpoint metric at `y`
  -- exactly once, after the same-metric short-segment dual bound is available.
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let He : E →L[ℝ] E := hessian f y
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u
  let q : E := He.inverse v
  let hPosY : He.IsPositive := hself.hessian_isPositive hy
  let δy : ℝ := HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E v)
  have hz : z ∈ dom := by
    exact segment_point_mem (hself := hself) hx hy hτ.1 hτ.2
  have hHz : (hessian f z).det ≠ 0 := by
    let Hy : E →L[ℝ] E := hessian f y
    have hInvY : Hy.IsInvertible := hessian_isInvertible_of_det_ne_zero hHy
    have hy_le :
        hessian f y ≤ ((((1 - a) / (1 - τ * a)) ^ (2 : ℕ))⁻¹) • hessian f z := by
      simpa [r, a, d, z, one_mul] using
        (shortSubsegmentEndpoint_hessian_bounds_fromLivePoint
          (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
          hx hy hxy (τ := (1 : ℝ)) (s := τ) (by norm_num) hτ).2
    have hz_zero_eq (v : E) (hv : hessian f z v = 0) : v = 0 := by
      have hy_nonneg : 0 ≤ inner ℝ v (hessian f y v) :=
        (hself.hessian_isPositive hy).inner_nonneg_right v
      have hy_le_zero : inner ℝ v (hessian f y v) ≤ 0 := by
        have hgap_pos :
            (((((1 - a) / (1 - τ * a)) ^ (2 : ℕ))⁻¹) • hessian f z - hessian f y).IsPositive := by
          rw [← ContinuousLinearMap.le_def]
          exact hy_le
        have hcomp :
            inner ℝ v (hessian f y v) ≤
              ((((1 - a) / (1 - τ * a)) ^ (2 : ℕ))⁻¹) * inner ℝ v (hessian f z v) := by
          have hquad_gap :
              0 ≤ inner ℝ v
                (((((((1 - a) / (1 - τ * a)) ^ (2 : ℕ))⁻¹) • hessian f z) - hessian f y) v) :=
            hgap_pos.inner_nonneg_right v
          simpa [inner_sub_right, inner_smul_right] using hquad_gap
        have hz_quad_zero : inner ℝ v (hessian f z v) = 0 := by
          simp [hv]
        calc
          inner ℝ v (hessian f y v) ≤
              ((((1 - a) / (1 - τ * a)) ^ (2 : ℕ))⁻¹) * inner ℝ v (hessian f z v) := hcomp
          _ = 0 := by rw [hz_quad_zero]; ring
      have hquad_zero : inner ℝ v (hessian f y v) = 0 := le_antisymm hy_le_zero hy_nonneg
      have hHy_zero : hessian f y v = 0 := by
        obtain ⟨m, w, hA⟩ :=
          (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp (hself.hessian_isPositive hy)
        rw [real_inner_comm] at hquad_zero
        rw [hA] at hquad_zero ⊢
        have hsum : ∑ j : Fin m, (inner ℝ (w j) v) ^ (2 : ℕ) = 0 := by
          simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
            pow_two] using hquad_zero
        have hw : ∀ i : Fin m, inner ℝ (w i) v = 0 := by
          intro i
          have hwi_sq : (inner ℝ (w i) v) ^ (2 : ℕ) = 0 := by
            exact
              (Finset.sum_eq_zero_iff_of_nonneg
                (fun j _ ↦ sq_nonneg (inner ℝ (w j) v))).mp hsum i (by simp)
          exact sq_eq_zero_iff.mp hwi_sq
        simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
      exact hInvY.injective (by simpa [Hy] using hHy_zero)
    have hzker : (hessian f z).toLinearMap.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro v w hvw
      have hdiff : hessian f z (v - w) = 0 := by
        simpa [ContinuousLinearMap.sub_apply] using sub_eq_zero.mpr hvw
      have hzero : v - w = 0 := hz_zero_eq (v - w) hdiff
      exact sub_eq_zero.mp hzero
    have hzUnit : IsUnit (hessian f z).toLinearMap :=
      (LinearMap.isUnit_iff_ker_eq_bot ((hessian f z).toLinearMap)).2 hzker
    have hzDetUnit : IsUnit (LinearMap.det (hessian f z).toLinearMap) :=
      (LinearMap.isUnit_iff_isUnit_det ((hessian f z).toLinearMap)).1 hzUnit
    simpa using (isUnit_iff_ne_zero.mp hzDetUnit)
  let δz : ℝ :=
    HessianDualLocalNorm.ofDetNeZero f z (hself.hessian_isPositive hz) hHz (toDual ℝ E v)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
      (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτa_le_a : τ * a ≤ a := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
  have hfactor_nonneg : 0 ≤ (1 - τ * a) / (1 - a) := by
    have hnum_nonneg : 0 ≤ 1 - τ * a := by linarith
    have hden_pos : 0 < 1 - a := by linarith
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hq_realize : ‖q‖[f; y] = δy ∧ inner ℝ v q = δy ^ (2 : ℕ) := by
    -- Rewrite the endpoint image `q` as the inverse-Hessian witness realizing the dual norm at
    -- `y`, so the proof only needs one transport from `z` to `y`.
    simpa [He, q, v, δy] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := y) hy hHy v
  have hq_norm : ‖q‖[f; y] = δy := hq_realize.1
  have hδy_le : δy ≤ ((1 - τ * a) / (1 - a)) * δz := by
    -- Transport the already-fixed dual norm at `z` to the true endpoint metric at `y` once.
    simpa [r, a, z, δy, δz] using
      segmentPointDualLocalNorm_le_endpointFactor_ofDetNeZero
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
        hx hy hxy (τ := τ) hτ hHy hHz v
  have hδz_le :
      δz ≤ ((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[f; x] := by
    -- The remaining missing premise is the same-metric sharp dual bound at the fixed endpoint
    -- `z`; the current theorem now consumes it without reopening the mixed `p/z/y` route.
    simpa [r, a, d, p, z, v, δz] using
      weightedTailGapPrimitiveSegmentDualBound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy (τ := τ) (s := s) hτ hs hz hHz
  calc
    ‖q‖[f; y] = δy := hq_norm
    _ ≤ ((1 - τ * a) / (1 - a)) * δz := hδy_le
    _ ≤ ((1 - τ * a) / (1 - a)) *
          (((2 * (τ - s) * a) / (1 - s * a)) * ‖u‖[f; x]) := by
            exact mul_le_mul_of_nonneg_left hδz_le hfactor_nonneg
    _ = (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
          ‖u‖[f; x] := by
          ring


/-- Helper for Theorem 5.2.2: once the endpoint image `q` has the sharp endpoint-metric bound,
the weighted primitive pairing follows by Cauchy in the endpoint metric at `y`. -/
theorem weightedTailGapPrimitive_boundAtEndpointViaWitnessImage
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {τ s : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) τ) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let d := y - x
    let p := x + s • d
    let z := x + τ • d
    let H := hessian f x
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • d)
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    let v := (((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u
    |inner ℝ w v| ≤
      ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
        ‖w‖[f; y]) * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let d : E := y - x
  let p : E := x + s • d
  let z : E := x + τ • d
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • d)
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let v : E := (((1 - τ * a) / (1 - s * a)) • (hessian f p - hessian f z)) u
  let q : E := He.inverse v
  let hPosY : He.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  let δres : ℝ := HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E k)
  have hw_realize : ‖w‖[f; y] = δres ∧ inner ℝ k w = δres ^ (2 : ℕ) := by
    -- The endpoint inverse-Hessian witness at `y` realizes the dual norm of the residual `k`.
    simpa [He, w, δres, k] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := y) hy hHy k
  have hw_norm : ‖w‖[f; y] = δres := hw_realize.1
  have hδres_nonneg : 0 ≤ δres := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hdual_apply :
      |inner ℝ q k| ≤ δres * ‖q‖[f; y] := by
    -- Test the residual covector `k` against the endpoint image `q` in the endpoint metric.
    simpa [δres, real_inner_comm] using
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
        (Mf := Mf) (f := f) (x := y) (v := k) (z := q) hy hHy
  have hq_bound :
      ‖q‖[f; y] ≤
        (((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) * ‖u‖[f; x] := by
    -- This is the isolated sharp endpoint-image estimate for the primitive vector.
    simpa [r, a, d, p, z, He, v, q] using
      weightedTailGapPrimitiveEndpointImage_localNorm_bound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy hHy (τ := τ) (s := s) hτ hs
  -- Rewrite the primitive pairing through `q`, then apply endpoint Cauchy and the image bound.
  calc
    |inner ℝ w v| = |inner ℝ q k| := by
      rw [weightedTailGapPrimitive_pairing_eq_averageResidualImage
        (Mf := Mf) (f := f) (x := x) (y := y) (u := u) hy hHy (τ := τ) (s := s)]
    _ ≤ δres * ‖q‖[f; y] := hdual_apply
    _ ≤ δres *
          ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
            ‖u‖[f; x]) := by
            exact mul_le_mul_of_nonneg_left hq_bound hδres_nonneg
    _ = ((((1 - τ * a) / (1 - a)) * ((2 * (τ - s) * a) / (1 - s * a))) *
          ‖w‖[f; y]) * ‖u‖[f; x] := by
          rw [← hw_norm]
          ring

/-- Helper for Theorem 5.2.2: the fixed-`τ` endpoint-witness residual estimate first closes with
an unsimplified reciprocal-square kernel before the scalar integral is evaluated explicitly. -/
theorem average_hessian_residual_endpoint_witness_integrand_sharp_bound
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let z := x + τ • (y - x)
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    |inner ℝ w ((H - hessian f z) u)| ≤
      (((1 - τ * a) / (1 - a)) *
        (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
          ‖w‖[f; y] * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let z : E := x + τ • (y - x)
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let d : E := y - x
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτfactor_pos : 0 < 1 - τ * a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ))
        (hessianLocalNorm_nonneg f x (y - x))
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hs0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) τ := ⟨le_rfl, hτ.1⟩
  have hscaled_pointwise :
      |inner ℝ w ((1 - τ * a) • ((H - hessian f z) u))| ≤
        ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[f; y]) * ‖u‖[f; x] := by
    -- Specialize the short-segment witness-image bound to the basepoint `s = 0`.
    simpa [r, a, d, H, G, k, He, w, z] using
      weightedTailGapPrimitive_boundAtEndpointViaWitnessImage
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy hHy (τ := τ) (s := (0 : ℝ)) hτ hs0
  have hscaled :
      (1 - τ * a) * |inner ℝ w ((H - hessian f z) u)| ≤
        ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[f; y]) * ‖u‖[f; x] := by
    calc
      (1 - τ * a) * |inner ℝ w ((H - hessian f z) u)| =
          |inner ℝ w ((1 - τ * a) • ((H - hessian f z) u))| := by
            rw [inner_smul_right, abs_mul, abs_of_nonneg (le_of_lt hτfactor_pos)]
      _ ≤ ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[f; y]) * ‖u‖[f; x] :=
        hscaled_pointwise
  have hinner_split :
      ∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
        ∫ s in (0 : ℝ)..τ, 2 * (a * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    ring
  have hinner :
      ∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
        (2 * τ * a) / (1 - τ * a) := by
    calc
      ∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
          ∫ s in (0 : ℝ)..τ, 2 * (a * ((1 - s * a) ^ (2 : ℕ))⁻¹) := hinner_split
      _ = 2 * ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ := by
            rw [intervalIntegral.integral_const_mul]
      _ = 2 * ((τ * a) / (1 - τ * a)) := by
            rw [segmentReciprocalSquareIntegral_upto hτ ha_lt_one]
      _ = (2 * τ * a) / (1 - τ * a) := by
            ring
  have htarget_scaled :
      (1 - τ * a) * |inner ℝ w ((H - hessian f z) u)| ≤
        (1 - τ * a) *
          ((((1 - τ * a) / (1 - a)) *
            (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
              ‖w‖[f; y] * ‖u‖[f; x]) := by
    calc
      (1 - τ * a) * |inner ℝ w ((H - hessian f z) u)| ≤
          ((((1 - τ * a) / (1 - a)) * (2 * τ * a)) * ‖w‖[f; y]) * ‖u‖[f; x] := hscaled
      _ = (1 - τ * a) *
            ((((1 - τ * a) / (1 - a)) *
              (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
                ‖w‖[f; y] * ‖u‖[f; x]) := by
            rw [hinner]
            field_simp [hτfactor_pos.ne']
  have habs_target :
      |inner ℝ w ((H - hessian f z) u)| ≤
        (((1 - τ * a) / (1 - a)) *
          (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
            ‖w‖[f; y] * ‖u‖[f; x] := by
    exact le_of_mul_le_mul_left htarget_scaled hτfactor_pos
  exact habs_target

/-- Helper for Theorem 5.2.2: the fixed-`τ` endpoint-witness residual estimate is the remaining
short-segment scalar frontier. -/
theorem pointwiseSegmentResidualEndpointWitnessBoundAtSegmentPoint
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let z := x + τ • (y - x)
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    |inner ℝ w ((H - hessian f z) u)| ≤
      ((2 * τ * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let z : E := x + τ • (y - x)
  let G : E →L[ℝ] E := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let d : E := y - x
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hτfactor_pos : 0 < 1 - τ * a := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
    have hτa_le_a : τ * a ≤ a := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 ha_nonneg
    linarith
  have hsharp :
      |inner ℝ w ((H - hessian f z) u)| ≤
        (((1 - τ * a) / (1 - a)) *
          (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
            ‖w‖[f; y] * ‖u‖[f; x] := by
    -- Reuse the sharp-kernel theorem instead of reopening the same endpoint cancellation.
    simpa [r, a, d, H, G, k, He, w, z] using
      average_hessian_residual_endpoint_witness_integrand_sharp_bound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy hHy (τ := τ) hτ
  have hinner :
      ∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
        (2 * τ * a) / (1 - τ * a) := by
    calc
      ∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹ =
          ∫ s in (0 : ℝ)..τ, 2 * (a * ((1 - s * a) ^ (2 : ℕ))⁻¹) := by
            refine intervalIntegral.integral_congr ?_
            intro s hs
            ring
      _ = 2 * ∫ s in (0 : ℝ)..τ, a * ((1 - s * a) ^ (2 : ℕ))⁻¹ := by
            rw [intervalIntegral.integral_const_mul]
      _ = 2 * ((τ * a) / (1 - τ * a)) := by
            rw [segmentReciprocalSquareIntegral_upto hτ ha_lt_one]
      _ = (2 * τ * a) / (1 - τ * a) := by
            ring
  calc
    |inner ℝ w ((H - hessian f z) u)| ≤
        (((1 - τ * a) / (1 - a)) *
          (∫ s in (0 : ℝ)..τ, (2 * a) * ((1 - s * a) ^ (2 : ℕ))⁻¹)) *
            ‖w‖[f; y] * ‖u‖[f; x] := hsharp
    _ = ((((1 - τ * a) / (1 - a)) * ((2 * τ * a) / (1 - τ * a))) * ‖w‖[f; y]) *
          ‖u‖[f; x] := by
            rw [hinner]
    _ = ((2 * τ * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
          field_simp [hτfactor_pos.ne']

/-- Helper for Theorem 5.2.2: the live endpoint-witness frontier is the pointwise residual
integrand estimate at a fixed segment parameter. -/
theorem average_hessian_residual_endpoint_witness_integrand_bound_atEndpoint
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let z := x + τ • (y - x)
    let G := ∫ σ in (0 : ℝ)..1, hessian f (x + σ • (y - x))
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    |inner ℝ w ((H - hessian f z) u)| ≤
      ((2 * τ * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
  -- The normalized endpoint-metric helper now carries the exact fixed-`τ` statement used later.
  simpa using
    pointwiseSegmentResidualEndpointWitnessBoundAtSegmentPoint
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) hx hy hxy hHy
      (τ := τ) hτ

/-- Helper for Theorem 5.2.2: once the pointwise endpoint-witness residual estimate is available,
integrating it yields the full endpoint witness pairing bound for the averaged residual. -/
theorem average_hessian_residual_endpoint_witness_bound
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) (hHy : (hessian f y).det ≠ 0) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    let k := (H - G) u
    let He := hessian f y
    let w := He.inverse k
    |inner ℝ w k| ≤
      (a / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ w ((H - hessian f (x + τ • (y - x))) u)
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) 1) := by
    let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • (y - x))
    have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • (y - x)) (Set.Icc (0 : ℝ) 1) dom := by
      intro τ hτ
      exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
    have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
      -- Restrict the Hessian field to the affine segment used in the residual integral.
      simpa [Hτ] using
        (hessian_continuousOn (dom := dom) (Mf := (Mf : NNReal)) (f := f) hself).comp
          (show Continuous (fun τ : ℝ ↦ x + τ • (y - x)) by continuity).continuousOn
          hHτ_maps
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E u
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
    have hscalar_cont :
        ContinuousOn (fun τ : ℝ ↦ inner ℝ w (Hτ τ u)) (Set.Icc (0 : ℝ) 1) := by
      simpa [Hτ, ev, φ, InnerProductSpace.toDual_apply_apply] using
        φ.continuous.comp_continuousOn (ev.continuous.comp_continuousOn hHτ_cont)
    -- Pairing against the fixed witness and subtracting the fixed base Hessian keeps continuity.
    have hdiff_cont :
        ContinuousOn (fun τ : ℝ ↦ inner ℝ w (H u) - inner ℝ w (Hτ τ u)) (Set.Icc (0 : ℝ) 1) :=
      continuous_const.continuousOn.sub hscalar_cont
    simpa [θ, Hτ, H, ContinuousLinearMap.sub_apply, inner_sub_right] using hdiff_cont
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 :=
    hθ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hrewrite : inner ℝ w k = ∫ τ in (0 : ℝ)..1, θ τ := by
    -- Rewrite the endpoint witness pairing through the scalar segment integral first.
    simpa [r, a, H, G, k, He, w, θ] using
      average_hessian_residual_endpoint_witness_integral_rewrite
        (dom := dom) (Mf := Mf) (f := f) (hself := inferInstance)
        (x := x) (y := y) (u := u) (w := w) hx hy
  have hsharp_pointwise :
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        |θ τ| ≤ (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x] := by
    intro τ hτ
    have hpoint :
        |inner ℝ w ((H - hessian f (x + τ • (y - x))) u)| ≤
          ((2 * τ * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
      -- Consume the fixed-`τ` endpoint-witness residual estimate in the current spelling.
      simpa [r, a, H, G, k, He, w] using
        pointwiseSegmentResidualEndpointWitnessBoundAtSegmentPoint
          (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) hx hy hxy hHy
          (τ := τ) hτ
    calc
      |θ τ| = |inner ℝ w ((H - hessian f (x + τ • (y - x))) u)| := by
        simp [θ]
      _ ≤ ((2 * τ * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := hpoint
      _ = (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x] := by
        field_simp [hfactor_pos.ne']
  have habs_int : IntervalIntegrable (fun τ : ℝ ↦ |θ τ|) MeasureTheory.volume 0 1 :=
    hθ_int.abs
  have hmajorant_int :
      IntervalIntegrable
        (fun τ : ℝ ↦ (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x])
        MeasureTheory.volume 0 1 := by
    -- The outer majorant is linear in `τ`, so it is interval-integrable on `[0, 1]`.
    exact
      (show Continuous
        (fun τ : ℝ ↦ (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x]) by
          continuity).continuousOn.intervalIntegrable_of_Icc (by norm_num)
  -- Integrate the sharp pointwise endpoint residual estimate and simplify the linear coefficient.
  calc
    |inner ℝ w k| = |∫ τ in (0 : ℝ)..1, θ τ| := by
      rw [hrewrite]
    _ ≤ ∫ τ in (0 : ℝ)..1, |θ τ| := by
      simpa [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm
          (f := θ) (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num))
    _ ≤ ∫ τ in (0 : ℝ)..1, (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x] := by
      exact intervalIntegral.integral_mono_on
        (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun τ : ℝ ↦ |θ τ|)
        (g := fun τ : ℝ ↦ (((2 * a) / (1 - a)) * τ) * ‖w‖[f; y] * ‖u‖[f; x])
        (by norm_num) habs_int hmajorant_int hsharp_pointwise
    _ = ∫ τ in (0 : ℝ)..1,
          ((((2 * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x]) * τ) := by
        refine intervalIntegral.integral_congr ?_
        intro τ hτ
        ring
    _ = (((2 * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x]) *
          ∫ τ in (0 : ℝ)..1, τ := by
        rw [intervalIntegral.integral_const_mul]
    _ = (((2 * a) / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x]) *
          (((1 : ℝ) ^ (2 : ℕ) - (0 : ℝ) ^ (2 : ℕ)) / 2) := by
        rw [integral_id]
    _ = (a / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
      field_simp [hfactor_pos.ne']
      ring

/-- Helper for Theorem 5.2.2: the averaged-Hessian residual is controlled directly in the
endpoint dual local norm by the factor `a / (1 - a)`, where `a = M_f ‖y - x‖_x`. -/
theorem average_hessian_residual_endpointDualBound
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hHy : (hessian f y).det ≠ 0) (hxy : y ∈ W⁰[f; x](1 / (((Mf : NNReal)) : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    HessianDualLocalNorm.ofDetNeZero f y
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy) hHy
      (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let k : E := (H - G) u
  let He : E →L[ℝ] E := hessian f y
  let w : E := He.inverse k
  let hPosY : He.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  let δres : ℝ := HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E k)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hw_realize : ‖w‖[f; y] = δres ∧ inner ℝ k w = δres ^ (2 : ℕ) := by
    -- The endpoint inverse-Hessian witness realizes both the dual norm and its square.
    simpa [He, w, δres] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := (Mf : NNReal)) (f := f) (x := y) hy hHy k
  have hw_norm : ‖w‖[f; y] = δres := hw_realize.1
  have hpair_sq : inner ℝ k w = δres ^ (2 : ℕ) := hw_realize.2
  have hδres_nonneg : 0 ≤ δres := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ (a / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := by
    -- Test the scalar endpoint witness bound against the inverse-Hessian witness at `y`.
    simpa [r, a, H, G, k, He, w, real_inner_comm, mul_assoc, mul_left_comm, mul_comm] using
      average_hessian_residual_endpoint_witness_bound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) hx hy hxy hHy
  change δres ≤ (a / (1 - a)) * ‖u‖[f; x]
  by_cases hzero : δres = 0
  · have hfactor_nonneg : 0 ≤ (a / (1 - a)) * ‖u‖[f; x] := by
      have hden_pos : 0 < 1 - a := by linarith
      exact mul_nonneg (div_nonneg ha_nonneg (le_of_lt hden_pos)) (hessianLocalNorm_nonneg f x u)
    simpa [hzero] using hfactor_nonneg
  · have hδres_pos : 0 < δres := lt_of_le_of_ne hδres_nonneg (by simpa [eq_comm] using hzero)
    have hsq_bound : δres ^ (2 : ℕ) ≤ (a / (1 - a)) * (δres * ‖u‖[f; x]) := by
      calc
        δres ^ (2 : ℕ) = inner ℝ k w := by symm; exact hpair_sq
        _ = |inner ℝ k w| := by rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by rw [real_inner_comm]
        _ ≤ (a / (1 - a)) * ‖w‖[f; y] * ‖u‖[f; x] := hpair_bound
        _ = (a / (1 - a)) * (δres * ‖u‖[f; x]) := by rw [hw_norm]; ring
    -- Cancel the positive endpoint witness norm from the squared dual-norm bound.
    nlinarith

/-- Helper for Theorem 5.2.2: nonnegative scalar combinations are bounded by the corresponding
weighted sum in a fixed endpoint metric. -/
theorem hessianDualLocalNorm_ofDetNeZero_nonneg_smul_add_le
    {x : E} (hPos : (hessian f x).IsPositive) (hH : (hessian f x).det ≠ 0)
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (φ ψ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ + γ • ψ) ≤
      β * HessianDualLocalNorm.ofDetNeZero f x hPos hH φ +
        γ * HessianDualLocalNorm.ofDetNeZero f x hPos hH ψ := by
  -- Separate the two nonnegative scalar factors and use the fixed-point triangle inequality.
  calc
    HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ + γ • ψ) ≤
        HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ) +
          HessianDualLocalNorm.ofDetNeZero f x hPos hH (γ • ψ) := by
      exact hessianDualLocalNorm_ofDetNeZero_add_le hPos hH _ _
    _ = β * HessianDualLocalNorm.ofDetNeZero f x hPos hH φ +
          γ * HessianDualLocalNorm.ofDetNeZero f x hPos hH ψ := by
      rw [hessianDualLocalNorm_ofDetNeZero_smul hPos hH φ β,
        hessianDualLocalNorm_ofDetNeZero_smul hPos hH ψ γ, abs_of_nonneg hβ,
        abs_of_nonneg hγ]

/-- Helper for Theorem 5.2.2: transporting the old gradient from the base point to an admissible
endpoint gives the sharp factor `(1 - a)⁻¹`. -/
theorem oldGradientEndpointDualBound
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {a : ℝ} (ha : a = (Mf : ℝ) * ‖y - x‖[f; x]) :
    HessianDualLocalNorm.ofDetNeZero f y
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy)
      hHy (toDual ℝ E (∇ f x)) ≤
        (1 / (1 - a)) * ndec(f, x, (Mf : NNReal), hx, hH) := by
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  -- Transport the old gradient to the endpoint metric once, then rewrite the base dual norm as
  -- the old Newton decrement.
  calc
    HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f x)) ≤
          (1 / (1 - (Mf : ℝ) * ‖y - x‖[f; x])) *
            HessianDualLocalNorm.ofDetNeZero f x
              ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
              hH (toDual ℝ E (∇ f x)) := by
      simpa [hPosY] using
        dualLocalNorm_transport_to_endpoint
          (Mf := (Mf : NNReal)) (f := f) (x := x) (y := y) (v := ∇ f x) hx hH hxy hHy
    _ = (1 / (1 - a)) * ndec(f, x, (Mf : NNReal), hx, hH) := by
      simpa [ha, NewtonDecrement.ofDetNeZero_def]

/-- Helper for Theorem 5.2.2: once the next point is fixed, the averaged-Hessian residual already
has the sharp endpoint dual-norm bound in that spelling world. -/
theorem averageResidualEndpointDualBound_ofStep
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) (hH : (hessian f x).det ≠ 0)
    (hHy : (hessian f y).det ≠ 0) {a : ℝ}
    (ha : a = (Mf : ℝ) * ‖y - x‖[f; x]) :
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    HessianDualLocalNorm.ofDetNeZero f y
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy) hHy
      (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
  -- Reuse the endpoint residual theorem directly and only rewrite the scalar `a`.
  simpa [hy, ha] using
    average_hessian_residual_endpointDualBound
      (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u) hx hy hH hHy hxy

/-- Helper for Theorem 5.2.2: the inverse-Hessian Newton direction has base local norm equal to
the old Newton decrement. -/
theorem inverseNewtonDirectionLocalNorm_eq_ndec
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let H := hessian f x
    let u := H.inverse (∇ f x)
    ‖u‖[f; x] = ndec(f, x, (Mf : NNReal), hx, hH) := by
  dsimp
  have hu_norm :
      ‖(hessian f x).inverse (∇ f x)‖[f; x] =
        HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
          hH (toDual ℝ E (∇ f x)) := by
    -- Reuse the inverse-Hessian witness instead of rebuilding the local-norm identity inline.
    simpa using
      (endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := (Mf : NNReal)) (f := f) (x := x) hx hH (∇ f x)).1
  simpa [NewtonDecrement.ofDetNeZero_def] using hu_norm

/-- Helper for Theorem 5.2.2: dualizing the next-gradient formula gives the endpoint decomposition
used by both positive variants. -/
theorem positiveVariantDualGradientDecomposition
    (variant : SelfConcordantNewtonVariant) {x : E}
    (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hy :
      let y := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
      y ∈ dom) :
    let y := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
    let H := hessian f x
    let u := H.inverse (∇ f x)
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
    toDual ℝ E (∇ f y) =
      (1 - α) • toDual ℝ E (∇ f x) + α • toDual ℝ E ((H - G) u) := by
  dsimp
  have hy' :
      selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH ∈ dom := by
    simpa using hy
  have hgrad :
      ∇ f (selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH) =
        (1 - selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH) • ∇ f x +
          selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH •
            ((hessian f x -
                ∫ τ in (0 : ℝ)..1,
                  hessian f
                    (x + τ •
                      (selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH - x)))
              ((hessian f x).inverse (∇ f x))) := by
    -- Route correction: normalize the positive-variant gradient update once before the endpoint
    -- dual-norm assembly.
    simpa [selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      nextGradient_eq_oldGradient_plus_averageResidual
        (Mf := (Mf : NNReal)) (f := f) variant hx hH (hxPlus := hy')
  -- Dualize the normalized gradient identity so the endpoint metric sees one fixed spelling.
  simpa [map_add, map_smul] using congrArg (toDual ℝ E) hgrad

/-- Helper for Theorem 5.2.2: the shared positive-variant endpoint assembly combines the
transported old gradient and averaged-residual endpoint bounds into one decrement estimate. -/
theorem positiveVariantEndpointAssemblyBound
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hHy : (hessian f y).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) {α a : ℝ}
    (hα_nonneg : 0 ≤ α) (h1mα_nonneg : 0 ≤ 1 - α)
    (ha : a = (Mf : ℝ) * ‖y - x‖[f; x])
    (hgrad :
      let H := hessian f x
      let u := H.inverse (∇ f x)
      let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
      toDual ℝ E (∇ f y) =
        (1 - α) • toDual ℝ E (∇ f x) + α • toDual ℝ E ((H - G) u)) :
    ndec(f, y, (Mf : NNReal), hy, hHy) ≤
      (((1 - α) / (1 - a)) + α * (a / (1 - a))) *
        ndec(f, x, (Mf : NNReal), hx, hH) := by
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let δ : ℝ := ndec(f, x, (Mf : NNReal), hx, hH)
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  have hu_norm : ‖u‖[f; x] = δ := by
    -- Rewrite the Newton-direction local norm once so the residual bound lands directly in `δ`.
    simpa [H, u, δ] using
      inverseNewtonDirectionLocalNorm_eq_ndec
        (dom := dom) (Mf := Mf) (f := f) (x := x) hx hH
  have htransport :
      HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f x)) ≤
        (1 / (1 - a)) * δ := by
    -- Transport the old gradient to the endpoint metric without reopening the transport chain.
    simpa [hPosY, δ] using
      oldGradientEndpointDualBound
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) hx hy hH hxy hHy ha
  have hresidual_raw :
      HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
    -- Keep the averaged residual in the endpoint metric from the start.
    simpa [hPosY, H, G, u] using
      averageResidualEndpointDualBound_ofStep
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y) (u := u)
        hx hy hxy hH hHy ha
  have hresidual :
      HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * δ := by
    simpa [hu_norm] using hresidual_raw
  have hgrad' :
      toDual ℝ E (∇ f y) =
        (1 - α) • toDual ℝ E (∇ f x) + α • toDual ℝ E ((H - G) u) := by
    simpa [H, u, G] using hgrad
  have hndec :
      ndec(f, y, (Mf : NNReal), hy, hHy) =
        HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f y)) := by
    rw [NewtonDecrement.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
    simp [InnerProductSpace.toDual_apply_apply]
  -- Assemble the shared endpoint decomposition in the fixed metric at `y`.
  calc
    ndec(f, y, (Mf : NNReal), hy, hHy) =
        HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f y)) := hndec
    _ = HessianDualLocalNorm.ofDetNeZero f y hPosY hHy
          (((1 - α) • toDual ℝ E (∇ f x)) + (α • toDual ℝ E ((H - G) u))) := by
          rw [hgrad']
    _ ≤ (1 - α) * HessianDualLocalNorm.ofDetNeZero f y hPosY hHy
          (toDual ℝ E (∇ f x)) +
        α * HessianDualLocalNorm.ofDetNeZero f y hPosY hHy
          (toDual ℝ E ((H - G) u)) := by
          exact hessianDualLocalNorm_ofDetNeZero_nonneg_smul_add_le
            hPosY hHy h1mα_nonneg hα_nonneg _ _
    _ ≤ ((1 - α) / (1 - a)) * δ + α * ((a / (1 - a)) * δ) := by
          have htransport' :
              (1 - α) * HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f x)) ≤
                ((1 - α) / (1 - a)) * δ := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              (mul_le_mul_of_nonneg_left htransport h1mα_nonneg)
          have hresidual' :
              α * HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E ((H - G) u)) ≤
                α * ((a / (1 - a)) * δ) := by
            exact mul_le_mul_of_nonneg_left hresidual hα_nonneg
          exact add_le_add htransport' hresidual'
    _ = (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := by
          ring

/-- Helper for Theorem 5.2.2: the damped-step convex-combination coefficient simplifies to the
textbook scalar factor. -/
theorem dampedStepCoefficientIdentity
    {α a s : ℝ} (hs_nonneg : 0 ≤ s) (hα : α = 1 / (1 + s)) (ha : a = s / (1 + s)) :
    ((1 - α) / (1 - a) + α * (a / (1 - a))) = s * (1 + 1 / (1 + s)) := by
  have hden_pos : 0 < 1 + s := by
    linarith
  -- Normalize every scalar term over the shared denominator `1 + s`.
  rw [hα, ha]
  field_simp [hden_pos.ne']
  ring

/-- Helper for Theorem 5.2.2: the intermediate-step convex-combination coefficient simplifies to
the explicit textbook scalar factor. -/
theorem intermediateStepCoefficientIdentity
    {α a s : ℝ} (hs_nonneg : 0 ≤ s)
    (hα : α = (1 + s) / (1 + s + s ^ (2 : ℕ)))
    (ha : a = s * (1 + s) / (1 + s + s ^ (2 : ℕ))) :
    ((1 - α) / (1 - a) + α * (a / (1 - a))) =
      s * (1 + s + s / (1 + s + s ^ (2 : ℕ))) := by
  have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by
    positivity
  -- Normalize the intermediate coefficient over the common denominator `1 + s + s²`.
  rw [hα, ha]
  field_simp [hden_pos.ne']
  ring
/-- Helper for Theorem 5.2.2: the intermediate Newton step size has the simplified textbook
rational form. -/
theorem intermediate_stepSize_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    selfConcordantNewtonStepSize f (Mf : NNReal) .intermediate x hx hH =
      (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) f hx hH
  have hshift_den_pos : 0 < 1 + (Mf : ℝ) * δ := by
    positivity
  -- Expand the intermediate shift and simplify the resulting rational expression.
  rw [selfConcordantNewtonStepSize]
  simp [selfConcordantNewtonShift, δ]
  field_simp [hshift_den_pos.ne']

/-- Helper for Theorem 5.2.2: the intermediate-step local norm is always strictly smaller than
the admissible Dikin radius `1 / M_f` once `M_f > 0`. -/
theorem intermediate_step_localNorm_lt_inv
    {δ : ℝ} (hδ_nonneg : 0 ≤ δ) :
    δ * (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
      1 / (Mf : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hden_pos :
      0 <
        1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
    positivity
  refine (lt_div_iff₀ hMf_pos).2 ?_
  have hnum_lt :
      ((Mf : ℝ) * δ) * (1 + (Mf : ℝ) * δ) <
        1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
    nlinarith
  have hscaled_lt :
      (((Mf : ℝ) * δ) * (1 + (Mf : ℝ) * δ)) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
        1 := by
    refine (div_lt_iff₀ hden_pos).2 ?_
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled_lt

end PositiveVariants

end
