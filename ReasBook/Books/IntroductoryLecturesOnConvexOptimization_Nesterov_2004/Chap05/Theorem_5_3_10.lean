/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Topology
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 5.3.10: a strict convex combination of an interior point of `dom` and a
closure point of `dom` stays in `dom`. -/
theorem strict_chord_mem_dom_of_mem_closure
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (x : dom) (y : closure dom) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (1 - α) • (x : E) + α • (y : E) ∈ dom := by
  let hstd : IsStandardSelfConcordantOn dom F := hF.toIsStandardSelfConcordantOn
  have hx_int : (x : E) ∈ interior dom := by
    rw [hstd.isOpen_domain.interior_eq]
    exact x.2
  -- The open segment from an interior point to a closure point lies in the interior.
  have hz_int :
      (1 - α) • (x : E) + α • (y : E) ∈ interior dom := by
    exact hstd.convex_domain.combo_interior_closure_mem_interior
      hx_int y.2 (sub_pos.mpr hα.2) hα.1 (by ring)
  simpa [hstd.isOpen_domain.interior_eq] using hz_int

/-- Helper for Theorem 5.3.10: the logarithmic segment upper bound extends from interior endpoints
to a closure endpoint by sequential approximation. -/
theorem segment_upper_bound_log_one_sub_of_mem_closure
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (x : dom) (y : closure dom) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    F ((1 - α) • (x : E) + α • (y : E)) ≤ F (x : E) - (ν : ℝ) * Real.log (1 - α) := by
  let hstd : IsStandardSelfConcordantOn dom F := hF.toIsStandardSelfConcordantOn
  rcases mem_closure_iff_seq_limit.mp y.2 with ⟨ySeq, hySeq_mem, hySeq_tendsto⟩
  let z : E := (1 - α) • (x : E) + α • (y : E)
  let zSeq : ℕ → E := fun n ↦ (1 - α) • (x : E) + α • ySeq n
  have hz_mem : z ∈ dom := strict_chord_mem_dom_of_mem_closure hF x y hα
  have hzSeq_tendsto : Tendsto zSeq atTop (nhds z) := by
    -- The affine chord map is continuous in the closure endpoint.
    have hcontAffine : Continuous fun u : E ↦ (1 - α) • (x : E) + α • u := by
      exact continuous_const.add (continuous_const.smul continuous_id)
    simpa only [z, zSeq] using hcontAffine.continuousAt.tendsto.comp hySeq_tendsto
  have hF_tendsto :
      Tendsto (fun n ↦ F (zSeq n)) atTop (nhds (F z)) := by
    -- Continuity of `F` at the strict chord point lets the pointwise bounds pass to the limit.
    have hcontF : ContinuousAt F z := by
      exact (hstd.contDiffOn.continuousOn.continuousAt (hstd.isOpen_domain.mem_nhds hz_mem))
    simpa only [zSeq, z] using hcontF.tendsto.comp hzSeq_tendsto
  have hzSeq_mem_bound :
      ∀ n, F (zSeq n) ∈ Set.Iic (F (x : E) - (ν : ℝ) * Real.log (1 - α)) := by
    intro n
    have hbound_n :
        F ((x : E) + α • (ySeq n - (x : E))) ≤ F (x : E) - (ν : ℝ) * Real.log (1 - α) :=
      hF.segment_upper_bound_log_one_sub x.2 (hySeq_mem n) hα
    have hzSeq_eq :
        zSeq n = (x : E) + α • (ySeq n - (x : E)) := by
      calc
        zSeq n = ((x : E) - α • (x : E)) + α • ySeq n := by
          dsimp [zSeq]
          rw [sub_smul, one_smul]
        _ = (x : E) + α • ySeq n - α • (x : E) := by
          abel
        _ = (x : E) + α • (ySeq n - (x : E)) := by
          rw [smul_sub]
          abel
    exact hzSeq_eq ▸ hbound_n
  -- Closedness of the upper half-line transfers the segment bound to the closure endpoint.
  exact isClosed_Iic.mem_of_tendsto hF_tendsto (Filter.Eventually.of_forall hzSeq_mem_bound)

/-- Helper for Theorem 5.3.10: an exact minimizer of the penalty objective is stationary. -/
theorem centralPathPenaltyObjective_gradient_eq_zero_at_minimizer
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {xPath : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    (t : ℝ) • c + ∇ F (xPath : E) = 0 := by
  let hstd : IsStandardSelfConcordantOn dom F := inferInstance
  have hdiff : DifferentiableAt ℝ F (xPath : E) := by
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds xPath.2)).differentiableAt
        (by norm_num)
  have hlocal : IsLocalMin (centralPathPenaltyObjective c F t) (xPath : E) :=
    hpath.isLocalMin (hstd.isOpen_domain.mem_nhds xPath.2)
  have hgrad :
      ∇ (centralPathPenaltyObjective c F t) (xPath : E) =
        (t : ℝ) • c + ∇ F (xPath : E) :=
    (hasGradientAt_centralPathPenaltyObjective c F (t : ℝ) hdiff).gradient
  have hzero : ∇ (centralPathPenaltyObjective c F t) (xPath : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  rw [hgrad] at hzero
  exact hzero

/-- Helper for Theorem 5.3.10: the tilted central-path penalty objective is standard
self-concordant on `dom`. -/
theorem centralPathPenaltyObjective_isStandardSelfConcordantOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) :
    IsStandardSelfConcordantOn dom (centralPathPenaltyObjective c F (t : ℝ)) := by
  have hrewrite :
      centralPathPenaltyObjective c F (t : ℝ) = fun z ↦ inner ℝ ((t : ℝ) • c) z + F z := by
    -- Normalize the penalty objective to the linear-tilt shape used by the chapter API.
    funext z
    simp [centralPathPenaltyObjective_apply, inner_smul_left, mul_comm]
  -- Rewrite the tilt as the linear perturbation by the vector `(t : ℝ) • c`.
  rw [hrewrite]
  simpa using
    selfConcordantBarrier_add_linear_isStandardSelfConcordantOn
      dom F ((t : ℝ) • c) (inferInstance : IsStandardSelfConcordantOn dom F)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.3.10: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.3.10: the barrier gradient is continuous on the domain. -/
private theorem barrier_gradient_continuousOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F] :
    ContinuousOn (∇ F) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd_cont : ContinuousOn (fderiv ℝ F) dom := by
    exact
      ((inferInstance : IsStandardSelfConcordantOn dom F).contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          (inferInstance : IsStandardSelfConcordantOn dom F).isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num) |>.continuousOn
  simpa [gradient, D] using D.continuous.comp_continuousOn hfd_cont

/-- Helper for Theorem 5.3.10: the barrier Hessian is continuous on the domain. -/
private theorem barrier_hessian_continuousOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F] :
    ContinuousOn (hessian F) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ F) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) dom :=
      ((inferInstance : IsStandardSelfConcordantOn dom F).contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          (inferInstance : IsStandardSelfConcordantOn dom F).isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      (inferInstance : IsStandardSelfConcordantOn dom F).isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5.3.10: a quadratic family bounded above by `c` forces the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Route correction: reuse the stable discriminant argument already used for the sibling
  -- determinant-side Cauchy inequalities.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have htest := hline ((|c| + 1) / a)
      have hcontr : 2 * (|c| + 1) ≤ c := by
        have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
          simpa [hb_zero] using htest
        field_simp [ha_zero] at hrew
        linarith
      nlinarith [hcontr, le_abs_self c, abs_nonneg c]
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Theorem 5.3.10: at a point with invertible Hessian, the Euclidean pairing is
bounded by the Hessian dual local norm times the Hessian local norm. -/
theorem abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
    {F : E → ℝ} {x v z : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v) *
        ‖z‖[F; x] := by
  let H := hessian F x
  let w := H.inverse v
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
      (HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v)) ^
          (2 : ℕ) =
        inner ℝ v w := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[F; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v) *
          ‖z‖[F; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v)) ^
              (2 : ℕ) *
            ‖z‖[F; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v) *
            ‖z‖[F; x]) ^ (2 : ℕ) := by
          ring
  have hdual_nonneg :
      0 ≤ HessianDualLocalNorm.ofDetNeZero F x hPos hH ((InnerProductSpace.toDual ℝ E) v) := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg F x z))

/-- Helper for Theorem 5.3.10: the residual covector at an approximate center pairs with the
chord to the exact minimizer by at most `β` times the local distance. -/
theorem centralPathPenalty_residual_pairing_le_beta_mul_distance
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ}
    {xPath x : dom}
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) ≤
      β * ‖(x : E) - (xPath : E)‖[F; (x : E)] := by
  -- First control the residual pairing by the fixed dual/local Cauchy inequality at `x`.
  have habs :
      |inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E))| ≤
        HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
          ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) *
            ‖(x : E) - (xPath : E)‖[F; (x : E)] :=
    abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
      (F := F)
      (x := (x : E))
      (v := (t : ℝ) • c + ∇ F (x : E))
      (z := (x : E) - (xPath : E))
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2)
      hxH
  calc
    inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) ≤
        |inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E))| := by
          exact le_abs_self _
    _ ≤ HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
          ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) *
            ‖(x : E) - (xPath : E)‖[F; (x : E)] := habs
    _ ≤ β * ‖(x : E) - (xPath : E)‖[F; (x : E)] := by
          exact mul_le_mul_of_nonneg_right happrox
            (hessianLocalNorm_nonneg F (x : E) ((x : E) - (xPath : E)))

/-- Helper for Theorem 5.3.10: along a chord in the barrier domain, the scalarized gradient line
has derivative given by the corresponding Hessian pairing. -/
private theorem barrier_scalarized_gradient_line_hasDerivAt
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (x + s • d)) u)
      (inner ℝ (hessian F (x + t • d) d) u) t := by
  -- Differentiate the gradient line restriction and then evaluate on the fixed direction `u`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (x + t • d) :=
      (inferInstance : IsStandardSelfConcordantOn dom F).contDiffOn.contDiffAt
        ((inferInstance : IsStandardSelfConcordantOn dom F).isOpen_domain.mem_nhds hxt)
        |>.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (x + t • d) := by
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (x + s • d))
        ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (x + s • d)))
        (φ.comp ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.3.10: nonnegative scalar dilations scale the barrier local norm by the
same scalar. -/
private theorem barrier_hessianLocalNorm_smul_nonneg_at_mem
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {z d : E} (hz : z ∈ dom) {t : ℝ} (ht : 0 ≤ t) :
    ‖t • d‖[F; z] = t * ‖d‖[F; z] := by
  -- Expand the local norm and simplify the square root of `t²`.
  have hquad : 0 ≤ inner ℝ d (hessian F z d) :=
    (inferInstance : IsStandardSelfConcordantOn dom F).hessian_posSemidef hz d
  calc
    ‖t • d‖[F; z] = Real.sqrt ((t * t) * inner ℝ d (hessian F z d)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ d (hessian F z d)) * Real.sqrt (t * t) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = t * ‖d‖[F; z] := by
      rw [show t * t = t ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.3.10: every point on the chord between two barrier-domain points stays
in the domain. -/
private theorem barrier_segment_point_mem
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the segment point as a convex combination and use convexity of the barrier domain.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have hconv := (inferInstance : IsStandardSelfConcordantOn dom F).convex_domain
  have h1t : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5.3.10: squaring the barrier local norm recovers the Hessian quadratic
form whenever that quadratic form is nonnegative. -/
private theorem sq_barrier_hessianLocalNorm_eq_inner_hessian
    {F : E → ℝ} {z d : E} (hquad : 0 ≤ inner ℝ d (hessian F z d)) :
    ‖d‖[F; z] ^ (2 : ℕ) = inner ℝ d (hessian F z d) := by
  -- The local norm is the square root of the Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.3.10: the rational lower integrand integrates to the expected transport
factor. -/
private theorem integral_sq_div_eq_scaled_sq_div
    {r α : ℝ} (hα0 : 0 ≤ α) (hr0 : 0 ≤ r) :
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) =
      α * r ^ (2 : ℕ) / (1 + α * r) := by
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) α, 0 < 1 + t * r := by
    intro t ht
    nlinarith [ht.1, hr0]
  have hnum : ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * r))
      (Set.Icc (0 : ℝ) α) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * r) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * r) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * r))
          (r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) α := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * r ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * r) r t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const r) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hquot_slope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * r) - t * r ^ (2 : ℕ) * r) /
            (1 + t * r) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt (fun s : ℝ ↦ (s * r ^ (2 : ℕ)) / (1 + s * r))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * r) - t * r ^ (2 : ℕ) * r) /
            (1 + t * r) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hquot_slope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hnum hderiv hint
  calc
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ)
        = α * r ^ (2 : ℕ) / (1 + α * r) - (0 * r ^ (2 : ℕ) / (1 + 0 * r)) := by
            simpa using hftc
    _ = α * r ^ (2 : ℕ) / (1 + α * r) := by ring

/-- Helper for Theorem 5.3.10: for a barrier, the gradient increment along any chord dominates
the textbook transport factor built from the base-point local norm. -/
private theorem barrier_gradient_increment_inner_ge_scaled_localNorm_sq_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[F; x]
    inner ℝ (∇ F (x + α • d) - ∇ F x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * r) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[F; x]
  have hr0 : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg F x d
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ F (x + t • d)) d
  -- Route correction: integrate the scalar gradient line directly and feed the source transport
  -- estimate pointwise along the segment.
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) α) := by
    intro t ht
    have hz : x + t • d ∈ dom := barrier_segment_point_mem
      (dom := dom) (ν := ν) (F := F) hx hy ht.1 (le_trans ht.2 hα1)
    have hderiv_t : HasDerivAt g (inner ℝ d (hessian F (x + t • d) d)) t := by
      simpa [g, real_inner_comm] using
        barrier_scalarized_gradient_line_hasDerivAt
          (dom := dom) (ν := ν) (F := F) (x := x) (d := d) (u := d) hz
    exact hderiv_t.continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt g (inner ℝ d (hessian F (x + t • d) d)) t := by
    intro t ht
    have hz : x + t • d ∈ dom := barrier_segment_point_mem
      (dom := dom) (ν := ν) (F := F) hx hy (le_of_lt ht.1)
      (le_trans (le_of_lt ht.2) hα1)
    simpa [g, real_inner_comm] using
      barrier_scalarized_gradient_line_hasDerivAt
        (dom := dom) (ν := ν) (F := F) (x := x) (d := d) (u := d) hz
  have hderiv_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d (hessian F (x + t • d) d))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ inner ℝ d (hessian F (x + t • d) d))
          (Set.Icc (0 : ℝ) α) := by
      intro t ht
      have hz : x + t • d ∈ dom := barrier_segment_point_mem
        (dom := dom) (ν := ν) (F := F) hx hy ht.1
        (le_trans ht.2 hα1)
      have hsmul_cont : ContinuousAt (fun s : ℝ ↦ s • d) t := by
        simpa [one_smul] using ((hasDerivAt_id t).smul_const d).continuousAt
      have hhess_cont : ContinuousAt (hessian F) (x + t • d) :=
        (barrier_hessian_continuousOn (dom := dom) (ν := ν) (F := F)).continuousAt
          ((inferInstance : IsStandardSelfConcordantOn dom F).isOpen_domain.mem_nhds hz)
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian F (x + s • d)) t := by
        refine ContinuousAt.comp hhess_cont ?_
        exact ContinuousAt.comp (continuousAt_const.add continuousAt_id) hsmul_cont
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian F (x + s • d) d) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E d).continuous.continuousAt) hhess_line
      have hinner_cont :
          ContinuousAt (fun s : ℝ ↦ inner ℝ d (hessian F (x + s • d) d)) t := by
        simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φ.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hα0
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * r) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        have : 0 < 1 + t * r := by nlinarith [ht.1, hr0]
        exact pow_ne_zero 2 this.ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) α,
        r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) ≤
          inner ℝ d (hessian F (x + t • d) d) := by
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hα1
    have hz : x + t • d ∈ dom := barrier_segment_point_mem
      (dom := dom) (ν := ν) (F := F) hx hy ht.1 ht1
    have hquadz : 0 ≤ inner ℝ d (hessian F (x + t • d) d) :=
      (inferInstance : IsStandardSelfConcordantOn dom F).hessian_posSemidef hz d
    have hsub : (x + t • d) - x = t • d := by
      abel
    have hdisp :
        ‖(x + t • d) - x‖[F; x + t • d] ≥
          ‖(x + t • d) - x‖[F; x] / (1 + ‖(x + t • d) - x‖[F; x]) := by
      simpa [one_mul] using
        (inferInstance : IsStandardSelfConcordantOn dom F).displacement_localNorm_lower_bound hx hz
    rw [hsub,
      barrier_hessianLocalNorm_smul_nonneg_at_mem (dom := dom) (ν := ν) (F := F) hz ht.1,
      barrier_hessianLocalNorm_smul_nonneg_at_mem (dom := dom) (ν := ν) (F := F) hx ht.1] at hdisp
    have hden_pos : 0 < 1 + t * r := by
      nlinarith [ht.1, hr0]
    have hdir : r / (1 + t * r) ≤ ‖d‖[F; x + t • d] := by
      by_cases ht_zero : t = 0
      · subst ht_zero
        simp [r]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
        have hdisp' : t * (r / (1 + t * r)) ≤ t * ‖d‖[F; x + t • d] := by
          simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdisp
        exact le_of_mul_le_mul_left hdisp' ht_pos
    have hsq_norm :
        (r / (1 + t * r)) ^ (2 : ℕ) ≤ ‖d‖[F; x + t • d] ^ (2 : ℕ) := by
      have hdir_nonneg : 0 ≤ r / (1 + t * r) := by positivity
      have hnorm_nonneg : 0 ≤ ‖d‖[F; x + t • d] :=
        hessianLocalNorm_nonneg F (x + t • d) d
      nlinarith [hdir, hdir_nonneg, hnorm_nonneg]
    have hfrac :
        (r / (1 + t * r)) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
      field_simp [hden_pos.ne']
    calc
      r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) = (r / (1 + t * r)) ^ (2 : ℕ) := by
        exact hfrac.symm
      _ ≤ ‖d‖[F; x + t • d] ^ (2 : ℕ) := hsq_norm
      _ = inner ℝ d (hessian F (x + t • d) d) :=
          sq_barrier_hessianLocalNorm_eq_inner_hessian hquadz
  have hmono :
      ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) ≤
        ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) := by
    exact intervalIntegral.integral_mono_on hα0 hint_lower hderiv_int hpoint
  have hftc :
      ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) = g α - g 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hg_cont hderiv hderiv_int
  have hcalc :
      α * r ^ (2 : ℕ) / (1 + α * r) ≤ g α - g 0 := by
    calc
      α * r ^ (2 : ℕ) / (1 + α * r)
          = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
              symm
              exact integral_sq_div_eq_scaled_sq_div hα0 hr0
      _ ≤ ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) := hmono
      _ = g α - g 0 := hftc
  simpa [g, d, r, inner_sub_left] using hcalc

/-- Helper for Theorem 5.3.10: the missing source-faithful lower pairing toward the exact
minimizer of the tilted objective. -/
theorem centralPathPenalty_gradient_pairing_lower_to_minimizer
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    ‖(x : E) - (xPath : E)‖[F; (x : E)] ^ (2 : ℕ) /
        (1 + ‖(x : E) - (xPath : E)‖[F; (x : E)]) ≤
      inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) := by
  let d : E := (x : E) - (xPath : E)
  let r : ℝ := ‖d‖[F; (x : E)]
  have hstationary :
      (t : ℝ) • c + ∇ F (xPath : E) = 0 :=
    centralPathPenaltyObjective_gradient_eq_zero_at_minimizer
      (dom := dom) (ν := ν) (F := F) c t hpath
  have hresidual :
      (t : ℝ) • c + ∇ F (x : E) = -(∇ F (xPath : E) - ∇ F (x : E)) := by
    have htc : (t : ℝ) • c = -∇ F (xPath : E) := by
      calc
        (t : ℝ) • c = (t : ℝ) • c + ∇ F (xPath : E) - ∇ F (xPath : E) := by abel
        _ = -∇ F (xPath : E) := by rw [hstationary]; abel
    calc
      (t : ℝ) • c + ∇ F (x : E) = -∇ F (xPath : E) + ∇ F (x : E) := by rw [htc]
      _ = -(∇ F (xPath : E) - ∇ F (x : E)) := by abel
  have hinc :
      r ^ (2 : ℕ) / (1 + r) ≤
        inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) (-d) := by
    -- Route correction: use the restored segment-calculus lower bound with `α = 1`.
    have hraw :
        ‖(xPath : E) - (x : E)‖[F; (x : E)] ^ (2 : ℕ) /
            (1 + ‖(xPath : E) - (x : E)‖[F; (x : E)]) ≤
          inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) ((xPath : E) - (x : E)) := by
      simpa [one_smul] using
        barrier_gradient_increment_inner_ge_scaled_localNorm_sq_div
          (dom := dom) (ν := ν) (F := F) x.2 xPath.2 (show (0 : ℝ) ≤ 1 by norm_num)
          (show (1 : ℝ) ≤ 1 by norm_num)
    have hr_eq : ‖(xPath : E) - (x : E)‖[F; (x : E)] = r := by
      have hd_eq : (xPath : E) - (x : E) = -d := by
        simp [d]
      rw [hd_eq, hessianLocalNorm_neg]
    have hd_eq : (xPath : E) - (x : E) = -d := by
      simp [d]
    calc
      r ^ (2 : ℕ) / (1 + r)
          = ‖(xPath : E) - (x : E)‖[F; (x : E)] ^ (2 : ℕ) /
              (1 + ‖(xPath : E) - (x : E)‖[F; (x : E)]) := by
                rw [hr_eq]
      _ ≤ inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) ((xPath : E) - (x : E)) := hraw
      _ = inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) (-d) := by rw [hd_eq]
  have hpair :
      inner ℝ ((t : ℝ) • c + ∇ F (x : E)) d =
        inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) (-d) := by
    rw [hresidual, inner_neg_left, inner_neg_right]
  calc
    ‖(x : E) - (xPath : E)‖[F; (x : E)] ^ (2 : ℕ) /
        (1 + ‖(x : E) - (xPath : E)‖[F; (x : E)]) = r ^ (2 : ℕ) / (1 + r) := by
          rfl
    _ ≤ inner ℝ (∇ F (xPath : E) - ∇ F (x : E)) (-d) := hinc
    _ = inner ℝ ((t : ℝ) • c + ∇ F (x : E)) d := hpair.symm
    _ = inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) := by
          rfl

/-- Helper for Theorem 5.3.10: once the minimizer pairing lower bound and the residual pairing
upper bound are available, the local distance to the exact minimizer is at most `β / (1 - β)`.
-/
theorem centralPathPenalty_localNorm_distance_le_beta_div_one_sub
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (hβ : β < 1)
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    ‖(x : E) - (xPath : E)‖[F; (x : E)] ≤ β / (1 - β) := by
  let r : ℝ := ‖(x : E) - (xPath : E)‖[F; (x : E)]
  have hr0 : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg F (x : E) ((x : E) - (xPath : E))
  have hβ_nonneg : 0 ≤ β := by
    have hresidual_nonneg :
        0 ≤ HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
          ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) := by
      rw [HessianDualLocalNorm.ofDetNeZero_def]
      exact Real.sqrt_nonneg _
    exact le_trans hresidual_nonneg happrox
  have hlower :
      r ^ (2 : ℕ) / (1 + r) ≤
        inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) := by
    simpa [r] using
      centralPathPenalty_gradient_pairing_lower_to_minimizer
        (dom := dom) (ν := ν) (F := F) c t (xPath := xPath) (x := x) hpath
  have hupper :
      inner ℝ ((t : ℝ) • c + ∇ F (x : E)) ((x : E) - (xPath : E)) ≤ β * r := by
    simpa [r] using
      centralPathPenalty_residual_pairing_le_beta_mul_distance
        (dom := dom) (ν := ν) (F := F) c t (β := β) (xPath := xPath) (x := x) hxH happrox
  have hmain : r ^ (2 : ℕ) / (1 + r) ≤ β * r := le_trans hlower hupper
  have hgoal : r ≤ β / (1 - β) := by
    by_cases hr_zero : r = 0
    · have : 0 ≤ β / (1 - β) := by
        exact div_nonneg hβ_nonneg (sub_pos.mpr hβ).le
      simpa [r, hr_zero] using this
    · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
      have hden_pos : 0 < 1 + r := by positivity
      have hcross : (1 - β) * r ≤ β := by
        have hmain' : r ^ (2 : ℕ) ≤ β * r * (1 + r) := by
          exact (div_le_iff₀ hden_pos).1 hmain
        nlinarith
      exact (le_div_iff₀ (sub_pos.mpr hβ)).2 (by simpa [mul_comm] using hcross)
  simpa [r] using hgoal

/-- Helper for Theorem 5.3.10: the approximate-centering condition for the tilted objective
controls the objective correction from `x` to the exact minimizer `xPath`. -/
theorem centralPathPenalty_objectiveCorrection_le_error_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (ht : 0 < (t : ℝ)) (hβ : β < 1)
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ c (x : E) - inner ℝ c (xPath : E) ≤
      ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) := by
  have hβ_nonneg : 0 ≤ β := by
    have hresidual_nonneg :
        0 ≤ HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
          ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) := by
      rw [HessianDualLocalNorm.ofDetNeZero_def]
      exact Real.sqrt_nonneg _
    exact le_trans hresidual_nonneg happrox
  have hdual :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) c) ≤
      (β + Real.sqrt (ν : ℝ)) / (t : ℝ) :=
    dualLocalNorm_objectiveVector_le_add_sqrt_barrierParameter_div
      (dom := dom) (ν := ν) (F := F) c ht hxH happrox
  have hdist :
      ‖(x : E) - (xPath : E)‖[F; (x : E)] ≤ β / (1 - β) :=
    centralPathPenalty_localNorm_distance_le_beta_div_one_sub
      (dom := dom) (ν := ν) (F := F) c t hβ hpath hxH happrox
  have hr0 :
      0 ≤ ‖(x : E) - (xPath : E)‖[F; (x : E)] :=
    hessianLocalNorm_nonneg F (x : E) ((x : E) - (xPath : E))
  have hcoeff_nonneg : 0 ≤ (β + Real.sqrt (ν : ℝ)) / (t : ℝ) := by
    positivity
  -- Bound the objective correction by dual-local Cauchy and then substitute the distance estimate.
  calc
    inner ℝ c (x : E) - inner ℝ c (xPath : E) = inner ℝ c ((x : E) - (xPath : E)) := by
      rw [inner_sub_right]
    _ ≤ |inner ℝ c ((x : E) - (xPath : E))| := by
          exact le_abs_self _
    _ ≤ HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
          ((InnerProductSpace.toDual ℝ E) c) *
            ‖(x : E) - (xPath : E)‖[F; (x : E)] :=
          abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
            (F := F)
            (x := (x : E))
            (v := c)
            (z := (x : E) - (xPath : E))
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2)
            hxH
    _ ≤ ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * ‖(x : E) - (xPath : E)‖[F; (x : E)] := by
          exact mul_le_mul_of_nonneg_right hdual hr0
    _ ≤ ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) := by
          exact mul_le_mul_of_nonneg_left hdist hcoeff_nonneg

-- Proof sketch: let `x*(t)` be the exact minimizer of the penalty objective. Apply the
-- first-order optimality condition for `x*(t)` and compare it with an optimal solution `xOpt`
-- of the original linear problem on `closure dom`. The barrier inequality against the chord from
-- `x*(t)` to `xOpt`, together with `closure dom` as the closed feasible set, yields the estimate
-- `⟪c, x*(t)⟫ - ⟪c, xOpt⟫ ≤ ν / t`.
/-- For an exact central-path point at parameter `t > 0`, the objective gap to any optimal point
of the original linear problem on `closure dom` is at most `ν / t`. -/
theorem centralPathPoint_objectiveGap_le_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) := by
  have : inner ℝ c (xOpt : E) ≤ inner ℝ c (xOpt : E) := hopt xOpt
  let gap : ℝ := inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)
  let scaledGap : ℝ := (t : ℝ) * gap
  have hchord :
      ∀ α, α ∈ Set.Ico (0 : ℝ) 1 →
        α * scaledGap ≤ -(ν : ℝ) * Real.log (1 - α) := by
    intro α hα
    let z : E := (1 - α) • (xPath : E) + α • (xOpt : E)
    have hz_mem : z ∈ dom := strict_chord_mem_dom_of_mem_closure
      (hF := (inferInstance : IsSelfConcordantBarrierOnWith dom ν F)) xPath xOpt hα
    have hupper :
        F z ≤ F (xPath : E) - (ν : ℝ) * Real.log (1 - α) :=
      segment_upper_bound_log_one_sub_of_mem_closure
        (hF := (inferInstance : IsSelfConcordantBarrierOnWith dom ν F)) xPath xOpt hα
    have hmin :
        centralPathPenaltyObjective c F t (xPath : E) ≤ centralPathPenaltyObjective c F t z :=
      hpath hz_mem
    have hpair :
        inner ℝ c (xPath : E) - inner ℝ c z = α * gap := by
      dsimp [z, gap]
      calc
        inner ℝ c (xPath : E) - inner ℝ c ((1 - α) • (xPath : E) + α • (xOpt : E))
            = inner ℝ c (xPath : E) -
                ((1 - α) * inner ℝ c (xPath : E) + α * inner ℝ c (xOpt : E)) := by
                  rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = α * (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := by ring
        _ = α * gap := by rfl
    have hpen :
        (t : ℝ) * (inner ℝ c (xPath : E) - inner ℝ c z) ≤ F z - F (xPath : E) := by
      rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply] at hmin
      linarith
    have hchord' :
        α * scaledGap ≤ -(ν : ℝ) * Real.log (1 - α) := by
      have hpen' :
          (t : ℝ) * (α * gap) ≤ F z - F (xPath : E) := by
        rw [hpair] at hpen
        simpa [scaledGap, mul_assoc, mul_left_comm, mul_comm] using hpen
      linarith
    exact hchord'
  have hscaled : scaledGap ≤ (ν : ℝ) := by
    by_cases hν : ν = 0
    · have hhalf :
          (1 / 2 : ℝ) * scaledGap ≤ -(ν : ℝ) * Real.log (1 - (1 / 2 : ℝ)) := by
        exact hchord (1 / 2 : ℝ) (by constructor <;> norm_num)
      rw [hν] at hhalf
      norm_num at hhalf
      linarith
    · have hν_pos : 0 < (ν : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hν)
      by_contra hgap_gt
      have hε_pos : 0 < scaledGap / (ν : ℝ) - 1 := by
        have hgap_gt' : (ν : ℝ) < scaledGap := by
          exact not_le.mp hgap_gt
        have hdiv_lt : 1 < scaledGap / (ν : ℝ) := by
          exact (one_lt_div hν_pos).2 hgap_gt'
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_pos
      have hα_mem : (1 / ((n : ℝ) + 2)) ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · positivity
        · have htwo_pos : 0 < (n : ℝ) + 2 := by positivity
          exact (div_lt_one htwo_pos).2 (by linarith)
      have hstep :
          (1 / ((n : ℝ) + 2)) * scaledGap ≤
            -(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2)) := by
        exact hchord (1 / ((n : ℝ) + 2)) hα_mem
      have hlog_bound :
          -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) ≤
            1 + 1 / ((n : ℝ) + 1) := by
        have hratio_pos : 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
        have hratio_bound :
            Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
          have hlog := Real.log_le_sub_one_of_pos hratio_pos
          have hden1_pos : 0 < (n : ℝ) + 1 := by positivity
          have hsplit :
              ((n : ℝ) + 2) / ((n : ℝ) + 1) = 1 + 1 / ((n : ℝ) + 1) := by
            field_simp [hden1_pos.ne']
            ring
          have hrewrite :
              ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
            rw [hsplit]
            ring
          simpa [hrewrite] using hlog
        have hden1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have hden2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have hratio_eq :
            -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) =
              ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
          have hbase_pos : 0 < 1 - 1 / ((n : ℝ) + 2) := by
            have htwo_pos : 0 < (n : ℝ) + 2 := by positivity
            have hrecip_lt : 1 / ((n : ℝ) + 2) < 1 := by
              exact (div_lt_one htwo_pos).2 (by linarith)
            linarith
          have hbase_eq :
              (1 - 1 / ((n : ℝ) + 2) : ℝ) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
            field_simp [hden2]
            ring
          have hinv_eq :
              ((1 - 1 / ((n : ℝ) + 2)) : ℝ)⁻¹ = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
            rw [hbase_eq]
            field_simp [hden1, hden2]
          have hlog_inv :
              -Real.log (1 - 1 / ((n : ℝ) + 2)) =
                Real.log (((1 - 1 / ((n : ℝ) + 2)) : ℝ)⁻¹) := by
            exact (Real.log_inv (1 - 1 / ((n : ℝ) + 2))).symm
          calc
            -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))
                = -(((n : ℝ) + 2) * Real.log (1 - 1 / ((n : ℝ) + 2))) := by
                    field_simp [hden2]
            _ = ((n : ℝ) + 2) * (-Real.log (1 - 1 / ((n : ℝ) + 2))) := by
                  ring
            _ = ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
                  rw [hlog_inv, hinv_eq]
        calc
          -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))
              = ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := hratio_eq
          _ ≤ ((n : ℝ) + 2) * (1 / ((n : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left hratio_bound (by positivity)
          _ = 1 + 1 / ((n : ℝ) + 1) := by
                field_simp [hden1]
                ring
      have hgap_bound :
          scaledGap ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
        have hα_pos : 0 < 1 / ((n : ℝ) + 2) := by positivity
        have hdiv_bound :
            scaledGap ≤
              (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
                (1 / ((n : ℝ) + 2)) := by
          refine (le_div_iff₀ hα_pos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hstep
        have hrhs_nonneg : 0 ≤ (ν : ℝ) := by
          exact_mod_cast ν.2
        calc
          scaledGap ≤
              (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
                (1 / ((n : ℝ) + 2)) := hdiv_bound
          _ = (ν : ℝ) *
              (-(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))) := by
                field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
          _ ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left hlog_bound hrhs_nonneg
      have hsmall :
          1 + 1 / ((n : ℝ) + 1) < scaledGap / (ν : ℝ) := by
        have := hn
        linarith
      have hlarge :
          (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) < scaledGap := by
        simpa [mul_comm] using (lt_div_iff₀ hν_pos).1 hsmall
      exact (not_lt_of_ge hgap_bound) hlarge
  -- Divide the scaled-gap estimate by the positive path parameter.
  exact (le_div_iff₀ ht).2 (by simpa [gap, scaledGap, mul_comm] using hscaled)

-- Proof sketch: compare the approximate center `x` with an exact penalty minimizer `xPath` at
-- the same parameter `t`. The approximate-centering hypothesis bounds the primal error
-- `t ⟪c, x - xPath⟫` by the Newton-decrement correction
-- `((β + √ν) β) / (1 - β)`, while
-- `centralPathPoint_objectiveGap_le_barrierParameter_div` controls the exact central-path gap
-- `⟪c, xPath⟫ - ⟪c, xOpt⟫` by `ν / t`. Adding the two bounds gives the stated estimate.
/-- Theorem 5.3.10: if `xPath` is an exact central-path point for the penalty objective
`z ↦ t ⟪c, z⟫ + F z` at some `t > 0`, and if another point `x` in `dom` satisfies the
approximate-centering condition
`‖t c + ∇ F(x)‖*ₓ ≤ β` with `β < 1`, then the objective gap from `x` to any optimal point
`xOpt ∈ closure dom` is bounded by
`(ν + ((β + √ν) β) / (1 - β)) / t`. In particular, the exact central-path gap is recovered by
the companion theorem above. -/
theorem centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (ht : 0 < (t : ℝ)) (hβ : β < 1)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := by
  have hcorr :
      inner ℝ c (x : E) - inner ℝ c (xPath : E) ≤
        ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) :=
    centralPathPenalty_objectiveCorrection_le_error_div
      (dom := dom) (ν := ν) (F := F) c t ht hβ hpath hxH happrox
  have hgap :
      inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) :=
    centralPathPoint_objectiveGap_le_barrierParameter_div
      (dom := dom) (ν := ν) (F := F) c t ht xOpt hopt hpath
  have hsplit :
      inner ℝ c (x : E) - inner ℝ c (xOpt : E) =
        (inner ℝ c (x : E) - inner ℝ c (xPath : E)) +
          (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := by
    ring
  -- Add the approximate-center correction to the exact central-path gap and normalize the scalar
  -- expression to the source form.
  calc
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) =
        (inner ℝ c (x : E) - inner ℝ c (xPath : E)) +
          (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := hsplit
    _ ≤ ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) + (ν : ℝ) / (t : ℝ) := by
          exact add_le_add hcorr hgap
    _ = ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := by
          field_simp [ht.ne', sub_ne_zero.mpr (ne_of_lt hβ)]
          ring

end
