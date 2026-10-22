/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Gradient HessianLocalNorm

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.4.1.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction`
  in `Corollary_5_3_2`, the owner-level recession-direction estimate used for each `p i`;
* `hessianLocalNorm` and the notation `‖u‖[F; x]` in `Definition_5_1_1`, the canonical Chapter 5
  owner for the Hessian local norm;
* the project’s generic finite-family pattern, for example `Theorem_3_38`, where a finite sum
  lives over `ι : Type*` with `[Fintype ι]` instead of the display model `Fin k`.

Source/core/bridge triage:
* source-facing: the textbook lower bound `∑ i, αᵢ / βᵢ ≤ ν`;
* core/canonical: `IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* bridge/view: the recession-direction lower bounds for each `p i` and the combined gradient
  estimate at `xBar`.

Primitive data:
* the barrier owner `hF : IsSelfConcordantBarrierOnWith (interior Q) ν F`;
* the convex set `Q`, base point `xBar ∈ interior Q`, and recession directions `p i`;
* the finite index owner `[Fintype ι]`, since the theorem uses only finite summation and no order
  or adjacency on the indices;
* the nonnegative scalars `α i`, the positive scalars `β i`, the backward-exit hypotheses, and
  the final point
  `xBar - ∑ i, α i • p i ∈ Q`.

Derived API:
* for each `i`, the owner-level recession-direction estimate
  `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`;
* the summed source-facing inequality `∑ i, α i / β i ≤ ν`.

The previous file fixed the ambient space to `EuclideanSpace ℝ (Fin n)` and the finite family to
`Fin k` even though the theorem uses only the real inner-product-space barrier owner and finite
summation. The refined statement keeps the same mathematical semantics while moving the public
surface to the canonical owner namespace, deleting the unnecessary concrete model layer, and
placing the finite family at the generic `[Fintype ι]` owner level. -/

namespace IsSelfConcordantBarrierOnWith

section

omit [CompleteSpace E]

/-- Helper for Theorem 5.4.1.2: every point of a convex set with a nonempty interior lies in the
closure of the interior. -/
private theorem mem_closure_interior_of_convex
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x y : E}
    (hx : x ∈ interior Q) (hy : y ∈ Q) :
    y ∈ closure (interior Q) := by
  -- Convexity identifies `closure (interior Q)` with `closure Q` once `interior Q` is nonempty.
  rw [hQ_convex.closure_interior_eq_closure_of_nonempty_interior ⟨x, hx⟩]
  exact subset_closure hy

/-- Helper for Theorem 5.4.1.2: a recession direction of `Q` also preserves `interior Q`. -/
private theorem recessionDirection_add_smul_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q) {q : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • q ∈ Q)
    {x : E} (hx : x ∈ interior Q) {t : ℝ} (ht : 0 ≤ t) :
    x + t • q ∈ interior Q := by
  let y : E := x + (2 * t) • q
  have hy_mem : y ∈ Q := by
    -- The recession hypothesis places the doubled forward step back in `Q`.
    simpa [y] using hrecession (interior_subset hx) (2 * t) (by positivity)
  have hx_as_shift : y + (-(2 * t)) • q ∈ interior Q := by
    -- Shifting the doubled point back by the same amount recovers the original interior point.
    convert hx using 1
    simp [y, add_assoc]
  have hmid :=
    hQ_convex.add_smul_mem_interior hy_mem hx_as_shift (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
  have hsum : (2 * t) • q + -t • q = t • q := by
    rw [← add_smul]
    ring
  -- The midpoint of the doubled forward step and the original interior point is the desired point.
  convert hmid using 1
  rw [show y = x + (2 * t) • q by rfl, smul_smul]
  have hcoeff : (1 / 2 : ℝ) * (-(2 * t)) = -t := by ring
  rw [hcoeff]
  simpa [y, add_assoc] using congrArg (fun v : E ↦ x + v) hsum.symm

end

/-- Helper for Theorem 5.4.1.2: the segment upper bound extends from interior endpoints to a
closure endpoint by sequential approximation. -/
private theorem segmentUpperBoundLogOneSub_of_mem_closure
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x : E} (hx : x ∈ dom) {y : E} (hy : y ∈ closure dom)
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    F ((1 - α) • x + α • y) ≤ F x - (ν : ℝ) * Real.log (1 - α) := by
  let hstd : IsStandardSelfConcordantOn dom F := hF.toIsStandardSelfConcordantOn
  rcases mem_closure_iff_seq_limit.mp hy with ⟨ySeq, hySeq_mem, hySeq_tendsto⟩
  let z : E := (1 - α) • x + α • y
  let zSeq : ℕ → E := fun n ↦ (1 - α) • x + α • ySeq n
  have hx_int : x ∈ interior dom := by
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hz_mem : z ∈ dom := by
    -- A strict chord from an interior point to a closure point stays in the open domain.
    have hz_int :
        (1 - α) • x + α • y ∈ interior dom :=
      hstd.convex_domain.combo_interior_closure_mem_interior
        hx_int hy (sub_pos.mpr hα.2) hα.1 (by ring)
    simpa [hstd.isOpen_domain.interior_eq] using hz_int
  have hzSeq_tendsto : Tendsto zSeq atTop (nhds z) := by
    -- The affine chord map is continuous in the closure endpoint.
    have hcontAffine : Continuous fun u : E ↦ (1 - α) • x + α • u := by
      exact continuous_const.add (continuous_const.smul continuous_id)
    simpa only [z, zSeq] using hcontAffine.continuousAt.tendsto.comp hySeq_tendsto
  have hF_tendsto :
      Tendsto (fun n ↦ F (zSeq n)) atTop (nhds (F z)) := by
    -- Continuity of `F` at the strict chord point lets the pointwise bounds pass to the limit.
    have hcontF : ContinuousAt F z := by
      exact (hstd.contDiffOn.continuousOn.continuousAt (hstd.isOpen_domain.mem_nhds hz_mem))
    simpa only [zSeq, z] using hcontF.tendsto.comp hzSeq_tendsto
  have hzSeq_mem_bound :
      ∀ n, F (zSeq n) ∈ Set.Iic (F x - (ν : ℝ) * Real.log (1 - α)) := by
    intro n
    have hbound_n :
        F (x + α • (ySeq n - x)) ≤ F x - (ν : ℝ) * Real.log (1 - α) :=
      hF.segment_upper_bound_log_one_sub hx (hySeq_mem n) hα
    have hzSeq_eq :
        zSeq n = x + α • (ySeq n - x) := by
      calc
        zSeq n = (x - α • x) + α • ySeq n := by
          dsimp [zSeq]
          rw [sub_smul, one_smul]
        _ = x + α • ySeq n - α • x := by
          abel
        _ = x + α • (ySeq n - x) := by
          rw [smul_sub]
          abel
    exact hzSeq_eq ▸ hbound_n
  -- Closedness of the upper half-line transfers the segment bound to the closure endpoint.
  exact isClosed_Iic.mem_of_tendsto hF_tendsto (Filter.Eventually.of_forall hzSeq_mem_bound)

/-- Helper for Theorem 5.4.1.2: the backward exit at scale `β i` forces the reciprocal bound
`1 / β ≤ ‖q‖[F; xBar]`. -/
private theorem oneDivBetaLe_hessianLocalNorm_of_backward_exit
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    {xBar q : E} (hxBar : xBar ∈ interior Q) {β : ℝ}
    (hβ_pos : 0 < β)
    (hβ_exit : xBar - β • q ∉ interior Q) :
    1 / β ≤ ‖q‖[F; xBar] := by
  let hstd : IsStandardSelfConcordantOn (interior Q) F := hF.toIsStandardSelfConcordantOn
  by_contra hrecip
  have hnorm_lt : ‖q‖[F; xBar] < 1 / β := lt_of_not_ge hrecip
  have hβ_nonneg : 0 ≤ β := hβ_pos.le
  have hquad_nonneg : 0 ≤ inner ℝ q (hessian F xBar q) :=
    hstd.hessian_posSemidef hxBar q
  have hsmul : ‖β • q‖[F; xBar] = β * ‖q‖[F; xBar] := by
    -- Positive homogeneity of the Hessian local norm turns the Dikin-radius test into a scalar one.
    calc
      ‖β • q‖[F; xBar]
          = Real.sqrt ((β * β) * inner ℝ q (hessian F xBar q)) := by
              rw [hessianLocalNorm_def]
              congr 1
              simp [inner_smul_left, inner_smul_right, mul_assoc]
      _ = Real.sqrt (β * β) * Real.sqrt (inner ℝ q (hessian F xBar q)) := by
            rw [Real.sqrt_mul' _ hquad_nonneg]
      _ = β * Real.sqrt (inner ℝ q (hessian F xBar q)) := by
            have hsqrtβ : Real.sqrt (β * β) = β := by
              rw [show β * β = β ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hβ_nonneg]
            rw [hsqrtβ]
      _ = β * ‖q‖[F; xBar] := by rw [hessianLocalNorm_def]
  have hstep_mem : xBar - β • q ∈ openDikinEllipsoid F xBar (1 / (1 : ℝ)) := by
    -- A backward step with local norm below `1` stays inside the unit Dikin ellipsoid.
    refine (mem_openDikinEllipsoid_iff F xBar (xBar - β • q) (1 / (1 : ℝ))).2 ?_
    calc
      ‖(xBar - β • q) - xBar‖[F; xBar] = ‖-(β • q)‖[F; xBar] := by
        congr 1
        abel
      _ = ‖β • q‖[F; xBar] := by rw [hessianLocalNorm_neg]
      _ = β * ‖q‖[F; xBar] := hsmul
      _ < β * (1 / β) := by
            exact mul_lt_mul_of_pos_left hnorm_lt hβ_pos
      _ = 1 / (1 : ℝ) := by
            field_simp [hβ_pos.ne']
  have hinside : xBar - β • q ∈ interior Q :=
    hstd.openDikinEllipsoid_inv_constant_subset hxBar hstep_mem
  exact (hβ_exit hinside)

/-- Helper for Theorem 5.4.1.2: evaluating the barrier inequality on a scaled direction produces
the scalar quadratic family used in the recession-direction argument. -/
private theorem barrierExpressionSmul
    {F : E → ℝ} {z u : E} (t : ℝ) :
    2 * inner ℝ (∇ F z) (t • u) - inner ℝ (t • u) (hessian F z (t • u)) =
      2 * t * inner ℝ (∇ F z) u - t ^ (2 : ℕ) * inner ℝ u (hessian F z u) := by
  -- Pull the scalar through the gradient pairing and the Hessian quadratic form.
  simp [inner_smul_left, inner_smul_right, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 5.4.1.2: a scalar quadratic family bounded above by `ν` forces the
discriminant estimate `a² ≤ ν b`. -/
private theorem sqLeMulOfBarrierLineFamily
    {a b ν : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ ν) :
    a ^ (2 : ℕ) ≤ ν * b := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · simp [ha0, hb0]
    · have htest := hline ((ν + 1) / (2 * a))
      have hcontr : ν + 1 ≤ ν := by
        have hrew : 2 * ((ν + 1) / (2 * a)) * a ≤ ν := by
          simpa [hb0] using htest
        field_simp [ha0] at hrew
        linarith
      linarith
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have htest := hline (a / b)
    have hquot : a ^ (2 : ℕ) / b ≤ ν := by
      have hrewrite :
          2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
        field_simp [hb_ne]
        ring
      simpa [hrewrite] using htest
    exact (_root_.div_le_iff₀ hb_pos).1 hquot

section

omit [CompleteSpace E]

/-- Helper for Theorem 5.4.1.2: differentiating the affine line `z + t • h` returns the fixed
direction `h`. -/
private theorem lineHasDerivAt
    (z h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • h) h t := by
  -- The affine line is the sum of a constant and a scalar multiple of the identity.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add z

end

/-- Helper for Theorem 5.4.1.2: scalarizing the gradient along a feasible line differentiates to
the corresponding Hessian pairing. -/
private theorem gradientPairingLineHasDerivAt
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} {t : ℝ} (hzt : z + t • h ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (z + s • h)) h)
      (inner ℝ (hessian F (z + t • h) h) h) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (z + t • h) := by
    -- A `C²` barrier objective has a differentiable Fréchet derivative field on its open domain.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (z + t • h) :=
      (hF.toIsStandardSelfConcordantOn.contDiffOn.of_le (by norm_num)).contDiffAt
          (hF.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hzt)
        |>.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (z + t • h) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (z + t • h) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (z + s • h))
        ((hessian F (z + t • h)).comp (ContinuousLinearMap.toSpanSingleton ℝ h)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (lineHasDerivAt z h t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (z + s • h)))
        (φ.comp ((hessian F (z + t • h)).comp (ContinuousLinearMap.toSpanSingleton ℝ h))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, h⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.4.1.2: the barrier-parameter inequality implies the pointwise quadratic
estimate `⟪∇F(z), h⟫² ≤ ν ⟪h, ∇²F(z)h⟫`. -/
private theorem gradientPairingSqLeBarrierParameterHessianPairing
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} (hz : z ∈ dom) :
    (inner ℝ (∇ F z) h) ^ (2 : ℕ) ≤
      (ν : ℝ) * inner ℝ h (hessian F z h) := by
  have hquad : 0 ≤ inner ℝ h (hessian F z h) :=
    hF.toIsStandardSelfConcordantOn.hessian_posSemidef hz h
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ (∇ F z) h - t ^ (2 : ℕ) * inner ℝ h (hessian F z h) ≤ (ν : ℝ) := by
    intro t
    have hbound := hF.barrier_parameter_bound hz (t • h)
    rw [barrierExpressionSmul] at hbound
    exact hbound
  -- Evaluating the owner inequality on all scalar multiples of `h` yields the discriminant bound.
  exact sqLeMulOfBarrierLineFamily hquad hline

/-- Helper for Theorem 5.4.1.2: along any feasible forward ray, the gradient pairing with the ray
direction is nonpositive. -/
private theorem innerGradientNonposOfRecessionDirectionAux
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} (hforward : ∀ τ : ℝ, 0 ≤ τ → z + τ • h ∈ dom)
    (hz : z ∈ dom) :
    inner ℝ (∇ F z) h ≤ 0 := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ F (z + t • h)) h
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t ht
    have hcontAt :=
      (gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt).continuousAt
    exact hcontAt.continuousWithinAt
  have hg_diff : DifferentiableOn ℝ g (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
    have hdiffAt :=
      (gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt).differentiableAt
    exact hdiffAt.differentiableWithinAt
  have hg_deriv_nonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ deriv g t := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
    have hquad := hF.toIsStandardSelfConcordantOn.hessian_posSemidef hzt h
    rw [(gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt).deriv]
    simpa [g, real_inner_comm] using hquad
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    -- The Hessian positivity makes the scalar gradient pairing monotone along the forward ray.
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hg_cont ?_ ?_
    · simpa [interior_Ici] using hg_diff
    · simpa [interior_Ici] using hg_deriv_nonneg
  by_cases hν : ν = 0
  · have hsq :=
      gradientPairingSqLeBarrierParameterHessianPairing (hF := hF) (z := z) (h := h) hz
    have hν_real : (ν : ℝ) = 0 := by
      exact_mod_cast hν
    have hsq_zero : (g 0) ^ (2 : ℕ) ≤ 0 := by
      simpa [g, hν_real] using hsq
    have hg_zero : g 0 = 0 := by
      nlinarith [sq_nonneg (g 0), hsq_zero]
    simpa [g] using hg_zero.le
  · have hν_pos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    by_contra hg0_pos
    have hg0_pos' : 0 < g 0 := by
      simpa [g] using lt_of_not_ge hg0_pos
    have hg_pos : ∀ t ∈ Set.Ici (0 : ℝ), 0 < g t := by
      intro t ht
      have hmono := hg_mono (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) ht (by simpa using ht)
      exact lt_of_lt_of_le hg0_pos' hmono
    let q : ℝ → ℝ := fun t ↦ (g t)⁻¹ + t / (ν : ℝ)
    have hq_cont : ContinuousOn q (Set.Ici (0 : ℝ)) := by
      intro t ht
      have hgt_ne : g t ≠ 0 := (hg_pos t ht).ne'
      have hg_contAt : ContinuousAt g t := by
        have hzt : z + t • h ∈ dom := hforward t ht
        exact (gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt).continuousAt
      have hlinCont : ContinuousAt (fun s : ℝ ↦ s / (ν : ℝ)) t := by
        simpa [div_eq_mul_inv] using
          ((continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) t).mul continuousAt_const)
      -- The reciprocal correction term is continuous wherever the scalar pairing stays positive.
      simpa [q] using ((hg_contAt.inv₀ hgt_ne).add hlinCont).continuousWithinAt
    have hq_hasDerivAt :
        ∀ t ∈ Set.Ioi (0 : ℝ),
          HasDerivAt q (-(deriv g t) / (g t) ^ (2 : ℕ) + 1 / (ν : ℝ)) t := by
      intro t ht
      have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
      have hgt_ne : g t ≠ 0 :=
        (hg_pos t (by simpa using (le_of_lt ht))).ne'
      have hg_hasDerivAt :
          HasDerivAt g (inner ℝ (hessian F (z + t • h) h) h) t := by
        simpa [g] using gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt
      have hginv :
          HasDerivAt (fun s : ℝ ↦ (g s)⁻¹) (-(deriv g t) / (g t) ^ (2 : ℕ)) t := by
        have hg_deriv : deriv g t = inner ℝ (hessian F (z + t • h) h) h := by
          rw [hg_hasDerivAt.deriv]
        simpa [hg_deriv] using hg_hasDerivAt.inv hgt_ne
      have hlin :
          HasDerivAt (fun s : ℝ ↦ s / (ν : ℝ)) (1 / (ν : ℝ)) t := by
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          (hasDerivAt_id t).const_mul ((ν : ℝ)⁻¹)
      -- Differentiate the reciprocal correction term entrywise.
      simpa [q] using hginv.add hlin
    have hq_diff : DifferentiableOn ℝ q (Set.Ioi (0 : ℝ)) := by
      intro t ht
      exact (hq_hasDerivAt t ht).differentiableAt.differentiableWithinAt
    have hq_deriv_nonpos : ∀ t ∈ Set.Ioi (0 : ℝ), deriv q t ≤ 0 := by
      intro t ht
      have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
      have hgt_pos : 0 < g t :=
        hg_pos t (by simpa using (le_of_lt ht))
      have hg_hasDerivAt :
          HasDerivAt g (inner ℝ (hessian F (z + t • h) h) h) t := by
        simpa [g] using gradientPairingLineHasDerivAt (hF := hF) (z := z) (h := h) hzt
      have hsq :
          (g t) ^ (2 : ℕ) ≤ (ν : ℝ) * deriv g t := by
        have hquad :=
          gradientPairingSqLeBarrierParameterHessianPairing
            (hF := hF) (z := z + t • h) (h := h) hzt
        have hg_deriv : deriv g t = inner ℝ (hessian F (z + t • h) h) h := by
          rw [hg_hasDerivAt.deriv]
        have hhess_eq : inner ℝ h (hessian F (z + t • h) h) = deriv g t := by
          rw [real_inner_comm, hg_deriv]
        simpa [g, hhess_eq] using hquad
      have hgt_sq_pos : 0 < (g t) ^ (2 : ℕ) := sq_pos_iff.mpr hgt_pos.ne'
      have hbase : 1 / (ν : ℝ) ≤ deriv g t / (g t) ^ (2 : ℕ) := by
        refine (_root_.le_div_iff₀ hgt_sq_pos).2 ?_
        have hdiv :
            (g t) ^ (2 : ℕ) / (ν : ℝ) ≤ deriv g t := by
          exact (_root_.div_le_iff₀ hν_pos).2 (by simpa [mul_comm] using hsq)
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      rw [(hq_hasDerivAt t ht).deriv]
      calc
        -(deriv g t) / (g t) ^ (2 : ℕ) + 1 / (ν : ℝ)
            = 1 / (ν : ℝ) - deriv g t / (g t) ^ (2 : ℕ) := by ring
        _ ≤ 0 := sub_nonpos.mpr hbase
    have hq_antitone : AntitoneOn q (Set.Ici (0 : ℝ)) := by
      -- The correction `1 / g + t / ν` has nonpositive derivative, hence decreases on the ray.
      refine antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hq_cont ?_ ?_
      · simpa [interior_Ici] using hq_diff
      · simpa [interior_Ici] using hq_deriv_nonpos
    let T : ℝ := (ν : ℝ) / (g 0) + 1
    have hT_nonneg : 0 ≤ T := by
      dsimp [T]
      positivity
    have hq_upper : q T ≤ q 0 := by
      exact hq_antitone (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp)
        (show T ∈ Set.Ici (0 : ℝ) by simpa [T] using hT_nonneg) hT_nonneg
    have hq_lower : T / (ν : ℝ) < q T := by
      have hgt_pos : 0 < g T := hg_pos T (by simpa [T] using hT_nonneg)
      dsimp [q]
      have hrecip_pos : 0 < (g T)⁻¹ := inv_pos.mpr hgt_pos
      linarith
    have hbad : T / (ν : ℝ) < 1 / (g 0) := by
      have hq_upper' : q T ≤ 1 / g 0 := by
        simpa [q] using hq_upper
      exact lt_of_lt_of_le hq_lower hq_upper'
    have hT_eval : T / (ν : ℝ) = 1 / (g 0) + 1 / (ν : ℝ) := by
      dsimp [T]
      field_simp [hν_pos.ne', hg0_pos'.ne']
    have hν_inv_pos : 0 < 1 / (ν : ℝ) := one_div_pos.mpr hν_pos
    rw [hT_eval] at hbad
    linarith

/-- Helper for Theorem 5.4.1.2: either the whole backward ray stays in the domain, or the first
obstruction lies on the frontier. -/
private theorem backwardFrontierOrBackwardRay
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F) {x : E} (hx : x ∈ dom) {h : E} :
    (∀ τ : ℝ, 0 ≤ τ → x - τ • h ∈ dom) ∨ ∃ τ : ℝ, 0 < τ ∧ x - τ • h ∈ frontier dom := by
  classical
  let line : ℝ → E := fun τ ↦ x - τ • h
  have hline_cont : Continuous line := by
    simpa [line, sub_eq_add_neg] using
      (continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ (-h : E))))
  by_cases hfull : ∀ τ : ℝ, 0 ≤ τ → x - τ • h ∈ dom
  · exact Or.inl hfull
  · right
    push Not at hfull
    rcases hfull with ⟨τbad, hτbad_nonneg, hτbad_not_mem⟩
    let S : Set ℝ := {τ : ℝ | 0 ≤ τ ∧ x - τ • h ∈ dom}
    have hS_nonempty : S.Nonempty := by
      refine ⟨0, ?_⟩
      simp [S, hx]
    have hS_bdd : BddAbove S := by
      refine ⟨τbad, ?_⟩
      intro s hs
      rcases hs with ⟨hs_nonneg, hs_mem⟩
      by_contra hs_gt
      have hs_pos : 0 < s := lt_of_le_of_lt hτbad_nonneg (lt_of_not_ge hs_gt)
      have hfrac : τbad / s ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg hτbad_nonneg hs_pos.le, ?_⟩
        field_simp [hs_pos.ne']
        linarith [lt_of_not_ge hs_gt]
      have hsegment :
          x + (τbad / s) • ((x - s • h) - x) ∈ dom :=
        hF.toIsStandardSelfConcordantOn.convex_domain.add_smul_sub_mem hx hs_mem hfrac
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have hmul : (τbad / s) * s = τbad := by
        field_simp [hs_ne]
      have hrewrite :
          x + (τbad / s) • ((x - s • h) - x) = x - τbad • h := by
        calc
          x + (τbad / s) • ((x - s • h) - x)
              = x - (((τbad / s) * s) • h) := by
                  simp [sub_eq_add_neg, smul_smul, mul_comm]
          _ = x - τbad • h := by
                rw [hmul]
      exact hτbad_not_mem (hrewrite ▸ hsegment)
    let τ0 : ℝ := sSup S
    have hτ0_closure : τ0 ∈ closure S := csSup_mem_closure hS_nonempty hS_bdd
    have hτ0_nonneg : 0 ≤ τ0 := by
      exact le_csSup hS_bdd (by simp [S, hx])
    have hopen : IsOpen dom := hF.toIsStandardSelfConcordantOn.isOpen_domain
    have hzero_mem : x - (0 : ℝ) • h ∈ dom := by
      simpa using hx
    have hpreimage : {τ : ℝ | line τ ∈ dom} ∈ nhds (0 : ℝ) := by
      exact hline_cont.continuousAt.preimage_mem_nhds (hopen.mem_nhds hzero_mem)
    rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hε_pos, hε_ball⟩
    let δ : ℝ := ε / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_mem : x - δ • h ∈ dom := by
      apply hε_ball
      rw [Metric.mem_ball, Real.dist_eq]
      have hδ_lt : δ < ε := by
        dsimp [δ]
        linarith
      simpa [abs_of_nonneg hδ_pos.le] using hδ_lt
    have hδ_in_S : δ ∈ S := ⟨hδ_pos.le, hδ_mem⟩
    have hτ0_pos : 0 < τ0 := lt_of_lt_of_le hδ_pos (le_csSup hS_bdd hδ_in_S)
    have hτ0_closure_dom : x - τ0 • h ∈ closure dom := by
      have hmaps : Set.MapsTo line S dom := by
        intro τ hτ
        exact hτ.2
      exact map_mem_closure (f := line) hline_cont hτ0_closure hmaps
    have hτ0_not_mem : x - τ0 • h ∉ dom := by
      intro hτ0_mem
      have hpreimage0 : {τ : ℝ | line τ ∈ dom} ∈ nhds τ0 := by
        exact (hline_cont.continuousAt).preimage_mem_nhds (hopen.mem_nhds hτ0_mem)
      rcases Metric.mem_nhds_iff.mp hpreimage0 with ⟨ε0, hε0_pos, hε0_ball⟩
      let τ1 : ℝ := τ0 + ε0 / 2
      have hτ1_nonneg : 0 ≤ τ1 := by
        dsimp [τ1]
        positivity
      have hτ1_mem : x - τ1 • h ∈ dom := by
        apply hε0_ball
        rw [Metric.mem_ball, Real.dist_eq]
        have hhalf_nonneg : 0 ≤ ε0 / 2 := by positivity
        have hhalf_lt : ε0 / 2 < ε0 := by linarith
        rw [show τ1 - τ0 = ε0 / 2 by simp [τ1], abs_of_nonneg hhalf_nonneg]
        exact hhalf_lt
      have hτ1_in_S : τ1 ∈ S := ⟨hτ1_nonneg, hτ1_mem⟩
      have hτ1_le : τ1 ≤ τ0 := le_csSup hS_bdd hτ1_in_S
      have : τ0 + ε0 / 2 ≤ τ0 := by
        simpa [τ1] using hτ1_le
      linarith
    refine ⟨τ0, hτ0_pos, ?_⟩
    -- The supremum point is in the closure but not in the open domain, hence on the frontier.
    rw [frontier, hopen.interior_eq]
    exact ⟨hτ0_closure_dom, hτ0_not_mem⟩

/-- Helper for Theorem 5.4.1.2: the backward exit at scale `β i` forces the reciprocal bound
`1 / β i ≤ ⟪-∇ F xBar, p i⟫`. -/
private theorem oneDivBetaLe_negGradientInner_of_recession_exit
    {ι : Type v} {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    (p : ι → E)
    (hrecession :
      ∀ i, ∀ ⦃x : E⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q)
    (β : ι → ℝ)
    (hβ_pos : ∀ i, 0 < β i)
    (hβ_exit : ∀ i, xBar - β i • p i ∉ interior Q)
    (i : ι) :
    1 / β i ≤ inner ℝ (-∇ F xBar) (p i) := by
  have hrecip_le :
      1 / β i ≤ ‖p i‖[F; xBar] :=
    oneDivBetaLe_hessianLocalNorm_of_backward_exit hF hxBar (hβ_pos i) (hβ_exit i)
  have hrecession_int :
      ∀ ⦃y : E⦄, y ∈ interior Q → ∀ t : ℝ, 0 ≤ t → y + t • p i ∈ interior Q := by
    intro y hy t ht
    -- Convexity keeps an interior point inside `interior Q` along any recession direction.
    exact recessionDirection_add_smul_mem_interior hQ_convex (hrecession i) hy ht
  have hnonascent :
      inner ℝ (∇ F xBar) (p i) ≤ 0 :=
    innerGradientNonposOfRecessionDirectionAux
      (hF := hF) (z := xBar) (h := p i) (fun t ht ↦ hrecession_int hxBar t ht) hxBar
  have hfrontier :
      ∃ τ : ℝ, 0 < τ ∧ xBar - τ • p i ∈ frontier (interior Q) := by
    rcases backwardFrontierOrBackwardRay (hF := hF) (x := xBar) (h := p i) hxBar with
      hbackward | hfrontier
    · exact False.elim <| hβ_exit i <| hbackward (β i) (hβ_pos i).le
    · exact hfrontier
  have hnorm_le :
      ‖p i‖[F; xBar] ≤ inner ℝ (-∇ F xBar) (p i) := by
    let hself : IsSelfConcordantOnWith (interior Q) 1 F := hF.toIsStandardSelfConcordantOn
    -- The self-concordant owner theorem closes the norm-to-gradient step once the frontier and
    -- nonascent side conditions are supplied on the barrier domain.
    simpa using
      hself.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
        (hMf := by norm_num) hrecession_int hxBar hfrontier hnonascent
  -- The reciprocal-local-norm estimate and the owner recession estimate close the one-step bound.
  exact le_trans hrecip_le hnorm_le

/-- Helper for Theorem 5.4.1.2: summing the per-direction exit bounds rewrites to the single
gradient pairing with `xBar - ∑ i, α i • p i`. -/
private theorem sumAlphaDivBetaLe_gradientPairing_of_recession_exits
    {ι : Type v} [Fintype ι] {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    (p : ι → E)
    (hrecession :
      ∀ i, ∀ ⦃x : E⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q)
    (β α : ι → ℝ)
    (hβ_pos : ∀ i, 0 < β i)
    (hβ_exit : ∀ i, xBar - β i • p i ∉ interior Q)
    (hα_nonneg : ∀ i, 0 ≤ α i) :
    ∑ i, α i / β i ≤ inner ℝ (∇ F xBar) ((xBar - ∑ i, α i • p i) - xBar) := by
  have hterm :
      ∀ i, α i / β i ≤ α i * inner ℝ (-∇ F xBar) (p i) := by
    intro i
    have hbase :=
      oneDivBetaLe_negGradientInner_of_recession_exit
        hF hQ_convex hxBar p hrecession β hβ_pos hβ_exit i
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hbase (hα_nonneg i)
  calc
    ∑ i, α i / β i ≤ ∑ i, α i * inner ℝ (-∇ F xBar) (p i) := by
      exact Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ = ∑ i, inner ℝ (-∇ F xBar) (α i • p i) := by
      simp [inner_smul_right]
    _ = inner ℝ (-∇ F xBar) (∑ i, α i • p i) := by
      rw [inner_sum]
    _ = inner ℝ (∇ F xBar) ((xBar - ∑ i, α i • p i) - xBar) := by
      simp [inner_neg_left, sub_eq_add_neg, add_comm, add_left_comm]

/-- Helper for Theorem 5.4.1.2: every feasible point `y ∈ Q` satisfies
`⟪∇ F xBar, y - xBar⟫ ≤ ν`. -/
private theorem gradientPairingToPoint_le_barrierParameter
    {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    {y : E} (hy : y ∈ Q) :
    inner ℝ (∇ F xBar) (y - xBar) ≤ (ν : ℝ) := by
  let hstd : IsStandardSelfConcordantOn (interior Q) F := hF.toIsStandardSelfConcordantOn
  let gap : ℝ := inner ℝ (∇ F xBar) (y - xBar)
  have hy_closure : y ∈ closure (interior Q) :=
    mem_closure_interior_of_convex hQ_convex hxBar hy
  have hdiff : DifferentiableAt ℝ F xBar := by
    -- The barrier objective is `C³` on its open domain.
    -- Therefore the ambient gradient is defined at `xBar`.
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds hxBar)).differentiableAt
        (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad :
      gradientWithin F (interior Q) xBar = ∇ F xBar := by
    -- On the open domain `interior Q`, the within-gradient agrees with the ambient gradient.
    rw [gradientWithin, gradient]
    congr
    exact fderivWithin_eq_fderiv (hstd.isOpen_domain.uniqueDiffWithinAt hxBar) hdiff
  have hchord :
      ∀ α, α ∈ Set.Ico (0 : ℝ) 1 →
        α * gap ≤ -(ν : ℝ) * Real.log (1 - α) := by
    intro α hα
    let z : E := (1 - α) • xBar + α • y
    have hz_mem : z ∈ interior Q := by
      have hx_int : xBar ∈ interior (interior Q) := by
        simpa [hstd.isOpen_domain.interior_eq] using hxBar
      -- A strict chord from `xBar` to a closure point of the feasible set remains feasible.
      have hz_int : z ∈ interior (interior Q) :=
        hstd.convex_domain.combo_interior_closure_mem_interior
          hx_int hy_closure (sub_pos.mpr hα.2) hα.1 (by ring)
      simpa [hstd.isOpen_domain.interior_eq] using hz_int
    have hupper :
        F z ≤ F xBar - (ν : ℝ) * Real.log (1 - α) :=
      segmentUpperBoundLogOneSub_of_mem_closure hF hxBar hy_closure hα
    have hsupport :
        F z ≥ F xBar + inner ℝ (∇ F xBar) (z - xBar) := by
      -- Convexity at `xBar` supplies the lower tangent-plane estimate for the strict chord point.
      simpa [hgrad] using
        hstd.convexOn.lower_tangent_plane xBar hxBar hdiff.differentiableWithinAt z hz_mem
    have hpair :
        inner ℝ (∇ F xBar) (z - xBar) = α * gap := by
      dsimp [z, gap]
      calc
        inner ℝ (∇ F xBar) ((1 - α) • xBar + α • y - xBar)
            = inner ℝ (∇ F xBar) (α • (y - xBar)) := by
                congr 1
                calc
                  (1 - α) • xBar + α • y - xBar
                      = (xBar - α • xBar) + α • y - xBar := by
                          rw [sub_smul, one_smul]
                  _ = α • y - α • xBar := by
                        abel
                  _ = α • (y - xBar) := by
                        rw [smul_sub]
        _ = α * inner ℝ (∇ F xBar) (y - xBar) := by
              rw [inner_smul_right]
        _ = α * gap := by
              rfl
    linarith
  by_cases hν : ν = 0
  · have hhalf :
        (1 / 2 : ℝ) * gap ≤ -(ν : ℝ) * Real.log (1 - (1 / 2 : ℝ)) := by
      exact hchord (1 / 2 : ℝ) (by constructor <;> norm_num)
    rw [hν] at hhalf
    norm_num at hhalf
    have hgap_nonpos : gap ≤ 0 := by
      linarith
    simpa [gap, hν] using hgap_nonpos
  · have hν_pos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    by_contra hgap_gt
    have hε_pos : 0 < gap / (ν : ℝ) - 1 := by
      have hgap_gt' : (ν : ℝ) < gap := by
        exact not_le.mp (by simpa [gap] using hgap_gt)
      have hdiv_lt : 1 < gap / (ν : ℝ) := by
        exact (one_lt_div hν_pos).2 hgap_gt'
      linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_pos
    have hα_mem : (1 / ((n : ℝ) + 2)) ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · positivity
      · have htwo_pos : 0 < (n : ℝ) + 2 := by positivity
        exact (div_lt_one htwo_pos).2 (by linarith)
    have hstep :
        (1 / ((n : ℝ) + 2)) * gap ≤
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
        have hbase_ne : 1 - 1 / ((n : ℝ) + 2) ≠ 0 := by linarith
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
        gap ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
      have hα_pos : 0 < 1 / ((n : ℝ) + 2) := by positivity
      have hdiv_bound :
          gap ≤
            (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
              (1 / ((n : ℝ) + 2)) := by
        refine (le_div_iff₀ hα_pos).2 ?_
        simpa [mul_assoc, mul_left_comm, mul_comm] using hstep
      have hrhs_nonneg : 0 ≤ (ν : ℝ) := by
        exact_mod_cast ν.2
      calc
        gap ≤
            (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
              (1 / ((n : ℝ) + 2)) := hdiv_bound
        _ = (ν : ℝ) *
            (-(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))) := by
              field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
        _ ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hlog_bound hrhs_nonneg
    have hsmall :
        1 + 1 / ((n : ℝ) + 1) < gap / (ν : ℝ) := by
      have := hn
      linarith
    have hlarge :
        (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) < gap := by
      simpa [mul_comm] using (lt_div_iff₀ hν_pos).1 hsmall
    exact (not_lt_of_ge hgap_bound) hlarge

-- Proof sketch: for each recession direction `p i`, apply the recession-direction gradient bound
-- for self-concordant barriers at `xBar` together with the finite backward-step hypothesis
-- `xBar - β i • p i ∉ interior Q` to obtain
-- `1 / β i ≤ ‖p i‖[F; xBar] ≤ ⟪-∇ F xBar, p i⟫`.
-- Then use the basic barrier-parameter inequality with
-- `y = xBar - ∑ i, α i • p i ∈ Q` to get
-- `∑ i α i / β i ≤ ⟪∇ F xBar, xBar - y⟫ ≤ ν`.
/-- Theorem 5.4.1.2: if `Q ⊆ E` is a convex set in a real Hilbert space, `xBar ∈ interior Q`,
`(p i)` is a finite family of recession directions of `Q`, each backward step
`xBar - βᵢ • p i` leaves `interior Q`, and `xBar - ∑ i, α i • p i ∈ Q` for nonnegative scalars
`α i` and positive scalars `β i`, then every `ν`-self-concordant barrier `F` on `interior Q`
satisfies
`∑ i, αᵢ / βᵢ ≤ ν`. -/
theorem barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
    {ι : Type v} [Fintype ι] {Q : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hQ_convex : Convex ℝ Q)
    {xBar : E} (hxBar : xBar ∈ interior Q)
    (p : ι → E)
    (hrecession :
      ∀ i, ∀ ⦃x⦄, x ∈ Q → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ Q)
    (β α : ι → ℝ)
    (hβ_pos : ∀ i, 0 < β i)
    (hβ_exit : ∀ i, xBar - β i • p i ∉ interior Q)
    (hα_nonneg : ∀ i, 0 ≤ α i)
    (hy : xBar - ∑ i, α i • p i ∈ Q) :
    ∑ i, α i / β i ≤ (ν : ℝ) := by
  let y : E := xBar - ∑ i, α i • p i
  have hsum :
      ∑ i, α i / β i ≤ inner ℝ (∇ F xBar) (y - xBar) := by
    -- Sum the per-direction exit inequalities and rewrite the result as one gradient pairing.
    simpa [y] using
      sumAlphaDivBetaLe_gradientPairing_of_recession_exits
        hF hQ_convex hxBar p hrecession β α hβ_pos hβ_exit hα_nonneg
  have hgap :
      inner ℝ (∇ F xBar) (y - xBar) ≤ (ν : ℝ) := by
    -- The endpoint `y` lies in `Q`, so the global barrier-parameter pairing bound applies.
    simpa [y] using
      gradientPairingToPoint_le_barrierParameter hF hQ_convex hxBar hy
  exact le_trans hsum hgap

end IsSelfConcordantBarrierOnWith

end
