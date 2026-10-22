/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_2_2.Common

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped DikinEllipsoidNotation Gradient HessianLocalNorm NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.2.2 lies in the Chapter 5 self-concordant Newton local-convergence domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint` and `selfConcordantNewtonShift` in `Definition_5_2_1`, the
  Chapter 5 owners for the three one-step Newton variants;
* `newtonDecrement` and the notation `λ[f; x | hx]`, the chapter owner for the Newton decrement;
* `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem`, which supplies the determinant
  witness needed by `selfConcordantNewtonNextPoint`;
* `Nesterov.Chap05.Theorem_5_2_2.Common`, the canonical owner for the determinant-based
  transport and residual helpers used below.

Best owner abstraction:
* source-facing: the three source clauses of Theorem 5.2.2 for the standard, damped, and
  intermediate one-step updates;
* core/canonical: `selfConcordantNewtonNextPoint` together with the Newton decrement notation;
* bridge/view: the determinant witness derived from `x ∈ dom`.

This repair keeps the item as the three numbered source-facing clauses of Theorem 5.2.2.
The textbook parameter `M_f` is positive, so each clause is stated on the canonical positive
surface `Mf : NNRealˣ`, matching the nearby Chapter 5 API for the damped and intermediate
variants.
-/

section SourceFaithfulPublicAPI

variable {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f] [HasPositiveDefiniteHessianOn dom f]

/-- Helper for Theorem 5.2.2: the source-facing decrement notation `λ[f; x | hx]` agrees with the
determinant-based normal form used by the support API. -/
private theorem newtonDecrement_eq_ndec_of_mem
    {x : E} (hx : x ∈ dom) :
    λ[f; x | hx] =
      ndec(f, x, (Mf : NNReal), hx,
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)) := by
  -- Expand both Chapter 5 decrement owners once and compare the shared dual-local-norm formula.
  simp

/-- Helper for Theorem 5.2.2: the explicit intermediate-step coefficient from `(5.2.8)` is
dominated by the simpler factor `1 + 2 s` for every `s ≥ 0`. -/
private theorem intermediate_textbookFactor_le_double
    {s : ℝ} (hs : 0 ≤ s) :
    1 + s + s / (1 + s + s ^ (2 : ℕ)) ≤ 1 + 2 * s := by
  have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by
    positivity
  have hfrac_le : s / (1 + s + s ^ (2 : ℕ)) ≤ s := by
    -- The extra positive denominator factor can only decrease the final fractional term.
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith [sq_nonneg s]
  nlinarith

/-- Helper for Theorem 5.2.2: the damped Newton-step radius is strictly below the admissible
Dikin threshold. -/
private theorem damped_step_localNorm_lt_inv
    {δ : ℝ} (hδ_nonneg : 0 ≤ δ) :
    δ / (1 + (Mf : ℝ) * δ) < 1 / (Mf : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  -- Clear denominators after isolating the positive damped-step denominator.
  refine (lt_div_iff₀ hMf_pos).2 ?_
  have hfrac_lt :
      ((Mf : ℝ) * δ) / (1 + (Mf : ℝ) * δ) < 1 := by
    have hden_pos : 0 < 1 + (Mf : ℝ) * δ := by
      positivity
    refine (div_lt_iff₀ hden_pos).2 ?_
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac_lt

omit [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.2: any point whose local distance from `x` is below `1 / M_f`
belongs to the open Dikin ellipsoid around `x`, hence stays in the self-concordant domain. -/
private theorem mem_openDikinEllipsoid_and_domain_of_localNorm_lt_inv
    {x y : E} (hx : x ∈ dom) (hstep_lt : ‖y - x‖[f; x] < 1 / (Mf : ℝ)) :
    y ∈ W⁰[f; x](1 / (Mf : ℝ)) ∧ y ∈ dom := by
  have hy_mem : y ∈ W⁰[f; x](1 / (Mf : ℝ)) := by
    -- Convert the local-radius estimate into the canonical open-Dikin membership criterion.
    exact (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).2 hstep_lt
  refine ⟨hy_mem, ?_⟩
  -- Route correction: endpoint membership is owned by the Dikin inclusion theorem, so the
  -- wrapper file should reuse that bridge instead of rebuilding branch-local domain arguments.
  exact
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
      (domain := dom) (Mf := (Mf : NNReal)) (f := f) inferInstance hx hy_mem

/- The determinant-based transport and averaged-residual helper layer now lives in
`Nesterov.Chap05.Theorem_5_2_2.Common`, and the source-facing item file below only keeps the
branch-specific wrappers that are not exported from that shared owner. -/

/-- Helper for Theorem 5.2.2: after proving domain membership for the standard Newton update, the
remaining decrement bound is exactly the base-residual-plus-transport endpoint closure in
determinant-based normal form. -/
private theorem standardNextPointDecrementBound
    {x xPlus : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus_def : xPlus = selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH)
    (hxPlus : xPlus ∈ dom)
    (hxPlus_mem : xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)))
    (hstep_eq :
      let δ := ndec(f, x, (Mf : NNReal), hx, hH)
      ‖xPlus - x‖[f; x] = δ) :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    ndec(f, xPlus, (Mf : NNReal), hxPlus,
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus)) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) / (1 - (Mf : ℝ) * δ) ^ (2 : ℕ) := by
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
  let a : ℝ := (Mf : ℝ) * ‖xPlus - x‖[f; x]
  let hPosX : (hessian f x).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hPosXPlus : (hessian f xPlus).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hxPlus
  let hHPlus : (hessian f xPlus).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus
  have hu_norm : ‖u‖[f; x] = δ := by
    -- Identify the Newton direction norm with the old decrement before transporting anything.
    simpa [H, u, δ] using
      inverseNewtonDirectionLocalNorm_eq_ndec
        (dom := dom) (Mf := Mf) (f := f) (x := x) hx hH
  have hgrad :
      ∇ f xPlus = (H - G) u := by
    -- Route correction: for the standard step, the gradient update collapses to the pure
    -- averaged-Hessian residual because the step size is exactly `1`.
    have hgrad_raw :
        ∇ f (selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH) =
          (1 - selfConcordantNewtonStepSize f (Mf : NNReal) .standard x hx hH) • ∇ f x +
            selfConcordantNewtonStepSize f (Mf : NNReal) .standard x hx hH •
              ((hessian f x -
                  ∫ τ in (0 : ℝ)..1,
                    hessian f
                      (x + τ •
                        (selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH - x)))
                ((hessian f x).inverse (∇ f x))) := by
      simpa [hxPlus_def] using
        nextGradient_eq_oldGradient_plus_averageResidual
          (dom := dom) (Mf := Mf) (f := f)
          .standard hx hH
          (hxPlus := by simpa [hxPlus_def] using hxPlus)
    simpa [H, u, G, hxPlus_def, selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      hgrad_raw
  have hstep_lt : ‖xPlus - x‖[f; x] < 1 / (Mf : ℝ) := by
    -- The endpoint stays inside the open Dikin ellipsoid, so its radius is strictly admissible.
    simpa using (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1 hxPlus_mem
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have ha_lt_one : a < 1 := by
    -- Convert the Dikin-radius bound into the scalar transport parameter bound `a < 1`.
    dsimp [a]
    simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hstep_lt
  have hfactor_nonneg : 0 ≤ 1 / (1 - a) := by
    have hden_pos : 0 < 1 - a := by
      linarith
    positivity
  have hbase :
      HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
    -- Bound the averaged-Hessian residual first in the base metric at `x`.
    simpa [H, G, a, hPosX] using
      average_hessian_residual_baseDualBound
        (dom := dom) (Mf := Mf) (f := f)
        (x := x) (y := xPlus) (u := u) hx hH hxPlus_mem
  have htransport :
      HessianDualLocalNorm.ofDetNeZero f xPlus hPosXPlus hHPlus (toDual ℝ E ((H - G) u)) ≤
        (1 / (1 - a)) *
          HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E ((H - G) u)) := by
    -- Transport that residual once from the base metric to the endpoint metric.
    simpa [a, hPosX, hPosXPlus] using
      dualLocalNorm_transport_to_endpoint
        (dom := dom) (Mf := Mf) (f := f)
        (x := x) (y := xPlus) (v := (H - G) u) hx hH hxPlus_mem hHPlus
  have hendpoint :
      HessianDualLocalNorm.ofDetNeZero f xPlus hPosXPlus hHPlus (toDual ℝ E ((H - G) u)) ≤
        (1 / (1 - a)) * ((a / (1 - a)) * ‖u‖[f; x]) := by
    -- Chain the transport estimate with the base residual bound in one fixed spelling.
    exact le_trans htransport (mul_le_mul_of_nonneg_left hbase hfactor_nonneg)
  have hndec :
      ndec(f, xPlus, (Mf : NNReal), hxPlus, hHPlus) =
        HessianDualLocalNorm.ofDetNeZero f xPlus hPosXPlus hHPlus (toDual ℝ E (∇ f xPlus)) := by
    -- Rewrite the endpoint decrement into determinant-based dual-local-norm form.
    rw [NewtonDecrement.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
    simp [InnerProductSpace.toDual_apply_apply]
  have ha_delta : a = (Mf : ℝ) * δ := by
    -- Replace the transport scalar `a` by the old decrement using the standard-step norm identity.
    dsimp [a]
    rw [hstep_eq]
  have hden_pos : 0 < 1 - (Mf : ℝ) * δ := by
    rw [← ha_delta]
    linarith
  -- Assemble the transported residual bound and normalize the scalar expression.
  calc
    ndec(f, xPlus, (Mf : NNReal), hxPlus, hHPlus) =
        HessianDualLocalNorm.ofDetNeZero f xPlus hPosXPlus hHPlus
          (toDual ℝ E (∇ f xPlus)) := hndec
    _ = HessianDualLocalNorm.ofDetNeZero f xPlus hPosXPlus hHPlus
          (toDual ℝ E ((H - G) u)) := by
          rw [hgrad]
    _ ≤ (1 / (1 - a)) * ((a / (1 - a)) * ‖u‖[f; x]) := hendpoint
    _ = ((Mf : ℝ) * δ ^ (2 : ℕ)) / (1 - (Mf : ℝ) * δ) ^ (2 : ℕ) := by
          rw [ha_delta, hu_norm]
          field_simp [hden_pos.ne']

/-- Helper for Theorem 5.2.2: both positive Newton variants should close from one endpoint-metric
assembly lemma rather than repeating the same transport and residual argument branch-by-branch. -/
private theorem positiveVariantNextPointAssemblyBound
    (variant : SelfConcordantNewtonVariant)
    {x xPlus : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus_def : xPlus = selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH)
    (hxPlus : xPlus ∈ dom)
    (hxPlus_mem : xPlus ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) {α a : ℝ}
    (hα_eq : α = selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH)
    (hα_nonneg : 0 ≤ α) (h1mα_nonneg : 0 ≤ 1 - α)
    (ha : a = (Mf : ℝ) * ‖xPlus - x‖[f; x])
    (hlowerCoeff : α / (1 - a) - 1 ≤ (1 - α) + α * a) :
    ndec(f, xPlus, (Mf : NNReal), hxPlus,
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus)) ≤
      (((1 - α) / (1 - a)) + α * (a / (1 - a))) *
        ndec(f, x, (Mf : NNReal), hx, hH) := by
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
  let hHPlus : (hessian f xPlus).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus
  have hu : H u = ∇ f x := by
    let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
    exact hInv.self_apply_inverse (∇ f x)
  have hgrad :
      let H := hessian f x
      let u := H.inverse (∇ f x)
      let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
      ∇ f xPlus = (H - α • G) u := by
    have hgrad_raw :
        ∇ f xPlus =
          (1 - α) • ∇ f x + α • ((H - G) u) := by
      simpa [hxPlus_def, hα_eq, H, u, G, ContinuousLinearMap.sub_apply] using
        nextGradient_eq_oldGradient_plus_averageResidual
          (dom := dom) (Mf := Mf) (f := f)
          variant hx hH
          (hxPlus := by simpa [hxPlus_def] using hxPlus)
    -- Rewrite the normalized gradient decomposition into the single operator spelling `H - α G`.
    calc
      ∇ f xPlus = (1 - α) • ∇ f x + α • ((H - G) u) := hgrad_raw
      _ = (1 - α) • H u + α • ((H - G) u) := by rw [hu]
      _ = (H - α • G) u := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, smul_sub]
        calc
          (1 - α) • H u + (α • H u - α • G u) =
              ((1 - α) • H u + α • H u) - α • G u := by
                abel
          _ = H u - α • G u := by
                rw [← add_smul]
                have hsum : (1 - α) + α = 1 := by ring
                rw [hsum, one_smul]
  -- Reuse the shared endpoint assembly once the branch-specific scalar inequality is supplied.
  simpa [hHPlus] using
    positiveVariantEndpointAssemblyBound
        (dom := dom) (Mf := Mf) (f := f)
        (x := x) (y := xPlus) hx hxPlus hH hHPlus hxPlus_mem hα_nonneg h1mα_nonneg
        ha hlowerCoeff hgrad

/-- Helper for Theorem 5.2.2: the standard Newton branch should be proved in determinant-based
normal form before rewriting back to the source-facing `λ` notation. -/
private theorem standardNextPointMemAndNdecBound
    {x : E} (hx : x ∈ dom) (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let hH := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH
    ∃ hxPlus : xPlus ∈ dom,
      ndec(f, xPlus, (Mf : NNReal), hxPlus,
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus)) ≤
        ((Mf : ℝ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)) /
          (1 - (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ) := by
  let hH : (hessian f x).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (f := f) hx
  let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  have hstep_eq : ‖xPlus - x‖[f; x] = δ := by
    -- The standard branch uses step size `1`, so its displacement norm is exactly `δ`.
    simpa [xPlus, hH, δ, selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      next_point_sub_localNorm_eq_stepSize_mul_ndec
        (dom := dom) (Mf := Mf) (f := f) .standard hx hH
  have hstep_lt : ‖xPlus - x‖[f; x] < 1 / (Mf : ℝ) := by
    -- Rewrite the source-facing hypothesis into the determinant-based decrement spelling.
    simpa [δ, hstep_eq] using
      (show ndec(f, x, (Mf : NNReal), hx, hH) < 1 / (Mf : ℝ) by
        simpa [newtonDecrement_eq_ndec_of_mem (Mf := Mf) (f := f) hx] using hlambda)
  have hxPlus_data :
      xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) ∧ xPlus ∈ dom := by
    -- Package the admissible-radius consequences once so the standard branch only keeps the
    -- decrement-specific closure step below.
    exact mem_openDikinEllipsoid_and_domain_of_localNorm_lt_inv
      (Mf := Mf) (f := f) (x := x) (y := xPlus) hx hstep_lt
  have hxPlus_mem : xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) := hxPlus_data.1
  have hxPlus : xPlus ∈ dom := hxPlus_data.2
  refine ⟨hxPlus, ?_⟩
  -- Route correction: the standard branch is now isolated to one theorem-local closure helper
  -- with the already verified Dikin-radius data passed in explicitly.
  simpa [xPlus, hH, δ] using
    standardNextPointDecrementBound
      (Mf := Mf) (f := f) (x := x) (xPlus := xPlus) hx hH rfl hxPlus hxPlus_mem
      (by simpa [δ] using hstep_eq)

/-- Helper for Theorem 5.2.2: the damped Newton branch should be proved in determinant-based
normal form before rewriting back to the source-facing `λ` notation. -/
private theorem dampedNextPointMemAndNdecBound
    {x : E} (hx : x ∈ dom) :
    let hH := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx hH
    ∃ hxPlus : xPlus ∈ dom,
      ndec(f, xPlus, (Mf : NNReal), hxPlus,
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus)) ≤
        ((Mf : ℝ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)) *
          (1 + 1 / (1 + (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH))) := by
  let hH : (hessian f x).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (f := f) hx
  let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx hH
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) f hx hH
  have hstep_eq : ‖xPlus - x‖[f; x] = δ / (1 + (Mf : ℝ) * δ) := by
    -- Normalize the damped step size to the textbook rational factor `1 / (1 + M_f δ)`.
    simpa [xPlus, hH, δ, selfConcordantNewtonStepSize, selfConcordantNewtonShift, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
      next_point_sub_localNorm_eq_stepSize_mul_ndec
        (dom := dom) (Mf := Mf) (f := f) .damped hx hH
  have hstep_lt : ‖xPlus - x‖[f; x] < 1 / (Mf : ℝ) := by
    -- The damped rational factor is always strictly below the reciprocal Dikin threshold.
    simpa [hstep_eq] using damped_step_localNorm_lt_inv (Mf := Mf) hδ_nonneg
  have hxPlus_data :
      xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) ∧ xPlus ∈ dom := by
    -- Reuse the common Dikin-radius bridge rather than reopening the same membership argument.
    exact mem_openDikinEllipsoid_and_domain_of_localNorm_lt_inv
      (Mf := Mf) (f := f) (x := x) (y := xPlus) hx hstep_lt
  have hxPlus_mem : xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) := hxPlus_data.1
  have hxPlus : xPlus ∈ dom := hxPlus_data.2
  refine ⟨hxPlus, ?_⟩
  let hHy : (hessian f xPlus).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus
  let α : ℝ := selfConcordantNewtonStepSize f (Mf : NNReal) .damped x hx hH
  let a : ℝ := (Mf : ℝ) * ‖xPlus - x‖[f; x]
  let s : ℝ := (Mf : ℝ) * δ
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδ_nonneg
  have hα_eq : α = 1 / (1 + s) := by
    dsimp [α, s, δ]
    rw [selfConcordantNewtonStepSize]
    simp [selfConcordantNewtonShift]
  have hα_nonneg : 0 ≤ α := by
    rw [hα_eq]
    positivity
  have h1mα_nonneg : 0 ≤ 1 - α := by
    rw [hα_eq]
    have hden_pos : 0 < 1 + s := by positivity
    have hrew : 1 - 1 / (1 + s) = s / (1 + s) := by
      field_simp [hden_pos.ne']
      ring
    rw [hrew]
    exact div_nonneg hs_nonneg (le_of_lt hden_pos)
  have ha_coeff : a = s / (1 + s) := by
    dsimp [a, s]
    rw [hstep_eq]
    ring
  have hlowerCoeff :
      α / (1 - a) - 1 ≤ (1 - α) + α * a := by
    rw [hα_eq, ha_coeff]
    have hden_pos : 0 < 1 + s := by positivity
    field_simp [hden_pos.ne']
    nlinarith [hs_nonneg]
  have hmain :
      ndec(f, xPlus, (Mf : NNReal), hxPlus, hHy) ≤
        (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := by
    -- Route correction: both positive variants now feed one shared endpoint assembly frontier.
    simpa [xPlus, α, a, δ] using
      positiveVariantNextPointAssemblyBound
        (Mf := Mf) (f := f) (variant := .damped) (x := x) (xPlus := xPlus)
        hx hH rfl hxPlus hxPlus_mem rfl hα_nonneg h1mα_nonneg rfl hlowerCoeff
  have hcoeff :
      ((1 - α) / (1 - a) + α * (a / (1 - a))) =
        s * (1 + 1 / (1 + s)) := by
    simpa using dampedStepCoefficientIdentity (s := s) hs_nonneg hα_eq ha_coeff
  calc
    ndec(f, xPlus, (Mf : NNReal), hxPlus, hHy) ≤
        (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := hmain
    _ = (s * (1 + 1 / (1 + s))) * δ := by rw [hcoeff]
    _ = ((Mf : ℝ) * δ ^ (2 : ℕ)) * (1 + 1 / (1 + (Mf : ℝ) * δ)) := by
          dsimp [s]
          ring

/-- Helper for Theorem 5.2.2: the intermediate Newton branch should be proved in determinant-based
normal form before rewriting back to the source-facing `λ` notation. -/
private theorem intermediateNextPointMemAndNdecBounds
    {x : E} (hx : x ∈ dom)
    (hsmall :
      (Mf : ℝ) * λ[f; x | hx] + (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * (λ[f; x | hx]) ^ (3 : ℕ) ≤ 1) :
    let hH := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
    ∃ hxPlus : xPlus ∈ dom,
      (ndec(f, xPlus, (Mf : NNReal), hxPlus,
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus)) ≤
          ((Mf : ℝ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)) *
            (1 + (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH) +
              ((Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH)) /
                (1 + (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH) +
                  (Mf : ℝ) ^ (2 : ℕ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)))) ∧
      (((Mf : ℝ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)) *
            (1 + (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH) +
              ((Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH)) /
                (1 + (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH) +
                  (Mf : ℝ) ^ (2 : ℕ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ))) ≤
          ((Mf : ℝ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ)) *
            (1 + 2 * (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH))) := by
  let hH : (hessian f x).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (f := f) hx
  let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) f hx hH
  have hstep_eq :
      ‖xPlus - x‖[f; x] =
        δ * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
    -- Rewrite the intermediate step size to its textbook rational form before testing the Dikin
    -- radius.
    calc
      ‖xPlus - x‖[f; x] =
          selfConcordantNewtonStepSize f (Mf : NNReal) .intermediate x hx hH * δ := by
            simpa [xPlus, hH, δ] using
              next_point_sub_localNorm_eq_stepSize_mul_ndec
                (dom := dom) (Mf := Mf) (f := f) .intermediate hx hH
      _ =
          ((1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) * δ := by
              rw [intermediate_stepSize_eq
                (dom := dom) (Mf := Mf) (f := f) hx hH]
      _ =
          δ * (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
              field_simp
  have hstep_lt : ‖xPlus - x‖[f; x] < 1 / (Mf : ℝ) := by
    -- The intermediate rational factor also stays strictly below the reciprocal Dikin radius.
    simpa [hstep_eq] using intermediate_step_localNorm_lt_inv
      (Mf := Mf) hδ_nonneg
  have hxPlus_data :
      xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) ∧ xPlus ∈ dom := by
    -- Keep the intermediate branch on the same owner path for endpoint membership.
    exact mem_openDikinEllipsoid_and_domain_of_localNorm_lt_inv
      (Mf := Mf) (f := f) (x := x) (y := xPlus) hx hstep_lt
  have hxPlus_mem : xPlus ∈ W⁰[f; x](1 / (Mf : ℝ)) := hxPlus_data.1
  have hxPlus : xPlus ∈ dom := hxPlus_data.2
  have _hsmall_ndec :
      (Mf : ℝ) * ndec(f, x, (Mf : NNReal), hx, hH) +
          (Mf : ℝ) ^ (2 : ℕ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (2 : ℕ) +
            (Mf : ℝ) ^ (3 : ℕ) * (ndec(f, x, (Mf : NNReal), hx, hH)) ^ (3 : ℕ) ≤ 1 := by
    -- Rewrite the source-facing smallness hypothesis into the determinant-based decrement normal
    -- form used by the private helper theorem.
    simpa [newtonDecrement_eq_ndec_of_mem (Mf := Mf) (f := f) hx] using hsmall
  refine ⟨hxPlus, ?_⟩
  constructor
  · let hHy : (hessian f xPlus).det ≠ 0 :=
        HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hxPlus
    let α : ℝ := selfConcordantNewtonStepSize f (Mf : NNReal) .intermediate x hx hH
    let a : ℝ := (Mf : ℝ) * ‖xPlus - x‖[f; x]
    let s : ℝ := (Mf : ℝ) * δ
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδ_nonneg
    have hα_eq : α = (1 + s) / (1 + s + s ^ (2 : ℕ)) := by
      dsimp [α, s]
      rw [intermediate_stepSize_eq (dom := dom) (Mf := Mf) (f := f) hx hH]
      ring
    have hα_nonneg : 0 ≤ α := by
      rw [hα_eq]
      positivity
    have h1mα_nonneg : 0 ≤ 1 - α := by
      rw [hα_eq]
      have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by positivity
      have hrew :
          1 - (1 + s) / (1 + s + s ^ (2 : ℕ)) =
            s ^ (2 : ℕ) / (1 + s + s ^ (2 : ℕ)) := by
        field_simp [hden_pos.ne']
        ring_nf
      rw [hrew]
      exact div_nonneg (sq_nonneg s) (le_of_lt hden_pos)
    have ha_coeff : a = s * (1 + s) / (1 + s + s ^ (2 : ℕ)) := by
      dsimp [a, s]
      rw [hstep_eq]
      ring
    have hlowerCoeff :
        α / (1 - a) - 1 ≤ (1 - α) + α * a := by
      have hs_small : s + s ^ (2 : ℕ) + s ^ (3 : ℕ) ≤ 1 := by
        dsimp [s]
        simpa [δ, pow_two, pow_succ, mul_assoc, mul_left_comm, mul_comm] using _hsmall_ndec
      have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by positivity
      have hOneSubA : 1 - a = 1 / (1 + s + s ^ (2 : ℕ)) := by
        rw [ha_coeff]
        field_simp [hden_pos.ne']
        ring
      have hlhs : α / (1 - a) - 1 = s := by
        rw [hα_eq, hOneSubA]
        field_simp [hden_pos.ne']
        ring
      have hrhs :
          (1 - α) + α * a =
            s + s ^ (2 : ℕ) * (1 - (s + s ^ (2 : ℕ) + s ^ (3 : ℕ))) /
              (1 + s + s ^ (2 : ℕ)) ^ (2 : ℕ) := by
        rw [hα_eq, ha_coeff]
        field_simp [hden_pos.ne']
        ring
      rw [hlhs, hrhs]
      have hcorrection_nonneg :
          0 ≤
            s ^ (2 : ℕ) * (1 - (s + s ^ (2 : ℕ) + s ^ (3 : ℕ))) /
              (1 + s + s ^ (2 : ℕ)) ^ (2 : ℕ) := by
        have hsmall_nonneg : 0 ≤ 1 - (s + s ^ (2 : ℕ) + s ^ (3 : ℕ)) := by
          linarith
        exact div_nonneg (mul_nonneg (sq_nonneg s) hsmall_nonneg) (sq_nonneg _)
      linarith
    have hmain :
        ndec(f, xPlus, (Mf : NNReal), hxPlus, hHy) ≤
          (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := by
      -- Route correction: the intermediate branch now shares the same endpoint assembly frontier
      -- as the damped branch, and only the scalar simplification is branch-specific.
      simpa [xPlus, α, a, δ] using
        positiveVariantNextPointAssemblyBound
          (Mf := Mf) (f := f) (variant := .intermediate) (x := x) (xPlus := xPlus)
          hx hH rfl hxPlus hxPlus_mem rfl hα_nonneg h1mα_nonneg rfl hlowerCoeff
    have hcoeff :
        ((1 - α) / (1 - a) + α * (a / (1 - a))) =
          s * (1 + s + s / (1 + s + s ^ (2 : ℕ))) := by
      simpa using
        intermediateStepCoefficientIdentity (s := s) hs_nonneg hα_eq ha_coeff
    calc
      ndec(f, xPlus, (Mf : NNReal), hxPlus, hHy) ≤
          (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := hmain
      _ = (s * (1 + s + s / (1 + s + s ^ (2 : ℕ)))) * δ := by rw [hcoeff]
      _ = ((Mf : ℝ) * δ ^ (2 : ℕ)) *
            (1 + (Mf : ℝ) * δ + ((Mf : ℝ) * δ) /
              (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
            dsimp [s]
            ring
  · -- The weaker textbook estimate already follows from the scalar companion proved above.
    have hs_nonneg : 0 ≤ (Mf : ℝ) * δ := by
      exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) hδ_nonneg
    have hfactor :
        1 + (Mf : ℝ) * δ +
            ((Mf : ℝ) * δ) /
              (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) ≤
          1 + 2 * (Mf : ℝ) * δ := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
        intermediate_textbookFactor_le_double (s := (Mf : ℝ) * δ) hs_nonneg
    exact
      mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (sq_nonneg δ))

/-- Standard clause of Theorem 5.2.2: if `x ∈ dom` satisfies `λ_f(x) < 1 / M_f`, then the standard
Newton update stays in `dom`, and its Newton decrement satisfies the bound `(5.2.6)`. -/
theorem selfConcordantNewton_mem_and_decrement_bound_standard
    {x : E} (hx : x ∈ dom) :
    (λ[f; x | hx] < 1 / (Mf : ℝ)) →
      ∃ hxPlus :
          selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
        λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
          ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) /
            (1 - (Mf : ℝ) * λ[f; x | hx]) ^ (2 : ℕ) := by
  intro hlambda
  -- Rewrite the source-facing theorem to the determinant-based helper normal form.
  simpa [newtonDecrement_eq_ndec_of_mem (Mf := Mf) (f := f) hx] using
    standardNextPointMemAndNdecBound (Mf := Mf) (f := f) hx hlambda

/-- Damped clause of Theorem 5.2.2:
the damped Newton update stays in `dom`, and its Newton decrement
satisfies the bound `(5.2.7)`. -/
theorem selfConcordantNewton_mem_and_decrement_bound_damped
    {x : E} (hx : x ∈ dom) :
    ∃ hxPlus :
        selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx
          (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
      λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx
          (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
        ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
          (1 + 1 / (1 + (Mf : ℝ) * λ[f; x | hx])) := by
  -- Rewrite the source-facing theorem to the determinant-based helper normal form.
  simpa [newtonDecrement_eq_ndec_of_mem (Mf := Mf) (f := f) hx] using
    dampedNextPointMemAndNdecBound (Mf := Mf) (f := f) hx

/-- Intermediate clause of Theorem 5.2.2: if the intermediate-step size condition holds, then the
intermediate Newton update stays in `dom`, its Newton decrement satisfies the bound `(5.2.8)`,
and that bound is itself dominated by the simpler quadratic expression from the source text. -/
theorem selfConcordantNewton_mem_and_decrement_bounds_intermediate
    {x : E} (hx : x ∈ dom) :
    ((Mf : ℝ) * λ[f; x | hx] + (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * (λ[f; x | hx]) ^ (3 : ℕ) ≤ 1) →
      ∃ hxPlus :
          selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
        λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
            ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
              (1 + (Mf : ℝ) * λ[f; x | hx] +
                ((Mf : ℝ) * λ[f; x | hx]) /
                  (1 + (Mf : ℝ) * λ[f; x | hx] +
                    (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ))) ∧
          ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
              (1 + (Mf : ℝ) * λ[f; x | hx] +
                ((Mf : ℝ) * λ[f; x | hx]) /
                  (1 + (Mf : ℝ) * λ[f; x | hx] +
                    (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ))) ≤
            ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
              (1 + 2 * (Mf : ℝ) * λ[f; x | hx]) := by
  intro hsmall
  -- Rewrite the source-facing theorem to the determinant-based helper normal form.
  simpa [newtonDecrement_eq_ndec_of_mem (Mf := Mf) (f := f) hx] using
    intermediateNextPointMemAndNdecBounds (Mf := Mf) (f := f) hx hsmall

/-- Theorem 5.2.2: the three Chapter 5 Newton updates satisfy the
source-facing domain-membership and Newton-decrement bounds for the standard, damped, and
intermediate variants. -/
theorem selfConcordantNewton_mem_and_decrement_bounds
    {x : E} (hx : x ∈ dom) :
    let standardBound : Prop :=
      (λ[f; x | hx] < 1 / (Mf : ℝ)) →
        ∃ hxPlus :
            selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx
              (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
          λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx
              (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
            ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) /
              (1 - (Mf : ℝ) * λ[f; x | hx]) ^ (2 : ℕ)
    let dampedBound : Prop :=
      ∃ hxPlus :
          selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
        λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx
            (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
          ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
            (1 + 1 / (1 + (Mf : ℝ) * λ[f; x | hx]))
    let intermediateBound : Prop :=
      ((Mf : ℝ) * λ[f; x | hx] + (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ) +
          (Mf : ℝ) ^ (3 : ℕ) * (λ[f; x | hx]) ^ (3 : ℕ) ≤ 1) →
        ∃ hxPlus :
            selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx
              (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) ∈ dom,
          λ[f; selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx
              (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx) | hxPlus] ≤
              ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
                (1 + (Mf : ℝ) * λ[f; x | hx] +
                  ((Mf : ℝ) * λ[f; x | hx]) /
                    (1 + (Mf : ℝ) * λ[f; x | hx] +
                      (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ))) ∧
            ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
                (1 + (Mf : ℝ) * λ[f; x | hx] +
                  ((Mf : ℝ) * λ[f; x | hx]) /
                    (1 + (Mf : ℝ) * λ[f; x | hx] +
                      (Mf : ℝ) ^ (2 : ℕ) * (λ[f; x | hx]) ^ (2 : ℕ))) ≤
              ((Mf : ℝ) * (λ[f; x | hx]) ^ (2 : ℕ)) *
                (1 + 2 * (Mf : ℝ) * λ[f; x | hx])
    standardBound ∧ dampedBound ∧ intermediateBound := by
  -- Package the three already-proved source clauses under the single label-bearing theorem.
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact selfConcordantNewton_mem_and_decrement_bound_standard (Mf := Mf) (f := f) hx
  · exact selfConcordantNewton_mem_and_decrement_bound_damped (Mf := Mf) (f := f) hx
  · exact selfConcordantNewton_mem_and_decrement_bounds_intermediate (Mf := Mf) (f := f) hx

end SourceFaithfulPublicAPI

end
