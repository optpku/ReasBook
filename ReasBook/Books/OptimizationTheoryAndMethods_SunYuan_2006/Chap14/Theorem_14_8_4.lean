/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Exercise_14_13
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_8_2

noncomputable section

open Filter
open scoped GeneralizedJacobian

section Chapter14Theorem1484

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "JacobianMap" => Point →L[ℝ] Point

-- Domain-style sampling:
-- * primary domain: semismooth generalized-Newton convergence on closed balls in Euclidean space
-- * core/canonical owner reused here for semismooth directional data:
--   `SemismoothAt` and its derived common-limit theorem
--   `SemismoothAt.existsCommonLimit` from `Definition_14_8_extra_2`
-- * core/canonical owner reused here for the closed-ball convergence data:
--   `HasGeneralizedNewtonClosedBallConvergenceAssumptions` from `Exercise_14_13`
-- * core/canonical owner reused here for closed-ball uniqueness:
--   `IsUniqueZeroOnClosedBall` from `Exercise_14_13`
-- * source-facing semismooth Newton method owner reused here:
--   `NonsmoothNewtonMethod` from `Algorithm_14_8_extra_5`
-- * layer used here:
--   source-facing closed-ball semismooth Newton assumptions on top of the canonical owners above
-- * primitive data kept here:
--   semismoothness on the closed ball and the chosen linearization-limit data for `semideriv`
-- * derived API kept here:
--   the semismooth difference-quotient limit and the closed-ball convergence consequences

/-- The global-convergence assumptions from Chapter14 Theorem 14.8.4 on the closed ball
`S = Metric.closedBall x0 r`: `F` is semismooth on `S`, `semideriv x h` realizes the common
semismooth directional derivative `F'(x; h)`, every selected generalized-Jacobian element is
nonsingular with inverse norm bounded by `β`, the source linearization and remainder estimates
hold with constants `γ` and `δ`, and the contraction quantity `β * (γ + δ)` is strictly less
than `1` with the initial residual bound `β * ‖F x0‖ ≤ r * (1 - β * (γ + δ))`. -/
structure HasSemismoothNewtonGlobalConvergenceAssumptions
    (F : Point → Point) (semideriv : Point → Point → Point)
    (x0 : Point) (r β γ δ : ℝ) : Prop
    extends HasGeneralizedNewtonClosedBallConvergenceAssumptions
      F semideriv x0 r β γ δ where
  semismoothOn (x : Point) (_ : x ∈ Metric.closedBall x0 r) : SemismoothAt F x
  linearization_limit (x : Point) (_ : x ∈ Metric.closedBall x0 r) (h : Point) :
    hasSemismoothLinearizationLimit F x h (semideriv x h)

namespace HasSemismoothNewtonGlobalConvergenceAssumptions

private theorem semismoothSelectionFilter_neBot
    {F : Point → Point} {semideriv : Point → Point → Point} {x0 : Point}
    {r β γ δ : ℝ}
    (h_assumptions : HasSemismoothNewtonGlobalConvergenceAssumptions
      F semideriv x0 r β γ δ)
    (x : Point) (hx : x ∈ Metric.closedBall x0 r) (h : Point) :
    NeBot (semismoothSelectionFilter F x h) := by
  let h_semismooth := h_assumptions.semismoothOn x hx
  have h_local : LocallyLipschitzAt F x := h_semismooth.toLocallyLipschitzAt
  have h_nonsingular :
      ∀ ⦃V : JacobianMap⦄, V ∈ (∂ F) x → V.IsInvertible := fun _ hV ↦
    h_assumptions.jacobian_isInvertible hx hV
  obtain ⟨ρ, hρ_pos, _, h_ball⟩ :=
    exists_ball_bound_of_generalizedJacobian_nonsingularAt F x h_local h_nonsingular
  have h_base : NeBot (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact (show NeBot (nhds h) by infer_instance).prod (nhdsWithin_Ioi_neBot le_rfl)
  have h_step :
      Tendsto (fun p : Point × ℝ ↦ x + p.2 • p.1)
        (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
    have ht0 :
        Tendsto (fun p : Point × ℝ ↦ p.2)
          (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have h_smul :
        Tendsto (fun p : Point × ℝ ↦ p.2 • p.1)
          (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) • h)) :=
      ht0.smul tendsto_fst
    simpa using tendsto_const_nhds.add h_smul
  have h_image_mem :
      (fun p : JacobianMap × Point × ℝ ↦ (p.2.1, p.2.2)) ''
          {p | p.1 ∈ (∂ F) (x + p.2.2 • p.2.1)} ∈
        nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_of_superset (h_step <| Metric.ball_mem_nhds x hρ_pos) ?_
    intro q hq
    rcases (h_ball hq).1 with ⟨V, hV⟩
    exact ⟨(V, q.1, q.2), hV, rfl⟩
  simpa [semismoothSelectionFilter, inf_comm] using
    Filter.comap_inf_principal_neBot_of_image_mem h_base h_image_mem

/-- On the closed ball of Chapter14 Theorem 14.8.4, the chosen semiderivative also realizes the
corresponding semismooth difference-quotient limit. This is derived from the canonical
semismooth common-limit theorem, so it is not stored as primitive data in the owner above. -/
theorem differenceQuotient_tendsto
    {F : Point → Point} {semideriv : Point → Point → Point} {x0 : Point}
    {r β γ δ : ℝ}
    (h_assumptions : HasSemismoothNewtonGlobalConvergenceAssumptions
      F semideriv x0 r β γ δ)
    (x : Point) (hx : x ∈ Metric.closedBall x0 r) (h : Point) :
    Tendsto (semismoothDifferenceQuotient F x)
      (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (semideriv x h)) := by
  letI := semismoothSelectionFilter_neBot h_assumptions x hx h
  rcases (h_assumptions.semismoothOn x hx).existsCommonLimit with
    ⟨l, h_common_limit, h_difference_limit⟩
  have h_linearization_limit := h_assumptions.linearization_limit x hx h
  have hl : l = semideriv x h := by
    simpa [hasSemismoothLinearizationLimit] using
      tendsto_nhds_unique h_common_limit h_linearization_limit
  simpa [hl] using h_difference_limit

end HasSemismoothNewtonGlobalConvergenceAssumptions

variable (method : NonsmoothNewtonMethod n) (semideriv : Point → Point → Point)
variable (r β γ δ : ℝ)
variable (h_assumptions :
  HasSemismoothNewtonGlobalConvergenceAssumptions
    method.map semideriv method.initialPoint r β γ δ)

include semideriv β γ δ h_assumptions

/-- Helper for Chapter14 Theorem 14.8.4: if the semismooth Newton iterates converge to a limit
inside the admissible closed ball, then that limit is a zero of `method.map`. -/
lemma semismoothNewtonLimitMap_eq_zero
    {xStar : Point}
    (hxStar : xStar ∈ Metric.closedBall method.initialPoint r)
    (h_tendsto : Tendsto method.iterate atTop (nhds xStar)) :
    method.map xStar = 0 := by
  let q : ℝ := β * (γ + δ)
  let C : ℝ := β * ‖method.map method.initialPoint‖
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg h_assumptions.beta_nonneg
      (add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg)
  have hstep_geometric :
      ∀ k : ℕ, ‖method.iterate (k + 1) - method.iterate k‖ ≤ q ^ k * C := by
    intro k
    -- Reuse the closed-ball geometric-step estimate inherited from Exercise 14.13.
    simpa [q, C] using
      (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).2
  have hresidual_geometric :
      ∀ k : ℕ, ‖method.map (method.iterate (k + 1))‖ ≤ ((γ + δ) * C) * q ^ k := by
    intro k
    have hk_mem :
        method.iterate k ∈ Metric.closedBall method.initialPoint r := by
      exact
        (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
          (method := method) (semideriv := semideriv)
          (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).1
    have hk1_mem :
        method.iterate (k + 1) ∈ Metric.closedBall method.initialPoint r := by
      exact
        (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
          (method := method) (semideriv := semideriv)
          (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions (k + 1)).1
    have hk_residual :
        ‖method.map (method.iterate (k + 1))‖ ≤
          (γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖ := by
      -- The next residual is controlled by the current Newton step inside the admissible ball.
      simpa using
        generalizedNewtonStep_map_norm_le_ofClosedBallConvergenceAssumptions
          (method := method) (semideriv := semideriv)
          (r := r) (β := β) (γ := γ) (δ := δ)
          h_assumptions hk_mem hk1_mem (method.selectedOperator_mem_at k)
          (method.iterate_succ_eq_generalizedNewtonStep k)
    have hgd_nonneg : 0 ≤ γ + δ :=
      add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg
    calc
      ‖method.map (method.iterate (k + 1))‖ ≤
          (γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖ :=
        hk_residual
      _ ≤ (γ + δ) * (q ^ k * C) :=
        mul_le_mul_of_nonneg_left (hstep_geometric k) hgd_nonneg
      _ = ((γ + δ) * C) * q ^ k := by
        ring
  have hpow_tendsto_zero :
      Tendsto (fun k : ℕ ↦ q ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg h_assumptions.contraction_lt_one
  have hupper_tendsto_zero :
      Tendsto (fun k : ℕ ↦ ((γ + δ) * C) * q ^ k) atTop (nhds 0) := by
    -- A fixed coefficient preserves convergence of the geometric majorant to `0`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Filter.Tendsto.const_mul ((γ + δ) * C) hpow_tendsto_zero)
  have hresidual_tendsto_zero :
      Tendsto (fun k : ℕ ↦ ‖method.map (method.iterate (k + 1))‖) atTop (nhds 0) := by
    -- Squeeze the residual norms between `0` and the geometric majorant.
    refine squeeze_zero (fun k ↦ norm_nonneg _) hresidual_geometric hupper_tendsto_zero
  have h_cont : ContinuousAt method.map xStar := by
    let h_semismooth := h_assumptions.semismoothOn xStar hxStar
    rcases locallyLipschitzAt_iff.mp h_semismooth.toLocallyLipschitzAt with ⟨ε, hε, K, hK⟩
    -- Local Lipschitz regularity on a closed ball gives continuity at the limit point.
    exact hK.continuousOn.continuousAt (Metric.closedBall_mem_nhds xStar hε)
  have hshift_tendsto :
      Tendsto (fun k : ℕ ↦ method.iterate (k + 1)) atTop (nhds xStar) := by
    -- Reindex the convergent iterate sequence by one step.
    exact h_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have hnorm_tendsto_limit :
      Tendsto (fun k : ℕ ↦ ‖method.map (method.iterate (k + 1))‖)
        atTop (nhds ‖method.map xStar‖) := by
    -- Continuity transports the iterate limit through `method.map`, then through the norm.
    exact continuous_norm.continuousAt.tendsto.comp (h_cont.tendsto.comp hshift_tendsto)
  have hnorm_eq_zero : ‖method.map xStar‖ = 0 :=
    tendsto_nhds_unique hnorm_tendsto_limit hresidual_tendsto_zero
  exact norm_eq_zero.mp hnorm_eq_zero

/-- Helper for Chapter14 Theorem 14.8.4: any zero of `method.map` inside the admissible closed
ball coincides with the distinguished limit point `xStar`. -/
lemma closedBall_eq_of_map_eq_zero
    {xStar y : Point}
    (hxStar : xStar ∈ Metric.closedBall method.initialPoint r)
    (hy : y ∈ Metric.closedBall method.initialPoint r)
    (hxStar_zero : method.map xStar = 0)
    (hy_zero : method.map y = 0) :
    y = xStar := by
  let q : ℝ := β * (γ + δ)
  let h_semismooth := h_assumptions.semismoothOn xStar hxStar
  rcases locallyLipschitzAt_iff.mp h_semismooth.toLocallyLipschitzAt with ⟨ε, hε, K, hK⟩
  have hxStar_ball : xStar ∈ Metric.ball xStar (ε / 2) := by
    exact Metric.mem_ball_self (half_pos hε)
  obtain ⟨V, hV⟩ :=
    generalizedJacobianNonempty_of_closedBallLipschitzNear
      (F := method.map) (x := xStar) (ε := ε) (K := K) hε hK hxStar_ball
  let hVInv := h_assumptions.jacobian_isInvertible hxStar hV
  have h_linearization :
      ‖V (y - xStar) - semideriv xStar (y - xStar)‖ ≤ γ * ‖y - xStar‖ :=
    h_assumptions.linearization_bound hxStar hy hV
  have h_remainder :
      ‖method.map y - method.map xStar - semideriv xStar (y - xStar)‖ ≤
        δ * ‖y - xStar‖ :=
    h_assumptions.remainder_bound hxStar hy
  have h_expand :
      V (y - xStar) =
        (V (y - xStar) - semideriv xStar (y - xStar)) -
          (method.map y - method.map xStar - semideriv xStar (y - xStar)) := by
    -- Normalize the defect to the two source estimates centered at `xStar`.
    rw [hy_zero, hxStar_zero]
    abel
  have h_defect :
      ‖V (y - xStar)‖ ≤ (γ + δ) * ‖y - xStar‖ := by
    -- Combine the linearization error and the nonlinear remainder.
    calc
      ‖V (y - xStar)‖
          = ‖(V (y - xStar) - semideriv xStar (y - xStar)) -
              (method.map y - method.map xStar - semideriv xStar (y - xStar))‖ := by
                rw [h_expand]
      _ ≤ ‖V (y - xStar) - semideriv xStar (y - xStar)‖ +
            ‖method.map y - method.map xStar - semideriv xStar (y - xStar)‖ :=
          norm_sub_le _ _
      _ ≤ γ * ‖y - xStar‖ + δ * ‖y - xStar‖ :=
          add_le_add h_linearization h_remainder
      _ = (γ + δ) * ‖y - xStar‖ := by
          ring
  have hq_le : q * ‖y - xStar‖ < ‖y - xStar‖ := by
    have hnorm_nonneg : 0 ≤ ‖y - xStar‖ := norm_nonneg _
    nlinarith [h_assumptions.contraction_lt_one]
  have hnorm_le :
      ‖y - xStar‖ ≤ q * ‖y - xStar‖ := by
    -- Apply the inverse bound to transport the defect estimate back to `y - xStar`.
    calc
      ‖y - xStar‖ = ‖V.inverse (V (y - xStar))‖ := by
        rw [hVInv.inverse_apply_self]
      _ ≤ ‖V.inverse‖ * ‖V (y - xStar)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * ‖V (y - xStar)‖ :=
        mul_le_mul_of_nonneg_right (h_assumptions.inverse_bound hxStar hV) (norm_nonneg _)
      _ ≤ β * ((γ + δ) * ‖y - xStar‖) :=
        mul_le_mul_of_nonneg_left h_defect h_assumptions.beta_nonneg
      _ = q * ‖y - xStar‖ := by
        dsimp [q]
        ring
  have hnorm_zero : ‖y - xStar‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖y - xStar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/-- Helper for Chapter14 Theorem 14.8.4: each new Newton step is bounded by the previous step
times the contraction factor `β * (γ + δ)`. -/
lemma semismoothNewton_stepNorm_le_contraction
    (k : ℕ) :
    ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤
      (β * (γ + δ)) * ‖method.iterate (k + 1) - method.iterate k‖ := by
  have hk_mem :
      method.iterate k ∈ Metric.closedBall method.initialPoint r := by
    exact
      (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).1
  have hk1_mem :
      method.iterate (k + 1) ∈ Metric.closedBall method.initialPoint r := by
    exact
      (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions (k + 1)).1
  have hk1_residual :
      ‖method.map (method.iterate (k + 1))‖ ≤
        (γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖ := by
    -- The residual recursion is available because both consecutive iterates stay in the ball.
    simpa using
      generalizedNewtonStep_map_norm_le_ofClosedBallConvergenceAssumptions
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ)
        h_assumptions hk_mem hk1_mem (method.selectedOperator_mem_at k)
        (method.iterate_succ_eq_generalizedNewtonStep k)
  have hk1_step_raw :
      ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤
        β * ‖method.map (method.iterate (k + 1))‖ := by
    -- The inverse bound controls the next Newton step by the current residual.
    have h_step_bound :
        ∀ {x : Point} (hx : x ∈ Metric.closedBall method.initialPoint r)
          {V : Point →L[ℝ] Point} (hV : V ∈ generalizedJacobian method.map x),
          ‖generalizedNewtonStep method.map x V (h_assumptions.jacobian_isInvertible hx hV) - x‖ ≤
            β * ‖method.map x‖ := by
      intro x hx V hV
      let hVInv := h_assumptions.jacobian_isInvertible hx hV
      calc
        ‖generalizedNewtonStep method.map x V hVInv - x‖
            = ‖-V.inverse (method.map x)‖ := by
                simp [generalizedNewtonStep_eq, sub_eq_add_neg, add_left_comm, add_comm]
        _ = ‖V.inverse (method.map x)‖ := by
              rw [norm_neg]
        _ ≤ ‖V.inverse‖ * ‖method.map x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ β * ‖method.map x‖ :=
          mul_le_mul_of_nonneg_right (h_assumptions.inverse_bound hx hV) (norm_nonneg _)
    simpa [method.iterate_succ_eq_generalizedNewtonStep] using
      h_step_bound hk1_mem (method.selectedOperator_mem_at (k + 1))
  have hgd_nonneg : 0 ≤ γ + δ :=
    add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg
  -- Combine the inverse bound with the residual recursion.
  calc
    ‖method.iterate (k + 2) - method.iterate (k + 1)‖ ≤
        β * ‖method.map (method.iterate (k + 1))‖ :=
      hk1_step_raw
    _ ≤ β * ((γ + δ) * ‖method.iterate (k + 1) - method.iterate k‖) :=
      mul_le_mul_of_nonneg_left hk1_residual h_assumptions.beta_nonneg
    _ = (β * (γ + δ)) * ‖method.iterate (k + 1) - method.iterate k‖ := by
      ring

/-- Helper for Chapter14 Theorem 14.8.4: every future Newton step is controlled geometrically by
the previous step `‖x_k - x_(k-1)‖` once `k ≥ 1`. -/
lemma semismoothNewton_futureStepNorm_le_geomFromPrev
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ j : ℕ,
      ‖method.iterate (k + j + 1) - method.iterate (k + j)‖ ≤
        (β * (γ + δ)) ^ (j + 1) * ‖method.iterate k - method.iterate (k - 1)‖ := by
  let q : ℝ := β * (γ + δ)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg h_assumptions.beta_nonneg
      (add_nonneg h_assumptions.gamma_nonneg h_assumptions.delta_nonneg)
  intro j
  induction j with
  | zero =>
      -- The first tail step is exactly the one-step contraction at stage `k - 1`.
      have hk_pos : 0 < k := hk
      have hk_prev : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hk_prev_comm : 1 + (k - 1) = k := by
        simpa [Nat.add_comm] using hk_prev
      have hk_succ : k - 1 + 2 = k + 1 := by
        have hk_prev_add := congrArg (fun t : ℕ ↦ t + 1) hk_prev
        simpa [Nat.add_assoc] using hk_prev_add
      simpa [q, hk_prev, hk_prev_comm, hk_succ] using
        semismoothNewton_stepNorm_le_contraction
          (method := method) (semideriv := semideriv)
          (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions (k - 1)
  | succ j hj =>
      -- Iterate the one-step contraction and fold the powers together.
      calc
        ‖method.iterate (k + (j + 1) + 1) - method.iterate (k + (j + 1))‖
            ≤ q * ‖method.iterate (k + j + 1) - method.iterate (k + j)‖ := by
                simpa [q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  semismoothNewton_stepNorm_le_contraction
                    (method := method) (semideriv := semideriv)
                    (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions (k + j)
        _ ≤ q * (q ^ (j + 1) * ‖method.iterate k - method.iterate (k - 1)‖) :=
          mul_le_mul_of_nonneg_left hj hq_nonneg
        _ = q ^ (j + 2) * ‖method.iterate k - method.iterate (k - 1)‖ := by
          rw [pow_succ']
          ring

/-- Part (1) of Chapter14 Theorem 14.8.4: under the global-convergence assumptions on
`S = Metric.closedBall method.initialPoint r`, every semismooth Newton iterate of `method`
remains in `S`. -/
theorem semismoothNewton_iterates_mem_closedBall
    (k : ℕ) :
    method.iterate k ∈ Metric.closedBall method.initialPoint r := by
  -- This is exactly the invariant-ball part of the imported closed-ball convergence package.
  simpa using
    (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
      (method := method) (semideriv := semideriv)
      (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).1

/-- Chapter14 Theorem 14.8.4: under the same assumptions, the semismooth Newton iterates
of `method` converge to the unique solution `x* ∈ S` of `method.map x* = 0`. The closed-ball
uniqueness conclusion reuses the canonical owner
`IsUniqueZeroOnClosedBall method.map method.initialPoint r xStar`. -/
theorem semismoothNewton_existsUniqueRoot_tendsto
    :
    ∃ xStar : Point,
      IsUniqueZeroOnClosedBall method.map method.initialPoint r xStar ∧
        Tendsto method.iterate atTop (nhds xStar) := by
  let q : ℝ := β * (γ + δ)
  let C : ℝ := β * ‖method.map method.initialPoint‖
  have hstep_geometric :
      ∀ k : ℕ, dist (method.iterate k) (method.iterate (k + 1)) ≤ C * q ^ k := by
    intro k
    have hk_step :
        ‖method.iterate (k + 1) - method.iterate k‖ ≤ q ^ k * C := by
      simpa [q, C] using
        (iterate_mem_closedBall_and_step_norm_le_geom_ofClosedBallConvergenceAssumptions
          (method := method) (semideriv := semideriv)
          (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k).2
    -- Rewrite the geometric step estimate into the metric form expected by the Cauchy lemma.
    calc
      dist (method.iterate k) (method.iterate (k + 1))
          = ‖method.iterate (k + 1) - method.iterate k‖ := by
              rw [dist_eq_norm, norm_sub_rev]
      _ ≤ q ^ k * C := hk_step
      _ = C * q ^ k := by
          ring
  have h_iterate_cauchy : CauchySeq method.iterate := by
    -- Geometric control of successive differences makes the iterate sequence Cauchy.
    simpa [q, C] using
      cauchySeq_of_le_geometric (f := method.iterate) q C h_assumptions.contraction_lt_one
        hstep_geometric
  rcases cauchySeq_tendsto_of_complete h_iterate_cauchy with ⟨xStar, h_tendsto⟩
  have hxStar :
      xStar ∈ Metric.closedBall method.initialPoint r := by
    -- The closed ball is closed, so it contains the limit of the iterate sequence.
    refine IsClosed.mem_of_tendsto Metric.isClosed_closedBall h_tendsto ?_
    exact Filter.Eventually.of_forall
      (semismoothNewton_iterates_mem_closedBall
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions)
  have hxStar_zero : method.map xStar = 0 :=
    semismoothNewtonLimitMap_eq_zero
      (method := method) (semideriv := semideriv)
      (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions hxStar h_tendsto
  refine ⟨xStar, ?_, h_tendsto⟩
  refine
    { mem_closedBall := hxStar
      map_eq_zero := hxStar_zero
      eq_of_mem_closedBall_of_map_eq_zero := ?_ }
  intro y hy hy_zero
  -- Uniqueness of zeros on the closed ball is isolated in the dedicated helper.
  exact
    closedBall_eq_of_map_eq_zero
      (method := method) (semideriv := semideriv)
      (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions hxStar hy hxStar_zero hy_zero

/-- Part (3) of Chapter14 Theorem 14.8.4: if `x*` is the unique root of `method.map` on
`S = Metric.closedBall method.initialPoint r`, then the semismooth Newton iterates of `method`
converge to `x*` by part `(2)`, and the error estimate `(14.8.22)` holds:
`‖x k - x*‖ ≤ [β * (γ + δ) / (1 - β * (γ + δ))] * ‖x k - x (k - 1)‖` for every `k ≥ 1`. -/
theorem semismoothNewton_errorEstimate
    (xStar : Point)
    (h_root : IsUniqueZeroOnClosedBall method.map method.initialPoint r xStar)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖method.iterate k - xStar‖ ≤
      (β * (γ + δ) / (1 - β * (γ + δ))) * ‖method.iterate k - method.iterate (k - 1)‖ := by
  let q : ℝ := β * (γ + δ)
  have h_tendsto :
      Tendsto method.iterate atTop (nhds xStar) := by
    rcases semismoothNewton_existsUniqueRoot_tendsto
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions with
      ⟨xLimit, h_limit_root, h_limit_tendsto⟩
    have hxStar_eq : xStar = xLimit :=
      IsUniqueZeroOnClosedBall.eq_of_map_eq_zero
        h_limit_root h_root.mem_closedBall h_root.map_eq_zero
    -- Route correction: reuse the existence/uniqueness theorem instead of rebuilding the limit.
    simpa [hxStar_eq] using h_limit_tendsto
  let u : ℕ → Point := fun j ↦ method.iterate (k + j)
  let C : ℝ := q * ‖method.iterate k - method.iterate (k - 1)‖
  have hu_tendsto : Tendsto u atTop (nhds xStar) := by
    -- Shift the convergent iterate sequence so it starts at the requested index `k`.
    have hshift :
        Tendsto (fun j : ℕ ↦ method.iterate (j + k)) atTop (nhds xStar) :=
      h_tendsto.comp (Filter.tendsto_add_atTop_nat k)
    convert hshift using 1
    ext j
    rw [Nat.add_comm]
  have hstep_geometric :
      ∀ j : ℕ, dist (u j) (u (j + 1)) ≤ C * q ^ j := by
    intro j
    have hj :
        ‖method.iterate (k + j + 1) - method.iterate (k + j)‖ ≤
          q ^ (j + 1) * ‖method.iterate k - method.iterate (k - 1)‖ :=
      semismoothNewton_futureStepNorm_le_geomFromPrev
        (method := method) (semideriv := semideriv)
        (r := r) (β := β) (γ := γ) (δ := δ) h_assumptions k hk j
    -- Rewrite the tail-step estimate into the geometric metric form expected by the tail bound.
    calc
      dist (u j) (u (j + 1))
          = ‖method.iterate (k + j + 1) - method.iterate (k + j)‖ := by
              simp [u, dist_eq_norm, Nat.add_assoc, norm_sub_rev]
      _ ≤ q ^ (j + 1) * ‖method.iterate k - method.iterate (k - 1)‖ := hj
      _ = C * q ^ j := by
          dsimp [C]
          rw [pow_succ']
          ring
  -- Apply the standard geometric-tail estimate at the shifted sequence `u`.
  calc
    ‖method.iterate k - xStar‖ = dist (u 0) xStar := by
      simp [u, dist_eq_norm]
    _ ≤ C * q ^ 0 / (1 - q) := by
      simpa [u, C, q] using
        dist_le_of_le_geometric_of_tendsto
          (f := u) q C h_assumptions.contraction_lt_one hstep_geometric hu_tendsto 0
    _ = (β * (γ + δ) / (1 - β * (γ + δ))) *
          ‖method.iterate k - method.iterate (k - 1)‖ := by
          dsimp [C, q]
          rw [pow_zero, mul_one, div_eq_mul_inv, div_eq_mul_inv]
          ring

end Chapter14Theorem1484
