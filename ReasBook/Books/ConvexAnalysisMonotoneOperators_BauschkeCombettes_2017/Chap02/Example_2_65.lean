/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54

open InnerProductSpace
open scoped Gradient InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 2.65: on a real Hilbert space, the norm has Fréchet derivative at each nonzero point
`x`, represented by the continuous linear functional corresponding to `x / ‖x‖`. -/
theorem norm_hasFDerivAt {x : H} (hx : x ≠ 0) :
    HasFDerivAt (fun y : H ↦ ‖y‖) (toDual ℝ H (‖x‖⁻¹ • x)) x := by
  have hsq : HasFDerivAt (fun y : H ↦ ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    hasStrictFDerivAt_norm_sq x |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : H ↦ Real.sqrt (‖y‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    hsq.sqrt (by positivity)
  convert hcomp using 1
  · ext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · have hs : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
    rw [hs]
    ext y
    simp
    ring

/-- Example 2.65 in gradient form: the norm has gradient `x / ‖x‖` at each nonzero point `x`. -/
theorem norm_hasGradientAt {x : H} (hx : x ≠ 0) :
    HasGradientAt (fun y : H ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
  simpa using (norm_hasFDerivAt hx).hasGradientAt

/-- The gradient of the norm at a nonzero point is the normalized vector `x / ‖x‖`. -/
theorem gradient_norm {x : H} (hx : x ≠ 0) :
    ∇ (fun y : H ↦ ‖y‖) x = ‖x‖⁻¹ • x :=
  (norm_hasGradientAt hx).gradient

omit [CompleteSpace H] in
/-- The one-sided directional difference quotients of the norm at the origin converge to `‖y‖`. -/
theorem norm_zero_directional_difference_quotient_tendsto (y : H) :
    Filter.Tendsto
      (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
  have hEq :
      (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun _ : ℝ ↦ ‖y‖ := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hαpos : 0 < α := hα
    rw [norm_zero, zero_add, sub_zero, norm_smul, Real.norm_of_nonneg hαpos.le]
    field_simp [hαpos.ne']
  exact tendsto_const_nhds.congr' hEq.symm

omit [CompleteSpace H] in
/-- Example 2.65: the norm is not Gâteaux differentiable at the origin on a nontrivial real
Hilbert space. -/
theorem not_gateauxDifferentiableAt_norm_zero [Nontrivial H] :
    ¬ GateauxDifferentiableAt (fun y : H ↦ ‖y‖) (0 : H) := by
  intro h
  rcases h with ⟨A, hA⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : H)
  have hnorm_y :
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) * (‖(0 : H) + α • y‖ - ‖(0 : H)‖))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
    simpa [one_div, div_eq_mul_inv, mul_comm] using
      norm_zero_directional_difference_quotient_tendsto y
  have hAy : A y = ‖y‖ :=
    tendsto_nhds_unique (hA.tendsto_directionalDifferenceQuotient y) hnorm_y
  have hnorm_neg :
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) * (‖(0 : H) + α • (-y)‖ - ‖(0 : H)‖))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
    simpa [norm_neg, one_div, div_eq_mul_inv, mul_comm] using
      norm_zero_directional_difference_quotient_tendsto (-y)
  have hAneg : A (-y) = ‖y‖ :=
    tendsto_nhds_unique (hA.tendsto_directionalDifferenceQuotient (-y)) hnorm_neg
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have : -‖y‖ = ‖y‖ := by
    calc
      -‖y‖ = A (-y) := by rw [map_neg, hAy]
      _ = ‖y‖ := hAneg
  linarith

omit [CompleteSpace H] in
/-- No continuous linear functional can realize all one-sided directional derivatives of the norm at
the origin on a nontrivial real Hilbert space; equivalently, the norm is not Gâteaux
differentiable there. -/
theorem not_exists_gateauxDerivative_norm_zero [Nontrivial H] :
    ¬ ∃ A : H →L[ℝ] ℝ,
      ∀ y : H,
        Filter.Tendsto
          (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  intro h
  rcases h with ⟨A, hA⟩
  have hnot : ¬ GateauxDifferentiableAt (fun y : H ↦ ‖y‖) (0 : H) :=
    not_gateauxDifferentiableAt_norm_zero
  apply hnot
  refine ⟨A, ?_⟩
  rw [hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient]
  intro y
  simpa [one_div, div_eq_mul_inv, mul_comm] using hA y
