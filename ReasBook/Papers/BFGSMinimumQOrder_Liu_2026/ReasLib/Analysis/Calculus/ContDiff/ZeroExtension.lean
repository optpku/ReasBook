module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

open Filter Set Topology

universe u v

namespace IsClosed

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Decay relative to the distance from a closed set implies decay relative to the
distance from each point of the set. -/
private lemma tendsto_norm_div_norm_sub_of_infDist {Γ : Set E} {Ψ : E → F} {x : E}
    (hΓ : IsClosed Γ) (hx : x ∈ Γ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    Tendsto (fun z ↦ ‖Ψ z‖ / ‖z - x‖) (𝓝[Γᶜ] x) (𝓝 0) := by
  -- Continuity of `infDist` transports the assumed limit to the punctured side of `Γ`.
  have hinfDist : Tendsto (fun z ↦ Metric.infDist z Γ) (𝓝[Γᶜ] x) (𝓝 0) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    simpa only [Metric.infDist_zero_of_mem hx] using
      (Metric.continuous_infDist_pt Γ).tendsto x
  have hrestricted : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (𝓝[Γᶜ] x) (𝓝 0) :=
    hvalue.mono_left (le_inf hinfDist.le_comap inf_le_right)
  -- Outside `Γ`, its infimum distance is positive and no larger than the distance to `x`.
  have hnonneg : ∀ᶠ z in 𝓝[Γᶜ] x, 0 ≤ ‖Ψ z‖ / ‖z - x‖ :=
    Filter.Eventually.of_forall fun z ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ∀ᶠ z in 𝓝[Γᶜ] x,
      ‖Ψ z‖ / ‖z - x‖ ≤ ‖Ψ z‖ / Metric.infDist z Γ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzinfDist : 0 < Metric.infDist z Γ :=
      (hΓ.notMem_iff_infDist_pos ⟨x, hx⟩).mp hz
    refine div_le_div_of_nonneg_left (norm_nonneg _) hzinfDist ?_
    simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := z) hx
  exact squeeze_zero' hnonneg hbound hrestricted

/-- A function extended by zero from the complement of a closed set has zero derivative
at a point of the set when its value is little-o of the distance to the set. -/
private lemma hasFDerivAt_indicator_compl_zero_of_tendsto {Γ : Set E} {Ψ : E → F} {x : E}
    (hΓ : IsClosed Γ) (hx : x ∈ Γ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    HasFDerivAt (Γᶜ.indicator Ψ) (0 : E →L[ℝ] F) x := by
  -- On the complement, the normalized first-order remainder is the quotient just controlled.
  have hcompl : HasFDerivWithinAt (Γᶜ.indicator Ψ) (0 : E →L[ℝ] F) Γᶜ x := by
    rw [hasFDerivWithinAt_iff_tendsto]
    refine Tendsto.congr' ?_
      (tendsto_norm_div_norm_sub_of_infDist hΓ hx hvalue)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hxcompl : x ∉ Γᶜ := by
      simpa only [mem_compl_iff, not_not] using hx
    simp only [indicator_of_mem hz, indicator_of_notMem hxcompl, zero_apply, sub_zero,
      div_eq_inv_mul]
  -- On `Γ` the extension is identically zero, so the two within-derivatives glue globally.
  have hzero : HasFDerivWithinAt (Γᶜ.indicator Ψ) (0 : E →L[ℝ] F) Γ x := by
    refine (hasFDerivWithinAt_zero x Γ).congr' ?_ hx
    intro z hz
    have hzcompl : z ∉ Γᶜ := by
      simpa only [mem_compl_iff, not_not] using hz
    exact indicator_of_notMem hzcompl Ψ
  simpa only [union_compl_self, hasFDerivWithinAt_univ] using hzero.union hcompl

/-- The derivative of the extension by zero off a closed set agrees with the extension of
the derivative when the function is differentiable off the set and decays faster than the
distance to the set. -/
theorem fderiv_indicator_compl (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : DifferentiableOn ℝ Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    fderiv ℝ (Γᶜ.indicator Ψ) = Γᶜ.indicator (fderiv ℝ Ψ) := by
  -- At points of `Γ`, the distance decay gives the zero derivative on both sides.
  funext x
  by_cases hx : x ∈ Γ
  · have hxcompl : x ∉ Γᶜ := by
      simpa only [mem_compl_iff, not_not] using hx
    rw [(hasFDerivAt_indicator_compl_zero_of_tendsto hΓ hx hvalue).fderiv,
      indicator_of_notMem hxcompl]
  · have hxcompl : x ∈ Γᶜ := by
      simpa only [mem_compl_iff] using hx
    have hΨx : DifferentiableAt ℝ Ψ x :=
      (hΨ x hxcompl).differentiableAt (hΓ.compl_mem_nhds hx)
    have hlocal : Γᶜ.indicator Ψ =ᶠ[𝓝 x] Ψ :=
      Filter.eventuallyEq_of_mem (hΓ.compl_mem_nhds hx)
        (fun z hz ↦ indicator_of_mem hz Ψ)
    -- Off `Γ`, openness makes the extension locally equal to `Ψ`.
    have hderiv : HasFDerivAt (Γᶜ.indicator Ψ) (fderiv ℝ Ψ x) x :=
      hΨx.hasFDerivAt.congr_of_eventuallyEq hlocal
    rw [hderiv.fderiv, indicator_of_mem hxcompl]

/-- If a function and its first derivative decay at the required rates toward a closed set,
then the second derivative of its extension by zero is the extension by zero of its second
derivative. -/
theorem fderiv_fderiv_indicator_compl (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    fderiv ℝ (fderiv ℝ (Γᶜ.indicator Ψ)) =
      Γᶜ.indicator (fderiv ℝ (fderiv ℝ Ψ)) := by
  -- Quadratic value decay implies the first-order decay needed for the first extension step.
  have hinfDist : Tendsto (fun z ↦ Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) :=
    tendsto_inf_left tendsto_comap
  have hvalueFirst : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) := by
    have hproduct : Tendsto
        (fun z ↦ (‖Ψ z‖ / Metric.infDist z Γ ^ 2) * Metric.infDist z Γ)
        (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) := by
      simpa only [mul_zero] using hvalue.mul hinfDist
    refine Tendsto.congr' ?_ hproduct
    filter_upwards with z
    by_cases hz : Metric.infDist z Γ = 0
    · simp only [hz, pow_two, mul_zero, div_zero]
    · field_simp
  have hderivDifferentiable : DifferentiableOn ℝ (fderiv ℝ Ψ) Γᶜ :=
    (hΨ.fderiv_of_isOpen hΓ.isOpen_compl (by norm_num)).differentiableOn_one
  -- Apply the first-order extension identity successively to `Ψ` and to its derivative.
  rw [fderiv_indicator_compl Γ Ψ hΓ (hΨ.differentiableOn (by norm_num)) hvalueFirst,
    fderiv_indicator_compl Γ (fderiv ℝ Ψ) hΓ hderivDifferentiable hderiv]

/-- A twice continuously differentiable function off a closed set extends by zero to a
globally twice continuously differentiable function when its value, first derivative, and
second derivative vanish at the corresponding distance-scaled rates. -/
theorem contDiff_two_indicator_compl (Γ : Set E) (Ψ : E → F) (hΓ : IsClosed Γ)
    (hΨ : ContDiffOn ℝ 2 Ψ Γᶜ)
    (hvalue : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hderiv : Tendsto (fun z ↦ ‖fderiv ℝ Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0))
    (hsecond : Tendsto (fun z ↦ ‖fderiv ℝ (fderiv ℝ Ψ) z‖)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0)) :
    ContDiff ℝ 2 (Γᶜ.indicator Ψ) := by
  -- First convert the quadratic value decay to the first-order decay used at points of `Γ`.
  have hinfDist : Tendsto (fun z ↦ Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) :=
    tendsto_inf_left tendsto_comap
  have hvalueFirst : Tendsto (fun z ↦ ‖Ψ z‖ / Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) := by
    have hproduct : Tendsto
        (fun z ↦ (‖Ψ z‖ / Metric.infDist z Γ ^ 2) * Metric.infDist z Γ)
        (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ) (𝓝 0) := by
      simpa only [mul_zero] using hvalue.mul hinfDist
    refine Tendsto.congr' ?_ hproduct
    filter_upwards with z
    by_cases hz : Metric.infDist z Γ = 0
    · simp only [hz, pow_two, mul_zero, div_zero]
    · field_simp
  have hΨDifferentiable : DifferentiableOn ℝ Ψ Γᶜ :=
    hΨ.differentiableOn (by norm_num)
  have hderivContDiff : ContDiffOn ℝ 1 (fderiv ℝ Ψ) Γᶜ :=
    hΨ.fderiv_of_isOpen hΓ.isOpen_compl (by norm_num)
  have hderivDifferentiable : DifferentiableOn ℝ (fderiv ℝ Ψ) Γᶜ :=
    hderivContDiff.differentiableOn_one
  have hsecondContDiff : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ Ψ)) Γᶜ :=
    hderivContDiff.fderiv_of_isOpen hΓ.isOpen_compl (by norm_num)
  -- The value decay supplies differentiability on `Γ`; openness supplies it on the complement.
  have hExtensionDifferentiable : Differentiable ℝ (Γᶜ.indicator Ψ) := by
    intro x
    by_cases hx : x ∈ Γ
    · exact (hasFDerivAt_indicator_compl_zero_of_tendsto hΓ hx hvalueFirst).differentiableAt
    · have hxcompl : x ∈ Γᶜ := by
        simpa only [mem_compl_iff] using hx
      have hlocal : Γᶜ.indicator Ψ =ᶠ[𝓝 x] Ψ :=
        Filter.eventuallyEq_of_mem (hΓ.compl_mem_nhds hx)
          (fun z hz ↦ indicator_of_mem hz Ψ)
      exact ((hΨDifferentiable x hxcompl).differentiableAt
        (hΓ.compl_mem_nhds hx)).congr_of_eventuallyEq hlocal
  -- Apply the same argument to the first derivative.
  have hderivExtensionDifferentiable : Differentiable ℝ (Γᶜ.indicator (fderiv ℝ Ψ)) := by
    intro x
    by_cases hx : x ∈ Γ
    · exact (hasFDerivAt_indicator_compl_zero_of_tendsto hΓ hx hderiv).differentiableAt
    · have hxcompl : x ∈ Γᶜ := by
        simpa only [mem_compl_iff] using hx
      have hlocal : Γᶜ.indicator (fderiv ℝ Ψ) =ᶠ[𝓝 x] fderiv ℝ Ψ :=
        Filter.eventuallyEq_of_mem (hΓ.compl_mem_nhds hx)
          (fun z hz ↦ indicator_of_mem hz (fderiv ℝ Ψ))
      exact ((hderivDifferentiable x hxcompl).differentiableAt
        (hΓ.compl_mem_nhds hx)).congr_of_eventuallyEq hlocal
  have hfderivExtensionDifferentiable :
      Differentiable ℝ (fderiv ℝ (Γᶜ.indicator Ψ)) := by
    rw [fderiv_indicator_compl Γ Ψ hΓ hΨDifferentiable hvalueFirst]
    exact hderivExtensionDifferentiable
  -- The second derivative tends to zero from the complement and is identically zero on `Γ`.
  have hsecondExtensionContinuous :
      Continuous (Γᶜ.indicator (fderiv ℝ (fderiv ℝ Ψ))) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Γ
    · have hxcompl : x ∉ Γᶜ := by
        simpa only [mem_compl_iff, not_not] using hx
      rw [ContinuousAt, indicator_of_notMem hxcompl]
      have hinfDistAt : Tendsto (fun z ↦ Metric.infDist z Γ) (𝓝[Γᶜ] x) (𝓝 0) := by
        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        simpa only [Metric.infDist_zero_of_mem hx] using
          (Metric.continuous_infDist_pt Γ).tendsto x
      have hsecondWithin : Tendsto (fun z ↦ ‖fderiv ℝ (fderiv ℝ Ψ) z‖)
          (𝓝[Γᶜ] x) (𝓝 0) :=
        hsecond.mono_left (le_inf hinfDistAt.le_comap inf_le_right)
      have hsecondVectorWithin : Tendsto (fun z ↦ fderiv ℝ (fderiv ℝ Ψ) z)
          (𝓝[Γᶜ] x) (𝓝 0) := by
        refine (Metric.tendsto_nhds
          (α := E →L[ℝ] E →L[ℝ] F)
          (u := fun z ↦ fderiv ℝ (fderiv ℝ Ψ) z)
          (f := 𝓝[Γᶜ] x) (a := 0)).mpr ?_
        intro ε hε
        filter_upwards [(Metric.tendsto_nhds.mp hsecondWithin ε hε)] with z hz
        have hz' : ‖fderiv ℝ (fderiv ℝ Ψ) z‖ < ε := by
          calc
            ‖fderiv ℝ (fderiv ℝ Ψ) z‖ = ‖(‖fderiv ℝ (fderiv ℝ Ψ) z‖ : ℝ)‖ :=
              (Real.norm_of_nonneg (norm_nonneg
                (fderiv ℝ (fderiv ℝ Ψ) z : E →L[ℝ] E →L[ℝ] F))).symm
            _ = dist (‖fderiv ℝ (fderiv ℝ Ψ) z‖ : ℝ) 0 :=
              (dist_zero_right (‖fderiv ℝ (fderiv ℝ Ψ) z‖ : ℝ)).symm
            _ < ε := hz
        calc
          dist (fderiv ℝ (fderiv ℝ Ψ) z) 0 = ‖fderiv ℝ (fderiv ℝ Ψ) z‖ :=
            dist_zero_right (fderiv ℝ (fderiv ℝ Ψ) z : E →L[ℝ] E →L[ℝ] F)
          _ < ε := hz'
      have hcompl : Tendsto (Γᶜ.indicator (fderiv ℝ (fderiv ℝ Ψ)))
          (𝓝[Γᶜ] x) (𝓝 0) := by
        refine Tendsto.congr' ?_ hsecondVectorWithin
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (indicator_of_mem hz (fderiv ℝ (fderiv ℝ Ψ))).symm
      have hzero : Tendsto (Γᶜ.indicator (fderiv ℝ (fderiv ℝ Ψ)))
          (𝓝[Γ] x) (𝓝 0) := by
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hzcompl : z ∉ Γᶜ := by
          simpa only [mem_compl_iff, not_not] using hz
        exact (indicator_of_notMem hzcompl (fderiv ℝ (fderiv ℝ Ψ))).symm
      rw [← nhdsWithin_univ x, ← union_compl_self Γ, nhdsWithin_union]
      exact tendsto_sup.mpr ⟨hzero, hcompl⟩
    · have hxcompl : x ∈ Γᶜ := by
        simpa only [mem_compl_iff] using hx
      have hlocal : Γᶜ.indicator (fderiv ℝ (fderiv ℝ Ψ)) =ᶠ[𝓝 x]
          fderiv ℝ (fderiv ℝ Ψ) :=
        Filter.eventuallyEq_of_mem (hΓ.compl_mem_nhds hx)
          (fun z hz ↦ indicator_of_mem hz (fderiv ℝ (fderiv ℝ Ψ)))
      exact (hsecondContDiff.continuousOn.continuousAt
        (hΓ.compl_mem_nhds hx)).congr_of_eventuallyEq hlocal
  -- The two derivative identities reduce the global `C²` criterion to these three facts.
  have htwo : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [htwo, contDiff_succ_iff_fderiv]
  refine ⟨hExtensionDifferentiable, ?_, ?_⟩
  · norm_num
  · refine contDiff_one_iff_fderiv.mpr ⟨hfderivExtensionDifferentiable, ?_⟩
    rw [fderiv_fderiv_indicator_compl Γ Ψ hΓ hΨ hvalue hderiv]
    exact hsecondExtensionContinuous

end IsClosed
