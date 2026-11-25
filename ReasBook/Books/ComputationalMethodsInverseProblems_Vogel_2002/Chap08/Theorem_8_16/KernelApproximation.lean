/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.Mollification
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.IntegralKernelCompactness
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Convolution Topology BoundedContinuousFunction NNReal
namespace VariationalRegularization.BVCompactness
namespace KernelApproximation
variable {d : ℕ}
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Output (Ω : TopologicalSpace.Opens (Space d)) := {x : Space d // x ∈ closure (Ω : Set (Space d))}

lemma domainMeasure_le_volume (Ω : TopologicalSpace.Opens (Space d)) : domainMeasure Ω ≤ volume := by
  simpa only [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
    (Measure.restrict_le_self (μ := (volume : Measure (Space d))) (s := (Ω : Set (Space d))))

@[expose] def restrictLp (Ω : TopologicalSpace.Opens (Space d))
    (f : Space d → ℝ) (hf : Integrable f) : Lp ℝ 1 (domainMeasure Ω) :=
  (memLp_one_iff_integrable.2 (hf.mono_measure (domainMeasure_le_volume Ω))).toLp f

lemma restrictLp_ae (Ω : TopologicalSpace.Opens (Space d))
    (f : Space d → ℝ) (hf : Integrable f) : restrictLp Ω f hf =ᵐ[domainMeasure Ω] f := by
  simpa only [restrictLp] using
    (memLp_one_iff_integrable.2 (hf.mono_measure (domainMeasure_le_volume Ω))).coeFn_toLp

lemma dist_restrictLp_eq_integral (Ω : TopologicalSpace.Opens (Space d))
    (u : Lp ℝ 1 (domainMeasure Ω)) {f g : Space d → ℝ} (hg : Integrable g)
    (hu : u =ᵐ[domainMeasure Ω] f) :
    dist u (restrictLp Ω g hg) = ∫ x, ‖f x - g x‖ ∂domainMeasure Ω := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u (restrictLp Ω g hg), hu, restrictLp_ae Ω g hg]
    with x hx huf hgf
  simp only [hx, Pi.sub_apply, huf, hgf]

lemma dist_restrictLp_le_integral (Ω : TopologicalSpace.Opens (Space d))
    (u : Lp ℝ 1 (domainMeasure Ω)) {f g : Space d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hu : u =ᵐ[domainMeasure Ω] f) :
    dist u (restrictLp Ω g hg) ≤ ∫ x, ‖f x - g x‖ := by
  rw [dist_restrictLp_eq_integral Ω u hg hu]
  exact integral_mono_measure (domainMeasure_le_volume Ω) (.of_forall fun x ↦ norm_nonneg _) (hf.sub hg).norm

lemma dist_restrictLp_le_uniform (Ω : TopologicalSpace.Opens (Space d))
    [IsFiniteMeasure (domainMeasure Ω)] {f g : Space d → ℝ} (hf : Integrable f) (hg : Integrable g)
    {B : ℝ} (hB : ∀ x ∈ (Ω : Set (Space d)), ‖f x - g x‖ ≤ B) :
    dist (restrictLp Ω f hf) (restrictLp Ω g hg) ≤ (domainMeasure Ω univ).toReal * B := by
  rw [dist_restrictLp_eq_integral Ω _ hg (restrictLp_ae Ω f hf)]
  have ha : ∀ᵐ x ∂domainMeasure Ω, x ∈ (Ω : Set (Space d)) := by
    simpa only [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
      (ae_restrict_mem Ω.2.measurableSet : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)), x ∈ (Ω : Set (Space d)))
  have hb := integral_mono_ae ((hf.sub hg).norm.mono_measure (domainMeasure_le_volume Ω))
    (integrable_const B) (ha.mono fun x hx ↦ hB x hx)
  simpa [measureReal_def] using hb

/-- A fixed smooth compactly supported kernel has finite `L¹(Ω)` nets on every
ambient `L¹` ball. The net centers come from the Arzelà–Ascoli image itself. -/
theorem finiteApprox (Ω : TopologicalSpace.Opens (Space d))
    [IsFiniteMeasure (domainMeasure Ω)] (hΩ : Bornology.IsBounded (Ω : Set (Space d)))
    {ρ : Space d → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set (Lp ℝ 1 (domainMeasure Ω)), t.Finite ∧
      ∀ (f : Space d → ℝ) (hf : Integrable f), (∫ x, ‖f x‖) ≤ R →
        ∃ v ∈ t, dist (restrictLp Ω (ρ ⋆ f)
          ((hρ.continuous.integrable_of_hasCompactSupport hc).integrable_convolution
            (ContinuousLinearMap.lsmul ℝ ℝ) hf)) v < ε := by
  letI : CompactSpace (Output Ω) := isCompact_iff_compactSpace.1 hΩ.isCompact_closure
  obtain ⟨M₀, hM₀⟩ := hρ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  obtain ⟨L₀, hL₀⟩ := (hρ.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport (hc.fderiv ℝ).norm
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  let L : ℝ≥0 := ⟨max L₀ 0, le_max_right _ _⟩
  have hρlip : LipschitzWith L ρ := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hρ.differentiable one_ne_zero)
    intro x
    exact_mod_cast ((hL₀ ⟨x, rfl⟩).trans (le_max_left L₀ 0))
  let k : (Output Ω) → Space d → ℝ := fun x y ↦ ρ (x.val - y)
  have hmeas (x : (Output Ω)) : AEStronglyMeasurable (k x) volume :=
    (hρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbound (x : (Output Ω)) (y : Space d) : ‖k x y‖ ≤ M :=
    (hM₀ ⟨x.val - y, rfl⟩).trans (le_max_left M₀ 0)
  have hlip (y : Space d) : LipschitzWith L (fun x : (Output Ω) ↦ k x y) := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    simpa only [k, dist_sub_right, Subtype.dist_eq] using hρlip.dist_le_mul (x.val - y) (x'.val - y)
  let A := IntegralKernel.regularize volume k M L hmeas hbound hlip ''
    Metric.closedBall (0 : Lp ℝ 1 (volume : Measure (Space d))) R
  let V : ℝ := (domainMeasure Ω univ).toReal
  let η : ℝ := ε / (V + 1)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos hε (by linarith)
  have hcompact : IsCompact (closure A) :=
    IntegralKernel.regularize_closedBall_relativelyCompact volume k M L hmeas hbound hlip R
  obtain ⟨s, hsA, hsfinite, hscover⟩ :=
    Metric.finite_approx_of_totallyBounded (totallyBounded_closure.1 hcompact.totallyBounded) η hη
  letI : Fintype {b // b ∈ s} := hsfinite.fintype
  let center : {b // b ∈ s} → Lp ℝ 1 (volume : Measure (Space d)) :=
    fun b ↦ Classical.choose (hsA b.property)
  have hcenter (b : {b // b ∈ s}) :
      IntegralKernel.regularize volume k M L hmeas hbound hlip (center b) = b.val :=
    (Classical.choose_spec (hsA b.property)).2
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hc
  let net : {b // b ∈ s} → Lp ℝ 1 (domainMeasure Ω) := fun b ↦
    restrictLp Ω (ρ ⋆ (center b : Space d → ℝ))
      (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        (memLp_one_iff_integrable.1 (Lp.memLp (center b))))
  refine ⟨Set.range net, Set.finite_range net, ?_⟩
  intro f hf hfR
  let fLp : Lp ℝ 1 (volume : Measure (Space d)) := (memLp_one_iff_integrable.2 hf).toLp f
  have hflp : ‖fLp‖ ≤ R := by
    rw [L1.norm_eq_integral_norm]
    exact (le_of_eq (integral_congr_ae ((memLp_one_iff_integrable.2 hf).coeFn_toLp.fun_comp (fun t : ℝ ↦ ‖t‖)))).trans hfR
  have hfA : IntegralKernel.regularize volume k M L hmeas hbound hlip fLp ∈ A :=
    ⟨fLp, by simpa [Metric.mem_closedBall, dist_zero_right] using hflp, rfl⟩
  have hcov : ∃ b ∈ s, dist (IntegralKernel.regularize volume k M L hmeas hbound hlip fLp) b < η := by
    simpa [Set.mem_iUnion] using hscover hfA
  obtain ⟨b, hbs, hnear⟩ := hcov
  let b' : {b // b ∈ s} := ⟨b, hbs⟩
  refine ⟨net b', ⟨b', rfl⟩, ?_⟩
  have hconvEq : ρ ⋆ f = ρ ⋆ (fLp : Space d → ℝ) :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) EventuallyEq.rfl
      (memLp_one_iff_integrable.2 hf).coeFn_toLp.symm
  have huniform (x : Space d) (hx : x ∈ (Ω : Set (Space d))) :
      ‖(ρ ⋆ f) x - (ρ ⋆ (center b' : Space d → ℝ)) x‖ ≤
        dist (IntegralKernel.regularize volume k M L hmeas hbound hlip fLp) b := by
    have hbc : IntegralKernel.regularize volume k M L hmeas hbound hlip (center b') = b := hcenter b'
    rw [hconvEq, ← hbc]
    have hd := BoundedContinuousFunction.dist_coe_le_dist
      (f := IntegralKernel.regularize volume k M L hmeas hbound hlip fLp)
      (g := IntegralKernel.regularize volume k M L hmeas hbound hlip (center b'))
      (⟨x, subset_closure hx⟩ : (Output Ω))
    simpa only [IntegralKernel.regularize_apply, k, convolution_eq_swap,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, dist_eq_norm] using hd
  have hd := dist_restrictLp_le_uniform Ω
    (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf)
    (hρi.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (memLp_one_iff_integrable.1 (Lp.memLp (center b')))) huniform
  have hdist0 : 0 ≤ dist (IntegralKernel.regularize volume k M L hmeas hbound hlip fLp) b := dist_nonneg
  have hηeq : (V + 1) * η = ε := by dsimp [η]; field_simp
  change dist (restrictLp Ω (ρ ⋆ f) _) (restrictLp Ω (ρ ⋆ (center b' : Space d → ℝ)) _) < ε
  apply lt_of_le_of_lt hd
  change V * _ < ε
  nlinarith

end KernelApproximation
end VariationalRegularization.BVCompactness
