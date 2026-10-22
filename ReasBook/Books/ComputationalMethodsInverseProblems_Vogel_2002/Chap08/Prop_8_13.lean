/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13.Sobolev
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.UrysohnsLemma

public section

namespace VariationalRegularization

open scoped ContDiff

variable {d : ℕ}

/-!
Proposition 8.13.

The source theorem is a statement about the canonical domain-local Sobolev
surface `W¹,¹(Ω)`: for `f : W¹,¹(Ω)`, the Chapter 8 total variation of the
underlying `L¹(Ω)` function agrees with the integral of the norm of the weak
gradient.
-/

/-- Helper for Proposition 8.13: every admissible divergence pairing is bounded
above by the integral of the weak-gradient norm. -/
lemma pairingLeIntegralNormWeakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) (v : AdmissibleTestField Ω) :
    admissibleDivergencePairing f.toL1 v ≤ f.integralNormWeakGradient := by
  -- Rewrite the Chapter 8 pairing through the weak gradient so the estimate becomes pointwise.
  rw [W11.pairing_eq_neg_integral_inner, W11.integralNormWeakGradient_def]
  have hgradInt : MeasureTheory.Integrable (fun x ↦ ‖f.weakGradient x‖) (domainMeasure Ω) := by
    -- `f.weakGradient ∈ L¹(Ω)` gives integrability of its pointwise norm.
    simpa [MeasureTheory.memLp_one_iff_integrable] using
      (MeasureTheory.Lp.memLp f.weakGradient).norm
  have hvNorm : ∀ x : EuclideanSpace ℝ (Fin d), ‖v.toTestFunction x‖ ≤ 1 := by
    -- Inside `Ω` this is part of admissibility, while outside `Ω` the test function vanishes.
    intro x
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d)))
    · exact v.norm_le_one x hx
    · have htsupport : x ∉ tsupport v.toTestFunction := by
        exact fun hxt ↦ hx (v.toTestFunction.tsupport_subset hxt)
      have hzero : v.toTestFunction x = 0 := image_eq_zero_of_notMem_tsupport htsupport
      simp [hzero]
  have hinnerAesm :
      MeasureTheory.AEStronglyMeasurable
        (fun x ↦ -inner ℝ (f.weakGradient x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- The integrand is measurable because both factors are measurable.
    fun_prop
  have hinnerInt :
      MeasureTheory.Integrable
        (fun x ↦ -inner ℝ (f.weakGradient x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- Dominate the pairing integrand by the integrable norm of the weak gradient.
    refine hgradInt.mono' hinnerAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      calc
        ‖-inner ℝ (f.weakGradient x) (v.toTestFunction x)‖
            = |inner ℝ (f.weakGradient x) (v.toTestFunction x)| := by
              simp
        _ ≤ ‖f.weakGradient x‖ * ‖v.toTestFunction x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖f.weakGradient x‖ := by
          nlinarith [hvNorm x, norm_nonneg (f.weakGradient x)]
  have hpointwise :
      ∀ᵐ x ∂domainMeasure Ω,
        -inner ℝ (f.weakGradient x) (v.toTestFunction x) ≤ ‖f.weakGradient x‖ := by
    -- The admissibility bound `‖v x‖ ≤ 1` gives the pointwise estimate on the pairing density.
    exact Filter.Eventually.of_forall fun x ↦ by
      calc
        -inner ℝ (f.weakGradient x) (v.toTestFunction x)
            ≤ |inner ℝ (f.weakGradient x) (v.toTestFunction x)| := neg_le_abs _
        _ ≤ ‖f.weakGradient x‖ * ‖v.toTestFunction x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖f.weakGradient x‖ := by
          nlinarith [hvNorm x, norm_nonneg (f.weakGradient x)]
  have hnegIntegral :
      -∫ x, inner ℝ (f.weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω =
        ∫ x, -inner ℝ (f.weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω := by
    -- Move the outer minus sign into the integrand before applying monotonicity of the integral.
    simpa using
      (MeasureTheory.integral_neg
        (fun x ↦ inner ℝ (f.weakGradient x) (v.toTestFunction x))
        (μ := domainMeasure Ω)).symm
  rw [hnegIntegral]
  -- Integrate the pointwise bound.
  exact MeasureTheory.integral_mono_ae hinnerInt hgradInt hpointwise

/-- Helper for Proposition 8.13: a smooth compactly supported field inside `Ω`
with pointwise norm at most `1` packages as an admissible test field. -/
lemma smoothFieldToAdmissibleTestField
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hψ_norm : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖ψ x‖ ≤ 1) :
    ∃ v : AdmissibleTestField Ω, ∀ x, v.toTestFunction x = ψ x := by
  -- Package the ambient smooth field into the Chapter 8 admissible owner.
  refine ⟨AdmissibleTestField.ofTestFunction
      (TestFunction.mk ψ hψ_cont hψ_compact hψ_subset) ?_, ?_⟩
  · intro x hx
    simpa using hψ_norm x hx
  · intro x
    rfl

/-- Helper for Proposition 8.13: an integrable nonnegative density on `Ω` has a
compact core inside `Ω` that captures all but an arbitrarily small tail
integral. -/
lemma existsCompactSubset_tailIntegral_lt
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hInt : MeasureTheory.Integrable h (domainMeasure Ω))
    (h_nonneg : ∀ x, 0 ≤ h x)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)),
      K ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      IsCompact K ∧
      ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), h x ∂domainMeasure Ω < ε := by
  let ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    (domainMeasure Ω).withDensity fun x ↦ ENNReal.ofReal (h x)
  have hν_finite : MeasureTheory.IsFiniteMeasure ν := by
    -- The weighted measure is finite because `h` is integrable.
    simpa [ν] using MeasureTheory.isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral
  have hΩ_meas : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin d))) := Ω.2.measurableSet
  obtain ⟨K, hK_subset, hK_compact, _hK_closed, hK_tail⟩ :=
    hΩ_meas.exists_isCompact_isClosed_sdiff_lt
      (μ := ν)
      (by simp)
      (ε := ENNReal.ofReal ε)
      (by positivity)
  refine ⟨K, hK_subset, hK_compact, ?_⟩
  have h_nonneg_ae :
      0 ≤ᵐ[domainMeasure Ω] fun x ↦ h x :=
    Filter.Eventually.of_forall h_nonneg
  have hInt_restrict :
      MeasureTheory.Integrable h
        ((domainMeasure Ω).restrict ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K)) := by
    -- Restrict the original integrable density to the tail region.
    exact hInt.restrict
  have h_tail_eq :
      ENNReal.ofReal
          (∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), h x ∂domainMeasure Ω) =
        ν (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K)) := by
    -- Convert the tail integral to the weighted-measure mass of the same set.
    rw [MeasureTheory.withDensity_apply _ ((show
      MeasurableSet (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K)) from
        hΩ_meas.diff hK_compact.isClosed.measurableSet))]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt_restrict
      (MeasureTheory.ae_restrict_of_ae h_nonneg_ae)
  have h_tail_lt_ennreal :
      ENNReal.ofReal
          (∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), h x ∂domainMeasure Ω) <
        ENNReal.ofReal ε := by
    -- The compact approximation for the weighted measure is exactly the desired tail bound.
    simpa [h_tail_eq, ν] using hK_tail
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h_tail_lt_ennreal

/-- Helper for Proposition 8.13: a compact subset of `Ω` admits a compactly
supported continuous cutoff equal to `1` on that compact core. -/
lemma existsCompactlySupportedCutoff_eqOneOnCompact
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      Continuous χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn χ 1 K ∧
      ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Use Urysohn's lemma to produce the compactly supported cutoff inside `Ω`.
  obtain ⟨χ, hχ_one, hχ_tsupport_compact, hχ_subset, hχ_range⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK_compact Ω.2 hK_subset
  refine ⟨χ, χ.continuous, ?_, hχ_subset, hχ_one, hχ_range⟩
  exact HasCompactSupport.intro hχ_tsupport_compact fun x hx ↦ image_eq_zero_of_notMem_tsupport hx

/-- Helper for Proposition 8.13: the restricted domain measure `domainMeasure Ω`
is finite on compact sets because it is a restriction of the Euclidean
Hausdorff measure. -/
instance domainMeasure_isFiniteMeasureOnCompacts
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    MeasureTheory.IsFiniteMeasureOnCompacts (domainMeasure Ω) := by
  -- Unfold `domainMeasure` once so the standard `restrict` instance applies.
  simpa [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
    (inferInstance :
      MeasureTheory.IsFiniteMeasureOnCompacts
        ((MeasureTheory.MeasureSpace.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
          (Ω : Set (EuclideanSpace ℝ (Fin d)))))

/-- Helper for Proposition 8.13: a compactly supported function supported in `Ω`
admits a smooth scalar cutoff that is identically `1` on its topological support
and whose own topological support is compactly contained in `Ω`. -/
lemma existsSmoothCompactSupportCutoffOnSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hu_compact : HasCompactSupport u)
    (hsub : tsupport u ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧
      tsupport η ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn η 1 (tsupport u) ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) := by
  let K : Set (EuclideanSpace ℝ (Fin d)) := tsupport u
  obtain ⟨L, hL_compact, hKL, hL_subset⟩ :=
    exists_compact_between hu_compact Ω.2 hsub
  obtain ⟨U, hU_open, hKU, hUclosure_subset⟩ :=
    normal_exists_closure_subset hu_compact.isClosed isOpen_interior hKL
  obtain ⟨η, hη_smooth, hη_range, hη_support, hη_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      hU_open hu_compact.isClosed hKU
  refine ⟨η, hη_smooth.contDiff, ?_, ?_, ?_, fun x ↦ hη_range ⟨x, rfl⟩⟩
  · -- The refined open neighborhood has compact closure inside `Ω`.
    have hclosure_compact : IsCompact (closure U) := by
      refine hL_compact.of_isClosed_subset isClosed_closure ?_
      exact hUclosure_subset.trans interior_subset
    have htsupport_compact : IsCompact (tsupport η) := by
      simpa [K, tsupport, hη_support] using hclosure_compact
    exact HasCompactSupport.intro htsupport_compact fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  · -- The cutoff support sits in the compact neighborhood chosen inside `Ω`.
    simpa [K, tsupport, hη_support] using
      hUclosure_subset.trans (interior_subset.trans hL_subset)
  · -- On `tsupport u`, the support-equals-one theorem gives the desired identity.
    intro x hx
    exact (hη_one x).1 hx

/-- Helper for Proposition 8.13: a scalar cutoff equal to `1` on the support of
`u` acts trivially on `u`. -/
lemma eq_smul_of_eqOn_tsupport
    {α : Type*} [TopologicalSpace α]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : α → F} {η : α → ℝ}
    (hη : Set.EqOn η 1 (tsupport u)) :
    u = fun x ↦ η x • u x := by
  funext x
  by_cases hx : x ∈ tsupport u
  · -- On the support, the cutoff is exactly `1`.
    have hηx : η x = 1 := hη hx
    simp [hηx]
  · -- Off the support, the function already vanishes.
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hu0]

/-- Helper for Proposition 8.13: multiplying a global approximation by a scalar
cutoff bounded by `1` does not increase the `L¹` approximation error once the
cutoff is `1` on the support of the target function. -/
lemma cutoffRestore_eLpNormOne_le
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u ψ₀ : α → F} {η : α → ℝ}
    (hη_one : Set.EqOn η 1 (tsupport u))
    (hη_norm : ∀ x, |η x| ≤ 1) :
    MeasureTheory.eLpNorm (fun x ↦ u x - η x • ψ₀ x) 1 μ ≤
      MeasureTheory.eLpNorm (fun x ↦ u x - ψ₀ x) 1 μ := by
  -- After rewriting `u = η • u`, compare pointwise using `‖η x‖ ≤ 1`.
  refine MeasureTheory.eLpNorm_mono_ae <| Filter.Eventually.of_forall fun x ↦ ?_
  have hux : u x = η x • u x := by
    simpa using congrFun (eq_smul_of_eqOn_tsupport hη_one) x
  calc
    ‖u x - η x • ψ₀ x‖ = ‖η x • u x - η x • ψ₀ x‖ := by
      exact congrArg (fun z ↦ ‖z - η x • ψ₀ x‖) hux
    _ = ‖η x • (u x - ψ₀ x)‖ := by rw [smul_sub]
    _ ≤ ‖η x‖ * ‖u x - ψ₀ x‖ := norm_smul_le _ _
    _ ≤ ‖u x - ψ₀ x‖ := by
      have hηx : ‖η x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using hη_norm x
      nlinarith [norm_nonneg (u x - ψ₀ x)]

/-- Helper for Proposition 8.13: localizing an `L¹` vector field by a cutoff
equal to `1` on a compact core produces an `L¹` error controlled by the tail
outside that core. -/
lemma localizationError_integralNorm_le_tail
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {K : Set (EuclideanSpace ℝ (Fin d))} {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hgInt : MeasureTheory.Integrable g (domainMeasure Ω))
    (hχ_cont : Continuous χ)
    (hK_meas : MeasurableSet K)
    (hχ_one : Set.EqOn χ 1 K)
    (hχ_range : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x, ‖g x - χ x • g x‖ ∂domainMeasure Ω ≤
      ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖g x‖ ∂domainMeasure Ω := by
  let μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) := domainMeasure Ω
  have hnormInt : MeasureTheory.Integrable (fun x ↦ ‖g x‖) μ := hgInt.norm
  have hdiffAesm :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ g x - χ x • g x) μ := by
    -- The localization error is measurable because the cutoff is continuous and `g` is `L¹`.
    exact hgInt.aestronglyMeasurable.sub
      (hχ_cont.aestronglyMeasurable.smul hgInt.aestronglyMeasurable)
  have hdiffInt : MeasureTheory.Integrable (fun x ↦ g x - χ x • g x) μ := by
    -- The localization error is pointwise dominated by `‖g‖`.
    refine hnormInt.mono' hdiffAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hχ0 : 0 ≤ χ x := (hχ_range x).1
      have hχ1 : χ x ≤ 1 := (hχ_range x).2
      have habs : |1 - χ x| ≤ 1 := by
        have hnonneg : 0 ≤ 1 - χ x := by linarith
        rw [abs_of_nonneg hnonneg]
        linarith
      have hcoeff : ‖1 - χ x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using habs
      have hsmul : g x - χ x • g x = (1 - χ x) • g x := by
        calc
          g x - χ x • g x = (1 : ℝ) • g x - χ x • g x := by rw [one_smul]
          _ = (1 - χ x) • g x := by rw [sub_smul]
      calc
        ‖g x - χ x • g x‖ = ‖(1 - χ x) • g x‖ := by rw [hsmul]
        _ ≤ ‖1 - χ x‖ * ‖g x‖ := norm_smul_le _ _
        _ ≤ ‖g x‖ := by
          nlinarith [hcoeff, norm_nonneg (g x)]
  have hrightInt :
      MeasureTheory.Integrable
        (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K).indicator fun x ↦ ‖g x‖) μ := by
    -- Restricting the integrable norm density to the tail set keeps it integrable.
    exact hnormInt.indicator (Ω.2.measurableSet.diff hK_meas)
  have hpointwise :
      ∀ᵐ x ∂μ,
        ‖g x - χ x • g x‖ ≤
          (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K).indicator fun x ↦ ‖g x‖) x := by
    -- On the compact core the error vanishes, and away from it the same pointwise domination applies.
    have hpointwiseBase :
        ∀ᵐ x ∂((MeasureTheory.Measure.euclideanHausdorffMeasure d :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
            (Ω : Set (EuclideanSpace ℝ (Fin d)))),
          ‖g x - χ x • g x‖ ≤
            (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K).indicator fun y ↦ ‖g y‖) x := by
      exact
        (MeasureTheory.ae_restrict_iff'
          (μ := (MeasureTheory.Measure.euclideanHausdorffMeasure d :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
          (s := (Ω : Set (EuclideanSpace ℝ (Fin d))))
          Ω.2.measurableSet).2 <|
          Filter.Eventually.of_forall fun x hxΩ ↦ by
            by_cases hxK : x ∈ K
            · have hχx : χ x = 1 := hχ_one hxK
              simp [hxΩ, hxK, hχx]
            · have hχ0 : 0 ≤ χ x := (hχ_range x).1
              have hχ1 : χ x ≤ 1 := (hχ_range x).2
              have habs : |1 - χ x| ≤ 1 := by
                have hnonneg : 0 ≤ 1 - χ x := by linarith
                rw [abs_of_nonneg hnonneg]
                linarith
              have hcoeff : ‖1 - χ x‖ ≤ 1 := by
                simpa [Real.norm_eq_abs] using habs
              have hsmul : g x - χ x • g x = (1 - χ x) • g x := by
                calc
                  g x - χ x • g x = (1 : ℝ) • g x - χ x • g x := by rw [one_smul]
                  _ = (1 - χ x) • g x := by rw [sub_smul]
              calc
                ‖g x - χ x • g x‖ = ‖(1 - χ x) • g x‖ := by rw [hsmul]
                _ ≤ ‖1 - χ x‖ * ‖g x‖ := norm_smul_le _ _
                _ ≤ ‖g x‖ := by
                  nlinarith [hcoeff, norm_nonneg (g x)]
                _ = (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K).indicator fun y ↦ ‖g y‖) x := by
                  simp [hxΩ, hxK]
    simpa [μ, domainMeasure_def] using hpointwiseBase
  simpa [μ] using
    (calc
      ∫ x, ‖g x - χ x • g x‖ ∂μ
          ≤ ∫ x, (((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K).indicator fun y ↦ ‖g y‖) x ∂μ := by
            exact MeasureTheory.integral_mono_ae hdiffInt.norm hrightInt hpointwise
      _ = ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖g x‖ ∂μ := by
            simpa using
              (MeasureTheory.integral_indicator
                (μ := μ)
                (f := fun y ↦ ‖g y‖)
                (s := ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K))
                (Ω.2.measurableSet.diff hK_meas)))

/-- Helper for Proposition 8.13: pairing an integrable vector field with an
admissible test field gives an integrable pairing density. -/
lemma integrableNegInner_of_admissible
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hgInt : MeasureTheory.Integrable g (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ -inner ℝ (g x) (v.toTestFunction x))
      (domainMeasure Ω) := by
  have hvNorm : ∀ x : EuclideanSpace ℝ (Fin d), ‖v.toTestFunction x‖ ≤ 1 := by
    -- Extend the admissibility bound from `Ω` to all points using vanishing off `Ω`.
    intro x
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d)))
    · exact v.norm_le_one x hx
    · have htsupport : x ∉ tsupport v.toTestFunction := by
        exact fun hxt ↦ hx (v.toTestFunction.tsupport_subset hxt)
      have hzero : v.toTestFunction x = 0 := image_eq_zero_of_notMem_tsupport htsupport
      simp [hzero]
  have hnormInt : MeasureTheory.Integrable (fun x ↦ ‖g x‖) (domainMeasure Ω) := hgInt.norm
  have hinnerAesm :
      MeasureTheory.AEStronglyMeasurable
        (fun x ↦ -inner ℝ (g x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- The pairing density is measurable because both factors are measurable.
    fun_prop
  -- Dominate the pairing density by the integrable norm of `g`.
  refine hnormInt.mono' hinnerAesm ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    calc
      ‖-inner ℝ (g x) (v.toTestFunction x)‖
          = |inner ℝ (g x) (v.toTestFunction x)| := by
            simp
      _ ≤ ‖g x‖ * ‖v.toTestFunction x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖g x‖ := by
        nlinarith [hvNorm x, norm_nonneg (g x)]

/-- Helper for Proposition 8.13: pairing an integrable vector field with an
admissible test field is bounded by the integral of its norm. -/
lemma integralNegInner_le_integralNorm_of_admissible
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hgInt : MeasureTheory.Integrable g (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω ≤
      ∫ x, ‖g x‖ ∂domainMeasure Ω := by
  have hvNorm : ∀ x : EuclideanSpace ℝ (Fin d), ‖v.toTestFunction x‖ ≤ 1 := by
    -- Extend the admissibility bound from `Ω` to all points using vanishing off `Ω`.
    intro x
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d)))
    · exact v.norm_le_one x hx
    · have htsupport : x ∉ tsupport v.toTestFunction := by
        exact fun hxt ↦ hx (v.toTestFunction.tsupport_subset hxt)
      have hzero : v.toTestFunction x = 0 := image_eq_zero_of_notMem_tsupport htsupport
      simp [hzero]
  have hnormInt : MeasureTheory.Integrable (fun x ↦ ‖g x‖) (domainMeasure Ω) := hgInt.norm
  have hinnerAesm :
      MeasureTheory.AEStronglyMeasurable
        (fun x ↦ -inner ℝ (g x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- The pairing integrand is measurable because both factors are measurable.
    fun_prop
  have hinnerInt :
      MeasureTheory.Integrable
        (fun x ↦ -inner ℝ (g x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- Reuse the standalone integrability bridge before applying integral monotonicity.
    exact integrableNegInner_of_admissible hgInt v
  have hpointwise :
      ∀ᵐ x ∂domainMeasure Ω,
        -inner ℝ (g x) (v.toTestFunction x) ≤ ‖g x‖ := by
    -- The globalized bound `‖v x‖ ≤ 1` gives the pointwise estimate.
    exact Filter.Eventually.of_forall fun x ↦ by
      calc
        -inner ℝ (g x) (v.toTestFunction x)
            ≤ |inner ℝ (g x) (v.toTestFunction x)| := neg_le_abs _
        _ ≤ ‖g x‖ * ‖v.toTestFunction x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖g x‖ := by
          nlinarith [hvNorm x, norm_nonneg (g x)]
  have hnegIntegral :
      -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω =
        ∫ x, -inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω := by
    -- Move the outer minus sign into the integrand before integrating.
    simpa using
      (MeasureTheory.integral_neg
        (fun x ↦ inner ℝ (g x) (v.toTestFunction x))
        (μ := domainMeasure Ω)).symm
  rw [hnegIntegral]
  exact MeasureTheory.integral_mono_ae hinnerInt hnormInt hpointwise

/-- Helper for Proposition 8.13: changing the paired field by an `L¹` error
changes the admissible pairing by at most the integral of that error. -/
lemma pairingSubError_ge
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {g u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hsubInt : MeasureTheory.Integrable (fun x ↦ g x - u x) (domainMeasure Ω))
    (huInt : MeasureTheory.Integrable u (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω ≥
      -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂domainMeasure Ω -
        ∫ x, ‖g x - u x‖ ∂domainMeasure Ω := by
  have hsubPairInt :
      MeasureTheory.Integrable
        (fun x ↦ -inner ℝ (g x - u x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- The pairing density for the difference field is integrable by the same domination estimate.
    exact integrableNegInner_of_admissible (g := fun x ↦ g x - u x) hsubInt v
  have huPairInt :
      MeasureTheory.Integrable
        (fun x ↦ -inner ℝ (u x) (v.toTestFunction x))
        (domainMeasure Ω) := by
    -- The pairing density for the reference field is also integrable.
    exact integrableNegInner_of_admissible (g := u) huInt v
  have hdecomp :
      -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω =
        -∫ x, inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω +
          -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂domainMeasure Ω := by
    -- Expand `g = (g - u) + u` and split the integral into the error and reference parts.
    have hpointwise :
        (fun x ↦ -inner ℝ (g x) (v.toTestFunction x)) =ᵐ[domainMeasure Ω]
          (fun x ↦
            -inner ℝ (g x - u x) (v.toTestFunction x) +
              -inner ℝ (u x) (v.toTestFunction x)) := by
      exact Filter.Eventually.of_forall fun x ↦ by
        have hinner :
            inner ℝ (g x) (v.toTestFunction x) =
              inner ℝ (g x - u x) (v.toTestFunction x) +
                inner ℝ (u x) (v.toTestFunction x) := by
          rw [← inner_add_left]
          simpa using (sub_add_cancel (g x) (u x)).symm
        nlinarith [hinner]
    calc
      -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂domainMeasure Ω
          = ∫ x, (-inner ℝ (g x) (v.toTestFunction x)) ∂domainMeasure Ω := by
              simpa using
                (MeasureTheory.integral_neg
                  (fun x ↦ inner ℝ (g x) (v.toTestFunction x))
                  (μ := domainMeasure Ω)).symm
      _ = ∫ x,
            (-inner ℝ (g x - u x) (v.toTestFunction x) +
              -inner ℝ (u x) (v.toTestFunction x)) ∂domainMeasure Ω := by
              exact MeasureTheory.integral_congr_ae hpointwise
      _ = ∫ x, -inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω +
            ∫ x, -inner ℝ (u x) (v.toTestFunction x) ∂domainMeasure Ω := by
              rw [MeasureTheory.integral_add hsubPairInt huPairInt]
      _ = -∫ x, inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω +
            -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂domainMeasure Ω := by
              simp [MeasureTheory.integral_neg]
  have herrorLower :
      -∫ x, inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω ≥
        -∫ x, ‖g x - u x‖ ∂domainMeasure Ω := by
    -- Apply the admissible upper bound to the negated error field to get the required lower bound.
    have hsubInt' : MeasureTheory.Integrable (fun x ↦ u x - g x) (domainMeasure Ω) := by
      refine hsubInt.neg.congr ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        simp [sub_eq_add_neg, add_comm]
    have hflip :
        -∫ x, inner ℝ (u x - g x) (v.toTestFunction x) ∂domainMeasure Ω ≤
          ∫ x, ‖u x - g x‖ ∂domainMeasure Ω := by
      exact integralNegInner_le_integralNorm_of_admissible
        (g := fun x ↦ u x - g x) hsubInt' v
    have hflip' :
        ∫ x, inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω ≤
          ∫ x, ‖g x - u x‖ ∂domainMeasure Ω := by
      have hEq :
          (fun x ↦ inner ℝ (g x - u x) (v.toTestFunction x)) =ᵐ[domainMeasure Ω]
            (fun x ↦ -inner ℝ (u x - g x) (v.toTestFunction x)) := by
        exact Filter.Eventually.of_forall fun x ↦ by
          have hsub : g x - u x = -(u x - g x) := by
            abel
          calc
            inner ℝ (g x - u x) (v.toTestFunction x)
                = inner ℝ (-(u x - g x)) (v.toTestFunction x) := by rw [hsub]
            _ = -inner ℝ (u x - g x) (v.toTestFunction x) := by
                  rw [inner_neg_left]
      calc
        ∫ x, inner ℝ (g x - u x) (v.toTestFunction x) ∂domainMeasure Ω
            = ∫ x, -inner ℝ (u x - g x) (v.toTestFunction x) ∂domainMeasure Ω := by
                exact MeasureTheory.integral_congr_ae hEq
        _ = -∫ x, inner ℝ (u x - g x) (v.toTestFunction x) ∂domainMeasure Ω := by
              simpa using
                (MeasureTheory.integral_neg
                  (fun x ↦ inner ℝ (u x - g x) (v.toTestFunction x))
                  (μ := domainMeasure Ω))
        _ ≤ ∫ x, ‖u x - g x‖ ∂domainMeasure Ω := hflip
        _ = ∫ x, ‖g x - u x‖ ∂domainMeasure Ω := by
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun x ↦ by
                simpa [sub_eq_add_neg, add_comm] using norm_neg (g x - u x)
    linarith
  linarith [hdecomp, herrorLower]

/-- Helper for Proposition 8.13: the zero admissible field has zero divergence. -/
lemma admissibleDivergence_zeroField
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
  -- Rewrite the derivative of the zero test function and simplify the coordinate sum.
  have hzero :
      fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
    change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) => (0 : EuclideanSpace ℝ (Fin d))) x = 0
    simp
  rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hzero]
  simp

/-- Helper for Proposition 8.13: the scalar saturation loss is at most `δ`. -/
lemma sqrtSaturation_loss_le_delta
    {t δ : ℝ}
    (ht : 0 ≤ t)
    (hδ : 0 < δ) :
    t ^ 2 / Real.sqrt (δ ^ 2 + t ^ 2) ≥ t - δ := by
  -- Split according to whether the target lower bound is already nonpositive.
  by_cases htd : t ≤ δ
  · have hnonneg : 0 ≤ t ^ 2 / Real.sqrt (δ ^ 2 + t ^ 2) := by
      positivity
    linarith
  · have htd' : 0 < t - δ := sub_pos.mpr <| lt_of_not_ge htd
    have hsqrt_pos : 0 < Real.sqrt (δ ^ 2 + t ^ 2) := by
      apply Real.sqrt_pos.mpr
      nlinarith [hδ]
    have hsqrt_le : Real.sqrt (δ ^ 2 + t ^ 2) ≤ δ + t := by
      refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
      rw [Real.sq_sqrt]
      · nlinarith [sq_nonneg δ]
      · positivity
    have hmul :
        (t - δ) * Real.sqrt (δ ^ 2 + t ^ 2) ≤ t ^ 2 := by
      calc
        (t - δ) * Real.sqrt (δ ^ 2 + t ^ 2) ≤ (t - δ) * (δ + t) := by
          exact mul_le_mul_of_nonneg_left hsqrt_le htd'.le
        _ = t ^ 2 - δ ^ 2 := by ring
        _ ≤ t ^ 2 := by nlinarith [sq_nonneg δ]
    exact (le_div_iff₀ hsqrt_pos).2 hmul

/-- Helper for Proposition 8.13: the saturated field associated to `ψ` has
pointwise norm at most `1`. -/
lemma saturatedField_norm_le_one
    {ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ x,
      ‖(-(1 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2)) • ψ x :
          EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
  -- Compare `‖ψ x‖` with the saturation denominator by squaring both sides.
  intro x
  have hsqrt_pos : 0 < Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [hδ]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := le_of_lt hsqrt_pos
  have hnorm_le :
      ‖ψ x‖ ≤ Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
    refine (sq_le_sq₀ (norm_nonneg _) hsqrt_nonneg).mp ?_
    rw [Real.sq_sqrt]
    · nlinarith [sq_nonneg δ]
    · positivity
  have hdiv_le_one : ‖ψ x‖ / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) ≤ 1 := by
    exact (div_le_one hsqrt_pos).2 hnorm_le
  have hmul_le_one : ‖ψ x‖ * (Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2))⁻¹ ≤ 1 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le_one
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt_pos, one_div, mul_comm, mul_left_comm,
    mul_assoc] using hmul_le_one

/-- Helper for Proposition 8.13: the smooth saturation of `ψ` gives a pointwise
lower bound against any compactly supported comparison field `u`, with the
scalar defect confined to a fixed support set `s`. -/
lemma saturatedField_pointwiseLowerBoundOnSupport
    {u ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {s : Set (EuclideanSpace ℝ (Fin d))} {δ : ℝ}
    (hsub : tsupport u ⊆ s)
    (hδ : 0 < δ) :
    ∀ x,
      -inner ℝ (u x) (-(1 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2)) • ψ x) ≥
        ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x := by
  -- Route correction: keep the denominator in one spelling world and split the
  -- estimate into the off-support vanishing case and the on-support scalar-loss
  -- estimate.
  intro x
  by_cases hx : x ∈ s
  · have hsqrt_pos : 0 < Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
      apply Real.sqrt_pos.mpr
      nlinarith [hδ]
    let satx : EuclideanSpace ℝ (Fin d) :=
      -(1 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2)) • ψ x
    have hsat_norm :
        ‖satx‖ ≤ 1 := by
      simpa [satx] using saturatedField_norm_le_one (ψ := ψ) hδ x
    have herror :
        -inner ℝ (u x - ψ x) satx ≥ -‖u x - ψ x‖ := by
      have habs :
          |inner ℝ (u x - ψ x) satx| ≤ ‖u x - ψ x‖ := by
        calc
          |inner ℝ (u x - ψ x) satx| ≤ ‖u x - ψ x‖ * ‖satx‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖u x - ψ x‖ := by
            nlinarith [hsat_norm, norm_nonneg (u x - ψ x)]
      have hinner_le : inner ℝ (u x - ψ x) satx ≤ ‖u x - ψ x‖ := by
        exact (le_abs_self _).trans habs
      nlinarith
    have hscalar :
        ‖ψ x‖ ^ 2 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) ≥ ‖ψ x‖ - δ := by
      exact sqrtSaturation_loss_le_delta (norm_nonneg _) hδ
    have hnorm_bridge : ‖u x‖ ≤ ‖ψ x‖ + ‖u x - ψ x‖ := by
      have := norm_add_le (ψ x) (u x - ψ x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hmain :
        -inner ℝ (u x) satx ≥
          ‖ψ x‖ - ‖u x - ψ x‖ - δ := by
      have hsplit :
          inner ℝ (u x) satx =
            inner ℝ (u x - ψ x) satx + inner ℝ (ψ x) satx := by
        rw [inner_sub_left]
        ring
      have hpsi_sat :
          -inner ℝ (ψ x) satx =
            ‖ψ x‖ ^ 2 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
        dsimp [satx]
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [hsqrt_pos.ne']
      calc
        -inner ℝ (u x) satx
            = -(inner ℝ (u x - ψ x) satx) +
                ‖ψ x‖ ^ 2 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
              rw [hsplit, neg_add, hpsi_sat]
        _ ≥ -‖u x - ψ x‖ + (‖ψ x‖ - δ) := by
              nlinarith [herror, hscalar]
        _ = ‖ψ x‖ - ‖u x - ψ x‖ - δ := by ring
    have hindicator : s.indicator (fun _ ↦ (1 : ℝ)) x = 1 := by
      simp [hx]
    rw [hindicator]
    nlinarith [hmain, hnorm_bridge]
  · have hu_zero : u x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hxt ↦ hx (hsub hxt)
    have hindicator : s.indicator (fun _ ↦ (1 : ℝ)) x = 0 := by
      simp [hx]
    have htrivial : (0 : ℝ) ≥ -2 * ‖ψ x‖ := by
      nlinarith [norm_nonneg (ψ x)]
    simpa [hu_zero, hindicator] using htrivial

/-- Helper for Proposition 8.13: saturating a smooth compactly supported field
produces an admissible test field. -/
lemma existsAdmissibleSaturatedField
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ v : AdmissibleTestField Ω,
      ∀ x,
        v.toTestFunction x =
          -(1 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2)) • ψ x := by
  let coeff : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x ↦ -(1 / Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2))
  let sat : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    coeff • ψ
  have hsat_cont : ContDiff ℝ 1 sat := by
    -- Smoothness comes from combining the smooth denominator with the smooth field `ψ`.
    have hnorm_sq : ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin d) => ‖ψ x‖ ^ 2 := by
      exact (contDiff_norm_sq (𝕜 := ℝ)).comp hψ_cont
    have hden_cont :
        ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin d) =>
          Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2) := by
      refine ((contDiff_const : ContDiff ℝ 1 fun _ : EuclideanSpace ℝ (Fin d) => δ ^ 2).add
        hnorm_sq).sqrt ?_
      intro x
      nlinarith [hδ]
    have hcoeff_cont :
        ContDiff ℝ 1 coeff := by
      have hinv :
          ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin d) =>
            (Real.sqrt (δ ^ 2 + ‖ψ x‖ ^ 2))⁻¹ := by
        refine hden_cont.inv ?_
        intro x
        apply Real.sqrt_ne_zero'.mpr
        nlinarith [hδ]
      simpa [coeff, one_div] using hinv.neg
    simpa [sat] using hcoeff_cont.smul hψ_cont
  have hsat_compact : HasCompactSupport sat := by
    -- The saturation factor does not enlarge the support beyond that of `ψ`.
    exact hψ_compact.smul_left (f := coeff)
  have hsat_subset : tsupport sat ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- The saturated field vanishes wherever `ψ` vanishes.
    exact (tsupport_smul_subset_right coeff ψ).trans hψ_subset
  have hsat_norm :
      ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖sat x‖ ≤ 1 := by
    -- The pointwise norm bound is the scalar denominator estimate.
    intro x _hx
    simpa [sat, coeff] using saturatedField_norm_le_one (ψ := ψ) hδ x
  obtain ⟨v, hv⟩ :=
    smoothFieldToAdmissibleTestField sat hsat_cont hsat_compact hsat_subset hsat_norm
  refine ⟨v, ?_⟩
  intro x
  simpa [sat, coeff] using hv x

/-- Helper for Proposition 8.13: for `p = 1`, an `eLpNorm` bound is the same as
an ordinary integral bound on the pointwise norm once the difference field is
known to be integrable. -/
lemma integralNorm_le_of_eLpNorm_one_le
    {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {F : Type*} [NormedAddCommGroup F]
    {h : α → F} {ε : ℝ}
    (hhInt : MeasureTheory.Integrable h μ)
    (hε : 0 ≤ ε)
    (hh : MeasureTheory.eLpNorm h 1 μ ≤ ENNReal.ofReal ε) :
    ∫ x, ‖h x‖ ∂μ ≤ ε := by
  -- Rewrite the `p = 1` seminorm as the lintegral of the norm and then back as a real integral.
  have hnonneg : 0 ≤ᵐ[μ] fun x ↦ ‖h x‖ := Filter.Eventually.of_forall fun x ↦ norm_nonneg _
  have hrewrite :
      ENNReal.ofReal (∫ x, ‖h x‖ ∂μ) = MeasureTheory.eLpNorm h 1 μ := by
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    simpa using MeasureTheory.ofReal_integral_eq_lintegral_ofReal hhInt.norm hnonneg
  have hbound :
      ENNReal.ofReal (∫ x, ‖h x‖ ∂μ) ≤ ENNReal.ofReal ε := by
    simpa [hrewrite] using hh
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hbound

/-- Helper for Proposition 8.13: for every `ε > 0`, there is an admissible test
field whose divergence pairing is within `ε` of the weak-gradient norm
integral. -/
lemma existsAlmostSharpAdmissibleField
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : AdmissibleTestField Ω,
      f.integralNormWeakGradient ≤ admissibleDivergencePairing f.toL1 v + ε := by
  let μ := domainMeasure Ω
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦ f.weakGradient x
  have hgInt : MeasureTheory.Integrable g μ := by
    -- Start from the given `L¹` weak gradient.
    simpa [μ, g, MeasureTheory.memLp_one_iff_integrable] using
      (MeasureTheory.Lp.memLp f.weakGradient)
  have hnormInt : MeasureTheory.Integrable (fun x ↦ ‖g x‖) μ := hgInt.norm
  -- First localize the weak gradient onto a compact core of `Ω`.
  obtain ⟨K, hK_subset, hK_compact, hK_tail⟩ :=
    existsCompactSubset_tailIntegral_lt
      (Ω := Ω) (h := fun x ↦ ‖g x‖) hnormInt (fun x ↦ norm_nonneg _) (ε := ε / 8)
      (by positivity)
  obtain ⟨χ, hχ_cont, hχ_compact, hχ_subset, hχ_one, hχ_range⟩ :=
    existsCompactlySupportedCutoff_eqOneOnCompact (Ω := Ω) hK_compact hK_subset
  let u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦ χ x • g x
  have hu_compact : HasCompactSupport u := by
    -- The cutoff support controls the localized field support.
    change HasCompactSupport (χ • g)
    simpa [u] using hχ_compact.smul_right (f' := g)
  have hu_subset : tsupport u ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- Since `u = χ • g`, its support stays inside the support of `χ`.
    simpa [u] using (tsupport_smul_subset_left χ g).trans hχ_subset
  have huAesm : MeasureTheory.AEStronglyMeasurable u μ := by
    -- The localized field is measurable because the cutoff is continuous.
    exact hχ_cont.aestronglyMeasurable.smul hgInt.aestronglyMeasurable
  have huInt : MeasureTheory.Integrable u μ := by
    -- The cutoff takes values in `[0, 1]`, so `u` is dominated by `‖g‖`.
    refine hnormInt.mono' huAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hχ0 : 0 ≤ χ x := (hχ_range x).1
      have hχ1 : χ x ≤ 1 := (hχ_range x).2
      have hχnorm : ‖χ x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hχ0] using hχ1
      calc
        ‖u x‖ = ‖χ x • g x‖ := by rfl
        _ ≤ ‖χ x‖ * ‖g x‖ := norm_smul_le _ _
        _ ≤ ‖g x‖ := by
          nlinarith [hχnorm, norm_nonneg (g x)]
  have hsubInt : MeasureTheory.Integrable (fun x ↦ g x - u x) μ := by
    -- The localization error is also dominated by `‖g‖`.
    have hdiffAesm :
        MeasureTheory.AEStronglyMeasurable (fun x ↦ g x - u x) μ := by
      exact hgInt.aestronglyMeasurable.sub huAesm
    refine hnormInt.mono' hdiffAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hχ0 : 0 ≤ χ x := (hχ_range x).1
      have hχ1 : χ x ≤ 1 := (hχ_range x).2
      have habs : |1 - χ x| ≤ 1 := by
        have hnonneg : 0 ≤ 1 - χ x := by linarith
        rw [abs_of_nonneg hnonneg]
        linarith
      have hcoeff : ‖1 - χ x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using habs
      have hsmul : g x - u x = (1 - χ x) • g x := by
        calc
          g x - u x = (1 : ℝ) • g x - χ x • g x := by simp [u]
          _ = (1 - χ x) • g x := by rw [sub_smul]
      calc
        ‖g x - u x‖ = ‖(1 - χ x) • g x‖ := by rw [hsmul]
        _ ≤ ‖1 - χ x‖ * ‖g x‖ := norm_smul_le _ _
        _ ≤ ‖g x‖ := by
          nlinarith [hcoeff, norm_nonneg (g x)]
  have hlocError :
      ∫ x, ‖g x - u x‖ ∂μ ≤ ε / 8 := by
    -- The localization error is exactly the tail missed by the compact core.
    refine
      (localizationError_integralNorm_le_tail
        (Ω := Ω) (g := g) (K := K) (χ := χ) hgInt hχ_cont
        hK_compact.isClosed.measurableSet hχ_one hχ_range).trans (le_of_lt hK_tail)
  -- Next approximate the localized field by a smooth compactly supported field.
  have huMem : MeasureTheory.MemLp u 1 μ := by
    simpa [μ, u, MeasureTheory.memLp_one_iff_integrable] using huInt
  obtain ⟨ψ₀, hψ₀_compact, hψ₀_smooth, hψ₀_eLp⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := domainMeasure Ω) (p := (1 : ENNReal)) (by simp) (by simp) huMem (ε := ε / 8)
      (by positivity)
  obtain ⟨η, hη_smooth, hη_compact, hη_subset, hη_one, hη_range⟩ :=
    existsSmoothCompactSupportCutoffOnSupport (Ω := Ω) (u := u) hu_compact hu_subset
  let ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x ↦ η x • ψ₀ x
  have hη_abs : ∀ x, |η x| ≤ 1 := by
    -- The support-restoring cutoff also takes values in `[0, 1]`.
    intro x
    have hη0 : 0 ≤ η x := (hη_range x).1
    have hη1 : η x ≤ 1 := (hη_range x).2
    rwa [abs_of_nonneg hη0]
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    -- Multiplying by the smooth cutoff preserves smoothness.
    change ContDiff ℝ ∞ (η • ψ₀)
    simpa [ψ] using hη_smooth.smul hψ₀_smooth
  have hψ_compact : HasCompactSupport ψ := by
    -- The restored field inherits compact support from the cutoff.
    change HasCompactSupport (η • ψ₀)
    simpa [ψ] using hη_compact.smul_right (f' := ψ₀)
  have hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- The restored field support stays inside `Ω`.
    simpa [ψ] using (tsupport_smul_subset_left η ψ₀).trans hη_subset
  have hψInt : MeasureTheory.Integrable ψ μ := by
    -- Smooth compact support implies `L¹` integrability on the domain measure.
    simpa [μ, MeasureTheory.memLp_one_iff_integrable] using
      (hψ_smooth.continuous.memLp_of_hasCompactSupport (μ := μ) hψ_compact :
        MeasureTheory.MemLp ψ 1 μ)
  have huψ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ u x - ψ x) 1 μ ≤ ENNReal.ofReal (ε / 8) := by
    -- Restoring the support by a cutoff equal to `1` on `tsupport u` does not increase the error.
    calc
      MeasureTheory.eLpNorm (fun x ↦ u x - ψ x) 1 μ
          = MeasureTheory.eLpNorm (fun x ↦ u x - η x • ψ₀ x) 1 μ := by rfl
      _ ≤ MeasureTheory.eLpNorm (fun x ↦ u x - ψ₀ x) 1 μ := by
            simpa [ψ] using
              (cutoffRestore_eLpNormOne_le
                (μ := μ) (u := u) (ψ₀ := ψ₀) (η := η) hη_one hη_abs)
      _ ≤ ENNReal.ofReal (ε / 8) := hψ₀_eLp
  have huψInt : MeasureTheory.Integrable (fun x ↦ u x - ψ x) μ := huInt.sub hψInt
  have huψError :
      ∫ x, ‖u x - ψ x‖ ∂μ ≤ ε / 8 := by
    -- Keep the approximation error in the same integral normal form used by the rest of the proof.
    exact integralNorm_le_of_eLpNorm_one_le huψInt (by positivity) huψ_eLp
  -- Finally saturate the smooth field and integrate the pointwise lower bound.
  let s : Set (EuclideanSpace ℝ (Fin d)) := tsupport u
  have hs_meas : MeasurableSet s := by
    simpa [s] using (isClosed_tsupport (f := u)).measurableSet
  have hs_lt_top : μ s < ⊤ := by
    -- Compact support gives finite domain measure on the support set.
    simpa [μ, s] using
      (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hu_compact.isCompact)
  let M : ℝ := (μ s).toReal
  let δ : ℝ := (ε / 2) / (M + 1)
  have hδ : 0 < δ := by
    -- The saturation parameter is chosen so its support defect stays within the remaining budget.
    dsimp [δ, M]
    positivity
  have hδM :
      δ * M ≤ ε / 2 := by
    have hM_nonneg : 0 ≤ M := by
      simp [M]
    have hM_le : M ≤ M + 1 := by
      nlinarith
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
    have hmul :
        δ * M ≤ δ * (M + 1) := by
      exact mul_le_mul_of_nonneg_left hM_le hδ_nonneg
    have hEq : δ * (M + 1) = ε / 2 := by
      have hM1 : M + 1 ≠ 0 := by
        dsimp [M]
        positivity
      dsimp [δ]
      field_simp [hM1]
    exact hmul.trans_eq hEq
  obtain ⟨v, hv⟩ :=
    existsAdmissibleSaturatedField
      (Ω := Ω) (ψ := ψ) (hψ_smooth.of_le (by simp)) hψ_compact hψ_subset (δ := δ) hδ
  have huNormInt : MeasureTheory.Integrable (fun x ↦ ‖u x‖) μ := huInt.norm
  have hsIndicatorInt :
      MeasureTheory.Integrable (s.indicator fun _ ↦ (1 : ℝ)) μ := by
    -- The indicator of the compact support is integrable because the support has finite measure.
    rw [MeasureTheory.integrable_indicator_iff hs_meas]
    exact MeasureTheory.integrableOn_const hs_lt_top.ne
  have hsScaledInt :
      MeasureTheory.Integrable
        (fun x ↦ δ * s.indicator (fun _ ↦ (1 : ℝ)) x) μ := by
    exact hsIndicatorInt.const_mul δ
  have hsatPointwise :
      ∀ᵐ x ∂μ,
        ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x ≤
          -inner ℝ (u x) (v.toTestFunction x) := by
    -- The pointwise saturation estimate is now expressed through the packaged admissible field.
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [hv x]
      simpa [s] using
        saturatedField_pointwiseLowerBoundOnSupport
          (u := u) (ψ := ψ) (s := s) (hsub := by simpa [s]) hδ x
  have hsatRhsInt :
      MeasureTheory.Integrable
        (fun x ↦ ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x) μ := by
    -- Each term in the integrated lower bound is integrable.
    have haux :
        MeasureTheory.Integrable
          (fun x ↦ 2 * ‖u x - ψ x‖ + δ * s.indicator (fun _ ↦ (1 : ℝ)) x) μ := by
      exact (huψInt.norm.const_mul 2).add hsScaledInt
    refine (huNormInt.sub haux).congr ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      change
        ‖u x‖ - (2 * ‖u x - ψ x‖ + δ * s.indicator (fun _ ↦ (1 : ℝ)) x) =
          ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x
      ring
  have hsatLhsInt :
      MeasureTheory.Integrable
        (fun x ↦ -inner ℝ (u x) (v.toTestFunction x)) μ := by
    exact integrableNegInner_of_admissible huInt v
  have hsatIntegral :
      ∫ x, ‖u x‖ ∂μ - 2 * ∫ x, ‖u x - ψ x‖ ∂μ - δ * M ≤
        -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂μ := by
    have hmono :
        ∫ x, ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ ≤
          ∫ x, -inner ℝ (u x) (v.toTestFunction x) ∂μ := by
      exact MeasureTheory.integral_mono_ae hsatRhsInt hsatLhsInt hsatPointwise
    have hs_indicator :
        ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = M := by
      change ∫ x, s.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ) x ∂μ = M
      simpa [M, μ, MeasureTheory.measureReal_def] using
        (MeasureTheory.integral_indicator_one (μ := μ) hs_meas)
    have hright :
        ∫ x, -inner ℝ (u x) (v.toTestFunction x) ∂μ =
          -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂μ := by
      simpa using
        (MeasureTheory.integral_neg
          (fun x ↦ inner ℝ (u x) (v.toTestFunction x)) (μ := μ))
    have hleft :
        ∫ x, ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ =
          ∫ x, ‖u x‖ ∂μ - 2 * ∫ x, ‖u x - ψ x‖ ∂μ - δ * M := by
      calc
        ∫ x, ‖u x‖ - 2 * ‖u x - ψ x‖ - δ * s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ
            = ∫ x, ‖u x‖ - (2 * ‖u x - ψ x‖ + δ * s.indicator (fun _ ↦ (1 : ℝ)) x) ∂μ := by
                congr 1
                funext x
                ring
        _ = ∫ x, ‖u x‖ ∂μ -
              ∫ x, (2 * ‖u x - ψ x‖ + δ * s.indicator (fun _ ↦ (1 : ℝ)) x) ∂μ := by
                simpa using
                  (MeasureTheory.integral_sub huNormInt ((huψInt.norm.const_mul 2).add hsScaledInt))
        _ = ∫ x, ‖u x‖ ∂μ -
              (∫ x, 2 * ‖u x - ψ x‖ ∂μ +
                ∫ x, δ * s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) := by
                rw [MeasureTheory.integral_add (huψInt.norm.const_mul 2) hsScaledInt]
        _ = ∫ x, ‖u x‖ ∂μ -
              (2 * ∫ x, ‖u x - ψ x‖ ∂μ + δ * M) := by
                rw [MeasureTheory.integral_const_mul 2, MeasureTheory.integral_const_mul δ]
                simp [hs_indicator]
        _ = ∫ x, ‖u x‖ ∂μ - 2 * ∫ x, ‖u x - ψ x‖ ∂μ - δ * M := by ring
    rw [hleft, hright] at hmono
    exact hmono
  have hpairCompare :
      -∫ x, inner ℝ (u x) (v.toTestFunction x) ∂μ ≤
        admissibleDivergencePairing f.toL1 v + ∫ x, ‖g x - u x‖ ∂μ := by
    -- Compare the localized pairing to the weak-gradient pairing using the `L¹` localization error.
    have hpairErr := pairingSubError_ge (Ω := Ω) (g := g) (u := u) hsubInt huInt v
    have hpairEq :
        admissibleDivergencePairing f.toL1 v =
          -∫ x, inner ℝ (g x) (v.toTestFunction x) ∂μ := by
      simpa [μ, g] using W11.pairing_eq_neg_integral_inner f v
    linarith
  have hnormCompare :
      f.integralNormWeakGradient ≤ ∫ x, ‖g x - u x‖ ∂μ + ∫ x, ‖u x‖ ∂μ := by
    -- The pointwise triangle inequality compares `‖g‖` to the localized field plus its error.
    rw [W11.integralNormWeakGradient_def]
    have hpointwise :
        ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖g x - u x‖ + ‖u x‖ := by
      exact Filter.Eventually.of_forall fun x ↦ by
        have htri := norm_add_le (g x - u x) (u x)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
    have hmono :=
      MeasureTheory.integral_mono_ae hnormInt (hsubInt.norm.add huNormInt) hpointwise
    have hadd :
        ∫ x, ‖g x - u x‖ + ‖u x‖ ∂μ =
          ∫ x, ‖g x - u x‖ ∂μ + ∫ x, ‖u x‖ ∂μ := by
      simpa using MeasureTheory.integral_add hsubInt.norm huNormInt
    exact hmono.trans_eq hadd
  have hbudget :
      2 * ∫ x, ‖g x - u x‖ ∂μ + 2 * ∫ x, ‖u x - ψ x‖ ∂μ + δ * M ≤ ε := by
    -- The tail error, smoothing error, and saturation defect fit into the chosen `ε` budget.
    linarith [hlocError, huψError, hδM]
  refine ⟨v, ?_⟩
  -- Assemble the localization, approximation, and saturation estimates.
  linarith [hnormCompare, hsatIntegral, hpairCompare, hbudget]

/-- Helper for Proposition 8.13: the weak-gradient norm integral is bounded
above by the Chapter 8 total variation once one builds an almost-attaining
admissible field. -/
lemma integralNormWeakGradient_le_totalVariation
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) :
    (f.integralNormWeakGradient : EReal) ≤ totalVariation f.toL1 := by
  have hTV_le :
      totalVariation f.toL1 ≤ (f.integralNormWeakGradient : EReal) := by
    -- The already proved upper-bound half shows that `TV` is finite.
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le f.toL1 ?_
    intro v
    exact_mod_cast pairingLeIntegralNormWeakGradient f v
  have hTV_ne_top : totalVariation f.toL1 ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt hTV_le (by simp)
  have hpair_zero :
      admissibleDivergencePairing f.toL1 (AdmissibleTestField.zero Ω) = 0 := by
    -- The zero admissible field has zero divergence, so its pairing vanishes.
    have hdiv_zero :
        admissibleDivergence (AdmissibleTestField.zero Ω) = 0 := by
      funext x
      exact admissibleDivergence_zeroField x
    simp [admissibleDivergencePairing_def, hdiv_zero]
  have hTV_ne_bot : totalVariation f.toL1 ≠ ⊥ := by
    -- The supremum defining total variation dominates the zero admissible field.
    have hzero_le : (0 : EReal) ≤ totalVariation f.toL1 := by
      simpa [hpair_zero] using
        admissibleDivergencePairing_le_totalVariation f.toL1 (AdmissibleTestField.zero Ω)
    exact ne_of_gt <| lt_of_lt_of_le (by simp) hzero_le
  -- Route correction: the compact-support restoration is now handled by the
  -- stronger smooth cutoff `existsSmoothCompactSupportCutoffOnSupport`. The
  -- remaining blocker is the final saturation/endgame assembly packaged in
  -- `existsAlmostSharpAdmissibleField`.
  have hreal :
      f.integralNormWeakGradient ≤ (totalVariation f.toL1).toReal := by
    -- Every ε-sharp admissible field gives a real upper bound by the total-variation supremum.
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨v, hv⟩ := existsAlmostSharpAdmissibleField f hε
    have hpair_le_real :
        admissibleDivergencePairing f.toL1 v ≤ (totalVariation f.toL1).toReal := by
      exact EReal.coe_le_coe_iff.mp <|
        (admissibleDivergencePairing_le_totalVariation f.toL1 v).trans
          (EReal.le_coe_toReal hTV_ne_top)
    linarith
  exact (EReal.coe_le_coe_iff.2 hreal).trans (EReal.coe_toReal_le hTV_ne_bot)

/-- Proposition 8.13 in reusable accessor form: the Chapter 8 total variation
of the underlying `L¹(Ω)` function is the `EReal` lift of the weak-gradient
norm integral attached to the source-facing `W¹,¹(Ω)` owner. -/
theorem totalVariation_eq_integralNormWeakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) :
    totalVariation f.toL1 = (f.integralNormWeakGradient : EReal) := by
  apply le_antisymm
  · -- Bound every admissible divergence pairing by the weak-gradient norm integral.
    refine totalVariation_le_of_forall_admissibleDivergencePairing_le f.toL1 ?_
    intro v
    exact_mod_cast pairingLeIntegralNormWeakGradient f v
  · -- The reverse inequality is the remaining almost-attainment step.
    exact integralNormWeakGradient_le_totalVariation f

/-- Proposition 8.13. For `f ∈ W¹,¹(Ω)`, the Chapter 8 total variation of the
underlying `L¹(Ω)` function is the integral of the norm of the weak gradient. -/
theorem totalVariation_eq_integral_norm_of_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) :
    totalVariation f.toL1 =
      ((∫ x, ‖f.weakGradient x‖ ∂domainMeasure Ω : ℝ) : EReal) := by
  simpa [W11.integralNormWeakGradient_def] using totalVariation_eq_integralNormWeakGradient f

/-- Real-valued form of Proposition 8.13, obtained by applying `EReal.toReal`
to the source-facing `EReal` identity. -/
theorem totalVariation_toReal_eq_integral_norm_of_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W¹,¹(Ω)) :
    (totalVariation f.toL1).toReal = ∫ x, ‖f.weakGradient x‖ ∂domainMeasure Ω := by
  simpa [W11.integralNormWeakGradient_def] using
    congrArg EReal.toReal (totalVariation_eq_integralNormWeakGradient f)

end VariationalRegularization
