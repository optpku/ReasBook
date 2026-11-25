/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.SmoothVariation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.Mollification
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

open scoped ContDiff

namespace BVCompactness

/-- Helper for Theorem 8.16: a compact set inside `Ω` admits a smooth scalar cutoff whose support
is compactly contained in `Ω` and which is identically `1` on that compact core. -/
lemma existsSmoothCompactSupportCutoffOnCompactSubset
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧
      tsupport η ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn η 1 K ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, hL_compact, hKL, hL_subset⟩ :=
    exists_compact_between hK_compact Ω.2 hK_subset
  obtain ⟨η, hη_cmdiff, hη_range, hη_support, hη_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      isOpen_interior hK_compact.isClosed hKL
  have hη_tsupport_subset : tsupport η ⊆ L := by
    rw [tsupport, hη_support]
    exact closure_minimal interior_subset hL_compact.isClosed
  have hη_tsupport_compact : IsCompact (tsupport η) :=
    hL_compact.of_isClosed_subset (isClosed_tsupport (f := η)) hη_tsupport_subset
  have hη_compact : HasCompactSupport η := by
    exact HasCompactSupport.intro hη_tsupport_compact fun x hx ↦
      image_eq_zero_of_notMem_tsupport hx
  refine ⟨η, hη_cmdiff.contDiff, hη_compact, hη_tsupport_subset.trans hL_subset, ?_, ?_⟩
  · intro x hx
    exact (hη_one x).1 hx
  · intro x
    exact hη_range ⟨x, rfl⟩

/-- Helper for Theorem 8.16: cutting an integrable scalar field by a smooth cutoff equal to `1`
on a compact core produces an `L¹` tail error controlled by the mass outside that core. -/
lemma cutoffTail_eLpNorm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ η : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    {δ : ℝ}
    (hφInt : MeasureTheory.Integrable φ (domainMeasure Ω))
    (hK_compact : IsCompact K)
    (hη_cont : Continuous η)
    (hη_one : Set.EqOn η 1 K)
    (hη_range : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (htail :
      ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖φ x‖ ∂domainMeasure Ω ≤ δ) :
    MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal δ := by
  have hcutoffAesm :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ η x * φ x) (domainMeasure Ω) := by
    -- The cutoff localization is measurable because the cutoff is continuous and `φ` is `L¹`.
    exact hη_cont.aestronglyMeasurable.mul hφInt.aestronglyMeasurable
  have hcutoffInt :
      MeasureTheory.Integrable (fun x ↦ η x * φ x) (domainMeasure Ω) := by
    -- The range restriction `0 ≤ η ≤ 1` keeps the localized field dominated by `|φ|`.
    refine hφInt.norm.mono' hcutoffAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hη0 : 0 ≤ η x := (hη_range x).1
      have hη1 : η x ≤ 1 := (hη_range x).2
      have hηnorm : ‖η x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hη0] using hη1
      calc
        ‖η x * φ x‖ = ‖η x‖ * ‖φ x‖ := norm_mul _ _
        _ ≤ ‖φ x‖ := by
          nlinarith [hηnorm, norm_nonneg (φ x)]
  have hcutoffErrorInt :
      MeasureTheory.Integrable (fun x ↦ φ x - η x * φ x) (domainMeasure Ω) := by
    -- The cutoff defect is integrable as a difference of two `L¹` scalars.
    exact hφInt.sub hcutoffInt
  have hcutoffError_le :
      ∫ x, ‖φ x - η x * φ x‖ ∂domainMeasure Ω ≤
        ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖φ x‖ ∂domainMeasure Ω := by
    let s : Set (EuclideanSpace ℝ (Fin d)) := (Ω : Set (EuclideanSpace ℝ (Fin d))) \ K
    have hs_meas : MeasurableSet s := Ω.2.measurableSet.diff hK_compact.isClosed.measurableSet
    have htailInt :
        MeasureTheory.Integrable (s.indicator fun x ↦ ‖φ x‖) (domainMeasure Ω) := by
      -- The tail indicator keeps the integrable norm density in `L¹`.
      exact hφInt.norm.indicator hs_meas
    have hpointwise :
        ∀ᵐ x ∂domainMeasure Ω, ‖φ x - η x * φ x‖ ≤ s.indicator (fun x ↦ ‖φ x‖) x := by
      -- On the compact core the cutoff is exactly `1`; on the tail, `0 ≤ η ≤ 1` bounds the
      -- localization defect by the ambient norm.
      rw [domainMeasure_def]
      refine
        (MeasureTheory.ae_restrict_iff'
          (μ := (MeasureTheory.Measure.euclideanHausdorffMeasure d :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
          (s := (Ω : Set (EuclideanSpace ℝ (Fin d))))
          Ω.2.measurableSet).2 ?_
      refine Filter.Eventually.of_forall fun x hxΩ ↦ ?_
      by_cases hKx : x ∈ K
      · have hηx : η x = 1 := hη_one hKx
        have hsx : x ∉ s := by
          simp [s, hKx]
        simp [s, hsx, hηx]
      · have hη0 : 0 ≤ η x := (hη_range x).1
        have hη1 : η x ≤ 1 := (hη_range x).2
        have habs : |1 - η x| ≤ 1 := by
          have hnonneg : 0 ≤ 1 - η x := by linarith
          rw [abs_of_nonneg hnonneg]
          linarith
        have hcoeff : ‖1 - η x‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using habs
        have hnorm :
            ‖φ x - η x * φ x‖ ≤ ‖φ x‖ := by
          have hrewrite : φ x - η x * φ x = (1 - η x) * φ x := by ring
          calc
            ‖φ x - η x * φ x‖ = ‖(1 - η x) * φ x‖ := by rw [hrewrite]
            _ = ‖(1 - η x) • φ x‖ := by simp [smul_eq_mul]
            _ ≤ ‖1 - η x‖ * ‖φ x‖ := norm_smul_le _ _
            _ ≤ ‖φ x‖ := by
                nlinarith [hcoeff, norm_nonneg (φ x)]
        have hsx : x ∈ s := by
          simp [s, hxΩ, hKx]
        simpa [s, Set.indicator_of_mem hsx] using hnorm
    -- Integrate the pointwise tail domination on the restricted domain measure.
    refine
      (MeasureTheory.integral_mono_ae hcutoffErrorInt.norm htailInt hpointwise).trans ?_
    rw [MeasureTheory.integral_indicator hs_meas]
  -- For `p = 1`, convert the integral bound back to the `eLpNorm` normal form.
  calc
    MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω)
        = ENNReal.ofReal (∫ x, ‖φ x - η x * φ x‖ ∂domainMeasure Ω) := by
            rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
            symm
            exact MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hcutoffErrorInt
    _ ≤ ENNReal.ofReal δ := by
          exact ENNReal.ofReal_le_ofReal (hcutoffError_le.trans htail)

/-- Helper for Theorem 8.16: once both the ambient approximation error and the cutoff defect
consume half of the `L¹` budget, the triangle inequality closes the full error estimate. -/
lemma smoothApprox_triangle_eLpNorm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω))
    (hψMem : MeasureTheory.MemLp ψ 1 (domainMeasure Ω))
    (hφ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2))
    (hψ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2)) :
    MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  have hε_half_nonneg : 0 ≤ ε / 2 := by
    linarith
  have huMem : MeasureTheory.MemLp u.toL1 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.memLp u.toL1
  have hleft :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ u.toL1 x - φ x) (domainMeasure Ω) :=
    (huMem.sub hφMem).aestronglyMeasurable
  have hright :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ φ x - ψ x) (domainMeasure Ω) :=
    (hφMem.sub hψMem).aestronglyMeasurable
  have hsum :
      MeasureTheory.eLpNorm
          ((fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x))
          1 (domainMeasure Ω) ≤
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) +
          MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) := by
    -- Keep the triangle inequality on the two explicit `L¹` defects, avoiding extra transport.
    exact MeasureTheory.eLpNorm_add_le hleft hright (by simp : (1 : ENNReal) ≤ 1)
  have hrewrite :
      (fun x ↦ u.toL1 x - ψ x) =
        (fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x) := by
    ext x
    simp [Pi.add_apply]
  calc
    MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω)
        = MeasureTheory.eLpNorm
            ((fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x))
            1 (domainMeasure Ω) := by
              rw [hrewrite]
    _ ≤ MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) +
          MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) := hsum
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add hφ_eLp hψ_eLp
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε_half_nonneg hε_half_nonneg, add_halves]

/-- Helper for Theorem 8.16: multiplying an ambient smooth approximant by a compactly supported
cutoff restores support inside `Ω` while preserving the final `L¹` error budget. -/
lemma cutoffRestoreSmoothL1Approx
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {φ η : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_compact : HasCompactSupport φ)
    (hη_smooth : ContDiff ℝ ∞ η)
    (hη_compact : HasCompactSupport η)
    (hη_subset : tsupport η ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hφ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2))
    (hcutoffError_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2)) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ ψ ∧
      HasCompactSupport ψ ∧
      tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  let ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ η x * φ x
  have hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω) := by
    -- Smooth compact support places the ambient approximant in `L¹(domainMeasure Ω)`.
    exact hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    -- Multiplying by the smooth cutoff preserves smoothness of the ambient approximant.
    simpa [ψ] using hη_smooth.mul hφ_smooth
  have hψ_compact : HasCompactSupport ψ := by
    -- The restored approximant inherits compact support from the cutoff.
    change HasCompactSupport (η * φ)
    simpa [ψ] using hη_compact.mul_right (f' := φ)
  have hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- The topological support of the restored approximant stays inside the cutoff support.
    simpa [ψ] using (tsupport_mul_subset_left (f := η) (g := φ)).trans hη_subset
  have hψMem : MeasureTheory.MemLp ψ 1 (domainMeasure Ω) := by
    -- Smooth compact support keeps the restored approximant in `L¹(domainMeasure Ω)`.
    exact hψ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hψ_compact
  refine ⟨ψ, hψ_smooth, hψ_compact, hψ_subset, ?_⟩
  -- The pure `L¹` estimate is now isolated in a small triangle-inequality helper.
  exact
    smoothApprox_triangle_eLpNorm_le
      (Ω := Ω) (u := u) (φ := φ) (ψ := ψ) (ε := ε) hε
      hφMem hψMem hφ_eLp (by simpa [ψ] using hcutoffError_eLp)

/-- Helper for Theorem 8.16: every `BV(Ω)` element admits a smooth scalar approximation with
compact support inside `Ω` and arbitrarily small `L¹` error on `domainMeasure Ω`. -/
theorem existsSmoothCompactSupportL1Approx_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  have hε_half : 0 < ε / 2 := by linarith
  -- Route correction: separate the ambient approximation, tail cutoff estimate, and final
  -- support-restoration step so the theorem stays a short assembly owner.
  have huMem : MeasureTheory.MemLp u.toL1 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.memLp u.toL1
  obtain ⟨φ, hφ_compact, hφ_smooth, hφ_eLp⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := domainMeasure Ω) (p := (1 : ENNReal)) (by simp) (by simp) huMem
      (ε := ε / 2) hε_half
  have hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω) := by
    exact hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact
  have hφInt : MeasureTheory.Integrable φ (domainMeasure Ω) := by
    simpa [MeasureTheory.memLp_one_iff_integrable] using hφMem
  obtain ⟨K, hK_subset, hK_compact, hK_tail⟩ :=
    existsCompactSubset_tailIntegral_lt
      (Ω := Ω) (h := fun x ↦ ‖φ x‖) hφInt.norm (fun _ ↦ norm_nonneg _) hε_half
  obtain ⟨η, hη_smooth, hη_compact, hη_subset, hη_one, hη_range⟩ :=
    existsSmoothCompactSupportCutoffOnCompactSubset
      (Ω := Ω) hK_compact hK_subset
  have hcutoffError_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2) := by
    -- The cutoff estimate is now its own theorem-local bridge.
    exact
      cutoffTail_eLpNorm_le
        (Ω := Ω) (φ := φ) (η := η) (K := K) (δ := ε / 2)
        hφInt hK_compact hη_smooth.continuous hη_one hη_range
        (le_of_lt <| by simpa using hK_tail)
  -- Finish by packaging the localized approximant through the dedicated support-restoration
  -- helper, rather than replaying the whole triangle argument inline.
  exact
    cutoffRestoreSmoothL1Approx
      (Ω := Ω) (u := u) (φ := φ) (η := η) (ε := ε) (le_of_lt hε)
      hφ_smooth hφ_compact hη_smooth hη_compact hη_subset hφ_eLp hcutoffError_eLp

/-- Ambient smooth approximation on a BV extension domain. The constant is
uniform over `u` and the error tolerance. The approximants have compact support
in the whole space; no zero boundary trace is imposed on `u`. -/
theorem existsSmoothCompactSupportApprox_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : BV Ω) (ε : ℝ), 0 < ε →
      ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
          ENNReal.ofReal ε ∧
        (∫ x, ‖fderiv ℝ φ x‖ ∂MeasureTheory.volume) ≤ C * ‖u‖ := by
  obtain ⟨E, K, C, hK, hC, hext, hsupp, hE⟩ :=
    HasBoundedBVExtension.exists_extension_with_bound Ω
  refine ⟨C, hC, ?_⟩
  intro u ε hε
  let B : ℝ := C * ‖u‖
  have hB : 0 ≤ B := mul_nonneg hC (norm_nonneg u)
  let r : ℝ := ε / (B + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  have hrB : r * B ≤ ε := by
    have heq : r * (B + 1) = ε := by
      dsimp [r]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  let κ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨r / 2, r, by positivity, by linarith⟩
  let ρ : EuclideanSpace ℝ (Fin d) → ℝ := κ.normed MeasureTheory.volume
  let f : EuclideanSpace ℝ (Fin d) → ℝ := (E u).toL1
  let φ : EuclideanSpace ℝ (Fin d) → ℝ :=
    MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume
  have hf : MeasureTheory.Integrable f := Mollification.ambient_integrable (E u)
  have hφsmooth : ContDiff ℝ ∞ φ :=
    κ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      κ.contDiff_normed hf.locallyIntegrable
  have hsupport : ∀ᵐ x ∂MeasureTheory.volume, x ∉ K → (E u).toL1 x = 0 := by
    simpa only [domainMeasure_top_eq_volume] using hsupp u
  have hφcompact : HasCompactSupport φ :=
    Mollification.convolution_hasCompactSupport κ.hasCompactSupport_normed hK hsupport
  have hφint : MeasureTheory.Integrable φ :=
    κ.integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hμ : domainMeasure Ω ≤ MeasureTheory.volume := by
    simpa only [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
      (MeasureTheory.Measure.restrict_le_self (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
        (s := (Ω : Set (EuclideanSpace ℝ (Fin d)))))
  refine ⟨φ, hφsmooth, hφcompact, ?_, ?_⟩
  · have huInt := MeasureTheory.memLp_one_iff_integrable.1 (MeasureTheory.Lp.memLp u.toL1)
    have hdiff : MeasureTheory.Integrable (fun x ↦ u.toL1 x - φ x) (domainMeasure Ω) :=
      huInt.sub (hφint.mono_measure hμ)
    have herr := Mollification.integral_norm_sub_convolution_le (E u) hK hsupport
      κ.hasCompactSupport_normed κ.contDiff_normed κ.nonneg_normed κ.integral_normed (by
        simpa only [κ.support_normed_eq] using
          (Metric.ball_subset_closedBall : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆
            Metric.closedBall 0 r))
    have hint : (∫ x, ‖u.toL1 x - φ x‖ ∂domainMeasure Ω) ≤ ε := by
      calc
        _ = ∫ x, ‖f x - φ x‖ ∂domainMeasure Ω := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hext u] with x hx
          simp only [f, hx]
        _ ≤ ∫ x, ‖f x - φ x‖ ∂MeasureTheory.volume :=
          MeasureTheory.integral_mono_measure hμ
            (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hf.sub hφint).norm
        _ ≤ r * ‖E u‖ := herr
        _ ≤ r * B := mul_le_mul_of_nonneg_left (hE u) hr.le
        _ ≤ ε := hrB
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
      ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hdiff]
    exact ENNReal.ofReal_le_ofReal hint
  · exact (Mollification.convolution_integral_norm_fderiv_le (E u) κ.hasCompactSupport_normed
      κ.contDiff_normed κ.nonneg_normed κ.integral_normed hφcompact).trans (hE u)

/-- Independent `L¹` and derivative budgets, with the corrected ambient
support and domain-dependent BV norm bound. -/
theorem existsSmoothCompactSupportApprox_of_bv_twoBudgetsDeriv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : BV Ω) (δ η : ℝ), 0 < δ → 0 < η →
      ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal δ ∧
        (∫ x, ‖fderiv ℝ φ x‖ ∂MeasureTheory.volume) ≤ C * ‖u‖ + η := by
  obtain ⟨C, hC, happrox⟩ := existsSmoothCompactSupportApprox_of_bv (Ω := Ω)
  refine ⟨C, hC, ?_⟩
  intro u δ η hδ hη
  obtain ⟨φ, hs, hc, herr, hd⟩ := happrox u δ hδ
  exact ⟨φ, hs, hc, herr, hd.trans (by linarith)⟩

/-- The ambient TV version of the same approximation, obtained from the
smooth derivative identity after constructing the approximants. -/
theorem existsSmoothCompactSupportApprox_of_bv_totalVariationToReal_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : BV Ω) (ε : ℝ), 0 < ε →
      ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ∃ hφ : MeasureTheory.MemLp φ 1
          (domainMeasure (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))),
        ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε ∧
        (totalVariation (hφ.toLp φ)).toReal ≤ C * ‖u‖ := by
  obtain ⟨C, hC, happrox⟩ := existsSmoothCompactSupportApprox_of_bv (Ω := Ω)
  refine ⟨C, hC, ?_⟩
  intro u ε hε
  obtain ⟨φ, hs, hc, herr, hd⟩ := happrox u ε hε
  have hm : MeasureTheory.MemLp φ 1
      (domainMeasure (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))) :=
    hs.continuous.memLp_of_hasCompactSupport hc
  refine ⟨φ, hm, hs, hc, herr, ?_⟩
  have heq := smoothCompactSupport_totalVariationToReal_eq_integral_norm_fderiv
    (Ω := (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))))
    (hs.of_le (by simp)) hc (Set.subset_univ _)
  simp only [domainMeasure_top_eq_volume] at heq
  exact heq.trans_le hd

end BVCompactness
end VariationalRegularization
