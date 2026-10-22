/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

public section

noncomputable section

namespace VariationalRegularization

open scoped BigOperators

variable {d : ℕ}

/-- The canonical inclusion from `L^p(Ω)` to `L¹(Ω)` on a finite-measure domain. -/
def lpToL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  ⟨(f : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ),
    MeasureTheory.Lp.antitone (E := ℝ) (μ := domainMeasure Ω)
      (show (1 : ENNReal) ≤ p from Fact.out) f.2⟩

/-- `lpToL1` preserves the underlying almost-everywhere equivalence class. -/
@[simp] theorem lpToL1_toAEEqFun
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    ((lpToL1 f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
        (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) =
      (f : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ) := by
  simp [lpToL1]

/-- The `L¹(Ω)` image produced by `lpToL1` agrees almost everywhere with the original
`L^p(Ω)` representative. -/
theorem lpToL1_ae_eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 f =ᵐ[domainMeasure Ω] f := by
  simp [lpToL1]

/-- Helper for Theorem 8.18: rewrite the divergence in the stable projection spelling used by the
continuity and compact-support APIs. -/
lemma admissibleDivergence_eq_sum_projFDeriv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v x =
      ∑ i : Fin d, (ContinuousLinearMap.proj (R := ℝ) i)
        (fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ))) := by
  -- Replace raw coordinate access by the canonical projection map once and for all.
  rw [admissibleDivergence_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rfl

/-- Helper for Theorem 8.18: rewrite the divergence in the kernel-stable `PiLp` coordinate spelling
used by the derivative regularity lemmas. -/
lemma admissibleDivergence_eq_sum_ofLpFDeriv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (x : EuclideanSpace ℝ (Fin d)) :
    admissibleDivergence v x =
      ∑ i : Fin d,
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
  -- This is the same divergence formula, spelled in the `PiLp` normal form used by the kernel.
  rw [admissibleDivergence_def]

/-- Helper for Theorem 8.18: each coordinate summand in the divergence formula is continuous. -/
lemma admissibleDivergenceSummandContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (i : Fin d) :
    Continuous
      (fun x ↦
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  -- Route correction: Lean normalizes Euclidean coordinates to the direct coordinate spelling here,
  -- so we prove continuity in that canonical form.
  -- The bundled derivative-evaluation map is continuous for `C¹` test fields.
  have hderiv :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))) := by
    have happly :
        Continuous
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
            (fderiv ℝ v.toTestFunction p.1) p.2) :=
      v.toTestFunction.contDiff.continuous_fderiv_apply (by simp)
    -- Freeze the derivative direction to the `i`th basis vector.
    have hfreeze :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin d) ↦
            (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              (fderiv ℝ v.toTestFunction p.1) p.2)
              (x, WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      happly.comp (continuous_id.prodMk continuous_const)
    simpa [PiLp.toLp_single] using hfreeze
  -- Postcompose with the continuous coordinate projection.
  have happly :
      Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
  have hcoord :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ)))) :=
    happly.comp hderiv
  simpa using hcoord

/-- Helper for Theorem 8.18: each coordinate summand in the divergence formula has compact
support. -/
lemma admissibleDivergenceSummandHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (i : Fin d) :
    HasCompactSupport
      (fun x ↦
        (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  -- Route correction: the support lemma should use the same direct coordinate spelling as the
  -- main divergence formula, avoiding another projection-vs-coordinate normalization step.
  -- First keep the derivative evaluation in the stable fixed-direction spelling.
  have hderiv :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))) := by
    simpa using
      (v.toTestFunction.hasCompactSupport.fderiv_apply ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ))))
  -- Then push compact support through the zero-preserving coordinate projection.
  have hcoord :
      HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ)))) :=
    hderiv.comp_left (g := fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) rfl
  simpa using hcoord

/-- Helper for Theorem 8.18: the admissible divergence is continuous. -/
lemma admissibleDivergenceContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    Continuous (admissibleDivergence v) := by
  have hsum :
      admissibleDivergence v =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    -- Use the dedicated normalization lemma once at function level.
    funext x
    exact admissibleDivergence_eq_sum_ofLpFDeriv v x
  -- Rewrite once to the kernel-stable `PiLp` normal form and sum the coordinate lemmas there.
  rw [hsum]
  exact continuous_finsetSum Finset.univ fun i _ ↦ admissibleDivergenceSummandContinuous v i

/-- Helper for Theorem 8.18: the normalized `PiLp` divergence sum has compact support. -/
lemma admissibleDivergenceNormalizedHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i) := by
  let φ : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x ↦
    (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i
  have hφ : ∀ i ∈ Finset.univ, HasCompactSupport (φ i) := by
    intro i _
    simpa [φ] using admissibleDivergenceSummandHasCompactSupport v i
  have hsum :
      (∑ i : Fin d, φ i) =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    -- Normalize the sum of functions to the pointwise finite sum.
    funext x
    simp [φ]
  -- Sum the coordinate support lemmas before transporting back to the source-facing divergence.
  rw [← hsum]
  exact HasCompactSupport.finset_sum (s := Finset.univ) hφ

/-- Helper for Theorem 8.18: the admissible divergence has compact support. -/
lemma admissibleDivergenceHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    HasCompactSupport (admissibleDivergence v) := by
  have hsum :
      admissibleDivergence v =
        fun x : EuclideanSpace ℝ (Fin d) ↦
          ∑ i : Fin d, (fderiv ℝ v.toTestFunction x (PiLp.single 2 i (1 : ℝ))).ofLp i := by
    -- Use the dedicated normalization lemma once at function level.
    funext x
    exact admissibleDivergence_eq_sum_ofLpFDeriv v x
  -- Transport the normalized compact-support statement back to `admissibleDivergence`.
  rw [hsum]
  exact admissibleDivergenceNormalizedHasCompactSupport v

/-- Helper for Theorem 8.18: the admissible divergence belongs to `L∞(Ω)`. -/
lemma admissibleDivergenceMemLpTop
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.MemLp (admissibleDivergence v) ⊤ (domainMeasure Ω) :=
  (admissibleDivergenceContinuous v).memLp_top_of_hasCompactSupport
    (admissibleDivergenceHasCompactSupport v) (domainMeasure Ω)

/-- Helper for Theorem 8.18: pairing against a fixed admissible divergence defines a continuous
linear functional on `L¹(Ω)`. -/
def totalVariationPairingCLM
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) →L[ℝ] ℝ :=
  let divLp : MeasureTheory.Lp ℝ ⊤ (domainMeasure Ω) :=
    MeasureTheory.MemLp.toLp (admissibleDivergence v) (admissibleDivergenceMemLpTop v)
  ((ContinuousLinearMap.apply ℝ ℝ) divLp).comp
    (ContinuousLinearMap.lpPairing (μ := domainMeasure Ω) (p := (1 : ENNReal))
      (q := (⊤ : ENNReal)) (ContinuousLinearMap.mul ℝ ℝ))

/-- Helper for Theorem 8.18: the pairing continuous linear map evaluates to the original
divergence pairing. -/
lemma totalVariationPairingCLM_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω)
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    totalVariationPairingCLM v f = admissibleDivergencePairing f v := by
  -- Unfold the packaging once, then use the canonical `Lp` pairing integral formula.
  rw [admissibleDivergencePairing_def, totalVariationPairingCLM]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  -- Normalize the `L∞` witness back to the original divergence function.
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp (admissibleDivergenceMemLpTop v)] with x hx
  simp [hx]

/-- Helper for Theorem 8.18: continuous linear functionals remain continuous on the weak space. -/
lemma continuousEvalOnWeakSpace
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) :
    Continuous fun x : WeakSpace ℝ E ↦ L ((toWeakSpace ℝ E).symm x) := by
  -- Route correction: evaluation is part of the definition of the weak topology.
  change Continuous (fun x : WeakBilin (topDualPairing ℝ E).flip ↦ L x)
  exact WeakBilin.eval_continuous (B := (topDualPairing ℝ E).flip) L

/-- Helper for Theorem 8.18: each fixed admissible divergence pairing is lower semicontinuous on
the weak `L¹(Ω)` space. -/
lemma totalVariationPairingOnWeakSpace_lowerSemicontinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    LowerSemicontinuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        ((totalVariationPairingCLM v
          ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) : EReal)) := by
  -- A continuous real-valued weak-space evaluation stays lower semicontinuous after casting to
  -- `EReal`.
  have hcont :
      Continuous
        (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
          totalVariationPairingCLM v
            ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) :=
    continuousEvalOnWeakSpace (totalVariationPairingCLM v)
  exact continuous_coe_real_ereal.comp_lowerSemicontinuous
    hcont.lowerSemicontinuous EReal.coe_strictMono.monotone

/-- Helper for Theorem 8.18: the weak-space pullback of `totalVariation` is the supremum of the
fixed-field pairings. -/
lemma totalVariationOnWeakSpace_eq_iSup
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
      totalVariation ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) =
      fun x ↦
        ⨆ v : AdmissibleTestField Ω,
          ((totalVariationPairingCLM v
            ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) : EReal) := by
  -- Expand `totalVariation` to its defining supremum and rewrite each term through the CLM
  -- computation lemma.
  funext x
  rw [totalVariation_def, sSup_range]
  simp [totalVariationPairingCLM_apply]

/-- Helper for Theorem 8.18: `lpToL1` preserves addition. -/
lemma lpToL1_add
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f g : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 (f + g) = lpToL1 f + lpToL1 g := by
  -- Both sides are represented by the same almost-everywhere sum.
  refine MeasureTheory.Lp.ext ?_
  filter_upwards with x
  rfl

/-- Helper for Theorem 8.18: `lpToL1` preserves scalar multiplication. -/
lemma lpToL1_smul
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (c : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1 (c • f) = c • lpToL1 f := by
  -- Both sides are represented by the same almost-everywhere scalar multiple.
  refine MeasureTheory.Lp.ext ?_
  filter_upwards with x
  rfl

/-- Helper for Theorem 8.18: the canonical inclusion `lpToL1` satisfies the standard finite-measure
norm bound. -/
lemma lpToL1_norm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    ‖lpToL1 f‖ ≤
      (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal * ‖f‖ := by
  -- Compare the `eLpNorm`s first; the `Lp` norm statement is just the corresponding `toReal`
  -- normalization.
  let fμ : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ := f
  let C : ENNReal :=
    domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)
  have hLp1 : MeasureTheory.MemLp fμ 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.mem_Lp_iff_memLp.mp <|
      MeasureTheory.Lp.antitone (E := ℝ) (μ := domainMeasure Ω)
        (show (1 : ENNReal) ≤ p from Fact.out) f.2
  have hcompare :
      MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω) ≤
        MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (show (1 : ENNReal) ≤ p from Fact.out) fμ.aestronglyMeasurable
  have hC_ne_top : C ≠ ⊤ := by
    have hp_inv_le_one : 1 / p.toReal ≤ 1 := by
      by_cases hp_top : p = ⊤
      · simp [hp_top]
      · have hp_one : 1 ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hp_top (show (1 : ENNReal) ≤ p from Fact.out)
        simpa [one_div] using inv_le_one_of_one_le₀ hp_one
    have hC_nonneg : 0 ≤ 1 / (1 : ENNReal).toReal - 1 / p.toReal := by
      simpa using sub_nonneg.mpr hp_inv_le_one
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        hC_nonneg
        (MeasureTheory.measure_ne_top (domainMeasure Ω) Set.univ)).ne
  have hcompareRealENN :
      ENNReal.toReal (MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω)) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C) := by
    exact
      (ENNReal.toReal_le_toReal hLp1.2.ne
        (ENNReal.mul_ne_top f.2.ne hC_ne_top)).2 hcompare
  -- Rewrite both `Lp` norms to the same `eLpNorm` spelling and apply the real-valued inequality.
  have hcompareReal :
      ‖lpToL1 f‖ ≤ C.toReal * ‖f‖ := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def, lpToL1_toAEEqFun]
    simpa [C, fμ, ENNReal.toReal_mul, mul_comm, mul_left_comm, mul_assoc] using hcompareRealENN
  simpa [C] using hcompareReal

/-- Helper for Theorem 8.18: `lpToL1` is linear on finite-measure domains. -/
def lpToL1LinearMap
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)] :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) →ₗ[ℝ] MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  { toFun := lpToL1
    map_add' := lpToL1_add
    map_smul' := lpToL1_smul }

/-- Helper for Theorem 8.18: `lpToL1` upgrades to a continuous linear map on finite-measure
domains. -/
def lpToL1CLM
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)] :
    MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  LinearMap.mkContinuous
    lpToL1LinearMap
    (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal
    lpToL1_norm_le

/-- Helper for Theorem 8.18: the continuous linear inclusion `lpToL1CLM` evaluates to `lpToL1`. -/
@[simp] lemma lpToL1CLM_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    lpToL1CLM f = lpToL1 f := by
  -- `mkContinuous` does not change the underlying linear map on points.
  rw [lpToL1CLM, LinearMap.mkContinuous_apply]
  rfl

/-- Helper for Theorem 8.18: weak-space transport through the continuous inclusion agrees with the
canonical weak `L¹(Ω)` image. -/
lemma weakSpace_map_lpToL1CLM_apply
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    WeakSpace.map (lpToL1CLM (Ω := Ω) (p := p))
      (toWeakSpace ℝ (MeasureTheory.Lp ℝ p (domainMeasure Ω)) f) =
        toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (lpToL1 f) := by
  -- Both weak-space maps are identity maps on the underlying carrier once the CLM is evaluated.
  rw [WeakSpace.map_apply, lpToL1CLM_apply]
  rfl

/-- Lower semicontinuity of `totalVariation` on the weak topology of the canonical `L¹(Ω)`
carrier. -/
theorem totalVariation_lowerSemicontinuous_weakL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    LowerSemicontinuous
      (fun x : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) ↦
        totalVariation ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)) := by
  -- Rewrite `totalVariation` as an `iSup` of fixed-field pairings and use stability of lower
  -- semicontinuity under `iSup`.
  rw [totalVariationOnWeakSpace_eq_iSup]
  exact lowerSemicontinuous_iSup fun v =>
    totalVariationPairingOnWeakSpace_lowerSemicontinuous v

/-- Sequential weak-`L¹` liminf form of weak lower semicontinuity for `totalVariation`. -/
theorem totalVariation_le_liminf_of_tendsto_weakL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    (hf : Filter.Tendsto
      (fun n ↦ toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (f n))
      Filter.atTop
      (nhds (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) g))) :
    totalVariation g ≤ Filter.liminf (fun n ↦ totalVariation (f n)) Filter.atTop := by
  let Φ : WeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) → EReal := fun x ↦
    totalVariation ((toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω))).symm x)
  -- Lower semicontinuity controls the neighborhood `liminf` at the weak limit point.
  have hsc :
      Φ (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) g) ≤
        Filter.liminf Φ
          (nhds (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) g)) :=
    (totalVariation_lowerSemicontinuous_weakL1 (Ω := Ω)).le_liminf
      (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) g)
  -- The sequence `liminf` dominates the neighborhood `liminf` along the convergent weak trajectory.
  have hcomp :
      Filter.liminf Φ
          (nhds (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) g)) ≤
        Filter.liminf
          (fun n ↦ Φ (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (f n)))
          Filter.atTop :=
    hf.liminf_le_liminf_comp
  -- Unfold the weak-space functional only at the very end.
  exact (le_trans hsc hcomp).trans_eq (by simp [Φ])

/-- Theorem 8.18. If a sequence converges weakly in `L^p(Ω)` for `1 ≤ p < ∞`, then the
Chapter 8 total-variation functional of its canonical `L¹(Ω)` images satisfies the
corresponding liminf inequality. -/
theorem totalVariation_le_liminf_of_tendsto_weakLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [Fact (p < (⊤ : ENNReal))]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {f : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    {g : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : Filter.Tendsto
      (fun n ↦ toWeakSpace ℝ (MeasureTheory.Lp ℝ p (domainMeasure Ω)) (f n))
      Filter.atTop
      (nhds (toWeakSpace ℝ (MeasureTheory.Lp ℝ p (domainMeasure Ω)) g))) :
    totalVariation (lpToL1 g) ≤
      Filter.liminf (fun n ↦ totalVariation (lpToL1 (f n))) Filter.atTop := by
  -- Transport the weak convergence through the continuous inclusion `L^p(Ω) → L¹(Ω)`.
  have htransport :
      Filter.Tendsto
        (fun n ↦
          WeakSpace.map (lpToL1CLM (Ω := Ω) (p := p))
            (toWeakSpace ℝ (MeasureTheory.Lp ℝ p (domainMeasure Ω)) (f n)))
        Filter.atTop
        (nhds
          (WeakSpace.map (lpToL1CLM (Ω := Ω) (p := p))
            (toWeakSpace ℝ (MeasureTheory.Lp ℝ p (domainMeasure Ω)) g))) :=
    ((WeakSpace.map (lpToL1CLM (Ω := Ω) (p := p))).continuous.tendsto _).comp hf
  have hweakL1 :
      Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (lpToL1 (f n)))
        Filter.atTop
        (nhds (toWeakSpace ℝ (MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (lpToL1 g))) := by
    simpa [weakSpace_map_lpToL1CLM_apply] using htransport
  -- Finish with the already-proved weak-`L¹` liminf theorem.
  exact totalVariation_le_liminf_of_tendsto_weakL1 (Ω := Ω) (f := fun n ↦ lpToL1 (f n))
    (g := lpToL1 g) hweakL1

end VariationalRegularization
