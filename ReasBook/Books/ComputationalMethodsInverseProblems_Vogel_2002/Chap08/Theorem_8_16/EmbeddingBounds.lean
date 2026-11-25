/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.ApproximationRecovery
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.DomainRegularity
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

public section

noncomputable section

open scoped ContDiff NNReal

/-!
The critical and endpoint bounds use ambient smooth approximation after a bounded
BV extension. The same extension constant controls every function in a BV ball;
restriction back to Ω can only decrease the `eLpNorm`. No zero-trace density
statement is used.
-/

namespace VariationalRegularization

variable {d : ℕ}

namespace BVCompactness

/-- The critical Sobolev exponent used in Theorem 8.16, with the one-dimensional
endpoint interpreted as `∞`. -/
def criticalExponent (d : ℕ) : ENNReal :=
  if d = 1 then ⊤ else (d : ENNReal) / ((d - 1 : ℕ) : ENNReal)

/-- The one-dimensional endpoint convention for `criticalExponent`. -/
theorem criticalExponent_one :
    criticalExponent 1 = ⊤ := by
  -- The source convention is built into the definition by the `d = 1` branch.
  simp [criticalExponent]

/-- Away from the endpoint case `d = 1`, `criticalExponent` is the usual ratio
`d / (d - 1)`. -/
theorem criticalExponent_eq_div_of_ne_one
    {d : ℕ}
    (hd1 : d ≠ 1) :
    criticalExponent d = (d : ENNReal) / ((d - 1 : ℕ) : ENNReal) := by
  -- Unfold the branch definition once and discard the one-dimensional case.
  simp [criticalExponent, hd1]

/-- The critical Sobolev exponent is at least `1` in positive dimension. -/
theorem one_le_criticalExponent
    (hd : 1 ≤ d) :
    1 ≤ criticalExponent d := by
  by_cases h1 : d = 1
  · -- In one dimension the endpoint is `∞`, so the lower bound is immediate.
    simp [criticalExponent, h1]
  · have h1d : 1 < d := lt_of_le_of_ne hd (by simpa [eq_comm] using h1)
    rw [criticalExponent_eq_div_of_ne_one h1]
    have hden_ne_zero : ((d - 1 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt h1d).ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hden_ne_zero) (Or.inl (by simp))]
    -- The denominator `d - 1` is bounded above by the numerator `d`.
    rw [one_mul]
    exact_mod_cast Nat.sub_le d 1

/-- The canonical lower-bound witness for the critical Sobolev exponent in positive
dimension. -/
theorem factOneLeCriticalExponent
    (hd : 1 ≤ d) :
    Fact (1 ≤ criticalExponent d) :=
  ⟨one_le_criticalExponent hd⟩

/-- The endpoint exponent `∞` carries the canonical lower-bound witness required by
the `Lᵖ` API. -/
instance instFactOneLeTopENNReal :
    Fact (1 ≤ (⊤ : ENNReal)) :=
  ⟨le_top⟩

/-- Helper for Theorem 8.16: every `BV(Ω)` element already belongs to `L¹(Ω)` on its
canonical carrier. -/
theorem toL1_memLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 1 (domainMeasure Ω) := by
  -- The `BV(Ω)` carrier is a subtype of `L¹(Ω)`, so its underlying function is in `L¹` by
  -- construction.
  exact MeasureTheory.Lp.memLp u.toL1

/-- Helper for Theorem 8.16: BV closed-ball membership controls the underlying `L¹(Ω)` norm. -/
theorem normToL1_le_of_mem_closedBall
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {R : ℝ}
    {u : BV Ω}
    (hu : u ∈ Metric.closedBall (0 : BV Ω) R) :
    ‖u.toL1‖ ≤ R := by
  -- Rewrite the closed-ball hypothesis to the BV norm bound and then use the contractive `toL1`
  -- projection.
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  exact (BV.normToL1_le u).trans hu

/-- Helper for Theorem 8.16: BV closed-ball membership also bounds the total variation term. -/
theorem totalVariationToReal_le_of_mem_closedBall
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {R : ℝ}
    {u : BV Ω}
    (hu : u ∈ Metric.closedBall (0 : BV Ω) R) :
    (totalVariation u.toL1).toReal ≤ R := by
  -- The BV norm already dominates the total-variation contribution on the canonical carrier.
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  exact (BV.lpTotalVariationToReal_le_norm u).trans hu

/-- Helper for Theorem 8.16: BV closed-ball membership yields the exact `L¹` and total-variation
side bounds needed by the exact-exponent owners. -/
theorem closedBall_normToL1_and_totalVariationToReal_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {R : ℝ}
    {u : BV Ω}
    (hu : u ∈ Metric.closedBall (0 : BV Ω) R) :
    ‖u.toL1‖ ≤ R ∧ (totalVariation u.toL1).toReal ≤ R := by
  -- Package the two radius bounds once so downstream analytic proofs can consume them together.
  exact ⟨normToL1_le_of_mem_closedBall hu, totalVariationToReal_le_of_mem_closedBall hu⟩

/-- Helper for Theorem 8.16: in dimensions `d > 1`, the source-facing critical exponent agrees
with the canonical Hölder conjugate of `d` on the `NNReal` surface used by the smooth Sobolev
inequality. -/
lemma criticalExponent_eq_coe_conjExponent
    (h1d : 1 < d) :
    criticalExponent d = (NNReal.conjExponent d : ENNReal) := by
  have hd_ne_one : d ≠ 1 := Nat.ne_of_gt h1d
  have hsub_ne_zero : ((d - 1 : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt h1d).ne'
  -- Normalize the branch definition once, then compare it to the explicit NNReal conjugate
  -- exponent formula `d / (d - 1)`.
  calc
    criticalExponent d = (d : ENNReal) / ((d - 1 : ℕ) : ENNReal) :=
      criticalExponent_eq_div_of_ne_one hd_ne_one
    _ = ((((d : ℝ≥0) / ((d - 1 : ℕ) : ℝ≥0)) : ℝ≥0) : ENNReal) := by
          simpa using (ENNReal.coe_div (p := (d : ℝ≥0)) hsub_ne_zero).symm
    _ = (NNReal.conjExponent d : ENNReal) := by
          simp [NNReal.conjExponent]

/-- Helper for Theorem 8.16: if a function vanishes outside `Ω`, then its `eLpNorm` on the
restricted domain measure agrees with its ambient-volume `eLpNorm`. -/
lemma eLpNorm_eq_domainMeasure_of_tsupport_subset
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {F : Type*}
    [TopologicalSpace F] [ESeminormedAddMonoid F]
    {f : EuclideanSpace ℝ (Fin d) → F}
    {p : ENNReal}
    (hsubset : tsupport f ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    MeasureTheory.eLpNorm f p (domainMeasure Ω) =
      MeasureTheory.eLpNorm f p MeasureTheory.volume := by
  have heq : (Ω : Set (EuclideanSpace ℝ (Fin d))).indicator f = f := by
    funext x
    by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d)))
    · simp [hx]
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport fun htx ↦ hx (hsubset htx)
      simp [hx, hfx]
  calc
    _ = MeasureTheory.eLpNorm ((Ω : Set (EuclideanSpace ℝ (Fin d))).indicator f) p MeasureTheory.volume := by
      simpa only [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
        (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
          (μ := MeasureTheory.volume) (f := f) (p := p) (s := (Ω : Set (EuclideanSpace ℝ (Fin d))))
          Ω.2.measurableSet).symm
    _ = _ := by rw [heq]

/-- Transfer any ambient smooth Sobolev estimate through extension and recovery.
The domain-dependent constant is uniform on the BV closed ball. -/
lemma closedBall_eLpNormBound_of_ambient_smoothEstimate
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] (p : ENNReal) (Cs : ℝ≥0)
    (hsmooth : ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      MeasureTheory.eLpNorm φ p MeasureTheory.volume ≤ (Cs : ENNReal) *
        ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂MeasureTheory.volume))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
      MeasureTheory.eLpNorm u.toL1 p (domainMeasure Ω) ≤ ENNReal.ofReal C := by
  obtain ⟨Ce, hCe, hrec⟩ := existsSmoothCompactSupportRecoverySeq_of_bv (Ω := Ω)
  let C : ℝ := (Cs : ℝ) * (Ce * max R 0)
  refine ⟨C, by positivity, ?_⟩
  intro u hu
  obtain ⟨φ, hφ⟩ := hrec u
  have huR : ‖u‖ ≤ max R 0 :=
    (show ‖u‖ ≤ R by simpa [Metric.mem_closedBall, dist_zero_right] using hu).trans (le_max_left _ _)
  have hμ : domainMeasure Ω ≤ MeasureTheory.volume := by
    simpa only [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
      (MeasureTheory.Measure.restrict_le_self (μ := (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
        (s := (Ω : Set (EuclideanSpace ℝ (Fin d)))))
  have hlim := recoverySeq_tendstoInMeasure u φ (fun n ↦ (hφ n).1) (fun n ↦ (hφ n).2.2.1)
  have hbound (n : ℕ) : MeasureTheory.eLpNorm (φ n) p (domainMeasure Ω) ≤ ENNReal.ofReal C := by
    calc
      _ ≤ MeasureTheory.eLpNorm (φ n) p MeasureTheory.volume :=
        MeasureTheory.eLpNorm_mono_measure _ hμ
      _ ≤ (Cs : ENNReal) * ENNReal.ofReal (∫ x, ‖fderiv ℝ (φ n) x‖ ∂MeasureTheory.volume) :=
        hsmooth (φ n) (hφ n).1 (hφ n).2.1
      _ ≤ (Cs : ENNReal) * ENNReal.ofReal (Ce * max R 0) := by
        gcongr
        exact (hφ n).2.2.2.trans (mul_le_mul_of_nonneg_left huR hCe)
      _ = ENNReal.ofReal C := by
        simp only [C, ENNReal.ofReal_mul Cs.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact MeasureTheory.eLpNorm_le_of_tendstoInMeasure
    (Filter.Eventually.of_forall hbound) hlim (fun n ↦ (hφ n).1.continuous.aestronglyMeasurable)

/-- The critical BV bound on a bounded extension domain, obtained from ambient
smooth Sobolev estimates. -/
theorem criticalClosedBall_exactBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    [HasBoundedBVExtension Ω]
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
      MeasureTheory.eLpNorm u.toL1 (criticalExponent d) (domainMeasure Ω) ≤ ENNReal.ofReal C := by
  let _ := hΩ
  let q : ℝ≥0 := NNReal.conjExponent d
  apply closedBall_eLpNormBound_of_ambient_smoothEstimate (criticalExponent d)
    (MeasureTheory.eLpNormLESNormFDerivOneConst
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) q) ?_ R
  intro φ hs hc
  have hs1 : ContDiff ℝ 1 φ := hs.of_le (by simp)
  have hdq : NNReal.HolderConjugate d q :=
    NNReal.HolderConjugate.conjExponent (by exact_mod_cast h1d)
  have hdq' : NNReal.HolderConjugate (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) q := by
    simpa using hdq
  have hdi : MeasureTheory.Integrable (fderiv ℝ φ) MeasureTheory.volume :=
    (hs1.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ)
  rw [criticalExponent_eq_coe_conjExponent h1d]
  have h := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one
    (μ := MeasureTheory.volume) (u := φ) hs1 hc hdq'
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
    ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hdi] at h
  exact h

/-- Helper for Theorem 8.16: the exact critical BV-to-`L^(criticalExponent d)` estimate for
dimensions `d > 1`. -/
theorem criticalExponentEstimate
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    [HasBoundedBVExtension Ω]
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 (criticalExponent d) (domainMeasure Ω) := by
  -- Package the exact-exponent bound by placing `u` in the BV closed ball of radius `‖u‖`.
  rcases criticalClosedBall_exactBound (d := d) (Ω := Ω) h1d hΩ ‖u‖ with ⟨C, _, hC⟩
  refine ⟨(MeasureTheory.Lp.memLp u.toL1).aestronglyMeasurable, ?_⟩
  have hu_ball : u ∈ Metric.closedBall (0 : BV Ω) ‖u‖ := by
    -- The center is `0`, so closed-ball membership is exactly the tautological norm bound.
    simp [Metric.mem_closedBall, dist_zero_right]
  exact lt_of_le_of_lt (hC hu_ball) ENNReal.ofReal_lt_top

/-- Helper for Theorem 8.16: the one-dimensional smooth compact-support endpoint estimate is the
quantitative owner that turns the recovery-sequence route into an `L∞` seminorm bound. -/
lemma smoothCompactSupport_endpointELpNormBound
    {φ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MeasureTheory.eLpNorm φ ⊤ MeasureTheory.volume ≤
      ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂MeasureTheory.volume) := by
  let b := OrthonormalBasis.singleton (Fin 1) ℝ
  let e : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) := b.repr
  let g : ℝ → ℝ := fun t ↦ φ (e t)
  have hgs : ContDiff ℝ 1 g := (hs.of_le (by simp)).comp e.toContinuousLinearEquiv.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph e.toHomeomorph
  have hdi : MeasureTheory.Integrable (fderiv ℝ φ) MeasureTheory.volume :=
    ((hs.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
      (hc.fderiv ℝ)
  have hder (y : ℝ) : deriv g y = fderiv ℝ φ (e y) (e 1) := by
    have hin : HasDerivAt (fun t : ℝ ↦ e t) (e 1) y :=
      e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.hasDerivAt
    exact ((hs.differentiable (by simp) (e y)).hasFDerivAt.comp_hasDerivAt y hin).deriv
  have hnorm (y : ℝ) : ‖deriv g y‖ₑ ≤ ‖fderiv ℝ φ (e y)‖ₑ := by
    rw [hder]
    simpa only [e.enorm_map, enorm_one, mul_one] using
      (ContinuousLinearMap.le_opENorm (fderiv ℝ φ (e y)) (e 1))
  rw [MeasureTheory.eLpNorm_exponent_top]
  apply MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound
  apply Filter.Eventually.of_forall
  intro x
  have hpt := HasCompactSupport.enorm_le_lintegral_Ici_deriv hgs hgc (e.symm x)
  calc
    ‖φ x‖ₑ = ‖g (e.symm x)‖ₑ := by simp [g]
    _ ≤ ∫⁻ y in Set.Iic (e.symm x), ‖deriv g y‖ₑ := hpt
    _ ≤ ∫⁻ y, ‖deriv g y‖ₑ := by
      simpa only [MeasureTheory.Measure.restrict_univ] using
        (MeasureTheory.lintegral_mono_set (f := fun y ↦ ‖deriv g y‖ₑ) (μ := MeasureTheory.volume)
          (Set.subset_univ (Set.Iic (e.symm x))))
    _ ≤ ∫⁻ y, ‖fderiv ℝ φ (e y)‖ₑ := MeasureTheory.lintegral_mono hnorm
    _ = ∫⁻ z, ‖fderiv ℝ φ z‖ₑ := by
      exact b.measurePreserving_repr.lintegral_comp
        ((hs.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).continuous_fderiv one_ne_zero).enorm.measurable
    _ = ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂MeasureTheory.volume) :=
      (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hdi).symm

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains on one BV closed ball. -/
theorem endpointClosedBall_eLpNormBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    [HasBoundedBVExtension Ω]
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
      MeasureTheory.eLpNorm u.toL1 ⊤ (domainMeasure Ω) ≤ ENNReal.ofReal C := by
  let _ := hΩ
  apply closedBall_eLpNormBound_of_ambient_smoothEstimate ⊤ 1 ?_ R
  intro φ hs hc
  simpa only [ENNReal.coe_one, one_mul] using smoothCompactSupport_endpointELpNormBound hs hc

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains on one BV closed ball. -/
theorem endpointClosedBall_aeBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    [HasBoundedBVExtension Ω] (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
      ∀ᵐ x ∂domainMeasure Ω, ‖u.toL1 x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := endpointClosedBall_eLpNormBound hΩ R
  refine ⟨C, hC, ?_⟩
  intro u hu
  have hb := hbound hu
  rw [MeasureTheory.eLpNorm_exponent_top] at hb
  filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup u.toL1 (domainMeasure Ω)] with x hx
  have hx' : ENNReal.ofReal ‖u.toL1 x‖ ≤ ENNReal.ofReal C := by
    simpa only [ofReal_norm] using hx.trans hb
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 hx'

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains. -/
theorem endpointExponentEstimate
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    [HasBoundedBVExtension Ω]
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 ⊤ (domainMeasure Ω) := by
  -- Package the endpoint a.e. bound by placing `u` in the BV closed ball of radius `‖u‖`.
  rcases endpointClosedBall_aeBound (Ω := Ω) hΩ ‖u‖ with ⟨C, _, hC⟩
  have hu_ball : u ∈ Metric.closedBall (0 : BV Ω) ‖u‖ := by
    -- The center is `0`, so closed-ball membership is exactly the tautological norm bound.
    simp [Metric.mem_closedBall, dist_zero_right]
  exact
    MeasureTheory.memLp_top_of_bound
      ((MeasureTheory.Lp.memLp u.toL1).aestronglyMeasurable) C (hC hu_ball)

end BVCompactness

end VariationalRegularization
