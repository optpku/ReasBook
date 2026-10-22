/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.ApproximationBridge
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_14.BV
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.Holder

public section

noncomputable section

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
          exact ENNReal.coe_div hsub_ne_zero
    _ = (NNReal.conjExponent d : ENNReal) := by
          simp [NNReal.conjExponent]

/-- Helper for Theorem 8.16: if a function vanishes outside `Ω`, then its `eLpNorm` on the
restricted domain measure agrees with its ambient-volume `eLpNorm`. -/
lemma eLpNorm_eq_domainMeasure_of_tsupport_subset
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {F : Type*}
    [TopologicalSpace F] [ESeminormedAddMonoid F] [ContinuousENorm F]
    {f : EuclideanSpace ℝ (Fin d) → F}
    {p : ENNReal}
    (hsubset : tsupport f ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    MeasureTheory.eLpNorm f p (domainMeasure Ω) =
      MeasureTheory.eLpNorm f p MeasureTheory.volume := by
  rw [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rw [← MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := MeasureTheory.volume)
    Ω.2.measurableSet]
  -- The indicator is redundant because the function already vanishes off `Ω`.
  apply MeasureTheory.eLpNorm_congr_ae
  refine Filter.Eventually.of_forall fun x ↦ ?_
  by_cases hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d)))
  · simp [hx]
  · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport fun htx ↦ hx (hsubset htx)
    simp [hx, hfx]

/-- Helper for Theorem 8.16: the exact critical BV-to-`L^(criticalExponent d)` estimate for
dimensions `d > 1` on one BV closed ball. -/
theorem criticalClosedBall_exactBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
        MeasureTheory.eLpNorm u.toL1 (criticalExponent d) (domainMeasure Ω) ≤ ENNReal.ofReal C := by
  by_cases hR : R < 0
  · -- A negative-radius closed ball is empty, so the quantitative bound is vacuous.
    refine ⟨0, le_rfl, ?_⟩
    intro u hu
    have : False := by
      simpa [Metric.closedBall_eq_empty.2 hR] using hu
    exact this.elim
  · have hR_nonneg : 0 ≤ R := le_of_not_gt hR
    let q : ℝ≥0 := NNReal.conjExponent d
    let Csob : ℝ≥0 := MeasureTheory.eLpNormLESNormFDerivOneConst
      (μ := MeasureTheory.volume) q
    let C : ℝ := Csob * (R + 1)
    have hdq : NNReal.HolderConjugate d q := by
      -- The smooth Sobolev inequality is stated with the NNReal conjugate exponent.
      simpa [q] using
        (NNReal.HolderConjugate.conjExponent (p := (d : ℝ≥0)) (by exact_mod_cast h1d))
    have hR1_nonneg : 0 ≤ R + 1 := by linarith
    refine ⟨C, by positivity, ?_⟩
    intro u hu
    rcases closedBall_normToL1_and_totalVariationToReal_le hu with ⟨_, htv_le⟩
    have happrox :
        ∀ n : ℕ,
          ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
            ContDiff ℝ ∞ φ ∧
            HasCompactSupport φ ∧
            tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
            MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
              ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
            ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤
              (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := by
      intro n
      -- Approximate `u` by a supported smooth witness at tolerance `1 / (n + 1)`.
      simpa using
        (existsSmoothCompactSupportApprox_of_bv
          (u := u) (ε := 1 / (n + 1 : ℝ)) (by positivity))
    choose φ hφ_smooth hφ_compact hφ_subset hφ_err hφ_deriv using happrox
    have hφ_meas :
        ∀ n, AEStronglyMeasurable (φ n) (domainMeasure Ω) := by
      intro n
      exact (hφ_smooth n).continuous.aestronglyMeasurable
    have h_err_bound :
        ∀ n,
          MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω) ≤
            ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      intro n
      -- Flip the approximation error once; `eLpNorm` is invariant under negation.
      calc
        MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω)
            = MeasureTheory.eLpNorm (fun x ↦ -(u.toL1 x - φ n x)) 1 (domainMeasure Ω) := by
                congr with x
                ring
        _ = MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ n x) 1 (domainMeasure Ω) := by
              rw [MeasureTheory.eLpNorm_neg]
        _ ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := hφ_err n
    have h_err_tendsto :
        Tendsto
          (fun n ↦ MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω))
          Filter.atTop (𝓝 0) := by
      have hupper :
          Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) Filter.atTop (𝓝 0) := by
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat
      -- The approximation error is trapped between `0` and the scalar tolerance.
      exact squeeze_zero (fun n ↦ bot_le)
        (fun n ↦ h_err_bound n) hupper
    have h_tendsto_measure :
        MeasureTheory.TendstoInMeasure (domainMeasure Ω) (fun n ↦ φ n) Filter.atTop u.toL1 := by
      -- `L¹`-small approximation errors force convergence in measure.
      exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        hφ_meas (MeasureTheory.Lp.aestronglyMeasurable u.toL1) h_err_tendsto
    have h_bound_seq :
        ∀ n,
          MeasureTheory.eLpNorm (φ n) (criticalExponent d) (domainMeasure Ω) ≤
            ENNReal.ofReal C := by
      intro n
      have hφ_contdiff1 : ContDiff ℝ 1 (φ n) := (hφ_smooth n).of_le (by norm_num)
      have hφ_fderiv_subset :
          tsupport (fderiv ℝ (φ n)) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) :=
        (tsupport_fderiv_subset ℝ).trans (hφ_subset n)
      have hφ_fderiv_mem :
          MeasureTheory.MemLp (fderiv ℝ (φ n)) 1 (domainMeasure Ω) := by
        -- The Fréchet derivative is continuous with compact support, hence `L¹` on the domain.
        exact
          (hφ_contdiff1.continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport
            (μ := domainMeasure Ω) ((hφ_compact n).fderiv ℝ)
      have hφ_fderiv_int :
          MeasureTheory.Integrable (fun x ↦ ‖fderiv ℝ (φ n) x‖) (domainMeasure Ω) := by
        simpa [MeasureTheory.memLp_one_iff_integrable] using hφ_fderiv_mem.norm
      have hφ_fderiv_eLp :
          MeasureTheory.eLpNorm (fderiv ℝ (φ n)) 1 (domainMeasure Ω) =
            ENNReal.ofReal (∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω) := by
        rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        symm
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφ_fderiv_int
          (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      have hderiv_le_R1 :
          ∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω ≤ R + 1 := by
        have hone_div_le : 1 / (n + 1 : ℝ) ≤ 1 := by
          have hpos : (0 : ℝ) < 1 := by positivity
          have hle : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          simpa using one_div_le_one_div_of_le hpos hle
        calc
          ∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω
              ≤ (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := hφ_deriv n
          _ ≤ R + 1 / (n + 1 : ℝ) := add_le_add htv_le le_rfl
          _ ≤ R + 1 := add_le_add_left hone_div_le R
      -- Apply the smooth Sobolev inequality on ambient volume, then transport it back to the
      -- restricted domain measure using the support information.
      calc
        MeasureTheory.eLpNorm (φ n) (criticalExponent d) (domainMeasure Ω)
            = MeasureTheory.eLpNorm (φ n) q MeasureTheory.volume := by
                rw [criticalExponent_eq_coe_conjExponent h1d,
                  eLpNorm_eq_domainMeasure_of_tsupport_subset (Ω := Ω) (f := φ n) (p := (q : ENNReal))
                    (hφ_subset n)]
        _ ≤ (Csob : ENNReal) * MeasureTheory.eLpNorm (fderiv ℝ (φ n)) 1 MeasureTheory.volume := by
              simpa [Csob, q] using
                (MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one
                  (μ := MeasureTheory.volume) (u := φ n) hφ_contdiff1 (hφ_compact n) hdq)
        _ = (Csob : ENNReal) * MeasureTheory.eLpNorm (fderiv ℝ (φ n)) 1 (domainMeasure Ω) := by
              rw [eLpNorm_eq_domainMeasure_of_tsupport_subset
                (Ω := Ω) (f := fderiv ℝ (φ n)) (p := (1 : ENNReal)) hφ_fderiv_subset]
        _ = (Csob : ENNReal) * ENNReal.ofReal
              (∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω) := by
              rw [hφ_fderiv_eLp]
        _ ≤ (Csob : ENNReal) * ENNReal.ofReal (R + 1) := by
              gcongr
              exact hderiv_le_R1
        _ = ENNReal.ofReal C := by
              rw [show C = (Csob : ℝ) * (R + 1) by rfl,
                ← ENNReal.ofReal_mul (by positivity) hR1_nonneg]
    have hbound_eventually :
        ∀ᶠ n in Filter.atTop,
          MeasureTheory.eLpNorm (φ n) (criticalExponent d) (domainMeasure Ω) ≤ ENNReal.ofReal C :=
      Filter.Eventually.of_forall h_bound_seq
    -- Pass the uniform smooth critical-exponent bound through convergence in measure.
    exact
      MeasureTheory.eLpNorm_le_of_tendstoInMeasure hbound_eventually h_tendsto_measure hφ_meas

/-- Helper for Theorem 8.16: the exact critical BV-to-`L^(criticalExponent d)` estimate for
dimensions `d > 1`. -/
theorem criticalExponentEstimate
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h1d : 1 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 (criticalExponent d) (domainMeasure Ω) := by
  -- Package the exact-exponent bound by placing `u` in the BV closed ball of radius `‖u‖`.
  rcases criticalClosedBall_exactBound (d := d) (Ω := Ω) h1d hΩ ‖u‖ with ⟨C, _, hC⟩
  refine ⟨(MeasureTheory.Lp.memLp u.toL1).aestronglyMeasurable, ?_⟩
  have hu_ball : u ∈ Metric.closedBall (0 : BV Ω) ‖u‖ := by
    -- The center is `0`, so closed-ball membership is exactly the tautological norm bound.
    simpa [Metric.mem_closedBall, dist_zero_right] using le_rfl
  exact lt_of_le_of_lt (hC hu_ball) ENNReal.ofReal_lt_top

/-- Helper for Theorem 8.16: the one-dimensional smooth compact-support endpoint estimate is the
quantitative owner that turns the recovery-sequence route into an `L∞` seminorm bound. -/
lemma smoothCompactSupport_endpointELpNormBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {φ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset : tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin 1)))) :
    MeasureTheory.eLpNorm φ ⊤ (domainMeasure Ω) ≤
      ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω) := by
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  let g : ℝ → ℝ := φ ∘ e
  have hg_smooth : ContDiff ℝ ∞ g := by
    -- Transport the smooth compact-support scalar from `EuclideanSpace ℝ (Fin 1)` to `ℝ`.
    simpa [g, e] using hφ_smooth.comp e.contDiff
  have hg_compact : HasCompactSupport g := by
    -- The `funUnique` equivalence preserves compact support.
    simpa [g, e] using hφ_compact.comp_left (g := e) (by simp)
  have hderiv_int :
      Integrable (fun y : ℝ ↦ ‖deriv g y‖) := by
    -- The transported derivative is continuous with compact support, hence integrable.
    exact
      (hg_smooth.continuous_deriv le_rfl).integrable_of_hasCompactSupport hg_compact.deriv
  have hderiv_dom :
      Integrable (fun x : EuclideanSpace ℝ (Fin 1) ↦ ‖fderiv ℝ φ x‖) (domainMeasure Ω) := by
    have hφ_fderiv_mem :
        MeasureTheory.MemLp (fderiv ℝ φ) 1 (domainMeasure Ω) := by
      -- The Fréchet derivative is continuous with compact support on the domain.
      exact
        (hφ_smooth.of_le (by norm_num)).continuous_fderiv (by norm_num)
          |>.memLp_of_hasCompactSupport
            (μ := domainMeasure Ω) (hφ_compact.fderiv ℝ)
    simpa [MeasureTheory.memLp_one_iff_integrable] using hφ_fderiv_mem.norm
  have hφ_fderiv_subset :
      tsupport (fderiv ℝ φ) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin 1))) :=
    (tsupport_fderiv_subset ℝ).trans hφ_subset
  have hlintegral_fderiv :
      ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ∂MeasureTheory.volume =
        ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω) := by
    -- Rewrite the derivative integral onto ambient volume once so the transported real-line bound
    -- can close directly against the target right-hand side.
    calc
      ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ∂MeasureTheory.volume
          = MeasureTheory.eLpNorm (fderiv ℝ φ) 1 MeasureTheory.volume := by
              rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      _ = MeasureTheory.eLpNorm (fderiv ℝ φ) 1 (domainMeasure Ω) := by
            rw [← eLpNorm_eq_domainMeasure_of_tsupport_subset
              (Ω := Ω) (f := fderiv ℝ φ) (p := (1 : ENNReal)) hφ_fderiv_subset]
      _ = ENNReal.ofReal (∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω) := by
            rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
              MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hderiv_dom]
  have hpointwise :
      ∀ x : EuclideanSpace ℝ (Fin 1),
        ‖φ x‖ ≤ ∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω := by
    intro x
    have hx_real :
        ‖g (e.symm x)‖ₑ ≤
          ∫⁻ y in Set.Iic (e.symm x), ‖deriv g y‖ₑ ∂MeasureTheory.volume :=
      hg_compact.enorm_le_lintegral_Ici_deriv (hf := hg_smooth.of_le (by norm_num)) (e.symm x)
    have hderiv_le :
        ∀ y : ℝ, ‖deriv g y‖ₑ ≤ ‖fderiv ℝ φ (e y)‖ₑ := by
      intro y
      have hcomp :
          deriv g y = (fderiv ℝ φ (e y) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) (e 1) := by
        -- Differentiate the transported scalar once using the linear chain rule.
        simpa [g, e, ContinuousLinearMap.fderiv] using
          (fderiv_comp_deriv (x := y)
            (l := φ) (f := e)
            ((hφ_smooth.of_le (by norm_num)).differentiableAt)
            e.differentiableAt)
      calc
        ‖deriv g y‖ₑ = ‖(fderiv ℝ φ (e y) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) (e 1)‖ₑ := by
          rw [hcomp]
        _ ≤ ‖fderiv ℝ φ (e y)‖ₑ * ‖e 1‖ₑ := ContinuousLinearMap.le_opENorm _ _
        _ = ‖fderiv ℝ φ (e y)‖ₑ := by
          have hnorm_e : ‖e 1‖ = 1 := by
            simpa [e] using e.norm_map (1 : ℝ)
          simp [hnorm_e]
    have hglobal :
        ∫⁻ y, ‖deriv g y‖ₑ ∂MeasureTheory.volume ≤
          ENNReal.ofReal (∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω) := by
      calc
        ∫⁻ y, ‖deriv g y‖ₑ ∂MeasureTheory.volume
            ≤ ∫⁻ y, ‖fderiv ℝ φ (e y)‖ₑ ∂MeasureTheory.volume := by
                exact MeasureTheory.lintegral_mono fun y ↦ hderiv_le y
        _ = ∫⁻ z, ‖fderiv ℝ φ z‖ₑ ∂MeasureTheory.volume := by
              -- The `funUnique` equivalence preserves volume, so composing with `e` does not
              -- change the derivative integral.
              simpa [e] using
                (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm.lintegral_comp
                  (show Measurable (fun z : EuclideanSpace ℝ (Fin 1) ↦ ‖fderiv ℝ φ z‖ₑ) by
                    fun_prop)
        _ = ENNReal.ofReal (∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω) := hlintegral_fderiv
    have hx_volume :
        ‖g (e.symm x)‖ₑ ≤ ENNReal.ofReal (∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω) := by
      calc
        ‖g (e.symm x)‖ₑ
            ≤ ∫⁻ y in Set.Iic (e.symm x), ‖deriv g y‖ₑ ∂MeasureTheory.volume := hx_real
        _ ≤ ∫⁻ y, ‖deriv g y‖ₑ ∂MeasureTheory.volume := by
              exact MeasureTheory.lintegral_mono_set (by intro y hy; simp)
        _ ≤ ENNReal.ofReal (∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω) := hglobal
    have hderiv_nonneg :
        0 ≤ ∫ y, ‖fderiv ℝ φ y‖ ∂domainMeasure Ω := by
      exact MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _
    -- Convert the `ENNReal` pointwise estimate back to the requested real-valued bound.
    simpa [g, e] using (ENNReal.ofReal_le_ofReal_iff hderiv_nonneg).1 hx_volume
  -- Move the endpoint norm onto ambient volume, then close by the pointwise FTC bound.
  rw [eLpNorm_eq_domainMeasure_of_tsupport_subset (Ω := Ω) (f := φ) (p := (⊤ : ENNReal))
    hφ_subset]
  exact
    MeasureTheory.eLpNorm_le_of_ae_bound
      (Filter.Eventually.of_forall hpointwise)

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains on one BV closed ball. -/
theorem endpointClosedBall_eLpNormBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
        MeasureTheory.eLpNorm u.toL1 ⊤ (domainMeasure Ω) ≤ ENNReal.ofReal C := by
  by_cases hR : R < 0
  · -- A negative-radius closed ball is empty, so the endpoint `L∞` seminorm estimate is vacuous.
    refine ⟨0, le_rfl, ?_⟩
    intro u hu
    have : False := by
      simpa [Metric.closedBall_eq_empty.2 hR] using hu
    exact this.elim
  · have hR_nonneg : 0 ≤ R := le_of_not_gt hR
    have hR1_nonneg : 0 ≤ R + 1 := by linarith
    refine ⟨R + 1, hR1_nonneg, ?_⟩
    intro u hu
    rcases closedBall_normToL1_and_totalVariationToReal_le hu with ⟨_, htv_le⟩
    have happrox :
        ∀ n : ℕ,
          ∃ φ : EuclideanSpace ℝ (Fin 1) → ℝ,
            ContDiff ℝ ∞ φ ∧
            HasCompactSupport φ ∧
            tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin 1))) ∧
            MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
              ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
            ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤
              (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := by
      intro n
      -- Reuse the same strict-BV smooth approximant family as in the finite-critical branch.
      simpa using
        (existsSmoothCompactSupportApprox_of_bv
          (u := u) (ε := 1 / (n + 1 : ℝ)) (by positivity))
    choose φ hφ_smooth hφ_compact hφ_subset hφ_err hφ_deriv using happrox
    have hφ_meas :
        ∀ n, AEStronglyMeasurable (φ n) (domainMeasure Ω) := by
      intro n
      exact (hφ_smooth n).continuous.aestronglyMeasurable
    have h_err_bound :
        ∀ n,
          MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω) ≤
            ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      intro n
      -- Flip the approximation error once; `eLpNorm` is invariant under negation.
      calc
        MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω)
            = MeasureTheory.eLpNorm (fun x ↦ -(u.toL1 x - φ n x)) 1 (domainMeasure Ω) := by
                congr with x
                ring
        _ = MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ n x) 1 (domainMeasure Ω) := by
              rw [MeasureTheory.eLpNorm_neg]
        _ ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := hφ_err n
    have h_err_tendsto :
        Tendsto
          (fun n ↦ MeasureTheory.eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω))
          Filter.atTop (𝓝 0) := by
      have hupper :
          Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) Filter.atTop (𝓝 0) := by
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat
      -- The `L¹` approximation error is squeezed between `0` and the reciprocal budget.
      exact squeeze_zero (fun n ↦ bot_le) (fun n ↦ h_err_bound n) hupper
    have h_tendsto_measure :
        MeasureTheory.TendstoInMeasure (domainMeasure Ω) (fun n ↦ φ n) Filter.atTop u.toL1 := by
      -- The same `L¹` convergence-in-measure bridge closes the endpoint transfer.
      exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
        hφ_meas (MeasureTheory.Lp.aestronglyMeasurable u.toL1) h_err_tendsto
    have h_bound_seq :
        ∀ n,
          MeasureTheory.eLpNorm (φ n) ⊤ (domainMeasure Ω) ≤ ENNReal.ofReal (R + 1) := by
      intro n
      have hone_div_le : 1 / (n + 1 : ℝ) ≤ 1 := by
        have hpos : (0 : ℝ) < 1 := by positivity
        have hle : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        simpa using one_div_le_one_div_of_le hpos hle
      have hderiv_le_R1 :
          ∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω ≤ R + 1 := by
        calc
          ∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω
              ≤ (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := hφ_deriv n
          _ ≤ R + 1 / (n + 1 : ℝ) := add_le_add htv_le le_rfl
          _ ≤ R + 1 := add_le_add_left hone_div_le R
      -- Consume the smooth endpoint owner on each approximant before passing to the limit.
      calc
        MeasureTheory.eLpNorm (φ n) ⊤ (domainMeasure Ω)
            ≤ ENNReal.ofReal (∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω) := by
                exact
                  smoothCompactSupport_endpointELpNormBound
                    (Ω := Ω) (hφ_smooth n) (hφ_compact n) (hφ_subset n)
        _ ≤ ENNReal.ofReal (R + 1) := ENNReal.ofReal_le_ofReal hderiv_le_R1
    have hbound_eventually :
        ∀ᶠ n in Filter.atTop,
          MeasureTheory.eLpNorm (φ n) ⊤ (domainMeasure Ω) ≤ ENNReal.ofReal (R + 1) :=
      Filter.Eventually.of_forall h_bound_seq
    -- Pass the uniform smooth endpoint bound through convergence in measure.
    exact
      MeasureTheory.eLpNorm_le_of_tendstoInMeasure hbound_eventually h_tendsto_measure hφ_meas

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains on one BV closed ball. -/
theorem endpointClosedBall_aeBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ ⦃u : BV Ω⦄, u ∈ Metric.closedBall (0 : BV Ω) R →
        ∀ᵐ x ∂domainMeasure Ω, ‖u.toL1 x‖ ≤ C := by
  by_cases hR : R < 0
  · -- A negative-radius closed ball is empty, so the endpoint a.e. estimate is vacuous.
    refine ⟨0, le_rfl, ?_⟩
    intro u hu
    have : False := by
      simpa [Metric.closedBall_eq_empty.2 hR] using hu
    exact this.elim
  · have hR_nonneg : 0 ≤ R := le_of_not_gt hR
    rcases endpointClosedBall_eLpNormBound (Ω := Ω) hΩ R with ⟨C₀, hC₀_nonneg, hC₀⟩
    refine ⟨C₀ + 1, by linarith, ?_⟩
    intro u hu
    have hnorm_top :
        MeasureTheory.eLpNorm u.toL1 ⊤ (domainMeasure Ω) ≤ ENNReal.ofReal C₀ :=
      hC₀ hu
    have hess :
        MeasureTheory.essSup (fun x ↦ ‖u.toL1 x‖ₑ) (domainMeasure Ω) ≤ ENNReal.ofReal C₀ := by
      simpa [MeasureTheory.eLpNorm_exponent_top, MeasureTheory.eLpNormEssSup_eq_essSup_enorm] using
        hnorm_top
    have hlt :
        MeasureTheory.essSup (fun x ↦ ‖u.toL1 x‖ₑ) (domainMeasure Ω) <
          ENNReal.ofReal (C₀ + 1) := by
      refine lt_of_le_of_lt hess ?_
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hae_lt :
        ∀ᵐ x ∂domainMeasure Ω, ‖u.toL1 x‖ₑ < ENNReal.ofReal (C₀ + 1) :=
      MeasureTheory.ae_lt_of_essSup_lt hlt
    -- Convert the strict essential-supremum bound back to the requested real-valued a.e. estimate.
    filter_upwards [hae_lt] with x hx
    have hx' : ENNReal.ofReal ‖u.toL1 x‖ < ENNReal.ofReal (C₀ + 1) := by
      simpa using hx
    exact
      le_of_lt <| (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hx'

/-- Helper for Theorem 8.16: the one-dimensional endpoint BV-to-`L∞` estimate on bounded
domains. -/
theorem endpointExponentEstimate
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 1))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin 1))))
    (u : BV Ω) :
    MeasureTheory.MemLp u.toL1 ⊤ (domainMeasure Ω) := by
  -- Package the endpoint a.e. bound by placing `u` in the BV closed ball of radius `‖u‖`.
  rcases endpointClosedBall_aeBound (Ω := Ω) hΩ ‖u‖ with ⟨C, _, hC⟩
  have hu_ball : u ∈ Metric.closedBall (0 : BV Ω) ‖u‖ := by
    -- The center is `0`, so closed-ball membership is exactly the tautological norm bound.
    simpa [Metric.mem_closedBall, dist_zero_right] using le_rfl
  exact
    MeasureTheory.memLp_top_of_bound
      ((MeasureTheory.Lp.memLp u.toL1).aestronglyMeasurable) C (hC hu_ball)

end BVCompactness

end VariationalRegularization
