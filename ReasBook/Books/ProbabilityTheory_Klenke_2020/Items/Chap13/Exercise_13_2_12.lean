/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal Topology

universe u v

noncomputable section

section

/- Exercise 13.2.12 is `source-facing`: it keeps the textbook hypotheses and conclusions in terms
of random variables, but its `core/canonical` owner abstraction is weak convergence of their laws,
accessed here through `MeasureTheory.TendstoInDistribution`. The chapter-level bridge is
`tendstoInDistribution_iff_tendsto_limit_law`, and the lower-semicontinuity input for item `(i)`
is the Portmanteau lintegral theorem
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`. The moment
expressions are therefore derived from the law-level owner API, not additional primitive data. -/

variable {Ω : ℕ → Type u} {Ω' : Type v}
variable {m : ∀ n, MeasurableSpace (Ω n)} {m' : MeasurableSpace Ω'}
variable {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
variable {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}

/-- Helper for Exercise 13.2.12: weak convergence in distribution implies lower semicontinuity of
the absolute `s`-moment for every positive exponent `s`. -/
lemma lintegral_abs_rpow_le_liminf_of_tendstoInDistribution {s : ℝ} (hs : 0 < s)
    (hXZ : TendstoInDistribution X atTop Z μ μ') :
    ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ s) ∂μ' ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ s) ∂μ n) atTop := by
  let ν : ProbabilityMeasure ℝ :=
    ⟨μ'.map Z, Measure.isProbabilityMeasure_map hXZ.aemeasurable_limit⟩
  let νs : ℕ → ProbabilityMeasure ℝ :=
    fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (hXZ.forall_aemeasurable n)⟩
  let f : ℝ → ℝ := fun x ↦ |x| ^ s
  have hf_cont : Continuous f := by
    exact continuous_abs.rpow_const fun _ ↦ Or.inr hs.le
  have hf_nonneg : 0 ≤ f := by
    intro x
    exact Real.rpow_nonneg (abs_nonneg x) s
  have hZlaw : HasLaw Z (ν : Measure ℝ) μ' := ⟨hXZ.aemeasurable_limit, rfl⟩
  have hXlaw : ∀ n, HasLaw (X n) ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) (μ n) :=
    fun n ↦ ⟨hXZ.forall_aemeasurable n, rfl⟩
  -- Proof comment: apply the Portmanteau lower-semicontinuity theorem to the laws and then
  -- rewrite the law integrals back to the original random variables.
  have hlaw :
      ∫⁻ x, ENNReal.ofReal (f x) ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) ≤
        liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ))
          atTop := by
    refine
      lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
        hf_cont hf_nonneg ?_
    intro G hG
    simpa [ν, νs] using
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hXZ.tendsto hG
  have hleft :
      ∫⁻ x, ENNReal.ofReal (f x) ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ s) ∂μ' := by
    symm
    simpa [ν, f, Function.comp] using
      (hZlaw.lintegral_comp ((hf_cont.measurable.ennreal_ofReal).aemeasurable))
  have hright :
      (fun n ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ)) =
        fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ s) ∂μ n := by
    funext n
    symm
    simpa [νs, f, Function.comp] using
      (hXlaw n).lintegral_comp ((hf_cont.measurable.ennreal_ofReal).aemeasurable)
  simpa [hleft, hright] using hlaw

-- Proof sketch: apply the portmanteau lower-semicontinuity inequality to the nonnegative lower
-- semicontinuous test function `x ↦ |x|`, written as an `ENNReal`-valued lower integral of the
-- laws of the random variables.
/-- Item (i) of Exercise 13.2.12. Under convergence in distribution, the first absolute moment
of the limit is bounded above by the liminf of the first absolute moments of the approximating
random variables, interpreted as nonnegative extended expectations. -/
theorem lintegral_abs_le_liminf_of_tendstoInDistribution
    (hXZ : TendstoInDistribution X atTop Z μ μ') :
    ∫⁻ ω, ENNReal.ofReal |Z ω| ∂μ' ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal |X n ω| ∂μ n) atTop := by
  -- Proof comment: specialize the general absolute-power lower-semicontinuity lemma to `s = 1`.
  simpa using
    (lintegral_abs_rpow_le_liminf_of_tendstoInDistribution (X := X) (Z := Z)
      (μ := μ) (μ' := μ') (s := 1) zero_lt_one hXZ)

/-- Helper for Exercise 13.2.12: the fixed cutoff value `min (|x| ^ p) (A ^ p)` is nonnegative. -/
lemma minAbsRpowCutoff_nonneg {A p x : ℝ} (hA : 0 < A) :
    0 ≤ min (|x| ^ p) (A ^ p) := by
  positivity

/-- Helper for Exercise 13.2.12: the NNReal-valued cutoff profile is continuous. -/
lemma continuous_minAbsRpowCutoff {A p : ℝ} (hA : 0 < A) (hp : 0 < p) :
    Continuous
      (fun x : ℝ ↦
        (⟨min (|x| ^ p) (A ^ p), minAbsRpowCutoff_nonneg (x := x) hA⟩ : NNReal)) := by
  -- Proof comment: continuity comes from the real-valued cutoff and the subtype embedding into
  -- `NNReal`.
  exact
    Continuous.subtype_mk
      ((continuous_abs.rpow_const fun _ ↦ Or.inr hp.le).min continuous_const)
      (fun x ↦ minAbsRpowCutoff_nonneg (x := x) hA)

/-- Helper for Exercise 13.2.12: the NNReal-valued cutoff stays within the bounded interval
`[0, A ^ p]`, so any two values are at distance at most `A ^ p`. -/
lemma dist_minAbsRpowCutoff_le {A p : ℝ} (hA : 0 < A) :
    ∀ x y : ℝ,
      dist
          ((⟨min (|x| ^ p) (A ^ p), minAbsRpowCutoff_nonneg (x := x) hA⟩ : NNReal))
          ((⟨min (|y| ^ p) (A ^ p), minAbsRpowCutoff_nonneg (x := y) hA⟩ : NNReal))
        ≤ A ^ p := by
  intro x y
  change |(min (|x| ^ p) (A ^ p) : ℝ) - (min (|y| ^ p) (A ^ p) : ℝ)| ≤ A ^ p
  have hx_le : min (|x| ^ p) (A ^ p) ≤ A ^ p := min_le_right _ _
  have hy_le : min (|y| ^ p) (A ^ p) ≤ A ^ p := min_le_right _ _
  have hx_nonneg : 0 ≤ min (|x| ^ p) (A ^ p) := minAbsRpowCutoff_nonneg (x := x) hA
  have hy_nonneg : 0 ≤ min (|y| ^ p) (A ^ p) := minAbsRpowCutoff_nonneg (x := y) hA
  refine abs_le.mpr ?_
  constructor <;> linarith

/-- Helper for Exercise 13.2.12: the bounded cutoff `x ↦ min (|x| ^ p) (A ^ p)` defines a
nonnegative bounded continuous test function. -/
def minAbsRpowCutoff_bcf {A p : ℝ} (hA : 0 < A) (hp : 0 < p) :
    ℝ →ᵇ NNReal where
  toContinuousMap :=
    { toFun := fun x ↦ ⟨min (|x| ^ p) (A ^ p), minAbsRpowCutoff_nonneg (x := x) hA⟩
      continuous_toFun := continuous_minAbsRpowCutoff hA hp }
  map_bounded' := ⟨A ^ p, dist_minAbsRpowCutoff_le hA⟩

/-- Helper for Exercise 13.2.12: weak convergence in distribution gives convergence of the fixed
cutoff absolute `p`-moments. -/
lemma tendsto_lintegral_min_abs_rpow_cutoff_of_tendstoInDistribution {A p : ℝ}
    (hA : 0 < A) (hp : 0 < p) (hXZ : TendstoInDistribution X atTop Z μ μ') :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ')) := by
  let ν : ProbabilityMeasure ℝ :=
    ⟨μ'.map Z, Measure.isProbabilityMeasure_map hXZ.aemeasurable_limit⟩
  let νs : ℕ → ProbabilityMeasure ℝ :=
    fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (hXZ.forall_aemeasurable n)⟩
  let f : ℝ →ᵇ NNReal := minAbsRpowCutoff_bcf hA hp
  have hZlaw : HasLaw Z (ν : Measure ℝ) μ' := ⟨hXZ.aemeasurable_limit, rfl⟩
  have hXlaw : ∀ n, HasLaw (X n) ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) (μ n) :=
    fun n ↦ ⟨hXZ.forall_aemeasurable n, rfl⟩
  have hf_apply :
      ∀ x : ℝ, (f x : ℝ≥0∞) = ENNReal.ofReal (min (|x| ^ p) (A ^ p)) := by
    intro x
    simpa [f, minAbsRpowCutoff_bcf] using
      (ENNReal.ofReal_eq_coe_nnreal (minAbsRpowCutoff_nonneg (x := x) hA)).symm
  -- Proof comment: apply bounded-continuous convergence on the laws and rewrite those law
  -- integrals back to the original random variables.
  have hf :
      Tendsto (fun n ↦ ∫⁻ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ)) atTop
        (𝓝 (∫⁻ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ))) :=
    (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hXZ.tendsto) f
  have hleft :
      ∫⁻ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ' := by
    have hleft_raw :
        ∫⁻ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫⁻ ω, (f (Z ω) : ℝ≥0∞) ∂μ' := by
      symm
      simpa [ν, Function.comp] using
        (hZlaw.lintegral_comp (f.continuous.measurable.coe_nnreal_ennreal.aemeasurable))
    calc
      ∫⁻ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫⁻ ω, (f (Z ω) : ℝ≥0∞) ∂μ' := hleft_raw
      _ = ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ' := by
        refine lintegral_congr_ae ?_
        filter_upwards with ω
        simpa using hf_apply (Z ω)
  have hright :
      (fun n ↦ ∫⁻ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ)) =
        fun n ↦ ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n := by
    funext n
    have hright_raw :
        ∫⁻ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫⁻ ω, (f (X n ω) : ℝ≥0∞) ∂μ n := by
      symm
      simpa [νs, Function.comp] using
        (hXlaw n).lintegral_comp (f.continuous.measurable.coe_nnreal_ennreal.aemeasurable)
    calc
      ∫⁻ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫⁻ ω, (f (X n ω) : ℝ≥0∞) ∂μ n := hright_raw
      _ = ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n := by
        refine lintegral_congr_ae ?_
        filter_upwards with ω
        simpa using hf_apply (X n ω)
  simpa [hleft, hright] using hf

/-- Helper for Exercise 13.2.12: above the cutoff level `A`, the `p`-th power is controlled by
`A ^ (p - r)` times the `r`-th power. -/
lemma abs_rpow_le_cutoffMul_of_le {A p r t : ℝ} (hA : 0 < A) (hpr : p < r) (ht : A ≤ t) :
    t ^ p ≤ A ^ (p - r) * t ^ r := by
  have ht_pos : 0 < t := lt_of_lt_of_le hA ht
  have hbase :
      t ^ (p - r) ≤ A ^ (p - r) :=
    Real.rpow_le_rpow_of_nonpos hA ht (sub_nonpos.mpr hpr.le)
  -- Proof comment: compare the negative exponent `p - r` on the larger base `t`, then multiply
  -- back by the nonnegative factor `t ^ r`.
  calc
    t ^ p = t ^ (p - r) * t ^ r := by
      symm
      rw [← Real.rpow_add ht_pos, sub_add_cancel]
    _ ≤ A ^ (p - r) * t ^ r := by
      exact mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (le_of_lt ht_pos) r)

/-- Helper for Exercise 13.2.12: pointwise, the full absolute `p`-power is bounded by the fixed
cutoff plus the higher-moment tail term. -/
lemma abs_rpow_le_min_abs_rpow_add_cutoffMul {A p r x : ℝ} (hA : 0 < A) (hp : 0 < p)
    (hpr : p < r) :
    ENNReal.ofReal (|x| ^ p) ≤
      ENNReal.ofReal (min (|x| ^ p) (A ^ p)) +
        ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|x| ^ r) := by
  by_cases hxA : |x| ≤ A
  · have hmin : min (|x| ^ p) (A ^ p) = |x| ^ p := by
      apply min_eq_left
      exact Real.rpow_le_rpow (abs_nonneg x) hxA hp.le
    -- Proof comment: below the cutoff, the truncated term already equals the full `p`-power.
    rw [hmin]
    exact le_add_of_nonneg_right bot_le
  · have hAx : A ≤ |x| := le_of_not_ge hxA
    have htail : |x| ^ p ≤ A ^ (p - r) * |x| ^ r :=
      abs_rpow_le_cutoffMul_of_le hA hpr hAx
    have hmul :
        ENNReal.ofReal (A ^ (p - r) * |x| ^ r) =
          ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|x| ^ r) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    -- Proof comment: above the cutoff, the tail estimate absorbs the full `p`-power, while the
    -- truncated term contributes only an extra nonnegative summand.
    calc
      ENNReal.ofReal (|x| ^ p)
          ≤ ENNReal.ofReal (A ^ (p - r) * |x| ^ r) := ENNReal.ofReal_le_ofReal htail
      _ = ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|x| ^ r) := hmul
      _ ≤ ENNReal.ofReal (min (|x| ^ p) (A ^ p)) +
          ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|x| ^ r) := by
        exact le_add_of_nonneg_left bot_le

/-- Helper for Exercise 13.2.12: integrating the pointwise cutoff estimate bounds the full
absolute `p`-moment by the truncated moment plus a higher-moment tail term. -/
lemma lintegral_abs_rpow_le_lintegral_min_abs_rpow_add_cutoffMul
    {α : Type*} {_ : MeasurableSpace α} {ν : Measure α} {Y : α → ℝ}
    (hY : AEMeasurable Y ν) {A p r : ℝ} (hA : 0 < A) (hp : 0 < p) (hpr : p < r) :
    ∫⁻ x, ENNReal.ofReal (|Y x| ^ p) ∂ν ≤
      ∫⁻ x, ENNReal.ofReal (min (|Y x| ^ p) (A ^ p)) ∂ν +
        ENNReal.ofReal (A ^ (p - r)) * ∫⁻ x, ENNReal.ofReal (|Y x| ^ r) ∂ν := by
  have hmeas_r :
      AEMeasurable (fun x : α ↦ ENNReal.ofReal (|Y x| ^ r)) ν := by
    have hpow_meas :
        AEMeasurable (fun x : α ↦ |Y x| ^ r) ν := by
      have hbase_meas : Measurable (fun t : ℝ ↦ |t| ^ r) :=
        (continuous_abs.rpow_const fun _ ↦ Or.inr (le_trans hp.le hpr.le)).measurable
      exact hbase_meas.comp_aemeasurable hY
    exact hpow_meas.ennreal_ofReal
  have hmeas_tail :
      AEMeasurable
        (fun x : α ↦ ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|Y x| ^ r)) ν :=
    hmeas_r.const_mul (ENNReal.ofReal (A ^ (p - r)))
  -- Proof comment: integrate the pointwise bound and then pull the constant tail factor out of
  -- the higher-moment integral.
  calc
    ∫⁻ x, ENNReal.ofReal (|Y x| ^ p) ∂ν
      ≤ ∫⁻ x,
          (ENNReal.ofReal (min (|Y x| ^ p) (A ^ p)) +
            ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|Y x| ^ r)) ∂ν := by
        exact lintegral_mono fun x ↦ abs_rpow_le_min_abs_rpow_add_cutoffMul hA hp hpr
    _ = ∫⁻ x, ENNReal.ofReal (min (|Y x| ^ p) (A ^ p)) ∂ν +
          ∫⁻ x, ENNReal.ofReal (A ^ (p - r)) * ENNReal.ofReal (|Y x| ^ r) ∂ν := by
        rw [lintegral_add_right' _ hmeas_tail]
    _ = ∫⁻ x, ENNReal.ofReal (min (|Y x| ^ p) (A ^ p)) ∂ν +
          ENNReal.ofReal (A ^ (p - r)) * ∫⁻ x, ENNReal.ofReal (|Y x| ^ r) ∂ν := by
        rw [lintegral_const_mul'' _ hmeas_r]

/-- Helper for Exercise 13.2.12: the increasing cutoffs
`ENNReal.ofReal (min (|x| ^ p) (((N + 1 : ℝ) ^ p)))` converge pointwise to
`ENNReal.ofReal (|x| ^ p)`. -/
lemma iSup_minAbsRpowCutoff_eq_absRpow {p : ℝ} (hp : 0 < p) (x : ℝ) :
    (⨆ N : ℕ, ENNReal.ofReal (min (|x| ^ p) (((N + 1 : ℝ) ^ p)))) =
      ENNReal.ofReal (|x| ^ p) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro N
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · let N : ℕ := ⌈|x|⌉₊
    have hx_le : |x| ≤ (N + 1 : ℝ) := by
      calc
        |x| ≤ (N : ℝ) := by
          simpa [N] using (Nat.le_ceil (|x|))
        _ ≤ (N + 1 : ℝ) := by
          exact le_add_of_nonneg_right zero_le_one
    have hpow_le : |x| ^ p ≤ ((N + 1 : ℝ) ^ p) := by
      exact Real.rpow_le_rpow (abs_nonneg x) hx_le hp.le
    have hmin : min (|x| ^ p) (((N + 1 : ℝ) ^ p)) = |x| ^ p := min_eq_left hpow_le
    calc
      ENNReal.ofReal (|x| ^ p) = ENNReal.ofReal (min (|x| ^ p) (((N + 1 : ℝ) ^ p)) ) := by
        rw [hmin]
      _ ≤ ⨆ M : ℕ, ENNReal.ofReal (min (|x| ^ p) (((M + 1 : ℝ) ^ p))) := by
        exact le_iSup_of_le N le_rfl

/-- Helper for Exercise 13.2.12: a fixed truncation level `A` controls the limsup of the
absolute `p`-moments by the corresponding truncated limit moment plus a tail term coming from an
arbitrary uniform bound on the absolute `r`-moments. -/
lemma limsupAbsRpow_le_cutoffLimit_add_tail {p r A : ℝ} (hA : 0 < A) (hp : 0 < p) (hpr : p < r)
    (hXZ : TendstoInDistribution X atTop Z μ μ') {B : ENNReal}
    (hB : ∀ n, ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n ≤ B) :
    limsup (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop ≤
      ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ' +
        ENNReal.ofReal (A ^ (p - r)) * B := by
  -- Route correction: compare the `p`-moments directly with a convergent cutoff envelope, rather
  -- than splitting `limsup` across a variable tail term.
  let y : ℕ → ENNReal := fun n ↦
    ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n +
      ENNReal.ofReal (A ^ (p - r)) * B
  have hy_le :
      ∀ n, ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n ≤ y n := by
    intro n
    -- Proof comment: first use the integrated cutoff estimate, then replace the varying `r`-moment
    -- by the uniform bound `B`.
    calc
      ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n
        ≤ ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n +
            ENNReal.ofReal (A ^ (p - r)) *
              ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n := by
            simpa using
              (lintegral_abs_rpow_le_lintegral_min_abs_rpow_add_cutoffMul
                (ν := μ n) (Y := X n) (hY := hXZ.forall_aemeasurable n)
                (A := A) (p := p) (r := r) hA hp hpr)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (min (|X n ω| ^ p) (A ^ p)) ∂μ n +
          ENNReal.ofReal (A ^ (p - r)) * B := by
            gcongr
            exact hB n
      _ = y n := rfl
  have hy_tendsto :
      Tendsto y atTop
        (𝓝
          (∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ' +
            ENNReal.ofReal (A ^ (p - r)) * B)) := by
    have hcutoff :=
      tendsto_lintegral_min_abs_rpow_cutoff_of_tendstoInDistribution
        (X := X) (Z := Z) (μ := μ) (μ' := μ') (A := A) (p := p) hA hp hXZ
    have hconst :
        Tendsto (fun _ : ℕ ↦ ENNReal.ofReal (A ^ (p - r)) * B) atTop
          (𝓝 (ENNReal.ofReal (A ^ (p - r)) * B)) :=
      tendsto_const_nhds
    -- Proof comment: the envelope sequence converges because only the cutoff term varies with `n`.
    simpa [y] using hcutoff.add hconst
  -- Proof comment: `limsup` respects eventual pointwise domination, and the envelope limit
  -- identifies the final right-hand side.
  calc
    limsup (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop ≤ limsup y atTop := by
      exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hy_le)
    _ =
        ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (A ^ p)) ∂μ' +
          ENNReal.ofReal (A ^ (p - r)) * B := by
            exact hy_tendsto.limsup_eq

/-- Helper for Exercise 13.2.12: the truncated absolute `p`-moments along the limit variable
increase to the full absolute `p`-moment. -/
lemma tendsto_lintegral_minAbsRpowCutoff_atTop {p : ℝ} (hp : 0 < p)
    {ν : Measure Ω'} (hZ : AEMeasurable Z ν) :
    Tendsto
      (fun N : ℕ ↦ ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))) ∂ν)
      atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂ν)) := by
  have hcutoff_meas :
      ∀ N : ℕ,
        AEMeasurable
          (fun ω : Ω' ↦ ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p)))) ν := by
    intro N
    have hreal_meas :
        AEMeasurable (fun ω : Ω' ↦ min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))) ν := by
      have hbase_meas : Measurable (fun t : ℝ ↦ min (|t| ^ p) (((N + 1 : ℝ) ^ p)) ) :=
        ((continuous_abs.rpow_const fun _ ↦ Or.inr hp.le).min continuous_const).measurable
      exact hbase_meas.comp_aemeasurable hZ
    exact hreal_meas.ennreal_ofReal
  have hcutoff_mono :
      ∀ᵐ ω ∂ν,
        Monotone fun N : ℕ ↦ ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))) := by
    filter_upwards with ω
    intro N M hNM
    apply ENNReal.ofReal_le_ofReal
    apply min_le_min_left
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ hNM) hp.le
  have hcutoff_tendsto :
      ∀ᵐ ω ∂ν,
        Tendsto
          (fun N : ℕ ↦ ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))))
          atTop (𝓝 (ENNReal.ofReal (|Z ω| ^ p))) := by
    filter_upwards with ω
    -- Proof comment: once the cutoff level overtakes `|Z ω|`, the truncated integrand is
    -- literally constant and hence converges to the full `p`-power.
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioi_mem_atTop (Nat.ceil |Z ω|)] with N hN
    have hx_le : |Z ω| ≤ (N + 1 : ℝ) := by
      calc
        |Z ω| ≤ ((Nat.ceil |Z ω|) : ℝ) := by
          exact_mod_cast Nat.le_ceil (|Z ω|)
        _ ≤ (N : ℝ) := by
          exact_mod_cast Nat.le_of_lt hN
        _ ≤ (N + 1 : ℝ) := by
          exact le_add_of_nonneg_right zero_le_one
    have hpow_le : |Z ω| ^ p ≤ ((N + 1 : ℝ) ^ p) :=
      Real.rpow_le_rpow (abs_nonneg _) hx_le hp.le
    have hmin : min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p)) = |Z ω| ^ p := min_eq_left hpow_le
    simp [hmin]
  -- Proof comment: monotone convergence applies because the cutoff integrands increase
  -- pointwise to the full absolute `p`-power.
  exact lintegral_tendsto_of_tendsto_of_monotone hcutoff_meas hcutoff_mono hcutoff_tendsto

/-- Helper for Exercise 13.2.12: the tail factor `((N + 1)^ (p - r))` vanishes in `ENNReal`
when `p < r`, and multiplication by a finite constant preserves that limit. -/
lemma tendsto_cutoffTailFactor_zero {p r : ℝ} (hpr : p < r) {B : ENNReal} (hB_lt_top : B < ⊤) :
    Tendsto (fun N : ℕ ↦ ENNReal.ofReal (((N + 1 : ℝ) ^ (p - r))) * B) atTop (𝓝 0) := by
  have hNatSucc : Tendsto (fun N : ℕ ↦ N + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hshiftNat : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNatSucc
  have hshift : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ)) atTop atTop := by
    -- Proof comment: shifting the natural parameter by one does not change its divergence to
    -- `atTop`.
    simpa [Nat.cast_add, Nat.cast_one] using hshiftNat
  have hpow :
      Tendsto (fun N : ℕ ↦ ((N + 1 : ℝ) ^ (p - r))) atTop (𝓝 (0 : ℝ)) := by
    have hpow' :
        Tendsto (fun N : ℕ ↦ ((N + 1 : ℝ) ^ (-(r - p)))) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hpr)).comp hshift
    have hexp : p - r = -(r - p) := by ring
    -- Proof comment: rewrite the exponent as a negative power and invoke the standard asymptotic
    -- decay lemma.
    convert hpow' using 1
    funext N
    rw [hexp]
  have hofReal :
      Tendsto (fun N : ℕ ↦ ENNReal.ofReal (((N + 1 : ℝ) ^ (p - r)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hpow
  -- Proof comment: multiplying by the finite constant `B` preserves the vanishing limit.
  simpa using ENNReal.Tendsto.mul_const hofReal (Or.inr hB_lt_top.ne)

/-- Helper for Exercise 13.2.12: a uniform bound on the absolute `r`-moments forces the limsup of
the absolute `p`-moments to stay below the limit moment. -/
lemma limsup_lintegral_abs_rpow_le_of_bounded_moment {p r : ℝ} (hp : 0 < p) (hpr : p < r)
    (hXZ : TendstoInDistribution X atTop Z μ μ')
    (hbound : sSup (Set.range fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n) < ⊤) :
    limsup (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop ≤
      ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ' := by
  let B : ENNReal :=
    sSup (Set.range fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n)
  have hB_lt_top : B < ⊤ := by
    simpa [B] using hbound
  have hB :
      ∀ n, ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n ≤ B := by
    intro n
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ (Set.mem_range_self n)
  let u : ℕ → ENNReal := fun N ↦
    ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))) ∂μ' +
      ENNReal.ofReal (((N + 1 : ℝ) ^ (p - r))) * B
  have hlimsup_le_u :
      ∀ N, limsup (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop ≤ u N := by
    intro N
    have hN_pos : 0 < (N + 1 : ℝ) := by positivity
    -- Proof comment: each fixed cutoff level gives a limsup bound by the corresponding cutoff
    -- limit moment plus the tail term controlled by the common `r`-moment bound `B`.
    simpa [u] using
      (limsupAbsRpow_le_cutoffLimit_add_tail
        (X := X) (Z := Z) (μ := μ) (μ' := μ') (A := (N + 1 : ℝ)) (p := p) (r := r)
        hN_pos hp hpr hXZ hB)
  have hcutoff_tendsto :
      Tendsto
        (fun N : ℕ ↦ ∫⁻ ω, ENNReal.ofReal (min (|Z ω| ^ p) (((N + 1 : ℝ) ^ p))) ∂μ')
        atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ')) := by
    exact
      tendsto_lintegral_minAbsRpowCutoff_atTop
        (Z := Z) (ν := μ') hp hXZ.aemeasurable_limit
  have htail_tendsto :
      Tendsto (fun N : ℕ ↦ ENNReal.ofReal (((N + 1 : ℝ) ^ (p - r))) * B) atTop (𝓝 0) := by
    exact tendsto_cutoffTailFactor_zero (p := p) (r := r) hpr hB_lt_top
  have hu_tendsto :
      Tendsto u atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ')) := by
    -- Proof comment: the envelope converges because the cutoff term increases to the full moment
    -- and the tail factor vanishes.
    simpa [u] using hcutoff_tendsto.add htail_tendsto
  -- Proof comment: compare the constant limsup with the convergent envelope and pass to limits.
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hu_tendsto hlimsup_le_u

-- Proof sketch: first apply the continuous mapping theorem to `x ↦ |x| ^ p` to obtain
-- convergence in distribution of the `p`-th absolute powers, then use the uniform `r`-moment
-- bound with `r > p` to get uniform integrability and conclude convergence of the corresponding
-- moments by Vitali/portmanteau.
/-- Exercise 13.2.12 (2): Item (ii). If `0 < p < r` and the `r`-th absolute moments are
uniformly bounded, then the `p`-th absolute moments converge along the distributional limit,
again in the extended nonnegative sense. -/
theorem tendsto_lintegral_abs_rpow_of_tendstoInDistribution_of_bounded_moment
    {p r : ℝ} (hp : 0 < p) (hpr : p < r)
    (hXZ : TendstoInDistribution X atTop Z μ μ')
    (hbound : sSup (Set.range fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ r) ∂μ n) < ⊤) :
    Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (|X n ω| ^ p) ∂μ n) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (|Z ω| ^ p) ∂μ')) := by
  -- Proof comment: combine the already-proved liminf inequality with the fixed-cutoff limsup
  -- bound; the order-topology criterion then upgrades these two one-sided estimates to convergence.
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact lintegral_abs_rpow_le_liminf_of_tendstoInDistribution hp hXZ
  · exact limsup_lintegral_abs_rpow_le_of_bounded_moment hp hpr hXZ hbound

end
