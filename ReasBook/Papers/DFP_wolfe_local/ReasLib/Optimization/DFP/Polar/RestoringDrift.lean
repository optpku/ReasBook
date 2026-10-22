/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.TwoCycle
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import ReasLib.Optimization.DFP.Polar.Normalized.Regularity

/-!
# Restoring drift for the v21 polar construction

The first-diagonal cubic coefficient is derived from the exact normalized DFP
bracket, its two feedback stages, and the boundary rescaling. The remainder is
uniform on fixed compact neighborhoods of the source's cycle curve. The same
selected inverse cycle parameter gives a fixed restoring rate stronger than
`1 / 3` for nearby choices of the limiting normalization.
-/

public section

noncomputable section

open Filter
open scoped Topology
open scoped ContDiff

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: the fixed polar angle is positive. -/
private lemma baseAngle_pos : 0 < baseAngle := by
  rw [baseAngle_def]
  positivity

/-- Helper for eq:polar-slow-drift: the rational cycle normalization is analytic
at the reference parameter. -/
theorem cycleK_analyticAt_baseAngle : AnalyticAt ℝ cycleK baseAngle := by
  have hleft : 2 * baseAngle - baseAngle ≠ 0 := by
    linarith [baseAngle_pos]
  have hright : baseAngle + baseAngle ≠ 0 := by
    linarith [baseAngle_pos]
  rw [funext cycleK_def]
  have hnum : AnalyticAt ℝ (fun ν : ℝ ↦ 2 * ν - baseAngle) baseAngle := by
    fun_prop
  have hden : AnalyticAt ℝ
      (fun ν : ℝ ↦ ν * (2 * baseAngle - ν) * (baseAngle + ν)) baseAngle := by
    fun_prop
  exact hnum.div hden (mul_ne_zero (mul_ne_zero baseAngle_pos.ne' hleft) hright)

/-- Helper for eq:polar-slow-drift: the selected inverse cycle parameter is
analytic at `K₀`, with the same local inverse as the rational family. -/
theorem inverseParameter_contDiffAt_kZero :
    ContDiffAt ℝ ω inverseParameter kZero := by
  have hs : ContDiffAt ℝ ω cycleK baseAngle :=
    cycleK_analyticAt_baseAngle.contDiffAt
  have hd := hasDerivAt_cycleK_baseAngle.hasFDerivAt_equiv
    cycleK_derivCoefficient_pos.ne'
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hleft : ∀ᶠ ν in 𝓝 baseAngle, inverseParameter (cycleK ν) = ν :=
    Filter.Eventually.mono parameterSet_mem_nhds inverseParameter_invOn.1
  have heq := (hs.hasStrictFDerivAt' hd hn).localInverse_unique hleft
  have hinverse := (hs.to_localInverse hd hn).congr_of_eventuallyEq heq
  simpa only [← kZero_def] using hinverse

/-- Helper for eq:polar-slow-drift: the derivative of the selected inverse is
continuous at the reference normalization. -/
theorem inverseParameter_deriv_continuousAt_kZero :
    ContinuousAt (deriv inverseParameter) kZero := by
  have horder : (0 : ℕ∞ω) + 1 ≤ ω := le_top
  exact (inverseParameter_contDiffAt_kZero.derivWithin horder).continuousAt

/-- Helper for eq:polar-slow-drift: the inverse cycle parameter has derivative
`4 * baseAngle ^ 3 / 3` at the reference normalization. -/
theorem hasDerivAt_inverseParameter_kZero :
    HasDerivAt inverseParameter (4 * baseAngle ^ 3 / 3) kZero := by
  have hleft : ∀ᶠ ν in 𝓝 baseAngle, inverseParameter (cycleK ν) = ν :=
    Filter.Eventually.mono parameterSet_mem_nhds inverseParameter_invOn.1
  have hd := (hasStrictDerivAt_cycleK_baseAngle.to_local_left_inverse
    cycleK_derivCoefficient_pos.ne' hleft).hasDerivAt
  have hvalue : (3 / (4 * baseAngle ^ 3))⁻¹ = 4 * baseAngle ^ 3 / 3 := by
    field_simp
  simpa only [← kZero_def] using hd.congr_deriv hvalue

/-- Helper for eq:polar-slow-drift: the scalar restoring coefficient for the
feedback `L = 4 * baseAngle / (9 * νStar)` and `KStar = cycleK νStar`. -/
def restoringDrift (νStar A : ℝ) : ℝ :=
  (3 * (4 * baseAngle / (9 * νStar)) * cycleK νStar ^ 2 / baseAngle) *
    (inverseParameter A / A) - 4 / 3 * A

/-- Helper for eq:polar-slow-drift: the explicit scalar formula for the
restoring coefficient on the selected inverse branch. -/
theorem restoringDrift_apply (νStar A : ℝ) :
    restoringDrift νStar A =
      (3 * (4 * baseAngle / (9 * νStar)) * cycleK νStar ^ 2 / baseAngle) *
        (inverseParameter A / A) - 4 / 3 * A := by
  rfl

/-- Helper for eq:polar-slow-drift: the two cubic stage contributions and the
scale correction combine into the stated scalar drift. -/
theorem restoringDrift_eq_stageSum (νStar A : ℝ) (hA : A ≠ 0) :
    restoringDrift νStar A =
      -((4 * baseAngle / (9 * νStar)) * (cycleK νStar / A) ^ 2) /
          baseAngle * A * (2 * baseAngle - inverseParameter A) +
        2 * ((4 * baseAngle / (9 * νStar)) * (cycleK νStar / A) ^ 2) /
          baseAngle * A * (baseAngle + inverseParameter A) - 4 / 3 * A := by
  unfold restoringDrift
  field_simp [hA, baseAngle_pos.ne']
  all_goals ring

/-- Helper for eq:polar-slow-drift: the feedback makes its selected limiting
normalization an equilibrium of the scalar drift. -/
theorem restoringDrift_cycleK (ν : ℝ) (hν : ν ∈ parameterSet) :
    restoringDrift ν (cycleK ν) = 0 := by
  have hpos := cycleFamily_mapsTo_positive hν
  simp only [Set.mem_prod, Set.mem_Ioi] at hpos
  have hνpos : 0 < ν := by
    rw [parameterSet_def] at hν
    have hbound := hν.1
    linarith [baseAngle_pos]
  rw [restoringDrift, inverseParameter_invOn.1 hν]
  field_simp [baseAngle_pos.ne', hνpos.ne', hpos.1.ne']
  all_goals ring

/-- Helper for eq:polar-slow-drift: the reference restoring coefficient vanishes
at `K₀`. -/
theorem restoringDrift_kZero : restoringDrift baseAngle kZero = 0 := by
  have hbase : baseAngle ∈ parameterSet :=
    mem_of_mem_nhds parameterSet_mem_nhds
  simpa only [← kZero_def] using restoringDrift_cycleK baseAngle hbase

/-- Helper for eq:polar-slow-drift: the reference restoring rate is `16 / 9`,
strictly stronger than the `1 / 3` scale decrease. -/
theorem hasDerivAt_restoringDrift_kZero :
    HasDerivAt (restoringDrift baseAngle) (-16 / 9) kZero := by
  have hk : kZero ≠ 0 := by
    rw [kZero_eq]
    have ha := baseAngle_pos
    positivity
  have hd := ((hasDerivAt_inverseParameter_kZero.fun_div
    (hasDerivAt_id kZero) hk).const_mul
      (3 * (4 * baseAngle / (9 * baseAngle)) * cycleK baseAngle ^ 2 / baseAngle)).sub
        ((hasDerivAt_id kZero).const_mul (4 / 3))
  have hvalue :
      (3 * (4 * baseAngle / (9 * baseAngle)) * cycleK baseAngle ^ 2 / baseAngle) *
        ((4 * baseAngle ^ 3 / 3 * kZero - inverseParameter kZero * 1) / kZero ^ 2) -
          4 / 3 * 1 = -16 / 9 := by
    rw [inverseParameter_kZero, ← kZero_def, kZero_eq]
    field_simp [baseAngle_pos.ne']
    all_goals ring
  have hfun :
      ((fun y : ℝ ↦
          (3 * (4 * baseAngle / (9 * baseAngle)) * cycleK baseAngle ^ 2 / baseAngle) *
            (inverseParameter y / id y)) - fun y ↦ 4 / 3 * id y) =
        restoringDrift baseAngle := by
    funext y
    rfl
  rw [hfun] at hd
  exact hd.congr_deriv hvalue

/-- Helper for eq:polar-slow-drift: the derivative of the restoring coefficient
is the quotient-rule expression on the smooth inverse branch. -/
theorem deriv_restoringDrift (νStar A : ℝ)
    (hν : DifferentiableAt ℝ inverseParameter A) (hA : A ≠ 0) :
    deriv (restoringDrift νStar) A =
      (3 * (4 * baseAngle / (9 * νStar)) * cycleK νStar ^ 2 / baseAngle) *
        ((deriv inverseParameter A * A - inverseParameter A) / A ^ 2) - 4 / 3 := by
  have hd := ((hν.hasDerivAt.fun_div (hasDerivAt_id A) hA).const_mul
    (3 * (4 * baseAngle / (9 * νStar)) * cycleK νStar ^ 2 / baseAngle)).sub
      ((hasDerivAt_id A).const_mul (4 / 3))
  have hfun :
      ((fun y : ℝ ↦
        (3 * (4 * baseAngle / (9 * νStar)) * cycleK νStar ^ 2 / baseAngle) *
          (inverseParameter y / id y)) - fun y ↦ 4 / 3 * id y) =
        restoringDrift νStar := by
    funext y
    exact (restoringDrift_apply νStar y).symm
  rw [hfun] at hd
  simpa only [id_eq, mul_one] using hd.deriv

/-- Helper for eq:polar-slow-drift: one fixed product neighborhood of
`(baseAngle, K₀)` has restoring derivative at most `-1`. -/
theorem restoringDrift_deriv_eventually :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (baseAngle, kZero),
      ContDiffAt ℝ ω inverseParameter p.2 ∧ p.2 ∈ normalizationSet ∧
        0 < p.2 ∧ deriv (restoringDrift p.1) p.2 ≤ -1 := by
  have ha := baseAngle_pos
  have hnonzeroOrder : (ω : ℕ∞ω) ≠ 0 := by simp
  have hkpos : 0 < kZero := by
    rw [kZero_eq]
    positivity
  have hν : ContinuousAt (fun p : ℝ × ℝ ↦ inverseParameter p.2)
      (baseAngle, kZero) :=
    inverseParameter_contDiffAt_kZero.continuousAt.comp continuousAt_snd
  have hν' : ContinuousAt (fun p : ℝ × ℝ ↦ deriv inverseParameter p.2)
      (baseAngle, kZero) := by
    have hcomp := ContinuousAt.comp (x := (baseAngle, kZero))
      (f := Prod.snd) (g := deriv inverseParameter)
      inverseParameter_deriv_continuousAt_kZero continuousAt_snd
    simpa only [Function.comp_def] using hcomp
  have hK : ContinuousAt (fun p : ℝ × ℝ ↦ cycleK p.1) (baseAngle, kZero) :=
    cycleK_analyticAt_baseAngle.continuousAt.comp continuousAt_fst
  have hrate : ContinuousAt
      (fun p : ℝ × ℝ ↦
        (3 * (4 * baseAngle / (9 * p.1)) * cycleK p.1 ^ 2 / baseAngle) *
          ((deriv inverseParameter p.2 * p.2 - inverseParameter p.2) / p.2 ^ 2) -
            4 / 3) (baseAngle, kZero) := by
    fun_prop (disch := positivity)
  have href :
      (3 * (4 * baseAngle / (9 * baseAngle)) * cycleK baseAngle ^ 2 / baseAngle) *
        ((deriv inverseParameter kZero * kZero - inverseParameter kZero) / kZero ^ 2) -
          4 / 3 < (-1 : ℝ) := by
    rw [← deriv_restoringDrift baseAngle kZero
      (inverseParameter_contDiffAt_kZero.differentiableAt hnonzeroOrder) hkpos.ne',
      hasDerivAt_restoringDrift_kZero.deriv]
    norm_num
  have hbound := hrate.eventually (Iio_mem_nhds href)
  have hsmooth : ∀ᶠ p : ℝ × ℝ in 𝓝 (baseAngle, kZero),
      ContDiffAt ℝ ω inverseParameter p.2 :=
    continuousAt_snd.eventually (inverseParameter_contDiffAt_kZero.eventually
      WithTop.top_ne_coe)
  have hnormal : ∀ᶠ p : ℝ × ℝ in 𝓝 (baseAngle, kZero),
      p.2 ∈ normalizationSet :=
    continuousAt_snd.eventually normalizationSet_mem_nhds
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (baseAngle, kZero), 0 < p.2 :=
    continuousAt_snd.eventually (Ioi_mem_nhds hkpos)
  filter_upwards [hsmooth, hnormal, hpos, hbound] with p hp hn hp0 hb
  refine ⟨hp, hn, hp0, ?_⟩
  rw [deriv_restoringDrift p.1 p.2 (hp.differentiableAt hnonzeroOrder) hp0.ne']
  exact hb.le

/-- Helper for eq:polar-slow-drift: choose a single restoring rate before the
nearby parameter, and obtain a smooth restoring neighborhood of each selected
normalization, independently of the initial cycle index. -/
theorem exists_uniformRestoringNeighborhood :
    ∃ rate > (1 / 3 : ℝ), ∃ δ > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + δ),
      νStar ∈ parameterSet ∧ ∃ r > 0,
        ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
          ContDiffAt ℝ ω inverseParameter A ∧ A ∈ normalizationSet ∧
            0 < A ∧ deriv (restoringDrift νStar) A ≤ -rate := by
  obtain ⟨U, V, hUopen, hUa, hVopen, hVk, hUV⟩ :=
    mem_nhds_prod_iff'.mp restoringDrift_deriv_eventually
  have hKV : ∀ᶠ ν in 𝓝 baseAngle, cycleK ν ∈ V := by
    have hV : V ∈ 𝓝 (cycleK baseAngle) := by
      rw [← kZero_def]
      exact hVopen.mem_nhds hVk
    exact cycleK_analyticAt_baseAngle.continuousAt.eventually hV
  have hparameters : U ∩ parameterSet ∩ cycleK ⁻¹' V ∈ 𝓝 baseAngle :=
    inter_mem (inter_mem (hUopen.mem_nhds hUa) parameterSet_mem_nhds) hKV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hparameters
  refine ⟨1, ?_, δ, hδ, ?_⟩
  · norm_num
  · intro νStar hνStar
    have hnear : νStar ∈ Metric.ball baseAngle δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hνStar.1)]
      linarith [hνStar.2]
    have hν := hball hnear
    refine ⟨hν.1.2, ?_⟩
    obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hν.2)
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro A hA
    have hAV : A ∈ V := by
      apply hεball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [hA.1]
      · linarith [hA.2]
    exact hUV (a := (νStar, A)) ⟨hν.1.1, hAV⟩

/-- Helper for eq:polar-slow-drift: the even cycle's radial defect is
`A * (2 * baseAngle - inverseParameter A)`. -/
theorem evenState_radialDefect (A : ℝ) (hA : A ∈ normalizationSet) :
    (evenState A).1 * Normalized.slope (evenState A) - (evenState A).2.1 =
      A * (2 * baseAngle - inverseParameter A) := by
  rw [slope_evenState A hA, evenState_apply]
  dsimp only
  have hdiff := cycleW_sub_cycleZ _ (inverseParameter_mapsTo hA)
  calc
    A * (cycleZ (inverseParameter A) + 2 * baseAngle) -
        A * cycleW (inverseParameter A) =
      A * (2 * baseAngle -
        (cycleW (inverseParameter A) - cycleZ (inverseParameter A))) := by ring
    _ = A * (2 * baseAngle - inverseParameter A) := by rw [hdiff]

/-- Helper for eq:polar-slow-drift: the odd cycle's radial defect is
`A * (baseAngle + inverseParameter A)`. -/
theorem oddState_radialDefect (A : ℝ) (hA : A ∈ normalizationSet) :
    (oddState A).1 * Normalized.slope (oddState A) - (oddState A).2.1 =
      A * (baseAngle + inverseParameter A) := by
  rw [slope_oddState A hA, oddState_apply]
  dsimp only
  have hdiff := cycleW_sub_cycleZ _ (inverseParameter_mapsTo hA)
  calc
    A * (cycleW (inverseParameter A) + baseAngle) -
        A * cycleZ (inverseParameter A) =
      A * (baseAngle +
        (cycleW (inverseParameter A) - cycleZ (inverseParameter A))) := by ring
    _ = A * (baseAngle + inverseParameter A) := by rw [hdiff]

end DFP.Polar.TwoCycle

namespace DFP.Polar.Normalized

/-- Helper for eq:polar-slow-drift: the normalized DFP bracket before the
rotation congruence, with normalized gradient change `w` and secant `σ`. -/
def preRotation (x : ℝ × ℝ × ℝ) (w : Fin 2 → ℝ) (σ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (1 - σ⁻¹ • Matrix.vecMulVec w (stepV x)) *
      RealSymmetric2.matrix x.1 x.2.1 x.2.2 *
      (1 - σ⁻¹ • Matrix.vecMulVec (stepV x) w) +
    σ⁻¹ • Matrix.vecMulVec w w

/-- Helper for eq:polar-slow-drift: the factored matrix formula for the
normalized bracket before rotation. -/
theorem preRotation_def (x : ℝ × ℝ × ℝ) (w : Fin 2 → ℝ) (σ : ℝ) :
    preRotation x w σ =
      (1 - σ⁻¹ • Matrix.vecMulVec w (stepV x)) *
          RealSymmetric2.matrix x.1 x.2.1 x.2.2 *
          (1 - σ⁻¹ • Matrix.vecMulVec (stepV x) w) +
        σ⁻¹ • Matrix.vecMulVec w w := by
  rfl

/-- Helper for eq:polar-slow-drift: the actual normalized stage is the
rotation congruence of its normalized pre-rotation bracket. -/
theorem stageMatrix_eq_preRotation (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ)
    (ζ η : ℝ) :
    stageMatrix i t x ζ η =
      rotation i t * preRotation x (stepW i t x ζ η) (stageSigma i t x ζ η) *
        (rotation i t).transpose := by
  rw [stageMatrix_def, preRotation_def]

/-- Helper for eq:polar-slow-drift: the first diagonal entry before rotation
is `A - 2 * E * w₀ / σ + (σ - Q * E) * w₀² / σ²`, where `E = C - A * Q`. -/
theorem preRotation_firstDiagonal (x : ℝ × ℝ × ℝ) (w : Fin 2 → ℝ) (σ : ℝ)
    (hC : x.2.1 ≠ 0) (hσ : σ ≠ 0) :
    preRotation x w σ 0 0 =
      x.1 - 2 * (x.2.1 - x.1 * slope x) * w 0 / σ +
        (σ - slope x * (x.2.1 - x.1 * slope x)) / σ ^ 2 * w 0 ^ 2 := by
  have honeZero : (1 : Fin 2) ≠ 0 := Ne.symm Fin.zero_ne_one
  simp only [preRotation_def, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, RealSymmetric2.matrix_eq, stepV_def, slope_def,
    Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, smul_eq_mul, ↓reduceIte]
  simp only [Fin.zero_ne_one, honeZero, ↓reduceIte]
  field_simp [hC, hσ]
  all_goals ring

/-- Helper for eq:polar-slow-drift: the canceled sine factor takes its limiting
angular coefficient at zero scale. -/
theorem sinFactor_at_zero (i : Fin 2) : sinFactor i 0 = limitAngle i := by
  fin_cases i
  all_goals norm_num [sinFactor_def, stageAngle_def, stageAngleFactor_def,
    angleFactor_def, unitRoot_def, limitAngle_zero, limitAngle_one,
    stageWeight_zero, stageWeight_one]
  all_goals ring

/-- Helper for eq:polar-slow-drift: the canceled cotangent at zero scale is the
reciprocal of the stage's limiting angular coefficient. -/
theorem cotFactor_at_zero (i : Fin 2) : cotFactor i 0 = 1 / limitAngle i := by
  rw [cotFactor_def, sinFactor_at_zero, stageAngle_def]
  simp

/-- Helper for eq:polar-slow-drift: the actual cubic feedback has an order-six
error after its constant and cubic terms. -/
theorem feedback_cubic_remainder (L κ : ℝ) (x₀ : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ feedback L κ t x₀ - (1 - L * (κ / x₀.1) ^ 2 * t ^ 3))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
  have hcubic : Tendsto (fun t : ℝ ↦ -L * (κ / x₀.1) ^ 2 * t ^ 3)
      (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ -L * (κ / x₀.1) ^ 2 * t ^ 3) 0 := by
      fun_prop
    simpa using hc.tendsto
  have hexp := (Real.exp_sub_sum_range_isBigO_pow 2).comp_tendsto hcubic
  have hpower := ((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).const_mul_left
    (-L * (κ / x₀.1) ^ 2)).pow 2
  have horder : (fun t : ℝ ↦ (-L * (κ / x₀.1) ^ 2 * t ^ 3) ^ 2)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
    simpa only [← pow_mul, Nat.reduceMul] using hpower
  have hsum (t : ℝ) :
      ∑ j ∈ Finset.range 2, (-L * (κ / x₀.1) ^ 2 * t ^ 3) ^ j / Nat.factorial j =
        1 - L * (κ / x₀.1) ^ 2 * t ^ 3 := by
    norm_num [Finset.sum_range_succ]
    ring
  simpa only [Function.comp_def, hsum, feedback_def] using hexp.trans horder

/-- Helper for eq:polar-slow-drift: a cubic multiplier difference contributes
`h / c` to the first normalized gradient-change component, with an order-four
remainder. -/
theorem stepW_first_cubic (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (ζ η : ℝ → ℝ) (h : ℝ) (hζ : ContinuousAt ζ 0)
    (hchange : (fun t : ℝ ↦ η t - ζ t - h * t ^ 3)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ stepW i t x (ζ t) (η t) 0 - (h / limitAngle i) * t ^ 3)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hcot : (fun t : ℝ ↦ cotFactor i t - 1 / limitAngle i)
      =O[𝓝 0] (fun t : ℝ ↦ t) := by
    simpa only [cotFactor_at_zero, sub_zero] using
      (cotFactor_analyticAt i).differentiableAt.isBigO_sub
  have hcotBound := (cotFactor_analyticAt i).continuousAt.isBigO_one ℝ
  have hfirst : (fun t : ℝ ↦ (η t - ζ t - h * t ^ 3) * cotFactor i t)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [mul_one] using hchange.mul hcotBound
  have hsecond : (fun t : ℝ ↦ h * (t ^ 3 * (cotFactor i t - 1 / limitAngle i)))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hpowers (t : ℝ) : t ^ 3 * t = t ^ 4 := by ring
    exact (((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).mul
      hcot).const_mul_left h).congr_right hpowers
  have hthird : (fun t : ℝ ↦ slope x * (ζ t * t ^ 4))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [one_mul] using
      ((hζ.isBigO_one ℝ).mul
        (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 4) (𝓝 0))).const_mul_left (slope x)
  have heq (t : ℝ) :
      (η t - ζ t - h * t ^ 3) * cotFactor i t +
          h * (t ^ 3 * (cotFactor i t - 1 / limitAngle i)) -
          slope x * (ζ t * t ^ 4) =
        stepW i t x (ζ t) (η t) 0 - (h / limitAngle i) * t ^ 3 := by
    rw [stepW_def]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    ring
  simpa only [heq] using (hfirst.add hsecond).sub hthird

/-- Helper for eq:polar-slow-drift: the first-stage feedback contributes
`-L * (κ / A)² / (2 * baseAngle)` to the cubic normalized gradient change. -/
theorem evenStepW_first_cubic (L κ : ℝ) (x₀ x : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ stepW 0 t x 1 (feedback L κ t x₀) 0 -
      (-L * (κ / x₀.1) ^ 2 / (2 * baseAngle)) * t ^ 3)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hlt : (4 : ℕ) < 6 := by norm_num
  have hfeedback := (feedback_cubic_remainder L κ x₀).trans
    (Asymptotics.isLittleO_pow_pow hlt).isBigO
  have hchange : (fun t : ℝ ↦ feedback L κ t x₀ - 1 -
      (-L * (κ / x₀.1) ^ 2) * t ^ 3) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    apply hfeedback.congr_left
    intro t
    ring
  simpa only [limitAngle_zero] using stepW_first_cubic 0 x (fun _ ↦ 1)
    (fun t ↦ feedback L κ t x₀) (-L * (κ / x₀.1) ^ 2) continuousAt_const hchange

/-- Helper for eq:polar-slow-drift: the second-stage feedback contributes
`L * (κ / A)² / baseAngle` to the cubic normalized gradient change. -/
theorem oddStepW_first_cubic (L κ : ℝ) (x₀ x : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ stepW 1 t x (feedback L κ t x₀) 1 0 -
      (L * (κ / x₀.1) ^ 2 / baseAngle) * t ^ 3)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hlt : (4 : ℕ) < 6 := by norm_num
  have hfeedback := (feedback_cubic_remainder L κ x₀).trans
    (Asymptotics.isLittleO_pow_pow hlt).isBigO
  have hchange : (fun t : ℝ ↦ 1 - feedback L κ t x₀ -
      (L * (κ / x₀.1) ^ 2) * t ^ 3) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    apply hfeedback.neg_left.congr_left
    intro t
    ring
  have hcontinuous : ContinuousAt (fun t : ℝ ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  simpa only [limitAngle_one] using stepW_first_cubic 1 x
    (fun t ↦ feedback L κ t x₀) (fun _ ↦ 1) (L * (κ / x₀.1) ^ 2)
    hcontinuous hchange

/-- Helper for eq:polar-slow-drift: the canceled sine factor recovers the
sine of the stage angle at every scale, including zero. -/
theorem sin_stageAngle_eq (i : Fin 2) (t : ℝ) :
    Real.sin (stageAngle i t) = t ^ 2 * sinFactor i t := by
  have hsinc : stageAngle i t * Real.sinc (stageAngle i t) =
      Real.sin (stageAngle i t) := by
    by_cases hzero : stageAngle i t = 0
    · rw [hzero]
      simp
    · rw [Real.sinc_of_ne_zero hzero, mul_div_cancel₀ _ hzero]
  rw [← hsinc, sinFactor_def, stageAngle_def]
  ring

/-- Helper for eq:polar-slow-drift: rotation changes the first diagonal entry
by an explicit multiple of `t ^ 4`. -/
theorem rotation_firstDiagonal_sub (i : Fin 2) (t : ℝ)
    (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    (rotation i t * Y * (rotation i t).transpose) 0 0 - Y 0 0 =
      t ^ 4 *
        (-(sinFactor i t) ^ 2 * Y 0 0 +
          Real.cos (stageAngle i t) * sinFactor i t * (Y 0 1 + Y 1 0) +
          t ^ 4 * (sinFactor i t) ^ 2 * Y 1 1) := by
  have hcos : Real.cos (stageAngle i t) ^ 2 =
      1 - t ^ 4 * sinFactor i t ^ 2 := by
    rw [Real.cos_sq', sin_stageAngle_eq]
    ring
  simp only [rotation_def, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  calc
    (Real.cos (stageAngle i t) * Y 0 0 + t ^ 4 * sinFactor i t * Y 1 0) *
          Real.cos (stageAngle i t) +
        (Real.cos (stageAngle i t) * Y 0 1 + t ^ 4 * sinFactor i t * Y 1 1) *
          (t ^ 4 * sinFactor i t) - Y 0 0 =
      (Real.cos (stageAngle i t) ^ 2 - 1) * Y 0 0 +
        t ^ 4 * Real.cos (stageAngle i t) * sinFactor i t * (Y 0 1 + Y 1 0) +
        t ^ 8 * sinFactor i t ^ 2 * Y 1 1 := by ring
    _ = _ := by
      rw [hcos]
      ring

/-- Helper for eq:polar-slow-drift: a continuous pre-rotation matrix has only
an order-four change in its first diagonal entry under the normalized rotation. -/
theorem rotation_firstDiagonal_isBigO (i : Fin 2)
    (Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hY : ∀ r c, ContinuousAt (fun t ↦ Y t r c) 0) :
    (fun t : ℝ ↦ (rotation i t * Y t * (rotation i t).transpose) 0 0 - Y t 0 0)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hsin := (sinFactor_analyticAt i).continuousAt
  have hcos : ContinuousAt (fun t : ℝ ↦ Real.cos (stageAngle i t)) 0 :=
    Real.continuous_cos.continuousAt.comp (stageAngle_analyticAt i).continuousAt
  have hcofactor : ContinuousAt
      (fun t : ℝ ↦ -(sinFactor i t) ^ 2 * Y t 0 0 +
        Real.cos (stageAngle i t) * sinFactor i t * (Y t 0 1 + Y t 1 0) +
        t ^ 4 * (sinFactor i t) ^ 2 * Y t 1 1) 0 := by
    fun_prop
  have horder := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 4) (𝓝 0)).mul
    (hcofactor.isBigO_one ℝ)
  simpa only [mul_one, ← rotation_firstDiagonal_sub] using horder

/-- Helper for eq:polar-slow-drift: continuous normalized gradient changes and
nonzero secants give continuous entries of the pre-rotation DFP bracket. -/
theorem preRotation_entry_continuousAt (x : ℝ × ℝ × ℝ)
    (w : ℝ → Fin 2 → ℝ) (σ : ℝ → ℝ)
    (hw : ∀ j, ContinuousAt (fun t ↦ w t j) 0)
    (hσ : ContinuousAt σ 0) (hσ0 : σ 0 ≠ 0) (r c : Fin 2) :
    ContinuousAt (fun t ↦ preRotation x (w t) (σ t) r c) 0 := by
  have hw0 := hw 0
  have hw1 := hw 1
  have hinv := hσ.inv₀ hσ0
  simp only [preRotation_def, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul]
  fin_cases r
  all_goals fin_cases c
  all_goals fun_prop

/-- Helper for eq:polar-slow-drift: a cubic first gradient-change component
produces the source's cubic first-diagonal increment before rotation. -/
theorem preRotation_first_cubic (x : ℝ × ℝ × ℝ) (hC : x.2.1 ≠ 0)
    (w : ℝ → Fin 2 → ℝ) (σ : ℝ → ℝ) (b : ℝ)
    (hσ : AnalyticAt ℝ σ 0) (hσone : σ 0 = 1)
    (hw : (fun t : ℝ ↦ w t 0 - b * t ^ 3) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ preRotation x (w t) (σ t) 0 0 -
      (x.1 + 2 * b * (x.1 * slope x - x.2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hσne : σ 0 ≠ 0 := by
    rw [hσone]
    exact one_ne_zero
  have hinv : AnalyticAt ℝ (fun t ↦ (σ t)⁻¹) 0 := by
    exact hσ.fun_inv hσne
  have hinvDefect : (fun t : ℝ ↦ (σ t)⁻¹ - 1)
      =O[𝓝 0] (fun t : ℝ ↦ t) := by
    simpa only [hσone, inv_one, sub_zero] using hinv.differentiableAt.isBigO_sub
  have hfirst : (fun t : ℝ ↦ (w t 0 - b * t ^ 3) * (σ t)⁻¹)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [mul_one] using hw.mul (hinv.continuousAt.isBigO_one ℝ)
  have hsecond : (fun t : ℝ ↦ b * (t ^ 3 * ((σ t)⁻¹ - 1)))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hpowers (t : ℝ) : t ^ 3 * t = t ^ 4 := by ring
    exact (((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).mul
      hinvDefect).const_mul_left b).congr_right hpowers
  have hwthree : (fun t : ℝ ↦ w t 0) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    have hfourThree : (fun t : ℝ ↦ t ^ 4) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) :=
      (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self 3)).isBigO
    simpa only [sub_add_cancel] using (hw.trans hfourThree).add
      ((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).const_mul_left b)
  have hcofactor : ContinuousAt
      (fun t : ℝ ↦ (σ t - slope x * (x.2.1 - x.1 * slope x)) / σ t ^ 2) 0 := by
    have hσcontinuous := hσ.continuousAt
    have hnonzero := pow_ne_zero 2 hσne
    fun_prop (disch := assumption)
  have hsquare : (fun t : ℝ ↦
      (σ t - slope x * (x.2.1 - x.1 * slope x)) / σ t ^ 2 * w t 0 ^ 2)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hlt : (4 : ℕ) < 6 := by norm_num
    have hpower : (fun t : ℝ ↦ w t 0 ^ 2) =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
      simpa only [← pow_mul, Nat.reduceMul] using hwthree.pow 2
    have hsix := (hcofactor.isBigO_one ℝ).mul hpower
    have hsix' : (fun t : ℝ ↦
        (σ t - slope x * (x.2.1 - x.1 * slope x)) / σ t ^ 2 * w t 0 ^ 2)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
      simpa only [one_mul] using hsix
    exact hsix'.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO
  have hlinear := (hfirst.add hsecond).const_mul_left
    (-2 * (x.2.1 - x.1 * slope x))
  have heq :
      (fun t : ℝ ↦ -2 * (x.2.1 - x.1 * slope x) *
          ((w t 0 - b * t ^ 3) * (σ t)⁻¹ + b * (t ^ 3 * ((σ t)⁻¹ - 1))) +
        (σ t - slope x * (x.2.1 - x.1 * slope x)) / σ t ^ 2 * w t 0 ^ 2)
        =ᶠ[𝓝 0]
      (fun t : ℝ ↦ preRotation x (w t) (σ t) 0 0 -
        (x.1 + 2 * b * (x.1 * slope x - x.2.1) * t ^ 3)) := by
    filter_upwards [hσ.continuousAt.eventually_ne hσne] with t ht
    rw [preRotation_firstDiagonal x (w t) (σ t) hC ht]
    ring
  exact (hlinear.add hsquare).congr' heq Filter.EventuallyEq.rfl

/-- Helper for eq:polar-slow-drift: analytic radial multipliers give analytic
normalized gradient-change components at zero scale. -/
theorem stepW_component_analyticAt (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0) (j : Fin 2) :
    AnalyticAt ℝ (fun t ↦ stepW i t x (ζ t) (η t) j) 0 := by
  have hcot := cotFactor_analyticAt i
  fin_cases j
  · simp only [Fin.zero_eta, stepW_def, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simpa only [Fin.mk_one, stepW_def, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using hη

/-- Helper for eq:polar-slow-drift: the secant scalar along analytic radial
multiplier paths is analytic at zero scale. -/
theorem stageSigma_analyticAt (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0) :
    AnalyticAt ℝ (fun t ↦ stageSigma i t x (ζ t) (η t)) 0 := by
  have hw0 := stepW_component_analyticAt i x ζ η hζ hη 0
  have hw1 := stepW_component_analyticAt i x ζ η hζ hη 1
  simp only [stageSigma_def, dotProduct, Fin.sum_univ_two]
  fun_prop

/-- Helper for eq:polar-slow-drift: unit radial multipliers make the
zero-scale normalized secant equal to one. -/
theorem stageSigma_at_zero (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    stageSigma i 0 x 1 1 = 1 := by
  simp [stageSigma_def, stepW_def, stepV_def]

/-- Helper for eq:polar-slow-drift: the actual normalized stage has the cubic
first-diagonal increment determined by its first gradient-change component. -/
theorem stage_first_cubic (i : Fin 2) (x : ℝ × ℝ × ℝ) (hC : x.2.1 ≠ 0)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0)
    (hζone : ζ 0 = 1) (hηone : η 0 = 1) (b : ℝ)
    (hw : (fun t : ℝ ↦ stepW i t x (ζ t) (η t) 0 - b * t ^ 3)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ (stage i t x (ζ t) (η t)).1 -
      (x.1 + 2 * b * (x.1 * slope x - x.2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  let w : ℝ → Fin 2 → ℝ := fun t ↦ stepW i t x (ζ t) (η t)
  let σ : ℝ → ℝ := fun t ↦ stageSigma i t x (ζ t) (η t)
  have hσ : AnalyticAt ℝ σ 0 := stageSigma_analyticAt i x ζ η hζ hη
  have hσone : σ 0 = 1 := by
    dsimp only [σ]
    rw [hζone, hηone, stageSigma_at_zero]
  have hσne : σ 0 ≠ 0 := by
    rw [hσone]
    exact one_ne_zero
  have hwcontinuous : ∀ j, ContinuousAt (fun t ↦ w t j) 0 := by
    intro j
    exact (stepW_component_analyticAt i x ζ η hζ hη j).continuousAt
  have hY := preRotation_entry_continuousAt x w σ hwcontinuous hσ.continuousAt hσne
  have hrotation := rotation_firstDiagonal_isBigO i
    (fun t ↦ preRotation x (w t) (σ t)) hY
  have hpre := preRotation_first_cubic x hC w σ b hσ hσone hw
  have hsum := hrotation.add hpre
  have heq (t : ℝ) :
      (rotation i t * preRotation x (w t) (σ t) * (rotation i t).transpose) 0 0 -
          preRotation x (w t) (σ t) 0 0 +
        (preRotation x (w t) (σ t) 0 0 -
          (x.1 + 2 * b * (x.1 * slope x - x.2.1) * t ^ 3)) =
      (stage i t x (ζ t) (η t)).1 -
        (x.1 + 2 * b * (x.1 * slope x - x.2.1) * t ^ 3) := by
    rw [stage_apply, stageMatrix_eq_preRotation]
    dsimp only [w, σ]
    ring
  exact hsum.congr_left heq

/-- Helper for eq:polar-slow-drift: the first actual feedback-controlled stage
has cubic first-diagonal increment `-ℓ * (A * Q - C) / baseAngle`. -/
theorem evenStage_first_cubic (L κ : ℝ) (x₀ x : ℝ × ℝ × ℝ)
    (hC : x.2.1 ≠ 0) :
    (fun t : ℝ ↦ (cycleStage L κ 0 t x₀ x).1 -
      (x.1 + (-L * (κ / x₀.1) ^ 2 / baseAngle) *
        (x.1 * slope x - x.2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hfeedback : AnalyticAt ℝ (fun t ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  have hfeedbackOne : feedback L κ 0 x₀ = 1 := by
    simp [feedback_def]
  have hstage := stage_first_cubic 0 x hC (fun _ ↦ 1)
    (fun t ↦ feedback L κ t x₀) analyticAt_const hfeedback rfl hfeedbackOne
    (-L * (κ / x₀.1) ^ 2 / (2 * baseAngle)) (evenStepW_first_cubic L κ x₀ x)
  have hcoefficient : 2 * (-L * (κ / x₀.1) ^ 2 / (2 * baseAngle)) =
      -L * (κ / x₀.1) ^ 2 / baseAngle := by
    ring
  simpa only [cycleStage_apply, Fin.isValue, Matrix.cons_val_zero, hcoefficient]
    using hstage

/-- Helper for eq:polar-slow-drift: the second actual feedback-controlled stage
has cubic first-diagonal increment `2 * ℓ * (A * Q - C) / baseAngle`. -/
theorem oddStage_first_cubic (L κ : ℝ) (x₀ x : ℝ × ℝ × ℝ)
    (hC : x.2.1 ≠ 0) :
    (fun t : ℝ ↦ (cycleStage L κ 1 t x₀ x).1 -
      (x.1 + (2 * (L * (κ / x₀.1) ^ 2 / baseAngle)) *
        (x.1 * slope x - x.2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hfeedback : AnalyticAt ℝ (fun t ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  have hfeedbackOne : feedback L κ 0 x₀ = 1 := by
    simp [feedback_def]
  have hstage := stage_first_cubic 1 x hC
    (fun t ↦ feedback L κ t x₀) (fun _ ↦ 1) hfeedback analyticAt_const
    hfeedbackOne rfl (L * (κ / x₀.1) ^ 2 / baseAngle)
    (oddStepW_first_cubic L κ x₀ x)
  simpa only [cycleStage_apply, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using hstage

end DFP.Polar.Normalized

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: the first diagonal coordinate of the even
cycle state is its normalization parameter. -/
theorem evenState_firstDiagonal (A : ℝ) : (evenState A).1 = A := by
  rw [evenState_apply]

/-- Helper for eq:polar-slow-drift: the first diagonal coordinate of the odd
cycle state is its normalization parameter. -/
theorem oddState_firstDiagonal (A : ℝ) : (oddState A).1 = A := by
  rw [oddState_apply]

/-- Helper for eq:polar-slow-drift: on the even cycle curve, the actual first
stage has the manuscript's cubic coefficient `-ℓ(A) * A * (2a - ν(A)) / a`. -/
theorem evenState_stage_first_cubic (L κ A : ℝ) (hA : A ∈ normalizationSet) :
    (fun t : ℝ ↦ (Normalized.cycleStage L κ 0 t (evenState A) (evenState A)).1 -
      (A + (-L * (κ / A) ^ 2 / baseAngle) *
        (A * (2 * baseAngle - inverseParameter A)) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hC := (evenState_mapsTo_positive hA).2.1
  have hstage := Normalized.evenStage_first_cubic L κ
    (evenState A) (evenState A) (ne_of_gt hC)
  rw [evenState_radialDefect A hA] at hstage
  simpa only [evenState_firstDiagonal] using hstage

/-- Helper for eq:polar-slow-drift: on the odd cycle curve, the actual second
stage has the manuscript's cubic coefficient `2 * ℓ(A) * A * (a + ν(A)) / a`. -/
theorem oddState_stage_first_cubic (L κ A : ℝ) (hA : A ∈ normalizationSet) :
    (fun t : ℝ ↦ (Normalized.cycleStage L κ 1 t (evenState A) (oddState A)).1 -
      (A + (2 * (L * (κ / A) ^ 2 / baseAngle)) *
        (A * (baseAngle + inverseParameter A)) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hC := (oddState_mapsTo_positive hA).2.1
  have hstage := Normalized.oddStage_first_cubic L κ
    (evenState A) (oddState A) (ne_of_gt hC)
  rw [oddState_radialDefect A hA] at hstage
  simpa only [evenState_firstDiagonal, oddState_firstDiagonal] using hstage

end DFP.Polar.TwoCycle

namespace DFP.Polar.Normalized

/-- Helper for eq:polar-slow-drift: the positive cubic-root branch is analytic
at zero scale. -/
theorem unitRoot_analyticAt_zero : AnalyticAt ℝ unitRoot 0 := by
  have hpoly : AnalyticAt ℝ (fun t : ℝ ↦ 1 + t ^ 3) 0 := by fun_prop
  have hpositive : 0 < (1 : ℝ) + 0 ^ 3 := by norm_num
  rw [funext unitRoot_def]
  exact ((hpoly.log hpositive).div_const).rexp'

/-- Helper for eq:polar-slow-drift: cubing the positive root recovers the
source's cubic scale polynomial. -/
theorem unitRoot_cube (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    unitRoot t ^ 3 = 1 + t ^ 3 := by
  rw [unitRoot_def, ← Real.exp_nat_mul]
  calc
    Real.exp (3 * (Real.log (1 + t ^ 3) / 3)) =
        Real.exp (Real.log (1 + t ^ 3)) := by
      congr 1
      ring
    _ = 1 + t ^ 3 := Real.exp_log ht

/-- Helper for eq:polar-slow-drift: the first-diagonal rescaling defect beyond
its cubic term factors exactly through `t ^ 6` on the positive root branch. -/
theorem rescale_firstDiagonalFactor_sub_cubic (t : ℝ) (ht : 0 < 1 + t ^ 3) :
    rescaleFactor t ^ 2 - (1 - (4 / 3 : ℝ) * t ^ 3) =
      t ^ 6 *
        ((4 * unitRoot t ^ 5 + 8 * unitRoot t ^ 4 + 12 * unitRoot t ^ 3 +
          9 * unitRoot t ^ 2 + 6 * unitRoot t + 3) /
          (3 * unitRoot t ^ 4 * (unitRoot t ^ 2 + unitRoot t + 1) ^ 2)) := by
  have hrootPositive : 0 < unitRoot t := by
    rw [unitRoot_def]
    exact Real.exp_pos _
  have hdenom : unitRoot t ^ 2 + unitRoot t + 1 ≠ 0 := by
    nlinarith [sq_nonneg (unitRoot t)]
  have hcubic : t ^ 3 = (unitRoot t - 1) *
      (unitRoot t ^ 2 + unitRoot t + 1) := by
    calc
      t ^ 3 = unitRoot t ^ 3 - 1 := by
        rw [unitRoot_cube t ht]
        ring
      _ = (unitRoot t - 1) * (unitRoot t ^ 2 + unitRoot t + 1) := by ring
  have hsix : t ^ 6 = (t ^ 3) ^ 2 := by ring
  rw [rescaleFactor_def, hsix, hcubic]
  field_simp [hrootPositive.ne', hdenom]
  ring

/-- Helper for eq:polar-slow-drift: the actual first-diagonal boundary rescaling
factor has cubic coefficient `-4 / 3` and an order-six remainder. -/
theorem rescale_firstDiagonalFactor_cubic :
    (fun t : ℝ ↦ rescaleFactor t ^ 2 - (1 - (4 / 3 : ℝ) * t ^ 3))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
  let q : ℝ → ℝ := fun t ↦
    (4 * unitRoot t ^ 5 + 8 * unitRoot t ^ 4 + 12 * unitRoot t ^ 3 +
      9 * unitRoot t ^ 2 + 6 * unitRoot t + 3) /
      (3 * unitRoot t ^ 4 * (unitRoot t ^ 2 + unitRoot t + 1) ^ 2)
  have hroot := unitRoot_analyticAt_zero.continuousAt
  have hq : ContinuousAt q 0 := by
    dsimp only [q]
    fun_prop (disch := norm_num [unitRoot_def])
  have hbound := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 6) (𝓝 0)).mul
    (hq.isBigO_one ℝ)
  have hpositive : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t ^ 3 := by
    have hc : ContinuousAt (fun t : ℝ ↦ 1 + t ^ 3) 0 := by fun_prop
    have hzero : 0 < (1 : ℝ) + 0 ^ 3 := by norm_num
    exact hc.eventually (Ioi_mem_nhds hzero)
  have hfactor : (fun t : ℝ ↦ t ^ 6 * q t) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ rescaleFactor t ^ 2 - (1 - (4 / 3 : ℝ) * t ^ 3)) := by
    filter_upwards [hpositive] with t ht
    exact (rescale_firstDiagonalFactor_sub_cubic t ht).symm
  have hbound' : (fun t : ℝ ↦ t ^ 6 * q t) =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
    simpa only [mul_one] using hbound
  exact hbound'.congr' hfactor Filter.EventuallyEq.rfl

end DFP.Polar.Normalized

namespace DFP.Polar.Normalized

/-- Helper for eq:polar-slow-drift: slope is analytic along a regular analytic
state path. -/
theorem slope_along_analyticAt (X : ℝ → ℝ × ℝ × ℝ)
    (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0) :
    AnalyticAt ℝ (fun t ↦ slope (X t)) 0 := by
  have hCV : AnalyticAt ℝ (fun t ↦ (X t).2) 0 :=
    AnalyticAt.comp analyticAt_snd hX
  have hCpath : AnalyticAt ℝ (fun t ↦ (X t).2.1) 0 :=
    AnalyticAt.comp analyticAt_fst hCV
  have hV : AnalyticAt ℝ (fun t ↦ (X t).2.2) 0 :=
    AnalyticAt.comp analyticAt_snd hCV
  simp only [slope_def]
  exact hV.fun_div hCpath hC

/-- Helper for eq:polar-slow-drift: continuous state, slope, gradient change,
and nonzero secant paths give continuous pre-rotation bracket entries. -/
theorem preRotation_along_entry_continuousAt (X : ℝ → ℝ × ℝ × ℝ)
    (w : ℝ → Fin 2 → ℝ) (σ : ℝ → ℝ)
    (hX : ContinuousAt X 0) (hQ : ContinuousAt (fun t ↦ slope (X t)) 0)
    (hw : ∀ j, ContinuousAt (fun t ↦ w t j) 0)
    (hσ : ContinuousAt σ 0) (hσ0 : σ 0 ≠ 0) (r c : Fin 2) :
    ContinuousAt (fun t ↦ preRotation (X t) (w t) (σ t) r c) 0 := by
  have hA := hX.fst
  have hC := hX.snd.fst
  have hV := hX.snd.snd
  have hw0 := hw 0
  have hw1 := hw 1
  have hinv := hσ.inv₀ hσ0
  simp only [preRotation_def, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, RealSymmetric2.matrix_eq, Matrix.of_apply, stepV_def,
    smul_eq_mul]
  fin_cases r
  all_goals fin_cases c
  all_goals simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals fun_prop

/-- Helper for eq:polar-slow-drift: the cubic first-diagonal increment along
an analytic state path uses its zero-scale radial defect. -/
theorem preRotation_first_cubic_along (X : ℝ → ℝ × ℝ × ℝ)
    (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0)
    (w : ℝ → Fin 2 → ℝ) (σ : ℝ → ℝ) (b : ℝ)
    (hσ : AnalyticAt ℝ σ 0) (hσone : σ 0 = 1)
    (hw : (fun t : ℝ ↦ w t 0 - b * t ^ 3) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ preRotation (X t) (w t) (σ t) 0 0 -
      ((X t).1 + 2 * b * ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  let D : ℝ → ℝ := fun t ↦ (X t).1 * slope (X t) - (X t).2.1
  have hA : AnalyticAt ℝ (fun t ↦ (X t).1) 0 :=
    AnalyticAt.comp analyticAt_fst hX
  have hCV : AnalyticAt ℝ (fun t ↦ (X t).2) 0 :=
    AnalyticAt.comp analyticAt_snd hX
  have hCpath : AnalyticAt ℝ (fun t ↦ (X t).2.1) 0 :=
    AnalyticAt.comp analyticAt_fst hCV
  have hQ := slope_along_analyticAt X hX hC
  have hD : AnalyticAt ℝ D 0 := by
    dsimp only [D]
    fun_prop
  have hσne : σ 0 ≠ 0 := by
    rw [hσone]
    exact one_ne_zero
  have hinv : AnalyticAt ℝ (fun t ↦ (σ t)⁻¹) 0 := hσ.fun_inv hσne
  have hinvDefect : (fun t : ℝ ↦ (σ t)⁻¹ - 1)
      =O[𝓝 0] (fun t : ℝ ↦ t) := by
    simpa only [hσone, inv_one, sub_zero] using hinv.differentiableAt.isBigO_sub
  have hfirst : (fun t : ℝ ↦ (w t 0 - b * t ^ 3) * (σ t)⁻¹)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [mul_one] using hw.mul (hinv.continuousAt.isBigO_one ℝ)
  have hpowers (t : ℝ) : t ^ 3 * t = t ^ 4 := by ring
  have hsecond : (fun t : ℝ ↦ b * (t ^ 3 * ((σ t)⁻¹ - 1)))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) :=
    (((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).mul
      hinvDefect).const_mul_left b).congr_right hpowers
  have hquotient : (fun t : ℝ ↦ w t 0 / σ t - b * t ^ 3)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    apply (hfirst.add hsecond).congr_left
    intro t
    ring
  have hlinear : (fun t : ℝ ↦ 2 * D t * (w t 0 / σ t - b * t ^ 3))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [one_mul] using
      ((hD.continuousAt.isBigO_one ℝ).const_mul_left 2).mul hquotient
  have hDdefect : (fun t : ℝ ↦ D t - D 0) =O[𝓝 0] (fun t : ℝ ↦ t) := by
    simpa only [sub_zero] using hD.differentiableAt.isBigO_sub
  have hvariation : (fun t : ℝ ↦ 2 * b * (t ^ 3 * (D t - D 0)))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) :=
    (((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).mul
      hDdefect).const_mul_left (2 * b)).congr_right hpowers
  have hwthree : (fun t : ℝ ↦ w t 0) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    have hfourThree : (fun t : ℝ ↦ t ^ 4) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) :=
      (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self 3)).isBigO
    simpa only [sub_add_cancel] using (hw.trans hfourThree).add
      ((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).const_mul_left b)
  have hcofactor : ContinuousAt
      (fun t : ℝ ↦ (σ t + slope (X t) * D t) / σ t ^ 2) 0 := by
    have hσcontinuous := hσ.continuousAt
    have hQcontinuous := hQ.continuousAt
    have hDcontinuous := hD.continuousAt
    have hnonzero := pow_ne_zero 2 hσne
    fun_prop (disch := assumption)
  have hsquare : (fun t : ℝ ↦
      (σ t + slope (X t) * D t) / σ t ^ 2 * w t 0 ^ 2)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hlt : (4 : ℕ) < 6 := by norm_num
    have hpower : (fun t : ℝ ↦ w t 0 ^ 2) =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
      simpa only [← pow_mul, Nat.reduceMul] using hwthree.pow 2
    have hsix : (fun t : ℝ ↦
        (σ t + slope (X t) * D t) / σ t ^ 2 * w t 0 ^ 2)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
      simpa only [one_mul] using (hcofactor.isBigO_one ℝ).mul hpower
    exact hsix.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO
  have heq :
      (fun t : ℝ ↦ 2 * D t * (w t 0 / σ t - b * t ^ 3) +
        2 * b * (t ^ 3 * (D t - D 0)) +
        (σ t + slope (X t) * D t) / σ t ^ 2 * w t 0 ^ 2)
        =ᶠ[𝓝 0]
      (fun t : ℝ ↦ preRotation (X t) (w t) (σ t) 0 0 -
        ((X t).1 + 2 * b * ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3)) := by
    filter_upwards [hσ.continuousAt.eventually_ne hσne,
      hCpath.continuousAt.eventually_ne hC] with t htσ htC
    rw [preRotation_firstDiagonal (X t) (w t) (σ t) htC htσ]
    dsimp only [D]
    ring
  exact ((hlinear.add hvariation).add hsquare).congr' heq Filter.EventuallyEq.rfl

/-- Helper for eq:polar-slow-drift: analytic regular state and radial
multiplier paths give analytic normalized gradient-change components. -/
theorem stepW_along_component_analyticAt (i : Fin 2) (X : ℝ → ℝ × ℝ × ℝ)
    (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0) (j : Fin 2) :
    AnalyticAt ℝ (fun t ↦ stepW i t (X t) (ζ t) (η t) j) 0 := by
  have hQ := slope_along_analyticAt X hX hC
  have hcot := cotFactor_analyticAt i
  fin_cases j
  · simp only [Fin.zero_eta, stepW_def, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simpa only [Fin.mk_one, stepW_def, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using hη

/-- Helper for eq:polar-slow-drift: the normalized secant is analytic along
regular analytic state and radial multiplier paths. -/
theorem stageSigma_along_analyticAt (i : Fin 2) (X : ℝ → ℝ × ℝ × ℝ)
    (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0) :
    AnalyticAt ℝ (fun t ↦ stageSigma i t (X t) (ζ t) (η t)) 0 := by
  have hQ := slope_along_analyticAt X hX hC
  have hw0 := stepW_along_component_analyticAt i X hX hC ζ η hζ hη 0
  have hw1 := stepW_along_component_analyticAt i X hX hC ζ η hζ hη 1
  simp only [stageSigma_def, stepV_def, dotProduct, Fin.sum_univ_two,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop

/-- Helper for eq:polar-slow-drift: an analytic state path through a regular
state has the source's cubic stage increment evaluated at that limiting state. -/
theorem stage_first_cubic_along (i : Fin 2) (X : ℝ → ℝ × ℝ × ℝ)
    (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0)
    (ζ η : ℝ → ℝ) (hζ : AnalyticAt ℝ ζ 0) (hη : AnalyticAt ℝ η 0)
    (hζone : ζ 0 = 1) (hηone : η 0 = 1) (b : ℝ)
    (hw : (fun t : ℝ ↦ stepW i t (X t) (ζ t) (η t) 0 - b * t ^ 3)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ (stage i t (X t) (ζ t) (η t)).1 -
      ((X t).1 + 2 * b * ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  let w : ℝ → Fin 2 → ℝ := fun t ↦ stepW i t (X t) (ζ t) (η t)
  let σ : ℝ → ℝ := fun t ↦ stageSigma i t (X t) (ζ t) (η t)
  have hσ : AnalyticAt ℝ σ 0 := stageSigma_along_analyticAt i X hX hC ζ η hζ hη
  have hσone : σ 0 = 1 := by
    dsimp only [σ]
    rw [hζone, hηone, stageSigma_at_zero]
  have hσne : σ 0 ≠ 0 := by
    rw [hσone]
    exact one_ne_zero
  have hQ := slope_along_analyticAt X hX hC
  have hwcontinuous : ∀ j, ContinuousAt (fun t ↦ w t j) 0 := by
    intro j
    exact (stepW_along_component_analyticAt i X hX hC ζ η hζ hη j).continuousAt
  have hY := preRotation_along_entry_continuousAt X w σ hX.continuousAt
    hQ.continuousAt hwcontinuous hσ.continuousAt hσne
  have hrotation := rotation_firstDiagonal_isBigO i
    (fun t ↦ preRotation (X t) (w t) (σ t)) hY
  have hpre := preRotation_first_cubic_along X hX hC w σ b hσ hσone hw
  have hsum := hrotation.add hpre
  have heq (t : ℝ) :
      (rotation i t * preRotation (X t) (w t) (σ t) * (rotation i t).transpose) 0 0 -
          preRotation (X t) (w t) (σ t) 0 0 +
        (preRotation (X t) (w t) (σ t) 0 0 -
          ((X t).1 + 2 * b * ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3)) =
      (stage i t (X t) (ζ t) (η t)).1 -
        ((X t).1 + 2 * b * ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3) := by
    rw [stage_apply, stageMatrix_eq_preRotation]
    dsimp only [w, σ]
    ring
  exact hsum.congr_left heq

/-- Helper for eq:polar-slow-drift: the actual odd stage along an analytic
state path keeps its cubic coefficient at the path's limiting state. -/
theorem oddStage_first_cubic_along (L κ : ℝ) (x₀ : ℝ × ℝ × ℝ)
    (X : ℝ → ℝ × ℝ × ℝ) (hX : AnalyticAt ℝ X 0) (hC : (X 0).2.1 ≠ 0) :
    (fun t : ℝ ↦ (cycleStage L κ 1 t x₀ (X t)).1 -
      ((X t).1 + (2 * (L * (κ / x₀.1) ^ 2 / baseAngle)) *
        ((X 0).1 * slope (X 0) - (X 0).2.1) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hfeedback : AnalyticAt ℝ (fun t ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  have hfeedbackOne : feedback L κ 0 x₀ = 1 := by simp [feedback_def]
  have hQ := (slope_along_analyticAt X hX hC).continuousAt
  have hfb := hfeedback.continuousAt
  have hcofactor : ContinuousAt
      (fun t ↦ -feedback L κ t x₀ * (slope (X t) - slope (X 0))) 0 := by
    fun_prop
  have hcorrection :
      (fun t : ℝ ↦ stepW 1 t (X t) (feedback L κ t x₀) 1 0 -
        stepW 1 t (X 0) (feedback L κ t x₀) 1 0)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hproduct :
        (fun t : ℝ ↦ (-feedback L κ t x₀ * (slope (X t) - slope (X 0))) * t ^ 4)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
      simpa only [one_mul] using (hcofactor.isBigO_one ℝ).mul
        (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 4) (𝓝 0))
    apply hproduct.congr_left
    intro t
    simp only [stepW_def, Fin.isValue, Matrix.cons_val_zero]
    ring
  have hw : (fun t : ℝ ↦ stepW 1 t (X t) (feedback L κ t x₀) 1 0 -
      (L * (κ / x₀.1) ^ 2 / baseAngle) * t ^ 3)
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [sub_add_sub_cancel] using
      hcorrection.add (oddStepW_first_cubic L κ x₀ (X 0))
  have hstage := stage_first_cubic_along 1 X hX hC
    (fun t ↦ feedback L κ t x₀) (fun _ ↦ 1) hfeedback analyticAt_const
    hfeedbackOne rfl (L * (κ / x₀.1) ^ 2 / baseAngle) hw
  simpa only [cycleStage_apply, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using hstage

end DFP.Polar.Normalized

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: the two actual stages on the even cycle
curve have the sum of the manuscript's two cubic feedback contributions. -/
theorem twoStep_evenState_first_cubic (νStar A : ℝ) (hA : A ∈ normalizationSet) :
    (fun t : ℝ ↦
      (Normalized.twoStep (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
        (evenState A)).1 -
      (A + (restoringDrift νStar A + 4 / 3 * A) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  let L := 4 * baseAngle / (9 * νStar)
  let κ := cycleK νStar
  let X : ℝ → ℝ × ℝ × ℝ :=
    fun t ↦ Normalized.cycleStage L κ 0 t (evenState A) (evenState A)
  have hX : AnalyticAt ℝ X 0 :=
    Normalized.cycleStage_analyticAt_zero L κ 0 (evenState A) (evenState A)
  have hXzero : X 0 = oddState A := by
    dsimp only [X]
    rw [Normalized.cycleStage_zero, Normalized.limitAngle_zero, evenToOdd A hA]
  have hC : (X 0).2.1 ≠ 0 := by
    rw [hXzero]
    exact ne_of_gt (oddState_mapsTo_positive hA).2.1
  have hApos : 0 < A := by
    simpa only [evenState_firstDiagonal, Set.mem_Ioi] using (evenState_mapsTo_positive hA).1
  have hodd := Normalized.oddStage_first_cubic_along L κ (evenState A) X hX hC
  rw [hXzero, oddState_radialDefect A hA, evenState_firstDiagonal] at hodd
  have heven := evenState_stage_first_cubic L κ A hA
  have hsum := hodd.add heven
  apply hsum.congr_left
  intro t
  rw [Normalized.twoStep_def, restoringDrift_eq_stageSum νStar A hApos.ne']
  dsimp only [L, κ, X]
  ring

end DFP.Polar.TwoCycle

namespace DFP.Polar.Normalized

/-- Helper for eq:polar-slow-drift: boundary rescaling subtracts `4 * A / 3`
from the cubic coefficient of a first-diagonal expansion. -/
theorem rescale_first_cubic_of_expansion (f : ℝ → ℝ) (A B : ℝ)
    (hf : (fun t : ℝ ↦ f t - (A + B * t ^ 3))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    (fun t : ℝ ↦ rescaleFactor t ^ 2 * f t -
      (A + (B - 4 / 3 * A) * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have hrescale := (rescaleFactor_analyticAt.fun_pow 2).continuousAt.isBigO_one ℝ
  have hfirst : (fun t : ℝ ↦ rescaleFactor t ^ 2 * (f t - (A + B * t ^ 3)))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    simpa only [one_mul] using hrescale.mul hf
  have hpoly : ContinuousAt (fun t : ℝ ↦ A + B * t ^ 3) 0 := by fun_prop
  have hlt : (4 : ℕ) < 6 := by norm_num
  have hsecond : (fun t : ℝ ↦
      (rescaleFactor t ^ 2 - (1 - (4 / 3 : ℝ) * t ^ 3)) * (A + B * t ^ 3))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    have hsix : (fun t : ℝ ↦
        (rescaleFactor t ^ 2 - (1 - (4 / 3 : ℝ) * t ^ 3)) * (A + B * t ^ 3))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ 6) := by
      simpa only [mul_one] using rescale_firstDiagonalFactor_cubic.mul (hpoly.isBigO_one ℝ)
    exact hsix.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO
  have hthird : (fun t : ℝ ↦ (-(4 / 3 : ℝ) * B) * t ^ 6)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) :=
    ((Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 6) (𝓝 0)).const_mul_left
      (-(4 / 3 : ℝ) * B)).trans (Asymptotics.isLittleO_pow_pow hlt).isBigO
  apply ((hfirst.add hsecond).add hthird).congr_left
  intro t
  ring

end DFP.Polar.Normalized

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: the actual normalized two-stage map on the
source's even cycle curve has cubic coefficient `restoringDrift νStar A`. -/
theorem map_evenState_first_cubic (νStar A : ℝ) (hA : A ∈ normalizationSet) :
    (fun t : ℝ ↦
      (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t (evenState A)).1 -
        (A + t ^ 3 * restoringDrift νStar A))
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
  have htwo := twoStep_evenState_first_cubic νStar A hA
  have hrescale := Normalized.rescale_first_cubic_of_expansion
    (fun t ↦ (Normalized.twoStep (4 * baseAngle / (9 * νStar))
      (cycleK νStar) t (evenState A)).1)
    A (restoringDrift νStar A + 4 / 3 * A) htwo
  apply hrescale.congr_left
  intro t
  rw [Normalized.map_def, Normalized.rescale_apply]
  dsimp only
  ring

end DFP.Polar.TwoCycle

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: the even source cycle curve is analytic
where its selected inverse parameter is analytic. -/
theorem evenState_analyticAt (A : ℝ) (hA : A ∈ normalizationSet)
    (hν : ContDiffAt ℝ ω inverseParameter A) : AnalyticAt ℝ evenState A := by
  have hparameter := inverseParameter_mapsTo hA
  rw [parameterSet_def] at hparameter
  have hdenom : 2 * inverseParameter A - baseAngle ≠ 0 := by
    have ha := baseAngle_pos
    linarith [hparameter.1]
  have hW : AnalyticAt ℝ cycleW (inverseParameter A) := by
    rw [funext cycleW_def]
    fun_prop (disch := assumption)
  have hWpath : AnalyticAt ℝ (fun x ↦ cycleW (inverseParameter x)) A :=
    hW.comp hν.analyticAt
  have hC : AnalyticAt ℝ (fun x ↦ x * cycleW (inverseParameter x)) A := by
    fun_prop
  have hV : AnalyticAt ℝ (fun x ↦ 1 + x * cycleW (inverseParameter x) ^ 2) A := by
    fun_prop
  rw [funext evenState_apply]
  exact analyticAt_id.prod (hC.prod hV)

/-- Helper for eq:polar-slow-drift: the scalar drift is analytic on the
regular selected inverse branch. -/
theorem restoringDrift_analyticAt (νStar A : ℝ) (hA : A ≠ 0)
    (hν : ContDiffAt ℝ ω inverseParameter A) :
    AnalyticAt ℝ (restoringDrift νStar) A := by
  have hinverse := hν.analyticAt
  rw [funext (restoringDrift_apply νStar)]
  fun_prop (disch := assumption)

/-- Helper for eq:polar-slow-drift: the actual cubic remainder is jointly
analytic in cycle normalization and scale on the regular source curve. -/
theorem map_evenState_cubicRemainder_analyticAt (νStar A : ℝ)
    (hA : A ∈ normalizationSet) (hν : ContDiffAt ℝ ω inverseParameter A) :
    AnalyticAt ℝ
      (fun p : ℝ × ℝ ↦
        (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar)
          p.2 (evenState p.1)).1 - (p.1 + p.2 ^ 3 * restoringDrift νStar p.1))
      (A, 0) := by
  have hpositive := evenState_mapsTo_positive hA
  have hApos : 0 < A := by
    simpa only [evenState_firstDiagonal, Set.mem_Ioi] using hpositive.1
  have hC₁ : 0 <
      (Normalized.leadingStage (Normalized.limitAngle 0) (evenState A)).2.1 := by
    rw [Normalized.limitAngle_zero, evenToOdd A hA]
    exact (oddState_mapsTo_positive hA).2.1
  have hmap := Normalized.map_analyticAt_zero
    (4 * baseAngle / (9 * νStar)) (cycleK νStar) (evenState A)
    hpositive.1 hpositive.2.1 hC₁
  have hcurve : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ evenState p.1) (A, 0) :=
    (evenState_analyticAt A hA hν).comp analyticAt_fst
  have hinput : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ (p.2, evenState p.1)) (A, 0) :=
    (analyticAt_snd : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ p.2) (A, 0)).prod hcurve
  have hresult : AnalyticAt ℝ (fun p : ℝ × ℝ ↦
      Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar)
        p.2 (evenState p.1)) (A, 0) := by
    have hcomposed := hmap.comp_of_eq hinput rfl
    simpa only [Function.uncurry_def, Function.comp_def] using hcomposed
  have hfirst : AnalyticAt ℝ (fun p : ℝ × ℝ ↦
      (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar)
        p.2 (evenState p.1)).1) (A, 0) :=
    AnalyticAt.comp analyticAt_fst hresult
  have hG : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ restoringDrift νStar p.1) (A, 0) := by
    have hcomposed := AnalyticAt.comp (x := (A, (0 : ℝ)))
      (f := (Prod.fst : ℝ × ℝ → ℝ))
      (g := restoringDrift νStar) (restoringDrift_analyticAt νStar A hApos.ne' hν)
      analyticAt_fst
    simpa only [Function.comp_def] using hcomposed
  have hscale : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ p.2 ^ 3) (A, 0) :=
    (analyticAt_snd : AnalyticAt ℝ (fun p : ℝ × ℝ ↦ p.2) (A, 0)).fun_pow 3
  have hmodel : AnalyticAt ℝ
      (fun p : ℝ × ℝ ↦ p.1 + p.2 ^ 3 * restoringDrift νStar p.1) (A, 0) :=
    analyticAt_fst.fun_add (hscale.fun_mul hG)
  exact hfirst.fun_sub hmodel

/-- Helper for eq:polar-slow-drift: a jointly smooth scalar family with
pointwise order-four vanishing has one quartic bound on a compact parameter set. -/
private theorem uniformQuarticBound (f : ℝ → ℝ → ℝ) (𝒦 : Set ℝ)
    (h𝒦 : IsCompact 𝒦)
    (hjoint : ∀ A ∈ 𝒦, ContDiffAt ℝ 4 (Function.uncurry f) (A, 0))
    (horder : ∀ A ∈ 𝒦, (f A) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4)) :
    ∃ C > 0, ∃ ε > 0, ∀ A ∈ 𝒦, ∀ t : ℝ, ‖t‖ < ε → ‖f A t‖ ≤ C * ‖t ^ 4‖ := by
  let J : ℝ → FiniteTaylorJet ℝ ℝ ℝ 4 :=
    fun A ↦ FiniteTaylorJet.ofFunction ℝ 4 (f A) 0
  have hJ : FiniteTaylorJet.IsUniformOn f J 0 𝒦 :=
    FiniteTaylorJet.isUniformOn_of_contDiffAt 4 f 0 𝒦 h𝒦 hjoint
  have hzero : ∀ A ∈ 𝒦, ∀ n : Fin 5, (n : ℕ) < 4 → (J A).coeff n = 0 := by
    intro A hA n hn
    have hfixed : ContDiffAt ℝ 4 (f A) 0 := by
      have hinput : ContDiffAt ℝ 4 (fun t : ℝ ↦ (A, t)) 0 :=
        contDiffAt_const.prodMk contDiffAt_id
      simpa only [Function.comp_def, Function.uncurry_def] using
        (hjoint A hA).comp 0 hinput
    have hdegree : (3 : ℕ∞ω) ≤ 4 := by norm_num
    have horderZero : (fun t : ℝ ↦ f A (0 + t) - (0 : ℝ))
        =O[𝓝 0] (fun t : ℝ ↦ t ^ (3 + 1)) := by
      simpa only [zero_add, sub_zero] using horder A hA
    have hjet := FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
      (hfixed.of_le hdegree) (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : ℝ ↦ (0 : ℝ)) 0)
      horderZero
    have hderiv := (FiniteTaylorJet.ofFunction_eq_zeroFunction_iff 3 (f A) 0).mp hjet
    have hlow : iteratedDeriv (n : ℕ) (f A) 0 = 0 := hderiv ⟨n, hn⟩
    apply ContinuousMultilinearMap.ext_ring
    simp only [J, FiniteTaylorJet.coeff_ofFunction_apply,
      ← iteratedDeriv_eq_iteratedFDeriv, hlow, smul_zero, zero_apply]
  obtain ⟨B, hB, htop⟩ := hJ.boundedCoeff (4 : Fin 5)
  obtain ⟨ε, hε, hrem⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound
    (hJ.remainder 1 zero_lt_one)
  have hC : 0 < B + 1 := by linarith
  refine ⟨B + 1, hC, ε, hε, ?_⟩
  intro A hA t ht
  have heval : (J A).eval t = (J A).coeff (4 : Fin 5) (fun _ : Fin 4 ↦ t) := by
    rw [FiniteTaylorJet.eval_eq_sum]
    apply Finset.sum_eq_single (4 : Fin 5)
    · intro n _ hn
      have hnlt : (n : ℕ) < 4 := by omega
      rw [hzero A hA n hnlt]
      rfl
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  have htopBound : ‖(J A).eval t‖ ≤ B * ‖t ^ (4 : ℕ)‖ := by
    rw [heval]
    calc
      ‖(J A).coeff (4 : Fin 5) (fun _ : Fin 4 ↦ t)‖ ≤
          ‖(J A).coeff (4 : Fin 5)‖ * ∏ _ : Fin 4, ‖t‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ B * ∏ _ : Fin 4, ‖t‖ :=
        mul_le_mul_of_nonneg_right (htop A hA) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg t)
      _ = B * ‖t ^ (4 : ℕ)‖ := by simp only [Finset.prod_const, Finset.card_fin, norm_pow]
  have hremainder : ‖(J A).remainder (f A) 0 t‖ ≤ ‖t ^ (4 : ℕ)‖ := by
    simpa only [Real.rpow_natCast, one_mul, norm_pow] using hrem A hA t ht
  have hvalue : f A t = (J A).remainder (f A) 0 t + (J A).eval t := by
    rw [FiniteTaylorJet.remainder_def, zero_add]
    ring
  rw [hvalue]
  calc
    ‖(J A).remainder (f A) 0 t + (J A).eval t‖ ≤
        ‖(J A).remainder (f A) 0 t‖ + ‖(J A).eval t‖ := norm_add_le _ _
    _ ≤ ‖t ^ (4 : ℕ)‖ + B * ‖t ^ (4 : ℕ)‖ := add_le_add hremainder htopBound
    _ = (B + 1) * ‖t ^ (4 : ℕ)‖ := by ring

end DFP.Polar.TwoCycle

namespace DFP.Polar.TwoCycle

/-- Helper for eq:polar-slow-drift: on any fixed compact part of the regular
source cycle curve, the actual normalized map has a uniform order-four
remainder after its cubic restoring term. -/
theorem map_evenState_first_cubic_uniformOn (νStar : ℝ) (𝒦 : Set ℝ)
    (h𝒦 : IsCompact 𝒦)
    (hbranch : ∀ A ∈ 𝒦, A ∈ normalizationSet ∧ ContDiffAt ℝ ω inverseParameter A) :
    ∃ C > 0, ∃ ε > 0, ∀ A ∈ 𝒦, ∀ t : ℝ, |t| < ε →
      |(Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t (evenState A)).1 -
        (A + t ^ 3 * restoringDrift νStar A)| ≤ C * |t| ^ 4 := by
  let f : ℝ → ℝ → ℝ := fun A t ↦
    (Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t (evenState A)).1 -
      (A + t ^ 3 * restoringDrift νStar A)
  have hjoint : ∀ A ∈ 𝒦, ContDiffAt ℝ 4 (Function.uncurry f) (A, 0) := by
    intro A hA
    have hregular := hbranch A hA
    have hanalytic := map_evenState_cubicRemainder_analyticAt νStar A hregular.1 hregular.2
    simpa only [Function.uncurry_def, f] using (hanalytic.contDiffAt : ContDiffAt ℝ 4 _ _)
  have horder : ∀ A ∈ 𝒦, (f A) =O[𝓝 0] (fun t : ℝ ↦ t ^ 4) := by
    intro A hA
    exact map_evenState_first_cubic νStar A (hbranch A hA).1
  obtain ⟨C, hC, ε, hε, hbound⟩ := uniformQuarticBound f 𝒦 h𝒦 hjoint horder
  refine ⟨C, hC, ε, hε, ?_⟩
  intro A hA t ht
  have hsmall : ‖t‖ < ε := by simpa only [Real.norm_eq_abs] using ht
  simpa only [f, Real.norm_eq_abs, abs_pow] using hbound A hA t hsmall

/-- eq:polar-slow-drift: for every sufficiently close choice `νStar > baseAngle`,
the actual normalized map has the stated cubic drift uniformly on a fixed
neighborhood of `KStar`, where the drift vanishes at `KStar` and its derivative
is at most a fixed negative rate stronger than `1 / 3`. All constants are
chosen before the initial cycle index. -/
theorem restoringSlowDrift :
    ∃ rate > (1 / 3 : ℝ), ∃ δ > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + δ),
      νStar ∈ parameterSet ∧ ∃ r > 0, ∃ C > 0, ∃ ε > 0,
        restoringDrift νStar (cycleK νStar) = 0 ∧
        ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
          ContDiffAt ℝ ω inverseParameter A ∧ A ∈ normalizationSet ∧ 0 < A ∧
          deriv (restoringDrift νStar) A ≤ -rate ∧
          ∀ t : ℝ, |t| < ε →
            |(Normalized.map (4 * baseAngle / (9 * νStar)) (cycleK νStar) t
              (evenState A)).1 - (A + t ^ 3 * restoringDrift νStar A)| ≤ C * |t| ^ 4 := by
  obtain ⟨rate, hrate, δ, hδ, hneighborhood⟩ := exists_uniformRestoringNeighborhood
  refine ⟨rate, hrate, δ, hδ, ?_⟩
  intro νStar hνStar
  obtain ⟨hparameter, r, hr, hbranch⟩ := hneighborhood νStar hνStar
  have hregular :
      ∀ A ∈ Set.Icc (cycleK νStar - r) (cycleK νStar + r),
        A ∈ normalizationSet ∧ ContDiffAt ℝ ω inverseParameter A := by
    intro A hA
    exact ⟨(hbranch A hA).2.1, (hbranch A hA).1⟩
  obtain ⟨C, hC, ε, hε, hbound⟩ := map_evenState_first_cubic_uniformOn νStar
    (Set.Icc (cycleK νStar - r) (cycleK νStar + r)) isCompact_Icc hregular
  refine ⟨hparameter, r, hr, C, hC, ε, hε, restoringDrift_cycleK νStar hparameter, ?_⟩
  intro A hA
  have hproperties := hbranch A hA
  exact ⟨hproperties.1, hproperties.2.1, hproperties.2.2.1,
    hproperties.2.2.2, hbound A hA⟩

end DFP.Polar.TwoCycle

