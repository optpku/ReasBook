/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.Latest.CenterEndpoints
public import DFPWolfe.Latest.CenterDesignRecovery
-- General continuity and coefficient identities need the regular coordinate
-- definitions, whose bodies are not exposed by the older public module.
import all DFPWolfe.V21.CenterManifold
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open Filter
open scoped Topology Matrix

namespace DFPWolfe.Latest.CenterDesign

open DFPWolfe.V21.CenterManifold

/-- Helper for cm-alternating-data: the regular matrix entries are continuous
at every zero-radius input with arbitrary positive limiting shape. -/
theorem regularEntries_continuousAt (q : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ × ℝ ↦
      regularEntries z.1 z.2.1 z.2.2.1 z.2.2.2) (q, 1, 0, 0) := by
  unfold regularEntries regularDenominator regularEnergy
  dsimp only
  fun_prop (disch := norm_num)

/-- Helper for cm-alternating-data: the removable eigenvalue factors are
continuous at the source zero-radius input. -/
theorem regularSpectrum_continuousAt (q : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ × ℝ ↦
      regularSpectrum z.1 z.2.1 z.2.2.1 z.2.2.2) (q, 1, 0, 0) := by
  have he := regularEntries_continuousAt q
  unfold regularSpectrum
  dsimp only
  unfold RealSymmetric2.high RealSymmetric2.gap regularDenominator regularEnergy
  fun_prop (disch := norm_num [regularEntries_zero])

/-- Helper for cm-alternating-data: the rotated gradient numerators and
eigenvector normalization are continuous at zero radius. -/
theorem regularRotatedData_continuousAt (q τ : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ × ℝ ↦
      regularRotatedData z.1 z.2.1 z.2.2.1 z.2.2.2 τ) (q, 1, 0, 0) := by
  have he := regularEntries_continuousAt q
  have hs := regularSpectrum_continuousAt q
  unfold regularRotatedData regularGradientResiduals regularDenominator
  dsimp only
  fun_prop (disch := norm_num)

/-- Helper for cm-alternating-data: the prescribed first cancellation ratio
makes the normalized transverse gradient numerator tend to one. -/
theorem firstRatio_normalization {q : ℝ} (hq : 0 < q) :
    (1 - q / (q + 1)) * (q + 1) = 1 := by
  have hqonePos : 0 < q + 1 := by linarith
  have hqone : q + 1 ≠ 0 := hqonePos.ne'
  field_simp
  ring

/-- Helper for cm-alternating-data: the actual regular first spectral update
has limiting radius multiplier q, shape 1/q, high eigenvalue one and amplitude one. -/
theorem firstRegularStep_zero {q : ℝ} (hq : 0 < q) :
    regularStep q 1 0 0 (q / (q + 1)) = (q, 1 / q, 1, 1) := by
  rw [regularStep_zero, firstRatio_normalization hq]
  simp

/-- Helper for cm-alternating-data: the general source first spectral step
is continuous at zero radius; no fixed shape two is assumed. -/
theorem firstRegularStep_continuousAt {q : ℝ} (hq : 0 < q) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ × ℝ ↦
      regularStep z.1 z.2.1 z.2.2.1 z.2.2.2 (q / (q + 1))) (q, 1, 0, 0) := by
  have hs := regularSpectrum_continuousAt q
  have hr := regularRotatedData_continuousAt q (q / (q + 1))
  unfold regularStep
  dsimp only
  fun_prop (disch := simp [regularSpectrum_zero, regularRotatedData_zero,
    firstRatio_normalization hq, hq.ne'])

/-- Helper for cm-alternating-data: the exact normalized center change
of one spectral secant step, before applying its incoming frame. -/
def centerShift (p r μ τ : ℝ) : Fin 2 → ℝ :=
  (τ * (p + 1) * μ * r / regularDenominator r μ) • ![1, r]

/-- Helper for cm-alternating-data: the source center-change formula agrees
with the displacement minus the gradient change of an actual secant step. -/
theorem centerShift_eq_secant (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * r])
    (hA : z.secantMatrix = !![1, μ; μ, 1]) :
    z.displacement - z.gradientChange = G • centerShift p r μ z.tau := by
  rw [spectralCenterDisplacement z p h r μ G hH hg hA]
  simp only [centerShift, smul_smul]
  congr 1
  ring

/-- Helper for cm-alternating-data: the two actual regular center changes
are expressed in the initial eigenbasis; the second uses the updated frame
and the spectral coordinates recovered by the first regular step. -/
def cycleCenterShift (q c₁ c₂ p h ε : ℝ) : Fin 2 → ℝ :=
  let τ₁ := q / (q + 1)
  let τ₂ := 1 / (q + 1)
  let next := regularStep p h (ε ^ 2) (c₁ * ε) τ₁
  centerShift p (ε ^ 2) (c₁ * ε) τ₁ +
    next.2.2.2 • (regularFrame p h (ε ^ 2) (c₁ * ε) τ₁ *ᵥ
      centerShift next.2.1 (ε ^ 2 * next.1) (c₂ * ε) τ₂)

/-- Helper for cm-alternating-data: the removable cubic and quintic
coefficients of the two-step center change, including the first frame rotation. -/
def cycleCoefficients (q c₁ c₂ p h ε : ℝ) : ℝ × ℝ :=
  let τ₁ := q / (q + 1)
  let next := regularStep p h (ε ^ 2) (c₁ * ε) τ₁
  let entries := regularEntries p h (ε ^ 2) (c₁ * ε)
  let C := entries.2.2 - (ε ^ 2) ^ 2 * (regularSpectrum p h (ε ^ 2) (c₁ * ε)).1
  let N := (regularRotatedData p h (ε ^ 2) (c₁ * ε) τ₁).2
  let A := τ₁ * (p + 1) * c₁ / regularDenominator (ε ^ 2) (c₁ * ε)
  let B := next.2.2.2 * (1 / (q + 1)) * (next.2.1 + 1) * c₂ * next.1 /
    regularDenominator (ε ^ 2 * next.1) (c₂ * ε)
  (A + B / N * (C + ε ^ 4 * entries.2.1 * next.1),
    A + B / N * (-entries.2.1 + C * next.1))

/-- Helper for cm-alternating-data: exact factorization exposes the cubic
horizontal and quintic vertical center scales; the minus sign in the latter
is the rotation contribution of the first low eigenvector. -/
theorem cycleCenterShift_factorization (q c₁ c₂ p h ε : ℝ) :
    cycleCenterShift q c₁ c₂ p h ε =
      ![ε ^ 3 * (cycleCoefficients q c₁ c₂ p h ε).1,
        ε ^ 5 * (cycleCoefficients q c₁ c₂ p h ε).2] := by
  unfold cycleCenterShift cycleCoefficients centerShift regularFrame
  dsimp only
  ext i
  fin_cases i
  · simp [div_eq_mul_inv]
    ring
  · simp [div_eq_mul_inv]
    ring

/-- Helper for cm-alternating-data: the removable coefficients at zero
radius are the source cubic and quintic cancellation polynomials. -/
theorem cycleCoefficients_zero {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ) :
    cycleCoefficients q c₁ c₂ q 1 0 = (q * c₁ + c₂, q * c₁ + (q - 1) * c₂) := by
  have hqonePos : 0 < q + 1 := by linarith
  have hqone : q + 1 ≠ 0 := hqonePos.ne'
  simp [cycleCoefficients, firstRegularStep_zero hq,
    regularEntries_zero, regularSpectrum_zero, regularRotatedData_zero,
    firstRatio_normalization hq, regularDenominator]
  constructor
  · field_simp [hq.ne']
    ring
  · field_simp [hq.ne']
    ring

/-- Helper for cm-alternating-data: the exact source cubic and quintic
coefficient functions are continuous at the general limiting state. -/
theorem cycleCoefficients_continuousAt {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ) :
    ContinuousAt (fun z : ℝ × ℝ × ℝ ↦ cycleCoefficients q c₁ c₂ z.1 z.2.1 z.2.2)
      (q, 1, 0) := by
  have hpath : ContinuousAt (fun z : ℝ × ℝ × ℝ ↦
      (z.1, z.2.1, z.2.2 ^ 2, c₁ * z.2.2)) (q, 1, 0) := by fun_prop
  have hbase : (q, (1 : ℝ), (0 : ℝ) ^ 2, c₁ * 0) = (q, 1, 0, 0) := by simp
  have hstep := (firstRegularStep_continuousAt hq).comp_of_eq hpath hbase
  have he := (regularEntries_continuousAt q).comp_of_eq hpath hbase
  have hs := (regularSpectrum_continuousAt q).comp_of_eq hpath hbase
  have hr := (regularRotatedData_continuousAt q (q / (q + 1))).comp_of_eq hpath hbase
  simp only [Function.comp_def] at hstep he hs hr
  unfold cycleCoefficients regularDenominator
  dsimp only
  fun_prop (disch := simp [regularRotatedData_zero,
    firstRegularStep_zero hq, firstRatio_normalization hq])

/-- Helper for cm-alternating-data: the source assumptions p(ε) → q and
h(ε) → 1 determine both center-displacement coefficients without assuming jets. -/
theorem cycleCoefficients_tendsto {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ)
    (p h : ℝ → ℝ) (hp : Tendsto p (𝓝[>] 0) (𝓝 q))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun ε ↦ cycleCoefficients q c₁ c₂ (p ε) (h ε) ε) (𝓝[>] 0)
      (𝓝 (q * c₁ + c₂, q * c₁ + (q - 1) * c₂)) := by
  have hscale : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hpath := hp.prodMk_nhds (hh.prodMk_nhds hscale)
  have hlimit := (cycleCoefficients_continuousAt hq c₁ c₂).tendsto.comp hpath
  simpa only [Function.comp_def, cycleCoefficients_zero hq] using hlimit

/-- Helper for cm-alternating-data: away from zero scale, the normalized
actual two-step center displacements equal the removable coefficient pair. -/
theorem cycleCenterShift_normalized (q c₁ c₂ p h : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ((cycleCenterShift q c₁ c₂ p h ε 0) / ε ^ 3,
      (cycleCenterShift q c₁ c₂ p h ε 1) / ε ^ 5) =
        cycleCoefficients q c₁ c₂ p h ε := by
  rw [cycleCenterShift_factorization]
  simp [hε]

/-- Helper for cm-alternating-data: general positive limiting shape and the source
ratios determine the cubic and quintic center changes of the exact regular
spectral recurrence. The second coefficient contains the intervening frame
rotation through the term `(q − 1) * c₂`. -/
theorem generalCenterDisplacementLimits {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ)
    (p h : ℝ → ℝ) (hp : Tendsto p (𝓝[>] 0) (𝓝 q))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun ε ↦
      ((cycleCenterShift q c₁ c₂ (p ε) (h ε) ε 0) / ε ^ 3,
        (cycleCenterShift q c₁ c₂ (p ε) (h ε) ε 1) / ε ^ 5))
      (𝓝[>] (0 : ℝ)) (𝓝 (q * c₁ + c₂, q * c₁ + (q - 1) * c₂)) := by
  have hcoeff := cycleCoefficients_tendsto hq c₁ c₂ p h hp hh
  apply hcoeff.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (cycleCenterShift_normalized q c₁ c₂ (p ε) (h ε) hε.ne').symm

/-- Helper for cm-alternating-data: cancellation of both leading actual
center displacements forces shape two and second control minus twice the first. -/
theorem controls_of_centerCancellation {q c₁ c₂ : ℝ} (hq : 0 < q) (hc₁ : c₁ ≠ 0)
    (p h : ℝ → ℝ) (hp : Tendsto p (𝓝[>] 0) (𝓝 q))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 1))
    (hcancel : Tendsto (fun ε ↦
      ((cycleCenterShift q c₁ c₂ (p ε) (h ε) ε 0) / ε ^ 3,
        (cycleCenterShift q c₁ c₂ (p ε) (h ε) ε 1) / ε ^ 5))
      (𝓝[>] (0 : ℝ)) (𝓝 (0, 0))) :
    q = 2 ∧ c₂ = -2 * c₁ := by
  have hlimits := tendsto_nhds_unique
    (generalCenterDisplacementLimits hq c₁ c₂ p h hp hh) hcancel
  exact CenterEndpoints.centerControlCancellation hq hc₁
    (congrArg Prod.fst hlimits) (congrArg Prod.snd hlimits)

/-- Helper for cm-alternating-data: the regular quantities needed to execute
both actual spectral stages are strictly admissible. -/
structure SourceRegularData (q c₁ c₂ p h ε : ℝ) : Prop where
  /-- Helper for cm-alternating-data: the incoming shape is positive. -/
  shape_pos : 0 < p
  /-- Helper for cm-alternating-data: the incoming high eigenvalue is positive. -/
  high_pos : 0 < h
  /-- Helper for cm-alternating-data: the source scale is positive. -/
  scale_pos : 0 < ε
  /-- Helper for cm-alternating-data: the first secant matrix is positive definite. -/
  firstControl : |c₁ * ε| < 1
  /-- Helper for cm-alternating-data: the second secant matrix is positive definite. -/
  secondControl : |c₂ * ε| < 1
  /-- Helper for cm-alternating-data: the removable low eigenvalue factor is positive. -/
  lowFactor : 0 < (regularSpectrum p h (ε ^ 2) (c₁ * ε)).1
  /-- Helper for cm-alternating-data: the updated high eigenvalue is positive. -/
  highFactor : 0 < (regularSpectrum p h (ε ^ 2) (c₁ * ε)).2
  /-- Helper for cm-alternating-data: the first rotated gradient numerator is positive. -/
  firstNumerator : 0 < (regularRotatedData p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).1.1
  /-- Helper for cm-alternating-data: the second rotated gradient numerator is positive. -/
  secondNumerator : 0 < (regularRotatedData p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).1.2
  /-- Helper for cm-alternating-data: the updated eigenvector normalization is positive. -/
  normalizer : 0 < (regularRotatedData p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).2

/-- Helper for cm-alternating-data: the intermediate spectral frame of
admissible source data is a positively oriented orthonormal eigenbasis. -/
theorem SourceRegularData.frame_oriented {q c₁ c₂ p h ε : ℝ}
    (hv : SourceRegularData q c₁ c₂ p h ε) :
    regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1)) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  exact regularFrame_oriented p h (ε ^ 2) (c₁ * ε) (q / (q + 1))
    (regularDenominator_pos (ε ^ 2) (c₁ * ε) hv.firstControl).ne'
    (regularEnergy_pos p (ε ^ 2) (c₁ * ε) hv.shape_pos hv.firstControl).ne'
    hv.highFactor.ne' hv.normalizer.ne'

/-- Helper for cm-alternating-data: all local spectral admissibility conditions
follow from the source limits, rather than becoming extra assumptions. -/
theorem sourceRegularData_eventually {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ)
    (p h : ℝ → ℝ) (hp : Tendsto p (𝓝[>] 0) (𝓝 q))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 1)) :
    ∀ᶠ ε in 𝓝[>] 0, SourceRegularData q c₁ c₂ (p ε) (h ε) ε := by
  have hscale : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hμ₁ : Tendsto (fun ε : ℝ ↦ c₁ * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hscale.const_mul c₁
  have hμ₂ : Tendsto (fun ε : ℝ ↦ c₂ * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hscale.const_mul c₂
  have hradius : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hscale.pow 2
  have hinput := hp.prodMk_nhds (hh.prodMk_nhds (hradius.prodMk_nhds hμ₁))
  have hspectrum : Tendsto (fun ε ↦ regularSpectrum (p ε) (h ε) (ε ^ 2) (c₁ * ε))
      (𝓝[>] 0) (𝓝 (q, 1)) := by
    simpa only [Function.comp_def, regularSpectrum_zero, one_mul] using
      (regularSpectrum_continuousAt q).tendsto.comp hinput
  have hrotated : Tendsto (fun ε ↦
      regularRotatedData (p ε) (h ε) (ε ^ 2) (c₁ * ε) (q / (q + 1)))
      (𝓝[>] 0) (𝓝 ((1, 1), 1)) := by
    simpa only [Function.comp_def, regularRotatedData_zero, firstRatio_normalization hq] using
      (regularRotatedData_continuousAt q (q / (q + 1))).tendsto.comp hinput
  have hcontrol₁ : ∀ᶠ ε in 𝓝[>] 0, |c₁ * ε| < 1 := by
    have habs : Tendsto (fun ε : ℝ ↦ |c₁ * ε|) (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using hμ₁.abs
    exact habs.eventually (gt_mem_nhds zero_lt_one)
  have hcontrol₂ : ∀ᶠ ε in 𝓝[>] 0, |c₂ * ε| < 1 := by
    have habs : Tendsto (fun ε : ℝ ↦ |c₂ * ε|) (𝓝[>] 0) (𝓝 0) := by
      simpa only [abs_zero] using hμ₂.abs
    exact habs.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [hp.eventually (Ioi_mem_nhds hq), hh.eventually (Ioi_mem_nhds zero_lt_one),
    self_mem_nhdsWithin, hcontrol₁, hcontrol₂,
    hspectrum.fst_nhds.eventually (Ioi_mem_nhds hq),
    hspectrum.snd_nhds.eventually (Ioi_mem_nhds zero_lt_one),
    hrotated.fst_nhds.fst_nhds.eventually (Ioi_mem_nhds zero_lt_one),
    hrotated.fst_nhds.snd_nhds.eventually (Ioi_mem_nhds zero_lt_one),
    hrotated.snd_nhds.eventually (Ioi_mem_nhds zero_lt_one)]
    with ε hpε hhε hε hc₁ hc₂ hL hH hX hY hN
  exact ⟨hpε, hhε, hε, hc₁, hc₂, hL, hH, hX, hY, hN⟩

/-- Helper for cm-alternating-data: two genuine DFP steps use the source
controls, and the second takes precisely the first output in its new eigenbasis. -/
structure IsSourceCycle (q c₁ c₂ p h ε G : ℝ)
    (first second : DFP.AbstractSecantStep (Fin 2)) : Prop where
  /-- Helper for cm-alternating-data: the initial inverse Hessian has
  source spectral coordinates. -/
  firstMetric : first.inverseHessian = Matrix.diagonal ![h * p * (ε ^ 2) ^ 2, h]
  /-- Helper for cm-alternating-data: the initial gradient has source spectral coordinates. -/
  firstGradient : first.gradient = G • ![(1 : ℝ), p * ε ^ 2]
  /-- Helper for cm-alternating-data: the first source secant matrix is used. -/
  firstMatrix : first.secantMatrix = !![1, c₁ * ε; c₁ * ε, 1]
  /-- Helper for cm-alternating-data: the first source line ratio is used. -/
  firstRatio : first.tau = q / (q + 1)
  /-- Helper for cm-alternating-data: the second inverse Hessian is the first updated matrix. -/
  secondMetric : second.inverseHessian =
    (regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).transpose *
      first.nextInverseHessian * regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1))
  /-- Helper for cm-alternating-data: the second gradient is the first updated gradient. -/
  secondGradient : second.gradient =
    (regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).transpose *ᵥ first.nextGradient
  /-- Helper for cm-alternating-data: the second source matrix uses the same cycle scale. -/
  secondMatrix : second.secantMatrix = !![1, c₂ * ε; c₂ * ε, 1]
  /-- Helper for cm-alternating-data: the second source line ratio is used. -/
  secondRatio : second.tau = 1 / (q + 1)

/-- Helper for cm-alternating-data: the source limiting hypotheses guarantee
existence of the actual attached pair of positive-definite DFP steps for every
sufficiently small positive scale and every positive initial amplitude. -/
theorem sourceCycle_exists_eventually {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ)
    (p h : ℝ → ℝ) (hp : Tendsto p (𝓝[>] 0) (𝓝 q))
    (hh : Tendsto h (𝓝[>] 0) (𝓝 1)) :
    ∀ᶠ ε in 𝓝[>] 0, ∀ G : ℝ, 0 < G →
      ∃ first second : DFP.AbstractSecantStep (Fin 2),
        IsSourceCycle q c₁ c₂ (p ε) (h ε) ε G first second := by
  have hqone : 0 < q + 1 := by linarith
  have hτ₁ : 0 < q / (q + 1) := div_pos hq hqone
  have hτ₂ : 0 < 1 / (q + 1) := one_div_pos.mpr hqone
  filter_upwards [sourceRegularData_eventually hq c₁ c₂ p h hp hh] with ε hv
  intro G hG
  obtain ⟨first, second, hH₁, hg₁, hA₁, ht₁, hH₂, hg₂, hA₂, ht₂⟩ :=
    CenterDesignRecovery.existsActualSpectralCycle (p ε) (h ε) (ε ^ 2)
      (c₁ * ε) (c₂ * ε) (q / (q + 1)) (1 / (q + 1)) G
      hv.shape_pos hv.high_pos (pow_pos hv.scale_pos 2) hG hτ₁ hτ₂
      hv.firstControl hv.secondControl hv.lowFactor hv.highFactor
      hv.firstNumerator hv.secondNumerator hv.normalizer
  exact ⟨first, second, ⟨hH₁, hg₁, hA₁, ht₁, hH₂, hg₂, hA₂, ht₂⟩⟩

/-- Helper for cm-alternating-data: the actual two-step center displacement,
transported back from the updated eigenbasis, is the regular source expression. -/
theorem IsSourceCycle.centerDisplacement {q c₁ c₂ p h ε G : ℝ}
    {first second : DFP.AbstractSecantStep (Fin 2)}
    (hcycle : IsSourceCycle q c₁ c₂ p h ε G first second)
    (hvalid : SourceRegularData q c₁ c₂ p h ε) :
    (first.displacement - first.gradientChange) +
      regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1)) *ᵥ
        (second.displacement - second.gradientChange) = G • cycleCenterShift q c₁ c₂ p h ε := by
  have hD := (regularDenominator_pos (ε ^ 2) (c₁ * ε) hvalid.firstControl).ne'
  have hE := (regularEnergy_pos p (ε ^ 2) (c₁ * ε)
    hvalid.shape_pos hvalid.firstControl).ne'
  have hX : (regularRotatedData p h (ε ^ 2) (c₁ * ε) first.tau).1.1 ≠ 0 := by
    rw [hcycle.firstRatio]
    exact hvalid.firstNumerator.ne'
  have hY : (regularRotatedData p h (ε ^ 2) (c₁ * ε) first.tau).1.2 ≠ 0 := by
    rw [hcycle.firstRatio]
    exact hvalid.secondNumerator.ne'
  have hN : (regularRotatedData p h (ε ^ 2) (c₁ * ε) first.tau).2 ≠ 0 := by
    rw [hcycle.firstRatio]
    exact hvalid.normalizer.ne'
  have hm := CenterDesignRecovery.spectralMetricRecovery first p h (ε ^ 2) (c₁ * ε) G
    hcycle.firstMetric hcycle.firstGradient hcycle.firstMatrix hD hE
    hvalid.lowFactor.ne' hvalid.highFactor.ne' hX hY hN
  have hg := CenterDesignRecovery.spectralGradientRecovery first p h (ε ^ 2) (c₁ * ε) G
    hcycle.firstMetric hcycle.firstGradient hcycle.firstMatrix
    hvalid.lowFactor.ne' hvalid.highFactor.ne' hX hY
  rw [hcycle.firstRatio] at hm hg
  have hfirst := centerShift_eq_secant first p h (ε ^ 2) (c₁ * ε) G
    hcycle.firstMetric hcycle.firstGradient hcycle.firstMatrix
  have hsecond := centerShift_eq_secant second
    (regularStep p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).2.1
    (regularStep p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).2.2.1
    (ε ^ 2 * (regularStep p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).1)
    (c₂ * ε) (G * (regularStep p h (ε ^ 2) (c₁ * ε) (q / (q + 1))).2.2.2)
    (hcycle.secondMetric.trans hm) (hcycle.secondGradient.trans hg) hcycle.secondMatrix
  rw [hfirst, hsecond, hcycle.firstRatio, hcycle.secondRatio]
  simp only [cycleCenterShift, smul_add, Matrix.mulVec_smul, smul_smul]

/-- Helper for cm-alternating-data: the cubic and quintic normalized actual
center changes, with the second displacement transported to the initial frame. -/
def normalizedActualCenterChange (q c₁ p h ε G : ℝ)
    (first second : DFP.AbstractSecantStep (Fin 2)) : ℝ × ℝ :=
  let change := (first.displacement - first.gradientChange) +
    regularFrame p h (ε ^ 2) (c₁ * ε) (q / (q + 1)) *ᵥ
      (second.displacement - second.gradientChange)
  (change 0 / (G * ε ^ 3), change 1 / (G * ε ^ 5))

/-- Helper for cm-alternating-data: positive amplitude normalization identifies
the actual source center changes with the exact removable coefficient pair. -/
theorem IsSourceCycle.normalizedCenterChange {q c₁ c₂ p h ε G : ℝ}
    {first second : DFP.AbstractSecantStep (Fin 2)}
    (hcycle : IsSourceCycle q c₁ c₂ p h ε G first second)
    (hvalid : SourceRegularData q c₁ c₂ p h ε) (hG : 0 < G) :
    normalizedActualCenterChange q c₁ p h ε G first second =
      cycleCoefficients q c₁ c₂ p h ε := by
  unfold normalizedActualCenterChange
  rw [hcycle.centerDisplacement hvalid, cycleCenterShift_factorization]
  apply Prod.ext
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    field_simp [hG.ne', hvalid.scale_pos.ne']
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [hG.ne', hvalid.scale_pos.ne']

/-- cm-alternating-data: any actual source two-step spectral recurrence with
p(ε) → q > 0 and h(ε) → 1 has center coefficients q*c₁+c₂ and
q*c₁+(q−1)*c₂. All spectral admissibility follows from those limits; the
second step is literally attached to the first updated matrix and gradient. -/
theorem actualSourceCenterDisplacementLimits {q : ℝ} (hq : 0 < q) (c₁ c₂ : ℝ)
    (p h G : ℝ → ℝ) (first second : ℝ → DFP.AbstractSecantStep (Fin 2))
    (hp : Tendsto p (𝓝[>] 0) (𝓝 q)) (hh : Tendsto h (𝓝[>] 0) (𝓝 1))
    (hG : ∀ᶠ ε in 𝓝[>] 0, 0 < G ε)
    (hcycle : ∀ᶠ ε in 𝓝[>] 0,
      IsSourceCycle q c₁ c₂ (p ε) (h ε) ε (G ε) (first ε) (second ε)) :
    Tendsto (fun ε ↦ normalizedActualCenterChange q c₁ (p ε) (h ε) ε (G ε)
      (first ε) (second ε)) (𝓝[>] 0)
        (𝓝 (q * c₁ + c₂, q * c₁ + (q - 1) * c₂)) := by
  apply (cycleCoefficients_tendsto hq c₁ c₂ p h hp hh).congr'
  filter_upwards [sourceRegularData_eventually hq c₁ c₂ p h hp hh, hG, hcycle]
    with ε hvalid hGε hcycleε
  exact (hcycleε.normalizedCenterChange hvalid hGε).symm

/-- Helper for cm-alternating-data: canceling both leading changes of two
attached actual secant steps forces the manuscript's shape and control ratio. -/
theorem actualControls_of_centerCancellation {q c₁ c₂ : ℝ}
    (hq : 0 < q) (hc₁ : c₁ ≠ 0)
    (p h G : ℝ → ℝ) (first second : ℝ → DFP.AbstractSecantStep (Fin 2))
    (hp : Tendsto p (𝓝[>] 0) (𝓝 q)) (hh : Tendsto h (𝓝[>] 0) (𝓝 1))
    (hG : ∀ᶠ ε in 𝓝[>] 0, 0 < G ε)
    (hcycle : ∀ᶠ ε in 𝓝[>] 0,
      IsSourceCycle q c₁ c₂ (p ε) (h ε) ε (G ε) (first ε) (second ε))
    (hcancel : Tendsto (fun ε ↦ normalizedActualCenterChange q c₁ (p ε) (h ε) ε (G ε)
      (first ε) (second ε)) (𝓝[>] 0) (𝓝 (0, 0))) :
    q = 2 ∧ c₂ = -2 * c₁ := by
  have hlimits := tendsto_nhds_unique
    (actualSourceCenterDisplacementLimits hq c₁ c₂ p h G first second hp hh hG hcycle) hcancel
  exact CenterEndpoints.centerControlCancellation hq hc₁
    (congrArg Prod.fst hlimits) (congrArg Prod.snd hlimits)

end DFPWolfe.Latest.CenterDesign
