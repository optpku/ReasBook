module

public import ReasLib.Optimization.DFP.Polar.General.PhysicalRecurrence
public import ReasLib.Optimization.DFP.Polar.General.Geometry
public import ReasLib.Optimization.DFP.Polar.General.FastContraction
public import ReasLib.Optimization.DFP.Polar.General.Realization

/-!
# Radial factor and Wolfe bounds for the general polar trajectory

The quadratic radial factor is canceled exactly using `sinc`. Its coefficient
is analytic in the independent scale, inverse index, and normalized state.
This separates the source power remainder from the tube estimates that the
continuation argument supplies.
-/

public section

noncomputable section

open Set Filter
open scoped Matrix Topology

namespace DFP.Polar.General.RadiusBounds

/-- Helper for eq:polar-W-expansion: multiplication by its argument removes
the removable singularity in `sinc`. This identity is upstream-worthy for
the real trigonometric API. -/
theorem mul_sinc_eq_sin (u : ℝ) : u * Real.sinc u = Real.sin u := by
  by_cases hu : u = 0
  · simp only [hu, Real.sinc_zero, zero_mul, Real.sin_zero]
  · rw [Real.sinc_of_ne_zero hu]
    field_simp

/-- Helper for eq:polar-W-expansion: the exact source radial factor at an
independent angle coefficient, scale, and normalized slope.
This is a reusable scalar interface for the general raw radius ratio. -/
def radiusAtSlope (a t Q : ℝ) : ℝ := Real.cos (a * t) + t * Q * Real.sin (a * t)

/-- Helper for eq:polar-W-expansion: the trigonometric formula for the
general radial factor. This is its reusable scalar construction interface. -/
theorem radiusAtSlope_def (a t Q : ℝ) :
    radiusAtSlope a t Q = Real.cos (a * t) + t * Q * Real.sin (a * t) := by
  rfl

/-- Helper for eq:polar-W-expansion: the exact canceled quadratic coefficient
of the general radial factor. It is regular at zero scale.
This is a reusable analytic scalar observable. -/
def radiusCoefficient (a t Q : ℝ) : ℝ :=
  a * Q * Real.sinc (a * t) - (a ^ 2 / 2) * Real.sinc (a * t / 2) ^ 2

/-- Helper for eq:polar-W-expansion: the sinc formula for the canceled
quadratic radial coefficient. This is its reusable construction interface. -/
theorem radiusCoefficient_def (a t Q : ℝ) :
    radiusCoefficient a t Q =
      a * Q * Real.sinc (a * t) - (a ^ 2 / 2) * Real.sinc (a * t / 2) ^ 2 := by
  rfl

/-- Helper for eq:polar-W-expansion: the canceled coefficient at zero scale
is the source principal coefficient `a Q - a²/2`.
This is a reusable zero-scale scalar interface. -/
theorem radiusCoefficient_zero (a Q : ℝ) : radiusCoefficient a 0 Q = a * Q - a ^ 2 / 2 := by
  simp only [radiusCoefficient_def, mul_zero, zero_div, Real.sinc_zero, mul_one, one_pow]

/-- Helper for eq:polar-W-expansion: the raw radial factor equals one plus
the scale squared times its exact canceled analytic coefficient.
This identity is valid even at zero scale and is reusable for every phase. -/
theorem radiusAtSlope_eq_one_add_sq (a t Q : ℝ) :
    radiusAtSlope a t Q = 1 + t ^ 2 * radiusCoefficient a t Q := by
  have hcos : Real.cos (a * t) = 1 - 2 * Real.sin (a * t / 2) ^ 2 := by
    have hargument : 2 * (a * t / 2) = a * t := by
      ring
    have h := Real.cos_two_mul_eq_one_sub (a * t / 2)
    rwa [hargument] at h
  have hsin := mul_sinc_eq_sin (a * t)
  have hhalf := mul_sinc_eq_sin (a * t / 2)
  rw [radiusAtSlope_def, radiusCoefficient_def, hcos, ← hsin, ← hhalf]
  ring

/-- Helper for eq:polar-W-expansion: the canceled radial coefficient is
analytic along independent analytic coefficient, scale, and slope paths when
the scale vanishes at the base. This is a reusable analytic interface. -/
theorem radiusCoefficientAlong_analyticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a t Q : E → ℝ} {z : E} (ha : AnalyticAt ℝ a z) (ht : AnalyticAt ℝ t z)
    (hQ : AnalyticAt ℝ Q z) (htzero : t z = 0) :
    AnalyticAt ℝ (fun y ↦ radiusCoefficient (a y) (t y) (Q y)) z := by
  have hangle := ha.mul ht
  have hanglezero : a z * t z = 0 := by
    rw [htzero, mul_zero]
  have hhalf : AnalyticAt ℝ (fun y ↦ a y * t y / 2) z := hangle.div_const
  have hhalfzero : a z * t z / 2 = 0 := by
    rw [hanglezero, zero_div]
  have hsinc := Normalized.analyticAt_sinc_zero.comp_of_eq hangle hanglezero
  have hsincHalf := Normalized.analyticAt_sinc_zero.comp_of_eq hhalf hhalfzero
  simp only [radiusCoefficient_def]
  exact ((ha.mul hQ).mul hsinc).sub (((ha.pow 2).div_const).mul (hsincHalf.pow 2))

/-- Helper for eq:polar-slope-estimates: the general normalized slope is
the same canonical coordinate quotient as the existing polar slope.
This file-local adapter reuses the established slope API. -/
theorem slope_eq_original (x : ℝ × ℝ × ℝ) :
    Normalized.slope x = DFP.Polar.Normalized.slope x := by
  rw [Normalized.slope_def, DFP.Polar.Normalized.slope_def]

/-- Helper for eq:polar-slope-estimates: analytic state paths with nonzero
off-diagonal entry have analytic normalized slopes.
This is a reusable adapter to the existing scalar slope theorem. -/
theorem slopeAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : AnalyticAt ℝ X z) (hC : (X z).2.1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ Normalized.slope (X y)) z := by
  simpa only [slope_eq_original] using
    DFP.Polar.RadiusExpansions.slopeAlong_analyticAt hX hC

/-- Helper for eq:polar-slope-estimates: the even source base slope has the
exact value `1 + δE` fixed by the two-cycle normalization.
This is a reusable scalar interface for the selected general base. -/
theorem slope_initialState (p : Parameters) :
    Normalized.slope p.initialState = 1 + p.deltaEven := by
  have hell : 0 < p.ell := zero_lt_one.trans p.base.one_lt_ell
  rw [slope_eq_original, p.initialState_def,
    slope_cycleState p.gammaStar_pos.ne' hell.ne', p.gammaStar_def, baseGamma_def,
    p.deltaEven_def, baseDeltaEven_def]
  field_simp [hell.ne', p.base.z_pos.ne']
  ring

/-- Helper for eq:polar-slope-estimates: the odd source base slope has the
exact value `ell + δO` fixed by the two-cycle normalization.
This is a reusable scalar interface for the selected general base. -/
theorem slope_oddReference_base (p : Parameters) :
    Normalized.slope (p.oddReference p.gammaStar) = p.ell + p.deltaOdd := by
  rw [slope_eq_original, p.oddReference_gammaStar,
    slope_cycleState p.gammaStar_pos.ne' one_ne_zero, p.gammaStar_def, baseGamma_def,
    p.deltaOdd_def, baseDeltaOdd_def]
  field_simp [p.base.z_pos.ne', (zero_lt_one.trans p.base.one_lt_ell).ne']
  ring

/-- Helper for eq:polar-slope-estimates: the analytic angle coefficient for
either source phase. This reusable observable retains the inverse index as
an independent variable. -/
def phaseAngle (p : Parameters) (i : Fin 2) (v : ℝ) : ℝ :=
  ![p.evenAngleFactor v, p.oddAngleFactor v] i

/-- Helper for eq:polar-slope-estimates: the even phase angle coefficient is
the original even analytic coefficient. This is its reusable projection API. -/
theorem phaseAngle_zero (p : Parameters) (v : ℝ) : phaseAngle p 0 v = p.evenAngleFactor v := by
  rfl

/-- Helper for eq:polar-slope-estimates: the odd phase angle coefficient is
the original odd analytic coefficient. This is its reusable projection API. -/
theorem phaseAngle_one (p : Parameters) (v : ℝ) : phaseAngle p 1 v = p.oddAngleFactor v := by
  rfl

/-- Helper for eq:polar-slope-estimates: the actual input state at each phase
of a canceled cycle. The odd input is computed by the first stage and retains
its feedback from the original boundary state.
This is a reusable interface for both source phases. -/
def phaseInput (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ![x, Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
    0 t v x x] i

/-- Helper for eq:polar-slope-estimates: the even cycle input is the original
boundary state. This is the reusable even-phase state projection. -/
theorem phaseInput_zero (p : Parameters) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseInput p 0 t v x = x := by
  rfl

/-- Helper for eq:polar-slope-estimates: the odd input is the actual first
normalized stage. This is the reusable odd-phase state projection. -/
theorem phaseInput_one (p : Parameters) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseInput p 1 t v x = Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor
      p.feedbackPotential 0 t v x x := by
  rfl

/-- Helper for eq:polar-slope-estimates: the original source normalized slope
at each actual phase input. This is a reusable analytic observable. -/
def phaseSlope (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Normalized.slope (phaseInput p i t v x)

/-- Helper for eq:polar-slope-estimates: the quotient at the actual phase
input defines the source slope observable. This is its reusable interface. -/
theorem phaseSlope_def (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseSlope p i t v x = Normalized.slope (phaseInput p i t v x) := by
  rfl

/-- Helper for eq:polar-W-expansion: the exact raw radius ratio for either
source phase, expressed at its actual normalized input.
This is a reusable canceled scalar observable. -/
def phaseRadius (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  radiusAtSlope (phaseAngle p i v) t (phaseSlope p i t v x)

/-- Helper for eq:polar-W-expansion: the source phase radius uses its actual
angle coefficient and slope. This is its reusable scalar interface. -/
theorem phaseRadius_def (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseRadius p i t v x = radiusAtSlope (phaseAngle p i v) t (phaseSlope p i t v x) := by
  rfl

/-- Helper for eq:polar-W-expansion: the analytic quadratic coefficient of
the actual source phase radius. This is a reusable canceled observable. -/
def phaseCoefficient (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  radiusCoefficient (phaseAngle p i v) t (phaseSlope p i t v x)

/-- Helper for eq:polar-W-expansion: the phase coefficient is the scalar
canceled coefficient at the actual angle and slope. This is its reusable API. -/
theorem phaseCoefficient_def (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseCoefficient p i t v x = radiusCoefficient (phaseAngle p i v) t (phaseSlope p i t v x) := by
  rfl

/-- Helper for eq:polar-W-expansion: every actual phase radius has the exact
canceled form `1 + t² D`. This is reusable at zero and positive scales. -/
theorem phaseRadius_eq_one_add_sq (p : Parameters) (i : Fin 2) (t v : ℝ)
    (x : ℝ × ℝ × ℝ) : phaseRadius p i t v x = 1 + t ^ 2 * phaseCoefficient p i t v x := by
  rw [phaseRadius_def, phaseCoefficient_def, radiusAtSlope_eq_one_add_sq]

/-- Helper for eq:polar-W-expansion: the concrete recursively generated
source radius ratio equals the phase observable on the same actual trajectory.
No radial recurrence or asymptotic estimate is assumed in this bridge. -/
theorem radiusRatio_eq_phaseRadius (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    p.radiusRatio (2 * j + (i : ℕ)) =
      phaseRadius p i (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [Fin.val_zero, Nat.add_zero, phaseRadius_def, phaseAngle_zero,
      phaseSlope_def, phaseInput_zero, radiusAtSlope_def, Normalized.stageAngle_def] using
      p.radiusRatio_even_eq_normalized hβ hstart j
  · simpa only [Fin.val_one, phaseRadius_def, phaseAngle_one, phaseSlope_def,
      phaseInput_one, ← p.normalizedOddState_apply, radiusAtSlope_def,
      Normalized.stageAngle_def] using p.radiusRatio_odd_eq_normalized hβ hstart j

/-- Helper for eq:polar-slope-estimates: the selected source base slopes are
`1 + δE` and `ell + δO`. This is a reusable fixed-before-index scalar datum. -/
def referenceSlope (p : Parameters) : Fin 2 → ℝ :=
  ![1 + p.deltaEven, p.ell + p.deltaOdd]

/-- Helper for eq:polar-slope-estimates: the even source base slope is
`1 + δE`. This is its reusable projection API. -/
theorem referenceSlope_zero (p : Parameters) : referenceSlope p 0 = 1 + p.deltaEven := by
  rfl

/-- Helper for eq:polar-slope-estimates: the odd source base slope is
`ell + δO`. This is its reusable projection API. -/
theorem referenceSlope_one (p : Parameters) : referenceSlope p 1 = p.ell + p.deltaOdd := by
  rfl

/-- Helper for eq:polar-slope-estimates: the computed odd input at the
selected equilibrium is precisely the source odd reference state.
This is a reusable zero-parameter phase interface. -/
theorem phaseInput_one_at_base (p : Parameters) (hβ : 0 < p.beta) :
    phaseInput p 1 0 0 p.initialState = p.oddReference p.gammaStar := by
  rw [phaseInput_one, Normalized.cycleStage_even, Normalized.feedback_zero,
    Normalized.stage_zero, p.evenAngleFactor_zero hβ]
  have hcycle := p.referenceCycle_eventually.self_of_nhds
  simpa only [p.evenReference_gammaStar] using hcycle.1

/-- Helper for eq:polar-slope-estimates: both actual phase slopes recover
the source's selected base slopes at zero independent parameters.
This is a reusable normalization identity. -/
theorem phaseSlope_at_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    phaseSlope p i 0 0 p.initialState = referenceSlope p i := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseSlope_def, phaseInput_zero, referenceSlope_zero, slope_initialState]
  · rw [phaseSlope_def, phaseInput_one_at_base p hβ, referenceSlope_one,
      slope_oddReference_base]

/-- Helper for eq:polar-W-expansion: the source principal radial coefficient
is `δ (Q - δ/2)` for either selected phase.
This is a reusable fixed-before-index scalar datum. -/
def radiusLimitCoefficient (p : Parameters) (i : Fin 2) : ℝ :=
  phaseAngle p i 0 * referenceSlope p i - (phaseAngle p i 0) ^ 2 / 2

/-- Helper for eq:polar-W-expansion: the explicit source formula for the
limiting quadratic radial coefficient. This is its reusable scalar API. -/
theorem radiusLimitCoefficient_def (p : Parameters) (i : Fin 2) :
    radiusLimitCoefficient p i =
      phaseAngle p i 0 * referenceSlope p i - (phaseAngle p i 0) ^ 2 / 2 := by
  rfl

/-- Helper for eq:polar-W-expansion: the analytic phase coefficient at the
selected equilibrium is the actual source principal radial coefficient.
This is a reusable zero-parameter identity. -/
theorem phaseCoefficient_at_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    phaseCoefficient p i 0 0 p.initialState = radiusLimitCoefficient p i := by
  rw [phaseCoefficient_def, radiusCoefficient_zero, phaseSlope_at_base p hβ,
    radiusLimitCoefficient_def]

/-- Helper for eq:polar-slope-estimates: the selected analytic angle
coefficient of either phase is positive at zero inverse index.
This is reusable positivity for the general two-cycle observables. -/
theorem phaseAngle_base_pos (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    0 < phaseAngle p i 0 := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseAngle_zero, p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos
  · rw [phaseAngle_one, p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos

/-- Helper for eq:polar-slope-estimates: each source base slope is strictly
larger than its phase angle coefficient. This is reusable scalar positivity
for the radial expansion and both Wolfe ratios. -/
theorem referenceSlope_gt_angle (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    phaseAngle p i 0 < referenceSlope p i := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseAngle_zero, p.evenAngleFactor_zero hβ, referenceSlope_zero]
    linarith
  · rw [phaseAngle_one, p.oddAngleFactor_zero hβ, referenceSlope_one]
    linarith [p.base.one_lt_ell]

/-- Helper for eq:polar-W-expansion: both source principal radial
coefficients are strictly positive for every selected strict Wolfe base.
This is reusable positivity independent of the starting index. -/
theorem radiusLimitCoefficient_pos (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    0 < radiusLimitCoefficient p i := by
  have ha := phaseAngle_base_pos p hβ i
  have hQ := referenceSlope_gt_angle p hβ i
  have hproduct := mul_pos ha (sub_pos.mpr hQ)
  rw [radiusLimitCoefficient_def]
  nlinarith [sq_pos_of_pos ha]

/-- Helper for eq:polar-W-expansion: both source angle-coefficient paths
are analytic at zero inverse index. This is a reusable phase observable API. -/
theorem phaseAngle_analyticAt (p : Parameters) (i : Fin 2) :
    AnalyticAt ℝ (phaseAngle p i) 0 := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [funext (phaseAngle_zero p)] using p.evenAngleFactor_analyticAt
  · simpa only [funext (phaseAngle_one p)] using p.oddAngleFactor_analyticAt

/-- Helper for eq:polar-slope-estimates: the actual input of each phase is
jointly analytic in the independent scale, inverse index, and boundary state
at the selected equilibrium. This is a reusable actual-cycle interface. -/
theorem phaseInput_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseInput p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simp only [phaseInput_zero]
    exact analyticAt_snd
  · have hγ : p.initialState.1 = p.gammaStar := by
      simp only [p.initialState_def, cycleState_apply]
    have hφ : AnalyticAt ℝ p.feedbackPotential p.initialState.1 := by
      rw [hγ]
      exact p.feedbackPotential_analyticAt hβ
    have ha : p.evenAngleFactor 0 ≠ 0 := by
      rw [p.evenAngleFactor_zero hβ]
      exact p.deltaEven_pos.ne'
    simpa only [phaseInput_one] using Normalized.evenStage_analyticAt
      p.evenAngleFactor p.oddAngleFactor p.feedbackPotential p.initialState
      p.evenAngleFactor_analyticAt hφ ha p.initial_reference_positive.1.ne'

/-- Helper for eq:polar-slope-estimates: each actual phase input has a
positive off-diagonal entry at the selected zero-parameter equilibrium.
This is reusable positivity for the slope analytic interface. -/
theorem phaseInput_offDiagonal_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    0 < (phaseInput p i 0 0 p.initialState).2.1 := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [phaseInput_zero] using p.initial_reference_positive.1
  · simpa only [phaseInput_one_at_base p hβ] using p.initial_reference_positive.2

/-- Helper for eq:polar-slope-estimates: actual phase slopes are jointly
analytic in the two independent small parameters and normalized state.
This is a reusable analytic source-observable theorem. -/
theorem phaseSlope_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseSlope p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  simp only [phaseSlope_def]
  exact slopeAlong_analyticAt (phaseInput_joint_analyticAt p hβ i)
    (phaseInput_offDiagonal_base p hβ i).ne'

/-- Helper for eq:polar-W-expansion: actual canceled radial coefficients
are jointly analytic in the two independent small parameters and normalized
state. This is a reusable source-observable theorem that never assigns an
analytic extension to a noninteger power of the scale. -/
theorem phaseCoefficient_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseCoefficient p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have ht : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1) ((0, 0), p.initialState) :=
    analyticAt_fst.comp analyticAt_fst
  have hv : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2) ((0, 0), p.initialState) :=
    analyticAt_snd.comp analyticAt_fst
  have ha := (phaseAngle_analyticAt p i).comp_of_eq hv rfl
  simp only [phaseCoefficient_def]
  exact radiusCoefficientAlong_analyticAt ha ht (phaseSlope_joint_analyticAt p hβ i) rfl

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: a common
ordinary-state bound of order `t^(1-β)` yields uniform bounds of the same
order for both actual phase slopes and canceled radial coefficients.
The constants precede all choices of scale and inverse index. -/
theorem localSlopeAndCoefficientBounds (p : Parameters) (hβ : 0 < p.beta)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ v : ℝ, |v| ≤ t ^ (1 - p.beta) → ∀ x : ℝ × ℝ × ℝ,
        ‖x - p.initialState‖ ≤ B * t ^ (1 - p.beta) → ∀ i : Fin 2,
        |phaseSlope p i t v x - referenceSlope p i| ≤ C * t ^ (1 - p.beta) ∧
        |phaseCoefficient p i t v x - radiusLimitCoefficient p i| ≤
          C * t ^ (1 - p.beta) := by
  let f : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) → Fin 2 → ℝ × ℝ :=
    fun z i ↦ (phaseSlope p i z.1.1 z.1.2 z.2, phaseCoefficient p i z.1.1 z.1.2 z.2)
  have hf : AnalyticAt ℝ f ((0, 0), p.initialState) := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (phaseSlope_joint_analyticAt p hβ i).prod
      (phaseCoefficient_joint_analyticAt p hβ i)
  obtain ⟨K, s, hs, hLip⟩ := hf.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hbase : ((0, 0), p.initialState) ∈ s := mem_of_mem_nhds hs
  have hBOne : 0 < B + 1 := by
    linarith
  have hKOne : 0 < (K : ℝ) + 1 := by
    positivity
  refine ⟨((K : ℝ) + 1) * (B + 1), mul_pos hKOne hBOne,
    ε / (B + 1), div_pos hε hBOne, ?_⟩
  intro t ht htone htδ v hv x hx i
  have hslow : 0 ≤ t ^ (1 - p.beta) := Real.rpow_nonneg ht.le _
  have hslowExponent : 1 - p.beta ≤ 1 := by
    linarith
  have htSlow := Real.self_le_rpow_of_le_one ht.le htone hslowExponent
  have hcommon : t ^ (1 - p.beta) ≤ (B + 1) * t ^ (1 - p.beta) := by
    nlinarith [mul_nonneg hB hslow]
  have hstate : B * t ^ (1 - p.beta) ≤ (B + 1) * t ^ (1 - p.beta) := by
    nlinarith
  have hdist : dist ((t, v), x) ((0, 0), p.initialState) ≤
      (B + 1) * t ^ (1 - p.beta) := by
    rw [Prod.dist_eq, Prod.dist_eq]
    apply max_le
    · apply max_le
      · rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.le]
        exact htSlow.trans hcommon
      · rw [Real.dist_eq, sub_zero]
        exact hv.trans hcommon
    · rw [dist_eq_norm]
      exact hx.trans hstate
  have hsmall : (B + 1) * t ^ (1 - p.beta) < ε := by
    nlinarith [(lt_div_iff₀ hBOne).mp htδ]
  have hin : ((t, v), x) ∈ s := hball (Metric.mem_ball.mpr (hdist.trans_lt hsmall))
  have hfull := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hin hbase
  have hnorm : ‖((t, v), x) - ((0, 0), p.initialState)‖ ≤
      (B + 1) * t ^ (1 - p.beta) := by
    simpa only [dist_eq_norm] using hdist
  have htotal : ‖f ((t, v), x) - f ((0, 0), p.initialState)‖ ≤
      (((K : ℝ) + 1) * (B + 1)) * t ^ (1 - p.beta) := by
    apply hfull.trans
    have hfirst := mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
    nlinarith [mul_nonneg hBOne.le hslow]
  have hcoordinate :=
    (norm_le_pi_norm (f ((t, v), x) - f ((0, 0), p.initialState)) i).trans htotal
  constructor
  · have h := (norm_fst_le ((f ((t, v), x) - f ((0, 0), p.initialState)) i)).trans hcoordinate
    simpa only [f, Pi.sub_apply, Prod.fst_sub, phaseSlope_at_base p hβ,
      Real.norm_eq_abs] using h
  · have h := (norm_snd_le ((f ((t, v), x) - f ((0, 0), p.initialState)) i)).trans hcoordinate
    simpa only [f, Pi.sub_apply, Prod.snd_sub, phaseCoefficient_at_base p hβ,
      Real.norm_eq_abs] using h

/-- Helper for eq:polar-W-expansion: ordinary-state deviations of the source
slow order imply the exact general radial factor expansion with error
`C t^(3-β)` at both actual phase inputs.
The bound is uniform in the independent inverse-index parameter. -/
theorem localRadiusBoundsOfStateBound (p : Parameters) (hβ : 0 < p.beta)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ v : ℝ, |v| ≤ t ^ (1 - p.beta) → ∀ x : ℝ × ℝ × ℝ,
        ‖x - p.initialState‖ ≤ B * t ^ (1 - p.beta) → ∀ i : Fin 2,
        |phaseSlope p i t v x - referenceSlope p i| ≤ C * t ^ (1 - p.beta) ∧
        |phaseRadius p i t v x - 1 - radiusLimitCoefficient p i * t ^ 2| ≤
          C * t ^ (3 - p.beta) := by
  obtain ⟨C, hC, δ, hδ, hbound⟩ := localSlopeAndCoefficientBounds p hβ hB
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro t ht htone htδ v hv x hx i
  have h := hbound t ht htone htδ v hv x hx i
  have hexponent : (2 : ℝ) + (1 - p.beta) = 3 - p.beta := by
    ring
  have hpower : t ^ 2 * t ^ (1 - p.beta) = t ^ (3 - p.beta) := by
    rw [← Real.rpow_two, ← Real.rpow_add ht, hexponent]
  have hidentity : phaseRadius p i t v x - 1 - radiusLimitCoefficient p i * t ^ 2 =
      t ^ 2 * (phaseCoefficient p i t v x - radiusLimitCoefficient p i) := by
    rw [phaseRadius_eq_one_add_sq]
    ring
  refine ⟨h.1, ?_⟩
  calc
    |phaseRadius p i t v x - 1 - radiusLimitCoefficient p i * t ^ 2| =
        t ^ 2 * |phaseCoefficient p i t v x - radiusLimitCoefficient p i| := by
      rw [hidentity, abs_mul, abs_of_nonneg (sq_nonneg t)]
    _ ≤ t ^ 2 * (C * t ^ (1 - p.beta)) :=
      mul_le_mul_of_nonneg_left h.2 (sq_nonneg t)
    _ = C * t ^ (3 - p.beta) := by
      rw [← hpower]
      ring

/-- Helper for eq:polar-slope-estimates: when first coordinates agree, the
full coordinate-triple difference is bounded by the supremum norm of its two
fast coordinates. This is a reusable canonical coordinate-norm estimate. -/
theorem norm_state_sub_of_fst_eq {x y : ℝ × ℝ × ℝ} (hfst : x.1 = y.1) :
    ‖x - y‖ ≤ ‖DFP.Polar.FastContraction.fastCoordinates x -
      DFP.Polar.FastContraction.fastCoordinates y‖ := by
  have hfirst := norm_le_pi_norm (DFP.Polar.FastContraction.fastCoordinates x -
    DFP.Polar.FastContraction.fastCoordinates y) (0 : Fin 2)
  have hsecond := norm_le_pi_norm (DFP.Polar.FastContraction.fastCoordinates x -
    DFP.Polar.FastContraction.fastCoordinates y) (1 : Fin 2)
  simp only [DFP.Polar.FastContraction.fastCoordinates_apply, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hfirst hsecond
  have hstate : ‖x - y‖ = max ‖x.1 - y.1‖
      (max ‖x.2.1 - y.2.1‖ ‖x.2.2 - y.2.2‖) := rfl
  rw [hstate, hfst, sub_self, norm_zero]
  simpa only [DFP.Polar.FastContraction.fastCoordinates_apply] using
    max_le (norm_nonneg _) (max_le hfirst hsecond)

/-- Helper for eq:polar-slope-estimates: the full deviation from the genuine
reference curve is bounded by the fixed source Lyapunov norm of its fast
coordinates. This reusable bridge uses the canonical coordinate supremum
norm and the proved Lyapunov norm comparison. -/
theorem norm_state_sub_reference_le_fixedNorm (p : Parameters) (x : ℝ × ℝ × ℝ) :
    ‖x - p.evenReference x.1‖ ≤ FastContraction.fixedNorm p.ell p.z
      (DFP.Polar.FastContraction.fastCoordinates x - FastContraction.evenFastReference p x.1) := by
  rw [FastContraction.evenFastReference_apply]
  exact (norm_state_sub_of_fst_eq (p.evenReference_fst x.1).symm).trans
    (FastContraction.norm_le_fixedNorm p.base.stable _)

/-- Helper for eq:polar-slope-estimates: the source slow tube
`|γ-γ*| ≤ M t^(1-β)` and fast Lyapunov tube `‖u‖ ≤ N t^(1+β)` imply an
ordinary-state bound `B t^(1-β)` around the selected equilibrium.
The constants precede the scale, inverse index, and starting-index choice. -/
theorem stateBoundOfTube (p : Parameters) (hβ : 0 < p.beta) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ B > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ x : ℝ × ℝ × ℝ, |x.1 - p.gammaStar| ≤ M * t ^ (1 - p.beta) →
        FastContraction.fixedNorm p.ell p.z
          (DFP.Polar.FastContraction.fastCoordinates x -
            FastContraction.evenFastReference p x.1) ≤ N * t ^ (1 + p.beta) →
        ‖x - p.initialState‖ ≤ B * t ^ (1 - p.beta) := by
  obtain ⟨K, s, hs, hLip⟩ := p.evenReference_analyticAt.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hbase : p.gammaStar ∈ s := mem_of_mem_nhds hs
  have hMOne : 0 < M + 1 := by
    linarith
  have hB : 0 < N + (K : ℝ) * M + 1 := by
    positivity
  refine ⟨N + (K : ℝ) * M + 1, hB, ε / (M + 1), div_pos hε hMOne, ?_⟩
  intro t ht htone htδ x hslow hfast
  have hslowNonneg : 0 ≤ t ^ (1 - p.beta) := Real.rpow_nonneg ht.le _
  have hsmall : (M + 1) * t ^ (1 - p.beta) < ε := by
    nlinarith [(lt_div_iff₀ hMOne).mp htδ]
  have hin : x.1 ∈ s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hbound : M * t ^ (1 - p.beta) ≤ (M + 1) * t ^ (1 - p.beta) := by
      nlinarith
    exact hslow.trans_lt (hbound.trans_lt hsmall)
  have hcurve := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hin hbase
  rw [p.evenReference_gammaStar] at hcurve
  have hslowNorm : ‖x.1 - p.gammaStar‖ ≤ M * t ^ (1 - p.beta) := by
    simpa only [Real.norm_eq_abs] using hslow
  have hcurveBound : ‖p.evenReference x.1 - p.initialState‖ ≤
      ((K : ℝ) * M) * t ^ (1 - p.beta) := by
    apply hcurve.trans
    have h := mul_le_mul_of_nonneg_left hslowNorm K.coe_nonneg
    simpa only [mul_assoc] using h
  have hexponents : 1 - p.beta ≤ 1 + p.beta := by
    linarith
  have hfastPower := Real.rpow_le_rpow_of_exponent_ge ht htone hexponents
  have hfastBound : ‖x - p.evenReference x.1‖ ≤ N * t ^ (1 - p.beta) :=
    ((norm_state_sub_reference_le_fixedNorm p x).trans hfast).trans
      (mul_le_mul_of_nonneg_left hfastPower hN)
  have htriangle := norm_sub_le_norm_sub_add_norm_sub x (p.evenReference x.1) p.initialState
  nlinarith

/-- Helper for eq:polar-slope-estimates and eq:polar-W-expansion: the source
slow and fast tube bounds imply both phase slope errors `O(t^(1-β))` and
radial factor errors `O(t^(3-β))` on the actual two-stage input construction.
This is a reusable analytic consequence of the continuation tube. -/
theorem localSlopeAndRadiusBoundsOfTube (p : Parameters) (hβ : 0 < p.beta)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ v : ℝ, |v| ≤ t ^ (1 - p.beta) → ∀ x : ℝ × ℝ × ℝ,
        |x.1 - p.gammaStar| ≤ M * t ^ (1 - p.beta) →
        FastContraction.fixedNorm p.ell p.z
          (DFP.Polar.FastContraction.fastCoordinates x -
            FastContraction.evenFastReference p x.1) ≤ N * t ^ (1 + p.beta) →
        ∀ i : Fin 2,
        |phaseSlope p i t v x - referenceSlope p i| ≤ C * t ^ (1 - p.beta) ∧
        |phaseRadius p i t v x - 1 - radiusLimitCoefficient p i * t ^ 2| ≤
          C * t ^ (3 - p.beta) := by
  obtain ⟨B, hB, δs, hδs, hstate⟩ := stateBoundOfTube p hβ hM hN
  obtain ⟨C, hC, δr, hδr, hradius⟩ := localRadiusBoundsOfStateBound p hβ hB.le
  refine ⟨C, hC, min δs δr, lt_min hδs hδr, ?_⟩
  intro t ht htone htδ v hv x hslow hfast i
  have hts : t ^ (1 - p.beta) < δs := htδ.trans_le (min_le_left _ _)
  have htr : t ^ (1 - p.beta) < δr := htδ.trans_le (min_le_right _ _)
  exact hradius t ht htone htr v hv x (hstate t ht htone hts x hslow hfast) i

/-- Helper for eq:polar-W-expansion: increasing the starting index leaves
each analytic angle-coefficient path unchanged. This is a reusable uniformity
interface for the source observables. -/
theorem phaseAngle_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2) (v : ℝ) :
    phaseAngle (p.withStartIndex j0) i v = phaseAngle p i v := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseAngle_zero, phaseAngle_zero, (p.withStartIndex_analyticData j0).1]
  · rw [phaseAngle_one, phaseAngle_one, (p.withStartIndex_analyticData j0).2.1]

/-- Helper for eq:polar-W-expansion: increasing the starting index leaves
the actual phase-input map unchanged. This is a reusable uniformity interface
for both normalized source stages. -/
theorem phaseInput_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseInput (p.withStartIndex j0) i t v x = phaseInput p i t v x := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseInput_zero, phaseInput_zero]
  · rw [phaseInput_one, phaseInput_one, (p.withStartIndex_analyticData j0).1,
      (p.withStartIndex_analyticData j0).2.1, (p.withStartIndex_analyticData j0).2.2]

/-- Helper for eq:polar-W-expansion: the exact phase radius is unchanged
by increasing the starting index. This reusable identity makes its analytic
constants uniform before the final source index is selected. -/
theorem phaseRadius_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseRadius (p.withStartIndex j0) i t v x = phaseRadius p i t v x := by
  rw [phaseRadius_def, phaseRadius_def, phaseAngle_withStartIndex,
    phaseSlope_def, phaseSlope_def, phaseInput_withStartIndex]

/-- Helper for eq:polar-W-expansion: actual recursively generated normalized
trajectories in the source slow and fast tube satisfy the radial factor
expansion at every phase and every cycle. The error constant and scale
threshold are chosen before the starting index, and the factors are the raw
radius ratios of that same trajectory. -/
theorem radiusBoundsOfActualTube (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∃ δ > 0, ∀ j0 : ℕ, 0 < j0 → scale p.beta j0 0 ^ (1 - p.beta) < δ →
      (∀ j, |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta)) →
      (∀ j, FastContraction.fixedNorm p.ell p.z
        (DFP.Polar.FastContraction.fastCoordinates ((p.withStartIndex j0).normalizedEvenState j) -
          FastContraction.evenFastReference p ((p.withStartIndex j0).normalizedEvenState j).1) ≤
        N * scale p.beta j0 j ^ (1 + p.beta)) →
      ∀ j : ℕ, ∀ i : Fin 2,
        |(p.withStartIndex j0).radiusRatio (2 * j + (i : ℕ)) - 1 -
          radiusLimitCoefficient p i * scale p.beta j0 j ^ 2| ≤
            C * scale p.beta j0 j ^ (3 - p.beta) := by
  obtain ⟨C, hC, δ, hδ, hbound⟩ := localSlopeAndRadiusBoundsOfTube p hβ hM hN
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro j0 hstart hsmall hslow hfast j i
  let q := p.withStartIndex j0
  have hqβ : 0 < q.beta := by
    simpa only [q, Parameters.withStartIndex_beta] using hβ
  have hqstart : 0 < q.startIndex := by
    simpa only [q, Parameters.withStartIndex_startIndex] using hstart
  have hqscale : q.scale j = scale p.beta j0 j := by
    simp only [q, Parameters.scale_def, Parameters.withStartIndex_beta,
      Parameters.withStartIndex_startIndex]
  have hqinv : q.inverseIndex j = scale p.beta j0 j ^ (1 + p.beta) := by
    rw [q.inverseIndex_def]
    simpa only [q, Parameters.withStartIndex_startIndex] using
      (scale_rpow_one_add hβ j0 j).symm
  have ht := scale_pos p.beta hstart j
  have htone := scale_le_one hβ hstart j
  have hslowPower := Real.rpow_le_rpow ht.le
    (scale_antitone hβ hstart (Nat.zero_le j)) (sub_pos.mpr hβone).le
  have hlocal : scale p.beta j0 j ^ (1 - p.beta) < δ := hslowPower.trans_lt hsmall
  have hexponents : 1 - p.beta ≤ 1 + p.beta := by
    linarith
  have hv : |q.inverseIndex j| ≤ scale p.beta j0 j ^ (1 - p.beta) := by
    rw [hqinv, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge ht htone hexponents
  have h := (hbound (scale p.beta j0 j) ht htone hlocal (q.inverseIndex j) hv
    (q.normalizedEvenState j) (hslow j) (hfast j) i).2
  have hphase := phaseRadius_withStartIndex p j0 i (q.scale j) (q.inverseIndex j)
    (q.normalizedEvenState j)
  rw [radiusRatio_eq_phaseRadius q hqβ hqstart j i, hphase, hqscale]
  exact h

/-- Helper for eq:polar-W-expansion and eq:polar-radii: the actual source
radius factors are strictly above one and have two-sided quadratic defects
once the common slow-scale threshold is small enough. The constants and
threshold are fixed before the final starting index; the only orbit premises
are the source continuation tube bounds. -/
theorem factorBoundsOfActualTube (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∃ δ > 0, ∀ j0 : ℕ, 0 < j0 → scale p.beta j0 0 ^ (1 - p.beta) < δ →
      (∀ j, |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta)) →
      (∀ j, FastContraction.fixedNorm p.ell p.z
        (DFP.Polar.FastContraction.fastCoordinates ((p.withStartIndex j0).normalizedEvenState j) -
          FastContraction.evenFastReference p ((p.withStartIndex j0).normalizedEvenState j).1) ≤
        N * scale p.beta j0 j ^ (1 + p.beta)) →
      ∀ j : ℕ, ∀ i : Fin 2,
        1 < (p.withStartIndex j0).radiusRatio (2 * j + (i : ℕ)) ∧
        (radiusLimitCoefficient p i / 2) * scale p.beta j0 j ^ 2 ≤
          (p.withStartIndex j0).radiusRatio (2 * j + (i : ℕ)) - 1 ∧
        (p.withStartIndex j0).radiusRatio (2 * j + (i : ℕ)) - 1 ≤
          (radiusLimitCoefficient p i + C) * scale p.beta j0 j ^ 2 := by
  obtain ⟨C, hC, δ, hδ, herror⟩ := radiusBoundsOfActualTube p hβ hβone hM hN
  let D := min (radiusLimitCoefficient p 0) (radiusLimitCoefficient p 1)
  have hD : 0 < D := lt_min (radiusLimitCoefficient_pos p hβ 0)
    (radiusLimitCoefficient_pos p hβ 1)
  have htwoC : 0 < 2 * C := mul_pos zero_lt_two hC
  have hmin (i : Fin 2) : D ≤ radiusLimitCoefficient p i := by
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨min_le_left _ _, min_le_right _ _⟩
  refine ⟨C, hC, min δ (D / (2 * C)), lt_min hδ (div_pos hD htwoC), ?_⟩
  intro j0 hstart hsmall hslow hfast j i
  have ht := scale_pos p.beta hstart j
  have htone := scale_le_one hβ hstart j
  have hsmallError : scale p.beta j0 0 ^ (1 - p.beta) < δ :=
    hsmall.trans_le (min_le_left _ _)
  have hfactorError := herror j0 hstart hsmallError hslow hfast j i
  have hpower := Real.rpow_le_rpow ht.le
    (scale_antitone hβ hstart (Nat.zero_le j)) (sub_pos.mpr hβone).le
  have hsmallFactor : scale p.beta j0 j ^ (1 - p.beta) < D / (2 * C) :=
    hpower.trans_lt (hsmall.trans_le (min_le_right _ _))
  have hcoefficient : C * scale p.beta j0 j ^ (1 - p.beta) ≤
      radiusLimitCoefficient p i / 2 := by
    have h := (lt_div_iff₀ htwoC).mp hsmallFactor
    linarith [hmin i]
  have hbounds := Geometry.factor_sub_one_bounds hβone ht htone hC.le
    hcoefficient hfactorError
  have hpositive : 0 < (radiusLimitCoefficient p i / 2) * scale p.beta j0 j ^ 2 :=
    mul_pos (div_pos (radiusLimitCoefficient_pos p hβ i) zero_lt_two) (sq_pos_of_pos ht)
  have hfactor : 1 < (p.withStartIndex j0).radiusRatio (2 * j + (i : ℕ)) := by
    linarith [hbounds.1]
  exact ⟨hfactor, hbounds.1, hbounds.2⟩

/-- Helper for eq:polar-feedback: the selected source feedback potential is
strictly positive at its equilibrium. This is reusable positivity for the
actual correction coefficients. -/
theorem feedbackPotential_base_pos (p : Parameters) (hβ : 0 < p.beta) :
    0 < p.feedbackPotential p.gammaStar := by
  have hν : 0 < p.inverseParameter p.gammaStar := by
    rw [p.inverseParameter_gammaStar]
    exact sub_pos.mpr p.base.one_lt_ell
  exact p.feedbackPotential_pos hβ p.gammaStar_pos hν

/-- Helper for eq:polar-corrections: the exponential feedback defect lies
between one half and one times its nonnegative exponent when that exponent
is at most one half. This is a reusable scalar feedback estimate. -/
theorem feedback_defect_bounds {u : ℝ} (hu : 0 ≤ u) (hsmall : u ≤ 1 / 2) :
    u / 2 ≤ 1 - Real.exp (-u) ∧ 1 - Real.exp (-u) ≤ u := by
  have hnorm : |(-u)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hu]
    linarith
  have herror := Real.abs_exp_sub_one_sub_id_le hnorm
  have hupper := Real.add_one_le_exp (-u)
  have hsquare : u ^ 2 ≤ u / 2 := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hsmall)]
  constructor
  · have h := (abs_le.mp herror).2
    nlinarith
  · linarith

/-- Helper for eq:polar-corrections: a positive bounded feedback potential
gives two-sided correction bounds at the original vector, with its original
norm. This reusable estimate applies to the same correction that enters the
explicit interpolation objective. -/
theorem feedback_correction_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → ℝ) (v γ : ℝ) (x : E) {L U B : ℝ}
    (hL : 0 ≤ L) (hφLower : L ≤ φ γ) (hφUpper : φ γ ≤ U)
    (hv : 0 ≤ v) (hsmall : U * v ≤ 1 / 2) (hxLower : 1 ≤ ‖x‖) (hxUpper : ‖x‖ ≤ B) :
    (L / 2) * v ≤ ‖(Normalized.feedback φ v γ - 1) • x‖ ∧
      ‖(Normalized.feedback φ v γ - 1) • x‖ ≤ (B * U) * v := by
  have hφ : 0 ≤ φ γ := hL.trans hφLower
  have hu := mul_nonneg hφ hv
  have huSmall := (mul_le_mul_of_nonneg_right hφUpper hv).trans hsmall
  have hdefect := feedback_defect_bounds hu huSmall
  have hnonneg : 0 ≤ 1 - Real.exp (-(φ γ * v)) := by
    linarith [hdefect.1]
  have hfeedback : Normalized.feedback φ v γ ≤ 1 := by
    rw [Normalized.feedback_def, neg_mul]
    linarith
  have hnorm : ‖(Normalized.feedback φ v γ - 1) • x‖ =
      (1 - Real.exp (-(φ γ * v))) * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hfeedback),
      Normalized.feedback_def, neg_mul]
    ring
  rw [hnorm]
  constructor
  · have hscaled := mul_le_mul_of_nonneg_right hφLower hv
    have hlower : (L / 2) * v ≤ 1 - Real.exp (-(φ γ * v)) := by
      linarith [hdefect.1]
    exact hlower.trans (le_mul_of_one_le_right hnonneg hxLower)
  · calc
      (1 - Real.exp (-(φ γ * v))) * ‖x‖ ≤ (φ γ * v) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hdefect.2 (norm_nonneg x)
      _ ≤ (U * v) * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right hφUpper hv) hxUpper
          (norm_nonneg x) (mul_nonneg (hφ.trans hφUpper) hv)
      _ = (B * U) * v := by
        ring

/-- Helper for eq:polar-corrections: near the source equilibrium the
feedback potential stays above half its positive base value and below that
value plus one. This is reusable uniform scalar feedback control. -/
theorem feedbackPotential_eventually_bounds (p : Parameters) (hβ : 0 < p.beta) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      p.feedbackPotential p.gammaStar / 2 ≤ p.feedbackPotential γ ∧
        p.feedbackPotential γ ≤ p.feedbackPotential p.gammaStar + 1 := by
  have hP := feedbackPotential_base_pos p hβ
  have hhalf : p.feedbackPotential p.gammaStar / 2 < p.feedbackPotential p.gammaStar := by
    linarith
  have hupper : p.feedbackPotential p.gammaStar < p.feedbackPotential p.gammaStar + 1 := by
    linarith
  have hlimit := (p.feedbackPotential_analyticAt hβ).continuousAt.tendsto
  filter_upwards [Filter.Tendsto.eventually_const_lt hhalf hlimit,
    Filter.Tendsto.eventually_lt_const hupper hlimit]
    with γ hγLower hγUpper
  exact ⟨hγLower.le, hγUpper.le⟩

/-- Helper for eq:polar-angles: the scale of an index-shifted source
trajectory is exactly the generic power-law scale.
This is a reusable uniformity interface for actual-orbit estimates. -/
theorem scale_withStartIndex (p : Parameters) (j0 j : ℕ) :
    (p.withStartIndex j0).scale j = scale p.beta j0 j := by
  simp only [Parameters.scale_def, Parameters.withStartIndex_beta,
    Parameters.withStartIndex_startIndex]

/-- Helper for eq:polar-feedback: the independent inverse index of an
actual source trajectory is exactly its scale to power `1+β`.
This is a reusable bridge for the original correction coefficients. -/
theorem inverseIndex_withStartIndex (p : Parameters) (hβ : 0 < p.beta) (j0 j : ℕ) :
    (p.withStartIndex j0).inverseIndex j = scale p.beta j0 j ^ (1 + p.beta) := by
  rw [Parameters.inverseIndex_def, Parameters.withStartIndex_startIndex]
  exact (scale_rpow_one_add hβ j0 j).symm

/-- Helper for eq:polar-corrections: on the same actual source trajectory,
the original correction coefficients have a uniform upper bound at scale
`τ^(1+β)` and a positive lower bound at that scale at every odd point.
The constants precede the starting index. Only the slow tube and uniform
radius bounds are premises; no correction estimate is assumed. -/
theorem correctionBoundsOfActualSlowTube (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 < B) :
    ∃ c > 0, ∃ A > 0, ∃ δ > 0, ∀ j0 : ℕ, 0 < j0 →
      scale p.beta j0 0 ^ (1 - p.beta) < δ →
      (∀ j, |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta)) →
      (∀ k, 1 ≤ (p.withStartIndex j0).radius k ∧ (p.withStartIndex j0).radius k ≤ B) →
      (∀ k, ‖(p.withStartIndex j0).correction k‖ ≤
        A * scale p.beta j0 (k / 2) ^ (1 + p.beta)) ∧
      (∀ j, c * scale p.beta j0 j ^ (1 + p.beta) ≤
        ‖(p.withStartIndex j0).correction (2 * j + 1)‖) := by
  let P := p.feedbackPotential p.gammaStar
  let U := P + 1
  have hP : 0 < P := feedbackPotential_base_pos p hβ
  have hU : 0 < U := by
    dsimp only [U]
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (feedbackPotential_eventually_bounds p hβ)
  have hMOne : 0 < M + 1 := by
    linarith
  have htwoU : 0 < 2 * U := mul_pos zero_lt_two hU
  have hfour : (0 : ℝ) < 4 := by
    norm_num
  refine ⟨P / 4, div_pos hP hfour, B * U, mul_pos hB hU,
    min (ε / (M + 1)) (1 / (2 * U)),
      lt_min (div_pos hε hMOne) (one_div_pos.mpr htwoU), ?_⟩
  intro j0 hstart hsmall hslow hradius
  let q := p.withStartIndex j0
  have hodd (j : ℕ) : (P / 4) * scale p.beta j0 j ^ (1 + p.beta) ≤
      ‖q.correction (2 * j + 1)‖ ∧
      ‖q.correction (2 * j + 1)‖ ≤ (B * U) * scale p.beta j0 j ^ (1 + p.beta) := by
    have ht := scale_pos p.beta hstart j
    have htone := scale_le_one hβ hstart j
    have hpower := Real.rpow_le_rpow ht.le
      (scale_antitone hβ hstart (Nat.zero_le j)) (sub_pos.mpr hβone).le
    have hsmallState : scale p.beta j0 j ^ (1 - p.beta) < ε / (M + 1) :=
      hpower.trans_lt (hsmall.trans_le (min_le_left _ _))
    have hsmallFeedback : scale p.beta j0 j ^ (1 - p.beta) < 1 / (2 * U) :=
      hpower.trans_lt (hsmall.trans_le (min_le_right _ _))
    have hγ : (q.normalizedEvenState j).1 ∈ Metric.ball p.gammaStar ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hεsmall := (lt_div_iff₀ hMOne).mp hsmallState
      have hs := Real.rpow_nonneg ht.le (1 - p.beta)
      have hbound : M * scale p.beta j0 j ^ (1 - p.beta) < ε := by
        nlinarith
      exact (hslow j).trans_lt hbound
    have hφ := hball hγ
    have hexponents : 1 - p.beta ≤ 1 + p.beta := by
      linarith
    have hfastPower := Real.rpow_le_rpow_of_exponent_ge ht htone hexponents
    have hv : 0 ≤ q.inverseIndex j := by
      rw [inverseIndex_withStartIndex p hβ j0 j]
      exact Real.rpow_nonneg ht.le _
    have hsmallV : U * q.inverseIndex j ≤ 1 / 2 := by
      rw [inverseIndex_withStartIndex p hβ j0 j]
      have hbound := (lt_div_iff₀ htwoU).mp hsmallFeedback
      have hscaleBound := mul_le_mul_of_nonneg_left hfastPower hU.le
      nlinarith
    have hpointLower : 1 ≤ ‖q.point (2 * j + 1)‖ := by
      rw [q.point_norm _ (zero_le_one.trans (hradius (2 * j + 1)).1)]
      exact (hradius (2 * j + 1)).1
    have hpointUpper : ‖q.point (2 * j + 1)‖ ≤ B := by
      rw [q.point_norm _ (zero_le_one.trans (hradius (2 * j + 1)).1)]
      exact (hradius (2 * j + 1)).2
    have hφEqual : q.feedbackPotential = p.feedbackPotential :=
      (p.withStartIndex_analyticData j0).2.2
    have hcorrection : q.correction (2 * j + 1) =
        (Normalized.feedback p.feedbackPotential (q.inverseIndex j)
          (q.normalizedEvenState j).1 - 1) • q.point (2 * j + 1) := by
      rw [q.correction_def, q.zeta_odd, q.oddMultiplier_def, hφEqual]
    have h := feedback_correction_bounds p.feedbackPotential (q.inverseIndex j)
      (q.normalizedEvenState j).1 (q.point (2 * j + 1)) (div_pos hP zero_lt_two).le
      hφ.1 hφ.2 hv hsmallV hpointLower hpointUpper
    rw [← hcorrection, inverseIndex_withStartIndex p hβ j0 j] at h
    constructor
    · nlinarith [h.1]
    · exact h.2
  constructor
  · intro k
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [q.correction_even, norm_zero]
      exact mul_nonneg (mul_pos hB hU).le (Real.rpow_nonneg (scale_nonneg p.beta j0 _) _)
    · have hhalf : (2 * j + 1) / 2 = j := by
        omega
      rw [hhalf]
      exact (hodd j).2
  · intro j
    exact (hodd j).1

/-- Helper for eq:polar-wolfe-asymptotics: the current and next gradient
multipliers at either actual canceled source stage. The same original
boundary feedback is shared between the stages.
This is a reusable scalar source-observable interface. -/
def phaseMultipliers (p : Parameters) (i : Fin 2) (v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  ![(1, Normalized.feedback p.feedbackPotential v x.1),
    (Normalized.feedback p.feedbackPotential v x.1, 1)] i

/-- Helper for eq:polar-wolfe-asymptotics: the even stage changes its
gradient multiplier from one to the shared feedback.
This is the reusable even-phase scalar projection. -/
theorem phaseMultipliers_zero (p : Parameters) (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseMultipliers p 0 v x = (1, Normalized.feedback p.feedbackPotential v x.1) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the odd stage returns from the
shared feedback multiplier to one.
This is the reusable odd-phase scalar projection. -/
theorem phaseMultipliers_one (p : Parameters) (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseMultipliers p 1 v x = (Normalized.feedback p.feedbackPotential v x.1, 1) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: both multipliers are one at zero
inverse index, independently of the scale or state.
This is a reusable zero-parameter scalar identity. -/
theorem phaseMultipliers_at_zero (p : Parameters) (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    phaseMultipliers p i 0 x = (1, 1) := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseMultipliers_zero, Normalized.feedback_zero]
  · rw [phaseMultipliers_one, Normalized.feedback_zero]

/-- Helper for eq:polar-wolfe-asymptotics: the canceled Armijo model ratio
has no division by the scale. This reusable source observable uses the exact
analytic quadratic radial coefficient and the original multipliers. -/
def phaseArmijo (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  (2 * phaseCoefficient p i t v x + t ^ 2 * phaseCoefficient p i t v x ^ 2) /
    (2 * (phaseMultipliers p i v x).1 * phaseSlope p i t v x * phaseAngle p i v *
      Real.sinc (phaseAngle p i v * t) * phaseRadius p i t v x)

/-- Helper for eq:polar-wolfe-asymptotics: the exact canceled source
Armijo formula. This is its reusable scalar construction interface. -/
theorem phaseArmijo_def (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseArmijo p i t v x =
      (2 * phaseCoefficient p i t v x + t ^ 2 * phaseCoefficient p i t v x ^ 2) /
      (2 * (phaseMultipliers p i v x).1 * phaseSlope p i t v x * phaseAngle p i v *
        Real.sinc (phaseAngle p i v * t) * phaseRadius p i t v x) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the canceled strong-curvature
ratio has no division by the scale and retains the source absolute value.
This is a reusable scalar source observable. -/
def phaseCurvature (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  ((phaseMultipliers p i v x).2 / (phaseMultipliers p i v x).1) *
    |phaseSlope p i t v x * Real.cos (phaseAngle p i v * t) -
      phaseAngle p i v * Real.sinc (phaseAngle p i v * t)| /
    (phaseSlope p i t v x * phaseRadius p i t v x)

/-- Helper for eq:polar-wolfe-asymptotics: the exact canceled source
strong-curvature formula. This is its reusable construction interface. -/
theorem phaseCurvature_def (p : Parameters) (i : Fin 2) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseCurvature p i t v x =
      ((phaseMultipliers p i v x).2 / (phaseMultipliers p i v x).1) *
        |phaseSlope p i t v x * Real.cos (phaseAngle p i v * t) -
          phaseAngle p i v * Real.sinc (phaseAngle p i v * t)| /
      (phaseSlope p i t v x * phaseRadius p i t v x) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: every phase radius is one at zero
scale, even away from the base state. This is a reusable scalar identity. -/
theorem phaseRadius_zero_scale (p : Parameters) (i : Fin 2) (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseRadius p i 0 v x = 1 := by
  simp only [phaseRadius_def, radiusAtSlope_def, mul_zero, Real.cos_zero,
    Real.sin_zero, zero_mul, add_zero]

/-- Helper for eq:polar-wolfe-asymptotics: the selected source limiting
Armijo ratio. This is a reusable scalar datum independent of the final index. -/
def armijoLimit (p : Parameters) (i : Fin 2) : ℝ :=
  1 - phaseAngle p i 0 / (2 * referenceSlope p i)

/-- Helper for eq:polar-wolfe-asymptotics: the source formula for the
limiting Armijo ratio. This is its reusable scalar interface. -/
theorem armijoLimit_def (p : Parameters) (i : Fin 2) :
    armijoLimit p i = 1 - phaseAngle p i 0 / (2 * referenceSlope p i) := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: the selected source limiting
strong-curvature ratio. This is a reusable fixed-before-index scalar datum. -/
def curvatureLimit (p : Parameters) (i : Fin 2) : ℝ :=
  1 - phaseAngle p i 0 / referenceSlope p i

/-- Helper for eq:polar-wolfe-asymptotics: the source formula for the
limiting strong-curvature ratio. This is its reusable scalar interface. -/
theorem curvatureLimit_def (p : Parameters) (i : Fin 2) :
    curvatureLimit p i = 1 - phaseAngle p i 0 / referenceSlope p i := by
  rfl

/-- Helper for eq:polar-wolfe-asymptotics: each selected source limiting
slope is strictly positive. This is reusable positivity for the canceled
Wolfe quotient denominators. -/
theorem referenceSlope_pos (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    0 < referenceSlope p i :=
  (phaseAngle_base_pos p hβ i).trans (referenceSlope_gt_angle p hβ i)

/-- Helper for eq:polar-wolfe-asymptotics: the canceled Armijo observable
recovers the source Armijo limit at the selected equilibrium.
This is a reusable zero-parameter quotient identity. -/
theorem phaseArmijo_at_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    phaseArmijo p i 0 0 p.initialState = armijoLimit p i := by
  rw [phaseArmijo_def, phaseMultipliers_at_zero, phaseSlope_at_base p hβ,
    phaseCoefficient_at_base p hβ, phaseRadius_zero_scale]
  simp only [mul_zero, Real.sinc_zero, zero_pow two_ne_zero, zero_mul, add_zero,
    mul_one]
  rw [radiusLimitCoefficient_def, armijoLimit_def]
  field_simp [(phaseAngle_base_pos p hβ i).ne', (referenceSlope_pos p hβ i).ne']

/-- Helper for eq:polar-wolfe-asymptotics: the canceled curvature observable
recovers the source curvature limit at the selected equilibrium.
This is a reusable zero-parameter quotient identity. -/
theorem phaseCurvature_at_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    phaseCurvature p i 0 0 p.initialState = curvatureLimit p i := by
  rw [phaseCurvature_def, phaseMultipliers_at_zero, phaseSlope_at_base p hβ,
    phaseRadius_zero_scale]
  simp only [mul_zero, Real.cos_zero, Real.sinc_zero, div_self one_ne_zero,
    mul_one, one_mul]
  rw [abs_of_pos (sub_pos.mpr (referenceSlope_gt_angle p hβ i)), curvatureLimit_def]
  field_simp [(referenceSlope_pos p hβ i).ne']

/-- Helper for eq:polar-wolfe-asymptotics: the two curvature limits are
exactly the ratios selected by the general strict Wolfe base.
This is a reusable link to the parameter-selection theorem. -/
theorem curvatureLimit_eq_base (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    curvatureLimit p i = (![curvatureEven p.ell p.z, curvatureOdd p.ell p.z] : Fin 2 → ℝ) i := by
  have hell : 0 < p.ell := zero_lt_one.trans p.base.one_lt_ell
  have hQE : 1 + p.deltaEven = p.ell + p.z := by
    rw [p.deltaEven_def, baseDeltaEven_def]
    ring
  have hQO : p.ell + p.deltaOdd = 1 + p.z * p.ell := by
    rw [p.deltaOdd_def, baseDeltaOdd_def]
    ring
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [curvatureLimit_def, phaseAngle_zero, p.evenAngleFactor_zero hβ,
      referenceSlope_zero, hQE, p.deltaEven_def, baseDeltaEven_def]
    simp only [Matrix.cons_val_zero, curvatureEven_def]
    field_simp [(add_pos hell p.base.z_pos).ne']
    ring
  · rw [curvatureLimit_def, phaseAngle_one, p.oddAngleFactor_zero hβ,
      referenceSlope_one, hQO, p.deltaOdd_def, baseDeltaOdd_def]
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, curvatureOdd_def]
    field_simp [(add_pos zero_lt_one (mul_pos p.base.z_pos hell)).ne',
      (add_pos zero_lt_one (mul_pos hell p.base.z_pos)).ne']
    ring

/-- Helper for eq:polar-wolfe-asymptotics: each limiting Armijo ratio equals
one half plus one half of the corresponding curvature ratio.
This is a reusable scalar relation for the selected source limits. -/
theorem armijoLimit_eq_half_add_curvature (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    armijoLimit p i = (1 + curvatureLimit p i) / 2 := by
  rw [armijoLimit_def, curvatureLimit_def]
  field_simp [(referenceSlope_pos p hβ i).ne']
  ring

/-- Helper for eq:polar-wolfe-asymptotics: both selected source curvature
limits satisfy the strict requested Wolfe upper margin.
This is a reusable consequence of the actual parameter-selection witness. -/
theorem curvatureLimit_lt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    curvatureLimit p i < p.c2 := by
  rw [curvatureLimit_eq_base p hβ]
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨p.base.even_curvature_lt, p.base.odd_curvature_lt⟩

/-- Helper for eq:polar-wolfe-asymptotics: both selected source Armijo limits
satisfy the strict requested Wolfe lower margin.
This is a reusable consequence of the actual parameter-selection witness. -/
theorem armijoLimit_gt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    p.c1 < armijoLimit p i := by
  rw [armijoLimit_eq_half_add_curvature p hβ, curvatureLimit_eq_base p hβ]
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨p.base.even_armijo_lt, p.base.odd_armijo_lt⟩

/-- Helper for eq:polar-wolfe-asymptotics: the exact gradient multipliers
are jointly analytic in the independent small parameters and boundary state
at the source equilibrium. This is a reusable actual-cycle observable API. -/
theorem phaseMultipliers_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseMultipliers p i z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have hv : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2) ((0, 0), p.initialState) :=
    analyticAt_snd.comp analyticAt_fst
  have hγ : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1) ((0, 0), p.initialState) :=
    analyticAt_fst.comp analyticAt_snd
  have hfirst : p.initialState.1 = p.gammaStar := by
    simp only [p.initialState_def, cycleState_apply]
  have hφ : AnalyticAt ℝ p.feedbackPotential p.initialState.1 := by
    rw [hfirst]
    exact p.feedbackPotential_analyticAt hβ
  have hfeedback := Normalized.feedbackAlong_analyticAt
    (γ := fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.2.1)
    (z := ((0, 0), p.initialState)) hφ hv hγ
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [phaseMultipliers_zero] using analyticAt_const.prod hfeedback
  · simpa only [phaseMultipliers_one] using hfeedback.prod analyticAt_const

/-- Helper for eq:polar-wolfe-asymptotics: the source phase radius is
jointly analytic at zero independent parameters by its exact canceled form.
This is a reusable radial-observable interface. -/
theorem phaseRadius_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseRadius p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have ht : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1) ((0, 0), p.initialState) :=
    analyticAt_fst.comp analyticAt_fst
  simp only [phaseRadius_eq_one_add_sq]
  exact analyticAt_const.add ((ht.pow 2).mul (phaseCoefficient_joint_analyticAt p hβ i))

/-- Helper for eq:polar-wolfe-asymptotics: the canceled source Armijo ratio
is jointly continuous at the selected equilibrium, with its denominator
proved nonzero from the actual base slopes and angles.
This is a reusable source-neighborhood interface. -/
theorem phaseArmijo_joint_continuousAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseArmijo p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have ht : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1) ((0, 0), p.initialState) :=
    continuousAt_fst.comp continuousAt_fst
  have hv : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2) ((0, 0), p.initialState) :=
    analyticAt_snd.comp analyticAt_fst
  have ha : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseAngle p i z.1.2)
      ((0, 0), p.initialState) := ((phaseAngle_analyticAt p i).comp_of_eq hv rfl).continuousAt
  have hQ := (phaseSlope_joint_analyticAt p hβ i).continuousAt
  have hD := (phaseCoefficient_joint_analyticAt p hβ i).continuousAt
  have hR := (phaseRadius_joint_analyticAt p hβ i).continuousAt
  have hmult := (phaseMultipliers_joint_analyticAt p hβ i).continuousAt
  have hζ := continuousAt_fst.comp hmult
  have hsinc : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ Real.sinc (phaseAngle p i z.1.2 * z.1.1))
      ((0, 0), p.initialState) := Real.continuous_sinc.continuousAt.comp (ha.mul ht)
  have hden : 2 * (phaseMultipliers p i 0 p.initialState).1 *
      phaseSlope p i 0 0 p.initialState * phaseAngle p i 0 *
      Real.sinc (phaseAngle p i 0 * 0) * phaseRadius p i 0 0 p.initialState ≠ 0 := by
    rw [phaseMultipliers_at_zero, phaseSlope_at_base p hβ, phaseRadius_zero_scale]
    simp only [mul_zero, Real.sinc_zero, mul_one]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (referenceSlope_pos p hβ i).ne')
      (phaseAngle_base_pos p hβ i).ne'
  simp only [phaseArmijo_def]
  exact ((continuousAt_const.mul hD).add ((ht.pow 2).mul (hD.pow 2))).div
    (((((continuousAt_const.mul hζ).mul hQ).mul ha).mul hsinc).mul hR) hden

/-- Helper for eq:polar-wolfe-asymptotics: the canceled strong-curvature
ratio is jointly continuous at the selected equilibrium, including its
absolute value, with all quotient denominators proved nonzero.
This is a reusable source-neighborhood interface. -/
theorem phaseCurvature_joint_continuousAt (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseCurvature p i z.1.1 z.1.2 z.2)
      ((0, 0), p.initialState) := by
  have ht : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.1) ((0, 0), p.initialState) :=
    continuousAt_fst.comp continuousAt_fst
  have hv : AnalyticAt ℝ
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ z.1.2) ((0, 0), p.initialState) :=
    analyticAt_snd.comp analyticAt_fst
  have ha : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseAngle p i z.1.2)
      ((0, 0), p.initialState) := ((phaseAngle_analyticAt p i).comp_of_eq hv rfl).continuousAt
  have hQ := (phaseSlope_joint_analyticAt p hβ i).continuousAt
  have hR := (phaseRadius_joint_analyticAt p hβ i).continuousAt
  have hmult := (phaseMultipliers_joint_analyticAt p hβ i).continuousAt
  have hζ := continuousAt_fst.comp hmult
  have hη := continuousAt_snd.comp hmult
  have hsinc : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ Real.sinc (phaseAngle p i z.1.2 * z.1.1))
      ((0, 0), p.initialState) := Real.continuous_sinc.continuousAt.comp (ha.mul ht)
  have hcos : ContinuousAt
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ Real.cos (phaseAngle p i z.1.2 * z.1.1))
      ((0, 0), p.initialState) := Real.continuous_cos.continuousAt.comp (ha.mul ht)
  have hζbase : (phaseMultipliers p i 0 p.initialState).1 ≠ 0 := by
    rw [phaseMultipliers_at_zero]
    exact one_ne_zero
  have hden : phaseSlope p i 0 0 p.initialState * phaseRadius p i 0 0 p.initialState ≠ 0 := by
    rw [phaseSlope_at_base p hβ, phaseRadius_zero_scale, mul_one]
    exact (referenceSlope_pos p hβ i).ne'
  simp only [phaseCurvature_def]
  exact ((hη.div hζ hζbase).mul ((hQ.mul hcos).sub (ha.mul hsinc)).abs).div
    (hQ.mul hR) hden

/-- Helper for eq:polar-wolfe-asymptotics: each actual canceled source phase
satisfies strict Armijo and strong-curvature margins on a neighborhood of the
selected zero-parameter equilibrium. The inequalities follow from the
chosen general Wolfe base and continuity, rather than assumed acceptance. -/
theorem phaseWolfe_eventually (p : Parameters) (hβ : 0 < p.beta) (i : Fin 2) :
    ∀ᶠ z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) in 𝓝 ((0, 0), p.initialState),
      p.c1 < phaseArmijo p i z.1.1 z.1.2 z.2 ∧
        phaseCurvature p i z.1.1 z.1.2 z.2 < p.c2 := by
  have hA : p.c1 < phaseArmijo p i 0 0 p.initialState := by
    rw [phaseArmijo_at_base p hβ]
    exact armijoLimit_gt p hβ i
  have hC : phaseCurvature p i 0 0 p.initialState < p.c2 := by
    rw [phaseCurvature_at_base p hβ]
    exact curvatureLimit_lt p hβ i
  have hlimitA : Tendsto
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseArmijo p i z.1.1 z.1.2 z.2)
      (𝓝 ((0, 0), p.initialState)) (𝓝 (phaseArmijo p i 0 0 p.initialState)) :=
    (phaseArmijo_joint_continuousAt p hβ i).tendsto
  have hlimitC : Tendsto
      (fun z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ phaseCurvature p i z.1.1 z.1.2 z.2)
      (𝓝 ((0, 0), p.initialState)) (𝓝 (phaseCurvature p i 0 0 p.initialState)) :=
    (phaseCurvature_joint_continuousAt p hβ i).tendsto
  filter_upwards [Filter.Tendsto.eventually_const_lt hA hlimitA,
    Filter.Tendsto.eventually_lt_const hC hlimitC]
    with z hArmijo hCurvature
  exact ⟨hArmijo, hCurvature⟩

/-- Helper for eq:polar-wolfe-asymptotics: at nonzero scale the canceled
Armijo observable equals the original raw radius-ratio quotient. The equality
uses the exact radial cancellation and remains valid at totalized zero values
of the other denominators. This is a reusable source quotient bridge. -/
theorem phaseArmijo_eq_raw (p : Parameters) (i : Fin 2) {t : ℝ} (ht : t ≠ 0)
    (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseArmijo p i t v x = (phaseRadius p i t v x ^ 2 - 1) /
      (2 * (phaseMultipliers p i v x).1 * (t * phaseSlope p i t v x) *
        Real.sin (phaseAngle p i v * t) * phaseRadius p i t v x) := by
  have hs : Real.sin (phaseAngle p i v * t) =
      t * phaseAngle p i v * Real.sinc (phaseAngle p i v * t) := by
    calc
      Real.sin (phaseAngle p i v * t) =
          (phaseAngle p i v * t) * Real.sinc (phaseAngle p i v * t) :=
        (mul_sinc_eq_sin _).symm
      _ = t * phaseAngle p i v * Real.sinc (phaseAngle p i v * t) := by
        ring
  have hnum : phaseRadius p i t v x ^ 2 - 1 =
      t ^ 2 * (2 * phaseCoefficient p i t v x + t ^ 2 * phaseCoefficient p i t v x ^ 2) := by
    rw [phaseRadius_eq_one_add_sq]
    ring
  have hden : 2 * (phaseMultipliers p i v x).1 * (t * phaseSlope p i t v x) *
      Real.sin (phaseAngle p i v * t) * phaseRadius p i t v x =
      t ^ 2 * (2 * (phaseMultipliers p i v x).1 * phaseSlope p i t v x * phaseAngle p i v *
        Real.sinc (phaseAngle p i v * t) * phaseRadius p i t v x) := by
    rw [hs]
    ring
  rw [hnum, hden, phaseArmijo_def, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

/-- Helper for eq:polar-wolfe-asymptotics: at positive scale the canceled
curvature observable equals the source raw curvature quotient at slope `t Q`.
The scale is canceled through its positive absolute value, preserving the
actual current and next gradient multipliers.
This is a reusable source quotient bridge. -/
theorem phaseCurvature_eq_raw (p : Parameters) (i : Fin 2) {t : ℝ} (ht : 0 < t)
    (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseCurvature p i t v x =
      ((phaseMultipliers p i v x).2 / (phaseMultipliers p i v x).1) *
        |(t * phaseSlope p i t v x) * Real.cos (phaseAngle p i v * t) -
          Real.sin (phaseAngle p i v * t)| /
      ((t * phaseSlope p i t v x) * phaseRadius p i t v x) := by
  have hs : Real.sin (phaseAngle p i v * t) =
      t * phaseAngle p i v * Real.sinc (phaseAngle p i v * t) := by
    calc
      Real.sin (phaseAngle p i v * t) =
          (phaseAngle p i v * t) * Real.sinc (phaseAngle p i v * t) :=
        (mul_sinc_eq_sin _).symm
      _ = t * phaseAngle p i v * Real.sinc (phaseAngle p i v * t) := by
        ring
  have hinner : (t * phaseSlope p i t v x) * Real.cos (phaseAngle p i v * t) -
      Real.sin (phaseAngle p i v * t) =
      t * (phaseSlope p i t v x * Real.cos (phaseAngle p i v * t) -
        phaseAngle p i v * Real.sinc (phaseAngle p i v * t)) := by
    rw [hs]
    ring
  rw [hinner, abs_mul, abs_of_pos ht, phaseCurvature_def]
  have hnum : ((phaseMultipliers p i v x).2 / (phaseMultipliers p i v x).1) *
      (t * |phaseSlope p i t v x * Real.cos (phaseAngle p i v * t) -
        phaseAngle p i v * Real.sinc (phaseAngle p i v * t)|) =
      t * (((phaseMultipliers p i v x).2 / (phaseMultipliers p i v x).1) *
        |phaseSlope p i t v x * Real.cos (phaseAngle p i v * t) -
          phaseAngle p i v * Real.sinc (phaseAngle p i v * t)|) := by
    ring
  rw [hnum, mul_assoc t, mul_div_mul_left _ _ ht.ne']

/-- Helper for eq:polar-wolfe-asymptotics: scalar parameter bounds and an
ordinary-state bound control distance in the canonical independent-parameter
product space. This is reusable metric support for source neighborhoods. -/
theorem input_dist_le {x x₀ : ℝ × ℝ × ℝ} {t v s B : ℝ}
    (ht : |t| ≤ s) (hv : |v| ≤ s) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hx : ‖x - x₀‖ ≤ B * s) : dist ((t, v), x) ((0, 0), x₀) ≤ (B + 1) * s := by
  have hcommon : s ≤ (B + 1) * s := by
    nlinarith [mul_nonneg hB hs]
  have hstate : B * s ≤ (B + 1) * s := by
    nlinarith
  rw [Prod.dist_eq, Prod.dist_eq]
  apply max_le
  · apply max_le
    · rw [Real.dist_eq, sub_zero]
      exact ht.trans hcommon
    · rw [Real.dist_eq, sub_zero]
      exact hv.trans hcommon
  · rw [dist_eq_norm]
    exact hx.trans hstate

/-- Helper for eq:polar-wolfe-asymptotics: an ordinary-state bound of the
source slow order places both actual canceled phases inside their strict
Wolfe neighborhoods, uniformly in the independent inverse index.
This is a reusable local source-acceptance estimate. -/
theorem localWolfeMarginsOfStateBound (p : Parameters) (hβ : 0 < p.beta)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ v : ℝ, |v| ≤ t ^ (1 - p.beta) → ∀ x : ℝ × ℝ × ℝ,
        ‖x - p.initialState‖ ≤ B * t ^ (1 - p.beta) → ∀ i : Fin 2,
        p.c1 < phaseArmijo p i t v x ∧ phaseCurvature p i t v x < p.c2 := by
  have hevent : ∀ᶠ z : (ℝ × ℝ) × (ℝ × ℝ × ℝ) in 𝓝 ((0, 0), p.initialState),
      ∀ i : Fin 2, p.c1 < phaseArmijo p i z.1.1 z.1.2 z.2 ∧
        phaseCurvature p i z.1.1 z.1.2 z.2 < p.c2 := by
    filter_upwards [phaseWolfe_eventually p hβ 0, phaseWolfe_eventually p hβ 1]
      with z hfirst hsecond
    rw [Fin.forall_fin_two]
    exact ⟨hfirst, hsecond⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hBOne : 0 < B + 1 := by
    linarith
  refine ⟨ε / (B + 1), div_pos hε hBOne, ?_⟩
  intro t ht htone htδ v hv x hx i
  have hexponent : 1 - p.beta ≤ 1 := by
    linarith
  have htSlow : |t| ≤ t ^ (1 - p.beta) := by
    rw [abs_of_pos ht]
    exact Real.self_le_rpow_of_le_one ht.le htone hexponent
  have hdist := input_dist_le htSlow hv (Real.rpow_nonneg ht.le _) hB hx
  have hsmall : (B + 1) * t ^ (1 - p.beta) < ε := by
    nlinarith [(lt_div_iff₀ hBOne).mp htδ]
  exact hball (Metric.mem_ball.mpr (hdist.trans_lt hsmall)) i

/-- Helper for eq:polar-wolfe-asymptotics: the source slow and fast tube
places both actual canceled phases in their strict Wolfe neighborhoods.
The neighborhood threshold is fixed before the starting index is increased. -/
theorem localWolfeMarginsOfTube (p : Parameters) (hβ : 0 < p.beta)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t ≤ 1 → t ^ (1 - p.beta) < δ →
      ∀ v : ℝ, |v| ≤ t ^ (1 - p.beta) → ∀ x : ℝ × ℝ × ℝ,
        |x.1 - p.gammaStar| ≤ M * t ^ (1 - p.beta) →
        FastContraction.fixedNorm p.ell p.z
          (DFP.Polar.FastContraction.fastCoordinates x -
            FastContraction.evenFastReference p x.1) ≤ N * t ^ (1 + p.beta) →
        ∀ i : Fin 2, p.c1 < phaseArmijo p i t v x ∧ phaseCurvature p i t v x < p.c2 := by
  obtain ⟨B, hB, δs, hδs, hstate⟩ := stateBoundOfTube p hβ hM hN
  obtain ⟨δw, hδw, hwolfe⟩ := localWolfeMarginsOfStateBound p hβ hB.le
  refine ⟨min δs δw, lt_min hδs hδw, ?_⟩
  intro t ht htone htδ v hv x hslow hfast i
  have hts : t ^ (1 - p.beta) < δs := htδ.trans_le (min_le_left _ _)
  have htw : t ^ (1 - p.beta) < δw := htδ.trans_le (min_le_right _ _)
  exact hwolfe t ht htone htw v hv x (hstate t ht htone hts x hslow hfast) i

/-- Helper for eq:polar-wolfe-asymptotics: changing the starting index does
not change the exact phase multipliers at independent parameter values.
This is a reusable uniformity interface for the actual Wolfe observables. -/
theorem phaseMultipliers_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseMultipliers (p.withStartIndex j0) i v x = phaseMultipliers p i v x := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [phaseMultipliers_zero, phaseMultipliers_zero,
      (p.withStartIndex_analyticData j0).2.2]
  · rw [phaseMultipliers_one, phaseMultipliers_one,
      (p.withStartIndex_analyticData j0).2.2]

/-- Helper for eq:polar-wolfe-asymptotics: the canceled Armijo observable
is fixed before increasing the starting index.
This is a reusable uniformity identity for the actual source ratios. -/
theorem phaseArmijo_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseArmijo (p.withStartIndex j0) i t v x = phaseArmijo p i t v x := by
  simp only [phaseArmijo_def, phaseCoefficient_def, phaseSlope_def,
    phaseAngle_withStartIndex, phaseInput_withStartIndex, phaseMultipliers_withStartIndex,
    phaseRadius_withStartIndex]

/-- Helper for eq:polar-wolfe-asymptotics: the canceled strong-curvature
observable is fixed before increasing the starting index.
This is a reusable uniformity identity for the actual source ratios. -/
theorem phaseCurvature_withStartIndex (p : Parameters) (j0 : ℕ) (i : Fin 2)
    (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    phaseCurvature (p.withStartIndex j0) i t v x = phaseCurvature p i t v x := by
  simp only [phaseCurvature_def, phaseSlope_def, phaseAngle_withStartIndex,
    phaseInput_withStartIndex, phaseMultipliers_withStartIndex, phaseRadius_withStartIndex]

/-- Helper for eq:polar-wolfe-asymptotics: every actual source cycle in the
proved continuation tube has strict canceled Armijo and strong-curvature
margins once the initial scale crosses a threshold selected before the final
starting index. The ratios are evaluated on that same recursive trajectory
and coincide with the raw ratios through the cancellation identities above. -/
theorem wolfeBoundsOfActualTube (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ δ > 0, ∀ j0 : ℕ, 0 < j0 → scale p.beta j0 0 ^ (1 - p.beta) < δ →
      (∀ j, |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta)) →
      (∀ j, FastContraction.fixedNorm p.ell p.z
        (DFP.Polar.FastContraction.fastCoordinates ((p.withStartIndex j0).normalizedEvenState j) -
          FastContraction.evenFastReference p ((p.withStartIndex j0).normalizedEvenState j).1) ≤
        N * scale p.beta j0 j ^ (1 + p.beta)) →
      ∀ j : ℕ, ∀ i : Fin 2,
        p.c1 < phaseArmijo (p.withStartIndex j0) i ((p.withStartIndex j0).scale j)
          ((p.withStartIndex j0).inverseIndex j) ((p.withStartIndex j0).normalizedEvenState j) ∧
        phaseCurvature (p.withStartIndex j0) i ((p.withStartIndex j0).scale j)
          ((p.withStartIndex j0).inverseIndex j) ((p.withStartIndex j0).normalizedEvenState j) <
            p.c2 := by
  obtain ⟨δ, hδ, hbound⟩ := localWolfeMarginsOfTube p hβ hM hN
  refine ⟨δ, hδ, ?_⟩
  intro j0 hstart hsmall hslow hfast j i
  let q := p.withStartIndex j0
  have ht := scale_pos p.beta hstart j
  have htone := scale_le_one hβ hstart j
  have hpower := Real.rpow_le_rpow ht.le
    (scale_antitone hβ hstart (Nat.zero_le j)) (sub_pos.mpr hβone).le
  have hlocal : scale p.beta j0 j ^ (1 - p.beta) < δ := hpower.trans_lt hsmall
  have hexponents : 1 - p.beta ≤ 1 + p.beta := by
    linarith
  have hv : |q.inverseIndex j| ≤ scale p.beta j0 j ^ (1 - p.beta) := by
    rw [inverseIndex_withStartIndex p hβ j0 j, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    exact Real.rpow_le_rpow_of_exponent_ge ht htone hexponents
  have h := hbound (scale p.beta j0 j) ht htone hlocal (q.inverseIndex j) hv
    (q.normalizedEvenState j) (hslow j) (hfast j) i
  rw [phaseArmijo_withStartIndex, phaseCurvature_withStartIndex, scale_withStartIndex]
  exact h

end DFP.Polar.General.RadiusBounds
