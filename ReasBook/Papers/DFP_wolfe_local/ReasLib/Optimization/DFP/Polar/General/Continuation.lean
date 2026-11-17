module

public import ReasLib.Optimization.DFP.Polar.General.FastContraction
public import ReasLib.Optimization.DFP.Polar.General.TubeBounds
public import ReasLib.Optimization.DFP.Polar.General.PhysicalRecurrence
public import ReasLib.Optimization.DFP.Polar.General.Estimates
public import ReasLib.Optimization.DFP.Polar.StageFeasibility

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.General.Continuation

open DFP.Polar.General.FastContraction
open DFP.Polar.FastContraction (fastCoordinates)
open DFP.Polar.StageFeasibility (regularState)

/-- Helper for lem:polar-continuation: displacement from the genuine even curve at the
state's own first coordinate. -/
def fastError (p : Parameters) (x : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  fastCoordinates x - evenFastReference p x.1

/-- Helper for lem:polar-continuation: the fixed norm of the transverse displacement. -/
def fastSize (p : Parameters) (x : ℝ × ℝ × ℝ) : ℝ :=
  fixedNorm p.ell p.z (fastError p x)

/-- Helper for lem:polar-continuation: the signed slow displacement from equilibrium. -/
def slowError (p : Parameters) (x : ℝ × ℝ × ℝ) : ℝ := x.1 - p.gammaStar

/-- Helper for lem:polar-continuation: the source transverse error formula. -/
theorem fastError_def (p : Parameters) (x : ℝ × ℝ × ℝ) :
    fastError p x = fastCoordinates x - evenFastReference p x.1 := by
  rfl

/-- Helper for lem:polar-continuation: the source fixed-norm error formula. -/
theorem fastSize_def (p : Parameters) (x : ℝ × ℝ × ℝ) :
    fastSize p x = fixedNorm p.ell p.z (fastError p x) := by
  rfl

/-- Helper for lem:polar-continuation: the source slow displacement formula. -/
theorem slowError_def (p : Parameters) (x : ℝ × ℝ × ℝ) :
    slowError p x = x.1 - p.gammaStar := by
  rfl

/-- Helper for lem:polar-continuation: the transverse displacement size is nonnegative. -/
theorem fastSize_nonneg (p : Parameters) (x : ℝ × ℝ × ℝ) : 0 ≤ fastSize p x := by
  exact fixedNorm_nonneg _ _ _

/-- Helper for lem:polar-continuation: each reference state has zero transverse displacement. -/
theorem fastError_evenReference (p : Parameters) (γ : ℝ) :
    fastError p (p.evenReference γ) = 0 := by
  rw [fastError_def, p.evenReference_fst, evenFastReference_apply, sub_self]

/-- Helper for lem:polar-continuation: the fixed transverse error size vanishes on the reference
curve. -/
theorem fastSize_evenReference (p : Parameters) (γ : ℝ) :
    fastSize p (p.evenReference γ) = 0 := by
  rw [fastSize_def, fastError_evenReference, fixedNorm_eq_norm, map_zero, norm_zero]

/-- Helper for lem:polar-continuation: the actual initial normalized state has zero fast error. -/
theorem fastSize_initialState (p : Parameters) : fastSize p p.initialState = 0 := by
  rw [← p.evenReference_gammaStar]
  exact fastSize_evenReference p _

/-- Helper for lem:polar-continuation: the actual initial normalized state has zero slow error. -/
theorem slowError_initialState (p : Parameters) : slowError p p.initialState = 0 := by
  rw [← p.evenReference_gammaStar, slowError_def, p.evenReference_fst, sub_self]

/-- Helper for lem:polar-continuation: reference plus error recovers the actual fast coordinates. -/
theorem reference_add_fastError (p : Parameters) (x : ℝ × ℝ × ℝ) :
    evenFastReference p x.1 + fastError p x = fastCoordinates x := by
  rw [fastError_def]
  abel

/-- Helper for lem:polar-continuation: every state is reconstructed from its slow coordinate
and transverse displacement. -/
theorem state_reconstruction (p : Parameters) (x : ℝ × ℝ × ℝ) :
    (x.1, (evenFastReference p x.1 + fastError p x) 0,
      (evenFastReference p x.1 + fastError p x) 1) = x := by
  rw [reference_add_fastError, DFP.Polar.FastContraction.fastCoordinates_apply]
  rcases x with ⟨γ, C, V⟩
  rfl

/-- Helper for lem:polar-continuation: displacement from the reference has zero first coordinate. -/
theorem state_sub_evenReference (p : Parameters) (x : ℝ × ℝ × ℝ) :
    x - p.evenReference x.1 = (0, fastError p x 0, fastError p x 1) := by
  simp only [fastError_def, evenFastReference_apply,
    DFP.Polar.FastContraction.fastCoordinates_apply, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  apply Prod.ext
  · simp only [Prod.fst_sub, p.evenReference_fst, sub_self]
  · rfl

/-- Helper for lem:polar-continuation: the fast norm controls the whole displacement from the
reference. -/
theorem norm_state_sub_evenReference_le (p : Parameters) (x : ℝ × ℝ × ℝ) :
    ‖x - p.evenReference x.1‖ ≤ fastSize p x := by
  rw [state_sub_evenReference]
  have hnorm : ‖((0, fastError p x 0, fastError p x 1) : ℝ × ℝ × ℝ)‖ ≤ ‖fastError p x‖ := by
    simp only [Prod.norm_mk, norm_zero]
    exact max_le (norm_nonneg _) (max_le (norm_le_pi_norm _ 0) (norm_le_pi_norm _ 1))
  exact hnorm.trans (norm_le_fixedNorm p.base.stable _)

/-- Helper for lem:polar-continuation: a fixed tube box fits into any prescribed neighborhood
of the actual initial state. -/
theorem exists_tube_sub_neighborhood (p : Parameters) {s : Set (ℝ × ℝ × ℝ)}
    (hs : s ∈ 𝓝 p.initialState) :
    ∃ r > 0, ∃ ρ > 0, ∀ x : ℝ × ℝ × ℝ,
      |slowError p x| ≤ r → fastSize p x ≤ ρ → x ∈ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have href : ∀ᶠ γ in 𝓝 p.gammaStar,
      dist (p.evenReference γ) p.initialState < ε / 2 := by
    have hcont := p.evenReference_analyticAt.continuousAt
    have hlim : Tendsto p.evenReference (𝓝 p.gammaStar) (𝓝 p.initialState) := by
      simpa only [ContinuousAt, p.evenReference_gammaStar] using hcont
    exact hlim.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨η, hη, hηbound⟩ := Metric.eventually_nhds_iff.mp href
  have hfour : (0 : ℝ) < 4 := by norm_num
  refine ⟨η / 2, half_pos hη, ε / 4, div_pos hε hfour, ?_⟩
  intro x hxslow hxfast
  have hxγ : dist x.1 p.gammaStar < η := by
    rw [Real.dist_eq, ← slowError_def]
    linarith
  apply hball
  have hrefdist := hηbound hxγ
  have hfastdist : dist x (p.evenReference x.1) ≤ ε / 4 := by
    rw [dist_eq_norm]
    exact (norm_state_sub_evenReference_le p x).trans hxfast
  have htriangle := dist_triangle x (p.evenReference x.1) p.initialState
  have hsum : dist x (p.evenReference x.1) + dist (p.evenReference x.1) p.initialState < ε := by
    linarith
  exact htriangle.trans_lt hsum

/-- Helper for lem:polar-continuation: the initial state lies in the positive normalized domain. -/
theorem regularState_initialState (p : Parameters) : regularState p.initialState := by
  rw [DFP.Polar.StageFeasibility.regularState_def, p.initialState_def, cycleState_apply]
  have hγ := p.gammaStar_pos
  have hell : 0 < p.ell := lt_trans zero_lt_one p.base.one_lt_ell
  refine ⟨hγ, mul_pos hγ hell, ?_⟩
  have hdet : p.gammaStar * (1 + p.gammaStar * p.ell ^ 2) -
      (p.gammaStar * p.ell) ^ 2 = p.gammaStar := by ring
  rwa [hdet]

/-- Helper for lem:polar-continuation: the odd reference at equilibrium lies in the positive
domain. -/
theorem regularState_oddReference (p : Parameters) :
    regularState (p.oddReference p.gammaStar) := by
  rw [p.oddReference_gammaStar, DFP.Polar.StageFeasibility.regularState_def, cycleState_apply]
  have hγ := p.gammaStar_pos
  refine ⟨hγ, ?_, ?_⟩
  · simpa only [mul_one] using hγ
  · simp only [one_pow, mul_one]
    nlinarith

/-- Helper for lem:polar-continuation: one source normalized even stage. -/
def firstStage (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  Normalized.cycleStage aE aO φ 0 t v x x

/-- Helper for lem:polar-continuation: the concrete first-stage formula. -/
theorem firstStage_def (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    firstStage aE aO φ t v x = Normalized.cycleStage aE aO φ 0 t v x x := by
  rfl

/-- Helper for lem:polar-continuation: at the base parameters the even stage lands on the odd
reference. -/
theorem firstStage_initialState (p : Parameters) (hβ : 0 < p.beta) :
    firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 p.initialState =
      p.oddReference p.gammaStar := by
  rw [firstStage_def, Normalized.cycleStage_even, Normalized.feedback_zero,
    Normalized.stage_zero, p.evenAngleFactor_zero hβ]
  have h := p.referenceCycle_eventually.self_of_nhds
  simpa only [p.evenReference_gammaStar] using h.1

/-- Helper for lem:polar-continuation: the normalized radius factor with the new linear scale. -/
def normalizedRadius (a t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Real.cos (Normalized.stageAngle a t) +
    t * Normalized.slope x * Real.sin (Normalized.stageAngle a t)

/-- Helper for lem:polar-continuation: the radius factor is one at zero scale. -/
theorem normalizedRadius_zero (a : ℝ) (x : ℝ × ℝ × ℝ) : normalizedRadius a 0 x = 1 := by
  simp [normalizedRadius, Normalized.stageAngle_def]

/-- Helper for lem:polar-continuation: a normalized secant scalar at unit multipliers is one at
zero scale. -/
theorem stageSigma_zero_unit (a : ℝ) (x : ℝ × ℝ × ℝ) :
    Normalized.stageSigma a 0 x 1 1 = 1 := by
  simp [Normalized.stageSigma_def, Normalized.stepV_def, Normalized.stepW_def]

/-- Helper for lem:polar-continuation: the normalized slope is continuous along regular state
germs. -/
theorem slopeAlong_continuousAt {E : Type*} [TopologicalSpace E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : ContinuousAt X z) (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ Normalized.slope (X y)) z := by
  have hCV := continuousAt_snd.comp hX
  have hfirst := continuousAt_fst.comp hCV
  have hsecond := continuousAt_snd.comp hCV
  simpa only [Normalized.slope_def, Function.comp_def] using hsecond.div₀ hfirst hC

/-- Helper for lem:polar-continuation: the canceled cotangent is continuous at nonzero angles
and zero scale. -/
theorem cotFactorAlong_continuousAt {E : Type*} [TopologicalSpace E]
    {a t : E → ℝ} {z : E} (ha : ContinuousAt a z) (ht : ContinuousAt t z)
    (ha0 : a z ≠ 0) (ht0 : t z = 0) :
    ContinuousAt (fun y ↦ Normalized.cotFactor (a y) (t y)) z := by
  have hangle : ContinuousAt (fun y ↦ a y * t y) z := ha.fun_mul ht
  have hsin : ContinuousAt (fun y ↦ a y * Real.sinc (a y * t y)) z :=
    ha.fun_mul (Real.continuous_sinc.continuousAt.comp hangle)
  have hden : a z * Real.sinc (a z * t z) ≠ 0 := by
    simpa only [ht0, mul_zero, Real.sinc_zero, mul_one] using ha0
  simpa only [Normalized.cotFactor_def, Normalized.sinFactor_def,
    Normalized.stageAngle_def, Function.comp_def] using
      (Real.continuous_cos.continuousAt.comp hangle).div₀ hsin hden

/-- Helper for lem:polar-continuation: the normalized secant scalar is continuous through zero
scale. -/
theorem stageSigmaAlong_continuousAt {E : Type*} [TopologicalSpace E]
    {a t ζ η : E → ℝ} {X : E → ℝ × ℝ × ℝ} {z : E}
    (ha : ContinuousAt a z) (ht : ContinuousAt t z) (hX : ContinuousAt X z)
    (hζ : ContinuousAt ζ z) (hη : ContinuousAt η z)
    (ha0 : a z ≠ 0) (ht0 : t z = 0) (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ Normalized.stageSigma (a y) (t y) (X y) (ζ y) (η y)) z := by
  have hslope := slopeAlong_continuousAt hX hC
  have hcot := cotFactorAlong_continuousAt ha ht ha0 ht0
  simp only [Normalized.stageSigma_def, Normalized.stepV_def, Normalized.stepW_def,
    dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  fun_prop

/-- Helper for lem:polar-continuation: the exact normalized radius is continuous on regular
state germs. -/
theorem normalizedRadiusAlong_continuousAt {E : Type*} [TopologicalSpace E]
    {a t : E → ℝ} {X : E → ℝ × ℝ × ℝ} {z : E}
    (ha : ContinuousAt a z) (ht : ContinuousAt t z) (hX : ContinuousAt X z)
    (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ normalizedRadius (a y) (t y) (X y)) z := by
  have hslope := slopeAlong_continuousAt hX hC
  simp only [normalizedRadius, Normalized.stageAngle_def]
  fun_prop

/-- Helper for lem:polar-continuation: the actual source first stage is jointly analytic
at the initial even state. -/
theorem firstStage_analyticAt (p : Parameters) (hβ : 0 < p.beta) :
    AnalyticAt ℝ (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
      firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential y.1.1 y.1.2 y.2)
      ((0, 0), p.initialState) := by
  have hfirst : p.initialState.1 = p.gammaStar := by
    rw [p.initialState_def, cycleState_apply]
  have hφ : AnalyticAt ℝ p.feedbackPotential p.initialState.1 := by
    rw [hfirst]
    exact p.feedbackPotential_analyticAt hβ
  have ha0 : p.evenAngleFactor 0 ≠ 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  exact Normalized.evenStage_analyticAt _ _ _ _ p.evenAngleFactor_analyticAt hφ ha0
    p.initial_reference_positive.1.ne'

/-- Helper for lem:polar-continuation: normalized positivity and uniformly positive stage
denominators and radius factors for one complete source cycle. -/
structure RegularCycle (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) : Prop where
  even_regular : regularState x
  odd_regular : regularState (firstStage aE aO φ t v x)
  evenAngle_pos : 0 < aE v
  oddAngle_pos : 0 < aO v
  evenSigma_lower : (1 : ℝ) / 2 ≤
    Normalized.stageSigma (aE v) t x 1 (Normalized.feedback φ v x.1)
  oddSigma_lower : (1 : ℝ) / 2 ≤
    Normalized.stageSigma (aO v) t (firstStage aE aO φ t v x)
      (Normalized.feedback φ v x.1) 1
  evenRadius_lower : (1 : ℝ) / 2 ≤ normalizedRadius (aE v) t x
  oddRadius_lower : (1 : ℝ) / 2 ≤ normalizedRadius (aO v) t (firstStage aE aO φ t v x)

/-- Helper for lem:polar-continuation: a fixed neighborhood of the actual even base state
keeps both stages positive and their radius and secant factors bounded below by `1/2`. -/
theorem eventually_regularCycle (p : Parameters) (hβ : 0 < p.beta) :
    ∀ᶠ y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) in 𝓝 ((0, 0), p.initialState),
      RegularCycle p.evenAngleFactor p.oddAngleFactor p.feedbackPotential y.1.1 y.1.2 y.2 := by
  have ht : ContinuousAt (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ y.1.1)
      ((0, 0), p.initialState) := by fun_prop
  have hv : ContinuousAt (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ y.1.2)
      ((0, 0), p.initialState) := by fun_prop
  have hX : ContinuousAt (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ y.2)
      ((0, 0), p.initialState) := continuousAt_snd
  have haE := p.evenAngleFactor_analyticAt.continuousAt.comp_of_eq hv rfl
  have haO := p.oddAngleFactor_analyticAt.continuousAt.comp_of_eq hv rfl
  have hy := (firstStage_analyticAt p hβ).continuousAt
  have hfirst : p.initialState.1 = p.gammaStar := by
    rw [p.initialState_def, cycleState_apply]
  have hφ : ContinuousAt
      (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ p.feedbackPotential y.2.1)
      ((0, 0), p.initialState) :=
    (p.feedbackPotential_analyticAt hβ).continuousAt.comp_of_eq (continuousAt_fst.comp hX) hfirst
  have hfb : ContinuousAt
      (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦
        Normalized.feedback p.feedbackPotential y.1.2 y.2.1) ((0, 0), p.initialState) := by
    simp only [Normalized.feedback_def]
    fun_prop
  have hC := p.initial_reference_positive.1.ne'
  have hCO : (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
      0 0 p.initialState).2.1 ≠ 0 := by
    rw [firstStage_initialState p hβ]
    exact p.initial_reference_positive.2.ne'
  have haE0 : p.evenAngleFactor 0 ≠ 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  have haO0 : p.oddAngleFactor 0 ≠ 0 := by
    rw [p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos.ne'
  have hσE := stageSigmaAlong_continuousAt (ζ := fun _ ↦ (1 : ℝ))
    haE ht hX continuousAt_const hfb haE0 rfl hC
  have hσO := stageSigmaAlong_continuousAt (η := fun _ ↦ (1 : ℝ))
    haO ht hy hfb continuousAt_const haO0 rfl hCO
  have hrE := normalizedRadiusAlong_continuousAt haE ht hX hC
  have hrO := normalizedRadiusAlong_continuousAt haO ht hy hCO
  have hσE0 : (1 : ℝ) / 2 < Normalized.stageSigma (p.evenAngleFactor 0) 0
      p.initialState 1 (Normalized.feedback p.feedbackPotential 0 p.initialState.1) := by
    rw [Normalized.feedback_zero, stageSigma_zero_unit]
    norm_num
  have hσO0 : (1 : ℝ) / 2 < Normalized.stageSigma (p.oddAngleFactor 0) 0
      (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 p.initialState)
      (Normalized.feedback p.feedbackPotential 0 p.initialState.1) 1 := by
    rw [Normalized.feedback_zero, stageSigma_zero_unit]
    norm_num
  have hrE0 : (1 : ℝ) / 2 < normalizedRadius (p.evenAngleFactor 0) 0 p.initialState := by
    rw [normalizedRadius_zero]
    norm_num
  have hrO0 : (1 : ℝ) / 2 < normalizedRadius (p.oddAngleFactor 0) 0
      (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 p.initialState) := by
    rw [normalizedRadius_zero]
    norm_num
  have hangleE : 0 < p.evenAngleFactor 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos
  have hangleO : 0 < p.oddAngleFactor 0 := by
    rw [p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos
  have hoddRegular : regularState
      (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 p.initialState) := by
    rw [firstStage_initialState p hβ]
    exact regularState_oddReference p
  filter_upwards
    [DFP.Polar.StageFeasibility.eventually_regularState hX (regularState_initialState p),
    DFP.Polar.StageFeasibility.eventually_regularState hy hoddRegular,
    haE.eventually (eventually_gt_nhds hangleE), haO.eventually (eventually_gt_nhds hangleO),
    hσE.eventually (eventually_gt_nhds hσE0), hσO.eventually (eventually_gt_nhds hσO0),
    hrE.eventually (eventually_gt_nhds hrE0), hrO.eventually (eventually_gt_nhds hrO0)] with
      y hregular hodd hangleEven hangleOdd hsecEven hsecOdd hradEven hradOdd
  exact ⟨hregular, hodd, hangleEven, hangleOdd,
    hsecEven.le, hsecOdd.le, hradEven.le, hradOdd.le⟩

/-- Helper for lem:polar-continuation: the fixed fast norm satisfies the triangle inequality. -/
theorem fixedNorm_add_le (ell z : ℝ) (u v : Fin 2 → ℝ) :
    fixedNorm ell z (u + v) ≤ fixedNorm ell z u + fixedNorm ell z v := by
  simp only [fixedNorm_eq_norm, map_add]
  exact norm_add_le _ _

/-- Helper for lem:polar-continuation: the fixed fast norm is bounded by its embedding operator
norm. -/
theorem fixedNorm_le_operator (ell z : ℝ) (u : Fin 2 → ℝ) :
    fixedNorm ell z u ≤ ‖fixedEmbeddingOperator ell z‖ * ‖u‖ := by
  rw [fixedNorm_eq_norm]
  exact (fixedEmbeddingOperator ell z).le_opNorm u

/-- Helper for lem:polar-continuation: a Lipschitz reference curve makes recentered fast
errors Lipschitz in the whole normalized state. -/
theorem fixedNorm_fastError_sub_le (p : Parameters) {L : NNReal} {s : Set ℝ}
    (hLip : LipschitzOnWith L p.evenReference s) (y z : ℝ × ℝ × ℝ)
    (hy : y.1 ∈ s) (hz : z.1 ∈ s) :
    fixedNorm p.ell p.z (fastError p y - fastError p z) ≤
      ((‖fixedEmbeddingOperator p.ell p.z‖ + 1) * (1 + (L : ℝ))) * ‖y - z‖ := by
  have hcurve := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hy hz
  have hslow : ‖y.1 - z.1‖ ≤ ‖y - z‖ := norm_fst_le (y - z)
  have hcurveBound : ‖p.evenReference y.1 - p.evenReference z.1‖ ≤ (L : ℝ) * ‖y - z‖ :=
    hcurve.trans (mul_le_mul_of_nonneg_left hslow L.coe_nonneg)
  have hid : fastError p y - fastError p z =
      DFP.Polar.FastRemainder.fastProjection (y - z) -
        DFP.Polar.FastRemainder.fastProjection (p.evenReference y.1 - p.evenReference z.1) := by
    simp only [fastError_def, evenFastReference_apply,
      ← DFP.Polar.FastRemainder.fastProjection_apply, map_sub]
    abel
  have hnorm : ‖fastError p y - fastError p z‖ ≤ (1 + (L : ℝ)) * ‖y - z‖ := by
    rw [hid]
    calc
      ‖DFP.Polar.FastRemainder.fastProjection (y - z) -
          DFP.Polar.FastRemainder.fastProjection (p.evenReference y.1 - p.evenReference z.1)‖ ≤
        ‖DFP.Polar.FastRemainder.fastProjection (y - z)‖ +
          ‖DFP.Polar.FastRemainder.fastProjection (p.evenReference y.1 - p.evenReference z.1)‖ :=
        norm_sub_le _ _
      _ ≤ ‖y - z‖ + ‖p.evenReference y.1 - p.evenReference z.1‖ :=
        add_le_add (DFP.Polar.FastRemainder.norm_fastProjection_le _)
          (DFP.Polar.FastRemainder.norm_fastProjection_le _)
      _ ≤ (1 + (L : ℝ)) * ‖y - z‖ := by linarith
  calc
    fixedNorm p.ell p.z (fastError p y - fastError p z) ≤
        ‖fixedEmbeddingOperator p.ell p.z‖ * ‖fastError p y - fastError p z‖ :=
      fixedNorm_le_operator _ _ _
    _ ≤ ‖fixedEmbeddingOperator p.ell p.z‖ * ((1 + (L : ℝ)) * ‖y - z‖) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ (‖fixedEmbeddingOperator p.ell p.z‖ + 1) * ((1 + (L : ℝ)) * ‖y - z‖) := by
      have hnonneg : 0 ≤ (1 + (L : ℝ)) * ‖y - z‖ := by positivity
      nlinarith
    _ = ((‖fixedEmbeddingOperator p.ell p.z‖ + 1) * (1 + (L : ℝ))) * ‖y - z‖ := by ring

/-- Helper for lem:polar-continuation: the zero-parameter map's recentered fast error is
the actual general leading-cycle error. -/
theorem fastError_parameterMap_zero (p : Parameters) (hβ : 0 < p.beta)
    (x : ℝ × ℝ × ℝ) :
    fastError p (Estimates.parameterMap p x 0) =
      leadingCycle p.deltaEven p.deltaOdd x.1 (fastCoordinates x) - evenFastReference p x.1 := by
  rw [fastError_def, Estimates.parameterMap_zero_first]
  simp only [Estimates.parameterMap_apply, Prod.fst_zero, Prod.snd_zero]
  rw [Normalized.map_apply, Normalized.rescale_zero, Normalized.twoStep_zero,
    p.evenAngleFactor_zero hβ, p.oddAngleFactor_zero hβ,
    Parameters.leadingStage_eq_original, Parameters.leadingStage_eq_original,
    ← leadingCycle_fastCoordinates]

/-- Helper for eq:polar-slow-drift: the source scalar residual is exactly the restoring
linear-map residual for the slow displacement. -/
theorem slowError_residual (p : Parameters) (x y : ℝ × ℝ × ℝ) (v : ℝ) :
    slowError p y - (1 - (2 / (1 + p.beta)) * v) * slowError p x =
      y.1 - x.1 - v * (-2 * (x.1 - p.gammaStar) / (1 + p.beta)) := by
  rw [slowError_def, slowError_def]
  ring

/-- Helper for lem:polar-continuation: the concrete source cycle at a separately selected
starting index. -/
def stateAt (p : Parameters) (j0 j : ℕ) : ℝ × ℝ × ℝ :=
  (p.withStartIndex j0).normalizedEvenState j

/-- Helper for lem:polar-continuation: selecting the starting index retains the actual
trajectory. -/
theorem stateAt_def (p : Parameters) (j0 j : ℕ) :
    stateAt p j0 j = (p.withStartIndex j0).normalizedEvenState j := by
  rfl

/-- Helper for lem:polar-continuation: the initial state is independent of the chosen starting
index. -/
theorem stateAt_zero (p : Parameters) (j0 : ℕ) : stateAt p j0 0 = p.initialState := by
  rw [stateAt_def, Parameters.normalizedEvenState_zero]
  exact (p.withStartIndex_referenceData j0).2.2.2

/-- Helper for lem:polar-continuation: the concrete shifted trajectory follows the same
fixed source map at its prescribed real-power scales. -/
theorem stateAt_succ (p : Parameters) (j0 j : ℕ) :
    stateAt p j0 (j + 1) =
      Estimates.parameterMap p (stateAt p j0 j)
        (scale p.beta j0 j, (((j0 + j : ℕ) : ℝ))⁻¹) := by
  have hd := p.withStartIndex_analyticData j0
  rw [stateAt_def, Parameters.normalizedEvenState_succ, Parameters.normalizedStep_apply,
    Parameters.scale_def, Parameters.inverseIndex_def, p.withStartIndex_beta,
    p.withStartIndex_startIndex, hd.1, hd.2.1, hd.2.2, Estimates.parameterMap_apply]
  rfl

/-- Helper for lem:polar-continuation: one common index threshold makes both independent
small parameters uniformly small at every subsequent source cycle. -/
theorem exists_smallParameter_threshold {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j0 : ℕ, J ≤ j0 → ∀ j : ℕ,
      ‖(scale β j0 j, (((j0 + j : ℕ) : ℝ))⁻¹)‖ < ε := by
  have ht := scale_tendsto_zero hβ 0
  have hv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpair := ht.prodMk_nhds hv
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hpair.eventually (Metric.ball_mem_nhds _ hε))
  refine ⟨J, ?_⟩
  intro j0 hj0 j
  have h := hJ (j0 + j) (hj0.trans (Nat.le_add_right j0 j))
  simpa only [scale_def, Nat.zero_add, Prod.dist_eq, Real.dist_eq, sub_zero,
    Prod.norm_mk, Real.norm_eq_abs] using h

/-- Helper for lem:polar-continuation: concrete local source estimates on a fixed slow-fast
box and independent small parameters. -/
structure LocalCycleBounds (p : Parameters) (C r ρ ε : ℝ) : Prop where
  fast_bound : ∀ x : ℝ × ℝ × ℝ, ∀ t v : ℝ,
    |slowError p x| ≤ r → fastSize p x ≤ ρ → ‖(t, v)‖ < ε →
    fastSize p (Estimates.parameterMap p x (t, v)) ≤
      fixedFactor p.ell p.z * fastSize p x + C * (|v| + t ^ 2) + C * fastSize p x ^ 2
  slow_bound : ∀ x : ℝ × ℝ × ℝ, ∀ t v : ℝ,
    |slowError p x| ≤ r → fastSize p x ≤ ρ → ‖(t, v)‖ < ε →
    |slowError p (Estimates.parameterMap p x (t, v)) -
        (1 - (2 / (1 + p.beta)) * v) * slowError p x| ≤
      C * (|v| * fastSize p x + v ^ 2 + t ^ 2)
  regular : ∀ x : ℝ × ℝ × ℝ, ∀ t v : ℝ,
    |slowError p x| ≤ r → fastSize p x ≤ ρ → ‖(t, v)‖ < ε →
    RegularCycle p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x

/-- Helper for lem:polar-continuation: the actual source map satisfies the fast contraction,
exact restoring scalar drift and stage feasibility on one fixed neighborhood. -/
theorem exists_localCycleBounds (p : Parameters) (hβ : 0 < p.beta) :
    ∃ C > 0, ∃ r > 0, ∃ ρ > 0, ∃ ε > 0, LocalCycleBounds p C r ρ ε := by
  obtain ⟨rP, hrP, CP, hCP, εP, hεP, hparameter⟩ :=
    Estimates.exists_sourceMap_parameter_bound p hβ
  obtain ⟨rS, hrS, ρS, hρS, CS, hCS, εS, hεS, hscalar⟩ :=
    Estimates.exists_sourceMap_scalar_bound p hβ
  obtain ⟨ρC, hρC, hcontraction⟩ := exists_uniform_reference_contraction p
  obtain ⟨η, hη, hcontractNear⟩ := Metric.eventually_nhds_iff.mp hcontraction
  obtain ⟨L, S, hS, hLip⟩ := p.evenReference_analyticAt.hasStrictFDerivAt.exists_lipschitzOnWith
  have hfirst : p.initialState.1 = p.gammaStar := by rw [p.initialState_def, cycleState_apply]
  have hmap : ContinuousAt
      (fun y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ Estimates.parameterMap p y.2 y.1)
      ((0, 0), p.initialState) :=
    (Estimates.parameterMap_joint_analyticAt p hβ).continuousAt.comp_of_eq
      (continuousAt_snd.prodMk continuousAt_fst) rfl
  have hinputMem : S ∈ 𝓝 p.initialState.1 := by rwa [hfirst]
  have houtputMem : S ∈ 𝓝 (Estimates.parameterMap p p.initialState 0).1 := by
    rwa [Estimates.parameterMap_zero_first, hfirst]
  have hin : ∀ᶠ y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) in 𝓝 ((0, 0), p.initialState), y.2.1 ∈ S :=
    (continuousAt_fst.comp continuousAt_snd).eventually hinputMem
  have hout : ∀ᶠ y : (ℝ × ℝ) × (ℝ × ℝ × ℝ) in 𝓝 ((0, 0), p.initialState),
      (Estimates.parameterMap p y.2 y.1).1 ∈ S :=
    (continuousAt_fst.comp hmap).eventually houtputMem
  have hneigh := hin.and (hout.and (eventually_regularCycle p hβ))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hneigh
  let R := min rP (δ / 2)
  have hR : 0 < R := lt_min hrP (half_pos hδ)
  obtain ⟨r0, hr0, ρ0, hρ0, hstate⟩ :=
    exists_tube_sub_neighborhood p (Metric.ball_mem_nhds p.initialState hR)
  let r := min r0 (min rS (η / 2))
  let ρ := min ρ0 (min ρS (ρC / 2))
  let ε := min εP (min εS (δ / 2))
  let D := (‖fixedEmbeddingOperator p.ell p.z‖ + 1) * (1 + (L : ℝ))
  let C := D * CP + CS + 1
  have hr : 0 < r := lt_min hr0 (lt_min hrS (half_pos hη))
  have hρ : 0 < ρ := lt_min hρ0 (lt_min hρS (half_pos hρC))
  have hε : 0 < ε := lt_min hεP (lt_min hεS (half_pos hδ))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCPle : D * CP ≤ C := by
    dsimp [C]
    linarith
  have hCSle : CS ≤ C := by
    dsimp [C]
    linarith [mul_pos hD hCP]
  have hstep : ∀ x : ℝ × ℝ × ℝ, ∀ t v : ℝ,
      |slowError p x| ≤ r → fastSize p x ≤ ρ → ‖(t, v)‖ < ε →
      fastSize p (Estimates.parameterMap p x (t, v)) ≤
          fixedFactor p.ell p.z * fastSize p x + C * (|v| + t ^ 2) + C * fastSize p x ^ 2 ∧
        |slowError p (Estimates.parameterMap p x (t, v)) -
            (1 - (2 / (1 + p.beta)) * v) * slowError p x| ≤
          C * (|v| * fastSize p x + v ^ 2 + t ^ 2) ∧
        RegularCycle p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x := by
    intro x t v hxslow hxfast htv
    have hxslow0 : |slowError p x| ≤ r0 := hxslow.trans (min_le_left _ _)
    have hxfast0 : fastSize p x ≤ ρ0 := hxfast.trans (min_le_left _ _)
    have hxball := hstate x hxslow0 hxfast0
    have hxR : ‖x - p.initialState‖ < R := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hxball
    have hxP : ‖x - p.initialState‖ ≤ rP := hxR.le.trans (min_le_left _ _)
    have hxδ : ‖x - p.initialState‖ < δ :=
      (hxR.trans_le (min_le_right _ _)).trans (half_lt_self hδ)
    have htvδ : ‖(t, v)‖ < δ :=
      (htv.trans_le ((min_le_right εP _).trans (min_le_right εS _))).trans (half_lt_self hδ)
    have hdist : dist ((t, v), x) ((0, 0), p.initialState) < δ := by
      have htvDist : dist (t, v) ((0, 0) : ℝ × ℝ) < δ := by
        simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, Prod.norm_mk,
          Real.norm_eq_abs] using htvδ
      have hxDist : dist x p.initialState < δ := by rwa [dist_eq_norm]
      rw [Prod.dist_eq]
      exact max_lt htvDist hxDist
    have hregular := hδbound hdist
    have hzS : (Estimates.parameterMap p x 0).1 ∈ S := by
      rw [Estimates.parameterMap_zero_first]
      exact hregular.1
    have hparam := hparameter x hxP t v (htv.trans_le (min_le_left _ _))
    have hdiff := fixedNorm_fastError_sub_le p hLip
      (Estimates.parameterMap p x (t, v)) (Estimates.parameterMap p x 0) hregular.2.1 hzS
    have hdiffBound : fixedNorm p.ell p.z
        (fastError p (Estimates.parameterMap p x (t, v)) -
          fastError p (Estimates.parameterMap p x 0)) ≤
        D * CP * (|v| + t ^ 2) := by
      have h := hdiff.trans (mul_le_mul_of_nonneg_left hparam hD.le)
      simpa only [D, mul_assoc] using h
    have hxη : dist x.1 p.gammaStar < η := by
      rw [Real.dist_eq, ← slowError_def]
      have h := hxslow.trans ((min_le_right r0 _).trans (min_le_right rS _))
      linarith
    have huC : fixedNorm p.ell p.z (fastError p x) < ρC := by
      have h := hxfast.trans ((min_le_right ρ0 _).trans (min_le_right ρS _))
      exact h.trans_lt (half_lt_self hρC)
    have hleading := hcontractNear hxη (fastError p x) huC
    have hzero : fastSize p (Estimates.parameterMap p x 0) ≤
        fixedFactor p.ell p.z * fastSize p x := by
      rw [fastSize_def, fastError_parameterMap_zero p hβ, ← reference_add_fastError p x]
      exact hleading
    have hfast : fastSize p (Estimates.parameterMap p x (t, v)) ≤
        fixedFactor p.ell p.z * fastSize p x + C * (|v| + t ^ 2) + C * fastSize p x ^ 2 := by
      have hid : fastError p (Estimates.parameterMap p x (t, v)) =
          fastError p (Estimates.parameterMap p x 0) +
            (fastError p (Estimates.parameterMap p x (t, v)) -
          fastError p (Estimates.parameterMap p x 0)) := by
        abel
      have htriangle := fixedNorm_add_le p.ell p.z
        (fastError p (Estimates.parameterMap p x 0))
        (fastError p (Estimates.parameterMap p x (t, v)) -
          fastError p (Estimates.parameterMap p x 0))
      rw [← hid] at htriangle
      have htriangleSize : fastSize p (Estimates.parameterMap p x (t, v)) ≤
          fastSize p (Estimates.parameterMap p x 0) +
            fixedNorm p.ell p.z (fastError p (Estimates.parameterMap p x (t, v)) -
              fastError p (Estimates.parameterMap p x 0)) := htriangle
      have hboost := mul_le_mul_of_nonneg_right hCPle (add_nonneg (abs_nonneg v) (sq_nonneg t))
      have hquad := mul_nonneg hC.le (sq_nonneg (fastSize p x))
      linarith [htriangleSize]
    have hxS : |x.1 - p.gammaStar| ≤ rS := by
      simpa only [slowError_def] using
        hxslow.trans ((min_le_right r0 _).trans (min_le_left _ _))
    have hnormu : ‖x - p.evenReference x.1‖ ≤ fastSize p x := norm_state_sub_evenReference_le p x
    have hnormS : ‖x - p.evenReference x.1‖ ≤ ρS :=
      hnormu.trans (hxfast.trans ((min_le_right ρ0 _).trans (min_le_left _ _)))
    have hs := hscalar x.1 hxS x rfl hnormS t v
      (htv.trans_le ((min_le_right εP _).trans (min_le_left _ _)))
    rw [← slowError_residual] at hs
    have hterm : |v| * ‖x - p.evenReference x.1‖ + v ^ 2 + t ^ 2 ≤
        |v| * fastSize p x + v ^ 2 + t ^ 2 := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hnormu (abs_nonneg v)) le_rfl) le_rfl
    have hslow := hs.trans (mul_le_mul_of_nonneg_left hterm hCS.le)
    have hforcing : 0 ≤ |v| * fastSize p x + v ^ 2 + t ^ 2 :=
      add_nonneg (add_nonneg (mul_nonneg (abs_nonneg v) (fastSize_nonneg p x))
        (sq_nonneg v)) (sq_nonneg t)
    exact ⟨hfast, hslow.trans (mul_le_mul_of_nonneg_right hCSle hforcing), hregular.2.2⟩
  refine ⟨C, hC, r, hr, ρ, hρ, ε, hε, ?_⟩
  constructor
  · intro x t v hx hu hsmall
    exact (hstep x t v hx hu hsmall).1
  · intro x t v hx hu hsmall
    exact (hstep x t v hx hu hsmall).2.1
  · intro x t v hx hu hsmall
    exact (hstep x t v hx hu hsmall).2.2

/-- Helper for lem:polar-continuation: bounds and stage feasibility for the actual
trajectory at one chosen starting index. -/
structure TrajectoryBounds (p : Parameters) (j0 : ℕ) (N M : ℝ) : Prop where
  fast_bound : ∀ j : ℕ, fastSize p (stateAt p j0 j) ≤ N / ((j0 + j : ℕ) : ℝ)
  slow_bound : ∀ j : ℕ,
    |slowError p (stateAt p j0 j)| ≤ M * scale p.beta j0 j ^ (1 - p.beta)
  regular : ∀ j : ℕ,
    RegularCycle p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
      (scale p.beta j0 j) (((j0 + j : ℕ) : ℝ))⁻¹ (stateAt p j0 j)

/-- Helper for lem:polar-continuation: the proved local source estimates preserve the actual
recursive trajectory, with all widths fixed before the starting index. -/
theorem LocalCycleBounds.existsTrajectoryBounds {p : Parameters} {C r ρ ε : ℝ}
    (hlocal : LocalCycleBounds p C r ρ ε) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    (hC : 0 < C) (hr : 0 < r) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧
      ∀ j0 : ℕ, J ≤ j0 → TrajectoryBounds p j0 N M := by
  have hq := fixedFactor_bounds p.base.stable
  obtain ⟨N, hN, _, M, hM, _, J0, hJ0, htube⟩ :=
    TubeBounds.existsInvariantTubeConstants hβ hβone hq.1.le hq.2 hC.le
      (fun N ↦ C * (N + 2)) r ρ hr hρ
  obtain ⟨J1, hsmall⟩ := exists_smallParameter_threshold hβ hε
  refine ⟨N, hN, M, hM, max J0 J1, hJ0.trans_le (le_max_left _ _), ?_⟩
  intro j0 hj0
  have hj00 : J0 ≤ j0 := (le_max_left _ _).trans hj0
  have hj01 : J1 ≤ j0 := (le_max_right _ _).trans hj0
  have hstart : 0 < j0 := hJ0.trans_le hj00
  obtain ⟨hinside, hinduction⟩ := htube j0 hj00
  let u : ℕ → ℝ := fun j ↦ fastSize p (stateAt p j0 j)
  let b : ℕ → ℝ := fun j ↦ slowError p (stateAt p j0 j)
  have hu : ∀ j : ℕ, 0 ≤ u j := fun j ↦ fastSize_nonneg p (stateAt p j0 j)
  have hu0 : u 0 ≤ N / ((j0 + 0 : ℕ) : ℝ) := by
    dsimp only [u]
    rw [stateAt_zero, fastSize_initialState]
    positivity
  have hb0 : |b 0| ≤ M * scale p.beta j0 0 ^ (1 - p.beta) := by
    dsimp only [b]
    rw [stateAt_zero, slowError_initialState, abs_zero]
    exact mul_nonneg hM.le (Real.rpow_nonneg (scale_nonneg p.beta j0 0) _)
  have hfast : ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
      |b j| ≤ M * scale p.beta j0 j ^ (1 - p.beta) →
      u (j + 1) ≤ fixedFactor p.ell p.z * u j +
        C * (1 / ((j0 + j : ℕ) : ℝ) + scale p.beta j0 j ^ 2) + C * u j ^ 2 := by
    intro j huj hbj
    have hv : 0 ≤ (((j0 + j : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h := hlocal.fast_bound (stateAt p j0 j) (scale p.beta j0 j)
      (((j0 + j : ℕ) : ℝ))⁻¹ (hbj.trans (hinside j).2) (huj.trans (hinside j).1)
      (hsmall j0 hj01 j)
    rw [← stateAt_succ] at h
    simpa only [u, one_div, abs_of_nonneg hv] using h
  have hslow : ∀ j : ℕ, u j ≤ N / ((j0 + j : ℕ) : ℝ) →
      |b j| ≤ M * scale p.beta j0 j ^ (1 - p.beta) →
      |b (j + 1) - (1 - (2 / (1 + p.beta)) / ((j0 + j : ℕ) : ℝ)) * b j| ≤
        (C * (N + 2)) * scale p.beta j0 j ^ 2 := by
    intro j huj hbj
    have hv : 0 ≤ (((j0 + j : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h := hlocal.slow_bound (stateAt p j0 j) (scale p.beta j0 j)
      (((j0 + j : ℕ) : ℝ))⁻¹ (hbj.trans (hinside j).2) (huj.trans (hinside j).1)
      (hsmall j0 hj01 j)
    rw [← stateAt_succ, abs_of_nonneg hv] at h
    have huj' : fastSize p (stateAt p j0 j) ≤ N * (((j0 + j : ℕ) : ℝ))⁻¹ := by
      simpa only [u, div_eq_mul_inv] using huj
    have hmul := mul_le_mul_of_nonneg_left huj' hv
    have hscale := inv_sq_le_scale_sq hβ hstart j
    have hNscale := mul_le_mul_of_nonneg_left hscale hN.le
    have hforcing :
        (((j0 + j : ℕ) : ℝ))⁻¹ * fastSize p (stateAt p j0 j) +
            (((j0 + j : ℕ) : ℝ))⁻¹ ^ 2 + scale p.beta j0 j ^ 2 ≤
          (N + 2) * scale p.beta j0 j ^ 2 := by
      nlinarith
    have hbound := h.trans (mul_le_mul_of_nonneg_left hforcing hC.le)
    simpa only [b, div_eq_mul_inv, mul_assoc] using hbound
  have hall := hinduction u b hu hu0 hb0 hfast hslow
  constructor
  · intro j
    exact (hall j).1
  · intro j
    exact (hall j).2
  · intro j
    exact hlocal.regular (stateAt p j0 j) (scale p.beta j0 j)
      (((j0 + j : ℕ) : ℝ))⁻¹ ((hall j).2.trans (hinside j).2)
      ((hall j).1.trans (hinside j).1) (hsmall j0 hj01 j)

/-- Helper for lem:polar-continuation: the actual recursive
normalized matrices remain in the slow and fast tubes, and both actual stages stay
positive, for every starting index above one fixed threshold. -/
theorem existsTrajectoryBounds (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧
      ∀ j0 : ℕ, J ≤ j0 → TrajectoryBounds p j0 N M := by
  obtain ⟨C, hC, r, hr, ρ, hρ, ε, hε, hlocal⟩ := exists_localCycleBounds p hβ
  exact hlocal.existsTrajectoryBounds hβ hβone hC hr hρ hε

/-- Helper for lem:polar-continuation: trajectory feasibility uses exactly the data and scale
of the concrete shifted parameter record. -/
theorem TrajectoryBounds.regularCycle_shifted {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (j : ℕ) :
    RegularCycle (p.withStartIndex j0).evenAngleFactor (p.withStartIndex j0).oddAngleFactor
      (p.withStartIndex j0).feedbackPotential ((p.withStartIndex j0).scale j)
      ((p.withStartIndex j0).inverseIndex j) ((p.withStartIndex j0).normalizedEvenState j) := by
  have hd := p.withStartIndex_analyticData j0
  simpa only [Parameters.scale_def, Parameters.inverseIndex_def,
    p.withStartIndex_beta, p.withStartIndex_startIndex, hd.1, hd.2.1, hd.2.2, stateAt_def] using
      h.regular j

/-- Helper for lem:polar-continuation: both concrete normalized states remain in the positive
domain. -/
theorem TrajectoryBounds.normalized_regular {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (j : ℕ) :
    regularState ((p.withStartIndex j0).normalizedEvenState j) ∧
      regularState ((p.withStartIndex j0).normalizedOddState j) := by
  have hj := h.regularCycle_shifted j
  constructor
  · exact hj.even_regular
  · simpa only [firstStage_def, Parameters.normalizedOddState_apply] using hj.odd_regular

/-- Helper for lem:polar-continuation: the old and general symmetric-state interfaces coincide. -/
theorem stateMatrix_eq_legacy (x : ℝ × ℝ × ℝ) :
    PhysicalRecurrence.stateMatrix x = DFP.Polar.StageFeasibility.stateMatrix x := by
  rw [PhysicalRecurrence.stateMatrix_def, DFP.Polar.StageFeasibility.stateMatrix_def]

/-- Helper for lem:polar-continuation: the positivity and denominator conditions at one
actual physical DFP stage. -/
structure RawFeasible (p : Parameters) (k : ℕ) : Prop where
  posDef : (p.matrix k).PosDef
  offDiagonal_pos : 0 < p.matrix k 0 1
  radius_pos : 0 < p.radiusRatio k
  secant_pos : 0 < DFP.Polar.sigmaOf (p.matrix k) (p.angleIncrement k)
    (p.zeta k) (p.zeta (k + 1))
  angle_pos : 0 < p.angleIncrement k

/-- Helper for lem:polar-continuation: the proved normalized tube makes every actual
physical DFP matrix and every required stage denominator positive. -/
theorem TrajectoryBounds.rawFeasible {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hstart : 0 < j0) (k : ℕ) :
    RawFeasible (p.withStartIndex j0) k := by
  let q := p.withStartIndex j0
  have hβq : 0 < q.beta := by simpa only [q, p.withStartIndex_beta] using hβ
  have hstartq : 0 < q.startIndex := by simpa only [q, p.withStartIndex_startIndex] using hstart
  have heven : ∀ j, (PhysicalRecurrence.stateMatrix (q.normalizedEvenState j)).PosDef := by
    intro j
    rw [stateMatrix_eq_legacy]
    exact (DFP.Polar.StageFeasibility.regularState_posDef _ (h.normalized_regular j).1).1
  have hodd : ∀ j, (PhysicalRecurrence.stateMatrix (q.normalizedOddState j)).PosDef := by
    intro j
    rw [stateMatrix_eq_legacy]
    exact (DFP.Polar.StageFeasibility.regularState_posDef _ (h.normalized_regular j).2).1
  have hpos := q.matrix_posDef_of_normalized hstartq heven hodd
  have hoff := q.matrix_offDiagonal_pos_of_normalized hstartq
    (fun j ↦ (DFP.Polar.StageFeasibility.regularState_posDef _ (h.normalized_regular j).1).2)
    (fun j ↦ (DFP.Polar.StageFeasibility.regularState_posDef _ (h.normalized_regular j).2).2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hj := h.regularCycle_shifted j
    have ht : 0 < q.scale j := by
      rw [q.scale_def]
      exact General.scale_pos q.beta hstartq j
    refine ⟨hpos _, hoff _, ?_, ?_, ?_⟩
    · rw [q.radiusRatio_even_eq_normalized hβq hstartq]
      exact hhalf.trans_le hj.evenRadius_lower
    · rw [q.sigma_even_eq_normalized hβq hstartq, q.oddMultiplier_def]
      exact hhalf.trans_le hj.evenSigma_lower
    · rw [q.angleIncrement_even hβq hstartq, Normalized.stageAngle_def]
      exact mul_pos hj.evenAngle_pos ht
  · have hj := h.regularCycle_shifted j
    have ht : 0 < q.scale j := by
      rw [q.scale_def]
      exact General.scale_pos q.beta hstartq j
    refine ⟨hpos _, hoff _, ?_, ?_, ?_⟩
    · rw [q.radiusRatio_odd_eq_normalized hβq hstartq]
      have hlow := hj.oddRadius_lower
      rw [firstStage_def, ← q.normalizedOddState_apply j] at hlow
      exact hhalf.trans_le hlow
    · rw [q.sigma_odd_eq_normalized hβq hstartq, q.oddMultiplier_def]
      have hlow := hj.oddSigma_lower
      rw [firstStage_def, ← q.normalizedOddState_apply j] at hlow
      exact hhalf.trans_le hlow
    · rw [q.angleIncrement_odd hβq hstartq, Normalized.stageAngle_def]
      exact mul_pos hj.oddAngle_pos ht

/-- Helper for lem:polar-continuation: the actual normalized source tube and physical stage
feasibility hold uniformly for every sufficiently large starting index. -/
theorem existsContinuation (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      TrajectoryBounds p j0 N M ∧ ∀ k : ℕ, RawFeasible (p.withStartIndex j0) k := by
  obtain ⟨N, hN, M, hM, J, hJ, hbound⟩ := existsTrajectoryBounds p hβ hβone
  refine ⟨N, hN, M, hM, J, hJ, ?_⟩
  intro j0 hj0
  exact ⟨hbound j0 hj0, (hbound j0 hj0).rawFeasible hβ (hJ.trans_le hj0)⟩

/-- Helper for lem:polar-continuation: the real source cycle index diverges. -/
theorem index_tendsto_atTop (j0 : ℕ) :
    Tendsto (fun j : ℕ ↦ ((j0 + j : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_add, add_comm] using
    tendsto_atTop_add_const_right atTop (j0 : ℝ) tendsto_natCast_atTop_atTop

/-- Helper for lem:polar-continuation: the fast tube width tends to zero. -/
theorem TrajectoryBounds.fastSize_tendsto_zero {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) :
    Tendsto (fun j : ℕ ↦ fastSize p (stateAt p j0 j)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun j : ℕ ↦ N / ((j0 + j : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (index_tendsto_atTop j0)
  exact squeeze_zero (fun j ↦ fastSize_nonneg p _) h.fast_bound hbound

/-- Helper for lem:polar-continuation: the controlled slow coordinate tends to the selected
equilibrium. -/
theorem TrajectoryBounds.gamma_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (fun j : ℕ ↦ (stateAt p j0 j).1) atTop (𝓝 p.gammaStar) := by
  have hrpow := ((tendsto_rpow_neg_atTop (slowExponent_pos hβ hβone)).comp
    (index_tendsto_atTop j0)).const_mul M
  have hbound : Tendsto (fun j : ℕ ↦ M * scale p.beta j0 j ^ (1 - p.beta))
      atTop (𝓝 0) := by
    simpa only [scale_rpow_one_sub, mul_zero, Function.comp_def] using hrpow
  have hnorm : ∀ j : ℕ, ‖(stateAt p j0 j).1 - p.gammaStar‖ ≤
      M * scale p.beta j0 j ^ (1 - p.beta) := by
    intro j
    simpa only [Real.norm_eq_abs, slowError_def] using h.slow_bound j
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hnorm hbound)

/-- Helper for lem:polar-continuation: the full normalized even trajectory converges to its
genuine reference. -/
theorem TrajectoryBounds.evenState_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (stateAt p j0) atTop (𝓝 p.initialState) := by
  have hresidual : Tendsto
      (fun j : ℕ ↦ stateAt p j0 j - p.evenReference (stateAt p j0 j).1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j ↦ norm_state_sub_evenReference_le p _) h.fastSize_tendsto_zero
  have href := p.evenReference_analyticAt.continuousAt.tendsto.comp (h.gamma_tendsto hβ hβone)
  have hsum := hresidual.add href
  simpa only [Function.comp_def, sub_add_cancel, zero_add, p.evenReference_gammaStar] using hsum

/-- Helper for lem:polar-continuation: both independent small source parameters tend to zero. -/
theorem smallParameters_tendsto_zero (p : Parameters) (hβ : 0 < p.beta) (j0 : ℕ) :
    Tendsto (fun j : ℕ ↦ (scale p.beta j0 j, (((j0 + j : ℕ) : ℝ))⁻¹))
      atTop (𝓝 ((0, 0) : ℝ × ℝ)) := by
  exact (scale_tendsto_zero hβ j0).prodMk_nhds
    (tendsto_inv_atTop_zero.comp (index_tendsto_atTop j0))

/-- Helper for lem:polar-continuation: the full normalized odd trajectory converges to its
genuine odd reference. -/
theorem TrajectoryBounds.oddState_tendsto {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (fun j : ℕ ↦ (p.withStartIndex j0).normalizedOddState j)
      atTop (𝓝 (p.oddReference p.gammaStar)) := by
  have hinput := (smallParameters_tendsto_zero p hβ j0).prodMk_nhds
    (h.evenState_tendsto hβ hβone)
  have houtput := (firstStage_analyticAt p hβ).continuousAt.tendsto.comp hinput
  rw [firstStage_initialState p hβ] at houtput
  have hd := p.withStartIndex_analyticData j0
  simpa only [Function.comp_def, firstStage_def, firstStage_initialState p hβ,
    Parameters.normalizedOddState_apply, Parameters.scale_def, Parameters.inverseIndex_def,
    p.withStartIndex_beta, p.withStartIndex_startIndex, hd.1, hd.2.1, hd.2.2, stateAt_def]
    using houtput

/-- Helper for lem:polar-continuation: the actual intermediate exponential gradient multiplier
tends to one. -/
theorem TrajectoryBounds.oddMultiplier_tendsto_one {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (p.withStartIndex j0).oddMultiplier atTop (𝓝 1) := by
  have hgamma := h.gamma_tendsto hβ hβone
  have hphi := (p.feedbackPotential_analyticAt hβ).continuousAt.tendsto.comp hgamma
  have hv := tendsto_inv_atTop_zero.comp (index_tendsto_atTop j0)
  have hexponent := hphi.neg.mul hv
  have houtput := Real.continuous_exp.continuousAt.tendsto.comp hexponent
  have hd := p.withStartIndex_analyticData j0
  rw [funext (Parameters.oddMultiplier_def (p.withStartIndex j0))]
  simpa only [Function.comp_def, Parameters.oddMultiplier_def, Normalized.feedback_def,
    Parameters.inverseIndex_def, p.withStartIndex_startIndex, hd.2.2, stateAt_def,
    mul_zero, Real.exp_zero] using houtput

/-- Helper for lem:polar-continuation: interleaving unit even multipliers with the actual odd
feedback factors gives a complete multiplier sequence tending to one. -/
theorem TrajectoryBounds.zeta_tendsto_one {p : Parameters} {j0 : ℕ} {N M : ℝ}
    (h : TrajectoryBounds p j0 N M) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    Tendsto (p.withStartIndex j0).zeta atTop (𝓝 1) := by
  have hodd := h.oddMultiplier_tendsto_one hβ hβone
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hodd ε hε
  refine ⟨2 * J, ?_⟩
  intro k hk
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [Parameters.zeta_even]
    simpa only [dist_self] using hε
  · rw [Parameters.zeta_odd]
    have hj : J ≤ j := by omega
    exact hJ j hj

/-- Helper for lem:polar-continuation: the actual intermediate normalized matrix differs
from the odd reference by the fast error and the two small source parameters. -/
theorem exists_localOdd_bound (p : Parameters) (hβ : 0 < p.beta) :
    ∃ C > 0, ∃ r > 0, ∃ ρ > 0, ∃ ε > 0, ∀ x : ℝ × ℝ × ℝ, ∀ t v : ℝ,
      |slowError p x| ≤ r → fastSize p x ≤ ρ → ‖(t, v)‖ < ε →
      ‖firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x -
          p.oddReference x.1‖ ≤ C * (fastSize p x + |v| + t ^ 2) := by
  obtain ⟨rP, hrP, CP, hCP, ε, hε, hparameter⟩ :=
    Estimates.exists_evenStage_parameter_bound p hβ
  have hslice : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 x)
      p.initialState :=
    (firstStage_analyticAt p hβ).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  obtain ⟨L, S, hS, hLip⟩ := hslice.hasStrictFDerivAt.exists_lipschitzOnWith
  have hrefMem : ∀ᶠ γ in 𝓝 p.gammaStar, p.evenReference γ ∈ S := by
    have hlim := p.evenReference_analyticAt.continuousAt.tendsto
    rw [p.evenReference_gammaStar] at hlim
    exact hlim.eventually hS
  have hreference : ∀ᶠ γ in 𝓝 p.gammaStar,
      firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 (p.evenReference γ) =
          p.oddReference γ ∧ p.evenReference γ ∈ S := by
    filter_upwards [p.referenceCycle_eventually, hrefMem] with γ hcycle hmem
    constructor
    · simpa only [firstStage_def, Normalized.cycleStage_even, Normalized.feedback_zero,
        Normalized.stage_zero, p.evenAngleFactor_zero hβ] using hcycle.1
    · exact hmem
  obtain ⟨η, hη, hreferenceNear⟩ := Metric.eventually_nhds_iff.mp hreference
  obtain ⟨r0, hr0, ρ, hρ, hstate⟩ := exists_tube_sub_neighborhood p
    (inter_mem hS (Metric.ball_mem_nhds p.initialState hrP))
  let C := CP + (L : ℝ) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, min r0 (η / 2), lt_min hr0 (half_pos hη), ρ, hρ, ε, hε, ?_⟩
  intro x t v hx hu htv
  have hxS := hstate x (hx.trans (min_le_left _ _)) hu
  have hxP : ‖x - p.initialState‖ ≤ rP := by
    simpa only [dist_eq_norm] using (Metric.mem_ball.mp hxS.2).le
  have hγ : dist x.1 p.gammaStar < η := by
    rw [Real.dist_eq, ← slowError_def]
    have h := hx.trans (min_le_right _ _)
    linarith
  have href := hreferenceNear hγ
  have hparam := hparameter x hxP t v htv
  have hlead := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hxS.1 href.2
  rw [href.1] at hlead
  have hleadBound :
      ‖firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 x -
          p.oddReference x.1‖ ≤
        (L : ℝ) * fastSize p x :=
    hlead.trans (mul_le_mul_of_nonneg_left (norm_state_sub_evenReference_le p x) L.coe_nonneg)
  have hparamBound :
      ‖firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x -
          firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 x‖ ≤
        CP * (|v| + t ^ 2) := hparam
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x)
    (firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential 0 0 x) (p.oddReference x.1)
  have hCPle : CP ≤ C := by
    dsimp [C]
    linarith [L.coe_nonneg]
  have hLle : (L : ℝ) ≤ C := by
    dsimp [C]
    linarith
  have hforcing := mul_le_mul_of_nonneg_right hCPle (add_nonneg (abs_nonneg v) (sq_nonneg t))
  have hfast := mul_le_mul_of_nonneg_right hLle (fastSize_nonneg p x)
  nlinarith

/-- Helper for lem:polar-continuation: fixed source tube barriers enter any smaller slow-fast
box uniformly once the common index is sufficiently large. -/
theorem exists_barrier_threshold {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (N M r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    ∃ J : ℕ, ∀ j0 : ℕ, J ≤ j0 → ∀ j : ℕ,
      N / ((j0 + j : ℕ) : ℝ) ≤ ρ ∧ M * scale β j0 j ^ (1 - β) ≤ r := by
  have hfast : Tendsto (fun n : ℕ ↦ N / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hslow : Tendsto (fun n : ℕ ↦ M * (n : ℝ) ^ (-slowExponent β)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (slowExponent_pos hβ hβone)).comp
        tendsto_natCast_atTop_atTop).const_mul M
  have hevent : ∀ᶠ n : ℕ in atTop,
      N / (n : ℝ) ≤ ρ ∧ M * (n : ℝ) ^ (-slowExponent β) ≤ r := by
    filter_upwards [hfast.eventually (Iio_mem_nhds hρ), hslow.eventually (Iio_mem_nhds hr)] with
      n hnfast hnslow
    exact ⟨hnfast.le, hnslow.le⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
  refine ⟨J, ?_⟩
  intro j0 hj0 j
  simpa only [scale_rpow_one_sub] using hJ (j0 + j) (hj0.trans (Nat.le_add_right j0 j))

/-- Helper for lem:polar-continuation: the actual odd state is the first source stage of
the shifted even trajectory. -/
theorem oddState_eq_firstStage (p : Parameters) (j0 j : ℕ) :
    (p.withStartIndex j0).normalizedOddState j =
      firstStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
        (scale p.beta j0 j) (((j0 + j : ℕ) : ℝ))⁻¹ (stateAt p j0 j) := by
  have hd := p.withStartIndex_analyticData j0
  rw [Parameters.normalizedOddState_apply, firstStage_def, Parameters.scale_def,
    Parameters.inverseIndex_def, p.withStartIndex_beta, p.withStartIndex_startIndex,
    hd.1, hd.2.1, hd.2.2, stateAt_def]

/-- lem:polar-continuation. Both normalized phases have the source's uniform
`O(1/n)` transverse error, together with the actual slow tube and physical feasibility. -/
theorem existsContinuationEstimates (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ K > 0, ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 →
      TrajectoryBounds p j0 N M ∧ (∀ k : ℕ, RawFeasible (p.withStartIndex j0) k) ∧
        ∀ j : ℕ,
          ‖(p.withStartIndex j0).normalizedOddState j - p.oddReference (stateAt p j0 j).1‖ ≤
            K / ((j0 + j : ℕ) : ℝ) := by
  obtain ⟨CO, hCO, rO, hrO, ρO, hρO, εO, hεO, hodd⟩ := exists_localOdd_bound p hβ
  obtain ⟨N, hN, M, hM, J0, hJ0, hcontinuation⟩ := existsContinuation p hβ hβone
  obtain ⟨J1, hinside⟩ := exists_barrier_threshold hβ hβone N M rO ρO hrO hρO
  obtain ⟨J2, hsmall⟩ := exists_smallParameter_threshold hβ hεO
  let K := CO * (N + 2)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨N, hN, M, hM, K, hK, max J0 (max J1 J2), hJ0.trans_le (le_max_left _ _), ?_⟩
  intro j0 hj0
  have hj00 : J0 ≤ j0 := (le_max_left _ _).trans hj0
  have hj01 : J1 ≤ j0 := (le_max_left _ _).trans ((le_max_right _ _).trans hj0)
  have hj02 : J2 ≤ j0 := (le_max_right _ _).trans ((le_max_right _ _).trans hj0)
  have hstart : 0 < j0 := hJ0.trans_le hj00
  have hbase := hcontinuation j0 hj00
  refine ⟨hbase.1, hbase.2, ?_⟩
  intro j
  have hi := hinside j0 hj01 j
  have hb := hodd (stateAt p j0 j) (scale p.beta j0 j) (((j0 + j : ℕ) : ℝ))⁻¹
    ((hbase.1.slow_bound j).trans hi.2) ((hbase.1.fast_bound j).trans hi.1) (hsmall j0 hj02 j)
  have hv : 0 ≤ (((j0 + j : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [abs_of_nonneg hv, ← oddState_eq_firstStage] at hb
  have hscale : scale p.beta j0 j ^ 2 ≤ 1 / ((j0 + j : ℕ) : ℝ) := by
    simpa only [one_div] using scale_sq_le_inv hβ hβone hstart j
  have hforcing : fastSize p (stateAt p j0 j) + (((j0 + j : ℕ) : ℝ))⁻¹ +
        scale p.beta j0 j ^ 2 ≤ (N + 2) / ((j0 + j : ℕ) : ℝ) := by
    have hfast := hbase.1.fast_bound j
    simp only [div_eq_mul_inv] at hfast hscale ⊢
    nlinarith
  have hbound := hb.trans (mul_le_mul_of_nonneg_left hforcing hCO.le)
  simpa only [K, mul_div_assoc] using hbound

end DFP.Polar.General.Continuation
