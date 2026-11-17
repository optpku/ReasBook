module

public import ReasLib.Optimization.DFP.Polar.General.CycleFamily
public import ReasLib.Optimization.DFP.Polar.General.Scale
public import ReasLib.Optimization.DFP.Polar.General.Normalized

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.General

/-- Helper for lem:polar-continuation: concrete data of the general polar construction.
The strict Wolfe base is chosen before the starting index is increased. -/
structure Parameters where
  beta : ℝ
  c1 : ℝ
  c2 : ℝ
  ell : ℝ
  z : ℝ
  base : StrictWolfeBase c1 c2 ell z
  startIndex : ℕ

namespace Parameters

/-- Helper for lem:polar-continuation: the selected even angular coefficient. -/
def deltaEven (p : Parameters) : ℝ := baseDeltaEven p.ell p.z

/-- Helper for lem:polar-continuation: the selected odd angular coefficient. -/
def deltaOdd (p : Parameters) : ℝ := baseDeltaOdd p.ell p.z

/-- Helper for lem:polar-continuation: the selected normalization at the base cycle. -/
def gammaStar (p : Parameters) : ℝ := baseGamma p.ell p.z

/-- Helper for lem:polar-continuation: the analytic inverse of the rational family. -/
def inverseParameter (p : Parameters) : ℝ → ℝ := p.base.inverseParameter

/-- Helper for eq:polar-feedback: the exact source feedback potential. -/
def feedbackPotential (p : Parameters) (γ : ℝ) : ℝ :=
  p.gammaStar /
    ((1 + p.beta) * γ * p.inverseParameter γ * (1 / p.deltaEven + 1 / p.deltaOdd))

/-- Helper for eq:polar-angles: the prescribed real-power scale. -/
def scale (p : Parameters) (j : ℕ) : ℝ := General.scale p.beta p.startIndex j

/-- Helper for lem:polar-continuation: the inverse index is an independent
small parameter in the normalized map. -/
def inverseIndex (p : Parameters) (j : ℕ) : ℝ :=
  (((p.startIndex + j : ℕ) : ℝ))⁻¹

/-- Helper for eq:polar-angles: the exact unreduced even polar angle. -/
def evenAngle (p : Parameters) (j : ℕ) : ℝ :=
  (p.deltaEven + p.deltaOdd) * ((1 + p.beta) / p.beta) *
    (((p.startIndex + j : ℕ) : ℝ)) ^ (p.beta / (1 + p.beta))

/-- Helper for eq:polar-angles: the odd angle divides the full cycle in the
ratio of the selected even and odd angular coefficients. -/
def oddAngle (p : Parameters) (j : ℕ) : ℝ :=
  p.evenAngle j + p.deltaEven / (p.deltaEven + p.deltaOdd) *
    (p.evenAngle (j + 1) - p.evenAngle j)

/-- Helper for eq:polar-angles: interleaving retains unreduced real angles. -/
def angle (p : Parameters) : ℕ → ℝ :=
  DFP.twoStepSequence p.evenAngle p.oddAngle

/-- Helper for eq:polar-angles: every angle increment is the actual consecutive
difference of prescribed polar angles. -/
def angleIncrement (p : Parameters) (k : ℕ) : ℝ := p.angle (k + 1) - p.angle k

/-- Helper for lem:polar-continuation: the analytic even angle coefficient
retains the inverse index as an independent variable. -/
def evenAngleFactor (p : Parameters) (v : ℝ) : ℝ :=
  p.deltaEven * General.angleFactor p.beta v

/-- Helper for lem:polar-continuation: the analytic odd angle coefficient
retains the inverse index as an independent variable. -/
def oddAngleFactor (p : Parameters) (v : ℝ) : ℝ :=
  p.deltaOdd * General.angleFactor p.beta v

/-- Helper for eq:polar-two-cycle: the source even reference state as a function
of its first diagonal coordinate. -/
def evenReference (p : Parameters) (γ : ℝ) : ℝ × ℝ × ℝ :=
  cycleState γ (cycleLambdaEven p.deltaEven p.deltaOdd (p.inverseParameter γ))

/-- Helper for eq:polar-two-cycle: the source odd reference state as a function
of its first diagonal coordinate. -/
def oddReference (p : Parameters) (γ : ℝ) : ℝ × ℝ × ℝ :=
  cycleState γ (cycleLambdaOdd p.deltaEven p.deltaOdd (p.inverseParameter γ))

/-- Helper for eq:polar-initial-matrix: the initial normalized source matrix. -/
def initialState (p : Parameters) : ℝ × ℝ × ℝ := cycleState p.gammaStar p.ell

/-- Helper for lem:polar-continuation: one full source normalized cycle at
its prescribed scale and inverse index. -/
def normalizedStep (p : Parameters) (j : ℕ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
    (p.scale j) (p.inverseIndex j) x

/-- Helper for lem:polar-continuation: the actual normalized trajectory is
constructed by recursion, without assuming a tube or feasibility certificate. -/
def normalizedEvenState (p : Parameters) : ℕ → ℝ × ℝ × ℝ
  | 0 => p.initialState
  | j + 1 => p.normalizedStep j (p.normalizedEvenState j)

/-- Helper for lem:polar-continuation: the actual intermediate state is the
first stage, with feedback evaluated at its even boundary. -/
def normalizedOddState (p : Parameters) (j : ℕ) : ℝ × ℝ × ℝ :=
  Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
    0 (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) (p.normalizedEvenState j)

/-- Helper for lem:polar-continuation: the even physical matrix is recovered
by undoing the normalization of the actual recursively constructed state. -/
def evenMatrix (p : Parameters) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Normalized.invScaleMatrix (p.scale j) *
    RealSymmetric2.matrix (p.normalizedEvenState j).1 (p.normalizedEvenState j).2.1
      (p.normalizedEvenState j).2.2 * Normalized.invScaleMatrix (p.scale j)

/-- Helper for lem:polar-continuation: the intermediate matrix uses the same
scale as its even boundary. -/
def oddMatrix (p : Parameters) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Normalized.invScaleMatrix (p.scale j) *
    RealSymmetric2.matrix (p.normalizedOddState j).1 (p.normalizedOddState j).2.1
      (p.normalizedOddState j).2.2 * Normalized.invScaleMatrix (p.scale j)

/-- Helper for eq:polar-matrix-map: the complete local matrix sequence. -/
def matrix (p : Parameters) : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.twoStepSequence p.evenMatrix p.oddMatrix

/-- Helper for eq:polar-feedback: the intermediate gradient factor is evaluated
at the original first diagonal coordinate of the cycle. -/
def oddMultiplier (p : Parameters) (j : ℕ) : ℝ :=
  Normalized.feedback p.feedbackPotential (p.inverseIndex j) (p.normalizedEvenState j).1

/-- Helper for eq:polar-feedback: even gradients remain those of the base
quadratic and odd gradients receive the shared positive correction. -/
def zeta (p : Parameters) : ℕ → ℝ :=
  DFP.twoStepSequence (fun _ ↦ 1) p.oddMultiplier

/-- Helper for eq:polar-step-data: the exact radius ratio of every raw polar stage. -/
def radiusRatio (p : Parameters) (k : ℕ) : ℝ :=
  DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k)

/-- Helper for lem:polar-continuation: the selected even coefficient is positive. -/
theorem deltaEven_pos (p : Parameters) : 0 < p.deltaEven := p.base.deltaEven_pos

/-- Helper for lem:polar-continuation: the selected odd coefficient is positive. -/
theorem deltaOdd_pos (p : Parameters) : 0 < p.deltaOdd := p.base.deltaOdd_pos

/-- Helper for lem:polar-continuation: the selected base normalization is positive. -/
theorem gammaStar_pos (p : Parameters) : 0 < p.gammaStar := by
  simpa only [gammaStar, baseGamma_def] using
    one_div_pos.mpr (mul_pos p.base.z_pos (lt_trans zero_lt_one p.base.one_lt_ell))

/-- Helper for lem:polar-continuation: the selected inverse branch recovers the
positive base parameter. -/
theorem inverseParameter_gammaStar (p : Parameters) :
    p.inverseParameter p.gammaStar = p.ell - 1 := by
  simpa only [inverseParameter, gammaStar, baseNu_def] using p.base.inverseParameter_base

/-- Helper for lem:polar-continuation: the inverse parameter is analytic at
the selected base normalization. -/
theorem inverseParameter_analyticAt (p : Parameters) :
    AnalyticAt ℝ p.inverseParameter p.gammaStar := p.base.inverseParameter_analyticAt

/-- Helper for lem:polar-continuation: both angular coefficients have a positive
reciprocal sum, which appears in the feedback denominator. -/
theorem inverseAngleSum_pos (p : Parameters) : 0 < 1 / p.deltaEven + 1 / p.deltaOdd := by
  exact add_pos (one_div_pos.mpr p.deltaEven_pos) (one_div_pos.mpr p.deltaOdd_pos)

/-- Helper for eq:polar-feedback: the feedback potential is positive whenever
its normalization and inverse parameter are positive. -/
theorem feedbackPotential_pos (p : Parameters) (hβ : 0 < p.beta) {γ : ℝ}
    (hγ : 0 < γ) (hν : 0 < p.inverseParameter γ) : 0 < p.feedbackPotential γ := by
  exact div_pos p.gammaStar_pos
    (mul_pos (mul_pos (mul_pos (add_pos zero_lt_one hβ) hγ) hν) p.inverseAngleSum_pos)

/-- Helper for eq:polar-slow-drift: substituting the source feedback gives
the exact linear restoring drift throughout the positive inverse branch. -/
theorem restoringDrift_eq (p : Parameters) (hβ : 0 < p.beta) {γ : ℝ}
    (hγ : γ ≠ 0) (hν : p.inverseParameter γ ≠ 0) :
    2 * γ * p.inverseParameter γ * (1 / p.deltaEven + 1 / p.deltaOdd) *
        p.feedbackPotential γ - 2 * γ / (1 + p.beta) =
      -2 * (γ - p.gammaStar) / (1 + p.beta) := by
  have hβden : 1 + p.beta ≠ 0 := (add_pos zero_lt_one hβ).ne'
  have hsum : p.deltaEven⁻¹ + p.deltaOdd⁻¹ ≠ 0 := by
    simpa only [one_div] using p.inverseAngleSum_pos.ne'
  rw [feedbackPotential]
  field_simp [hβden, hγ, hν, hsum]
  ring

/-- Helper for eq:polar-feedback: the source feedback potential is analytic
at the selected equilibrium, with every denominator proved nonzero. -/
theorem feedbackPotential_analyticAt (p : Parameters) (hβ : 0 < p.beta) :
    AnalyticAt ℝ p.feedbackPotential p.gammaStar := by
  have hid : AnalyticAt ℝ (fun γ : ℝ ↦ γ) p.gammaStar := analyticAt_id
  have hden : AnalyticAt ℝ (fun γ : ℝ ↦
      (1 + p.beta) * γ * p.inverseParameter γ * (1 / p.deltaEven + 1 / p.deltaOdd))
      p.gammaStar :=
    ((analyticAt_const.mul hid).mul p.inverseParameter_analyticAt).mul analyticAt_const
  have hν : 0 < p.inverseParameter p.gammaStar := by
    rw [inverseParameter_gammaStar]
    exact sub_pos.mpr p.base.one_lt_ell
  exact analyticAt_const.div hden
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (add_pos zero_lt_one hβ).ne'
      p.gammaStar_pos.ne') hν.ne') p.inverseAngleSum_pos.ne')

/-- Helper for eq:polar-angles: the even angular coefficient is analytic at zero. -/
theorem evenAngleFactor_analyticAt (p : Parameters) :
    AnalyticAt ℝ p.evenAngleFactor 0 :=
  analyticAt_const.mul (analyticAt_angleFactor_zero p.beta)

/-- Helper for eq:polar-angles: the odd angular coefficient is analytic at zero. -/
theorem oddAngleFactor_analyticAt (p : Parameters) :
    AnalyticAt ℝ p.oddAngleFactor 0 :=
  analyticAt_const.mul (analyticAt_angleFactor_zero p.beta)

/-- Helper for eq:polar-angles: the even angle factor recovers its prescribed
positive limiting coefficient. -/
theorem evenAngleFactor_zero (p : Parameters) (hβ : 0 < p.beta) :
    p.evenAngleFactor 0 = p.deltaEven := by
  simp only [evenAngleFactor, angleFactor_zero hβ, mul_one]

/-- Helper for eq:polar-angles: the odd angle factor recovers its prescribed
positive limiting coefficient. -/
theorem oddAngleFactor_zero (p : Parameters) (hβ : 0 < p.beta) :
    p.oddAngleFactor 0 = p.deltaOdd := by
  simp only [oddAngleFactor, angleFactor_zero hβ, mul_one]

/-- Helper for eq:polar-angles: even terms of the interleaving are exact. -/
@[simp]
theorem angle_even (p : Parameters) (j : ℕ) : p.angle (2 * j) = p.evenAngle j := by
  exact DFP.twoStepSequence_even p.evenAngle p.oddAngle j

/-- Helper for eq:polar-angles: odd terms of the interleaving are exact. -/
@[simp]
theorem angle_odd (p : Parameters) (j : ℕ) : p.angle (2 * j + 1) = p.oddAngle j := by
  exact DFP.twoStepSequence_odd p.evenAngle p.oddAngle j

/-- Helper for lem:polar-continuation: the initial normalized state is the
prescribed base state, rather than an assumed feasible witness. -/
@[simp]
theorem normalizedEvenState_zero (p : Parameters) :
    p.normalizedEvenState 0 = p.initialState := by
  rfl

/-- Helper for lem:polar-continuation: the source trajectory satisfies its
normalized recurrence by construction. -/
theorem normalizedEvenState_succ (p : Parameters) (j : ℕ) :
    p.normalizedEvenState (j + 1) = p.normalizedStep j (p.normalizedEvenState j) := by
  rfl

/-- Helper for eq:polar-feedback: the even gradient factors are exactly one. -/
@[simp]
theorem zeta_even (p : Parameters) (j : ℕ) : p.zeta (2 * j) = 1 := by
  exact DFP.twoStepSequence_even (fun _ ↦ 1) p.oddMultiplier j

/-- Helper for eq:polar-feedback: the odd gradient factors use the actual
recursively constructed boundary state. -/
@[simp]
theorem zeta_odd (p : Parameters) (j : ℕ) : p.zeta (2 * j + 1) = p.oddMultiplier j := by
  exact DFP.twoStepSequence_odd (fun _ ↦ 1) p.oddMultiplier j

/-- Helper for eq:polar-feedback: positivity of every gradient multiplier
holds directly from the exponential feedback formula. -/
theorem zeta_pos (p : Parameters) (k : ℕ) : 0 < p.zeta k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [zeta_even]
    exact zero_lt_one
  · rw [zeta_odd]
    exact Normalized.feedback_pos _ _ _



/-- Helper for eq:polar-angles: the exact full-cycle angular increment is the
scale times its analytic inverse-index correction. -/
theorem evenAngle_sub (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.evenAngle (j + 1) - p.evenAngle j =
      (p.deltaEven + p.deltaOdd) * p.scale j *
        General.angleFactor p.beta (p.inverseIndex j) := by
  have hpower := powerIncrement_eq_scale_angleFactor hβ hstart j
  have hindex : ((p.startIndex + (j + 1) : ℕ) : ℝ) =
      ((p.startIndex + j : ℕ) : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hindex] at hpower
  simp only [evenAngle, scale, inverseIndex]
  rw [hindex]
  calc
    (p.deltaEven + p.deltaOdd) * ((1 + p.beta) / p.beta) *
          ((((p.startIndex + j : ℕ) : ℝ) + 1) ^ (p.beta / (1 + p.beta))) -
        (p.deltaEven + p.deltaOdd) * ((1 + p.beta) / p.beta) *
          (((p.startIndex + j : ℕ) : ℝ) ^ (p.beta / (1 + p.beta))) =
      (p.deltaEven + p.deltaOdd) *
        (((1 + p.beta) / p.beta) *
          ((((p.startIndex + j : ℕ) : ℝ) + 1) ^ (p.beta / (1 + p.beta)) -
            (((p.startIndex + j : ℕ) : ℝ) ^ (p.beta / (1 + p.beta))))) := by
      ring
    _ = _ := by
      simpa only [mul_assoc] using
        congrArg (fun y : ℝ ↦ (p.deltaEven + p.deltaOdd) * y) hpower

/-- Helper for eq:polar-angles: the actual even angular increment is exactly
the canceled stage angle at the prescribed scale and inverse index. -/
theorem angleIncrement_even (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.angleIncrement (2 * j) =
      Normalized.stageAngle (p.evenAngleFactor (p.inverseIndex j)) (p.scale j) := by
  have hsum : p.deltaEven + p.deltaOdd ≠ 0 :=
    (add_pos p.deltaEven_pos p.deltaOdd_pos).ne'
  simp only [angleIncrement, angle_odd, angle_even, oddAngle]
  rw [evenAngle_sub p hβ hstart j, Normalized.stageAngle_def, evenAngleFactor]
  field_simp [hsum]
  ring

/-- Helper for eq:polar-angles: the actual odd angular increment is exactly
the canceled stage angle, with the same scale used through both stages. -/
theorem angleIncrement_odd (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.angleIncrement (2 * j + 1) =
      Normalized.stageAngle (p.oddAngleFactor (p.inverseIndex j)) (p.scale j) := by
  have hsum : p.deltaEven + p.deltaOdd ≠ 0 :=
    (add_pos p.deltaEven_pos p.deltaOdd_pos).ne'
  have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [angleIncrement, hindex, angle_even, angle_odd, oddAngle]
  have hsplit :
      p.evenAngle (j + 1) -
          (p.evenAngle j + p.deltaEven / (p.deltaEven + p.deltaOdd) *
            (p.evenAngle (j + 1) - p.evenAngle j)) =
        (p.deltaOdd / (p.deltaEven + p.deltaOdd)) *
          (p.evenAngle (j + 1) - p.evenAngle j) := by
    field_simp [hsum]
    ring
  rw [hsplit, evenAngle_sub p hβ hstart j, Normalized.stageAngle_def, oddAngleFactor]
  field_simp [hsum]

/-- Helper for eq:polar-two-cycle: the analytic even reference at equilibrium
is exactly the source initial normalized matrix. -/
theorem evenReference_gammaStar (p : Parameters) :
    p.evenReference p.gammaStar = p.initialState := by
  rw [evenReference, inverseParameter_gammaStar]
  have hvalue : cycleLambdaEven p.deltaEven p.deltaOdd (p.ell - 1) = p.ell := by
    simpa only [deltaEven, deltaOdd, baseNu_def] using
      cycleLambdaEven_base p.base.one_lt_ell p.base.z_pos
  rw [hvalue, initialState]

/-- Helper for eq:polar-two-cycle: the analytic odd reference at equilibrium
has coefficient one by the source normalization. -/
theorem oddReference_gammaStar (p : Parameters) :
    p.oddReference p.gammaStar = cycleState p.gammaStar 1 := by
  rw [oddReference, inverseParameter_gammaStar]
  have hvalue : cycleLambdaOdd p.deltaEven p.deltaOdd (p.ell - 1) = 1 := by
    simpa only [deltaEven, deltaOdd, baseNu_def] using
      cycleLambdaOdd_base p.base.one_lt_ell p.base.z_pos
  rw [hvalue]

/-- Helper for lem:polar-continuation: the source base state has a positive
off-diagonal entry at each stage. -/
theorem initial_reference_positive (p : Parameters) :
    0 < p.initialState.2.1 ∧ 0 < (p.oddReference p.gammaStar).2.1 := by
  rw [initialState, oddReference_gammaStar, cycleState_apply, cycleState_apply]
  exact ⟨mul_pos p.gammaStar_pos (lt_trans zero_lt_one p.base.one_lt_ell),
    mul_pos p.gammaStar_pos zero_lt_one⟩





/-- Helper for eq:polar-family: the selected even angular coefficient formula. -/
theorem deltaEven_def (p : Parameters) : p.deltaEven = baseDeltaEven p.ell p.z := by
  rfl

/-- Helper for eq:polar-family: the selected odd angular coefficient formula. -/
theorem deltaOdd_def (p : Parameters) : p.deltaOdd = baseDeltaOdd p.ell p.z := by
  rfl

/-- Helper for eq:polar-family: the selected equilibrium normalization formula. -/
theorem gammaStar_def (p : Parameters) : p.gammaStar = baseGamma p.ell p.z := by
  rfl

/-- Helper for eq:polar-family: the inverse branch comes from the chosen strict Wolfe base. -/
theorem inverseParameter_def (p : Parameters) : p.inverseParameter = p.base.inverseParameter := by
  rfl

/-- Helper for eq:polar-feedback: the exact source potential formula. -/
theorem feedbackPotential_def (p : Parameters) (γ : ℝ) :
    p.feedbackPotential γ = p.gammaStar /
      ((1 + p.beta) * γ * p.inverseParameter γ * (1 / p.deltaEven + 1 / p.deltaOdd)) := by
  rfl

/-- Helper for lem:polar-continuation: the scale is the prescribed generic real-power scale. -/
theorem scale_def (p : Parameters) (j : ℕ) :
    p.scale j = General.scale p.beta p.startIndex j := by
  rfl

/-- Helper for lem:polar-continuation: the inverse index formula used by feedback. -/
theorem inverseIndex_def (p : Parameters) (j : ℕ) :
    p.inverseIndex j = (((p.startIndex + j : ℕ) : ℝ))⁻¹ := by
  rfl

/-- Helper for eq:polar-initial-matrix: the exact initial normalized state. -/
theorem initialState_def (p : Parameters) : p.initialState = cycleState p.gammaStar p.ell := by
  rfl

/-- Helper for eq:polar-two-cycle: the even reference has the source coefficients. -/
theorem evenReference_apply (p : Parameters) (γ : ℝ) :
    p.evenReference γ =
      cycleState γ (cycleLambdaEven p.deltaEven p.deltaOdd (p.inverseParameter γ)) := by
  rfl

/-- Helper for eq:polar-two-cycle: the odd reference has the source coefficients. -/
theorem oddReference_apply (p : Parameters) (γ : ℝ) :
    p.oddReference γ =
      cycleState γ (cycleLambdaOdd p.deltaEven p.deltaOdd (p.inverseParameter γ)) := by
  rfl

/-- Helper for lem:polar-continuation: the even reference preserves its first coordinate. -/
theorem evenReference_fst (p : Parameters) (γ : ℝ) : (p.evenReference γ).1 = γ := by
  simp only [evenReference_apply, cycleState_apply]

/-- Helper for lem:polar-continuation: the odd reference preserves its first coordinate. -/
theorem oddReference_fst (p : Parameters) (γ : ℝ) : (p.oddReference γ).1 = γ := by
  simp only [oddReference_apply, cycleState_apply]

/-- Helper for lem:polar-continuation: the even reference curve is analytic
near the equilibrium by the rational family and its analytic inverse. -/
theorem evenReference_analyticAt (p : Parameters) :
    AnalyticAt ℝ p.evenReference p.gammaStar := by
  have hdomain := baseCycleDomain p.base.one_lt_ell p.base.z_pos
  have hν : p.inverseParameter p.gammaStar = baseNu p.ell := p.base.inverseParameter_base
  have hcoeff : AnalyticAt ℝ
      (fun γ ↦ cycleLambdaEven p.deltaEven p.deltaOdd (p.inverseParameter γ))
      p.gammaStar :=
    (cycleFamily_analyticAt hdomain).1.comp_of_eq p.inverseParameter_analyticAt hν
  have hid : AnalyticAt ℝ (fun γ : ℝ ↦ γ) p.gammaStar := analyticAt_id
  simp only [funext p.evenReference_apply, cycleState_apply]
  exact hid.prod ((hid.mul hcoeff).prod (analyticAt_const.add (hid.mul (hcoeff.pow 2))))

/-- Helper for lem:polar-continuation: the odd reference curve has the same
analytic inverse-parameter regularity. -/
theorem oddReference_analyticAt (p : Parameters) :
    AnalyticAt ℝ p.oddReference p.gammaStar := by
  have hdomain := baseCycleDomain p.base.one_lt_ell p.base.z_pos
  have hν : p.inverseParameter p.gammaStar = baseNu p.ell := p.base.inverseParameter_base
  have hcoeff : AnalyticAt ℝ
      (fun γ ↦ cycleLambdaOdd p.deltaEven p.deltaOdd (p.inverseParameter γ))
      p.gammaStar :=
    (cycleFamily_analyticAt hdomain).2.1.comp_of_eq p.inverseParameter_analyticAt hν
  have hid : AnalyticAt ℝ (fun γ : ℝ ↦ γ) p.gammaStar := analyticAt_id
  simp only [funext p.oddReference_apply, cycleState_apply]
  exact hid.prod ((hid.mul hcoeff).prod (analyticAt_const.add (hid.mul (hcoeff.pow 2))))

/-- Helper for lem:polar-continuation: the general canceled limiting stage is
the previously proved canonical leading-stage formula. -/
theorem leadingStage_eq_original (a : ℝ) (x : ℝ × ℝ × ℝ) :
    Normalized.leadingStage a x = DFP.Polar.Normalized.leadingStage a x := by
  rw [Normalized.leadingStage_apply, DFP.Polar.Normalized.leadingStage_apply]

/-- Helper for lem:polar-continuation: near the equilibrium both source
reference states lie on the positive rational two-cycle family. -/
theorem referenceFamily_eventually (p : Parameters) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      CycleDomain p.deltaEven p.deltaOdd (p.inverseParameter γ) ∧
        p.evenReference γ = evenState p.deltaEven p.deltaOdd (p.inverseParameter γ) ∧
        p.oddReference γ = oddState p.deltaEven p.deltaOdd (p.inverseParameter γ) := by
  filter_upwards [p.base.inverseParameter_eventually_domain,
    p.base.inverseParameter_eventually_right] with γ hdomain hright
  have hright' : cycleGamma p.deltaEven p.deltaOdd (p.inverseParameter γ) = γ := by
    simpa only [deltaEven_def, deltaOdd_def, inverseParameter_def] using hright
  refine ⟨hdomain, ?_, ?_⟩
  · rw [evenReference_apply, evenState_def, hright']
  · rw [oddReference_apply, oddState_def, hright']

/-- Helper for lem:polar-continuation: every nearby even reference maps to its
odd reference, and the odd reference returns to the same even reference. -/
theorem referenceCycle_eventually (p : Parameters) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      Normalized.leadingStage p.deltaEven (p.evenReference γ) = p.oddReference γ ∧
        Normalized.leadingStage p.deltaOdd (p.oddReference γ) = p.evenReference γ := by
  filter_upwards [p.referenceFamily_eventually] with γ hfamily
  constructor
  · rw [leadingStage_eq_original, hfamily.2.1, hfamily.2.2]
    exact evenToOdd hfamily.1
  · rw [leadingStage_eq_original, hfamily.2.2, hfamily.2.1]
    exact oddToEven hfamily.1

/-- Helper for lem:polar-continuation: the limiting complete cycle fixes each
reference state throughout one neighborhood of the base normalization. -/
theorem leadingCycle_eventually_fixed (p : Parameters) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      Normalized.leadingStage p.deltaOdd
        (Normalized.leadingStage p.deltaEven (p.evenReference γ)) = p.evenReference γ := by
  filter_upwards [p.referenceCycle_eventually] with γ hcycle
  rw [hcycle.1, hcycle.2]


/-- Helper for eq:polar-angles: the exact even coefficient input to the canceled stage. -/
theorem evenAngleFactor_def (p : Parameters) (v : ℝ) :
    p.evenAngleFactor v = p.deltaEven * General.angleFactor p.beta v := by
  rfl

/-- Helper for eq:polar-angles: the exact odd coefficient input to the canceled stage. -/
theorem oddAngleFactor_def (p : Parameters) (v : ℝ) :
    p.oddAngleFactor v = p.deltaOdd * General.angleFactor p.beta v := by
  rfl

/-- Helper for lem:polar-continuation: the prescribed complete-cycle step. -/
theorem normalizedStep_apply (p : Parameters) (j : ℕ) (x : ℝ × ℝ × ℝ) :
    p.normalizedStep j x =
      Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
        (p.scale j) (p.inverseIndex j) x := by
  rfl

/-- Helper for lem:polar-continuation: the prescribed intermediate first stage. -/
theorem normalizedOddState_apply (p : Parameters) (j : ℕ) :
    p.normalizedOddState j =
      Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
        0 (p.scale j) (p.inverseIndex j) (p.normalizedEvenState j) (p.normalizedEvenState j) := by
  rfl

/-- Helper for eq:polar-matrix-map: undoing normalization recovers the even raw matrix. -/
theorem evenMatrix_apply (p : Parameters) (j : ℕ) :
    p.evenMatrix j = Normalized.invScaleMatrix (p.scale j) *
      RealSymmetric2.matrix (p.normalizedEvenState j).1 (p.normalizedEvenState j).2.1
        (p.normalizedEvenState j).2.2 * Normalized.invScaleMatrix (p.scale j) := by
  rfl

/-- Helper for eq:polar-matrix-map: the odd raw matrix retains its even boundary's scale. -/
theorem oddMatrix_apply (p : Parameters) (j : ℕ) :
    p.oddMatrix j = Normalized.invScaleMatrix (p.scale j) *
      RealSymmetric2.matrix (p.normalizedOddState j).1 (p.normalizedOddState j).2.1
        (p.normalizedOddState j).2.2 * Normalized.invScaleMatrix (p.scale j) := by
  rfl

/-- Helper for eq:polar-feedback: the shared odd multiplier formula. -/
theorem oddMultiplier_def (p : Parameters) (j : ℕ) :
    p.oddMultiplier j = Normalized.feedback p.feedbackPotential (p.inverseIndex j)
      (p.normalizedEvenState j).1 := by
  rfl

/-- Helper for eq:polar-matrix-map: the even matrix is selected by interleaving. -/
@[simp]
theorem matrix_even (p : Parameters) (j : ℕ) : p.matrix (2 * j) = p.evenMatrix j := by
  exact DFP.twoStepSequence_even p.evenMatrix p.oddMatrix j

/-- Helper for eq:polar-matrix-map: the odd matrix is selected by interleaving. -/
@[simp]
theorem matrix_odd (p : Parameters) (j : ℕ) : p.matrix (2 * j + 1) = p.oddMatrix j := by
  exact DFP.twoStepSequence_odd p.evenMatrix p.oddMatrix j


/-- Helper for lem:polar-continuation: increase the starting index while
retaining every selected geometric and analytic parameter. -/
def withStartIndex (p : Parameters) (j0 : ℕ) : Parameters :=
  { p with startIndex := j0 }

/-- Helper for lem:polar-continuation: replacing the initial index preserves beta. -/
@[simp]
theorem withStartIndex_beta (p : Parameters) (j0 : ℕ) : (p.withStartIndex j0).beta = p.beta := by
  rfl

/-- Helper for lem:polar-continuation: the replacement starting index is exact. -/
@[simp]
theorem withStartIndex_startIndex (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).startIndex = j0 := by
  rfl

/-- Helper for lem:polar-continuation: the initial-index choice does not change
the angular coefficient functions or feedback potential. -/
theorem withStartIndex_analyticData (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).evenAngleFactor = p.evenAngleFactor ∧
      (p.withStartIndex j0).oddAngleFactor = p.oddAngleFactor ∧
        (p.withStartIndex j0).feedbackPotential = p.feedbackPotential := by
  exact ⟨rfl, rfl, rfl⟩

/-- Helper for lem:polar-continuation: the reference state and equilibrium
normalization are fixed before the initial index is increased. -/
theorem withStartIndex_referenceData (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).evenReference = p.evenReference ∧
      (p.withStartIndex j0).oddReference = p.oddReference ∧
        (p.withStartIndex j0).gammaStar = p.gammaStar ∧
          (p.withStartIndex j0).initialState = p.initialState := by
  exact ⟨rfl, rfl, rfl, rfl⟩


/-- Helper for eq:polar-step-data: the actual radius factor is computed from
the current raw matrix and the consecutive angle difference. -/
theorem radiusRatio_def (p : Parameters) (k : ℕ) :
    p.radiusRatio k = DFP.Polar.radiusRatioOf (p.matrix k) (p.angleIncrement k) := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `ell`. -/
@[simp]
theorem withStartIndex_ell (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).ell = p.ell := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `z`. -/
@[simp]
theorem withStartIndex_z (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).z = p.z := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `c1`. -/
@[simp]
theorem withStartIndex_c1 (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).c1 = p.c1 := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `c2`. -/
@[simp]
theorem withStartIndex_c2 (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).c2 = p.c2 := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `deltaEven`. -/
@[simp]
theorem withStartIndex_deltaEven (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).deltaEven = p.deltaEven := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `deltaOdd`. -/
@[simp]
theorem withStartIndex_deltaOdd (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).deltaOdd = p.deltaOdd := by
  rfl

/-- Helper for lem:polar-continuation: the final index choice preserves `gammaStar`. -/
@[simp]
theorem withStartIndex_gammaStar (p : Parameters) (j0 : ℕ) :
    (p.withStartIndex j0).gammaStar = p.gammaStar := by
  rfl



/-- Helper for eq:polar-angles: every source increment is an actual angle difference. -/
theorem angleIncrement_def (p : Parameters) (k : ℕ) :
    p.angleIncrement k = p.angle (k + 1) - p.angle k := by
  rfl

end Parameters

end DFP.Polar.General
