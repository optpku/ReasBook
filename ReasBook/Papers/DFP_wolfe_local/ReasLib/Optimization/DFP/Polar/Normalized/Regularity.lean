/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.Normalized

/-- The ordered family of scalar denominators in the two normalized stages and rescaling. -/
def denominators (L κ t : ℝ) (x : ℝ × ℝ × ℝ) : Fin 9 → ℝ :=
  let ζOdd := feedback L κ t x
  let x₁ := cycleStage L κ 0 t x x
  ![unitRoot t, unitRoot t ^ 2 + unitRoot t + 1,
    sinFactor 0 t, sinFactor 1 t, x.1, x.2.1,
    stageSigma 0 t x 1 ζOdd, x₁.2.1,
    stageSigma 1 t x₁ ζOdd 1]

/-- The explicit ordered formula defining all denominators used by `map`. -/
theorem denominators_apply (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    denominators L κ t x =
      let ζOdd := feedback L κ t x
      let x₁ := cycleStage L κ 0 t x x
      ![unitRoot t, unitRoot t ^ 2 + unitRoot t + 1,
        sinFactor 0 t, sinFactor 1 t, x.1, x.2.1,
        stageSigma 0 t x 1 ζOdd, x₁.2.1,
        stageSigma 1 t x₁ ζOdd 1] := by
  -- The denominator family is defined by exactly this displayed vector.
  rfl

/-- A two-entry vector is
analytic when both scalar coordinates are analytic. -/
private lemma analyticAtFin2Vec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Fin 2 → ℝ} {z : E}
    (h0 : AnalyticAt ℝ (fun y : E ↦ f y 0) z)
    (h1 : AnalyticAt ℝ (fun y : E ↦ f y 1) z) :
    AnalyticAt ℝ f z := by
  -- Reduce the finite vector to its two coordinate germs.
  rw [analyticAt_pi_iff]
  intro j
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- The coordinate update
as a function of its normalized gradient change and rotation matrix. -/
private def stageFromFactors (x : ℝ × ℝ × ℝ)
    (d : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := d.1
  let σ := v ⬝ᵥ w
  let P := Matrix.of d.2
  let Y := P * ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) * P.transpose
  (Y 0 0, Y 0 1, Y 1 1)

/-- The normalized stage equals the update formed from its gradient change
and rotation matrix. -/
private lemma stage_eq_fromFactors (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stage i t x ζ η =
      stageFromFactors x (stepW i t x ζ η, fun r c ↦ rotation i t r c) := by
  -- The interface uses exactly the source's factored bracket and rotation congruence.
  simp only [stage_apply, stageMatrix_def, stageSigma_def, stageFromFactors]
  rfl

/-- The factorized coordinate
update preserves analytic state and factor paths with a nonzero secant scalar. -/
private lemma stageFromFactorsAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : E → ℝ × ℝ × ℝ}
    {d : E → (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)} {z : E}
    (hX : AnalyticAt ℝ X z) (hd : AnalyticAt ℝ d z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z)
    (hσ0 : stepV (X z) ⬝ᵥ (d z).1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stageFromFactors (X y) (d y)) z := by
  -- Expose each state coordinate through analytic projections.
  have hA : AnalyticAt ℝ (fun y ↦ (X y).1) z :=
    AnalyticAt.comp (f := X) analyticAt_fst hX
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z :=
    AnalyticAt.comp (f := X) analyticAt_snd hX
  have hC : AnalyticAt ℝ (fun y ↦ (X y).2.1) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_fst hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_snd hCV
  -- The finite factor coordinates supply the vector and rotation entries.
  have hW : AnalyticAt ℝ (fun y ↦ (d y).1) z :=
    AnalyticAt.comp (f := d) analyticAt_fst hd
  have hP : AnalyticAt ℝ (fun y ↦ (d y).2) z :=
    AnalyticAt.comp (f := d) analyticAt_snd hd
  have hW0 := analyticAt_pi_iff.mp hW 0
  have hW1 := analyticAt_pi_iff.mp hW 1
  have hP0 := analyticAt_pi_iff.mp hP 0
  have hP1 := analyticAt_pi_iff.mp hP 1
  have hP00 := analyticAt_pi_iff.mp hP0 0
  have hP01 := analyticAt_pi_iff.mp hP0 1
  have hP10 := analyticAt_pi_iff.mp hP1 0
  have hP11 := analyticAt_pi_iff.mp hP1 1
  have hV0 : AnalyticAt ℝ (fun y ↦ stepV (X y) 0) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_zero]
    exact hSlope.neg
  have hV1 : AnalyticAt ℝ (fun y ↦ stepV (X y) 1) z := by
    simp only [stepV_def, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact analyticAt_const
  have hσ : AnalyticAt ℝ (fun y ↦ stepV (X y) ⬝ᵥ (d y).1) z := by
    simp only [dotProduct, Fin.sum_univ_two]
    exact (hV0.mul hW0).add (hV1.mul hW1)
  have hσinv := hσ.inv hσ0
  -- The inverse secant is the only nonpolynomial operation in the factored bracket.
  simp only [stageFromFactors, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, RealSymmetric2.matrix_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop

/-- The factorized coordinate
update is analytic in its vector and rotation at a nonzero secant scalar. -/
private lemma stageFromFactors_analyticAt (x : ℝ × ℝ × ℝ)
    (d : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) (hσ0 : stepV x ⬝ᵥ d.1 ≠ 0) :
    AnalyticAt ℝ (stageFromFactors x) d := by
  -- Fixed-state quotients are scalar constants, including when C is zero.
  exact stageFromFactorsAlong_analyticAt analyticAt_const analyticAt_id analyticAt_const hσ0

/-- The canceled normalized
stage is analytic along analytic scale, state, and multiplier paths. -/
private lemma stageAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 2) (τ : E → ℝ) (X : E → ℝ × ℝ × ℝ)
    (ζ ζNext : E → ℝ) (z : E)
    (hτ : AnalyticAt ℝ τ z)
    (hX : AnalyticAt ℝ X z)
    (hζ : AnalyticAt ℝ ζ z)
    (hζNext : AnalyticAt ℝ ζNext z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z)
    (hτ0 : τ z = 0)
    (hσ0 : stageSigma i (τ z) (X z) (ζ z) (ζNext z) ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stage i (τ y) (X y) (ζ y) (ζNext y)) z := by
  -- Compose only the regularized trigonometric germs with the scale path.
  have hAngle : AnalyticAt ℝ (fun y ↦ stageAngle i (τ y)) z :=
    (stageAngle_analyticAt i).comp_of_eq hτ hτ0
  have hSin : AnalyticAt ℝ (fun y ↦ sinFactor i (τ y)) z :=
    (sinFactor_analyticAt i).comp_of_eq hτ hτ0
  have hCot : AnalyticAt ℝ (fun y ↦ cotFactor i (τ y)) z :=
    (cotFactor_analyticAt i).comp_of_eq hτ hτ0
  have hW : AnalyticAt ℝ (fun y ↦ stepW i (τ y) (X y) (ζ y) (ζNext y)) z := by
    apply analyticAtFin2Vec
    · simp only [stepW_def, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simpa only [stepW_def, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hζNext
  have hP : AnalyticAt ℝ (fun y ↦ fun r c : Fin 2 ↦ rotation i (τ y) r c) z := by
    refine analyticAt_pi_iff.mpr ?_
    intro r
    refine analyticAt_pi_iff.mpr ?_
    intro c
    fin_cases r
    all_goals fin_cases c
    all_goals simp only [rotation_def, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  have hsecant : stepV (X z) ⬝ᵥ stepW i (τ z) (X z) (ζ z) (ζNext z) ≠ 0 := by
    simpa only [stageSigma_def] using hσ0
  -- Assemble the exact source bracket through its factor interface.
  simp only [stage_eq_fromFactors]
  exact stageFromFactorsAlong_analyticAt hX (hW.prod hP) hSlope hsecant

/-- The normalized secant scalar is the dot product of the normalized step
and gradient change. -/
private lemma stageSigma_scalar (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stageSigma i t x ζ η =
      -slope x * ((η - ζ) * cotFactor i t - ζ * t ^ 4 * slope x) + η := by
  -- Evaluate the two entries of the normalized dot product.
  simp [stageSigma_def, stepV_def, stepW_def]

/-- Slope preserves analyticity
along a state path with a nonzero off-diagonal coordinate. -/
private lemma slopeAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : AnalyticAt ℝ X z)
    (hC : (X z).2.1 ≠ 0) : AnalyticAt ℝ (fun y ↦ slope (X y)) z := by
  -- Compose the two coordinate projections before dividing by C.
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z :=
    AnalyticAt.comp (f := X) analyticAt_snd hX
  have hC' : AnalyticAt ℝ (fun y ↦ (X y).2.1) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_fst hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_snd hCV
  simp only [slope_def]
  exact hV.div hC' hC

/-- Feedback is analytic along
scale and boundary-state paths with nonzero radial coordinate. -/
private lemma feedbackAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L κ : ℝ) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {z : E}
    (hτ : AnalyticAt ℝ τ z) (hX : AnalyticAt ℝ X z) (hA : (X z).1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ feedback L κ (τ y) (X y)) z := by
  -- The only state quotient is κ / A; the remaining operations are entire.
  have hA' : AnalyticAt ℝ (fun y ↦ (X y).1) z :=
    AnalyticAt.comp (f := X) analyticAt_fst hX
  simp only [feedback_def]
  fun_prop

/-- The normalized secant scalar
is analytic along regular analytic input paths. -/
private lemma stageSigmaAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ}
    {ζ η : E → ℝ} {z : E} (hτ : AnalyticAt ℝ τ z)
    (hζ : AnalyticAt ℝ ζ z) (hη : AnalyticAt ℝ η z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z) (hτ0 : τ z = 0) :
    AnalyticAt ℝ (fun y ↦ stageSigma i (τ y) (X y) (ζ y) (η y)) z := by
  -- Use the canceled cotangent rather than its singular quotient representation.
  have hCot : AnalyticAt ℝ (fun y ↦ cotFactor i (τ y)) z :=
    (cotFactor_analyticAt i).comp_of_eq hτ hτ0
  simp only [stageSigma_scalar]
  fun_prop

/-- A cycle stage is analytic
along paths with analytic feedback and slope at zero scale. -/
private lemma cycleStageAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L κ : ℝ) (i : Fin 2) {τ : E → ℝ}
    {X₀ X : E → ℝ × ℝ × ℝ} {z : E} (hτ : AnalyticAt ℝ τ z)
    (hX : AnalyticAt ℝ X z)
    (hfb : AnalyticAt ℝ (fun y ↦ feedback L κ (τ y) (X₀ y)) z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z) (hτ0 : τ z = 0) :
    AnalyticAt ℝ (fun y ↦ cycleStage L κ i (τ y) (X₀ y) (X y)) z := by
  -- Each phase selects one constant multiplier and the same boundary feedback.
  let ζ : E → ℝ := fun y ↦ (![1, feedback L κ (τ y) (X₀ y)] : Fin 2 → ℝ) i
  let η : E → ℝ := fun y ↦ (![feedback L κ (τ y) (X₀ y), 1] : Fin 2 → ℝ) i
  have hζ : AnalyticAt ℝ ζ z := by
    fin_cases i
    · simpa only [ζ, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : E ↦ (1 : ℝ)) z)
    · simpa [ζ] using hfb
  have hη : AnalyticAt ℝ η z := by
    fin_cases i
    · simpa [η] using hfb
    · simpa [η] using (analyticAt_const : AnalyticAt ℝ (fun _ : E ↦ (1 : ℝ)) z)
  have hfb0 : feedback L κ (τ z) (X₀ z) = 1 := by
    rw [hτ0]
    simp [feedback_def]
  have hζ0 : ζ z = 1 := by
    dsimp only [ζ]
    rw [hfb0]
    fin_cases i
    all_goals rfl
  have hη0 : η z = 1 := by
    dsimp only [η]
    rw [hfb0]
    fin_cases i
    all_goals rfl
  have hσ0 : stageSigma i (τ z) (X z) (ζ z) (η z) ≠ 0 := by
    rw [hτ0, hζ0, hη0]
    simp [stageSigma_scalar]
  simpa only [cycleStage_apply, ζ, η] using
    stageAlong_analyticAt i τ X ζ η z hτ hX hζ hη hSlope hτ0 hσ0

/-- Rescaling preserves
analyticity of state and scale paths based at zero scale. -/
private lemma rescaleAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {z : E}
    (hτ : AnalyticAt ℝ τ z) (hX : AnalyticAt ℝ X z) (hτ0 : τ z = 0) :
    AnalyticAt ℝ (fun y ↦ rescale (τ y) (X y)) z := by
  -- Coordinate multiplication by the regularized rescaling factor is analytic.
  have hA : AnalyticAt ℝ (fun y ↦ (X y).1) z :=
    AnalyticAt.comp (f := X) analyticAt_fst hX
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z :=
    AnalyticAt.comp (f := X) analyticAt_snd hX
  have hC : AnalyticAt ℝ (fun y ↦ (X y).2.1) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_fst hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z :=
    AnalyticAt.comp (f := fun y ↦ (X y).2) analyticAt_snd hCV
  have hρ : AnalyticAt ℝ (fun y ↦ rescaleFactor (τ y)) z :=
    rescaleFactor_analyticAt.comp_of_eq hτ hτ0
  simp only [rescale_apply]
  exact ((hρ.pow 2).mul hA).prod ((hρ.mul hC).prod hV)

/-- The root branch is analytic
at its unit base value. -/
private lemma unitRootAnalytic : AnalyticAt ℝ unitRoot 0 := by
  -- The logarithm argument equals one at zero.
  have hpoly : AnalyticAt ℝ (fun t : ℝ ↦ 1 + t ^ 3) 0 := by fun_prop
  have hnonzero : 0 < (1 : ℝ) + 0 ^ 3 := by norm_num
  rw [funext unitRoot_def]
  exact ((hpoly.log hnonzero).div_const).rexp'

/-- The regularized sine factor
has the prescribed limiting angular coefficient. -/
private lemma sinFactor_zero (i : Fin 2) : sinFactor i 0 = limitAngle i := by
  -- Evaluate the canceled sinc formula, whose value at zero is one.
  fin_cases i
  all_goals norm_num [sinFactor_def, stageAngle_def, stageAngleFactor_def,
    angleFactor_def, unitRoot_def, limitAngle_zero, limitAngle_one,
    stageWeight_zero, stageWeight_one]
  all_goals ring

/-- At zero scale, the denominators reduce to limiting angular coefficients
and state coordinates. -/
private lemma denominators_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ) :
    denominators L κ 0 x =
      ![1, 3, limitAngle 0, limitAngle 1, x.1, x.2.1, 1,
        (leadingStage (limitAngle 0) x).2.1, 1] := by
  -- Unit feedback makes both secant scalars exactly one at zero.
  simp [denominators_apply, unitRoot_def, sinFactor_zero, feedback_def,
    cycleStage_zero, stageSigma_scalar]
  norm_num

/-- The finite denominator
family is jointly analytic at zero scale and a positive state. -/
private lemma denominators_analyticAt_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hC₁ : 0 < (leadingStage (limitAngle 0) x).2.1) :
    AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ denominators L κ y.1 y.2) (0, x) := by
  -- The first-stage state and both secant scalars use the same analytic feedback.
  have hτ : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.1) (0, x) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2) (0, x) := analyticAt_snd
  have hfb := feedbackAlong_analyticAt L κ hτ hX hA.ne'
  have hSlope := slopeAlong_analyticAt hX hC.ne'
  have hX₁ := cycleStageAlong_analyticAt L κ 0 hτ hX hfb hSlope rfl
  have hC₁₀ : (cycleStage L κ 0 0 x x).2.1 ≠ 0 := by
    rw [cycleStage_zero]
    exact hC₁.ne'
  have hSlope₁ := slopeAlong_analyticAt hX₁ hC₁₀
  have hσ₀ := stageSigmaAlong_analyticAt 0 (ζ := fun _ ↦ 1) hτ analyticAt_const hfb hSlope rfl
  have hσ₁ := stageSigmaAlong_analyticAt 1 (η := fun _ ↦ 1) hτ hfb analyticAt_const hSlope₁ rfl
  have hroot : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ unitRoot y.1) (0, x) :=
    unitRootAnalytic.comp_of_eq hτ rfl
  have hsin0 : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ sinFactor 0 y.1) (0, x) :=
    (sinFactor_analyticAt 0).comp_of_eq hτ rfl
  have hsin1 : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ sinFactor 1 y.1) (0, x) :=
    (sinFactor_analyticAt 1).comp_of_eq hτ rfl
  have hCV : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2.2) (0, x) :=
    AnalyticAt.comp (f := fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2) analyticAt_snd hX
  have hA' : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2.1) (0, x) :=
    AnalyticAt.comp (f := fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2) analyticAt_fst hX
  have hC' : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2.2.1) (0, x) :=
    AnalyticAt.comp (f := fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2.2) analyticAt_fst hCV
  have hX₁CV : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦
      (cycleStage L κ 0 y.1 y.2 y.2).2) (0, x) :=
    AnalyticAt.comp (f := fun y : ℝ × (ℝ × ℝ × ℝ) ↦
      cycleStage L κ 0 y.1 y.2 y.2) analyticAt_snd hX₁
  have hX₁C : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦
      (cycleStage L κ 0 y.1 y.2 y.2).2.1) (0, x) :=
    AnalyticAt.comp (f := fun y : ℝ × (ℝ × ℝ × ℝ) ↦
      (cycleStage L κ 0 y.1 y.2 y.2).2) analyticAt_fst hX₁CV
  -- Evaluate each finite index after proving all meaningful component germs.
  refine analyticAt_pi_iff.mpr ?_
  intro i
  fin_cases i
  all_goals simp only [denominators_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val]
  all_goals fun_prop

/-- Both limiting angular
coefficients are strictly positive. -/
private lemma limitAngle_pos (i : Fin 2) : 0 < limitAngle i := by
  -- Both phase weights multiply the positive prescribed base angle.
  have hbase : 0 < DFP.Polar.baseAngle := by
    rw [DFP.Polar.baseAngle_def]
    positivity
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, limitAngle_zero] using
      mul_pos (two_pos : (0 : ℝ) < 2) hbase
  · simpa only [Fin.mk_one, Fin.isValue, limitAngle_one] using hbase

/-- All zero-scale
denominators are positive on a positive state neighborhood. -/
private lemma denominators_pos_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hC₁ : 0 < (leadingStage (limitAngle 0) x).2.1) (i : Fin 9) :
    0 < denominators L κ 0 x i := by
  -- Read positivity from the exact boundary denominator vector.
  rw [denominators_zero]
  fin_cases i
  all_goals simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Fin.reduceFinMk, Matrix.cons_val]
  all_goals first | exact hA | exact hC | exact hC₁ | exact limitAngle_pos _ | norm_num

/-- On a compact positive-state set, all normalized denominators have one positive
lower bound for uniformly small scale. -/
theorem denominators_uniformOn (L κ : ℝ) (𝒦 : Set (ℝ × ℝ × ℝ))
    (h𝒦 : IsCompact 𝒦)
    (hA : ∀ x ∈ 𝒦, 0 < x.1)
    (hC : ∀ x ∈ 𝒦, 0 < x.2.1)
    (hC₁ : ∀ x ∈ 𝒦, 0 < (leadingStage (limitAngle 0) x).2.1) :
    ∃ ε > 0, ∃ d > 0, ∀ t ∈ Set.Icc (-ε) ε,
      ∀ x ∈ 𝒦, ∀ i : Fin 9, d ≤ |denominators L κ t x i| := by
  -- Take one positive minimum on the fixed compact state/index fiber.
  have hcompact : IsCompact (𝒦 ×ˢ (Set.univ : Set (Fin 9))) := h𝒦.prod isCompact_univ
  have hcontinuous : ContinuousOn
      (fun xi : (ℝ × ℝ × ℝ) × Fin 9 ↦ |denominators L κ 0 xi.1 xi.2|)
      (𝒦 ×ˢ Set.univ) := by
    intro xi hxi
    have hD := (denominators_analyticAt_zero L κ xi.1
      (hA xi.1 hxi.1) (hC xi.1 hxi.1) (hC₁ xi.1 hxi.1)).continuousAt
    have hbase : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦ denominators L κ 0 x) xi.1 :=
      hD.comp (continuousAt_const.prodMk continuousAt_id)
    have heval : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × Fin 9 ↦ denominators L κ 0 z.1 z.2) xi := by
      apply continuousAt_prod_of_discrete_right.mpr
      exact (continuousAt_apply xi.2 _).comp hbase
    exact heval.abs.continuousWithinAt
  have hpositive : ∀ xi ∈ (𝒦 ×ˢ (Set.univ : Set (Fin 9))),
      0 < |denominators L κ 0 xi.1 xi.2| := by
    intro xi hxi
    exact abs_pos.mpr (denominators_pos_zero L κ xi.1
      (hA xi.1 hxi.1) (hC xi.1 hxi.1) (hC₁ xi.1 hxi.1) xi.2).ne'
  obtain ⟨b, hb, hbound⟩ := hcompact.exists_forall_le' hcontinuous hpositive
  -- Joint continuity preserves half this minimum on one common scale radius.
  have hnear : ∀ xi ∈ (𝒦 ×ˢ (Set.univ : Set (Fin 9))),
      ∀ᶠ z : ℝ × ((ℝ × ℝ × ℝ) × Fin 9) in 𝓝 (0, xi),
        b / 2 ≤ |denominators L κ z.1 z.2.1 z.2.2| := by
    intro xi hxi
    have hD := (denominators_analyticAt_zero L κ xi.1
      (hA xi.1 hxi.1) (hC xi.1 hxi.1) (hC₁ xi.1 hxi.1)).continuousAt
    have hinput : ContinuousAt
        (fun z : ℝ × ((ℝ × ℝ × ℝ) × Fin 9) ↦ (z.1, z.2.1)) (0, xi) :=
      continuousAt_fst.prodMk (continuousAt_snd.fst)
    have hindex : ContinuousAt
        (fun z : ℝ × ((ℝ × ℝ × ℝ) × Fin 9) ↦ z.2.2) (0, xi) :=
      continuousAt_snd.snd
    have hfull : ContinuousAt
        (fun z : (ℝ × (ℝ × ℝ × ℝ)) × Fin 9 ↦
          |denominators L κ z.1.1 z.1.2 z.2|) ((0, xi.1), xi.2) := by
      apply continuousAt_prod_of_discrete_right.mpr
      exact ((continuousAt_apply xi.2 _).comp hD).abs
    have heval : ContinuousAt
        (fun z : ℝ × ((ℝ × ℝ × ℝ) × Fin 9) ↦
          |denominators L κ z.1 z.2.1 z.2.2|) (0, xi) := by
      simpa only [Function.comp_def] using
        (ContinuousAt.comp
          (g := fun z : (ℝ × (ℝ × ℝ × ℝ)) × Fin 9 ↦
            |denominators L κ z.1.1 z.1.2 z.2|)
          (f := fun z : ℝ × ((ℝ × ℝ × ℝ) × Fin 9) ↦
            ((z.1, z.2.1), z.2.2)) hfull (hinput.prodMk hindex))
    have hgap : b / 2 < |denominators L κ 0 xi.1 xi.2| :=
      (half_lt_self hb).trans_le (hbound xi hxi)
    exact (heval.eventually (Ioi_mem_nhds hgap)).mono fun _ hz ↦ hz.le
  obtain ⟨δ, hδ, hδbound⟩ := FiniteTaylorJet.compactFiberNormRadius (X := ℝ)
    (P := fun t xi ↦ b / 2 ≤ |denominators L κ t xi.1 xi.2|) hcompact hnear
  refine ⟨δ / 2, half_pos hδ, b / 2, half_pos hb, ?_⟩
  intro t ht x hx i
  have htNorm : ‖t‖ ≤ δ / 2 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ht
  exact hδbound (x, i) ⟨hx, Set.mem_univ i⟩ t
    (htNorm.trans_lt (half_lt_self hδ))

/-- The normalized two-stage map is jointly analytic at zero scale and a positive state. -/
theorem map_analyticAt_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hC₁ : 0 < (leadingStage (limitAngle 0) x).2.1) :
    AnalyticAt ℝ (Function.uncurry (map L κ)) (0, x) := by
  -- First stage, evaluated at its exact limiting state.
  have hτ : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.1) (0, x) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ y.2) (0, x) := analyticAt_snd
  have hfb := feedbackAlong_analyticAt L κ hτ hX hA.ne'
  have hSlope := slopeAlong_analyticAt hX hC.ne'
  have hX₁ := cycleStageAlong_analyticAt L κ 0 hτ hX hfb hSlope rfl
  have hC₁₀ : (cycleStage L κ 0 0 x x).2.1 ≠ 0 := by
    rw [cycleStage_zero]
    exact hC₁.ne'
  have hSlope₁ := slopeAlong_analyticAt hX₁ hC₁₀
  have hX₂ := cycleStageAlong_analyticAt L κ 1 hτ hX₁ hfb hSlope₁ rfl
  have hrescale := rescaleAlong_analyticAt hτ hX₂ rfl
  -- Compose the two stages before the source's final change of scale.
  change AnalyticAt ℝ (fun y : ℝ × (ℝ × ℝ × ℝ) ↦ map L κ y.1 y.2) (0, x)
  simp only [map_def, twoStep_def]
  exact hrescale

/-- Every finite Taylor order of the normalized map is uniform on a fixed compact
positive-state set. -/
theorem map_uniformJets (L κ : ℝ) (m : ℕ) (𝒦 : Set (ℝ × ℝ × ℝ))
    (h𝒦 : IsCompact 𝒦)
    (hA : ∀ x ∈ 𝒦, 0 < x.1)
    (hC : ∀ x ∈ 𝒦, 0 < x.2.1)
    (hC₁ : ∀ x ∈ 𝒦, 0 < (leadingStage (limitAngle 0) x).2.1) :
    FiniteTaylorJet.IsUniformOn
      (fun x : ℝ × ℝ × ℝ ↦ fun t : ℝ ↦ map L κ t x)
      (fun x ↦ FiniteTaylorJet.ofFunction ℝ m (fun t ↦ map L κ t x) 0)
      0 𝒦 := by
  -- Compact-fiber Taylor uniformity applies after swapping parameter and scale coordinates.
  refine FiniteTaylorJet.isUniformOn_of_contDiffAt m
    (fun x : ℝ × ℝ × ℝ ↦ fun t : ℝ ↦ map L κ t x) 0 𝒦 h𝒦 ?_
  intro x hx
  have hm := map_analyticAt_zero L κ x (hA x hx) (hC x hx) (hC₁ x hx)
  have hswap : AnalyticAt ℝ
      (fun y : (ℝ × ℝ × ℝ) × ℝ ↦ (y.2, y.1)) (x, 0) := by
    exact (analyticAt_snd : AnalyticAt ℝ
      (fun y : (ℝ × ℝ × ℝ) × ℝ ↦ y.2) (x, 0)).prod
      (analyticAt_fst : AnalyticAt ℝ
        (fun y : (ℝ × ℝ × ℝ) × ℝ ↦ y.1) (x, 0))
  have hswap0 : (fun y : (ℝ × ℝ × ℝ) × ℝ ↦ (y.2, y.1)) (x, 0) = (0, x) := rfl
  have hcomp := hm.comp_of_eq hswap hswap0
  have htarget : AnalyticAt ℝ
      (Function.uncurry (fun x : ℝ × ℝ × ℝ ↦ fun t : ℝ ↦ map L κ t x)) (x, 0) := by
    change AnalyticAt ℝ (fun y : (ℝ × ℝ × ℝ) × ℝ ↦ map L κ y.2 y.1) (x, 0)
    exact hcomp
  exact htarget.contDiffAt

/-- Each feedback-controlled normalized stage is analytic in scale at zero. -/
theorem cycleStage_analyticAt_zero (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun t ↦ cycleStage L κ i t x₀ x) 0 := by
  -- Fixed-state quotients are constants; cubic feedback is an analytic scale path.
  have hfb : AnalyticAt ℝ (fun t : ℝ ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  exact cycleStageAlong_analyticAt L κ i analyticAt_id analyticAt_const hfb
    analyticAt_const rfl

/-- The cubic root differs
from one by order three in scale. -/
private lemma unitRoot_sub_one_isBigO :
    (fun t : ℝ ↦ unitRoot t - 1) =O[𝓝 0] (fun t ↦ t ^ 3) := by
  -- Compose the regular exp-log branch with the cubic scale variable.
  let f : ℝ → ℝ := fun u ↦ Real.exp (Real.log (1 + u) / 3)
  have ha : AnalyticAt ℝ f 0 := by
    have hpos : 0 < (1 : ℝ) + 0 := by norm_num
    dsimp only [f]
    fun_prop
  have hcubic : Tendsto (fun t : ℝ ↦ t ^ 3) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun t : ℝ ↦ t ^ 3) 0 := by fun_prop
    simpa [ContinuousAt] using hcont
  have hb := ha.differentiableAt.isBigO_sub.comp_tendsto hcubic
  simpa [f, unitRoot_def, Function.comp_def] using hb

/-- The regular angle factor
is analytic at zero. -/
private lemma stageAngleFactorAnalytic (i : Fin 2) :
    AnalyticAt ℝ (stageAngleFactor i) 0 := by
  -- Its only denominator has the value three at zero.
  have hd := (unitRootAnalytic.pow 2).add unitRootAnalytic |>.add
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) 0)
  have hd0 : unitRoot 0 ^ 2 + unitRoot 0 + 1 ≠ 0 := by norm_num [unitRoot_def]
  rw [funext (stageAngleFactor_def i)]
  simp only [angleFactor_def]
  exact analyticAt_const.mul (analyticAt_const.div hd hd0)

/-- The canceled angle
factor has its limiting coefficient at zero. -/
private lemma stageAngleFactor_zero (i : Fin 2) :
    stageAngleFactor i 0 = limitAngle i := by
  -- At zero the sinc multiplier is one.
  have h := sinFactor_zero i
  simpa [sinFactor_def, stageAngle_def] using h

/-- The canceled angle factor
differs from its limiting value only at cubic order. -/
private lemma stageAngleFactor_sub_limit_isBigO (i : Fin 2) :
    (fun t : ℝ ↦ stageAngleFactor i t - limitAngle i) =O[𝓝 0] (fun t ↦ t ^ 3) := by
  -- Exact cubic cancellation leaves an analytic rational function of the unit root.
  let f : ℝ → ℝ := fun u ↦ stageWeight i * (9 * DFP.Polar.baseAngle / (u ^ 2 + u + 1))
  have hd0 : (1 : ℝ) ^ 2 + 1 + 1 ≠ 0 := by norm_num
  have ha : AnalyticAt ℝ f 1 := by
    dsimp only [f]
    fun_prop
  have hroot : Tendsto unitRoot (𝓝 0) (𝓝 1) := by
    simpa [ContinuousAt, unitRoot_def] using unitRootAnalytic.continuousAt
  have hb := (ha.differentiableAt.isBigO_sub.comp_tendsto hroot).trans
    unitRoot_sub_one_isBigO
  have hf0 : f 1 = limitAngle i := by
    have h := stageAngleFactor_zero i
    simpa [f, stageAngleFactor_def, angleFactor_def, unitRoot_def] using h
  simp only [hf0, Function.comp_def] at hb
  simpa only [f, stageAngleFactor_def, angleFactor_def] using hb

/-- The stage angle is of
quadratic scale order. -/
private lemma stageAngle_isBigO (i : Fin 2) :
    (stageAngle i) =O[𝓝 0] (fun t : ℝ ↦ t ^ 2) := by
  -- The analytic canceled coefficient is bounded at zero.
  have hb := (stageAngleFactorAnalytic i).continuousAt.isBigO_one ℝ
  have hm := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 2) (𝓝 0)).mul hb
  rw [funext (stageAngle_def i)]
  simpa only [mul_one] using hm

/-- The sinc defect factors
through the square of its argument with an analytic cofactor. -/
private lemma sinc_sub_one_factor :
    ∃ q : ℝ → ℝ, AnalyticAt ℝ q 0 ∧ ∀ u : ℝ, Real.sinc u - 1 = u ^ 2 * q u := by
  -- The sine Taylor formula has zero constant and quadratic coefficients.
  obtain ⟨q, hq, hformula⟩ :=
    (Real.analyticAt_sin : AnalyticAt ℝ Real.sin 0).exists_eq_sum_add_pow_mul 3
  have hsin : ∀ u : ℝ, Real.sin u = u + u ^ 3 * q u := by
    intro u
    simpa [Finset.sum_range_succ, iteratedDeriv_succ', iteratedDeriv_zero,
      Real.deriv_sin, Real.deriv_cos, smul_eq_mul] using hformula u
  refine ⟨q, hq, ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    simp
  · rw [Real.sinc_of_ne_zero hu]
    rw [sub_eq_iff_eq_add]
    apply (div_eq_iff hu).mpr
    rw [hsin]
    ring

/-- The cosine defect has an
analytic quadratic factor. -/
private lemma cos_sub_one_factor :
    ∃ q : ℝ → ℝ, AnalyticAt ℝ q 0 ∧ ∀ u : ℝ, Real.cos u - 1 = u ^ 2 * q u := by
  -- Cosine has value one and zero linear coefficient at the origin.
  obtain ⟨q, hq, hformula⟩ :=
    (Real.analyticAt_cos : AnalyticAt ℝ Real.cos 0).exists_eq_sum_add_pow_mul 2
  refine ⟨q, hq, ?_⟩
  intro u
  have h := hformula u
  have hcos : Real.cos u = 1 + u ^ 2 * q u := by
    simpa [Finset.sum_range_succ, iteratedDeriv_succ', iteratedDeriv_zero,
      Real.deriv_cos, smul_eq_mul] using h
  linarith

/-- Quadratic analytic
trigonometric defects become fourth-order scale errors. -/
private lemma quadraticFactorAlong_isBigO (i : Fin 2) (q : ℝ → ℝ)
    (hq : AnalyticAt ℝ q 0) :
    (fun t : ℝ ↦ stageAngle i t ^ 2 * q (stageAngle i t)) =O[𝓝 0]
      (fun t ↦ t ^ 4) := by
  -- The angle is O(t²), and the composed analytic cofactor stays bounded.
  have hangle0 : stageAngle i 0 = 0 := by simp [stageAngle_def]
  have hcomp := hq.comp_of_eq (stageAngle_analyticAt i) hangle0
  have hb := ((stageAngle_isBigO i).pow 2).mul (hcomp.continuousAt.isBigO_one ℝ)
  simpa only [mul_one, ← pow_mul, Nat.reduceMul, Function.comp_def] using hb

/-- The regularized sine
coefficient has no scale terms of order one or two. -/
private lemma sinFactor_sub_limitAngle_isBigO (i : Fin 2) :
    (fun t : ℝ ↦ sinFactor i t - limitAngle i) =O[𝓝 0] (fun t ↦ t ^ 3) := by
  -- Separate cubic variation of the canceled angle factor from the fourth-order sinc defect.
  obtain ⟨q, hq, hfactor⟩ := sinc_sub_one_factor
  have hsinc4 : (fun t : ℝ ↦ Real.sinc (stageAngle i t) - 1) =O[𝓝 0]
      (fun t ↦ t ^ 4) := by
    simpa only [hfactor] using quadraticFactorAlong_isBigO i q hq
  have hfour : (fun t : ℝ ↦ t ^ 4) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self 3)).isBigO
  have hbounded : (fun t : ℝ ↦ Real.sinc (stageAngle i t)) =O[𝓝 0]
      (fun _ : ℝ ↦ (1 : ℝ)) :=
    (Real.continuous_sinc.continuousAt.comp (stageAngle_analyticAt i).continuousAt).isBigO_one ℝ
  have hfirst := (stageAngleFactor_sub_limit_isBigO i).mul hbounded
  have hsecond := (hsinc4.trans hfour).const_mul_left (limitAngle i)
  have heq (t : ℝ) :
      sinFactor i t - limitAngle i =
        (stageAngleFactor i t - limitAngle i) * Real.sinc (stageAngle i t) +
          limitAngle i * (Real.sinc (stageAngle i t) - 1) := by
    rw [sinFactor_def]
    ring
  have hfirst' : (fun t : ℝ ↦ (stageAngleFactor i t - limitAngle i) *
      Real.sinc (stageAngle i t)) =O[𝓝 0] (fun t ↦ t ^ 3) := by
    simpa only [mul_one] using hfirst
  simpa only [← heq] using hfirst'.add hsecond

/-- The normalized rotation
has only cubic and higher scale perturbations of its limiting shear. -/
private lemma rotation_sub_zero_isBigO (i : Fin 2) :
    (fun t : ℝ ↦ fun r c : Fin 2 ↦ rotation i t r c - rotation i 0 r c) =O[𝓝 0]
      (fun t ↦ t ^ 3) := by
  -- The diagonal cosine and upper-right entry are O(t⁴); the lower-left error is O(t³).
  obtain ⟨q, hq, hfactor⟩ := cos_sub_one_factor
  have hcos4 : (fun t : ℝ ↦ Real.cos (stageAngle i t) - 1) =O[𝓝 0]
      (fun t ↦ t ^ 4) := by
    simpa only [hfactor] using quadraticFactorAlong_isBigO i q hq
  have hfour : (fun t : ℝ ↦ t ^ 4) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self 3)).isBigO
  have hupper := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 4) (𝓝 0)).mul
    ((sinFactor_analyticAt i).continuousAt.isBigO_one ℝ)
  have hsin := sinFactor_sub_limitAngle_isBigO i
  have hupper' : (fun t : ℝ ↦ t ^ 4 * sinFactor i t) =O[𝓝 0]
      (fun t ↦ t ^ 4) := by
    simpa only [mul_one] using hupper
  have hangle0 : stageAngle i 0 = 0 := by simp [stageAngle_def]
  refine Asymptotics.isBigO_pi.mpr ?_
  intro r
  refine Asymptotics.isBigO_pi.mpr ?_
  intro c
  fin_cases r
  all_goals fin_cases c
  · simpa [rotation_def, hangle0, sinFactor_zero] using hcos4.trans hfour
  · simpa [rotation_def, hangle0, sinFactor_zero] using hupper'.trans hfour
  · simpa [rotation_def, hangle0, sinFactor_zero, neg_sub, sub_eq_add_neg, add_comm]
      using hsin.neg_left
  · simpa [rotation_def, hangle0, sinFactor_zero] using hcos4.trans hfour

/-- Fixed-boundary feedback
is a cubic perturbation of one. -/
private lemma feedback_sub_one_isBigO (L κ : ℝ) (x₀ : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ feedback L κ t x₀ - 1) =O[𝓝 0] (fun t ↦ t ^ 3) := by
  -- The cubic exponent is the sole scale input to an analytic exponential.
  let f : ℝ → ℝ := fun u ↦ Real.exp (-L * (κ / x₀.1) ^ 2 * u)
  have ha : AnalyticAt ℝ f 0 := by
    dsimp only [f]
    fun_prop
  have hcubic : Tendsto (fun t : ℝ ↦ t ^ 3) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ t ^ 3) 0 := by fun_prop
    simpa [ContinuousAt] using hc
  have hb := ha.differentiableAt.isBigO_sub.comp_tendsto hcubic
  simpa [f, feedback_def, Function.comp_def] using hb

/-- Cubic multiplier
perturbations produce a cubic error in the canceled gradient change. -/
private lemma stepW_sub_zero_isBigO (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (ζ η : ℝ → ℝ) (hζ : ContinuousAt ζ 0) (hζ0 : ζ 0 = 1) (hη0 : η 0 = 1)
    (hζ3 : (fun t ↦ ζ t - 1) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3))
    (hη3 : (fun t ↦ η t - 1) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3)) :
    (fun t : ℝ ↦ fun j : Fin 2 ↦
      stepW i t x (ζ t) (η t) j - stepW i 0 x (ζ 0) (η 0) j) =O[𝓝 0]
      (fun t ↦ t ^ 3) := by
  -- The multiplier difference is cubic and cotFactor is bounded after regularization.
  have hdiff : (fun t ↦ η t - ζ t) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    simpa only [sub_sub_sub_cancel_right] using hη3.sub hζ3
  have hcot := (cotFactor_analyticAt i).continuousAt.isBigO_one ℝ
  have hfirst : (fun t ↦ (η t - ζ t) * cotFactor i t) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
    simpa only [mul_one] using hdiff.mul hcot
  have hfour : (fun t : ℝ ↦ t ^ 4) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self 3)).isBigO
  have hζbounded := hζ.isBigO_one ℝ
  have hsecond : (fun t ↦ ζ t * t ^ 4 * slope x) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
    have hb : (fun t : ℝ ↦ ζ t * t ^ 4) =O[𝓝 0] (fun t ↦ t ^ 4) := by
      simpa only [one_mul] using hζbounded.mul
        (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 4) (𝓝 0))
    simpa only [mul_comm (slope x)] using (hb.const_mul_left (slope x)).trans hfour
  refine Asymptotics.isBigO_pi.mpr ?_
  intro j
  fin_cases j
  · simpa [stepW_def, hζ0, hη0] using hfirst.sub hsecond
  · simpa [stepW_def, hζ0, hη0] using hη3

/-- The feedback-controlled
stage differs from its limiting stage by a cubic scale error. -/
private lemma cycleStage_sub_leading_isBigO (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    (fun t ↦ cycleStage L κ i t x₀ x - leadingStage (limitAngle i) x) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
  -- Both phases have unit limits and cubic feedback perturbations.
  let ζ : ℝ → ℝ := fun t ↦ (![1, feedback L κ t x₀] : Fin 2 → ℝ) i
  let η : ℝ → ℝ := fun t ↦ (![feedback L κ t x₀, 1] : Fin 2 → ℝ) i
  have hfb : ContinuousAt (fun t : ℝ ↦ feedback L κ t x₀) 0 := by
    simp only [feedback_def]
    fun_prop
  have hζ : ContinuousAt ζ 0 := by
    fin_cases i
    · simpa [ζ] using (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 0)
    · simpa [ζ] using hfb
  have hζ0 : ζ 0 = 1 := by
    dsimp only [ζ]
    have hf0 : feedback L κ 0 x₀ = 1 := by simp [feedback_def]
    rw [hf0]
    fin_cases i
    all_goals rfl
  have hη0 : η 0 = 1 := by
    dsimp only [η]
    have hf0 : feedback L κ 0 x₀ = 1 := by simp [feedback_def]
    rw [hf0]
    fin_cases i
    all_goals rfl
  have hζ3 : (fun t ↦ ζ t - 1) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    fin_cases i
    · simpa [ζ] using Asymptotics.isBigO_zero (fun t : ℝ ↦ t ^ 3) (𝓝 0)
    · simpa [ζ] using feedback_sub_one_isBigO L κ x₀
  have hη3 : (fun t ↦ η t - 1) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    fin_cases i
    · simpa [η] using feedback_sub_one_isBigO L κ x₀
    · simpa [η] using Asymptotics.isBigO_zero (fun t : ℝ ↦ t ^ 3) (𝓝 0)
  have hW3 := stepW_sub_zero_isBigO i x ζ η hζ hζ0 hη0 hζ3 hη3
  have hP3 := rotation_sub_zero_isBigO i
  let d : ℝ → (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ) := fun t ↦
    (stepW i t x (ζ t) (η t), fun r c ↦ rotation i t r c)
  have hd3 : (fun t : ℝ ↦ d t - d 0) =O[𝓝 0] (fun t ↦ t ^ 3) := by
    have hdataEq : (fun t : ℝ ↦ d t - d 0) =
        (fun t : ℝ ↦
          ((fun j : Fin 2 ↦ stepW i t x (ζ t) (η t) j -
              stepW i 0 x (ζ 0) (η 0) j),
            (fun r c : Fin 2 ↦ rotation i t r c - rotation i 0 r c))) := by
      funext t
      rfl
    rw [hdataEq]
    exact hW3.prod_left hP3
  -- The cubic factor perturbation tends to zero; the bracket is regular at that base.
  have hcubic : Tendsto (fun t : ℝ ↦ t ^ 3) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ t ^ 3) 0 := by fun_prop
    simpa [ContinuousAt] using hc
  have hd : Tendsto d (𝓝 0) (𝓝 (d 0)) :=
    tendsto_sub_nhds_zero_iff.mp (hd3.trans_tendsto hcubic)
  have hσ0 : stepV x ⬝ᵥ (d 0).1 ≠ 0 := by
    simp [d, hζ0, hη0, stepV_def, stepW_def]
  have hregular := (stageFromFactors_analyticAt x (d 0) hσ0).differentiableAt.isBigO_sub
  have hcore := (hregular.comp_tendsto hd).trans hd3
  have heq (t : ℝ) : cycleStage L κ i t x₀ x = stageFromFactors x (d t) := by
    simp only [cycleStage_apply, d, ζ, η]
    rw [stage_eq_fromFactors]
  have hstage : (fun t : ℝ ↦ cycleStage L κ i t x₀ x - cycleStage L κ i 0 x₀ x)
      =O[𝓝 0] (fun t ↦ t ^ 3) := by
    simpa only [Function.comp_def, ← heq] using hcore
  simpa only [cycleStage_zero] using hstage

/-- The quadratic Taylor jet
of a normalized stage is its constant limiting jet. -/
private lemma cycleStage_twoJet_eq_constant (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    FiniteTaylorJet.ofFunction ℝ 2 (fun t ↦ cycleStage L κ i t x₀ x) 0 =
      FiniteTaylorJet.ofFunction ℝ 2 (fun _ : ℝ ↦ leadingStage (limitAngle i) x) 0 := by
  -- An O(t³) perturbation is invisible to the order-two Peano jet.
  have hf : ContDiffAt ℝ 2 (fun t ↦ cycleStage L κ i t x₀ x) 0 :=
    (cycleStage_analyticAt_zero L κ i x₀ x).contDiffAt
  have hg : ContDiffAt ℝ 2 (fun _ : ℝ ↦ leadingStage (limitAngle i) x) 0 := contDiffAt_const
  have herr : (fun t : ℝ ↦ cycleStage L κ i (0 + t) x₀ x -
      (fun _ : ℝ ↦ leadingStage (limitAngle i) x) (0 + t)) =O[𝓝 0]
        (fun t ↦ t ^ (2 + 1)) := by
    simpa only [zero_add, Nat.reduceAdd] using cycleStage_sub_leading_isBigO L κ i x₀ x
  exact FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hf hg herr

/-- Every positive-order
scale derivative through order two of a normalized stage vanishes at zero. -/
private lemma cycleStage_iteratedFDeriv_eq_zero (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) (n : Fin 3) (hn : (n : ℕ) ≠ 0) :
    iteratedFDeriv ℝ (n : ℕ) (fun t ↦ cycleStage L κ i t x₀ x) 0 = 0 := by
  -- The jet comparison API cancels the nonzero factorial in each coefficient.
  have hderiv := (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 2
    (fun t ↦ cycleStage L κ i t x₀ x)
    (fun _ : ℝ ↦ leadingStage (limitAngle i) x) 0 0).mp
      (cycleStage_twoJet_eq_constant L κ i x₀ x) n
  -- A one-variable multilinear derivative is determined by its value at ones.
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_const_of_ne hn,
    Pi.zero_apply, zero_apply] using hderiv

/-- A normalized stage has zero first scale derivative at zero. -/
theorem cycleStage_firstIteratedFDeriv_eq_zero (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    iteratedFDeriv ℝ 1 (fun t ↦ cycleStage L κ i t x₀ x) 0 = 0 := by
  -- Select the linear derivative of the constant quadratic jet.
  exact cycleStage_iteratedFDeriv_eq_zero L κ i x₀ x 1 one_ne_zero

/-- A normalized stage has zero second scale derivative at zero. -/
theorem cycleStage_secondIteratedFDeriv_eq_zero (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (fun t ↦ cycleStage L κ i t x₀ x) 0 = 0 := by
  -- Select the quadratic derivative of the same constant jet.
  exact cycleStage_iteratedFDeriv_eq_zero L κ i x₀ x 2 two_ne_zero

end DFP.Polar.Normalized
