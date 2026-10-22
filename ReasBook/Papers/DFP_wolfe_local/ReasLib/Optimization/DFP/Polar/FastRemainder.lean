/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.FastContraction
public import ReasLib.Optimization.DFP.Polar.RestoringDrift

public section

noncomputable section

open Filter
open scoped Matrix Topology NNReal

namespace DFP.Polar.FastRemainder

open Normalized

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the normalized
stage as a function of its state, gradient-change vector, and rotation. -/
private def stageCore (x : ℝ × ℝ × ℝ)
    (d : (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  let X := RealSymmetric2.matrix x.1 x.2.1 x.2.2
  let v := stepV x
  let w := d.1
  let σ := v ⬝ᵥ w
  let R := Matrix.of d.2
  let Y := R * ((1 - σ⁻¹ • Matrix.vecMulVec w v) * X *
      (1 - σ⁻¹ • Matrix.vecMulVec v w) + σ⁻¹ • Matrix.vecMulVec w w) * R.transpose
  (Y 0 0, Y 0 1, Y 1 1)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the core uses
exactly the original canceled stage factors. -/
private theorem stage_eq_core (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stage i t x ζ η =
      stageCore x (stepW i t x ζ η, fun r c ↦ rotation i t r c) := by
  simp only [stage_apply, stageMatrix_def, stageSigma_def, stageCore]
  rfl

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the factored
stage preserves analytic state and factor germs at a nonzero secant scalar. -/
private theorem stageCoreAlong_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {X : E → ℝ × ℝ × ℝ}
    {d : E → (Fin 2 → ℝ) × (Fin 2 → Fin 2 → ℝ)} {z : E}
    (hX : AnalyticAt ℝ X z) (hd : AnalyticAt ℝ d z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z)
    (hσ : stepV (X z) ⬝ᵥ (d z).1 ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stageCore (X y) (d y)) z := by
  have hA : AnalyticAt ℝ (fun y ↦ (X y).1) z := analyticAt_fst.comp hX
  have hCV : AnalyticAt ℝ (fun y ↦ (X y).2) z := analyticAt_snd.comp hX
  have hC : AnalyticAt ℝ (fun y ↦ (X y).2.1) z := analyticAt_fst.comp hCV
  have hV : AnalyticAt ℝ (fun y ↦ (X y).2.2) z := analyticAt_snd.comp hCV
  have hW : AnalyticAt ℝ (fun y ↦ (d y).1) z := analyticAt_fst.comp hd
  have hR : AnalyticAt ℝ (fun y ↦ (d y).2) z := analyticAt_snd.comp hd
  have hW0 := analyticAt_pi_iff.mp hW 0
  have hW1 := analyticAt_pi_iff.mp hW 1
  have hR0 := analyticAt_pi_iff.mp hR 0
  have hR1 := analyticAt_pi_iff.mp hR 1
  have hR00 := analyticAt_pi_iff.mp hR0 0
  have hR01 := analyticAt_pi_iff.mp hR0 1
  have hR10 := analyticAt_pi_iff.mp hR1 0
  have hR11 := analyticAt_pi_iff.mp hR1 1
  have hv0 : AnalyticAt ℝ (fun y ↦ stepV (X y) 0) z := by
    simp only [stepV_def, Matrix.cons_val_zero]
    exact hSlope.neg
  have hv1 : AnalyticAt ℝ (fun y ↦ stepV (X y) 1) z := by
    simp only [stepV_def, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact analyticAt_const
  have hsecant : AnalyticAt ℝ (fun y ↦ stepV (X y) ⬝ᵥ (d y).1) z := by
    simp only [dotProduct, Fin.sum_univ_two]
    exact (hv0.mul hW0).add (hv1.mul hW1)
  have hinv := hsecant.inv hσ
  simp only [stageCore, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, RealSymmetric2.matrix_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  fun_prop

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the canceled
stage is analytic along regular analytic scale, state, and multiplier germs. -/
private theorem stageAlong_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (hτ : AnalyticAt ℝ τ z) (hX : AnalyticAt ℝ X z)
    (hζ : AnalyticAt ℝ ζ z) (hη : AnalyticAt ℝ η z)
    (hSlope : AnalyticAt ℝ (fun y ↦ slope (X y)) z) (hτ0 : τ z = 0)
    (hσ : stageSigma i (τ z) (X z) (ζ z) (η z) ≠ 0) :
    AnalyticAt ℝ (fun y ↦ stage i (τ y) (X y) (ζ y) (η y)) z := by
  have hAngle := (stageAngle_analyticAt i).comp_of_eq hτ hτ0
  have hSin := (sinFactor_analyticAt i).comp_of_eq hτ hτ0
  have hCot := (cotFactor_analyticAt i).comp_of_eq hτ hτ0
  have hW : AnalyticAt ℝ (fun y ↦ stepW i (τ y) (X y) (ζ y) (η y)) z := by
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases j
    · simp only [stepW_def, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simpa only [stepW_def, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hη
  have hR : AnalyticAt ℝ (fun y ↦ fun r c : Fin 2 ↦ rotation i (τ y) r c) z := by
    apply analyticAt_pi_iff.mpr
    intro r
    apply analyticAt_pi_iff.mpr
    intro c
    fin_cases r
    all_goals fin_cases c
    all_goals simp only [rotation_def, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  have hsecant : stepV (X z) ⬝ᵥ stepW i (τ z) (X z) (ζ z) (η z) ≠ 0 := by
    simpa only [stageSigma_def] using hσ
  simp only [stage_eq_core]
  exact stageCoreAlong_analyticAt hX (hW.prod hR) hSlope hsecant

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): a cycle stage
with its original fixed boundary feedback is jointly analytic in scale and
the updated state wherever the limiting off-diagonal coordinate is nonzero. -/
theorem cycleStage_joint_analyticAt (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) (hC : x.2.1 ≠ 0) :
    AnalyticAt ℝ
      (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleStage L κ i z.1 x₀ z.2) (0, x) := by
  have hτ : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.1) (0, x) := analyticAt_fst
  have hX : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x) := analyticAt_snd
  have hfb : AnalyticAt ℝ
      (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ feedback L κ z.1 x₀) (0, x) := by
    simp only [feedback_def]
    fun_prop (disch := assumption)
  have hSlope : AnalyticAt ℝ
      (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ slope z.2) (0, x) := by
    have hCV : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2) (0, x) :=
      analyticAt_snd.comp hX
    have hC' : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2.1) (0, x) :=
      analyticAt_fst.comp hCV
    have hV : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2.2) (0, x) :=
      analyticAt_snd.comp hCV
    simp only [slope_def]
    exact hV.div hC' hC
  fin_cases i
  · have hσ : stageSigma 0 0 x 1 (feedback L κ 0 x₀) ≠ 0 := by
      simp [feedback_def, stageSigma_def, stepV_def, stepW_def]
    simpa only [cycleStage_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] using
      stageAlong_analyticAt 0 hτ hX analyticAt_const hfb hSlope rfl hσ
  · have hσ : stageSigma 1 0 x (feedback L κ 0 x₀) 1 ≠ 0 := by
      simp [feedback_def, stageSigma_def, stepV_def, stepW_def]
    simpa only [cycleStage_apply, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using
      stageAlong_analyticAt 1 hτ hX hfb analyticAt_const hSlope rfl hσ

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the exact final
rescaling is jointly analytic at zero scale. -/
theorem rescale_joint_analyticAt (x : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ rescale z.1 z.2) (0, x) := by
  have hρ := rescaleFactor_analyticAt.comp_of_eq
    (analyticAt_fst : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.1) (0, x)) rfl
  have hX : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x) := analyticAt_snd
  have hA : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.1) (0, x) :=
    analyticAt_fst.comp hX
  have hCV : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2) (0, x) :=
    analyticAt_snd.comp hX
  have hC : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2.1) (0, x) :=
    analyticAt_fst.comp hCV
  have hV : AnalyticAt ℝ (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2.2.2) (0, x) :=
    analyticAt_snd.comp hCV
  simp only [rescale_apply]
  exact ((hρ.pow 2).mul hA).prod ((hρ.mul hC).prod hV)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): analytic maps
preserve a common asymptotic order between two germs with the same limit. -/
theorem analytic_comp_sub_isBigO {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {a : E}
    {p q : ℝ → E} {g : ℝ → ℝ} (hf : AnalyticAt ℝ f a)
    (hp : Tendsto p (𝓝 0) (𝓝 a)) (hq : Tendsto q (𝓝 0) (𝓝 a))
    (hpq : (fun t ↦ p t - q t) =O[𝓝 0] g) :
    (fun t ↦ f (p t) - f (q t)) =O[𝓝 0] g := by
  have h := hf.hasStrictFDerivAt.isBigO_sub.comp_tendsto (hp.prodMk_nhds hq)
  simpa only [Function.comp_def] using h.trans hpq

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): an analytic
one-variable germ with zero first and second derivatives has cubic variation. -/
theorem analytic_sub_value_isBigO_cube {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : ℝ → F} (hf : AnalyticAt ℝ f 0)
    (hfirst : iteratedFDeriv ℝ 1 f 0 = 0) (hsecond : iteratedFDeriv ℝ 2 f 0 = 0) :
    (fun t : ℝ ↦ f t - f 0) =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
  have hderiv1 : iteratedDeriv 1 f 0 = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hfirst]
    rfl
  have hderiv2 : iteratedDeriv 2 f 0 = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv, hsecond]
    rfl
  obtain ⟨q, hq, hformula⟩ := hf.exists_eq_sum_add_pow_mul 3
  have hfactor (t : ℝ) : f t - f 0 = t ^ 3 • q t := by
    have hvalue : f t = f 0 + t ^ 3 • q t := by
      simpa [Finset.sum_range_succ, hderiv1, hderiv2, iteratedDeriv_zero]
        using hformula t
    rw [hvalue]
    abel
  have hbound := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).smul
    (hq.continuousAt.isBigO_one ℝ)
  simpa only [hfactor, smul_eq_mul, mul_one] using hbound

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the original
two consecutive stages have no scale perturbation below cubic order. -/
theorem twoStep_sub_zero_isBigO (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    (fun t : ℝ ↦ twoStep L κ t x - twoStep L κ 0 x) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
  let y := cycleStage L κ 0 0 x x
  have hyC : y.2.1 ≠ 0 := by
    simpa only [y, cycleStage_zero] using hCNext
  have hfirst3 : (fun t : ℝ ↦ cycleStage L κ 0 t x x - y) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
    simpa only [y, cycleStage_zero] using
      FastContraction.cycleStage_sub_leading_isBigO L κ 0 x x
  have hfirst : Tendsto (fun t : ℝ ↦ cycleStage L κ 0 t x x) (𝓝 0) (𝓝 y) := by
    simpa only [ContinuousAt, y] using (cycleStage_analyticAt_zero L κ 0 x x).continuousAt
  have hp : Tendsto (fun t : ℝ ↦ (t, cycleStage L κ 0 t x x))
      (𝓝 0) (𝓝 (0, y)) := tendsto_id.prodMk_nhds hfirst
  have hq : Tendsto (fun t : ℝ ↦ (t, y)) (𝓝 0) (𝓝 (0, y)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hpq : (fun t : ℝ ↦ (t, cycleStage L κ 0 t x x) - (t, y)) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
    simpa only [Prod.mk_sub_mk, sub_self] using
      (Asymptotics.isBigO_zero (fun t : ℝ ↦ t ^ 3) (𝓝 0)).prod_left hfirst3
  have hstate3 := analytic_comp_sub_isBigO
    (cycleStage_joint_analyticAt L κ 1 x y hyC) hp hq hpq
  have hsecond3 : (fun t : ℝ ↦ cycleStage L κ 1 t x y - cycleStage L κ 1 0 x y)
      =O[𝓝 0] (fun t : ℝ ↦ t ^ 3) := by
    simpa only [cycleStage_zero] using
      FastContraction.cycleStage_sub_leading_isBigO L κ 1 x y
  simpa only [Function.comp_def, sub_add_sub_cancel, twoStep_def, y] using
    hstate3.add hsecond3

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the exact final
rescaling of a fixed state differs from that state by cubic order. -/
theorem rescale_sub_zero_isBigO (x : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ rescale t x - rescale 0 x) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
  have hρ3 := analytic_sub_value_isBigO_cube rescaleFactor_analyticAt
    rescaleFactor_firstIteratedFDeriv_eq_zero rescaleFactor_secondIteratedFDeriv_eq_zero
  have hρ : Tendsto rescaleFactor (𝓝 0) (𝓝 (rescaleFactor 0)) := by
    simpa only [ContinuousAt] using rescaleFactor_analyticAt.continuousAt
  have hf : AnalyticAt ℝ (fun r : ℝ ↦ (r ^ 2 * x.1, r * x.2.1, x.2.2))
      (rescaleFactor 0) := by
    fun_prop
  have h := (hf.differentiableAt.isBigO_sub.comp_tendsto hρ).trans hρ3
  simpa only [Function.comp_def, rescale_apply] using h

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the actual
composed and rescaled normalized map has pointwise cubic scale variation. -/
theorem map_sub_zero_isBigO (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    (fun t : ℝ ↦ Normalized.map L κ t x - Normalized.map L κ 0 x) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
  let y := twoStep L κ 0 x
  have htwo3 := twoStep_sub_zero_isBigO L κ x hCNext
  have htzero : Tendsto (fun t : ℝ ↦ t ^ 3) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ t ^ 3) 0 := by fun_prop
    simpa [ContinuousAt] using hc
  have htwo : Tendsto (fun t : ℝ ↦ twoStep L κ t x) (𝓝 0) (𝓝 y) :=
    tendsto_sub_nhds_zero_iff.mp (htwo3.trans_tendsto htzero)
  have hp : Tendsto (fun t : ℝ ↦ (t, twoStep L κ t x)) (𝓝 0) (𝓝 (0, y)) :=
    tendsto_id.prodMk_nhds htwo
  have hq : Tendsto (fun t : ℝ ↦ (t, y)) (𝓝 0) (𝓝 (0, y)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hpq : (fun t : ℝ ↦ (t, twoStep L κ t x) - (t, y)) =O[𝓝 0]
      (fun t : ℝ ↦ t ^ 3) := by
    simpa only [Prod.mk_sub_mk, sub_self, y] using
      (Asymptotics.isBigO_zero (fun t : ℝ ↦ t ^ 3) (𝓝 0)).prod_left htwo3
  have hstate3 := analytic_comp_sub_isBigO (rescale_joint_analyticAt y) hp hq hpq
  have hrescale3 := rescale_sub_zero_isBigO y
  simpa only [Function.comp_def, sub_add_sub_cancel, Normalized.map_def, y] using
    hstate3.add hrescale3

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the exact map
is analytic as a scale slice at every positive regular state. -/
theorem map_scale_analyticAt (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hCNext : 0 < (leadingStage (limitAngle 0) x).2.1) :
    AnalyticAt ℝ (fun t : ℝ ↦ Normalized.map L κ t x) 0 := by
  have hpath : AnalyticAt ℝ (fun t : ℝ ↦ (t, x)) 0 :=
    analyticAt_id.prod analyticAt_const
  have h := (map_analyticAt_zero L κ x hA hC hCNext).comp_of_eq hpath rfl
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the order-two
scale jet of the actual two-stage rescaled map is its constant zero-scale jet. -/
theorem map_twoJet_eq_constant (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hCNext : 0 < (leadingStage (limitAngle 0) x).2.1) :
    FiniteTaylorJet.ofFunction ℝ 2 (fun t ↦ Normalized.map L κ t x) 0 =
      FiniteTaylorJet.ofFunction ℝ 2 (fun _ : ℝ ↦ Normalized.map L κ 0 x) 0 := by
  have hf : ContDiffAt ℝ 2 (fun t ↦ Normalized.map L κ t x) 0 :=
    (map_scale_analyticAt L κ x hA hC hCNext).contDiffAt
  have herr : (fun t : ℝ ↦ Normalized.map L κ (0 + t) x -
      (fun _ : ℝ ↦ Normalized.map L κ 0 x) (0 + t)) =O[𝓝 0]
        (fun t : ℝ ↦ t ^ (2 + 1)) := by
    simpa only [zero_add, Nat.reduceAdd] using map_sub_zero_isBigO L κ x hCNext.ne'
  exact FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hf contDiffAt_const herr

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): every positive
scale derivative below cubic order of the exact normalized map vanishes. -/
theorem map_positiveIteratedFDeriv_eq_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : 0 < x.1) (hC : 0 < x.2.1)
    (hCNext : 0 < (leadingStage (limitAngle 0) x).2.1)
    (n : Fin 3) (hn : (n : ℕ) ≠ 0) :
    iteratedFDeriv ℝ (n : ℕ) (fun t ↦ Normalized.map L κ t x) 0 = 0 := by
  have hderiv := (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 2
    (fun t ↦ Normalized.map L κ t x) (fun _ : ℝ ↦ Normalized.map L κ 0 x) 0 0).mp
      (map_twoJet_eq_constant L κ x hA hC hCNext) n
  apply ContinuousMultilinearMap.ext_ring
  simpa only [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_const_of_ne hn,
    Pi.zero_apply, zero_apply] using hderiv

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): a uniform cubic
scalar jet with zero linear and quadratic coefficients gives one common cubic
bound on variation from the base value. -/
theorem uniformCubicSubBound {Θ F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Θ → ℝ → F} {J : Θ → FiniteTaylorJet ℝ ℝ F 3} {K : Set Θ}
    (hJ : FiniteTaylorJet.IsUniformOn f J 0 K)
    (hzero : ∀ θ ∈ K, (J θ).coeff 1 = 0 ∧ (J θ).coeff 2 = 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖f θ t - f θ 0‖ ≤ C * ‖t ^ 3‖ := by
  obtain ⟨B, hB, htop⟩ := hJ.boundedCoeff (3 : Fin 4)
  obtain ⟨δ, hδ, hrem⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound
    (hJ.remainder 1 zero_lt_one)
  refine ⟨B + 1, add_pos_of_nonneg_of_pos hB zero_lt_one, δ, hδ, ?_⟩
  intro θ hθ t ht
  have hconstant : (J θ).coeff (0 : Fin 4) (fun _ ↦ t) = f θ 0 := by
    have harg : (fun _ : Fin ((0 : Fin 4) : ℕ) ↦ t) = (fun _ ↦ (0 : ℝ)) := by
      simp only [Fin.val_zero]
      exact Subsingleton.elim _ _
    calc
      (J θ).coeff (0 : Fin 4) (fun _ ↦ t) =
          (J θ).coeff (0 : Fin 4) (fun _ ↦ 0) :=
        congrArg ((J θ).coeff (0 : Fin 4)) harg
      _ = (J θ).constantCoeff := (FiniteTaylorJet.constantCoeff_eq_coeff_zero (J θ)).symm
      _ = f θ 0 := (hJ.value_eq_constantCoeff hθ).symm
  have heval : (J θ).eval t = f θ 0 + (J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t) := by
    rw [FiniteTaylorJet.eval_eq_sum, Fin.sum_univ_four, (hzero θ hθ).1,
      (hzero θ hθ).2]
    simp only [zero_apply, add_zero, hconstant]
    rfl
  have htopBound : ‖(J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t)‖ ≤ B * ‖t ^ 3‖ := by
    calc
      ‖(J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t)‖ ≤
          ‖(J θ).coeff (3 : Fin 4)‖ * ∏ _i : Fin 3, ‖t‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ B * ∏ _i : Fin 3, ‖t‖ :=
        mul_le_mul_of_nonneg_right (htop θ hθ) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg t)
      _ = B * ‖t ^ 3‖ := by simp only [Finset.prod_const, Finset.card_fin, norm_pow]
  have hremBound : ‖(J θ).remainder (f θ) 0 t‖ ≤ ‖t ^ 3‖ := by
    simpa only [Real.rpow_natCast, one_mul, norm_pow] using hrem θ hθ t ht
  have hvalue : f θ t - f θ 0 =
      (J θ).remainder (f θ) 0 t + (J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t) := by
    rw [FiniteTaylorJet.remainder_def, zero_add, heval]
    abel
  rw [hvalue]
  calc
    ‖(J θ).remainder (f θ) 0 t + (J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t)‖ ≤
        ‖(J θ).remainder (f θ) 0 t‖ + ‖(J θ).coeff (3 : Fin 4) (fun _ : Fin 3 ↦ t)‖ :=
      norm_add_le _ _
    _ ≤ ‖t ^ 3‖ + B * ‖t ^ 3‖ := add_le_add hremBound htopBound
    _ = (B + 1) * ‖t ^ 3‖ := by ring

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): on any fixed
compact positive state set, the exact normalized map has one cubic scale
constant and radius for all states in the set. -/
theorem map_uniform_cubic_bound (L κ : ℝ) (K : Set (ℝ × ℝ × ℝ)) (hK : IsCompact K)
    (hA : ∀ x ∈ K, 0 < x.1) (hC : ∀ x ∈ K, 0 < x.2.1)
    (hCNext : ∀ x ∈ K, 0 < (leadingStage (limitAngle 0) x).2.1) :
    ∃ C > 0, ∃ δ > 0, ∀ x ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖Normalized.map L κ t x - Normalized.map L κ 0 x‖ ≤ C * ‖t ^ 3‖ := by
  have huniform := map_uniformJets L κ 3 K hK hA hC hCNext
  apply uniformCubicSubBound huniform
  intro x hx
  have hfirst : iteratedFDeriv ℝ 1 (fun t ↦ Normalized.map L κ t x) 0 = 0 :=
    map_positiveIteratedFDeriv_eq_zero L κ x (hA x hx) (hC x hx) (hCNext x hx) 1 one_ne_zero
  have hsecond : iteratedFDeriv ℝ 2 (fun t ↦ Normalized.map L κ t x) 0 = 0 :=
    map_positiveIteratedFDeriv_eq_zero L κ x (hA x hx) (hC x hx) (hCNext x hx) 2 two_ne_zero
  constructor
  · simp only [FiniteTaylorJet.coeff_ofFunction]
    norm_num only [Fin.val_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
    exact hfirst
  · simp only [FiniteTaylorJet.coeff_ofFunction]
    exact smul_eq_zero_of_right _ hsecond

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the original
even reference curve is Lipschitz on a neighborhood of `K₀`. -/
theorem evenState_locally_lipschitz :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 TwoCycle.kZero, LipschitzOnWith K TwoCycle.evenState s := by
  have hK : TwoCycle.kZero ∈ TwoCycle.normalizationSet :=
    mem_of_mem_nhds TwoCycle.normalizationSet_mem_nhds
  exact (TwoCycle.evenState_analyticAt TwoCycle.kZero hK
    TwoCycle.inverseParameter_contDiffAt_kZero).hasStrictFDerivAt.exists_lipschitzOnWith

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the reference
state and its first leading image have positive required diagonal entries. -/
theorem reference_positive :
    0 < TwoCycle.evenReference.1 ∧ 0 < TwoCycle.evenReference.2.1 ∧
      0 < (leadingStage (limitAngle 0) TwoCycle.evenReference).2.1 := by
  have hK : TwoCycle.kZero ∈ TwoCycle.normalizationSet :=
    mem_of_mem_nhds TwoCycle.normalizationSet_mem_nhds
  have hE := TwoCycle.evenState_mapsTo_positive hK
  have hO := TwoCycle.oddState_mapsTo_positive hK
  have hstage : leadingStage (limitAngle 0) TwoCycle.evenReference =
      TwoCycle.oddReference := by
    rw [limitAngle_zero, ← TwoCycle.evenState_kZero, TwoCycle.evenToOdd _ hK,
      TwoCycle.oddState_kZero]
  rw [hstage, ← TwoCycle.evenState_kZero, ← TwoCycle.oddState_kZero]
  exact ⟨hE.1, hE.2.1, hO.2.1⟩

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): one fixed closed
state ball lies in the positive regular domain of both leading stages. -/
theorem exists_regular_closedBall :
    ∃ r > 0, ∀ x ∈ Metric.closedBall TwoCycle.evenReference r,
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < (leadingStage (limitAngle 0) x).2.1 := by
  have hA : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.1) TwoCycle.evenReference :=
    continuous_fst.continuousAt
  have hC : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) TwoCycle.evenReference :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hV : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) TwoCycle.evenReference :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hCne : TwoCycle.evenReference.2.1 ≠ 0 := reference_positive.2.1.ne'
  have hnext : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (leadingStage (limitAngle 0) x).2.1)
      TwoCycle.evenReference := by
    simp only [leadingStage_apply]
    fun_prop (disch := assumption)
  have hregular : ∀ᶠ x : ℝ × ℝ × ℝ in 𝓝 TwoCycle.evenReference,
      0 < x.1 ∧ 0 < x.2.1 ∧ 0 < (leadingStage (limitAngle 0) x).2.1 := by
    filter_upwards [hA.eventually (Ioi_mem_nhds reference_positive.1),
      hC.eventually (Ioi_mem_nhds reference_positive.2.1),
      hnext.eventually (Ioi_mem_nhds reference_positive.2.2)] with x hxA hxC hxNext
    exact ⟨hxA, hxC, hxNext⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hregular
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro x hx
  exact hball ((Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hr))

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the complete
map has one cubic error constant and one scale threshold on a fixed compact
neighborhood of the reference even state. -/
theorem exists_uniform_map_cubic_bound (L κ : ℝ) :
    ∃ r > 0, ∃ C > 0, ∃ δ > 0,
      ∀ x ∈ Metric.closedBall TwoCycle.evenReference r, ∀ t : ℝ, ‖t‖ < δ →
        ‖Normalized.map L κ t x - Normalized.map L κ 0 x‖ ≤ C * ‖t ^ 3‖ := by
  obtain ⟨r, hr, hregular⟩ := exists_regular_closedBall
  obtain ⟨C, hC, δ, hδ, hbound⟩ := map_uniform_cubic_bound L κ
    (Metric.closedBall TwoCycle.evenReference r) (isCompact_closedBall _ _)
    (fun x hx ↦ (hregular x hx).1) (fun x hx ↦ (hregular x hx).2.1)
    (fun x hx ↦ (hregular x hx).2.2)
  exact ⟨r, hr, C, hC, δ, hδ, hbound⟩

open FastContraction

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the fast
coordinate projection as a continuous linear map. -/
def fastProjection : (ℝ × ℝ × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi
    ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)),
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the continuous
projection is the fast-coordinate map of the original normalized state. -/
theorem fastProjection_apply (x : ℝ × ℝ × ℝ) : fastProjection x = fastCoordinates x := by
  ext i
  fin_cases i
  all_goals simp [fastProjection, fastCoordinates_apply, ContinuousLinearMap.comp_apply,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the fast
projection does not increase the ordinary supremum norm. -/
theorem norm_fastProjection_le (x : ℝ × ℝ × ℝ) : ‖fastProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · simpa only [fastProjection_apply, fastCoordinates_apply, Fin.zero_eta,
      Fin.isValue, Matrix.cons_val_zero] using (norm_fst_le x.2).trans (norm_snd_le x)
  · simpa only [fastProjection_apply, fastCoordinates_apply, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      (norm_snd_le x.2).trans (norm_snd_le x)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the prescribed
fixed fast norm is bounded by a positive fixed multiple of the ordinary norm. -/
theorem fixedNorm_le_inverseOperator (u : Fin 2 → ℝ) :
    fixedNorm u ≤ (‖matrixOperator inverseBasis‖ + 1) * ‖u‖ := by
  have hbound := (matrixOperator inverseBasis).le_opNorm u
  calc
    fixedNorm u ≤ ‖matrixOperator inverseBasis‖ * ‖u‖ := by
      simpa only [fixedNorm_def, matrixOperator_apply] using hbound
    _ ≤ (‖matrixOperator inverseBasis‖ + 1) * ‖u‖ := by
      nlinarith [norm_nonneg u]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): transporting
the center to the output slow coordinate is Lipschitz on the original even
curve's local Lipschitz neighborhood. -/
theorem fixedNorm_fastError_sub_le {K : ℝ≥0} {s : Set ℝ}
    (hLip : LipschitzOnWith K TwoCycle.evenState s) (y z : ℝ × ℝ × ℝ)
    (hy : y.1 ∈ s) (hz : z.1 ∈ s) :
    fixedNorm (fastError y - fastError z) ≤
      (‖matrixOperator inverseBasis‖ + 1) * (1 + (K : ℝ)) * ‖y - z‖ := by
  have hcurve := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hy hz
  have hslow : ‖y.1 - z.1‖ ≤ ‖y - z‖ := norm_fst_le (y - z)
  have hcurveBound : ‖TwoCycle.evenState y.1 - TwoCycle.evenState z.1‖ ≤
      (K : ℝ) * ‖y - z‖ := hcurve.trans (mul_le_mul_of_nonneg_left hslow K.coe_nonneg)
  have hidentity : fastError y - fastError z =
      fastProjection (y - z) -
        fastProjection (TwoCycle.evenState y.1 - TwoCycle.evenState z.1) := by
    simp only [map_sub, fastProjection_apply, fastError_def]
    abel
  rw [hidentity]
  calc
    fixedNorm (fastProjection (y - z) -
        fastProjection (TwoCycle.evenState y.1 - TwoCycle.evenState z.1)) ≤
      (‖matrixOperator inverseBasis‖ + 1) *
        ‖fastProjection (y - z) -
          fastProjection (TwoCycle.evenState y.1 - TwoCycle.evenState z.1)‖ :=
      fixedNorm_le_inverseOperator _
    _ ≤ (‖matrixOperator inverseBasis‖ + 1) *
        (‖fastProjection (y - z)‖ +
          ‖fastProjection (TwoCycle.evenState y.1 - TwoCycle.evenState z.1)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _)
        (add_nonneg (norm_nonneg _) zero_le_one)
    _ ≤ (‖matrixOperator inverseBasis‖ + 1) *
        (‖y - z‖ + ‖TwoCycle.evenState y.1 - TwoCycle.evenState z.1‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (norm_fastProjection_le _) (norm_fastProjection_le _))
        (add_nonneg (norm_nonneg _) zero_le_one)
    _ ≤ (‖matrixOperator inverseBasis‖ + 1) * (‖y - z‖ + (K : ℝ) * ‖y - z‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hcurveBound)
        (add_nonneg (norm_nonneg _) zero_le_one)
    _ = (‖matrixOperator inverseBasis‖ + 1) * (1 + (K : ℝ)) * ‖y - z‖ := by ring

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the source
state with slow coordinate `A` and fast displacement `u` from the even curve. -/
def perturbedState (A : ℝ) (u : Fin 2 → ℝ) : ℝ × ℝ × ℝ :=
  (A, (TwoCycle.evenState A).2.1 + u 0, (TwoCycle.evenState A).2.2 + u 1)

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the coordinates
of the source state expressed using its fast projection and displacement. -/
theorem perturbedState_apply (A : ℝ) (u : Fin 2 → ℝ) :
    perturbedState A u =
      (A, (fastCoordinates (TwoCycle.evenState A) + u) 0,
        (fastCoordinates (TwoCycle.evenState A) + u) 1) := by
  simp only [perturbedState, fastCoordinates_apply, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): zero fast
displacement gives the genuine even cycle state. -/
theorem perturbedState_zero (A : ℝ) : perturbedState A 0 = TwoCycle.evenState A := by
  simp only [perturbedState, TwoCycle.evenState_apply, Pi.zero_apply, add_zero]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the source
fast displacement of the perturbed state is exactly its input `u`. -/
theorem fastError_perturbedState (A : ℝ) (u : Fin 2 → ℝ) :
    fastError (perturbedState A u) = u := by
  rw [fastError_def, perturbedState_apply, fastCoordinates_mk]
  simp only [add_sub_cancel_left]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the perturbed
source state is continuous at the reference cycle and zero displacement. -/
theorem continuousAt_perturbedState :
    ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ perturbedState z.1 z.2)
      (TwoCycle.kZero, 0) := by
  have hE := FastContraction.continuousAt_evenState.comp_of_eq
    (continuousAt_fst : ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ z.1) (TwoCycle.kZero, 0)) rfl
  have hC : ContinuousAt
      (fun z : ℝ × (Fin 2 → ℝ) ↦ (TwoCycle.evenState z.1).2.1) (TwoCycle.kZero, 0) :=
    (continuous_fst.comp continuous_snd).continuousAt.comp_of_eq hE rfl
  have hV : ContinuousAt
      (fun z : ℝ × (Fin 2 → ℝ) ↦ (TwoCycle.evenState z.1).2.2) (TwoCycle.kZero, 0) :=
    (continuous_snd.comp continuous_snd).continuousAt.comp_of_eq hE rfl
  simp only [perturbedState]
  fun_prop

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): at zero scale
the exact map fixes the genuine even reference curve. -/
theorem map_zero_evenState (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    Normalized.map L κ 0 (TwoCycle.evenState A) = TwoCycle.evenState A := by
  rw [FastContraction.map_zero, TwoCycle.evenToOdd A hA, TwoCycle.oddToEven A hA]

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the exact
zero-scale map fixes the explicit even reference state. -/
theorem map_zero_evenReference (L κ : ℝ) :
    Normalized.map L κ 0 TwoCycle.evenReference = TwoCycle.evenReference := by
  have hK : TwoCycle.kZero ∈ TwoCycle.normalizationSet :=
    mem_of_mem_nhds TwoCycle.normalizationSet_mem_nhds
  simpa only [TwoCycle.evenState_kZero] using map_zero_evenState L κ TwoCycle.kZero hK

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): a common
neighborhood keeps the input in a fixed compact state ball and both the input
and output slow coordinates in the original curve's Lipschitz neighborhood. -/
theorem eventually_input_and_output_near (L κ r : ℝ) (hr : 0 < r)
    (s : Set ℝ) (hs : s ∈ 𝓝 TwoCycle.kZero) :
    ∀ᶠ z : ℝ × (ℝ × (Fin 2 → ℝ)) in 𝓝 (0, (TwoCycle.kZero, 0)),
      perturbedState z.2.1 z.2.2 ∈ Metric.closedBall TwoCycle.evenReference r ∧
        (Normalized.map L κ z.1 (perturbedState z.2.1 z.2.2)).1 ∈ s ∧ z.2.1 ∈ s := by
  have hstate : ContinuousAt
      (fun z : ℝ × (ℝ × (Fin 2 → ℝ)) ↦ perturbedState z.2.1 z.2.2)
      (0, (TwoCycle.kZero, 0)) :=
    continuousAt_perturbedState.comp_of_eq continuousAt_snd rfl
  have hinput : ContinuousAt
      (fun z : ℝ × (ℝ × (Fin 2 → ℝ)) ↦ (z.1, perturbedState z.2.1 z.2.2))
      (0, (TwoCycle.kZero, 0)) := continuousAt_fst.prodMk hstate
  have hinput0 : (fun z : ℝ × (ℝ × (Fin 2 → ℝ)) ↦
      (z.1, perturbedState z.2.1 z.2.2)) (0, (TwoCycle.kZero, 0)) =
        (0, TwoCycle.evenReference) := by
    simp only [perturbedState_zero, TwoCycle.evenState_kZero]
  have hmap := (map_analyticAt_zero L κ TwoCycle.evenReference
    reference_positive.1 reference_positive.2.1 reference_positive.2.2).continuousAt.comp_of_eq
      hinput hinput0
  have houtput : ContinuousAt
      (fun z : ℝ × (ℝ × (Fin 2 → ℝ)) ↦
        (Normalized.map L κ z.1 (perturbedState z.2.1 z.2.2)).1)
      (0, (TwoCycle.kZero, 0)) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      continuousAt_fst.comp_of_eq hmap rfl
  have hsOutput : s ∈ 𝓝
      ((Normalized.map L κ 0 (perturbedState TwoCycle.kZero 0)).1) := by
    rw [perturbedState_zero, TwoCycle.evenState_kZero, map_zero_evenReference,
      TwoCycle.evenReference_def]
    exact hs
  have hsInput : Metric.closedBall TwoCycle.evenReference r ∈
      𝓝 (perturbedState TwoCycle.kZero 0) := by
    simpa only [perturbedState_zero, TwoCycle.evenState_kZero] using
      Metric.closedBall_mem_nhds TwoCycle.evenReference hr
  have hA : ContinuousAt (fun z : ℝ × (ℝ × (Fin 2 → ℝ)) ↦ z.2.1)
      (0, (TwoCycle.kZero, 0)) := (continuous_fst.comp continuous_snd).continuousAt
  filter_upwards [hstate.eventually hsInput, houtput.eventually hsOutput,
    hA.eventually hs] with z hx hy hAin
  exact ⟨hx, hy, hAin⟩

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): one slow radius
and one fast radius work before the feedback parameters are fixed; only the
cubic constant and scale threshold then depend on `L` and `κ`. -/
theorem uniformFastBoundFixedNeighborhood :
    ∃ r > 0, ∃ d > 0, ∀ L κ : ℝ, ∃ C₀ > 0, ∃ δ > 0,
      ∀ A : ℝ, |A - TwoCycle.kZero| < d →
        A ∈ TwoCycle.normalizationSet ∧
          ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
            fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
              (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3 := by
  obtain ⟨R, hR, hregular⟩ := exists_regular_closedBall
  obtain ⟨K, s, hs, hLip⟩ := evenState_locally_lipschitz
  obtain ⟨a, ha, hslowBall⟩ := Metric.mem_nhds_iff.mp hs
  let D := (‖matrixOperator inverseBasis‖ + 1) * (1 + (K : ℝ))
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hcompact : Metric.closedBall TwoCycle.evenReference R ∈
      𝓝 (perturbedState TwoCycle.kZero 0) := by
    simpa only [perturbedState_zero, TwoCycle.evenState_kZero] using
      Metric.closedBall_mem_nhds TwoCycle.evenReference hR
  obtain ⟨η, hη, hinput⟩ := Metric.eventually_nhds_iff.mp
    (continuousAt_perturbedState.eventually hcompact)
  obtain ⟨r₀, hr₀, hleading⟩ := exists_uniform_leadingCycle_contraction
  obtain ⟨b, hb, hzeroLeading⟩ := Metric.eventually_nhds_iff.mp hleading
  let B := ‖matrixOperator basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨min r₀ (η / (2 * B)), lt_min hr₀ (div_pos hη (mul_pos zero_lt_two hB)),
    min b (min (η / 2) (a / 4)),
    lt_min hb (lt_min (half_pos hη) (div_pos ha zero_lt_four)), ?_⟩
  intro L κ
  obtain ⟨C, hC, δ₀, hδ₀, hmap⟩ := map_uniform_cubic_bound L κ
    (Metric.closedBall TwoCycle.evenReference R) (isCompact_closedBall _ _)
    (fun x hx ↦ (hregular x hx).1) (fun x hx ↦ (hregular x hx).2.1)
    (fun x hx ↦ (hregular x hx).2.2)
  have hCOne : 0 < C + 1 := by linarith
  refine ⟨D * C, mul_pos hD hC, min δ₀ (min 1 (a / (4 * (C + 1)))),
    lt_min hδ₀ (lt_min zero_lt_one (div_pos ha (mul_pos zero_lt_four hCOne))), ?_⟩
  intro A hA
  have hAb : dist A TwoCycle.kZero < b := by
    simpa only [Real.dist_eq] using hA.trans_le (min_le_left _ _)
  have hAcontract := hzeroLeading hAb
  refine ⟨hAcontract.1, ?_⟩
  intro u hu t ht htsmall
  have hu₀ : fixedNorm u < r₀ := hu.trans_le (min_le_left _ _)
  have huη : fixedNorm u < η / (2 * B) := hu.trans_le (min_le_right _ _)
  have hnormu : ‖u‖ < η / 2 := by
    calc
      ‖u‖ ≤ ‖matrixOperator basisMatrix‖ * fixedNorm u :=
        norm_le_basisOperator_mul_fixedNorm u
      _ ≤ B * fixedNorm u := by
        apply mul_le_mul_of_nonneg_right _ (fixedNorm_nonneg u)
        dsimp only [B]
        linarith
      _ < B * (η / (2 * B)) := mul_lt_mul_of_pos_left huη hB
      _ = η / 2 := by field_simp
  have hAη : |A - TwoCycle.kZero| < η / 2 :=
    (hA.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hAa : dist A TwoCycle.kZero < a / 4 := by
    simpa only [Real.dist_eq] using
      (hA.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hdist : dist (A, u) (TwoCycle.kZero, 0) < η := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, dist_zero_right, max_lt_iff]
    exact ⟨hAη.trans (half_lt_self hη), hnormu.trans (half_lt_self hη)⟩
  have hinputMem := hinput hdist
  have htδ : ‖t‖ < δ₀ := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
    exact htsmall.trans_le (min_le_left _ _)
  have htOne : t < 1 :=
    (htsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htScale : t < a / (4 * (C + 1)) :=
    (htsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have htSquare : t ^ 2 ≤ 1 := pow_le_one₀ ht htOne.le
  have htCube : t ^ 3 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr htSquare)]
  have hsmallCubic : C * ‖t ^ 3‖ < a / 4 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 3)]
    calc
      C * t ^ 3 ≤ C * t := mul_le_mul_of_nonneg_left htCube hC.le
      _ ≤ (C + 1) * t := by nlinarith
      _ < (C + 1) * (a / (4 * (C + 1))) := mul_lt_mul_of_pos_left htScale hCOne
      _ = a / 4 := by field_simp
  have hmapBound := hmap _ hinputMem t htδ
  have hzeroFirst : (Normalized.map L κ 0 (perturbedState A u)).1 = A := by
    rw [map_zero_fst, perturbedState_apply]
  have hslowError :
      ‖(Normalized.map L κ t (perturbedState A u)).1 - A‖ ≤
        ‖Normalized.map L κ t (perturbedState A u) -
          Normalized.map L κ 0 (perturbedState A u)‖ := by
    have hfst := norm_fst_le (Normalized.map L κ t (perturbedState A u) -
      Normalized.map L κ 0 (perturbedState A u))
    simpa only [Prod.fst_sub, hzeroFirst] using hfst
  have houtputDist : dist (Normalized.map L κ t (perturbedState A u)).1 TwoCycle.kZero < a := by
    have hstep : dist (Normalized.map L κ t (perturbedState A u)).1 A < a / 4 := by
      simpa only [dist_eq_norm] using hslowError.trans_lt (hmapBound.trans_lt hsmallCubic)
    calc
      dist (Normalized.map L κ t (perturbedState A u)).1 TwoCycle.kZero ≤
          dist (Normalized.map L κ t (perturbedState A u)).1 A + dist A TwoCycle.kZero :=
        dist_triangle _ _ _
      _ < a / 4 + a / 4 := add_lt_add hstep hAa
      _ < a := by linarith
  have houtputMem : (Normalized.map L κ t (perturbedState A u)).1 ∈ s :=
    hslowBall (Metric.mem_ball.mpr houtputDist)
  have hquarter : a / 4 < a := by linarith
  have hinputSlowMem : A ∈ s :=
    hslowBall (Metric.mem_ball.mpr (hAa.trans hquarter))
  have hzeroSlow : (Normalized.map L κ 0 (perturbedState A u)).1 ∈ s := by
    rw [hzeroFirst]
    exact hinputSlowMem
  have htransport := fixedNorm_fastError_sub_le hLip
    (Normalized.map L κ t (perturbedState A u))
    (Normalized.map L κ 0 (perturbedState A u)) houtputMem hzeroSlow
  have hcubic : fixedNorm
      (fastError (Normalized.map L κ t (perturbedState A u)) -
        fastError (Normalized.map L κ 0 (perturbedState A u))) ≤ (D * C) * t ^ 3 := by
    calc
      fixedNorm
          (fastError (Normalized.map L κ t (perturbedState A u)) -
            fastError (Normalized.map L κ 0 (perturbedState A u))) ≤
        D * ‖Normalized.map L κ t (perturbedState A u) -
          Normalized.map L κ 0 (perturbedState A u)‖ := htransport
      _ ≤ D * (C * ‖t ^ 3‖) := mul_le_mul_of_nonneg_left hmapBound hD.le
      _ = (D * C) * t ^ 3 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 3)]
        ring
  have hzero : fixedNorm (fastError (Normalized.map L κ 0 (perturbedState A u))) ≤
      (3 / 4 : ℝ) * fixedNorm u := by
    rw [perturbedState_apply, fastError_map_zero]
    exact hAcontract.2 u hu₀
  calc
    fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) =
        fixedNorm (fastError (Normalized.map L κ 0 (perturbedState A u)) +
          (fastError (Normalized.map L κ t (perturbedState A u)) -
            fastError (Normalized.map L κ 0 (perturbedState A u)))) := by
      congr 1
      abel
    _ ≤ fixedNorm (fastError (Normalized.map L κ 0 (perturbedState A u))) +
        fixedNorm (fastError (Normalized.map L κ t (perturbedState A u)) -
          fastError (Normalized.map L κ 0 (perturbedState A u))) := fixedNorm_add_le _ _
    _ ≤ (3 / 4 : ℝ) * fixedNorm u + (D * C) * t ^ 3 := add_le_add hzero hcubic

/-- lem:polar-continuation (eq:polar-fast-bound), fast estimate: the exact
positive-scale map contracts the original fast error, centered at the output
slow coordinate, up to one common cubic scale error. All constants and the
state neighborhood are fixed before `j₀` is selected. -/
theorem uniformFastBound (L κ : ℝ) :
    ∃ C₀ > 0, ∃ r > 0, ∃ δ > 0, ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
          fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
            (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3 := by
  obtain ⟨r, hr, d, hd, hbound⟩ := uniformFastBoundFixedNeighborhood
  obtain ⟨C₀, hC₀, δ, hδ, hfast⟩ := hbound L κ
  refine ⟨C₀, hC₀, r, hr, δ, hδ, ?_⟩
  filter_upwards [Metric.ball_mem_nhds TwoCycle.kZero hd] with A hA
  have hsmall : |A - TwoCycle.kZero| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hA
  exact hfast A hsmall

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the displayed
source fast bound follows from the stronger cubic-error contraction by adding
its nonnegative quadratic displacement term. -/
theorem sourceFastBound (L κ : ℝ) :
    ∃ C₀ > 0, ∃ r > 0, ∃ δ > 0, ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
          fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
            (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3 + C₀ * fixedNorm u ^ 2 := by
  obtain ⟨C₀, hC₀, r, hr, δ, hδ, hbound⟩ := uniformFastBound L κ
  refine ⟨C₀, hC₀, r, hr, δ, hδ, ?_⟩
  filter_upwards [hbound] with A hA
  refine ⟨hA.1, ?_⟩
  intro u hu t ht htδ
  exact (hA.2 u hu t ht htδ).trans
    (le_add_of_nonneg_right (mul_nonneg hC₀.le (sq_nonneg (fixedNorm u))))

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): one explicit
slow neighborhood, fast radius, scale threshold, and strict contraction
factor control the actual fast error centered at the output `A₊`. -/
theorem uniformFastBoundOnNeighborhood (L κ : ℝ) :
    ∃ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ C₀ > 0, ∃ r > 0, ∃ δ > 0,
      ∃ U ∈ 𝓝 TwoCycle.kZero, ∀ A ∈ U,
        A ∈ TwoCycle.normalizationSet ∧
          ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
            fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
              γ * fixedNorm u + C₀ * t ^ 3 := by
  obtain ⟨C₀, hC₀, r, hr, δ, hδ, hbound⟩ := uniformFastBound L κ
  have hγ : (3 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  refine ⟨3 / 4, hγ, C₀, hC₀, r, hr, δ, hδ,
    {A : ℝ | A ∈ TwoCycle.normalizationSet ∧
      ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
        fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
          (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3}, hbound, ?_⟩
  intro A hA
  exact hA

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): after choosing
`ν*` near `baseAngle`, the common fast radius works on a neighborhood of the
actual center `K* = cycleK ν*`, for every fixed feedback choice. -/
theorem uniformFastBoundNearCycle :
    ∃ r > 0, ∀ᶠ νStar : ℝ in 𝓝 baseAngle,
      νStar ∈ TwoCycle.parameterSet ∧ ∀ L κ : ℝ,
        ∃ C₀ > 0, ∃ δ > 0, ∃ U ∈ 𝓝 (cycleK νStar), ∀ A ∈ U,
          A ∈ TwoCycle.normalizationSet ∧
            ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
              fixedNorm (fastError (Normalized.map L κ t (perturbedState A u))) ≤
                (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3 := by
  obtain ⟨r, hr, d, hd, hbound⟩ := uniformFastBoundFixedNeighborhood
  have htendsto : Tendsto cycleK (𝓝 baseAngle) (𝓝 TwoCycle.kZero) := by
    simpa only [ContinuousAt, TwoCycle.kZero_def] using
      TwoCycle.hasDerivAt_cycleK_baseAngle.continuousAt
  refine ⟨r, hr, ?_⟩
  filter_upwards [TwoCycle.parameterSet_mem_nhds,
    htendsto.eventually (Metric.ball_mem_nhds TwoCycle.kZero hd)] with νStar hν hcenter
  refine ⟨hν, ?_⟩
  intro L κ
  obtain ⟨C₀, hC₀, δ, hδ, hfast⟩ := hbound L κ
  refine ⟨C₀, hC₀, δ, hδ, Metric.ball TwoCycle.kZero d,
    Metric.isOpen_ball.mem_nhds hcenter, ?_⟩
  intro A hA
  have hsmall : |A - TwoCycle.kZero| < d := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hA
  exact hfast A hsmall

/-- Helper for lem:polar-continuation (eq:polar-fast-bound): the original
feedback `L = 4a/(9ν*)` and `κ = K*` satisfy the uniform fast estimate on a
neighborhood of `K*`, with the fast error centered at the actual output `A₊`. -/
theorem polarFastBound :
    ∃ r > 0, ∀ᶠ νStar : ℝ in 𝓝 baseAngle,
      νStar ∈ TwoCycle.parameterSet ∧
        ∃ C₀ > 0, ∃ δ > 0, ∃ U ∈ 𝓝 (cycleK νStar), ∀ A ∈ U,
          A ∈ TwoCycle.normalizationSet ∧
            ∀ u : Fin 2 → ℝ, fixedNorm u < r → ∀ t : ℝ, 0 ≤ t → t < δ →
              fixedNorm (fastError (Normalized.map (4 * baseAngle / (9 * νStar))
                (cycleK νStar) t (perturbedState A u))) ≤
                  (3 / 4 : ℝ) * fixedNorm u + C₀ * t ^ 3 := by
  obtain ⟨r, hr, hbound⟩ := uniformFastBoundNearCycle
  refine ⟨r, hr, ?_⟩
  filter_upwards [hbound] with νStar hν
  exact ⟨hν.1, hν.2 (4 * baseAngle / (9 * νStar)) (cycleK νStar)⟩

end DFP.Polar.FastRemainder
