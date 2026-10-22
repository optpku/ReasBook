/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Order.IntermediateValue
public import TR_LALM_theory.Proposition_4_1.Parameters

public section

open scoped ContDiff Gradient NNReal
open InnerProductSpace

namespace LALM.Correction.SourceWitness

/-- The canonical continuous linear equivalence between the scalar Euclidean space and `ℝ`. -/
noncomputable abbrev scalarEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)

/-- The scalar equivalence evaluates the unique coordinate. -/
theorem scalarEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) : scalarEquiv x = x 0 := by
  rfl

/-- The scalar equivalence preserves the norm. -/
theorem norm_scalarEquiv (x : EuclideanSpace ℝ (Fin 1)) : ‖scalarEquiv x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarEquiv, PiLp.equivOfUnique_apply, Real.sqrt_sq_eq_abs]

/-- The inverse scalar equivalence preserves the norm. -/
theorem norm_scalarEquiv_symm (r : ℝ) : ‖scalarEquiv.symm r‖ = ‖r‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarEquiv, PiLp.equivOfUnique_symm_apply, Real.sqrt_sq_eq_abs]

/-- The scalar constraint expression `r ↦ 2r - cos r`. -/
noncomputable def scalarConstraint (r : ℝ) : ℝ :=
  2 * r - Real.cos r

/-- The unit coordinate vector in the scalar Euclidean space. -/
noncomputable def unitVector : EuclideanSpace ℝ (Fin 1) :=
  scalarEquiv.symm 1

/-- The unit coordinate vector has norm one. -/
theorem norm_unitVector : ‖unitVector‖ = 1 := by
  rw [unitVector, norm_scalarEquiv_symm]
  norm_num

/-- The scalar coordinate is pairing with the unit coordinate vector. -/
noncomputable def coordinate : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  innerSL ℝ unitVector

/-- Pairing with the unit coordinate vector evaluates the unique coordinate. -/
theorem coordinate_eq (x : EuclideanSpace ℝ (Fin 1)) : coordinate x = scalarEquiv x := by
  simp [coordinate, unitVector, scalarEquiv, PiLp.equivOfUnique_symm_apply,
    PiLp.inner_apply]

/-- Every scalar Euclidean vector is its coordinate times the unit vector. -/
theorem coordinate_smul_unitVector (x : EuclideanSpace ℝ (Fin 1)) :
    coordinate x • unitVector = x := by
  apply scalarEquiv.injective
  rw [map_smul, coordinate_eq]
  simp [unitVector]

/-- Pairing after scalar multiplication of the unit vector is composition with the
scalar coordinate functional. -/
theorem toDual_smul_unitVector (r : ℝ) :
    (toDual ℝ (EuclideanSpace ℝ (Fin 1))) (r • unitVector) =
      (toDual ℝ ℝ) r ∘L coordinate := by
  ext x
  rw [toDual_apply_apply, ContinuousLinearMap.comp_apply, toDual_apply_apply,
    coordinate, innerSL_apply_apply, inner_smul_left]
  rw [starRingEnd_apply, star_trivial, Real.inner_apply]

/-- Lifting a scalar multiple through the unique coordinate is scalar multiplication
of the identity map. -/
theorem scalarLift_comp_coordinate (r : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ r).comp coordinate).smulRight unitVector =
      r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [mul_comm, mul_smul, coordinate_smul_unitVector]

/-- The objective `f(x) = sin x` from the source strictness witness. -/
noncomputable def objective (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  Real.sin (coordinate x)

/-- The constraint `c(x) = 2x - cos x` from the source strictness witness. -/
noncomputable def constraint (x : EuclideanSpace ℝ (Fin 1)) :
    EuclideanSpace ℝ (Fin 1) :=
  scalarConstraint (coordinate x) • unitVector

/-- The source objective has gradient `cos x` times the unit coordinate vector. -/
theorem hasGradientAt_objective (x : EuclideanSpace ℝ (Fin 1)) :
    HasGradientAt objective (Real.cos (coordinate x) • unitVector) x := by
  have hsin : HasGradientAt Real.sin (Real.cos (coordinate x)) (coordinate x) :=
    (Real.hasDerivAt_sin (coordinate x)).hasGradientAt'
  have hcomposed := hsin.hasFDerivAt.comp x coordinate.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [toDual_smul_unitVector]
  convert hcomposed using 1
  all_goals rfl

/-- The source objective gradient has its scalar coordinate formula. -/
theorem gradient_objective (x : EuclideanSpace ℝ (Fin 1)) :
    ∇ objective x = Real.cos (coordinate x) • unitVector :=
  (hasGradientAt_objective x).gradient

/-- The derivative of `r ↦ 2r - cos r` is `2 + sin r`. -/
theorem hasDerivAt_scalarConstraint (r : ℝ) :
    HasDerivAt scalarConstraint (2 + Real.sin r) r := by
  have hderiv := ((hasDerivAt_id r).const_mul 2).sub (Real.hasDerivAt_cos r)
  convert hderiv using 1
  · rfl
  · rfl
  · rfl
  · rw [mul_one, sub_neg_eq_add]

/-- The source constraint derivative is scalar multiplication by `2 + sin x`. -/
theorem hasFDerivAt_constraint (x : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt constraint
      ((2 + Real.sin (scalarEquiv x)) •
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1))) x := by
  have hscalar :=
    (hasDerivAt_scalarConstraint (coordinate x)).hasFDerivAt.comp x coordinate.hasFDerivAt
  have hlift := hscalar.smul_const unitVector
  refine hlift.congr_fderiv ?_
  rw [coordinate_eq]
  exact scalarLift_comp_coordinate _

/-- The source constraint Fréchet derivative has its scalar-multiplication formula. -/
theorem fderiv_constraint (x : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ constraint x =
      (2 + Real.sin (scalarEquiv x)) •
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) :=
  (hasFDerivAt_constraint x).fderiv

/-- The source constraint gradient is scalar multiplication by `2 + sin x`. -/
theorem constraintGradient_eq (x : EuclideanSpace ℝ (Fin 1)) :
    EqualityConstrained.constraintGradient constraint x =
      (2 + Real.sin (scalarEquiv x)) •
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  rw [EqualityConstrained.constraintGradient_def, fderiv_constraint]
  simp

/-- The scalar coordinate preserves distances. -/
theorem dist_coordinate (x y : EuclideanSpace ℝ (Fin 1)) :
    dist (coordinate x) (coordinate y) = dist x y := by
  calc
    dist (coordinate x) (coordinate y) = ‖coordinate (x - y)‖ := by
      rw [dist_eq_norm, map_sub]
    _ = ‖scalarEquiv (x - y)‖ := by rw [coordinate_eq]
    _ = ‖x - y‖ := norm_scalarEquiv _
    _ = dist x y := by rw [dist_eq_norm]

/-- The scalar equivalence preserves distances. -/
theorem dist_scalarEquiv (x y : EuclideanSpace ℝ (Fin 1)) :
    dist (scalarEquiv x) (scalarEquiv y) = dist x y := by
  calc
    dist (scalarEquiv x) (scalarEquiv y) = ‖scalarEquiv (x - y)‖ := by
      rw [dist_eq_norm, map_sub]
    _ = ‖x - y‖ := norm_scalarEquiv _
    _ = dist x y := by rw [dist_eq_norm]

/-- The source objective is smooth on the whole scalar Euclidean space. -/
theorem contDiff_objective : ContDiff ℝ ∞ objective := by
  have hcoordinate : ContDiff ℝ ∞ (fun x => coordinate x) := coordinate.contDiff
  convert hcoordinate.sin using 1
  all_goals rfl

/-- The source constraint is smooth on the whole scalar Euclidean space. -/
theorem contDiff_constraint : ContDiff ℝ ∞ constraint := by
  have hcoordinate : ContDiff ℝ ∞ (fun x => coordinate x) := coordinate.contDiff
  have hscalar := (hcoordinate.const_smul 2).sub hcoordinate.cos
  have hlift := hscalar.smul_const unitVector
  convert hlift using 1
  funext x
  simp [constraint, scalarConstraint]

/-- The source objective is differentiable on the full source regularity region. -/
theorem differentiableOn_objective : DifferentiableOn ℝ objective Set.univ := by
  apply Differentiable.differentiableOn
  apply contDiff_objective.differentiable
  simp

/-- The source constraint is differentiable on the full source regularity region. -/
theorem differentiableOn_constraint : DifferentiableOn ℝ constraint Set.univ := by
  apply Differentiable.differentiableOn
  apply contDiff_constraint.differentiable
  simp

/-- The source objective is globally bounded below by `-1`. -/
theorem objective_lower_bound (x : EuclideanSpace ℝ (Fin 1)) :
    -1 ≤ objective x := by
  exact Real.neg_one_le_sin (coordinate x)

/-- The norm of the source objective gradient is at most one. -/
theorem norm_gradient_objective_le_one (x : EuclideanSpace ℝ (Fin 1)) :
    ‖∇ objective x‖ ≤ 1 := by
  rw [gradient_objective, norm_smul, norm_unitVector, mul_one, Real.norm_eq_abs]
  exact Real.abs_cos_le_one (coordinate x)

/-- The source objective gradient is globally one-Lipschitz. -/
theorem lipschitz_gradient_objective : LipschitzWith 1 (∇ objective) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [gradient_objective, gradient_objective, dist_eq_norm, ← sub_smul, norm_smul,
    norm_unitVector, mul_one, Real.norm_eq_abs]
  calc
    |Real.cos (coordinate x) - Real.cos (coordinate y)| ≤
        |coordinate x - coordinate y| :=
      Real.abs_cos_sub_cos_le (coordinate x) (coordinate y)
    _ = dist (coordinate x) (coordinate y) := (Real.dist_eq _ _).symm
    _ = dist x y := dist_coordinate x y

/-- The source constraint-gradient operator has norm at most three. -/
theorem norm_constraintGradient_le_three (x : EuclideanSpace ℝ (Fin 1)) :
    ‖EqualityConstrained.constraintGradient constraint x‖ ≤ 3 := by
  have hsinLower := Real.neg_one_le_sin (scalarEquiv x)
  have hsinUpper := Real.sin_le_one (scalarEquiv x)
  have hcoefficientNonneg : 0 ≤ 2 + Real.sin (scalarEquiv x) := by linarith
  rw [constraintGradient_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hcoefficientNonneg]
  simp only [ContinuousLinearMap.norm_id, mul_one]
  linarith

/-- The source constraint-gradient operator is globally one-Lipschitz. -/
theorem lipschitz_constraintGradient :
    LipschitzWith 1 (EqualityConstrained.constraintGradient constraint) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [constraintGradient_eq, constraintGradient_eq, dist_eq_norm, ← sub_smul,
    norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
  have htrig := Real.abs_sin_sub_sin_le (scalarEquiv x) (scalarEquiv y)
  have hdistance : |scalarEquiv x - scalarEquiv y| = dist x y := by
    rw [← Real.dist_eq, dist_scalarEquiv]
  rw [hdistance] at htrig
  convert htrig using 1
  all_goals ring_nf

/-- The source constraint-gradient operator has global lower modulus one. -/
theorem constraintGradient_lower_bound (x u : EuclideanSpace ℝ (Fin 1)) :
    ‖u‖ ≤ ‖EqualityConstrained.constraintGradient constraint x u‖ := by
  have hsinLower := Real.neg_one_le_sin (scalarEquiv x)
  have hcoefficientNonneg : 0 ≤ 2 + Real.sin (scalarEquiv x) := by linarith
  rw [constraintGradient_eq, smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hcoefficientNonneg, ContinuousLinearMap.id_apply]
  nlinarith [norm_nonneg u]

/-- The unit source LICQ modulus has the form required by the regularity constructor. -/
theorem regularity_licqLowerBound (x : EuclideanSpace ℝ (Fin 1))
    (_ : x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))))
    (u : EuclideanSpace ℝ (Fin 1)) :
    (1 : NNRealˣ) * ‖u‖ ≤ ‖EqualityConstrained.constraintGradient constraint x u‖ := by
  simpa using constraintGradient_lower_bound x u

/-- Three is positive as a nonnegative-real regularity constant. -/
theorem three_nnreal_pos : (0 : ℝ≥0) < 3 := by norm_num

/-- The global source problem satisfies Assumption 2.1 with
`G = L_f = L_c = σ = 1`, `M = 3`, and objective lower bound `-1`. -/
noncomputable def regularity : EqualityConstrained.Regularity objective constraint :=
  { region := Set.univ
    objectiveLower := -1
    gradientBound := 1
    gradientLipschitz := 1
    constraintGradientBound := 3
    constraintGradientLipschitz := 1
    licqModulus := 1
    nonempty_region := Set.univ_nonempty
    isOpen_region := isOpen_univ
    gradientBound_pos := zero_lt_one
    gradientLipschitz_pos := zero_lt_one
    constraintGradientBound_pos := three_nnreal_pos
    constraintGradientLipschitz_pos := zero_lt_one
    differentiableOn_objective := differentiableOn_objective
    differentiableOn_constraint := differentiableOn_constraint
    objectiveLower_le := fun x _ => objective_lower_bound x
    norm_gradient_le := fun x _ => norm_gradient_objective_le_one x
    lipschitzOn_gradient := lipschitz_gradient_objective.lipschitzOnWith
    norm_constraintGradient_le := fun x _ => norm_constraintGradient_le_three x
    lipschitzOn_constraintGradient := lipschitz_constraintGradient.lipschitzOnWith
    licqLowerBound := regularity_licqLowerBound }

/-- The source regularity region is all of the scalar Euclidean space. -/
theorem regularity_region : regularity.region = Set.univ := by
  rfl

/-- The source regularity constants are exactly the constants stated in the paper. -/
theorem regularity_constants :
    regularity.objectiveLower = -1 ∧ regularity.gradientBound = 1 ∧
      regularity.gradientLipschitz = 1 ∧ regularity.constraintGradientBound = 3 ∧
      regularity.constraintGradientLipschitz = 1 ∧ regularity.licqModulus = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The scalar source constraint is continuous. -/
theorem continuous_scalarConstraint : Continuous scalarConstraint := by
  rw [continuous_iff_continuousAt]
  intro r
  exact (hasDerivAt_scalarConstraint r).continuousAt

/-- The scalar source constraint `r ↦ 2r - cos r` is strictly increasing. -/
theorem strictMono_scalarConstraint : StrictMono scalarConstraint := by
  intro x y hxy
  have hcos := Real.abs_cos_sub_cos_le y x
  have hcosUpper : Real.cos y - Real.cos x ≤ y - x := by
    calc
      Real.cos y - Real.cos x ≤ |Real.cos y - Real.cos x| := le_abs_self _
      _ ≤ |y - x| := hcos
      _ = y - x := abs_of_pos (sub_pos.mpr hxy)
  simp only [scalarConstraint]
  linarith

/-- The scalar source constraint is nonpositive at zero. -/
theorem scalarConstraint_zero_nonpos : scalarConstraint 0 ≤ 0 := by
  norm_num [scalarConstraint]

/-- The scalar source constraint is nonnegative at one half. -/
theorem scalarConstraint_half_nonneg : 0 ≤ scalarConstraint (1 / 2) := by
  have hcos := Real.cos_le_one (1 / 2)
  simp only [scalarConstraint]
  norm_num at hcos ⊢
  linarith

/-- The scalar source constraint has a zero. -/
theorem exists_scalarRoot : ∃ r : ℝ, scalarConstraint r = 0 := by
  have hzeroInRange : 0 ∈ Set.range scalarConstraint :=
    mem_range_of_exists_le_of_exists_ge continuous_scalarConstraint
      ⟨0, scalarConstraint_zero_nonpos⟩ ⟨1 / 2, scalarConstraint_half_nonneg⟩
  exact hzeroInRange

/-- The scalar source constraint has a unique zero. -/
theorem existsUnique_scalarRoot : ∃! r : ℝ, scalarConstraint r = 0 := by
  obtain ⟨r, hr⟩ := exists_scalarRoot
  refine ⟨r, hr, ?_⟩
  intro y hy
  exact strictMono_scalarConstraint.injective (hy.trans hr.symm)

/-- The unique scalar root used for the source initialization. -/
noncomputable def scalarRoot : ℝ :=
  Classical.choose exists_scalarRoot

/-- The chosen scalar root satisfies the scalar constraint. -/
theorem scalarConstraint_scalarRoot : scalarConstraint scalarRoot = 0 :=
  Classical.choose_spec exists_scalarRoot

/-- The source initial point is the scalar root along the unit coordinate vector. -/
noncomputable def initialPoint : EuclideanSpace ℝ (Fin 1) :=
  scalarRoot • unitVector

/-- The source initial point has coordinate equal to the scalar root. -/
theorem coordinate_initialPoint : coordinate initialPoint = scalarRoot := by
  rw [coordinate_eq, initialPoint, map_smul]
  simp [unitVector]

/-- The source initial point is feasible. -/
theorem constraint_initialPoint : constraint initialPoint = 0 := by
  rw [constraint, coordinate_initialPoint, scalarConstraint_scalarRoot, zero_smul]

/-- The source constraint has the stated unique feasible point. -/
theorem existsUnique_constraintRoot : ∃! x : EuclideanSpace ℝ (Fin 1), constraint x = 0 := by
  refine ⟨initialPoint, constraint_initialPoint, ?_⟩
  intro x hx
  have hscalar : scalarConstraint (coordinate x) = 0 := by
    have himage := congrArg (fun z => scalarEquiv z) hx
    simpa [constraint, unitVector] using himage
  have hcoordinate : coordinate x = scalarRoot :=
    strictMono_scalarConstraint.injective
      (hscalar.trans scalarConstraint_scalarRoot.symm)
  rw [← coordinate_smul_unitVector x, hcoordinate, initialPoint]

/-- The source initial multiplier is `4` times the unit coordinate vector. -/
noncomputable def initialMultiplier : EuclideanSpace ℝ (Fin 1) :=
  (4 : ℝ) • unitVector

/-- The source initial multiplier has norm exactly four. -/
theorem norm_initialMultiplier : ‖initialMultiplier‖ = 4 := by
  rw [initialMultiplier, norm_smul, norm_unitVector, mul_one]
  norm_num

/-- The nonnegative real `1 / 20` is nonzero. -/
theorem sourceDelta_ne : (1 / 20 : ℝ≥0) ≠ 0 := by norm_num

/-- The nonnegative real `50` is nonzero. -/
theorem sourceBeta_ne : (50 : ℝ≥0) ≠ 0 := by norm_num

/-- The nonnegative real `2200` is nonzero. -/
theorem sourceRho_ne : (2200 : ℝ≥0) ≠ 0 := by norm_num

/-- The nonnegative real `4` is nonzero. -/
theorem sourceMultiplierBound_ne : (4 : ℝ≥0) ≠ 0 := by norm_num

/-- The source corrected step radius `Δ = 1 / 20`. -/
noncomputable def sourceDelta : NNRealˣ :=
  Units.mk0 (1 / 20 : ℝ≥0) sourceDelta_ne

/-- The source proximal parameter `β = 50`. -/
noncomputable def sourceBeta : NNRealˣ :=
  Units.mk0 (50 : ℝ≥0) sourceBeta_ne

/-- The source penalty parameter `ρ = 2200`. -/
noncomputable def sourceRho : NNRealˣ :=
  Units.mk0 (2200 : ℝ≥0) sourceRho_ne

/-- The source multiplier bound `Λ = 4`. -/
noncomputable def sourceMultiplierBound : NNRealˣ :=
  Units.mk0 (4 : ℝ≥0) sourceMultiplierBound_ne

/-- The real value of the source corrected step radius is `1 / 20`. -/
theorem sourceDelta_eq : (sourceDelta : ℝ) = 1 / 20 := by
  norm_num [sourceDelta]

/-- The real value of the source proximal parameter is `50`. -/
theorem sourceBeta_eq : (sourceBeta : ℝ) = 50 := by
  norm_num [sourceBeta]

/-- The real value of the source penalty parameter is `2200`. -/
theorem sourceRho_eq : (sourceRho : ℝ) = 2200 := by
  norm_num [sourceRho]

/-- The real value of the source multiplier bound is `4`. -/
theorem sourceMultiplierBound_eq : (sourceMultiplierBound : ℝ) = 4 := by
  norm_num [sourceMultiplierBound]

/-- The source correction step constant is `1 / 2`. -/
theorem sourceStepConstant_eq : stepConstant regularity = 1 / 2 := by
  rw [stepConstant_def]
  norm_num [regularity]

/-- The source correction error constant is `1 / 8`. -/
theorem sourceErrorConstant_eq : errorConstant regularity = 1 / 8 := by
  rw [errorConstant_def]
  norm_num [regularity]

/-- The source corrected-error factor is `1 / 3200`. -/
theorem sourceErrorFactor_eq : errorFactor regularity sourceDelta = 1 / 3200 := by
  rw [errorFactor_def, sourceErrorConstant_eq, sourceDelta_eq]
  norm_num

/-- The source displacement factor is `41 / 40`. -/
theorem sourceDisplacementFactor_eq :
    displacementFactor regularity sourceDelta = 41 / 40 := by
  rw [displacementFactor_def, sourceStepConstant_eq, sourceDelta_eq]
  norm_num

/-- The source corrected primal constant is `16033 / 320`. -/
theorem sourcePrimalConstant_eq :
    primalConstant regularity sourceDelta sourceBeta sourceRho = 16033 / 320 := by
  rw [primalConstant_def, sourceErrorFactor_eq, sourceDelta_eq, sourceBeta_eq,
    sourceRho_eq]
  norm_num [regularity]

/-- The source corrected primal comparison constant is `17673 / 320`. -/
theorem sourcePrimalComparisonConstant_eq :
    primalComparisonConstant regularity sourceDelta sourceBeta sourceRho
      sourceMultiplierBound = 17673 / 320 := by
  rw [primalComparisonConstant_def, sourcePrimalConstant_eq,
    sourceDisplacementFactor_eq, sourceMultiplierBound_eq]
  norm_num [regularity]

/-- The source corrected multiplier-radius expression is strictly below four. -/
theorem sourceParameterBound_lt :
    ((regularity.gradientBound + sourceBeta * sourceDelta +
      sourceRho * regularity.constraintGradientBound *
        errorFactor regularity sourceDelta * sourceDelta ^ 2) /
        regularity.licqModulus : ℝ) < sourceMultiplierBound := by
  rw [sourceErrorFactor_eq, sourceDelta_eq, sourceBeta_eq, sourceRho_eq,
    sourceMultiplierBound_eq]
  norm_num [regularity]

/-- The source corrected comparison expression is strictly below `1 / 20`. -/
theorem sourceComparisonBound_lt :
    (regularity.gradientBound / sourceBeta +
      3 * regularity.constraintGradientBound * sourceMultiplierBound /
        (sourceBeta + sourceRho * regularity.licqModulus ^ 2) : ℝ) < sourceDelta := by
  rw [sourceDelta_eq, sourceBeta_eq, sourceRho_eq, sourceMultiplierBound_eq]
  norm_num [regularity]

/-- The source corrected model constant is strictly below `6 / 5`. -/
theorem sourceModelConstant_lt :
    modelConstant regularity sourceDelta sourceRho sourceMultiplierBound < 6 / 5 := by
  rw [modelConstant_def, sourceStepConstant_eq, sourceErrorFactor_eq,
    sourceDisplacementFactor_eq, sourceDelta_eq, sourceRho_eq,
    sourceMultiplierBound_eq]
  norm_num [regularity]

/-- The source corrected multiplier-primal expression is strictly below `2008`. -/
theorem sourceMultiplierPrimalExpression_lt :
    8 * multiplierPrimalConstant regularity sourceDelta sourceBeta sourceRho
      sourceMultiplierBound / sourceBeta < 2008 := by
  rw [multiplierPrimalConstant_def, sourcePrimalConstant_eq,
    sourcePrimalComparisonConstant_eq, sourceBeta_eq]
  have hmax : ((16033 : ℝ) / 320) ^ 2 ≤ ((17673 : ℝ) / 320) ^ 2 := by
    norm_num
  rw [max_eq_right hmax]
  norm_num [regularity]

/-- The first corrected admissibility inequality holds for the source tuple. -/
theorem sourceParameterBound_le :
    ((regularity.gradientBound + sourceBeta * sourceDelta +
      sourceRho * regularity.constraintGradientBound *
        errorFactor regularity sourceDelta * sourceDelta ^ 2) /
        regularity.licqModulus : ℝ) ≤ sourceMultiplierBound :=
  sourceParameterBound_lt.le

/-- The second corrected admissibility inequality holds for the source tuple. -/
theorem sourceComparisonBound_le :
    (regularity.gradientBound / sourceBeta +
      3 * regularity.constraintGradientBound * sourceMultiplierBound /
        (sourceBeta + sourceRho * regularity.licqModulus ^ 2) : ℝ) ≤ sourceDelta :=
  sourceComparisonBound_lt.le

/-- The corrected source model constant is at most three eighths of `β`. -/
theorem sourceModelConstant_le :
    modelConstant regularity sourceDelta sourceRho sourceMultiplierBound ≤
      3 * sourceBeta / 8 := by
  have hthreshold : (6 : ℝ) / 5 ≤ 3 * sourceBeta / 8 := by
    rw [sourceBeta_eq]
    norm_num
  exact (lt_of_lt_of_le sourceModelConstant_lt hthreshold).le

/-- The corrected source penalty dominates the multiplier-primal expression. -/
theorem sourceMultiplierPrimalExpression_le :
    8 * multiplierPrimalConstant regularity sourceDelta sourceBeta sourceRho
      sourceMultiplierBound / sourceBeta ≤ sourceRho := by
  have hthreshold : (2008 : ℝ) ≤ sourceRho := by
    rw [sourceRho_eq]
    norm_num
  exact (lt_of_lt_of_le sourceMultiplierPrimalExpression_lt hthreshold).le

/-- The exact source tuple is a corrected admissible-parameter certificate. -/
noncomputable def correctedAdmissibleParameters : AdmissibleParameters regularity :=
  { delta := sourceDelta
    beta := sourceBeta
    rho := sourceRho
    multiplierBound := sourceMultiplierBound
    parameterBound_le := sourceParameterBound_le
    comparisonBound_le := sourceComparisonBound_le
    modelConstant_le := sourceModelConstant_le
    multiplierPrimalConstant_le := sourceMultiplierPrimalExpression_le }

/-- The source multiplier initialization obeys `Λ = 4`. -/
theorem sourceInitialMultiplierBound :
    ‖initialMultiplier‖ ≤ (correctedAdmissibleParameters.multiplierBound : ℝ) := by
  rw [norm_initialMultiplier]
  norm_num [correctedAdmissibleParameters, sourceMultiplierBound]

/-- Feasibility of the unique root makes the source initial residual vanish. -/
theorem sourceInitialResidualBound :
    (correctedAdmissibleParameters.rho : ℝ) * ‖constraint initialPoint‖ ≤
      correctedAdmissibleParameters.multiplierBound := by
  rw [constraint_initialPoint, norm_zero, mul_zero]
  positivity

/-- The exact source tuple satisfies the corrected initialization conditions. -/
noncomputable def correctedParameters :
    Parameters regularity initialPoint initialMultiplier :=
  { toAdmissibleParameters := correctedAdmissibleParameters
    norm_multiplier₀_le := sourceInitialMultiplierBound
    initialResidual_le := sourceInitialResidualBound }

/-- The corrected initialized certificate has the exact four source coordinates. -/
theorem correctedParameters_coordinates :
    correctedParameters.delta = sourceDelta ∧
      correctedParameters.beta = sourceBeta ∧
      correctedParameters.rho = sourceRho ∧
      correctedParameters.multiplierBound = sourceMultiplierBound := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Any base certificate at the source proximal and penalty parameters would have
multiplier bound at least four. -/
theorem baseMultiplierBound_ge_four
    (base : LALM.Parameters regularity initialPoint initialMultiplier) :
    (4 : ℝ) ≤ base.multiplierBound := by
  rw [← norm_initialMultiplier]
  exact base.norm_multiplier₀_le

/-- Any base certificate at `β = 50` and `ρ = 2200` would have
`Δ_base ≥ 9 / 250`. -/
theorem baseDelta_ge_nine_div_twoFifty
    (base : LALM.Parameters regularity initialPoint initialMultiplier)
    (hbeta : base.beta = sourceBeta) (hrho : base.rho = sourceRho) :
    (9 : ℝ) / 250 ≤ base.delta := by
  have hcomparison := base.comparisonBound_le
  have hmultiplier := baseMultiplierBound_ge_four base
  have hbetaReal : (base.beta : ℝ) = 50 := by rw [hbeta, sourceBeta_eq]
  have hrhoReal : (base.rho : ℝ) = 2200 := by rw [hrho, sourceRho_eq]
  rw [hbetaReal, hrhoReal] at hcomparison
  norm_num [regularity] at hcomparison
  nlinarith

/-- No base initialized certificate exists at the exact source values
`β = 50` and `ρ = 2200`. -/
theorem noBaseParametersAtSource
    (base : LALM.Parameters regularity initialPoint initialMultiplier)
    (hbeta : base.beta = sourceBeta) (hrho : base.rho = sourceRho) : False := by
  have hdelta := baseDelta_ge_nine_div_twoFifty base hbeta hrho
  have hbetaReal : (base.beta : ℝ) = 50 := by rw [hbeta, sourceBeta_eq]
  have hrhoReal : (base.rho : ℝ) = 2200 := by rw [hrho, sourceRho_eq]
  have hprimal :
      LALM.primalConstant regularity base.delta base.beta base.rho =
        50 + 3300 * (base.delta : ℝ) := by
    rw [LALM.primalConstant_def, hbetaReal, hrhoReal,
      LALM.linearizationConstant_def]
    norm_num [regularity]
  have hmaxLower :
      (50 + 3300 * (base.delta : ℝ)) ^ 2 ≤
        max ((LALM.primalConstant regularity base.delta base.beta base.rho) ^ 2)
          ((LALM.primalComparisonConstant regularity base.delta base.beta base.rho
            base.multiplierBound) ^ 2) := by
    rw [hprimal]
    exact le_max_left _ _
  rw [hbetaReal, hrhoReal] at hmaxLower
  have hpenalty := base.multiplierPrimalConstant_le
  rw [LALM.multiplierPrimalConstant_def, hbetaReal, hrhoReal] at hpenalty
  have hlicqReal : (regularity.licqModulus : ℝ) = 1 := rfl
  rw [hlicqReal] at hpenalty
  norm_num at hpenalty
  nlinarith [sq_nonneg (50 + 3300 * (base.delta : ℝ))]

/-- The source support layer packages the exact regularity constants, unique root,
initialization, and corrected parameter values used in Proposition 4.1. -/
theorem sourceWitness_spec :
    regularity.region = Set.univ ∧
      (∃! x : EuclideanSpace ℝ (Fin 1), constraint x = 0) ∧
      constraint initialPoint = 0 ∧ ‖initialMultiplier‖ = 4 ∧
      (correctedParameters.delta : ℝ) = 1 / 20 ∧
      (correctedParameters.beta : ℝ) = 50 ∧
      (correctedParameters.rho : ℝ) = 2200 ∧
      (correctedParameters.multiplierBound : ℝ) = 4 := by
  refine ⟨regularity_region, existsUnique_constraintRoot, constraint_initialPoint,
    norm_initialMultiplier, ?_⟩
  exact ⟨sourceDelta_eq, sourceBeta_eq, sourceRho_eq, sourceMultiplierBound_eq⟩

end LALM.Correction.SourceWitness

end
