module

public import ReasLib.Optimization.DFP.Polar.TwoCycle
public import ReasLib.Optimization.DFP.Polar.Normalized.Regularity
public import Mathlib.Analysis.Calculus.MeanValue

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.FastContraction

/-- Helper for lem:polar-continuation: the two fast coordinates `(C,V)` of a
normalized state, with the usual supremum norm on `Fin 2 → ℝ`. -/
def fastCoordinates (x : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  ![x.2.1, x.2.2]

/-- Helper for lem:polar-continuation: the coordinate formula for the fast
projection. -/
theorem fastCoordinates_apply (x : ℝ × ℝ × ℝ) :
    fastCoordinates x = ![x.2.1, x.2.2] := by
  rfl

/-- Helper for lem:polar-continuation: projecting a reconstructed normalized
state recovers its fast vector. -/
theorem fastCoordinates_mk (A : ℝ) (v : Fin 2 → ℝ) :
    fastCoordinates (A, v 0, v 1) = v := by
  ext i
  fin_cases i
  all_goals rfl

/-- Helper for lem:polar-continuation: the fast displacement `u` from the
genuine even reference curve at the state's own slow coordinate. -/
def fastError (x : ℝ × ℝ × ℝ) : Fin 2 → ℝ :=
  fastCoordinates x - fastCoordinates (TwoCycle.evenState x.1)

/-- Helper for lem:polar-continuation: the reference-curve formula defining
the fast displacement. -/
theorem fastError_def (x : ℝ × ℝ × ℝ) :
    fastError x = fastCoordinates x - fastCoordinates (TwoCycle.evenState x.1) := by
  rfl

/-- Helper for lem:polar-continuation: one leading stage at fixed first
diagonal entry, using the actual normalized leading map. -/
def leadingFast (c A : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fastCoordinates (Normalized.leadingStage c (A, v 0, v 1))

/-- Helper for lem:polar-continuation: the fast leading stage is the rational
map `(C,V) ↦ (A(V/C-c),1+A(V/C-c)²)`. -/
theorem leadingFast_apply (c A : ℝ) (v : Fin 2 → ℝ) :
    leadingFast c A v =
      ![A * (v 1 / v 0 - c), 1 + A * (v 1 / v 0 - c) ^ 2] := by
  rw [leadingFast, Normalized.leadingStage_apply, fastCoordinates_apply]

/-- Helper for lem:polar-continuation: restricting the leading stage to a
fixed first coordinate commutes with projection onto `(C,V)`. -/
theorem leadingFast_fastCoordinates (c : ℝ) (x : ℝ × ℝ × ℝ) :
    leadingFast c x.1 (fastCoordinates x) =
      fastCoordinates (Normalized.leadingStage c x) := by
  rcases x with ⟨A, C, V⟩
  rfl

/-- Helper for lem:polar-continuation: a two-by-two matrix acting as a
continuous linear map on the fast coordinates. -/
def matrixOperator (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi
    (fun i ↦ ∑ j : Fin 2, M i j • ContinuousLinearMap.proj j)

/-- Helper for lem:polar-continuation: the continuous linear matrix action is
ordinary matrix-vector multiplication. -/
theorem matrixOperator_apply (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    matrixOperator M v = M *ᵥ v := by
  ext i
  simp [matrixOperator, Matrix.mulVec, dotProduct]

/-- Helper for lem:polar-continuation: composition of continuous matrix
actions agrees with matrix multiplication. -/
theorem matrixOperator_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    matrixOperator (M * N) = (matrixOperator M).comp (matrixOperator N) := by
  ext v i
  simp only [ContinuousLinearMap.comp_apply, matrixOperator_apply,
    Matrix.mulVec_mulVec]

/-- Helper for lem:polar-continuation: the fast one-stage Jacobian `D_c`. -/
def stageDerivative (c A : ℝ) (v : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-A * v 1 / v 0 ^ 2, A / v 0;
    -2 * A * (v 1 / v 0 - c) * v 1 / v 0 ^ 2,
      2 * A * (v 1 / v 0 - c) / v 0]

/-- Helper for lem:polar-continuation: the displayed coordinate formula for
the one-stage Jacobian. -/
theorem stageDerivative_def (c A : ℝ) (v : Fin 2 → ℝ) :
    stageDerivative c A v =
      !![-A * v 1 / v 0 ^ 2, A / v 0;
        -2 * A * (v 1 / v 0 - c) * v 1 / v 0 ^ 2,
          2 * A * (v 1 / v 0 - c) / v 0] := by
  rfl

/-- Helper for lem:polar-continuation: the leading stage has exactly the
displayed fast derivative whenever its off-diagonal input is nonzero. -/
theorem hasFDerivAt_leadingFast (c A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0) :
    HasFDerivAt (leadingFast c A) (matrixOperator (stageDerivative c A v)) v := by
  have hCderiv := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) v
  have hVderiv := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) v
  have hinv := (hasFDerivAt_inv hC).comp v hCderiv
  have hquot := (hVderiv.mul hinv).sub_const c
  have hfirst := hquot.const_mul A
  have hsecond := ((hquot.pow 2).const_mul A).const_add 1
  rw [funext (leadingFast_apply c A)]
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · apply hfirst.congr_fderiv
    ext u
    simp [matrixOperator_apply, stageDerivative_def, Matrix.vecHead,
      Matrix.vecTail, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
    ring
  · apply hsecond.congr_fderiv
    ext u
    simp [matrixOperator_apply, stageDerivative_def, Matrix.vecHead,
      Matrix.vecTail, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
    ring

/-- Helper for lem:polar-continuation: the two-stage leading fast map, in the
source's even-then-odd order. -/
def leadingCycle (A : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  leadingFast baseAngle A (leadingFast (2 * baseAngle) A v)

/-- Helper for lem:polar-continuation: the two-stage composition formula. -/
theorem leadingCycle_def (A : ℝ) (v : Fin 2 → ℝ) :
    leadingCycle A v = leadingFast baseAngle A (leadingFast (2 * baseAngle) A v) := by
  rfl

/-- Helper for lem:polar-continuation: the fast two-stage map is the projection
of the actual two consecutive leading stages. -/
theorem leadingCycle_fastCoordinates (x : ℝ × ℝ × ℝ) :
    leadingCycle x.1 (fastCoordinates x) =
      fastCoordinates
        (Normalized.leadingStage baseAngle (Normalized.leadingStage (2 * baseAngle) x)) := by
  have hfirst : (Normalized.leadingStage (2 * baseAngle) x).1 = x.1 := by
    rw [Normalized.leadingStage_apply]
  have hstage := leadingFast_fastCoordinates baseAngle
    (Normalized.leadingStage (2 * baseAngle) x)
  rw [hfirst] at hstage
  rw [leadingCycle_def, leadingFast_fastCoordinates, hstage]

/-- Helper for lem:polar-continuation: at zero scale the exact normalized map
is the original even-then-odd leading map, for every state. -/
theorem map_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ) :
    Normalized.map L κ 0 x =
      Normalized.leadingStage baseAngle (Normalized.leadingStage (2 * baseAngle) x) := by
  simp [Normalized.map_def, Normalized.rescale_apply, Normalized.twoStep_def,
    Normalized.cycleStage_zero, Normalized.limitAngle_zero, Normalized.limitAngle_one,
    Normalized.rescaleFactor_def, Normalized.unitRoot_def]

/-- Helper for lem:polar-continuation: the fast coordinates of the exact
zero-scale map are the two-stage fast leading map. -/
theorem fastCoordinates_map_zero (L κ : ℝ) (x : ℝ × ℝ × ℝ) :
    fastCoordinates (Normalized.map L κ 0 x) = leadingCycle x.1 (fastCoordinates x) := by
  rw [map_zero, leadingCycle_fastCoordinates]

/-- Helper for lem:polar-continuation: the exact zero-scale map preserves
the slow coordinate for every fast displacement. -/
theorem map_zero_fst (L κ : ℝ) (x : ℝ × ℝ × ℝ) :
    (Normalized.map L κ 0 x).1 = x.1 := by
  rw [map_zero, Normalized.leadingStage_apply, Normalized.leadingStage_apply]

/-- Helper for lem:polar-continuation: subtracting the genuine reference
curve after the exact zero-scale map agrees with the leading fast error. -/
theorem fastError_map_zero (L κ A : ℝ) (v : Fin 2 → ℝ) :
    fastError (Normalized.map L κ 0 (A, v 0, v 1)) =
      leadingCycle A v - fastCoordinates (TwoCycle.evenState A) := by
  rw [fastError_def, fastCoordinates_map_zero, map_zero_fst, fastCoordinates_mk]

/-- Helper for lem:polar-continuation: the fast Jacobian of the two-stage
leading map is the odd-stage Jacobian times the even-stage Jacobian. -/
def cycleDerivative (A : ℝ) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  stageDerivative baseAngle A (leadingFast (2 * baseAngle) A v) *
    stageDerivative (2 * baseAngle) A v

/-- Helper for lem:polar-continuation: the defining ordered product of the
two-stage Jacobian. -/
theorem cycleDerivative_def (A : ℝ) (v : Fin 2 → ℝ) :
    cycleDerivative A v =
      stageDerivative baseAngle A (leadingFast (2 * baseAngle) A v) *
        stageDerivative (2 * baseAngle) A v := by
  rfl

/-- Helper for lem:polar-continuation: differentiating the actual two-stage
leading map gives `cycleDerivative`. -/
theorem hasFDerivAt_leadingCycle (A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0)
    (hCNext : leadingFast (2 * baseAngle) A v 0 ≠ 0) :
    HasFDerivAt (leadingCycle A) (matrixOperator (cycleDerivative A v)) v := by
  rw [cycleDerivative_def, matrixOperator_mul]
  exact (hasFDerivAt_leadingFast baseAngle A _ hCNext).comp v
    (hasFDerivAt_leadingFast (2 * baseAngle) A v hC)

/-- Helper for lem:polar-continuation: `cycleDerivative` is also the fast
linearization of the actual normalized map at zero scale. -/
theorem hasFDerivAt_map_zero_fast (L κ A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0)
    (hCNext : leadingFast (2 * baseAngle) A v 0 ≠ 0) :
    HasFDerivAt
      (fun w : Fin 2 → ℝ ↦ fastCoordinates (Normalized.map L κ 0 (A, w 0, w 1)))
      (matrixOperator (cycleDerivative A v)) v := by
  simpa only [fastCoordinates_map_zero, fastCoordinates_mk]
    using hasFDerivAt_leadingCycle A v hC hCNext

/-- Helper for lem:polar-continuation: the base angle is nonzero. -/
private theorem baseAngle_ne_zero : baseAngle ≠ 0 := by
  rw [baseAngle_def]
  positivity

/-- Helper for lem:polar-continuation: the even-stage Jacobian at `K₀` is the
source matrix `D_E`. -/
theorem stageDerivative_evenReference :
    stageDerivative (2 * baseAngle) TwoCycle.kZero
      (fastCoordinates TwoCycle.evenReference) =
      !![-3 / 2, 1 / (2 * baseAngle); -3 * baseAngle, 1] := by
  rw [stageDerivative_def, fastCoordinates_apply, TwoCycle.evenReference_def,
    TwoCycle.kZero_eq]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: the odd-stage Jacobian at `K₀` is the
source matrix `D_O`. -/
theorem stageDerivative_oddReference :
    stageDerivative baseAngle TwoCycle.kZero
      (fastCoordinates TwoCycle.oddReference) =
      !![-3, 1 / baseAngle; -12 * baseAngle, 4] := by
  rw [stageDerivative_def, fastCoordinates_apply, TwoCycle.oddReference_def,
    TwoCycle.kZero_eq]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: the leading fast stage carries each
even cycle state to the corresponding odd cycle state. -/
theorem leadingFast_evenState (A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    leadingFast (2 * baseAngle) A (fastCoordinates (TwoCycle.evenState A)) =
      fastCoordinates (TwoCycle.oddState A) := by
  have hfirst : (TwoCycle.evenState A).1 = A := by
    rw [TwoCycle.evenState_apply]
  have hstage := leadingFast_fastCoordinates (2 * baseAngle) (TwoCycle.evenState A)
  rw [hfirst, TwoCycle.evenToOdd A hA] at hstage
  exact hstage

/-- Helper for lem:polar-continuation: the leading two-stage map fixes the
fast coordinates of the general nearby even cycle. -/
theorem leadingCycle_evenState (A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    leadingCycle A (fastCoordinates (TwoCycle.evenState A)) =
      fastCoordinates (TwoCycle.evenState A) := by
  have hfirst : (TwoCycle.oddState A).1 = A := by
    rw [TwoCycle.oddState_apply]
  have hstage := leadingFast_fastCoordinates baseAngle (TwoCycle.oddState A)
  rw [hfirst, TwoCycle.oddToEven A hA] at hstage
  rw [leadingCycle_def, leadingFast_evenState A hA, hstage]

/-- Helper for lem:polar-continuation: the full two-stage derivative at the
reference cycle is the displayed matrix `D_cyc`. -/
theorem cycleDerivative_evenReference :
    cycleDerivative TwoCycle.kZero (fastCoordinates TwoCycle.evenReference) =
      !![3 / 2, -1 / (2 * baseAngle); 6 * baseAngle, -2] := by
  have hK : TwoCycle.kZero ∈ TwoCycle.normalizationSet :=
    mem_of_mem_nhds TwoCycle.normalizationSet_mem_nhds
  have hstage := leadingFast_evenState TwoCycle.kZero hK
  rw [TwoCycle.evenState_kZero, TwoCycle.oddState_kZero] at hstage
  rw [cycleDerivative_def, hstage, stageDerivative_evenReference,
    stageDerivative_oddReference]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: the fixed eigenvector matrix `P` of
the reference two-stage derivative. -/
def basisMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 3 * baseAngle, 4 * baseAngle]

/-- Helper for lem:polar-continuation: the explicit inverse of the fixed
eigenvector matrix, independent of the nearby cycle and of `j₀`. -/
def inverseBasis : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4, -1 / baseAngle; -3, 1 / baseAngle]

/-- Helper for lem:polar-continuation: the coordinate formula for `P`. -/
theorem basisMatrix_def :
    basisMatrix = !![1, 1; 3 * baseAngle, 4 * baseAngle] := by
  rfl

/-- Helper for lem:polar-continuation: the coordinate formula for `P⁻¹`. -/
theorem inverseBasis_def :
    inverseBasis = !![4, -1 / baseAngle; -3, 1 / baseAngle] := by
  rfl

/-- Helper for lem:polar-continuation: `P⁻¹ P = 1`. -/
theorem inverseBasis_mul_basisMatrix : inverseBasis * basisMatrix = 1 := by
  rw [inverseBasis_def, basisMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: `P P⁻¹ = 1`. -/
theorem basisMatrix_mul_inverseBasis : basisMatrix * inverseBasis = 1 := by
  rw [inverseBasis_def, basisMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, baseAngle_ne_zero]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: the actual reference cycle derivative
is conjugate by the fixed `P` to `diag(0,-1/2)`. -/
theorem referenceDerivative_conjugation :
    inverseBasis *
        cycleDerivative TwoCycle.kZero (fastCoordinates TwoCycle.evenReference) *
          basisMatrix = !![0, 0; 0, -1 / 2] := by
  rw [cycleDerivative_evenReference, inverseBasis_def, basisMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp [baseAngle_ne_zero]
  all_goals ring

/-- Helper for lem:polar-continuation: the fixed fast norm `|u|* = ‖P⁻¹u‖∞`. -/
def fixedNorm (u : Fin 2 → ℝ) : ℝ :=
  ‖inverseBasis *ᵥ u‖

/-- Helper for lem:polar-continuation: the supremum-norm formula defining
the fixed fast norm. -/
theorem fixedNorm_def (u : Fin 2 → ℝ) : fixedNorm u = ‖inverseBasis *ᵥ u‖ := by
  rfl

/-- Helper for lem:polar-continuation: the fixed fast norm is nonnegative. -/
theorem fixedNorm_nonneg (u : Fin 2 → ℝ) : 0 ≤ fixedNorm u := by
  exact norm_nonneg _

/-- Helper for lem:polar-continuation: the fixed fast norm vanishes exactly
at the zero fast displacement. -/
theorem fixedNorm_eq_zero (u : Fin 2 → ℝ) : fixedNorm u = 0 ↔ u = 0 := by
  rw [fixedNorm_def, norm_eq_zero]
  constructor
  · intro h
    have hmul := congrArg (fun v ↦ basisMatrix *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, basisMatrix_mul_inverseBasis,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hmul
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- Helper for lem:polar-continuation: the fixed fast norm satisfies the
triangle inequality. -/
theorem fixedNorm_add_le (u v : Fin 2 → ℝ) :
    fixedNorm (u + v) ≤ fixedNorm u + fixedNorm v := by
  simp only [fixedNorm_def, Matrix.mulVec_add]
  exact norm_add_le _ _

/-- Helper for lem:polar-continuation: the fixed fast norm is homogeneous. -/
theorem fixedNorm_smul (r : ℝ) (u : Fin 2 → ℝ) :
    fixedNorm (r • u) = |r| * fixedNorm u := by
  rw [fixedNorm_def, Matrix.mulVec_smul, norm_smul, Real.norm_eq_abs, fixedNorm_def]

/-- Helper for lem:polar-continuation: the usual fast norm is bounded by a
fixed multiple of the prescribed fast norm. -/
theorem norm_le_basisOperator_mul_fixedNorm (u : Fin 2 → ℝ) :
    ‖u‖ ≤ ‖matrixOperator basisMatrix‖ * fixedNorm u := by
  have hbound := (matrixOperator basisMatrix).le_opNorm (inverseBasis *ᵥ u)
  simpa only [matrixOperator_apply, Matrix.mulVec_mulVec,
    basisMatrix_mul_inverseBasis, Matrix.one_mulVec, fixedNorm_def] using hbound

/-- Helper for lem:polar-continuation: conjugation converts a matrix action
in the fixed fast norm to the ordinary supremum norm. -/
theorem inverseBasis_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    inverseBasis *ᵥ (M *ᵥ u) =
      (inverseBasis * M * basisMatrix) *ᵥ (inverseBasis *ᵥ u) := by
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, basisMatrix_mul_inverseBasis,
    Matrix.mul_one]

/-- Helper for lem:polar-continuation: a row-sum bound controls the matrix
action in the supremum norm. -/
theorem norm_mulVec_le_of_rowSum (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hrow : ∀ i, |M i 0| + |M i 1| ≤ r) (u : Fin 2 → ℝ) :
    ‖M *ᵥ u‖ ≤ r * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hr (norm_nonneg u))).mpr
  intro i
  calc
    ‖(M *ᵥ u) i‖ = ‖M i 0 * u 0 + M i 1 * u 1‖ := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    _ ≤ ‖M i 0 * u 0‖ + ‖M i 1 * u 1‖ := norm_add_le _ _
    _ = |M i 0| * ‖u 0‖ + |M i 1| * ‖u 1‖ := by
      simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ |M i 0| * ‖u‖ + |M i 1| * ‖u‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm u 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm u 1) (abs_nonneg _))
    _ = (|M i 0| + |M i 1|) * ‖u‖ := by ring
    _ ≤ r * ‖u‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg u)

/-- Helper for lem:polar-continuation: the reference fast derivative has
contraction factor `1/2` in the source's fixed norm. -/
theorem fixedNorm_referenceDerivative_le (u : Fin 2 → ℝ) :
    fixedNorm
        (cycleDerivative TwoCycle.kZero (fastCoordinates TwoCycle.evenReference) *ᵥ u) ≤
      (1 / 2 : ℝ) * fixedNorm u := by
  rw [fixedNorm_def, inverseBasis_mulVec, referenceDerivative_conjugation,
    fixedNorm_def]
  apply norm_mulVec_le_of_rowSum
  · norm_num
  · intro i
    fin_cases i
    all_goals norm_num

/-- Helper for lem:polar-continuation: the fast leading stage is jointly
continuous in the first diagonal entry and the fast input away from `C = 0`. -/
theorem continuousAt_leadingFast (c A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0) :
    ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ leadingFast c z.1 z.2) (A, v) := by
  simp only [leadingFast_apply]
  fun_prop (disch := assumption)

/-- Helper for lem:polar-continuation: the one-stage fast Jacobian is jointly
continuous wherever its off-diagonal input is nonzero. -/
theorem continuousAt_stageDerivative (c A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0) :
    ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ stageDerivative c z.1 z.2) (A, v) := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [stageDerivative_def, Matrix.of_apply]
  all_goals fun_prop (disch := positivity)

/-- Helper for lem:polar-continuation: the derivative of the actual two-stage
leading map varies continuously on its nonsingular state neighborhood. -/
theorem continuousAt_cycleDerivative (A : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0)
    (hCNext : leadingFast (2 * baseAngle) A v 0 ≠ 0) :
    ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ cycleDerivative z.1 z.2) (A, v) := by
  have hstage := continuousAt_leadingFast (2 * baseAngle) A v hC
  have hpair := continuousAt_fst.prodMk hstage
  have hodd := (continuousAt_stageDerivative baseAngle A _ hCNext).comp_of_eq hpair rfl
  simpa only [cycleDerivative_def, Function.comp_def] using
    hodd.fun_mul (continuousAt_stageDerivative (2 * baseAngle) A v hC)

/-- Helper for lem:polar-continuation: both off-diagonal inputs to the
reference leading cycle are nonzero. -/
theorem reference_nonsingular :
    fastCoordinates TwoCycle.evenReference 0 ≠ 0 ∧
      leadingFast (2 * baseAngle) TwoCycle.kZero
        (fastCoordinates TwoCycle.evenReference) 0 ≠ 0 := by
  have hK : TwoCycle.kZero ∈ TwoCycle.normalizationSet :=
    mem_of_mem_nhds TwoCycle.normalizationSet_mem_nhds
  have hstage := leadingFast_evenState TwoCycle.kZero hK
  rw [TwoCycle.evenState_kZero, TwoCycle.oddState_kZero] at hstage
  rw [hstage, fastCoordinates_apply, fastCoordinates_apply,
    TwoCycle.evenReference_def, TwoCycle.oddReference_def]
  simp [baseAngle_ne_zero]

/-- Helper for lem:polar-continuation: the reference row sums in the fixed
basis are strictly below `3/4`. -/
private theorem reference_conjugate_rowSum_lt (i : Fin 2) :
    |(inverseBasis *
        cycleDerivative TwoCycle.kZero (fastCoordinates TwoCycle.evenReference) *
          basisMatrix) i 0| +
      |(inverseBasis *
        cycleDerivative TwoCycle.kZero (fastCoordinates TwoCycle.evenReference) *
          basisMatrix) i 1| < (3 / 4 : ℝ) := by
  rw [referenceDerivative_conjugation]
  fin_cases i
  all_goals norm_num

/-- Helper for lem:polar-continuation: the fast derivative remains a uniform
strict contraction in the fixed norm on a neighborhood of the reference state.
The factor `3/4` and this neighborhood are independent of `j₀`. -/
theorem eventually_fixedNorm_cycleDerivative_le :
    ∀ᶠ z : ℝ × (Fin 2 → ℝ) in
        𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference),
      z.2 0 ≠ 0 ∧ leadingFast (2 * baseAngle) z.1 z.2 0 ≠ 0 ∧
        ∀ u : Fin 2 → ℝ,
          fixedNorm (cycleDerivative z.1 z.2 *ᵥ u) ≤ (3 / 4 : ℝ) * fixedNorm u := by
  have hC := reference_nonsingular.1
  have hCNext := reference_nonsingular.2
  have hd := continuousAt_cycleDerivative TwoCycle.kZero _ hC hCNext
  have hconjugate : ContinuousAt
      (fun z : ℝ × (Fin 2 → ℝ) ↦ inverseBasis * cycleDerivative z.1 z.2 * basisMatrix)
      (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) :=
    (continuousAt_const.mul hd).mul continuousAt_const
  have hrows : ∀ᶠ z : ℝ × (Fin 2 → ℝ) in
        𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference),
      ∀ i : Fin 2,
        |(inverseBasis * cycleDerivative z.1 z.2 * basisMatrix) i 0| +
          |(inverseBasis * cycleDerivative z.1 z.2 * basisMatrix) i 1| < (3 / 4 : ℝ) := by
    apply Filter.eventually_all.mpr
    intro i
    have hrow : ContinuousAt
        (fun z : ℝ × (Fin 2 → ℝ) ↦
          |(inverseBasis * cycleDerivative z.1 z.2 * basisMatrix) i 0| +
            |(inverseBasis * cycleDerivative z.1 z.2 * basisMatrix) i 1|)
        (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) := by
      fun_prop
    exact hrow.eventually (gt_mem_nhds (reference_conjugate_rowSum_lt i))
  have hcoordinate : ContinuousAt (fun z : ℝ × (Fin 2 → ℝ) ↦ z.2 0)
      (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) := by
    fun_prop
  have hCevent : ∀ᶠ z : ℝ × (Fin 2 → ℝ) in
      𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference), z.2 0 ≠ 0 :=
    hcoordinate.eventually_ne hC
  have hCNextEvent : ∀ᶠ z : ℝ × (Fin 2 → ℝ) in
      𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference),
      leadingFast (2 * baseAngle) z.1 z.2 0 ≠ 0 := by
    have hstage := continuousAt_leadingFast (2 * baseAngle) TwoCycle.kZero _ hC
    exact (continuousAt_pi.mp hstage 0).eventually_ne hCNext
  filter_upwards [hCevent, hCNextEvent, hrows] with z hz hzNext hrow
  refine ⟨hz, hzNext, ?_⟩
  intro u
  rw [fixedNorm_def, inverseBasis_mulVec, fixedNorm_def]
  apply norm_mulVec_le_of_rowSum
  · norm_num
  · intro i
    exact (hrow i).le

/-- Helper for lem:polar-continuation: the selected cycle parameter is
continuous at `K₀`, using the inverse of the original rational cycle family. -/
theorem continuousAt_inverseParameter :
    ContinuousAt TwoCycle.inverseParameter TwoCycle.kZero := by
  have hleft : ∀ᶠ ν : ℝ in 𝓝 baseAngle,
      TwoCycle.inverseParameter (cycleK ν) = ν := by
    filter_upwards [TwoCycle.parameterSet_mem_nhds] with ν hν
    exact TwoCycle.inverseParameter_invOn.1 hν
  have hinv := TwoCycle.hasStrictDerivAt_cycleK_baseAngle.to_local_left_inverse
    TwoCycle.cycleK_derivCoefficient_pos.ne' hleft
  rw [← TwoCycle.kZero_def] at hinv
  exact hinv.hasDerivAt.continuousAt

/-- Helper for lem:polar-continuation: the actual even reference curve is
continuous at `K₀`. -/
theorem continuousAt_evenState : ContinuousAt TwoCycle.evenState TwoCycle.kZero := by
  have hparameter := continuousAt_inverseParameter
  have hden : 2 * TwoCycle.inverseParameter TwoCycle.kZero - baseAngle ≠ 0 := by
    rw [TwoCycle.inverseParameter_kZero]
    simpa only [two_mul, add_sub_cancel_right] using baseAngle_ne_zero
  rw [funext TwoCycle.evenState_apply]
  simp only [cycleW_def]
  fun_prop

/-- Helper for lem:polar-continuation: the same fixed norm contracts the
linearization at every nearby genuine cycle, including `K* = cycleK ν*`
with `ν*` close to `baseAngle`. -/
theorem eventually_evenState_fixedNorm_cycleDerivative_le :
    ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ,
          fixedNorm (cycleDerivative A (fastCoordinates (TwoCycle.evenState A)) *ᵥ u) ≤
            (3 / 4 : ℝ) * fixedNorm u := by
  have heven := continuousAt_evenState
  have hcurve : ContinuousAt
      (fun A : ℝ ↦ (A, fastCoordinates (TwoCycle.evenState A))) TwoCycle.kZero := by
    simp only [fastCoordinates_apply]
    fun_prop
  have htendsto : Tendsto
      (fun A : ℝ ↦ (A, fastCoordinates (TwoCycle.evenState A))) (𝓝 TwoCycle.kZero)
      (𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference)) := by
    simpa only [ContinuousAt, TwoCycle.evenState_kZero] using hcurve
  filter_upwards [TwoCycle.normalizationSet_mem_nhds,
    htendsto.eventually eventually_fixedNorm_cycleDerivative_le] with A hA hcontract
  exact ⟨hA, hcontract.2.2⟩

/-- Helper for lem:polar-continuation: the leading two-stage map contracts
small fast displacements from every nearby genuine even cycle in one fixed
norm, with one radius and the factor `3/4` independent of `j₀`. -/
theorem exists_uniform_leadingCycle_contraction :
    ∃ r > 0, ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ, fixedNorm u < r →
          fixedNorm (leadingCycle A (fastCoordinates (TwoCycle.evenState A) + u) -
            fastCoordinates (TwoCycle.evenState A)) ≤ (3 / 4 : ℝ) * fixedNorm u := by
  obtain ⟨ε, hε, hcontract⟩ :=
    Metric.eventually_nhds_iff.mp eventually_fixedNorm_cycleDerivative_le
  have heven := continuousAt_evenState
  have hcurve : ContinuousAt
      (fun A : ℝ ↦ (A, fastCoordinates (TwoCycle.evenState A))) TwoCycle.kZero := by
    simp only [fastCoordinates_apply]
    fun_prop
  have htendsto : Tendsto
      (fun A : ℝ ↦ (A, fastCoordinates (TwoCycle.evenState A))) (𝓝 TwoCycle.kZero)
      (𝓝 (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference)) := by
    simpa only [ContinuousAt, TwoCycle.evenState_kZero] using hcurve
  have hnear : ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      dist (A, fastCoordinates (TwoCycle.evenState A))
        (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) < ε / 2 :=
    htendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  let B := ‖matrixOperator basisMatrix‖ + 1
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨ε / (2 * B), div_pos hε (mul_pos zero_lt_two hB), ?_⟩
  filter_upwards [TwoCycle.normalizationSet_mem_nhds, hnear] with A hA hAnear
  refine ⟨hA, ?_⟩
  intro u hu
  have hnormu : ‖u‖ < ε / 2 := by
    calc
      ‖u‖ ≤ ‖matrixOperator basisMatrix‖ * fixedNorm u :=
        norm_le_basisOperator_mul_fixedNorm u
      _ ≤ B * fixedNorm u := by
        apply mul_le_mul_of_nonneg_right _ (fixedNorm_nonneg u)
        dsimp only [B]
        linarith
      _ < B * (ε / (2 * B)) := mul_lt_mul_of_pos_left hu hB
      _ = ε / 2 := by field_simp
  have hsegment : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      dist (A, fastCoordinates (TwoCycle.evenState A) + s • u)
        (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) < ε := by
    intro s hs
    have hsmul : ‖s • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg u) hs.2
    have hdist : dist
        (A, fastCoordinates (TwoCycle.evenState A) + s • u)
        (A, fastCoordinates (TwoCycle.evenState A)) < ε / 2 := by
      rw [dist_prod_same_left, dist_eq_norm]
      simpa only [add_sub_cancel_left] using hsmul.trans_lt hnormu
    calc
      dist (A, fastCoordinates (TwoCycle.evenState A) + s • u)
          (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) ≤
        dist (A, fastCoordinates (TwoCycle.evenState A) + s • u)
            (A, fastCoordinates (TwoCycle.evenState A)) +
          dist (A, fastCoordinates (TwoCycle.evenState A))
            (TwoCycle.kZero, fastCoordinates TwoCycle.evenReference) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdist hAnear
      _ = ε := by ring
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ ↦ inverseBasis *ᵥ
          leadingCycle A (fastCoordinates (TwoCycle.evenState A) + s • u))
        (inverseBasis *ᵥ
          (cycleDerivative A (fastCoordinates (TwoCycle.evenState A) + s • u) *ᵥ u)) s := by
    intro s hs
    have hstate := hcontract (hsegment s hs)
    have hline : HasDerivAt
        (fun s : ℝ ↦ fastCoordinates (TwoCycle.evenState A) + s • u) u s := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id s).smul_const u).const_add (fastCoordinates (TwoCycle.evenState A))
    have hcycle := (hasFDerivAt_leadingCycle A _ hstate.1 hstate.2.1).comp_hasDerivAt s hline
    have houtput := (matrixOperator inverseBasis).hasFDerivAt.comp_hasDerivAt s hcycle
    simpa only [Function.comp_def, matrixOperator_apply] using houtput
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖inverseBasis *ᵥ
          (cycleDerivative A (fastCoordinates (TwoCycle.evenState A) + s • u) *ᵥ u)‖ ≤
        (3 / 4 : ℝ) * fixedNorm u := by
    intro s hs
    exact (hcontract (hsegment s (Set.Ico_subset_Icc_self hs))).2.2 u
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs ↦ (hderiv s hs).hasDerivWithinAt) hbound
  simpa only [zero_smul, one_smul, add_zero, leadingCycle_evenState A hA,
    ← Matrix.mulVec_sub, fixedNorm_def] using hmean

/-- Helper for lem:polar-continuation: the leading contraction holds for the
original parameter selection `K* = cycleK ν*` with `ν*` near `baseAngle`,
using a fast radius chosen independently of `ν*` and `j₀`. -/
theorem exists_uniform_parameter_leadingCycle_contraction :
    ∃ r > 0, ∀ᶠ ν : ℝ in 𝓝 baseAngle,
      ν ∈ TwoCycle.parameterSet ∧
        ∀ u : Fin 2 → ℝ, fixedNorm u < r →
          fixedNorm
              (leadingCycle (cycleK ν) (fastCoordinates (TwoCycle.evenState (cycleK ν)) + u) -
                fastCoordinates (TwoCycle.evenState (cycleK ν))) ≤
            (3 / 4 : ℝ) * fixedNorm u := by
  obtain ⟨r, hr, hcontract⟩ := exists_uniform_leadingCycle_contraction
  have htendsto : Tendsto cycleK (𝓝 baseAngle) (𝓝 TwoCycle.kZero) := by
    simpa only [TwoCycle.kZero_def, ContinuousAt] using
      TwoCycle.hasDerivAt_cycleK_baseAngle.continuousAt
  refine ⟨r, hr, ?_⟩
  filter_upwards [TwoCycle.parameterSet_mem_nhds, htendsto.eventually hcontract] with
    ν hν hcycle
  exact ⟨hν, hcycle.2⟩

/-- Helper for lem:polar-continuation: the actual normalized map contracts
its centered fast displacement at zero scale on one uniform neighborhood. -/
theorem exists_uniform_map_zero_contraction (L κ : ℝ) :
    ∃ r > 0, ∀ᶠ A : ℝ in 𝓝 TwoCycle.kZero,
      A ∈ TwoCycle.normalizationSet ∧
        ∀ u : Fin 2 → ℝ, fixedNorm u < r →
          fixedNorm (fastError (Normalized.map L κ 0
            (A, (fastCoordinates (TwoCycle.evenState A) + u) 0,
              (fastCoordinates (TwoCycle.evenState A) + u) 1))) ≤
            (3 / 4 : ℝ) * fixedNorm u := by
  simpa only [fastError_map_zero] using exists_uniform_leadingCycle_contraction

/-- Helper for lem:polar-continuation: the proved vanishing scale derivatives
of a normalized stage give an actual cubic error from its leading stage. -/
theorem cycleStage_sub_leading_isBigO (L κ : ℝ) (i : Fin 2)
    (x₀ x : ℝ × ℝ × ℝ) :
    (fun t : ℝ ↦ Normalized.cycleStage L κ i t x₀ x -
      Normalized.leadingStage (Normalized.limitAngle i) x) =O[𝓝 0]
        (fun t : ℝ ↦ t ^ 3) := by
  have hfirst : iteratedDeriv 1 (fun t ↦ Normalized.cycleStage L κ i t x₀ x) 0 = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      Normalized.cycleStage_firstIteratedFDeriv_eq_zero]
    rfl
  have hsecond : iteratedDeriv 2 (fun t ↦ Normalized.cycleStage L κ i t x₀ x) 0 = 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      Normalized.cycleStage_secondIteratedFDeriv_eq_zero]
    rfl
  obtain ⟨q, hq, hformula⟩ :=
    (Normalized.cycleStage_analyticAt_zero L κ i x₀ x).exists_eq_sum_add_pow_mul 3
  have hfactor (t : ℝ) :
      Normalized.cycleStage L κ i t x₀ x -
        Normalized.leadingStage (Normalized.limitAngle i) x = t ^ 3 • q t := by
    have hvalue : Normalized.cycleStage L κ i t x₀ x =
        Normalized.leadingStage (Normalized.limitAngle i) x + t ^ 3 • q t := by
      simpa [Finset.sum_range_succ, hfirst, hsecond, iteratedDeriv_zero,
        Normalized.cycleStage_zero] using hformula t
    rw [hvalue]
    abel
  have hbound := (Asymptotics.isBigO_refl (fun t : ℝ ↦ t ^ 3) (𝓝 0)).smul
    (hq.continuousAt.isBigO_one ℝ)
  simpa only [hfactor, smul_eq_mul, mul_one] using hbound

end DFP.Polar.FastContraction
