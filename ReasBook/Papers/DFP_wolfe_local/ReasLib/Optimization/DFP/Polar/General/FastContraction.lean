module

public import ReasLib.Optimization.DFP.Polar.General.CycleFamily
public import ReasLib.Optimization.DFP.Polar.General.Recurrence
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Algebra.Order.Star.Real

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.Polar.General.FastContraction

open DFP.Polar.FastContraction (fastCoordinates leadingFast matrixOperator stageDerivative)

/-- Helper for lem:polar-continuation: stability leaves a positive Lyapunov denominator. -/
theorem stableGap_pos {κ : ℝ} (hκ : |κ| < 1) : 0 < 1 - κ ^ 2 := by
  have hb := abs_lt.mp hκ
  have hp : 0 < 1 + κ := by linarith
  have hm : 0 < 1 - κ := by linarith
  have hprod := mul_pos hp hm
  nlinarith

/-- Helper for lem:polar-continuation: positive powers of a matrix satisfying `J² = κJ`. -/
theorem quadraticMatrix_pow {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (n : ℕ) : J ^ (n + 1) = κ ^ n • J := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ _ (n + 1), ih, Matrix.smul_mul, hJ, smul_smul, pow_succ]

/-- Helper for lem:polar-continuation: the Gram matrix of each positive power of `J`. -/
theorem quadraticMatrix_gram_pow {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (n : ℕ) :
    J.transpose ^ (n + 1) * J ^ (n + 1) =
      (κ ^ 2) ^ n • (J.transpose * J) := by
  rw [← Matrix.transpose_pow, quadraticMatrix_pow hJ n, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hscalar : κ ^ n * κ ^ n = (κ ^ 2) ^ n := by
    rw [← mul_pow, pow_two]
  rw [hscalar]

/-- Helper for lem:polar-continuation: the closed form of the source's Lyapunov series. -/
def lyapunovMatrix (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  1 + (1 - κ ^ 2)⁻¹ • (J.transpose * J)

/-- Helper for lem:polar-continuation: the positive powers form a geometric Gram series. -/
theorem hasSum_powerGramTail {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) :
    HasSum (fun n : ℕ ↦ J.transpose ^ (n + 1) * J ^ (n + 1))
      ((1 - κ ^ 2)⁻¹ • (J.transpose * J)) := by
  have hsq : κ ^ 2 < 1 := by linarith [stableGap_pos hκ]
  have hnorm : ‖κ ^ 2‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg κ)] using hsq
  have hgeo : HasSum (fun n : ℕ ↦ (κ ^ 2) ^ n) (1 - κ ^ 2)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hmodel : HasSum (fun n : ℕ ↦ (κ ^ 2) ^ n • (J.transpose * J))
      ((1 - κ ^ 2)⁻¹ • (J.transpose * J)) :=
    hgeo.smul_const (J.transpose * J)
  exact hmodel.congr_fun (quadraticMatrix_gram_pow hJ)

/-- Helper for lem:polar-continuation: the Lyapunov matrix is the convergent power-Gram series. -/
theorem hasSum_lyapunovMatrix {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) :
    HasSum (fun n : ℕ ↦ J.transpose ^ n * J ^ n) (lyapunovMatrix J κ) := by
  have hall := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ J.transpose ^ n * J ^ n) 1).mp (hasSum_powerGramTail hJ hκ)
  simpa only [Finset.sum_range_one, pow_zero, Matrix.one_mul,
    lyapunovMatrix, add_comm] using hall

/-- Helper for lem:polar-continuation: the Lyapunov matrix equals the source's infinite sum. -/
theorem lyapunovMatrix_eq_tsum {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) :
    lyapunovMatrix J κ = ∑' n : ℕ, J.transpose ^ n * J ^ n := by
  exact (hasSum_lyapunovMatrix hJ hκ).tsum_eq.symm

/-- Helper for lem:polar-continuation: the Lyapunov matrix is positive definite for stable `κ`. -/
theorem lyapunovMatrix_posDef (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) : (lyapunovMatrix J κ).PosDef := by
  have hgram : (J.transpose * J).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self J
  exact Matrix.PosDef.one.add_posSemidef
    (hgram.smul (inv_nonneg.mpr (stableGap_pos hκ).le))

/-- Helper for lem:polar-continuation: conjugating a Gram matrix squares its underlying map. -/
theorem gram_conjugate (J : Matrix (Fin 2) (Fin 2) ℝ) :
    J.transpose * (J.transpose * J) * J = (J * J).transpose * (J * J) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Helper for lem:polar-continuation: the scalar coefficient in the Lyapunov equation. -/
theorem lyapunovCoefficient {κ : ℝ} (hκ : |κ| < 1) :
    1 + (1 - κ ^ 2)⁻¹ * κ ^ 2 = (1 - κ ^ 2)⁻¹ := by
  field_simp [(stableGap_pos hκ).ne']
  ring

/-- Helper for lem:polar-continuation: the source's discrete Lyapunov equation. -/
theorem lyapunovMatrix_identity {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) :
    J.transpose * lyapunovMatrix J κ * J = lyapunovMatrix J κ - 1 := by
  have hgram : J.transpose * (J.transpose * J) * J =
      κ ^ 2 • (J.transpose * J) := by
    rw [gram_conjugate, hJ, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, pow_two]
  calc
    J.transpose * lyapunovMatrix J κ * J =
        J.transpose * J + (1 - κ ^ 2)⁻¹ •
          (J.transpose * (J.transpose * J) * J) := by
      simp only [lyapunovMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.mul_smul, Matrix.smul_mul]
    _ = (1 + (1 - κ ^ 2)⁻¹ * κ ^ 2) • (J.transpose * J) := by
      rw [hgram, smul_smul, add_smul, one_smul]
    _ = (1 - κ ^ 2)⁻¹ • (J.transpose * J) := by
      rw [lyapunovCoefficient hκ]
    _ = lyapunovMatrix J κ - 1 := by
      simp [lyapunovMatrix]

/-- Helper for lem:polar-continuation: a Gram quadratic form is the squared image norm. -/
theorem gram_quadratic (J : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ ((J.transpose * J) *ᵥ x) = (J *ᵥ x) ⬝ᵥ (J *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Helper for lem:polar-continuation: the quadratic form of the closed Lyapunov matrix. -/
theorem lyapunovMatrix_quadratic (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x : Fin 2 → ℝ) :
    x ⬝ᵥ (lyapunovMatrix J κ *ᵥ x) =
      x ⬝ᵥ x + (1 - κ ^ 2)⁻¹ * ((J *ᵥ x) ⬝ᵥ (J *ᵥ x)) := by
  rw [lyapunovMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, gram_quadratic]
  rfl

/-- Helper for lem:polar-continuation: a matrix acting continuously on Euclidean fast
coordinates. -/
def euclideanOperator (J : Matrix (Fin 2) (Fin 2) ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J

/-- Helper for lem:polar-continuation: Euclidean matrix action is ordinary matrix multiplication. -/
theorem euclideanOperator_ofLp (J : Matrix (Fin 2) (Fin 2) ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    WithLp.ofLp (euclideanOperator J x) = J *ᵥ WithLp.ofLp x := by
  exact Matrix.ofLp_toEuclideanCLM J x

/-- Helper for lem:polar-continuation: matrix action commutes with the Euclidean coordinate
equivalence. -/
theorem euclideanOperator_toLp (J : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    euclideanOperator J (WithLp.toLp 2 x) = WithLp.toLp 2 (J *ᵥ x) := by
  exact Matrix.toEuclideanCLM_toLp J x

/-- Helper for lem:polar-continuation: the Lyapunov norm as a Euclidean embedding in four
dimensions. -/
def lyapunovEmbedding (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![x 0, x 1,
    (Real.sqrt (1 - κ ^ 2))⁻¹ * (euclideanOperator J x) 0,
    (Real.sqrt (1 - κ ^ 2))⁻¹ * (euclideanOperator J x) 1]

/-- Helper for lem:polar-continuation: the fixed equivalent norm induced by the Lyapunov matrix. -/
def lyapunovNorm (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖lyapunovEmbedding J κ x‖

/-- Helper for lem:polar-continuation: the Lyapunov embedding respects addition. -/
theorem lyapunovEmbedding_add (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    lyapunovEmbedding J κ (x + y) = lyapunovEmbedding J κ x + lyapunovEmbedding J κ y := by
  ext i
  fin_cases i
  all_goals simp [lyapunovEmbedding, mul_add]

/-- Helper for lem:polar-continuation: the Lyapunov embedding respects scalar multiplication. -/
theorem lyapunovEmbedding_smul (J : Matrix (Fin 2) (Fin 2) ℝ) (κ a : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovEmbedding J κ (a • x) = a • lyapunovEmbedding J κ x := by
  ext i
  fin_cases i
  all_goals simp [lyapunovEmbedding]
  all_goals ring

/-- Helper for lem:polar-continuation: the fixed Lyapunov norm is nonnegative. -/
theorem lyapunovNorm_nonneg (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ lyapunovNorm J κ x := by
  exact norm_nonneg _

/-- Helper for lem:polar-continuation: the fixed Lyapunov norm vanishes exactly at zero. -/
theorem lyapunovNorm_eq_zero_iff (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : lyapunovNorm J κ x = 0 ↔ x = 0 := by
  rw [lyapunovNorm, norm_eq_zero]
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [lyapunovEmbedding] using congrArg
        (fun y : EuclideanSpace ℝ (Fin 4) ↦ y 0) h
    · simpa [lyapunovEmbedding] using congrArg
        (fun y : EuclideanSpace ℝ (Fin 4) ↦ y 1) h
  · intro h
    subst x
    simp [lyapunovEmbedding]

/-- Helper for lem:polar-continuation: the fixed Lyapunov norm satisfies the triangle inequality. -/
theorem lyapunovNorm_add_le (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (x + y) ≤ lyapunovNorm J κ x + lyapunovNorm J κ y := by
  rw [lyapunovNorm, lyapunovEmbedding_add]
  exact norm_add_le _ _

/-- Helper for lem:polar-continuation: the fixed Lyapunov norm is absolutely homogeneous. -/
theorem lyapunovNorm_smul (J : Matrix (Fin 2) (Fin 2) ℝ) (κ a : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (a • x) = |a| * lyapunovNorm J κ x := by
  rw [lyapunovNorm, lyapunovEmbedding_smul, norm_smul, Real.norm_eq_abs]
  rfl

/-- Helper for lem:polar-continuation: the squared fixed norm has the source's energy formula. -/
theorem lyapunovNorm_sq (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ} (hκ : |κ| < 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ x ^ 2 =
      ‖x‖ ^ 2 + ‖euclideanOperator J x‖ ^ 2 / (1 - κ ^ 2) := by
  have hs : (Real.sqrt (1 - κ ^ 2))⁻¹ ^ 2 = (1 - κ ^ 2)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (stableGap_pos hκ).le]
  simp [lyapunovNorm, EuclideanSpace.real_norm_sq_eq, lyapunovEmbedding,
    Fin.sum_univ_four, Fin.sum_univ_two, mul_pow, hs, div_eq_mul_inv]
  ring

/-- Helper for lem:polar-continuation: the fixed norm is exactly the norm of the Lyapunov
quadratic form. -/
theorem lyapunovNorm_sq_eq_quadratic (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ x ^ 2 =
      (WithLp.ofLp x) ⬝ᵥ (lyapunovMatrix J κ *ᵥ WithLp.ofLp x) := by
  rw [lyapunovNorm_sq J hκ, lyapunovMatrix_quadratic]
  simp [EuclideanSpace.real_norm_sq_eq, dotProduct, Fin.sum_univ_two,
    euclideanOperator_ofLp, div_eq_mul_inv]
  ring

/-- Helper for lem:polar-continuation: the fixed Lyapunov norm dominates the original Euclidean
norm. -/
theorem norm_le_lyapunovNorm (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ lyapunovNorm J κ x := by
  have hsq := lyapunovNorm_sq J hκ x
  have hterm : 0 ≤ ‖euclideanOperator J x‖ ^ 2 / (1 - κ ^ 2) :=
    div_nonneg (sq_nonneg _) (stableGap_pos hκ).le
  nlinarith [norm_nonneg x, lyapunovNorm_nonneg J κ x]

/-- Helper for lem:polar-continuation: an explicit squared equivalence constant for the fixed
norm. -/
def lyapunovBound (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) : ℝ :=
  1 + ‖euclideanOperator J‖ ^ 2 / (1 - κ ^ 2)

/-- Helper for lem:polar-continuation: the explicit squared equivalence constant is at least one. -/
theorem one_le_lyapunovBound (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) : 1 ≤ lyapunovBound J κ := by
  have hterm := div_nonneg (sq_nonneg ‖euclideanOperator J‖) (stableGap_pos hκ).le
  dsimp [lyapunovBound]
  linarith

/-- Helper for lem:polar-continuation: the squared fixed norm has an explicit Euclidean upper
bound. -/
theorem lyapunovNorm_sq_le (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ x ^ 2 ≤ lyapunovBound J κ * ‖x‖ ^ 2 := by
  have hop := (euclideanOperator J).le_opNorm x
  have hsquare : ‖euclideanOperator J x‖ ^ 2 ≤
      ‖euclideanOperator J‖ ^ 2 * ‖x‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg x))).mpr hop
    simpa only [mul_pow] using hs
  rw [lyapunovNorm_sq J hκ]
  calc
    ‖x‖ ^ 2 + ‖euclideanOperator J x‖ ^ 2 / (1 - κ ^ 2) ≤
        ‖x‖ ^ 2 + (‖euclideanOperator J‖ ^ 2 * ‖x‖ ^ 2) / (1 - κ ^ 2) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hsquare (stableGap_pos hκ).le)
    _ = lyapunovBound J κ * ‖x‖ ^ 2 := by
      dsimp [lyapunovBound]
      ring

/-- Helper for lem:polar-continuation: an explicit Euclidean upper bound for the fixed norm. -/
theorem lyapunovNorm_le (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ x ≤ Real.sqrt (lyapunovBound J κ) * ‖x‖ := by
  apply (sq_le_sq₀ (lyapunovNorm_nonneg J κ x)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  rw [mul_pow, Real.sq_sqrt (le_trans zero_le_one (one_le_lyapunovBound J hκ))]
  exact lyapunovNorm_sq_le J hκ x

/-- Helper for lem:polar-continuation: the quadratic matrix identity passes to Euclidean action. -/
theorem quadraticMatrix_action {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanOperator J (euclideanOperator J x) =
      κ • euclideanOperator J x := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ euclideanOperator M x) hJ
  simpa only [euclideanOperator, map_mul, mul_apply_eq_comp, map_smul,
    smul_apply] using h

/-- Helper for lem:polar-continuation: one application of `J` loses exactly the Euclidean energy. -/
theorem lyapunovNorm_energy_identity {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (euclideanOperator J x) ^ 2 =
      lyapunovNorm J κ x ^ 2 - ‖x‖ ^ 2 := by
  rw [lyapunovNorm_sq J hκ, lyapunovNorm_sq J hκ, quadraticMatrix_action hJ,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [(stableGap_pos hκ).ne']
  ring

/-- Helper for lem:polar-continuation: a strict contraction factor for the fixed Lyapunov norm. -/
def contractionFactor (J : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) : ℝ :=
  Real.sqrt (1 - 1 / (2 * lyapunovBound J κ))

/-- Helper for lem:polar-continuation: the radicand defining the contraction factor lies in
`(0,1)`. -/
theorem contractionRadicand_bounds (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) :
    0 < 1 - 1 / (2 * lyapunovBound J κ) ∧
      1 - 1 / (2 * lyapunovBound J κ) < 1 := by
  have hC := one_le_lyapunovBound J hκ
  have hCpos : 0 < lyapunovBound J κ := lt_of_lt_of_le zero_lt_one hC
  have htwo : (0 : ℝ) < 2 := by norm_num
  have htwopos : 0 < 2 * lyapunovBound J κ := mul_pos htwo hCpos
  have hquotpos : 0 < 1 / (2 * lyapunovBound J κ) := one_div_pos.mpr htwopos
  have hquotle : 1 / (2 * lyapunovBound J κ) ≤ 1 / 2 := by
    apply (div_le_iff₀ htwopos).mpr
    linarith
  constructor
  · linarith
  · linarith

/-- Helper for lem:polar-continuation: the fixed contraction factor is positive and strictly
below one. -/
theorem contractionFactor_bounds (J : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) : 0 < contractionFactor J κ ∧ contractionFactor J κ < 1 := by
  have hb := contractionRadicand_bounds J hκ
  have hs := Real.sq_sqrt hb.1.le
  dsimp [contractionFactor]
  constructor
  · exact Real.sqrt_pos.mpr hb.1
  · nlinarith [Real.sqrt_nonneg (1 - 1 / (2 * lyapunovBound J κ))]

/-- Helper for lem:polar-continuation: `J` contracts in the fixed Lyapunov norm, including
nonzero nilpotent `J`. -/
theorem lyapunovNorm_contraction {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (euclideanOperator J x) ≤
      contractionFactor J κ * lyapunovNorm J κ x := by
  have hCpos : 0 < lyapunovBound J κ :=
    lt_of_lt_of_le zero_lt_one (one_le_lyapunovBound J hκ)
  have htwo : (0 : ℝ) < 2 := by norm_num
  have htwopos : 0 < 2 * lyapunovBound J κ := mul_pos htwo hCpos
  have hquot : lyapunovNorm J κ x ^ 2 / (2 * lyapunovBound J κ) ≤ ‖x‖ ^ 2 := by
    apply (div_le_iff₀ htwopos).mpr
    have hbound := lyapunovNorm_sq_le J hκ x
    have hnonneg := mul_nonneg hCpos.le (sq_nonneg ‖x‖)
    nlinarith
  apply (sq_le_sq₀ (lyapunovNorm_nonneg J κ _)
    (mul_nonneg (contractionFactor_bounds J hκ).1.le (lyapunovNorm_nonneg J κ x))).mp
  rw [mul_pow, contractionFactor, Real.sq_sqrt (contractionRadicand_bounds J hκ).1.le,
    lyapunovNorm_energy_identity hJ hκ]
  have halgebra : (1 - 1 / (2 * lyapunovBound J κ)) * lyapunovNorm J κ x ^ 2 =
      lyapunovNorm J κ x ^ 2 - lyapunovNorm J κ x ^ 2 / (2 * lyapunovBound J κ) := by
    ring
  rw [halgebra]
  exact sub_le_sub_left hquot _

/-- Helper for lem:polar-continuation: the general two-stage limiting fast map. -/
def leadingCycle (δE δO γ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  leadingFast δO γ (leadingFast δE γ v)

/-- Helper for lem:polar-continuation: the general limiting cycle is a composition of stages. -/
theorem leadingCycle_apply (δE δO γ : ℝ) (v : Fin 2 → ℝ) :
    leadingCycle δE δO γ v = leadingFast δO γ (leadingFast δE γ v) := by
  rfl

/-- Helper for lem:polar-continuation: the general fast cycle is the projection of its two
leading stages. -/
theorem leadingCycle_fastCoordinates (δE δO : ℝ) (x : ℝ × ℝ × ℝ) :
    leadingCycle δE δO x.1 (fastCoordinates x) =
      fastCoordinates (DFP.Polar.Normalized.leadingStage δO
        (DFP.Polar.Normalized.leadingStage δE x)) := by
  have hfirst : (DFP.Polar.Normalized.leadingStage δE x).1 = x.1 := by
    rw [DFP.Polar.Normalized.leadingStage_apply]
  have hstage := DFP.Polar.FastContraction.leadingFast_fastCoordinates δO
    (DFP.Polar.Normalized.leadingStage δE x)
  rw [hfirst] at hstage
  rw [leadingCycle_apply, DFP.Polar.FastContraction.leadingFast_fastCoordinates, hstage]

/-- Helper for lem:polar-continuation: the ordered product of the general stage Jacobians. -/
def cycleDerivative (δE δO γ : ℝ) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  stageDerivative δO γ (leadingFast δE γ v) * stageDerivative δE γ v

/-- Helper for lem:polar-continuation: the product formula for the general cycle derivative. -/
theorem cycleDerivative_apply (δE δO γ : ℝ) (v : Fin 2 → ℝ) :
    cycleDerivative δE δO γ v =
      stageDerivative δO γ (leadingFast δE γ v) * stageDerivative δE γ v := by
  rfl

/-- Helper for lem:polar-continuation: differentiating the two actual limiting stages. -/
theorem hasFDerivAt_leadingCycle (δE δO γ : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0)
    (hCNext : leadingFast δE γ v 0 ≠ 0) :
    HasFDerivAt (leadingCycle δE δO γ)
      (matrixOperator (cycleDerivative δE δO γ v)) v := by
  rw [cycleDerivative_apply, DFP.Polar.FastContraction.matrixOperator_mul]
  exact (DFP.Polar.FastContraction.hasFDerivAt_leadingFast δO γ _ hCNext).comp v
    (DFP.Polar.FastContraction.hasFDerivAt_leadingFast δE γ v hC)

/-- Helper for lem:polar-continuation: the even limiting fast stage at the selected base. -/
theorem leadingFast_base_even {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    leadingFast (baseDeltaEven ell z) (baseGamma ell z)
        (fastCoordinates (cycleState (baseGamma ell z) ell)) =
      fastCoordinates (cycleState (baseGamma ell z) 1) := by
  have h := congrArg fastCoordinates (evenToOdd (baseCycleDomain hell hz))
  rw [evenState_base hell hz, oddState_base hell hz,
    ← DFP.Polar.FastContraction.leadingFast_fastCoordinates] at h
  simpa only [cycleState_apply] using h

/-- Helper for lem:polar-continuation: both off-diagonal inputs are nonzero at the selected base. -/
theorem base_nonsingular {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    fastCoordinates (cycleState (baseGamma ell z) ell) 0 ≠ 0 ∧
      leadingFast (baseDeltaEven ell z) (baseGamma ell z)
        (fastCoordinates (cycleState (baseGamma ell z) ell)) 0 ≠ 0 := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  have hγ : 0 < baseGamma ell z := by
    rw [baseGamma_def]
    exact one_div_pos.mpr (mul_pos hz hellpos)
  rw [leadingFast_base_even hell hz]
  constructor
  · simpa [DFP.Polar.FastContraction.fastCoordinates_apply, cycleState_apply] using
      (mul_pos hγ hellpos).ne'
  · simpa [DFP.Polar.FastContraction.fastCoordinates_apply, cycleState_apply] using hγ.ne'

/-- Helper for lem:polar-continuation: the actual general cycle derivative at its selected base. -/
theorem cycleDerivative_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseGamma ell z)
      (fastCoordinates (cycleState (baseGamma ell z) ell)) = baseTransverseJacobian ell z := by
  rw [cycleDerivative_apply, leadingFast_base_even hell hz, baseStageDerivative_product hell hz]

/-- Helper for lem:polar-continuation: the derivative of the actual limiting cycle is the source
Jacobian. -/
theorem hasFDerivAt_leadingCycle_base {ell z : ℝ} (hell : 1 < ell) (hz : 0 < z) :
    HasFDerivAt (leadingCycle (baseDeltaEven ell z) (baseDeltaOdd ell z) (baseGamma ell z))
      (matrixOperator (baseTransverseJacobian ell z))
      (fastCoordinates (cycleState (baseGamma ell z) ell)) := by
  rw [← cycleDerivative_base hell hz]
  exact hasFDerivAt_leadingCycle _ _ _ _ (base_nonsingular hell hz).1
    (base_nonsingular hell hz).2

/-- Helper for lem:polar-continuation: the general cycle derivative is continuous on its regular
domain. -/
theorem continuousAt_cycleDerivative (δE δO γ : ℝ) (v : Fin 2 → ℝ) (hC : v 0 ≠ 0)
    (hCNext : leadingFast δE γ v 0 ≠ 0) :
    ContinuousAt (fun p : ℝ × (Fin 2 → ℝ) ↦ cycleDerivative δE δO p.1 p.2) (γ, v) := by
  have hstage := DFP.Polar.FastContraction.continuousAt_leadingFast δE γ v hC
  have hpair := continuousAt_fst.prodMk hstage
  have hodd := (DFP.Polar.FastContraction.continuousAt_stageDerivative δO γ _ hCNext).comp_of_eq
    hpair rfl
  simpa only [cycleDerivative_apply, Function.comp_def] using
    hodd.fun_mul (DFP.Polar.FastContraction.continuousAt_stageDerivative δE γ v hC)

/-- Helper for lem:polar-continuation: Euclidean matrix action depends continuously on its
matrix. -/
theorem continuous_euclideanOperator :
    Continuous (euclideanOperator : Matrix (Fin 2) (Fin 2) ℝ →
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  exact (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
    |>.continuous_of_finiteDimensional

/-- Helper for lem:polar-continuation: Euclidean matrix action respects subtraction. -/
theorem euclideanOperator_sub (L J : Matrix (Fin 2) (Fin 2) ℝ) :
    euclideanOperator (L - J) = euclideanOperator L - euclideanOperator J := by
  exact map_sub (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) L J

/-- Helper for lem:polar-continuation: a matrix perturbation is bounded in the fixed Lyapunov
norm. -/
theorem lyapunovNorm_operator_le (J L : Matrix (Fin 2) (Fin 2) ℝ) {κ : ℝ}
    (hκ : |κ| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (euclideanOperator L x) ≤
      (Real.sqrt (lyapunovBound J κ) * ‖euclideanOperator L‖) * lyapunovNorm J κ x := by
  calc
    lyapunovNorm J κ (euclideanOperator L x) ≤
        Real.sqrt (lyapunovBound J κ) * ‖euclideanOperator L x‖ := lyapunovNorm_le J hκ _
    _ ≤ Real.sqrt (lyapunovBound J κ) * (‖euclideanOperator L‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((euclideanOperator L).le_opNorm x) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (lyapunovBound J κ) * (‖euclideanOperator L‖ * lyapunovNorm J κ x) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_le_lyapunovNorm J hκ x) (norm_nonneg _))
        (Real.sqrt_nonneg _)
    _ = (Real.sqrt (lyapunovBound J κ) * ‖euclideanOperator L‖) * lyapunovNorm J κ x := by
      ring

/-- Helper for lem:polar-continuation: contraction persists under small changes of the Jacobian. -/
theorem lyapunovNorm_perturbation {J : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ}
    (hJ : J * J = κ • J) (hκ : |κ| < 1) (L : Matrix (Fin 2) (Fin 2) ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    lyapunovNorm J κ (euclideanOperator L x) ≤
      (contractionFactor J κ + Real.sqrt (lyapunovBound J κ) *
        ‖euclideanOperator (L - J)‖) * lyapunovNorm J κ x := by
  have hdecomp : euclideanOperator L x =
      euclideanOperator J x + euclideanOperator (L - J) x := by
    rw [euclideanOperator_sub, sub_apply]
    abel
  rw [hdecomp]
  calc
    lyapunovNorm J κ (euclideanOperator J x + euclideanOperator (L - J) x) ≤
        lyapunovNorm J κ (euclideanOperator J x) +
          lyapunovNorm J κ (euclideanOperator (L - J) x) := lyapunovNorm_add_le _ _ _ _
    _ ≤ contractionFactor J κ * lyapunovNorm J κ x +
        (Real.sqrt (lyapunovBound J κ) * ‖euclideanOperator (L - J)‖) * lyapunovNorm J κ x :=
      add_le_add (lyapunovNorm_contraction hJ hκ x) (lyapunovNorm_operator_le J _ hκ x)
    _ = (contractionFactor J κ + Real.sqrt (lyapunovBound J κ) *
        ‖euclideanOperator (L - J)‖) * lyapunovNorm J κ x := by ring

/-- Helper for lem:polar-continuation: the fixed source norm on the two fast coordinates. -/
def fixedNorm (ell z : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  lyapunovNorm (baseTransverseJacobian ell z) (baseKappa ell z) (WithLp.toLp 2 u)

/-- Helper for lem:polar-continuation: the matrix formula for the fixed norm. -/
theorem fixedNorm_def (ell z : ℝ) (u : Fin 2 → ℝ) :
    fixedNorm ell z u =
      lyapunovNorm (baseTransverseJacobian ell z) (baseKappa ell z) (WithLp.toLp 2 u) := by
  rfl

/-- Helper for lem:polar-continuation: the fixed source norm is nonnegative. -/
theorem fixedNorm_nonneg (ell z : ℝ) (u : Fin 2 → ℝ) : 0 ≤ fixedNorm ell z u := by
  exact lyapunovNorm_nonneg _ _ _

/-- Helper for lem:polar-continuation: the fixed source norm dominates the coordinate supremum
norm. -/
theorem norm_le_fixedNorm {ell z : ℝ} (hκ : |baseKappa ell z| < 1) (u : Fin 2 → ℝ) :
    ‖u‖ ≤ fixedNorm ell z u := by
  have hpi : ‖u‖ ≤ ‖WithLp.toLp 2 u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp 2 u))).mpr
    intro i
    exact PiLp.norm_apply_le (WithLp.toLp 2 u) i
  exact hpi.trans (norm_le_lyapunovNorm _ hκ _)

/-- Helper for lem:polar-continuation: the fixed source norm is absolutely homogeneous. -/
theorem fixedNorm_smul (ell z a : ℝ) (u : Fin 2 → ℝ) :
    fixedNorm ell z (a • u) = |a| * fixedNorm ell z u := by
  exact lyapunovNorm_smul _ _ _ _

/-- Helper for lem:polar-continuation: a strict factor with room for nearby Jacobians. -/
def fixedFactor (ell z : ℝ) : ℝ :=
  (1 + contractionFactor (baseTransverseJacobian ell z) (baseKappa ell z)) / 2

/-- Helper for lem:polar-continuation: the fixed nearby-state contraction factor lies in `(0,1)`. -/
theorem fixedFactor_bounds {ell z : ℝ} (hκ : |baseKappa ell z| < 1) :
    0 < fixedFactor ell z ∧ fixedFactor ell z < 1 := by
  have hb := contractionFactor_bounds (baseTransverseJacobian ell z) hκ
  dsimp [fixedFactor]
  constructor
  · linarith
  · linarith

/-- Helper for lem:polar-continuation: the fixed norm bounds a perturbed transverse matrix. -/
theorem fixedNorm_matrix_perturbation {ell z : ℝ} (hell : 1 < ell)
    (hκ : |baseKappa ell z| < 1) (L : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    fixedNorm ell z (L *ᵥ u) ≤
      (contractionFactor (baseTransverseJacobian ell z) (baseKappa ell z) +
        Real.sqrt (lyapunovBound (baseTransverseJacobian ell z) (baseKappa ell z)) *
          ‖euclideanOperator (L - baseTransverseJacobian ell z)‖) * fixedNorm ell z u := by
  have hellpos : 0 < ell := lt_trans zero_lt_one hell
  simpa only [fixedNorm_def, euclideanOperator_toLp] using
    lyapunovNorm_perturbation (baseTransverseJacobian_mul_self hellpos.ne') hκ L (WithLp.toLp 2 u)

/-- Helper for lem:polar-continuation: the same fixed norm contracts every sufficiently nearby
regular cycle derivative. -/
theorem eventually_fixedNorm_cycleDerivative_le {ell z : ℝ} (hell : 1 < ell)
    (hz : 0 < z) (hκ : |baseKappa ell z| < 1) :
    ∀ᶠ p : ℝ × (Fin 2 → ℝ) in
        𝓝 (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)),
      p.2 0 ≠ 0 ∧ leadingFast (baseDeltaEven ell z) p.1 p.2 0 ≠ 0 ∧
        ∀ u : Fin 2 → ℝ,
          fixedNorm ell z (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z)
            p.1 p.2 *ᵥ u) ≤ fixedFactor ell z * fixedNorm ell z u := by
  let J := baseTransverseJacobian ell z
  let κ := baseKappa ell z
  let q := contractionFactor J κ
  let B := Real.sqrt (lyapunovBound J κ)
  let ε := (1 - q) / (2 * B)
  have hq : q < 1 := (contractionFactor_bounds J hκ).2
  have hB : 0 < B :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_lyapunovBound J hκ))
  have hε : 0 < ε := div_pos (sub_pos.mpr hq) (mul_pos zero_lt_two hB)
  have hformula : q + B * ε = (1 + q) / 2 := by
    dsimp only [ε]
    field_simp [hB.ne']
    ring
  have hC := (base_nonsingular hell hz).1
  have hCNext := (base_nonsingular hell hz).2
  have hd := continuousAt_cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z)
    (baseGamma ell z) _ hC hCNext
  have hnorm : ContinuousAt
      (fun p : ℝ × (Fin 2 → ℝ) ↦
        ‖euclideanOperator (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z)
          p.1 p.2 - J)‖)
      (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) :=
    (continuous_euclideanOperator.continuousAt.comp (hd.sub continuousAt_const)).norm
  have hsmallBase :
      ‖euclideanOperator (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z)
        (baseGamma ell z) (fastCoordinates (cycleState (baseGamma ell z) ell)) - J)‖ < ε := by
    rw [cycleDerivative_base hell hz]
    simpa only [J, sub_self, euclideanOperator, map_zero, norm_zero] using hε
  have hsmall := hnorm.eventually (eventually_lt_nhds hsmallBase)
  have hcoordinate : ContinuousAt (fun p : ℝ × (Fin 2 → ℝ) ↦ p.2 0)
      (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) := by fun_prop
  have hstage := DFP.Polar.FastContraction.continuousAt_leadingFast (baseDeltaEven ell z)
    (baseGamma ell z) _ hC
  filter_upwards [hcoordinate.eventually_ne hC,
    (continuousAt_pi.mp hstage 0).eventually_ne hCNext, hsmall] with p hp hpNext hsmallp
  refine ⟨hp, hpNext, ?_⟩
  intro u
  have hcoeff : q + B *
      ‖euclideanOperator (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z)
        p.1 p.2 - J)‖ ≤ (1 + q) / 2 := by
    have hmul := mul_lt_mul_of_pos_left hsmallp hB
    linarith
  exact (fixedNorm_matrix_perturbation hell hκ _ u).trans
    (mul_le_mul_of_nonneg_right hcoeff (fixedNorm_nonneg ell z u))

/-- Helper for lem:polar-continuation: the fixed Euclidean embedding on ordinary fast
coordinates. -/
def fixedEmbedding (ell z : ℝ) (u : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 4) :=
  lyapunovEmbedding (baseTransverseJacobian ell z) (baseKappa ell z) (WithLp.toLp 2 u)

/-- Helper for lem:polar-continuation: the fixed embedding preserves fast-vector addition. -/
theorem fixedEmbedding_add (ell z : ℝ) (u v : Fin 2 → ℝ) :
    fixedEmbedding ell z (u + v) = fixedEmbedding ell z u + fixedEmbedding ell z v := by
  exact lyapunovEmbedding_add _ _ _ _

/-- Helper for lem:polar-continuation: the fixed embedding preserves real scalar multiplication. -/
theorem fixedEmbedding_smul (ell z a : ℝ) (u : Fin 2 → ℝ) :
    fixedEmbedding ell z (a • u) = a • fixedEmbedding ell z u := by
  exact lyapunovEmbedding_smul _ _ _ _

/-- Helper for lem:polar-continuation: the fixed embedding as a linear map. -/
def fixedEmbeddingLinear (ell z : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun := fixedEmbedding ell z
  map_add' := fixedEmbedding_add ell z
  map_smul' := fixedEmbedding_smul ell z

/-- Helper for lem:polar-continuation: the fixed embedding as a continuous linear map. -/
def fixedEmbeddingOperator (ell z : ℝ) : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (fixedEmbeddingLinear ell z).toContinuousLinearMap

/-- Helper for lem:polar-continuation: the fixed norm is the norm of a continuous linear
embedding. -/
theorem fixedNorm_eq_norm (ell z : ℝ) (u : Fin 2 → ℝ) :
    fixedNorm ell z u = ‖fixedEmbeddingOperator ell z u‖ := by
  rfl

/-- Helper for lem:polar-continuation: a continuous curve of genuine fixed points has one
uniform fast contraction radius in the source's fixed norm. -/
theorem exists_uniform_leadingCycle_contraction {ell z : ℝ} (hell : 1 < ell)
    (hz : 0 < z) (hκ : |baseKappa ell z| < 1) (reference : ℝ → Fin 2 → ℝ)
    (hcont : ContinuousAt reference (baseGamma ell z))
    (hbase : reference (baseGamma ell z) = fastCoordinates (cycleState (baseGamma ell z) ell))
    (hfix : ∀ᶠ γ in 𝓝 (baseGamma ell z),
      leadingCycle (baseDeltaEven ell z) (baseDeltaOdd ell z) γ (reference γ) = reference γ) :
    ∃ r > 0, ∀ᶠ γ in 𝓝 (baseGamma ell z),
      ∀ u : Fin 2 → ℝ, fixedNorm ell z u < r →
        fixedNorm ell z
            (leadingCycle (baseDeltaEven ell z) (baseDeltaOdd ell z) γ (reference γ + u) -
              reference γ) ≤ fixedFactor ell z * fixedNorm ell z u := by
  obtain ⟨ε, hε, hcontract⟩ := Metric.eventually_nhds_iff.mp
    (eventually_fixedNorm_cycleDerivative_le hell hz hκ)
  have hcurve : ContinuousAt (fun γ : ℝ ↦ (γ, reference γ)) (baseGamma ell z) :=
    continuousAt_id.prodMk hcont
  have htendsto : Filter.Tendsto (fun γ : ℝ ↦ (γ, reference γ)) (𝓝 (baseGamma ell z))
      (𝓝 (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell))) := by
    simpa only [ContinuousAt, hbase] using hcurve
  have hnear : ∀ᶠ γ in 𝓝 (baseGamma ell z),
      dist (γ, reference γ)
        (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) < ε / 2 :=
    htendsto.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [hnear, hfix] with γ hγnear hγfix
  intro u hu
  have hnormu : ‖u‖ < ε / 2 := (norm_le_fixedNorm hκ u).trans_lt hu
  have hsegment : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      dist (γ, reference γ + s • u)
        (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) < ε := by
    intro s hs
    have hsmul : ‖s • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg u) hs.2
    have hdist : dist (γ, reference γ + s • u) (γ, reference γ) < ε / 2 := by
      rw [dist_prod_same_left, dist_eq_norm]
      simpa only [add_sub_cancel_left] using hsmul.trans_lt hnormu
    calc
      dist (γ, reference γ + s • u)
          (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) ≤
        dist (γ, reference γ + s • u) (γ, reference γ) +
          dist (γ, reference γ)
            (baseGamma ell z, fastCoordinates (cycleState (baseGamma ell z) ell)) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdist hγnear
      _ = ε := by ring
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun s : ℝ ↦ fixedEmbeddingOperator ell z
          (leadingCycle (baseDeltaEven ell z) (baseDeltaOdd ell z) γ (reference γ + s • u)))
        (fixedEmbeddingOperator ell z
          (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z) γ
            (reference γ + s • u) *ᵥ u)) s := by
    intro s hs
    have hstate := hcontract (hsegment s hs)
    have hline : HasDerivAt (fun s : ℝ ↦ reference γ + s • u) u s := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id s).smul_const u).const_add (reference γ)
    have hcycle := (hasFDerivAt_leadingCycle (baseDeltaEven ell z) (baseDeltaOdd ell z)
      γ (reference γ + s • u) hstate.1 hstate.2.1).comp_hasDerivAt s hline
    have houtput := (fixedEmbeddingOperator ell z).hasFDerivAt.comp_hasDerivAt s hcycle
    simpa only [Function.comp_def, DFP.Polar.FastContraction.matrixOperator_apply] using houtput
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖fixedEmbeddingOperator ell z
        (cycleDerivative (baseDeltaEven ell z) (baseDeltaOdd ell z) γ
          (reference γ + s • u) *ᵥ u)‖ ≤ fixedFactor ell z * fixedNorm ell z u := by
    intro s hs
    rw [← fixedNorm_eq_norm]
    exact (hcontract (hsegment s (Set.Ico_subset_Icc_self hs))).2.2 u
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s hs ↦ (hderiv s hs).hasDerivWithinAt) hbound
  simpa only [zero_smul, one_smul, add_zero, hγfix, ← map_sub, fixedNorm_eq_norm] using hmean

/-- Helper for lem:polar-continuation: the fast coordinates of the source's genuine even
reference. -/
def evenFastReference (p : Parameters) (γ : ℝ) : Fin 2 → ℝ :=
  fastCoordinates (p.evenReference γ)

/-- Helper for lem:polar-continuation: the fast reference is the projection of the genuine
family. -/
theorem evenFastReference_apply (p : Parameters) (γ : ℝ) :
    evenFastReference p γ = fastCoordinates (p.evenReference γ) := by
  rfl

/-- Helper for lem:polar-continuation: the source's genuine fast reference is continuous at its
base. -/
theorem continuousAt_evenFastReference (p : Parameters) :
    ContinuousAt (evenFastReference p) p.gammaStar := by
  have h := p.evenReference_analyticAt.continuousAt
  simp only [funext (evenFastReference_apply p), DFP.Polar.FastContraction.fastCoordinates_apply]
  fun_prop

/-- Helper for lem:polar-continuation: the source fast reference at equilibrium is the selected
base state. -/
theorem evenFastReference_gammaStar (p : Parameters) :
    evenFastReference p p.gammaStar = fastCoordinates (cycleState p.gammaStar p.ell) := by
  rw [evenFastReference_apply, p.evenReference_gammaStar, p.initialState_def]

/-- Helper for lem:polar-continuation: the general limiting cycle fixes the genuine fast
reference near equilibrium. -/
theorem leadingCycle_evenFastReference_eventually (p : Parameters) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      leadingCycle p.deltaEven p.deltaOdd γ (evenFastReference p γ) = evenFastReference p γ := by
  filter_upwards [p.leadingCycle_eventually_fixed] with γ hfix
  have h := congrArg fastCoordinates hfix
  rw [Parameters.leadingStage_eq_original, Parameters.leadingStage_eq_original,
    ← leadingCycle_fastCoordinates, p.evenReference_fst γ] at h
  simpa only [evenFastReference_apply] using h

/-- Helper for lem:polar-continuation: the actual source reference family has a uniform
fixed-norm contraction radius, chosen independently of the starting index. -/
theorem exists_uniform_reference_contraction (p : Parameters) :
    ∃ r > 0, ∀ᶠ γ in 𝓝 p.gammaStar,
      ∀ u : Fin 2 → ℝ, fixedNorm p.ell p.z u < r →
        fixedNorm p.ell p.z
            (leadingCycle p.deltaEven p.deltaOdd γ (evenFastReference p γ + u) -
              evenFastReference p γ) ≤ fixedFactor p.ell p.z * fixedNorm p.ell p.z u := by
  have hcont : ContinuousAt (evenFastReference p) (baseGamma p.ell p.z) := by
    simpa only [p.gammaStar_def] using continuousAt_evenFastReference p
  have hbase : evenFastReference p (baseGamma p.ell p.z) =
      fastCoordinates (cycleState (baseGamma p.ell p.z) p.ell) := by
    simpa only [p.gammaStar_def] using evenFastReference_gammaStar p
  have hfix : ∀ᶠ γ in 𝓝 (baseGamma p.ell p.z),
      leadingCycle (baseDeltaEven p.ell p.z) (baseDeltaOdd p.ell p.z) γ
        (evenFastReference p γ) = evenFastReference p γ := by
    simpa only [p.gammaStar_def, p.deltaEven_def, p.deltaOdd_def] using
      leadingCycle_evenFastReference_eventually p
  have h := exists_uniform_leadingCycle_contraction p.base.one_lt_ell p.base.z_pos p.base.stable
    (evenFastReference p) hcont hbase hfix
  simpa only [p.gammaStar_def, p.deltaEven_def, p.deltaOdd_def] using h

end DFP.Polar.General.FastContraction
