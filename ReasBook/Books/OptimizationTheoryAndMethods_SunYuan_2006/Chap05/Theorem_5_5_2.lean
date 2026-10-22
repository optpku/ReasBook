/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_5_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

/-
Domain sampling:
* primary domain: spectral interval control for Chapter 5 Broyden-class product matrices and
  their Hermitian SSVM representatives;
* sampled project owners in this domain: `ssvmInverseUpdate`,
  `ssvmInverseUpdate_self_isHermitian`, `ssvmInverseUpdate_one_eq_broydenClassDirection`, and
  `broydenClassInverseUpdate`;
* sampled mathlib owners in this domain: `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`,
  `Matrix.IsHermitian.spectrum_eq_image_range`, `Matrix.spectrum_toLin'`,
  `Module.End.hasEigenvalue_iff_mem_spectrum`, and `spectrum.units_conjugate`.

Source/core/bridge triage:
* source-facing: interval bounds for the spectrum/eigenvalues of `Hk * G` and
  `(broydenClassInverseUpdate Hk s y φ) * G`;
* core/canonical: the owner `ssvmInverseUpdate` together with the mathlib Hermitian-spectrum and
  `HasEigenvalue` APIs;
* bridge/view: the explicit similarity hypothesis
  `ssvmInverseUpdate R r r φ 1 = Q * (broydenClassInverseUpdate Hk s y φ * G) * Q⁻¹`.

Primitive data here: the current product matrix `Hk * G`, the updated product matrix
`(broydenClassInverseUpdate Hk s y φ) * G`, and the interval bounds on the current spectrum.
Derived API here: Hermitian persistence for SSVM representatives and bridge lemmas transferring
spectral/eigenvalue control from those representatives to the Broyden product matrix.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- If `R` is Hermitian, then the representative specialization `ssvmInverseUpdate R r r φ γ`
remains Hermitian. -/
theorem ssvmInverseUpdate_self_isHermitian
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) (φ γ : ℝ) :
    (ssvmInverseUpdate R r r φ γ).IsHermitian := by
  have hRsymm : R.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hR
  have hDfp : Matrix.IsSymm (dfpInverseUpdate R r r) := by
    -- Expand the DFP base term and use symmetry of each self-outer-product summand.
    simpa [dfpInverseUpdate, sub_eq_add_neg, add_assoc] using
      hRsymm.add
        (((outerSelf_isSymm r).smul ((dotProduct r r)⁻¹)).add
          ((outerSelf_isSymm (R.toEuclideanLin r)).smul (-(dotProduct r (R.mulVec r))⁻¹)))
  have hCorrection :
      Matrix.IsSymm
        ((φ * dotProduct r (R.mulVec r)) •
          Matrix.vecMulVec (ssvmCorrectionVector R r r) (ssvmCorrectionVector R r r)) := by
    -- The SSVM correction is another scaled self-outer-product.
    simpa using
      (outerSelf_isSymm (ssvmCorrectionVector R r r)).smul (φ * dotProduct r (R.mulVec r))
  have hTail :
      Matrix.IsSymm (((1 - γ) * (dotProduct r r)⁻¹) • Matrix.vecMulVec r r) := by
    -- The final rank-one term is symmetric for the same reason.
    simpa using (outerSelf_isSymm r).smul ((1 - γ) * (dotProduct r r)⁻¹)
  have hInner :
      Matrix.IsSymm
        (dfpInverseUpdate R r r
          + (φ * dotProduct r (R.mulVec r)) •
              Matrix.vecMulVec (ssvmCorrectionVector R r r) (ssvmCorrectionVector R r r)) := by
    -- Package the two symmetric terms before applying the SSVM scaling.
    exact hDfp.add hCorrection
  -- Rewrite the owner into its canonical normal form and convert symmetry back to Hermitian.
  rw [ssvmInverseUpdate_eq_dfpInverseUpdate_add]
  simpa [Matrix.isHermitian_iff_isSymm] using (hInner.smul γ).add hTail

/-- The `γ = 1` specialization of `ssvmInverseUpdate_self_isHermitian`. -/
theorem ssvmInverseUpdate_self_one_isHermitian
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) (φ : ℝ) :
    (ssvmInverseUpdate R r r φ 1).IsHermitian := by
  simpa using ssvmInverseUpdate_self_isHermitian hR r φ 1

/-- Helper for Chapter05 Theorem 5.5.2: Hermitian eigenvalue bounds give the scalar matrix bounds
`lambdaMin • 1 ≤ R ≤ lambdaMax • 1`. -/
lemma hermitianScalarBounds_of_eigenvalueBounds
    {R : MatrixN} (hR : R.IsHermitian) {lambdaMin lambdaMax : ℝ}
    (hBounds : ∀ i : Fin n, hR.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax) :
    ((R - lambdaMin • (1 : MatrixN)).PosSemidef ∧
      (lambdaMax • (1 : MatrixN) - R).PosSemidef) := by
  -- Move the interval hypothesis from indexed eigenvalues to the real spectrum of `R`.
  have hLowerSpec : ∀ x ∈ spectrum ℝ R, lambdaMin ≤ x := by
    intro x hx
    have hxRange : x ∈ Set.range hR.eigenvalues := by
      simpa [hR.spectrum_real_eq_range_eigenvalues] using hx
    rcases hxRange with ⟨i, rfl⟩
    exact (hBounds i).1
  have hUpperSpec : ∀ x ∈ spectrum ℝ R, x ≤ lambdaMax := by
    intro x hx
    have hxRange : x ∈ Set.range hR.eigenvalues := by
      simpa [hR.spectrum_real_eq_range_eigenvalues] using hx
    rcases hxRange with ⟨i, rfl⟩
    exact (hBounds i).2
  -- Convert the spectral bounds to the matrix order bounds.
  constructor
  · simpa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using
      (algebraMap_le_of_le_spectrum (A := MatrixN) (a := R) (r := lambdaMin) hLowerSpec)
  · simpa [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using
      (le_algebraMap_of_spectrum_le (A := MatrixN) (a := R) (r := lambdaMax) hUpperSpec)

/-- Helper for Chapter05 Theorem 5.5.2: the self-update at `γ = 1` moves monotonically along the
rank-one SSVM correction segment as `φ` varies in `[0, 1]`. -/
lemma ssvmInverseUpdate_self_one_monotoneSegment
    {R : MatrixN} (r : Point) {φ : ℝ}
    (hrRr_pos : 0 < dotProduct r (R.mulVec r)) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    ((ssvmInverseUpdate R r r φ 1 - dfpInverseUpdate R r r).PosSemidef ∧
      (ssvmInverseUpdate R r r 1 1 - ssvmInverseUpdate R r r φ 1).PosSemidef) := by
  let C :=
    (dotProduct r (R.mulVec r)) •
      Matrix.vecMulVec (ssvmCorrectionVector R r r) (ssvmCorrectionVector R r r)
  have hC : C.PosSemidef := by
    -- The common SSVM direction correction is a nonnegative scalar multiple of a self outer
    -- product.
    dsimp [C]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul hrRr_pos.le
  constructor
  · -- The lower endpoint-to-`φ` difference is `φ • C`.
    have hEq :
        ssvmInverseUpdate R r r φ 1 - dfpInverseUpdate R r r = φ • C := by
      rw [ssvmInverseUpdate_eq_dfpInverseUpdate_add]
      ext i j
      simp [C, Matrix.vecMulVec_apply, sub_eq_add_neg]
      ring
    rw [hEq]
    exact hC.smul hφ.1
  · -- The `φ`-to-upper-endpoint difference is `(1 - φ) • C`.
    have hEq :
        ssvmInverseUpdate R r r 1 1 - ssvmInverseUpdate R r r φ 1 = (1 - φ) • C := by
      rw [ssvmInverseUpdate_eq_dfpInverseUpdate_add, ssvmInverseUpdate_eq_dfpInverseUpdate_add]
      ext i j
      simp [C, Matrix.vecMulVec_apply, sub_eq_add_neg]
      ring
    rw [hEq]
    exact hC.smul (sub_nonneg.mpr hφ.2)

/-- Helper for Chapter05 Theorem 5.5.2: every affine line through `r` stays above the orthogonal
projection lower bound onto `r⊥`. -/
lemma dotProduct_sub_smul_self_ge_projection
    {r x : Point} (hrr : dotProduct r r ≠ 0) (α : ℝ) :
    dotProduct x x - (dotProduct r x)^2 / dotProduct r r ≤
      dotProduct (x - α • r) (x - α • r) := by
  have hrr_nonneg : 0 ≤ dotProduct r r := by
    simpa [dotProduct, pow_two] using Finset.sum_nonneg (fun i _ ↦ sq_nonneg (r i))
  have hExpand :
      dotProduct (x - α • r) (x - α • r) =
        dotProduct x x - 2 * α * dotProduct r x + α ^ (2 : ℕ) * dotProduct r r := by
    -- Expand the quadratic form of the shifted vector and collect the mixed terms.
    simp [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_comm]
    ring
  have hSquare :
      dotProduct (x - α • r) (x - α • r) - (dotProduct x x - (dotProduct r x)^2 / dotProduct r r) =
        (α * dotProduct r r - dotProduct r x) ^ (2 : ℕ) / dotProduct r r := by
    rw [hExpand]
    field_simp [hrr]
    ring
  have hNonneg :
      0 ≤ dotProduct (x - α • r) (x - α • r) - (dotProduct x x - (dotProduct r x)^2 / dotProduct r r) := by
    rw [hSquare]
    exact div_nonneg (sq_nonneg _) hrr_nonneg
  nlinarith

/-- Helper for Chapter05 Theorem 5.5.2: the Euclidean projection onto `span {r}` gives the exact
Pythagorean decomposition for `x`. -/
lemma projectionSplit_dotProduct
    {r x : Point} (hrr : dotProduct r r ≠ 0) :
    let β := (dotProduct r x)^2 / dotProduct r r
    let z := x - (dotProduct r x / dotProduct r r) • r
    dotProduct z z + β = dotProduct x x := by
  dsimp
  -- Expand the projector residual and then clear the denominator `dotProduct r r`.
  simp [dotProduct_sub, dotProduct_smul, dotProduct_comm]
  field_simp [hrr]
  ring

/-- Helper for Chapter05 Theorem 5.5.2: the scalar matrix `c • 1` evaluates on quadratic forms as
scalar multiplication of `dotProduct x x`. -/
lemma scalarIdentity_dotProduct_mulVec
    (c : ℝ) (x : Point) :
    dotProduct x (((c : ℝ) • (1 : MatrixN)).mulVec x) = c * dotProduct x x := by
  -- Normalize the scalar-identity action to scalar multiplication on the vector itself.
  simp [Matrix.smul_mulVec, dotProduct_smul]

/-- Helper for Chapter05 Theorem 5.5.2: in the symmetric self-update setting, the `γ = 1`,
`φ = 1` SSVM formula agrees with the compact BFGS inverse update. -/
lemma ssvmInverseUpdate_self_one_eq_bfgsInverseUpdate
    {R : MatrixN} (hR : R.IsHermitian) (r : Point)
    (hrRr : dotProduct r (R.mulVec r) ≠ 0) :
    ssvmInverseUpdate R r r 1 1 = bfgsInverseUpdate R r r := by
  have hRsymm : R.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hR
  have hyH : r ᵥ* R = R *ᵥ r := by
    simpa [hRsymm.eq] using (Matrix.vecMul_transpose R r)
  have hcorr :
      (dotProduct r (R.mulVec r)) •
          Matrix.vecMulVec (ssvmCorrectionVector R r r) (ssvmCorrectionVector R r r) =
        (dotProduct r (R.mulVec r) * (dotProduct r r)⁻¹ * (dotProduct r r)⁻¹) •
            Matrix.vecMulVec r r
          - (dotProduct r r)⁻¹ •
              (Matrix.vecMulVec r (R.mulVec r) + Matrix.vecMulVec (R.mulVec r) r)
          + (dotProduct r (R.mulVec r))⁻¹ •
              Matrix.vecMulVec (R.mulVec r) (R.mulVec r) := by
    by_cases hrr : dotProduct r r = 0
    · ext i j
      simp [ssvmCorrectionVector, Matrix.vecMulVec_apply, hrr]
      field_simp [hrRr]
    · ext i j
      simp [ssvmCorrectionVector, Matrix.vecMulVec_apply]
      field_simp [hrr, hrRr]
      ring_nf
  -- Route correction: identify the upper endpoint once so later bounds use the compact BFGS
  -- formula instead of repeatedly expanding the SSVM correction vector.
  rw [ssvmInverseUpdate_eq_dfpInverseUpdate_add]
  rw [bfgsInverseUpdate_eq_expandedForm]
  rw [Matrix.vecMulVec_mul, hyH, Matrix.mul_vecMulVec]
  rw [dfpInverseUpdate, ← smul_smul, hcorr]
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring

/-- Helper for Chapter05 Theorem 5.5.2: the self-BFGS quadratic form splits into the `R`
quadratic form of the orthogonal residual plus the exact projection energy onto `span {r}`. -/
lemma bfgsSelfQuadratic_eq_projectedQuadratic
    {R : MatrixN} (hR : R.IsHermitian) (r x : Point)
    (hrr : dotProduct r r ≠ 0) :
    let z := x - (dotProduct r x / dotProduct r r) • r
    dotProduct x ((bfgsInverseUpdate R r r).mulVec x) =
      dotProduct z (R.mulVec z) + (dotProduct r x)^2 / dotProduct r r := by
  let z := x - (dotProduct r x / dotProduct r r) • r
  have hRsymm : R.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hR
  have hyH : r ᵥ* R = R *ᵥ r := by
    -- The row-vector action of `rᵀ` agrees with the column-vector action of `R` by symmetry.
    simpa [hRsymm.eq] using Matrix.vecMul_transpose R r
  have hxy : dotProduct r (R.mulVec x) = dotProduct x (R.mulVec r) := by
    -- Symmetry lets us swap the `R` action between the two slots of the quadratic form.
    simpa [hRsymm.eq, dotProduct_comm] using Matrix.dotProduct_transpose_mulVec R r x
  have hLhs :
      dotProduct x ((bfgsInverseUpdate R r r).mulVec x) =
        dotProduct x (R.mulVec x)
          + ((1 + dotProduct r (R.mulVec r) / dotProduct r r) * (dotProduct r r)⁻¹) *
              (dotProduct r x)^2
          - 2 * (dotProduct r r)⁻¹ * dotProduct r x * dotProduct x (R.mulVec r) := by
    -- Expand the BFGS update once and evaluate the resulting rank-one terms on `x`.
    rw [bfgsInverseUpdate_eq_expandedForm]
    rw [Matrix.vecMulVec_mul, hyH, Matrix.mul_vecMulVec]
    simp [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_comm, pow_two]
    ring_nf
  have hRhs :
      dotProduct z (R.mulVec z) + (dotProduct r x)^2 / dotProduct r r =
        dotProduct x (R.mulVec x)
          + ((1 + dotProduct r (R.mulVec r) / dotProduct r r) * (dotProduct r r)⁻¹) *
              (dotProduct r x)^2
          - 2 * (dotProduct r r)⁻¹ * dotProduct r x * dotProduct x (R.mulVec r) := by
    -- Expand the quadratic form of the orthogonal residual and collect the projection term.
    have hMul :
        R.mulVec z = R.mulVec x - (dotProduct r x / dotProduct r r) • R.mulVec r := by
      simpa [z, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg WithLp.ofLp
          ((Matrix.toEuclideanLin R).map_sub x ((dotProduct r x / dotProduct r r) • r))
    calc
      dotProduct z (R.mulVec z) + (dotProduct r x)^2 / dotProduct r r
          = dotProduct z
              (R.mulVec x - (dotProduct r x / dotProduct r r) • R.mulVec r)
              + (dotProduct r x)^2 / dotProduct r r := by
                rw [hMul]
      _ = dotProduct x (R.mulVec x)
            - (dotProduct r x / dotProduct r r) * dotProduct x (R.mulVec r)
            - (dotProduct r x / dotProduct r r) * dotProduct r (R.mulVec x)
            + (dotProduct r x / dotProduct r r) ^ (2 : ℕ) * dotProduct r (R.mulVec r)
            + (dotProduct r x)^2 / dotProduct r r := by
              simp [z, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
                pow_two, dotProduct_comm]
              ring_nf
      _ = dotProduct x (R.mulVec x)
            - 2 * (dotProduct r x / dotProduct r r) * dotProduct x (R.mulVec r)
            + (dotProduct r x / dotProduct r r) ^ (2 : ℕ) * dotProduct r (R.mulVec r)
            + (dotProduct r x)^2 / dotProduct r r := by
              rw [hxy]
              ring_nf
      _ = dotProduct x (R.mulVec x)
            + ((1 + dotProduct r (R.mulVec r) / dotProduct r r) * (dotProduct r r)⁻¹) *
                (dotProduct r x)^2
            - 2 * (dotProduct r r)⁻¹ * dotProduct r x * dotProduct x (R.mulVec r) := by
              field_simp [hrr]
              ring_nf
  -- The expanded BFGS quadratic form and the projected quadratic form are now identical.
  exact hLhs.trans hRhs.symm

/-- Helper for Chapter05 Theorem 5.5.2: the DFP self-update preserves the lower scalar bound
`lambdaMin • 1 ≤ R` when `lambdaMin ≤ 1`. -/
lemma dfpSelf_lowerScalarBound
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) {lambdaMin lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr_pos : 0 < dotProduct r (R.mulVec r))
    (hLambdaMin_nonneg : 0 ≤ lambdaMin) (hLower : (R - lambdaMin • (1 : MatrixN)).PosSemidef)
    (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax) :
    ((dfpInverseUpdate R r r) - lambdaMin • (1 : MatrixN)).PosSemidef := by
  have hRsymm : R.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hR
  have hDfpHerm : (dfpInverseUpdate R r r).IsHermitian := by
    -- The self-DFP update is Hermitian because each rank-one summand is symmetric.
    have hDfpSymm :
        (R
          + ((dotProduct r r)⁻¹ • Matrix.vecMulVec r r
            + (-(dotProduct r (R.mulVec r))⁻¹) •
                Matrix.vecMulVec (R.toEuclideanLin r) (R.toEuclideanLin r))).IsSymm := by
      exact hRsymm.add
        (((outerSelf_isSymm r).smul ((dotProduct r r)⁻¹)).add
          ((outerSelf_isSymm (R.toEuclideanLin r)).smul (-(dotProduct r (R.mulVec r))⁻¹)))
    simpa [dfpInverseUpdate, sub_eq_add_neg, add_assoc, Matrix.isHermitian_iff_isSymm] using hDfpSymm
  have hScalarHerm : (lambdaMin • (1 : MatrixN)).IsHermitian := by
    -- Scalar multiples of the identity are Hermitian over `ℝ`.
    simpa [Matrix.isHermitian_iff_isSymm] using (Matrix.isSymm_one.smul lambdaMin)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hDfpHerm.sub hScalarHerm) ?_
  intro x
  let xPt : Point := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  let α : ℝ := dotProduct xPt (R.mulVec r) / dotProduct r (R.mulVec r)
  let z : Point := xPt - α • r
  let β : ℝ := (dotProduct r xPt)^2 / dotProduct r r
  have hLower_eval : lambdaMin * dotProduct z z ≤ dotProduct z (R.mulVec z) := by
    -- Evaluate the lower scalar bound on the completed-square residual.
    have hz :
        0 ≤ dotProduct z (((R - lambdaMin • (1 : MatrixN)).mulVec z)) := hLower.dotProduct_mulVec_nonneg z
    have hz' : 0 ≤ dotProduct z (R.mulVec z) - lambdaMin * dotProduct z z := by
      simpa [Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec] using hz
    exact sub_nonneg.mp hz'
  have hProjection :
      dotProduct xPt xPt - β ≤ dotProduct z z := by
    -- The residual norm dominates the orthogonal-projection remainder.
    simpa [xPt, α, z, β] using
      dotProduct_sub_smul_self_ge_projection (r := r) (x := xPt) hrr α
  have hScaleProjection :
      lambdaMin * (dotProduct xPt xPt - β) ≤ lambdaMin * dotProduct z z := by
    -- `lambdaMin ≥ 0` lets the projection bound pass through scalar multiplication.
    exact mul_le_mul_of_nonneg_left hProjection hLambdaMin_nonneg
  have hβ_nonneg : 0 ≤ β := by
    -- The projection-energy term is nonnegative because `dotProduct r r > 0`.
    have hrr_nonneg : 0 ≤ dotProduct r r := by
      simpa [dotProduct, pow_two] using Finset.sum_nonneg (fun i _ ↦ sq_nonneg (r i))
    exact div_nonneg (sq_nonneg _) hrr_nonneg
  have hβ_scale : lambdaMin * β ≤ β := by
    -- The source hypothesis `lambdaMin ≤ 1` upgrades the secant term from `lambdaMin β` to `β`.
    simpa using mul_le_mul_of_nonneg_right hOne.1 hβ_nonneg
  have hMain :
      lambdaMin * dotProduct xPt xPt ≤ dotProduct z (R.mulVec z) + β := by
    -- Combine the lower scalar bound on `R` with the projection estimate and the secant term.
    nlinarith [hLower_eval, hScaleProjection, hβ_scale]
  have hCompleted :
      dotProduct xPt ((dfpInverseUpdate R r r).mulVec xPt) = dotProduct z (R.mulVec z) + β := by
    -- Route correction: normalize the self-DFP quadratic form through the completed-square API.
    simpa [xPt, α, z, β] using
      dfpInverseUpdate_dotProduct_mulVec_eq_completedSquare R r r xPt hRsymm hrr hrRr_pos.ne'
  have hx :
      0 ≤ dotProduct xPt ((((dfpInverseUpdate R r r) - lambdaMin • (1 : MatrixN))).mulVec xPt) := by
    -- Rewrite the target quadratic form to the completed-square normal form and compare it with
    -- `lambdaMin * ‖x‖²`.
    rw [Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec, hCompleted]
    nlinarith [hMain]
  simpa [xPt] using hx

/-- Helper for Chapter05 Theorem 5.5.2: the BFGS self-update preserves the upper scalar bound
`R ≤ lambdaMax • 1` when `1 ≤ lambdaMax`. -/
lemma bfgsSelfUpperPointwise_gap
    {R : MatrixN} (hR : R.IsHermitian) (r x : Point) {lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0) :
    let z := x - (dotProduct r x / dotProduct r r) • r
    let β := (dotProduct r x)^2 / dotProduct r r
    dotProduct x (((lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).mulVec x)) =
      dotProduct z (((lambdaMax • (1 : MatrixN) - R).mulVec z)) + (lambdaMax - 1) * β := by
  let z : Point := x - (dotProduct r x / dotProduct r r) • r
  let β : ℝ := (dotProduct r x)^2 / dotProduct r r
  have hProjection : dotProduct z z + β = dotProduct x x := by
    -- Rewrite the Euclidean norm of `x` into the orthogonal residual plus the projection energy.
    simpa [z, β] using projectionSplit_dotProduct (r := r) (x := x) hrr
  have hCompleted :
      dotProduct x ((ssvmInverseUpdate R r r 1 1).mulVec x) =
        dotProduct z (R.mulVec z) + β := by
    -- Route correction: identify the `γ = 1` endpoint with BFGS before using the projected
    -- quadratic-form decomposition.
    rw [ssvmInverseUpdate_self_one_eq_bfgsInverseUpdate hR r hrRr]
    simpa [z, β] using bfgsSelfQuadratic_eq_projectedQuadratic hR r x hrr
  calc
    dotProduct x (((lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).mulVec x))
        = lambdaMax * dotProduct x x - dotProduct x ((ssvmInverseUpdate R r r 1 1).mulVec x) := by
            rw [Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec]
    _ = lambdaMax * (dotProduct z z + β) - (dotProduct z (R.mulVec z) + β) := by
          rw [← hProjection, hCompleted]
    _ = (lambdaMax * dotProduct z z - dotProduct z (R.mulVec z)) + (lambdaMax - 1) * β := by
          ring
    _ = dotProduct z (((lambdaMax • (1 : MatrixN) - R).mulVec z)) + (lambdaMax - 1) * β := by
          rw [Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec]

/-- Helper for Chapter05 Theorem 5.5.2: the BFGS upper-endpoint quadratic form is nonnegative on
every `Point` once `lambdaMax • 1 - R` is positive semidefinite and `1 ≤ lambdaMax`. -/
lemma bfgsSelfUpperPointwise_nonneg
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) {lambdaMin lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hUpper : (lambdaMax • (1 : MatrixN) - R).PosSemidef)
    (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax) (x : Point) :
    0 ≤ dotProduct x (((lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).mulVec x)) := by
  let z : Point := x - (dotProduct r x / dotProduct r r) • r
  let β : ℝ := (dotProduct r x)^2 / dotProduct r r
  have hz :
      0 ≤ dotProduct z (((lambdaMax • (1 : MatrixN) - R).mulVec z)) := by
    -- Evaluate the upper scalar bound on the orthogonal residual from the projection split.
    simpa [z] using hUpper.dotProduct_mulVec_nonneg z
  have hrr_nonneg : 0 ≤ dotProduct r r := by
    -- The Euclidean self-dot-product of `r` is a sum of squares.
    simpa [dotProduct, pow_two] using Finset.sum_nonneg (fun i _ ↦ sq_nonneg (r i))
  have hβ_nonneg : 0 ≤ β := by
    -- The projection-energy term is nonnegative because its numerator and denominator are.
    exact div_nonneg (sq_nonneg (dotProduct r x)) hrr_nonneg
  have hScale_nonneg : 0 ≤ (lambdaMax - 1) * β := by
    -- The interval hypothesis supplies `1 ≤ lambdaMax`, so the extra projection term is
    -- nonnegative.
    exact mul_nonneg (sub_nonneg.mpr hOne.2) hβ_nonneg
  rw [bfgsSelfUpperPointwise_gap hR r x hrr hrRr]
  nlinarith [hz, hScale_nonneg]

lemma bfgsSelf_upperScalarBound
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) {lambdaMin lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hUpper : (lambdaMax • (1 : MatrixN) - R).PosSemidef)
    (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax) :
    (lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).PosSemidef := by
  have hScalarHerm : (lambdaMax • (1 : MatrixN)).IsHermitian := by
    -- Scalar multiples of the identity are Hermitian over `ℝ`.
    simpa [Matrix.isHermitian_iff_isSymm] using (Matrix.isSymm_one.smul lambdaMax)
  have hEndpointHerm : (lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).IsHermitian := by
    -- Route correction: keep Hermitian verification separate from the quadratic-form inequality,
    -- so the final positivity wrapper only sees the raw-vector-to-`Point` transport once.
    exact hScalarHerm.sub (ssvmInverseUpdate_self_one_isHermitian hR r 1)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hEndpointHerm ?_
  intro x
  let xPt : Point := (EuclideanSpace.equiv (Fin n) ℝ).symm x
  -- The endpoint nonnegativity has already been proved on `Point`; only the final transport
  -- from raw vectors remains here.
  simpa [xPt] using bfgsSelfUpperPointwise_nonneg hR r hrr hrRr hUpper hOne xPt

/-- Helper for Chapter05 Theorem 5.5.2: scalar matrix bounds on a Hermitian matrix turn directly
into interval bounds for each indexed eigenvalue. -/
lemma hermitianEigenvalue_mem_Icc_of_scalarBounds
    {A : MatrixN} (hA : A.IsHermitian) {lambdaMin lambdaMax : ℝ}
    (hLower : (A - lambdaMin • (1 : MatrixN)).PosSemidef)
    (hUpper : (lambdaMax • (1 : MatrixN) - A).PosSemidef) (i : Fin n) :
    hA.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax := by
  let e : Point := hA.eigenvectorBasis i
  have he_norm : dotProduct e e = 1 := by
    -- The Hermitian eigenvector basis is orthonormal, so each basis vector has unit Euclidean norm.
    have he_sq : dotProduct e e = ‖e‖ ^ (2 : ℕ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [e, dotProduct, pow_two]
    have he_normOne : ‖e‖ = 1 := by
      simpa [e] using hA.eigenvectorBasis.norm_eq_one i
    nlinarith [he_sq, he_normOne]
  have hLower_i :
      lambdaMin ≤ hA.eigenvalues i := by
    -- Evaluate the lower scalar bound on the `i`-th normalized eigenvector.
    have heval :
        0 ≤ dotProduct e (((A - lambdaMin • (1 : MatrixN)).mulVec e)) :=
      hLower.dotProduct_mulVec_nonneg e
    have heval' : lambdaMin ≤ hA.eigenvalues i := by
      simpa [e, Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec,
        hA.mulVec_eigenvectorBasis i, dotProduct_smul, he_norm] using heval
    exact heval'
  have hUpper_i :
      hA.eigenvalues i ≤ lambdaMax := by
    -- Evaluate the upper scalar bound on the same normalized eigenvector.
    have heval :
        0 ≤ dotProduct e (((lambdaMax • (1 : MatrixN) - A).mulVec e)) :=
      hUpper.dotProduct_mulVec_nonneg e
    have heval' : hA.eigenvalues i ≤ lambdaMax := by
      simpa [e, Matrix.sub_mulVec, dotProduct_sub, scalarIdentity_dotProduct_mulVec,
        hA.mulVec_eigenvectorBasis i, dotProduct_smul, he_norm] using heval
    exact heval'
  exact ⟨hLower_i, hUpper_i⟩

/-- If every indexed eigenvalue of a Hermitian representative `R_k` lies in
`Set.Icc lambdaMin lambdaMax`, `0 < lambdaMin`, `1 ∈ Set.Icc lambdaMin lambdaMax`, and
`φ ∈ Set.Icc (0 : ℝ) 1`, then every indexed eigenvalue of
`R_(k+1)^φ = ssvmInverseUpdate R_k r r φ 1` remains in `Set.Icc lambdaMin lambdaMax`. -/
theorem ssvmInverseUpdate_self_one_eigenvalues_mem_Icc
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) {φ lambdaMin lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hLambdaMin_pos : 0 < lambdaMin) (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax)
    (hBounds : ∀ i : Fin n, hR.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax)
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    let Rφ := ssvmInverseUpdate R r r φ 1
    let hRφ : Rφ.IsHermitian := ssvmInverseUpdate_self_isHermitian hR r φ 1
    hRφ.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax := by
  let Rφ : MatrixN := ssvmInverseUpdate R r r φ 1
  let hRφ : Rφ.IsHermitian := ssvmInverseUpdate_self_isHermitian hR r φ 1
  have hRpos : R.PosDef := by
    -- The spectral lower bound `lambdaMin > 0` forces the Hermitian representative `R` to be positive definite.
    rw [hR.posDef_iff_eigenvalues_pos]
    intro j
    exact lt_of_lt_of_le hLambdaMin_pos (hBounds j).1
  have hr_ne : r ≠ 0 := by
    -- A nonzero Euclidean norm denominator forces the secant vector to be nonzero.
    intro hr0
    apply hrr
    simp [hr0]
  have hrRr_pos : 0 < dotProduct r (R.mulVec r) := by
    -- Positive definiteness of `R` upgrades the curvature denominator to strict positivity.
    simpa using hRpos.dotProduct_mulVec_pos (by simpa using hr_ne)
  obtain ⟨hLowerR, hUpperR⟩ := hermitianScalarBounds_of_eigenvalueBounds hR hBounds
  have hLower0 :
      ((dfpInverseUpdate R r r) - lambdaMin • (1 : MatrixN)).PosSemidef :=
    dfpSelf_lowerScalarBound
      hR r hrr hrRr_pos hLambdaMin_pos.le hLowerR hOne
  have hUpper1 :
      (lambdaMax • (1 : MatrixN) - ssvmInverseUpdate R r r 1 1).PosSemidef :=
    bfgsSelf_upperScalarBound hR r hrr hrRr hUpperR hOne
  obtain ⟨hMonLower, hMonUpper⟩ :=
    ssvmInverseUpdate_self_one_monotoneSegment (R := R) r hrRr_pos hφ
  have hLowerφ : (Rφ - lambdaMin • (1 : MatrixN)).PosSemidef := by
    -- Convert the endpoint and segment bounds to matrix order and use transitivity.
    have hLower0Order : lambdaMin • (1 : MatrixN) ≤ dfpInverseUpdate R r r := by
      simpa [Matrix.le_iff] using hLower0
    have hMonLowerOrder : dfpInverseUpdate R r r ≤ Rφ := by
      simpa [Rφ, Matrix.le_iff] using hMonLower
    simpa [Matrix.le_iff] using le_trans hLower0Order hMonLowerOrder
  have hUpperφ : (lambdaMax • (1 : MatrixN) - Rφ).PosSemidef := by
    -- Convert the endpoint and segment bounds to matrix order and use transitivity.
    have hUpper1Order : ssvmInverseUpdate R r r 1 1 ≤ lambdaMax • (1 : MatrixN) := by
      simpa [Matrix.le_iff] using hUpper1
    have hMonUpperOrder : Rφ ≤ ssvmInverseUpdate R r r 1 1 := by
      simpa [Rφ, Matrix.le_iff] using hMonUpper
    simpa [Matrix.le_iff] using le_trans hMonUpperOrder hUpper1Order
  -- Apply the generic Hermitian scalar-bound closing lemma to the updated representative.
  simpa [Rφ, hRφ] using hermitianEigenvalue_mem_Icc_of_scalarBounds hRφ hLowerφ hUpperφ i

/-- If all eigenvalues of a Hermitian representative `R_k` lie in
`Set.Icc lambdaMin lambdaMax`, `0 < lambdaMin`, `1 ∈ Set.Icc lambdaMin lambdaMax`, and the SSVM
denominators `dotProduct r r` and `dotProduct r (R.mulVec r)` are nonzero, then every real
eigenvalue of `R_(k+1)^φ = ssvmInverseUpdate R_k r r φ 1` stays in the same interval. -/
theorem ssvmInverseUpdate_self_one_hasEigenvalue_mem_Icc
    {R : MatrixN} (hR : R.IsHermitian) (r : Point) {φ lambdaMin lambdaMax : ℝ}
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hLambdaMin_pos : 0 < lambdaMin) (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax)
    (hBounds : ∀ i : Fin n, hR.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax)
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue ((ssvmInverseUpdate R r r φ 1).toLin') μ) :
    μ ∈ Set.Icc lambdaMin lambdaMax := by
  let Rφ := ssvmInverseUpdate R r r φ 1
  let hRφ : Rφ.IsHermitian := ssvmInverseUpdate_self_isHermitian hR r φ 1
  have hμSpec : μ ∈ spectrum ℝ Rφ := by
    -- Move the real eigenvalue of the linear map back to the matrix spectrum.
    simpa [Rφ] using
      (show μ ∈ spectrum ℝ ((ssvmInverseUpdate R r r φ 1).toLin') from
        Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ)
  have hμRange : μ ∈ Set.range hRφ.eigenvalues := by
    -- Hermitian real spectra are exactly the range of indexed eigenvalues.
    simpa [Rφ, hRφ.spectrum_real_eq_range_eigenvalues] using hμSpec
  rcases hμRange with ⟨i, hi⟩
  -- Reduce the real-eigenvalue statement to the indexed eigenvalue statement.
  simpa [Rφ, hRφ, hi] using
    ssvmInverseUpdate_self_one_eigenvalues_mem_Icc
      hR r hrr hrRr hLambdaMin_pos hOne hBounds hφ i

/-- Helper for Chapter05 Theorem 5.5.2: a real eigenvalue of `A.toLin'` remains in the complex
spectrum of the complexified matrix `A.map (algebraMap ℝ ℂ)`. -/
lemma complexSpectrum_mem_of_realHasEigenvalue
    {A : MatrixN} {μ : ℝ} (hμ : Module.End.HasEigenvalue A.toLin' μ) :
    (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  let vC : Fin n → ℂ := fun i ↦ (v i : ℂ)
  have hv_eq : A *ᵥ v = μ • v := by
    -- Rewrite the linear-map eigenvector equation in matrix `mulVec` form.
    simpa [Matrix.toLin'_apply'] using hv.apply_eq_smul
  have hvC_ne : vC ≠ 0 := by
    -- The complexified eigenvector stays nonzero coordinatewise.
    intro hvZero
    apply hv.2
    ext i
    exact Complex.ofReal_injective (congrFun hvZero i)
  have hvC_eq : (A.map (algebraMap ℝ ℂ)) *ᵥ vC = (μ : ℂ) • vC := by
    -- Map the real eigenvector equation coordinatewise through `algebraMap ℝ ℂ`.
    ext i
    calc
      ((A.map (algebraMap ℝ ℂ)) *ᵥ vC) i = (algebraMap ℝ ℂ) ((A *ᵥ v) i) := by
        symm
        exact RingHom.map_mulVec (algebraMap ℝ ℂ) A v i
      _ = (μ : ℂ) * (v i : ℂ) := by
        simpa using congrArg (algebraMap ℝ ℂ) (congrFun hv_eq i)
      _ = ((μ : ℂ) • vC) i := by
        simp [vC]
  have hμC :
      Module.End.HasEigenvalue ((A.map (algebraMap ℝ ℂ)).toLin') (μ : ℂ) := by
    -- Package the complexified eigenvector into a complex eigenvalue witness.
    exact Module.End.hasEigenvalue_of_hasEigenvector (x := vC) <|
      (Module.End.hasEigenvector_iff).2 <|
        ⟨Module.End.mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply'] using hvC_eq), hvC_ne⟩
  -- Finish by translating the complex linear-map eigenvalue back to the matrix spectrum.
  simpa [Matrix.spectrum_toLin'] using
    (Module.End.hasEigenvalue_iff_mem_spectrum.mp hμC)

section ProductSpectrum

variable {Hk G R : MatrixN} {Q : MatrixNˣ} (s y r : Point) {φ lambdaMin lambdaMax : ℝ}

/-- Chapter05 Theorem 5.5.2: if a Hermitian representative `R_k` has all eigenvalues in
`Set.Icc lambdaMin lambdaMax` and the specialized self-scaling update
`ssvmInverseUpdate R_k r r φ 1` is explicitly similar to the updated product matrix, then the
complex spectrum of `(broydenClassInverseUpdate Hk s y φ) * G` lies in
`Complex.ofReal '' Set.Icc lambdaMin lambdaMax`. -/
theorem broydenClassInverseUpdate_mul_spectrum_subset_Icc
    (hR : R.IsHermitian)
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hSimilarity :
      ssvmInverseUpdate R r r φ 1 =
        Q * (broydenClassInverseUpdate Hk s y φ * G) * Q⁻¹)
    (hLambdaMin_pos : 0 < lambdaMin) (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax)
    (hBounds : ∀ i : Fin n, hR.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax)
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    spectrum ℂ
        (((broydenClassInverseUpdate Hk s y φ) * G).map (algebraMap ℝ ℂ)) ⊆
      (Complex.ofReal '' Set.Icc lambdaMin lambdaMax : Set ℂ) := by
  let f : ℝ →+* ℂ := algebraMap ℝ ℂ
  let Rφ : MatrixN := ssvmInverseUpdate R r r φ 1
  let A : MatrixN := (broydenClassInverseUpdate Hk s y φ) * G
  let hRφ : Rφ.IsHermitian := ssvmInverseUpdate_self_isHermitian hR r φ 1
  let QC : Matrix (Fin n) (Fin n) ℂˣ := Units.map (RingHom.mapMatrix f).toMonoidHom Q
  have hSimilarityC :
      Rφ.map f = (QC : Matrix (Fin n) (Fin n) ℂ) * A.map f * QC⁻¹ := by
    -- Complexify the explicit similarity witness so `spectrum.units_conjugate` applies.
    simpa [Rφ, A, QC, f, Matrix.map_mul] using congrArg (Matrix.map f) hSimilarity
  have hConj :
      spectrum ℂ ((QC : Matrix (Fin n) (Fin n) ℂ) * A.map f * QC⁻¹) = spectrum ℂ (A.map f) := by
    -- Conjugation by the mapped unit preserves the complex spectrum.
    simpa [QC] using (spectrum.units_conjugate (R := ℂ) (a := A.map f) (u := QC))
  intro z hz
  have hzRφ : z ∈ spectrum ℂ (Rφ.map f) := by
    -- Rewrite the updated product matrix spectrum through the explicit similarity.
    rw [hSimilarityC, hConj]
    exact hz
  have hRφC : (Rφ.map f).IsHermitian := by
    -- Mapping a real Hermitian matrix to `ℂ` preserves Hermitian symmetry.
    exact hRφ.map (by intro x; simp)
  rw [hRφC.spectrum_eq_image_range] at hzRφ
  rcases hzRφ with ⟨x, hxRange, rfl⟩
  rcases hxRange with ⟨i, rfl⟩
  refine ⟨hRφC.eigenvalues i, ?_, rfl⟩
  have hiSpecMap : hRφC.eigenvalues i ∈ spectrum ℝ (Rφ.map f) :=
    hRφC.eigenvalues_mem_spectrum_real i
  have hiSpec : hRφC.eigenvalues i ∈ spectrum ℝ Rφ := by
    -- Real spectral points of the mapped matrix come from real spectral points of the source.
    exact AlgHom.spectrum_apply_subset (RingHom.mapMatrix f) Rφ hiSpecMap
  have hiRange : hRφC.eigenvalues i ∈ Set.range hRφ.eigenvalues := by
    -- Move back to indexed eigenvalues of the real Hermitian representative.
    simpa [Rφ, hRφ.spectrum_real_eq_range_eigenvalues] using hiSpec
  rcases hiRange with ⟨j, hj⟩
  -- Apply the core representative interval theorem at the matching real indexed eigenvalue.
  simpa [hj] using
    ssvmInverseUpdate_self_one_eigenvalues_mem_Icc
      hR r hrr hrRr hLambdaMin_pos hOne hBounds hφ j

/-- Companion real-eigenvalue consequence of
`broydenClassInverseUpdate_mul_spectrum_subset_Icc`. -/
theorem broydenClassInverseUpdate_mul_hasEigenvalue_mem_Icc
    (hR : R.IsHermitian)
    (hrr : dotProduct r r ≠ 0) (hrRr : dotProduct r (R.mulVec r) ≠ 0)
    (hSimilarity :
      ssvmInverseUpdate R r r φ 1 =
        Q * (broydenClassInverseUpdate Hk s y φ * G) * Q⁻¹)
    (hLambdaMin_pos : 0 < lambdaMin) (hOne : 1 ∈ Set.Icc lambdaMin lambdaMax)
    (hBounds : ∀ i : Fin n, hR.eigenvalues i ∈ Set.Icc lambdaMin lambdaMax)
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (((broydenClassInverseUpdate Hk s y φ) * G).toLin') μ) :
    μ ∈ Set.Icc lambdaMin lambdaMax := by
  let A : MatrixN := (broydenClassInverseUpdate Hk s y φ) * G
  have hSpectrum :
      spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆
        (Complex.ofReal '' Set.Icc lambdaMin lambdaMax : Set ℂ) :=
    broydenClassInverseUpdate_mul_spectrum_subset_Icc
      (s := s) (y := y) (r := r)
      hR hrr hrRr hSimilarity hLambdaMin_pos hOne hBounds hφ
  have hμSpec : μ ∈ spectrum ℝ A := by
    -- Translate the real eigenvalue of `A.toLin'` to matrix-spectrum language.
    simpa [A] using
      (show μ ∈ spectrum ℝ (((broydenClassInverseUpdate Hk s y φ) * G).toLin') from
        Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ)
  have hμSpecC : (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
    -- Promote the real eigenvalue witness to the complexified matrix spectrum.
    simpa [A] using complexSpectrum_mem_of_realHasEigenvalue hμ
  rcases hSpectrum hμSpecC with ⟨x, hx, hxeq⟩
  have hxμ : x = μ := Complex.ofReal_injective hxeq
  -- The interval conclusion is exactly the real shadow of the spectral inclusion.
  simpa [hxμ] using hx

/-- If the complex spectrum of a real matrix `A` lies in
`Complex.ofReal '' Set.Icc lambdaMin lambdaMax`, then any real eigenvalue of `A` lies in
`Set.Icc lambdaMin lambdaMax`. -/
theorem hasEigenvalue_mem_Icc_of_spectrum_subset
    {A : MatrixN} {lambdaMin lambdaMax μ : ℝ}
    (hSpectrum :
      spectrum ℂ (A.map (algebraMap ℝ ℂ)) ⊆
        (Complex.ofReal '' Set.Icc lambdaMin lambdaMax : Set ℂ))
    (hμ : Module.End.HasEigenvalue A.toLin' μ) :
    μ ∈ Set.Icc lambdaMin lambdaMax := by
  have hμSpec : μ ∈ spectrum ℝ A := by
    -- Translate the real eigenvalue of `A.toLin'` to the real matrix spectrum.
    simpa using
      (show μ ∈ spectrum ℝ A.toLin' from Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ)
  have hμSpecC : (μ : ℂ) ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
    -- Promote the real eigenvalue witness to the complexified matrix spectrum.
    exact complexSpectrum_mem_of_realHasEigenvalue hμ
  rcases hSpectrum hμSpecC with ⟨x, hx, hxeq⟩
  have hxμ : x = μ := Complex.ofReal_injective hxeq
  -- The complex-spectrum enclosure records the desired real interval directly.
  simpa [hxμ] using hx

end ProductSpectrum

end
