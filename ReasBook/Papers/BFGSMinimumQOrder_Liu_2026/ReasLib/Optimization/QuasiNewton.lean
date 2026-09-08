module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

universe u

namespace BFGS

section Update

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The Hessian-form BFGS rank-two update. -/
noncomputable def update (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  B - (dotProduct s (Matrix.mulVec B s))⁻¹ •
      (B * Matrix.vecMulVec s s * B) +
    (dotProduct s y)⁻¹ • Matrix.vecMulVec y y

/-- The explicit rank-two formula for the Hessian-form BFGS update. -/
theorem update_def (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    update B s y =
      B - (dotProduct s (Matrix.mulVec B s))⁻¹ •
          (B * Matrix.vecMulVec s s * B) +
        (dotProduct s y)⁻¹ • Matrix.vecMulVec y y := by
  -- Unfolding exposes exactly the advertised rank-two formula.
  rfl

/-- A positive-definite matrix has a positive quadratic denominator on a nonzero vector. -/
theorem quadraticDenominator_pos {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {s : EuclideanSpace ℝ ι} (hs : s ≠ 0) :
    0 < dotProduct s (Matrix.mulVec B s) := by
  -- Transfer nonzeroness through the Euclidean-space coercion, then apply positive definiteness.
  have hs' : s.ofLp ≠ 0 := by
    intro h
    exact hs ((WithLp.ofLp_injective 2) h)
  simpa using hB.dotProduct_mulVec_pos hs'

/-- The BFGS update satisfies the secant equation under positive curvature. -/
theorem update_secant {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {s y : EuclideanSpace ℝ ι} (hsy : 0 < dotProduct s y) :
    Matrix.mulVec (update B s y) s = (EuclideanSpace.equiv ι ℝ) y := by
  -- Positive curvature makes both rank-two denominators nonzero.
  have hs : s ≠ 0 := by
    intro hs
    subst hs
    simp at hsy
  have hq : 0 < dotProduct s (Matrix.mulVec B s) :=
    quadraticDenominator_pos hB hs
  have hq0 : dotProduct s (Matrix.mulVec B s) ≠ 0 := ne_of_gt hq
  have hry0 : dotProduct s y ≠ 0 := ne_of_gt hsy
  have hprod :
      Matrix.mulVec (B * Matrix.vecMulVec s.ofLp s.ofLp * B) s.ofLp =
        (dotProduct s.ofLp (Matrix.mulVec B s.ofLp)) • (Matrix.mulVec B s.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul]
  have hyprod : Matrix.mulVec (Matrix.vecMulVec y.ofLp y.ofLp) s.ofLp =
      (dotProduct s.ofLp y.ofLp) • y.ofLp := by
    rw [Matrix.vecMulVec_mulVec]
    simpa only [dotProduct_comm, op_smul_eq_smul]
  rw [update, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    hprod, Matrix.smul_mulVec, hyprod]
  simp only [smul_smul]
  rw [inv_mul_cancel₀ hq0, inv_mul_cancel₀ hry0]
  simp
  simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]

/-- The BFGS update preserves positive definiteness under positive curvature. -/
theorem update_posDef {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {s y : EuclideanSpace ℝ ι} (hsy : 0 < dotProduct s y) :
    (update B s y).PosDef := by
  -- Normalize the updated quadratic form as a positive residual term plus a positive square.
  have hsE : s ≠ 0 := by
    intro hs
    subst hs
    simp at hsy
  have hs : s.ofLp ≠ 0 := by
    intro h
    exact hsE ((WithLp.ofLp_injective 2) h)
  have hq : 0 < dotProduct s (Matrix.mulVec B s) := quadraticDenominator_pos hB hsE
  have hq0 : dotProduct s (Matrix.mulVec B s) ≠ 0 := ne_of_gt hq
  have hq0' : dotProduct (Matrix.mulVec B s.ofLp) s.ofLp ≠ 0 := by
    rw [dotProduct_comm]
    exact hq0
  have hry0 : dotProduct s y ≠ 0 := ne_of_gt hsy
  have hBs : (B * Matrix.vecMulVec s s * B).IsHermitian := by
    have hV : (Matrix.vecMulVec s s).IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      ext i j
      simp [Matrix.vecMulVec, mul_comm]
    simpa only [hB.1.eq] using
      (Matrix.isHermitian_mul_mul_conjTranspose (A := Matrix.vecMulVec s s) B hV)
  have hY : (Matrix.vecMulVec y y).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    simp [Matrix.vecMulVec, mul_comm]
  have hscalarSelfAdjoint (a : ℝ) : IsSelfAdjoint a := by
    rw [isSelfAdjoint_iff, star_trivial]
  have hHerm : (update B s y).IsHermitian := by
    rw [update]
    exact hB.1.sub (hBs.smul (hscalarSelfAdjoint _))
      |>.add (hY.smul (hscalarSelfAdjoint _))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro v hv
  have hBt : Matrix.transpose B = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.1.eq
  have hsymm (u w : ι → ℝ) :
      dotProduct u (Matrix.mulVec B w) = dotProduct w (Matrix.mulVec B u) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBt, dotProduct_comm]
  have hcross (w : ι → ℝ) :
      dotProduct s.ofLp (Matrix.mulVec B w) = dotProduct (Matrix.mulVec B s.ofLp) w := by
    rw [hsymm, dotProduct_comm]
  let q : ℝ := dotProduct s.ofLp (Matrix.mulVec B s.ofLp)
  let r : ℝ := dotProduct s.ofLp y.ofLp
  let a : ℝ := dotProduct (Matrix.mulVec B s.ofLp) v / q
  have hprodV :
      Matrix.mulVec (B * Matrix.vecMulVec s.ofLp s.ofLp * B) v =
        (dotProduct s.ofLp (Matrix.mulVec B v)) • (Matrix.mulVec B s.ofLp) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec]
    simpa only [op_smul_eq_smul]
  have hyprodV : Matrix.mulVec (Matrix.vecMulVec y.ofLp y.ofLp) v =
      (dotProduct y.ofLp v) • y.ofLp := by
    rw [Matrix.vecMulVec_mulVec]
    simpa only [op_smul_eq_smul]
  have hquad (z : ι → ℝ) (c : ℝ) :
      dotProduct (z - c • s.ofLp) (Matrix.mulVec B (z - c • s.ofLp)) =
        dotProduct z (Matrix.mulVec B z) - c * dotProduct z (Matrix.mulVec B s.ofLp) -
          c * dotProduct s.ofLp (Matrix.mulVec B z) +
            c ^ 2 * dotProduct s.ofLp (Matrix.mulVec B s.ofLp) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  have hform :
      dotProduct v (Matrix.mulVec (update B s y) v) =
        dotProduct (v - a • s.ofLp) (Matrix.mulVec B (v - a • s.ofLp)) +
          (dotProduct y.ofLp v) ^ 2 / r := by
    dsimp [q, r, a]
    rw [update, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      hprodV, Matrix.smul_mulVec, hyprodV]
    rw [hquad]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_smul, op_smul_eq_smul, smul_eq_mul, Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp_rw [hcross]
    rw [dotProduct_comm v y.ofLp]
    field_simp [hq0, hq0', hry0]
    ring
  have hformpos : 0 < dotProduct v (Matrix.mulVec (update B s y) v) := by
    rw [hform]
    by_cases hres : v - a • s.ofLp = 0
    · by_cases hyv : dotProduct y.ofLp v ≠ 0
      · have hsquare : 0 < (dotProduct y.ofLp v) ^ 2 / dotProduct s.ofLp y.ofLp :=
          div_pos (sq_pos_of_ne_zero hyv) hsy
        rw [hres, Matrix.mulVec_zero, dotProduct_zero, zero_add]
        exact hsquare
      · exfalso
        have hva : v = a • s.ofLp := sub_eq_zero.mp hres
        have hmul : a * dotProduct y.ofLp s.ofLp = 0 := by
          calc
            a * dotProduct y.ofLp s.ofLp = dotProduct y.ofLp (a • s.ofLp) := by
              simp [dotProduct_smul, smul_eq_mul]
            _ = dotProduct y.ofLp v := by rw [← hva]
            _ = 0 := by exact not_ne_iff.mp hyv
        have hys : dotProduct y.ofLp s.ofLp ≠ 0 := by
          simpa only [dotProduct_comm] using hry0
        have ha : a = 0 := (mul_eq_zero.mp hmul).resolve_right hys
        apply hv
        rw [hva, ha, zero_smul]
    · have hres' : v - a • s.ofLp ≠ 0 := hres
      have hstrict : 0 < dotProduct (v - a • s.ofLp)
          (Matrix.mulVec B (v - a • s.ofLp)) := by
        simpa only [star_trivial] using hB.dotProduct_mulVec_pos hres'
      have hnonneg : 0 ≤ (dotProduct y.ofLp v) ^ 2 / dotProduct s.ofLp y.ofLp :=
        div_nonneg (sq_nonneg _) (le_of_lt hsy)
      nlinarith
  simpa only [star_trivial] using hformpos

end Update

section SearchDirection

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The inverse-Hessian solve defining the BFGS search direction. -/
noncomputable def searchDirection (B : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm
    (-(Matrix.mulVec B⁻¹ ((EuclideanSpace.equiv ι ℝ) g)))

/-- The BFGS search direction is the negative inverse-matrix-vector product. -/
theorem searchDirection_def (B : Matrix ι ι ℝ) (g : EuclideanSpace ℝ ι) :
    searchDirection B g =
      (EuclideanSpace.equiv ι ℝ).symm
        (-(Matrix.mulVec B⁻¹ ((EuclideanSpace.equiv ι ℝ) g))) := by
  -- Unfolding once exposes the canonical inverse-Hessian representation.
  rfl

/-- A positive-definite Hessian approximation sends its BFGS direction to `-g`. -/
theorem searchDirection_spec {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (g : EuclideanSpace ℝ ι) :
    Matrix.mulVec B ((EuclideanSpace.equiv ι ℝ) (searchDirection B g)) =
      -(EuclideanSpace.equiv ι ℝ) g := by
  -- The positive-definite matrix is invertible, so its inverse is a genuine two-sided inverse.
  -- Local instance justification (proof-local temporary data): matrix inverse multiplication needs
  -- the canonical `Invertible B` witness supplied by positive definiteness.
  letI := hB.isUnit.invertible
  simp [searchDirection, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
  have hinv : Matrix.mulVec B (Matrix.mulVec B⁻¹ g.ofLp) = g.ofLp := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  simpa only [Matrix.mulVec_neg] using congrArg Neg.neg hinv

end SearchDirection

end BFGS

namespace DFP

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The Hessian-form Davidon--Fletcher--Powell rank-two update. -/
noncomputable def update (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec y s) * B *
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) +
    (dotProduct y s)⁻¹ • Matrix.vecMulVec y y

/-- The explicit product formula for the Hessian-form DFP update. -/
theorem update_def (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    update B s y =
      (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec y s) * B *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) +
        (dotProduct y s)⁻¹ • Matrix.vecMulVec y y := by
  -- Unfolding exposes exactly the advertised projection formula.
  rfl

/-- The DFP update satisfies the secant equation under positive curvature. -/
theorem update_secant (B : Matrix ι ι ℝ) {s y : EuclideanSpace ℝ ι}
    (hsy : 0 < dotProduct s y) :
    Matrix.mulVec (update B s y) s = (EuclideanSpace.equiv ι ℝ) y := by
  -- The right projection kills `s`, while the rank-one correction sends it to `y`.
  have hr : dotProduct s y ≠ 0 := ne_of_gt hsy
  have hright : Matrix.mulVec
      (1 - (dotProduct s.ofLp y.ofLp)⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp) s.ofLp = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec]
    simp [dotProduct_comm, hr]
  have hprod : Matrix.mulVec
      ((1 - (dotProduct y.ofLp s.ofLp)⁻¹ • Matrix.vecMulVec y.ofLp s.ofLp) * B *
        (1 - (dotProduct s.ofLp y.ofLp)⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp)) s.ofLp = 0 := by
    rw [← Matrix.mulVec_mulVec, hright, Matrix.mulVec_zero]
  have hyprod : Matrix.mulVec (Matrix.vecMulVec y.ofLp y.ofLp) s.ofLp =
      (dotProduct s.ofLp y.ofLp) • y.ofLp := by
    rw [Matrix.vecMulVec_mulVec]
    simpa only [dotProduct_comm, op_smul_eq_smul]
  rw [update, Matrix.add_mulVec, hprod, Matrix.smul_mulVec, hyprod]
  simp only [smul_smul]
  rw [dotProduct_comm y.ofLp s.ofLp]
  rw [inv_mul_cancel₀ hr]
  simp only [one_smul, zero_add]
  simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]

/-- The DFP update preserves positive definiteness under positive curvature. -/
theorem update_posDef {B : Matrix ι ι ℝ} (hB : B.PosDef)
    {s y : EuclideanSpace ℝ ι} (hsy : 0 < dotProduct s y) :
    (update B s y).PosDef := by
  -- Write the projection part as `PᴴBP` and the correction as a positive rank-one matrix.
  let P : Matrix ι ι ℝ :=
    1 - (dotProduct s.ofLp y.ofLp)⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp
  have hP : P =
      1 - (dotProduct s.ofLp y.ofLp)⁻¹ • Matrix.vecMulVec s.ofLp y.ofLp := rfl
  have hcurv' : 0 < dotProduct y.ofLp s.ofLp := by
    simpa only [dotProduct_comm] using hsy
  have hproj :
      1 - (dotProduct y.ofLp s.ofLp)⁻¹ • Matrix.vecMulVec y.ofLp s.ofLp =
        Matrix.conjTranspose P := by
    dsimp [P]
    ext i j
    simp [Matrix.one_apply, Matrix.vecMulVec, dotProduct_comm, mul_comm, eq_comm]
  have hprojection : (Matrix.conjTranspose P * B * P).PosSemidef :=
    hB.posSemidef.conjTranspose_mul_mul_same P
  have hrankHermitian :
      ((dotProduct y.ofLp s.ofLp)⁻¹ •
        Matrix.vecMulVec y.ofLp y.ofLp).IsHermitian := by
    have hy : (Matrix.vecMulVec y.ofLp y.ofLp).IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      ext i j
      simp [Matrix.vecMulVec, mul_comm]
    have hc : IsSelfAdjoint (dotProduct y.ofLp s.ofLp)⁻¹ := by
      rw [isSelfAdjoint_iff, star_trivial]
    exact hy.smul hc
  have hrankForm (v : ι → ℝ) : dotProduct v
      (Matrix.mulVec ((dotProduct y.ofLp s.ofLp)⁻¹ •
        Matrix.vecMulVec y.ofLp y.ofLp) v) =
        (dotProduct y.ofLp s.ofLp)⁻¹ * (dotProduct y.ofLp v) ^ 2 := by
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
    simp only [op_smul_eq_smul, smul_smul, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm v y.ofLp]
    ring
  have hprojectionForm (v : ι → ℝ) :
      dotProduct v (Matrix.mulVec (Matrix.conjTranspose P * B * P) v) =
        dotProduct (Matrix.mulVec P v) (Matrix.mulVec B (Matrix.mulVec P v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
    simp only [star_trivial]
  rw [update, ← hP, hproj]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hprojection.isHermitian.add hrankHermitian) ?_
  intro v hv
  rw [Matrix.add_mulVec, dotProduct_add]
  -- If the projected vector survives, the conjugated `B` term is already strictly positive.
  by_cases hPv : Matrix.mulVec P v = 0
  · have hyv : dotProduct y.ofLp v ≠ 0 := by
      intro hyv
      apply hv
      dsimp [P] at hPv
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.vecMulVec_mulVec] at hPv
      simpa only [op_smul_eq_smul, hyv, zero_smul, smul_zero, sub_zero] using hPv
    have hprojectionNonneg :
        0 ≤ dotProduct v (Matrix.mulVec (Matrix.conjTranspose P * B * P) v) := by
      simpa only [star_trivial] using hprojection.dotProduct_mulVec_nonneg v
    have hrankPos : 0 < dotProduct v
        (Matrix.mulVec ((dotProduct y.ofLp s.ofLp)⁻¹ •
          Matrix.vecMulVec y.ofLp y.ofLp) v) := by
      rw [hrankForm]
      exact mul_pos (inv_pos.mpr hcurv') (sq_pos_of_ne_zero hyv)
    exact add_pos_of_nonneg_of_pos hprojectionNonneg hrankPos
  · have hprojectionPos :
        0 < dotProduct v (Matrix.mulVec (Matrix.conjTranspose P * B * P) v) := by
      rw [hprojectionForm]
      simpa only [star_trivial] using hB.dotProduct_mulVec_pos hPv
    have hrankNonneg : 0 ≤ dotProduct v
        (Matrix.mulVec ((dotProduct y.ofLp s.ofLp)⁻¹ •
          Matrix.vecMulVec y.ofLp y.ofLp) v) := by
      rw [hrankForm]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hcurv')) (sq_nonneg _)
    exact add_pos_of_pos_of_nonneg hprojectionPos hrankNonneg

end

end DFP

namespace Broyden

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The convex Broyden interpolation between the BFGS and DFP Hessian updates. -/
noncomputable def update (φ : ℝ) (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  (1 - φ) • BFGS.update B s y + φ • DFP.update B s y

/-- The explicit affine-interpolation formula for the convex Broyden update. -/
theorem update_def (φ : ℝ) (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    update φ B s y = (1 - φ) • BFGS.update B s y + φ • DFP.update B s y := by
  -- Unfolding exposes the affine interpolation.
  rfl

/-- At parameter zero, the Broyden update is the BFGS update. -/
theorem update_zero (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    update 0 B s y = BFGS.update B s y := by
  -- At the left endpoint, scalar simplification removes the DFP summand.
  simp [update]

/-- At parameter one, the Broyden update is the DFP update. -/
theorem update_one (B : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    update 1 B s y = DFP.update B s y := by
  -- At the right endpoint, scalar simplification removes the BFGS summand.
  simp [update]

/-- Every convex Broyden update is positive definite under positive curvature. -/
theorem update_posDef {φ : ℝ} (hφ : φ ∈ Set.Icc (0 : ℝ) 1)
    {B : Matrix ι ι ℝ} (hB : B.PosDef) {s y : EuclideanSpace ℝ ι}
    (hsy : 0 < dotProduct s y) : (update φ B s y).PosDef := by
  -- Handle the endpoints directly; in the interior both weighted endpoint forms are positive.
  rcases hφ with ⟨hφ0, hφ1⟩
  by_cases hzero : φ = 0
  · subst φ
    rw [update_zero]
    exact BFGS.update_posDef hB hsy
  by_cases hone : φ = 1
  · subst φ
    rw [update_one]
    exact DFP.update_posDef hB hsy
  have hφpos : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hzero)
  have honeSubPos : 0 < 1 - φ := sub_pos.mpr (lt_of_le_of_ne hφ1 hone)
  have hBFGS := BFGS.update_posDef hB hsy
  have hDFP := DFP.update_posDef hB hsy
  have hleftSelfAdjoint : IsSelfAdjoint (1 - φ) := by
    rw [isSelfAdjoint_iff, star_trivial]
  have hrightSelfAdjoint : IsSelfAdjoint φ := by
    rw [isSelfAdjoint_iff, star_trivial]
  rw [update_def]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    ((hBFGS.isHermitian.smul hleftSelfAdjoint).add
      (hDFP.isHermitian.smul hrightSelfAdjoint)) ?_
  intro v hv
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul]
  have hBFGSPos : 0 < dotProduct v (Matrix.mulVec (BFGS.update B s y) v) := by
    simpa only [star_trivial] using hBFGS.dotProduct_mulVec_pos hv
  have hDFPPos : 0 < dotProduct v (Matrix.mulVec (DFP.update B s y) v) := by
    simpa only [star_trivial] using hDFP.dotProduct_mulVec_pos hv
  exact add_pos (mul_pos honeSubPos hBFGSPos) (mul_pos hφpos hDFPPos)

end

end Broyden
