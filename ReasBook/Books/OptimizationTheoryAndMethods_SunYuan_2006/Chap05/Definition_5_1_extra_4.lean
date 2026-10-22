/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.SR1Update
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix

noncomputable section

open Filter

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall hits verified for this item via `lean_leansearch`: `Matrix.vecMulVec`,
-- `Matrix.toEuclideanLin`, and `Matrix.IsSymm` support the canonical concrete-matrix surface
-- for the BFGS and PSB updates.

/-- Helper for Chapter05 Definition 5.1-extra-4: the BFGS Hessian update is
`B + (dotProduct y s)⁻¹ • Matrix.vecMulVec y y -
  (dotProduct s (B.mulVec s))⁻¹ • (B * Matrix.vecMulVec s s * B)`.
The source later assumes `dotProduct y s ≠ 0` and `dotProduct s (B.mulVec s) ≠ 0`
when proving the quasi-Newton property of this matrix. -/
def bfgsHessianUpdate (B : MatrixN) (s y : Point) : MatrixN :=
  B + (dotProduct y s)⁻¹ • Matrix.vecMulVec y y -
    (dotProduct s (Matrix.toEuclideanLin B s))⁻¹ • (B * Matrix.vecMulVec s s * B)

/-- Helper for Chapter05 Definition 5.1-extra-4: if `B` is symmetric, then the Hessian-side
rank-one sandwich `B * (u uᵀ) * B` is the outer product of `B u` with itself. -/
lemma symmetricSandwich_eq_rankOneOfMulVec
    {B : MatrixN} (hB : Matrix.IsSymm B) (u : Point) :
    B * Matrix.vecMulVec u u * B =
      Matrix.vecMulVec (Matrix.toEuclideanLin B u) (Matrix.toEuclideanLin B u) := by
  -- Rewrite the right row factor through symmetry and then collapse both rank-one products.
  have hVecMul : Matrix.vecMul u B = Matrix.toEuclideanLin B u := by
    simpa [hB.eq] using Matrix.vecMul_transpose B u
  calc
    B * Matrix.vecMulVec u u * B
        = Matrix.vecMulVec (Matrix.toEuclideanLin B u) u * B := by
            simp [Matrix.mul_vecMulVec, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    _ = Matrix.vecMulVec (Matrix.toEuclideanLin B u) (Matrix.vecMul u B) := by
          rw [Matrix.vecMulVec_mul]
    _ = Matrix.vecMulVec (Matrix.toEuclideanLin B u) (Matrix.toEuclideanLin B u) := by
          rw [hVecMul]

/-- Helper for Chapter05 Definition 5.1-extra-4: evaluating the Hessian-side BFGS sandwich on
`s` collapses to the secant scalar times `B s`. -/
lemma bfgsSandwich_mulVec_secant
    (B : MatrixN) (s : Point) :
    Matrix.toEuclideanLin (B * Matrix.vecMulVec s s * B) s =
      dotProduct s (Matrix.toEuclideanLin B s) • Matrix.toEuclideanLin B s := by
  -- Evaluate both rank-one multiplications before rewriting the remaining scalar with
  -- `dotProduct_mulVec`.
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  simp [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mulVec,
    Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.toLpLin_apply]

/-- The BFGS Hessian update satisfies the Hessian-form quasi-Newton equation `Bₖ₊₁ s = y`. -/
theorem bfgsHessianUpdate_mulVec
    (B : MatrixN) (s y : Point)
    (hys : dotProduct y s ≠ 0) (hBs : dotProduct s (Matrix.toEuclideanLin B s) ≠ 0) :
    Matrix.toEuclideanLin (bfgsHessianUpdate B s y) s = y := by
  have hyTerm :
      Matrix.toEuclideanLin ((dotProduct y s)⁻¹ • Matrix.vecMulVec y y) s = y := by
    -- The secant rank-one term sends `s` exactly to `y`.
    calc
      Matrix.toEuclideanLin ((dotProduct y s)⁻¹ • Matrix.vecMulVec y y) s
          = (dotProduct y s)⁻¹ • Matrix.toEuclideanLin (Matrix.vecMulVec y y) s := by
              simp
      _ = (dotProduct y s)⁻¹ • (dotProduct y s • y) := by
            rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
            simp [Matrix.vecMulVec_mulVec, dotProduct_comm]
      _ = y := by
            simp [hys]
  have hSandwichTerm :
      Matrix.toEuclideanLin
        ((dotProduct s (Matrix.toEuclideanLin B s))⁻¹ • (B * Matrix.vecMulVec s s * B)) s =
      Matrix.toEuclideanLin B s := by
    -- The Hessian-side correction contributes one copy of `B s`.
    calc
      Matrix.toEuclideanLin
          ((dotProduct s (Matrix.toEuclideanLin B s))⁻¹ • (B * Matrix.vecMulVec s s * B)) s
          = (dotProduct s (Matrix.toEuclideanLin B s))⁻¹ •
              Matrix.toEuclideanLin (B * Matrix.vecMulVec s s * B) s := by
                simp
      _ = (dotProduct s (Matrix.toEuclideanLin B s))⁻¹ •
            (dotProduct s (Matrix.toEuclideanLin B s) • Matrix.toEuclideanLin B s) := by
              rw [bfgsSandwich_mulVec_secant]
      _ = Matrix.toEuclideanLin B s := by
            have hcancel :
                (dotProduct s (Matrix.toEuclideanLin B s))⁻¹ *
                    dotProduct s (Matrix.toEuclideanLin B s) = 1 := by
              field_simp [hBs]
            rw [smul_smul, hcancel, one_smul]
  -- Evaluate both correction terms on `s`; the two secant cancellations then telescope.
  calc
    Matrix.toEuclideanLin (bfgsHessianUpdate B s y) s
        = Matrix.toEuclideanLin B s +
            Matrix.toEuclideanLin ((dotProduct y s)⁻¹ • Matrix.vecMulVec y y) s -
            Matrix.toEuclideanLin
              ((dotProduct s (Matrix.toEuclideanLin B s))⁻¹ •
                (B * Matrix.vecMulVec s s * B)) s := by
              simp [bfgsHessianUpdate, sub_eq_add_neg]
    _ = Matrix.toEuclideanLin B s + y - Matrix.toEuclideanLin B s := by
          rw [hyTerm, hSandwichTerm]
    _ = y := by
          abel

/-- Helper for Chapter05 Definition 5.1-extra-4: the inverse-Hessian BFGS update is the compact
form
`(1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) * H *
    (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
  (dotProduct s y)⁻¹ • Matrix.vecMulVec s s`.
The source later assumes `dotProduct s y ≠ 0` when proving the quasi-Newton property
of this matrix. -/
def bfgsInverseUpdate (H : MatrixN) (s y : Point) : MatrixN :=
  (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) * H *
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
    (dotProduct s y)⁻¹ • Matrix.vecMulVec s s

/-- Helper for Chapter05 Definition 5.1-extra-4: expanding the compact BFGS core produces the
usual rank-two-and-rank-one decomposition. -/
lemma bfgsInverseCompactCore_eqExpanded
    (H : MatrixN) (s y : Point) (ρ : ℝ) :
    (1 - ρ • Matrix.vecMulVec s y) * H * (1 - ρ • Matrix.vecMulVec y s) =
      H - ρ • (Matrix.vecMulVec s y * H + H * Matrix.vecMulVec y s) +
        (ρ ^ 2 * dotProduct y (Matrix.toEuclideanLin H y)) • Matrix.vecMulVec s s := by
  -- Expand the compact core entrywise, then collapse the rank-one products with the
  -- canonical `vecMulVec` multiplication lemmas.
  ext i j
  simp [sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.dotProduct_mulVec]
  ring_nf

/-- Helper for Chapter05 Definition 5.1-extra-4: under the search-direction hypotheses, the
rank-one BFGS sandwich is exactly the gradient outer product scaled by `α²`. -/
lemma bfgsSearchDirection_sandwich_eq_gradientRankOne
    {B : MatrixN} {s g d : Point} {α : ℝ}
    (hB : Matrix.IsSymm B) (hsd : s = α • d)
    (hBd : Matrix.toEuclideanLin B d = -g) :
    B * Matrix.vecMulVec s s * B = (α ^ 2) • Matrix.vecMulVec g g := by
  -- Route correction: prove the sandwich identity once so later proofs only cancel scalars.
  have hBs : Matrix.toEuclideanLin B s = (-α) • g := by
    rw [hsd]
    simpa [smul_neg] using congrArg (fun v : Point ↦ α • v) hBd
  calc
    B * Matrix.vecMulVec s s * B
        = Matrix.vecMulVec (Matrix.toEuclideanLin B s) (Matrix.toEuclideanLin B s) := by
            rw [symmetricSandwich_eq_rankOneOfMulVec hB s]
    _ = Matrix.vecMulVec ((-α) • g) ((-α) • g) := by rw [hBs]
    _ = ((-α) * (-α)) • Matrix.vecMulVec g g := by
          ext i j
          simp [Matrix.vecMulVec_apply]
          ring
    _ = (α ^ 2) • Matrix.vecMulVec g g := by
          congr 1
          ring

/-- The BFGS Hessian update can also be written in the search-direction form (5.1.46),
under the symmetric quasi-Newton setting, the previous-step relation `s = α • d`,
the nonzero step-size hypothesis `α ≠ 0`, and the gradient relation
`B.mulVec d = -g`. -/
theorem bfgsHessianUpdate_eq_searchDirectionForm
    (B : MatrixN) (s y g d : Point) (α : ℝ)
    (hB : Matrix.IsSymm B) (hsd : s = α • d) (hα : α ≠ 0)
    (hBd : Matrix.toEuclideanLin B d = -g) :
    bfgsHessianUpdate B s y =
      B + (dotProduct g d)⁻¹ • Matrix.vecMulVec g g +
        (α * dotProduct y d)⁻¹ • Matrix.vecMulVec y y := by
  have hBs : Matrix.toEuclideanLin B s = (-α) • g := by
    -- Rewrite `B s` through the previous search direction `d`.
    rw [hsd]
    simpa [smul_neg] using congrArg (fun v : Point ↦ α • v) hBd
  have hys : dotProduct y s = α * dotProduct y d := by
    -- Replace `s` with `α d` in the secant denominator.
    rw [hsd]
    simp [dotProduct_smul]
  have hBsDen : dotProduct s (Matrix.toEuclideanLin B s) = -(α ^ 2 * dotProduct g d) := by
    -- The Hessian-side denominator becomes `-α² (gᵀ d)`.
    rw [hsd]
    simp [hBd, dotProduct_smul, dotProduct_comm]
    ring
  -- Route correction: rewrite both denominators into the search-direction scalars before
  -- canceling the gradient rank-one term.
  rw [bfgsHessianUpdate, hys, hBsDen,
    bfgsSearchDirection_sandwich_eq_gradientRankOne hB hsd hBd]
  by_cases hgd : dotProduct g d = 0
  · -- If `gᵀ d = 0`, the gradient rank-one term vanishes by totalized inversion.
    simp [hgd]
  · -- Otherwise cancel the nonzero scalars entrywise.
    ext i j
    simp [Matrix.vecMulVec_apply]
    field_simp [hgd, hα]
    ring

/-- Helper for Chapter05 Definition 5.1-extra-4: the right BFGS projector sends `y` to a scalar
multiple of `y`. -/
lemma bfgsRightProjector_mulVec_self
    (s y : Point) (ρ : ℝ) :
    Matrix.toEuclideanLin (1 - ρ • Matrix.vecMulVec y s) y =
      (1 - ρ * dotProduct s y) • y := by
  -- Evaluate the rank-one correction on `y` and collect the remaining scalar factor.
  calc
    Matrix.toEuclideanLin (1 - ρ • Matrix.vecMulVec y s) y
        = y - Matrix.toEuclideanLin (ρ • Matrix.vecMulVec y s) y := by
            simp [sub_eq_add_neg]
    _ = y - ρ • Matrix.toEuclideanLin (Matrix.vecMulVec y s) y := by
          simp
    _ = y - ρ • (dotProduct s y • y) := by
          rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
          simp [Matrix.vecMulVec_mulVec]
    _ = (1 - ρ * dotProduct s y) • y := by
          ext i
          simp
          ring

/-- The inverse-Hessian BFGS update satisfies the inverse-form quasi-Newton equation
`Hₖ₊₁ y = s`. -/
theorem bfgsInverseUpdate_mulVec
    (H : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0) :
    Matrix.toEuclideanLin (bfgsInverseUpdate H s y) y = s := by
  have hproj :
      Matrix.toEuclideanLin (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) y = 0 := by
    -- The right projector annihilates the secant vector `y`.
    rw [bfgsRightProjector_mulVec_self]
    simp [hsy]
  have hproj0 :
      Matrix.mulVec (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) y.ofLp = 0 := by
    -- Evaluate the projector directly on coordinates and cancel the secant scalar.
    ext i
    simp [sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
    field_simp [hsy]
    ring
  have hcore0 :
      Matrix.mulVec
        (((1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) * H) *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s))
        y.ofLp = 0 := by
    -- The compact core vanishes because the right projector already sends `y` to `0`.
    rw [← Matrix.mulVec_mulVec, hproj0]
    simp
  have hRankOne :
      Matrix.mulVec ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s) y.ofLp = s.ofLp := by
    -- The remaining rank-one term evaluates to `s`.
    calc
      Matrix.mulVec ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s) y.ofLp
          = (dotProduct s y)⁻¹ • Matrix.mulVec (Matrix.vecMulVec s s) y.ofLp := by
              rw [Matrix.smul_mulVec]
      _ = (dotProduct s y)⁻¹ • (dotProduct s y • s.ofLp) := by
            simp [Matrix.vecMulVec_mulVec]
      _ = s.ofLp := by
            simp [hsy]
  -- Evaluate the compact BFGS form on `y`; only the final rank-one term survives.
  calc
    Matrix.toEuclideanLin (bfgsInverseUpdate H s y) y
        = WithLp.toLp 2
            (Matrix.mulVec
              (((1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) * H) *
                (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s))
              y.ofLp +
              Matrix.mulVec ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s) y.ofLp) := by
              rw [bfgsInverseUpdate, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.add_mulVec]
    _ = WithLp.toLp 2 (0 + s.ofLp) := by
          rw [hcore0, hRankOne]
    _ = s := by
          simp

/-- The inverse-Hessian BFGS update also has the expanded H-form (5.1.47). -/
theorem bfgsInverseUpdate_eq_expandedForm
    (H : MatrixN) (s y : Point) :
    bfgsInverseUpdate H s y =
      H +
        ((1 + dotProduct y (Matrix.toEuclideanLin H y) / dotProduct s y) * (dotProduct s y)⁻¹) •
          Matrix.vecMulVec s s -
        (dotProduct s y)⁻¹ •
          (Matrix.vecMulVec s y * H + H * Matrix.vecMulVec y s) := by
  -- Expand the compact core once and fold the remaining `s sᵀ` coefficient.
  rw [bfgsInverseUpdate, bfgsInverseCompactCore_eqExpanded]
  ext i j
  simp [Matrix.vecMulVec_apply, div_eq_mul_inv]
  ring

/-- In the symmetric quasi-Newton setting, the inverse-Hessian BFGS update also has the
residual form (5.1.48). -/
theorem bfgsInverseUpdate_eq_residualForm
    (H : MatrixN) (s y : Point) (hH : Matrix.IsSymm H) :
    bfgsInverseUpdate H s y =
      let r := s - Matrix.toEuclideanLin H y
      H + (dotProduct s y)⁻¹ • (Matrix.vecMulVec r s + Matrix.vecMulVec s r) -
        (dotProduct r y * (dotProduct s y)⁻¹ * (dotProduct s y)⁻¹) •
          Matrix.vecMulVec s s := by
  have hVecMul : Matrix.vecMul y H = Matrix.toEuclideanLin H y := by
    -- Symmetry turns the row-vector factor `yᵀ H` into the column-vector image `H y`.
    simpa [hH.eq] using Matrix.vecMul_transpose H y
  by_cases hsy : dotProduct s y = 0
  · -- When the secant denominator vanishes, both totalized formulas reduce to the same matrix.
    rw [bfgsInverseUpdate_eq_expandedForm]
    simp [hVecMul, hsy, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, sub_eq_add_neg,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  · -- Otherwise expand the residual `r = s - H y` and compare the coefficients entrywise.
    rw [bfgsInverseUpdate_eq_expandedForm]
    ext i j
    simp [hVecMul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_apply,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, sub_eq_add_neg, div_eq_mul_inv]
    rw [dotProduct_comm]
    field_simp [hsy]
    ring_nf

/-- Helper for Chapter05 Definition 5.1-extra-4: the DFP dual Hessian-form update obtained from
the
inverse-Hessian BFGS formula by exchanging `H ↔ B` and `s ↔ y` is
`(1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec y s) * B *
    (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec s y) +
  (dotProduct y s)⁻¹ • Matrix.vecMulVec y y`.
The source later assumes `dotProduct y s ≠ 0` when proving the quasi-Newton property
of this matrix. -/
def dfpDualHessianUpdate (B : MatrixN) (s y : Point) : MatrixN :=
  (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec y s) * B *
      (1 - (dotProduct y s)⁻¹ • Matrix.vecMulVec s y) +
    (dotProduct y s)⁻¹ • Matrix.vecMulVec y y

/-- The DFP dual Hessian-form update is the exchanged `B`-form of `bfgsInverseUpdate`. -/
theorem dfpDualHessianUpdate_eq_bfgsInverseUpdate
    (B : MatrixN) (s y : Point) :
    dfpDualHessianUpdate B s y = bfgsInverseUpdate B y s := rfl

/-- The DFP dual Hessian-form update satisfies the Hessian-form quasi-Newton equation
`Bₖ₊₁ s = y`. -/
theorem dfpDualHessianUpdate_mulVec
    (B : MatrixN) (s y : Point) (hys : dotProduct y s ≠ 0) :
    Matrix.toEuclideanLin (dfpDualHessianUpdate B s y) s = y := by
  -- This is the inverse-BFGS secant theorem after swapping `s` and `y`.
  simpa [dfpDualHessianUpdate_eq_bfgsInverseUpdate, dotProduct_comm] using
    bfgsInverseUpdate_mulVec B y s (by simpa [dotProduct_comm] using hys)

/-- The DFP dual Hessian-form update also has the expanded B-form (5.1.50). -/
theorem dfpDualHessianUpdate_eq_expandedForm
    (B : MatrixN) (s y : Point) :
    dfpDualHessianUpdate B s y =
      B +
        ((1 + dotProduct s (Matrix.toEuclideanLin B s) / dotProduct y s) * (dotProduct y s)⁻¹) •
          Matrix.vecMulVec y y -
        (dotProduct y s)⁻¹ •
          (Matrix.vecMulVec y s * B + B * Matrix.vecMulVec s y) := by
  -- This is the expanded inverse-BFGS form with the secant data exchanged.
  simpa [dfpDualHessianUpdate_eq_bfgsInverseUpdate, dotProduct_comm] using
    bfgsInverseUpdate_eq_expandedForm B y s

/-- In the symmetric quasi-Newton setting, the DFP dual Hessian-form update also has the
residual B-form (5.1.51). -/
theorem dfpDualHessianUpdate_eq_residualForm
    (B : MatrixN) (s y : Point) (hB : Matrix.IsSymm B) :
    dfpDualHessianUpdate B s y =
      let r := y - Matrix.toEuclideanLin B s
      B + (dotProduct y s)⁻¹ • (Matrix.vecMulVec r y + Matrix.vecMulVec y r) -
        (dotProduct r s * (dotProduct y s)⁻¹ * (dotProduct y s)⁻¹) •
          Matrix.vecMulVec y y := by
  -- The residual form is the same swap of the inverse-BFGS residual formula.
  simpa [dfpDualHessianUpdate_eq_bfgsInverseUpdate, dotProduct_comm] using
    bfgsInverseUpdate_eq_residualForm B y s hB

/-- The `B`-form produced by exchanging `H ↔ B` and `s ↔ y` in the SR1 inverse update. -/
def sr1DualBFormUpdate (B : MatrixN) (s y : Point) : MatrixN :=
  B + (dotProduct (sr1Residual B s y) s)⁻¹ •
    Matrix.vecMulVec (sr1Residual B s y) (sr1Residual B s y)

/-- The H-form dual object obtained by applying the Sherman-Morrison conversion step to the
exchanged SR1 `B`-form `sr1DualBFormUpdate H y s hry`. -/
def sr1DualHFormUpdate (H : MatrixN) (s y : Point) : MatrixN :=
  let r := s - Matrix.toEuclideanLin H y
  H + (dotProduct r y)⁻¹ • Matrix.vecMulVec r r

/-- Helper for Chapter05 Definition 5.1-extra-4: the SR1 update is self-dual; after exchanging
`H ↔ B` and `s ↔ y`, the dual `B`-form written back in `H`-form recovers `sr1Update`. -/
theorem sr1Update_selfDual
    (H : MatrixN) (s y : Point) :
    sr1DualHFormUpdate H s y = sr1Update H s y := by
  -- Both formulas are definitionally the same after unfolding the SR1 residual.
  rw [sr1DualHFormUpdate, sr1Update, sr1Residual]

/-- The Broyden rank-one update
`B + (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin B s) s`. -/
def broydenRankOneUpdate (B : MatrixN) (s y : Point) : MatrixN :=
  B + (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin B s) s

/-- The defining formula for `broydenRankOneUpdate`. -/
@[simp] theorem broydenRankOneUpdate_eq (B : MatrixN) (s y : Point) :
    broydenRankOneUpdate B s y =
      B + (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - Matrix.toEuclideanLin B s) s := rfl

/-- If `s ≠ 0`, then `broydenRankOneUpdate B s y` satisfies the secant equation
`Matrix.toEuclideanLin (broydenRankOneUpdate B s y) s = y`. -/
theorem broydenRankOneUpdate_mulVec
    (B : MatrixN) (s y : Point) (hs : s ≠ 0) :
    Matrix.toEuclideanLin (broydenRankOneUpdate B s y) s = y := by
  -- Expand the rank-one correction on `s`; the Gram denominator cancels because `s ≠ 0`.
  have hss : dotProduct s s ≠ 0 := by
    intro hzero
    exact hs <| by
      simpa using congrArg (WithLp.toLp 2) ((dotProduct_self_eq_zero).1 hzero)
  ext i
  simp [broydenRankOneUpdate_eq, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.vecMulVec_mulVec, sub_eq_add_neg]
  field_simp [hss]
  ring

/-- The sequence `{C_k}` from `(5.1.55)` generated by alternating the rank-one Broyden step
with symmetrization, starting from `C₀ = B`. -/
def symmetrizedBroydenSequence (B : MatrixN) (s y c : Point) : ℕ → MatrixN
  | 0 => B
  | k + 1 =>
      let Ck := symmetrizedBroydenSequence B s y c k
      if Even k then
        let r := y - Matrix.toEuclideanLin Ck s
        Ck + (dotProduct c s)⁻¹ • Matrix.vecMulVec r c
      else
        ((2 : ℝ)⁻¹) • (Ck + Ck.transpose)

/-- Helper for Chapter05 Definition 5.1-extra-4: the `c`-parametrized limit `B̄` of the
symmetrized Broyden process is the matrix
`B + (dotProduct c s)⁻¹ •
    (Matrix.vecMulVec (y - B.mulVec s) c + Matrix.vecMulVec c (y - B.mulVec s)) -
  (dotProduct (y - B.mulVec s) s * (dotProduct c s)⁻²) • Matrix.vecMulVec c c`.
The source later assumes `dotProduct c s ≠ 0` when proving the quasi-Newton property
and convergence statement for this matrix. -/
def symmetrizedBroydenLimit (B : MatrixN) (s y c : Point) : MatrixN :=
  let r := y - Matrix.toEuclideanLin B s
  B + (dotProduct c s)⁻¹ • (Matrix.vecMulVec r c + Matrix.vecMulVec c r) -
    (dotProduct r s * (dotProduct c s)⁻¹ * (dotProduct c s)⁻¹) • Matrix.vecMulVec c c

/-- Helper for Chapter05 Definition 5.1-extra-4: the first residual that remains after
symmetrizing the initial Broyden rank-one correction. -/
abbrev symmetrizedBroydenSeedResidual (B : MatrixN) (s y c : Point) : Point :=
  ((2 : ℝ)⁻¹) •
    ((y - Matrix.toEuclideanLin B s) -
      (dotProduct (y - Matrix.toEuclideanLin B s) s * (dotProduct c s)⁻¹) • c)

/-- Helper for Chapter05 Definition 5.1-extra-4: the explicit PSB limit already satisfies the
secant equation `B̄ s = y`. -/
lemma symmetrizedBroydenLimit_mulVecSecant
    (B : MatrixN) (s y c : Point) (hcs : dotProduct c s ≠ 0) :
    Matrix.toEuclideanLin (symmetrizedBroydenLimit B s y c) s = y := by
  -- Compare coordinates after evaluating the explicit correction on `s`.
  ext i
  simp [symmetrizedBroydenLimit, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.vecMulVec_mulVec, sub_eq_add_neg]
  field_simp [hcs]
  ring

/-- Helper for Chapter05 Definition 5.1-extra-4: if `B` is symmetric, then the explicit PSB
limit is symmetric as well. -/
lemma symmetrizedBroydenLimit_isSymmOfIsSymm
    {B : MatrixN} (hB : Matrix.IsSymm B) (s y c : Point) :
    Matrix.IsSymm (symmetrizedBroydenLimit B s y c) := by
  -- Transpose the explicit limit formula term-by-term and use symmetry of the initial matrix.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  have hBij : B j i = B i j := by
    simpa [Matrix.transpose_apply] using congrArg (fun M : MatrixN ↦ M i j) hB.eq
  simp [symmetrizedBroydenLimit, Matrix.vecMulVec_apply, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, mul_comm, hBij]

/-- Helper for Chapter05 Definition 5.1-extra-4: the residual after the first symmetrization step
is orthogonal to the secant vector `s`. -/
lemma symmetrizedBroydenSeedResidual_dotProduct
    (B : MatrixN) (s y c : Point) (hcs : dotProduct c s ≠ 0) :
    dotProduct (symmetrizedBroydenSeedResidual B s y c) s = 0 := by
  -- Expand the seed residual and cancel the only denominator with `dotProduct c s ≠ 0`.
  have hsc : dotProduct s c ≠ 0 := by
    simpa [dotProduct_comm] using hcs
  simp [symmetrizedBroydenSeedResidual, dotProduct_sub, dotProduct_smul, dotProduct_comm]
  field_simp [hcs, hsc]
  ring_nf

/-- Helper for Chapter05 Definition 5.1-extra-4: the first symmetric iterate of the alternating
process is the PSB limit minus the seed symmetric error. -/
lemma symmetrizedBroydenSequence_two_eq_limit_sub_seedError
    (B : MatrixN) (s y c : Point) (hB : Matrix.IsSymm B) (hcs : dotProduct c s ≠ 0) :
    symmetrizedBroydenSequence B s y c 2 =
      symmetrizedBroydenLimit B s y c -
        (dotProduct c s)⁻¹ •
          (Matrix.vecMulVec (symmetrizedBroydenSeedResidual B s y c) c +
            Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c)) := by
  -- Expand the first two recursion steps and compare them entrywise with the explicit PSB limit.
  ext i j
  simp [symmetrizedBroydenSequence, symmetrizedBroydenLimit, symmetrizedBroydenSeedResidual,
    hB.eq, Matrix.vecMulVec_apply, Matrix.toEuclideanLin, Matrix.toLpLin_apply, sub_eq_add_neg]
  field_simp [hcs]
  ring

/-- Helper for Chapter05 Definition 5.1-extra-4: after the first symmetrization, evaluating the
remaining secant defect recovers exactly the seed residual. -/
lemma symmetrizedBroydenSequence_two_residual_eq_seedResidual
    (B : MatrixN) (s y c : Point) (hB : Matrix.IsSymm B) (hcs : dotProduct c s ≠ 0) :
    y - Matrix.toEuclideanLin (symmetrizedBroydenSequence B s y c 2) s =
      symmetrizedBroydenSeedResidual B s y c := by
  -- Rewrite `C₂` through the explicit limit formula and evaluate the remaining rank-one error on
  -- `s`.
  have hseed :
      dotProduct (symmetrizedBroydenSeedResidual B s y c) s = 0 :=
    symmetrizedBroydenSeedResidual_dotProduct B s y c hcs
  ext i
  have hsec :
      (symmetrizedBroydenLimit B s y c).mulVec s.ofLp i = y.ofLp i := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      congrArg (fun v : Point ↦ v i) (symmetrizedBroydenLimit_mulVecSecant B s y c hcs)
  rw [symmetrizedBroydenSequence_two_eq_limit_sub_seedError B s y c hB hcs]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecMulVec_mulVec, sub_eq_add_neg]
  rw [hsec]
  field_simp [hcs]
  ring

/-- Helper for Chapter05 Definition 5.1-extra-4: the third iterate keeps only the one-sided seed
error after the second Broyden correction. -/
lemma symmetrizedBroydenSequence_three_eq_limit_subOneSidedSeedError
    (B : MatrixN) (s y c : Point) (hB : Matrix.IsSymm B) (hcs : dotProduct c s ≠ 0) :
    symmetrizedBroydenSequence B s y c 3 =
      symmetrizedBroydenLimit B s y c -
        (dotProduct c s)⁻¹ • Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c) := by
  -- Unfold one more Broyden step from `C₂`; the `vecMulVec residual c` term cancels the matching
  -- part of the symmetric seed error.
  calc
    symmetrizedBroydenSequence B s y c 3
        = symmetrizedBroydenSequence B s y c 2 +
            (dotProduct c s)⁻¹ •
              Matrix.vecMulVec
                (y - Matrix.toEuclideanLin (symmetrizedBroydenSequence B s y c 2) s) c := by
                  simp [symmetrizedBroydenSequence]
    _ = symmetrizedBroydenSequence B s y c 2 +
          (dotProduct c s)⁻¹ • Matrix.vecMulVec (symmetrizedBroydenSeedResidual B s y c) c := by
            rw [symmetrizedBroydenSequence_two_residual_eq_seedResidual B s y c hB hcs]
    _ = symmetrizedBroydenLimit B s y c -
          (dotProduct c s)⁻¹ • Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c) := by
            rw [symmetrizedBroydenSequence_two_eq_limit_sub_seedError B s y c hB hcs]
            ext i j
            simp [Matrix.vecMulVec_apply, sub_eq_add_neg]
            ring

/-- Helper for Chapter05 Definition 5.1-extra-4: once the initial symmetrization is done, the
even and odd iterates are explicit geometric perturbations of the PSB limit. -/
lemma symmetrizedBroyden_evenOdd_closedForm
    (B : MatrixN) (s y c : Point) (hB : Matrix.IsSymm B) (hcs : dotProduct c s ≠ 0) :
    ∀ k,
      symmetrizedBroydenSequence B s y c (2 * k + 2) =
        symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) •
          ((dotProduct c s)⁻¹ •
            (Matrix.vecMulVec (symmetrizedBroydenSeedResidual B s y c) c +
              Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c))) ∧
      symmetrizedBroydenSequence B s y c (2 * k + 3) =
        symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) •
          ((dotProduct c s)⁻¹ • Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c)) := by
  let evenError : MatrixN :=
    (dotProduct c s)⁻¹ •
      (Matrix.vecMulVec (symmetrizedBroydenSeedResidual B s y c) c +
        Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c))
  let oddError : MatrixN :=
    (dotProduct c s)⁻¹ • Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c)
  have hLimitSymm : Matrix.IsSymm (symmetrizedBroydenLimit B s y c) :=
    symmetrizedBroydenLimit_isSymmOfIsSymm hB s y c
  have hseed :
      dotProduct (symmetrizedBroydenSeedResidual B s y c) s = 0 :=
    symmetrizedBroydenSeedResidual_dotProduct B s y c hcs
  intro k
  induction k with
  | zero =>
      constructor
      · -- The base even iterate is exactly the previously normalized `C₂` formula.
        simpa [evenError] using symmetrizedBroydenSequence_two_eq_limit_sub_seedError B s y c hB hcs
      · -- The base odd iterate is exactly the one-sided `C₃` bridge.
        simpa [oddError] using
          symmetrizedBroydenSequence_three_eq_limit_subOneSidedSeedError B s y c hB hcs
  | succ k ih =>
      rcases ih with ⟨hkEven, hkOdd⟩
      have hSuccEven :
          symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2) =
            symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ (k + 1)) • evenError := by
        -- Route correction: obtain the next even iterate by symmetrizing the closed form for the
        -- preceding odd iterate instead of reopening the recursion from `0`.
        calc
          symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2)
              = symmetrizedBroydenSequence B s y c ((2 * k + 3) + 1) := by
                  rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by omega]
          _
              = ((2 : ℝ)⁻¹) •
                  (symmetrizedBroydenSequence B s y c (2 * k + 3) +
                    (symmetrizedBroydenSequence B s y c (2 * k + 3)).transpose) := by
                      have hodd : ¬ Even (2 * k + 3) := by
                        intro hEven
                        rcases hEven with ⟨m, hm⟩
                        omega
                      rw [symmetrizedBroydenSequence]
                      simp [hodd]
          _ = ((2 : ℝ)⁻¹) •
                ((symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • oddError) +
                  (symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • oddError).transpose) := by
                    rw [hkOdd]
          _ = symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ (k + 1)) • evenError := by
                ext i j
                simp [evenError, oddError, hLimitSymm.eq, Matrix.vecMulVec_apply,
                  sub_eq_add_neg, pow_succ]
                ring
      have hSuccResidual :
          y - Matrix.toEuclideanLin (symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2)) s =
            ((1 / 2 : ℝ) ^ (k + 1)) • symmetrizedBroydenSeedResidual B s y c := by
        -- Evaluate the symmetric error term on `s`; only the `vecMulVec seedResidual c`
        -- contribution survives.
        ext i
        have hsec :
            (symmetrizedBroydenLimit B s y c).mulVec s.ofLp i = y.ofLp i := by
          simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
            congrArg (fun v : Point ↦ v i) (symmetrizedBroydenLimit_mulVecSecant B s y c hcs)
        rw [hSuccEven]
        simp [evenError, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecMulVec_mulVec,
          sub_eq_add_neg]
        rw [hsec]
        field_simp [hcs]
        ring
      have hSuccOdd :
          symmetrizedBroydenSequence B s y c (2 * (k + 1) + 3) =
            symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ (k + 1)) • oddError := by
        -- The next odd iterate is one more Broyden correction applied to the newly computed even
        -- iterate, using the geometric residual from the previous step.
        calc
          symmetrizedBroydenSequence B s y c (2 * (k + 1) + 3)
              = symmetrizedBroydenSequence B s y c ((2 * (k + 1) + 2) + 1) := by
                  rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by omega]
          _
              = symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2) +
                  (dotProduct c s)⁻¹ •
                    Matrix.vecMulVec
                      (y - Matrix.toEuclideanLin
                        (symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2)) s)
                      c := by
                          have heven : Even (2 * (k + 1) + 2) := by
                            refine ⟨k + 2, by omega⟩
                          rw [symmetrizedBroydenSequence]
                          simp [heven]
          _ = symmetrizedBroydenSequence B s y c (2 * (k + 1) + 2) +
                (dotProduct c s)⁻¹ •
                  Matrix.vecMulVec (((1 / 2 : ℝ) ^ (k + 1)) •
                    symmetrizedBroydenSeedResidual B s y c) c := by
                      rw [hSuccResidual]
          _ = symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ (k + 1)) • oddError := by
                rw [hSuccEven]
                ext i j
                simp [evenError, oddError, Matrix.vecMulVec_apply, sub_eq_add_neg]
                ring
      exact ⟨hSuccEven, hSuccOdd⟩

/-- Chapter05 Definition 5.1-extra-4: if `B` is symmetric, then the sequence `(5.1.55)`
converges to the explicit matrix
`symmetrizedBroydenLimit` from `(5.1.56)`. This matches the source paragraph, which begins
with `Let B ∈ R^{n×n} be a symmetric matrix`. -/
theorem symmetrizedBroydenSequence_tendsto_limit
    (B : MatrixN) (s y c : Point) (hB : Matrix.IsSymm B) (hcs : dotProduct c s ≠ 0) :
    Tendsto (symmetrizedBroydenSequence B s y c) atTop
      (nhds (symmetrizedBroydenLimit B s y c)) := by
  let evenError : MatrixN :=
    (dotProduct c s)⁻¹ •
      (Matrix.vecMulVec (symmetrizedBroydenSeedResidual B s y c) c +
        Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c))
  let oddError : MatrixN :=
    (dotProduct c s)⁻¹ • Matrix.vecMulVec c (symmetrizedBroydenSeedResidual B s y c)
  have hpow :
      Tendsto (fun k : ℕ ↦ ((1 / 2 : ℝ) ^ k)) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hEvenTail :
      Tendsto
        (fun k ↦ symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • evenError)
        atTop (nhds (symmetrizedBroydenLimit B s y c)) := by
    simpa [sub_zero] using Tendsto.const_sub (symmetrizedBroydenLimit B s y c)
      (hpow.smul_const evenError)
  have hOddTail :
      Tendsto
        (fun k ↦ symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • oddError)
        atTop (nhds (symmetrizedBroydenLimit B s y c)) := by
    simpa [sub_zero] using Tendsto.const_sub (symmetrizedBroydenLimit B s y c)
      (hpow.smul_const oddError)
  change Tendsto (fun n ↦ fun i => symmetrizedBroydenSequence B s y c n i) atTop
    (nhds fun i => symmetrizedBroydenLimit B s y c i)
  rw [tendsto_pi_nhds]
  intro i
  change Tendsto (fun n ↦ fun j => symmetrizedBroydenSequence B s y c n i j) atTop
    (nhds fun j => symmetrizedBroydenLimit B s y c i j)
  rw [tendsto_pi_nhds]
  intro j
  have hEvenCoord :
      Tendsto
        (fun k ↦ (symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • evenError) i j)
        atTop (nhds ((symmetrizedBroydenLimit B s y c) i j)) := by
    simpa using tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hEvenTail i) j
  have hOddCoord :
      Tendsto
        (fun k ↦ (symmetrizedBroydenLimit B s y c - ((1 / 2 : ℝ) ^ k) • oddError) i j)
        atTop (nhds ((symmetrizedBroydenLimit B s y c) i j)) := by
    simpa using tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hOddTail i) j
  refine (Metric.tendsto_atTop
    (u := fun n ↦ symmetrizedBroydenSequence B s y c n i j)
    (a := (symmetrizedBroydenLimit B s y c) i j)).2 ?_
  intro ε hε
  rcases (Metric.tendsto_atTop.mp hEvenCoord) ε hε with ⟨Ne, hNe⟩
  rcases (Metric.tendsto_atTop.mp hOddCoord) ε hε with ⟨No, hNo⟩
  refine ⟨max (2 * Ne + 2) (2 * No + 3), ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with hne | hno
  · rcases hne with ⟨m, hm⟩
    have hm_pos : 1 ≤ m := by
      omega
    rcases m with _ | k
    · omega
    · have hk : Ne ≤ k := by
        omega
      have hclosed := (symmetrizedBroyden_evenOdd_closedForm B s y c hB hcs k).1
      have hn_eq : n = 2 * k + 2 := by
        omega
      rw [hn_eq, hclosed]
      exact hNe k hk
  · rcases hno with ⟨m, hm⟩
    have hm_pos : 1 ≤ m := by
      omega
    rcases m with _ | k
    · omega
    · have hk : No ≤ k := by
        omega
      have hclosed := (symmetrizedBroyden_evenOdd_closedForm B s y c hB hcs k).2
      have hn_eq : n = 2 * k + 3 := by
        omega
      rw [hn_eq, hclosed]
      exact hNo k hk

/-- The generic symmetrized Broyden limit satisfies the Hessian-form quasi-Newton equation
`Bₖ₊₁ s = y`. -/
theorem symmetrizedBroydenLimit_mulVec
    (B : MatrixN) (s y c : Point) (hcs : dotProduct c s ≠ 0) :
    Matrix.toEuclideanLin (symmetrizedBroydenLimit B s y c) s = y := by
  -- Reuse the PSB secant helper established for the convergence theorem.
  simpa using symmetrizedBroydenLimit_mulVecSecant B s y c hcs

/-- If `B` is symmetric, then the generic symmetrized Broyden limit is symmetric as well. -/
theorem symmetrizedBroydenLimit_isSymm
    {B : MatrixN} (hB : Matrix.IsSymm B) (s y c : Point) :
    Matrix.IsSymm (symmetrizedBroydenLimit B s y c) := by
  -- Reuse the symmetry helper needed to normalize the alternating recursion.
  simpa using symmetrizedBroydenLimit_isSymmOfIsSymm hB s y c

/-- The Powell-symmetric-Broyden update is the `c = s`
specialization of `symmetrizedBroydenLimit`. The source setup later assumes that the current
Hessian approximation `B` is symmetric when establishing the symmetry property of this update.
Explicitly,
`B + (dotProduct s s)⁻¹ •
    (Matrix.vecMulVec (y - B.mulVec s) s + Matrix.vecMulVec s (y - B.mulVec s)) -
  (dotProduct (y - B.mulVec s) s * (dotProduct s s)⁻²) • Matrix.vecMulVec s s`.
The source later assumes `dotProduct s s ≠ 0` when proving the quasi-Newton property
of this specialization. -/
abbrev powellSymmetricBroydenUpdate (B : MatrixN) (s y : Point) : MatrixN :=
  symmetrizedBroydenLimit B s y s

/-- The Powell-symmetric-Broyden update is the `c = s` specialization of
`symmetrizedBroydenLimit`. -/
theorem powellSymmetricBroydenUpdate_eq_symmetrizedBroydenLimit
    (B : MatrixN) (s y : Point) :
    powellSymmetricBroydenUpdate B s y = symmetrizedBroydenLimit B s y s := rfl

/-- The Powell-symmetric-Broyden update satisfies the Hessian-form quasi-Newton equation
`Bₖ₊₁ s = y`. -/
theorem powellSymmetricBroydenUpdate_mulVec
    (B : MatrixN) (s y : Point)
    (hss : dotProduct s s ≠ 0) :
    Matrix.toEuclideanLin (powellSymmetricBroydenUpdate B s y) s = y := by
  simpa [powellSymmetricBroydenUpdate] using symmetrizedBroydenLimit_mulVec B s y s hss

/-- If `B` is symmetric, then the Powell-symmetric-Broyden update is symmetric. -/
theorem powellSymmetricBroydenUpdate_isSymm
    {B : MatrixN} (hB : Matrix.IsSymm B) (s y : Point) :
    Matrix.IsSymm (powellSymmetricBroydenUpdate B s y) := by
  simpa [powellSymmetricBroydenUpdate] using symmetrizedBroydenLimit_isSymm hB s y s
