/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_7_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * project owner `lbfgsTwoLoopRecursion` from `Algorithm_5_7_1.lean`
-- * project owner `lbfgsTwoLoopRecursion_singleton` from `Algorithm_5_7_1.lean`
-- * project owner `bfgsInverseUpdate` from `Definition_5_1_extra_4.lean`
-- * project owner `bfgsInverseUpdate_mulVec` / `bfgsInverseUpdate_eq_expandedForm`
-- The source-facing memoryless matrix is therefore a bridge/view: the `H = 1`
-- specialization of the canonical inverse-BFGS owner, while the one-pair L-BFGS
-- statement should reuse the Algorithm 5.7.1 owner and its derived `rho` API rather than
-- restating that scalar as primitive data.

/-- Remark 5.7-extra-1 auxiliary result (1): setting `Hₖ = 1` in the inverse-form BFGS update gives
the memoryless BFGS matrix. This is the `H = 1` specialization of the Chapter 5 owner
`bfgsInverseUpdate`. -/
abbrev memorylessBfgsInverseUpdate (s y : Point) : MatrixN :=
  bfgsInverseUpdate (1 : MatrixN) s y

/-- Remark 5.7-extra-1 auxiliary result (2): the memoryless BFGS matrix also has the expanded form
`(1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) *
    (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
  (dotProduct s y)⁻¹ • Matrix.vecMulVec s s`. -/
theorem memorylessBfgsInverseUpdate_eq_expandedForm
    (s y : Point) :
    memorylessBfgsInverseUpdate s y =
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
        (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
  simp [memorylessBfgsInverseUpdate, bfgsInverseUpdate]

/-- Remark 5.7-extra-1 auxiliary result (3): the memoryless BFGS matrix satisfies the inverse-form
quasi-Newton equation `Hₖ₊₁ y = s`. -/
theorem memorylessBfgsInverseUpdate_mulVec
    (s y : Point) (hsy : dotProduct s y ≠ 0) :
    Matrix.toEuclideanLin (memorylessBfgsInverseUpdate s y) y = s := by
  simpa [memorylessBfgsInverseUpdate] using bfgsInverseUpdate_mulVec (1 : MatrixN) s y hsy

/-- Helper for Remark 5.7-extra-1: the memoryless BFGS matrix is the projector Gram
matrix `Vᵀ V` plus the rank-one secant correction `ρ s sᵀ`, where
`V = 1 - ρ • Matrix.vecMulVec y s`. -/
lemma memorylessBfgsInverseUpdate_eq_projectorGram
    (s y : Point) :
    memorylessBfgsInverseUpdate s y =
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s).transpose *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
        (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
  -- Rewrite `(5.7.43)` so the right factor becomes the projector `V` and the left factor is `Vᵀ`.
  calc
    memorylessBfgsInverseUpdate s y =
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec s y) *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
        (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
          rw [memorylessBfgsInverseUpdate_eq_expandedForm]
    _ =
      (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s).transpose *
          (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s) +
        (dotProduct s y)⁻¹ • Matrix.vecMulVec s s := by
          simp [sub_eq_add_neg, Matrix.transpose_vecMulVec]

/-- Helper for Remark 5.7-extra-1: the right BFGS projector acts on a vector by
subtracting the `s`-component scaled in the `y` direction. -/
lemma bfgsRightProjector_mulVec
    (s y : Point) (x : Fin n → ℝ) (ρ : ℝ) :
    (1 - ρ • Matrix.vecMulVec y s).mulVec x =
      x - (ρ * dotProduct s x) • y := by
  -- Evaluate the rank-one projector on `x` and collect the scalar factor on `y`.
  calc
    (1 - ρ • Matrix.vecMulVec y s).mulVec x
        = (1 : MatrixN).mulVec x - (ρ • Matrix.vecMulVec y s).mulVec x := by
            rw [Matrix.sub_mulVec]
    _ = x - ρ • (Matrix.vecMulVec y s).mulVec x := by
          rw [Matrix.smul_mulVec]
          simp
    _ = x - ρ • (dotProduct s x • y) := by
          simp [Matrix.vecMulVec_mulVec]
    _ = x - (ρ * dotProduct s x) • y := by
          ext i
          simp
          ring

/-- Helper for Remark 5.7-extra-1: a nonzero vector in the kernel of the memoryless
right projector must have nonzero pairing with `s`. -/
lemma memorylessBfgsProjector_zero_implies_dotProduct_ne_zero
    (s y : Point) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hVx : (1 - (dotProduct s y)⁻¹ • Matrix.vecMulVec y s).mulVec x = 0) :
    dotProduct s x ≠ 0 := by
  -- If `dotProduct s x = 0`, the projector formula collapses to `x = 0`, contradicting `hx`.
  intro hsx
  rw [bfgsRightProjector_mulVec] at hVx
  rw [hsx] at hVx
  have hxProj : x - ((dotProduct s y)⁻¹ * 0) • y = 0 := by
    simpa only [zero_mul, zero_smul] using hVx
  have hx0 : x = 0 := by
    simpa using hxProj
  exact hx hx0

/-- Chapter05 Remark 5.7-extra-1: under the curvature condition `0 < dotProduct s y`, the
memoryless BFGS matrix is positive definite. -/
theorem memorylessBfgsInverseUpdate_posDef
    (s y : Point) (hsy : 0 < dotProduct s y) :
    (memorylessBfgsInverseUpdate s y).PosDef := by
  let ρ : ℝ := (dotProduct s y)⁻¹
  let V : MatrixN := 1 - ρ • Matrix.vecMulVec y s
  have hρ : 0 < ρ := by
    simpa [ρ] using inv_pos.mpr hsy
  have hProjector :
      memorylessBfgsInverseUpdate s y = V.transpose * V + ρ • Matrix.vecMulVec s s := by
    -- Rewrite the memoryless update once into the projector-Gram form from `(5.7.42)`.
    simpa [V, ρ] using memorylessBfgsInverseUpdate_eq_projectorGram s y
  have hHermitianGram : (V.transpose * V).IsHermitian := by
    -- The Gram term is Hermitian because it is of the form `Vᵀ V`.
    simpa using (Matrix.isSymm_transpose_mul_self V)
  have hHermitianRankOne : (ρ • Matrix.vecMulVec s s).IsHermitian := by
    -- The secant rank-one term is symmetric, hence Hermitian over `ℝ`.
    have hSymm : (ρ • Matrix.vecMulVec s s).IsSymm := by
      refine Matrix.IsSymm.ext ?_
      intro i j
      simp [Matrix.vecMulVec_apply, mul_comm]
    simpa using hSymm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- The source decomposition makes Hermitian symmetry immediate term-by-term.
    rw [hProjector]
    exact hHermitianGram.add hHermitianRankOne
  · intro x hx
    have hGramEval :
        dotProduct x ((V.transpose * V).mulVec x) = dotProduct (V.mulVec x) (V.mulVec x) := by
      -- Move one copy of `V` across the bilinear pairing to expose the Gram square.
      calc
        dotProduct x ((V.transpose * V).mulVec x)
            = dotProduct x (V.transpose.mulVec (V.mulVec x)) := by
                rw [Matrix.mulVec_mulVec]
        _ = dotProduct (V.mulVec x) (V.mulVec x) := by
              rw [Matrix.dotProduct_transpose_mulVec]
    have hRankEval :
        dotProduct x ((ρ • Matrix.vecMulVec s s).mulVec x) =
          ρ * (dotProduct s x) ^ 2 := by
      -- Evaluate the rank-one correction on `x` and collect the secant scalar square.
      calc
        dotProduct x ((ρ • Matrix.vecMulVec s s).mulVec x)
            = dotProduct x (ρ • (Matrix.vecMulVec s s).mulVec x) := by
                rw [Matrix.smul_mulVec]
        _ = ρ * dotProduct x ((Matrix.vecMulVec s s).mulVec x) := by
              rw [dotProduct_smul, smul_eq_mul]
        _ = ρ * dotProduct x (dotProduct s x • s) := by
              simp [Matrix.vecMulVec_mulVec]
        _ = ρ * ((dotProduct s x) * dotProduct x s) := by
              rw [dotProduct_smul, smul_eq_mul]
        _ = ρ * (dotProduct s x) ^ 2 := by
              rw [dotProduct_comm]
              ring
    have hQuad :
        dotProduct x ((memorylessBfgsInverseUpdate s y).mulVec x) =
          dotProduct (V.mulVec x) (V.mulVec x) + ρ * (dotProduct s x) ^ 2 := by
      -- The quadratic form splits into the nonnegative Gram term and the secant rank-one term.
      rw [hProjector, Matrix.add_mulVec, dotProduct_add, hGramEval, hRankEval]
    by_cases hVx : V.mulVec x = 0
    · -- On the projector kernel, strict positivity comes from the rank-one correction.
      have hsx : dotProduct s x ≠ 0 := by
        simpa [V, ρ] using
          memorylessBfgsProjector_zero_implies_dotProduct_ne_zero s y x hx hVx
      have hRankPos : 0 < ρ * (dotProduct s x) ^ 2 := by
        exact mul_pos hρ (sq_pos_of_ne_zero hsx)
      have hPos : 0 < x ⬝ᵥ (memorylessBfgsInverseUpdate s y).mulVec x := by
        rw [hQuad, hVx]
        simpa using hRankPos
      simpa using hPos
    · -- Off the projector kernel, the Gram term is already strictly positive.
      have hGramNonneg : 0 ≤ dotProduct (V.mulVec x) (V.mulVec x) := by
        rw [dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((V.mulVec x) i)
      have hGramPos : 0 < dotProduct (V.mulVec x) (V.mulVec x) := by
        have hGramNe : dotProduct (V.mulVec x) (V.mulVec x) ≠ 0 := by
          intro hzero
          exact hVx ((dotProduct_self_eq_zero.mp hzero))
        exact lt_of_le_of_ne hGramNonneg hGramNe.symm
      have hRankNonneg : 0 ≤ ρ * (dotProduct s x) ^ 2 := by
        exact mul_nonneg hρ.le (sq_nonneg _)
      have hPos : 0 < x ⬝ᵥ (memorylessBfgsInverseUpdate s y).mulVec x := by
        rw [hQuad]
        exact add_pos_of_pos_of_nonneg hGramPos hRankNonneg
      simpa using hPos

/-- Remark 5.7-extra-1 auxiliary result (5): on the concrete two-loop-recursion surface of
`Algorithm_5_7_1`, taking one stored pair and the initial matrix `Hₖ⁽⁰⁾ = 1` makes L-BFGS
coincide with the memoryless BFGS matrix action. -/
theorem lbfgsTwoLoopRecursion_singleton_eq_memorylessBfgs
    (g s y : Point) :
    let entry : LBFGSHistoryEntry Point := { s := s, y := y }
    lbfgsTwoLoopRecursion (1 : MatrixN).toEuclideanLin g [entry] =
      Matrix.toEuclideanLin (memorylessBfgsInverseUpdate s y) g := by
  ext i
  simp [lbfgsTwoLoopRecursion_singleton, memorylessBfgsInverseUpdate, bfgsInverseUpdate,
    Matrix.toLpLin_apply, Matrix.vecMulVec_mulVec, PiLp.inner_apply, dotProduct,
    sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  ring_nf

end
