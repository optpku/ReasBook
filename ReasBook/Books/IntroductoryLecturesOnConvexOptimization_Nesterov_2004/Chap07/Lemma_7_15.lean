/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_8_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => Fin n → ℝ
local notation "SymmMat" => 𝕊^n

attribute [local instance] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace

/-
Lemma 7.15 lies in Chapter 7's positive-definite / semidefinite-factorization domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the project owners for symmetric, positive-semidefinite,
  and strict positive-definite matrices;
- `StrictPositiveSemidefiniteCone.inv`, the canonical inverse view of a strict-cone point;
- `mem_positiveSemidefiniteCone_iff`, the bridge from intrinsic cone membership to
  `Matrix.PosSemidef`;
- mathlib `Matrix.toQuadraticMap'`, the canonical quadratic-form owner on `Fin n → ℝ`.

Best owner abstraction:
- source-facing: Lemma 7.15's inverse-diagonal relaxation value and its semidefinite
  representation;
- core/canonical: the Chapter 5 symmetric-matrix cone owners together with
  `Matrix.toQuadraticMap'`;
- bridge/view: the textbook matrix-order and trace formulas recovered by the membership and
  expansion lemmas below.

Primitive data:
- `A : 𝕊^n₊₊`;
- `L : Mₙ`.

Derived API:
- inverse-diagonal feasibility expressed intrinsically by the PSD slack
  `A⁻¹ - diag(u) ∈ 𝕊^n₊`;
- semidefinite feasibility expressed on the symmetric carrier by `X ∈ 𝕊^n₊` and `trace X = 1`;
- the semidefinite objective written through the canonical quadratic-map owner instead of the
  duplicate entrywise formula `dotProduct (X.mulVec v) v`.

This refinement keeps the source-facing real-valued `inf`/`sup` statements, but removes the
parallel subtype `{A // A.PosDef}` and raw `Matrix.PosSemidef` surface from the primitive public
API. The textbook inequalities remain as bridge theorems.
-/

/-- The feasible diagonal vectors `u` for the inverse-diagonal relaxation, expressed intrinsically
by requiring the symmetric slack matrix `A⁻¹ - diag(u)` to be positive semidefinite and each
coordinate of `u` to be positive. -/
def factorizationDiagonalInverseFeasibleSet
    (A : 𝕊^n₊₊) : Set Eₙ :=
  {u |
    (StrictPositiveSemidefiniteCone.inv A -
        ⟨Matrix.diagonal u, by
          rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
          simp
        ⟩ : SymmMat) ∈ 𝕊^n₊ ∧
      ∀ i : Fin n, 0 < u i}

-- Proof sketch: expand membership in `𝕊^n₊` for the slack matrix `A⁻¹ - diag(u)`, then use
-- `Matrix.nonneg_iff_posSemidef` to recover the textbook matrix-order inequality
-- `diag(u) ≤ A⁻¹`.
/-- Membership in the inverse-diagonal feasible set means exactly that `diag(u) ≤ A⁻¹` and every
coordinate of `u` is positive. -/
theorem mem_factorizationDiagonalInverseFeasibleSet_iff
    (A : 𝕊^n₊₊) (u : Eₙ) :
    u ∈ factorizationDiagonalInverseFeasibleSet A ↔
      Matrix.diagonal u ≤ (((A : SymmMat) : Mₙ)⁻¹) ∧ ∀ i : Fin n, 0 < u i := by
  rw [factorizationDiagonalInverseFeasibleSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hfeas, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff] at hfeas
    refine ⟨?_, hpos⟩
    exact sub_nonneg.mp <| by
      simpa using (Matrix.nonneg_iff_posSemidef).mpr hfeas
  · rintro ⟨hdiag, hpos⟩
    refine ⟨?_, hpos⟩
    rw [mem_positiveSemidefiniteCone_iff]
    exact (Matrix.nonneg_iff_posSemidef).mp <| by
      simpa using sub_nonneg.mpr hdiag

/-- The inverse-diagonal relaxation value
`inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` attached to a positive-definite matrix `A`. -/
def factorizationDiagonalInverseRelaxationValue
    (A : 𝕊^n₊₊) : ℝ :=
  sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A)

/-- Expanding `factorizationDiagonalInverseRelaxationValue A` recovers the defining infimum over
the feasible diagonal vectors `u`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_sInf
    (A : 𝕊^n₊₊) :
    factorizationDiagonalInverseRelaxationValue A =
      sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A) :=
  rfl

/-- The feasible matrices `X` in the semidefinite representation: positive semidefinite symmetric
matrices with unit trace. -/
def factorizationSemidefiniteFeasibleSet : Set SymmMat :=
  {X | X ∈ 𝕊^n₊ ∧ Matrix.trace (X : Mₙ) = 1}

/-- Membership in the semidefinite feasible set means being positive semidefinite with unit trace.
-/
theorem mem_factorizationSemidefiniteFeasibleSet_iff
    (X : SymmMat) :
    X ∈ factorizationSemidefiniteFeasibleSet ↔
      (X : Mₙ).PosSemidef ∧ Matrix.trace (X : Mₙ) = 1 := by
  rw [factorizationSemidefiniteFeasibleSet, Set.mem_setOf_eq, mem_positiveSemidefiniteCone_iff]

/-- The semidefinite objective
`X ↦ (∑ᵢ √(qᵢᵀ X qᵢ))²`, where `qᵢ` is the `i`-th column of `L`, written as the `i`-th row of
`Lᵀ`. -/
def factorizationSemidefiniteObjective (L : Mₙ) (X : SymmMat) : ℝ :=
  (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)

/-- The semidefinite relaxation value attached to the factor matrix `L`. -/
def factorizationSemidefiniteRelaxationValue (L : Mₙ) : ℝ :=
  sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet)

/-- Expanding `factorizationSemidefiniteRelaxationValue L` gives the defining supremum of
`(∑ᵢ √(qᵢᵀ X qᵢ))²` over positive-semidefinite trace-one matrices `X`. -/
theorem factorizationSemidefiniteRelaxationValue_eq_sSup
    (L : Mₙ) :
    factorizationSemidefiniteRelaxationValue L =
      sSup (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet) :=
  rfl

/-- Helper for Lemma 7.15: the source-route strict weights are simplex points with every
coordinate strictly positive. -/
private def strictSimplexWeights : Set Eₙ :=
  {w | w ∈ stdSimplex ℝ (Fin n) ∧ ∀ i : Fin n, 0 < w i}

/-- Helper for Lemma 7.15: the fixed-weight payoff that linearizes the semidefinite objective. -/
private def strictWeightPayoff (L : Mₙ) (X : SymmMat) (w : Eₙ) : ℝ :=
  Matrix.trace ((X : Mₙ) * (L * Matrix.diagonal (fun i ↦ (w i)⁻¹) * Lᵀ))

/-- Helper for Lemma 7.15: matrix-order monotonicity of the trace on real symmetric matrices. -/
private theorem trace_le_trace_of_nonneg
    {A B : Mₙ} (hAB : A ≤ B) :
    Matrix.trace A ≤ Matrix.trace B := by
  -- Convert the order bound into positivity of the slack and then read that positivity on traces.
  have hslack : (B - A).PosSemidef := (Matrix.le_iff).mp hAB
  have htrace_nonneg : 0 ≤ Matrix.trace (B - A) := Matrix.PosSemidef.trace_nonneg hslack
  simpa [Matrix.trace_sub] using htrace_nonneg

/-- Helper for Lemma 7.15: the weighted columnwise quadratic terms are exactly one trace pairing
with the Gram-side diagonal matrix `L * diag(u) * Lᵀ`. -/
private theorem weighted_quadratic_sum_eq_trace_gram_diagonal
    (L : Mₙ) (X : SymmMat) (u : Eₙ) :
    (∑ i : Fin n, u i * (((X : Mₙ).toQuadraticMap') (Lᵀ i))) =
      Matrix.trace ((X : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) := by
  -- Cycle the trace so that the diagonal matrix acts on the right, then expand the diagonal sum.
  symm
  calc
    Matrix.trace ((X : Mₙ) * (L * Matrix.diagonal u * Lᵀ))
        = Matrix.trace (Lᵀ * (X : Mₙ) * (L * Matrix.diagonal u)) := by
            simpa [mul_assoc] using
              (Matrix.trace_mul_cycle (X : Mₙ) (L * Matrix.diagonal u) Lᵀ)
    _ = ∑ i : Fin n, u i * (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
      calc
        Matrix.trace (Lᵀ * (X : Mₙ) * (L * Matrix.diagonal u))
            = Matrix.trace ((Lᵀ * (X : Mₙ) * L) * Matrix.diagonal u) := by
                simp [mul_assoc]
        _ = ∑ i : Fin n, ((Lᵀ * (X : Mₙ) * L) i i) * u i := by
              simp [Matrix.trace, Matrix.mul_diagonal]
        _ = ∑ i : Fin n, u i * (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hsymm : ((X : Mₙ)).IsSymm := RealSymmetricMatrixSpace.isSymm X
              have hdiag_entry :
                  ((Lᵀ * (X : Mₙ) * L) i i) =
                    (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
                simp only [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
                  Matrix.toLinearMap₂'_apply', Matrix.mul_apply, Matrix.mulVec, dotProduct]
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hinner :
                    ∑ x_1, L x_1 i * ((X : Mₙ) x_1 x) =
                      ∑ x_1, L x_1 i * ((X : Mₙ) x x_1) := by
                  refine Finset.sum_congr rfl ?_
                  intro x_1 hx_1
                  have hentry : ((X : Mₙ) x_1 x) = ((X : Mₙ) x x_1) := by
                    symm
                    simpa [Matrix.transpose_apply] using
                      congrArg (fun M : Mₙ => M x_1 x) hsymm.eq
                  rw [hentry]
                have hcomm :
                    ∑ x_1, L x_1 i * ((X : Mₙ) x x_1) =
                      ∑ x_1, ((X : Mₙ) x x_1) * L x_1 i := by
                  refine Finset.sum_congr rfl ?_
                  intro x_1 hx_1
                  rw [mul_comm]
                have hsum_transpose :
                    ∑ j, Lᵀ i j * ((X : Mₙ) j x) =
                      ∑ x_1, ((X : Mₙ) x x_1) * Lᵀ i x_1 := by
                  simpa [Matrix.transpose_apply] using hinner.trans hcomm
                rw [hsum_transpose, mul_comm]
                simp [Matrix.transpose_apply]
              rw [hdiag_entry, mul_comm]

/-- Helper for Lemma 7.15: minimizing the scalar source-dual slice
`u ↦ u⁻¹ + a * u` over positive `u` gives the exact value `2 * √a`. -/
private theorem sInf_inverse_add_mul_eq_two_mul_sqrt
    (a : ℝ) (ha : 0 ≤ a) :
    sInf (((fun u : ℝ ↦ u⁻¹ + a * u) '' Set.Ioi (0 : ℝ)) : Set ℝ) =
      2 * Real.sqrt a := by
  by_cases ha0 : a = 0
  · -- At `a = 0`, the image is just the positive ray under inversion, whose infimum is `0`.
    have hzero :
        sInf ((((fun u : ℝ ↦ u⁻¹) '' Set.Ioi (0 : ℝ)) : Set ℝ)) = 0 := by
      have himageInv :
          (((fun u : ℝ ↦ u⁻¹) '' Set.Ioi (0 : ℝ)) : Set ℝ) = Set.Ioi (0 : ℝ) := by
        ext y
        constructor
        · rintro ⟨u, hu, rfl⟩
          have hu_pos : 0 < u := by
            simpa [Set.mem_Ioi] using hu
          simpa [Set.mem_Ioi] using (inv_pos.mpr hu_pos)
        · intro hy
          have hy_pos : 0 < y := by
            simpa [Set.mem_Ioi] using hy
          refine ⟨y⁻¹, ?_, ?_⟩
          · simpa [Set.mem_Ioi] using (inv_pos.mpr hy_pos)
          · have hy_ne : y ≠ 0 := hy_pos.ne'
            field_simp [hy_ne]
      rw [himageInv]
      simp
    simpa [ha0] using hzero
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    refine le_antisymm ?_ ?_
    · -- Evaluate the image at the optimizer `u = 1 / √a`.
      refine csInf_le ?_ ?_
      · refine ⟨2 * Real.sqrt a, ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        have hu_pos : 0 < u := by
          simpa [Set.mem_Ioi] using hu
        have hsqrt_sq : Real.sqrt a ^ 2 = a := by
          simpa [pow_two] using Real.sq_sqrt ha
        have hnonneg : 0 ≤ (1 - u * Real.sqrt a) ^ 2 / u := by
          refine div_nonneg ?_ hu_pos.le
          exact sq_nonneg _
        have hexpand :
            (1 - u * Real.sqrt a) ^ 2 / u = u⁻¹ + a * u - 2 * Real.sqrt a := by
          field_simp [hu_pos.ne']
          ring_nf
          rw [hsqrt_sq]
        have hnonneg' : 0 ≤ u⁻¹ + a * u - 2 * Real.sqrt a := by
          simpa [hexpand] using hnonneg
        linarith
      · have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
        have hsqrt_sq : Real.sqrt a ^ 2 = a := by
          simpa [pow_two] using Real.sq_sqrt ha
        refine ⟨(Real.sqrt a)⁻¹, inv_pos.mpr hsqrt, ?_⟩
        -- Substituting the optimizer collapses the scalar slice to the AM-GM value.
        field_simp [hsqrt.ne']
        ring_nf
        rw [hsqrt_sq]
        ring
    · -- The completed-square identity gives the global lower bound on the image.
      refine le_csInf ?_ ?_
      · have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha_pos
        exact Set.Nonempty.image _ ⟨(Real.sqrt a)⁻¹, inv_pos.mpr hsqrt⟩
      · rintro _ ⟨u, hu, rfl⟩
        have hu_pos : 0 < u := by
          simpa [Set.mem_Ioi] using hu
        have hsqrt_sq : Real.sqrt a ^ 2 = a := by
          simpa [pow_two] using Real.sq_sqrt ha
        have hnonneg : 0 ≤ (1 - u * Real.sqrt a) ^ 2 / u := by
          refine div_nonneg ?_ hu_pos.le
          exact sq_nonneg _
        have hexpand :
            (1 - u * Real.sqrt a) ^ 2 / u = u⁻¹ + a * u - 2 * Real.sqrt a := by
          field_simp [hu_pos.ne']
          ring_nf
          rw [hsqrt_sq]
        have hnonneg' : 0 ≤ u⁻¹ + a * u - 2 * Real.sqrt a := by
          simpa [hexpand] using hnonneg
        linarith

/-- Helper for Lemma 7.15: the reciprocal map is convex on the positive ray. -/
private theorem inv_weighted_average_le_weighted_average_inv
    {u v a b : ℝ}
    (hu : 0 < u) (hv : 0 < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u + b * v)⁻¹ ≤ a * u⁻¹ + b * v⁻¹ := by
  -- Compare the two reciprocal expressions after clearing denominators with the positive common
  -- denominator `u * v * (a * u + b * v)`.
  have hcomb_pos : 0 < a * u + b * v := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hv
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hu) (mul_nonneg hb hv.le)
  have hnonneg :
      0 ≤ a * b * (u - v) ^ (2 : ℕ) / (u * v * (a * u + b * v)) := by
    refine div_nonneg ?_ ?_
    · positivity
    · positivity
  have hidentity :
      a * u⁻¹ + b * v⁻¹ - (a * u + b * v)⁻¹ =
        a * b * (u - v) ^ (2 : ℕ) / (u * v * (a * u + b * v)) := by
    field_simp [hu.ne', hv.ne', hcomb_pos.ne']
    ring_nf
    have hab_sq : a ^ (2 : ℕ) + 2 * a * b + b ^ (2 : ℕ) = 1 := by
      nlinarith [hab]
    nlinarith [hab_sq]
  linarith

/-- Helper for Lemma 7.15: once the Gram-side matrix `L * diag(u) * Lᵀ` is bounded by the
identity, every trace-one PSD matrix yields the weak-duality estimate
`ψ(X) ≤ ∑ i, (u i)⁻¹`. -/
private theorem factorization_objective_le_inverse_diagonal_sum_of_trace_one_psd_and_gram_bound
    (L : Mₙ) (X : SymmMat) (u : Eₙ)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hgram : L * Matrix.diagonal u * Lᵀ ≤ (1 : Mₙ)) :
    factorizationSemidefiniteObjective L X ≤
      ∑ i : Fin n, (u i)⁻¹ := by
  rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
  rcases hX with ⟨hXpsd, hXtrace⟩
  let a : Fin n → ℝ := fun i ↦ (((X : Mₙ).toQuadraticMap') (Lᵀ i))
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := by
    -- Each quadratic value is nonnegative because `X` is positive semidefinite.
    intro i
    dsimp [a]
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using
      hXpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  have hweighted_sq :
      (∑ i : Fin n, Real.sqrt (a i)) ^ (2 : ℕ) ≤
        (∑ i : Fin n, (u i)⁻¹) * (∑ i : Fin n, u i * a i) := by
    -- Use the weighted Cauchy inequality in the sharp square-sum form.
    simpa [pow_two] using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := Finset.univ)
        (r := fun i : Fin n ↦ Real.sqrt (a i))
        (f := fun i : Fin n ↦ (u i)⁻¹)
        (g := fun i : Fin n ↦ u i * a i)
        (by
          intro i hi
          exact le_of_lt (inv_pos.mpr (hu_pos i)))
        (by
          intro i hi
          exact mul_nonneg (le_of_lt (hu_pos i)) (ha_nonneg i))
        (by
          intro i hi
          have hsquare : (Real.sqrt (a i)) ^ (2 : ℕ) = a i := by
            simpa [pow_two] using Real.sq_sqrt (ha_nonneg i)
          rw [hsquare]
          have hu_ne : u i ≠ 0 := (hu_pos i).ne'
          field_simp [hu_ne]))
  have htrace_bound : ∑ i : Fin n, u i * a i ≤ 1 := by
    -- Rewrite the weighted sum as a trace and compare it with `trace X = 1` by conjugating the
    -- order bound `L * diag(u) * Lᵀ ≤ I` through the square root factorization of `X`.
    let B : Mₙ := CFC.sqrt (X : Mₙ)
    have hB_symm : Bᵀ = B := by
      -- The square root of a real PSD symmetric matrix is symmetric again.
      have hsymm : B.IsSymm := by
        simpa [B, Matrix.IsHermitian, Matrix.IsSymm] using
          (CFC.sqrt_nonneg (X : Mₙ)).posSemidef.isHermitian
      simpa [Matrix.IsSymm] using hsymm
    have hX_eq : (X : Mₙ) = Bᵀ * B := by
      -- Rewrite `X` as the product of its symmetric square root with itself.
      calc
        (X : Mₙ) = B * B := by
          symm
          simpa [B] using CFC.sqrt_mul_sqrt_self (X : Mₙ) hXpsd.nonneg
        _ = Bᵀ * B := by simp [hB_symm]
    have hconj : B * (L * Matrix.diagonal u * Lᵀ) * Bᵀ ≤ B * (1 : Mₙ) * Bᵀ := by
      simpa using star_left_conjugate_le_conjugate hgram Bᵀ
    have htrace_le :
        Matrix.trace (B * (L * Matrix.diagonal u * Lᵀ) * Bᵀ) ≤
          Matrix.trace (B * (1 : Mₙ) * Bᵀ) :=
      trace_le_trace_of_nonneg hconj
    have htrace_id : Matrix.trace (B * (1 : Mₙ) * Bᵀ) = 1 := by
      calc
        Matrix.trace (B * (1 : Mₙ) * Bᵀ) = Matrix.trace (Bᵀ * B) := by
          simpa [mul_assoc] using Matrix.trace_mul_cycle B (1 : Mₙ) Bᵀ
        _ = Matrix.trace (X : Mₙ) := by rw [← hX_eq]
        _ = 1 := hXtrace
    calc
      ∑ i : Fin n, u i * a i
          = Matrix.trace ((X : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) := by
              rw [weighted_quadratic_sum_eq_trace_gram_diagonal]
      _ = Matrix.trace ((Bᵀ * B) * (L * Matrix.diagonal u * Lᵀ)) := by rw [hX_eq]
      _ = Matrix.trace (B * (L * Matrix.diagonal u * Lᵀ) * Bᵀ) := by
            calc
              Matrix.trace ((Bᵀ * B) * (L * Matrix.diagonal u * Lᵀ))
                  = Matrix.trace ((L * Matrix.diagonal u * Lᵀ) * (Bᵀ * B)) := by
                      simpa using
                        Matrix.trace_mul_comm (Bᵀ * B) (L * Matrix.diagonal u * Lᵀ)
              _ = Matrix.trace (B * (L * Matrix.diagonal u * Lᵀ) * Bᵀ) := by
                    simpa [mul_assoc] using
                      Matrix.trace_mul_cycle (L * Matrix.diagonal u * Lᵀ) Bᵀ B
      _ ≤ Matrix.trace (B * (1 : Mₙ) * Bᵀ) := htrace_le
      _ = 1 := htrace_id
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, (u i)⁻¹ := by
    -- The reciprocal objective is nonnegative because every feasible coordinate is positive.
    exact Finset.sum_nonneg fun i hi ↦ le_of_lt (inv_pos.mpr (hu_pos i))
  have hscale_bound :
      (∑ i : Fin n, (u i)⁻¹) * (∑ i : Fin n, u i * a i) ≤
        ∑ i : Fin n, (u i)⁻¹ := by
    -- The trace bound gives `∑ i u_i a_i ≤ 1`, so scaling by the nonnegative reciprocal sum
    -- preserves the inequality.
    simpa [one_mul] using mul_le_of_le_one_right hsum_nonneg htrace_bound
  exact hweighted_sq.trans hscale_bound

/-- Helper for Lemma 7.15: under `A = Lᵀ L`, the inverse-diagonal slack
`A⁻¹ - diag(u)` is positive semidefinite exactly when the Gram-side slack
`I - L * diag(u) * Lᵀ` is. -/
private theorem gram_diagonal_le_one_iff_inverse_diagonal_le_inv
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) (u : Eₙ) :
    Matrix.diagonal u ≤ (((A : SymmMat) : Mₙ)⁻¹) ↔
      L * Matrix.diagonal u * Lᵀ ≤ (1 : Mₙ) := by
  have hApos : (((A : SymmMat) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
  have hLunit : IsUnit L := by
    -- Positive definiteness of `A = Lᵀ L` forces the factor `L` to be invertible.
    have hprod : IsUnit (Lᵀ * L) := by
      simpa [hA] using hApos.isUnit
    exact isUnit_of_mul_isUnit_right hprod
  let _ : Invertible L := hLunit.invertible
  have hAinv :
      (((A : SymmMat) : Mₙ)⁻¹) = L⁻¹ * (Lᵀ)⁻¹ := by
    -- Compute the inverse of `Lᵀ * L` using the explicit inverse of `L`.
    rw [hA]
    exact Matrix.inv_eq_left_inv (by simp [mul_assoc])
  have hslack_eq :
      L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u) * Lᵀ =
        (1 : Mₙ) - L * Matrix.diagonal u * Lᵀ := by
    -- Conjugating the inverse-diagonal slack by `L` turns it into the Gram-side slack.
    calc
      L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u) * Lᵀ
          = (L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u)) * Lᵀ := by
              rw [mul_assoc]
      _ = (L * (((A : SymmMat) : Mₙ)⁻¹) - L * Matrix.diagonal u) * Lᵀ := by
            rw [mul_sub]
      _ = L * ((((A : SymmMat) : Mₙ)⁻¹) * Lᵀ) - L * (Matrix.diagonal u * Lᵀ) := by
            rw [sub_mul]
            simp [mul_assoc]
      _ = L * (((A : SymmMat) : Mₙ)⁻¹) * Lᵀ - L * Matrix.diagonal u * Lᵀ := by
            simp [mul_assoc]
      _ = (1 : Mₙ) - L * Matrix.diagonal u * Lᵀ := by
            rw [hAinv]
            simp [mul_assoc]
  -- Convert both order statements to PSD slacks and use invariance under invertible conjugation.
  simpa [Matrix.le_iff, hslack_eq, Matrix.star_eq_conjTranspose] using
    (hLunit.posSemidef_star_right_conjugate_iff
      (x := ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u))).symm

/-- Helper for Lemma 7.15: every semidefinite-feasible matrix `X` and every inverse-diagonal
feasible vector `u` satisfy the pointwise weak-duality estimate `ψ(X) ≤ ∑ᵢ uᵢ⁻¹`. -/
private theorem factorization_objective_le_inverse_diagonal_sum_of_feasible_pair
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L)
    (X : SymmMat) (u : Eₙ)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet)
    (hu : u ∈ factorizationDiagonalInverseFeasibleSet A) :
    factorizationSemidefiniteObjective L X ≤
      ∑ i : Fin n, (u i)⁻¹ := by
  rw [mem_factorizationDiagonalInverseFeasibleSet_iff] at hu
  rcases hu with ⟨hdiag, hu_pos⟩
  have hgram : L * Matrix.diagonal u * Lᵀ ≤ (1 : Mₙ) :=
    (gram_diagonal_le_one_iff_inverse_diagonal_le_inv A L hA u).mp hdiag
  -- Apply the weighted Cauchy estimate after transporting the inverse-diagonal constraint to the
  -- equivalent Gram-side order bound.
  exact
    factorization_objective_le_inverse_diagonal_sum_of_trace_one_psd_and_gram_bound
      L X u hX hu_pos hgram

/-- Helper for Lemma 7.15: in positive dimension, the semidefinite feasible set contains the
coordinate projector of trace `1`. -/
private theorem factorizationSemidefiniteFeasibleSet_nonempty
    (hn : 0 < n) :
    (factorizationSemidefiniteFeasibleSet : Set SymmMat).Nonempty := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨⟨Matrix.diagonal (Pi.single i0 (1 : ℝ)), by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simp
  ⟩, ?_⟩
  rw [mem_factorizationSemidefiniteFeasibleSet_iff]
  refine ⟨?_, ?_⟩
  · -- The rank-one coordinate projector is positive semidefinite because its diagonal is
    -- coordinatewise nonnegative.
    exact Matrix.PosSemidef.diagonal <| by
      intro i
      by_cases hi : i = i0
      · simp [Pi.single_apply, hi]
      · simp [hi]
  · -- Its trace is the single nonzero diagonal entry.
    simp [Matrix.trace, i0]

/-- Helper for Lemma 7.15: the trace-one positive-semidefinite slice is convex, matching the
compact side of the source minimax argument. -/
private theorem convex_factorizationSemidefiniteFeasibleSet :
    Convex ℝ (factorizationSemidefiniteFeasibleSet : Set SymmMat) := by
  intro X hX Y hY a b ha hb hab
  rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX hY ⊢
  refine ⟨?_, ?_⟩
  · -- Positive semidefiniteness is stable under nonnegative conic combinations.
    simpa using (hX.1.smul ha).add (hY.1.smul hb)
  · -- The trace constraint is affine, so the convex combination keeps trace `1`.
    calc
      Matrix.trace (((a • X + b • Y : SymmMat) : Mₙ))
          = a * Matrix.trace (X : Mₙ) + b * Matrix.trace (Y : Mₙ) := by
              simp [Matrix.trace_add, Matrix.trace_smul]
      _ = a * 1 + b * 1 := by rw [hX.2, hY.2]
      _ = 1 := by nlinarith

/-- Helper for Lemma 7.15: in positive dimension, the uniform weight vector belongs to the strict
simplex used in the source minimax route. -/
private theorem strict_simplex_weights_nonempty
    (hn : 0 < n) :
    (strictSimplexWeights (n := n)).Nonempty := by
  have hn_real : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn.ne'
  refine ⟨fun _ : Fin n ↦ (n : ℝ)⁻¹, ?_⟩
  rw [strictSimplexWeights, Set.mem_setOf_eq, stdSimplex]
  refine ⟨?_, fun _ ↦ inv_pos.mpr hn_real⟩
  refine ⟨fun _ ↦ le_of_lt (inv_pos.mpr hn_real), ?_⟩
  have hsum_inv : (∑ _ : Fin n, (n : ℝ)⁻¹) = (n : ℝ) * (n : ℝ)⁻¹ := by
    simp
  rw [hsum_inv]
  simp [hn_ne]

/-- Helper for Lemma 7.15: the strict simplex is convex because simplex mass is affine and each
coordinate stays in `(0, ∞)` under convex combinations. -/
private theorem convex_strictSimplexWeights :
    Convex ℝ (strictSimplexWeights (n := n)) := by
  intro w hw z hz a b ha hb hab
  rw [strictSimplexWeights, Set.mem_setOf_eq] at hw hz ⊢
  rcases hw with ⟨hw_simplex, hw_pos⟩
  rcases hz with ⟨hz_simplex, hz_pos⟩
  refine ⟨(convex_stdSimplex ℝ (Fin n)) hw_simplex hz_simplex ha hb hab, ?_⟩
  intro i
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by nlinarith
    simpa [ha0, hb1, Pi.smul_apply, Pi.add_apply] using hz_pos i
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hcoord_nonneg : 0 ≤ b * z i := mul_nonneg hb (le_of_lt (hz_pos i))
    have hcoord_pos : 0 < a * w i + b * z i := by
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (hw_pos i)) hcoord_nonneg
    simpa [Pi.smul_apply, Pi.add_apply] using hcoord_pos

/-- Helper for Lemma 7.15: fixing a strict simplex weight gives the easy Titu/Cauchy side of the
source linearization `ψ(X) ≤ payoff(X,w)`. -/
private theorem factorization_objective_le_strict_weight_payoff
    (L : Mₙ) (X : SymmMat) (w : Eₙ)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet)
    (hw : w ∈ strictSimplexWeights (n := n)) :
    factorizationSemidefiniteObjective L X ≤ strictWeightPayoff L X w := by
  rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
  rcases hX with ⟨hXpsd, _hXtrace⟩
  rw [strictSimplexWeights, Set.mem_setOf_eq] at hw
  rcases hw with ⟨hw_simplex, hw_pos⟩
  rw [stdSimplex] at hw_simplex
  rcases hw_simplex with ⟨_hw_nonneg, hw_sum⟩
  let a : Fin n → ℝ := fun i ↦ (((X : Mₙ).toQuadraticMap') (Lᵀ i))
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := by
    -- Feasibility of `X` keeps each quadratic term nonnegative, so the square roots are genuine.
    intro i
    dsimp [a]
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using
      hXpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  have hTitu :
      (∑ i : Fin n, Real.sqrt (a i)) ^ (2 : ℕ) / (∑ i : Fin n, w i) ≤
        ∑ i : Fin n, (Real.sqrt (a i)) ^ (2 : ℕ) / w i := by
    -- Titu's lemma is the source-side fixed-weight lower envelope for the quadratic-root sum.
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin n))
        (fun i ↦ Real.sqrt (a i)) (fun i _ ↦ hw_pos i))
  have hweighted :
      (∑ i : Fin n, Real.sqrt (a i)) ^ (2 : ℕ) ≤
        ∑ i : Fin n, (Real.sqrt (a i)) ^ (2 : ℕ) / w i := by
    simpa [hw_sum] using hTitu
  have hpayoff :
      ∑ i : Fin n, (w i)⁻¹ * a i = strictWeightPayoff L X w := by
    -- The trace pairing is exactly the weighted quadratic sum with reciprocal weights.
    simpa [strictWeightPayoff, a] using
      (weighted_quadratic_sum_eq_trace_gram_diagonal (L := L) (X := X)
        (u := fun i ↦ (w i)⁻¹))
  calc
    factorizationSemidefiniteObjective L X
        = (∑ i : Fin n, Real.sqrt (a i)) ^ (2 : ℕ) := by
            rfl
    _ ≤ ∑ i : Fin n, (Real.sqrt (a i)) ^ (2 : ℕ) / w i := hweighted
    _ = ∑ i : Fin n, (w i)⁻¹ * a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_eq_mul_inv, Real.sq_sqrt (ha_nonneg i), mul_comm]
    _ = strictWeightPayoff L X w := hpayoff

/-- Helper for Lemma 7.15: the easy half of the source linearization already identifies the
objective as a lower bound of the strict-weight payoff family. -/
private theorem factorization_objective_le_sInf_strict_weight_payoff
    (hn : 0 < n) (L : Mₙ) (X : SymmMat)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet) :
    factorizationSemidefiniteObjective L X ≤
      sInf (strictWeightPayoff L X '' strictSimplexWeights (n := n)) := by
  refine le_csInf ?_ ?_
  · exact Set.Nonempty.image _ (strict_simplex_weights_nonempty (n := n) hn)
  · rintro _ ⟨w, hw, rfl⟩
    exact factorization_objective_le_strict_weight_payoff L X w hX hw

/-- Helper for Lemma 7.15: the source-route regularized weights
`wᵢ = (√aᵢ + δ) / (∑ⱼ √aⱼ + n δ)` produce a strict-simplex witness whose payoff is within any
prescribed positive error of `ψ(X)`. -/
private theorem strict_weight_payoff_le_objective_add_epsilon
    (hn : 0 < n) (L : Mₙ) (X : SymmMat)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ strictSimplexWeights (n := n),
      strictWeightPayoff L X w ≤ factorizationSemidefiniteObjective L X + ε := by
  rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
  rcases hX with ⟨hXpsd, _hXtrace⟩
  let a : Fin n → ℝ := fun i ↦ (((X : Mₙ).toQuadraticMap') (Lᵀ i))
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := by
    -- Each source quadratic term stays nonnegative on the PSD feasible set.
    intro i
    dsimp [a]
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using
      hXpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  let s : ℝ := ∑ i : Fin n, Real.sqrt (a i)
  have hs_nonneg : 0 ≤ s := by
    -- The objective-side square-root sum is nonnegative termwise.
    exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg (a i)
  let δ : ℝ := ε / (((n : ℝ) * s) + 1)
  have hn_real : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hδ_pos : 0 < δ := by
    -- Choose the regularization scale directly so that the final error term is bounded by `ε`.
    apply div_pos hε
    nlinarith [hs_nonneg, hn_real]
  let d : ℝ := s + (n : ℝ) * δ
  have hd_pos : 0 < d := by
    have hnd_pos : 0 < (n : ℝ) * δ := mul_pos hn_real hδ_pos
    nlinarith [hs_nonneg, hnd_pos]
  let w : Eₙ := fun i ↦ (Real.sqrt (a i) + δ) / d
  have hw_mem : w ∈ strictSimplexWeights (n := n) := by
    rw [strictSimplexWeights, Set.mem_setOf_eq, stdSimplex]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- The regularized weights are nonnegative because both numerator and denominator are.
        intro i
        dsimp [w]
        exact le_of_lt <|
          div_pos (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos) hd_pos
      · -- The source normalization makes the regularized weights sum to `1`.
        calc
          ∑ i : Fin n, w i
              = ∑ i : Fin n, (Real.sqrt (a i) + δ) / d := by rfl
          _ = (∑ i : Fin n, (Real.sqrt (a i) + δ)) / d := by
                rw [Finset.sum_div]
          _ = (s + (n : ℝ) * δ) / d := by
                simp [s, Finset.sum_add_distrib, Fintype.card_fin]
          _ = 1 := by
                have hd_ne : d ≠ 0 := hd_pos.ne'
                field_simp [d, hd_ne]
                ring
    · -- Strict positivity is the only extra condition beyond simplex membership.
      intro i
      dsimp [w]
      exact div_pos (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos) hd_pos
  have hpayoff_eq :
      strictWeightPayoff L X w =
        d * ∑ i : Fin n, a i / (Real.sqrt (a i) + δ) := by
    -- Rewrite the payoff as the reciprocal-weight quadratic sum, then substitute the explicit
    -- regularized weights.
    have htrace :
        strictWeightPayoff L X w = ∑ i : Fin n, (w i)⁻¹ * a i := by
      symm
      simpa [strictWeightPayoff, a] using
        (weighted_quadratic_sum_eq_trace_gram_diagonal (L := L) (X := X)
          (u := fun i ↦ (w i)⁻¹))
    rw [htrace]
    calc
      ∑ i : Fin n, (w i)⁻¹ * a i
          = ∑ i : Fin n, (d / (Real.sqrt (a i) + δ)) * a i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hnum_pos : 0 < Real.sqrt (a i) + δ :=
                add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos
              dsimp [w]
              field_simp [hnum_pos.ne', hd_pos.ne']
      _ = ∑ i : Fin n, d * (a i / (Real.sqrt (a i) + δ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ = d * ∑ i : Fin n, a i / (Real.sqrt (a i) + δ) := by
            rw [Finset.mul_sum]
  have hterm_le : ∀ i : Fin n, a i / (Real.sqrt (a i) + δ) ≤ Real.sqrt (a i) := by
    -- The regularization denominator only decreases each source quotient.
    intro i
    have hden_pos : 0 < Real.sqrt (a i) + δ :=
      add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos
    have hsq : (Real.sqrt (a i)) ^ (2 : ℕ) = a i := by
      simpa [pow_two] using Real.sq_sqrt (ha_nonneg i)
    have hsq' : a i = Real.sqrt (a i) * Real.sqrt (a i) := by
      nlinarith [hsq]
    have hmul :
        Real.sqrt (a i) * Real.sqrt (a i) ≤
          Real.sqrt (a i) * (Real.sqrt (a i) + δ) := by
      gcongr
      linarith [hδ_pos.le]
    refine (div_le_iff₀ hden_pos).2 ?_
    calc
      a i = Real.sqrt (a i) * Real.sqrt (a i) := hsq'
      _ ≤ Real.sqrt (a i) * (Real.sqrt (a i) + δ) := hmul
  have hsum_div_le :
      ∑ i : Fin n, a i / (Real.sqrt (a i) + δ) ≤ s := by
    -- Summing the coordinatewise quotient bound returns to the source objective sum.
    calc
      ∑ i : Fin n, a i / (Real.sqrt (a i) + δ)
          ≤ ∑ i : Fin n, Real.sqrt (a i) := by
              exact Finset.sum_le_sum fun i _ ↦ hterm_le i
      _ = s := by rfl
  have hratio_le : ((n : ℝ) * s) / (((n : ℝ) * s) + 1) ≤ 1 := by
    have hns_nonneg : 0 ≤ (n : ℝ) * s := mul_nonneg hn_real.le hs_nonneg
    have hden_pos : 0 < ((n : ℝ) * s) + 1 := by
      nlinarith
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith
  have hδ_control : (n : ℝ) * δ * s ≤ ε := by
    have hε_nonneg : 0 ≤ ε := hε.le
    have hden_ne : (((n : ℝ) * s) + 1) ≠ 0 := by
      nlinarith [mul_nonneg hn_real.le hs_nonneg]
    calc
      (n : ℝ) * δ * s
          = ε * (((n : ℝ) * s) / (((n : ℝ) * s) + 1)) := by
              dsimp [δ]
              field_simp [hden_ne]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio_le hε_nonneg
      _ = ε := by ring
  refine ⟨w, hw_mem, ?_⟩
  have hd_nonneg : 0 ≤ d := hd_pos.le
  calc
    strictWeightPayoff L X w
        = d * ∑ i : Fin n, a i / (Real.sqrt (a i) + δ) := hpayoff_eq
    _ ≤ d * s := mul_le_mul_of_nonneg_left hsum_div_le hd_nonneg
    _ = factorizationSemidefiniteObjective L X + (n : ℝ) * δ * s := by
          simp [factorizationSemidefiniteObjective, d, s, pow_two]
          ring
    _ ≤ factorizationSemidefiniteObjective L X + ε := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hδ_control (factorizationSemidefiniteObjective L X)

/-- Helper for Lemma 7.15: the source linearization is exact pointwise, so each feasible `X`
realizes its objective as the infimum of the strict-weight payoff family. -/
private theorem factorization_objective_eq_sInf_strict_weight_payoff
    (hn : 0 < n) (L : Mₙ) (X : SymmMat)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet) :
    factorizationSemidefiniteObjective L X =
      sInf (strictWeightPayoff L X '' strictSimplexWeights (n := n)) := by
  refine le_antisymm ?_ ?_
  · -- The already-proved Titu inequality gives the lower bound on the infimum.
    exact factorization_objective_le_sInf_strict_weight_payoff (n := n) hn L X hX
  · -- The regularized source weights produce arbitrarily small upper errors.
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨w, hw, hwle⟩ :=
      strict_weight_payoff_le_objective_add_epsilon (n := n) hn L X hX (ε := ε) hε
    have hbelow :
        BddBelow (strictWeightPayoff L X '' strictSimplexWeights (n := n)) := by
      refine ⟨factorizationSemidefiniteObjective L X, ?_⟩
      rintro _ ⟨w', hw', rfl⟩
      exact factorization_objective_le_strict_weight_payoff L X w' hX hw'
    have hcsInf :
        sInf (strictWeightPayoff L X '' strictSimplexWeights (n := n)) ≤
          strictWeightPayoff L X w := by
      exact csInf_le hbelow ⟨w, hw, rfl⟩
    exact hcsInf.trans hwle

/-- Helper for Lemma 7.15: strict positive definiteness of `A` gives a constant diagonal witness
for the inverse-diagonal feasible set. -/
private theorem factorizationDiagonalInverseFeasibleSet_nonempty
    (A : 𝕊^n₊₊) :
    (factorizationDiagonalInverseFeasibleSet A).Nonempty := by
  let B : Mₙ := (((A : SymmMat) : Mₙ)⁻¹)
  have hB : B.PosDef := (strictPositiveSemidefiniteCone_posDef A).inv
  obtain ⟨m, hm_pos, _, _, hbound⟩ := posDef_exists_quadraticForm_bounds B hB
  refine ⟨fun _ : Fin n ↦ m, ?_⟩
  rw [mem_factorizationDiagonalInverseFeasibleSet_iff]
  refine ⟨?_, fun _ ↦ hm_pos⟩
  refine sub_nonneg.mp ?_
  have hdiag_const : Matrix.diagonal (fun _ : Fin n ↦ m) = m • (1 : Mₙ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal, hij]
  rw [hdiag_const]
  rw [Matrix.nonneg_iff_posSemidef]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- The slack `B - m I` is symmetric because both `B` and the scalar identity are symmetric.
    have hB_symm : B.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hB.posSemidef.isHermitian
    simpa [Matrix.IsHermitian, Matrix.IsSymm, hdiag_const, sub_eq_add_neg] using
      hB_symm.sub (Matrix.isSymm_one.smul m)
  · intro x
    -- Convert the quadratic lower bound `m ‖x‖² ≤ xᵀ B x` into positivity of the slack form.
    have hquad_bound :
        m * (x ⬝ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
      have hbound' :
          m * ‖WithLp.toLp 2 x‖ ^ 2 ≤
            inner ℝ (WithLp.toLp 2 x) (B.toEuclideanLin (WithLp.toLp 2 x)) := by
        simpa [real_inner_comm] using (hbound (WithLp.toLp 2 x)).1
      have hnorm_sq : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
        simpa [dotProduct, pow_two] using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)
      have hquad_B :
          inner ℝ (WithLp.toLp 2 x) (B.toEuclideanLin (WithLp.toLp 2 x)) =
            x ⬝ᵥ B *ᵥ x := by
        simpa using inner_toEuclideanLin_eq_dotProduct_mulVec B (WithLp.toLp 2 x)
      calc
        m * (x ⬝ᵥ x) = m * ‖WithLp.toLp 2 x‖ ^ 2 := by rw [hnorm_sq]
        _ ≤ inner ℝ (WithLp.toLp 2 x) (B.toEuclideanLin (WithLp.toLp 2 x)) := hbound'
        _ = x ⬝ᵥ B *ᵥ x := hquad_B
    have hquad_B :
        inner ℝ (WithLp.toLp 2 x) (B.toEuclideanLin (WithLp.toLp 2 x)) =
          x ⬝ᵥ B *ᵥ x := by
      simpa using inner_toEuclideanLin_eq_dotProduct_mulVec B (WithLp.toLp 2 x)
    have hquad_diag :
        x ⬝ᵥ ((m • (1 : Mₙ)) *ᵥ x) = m * (x ⬝ᵥ x) := by
      have hmulVec :
          ((m • (1 : Mₙ)) *ᵥ x) = fun i ↦ m * x i := by
        ext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      rw [hmulVec, dotProduct]
      calc
        ∑ i : Fin n, x i * (m * x i) = ∑ i : Fin n, m * (x i * x i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = m * ∑ i : Fin n, x i * x i := by rw [Finset.mul_sum]
        _ = m * (x ⬝ᵥ x) := by rfl
    have hsub :
        0 ≤ x ⬝ᵥ (B *ᵥ x) - x ⬝ᵥ ((m • (1 : Mₙ)) *ᵥ x) := by
      rw [hquad_diag]
      linarith
    simpa [sub_mulVec, dotProduct_sub] using hsub

/-- Helper for Lemma 7.15: halving any positive inverse-diagonal feasible point produces a strict
Gram-side slack matrix, so the source dual problem satisfies the Slater interior condition. -/
private theorem inverse_diagonal_strict_feasible_point
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) :
    ∃ u0 : Eₙ, (∀ i : Fin n, 0 < u0 i) ∧
      ((1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ).PosDef := by
  obtain ⟨u, hu_mem⟩ := factorizationDiagonalInverseFeasibleSet_nonempty A
  rw [mem_factorizationDiagonalInverseFeasibleSet_iff] at hu_mem
  rcases hu_mem with ⟨hu_diag, hu_pos⟩
  let u0 : Eₙ := fun i ↦ u i / 2
  have hu0_pos : ∀ i : Fin n, 0 < u0 i := by
    -- Halving preserves strict positivity of every diagonal entry.
    intro i
    dsimp [u0]
    exact div_pos (hu_pos i) (by norm_num)
  have hslack_psd :
      ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u).PosSemidef := by
    -- Repackage the inverse-diagonal order constraint as positivity of the slack matrix.
    exact (Matrix.nonneg_iff_posSemidef).mp <| by
      simpa using sub_nonneg.mpr hu_diag
  have hdiag_split :
      (((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0 =
        Matrix.diagonal u0 + ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u) := by
    -- The halved diagonal leaves an explicit positive diagonal margin in the slack.
    ext i j
    by_cases hij : i = j
    · subst hij
      dsimp [u0]
      simp [Matrix.diagonal]
      ring
    · simp [Matrix.diagonal, hij]
  have hdiag_posdef : (Matrix.diagonal u0).PosDef := by
    -- A diagonal matrix with strictly positive diagonal is positive definite.
    exact Matrix.PosDef.diagonal hu0_pos
  have hstrict_slack :
      ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0).PosDef := by
    -- Add the positive diagonal margin to the old PSD slack.
    rw [hdiag_split]
    exact Matrix.PosDef.add_posSemidef hdiag_posdef hslack_psd
  have hApos : (((A : SymmMat) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
  have hLunit : IsUnit L := by
    -- Positive definiteness of `A = Lᵀ L` forces the factor `L` to be invertible.
    have hprod : IsUnit (Lᵀ * L) := by
      simpa [hA] using hApos.isUnit
    exact isUnit_of_mul_isUnit_right hprod
  let _ : Invertible L := hLunit.invertible
  have hAinv :
      (((A : SymmMat) : Mₙ)⁻¹) = L⁻¹ * (Lᵀ)⁻¹ := by
    -- Compute the inverse of `Lᵀ * L` to expose the conjugation identity.
    rw [hA]
    exact Matrix.inv_eq_left_inv (by simp [mul_assoc])
  have hslack_eq :
      L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0) * Lᵀ =
        (1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ := by
    -- Conjugating the strict inverse-diagonal slack gives the strict Gram-side slack.
    calc
      L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0) * Lᵀ
          = (L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0)) * Lᵀ := by
              rw [mul_assoc]
      _ = (L * (((A : SymmMat) : Mₙ)⁻¹) - L * Matrix.diagonal u0) * Lᵀ := by
            rw [mul_sub]
      _ = L * ((((A : SymmMat) : Mₙ)⁻¹) * Lᵀ) - L * (Matrix.diagonal u0 * Lᵀ) := by
            rw [sub_mul]
            simp [mul_assoc]
      _ = L * (((A : SymmMat) : Mₙ)⁻¹) * Lᵀ - L * Matrix.diagonal u0 * Lᵀ := by
            simp [mul_assoc]
      _ = (1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ := by
            rw [hAinv]
            simp [mul_assoc]
  refine ⟨u0, hu0_pos, ?_⟩
  -- Transport strict positivity across the invertible conjugation by `L`.
  have hconj :
      (L * ((((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0) * Lᵀ).PosDef := by
    exact (hLunit.posDef_star_right_conjugate_iff
      (x := (((A : SymmMat) : Mₙ)⁻¹) - Matrix.diagonal u0)).2 hstrict_slack
  simpa [hslack_eq, Matrix.star_eq_conjTranspose] using hconj

/-- Helper for Lemma 7.15: the scalar AM-GM slice used in the PSD dual is bounded below by
`2 * √a`. -/
private theorem two_mul_sqrt_le_inverse_add_mul
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    2 * Real.sqrt a ≤ u⁻¹ + a * u := by
  have hsqrt_sq : Real.sqrt a ^ (2 : ℕ) = a := by
    simpa [pow_two] using Real.sq_sqrt ha
  have hnonneg : 0 ≤ (1 - u * Real.sqrt a) ^ (2 : ℕ) / u := by
    refine div_nonneg ?_ hu.le
    exact sq_nonneg _
  have hexpand :
      (1 - u * Real.sqrt a) ^ (2 : ℕ) / u =
        u⁻¹ + a * u - 2 * Real.sqrt a := by
    field_simp [pow_two, hu.ne']
    ring_nf
    rw [hsqrt_sq]
  have hnonneg' : 0 ≤ u⁻¹ + a * u - 2 * Real.sqrt a := by
    simpa [hexpand] using hnonneg
  linarith

/-- Helper for Lemma 7.15: the regularized reciprocal choice
`u = (√a + δ)⁻¹` approximates the scalar dual slice from above. -/
private theorem regularized_inverse_add_mul_le_two_mul_sqrt_add
    {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    (Real.sqrt a + δ) + a / (Real.sqrt a + δ) ≤ 2 * Real.sqrt a + δ := by
  have hden_pos : 0 < Real.sqrt a + δ :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg a) hδ
  have hsq : a = Real.sqrt a * Real.sqrt a := by
    nlinarith [Real.sq_sqrt ha]
  have hdiv : a / (Real.sqrt a + δ) ≤ Real.sqrt a := by
    refine (div_le_iff₀ hden_pos).2 ?_
    calc
      a = Real.sqrt a * Real.sqrt a := hsq
      _ ≤ Real.sqrt a * (Real.sqrt a + δ) := by
            gcongr
            linarith [hδ]
  linarith

/-- Helper for Lemma 7.15: the source-faithful PSD-multiplier dual slice for the inverse-diagonal
relaxation. -/
private def psdDualSlice
    (L : Mₙ) (Y : SymmMat) : ℝ :=
  sInf (((fun u : Eₙ ↦
      ∑ i : Fin n, (u i)⁻¹ +
        Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
        Matrix.trace (Y : Mₙ)) '' {u | ∀ i : Fin n, 0 < u i}) : Set ℝ)

/-- Helper for Lemma 7.15: the PSD dual problem is the supremum of the dual slice over all
positive-semidefinite multipliers. -/
private def psdDualSup
    (L : Mₙ) : ℝ :=
  sSup (psdDualSlice L '' {Y : SymmMat | Y ∈ 𝕊^n₊})

/-- Helper for Lemma 7.15: scaling a symmetric matrix scales each column quadratic value by the
same scalar. -/
private theorem quadratic_value_smul
    (t : ℝ) (X : SymmMat) (v : Eₙ) :
    ((((t • X : SymmMat) : Mₙ).toQuadraticMap') v) =
      t * (((X : Mₙ).toQuadraticMap') v) := by
  simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]

/-- Helper for Lemma 7.15: for a fixed positive-semidefinite multiplier `Y`, the PSD dual slice
evaluates exactly to the textbook sum-of-square-roots expression minus the trace term. -/
private theorem inverse_diagonal_psd_dualSlice_eq_sum_sqrt_sub_trace
    (L : Mₙ) (Y : SymmMat) (hY : Y ∈ 𝕊^n₊) :
    psdDualSlice L Y =
      2 * ∑ i : Fin n, Real.sqrt (((Y : Mₙ).toQuadraticMap') (Lᵀ i)) -
        Matrix.trace (Y : Mₙ) := by
  rw [psdDualSlice]
  let a : Fin n → ℝ := fun i ↦ (((Y : Mₙ).toQuadraticMap') (Lᵀ i))
  have hYpsd : (Y : Mₙ).PosSemidef := by
    rw [mem_positiveSemidefiniteCone_iff] at hY
    exact hY
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := by
    -- Positive semidefiniteness keeps every quadratic column value nonnegative.
    intro i
    dsimp [a]
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using
      hYpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  let S : Set ℝ :=
    ((fun u : Eₙ ↦ ∑ i : Fin n, ((u i)⁻¹ + a i * u i) - Matrix.trace (Y : Mₙ)) ''
      {u | ∀ i : Fin n, 0 < u i})
  have hrewrite :
      (((fun u : Eₙ ↦
          ∑ i : Fin n, (u i)⁻¹ +
            Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Y : Mₙ)) '' {u | ∀ i : Fin n, 0 < u i}) : Set ℝ) = S := by
    ext r
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      have htrace :
          Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) =
            ∑ i : Fin n, u i * a i := by
        simpa [a] using
          (weighted_quadratic_sum_eq_trace_gram_diagonal (L := L) (X := Y) (u := u)).symm
      dsimp [S]
      calc
        (∑ i : Fin n, ((u i)⁻¹ + a i * u i)) - Matrix.trace (Y : Mₙ)
            = (∑ i : Fin n, (u i)⁻¹) + (∑ i : Fin n, a i * u i) - Matrix.trace (Y : Mₙ) := by
                rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin n, (u i)⁻¹) + (∑ i : Fin n, u i * a i) - Matrix.trace (Y : Mₙ) := by
              refine congrArg
                (fun s : ℝ ↦ (∑ i : Fin n, (u i)⁻¹) + s - Matrix.trace (Y : Mₙ)) ?_
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
        _ = (∑ i : Fin n, (u i)⁻¹) +
              Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
              Matrix.trace (Y : Mₙ) := by rw [htrace]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      have htrace :
          Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) =
            ∑ i : Fin n, u i * a i := by
        simpa [a] using
          (weighted_quadratic_sum_eq_trace_gram_diagonal (L := L) (X := Y) (u := u)).symm
      dsimp [S]
      calc
        (∑ i : Fin n, (u i)⁻¹) +
            Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Y : Mₙ)
            = (∑ i : Fin n, (u i)⁻¹) + (∑ i : Fin n, u i * a i) - Matrix.trace (Y : Mₙ) := by
                rw [htrace]
        _ = (∑ i : Fin n, (u i)⁻¹) + (∑ i : Fin n, a i * u i) - Matrix.trace (Y : Mₙ) := by
              refine congrArg
                (fun s : ℝ ↦ (∑ i : Fin n, (u i)⁻¹) + s - Matrix.trace (Y : Mₙ)) ?_
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [mul_comm]
        _ = (∑ i : Fin n, ((u i)⁻¹ + a i * u i)) - Matrix.trace (Y : Mₙ) := by
              rw [Finset.sum_add_distrib]
  rw [hrewrite]
  have hS_nonempty : S.Nonempty := by
    refine Set.Nonempty.image _ ?_
    refine ⟨fun _ : Fin n ↦ 1, ?_⟩
    intro i
    norm_num
  have hlower :
      2 * ∑ i : Fin n, Real.sqrt (a i) - Matrix.trace (Y : Mₙ) ≤ sInf S := by
    refine le_csInf hS_nonempty ?_
    rintro r ⟨u, hu, rfl⟩
    have hsumbound :
        2 * ∑ i : Fin n, Real.sqrt (a i) ≤
          ∑ i : Fin n, ((u i)⁻¹ + a i * u i) := by
      calc
        2 * ∑ i : Fin n, Real.sqrt (a i)
            = ∑ i : Fin n, 2 * Real.sqrt (a i) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin n, ((u i)⁻¹ + a i * u i) := by
              exact Finset.sum_le_sum fun i _ ↦
                two_mul_sqrt_le_inverse_add_mul (ha_nonneg i) (hu i)
    linarith
  have hS_bddBelow : BddBelow S := by
    refine ⟨2 * ∑ i : Fin n, Real.sqrt (a i) - Matrix.trace (Y : Mₙ), ?_⟩
    rintro r ⟨u, hu, rfl⟩
    have hsumbound :
        2 * ∑ i : Fin n, Real.sqrt (a i) ≤
          ∑ i : Fin n, ((u i)⁻¹ + a i * u i) := by
      calc
        2 * ∑ i : Fin n, Real.sqrt (a i)
            = ∑ i : Fin n, 2 * Real.sqrt (a i) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin n, ((u i)⁻¹ + a i * u i) := by
              exact Finset.sum_le_sum fun i _ ↦
                two_mul_sqrt_le_inverse_add_mul (ha_nonneg i) (hu i)
    linarith
  have hupper :
      sInf S ≤
        2 * ∑ i : Fin n, Real.sqrt (a i) - Matrix.trace (Y : Mₙ) := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    let δ : ℝ := ε / ((n : ℝ) + 1)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      refine div_pos hε ?_
      positivity
    let uδ : Eₙ := fun i ↦ (Real.sqrt (a i) + δ)⁻¹
    have huδ : ∀ i : Fin n, 0 < uδ i := by
      intro i
      dsimp [uδ]
      exact inv_pos.mpr <| add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos
    have hcsInf :
        sInf S ≤
          ∑ i : Fin n, ((uδ i)⁻¹ + a i * uδ i) - Matrix.trace (Y : Mₙ) := by
      exact csInf_le hS_bddBelow ⟨uδ, huδ, rfl⟩
    have hterm_le :
        ∀ i : Fin n, (uδ i)⁻¹ + a i * uδ i ≤ 2 * Real.sqrt (a i) + δ := by
      intro i
      have hδi_pos : 0 < Real.sqrt (a i) + δ :=
        add_pos_of_nonneg_of_pos (Real.sqrt_nonneg (a i)) hδ_pos
      have huδ_inv :
          (uδ i)⁻¹ = Real.sqrt (a i) + δ := by
        simp [uδ]
      have huδ_mul :
          a i * uδ i = a i / (Real.sqrt (a i) + δ) := by
        dsimp [uδ]
        rw [div_eq_mul_inv]
      rw [huδ_inv, huδ_mul]
      exact regularized_inverse_add_mul_le_two_mul_sqrt_add (ha_nonneg i) hδ_pos
    have hsum_le :
        ∑ i : Fin n, ((uδ i)⁻¹ + a i * uδ i) ≤
          2 * ∑ i : Fin n, Real.sqrt (a i) + (n : ℝ) * δ := by
      calc
        ∑ i : Fin n, ((uδ i)⁻¹ + a i * uδ i)
            ≤ ∑ i : Fin n, (2 * Real.sqrt (a i) + δ) := by
                exact Finset.sum_le_sum fun i _ ↦ hterm_le i
        _ = 2 * ∑ i : Fin n, Real.sqrt (a i) + (n : ℝ) * δ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
              simp [Fintype.card_fin]
    have hδ_bound : (n : ℝ) * δ ≤ ε := by
      have hden_pos : 0 < (n : ℝ) + 1 := by positivity
      have hfrac_le : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        refine (div_le_iff₀ hden_pos).2 ?_
        linarith
      calc
        (n : ℝ) * δ = ε * ((n : ℝ) / ((n : ℝ) + 1)) := by
            dsimp [δ]
            ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfrac_le hε.le
        _ = ε := by ring
    linarith
  refine le_antisymm hupper hlower

/-- Helper for Lemma 7.15: on a trace-one feasible PSD matrix, the dual slice restricted to the
ray `t • X` becomes the one-variable source formula `2 * √t * Σ√(qᵢᵀXqᵢ) - t`. -/
private theorem dualSlice_smul_trace_one_eq_ray_formula
    (L : Mₙ) (X : SymmMat)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet)
    {t : ℝ} (ht : 0 ≤ t) :
    psdDualSlice L (t • X) =
      2 * Real.sqrt t *
          (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) - t := by
  rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
  rcases hX with ⟨hXpsd, hXtrace⟩
  have hsmul_psd : (t • X : SymmMat) ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff]
    simpa using hXpsd.smul ht
  rw [inverse_diagonal_psd_dualSlice_eq_sum_sqrt_sub_trace L (t • X) hsmul_psd]
  have ha_nonneg :
      ∀ i : Fin n, 0 ≤ (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
    -- The feasible PSD matrix `X` keeps all quadratic column values nonnegative.
    intro i
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using
      hXpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  calc
    2 * ∑ i : Fin n, Real.sqrt ((((t • X : SymmMat) : Mₙ).toQuadraticMap') (Lᵀ i)) -
        Matrix.trace (((t • X : SymmMat) : Mₙ))
        =
          2 * ∑ i : Fin n,
            Real.sqrt (t * (((X : Mₙ).toQuadraticMap') (Lᵀ i))) - t := by
              have hsum_eq :
                  ∑ i : Fin n, Real.sqrt ((((t • X : SymmMat) : Mₙ).toQuadraticMap') (Lᵀ i)) =
                    ∑ i : Fin n, Real.sqrt (t * (((X : Mₙ).toQuadraticMap') (Lᵀ i))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [quadratic_value_smul]
              have htrace_eq : Matrix.trace (((t • X : SymmMat) : Mₙ)) = t := by
                simp [Matrix.trace_smul, hXtrace]
              rw [hsum_eq, htrace_eq]
    _ =
          2 * ∑ i : Fin n,
            (Real.sqrt t * Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) - t := by
              have hsum_eq :
                  ∑ i : Fin n, Real.sqrt (t * (((X : Mₙ).toQuadraticMap') (Lᵀ i))) =
                    ∑ i : Fin n,
                      (Real.sqrt t * Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Real.sqrt_mul ht (((X : Mₙ).toQuadraticMap') (Lᵀ i))]
              rw [hsum_eq]
    _ =
          2 * (Real.sqrt t *
            ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) - t := by
              rw [← Finset.mul_sum]
    _ =
          2 * Real.sqrt t *
            (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) - t := by
              ring

/-- Helper for Lemma 7.15: along a fixed trace-one PSD ray, the dual slice attains its supremum
exactly at the semidefinite objective value. -/
private theorem ray_sup_dualSlice_eq_factorization_objective
    (L : Mₙ) (X : SymmMat)
    (hX : X ∈ factorizationSemidefiniteFeasibleSet) :
    sSup ((fun t : ℝ ↦ psdDualSlice L (t • X)) '' Set.Ici 0) =
      factorizationSemidefiniteObjective L X := by
  let s : ℝ := ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))
  let S : Set ℝ := ((fun t : ℝ ↦ psdDualSlice L (t • X)) '' Set.Ici 0)
  have hs_nonneg : 0 ≤ s := by
    -- The source square-root sum is nonnegative termwise along the trace-one PSD slice.
    exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg _
  have hupper : ∀ y ∈ S, y ≤ s ^ (2 : ℕ) := by
    -- The completed-square identity shows every point on the ray lies below `s^2`.
    rintro y ⟨t, ht, rfl⟩
    have hsq_nonneg : 0 ≤ (Real.sqrt t - s) ^ (2 : ℕ) := sq_nonneg _
    have hsqrt_sq : (Real.sqrt t) ^ (2 : ℕ) = t := by
      simpa [pow_two] using Real.sq_sqrt ht
    change psdDualSlice L (t • X) ≤ s ^ (2 : ℕ)
    rw [dualSlice_smul_trace_one_eq_ray_formula L X hX ht]
    dsimp [s]
    nlinarith
  have hmax_mem : s ^ (2 : ℕ) ∈ S := by
    -- The maximizing ray parameter is `t = s^2`, where the quadratic slice closes exactly.
    refine ⟨s ^ (2 : ℕ), ?_, ?_⟩
    · simpa [Set.mem_Ici] using sq_nonneg s
    · change psdDualSlice L ((s ^ (2 : ℕ)) • X) = s ^ (2 : ℕ)
      rw [dualSlice_smul_trace_one_eq_ray_formula L X hX (by positivity)]
      have hsqrt : Real.sqrt (s ^ (2 : ℕ)) = s := by
        simpa [pow_two, abs_of_nonneg hs_nonneg] using (Real.sqrt_sq_eq_abs s)
      rw [hsqrt]
      ring
  have hgreatest : IsGreatest S (s ^ (2 : ℕ)) := ⟨hmax_mem, hupper⟩
  -- Replace the auxiliary notation by the textbook objective after identifying the ray maximum.
  simpa [S, s, factorizationSemidefiniteObjective] using hgreatest.csSup_eq

/-- Helper for Lemma 7.15: the semidefinite relaxation value is nonnegative because every feasible
objective is a square. -/
private theorem factorizationSemidefiniteRelaxationValue_nonneg
    (L : Mₙ) :
    0 ≤ factorizationSemidefiniteRelaxationValue L := by
  -- Rewrite the relaxation as a supremum over squared objective values and read off termwise
  -- nonnegativity.
  rw [factorizationSemidefiniteRelaxationValue_eq_sSup]
  refine Real.sSup_nonneg ?_
  rintro _ ⟨X, hX, rfl⟩
  exact sq_nonneg _

/-- Helper for Lemma 7.15: on real symmetric matrices, the inherited Frobenius pairing is the
plain trace of the product because the transpose disappears. -/
private theorem frobeniusInner_eq_trace_mul
    (X Y : SymmMat) :
    ⟪X, Y⟫_F = Matrix.trace ((X : Mₙ) * (Y : Mₙ)) := by
  -- Rewrite the Chapter 5 Frobenius pairing and use symmetry to drop the transpose.
  rw [RealSymmetricMatrixSpace.frobeniusInner_def]
  have hsymm : ((X : Mₙ)ᵀ) = (X : Mₙ) := by
    exact RealSymmetricMatrixSpace.isSymm X |>.eq
  rw [hsymm]

/-- Helper for Lemma 7.15: the primal value region stores matrix slacks that lie below
`I - L * diag(u) * Lᵀ` together with scalar upper bounds on `∑ᵢ (u i)⁻¹`. -/
private def inverseDiagonalValueRegion
    (L : Mₙ) : Set (SymmMat × ℝ) :=
  {p | ∃ u : Eₙ, (∀ i : Fin n, 0 < u i) ∧
      ((p.1 : Mₙ) ≤ (1 : Mₙ) - L * Matrix.diagonal u * Lᵀ) ∧
      (∑ i : Fin n, (u i)⁻¹) ≤ p.2}

/-- Helper for Lemma 7.15: the primal value region is convex because the matrix slack is affine
in `u` and the reciprocal sum is convex on the positive orthant. -/
private theorem convex_inverseDiagonalValueRegion
    (L : Mₙ) :
    Convex ℝ (inverseDiagonalValueRegion L) := by
  -- Combine the affine Gram-slack interpolation with the coordinatewise convexity of `u ↦ u⁻¹`.
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨u, hu_pos, hp_mat, hp_cost⟩
  rcases hq with ⟨v, hv_pos, hq_mat, hq_cost⟩
  let w : Eₙ := fun i ↦ a * u i + b * v i
  refine ⟨w, ?_, ?_, ?_⟩
  · -- Every interpolated coordinate stays positive because the source weights are nonnegative.
    intro i
    dsimp [w]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hv_pos i
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (hu_pos i))
        (mul_nonneg hb (le_of_lt (hv_pos i)))
  · -- The matrix coordinate is affine in `u`, so the interpolated slack still dominates the
    -- interpolated point.
    have hdiag :
        Matrix.diagonal w = a • Matrix.diagonal u + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [w]
      · simp [Matrix.diagonal, hij]
    have hp_scaled :
        a • ((p.1 : SymmMat) : Mₙ) ≤ a • ((1 : Mₙ) - L * Matrix.diagonal u * Lᵀ) := by
      gcongr
    have hq_scaled :
        b • ((q.1 : SymmMat) : Mₙ) ≤ b • ((1 : Mₙ) - L * Matrix.diagonal v * Lᵀ) := by
      gcongr
    have hone : a • (1 : Mₙ) + b • (1 : Mₙ) = (1 : Mₙ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hab]
      · simp [hij]
    calc
      (((a • p + b • q).1 : SymmMat) : Mₙ)
          = a • ((p.1 : SymmMat) : Mₙ) + b • ((q.1 : SymmMat) : Mₙ) := by
              simp
      _ ≤ a • ((1 : Mₙ) - L * Matrix.diagonal u * Lᵀ) +
            b • ((1 : Mₙ) - L * Matrix.diagonal v * Lᵀ) := by
              exact add_le_add hp_scaled hq_scaled
      _ = (1 : Mₙ) - L * Matrix.diagonal w * Lᵀ := by
            calc
              a • ((1 : Mₙ) - L * Matrix.diagonal u * Lᵀ) +
                  b • ((1 : Mₙ) - L * Matrix.diagonal v * Lᵀ)
                  = (a • (1 : Mₙ) + b • (1 : Mₙ)) -
                      (a • (L * Matrix.diagonal u * Lᵀ) +
                        b • (L * Matrix.diagonal v * Lᵀ)) := by
                          simp [sub_eq_add_neg, smul_add, smul_neg, add_comm, add_left_comm,
                            add_assoc]
              _ = (1 : Mₙ) -
                    (a • (L * Matrix.diagonal u * Lᵀ) +
                      b • (L * Matrix.diagonal v * Lᵀ)) := by
                        rw [hone]
              _ = (1 : Mₙ) - L * Matrix.diagonal w * Lᵀ := by
                    rw [hdiag]
                    simp [mul_add, add_mul, mul_assoc]
  · -- The scalar epigraph coordinate is also convex because `u ↦ u⁻¹` is convex on `(0, ∞)`.
    calc
      ∑ i : Fin n, (w i)⁻¹
          ≤ ∑ i : Fin n, (a * (u i)⁻¹ + b * (v i)⁻¹) := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              exact inv_weighted_average_le_weighted_average_inv
                (hu_pos i) (hv_pos i) ha hb hab
      _ = a * ∑ i : Fin n, (u i)⁻¹ + b * ∑ i : Fin n, (v i)⁻¹ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * p.2 + b * q.2 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hp_cost ha)
              (mul_le_mul_of_nonneg_left hq_cost hb)
      _ = (a • p + b • q).2 := by
            simp

/-- Helper for Lemma 7.15: a separator that pairs nonnegatively with every PSD test matrix is
itself positive semidefinite. -/
private theorem separator_nonnegative_on_psd_cone_iff_psd
    (Z : SymmMat)
    (hZ :
      ∀ P : SymmMat, P ∈ 𝕊^n₊ →
        0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ))) :
    Z ∈ 𝕊^n₊ := by
  -- Test the separator on rank-one PSD matrices `x xᵀ` to recover the quadratic-form
  -- characterization of positive semidefiniteness.
  rw [mem_positiveSemidefiniteCone_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨RealSymmetricMatrixSpace.isHermitian Z, ?_⟩
  intro x
  have hx_symm : (Matrix.vecMulVec x x : Mₙ).IsSymm := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_comm]
  have hx_mem : (Matrix.vecMulVec x x : Mₙ) ∈ selfAdjointMatricesSubmodule 1 := by
    rwa [RealSymmetricMatrixSpace.mem_iff_isSymm]
  let P : SymmMat := ⟨Matrix.vecMulVec x x, hx_mem⟩
  have hP : P ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff]
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := ℝ) x)
  have htrace_nonneg : 0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := hZ P hP
  calc
    0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := htrace_nonneg
    _ = Matrix.trace ((Z : Mₙ) * Matrix.vecMulVec x x) := by rfl
    _ = Matrix.trace (Matrix.vecMulVec ((Z : Mₙ) *ᵥ x) x) := by
          rw [Matrix.mul_vecMulVec]
    _ = ((Z : Mₙ) *ᵥ x) ⬝ᵥ x := by
          rw [Matrix.trace_vecMulVec]
    _ = x ⬝ᵥ ((Z : Mₙ) *ᵥ x) := by
          rw [dotProduct_comm]

/-- Helper for Lemma 7.15: a strict Gram-side feasible point produces an interior point of the
primal value region by leaving room in both the matrix slack and the scalar epigraph direction. -/
private theorem inverseDiagonalValueRegion_interior_nonempty_of_strict_feasible
    (L : Mₙ) {u0 : Eₙ}
    (hu0_pos : ∀ i : Fin n, 0 < u0 i)
    (hslack : ((1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ).PosDef) :
    (interior (inverseDiagonalValueRegion L)).Nonempty := by
  -- Use the strict slack as an open matrix margin and the epigraph half-line as an open scalar
  -- margin around the point `(0, cost0 + 1)`.
  have hslack_symm : ((1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hslack.isHermitian
  have hslack_mem :
      ((1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ : Mₙ) ∈ selfAdjointMatricesSubmodule 1 := by
    rwa [RealSymmetricMatrixSpace.mem_iff_isSymm]
  let S0 : SymmMat := ⟨(1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ, hslack_mem⟩
  let c0 : ℝ := ∑ i : Fin n, (u0 i)⁻¹
  let U : Set (SymmMat × ℝ) :=
    {p | S0 - p.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧ c0 < p.2}
  have hU_open : IsOpen U := by
    -- The matrix-margin condition is the preimage of the open strict cone under an affine map,
    -- and the scalar condition is the open upper half-line.
    have hstrict_open : IsOpen (𝕊^n₊₊ : Set SymmMat) := by
      exact (isOpen_interior : IsOpen (interior (𝕊^n₊ : Set SymmMat)))
    have hmatrix_open :
        IsOpen ((fun p : SymmMat × ℝ ↦ S0 - p.1) ⁻¹' (𝕊^n₊₊ : Set SymmMat)) :=
      hstrict_open.preimage (continuous_const.sub continuous_fst)
    have hscalar_open :
        IsOpen ((fun p : SymmMat × ℝ ↦ p.2) ⁻¹' Set.Ioi c0) :=
      isOpen_Ioi.preimage continuous_snd
    simpa [U, Set.preimage, Set.setOf_and] using hmatrix_open.inter hscalar_open
  have hU_subset : U ⊆ inverseDiagonalValueRegion L := by
    intro p hp
    rcases hp with ⟨hp_mat, hp_cost⟩
    have hp_psd : S0 - p.1 ∈ (𝕊^n₊ : Set SymmMat) := interior_subset hp_mat
    have hp_le :
        ((p.1 : SymmMat) : Mₙ) ≤ (S0 : Mₙ) := by
      rw [mem_positiveSemidefiniteCone_iff] at hp_psd
      exact sub_nonneg.mp <| by
        simpa using (Matrix.nonneg_iff_posSemidef).mpr hp_psd
    refine ⟨u0, hu0_pos, ?_, hp_cost.le⟩
    simpa [S0] using hp_le
  let p0 : SymmMat × ℝ := ((0 : SymmMat), c0 + 1)
  have hp0_mem : p0 ∈ U := by
    refine ⟨?_, by simp [p0, c0]⟩
    simpa [p0, S0] using (mem_strictPositiveSemidefiniteCone_of_posDef hslack : S0 ∈ 𝕊^n₊₊)
  refine ⟨p0, ?_⟩
  -- The open neighborhood `U` around `p0` lies in the value region, so `p0` is an interior point.
  refine mem_interior_iff_mem_nhds.2 ?_
  exact Filter.mem_of_superset (hU_open.mem_nhds hp0_mem) hU_subset

/-- Helper for Lemma 7.15: a separating inequality with positive scalar coefficient yields a lower
bound on the PSD dual slice of the normalized multiplier. -/
private theorem separatorBound_le_psdDualSlice
    (L : Mₙ) {α a : ℝ} {Z Y : SymmMat}
    (ha_pos : 0 < a)
    (hZ_eq : Z = a • Y)
    (hsep :
      ∀ p ∈ inverseDiagonalValueRegion L,
        Matrix.trace ((Z : Mₙ) * ((p.1 : SymmMat) : Mₙ)) - a * p.2 ≤ -a * α) :
    α ≤ psdDualSlice L Y := by
  rw [psdDualSlice]
  refine le_csInf ?_ ?_
  · refine Set.Nonempty.image _ ?_
    exact ⟨fun _ ↦ 1, fun _ ↦ zero_lt_one⟩
  · rintro r ⟨u, hu_pos, rfl⟩
    have hslack_symm :
        ((1 : Mₙ) - L * Matrix.diagonal u * Lᵀ).IsSymm := by
      rw [Matrix.IsSymm]
      simp [mul_assoc]
    let Su : SymmMat := ⟨(1 : Mₙ) - L * Matrix.diagonal u * Lᵀ, by
      rwa [RealSymmetricMatrixSpace.mem_iff_isSymm]⟩
    have hSu_mem :
        (Su, ∑ i : Fin n, (u i)⁻¹) ∈ inverseDiagonalValueRegion L := by
      refine ⟨u, hu_pos, le_rfl, le_rfl⟩
    have hsep_u :
        Matrix.trace ((Z : Mₙ) * ((Su : SymmMat) : Mₙ)) -
            a * (∑ i : Fin n, (u i)⁻¹) ≤
          -a * α := by
      simpa [Su] using hsep (Su, ∑ i : Fin n, (u i)⁻¹) hSu_mem
    have hscaled :
        a * α ≤
          a * (∑ i : Fin n, (u i)⁻¹) +
            Matrix.trace ((Z : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Z : Mₙ) := by
      have htrace_Su :
          Matrix.trace ((Z : Mₙ) * ((Su : SymmMat) : Mₙ)) =
            Matrix.trace (Z : Mₙ) -
              Matrix.trace ((Z : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) := by
        calc
          Matrix.trace ((Z : Mₙ) * ((Su : SymmMat) : Mₙ))
              = Matrix.trace ((Z : Mₙ) * ((1 : Mₙ) - L * Matrix.diagonal u * Lᵀ)) := by
                  rfl
          _ = Matrix.trace ((Z : Mₙ) * (1 : Mₙ)) -
                Matrix.trace ((Z : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) := by
                  rw [Matrix.mul_sub, Matrix.trace_sub]
          _ = Matrix.trace (Z : Mₙ) -
                Matrix.trace ((Z : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) := by
                  simp
      rw [htrace_Su] at hsep_u
      linarith
    have hrewrite :
        a * (∑ i : Fin n, (u i)⁻¹ +
            Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Y : Mₙ)) =
          a * (∑ i : Fin n, (u i)⁻¹) +
            Matrix.trace ((Z : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Z : Mₙ) := by
      rw [hZ_eq]
      simp [Matrix.trace_smul, sub_eq_add_neg, mul_add, mul_assoc]
    have hscaled' :
        a * α ≤
          a * (∑ i : Fin n, (u i)⁻¹ +
            Matrix.trace ((Y : Mₙ) * (L * Matrix.diagonal u * Lᵀ)) -
            Matrix.trace (Y : Mₙ)) := by
      rw [hrewrite]
      exact hscaled
    exact le_of_mul_le_mul_left hscaled' ha_pos

/-- Helper for Lemma 7.15: once the PSD-dual image is known to be bounded above, a strict
Gram-side feasible point yields the reverse inequality from the primal value to the dual
supremum by separating the primal value region at the point `(0, α)`. -/
private theorem inverse_diagonal_value_le_psdDualSup_of_slater
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L)
    (hDualImageBddAbove :
      BddAbove (psdDualSlice L '' {Y : SymmMat | Y ∈ 𝕊^n₊})) :
    factorizationDiagonalInverseRelaxationValue A ≤ psdDualSup L := by
  let α : ℝ := factorizationDiagonalInverseRelaxationValue A
  let xα : SymmMat × ℝ := ((0 : SymmMat), α)
  obtain ⟨u0, hu0_pos, hslack0_posdef⟩ := inverse_diagonal_strict_feasible_point A L hA
  let slack0M : Mₙ := (1 : Mₙ) - L * Matrix.diagonal u0 * Lᵀ
  let c0 : ℝ := ∑ i : Fin n, (u0 i)⁻¹
  have hslack0_nonneg : (0 : Mₙ) ≤ slack0M := by
    simpa [slack0M] using (Matrix.nonneg_iff_posSemidef).mpr hslack0_posdef.posSemidef
  have hp0_mem : ((0 : SymmMat), c0) ∈ inverseDiagonalValueRegion L := by
    -- The strict feasible diagonal vector gives a zero-slack point on the primal value region.
    refine ⟨u0, hu0_pos, hslack0_nonneg, le_rfl⟩
  have hp0_up_mem : ((0 : SymmMat), c0 + 1) ∈ inverseDiagonalValueRegion L := by
    -- The value region is an epigraph in the scalar coordinate, so we may move one unit upward.
    refine ⟨u0, hu0_pos, hslack0_nonneg, ?_⟩
    linarith
  have hprimalImageBddBelow :
      BddBelow ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) '' factorizationDiagonalInverseFeasibleSet A) :=
    by
      refine ⟨0, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      rw [mem_factorizationDiagonalInverseFeasibleSet_iff] at hu
      exact Finset.sum_nonneg fun i _ ↦ le_of_lt (inv_pos.mpr (hu.2 i))
  have hzeroFiberLowerBound :
      ∀ {c : ℝ}, ((0 : SymmMat), c) ∈ inverseDiagonalValueRegion L → α ≤ c := by
    intro c hc
    rcases hc with ⟨u, hu_pos, hzero_le, hcost⟩
    have hgram : L * Matrix.diagonal u * Lᵀ ≤ (1 : Mₙ) := by
      exact sub_nonneg.mp <| by simpa using hzero_le
    have hdiag :
        Matrix.diagonal u ≤ (((A : SymmMat) : Mₙ)⁻¹) := by
      exact (gram_diagonal_le_one_iff_inverse_diagonal_le_inv A L hA u).mpr hgram
    have hu_feas : u ∈ factorizationDiagonalInverseFeasibleSet A := by
      rw [mem_factorizationDiagonalInverseFeasibleSet_iff]
      exact ⟨hdiag, hu_pos⟩
    -- Compare the zero-fiber point with the defining infimum of the primal value.
    have hα_le_cost :
        α ≤ ∑ i : Fin n, (u i)⁻¹ := by
      simpa [α] using
        (show factorizationDiagonalInverseRelaxationValue A ≤ ∑ i : Fin n, (u i)⁻¹ by
          rw [factorizationDiagonalInverseRelaxationValue_eq_sInf]
          exact csInf_le hprimalImageBddBelow ⟨u, hu_feas, rfl⟩)
    exact hα_le_cost.trans hcost
  have hα_le_c0 : α ≤ c0 := hzeroFiberLowerBound hp0_mem
  have hinterior_nonempty :
      (interior (inverseDiagonalValueRegion L)).Nonempty := by
    exact inverseDiagonalValueRegion_interior_nonempty_of_strict_feasible L hu0_pos hslack0_posdef
  have hxα_not_mem_interior : xα ∉ interior (inverseDiagonalValueRegion L) := by
    -- Any interior neighborhood around `((0), α)` would contain a zero-fiber point below the
    -- infimum value, contradicting the zero-fiber lower bound.
    intro hxα_mem
    let γ : ℝ → SymmMat × ℝ := fun t ↦ xα + t • ((0 : SymmMat), (1 : ℝ))
    have hγ_cont : Continuous γ := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hpre :
        {t : ℝ | γ t ∈ interior (inverseDiagonalValueRegion L)} ∈ nhds (0 : ℝ) := by
      have hγ0_mem : γ 0 ∈ interior (inverseDiagonalValueRegion L) := by
        simpa [γ, xα] using hxα_mem
      exact hγ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hγ0_mem)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
    have hhalf_mem : (-(ε / 2) : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hneg_half : (-(ε / 2) : ℝ) < 0 := by
        nlinarith
      simpa [abs_of_neg hneg_half] using half_lt_self hε_pos
    have hbelow_mem :
        ((0 : SymmMat), α - ε / 2) ∈ inverseDiagonalValueRegion L := by
      exact interior_subset <| by
        have hmem : γ (-(ε / 2)) ∈ interior (inverseDiagonalValueRegion L) := hε_sub hhalf_mem
        simpa [γ, xα, sub_eq_add_neg] using hmem
    have hα_le : α ≤ α - ε / 2 := hzeroFiberLowerBound hbelow_mem
    linarith
  obtain ⟨f, hf_ne, hf_sep_raw⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      (convex_inverseDiagonalValueRegion L) hxα_not_mem_interior hinterior_nonempty
  obtain ⟨Z, hmatrixRep⟩ :
      ∃ Z : SymmMat, ∀ S : SymmMat, f (S, 0) = Matrix.trace ((Z : Mₙ) * (S : Mₙ)) := by
    let gMatrix : StrongDual ℝ SymmMat := f.comp (ContinuousLinearMap.inl ℝ SymmMat ℝ)
    let b := stdOrthonormalBasis ℝ SymmMat
    let Z : SymmMat := ∑ i, gMatrix (b i) • b i
    refine ⟨Z, ?_⟩
    intro S
    have hrepr :
        gMatrix S = ∑ i, inner ℝ (b i) S * gMatrix (b i) := by
      have hsum := congrArg gMatrix (b.sum_repr' S)
      simpa [map_sum, map_smul, mul_comm] using hsum.symm
    have hinner :
        inner ℝ Z S = ∑ i, gMatrix (b i) * inner ℝ (b i) S := by
      simp [Z, sum_inner, real_inner_smul_left]
    have hinner' :
        inner ℝ Z S = ∑ i, inner ℝ (b i) S * gMatrix (b i) := by
      rw [hinner]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [mul_comm]
    calc
      f (S, 0) = gMatrix S := by
        rfl
      _ = inner ℝ Z S := by rw [hinner', hrepr]
      _ = Matrix.trace ((Z : Mₙ) * (S : Mₙ)) := by
        rw [RealSymmetricMatrixSpace.inner_eq_frobeniusInner, frobeniusInner_eq_trace_mul]
  let a : ℝ := -f ((0 : SymmMat), (1 : ℝ))
  have hf_eval :
      ∀ p : SymmMat × ℝ,
        f p = Matrix.trace ((Z : Mₙ) * ((p.1 : SymmMat) : Mₙ)) - a * p.2 := by
    intro p
    rcases p with ⟨S, c⟩
    have hsplit : f (S, c) = f (S, 0) + f (0, c) := by
      rw [show (S, c) = (S, 0) + (0, c) by ext <;> simp, map_add]
    have hmatrix :
        f (S, 0) = Matrix.trace ((Z : Mₙ) * (S : Mₙ)) := by
      exact hmatrixRep S
    have hscalar :
        f (0, c) = -a * c := by
      calc
        f (0, c) = f (c • ((0 : SymmMat), (1 : ℝ))) := by
          congr 1
          ext <;> simp [smul_eq_mul]
        _ = c * f ((0 : SymmMat), (1 : ℝ)) := by
          rw [map_smul]
          simp [smul_eq_mul]
        _ = -a * c := by
          simp [a, mul_comm]
    rw [hsplit, hmatrix, hscalar]
    ring
  have hf_sep :
      ∀ p ∈ inverseDiagonalValueRegion L,
        Matrix.trace ((Z : Mₙ) * ((p.1 : SymmMat) : Mₙ)) - a * p.2 ≤ -a * α := by
    intro p hp
    have hp_sep : f p ≤ f xα := hf_sep_raw p hp
    rw [hf_eval p, hf_eval xα] at hp_sep
    simpa [xα, a] using hp_sep
  have hrecession_nonpos :
      ∀ {p d : SymmMat × ℝ}, p ∈ inverseDiagonalValueRegion L →
        (∀ t : ℝ, 0 ≤ t → p + t • d ∈ inverseDiagonalValueRegion L) →
        f d ≤ 0 := by
    intro p d hp hdir
    by_contra hd_pos
    have hfd_pos : 0 < f d := lt_of_not_ge hd_pos
    let t : ℝ := (f xα - f p + 1) / f d
    have ht_nonneg : 0 ≤ t := by
      refine div_nonneg ?_ hfd_pos.le
      linarith [hf_sep_raw p hp]
    have hsep_t : f (p + t • d) ≤ f xα := hf_sep_raw (p + t • d) (hdir t ht_nonneg)
    have hlin :
        f (p + t • d) = f p + t * f d := by
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
      simp [t, smul_eq_mul, mul_comm]
    rw [hlin] at hsep_t
    have hfd_ne : f d ≠ 0 := ne_of_gt hfd_pos
    have htd : t * f d = 1 + f xα - f p := by
      dsimp [t]
      field_simp [t, hfd_ne]
      ring_nf
    linarith
  have hup_dir :
      f ((0 : SymmMat), (1 : ℝ)) ≤ 0 := by
    refine hrecession_nonpos hp0_mem ?_
    intro t ht
    refine ⟨u0, hu0_pos, ?_, ?_⟩
    · simpa [slack0M, sub_eq_add_neg] using hslack0_nonneg
    simpa [c0] using add_le_add_left ht c0
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using neg_nonneg.mpr hup_dir
  have htrace_nonneg :
      ∀ P : SymmMat, P ∈ 𝕊^n₊ → 0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := by
    intro P hP
    have hPpsd : (P : Mₙ).PosSemidef := by
      rw [mem_positiveSemidefiniteCone_iff] at hP
      exact hP
    have hneg_dir :
        f ((-P : SymmMat), (0 : ℝ)) ≤ 0 := by
      refine hrecession_nonpos hp0_mem ?_
      intro t ht
      refine ⟨u0, hu0_pos, ?_, ?_⟩
      · exact sub_nonneg.mp <| by
          have hsum_psd : (slack0M + t • (P : Mₙ)).PosSemidef :=
            hslack0_posdef.posSemidef.add (hPpsd.smul ht)
          simpa [slack0M, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_neg] using
            (Matrix.nonneg_iff_posSemidef).mpr hsum_psd
      · simp [c0]
    have hneg_trace : -Matrix.trace ((Z : Mₙ) * (P : Mₙ)) ≤ 0 := by
      rw [hf_eval] at hneg_dir
      simpa [Matrix.mul_neg, a] using hneg_dir
    linarith
  have hZ_psd : Z ∈ 𝕊^n₊ := separator_nonnegative_on_psd_cone_iff_psd Z htrace_nonneg
  have hp0_int :
      ((0 : SymmMat), c0 + 1) ∈ interior (inverseDiagonalValueRegion L) := by
    -- Reuse the strict feasible slack as an explicit open neighborhood around the zero matrix.
    have hslack0_symm : slack0M.IsSymm := by
      simpa [slack0M, Matrix.IsHermitian, Matrix.IsSymm] using hslack0_posdef.isHermitian
    have hslack0_mem :
        (slack0M : Mₙ) ∈ selfAdjointMatricesSubmodule 1 := by
      rwa [RealSymmetricMatrixSpace.mem_iff_isSymm]
    let S0 : SymmMat := ⟨slack0M, hslack0_mem⟩
    let U : Set (SymmMat × ℝ) :=
      {p | S0 - p.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧ c0 < p.2}
    have hU_open : IsOpen U := by
      have hstrict_open : IsOpen (𝕊^n₊₊ : Set SymmMat) := by
        exact (isOpen_interior : IsOpen (interior (𝕊^n₊ : Set SymmMat)))
      have hmatrix_open :
          IsOpen ((fun p : SymmMat × ℝ ↦ S0 - p.1) ⁻¹' (𝕊^n₊₊ : Set SymmMat)) :=
        hstrict_open.preimage (continuous_const.sub continuous_fst)
      have hscalar_open :
          IsOpen ((fun p : SymmMat × ℝ ↦ p.2) ⁻¹' Set.Ioi c0) :=
        isOpen_Ioi.preimage continuous_snd
      simpa [U, Set.preimage, Set.setOf_and] using hmatrix_open.inter hscalar_open
    have hU_subset : U ⊆ inverseDiagonalValueRegion L := by
      intro p hp
      rcases hp with ⟨hp_mat, hp_cost⟩
      have hp_psd : S0 - p.1 ∈ (𝕊^n₊ : Set SymmMat) := interior_subset hp_mat
      have hp_le :
          ((p.1 : SymmMat) : Mₙ) ≤ (S0 : Mₙ) := by
        rw [mem_positiveSemidefiniteCone_iff] at hp_psd
        exact sub_nonneg.mp <| by
          simpa using (Matrix.nonneg_iff_posSemidef).mpr hp_psd
      refine ⟨u0, hu0_pos, ?_, hp_cost.le⟩
      simpa [S0, slack0M] using hp_le
    have hp0_memU : ((0 : SymmMat), c0 + 1) ∈ U := by
      refine ⟨?_, by simp [c0]⟩
      simpa [U, S0] using
        (mem_strictPositiveSemidefiniteCone_of_posDef hslack0_posdef : S0 ∈ 𝕊^n₊₊)
    exact mem_interior_iff_mem_nhds.2 <| Filter.mem_of_superset
      (hU_open.mem_nhds hp0_memU) hU_subset
  have ha_ne : a ≠ 0 := by
    -- If `a = 0`, then the separator vanishes on a whole ball around the explicit interior point
    -- `((0), c0 + 1)`, forcing the separating functional itself to be zero.
    intro ha_zero
    have hf_xα_zero : f xα = 0 := by
      rw [hf_eval, ha_zero]
      simp [xα]
    have hf_p0_zero : f ((0 : SymmMat), c0 + 1) = 0 := by
      rw [hf_eval, ha_zero]
      simp
    have hf_zero_eval : ∀ v : SymmMat × ℝ, f v = 0 := by
      intro v
      let γ : ℝ → SymmMat × ℝ := fun t ↦ ((0 : SymmMat), c0 + 1) + t • v
      have hγ_cont : Continuous γ := by
        exact continuous_const.add (continuous_id.smul continuous_const)
      have hpre :
          {t : ℝ | γ t ∈ interior (inverseDiagonalValueRegion L)} ∈ nhds (0 : ℝ) := by
        have hγ0_mem : γ 0 ∈ interior (inverseDiagonalValueRegion L) := by
          simpa [γ] using hp0_int
        exact hγ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hγ0_mem)
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
      let t : ℝ := ε / (2 * (‖v‖ + 1))
      have ht_pos : 0 < t := by
        dsimp [t]
        positivity
      have ht_lt : t < ε := by
        dsimp [t]
        have hden_pos : 0 < 2 * (‖v‖ + 1) := by positivity
        rw [div_lt_iff₀ hden_pos]
        nlinarith [norm_nonneg v, hε_pos]
      have hplus_mem :
          ((0 : SymmMat), c0 + 1) + t • v ∈ inverseDiagonalValueRegion L := by
        exact interior_subset <| hε_sub <| by
          rw [Metric.mem_ball, Real.dist_eq]
          simpa [abs_of_nonneg ht_pos.le] using ht_lt
      have hminus_mem :
          ((0 : SymmMat), c0 + 1) - t • v ∈ inverseDiagonalValueRegion L := by
        exact interior_subset <| by
          have hball_mem : -t ∈ Metric.ball (0 : ℝ) ε := by
            rw [Metric.mem_ball, Real.dist_eq]
            have hneg_t : -t < 0 := by linarith
            simpa [abs_of_neg hneg_t] using ht_lt
          simpa [γ, sub_eq_add_neg] using hε_sub hball_mem
      have hplus_le : f (((0 : SymmMat), c0 + 1) + t • v) ≤ 0 := by
        have hplus_raw : f (((0 : SymmMat), c0 + 1) + t • v) ≤ f xα := hf_sep_raw _ hplus_mem
        rw [hf_xα_zero] at hplus_raw
        exact hplus_raw
      have hminus_le : f (((0 : SymmMat), c0 + 1) - t • v) ≤ 0 := by
        have hminus_raw : f (((0 : SymmMat), c0 + 1) - t • v) ≤ f xα := hf_sep_raw _ hminus_mem
        rw [hf_xα_zero] at hminus_raw
        exact hminus_raw
      have hplus_eq :
          f (((0 : SymmMat), c0 + 1) + t • v) = t * f v := by
        rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, hf_p0_zero]
        ring
      have hminus_eq :
          f (((0 : SymmMat), c0 + 1) - t • v) = -t * f v := by
        rw [sub_eq_add_neg, ContinuousLinearMap.map_add, ContinuousLinearMap.map_neg,
          ContinuousLinearMap.map_smul, hf_p0_zero]
        ring
      rw [hplus_eq] at hplus_le
      rw [hminus_eq] at hminus_le
      have htv_nonpos : t * f v ≤ 0 := hplus_le
      have htv_nonneg : 0 ≤ t * f v := by linarith
      have htv_zero : t * f v = 0 := le_antisymm htv_nonpos htv_nonneg
      exact (mul_eq_zero.mp htv_zero).resolve_left ht_pos.ne'
    have hf_zero : f = 0 := by
      exact ContinuousLinearMap.ext fun v ↦ hf_zero_eval v
    exact hf_ne hf_zero
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg ha_ne.symm
  let Y : SymmMat := a⁻¹ • Z
  have hY_psd : Y ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff] at hZ_psd ⊢
    simpa [Y] using hZ_psd.smul (inv_nonneg.mpr ha_nonneg)
  have hα_le_dualSlice : α ≤ psdDualSlice L Y := by
    have hZ_eq : Z = a • Y := by
      dsimp [Y]
      rw [smul_smul]
      simp [ha_ne]
    exact separatorBound_le_psdDualSlice L ha_pos hZ_eq hf_sep
  exact
    hα_le_dualSlice.trans <|
      le_csSup hDualImageBddAbove ⟨Y, hY_psd, rfl⟩

/-- Helper for Lemma 7.15: a nonzero PSD multiplier becomes semidefinite-feasible after
normalizing by its trace. -/
private theorem trace_normalized_mem_factorizationSemidefiniteFeasibleSet
    (Y : SymmMat) (hY : Y ∈ 𝕊^n₊) (hY_ne : Y ≠ 0) :
    (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) ∈ factorizationSemidefiniteFeasibleSet := by
  have hYpsd : (Y : Mₙ).PosSemidef := by
    rw [mem_positiveSemidefiniteCone_iff] at hY
    exact hY
  have htrace_nonneg : 0 ≤ Matrix.trace (Y : Mₙ) :=
    Matrix.PosSemidef.trace_nonneg hYpsd
  have htrace_ne : Matrix.trace (Y : Mₙ) ≠ 0 := by
    intro htrace_zero
    apply hY_ne
    apply Subtype.ext
    exact (Matrix.PosSemidef.trace_eq_zero_iff hYpsd).1 htrace_zero
  -- Trace normalization preserves PSD and forces the trace constraint to become `1`.
  rw [mem_factorizationSemidefiniteFeasibleSet_iff]
  refine ⟨?_, ?_⟩
  · simpa using hYpsd.smul (inv_nonneg.mpr htrace_nonneg)
  · simp [Matrix.trace_smul, htrace_ne]

/-- Helper for Lemma 7.15: the PSD dual slice vanishes at the zero multiplier. -/
private theorem psdDualSlice_zero
    (L : Mₙ) :
    psdDualSlice L (0 : SymmMat) = 0 := by
  -- Specialize the fixed-multiplier evaluation theorem to the zero PSD multiplier.
  have hzero_psd : (0 : SymmMat) ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff]
    simpa using (Matrix.PosSemidef.zero : (0 : Mₙ).PosSemidef)
  calc
    psdDualSlice L (0 : SymmMat)
        = 2 * ∑ i : Fin n, Real.sqrt ((((0 : SymmMat) : Mₙ).toQuadraticMap') (Lᵀ i)) -
            Matrix.trace ((0 : SymmMat) : Mₙ) := by
              simpa using
                inverse_diagonal_psd_dualSlice_eq_sum_sqrt_sub_trace L (0 : SymmMat) hzero_psd
    _ = 0 := by
          have hsum_zero :
              ∑ i : Fin n, Real.sqrt ((((0 : SymmMat) : Mₙ).toQuadraticMap') (Lᵀ i)) = 0 := by
            refine Finset.sum_eq_zero fun i _ ↦ ?_
            simp [Matrix.toQuadraticMap']
          rw [hsum_zero]
          simp

/-- Helper for Lemma 7.15: a nonzero PSD multiplier is dominated by the objective of its
trace-normalized trace-one representative. -/
private theorem psdDualSlice_le_trace_normalized_objective
    (L : Mₙ) (Y : SymmMat) (hY : Y ∈ 𝕊^n₊) (hY_ne : Y ≠ 0) :
    psdDualSlice L Y ≤
      factorizationSemidefiniteObjective L
        (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) := by
  have hYpsd : (Y : Mₙ).PosSemidef := by
    rw [mem_positiveSemidefiniteCone_iff] at hY
    exact hY
  have htrace_nonneg : 0 ≤ Matrix.trace (Y : Mₙ) :=
    Matrix.PosSemidef.trace_nonneg hYpsd
  have htrace_ne : Matrix.trace (Y : Mₙ) ≠ 0 := by
    intro htrace_zero
    apply hY_ne
    apply Subtype.ext
    exact (Matrix.PosSemidef.trace_eq_zero_iff hYpsd).1 htrace_zero
  let X : SymmMat := (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat)
  have hX : X ∈ factorizationSemidefiniteFeasibleSet := by
    -- Normalize the nonzero PSD multiplier to the trace-one feasible slice once and reuse it.
    simpa [X] using trace_normalized_mem_factorizationSemidefiniteFeasibleSet Y hY hY_ne
  let s : ℝ := ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))
  have hs_nonneg : 0 ≤ s := by
    -- The normalized PSD multiplier keeps every columnwise quadratic term nonnegative.
    dsimp [s]
    exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt (Matrix.trace (Y : Mₙ)) ^ (2 : ℕ) = Matrix.trace (Y : Mₙ) := by
    simpa [pow_two] using Real.sq_sqrt htrace_nonneg
  have hcompleted_square :
      2 * Real.sqrt (Matrix.trace (Y : Mₙ)) * s - Matrix.trace (Y : Mₙ) ≤ s ^ (2 : ℕ) := by
    -- The trace-normalized ray formula is bounded by its maximizer through one completed square.
    have hsq_nonneg : 0 ≤ (Real.sqrt (Matrix.trace (Y : Mₙ)) - s) ^ (2 : ℕ) := by
      exact sq_nonneg _
    nlinarith
  have hY_eq : Y = (Matrix.trace (Y : Mₙ)) • X := by
    -- Undo the trace normalization to recover the original multiplier.
    dsimp [X]
    rw [smul_smul]
    simp [htrace_ne]
  have hslice_eq :
      psdDualSlice L Y = psdDualSlice L ((Matrix.trace (Y : Mₙ)) • X) := by
    exact congrArg (psdDualSlice L) hY_eq
  calc
    psdDualSlice L Y
        = psdDualSlice L ((Matrix.trace (Y : Mₙ)) • X) := hslice_eq
    _ = 2 * Real.sqrt (Matrix.trace (Y : Mₙ)) * s - Matrix.trace (Y : Mₙ) := by
          simpa [X, s] using
            dualSlice_smul_trace_one_eq_ray_formula L X hX htrace_nonneg
    _ ≤ s ^ (2 : ℕ) := hcompleted_square
    _ = factorizationSemidefiniteObjective L X := by
          rfl
    _ = factorizationSemidefiniteObjective L
          (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) := by
          rfl

/-- Helper for Lemma 7.15: every semidefinite-feasible matrix already satisfies the inverse-side
weak-duality bound against the diagonal relaxation value. -/
private theorem factorizationSemidefiniteObjective_le_diagonalInverseRelaxationValue
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L)
    (X : SymmMat) (hX : X ∈ factorizationSemidefiniteFeasibleSet) :
    factorizationSemidefiniteObjective L X ≤
      factorizationDiagonalInverseRelaxationValue A := by
  -- Package the feasible-pair weak-duality estimate into the `sInf` defining the primal value.
  rw [factorizationDiagonalInverseRelaxationValue_eq_sInf]
  refine le_csInf ?_ ?_
  · exact Set.Nonempty.image _ (factorizationDiagonalInverseFeasibleSet_nonempty A)
  · rintro _ ⟨u, hu, rfl⟩
    exact factorization_objective_le_inverse_diagonal_sum_of_feasible_pair A L hA X u hX hu

/-- Helper for Lemma 7.15: once both feasible sets are known to be nonempty, the pointwise
feasible-pair inequality packages into the order-level weak-duality inequality. -/
private theorem factorizationSemidefiniteRelaxationValue_le_diagonalInverseRelaxationValue
    (hn : 0 < n)
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) :
    factorizationSemidefiniteRelaxationValue L ≤
      factorizationDiagonalInverseRelaxationValue A := by
  rw [factorizationSemidefiniteRelaxationValue_eq_sSup]
  rw [factorizationDiagonalInverseRelaxationValue_eq_sInf]
  refine csSup_le ?_ ?_
  · -- Positive dimension gives a trace-one PSD witness, so the `sSup` image is nonempty.
    exact Set.Nonempty.image _ (factorizationSemidefiniteFeasibleSet_nonempty hn)
  · rintro _ ⟨X, hX, rfl⟩
    refine le_csInf ?_ ?_
    · -- Positive definiteness of `A` provides a constant diagonal point below `A⁻¹`.
      exact Set.Nonempty.image _ (factorizationDiagonalInverseFeasibleSet_nonempty A)
    · rintro _ ⟨u, hu, rfl⟩
      exact factorization_objective_le_inverse_diagonal_sum_of_feasible_pair A L hA X u hX hu

-- Proof sketch: start from the inverse-diagonal formulation of `ψ⋆`, form the Lagrange dual with
-- a positive-semidefinite multiplier, maximize along a fixed ray to obtain the quadratic-root
-- objective, and then apply the change of variables `X = L^{-T} Y L^{-1}` using
-- `A = Lᵀ L`.
/-- Lemma 7.15: if `A = Lᵀ L`, then the value
`ψ⋆ = inf {∑ᵢ uᵢ⁻¹ | diag(u) ≤ A⁻¹, uᵢ > 0}` admits the semidefinite representation
`sup {([∑ᵢ √(qᵢᵀ X qᵢ)]^2) | X ⪰ 0, trace X = 1}`, where `qᵢ` are the columns of `L`. -/
theorem factorizationDiagonalInverseRelaxationValue_eq_semidefiniteRelaxationValue
    (A : 𝕊^n₊₊) (L : Mₙ) (hA : ((A : SymmMat) : Mₙ) = Lᵀ * L) :
    factorizationDiagonalInverseRelaxationValue A =
      factorizationSemidefiniteRelaxationValue L := by
  by_cases hn : n = 0
  · -- In zero dimension the diagonal image is `{0}` and the semidefinite feasible set is empty,
    -- so both relaxation values simplify directly to `0`.
    subst hn
    simp [factorizationDiagonalInverseRelaxationValue, factorizationDiagonalInverseFeasibleSet,
      factorizationSemidefiniteRelaxationValue, factorizationSemidefiniteObjective,
      factorizationSemidefiniteFeasibleSet]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    refine le_antisymm ?_ ?_
    · -- Route correction: the stale strict-simplex minimax scaffold has been removed. The source
      -- proof is now reduced to the PSD dual route: first bound every PSD multiplier by the
      -- trace-normalized trace-one slice, then recover the reverse inequality from the separated
      -- primal value region supplied by the strict feasible point.
      have hDualZero : psdDualSlice L (0 : SymmMat) = 0 := psdDualSlice_zero L
      have hPrimalNonneg : 0 ≤ factorizationSemidefiniteRelaxationValue L := by
        simpa using factorizationSemidefiniteRelaxationValue_nonneg L
      have hNormalize :
          ∀ {Y : SymmMat}, Y ∈ 𝕊^n₊ → Y ≠ 0 →
            psdDualSlice L Y ≤
              factorizationSemidefiniteObjective L
                (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) := by
        intro Y hY hY_ne
        exact psdDualSlice_le_trace_normalized_objective L Y hY hY_ne
      have hObjectiveImageBddAbove :
          BddAbove
            (factorizationSemidefiniteObjective L '' factorizationSemidefiniteFeasibleSet) := by
        refine ⟨factorizationDiagonalInverseRelaxationValue A, ?_⟩
        rintro _ ⟨X, hX, rfl⟩
        exact
          factorizationSemidefiniteObjective_le_diagonalInverseRelaxationValue A L hA X hX
      have hDualImageBddAbove :
          BddAbove (psdDualSlice L '' {Y : SymmMat | Y ∈ 𝕊^n₊}) := by
        refine ⟨factorizationSemidefiniteRelaxationValue L, ?_⟩
        rintro _ ⟨Y, hY, rfl⟩
        by_cases hY_ne : Y = 0
        · rw [hY_ne, hDualZero]
          exact hPrimalNonneg
        · have hX :
              (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) ∈
                factorizationSemidefiniteFeasibleSet := by
            exact trace_normalized_mem_factorizationSemidefiniteFeasibleSet Y hY hY_ne
          have hobj_le :
              factorizationSemidefiniteObjective L
                  (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) ≤
                factorizationSemidefiniteRelaxationValue L := by
            exact le_csSup hObjectiveImageBddAbove ⟨_, hX, rfl⟩
          exact (hNormalize hY hY_ne).trans hobj_le
      have hDualLeSemidefinite :
          psdDualSup L ≤ factorizationSemidefiniteRelaxationValue L := by
        -- Package the fixed-multiplier normalization into the global `sSup` over PSD multipliers.
        rw [psdDualSup]
        refine csSup_le ?_ ?_
        · refine Set.Nonempty.image _ ?_
          refine ⟨0, ?_⟩
          change (0 : SymmMat) ∈ 𝕊^n₊
          rw [mem_positiveSemidefiniteCone_iff]
          simpa using (Matrix.PosSemidef.zero : (0 : Mₙ).PosSemidef)
        · rintro _ ⟨Y, hY, rfl⟩
          by_cases hY_ne : Y = 0
          · rw [hY_ne, hDualZero]
            exact hPrimalNonneg
          · have hX :
                (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) ∈
                  factorizationSemidefiniteFeasibleSet := by
              exact trace_normalized_mem_factorizationSemidefiniteFeasibleSet Y hY hY_ne
            have hobj_le :
                factorizationSemidefiniteObjective L
                    (((Matrix.trace (Y : Mₙ))⁻¹) • Y : SymmMat) ≤
                  factorizationSemidefiniteRelaxationValue L := by
              exact le_csSup hObjectiveImageBddAbove ⟨_, hX, rfl⟩
            exact (hNormalize hY hY_ne).trans hobj_le
      have hSemidefiniteLeDual :
          factorizationSemidefiniteRelaxationValue L ≤ psdDualSup L := by
        -- Every trace-one PSD feasible matrix contributes a whole PSD ray inside the dual
        -- supremum, so the semidefinite objective is already dominated by `psdDualSup`.
        rw [factorizationSemidefiniteRelaxationValue_eq_sSup]
        refine csSup_le ?_ ?_
        · exact Set.Nonempty.image _ (factorizationSemidefiniteFeasibleSet_nonempty hn_pos)
        · rintro _ ⟨X, hX, rfl⟩
          have hRayNonempty :
              (((fun t : ℝ ↦ psdDualSlice L (t • X)) '' Set.Ici 0) : Set ℝ).Nonempty := by
            exact ⟨psdDualSlice L (0 • X), ⟨0, by simp, rfl⟩⟩
          have hRayLe :
              sSup ((fun t : ℝ ↦ psdDualSlice L (t • X)) '' Set.Ici 0) ≤ psdDualSup L := by
            refine csSup_le hRayNonempty ?_
            rintro _ ⟨t, ht, rfl⟩
            have hsmul_psd : (t • X : SymmMat) ∈ 𝕊^n₊ := by
              rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
              rw [mem_positiveSemidefiniteCone_iff]
              simpa using hX.1.smul ht
            exact le_csSup hDualImageBddAbove ⟨t • X, hsmul_psd, rfl⟩
          calc
            factorizationSemidefiniteObjective L X
                = sSup ((fun t : ℝ ↦ psdDualSlice L (t • X)) '' Set.Ici 0) := by
                    symm
                    exact ray_sup_dualSlice_eq_factorization_objective L X hX
            _ ≤ psdDualSup L := hRayLe
      have hDualEqSemidefinite :
          psdDualSup L = factorizationSemidefiniteRelaxationValue L :=
        le_antisymm hDualLeSemidefinite hSemidefiniteLeDual
      have hReverse :
          factorizationDiagonalInverseRelaxationValue A ≤ psdDualSup L := by
        -- The only genuinely new step is the Slater/separation bridge from the primal value
        -- region to the PSD multiplier supremum.
        exact inverse_diagonal_value_le_psdDualSup_of_slater A L hA hDualImageBddAbove
      calc
        factorizationDiagonalInverseRelaxationValue A ≤ psdDualSup L := hReverse
        _ = factorizationSemidefiniteRelaxationValue L := hDualEqSemidefinite
    · -- The forward weak-duality direction is now fully packaged from the feasible-pair bound.
      simpa using
        factorizationSemidefiniteRelaxationValue_le_diagonalInverseRelaxationValue
          hn_pos A L hA
