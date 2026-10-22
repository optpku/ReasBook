/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_42
import Mathlib.Analysis.Convex.Birkhoff

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open PositiveSemidefiniteCone
open scoped BigOperators MatrixOrder NNReal RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/- Lemma 6.14 lies in the chapter's symmetric-matrix/Frobenius spectral-calculus domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the established owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊`, `PositiveSemidefiniteCone.nnrpow`, and the induced notation `X ^ p` on
  `𝕊^n₊` in `Definition_5_4_4_3`, the established positive-semidefinite owner and its intrinsic
  nonnegative-power bridge;
- Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the established
  Frobenius owner `⟪·, ·⟫_F` on `𝕊^n`;
- mathlib `CFC.nnrpow`, the canonical ambient nonnegative-spectrum functional-calculus power.

Best owner abstraction:
- source-facing: the symmetric-matrix/Frobenius inequality of Lemma 6.14;
- core/canonical: the chapter carriers `𝕊^n`, `𝕊^n₊`, and `⟪·, ·⟫_F`;
- bridge/view: the ambient matrix real-power operation on a positive-semidefinite symmetric
  matrix, viewed back in `𝕊^n`.

Primitive data:
- nonnegative exponents `p q : ℝ≥0`;
- a positive-semidefinite symmetric matrix `X : 𝕊^n₊`;
- a symmetric direction `H : 𝕊^n`.

Derived API:
- the source-facing PSD power notation `X ^ p` on `𝕊^n₊`;
- the symmetric square `H ^ 2`.

Source/core/bridge triage:
- source-facing: Lemma 6.14 itself on symmetric matrices and the Frobenius pairing;
- core/canonical: `𝕊^n`, `𝕊^n₊`, `X ^ p` on `𝕊^n₊`, `⟪·, ·⟫_F`, and intrinsic eigenvalues on
  `𝕊^n`;
- bridge/view: the coercion from `𝕊^n₊` to `𝕊^n` and then to ambient matrices.

The refinement below reuses the chapter owner `X ^ p` on the intrinsic cone subtype `X : 𝕊^n₊`,
keeps the source-facing inequality on the single mixed trace term that appears in Proposition 6.33,
and does not export a separate owner for a one-off symmetrized package.
-/

-- Proof sketch: diagonalize the positive-semidefinite symmetric matrix `X` orthogonally, compare
-- the mixed power term entrywise using `a^p b^q ≤ a^(p+q)` on the nonnegative eigenvalues of `X`,
-- rewrite the resulting trace as the Frobenius pairing with `X^(p+q)` and
-- `H^2`, and then apply von Neumann's trace inequality to the positive semidefinite matrices
-- `X^(p+q)` and `H^2`.
/-- Helper for Lemma 6.14: the intrinsic square `H ^ 2` is positive semidefinite because, for a
real symmetric matrix, the ambient square is `H * Hᵀ`. -/
theorem square_posSemidef
    (H : SymmMat) :
    (((H ^ (2 : ℕ) : SymmMat) : Mat)).PosSemidef := by
  -- Rewrite the intrinsic square back to the ambient matrix square and use the standard
  -- `AAᵀ` positive-semidefinite fact.
  have hH_transpose : (H : Mat)ᵀ = (H : Mat) := (isSymm H).eq
  simpa [RealSymmetricMatrixSpace.coe_pow, pow_two, hH_transpose] using
    Matrix.posSemidef_self_mul_conjTranspose (H : Mat)

/-- Helper for Lemma 6.14: the positive-semidefinite power `X ^ (p + q)` remains positive
semidefinite when viewed in the ambient matrix space. -/
theorem power_posSemidef
    (p q : ℝ≥0) (X : 𝕊^n₊) :
    ((((X ^ (p + q) : 𝕊^n₊) : SymmMat) : Mat)).PosSemidef :=
  (X ^ (p + q)).2

/-- Helper for Lemma 6.14: the project-specific nonunital PSD power satisfies `X ^ 0 = 0` after
coercing back to ambient matrices. -/
theorem zero_psdPower_matrix
    (X : 𝕊^n₊) :
    ((((X ^ (0 : ℝ≥0) : 𝕊^n₊) : SymmMat) : Mat)) = 0 := by
  -- The PSD cone power is ambient `CFC.nnrpow`, so the project-specific boundary case is the
  -- ambient `nnrpow_zero` identity seen through the coercions.
  rw [PositiveSemidefiniteCone.coe_pow]
  exact CFC.nnrpow_zero

/-- Helper for Lemma 6.14: pairing a positive-semidefinite power of `X` with the intrinsic square
`H ^ 2` is nonnegative. -/
theorem power_pairing_nonneg
    (r : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    0 ≤ ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
  rcases eq_zero_or_pos r with rfl | hr
  · -- The chapter's nonunital power sends exponent `0` to the zero matrix, so the pairing vanishes.
    have hzero : ⟪(X ^ (0 : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F = 0 := by
      rw [RealSymmetricMatrixSpace.frobeniusInner_def]
      rw [zero_psdPower_matrix X]
      simp
    rw [hzero]
  · let Y : Mat := ((((X ^ (r / 2) : 𝕊^n₊) : SymmMat) : Mat))
    have hr_half : 0 < r / 2 := by
      exact div_pos hr (by positivity)
    have hsplit : r / 2 + r / 2 = r := by
      exact_mod_cast (show (r : ℝ) / 2 + (r : ℝ) / 2 = (r : ℝ) by ring)
    have hY_transpose : Yᵀ = Y := by
      -- The half-power remains symmetric because it still lives in the symmetric cone subtype.
      simpa [Y] using (isSymm (((X ^ (r / 2) : 𝕊^n₊) : SymmMat))).eq
    have hpow :
        ((((X ^ r : 𝕊^n₊) : SymmMat) : Mat)) = Y * Y := by
      -- Split the exponent as `r / 2 + r / 2` and recombine it with the CFC power law.
      calc
        ((((X ^ r : 𝕊^n₊) : SymmMat) : Mat))
            = ((((X ^ (r / 2 + r / 2) : 𝕊^n₊) : SymmMat) : Mat)) := by rw [hsplit]
        _ = (((X : SymmMat) : Mat) ^ (r / 2 + r / 2)) := by
              simpa using (PositiveSemidefiniteCone.coe_pow X (r / 2 + r / 2))
        _ = (((X : SymmMat) : Mat) ^ (r / 2)) * (((X : SymmMat) : Mat) ^ (r / 2)) := by
              rw [CFC.nnrpow_add hr_half hr_half]
        _ = Y * Y := by
              rfl
    have htrace :
        ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F =
          Matrix.trace ((((H : Mat) * Y)ᵀ) * ((H : Mat) * Y)) := by
      -- Rewrite the Frobenius pairing as a trace, factor `X ^ r` as `Y * Y`, and package the
      -- result as the trace of a transpose-times-itself square.
      calc
        ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
            = Matrix.trace
                ((((((X ^ r : 𝕊^n₊) : SymmMat) : Mat)ᵀ) *
                    (((H ^ (2 : ℕ) : SymmMat) : Mat)))) := by
                  rw [RealSymmetricMatrixSpace.frobeniusInner_def]
        _ = Matrix.trace
              (((((X ^ r : 𝕊^n₊) : SymmMat) : Mat)) *
                ((H : Mat) * (H : Mat))) := by
              rw [(isSymm (((X ^ r : 𝕊^n₊) : SymmMat))).eq]
              simp [pow_two]
        _ = Matrix.trace ((Y * Y) * ((H : Mat) * (H : Mat))) := by
              rw [hpow]
        _ = Matrix.trace (Y * (((H : Mat) * (H : Mat)) * Y)) := by
              calc
                Matrix.trace ((Y * Y) * ((H : Mat) * (H : Mat)))
                    = Matrix.trace (((H : Mat) * (H : Mat)) * (Y * Y)) := by
                        simpa [Matrix.mul_assoc] using
                          Matrix.trace_mul_comm (Y * Y) ((H : Mat) * (H : Mat))
                _ = Matrix.trace (((H : Mat) * (H : Mat)) * Y * Y) := by
                      simp [Matrix.mul_assoc]
                _ = Matrix.trace (Y * (((H : Mat) * (H : Mat)) * Y)) := by
                      simpa [Matrix.mul_assoc] using
                        Matrix.trace_mul_cycle ((H : Mat) * (H : Mat)) Y Y
        _ = Matrix.trace ((((H : Mat) * Y)ᵀ) * ((H : Mat) * Y)) := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc, hY_transpose, (isSymm H).eq]
    have htrace_nonneg :
        0 ≤ Matrix.trace ((((H : Mat) * Y)ᵀ) * ((H : Mat) * Y)) := by
      -- A transpose-times-itself product is positive semidefinite, hence its trace is nonnegative.
      simpa using
        Matrix.PosSemidef.trace_nonneg
          (Matrix.posSemidef_conjTranspose_mul_self ((H : Mat) * Y))
    rw [htrace]
    exact htrace_nonneg

/-- Helper for Lemma 6.14: the scalar eigenvalue weights satisfy the paired power inequality used
after the spectral rewrite of the mixed trace term. -/
theorem mixed_rpow_scalar_le_sum_of_powers
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p q : ℝ≥0) :
    a ^ (p : ℝ) * b ^ (q : ℝ) + a ^ (q : ℝ) * b ^ (p : ℝ)
      ≤ a ^ ((p + q : ℝ≥0) : ℝ) + b ^ ((p + q : ℝ≥0) : ℝ) := by
  -- First prove the ordered branch `a ≤ b`; the other branch follows by swapping the scalars.
  have hordered :
      ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ≤ y →
        x ^ (p : ℝ) * y ^ (q : ℝ) + x ^ (q : ℝ) * y ^ (p : ℝ)
          ≤ x ^ ((p + q : ℝ≥0) : ℝ) + y ^ ((p + q : ℝ≥0) : ℝ) := by
    intro x y hx hy hxy
    -- Monotonicity of `rpow` makes the two scalar differences nonnegative.
    have hxp : x ^ (p : ℝ) ≤ y ^ (p : ℝ) :=
      Real.rpow_le_rpow hx hxy p.2
    have hxq : x ^ (q : ℝ) ≤ y ^ (q : ℝ) :=
      Real.rpow_le_rpow hx hxy q.2
    have hnonneg :
        0 ≤ (y ^ (p : ℝ) - x ^ (p : ℝ)) * (y ^ (q : ℝ) - x ^ (q : ℝ)) := by
      exact mul_nonneg (sub_nonneg.mpr hxp) (sub_nonneg.mpr hxq)
    -- Expanding that nonnegative product gives exactly the desired rearrangement inequality.
    have hxpq : x ^ ((p + q : ℝ≥0) : ℝ) = x ^ (p : ℝ) * x ^ (q : ℝ) := by
      simpa using (Real.rpow_add_of_nonneg hx p.2 q.2)
    have hypq : y ^ ((p + q : ℝ≥0) : ℝ) = y ^ (p : ℝ) * y ^ (q : ℝ) := by
      simpa using (Real.rpow_add_of_nonneg hy p.2 q.2)
    nlinarith [hnonneg, hxpq, hypq]
  rcases le_total a b with hab | hba
  · exact hordered ha hb hab
  · simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hordered hb ha hba

/-- Helper for Lemma 6.14: the squared overlap matrix of two real orthogonal bases is doubly
stochastic, isolating the combinatorial input to the PSD trace-majorization step. -/
theorem squared_overlap_matrix_mem_doubly_stochastic
    (UA UB : Matrix.unitaryGroup (Fin n) ℝ) :
    (fun i j : Fin n ↦ ((star (UA : Mat) * (UB : Mat)) i j) ^ (2 : ℕ) : Mat) ∈
      doublyStochastic ℝ (Fin n) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := UA⁻¹ * UB
  have hU : (U : Mat) = star (UA : Mat) * (UB : Mat) := by
    rfl
  have hU_mul_star : (U : Mat) * star (U : Mat) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hU_star_mul : star (U : Mat) * (U : Mat) = 1 := by
    exact Unitary.coe_star_mul_self U
  -- The overlap matrix has nonnegative entries and row/column sums equal to the diagonal of the
  -- unitary identities for `U`.
  simpa [hU] using
    (show (fun i j : Fin n ↦ ((U : Mat) i j) ^ (2 : ℕ) : Mat) ∈
        doublyStochastic ℝ (Fin n) from by
      refine (mem_doublyStochastic_iff_sum
        (M := (fun i j : Fin n ↦ ((U : Mat) i j) ^ (2 : ℕ) : Mat))).2 ?_
      constructor
      · intro i j
        positivity
      · constructor
        · intro i
          calc
            ∑ j : Fin n, ((U : Mat) i j) ^ (2 : ℕ)
                = ∑ j : Fin n, (U : Mat) i j * star ((U : Mat) i j) := by
                    simp [pow_two]
            _ = ((U : Mat) * star (U : Mat)) i i := by
                  simp [Matrix.mul_apply]
            _ = 1 := by
                  simpa only [Matrix.one_apply] using
                    congrArg (fun M : Mat ↦ M i i) hU_mul_star
        · intro j
          calc
            ∑ i : Fin n, ((U : Mat) i j) ^ (2 : ℕ)
                = ∑ i : Fin n, star ((U : Mat) i j) * (U : Mat) i j := by
                    simp [pow_two]
            _ = (star (U : Mat) * (U : Mat)) j j := by
                  simp [Matrix.mul_apply]
            _ = 1 := by
                  simpa only [Matrix.one_apply] using
                    congrArg (fun M : Mat ↦ M j j) hU_star_mul)

/-- Helper for Lemma 6.14: a permutation pairing is maximal at the identity when both weight lists
are antitone. -/
theorem permPairing_le_identity_of_antitone
    {α β : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hα : Antitone α) (hβ : Antitone β) :
    (∑ i : Fin n, α i * β (σ i)) ≤ ∑ i : Fin n, α i * β i := by
  -- The rearrangement inequality in mathlib is packaged as a monovary estimate on permutations.
  exact Monovary.sum_mul_comp_perm_le_sum_mul (Antitone.monovary hα hβ)

/-- Helper for Lemma 6.14: averaging permutation pairings with doubly stochastic coefficients is
still bounded by the identity pairing. -/
theorem doublyStochastic_weightedSum_le_identityPairing
    {W : Mat} {α β : Fin n → ℝ}
    (hW : W ∈ doublyStochastic ℝ (Fin n))
    (hα : Antitone α) (hβ : Antitone β) :
    (∑ i : Fin n, ∑ j : Fin n, α i * β j * W i j) ≤ ∑ i : Fin n, α i * β i := by
  obtain ⟨w, hw_nonneg, hw_sum, hwWsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hW
  have hpairing_mulVec :
      (∑ i : Fin n, ∑ j : Fin n, α i * β j * W i j) = ∑ i : Fin n, α i * (W.mulVec β) i := by
    -- Package the inner row sum as the `mulVec` action of `W` on `β`.
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, mul_comm]
  have hmulVec :
      W.mulVec β = ∑ σ : Equiv.Perm (Fin n), w σ • (β ∘ σ) := by
    -- Apply `mulVec` to the Birkhoff decomposition and simplify each permutation-matrix action.
    calc
      W.mulVec β = (∑ σ : Equiv.Perm (Fin n), w σ • (σ.permMatrix ℝ)).mulVec β := by
        rw [hwWsum]
      _ = ∑ σ : Equiv.Perm (Fin n), (w σ • (σ.permMatrix ℝ)).mulVec β := by
        simpa using
          (Matrix.sum_mulVec (s := Finset.univ) (x := fun σ : Equiv.Perm (Fin n) ↦
            w σ • (σ.permMatrix ℝ)) β)
      _ = ∑ σ : Equiv.Perm (Fin n), w σ • ((σ.permMatrix ℝ).mulVec β) := by
        refine Finset.sum_congr rfl ?_
        intro σ hσ
        rw [Matrix.smul_mulVec]
      _ = ∑ σ : Equiv.Perm (Fin n), w σ • (β ∘ σ) := by
        refine Finset.sum_congr rfl ?_
        intro σ hσ
        rw [Matrix.permMatrix_mulVec]
  have hperm_average :
      (∑ i : Fin n, α i * (W.mulVec β) i)
        = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, α i * β (σ i) := by
    -- Interchange the `i`- and `σ`-sums after expanding the `mulVec` formula from the Birkhoff
    -- decomposition.
    calc
      ∑ i : Fin n, α i * (W.mulVec β) i
          = ∑ i : Fin n, α i * ((∑ σ : Equiv.Perm (Fin n), w σ • (β ∘ σ)) i) := by
              rw [hmulVec]
      _ = ∑ i : Fin n, α i * (∑ σ : Equiv.Perm (Fin n), w σ * β (σ i)) := by
            simp [Pi.smul_apply]
      _ = ∑ i : Fin n, ∑ σ : Equiv.Perm (Fin n), α i * (w σ * β (σ i)) := by
              simp [Finset.mul_sum]
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, α i * (w σ * β (σ i)) := by
            rw [Finset.sum_comm]
      _ = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, α i * β (σ i) := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            calc
              ∑ i : Fin n, α i * (w σ * β (σ i))
                  = ∑ i : Fin n, w σ * (α i * β (σ i)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = w σ * ∑ i : Fin n, α i * β (σ i) := by
                    symm
                    rw [Finset.mul_sum]
  -- Compare each permutation term with the identity pairing and then use the convex weights.
  calc
    (∑ i : Fin n, ∑ j : Fin n, α i * β j * W i j)
        = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, α i * β (σ i) := by
            rw [hpairing_mulVec, hperm_average]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, α i * β i := by
          refine Finset.sum_le_sum ?_
          intro σ hσ
          exact mul_le_mul_of_nonneg_left
            (permPairing_le_identity_of_antitone σ hα hβ)
            (hw_nonneg σ)
    _ = (∑ σ : Equiv.Perm (Fin n), w σ) * ∑ i : Fin n, α i * β i := by
          rw [Finset.sum_mul]
    _ = ∑ i : Fin n, α i * β i := by
          rw [hw_sum, one_mul]

/-- Helper for Lemma 6.14: reindexing a doubly stochastic matrix along an equivalence preserves
doubly stochasticity. -/
theorem doublyStochastic_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {W : Matrix κ κ ℝ}
    (hW : W ∈ doublyStochastic ℝ κ) :
    (fun i j ↦ W (e i) (e j) : Matrix ι ι ℝ) ∈ doublyStochastic ℝ ι := by
  rcases (mem_doublyStochastic_iff_sum (M := W)).1 hW with ⟨hnonneg, hrow, hcol⟩
  -- Reindex rows and columns through the equivalence and transport the row/column-sum axioms.
  refine
    (mem_doublyStochastic_iff_sum (M := (fun i j ↦ W (e i) (e j) : Matrix ι ι ℝ))).2 ?_
  constructor
  · intro i j
    exact hnonneg (e i) (e j)
  · constructor
    · intro i
      calc
        ∑ j, W (e i) (e j) = ∑ j' : κ, W (e i) j' := by
          simpa using (Equiv.sum_comp e (fun j' : κ ↦ W (e i) j'))
        _ = 1 := hrow (e i)
    · intro j
      calc
        ∑ i, W (e i) (e j) = ∑ i' : κ, W i' (e j) := by
          simpa using (Equiv.sum_comp e (fun i' : κ ↦ W i' (e j)))
        _ = 1 := hcol (e j)

/-- Helper for Lemma 6.14: a diagonal-weighted trace against a symmetric matrix is the weighted sum
of the squared entries of that matrix. -/
theorem diagonal_weighted_trace_eq_sumSquares
    (v w : Fin n → ℝ) (K : Mat) (hK : Kᵀ = K) :
    Matrix.trace (Matrix.diagonal v * K * Matrix.diagonal w * K)
      = ∑ i : Fin n, ∑ j : Fin n, v i * (K i j) ^ (2 : ℕ) * w j := by
  -- Convert symmetry of `K` into an entrywise rewrite so the final square is literally `K i j ^ 2`.
  have hsymm : ∀ i j : Fin n, K j i = K i j := by
    intro i j
    have hij : K i j = K j i := by
      simpa [Matrix.transpose_apply] using congrArg (fun M : Mat ↦ M j i) hK
    exact hij.symm
  -- Expand the trace into a diagonal sum, then normalize the two diagonal multiplications.
  calc
    Matrix.trace (Matrix.diagonal v * K * Matrix.diagonal w * K)
        = ∑ i : Fin n, ((Matrix.diagonal v * K * Matrix.diagonal w * K) i i) := by
            simp [Matrix.trace, Matrix.diag_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, ((Matrix.diagonal v * K * Matrix.diagonal w) i j) * K j i := by
          simp [Matrix.mul_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * K i j * w j * K j i := by
          simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * K i j * w j * K i j := by
          simp_rw [hsymm]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * (K i j) ^ (2 : ℕ) * w j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Lemma 6.14: a diagonal-weighted trace against `Kᵀ` expands as the weighted sum of
the squared entries of `K`, so the overlap matrix can be handled without symmetry assumptions. -/
theorem diagonal_weighted_trace_eq_overlapSquares
    (v w : Fin n → ℝ) (K : Mat) :
    Matrix.trace (Matrix.diagonal v * K * Matrix.diagonal w * Kᵀ)
      = ∑ i : Fin n, ∑ j : Fin n, v i * (K i j) ^ (2 : ℕ) * w j := by
  -- Expand the diagonal trace entrywise and use the transpose to expose the same matrix entry
  -- twice, which turns the overlap term into a literal square.
  calc
    Matrix.trace (Matrix.diagonal v * K * Matrix.diagonal w * Kᵀ)
        = ∑ i : Fin n, ((Matrix.diagonal v * K * Matrix.diagonal w * Kᵀ) i i) := by
            simp [Matrix.trace, Matrix.diag_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, ((Matrix.diagonal v * K * Matrix.diagonal w) i j) * Kᵀ j i := by
          simp [Matrix.mul_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * K i j * w j * Kᵀ j i := by
          simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * K i j * w j * K i j := by
          simp [Matrix.transpose_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * (K i j) ^ (2 : ℕ) * w j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Lemma 6.14: after diagonalizing two symmetric matrices, their trace pairing is the
weighted overlap sum of the squared change-of-basis coefficients. -/
theorem unitary_diagonal_pairing_eq_sum_overlapSquares
    (UA UB : Matrix.unitaryGroup (Fin n) ℝ) (v w : Fin n → ℝ) :
    Matrix.trace (((UA : Mat) * Matrix.diagonal v * star (UA : Mat)) *
        ((UB : Mat) * Matrix.diagonal w * star (UB : Mat)))
      = ∑ i : Fin n, ∑ j : Fin n, v i * (((star (UA : Mat) * (UB : Mat)) i j) ^ (2 : ℕ)) * w j := by
  let K : Mat := star (UA : Mat) * (UB : Mat)
  have hK : Kᵀ = star (UB : Mat) * (UA : Mat) := by
    -- Over `ℝ`, transposing the overlap matrix swaps the two orthogonal bases.
    ext i j
    simp [K, Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
  -- Cycle one unitary factor across the trace so only the basis overlap matrix remains.
  calc
    Matrix.trace (((UA : Mat) * Matrix.diagonal v * star (UA : Mat)) *
        ((UB : Mat) * Matrix.diagonal w * star (UB : Mat)))
        = Matrix.trace
            ((UA : Mat) * (Matrix.diagonal v * K * Matrix.diagonal w * star (UB : Mat))) := by
            simp [K, Matrix.mul_assoc]
    _ = Matrix.trace
          ((Matrix.diagonal v * K * Matrix.diagonal w * star (UB : Mat)) * (UA : Mat)) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_comm
              (UA : Mat) (Matrix.diagonal v * K * Matrix.diagonal w * star (UB : Mat)))
    _ = Matrix.trace ((Matrix.diagonal v * K * Matrix.diagonal w) * Kᵀ) := by
          simp [K, hK, Matrix.mul_assoc]
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * (K i j) ^ (2 : ℕ) * w j :=
          diagonal_weighted_trace_eq_overlapSquares v w K
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * (((star (UA : Mat) * (UB : Mat)) i j) ^ (2 : ℕ)) * w j := by
          rfl

/-- Helper for Lemma 6.14: conjugating a symmetric direction by the orthogonal eigenbasis of `X`
keeps it symmetric. -/
theorem conjugatedDirection_transpose_eq_self
    (U : Matrix.unitaryGroup (Fin n) ℝ) (H : SymmMat) :
    (star (U : Mat) * (H : Mat) * (U : Mat))ᵀ = star (U : Mat) * (H : Mat) * (U : Mat) := by
  -- Expand the transpose and use that `H` is symmetric while `star` is transpose over `ℝ`.
  rw [Matrix.transpose_mul, Matrix.transpose_mul, (isSymm H).eq]
  rw [show (U : Mat)ᵀ = star (U : Mat) by rfl]
  rw [show (star (U : Mat))ᵀ = (U : Mat) by rfl]
  simp [Matrix.mul_assoc]

/-- Helper for Lemma 6.14: undoing a unitary conjugation recovers the original ambient matrix. -/
theorem unitary_mul_conjugated_mul_star
    (U : Matrix.unitaryGroup (Fin n) ℝ) (A : Mat) :
    (U : Mat) * (star (U : Mat) * A * (U : Mat)) * star (U : Mat) = A := by
  have hU_mul_star : (U : Mat) * star (U : Mat) = 1 := by
    exact Unitary.coe_mul_star_self U
  -- Reassociate so the unitary cancellations happen at the cheapest matrix layer.
  calc
    (U : Mat) * (star (U : Mat) * A * (U : Mat)) * star (U : Mat)
        = ((U : Mat) * star (U : Mat)) * A * ((U : Mat) * star (U : Mat)) := by
            simp_rw [Matrix.mul_assoc]
    _ = (1 : Mat) * A * ((U : Mat) * star (U : Mat)) := by
          rw [hU_mul_star]
    _ = (1 : Mat) * A * (1 : Mat) := by
          rw [hU_mul_star]
    _ = A := by
          simp

/-- Helper for Lemma 6.14: conjugating an ambient matrix by a real unitary basis preserves its
trace. -/
theorem trace_unitary_conjugation
    (U : Matrix.unitaryGroup (Fin n) ℝ) (A : Mat) :
    Matrix.trace ((U : Mat) * A * star (U : Mat)) = Matrix.trace A := by
  -- Cycle the trace once so the unitary factors cancel on the left.
  calc
    Matrix.trace ((U : Mat) * A * star (U : Mat))
        = Matrix.trace (star (U : Mat) * (U : Mat) * A) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (U : Mat) A (star (U : Mat))
    _ = Matrix.trace A := by
          rw [Unitary.coe_star_mul_self]
          simp

/-- Helper for Lemma 6.14: conjugating a positive-semidefinite cone power by the eigenbasis of
`X` turns it into the diagonal matrix of the powered eigenvalues of `X`. -/
theorem conjugatedPsdPower_eq_diagonalRpow
    {r : ℝ≥0} (hr : 0 < r) (X : 𝕊^n₊) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
    star (U : Mat) * ((((X ^ r : 𝕊^n₊) : SymmMat) : Mat)) * (U : Mat) =
      Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (r : ℝ)) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
  have hX_nonneg : 0 ≤ ((X : SymmMat) : Mat) := Matrix.nonneg_iff_posSemidef.mpr X.2
  -- Rewrite the cone power as the ambient real functional calculus and then evaluate that
  -- functional calculus in the orthonormal eigenbasis of `X`.
  calc
    star (U : Mat) * ((((X ^ r : 𝕊^n₊) : SymmMat) : Mat)) * (U : Mat)
        = star (U : Mat) * (((((X : SymmMat) : Mat)) ^ (r : ℝ))) * (U : Mat) := by
            rw [PositiveSemidefiniteCone.coe_pow, CFC.nnrpow_eq_rpow hr]
    _ = star (U : Mat) *
          ((isHermitian (X : SymmMat)).cfc (fun x : ℝ ↦ x ^ (r : ℝ))) *
            (U : Mat) := by
          rw [CFC.rpow_eq_cfc_real hX_nonneg, (isHermitian (X : SymmMat)).cfc_eq]
    _ = Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (r : ℝ)) := by
          rw [Matrix.IsHermitian.cfc]
          simp_rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]
          simp [Function.comp]

/-- Helper for Lemma 6.14: the mixed trace term becomes a diagonal trace in a single eigenbasis
of `X`, with the conjugated direction matrix appearing twice. -/
theorem mixedPowerTrace_eq_diagonalWeightedTrace
    {p q : ℝ≥0} (hp : 0 < p) (hq : 0 < q) (X : 𝕊^n₊) (H : SymmMat) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
    let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat)) =
      Matrix.trace
        (Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (q : ℝ)) * K *
          Matrix.diagonal (fun j => (eigenvalues (X : SymmMat) j) ^ (p : ℝ)) * K) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
  let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
  have hleft :
      Matrix.trace
          (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat)) =
        Matrix.trace
          (((((X ^ q : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ p : 𝕊^n₊) : Mat))) * (H : Mat)) := by
    -- Remove the transpose by symmetry of `H`, `X ^ p`, and `X ^ q`.
    rw [Matrix.transpose_mul, Matrix.transpose_mul, (isSymm H).eq,
      (isSymm (((X ^ p : 𝕊^n₊) : SymmMat))).eq, (isSymm (((X ^ q : 𝕊^n₊) : SymmMat))).eq]
    simp [Matrix.mul_assoc]
  -- Conjugate the trace into the eigenbasis of `X`, where both powers become diagonal.
  have hqdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ q : 𝕊^n₊) : Mat)) =
        Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (q : ℝ)) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedPsdPower_eq_diagonalRpow hq X
  have hpdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ p : 𝕊^n₊) : Mat)) =
        Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (p : ℝ)) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedPsdPower_eq_diagonalRpow hp X
  have hHconj : ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (H : Mat) = K := by
    simp [K, U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
  rw [hleft]
  calc
    Matrix.trace (((((X ^ q : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ p : 𝕊^n₊) : Mat))) * (H : Mat))
        = Matrix.trace
            (((Unitary.conjStarAlgAut ℝ Mat) (star U))
              (((((X ^ q : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ p : 𝕊^n₊) : Mat))) *
                (H : Mat))) := by
            symm
            exact
              Matrix.trace_map
                ((Unitary.conjStarAlgAut ℝ Mat) (star U))
                (((((X ^ q : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ p : 𝕊^n₊) : Mat))) *
                  (H : Mat))
    _ = Matrix.trace
          (Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (q : ℝ)) * K *
            Matrix.diagonal (fun j => (eigenvalues (X : SymmMat) j) ^ (p : ℝ)) * K) := by
          -- Evaluate the conjugated product factorwise in the fixed eigenbasis.
          simp_rw [map_mul]
          rw [hqdiag, hpdiag]
          simp [hHconj, K, U, Matrix.mul_assoc]

/-- Helper for Lemma 6.14: the Frobenius pairing with `H²` becomes the diagonal trace with the
same conjugated direction matrix in the eigenbasis of `X`. -/
theorem powerPairing_eq_diagonalPowerTrace
    {p q : ℝ≥0} (hpq : 0 < p + q) (X : 𝕊^n₊) (H : SymmMat) :
    let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
    let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
    ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F =
      Matrix.trace
        (Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (((p + q : ℝ≥0)) : ℝ)) *
          K * K) := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
  let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
  have hpow_symm :
      (((((X ^ (p + q) : 𝕊^n₊) : SymmMat) : Mat))ᵀ) =
        ((((X ^ (p + q) : 𝕊^n₊) : SymmMat) : Mat)) := by
    simpa using (isSymm (((X ^ (p + q) : 𝕊^n₊) : SymmMat))).eq
  -- Rewrite the Frobenius pairing as an ambient trace and conjugate it into the same basis.
  have hpqdiag :
      ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (((X ^ (p + q) : 𝕊^n₊) : Mat)) =
        Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (((p + q : ℝ≥0)) : ℝ)) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using
      conjugatedPsdPower_eq_diagonalRpow hpq X
  have hHconj : ((Unitary.conjStarAlgAut ℝ Mat) (star U)) (H : Mat) = K := by
    simp [K, U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
  calc
    ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
        = Matrix.trace
            ((((X ^ (p + q) : 𝕊^n₊) : Mat) * ((H : Mat) * (H : Mat)))) := by
              rw [RealSymmetricMatrixSpace.frobeniusInner_def, hpow_symm]
              simp [RealSymmetricMatrixSpace.coe_pow, pow_two]
    _ = Matrix.trace
          (((Unitary.conjStarAlgAut ℝ Mat) (star U))
            ((((X ^ (p + q) : 𝕊^n₊) : Mat) * ((H : Mat) * (H : Mat))))) := by
          symm
          exact
            Matrix.trace_map
              ((Unitary.conjStarAlgAut ℝ Mat) (star U))
              ((((X ^ (p + q) : 𝕊^n₊) : Mat) * ((H : Mat) * (H : Mat))))
    _ = Matrix.trace
          (Matrix.diagonal (fun i => (eigenvalues (X : SymmMat) i) ^ (((p + q : ℝ≥0)) : ℝ)) *
            K * K) := by
          -- The power factor becomes diagonal, while `H²` becomes `K * K`.
          simp_rw [map_mul]
          rw [hpqdiag]
          simp [hHconj, K, U, Matrix.mul_assoc]

/-- Helper for Lemma 6.14: after rewriting in a fixed eigenbasis of `X`, the mixed weighted square
sum is bounded by the pure power-weighted square sum. -/
theorem weightedMixedSquares_le_powerSquares
    {p q : ℝ≥0} {lam : Fin n → ℝ} {K : Mat}
    (hK : Kᵀ = K) (hlam : ∀ i : Fin n, 0 ≤ lam i) :
    (∑ i : Fin n, ∑ j : Fin n, lam i ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam j ^ (p : ℝ))
      ≤
        ∑ i : Fin n, ∑ j : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) := by
  have hsymm : ∀ i j : Fin n, K j i = K i j := by
    intro i j
    have hij : K i j = K j i := by
      simpa [Matrix.transpose_apply] using congrArg (fun M : Mat ↦ M j i) hK
    exact hij.symm
  let mixedSum : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, lam i ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam j ^ (p : ℝ)
  let powerSum : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ)
  have hswapMixed :
      mixedSum =
        ∑ i : Fin n, ∑ j : Fin n, lam j ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam i ^ (p : ℝ) := by
    -- Swap the indices `(i,j)` and use symmetry of `K` to return to the original matrix entry.
    calc
      mixedSum
          = ∑ i : Fin n, ∑ j : Fin n, lam i ^ (q : ℝ) * (K j i) ^ (2 : ℕ) * lam j ^ (p : ℝ) := by
              unfold mixedSum
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hsymm j i]
      _ = ∑ j : Fin n, ∑ i : Fin n, lam i ^ (q : ℝ) * (K j i) ^ (2 : ℕ) * lam j ^ (p : ℝ) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, lam j ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam i ^ (p : ℝ) := by
            rfl
  have hswapPower :
      powerSum =
        ∑ i : Fin n, ∑ j : Fin n, lam j ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) := by
    -- The same index swap keeps the pure power-weighted square sum unchanged.
    calc
      powerSum
          = ∑ i : Fin n, ∑ j : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K j i) ^ (2 : ℕ) := by
              unfold powerSum
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [hsymm j i]
      _ = ∑ j : Fin n, ∑ i : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K j i) ^ (2 : ℕ) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, lam j ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) := by
            rfl
  have hdouble :
      mixedSum + mixedSum ≤ powerSum + powerSum := by
    -- Average the `(i,j)` and `(j,i)` scalar bounds obtained from
    -- `mixed_rpow_scalar_le_sum_of_powers`.
    calc
      mixedSum + mixedSum
          = ∑ i : Fin n, ∑ j : Fin n,
              (lam i ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam j ^ (p : ℝ) +
                lam j ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam i ^ (p : ℝ)) := by
              nth_rewrite 2 [hswapMixed]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
            (lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) +
              lam j ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ)) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            refine Finset.sum_le_sum ?_
            intro j hj
            have hsq_nonneg : 0 ≤ (K i j) ^ (2 : ℕ) := by positivity
            have hscalar :
                lam j ^ (p : ℝ) * lam i ^ (q : ℝ) + lam j ^ (q : ℝ) * lam i ^ (p : ℝ)
                  ≤ lam j ^ (((p + q : ℝ≥0)) : ℝ) + lam i ^ (((p + q : ℝ≥0)) : ℝ) :=
              mixed_rpow_scalar_le_sum_of_powers (hlam j) (hlam i) p q
            have hmul := mul_le_mul_of_nonneg_right hscalar hsq_nonneg
            simpa [mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc] using hmul
      _ = powerSum + powerSum := by
            nth_rewrite 2 [hswapPower]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← Finset.sum_add_distrib]
  -- Cancel the duplicated sums to recover the desired inequality.
  nlinarith

/-- Helper for Lemma 6.14: once the zero-exponent boundary cases are removed, the first conjunct
is the positive-exponent spectral core of the source proof. -/
theorem mixed_power_trace_le_power_pairing_positive
    {p q : ℝ≥0} (hp : 0 < p) (hq : 0 < q) (X : 𝕊^n₊) (H : SymmMat) :
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
      ≤ ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian (X : SymmMat)).eigenvectorUnitary
  let K : Mat := star (U : Mat) * (H : Mat) * (U : Mat)
  let lam : Fin n → ℝ := eigenvalues (X : SymmMat)
  have hK : Kᵀ = K := by
    -- The conjugated direction stays symmetric in the chosen eigenbasis of `X`.
    simpa [K] using conjugatedDirection_transpose_eq_self U H
  have hlam : ∀ i : Fin n, 0 ≤ lam i := by
    -- Positive semidefiniteness of `X` makes every eigenvalue nonnegative.
    intro i
    simpa [lam, RealSymmetricMatrixSpace.eigenvalues] using X.2.eigenvalues_nonneg i
  have hmixed :
      Matrix.trace
          (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat)) =
        Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (q : ℝ)) * K *
            Matrix.diagonal (fun j => lam j ^ (p : ℝ)) * K) := by
    -- Rewrite the mixed trace in the fixed eigenbasis of `X`.
    simpa [U, K, lam] using mixedPowerTrace_eq_diagonalWeightedTrace hp hq X H
  have hpair :
      ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F =
        Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ)) * K * K) := by
    -- Rewrite the Frobenius pairing in the same eigenbasis, with the same conjugated matrix `K`.
    simpa [U, K, lam] using powerPairing_eq_diagonalPowerTrace (add_pos hp hq) X H
  have hmixed_sum :
      Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (q : ℝ)) * K *
            Matrix.diagonal (fun j => lam j ^ (p : ℝ)) * K) =
        ∑ i : Fin n, ∑ j : Fin n, lam i ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam j ^ (p : ℝ) := by
    -- Expand the diagonal trace of the mixed term into a weighted square sum.
    simpa using
      diagonal_weighted_trace_eq_sumSquares
        (fun i => lam i ^ (q : ℝ))
        (fun j => lam j ^ (p : ℝ))
        K hK
  have hpair_sum :
      Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ)) * K * K) =
        ∑ i : Fin n, ∑ j : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) := by
    -- The pure power term is the same expansion with the second diagonal weight equal to `1`.
    calc
      Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ)) * K * K)
          =
        Matrix.trace
          (Matrix.diagonal (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ)) * K *
            Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) * K) := by
              simp [Matrix.mul_assoc]
      _ =
        ∑ i : Fin n, ∑ j : Fin n,
          lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) * (1 : ℝ) := by
            simpa using
              diagonal_weighted_trace_eq_sumSquares
                (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ))
                (fun _ : Fin n => (1 : ℝ))
                K hK
      _ =
        ∑ i : Fin n, ∑ j : Fin n,
          lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) := by
            simp
  -- Compare the two weighted square sums by the scalar inequality on each eigenvalue pair.
  calc
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
        =
      Matrix.trace
        (Matrix.diagonal (fun i => lam i ^ (q : ℝ)) * K *
          Matrix.diagonal (fun j => lam j ^ (p : ℝ)) * K) := hmixed
    _ =
      ∑ i : Fin n, ∑ j : Fin n, lam i ^ (q : ℝ) * (K i j) ^ (2 : ℕ) * lam j ^ (p : ℝ) :=
        hmixed_sum
    _ ≤
      ∑ i : Fin n, ∑ j : Fin n, lam i ^ (((p + q : ℝ≥0)) : ℝ) * (K i j) ^ (2 : ℕ) :=
        weightedMixedSquares_le_powerSquares (p := p) (q := q) hK hlam
    _ =
      Matrix.trace
        (Matrix.diagonal (fun i => lam i ^ (((p + q : ℝ≥0)) : ℝ)) * K * K) := hpair_sum.symm
    _ = ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := hpair.symm

/-- Helper for Lemma 6.14: after separating the zero-exponent edge case, the second conjunct is
the positive-exponent PSD trace-majorization step from the source proof. -/
theorem power_pairing_le_eigenvalue_pairing_of_pos
    {r : ℝ≥0} (hr : 0 < r) (X : 𝕊^n₊) (H : SymmMat) :
    ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
      ≤ ∑ i : Fin n, eigenvalues (X ^ r : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i := by
  -- The wrapper already removed the zero-exponent branch, so the core PSD majorization argument
  -- uses only the positive-exponent object `X ^ r` and does not need `hr` again.
  let _ := hr
  let A : SymmMat := ((X ^ r : 𝕊^n₊) : SymmMat)
  let B : SymmMat := H ^ (2 : ℕ)
  let hA : ((A : Mat)).IsHermitian := isHermitian A
  let hB : ((B : Mat)).IsHermitian := isHermitian B
  let UA : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian A).eigenvectorUnitary
  let UB : Matrix.unitaryGroup (Fin n) ℝ := (isHermitian B).eigenvectorUnitary
  let W : Mat := fun i j ↦ (((star (UA : Mat) * (UB : Mat)) i j) ^ (2 : ℕ))
  let ι : Type := Fin (Fintype.card (Fin n))
  let e : ι ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let W₀ : Matrix ι ι ℝ := fun i j ↦ W (e i) (e j)
  have hpairing :
      ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F =
        ∑ i : Fin n, ∑ j : Fin n,
          eigenvalues A i * W i j * eigenvalues B j := by
    -- Rewrite both symmetric factors in orthonormal eigenbases and then apply the overlap-sum
    -- trace formula from the earlier helper.
    have hA_spec :
        (A : Mat) =
          (UA : Mat) * Matrix.diagonal (eigenvalues A) * star (UA : Mat) := by
      simpa [A, UA, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
        (isHermitian A).spectral_theorem
    have hB_spec :
        (B : Mat) =
          (UB : Mat) * Matrix.diagonal (eigenvalues B) * star (UB : Mat) := by
      simpa [B, UB, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
        (isHermitian B).spectral_theorem
    calc
      ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
          = Matrix.trace (((A : Mat)ᵀ) * (B : Mat)) := by
              rw [RealSymmetricMatrixSpace.frobeniusInner_def]
      _ = Matrix.trace ((A : Mat) * (B : Mat)) := by
            rw [(isSymm A).eq]
      _ = Matrix.trace
            (((UA : Mat) * Matrix.diagonal (eigenvalues A) * star (UA : Mat)) *
              ((UB : Mat) * Matrix.diagonal (eigenvalues B) * star (UB : Mat))) := by
            rw [hA_spec, hB_spec]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            eigenvalues A i * W i j * eigenvalues B j := by
            exact
              unitary_diagonal_pairing_eq_sum_overlapSquares
                UA UB (eigenvalues A) (eigenvalues B)
  have hW :
      W ∈ doublyStochastic ℝ (Fin n) :=
    squared_overlap_matrix_mem_doubly_stochastic UA UB
  have hW₀ : W₀ ∈ doublyStochastic ℝ ι :=
    doublyStochastic_reindex e hW
  have hpairing₀ :
      ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F =
        ∑ i : ι, ∑ j : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ j * W₀ i j := by
    -- Route correction: `eigenvalues` is only a reindex of the ordered list `eigenvalues₀`,
    -- so reindex the overlap sum to the genuinely ordered surface before applying rearrangement.
    rw [hpairing]
    calc
      ∑ i : Fin n, ∑ j : Fin n, eigenvalues A i * W i j * eigenvalues B j
          = ∑ i : ι, ∑ j : Fin n, eigenvalues A (e i) * W (e i) j * eigenvalues B j := by
              symm
              exact Equiv.sum_comp e (fun i : Fin n ↦
                ∑ j : Fin n, eigenvalues A i * W i j * eigenvalues B j)
      _ = ∑ i : ι, ∑ j : ι, eigenvalues A (e i) * W (e i) (e j) * eigenvalues B (e j) := by
            exact
              Fintype.sum_congr
                (f := fun i : ι ↦
                  ∑ j : Fin n, eigenvalues A (e i) * W (e i) j * eigenvalues B j)
                (g := fun i : ι ↦
                  ∑ j : ι, eigenvalues A (e i) * W (e i) (e j) * eigenvalues B (e j))
                (fun i ↦ by
                  symm
                  exact Equiv.sum_comp e (fun j : Fin n ↦
                    eigenvalues A (e i) * W (e i) j * eigenvalues B j))
      _ = ∑ i : ι, ∑ j : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ j * W₀ i j := by
            exact
              Fintype.sum_congr
                (f := fun i : ι ↦
                  ∑ j : ι, eigenvalues A (e i) * W (e i) (e j) * eigenvalues B (e j))
                (g := fun i : ι ↦
                  ∑ j : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ j * W₀ i j)
                (fun i ↦ by
                  exact
                    Fintype.sum_congr
                      (f := fun j : ι ↦
                        eigenvalues A (e i) * W (e i) (e j) * eigenvalues B (e j))
                      (g := fun j : ι ↦ hA.eigenvalues₀ i * hB.eigenvalues₀ j * W₀ i j)
                      (fun j ↦ by
                        simp [W₀, W, e, RealSymmetricMatrixSpace.eigenvalues,
                          Matrix.IsHermitian.eigenvalues]
                        ring))
  have hidentity₀ :
      (∑ i : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ i) =
        ∑ i : Fin n, eigenvalues A i * eigenvalues B i := by
    -- Reindex the ordered eigenvalue pairing back to the chapter surface used in the statement.
    calc
      ∑ i : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ i
          = ∑ i : ι, eigenvalues A (e i) * eigenvalues B (e i) := by
              exact
                Fintype.sum_congr
                  (f := fun i : ι ↦ hA.eigenvalues₀ i * hB.eigenvalues₀ i)
                  (g := fun i : ι ↦ eigenvalues A (e i) * eigenvalues B (e i))
                  (fun i ↦ by
                    simp [e, RealSymmetricMatrixSpace.eigenvalues,
                      Matrix.IsHermitian.eigenvalues])
      _ = ∑ i : Fin n, eigenvalues A i * eigenvalues B i := by
            simpa using (Equiv.sum_comp e (fun i : Fin n ↦ eigenvalues A i * eigenvalues B i))
  -- The Birkhoff/rearrangement step now runs on the ordered `eigenvalues₀` lists, and the final
  -- comparison is transported back to the chapter eigenvalue surface by `hidentity₀`.
  calc
    ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
        = ∑ i : ι, ∑ j : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ j * W₀ i j := hpairing₀
    _ ≤ ∑ i : ι, hA.eigenvalues₀ i * hB.eigenvalues₀ i := by
          exact
            doublyStochastic_weightedSum_le_identityPairing
              hW₀ hA.eigenvalues₀_antitone hB.eigenvalues₀_antitone
    _ = ∑ i : Fin n, eigenvalues A i * eigenvalues B i := hidentity₀
    _ = ∑ i : Fin n, eigenvalues (X ^ r : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i := by
          rfl

/-- Helper for Lemma 6.14: the first conjunct becomes trivial on the boundary cases `p = 0` or
`q = 0`, and otherwise reduces to the positive-exponent spectral argument. -/
theorem mixed_power_trace_le_power_pairing
    (p q : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
      ≤ ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F := by
  -- Route correction: the chapter's nonunital PSD power has `X ^ 0 = 0`, so the boundary cases
  -- should be discharged first and only the interior branch needs the spectral weighted-sum proof.
  rcases eq_zero_or_pos p with rfl | hp
  · have hnonneg : 0 ≤ ⟪(X ^ q : 𝕊^n₊), H ^ (2 : ℕ)⟫_F :=
      power_pairing_nonneg q X H
    have hleft :
        Matrix.trace
            (((((X ^ (0 : ℝ≥0) : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) *
              (H : Mat)) = 0 := by
      rw [zero_psdPower_matrix X]
      simp
    rw [hleft]
    simpa using hnonneg
  · rcases eq_zero_or_pos q with rfl | hq
    · have hnonneg : 0 ≤ ⟪(X ^ p : 𝕊^n₊), H ^ (2 : ℕ)⟫_F :=
        power_pairing_nonneg p X H
      have hleft :
          Matrix.trace
              (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ (0 : ℝ≥0) : 𝕊^n₊) : Mat))ᵀ) *
                (H : Mat)) = 0 := by
        rw [zero_psdPower_matrix X]
        simp
      rw [hleft]
      simpa [add_comm] using hnonneg
    · simpa using mixed_power_trace_le_power_pairing_positive hp hq X H

/-- Helper for Lemma 6.14: the second conjunct is trivial at exponent `0`, while the positive
branch is the genuine PSD trace-majorization statement. -/
theorem power_pairing_le_eigenvalue_pairing
    (r : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    ⟪(X ^ r : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
      ≤ ∑ i : Fin n, eigenvalues (X ^ r : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i := by
  rcases eq_zero_or_pos r with rfl | hr
  · -- At exponent `0`, the PSD power is the zero matrix, so both sides simplify to `0`.
    have hX0 := zero_psdPower_matrix X
    have hX0symm : (((X ^ (0 : ℝ≥0) : 𝕊^n₊) : SymmMat)) = 0 := by
      ext i j
      simpa using congrArg (fun M : Mat ↦ M i j) hX0
    have hpair : ⟪(X ^ (0 : ℝ≥0) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F = 0 := by
      rw [RealSymmetricMatrixSpace.frobeniusInner_def]
      rw [hX0]
      simp
    have h0eig : eigenvalues (0 : SymmMat) = 0 := by
      simpa [RealSymmetricMatrixSpace.eigenvalues] using
        (isHermitian (0 : SymmMat)).eigenvalues_eq_zero_iff.mpr rfl
    have hXeig : eigenvalues (((X ^ (0 : ℝ≥0) : 𝕊^n₊) : SymmMat)) = 0 := by
      rw [hX0symm]
      exact h0eig
    have hsum :
        (∑ i : Fin n, eigenvalues (X ^ (0 : ℝ≥0) : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i) = 0 := by
      simp [RealSymmetricMatrixSpace.eigenvalues, hXeig]
    rw [hpair, hsum]
  · exact power_pairing_le_eigenvalue_pairing_of_pos hr X H

/-- Lemma 6.14: for nonnegative exponents, a positive-semidefinite symmetric matrix `X`, and a
real symmetric matrix `H`, the single mixed trace term `trace (((X^p H X^q)ᵀ) H)` is bounded by
the Frobenius pairing of `X^(p+q)` with `H^2`, and this is in turn bounded by the pairing of the
eigenvalue vectors of `X^(p+q)` and `H^2`. -/
theorem mixed_power_trace_le_power_pairing_of_pos
    (p q : ℝ≥0) (X : 𝕊^n₊) (H : SymmMat) :
    Matrix.trace
        (((((X ^ p : 𝕊^n₊) : Mat) * (H : Mat) * ((X ^ q : 𝕊^n₊) : Mat))ᵀ) * (H : Mat))
      ≤ ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F ∧
    ⟪(X ^ (p + q) : 𝕊^n₊), H ^ (2 : ℕ)⟫_F
      ≤ ∑ i : Fin n, eigenvalues (X ^ (p + q) : 𝕊^n₊) i * eigenvalues (H ^ (2 : ℕ)) i :=
  by
    -- Route correction: isolate the project-specific `X ^ 0 = 0` boundary behavior first, then
    -- leave only the positive-exponent spectral core to the two dedicated helpers above.
    refine ⟨?_, ?_⟩
    · exact mixed_power_trace_le_power_pairing p q X H
    · exact power_pairing_le_eigenvalue_pairing (p + q) X H
