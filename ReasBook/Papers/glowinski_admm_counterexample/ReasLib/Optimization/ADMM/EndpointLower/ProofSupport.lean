/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCases

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.EndpointLower
universe u

/- These generic cast and centered-quadratic arguments mirror the endpoint
reconstruction proofs, and apply to the newly checked affine extension. -/

theorem matrix_mul_constantModes_apply {ρ : Type u} {k : ℕ}
    (K : Matrix ρ (Fin k × Fin 2) ℚ) (i : ρ) (a : Fin 2) :
    (K * constantModes k) i a = ∑ t : Fin k, K i (t, a) := by
  -- Split the paired column index and collapse the Kronecker delta in the scalar coordinate.
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [constantModes]


theorem castMatrix_isSymm {ι : Type u} (M : Matrix ι ι ℚ) (symm : M.IsSymm) :
    (castMatrix M).IsSymm := by
  -- Cast the exact symmetry equation at each pair of entries.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  rw [castMatrix_apply, castMatrix_apply]
  exact congrArg (fun x : ℚ ↦ (x : ℝ)) (symm.apply i j)


theorem rationalMatrixOfQuadratic_isSymm {ι : Type u} [Fintype ι]
    [DecidableEq ι] (Q : (ι → ℚ) → ℚ) : (matrixOfQuadratic Q).IsSymm := by
  -- Swapping the two basis vectors commutes their pointwise sum and the two subtractions.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  rw [matrixOfQuadratic_apply, matrixOfQuadratic_apply]
  have basis_comm :
      (fun k : ι ↦ (if k = j then (1 : ℚ) else 0) + if k = i then 1 else 0) =
        fun k ↦ (if k = i then (1 : ℚ) else 0) + if k = j then 1 else 0 := by
    funext k
    ring
  rw [congrArg Q basis_comm]
  ring


theorem castLdl_quadratic_eq_sum_squares {k : ℕ}
    (K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ) (symm : K.IsSymm)
    (nonzero : ∀ i, (ldl K).pivot i ≠ 0) (x : Fin k × Fin 2 → ℝ) :
    (∑ i, ∑ j, castMatrix K i j * x i * x j) =
      ∑ h, ((ldl K).pivot h : ℝ) *
        (∑ i, ((ldl K).lower i h : ℝ) * x i) ^ 2 := by
  -- Cast the exact entrywise factorization, then commute the finite sums by pivot column.
  calc
    (∑ i, ∑ j, castMatrix K i j * x i * x j) =
        ∑ i, ∑ j, ∑ h,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [castMatrix_apply, ldl_factorization K symm nonzero i j]
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ i, ∑ h, ∑ j,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ h, ∑ i, ∑ j,
          (((ldl K).lower i h : ℝ) * ((ldl K).pivot h : ℝ) *
              ((ldl K).lower j h : ℝ)) * x i * x j := by
      rw [Finset.sum_comm]
    _ = ∑ h, ((ldl K).pivot h : ℝ) *
        (∑ i, ((ldl K).lower i h : ℝ) * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring


theorem castMatrix_posSemidef_of_positivePivots {k : ℕ} {threshold : ℚ}
    {K : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ} (symm : K.IsSymm)
    (threshold_nonneg : 0 ≤ threshold) (pivots : PositivePivots threshold K) :
    (castMatrix K).PosSemidef := by
  -- Expand a real matrix-vector contraction and apply the cast LDL sum-of-squares identity.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (castMatrix_isSymm K symm)) ?_
  intro x
  have contraction : dotProduct (star x) (Matrix.mulVec (castMatrix K) x) =
      ∑ i, ∑ j, castMatrix K i j * x i * x j := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [contraction, castLdl_quadratic_eq_sum_squares K symm
    (positivePivots_ne_zero threshold_nonneg pivots)]
  apply Finset.sum_nonneg
  intro h hh
  have pivot_nonneg : (0 : ℝ) ≤ (ldl K).pivot h := by
    exact_mod_cast le_of_lt (lt_of_le_of_lt threshold_nonneg (pivots h))
  exact mul_nonneg pivot_nonneg (sq_nonneg _)


theorem realQuadratic_eq_principal_of_rowSums_zero {ℓ : ℕ}
    (M : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℝ)
    (symm : M.IsSymm)
    (rowKernel : ∀ (p : Fin (ℓ + 2) × Fin 2) (a : Fin 2),
      (∑ t : Fin (ℓ + 2), M p (t, a)) = 0)
    (x : Fin (ℓ + 2) × Fin 2 → ℝ) :
    (∑ p, ∑ q, M p q * x p * x q) =
      ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        M (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
  -- Split the history into its final constant pair and centered remainder; both cross terms vanish
  -- by the row sums, and the final centered pair is zero.
  let constant : (Fin (ℓ + 2) × Fin 2) → ℝ :=
    fun p ↦ x (Fin.last (ℓ + 1), p.2)
  let centered : (Fin (ℓ + 2) × Fin 2) → ℝ :=
    fun p ↦ x p - constant p
  have symmetric (p q : Fin (ℓ + 2) × Fin 2) : M p q = M q p := by
    have entry := congrFun (congrFun symm q) p
    simpa only [Matrix.transpose_apply] using entry
  have rowConstant (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, M p q * constant q) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ t : Fin (ℓ + 2), ∑ a : Fin 2, M p (t, a) * constant (t, a)) =
          ∑ a : Fin 2, ∑ t : Fin (ℓ + 2), M p (t, a) * constant (t, a) := by
        rw [Finset.sum_comm]
      _ = ∑ a : Fin 2,
          (∑ t : Fin (ℓ + 2), M p (t, a)) * x (Fin.last (ℓ + 1), a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
      _ = 0 := by simp only [rowKernel, zero_mul, Finset.sum_const_zero]
  have columnConstant (q : Fin (ℓ + 2) × Fin 2) :
      (∑ p, constant p * M p q) = 0 := by
    calc
      (∑ p, constant p * M p q) = ∑ p, M q p * constant p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [symmetric p q]
        ring
      _ = 0 := rowConstant q
  have rowCentered (p : Fin (ℓ + 2) × Fin 2) :
      (∑ q, M p q * x q) = ∑ q, M p q * centered q := by
    calc
      (∑ q, M p q * x q) =
          ∑ q, (M p q * centered q + M p q * constant q) := by
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [centered]
        ring
      _ = (∑ q, M p q * centered q) + ∑ q, M p q * constant q := by
        rw [Finset.sum_add_distrib]
      _ = ∑ q, M p q * centered q := by rw [rowConstant, add_zero]
  have constantCross :
      (∑ p, constant p * (∑ q, M p q * centered q)) = 0 := by
    calc
      (∑ p, constant p * (∑ q, M p q * centered q)) =
          ∑ p, ∑ q, constant p * M p q * centered q := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = ∑ q, ∑ p, constant p * M p q * centered q := by
        rw [Finset.sum_comm]
      _ = ∑ q, (∑ p, constant p * M p q) * centered q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_mul]
      _ = 0 := by simp only [columnConstant, zero_mul, Finset.sum_const_zero]
  calc
    (∑ p, ∑ q, M p q * x p * x q) =
        ∑ p, x p * (∑ q, M p q * x q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ p, x p * (∑ q, M p q * centered q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [rowCentered]
    _ = ∑ p, (centered p * (∑ q, M p q * centered q) +
          constant p * (∑ q, M p q * centered q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [centered]
      ring
    _ = (∑ p, centered p * (∑ q, M p q * centered q)) +
        ∑ p, constant p * (∑ q, M p q * centered q) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ p, centered p * (∑ q, M p q * centered q) := by
      rw [constantCross, add_zero]
    _ = ∑ p, ∑ q, M p q * centered p * centered q := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ i : Fin (ℓ + 1) × Fin 2, ∑ j : Fin (ℓ + 1) × Fin 2,
        M (i.1.castSucc, i.2) (j.1.castSucc, j.2) *
          (x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)) *
          (x (j.1.castSucc, j.2) - x (Fin.last (ℓ + 1), j.2)) := by
      simp only [Fintype.sum_prod_type]
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, sub_self, zero_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fin.sum_univ_castSucc]
      simp only [centered, constant, Fin.val_castSucc, Prod.fst, Prod.snd,
        sub_self, mul_zero, Finset.sum_const_zero, add_zero]


theorem castMatrix_posSemidef_of_kernel_and_principalPivots {ℓ : ℕ}
    {threshold : ℚ}
    {K : Matrix (Fin (ℓ + 2) × Fin 2) (Fin (ℓ + 2) × Fin 2) ℚ}
    (symm : K.IsSymm) (kernel : K * constantModes (ℓ + 2) = 0)
    (threshold_nonneg : 0 ≤ threshold)
    (pivots : PositivePivots threshold
      (fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2))) :
    (castMatrix K).PosSemidef := by
  -- Cast the principal LDL certificate and center an arbitrary real vector using the cast kernel.
  let principal : Matrix (Fin (ℓ + 1) × Fin 2) (Fin (ℓ + 1) × Fin 2) ℚ :=
    fun i j ↦ K (i.1.castSucc, i.2) (j.1.castSucc, j.2)
  have principalSymm : principal.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    exact symm.apply (i.1.castSucc, i.2) (j.1.castSucc, j.2)
  have principalPSD : (castMatrix principal).PosSemidef :=
    castMatrix_posSemidef_of_positivePivots principalSymm threshold_nonneg pivots
  have rowKernel (p : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
      (∑ t : Fin (ℓ + 2), castMatrix K p (t, a)) = 0 := by
    have exactEntry := congrFun (congrFun kernel p) a
    rw [matrix_mul_constantModes_apply, Matrix.zero_apply] at exactEntry
    have castEntry := congrArg (fun z : ℚ ↦ (z : ℝ)) exactEntry
    push_cast at castEntry
    simpa only [castMatrix_apply, Rat.cast_zero] using castEntry
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (castMatrix_isSymm K symm)) ?_
  intro x
  have contraction : dotProduct (star x) (Matrix.mulVec (castMatrix K) x) =
      ∑ p, ∑ q, castMatrix K p q * x p * x q := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [contraction,
    realQuadratic_eq_principal_of_rowSums_zero (castMatrix K)
      (castMatrix_isSymm K symm) rowKernel]
  let centered : Fin (ℓ + 1) × Fin 2 → ℝ :=
    fun i ↦ x (i.1.castSucc, i.2) - x (Fin.last (ℓ + 1), i.2)
  have nonnegative := principalPSD.dotProduct_mulVec_nonneg centered
  have principalContraction :
      dotProduct (star centered) (Matrix.mulVec (castMatrix principal) centered) =
        ∑ i, ∑ j, castMatrix principal i j * centered i * centered j := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [principalContraction] at nonnegative
  simpa only [principal, centered, castMatrix_apply] using nonnegative


end ADMM.FiniteMemory.Reconstruction.EndpointLower
