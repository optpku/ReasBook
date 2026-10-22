/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_6_3.Section13325
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator
open LinearMap

section

variable {m n : ℕ}

/-
Domain sampling pass:
* primary domain: Powell-Yuan feasibility decrease estimates in Chapter 13
* inspected owner declarations:
  `cdtConstraintResidual` from `Chapter13.Theorem_13_5_1`
  `Matrix.pseudoinverse` / `A⁺` from `Chapter01.Exercise_1_5`
  `Matrix.pseudoinverseMulVec` from `Chapter01.Exercise_1_5`
  the nearby stagewise canonical use of `A⁺` in `Chapter13.Theorem_13_6_8`
* best owner abstractions: `Matrix.pseudoinverse` for the canonical pseudoinverse data and the
  source-facing Section 13.3 branch owner `powellYuanSection13325` for the two-case hypothesis
  reused downstream
* source/core/bridge triage:
  - source-facing: the Section 13.3 branch owner `powellYuanSection13325`
  - core/canonical: `Matrix.pseudoinverse`
  - bridge/view: the source vector `((A_k)⁺)ᵀ c_k`
* primitive data vs derived API:
  - primitive data: `ck`, `Ak`, `dk`, `ξk`, `Δ_k`, `b₂`
  - derived API: `powellYuanConstraintResidualDecreaseLowerBound`
-/

/-- Helper for Chapter13 Lemma 13.6.3: `EuclideanSpace.single` does not depend on the chosen
`DecidableEq` instance on the index type. -/
private lemma euclideanSingle_eq_of_decidableEq
    {ι : Type} (d₁ d₂ : DecidableEq ι) (j : ι) (c : ℝ) :
    @EuclideanSpace.single ι ℝ _ d₁ j c = @EuclideanSpace.single ι ℝ _ d₂ j c := by
  -- Compare both point-mass vectors coordinatewise.
  ext k
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

/-- Helper for Chapter13 Lemma 13.6.3: each entry of the real canonical pseudoinverse is the
matching coordinate of the projected-preimage construction used to define `A⁺`. -/
private lemma realPseudoinverseEntry_eq_projectedPreimageCoord
    (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin m) (j : Fin n) :
    A⁺ i j =
      ((((kerComplementEquivRange A.toEuclideanLin
          (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
          (A.toEuclideanLin.range.orthogonalProjectionOnto
            (EuclideanSpace.single j (1 : ℝ))) : (A.toEuclideanLin).kerᗮ) :
          EuclideanSpace ℝ (Fin m)) i) := by
  -- Unfold the owner once; the real specialization has the same coordinate formula as Chapter 1.
  classical
  simp only [Matrix.pseudoinverse]
  rw [euclideanSingle_eq_of_decidableEq _ _ j (1 : ℝ)]
  rfl

/-- Helper for Chapter13 Lemma 13.6.3: `Matrix.pseudoinverseMulVec A b` is the canonical
least-norm preimage of the orthogonal projection of `b` onto the range of `A.toEuclideanLin`. -/
private lemma realPseudoinverseMulVec_eq_projectedPreimage
    (A : Matrix (Fin n) (Fin m) ℝ) (b : EuclideanSpace ℝ (Fin n)) :
    Matrix.pseudoinverseMulVec A b =
      ((((kerComplementEquivRange A.toEuclideanLin
          (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
          (A.toEuclideanLin.range.orthogonalProjectionOnto b) :
          (A.toEuclideanLin).kerᗮ) : EuclideanSpace ℝ (Fin m))) := by
  let F : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := (A⁺).toEuclideanLin
  let G : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    ((A.toEuclideanLin).kerᗮ).subtype ∘ₗ
      ((kerComplementEquivRange A.toEuclideanLin
        (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm.toLinearMap ∘ₗ
        A.toEuclideanLin.range.orthogonalProjectionOnto.toLinearMap)
  have hsingle :
      ∀ j : Fin n, F (EuclideanSpace.single j (1 : ℝ)) = G (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    ext i
    -- Compare both linear maps on the standard basis vectors.
    calc
      F (EuclideanSpace.single j (1 : ℝ)) i = A⁺ i j := by
        simp [F, Matrix.toEuclideanLin_apply, EuclideanSpace.ofLp_single, Matrix.mulVec_single,
          PiLp.toLp_apply]
      _ =
          ((((kerComplementEquivRange A.toEuclideanLin
              (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
              (A.toEuclideanLin.range.orthogonalProjectionOnto
                (EuclideanSpace.single j (1 : ℝ))) : (A.toEuclideanLin).kerᗮ) :
              EuclideanSpace ℝ (Fin m)) i) :=
        realPseudoinverseEntry_eq_projectedPreimageCoord A i j
      _ = G (EuclideanSpace.single j (1 : ℝ)) i := by
        simp [G]
  have hsum :
      ∀ x : EuclideanSpace ℝ (Fin n),
        x = ∑ j : Fin n, x j • EuclideanSpace.single j (1 : ℝ) := by
    intro x
    ext k
    -- Expand against the standard basis of Euclidean coordinates.
    symm
    simpa [Pi.single_apply] using congrArg (fun v : Fin n → ℝ => v k)
      (Pi.sum_single_apply (v := fun j : Fin n => x.ofLp j))
  -- Since both sides are linear and agree on the standard basis, they agree everywhere.
  calc
    Matrix.pseudoinverseMulVec A b = F b := rfl
    _ = G b := by
      rw [hsum b]
      simp [F, G, hsingle, map_sum]
    _ =
        ((((kerComplementEquivRange A.toEuclideanLin
            (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).symm
            (A.toEuclideanLin.range.orthogonalProjectionOnto b) :
            (A.toEuclideanLin).kerᗮ) : EuclideanSpace ℝ (Fin m))) := by
      simp [G]

/-- Helper for Chapter13 Lemma 13.6.3: applying `A.toEuclideanLin` to the real canonical
pseudoinverse image of `b` recovers the range projection of `b`. -/
private lemma realToEuclideanLin_pseudoinverseMulVec
    (A : Matrix (Fin n) (Fin m) ℝ) (b : EuclideanSpace ℝ (Fin n)) :
    A.toEuclideanLin (Matrix.pseudoinverseMulVec A b) =
      A.toEuclideanLin.range.orthogonalProjectionOnto b := by
  -- Rewrite to the explicit projected preimage and apply the forward equivalence.
  rw [realPseudoinverseMulVec_eq_projectedPreimage]
  exact congrArg Subtype.val
    ((kerComplementEquivRange A.toEuclideanLin
      (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).apply_symm_apply
      (A.toEuclideanLin.range.orthogonalProjectionOnto b))

/-- Helper for Chapter13 Lemma 13.6.3: full column rank forces `A.toEuclideanLin` to have trivial
kernel. -/
private lemma ker_toEuclideanLin_eq_bot_of_fullColumnRank
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : Matrix.rank A = m) :
    LinearMap.ker A.toEuclideanLin = ⊥ := by
  -- First convert full column rank into injectivity of the raw matrix action `A.mulVec`.
  have hNullity : Matrix.rank A + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = m := by
    simpa [Matrix.rank] using LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hKerFinrank : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    omega
  have hMulVecKerBot : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 hKerFinrank
  have hMulVecInj : Function.Injective A.mulVec := LinearMap.ker_eq_bot.mp hMulVecKerBot
  -- Then transport that injectivity through `Matrix.toEuclideanLin`.
  refine LinearMap.ker_eq_bot.2 ?_
  intro x y hxy
  have hxyMulVecZero : A *ᵥ WithLp.ofLp (x - y) = 0 := by
    have hxyMulVec :
        A *ᵥ WithLp.ofLp x = A *ᵥ WithLp.ofLp y := by
      apply WithLp.toLp_injective (p := (2 : ENNReal))
      simpa [Matrix.toEuclideanLin_apply] using hxy
    simpa [Matrix.mulVec_sub, hxyMulVec]
  have hxyUnderlyingZero : WithLp.ofLp (x - y) = 0 := by
    have hEq : A *ᵥ WithLp.ofLp (x - y) = A *ᵥ 0 := by simpa using hxyMulVecZero
    exact hMulVecInj hEq
  have hxyZero : x - y = 0 := by
    simpa using (WithLp.ofLp_eq_zero (p := (2 : ENNReal))).mp hxyUnderlyingZero
  exact sub_eq_zero.mp hxyZero

/-- Helper for Chapter13 Lemma 13.6.3: under full column rank, the canonical pseudoinverse is a
left inverse of `A.toEuclideanLin`. -/
private lemma pseudoinverseMulVec_apply_toEuclideanLin_eq_self_of_fullColumnRank
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : Matrix.rank A = m)
    (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.pseudoinverseMulVec A (A.toEuclideanLin x) = x := by
  have hker : LinearMap.ker A.toEuclideanLin = ⊥ :=
    ker_toEuclideanLin_eq_bot_of_fullColumnRank A hA
  have hx_orth : x ∈ (A.toEuclideanLin).kerᗮ := by
    -- When the kernel is trivial, every vector lies in its orthogonal complement.
    simpa [hker]
  -- Rewrite the pseudoinverse image to the chosen kernel-complement preimage.
  rw [realPseudoinverseMulVec_eq_projectedPreimage]
  have hproj :
      A.toEuclideanLin.range.orthogonalProjectionOnto (A.toEuclideanLin x) =
        ⟨A.toEuclideanLin x, ⟨x, rfl⟩⟩ := by
    -- The image `A x` already lies in the range, so projection fixes it.
    simpa using
      A.toEuclideanLin.range.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨A.toEuclideanLin x, ⟨x, rfl⟩⟩
  rw [hproj]
  apply LinearMap.ker_eq_bot.mp hker
  -- Both sides have the same image under `A.toEuclideanLin`, so injectivity closes the proof.
  exact congrArg Subtype.val
    ((kerComplementEquivRange A.toEuclideanLin
      (A.toEuclideanLin.ker.isCompl_orthogonal.symm)).apply_symm_apply
      ⟨A.toEuclideanLin x, ⟨x, rfl⟩⟩)

/-- Helper for Chapter13 Lemma 13.6.3: full column rank gives the matrix identity `A⁺ * A = 1`
for the canonical pseudoinverse. -/
private lemma pseudoinverse_mul_self_of_fullColumnRank
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : Matrix.rank A = m) :
    A⁺ * A = 1 := by
  -- Evaluate the left-inverse identity on each standard basis vector, then read one coordinate.
  ext i j
  have hBasis :=
    congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i)
      (pseudoinverseMulVec_apply_toEuclideanLin_eq_self_of_fullColumnRank A hA
        (EuclideanSpace.single j (1 : ℝ)))
  change (A⁺ *ᵥ A.col j) i = (1 : Matrix (Fin m) (Fin m) ℝ) i j
  simpa [Matrix.one_apply] using hBasis

/-- Helper for Chapter13 Lemma 13.6.3: matrix multiplication inside `Matrix.toEuclideanLin`
evaluates as composition of the two matrix actions. -/
private theorem toEuclideanLin_mul_apply
    {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) ℝ) (N : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (M * N) v =
      Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) := by
  -- Evaluate the composed matrix action coordinatewise and use `Matrix.mulVec_mulVec`.
  ext i
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Helper for Chapter13 Lemma 13.6.3: the scaled pseudoinverse correction reduces to the scalar
multiple `(1 - α) • c_k` once `A⁺ * A = 1` is available. -/
private lemma scaledPseudoinverseCorrection_eq_smul
    (ck : EuclideanSpace ℝ (Fin m)) (Ak : Matrix (Fin n) (Fin m) ℝ) (α : ℝ)
    (hleftInv : Ak⁺ * Ak = 1) :
    ck - Ak.transpose.toEuclideanLin (α • (Ak⁺).transpose.toEuclideanLin ck) =
      (1 - α) • ck := by
  -- Route correction: normalize the transpose composite at the matrix-action level first.
  calc
    ck - Ak.transpose.toEuclideanLin (α • (Ak⁺).transpose.toEuclideanLin ck)
        = ck - α • (Ak.transpose.toEuclideanLin ((Ak⁺).transpose.toEuclideanLin ck)) := by
            rw [LinearMap.map_smul]
    _ = ck - α • ((Ak.transpose * (Ak⁺).transpose).toEuclideanLin ck) := by
          rw [← toEuclideanLin_mul_apply]
    _ = ck - α • (((Ak⁺ * Ak).transpose).toEuclideanLin ck) := by
          rw [← Matrix.transpose_mul]
    _ = ck - α • ck := by
          rw [hleftInv]
          simp
    _ = (1 - α) • ck := by
          simpa [sub_smul]

/-- Helper for Chapter13 Lemma 13.6.3: the transpose pseudoinverse action is bounded by the
operator norm `‖A⁺‖`. -/
private lemma pseudoinverseTranspose_apply_norm_le
    (A : Matrix (Fin n) (Fin m) ℝ) (c : EuclideanSpace ℝ (Fin m)) :
    ‖(A⁺).transpose.toEuclideanLin c‖ ≤ ‖A⁺‖ * ‖c‖ := by
  -- Apply the `L2` operator-norm estimate to `(A⁺)ᵀ` and then rewrite the matrix norm.
  calc
    ‖(A⁺).transpose.toEuclideanLin c‖ ≤ ‖(A⁺).transpose‖ * ‖c‖ := by
      simpa [Matrix.toEuclideanLin_apply] using
        (Matrix.l2_opNorm_mulVec (A := (A⁺).transpose) c)
    _ = ‖A⁺‖ * ‖c‖ := by
      congr 1
      simpa using (Matrix.l2_opNorm_conjTranspose (A := A⁺))

/-- Chapter13 Lemma 13.6.3: if the Section 13.3 estimate `(13.3.25)` holds for the stage data
`(ck, Ak, ξk, Δ_k, b₂)` via the source-facing owner `powellYuanSection13325` on the canonical
Moore-Penrose pseudoinverse `A_k⁺ = (A_k)⁺`, the Chapter 13 standing full-column-rank condition
from Assumption 13.6.2 is available for `Ak`, and the Step-2 constraint condition gives
`‖c_k + A_kᵀ d_k‖₂ ≤ ξ_k`, then the constraint residual decrease is bounded below by the source
quantity `(13.6.14)`, written using the canonical Chapter 13 residual owner
`cdtConstraintResidual` and the canonical pseudoinverse norm `‖(A_k)⁺‖`. -/
theorem powellYuanConstraintResidualDecreaseLowerBound
    (ck : EuclideanSpace ℝ (Fin m))
    (Ak : Matrix (Fin n) (Fin m) ℝ)
    (dk : EuclideanSpace ℝ (Fin n))
    (trustRegionRadius ξk b2 : ℝ)
    (h_b2 : 0 ≤ b2)
    (h_trustRegionRadius : 0 ≤ trustRegionRadius)
    (h_Ak_fullColumnRank : Matrix.rank Ak = m)
    (h_section13325 : powellYuanSection13325 ck Ak trustRegionRadius ξk b2)
    (h_constraint_condition :
      ‖cdtConstraintResidual ck Ak dk‖ ≤ ξk) :
    ‖ck‖ - ‖cdtConstraintResidual ck Ak dk‖ ≥
      min ‖ck‖ ((b2 * trustRegionRadius) / ‖Ak⁺‖) := by
  rw [ge_iff_le]
  rw [powellYuanSection13325_iff] at h_section13325
  rcases h_section13325 with ⟨h_largeRadius, h_smallRadius⟩
  by_cases hcase : b2 * trustRegionRadius ≥ ‖(Ak⁺).transpose.toEuclideanLin ck‖
  · have hξ_zero : ξk = 0 := h_largeRadius hcase
    have hres_zero : ‖cdtConstraintResidual ck Ak dk‖ = 0 := by
      -- The constraint condition and norm nonnegativity force the residual norm to vanish.
      refine le_antisymm ?_ (norm_nonneg _)
      simpa [hξ_zero] using h_constraint_condition
    -- In the zero branch, the left-hand side is exactly `‖ck‖`.
    calc
      min ‖ck‖ ((b2 * trustRegionRadius) / ‖Ak⁺‖) ≤ ‖ck‖ := min_le_left _ _
      _ = ‖ck‖ - ‖cdtConstraintResidual ck Ak dk‖ := by rw [hres_zero, sub_zero]
  · have hlt : b2 * trustRegionRadius < ‖(Ak⁺).transpose.toEuclideanLin ck‖ :=
      lt_of_not_ge hcase
    let α : ℝ := (b2 * trustRegionRadius) / ‖(Ak⁺).transpose.toEuclideanLin ck‖
    have hleftInv : Ak⁺ * Ak = 1 :=
      pseudoinverse_mul_self_of_fullColumnRank Ak h_Ak_fullColumnRank
    have hnum_nonneg : 0 ≤ b2 * trustRegionRadius := mul_nonneg h_b2 h_trustRegionRadius
    have hdenom_pos : 0 < ‖(Ak⁺).transpose.toEuclideanLin ck‖ := lt_of_le_of_lt hnum_nonneg hlt
    have hα_nonneg : 0 ≤ α := by
      exact div_nonneg hnum_nonneg hdenom_pos.le
    have hα_lt_one : α < 1 := by
      simpa [α] using (div_lt_one hdenom_pos).2 hlt
    have hone_sub_nonneg : 0 ≤ 1 - α := by
      linarith
    have hSectionCorrectionRaw := h_smallRadius hlt
    have hCorrection_norm :
        ‖ck -
            Ak.transpose.toEuclideanLin
              (((b2 * trustRegionRadius) / ‖(Ak⁺).transpose.toEuclideanLin ck‖) •
                (Ak⁺).transpose.toEuclideanLin ck)‖ =
          ‖(1 - α) • ck‖ := by
      -- Normalize the Section 13.3 correction term before taking norms.
      calc
        ‖ck -
            Ak.transpose.toEuclideanLin
              (((b2 * trustRegionRadius) / ‖(Ak⁺).transpose.toEuclideanLin ck‖) •
                (Ak⁺).transpose.toEuclideanLin ck)‖
            =
              ‖ck -
                  (b2 * trustRegionRadius / ‖(Ak⁺).transpose.toEuclideanLin ck‖) •
                    Ak.transpose.toEuclideanLin ((Ak⁺).transpose.toEuclideanLin ck)‖ := by
                rw [LinearMap.map_smul]
        _ = ‖ck - Ak.transpose.toEuclideanLin (α • (Ak⁺).transpose.toEuclideanLin ck)‖ := by
              simp [α, LinearMap.map_smul]
        _ = ‖(1 - α) • ck‖ := by
              rw [scaledPseudoinverseCorrection_eq_smul ck Ak α hleftInv]
    have hSectionCorrection :
        ξk ≤ ‖(1 - α) • ck‖ := by
      rw [hCorrection_norm] at hSectionCorrectionRaw
      exact hSectionCorrectionRaw
    have hResidual_le_scaled : ‖cdtConstraintResidual ck Ak dk‖ ≤ ‖(1 - α) • ck‖ := by
      exact le_trans h_constraint_condition hSectionCorrection
    have hnorm_scaled : ‖(1 - α) • ck‖ = (1 - α) * ‖ck‖ := by
      rw [norm_smul, Real.norm_of_nonneg hone_sub_nonneg]
    have hdifference_eq : ‖ck‖ - ‖(1 - α) • ck‖ = α * ‖ck‖ := by
      rw [hnorm_scaled]
      nlinarith [norm_nonneg ck]
    have hnorm_apply :
        ‖(Ak⁺).transpose.toEuclideanLin ck‖ ≤ ‖Ak⁺‖ * ‖ck‖ :=
      pseudoinverseTranspose_apply_norm_le Ak ck
    have hck_ne : ‖ck‖ ≠ 0 := by
      intro hck_zero
      have hdenom_le_zero : ‖(Ak⁺).transpose.toEuclideanLin ck‖ ≤ 0 := by
        simpa [hck_zero] using hnorm_apply
      exact not_lt_of_ge hdenom_le_zero hdenom_pos
    have hAkPlus_ne : ‖Ak⁺‖ ≠ 0 := by
      intro hAkPlus_zero
      have hdenom_le_zero : ‖(Ak⁺).transpose.toEuclideanLin ck‖ ≤ 0 := by
        simpa [hAkPlus_zero] using hnorm_apply
      exact not_lt_of_ge hdenom_le_zero hdenom_pos
    have hAkPlus_pos : 0 < ‖Ak⁺‖ :=
      lt_of_le_of_ne (norm_nonneg _) hAkPlus_ne.symm
    have hα_mul :
        α * ‖(Ak⁺).transpose.toEuclideanLin ck‖ = b2 * trustRegionRadius := by
      -- Clear the positive denominator once to recover the source scaling numerator.
      have hdenom_ne : ‖(Ak⁺).transpose.toEuclideanLin ck‖ ≠ 0 := ne_of_gt hdenom_pos
      dsimp [α]
      field_simp [α, hdenom_ne]
    have hLowerScaled :
        (b2 * trustRegionRadius) / ‖Ak⁺‖ ≤ α * ‖ck‖ := by
      rw [div_le_iff₀ hAkPlus_pos]
      calc
        b2 * trustRegionRadius
            = α * ‖(Ak⁺).transpose.toEuclideanLin ck‖ := hα_mul.symm
        _ ≤ α * (‖Ak⁺‖ * ‖ck‖) := by
            gcongr
        _ = α * ‖ck‖ * ‖Ak⁺‖ := by ring
    have hResidualDifference :
        ‖ck‖ - ‖(1 - α) • ck‖ ≤ ‖ck‖ - ‖cdtConstraintResidual ck Ak dk‖ :=
      sub_le_sub_left hResidual_le_scaled ‖ck‖
    exact le_trans (min_le_right _ _)
      (le_trans (by
        calc
          (b2 * trustRegionRadius) / ‖Ak⁺‖ ≤ α * ‖ck‖ := hLowerScaled
          _ = ‖ck‖ - ‖(1 - α) • ck‖ := hdifference_eq.symm)
        hResidualDifference)

#print axioms powellYuanSection13325
#print axioms powellYuanSection13325_iff
#print axioms powellYuanConstraintResidualDecreaseLowerBound

end
