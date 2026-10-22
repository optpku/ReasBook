/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_1
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_4

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5.SpectralRepresentation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped BigOperators Matrix

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 7.3 companion. Under the same Chapter 7 SVD and filter
representation setup, `Remark 7.4` rewrites the GCV denominator to the
dimension-minus-trace form determined by the spectral filter weights. -/
theorem gcvValue_influenceMatrix_eq_of_filterRep
    (K U V Rα : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (d : EuclideanSpace ℝ n)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    gcvValue (influenceMatrix K Rα) d =
      predictiveRisk (regularizedResidual (influenceMatrix K Rα) d) /
        ((((Fintype.card n : ℝ) - ∑ i : n, wα (s i ^ 2)) / (Fintype.card n : ℝ)) ^ 2) := by
  let Aα : Matrix n n ℝ := influenceMatrix K Rα
  have hAα :
      Aα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ := by
    simpa [Aα] using influenceMatrix_eq_spectralRep K U V Rα wα s hK hRα
  simpa [Aα] using
    gcvValue_eq_of_spectralRep Aα U wα s d hRα.orthogonalU hAα

/-- Helper for Exercise 7.3: orthogonal coordinate changes preserve
`predictiveRisk`. -/
lemma predictiveRisk_eq_of_orthogonal
    (U : Matrix n n ℝ) (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    predictiveRisk (U.toEuclideanLin x) = predictiveRisk x := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hU
  have hdot :
      (U *ᵥ x.ofLp) ⬝ᵥ (U *ᵥ x.ofLp) = x.ofLp ⬝ᵥ x.ofLp := by
    -- Push the quadratic form through `Uᵀ` so orthogonality cancels the basis change.
    calc
      (U *ᵥ x.ofLp) ⬝ᵥ (U *ᵥ x.ofLp) = x.ofLp ⬝ᵥ Uᵀ *ᵥ (U *ᵥ x.ofLp) := by
              symm
              exact Matrix.dotProduct_transpose_mulVec U x.ofLp (U *ᵥ x.ofLp)
      _ = x.ofLp ⬝ᵥ ((Uᵀ * U) *ᵥ x.ofLp) := by
            rw [← Matrix.mulVec_mulVec]
      _ = x.ofLp ⬝ᵥ x.ofLp := by
            rw [hUtU, Matrix.one_mulVec]
  have hsum :
      ∑ i : n, ((U *ᵥ x.ofLp) i) ^ 2 = ∑ i : n, (x.ofLp i) ^ 2 := by
    -- Over `ℝ`, the dot product with itself is exactly the sum of coordinate squares.
    simpa [dotProduct, pow_two] using hdot
  rw [predictiveRisk_def, predictiveRisk_def, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  have hcoords :
      ∑ i : n, (U.toEuclideanLin x i) ^ 2 = ∑ i : n, ((U *ᵥ x.ofLp) i) ^ 2 := by
    simpa using
      congrArg (fun y : n → ℝ ↦ ∑ i : n, (y i) ^ 2)
        (Matrix.ofLp_toEuclideanLin_apply U x)
  rw [hcoords, hsum]

/-- Helper for Exercise 7.3: in the orthogonal coordinates determined by `U`,
the regularized residual becomes the diagonal filter-deviation operator. -/
lemma orthogonalCoordinates_regularizedResidual_eq_diagonal
    (A U : Matrix n n ℝ) (w : ℝ → ℝ) (s : n → ℝ)
    (d ξ : EuclideanSpace ℝ n)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hA : A = U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ)
    (hξ : Uᵀ.toEuclideanLin d = ξ) :
    Uᵀ.toEuclideanLin (regularizedResidual A d) =
      Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1)) ξ := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).mp hU
  have hSub :
      A - 1 = U * Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ := by
    have hUUt : U * Uᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hU
    -- Rewrite the identity in the same orthogonal basis before subtracting diagonals.
    calc
      A - 1
          = U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ -
              U * Matrix.diagonal (fun _ : n ↦ (1 : ℝ)) * Uᵀ := by
                rw [hA, ← hUUt]
                simp
      _ = U *
            ((Matrix.diagonal (fun i ↦ w (s i ^ 2)) -
              Matrix.diagonal (fun _ : n ↦ (1 : ℝ))) *
              Uᵀ) := by
            simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
      _ = U * (Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ) := by
            rw [Matrix.diagonal_sub]
      _ = U * Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ := by
            simp [Matrix.mul_assoc]
  have hξ' : Uᵀ *ᵥ d.ofLp = ξ.ofLp := by
    -- Convert the coordinate hypothesis to the underlying function representation.
    simpa using congrArg WithLp.ofLp hξ
  have hLeft :
      Uᵀ * (A - 1) = Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ := by
    -- Pull the orthogonal factor through `A - 1` so only the diagonal deviation remains.
    calc
      Uᵀ * (A - 1) = Uᵀ * A - Uᵀ := by
        rw [Matrix.mul_sub]
        simp
      _ = Uᵀ * (U * Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ) - Uᵀ := by
            rw [hA]
      _ = (((Uᵀ * U) * Matrix.diagonal (fun i ↦ w (s i ^ 2))) * Uᵀ) - Uᵀ := by
            simp [Matrix.mul_assoc]
      _ = (Matrix.diagonal (fun i ↦ w (s i ^ 2)) * Uᵀ) - Uᵀ := by
            rw [hUtU]
            simp
      _ = (Matrix.diagonal (fun i ↦ w (s i ^ 2)) - 1) * Uᵀ := by
            rw [Matrix.sub_mul]
            simp
      _ = Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ := by
            congr 1
            ext i j
            by_cases hij : i = j
            · subst hij
              simp
            · simp [Matrix.diagonal, hij]
  -- Move both sides to coordinate functions so orthogonality and the diagonal action simplify directly.
  apply WithLp.ofLp_injective
  calc
    ((Uᵀ.toEuclideanLin (regularizedResidual A d)).ofLp)
        = (Uᵀ * (A - 1)) *ᵥ d.ofLp := by
            simp [regularizedResidual_eq, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
              Matrix.mul_sub, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    _ = (Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) * Uᵀ) *ᵥ d.ofLp := by
          simpa using congrArg (fun M : Matrix n n ℝ ↦ M *ᵥ d.ofLp) hLeft
    _ = Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1) *ᵥ ξ.ofLp := by
          simpa [hξ'] using
            (Matrix.mulVec_mulVec d.ofLp
              (Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1)) Uᵀ).symm
    _ = ((Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ w (s i ^ 2) - 1)) ξ).ofLp) := by
          simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Exercise 7.3: the predictive risk of a diagonal operator is the
normalized coordinate sum of the squared diagonal weights. -/
lemma predictiveRisk_diagonal_eq_coordinateSum
    (c : n → ℝ) (ξ : EuclideanSpace ℝ n) :
    predictiveRisk (Matrix.toEuclideanLin (Matrix.diagonal c) ξ) =
      (∑ i : n, (c i) ^ 2 * (ξ i) ^ 2) / (Fintype.card n : ℝ) := by
  rw [predictiveRisk_def, EuclideanSpace.real_norm_sq_eq]
  have hcoords :
      ∑ i : n, (Matrix.toEuclideanLin (Matrix.diagonal c) ξ i) ^ 2 =
        ∑ i : n, ((Matrix.diagonal c *ᵥ ξ.ofLp) i) ^ 2 := by
    -- Rewrite the matrix action in function coordinates before evaluating the diagonal.
    simpa using
      congrArg (fun y : n → ℝ ↦ ∑ i : n, (y i) ^ 2)
        (Matrix.ofLp_toEuclideanLin_apply (Matrix.diagonal c) ξ)
  rw [hcoords]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

/-- Helper for Exercise 7.3: after diagonalizing the influence matrix, the
predictive risk of the regularized residual becomes the spectral coordinate
sum from `(7.24)`. -/
lemma predictiveRisk_regularizedResidual_eq_spectralCoordinateSum
    (K U V Rα : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (d ξ : EuclideanSpace ℝ n)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s)
    (hξ : Uᵀ.toEuclideanLin d = ξ) :
    predictiveRisk (regularizedResidual (influenceMatrix K Rα) d) =
      (∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2) / (Fintype.card n : ℝ) := by
  have hA :
      influenceMatrix K Rα = U * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Uᵀ := by
    simpa using influenceMatrix_eq_spectralRep K U V Rα wα s hK hRα
  have hUUt : U * Uᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).mp hRα.orthogonalU
  let residual : EuclideanSpace ℝ n := regularizedResidual (influenceMatrix K Rα) d
  have hRecover :
      U.toEuclideanLin (Uᵀ.toEuclideanLin residual) = residual := by
    -- Apply the orthogonal change of basis and its inverse in sequence.
    apply WithLp.ofLp_injective
    simp [residual, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hUUt]
  have hCoords :
      Uᵀ.toEuclideanLin (regularizedResidual (influenceMatrix K Rα) d) =
        Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1)) ξ :=
    orthogonalCoordinates_regularizedResidual_eq_diagonal
      (A := influenceMatrix K Rα) (U := U) (w := wα) (s := s)
      (d := d) (ξ := ξ) hRα.orthogonalU hA hξ
  have hRiskInvariant :
      predictiveRisk residual = predictiveRisk (Uᵀ.toEuclideanLin residual) := by
    -- Apply orthogonal invariance after identifying `U ∘ Uᵀ` with the identity.
    have hRecoverRisk :
        predictiveRisk (U.toEuclideanLin (Uᵀ.toEuclideanLin residual)) =
          predictiveRisk residual := by
      rw [hRecover]
    have hRiskInvariant' :
        predictiveRisk (U.toEuclideanLin (Uᵀ.toEuclideanLin residual)) =
          predictiveRisk (Uᵀ.toEuclideanLin residual) :=
      predictiveRisk_eq_of_orthogonal U hRα.orthogonalU (Uᵀ.toEuclideanLin residual)
    exact hRecoverRisk.symm.trans hRiskInvariant'
  have hSign :
      ∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * (ξ i) ^ 2 =
        ∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2 := by
    -- Squaring removes the sign change between `w - 1` and `1 - w`.
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  -- Drop the orthogonal factor from the risk and then read the diagonal operator coordinatewise.
  calc
    predictiveRisk (regularizedResidual (influenceMatrix K Rα) d)
        = predictiveRisk (Uᵀ.toEuclideanLin residual) := by
            simpa [residual] using hRiskInvariant
    _ = predictiveRisk
          (Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1)) ξ) := by
            rw [hCoords]
    _ = (∑ i : n, (wα (s i ^ 2) - 1) ^ 2 * (ξ i) ^ 2) / (Fintype.card n : ℝ) := by
            rw [predictiveRisk_diagonal_eq_coordinateSum]
    _ = (∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2) / (Fintype.card n : ℝ) := by
            rw [hSign]

/-- Helper for Exercise 7.3: the Remark 7.4 denominator `card - ∑ wα`
is the sum of the filter deviations `∑ (1 - wα)`. -/
lemma spectralDenominator_eq_filterDeviationSum
    (wα : ℝ → ℝ) (s : n → ℝ) :
    (Fintype.card n : ℝ) - ∑ i : n, wα (s i ^ 2) =
      ∑ i : n, (1 - wα (s i ^ 2)) := by
  -- Rewrite the ambient dimension as the sum of constant ones and combine the sums.
  calc
    (Fintype.card n : ℝ) - ∑ i : n, wα (s i ^ 2)
        = (∑ i : n, (1 : ℝ)) - ∑ i : n, wα (s i ^ 2) := by
            simp
    _ = ∑ i : n, (1 - wα (s i ^ 2)) := by
          rw [← Finset.sum_sub_distrib]

/-- exercise_7_3

Exercise 7.3. Under the Chapter 7 SVD and filter representation setup, the
GCV formula `(7.23)` rewrites as the spectral-coordinate evaluation formula
`(7.24)`. -/
theorem gcvValue_influenceMatrix_eq_spectralSum
    (K U V Rα : Matrix n n ℝ) (wα : ℝ → ℝ) (s : n → ℝ)
    (d ξ : EuclideanSpace ℝ n)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s)
    (hξ : Uᵀ.toEuclideanLin d = ξ) :
    gcvValue (influenceMatrix K Rα) d =
      ((Fintype.card n : ℝ) *
          ∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2) /
        (∑ i : n, (1 - wα (s i ^ 2))) ^ 2 := by
  have hNumerator :
      predictiveRisk (regularizedResidual (influenceMatrix K Rα) d) =
        (∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2) / (Fintype.card n : ℝ) :=
    predictiveRisk_regularizedResidual_eq_spectralCoordinateSum
      K U V Rα wα s d ξ hK hRα hξ
  have hDenominator :
      (Fintype.card n : ℝ) - ∑ i : n, wα (s i ^ 2) =
        ∑ i : n, (1 - wα (s i ^ 2)) :=
    spectralDenominator_eq_filterDeviationSum (wα := wα) (s := s)
  -- Rewrite the Remark 7.4 formula into the spectral numerator and denominator sums.
  rw [gcvValue_influenceMatrix_eq_of_filterRep K U V Rα wα s d hK hRα]
  rw [hNumerator, hDenominator]
  set cardR : ℝ := (Fintype.card n : ℝ)
  set numerator : ℝ := ∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2
  set denominator : ℝ := ∑ i : n, (1 - wα (s i ^ 2))
  change (numerator / cardR) / ((denominator / cardR) ^ 2) =
    (cardR * numerator) / denominator ^ 2
  by_cases hcard : cardR = 0
  · have hcardNat : Fintype.card n = 0 := by
      change ((Fintype.card n : ℝ) = 0) at hcard
      exact_mod_cast hcard
    have hIsEmpty : IsEmpty n := Fintype.card_eq_zero_iff.mp hcardNat
    -- Local instance justification (zero-cardinality branch): simplify the empty index sums.
    letI : IsEmpty n := hIsEmpty
    simp [cardR, numerator, denominator, hcard]
  · by_cases hden : denominator = 0
    · simp [hden]
    · field_simp [hcard, hden]

end
