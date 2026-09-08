module

public import ReasLib.Optimization.DFP.InverseUpdate
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

open scoped Matrix

namespace Matrix

/-- The determinant lemma for a sum of two rank-one outer products. -/
private theorem det_add_two_vecMulVec {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A.det) (u v : Fin 2 → n → ℝ) :
    (A + vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1)).det =
      A.det *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          Matrix.of (fun i j : Fin 2 => v i ⬝ᵥ (A⁻¹ *ᵥ u j))).det := by
  let U : Matrix n (Fin 2) ℝ := fun i j => u j i
  let V : Matrix (Fin 2) n ℝ := fun i j => v i j
  let W : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => v i ⬝ᵥ (A⁻¹ *ᵥ u j)
  -- Package the two outer products as the single product `U * V`.
  have hUV : U * V = vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1) := by
    ext i j
    simp [U, V, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply]
  -- Identify the small correction matrix entrywise with its dot-product form.
  have hVAU : V * A⁻¹ * U = W := by
    ext i j
    rw [Matrix.mul_assoc]
    rfl
  -- Apply the matrix determinant lemma and expose the `Fin 2` correction.
  calc
    (A + vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1)).det =
        (A + U * V).det := by rw [hUV, add_assoc]
    _ = A.det * (1 + V * A⁻¹ * U).det := det_add_mul U V hA
    _ = A.det * (1 + W).det := by rw [hVAU]
    _ = A.det *
        ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
          Matrix.of (fun i j : Fin 2 => v i ⬝ᵥ (A⁻¹ *ᵥ u j))).det := by rfl

/-- The determinant of an inverse-form DFP update is the old determinant multiplied by
the ratio of secant curvature to the inverse-Hessian quadratic form. -/
theorem det_inverseDFPUpdate {n : Type u} [Fintype n] [DecidableEq n] {H : Matrix n n ℝ}
    {s y : n → ℝ} (hH : H.PosDef) (hsy : 0 < s ⬝ᵥ y) :
    (inverseDFPUpdate H s y).det =
      H.det * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y))) := by
  let q : ℝ := y ⬝ᵥ (H *ᵥ y)
  let r : ℝ := s ⬝ᵥ y
  let u : Fin 2 → n → ℝ := ![-q⁻¹ • (H *ᵥ y), r⁻¹ • s]
  let v : Fin 2 → n → ℝ := ![y ᵥ* H, s]
  have hden := hH.inverseDFPUpdate_denominators_ne_zero hsy
  have hq : q ≠ 0 := by simpa [q] using hden.1
  have hr : r ≠ 0 := by simpa [r] using hden.2
  have hHdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  -- The nonsingular inverse cancels `H` on either side before acting on a vector.
  have hinvH (z : n → ℝ) : H⁻¹ *ᵥ (H *ᵥ z) = z := by
    calc
      H⁻¹ *ᵥ (H *ᵥ z) = (H⁻¹ * H) *ᵥ z := mulVec_mulVec z H⁻¹ H
      _ = 1 *ᵥ z := by rw [nonsing_inv_mul H hHdet]
      _ = z := one_mulVec z
  have hHinv (z : n → ℝ) : H *ᵥ (H⁻¹ *ᵥ z) = z := by
    calc
      H *ᵥ (H⁻¹ *ᵥ z) = (H * H⁻¹) *ᵥ z := mulVec_mulVec z H H⁻¹
      _ = 1 *ᵥ z := by rw [mul_nonsing_inv H hHdet]
      _ = z := one_mulVec z
  -- Rewrite the DFP correction as the two outer products used by the adapter.
  have hupdate :
      inverseDFPUpdate H s y =
        H + vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1) := by
    ext i j
    simp [inverseDFPUpdate_apply, u, v, q, r, vecMulVec_apply]
    ring
  let B : Matrix (Fin 2) (Fin 2) ℝ :=
    (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Matrix.of fun i j => v i ⬝ᵥ (H⁻¹ *ᵥ u j)
  -- The first three entries determine the determinant; the fourth is immaterial.
  have hmetric00 :
      (y ᵥ* H) ⬝ᵥ (H⁻¹ *ᵥ (-(q⁻¹ • (H *ᵥ y)))) = -1 := by
    rw [mulVec_neg, mulVec_smul, hinvH, dotProduct_neg, dotProduct_smul,
      ← dotProduct_mulVec]
    simp [q, hq]
  have hmetric01 :
      (y ᵥ* H) ⬝ᵥ (H⁻¹ *ᵥ (r⁻¹ • s)) = 1 := by
    rw [mulVec_smul, dotProduct_smul, ← dotProduct_mulVec, hHinv,
      dotProduct_comm]
    simpa [r] using inv_mul_cancel₀ hr
  have hmetric10 :
      s ⬝ᵥ (H⁻¹ *ᵥ (-(q⁻¹ • (H *ᵥ y)))) = -(r / q) := by
    rw [mulVec_neg, mulVec_smul, hinvH, dotProduct_neg, dotProduct_smul]
    simp [r, div_eq_mul_inv]
    ring
  have hB00 : B 0 0 = 0 := by
    simp [B, u, v, hmetric00]
  have hB01 : B 0 1 = 1 := by
    simp [B, u, v, hmetric01]
  have hB10 : B 1 0 = -(r / q) := by
    simp [B, u, v, hmetric10]
  -- Apply the rank-two determinant lemma and evaluate the resulting `2 × 2` determinant.
  calc
    (inverseDFPUpdate H s y).det =
        (H + vecMulVec (u 0) (v 0) + vecMulVec (u 1) (v 1)).det := by
      rw [hupdate]
    _ = H.det * B.det := by
      exact det_add_two_vecMulVec H hHdet u v
    _ = H.det * (r / q) := by
      rw [det_fin_two, hB00, hB01, hB10]
      ring
    _ = H.det * ((s ⬝ᵥ y) / (y ⬝ᵥ (H *ᵥ y))) := by
      rfl

end Matrix
