module

public import ReasLib.LinearAlgebra.EuclideanSpace.OrthogonalSum
public import ReasLib.Optimization.DFP.Iteration

public section

noncomputable section

universe u v

open scoped Matrix

namespace DFP.OrthogonalSum.Transport

/-- Scaled DFP steps commute with the canonical left orthogonal-sum embedding. -/
theorem steps_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (α : ℕ → ℝ) (d : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.steps α
        (fun n ↦ EuclideanSpace.OrthogonalSum.inl (κ := κ) (d n)) k =
      EuclideanSpace.OrthogonalSum.inl (DFP.steps α d k) := by
  rw [DFP.steps_apply, DFP.steps_apply]
  exact ((EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_smul (α k) (d k)).symm

/-- Successive gradient differences commute with the canonical left orthogonal-sum
embedding. -/
theorem gradientChanges_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (g : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.gradientChanges
        (fun n ↦ EuclideanSpace.OrthogonalSum.inl (κ := κ) (g n)) k =
      EuclideanSpace.OrthogonalSum.inl (DFP.gradientChanges g k) := by
  rw [DFP.gradientChanges_apply, DFP.gradientChanges_apply]
  exact ((EuclideanSpace.OrthogonalSum.inl (ι := ι) (κ := κ)).map_sub
    (g (k + 1)) (g k)).symm

/-- Search directions for identity-block extensions are the embedded original search
directions. -/
theorem directions_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : ℕ → Matrix ι ι ℝ) (g : ℕ → EuclideanSpace ℝ ι) (k : ℕ) :
    DFP.directions
        (fun n ↦ EuclideanSpace.OrthogonalSum.extendMatrix (κ := κ) (H n))
        (fun n ↦ EuclideanSpace.OrthogonalSum.inl (κ := κ) (g n)) k =
      EuclideanSpace.OrthogonalSum.inl (DFP.directions H g k) := by
  rw [DFP.directions_apply, DFP.directions_apply]
  rw [EuclideanSpace.OrthogonalSum.extendMatrix_mulVec_inl]
  simp

/-- The dot product of two left-embedded Euclidean vectors is their original dot product. -/
theorem dotProduct_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (x y : EuclideanSpace ℝ ι) :
    WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) x) ⬝ᵥ
        WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y) =
      WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [Matrix.dotProduct_block]
  have hxL :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) x) ∘ Sum.inl =
        WithLp.ofLp x := by
    funext i
    exact EuclideanSpace.OrthogonalSum.inl_apply_inl x i
  have hyL :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y) ∘ Sum.inl =
        WithLp.ofLp y := by
    funext i
    exact EuclideanSpace.OrthogonalSum.inl_apply_inl y i
  have hxR :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) x) ∘ Sum.inr = 0 := by
    funext i
    exact EuclideanSpace.OrthogonalSum.inl_apply_inr x i
  have hyR :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y) ∘ Sum.inr = 0 := by
    funext i
    exact EuclideanSpace.OrthogonalSum.inl_apply_inr y i
  rw [hxL, hyL, hxR, hyR]
  simp

/-- Left vector multiplication by an identity-block extension stays in the left summand. -/
theorem vecMul_extendMatrix_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) :
    WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) z) ᵥ*
        EuclideanSpace.OrthogonalSum.extendMatrix H =
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl
        (WithLp.toLp 2 (WithLp.ofLp z ᵥ* H)) : EuclideanSpace ℝ (ι ⊕ κ)) := by
  ext i
  cases i <;> simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]

/-- An inverse-form DFP update by left-embedded secant vectors preserves the identity block.
No nonvanishing assumption on either update denominator is needed. -/
theorem inverseDFPUpdate_extendMatrix_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (s y : EuclideanSpace ℝ ι) :
    Matrix.inverseDFPUpdate
        (EuclideanSpace.OrthogonalSum.extendMatrix (κ := κ) H)
        (WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) s))
        (WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y)) =
      EuclideanSpace.OrthogonalSum.extendMatrix
        (Matrix.inverseDFPUpdate H (WithLp.ofLp s) (WithLp.ofLp y)) := by
  have hmul := EuclideanSpace.OrthogonalSum.extendMatrix_mulVec_inl
    (κ := κ) H y
  have hvec := vecMul_extendMatrix_inl (κ := κ) H y
  have hmetric :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y) ⬝ᵥ
          (EuclideanSpace.OrthogonalSum.extendMatrix H *ᵥ
            WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y)) =
        WithLp.ofLp y ⬝ᵥ (H *ᵥ WithLp.ofLp y) := by
    rw [hmul]
    simpa using dotProduct_inl (κ := κ) y
      (WithLp.toLp 2 (H *ᵥ WithLp.ofLp y))
  have hsecant :
      WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) s) ⬝ᵥ
          WithLp.ofLp (EuclideanSpace.OrthogonalSum.inl (κ := κ) y) =
        WithLp.ofLp s ⬝ᵥ WithLp.ofLp y :=
    dotProduct_inl s y
  ext i j
  rw [Matrix.inverseDFPUpdate_apply, hmetric, hsecant, hmul, hvec]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.inverseDFPUpdate_apply]

end DFP.OrthogonalSum.Transport
