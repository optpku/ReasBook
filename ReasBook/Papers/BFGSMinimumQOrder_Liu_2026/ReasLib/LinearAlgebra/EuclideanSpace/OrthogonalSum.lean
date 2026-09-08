module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

noncomputable section

universe u v

open scoped Matrix

namespace EuclideanSpace.OrthogonalSum

/-- The canonical continuous linear embedding into the left summand of an orthogonal
coordinate sum. -/
def inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (ι ⊕ κ) :=
  (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ κ))

/-- The left coordinates of the canonical left-summand embedding are unchanged. -/
@[simp]
theorem inl_apply_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) (i : ι) :
    WithLp.ofLp (inl z) (Sum.inl i : ι ⊕ κ) = WithLp.ofLp z i := by
  rfl

/-- The right coordinates of the canonical left-summand embedding vanish. -/
@[simp]
theorem inl_apply_inr {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) (j : κ) :
    WithLp.ofLp (inl z) (Sum.inr j : ι ⊕ κ) = 0 := by
  rfl

/-- The canonical left-summand embedding preserves the real inner product. -/
theorem inner_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z z' : EuclideanSpace ℝ ι) :
    inner ℝ (inl z : EuclideanSpace ℝ (ι ⊕ κ)) (inl z') = inner ℝ z z' := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_sum_type]
  simp

/-- The canonical left-summand embedding is an isometry. -/
@[simp]
theorem norm_inl {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    ‖(inl z : EuclideanSpace ℝ (ι ⊕ κ))‖ = ‖z‖ := by
  have hsquare := inner_inl (κ := κ) z z
  simp only [real_inner_self_eq_norm_sq] at hsquare
  nlinarith [norm_nonneg (inl z : EuclideanSpace ℝ (ι ⊕ κ)), norm_nonneg z]

/-- Extend a square matrix by the identity on a right coordinate summand. -/
def extendMatrix {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks H 0 0 1

/-- The upper-left block of `extendMatrix H` is `H`. -/
@[simp]
theorem extendMatrix_apply_inl_inl {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) (i j : ι) :
    extendMatrix (κ := κ) H (Sum.inl i) (Sum.inl j) = H i j := by
  rfl

/-- The upper-right block of `extendMatrix H` vanishes. -/
@[simp]
theorem extendMatrix_apply_inl_inr {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) (i : ι) (j : κ) :
    extendMatrix H (Sum.inl i) (Sum.inr j) = 0 := by
  rfl

/-- The lower-left block of `extendMatrix H` vanishes. -/
@[simp]
theorem extendMatrix_apply_inr_inl {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) (i : κ) (j : ι) :
    extendMatrix H (Sum.inr i) (Sum.inl j) = 0 := by
  rfl

/-- The lower-right block of `extendMatrix H` is the identity. -/
@[simp]
theorem extendMatrix_apply_inr_inr {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) (i j : κ) :
    extendMatrix H (Sum.inr i) (Sum.inr j) = if i = j then 1 else 0 := by
  simp [extendMatrix, Matrix.one_apply]

/-- The identity-block extension acts on a left-embedded vector by the embedded
original matrix action. -/
theorem extendMatrix_mulVec_inl {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) :
    extendMatrix H *ᵥ WithLp.ofLp (inl z : EuclideanSpace ℝ (ι ⊕ κ)) =
      WithLp.ofLp (inl (WithLp.toLp 2 (H *ᵥ WithLp.ofLp z)) :
        EuclideanSpace ℝ (ι ⊕ κ)) := by
  unfold extendMatrix
  rw [Matrix.fromBlocks_mulVec]
  ext i
  cases i <;> simp [Matrix.mulVec, dotProduct]

/-- The quadratic form of an identity-block extension splits as the original quadratic
form plus a sum of squares. -/
theorem quadraticForm_extendMatrix {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) (x : ι →₀ ℝ) (y : κ →₀ ℝ) :
    (x.sumElim y).sum (fun i xi ↦
        (x.sumElim y).sum (fun j xj ↦ xi * extendMatrix H i j * xj)) =
      x.sum (fun i xi ↦ x.sum (fun j xj ↦ xi * H i j * xj)) +
        y.sum (fun _ yi ↦ yi ^ 2) := by
  have hleft (i : ι) (xi : ℝ) :
      (x.sumElim y).sum (fun j xj ↦ xi * extendMatrix H (Sum.inl i) j * xj) =
        x.sum (fun j xj ↦ xi * H i j * xj) := by
    rw [Finsupp.sum_sumElim]
    change x.sum (fun j xj ↦ xi * extendMatrix H (Sum.inl i) (Sum.inl j) * xj) +
        y.sum (fun j xj ↦ xi * extendMatrix H (Sum.inl i) (Sum.inr j) * xj) = _
    simp [extendMatrix]
  have hright (i : κ) :
      (x.sumElim y).sum (fun j xj ↦ y i * extendMatrix H (Sum.inr i) j * xj) =
        (y i) ^ 2 := by
    rw [Finsupp.sum_sumElim]
    change x.sum (fun j xj ↦ y i * extendMatrix H (Sum.inr i) (Sum.inl j) * xj) +
        y.sum (fun j xj ↦ y i * extendMatrix H (Sum.inr i) (Sum.inr j) * xj) = _
    simp [extendMatrix, Matrix.one_apply, pow_two]
  rw [Finsupp.sum_sumElim]
  congr 1
  · apply Finsupp.sum_congr
    intro i hi
    simpa [Function.comp_apply] using hleft i (x i)
  · apply Finsupp.sum_congr
    intro i hi
    simpa [Function.comp_apply] using hright i

/-- Extending a real square matrix by an identity block preserves and reflects positive
definiteness. This statement does not require either index type to be finite. -/
theorem extendMatrix_posDef_iff {ι : Type u} {κ : Type v} [DecidableEq κ]
    (H : Matrix ι ι ℝ) :
    (extendMatrix H : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ).PosDef ↔ H.PosDef := by
  constructor
  · intro h
    have hsub := h.submatrix Sum.inl_injective
    have heq :
        (extendMatrix H).submatrix (Sum.inl : ι → ι ⊕ κ) Sum.inl = H := by
      ext i j
      rfl
    rw [heq] at hsub
    exact hsub
  · intro hH
    refine ⟨Matrix.IsHermitian.fromBlocks hH.1 (by simp) Matrix.isHermitian_one, ?_⟩
    intro z hz
    let x : ι →₀ ℝ := (Finsupp.sumFinsuppEquivProdFinsupp z).1
    let y : κ →₀ ℝ := (Finsupp.sumFinsuppEquivProdFinsupp z).2
    have hdecomp : x.sumElim y = z := by
      simp [x, y]
    rw [← hdecomp]
    change 0 < (x.sumElim y).sum (fun i xi ↦
      (x.sumElim y).sum (fun j xj ↦ xi * extendMatrix H i j * xj))
    rw [quadraticForm_extendMatrix]
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro hy
        apply hz
        rw [← hdecomp, hx, hy]
        exact Finsupp.sumElim_zero_zero
      have hypos : 0 < y.sum (fun _ yi ↦ yi ^ 2) := by
        refine Finsupp.sum_pos ?_ hy
        intro i hi
        exact sq_pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      simpa [hx] using hypos
    · have hxpos := hH.2 hx
      change 0 < x.sum (fun i xi ↦ x.sum (fun j xj ↦ xi * H i j * xj)) at hxpos
      exact add_pos_of_pos_of_nonneg hxpos
        (Finsupp.sum_nonneg fun i hi ↦ sq_nonneg (y i))

end EuclideanSpace.OrthogonalSum
