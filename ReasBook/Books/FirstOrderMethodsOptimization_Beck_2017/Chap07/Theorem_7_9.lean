/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ}

/- Theorem 7.9 is `source-facing` in the Chapter 7 symmetry API. The relevant owner declarations
are Chapter 7's `IsSymmetricFunction` for symmetry under a family of orthogonal matrices and
Chapter 4's `conjugate_function` for Fenchel conjugates. The owner abstraction stays on the
textbook coordinate model `ℝ^n`, with orthogonal matrices acting by `mulVec`. -/

/-- Helper for Theorem 7.9: moving an orthogonal matrix from the second dot-product input to the
first input amounts to applying the matrix itself. -/
private lemma dotProduct_transpose_mulVec_eq_dotProduct_smul
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (y z : Fin n → ℝ) :
    dotProduct y ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) =
      dotProduct (A • y) z := by
  -- Rewrite the left pairing by moving the transpose to the first vector.
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- Helper for Theorem 7.9: an orthogonal matrix followed by its transpose acts as the identity on
`ℝ^n`. -/
private lemma orthogonal_mulVec_transpose_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) :
    (A : Matrix (Fin n) (Fin n) ℝ).mulVec
        ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) = z := by
  -- Collapse the composition to the identity matrix using orthogonality.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin n) (Fin n) ℝ) *
        (A : Matrix (Fin n) (Fin n) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.9: the transpose of an orthogonal matrix is its inverse action on
`ℝ^n`. -/
private lemma theorem7_9_orthogonal_transpose_mulVec_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec
        ((A : Matrix (Fin n) (Fin n) ℝ).mulVec x) = x := by
  -- Collapse the transpose-after-action composition to the identity matrix.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin n) (Fin n) ℝ).transpose *
        (A : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.9: orthogonal precomposition preserves the range of the conjugate
integrand after the matching change of variables. -/
private lemma conjugate_integrand_range_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    Set.range
        (fun x : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - f (A • x)) =
      Set.range
        (fun z : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) - f z) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨A • x, ?_⟩
    simp only
    have hAx : A • x = (A : Matrix (Fin n) (Fin n) ℝ).mulVec x := rfl
    -- Route correction: use the transpose as the explicit inverse action for the change of
    -- variables, rather than searching for a subtype inverse on `Matrix.orthogonalGroup`.
    have hx :
        ((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec (A • x) = x := by
      rw [hAx]
      exact theorem7_9_orthogonal_transpose_mulVec_mulVec A x
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            (((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec (A • x)) : ℝ) :
            EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) (A • x) : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y (A • x))
    -- Rewrite the transformed pairing back to the original point `x`.
    rw [← hdot, hx]
  · rintro ⟨z, rfl⟩
    refine ⟨((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec z, ?_⟩
    simp only
    have hz : A • (A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z = z := by
      change (A : Matrix (Fin n) (Fin n) ℝ).mulVec
          (((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec z) = z
      exact orthogonal_mulVec_transpose_mulVec A z
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) : ℝ) : EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y z)
    -- The transpose-preimage reproduces the target integrand exactly.
    rw [hdot, hz]

/-- Helper for Theorem 7.9: precomposing by an orthogonal matrix transports the conjugate point by
that same matrix. -/
lemma theorem7_9_conjugate_function_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    conjugate_function (fun x : Fin n → ℝ ↦ f (A • x))
        (dotProductEquiv ℝ (Fin n) y) =
      conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) := by
  -- Unfold the conjugate and replace the defining range by the orthogonal change of variables.
  rw [conjugate_function_apply, conjugate_function_apply,
    conjugate_integrand_range_precompose_orthogonal_eq]

-- Proof sketch: fix `A ∈ 𝒜`. Apply the conjugate change-of-variables formula to the linear map
-- `x ↦ A.mulVec x`. The hypothesis `hf` identifies `f ∘ A` with `f`, and orthogonality shows that
-- the Euclidean dual vector corresponding to `A.mulVec y` is exactly the pullback of the dual
-- vector corresponding to `y`. Rewriting the transformed conjugate with these two facts gives the
-- required invariance.
/-- Theorem 7.9: if `f` is symmetric with respect to `𝒜`, then its Fenchel conjugate, viewed on
`ℝ^n` through `dotProductEquiv`, is invariant under every orthogonal matrix in `𝒜`. -/
theorem conjugate_function_eq_conjugate_function_orthogonal_mulVec
    (𝒜 : Set (Matrix.orthogonalGroup (Fin n) ℝ)) (f : (Fin n → ℝ) → EReal)
    (hf : IsSymmetricFunction 𝒜 f) :
    ∀ A : Matrix.orthogonalGroup (Fin n) ℝ, A ∈ 𝒜 →
      ∀ y : Fin n → ℝ,
        conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) =
          conjugate_function f (dotProductEquiv ℝ (Fin n) y) := by
  intro A hA y
  have hpre : (fun x : Fin n → ℝ ↦ f (A • x)) = f := by
    -- Symmetry identifies the orthogonal precomposition of `f` with `f` itself.
    ext x
    exact hf.map_smul A hA x
  calc
    conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) =
        conjugate_function (fun x : Fin n → ℝ ↦ f (A • x))
          (dotProductEquiv ℝ (Fin n) y) := by
          symm
          exact theorem7_9_conjugate_function_precompose_orthogonal_eq A f y
    _ = conjugate_function f (dotProductEquiv ℝ (Fin n) y) := by
          rw [hpre]

end
