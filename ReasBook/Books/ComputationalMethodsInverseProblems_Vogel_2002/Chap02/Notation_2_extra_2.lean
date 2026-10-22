/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_6
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.Defs

public section

open scoped BigOperators InnerProductSpace
open Module

universe u v w

namespace Submodule

/- Mathlib's canonical Gram-matrix owner is `Matrix.gram`.
The book writes `[G]ᵢⱼ = ⟨φⱼ, φᵢ⟩` and `bᵢ = ⟨f, φᵢ⟩`; in mathlib's inner-product
convention this becomes `(Matrix.gram 𝕜 (fun i ↦ (φ i : E))) i j = ⟪(φ i : E), φ j⟫_𝕜`
and the right-hand side vector `fun i ↦ ⟪(φ i : E), f⟫_𝕜`.
-/
#check Matrix.gram

/-- Helper for Notation 2-extra-2: if `s - f ∈ Sᗮ`, then every `u : S` has the same inner
product with `s` as with `f`. -/
lemma inner_eq_inner_of_sub_mem_orthogonal
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (S : Submodule 𝕜 E) {f s : E} (horth : s - f ∈ Sᗮ) (u : S) :
    ⟪(u : E), s⟫_𝕜 = ⟪(u : E), f⟫_𝕜 := by
  -- Rewrite the orthogonality condition into the coefficient identity needed below.
  have hzero : ⟪(u : E), s - f⟫_𝕜 = 0 := S.inner_right_of_mem_orthogonal u.property horth
  simpa [inner_sub_right, sub_eq_zero] using hzero

/-- If `s ∈ S` and the residual `s - f` lies in `Sᗮ`, then the coordinates of `s` in a basis `φ`
satisfy the Gram-matrix normal equations. -/
theorem repr_solve_gram_of_sub_mem_orthogonal
    {𝕜 : Type u} {E : Type v} {ι : Type w} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (S : Submodule 𝕜 E) (φ : Basis ι 𝕜 S)
    {f s : E} (hs : s ∈ S) (horth : s - f ∈ Sᗮ) :
    Matrix.mulVec (Matrix.gram 𝕜 (fun i ↦ (φ i : E))) (fun i ↦ φ.repr ⟨s, hs⟩ i) =
      fun i ↦ ⟪(φ i : E), f⟫_𝕜 := by
  ext i
  -- Expand `s` in the basis `φ`, but work in the ambient space `E`.
  have hinner :
      ⟪(φ i : E), ↑(∑ j, φ.repr ⟨s, hs⟩ j • φ j : S)⟫_𝕜 = ⟪(φ i : E), s⟫_𝕜 := by
    exact congrArg (fun x : S => ⟪(φ i : E), (x : E)⟫_𝕜) (φ.sum_repr ⟨s, hs⟩)
  -- Orthogonality of `s - f` replaces the coefficient target `⟪φ i, s⟫` by `⟪φ i, f⟫`.
  -- The left side is the `i`th entry of the Gram-matrix system, so the proof is a short `calc`.
  calc
    (Matrix.mulVec (Matrix.gram 𝕜 (fun j ↦ (φ j : E))) (fun j ↦ φ.repr ⟨s, hs⟩ j)) i =
        ⟪(φ i : E), ↑(∑ j, φ.repr ⟨s, hs⟩ j • φ j : S)⟫_𝕜 := by
      calc
        (Matrix.mulVec (Matrix.gram 𝕜 (fun j ↦ (φ j : E))) (fun j ↦ φ.repr ⟨s, hs⟩ j)) i =
            ∑ j, ⟪(φ i : E), (φ j : E)⟫_𝕜 * φ.repr ⟨s, hs⟩ j := by
          simp [Matrix.mulVec, dotProduct, Matrix.gram_apply]
        _ = ∑ j, φ.repr ⟨s, hs⟩ j * ⟪(φ i : E), (φ j : E)⟫_𝕜 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [mul_comm]
        _ = ⟪(φ i : E), ↑(∑ j, φ.repr ⟨s, hs⟩ j • φ j : S)⟫_𝕜 := by
          rw [Submodule.coe_sum]
          simp only [Submodule.coe_smul_of_tower]
          symm
          simp only [inner_sum, inner_smul_right]
    _ = ⟪(φ i : E), s⟫_𝕜 := hinner
    _ = ⟪(φ i : E), f⟫_𝕜 := inner_eq_inner_of_sub_mem_orthogonal S horth (φ i)

/-- Notation 2-extra-2 (1). For a basis `φ` of a subspace `S`, the coordinate vector of a best
approximation `hsStar : S.IsBestApproximation f sStar` solves the Gram-matrix normal equations. -/
theorem bestApproximation_repr_solve_gram
    {𝕜 : Type u} {E : Type v} {ι : Type w} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (S : Submodule 𝕜 E) (φ : Basis ι 𝕜 S)
    {f sStar : E} (hsStar : S.IsBestApproximation f sStar) :
    Matrix.mulVec (Matrix.gram 𝕜 (fun i ↦ (φ i : E))) (fun i ↦ φ.repr ⟨sStar, hsStar.mem⟩ i) =
      fun i ↦ ⟪(φ i : E), f⟫_𝕜 :=
  repr_solve_gram_of_sub_mem_orthogonal S φ hsStar.mem
    (sub_mem_orthogonal_of_bestApproximation S hsStar)

/-- If `s ∈ S` and the residual `s - f` lies in `Sᗮ`, then an orthonormal basis `φ` of `S`
expands `s` using the coefficients `⟪φ i, f⟫_𝕜`. -/
theorem eq_sum_inner_orthonormalBasis_of_sub_mem_orthogonal
    {𝕜 : Type u} {E : Type v} {ι : Type w} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (S : Submodule 𝕜 E)
    (φ : OrthonormalBasis ι 𝕜 S) {f s : E} (hs : s ∈ S) (horth : s - f ∈ Sᗮ) :
    s = ∑ i, ⟪(φ i : E), f⟫_𝕜 • (φ i : E) := by
  -- Expand `s` in the orthonormal basis of `S` and transport the identity to `E`.
  have hsum : ((↑(∑ i, ⟪φ i, ⟨s, hs⟩⟫_𝕜 • φ i : S) : E) = s) := by
    exact congrArg (fun x : S => (x : E)) (φ.sum_repr' ⟨s, hs⟩)
  -- Replace each coefficient using orthogonality of the residual.
  calc
    s = (↑(∑ i, ⟪φ i, ⟨s, hs⟩⟫_𝕜 • φ i : S) : E) := hsum.symm
    _ = ∑ i, ⟪(φ i : E), s⟫_𝕜 • (φ i : E) := by simp
    _ = ∑ i, ⟪(φ i : E), f⟫_𝕜 • (φ i : E) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [inner_eq_inner_of_sub_mem_orthogonal S horth (φ i)]

/-- Notation 2-extra-2 (2). For an orthonormal basis `φ` of a subspace `S`, a best approximation
`hsStar : S.IsBestApproximation f sStar` is the sum of the basis vectors weighted by the inner
products `⟪φ i, f⟫_𝕜`. -/
theorem bestApproximation_eq_sum_inner_orthonormalBasis
    {𝕜 : Type u} {E : Type v} {ι : Type w} [Fintype ι] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (S : Submodule 𝕜 E)
    (φ : OrthonormalBasis ι 𝕜 S) {f sStar : E} (hsStar : S.IsBestApproximation f sStar) :
    sStar = ∑ i, ⟪(φ i : E), f⟫_𝕜 • (φ i : E) :=
  eq_sum_inner_orthonormalBasis_of_sub_mem_orthogonal S φ hsStar.mem
    (sub_mem_orthogonal_of_bestApproximation S hsStar)

end Submodule
