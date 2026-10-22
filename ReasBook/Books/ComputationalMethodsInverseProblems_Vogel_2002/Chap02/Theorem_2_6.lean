/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_extra_1

public section

universe u v

namespace Submodule

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Theorem 2.6. If `sStar` is a best approximation to `f` from a subspace `S`, then
`⟪sStar - f, s⟫_𝕜 = 0` whenever `s ∈ S`. -/
theorem inner_eq_zero_of_bestApproximation
    (S : Submodule 𝕜 E) {f sStar s : E} (hsStar : S.IsBestApproximation f sStar)
    (hs : s ∈ S) :
    inner 𝕜 (sStar - f) s = 0 := by
  have hs0 : inner 𝕜 (f - sStar) s = 0 :=
    (S.norm_eq_iInf_iff_inner_eq_zero hsStar.mem).1 hsStar.norm_eq_iInf s hs
  have hsub : sStar - f = -(f - sStar) := by
    simp [sub_eq_add_neg]
  calc
    inner 𝕜 (sStar - f) s = inner 𝕜 (-(f - sStar)) s := by rw [hsub]
    _ = -inner 𝕜 (f - sStar) s := inner_neg_left _ _
    _ = 0 := by simp [hs0]

/-- Canonical orthogonality form of Theorem 2.6: the best-approximation error lies in `Sᗮ`. -/
theorem sub_mem_orthogonal_of_bestApproximation
    (S : Submodule 𝕜 E) {f sStar : E} (hsStar : S.IsBestApproximation f sStar) :
    sStar - f ∈ Sᗮ := by
  rw [S.mem_orthogonal']
  intro s hs
  exact inner_eq_zero_of_bestApproximation S hsStar hs

end Submodule
