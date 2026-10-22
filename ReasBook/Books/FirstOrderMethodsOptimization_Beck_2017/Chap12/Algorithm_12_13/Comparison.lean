/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_7

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Comparison bridge for Algorithm 12.13: the duplicated-block Chapter 12.2 primal argmax
condition is equivalent to the source-facing block-sum argmax condition. -/
theorem mem_dual_primal_x_argmax_duplication_iff
    {n : ℕ}
    {f : E → EReal} {x : E} {v : Fin n → E} :
    x ∈
        dual_proximal_gradient_primal_x_argmax
          f
          (dual_block_duplication E n).toLinearMap
          (WithLp.toLp 2 v) ↔
      x ∈ dual_proximal_gradient_primal_x_argmax f LinearMap.id (∑ i : Fin n, v i) := by
  rw [mem_dual_proximal_gradient_primal_x_argmax_iff,
    mem_dual_proximal_gradient_primal_x_argmax_iff]
  have hadj := by
    simpa using
      dual_block_duplication_linear_adjoint_apply (E := E) (p := n) (WithLp.toLp 2 v)
  constructor <;> intro hx <;> simpa [dual_block_duplication, hadj] using hx

end
