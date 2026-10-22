/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp

namespace Matrix

scoped syntax:max "‖" term "‖[" term "," term "]" : term
scoped macro_rules
  | `(‖$A‖[$a,$b]) => `(‖(($A).toLpLin $a $b).toContinuousLinearMap‖)

open scoped Matrix

section

variable {m n : ℕ}
variable (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
variable (A : Matrix (Fin m) (Fin n) ℝ)

/- Definition 1.34 is recall-only: the induced `(a,b)`-norm of a real matrix is the canonical
operator norm `‖A‖[a,b]` of the continuous linear map associated to the owner object
`Matrix.toLpLin a b`. -/
#check (‖A‖[a,b] : ℝ)

-- Proof sketch: apply `ContinuousLinearMap.unit_le_opNorm` to the continuous linear map induced by
-- `A`, then rewrite its value on a coordinate vector using `Matrix.toLpLin_toLp`.
/-- Every vector in the closed unit ball of the `a`-norm is sent to a vector whose `b`-norm is
bounded by the induced matrix norm. -/
theorem norm_mulVec_le_opNorm_toLpLin {x : Fin n → ℝ} (hx : ‖toLp a x‖ ≤ 1) :
    ‖toLp b (A *ᵥ x)‖ ≤ ‖A‖[a,b] := by
  simpa [toLpLin_toLp] using
    (A.toLpLin a b).toContinuousLinearMap.unit_le_opNorm (toLp a x) hx

-- Proof sketch: the closed unit ball in `WithLp a (Fin n → ℝ)` is compact, and the map induced by
-- `A.toLpLin a b` is continuous. Therefore it attains a maximum on that ball, and the preceding
-- bound identifies that maximum with `‖A‖[a,b]`.
/-- A vector in the closed unit ball of the `a`-norm realizes the induced `(a,b)`-norm. -/
theorem exists_norm_le_one_eq_opNorm_toLpLin :
    ∃ x : Fin n → ℝ,
      ‖toLp a x‖ ≤ 1 ∧ ‖A‖[a,b] = ‖toLp b (A *ᵥ x)‖ := by
  let f : WithLp a (Fin n → ℝ) →L[ℝ] WithLp b (Fin m → ℝ) :=
    (A.toLpLin a b).toContinuousLinearMap
  letI : FiniteDimensional ℝ (WithLp a (Fin n → ℝ)) :=
    (WithLp.linearEquiv a ℝ (Fin n → ℝ)).symm.finiteDimensional
  letI : ProperSpace (WithLp a (Fin n → ℝ)) :=
    FiniteDimensional.proper_real (WithLp a (Fin n → ℝ))
  have hcompact : IsCompact (Metric.closedBall (0 : WithLp a (Fin n → ℝ)) 1) :=
    isCompact_closedBall _ _
  have hnonempty : (Metric.closedBall (0 : WithLp a (Fin n → ℝ)) 1).Nonempty := ⟨0, by simp⟩
  have hnorm : ContinuousOn (fun z : WithLp a (Fin n → ℝ) ↦ ‖f z‖) (Metric.closedBall 0 1) := by
    let hf : Continuous fun z : WithLp a (Fin n → ℝ) ↦ ‖f z‖ := f.continuous.norm
    simpa using hf.continuousOn
  obtain ⟨y, hy, hySup⟩ :=
    hcompact.exists_sSup_image_eq hnonempty hnorm
  refine ⟨y.ofLp, ?_, ?_⟩
  · simpa using hy
  · calc
      ‖A‖[a,b] = ‖f‖ := rfl
      _ = sSup ((fun z : WithLp a (Fin n → ℝ) ↦ ‖f z‖) '' Metric.closedBall 0 1) := by
        symm
        exact ContinuousLinearMap.sSup_unitClosedBall_eq_norm f
      _ = ‖f y‖ := hySup
      _ = ‖toLp b (A *ᵥ y.ofLp)‖ := by
        change ‖A.toLpLin a b y‖ = ‖toLp b (A *ᵥ y.ofLp)‖
        rw [toLpLin_apply]

end

end Matrix
