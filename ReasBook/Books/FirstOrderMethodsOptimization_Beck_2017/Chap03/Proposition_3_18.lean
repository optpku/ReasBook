/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_27
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_17

-- Declarations for this item will be appended below by the statement pipeline.

section

open WithLp (ofLp toLp)

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.18 is a `bridge/view` corollary in the chapter Euclidean subdifferential API.
Its source-facing coordinate description is already owned upstream by
`l1CoordinateSubgradientVectors`, together with the derived API
`sign_vector_mem_l1CoordinateSubgradientVectors`. The present item only transports that canonical
member through Proposition 3.17's owner-set identification
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. -/

-- Proof sketch: rewrite the target subdifferential through Proposition 3.17 and then use the
-- upstream owner-view lemma `sign_vector_mem_l1CoordinateSubgradientVectors`.
/-- Proposition 3.18: for `f(x) = ∑ i, |x i|` on `ℝ^n`, the coordinatewise sign vector `sgn(x)`
viewed in the dual via the Euclidean identification belongs to the subdifferential `∂ f(x)`. -/
theorem sign_vector_mem_subdifferentialAt_l1_norm
    (x : E) :
    toLp 2 (sgn (ofLp x)) ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖toLp 1 (ofLp y)‖) x := by
  rw [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints]
  exact ⟨sgn (ofLp x), sign_vector_mem_l1CoordinateSubgradientVectors (ofLp x), by simp⟩

end
