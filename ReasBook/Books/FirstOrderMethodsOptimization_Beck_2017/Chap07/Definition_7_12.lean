/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/-- Definition 7.12: the spectahedron `γ[n]` is the set of positive semidefinite real `n × n`
matrices with trace equal to `1`. -/
def spectahedron (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.PosSemidef ∩ {X | Matrix.trace X = 1}

notation "γ[" n "]" => spectahedron n

-- Proof sketch: unfold `spectahedron`, identify membership in `Matrix.PosSemidef` with the
-- positive-semidefinite condition, and simplify membership in the trace-one slice.
/-- Membership in the spectahedron means positive semidefiniteness together with unit trace. -/
theorem mem_spectahedron_iff (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ γ[n] ↔ X.PosSemidef ∧ Matrix.trace X = 1 := by
  -- The notation expands directly to the intersection of the two defining constraints.
  rfl

end
