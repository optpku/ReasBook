/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {m : ℕ} (E : Fin m → Type u) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]

/- Definition 1.38 is recall-only: once Definition 1.35 identifies the Cartesian product of the
Euclidean spaces `E i` with `PiLp (2 : ENNReal) E`, the remaining Euclidean-space structure is
owned by mathlib through the canonical finite-dimensionality instance below and the canonical `L²`
norm formula `PiLp.norm_eq_of_L2`. -/
#check (inferInstance : FiniteDimensional ℝ (PiLp (2 : ENNReal) E))

/- The norm on the finite Cartesian product is the canonical `L²` norm formula. -/
recall PiLp.norm_eq_of_L2

end
