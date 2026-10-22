/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {m : ℕ} (E : Fin m → Type u) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/- Definition 1.35 is recall-only: the Cartesian product of finitely many real inner product
spaces is canonically modeled in Lean by the `L²` product `PiLp (2 : ENNReal) E`. The ambient
vector-space structure is pointwise, and the inner product is the sum of the component inner
products. -/
#check (PiLp (2 : ENNReal) E)

/- Componentwise addition in the Cartesian product is the canonical `PiLp.add_apply` formula. -/
recall PiLp.add_apply

/- Componentwise scalar multiplication in the Cartesian product is the canonical
`PiLp.smul_apply` formula. -/
recall PiLp.smul_apply

/- The inner product on the Cartesian product is the sum of the component inner products. -/
recall PiLp.inner_apply

end
