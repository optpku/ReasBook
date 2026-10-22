/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (ι : Type v) (E : Type u) [AddCommGroup E] [Module ℝ E]

/- Definition 1.5 (dimension): the owner notion is the cardinal-valued dimension `Module.rank ℝ E`.
For any basis of `E`, the canonical theorem `Module.Basis.mk_eq_rank` identifies the cardinality of
its index type with this rank. -/
#check Module.rank ℝ E
recall Module.Basis.mk_eq_rank

/- Definition 1.5 (finite-dimensionality): the textbook predicate is the standard vector-space
abbreviation `FiniteDimensional ℝ E`, i.e. the owner predicate `Module.Finite ℝ E`. -/
#check FiniteDimensional ℝ E

/- For real vector spaces, `Module.rank_lt_aleph0_iff` is the canonical bridge between
finite-dimensionality and the inequality `Module.rank ℝ E < ℵ₀`. -/
#check Module.rank_lt_aleph0_iff

end
