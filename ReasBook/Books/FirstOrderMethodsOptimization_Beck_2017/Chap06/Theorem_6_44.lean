/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_45

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Theorem 6.44 is `source-facing` in the proximal-operator chapter, but in the local
Moreau-decomposition API the reusable owner theorem is the scaled identity
`prox_scaled_conjugate_sum_eq_singleton` from Theorem 6.45. The present file should therefore keep
only the exact textbook `λ = 1` specialization on the canonical owners `prox[...]` and `f∗`,
with the same proper-space owner assumptions rather than the stronger finite-dimensional proof
model. -/
recall conjugate_function_primal
recall prox_scaled_conjugate_sum_eq_singleton

-- Proof sketch: specialize the scaled Moreau decomposition from Theorem 6.45 at `λ = 1`. The
-- scaling terms then simplify definitionally to the unscaled proximal sets of `f` and `f∗`.
/-- Theorem 6.44: Moreau decomposition. On a proper real inner product space, for a proper closed
convex function `f`, after identifying the Fenchel conjugate with the source-facing primal-space
surface `f∗`, the pointwise sum of the proximal sets of `f` and `f∗` at `x` is the singleton
`{x}`. This is the set-valued owner-level rendering of `prox_f(x) + prox_{f^*}(x) = x`. -/
theorem prox_conjugate_sum_eq_singleton
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    prox[f] x + prox[(f∗)] x = {x} := by
  simpa using
    prox_scaled_conjugate_sum_eq_singleton
      f hf_proper hf_closed hf_convex (1 : PosReal) x

end
