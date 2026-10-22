/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_51
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Corollary 10.52 is `source-facing` in the Chapter 10 smoothability API. The owner abstraction is
`is_smoothable_nonneg` from Definition 10.43, and the fixed-`μ` input is the ambient-space Moreau
envelope approximation theorem from Theorem 10.51. Since the textbook constant `ℓ_h^2 / 2` may
vanish, the faithful statement stays with the nonnegative-parameter owner rather than the strictly
positive variant. -/

-- Proof sketch: combine the ambient-space convexity and Lipschitz hypotheses with Theorem 10.51 to get,
-- for each `μ > 0`, the Moreau-envelope witness `hμ` with parameters
-- `(1, ℓ_h^2 / 2)`. Then package these witnesses into the `∀ μ` clause of
-- `is_smoothable_nonneg`.
/-- Corollary 10.52: on a real inner-product proper space, a convex real-valued function with
global Lipschitz constant `ℓ_h` is nonnegatively `(1, ℓ_h^2 / 2)`-smoothable. -/
theorem convex_lipschitz_is_one_lipschitz_sq_div_two_smoothable_nonneg
    (h : E → ℝ) (hconv : ConvexOn ℝ Set.univ h) (ℓh : NNReal) (hlip : LipschitzWith ℓh h) :
    is_smoothable_nonneg h 1 (ℓh ^ (2 : ℕ) / 2) := by
  intro μ
  exact ⟨_, moreau_envelope_real_is_smooth_approximation h hconv ℓh hlip μ⟩

end
