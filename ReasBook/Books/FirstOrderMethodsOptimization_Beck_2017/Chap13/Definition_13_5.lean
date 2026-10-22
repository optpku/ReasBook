/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 13.5 lives in the Chapter 13 conditional-gradient domain.

Domain sampling of the existing project owners shows:
- `generalized_conditional_gradient_argmin` in Definition 13.4 for the linearized subproblem;
- `generalized_conditional_gradient_gap_objective` in Text 13.2 for the gap-value objective;
- `generalized_conditional_gradient_norm` in Text 13.2 for the canonical conditional-gradient norm.

This file is therefore a `bridge/view` item. The owner abstraction is already the canonical norm
from Text 13.2. The only additional source-facing datum here is a chosen pointwise minimizer map
`p(x)`, which should be recorded as a selection property rather than as a second norm owner. -/

/- Definition 13.5: the chapter conditional-gradient quantity `S(x)` is the existing canonical
owner `S[f, g](x)`, i.e. `generalized_conditional_gradient_norm f g x`. A chosen search-point map
`p(x)` is handled below only as a bridge to that owner via pointwise argmin selection. -/
recall generalized_conditional_gradient_norm

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → EReal}

/-- A generalized conditional-gradient selection chooses, for every `x ∈ dom(f)`, a minimizer of
the linearized subproblem from Definition 13.4. -/
def IsGeneralizedConditionalGradientSelection
    (f g : E → EReal) (p : effective_domain f → E) : Prop :=
  ∀ x : effective_domain f,
    p x ∈ generalized_conditional_gradient_argmin (fun y ↦ (f y).toReal) g x

-- Proof sketch: apply `generalized_conditional_gradient_norm_eq_of_mem_argmin` from Text 13.2 to
-- the selected point `p x`, using the defining property of
-- `IsGeneralizedConditionalGradientSelection`.
/-- A chosen generalized conditional-gradient selection realizes the canonical norm from Text 13.2
as the gap objective evaluated at the selected minimizer. -/
theorem generalized_conditional_gradient_norm_eq_of_selection
    {p : effective_domain f → E}
    (hselection : IsGeneralizedConditionalGradientSelection f g p) (x : effective_domain f) :
    S[(fun y ↦ (f y).toReal), g](x) =
      generalized_conditional_gradient_gap_objective
        (fun y ↦ (f y).toReal) g x (p x) :=
  generalized_conditional_gradient_norm_eq_of_mem_argmin (hselection x)

end
