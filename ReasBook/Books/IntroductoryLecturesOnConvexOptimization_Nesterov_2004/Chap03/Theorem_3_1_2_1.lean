/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.1.2.1 is recall-only in the chapter's `ClosedConvexOn` owner API.

Primary domain:
- closure properties of closed convex `WithTop ℝ`-valued functions on a feasible set in a real
  topological module.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.nonneg_smul` from `Theorem_3_1_5`
- `ClosedConvexOn.add_inter` from `Theorem_3_1_5`
- `ClosedConvexOn.max_inter` from `Theorem_3_1_5`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witnesses `hf`, `hf₁`, `hf₂`
- the nonnegative scalar `β`

Derived API:
- `ClosedConvexOn.nonneg_smul`
- `ClosedConvexOn.add_inter`
- `ClosedConvexOn.max_inter`

Source/core/bridge triage:
- source-facing: the three closure properties recorded under Theorem 3.1.2.1
- core/canonical: the owner namespace `ClosedConvexOn`
- bridge/view: this later numbered file, which now directly recalls the owner theorems instead of
  introducing parallel aliases `smul_nonneg`, `add`, and `max`

The earlier file `Theorem_3_1_5` already owns these exact closure operations with the chapter's
canonical names. This file therefore reuses those owner entries directly rather than keeping a
second public vocabulary for the same mathematics.
-/

recall ClosedConvexOn.nonneg_smul
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) :
    ClosedConvexOn Q ((β : WithTop ℝ) • f)

recall ClosedConvexOn.add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ + f₂)

recall ClosedConvexOn.max_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ ⊔ f₂)

end
