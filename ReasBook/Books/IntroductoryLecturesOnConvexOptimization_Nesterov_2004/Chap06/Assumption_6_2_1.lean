/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Assumption 6.2.1 lies in the chapter's fixed-parameter strong-convexity domain for the primal
smooth term.

Sampled owner-style declarations:
- project `S0On` with notation `𝒮^0_μ(Q)` in `Chap03/Definition_3_47`, the chapter's
  source-facing owner for positive-parameter strong convexity on a feasible set;
- project `mem_S0On_iff`, the source-facing specification theorem for that owner;
- project `StrongConvexOnClass.strongConvexOn`, the canonical projection from that owner to
  `StrongConvexOn`;
- mathlib `StrongConvexOn`, the ambient-norm core predicate reused throughout later chapters.

Best owner abstraction:
- source-facing: `hatf ∈ 𝒮^0_hatσ(Q₁)`;
- core/canonical: `StrongConvexOn Q₁ hatσ hatf`;
- bridge/view: `mem_S0On_iff`, which expands the source-facing owner to
  `0 < hatσ ∧ StrongConvexOn Q₁ hatσ hatf`.

Primitive data:
- the feasible set `Q₁`, the smooth part `hatf`, and the fixed modulus `hatσ`.

Derived API:
- positivity of the modulus `hatσ` via `StrongConvexOnClass.mu_pos`;
- the canonical core view `StrongConvexOn Q₁ hatσ hatf` via
  `StrongConvexOnClass.strongConvexOn`;
- the lower Chapter 2 `StrongConvexOnWith (normSeminorm ℝ E) ...` vocabulary only through the
  existing bridge already subsumed by the Chapter 3 owner.

Source/core/bridge triage:
- source-facing main entry: `hatf ∈ 𝒮^0_hatσ(Q₁)`;
- core/canonical companion: `StrongConvexOn Q₁ hatσ hatf`;
- bridge/view companion: `mem_S0On_iff`.

This numbered assumption adds no new mathematics beyond the chapter owner already introduced in
Definition 3.47, so this file now recalls that owner directly instead of centering the lower
ambient `StrongConvexOnWith (normSeminorm ...)` bridge.
-/

section

open scoped StrongConvex

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (Q₁ : Set E) (hatf : E → ℝ) (hatσ : ℝ)

/- Assumption 6.2.1 uses the chapter's source-facing fixed-parameter strong-convexity owner. -/
#check (hatf ∈ 𝒮^0_hatσ(Q₁))

/- The source-facing owner exposes the textbook form
`0 < hatσ ∧ StrongConvexOn Q₁ hatσ hatf`. -/
recall mem_S0On_iff

/- Membership in the chapter owner forces positivity of the fixed modulus. -/
recall StrongConvexOnClass.mu_pos

/- Membership in the chapter owner projects to the canonical core predicate `StrongConvexOn`. -/
recall StrongConvexOnClass.strongConvexOn

end

end
