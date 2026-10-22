/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_47

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 6.65 lies in the chapter's fixed-parameter strong-convexity domain.

Sampled owner-style declarations:
- project `S0On` with notation `𝒮^0_σ(Q)` in `Chap03/Definition_3_47`, the chapter's
  source-facing owner for positive-parameter strong convexity on a feasible set;
- project `mem_S0On_iff`, the specification theorem expanding that owner to
  `0 < σ ∧ StrongConvexOn Q σ Ψ`;
- mathlib `StrongConvexOn`, the canonical core predicate on a feasible set;
- project `strongConvexOn_iff_quadratic_jensen_bound` in `Chap02/Theorem_2_10`, the thin bridge
  from the core predicate to the textbook segment inequality.

Best owner abstraction:
- source-facing: `Ψ ∈ 𝒮^0_σΨ(Q)`;
- core/canonical: `StrongConvexOn Q σΨ Ψ`;
- bridge/view: `mem_S0On_iff` and `strongConvexOn_iff_quadratic_jensen_bound`.

Primitive data:
- the feasible set `Q`;
- the modulus `σΨ`;
- the objective `Ψ`.

Derived API:
- positivity of `σΨ` and the core predicate `StrongConvexOn Q σΨ Ψ`, via `mem_S0On_iff`;
- the quadratic Jensen inequality, via `strongConvexOn_iff_quadratic_jensen_bound`.

Source/core/bridge triage:
- source-facing main entry: `Ψ ∈ 𝒮^0_σΨ(Q)`;
- core/canonical companion: `StrongConvexOn Q σΨ Ψ`;
- bridge/view companions: `mem_S0On_iff` and `strongConvexOn_iff_quadratic_jensen_bound`.

The source semantics include the positivity condition `0 < σΨ`, already built into the chapter
owner `𝒮^0_σΨ(Q)`. This file therefore recalls that owner directly and keeps only the existing
specification and quadratic-Jensen bridges as companions, rather than centering the bare core
predicate `StrongConvexOn Q σΨ Ψ`.
-/

section

open scoped StrongConvex

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E} {σΨ : ℝ} {Ψ : E → ℝ}

/- Definition 6.65, owner form: the chapter's positive fixed-parameter strong-convexity class on
`Q`. -/
#check (Ψ ∈ 𝒮^0_σΨ(Q))

/- The source-facing owner expands to `0 < σΨ ∧ StrongConvexOn Q σΨ Ψ`. -/
recall mem_S0On_iff

/- On a convex set, the core predicate in `mem_S0On_iff` is equivalent to the textbook quadratic
Jensen inequality. -/
recall strongConvexOn_iff_quadratic_jensen_bound

end
