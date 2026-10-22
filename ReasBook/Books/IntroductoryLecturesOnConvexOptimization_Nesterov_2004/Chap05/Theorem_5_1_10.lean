/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.10 lies in the Chapter 5 self-concordance / Dikin-ellipsoid transport domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative Chapter 5 owner for
  self-concordance on a domain;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` from `Theorem_5_1_5`, the
  canonical owner theorem for the Dikin-inclusion clause;
* `IsSelfConcordantOnWith.displacement_localNorm_lower_bound` from `Theorem_5_1_5`, the canonical
  owner theorem for the lower transport inequality `(5.1.9)`;
* `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` from `Theorem_5_1_5`, the canonical
  owner theorem for the upper transport inequality `(5.1.10)`.

Source/core/bridge triage:
* source-facing: the three forward consequences of quantitative self-concordance appearing as the
  clauses of Theorem 5.1.10;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`;
* bridge/view: no new bridge layer is needed, because each clause already has the correct
  owner-level statement upstream.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, and an objective `f`;
* the owner hypothesis `IsSelfConcordantOnWith dom Mf f`.

Derived API:
* `W⁰[f; x](1 / (Mf : ℝ)) ⊆ dom`;
* the lower displacement transport inequality `(5.1.9)`;
* the upper displacement transport inequality `(5.1.10)`.

The previous version incorrectly replaced this source item by a stronger qualitative
characterization theorem for `IsSelfConcordantOn dom f`. The textbook content here is already
owned canonically by the three Chapter 5 methods below, so this file refines to direct recall of
those owner declarations instead of keeping a parallel wrapper theorem. -/

/- Theorem 5.1.10 (1) is the canonical Dikin-inclusion theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

/- Theorem 5.1.10 (2) is the canonical lower transport theorem
`IsSelfConcordantOnWith.displacement_localNorm_lower_bound`. -/
recall IsSelfConcordantOnWith.displacement_localNorm_lower_bound

/- Theorem 5.1.10 (3) is the canonical upper transport theorem
`IsSelfConcordantOnWith.displacement_localNorm_upper_bound`. -/
recall IsSelfConcordantOnWith.displacement_localNorm_upper_bound

end
