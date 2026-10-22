/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E} {μ : ℝ} {f : E → ℝ}

def S0On (μ : ℝ) (Q : Set E) : Set (E → ℝ) :=
  setOf (fun f ↦ 0 < μ ∧ StrongConvexOn Q μ f)

scoped[StrongConvex] notation "𝒮^0_" μ "(" Q ")" => S0On μ Q

open scoped StrongConvex

/- Definition 3.47 is a source-facing recall in the chapter's fixed-parameter strong-convexity
domain.

Primary domain:
* fixed-parameter strong convexity of real-valued functions on a feasible set

Sampled owner-style declarations:
* `StrongConvexOnWith` and `strongConvexOnWith_normSeminorm_iff` in
  `Nesterov.Chap02.Definition_2_14`
* mathlib `StrongConvexOn`
* `exists_pos_strongConvexOn_iff_forall_segment_upper_bound` in
  `Nesterov.Chap03.Definition_3_2_2`

Best owner abstraction:
* source-facing: the fixed-parameter class `𝒮^0_μ(Q)` as `f ∈ 𝒮^0_μ(Q)`
* core/canonical: `StrongConvexOn Q μ f`
* bridge/view: the Euclidean `StrongConvexOnWith` specialization from `Definition_2_14`

Primitive data:
* a feasible set `Q`
* a modulus `μ`
* an objective `f`

Derived API:
* positivity of the fixed modulus via membership in `𝒮^0_μ(Q)`
* convexity and the quadratic Jensen inequality carried by `StrongConvexOn`
* the positive-existential class `∃ μ > 0, StrongConvexOn Q μ f` from `Definition_3_2_2`

Source/core/bridge triage:
* source-facing: the textbook fixed-parameter class `𝒮^0_μ(Q)`
* core/canonical: `StrongConvexOn Q μ f`
* bridge/view: the Euclidean reformulation from `Definition_2_14` and the positive-existential
  restatement from `Definition_3_2_2`

The source semantics include `μ > 0`, so the public center here is the source-facing membership
surface `f ∈ 𝒮^0_μ(Q)`. The bare owner predicate `StrongConvexOn Q μ f` is retained only as the
canonical core companion. -/
#check (f ∈ 𝒮^0_μ(Q))

#check StrongConvexOn Q μ f

/-- The source-facing notation `𝒮^0_μ(Q)` is the set view of positive-parameter strong convexity
on `Q`. -/
@[simp] theorem mem_S0On_iff :
    f ∈ 𝒮^0_μ(Q) ↔ 0 < μ ∧ StrongConvexOn Q μ f :=
  Iff.rfl

namespace StrongConvexOnClass

/-- Membership in `𝒮^0_μ(Q)` forces positivity of the fixed strong-convexity parameter. -/
theorem mu_pos (hf : f ∈ 𝒮^0_μ(Q)) :
    0 < μ :=
  hf.1

/-- Membership in `𝒮^0_μ(Q)` includes the canonical strong-convexity owner on `Q`. -/
theorem strongConvexOn (hf : f ∈ 𝒮^0_μ(Q)) :
    StrongConvexOn Q μ f :=
  hf.2

end StrongConvexOnClass

namespace StrongConvexOn

/-- A positive strong-convexity witness gives source-facing membership in `𝒮^0_μ(Q)`. -/
theorem mem_S0On (hμ : 0 < μ) (hf : StrongConvexOn Q μ f) :
    f ∈ 𝒮^0_μ(Q) :=
  ⟨hμ, hf⟩

end StrongConvexOn

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {Q : Set E} {μ : ℝ} {f : E → ℝ}

open scoped StrongConvex

recall strongConvexOnWith_normSeminorm_iff

end
