/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Algebra.Module.Submodule.Basic
-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Lemma 6.11 lies in the linear-algebra / submodule domain.

Primary mathematical domain:
- closure of a submodule under subtraction.

Sampled owner-style declarations:
- `Submodule.sub_mem` in mathlib, the canonical subtraction-closure theorem for a submodule;
- `Submodule.add_mem` in mathlib, the additive-closure companion on the same owner;
- `Submodule.neg_mem` in mathlib, the inverse-closure companion deriving subtraction closure.

Best owner abstraction:
- source-facing/core: a submodule `Q₂ : Submodule R M` together with the owner theorem
  `Submodule.sub_mem`;
- bridge/view: this numbered file, which is only a recall surface for that owner theorem.

Primitive data:
- a submodule `Q₂ : Submodule R M`;
- vectors `u`, `uHat : M`;
- membership hypotheses `hu : u ∈ Q₂` and `huHat : uHat ∈ Q₂`.

Derived API:
- the canonical conclusion `u - uHat ∈ Q₂`, provided directly by `Submodule.sub_mem`.

Source/core/bridge triage:
- source-facing: the textbook statement that `Q₂` is closed under subtraction;
- core/canonical: `Submodule.sub_mem`;
- bridge/view: this later numbered recall surface.

This file therefore does not keep a parallel theorem name `sub_mem_of_mem_Q2`: downstream files
should use `Q₂.sub_mem hu huHat` or `Submodule.sub_mem Q₂ hu huHat` directly.
-/

/- Lemma 6.11: for any `u, \hat u ∈ Q₂`, the difference `u - \hat u` also belongs to `Q₂`;
this is exactly the canonical subtraction-closure theorem for a submodule. -/
#check (Submodule.sub_mem : ∀ {R : Type u} {M : Type v}, [Ring R] → [AddCommGroup M] →
  [Module R M] → (Q₂ : Submodule R M) → {u uHat : M} → u ∈ Q₂ → uHat ∈ Q₂ → u - uHat ∈ Q₂)
