/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_55

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 10.57 is a `bridge/view` item. For a chosen smoothing parameter `μ > 0` and a
chosen `1 / μ`-smooth approximation `h_μ` of `h` with parameters `(α, β)`, the smoothed problem
(10.65) keeps the same Chapter 10 owner `composite_model_objective`, applied twice after coercing
the real-valued smooth terms to `EReal`.

Domain sampling identifies the owner abstraction and the primitive/derived split:
- `Function.toEReal` from Chapter 9 is the canonical coercion from real-valued smooth terms to the
  extended-real codomain;
- `composite_model_objective` from Definition 10.2 is the Chapter 10 owner for composite
  objectives;
- the explicit three-term evaluation and minimization rewrites are definitional consequences of the
  nested Chapter 10 owner from Definition 10.55, so this file should not introduce a second named
  specialization.

Primitive data here are only the three objective terms `f`, `h_μ`, and `g`; the source item adds
no new owner-level construction beyond the existing composite objective. -/

recall Function.toEReal
recall composite_model_objective
recall composite_model_objective_apply
recall isMinOn_composite_model_objective_iff

section

variable {E : Type u}
variable (f hμ : E → ℝ) (g : E → EReal) (x : E)

/- Definition 10.57: after choosing the smoothing `h_μ`, the smoothed problem (10.65) minimizes
the specialized three-term Chapter 10 objective `H[f.toEReal, hμ.toEReal, g]`. -/
#check H[f.toEReal, hμ.toEReal, g]

/- The evaluation formula for the smoothed objective is definitionally the specialized nested
Chapter 10 owner at `f`, `h_μ`, and `g`. -/
#check
  (rfl :
    H[f.toEReal, hμ.toEReal, g] x =
      (f x : EReal) + hμ x + g x)

/- The corresponding minimization statement is likewise a definitional specialization of the
nested Chapter 10 owner. -/
#check
  (Iff.rfl :
    IsMinOn H[f.toEReal, hμ.toEReal, g] Set.univ x ↔
      IsMinOn (fun y ↦ (f y : EReal) + hμ y + g y) Set.univ x)

end
