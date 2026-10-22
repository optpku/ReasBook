/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g ω : E → EReal}

/- Definition 10.68 is `source-facing` in the Chapter 10 non-Euclidean proximal-gradient API, but
it adds no new owner beyond the composite-model specialization already isolated in Definition 9.5.
Domain sampling identifies:
- Definition 9.2's `IsBregmanPotentialOn` as the `core/canonical` owner of the Bregman-potential
  data;
- Definition 9.5 as the existing `source-facing` specialization to the feasible set
  `dom(g) = effective_domain g`;
- Algorithm 10.69 and Theorem 10.72 as direct downstream users of exactly the modulus-`1`
  specialization.

Primitive data therefore remain only `ω`, `g`, and the fixed modulus `1`; Hilbert and
finite-dimensional structure are not part of this assumption package. The correct main entry is the
existing specialized type expression, not a Chapter 10 wrapper class parallel to Chapter 9. -/

/- Definition 10.68: Assumption 10.78 for the proximal gradient method is exactly that `ω` is a
Bregman potential on `dom(g) = effective_domain g` with strong-convexity modulus `1`. -/
#check (IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))

end
