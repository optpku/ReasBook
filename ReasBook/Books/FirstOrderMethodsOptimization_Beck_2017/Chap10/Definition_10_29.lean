/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Definition 10.29 is a `bridge/view` item in the Chapter 10 Moreau-smoothing API.
Domain sampling identifies the owner abstraction and the primitive/derived split:

- `moreau_envelope` from Definition 6.7 is the `core/canonical` owner `M[μ, f]`;
- `moreau_envelope_apply` is the owner's canonical pointwise infimum formula;
- `Function.toEReal` from Definition 9.2 is the canonical bridge from a real-valued function `h`
  to the extended-real input expected by `M[μ, f]`.

The primitive data are only the smoothing parameter `μ` and the real-valued function `h`. The
numbered item adds no new owner-level construction beyond the specialization `M[μ, h.toEReal]`,
so this file should present that specialized chapter object directly rather than recalling only the
generic ingredients or reintroducing a parallel wrapper. -/

section

variable {E : Type u} [NormedAddCommGroup E]
variable (μ : PosReal) (h : E → ℝ)

/- Definition 10.29: for a real-valued function `h`, the Chapter 10 Moreau smoothing is exactly
the specialized Chapter 6 owner `M[μ, h.toEReal]`. -/
#check M[μ, h.toEReal]

end

section

variable {E : Type u} [NormedAddCommGroup E]
variable (μ : PosReal) (h : E → ℝ) (x : E)

/- Its pointwise formula is the corresponding specialization of
`moreau_envelope_apply` to `h.toEReal`. -/
#check
  (by
    simpa using (moreau_envelope_apply μ h.toEReal x) :
      M[μ, h.toEReal] x =
        ⨅ u : E, (h u : EReal) + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal))

end
