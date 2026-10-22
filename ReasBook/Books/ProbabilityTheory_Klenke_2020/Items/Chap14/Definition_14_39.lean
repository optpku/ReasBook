/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ProbabilityTheory

namespace ProbabilityTheory

universe u v

variable {I : Type u} [Preorder I]
variable {E : Type v} [MeasurableSpace E]

/-- Definition 14.39: a family of kernels `(κ_{s,t})` indexed by strict inequalities `s < t` is
consistent if it satisfies the Chapman-Kolmogorov composition law with respect to the canonical
kernel composition from Definition 14.25, namely
`κ_{r,s} · κ_{s,t} = κ_{r,t}` for every `r < s < t`. -/
def IsConsistentKernelFamily (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) : Prop :=
  ∀ ⦃r s t : I⦄ (hrs : r < s) (hst : s < t),
    κ hst ∘ₖ κ hrs = κ (hrs.trans hst)

namespace IsConsistentKernelFamily

variable {κ : ∀ ⦃s t : I⦄, s < t → Kernel E E}

/-- In a consistent kernel family, composing the transition from `r` to `s` with the transition
from `s` to `t` recovers the direct transition from `r` to `t`. -/
theorem comp_eq (hκ : IsConsistentKernelFamily κ) {r s t : I} (hrs : r < s) (hst : s < t) :
    κ hst ∘ₖ κ hrs = κ (hrs.trans hst) :=
  hκ hrs hst

end IsConsistentKernelFamily

end ProbabilityTheory
