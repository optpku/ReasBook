/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Asymptotics

universe u

namespace Asymptotics

/- Definition 7.66 lies in filtered asymptotic-complexity estimates.

Sampled owner-style declarations:
- mathlib `Asymptotics.IsBigO`, the canonical Landau owner behind `f =O[l] g`;
- mathlib `Asymptotics.isBigO_iff`, the canonical existential expansion of `=O[l]`;
- mathlib `Asymptotics.IsBigO.trans`, the owner-level composition API used by nearby Chapter 7
  complexity bounds.

Best owner abstraction:
- source-facing: the Chapter 7 soft-`O` relation, which remembers a size parameter and allows an
  omitted polylogarithmic factor;
- core/canonical: `Asymptotics.IsBigO`;
- bridge/view: the definitional expansion below from soft-`O` to ordinary `O` after restoring a
  power of `log (size + 2)`.

Primitive data:
- a filter `l`;
- a size parameter `size : α → ℕ`;
- the compared functions `f g : α → ℝ`.

Derived API:
- the witness `logPower : ℕ`;
- the canonical `=O[l]` comparison after reinstating the logarithmic factor.

There is no upstream soft-`O` owner in mathlib, so this file keeps the source-facing notion, but
places it directly in the `Asymptotics` namespace because its mathematical core is an
`Asymptotics.IsBigO` statement rather than a Chapter-7-specific wrapper. -/

/-- Source-facing owner for Definition 7.66: a soft-`O` bound for `f` by `g` relative to a size
parameter `size` means that the corresponding `O` bound holds after reinstating some omitted
logarithmic factor, formalized here as a power of `log (size + 2)`. -/
def IsSoftBigO {α : Type u} (l : Filter α) (size : α → ℕ) (f g : α → ℝ) : Prop :=
  ∃ logPower : ℕ, f =O[l] fun x ↦ (Real.log ((size x : ℝ) + 2)) ^ logPower * g x

end Asymptotics

@[inherit_doc Asymptotics.IsSoftBigO]
notation:100 f " =Õ[" size:100 "; " l:100 "] " g:100 => Asymptotics.IsSoftBigO l size f g

namespace Asymptotics

/- Unfolding `Asymptotics.IsSoftBigO` is exactly the source-facing bridge back to the canonical
`Asymptotics.IsBigO` owner. -/
/-- Definition 7.66: unfolding `Asymptotics.IsSoftBigO l size f g` gives an ordinary `O`-bound
after restoring a power of the omitted logarithmic factor `log (size + 2)`. -/
-- Proof sketch: unfold `IsSoftBigO`.
theorem isSoftBigO_iff
    {α : Type u} {l : Filter α} {size : α → ℕ} {f g : α → ℝ} :
    IsSoftBigO l size f g ↔
      ∃ logPower : ℕ, f =O[l] fun x ↦ (Real.log ((size x : ℝ) + 2)) ^ logPower * g x := by
  -- Unfolding the soft-`O` owner reduces the theorem to the same existential `=O[l]` statement.
  rfl

end Asymptotics
