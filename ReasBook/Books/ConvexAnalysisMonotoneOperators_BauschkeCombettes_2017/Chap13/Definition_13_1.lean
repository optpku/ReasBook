/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Reflection

variable {H : Type u} [AddGroup H]

/-- The reflection of an extended-real-valued function is the precomposition `x ↦ f (-x)`. -/
def reverse (f : H → EReal) : H → EReal :=
  fun x ↦ f (-x)

/- Lean cannot use the textbook ASCII surface `f^∨` here. We therefore use the postfix vee token
`fᵛ` as the direct Lean surface for function reversal. -/
scoped postfix:max "ᵛ" => ERealFunction.reverse

/-- Evaluating the reflection rewrites it as the pointwise formula `f (-x)`. -/
@[simp] theorem reverse_apply (f : H → EReal) (x : H) :
    fᵛ x = f (-x) :=
  rfl

end Reflection

end ERealFunction

namespace Function

section Reflection

variable {H : Type u} [AddGroup H]

/-- The reflection of an `]-∞,+∞]`-valued function is the precomposition `x ↦ f (-x)`. -/
def reverse (f : H → Set.Ioi (⊥ : EReal)) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ f (-x)

/- Lean cannot use the textbook ASCII surface `f^∨` here either. We therefore reuse the postfix
vee token `fᵛ` as the direct Lean surface for reflection on `]-∞,+∞]`-valued functions. -/
scoped postfix:max "ᵛ" => Function.reverse

/-- Evaluating the reflection rewrites it as the pointwise formula `f (-x)`. -/
@[simp] theorem reverse_apply (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    fᵛ x = f (-x) :=
  rfl

end Reflection

end Function

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 13.1: the conjugate of an extended-real-valued function on a real inner-product
space is the function `u ↦ sup_x (⟪x, u⟫ - f x)`. -/
noncomputable def conjugate (f : H → EReal) : H → EReal :=
  fun u ↦ ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x

/- Lean cannot use the textbook ASCII surface `f^*` here: `^` is exponent syntax and `*` is the
multiplicative token. We therefore use the postfix star token `f∗` as the direct Lean surface for
Fenchel conjugation, so `f∗∗` is the biconjugate. -/
scoped postfix:max "∗" => ERealFunction.conjugate

/-- Evaluating the conjugate rewrites it as the supremum of the affine defects
`x ↦ ⟪x, u⟫ - f x`. -/
@[simp] theorem conjugate_apply (f : H → EReal) (u : H) :
    f∗ u = ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x :=
  rfl

end Conjugation

end ERealFunction
