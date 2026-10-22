/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

section

variable {H : Type u} [Group H]

/-!
Primary domain: subgroup combinatorics in small cancellation theory over amalgamated products and
HNN extensions.

Layer triage:
- `source-facing`: a subgroup `A ≤ H` together with two elements `x₁, x₂ : H` forming the
  textbook blocking pair.
- `core/canonical`: `Subgroup H` is the owner abstraction for `A`, and the condition is a
  `Prop`-valued structure on the displayed elements rather than a second packaged owner.
- `bridge/view`: the unordered pair `{x₁, x₂}` is rendered by the two-point set
  `({x₁, x₂} : Set H)`, and the signs `±1` are rendered by the canonical sign type `ℤˣ`,
  coerced to integer exponents in powers.

Domain sampling:
1. `Subgroup H` is mathlib's canonical owner for subgroup-valued data in a group.
2. `({x₁, x₂} : Set H)` is the canonical set-theoretic rendering of the unordered pair
   `{x₁, x₂}`.
3. `ℤˣ` is the project's canonical carrier for the source signs `±1`, and the group-theoretic
   powers use the coerced exponents `y ^ (ε : ℤ)`.
4. Existing chapter predicates such as `Subgroup.IsBenign` are stated directly on the subgroup
   owner rather than through a parallel wrapper structure on the ambient group.

Primitive vs. derived:
- primitive public data: the subgroup `A` and the elements `x₁`, `x₂`;
- primitive source conditions: `x₁ ≠ x₂`, `x₁ ∉ A`, `x₂ ∉ A`, and the blocking condition for
  every nontrivial `a ∈ A`;
- derived API: consequences such as any element of `{x₁, x₂}` lying outside `A`.
-/

namespace Subgroup

/-- Definition 5-11-8: `{x₁, x₂}` is a blocking pair for the subgroup `A ≤ H` if `x₁ ≠ x₂`,
neither `x₁` nor `x₂` belongs to `A`, and for every nontrivial `a ∈ A`, every choice of
`y, z ∈ {x₁, x₂}`, and every signs `ε, δ : ℤˣ`, the element
`y ^ (ε : ℤ) * a * z ^ (δ : ℤ)` does not belong to `A`. -/
structure IsBlockingPair (A : Subgroup H) (x₁ x₂ : H) : Prop where
  /-- The two displayed elements of a blocking pair are distinct. -/
  distinct : x₁ ≠ x₂
  /-- Every element of the displayed pair lies outside the subgroup. -/
  not_mem {x : H} (hx : x ∈ ({x₁, x₂} : Set H)) : x ∉ A
  /-- No signed sandwich `y^ε a z^δ` with nontrivial `a ∈ A`, `y, z ∈ {x₁, x₂}`, and
  signs `ε, δ : ℤˣ` returns to `A`. -/
  blocked {a y z : H} (ha : a ∈ A) (ha_ne_one : a ≠ 1)
      (hy : y ∈ ({x₁, x₂} : Set H)) (hz : z ∈ ({x₁, x₂} : Set H))
      (ε δ : ℤˣ) : y ^ (ε : ℤ) * a * z ^ (δ : ℤ) ∉ A

/-- Any element of the pair underlying a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.not_mem_of_mem_pair
    {A : Subgroup H} {x₁ x₂ x : H} (h : A.IsBlockingPair x₁ x₂)
    (hx : x ∈ ({x₁, x₂} : Set H)) :
    x ∉ A :=
  h.not_mem hx

/-- The left entry of a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.left_not_mem
    {A : Subgroup H} {x₁ x₂ : H} (h : A.IsBlockingPair x₁ x₂) :
    x₁ ∉ A :=
  h.not_mem_of_mem_pair (by simp)

/-- The right entry of a blocking pair lies outside the subgroup. -/
theorem IsBlockingPair.right_not_mem
    {A : Subgroup H} {x₁ x₂ : H} (h : A.IsBlockingPair x₁ x₂) :
    x₂ ∉ A :=
  h.not_mem_of_mem_pair (by simp)

end Subgroup

end
