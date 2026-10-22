/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

set_option autoImplicit false

open Subgroup

/-!
Primary domain: Bass-Serre type decompositions of groups with bipolar structures.

Layer triage:
- `source-facing`: a group admitting a bipolar structure, and the two alternative decompositions
  from the theorem, namely a nontrivial amalgamated free product or an HNN extension.
- `core/canonical`: `Nonempty (BipolarStructure G)`, `Subgroup.amalgamatedProductAlong`, and
  `HNNExtension G₀ A B φ`.
- `bridge/view`: a multiplicative equivalence from the ambient group onto one of those canonical
  owner constructions.

Domain sampling:
1. `BipolarStructure` from Definition `4-6-1` is the project owner for the bipolar axioms.
2. `Subgroup.amalgamatedProductAlong` from Definition `4-2-9` is the chapter-facing owner for a
   two-factor free product with amalgamation.
3. `HNNExtension G₀ A B φ` is mathlib's canonical owner abstraction for HNN extensions.
4. `MulEquiv` is the canonical API for identifying the ambient group with one of these
   constructions.

Primitive vs. derived:
the primitive public content is the ambient group `G` together with either a bipolar structure or
one of the two source-facing decomposition data sets appearing directly in the theorem statement.
The exact subgroup pieces and stable-letter data belong to those existential alternatives, while
the theorem itself is the direct equivalence between `Nonempty (BipolarStructure G)` and
admitting one of the two canonical owner-level decomposition types.
-/

section

/-- Theorem 4-6-5: a group has a bipolar structure if and only if it is either a nontrivial free
product with amalgamation, including the ordinary free product case, or an HNN extension. -/
-- Proof sketch: for the forward direction, build the subgroups `G₁` and `G₂` from the fixed part
-- and the irreducible sector pieces of a bipolar structure, then distinguish whether the sector
-- `EE*` is empty or not to obtain respectively an amalgamated-product or HNN-extension
-- decomposition. For the reverse direction, use the canonical bipolar structures constructed
-- earlier for amalgamated free products and for HNN extensions.
theorem nonempty_bipolarStructure_iff_nontrivialAmalgamatedFreeProduct_or_hnnExtension
    (G : Type u) [Group G] :
    Nonempty (BipolarStructure G) ↔
      (∃ (G₁ : Type v) (_ : Group G₁) (G₂ : Type w) (_ : Group G₂)
        (A : Subgroup G₁) (B : Subgroup G₂) (e : A ≃* B)
        (_ : G ≃* amalgamatedProductAlong e),
          A < ⊤ ∧ B < ⊤) ∨
      ∃ (G₀ : Type v) (_ : Group G₀) (A : Subgroup G₀) (B : Subgroup G₀) (φ : A ≃* B),
        Nonempty (G ≃* HNNExtension G₀ A B φ) := sorry

end
