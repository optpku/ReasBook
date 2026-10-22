/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_9_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqX_5_9_3 : DecidableEq X := Classical.decEq X

/-!
Primary domain: one-eighth small-cancellation relators and the conjugacy obstruction `J`.

Layer triage:
- `source-facing`: a chosen basis `basis : FreeGroupBasis X F`, a relator set `R : Set F`,
  the Chapter `5` small-cancellation hypothesis `C'(1 / 8)`, and the conclusion that no relator
  in `R` is conjugate to its inverse.
- `core/canonical`: `FreeGroupBasis.condition_c_prime`, written `C'(\lambda)[basis, R]`, is the
  chapter owner for the small-cancellation hypothesis, `Set.SatisfiesConditionJ`, written `J[R]`,
  is the owner predicate for the conclusion, and `IsConj` is the owner relation for conjugacy.
- `bridge/view`: this theorem is the direct bridge from the owner `C'((1 / 8 : ℝ))[basis, R]`
  to the already-owned predicate `J[R]`; it does not introduce a parallel wrapper for
  “not conjugate to its inverse”.

Domain sampling:
1. `FreeGroupBasis.condition_c_prime` from Definition `5-2-1` is the Chapter `5` owner for the
   `C'(\lambda)` hypothesis.
2. `Set.SatisfiesConditionJ` from Definition `5-9-7` is the owner predicate for the source
   condition that no relator is conjugate to its inverse.
3. `Set.not_isConj_inv` is the companion elimination lemma for `J[R]`, so the theorem should
   produce `J[R]` directly instead of a theorem with the same conclusion unpacked pointwise.
4. `IsConj` from mathlib is the canonical owner relation for conjugacy, so no explicit conjugator
   witness data belongs in the public interface.

Primitive vs. derived:
- primitive public data: the basis `basis`, the relator set `R`, the one-eighth
  small-cancellation hypothesis, and the nontriviality condition on relators in `R`;
- derived API: the owner-level conclusion `J[R]`.
- API refinement note: the extra nontriviality hypothesis remains explicit because the current
  Chapter `5` owner `condition_c_prime` does not encode the textbook convention that relators are
  already nontrivial cyclically reduced words.
-/

namespace FreeGroupBasis

-- Proof sketch: if some `r ∈ R` were conjugate to `r⁻¹`, pass to a cyclically reduced conjugate
-- of `basis.repr r`, compare it with the inverse cyclic word, and apply the Section `9`
-- one-eighth overlap estimate to obtain a common subword longer than half the relator length.
-- The nontriviality hypothesis rules out the degenerate empty-word case, and the overlap bound
-- contradicts the `C'(1 / 8)` piece inequality.
/-- Theorem 5-9-3: if the relator set `R` satisfies `C'(1 / 8)` with respect to `basis`, and no
relator in `R` is trivial, then `R` satisfies Condition `J`; equivalently, no relator in `R` is
conjugate to its inverse. -/
theorem satisfiesConditionJ_of_condition_c_prime_one_eighth
    (basis : FreeGroupBasis X F) (R : Set F) (hR : C'((1 / 8 : ℝ))[basis, R])
    (hrel_ne_one : ∀ ⦃r : F⦄, r ∈ R → r ≠ 1) :
    J[R] := by
  intro r hr
  have _hr_ne_one : r ≠ 1 := hrel_ne_one hr
  sorry

end FreeGroupBasis

end
