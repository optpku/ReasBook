/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_4_11
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_4_13

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

namespace BaumslagSolitar23

/-!
Primary domain: residual finiteness and Hopfianity for the Baumslag-Solitar group `BS(2,3)`.

Layer triage:
- `source-facing`: the textbook consequence that `BS(2,3)` is not residually finite.
- `core/canonical`: `Group.ResiduallyFinite`, `IsHopfian`, the chapter theorem `not_isHopfian`,
  and the owner instance `isHopfian_of_fg_residuallyFinite`.
- `bridge/view`: this remark is the direct contradiction between those owner-level facts, so it
  should stay a thin theorem rather than introducing a new endomorphism-level wrapper.

Domain sampling:
1. `Group.ResiduallyFinite` is mathlib's owner predicate for residual finiteness.
2. `IsHopfian` from Proposition `1-3-5` is the chapter owner predicate for Hopfianity.
3. `not_isHopfian` from Theorem `4-4-11` is the canonical non-Hopfianity result for `BS(2,3)`.
4. `isHopfian_of_fg_residuallyFinite` from Theorem `4-4-13` is the canonical owner instance
   turning finite generation and residual finiteness into Hopfianity.

Primitive vs. derived:
the only new public content here is the source-facing failure of residual finiteness. The Hopfian
instance and the non-Hopfian counterexample already live upstream, so the remark should expose only
their direct owner-level consequence.
-/

/-- Remark 4-4-12: the Baumslag-Solitar group `⟨ b, t ; t⁻¹ b^2 t = b^3 ⟩` is not residually
finite. -/
theorem not_residuallyFinite : ¬ Group.ResiduallyFinite Group := by
  intro hRF
  letI : Group.ResiduallyFinite Group := hRF
  exact not_isHopfian inferInstance

end BaumslagSolitar23
