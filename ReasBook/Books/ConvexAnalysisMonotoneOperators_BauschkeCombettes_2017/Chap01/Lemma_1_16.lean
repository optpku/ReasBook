/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter

namespace Net

variable {A : Type u} [Preorder A]

/-- Lemma 1.16: if two extended-real-valued nets have lower limits strictly above `-∞`, then the
sum of their lower limits is bounded above by the lower limit of their pointwise sum. -/
-- Proof sketch: keep the source's hypotheses `liminf ξ > -∞` and `liminf η > -∞` in the
-- statement, then specialize the stronger canonical `EReal.le_liminf_add` theorem to the net
-- filter `atTop`.
theorem le_liminf_add [IsDirectedOrder A] (ξ η : A → EReal)
    (_hξ : (⊥ : EReal) < liminf ξ atTop) (_hη : (⊥ : EReal) < liminf η atTop) :
    liminf ξ atTop + liminf η atTop ≤ liminf (ξ + η) atTop := by
  simpa using
    (EReal.le_liminf_add :
      liminf ξ atTop + liminf η atTop ≤ liminf (ξ + η) atTop)

end Net
