/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {B : Type u} [TopologicalSpace B]

open Path.Homotopic.Quotient

/-- Construction 3.8.3: the universal-cover candidate over a basepoint `b` is the total space of
endpoint-fixed homotopy classes of paths in `B` starting at `b`, indexed by their endpoint. -/
abbrev universalCoverCandidate (b : B) : Type u :=
  Σ x : B, Path.Homotopic.Quotient b x

/-- The canonical sigma-point represented by a path has endpoint `f 1`. -/
-- Proof sketch: the first component of `⟨x, mk f⟩` is definitionally `x`, and `Path.target`
-- identifies `x` with `f 1`.
@[simp] theorem universalCoverCandidate_mk_fst_eq_endpoint (b : B) {x : B} (f : Path b x) :
    (⟨x, mk f⟩ : universalCoverCandidate b).1 = f 1 := by
  simp
