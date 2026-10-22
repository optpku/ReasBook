/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient

variable {X : Type u} [TopologicalSpace X] {x y : X}

/- Lemma 1.2.7 (1): constant paths are right units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `f.trans (Path.refl y)` equals the class of `f`. -/
recall trans_refl (γ : Path.Homotopic.Quotient x y) :
  trans γ (refl y) = γ

/- Lemma 1.2.7 (2): constant paths are left units up to endpoint-fixed homotopy, so for a path
`f : Path x y`, the class of `(Path.refl x).trans f` equals the class of `f`. -/
recall refl_trans (γ : Path.Homotopic.Quotient x y) :
  trans (refl x) γ = γ
