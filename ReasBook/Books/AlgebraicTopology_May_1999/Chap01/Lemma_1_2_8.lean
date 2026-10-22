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

/- Lemma 1.2.8 (1): a path class followed by its reverse is endpoint-fixed homotopic to the
constant path at the starting point, so for `γ : Path.Homotopic.Quotient x y`,
`γ.trans γ.symm = refl x`. -/
recall trans_symm (γ : Path.Homotopic.Quotient x y) :
  γ.trans γ.symm = refl x

/- Lemma 1.2.8 (2): the reverse of a path class followed by the original path class is
endpoint-fixed homotopic to the constant path at the endpoint, so for
`γ : Path.Homotopic.Quotient x y`, `γ.symm.trans γ = refl y`. -/
recall symm_trans (γ : Path.Homotopic.Quotient x y) :
  γ.symm.trans γ = refl y
