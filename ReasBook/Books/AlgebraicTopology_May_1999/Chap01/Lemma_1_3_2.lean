/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] {x y : X}

open CategoryTheory FundamentalGroup
open Path.Homotopic.Quotient
open scoped FundamentalGroup

/-- Lemma 1.3.2 (1): the basepoint-change equivalence associated to a path `a : Path x y`
depends only on the endpoint-fixed homotopy class of `a`. -/
-- Proof sketch: identify `FundamentalGroup.fundamentalGroupMulEquivOfPath a` with conjugation by
-- the image of `a` in the fundamental groupoid, then use that homotopic paths define the same
-- morphism in the quotient groupoid.
lemma fundamentalGroupMulEquivOfPath_homotopic_eq {a b : Path x y} (h : a.Homotopic b) :
    γ[a] = γ[b] := by
  simpa [fundamentalGroupMulEquivOfPath] using
    congrArg (fun q ↦ ((Groupoid.isoEquivHom ..).symm q).conj) (eq.2 h)

/-- Lemma 1.3.2 (2): for a path `a : Path x y`, the basepoint-change map `γ[a]` preserves
multiplication on fundamental groups. -/
theorem fundamentalGroupMulEquivOfPath_map_mul
    (a : Path x y) (g h : FundamentalGroup X x) :
    γ[a] (g * h) = γ[a] g * γ[a] h := by
  exact (γ[a]).map_mul g h
