/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open scoped MatrixGroups

section

variable {F : Type u} [Field F]
variable {n : ℕ}

-- Layer triage:
-- `source-facing`: a finitely generated subgroup `H` of the special linear group `SL(n, F)`.
-- `core/canonical`: the subgroup owner `Subgroup (SL(n, F))`, together with the owner predicates
-- `Subgroup.FG` for finite generation and `Group.ResiduallyFinite` for residual finiteness.
-- `bridge/view`: `Matrix.SpecialLinearGroup.toLin'_equiv` identifies the matrix group `SL(n, F)`
-- with the intrinsic module-level special linear group on `Fin n → F`, but this bridge does not
-- replace the source-facing matrix formulation of the proposition.
-- Domain sampling:
-- 1. `SL(n, F)` from `Matrix.SpecialLinearGroup` is the chapter's source-facing realization of the
--    special linear group.
-- 2. `Matrix.SpecialLinearGroup.toLin'_equiv` is the canonical bridge from the matrix
--    presentation to the module-level owner `SpecialLinearGroup F (Fin n → F)`.
-- 3. `Subgroup (SL(n, F))` is the canonical owner abstraction for the subgroup named in the
--    proposition.
-- 4. `Group.FG` on the subgroup carrier and `Group.ResiduallyFinite` are mathlib's owner
--    predicates for the two mathematical properties appearing in the statement.
-- 5. `Group.fg_iff_subgroup_fg` is the canonical bridge between the subgroup-facing finite
--    generation predicate `H.FG` and the owner instance `Group.FG H`.
-- Best owner abstraction:
-- keep the public statement at the subgroup-owner level `Subgroup (SL(n, F))`. The finitely
-- generated linear-group input is exactly the owner instance `Group.FG H`, and the matrix-to-
-- module bridge for `SL(n, F)` remains proof infrastructure rather than a second public owner.
-- Primitive vs. derived:
-- the primitive public content is the owner instance `Group.ResiduallyFinite H` for a finitely
-- generated subgroup `H ≤ SL(n, F)`, with `Group.FG H` as the only extra owner-level input. The
-- explicit theorem below is the source-facing bridge back to the textbook formulation using
-- `H.FG`. The ambient field `F` and size parameter `n` are inferred from `H`, and the module-
-- level special linear group equivalence is derived bridge data rather than additional primitive
-- content. There is no upstream theorem in the project or mathlib giving Mal'cev's
-- residual-finiteness result for finitely generated linear subgroups. The source restriction
-- `n ≥ 1` is mathematically redundant here, since `SL(0, F)` is trivial and hence residually
-- finite.

variable (H : Subgroup (SL(n, F)))

/-- Owner-level form of Proposition 3-7-12: a finitely generated subgroup of `SL(n, F)` is
residually finite. -/
-- Proof sketch: this is Mal'cev's theorem for finitely generated linear groups. For a nontrivial
-- element of `H`, choose generators for `H` and let `R` be the finitely generated subring of `F`
-- spanned by all matrix entries of those generators. Reduce modulo a suitable maximal ideal of `R`
-- so that the chosen element remains nontrivial; the resulting image lies in a finite special
-- linear group, giving a finite quotient that separates the element.
instance residuallyFinite_subgroup_specialLinearGroup_of_fg [Group.FG H] :
    Group.ResiduallyFinite H where
  iInf_eq_bot := sorry

/-- Proposition 3-7-12: every finitely generated subgroup of `SL(n, F)` is residually finite. -/
theorem residuallyFinite_of_fg_subgroup_specialLinearGroup (hH : H.FG) :
    Group.ResiduallyFinite H := by
  letI := (Group.fg_iff_subgroup_fg H).2 hH
  infer_instance

end
