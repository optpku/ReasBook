/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_5_6

universe u v w

-- Declarations for this item are recorded in this dedicated item file.

noncomputable section

-- Primary domain: combinatorial group theory for presentations indexed by an ordered family of
-- generators and relators.
-- Layer triage:
-- `source-facing`: the ordered generator families `Yᵢ`, the indexed relators `rⱼ`, the
-- interval-support restriction on relators and consequences, the staggered relator-family
-- condition, and the proposition that an interval-supported consequence is already forced by the
-- interval-supported relators.
-- `core/canonical`: `FreeGroup`, `reducedWordSupport`, `IsLeast`, `IsGreatest`, `Set.Icc`, and
-- `Subgroup.normalClosure`.
-- `bridge/view`: support indices are read by projecting the canonical reduced-word support
-- `reducedWordSupport w : Finset (Σ i, Y i)` along `Sigma.fst`, and “is a consequence of” is
-- expressed as membership in the normal closure of the relevant relator set.
-- Domain sampling:
-- 1. `reducedWordSupport` from Proposition `1-5-6` is the chapter owner notion of the
--    generators occurring in the canonical reduced word of an element of `FreeGroup Generators`.
-- 2. `IsLeast`, `IsGreatest`, and `Set.Icc α ω` are the canonical order-theoretic owners for the
--    least and greatest support indices and the interval they determine.
-- 3. `Subgroup.normalClosure` is the owner construction for the set of consequences of a relator
--    family.
-- 4. Projecting `reducedWordSupport w` along `Sigma.fst` is the canonical bridge from occurring
--    generators in `Σ i, Y i` to their support indices in `ι`.
-- Primitive vs. derived:
-- the primitive source data are the indexed generator families, the indexed relators, and the
-- least/greatest support-index data in the staggered relator-family property; the support-index
-- set, the extreme-support predicate, the interval-support predicate, the interval-restricted
-- relator set, and the consequence statement are derived from that data.

namespace GroupPresentation

section

variable {ι : Type u} [LinearOrder ι]
variable {Y : ι → Type v}
variable {J : Type w}

open Subgroup

local notation "Generators" => Σ i, Y i

/-- The support indices of the indexed generators occurring in `w`. -/
def supportIndices (w : FreeGroup Generators) : Set ι :=
  Sigma.fst '' (reducedWordSupport w : Set Generators)

/-- A word in the free group on the indexed generators `Σ i, Y i` is supported on the interval
`[α, ω]` when every support index of an occurring generator lies between `α` and `ω`. -/
def SupportedOnInterval (α ω : ι) (w : FreeGroup Generators) : Prop :=
  supportIndices w ⊆ Set.Icc α ω

/-- The generators of `w` have extreme support indices `α` and `ω`. -/
def HasExtremeSupport (w : FreeGroup Generators) (α ω : ι) : Prop :=
  IsLeast (supportIndices w) α ∧
    IsGreatest (supportIndices w) ω

/-- Least and greatest support indices bound the full support inside their interval. -/
theorem supportedOnInterval_of_hasExtremeSupport
    {w : FreeGroup Generators} {α ω : ι} (h : HasExtremeSupport w α ω) :
    SupportedOnInterval α ω w := by
  intro i hi
  exact ⟨h.1.2 hi, h.2.2 hi⟩

variable [Preorder J]

/-- A relator family is staggered when each relator has least and greatest support indices, and
those extremal indices increase strictly with the relator order. -/
def IsStaggeredRelatorFamily (r : J → FreeGroup Generators) : Prop :=
  ∃ initial terminal : J → ι,
    (∀ j, HasExtremeSupport (r j) (initial j) (terminal j)) ∧
      StrictMono initial ∧
      StrictMono terminal

/-- The relators supported on the interval `[α, ω]`. -/
def relatorsSupportedOnInterval (r : J → FreeGroup Generators) (α ω : ι) :
    Set (FreeGroup Generators) :=
  Set.range r ∩ SupportedOnInterval α ω

-- Proof sketch: apply the staggered Freiheitssatz argument to a van Kampen diagram for `w`.
-- Since every letter of `w` lies in the interval `[α, ω]`, the extreme relators forced by the
-- staggered ordering also lie in that interval; peeling them off inductively shows that `w`
-- belongs to the normal closure of exactly the relators supported in `[α, ω]`.
/-- Proposition 2-5-2: in a staggered presentation, any consequence whose generators all lie in the
interval `α ≤ i ≤ ω` is already a consequence of the relators whose generators lie in that same
interval. -/
theorem consequence_of_interval_relators_of_staggered_presentation
    (r : J → FreeGroup Generators)
    (hstaggered : IsStaggeredRelatorFamily r)
    {α ω : ι} {w : FreeGroup Generators}
    (hw : w ∈ normalClosure (Set.range r))
    (hsupp : SupportedOnInterval α ω w) :
    w ∈ normalClosure (relatorsSupportedOnInterval r α ω) := by
  sorry

end

end GroupPresentation
