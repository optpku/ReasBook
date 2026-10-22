/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_4

-- Declarations for this item are recorded in this dedicated item file.

universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory for staggered presentations and interval restrictions on
normal closures.

Layer triage:
- `source-facing`: a staggered presentation on generators `X` with a distinguished ordered subset
  `X₀`, together with the least and greatest generators of `X₀` occurring in a word.
- `core/canonical`: `FreeGroup X`, `FreeGroupBasis.ofFreeGroup X`, `basisLetterOccurs`, `IsLeast`,
  `IsGreatest`, `Set.Icc`, and `Subgroup.normalClosure`.
- `bridge/view`: distinguished support is the subset of `X₀` cut out by the owner predicate
  `basisLetterOccurs (FreeGroupBasis.ofFreeGroup X)`, and interval support is expressed as
  inclusion in the canonical interval `Set.Icc xₐ x_b`.

Domain sampling:
1. `FreeGroup X` is the owner object for words in the presentation.
2. `FreeGroupBasis.ofFreeGroup X` together with `basisLetterOccurs` from Proposition `1-7-4` is
   the chapter owner abstraction for the source phrase “the generator `x` occurs in `w`”.
3. `IsLeast`, `IsGreatest`, and `Set.Icc` are the canonical order-theoretic owners for extremal
   distinguished generators and the interval they determine.
4. Proposition `2-5-2` shows the same chapter-level interval/normal-closure pattern for indexed
   generators; this file keeps the extra distinguished-subset data source-facing, but it should
   still reuse the same owner-level occurrence and interval abstractions.

Primitive vs. derived:
- primitive public data: the ordered distinguished subset `X₀` and the indexed relator family
  `r`;
- derived API: the distinguished support set, distinguished interval support, the staggered
  predicate, and the interval-restricted relator set.
-/

namespace GroupPresentation

section

variable {X : Type u} [LinearOrder X]

open Subgroup

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-- The distinguished generators from `X₀` occurring in `w`. -/
def distinguishedSupport (X₀ : Set X) (w : FreeGroup X) : Set X :=
  X₀ ∩ {x | basisLetterOccurs basis x w}

/-- Every distinguished generator of `X₀` occurring in `w` lies in the interval `xₐ ≤ x ≤ x_b`. -/
def SupportedOnDistinguishedInterval (X₀ : Set X) (xₐ x_b : X) (w : FreeGroup X) : Prop :=
  distinguishedSupport X₀ w ⊆ Set.Icc xₐ x_b

/-- The generators `xₐ` and `x_b` are the least and greatest distinguished generators from `X₀`
occurring in `w`. -/
def HasExtremeDistinguishedSupport (X₀ : Set X) (w : FreeGroup X) (xₐ x_b : X) : Prop :=
  IsLeast (distinguishedSupport X₀ w) xₐ ∧
    IsGreatest (distinguishedSupport X₀ w) x_b

/-- Extreme distinguished support bounds the full distinguished support inside the interval
`[xₐ, x_b]`. -/
theorem supportedOnDistinguishedInterval_of_hasExtremeDistinguishedSupport
    {X₀ : Set X} {w : FreeGroup X} {xₐ x_b : X}
    (h : HasExtremeDistinguishedSupport X₀ w xₐ x_b) :
    SupportedOnDistinguishedInterval X₀ xₐ x_b w := by
  intro x hx
  exact ⟨h.1.2 hx, h.2.2 hx⟩

-- Proof sketch: the least distinguished support element already lies in `distinguishedSupport X₀ w`.
/-- Extreme distinguished support implies that some generator from `X₀` occurs in `w`. -/
theorem exists_distinguished_generator_of_hasExtremeDistinguishedSupport
    {X₀ : Set X} {w : FreeGroup X} {xₐ x_b : X}
    (h : HasExtremeDistinguishedSupport X₀ w xₐ x_b) :
    ∃ x : X, x ∈ X₀ ∧ basisLetterOccurs basis x w := by
  refine ⟨xₐ, ?_⟩
  simpa [distinguishedSupport] using h.1.1

end

section

variable {X : Type u} [LinearOrder X]
variable {J : Type v} [Preorder J]

open Subgroup

/-- A relator family is staggered relative to the distinguished generator set `X₀` when each
relator has least and greatest distinguished generators in its support, and those endpoints
increase with the relator order. -/
def IsStaggeredPresentation (X₀ : Set X) (r : J → FreeGroup X) : Prop :=
  ∃ initial terminal : J → X,
    (∀ j, HasExtremeDistinguishedSupport X₀ (r j) (initial j) (terminal j)) ∧
      StrictMono initial ∧
      StrictMono terminal

/-- The interval-restricted relator set consists of those relators whose distinguished generators
from `X₀` all lie between `xₐ` and `x_b`. -/
def relatorsSupportedOnDistinguishedInterval
    (X₀ : Set X) (r : J → FreeGroup X) (xₐ x_b : X) : Set (FreeGroup X) :=
  Set.range r ∩ SupportedOnDistinguishedInterval X₀ xₐ x_b

-- Proof sketch: choose a van Kampen diagram for `w` over the relators `r`. The staggered ordering
-- forces the least and greatest distinguished generators on the boundary word to control the
-- distinguished supports of every relator that appears in the diagram. Removing extremal faces
-- inductively leaves a diagram using only relators whose distinguished generators lie between
-- those two extremes, so `w` already lies in the normal closure of the interval-restricted
-- relators.
/-- Proposition 3-9-5: if `r` is a staggered presentation relative to `X₀` and a nontrivial word
`w` lies in the normal closure of `r`, then `w` contains generators of `X₀`; choosing the least
and greatest such generators `xₐ` and `x_b`, the word already lies in the normal closure of the
relators whose distinguished generators from `X₀` all lie between `xₐ` and `x_b`. -/
theorem exists_extreme_distinguished_support_and_interval_normalClosure
    (X₀ : Set X) (r : J → FreeGroup X) (hstaggered : IsStaggeredPresentation X₀ r)
    {w : FreeGroup X} (hw : w ∈ normalClosure (Set.range r)) (hwne : w ≠ 1) :
    ∃ xₐ x_b : X,
      HasExtremeDistinguishedSupport X₀ w xₐ x_b ∧
        w ∈ normalClosure (relatorsSupportedOnDistinguishedInterval X₀ r xₐ x_b) := sorry

end

end GroupPresentation
