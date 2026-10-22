/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_8

universe u

set_option autoImplicit false

noncomputable section

variable {X : Type u}

open FreeGroup.Finset

-- Layer triage:
-- `source-facing`: a group together with a finite presentation `G = (X; R)` and a finite chosen
-- relator-root family `S`, with `S` strictly quadratic and having cyclic star graph.
-- `core/canonical`: `PresentedGroup R` for groups given by generators and relations, `Finite X`
-- for the finite generator datum, `Set.Finite R` as the derived finiteness predicate for relator
-- families coming from finite root systems, `SignedLetter X` for the
-- signed-basis vocabulary, `IsStrictlyQuadraticSet` from Proposition `1-7-6`,
-- `FreeGroup.Finset.sigmaGraph` from Proposition `1-7-8`, and `SimpleGraph.IsCycles` for the
-- graph-theoretic cycle condition.
-- `bridge/view`: the textbook phrase "the chosen set `S` of relator roots" is
-- expressed by `GroupPresentation.IsRelatorRootSet`; the star-graph condition is
-- expressed directly by the owner predicates `(sigmaGraph S).Connected` and
-- `(sigmaGraph S).IsCycles`.
-- Domain sampling:
-- 1. `PresentedGroup R`, together with `Finite X`, is the
--    canonical owner layer for finite presentations.
-- 2. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the chapter owner for strict
--    quadraticity of finite free-group word systems, so this file reuses it directly.
-- 3. `FreeGroup.Finset.sigmaGraph` from Proposition `1-7-8` is the chapter owner construction
--    for the star graph attached to a finite system of reduced words.
-- 4. `GroupPresentation` from Chapter `2` is the natural owner namespace for auxiliary
--    presentation-level predicates, so the relator-root and relator-power relations live there
--    rather than as bare globals.
-- 5. `Set.Finite.image` is the canonical finiteness API showing that a relator set realized as the
--    image of a finite root family under `s ↦ s ^ m s` is finite, so that finiteness is derived
--    rather than stored as primitive data.
-- 6. `SimpleGraph.IsCycles` is mathlib's owner predicate for graphs whose nonisolated vertices all
--    have degree `2`, so together with connectedness it captures the textbook "cyclic graph"
--    condition.
-- Primitive vs. derived:
-- the primitive source data are the finite presentation `(X; R)` and the finite chosen relator
-- root system `S`, expressed source-facing by `GroupPresentation.IsRelatorRootSet` and canonically
-- by a multiplicity witness for `GroupPresentation.IsRelatorPowerFamily`. The finiteness of `R`,
-- strict quadraticity, and the star graph are derived through the owner predicates already
-- available upstream.

namespace GroupPresentation

/-- A multiplicity function `m` realizes `R` as the relator power family on `S` when the
relators are exactly the powers `s ^ m(s)` with `s ∈ S`. -/
def IsRelatorPowerFamily
    (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) (m : FreeGroup X → ℕ+) : Prop :=
  R = Set.image (fun s : FreeGroup X ↦ s ^ (m s : ℕ)) S

/-- A multiplicity function `m` realizes `R` as a primitive relator power family on `S` when the
relators are exactly the powers `s ^ m(s)` with `s ∈ S` and every chosen root in `S` is
primitive. -/
def IsPrimitiveRelatorPowerFamily
    (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) (m : FreeGroup X → ℕ+) : Prop :=
  IsRelatorPowerFamily R S m ∧ ∀ ⦃s : FreeGroup X⦄, s ∈ S → ¬ IsProperPower s

/-- A set `S` is a chosen relator-root family for `R` when some multiplicity function realizes the
relators exactly as the powers `s ^ m(s)` with `s ∈ S`. -/
def IsRelatorRootSet (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) : Prop :=
  ∃ m : FreeGroup X → ℕ+, IsRelatorPowerFamily R S m

theorem IsRelatorPowerFamily.isRelatorRootSet
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsRelatorPowerFamily R S m) :
    IsRelatorRootSet R S :=
  ⟨m, hR⟩

theorem IsPrimitiveRelatorPowerFamily.isRelatorPowerFamily
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) :
    IsRelatorPowerFamily R S m :=
  hR.1

theorem IsPrimitiveRelatorPowerFamily.isRelatorRootSet
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) :
    IsRelatorRootSet R S :=
  hR.isRelatorPowerFamily.isRelatorRootSet

/-- A relator family realized by powers of a finite chosen root system is finite. -/
theorem IsRelatorRootSet.finite_relators
    {R : Set (FreeGroup X)} {S : Finset (FreeGroup X)}
    (hR : IsRelatorRootSet R S) :
    R.Finite := by
  rcases hR with ⟨m, hm⟩
  rw [hm]
  exact (S.finite_toSet.image fun s : FreeGroup X ↦ s ^ (m s : ℕ))

/-- A primitive chosen relator root is a relator root that is not itself a proper power. -/
def IsPrimitiveRelatorRoot (S : Set (FreeGroup X)) (s : FreeGroup X) : Prop :=
  s ∈ S ∧ ¬ IsProperPower s

theorem IsPrimitiveRelatorPowerFamily.isPrimitiveRelatorRoot
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) {s : FreeGroup X} (hs : s ∈ S) :
    IsPrimitiveRelatorRoot S s :=
  ⟨hs, hR.2 hs⟩

end GroupPresentation

/-- Definition 3-5-3: an `F`-group is a group admitting a finite presentation `G = (X; R)` whose
finite chosen relator-root system `S` is strictly quadratic over `X` and has cyclic star graph. -/
class IsFGroup (G : Type u) [Group G] : Prop where
  /-- An `F`-group admits finite presentation data whose finite chosen relator-root system is
  strictly quadratic and has cyclic star graph. -/
  exists_presentation :
    ∃ (X : Type u) (_ : Finite X) (R : Set (FreeGroup X)) (S : Finset (FreeGroup X)),
      ∃ _ : PresentedGroup R ≃* G,
        GroupPresentation.IsRelatorRootSet R S ∧
        IsStrictlyQuadraticSet S ∧
        (sigmaGraph S).Connected ∧
        (sigmaGraph S).IsCycles

end
