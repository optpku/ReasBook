/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped commutatorElement
open FreeGroupBasis

section

variable {X : Type u} [DecidableEq X]

local notation "basis" => FreeGroupBasis.ofFreeGroup X

-- Layer triage:
-- `source-facing`: finite connected strictly quadratic word systems in `FreeGroup X`, their
-- automorphic normalization, and the attached elementary transformation relation used in
-- Proposition `1-7-6 (2)`.
-- `core/canonical`: `FreeGroupBasis.ofFreeGroup X`, `IsQuadraticWordSet`,
-- `IsStrictlyQuadraticWordSet`, `wordIncidenceGraph`,
-- `basis.elementaryNielsenTransvection`, `Finset.image`, `List.IsInfix`, and
-- `Relation.ReflTransGen`.
-- `bridge/view`: the finite-set strictness predicate below is the thin bridge from
-- `Finset (FreeGroup X)` to the owner Section 7 API on `Set (FreeGroup X)` for the canonical
-- basis of `FreeGroup X`.
-- Domain sampling:
-- 1. `FreeGroupBasis.ofFreeGroup X` is the canonical basis owner of `FreeGroup X`.
-- 2. `IsQuadraticWordSet` from Proposition `1-7-4` is the owner predicate for the per-word
--    quadraticity and two-word incidence conditions.
-- 3. `IsStrictlyQuadraticWordSet` from Proposition `1-7-5` is the owner predicate for the
--    `0-or-2` word-incidence condition on each basis generator.
-- 4. `basis.elementaryNielsenTransvection` from Proposition `1-4-1`,
--    `wordIncidenceGraph`, `List.IsInfix`, and `Relation.ReflTransGen` are the canonical owners
--    for attached regular Nielsen steps, connectedness, contiguous reduced subwords, and finite
--    transformation sequences.
-- Primitive vs. derived:
-- the primitive source data are the finite word system `S : Finset (FreeGroup X)` and, for the
-- second clause, the one-step attached elementary transformation relation. Strict quadraticity,
-- connectedness, automorphic images, and finite-step reachability are derived from the owner
-- abstractions above.

/-- A finite set of words is strictly quadratic for the canonical basis of `FreeGroup X` when it
is quadratic in the Section 7 sense and every basis generator occurs in either zero or two words
of the set. -/
def IsStrictlyQuadraticSet (S : Finset (FreeGroup X)) : Prop :=
  IsQuadraticWordSet basis (S : Set (FreeGroup X)) ∧
    IsStrictlyQuadraticWordSet basis (S : Set (FreeGroup X))

/-- The orientable quadratic tail form from Proposition `1-7-6`: a product of commutators on
generators disjoint from the singleton prefix. -/
def IsOrientableQuadraticTail (forbidden : Finset X) (q : FreeGroup X) : Prop :=
  ∃ pairs : List (X × X),
    (pairs.flatMap fun p ↦ [p.1, p.2]).Nodup ∧
      (∀ y ∈ pairs.flatMap (fun p ↦ [p.1, p.2]), y ∉ forbidden) ∧
      q = (pairs.map fun p ↦ ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆).prod

/-- The nonorientable quadratic tail form from Proposition `1-7-6`: a product of squares on
generators disjoint from the singleton prefix. -/
def IsNonorientableQuadraticTail (forbidden : Finset X) (q : FreeGroup X) : Prop :=
  ∃ ys : List X,
    ys.Nodup ∧
      (∀ y ∈ ys, y ∉ forbidden) ∧
      q = (ys.map fun y ↦ FreeGroup.of y ^ (2 : ℕ)).prod

/-- A finite word system is in the standard quadratic normal form of Proposition `1-7-6` when it
consists of singleton generator words together with one terminal word whose tail is a product of
commutators or a product of squares on generators disjoint from the singleton part. -/
def IsStandardQuadraticWordSystem (S : Finset (FreeGroup X)) : Prop :=
  ∃ k : ℕ, ∃ x : Fin k → X, Function.Injective x ∧
    ∃ q : FreeGroup X,
      (IsOrientableQuadraticTail (Finset.univ.image x) q ∨
        IsNonorientableQuadraticTail (Finset.univ.image x) q) ∧
      S =
        Finset.univ.image (fun i ↦ FreeGroup.of (x i)) ∪
          {(List.ofFn fun i ↦ FreeGroup.of (x i)).prod * q}

/-- The canonical regular Nielsen transvection `x ↦ x y^ε` relative to the free basis on `X`. -/
private noncomputable def signedElementaryNielsenTransvection
    (srcGen dstGen : X) (ySign : Bool) (hxy : srcGen ≠ dstGen) :
    MulAut (FreeGroup X) :=
  if ySign then
    elementaryNielsenTransvection basis srcGen dstGen hxy
  else
    (elementaryNielsenTransvection basis srcGen dstGen hxy)⁻¹

omit [DecidableEq X] in
@[simp] private theorem signedElementaryNielsenTransvection_apply_src
    (srcGen dstGen : X) (ySign : Bool) (hxy : srcGen ≠ dstGen) :
    signedElementaryNielsenTransvection srcGen dstGen ySign hxy (FreeGroup.of srcGen) =
      FreeGroup.of srcGen *
        if ySign then FreeGroup.of dstGen else (FreeGroup.of dstGen)⁻¹ := by
  by_cases hy : ySign
  · simpa [signedElementaryNielsenTransvection, hy] using
      elementaryNielsenTransvection_apply_fst basis srcGen dstGen hxy
  · simpa [signedElementaryNielsenTransvection, hy] using
      elementaryNielsenTransvection_inv_apply_fst basis srcGen dstGen hxy

omit [DecidableEq X] in
@[simp] private theorem signedElementaryNielsenTransvection_apply_of_ne
    (srcGen dstGen : X) (ySign : Bool) (hxy : srcGen ≠ dstGen) {z : X} (hz : z ≠ srcGen) :
    signedElementaryNielsenTransvection srcGen dstGen ySign hxy (FreeGroup.of z) =
      FreeGroup.of z := by
  by_cases hy : ySign
  · simpa [signedElementaryNielsenTransvection, hy] using
      elementaryNielsenTransvection_apply_of_ne basis srcGen dstGen hxy hz
  · simpa [signedElementaryNielsenTransvection, hy] using
      elementaryNielsenTransvection_inv_apply_of_ne basis srcGen dstGen hxy hz

/-- An attached elementary transformation of a finite word system is a regular Nielsen
transvection `x ↦ x y^ε`, fixing the other generators, whose attaching condition is witnessed by
the infix `x y^{-ε}` in the canonical reduced word of one member of the source system; the target
system is the image under that canonical transvection. -/
def AttachedElementaryTransformation
    (S S' : Finset (FreeGroup X)) : Prop :=
  ∃ srcGen dstGen : X, ∃ ySign : Bool, ∃ hxy : srcGen ≠ dstGen,
    (∃ w ∈ S, [(srcGen, true), (dstGen, !ySign)] <:+: w.toWord) ∧
      S' = S.image (signedElementaryNielsenTransvection srcGen dstGen ySign hxy)

/-- Proposition 1-7-6 (1): a finite connected strictly quadratic set of words in `FreeGroup X`
is automorphically equivalent to one whose members are singleton generators together with one
terminal word `x₁ ⋯ xₖ q`, where `q` is either a product of commutators or a product of squares on
generators disjoint from the singleton part. -/
-- Proof sketch: induct on the number of non-singleton words. Connectedness produces a new
-- generator occurring in a word not yet reduced to a singleton, and the elementary
-- transformations from the preceding lemmas isolate that generator as a new singleton while
-- preserving strict quadraticity and connectedness. After all but one words are singletons, the
-- remaining word is rewritten into `x₁ ⋯ xₖ q`, and a second induction on the length of `q`
-- reduces the strictly quadratic tail to either the commutator product form or the square product
-- form.
theorem exists_automorphicImage_standardQuadraticForm
    (S : Finset (FreeGroup X)) (hS : IsStrictlyQuadraticSet S)
    (hconn : (wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected) :
    ∃ α : MulAut (FreeGroup X), IsStandardQuadraticWordSystem (S.image α) := sorry

/-- Proposition 1-7-6 (2): the same normal form can be reached from the original strictly
quadratic connected set by a finite sequence of source-facing attached elementary
transformations. -/
-- Proof sketch: the inductive normalization procedure of the first clause is implemented by the
-- source-facing attached elementary transformations. Concatenating those one-step moves gives a
-- `Relation.ReflTransGen` chain from `S` to a system in quadratic normal form.
theorem exists_attachedElementaryTransformationSequence_standardQuadraticForm
    (S : Finset (FreeGroup X)) (hS : IsStrictlyQuadraticSet S)
    (hconn : (wordIncidenceGraph basis (S : Set (FreeGroup X))).Connected) :
    ∃ S' : Finset (FreeGroup X), Relation.ReflTransGen AttachedElementaryTransformation S S' ∧
      IsStandardQuadraticWordSystem S' := sorry

end
