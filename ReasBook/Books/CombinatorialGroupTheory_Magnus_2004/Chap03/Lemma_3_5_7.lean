/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

import CombinatorialGroupTheory_Magnus_2004.Chap01.SignedLetter
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Lemma_3_3_8
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_1

universe u

set_option autoImplicit false

namespace GroupPresentation

-- Layer triage:
-- `source-facing`: the word-metric balls around `1` in the Cayley graph of a presentation
-- `(X; R)`, and the consequence that effective finite construction of all such balls yields a
-- solution to the word problem.
-- `core/canonical`: `PresentedGroup R` is mathlib's owner for the group presented by `R`,
-- `HasSolvableWordProblem R` is the chapter owner predicate for decidability of the word problem,
-- `cayleyOneComplex R` below is the intrinsic Cayley `1`-skeleton of the presentation, and
-- `OneComplex.Subcomplex` is the chapter owner for the ball `Bₙ(C, 1)` as a genuine `1`-skeleton.
-- `bridge/view`: `wordMetricBallSubcomplex R n` is the source-facing ball inside the ambient
-- Cayley `1`-skeleton, while `WordMetricBall R n` is the derived `1`-complex carried by that
-- subcomplex.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for the group with presentation `(X; R)`.
-- 2. `HasSolvableWordProblem R` from Definition `2-1-4` is the project owner predicate for the
--    conclusion of the lemma.
-- 3. `OneComplex.Subcomplex` from Lemma `3-3-8` is the chapter owner for intrinsic `1`-skeleton
--    subobjects, so the ball should be expressed as a genuine subcomplex of the Cayley graph.
-- 4. `SignedLetter.inv` and `SignedLetter.value` are the chapter owners for orientation reversal
--    and evaluation of a signed generator, so the intrinsic Cayley graph should reuse them rather
--    than keeping parallel local copies.
-- 5. `FreeGroup.norm` is the canonical owner for reduced-word length on `FreeGroup X`, so the
--    textbook metric ball is organized around that owner rather than raw list length.
-- Primitive vs. derived:
-- the primitive data are the relator set `R`, the radius `n`, and the actual Cayley `1`-skeleton;
-- `wordMetricBallSubcomplex R n` is the source-facing ball object, `WordMetricBall R n` is the
-- derived `1`-complex it carries, and the extra effective data needed for Lemma `3-5-7` are only
-- a finite codable structure on the actual vertex carrier of that intrinsic ball together with the
-- computable source-facing evaluation map sending a bounded signed word to its canonical ball
-- vertex. The oriented-edge carrier of the same ball remains derived structure of the owner
-- `1`-complex, not primitive public data of the effective hypothesis.

variable {X : Type u}

/-- The bounded signed words of length at most `n`. -/
abbrev BoundedSignedWord (X : Type u) (n : ℕ) :=
  { L : List (SignedLetter X) // L.length ≤ n }

instance instPrimcodableBoundedSignedWord [Primcodable X] (n : ℕ) :
    Primcodable (BoundedSignedWord X n) := by
  dsimp [BoundedSignedWord]
  exact Primcodable.subtype ((Primrec.nat_le).comp Primrec.list_length (Primrec.const n))

/-- A vertex of the Cayley graph of `(X; R)` lies in the closed word-metric ball of radius `n`
when some representing word has reduced-word length at most `n`. -/
noncomputable def InWordMetricBall (R : Set (FreeGroup X)) (n : ℕ) (g : PresentedGroup R) : Prop :=
  by
    classical
    exact ∃ w : FreeGroup X, PresentedGroup.mk R w = g ∧ FreeGroup.norm w ≤ n

/-- The intrinsic Cayley `1`-skeleton of the presentation `(X; R)`. -/
def cayleyOneComplex (R : Set (FreeGroup X)) : OneComplex where
  Vertex := PresentedGroup R
  Edge := PresentedGroup R × SignedLetter X
  initial := Prod.fst
  terminal := fun e ↦ e.1 * SignedLetter.value PresentedGroup.of e.2
  edgeInv := fun e ↦ (e.1 * SignedLetter.value PresentedGroup.of e.2, e.2⁻¹)
  edgeInv_involutive := by
    rintro ⟨g, letter⟩
    rcases letter with ⟨x, b⟩
    cases b <;> ext <;> simp [mul_assoc]
  edgeInv_ne := by
    intro e h
    rcases e with ⟨g, x, b⟩
    have hletter : (x, b)⁻¹ = (x, b) := congrArg Prod.snd h
    cases b <;> simp at hletter
  initial_edgeInv := by
    intro e
    rfl

/-- The signed-generator word read along a path in the intrinsic Cayley `1`-skeleton of the
presentation `(X; R)`. -/
def cayleyPathLabel (R : Set (FreeGroup X)) {a b : cayleyOneComplex R} (p : Quiver.Path a b) :
    List (SignedLetter X) :=
  (Quiver.Path.edgeList p).map fun e ↦ e.hom.1.2

/-- Membership in a smaller word ball implies membership in every larger one. -/
theorem inWordMetricBall_mono (R : Set (FreeGroup X)) {m n : ℕ} (hmn : m ≤ n)
    {g : PresentedGroup R} (hg : InWordMetricBall R m g) :
    InWordMetricBall R n g := by
  rcases hg with ⟨w, rfl, hw⟩
  exact ⟨w, rfl, hw.trans hmn⟩

/-- The radius-`n` word ball `Bₙ(C, 1)` as a genuine subcomplex of the intrinsic Cayley
`1`-skeleton. -/
def wordMetricBallSubcomplex (R : Set (FreeGroup X)) (n : ℕ) :
    OneComplex.Subcomplex (cayleyOneComplex R) where
  vertexSet := InWordMetricBall R n
  edgeSet := { e | InWordMetricBall R n ((cayleyOneComplex R).initial e) ∧
    InWordMetricBall R n ((cayleyOneComplex R).terminal e) }
  initial_mem := fun h ↦ h.1
  terminal_mem := fun h ↦ h.2
  edgeInv_mem := by
    intro e h
    rcases h with ⟨hinitial, hterminal⟩
    constructor
    · simpa [cayleyOneComplex] using hterminal
    · rcases e with ⟨g, letter⟩
      rcases letter with ⟨x, b⟩
      cases b <;> simpa [cayleyOneComplex, mul_assoc] using hinitial

/-- The intrinsic `1`-skeleton carried by the closed radius-`n` word ball `Bₙ(C, 1)`. -/
abbrev WordMetricBall (R : Set (FreeGroup X)) (n : ℕ) :=
  (wordMetricBallSubcomplex R n).toOneComplex

/-- The identity element of a presented group lies in every closed word-metric ball. -/
-- Proof sketch: represent `1` by the empty word in `FreeGroup X`, whose reduced-word length is
-- `0`.
theorem one_mem_inWordMetricBall (R : Set (FreeGroup X)) (n : ℕ) :
    InWordMetricBall R n 1 := by
  classical
  refine ⟨1, rfl, ?_⟩
  simp

/-- The quotient image of a signed word lies in the word ball of radius equal to its length. -/
-- Proof sketch: use the word itself as the witnessing representative.
theorem mk_mem_inWordMetricBall (R : Set (FreeGroup X)) (L : List (SignedLetter X)) :
    InWordMetricBall R L.length (PresentedGroup.mk R (FreeGroup.mk L)) := by
  classical
  refine ⟨FreeGroup.mk L, rfl, ?_⟩
  exact (show FreeGroup.norm (FreeGroup.mk L) ≤ L.length from FreeGroup.norm_mk_le)

/-- A bounded signed word determines canonically a vertex of the corresponding radius word ball.
-/
def boundedSignedWordVertex (R : Set (FreeGroup X)) {n : ℕ} :
    BoundedSignedWord X n → WordMetricBall R n
  | ⟨L, hL⟩ =>
      ⟨PresentedGroup.mk R (FreeGroup.mk L),
        inWordMetricBall_mono R hL (mk_mem_inWordMetricBall R L)⟩

@[simp] theorem boundedSignedWordVertex_val (R : Set (FreeGroup X)) {n : ℕ}
    (L : BoundedSignedWord X n) :
    (boundedSignedWordVertex R L).1 =
      PresentedGroup.mk R (FreeGroup.mk L.1) := by
  cases L
  rfl

/-- A radius-`n` word ball is finite and effectively constructible for Lemma `3-5-7` when its
intrinsic vertex type is finite and effectively codable, and the canonical source-facing map
`boundedSignedWordVertex` from bounded signed words to ball vertices is computable. The ambient
`1`-skeleton data of the same ball already come from the owner object `WordMetricBall R n`, so the
effective hypothesis does not repackage oriented-edge data as primitive public fields. -/
def HasFiniteConstructibleWordMetricBall [Primcodable X] (R : Set (FreeGroup X)) (n : ℕ) : Prop :=
  ∃ (_ : Fintype (WordMetricBall R n)) (_ : Primcodable (WordMetricBall R n)),
    Computable (boundedSignedWordVertex R : BoundedSignedWord X n → WordMetricBall R n)

section

variable [Primcodable X]

/-- Lemma 3-5-7: if every ball `Bₙ(C, 1)` in the Cayley graph of the presentation `(X; R)` has
finite, effectively constructible vertex set, then the presentation has solvable word problem. In
the owner formulation, each intrinsic ball `WordMetricBall R n` is already an actual `1`-complex,
and the effective hypothesis supplies only the vertex-side data used by the word-problem argument:
a finite codable structure on the genuine ball vertices together with the computable source-facing
evaluation map from bounded signed words into that intrinsic ball. -/
-- Proof sketch: on an input signed word `L`, work in the finite model of the radius-`L.length`
-- ball. Compare the canonical ball vertex of `L` with the canonical base vertex `1` inside that
-- finite ball. Since both points already live in the actual ball `1`-skeleton, equality of those
-- ball vertices is exactly equality of their images in `PresentedGroup R`, so `L` represents `1`
-- precisely when those two vertices agree.
theorem hasSolvableWordProblem_of_finite_effective_wordMetricBalls
    (R : Set (FreeGroup X))
    (hball : ∀ n, HasFiniteConstructibleWordMetricBall R n) :
    HasSolvableWordProblem R := sorry

end

end GroupPresentation
