/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Lemma_3_5_7

universe u

open Quiver.Path

set_option autoImplicit false

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- The canonical sign-sensitive map from the intrinsic Cayley graph of `(X; R)` to the chosen
actual Cayley `1`-skeleton. The coordinate formulas for positive and negative letters are derived
API of this owner map, rather than primitive public data in downstream theorems. -/
def fromIntrinsicCayley (coords : PresentationCoordinates C R) :
    OneComplex.Hom (GroupPresentation.cayleyOneComplex R) C.skeleton where
  toVertex := coords.vertexEquiv.symm
  toEdge := coords.edgeEquiv.symm
  map_initial := by
    intro e
    sorry
  map_terminal := by
    intro e
    sorry
  map_edgeInv := by
    intro e
    sorry

@[simp] theorem fromIntrinsicCayley_toVertex (coords : PresentationCoordinates C R)
    (g : PresentedGroup R) :
    (fromIntrinsicCayley coords).toVertex g = coords.vertexEquiv.symm g :=
  rfl

@[simp] theorem fromIntrinsicCayley_toEdge (coords : PresentationCoordinates C R)
    (e : (GroupPresentation.cayleyOneComplex R).Edge) :
    (fromIntrinsicCayley coords).toEdge e = coords.edgeEquiv.symm e :=
  rfl

/-- The signed-generator word read along a path in the chosen actual Cayley `1`-skeleton. -/
def pathLabel (coords : PresentationCoordinates C R) {a b : C.skeleton} :
    Quiver.Path a b → List (SignedLetter X)
  | .nil => []
  | .cons p e => pathLabel coords p ++ [(coords.edgeEquiv e.1).2]

@[simp] theorem pathLabel_nil (coords : PresentationCoordinates C R) (a : C.skeleton) :
    pathLabel coords (Quiver.Path.nil : Quiver.Path a a) = [] :=
  rfl

@[simp] theorem pathLabel_cons (coords : PresentationCoordinates C R) {a b c : C.skeleton}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    pathLabel coords (.cons p e) = pathLabel coords p ++ [(coords.edgeEquiv e.1).2] :=
  rfl

/-- The signed-generator boundary word read directly from an actual Cayley loop. -/
def boundaryLabel (coords : PresentationCoordinates C R) (p : Loop C.skeleton) :
    List (SignedLetter X) :=
  pathLabel coords p.2

/-- Transporting an intrinsic Cayley path into the chosen actual Cayley coordinates preserves its
signed-generator label word exactly. -/
@[simp] theorem pathLabel_fromIntrinsicCayley_mapPath (coords : PresentationCoordinates C R)
    {a b : GroupPresentation.cayleyOneComplex R} (p : Quiver.Path a b) :
    pathLabel coords ((fromIntrinsicCayley coords).mapPath p) =
      GroupPresentation.cayleyPathLabel R p := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      simpa [pathLabel, GroupPresentation.cayleyPathLabel, Quiver.Path.edgeList] using
        And.intro ih <| by
          change (coords.edgeEquiv ((fromIntrinsicCayley coords).toEdge e.1)).2 = e.1.2
          simp [fromIntrinsicCayley]

/-- Transporting an intrinsic Cayley loop into the chosen actual Cayley coordinates preserves its
boundary word exactly. -/
@[simp] theorem boundaryLabel_fromIntrinsicCayley_mapLoop (coords : PresentationCoordinates C R)
    (p : Loop (GroupPresentation.cayleyOneComplex R)) :
    boundaryLabel coords ((fromIntrinsicCayley coords).mapLoop p) =
      GroupPresentation.cayleyPathLabel R p.2 :=
  pathLabel_fromIntrinsicCayley_mapPath coords p.2

/-- The actual radius-`n` word ball in the chosen Cayley `1`-skeleton, obtained by transporting
the intrinsic ball along the Cayley coordinates. -/
def wordMetricBallSubcomplex (coords : PresentationCoordinates C R) (n : ℕ) :
    OneComplex.Subcomplex C.skeleton where
  vertexSet := fun v ↦ GroupPresentation.InWordMetricBall R n (coords.vertexEquiv v)
  edgeSet := fun e ↦
    GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.initial e)) ∧
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.terminal e))
  initial_mem := by
    intro e he
    exact he.1
  terminal_mem := by
    intro e he
    exact he.2
  edgeInv_mem := by
    intro e he
    constructor
    · convert he.2 using 1
      exact congrArg coords.vertexEquiv (C.skeleton.initial_edgeInv e)
    · convert he.1 using 1
      exact congrArg coords.vertexEquiv (C.skeleton.terminal_edgeInv e)

@[simp] theorem mem_wordMetricBallSubcomplex_vertex (coords : PresentationCoordinates C R)
    (n : ℕ) (v : C.skeleton) :
    v ∈ (wordMetricBallSubcomplex coords n).vertexSet ↔
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv v) :=
  Iff.rfl

@[simp] theorem mem_wordMetricBallSubcomplex_edge (coords : PresentationCoordinates C R)
    (n : ℕ) (e : C.skeleton.Edge) :
    e ∈ (wordMetricBallSubcomplex coords n).edgeSet ↔
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.initial e)) ∧
        GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.terminal e)) :=
  Iff.rfl

/-- A based loop lies in the radius-`n` word ball when every vertex visited by the loop is
represented by a word of length at most `n`. -/
def LoopInWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ)
    (p : Loop C.skeleton) : Prop :=
  ∀ v ∈ p.2.vertices, v ∈ (wordMetricBallSubcomplex coords n).vertexSet

/-- The constant loop at a vertex already lying in the radius-`n` ball also lies in that ball. -/
-- Proof sketch: the empty loop visits only its basepoint, so the given ball condition on that
-- basepoint is exactly the required statement.
theorem nil_loopInWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ) (a : C.skeleton)
    (ha : a ∈ (wordMetricBallSubcomplex coords n).vertexSet) :
    LoopInWordMetricBall coords n ⟨a, Quiver.Path.nil⟩ := sorry

/-- Two loops at the same basepoint are `2`-equivalent within the radius-`n` word ball when they
are joined by a finite chain of elementary `2`-reductions whose endpoints stay inside that same
ball at every step. -/
def PathTwoEquivWithinWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ)
    {a : C.skeleton} (p q : Quiver.Path a a) : Prop :=
  Relation.EqvGen
    (fun r s : Quiver.Path a a ↦
      C.path_two_reduction_step r s ∧
        LoopInWordMetricBall coords n ⟨a, r⟩ ∧
        LoopInWordMetricBall coords n ⟨a, s⟩)
    p q

/-- A loop is `2`-equivalent to itself within a fixed word ball as soon as it lies in that ball.
-/
-- Proof sketch: use reflexivity of `Relation.EqvGen`.
theorem pathTwoEquivWithinWordMetricBall_refl (coords : PresentationCoordinates C R) (n : ℕ)
    {a : C.skeleton} (p : Quiver.Path a a) (hp : LoopInWordMetricBall coords n ⟨a, p⟩) :
    PathTwoEquivWithinWordMetricBall coords n p p := sorry

/-- A Cayley complex satisfies the maximum principle when every null-homotopic loop contained in a
word ball contracts to the empty loop through elementary `2`-reductions that remain inside the
same word ball. -/
def SatisfiesMaximumPrinciple (coords : PresentationCoordinates C R) : Prop :=
  ∀ (n : ℕ) (a : C.skeleton) (p : Quiver.Path a a),
    LoopInWordMetricBall coords n ⟨a, p⟩ →
      C.path_two_equiv p (Quiver.Path.nil : Quiver.Path a a) →
      PathTwoEquivWithinWordMetricBall coords n p (Quiver.Path.nil : Quiver.Path a a)

/-- Under the maximum principle, any null-homotopic loop contained in a fixed word ball contracts
to the empty loop inside that same ball. -/
-- Proof sketch: this is exactly the defining clause of
-- `SatisfiesMaximumPrinciple`.
theorem pathTwoEquivWithinWordMetricBall_of_maximumPrinciple
    (coords : PresentationCoordinates C R) (hmax : SatisfiesMaximumPrinciple coords) (n : ℕ)
    (a : C.skeleton) (p : Quiver.Path a a) (hp : LoopInWordMetricBall coords n ⟨a, p⟩)
    (hnull : C.path_two_equiv p (Quiver.Path.nil : Quiver.Path a a)) :
    PathTwoEquivWithinWordMetricBall coords n p (Quiver.Path.nil : Quiver.Path a a) := sorry

variable [Primcodable X] [Finite X]

/-- Proposition 3-5-9: if the Cayley complex of a finite presentation `(X; R)` satisfies the
maximum principle, then the presentation has solvable word problem. -/
-- Proof sketch: for each radius `n`, the maximum principle turns any null-homotopic loop whose
-- vertices lie in the radius-`n` word ball into a contraction that stays inside the same finite
-- ball. The bounded `2`-equivalence quotient of that finite ball is therefore finite and
-- constructible, so Lemma `3-5-7` applies to decide whether a word of length at most `n`
-- represents `1` in the presented group.
theorem hasSolvableWordProblem_of_maximumPrinciple
    (coords : PresentationCoordinates C R) (hR : Set.Finite R)
    (hmax : SatisfiesMaximumPrinciple coords) :
    GroupPresentation.HasSolvableWordProblem R := sorry

end CayleyComplex.Coordinates
