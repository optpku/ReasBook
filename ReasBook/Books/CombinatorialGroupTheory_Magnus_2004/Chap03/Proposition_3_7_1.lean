/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

/-!
Primary domain: Fuchsian complexes, modified presentations, and dual modified Cayley complexes.

Layer triage:
- `source-facing`: a Fuchsian complex for a group `G`, a modified presentation `(X, J; R)` of
  `G`, the associated modified Cayley complex, and the statement that this complex can be chosen
  dual to the given Fuchsian complex.
- `core/canonical`: `TwoComplex` is the owner for the underlying `2`-complex geometry,
  `TwoComplex.Aut` is the owner for automorphisms of a `2`-complex,
  `TwoComplex.AutAction` is the owner for a group action by such automorphisms,
  `TwoComplex.GeometricFace` and `OneComplex.GeometricEdge` are the owners for unoriented faces
  and edges, and
  `CayleyComplex.Coordinates` is the owner for Cayley-type coordinates on an actual `2`-complex,
  `SignedLetter` is the chapter owner for signed ordinary generators,
  `PresentedGroup` is the canonical owner for the relators of a modified presentation, and
  `TwoComplex.VertexOnFace` is the owner for vertex-face incidence.
- `bridge/view`: `TwoComplex.Duality` records the duality data between two actual
  `2`-complexes together with their incidence compatibility, and
  `ModifiedCayleyComplex.RealizesFuchsianDuality` expresses the textbook equivariance statement
  for the dual vertices.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the owner abstraction for the actual complex `K`.
2. `TwoComplex.Aut` and its induced permutations from Proposition `3-4-1` are the natural owner
   abstractions for the group action on a Fuchsian complex.
3. `TwoComplex.AutAction` is the right owner for the group law on those automorphisms, so the
   induced geometric-face and geometric-edge permutations are derived API rather than primitive
   fields of `FuchsianComplex`.
4. `TwoComplex.GeometricFace`, `OneComplex.GeometricEdge`, and `TwoComplex.VertexOnFace` are the
   correct intrinsic carriers and incidence owners for duality and for the "without reflections"
   condition.
5. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the owner abstraction for an actual
   Cayley-type complex with the canonical left translations by `G`.
6. `SignedLetter` from Proposition `3-4-1` is the owner vocabulary for signed ordinary
   generators, so the modified relator alphabet should reuse it directly.
7. `PresentedGroup` is the canonical owner for saying that a relator family presents `G`.

Primitive vs. derived:
- primitive data: the actual Fuchsian `2`-complex, its action by automorphisms, the modified
  presentation data `(X, J; R)` together with the actual relator words, the involution condition
  on the reflection generators, the presentation equivalence to `G`, and the actual modified
  Cayley complex with Cayley coordinates and relator boundary words;
- derived API: the induced actions on geometric faces and edges, the generator/reflection values
  in `G`, the duality equivalences together with their incidence view, the vertex corresponding to
  a face under a duality, and the equivariance statement for those vertices.
-/

namespace TwoComplex

/-- An action of a group on a `2`-complex by automorphisms, recorded on the actual vertex,
oriented-edge, and oriented-face carriers. The induced actions on geometric faces and geometric
edges are derived API. -/
structure AutAction (G : Type u) [Group G] (C : TwoComplex) where
  /-- The automorphism corresponding to an element of `G`. -/
  toAut : G → Aut C
  /-- The identity element acts trivially on vertices. -/
  one_vertex (v : C.skeleton) :
      (toAut 1).vertexPerm v = v
  /-- Multiplication in `G` matches composition on vertices. -/
  mul_vertex (g h : G) (v : C.skeleton) :
      (toAut (g * h)).vertexPerm v =
        (toAut g).vertexPerm ((toAut h).vertexPerm v)
  /-- The identity element acts trivially on oriented edges. -/
  one_edge (e : C.skeleton.Edge) :
      (toAut 1).edgePerm e = e
  /-- Multiplication in `G` matches composition on oriented edges. -/
  mul_edge (g h : G) (e : C.skeleton.Edge) :
      (toAut (g * h)).edgePerm e =
        (toAut g).edgePerm ((toAut h).edgePerm e)
  /-- The identity element acts trivially on oriented faces. -/
  one_face (D : C.Face) :
      (toAut 1).facePerm D = D
  /-- Multiplication in `G` matches composition on oriented faces. -/
  mul_face (g h : G) (D : C.Face) :
      (toAut (g * h)).facePerm D =
        (toAut g).facePerm ((toAut h).facePerm D)

namespace AutAction

variable {G : Type u} [Group G] {C : TwoComplex}

instance : CoeFun (AutAction G C) fun _ ↦ G → Aut C :=
  ⟨AutAction.toAut⟩

/-- The induced action on geometric faces. -/
abbrev geometricFacePerm (ρ : AutAction G C) (g : G) :
    Equiv.Perm (GeometricFace C) :=
  (ρ g).geometricFacePerm

/-- The induced action on geometric edges. -/
abbrev geometricEdgePerm (ρ : AutAction G C) (g : G) :
    Equiv.Perm (OneComplex.GeometricEdge C.skeleton) :=
  (ρ g).geometricEdgePerm

/-- The action by automorphisms induces a homomorphism to the permutation group of geometric
faces. -/
private def toGeometricFacePermHom (ρ : AutAction G C) : G →* Equiv.Perm (GeometricFace C) where
  toFun := ρ.geometricFacePerm
  map_one' := by
    ext D
    refine Quotient.inductionOn D ?_
    intro D
    change Quotient.mk _ ((ρ 1).facePerm D) = Quotient.mk _ D
    simp [ρ.one_face D]
  map_mul' g h := by
    ext D
    refine Quotient.inductionOn D ?_
    intro D
    change Quotient.mk _ ((ρ (g * h)).facePerm D) =
      Quotient.mk _ ((ρ g).facePerm ((ρ h).facePerm D))
    simp [ρ.mul_face g h D]

/-- The induced action of `G` on geometric faces. -/
abbrev geometricFaceMulAction (ρ : AutAction G C) : MulAction G (GeometricFace C) :=
  MulAction.compHom (GeometricFace C) ρ.toGeometricFacePermHom

end AutAction

variable (C K : TwoComplex)

/-- A duality between `2`-complexes identifies vertices of one complex with geometric faces of the
other, geometric faces with vertices, and geometric edges on both sides, in a way compatible with
vertex-face incidence. -/
structure Duality where
  /-- Vertices of the first complex correspond to geometric faces of the second. -/
  vertexToFace : C.skeleton ≃ GeometricFace K
  /-- Geometric faces of the first complex correspond to vertices of the second. -/
  faceToVertex : GeometricFace C ≃ K.skeleton
  /-- Geometric edges correspond under the duality. -/
  edgeToEdge : OneComplex.GeometricEdge C.skeleton ≃ OneComplex.GeometricEdge K.skeleton
  /-- A vertex of `C` lies on an oriented face `D` exactly when the dual vertex of `D` lies on
  some oriented representative of the dual geometric face of that vertex in `K`. -/
  vertexOnFace_iff (v : C.skeleton) (D : C.Face) :
      C.VertexOnFace v D ↔
        ∃ E : K.Face, ⟦E⟧ = vertexToFace v ∧ K.VertexOnFace (faceToVertex ⟦D⟧) E

end TwoComplex

/-- A Fuchsian complex for `G` is an actual `2`-complex equipped with an action of `G` by
automorphisms of that complex. -/
structure FuchsianComplex (G : Type u) [Group G] where
  /-- The underlying `2`-complex. -/
  complex : TwoComplex.{v}
  /-- The action of `G` by automorphisms of the complex. -/
  action : TwoComplex.AutAction G complex

namespace FuchsianComplex

variable {G : Type u} [Group G]

/-- A Fuchsian complex is without reflections when no nontrivial group element fixes a geometric
edge. -/
def WithoutReflections (K : FuchsianComplex G) : Prop :=
  ∀ ⦃g : G⦄, g ≠ 1 →
    ∀ e : OneComplex.GeometricEdge K.complex.skeleton, (K.action g).geometricEdgePerm e ≠ e

end FuchsianComplex

/-- The relator set in the free group on ordinary and reflection generators determined by a family
of modified relator words. -/
def modifiedRelators
    {X : Type v} {J : Type w} {Rel : Type x}
    (relatorWord : Rel → List (SignedLetter X ⊕ J)) :
    Set (FreeGroup (X ⊕ J)) :=
  Set.range fun r ↦
    List.prod ((relatorWord r).map <|
      Sum.elim
        (SignedLetter.value fun x ↦ FreeGroup.of (Sum.inl x))
        fun j ↦ FreeGroup.of (Sum.inr j))

/-- A modified presentation of `G` consists of ordinary generators, involutory reflection
generators, and relators, together with the canonical statement that those relators present
`G`. -/
structure ModifiedPresentation (G : Type u) [Group G] where
  /-- The ordinary generators. -/
  X : Type v
  /-- The reflection generators. -/
  J : Type w
  /-- The relators. -/
  Rel : Type x
  /-- The boundary word attached to a relator, written in signed ordinary generators and
  reflection generators. -/
  relatorWord : Rel → List (SignedLetter X ⊕ J)
  /-- The corresponding relators present `G`. -/
  presentationEquiv : PresentedGroup (modifiedRelators relatorWord) ≃* G
  /-- Each reflection generator represents an involution in `G`. -/
  reflection_sq_eq_one (j : J) :
      presentationEquiv (PresentedGroup.of (Sum.inr j)) ^ 2 = 1

namespace ModifiedPresentation

variable {G : Type u} [Group G]

/-- The relators of a modified presentation, viewed as elements of the free group on the ordinary
and reflection generators. -/
abbrev relators (P : ModifiedPresentation G) : Set (FreeGroup (P.X ⊕ P.J)) :=
  modifiedRelators P.relatorWord

/-- The value in `G` of a signed ordinary generator or reflection generator in a modified
presentation. -/
def letterValue (P : ModifiedPresentation G) : SignedLetter P.X ⊕ P.J → G :=
  Sum.elim
    (SignedLetter.value fun x ↦ P.presentationEquiv (PresentedGroup.of (Sum.inl x)))
    fun j ↦ P.presentationEquiv (PresentedGroup.of (Sum.inr j))

/-- Each reflection generator evaluates to an involution in `G`. -/
theorem letterValue_reflection_sq_eq_one (P : ModifiedPresentation G) (j : P.J) :
    P.letterValue (Sum.inr j) ^ 2 = 1 :=
  P.reflection_sq_eq_one j

/-- A modified presentation is ordinary when it has no reflection letters. -/
def IsOrdinary (P : ModifiedPresentation G) : Prop :=
  IsEmpty P.J

end ModifiedPresentation

/-- A modified Cayley complex is an actual `2`-complex equipped with Cayley coordinates for the
signed letters and relators of a modified presentation, together with the statement that each
chosen oriented relator face boundary reads the corresponding relator word. -/
structure ModifiedCayleyComplex {G : Type u} [Group G] (P : ModifiedPresentation G) where
  /-- The underlying `2`-complex. -/
  complex : TwoComplex.{y}
  /-- Cayley coordinates on the complex using the signed letters of the modified presentation. -/
  coordinates : CayleyComplex.Coordinates complex P.letterValue P.Rel
  /-- The chosen oriented representative of the geometric face `(g, r)` has a boundary path based
  at the vertex `g` whose label word is exactly the relator word `r`. -/
  faceBoundary_word (g : G) (r : P.Rel) :
      (Quiver.Path.edgeList (coordinates.faceBoundary g r).1).map
          (fun e ↦ (coordinates.edgeEquiv e.hom.1).2) =
        P.relatorWord r

namespace ModifiedCayleyComplex

variable {G : Type u} [Group G]
variable {P : ModifiedPresentation G}

/-- A dual modified Cayley complex realizes a Fuchsian complex when the dual vertex of `gD` is the
translate by `g` of the dual vertex of `D`. -/
def RealizesFuchsianDuality (K : FuchsianComplex G) (C : ModifiedCayleyComplex P)
    (dual : C.complex.Duality K.complex) : Prop :=
  ∀ (g : G) (D : K.complex.GeometricFace),
    dual.vertexToFace.symm ((K.action g).geometricFacePerm D) =
      (C.coordinates.leftTranslation g).vertexPerm (dual.vertexToFace.symm D)

end ModifiedCayleyComplex

section Proposition371

variable {G : Type u} [Group G]

/-- Proposition 3-7-1 (1): every Fuchsian complex of `G` admits a modified presentation whose
modified Cayley complex is dual to it. -/
-- Proof sketch: choose a base face of the Fuchsian complex, use adjacent faces to define the
-- modified generating letters, construct the barycentric-dual `1`-skeleton, and read off the
-- relators from the bounded complementary regions.
theorem exists_modifiedPresentation_with_dual_modifiedCayleyComplex
    (K : FuchsianComplex G) :
    ∃ (P : ModifiedPresentation G) (C : ModifiedCayleyComplex P)
      (dual : C.complex.Duality K.complex),
      C.RealizesFuchsianDuality K dual := sorry

variable {P : ModifiedPresentation G}

/- Proposition 3-7-1 (2): in a dual modified Cayley complex, the vertex corresponding to the face
`gD` is the translate by `g` of the vertex corresponding to `D`. This is exactly the owner
predicate `ModifiedCayleyComplex.RealizesFuchsianDuality`, so the numbered item is recorded as a
direct recall of that canonical declaration rather than as a duplicate wrapper theorem. -/
#check (ModifiedCayleyComplex.RealizesFuchsianDuality :
  (K : FuchsianComplex G) → (C : ModifiedCayleyComplex P) →
    C.complex.Duality K.complex → Prop)

/-- Proposition 3-7-1 (3): if the Fuchsian complex has no reflections, the dual modified Cayley
complex may be chosen to come from an ordinary presentation. -/
-- Proof sketch: when no nontrivial element fixes a geometric edge, the reflection letters are
-- absent from the construction, so the same dual complex is obtained from an ordinary generating
-- set alone.
theorem exists_ordinaryCayleyComplex_with_dual_modifiedPresentation
    (K : FuchsianComplex G) (hK : K.WithoutReflections) :
    ∃ (P : ModifiedPresentation G) (_ : P.IsOrdinary) (C : ModifiedCayleyComplex P)
      (dual : C.complex.Duality K.complex),
      C.RealizesFuchsianDuality K dual := sorry

end Proposition371
