module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Logic.Small.Basic
public import Mathlib.Logic.Function.ULift
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.GroupAction.Basic
public import stacks_project.Chap04.Definition_4_19_1
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FunctorToTypes

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I] [Small.{w} I]

/-
Domain-style sampling for Lemma 4.19.4:
- source-facing hypothesis: every pair of objects admits a common successor
- sampled owner declarations in this domain:
  - `CategoryTheory.Limits.prodComparison`
  - `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
  - `CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types`
- primitive data: a pair of colimit representatives together with the source-level
  common-successor hypothesis
- derived API: the resulting surjectivity bridge for `prodComparison`
- best owner abstraction: the comparison morphism `prodComparison` itself; the source-facing
  theorem below is the weak bridge from common successors to surjectivity, while the stronger
  finite-limit preservation owner is only background because it proves more than this lemma needs
- target layer here: `bridge/view`, namely the surjectivity statement for `prodComparison`,
  with a thin `IsFilteredOrEmpty` corollary through the owner field
  `CategoryTheory.IsFilteredOrEmpty.cocone_objs`
-/

/-
Source/core/bridge triage for Lemma 4.19.4:
- `source-facing`: the explicit common-successor hypothesis on the index category
- `core/canonical`: the binary-product comparison morphism `prodComparison colim M N`
- `bridge/view`: surjectivity of that comparison under the weaker source hypothesis, plus the
  `IsFilteredOrEmpty` specialization obtained from `IsFilteredOrEmpty.cocone_objs`
-/

/-- Applied form of the first projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: compose `prodComparison` with the first projection from the binary product
-- isomorphism, then rewrite using the canonical `prodComparison_fst` compatibility together with
-- the explicit `Type` colimit map formula.
theorem prodComparison_colim_ι_fst (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
      colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := by
  -- Rewrite the first coordinate through the explicit `Type` binary-product isomorphism.
  have hIso :
      ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
        (Limits.prod.fst : colimit M ⨯ colimit N ⟶ colimit M)
          (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) := by
    simpa using
      congrFun (Types.binaryProductIso_hom_comp_fst (colimit M) (colimit N))
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))
  have hComp :
      (Limits.prod.fst : colimit M ⨯ colimit N ⟶ colimit M)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) =
        (colim.map (prod.fst : M ⨯ N ⟶ M)) (colimit.ι (M ⨯ N) k x) := by
    simpa using
      congrFun (prodComparison_fst (F := colim) (A := M) (B := N))
        (colimit.ι (M ⨯ N) k x)
  have hMap :
      (colim.map (prod.fst : M ⨯ N ⟶ M)) (colimit.ι (M ⨯ N) k x) =
        colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := by
    simpa using Types.Colimit.ι_map_apply (prod.fst : M ⨯ N ⟶ M) k x
  exact hIso.trans (hComp.trans hMap)

/-- Applied form of the second projection formula for the colimit binary-product comparison in
`Type`. -/
-- Proof sketch: this is the second-projection analogue of
-- `prodComparison_colim_ι_fst`, using `prodComparison_snd` and the `Type` colimit map formula for
-- `prod.snd`.
theorem prodComparison_colim_ι_snd (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
      colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := by
  -- Rewrite the second coordinate through the explicit `Type` binary-product isomorphism.
  have hIso :
      ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
        (Limits.prod.snd : colimit M ⨯ colimit N ⟶ colimit N)
          (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) := by
    simpa using
      congrFun (Types.binaryProductIso_hom_comp_snd (colimit M) (colimit N))
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x))
  have hComp :
      (Limits.prod.snd : colimit M ⨯ colimit N ⟶ colimit N)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) =
        (colim.map (prod.snd : M ⨯ N ⟶ N)) (colimit.ι (M ⨯ N) k x) := by
    simpa using
      congrFun (prodComparison_snd (F := colim) (A := M) (B := N))
        (colimit.ι (M ⨯ N) k x)
  have hMap :
      (colim.map (prod.snd : M ⨯ N ⟶ N)) (colimit.ι (M ⨯ N) k x) =
        colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := by
    simpa using Types.Colimit.ι_map_apply (prod.snd : M ⨯ N ⟶ N) k x
  exact hIso.trans (hComp.trans hMap)

-- Proof sketch: represent the two coordinates of a point in
-- `colimit M × colimit N` at possibly different stages, move both representatives to a common
-- successor using the source hypothesis, and then use the induced element of `(M ⨯ N).obj k` to
-- build a preimage under `prodComparison`.
/-- Lemma 4.19.4 (1): if every pair of objects in the index category admits a common successor,
then the canonical comparison map
`colimit (M ⨯ N) ⟶ colimit M × colimit N`
is surjective for `Type`-valued diagrams `M` and `N`. -/
theorem prodComparison_colim_surjective_of_commonSuccessor
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (M N : I ⥤ Type w)
    : Function.Surjective (prodComparison colim M N) := by
  classical
  intro y
  let e := Types.binaryProductIso (colimit M) (colimit N)
  -- Choose representatives for the two coordinates of the target pair.
  obtain ⟨i, m, hm⟩ := Types.jointly_surjective' (e.hom y).1
  obtain ⟨j, n, hn⟩ := Types.jointly_surjective' (e.hom y).2
  -- Move both representatives to a common successor stage.
  obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hObj i j
  let x : (M ⨯ N).obj k := FunctorToTypes.prodMk (F := M) (G := N) (M.map f m) (N.map g n)
  refine ⟨colimit.ι (M ⨯ N) k x, ?_⟩
  -- Compare after applying the explicit `Type` product isomorphism and checking coordinates.
  have hxy :
      e.hom (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) = e.hom y := by
    ext
    · rw [prodComparison_colim_ι_fst]
      simpa [x, hm]
    · rw [prodComparison_colim_ι_snd]
      simpa [x, hn]
  exact by
    apply (congrArg e.inv) at hxy
    simpa [e] using hxy

/-- For a filtered-or-empty index category, the common-successor hypothesis is already available
from the owner field `CategoryTheory.IsFilteredOrEmpty.cocone_objs`, so the surjectivity
statement is just the preceding source-facing bridge specialized to that canonical API. -/
-- Proof sketch: apply `prodComparison_colim_surjective_of_commonSuccessor` and obtain the common
-- successor from `IsFilteredOrEmpty.cocone_objs`.
theorem prodComparison_colim_surjective_of_isFilteredOrEmpty [IsFilteredOrEmpty I]
    (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := by
  -- Extract the common successor promised by filteredness and invoke the source-facing theorem.
  apply prodComparison_colim_surjective_of_commonSuccessor
  intro i j
  obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs i j
  exact ⟨k, ⟨f⟩, ⟨g⟩⟩

/-- Helper for Lemma 4.19.4: `OneObjCat G` is the one-object category in universe `u` whose
endomorphism monoid is `G`. -/
@[nolint unusedArguments]
def OneObjCat (_ : Type v) : Type u := ULift.{u} Unit

instance (G : Type v) [Monoid G] : Category.{v} (OneObjCat G) where
  Hom _ _ := G
  id _ := 1
  comp f g := g * f
  comp_id := by
    intro X Y f
    exact one_mul f
  id_comp := by
    intro X Y f
    exact mul_one f
  assoc := by
    intro W X Y Z f g h
    exact (mul_assoc h g f).symm

instance (G : Type v) : Subsingleton (OneObjCat G) := ⟨fun a b ↦ by
  cases a
  cases b
  rfl⟩

instance (G : Type v) : Small.{w} (OneObjCat G) := by
  infer_instance

/-- Helper for Lemma 4.19.4: the unique object of `OneObjCat G`. -/
abbrev oneObj (G : Type v) : OneObjCat G := ULift.up ()

/-- Helper for Lemma 4.19.4: a multiplicative action `G ↻ X` viewed as a `Type`-valued diagram on
the one-object category `OneObjCat G`. -/
def oneObjActionFunctor (G : Type v) [Monoid G] (X : Type w) [MulAction G X] :
    OneObjCat G ⥤ Type w where
  obj _ := X
  map := fun {_ _} g x ↦ g • x
  map_id := fun _ ↦ funext fun x ↦ one_smul G x
  map_comp := fun {_ _ _} f g ↦ funext fun x ↦ (smul_smul g f x).symm

/-- Helper for Lemma 4.19.4: `ULift P` acts on `ULift P` by left translation. -/
instance uliftLeftMulAction (P : Type) [Group P] : MulAction (ULift.{v} P) (ULift.{w} P) where
  smul g x := ULift.up (g.down * x.down)
  one_smul x := by
    -- Unfold the lifted action and reduce to the unit law in `P`.
    change ULift.up ((1 : P) * x.down) = x
    simpa
  mul_smul g h x := by
    -- Both sides reduce to the same multiplication expression in `P`.
    change ULift.up (((g * h).down) * x.down) = ULift.up (g.down * (h.down * x.down))
    simp [mul_assoc]

/-- Helper for Lemma 4.19.4: the colimit relation of a one-object action diagram is the orbit
relation of the underlying action. -/
theorem oneObjAction_colimitTypeRel_iff_orbitRel
    (G : Type v) [Group G] (X : Type w) [MulAction G X] (x y : X) :
    (oneObjActionFunctor G X).ColimitTypeRel ⟨oneObj G, x⟩ ⟨oneObj G, y⟩ ↔
      MulAction.orbitRel G X x y := by
  -- Rewrite the orbit relation as an existence statement and compare it to the explicit
  -- one-object colimit relation.
  have hshape :
      (oneObjActionFunctor G X).ColimitTypeRel ⟨oneObj G, x⟩ ⟨oneObj G, y⟩ ↔
        ∃ g : G, y = g • x := by
    rfl
  rw [hshape, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp⟩
  · rintro ⟨g, hg⟩
    have h' : g⁻¹ • x = y := by
      simpa [hg] using smul_smul g⁻¹ g y
    exact ⟨g⁻¹, h'.symm⟩

/-- Helper for Lemma 4.19.4: the sigma type of representatives for a one-object action diagram is
canonically equivalent to the underlying set. -/
noncomputable def oneObjAction_sigmaEquiv (G : Type v) (X : Type w) :
    (Sigma fun _ : OneObjCat G ↦ X) ≃ X where
  toFun p := p.2
  invFun x := ⟨oneObj G, x⟩
  left_inv p := by
    cases p with
    | mk j x =>
        rw [Subsingleton.elim j (oneObj G)]
  right_inv x := rfl

/-- Helper for Lemma 4.19.4: under `oneObjAction_sigmaEquiv`, the concrete one-object colimit
relation becomes the orbit relation. -/
theorem oneObjAction_colimitTypeRel_iff_orbitRel_all
    (G : Type v) [Group G] (X : Type w) [MulAction G X]
    (p q : Sigma fun _ : OneObjCat G ↦ X) :
    (oneObjActionFunctor G X).ColimitTypeRel p q ↔
      MulAction.orbitRel G X (oneObjAction_sigmaEquiv G X p) (oneObjAction_sigmaEquiv G X q) := by
  -- Reduce to the unique object and then apply the pointwise orbit-relation comparison.
  cases p
  cases q
  simpa [oneObjAction_sigmaEquiv] using oneObjAction_colimitTypeRel_iff_orbitRel G X _ _

/-- Helper for Lemma 4.19.4: the concrete colimit quotient of a one-object action diagram is the
orbit quotient. -/
noncomputable def oneObjAction_colimitTypeRelEquivOrbitRelQuotient
    (G : Type v) [Group G] (X : Type w) [MulAction G X] :
    (oneObjActionFunctor G X).ColimitType ≃ MulAction.orbitRel.Quotient G X :=
  Quot.congr (oneObjAction_sigmaEquiv G X) (oneObjAction_colimitTypeRel_iff_orbitRel_all G X)

/-- Helper for Lemma 4.19.4: the colimit of a one-object action diagram is the corresponding
orbit quotient. -/
noncomputable def oneObjAction_colimitEquivQuotient
    (G : Type v) [Group G] (X : Type w) [MulAction G X] :
    colimit (oneObjActionFunctor G X) ≃ MulAction.orbitRel.Quotient G X :=
  (Types.colimitEquivColimitType (oneObjActionFunctor G X)).trans
    (oneObjAction_colimitTypeRelEquivOrbitRelQuotient G X)

/-- Helper for Lemma 4.19.4: a stage representative of a one-object action diagram maps to its
orbit class under the colimit/orbit quotient equivalence. -/
theorem oneObjAction_colimitEquivQuotient_ι
    (G : Type v) [Group G] (X : Type w) [MulAction G X] (x : X) :
    oneObjAction_colimitEquivQuotient G X
      (colimit.ι (oneObjActionFunctor G X) (oneObj G) x) = Quotient.mk'' x := by
  -- Expand the explicit colimit model and evaluate both quotient maps on a representative.
  change oneObjAction_colimitTypeRelEquivOrbitRelQuotient G X
      ((Types.colimitEquivColimitType (oneObjActionFunctor G X))
        (colimit.ι (oneObjActionFunctor G X) (oneObj G) x)) = Quotient.mk'' x
  rw [Types.colimitEquivColimitType_apply]
  rfl

/-- Helper for Lemma 4.19.4: the orbit quotient of the regular left-translation action is a
singleton. -/
theorem left_translation_orbit_quotient_subsingleton (P : Type) [Group P] :
    Subsingleton (MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P)) := by
  -- Any two points differ by left translation by `x * y⁻¹`, so all orbit classes coincide.
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  apply Quotient.sound
  change MulAction.orbitRel (ULift.{v} P) (ULift.{w} P) x y
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨ULift.up (x.down * y.down⁻¹), ?_⟩
  change ULift.up ((x.down * y.down⁻¹) * y.down) = x
  simpa [mul_assoc]

/-- Helper for Lemma 4.19.4: all stage representatives coincide in the colimit of the regular
left-translation action. -/
theorem left_translation_colimit_eq (P : Type) [Group P] (x y : ULift.{w} P) :
    colimit.ι (oneObjActionFunctor (ULift.{v} P) (ULift.{w} P))
      (oneObj (ULift.{v} P)) x =
    colimit.ι (oneObjActionFunctor (ULift.{v} P) (ULift.{w} P))
      (oneObj (ULift.{v} P)) y := by
  -- Pass to orbit classes, where the regular-action quotient is already a singleton.
  apply (oneObjAction_colimitEquivQuotient (ULift.{v} P) (ULift.{w} P)).injective
  rw [oneObjAction_colimitEquivQuotient_ι, oneObjAction_colimitEquivQuotient_ι]
  let hsub : Subsingleton (MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P)) :=
    left_translation_orbit_quotient_subsingleton (P := P)
  exact @Subsingleton.elim _ hsub _ _

/-- Helper for Lemma 4.19.4: for the diagonal left-translation action, the orbit classes of
`(1, 1)` and `(1, s)` are distinct whenever `s ≠ 1`. -/
theorem diagonal_left_translation_orbit_classes_ne
    (P : Type) [Group P] (s : ULift.{w} P) (hs : s ≠ 1) :
    (Quotient.mk'' ((1 : ULift.{w} P), (1 : ULift.{w} P)) :
      MulAction.orbitRel.Quotient (ULift.{v} P) (ULift.{w} P × ULift.{w} P)) ≠
      Quotient.mk'' ((1 : ULift.{w} P), s) := by
  -- Compare the two coordinates of a hypothetical diagonal-translation witness.
  intro hq
  have horbit :
      MulAction.orbitRel (ULift.{v} P) (ULift.{w} P × ULift.{w} P)
        ((1 : ULift.{w} P), (1 : ULift.{w} P)) ((1 : ULift.{w} P), s) := Quotient.eq''.mp hq
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  rcases horbit with ⟨g, hg⟩
  have hfst : g • (1 : ULift.{w} P) = (1 : ULift.{w} P) := by
    simpa using congrArg (fun z : ULift.{w} P × ULift.{w} P ↦ z.1) hg
  have hsnd : g • s = (1 : ULift.{w} P) := by
    simpa using congrArg (fun z : ULift.{w} P × ULift.{w} P ↦ z.2) hg
  cases s with
  | up t =>
      -- The first coordinate forces `g = 1`, and then the second forces `t = 1`.
      have hgdown : g.down = 1 := by
        have hfst' : g.down * 1 = 1 := by
          change ULift.down (g • (1 : ULift.{w} P)) = 1
          simpa using congrArg ULift.down hfst
        simpa using hfst'
      have hsdown : g.down * t = 1 := by
        simpa using congrArg ULift.down hsnd
      have ht : t = 1 := by
        simpa [hgdown] using hsdown
      apply hs
      change ULift.up t = ULift.up 1
      simp [ht]

-- Proof sketch: take the one-object category attached to a nontrivial group acting on itself by
-- translation; then the colimit of the diagonal action on `G × G` has more than one orbit, while
-- the product of the two quotient colimits is a singleton.
/-- Lemma 4.19.4 (2): even if every pair of objects in the index category admits a common
successor, colimits of `Type`-valued diagrams do not in general commute with finite nonempty
products; in fact, there is already a counterexample for binary products. -/
theorem colimits_of_set_valued_diagrams_need_not_commute_with_binary_products :
    ∃ (J : Type u) (_ : Category.{v} J) (_ : Small.{w} J)
      (_ : ∀ i j : J, ∃ k : J, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
      (F G : J ⥤ Type w),
        ¬ Function.Bijective (prodComparison colim F G) := by
  let G : Type v := ULift.{v} (Equiv.Perm Bool)
  let X : Type w := ULift.{w} (Equiv.Perm Bool)
  let F : OneObjCat G ⥤ Type w := oneObjActionFunctor G X
  refine ⟨OneObjCat G, inferInstance, inferInstance, ?_, F, F, ?_⟩
  · -- The witness category has one object, so any pair of objects has the same common successor.
    intro i j
    cases i
    cases j
    exact ⟨oneObj G, ⟨(1 : G)⟩, ⟨(1 : G)⟩⟩
  · -- Choose the two diagonal-orbit representatives that collapse after applying
    -- `prodComparison`, but remain distinct in the source colimit.
    let s : X := ULift.up (Equiv.swap true false)
    have hs : s ≠ 1 := by
      -- The transposition of `true` and `false` is not the identity permutation.
      intro hsEq
      have hdown : Equiv.swap true false = 1 := by
        change ULift.up (Equiv.swap true false) = ULift.up 1 at hsEq
        simpa using congrArg ULift.down hsEq
      have htrue := congrArg (fun e : Equiv.Perm Bool ↦ e true) hdown
      simp at htrue
    let ab : (F ⨯ F).obj (oneObj G) := FunctorToTypes.prodMk (F := F) (G := F) (1 : X) (1 : X)
    let as : (F ⨯ F).obj (oneObj G) := FunctorToTypes.prodMk (F := F) (G := F) (1 : X) s
    let a : colimit (F ⨯ F) :=
      colimit.ι (F ⨯ F) (oneObj G) ab
    let b : colimit (F ⨯ F) :=
      colimit.ι (F ⨯ F) (oneObj G) as
    intro hbij
    have hEqImage : prodComparison colim F F a = prodComparison colim F F b := by
      -- Compare after identifying the binary product in `Type`, and compute both projections.
      let e := Types.binaryProductIso (colimit F) (colimit F)
      have hxy : e.hom (prodComparison colim F F a) = e.hom (prodComparison colim F F b) := by
        ext
        · rw [prodComparison_colim_ι_fst, prodComparison_colim_ι_fst]
          simp [ab, as, F, FunctorToTypes.prodMk_fst]
        · rw [prodComparison_colim_ι_snd, prodComparison_colim_ι_snd]
          simpa [a, b, ab, as, F, FunctorToTypes.prodMk_snd] using
            left_translation_colimit_eq (P := Equiv.Perm Bool) (x := (1 : X)) (y := s)
      apply (congrArg e.inv) at hxy
      simpa [e] using hxy
    have hneq : a ≠ b := by
      -- Convert equality in the source colimit to equality of orbit classes and use the diagonal
      -- invariant.
      intro hab
      have hmap :
          colim.map ((FunctorToTypes.binaryProductIso F F).hom) a =
            colim.map ((FunctorToTypes.binaryProductIso F F).hom) b := by
        simpa [hab]
      have hq :
          (Quotient.mk'' ((1 : X), (1 : X)) :
            MulAction.orbitRel.Quotient G (X × X)) =
            Quotient.mk'' ((1 : X), s) := by
        have hqcolim :
            oneObjAction_colimitEquivQuotient G (X × X)
              (colim.map ((FunctorToTypes.binaryProductIso F F).hom) a) =
            oneObjAction_colimitEquivQuotient G (X × X)
              (colim.map ((FunctorToTypes.binaryProductIso F F).hom) b) := by
          exact congrArg (fun z ↦ oneObjAction_colimitEquivQuotient G (X × X) z) hmap
        have hqcolim' :
            colimit.ι (FunctorToTypes.prod F F) (oneObj G) ((1 : X), (1 : X)) =
              colimit.ι (FunctorToTypes.prod F F) (oneObj G) ((1 : X), s) := by
          simpa [a, b, ab, as, FunctorToTypes.prodMk, Types.Colimit.ι_map_apply] using hqcolim
        have hqcolim'' :
            colimit.ι (oneObjActionFunctor G (X × X)) (oneObj G) ((1 : X), (1 : X)) =
              colimit.ι (oneObjActionFunctor G (X × X)) (oneObj G) ((1 : X), s) := by
          simpa [F, oneObjActionFunctor] using hqcolim'
        simpa [oneObjAction_colimitEquivQuotient_ι] using
          congrArg (fun z ↦ oneObjAction_colimitEquivQuotient G (X × X) z) hqcolim''
      exact (diagonal_left_translation_orbit_classes_ne (P := Equiv.Perm Bool) (s := s) hs) hq
    exact hneq (hbij.1 hEqImage)

end CategoryTheory.Limits
