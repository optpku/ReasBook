module

public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Limits
public import stacks_project.Chap06.ClosedSubsetInclusion
public import stacks_project.Chap06.Lemma_6_32_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

/- Domain-style sampling for Remark 6.32.5:
- primary domain: right exactness of sheaf pushforward along the inclusion of a closed subset of a
  topological space;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `rightExactFunctor`,
  `rightExactFunctor_iff`;
- owner abstraction: the chapter owner is
  `rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ)`, built from the canonical inclusion
  `TopCat.closedSubsetInclusion X Z`;
- primitive data: the ambient space `X`, the closed subset `Z`, the properness witness
  `Z ≠ Set.univ`, and the functor `Sheaf.pushforward (Type u) iZ`;
- derived API: failure to preserve binary coproducts as the witness, the equivalent
  finite-colimit formulation via `rightExactFunctor_iff`, and the consequence that pushforward has
  no right adjoint.

Source/core/bridge triage:
- `source-facing`: the Stacks-project remark that pushforward from a proper closed subset is not
  right exact on sheaves of sets;
- `core/canonical`: `rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ)`;
- `bridge/view`: the binary-coproduct obstruction, the reformulation via
  `PreservesFiniteColimits`, and the no-right-adjoint consequence. -/

local notation "iZ" => X.closedSubsetInclusion Z

/-- Helper for Remark 6.32.5: the underlying presheaf diagram of the binary pair `(T,T)` is
definitionally the pair of the underlying presheaves. -/
private theorem pairForgetEq
    (T : TopCat.Sheaf (Type u) (TopCat.of Z)) :
    pair T T ⋙ TopCat.Sheaf.forget (Type u) (TopCat.of Z) = pair T.presheaf T.presheaf := by
  -- This removes a recurring transport mismatch between the sheaf diagram and its underlying
  -- presheaf diagram.
  ext j
  cases j <;> rfl

/-- Helper for Remark 6.32.5: outside the closed subset, the stalk of the pushforward of a sheaf
of sets is a subsingleton. -/
private theorem pushforwardStalkSubsingletonOfNotMem
    (hZ : IsClosed Z) (F : TopCat.Sheaf (Type u) (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Subsingleton ((((Sheaf.pushforward (Type u) iZ).obj F).presheaf).stalk x) := by
  letI :
      IsIso
        (terminal.from
          (((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x)) :=
    closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem (X := X) (Z := Z) hZ F hx
  let hTerminal :
      IsTerminal (((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x) :=
    IsTerminal.ofIso terminalIsTerminal
      (asIso (terminal.from (((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x))).symm
  letI : Unique ((((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x)) :=
    CategoryTheory.Limits.Types.isTerminalEquivUnique _ hTerminal
  -- Repackage Lemma 6.32.1 into the `Subsingleton` form needed for the contradiction.
  infer_instance

/-- Helper for Remark 6.32.5: outside the closed subset, the stalk of the pushforward of a sheaf
of sets is inhabited. -/
private theorem pushforwardStalkNonemptyOfNotMem
    (hZ : IsClosed Z) (F : TopCat.Sheaf (Type u) (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty ((((Sheaf.pushforward (Type u) iZ).obj F).presheaf).stalk x) := by
  letI :
      IsIso
        (terminal.from
          (((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x)) :=
    closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem (X := X) (Z := Z) hZ F hx
  -- Choose the preimage of the unique point of the terminal object through the stalk isomorphism.
  exact ⟨(asIso (terminal.from (((Sheaf.pushforward (Type u) iZ).obj F).presheaf.stalk x))).inv
    default⟩

/-- Helper for Remark 6.32.5: the pair of terminal sheaves admits an explicit colimit cocone,
obtained by sheafifying the colimit cocone in presheaves. -/
private theorem terminalSheafUnderlyingPairColimitCocone
    (T : TopCat.Sheaf (Type u) (TopCat.of Z)) :
    Nonempty (ColimitCocone (pair T.presheaf T.presheaf)) := by
  -- Use the explicit pointwise binary-coproduct cocone for type-valued functors, avoiding a large
  -- generic instance search in the functor category.
  exact ⟨CategoryTheory.FunctorToTypes.binaryCoproductColimitCocone T.presheaf T.presheaf⟩

/-- Helper for Remark 6.32.5: the pair of terminal sheaves admits an explicit colimit cocone,
obtained by sheafifying the colimit cocone in presheaves. -/
private theorem terminalSheafPairColimitCocone
    (T : TopCat.Sheaf (Type u) (TopCat.of Z)) :
    Nonempty (ColimitCocone (pair T T)) := by
  obtain ⟨E⟩ := terminalSheafUnderlyingPairColimitCocone (X := X) (Z := Z) T
  let E' : Cocone (pair T T ⋙ TopCat.Sheaf.forget (Type u) (TopCat.of Z)) :=
    (Cocone.precompose (eqToIso (pairForgetEq (X := X) (Z := Z) T)).hom).obj E.cocone
  let hE' : IsColimit E' :=
    (IsColimit.precomposeHomEquiv (eqToIso (pairForgetEq (X := X) (Z := Z) T)) E.cocone).symm
      E.isColimit
  -- The sheaf-category colimit is the sheafification of the presheaf colimit cocone.
  exact ⟨⟨Sheaf.sheafifyCocone E', Sheaf.isColimitSheafifyCocone E' hE'⟩⟩

/-- Helper for Remark 6.32.5: any colimit of two inhabited singleton types in `Type` has a point
lying in each summand image, so its cocone point cannot be a subsingleton. -/
private theorem binaryCofanPointNotSubsingletonOfSingletonSummands
    {A B : Type u} [Subsingleton A] [Inhabited A] [Subsingleton B] [Inhabited B]
    (c : BinaryCofan A B) (hc : IsColimit c) :
    ¬ Subsingleton c.pt := by
  intro hsub
  letI : Subsingleton c.pt := hsub
  let a : A := default
  let b : B := default
  rcases (CategoryTheory.Limits.Types.binaryCofan_isColimit_iff c).1 ⟨hc⟩ with ⟨_, _, hCompl⟩
  have hdisj := Set.disjoint_left.mp hCompl.disjoint
  have hmeml : c.inl a ∈ Set.range c.inl := ⟨a, rfl⟩
  have hmemr : c.inl a ∈ Set.range c.inr := by
    refine ⟨b, ?_⟩
    exact @Subsingleton.elim c.pt hsub (c.inr b) (c.inl a)
  -- A subsingleton cocone point would force the two coproduct summands to meet.
  exact hdisj hmeml hmemr

-- Proof sketch: evaluate pushforward at a point `x ∉ Z`. By Lemma 6.32.1 the stalk there is
-- terminal, so the pushforward of the coproduct of two copies of the terminal sheaf has one-point
-- stalk at `x`, whereas the coproduct of the two pushforward sheaves has two-point stalk there.
-- Since stalk functors preserve finite colimits, pushforward cannot preserve that coproduct.
/-- Remark 6.32.5 (1): if `i : Z ↪ X` is the inclusion of a proper closed subset, then pushforward on
sheaves of sets along `i` does not preserve binary coproducts. The Stacks argument tests the
coproduct of two copies of the terminal sheaf. -/
theorem closedSubsetTypeSheafPushforward_not_preservesBinaryCoproducts
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Sheaf.pushforward (Type u) iZ) := by
  intro hpres
  classical
  letI : PreservesColimitsOfShape (Discrete WalkingPair) (Sheaf.pushforward (Type u) iZ) := hpres
  have hnotforall : ¬ ∀ x : X, x ∈ Z := by
    intro hx
    apply hproper
    exact Set.eq_univ_iff_forall.mpr hx
  obtain ⟨x, hx⟩ := not_forall.mp hnotforall
  let T : TopCat.Sheaf (Type u) (TopCat.of Z) := ⊤_ TopCat.Sheaf (Type u) (TopCat.of Z)
  let S : TopCat.Sheaf (Type u) X ⥤ Type u :=
    TopCat.Sheaf.forget (Type u) X ⋙ TopCat.Presheaf.stalkFunctor (Type u) x
  let G : TopCat.Sheaf (Type u) (TopCat.of Z) ⥤ Type u :=
    Sheaf.pushforward (Type u) iZ ⋙ S
  letI : PreservesColimitsOfShape (Discrete WalkingPair) S := inferInstance
  obtain ⟨colimF⟩ := terminalSheafPairColimitCocone (X := X) (Z := Z) T
  let c := colimF.cocone
  let hc := colimF.isColimit
  letI : HasColimit (pair T T) := HasColimit.mk ⟨c, hc⟩
  let cT : BinaryCofan T T :=
    BinaryCofan.mk (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩)
  have hcT : IsColimit cT := by
    -- Repackage the explicit colimit cocone as a binary cofan so the preservation lemma applies.
    refine IsColimit.ofIsoColimit hc ?_
    refine Cocone.ext (Iso.refl _) ?_
    rintro (_ | _) <;> simp [c, cT]
  letI : PreservesColimit (pair T T) G := inferInstance
  let cG : BinaryCofan (G.obj T) (G.obj T) :=
    BinaryCofan.mk (G.map cT.inl) (G.map cT.inr)
  have hcG : IsColimit cG := mapIsColimitOfPreservesOfIsColimit G cT.inl cT.inr hcT
  have hLeftSubsingleton : Subsingleton (G.obj cT.pt) := by
    -- The stalk of the pushed source colimit is still terminal outside `Z`.
    simpa [cT, c, G, S] using
      (pushforwardStalkSubsingletonOfNotMem (X := X) (Z := Z) hZ cT.pt hx)
  have hFactorSubsingleton : Subsingleton (G.obj T) := by
    -- Each pushed terminal sheaf has singleton stalk outside `Z`.
    simpa [G, S, T] using
      (pushforwardStalkSubsingletonOfNotMem (X := X) (Z := Z) hZ T hx)
  have hFactorNonempty : Nonempty (G.obj T) := by
    -- The same terminality also gives an actual stalk element in each summand.
    simpa [G, S, T] using
      (pushforwardStalkNonemptyOfNotMem (X := X) (Z := Z) hZ T hx)
  letI : Subsingleton (G.obj T) := hFactorSubsingleton
  letI : Inhabited (G.obj T) := Classical.inhabited_of_nonempty hFactorNonempty
  -- But any colimit of two inhabited singleton types in `Type` has two distinct image points.
  exact binaryCofanPointNotSubsingletonOfSingletonSummands cG hcG hLeftSubsingleton

/-- Remark 6.32.5 (2): if `i : Z ↪ X` is the inclusion of a proper closed subset, then pushforward on
sheaves of sets along `i` is not right exact. The binary-coproduct obstruction above is the
source-facing witness for the canonical owner predicate `rightExactFunctor`. -/
theorem closedSubsetTypeSheafPushforward_not_rightExact
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ) := by
  intro hright
  let _ : PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ) := by
    simpa [rightExactFunctor_iff] using hright
  exact closedSubsetTypeSheafPushforward_not_preservesBinaryCoproducts hZ hproper inferInstance

/-- Companion bridge for Remark 6.32.5: pushforward on sheaves of sets along the inclusion of a
proper closed subset does not preserve finite colimits. This is just
`closedSubsetTypeSheafPushforward_not_rightExact` rewritten through `rightExactFunctor_iff`. -/
theorem closedSubsetTypeSheafPushforward_not_preservesFiniteColimits
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ) := by
  simpa [rightExactFunctor_iff] using
    (closedSubsetTypeSheafPushforward_not_rightExact hZ hproper)

-- Proof sketch: a left adjoint preserves all colimits, hence is right exact. Apply the owner-level
-- obstruction above to the pushforward functor along the proper closed-subset inclusion.
/-- Pushforward on sheaves of sets along the inclusion of a proper closed subset has no right
adjoint. -/
theorem closedSubsetTypeSheafPushforward_not_isLeftAdjoint
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ (Sheaf.pushforward (Type u) iZ).IsLeftAdjoint := by
  intro hleft
  let _ : (Sheaf.pushforward (Type u) iZ).IsLeftAdjoint := hleft
  exact
    closedSubsetTypeSheafPushforward_not_rightExact hZ hproper
      (by
        simpa [rightExactFunctor_iff] using
          (inferInstance : PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ)))

end
