module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopCat TopCat.Sheaf TopologicalSpace

noncomputable section

/-
Domain-style sampling for Example 7.41.3:
- primary domain: pushforward of sheaves of sets along a fixed continuous map of spaces, together
  with the finite-colimit preservation predicates `PreservesColimitsOfShape WalkingParallelPair`
  and `PreservesColimitsOfShape WalkingSpan`;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward`,
  `TopCat.discrete.map`,
  `Functor.sheafPushforwardContinuous`,
  `MorphismOfTopoiIn.pushforward`;
- owner abstraction: the core owner is the canonical sheaf-pushforward functor
  `TopCat.Sheaf.pushforward`, specialized here to the collapse map from the discrete two-point
  space to the one-point space;
- primitive data: only the fixed continuous map `Fin 2 → PUnit`;
- derived API: the two non-preservation statements for coequalizers and pushouts.

Source/core/bridge triage:
- `source-facing`: the Stacks counterexample for the direct image along the two-point collapse map;
- `core/canonical`: the functor
  `pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))`;
- `bridge/view`: the identification of this pushforward with binary product on pairs of sets used
  in the proof sketch.

There is no upstream chapter-local duplicate owner here: the correct public surface is the
canonical pushforward functor itself. Since the file only exports the two counterexample
statements, the right public surface is the explicit canonical owner term rather than a local alias
for the fixed collapse map or its pushforward.
-/

namespace Example_7_41_3

/-- Helper for Example 7.41.3: the discrete two-point source space. -/
private abbrev X₂ : TopCat := TopCat.of (Fin 2)

/-- Helper for Example 7.41.3: the one-point target space. -/
private abbrev Y₁ : TopCat := TopCat.of PUnit

/-- Helper for Example 7.41.3: the collapse map from the discrete two-point space to the point. -/
private abbrev collapseMap : X₂ ⟶ Y₁ :=
  TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit)

/-- Helper for Example 7.41.3: the singleton open containing `0`. -/
private def U₀ : Opens X₂ := ⟨{0}, isOpen_discrete _⟩

/-- Helper for Example 7.41.3: the singleton open containing `1`. -/
private def U₁ : Opens X₂ := ⟨{1}, isOpen_discrete _⟩

/-- Helper for Example 7.41.3: the top open of the two-point space. -/
private def Utop : Opens X₂ := ⟨Set.univ, isOpen_discrete _⟩

/-- Helper for Example 7.41.3: the top open of the point space. -/
private def Vtop : Opens Y₁ := ⟨Set.univ, isOpen_univ⟩

/-- Helper for Example 7.41.3: the collapse map pulls the top open of the point back to the top
open of the two-point space. -/
private lemma collapseMap_preimage_Vtop : (Opens.map collapseMap).obj Vtop = Utop := by
  ext x
  constructor
  · intro hx
    simp [Utop]
  · intro hx
    change collapseMap x ∈ Vtop
    simp [collapseMap, Vtop]

/-- Helper for Example 7.41.3: the family `(A₀, A₁)` realized as a dependent type on `Fin 2`. -/
private def pairFamily (A₀ A₁ : Type) : X₂ → Type := fun i ↦ if i = 0 then A₀ else A₁

/-- Helper for Example 7.41.3: the sheaf on the discrete two-point space corresponding to the pair
`(A₀, A₁)`. -/
private abbrev pairSheaf (A₀ A₁ : Type) : Sheaf Type X₂ :=
  X₂.sheafToTypes (pairFamily A₀ A₁)

/-- Helper for Example 7.41.3: pointwise maps of the underlying pair family induce sheaf maps. -/
private def pairFamilyMap {A₀ A₁ B₀ B₁ : Type} (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (i : X₂) :
    pairFamily A₀ A₁ i → pairFamily B₀ B₁ i := by
  by_cases h : i = 0
  · simpa [pairFamily, h] using f₀
  · simpa [pairFamily, h] using f₁

/-- Helper for Example 7.41.3: the induced morphism between pair sheaves. -/
private def pairSheafMap {A₀ A₁ B₀ B₁ : Type} (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) :
    pairSheaf A₀ A₁ ⟶ pairSheaf B₀ B₁ :=
  ⟨
    { app := fun _ s x ↦ pairFamilyMap f₀ f₁ x.1 (s x)
      naturality := by
        intro U V i
        rfl }⟩

/-- Helper for Example 7.41.3: the witness map `a` uses the constant `false` on the first
component and the unique map out of `PEmpty` on the second. -/
private def a : pairSheaf PUnit PEmpty ⟶ pairSheaf Bool PUnit :=
  pairSheafMap (fun _ ↦ false) PEmpty.elim

/-- Helper for Example 7.41.3: the witness map `b` uses the constant `true` on the first
component and the unique map out of `PEmpty` on the second. -/
private def b : pairSheaf PUnit PEmpty ⟶ pairSheaf Bool PUnit :=
  pairSheafMap (fun _ ↦ true) PEmpty.elim

/-- Helper for Example 7.41.3: the quotient map collapses the first coordinate `Bool ⟶ PUnit` and
keeps the second coordinate unchanged. -/
private def q : pairSheaf Bool PUnit ⟶ pairSheaf PUnit PUnit :=
  pairSheafMap (fun _ ↦ PUnit.unit) (fun x ↦ x)

/-- Helper for Example 7.41.3: every open of the discrete two-point space is one of the four
obvious subsets. -/
private lemma eq_bot_or_u0_or_u1_or_utop (U : Opens X₂) :
    U = ⊥ ∨ U = U₀ ∨ U = U₁ ∨ U = Utop := by
  by_cases h0 : (0 : X₂) ∈ U
  · by_cases h1 : (1 : X₂) ∈ U
    · right
      right
      right
      ext x
      fin_cases x <;> simp [Utop, h0, h1]
    · right
      left
      ext x
      fin_cases x <;> simp [U₀, h0, h1]
  · by_cases h1 : (1 : X₂) ∈ U
    · right
      right
      left
      ext x
      fin_cases x
      · constructor
        · intro hx
          exact (h0 hx).elim
        · intro hx
          cases hx
      · simp [U₁, h1]
    · left
      ext x
      fin_cases x
      · constructor
        · intro hx
          exact (h0 hx).elim
        · intro hx
          cases hx
      · constructor
        · intro hx
          exact (h1 hx).elim
        · intro hx
          cases hx

/-- Helper for Example 7.41.3: the two parallel arrows have the same composite with `q`. -/
private theorem aq_eq_bq : a ≫ q = b ≫ q := by
  -- The source has only four opens, and the ones meeting the second point carry no sections.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rcases eq_bot_or_u0_or_u1_or_utop U.unop with hU | hU | hU | hU
  · have hU' : U = op ⊥ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    exact congrFun ((pairSheaf PUnit PUnit).isTerminalOfEmpty.hom_ext _ _) s
  · have hU' : U = op U₀ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    funext x
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    rfl
  · have hU' : U = op U₁ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    have hx : PEmpty := by
      simpa [pairFamily, U₁] using s ⟨1, by simp [U₁]⟩
    exact hx.elim
  · have hU' : U = op Utop := by
      cases U
      simpa using congrArg op hU
    subst hU'
    have hx : PEmpty := by
      simpa [pairFamily, Utop] using s ⟨1, by simp [Utop]⟩
    exact hx.elim

/-- Helper for Example 7.41.3: the singleton opens cover the top open. -/
private lemma utop_le_u0_sup_u1 : Utop ≤ U₀ ⊔ U₁ := by
  intro x hx
  fin_cases x <;> simp [U₀, U₁]

/-- Helper for Example 7.41.3: the singleton opens are disjoint. -/
private lemma u0_inf_u1_eq_bot : U₀ ⊓ U₁ = ⊥ := by
  ext x
  constructor
  · intro hx
    fin_cases x <;> simpa [U₀, U₁] using hx
  · intro hx
    cases hx

/-- Helper for Example 7.41.3: top sections are determined by their restrictions to the singleton
opens. -/
private lemma top_section_ext_of_singleton_restrictions {G : Sheaf Type X₂}
    {s t : G.1.obj (op Utop)}
    (hU₀ :
      G.1.map (homOfLE (show U₀ ≤ Utop by
        intro x _
        simp [Utop])).op s =
        G.1.map (homOfLE (show U₀ ≤ Utop by
          intro x _
          simp [Utop])).op t)
    (hU₁ :
      G.1.map (homOfLE (show U₁ ≤ Utop by
        intro x _
        simp [Utop])).op s =
        G.1.map (homOfLE (show U₁ ≤ Utop by
          intro x _
          simp [Utop])).op t) :
    s = t := by
  -- Compare the two top sections on the concrete cover `U₀ ∪ U₁ = Utop`.
  refine G.eq_of_locally_eq₂
    (homOfLE (show U₀ ≤ Utop by
      intro x _
      simp [Utop]))
    (homOfLE (show U₁ ≤ Utop by
      intro x _
      simp [Utop]))
    utop_le_u0_sup_u1 s t hU₀ hU₁

/-- Helper for Example 7.41.3: a morphism out of a pair sheaf on the discrete two-point space is
determined by its components on the two singleton opens. -/
private lemma pair_hom_ext_of_singleton_apps {A₀ A₁ : Type} {G : Sheaf Type X₂}
    {φ ψ : pairSheaf A₀ A₁ ⟶ G} (hU₀ : φ.1.app (op U₀) = ψ.1.app (op U₀))
    (hU₁ : φ.1.app (op U₁) = ψ.1.app (op U₁)) : φ = ψ := by
  -- Check equality on each of the four opens; the top-open case reduces to singleton restrictions.
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rcases eq_bot_or_u0_or_u1_or_utop U.unop with hU | hU | hU | hU
  · have hU' : U = op ⊥ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    exact congrFun (G.isTerminalOfEmpty.hom_ext _ _) s
  · have hU' : U = op U₀ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    exact congrFun hU₀ s
  · have hU' : U = op U₁ := by
      cases U
      simpa using congrArg op hU
    subst hU'
    exact congrFun hU₁ s
  · have hU' : U = op Utop := by
      cases U
      simpa using congrArg op hU
    subst hU'
    -- Reduce equality on `Utop` to equality after restricting to `U₀` and `U₁`.
    refine top_section_ext_of_singleton_restrictions ?_ ?_
    · -- Naturality rewrites each restricted top section to the singleton component.
      calc
        G.1.map (homOfLE (show U₀ ≤ Utop by
          intro x _
          simp [Utop])).op (φ.1.app (op Utop) s) =
            φ.1.app (op U₀) ((pairSheaf A₀ A₁).1.map
              (homOfLE (show U₀ ≤ Utop by
                intro x _
                simp [Utop])).op s) := by
              symm
              simpa using congrFun
                (NatTrans.naturality φ.1
                  (homOfLE (show U₀ ≤ Utop by
                    intro x _
                    simp [Utop])).op) s
        _ =
            ψ.1.app (op U₀) ((pairSheaf A₀ A₁).1.map
              (homOfLE (show U₀ ≤ Utop by
                intro x _
                simp [Utop])).op s) := by
              exact congrFun hU₀ _
        _ =
            G.1.map (homOfLE (show U₀ ≤ Utop by
              intro x _
              simp [Utop])).op (ψ.1.app (op Utop) s) := by
              simpa using congrFun
                (NatTrans.naturality ψ.1
                  (homOfLE (show U₀ ≤ Utop by
                    intro x _
                    simp [Utop])).op) s
    · -- The same naturality argument works on the second singleton open.
      calc
        G.1.map (homOfLE (show U₁ ≤ Utop by
          intro x _
          simp [Utop])).op (φ.1.app (op Utop) s) =
            φ.1.app (op U₁) ((pairSheaf A₀ A₁).1.map
              (homOfLE (show U₁ ≤ Utop by
                intro x _
                simp [Utop])).op s) := by
              symm
              simpa using congrFun
                (NatTrans.naturality φ.1
                  (homOfLE (show U₁ ≤ Utop by
                    intro x _
                    simp [Utop])).op) s
        _ =
            ψ.1.app (op U₁) ((pairSheaf A₀ A₁).1.map
              (homOfLE (show U₁ ≤ Utop by
                intro x _
                simp [Utop])).op s) := by
              exact congrFun hU₁ _
        _ =
            G.1.map (homOfLE (show U₁ ≤ Utop by
              intro x _
              simp [Utop])).op (ψ.1.app (op Utop) s) := by
              simpa using congrFun
                (NatTrans.naturality ψ.1
                  (homOfLE (show U₁ ≤ Utop by
                    intro x _
                    simp [Utop])).op) s

/-- Helper for Example 7.41.3: the `false` top section of `(Bool, PUnit)`. -/
private def falseTop : (pairSheaf Bool PUnit).1.obj (op Utop) := fun x ↦ by
  by_cases h : (x : X₂) = 0
  · simpa [pairFamily, h] using false
  · simpa [pairFamily, h] using PUnit.unit

/-- Helper for Example 7.41.3: the `true` top section of `(Bool, PUnit)`. -/
private def trueTop : (pairSheaf Bool PUnit).1.obj (op Utop) := fun x ↦ by
  by_cases h : (x : X₂) = 0
  · simpa [pairFamily, h] using true
  · simpa [pairFamily, h] using PUnit.unit

/-- Helper for Example 7.41.3: the two top sections of `(Bool, PUnit)` are distinct. -/
private lemma falseTop_ne_trueTop : falseTop ≠ trueTop := by
  intro h
  have h0 := congrFun h ⟨0, by simp [Utop]⟩
  simpa [falseTop, trueTop, pairFamily] using h0

/-- Helper for Example 7.41.3: the top sections of `(PUnit, PEmpty)` are empty. -/
private lemma isEmpty_top_pairSheaf_punit_pempty :
    IsEmpty ((pairSheaf PUnit PEmpty).1.obj (op Utop)) := by
  refine ⟨fun s ↦ ?_⟩
  have : PEmpty := by
    simpa [pairFamily] using s ⟨1, by simp [Utop]⟩
  exact this.elim

/-- Helper for Example 7.41.3: the top sections of `(PEmpty, PEmpty)` are empty. -/
private lemma isEmpty_top_pairSheaf_pempty_pempty :
    IsEmpty ((pairSheaf PEmpty PEmpty).1.obj (op Utop)) := by
  refine ⟨fun s ↦ ?_⟩
  have : PEmpty := by
    simpa [pairFamily] using s ⟨0, by simp [Utop]⟩
  exact this.elim

/-- Helper for Example 7.41.3: a section over `Utop` determines a morphism from
`(PUnit, PUnit)` by restriction. -/
private def pairSheaf_punit_punit_hom_of_top {G : Sheaf Type X₂}
    (t : G.1.obj (op Utop)) : pairSheaf PUnit PUnit ⟶ G := by
  let sectionOn :
      ∀ U : (Opens X₂)ᵒᵖ, (pairSheaf PUnit PUnit).1.obj U → G.1.obj U :=
    fun U _ ↦ G.1.map (homOfLE (show U.unop ≤ Utop by
      intro x _
      simp [Utop])).op t
  refine ⟨{ app := sectionOn, naturality := ?_ }⟩
  intro U V i
  funext s
  dsimp [sectionOn]
  -- Rewrite the target restriction as the composite `Utop ⟶ U ⟶ V`.
  have hcomp :
      (homOfLE (show V.unop ≤ Utop by
        intro x _
        simp [Utop]) : V.unop ⟶ Utop) =
        i.unop ≫ homOfLE (show U.unop ≤ Utop by
          intro x _
          simp [Utop]) := by
    exact Subsingleton.elim _ _
  have hop :
      (homOfLE (show V.unop ≤ Utop by
        intro x _
        simp [Utop]) : V.unop ⟶ Utop).op =
        (homOfLE (show U.unop ≤ Utop by
          intro x _
          simp [Utop]) : U.unop ⟶ Utop).op ≫ i := by
    have hop0 :
        (homOfLE (show V.unop ≤ Utop by
          intro x _
          simp [Utop]) : V.unop ⟶ Utop).op =
          Quiver.Hom.op (i.unop ≫ homOfLE (show U.unop ≤ Utop by
            intro x _
            simp [Utop]) : V.unop ⟶ Utop) := by
      exact congrArg Quiver.Hom.op hcomp
    exact hop0.trans rfl
  rw [hop]
  simpa using congrFun
    (G.1.map_comp
      (homOfLE (show U.unop ≤ Utop by
        intro x _
        simp [Utop])).op i) t

/-- Helper for Example 7.41.3: `(PEmpty, PEmpty)` is the initial sheaf on the discrete two-point
space. -/
private def pairSheaf_pempty_pempty_isInitial : IsInitial (pairSheaf PEmpty PEmpty) := by
  classical
  refine IsInitial.ofUniqueHom (fun G ↦ ?_) (fun G m ↦ ?_)
  · refine ⟨{ app := fun U s ↦ ?_, naturality := ?_ }⟩
    · -- Sections away from `⊥` are impossible because both fibers are empty.
      by_cases hU : U.unop = ⊥
      · letI : Unique (G.1.obj (op U.unop)) :=
          CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hU)
        exact default
      · have h_nonempty : Set.Nonempty U.unop.1 := by
          by_contra hEmpty
          apply hU
          ext x
          simp only
          constructor
          · intro hx
            exact hEmpty ⟨x, hx⟩
          · intro hx
            cases hx
        let x : U.unop := ⟨h_nonempty.choose, h_nonempty.choose_spec⟩
        have hs : PEmpty := by
          simpa [pairFamily] using s x
        exact hs.elim
    · -- Naturality is automatic on `⊥`, while every nonempty-open source section is impossible.
      intro U V i
      funext s
      by_cases hU : U.unop = ⊥
      · have hV : V.unop = ⊥ := by
          apply le_antisymm
          · simpa [hU] using i.unop.le
          · intro x hx
            cases hx
        letI : Unique (G.1.obj (op U.unop)) :=
          CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hU)
        letI : Unique (G.1.obj (op V.unop)) :=
          CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hV)
        exact Subsingleton.elim _ _
      · have h_nonempty : Set.Nonempty U.unop.1 := by
          by_contra hEmpty
          apply hU
          ext x
          simp only
          constructor
          · intro hx
            exact hEmpty ⟨x, hx⟩
          · intro hx
            cases hx
        let x : U.unop := ⟨h_nonempty.choose, h_nonempty.choose_spec⟩
        have hs : PEmpty := by
          simpa [pairFamily] using s x
        exact hs.elim
  · -- Any two morphisms out of an initial object candidate agree on all four opens.
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    by_cases hU : U.unop = ⊥
    · exact congrFun ((G.isTerminalOfEqEmpty hU).hom_ext _ _) s
    · have h_nonempty : Set.Nonempty U.unop.1 := by
        by_contra hEmpty
        apply hU
        ext x
        simp only
        constructor
        · intro hx
          exact hEmpty ⟨x, hx⟩
        · intro hx
          cases hx
      let x : U.unop := ⟨h_nonempty.choose, h_nonempty.choose_spec⟩
      have hs : PEmpty := by
        simpa [pairFamily] using s x
      exact hs.elim

/-- Helper for Example 7.41.3: the singleton open `U₀` includes into the top open. -/
private lemma u0_le_utop : U₀ ≤ Utop := by
  intro x hx
  simp [Utop]

/-- Helper for Example 7.41.3: the singleton open `U₁` includes into the top open. -/
private lemma u1_le_utop : U₁ ≤ Utop := by
  intro x hx
  simp [Utop]

/-- Helper for Example 7.41.3: the restriction of `falseTop` to `U₀`. -/
private def falseU₀ : (pairSheaf Bool PUnit).1.obj (op U₀) := fun x ↦ by
  rcases x with ⟨x, hx⟩
  simp [U₀] at hx
  subst x
  simpa [pairFamily] using false

/-- Helper for Example 7.41.3: the restriction of `trueTop` to `U₀`. -/
private def trueU₀ : (pairSheaf Bool PUnit).1.obj (op U₀) := fun x ↦ by
  rcases x with ⟨x, hx⟩
  simp [U₀] at hx
  subst x
  simpa [pairFamily] using true

/-- Helper for Example 7.41.3: every section of `(Bool, PUnit)` over `U₀` is one of the two
generator sections coming from the top open. -/
private lemma u0_bool_section_eq_false_or_true
    (s : (pairSheaf Bool PUnit).1.obj (op U₀)) :
    s = falseU₀ ∨ s = trueU₀ := by
  let x₀ : U₀ := ⟨0, by simp [U₀]⟩
  -- Evaluate the section at the unique point of `U₀`; that value determines the whole section.
  by_cases hs : s x₀ = false
  · left
    funext x
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    simpa [falseU₀, falseTop, pairFamily, u0_le_utop] using hs
  · right
    have hs' : s x₀ = true := by
      cases hval : s x₀ <;> simp [hval] at hs ⊢
    funext x
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    simpa [trueU₀, trueTop, pairFamily, u0_le_utop] using hs'

/-- Helper for Example 7.41.3: every cofork equalizes the two distinguished `U₀` sections coming
from `falseTop` and `trueTop`. -/
private lemma cofork_app_u0_false_eq_true (s : Cofork a b) :
    s.π.1.app (op U₀) falseU₀ = s.π.1.app (op U₀) trueU₀ := by
  let u : (pairSheaf PUnit PEmpty).1.obj (op U₀) := fun x ↦ by
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    simpa [pairFamily] using PUnit.unit
  -- Evaluate the cofork condition on the unique section over `U₀`.
  have hEq : a ≫ s.π = b ≫ s.π := s.condition
  have hNat :
      (a ≫ s.π).hom = (b ≫ s.π).hom := by
    exact congrArg (fun k : pairSheaf PUnit PEmpty ⟶ s.pt => k.hom) hEq
  have h :=
    congrFun (congrArg (fun η => η.app (op U₀)) hNat) u
  have ha : a.1.app (op U₀) u = falseU₀ := by
    funext x
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    simp [u, falseU₀, a, pairSheafMap, pairFamilyMap, pairFamily]
  have hb : b.1.app (op U₀) u = trueU₀ := by
    funext x
    rcases x with ⟨x, hx⟩
    simp [U₀] at hx
    subst x
    simp [u, trueU₀, b, pairSheafMap, pairFamilyMap, pairFamily]
  change s.π.1.app (op U₀) (a.1.app (op U₀) u) = s.π.1.app (op U₀) (b.1.app (op U₀) u) at h
  simpa [ha, hb] using h

/-- Helper for Example 7.41.3: the explicit source-side coequalizer witness.
TODO: formalize the universal property by gluing singleton restrictions across the disjoint cover
`U₀ ⊔ U₁ = Utop`. -/
private noncomputable def pair_witness_isColimit :
    IsColimit (Cofork.ofπ q aq_eq_bq) := by
  classical
  refine Cofork.IsColimit.mk' _ (fun s ↦ ?_)
  let G : Sheaf Type X₂ := s.pt
  let cover : Bool → Opens X₂ := fun i ↦ if i then U₁ else U₀
  let iUV : ∀ i : Bool, cover i ⟶ Utop
    | true => homOfLE u1_le_utop
    | false => homOfLE u0_le_utop
  let falseU₁ : (pairSheaf Bool PUnit).1.obj (op U₁) :=
    (pairSheaf Bool PUnit).1.map (homOfLE u1_le_utop).op falseTop
  let sf : ∀ i : Bool, G.1.obj (op (cover i))
    | true => s.π.1.app (op U₁) falseU₁
    | false => s.π.1.app (op U₀) falseU₀
  have hcover : Utop ≤ iSup cover := by
    -- The two singleton opens cover the whole two-point space.
    intro x hx
    fin_cases x <;> simp [cover, U₀, U₁]
  have hcompat : TopCat.Presheaf.IsCompatible G.1 cover sf := by
    intro i j
    cases i <;> cases j
    · have hleft : Opens.infLELeft U₀ U₀ = Opens.infLERight U₀ U₀ := Subsingleton.elim _ _
      simpa [cover, sf] using
        congrArg (fun e ↦ G.1.map e.op (s.π.1.app (op U₀) falseU₀)) hleft
    · have hbot : U₀ ⊓ U₁ = ⊥ := u0_inf_u1_eq_bot
      have hbotCover : cover false ⊓ cover true = ⊥ := by
        simpa [cover] using hbot
      letI : Unique (G.1.obj (op (cover false ⊓ cover true))) :=
        CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hbotCover)
      exact Subsingleton.elim _ _
    · have hbot : U₁ ⊓ U₀ = ⊥ := by
        simpa [inf_comm] using u0_inf_u1_eq_bot
      have hbotCover : cover true ⊓ cover false = ⊥ := by
        simpa [cover] using hbot
      letI : Unique (G.1.obj (op (cover true ⊓ cover false))) :=
        CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hbotCover)
      exact Subsingleton.elim _ _
    · have hright : Opens.infLELeft U₁ U₁ = Opens.infLERight U₁ U₁ := Subsingleton.elim _ _
      simpa [cover, sf] using
        congrArg (fun e ↦ G.1.map e.op (s.π.1.app (op U₁) falseU₁)) hright
  let hglue := G.existsUnique_gluing' (U := cover) (V := Utop) iUV hcover sf hcompat
  let t : G.1.obj (op Utop) := Classical.choose (ExistsUnique.exists hglue)
  have ht : ∀ i : Bool, G.1.map (iUV i).op t = sf i :=
    Classical.choose_spec (ExistsUnique.exists hglue)
  let desc : pairSheaf PUnit PUnit ⟶ G := pairSheaf_punit_punit_hom_of_top t
  refine ⟨desc, ?_, ?_⟩
  · -- Compare the factorization on the two singleton opens, then extend to all opens.
    apply pair_hom_ext_of_singleton_apps
    · funext u
      rcases u0_bool_section_eq_false_or_true u with rfl | rfl
      · simpa [desc, cover, sf, q, falseU₀, pairSheaf_punit_punit_hom_of_top, pairSheafMap,
          pairFamilyMap, pairFamily, u0_le_utop] using ht false
      · calc
          ((q ≫ desc).1.app (op U₀)) trueU₀ =
              desc.1.app (op U₀) (q.1.app (op U₀) trueU₀) := rfl
        _ =
              desc.1.app (op U₀) (q.1.app (op U₀) falseU₀) := rfl
        _ =
              s.π.1.app (op U₀) falseU₀ := by
                simpa [desc, cover, sf, q, trueU₀, pairSheaf_punit_punit_hom_of_top,
                  pairSheafMap, pairFamilyMap, pairFamily, u0_le_utop] using ht false
        _ = s.π.1.app (op U₀) trueU₀ := cofork_app_u0_false_eq_true s
    · funext u
      have hu : u = falseU₁ := by
        funext x
        rcases x with ⟨x, hx⟩
        simp [U₁] at hx
        subst x
        have hpoint : u ⟨1, by simp [U₁]⟩ = PUnit.unit := by
          cases u ⟨1, by simp [U₁]⟩
          rfl
        simpa [falseU₁, pairFamily] using hpoint
      subst hu
      simpa [desc, cover, sf, q, falseU₁, pairSheaf_punit_punit_hom_of_top, pairSheafMap,
        pairFamilyMap, pairFamily, u1_le_utop] using ht true
  · intro m hm
    -- The factorization is uniquely determined by its values on the singleton opens.
    apply pair_hom_ext_of_singleton_apps
    · funext u
      let unitU₀ : (pairSheaf PUnit PUnit).1.obj (op U₀) := q.1.app (op U₀) falseU₀
      have hu : u = unitU₀ := by
        funext x
        rcases x with ⟨x, hx⟩
        simp [U₀] at hx
        subst x
        have hpoint : u ⟨0, by simp [U₀]⟩ = PUnit.unit := by
          cases u ⟨0, by simp [U₀]⟩
          rfl
        simpa [unitU₀, q, falseU₀, pairSheafMap, pairFamilyMap, pairFamily] using hpoint
      subst hu
      have hm0 :=
        congrFun (congrArg (fun k : pairSheaf Bool PUnit ⟶ G => k.1.app (op U₀)) hm) falseU₀
      have hdesc0 : desc.1.app (op U₀) unitU₀ = s.π.1.app (op U₀) falseU₀ := by
        simpa [desc, cover, sf, pairSheaf_punit_punit_hom_of_top, unitU₀, u0_le_utop] using
          ht false
      have hm0' : m.1.app (op U₀) unitU₀ = s.π.1.app (op U₀) falseU₀ := by
        simpa [q, falseU₀, unitU₀, pairSheafMap, pairFamilyMap, pairFamily] using hm0
      exact hm0'.trans hdesc0.symm
    · funext u
      let unitU₁ : (pairSheaf PUnit PUnit).1.obj (op U₁) := q.1.app (op U₁) falseU₁
      have hu : u = unitU₁ := by
        funext x
        rcases x with ⟨x, hx⟩
        simp [U₁] at hx
        subst x
        have hpoint : u ⟨1, by simp [U₁]⟩ = PUnit.unit := by
          cases u ⟨1, by simp [U₁]⟩
          rfl
        simpa [unitU₁, q, falseU₁, pairSheafMap, pairFamilyMap, pairFamily] using hpoint
      subst hu
      have hm1 :=
        congrFun (congrArg (fun k : pairSheaf Bool PUnit ⟶ G => k.1.app (op U₁)) hm) falseU₁
      have hdesc1 : desc.1.app (op U₁) unitU₁ = s.π.1.app (op U₁) falseU₁ := by
        simpa [desc, cover, sf, pairSheaf_punit_punit_hom_of_top, unitU₁, u1_le_utop] using
          ht true
      have hm1' : m.1.app (op U₁) unitU₁ = s.π.1.app (op U₁) falseU₁ := by
        simpa [q, falseU₁, unitU₁, pairSheafMap, pairFamilyMap, pairFamily] using hm1
      exact hm1'.trans hdesc1.symm

/-- Helper for Example 7.41.3: a sheaf on the point space with empty top sections admits a
morphism to every sheaf. -/
private lemma point_empty_nonempty_hom {F G : Sheaf Type Y₁}
    (hF : IsEmpty (F.1.obj (op Vtop))) : Nonempty (F ⟶ G) := by
  classical
  refine ⟨⟨{ app := fun U s ↦ ?_, naturality := ?_ }⟩⟩
  · -- On `⊥` we use the unique section of the target, and on `⊤` there are no source sections.
    by_cases hU : U.unop = ⊥
    · letI : Unique (G.1.obj (op U.unop)) :=
        CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hU)
      exact default
    · have hUtop : U.unop = ⊤ := U.unop.eq_bot_or_top.resolve_left hU
      have hU' : U = op Vtop := by
        cases U
        simpa [Vtop] using congrArg op hUtop
      subst hU'
      have hFU : IsEmpty (F.1.obj (op Vtop)) := hF
      exact (hFU.false s).elim
  · -- Naturality is automatic because every codomain section over `⊥` is unique,
    -- while the `⊤`-source case is impossible.
    intro U V i
    funext s
    rcases U.unop.eq_bot_or_top with hU | hU
    · have hV : V.unop = ⊥ := by
        apply le_antisymm
        · simpa [hU] using i.unop.le
        · intro x hx
          cases hx
      letI : Unique (G.1.obj (op U.unop)) :=
        CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hU)
      letI : Unique (G.1.obj (op V.unop)) :=
        CategoryTheory.Limits.Types.isTerminalEquivUnique _ (G.isTerminalOfEqEmpty hV)
      exact Subsingleton.elim _ _
    · have hFU : IsEmpty (F.1.obj (op U.unop)) := by
        simpa [Vtop, hU] using hF
      exact (hFU.false s).elim

/-- Helper for Example 7.41.3: a sheaf on the point space with empty top sections has at most one
morphism to any other sheaf. -/
private lemma point_empty_subsingleton_hom {F G : Sheaf Type Y₁}
    (hF : IsEmpty (F.1.obj (op Vtop))) : Subsingleton (F ⟶ G) := by
  refine ⟨fun m n ↦ ?_⟩
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rcases U.unop.eq_bot_or_top with hU | hU
  · exact congrFun ((G.isTerminalOfEqEmpty hU).hom_ext _ _) s
  · have hFU : IsEmpty (F.1.obj (op U.unop)) := by
      simpa [Vtop, hU] using hF
    exact (hFU.false s).elim

/-- Helper for Example 7.41.3: the canonical morphism from a point-space sheaf with empty top
sections to any target sheaf. -/
private noncomputable abbrev point_empty_hom {F G : Sheaf Type Y₁}
    (hF : IsEmpty (F.1.obj (op Vtop))) : F ⟶ G :=
  Classical.choice (point_empty_nonempty_hom (F := F) (G := G) hF)

/-- Helper for Example 7.41.3: the canonical morphism out of a point-space sheaf with empty top
sections is unique. -/
private theorem point_empty_hom_unique {F G : Sheaf Type Y₁}
    (hF : IsEmpty (F.1.obj (op Vtop))) (m : F ⟶ G) : m = point_empty_hom (F := F) (G := G) hF :=
  (point_empty_subsingleton_hom (F := F) (G := G) hF).elim _ _

/-- Helper for Example 7.41.3: on the point space, a sheaf with empty top sections is initial. -/
private def sheaf_on_point_isInitial_of_top_empty {F : Sheaf Type Y₁}
    (hF : IsEmpty (F.1.obj (op Vtop))) : IsInitial F :=
  IsInitial.ofUniqueHom (fun G ↦ point_empty_hom (F := F) (G := G) hF)
    (fun G m ↦ point_empty_hom_unique (F := F) (G := G) hF m)

/-- Helper for Example 7.41.3: once the collapse-map pushforward is known to preserve the initial
sheaf, preservation of pushouts would force preservation of coequalizers as well. -/
theorem collapse_pushforward_preserves_coequalizers_of_preserves_pushouts
    [hinit : PreservesColimitsOfShape (Discrete.{0} PEmpty.{1})
      (pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit)))]
    (hpush : PreservesColimitsOfShape WalkingSpan
      (pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit)))) :
    PreservesColimitsOfShape WalkingParallelPair
      (pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := by
  -- Route correction: the generic pushout-to-coequalizer bridge also needs binary coproduct
  -- preservation, so we first obtain that from initial-object preservation plus pushouts.
  let F :
      CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type ⥤
        CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type :=
    pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit))
  change PreservesColimitsOfShape WalkingSpan F at hpush
  change PreservesColimitsOfShape WalkingParallelPair F
  -- Transport the explicit initial-preservation hypothesis to the sheaf-category presentation
  -- where mathlib's finite-colimit comparison lemmas elaborate smoothly.
  letI : PreservesColimitsOfShape (Discrete.{0} PEmpty.{1}) F := by
    simpa [F] using hinit
  letI : HasInitial (CategoryTheory.Sheaf
      (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type) := by
    infer_instance
  letI : HasPushouts (CategoryTheory.Sheaf
      (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type) := by
    infer_instance
  letI := hpush
  -- Pushouts plus initials give binary coproducts, and then the standard comparison lemma gives
  -- coequalizers.
  letI : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts F
  exact preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts F

end Example_7_41_3

-- Proof sketch: identify sheaves on the discrete two-point space with pairs of sets, note that
-- the pushforward along the collapse map `Fin 2 → PUnit` acts as binary product, and use the
-- case `A₂ = ∅` from the Stacks example to see that this product functor does not preserve the
-- relevant coequalizer.
/-- Example 7.41.3 (1): for the collapse map from the discrete two-point space to the one-point
space, the direct-image functor on sheaves of sets does not preserve coequalizers. -/
theorem two_point_to_point_pushforward_not_preserves_coequalizers :
    ¬ PreservesColimitsOfShape WalkingParallelPair
      (pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := by
  intro hpres
  let F :
      CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type ⥤
        CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type :=
    pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit))
  -- Push the explicit source-side coequalizer witness forward.
  letI : PreservesColimitsOfShape WalkingParallelPair F := by
    simpa [F] using hpres
  have hcol :=
    isColimitCoforkMapOfIsColimit (G := F) (h := Example_7_41_3.q)
      (w := Example_7_41_3.aq_eq_bq) Example_7_41_3.pair_witness_isColimit
  -- The pushed source sheaf has no top sections, hence is initial on the point space.
  have hsourceEmpty :
      IsEmpty
        (((F.obj (Example_7_41_3.pairSheaf PUnit PEmpty)).1.obj
          (op Example_7_41_3.Vtop))) := by
    simpa [F, TopCat.Sheaf.pushforward_obj_val, Example_7_41_3.collapseMap_preimage_Vtop] using
      Example_7_41_3.isEmpty_top_pairSheaf_punit_pempty
  have hsourceInit : IsInitial (F.obj (Example_7_41_3.pairSheaf PUnit PEmpty)) :=
    Example_7_41_3.sheaf_on_point_isInitial_of_top_empty hsourceEmpty
  have hab : F.map Example_7_41_3.a = F.map Example_7_41_3.b :=
    hsourceInit.hom_ext _ _
  have hqIso : IsIso (F.map Example_7_41_3.q) :=
    isIso_colimit_cocone_parallelPair_of_eq hab hcol
  letI := hqIso
  -- Evaluate the pushed arrow on the unique nonempty open of the point space.
  have hAppIso :
      IsIso (((F.map Example_7_41_3.q).1.app (op Example_7_41_3.Vtop))) := by
    letI :
        IsIso
          ((sheafToPresheaf
              (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type).map
            (F.map Example_7_41_3.q)) :=
      Functor.map_isIso _ (F.map Example_7_41_3.q)
    simpa using
      (NatTrans.isIso_iff_isIso_app
        ((sheafToPresheaf
            (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type).map
          (F.map Example_7_41_3.q))).1 inferInstance (op Example_7_41_3.Vtop)
  letI := hAppIso
  have hbij :
      Function.Bijective
        (((F.map Example_7_41_3.q).1.app (op Example_7_41_3.Vtop))) := by
    exact (CategoryTheory.isIso_iff_bijective _).1 inferInstance
  have hsame :
      ((F.map Example_7_41_3.q).1.app (op Example_7_41_3.Vtop)) Example_7_41_3.falseTop =
        ((F.map Example_7_41_3.q).1.app (op Example_7_41_3.Vtop)) Example_7_41_3.trueTop := by
    -- On top sections, the pushed map is exactly the collapse map `Bool → PUnit`.
    change Example_7_41_3.q.1.app (op Example_7_41_3.Utop) Example_7_41_3.falseTop =
      Example_7_41_3.q.1.app (op Example_7_41_3.Utop) Example_7_41_3.trueTop
    funext x
    rcases x with ⟨x, hx⟩
    fin_cases x
    · dsimp [Example_7_41_3.q, Example_7_41_3.falseTop, Example_7_41_3.trueTop,
        Example_7_41_3.pairSheafMap, Example_7_41_3.pairFamilyMap, Example_7_41_3.pairFamily]
    · dsimp [Example_7_41_3.q, Example_7_41_3.falseTop, Example_7_41_3.trueTop,
        Example_7_41_3.pairSheafMap, Example_7_41_3.pairFamilyMap, Example_7_41_3.pairFamily]
  exact Example_7_41_3.falseTop_ne_trueTop (hbij.1 hsame)

-- Proof sketch: the same discrete-two-point computation provides a pushout diagram whose image
-- under the pushforward functor fails to remain a pushout, again because the functor acts as
-- binary product on the underlying pair of sets.
/-- Example 7.41.3 (2): for the same collapse map, the direct-image functor on sheaves of sets
does not preserve pushouts. -/
theorem two_point_to_point_pushforward_not_preserves_pushouts :
    ¬ PreservesColimitsOfShape WalkingSpan
      (pushforward Type (discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := by
  intro hpush
  let F :
      CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type ⥤
        CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type :=
    pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit))
  -- The pushed image of `(PEmpty, PEmpty)` is initial on the point space.
  have hinit : PreservesColimitsOfShape (Discrete.{0} PEmpty.{1})
      (pushforward Type (TopCat.discrete.map (fun _ : Fin 2 ↦ PUnit.unit))) := by
    letI : HasInitial (CategoryTheory.Sheaf
        (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type) := by
      infer_instance
    letI : HasInitial (CategoryTheory.Sheaf
        (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type) := by
      infer_instance
    letI : IsInitial (Example_7_41_3.pairSheaf PEmpty PEmpty) :=
      Example_7_41_3.pairSheaf_pempty_pempty_isInitial
    have htargetEmpty :
        IsEmpty (((F.obj (Example_7_41_3.pairSheaf PEmpty PEmpty)).1.obj
          (op Example_7_41_3.Vtop))) := by
      simpa [F, TopCat.Sheaf.pushforward_obj_val, Example_7_41_3.collapseMap_preimage_Vtop] using
        Example_7_41_3.isEmpty_top_pairSheaf_pempty_pempty
    letI : IsInitial (F.obj (Example_7_41_3.pairSheaf PEmpty PEmpty)) :=
      Example_7_41_3.sheaf_on_point_isInitial_of_top_empty htargetEmpty
    let hSourceIso :
        (⊥_ (CategoryTheory.Sheaf
          (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type)) ≅
          Example_7_41_3.pairSheaf PEmpty PEmpty :=
      IsInitial.uniqueUpToIso initialIsInitial Example_7_41_3.pairSheaf_pempty_pempty_isInitial
    let hTargetIso :
        (⊥_ (CategoryTheory.Sheaf
          (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type)) ≅
          F.obj (Example_7_41_3.pairSheaf PEmpty PEmpty) :=
      IsInitial.uniqueUpToIso initialIsInitial
        (Example_7_41_3.sheaf_on_point_isInitial_of_top_empty htargetEmpty)
    have hIso :
        (⊥_ (CategoryTheory.Sheaf
          (Opens.grothendieckTopology ↑(TopCat.discrete.obj PUnit)) Type)) ≅
          F.obj (⊥_ (CategoryTheory.Sheaf
            (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type)) :=
      hTargetIso ≪≫ (F.mapIso hSourceIso).symm
    have : PreservesColimit (Functor.empty.{0}
        (CategoryTheory.Sheaf (Opens.grothendieckTopology ↑(TopCat.discrete.obj (Fin 2))) Type)) F :=
      preservesInitial_of_iso F hIso
    exact preservesColimitsOfShape_pempty_of_preservesInitial F
  letI := hinit
  -- Once initial preservation is available, pushout preservation would force coequalizer
  -- preservation, contradicting the first half of the example.
  exact two_point_to_point_pushforward_not_preserves_coequalizers
    (by
      simpa [F] using
        Example_7_41_3.collapse_pushforward_preserves_coequalizers_of_preserves_pushouts hpush)

end
