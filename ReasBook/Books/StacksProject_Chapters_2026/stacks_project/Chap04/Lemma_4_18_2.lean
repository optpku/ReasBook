module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import stacks_project.Chap04.Lemma_4_18_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v' u' v u

namespace CategoryTheory.Limits

/- Domain-style sampling for Lemma 4.18.2:
- primary domain: connected finite limit shapes in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteLimits`,
  `hasFiniteLimits_of_hasLimitsOfSize`,
  `hasLimit_of_equalizer_and_product`,
  `HasLimitsOfShape`;
- primitive data: the owner class `HasFiniteConnectedLimits`, whose only primitive field is the
  family of `HasLimitsOfShape J C` instances for finite connected shapes;
- derived API: the shape-transfer instance, the size-change theorem, and the source-facing
  equivalence theorem below;
- layer triage:
  - `source-facing`: the constructor theorem from equalizers and pullbacks and the final `iff`;
  - `core/canonical`: `HasFiniteConnectedLimits`;
  - `bridge/view`: the universe-change theorem and the shape-transfer instance. -/

/-- A category has finite connected limits if it has limits of every finite connected small
diagram. -/
class HasFiniteConnectedLimits (C : Type u) [Category.{v} C] : Prop where
  /-- A finite connected shape admits limits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] : HasLimitsOfShape J C

variable (C : Type u) [Category.{v} C]

instance hasLimitsOfShape_of_hasFiniteConnectedLimits
    [HasFiniteConnectedLimits C] (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasLimitsOfShape J C := by
  refine @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  haveI : IsConnected (FinCategory.AsType J) :=
    isConnected_of_equivalent (FinCategory.equivAsType J).symm
  exact HasFiniteConnectedLimits.out (FinCategory.AsType J)

attribute [instance 100] hasLimitsOfShape_of_hasFiniteConnectedLimits

/-- Finite limits are in particular finite connected limits. -/
instance hasFiniteConnectedLimits_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteConnectedLimits C where
  out _ := inferInstance

attribute [instance 100] hasFiniteConnectedLimits_of_hasFiniteLimits

/-- If `C` has limits of a fixed size, then it has finite connected limits. -/
lemma hasFiniteConnectedLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteConnectedLimits C := by
  letI : HasFiniteLimits C := hasFiniteLimits_of_hasLimitsOfSize C
  infer_instance

/-- We can derive finite connected limits by supplying them in one arbitrary universe. -/
theorem hasFiniteConnectedLimits_of_hasFiniteConnectedLimits_of_size
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C) :
    HasFiniteConnectedLimits C where
  out := fun J hJ hJ' hJc ↦ by
    haveI := h (ULiftHom.{w} (ULift.{w} J))
    haveI : IsConnected (ULiftHom (ULift J)) :=
      isConnected_of_equivalent (ULiftHomULiftCategory.equiv J)
    exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv J).symm

/-- Unpack `HasFiniteConnectedLimits` into the corresponding family of limit instances. -/
theorem hasFiniteConnectedLimits_iff :
    HasFiniteConnectedLimits C ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C := by
  constructor
  · intro h J _ _ _
    letI := h
    infer_instance
  · intro h
    exact hasFiniteConnectedLimits_of_hasFiniteConnectedLimits_of_size C h

/-- Helper for Lemma 4.18.2: a finite category has finite arrow generators by taking all of its
arrows. -/
lemma finite_arrow_generators_of_finCategory (J : Type w) [SmallCategory J] [FinCategory J] :
    CategoryTheory.HasFiniteArrowGenerators J := by
  classical
  refine ⟨Set.univ, Set.finite_univ, ?_⟩
  intro X Y f
  refine ⟨0, ComposableArrows.mk₁ f, ?_, ?_⟩
  · rfl
  · intro i
    fin_cases i
    simp

/-- Helper for Lemma 4.18.2: Lemma 4.18.1 supplies an initial functor from the explicit finite
reduction shape attached to a chosen generating arrow set. -/
lemma exists_initial_reduction_functor {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J)) (hS : S.Finite)
    (hsplit :
      ∀ {X Y : J} (f : X ⟶ Y),
        ∃ n : ℕ, ∃ g : ComposableArrows J (n + 1),
          Arrow.mk g.hom = Arrow.mk f ∧
            ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) :
    ∃ (F : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ J), F.Initial := by
  -- Record the finiteness of the concrete reduction shape before extracting the reduction functor.
  letI : FinCategory (_root_.CategoryTheory.ReductionObj (I := J) S) :=
    _root_.CategoryTheory.reductionFinCategory (I := J) S hS
  -- Lemma 4.18.1 already exposes the concrete reduction functor on the explicit reduction shape.
  refine ⟨reductionFunctor (I := J) S, ?_⟩
  exact (reductionFunctor_initial_final (I := J) S hsplit).1

/-- Helper for Lemma 4.18.2: the region cut out by a treated source set consists of the treated
source copies together with the target copies receiving an arrow from one of them. -/
def treated_reduction_region {J : Type w} [SmallCategory J] (S : Set (Arrow J)) (T : Finset J) :
    Set (_root_.CategoryTheory.ReductionObj (I := J) S)
  | .src X => X ∈ T
  | .tgt Y =>
      ∃ X ∈ T,
        Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y))

/-- Helper for Lemma 4.18.2: if no untreated source shares a target with a treated source, then the
associated treated region is closed under every morphism of the reduction category. -/
lemma treated_reduction_region_closed_of_no_boundary
    {J : Type w} [SmallCategory J] (S : Set (Arrow J)) (T : Finset J)
    (hNoBoundary :
      ¬ ∃ (X : J), X ∉ T ∧
          ∃ (X' : J), X' ∈ T ∧
            ∃ (Y : J),
              Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y)) ∧
                Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y))) :
    ∀ {A B : _root_.CategoryTheory.ReductionObj (I := J) S}
      (f : _root_.CategoryTheory.ReductionHom (I := J) S A B),
      treated_reduction_region (J := J) S T A ↔ treated_reduction_region (J := J) S T B := by
  intro A B f
  -- The only nonidentity morphisms are source-to-target arrows, so boundary control is enough.
  cases f with
  | id_src X =>
      simp
  | id_tgt X =>
      simp
  | @gen X Y a =>
      constructor
      · intro hX
        exact ⟨X, hX, ⟨_root_.CategoryTheory.ReductionHom.gen a⟩⟩
      · rintro ⟨X', hX', hv⟩
        by_contra hX
        exact hNoBoundary ⟨X, hX, X', hX', Y, ⟨_root_.CategoryTheory.ReductionHom.gen a⟩, hv⟩
  | diag X =>
      constructor
      · intro hX
        exact ⟨X, hX, ⟨_root_.CategoryTheory.ReductionHom.diag X⟩⟩
      · rintro ⟨X', hX', hv⟩
        by_contra hX
        exact hNoBoundary ⟨X, hX, X', hX', X, ⟨_root_.CategoryTheory.ReductionHom.diag X⟩, hv⟩

/-- Helper for Lemma 4.18.2: in a connected reduction category, every proper nonempty finite set of
source indices has a frontier edge from some untreated source to a target already reached by a
treated source. -/
lemma connected_reduction_next_source
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    [IsConnected (_root_.CategoryTheory.ReductionObj (I := J) S)]
    (T : Finset J) (hT : T.Nonempty) (hTne : T ≠ Finset.univ) :
    ∃ (X : J), X ∉ T ∧
      ∃ (X' : J), X' ∈ T ∧
        ∃ (Y : J),
          Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y)) ∧
            Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y)) := by
  classical
  by_contra hBoundary
  let p : Set (_root_.CategoryTheory.ReductionObj (I := J) S) :=
    treated_reduction_region (J := J) S T
  have hp :
      ∀ {A B : _root_.CategoryTheory.ReductionObj (I := J) S}
        (f : _root_.CategoryTheory.ReductionHom (I := J) S A B), p A ↔ p B :=
    treated_reduction_region_closed_of_no_boundary (J := J) S T hBoundary
  obtain ⟨X₀, hX₀⟩ := hT
  have hp_all : ∀ A : _root_.CategoryTheory.ReductionObj (I := J) S, p A := by
    intro A
    -- Connectedness propagates membership from one treated source through every reduction morphism.
    exact CategoryTheory.induct_on_objects p
      (j₀ := .src X₀)
      (by simpa [p, treated_reduction_region] using hX₀)
      (fun {A B} f => by simpa [p] using hp f) A
  have hUntreated : ∃ X : J, X ∉ T := by
    -- A proper finite subset of the finite source index type omits some source.
    by_contra hUntreated
    apply hTne
    exact Finset.eq_univ_iff_forall.2 fun X => by
      by_contra hX
      exact hUntreated ⟨X, hX⟩
  obtain ⟨X, hX⟩ := hUntreated
  have hPX : p (.src X) := hp_all (.src X)
  exact hX (by simpa [p, treated_reduction_region] using hPX)

/-- Helper for Lemma 4.18.2: a compatibility condition on source legs over a treated finite set of
source vertices. -/
abbrev reduction_source_family_condition
    {J : Type w} [SmallCategory J] (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) (T : Finset J) :=
  ∀ ⦃W : C⦄, (∀ X, X ∈ T → (W ⟶ K.obj (.src X))) → Prop

/-- Helper for Lemma 4.18.2: a representing object for source families on a treated finite set,
subject only to a chosen compatibility condition. -/
structure reduction_source_family_representation
    {J : Type w} [SmallCategory J] (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) (T : Finset J)
    (Compat : reduction_source_family_condition C S K T) where
  /-- The representing object for the compatible source family. -/
  pt : C
  /-- The universal source legs on the treated source copies. -/
  π : ∀ X, X ∈ T → (pt ⟶ K.obj (.src X))
  /-- Any compatible source family factors uniquely through the representing object. -/
  isUniversal :
    ∀ ⦃W : C⦄ (τ : ∀ X, X ∈ T → (W ⟶ K.obj (.src X))), Compat τ →
      ∃! l : W ⟶ pt, ∀ X hX, l ≫ π X hX = τ X hX

/-- Helper for Lemma 4.18.2: the singleton source set is represented by the corresponding source
object itself. -/
def reduction_source_family_representation_singleton
    {J : Type w} [SmallCategory J] (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) (root : J) :
    reduction_source_family_representation C S K ({root} : Finset J)
      (fun {_} _ ↦ True) := by
  refine ⟨K.obj (.src root), ?_, ?_⟩
  · intro X hX
    -- On the singleton treated set, the universal family is the identity leg.
    rcases Finset.mem_singleton.mp hX with rfl
    simpa using (𝟙 (K.obj (.src X)))
  · intro W τ hτ
    -- Any singleton family factors through its only leg.
    refine ⟨τ root (by simp), ?_, ?_⟩
    · intro X hX
      rcases Finset.mem_singleton.mp hX with rfl
      exact Category.comp_id (τ X (by simp))
    · intro m hm
      simpa using hm root (by simp)

/-- Helper for Lemma 4.18.2: adjoining one new source vertex adds exactly one pullback
compatibility equation to the treated family condition. -/
def reduction_source_family_extension_condition
    {J : Type w} [SmallCategory J] [DecidableEq J] (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) (T : Finset J)
    (Compat : reduction_source_family_condition C S K T)
    (X X' Y : J) (hX' : X' ∈ T)
    (u : _root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y))
    (v : _root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y)) :
    reduction_source_family_condition C S K (insert X T) :=
  fun {_} τ ↦
    Compat (fun Z hZ => τ Z (Finset.mem_insert_of_mem hZ)) ∧
      τ X (Finset.mem_insert_self X T) ≫ K.map u =
        τ X' (Finset.mem_insert_of_mem hX') ≫ K.map v

/-- Helper for Lemma 4.18.2: if a treated source family is already represented, adjoining one new
source whose leg is required to meet a fixed treated parent at a common target is represented by
the corresponding pullback. -/
noncomputable def reduction_source_family_extension
    {J : Type w} [SmallCategory J] [DecidableEq J] [HasPullbacks C] (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) (T : Finset J)
    (Compat : reduction_source_family_condition C S K T)
    (R : reduction_source_family_representation C S K T Compat)
    (X X' Y : J) (hX : X ∉ T) (hX' : X' ∈ T)
    (u : _root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y))
    (v : _root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y)) :
    reduction_source_family_representation C S K (insert X T)
      (reduction_source_family_extension_condition C S K T Compat X X' Y hX' u v) := by
  classical
  let σ : ∀ Z, Z ∈ insert X T →
      (pullback (R.π X' hX' ≫ K.map v) (K.map u) ⟶ K.obj (.src Z)) := by
    intro Z hZ
    by_cases hZX : Z = X
    · subst hZX
      exact pullback.snd _ _
    · exact
        pullback.fst _ _ ≫
          R.π Z (Finset.mem_of_mem_insert_of_ne hZ hZX)
  refine ⟨pullback (R.π X' hX' ≫ K.map v) (K.map u), σ, ?_⟩
  intro W τ hτ
  rcases hτ with ⟨hCompat, hEq⟩
  obtain ⟨l, hl, hluniq⟩ :=
    R.isUniversal (fun Z hZ => τ Z (Finset.mem_insert_of_mem hZ)) hCompat
  have hPullback :
      l ≫ R.π X' hX' ≫ K.map v =
        τ X (Finset.mem_insert_self X T) ≫ K.map u := by
    -- The pullback equation is exactly the newly added source-target compatibility.
    calc
      l ≫ R.π X' hX' ≫ K.map v =
          τ X' (Finset.mem_insert_of_mem hX') ≫ K.map v := by
            simpa [Category.assoc] using congrArg (fun k => k ≫ K.map v) (hl X' hX')
      _ = τ X (Finset.mem_insert_self X T) ≫ K.map u := hEq.symm
  refine ⟨pullback.lift l (τ X (Finset.mem_insert_self X T)) hPullback, ?_, ?_⟩
  · intro Z hZ
    by_cases hZX : Z = X
    · cases hZX
      simpa [σ] using pullback.lift_snd l (τ X (Finset.mem_insert_self X T)) hPullback
    · have hZT : Z ∈ T := Finset.mem_of_mem_insert_of_ne hZ hZX
      have hFac :
          pullback.lift l (τ X (Finset.mem_insert_self X T)) hPullback ≫
              pullback.fst (R.π X' hX' ≫ K.map v) (K.map u) ≫
                R.π Z hZT =
            τ Z (Finset.mem_insert_of_mem hZT) := by
        simp [pullback.lift_fst_assoc, hl Z hZT]
      simpa [σ, hZX] using hFac
  · intro m hm
    apply pullback.hom_ext
    · have hmFst : m ≫ pullback.fst (R.π X' hX' ≫ K.map v) (K.map u) = l := by
        apply hluniq
        intro Z hZ
        have hmZ := hm Z (Finset.mem_insert_of_mem hZ)
        have hZX : Z ≠ X := by
          intro hEqZX
          exact hX (hEqZX ▸ hZ)
        simpa [σ, hZX, hZ] using hmZ
      have hLiftFst :
          pullback.lift l (τ X (Finset.mem_insert_self X T)) hPullback ≫
              pullback.fst (R.π X' hX' ≫ K.map v) (K.map u) =
            l := by
        simpa using pullback.lift_fst l (τ X (Finset.mem_insert_self X T)) hPullback
      exact hmFst.trans hLiftFst.symm
    · have hmSnd :
          m ≫ pullback.snd (R.π X' hX' ≫ K.map v) (K.map u) =
            τ X (Finset.mem_insert_self X T) := by
        simpa [σ] using hm X (Finset.mem_insert_self X T)
      have hLiftSnd :
          pullback.lift l (τ X (Finset.mem_insert_self X T)) hPullback ≫
              pullback.snd (R.π X' hX' ≫ K.map v) (K.map u) =
            τ X (Finset.mem_insert_self X T) := by
        simpa using pullback.lift_snd l (τ X (Finset.mem_insert_self X T)) hPullback
      exact hmSnd.trans hLiftSnd.symm

/-- Helper for Lemma 4.18.2: a forward schedule for adjoining source vertices one at a time,
starting from a singleton treated set and ending at the full finite source set. -/
inductive reduction_source_extension_schedule
    {J : Type w} [SmallCategory J] [DecidableEq J] (S : Set (Arrow J)) :
    Finset J → Type (max w v u) where
  | singleton (root : J) :
      reduction_source_extension_schedule S ({root} : Finset J)
  | step {T : Finset J}
      (sched : reduction_source_extension_schedule S T)
      (X X' Y : J) (hX : X ∉ T) (hX' : X' ∈ T)
      (u : _root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y))
      (v : _root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y)) :
      reduction_source_extension_schedule S (insert X T)

/-- Helper for Lemma 4.18.2: every source-extension schedule keeps the treated source set
nonempty. -/
lemma reduction_source_extension_schedule.nonempty
    {J : Type w} [SmallCategory J] [DecidableEq J] {S : Set (Arrow J)} :
    ∀ {T : Finset J},
      reduction_source_extension_schedule (J := J) S T → T.Nonempty
  | _, .singleton root => ⟨root, by simp⟩
  | _, .step _ X _ _ _ _ _ _ => by
      simp

/-- Helper for Lemma 4.18.2: complete any partial source-extension schedule by repeatedly adding a
frontier source provided by connectedness of the reduction category. -/
noncomputable def complete_reduction_source_extension_schedule
    {J : Type w} [SmallCategory J] [FinCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    [IsConnected (_root_.CategoryTheory.ReductionObj (I := J) S)]
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T) :
    reduction_source_extension_schedule (J := J) S Finset.univ := by
  classical
  -- Route correction: recurse on the untreated complement, so each frontier extension strictly
  -- decreases the remaining cardinality.
  refine
    (show
      ∀ n : ℕ, ∀ {T : Finset J},
        reduction_source_extension_schedule (J := J) S T →
          ((Finset.univ : Finset J) \ T).card = n →
            reduction_source_extension_schedule (J := J) S Finset.univ from ?_)
      ((Finset.univ : Finset J) \ T).card sched rfl
  intro n
  induction n with
  | zero =>
      intro T sched hCard
      -- If no untreated source remains, the treated set is already all of `Finset.univ`.
      have hEmpty : ((Finset.univ : Finset J) \ T) = ∅ := Finset.card_eq_zero.mp hCard
      have hT : T = (Finset.univ : Finset J) := by
        apply Finset.eq_univ_iff_forall.2
        intro X
        by_contra hX
        have hXT : X ∈ ((Finset.univ : Finset J) \ T) := by
          simp [hX]
        have : X ∈ (∅ : Finset J) := by
          simpa [hEmpty] using hXT
        simpa using this
      simpa [hT] using sched
  | succ n ih =>
      intro T sched hCard
      -- Choose a frontier source sharing a target with the treated region, then extend once.
      have hTne : T ≠ (Finset.univ : Finset J) := by
        intro hT
        simpa [hT] using hCard
      have hFrontier :=
        connected_reduction_next_source (J := J) S T sched.nonempty hTne
      let X : J := Classical.choose hFrontier
      have hX : X ∉ T := (Classical.choose_spec hFrontier).1
      let hFrontier' := (Classical.choose_spec hFrontier).2
      let X' : J := Classical.choose hFrontier'
      have hX' : X' ∈ T := (Classical.choose_spec hFrontier').1
      let hFrontier'' := (Classical.choose_spec hFrontier').2
      let Y : J := Classical.choose hFrontier''
      have hu :
          Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y)) :=
        (Classical.choose_spec hFrontier'').1
      have hv :
          Nonempty (_root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y)) :=
        (Classical.choose_spec hFrontier'').2
      let u : _root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y) :=
        Classical.choice hu
      let v : _root_.CategoryTheory.ReductionHom (I := J) S (.src X') (.tgt Y) :=
        Classical.choice hv
      have hXmem : X ∈ ((Finset.univ : Finset J) \ T) := by
        simp [hX]
      have hErase :
          ((Finset.univ : Finset J) \ insert X T) =
            (((Finset.univ : Finset J) \ T).erase X) := by
        ext Z
        by_cases hZX : Z = X
        · subst hZX
          simp [hX]
        · simp [Finset.mem_sdiff, hZX, and_left_comm, and_assoc]
      have hCard' : ((Finset.univ : Finset J) \ insert X T).card = n := by
        rw [hErase, Finset.card_erase_of_mem hXmem]
        omega
      exact ih
        (.step sched X X' Y hX hX' u v)
        hCard'

/-- Helper for Lemma 4.18.2: choose a full source-extension schedule from a singleton source to
all source vertices of the connected finite reduction category. -/
lemma exists_reduction_source_extension_schedule
    {J : Type w} [SmallCategory J] [FinCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    [IsConnected (_root_.CategoryTheory.ReductionObj (I := J) S)] :
    ∃ sched : reduction_source_extension_schedule (J := J) S Finset.univ, True := by
  classical
  -- Pick any object of the connected reduction category and use its underlying source index.
  obtain ⟨A⟩ : Nonempty (_root_.CategoryTheory.ReductionObj (I := J) S) := inferInstance
  cases A with
  | src root =>
      exact ⟨complete_reduction_source_extension_schedule (J := J) S (.singleton root), trivial⟩
  | tgt root =>
      exact ⟨complete_reduction_source_extension_schedule (J := J) S (.singleton root), trivial⟩

/-- Helper for Lemma 4.18.2: the recursive compatibility condition attached to a chosen
source-extension schedule. -/
def reduction_source_schedule_condition
    {J : Type w} [SmallCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T) :
    reduction_source_family_condition C S K T :=
  match sched with
  | .singleton _ => fun {_} _ ↦ True
  | .step (T := T) sched X X' Y _ hX' u v =>
      reduction_source_family_extension_condition C S K T
        (reduction_source_schedule_condition S K sched) X X' Y hX' u v

/-- Helper for Lemma 4.18.2: the schedule condition is extensional in the chosen family of source
legs. -/
lemma reduction_source_schedule_condition_congr
    {J : Type w} [SmallCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T)
    {W : C}
    {τ τ' : ∀ X, X ∈ T → (W ⟶ K.obj (.src X))}
    (hEq : ∀ X hX, τ X hX = τ' X hX) :
    reduction_source_schedule_condition C S K sched τ →
      reduction_source_schedule_condition C S K sched τ' := by
  induction sched with
  | singleton root =>
      intro _
      trivial
  | @step T sched X X' Y hX hX' u v ih =>
      intro hτ
      rcases hτ with ⟨hOld, hNew⟩
      refine ⟨?_, ?_⟩
      · -- Restrict to the previously treated sources and apply the induction hypothesis there.
        refine ih (fun Z hZ => hEq Z (Finset.mem_insert_of_mem hZ)) hOld
      · -- The new pullback relation is pointwise extensional in the two compared source legs.
        simpa [hEq X (Finset.mem_insert_self X T), hEq X' (Finset.mem_insert_of_mem hX')] using hNew

/-- Helper for Lemma 4.18.2: the schedule condition is preserved when every source leg is
precomposed with a fixed morphism. -/
lemma reduction_source_schedule_condition_comp
    {J : Type w} [SmallCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T)
    {W W' : C}
    {τ : ∀ X, X ∈ T → (W ⟶ K.obj (.src X))}
    (hτ : reduction_source_schedule_condition C S K sched τ)
    (l : W' ⟶ W) :
    reduction_source_schedule_condition C S K sched (fun X hX => l ≫ τ X hX) := by
  induction sched with
  | singleton root =>
      trivial
  | @step T sched X X' Y hX hX' u v ih =>
      rcases hτ with ⟨hOld, hNew⟩
      refine ⟨?_, ?_⟩
      · -- Precomposition preserves the old compatibility data by the recursive hypothesis.
        exact ih hOld
      · -- The newly added relation is preserved after whiskering on the left.
        simpa [Category.assoc] using congrArg (fun k => l ≫ k) hNew

/-- Helper for Lemma 4.18.2: folding the pullback extension lemma along a source-extension
schedule produces a representing object for the source legs on the treated source set. -/
noncomputable def reduction_source_representation_of_schedule
    {J : Type w} [SmallCategory J] [DecidableEq J] [HasPullbacks C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T) :
    reduction_source_family_representation C S K T
      (reduction_source_schedule_condition C S K sched) := by
  induction sched with
  | singleton root =>
      -- The singleton schedule is represented by the corresponding source object itself.
      exact reduction_source_family_representation_singleton C S K root
  | @step T sched X X' Y hX hX' u v ih =>
      -- Extend the previous universal source family by one pullback step.
      exact reduction_source_family_extension C S K T
        (reduction_source_schedule_condition C S K sched) ih X X' Y hX hX' u v

/-- Helper for Lemma 4.18.2: the universal family produced by the source-schedule representation
satisfies every tree relation encoded by the schedule. -/
lemma reduction_source_representation_of_schedule_compatible
    {J : Type w} [SmallCategory J] [FinCategory J] [DecidableEq J] [HasPullbacks C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T) :
    reduction_source_schedule_condition C S K sched
      (fun X hX => (reduction_source_representation_of_schedule C S K sched).π X hX) := by
  induction sched with
  | singleton root =>
      trivial
  | @step T sched X X' Y hX hX' u v ih =>
      refine ⟨?_, ?_⟩
      · -- On the old treated set, the new universal family is the old one precomposed with the
        -- pullback projection.
        let τold :
            ∀ Z, Z ∈ T →
              ((reduction_source_representation_of_schedule C S K
                    (.step sched X X' Y hX hX' u v)).pt ⟶
                  K.obj (.src Z)) :=
          fun Z hZ =>
            (reduction_source_representation_of_schedule C S K
              (.step sched X X' Y hX hX' u v)).π Z (Finset.mem_insert_of_mem hZ)
        let τold' :
            ∀ Z, Z ∈ T →
              ((reduction_source_representation_of_schedule C S K
                    (.step sched X X' Y hX hX' u v)).pt ⟶
                  K.obj (.src Z)) :=
          fun Z hZ =>
            pullback.fst
                (((reduction_source_representation_of_schedule C S K sched).π X' hX') ≫ K.map v)
                (K.map u) ≫
              (reduction_source_representation_of_schedule C S K sched).π Z hZ
        have hEqOld : ∀ Z hZ, τold Z hZ = τold' Z hZ := by
          intro Z hZ
          have hZX : Z ≠ X := by
            intro hZX
            exact hX (hZX ▸ hZ)
          simp [τold, τold', reduction_source_representation_of_schedule,
            reduction_source_family_extension, hZX]
        exact reduction_source_schedule_condition_congr C S K sched
          (τ := τold') (τ' := τold) (fun Z hZ => (hEqOld Z hZ).symm)
          (reduction_source_schedule_condition_comp C S K sched ih
            (pullback.fst
              (((reduction_source_representation_of_schedule C S K sched).π X' hX') ≫ K.map v)
              (K.map u)))
      · -- The pullback condition is exactly the new source-target compatibility relation.
        have hXX' : X' ≠ X := by
          intro hEqXX'
          exact hX (hEqXX' ▸ hX')
        simpa [reduction_source_representation_of_schedule, reduction_source_family_extension,
          hXX', Category.assoc] using (pullback.condition (f :=
            ((reduction_source_representation_of_schedule C S K sched).π X' hX') ≫ K.map v)
            (g := K.map u)).symm

/-- Helper for Lemma 4.18.2: any cone on the reduction diagram satisfies the recursively encoded
source schedule relations on its source legs. -/
lemma cone_source_family_compatible_of_schedule
    {J : Type w} [SmallCategory J] [DecidableEq J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {T : Finset J}
    (sched : reduction_source_extension_schedule (J := J) S T)
    (s : Cone K) :
    reduction_source_schedule_condition C S K sched
      (fun X _ => s.π.app (.src X)) := by
  induction sched generalizing s with
  | singleton root =>
      trivial
  | @step T sched X X' Y hX hX' u v ih =>
      refine ⟨ih s, ?_⟩
      -- The two source legs agree after mapping to the common target because `s` is a cone.
      have hu : s.π.app (.src X) ≫ K.map u = s.π.app (.tgt Y) := by
        simpa using s.w u
      have hv : s.π.app (.src X') ≫ K.map v = s.π.app (.tgt Y) := by
        simpa using s.w v
      exact hu.trans hv.symm

/-- Helper for Lemma 4.18.2: the finite family of all source-to-target morphisms in the reduction
category. -/
abbrev reduction_target_relation_index
    {J : Type w} [SmallCategory J] [FinCategory J] (S : Set (Arrow J)) :=
  Σ Y : J, Σ X : J,
    _root_.CategoryTheory.ReductionHom (I := J) S (.src X) (.tgt Y)

/-- Helper for Lemma 4.18.2: a source family satisfies a target relation when the leg into the
source copy `X` followed by `u` agrees with the target leg determined from the source copy `Y`. -/
def reduction_target_relation
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {W : C}
    (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
    (r : reduction_target_relation_index (J := J) S) : Prop :=
  τ r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2 =
    τ r.1 (Finset.mem_univ _) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1)

/-- Helper for Lemma 4.18.2: adjoining a finite family of target relations means keeping the old
compatibility condition and imposing those relations for every indexed source-to-target arrow. -/
def reduction_target_relations_condition
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (U : Finset (reduction_target_relation_index (J := J) S)) :
    reduction_source_family_condition C S K Finset.univ :=
  fun {_} τ ↦ Compat τ ∧ ∀ r ∈ U, reduction_target_relation C S K τ r

/-- Helper for Lemma 4.18.2: we may always strengthen the represented family condition by an
implication without changing the representing object or its universal family. -/
def reduction_source_family_representation_of_imp
    {J : Type w} [SmallCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (T : Finset J)
    {Compat Compat' : reduction_source_family_condition C S K T}
    (R : reduction_source_family_representation C S K T Compat)
    (hImp : ∀ ⦃W : C⦄ (τ : ∀ X, X ∈ T → (W ⟶ K.obj (.src X))), Compat' τ → Compat τ) :
    reduction_source_family_representation C S K T Compat' := by
  refine ⟨R.pt, R.π, ?_⟩
  intro W τ hτ
  exact R.isUniversal τ (hImp τ hτ)

/-- Helper for Lemma 4.18.2: one additional source-to-target relation is imposed by taking the
equalizer of the two corresponding maps out of the current representing object. -/
noncomputable def reduction_source_family_equalizer_extension
    {J : Type w} [SmallCategory J] [FinCategory J] [HasEqualizers C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (R : reduction_source_family_representation C S K Finset.univ Compat)
    (r : reduction_target_relation_index (J := J) S) :
    reduction_source_family_representation C S K Finset.univ
      (fun {_} τ ↦ Compat τ ∧ reduction_target_relation C S K τ r) := by
  refine ⟨equalizer (R.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2)
      (R.π r.1 (Finset.mem_univ _) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1)),
    (fun X _ => equalizer.ι _ _ ≫ R.π X (Finset.mem_univ _)), ?_⟩
  intro W τ hτ
  rcases hτ with ⟨hCompat, hRel⟩
  obtain ⟨l, hl, hluniq⟩ := R.isUniversal τ hCompat
  have hEq :
      l ≫ R.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2 =
        l ≫ R.π r.1 (Finset.mem_univ _) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1) := by
    calc
      l ≫ R.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2 =
          τ r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2 := by
            simpa [Category.assoc] using congrArg (fun k => k ≫ K.map r.2.2) (hl r.2.1 _)
      _ = τ r.1 (Finset.mem_univ _) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1) := hRel
      _ = l ≫ R.π r.1 (Finset.mem_univ _) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1) := by
            simpa [Category.assoc] using
              congrArg (fun k => k ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1))
                (hl r.1 _).symm
  refine ⟨equalizer.lift l hEq, ?_, ?_⟩
  · intro X hX
    calc
      equalizer.lift l hEq ≫ equalizer.ι _ _ ≫ R.π X hX = l ≫ R.π X hX := by
        simpa [Category.assoc] using
          congrArg (fun k => k ≫ R.π X hX) (equalizer.lift_ι l hEq)
      _ = τ X hX := hl X hX
  · intro m hm
    apply equalizer.hom_ext
    have hmBase : m ≫ equalizer.ι _ _ = l := by
      apply hluniq
      intro X hX
      simpa [Category.assoc] using hm X hX
    calc
      m ≫ equalizer.ι _ _ = l := hmBase
      _ = equalizer.lift l hEq ≫ equalizer.ι _ _ := by
        simpa using (equalizer.lift_ι l hEq).symm

/-- Helper for Lemma 4.18.2: the explicit target-relation condition is preserved when every source
leg is precomposed with a fixed morphism, provided the base compatibility condition has the same
stability. -/
lemma reduction_target_relations_condition_comp
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    {Compat : reduction_source_family_condition C S K Finset.univ}
    {U : Finset (reduction_target_relation_index (J := J) S)}
    (hCompatComp :
      ∀ ⦃W W' : C⦄
        (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
        (l : W' ⟶ W),
        Compat τ → Compat (fun X hX => l ≫ τ X hX))
    {W W' : C}
    {τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X))}
    (hτ : reduction_target_relations_condition C S K Compat U τ)
    (l : W' ⟶ W) :
    reduction_target_relations_condition C S K Compat U
      (fun X hX => l ≫ τ X hX) := by
  rcases hτ with ⟨hCompat, hRelations⟩
  refine ⟨hCompatComp τ l hCompat, ?_⟩
  intro r hr
  -- Each explicit target relation is stable under left whiskering by associativity.
  simpa [reduction_target_relation, Category.assoc] using
    congrArg (fun k => l ≫ k) (hRelations r hr)

/-- Helper for Lemma 4.18.2: the sigma type indexing all source-to-target relations is finite once
the finite reduction category attached to `S` is fixed. -/
@[reducible] noncomputable def reduction_target_relation_index_fintype
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J)) (hS : S.Finite) :
    Fintype (reduction_target_relation_index (J := J) S) := by
  -- Reuse the finite reduction shape from Lemma 4.18.1 so the sigma index is genuinely finite.
  letI : FinCategory (_root_.CategoryTheory.ReductionObj (I := J) S) :=
    _root_.CategoryTheory.reductionFinCategory (I := J) S hS
  letI : Fintype J := CategoryTheory.FinCategory.fintypeObj (J := J)
  change Fintype
    (Σ Y : J, Σ X : J,
      (_root_.CategoryTheory.ReductionObj.src (S := S) X ⟶
        _root_.CategoryTheory.ReductionObj.tgt (S := S) Y))
  infer_instance

/-- Helper for Lemma 4.18.2: imposing no target relations leaves the original source-family
compatibility condition unchanged. -/
lemma reduction_target_relations_empty_imp
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (Compat : reduction_source_family_condition C S K Finset.univ)
    {W : C}
    (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X))) :
    reduction_target_relations_condition C S K Compat ∅ τ → Compat τ := by
  -- With no indexed target relations, only the base source-family compatibility remains.
  intro hτ
  exact hτ.1

/-- Helper for Lemma 4.18.2: adding one indexed target relation amounts to keeping the old family
compatibility and appending the new equalizer equation. -/
lemma reduction_target_relations_insert_imp
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    [DecidableEq (reduction_target_relation_index (J := J) S)]
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (U : Finset (reduction_target_relation_index (J := J) S))
    (r : reduction_target_relation_index (J := J) S)
    {W : C}
    (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X))) :
    (reduction_target_relations_condition C S K Compat U τ ∧
        reduction_target_relation C S K τ r) →
      reduction_target_relations_condition C S K Compat (insert r U) τ := by
  intro hτ
  rcases hτ with ⟨hOld, hr⟩
  rcases hOld with ⟨hCompat, hRelations⟩
  refine ⟨hCompat, ?_⟩
  intro r' hr'
  rcases Finset.mem_insert.mp hr' with rfl | hr'U
  · exact hr
  · exact hRelations r' hr'U

/-- Helper for Lemma 4.18.2: the relation condition indexed by `insert r U` restricts to the old
family condition on `U` together with the distinguished new relation `r`. -/
lemma reduction_target_relations_insert_proj
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    [DecidableEq (reduction_target_relation_index (J := J) S)]
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (U : Finset (reduction_target_relation_index (J := J) S))
    (r : reduction_target_relation_index (J := J) S)
    {W : C}
    (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X))) :
    reduction_target_relations_condition C S K Compat (insert r U) τ →
      (reduction_target_relations_condition C S K Compat U τ ∧
        reduction_target_relation C S K τ r) := by
  intro hτ
  rcases hτ with ⟨hCompat, hRelations⟩
  refine ⟨⟨hCompat, ?_⟩, hRelations r (by simp)⟩
  intro r' hr'
  exact hRelations r' (by simp [hr'])

/-- Helper for Lemma 4.18.2: recursively package the iterated equalizer construction together with
the proof that its universal source family satisfies all imposed target relations. -/
noncomputable def reduction_target_relations_representation_package
    {J : Type w} [SmallCategory J] [FinCategory J] [HasEqualizers C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (U : Finset (reduction_target_relation_index (J := J) S))
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (R : reduction_source_family_representation C S K Finset.univ Compat)
    (hCompatComp :
      ∀ ⦃W W' : C⦄
        (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
        (l : W' ⟶ W),
        Compat τ → Compat (fun X hX => l ≫ τ X hX))
    (hCompat : Compat (fun X hX => R.π X hX)) :
    Σ' R' : reduction_source_family_representation C S K Finset.univ
        (reduction_target_relations_condition C S K Compat U),
      reduction_target_relations_condition C S K Compat U
        (fun X hX => R'.π X hX) := by
  classical
  refine
    (show
      ∀ n : ℕ,
        ∀ U : Finset (reduction_target_relation_index (J := J) S),
          U.card = n →
            Σ' R' : reduction_source_family_representation C S K Finset.univ
                (reduction_target_relations_condition C S K Compat U),
              reduction_target_relations_condition C S K Compat U
                (fun X hX => R'.π X hX) from ?_)
      U.card U rfl
  intro n
  induction n with
  | zero =>
      intro U hU
      have hEmpty : U = ∅ := Finset.card_eq_zero.mp hU
      subst hEmpty
      let Rempty :
          reduction_source_family_representation C S K Finset.univ
            (reduction_target_relations_condition C S K Compat ∅) :=
        reduction_source_family_representation_of_imp C S K Finset.univ R
          (fun {W} τ hτ => reduction_target_relations_empty_imp C S K Compat (W := W) τ hτ)
      refine ⟨Rempty, ?_⟩
      -- In the empty case only the original source-family compatibility remains.
      refine ⟨?_, ?_⟩
      · simpa [Rempty] using hCompat
      · simp
  | succ n ih =>
      intro U hU
      have hCardPos : 0 < U.card := by
        omega
      have hUNonempty : U.Nonempty := Finset.card_pos.mp hCardPos
      let r : reduction_target_relation_index (J := J) S := Classical.choose hUNonempty
      have hrU : r ∈ U := Classical.choose_spec hUNonempty
      have hCardErase : (U.erase r).card = n := by
        rw [Finset.card_erase_of_mem hrU, hU]
        omega
      let prev :=
        ih (U.erase r) hCardErase
      let Rprev := prev.1
      have hPrev :
          reduction_target_relations_condition C S K Compat (U.erase r)
            (fun X hX => Rprev.π X hX) := prev.2
      have hPrevComp :
          reduction_target_relations_condition C S K Compat (U.erase r)
            (fun X hX =>
              equalizer.ι
                  (Rprev.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2)
                  (Rprev.π r.1 (Finset.mem_univ _) ≫
                    K.map (_root_.CategoryTheory.ReductionHom.diag r.1)) ≫
                Rprev.π X hX) := by
        -- Existing relations survive after precomposing with the equalizer inclusion.
        exact reduction_target_relations_condition_comp C S K hCompatComp hPrev
          (equalizer.ι
            (Rprev.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2)
            (Rprev.π r.1 (Finset.mem_univ _) ≫
              K.map (_root_.CategoryTheory.ReductionHom.diag r.1)))
      have hNew :
          reduction_target_relation C S K
            (fun X hX =>
              equalizer.ι
                  (Rprev.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2)
                  (Rprev.π r.1 (Finset.mem_univ _) ≫
                    K.map (_root_.CategoryTheory.ReductionHom.diag r.1)) ≫
                Rprev.π X hX)
            r := by
        -- The newly imposed relation is the defining equalizer condition.
        simpa [reduction_target_relation, Category.assoc] using
          (equalizer.condition
            (f := Rprev.π r.2.1 (Finset.mem_univ _) ≫ K.map r.2.2)
            (g := Rprev.π r.1 (Finset.mem_univ _) ≫
              K.map (_root_.CategoryTheory.ReductionHom.diag r.1)))
      let Rstep :
          reduction_source_family_representation C S K Finset.univ
            (reduction_target_relations_condition C S K Compat (insert r (U.erase r))) :=
        reduction_source_family_representation_of_imp C S K Finset.univ
          (reduction_source_family_equalizer_extension C S K
            (Compat := reduction_target_relations_condition C S K Compat (U.erase r))
            Rprev r)
          (fun {W} τ hτ =>
            reduction_target_relations_insert_proj C S K Compat (U.erase r) r (W := W) τ hτ)
      have hStep :
          reduction_target_relations_condition C S K Compat (insert r (U.erase r))
            (fun X hX => Rstep.π X hX) := by
        exact reduction_target_relations_insert_imp C S K Compat (U.erase r) r _
          ⟨hPrevComp, hNew⟩
      have hInsert : U = insert r (U.erase r) := (Finset.insert_erase hrU).symm
      exact hInsert ▸ ⟨Rstep, hStep⟩

/-- Helper for Lemma 4.18.2: iterating the equalizer extension over a finite family of
source-to-target arrows imposes all of those relations simultaneously. -/
noncomputable def reduction_target_relations_representation
    {J : Type w} [SmallCategory J] [FinCategory J] [HasEqualizers C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (U : Finset (reduction_target_relation_index (J := J) S))
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (R : reduction_source_family_representation C S K Finset.univ Compat)
    (hCompatComp :
      ∀ ⦃W W' : C⦄
        (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
        (l : W' ⟶ W),
        Compat τ → Compat (fun X hX => l ≫ τ X hX))
    (hCompat : Compat (fun X hX => R.π X hX)) :
    reduction_source_family_representation C S K Finset.univ
      (reduction_target_relations_condition C S K Compat U) :=
  (reduction_target_relations_representation_package C S K U Compat R hCompatComp hCompat).1

/-- Helper for Lemma 4.18.2: the universal family of the iterated equalizer construction satisfies
all target relations in the chosen finite family. -/
lemma reduction_target_relations_representation_compatible
    {J : Type w} [SmallCategory J] [FinCategory J] [HasEqualizers C]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (U : Finset (reduction_target_relation_index (J := J) S))
    (Compat : reduction_source_family_condition C S K Finset.univ)
    (R : reduction_source_family_representation C S K Finset.univ Compat)
    (hCompatComp :
      ∀ ⦃W W' : C⦄
        (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
        (l : W' ⟶ W),
        Compat τ → Compat (fun X hX => l ≫ τ X hX))
    (hCompat : Compat (fun X hX => R.π X hX)) :
    reduction_target_relations_condition C S K Compat U
      (fun X hX =>
        (reduction_target_relations_representation C S K U Compat R hCompatComp hCompat).π X hX) := by
  exact (reduction_target_relations_representation_package C S K U Compat R hCompatComp hCompat).2

/-- Helper for Lemma 4.18.2: every cone on the reduction diagram satisfies every explicit
source-to-target relation. -/
lemma cone_source_family_satisfies_reduction_target_relation
    {J : Type w} [SmallCategory J] [FinCategory J]
    (S : Set (Arrow J))
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C)
    (s : Cone K)
    (r : reduction_target_relation_index (J := J) S) :
    reduction_target_relation C S K (fun X _ => s.π.app (.src X)) r := by
  -- Both sides are the source and target cone equations for the chosen reduction arrow.
  have hu : s.π.app (.src r.2.1) ≫ K.map r.2.2 = s.π.app (.tgt r.1) := by
    simpa using s.w r.2.2
  have hd :
      s.π.app (.src r.1) ≫ K.map (_root_.CategoryTheory.ReductionHom.diag r.1) =
        s.π.app (.tgt r.1) := by
    simpa using s.w (_root_.CategoryTheory.ReductionHom.diag r.1)
  exact hu.trans hd.symm

/-- Helper for Lemma 4.18.2: after Lemma 4.18.1 replaces a finite connected category by the
explicit finite bipartite reduction shape, the remaining source-proof step is to construct limits
on that reduction shape using pullbacks and equalizers. -/
lemma hasLimit_of_connected_reduction_diagram
    {J : Type w} [SmallCategory J] [FinCategory J] [HasEqualizers C] [HasPullbacks C]
    (S : Set (Arrow J)) (hS : S.Finite)
    [IsConnected (_root_.CategoryTheory.ReductionObj (I := J) S)]
    (K : _root_.CategoryTheory.ReductionObj (I := J) S ⥤ C) :
    HasLimit K := by
  classical
  letI : Fintype (reduction_target_relation_index (J := J) S) :=
    reduction_target_relation_index_fintype (J := J) S hS
  letI : DecidableEq (reduction_target_relation_index (J := J) S) := Classical.decEq _
  obtain ⟨sched, -⟩ :
      ∃ sched : reduction_source_extension_schedule.{w, u, v} (J := J) (S := S)
          (Finset.univ : Finset J),
        True :=
    exists_reduction_source_extension_schedule (J := J) S
  let CompatSched : reduction_source_family_condition C S K Finset.univ :=
    reduction_source_schedule_condition (C := C) (J := J) S K sched
  let Rsrc : reduction_source_family_representation C S K Finset.univ CompatSched :=
    reduction_source_representation_of_schedule C S K sched
  have hRsrc : CompatSched (fun X hX => Rsrc.π X hX) := by
    -- The pullback fold already enforces the schedule relations.
    exact reduction_source_representation_of_schedule_compatible C S K sched
  let hSchedComp :
      ∀ ⦃W W' : C⦄
        (τ : ∀ X, X ∈ (Finset.univ : Finset J) → (W ⟶ K.obj (.src X)))
        (l : W' ⟶ W),
        CompatSched τ →
          CompatSched (fun X hX => l ≫ τ X hX) :=
    fun {W} {W'} τ l hτ =>
      reduction_source_schedule_condition_comp (C := C) (J := J) (S := S) (K := K)
        (sched := sched) (τ := τ) hτ l
  let Rrel :
      reduction_source_family_representation C S K Finset.univ
        (reduction_target_relations_condition C S K CompatSched
          (Finset.univ : Finset (reduction_target_relation_index (J := J) S))) :=
    reduction_target_relations_representation C S K (Finset.univ : Finset
      (reduction_target_relation_index (J := J) S)) CompatSched Rsrc hSchedComp hRsrc
  have hRrel :
      reduction_target_relations_condition C S K CompatSched
        (Finset.univ : Finset (reduction_target_relation_index (J := J) S))
        (fun X hX => Rrel.π X hX) := by
    -- The equalizer fold preserves the old schedule compatibility and adds all target relations.
    exact reduction_target_relations_representation_compatible C S K
      (Finset.univ : Finset (reduction_target_relation_index (J := J) S)) CompatSched
      Rsrc hSchedComp hRsrc
  let πapp : ∀ A : _root_.CategoryTheory.ReductionObj (I := J) S, Rrel.pt ⟶ K.obj A :=
    fun A =>
      match A with
      | _root_.CategoryTheory.ReductionObj.src X => Rrel.π X (Finset.mem_univ _)
      | _root_.CategoryTheory.ReductionObj.tgt Y =>
          Rrel.π Y (Finset.mem_univ _) ≫
            K.map (_root_.CategoryTheory.ReductionHom.diag Y)
  have hπnat : ∀ {A B} (f : _root_.CategoryTheory.ReductionHom (I := J) S A B),
      πapp A ≫ K.map f = πapp B := by
    intro A B f
    cases f with
    | id_src X =>
        change Rrel.π X (Finset.mem_univ X) ≫
            K.map (𝟙 (_root_.CategoryTheory.ReductionObj.src (S := S) X)) =
          Rrel.π X (Finset.mem_univ X)
        rw [Functor.map_id, Category.comp_id]
    | id_tgt Y =>
        change πapp (_root_.CategoryTheory.ReductionObj.tgt (S := S) Y) ≫
            K.map (𝟙 (_root_.CategoryTheory.ReductionObj.tgt (S := S) Y)) =
          πapp (_root_.CategoryTheory.ReductionObj.tgt (S := S) Y)
        rw [Functor.map_id, Category.comp_id]
    | gen a =>
        simpa [πapp, reduction_target_relation, Category.assoc] using
          hRrel.2 ⟨_, _, _root_.CategoryTheory.ReductionHom.gen a⟩ (by simp)
    | diag X =>
        simp [πapp, Category.assoc]
  let t : Cone K :=
    { pt := Rrel.pt
      π :=
        { app := πapp
          naturality := by
            intro A B f
            simpa using (hπnat f).symm } }
  refine HasLimit.mk ⟨t, IsLimit.ofExistsUnique ?_⟩
  intro s
  have hsCompat :
      reduction_target_relations_condition C S K CompatSched
        (Finset.univ : Finset (reduction_target_relation_index (J := J) S))
        (fun X _ => s.π.app (.src X)) := by
    -- Any cone already satisfies the source schedule and every indexed target relation.
    refine ⟨cone_source_family_compatible_of_schedule C S K sched s, ?_⟩
    intro r hr
    exact cone_source_family_satisfies_reduction_target_relation C S K s r
  obtain ⟨l, hl, hluniq⟩ := Rrel.isUniversal (fun X _ => s.π.app (.src X)) hsCompat
  refine ⟨l, ?_, ?_⟩
  · intro A
    cases A with
    | src X =>
        simpa [t] using hl X (Finset.mem_univ X)
    | tgt Y =>
        -- The target leg is defined from the source leg via the diagonal arrow.
        change l ≫ (Rrel.π Y (Finset.mem_univ _) ≫
            K.map (_root_.CategoryTheory.ReductionHom.diag Y)) = s.π.app (.tgt Y)
        rw [← Category.assoc, hl Y (Finset.mem_univ Y)]
        simpa using s.w (_root_.CategoryTheory.ReductionHom.diag Y)
  · intro m hm
    -- Uniqueness is already controlled by the universal property on the source legs.
    exact hluniq m (fun X hX => by simpa [t] using hm (.src X))

/-- If `C` has equalizers and pullbacks, then it has finite connected limits. -/
theorem hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks [HasEqualizers C] [HasPullbacks C] :
    HasFiniteConnectedLimits C where
  out := fun J _ _ _ ↦ by
    classical
    refine { has_limit := fun K ↦ ?_ }
    -- Reduce the finite connected indexing shape to the explicit bipartite category from
    -- Lemma 4.18.1 by taking all arrows as generators.
    obtain ⟨S, hS, hsplit⟩ := finite_arrow_generators_of_finCategory J
    obtain ⟨F, hInitial⟩ := exists_initial_reduction_functor (J := J) S hS hsplit
    letI : F.Initial := hInitial
    -- Transport connectedness across the initial functor so the reduced shape matches the
    -- connected hypothesis needed for the source proof.
    haveI : IsConnected (_root_.CategoryTheory.ReductionObj (I := J) S) :=
      (Functor.isConnected_iff_of_initial F).mpr inferInstance
    -- Apply the still-missing pullback/equalizer construction on the reduced bipartite diagram.
    haveI : HasLimit (F ⋙ K) :=
      hasLimit_of_connected_reduction_diagram (C := C) (J := J) S hS (K := F ⋙ K)
    -- Transfer the constructed limit back along the initial functor.
    exact Functor.Initial.hasLimit_of_comp F

/-- Lemma 4.18.2: a category has limits of every finite connected small diagram if and only if it
has equalizers and fibre products. -/
-- Proof sketch: equalizers and pullbacks are themselves finite connected limits, so the forward
-- implication is immediate. For the converse, use Lemma 4.18.1 to replace any finite connected
-- indexing category by a finite bipartite one, then inductively merge source vertices using
-- pullbacks until only one source remains; the remaining limit is a successive equalizer.
theorem finite_connected_limits_iff_equalizers_and_pullbacks :
    HasFiniteConnectedLimits C ↔ HasEqualizers C ∧ HasPullbacks C := by
  constructor
  · intro h
    letI : HasFiniteConnectedLimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hE, hPB⟩
    letI : HasEqualizers C := hE
    letI : HasPullbacks C := hPB
    exact hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks C

end CategoryTheory.Limits
