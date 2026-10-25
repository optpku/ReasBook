module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Plus

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))
variable (U : C)

/- Domain-style sampling for Lemma 7.10.16:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Meq`,
  `CategoryTheory.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Presheaf.IsLocallyInjective`,
  `CategoryTheory.Presheaf.IsSheaf.amalgamate`,
  `CategoryTheory.Presheaf.IsSheaf.hom_ext`;
- source-facing layer: the two textbook assertions describing sections of `J.sheafify F` in terms
  of local representatives in `F` and the converse gluing of compatible matching families;
- core/canonical owners: the matching-family object `Meq F S`, the local-bijectivity owners for
  `J.toSheafify F`, and the sheaf gluing/extensionality API on `J.sheafify F`;
- bridge/view layer: the source-facing existence and uniqueness theorems below, derived from those
  owner abstractions.

Primitive data for the second assertion are exactly a cover `S : J.Cover U` and a matching family
`x : Meq F S`. The glued section, its restriction formula, and the uniqueness statement are
derived API from the canonical sheaf owner `J.sheafify_isSheaf F`; no additional public wrapper
around matching families is warranted.
-/

-- Proof sketch: local surjectivity of `J.toSheafify F` gives local representatives for any
-- section of `J.sheafify F`, and local injectivity provides the compatibility on overlaps after
-- refining by further covers. Conversely, `J.sheafify F` is a sheaf, so any compatible matching
-- family of sections of `F` glues uniquely to a global section.
/-- Helper for Lemma 7.10.16: the image sieve of a sheafified section is a covering sieve, and
each arrow in that cover carries a chosen representative in the original presheaf. -/
lemma imageSieve_cover_with_local_preimages
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S : J.Cover U) (y : ∀ I : S.Arrow, F.obj (op I.Y)),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I) := by
  let S : J.Cover U :=
    ⟨Presheaf.imageSieve (J.toSheafify F) s, Presheaf.imageSieve_mem J (J.toSheafify F) s⟩
  let y : ∀ I : S.Arrow, F.obj (op I.Y) :=
    fun I ↦ Presheaf.localPreimage (J.toSheafify F) s I.f I.hf
  refine ⟨S, y, ?_⟩
  intro I
  -- The chosen representative maps to the restricted sheafified section by construction.
  simpa [y] using (Presheaf.app_localPreimage (J.toSheafify F) s I.f I.hf).symm

/-- Helper for Lemma 7.10.16: on each overlap of the initial local representatives, local
injectivity of `J.toSheafify F` yields a covering on which the two pullbacks agree. -/
lemma overlap_equalizer_cover_of_local_representatives
    (s : (J.sheafify F).obj (op U))
    (S : J.Cover U)
    (y : ∀ I : S.Arrow, F.obj (op I.Y))
    (hy : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I)) :
    ∃ T : ∀ r : S.Relation, J.Cover r.r.Z,
      ∀ r : S.Relation, ∀ I : (T r).Arrow,
        F.map I.f.op (F.map r.r.g₁.op (y r.fst)) =
          F.map I.f.op (F.map r.r.g₂.op (y r.snd)) := by
  let T : ∀ r : S.Relation, J.Cover r.r.Z := fun r ↦
    let a : F.obj (op r.r.Z) := F.map r.r.g₁.op (y r.fst)
    let b : F.obj (op r.r.Z) := F.map r.r.g₂.op (y r.snd)
    let h :
        (J.toSheafify F).app (op r.r.Z) a =
          (J.toSheafify F).app (op r.r.Z) b := by
      -- Both images are the restriction of the original global section to the overlap object.
      calc
        (J.toSheafify F).app (op r.r.Z) a =
            (J.sheafify F).map r.r.g₁.op ((J.toSheafify F).app (op r.fst.Y) (y r.fst)) := by
              simpa [a] using
                (FunctorToTypes.naturality _ _ (J.toSheafify F) r.r.g₁.op (y r.fst))
        _ = (J.sheafify F).map r.r.g₁.op ((J.sheafify F).map r.fst.f.op s) := by
              rw [hy r.fst]
        _ = (J.sheafify F).map r.r.g₂.op ((J.sheafify F).map r.snd.f.op s) := by
              simpa only [FunctorToTypes.map_comp_apply, op_comp] using
                congrArg (fun k => (J.sheafify F).map k.op s) r.r.w
        _ = (J.sheafify F).map r.r.g₂.op ((J.toSheafify F).app (op r.snd.Y) (y r.snd)) := by
              rw [hy r.snd]
        _ = (J.toSheafify F).app (op r.r.Z) b := by
              simpa [b] using
                (FunctorToTypes.naturality _ _ (J.toSheafify F) r.r.g₂.op (y r.snd)).symm
    let E : Sieve r.r.Z := Presheaf.equalizerSieve (X := op r.r.Z) a b
    have hmem : E ∈ J r.r.Z := by
      simpa [E] using
        (Presheaf.equalizerSieve_mem (J := J) (φ := J.toSheafify F) (X := op r.r.Z) a b h)
    ⟨E, hmem⟩
  refine ⟨T, ?_⟩
  intro r I
  -- Membership in the equalizer sieve is exactly the required equality.
  exact I.hf

/-- Helper for Lemma 7.10.16: a section of the sheafification is represented by a matching family
of `F⁺`-sections on some outer cover. -/
lemma outer_plus_representation_of_sheafification_section
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀),
      s = Plus.mk y := by
  -- Unfold the concrete sheafification model only at the outermost level.
  simpa using (Plus.exists_rep (J := J) (P := J.plusObj F) s)

/-- Helper for Lemma 7.10.16: each local `F⁺`-section in an outer matching family admits a
representative by a matching family of `F`-sections on an inner cover. -/
lemma inner_plus_representatives_over_outer_cover
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀) :
    ∃ (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      ∀ I : S₀.Arrow, y I = Plus.mk (t I) := by
  -- Choose a concrete `F`-matching family representing each local `F⁺`-section.
  choose T t ht using fun I => Plus.exists_rep (J := J) (P := F) (y I)
  exact ⟨T, t, ht⟩

/-- Helper for Lemma 7.10.16: on each outer overlap, the chosen inner representatives admit a
common refinement over which their pullbacks agree strictly as matching families of `F`. -/
lemma overlap_refinement_of_nested_representatives
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀)
    (T : ∀ I : S₀.Arrow, J.Cover I.Y)
    (t : ∀ I : S₀.Arrow, Meq F (T I))
    (ht : ∀ I : S₀.Arrow, y I = Plus.mk (t I)) :
    ∀ r : S₀.Relation,
      ∃ (W : J.Cover r.r.Z)
        (h₁ : W ⟶ (J.pullback r.r.g₁).obj (T r.fst))
        (h₂ : W ⟶ (J.pullback r.r.g₂).obj (T r.snd)),
        ((t r.fst).pullback r.r.g₁).refine h₁ = ((t r.snd).pullback r.r.g₂).refine h₂ := by
  intro r
  -- Rewrite the outer compatibility equality using the chosen inner representatives.
  have hr : Plus.mk ((t r.fst).pullback r.r.g₁) = Plus.mk ((t r.snd).pullback r.r.g₂) := by
    calc
      Plus.mk ((t r.fst).pullback r.r.g₁)
          = (J.plusObj F).map r.r.g₁.op (Plus.mk (t r.fst)) := by
              symm
              exact Plus.res_mk_eq_mk_pullback (J := J) (x := t r.fst) r.r.g₁
      _ = (J.plusObj F).map r.r.g₁.op (y r.fst) := by
            rw [ht]
      _ = (J.plusObj F).map r.r.g₂.op (y r.snd) := by
            exact y.condition r
      _ = (J.plusObj F).map r.r.g₂.op (Plus.mk (t r.snd)) := by
            rw [ht]
      _ = Plus.mk ((t r.snd).pullback r.r.g₂) := by
            exact Plus.res_mk_eq_mk_pullback (J := J) (x := t r.snd) r.r.g₂
  -- Equality in `F⁺` is exactly represented by a common refinement of the underlying `F` data.
  simpa using
    (Plus.eq_mk_iff_exists (J := J) ((t r.fst).pullback r.r.g₁) ((t r.snd).pullback r.r.g₂)).mp hr

/-- Helper for Lemma 7.10.16: a strict `Meq F`-description of a sheafified section on one cover
already descends that section to a global section of `F⁺`. -/
lemma plus_representation_of_strict_matching_family
    (s : (J.sheafify F).obj (op U))
    {S : J.Cover U} (x : Meq F S)
    (hx : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I)) :
    ∃ y : (J.plusObj F).obj (op U),
      s = (J.toPlus (J.plusObj F)).app (op U) y := by
  refine ⟨Plus.mk x, ?_⟩
  -- Equality in `F⁺⁺` follows from equality on a cover because `F⁺` is separated.
  apply Plus.sep (J := J) (P := J.plusObj F) (S := S)
  intro I
  -- Rewrite the chosen local `F`-section through `F⁺` and then through `F⁺⁺`.
  calc
    (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := hx I
    _ = (J.sheafify F).map I.f.op ((J.toPlus (J.plusObj F)).app (op U) (Plus.mk x)) := by
          rw [GrothendieckTopology.toSheafify]
          rw [GrothendieckTopology.plusMap_toPlus]
          change
            (J.toPlus (J.plusObj F)).app (op I.Y) ((J.toPlus F).app (op I.Y) (x I)) =
              (J.sheafify F).map I.f.op ((J.toPlus (J.plusObj F)).app (op U) (Plus.mk x))
          have hnat :=
            (FunctorToTypes.naturality _ _ (J.toPlus (J.plusObj F)) I.f.op (Plus.mk x)).symm
          exact Eq.trans
            (congrArg ((J.toPlus (J.plusObj F)).app (op I.Y))
              (Plus.toPlus_apply (J := J) (P := F) S x I))
            hnat.symm

/-- Lemma 7.10.16, first assertion: every section of the sheafification is represented by an
outer matching family of `F⁺`-sections, and each of those local `F⁺`-sections is itself represented
by a matching family of sections of the original presheaf `F`.  This is the faithful two-stage
`F⁺⁺` formulation of the source phrase "locally comes from the presheaf"; it deliberately does
not assert the stronger false claim that one can strictify to a single `Meq F S` over the original
cover. -/
theorem exists_cover_and_matchingFamily_of_sheafification_section
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀)
      (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      s = Plus.mk y ∧ ∀ I : S₀.Arrow, y I = Plus.mk (t I) := by
  obtain ⟨S₀, y, hy⟩ := outer_plus_representation_of_sheafification_section (J := J) (F := F) (U := U) s
  obtain ⟨T, t, ht⟩ := inner_plus_representatives_over_outer_cover (J := J) (F := F) (U := U) y
  exact ⟨S₀, y, T, t, hy, ht⟩


/-- Companion source-facing formulation of Lemma 7.10.16, second assertion: a compatible matching
family glues uniquely to a section of the sheafification. -/
theorem existsUnique_sheafificationSection_of_matchingFamily
    (S : J.Cover U) (x : Meq F S) :
    ∃! s : (J.sheafify F).obj (op U),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := by
  let y : ∀ I : S.Arrow, PUnit ⟶ (J.sheafify F).obj (op I.Y) :=
    fun I _ ↦ (J.toSheafify F).app (op I.Y) (x I)
  have hy :
      ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
        y I₁ ≫ (J.sheafify F).map r.g₁.op = y I₂ ≫ (J.sheafify F).map r.g₂.op := by
    intro I₁ I₂ r
    funext _
    change
      (J.sheafify F).map r.g₁.op ((J.toSheafify F).app (op I₁.Y) (x I₁)) =
        (J.sheafify F).map r.g₂.op ((J.toSheafify F).app (op I₂.Y) (x I₂))
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₁.op (x I₁)]
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₂.op (x I₂)]
    exact congrArg ((J.toSheafify F).app (op r.Z))
      (x.condition (Cover.Relation.mk' r))
  refine ⟨((J.sheafify_isSheaf F).amalgamate S y hy) PUnit.unit, ?_, ?_⟩
  · intro I
    exact congrFun ((J.sheafify_isSheaf F).amalgamate_map S y hy I) PUnit.unit
  intro s hs
  have h :
      (fun _ : PUnit ↦ s) = (J.sheafify_isSheaf F).amalgamate S y hy := by
    apply (J.sheafify_isSheaf F).hom_ext S
    intro I
    funext u
    cases u
    simpa [y, hs I] using
      congrFun (((J.sheafify_isSheaf F).amalgamate_map S y hy I).symm) PUnit.unit
  exact congrFun h PUnit.unit
