module

public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.Index
public import stacks_project.Chap07.Lemma_7_26_4.DirectSourceComparison.ComponentRestriction

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}
variable [univLE : UnivLE.{max u v, w}]

omit [UnivLE.{max u v, w}] in
theorem eq_iff_eq_of_heq {α β : Sort _} {a b : α} {c d : β}
    (hac : HEq a c) (hbd : HEq b d) : (a = b) ↔ (c = d) := by
  cases hac
  cases hbd
  exact Iff.rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: two heterogeneously equal equivalences send heterogeneously equal
arguments to heterogeneously equal values once the domain and codomain types have been named. -/
theorem equiv_apply_heq_of_type_eqs {α α' : Sort _} {β β' : Sort _}
    (hα : α = α') (hβ : β = β')
    {e : α ≃ β} {e' : α' ≃ β'} (he : HEq e e')
    {x : α} {x' : α'} (hx : HEq x x') :
    HEq (e x) (e' x') := by
  -- After aligning the source and target types, the equivalences themselves become equal and
  -- the conclusion is just the supplied heterogeneous equality of inputs.
  subst hα
  subst hβ
  cases he
  rw [eq_of_heq hx]

omit [UnivLE.{max u v, w}] in
theorem natTrans_app_heq_of_eq
    {A : Type*} {B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (η : F ⟶ G) {X Y : A} (h : X = Y) :
    HEq (η.app X) (η.app Y) := by
  subst h
  rfl

omit [UnivLE.{max u v, w}] in
theorem equiv_cast_symm_apply {α β : Sort _} (h : α = β) (b : β) :
    (Equiv.cast h).symm b = cast h.symm b := by
  subst h
  rfl

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
    {D : Type*} [Category D] (F : Dᵒᵖ ⥤ Type w)
    {A B A' B' : D} (hA : A = A') (hB : B = B')
    (φ : A ⟶ B) (ψ : A' ⟶ B')
    (hφ : φ = eqToHom hA ≫ ψ ≫ eqToHom hB.symm)
    {x : F.obj (Opposite.op B)} {y : F.obj (Opposite.op B')}
    (hxy : HEq x y) :
    HEq (F.map φ.op x) (F.map ψ.op y) := by
  subst hA
  subst hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hφ
  subst hφ
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_presheaf_map_heq_of_eqs
    {D : Type*} [Category D] {F G : Dᵒᵖ ⥤ Type w}
    (hF : HEq F G)
    {A B A' B' : D} (hA : A = A') (hB : B = B')
    (φ : A ⟶ B) (ψ : A' ⟶ B')
    (hφ : HEq φ ψ)
    {x : F.obj (Opposite.op B)} {y : G.obj (Opposite.op B')}
    (hxy : HEq x y) :
    HEq (F.map φ.op x) (G.map ψ.op y) := by
  cases hF
  subst hA
  subst hB
  have hφ' : φ = ψ := eq_of_heq hφ
  subst hφ'
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_sheaf_hom_app_heq_of_eqs
    {S : C}
    {M N M' N' : Sheaf (J.over S) (Type w)}
    (hM : M = M') (hN : N = N')
    (φ : M ⟶ N) (ψ : M' ⟶ N')
    (hφ : HEq φ ψ)
    {X X' : (Over S)ᵒᵖ} (hX : X = X')
    {x : M.1.obj X} {y : M'.1.obj X'}
    (hxy : HEq x y) :
    HEq (φ.hom.app X x) (ψ.hom.app X' y) := by
  subst hM
  subst hN
  subst hX
  have hφ' : φ = ψ := eq_of_heq hφ
  subst hφ'
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_sheaf_hom_app_heq
    {S : C}
    {M N M' N' : Sheaf (J.over S) (Type w)}
    (hM : M = M') (hN : N = N')
    (φ : M ⟶ N) (ψ : M' ⟶ N')
    (hφ : HEq φ ψ)
    {X X' : (Over S)ᵒᵖ} (hX : HEq X X')
    {x : M.1.obj X} {y : M'.1.obj X'}
    (hxy : HEq x y) :
    HEq (φ.hom.app X x) (ψ.hom.app X' y) := by
  exact localized_cover_descent_sheaf_hom_app_heq_of_eqs
    hM hN φ ψ hφ (eq_of_heq hX) hxy

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_fun_app_heq_of_type_eqs {α α' : Sort _} {β β' : Sort _}
    (hα : α = α') (hβ : β = β')
    {f : α → β} {g : α' → β'} (hf : HEq f g)
    {x : α} {y : α'} (hxy : HEq x y) :
    HEq (f x) (g y) := by
  subst hα
  subst hβ
  have hf' : f = g := eq_of_heq hf
  subst hf'
  rw [eq_of_heq hxy]

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: a terminal-section restriction in
`toDescentData` is the underlying sheaf restriction along the corresponding over-map. -/
theorem localized_cover_descent_toDescentData_terminal_map_heq
    {S : C}
    (𝒱 : J.Cover S)
    (M : Sheaf (J.over S) (Type w))
    (K : 𝒱.Arrow)
    (Z : Over S)
    (gi : Z ⟶ Over.mk K.f)
    (x : M.1.obj (Opposite.op (Over.mk K.f))) :
    HEq
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := gi.left)
          (M := (J.overMapPullback (Type w) K.f).obj M)).symm
        ((((J.overMapPullback (Type w) K.f).obj M).1.map
          (show Over.mk gi.left ⟶ Over.mk (𝟙 K.Y) from Over.homMk gi.left).op)
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := K.f) (M := M)).symm x)))
      (M.1.map gi.op x) := by
  cases K with
  | mk Y f hf =>
      rcases Z with ⟨Zleft, Zright, Zhom⟩
      cases Zright
      let A : Over S := Over.mk (gi.left ≫ f)
      let B : Over S := Over.mk ((𝟙 Y) ≫ f)
      let A' : Over S := Over.mk Zhom
      let B' : Over S := Over.mk f
      have hA : A = A' := by
        change Over.mk (gi.left ≫ f) = Over.mk Zhom
        exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
          (gi.left ≫ f) Zhom (heq_of_eq (Over.w gi))
      have hB : B = B' := by
        change Over.mk ((𝟙 Y) ≫ f) = Over.mk f
        exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
          ((𝟙 Y) ≫ f) f (heq_of_eq (Category.id_comp f))
      have hAleft : (eqToHom hA).left = 𝟙 Zleft := by
        rw [over_eqToHom_left hA]
        rfl
      have hBleft : (eqToHom hB.symm).left = 𝟙 Y := by
        rw [over_eqToHom_left hB.symm]
        rfl
      let φ : A ⟶ B :=
        (Over.map f).map
          (show Over.mk gi.left ⟶ Over.mk (𝟙 Y) from Over.homMk gi.left)
      have hφ : φ = eqToHom hA ≫ gi ≫ eqToHom hB.symm := by
        apply Over.OverMorphism.ext
        change gi.left = (eqToHom hA).left ≫ gi.left ≫ (eqToHom hB.symm).left
        rw [hAleft, hBleft]
        change gi.left = 𝟙 Zleft ≫ (gi.left ≫ 𝟙 Y)
        calc
          gi.left = gi.left ≫ 𝟙 Y := (Category.comp_id gi.left).symm
          _ = 𝟙 Zleft ≫ (gi.left ≫ 𝟙 Y) :=
            (Category.id_comp (gi.left ≫ 𝟙 Y)).symm
      refine (cast_heq _ _).trans ?_
      simpa [GrothendieckTopology.overMapPullback, φ] using
        (localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
          M.1 hA hB φ gi hφ (cast_heq _ _))

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting a sheaf section after
first restricting along a slice morphism agrees heterogeneously with restriction along the
composite over-map arrow. -/
theorem localized_cover_descent_overMap_pullback_map_comp_heq
    {S : C}
    (M : Sheaf (J.over S) (Type w))
    {A B : Over S}
    (g : A ⟶ B)
    {Z : C}
    (a : Z ⟶ A.left)
    (x : M.1.obj (Opposite.op B)) :
    HEq
      (((J.overMapPullback (Type w) B.hom).obj M).1.map
        (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
          Over.homMk (a ≫ g.left)).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := B.hom) (M := M)).symm
          x))
      (((J.overMapPullback (Type w) A.hom).obj M).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := A.hom) (M := M)).symm
          (M.1.map g.op x))) := by
  let A₀ : Over S := (Over.map B.hom).obj (Over.mk (a ≫ g.left))
  let A₁ : Over S := (Over.map A.hom).obj (Over.mk a)
  let B₀ : Over S := (Over.map B.hom).obj (Over.mk (𝟙 B.left))
  let Aₜ : Over S := (Over.map A.hom).obj (Over.mk (𝟙 A.left))
  have hA₀ : A₀ = A₁ := by
    dsimp [A₀, A₁]
    apply over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
    exact heq_of_eq (by
      calc
        (a ≫ g.left) ≫ B.hom = a ≫ (g.left ≫ B.hom) :=
          Category.assoc a g.left B.hom
        _ = a ≫ A.hom :=
          congrArg (fun h ↦ a ≫ h) (Over.w g))
  have hB₀ : B₀ = B := by
    change Over.mk ((𝟙 B.left) ≫ B.hom) = B
    exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
      ((𝟙 B.left) ≫ B.hom) B.hom (heq_of_eq (Category.id_comp B.hom))
  have hAₜ : Aₜ = A := by
    change Over.mk ((𝟙 A.left) ≫ A.hom) = A
    exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
      ((𝟙 A.left) ≫ A.hom) A.hom (heq_of_eq (Category.id_comp A.hom))
  let φ : A₀ ⟶ B₀ :=
    (Over.map B.hom).map
      (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
        Over.homMk (a ≫ g.left))
  let ψ : A₁ ⟶ B :=
    (show A₁ ⟶ A from Over.homMk a) ≫ g
  have hφ : φ = eqToHom hA₀ ≫ ψ ≫ eqToHom hB₀.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hA₀).left = 𝟙 Z := by
      rw [over_eqToHom_left hA₀]
      simp [A₀, A₁]
    have hBleft : (eqToHom hB₀.symm).left = 𝟙 B.left := by
      rw [over_eqToHom_left hB₀.symm]
      rfl
    dsimp [φ, ψ, A₀, A₁, B₀]
    calc
      a ≫ g.left = 𝟙 Z ≫ (a ≫ g.left) ≫ 𝟙 B.left := by
        rw [Category.id_comp, Category.comp_id]
      _ = (eqToHom hA₀).left ≫ (a ≫ g.left) ≫ (eqToHom hB₀.symm).left := by
        rw [hAleft, hBleft]
        rfl
  have hleft :
      HEq
        (((J.overMapPullback (Type w) B.hom).obj M).1.map
          (show Over.mk (a ≫ g.left) ⟶ Over.mk (𝟙 B.left) from
            Over.homMk (a ≫ g.left)).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := B.hom) (M := M)).symm
            x))
        (M.1.map ψ.op x) := by
    simpa [GrothendieckTopology.overMapPullback, A₀, B₀, φ, ψ] using
      (localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
        M.1 hA₀ hB₀ φ ψ hφ (cast_heq _ _))
  let ρ : A₁ ⟶ Aₜ :=
    (Over.map A.hom).map
      (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a)
  let ρ' : A₁ ⟶ A := show A₁ ⟶ A from Over.homMk a
  have hρ : ρ = eqToHom (rfl : A₁ = A₁) ≫ ρ' ≫ eqToHom hAₜ.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hAₜ.symm).left = 𝟙 A.left := by
      rw [over_eqToHom_left hAₜ.symm]
      rfl
    dsimp [ρ, ρ', A₁, Aₜ]
    calc
      a = 𝟙 Z ≫ a ≫ 𝟙 A.left := by
        rw [Category.id_comp, Category.comp_id]
      _ = 𝟙 Z ≫ a ≫ (eqToHom hAₜ.symm).left := by
        rw [hAleft]
        rfl
  have hright₀ :
      HEq
        (((J.overMapPullback (Type w) A.hom).obj M).1.map
          (show Over.mk a ⟶ Over.mk (𝟙 A.left) from Over.homMk a).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := A.hom) (M := M)).symm
            (M.1.map g.op x)))
        (M.1.map ρ'.op (M.1.map g.op x)) := by
    simpa [GrothendieckTopology.overMapPullback, A₁, Aₜ, ρ, ρ'] using
      (localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
        M.1 (rfl : A₁ = A₁) hAₜ ρ ρ' hρ (cast_heq _ _))
  have hright₁ :
      M.1.map ρ'.op (M.1.map g.op x) = M.1.map ψ.op x := by
    calc
      M.1.map ρ'.op (M.1.map g.op x) = M.1.map (g.op ≫ ρ'.op) x :=
        (FunctorToTypes.map_comp_apply M.1 g.op ρ'.op x).symm
      _ = M.1.map ψ.op x := by
        rfl
  exact hleft.trans ((hright₀.trans (heq_of_eq hright₁)).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: restricting a terminal over-map section is the same, up to the
canonical terminal cast, as the original sheaf restriction along the corresponding slice map. -/
theorem localized_cover_descent_overMap_terminal_restrict_heq
    {S X Y : C}
    (M : Sheaf (J.over S) (Type w))
    (f : X ⟶ S)
    (a : Y ⟶ X)
    (x : M.1.obj (Opposite.op (Over.mk f))) :
    HEq
      (((J.overMapPullback (Type w) f).obj M).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 X) from Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := f) (M := M)).symm
          x))
      (M.1.map (show Over.mk (a ≫ f) ⟶ Over.mk f from Over.homMk a).op x) := by
  let A : Over S := (Over.map f).obj (Over.mk a)
  let B : Over S := (Over.map f).obj (Over.mk (𝟙 X))
  let A' : Over S := Over.mk (a ≫ f)
  let B' : Over S := Over.mk f
  have hA : A = A' := by
    change Over.mk (a ≫ f) = Over.mk (a ≫ f)
    rfl
  have hB : B = B' := by
    change Over.mk ((𝟙 X) ≫ f) = Over.mk f
    exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
      ((𝟙 X) ≫ f) f (heq_of_eq (Category.id_comp f))
  let φ : A ⟶ B :=
    (Over.map f).map (show Over.mk a ⟶ Over.mk (𝟙 X) from Over.homMk a)
  let ψ : A' ⟶ B' := show Over.mk (a ≫ f) ⟶ Over.mk f from Over.homMk a
  have hφ : φ = eqToHom hA ≫ ψ ≫ eqToHom hB.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hA).left = 𝟙 Y := by
      rw [over_eqToHom_left hA]
      rfl
    have hBleft : (eqToHom hB.symm).left = 𝟙 X := by
      rw [over_eqToHom_left hB.symm]
      rfl
    dsimp [φ, ψ, A, A', B, B']
    rw [hAleft, hBleft]
    rw [Category.id_comp, Category.comp_id]
  simpa [GrothendieckTopology.overMapPullback, A, A', B, B', φ, ψ] using
    localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
      M.1 hA hB φ ψ hφ (cast_heq _ _)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the terminal over-map restriction above an object already written as
`Over.map f` agrees with the sheaf restriction along the mapped slice morphism. -/
theorem localized_cover_descent_overMap_terminal_restrict_overMap_hom_heq
    {S X Z : C}
    (M : Sheaf (J.over S) (Type w))
    (f : X ⟶ S)
    (T : Over X)
    (a : Z ⟶ T.left)
    (x : M.1.obj (Opposite.op ((Over.map f).obj T))) :
    HEq
      (((J.overMapPullback (Type w) ((Over.map f).obj T).hom).obj M).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 ((Over.map f).obj T).left) from Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := ((Over.map f).obj T).hom) (M := M)).symm
          x))
      (M.1.map
        ((Over.map f).map
          (show (Over.map T.hom).obj (Over.mk a) ⟶ T from Over.homMk a)).op x) := by
  let A : Over S := Over.mk (a ≫ ((Over.map f).obj T).hom)
  let B : Over S := Over.mk ((Over.map f).obj T).hom
  let A' : Over S := (Over.map f).obj ((Over.map T.hom).obj (Over.mk a))
  let B' : Over S := (Over.map f).obj T
  let ψ : A ⟶ B := show Over.mk (a ≫ ((Over.map f).obj T).hom) ⟶
    Over.mk ((Over.map f).obj T).hom from Over.homMk a
  let ψ' : A' ⟶ B' :=
    (Over.map f).map (show (Over.map T.hom).obj (Over.mk a) ⟶ T from Over.homMk a)
  have hA : A = A' := by
    change Over.mk (a ≫ (T.hom ≫ f)) = Over.mk ((a ≫ T.hom) ≫ f)
    exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
      (a ≫ (T.hom ≫ f)) ((a ≫ T.hom) ≫ f)
      (heq_of_eq (Category.assoc a T.hom f).symm)
  have hB : B = B' := by
    change Over.mk ((Over.map f).obj T).hom = (Over.map f).obj T
    exact over_mk_hext (𝒞 := C) (B := S) (hY := rfl)
      ((Over.map f).obj T).hom ((Over.map f).obj T).hom (heq_of_eq rfl)
  have hψ : ψ = eqToHom hA ≫ ψ' ≫ eqToHom hB.symm := by
    apply Over.OverMorphism.ext
    have hAleft : (eqToHom hA).left = 𝟙 Z := by
      rw [over_eqToHom_left hA]
      simp [A, A']
    have hBleft : (eqToHom hB.symm).left = 𝟙 T.left := by
      rw [over_eqToHom_left hB.symm]
      rfl
    dsimp [ψ, ψ', A, A', B, B']
    calc
      a = 𝟙 Z ≫ a ≫ 𝟙 T.left := by
        rw [Category.id_comp, Category.comp_id]
      _ = (eqToHom hA).left ≫ a ≫ (eqToHom hB.symm).left := by
        rw [← hAleft, ← hBleft]
        rfl
  have hterminal :
      HEq
        (((J.overMapPullback (Type w) ((Over.map f).obj T).hom).obj M).1.map
          (show Over.mk a ⟶ Over.mk (𝟙 ((Over.map f).obj T).left) from Over.homMk a).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := ((Over.map f).obj T).hom) (M := M)).symm
            x))
        (M.1.map ψ.op x) := by
    simpa [A, B, ψ] using
      localized_cover_descent_overMap_terminal_restrict_heq
        (J := J) (M := M) (f := ((Over.map f).obj T).hom) (a := a) x
  have hmap :
      HEq (M.1.map ψ.op x) (M.1.map ψ'.op x) := by
    exact localized_cover_descent_presheaf_map_heq_of_eqToHom_conj
      M.1 hA hB ψ ψ' hψ (heq_of_eq rfl)
  simpa [ψ'] using hterminal.trans hmap

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: terminal compatibility for an
ordinary `toDescentData` object implies ordinary arrows-compatibility of the underlying sheaf
sections. -/
theorem localized_cover_descent_toDescentData_terminalCompatible_to_arrows
    {S : C}
    (𝒱 : J.Cover S)
    (M : Sheaf (J.over S) (Type w))
    (s : ∀ K : 𝒱.Arrow,
      ((((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : 𝒱.Arrow ↦ K.f)).obj M).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))
    (hs :
      localized_cover_descent_terminalCompatible (J := J) 𝒱
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun K : 𝒱.Arrow ↦ K.f)).obj M) s) :
    Presieve.Arrows.Compatible M.1
      (fun K : 𝒱.Arrow ↦
        (show Over.mk K.f ⟶ Over.mk (𝟙 S) from Over.homMk K.f))
      (fun K ↦
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f) (M := M))
          (s K)) := by
  let P :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun K : 𝒱.Arrow ↦ K.f)).obj M)
  intro K L Z gi gj h
  let r : K.Relation L := {
    Z := Z.left
    g₁ := gi.left
    g₂ := gj.left
    w := by
      simpa using congrArg (fun e ↦ e.left) h
  }
  let R : 𝒱.Relation := Cover.Relation.mk' r
  have hR := hs R
  let xK : M.1.obj (Opposite.op (Over.mk K.f)) :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := K.f) (M := M))
      (s K)
  let xL : M.1.obj (Opposite.op (Over.mk L.f)) :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := L.f) (M := M))
      (s L)
  have hleft_terminal :
      HEq
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := gi.left)
            (M := P.obj K)).symm
          (((P.obj K).1.map
            (show Over.mk gi.left ⟶ Over.mk (𝟙 K.Y) from Over.homMk gi.left).op)
            (s K)))
        (M.1.map gi.op xK) := by
    simpa [P, xK, Pseudofunctor.toDescentData] using
      localized_cover_descent_toDescentData_terminal_map_heq (J := J) 𝒱 M K Z gi xK
  have hright_terminal :
      HEq
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := gj.left)
            (M := P.obj L)).symm
          (((P.obj L).1.map
            (show Over.mk gj.left ⟶ Over.mk (𝟙 L.Y) from Over.homMk gj.left).op)
            (s L)))
        (M.1.map gj.op xL) := by
    simpa [P, xL, Pseudofunctor.toDescentData] using
      localized_cover_descent_toDescentData_terminal_map_heq (J := J) 𝒱 M L Z gj xL
  dsimp [localized_cover_descent_terminalCompatible] at hR
  dsimp [R, r] at hR
  let XZ : (Over Z.left)ᵒᵖ := Opposite.op (Over.mk (𝟙 Z.left))
  have hkL :
      L.f.op.toLoc ≫ gj.left.op.toLoc =
        K.f.op.toLoc ≫ gi.left.op.toLoc := by
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
      congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op r.w.symm)
  let leftTerm :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := gi.left) (M := P.obj K)).symm
      (((P.obj K).1.map
        (show Over.mk gi.left ⟶ Over.mk (𝟙 K.Y) from Over.homMk gi.left).op) (s K))
  let A :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      K.f.op.toLoc gi.left.op.toLoc (K.f.op.toLoc ≫ gi.left.op.toLoc) rfl).inv.toNatTrans.app M
  let B :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      L.f.op.toLoc gj.left.op.toLoc (K.f.op.toLoc ≫ gi.left.op.toLoc) hkL).hom.toNatTrans.app M
  have hinv : HEq (A.hom.app XZ leftTerm) leftTerm := by
    simpa [A, XZ, leftTerm, P, Pseudofunctor.toDescentData] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (f := K.f.op.toLoc)
        (g' := gi.left.op.toLoc)
        (k := K.f.op.toLoc ≫ gi.left.op.toLoc)
        (hk := rfl)
        M XZ leftTerm)
  have hhom : HEq (B.hom.app XZ (A.hom.app XZ leftTerm)) (A.hom.app XZ leftTerm) := by
    simpa [B, XZ] using
      (pf_mapComp'_hom_component_apply_heq
        (J := J)
        (f := L.f.op.toLoc)
        (g' := gj.left.op.toLoc)
        (k := K.f.op.toLoc ≫ gi.left.op.toLoc)
        (hk := hkL)
        M XZ (A.hom.app XZ leftTerm))
  have hleft_full :
      HEq ((A ≫ B).hom.app XZ leftTerm) (M.1.map gi.op xK) := by
    simpa [A, B, XZ, leftTerm, P, Pseudofunctor.toDescentData] using
      hhom.trans (hinv.trans hleft_terminal)
  have hmain : HEq (M.1.map gi.op xK) (M.1.map gj.op xL) :=
    hleft_full.symm.trans ((heq_of_eq hR).trans hright_terminal)
  exact eq_of_heq (by
    simpa [xK, xL] using hmain)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: arrows-compatible sheaf sections
give terminal-compatible sections for the corresponding `toDescentData` object. -/
theorem localized_cover_descent_toDescentData_arrows_to_terminalCompatible
    {S : C}
    (𝒱 : J.Cover S)
    (M : Sheaf (J.over S) (Type w))
    (x : ∀ K : 𝒱.Arrow, M.1.obj (Opposite.op (Over.mk K.f)))
    (hx :
      Presieve.Arrows.Compatible M.1
        (fun K : 𝒱.Arrow ↦
          (show Over.mk K.f ⟶ Over.mk (𝟙 S) from Over.homMk K.f))
        x) :
    localized_cover_descent_terminalCompatible (J := J) 𝒱
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : 𝒱.Arrow ↦ K.f)).obj M)
      (fun K ↦
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f) (M := M)).symm
          (x K)) := by
  let P :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun K : 𝒱.Arrow ↦ K.f)).obj M)
  intro R
  let K := R.fst
  let L := R.snd
  let Z : Over S := Over.mk (R.r.g₁ ≫ R.fst.f)
  let gi : Z ⟶ Over.mk K.f := Over.homMk R.r.g₁
  let gj : Z ⟶ Over.mk L.f :=
    Over.homMk R.r.g₂ (by
      simpa [Z, K, L] using R.r.w.symm)
  have hrel :
      gi ≫ (show Over.mk K.f ⟶ Over.mk (𝟙 S) from Over.homMk K.f) =
        gj ≫ (show Over.mk L.f ⟶ Over.mk (𝟙 S) from Over.homMk L.f) := by
    ext
    simpa [Z, K, L, gi, gj, Category.assoc] using R.r.w
  have hxR := hx K L Z gi gj hrel
  let XZ : (Over R.r.Z)ᵒᵖ := Opposite.op (Over.mk (𝟙 R.r.Z))
  have hkL :
      L.f.op.toLoc ≫ R.r.g₂.op.toLoc =
        K.f.op.toLoc ≫ R.r.g₁.op.toLoc := by
    simpa [K, L, ← Quiver.Hom.comp_toLoc, ← op_comp] using
      congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op R.r.w.symm)
  let leftTerm :=
    cast
      (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := R.r.g₁) (M := P.obj K)).symm
      (((P.obj K).1.map
        (show Over.mk R.r.g₁ ⟶ Over.mk (𝟙 K.Y) from Over.homMk R.r.g₁).op)
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f) (M := M)).symm
          (x K)))
  let A :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      K.f.op.toLoc R.r.g₁.op.toLoc (K.f.op.toLoc ≫ R.r.g₁.op.toLoc) rfl).inv.toNatTrans.app M
  let B :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      L.f.op.toLoc R.r.g₂.op.toLoc (K.f.op.toLoc ≫ R.r.g₁.op.toLoc) hkL).hom.toNatTrans.app M
  have hleft_terminal :
      HEq leftTerm (M.1.map gi.op (x K)) := by
    simpa [leftTerm, P, K, Z, gi, Pseudofunctor.toDescentData] using
      localized_cover_descent_toDescentData_terminal_map_heq (J := J) 𝒱 M K Z gi (x K)
  have hright_terminal :
      HEq
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := R.r.g₂) (M := P.obj L)).symm
          (((P.obj L).1.map
            (show Over.mk R.r.g₂ ⟶ Over.mk (𝟙 L.Y) from Over.homMk R.r.g₂).op)
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := L.f) (M := M)).symm
              (x L))))
        (M.1.map gj.op (x L)) := by
    simpa [P, L, Z, gj, Pseudofunctor.toDescentData] using
      localized_cover_descent_toDescentData_terminal_map_heq (J := J) 𝒱 M L Z gj (x L)
  have hinv : HEq (A.hom.app XZ leftTerm) leftTerm := by
    simpa [A, XZ, leftTerm, P, K, Pseudofunctor.toDescentData] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (f := K.f.op.toLoc)
        (g' := R.r.g₁.op.toLoc)
        (k := K.f.op.toLoc ≫ R.r.g₁.op.toLoc)
        (hk := rfl)
        M XZ leftTerm)
  have hhom : HEq (B.hom.app XZ (A.hom.app XZ leftTerm)) (A.hom.app XZ leftTerm) := by
    simpa [B, XZ] using
      (pf_mapComp'_hom_component_apply_heq
        (J := J)
        (f := L.f.op.toLoc)
        (g' := R.r.g₂.op.toLoc)
        (k := K.f.op.toLoc ≫ R.r.g₁.op.toLoc)
        (hk := hkL)
        M XZ (A.hom.app XZ leftTerm))
  have hleft_full :
      HEq ((A ≫ B).hom.app XZ leftTerm) (M.1.map gi.op (x K)) := by
    simpa [A, B, XZ, leftTerm, P, K, L, Pseudofunctor.toDescentData] using
      hhom.trans (hinv.trans hleft_terminal)
  exact eq_of_heq
    (hleft_full.trans ((heq_of_eq hxR).trans hright_terminal.symm))

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: terminal compatibility for the
normalized direct-source descent datum implies the component-side arrows compatibility used by
the direct glued-family predicate. -/
theorem localized_cover_descent_glue_direct_compatible_of_terminalCompatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T)
    (hs : localized_cover_descent_terminalCompatible (J := J)
      ((𝒰.pullback I.f).pullback T.hom)
      (localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I T) s) :
    localized_cover_descent_glue_direct_compatible (J := J) (U := U) 𝒰 D I T s := by
  let P := localized_cover_descent_pullbackDatum_over_direct_source
    (J := J) (U := U) 𝒰 D I T
  let M := (J.overMapPullback (Type w) T.hom).obj (D.obj I)
  let Q :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)).obj M)
  let φ := localized_cover_descent_pullbackDatum_over_direct_to_component_iso
    (J := J) (U := U) 𝒰 D I T
  -- Transport terminal compatibility along the direct-to-component descent-data isomorphism.
  have hQ :
      localized_cover_descent_terminalCompatible (J := J)
        ((𝒰.pullback I.f).pullback T.hom) Q
        (fun K ↦ (φ.hom.hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) (s K)) := by
    simpa [P, Q, φ] using
      localized_cover_descent_terminalCompatible_map
        (J := J) ((𝒰.pullback I.f).pullback T.hom) P Q φ.hom s hs
  -- The ordinary `toDescentData` bridge converts terminal compatibility into arrows
  -- compatibility; the pointwise iso computation gives exactly the direct predicate.
  have harrows :=
    localized_cover_descent_toDescentData_terminalCompatible_to_arrows
      (J := J) ((𝒰.pullback I.f).pullback T.hom) M
      (fun K ↦ (φ.hom.hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) (s K)) hQ
  simpa [localized_cover_descent_glue_direct_compatible, M, φ,
    localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply,
    localized_cover_descent_toDescentData_over_section_eq] using harrows

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: component-side compatibility for a
normalized direct-source family gives terminal compatibility for the direct-source descent datum. -/
theorem localized_cover_descent_glue_direct_terminalCompatible_of_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T)
    (hs : localized_cover_descent_glue_direct_compatible (J := J) (U := U) 𝒰 D I T s) :
    localized_cover_descent_terminalCompatible (J := J)
      ((𝒰.pullback I.f).pullback T.hom)
      (localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I T) s := by
  let P := localized_cover_descent_pullbackDatum_over_direct_source
    (J := J) (U := U) 𝒰 D I T
  let M := (J.overMapPullback (Type w) T.hom).obj (D.obj I)
  let Q :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)).obj M)
  let φ := localized_cover_descent_pullbackDatum_over_direct_to_component_iso
    (J := J) (U := U) 𝒰 D I T
  let x :=
    fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K (s K)
  -- Reconstruct terminal compatibility for the ordinary `toDescentData` object from the
  -- component-side arrows-compatible family.
  have hQ :
      localized_cover_descent_terminalCompatible (J := J)
        ((𝒰.pullback I.f).pullback T.hom) Q
        (fun K ↦
          cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := K.f) (M := M)).symm
            (x K)) := by
    exact localized_cover_descent_toDescentData_arrows_to_terminalCompatible
      (J := J) ((𝒰.pullback I.f).pullback T.hom) M x
      (by
        simpa [localized_cover_descent_glue_direct_compatible, M, x] using hs)
  -- Pull this terminal-compatible family back through the inverse direct-to-component
  -- descent-data isomorphism.
  have hP :=
    localized_cover_descent_terminalCompatible_map (J := J)
      ((𝒰.pullback I.f).pullback T.hom) Q P φ.inv
      (fun K ↦
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f) (M := M)).symm
          (x K))
      hQ
  have hsections :
      (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
        (φ.inv.hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y)))
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := K.f) (M := M)).symm
            (x K))) = s := by
    funext K
    -- The inverse pointwise component map is precisely the inverse section equivalence.
    calc
      (φ.inv.hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y)))
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := K.f) (M := M)).symm
            (x K)) =
          (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
            (J := J) (U := U) 𝒰 D I T K).symm (x K) := by
            simpa [P, Q, M, φ, x, localized_cover_descent_toDescentData_over_section_eq] using
              localized_cover_descent_pullbackDatum_over_direct_to_component_iso_inv_apply
                (J := J) (U := U) 𝒰 D I T K (x K)
      _ = s K := by
        exact
          (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
            (J := J) (U := U) 𝒰 D I T K).left_inv (s K)
  exact localized_cover_descent_terminalCompatible_eq
    (J := J) (𝒱 := (𝒰.pullback I.f).pullback T.hom) (P := P) hsections hP

/-- Helper for Lemma 7.26.4: raw over-map glued families are equivalent to component-source
families over the normalized iterated pullback cover. -/
noncomputable def localized_cover_descent_glue_family_overMap_equiv_component_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T) ≃
      (∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
          (Opposite.op (Over.mk K.f)))) :=
  (localized_cover_descent_glue_family_overMap_equiv_direct_source
    (J := J) (U := U) 𝒰 D I T).trans
    (localized_cover_descent_glue_direct_family_equiv
      (J := J) (U := U) 𝒰 D I T)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: evaluating the raw over-map/component-source family equivalence is
the direct-source section comparison applied after the over-map/direct-source reindexing. -/
theorem localized_cover_descent_glue_family_overMap_equiv_component_source_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (localized_cover_descent_glue_family_overMap_equiv_component_source
      (J := J) (U := U) 𝒰 D I T s) K =
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T s) K) := by
  -- Unfold only the composed raw equivalence; the existing direct-family computation supplies the
  -- component-source value at `K`.
  simpa [localized_cover_descent_glue_family_overMap_equiv_component_source] using
    localized_cover_descent_glue_direct_family_equiv_apply
      (J := J) (U := U) 𝒰 D I T
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T) s) K

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting a forward-reindexed
direct-source section agrees heterogeneously with restricting the original over-map section at
the inverse `Cover.pullbackComp` index. -/
theorem localized_cover_descent_glue_overMap_to_direct_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    HEq
      (((localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I T).obj K).1.map
        (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g).op
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T s) K))
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
          ((Over.map I.f).obj T)).obj
            (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)).1.map
        (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g).op
        (s (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv))) := by
  refine localized_cover_descent_presheaf_map_heq_of_eqs
    (F := ((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1)
    (G := ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T)).obj (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)).1)
    ?hF rfl rfl
    (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g)
    (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g)
    (heq_of_eq rfl) ?hxy
  · cases T
    cases K
    simp only [localized_cover_descent_pullbackDatum,
      localized_cover_descent_pullbackDatum_over_direct_source,
      Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
      Functor.id_obj, Over.map_obj_left,
      Pseudofunctor.DescentData.pullFunctor_obj, Over.map_obj_hom, Functor.const_obj_obj,
      Pseudofunctor.DescentData.pullFunctorObj_obj,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
      op_id, Quiver.Hom.id_toLoc, heq_eq_eq]
    congr 2
    exact eq_of_heq (congr_arg_heq D.obj (by
      ext <;> simp [Category.assoc]))
  · exact localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
      (J := J) (U := U) 𝒰 D I T s K

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the forward reindexing normalizer
after both sides are put into the terminal-section type used by the descent overlap equation. -/
theorem localized_cover_descent_glue_overMap_to_direct_terminal_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    HEq
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := g)
          (M := (localized_cover_descent_pullbackDatum_over_direct_source
            (J := J) (U := U) 𝒰 D I T).obj K)).symm
        ((((localized_cover_descent_pullbackDatum_over_direct_source
            (J := J) (U := U) 𝒰 D I T).obj K).1.map
          (Over.homMk g).op)
          ((localized_cover_descent_glue_family_overMap_equiv_direct_source
            (J := J) (U := U) 𝒰 D I T s) K)))
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := g)
          (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
            ((Over.map I.f).obj T)).obj
              (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv))).symm
        ((((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
            ((Over.map I.f).obj T)).obj
              (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)).1.map
          (Over.homMk g).op)
          (s (K.map (Cover.pullbackComp 𝒰 T.hom I.f).inv)))) := by
  exact (cast_heq _ _).trans
    ((localized_cover_descent_glue_overMap_to_direct_map_heq
      (J := J) (U := U) 𝒰 D I T s K g).trans
      (cast_heq _ _).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting an inverse-reindexed
direct-source section agrees heterogeneously with restricting the original direct section at the
`Cover.pullbackComp` image. -/
theorem localized_cover_descent_glue_overMap_from_direct_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T)
    (K : (𝒰.pullback ((Over.map I.f).obj T).hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    HEq
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
          ((Over.map I.f).obj T)).obj K).1.map
        (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g).op
        (((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T).symm t) K))
      (((localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I T).obj
            (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)).1.map
        (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g).op
        (t (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom))) := by
  refine localized_cover_descent_presheaf_map_heq_of_eqs
    (F := ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T)).obj K).1)
    (G := ((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj
        (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)).1)
    ?hF rfl rfl
    (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g)
    (show Over.mk g ⟶ Over.mk (𝟙 K.Y) from Over.homMk g)
    (heq_of_eq rfl) ?hxy
  · cases T
    cases K
    simp only [localized_cover_descent_pullbackDatum,
      localized_cover_descent_pullbackDatum_over_direct_source,
      Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
      Over.map_obj_left, Functor.id_obj, Over.map_obj_hom, Functor.const_obj_obj,
      Pseudofunctor.DescentData.pullFunctor_obj,
      Pseudofunctor.DescentData.pullFunctorObj_obj,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
      op_id, Quiver.Hom.id_toLoc, heq_eq_eq]
    congr 2
    exact eq_of_heq (congr_arg_heq D.obj (by
      ext <;> simp [Category.assoc]))
  · exact localized_cover_descent_glue_family_overMap_equiv_direct_source_symm_apply_heq
      (J := J) (U := U) 𝒰 D I T t K

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the inverse reindexing normalizer
after both sides are put into the terminal-section type used by the descent overlap equation. -/
theorem localized_cover_descent_glue_overMap_from_direct_terminal_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : localized_cover_descent_glue_direct_family_over (J := J) (U := U) 𝒰 D I T)
    (K : (𝒰.pullback ((Over.map I.f).obj T).hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    HEq
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := g)
          (M := (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
            ((Over.map I.f).obj T)).obj K)).symm
        ((((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D
            ((Over.map I.f).obj T)).obj K).1.map
          (Over.homMk g).op)
          (((localized_cover_descent_glue_family_overMap_equiv_direct_source
            (J := J) (U := U) 𝒰 D I T).symm t) K)))
      (cast
        (localized_cover_descent_overMap_terminal_section_eq
          (J := J) (f := g)
          (M := (localized_cover_descent_pullbackDatum_over_direct_source
            (J := J) (U := U) 𝒰 D I T).obj
              (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom))).symm
        ((((localized_cover_descent_pullbackDatum_over_direct_source
            (J := J) (U := U) 𝒰 D I T).obj
              (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)).1.map
          (Over.homMk g).op)
          (t (K.map (Cover.pullbackComp 𝒰 T.hom I.f).hom)))) := by
  exact (cast_heq _ _).trans
    ((localized_cover_descent_glue_overMap_from_direct_map_heq
      (J := J) (U := U) 𝒰 D I T t K g).trans
      (cast_heq _ _).symm)

/-
omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_direct_pullFunctorObjHom_assoc_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {Tleft : C}
    (hom : Tleft ⟶ I.Y)
    (fst snd : ((𝒰.pullback I.f).pullback hom).Arrow)
    (r : fst.Relation snd) :
    HEq
      (((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op fst.Y }) r.g₁.op.toLoc).inv.toNatTrans.app
          (D.obj (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow)) ≫
        D.hom (r.g₁ ≫ fst.f ≫ hom ≫ I.f)
          (r.g₁ ≫ 𝟙 fst.Y) (r.g₂ ≫ 𝟙 snd.Y) (by simp [Category.assoc])
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm) ≫
        ((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op snd.Y }) r.g₂.op.toLoc).hom.toNatTrans.app
          (D.obj (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow)))
      (((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op fst.Y }) r.g₁.op.toLoc).inv.toNatTrans.app
          (D.obj (⟨fst.Y, fst.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
            𝒰.Arrow)) ≫
        D.hom (r.g₁ ≫ fst.f ≫ hom ≫ I.f)
          (r.g₁ ≫ 𝟙 fst.Y) (r.g₂ ≫ 𝟙 snd.Y) (by simp [Category.assoc])
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm) ≫
        ((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op snd.Y }) r.g₂.op.toLoc).hom.toNatTrans.app
          (D.obj (⟨snd.Y, snd.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
            𝒰.Arrow))) := by
  have hfst :
      (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow) =
      (⟨fst.Y, fst.f ≫ hom ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
        𝒰.Arrow) := by
    exact Cover.Arrow.ext rfl (heq_of_eq (by simp [Category.assoc, hgw]))
  have hsnd :
      (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow) =
      (⟨snd.Y, snd.f ≫ hom ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
        𝒰.Arrow) := by
    exact congrArg D.obj (Cover.Arrow.ext rfl (heq_of_eq (by simp [Category.assoc])))
  have hDfst : HEq
      (D.obj (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow))
      (D.obj (⟨fst.Y, fst.f ≫ hom ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
        𝒰.Arrow)) :=
    congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hfst
  have hDsnd : HEq
      (D.obj (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow))
      (D.obj (⟨snd.Y, snd.f ≫ hom ≫ I.f,
        by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
        𝒰.Arrow)) :=
    congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hsnd
  have hDfst_eq := eq_of_heq hDfst
  have hDsnd_eq := eq_of_heq hDsnd
  refine heq_comp ?_ ?_ ?_ ?_ ?_
  · exact congrArg
      (((J.pseudofunctorOver (Type w)).map r.g₁.op.toLoc).toFunctor.obj)
      (congrArg
        (((J.pseudofunctorOver (Type w)).map
          (𝟙 { as := Opposite.op fst.Y })).toFunctor.obj)
        hDfst_eq)
  · exact congrArg
      (((J.pseudofunctorOver (Type w)).map
        (𝟙 { as := Opposite.op fst.Y } ≫ r.g₁.op.toLoc)).toFunctor.obj)
      hDfst_eq
  · exact congrArg
      (((J.pseudofunctorOver (Type w)).map r.g₂.op.toLoc).toFunctor.obj)
      (congrArg
        (((J.pseudofunctorOver (Type w)).map
          (𝟙 { as := Opposite.op snd.Y })).toFunctor.obj)
        hDsnd_eq)
  · exact natTrans_app_heq_of_eq
      (A := Sheaf (J.over fst.Y) (Type w))
      (B := Sheaf (J.over r.Z) (Type w))
      (((J.pseudofunctorOver (Type w)).mapComp
        (𝟙 { as := Opposite.op fst.Y }) r.g₁.op.toLoc).inv.toNatTrans)
      hDfst_eq
  · refine heq_comp ?_ ?_ ?_ ?_ ?_
    · exact congrArg
        (((J.pseudofunctorOver (Type w)).map
          (𝟙 { as := Opposite.op fst.Y } ≫ r.g₁.op.toLoc)).toFunctor.obj)
        hDfst_eq
    · exact congrArg
        (((J.pseudofunctorOver (Type w)).map
          (𝟙 { as := Opposite.op snd.Y } ≫ r.g₂.op.toLoc)).toFunctor.obj)
        hDsnd_eq
    · exact congrArg
        (((J.pseudofunctorOver (Type w)).map r.g₂.op.toLoc).toFunctor.obj)
        (congrArg
          (((J.pseudofunctorOver (Type w)).map
            (𝟙 { as := Opposite.op snd.Y })).toFunctor.obj)
          hDsnd_eq)
    · exact localized_cover_descent_descent_hom_heq_of_arrow_eqs
        (J := J) (U := U) (Y := r.Z)
        (q := r.g₁ ≫ fst.f ≫ hom ≫ I.f)
        (I₁ := (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow))
        (I₁' := (⟨fst.Y, fst.f ≫ hom ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
          𝒰.Arrow))
        (I₂ := (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow))
        (I₂' := (⟨snd.Y, snd.f ≫ hom ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
          𝒰.Arrow))
        𝒰 D hfst hsnd
        (r.g₁ ≫ 𝟙 fst.Y) (r.g₁ ≫ 𝟙 fst.Y)
        (r.g₂ ≫ 𝟙 snd.Y) (r.g₂ ≫ 𝟙 snd.Y)
        (heq_of_eq rfl) (heq_of_eq rfl)
              (by simp)
        (by simp [Category.assoc])
        (by
          simpa [Category.assoc] using
            congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm)
        (by
          simpa [Category.assoc] using
            congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm)
    · exact natTrans_app_heq_of_eq
        (A := Sheaf (J.over snd.Y) (Type w))
        (B := Sheaf (J.over r.Z) (Type w))
        (((J.pseudofunctorOver (Type w)).mapComp
          (𝟙 { as := Opposite.op snd.Y }) r.g₂.op.toLoc).hom.toNatTrans)
        hDsnd_eq
-/

omit [UnivLE.{max u v, w}] in
theorem localized_cover_descent_pullFunctorObjHom_heq_of_arrow_eqs
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Z : C} {I₁ I₁' I₂ I₂' : 𝒰.Arrow}
    (hI₁ : I₁ = I₁') (hI₂ : I₂ = I₂')
    (g₁ : Z ⟶ I₁.Y) (g₁' : Z ⟶ I₁'.Y)
    (g₂ : Z ⟶ I₂.Y) (g₂' : Z ⟶ I₂'.Y)
    (hg₁ : HEq g₁ g₁') (hg₂ : HEq g₂ g₂')
    {q : Z ⟶ U}
    (h₁ : (g₁ ≫ 𝟙 I₁.Y) ≫ I₁.f = q)
    (h₁' : (g₁' ≫ 𝟙 I₁'.Y) ≫ I₁'.f = q)
    (h₂ : (g₂ ≫ 𝟙 I₂.Y) ≫ I₂.f = q)
    (h₂' : (g₂' ≫ 𝟙 I₂'.Y) ≫ I₂'.f = q) :
    HEq
      (((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op I₁.Y }) g₁.op.toLoc).inv.toNatTrans.app
          (D.obj I₁) ≫
        D.hom q (g₁ ≫ 𝟙 I₁.Y) (g₂ ≫ 𝟙 I₂.Y) h₁ h₂ ≫
        ((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op I₂.Y }) g₂.op.toLoc).hom.toNatTrans.app
          (D.obj I₂))
      (((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op I₁'.Y }) g₁'.op.toLoc).inv.toNatTrans.app
          (D.obj I₁') ≫
        D.hom q (g₁' ≫ 𝟙 I₁'.Y) (g₂' ≫ 𝟙 I₂'.Y) h₁' h₂' ≫
        ((J.pseudofunctorOver (Type w)).mapComp
            (𝟙 { as := Opposite.op I₂'.Y }) g₂'.op.toLoc).hom.toNatTrans.app
          (D.obj I₂')) := by
  subst hI₁
  subst hI₂
  have hg₁eq : g₁ = g₁' := eq_of_heq hg₁
  subst hg₁eq
  have hg₂eq : g₂ = g₂' := eq_of_heq hg₂
  subst hg₂eq
  cases proof_irrel h₁ h₁'
  cases proof_irrel h₂ h₂'
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: reindexing an over-map glued value
to the normalized direct-source family preserves the direct compatibility condition. -/
theorem localized_cover_descent_glue_overMap_to_direct_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T)) :
    localized_cover_descent_glue_direct_compatible (J := J) (U := U) 𝒰 D I T
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T) s.1) := by
  -- First read the source compatibility as terminal compatibility for the normalized direct
  -- pullback datum, then transport those terminal sections to the component sheaf.
  have hdirectSource :
      localized_cover_descent_terminalCompatible (J := J)
        ((𝒰.pullback I.f).pullback T.hom)
        (localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I T)
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T) s.1) := by
    intro Rdirect
    let Z : Over T.left := Over.mk (Rdirect.r.g₁ ≫ Rdirect.fst.f)
    let gi : Z ⟶ Over.mk Rdirect.fst.f := Over.homMk Rdirect.r.g₁
    let gj : Z ⟶ Over.mk Rdirect.snd.f :=
      Over.homMk Rdirect.r.g₂ (by
        simpa [Z] using Rdirect.r.w.symm)
    have hrel :
        gi ≫ (show Over.mk Rdirect.fst.f ⟶ Over.mk (𝟙 T.left) from
            Over.homMk Rdirect.fst.f) =
          gj ≫ (show Over.mk Rdirect.snd.f ⟶ Over.mk (𝟙 T.left) from
            Over.homMk Rdirect.snd.f) := by
      ext
      simpa [Z, gi, gj, Category.assoc] using Rdirect.r.w
    let R :=
      localized_cover_descent_overMap_cover_relation_of_direct
        (J := J) (U := U) 𝒰 I T Rdirect.fst Rdirect.snd gi gj hrel
    have hsource := s.2 R
    dsimp [localized_cover_descent_terminalCompatible,
      localized_cover_descent_glue_compatible] at hsource ⊢
    refine (eq_iff_eq_of_heq ?hleft ?hright).2 hsource
    · cases T
      cases Rdirect
      rename_i Tleft Tright hom fst snd r
      have hfst :
          (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow) =
          (⟨fst.Y, fst.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
            𝒰.Arrow) := by
        exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc fst.f hom I.f))
      have hsnd :
          (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow) =
          (⟨snd.Y, snd.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
            𝒰.Arrow) := by
        exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc snd.f hom I.f))
      simp only [Functor.id_obj]
      refine localized_cover_descent_sheaf_hom_app_heq ?hM ?hN _ _ ?hφ (heq_of_eq rfl) ?hxy
      · exact congrArg
          (((J.pseudofunctorOver (Type w)).map r.g₁.op.toLoc).toFunctor.obj)
          (congrArg
            (((J.pseudofunctorOver (Type w)).map
              (𝟙 { as := Opposite.op fst.Y })).toFunctor.obj)
            (eq_of_heq (congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hfst)))
      · exact congrArg
          (((J.pseudofunctorOver (Type w)).map r.g₂.op.toLoc).toFunctor.obj)
          (congrArg
            (((J.pseudofunctorOver (Type w)).map
              (𝟙 { as := Opposite.op snd.Y })).toFunctor.obj)
            (eq_of_heq (congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hsnd)))
      · exact localized_cover_descent_pullFunctorObjHom_heq_of_arrow_eqs
          (J := J) (U := U)
          (I₁ := (⟨fst.Y, (fst.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using fst.hf⟩ : 𝒰.Arrow))
          (I₁' := (⟨fst.Y, fst.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using fst.hf⟩ :
            𝒰.Arrow))
          (I₂ := (⟨snd.Y, (snd.f ≫ hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using snd.hf⟩ : 𝒰.Arrow))
          (I₂' := (⟨snd.Y, snd.f ≫ hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using snd.hf⟩ :
            𝒰.Arrow))
          𝒰 D hfst hsnd
          r.g₁ r.g₁ r.g₂ r.g₂
          (heq_of_eq rfl) (heq_of_eq rfl)
          (by
            change (r.g₁ ≫ 𝟙 fst.Y) ≫ ((fst.f ≫ hom) ≫ I.f) =
              (r.g₁ ≫ fst.f) ≫ hom ≫ I.f
            calc
              (r.g₁ ≫ 𝟙 fst.Y) ≫ ((fst.f ≫ hom) ≫ I.f) =
                  r.g₁ ≫ ((fst.f ≫ hom) ≫ I.f) := by
                    rw [Category.comp_id]
              _ =
                  r.g₁ ≫ (fst.f ≫ hom ≫ I.f) := by
                    rw [Category.assoc fst.f hom I.f]
              _ = (r.g₁ ≫ fst.f) ≫ hom ≫ I.f := by
                    rw [← Category.assoc])
          (by
            change (r.g₁ ≫ 𝟙 fst.Y) ≫ (fst.f ≫ hom ≫ I.f) =
              (r.g₁ ≫ fst.f) ≫ hom ≫ I.f
            calc
              (r.g₁ ≫ 𝟙 fst.Y) ≫ (fst.f ≫ hom ≫ I.f) =
                  r.g₁ ≫ (fst.f ≫ hom ≫ I.f) := by
                    rw [Category.comp_id]
              _ = (r.g₁ ≫ fst.f) ≫ hom ≫ I.f := by
                    rw [← Category.assoc])
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm)
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ hom ≫ I.f) r.w.symm)
      · simpa [R, Z, gi, gj,
          localized_cover_descent_overMap_cover_relation_of_direct,
          localized_cover_descent_overMap_relation_of_direct,
          localized_cover_descent_pullbackDatum,
          localized_cover_descent_pullbackDatum_over_direct_source,
          Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
          Pseudofunctor.DescentData.pullFunctorObjHom, Category.assoc] using
          localized_cover_descent_glue_overMap_to_direct_terminal_map_heq
            (J := J) (U := U) 𝒰 D I { left := Tleft, right := Tright, hom := hom }
            s.1 fst r.g₁
    · simpa [R, Z, gi, gj,
        localized_cover_descent_overMap_cover_relation_of_direct,
        localized_cover_descent_overMap_relation_of_direct,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullbackDatum_over_direct_source,
        Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
        Pseudofunctor.DescentData.pullFunctorObjHom, Category.assoc] using
        localized_cover_descent_glue_overMap_to_direct_terminal_map_heq
          (J := J) (U := U) 𝒰 D I T s.1 Rdirect.snd Rdirect.r.g₂
  exact localized_cover_descent_glue_direct_compatible_of_terminalCompatible
    (J := J) (U := U) 𝒰 D I T
    ((localized_cover_descent_glue_family_overMap_equiv_direct_source
      (J := J) (U := U) 𝒰 D I T) s.1) hdirectSource

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: a normalized direct-source
compatible value reindexes back to a compatible over-map glued family. -/
theorem localized_cover_descent_glue_overMap_from_direct_compatible
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : localized_cover_descent_glue_direct_source_over (J := J) (U := U) 𝒰 D I T) :
    localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T)
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).symm t.1) := by
  -- Reindex an over-map overlap to the normalized direct cover and use the component-side
  -- compatibility stored in `t`.
  let Q :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)).obj
      ((J.overMapPullback (Type w) T.hom).obj (D.obj I)))
  let x :
      ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.obj
          (Opposite.op (Over.mk K.f))) :=
    fun K ↦
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K (t.1 K)
  have hQ :
      localized_cover_descent_terminalCompatible (J := J)
        ((𝒰.pullback I.f).pullback T.hom)
        Q
        (fun K ↦
          cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := K.f)
              (M := (J.overMapPullback (Type w) T.hom).obj (D.obj I))).symm
            (x K)) := by
    exact localized_cover_descent_toDescentData_arrows_to_terminalCompatible
      (J := J)
      ((𝒰.pullback I.f).pullback T.hom)
      ((J.overMapPullback (Type w) T.hom).obj (D.obj I))
      x t.2
  let y :
      ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
        (((localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I T).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) :=
    fun K ↦
      (((localized_cover_descent_pullbackDatum_over_direct_to_component_iso
        (J := J) (U := U) 𝒰 D I T).inv.hom K).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f)
            (M := (J.overMapPullback (Type w) T.hom).obj (D.obj I))).symm
          (x K)))
  have hDirect0 :=
    localized_cover_descent_terminalCompatible_map (J := J)
      ((𝒰.pullback I.f).pullback T.hom)
      Q
      (localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I T)
      (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
        (J := J) (U := U) 𝒰 D I T).inv
      (fun K ↦
        cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := K.f)
            (M := (J.overMapPullback (Type w) T.hom).obj (D.obj I))).symm
          (x K))
      hQ
  have hfamily : y = t.1 := by
    funext K
    let e :=
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K
    -- The inverse component map is the inverse of the terminal-section equivalence.
    calc
      y K = e.symm (x K) := by
        simpa [e, x, y, localized_cover_descent_toDescentData_over_section_eq] using
          localized_cover_descent_pullbackDatum_over_direct_to_component_iso_inv_apply_terminal
            (J := J) (U := U) 𝒰 D I T K (x K)
      _ = t.1 K := by
        simpa [e, x] using Equiv.symm_apply_apply e (t.1 K)
  have hDirect :
      localized_cover_descent_terminalCompatible (J := J)
        ((𝒰.pullback I.f).pullback T.hom)
        (localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I T)
        t.1 :=
    localized_cover_descent_terminalCompatible_eq
      (J := J) ((𝒰.pullback I.f).pullback T.hom)
      (localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I T)
      hfamily hDirect0
  refine (localized_cover_descent_terminalCompatible_pullbackDatum_iff
    (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T)
    ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).symm t.1)).1 ?_
  intro R
  let Rdirect :=
    localized_cover_descent_direct_cover_relation_of_overMap
      (J := J) (U := U) 𝒰 I T R
  have ht := hDirect Rdirect
  dsimp [localized_cover_descent_terminalCompatible] at ht ⊢
  refine (eq_iff_eq_of_heq ?hleft ?hright).1 ht
  · have hfst :
        (⟨R.fst.Y, (R.fst.f ≫ T.hom) ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback] using R.fst.hf⟩ : 𝒰.Arrow) =
        (⟨R.fst.Y, R.fst.f ≫ T.hom ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using R.fst.hf⟩ :
          𝒰.Arrow) := by
      exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc R.fst.f T.hom I.f))
    have hsnd :
        (⟨R.snd.Y, (R.snd.f ≫ T.hom) ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback] using R.snd.hf⟩ : 𝒰.Arrow) =
        (⟨R.snd.Y, R.snd.f ≫ T.hom ≫ I.f,
          by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using R.snd.hf⟩ :
          𝒰.Arrow) := by
      exact Cover.Arrow.ext rfl (heq_of_eq (Category.assoc R.snd.f T.hom I.f))
    refine localized_cover_descent_sheaf_hom_app_heq ?hM ?hN _ _ ?hφ
      (heq_of_eq rfl) ?hxy
    · exact congrArg
        (((J.pseudofunctorOver (Type w)).map R.r.g₁.op.toLoc).toFunctor.obj)
        (congrArg
          (((J.pseudofunctorOver (Type w)).map
            (𝟙 { as := Opposite.op R.fst.Y })).toFunctor.obj)
          (eq_of_heq (congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hfst)))
    · exact congrArg
        (((J.pseudofunctorOver (Type w)).map R.r.g₂.op.toLoc).toFunctor.obj)
        (congrArg
          (((J.pseudofunctorOver (Type w)).map
            (𝟙 { as := Opposite.op R.snd.Y })).toFunctor.obj)
          (eq_of_heq (congr_arg_heq (fun K : 𝒰.Arrow => D.obj K) hsnd)))
    · simpa only [Rdirect,
        localized_cover_descent_direct_cover_relation_of_overMap,
        localized_cover_descent_direct_relation_of_overMap,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullbackDatum_over_direct_source,
        Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
        Pseudofunctor.DescentData.pullFunctorObjHom,
        Pseudofunctor.DescentData.pullFunctorObj_hom,
        Pseudofunctor.DescentData.pullFunctorObj,
        Pseudofunctor.DescentData.pullFunctor,
        Category.assoc] using
        (localized_cover_descent_pullFunctorObjHom_heq_of_arrow_eqs
          (J := J) (U := U)
          (I₁ := (⟨R.fst.Y, (R.fst.f ≫ T.hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using R.fst.hf⟩ : 𝒰.Arrow))
          (I₁' := (⟨R.fst.Y, R.fst.f ≫ T.hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using R.fst.hf⟩ :
            𝒰.Arrow))
          (I₂ := (⟨R.snd.Y, (R.snd.f ≫ T.hom) ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback] using R.snd.hf⟩ : 𝒰.Arrow))
          (I₂' := (⟨R.snd.Y, R.snd.f ≫ T.hom ≫ I.f,
            by simpa [GrothendieckTopology.Cover.coe_pullback, Category.assoc] using R.snd.hf⟩ :
            𝒰.Arrow))
          (q := R.r.g₁ ≫ R.fst.f ≫ T.hom ≫ I.f) 𝒰 D hfst hsnd
          R.r.g₁ R.r.g₁ R.r.g₂ R.r.g₂ (heq_of_eq rfl) (heq_of_eq rfl)
          (by
            change ((R.r.g₁ ≫ 𝟙 R.fst.Y) ≫ ((R.fst.f ≫ T.hom) ≫ I.f)) =
              R.r.g₁ ≫ R.fst.f ≫ T.hom ≫ I.f
            calc
              (R.r.g₁ ≫ 𝟙 R.fst.Y) ≫ ((R.fst.f ≫ T.hom) ≫ I.f) =
                  R.r.g₁ ≫ ((R.fst.f ≫ T.hom) ≫ I.f) := by
                    rw [Category.comp_id]
              _ =
                  R.r.g₁ ≫ (R.fst.f ≫ T.hom ≫ I.f) := by
                    rw [Category.assoc R.fst.f T.hom I.f]
              _ = R.r.g₁ ≫ R.fst.f ≫ T.hom ≫ I.f := by
                    rfl)
          (by
            change ((R.r.g₁ ≫ 𝟙 R.fst.Y) ≫ (R.fst.f ≫ T.hom ≫ I.f)) =
              R.r.g₁ ≫ R.fst.f ≫ T.hom ≫ I.f
            calc
              (R.r.g₁ ≫ 𝟙 R.fst.Y) ≫ (R.fst.f ≫ T.hom ≫ I.f) =
                  R.r.g₁ ≫ (R.fst.f ≫ T.hom ≫ I.f) := by
                    rw [Category.comp_id]
              _ = R.r.g₁ ≫ R.fst.f ≫ T.hom ≫ I.f := by
                    rfl)
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ T.hom ≫ I.f) R.r.w.symm)
          (by
            simpa [Category.assoc] using
              congrArg (fun e => e ≫ T.hom ≫ I.f) R.r.w.symm))
    · simpa only [Rdirect,
        localized_cover_descent_direct_cover_relation_of_overMap,
        localized_cover_descent_direct_relation_of_overMap,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullbackDatum_over_direct_source,
        Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
        Category.assoc] using
        (localized_cover_descent_glue_overMap_from_direct_terminal_map_heq
          (J := J) (U := U) 𝒰 D I T t.1 R.fst R.r.g₁).symm
  · simpa only [Rdirect,
      localized_cover_descent_direct_cover_relation_of_overMap,
      localized_cover_descent_direct_relation_of_overMap,
      localized_cover_descent_pullbackDatum,
      localized_cover_descent_pullbackDatum_over_direct_source,
      Cover.pullbackComp, Cover.Arrow.map, Cover.Arrow.base,
      Category.assoc] using
      (localized_cover_descent_glue_overMap_from_direct_terminal_map_heq
        (J := J) (U := U) 𝒰 D I T t.1 R.snd R.r.g₂).symm

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: source-compatible over-map families become compatible
component-source families after the raw over-map/component-source family equivalence. -/
theorem localized_cover_descent_glue_component_source_compatible_of_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (hs : localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T) s) :
    Presieve.Arrows.Compatible
      (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
      (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
      (localized_cover_descent_glue_family_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I T s) := by
  have hdirect :=
    localized_cover_descent_glue_overMap_to_direct_compatible
      (J := J) (U := U) 𝒰 D I T ⟨s, hs⟩
  simpa [localized_cover_descent_glue_family_overMap_equiv_component_source,
    localized_cover_descent_glue_direct_compatible] using hdirect

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: component-source compatibility for the raw transported family
recovers the original over-map source compatibility relation-by-relation. -/
theorem localized_cover_descent_glue_source_compatible_of_component_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_family (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (hs :
      Presieve.Arrows.Compatible
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
        (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f))
        (localized_cover_descent_glue_family_overMap_equiv_component_source
          (J := J) (U := U) 𝒰 D I T s)) :
    localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T) s := by
  have hdirect :
      localized_cover_descent_glue_direct_compatible (J := J) (U := U) 𝒰 D I T
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T) s) := by
    simpa [localized_cover_descent_glue_family_overMap_equiv_component_source,
      localized_cover_descent_glue_direct_compatible] using hs
  let t : localized_cover_descent_glue_direct_source_over (J := J) (U := U) 𝒰 D I T :=
    ⟨(localized_cover_descent_glue_family_overMap_equiv_direct_source
      (J := J) (U := U) 𝒰 D I T) s, hdirect⟩
  have hcompat :=
    localized_cover_descent_glue_overMap_from_direct_compatible
      (J := J) (U := U) 𝒰 D I T t
  have hfamily :
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).symm t.1) = s :=
    (localized_cover_descent_glue_family_overMap_equiv_direct_source
      (J := J) (U := U) 𝒰 D I T).left_inv s
  exact (congrArg
    (localized_cover_descent_glue_compatible (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T)) hfamily).mp hcompat

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: over-map glued values are equivalent
to the normalized direct-source compatible families used by the component comparison. -/
noncomputable def localized_cover_descent_glue_value_overMap_equiv_direct_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T) ≃
      localized_cover_descent_glue_direct_source_over (J := J) (U := U) 𝒰 D I T where
  toFun s :=
    ⟨localized_cover_descent_glue_family_overMap_equiv_direct_source
      (J := J) (U := U) 𝒰 D I T s.1,
      localized_cover_descent_glue_overMap_to_direct_compatible
        (J := J) (U := U) 𝒰 D I T s⟩
  invFun t :=
    ⟨(localized_cover_descent_glue_family_overMap_equiv_direct_source
      (J := J) (U := U) 𝒰 D I T).symm t.1,
      localized_cover_descent_glue_overMap_from_direct_compatible
        (J := J) (U := U) 𝒰 D I T t⟩
  left_inv s := by
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).left_inv s.1) K
  right_inv t := by
    apply Subtype.ext
    funext K
    exact congrFun
      ((localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I T).right_inv t.1) K

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: over-map glued values are equivalent
to the component-source compatible families, using the direct-source normal form as the bridge. -/
noncomputable def localized_cover_descent_glue_value_overMap_equiv_component_source
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D ((Over.map I.f).obj T) ≃
      localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T :=
  (localized_cover_descent_glue_value_overMap_equiv_direct_source
    (J := J) (U := U) 𝒰 D I T).trans
    (localized_cover_descent_glue_restrict_obj_equiv_over
      (J := J) (U := U) 𝒰 D I T)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: projecting the value-level
over-map/component-source equivalence is the raw family-level equivalence. -/
theorem localized_cover_descent_glue_value_overMap_equiv_component_source_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    (((((localized_cover_descent_glue_value_overMap_equiv_component_source
      (J := J) (U := U) 𝒰 D I T) s) :
        localized_cover_descent_glue_component_source_over
          (J := J) (U := U) 𝒰 D I T) :
        ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
          ((((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1).obj
            (Opposite.op (Over.mk K.f)))) K) =
      (localized_cover_descent_glue_family_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I T s.1) K := by
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the component-source gluing
equivalence restricts to the compatible family it glues. -/
theorem localized_cover_descent_glue_component_equiv_over_valid_glue
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map (Over.homMk K.f).op
      (cast (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := T.hom) (M := D.obj I)).symm
        (localized_cover_descent_glue_component_equiv_over (J := J) (U := U) 𝒰 D I T s)) =
    s.1 K := by
  let P := (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1)
  let π :=
    fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦
      (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from
        Over.homMk K.f (Category.comp_id K.f))
  have hsheaf :
      Presieve.IsSheafFor P
        (Presieve.ofArrows
          (fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ Over.mk K.f) π) := by
    rw [Presieve.isSheafFor_iff_generate]
    simpa [P, π, localized_cover_descent_terminal_cover] using
      (Presheaf.IsSheaf.isSheafFor
        (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).2)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).1)
        ((localized_cover_descent_terminal_cover
          (J := J) (U := T.left) ((𝒰.pullback I.f).pullback T.hom)).condition))
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp hsheaf
  let e := Equiv.ofBijective (Presieve.Arrows.toCompatible P π) hbij
  have h : P.map (π K).op (e.symm s) = s.1 K :=
    congrFun (congrArg Subtype.val (e.right_inv s)) K
  unfold localized_cover_descent_glue_component_equiv_over
  unfold localized_cover_descent_component_sections_equiv_over
  simp only [Equiv.trans_apply, Equiv.cast_apply]
  change P.map (π K).op (cast _ (cast _ (e.symm s))) = s.1 K
  -- The two terminal-section casts only change the dependent type of the glued section, so the
  -- sheaf restriction agrees with the uncast compatible-family projection.
  convert h using 1
  exact congrArg (P.map (π K).op)
    (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the valid-glue computation is unchanged when the terminal
restriction arrow is written with an explicitly named proof. -/
theorem localized_cover_descent_glue_component_equiv_over_valid_glue_homMk
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {hK : K.f ≫ 𝟙 T.left = K.f} :
    ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
      (Over.homMk K.f hK).op
      (cast (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := T.hom) (M := D.obj I)).symm
        (localized_cover_descent_glue_component_equiv_over (J := J) (U := U) 𝒰 D I T s)) =
    s.1 K := by
  let P := ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1
  let z :=
    cast (localized_cover_descent_overMap_terminal_section_eq
      (J := J) (f := T.hom) (M := D.obj I)).symm
      (localized_cover_descent_glue_component_equiv_over (J := J) (U := U) 𝒰 D I T s)
  have hπ :
      (Over.homMk K.f hK :
        Over.mk K.f ⟶ Over.mk (𝟙 T.left)) =
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f) := by
    apply Over.OverMorphism.ext
    rfl
  have hπop :
      (Over.homMk K.f hK :
        Over.mk K.f ⟶ Over.mk (𝟙 T.left)).op =
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op :=
    congrArg Quiver.Hom.op hπ
  have hmap :
      P.map
        (Over.homMk K.f hK :
          Over.mk K.f ⟶ Over.mk (𝟙 T.left)).op =
      P.map
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op := by
    rw [hπop]
  calc
    P.map
        (Over.homMk K.f hK :
          Over.mk K.f ⟶ Over.mk (𝟙 T.left)).op z =
      P.map
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op z := by
        rw [hmap]
    _ = s.1 K :=
        localized_cover_descent_glue_component_equiv_over_valid_glue
          (J := J) (U := U) 𝒰 D I T s K

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the valid-glue computation in the unfolded
`overMapPullback` form used by component restriction goals. -/
theorem localized_cover_descent_glue_component_equiv_over_valid_glue_unfolded
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (s : localized_cover_descent_glue_component_source_over (J := J) (U := U) 𝒰 D I T)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    {hK : K.f ≫ 𝟙 T.left = K.f} :
    (D.obj I).1.map
      (((Over.map T.hom).map
        (Over.homMk K.f hK :
          Over.mk K.f ⟶ Over.mk (𝟙 T.left))).op.unop).op
      (cast (localized_cover_descent_overMap_terminal_section_eq
        (J := J) (f := T.hom) (M := D.obj I)).symm
        (localized_cover_descent_glue_component_equiv_over (J := J) (U := U) 𝒰 D I T s)) =
    s.1 K := by
  simpa [GrothendieckTopology.overMapPullback] using
    localized_cover_descent_glue_component_equiv_over_valid_glue_homMk
      (J := J) (U := U) 𝒰 D I T s K (hK := hK)

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the inverse of the component-side
gluing equivalence is the compatible family of ordinary restrictions of the given section. -/
theorem localized_cover_descent_glue_component_equiv_over_symm_apply
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (t : (D.obj I).1.obj (Opposite.op T))
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow) :
    ((localized_cover_descent_glue_component_equiv_over
      (J := J) (U := U) 𝒰 D I T).symm t).1 K =
      (((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
        (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op)
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := T.hom) (M := D.obj I)).symm
          t) := by
  unfold localized_cover_descent_glue_component_equiv_over
  unfold localized_cover_descent_component_sections_equiv_over
  rw [Equiv.symm_trans_apply]
  rw [Equiv.symm_symm_apply]
  rw [equiv_cast_symm_apply]
  rw [Equiv.ofBijective_apply]
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: two component sections over a slice
object are equal once their restrictions to every pulled-back cover member agree. -/
theorem localized_cover_descent_glue_component_equiv_over_ext
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    {x y : (D.obj I).1.obj (Opposite.op T)}
    (h : ∀ K : ((𝒰.pullback I.f).pullback T.hom).Arrow,
      ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T.hom) (M := D.obj I)).symm x) =
        ((J.overMapPullback (Type w) T.hom).obj (D.obj I)).1.map
          (show Over.mk K.f ⟶ Over.mk (𝟙 T.left) from Over.homMk K.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T.hom) (M := D.obj I)).symm y)) :
    x = y := by
  -- Pull both sections back through the component gluing equivalence; the supplied pointwise
  -- restriction equalities are exactly the resulting equality of compatible families.
  apply (localized_cover_descent_glue_component_equiv_over
    (J := J) (U := U) 𝒰 D I T).symm.injective
  ext K
  rw [localized_cover_descent_glue_component_equiv_over_symm_apply]
  rw [localized_cover_descent_glue_component_equiv_over_symm_apply]
  exact h K

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: reindexing a pullback-cover arrow along a slice morphism gives the
same object after mapping both sides to the slice over the cover member. -/
theorem localized_cover_descent_pullback_arrow_map_overMap_obj_eq
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow) :
    (Over.map T₂.hom).obj (Over.mk K.f) =
      (Over.map T₁.hom).obj
        (Over.mk
          (localized_cover_descent_pullback_arrow_map
            (J := J) (U := I.Y) (𝒰.pullback I.f) g K).f) := by
  -- Expanding the transported pullback arrow reduces the slice-object equality to the defining
  -- commutative triangle for `g`.
  cases T₁
  cases T₂
  rcases K with ⟨Y, f, hf⟩
  apply over_mk_hext (𝒞 := C) (B := I.Y) (hY := rfl)
  exact heq_of_eq (by
    simpa [localized_cover_descent_pullback_arrow_map, Category.assoc] using
      (congrArg (fun h ↦ f ≫ h) (Over.w g)).symm)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: pulling a reindexed arrow through the inverse pullback-composition
cover agrees with reindexing after pulling through the corresponding inverse cover. -/
theorem localized_cover_descent_pullbackComp_inv_arrow_map_eq
    (𝒰 : J.Cover U)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow) :
    localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰
        ((Over.map I.f).map g)
        (K.map (Cover.pullbackComp 𝒰 T₂.hom I.f).inv) =
      (localized_cover_descent_pullback_arrow_map
        (J := J) (U := I.Y) (𝒰.pullback I.f) g K).map
          (Cover.pullbackComp 𝒰 T₁.hom I.f).inv := by
  -- Expand the cover-arrow maps; both sides are the same arrow over `U` by associativity.
  cases T₁
  cases T₂
  rcases K with ⟨Y, f, hf⟩
  apply Cover.Arrow.ext rfl
  exact heq_of_eq rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the inverse direct-source normalization component is an identity
transport on terminal sections, up to heterogeneous equality. -/
theorem localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T).inv.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  simpa [localized_cover_descent_pullbackDatum_over_direct_source_iso,
    localized_cover_descent_pullbackDatum, localized_cover_descent_pullbackDatum_over_direct_source,
    Cover.Arrow.base, Pseudofunctor.DescentData.pullFunctorObjHom, Category.assoc] using
    (pf_mapComp'_hom_component_apply_heq
      (J := J)
      ((𝟙 K.Y).op.toLoc)
      ((𝟙 K.Y).op.toLoc)
      ((𝟙 K.Y).op.toLoc)
      (by
        rw [op_id]
        rw [Quiver.Hom.id_toLoc]
        rw [Category.id_comp])
      (D.obj K.base.base)
      (Opposite.op (Over.mk (𝟙 K.Y))) x)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the `toDescentData` comparison after a pullback acts as the
identity on terminal sections, up to heterogeneous equality. -/
theorem localized_cover_descent_toDescentDataCompPullFunctorIso_hom_app_heq
    {S : C}
    (𝒱 : J.Cover S)
    (M : Sheaf (J.over S) (Type w))
    (T : Over S)
    (K : (𝒱.pullback T.hom).Arrow)
    (x : ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun I : 𝒱.Arrow ↦ I.f)
      (p := T.hom)
      (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).obj
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒱.Arrow ↦ I.f)).obj M)).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      ((((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun I : 𝒱.Arrow ↦ I.f)
        (p := T.hom)
        (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).hom.app M).hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      x := by
  let X : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
  let A :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      (T.hom.op.toLoc ≫ K.f.op.toLoc) (𝟙 K.Y).op.toLoc
      (T.hom.op.toLoc ≫ K.f.op.toLoc)
      (by
        rw [op_id]
        rw [Quiver.Hom.id_toLoc]
        rw [Category.comp_id])).inv.toNatTrans.app M
  let B :=
    ((J.pseudofunctorOver (Type w)).mapComp
      T.hom.op.toLoc K.f.op.toLoc).hom.toNatTrans.app M
  have hA : HEq (A.hom.app X x) x := by
    simpa [A, X, Pseudofunctor.toDescentData] using
      (pf_mapComp'_inv_component_apply_heq
        (J := J)
        (T.hom.op.toLoc ≫ K.f.op.toLoc)
        ((𝟙 K.Y).op.toLoc)
        (T.hom.op.toLoc ≫ K.f.op.toLoc)
        (by
          rw [op_id]
          rw [Quiver.Hom.id_toLoc]
          rw [Category.comp_id])
        M X x)
  have hB : HEq (B.hom.app X (A.hom.app X x)) (A.hom.app X x) := by
    simpa [B, X, Pseudofunctor.toDescentData] using
      (pf_mapComp_hom_component_apply_heq
        (J := J)
        (f := T.hom.op.toLoc)
        (g' := K.f.op.toLoc)
        M X (A.hom.app X x))
  simpa [A, B, X, Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso,
    Pseudofunctor.toDescentData, Pseudofunctor.isoMapOfCommSq,
    Pseudofunctor.mapComp'_eq_mapComp, Category.assoc] using hB.trans hA

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the `I`-level pullback-datum comparison is the descent transition
from the pullback cover member to `I` on terminal sections. -/
theorem localized_cover_descent_pullbackDatum_component_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow)
    (x : (((localized_cover_descent_pullbackDatum
      (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (((localized_cover_descent_pullbackDatum_toDescentData_obj
        (J := J) (U := U) 𝒰 D I).hom.hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      ((D.hom (K.f ≫ I.f)
          (i₁ := K.base) (i₂ := I)
          (𝟙 K.Y) K.f
          (by simp [GrothendieckTopology.Cover.Arrow.base])
          rfl).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y))) x) := by
  change
    HEq
      ((((localized_cover_descent_pullbackDatum_reindex_iso
        (J := J) (U := U) 𝒰 D I).hom ≫
          (localized_cover_descent_componentPullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom).hom K).hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
      ((D.hom (K.f ≫ I.f)
          (i₁ := K.base) (i₂ := I)
          (𝟙 K.Y) K.f
          (by simp [GrothendieckTopology.Cover.Arrow.base])
          rfl).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y))) x)
  rw [Pseudofunctor.DescentData.comp_hom]
  simp only [Over.mk_left, Functor.id_obj, Over.mk_hom,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, localized_cover_descent_pullbackDatum,
    Pseudofunctor.DescentData.pullFunctor_obj, Pseudofunctor.DescentData.pullFunctorObj_obj,
    Cover.Arrow.base_Y, op_id, Quiver.Hom.id_toLoc,
    localized_cover_descent_componentPullbackDatum, localized_cover_descent_pullbackDatum_reindex_iso,
    Pseudofunctor.DescentData.pullFunctorIso, Pseudofunctor.DescentData.isoMk,
    Pseudofunctor.DescentData.iso, Cover.Arrow.base_f, Category.id_comp,
    NatIso.ofComponents.app, localized_cover_descent_componentPullbackDatum_toDescentData_obj,
    Iso.refl_hom, Iso.refl_inv, heq_eq_eq]
  let φ :=
    D.hom (K.f ≫ I.f)
      (i₁ := K.base) (i₂ := I)
      (𝟙 K.Y) K.f
      (by simp [GrothendieckTopology.Cover.Arrow.base])
      rfl
  change (φ ≫ 𝟙 _).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) x =
    φ.hom.app (Opposite.op (Over.mk (𝟙 K.Y))) x
  rw [Category.comp_id]

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: pulling a descent-data morphism through the pullback functor and
evaluating at a terminal section is the same as evaluating the original component at the identity
over-map. -/
theorem localized_cover_descent_pullFunctor_map_id_app_heq
    {S : C}
    (𝒱 : J.Cover S)
    {D₁ D₂ : (J.pseudofunctorOver (Type w)).DescentData
      (fun I : 𝒱.Arrow ↦ I.f)}
    (φ : D₁ ⟶ D₂)
    (T : Over S)
    (K : (𝒱.pullback T.hom).Arrow)
    (x : ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun I : 𝒱.Arrow ↦ I.f)
      (p := T.hom)
      (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).obj
        D₁).obj K).1.obj (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      ((((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun I : 𝒱.Arrow ↦ I.f)
        (p := T.hom)
        (f' := fun K : (𝒱.pullback T.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := S) 𝒱 T)).map
          φ).hom K).hom.app (Opposite.op (Over.mk (𝟙 K.Y))) x)
        ((φ.hom K.base).hom.app
          (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)))) x) := by
    simp [Pseudofunctor.DescentData.pullFunctor]

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the direct-source terminal-section comparison with the pulled-back
component sheaf is the descent transition from the direct source to the fixed component. -/
theorem localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y)
    (K : ((𝒰.pullback I.f).pullback T.hom).Arrow)
    (x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))) :
    HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K x)
      ((D.hom (K.f ≫ T.hom ≫ I.f)
          (i₁ := K.base.base) (i₂ := I)
          (𝟙 K.Y) (K.f ≫ T.hom)
          (by simp [GrothendieckTopology.Cover.Arrow.base, Category.assoc])
          (Category.assoc K.f T.hom I.f)).hom.app
        (Opposite.op (Over.mk (𝟙 K.Y))) x) := by
  let X : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
  let φ :=
    (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T).hom.hom K
  let η :=
    ((localized_cover_descent_pullbackDatum_over_direct_source_iso
      (J := J) (U := U) 𝒰 D I T).inv.hom K)
  let θ :=
    (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).hom
  let μ :=
    ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
        (𝒰.pullback I.f) T)).map θ).hom K
  let ν :=
    ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
      (J.pseudofunctorOver (Type w))
      (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (p := T.hom)
      (f' := fun K : ((𝒰.pullback I.f).pullback T.hom).Arrow ↦ K.f)
      (α := fun K ↦ K.base)
      (p' := fun _ ↦ 𝟙 _)
      (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
        (𝒰.pullback I.f) T)).hom.app (D.obj I)).hom K
  let ξ : (((localized_cover_descent_pullbackDatum_over_source
      (J := J) (U := U) 𝒰 D I T).obj K).1.obj X) :=
    η.hom.app X x
  have hη : HEq ξ x := by
    simpa [η, ξ, X] using
      localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
        (J := J) (U := U) 𝒰 D I T K x
  have hμ : HEq
      (μ.hom.app X ξ)
      ((θ.hom K.base).hom.app
        (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)))) ξ) := by
    dsimp [μ, θ, X]
    rfl
  have hX :
      HEq (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)))) X := by
    have hObj :
        (Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)) = Over.mk (𝟙 K.Y) := by
      change Over.mk ((𝟙 K.Y) ≫ 𝟙 K.Y) = Over.mk (𝟙 K.Y)
      rw [Category.comp_id]
    exact heq_of_eq (congrArg Opposite.op hObj)
  have hθinput : HEq
      ((θ.hom K.base).hom.app
        (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y)))) ξ)
      ((θ.hom K.base).hom.app X x) := by
    exact localized_cover_descent_sheaf_hom_app_heq
      (J := J) (hM := rfl) (hN := rfl)
      _ _ (heq_of_eq rfl) hX hη
  have hθdirect : HEq
      ((θ.hom K.base).hom.app X x)
      ((D.hom (K.f ≫ T.hom ≫ I.f)
          (i₁ := K.base.base) (i₂ := I)
          (𝟙 K.Y) (K.f ≫ T.hom)
          (by simp [GrothendieckTopology.Cover.Arrow.base, Category.assoc])
          (Category.assoc K.f T.hom I.f)).hom.app X x) := by
    simpa [θ, X, GrothendieckTopology.Cover.Arrow.base, Category.assoc] using
      localized_cover_descent_pullbackDatum_component_app_heq
        (J := J) (U := U) 𝒰 D I K.base x
  have hν : HEq
      (ν.hom.app X (μ.hom.app X ξ))
      (μ.hom.app X ξ) := by
    simpa [ν, X] using
      localized_cover_descent_toDescentDataCompPullFunctorIso_hom_app_heq
        (J := J) (𝒱 := 𝒰.pullback I.f) (M := D.obj I) T K
        (μ.hom.app X ξ)
  have hφ : HEq
      (φ.hom.app X x)
      ((D.hom (K.f ≫ T.hom ≫ I.f)
          (i₁ := K.base.base) (i₂ := I)
          (𝟙 K.Y) (K.f ≫ T.hom)
          (by simp [GrothendieckTopology.Cover.Arrow.base, Category.assoc])
          (Category.assoc K.f T.hom I.f)).hom.app X x) := by
    -- Expand the direct-to-component comparison only to its named structural factors, then
    -- compose the three pointwise HEq computations above.
    change HEq
      (ν.hom.app X (μ.hom.app X ξ))
      ((D.hom (K.f ≫ T.hom ≫ I.f)
          (i₁ := K.base.base) (i₂ := I)
          (𝟙 K.Y) (K.f ≫ T.hom)
          (by simp [GrothendieckTopology.Cover.Arrow.base, Category.assoc])
          (Category.assoc K.f T.hom I.f)).hom.app X x)
    exact hν.trans (hμ.trans (hθinput.trans hθdirect))
  have hsection : HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T K x)
      (φ.hom.app X x) := by
    have h :=
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
        (J := J) (U := U) 𝒰 D I T K x
    exact (heq_of_eq h).symm.trans (cast_heq _ _)
  exact hsection.trans hφ

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the direct-source terminal-section comparison with the pulled-back
component sheaf is stable under reindexing a pullback-cover arrow along a slice morphism. -/
theorem localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_arrow_map_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow)
    {x : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T₂).obj K).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))}
    {y : (((localized_cover_descent_pullbackDatum_over_direct_source
      (J := J) (U := U) 𝒰 D I T₁).obj
        (localized_cover_descent_pullback_arrow_map
          (J := J) (U := I.Y) (𝒰.pullback I.f) g K)).1.obj
        (Opposite.op (Over.mk (𝟙 K.Y))))}
    (hxy : HEq x y) :
    HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₂ K x)
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₁
        (localized_cover_descent_pullback_arrow_map
          (J := J) (U := I.Y) (𝒰.pullback I.f) g K) y) := by
  cases T₁
  cases T₂
  rename_i T₁Y T₁pt hT₁ T₂Y T₂pt hT₂
  cases T₁pt
  cases T₂pt
  rename_i a₁ a₂
  cases a₁
  cases a₂
  obtain ⟨gleft, hg, rfl⟩ := Over.homMk_surjective g
  change T₁Y ⟶ I.Y at hT₁
  change T₂Y ⟶ I.Y at hT₂
  change T₂Y ⟶ T₁Y at gleft
  have hg' : hT₂ = gleft ≫ hT₁ := by
    simpa using hg.symm
  revert K x y hxy
  cases hg'
  let T₂o : Over I.Y := { left := T₂Y, right := { as := PUnit.unit }, hom := gleft ≫ hT₁ }
  let T₁o : Over I.Y := { left := T₁Y, right := { as := PUnit.unit }, hom := hT₁ }
  let g' : T₂o ⟶ T₁o := Over.homMk gleft (by simp [T₁o, T₂o])
  intro K x y hxy
  let K' :=
    localized_cover_descent_pullback_arrow_map
      (J := J) (U := I.Y) (𝒰.pullback I.f) g' K
  change
    HEq
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₂o K x)
      (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I T₁o K' y)
  have hsourceType :
      (((localized_cover_descent_pullbackDatum_over_direct_source
        (J := J) (U := U) 𝒰 D I
        T₂o).obj K).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) =
        (((localized_cover_descent_pullbackDatum_over_direct_source
          (J := J) (U := U) 𝒰 D I
          T₁o).obj K').1.obj
            (Opposite.op (Over.mk (𝟙 K'.Y)))) := by
    simp only [K', g', T₁o, T₂o,
      localized_cover_descent_pullbackDatum_over_direct_source,
      localized_cover_descent_pullback_arrow_map, Cover.Arrow.base, Category.assoc,
      Functor.id_obj, Over.map_obj_left,
      Pseudofunctor.DescentData.pullFunctor_obj, Over.map_obj_hom, Functor.const_obj_obj,
      Pseudofunctor.DescentData.pullFunctorObj_obj,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
      op_id, Quiver.Hom.id_toLoc,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      LocallyDiscrete.id_as, unop_id]
    congr 2
    exact eq_of_heq (congr_arg_heq D.obj (by
      ext <;> simp [Category.assoc]))
  have htargetType :
      ((((J.overMapPullback (Type w)
        T₂o.hom).obj
          (D.obj I)).1).obj (Opposite.op (Over.mk K.f))) =
        ((((J.overMapPullback (Type w)
          T₁o.hom).obj
            (D.obj I)).1).obj (Opposite.op (Over.mk K'.f))) := by
    have hObj :
        (Over.map T₂o.hom).obj (Over.mk K.f) =
          (Over.map T₁o.hom).obj (Over.mk K'.f) := by
      apply over_mk_hext (𝒞 := C) (B := I.Y) (hY := rfl)
      exact heq_of_eq (by simp [K', g', T₁o, T₂o, localized_cover_descent_pullback_arrow_map,
        Category.assoc])
    simpa [GrothendieckTopology.overMapPullback] using
      congrArg (fun X : Over I.Y => (D.obj I).1.obj (Opposite.op X)) hObj
  let φ₂ :=
    (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T₂o).hom.hom K
  let φ₁ :=
    (localized_cover_descent_pullbackDatum_over_direct_to_component_iso
      (J := J) (U := U) 𝒰 D I T₁o).hom.hom K'
  let X₂ : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
  let X₁ : (Over K'.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K'.Y))
  let Q₂ :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun L : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ L.f)).obj
        ((J.overMapPullback (Type w) T₂o.hom).obj (D.obj I)))
  let Q₁ :=
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun L : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ L.f)).obj
        ((J.overMapPullback (Type w) T₁o.hom).obj (D.obj I)))
  have hcodType : (Q₂.obj K).1.obj X₂ = (Q₁.obj K').1.obj X₁ := by
    simpa [Q₂, Q₁, X₂, X₁, Pseudofunctor.toDescentData,
      localized_cover_descent_overMap_terminal_obj] using htargetType
  have happ : HEq (φ₂.hom.app X₂ x) (φ₁.hom.app X₁ y) := by
    let η₂ :=
      (localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₂o).inv.hom K
    let η₁ :=
      (localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₁o).inv.hom K'
    let μ₂ :=
      ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).map
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom).hom K
    let μ₁ :=
      ((Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).map
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom).hom K'
    let ν₂ :=
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).hom.app (D.obj I)).hom K
    let ν₁ :=
      ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
        (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).hom.app (D.obj I)).hom K'
    let ξ₂ : (((localized_cover_descent_pullbackDatum_over_source
        (J := J) (U := U) 𝒰 D I T₂o).obj K).1.obj X₂) :=
      ((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₂o).inv.hom K).hom.app X₂ x
    let ξ₁ : (((localized_cover_descent_pullbackDatum_over_source
        (J := J) (U := U) 𝒰 D I T₁o).obj K').1.obj X₁) :=
      ((localized_cover_descent_pullbackDatum_over_direct_source_iso
        (J := J) (U := U) 𝒰 D I T₁o).inv.hom K').hom.app X₁ y
    have hη₂ : HEq ξ₂ x := by
      simpa [ξ₂, X₂] using
        localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
          (J := J) (U := U) 𝒰 D I T₂o K x
    have hη₁ : HEq ξ₁ y := by
      simpa [ξ₁, X₁] using
        localized_cover_descent_pullbackDatum_over_direct_source_iso_inv_app_heq
          (J := J) (U := U) 𝒰 D I T₁o K' y
    have hη : HEq ξ₂ ξ₁ :=
      hη₂.trans (hxy.trans hη₁.symm)
    have hsourceOverType :
        (((localized_cover_descent_pullbackDatum_over_source
          (J := J) (U := U) 𝒰 D I T₂o).obj K).1.obj X₂) =
          (((localized_cover_descent_pullbackDatum_over_source
            (J := J) (U := U) 𝒰 D I T₁o).obj K').1.obj X₁) := by
      simp only [X₂, X₁, K', g', T₁o, T₂o,
        localized_cover_descent_pullbackDatum_over_source,
        localized_cover_descent_pullbackDatum,
        localized_cover_descent_pullback_arrow_map, Cover.Arrow.base,
        Functor.id_obj, Pseudofunctor.DescentData.pullFunctor_obj,
        Pseudofunctor.DescentData.pullFunctorObj_obj,
        pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        op_id, Quiver.Hom.id_toLoc,
        pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
        LocallyDiscrete.id_as, unop_id]
      congr 2
      exact eq_of_heq (congr_arg_heq D.obj (by
        ext <;> simp [Category.assoc]))
    let R₂ :=
      (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₂o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₂o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₂o)).obj
          (((J.pseudofunctorOver (Type w)).toDescentData
            (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I))
    let R₁ :=
      (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
        (f := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
        (p := T₁o.hom)
        (f' := fun K : ((𝒰.pullback I.f).pullback T₁o.hom).Arrow ↦ K.f)
        (α := fun K ↦ K.base)
        (p' := fun _ ↦ 𝟙 _)
        (w := localized_cover_descent_pullbackDatum_w (J := J) (U := I.Y)
          (𝒰.pullback I.f) T₁o)).obj
          (((J.pseudofunctorOver (Type w)).toDescentData
            (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I))
    have hmiddleCodType : (R₂.obj K).1.obj X₂ = (R₁.obj K').1.obj X₁ := by
      simp [R₂, R₁, X₂, X₁, K', g', T₁o, T₂o,
        Pseudofunctor.toDescentData,
        localized_cover_descent_pullback_arrow_map, Cover.Arrow.base,
        Category.assoc]
    let θ := (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).hom
    have hμ₂ : HEq
        (μ₂.hom.app X₂ (ξ₂))
        ((θ.hom K.base).hom.app
          (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y))))
          (ξ₂)) := by
      simpa only [μ₂, θ, X₂] using
        localized_cover_descent_pullFunctor_map_id_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f)
          (φ := (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom)
          T₂o K (ξ₂)
    have hμ₁ : HEq
        (μ₁.hom.app X₁ (ξ₁))
        ((θ.hom K'.base).hom.app
          (Opposite.op ((Over.map (𝟙 K'.Y)).obj (Over.mk (𝟙 K'.Y))))
          (ξ₁)) := by
      simpa only [μ₁, θ, X₁] using
        localized_cover_descent_pullFunctor_map_id_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f)
          (φ := (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom)
          T₁o K' (ξ₁)
    have hμmid : HEq
        ((θ.hom K.base).hom.app
          (Opposite.op ((Over.map (𝟙 K.Y)).obj (Over.mk (𝟙 K.Y))))
          (ξ₂))
        ((θ.hom K'.base).hom.app
          (Opposite.op ((Over.map (𝟙 K'.Y)).obj (Over.mk (𝟙 K'.Y))))
          (ξ₁)) := by
      apply localized_cover_descent_fun_app_heq_of_type_eqs hsourceOverType hmiddleCodType ?_ hη
      have hbase : K.base = K'.base := by
        exact (localized_cover_descent_pullback_arrow_map_base
          (J := J) (U := I.Y) (𝒰.pullback I.f) g' K).symm
      exact congr_arg_heq
        (fun L : (𝒰.pullback I.f).Arrow =>
          (θ.hom L).hom.app
            (Opposite.op ((Over.map (𝟙 L.Y)).obj (Over.mk (𝟙 L.Y)))))
        hbase
    have hμ : HEq
        (μ₂.hom.app X₂ (ξ₂))
        (μ₁.hom.app X₁ (ξ₁)) :=
      hμ₂.trans (hμmid.trans hμ₁.symm)
    have hν₂ : HEq
        (ν₂.hom.app X₂ (μ₂.hom.app X₂ (ξ₂)))
        (μ₂.hom.app X₂ (ξ₂)) := by
      simpa [ν₂, R₂, X₂] using
        localized_cover_descent_toDescentDataCompPullFunctorIso_hom_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f) (M := D.obj I) T₂o K
          (μ₂.hom.app X₂ (ξ₂))
    have hν₁ : HEq
        (ν₁.hom.app X₁ (μ₁.hom.app X₁ (ξ₁)))
        (μ₁.hom.app X₁ (ξ₁)) := by
      simpa [ν₁, R₁, X₁] using
        localized_cover_descent_toDescentDataCompPullFunctorIso_hom_app_heq
          (J := J) (𝒱 := 𝒰.pullback I.f) (M := D.obj I) T₁o K'
          (μ₁.hom.app X₁ (ξ₁))
    simpa [φ₂, φ₁, η₂, η₁, μ₂, μ₁, ν₂, ν₁,
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso,
      Category.assoc] using hν₂.trans (hμ.trans hν₁.symm)
  have hleft :
      HEq
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₂o K x)
        (φ₂.hom.app X₂ x) := by
    have h :=
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
        (J := J) (U := U) 𝒰 D I T₂o K x
    exact (heq_of_eq h).symm.trans (cast_heq _ _)
  have hright :
      HEq (φ₁.hom.app X₁ y)
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₁o K' y) := by
    have h :=
      localized_cover_descent_pullbackDatum_over_direct_to_component_iso_apply
        (J := J) (U := U) 𝒰 D I T₁o K' y
    exact (cast_heq _ _).symm.trans (heq_of_eq h)
  exact hleft.trans (happ.trans hright)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the over-map/component-source comparison commutes with
restriction along a morphism in the slice over a fixed cover member. -/
theorem localized_cover_descent_glue_value_overMap_equiv_component_source_restrict_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T₁))
    (K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow) :
    HEq
      ((((localized_cover_descent_glue_value_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I T₂)
          (localized_cover_descent_glue_restrict_value
            (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s)).1) K)
      ((((localized_cover_descent_glue_value_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I T₁) s).1)
          (localized_cover_descent_pullback_arrow_map
            (J := J) (U := I.Y) (𝒰.pullback I.f) g K)) := by
  let K' :=
    localized_cover_descent_pullback_arrow_map
      (J := J) (U := I.Y) (𝒰.pullback I.f) g K
  let H₂ := K.map (Cover.pullbackComp 𝒰 T₂.hom I.f).inv
  let H₁ := K'.map (Cover.pullbackComp 𝒰 T₁.hom I.f).inv
  have hH :
      localized_cover_descent_pullback_arrow_map
          (J := J) (U := U) 𝒰 ((Over.map I.f).map g) H₂ = H₁ := by
    simpa [K', H₂, H₁] using
      localized_cover_descent_pullbackComp_inv_arrow_map_eq
        (J := J) (U := U) 𝒰 I g K
  have hsource :
      HEq
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T₂
            (localized_cover_descent_glue_restrict_value
              (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s).1) K)
        ((localized_cover_descent_glue_family_overMap_equiv_direct_source
          (J := J) (U := U) 𝒰 D I T₁ s.1) K') := by
    refine
      (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
        (J := J) (U := U) 𝒰 D I T₂
        (localized_cover_descent_glue_restrict_value
          (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s).1 K).trans ?_
    refine
      (localized_cover_descent_glue_restrict_section_heq_source
        (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s H₂).trans ?_
    refine (congr_arg_heq s.1 hH).trans ?_
    exact
      (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
        (J := J) (U := U) 𝒰 D I T₁ s.1 K').symm
  exact
    show
      HEq
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₂ K
          ((localized_cover_descent_glue_family_overMap_equiv_direct_source
            (J := J) (U := U) 𝒰 D I T₂
            (localized_cover_descent_glue_restrict_value
              (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s).1) K))
        (localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
          (J := J) (U := U) 𝒰 D I T₁ K'
          ((localized_cover_descent_glue_family_overMap_equiv_direct_source
            (J := J) (U := U) 𝒰 D I T₁ s.1) K')) from
    localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_arrow_map_heq
      (J := J) (U := U) 𝒰 D I g K hsource

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: after passing from source-compatible families to an actual
component section, restriction along a slice morphism is ordinary sheaf restriction. -/
theorem localized_cover_descent_glue_component_equiv_over_restrict_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {T₁ T₂ : Over I.Y}
    (g : T₂ ⟶ T₁)
    (s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
      ((Over.map I.f).obj T₁)) :
    HEq
      (localized_cover_descent_glue_component_equiv_over
        (J := J) (U := U) 𝒰 D I T₂
        ((localized_cover_descent_glue_value_overMap_equiv_component_source
          (J := J) (U := U) 𝒰 D I T₂)
          (localized_cover_descent_glue_restrict_value
            (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s)))
      ((D.obj I).1.map g.op
        (localized_cover_descent_glue_component_equiv_over
          (J := J) (U := U) 𝒰 D I T₁
          ((localized_cover_descent_glue_value_overMap_equiv_component_source
            (J := J) (U := U) 𝒰 D I T₁) s))) := by
  -- Route correction: keep the component-gluing comparison at the sheaf section level, then
  -- use cover-member restrictions to avoid unfolding the sheafification or the source family.
  let t₁ :=
    (localized_cover_descent_glue_value_overMap_equiv_component_source
      (J := J) (U := U) 𝒰 D I T₁) s
  let t₂ :=
    (localized_cover_descent_glue_value_overMap_equiv_component_source
      (J := J) (U := U) 𝒰 D I T₂)
      (localized_cover_descent_glue_restrict_value
        (J := J) (U := U) 𝒰 D ((Over.map I.f).map g) s)
  have hsource : ∀ K : ((𝒰.pullback I.f).pullback T₂.hom).Arrow,
      HEq (t₂.1 K)
        (t₁.1
          (localized_cover_descent_pullback_arrow_map
            (J := J) (U := I.Y) (𝒰.pullback I.f) g K)) := by
    intro K
    exact localized_cover_descent_glue_value_overMap_equiv_component_source_restrict_heq
      (J := J) (U := U) 𝒰 D I g s K
  exact localized_cover_descent_glue_component_source_restrict_heq
    (J := J) (U := U) 𝒰 D I g t₁ t₂ hsource

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the restricted glued presheaf value
on a cover member is equivalent to the corresponding section set of that component sheaf. -/
noncomputable def localized_cover_descent_glue_component_obj_equiv_shrink_over
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (T : Over I.Y) :
    Shrink (localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
        ((Over.map I.f).obj T)) ≃
      ((D.obj I).1.obj (Opposite.op T)) :=
    (equivShrink _).symm.trans
      ((localized_cover_descent_glue_value_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I T).trans
        (localized_cover_descent_glue_component_equiv_over
          (J := J) (U := U) 𝒰 D I T))

/-- Helper for Lemma 7.26.4: objectwise naturality of the shrink-wrapped component comparison
is heterogeneously the component-section restriction bridge after unwrapping `Shrink`. -/
theorem localized_cover_descent_glue_component_obj_equiv_shrink_over_map_apply_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {X Y : (Over I.Y)ᵒᵖ}
    (f : X ⟶ Y)
    (x : Shrink (localized_cover_descent_glue_value
      (J := J) (U := U) 𝒰 D ((Over.map I.f).obj (Opposite.unop X)))) :
    HEq
      ((localized_cover_descent_glue_component_obj_equiv_shrink_over
        (J := J) (U := U) 𝒰 D I (Opposite.unop Y))
          (equivShrink _ (localized_cover_descent_glue_restrict_value
            (J := J) (U := U) 𝒰 D ((Over.map I.f).map f.unop)
            ((equivShrink _).symm x))))
      ((D.obj I).1.map f
        ((localized_cover_descent_glue_component_obj_equiv_shrink_over
          (J := J) (U := U) 𝒰 D I (Opposite.unop X)) x)) := by
  -- Unwrap the resize equivalence and then use the component-level restriction comparison.
  simpa [localized_cover_descent_glue_component_obj_equiv_shrink_over] using
    localized_cover_descent_glue_component_equiv_over_restrict_heq
      (J := J) (U := U) 𝒰 D I f.unop ((equivShrink _).symm x)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the objectwise comparison between
the restricted glued presheaf and `D.obj I` is natural in the slice object over `I.Y`. -/
theorem localized_cover_descent_glue_component_presheaf_iso_naturality
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    {X Y : (Over I.Y)ᵒᵖ}
    (f : X ⟶ Y) :
    ((Over.map I.f).op ⋙ localized_cover_descent_glue_presheaf
        (J := J) (U := U) 𝒰 D).map f ≫
      (localized_cover_descent_glue_component_obj_equiv_shrink_over
        (J := J) (U := U) 𝒰 D I (Opposite.unop Y)).toIso.hom =
    (localized_cover_descent_glue_component_obj_equiv_shrink_over
        (J := J) (U := U) 𝒰 D I (Opposite.unop X)).toIso.hom ≫
          (D.obj I).1.map f := by
  -- Check naturality on sections; after this pointwise reduction the HEq bridge has a small
  -- target, so converting it to equality does not force a global presheaf-level whnf.
  ext x
  exact eq_of_heq
    (localized_cover_descent_glue_component_obj_equiv_shrink_over_map_apply_heq
      (J := J) (U := U) 𝒰 D I f x)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: restricting the glued presheaf to a
cover member is naturally isomorphic to the presheaf underlying the corresponding component
sheaf of `D`. -/
noncomputable def localized_cover_descent_glue_component_presheaf_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    (Over.map I.f).op ⋙ localized_cover_descent_glue_presheaf
        (J := J) (U := U) 𝒰 D ≅
      (D.obj I).1 :=
  NatIso.ofComponents
    (fun X ↦ (localized_cover_descent_glue_component_obj_equiv_shrink_over
      (J := J) (U := U) 𝒰 D I (Opposite.unop X)).toIso)
    (localized_cover_descent_glue_component_presheaf_iso_naturality
      (J := J) (U := U) 𝒰 D I)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: a presheaf-level comparison on the
restriction over a cover member sheafifies to the corresponding component sheaf isomorphism. -/
noncomputable def localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (e :
      (Over.map I.f).op ⋙ localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D ≅
        (D.obj I).1) :
    (J.overMapPullback (Type w) I.f).obj
        (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D) ≅
      D.obj I :=
  -- First identify pullback of the sheafification with sheafification after pullback; then
  -- sheafify the presheaf comparison and use the standard self-sheafification iso for the
  -- already-sheaf component.
  ((Over.map I.f).pushforwardContinuousSheafificationCompatibility
      (Type w) (J.over I.Y) (J.over U)).symm.app
        (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D) ≪≫
    (presheafToSheaf (J.over I.Y) (Type w)).mapIso e ≪≫
    (sheafificationIso (D.obj I)).symm

/-- Helper for Lemma 7.26.4: after sheafifying the glued presheaf, its pullback to the cover
member `I` is canonically isomorphic to the component sheaf `D.obj I`. -/
noncomputable def localized_cover_descent_glue_component_sheaf_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    (J.overMapPullback (Type w) I.f).obj
        (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D) ≅
      D.obj I :=
  localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso
    (J := J) (U := U) 𝒰 D I
    (localized_cover_descent_glue_component_presheaf_iso (J := J) (U := U) 𝒰 D I)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: a q-pulled presheaf agrees with the iterated pullback through a
cover member after normalizing the compositional equation `f ≫ I.f = q`. -/
theorem localized_cover_descent_q_pullback_presheaf_eq
    (𝒰 : J.Cover U)
    (P : (Over U)ᵒᵖ ⥤ Type w)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    (Over.map q).op ⋙ P = (Over.map f).op ⋙ (Over.map I.f).op ⋙ P := by
  -- Replace `q` by the composite and use the canonical functoriality lemma for `Over.map`.
  subst q
  rw [Over.mapComp_eq]
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the same q-pullback normalization in the reverse orientation,
for rewriting an iterated pullback back to the common `q`-pulled presheaf. -/
theorem localized_cover_descent_q_pullback_presheaf_eq_symm
    (𝒰 : J.Cover U)
    (P : (Over U)ᵒᵖ ⥤ Type w)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    (Over.map f).op ⋙ (Over.map I.f).op ⋙ P = (Over.map q).op ⋙ P := by
  -- Route correction: keep the final overlap comparison in a single q-pulled presheaf spelling
  -- instead of reopening the direct-source component transport at the sheafified level.
  -- This records the orientation needed when a sheafification comparison is cancelled back
  -- to the q-normalized presheaf square.
  exact (localized_cover_descent_q_pullback_presheaf_eq
    (J := J) (U := U) 𝒰 P q I f hf).symm

/-- Helper for Lemma 7.26.4: the q-normalized component presheaf comparison is the
cover-component comparison after rewriting `q` as `f ≫ I.f`. -/
noncomputable def localized_cover_descent_q_component_presheaf_hom
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    (Over.map q).op ⋙ localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D ⟶
      ((J.overMapPullback (Type w) f).obj (D.obj I)).1 :=
  eqToHom
      (localized_cover_descent_q_pullback_presheaf_eq
        (J := J) (U := U) 𝒰
        (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D) q I f hf) ≫
    (Functor.isoWhiskerLeft (Over.map f).op
      (localized_cover_descent_glue_component_presheaf_iso (J := J) (U := U) 𝒰 D I)).hom

/-- Helper for Lemma 7.26.4: the q-normalized component presheaf comparison unfolds to the
single q-pullback rewrite followed by the whiskered component presheaf isomorphism. -/
theorem localized_cover_descent_q_component_presheaf_hom_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    localized_cover_descent_q_component_presheaf_hom
        (J := J) (U := U) 𝒰 D q I f hf =
      eqToHom
          (localized_cover_descent_q_pullback_presheaf_eq
            (J := J) (U := U) 𝒰
            (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D) q I f hf) ≫
        (Functor.isoWhiskerLeft (Over.map f).op
          (localized_cover_descent_glue_component_presheaf_iso
            (J := J) (U := U) 𝒰 D I)).hom := by
  -- The lemma records the definitional normal form so later proofs can rewrite to the common
  -- q-pulled presheaf comparison without unfolding the component sheaf construction.
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: applying `eqToHom` at a presheaf object only changes the dependent
type of a section. -/
theorem localized_cover_descent_eqToHom_app_heq
    {A : Type*} [Category A] {F G : A ⥤ Type w} (h : F = G)
    (X : A) (x : F.obj X) :
    HEq ((eqToHom h).app X x) x := by
  -- Once the functor equality is eliminated, the `eqToHom` component is the identity.
  cases h
  rfl

/-- Helper for Lemma 7.26.4: the resize equivalence for glued values respects an explicitly named
equality of the underlying slice object. -/
theorem localized_cover_descent_equivShrink_symm_glue_value_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V V' : Over U} (hV : V = V')
    {x : Shrink (localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V)}
    {x' : Shrink (localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V')}
    (hx : HEq x x') :
    HEq ((equivShrink _).symm x) ((equivShrink _).symm x') := by
  -- The named object equality aligns both the shrink type and the glued-value type.
  subst hV
  cases hx
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: heterogeneously equal glued compatible families have
heterogeneously equal component values at heterogeneously equal pullback-cover arrows. -/
theorem localized_cover_descent_glue_value_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V V' : Over U} (hV : V = V')
    {s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V}
    {s' : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V'}
    (hs : HEq s s')
    {K : (𝒰.pullback V.hom).Arrow}
    {K' : (𝒰.pullback V'.hom).Arrow}
    (hK : HEq K K') :
    HEq (s.1 K) (s'.1 K') := by
  -- After aligning the base object, the glued value, and the cover arrow, this is reflexivity.
  subst hV
  cases hs
  cases hK
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: mapping an iterated pullback-cover arrow through
`Cover.pullbackComp.inv` only changes the cover type; after naming the composite arrow equality
the resulting arrow is heterogeneously the same pullback-cover arrow. -/
theorem localized_cover_descent_pullbackComp_inv_arrow_heq
    (𝒰 : J.Cover U)
    {Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ U) (h : Z ⟶ U)
    (hh : f ≫ g = h)
    (K : ((𝒰.pullback g).pullback f).Arrow)
    (K₀ : (𝒰.pullback h).Arrow)
    (hY : K.Y = K₀.Y)
    (hf : K.f ≍ K₀.f) :
    HEq (K.map (Cover.pullbackComp 𝒰 f g).inv) K₀ := by
  subst h
  exact heq_of_eq (Cover.Arrow.ext hY hf)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: descent transition morphisms are unchanged, up to heterogeneous
equality, when the base arrow, the two cover members, and the two legs are replaced by explicitly
equal data. The equation witnesses in the descent datum are proof-irrelevant. -/
theorem localized_cover_descent_descent_hom_heq_of_eqs
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} {q q' : Y ⟶ U}
    {I₁ I₁' I₂ I₂' : 𝒰.Arrow}
    (hq : q = q') (hI₁ : I₁ = I₁') (hI₂ : I₂ = I₂')
    {f₁ : Y ⟶ I₁.Y} {f₁' : Y ⟶ I₁'.Y}
    {f₂ : Y ⟶ I₂.Y} {f₂' : Y ⟶ I₂'.Y}
    (hf₁ : HEq f₁ f₁') (hf₂ : HEq f₂ f₂')
    (h₁ : f₁ ≫ I₁.f = q) (h₂ : f₂ ≫ I₂.f = q)
    (h₁' : f₁' ≫ I₁'.f = q') (h₂' : f₂' ≫ I₂'.f = q') :
    HEq (D.hom q f₁ f₂ h₁ h₂) (D.hom q' f₁' f₂' h₁' h₂') := by
  subst q'
  subst I₁'
  subst I₂'
  have hf₁' : f₁ = f₁' := eq_of_heq hf₁
  have hf₂' : f₂ = f₂' := eq_of_heq hf₂
  subst hf₁'
  subst hf₂'
  cases proof_irrel h₁ h₁'
  cases proof_irrel h₂ h₂'
  rfl

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: if the restricted source section is identified with a terminal
section over the over-map pullback, then restricting a descent transition agrees with applying
the descent transition whose legs are written in that over-map pullback form. -/
theorem localized_cover_descent_descent_hom_restrict_terminal_app_heq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y Z : C} (T : Over Y) (a : Z ⟶ T.left)
    {q : Y ⟶ U} {I₁ I₂ : 𝒰.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (x : (D.obj I₁).1.obj (Opposite.op ((Over.map f₁).obj T)))
    {y : (((J.pseudofunctorOver (Type w)).map
        (a ≫ ((Over.map f₁).obj T).hom).op.toLoc).toFunctor.obj
          (D.obj I₁)).1.obj (Opposite.op (Over.mk (𝟙 Z)))}
    (hxy : HEq
      (((J.overMapPullback (Type w) ((Over.map f₁).obj T).hom).obj (D.obj I₁)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 ((Over.map f₁).obj T).left) from
          Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := ((Over.map f₁).obj T).hom) (M := D.obj I₁)).symm
          x))
      y) :
    HEq
      (((J.overMapPullback (Type w) ((Over.map f₂).obj T).hom).obj (D.obj I₂)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 ((Over.map f₂).obj T).left) from
          Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := ((Over.map f₂).obj T).hom) (M := D.obj I₂)).symm
          ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (Opposite.op T) x)))
      ((D.hom (a ≫ ((Over.map f₁).obj T).hom ≫ I₁.f)
          (i₁ := I₁) (i₂ := I₂)
          (a ≫ ((Over.map f₁).obj T).hom)
          (a ≫ ((Over.map f₂).obj T).hom)
          (Category.assoc a ((Over.map f₁).obj T).hom I₁.f)
          (by
            calc
              (a ≫ ((Over.map f₂).obj T).hom) ≫ I₂.f =
                  a ≫ T.hom ≫ f₂ ≫ I₂.f := by
                    change (a ≫ (T.hom ≫ f₂)) ≫ I₂.f =
                      a ≫ (T.hom ≫ (f₂ ≫ I₂.f))
                    exact
                      (Category.assoc a (T.hom ≫ f₂) I₂.f).trans
                        (congrArg (fun e : T.left ⟶ U ↦ a ≫ e)
                          (Category.assoc T.hom f₂ I₂.f))
                _ = a ≫ T.hom ≫ f₁ ≫ I₁.f := by
                      exact congrArg (fun e : Y ⟶ U ↦ a ≫ (T.hom ≫ e))
                        (hf₂.trans hf₁.symm)
                _ = a ≫ ((Over.map f₁).obj T).hom ≫ I₁.f := by
                      change a ≫ (T.hom ≫ (f₁ ≫ I₁.f)) =
                        a ≫ ((T.hom ≫ f₁) ≫ I₁.f)
                      exact congrArg (fun e : T.left ⟶ U ↦ a ≫ e)
                        (Category.assoc T.hom f₁ I₁.f).symm)).hom.app
          (Opposite.op (Over.mk (𝟙 Z))) y) := by
  -- Use naturality of the transition map along the over-map arrow, then identify the pulled-back
  -- transition with the descent transition whose legs are written after restriction.
  let g' : Z ⟶ Y := a ≫ T.hom
  let gf₁ : Z ⟶ I₁.Y := a ≫ ((Over.map f₁).obj T).hom
  let gf₂ : Z ⟶ I₂.Y := a ≫ ((Over.map f₂).obj T).hom
  let φ := D.hom q f₁ f₂ hf₁ hf₂
  let ψ :=
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := J.pseudofunctorOver (Type w)) φ g' gf₁ gf₂
      (by
        dsimp [g', gf₁]
        exact Category.assoc a T.hom f₁)
      (by
        dsimp [g', gf₂]
        exact Category.assoc a T.hom f₂)
  let δ :=
    D.hom (gf₁ ≫ I₁.f)
      (i₁ := I₁) (i₂ := I₂) gf₁ gf₂
      (by rfl)
      (by
        calc
          gf₂ ≫ I₂.f = a ≫ T.hom ≫ f₂ ≫ I₂.f := by
            dsimp [gf₂]
            change (a ≫ (T.hom ≫ f₂)) ≫ I₂.f =
              a ≫ (T.hom ≫ (f₂ ≫ I₂.f))
            exact
              (Category.assoc a (T.hom ≫ f₂) I₂.f).trans
                (congrArg (fun e : T.left ⟶ U ↦ a ≫ e)
                  (Category.assoc T.hom f₂ I₂.f))
          _ = a ≫ T.hom ≫ f₁ ≫ I₁.f := by
            exact congrArg (fun e : Y ⟶ U ↦ a ≫ (T.hom ≫ e))
              (hf₂.trans hf₁.symm)
          _ = gf₁ ≫ I₁.f := by
            dsimp [gf₁]
            change a ≫ (T.hom ≫ (f₁ ≫ I₁.f)) =
              (a ≫ (T.hom ≫ f₁)) ≫ I₁.f
            exact
              (congrArg (fun e : T.left ⟶ U ↦ a ≫ e)
                (Category.assoc T.hom f₁ I₁.f).symm).trans
                (Category.assoc a (T.hom ≫ f₁) I₁.f).symm)
  have hpull : ψ = δ := by
    have hq' : g' ≫ q = gf₁ ≫ I₁.f := by
      calc
        g' ≫ q = a ≫ T.hom ≫ (f₁ ≫ I₁.f) := by
          dsimp [g']
          calc
            (a ≫ T.hom) ≫ q = (a ≫ T.hom) ≫ (f₁ ≫ I₁.f) :=
              congrArg (fun e : Y ⟶ U ↦ (a ≫ T.hom) ≫ e) hf₁.symm
            _ = a ≫ T.hom ≫ (f₁ ≫ I₁.f) :=
              Category.assoc a T.hom (f₁ ≫ I₁.f)
        _ = gf₁ ≫ I₁.f := by
          dsimp [gf₁]
          change a ≫ (T.hom ≫ (f₁ ≫ I₁.f)) =
            (a ≫ (T.hom ≫ f₁)) ≫ I₁.f
          exact
            (congrArg (fun e : T.left ⟶ U ↦ a ≫ e)
              (Category.assoc T.hom f₁ I₁.f).symm).trans
              (Category.assoc a (T.hom ≫ f₁) I₁.f).symm
    simpa [ψ, δ, φ, g', gf₁, gf₂] using
      D.pullHom_hom g' q (gf₁ ≫ I₁.f) hq' f₁ f₂ hf₁ hf₂ gf₁ gf₂
        (by
          dsimp [g', gf₁]
          exact Category.assoc a T.hom f₁)
        (by
          dsimp [g', gf₂]
          exact Category.assoc a T.hom f₂)
  have hleft : HEq
      (((J.overMapPullback (Type w) ((Over.map f₂).obj T).hom).obj (D.obj I₂)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 ((Over.map f₂).obj T).left) from
          Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := ((Over.map f₂).obj T).hom) (M := D.obj I₂)).symm
          ((D.hom q f₁ f₂ hf₁ hf₂).hom.app (Opposite.op T) x)))
      (ψ.hom.app (Opposite.op (Over.mk (𝟙 Z))) y) := by
    cases T
    rename_i Tleft Tright Thom
    let X₀ : (Over Z)ᵒᵖ := Opposite.op (Over.mk (𝟙 Z))
    let T₀ : Over Y := { left := Tleft, right := Tright, hom := Thom }
    let A₀ : Over Y := (Over.map Thom).obj (Over.mk a)
    let m : A₀ ⟶ T₀ := Over.homMk a
    have hA₀term : (Over.map (a ≫ Thom)).obj (Over.mk (𝟙 Z)) = A₀ := by
      dsimp [A₀]
      apply over_mk_hext (𝒞 := C) (B := Y) (hY := rfl)
      exact heq_of_eq (Category.id_comp (a ≫ Thom))
    let raw₁ :=
      (((J.overMapPullback (Type w) (Thom ≫ f₁)).obj (D.obj I₁)).1.map
        (show Over.mk a ⟶ Over.mk (𝟙 Tleft) from Over.homMk a).op
        (cast
          (localized_cover_descent_overMap_terminal_section_eq
            (J := J) (f := Thom ≫ f₁) (M := D.obj I₁)).symm
          x))
    let raw₁' :
        (((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
          (D.obj I₁)).1.obj (Opposite.op A₀) :=
      (D.obj I₁).1.map ((Over.map f₁).map m).op x
    have hraw₁' : HEq raw₁ raw₁' := by
      simpa [raw₁, raw₁', m, A₀, T₀, GrothendieckTopology.overMapPullback,
        Category.assoc] using
        localized_cover_descent_overMap_terminal_restrict_overMap_hom_heq
          (J := J) (M := D.obj I₁) (f := f₁) (T := T₀) (a := a) x
    let mapφ := ((J.pseudofunctorOver (Type w)).map g'.op.toLoc).toFunctor.map φ
    let A :=
      ((J.pseudofunctorOver (Type w)).mapComp'
        f₁.op.toLoc g'.op.toLoc gf₁.op.toLoc
        (by simp [g', gf₁, ← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])).hom.toNatTrans.app
        (D.obj I₁)
    let B :=
      ((J.pseudofunctorOver (Type w)).mapComp'
        f₂.op.toLoc g'.op.toLoc gf₂.op.toLoc
        (by simp [g', gf₂, ← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])).inv.toNatTrans.app
        (D.obj I₂)
    have hA : HEq (A.hom.app X₀ y) y := by
      simpa [A, X₀] using
        (pf_mapComp'_hom_component_apply_heq
          (J := J)
          (f := f₁.op.toLoc)
          (g' := g'.op.toLoc)
          (k := gf₁.op.toLoc)
          (hk := by simp [g', gf₁, ← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])
          (D.obj I₁) X₀ y)
    have hinput : HEq (A.hom.app X₀ y) raw₁ :=
      hA.trans (HEq.symm (by
        simpa [raw₁, gf₁, GrothendieckTopology.overMapPullback] using hxy))
    have hinput' : HEq (A.hom.app X₀ y) raw₁' :=
      hinput.trans hraw₁'
    have hmap :
        HEq (mapφ.hom.app X₀ (A.hom.app X₀ y))
          (φ.hom.app (Opposite.op A₀) raw₁') := by
      have hsrcTy :
          (((J.pseudofunctorOver (Type w)).map g'.op.toLoc).toFunctor.obj
            (((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
              (D.obj I₁))).1.obj X₀ =
          (((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
              (D.obj I₁)).1.obj (Opposite.op A₀) := by
        simpa [g', X₀, GrothendieckTopology.overMapPullback] using
          congrArg
            (fun W : Over Y =>
              (D.obj I₁).1.obj (Opposite.op ((Over.map f₁).obj W)))
            hA₀term
      have htgtTy :
          (((J.pseudofunctorOver (Type w)).map g'.op.toLoc).toFunctor.obj
            (((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.obj
              (D.obj I₂))).1.obj X₀ =
          (((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.obj
              (D.obj I₂)).1.obj (Opposite.op A₀) := by
        simpa [g', X₀, GrothendieckTopology.overMapPullback] using
          congrArg
            (fun W : Over Y =>
              (D.obj I₂).1.obj (Opposite.op ((Over.map f₂).obj W)))
            hA₀term
      have hfun :
          HEq (mapφ.hom.app X₀) (φ.hom.app (Opposite.op A₀)) := by
        simpa [mapφ, g', X₀, GrothendieckTopology.overMapPullback] using
          natTrans_app_heq_of_eq φ.hom (congrArg Opposite.op hA₀term)
      exact localized_cover_descent_fun_app_heq_of_type_eqs hsrcTy htgtTy hfun hinput'
    let raw₂' :
        (((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.obj
          (D.obj I₂)).1.obj (Opposite.op A₀) :=
      (D.obj I₂).1.map ((Over.map f₂).map m).op
        (φ.hom.app (Opposite.op T₀) x)
    have hnat_eq :=
      congrFun (φ.hom.naturality m.op) x
    have hnat :
        HEq
          (((J.overMapPullback (Type w) (Thom ≫ f₂)).obj (D.obj I₂)).1.map
            (show Over.mk a ⟶ Over.mk (𝟙 Tleft) from Over.homMk a).op
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := Thom ≫ f₂) (M := D.obj I₂)).symm
              (φ.hom.app (Opposite.op T₀) x)))
          (φ.hom.app (Opposite.op A₀) raw₁') := by
      have hraw₂' :
          HEq
            (((J.overMapPullback (Type w) (Thom ≫ f₂)).obj (D.obj I₂)).1.map
              (show Over.mk a ⟶ Over.mk (𝟙 Tleft) from Over.homMk a).op
              (cast
                (localized_cover_descent_overMap_terminal_section_eq
                  (J := J) (f := Thom ≫ f₂) (M := D.obj I₂)).symm
                (φ.hom.app (Opposite.op T₀) x)))
            raw₂' := by
        simpa [raw₂', m, A₀, T₀, GrothendieckTopology.overMapPullback,
          Category.assoc] using
          localized_cover_descent_overMap_terminal_restrict_overMap_hom_heq
            (J := J) (M := D.obj I₂) (f := f₂) (T := T₀) (a := a)
            (φ.hom.app (Opposite.op T₀) x)
      have hnat' : HEq (φ.hom.app (Opposite.op A₀) raw₁') raw₂' := by
        exact heq_of_eq (by simpa [raw₁', raw₂'] using hnat_eq)
      exact hraw₂'.trans hnat'.symm
    have hB :
        HEq (B.hom.app X₀ (mapφ.hom.app X₀ (A.hom.app X₀ y)))
          (mapφ.hom.app X₀ (A.hom.app X₀ y)) := by
      simpa [B, X₀] using
        (pf_mapComp'_inv_component_apply_heq
          (J := J)
          (f := f₂.op.toLoc)
          (g' := g'.op.toLoc)
          (k := gf₂.op.toLoc)
          (hk := by simp [g', gf₂, ← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])
          (D.obj I₂) X₀ (mapφ.hom.app X₀ (A.hom.app X₀ y)))
    simpa [φ, ψ, mapφ, A, B, X₀, g', gf₁, gf₂,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      GrothendieckTopology.overMapPullback, Category.assoc] using
      hnat.trans (hmap.symm.trans hB.symm)
  have hright : HEq
      (ψ.hom.app (Opposite.op (Over.mk (𝟙 Z))) y)
      (δ.hom.app (Opposite.op (Over.mk (𝟙 Z))) y) := by
    exact localized_cover_descent_sheaf_hom_app_heq
      (J := J) rfl rfl ψ δ (heq_of_eq hpull) (heq_of_eq rfl) (heq_of_eq rfl)
  exact hleft.trans (by
    simpa [δ, gf₁, gf₂, Category.assoc] using hright)

/-- Helper for Lemma 7.26.4: the q-normalized component presheaf comparison is compatible with
the descent transition maps of the component datum. -/
theorem localized_cover_descent_q_component_presheaf_hom_descent
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : 𝒰.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    localized_cover_descent_q_component_presheaf_hom
        (J := J) (U := U) 𝒰 D q I₁ f₁ hf₁ ≫
      (D.hom q f₁ f₂ hf₁ hf₂).hom =
    localized_cover_descent_q_component_presheaf_hom
        (J := J) (U := U) 𝒰 D q I₂ f₂ hf₂ := by
  subst q
  ext X x
  cases X using Opposite.rec
  rename_i T
  simp only [
    localized_cover_descent_q_component_presheaf_hom,
    localized_cover_descent_glue_component_presheaf_iso,
    localized_cover_descent_glue_component_obj_equiv_shrink_over,
    localized_cover_descent_glue_presheaf,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, FunctorToTypes.comp, Category.assoc]
  apply localized_cover_descent_glue_component_equiv_over_ext
    (J := J) (U := U) 𝒰 D I₂ ((Over.map f₂).obj T)
  intro K
  let g : K.Y ⟶ Y := K.f ≫ T.hom
  have hObj₂ :
      (Over.map (T.hom ≫ f₂)).obj (Over.mk K.f) =
        (Over.map (K.f ≫ T.hom ≫ f₂)).obj (Over.mk (𝟙 K.Y)) := by
    apply over_mk_hext (𝒞 := C) (B := I₂.Y) (hY := rfl)
    exact heq_of_eq (by
      simp only [Over.map_obj_hom, Over.mk_hom, Discrete.natTrans_app]
      exact (Category.id_comp (K.f ≫ T.hom ≫ f₂)).symm)
  have hObj₂_left : (eqToHom hObj₂).left = 𝟙 K.Y := by
    rw [over_eqToHom_left hObj₂]
    rfl
  have hObj₁ :
      (Over.map (T.hom ≫ f₁)).obj (Over.mk K.f) =
        (Over.map (K.f ≫ T.hom ≫ f₁)).obj (Over.mk (𝟙 K.Y)) := by
    apply over_mk_hext (𝒞 := C) (B := I₁.Y) (hY := rfl)
    exact heq_of_eq (by
      simp only [Over.map_obj_hom, Over.mk_hom, Discrete.natTrans_app]
      exact (Category.id_comp (K.f ≫ T.hom ≫ f₁)).symm)
  let V : Over U := (Over.map (f₁ ≫ I₁.f)).obj T
  let K₀ : (𝒰.pullback V.hom).Arrow :=
    ⟨K.Y, K.f, by
      simpa [V, g, GrothendieckTopology.Cover.coe_pullback, Category.assoc, hf₂] using K.hf⟩
  let s : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D V :=
    (equivShrink _).symm x
  let z := s.1 K₀
  have h₂ : (g ≫ f₂) ≫ I₂.f = g ≫ f₁ ≫ I₁.f := by
    calc
      (g ≫ f₂) ≫ I₂.f = g ≫ (f₂ ≫ I₂.f) :=
        Category.assoc g f₂ I₂.f
      _ = g ≫ (f₁ ≫ I₁.f) :=
        congrArg (fun e ↦ g ≫ e) hf₂
      _ = g ≫ f₁ ≫ I₁.f :=
        rfl
  have hcomp :=
    congrArg
      (fun η ↦ η.hom.app (Opposite.op (Over.mk (𝟙 K.Y))) z)
      (D.hom_comp (g ≫ f₁ ≫ I₁.f)
        (i₁ := K₀.base) (i₂ := I₁) (i₃ := I₂)
        (𝟙 K.Y) (g ≫ f₁) (g ≫ f₂)
        (by simp [K₀, V, g, GrothendieckTopology.Cover.Arrow.base, Category.assoc])
        (Category.assoc g f₁ I₁.f)
        h₂)
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq hcomp) (HEq.symm ?_)))
  · -- Left bridge: compute the `I₁` component at `K`, move restriction through the descent
    -- map, and normalize the direct-source terminal value to `z`.
    let T₁ : Over I₁.Y := (Over.map f₁).obj T
    let X₀ : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
    let hq₁ := localized_cover_descent_q_pullback_presheaf_eq
      (J := J) (U := U) 𝒰
      (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D)
      (f₁ ≫ I₁.f) I₁ f₁ rfl
    let s₁ : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
        ((Over.map I₁.f).obj T₁) :=
      (equivShrink _).symm ((eqToHom hq₁).app (Opposite.op T) x)
    have hV₁ : ((Over.map I₁.f).obj T₁) = V := by
      apply over_mk_hext (𝒞 := C) (B := U) (hY := rfl)
      exact heq_of_eq (by
        change (T.hom ≫ f₁) ≫ I₁.f = T.hom ≫ (f₁ ≫ I₁.f)
        exact Category.assoc T.hom f₁ I₁.f)
    have hs₁ : HEq s₁ s := by
      exact localized_cover_descent_equivShrink_symm_glue_value_heq
        (J := J) (U := U) 𝒰 D hV₁
        (localized_cover_descent_eqToHom_app_heq hq₁ (Opposite.op T) x)
    let K₁ : ((𝒰.pullback I₁.f).pullback T₁.hom).Arrow :=
      ⟨K.Y, K.f, by
        simpa [T₁, V, GrothendieckTopology.Cover.coe_pullback, Category.assoc] using K₀.hf⟩
    let x₁ :=
      (localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I₁ T₁ s₁.1) K₁
    have hT₁hom : T₁.hom ≫ I₁.f = V.hom := by
      change (T.hom ≫ f₁) ≫ I₁.f = T.hom ≫ (f₁ ≫ I₁.f)
      exact Category.assoc T.hom f₁ I₁.f
    have hK₁ :
        HEq
          (K₁.map (Cover.pullbackComp 𝒰 T₁.hom I₁.f).inv)
          K₀ := by
      exact localized_cover_descent_pullbackComp_inv_arrow_heq
        (J := J) (U := U) 𝒰 T₁.hom I₁.f V.hom hT₁hom
        K₁ K₀ rfl (heq_of_eq rfl)
    have hx₁ : HEq x₁ z := by
      refine
        (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
          (J := J) (U := U) 𝒰 D I₁ T₁ s₁.1 K₁).trans ?_
      exact localized_cover_descent_glue_value_app_heq
        (J := J) (U := U) 𝒰 D hV₁ hs₁ hK₁
    let t₁ :=
      (localized_cover_descent_glue_value_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I₁ T₁) s₁
    let e₁ :=
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I₁ T₁ K₁ x₁
    let δ₁ :=
      D.hom (g ≫ f₁ ≫ I₁.f)
        (i₁ := K₀.base) (i₂ := I₁)
        (𝟙 K.Y) (g ≫ f₁)
        (by
          dsimp [K₀, V, g, GrothendieckTopology.Cover.Arrow.base]
          calc
            (𝟙 K.Y) ≫ K.f ≫ T.hom ≫ f₁ ≫ I₁.f =
                K.f ≫ T.hom ≫ f₁ ≫ I₁.f := by
              rw [Category.id_comp]
            _ = (K.f ≫ T.hom) ≫ f₁ ≫ I₁.f :=
              (Category.assoc K.f T.hom (f₁ ≫ I₁.f)).symm)
        (Category.assoc g f₁ I₁.f)
    have hleg₁ : K₁.f ≫ T₁.hom = g ≫ f₁ := by
      dsimp [K₁, T₁, g]
      exact (Category.assoc K.f T.hom f₁).symm
    have hbase₁ : K₁.base.base = K₀.base := by
      refine Cover.Arrow.ext (S := 𝒰) (x := K₁.base.base) (y := K₀.base) rfl ?_
      exact heq_of_eq (by
        change (K₁.f ≫ T₁.hom) ≫ I₁.f = K.f ≫ V.hom
        calc
          (K₁.f ≫ T₁.hom) ≫ I₁.f = K₁.f ≫ T₁.hom ≫ I₁.f :=
            Category.assoc K₁.f T₁.hom I₁.f
          _ = K.f ≫ V.hom := by
            rw [hT₁hom]
            rfl)
    let δ₁raw :=
      D.hom (K.f ≫ T₁.hom ≫ I₁.f)
        (i₁ := K₁.base.base) (i₂ := I₁)
        (𝟙 K.Y) (K.f ≫ T₁.hom)
        (by
          dsimp [K₁, GrothendieckTopology.Cover.Arrow.base]
          simp only [Category.id_comp]
          rw [Category.assoc]
          rfl)
        (Category.assoc K.f T₁.hom I₁.f)
    have he₁raw : HEq e₁ (δ₁raw.hom.app X₀ x₁) := by
      simpa [e₁, δ₁raw, K₁, X₀] using
        localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_app_heq
          (J := J) (U := U) 𝒰 D I₁ T₁ K₁ x₁
    have he₁ : HEq e₁ (δ₁.hom.app X₀ z) := by
      refine he₁raw.trans ?_
      have hDbase₁ : D.obj K₁.base.base = D.obj K₀.base :=
        eq_of_heq (congr_arg_heq (fun A : 𝒰.Arrow ↦ D.obj A) hbase₁)
      have hM₁ :
          ((J.pseudofunctorOver (Type w)).map (𝟙 K.Y).op.toLoc).toFunctor.obj
              (D.obj K₁.base.base) =
            ((J.pseudofunctorOver (Type w)).map (𝟙 K.Y).op.toLoc).toFunctor.obj
              (D.obj K₀.base) :=
        congrArg
          (fun M : Sheaf (J.over K.Y) (Type w) =>
            ((J.pseudofunctorOver (Type w)).map (𝟙 K.Y).op.toLoc).toFunctor.obj M)
          hDbase₁
      have hN₁ :
          ((J.pseudofunctorOver (Type w)).map (K.f ≫ T₁.hom).op.toLoc).toFunctor.obj
              (D.obj I₁) =
            ((J.pseudofunctorOver (Type w)).map (g ≫ f₁).op.toLoc).toFunctor.obj
              (D.obj I₁) :=
        congrArg
          (fun a : K.Y ⟶ I₁.Y =>
            ((J.pseudofunctorOver (Type w)).map a.op.toLoc).toFunctor.obj (D.obj I₁))
          hleg₁
      have hφ₁ : HEq δ₁raw δ₁ := by
        have hq₁' : K.f ≫ T₁.hom ≫ I₁.f = g ≫ f₁ ≫ I₁.f := by
          calc
            K.f ≫ T₁.hom ≫ I₁.f = (K.f ≫ T₁.hom) ≫ I₁.f :=
              (Category.assoc K.f T₁.hom I₁.f).symm
            _ = (g ≫ f₁) ≫ I₁.f :=
              congrArg (fun a : K.Y ⟶ I₁.Y ↦ a ≫ I₁.f) hleg₁
            _ = g ≫ f₁ ≫ I₁.f := Category.assoc g f₁ I₁.f
        have hraw₁ : (𝟙 K.Y) ≫ K₁.base.base.f = K.f ≫ T₁.hom ≫ I₁.f := by
          dsimp [K₁, GrothendieckTopology.Cover.Arrow.base]
          simp only [Category.id_comp]
          rw [Category.assoc]
          rfl
        have hraw₂ : (K.f ≫ T₁.hom) ≫ I₁.f = K.f ≫ T₁.hom ≫ I₁.f :=
          Category.assoc K.f T₁.hom I₁.f
        have hnorm₁ : (𝟙 K.Y) ≫ K₀.base.f = g ≫ f₁ ≫ I₁.f := by
          dsimp [K₀, V, g, GrothendieckTopology.Cover.Arrow.base]
          calc
            (𝟙 K.Y) ≫ K.f ≫ T.hom ≫ f₁ ≫ I₁.f =
                K.f ≫ T.hom ≫ f₁ ≫ I₁.f := by
              rw [Category.id_comp]
            _ = (K.f ≫ T.hom) ≫ f₁ ≫ I₁.f :=
              (Category.assoc K.f T.hom (f₁ ≫ I₁.f)).symm
        have hnorm₂ : (g ≫ f₁) ≫ I₁.f = g ≫ f₁ ≫ I₁.f :=
          Category.assoc g f₁ I₁.f
        simpa [δ₁raw, δ₁] using
          localized_cover_descent_descent_hom_heq_of_eqs
            (J := J) (U := U) 𝒰 D hq₁' hbase₁ rfl
            (heq_of_eq rfl) (heq_of_eq hleg₁)
            hraw₁ hraw₂ hnorm₁ hnorm₂
      exact localized_cover_descent_sheaf_hom_app_heq
        (J := J) hM₁ hN₁ δ₁raw δ₁ hφ₁ (heq_of_eq rfl) hx₁
    have ht₁ : HEq (t₁.1 K₁) e₁ := by
      rw [localized_cover_descent_glue_value_overMap_equiv_component_source_apply]
      rw [localized_cover_descent_glue_family_overMap_equiv_component_source_apply]
    have hvalid₁ :
        (((J.overMapPullback (Type w) T₁.hom).obj (D.obj I₁)).1.map
          (show Over.mk K₁.f ⟶ Over.mk (𝟙 T₁.left) from Over.homMk K₁.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T₁.hom) (M := D.obj I₁)).symm
            (localized_cover_descent_glue_component_equiv_over
              (J := J) (U := U) 𝒰 D I₁ T₁ t₁))) =
        t₁.1 K₁ :=
      localized_cover_descent_glue_component_equiv_over_valid_glue
        (J := J) (U := U) 𝒰 D I₁ T₁ t₁ K₁
    have hinput₁ :
        HEq
          (((J.overMapPullback (Type w) T₁.hom).obj (D.obj I₁)).1.map
            (show Over.mk K₁.f ⟶ Over.mk (𝟙 T₁.left) from Over.homMk K₁.f).op
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := T₁.hom) (M := D.obj I₁)).symm
              (localized_cover_descent_glue_component_equiv_over
                (J := J) (U := U) 𝒰 D I₁ T₁ t₁)))
          (δ₁.hom.app X₀ z) :=
      (heq_of_eq hvalid₁).trans (ht₁.trans he₁)
    have hsource₁ :
        HEq
          (((J.overMapPullback (Type w) T₁.hom).obj (D.obj I₁)).1.map
            (show Over.mk K₁.f ⟶ Over.mk (𝟙 T₁.left) from Over.homMk K₁.f).op
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := T₁.hom) (M := D.obj I₁)).symm
          (localized_cover_descent_glue_component_equiv_over
            (J := J) (U := U) 𝒰 D I₁ T₁ t₁)))
          e₁ :=
      (heq_of_eq hvalid₁).trans ht₁
    have hinput₁raw :
        HEq
          (((J.overMapPullback (Type w) T₁.hom).obj (D.obj I₁)).1.map
            (show Over.mk K₁.f ⟶ Over.mk (𝟙 T₁.left) from Over.homMk K₁.f).op
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := T₁.hom) (M := D.obj I₁)).symm
              (localized_cover_descent_glue_component_equiv_over
                (J := J) (U := U) 𝒰 D I₁ T₁ t₁)))
          (δ₁raw.hom.app X₀ x₁) :=
      hsource₁.trans he₁raw
    let δ₁₂ :=
      D.hom (g ≫ f₁ ≫ I₁.f)
        (i₁ := I₁) (i₂ := I₂)
        (g ≫ f₁) (g ≫ f₂)
        (Category.assoc g f₁ I₁.f)
        h₂
    let δ₁₂' :=
      D.hom (K.f ≫ T₁.hom ≫ I₁.f)
        (i₁ := I₁) (i₂ := I₂)
        (K.f ≫ T₁.hom) (K.f ≫ ((Over.map f₂).obj T).hom)
        (Category.assoc K.f T₁.hom I₁.f)
        (by
          calc
            (K.f ≫ ((Over.map f₂).obj T).hom) ≫ I₂.f =
                K.f ≫ T.hom ≫ f₂ ≫ I₂.f := by
                  change (K.f ≫ (T.hom ≫ f₂)) ≫ I₂.f =
                    K.f ≫ (T.hom ≫ (f₂ ≫ I₂.f))
                  exact
                    (Category.assoc K.f (T.hom ≫ f₂) I₂.f).trans
                      (congrArg (fun e : T.left ⟶ U ↦ K.f ≫ e)
                        (Category.assoc T.hom f₂ I₂.f))
            _ = K.f ≫ T.hom ≫ f₁ ≫ I₁.f := by
                  exact congrArg (fun e : Y ⟶ U ↦ K.f ≫ (T.hom ≫ e)) hf₂
            _ = K.f ≫ T₁.hom ≫ I₁.f := by
                  change K.f ≫ (T.hom ≫ (f₁ ≫ I₁.f)) =
                    K.f ≫ ((T.hom ≫ f₁) ≫ I₁.f)
                  exact congrArg (fun e : T.left ⟶ U ↦ K.f ≫ e)
                    (Category.assoc T.hom f₁ I₁.f).symm)
    have hrestrict :
        HEq
          (((J.overMapPullback (Type w) ((Over.map f₂).obj T).hom).obj (D.obj I₂)).1.map
            (show Over.mk K.f ⟶ Over.mk (𝟙 ((Over.map f₂).obj T).left) from
              Over.homMk K.f).op
            (cast
              (localized_cover_descent_overMap_terminal_section_eq
                (J := J) (f := ((Over.map f₂).obj T).hom) (M := D.obj I₂)).symm
              ((D.hom (f₁ ≫ I₁.f) f₁ f₂ rfl hf₂).hom.app (Opposite.op T)
                (localized_cover_descent_glue_component_equiv_over
                  (J := J) (U := U) 𝒰 D I₁ T₁ t₁))))
          (δ₁₂'.hom.app X₀ (δ₁raw.hom.app X₀ x₁)) := by
      simpa [T₁, K₁, X₀, t₁, δ₁₂', Category.assoc] using
        localized_cover_descent_descent_hom_restrict_terminal_app_heq
          (J := J) (U := U) 𝒰 D T K.f f₁ f₂ rfl hf₂
          (localized_cover_descent_glue_component_equiv_over
            (J := J) (U := U) 𝒰 D I₁ T₁ t₁)
          (y := δ₁raw.hom.app X₀ x₁)
          hinput₁raw
    refine HEq.trans (b := δ₁₂'.hom.app X₀ (δ₁raw.hom.app X₀ x₁)) ?_ ?_
    · simpa [T₁, t₁, s₁, hq₁] using hrestrict
    · have hleg₂' : K.f ≫ ((Over.map f₂).obj T).hom = g ≫ f₂ := by
        dsimp [g]
        exact (Category.assoc K.f T.hom f₂).symm
      have hδ₁₂' : HEq
          (δ₁₂'.hom.app X₀ (δ₁raw.hom.app X₀ x₁))
          (δ₁₂.hom.app X₀ (δ₁.hom.app X₀ z)) := by
        have hM₁₂ :
            ((J.pseudofunctorOver (Type w)).map (K.f ≫ T₁.hom).op.toLoc).toFunctor.obj
                (D.obj I₁) =
              ((J.pseudofunctorOver (Type w)).map (g ≫ f₁).op.toLoc).toFunctor.obj
                (D.obj I₁) :=
          congrArg
            (fun a : K.Y ⟶ I₁.Y =>
              ((J.pseudofunctorOver (Type w)).map a.op.toLoc).toFunctor.obj (D.obj I₁))
            hleg₁
        have hN₁₂ :
            ((J.pseudofunctorOver (Type w)).map
                  (K.f ≫ ((Over.map f₂).obj T).hom).op.toLoc).toFunctor.obj
                (D.obj I₂) =
              ((J.pseudofunctorOver (Type w)).map (g ≫ f₂).op.toLoc).toFunctor.obj
                (D.obj I₂) :=
          congrArg
            (fun a : K.Y ⟶ I₂.Y =>
              ((J.pseudofunctorOver (Type w)).map a.op.toLoc).toFunctor.obj (D.obj I₂))
            hleg₂'
        have hφ₁₂ : HEq δ₁₂' δ₁₂ := by
          have hq₁₂' : K.f ≫ T₁.hom ≫ I₁.f = g ≫ f₁ ≫ I₁.f := by
            calc
              K.f ≫ T₁.hom ≫ I₁.f = (K.f ≫ T₁.hom) ≫ I₁.f :=
                (Category.assoc K.f T₁.hom I₁.f).symm
              _ = (g ≫ f₁) ≫ I₁.f :=
                congrArg (fun a : K.Y ⟶ I₁.Y ↦ a ≫ I₁.f) hleg₁
              _ = g ≫ f₁ ≫ I₁.f := Category.assoc g f₁ I₁.f
          have hleft₁ : (K.f ≫ T₁.hom) ≫ I₁.f = K.f ≫ T₁.hom ≫ I₁.f :=
            Category.assoc K.f T₁.hom I₁.f
          have hleft₂ :
              (K.f ≫ ((Over.map f₂).obj T).hom) ≫ I₂.f =
                K.f ≫ T₁.hom ≫ I₁.f := by
            calc
              (K.f ≫ ((Over.map f₂).obj T).hom) ≫ I₂.f =
                  K.f ≫ T.hom ≫ f₂ ≫ I₂.f := by
                    change (K.f ≫ (T.hom ≫ f₂)) ≫ I₂.f =
                      K.f ≫ (T.hom ≫ (f₂ ≫ I₂.f))
                    exact
                      (Category.assoc K.f (T.hom ≫ f₂) I₂.f).trans
                        (congrArg (fun e : T.left ⟶ U ↦ K.f ≫ e)
                          (Category.assoc T.hom f₂ I₂.f))
              _ = K.f ≫ T.hom ≫ f₁ ≫ I₁.f := by
                    exact congrArg (fun e : Y ⟶ U ↦ K.f ≫ (T.hom ≫ e)) hf₂
              _ = K.f ≫ T₁.hom ≫ I₁.f := by
                    change K.f ≫ (T.hom ≫ (f₁ ≫ I₁.f)) =
                      K.f ≫ ((T.hom ≫ f₁) ≫ I₁.f)
                    exact congrArg (fun e : T.left ⟶ U ↦ K.f ≫ e)
                      (Category.assoc T.hom f₁ I₁.f).symm
          have hright₁ : (g ≫ f₁) ≫ I₁.f = g ≫ f₁ ≫ I₁.f :=
            Category.assoc g f₁ I₁.f
          simpa [δ₁₂', δ₁₂] using
            localized_cover_descent_descent_hom_heq_of_eqs
              (J := J) (U := U) 𝒰 D hq₁₂' rfl rfl
              (heq_of_eq hleg₁) (heq_of_eq hleg₂')
              hleft₁ hleft₂ hright₁ h₂
        have happ := localized_cover_descent_sheaf_hom_app_heq
          (J := J) hM₁₂ hN₁₂ δ₁₂' δ₁₂ hφ₁₂ (heq_of_eq rfl)
          ((HEq.symm he₁raw).trans he₁)
        simpa [δ₁, δ₁₂, X₀] using happ
      simpa [δ₁, δ₁₂] using hδ₁₂'
  · -- Right bridge: normalize the `I₂` q-pulled component source to the same terminal section
    -- `z`, using `hObj₂`, `hObj₂_left`, and the q-pullback object equality.
    let T₂ : Over I₂.Y := (Over.map f₂).obj T
    let X₀ : (Over K.Y)ᵒᵖ := Opposite.op (Over.mk (𝟙 K.Y))
    let hq₂ := localized_cover_descent_q_pullback_presheaf_eq
      (J := J) (U := U) 𝒰
      (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D)
      (f₁ ≫ I₁.f) I₂ f₂ hf₂
    let s₂ : localized_cover_descent_glue_value (J := J) (U := U) 𝒰 D
        ((Over.map I₂.f).obj T₂) :=
      (equivShrink _).symm ((eqToHom hq₂).app (Opposite.op T) x)
    have hV₂ : ((Over.map I₂.f).obj T₂) = V := by
      apply over_mk_hext (𝒞 := C) (B := U) (hY := rfl)
      exact heq_of_eq (by
        change (T.hom ≫ f₂) ≫ I₂.f = T.hom ≫ (f₁ ≫ I₁.f)
        calc
          (T.hom ≫ f₂) ≫ I₂.f = T.hom ≫ (f₂ ≫ I₂.f) :=
            Category.assoc T.hom f₂ I₂.f
          _ = T.hom ≫ (f₁ ≫ I₁.f) :=
            congrArg (fun e : Y ⟶ U ↦ T.hom ≫ e) hf₂)
    have hs₂ : HEq s₂ s := by
      exact localized_cover_descent_equivShrink_symm_glue_value_heq
        (J := J) (U := U) 𝒰 D hV₂
        (localized_cover_descent_eqToHom_app_heq hq₂ (Opposite.op T) x)
    let x₂ :=
      (localized_cover_descent_glue_family_overMap_equiv_direct_source
        (J := J) (U := U) 𝒰 D I₂ T₂ s₂.1) K
    have hT₂hom : T₂.hom ≫ I₂.f = V.hom := by
      change (T.hom ≫ f₂) ≫ I₂.f = T.hom ≫ (f₁ ≫ I₁.f)
      calc
        (T.hom ≫ f₂) ≫ I₂.f = T.hom ≫ (f₂ ≫ I₂.f) :=
          Category.assoc T.hom f₂ I₂.f
        _ = T.hom ≫ (f₁ ≫ I₁.f) :=
          congrArg (fun e : Y ⟶ U ↦ T.hom ≫ e) hf₂
    have hK₂ :
        HEq
          (K.map (Cover.pullbackComp 𝒰 T₂.hom I₂.f).inv)
          K₀ := by
      exact localized_cover_descent_pullbackComp_inv_arrow_heq
        (J := J) (U := U) 𝒰 T₂.hom I₂.f V.hom hT₂hom
        K K₀ rfl (heq_of_eq rfl)
    have hx₂ : HEq x₂ z := by
      refine
        (localized_cover_descent_glue_family_overMap_equiv_direct_source_apply_heq
          (J := J) (U := U) 𝒰 D I₂ T₂ s₂.1 K).trans ?_
      exact localized_cover_descent_glue_value_app_heq
        (J := J) (U := U) 𝒰 D hV₂ hs₂ hK₂
    let t₂ :=
      (localized_cover_descent_glue_value_overMap_equiv_component_source
        (J := J) (U := U) 𝒰 D I₂ T₂) s₂
    let e₂ :=
      localized_cover_descent_pullbackDatum_over_direct_section_equiv_component
        (J := J) (U := U) 𝒰 D I₂ T₂ K x₂
    let δ₂ :=
      D.hom (g ≫ f₁ ≫ I₁.f)
        (i₁ := K₀.base) (i₂ := I₂)
        (𝟙 K.Y) (g ≫ f₂)
        (by
          dsimp [K₀, V, g, GrothendieckTopology.Cover.Arrow.base]
          calc
            (𝟙 K.Y) ≫ K.f ≫ T.hom ≫ f₁ ≫ I₁.f =
                K.f ≫ T.hom ≫ f₁ ≫ I₁.f := by
              rw [Category.id_comp]
            _ = (K.f ≫ T.hom) ≫ f₁ ≫ I₁.f :=
              (Category.assoc K.f T.hom (f₁ ≫ I₁.f)).symm)
        h₂
    have hleg₂ : K.f ≫ T₂.hom = g ≫ f₂ := by
      dsimp [T₂, g]
      exact (Category.assoc K.f T.hom f₂).symm
    have hbase₂ : K.base.base = K₀.base := by
      refine Cover.Arrow.ext (S := 𝒰) (x := K.base.base) (y := K₀.base) rfl ?_
      exact heq_of_eq (by
        change (K.f ≫ T₂.hom) ≫ I₂.f = K.f ≫ V.hom
        calc
          (K.f ≫ T₂.hom) ≫ I₂.f = K.f ≫ T₂.hom ≫ I₂.f :=
            Category.assoc K.f T₂.hom I₂.f
          _ = K.f ≫ V.hom :=
            congrArg (fun e : T.left ⟶ U ↦ K.f ≫ e) hT₂hom)
    have he₂ : HEq e₂ (δ₂.hom.app X₀ z) := by
      have happ₂raw :=
        localized_cover_descent_pullbackDatum_over_direct_section_equiv_component_app_heq
          (J := J) (U := U) 𝒰 D I₂ T₂ K x₂
      refine happ₂raw.trans ?_
      refine localized_cover_descent_sheaf_hom_app_heq ?hM ?hN _ _ ?hφ
        (heq_of_eq rfl) hx₂
      · have hDbase₂ : D.obj K.base.base = D.obj K₀.base :=
          eq_of_heq (congr_arg_heq (fun A : 𝒰.Arrow ↦ D.obj A) hbase₂)
        exact congrArg
          (fun M : Sheaf (J.over K.Y) (Type w) =>
            ((J.pseudofunctorOver (Type w)).map (𝟙 K.Y).op.toLoc).toFunctor.obj M)
          hDbase₂
      · exact congrArg
          (fun a : K.Y ⟶ I₂.Y =>
            ((J.pseudofunctorOver (Type w)).map a.op.toLoc).toFunctor.obj (D.obj I₂))
          hleg₂
      · have hq₂' : K.f ≫ T₂.hom ≫ I₂.f = g ≫ f₁ ≫ I₁.f := by
          calc
            K.f ≫ T₂.hom ≫ I₂.f = (K.f ≫ T₂.hom) ≫ I₂.f :=
              (Category.assoc K.f T₂.hom I₂.f).symm
            _ = (g ≫ f₂) ≫ I₂.f :=
              congrArg (fun a : K.Y ⟶ I₂.Y ↦ a ≫ I₂.f) hleg₂
            _ = g ≫ f₁ ≫ I₁.f := h₂
        exact localized_cover_descent_descent_hom_heq_of_eqs
          (J := J) (U := U) 𝒰 D hq₂' hbase₂ rfl
          (heq_of_eq rfl) (heq_of_eq hleg₂) _ _ _ _
    have ht₂ : HEq (t₂.1 K) e₂ := by
      rw [localized_cover_descent_glue_value_overMap_equiv_component_source_apply]
      rw [localized_cover_descent_glue_family_overMap_equiv_component_source_apply]
    have hvalid₂ :
        (((J.overMapPullback (Type w) T₂.hom).obj (D.obj I₂)).1.map
          (show Over.mk K.f ⟶ Over.mk (𝟙 T₂.left) from Over.homMk K.f).op
          (cast
            (localized_cover_descent_overMap_terminal_section_eq
              (J := J) (f := T₂.hom) (M := D.obj I₂)).symm
            (localized_cover_descent_glue_component_equiv_over
              (J := J) (U := U) 𝒰 D I₂ T₂ t₂))) =
        t₂.1 K :=
      localized_cover_descent_glue_component_equiv_over_valid_glue
        (J := J) (U := U) 𝒰 D I₂ T₂ t₂ K
    simpa [T₂, X₀, δ₂, t₂, s₂] using
      (heq_of_eq hvalid₂).trans (ht₂.trans he₂)

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: the factorization equation `f ≫ I.f = q` in cover coordinates
becomes the corresponding composition equation in the localized opposite category. -/
theorem localized_cover_descent_factorization_toLoc
    (𝒰 : J.Cover U) {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    I.f.op.toLoc ≫ f.op.toLoc = q.op.toLoc := by
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hf)

/-- Helper for Lemma 7.26.4: the inverse of pullback-sheafification compatibility sends the
whiskered sheafification unit back to the sheafification unit of the pulled presheaf. -/
theorem overMap_toSheafify_comp_pushforwardCompatibility_inv
    {X Y : C} (f : X ⟶ Y) (F : (Over Y)ᵒᵖ ⥤ Type w) :
    (Over.map f).op.whiskerLeft (CategoryTheory.toSheafify (J.over Y) F) ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).inv.app F).hom =
      CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) := by
  rw [← (Over.map f).toSheafify_pullbackSheafificationCompatibility
    (Type w) (J.over X) (J.over Y) F]
  have hcomp :
      (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).hom.app F).hom ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).inv.app F).hom =
          𝟙 (CategoryTheory.sheafify (J.over X) ((Over.map f).op ⋙ F)) := by
    have hcompSheaf :
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over X) (J.over Y)).hom.app F) ≫
          (((Over.map f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over X) (J.over Y)).inv.app F) = 𝟙 _ := by
      exact NatTrans.congr_app
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).hom_inv_id) F
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom] using congrArg (fun k => k.hom) hcompSheaf
  calc
    (CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫
          (((Over.map f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over X) (J.over Y)).hom.app F).hom) ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).inv.app F).hom =
      CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫
        ((((Over.map f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over X) (J.over Y)).hom.app F).hom ≫
          (((Over.map f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over X) (J.over Y)).inv.app F).hom) := Category.assoc _ _ _
    _ = CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫ 𝟙 _ := by
      exact congrArg
        (fun k => CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫ k)
        hcomp
    _ = CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) := Category.comp_id _

/-- Helper for Lemma 7.26.4: a postcomposed version of the pullback-sheafification
compatibility unit equation. This keeps later rewrites from depending on the associativity shape
of long presheaf morphism composites. -/
theorem overMap_toSheafify_comp_pushforwardCompatibility_hom_assoc
    {X Y : C} (f : X ⟶ Y) (F : (Over Y)ᵒᵖ ⥤ Type w)
    {R : (Over X)ᵒᵖ ⥤ Type w}
    (g :
      (((Over.map f).sheafPushforwardContinuous (Type w) (J.over X) (J.over Y)).obj
          ((presheafToSheaf (J.over Y) (Type w)).obj F)).1 ⟶ R) :
    CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).hom.app F).hom ≫ g =
      (Over.map f).op.whiskerLeft (CategoryTheory.toSheafify (J.over Y) F) ≫ g := by
  exact congrArg (fun k => k ≫ g)
    ((Over.map f).toSheafify_pullbackSheafificationCompatibility
      (Type w) (J.over X) (J.over Y) F)

/-- Helper for Lemma 7.26.4: the same compatibility in the right-associated shape produced by
long categorical composites. -/
theorem overMap_toSheafify_comp_pushforwardCompatibility_hom_right_assoc
    {X Y : C} (f : X ⟶ Y) (F : (Over Y)ᵒᵖ ⥤ Type w)
    {R : (Over X)ᵒᵖ ⥤ Type w}
    (g :
      (((Over.map f).sheafPushforwardContinuous (Type w) (J.over X) (J.over Y)).obj
          ((presheafToSheaf (J.over Y) (Type w)).obj F)).1 ⟶ R) :
    CategoryTheory.toSheafify (J.over X) ((Over.map f).op ⋙ F) ≫
        ((((Over.map f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over X) (J.over Y)).hom.app F).hom ≫ g) =
      (Over.map f).op.whiskerLeft (CategoryTheory.toSheafify (J.over Y) F) ≫ g := by
  rw [← Category.assoc]
  exact overMap_toSheafify_comp_pushforwardCompatibility_hom_assoc
    (J := J) (f := f) (F := F) g

/-- Helper for Lemma 7.26.4: sheafifying a morphism into an already sheafified component and
then applying the canonical inverse self-sheafification recovers the original presheaf map. -/
theorem toSheafify_comp_sheafifyMap_comp_sheafificationIso_inv
    {X : C} {P : (Over X)ᵒᵖ ⥤ Type w}
    (M : Sheaf (J.over X) (Type w)) (e : P ⟶ M.1) :
    CategoryTheory.toSheafify (J.over X) P ≫
        ((presheafToSheaf (J.over X) (Type w)).map e).hom ≫
        (CategoryTheory.sheafificationIso M).inv.hom =
      e := by
  have hM :
      CategoryTheory.toSheafify (J.over X) M.1 ≫
          (CategoryTheory.sheafificationIso M).inv.hom =
        𝟙 M.1 := by
    exact congrArg (fun f => f.hom) (CategoryTheory.sheafificationIso M).hom_inv_id
  calc
    CategoryTheory.toSheafify (J.over X) P ≫
        ((presheafToSheaf (J.over X) (Type w)).map e).hom ≫
        (CategoryTheory.sheafificationIso M).inv.hom =
      (e ≫ CategoryTheory.toSheafify (J.over X) M.1) ≫
        (CategoryTheory.sheafificationIso M).inv.hom := by
          rw [Category.assoc]
          exact congrArg (fun k => k ≫ (CategoryTheory.sheafificationIso M).inv.hom)
            (CategoryTheory.toSheafify_naturality (J := J.over X) e).symm
    _ = e ≫
        (CategoryTheory.toSheafify (J.over X) M.1 ≫
          (CategoryTheory.sheafificationIso M).inv.hom) := by
          rw [Category.assoc]
    _ = e ≫ 𝟙 M.1 := by
          exact congrArg (fun k => e ≫ k) hM
    _ = e := Category.comp_id e

/-- Helper for Lemma 7.26.4: the previous sheafification cancellation after whiskering by an
over-map. -/
theorem overMap_whiskerLeft_toSheafify_comp_sheafificationIso_inv
    {X Y : C} (f : X ⟶ Y) {P : (Over Y)ᵒᵖ ⥤ Type w}
    (M : Sheaf (J.over Y) (Type w)) (e : P ⟶ M.1) :
    (Over.map f).op.whiskerLeft (CategoryTheory.toSheafify (J.over Y) P) ≫
        (Over.map f).op.whiskerLeft
          (((presheafToSheaf (J.over Y) (Type w)).map e).hom) ≫
        (Over.map f).op.whiskerLeft (CategoryTheory.sheafificationIso M).inv.hom =
      (Over.map f).op.whiskerLeft e := by
  ext Z z
  have hz :=
    congrFun
      (congrArg
        (fun η => η.app ((Over.map f).op.obj Z))
        (toSheafify_comp_sheafifyMap_comp_sheafificationIso_inv
          (J := J) M e))
      z
  simpa only [FunctorToTypes.comp, Category.assoc] using hz

/-- Helper for Lemma 7.26.4: the `mapComp'` comparison for `q = f ≫ I.f`, followed by the
inverse sheafification-pullback compatibility for `I.f`, is the q-pullback rewrite followed by
the sheafification unit on the iterated pullback presheaf. -/
theorem overMap_toSheafify_comp_mapComp'_hom_comp_pushforwardCompatibility_inv
    (𝒰 : J.Cover U) (P : (Over U)ᵒᵖ ⥤ Type w)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    (Over.map q).op.whiskerLeft (CategoryTheory.toSheafify (J.over U) P) ≫
      (((J.pseudofunctorOver (Type w)).mapComp'
        I.f.op.toLoc f.op.toLoc q.op.toLoc
        (localized_cover_descent_factorization_toLoc
          (J := J) (U := U) 𝒰 q I f hf)).hom.toNatTrans.app
          ((presheafToSheaf (J.over U) (Type w)).obj P)).hom ≫
      (Over.map f).op.whiskerLeft
        ((((Over.map I.f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over I.Y) (J.over U)).inv.app P).hom) =
    eqToHom
        (localized_cover_descent_q_pullback_presheaf_eq
          (J := J) (U := U) 𝒰 P q I f hf) ≫
      (Over.map f).op.whiskerLeft
        (CategoryTheory.toSheafify (J.over I.Y) ((Over.map I.f).op ⋙ P)) := by
  subst q
  ext X x
  let T : Over Y := Opposite.unop X
  let Tf : (Over I.Y)ᵒᵖ := Opposite.op ((Over.map f).obj T)
  let S := (presheafToSheaf (J.over U) (Type w)).obj P
  let hq := localized_cover_descent_q_pullback_presheaf_eq
    (J := J) (U := U) 𝒰 P (f ≫ I.f) I f rfl
  have hloc : I.f.op.toLoc ≫ f.op.toLoc = (f ≫ I.f).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  let α :=
    (((J.pseudofunctorOver (Type w)).mapComp'
      I.f.op.toLoc f.op.toLoc (f ≫ I.f).op.toLoc hloc).hom.toNatTrans.app S)
  let y : ((Over.map I.f).op ⋙ P).obj Tf := (eqToHom hq).app X x
  have hObj :
      (Over.map (f ≫ I.f)).obj T =
        (Over.map I.f).obj ((Over.map f).obj T) := by
    apply over_mk_hext (𝒞 := C) (B := U) (hY := rfl)
    exact heq_of_eq (by simp [T, Category.assoc])
  have hunit :
      HEq
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x)
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map I.f).obj ((Over.map f).obj T))) y) := by
    have happ :
        HEq
          ((CategoryTheory.toSheafify (J.over U) P).app
            (Opposite.op ((Over.map (f ≫ I.f)).obj T)))
          ((CategoryTheory.toSheafify (J.over U) P).app
            (Opposite.op ((Over.map I.f).obj ((Over.map f).obj T)))) := by
      exact natTrans_app_heq_of_eq
        (CategoryTheory.toSheafify (J.over U) P) (congrArg Opposite.op hObj)
    exact localized_cover_descent_fun_app_heq_of_type_eqs
      (congrArg (fun Z : Over U => P.obj (Opposite.op Z)) hObj)
      (congrArg
        (fun Z : Over U =>
          (CategoryTheory.sheafify (J.over U) P).obj (Opposite.op Z)) hObj)
      happ (localized_cover_descent_eqToHom_app_heq hq X x).symm
  have hαid :
      HEq
        (α.hom.app X
          ((CategoryTheory.toSheafify (J.over U) P).app
            (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x))
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x) := by
    simpa [α, S, T, hloc] using
      (pf_mapComp'_hom_component_apply_heq
        (J := J)
        (f := I.f.op.toLoc)
        (g' := f.op.toLoc)
        (k := (f ≫ I.f).op.toLoc)
        (hk := hloc)
        S X
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x))
  have hα :
      HEq
        (α.hom.app X
          ((CategoryTheory.toSheafify (J.over U) P).app
            (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x))
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map I.f).obj ((Over.map f).obj T))) y) :=
    hαid.trans hunit
  have hinv :
      (((Over.map I.f).pushforwardContinuousSheafificationCompatibility
          (Type w) (J.over I.Y) (J.over U)).inv.app P).hom.app Tf
        ((CategoryTheory.toSheafify (J.over U) P).app
          (Opposite.op ((Over.map I.f).obj ((Over.map f).obj T))) y) =
      (CategoryTheory.toSheafify (J.over I.Y) ((Over.map I.f).op ⋙ P)).app Tf y := by
    simpa [Tf, T, FunctorToTypes.comp] using
      congrFun
        (congrArg (fun η => η.app Tf)
          (overMap_toSheafify_comp_pushforwardCompatibility_inv
            (J := J) (f := I.f) (F := P)))
        y
  have hmain :
      HEq
        ((((Over.map I.f).pushforwardContinuousSheafificationCompatibility
            (Type w) (J.over I.Y) (J.over U)).inv.app P).hom.app Tf
          (α.hom.app X
            ((CategoryTheory.toSheafify (J.over U) P).app
              (Opposite.op ((Over.map (f ≫ I.f)).obj T)) x)))
        ((CategoryTheory.toSheafify (J.over I.Y) ((Over.map I.f).op ⋙ P)).app Tf y) := by
    have hfun :
        HEq
          ((((Over.map I.f).pushforwardContinuousSheafificationCompatibility
              (Type w) (J.over I.Y) (J.over U)).inv.app P).hom.app Tf)
          ((((Over.map I.f).pushforwardContinuousSheafificationCompatibility
              (Type w) (J.over I.Y) (J.over U)).inv.app P).hom.app Tf) := by
      rfl
    exact (localized_cover_descent_fun_app_heq_of_type_eqs rfl rfl hfun hα).trans
      (heq_of_eq hinv)
  exact eq_of_heq (by
    simpa [T, Tf, S, α, y, hq, hloc, FunctorToTypes.comp,
      localized_cover_descent_factorization_toLoc,
      localized_cover_descent_q_pullback_presheaf_eq,
      Pseudofunctor.DescentData.ofObj, Pseudofunctor.toDescentData,
      Pseudofunctor.mapComp', Pseudofunctor.mapComp'_eq_mapComp,
      GrothendieckTopology.pseudofunctorOver, GrothendieckTopology.overMapPullback,
      GrothendieckTopology.overMapPullbackComp,
      GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
      GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
      GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map_hom_app,
      Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans,
      eqToHom_map, eqToHom_refl, eqToHom_app, Quiver.Hom.toLoc_as,
      Quiver.Hom.unop_op, Category.id_comp, Category.comp_id, Category.assoc] using hmain)

/-- Helper for Lemma 7.26.4: after pulling the sheafified glued object along a factorization
`q = f ≫ I.f`, the component sheaf comparison restricts to the q-normalized presheaf
comparison. -/
theorem localized_cover_descent_q_component_sheaf_hom_to_presheaf_hom
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {Y : C} (q : Y ⟶ U) (I : 𝒰.Arrow) (f : Y ⟶ I.Y)
    (hf : f ≫ I.f = q) :
    (Over.map q).op.whiskerLeft
        (CategoryTheory.toSheafify (J.over U)
          (localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D)) ≫
      (((J.pseudofunctorOver (Type w)).mapComp'
        I.f.op.toLoc f.op.toLoc q.op.toLoc
        (localized_cover_descent_factorization_toLoc
          (J := J) (U := U) 𝒰 q I f hf)).hom.toNatTrans.app
          (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D)).hom ≫
      (((J.pseudofunctorOver (Type w)).map f.op.toLoc).toFunctor.map
        (localized_cover_descent_glue_component_sheaf_iso
          (J := J) (U := U) 𝒰 D I).hom).hom =
    localized_cover_descent_q_component_presheaf_hom
      (J := J) (U := U) 𝒰 D q I f hf := by
  let P := localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D
  let e := localized_cover_descent_glue_component_presheaf_iso (J := J) (U := U) 𝒰 D I
  let hq := localized_cover_descent_q_pullback_presheaf_eq
    (J := J) (U := U) 𝒰 P q I f hf
  let γI :=
    (((Over.map I.f).pushforwardContinuousSheafificationCompatibility
      (Type w) (J.over I.Y) (J.over U)).inv.app P).hom
  let γe := ((presheafToSheaf (J.over I.Y) (Type w)).map e.hom).hom
  let γD := (CategoryTheory.sheafificationIso (D.obj I)).inv.hom
  have hfirst :=
    overMap_toSheafify_comp_mapComp'_hom_comp_pushforwardCompatibility_inv
      (J := J) (U := U) 𝒰 P q I f hf
  have hsecond :=
    overMap_whiskerLeft_toSheafify_comp_sheafificationIso_inv
      (J := J) (f := f) (M := D.obj I) e.hom
  have hfull :
      ((Over.map q).op.whiskerLeft
          (CategoryTheory.toSheafify (J.over U) P) ≫
        (((J.pseudofunctorOver (Type w)).mapComp'
          I.f.op.toLoc f.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I f hf)).hom.toNatTrans.app
            ((presheafToSheaf (J.over U) (Type w)).obj P)).hom ≫
        (Over.map f).op.whiskerLeft γI) ≫
        (Over.map f).op.whiskerLeft γe ≫
        (Over.map f).op.whiskerLeft γD =
      eqToHom hq ≫ (Over.map f).op.whiskerLeft e.hom := by
    calc
      ((Over.map q).op.whiskerLeft
          (CategoryTheory.toSheafify (J.over U) P) ≫
        (((J.pseudofunctorOver (Type w)).mapComp'
          I.f.op.toLoc f.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I f hf)).hom.toNatTrans.app
            ((presheafToSheaf (J.over U) (Type w)).obj P)).hom ≫
        (Over.map f).op.whiskerLeft γI) ≫
        (Over.map f).op.whiskerLeft γe ≫
        (Over.map f).op.whiskerLeft γD =
          (eqToHom hq ≫
            (Over.map f).op.whiskerLeft
              (CategoryTheory.toSheafify (J.over I.Y) ((Over.map I.f).op ⋙ P))) ≫
            (Over.map f).op.whiskerLeft γe ≫
            (Over.map f).op.whiskerLeft γD := by
            exact congrArg
              (fun k => k ≫ (Over.map f).op.whiskerLeft γe ≫
                (Over.map f).op.whiskerLeft γD)
              hfirst
      _ = eqToHom hq ≫
            ((Over.map f).op.whiskerLeft
                (CategoryTheory.toSheafify (J.over I.Y) ((Over.map I.f).op ⋙ P)) ≫
              (Over.map f).op.whiskerLeft γe ≫
              (Over.map f).op.whiskerLeft γD) := by
            rfl
      _ = eqToHom hq ≫ (Over.map f).op.whiskerLeft e.hom := by
            exact congrArg (fun k => eqToHom hq ≫ k) hsecond
  simpa [P, e, hq, γI, γe, γD,
    localized_cover_descent_glue_sheaf,
    localized_cover_descent_q_component_presheaf_hom,
    localized_cover_descent_glue_component_sheaf_iso,
    localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso,
    Pseudofunctor.DescentData.ofObj, Pseudofunctor.toDescentData,
    Pseudofunctor.mapComp', Pseudofunctor.mapComp'_eq_mapComp,
    GrothendieckTopology.pseudofunctorOver, GrothendieckTopology.overMapPullback,
    GrothendieckTopology.overMapPullbackComp,
    GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map_hom_app,
    Functor.toSheafify_pullbackSheafificationCompatibility,
    overMap_toSheafify_comp_pushforwardCompatibility_inv,
    CategoryTheory.toSheafify_sheafifyLift,
    CategoryTheory.sheafificationIso, CategoryTheory.isoSheafify_inv,
    CategoryTheory.sheafifyMap, Functor.map_comp,
    Functor.isoWhiskerLeft_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans,
    eqToHom_map, eqToHom_refl, eqToHom_app, Quiver.Hom.toLoc_as,
    Quiver.Hom.unop_op, FunctorToTypes.comp,
    Category.id_comp, Category.comp_id, Category.assoc] using hfull

omit [UnivLE.{max u v, w}] in
/-- Helper for Lemma 7.26.4: for the descent datum induced by a global sheaf, precomposing
its overlap transition with the left `mapComp'` comparison cancels the inverse boundary and
leaves the right `mapComp'` comparison. -/
theorem localized_cover_descent_toDescentData_hom_after_mapComp'_hom
    (𝒰 : J.Cover U) (M : Sheaf (J.over U) (Type w))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : 𝒰.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) :
    (((J.pseudofunctorOver (Type w)).mapComp'
        I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
        (localized_cover_descent_factorization_toLoc
          (J := J) (U := U) 𝒰 q I₁ f₁ hf₁)).hom.toNatTrans.app M).hom ≫
      (((((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj M).hom q f₁ f₂ hf₁ hf₂).hom) =
    (((J.pseudofunctorOver (Type w)).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (localized_cover_descent_factorization_toLoc
          (J := J) (U := U) 𝒰 q I₂ f₂ hf₂)).hom.toNatTrans.app M).hom := by
  have hSheaf :
      ((J.pseudofunctorOver (Type w)).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I₁ f₁ hf₁)).hom.toNatTrans.app M ≫
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)).obj M).hom q f₁ f₂ hf₁ hf₂ =
      ((J.pseudofunctorOver (Type w)).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I₂ f₂ hf₂)).hom.toNatTrans.app M := by
    dsimp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
    simpa only using
      (Cat.Hom.hom_inv_id_toNatTrans_app_assoc
        ((J.pseudofunctorOver (Type w)).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I₁ f₁ hf₁))
        M
        (((J.pseudofunctorOver (Type w)).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (localized_cover_descent_factorization_toLoc
            (J := J) (U := U) 𝒰 q I₂ f₂ hf₂)).hom.toNatTrans.app M))
  simpa only [ObjectProperty.FullSubcategory.comp_hom] using
    congrArg (fun k => k.hom) hSheaf

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: component isomorphisms satisfying
the descent-data overlap square assemble into the final descent-data isomorphism. -/
noncomputable def localized_cover_descent_glued_descent_iso_of_components
    (𝒰 : J.Cover U)
    (D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f))
    (e : ∀ I : 𝒰.Arrow,
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj
          (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D)).obj I ≅
        D.obj I)
    (comm :
      ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ : 𝒰.Arrow⦄
        (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
        (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
        ((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.map (e I₁).hom ≫
            D.hom q f₁ f₂ hf₁ hf₂ =
          ((((J.pseudofunctorOver (Type w)).toDescentData
            (fun I : 𝒰.Arrow ↦ I.f)).obj
              (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D)).hom
                q f₁ f₂ hf₁ hf₂) ≫
            ((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.map
              (e I₂).hom) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).obj
        (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D) ≅ D :=
  -- The descent-data constructor is exactly the final assembly once the component comparisons
  -- and their overlap naturality are available.
  Pseudofunctor.DescentData.isoMk e comm

/-- Helper for Lemma 7.26.4: the component sheaf isomorphisms for the glued sheaf satisfy the
descent-data transition square. -/
theorem localized_cover_descent_glued_descent_iso_comm
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰) :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ : 𝒰.Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
      ((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.map
          (localized_cover_descent_glue_component_sheaf_iso
            (J := J) (U := U) 𝒰 D I₁).hom ≫
        D.hom q f₁ f₂ hf₁ hf₂ =
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj
          (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D)).hom
          q f₁ f₂ hf₁ hf₂ ≫
      ((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.map
          (localized_cover_descent_glue_component_sheaf_iso
            (J := J) (U := U) 𝒰 D I₂).hom := by
  intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
  -- Reduce the sheaf morphism square to the underlying sheafified presheaf square, where the
  -- q-normalized component comparison has already been checked.
  let P := localized_cover_descent_glue_presheaf (J := J) (U := U) 𝒰 D
  let S := localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D
  let h₁loc :=
    localized_cover_descent_factorization_toLoc (J := J) (U := U) 𝒰 q I₁ f₁ hf₁
  let αIso :=
    ((J.pseudofunctorOver (Type w)).mapComp'
      I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc h₁loc)
  let α₁ := αIso.hom.toNatTrans.app S
  let α₁' :
      ((J.pseudofunctorOver (Type w)).map q.op.toLoc).toFunctor.obj S ⟶
        ((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.obj
          ((J.overMapPullback (Type w) I₁.f).obj S) :=
    α₁
  let βIso := (Over.map q).pushforwardContinuousSheafificationCompatibility
    (Type w) (J.over Y) (J.over U)
  let β := βIso.hom.app P
  let β' :
      (presheafToSheaf (J.over Y) (Type w)).obj ((Over.map q).op ⋙ P) ⟶
        ((J.pseudofunctorOver (Type w)).map q.op.toLoc).toFunctor.obj S :=
    β
  letI : IsIso α₁' := by
    dsimp [α₁', α₁]
    exact NatIso.hom_app_isIso (Cat.Hom.toNatIso αIso) S
  letI : Epi α₁' := IsIso.epi_of_iso α₁'
  letI : IsIso β' := by
    dsimp [β', β]
    exact NatIso.hom_app_isIso βIso P
  letI : Epi β' := IsIso.epi_of_iso β'
  let M₂ := ((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.obj (D.obj I₂)
  rw [← (cancel_epi α₁')]
  refine (cancel_epi β').1 ?_
  apply Sheaf.hom_ext
  refine CategoryTheory.sheafify_hom_ext
    (J := J.over Y)
    (P := (Over.map q).op ⋙ P)
    (Q := M₂.1)
    (η := ((β' ≫ α₁' ≫
      ((J.pseudofunctorOver (Type w)).map f₁.op.toLoc).toFunctor.map
          (localized_cover_descent_glue_component_sheaf_iso
            (J := J) (U := U) 𝒰 D I₁).hom ≫
        D.hom q f₁ f₂ hf₁ hf₂).hom))
    (γ := ((β' ≫ α₁' ≫
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj S).hom q f₁ f₂ hf₁ hf₂ ≫
        ((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.map
          (localized_cover_descent_glue_component_sheaf_iso
            (J := J) (U := U) 𝒰 D I₂).hom).hom))
    M₂.property ?_
  simp only [S, M₂, βIso, β, β', αIso, α₁, α₁',
    localized_cover_descent_glue_component_sheaf_iso,
    localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso,
    CategoryTheory.sheafificationIso, CategoryTheory.isoSheafify_inv,
    ObjectProperty.FullSubcategory.comp_hom]
  calc
    CategoryTheory.toSheafify (J.over Y) ((Over.map q).op ⋙ P) ≫ _ =
        localized_cover_descent_q_component_presheaf_hom
          (J := J) (U := U) 𝒰 D q I₁ f₁ hf₁ ≫
        (D.hom q f₁ f₂ hf₁ hf₂).hom := by
      let p₁ := localized_cover_descent_q_component_presheaf_hom
        (J := J) (U := U) 𝒰 D q I₁ f₁ hf₁
      refine (overMap_toSheafify_comp_pushforwardCompatibility_hom_right_assoc
        (J := J) (f := q) (F := P) _).trans ?_
      have hcomp₁ :=
        congrArg (fun k => k ≫ (D.hom q f₁ f₂ hf₁ hf₂).hom)
          (localized_cover_descent_q_component_sheaf_hom_to_presheaf_hom
            (J := J) (U := U) 𝒰 D q I₁ f₁ hf₁)
      simpa only [S, βIso, β, β', αIso, α₁, α₁', p₁, P,
        localized_cover_descent_glue_component_sheaf_iso,
        localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso,
        Pseudofunctor.DescentData.ofObj, Pseudofunctor.toDescentData,
        Pseudofunctor.mapComp', Pseudofunctor.mapComp'_eq_mapComp,
        GrothendieckTopology.pseudofunctorOver, GrothendieckTopology.overMapPullback,
        GrothendieckTopology.overMapPullbackComp,
        GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
        Functor.toSheafify_pullbackSheafificationCompatibility,
        CategoryTheory.sheafificationIso, CategoryTheory.isoSheafify_inv,
        CategoryTheory.sheafifyMap, Functor.map_comp, Functor.isoWhiskerLeft_hom,
        ObjectProperty.FullSubcategory.comp_hom, eqToHom_map, eqToHom_refl,
        Category.id_comp, Category.comp_id,
        Category.assoc] using hcomp₁
    _ = localized_cover_descent_q_component_presheaf_hom
          (J := J) (U := U) 𝒰 D q I₂ f₂ hf₂ :=
      localized_cover_descent_q_component_presheaf_hom_descent
        (J := J) (U := U) 𝒰 D q f₁ f₂ hf₁ hf₂
    _ = CategoryTheory.toSheafify (J.over Y) ((Over.map q).op ⋙ P) ≫ _ := by
      let p₂ := localized_cover_descent_q_component_presheaf_hom
        (J := J) (U := U) 𝒰 D q I₂ f₂ hf₂
      symm
      refine (overMap_toSheafify_comp_pushforwardCompatibility_hom_right_assoc
        (J := J) (f := q) (F := P) _).trans ?_
      have hcomp₂ :=
        localized_cover_descent_q_component_sheaf_hom_to_presheaf_hom
          (J := J) (U := U) 𝒰 D q I₂ f₂ hf₂
      have htransition :=
        localized_cover_descent_toDescentData_hom_after_mapComp'_hom
          (J := J) (U := U) 𝒰 S q f₁ f₂ hf₁ hf₂
      have htransitionPost :=
        congrArg
          (fun k =>
            (Over.map q).op.whiskerLeft
                (CategoryTheory.toSheafify (J.over U) P) ≫
              k ≫
              (((J.pseudofunctorOver (Type w)).map f₂.op.toLoc).toFunctor.map
                (localized_cover_descent_glue_component_sheaf_iso
                  (J := J) (U := U) 𝒰 D I₂).hom).hom)
          htransition
      exact (by
        simpa only [S, p₂, P, h₁loc,
          localized_cover_descent_glue_component_sheaf_iso,
          localized_cover_descent_glue_component_sheaf_iso_of_presheaf_iso,
          CategoryTheory.sheafificationIso, CategoryTheory.isoSheafify_inv,
          CategoryTheory.sheafifyMap, Functor.map_comp, Functor.isoWhiskerLeft_hom,
          ObjectProperty.FullSubcategory.comp_hom,
          Category.id_comp, Category.comp_id, Category.assoc] using
          htransitionPost.trans hcomp₂)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: the sheafified glued presheaf has
descent datum canonically isomorphic to the fixed-cover datum being glued. -/
noncomputable def localized_cover_descent_glued_descent_iso
    (𝒰 : J.Cover U)
    (D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f)) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).obj
        (localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D) ≅ D :=
  localized_cover_descent_glued_descent_iso_of_components
    (J := J) (U := U) 𝒰 D
    (fun I ↦ localized_cover_descent_glue_component_sheaf_iso (J := J) (U := U) 𝒰 D I)
    (localized_cover_descent_glued_descent_iso_comm (J := J) (U := U) 𝒰 D)

/-- Helper for Chap07 Lemma 7 26 4/DirectSourceComparison: every fixed-cover descent datum
should be represented by a sheaf on the localized site `J.over U`. -/
theorem localized_cover_descent_glued_essImage
    (𝒰 : J.Cover U)
    (D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f)) :
    (((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).essImage D) := by
  -- The source-style compatible-family presheaf supplies the global object after sheafification;
  -- the remaining descent-data comparison is isolated in the named gluing isomorphism above.
  exact ⟨localized_cover_descent_glue_sheaf (J := J) (U := U) 𝒰 D,
    ⟨localized_cover_descent_glued_descent_iso (J := J) (U := U) 𝒰 D⟩⟩

/-- Helper for Lemma 7.26.4: the descent-data functor attached to a fixed cover `𝒰` of `U` is
essentially surjective. -/
theorem localized_cover_descent_essSurj
    (𝒰 : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- Package the objectwise glued essential-image witness as essential surjectivity.
  exact localized_cover_descent_essSurj_of_glued_objects
    (J := J) (U := U) 𝒰
    (fun D ↦ localized_cover_descent_glued_essImage (J := J) (U := U) 𝒰 D)

/-- Owner-level companion to Lemma 7.26.4: for a fixed cover `𝒰`, the localized sheaf
pseudofunctor satisfies effective descent for the presieve generated by the cover arrows. -/
theorem localizedSheafPseudofunctorOver_isStackFor_cover
    (𝒰 : J.Cover U) :
    (J.pseudofunctorOver (Type w)).IsStackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Combine the fixed-cover prestack theorem with the glued-object essential surjectivity.
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  let hFullyFaithful :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).FullyFaithful :=
    localized_cover_descent_fullyFaithful (J := J) (U := U) 𝒰
  let hEssSurj :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).EssSurj :=
    localized_cover_descent_essSurj (J := J) (U := U) 𝒰
  exact
    { faithful := hFullyFaithful.faithful
      full := hFullyFaithful.full
      essSurj := hEssSurj }

end

end GrothendieckTopology
end CategoryTheory
