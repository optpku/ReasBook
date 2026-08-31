module

public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

/- Domain-style sampling for Remark 4.21.6:
- primary domain: filtered colimits in category theory, specialized to preorder indexing categories
  and single-object diagrams in `Type`;
- sampled owner API:
  `Finite.exists_le`,
  `IsTop`,
  `Preorder.isTerminalTop`,
  `isIso_ι_of_isTerminal`,
  `SingleObj.functor`,
  `CategoryTheory.Limits.Types.Image`,
  `Set.rangeFactorization`;
- best owner abstraction: the source-facing Boolean idempotent diagram built via
  `SingleObj.functor`, together with the canonical order-theoretic owner `IsTop`, the colimit
  comparison from a terminal object in a preorder category, and the canonical `Type`-image owner
  for the colimit vertex of the Boolean example;
- primitive data: an idempotent endomorphism `f : End X`;
- derived API: the Boolean single-object diagram, its image cocone, the colimit proof for that
  cocone, and the finite-directed/top-stage colimit consequences. -/

/- Source/core/bridge triage for Remark 4.21.6:
- `source-facing`: finite directed preorders have a greatest element, and the Boolean filtered
  diagram attached to an idempotent endomorphism has colimit the image of that endomorphism.
- `core/canonical`: `IsDirectedOrder`, `Finite.exists_le`, `IsTop`, `Preorder.isTerminalTop`,
  `isIso_ι_of_isTerminal`, `SingleObj.functor`, `CategoryTheory.Limits.Types.Image`, and
  `Set.rangeFactorization`.
- `bridge/view`: the canonical cocone from the Boolean idempotent diagram to
  `CategoryTheory.Limits.Types.Image f`, its colimit proof, and the induced `HasColimit` instance
  used by the counterexample.
-/

section BoolIdempotent

variable {X : Type u}

/-- Auxiliary multiplication rule for the Boolean action associated to an idempotent endomorphism. -/
-- Proof sketch: split on the two Boolean values and reduce the nontrivial case to the idempotence
-- relation `f ≫ f = f`.
lemma bool_idempotent_end_hom_map_mul (f : End X) (hf : f ≫ f = f) (a b : Bool) :
    (cond (a * b) (1 : End X) f : End X) = (cond a (1 : End X) f) * cond b (1 : End X) f := by
  cases a <;> cases b
  · have h : false * false = false := by decide
    simp [h, hf]
  · have h : false * true = false := by decide
    simp [h]
  · have h : true * false = false := by decide
    simp [h]
  · have h : true * true = true := by decide
    simp [h]

def bool_idempotent_end_hom (f : End X) (hf : f ≫ f = f) : Bool →* End X where
  toFun a := cond a (𝟙 X) f
  map_one' := rfl
  map_mul' := bool_idempotent_end_hom_map_mul f hf

/-- The `SingleObj Bool` diagram attached to an idempotent endomorphism `f`, sending `true` to
`𝟙` and `false` to `f`. This is the source-facing owner object for the Boolean-idempotent clause
of Remark 4.21.6. -/
def bool_idempotent_diagram (f : End X) (hf : f ≫ f = f) :
    SingleObj Bool ⥤ Type u :=
  SingleObj.functor (bool_idempotent_end_hom f hf)

lemma bool_idempotent_rangeFactorization_naturality (f : End X) (hf : f ≫ f = f)
    (a : Bool) :
    (cond a (1 : End X) f : End X) ≫ Set.rangeFactorization f = Set.rangeFactorization f := by
  cases a
  · ext x
    change f (f x) = f x
    simpa using congrFun hf x
  · rfl

/-- The cocone on the Boolean idempotent diagram with vertex `Set.range f`. -/
def bool_idempotent_diagram_image_cocone (f : End X) (hf : f ≫ f = f) :
    Cocone (bool_idempotent_diagram f hf) where
  pt := Limits.Types.Image f
  ι :=
    { app := fun _ ↦ Set.rangeFactorization f
      naturality := fun _ _ a ↦ bool_idempotent_rangeFactorization_naturality f hf a }

private lemma bool_idempotent_mem_range_fixed (f : End X) (hf : f ≫ f = f)
    (x : Limits.Types.Image f) : f x.1 = x.1 := by
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨y, rfl⟩
  exact congrFun hf y

/- Remark 4.21.6 (order-theoretic ingredient): with Lean's `≤`-oriented convention for directed
preorders, the existence of a greatest element in a finite directed preorder is the specialization
of `Finite.exists_le` to the identity map. -/
recall Finite.exists_le

/- Remark 4.21.6 (colimit ingredient): if a preorder index has a top element, then that top object
is terminal via `Preorder.isTerminalTop`, and `isIso_ι_of_isTerminal` identifies the colimit with
the top stage. -/
recall Preorder.isTerminalTop

/- Companion recall for the terminal-stage colimit identification used above. -/
recall isIso_ι_of_isTerminal

section FiniteDirectedPreorder

variable {I : Type u} [Preorder I]

section

variable [Finite I] [Nonempty I] [IsDirectedOrder I]

/-- A finite directed preorder has a greatest element. -/
theorem exists_isTop_of_finite_directed : ∃ top : I, IsTop top := by
  obtain ⟨top, htop⟩ := Finite.exists_le (fun i : I ↦ i)
  exact ⟨top, htop⟩

end

variable {C : Type v} [Category.{w} C]

/-- If `top` is greatest in a preorder index category, then any colimit over that preorder is
already the stage at `top`. -/
theorem isIso_ι_of_isTop {top : I} (htop : IsTop top) (F : I ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F top) := by
  refine IsTop.rec (fun [OrderTop I] ↦ ?_) top htop
  simpa using
    (isIso_ι_of_isTerminal (Preorder.isTerminalTop I) F : IsIso (colimit.ι F (⊤ : I)))

section

variable [Finite I] [Nonempty I] [IsDirectedOrder I]

/-- In a finite directed preorder, any colimit is canonically the top stage. -/
theorem exists_topStage_of_finite_directed (F : I ⥤ C) [HasColimit F] :
    ∃ top : I, IsTop top ∧ IsIso (colimit.ι F top) := by
  obtain ⟨top, htop⟩ : ∃ top : I, IsTop top := exists_isTop_of_finite_directed
  exact ⟨top, htop, isIso_ι_of_isTop htop F⟩

end

end FiniteDirectedPreorder

/-- The single-object Boolean category is a finite filtered category. -/
instance singleObjBool_isFiltered : IsFiltered (SingleObj Bool) where
  cocone_objs _ _ := ⟨SingleObj.star Bool, 𝟙 _, 𝟙 _, trivial⟩
  cocone_maps := by
    intro X Y f g
    cases X
    cases Y
    refine ⟨SingleObj.star Bool, false, ?_⟩
    change Bool at f
    change Bool at g
    cases f <;> cases g <;> rfl
  nonempty := ⟨SingleObj.star Bool⟩

/-- For the single-object Boolean diagram of an idempotent endomorphism, the colimit is captured by
its image. -/
-- Proof sketch: the cocone leg is `x ↦ f x`, and every cocone on the Boolean diagram is constant
-- along `f`; this makes the image cocone universal.
def bool_idempotent_diagram_isColimit_image (f : End X) (hf : f ≫ f = f) :
    IsColimit (bool_idempotent_diagram_image_cocone f hf) where
  desc s x := s.ι.app (SingleObj.star Bool) x.1
  fac s j := by
    cases j
    ext x
    simpa using congrFun (s.w false) x
  uniq s m hm := by
    ext x
    have hx : Set.rangeFactorization f x.1 = x := by
      ext
      exact bool_idempotent_mem_range_fixed f hf x
    simpa [bool_idempotent_diagram_image_cocone, hx] using
      congrFun (hm (SingleObj.star Bool)) x.1

/-- The canonical colimit cocone for the Boolean idempotent diagram, with vertex the image of the
idempotent endomorphism. -/
def bool_idempotent_diagram_colimitCocone (f : End X) (hf : f ≫ f = f) :
    ColimitCocone (bool_idempotent_diagram f hf) where
  cocone := bool_idempotent_diagram_image_cocone f hf
  isColimit := bool_idempotent_diagram_isColimit_image f hf

instance bool_idempotent_diagram_hasColimit (f : End X) (hf : f ≫ f = f) :
    HasColimit (bool_idempotent_diagram f hf) :=
  HasColimit.mk (bool_idempotent_diagram_colimitCocone f hf)

/-- The colimit of the Boolean idempotent diagram is canonically the image of the idempotent
endomorphism. -/
noncomputable def bool_idempotent_diagram_colimitIsoImage (f : End X) (hf : f ≫ f = f) :
    colimit (bool_idempotent_diagram f hf) ≅ Limits.Types.Image f :=
  colimit.isoColimitCocone (bool_idempotent_diagram_colimitCocone f hf)

@[simp] theorem bool_idempotent_diagram_colimitIsoImage_hom_ι (f : End X) (hf : f ≫ f = f) :
    colimit.ι (bool_idempotent_diagram f hf) (SingleObj.star Bool) ≫
        (bool_idempotent_diagram_colimitIsoImage f hf).hom =
      Set.rangeFactorization f := by
  exact colimit.isoColimitCocone_ι_hom (bool_idempotent_diagram_colimitCocone f hf)
    (SingleObj.star Bool)

/-- The constant-false idempotent endomorphism of `Bool`. -/
def bool_constant_false_end : End Bool := fun _ ↦ false

theorem bool_constant_false_end_idempotent :
    bool_constant_false_end ≫ bool_constant_false_end = bool_constant_false_end := by
  ext b
  rfl

/-- The constant-false Boolean example shows that a finite filtered colimit in `Type` need not be a
trivial stage value. -/
-- Proof sketch: the chosen colimit cocone has singleton point `Set.range (fun _ ↦ false)`,
-- and its unique cocone leg identifies both elements of `Bool`.
theorem bool_constant_false_diagram_colimit_iota_not_iso :
    ¬ IsIso
      (colimit.ι
        (bool_idempotent_diagram bool_constant_false_end bool_constant_false_end_idempotent)
        (SingleObj.star Bool)) := by
  intro h
  letI := h
  have himage :
      IsIso
        ((bool_idempotent_diagram_image_cocone bool_constant_false_end
          bool_constant_false_end_idempotent).ι.app (SingleObj.star Bool)) := by
    simpa using
      (show IsIso
        (colimit.ι
            (bool_idempotent_diagram bool_constant_false_end
              bool_constant_false_end_idempotent)
            (SingleObj.star Bool) ≫
          (bool_idempotent_diagram_colimitIsoImage bool_constant_false_end
            bool_constant_false_end_idempotent).hom) by
        infer_instance)
  have hbijective : Function.Bijective (Set.rangeFactorization bool_constant_false_end) := by
    change Function.Bijective
      (((bool_idempotent_diagram_image_cocone bool_constant_false_end
          bool_constant_false_end_idempotent).ι.app (SingleObj.star Bool)))
    exact (isIso_iff_bijective _).1 himage
  have hfactorization_not_injective :
      ¬ Function.Injective (Set.rangeFactorization bool_constant_false_end) := by
    rw [Set.rangeFactorization_injective]
    intro h_injective
    exact Bool.false_ne_true (h_injective rfl)
  exact hfactorization_not_injective hbijective.1

end BoolIdempotent
