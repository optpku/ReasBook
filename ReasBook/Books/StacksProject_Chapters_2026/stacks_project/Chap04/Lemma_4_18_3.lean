module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import stacks_project.Chap04.Lemma_4_18_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v' u' v u

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Lemma 4.18.3:
- primary domain: finite nonempty limits in `CategoryTheory.Limits`;
- sampled owner API:
  `HasFiniteLimits`,
  `HasFiniteConnectedLimits`,
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`,
  `hasPullbacks_of_hasBinaryProducts_of_hasEqualizers`;
- best owner abstraction: the file-local owner `HasFiniteNonemptyLimits`, with the chapter-level
  owner `HasFiniteConnectedLimits` and the mathlib limit-construction theorems as the canonical
  supporting API;
- primitive data: the owner field assigning `HasLimitsOfShape J C` to each finite nonempty shape
  `J`;
- derived API: the shape-transfer instance, the accessors to binary products/equalizers/pullbacks,
  and the equivalence theorems below;
- layer triage:
  - `source-facing`: the equivalence statements `finite_nonempty_limits_tfae`,
    `finite_nonempty_limits_iff_binary_products_and_equalizers`, and
    `finite_nonempty_limits_iff_binary_products_and_pullbacks`;
  - `core/canonical`: `HasFiniteNonemptyLimits`;
  - `bridge/view`: the shape instance and the derived binary-product/connected-limit/equalizer/
    pullback instances. -/

/-- A category has finite nonempty limits if it has limits of every finite nonempty diagram. -/
class HasFiniteNonemptyLimits (C : Type u) [Category.{v} C] : Prop where
  /-- A finite nonempty shape admits limits in the ambient category. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] : HasLimitsOfShape J C

/-- A category with finite nonempty limits has limits of each finite nonempty shape. -/
instance hasLimitsOfShape_of_hasFiniteNonemptyLimits
    [HasFiniteNonemptyLimits C] (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    HasLimitsOfShape J C := by
  refine @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteNonemptyLimits.out

attribute [instance 100] hasLimitsOfShape_of_hasFiniteNonemptyLimits

/-- If `C` has limits of a fixed size, then it has finite nonempty limits. -/
lemma hasFiniteNonemptyLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteNonemptyLimits C := by
  letI : HasFiniteLimits C := hasFiniteLimits_of_hasLimitsOfSize C
  exact ⟨fun J _ _ _ ↦ inferInstance⟩

/-- We can derive finite nonempty limits by supplying them in one arbitrary universe. -/
theorem hasFiniteNonemptyLimits_of_hasFiniteNonemptyLimits_of_size
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J], HasLimitsOfShape J C) :
    HasFiniteNonemptyLimits C where
  out := fun J _ _ _ ↦ by
    haveI : Nonempty (ULiftHom.{w} (ULift.{w} J)) := by
      rcases ‹Nonempty J› with ⟨j⟩
      exact ⟨ULift.up j⟩
    haveI := h (ULiftHom.{w} (ULift.{w} J))
    exact hasLimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv J).symm

/-- Unpack `HasFiniteNonemptyLimits` into the corresponding family of limit instances. -/
theorem hasFiniteNonemptyLimits_iff :
    HasFiniteNonemptyLimits C ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J], HasLimitsOfShape J C := by
  constructor
  · intro h J _ _ _
    letI := h
    infer_instance
  · intro h
    exact hasFiniteNonemptyLimits_of_hasFiniteNonemptyLimits_of_size C h

/-- Finite limits are in particular finite nonempty limits. -/
instance hasFiniteNonemptyLimits_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteNonemptyLimits C where
  out _ := inferInstance

/-- Finite nonempty limits include products of pairs. -/
instance hasBinaryProducts_of_hasFiniteNonemptyLimits
    [HasFiniteNonemptyLimits C] : HasBinaryProducts C := by infer_instance

/-- Finite nonempty limits include finite connected limits. -/
instance hasFiniteConnectedLimits_of_hasFiniteNonemptyLimits
    [HasFiniteNonemptyLimits C] : HasFiniteConnectedLimits C where
  out := fun J _ _ _ ↦ by infer_instance

/-- Finite nonempty limits include equalizers. -/
instance hasEqualizers_of_hasFiniteNonemptyLimits
    [HasFiniteNonemptyLimits C] : HasEqualizers C := by infer_instance

/-- Finite nonempty limits include fibre products. -/
instance hasPullbacks_of_hasFiniteNonemptyLimits
    [HasFiniteNonemptyLimits C] : HasPullbacks C := by infer_instance

private theorem hasProduct_finSucc [HasBinaryProducts C] (n : ℕ) (f : Fin (n + 1) → C) :
    HasProduct f := by
  induction n with
  | zero =>
      let g : Unit → C := fun _ ↦ f 0
      have h : HasLimit (Discrete.functor g) := by infer_instance
      letI : HasLimit (Discrete.functor g) := h
      exact
        hasProduct_of_equiv_of_iso g f finOneEquiv
          (fun j ↦ eqToIso (by fin_cases j; rfl))
  | succ n ih =>
      haveI : HasProduct fun i : Fin (n + 1) ↦ f i.succ := ih (fun i : Fin (n + 1) ↦ f i.succ)
      exact HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

private theorem hasProduct_of_finite_of_nonempty {ι : Type w} [Finite ι] [Nonempty ι]
    [HasBinaryProducts C] (f : ι → C) : HasProduct f := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  let e : ι ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hn
  haveI : HasProduct fun i : Fin (n + 1) ↦ f (e.symm i) := hasProduct_finSucc C n _
  exact
    hasProduct_of_equiv_of_iso (fun i : Fin (n + 1) ↦ f (e.symm i)) f e
      (fun j ↦ eqToIso (by simp))

/-- Binary products and finite connected limits give finite nonempty limits. -/
theorem hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasFiniteConnectedLimits
    [HasBinaryProducts C] [HasFiniteConnectedLimits C] : HasFiniteNonemptyLimits C where
  out := fun J _ _ _ ↦ by
    let _ : HasEqualizers C := inferInstance
    exact
      { has_limit := fun F ↦ by
          haveI : HasProduct F.obj := hasProduct_of_finite_of_nonempty C F.obj
          let G : (Σ p : J × J, p.1 ⟶ p.2) → C := fun f ↦ F.obj f.1.2
          letI : Nonempty (Σ p : J × J, p.1 ⟶ p.2) := by
            rcases ‹Nonempty J› with ⟨j⟩
            exact ⟨⟨(j, j), 𝟙 j⟩⟩
          haveI : HasProduct G := hasProduct_of_finite_of_nonempty C G
          exact hasLimit_of_equalizer_and_product F }

/-- A category has finite nonempty limits if and only if it has binary products and finite
connected limits. -/
theorem finite_nonempty_limits_iff_binary_products_and_finite_connected_limits :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasFiniteConnectedLimits C := by
  constructor
  · intro h
    letI : HasFiniteNonemptyLimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hP, hC⟩
    letI : HasBinaryProducts C := hP
    letI : HasFiniteConnectedLimits C := hC
    exact hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasFiniteConnectedLimits C

/-- Binary products and equalizers give finite nonempty limits. -/
instance hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasEqualizers
    [HasBinaryProducts C] [HasEqualizers C] : HasFiniteNonemptyLimits C := by
  let _ : HasPullbacks C := hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C
  letI : HasFiniteConnectedLimits C := hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks C
  exact hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasFiniteConnectedLimits C

/-- Binary products and pullbacks give finite nonempty limits. -/
instance hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasPullbacks
    [HasBinaryProducts C] [HasPullbacks C] : HasFiniteNonemptyLimits C := by
  letI : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products
  letI : HasFiniteConnectedLimits C := hasFiniteConnectedLimits_of_hasEqualizers_and_pullbacks C
  exact hasFiniteNonemptyLimits_of_hasBinaryProducts_and_hasFiniteConnectedLimits C

/-- Lemma 4.18.3: a category has finite nonempty limits if and only if it has binary products
and equalizers. -/
theorem finite_nonempty_limits_iff_binary_products_and_equalizers :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasEqualizers C := by
  constructor
  · intro h
    letI : HasFiniteNonemptyLimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hP, hE⟩
    letI : HasBinaryProducts C := hP
    letI : HasEqualizers C := hE
    infer_instance

/-- A category has finite nonempty limits if and only if it has binary products and pullbacks. -/
theorem finite_nonempty_limits_iff_binary_products_and_pullbacks :
    HasFiniteNonemptyLimits C ↔ HasBinaryProducts C ∧ HasPullbacks C := by
  constructor
  · intro h
    letI : HasFiniteNonemptyLimits C := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hP, hPB⟩
    letI : HasBinaryProducts C := hP
    letI : HasPullbacks C := hPB
    infer_instance

end CategoryTheory.Limits
