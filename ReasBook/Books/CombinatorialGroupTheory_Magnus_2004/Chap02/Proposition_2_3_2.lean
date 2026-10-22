/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_10_4

open scoped MonoidAlgebra

noncomputable section

universe u

/- Proposition 2-3-2 lies in Fox calculus and the relation-module description of low-degree group
resolutions.

Layer triage:
- `source-facing`: for a quotient `G = F / N` with `F = FreeGroup X`, the augmentation ideal
  `𝓕 ⊆ ℤ[F]`, the relation ideal `𝓡 = ker (ℤ[F] → ℤ[F / N])`, the displayed quotients
  `𝓡² / 𝓡³`, `𝓕𝓡 / 𝓕𝓡²`, `𝓡 / 𝓡²`, `𝓕 / 𝓕𝓡`, `ℤ[F / N]`, and `ℤ`, together with the visible tail
  maps among them, interpreted as right `ℤG`-modules.
- `core/canonical`: the owner ring `FreeGroupRing X = ℤ[FreeGroup X]`, its quotient ring
  `FreeGroupRing X ⧸ relationIdeal N`, the opposite-ring owner
  `FreeGroupRing Xᵐᵒᵖ ⧸ relationIdealOpp N` for right `ℤG`-modules, the canonical quotient
  constructions on right `FreeGroupRing X`-modules, and
  `CategoryTheory.ProjectiveResolution` as the owner abstraction for the actual resolution.
- `bridge/view`: the textbook ring `ℤ[F / N]` is canonically recovered from the quotient-ring owner
  via `quotientGroupRingEquiv`, while the source-facing quotient terms
  `relationIdealSquareQuotient`, `augmentationRelationQuotient`, `relationIdealQuotient`, and
  `augmentationQuotient` are realized as quotient right modules over the same owner.

Domain sampling:
1. `FreeGroupRing` from Definition `1-10-4` is the chapter owner abbreviation for `ℤ[FreeGroup X]`.
2. `RingHom.ker` is the canonical owner abstraction for both `𝓕` and `𝓡`.
3. `Ideal.toTwoSided` together with `TwoSidedIdeal.asIdealOpposite` is the owner-side route from a
   two-sided ideal of `ℤ[F]` to the corresponding ideal of the opposite ring that governs right
   `ℤG`-modules.
4. `Module.IsTorsionBySet.module` and `Submodule.mapQ` are the canonical owners for quotient right
   modules `J / J𝓡` and the inclusion-induced maps between them.
5. `CategoryTheory.ProjectiveResolution` in `ModuleCat (quotientGroupRingRight N)` is the canonical
   owner for the statement that this tail extends to a genuine resolution of the trivial module.

Primitive vs. derived:
the primitive public data are the quotient ring `ℤ[F] ⧸ 𝓡`, the corresponding right-module owner
`FreeGroupRing Xᵐᵒᵖ ⧸ relationIdealOpp N`, the four displayed quotient modules by the products
`J * 𝓡`, and the named tail maps between them. The identification with the textbook ring
`ℤ[F / N]` is a bridge, and the exactness/freeness assertions together with the trivial-module
augmentation are theorem-level consequences rather than bundled data. -/

/-- The canonical quotient map `ℤ[F] → ℤ[F / N]` attached to the presentation `F ↠ F / N`. -/
abbrev quotientPresentationMap {X : Type u} (N : Subgroup (FreeGroup X)) [N.Normal] :
    FreeGroupRing X →+* MonoidAlgebra ℤ (FreeGroup X ⧸ N) :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' N)

/-- The augmentation ideal `𝓕` of `ℤ[F]` for `F = FreeGroup X`. -/
abbrev augmentationIdeal (X : Type u) : Ideal (FreeGroupRing X) :=
  RingHom.ker (Bialgebra.counitAlgHom ℤ (FreeGroupRing X))

/-- The relation ideal `𝓡 = ker (ℤ[F] → ℤ[F / N])` attached to a normal subgroup `N`. -/
abbrev relationIdeal {X : Type u} (N : Subgroup (FreeGroup X)) [N.Normal] :
    Ideal (FreeGroupRing X) :=
  RingHom.ker (quotientPresentationMap N)

/-- The quotient-ring owner for `ℤ[F / N]`, canonically equivalent to the integral group ring of
the quotient group. -/
abbrev quotientGroupRing {X : Type u} (N : Subgroup (FreeGroup X)) [N.Normal] :=
  FreeGroupRing X ⧸ relationIdeal N

/-- The source-facing bridge from the quotient-ring owner `ℤ[F] / 𝓡` to the textbook ring
`ℤ[F / N]`. -/
noncomputable abbrev quotientGroupRingEquiv {X : Type u} (N : Subgroup (FreeGroup X))
    [N.Normal] : quotientGroupRing N ≃+* MonoidAlgebra ℤ (FreeGroup X ⧸ N) :=
  RingHom.quotientKerEquivOfSurjective <| by
    intro x
    simpa [quotientPresentationMap, MonoidAlgebra.mapDomain] using
      (Finsupp.mapDomain_surjective (QuotientGroup.mk'_surjective N) x)

section

variable {X : Type u} (N : Subgroup (FreeGroup X)) [N.Normal]

local notation "R" => FreeGroupRing X
local notation "F" => augmentationIdeal X
local notation "Rel" => relationIdeal N

private def idealAsRightSubmodule (J : Ideal R) [J.IsTwoSided] : Submodule Rᵐᵒᵖ R where
  carrier := J
  zero_mem' := J.zero_mem
  add_mem' hx hy := J.add_mem hx hy
  smul_mem' a x hx := by
    change x * MulOpposite.unop a ∈ J
    exact J.mul_mem_right _ hx

private abbrev relationIdealOpp : Ideal Rᵐᵒᵖ :=
  TwoSidedIdeal.asIdealOpposite (Ideal.toTwoSided Rel)

private theorem mem_relationIdealOpp_iff {x : Rᵐᵒᵖ} :
    x ∈ relationIdealOpp N ↔ x.unop ∈ Rel := by
  simpa [relationIdealOpp] using
    (TwoSidedIdeal.mem_asIdealOpposite :
      x ∈ TwoSidedIdeal.asIdealOpposite (Ideal.toTwoSided Rel) ↔
        x.unop ∈ Ideal.toTwoSided Rel)

private instance relationIdealOpp_isTwoSided : (relationIdealOpp N).IsTwoSided where
  mul_mem_of_left b ha := by
    rw [mem_relationIdealOpp_iff N] at ha ⊢
    simpa using Ideal.mul_mem_left Rel (MulOpposite.unop b) ha

private abbrev relationIdealRightQuotient (J : Ideal R) [J.IsTwoSided] :=
  idealAsRightSubmodule J ⧸
    relationIdealOpp N • (⊤ : Submodule Rᵐᵒᵖ (idealAsRightSubmodule J))

/-- The opposite-ring owner for the right `ℤ[F / N]`-module structure coming from the quotient
presentation. -/
abbrev quotientGroupRingRight := Rᵐᵒᵖ ⧸ relationIdealOpp N

local notation "S" => quotientGroupRingRight N

/-- The quotient `𝓡² / 𝓡³`, written as the quotient of `𝓡²` by the right product `𝓡²𝓡`. -/
abbrev relationIdealSquareQuotient := relationIdealRightQuotient N (Rel ^ 2)

/-- The quotient `𝓕𝓡 / 𝓕𝓡²`, written as the quotient of `𝓕𝓡` by the right product
`(𝓕𝓡)𝓡 = 𝓕𝓡²`. -/
abbrev augmentationRelationQuotient := relationIdealRightQuotient N (F * Rel)

/-- The quotient `𝓡 / 𝓡²`, written as the quotient of `𝓡` by the right product `𝓡𝓡`. -/
abbrev relationIdealQuotient := relationIdealRightQuotient N Rel

/-- The quotient `𝓕 / 𝓕𝓡`, written as the quotient of `𝓕` by the right product `𝓕𝓡`. -/
abbrev augmentationQuotient := relationIdealRightQuotient N F

private theorem quotientPresentationMap_counit_comp :
    ((Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (FreeGroup X ⧸ N))).toRingHom).comp
        (quotientPresentationMap N) =
      (Bialgebra.counitAlgHom ℤ (R)).toRingHom := by
  apply MonoidAlgebra.ringHom_ext <;> intro x <;> simp [quotientPresentationMap]

/-- The relation ideal lies in the augmentation ideal, so `ℤ` carries the usual trivial
augmentation factor of the presentation. -/
theorem relationIdeal_le_augmentationIdeal : Rel ≤ F := by
  intro x hx
  change quotientPresentationMap N x = 0 at hx
  change ((Bialgebra.counitAlgHom ℤ R).toRingHom x = 0)
  rw [← quotientPresentationMap_counit_comp N]
  simpa using congrArg
    (((Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (FreeGroup X ⧸ N))).toRingHom)) hx

private theorem idealAsRightSubmodule_mono {J K : Ideal R} [J.IsTwoSided] [K.IsTwoSided]
    (hJK : J ≤ K) : idealAsRightSubmodule J ≤ idealAsRightSubmodule K :=
  hJK

private def liftQuotientGroupRingRightLinear {J K : Ideal R} [J.IsTwoSided] [K.IsTwoSided]
    (f : relationIdealRightQuotient N J →ₗ[Rᵐᵒᵖ] relationIdealRightQuotient N K) :
    relationIdealRightQuotient N J →ₗ[Rᵐᵒᵖ ⧸ relationIdealOpp N]
      relationIdealRightQuotient N K := by
  refine
    { toFun := f
      map_add' := f.map_add
      map_smul' := ?_ }
  intro a x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  change f (r • x) = r • f x
  exact f.map_smul r x

private def quotientMapOfLE {J K : Ideal R} [J.IsTwoSided] [K.IsTwoSided] (hJK : J ≤ K) :
    relationIdealRightQuotient N J →ₗ[quotientGroupRingRight N] relationIdealRightQuotient N K :=
  liftQuotientGroupRingRightLinear N <|
    Submodule.mapQ _ _ (Submodule.inclusion (idealAsRightSubmodule_mono hJK)) <| by
    intro x hx
    change (Submodule.inclusion (idealAsRightSubmodule_mono hJK) x) ∈
      relationIdealOpp N • (⊤ : Submodule Rᵐᵒᵖ (idealAsRightSubmodule K))
    rw [Submodule.mem_smul_top_iff] at hx ⊢
    exact (smul_mono_right (relationIdealOpp N))
      (idealAsRightSubmodule_mono hJK) hx

/-- The canonical right-module map `𝓡² / 𝓡³ → 𝓕𝓡 / 𝓕𝓡²` induced by the inclusion
`𝓡² ≤ 𝓕𝓡`. -/
abbrev relationIdealSquareBoundary :
    relationIdealSquareQuotient N →ₗ[quotientGroupRingRight N] augmentationRelationQuotient N :=
  quotientMapOfLE N <| by
    rw [Submodule.pow_succ, Submodule.pow_one]
    exact Ideal.mul_mono (relationIdeal_le_augmentationIdeal N) le_rfl

/-- The canonical right-module map `𝓕𝓡 / 𝓕𝓡² → 𝓡 / 𝓡²` induced by the inclusion `𝓕𝓡 ≤ 𝓡`. -/
abbrev augmentationRelationBoundary :
    augmentationRelationQuotient N →ₗ[quotientGroupRingRight N] relationIdealQuotient N :=
  quotientMapOfLE N (Ideal.mul_le_left : F * Rel ≤ Rel)

/-- The canonical right-module map `𝓡 / 𝓡² → 𝓕 / 𝓕𝓡` induced by the inclusion `𝓡 ≤ 𝓕`. -/
abbrev relationBoundary :
    relationIdealQuotient N →ₗ[quotientGroupRingRight N] augmentationQuotient N :=
  quotientMapOfLE N (relationIdeal_le_augmentationIdeal N)

private local instance quotientGroupRingRightModule : Module S S :=
  Semiring.toModule

/-- The underlying `Rᵐᵒᵖ`-linear map `𝓕 / 𝓕𝓡 → ℤ[F] / 𝓡`. -/
private def augmentationBoundaryAux :
    augmentationQuotient N →ₗ[Rᵐᵒᵖ] quotientGroupRingRight N :=
  Submodule.mapQ _ (relationIdealOpp N) {
      toFun := fun x ↦ MulOpposite.op ((x : idealAsRightSubmodule F) : R)
      map_add' := fun x y ↦ rfl
      map_smul' := fun a x ↦ rfl
    } <| by
      intro x hx
      rw [Submodule.mem_comap]
      rw [mem_relationIdealOpp_iff N]
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha y _
        rw [mem_relationIdealOpp_iff N] at ha
        change ((y : R) * MulOpposite.unop a) ∈ Rel
        exact Ideal.mul_mem_left Rel (y : R) ha
      · intro u v hu hv
        exact Ideal.add_mem Rel hu hv

/-- The canonical right-module map `𝓕 / 𝓕𝓡 → ℤ[F] / 𝓡`, landing directly in the quotient-ring
owner `quotientGroupRingRight N`. -/
abbrev augmentationBoundary :
    augmentationQuotient N →ₗ[quotientGroupRingRight N] quotientGroupRingRight N :=
  let f := augmentationBoundaryAux N
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro a x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      change f (r • x) = r • f x
      exact f.map_smul r x }

/-- The augmentation ring hom on the right quotient ring `ℤ[F] / 𝓡`, giving `ℤ` its canonical
trivial right `ℤ[F / N]`-module structure. -/
def quotientGroupRingRightAugmentation : quotientGroupRingRight N →+* ℤ :=
  Ideal.Quotient.lift (relationIdealOpp N)
    (((Bialgebra.counitAlgHom ℤ R).toRingHom).fromOpposite fun _ _ ↦ mul_comm _ _) <| by
      intro x hx
      change (Bialgebra.counitAlgHom ℤ R) (MulOpposite.unop x) = 0
      rw [mem_relationIdealOpp_iff N] at hx
      have hxF : MulOpposite.unop x ∈ F := relationIdeal_le_augmentationIdeal N hx
      simpa [augmentationIdeal, RingHom.mem_ker] using hxF

instance quotientGroupRingIntModule : Module S ℤ :=
  RingHom.toModule (quotientGroupRingRightAugmentation N)

/-- The trivial right `ℤ[F / N]`-module `ℤ`, expressed over the quotient-ring owner
`quotientGroupRingRight N`. -/
def quotientGroupRingTrivialModule {Y : Type u} (N : Subgroup (FreeGroup Y)) [N.Normal] :
    ModuleCat.{0} (quotientGroupRingRight N) :=
  ModuleCat.of.{0} (quotientGroupRingRight N) ℤ

/-- The augmentation map on the quotient-ring owner `ℤ[F] / 𝓡 → ℤ`, linear for the canonical
trivial right `ℤ[F / N]`-module structure on `ℤ`. The codomain is expressed through the owner
object `quotientGroupRingTrivialModule N`. -/
def quotientGroupRingCounit :
    S →ₗ[S] quotientGroupRingTrivialModule N where
  toFun := quotientGroupRingRightAugmentation N
  map_add' := fun x y ↦ (quotientGroupRingRightAugmentation N).map_add x y
  map_smul' := fun a x ↦ by
    change quotientGroupRingRightAugmentation N (a * x) =
      quotientGroupRingRightAugmentation N a * quotientGroupRingRightAugmentation N x
    exact (quotientGroupRingRightAugmentation N).map_mul a x

-- Proof sketch: the standard Fox-calculus resolution attached to the free presentation
-- `FreeGroup X ↠ FreeGroup X ⧸ N` identifies the visible relation-module tail with the canonical
-- quotient ring `ℤ[F] / 𝓡`, its right quotient modules `J / J𝓡`, and the inclusion/quotient maps
-- named above. The classical argument shows exactness and freeness of the four displayed
-- source-facing quotient terms.
/-- Proposition 2-3-2: for `G = F / N`, the canonical right `ℤG`-modules
`𝓡² / 𝓡³`, `𝓕𝓡 / 𝓕𝓡²`, `𝓡 / 𝓡²`, `𝓕 / 𝓕𝓡`, `ℤ[F / N]`, and `ℤ` occur as the first displayed terms
of a projective resolution of the trivial right module `ℤ` over the quotient-ring owner
`quotientGroupRingRight N`. The named boundary maps are the low-degree differentials of that
resolution; in particular the degree-`0` augmentation is the named counit
`quotientGroupRingCounit N`. The four displayed quotient modules are free over `ℤG`. -/
theorem relation_ideal_free_resolution :
    Module.Free S (relationIdealSquareQuotient N) ∧
      Module.Free S (augmentationRelationQuotient N) ∧
      Module.Free S (relationIdealQuotient N) ∧
      Module.Free S (augmentationQuotient N) ∧
      ∃ P : CategoryTheory.ProjectiveResolution (quotientGroupRingTrivialModule N),
        ∃ e4 : relationIdealSquareQuotient N ≃ₗ[S] P.complex.X 4,
          ∃ e3 : augmentationRelationQuotient N ≃ₗ[S] P.complex.X 3,
            ∃ e2 : relationIdealQuotient N ≃ₗ[S] P.complex.X 2,
              ∃ e1 : augmentationQuotient N ≃ₗ[S] P.complex.X 1,
                ∃ e0 : S ≃ₗ[S] P.complex.X 0,
                  e3.toLinearMap.comp (relationIdealSquareBoundary N) =
                      (P.complex.d 4 3).hom.comp e4.toLinearMap ∧
                    e2.toLinearMap.comp (augmentationRelationBoundary N) =
                      (P.complex.d 3 2).hom.comp e3.toLinearMap ∧
                    e1.toLinearMap.comp (relationBoundary N) =
                      (P.complex.d 2 1).hom.comp e2.toLinearMap ∧
                    e0.toLinearMap.comp (augmentationBoundary N) =
                      (P.complex.d 1 0).hom.comp e1.toLinearMap ∧
                    ((P.π.f 0).hom.comp e0.toLinearMap = quotientGroupRingCounit N) := by
  sorry

/-- Companion low-degree exactness and freeness consequences of
`relation_ideal_free_resolution`. -/
theorem relation_ideal_free_resolution_tail :
    Function.Surjective (quotientGroupRingCounit N) ∧
      Function.Exact (augmentationBoundary N) (quotientGroupRingCounit N) ∧
      LinearMap.range (relationBoundary N) = LinearMap.ker (augmentationBoundary N) ∧
      LinearMap.range (augmentationRelationBoundary N) = LinearMap.ker (relationBoundary N) ∧
      LinearMap.range (relationIdealSquareBoundary N) =
        LinearMap.ker (augmentationRelationBoundary N) ∧
      Module.Free S (relationIdealSquareQuotient N) ∧
      Module.Free S (augmentationRelationQuotient N) ∧
      Module.Free S (relationIdealQuotient N) ∧
      Module.Free S (augmentationQuotient N) := by
  sorry

end
