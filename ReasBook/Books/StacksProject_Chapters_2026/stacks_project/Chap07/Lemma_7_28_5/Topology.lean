module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃ t w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

local notation "j" => CostructuredArrow.proj u V
local notation "uOver" => CostructuredArrow.toOver u V

/-- The top sieve is covering for the topology on `CostructuredArrow u V` induced by the
projection to `C`. -/
-- Proof sketch: the image of the top sieve under `CostructuredArrow.proj u V` is again the top
-- sieve on the underlying object of `C`, so this is immediate from `J.top_mem`.
theorem cocontinuousOverTopology_top_mem
    (X : CostructuredArrow u V) :
    Sieve.functorPushforward j (⊤ : Sieve X) ∈ J X.left := by
  -- The induced topology declares covers exactly by pushforward along `j`.
  rw [Sieve.functorPushforward_top]
  exact J.top_mem X.left

/-- Pulling back a covering sieve for the topology on `CostructuredArrow u V` stays covering. -/
-- Proof sketch: a morphism in `CostructuredArrow u V` pulls back the defining arrow
-- `u(U) ⟶ V`, so the pushforward of a pullback sieve along `CostructuredArrow.proj u V`
-- identifies with the pullback of the corresponding sieve in `C`, and then one applies
-- `J.pullback_stable`.
theorem cocontinuousOverTopology_pullback_stable
    {X Y : CostructuredArrow u V} {S : Sieve Y} (f : X ⟶ Y)
    (hS : Sieve.functorPushforward j S ∈ J Y.left) :
    Sieve.functorPushforward j (S.pullback f) ∈ J X.left := by
  -- Any arrow in the pullback of the pushed-forward sieve lifts to the pullback sieve itself.
  have hle :
      Sieve.pullback f.left (Sieve.functorPushforward j S) ≤
        Sieve.functorPushforward j (Sieve.pullback f S) := by
    intro W k hk
    rcases hk with ⟨Z, g, i, hg, hki⟩
    have hki' : k ≫ f.left = i ≫ g.left := by
      simpa using hki
    let W' : CostructuredArrow u V := CostructuredArrow.mk (u.map k ≫ X.hom)
    let hX : W' ⟶ X := CostructuredArrow.homMk k
    have hZw : u.map i ≫ Z.hom = W'.hom := by
      have hwg : u.map i ≫ Z.hom = u.map (i ≫ g.left) ≫ Y.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun t => u.map i ≫ t) (CostructuredArrow.w g).symm
      have hwf : u.map (k ≫ f.left) ≫ Y.hom = u.map k ≫ X.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun t => u.map k ≫ t) (CostructuredArrow.w f)
      have hmid' : u.map (i ≫ g.left) ≫ Y.hom = u.map (k ≫ f.left) ≫ Y.hom := by
        rw [hki'.symm]
      exact (hwg.trans hmid').trans (by simpa [W'] using hwf)
    let hZ : W' ⟶ Z := CostructuredArrow.homMk i hZw
    have hpull : S.pullback f hX := by
      have hcomp : hX ≫ f = hZ ≫ g := by
        ext
        exact hki'
      change S (hX ≫ f)
      rw [hcomp]
      exact S.downward_closed hg hZ
    simpa [hX] using
      (Sieve.image_mem_functorPushforward (F := j) (R := S.pullback f) hpull)
  exact J.superset_covering hle (J.pullback_stable f.left hS)

/-- The transitivity axiom for the topology on `CostructuredArrow u V` follows from the
transitivity axiom on `C`. -/
-- Proof sketch: refine each object of the covering sieve on `CostructuredArrow u V` by the
-- hypothesized covering over that object, push everything forward along the projection to `C`,
-- and invoke `J.transitive`.
theorem cocontinuousOverTopology_transitive
    {X : CostructuredArrow u V} {S R : Sieve X}
    (hS : Sieve.functorPushforward j S ∈ J X.left)
    (hR : ∀ ⦃Y : CostructuredArrow u V⦄ (f : Y ⟶ X), S f →
      Sieve.functorPushforward j (R.pullback f) ∈ J Y.left) :
    Sieve.functorPushforward j R ∈ J X.left := by
  -- Refine the pushed-forward cover one arrow at a time and reduce to `J.transitive`.
  apply J.transitive hS
  rintro Y _ ⟨Z, g, i, hg, rfl⟩
  have hcover :
      Sieve.pullback i (Sieve.pullback g.left (Sieve.functorPushforward j R)) ∈ J Y := by
    apply J.pullback_stable i
    refine J.superset_covering (Sieve.functorPushforward_pullback_le (F := j) g R) (hR g hg)
  simpa [Sieve.pullback_comp] using hcover

/-- Helper for Lemma 7.28.5: the induced topology on `CostructuredArrow u V` built from
covering pushforwards along the projection to `C`. -/
def cocontinuousOverTopologyCore : GrothendieckTopology (CostructuredArrow u V) where
  sieves X S := Sieve.functorPushforward j S ∈ J X.left
  top_mem' := cocontinuousOverTopology_top_mem J u V
  pullback_stable' _ _ _ f hS := cocontinuousOverTopology_pullback_stable J u V f hS
  transitive' _ _ hS _ hR := cocontinuousOverTopology_transitive J u V hS hR

local notation "J'" => cocontinuousOverTopologyCore J u V

/-- Helper for Lemma 7.28.5: covers for the core induced topology on `CostructuredArrow u V`
are already defined by pushforward along the projection `j`. -/
theorem cocontinuousOverProjection_coverPreserving_core :
    CoverPreserving J' J j where
  cover_preserve hS := hS

/-- Helper for Lemma 7.28.5: the projection `j` preserves compatible families for the core
induced topology because a common comparison object can be built in `CostructuredArrow u V`. -/
theorem cocontinuousOverProjection_compatiblePreserving_core :
    CompatiblePreserving J j where
  compatible {ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : CostructuredArrow u V := CostructuredArrow.mk (u.map f₁ ≫ Y₁.hom)
    have hw_base : u.map f₂ ≫ Y₂.hom = u.map f₁ ≫ Y₁.hom := by
      have hleft : f₂ ≫ g₂.left = f₁ ≫ g₁.left := by
        simpa using h.symm
      have hw₂ : u.map f₂ ≫ Y₂.hom = u.map (f₂ ≫ g₂.left) ≫ Z.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₂ ≫ k) (CostructuredArrow.w g₂).symm
      have hmid : u.map (f₂ ≫ g₂.left) ≫ Z.hom = u.map (f₁ ≫ g₁.left) ≫ Z.hom := by
        simpa using congrArg (fun k => u.map k ≫ Z.hom) hleft
      have hw₁ : u.map (f₁ ≫ g₁.left) ≫ Z.hom = u.map f₁ ≫ Y₁.hom := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun k => u.map f₁ ≫ k) (CostructuredArrow.w g₁)
      exact hw₂.trans (hmid.trans hw₁)
    have hw : u.map f₂ ≫ Y₂.hom = W'.hom := by
      simpa [W'] using hw_base
    let g₁' : W' ⟶ Y₁ := CostructuredArrow.homMk f₁
    let g₂' : W' ⟶ Y₂ := CostructuredArrow.homMk f₂ hw
    have hcomp : g₁' ≫ g₁ = g₂' ≫ g₂ := by
      ext
      exact h
    simpa [g₁', g₂'] using hx g₁' g₂' hg₁ hg₂ hcomp

/-- Helper for Lemma 7.28.5: the projection `j` is continuous for the core induced topology. -/
instance cocontinuousOverProjection_isContinuous_core :
    Functor.IsContinuous j J' J := by
  exact Functor.isContinuous_of_coverPreserving
    (cocontinuousOverProjection_compatiblePreserving_core (J := J) (u := u) (V := V))
    (cocontinuousOverProjection_coverPreserving_core (J := J) (u := u) (V := V))

end CategoryTheory
