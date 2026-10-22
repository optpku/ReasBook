/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FundamentalGroup
open Path.Homotopic.Quotient
open TopologicalSpace.OpenNhdsOf
open CategoryTheory FundamentalGroupoidFunctor
open ContinuousMap

/-- Definition 3.8.1: a topological space is semilocally simply connected if every point has an
open neighborhood whose inclusion into the ambient space induces the trivial map on the based
fundamental group. -/
class SemilocallySimplyConnectedSpace (B : Type u) [TopologicalSpace B] : Prop where
  /-- Each point admits an open neighborhood whose inclusion into the ambient space induces the
  trivial homomorphism on the based fundamental group. -/
  trivial_fundamentalGroup_map (b : B) :
    ∃ U : TopologicalSpace.OpenNhdsOf b,
      FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)) ⟨b, U.mem⟩ = 1

variable {B : Type u} [TopologicalSpace B]

/-- A null-homotopic map induces the trivial morphism on based fundamental groups. -/
theorem ContinuousMap.Nullhomotopic.fundamentalGroup_map_eq_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : f.Nullhomotopic) (x : X) :
    FundamentalGroup.map f x = 1 := by
  obtain ⟨y, H⟩ := hf
  let η : FundamentalGroupoid.map f ⟶ FundamentalGroupoid.map (ContinuousMap.const X y) :=
    homotopicMapsNatIso H.some
  ext p
  refine Quotient.inductionOn p fun γ ↦ ?_
  change (FundamentalGroupoid.map f).map (.mk γ) = 𝟙 (FundamentalGroupoid.mk (f x))
  let e : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk y :=
    asIso (η.app (FundamentalGroupoid.mk x))
  have hη := η.naturality (.mk γ)
  have hconst :
      (FundamentalGroupoid.map (ContinuousMap.const X y)).map (.mk γ) =
        𝟙 (FundamentalGroupoid.mk y) := by
    change ⟦γ.map (ContinuousMap.const X y).continuous⟧ = ⟦Path.refl y⟧
    congr
    ext t
    rfl
  have hη' : (FundamentalGroupoid.map f).map (.mk γ) ≫ e.hom = e.hom := by
    exact hη.trans (by rw [hconst]; exact CategoryTheory.Category.comp_id _)
  have hid : 𝟙 (FundamentalGroupoid.mk (f x)) ≫ e.hom = e.hom :=
    CategoryTheory.Category.id_comp _
  exact (CategoryTheory.cancel_mono e.hom).1 (hη'.trans hid.symm)

/-- Locally contractible spaces are semilocally simply connected. -/
theorem LocallyContractibleSpace.semilocallySimplyConnectedSpace
    (hB : LocallyContractibleSpace B) : SemilocallySimplyConnectedSpace B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨V, hVuniv, hVmem, hnull⟩ := hB b Set.univ (by simp)
  obtain ⟨U, -, hUV⟩ := basis_nhds.mem_iff.mp hVmem
  let i : C(U, B) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi :
      i =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.univ, B)).comp
          ((ContinuousMap.inclusion hVuniv).comp (ContinuousMap.inclusion hUV)) := by
    ext x
    rfl
  have hnull' : i.Nullhomotopic := by
    rw [hi]
    exact (hnull.comp_left (ContinuousMap.inclusion hUV)).comp_right
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Set.univ, B))
  exact ⟨U, hnull'.fundamentalGroup_map_eq_one ⟨b, U.mem⟩⟩

/-- Strongly locally contractible spaces are semilocally simply connected. -/
instance [StronglyLocallyContractibleSpace B] : SemilocallySimplyConnectedSpace B :=
  LocallyContractibleSpace.semilocallySimplyConnectedSpace
    StronglyLocallyContractibleSpace.locallyContractible

/-- A simply connected space is semilocally simply connected. -/
instance [SimplyConnectedSpace B] : SemilocallySimplyConnectedSpace B where
  trivial_fundamentalGroup_map b := by
    refine ⟨⊤, ?_⟩
    ext p
    refine Quotient.inductionOn p ?_
    intro γ
    change fromPath (.mk (γ.map continuous_subtype_val)) = 1
    rw [show (1 : FundamentalGroup B b) = fromPath (.mk (Path.refl b)) by rfl]
    suffices h :
        (.mk (γ.map continuous_subtype_val) : Path.Homotopic.Quotient b b) =
          .mk (Path.refl b) by
      simpa using congrArg fromPath h
    exact eq.2 <| SimplyConnectedSpace.paths_homotopic
      (γ.map continuous_subtype_val) (Path.refl b)
