module

public import Mathlib.Topology.LocallyConstant.Basic
public import stacks_project.Chap05.Definition_5_20_1
public import stacks_project.Chap05.Definition_5_9_1
public import Mathlib.Topology.Sober
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import stacks_project.Chap05.Lemma_5_20_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

/- Domain-style sampling for Lemma 5.20.3:
- project owner for dimension functions: `IsDimensionFunction`
- derived codimension comparison owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood bridge: `LocallyNoetherianSpace.exists_mem_nhds_subset`
- canonical irreducible-component owner on Noetherian neighborhoods: `irreducibleComponents`

Layer triage:
- `source-facing`: the difference of two dimension functions is locally constant
- `core/canonical`: `IsDimensionFunction`, `IsLocallyConstant`, `LocallyNoetherianSpace`,
  `QuasiSober`
- `bridge/view`: shrink to a Noetherian open neighborhood, then compare both functions on each
  irreducible component through the common codimension formula from Lemma `5.20.2`

Primitive data versus derived API:
- primitive data already lives upstream in `IsDimensionFunction` and `LocallyNoetherianSpace`
- this file should contribute only the derived locally constant theorem under the owner namespace,
  not a new wrapper around local dimension data
-/

namespace IsDimensionFunction

section

variable {X : Type u} [TopologicalSpace X] [LocallyNoetherianSpace X] [QuasiSober X]
  {δ δ' : X → ℤ}

/-- Helper for Lemma 5.20.3: restricting a dimension function to an open subspace preserves the
dimension-function axioms. -/
lemma restrict_open (U : Opens X) (hδ : IsDimensionFunction δ) :
    IsDimensionFunction (fun u : U ↦ δ u) where
  strict_of_specializes := by
    intro x y hxy hne
    -- Pass the specialization relation to the ambient space and reuse the ambient strict decrease.
    exact hδ.strict_of_specializes ((subtype_specializes_iff x y).mp hxy) fun h =>
      hne (Subtype.ext h)
  eq_add_one_of_immediateSpecialization := by
    intro x y hxy
    -- Lift the immediate-specialization relation from the open subtype to the ambient space.
    have hxy_ambient : IsImmediateSpecialization (x : X) y := by
      refine ⟨(subtype_specializes_iff x y).mp hxy.specializes, ?_, ?_⟩
      · intro h
        exact hxy.ne (Subtype.ext h)
      · intro z hxz hzy
        have hzU : z ∈ (U : Set X) := hzy.mem_open U.2 y.2
        let zU : U := ⟨z, hzU⟩
        have hxzU : x ⤳ zU := (subtype_specializes_iff x zU).2 hxz
        have hzUy : zU ⤳ y := (subtype_specializes_iff zU y).2 hzy
        rcases hxy.eq_or_eq hxzU hzUy with hzx | hzy'
        · left
          exact congrArg Subtype.val hzx
        · right
          exact congrArg Subtype.val hzy'
    -- The unit-drop identity now follows from the ambient dimension function.
    simpa using hδ.eq_add_one_of_immediateSpecialization hxy_ambient

section Noetherian

variable [NoetherianSpace X]

/-- Helper for Lemma 5.20.3: the difference of two dimension functions is constant on each
irreducible component. -/
lemma sub_eq_sub_of_mem_irreducible_component (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') {Z : Set X} (hZ : Z ∈ irreducibleComponents X) {x y : X}
    (hx : x ∈ Z) (hy : y ∈ Z) :
    δ x - δ' x = δ y - δ' y := by
  let ξ : X := hZ.1.genericPoint
  have hξ : IsGenericPoint ξ Z := by
    simpa [ξ] using
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hξx : ξ ⤳ x := hξ.specializes hx
  have hξy : ξ ⤳ y := hξ.specializes hy
  -- Compare both functions to the same generic point of the component.
  have hx_eq : δ ξ - δ x = δ' ξ - δ' x := by
    rw [hδ.sub_eq_codimBetween_pointClosure ξ x hξx,
      hδ'.sub_eq_codimBetween_pointClosure ξ x hξx]
  have hy_eq : δ ξ - δ y = δ' ξ - δ' y := by
    rw [hδ.sub_eq_codimBetween_pointClosure ξ y hξy,
      hδ'.sub_eq_codimBetween_pointClosure ξ y hξy]
  -- Cancelling the common codimension terms gives the claimed equality of differences.
  linarith

/-- Helper for Lemma 5.20.3: in a Noetherian space, the union of irreducible components not
containing a fixed point has open complement. -/
lemma isOpen_component_neighborhood (x : X) :
    IsOpen (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X)) := by
  let bad : Set (Set X) := {Z | Z ∈ irreducibleComponents X ∧ x ∉ Z}
  have hbad_finite : bad.Finite := NoetherianSpace.finite_irreducibleComponents.subset fun _ h ↦ h.1
  have hbad_closed : IsClosed (⋃₀ bad) := by
    rw [Set.sUnion_eq_biUnion]
    exact hbad_finite.isClosed_biUnion fun W hW ↦
      isClosed_of_mem_irreducibleComponents W hW.1
  -- The desired neighborhood is the complement of this closed union.
  simpa [bad] using hbad_closed.isOpen_compl

/-- Helper for Lemma 5.20.3: on a Noetherian quasi-sober space, the difference of two dimension
functions is locally constant. -/
theorem isLocallyConstant_sub_of_noetherian (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro x
  let V : Set X :=
    (((⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z})ᶜ : Set X))
  have hV_open : IsOpen V := by
    simpa [V] using isOpen_component_neighborhood (X := X) x
  have hxV : x ∈ V := by
    -- By construction, `x` lies in no irreducible component excluded from the neighborhood.
    intro hx_bad
    rcases Set.mem_sUnion.1 hx_bad with ⟨B, hBbad, hxB⟩
    exact hBbad.2 hxB
  refine ⟨V, hV_open, hxV, ?_⟩
  intro y hyV
  have hy_components : y ∈ ⋃₀ irreducibleComponents X := by
    simp [sUnion_irreducibleComponents]
  rcases Set.mem_sUnion.1 hy_components with ⟨Z, hZ, hyZ⟩
  have hxZ : x ∈ Z := by
    -- Any irreducible component meeting the neighborhood must also contain `x`.
    by_contra hxZ
    have hy_bad : y ∈ ⋃₀ {Z : Set X | Z ∈ irreducibleComponents X ∧ x ∉ Z} := by
      exact Set.mem_sUnion.2 ⟨Z, ⟨hZ, hxZ⟩, hyZ⟩
    exact hyV hy_bad
  simpa using
    (sub_eq_sub_of_mem_irreducible_component (X := X) (x := x) (y := y) hδ hδ' hZ hxZ hyZ).symm

end Noetherian

-- Proof sketch: around each point, choose a Noetherian open neighbourhood using local
-- Noetherianity. In that neighbourhood, the finitely many irreducible components through the
-- point have generic points by sobriety, and Lemma 5.20.2 identifies both dimension functions
-- with the same codimension formula on each component, forcing `δ - δ'` to be constant there.
/-- Lemma 5.20.3: on a locally Noetherian sober topological space, the difference `δ - δ'` of two
dimension functions is locally constant; `T₀` is derived canonically from either dimension
function, so only quasi-sobriety remains ambient. -/
theorem isLocallyConstant_sub (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro x
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hxU, hU_noetherian⟩
  letI : NoetherianSpace U := hU_noetherian
  letI : QuasiSober U := U.isOpenEmbedding'.quasiSober
  have hδU : IsDimensionFunction (fun u : U ↦ δ u) := restrict_open U hδ
  have hδU' : IsDimensionFunction (fun u : U ↦ δ' u) := restrict_open U hδ'
  have hlocU : IsLocallyConstant (fun u : U ↦ δ u - δ' u) :=
    isLocallyConstant_sub_of_noetherian (X := U) hδU hδU'
  obtain ⟨V, hV_open, hxV, hconstV⟩ := (IsLocallyConstant.iff_exists_open _).1 hlocU ⟨x, hxU⟩
  let W : Set X := Subtype.val '' V
  have hW_open : IsOpen W := by
    simpa [W] using U.2.isOpenMap_subtype_val V hV_open
  have hxW : x ∈ W := by
    exact ⟨⟨x, hxU⟩, hxV, rfl⟩
  refine ⟨W, hW_open, hxW, ?_⟩
  intro y hyW
  rcases hyW with ⟨yU, hyV, rfl⟩
  -- The locally constant neighborhood in the open subtype pushes forward to one in `X`.
  simpa using hconstV yU hyV

end

end IsDimensionFunction
