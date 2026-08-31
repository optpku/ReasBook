module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Specialization
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.Sober

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Order Topology Specialization
open Topology.IsUpperSet
open Topology.WithUpperSet

/- Domain-style sampling for finite Alexandrov chain examples:
- primary domain: topological Krull dimension in Alexandrov-discrete spaces, with the two-point
  example organized around mathlib's canonical Sierpiński-space owner `Prop`;
- sampled canonical declarations:
  `topologicalKrullDim`,
  `homeoWithUpperSetTopologyorderIso`,
  `irreducibleSetEquivPoints`,
  `Topology.IsUpperSet.isOpen_iff_isUpperSet`;
- best owner abstraction: the canonical Sierpiński space `Prop`, with the finite upper-set chain
  `WithUpperSet (Fin (n + 1))` kept only as a bridge/view model for the general chain dimension
  computation;
- primitive-vs-derived split: the primitive bridge data are the chain model
  `WithUpperSet (Fin (n + 1))`, the local `T0Space`/`QuasiSober` instances used to apply
  `irreducibleSetEquivPoints`, and the order identifications of `Specialization Prop` with `Fin 2`;
  the explicit description of the Sierpiński opens and the resulting dimension statements are
  derived API.

Layer triage:
- `source-facing`: the canonical Sierpiński space `Prop`, its open-set classification, and its
  topological Krull dimension;
- `core/canonical`: `topologicalKrullDim`, `homeoWithUpperSetTopologyorderIso`,
  `irreducibleSetEquivPoints`, and the Sierpiński topology on `Prop`;
- `bridge/view`: the finite-chain model `WithUpperSet (Fin (n + 1))` and its comparison
  homeomorphism with the two-point Sierpiński space.
-/

instance (n : ℕ) : Fintype (WithUpperSet (Fin (n + 1))) :=
  inferInstanceAs (Fintype (Fin (n + 1)))

instance (n : ℕ) : LinearOrder (WithUpperSet (Fin (n + 1))) :=
  inferInstanceAs (LinearOrder (Fin (n + 1)))

private noncomputable def finSuccOrderIsoIic (n : ℕ) : Fin (n + 1) ≃o Set.Iic n where
  toFun i := ⟨i.1, Nat.le_of_lt_succ i.2⟩
  invFun i := ⟨i.1, Nat.lt_succ_of_le i.2⟩
  left_inv i := by
    ext
    rfl
  right_inv i := by
    ext
    rfl
  map_rel_iff' := by
    simp

private lemma krullDim_fin_succ (n : ℕ) : Order.krullDim (Fin (n + 1)) = n := by
  rw [Order.krullDim_eq_of_orderIso (finSuccOrderIsoIic n)]
  simpa using (Order.height_eq_krullDim_Iic n).symm

private lemma finiteChain_closed_eq_Iic (n : ℕ)
    (s : IrreducibleCloseds (WithUpperSet (Fin (n + 1)))) :
    ∃ a : WithUpperSet (Fin (n + 1)), (s : Set (WithUpperSet (Fin (n + 1)))) = Set.Iic a := by
  classical
  obtain ⟨a, ha⟩ := (s : Set (WithUpperSet (Fin (n + 1)))).toFinite.exists_maximal
    s.isIrreducible.nonempty
  have ha_mem : a ∈ (s : Set (WithUpperSet (Fin (n + 1)))) := (maximal_iff_forall_gt.mp ha).1
  have ha_max :
      ∀ ⦃b : WithUpperSet (Fin (n + 1))⦄, a < b → b ∉ (s : Set (WithUpperSet (Fin (n + 1)))) :=
    (maximal_iff_forall_gt.mp ha).2
  have hsLower : IsLowerSet (s : Set (WithUpperSet (Fin (n + 1)))) :=
    isClosed_iff_isLower.1 s.isClosed
  refine ⟨a, Set.ext fun b ↦ ?_⟩
  constructor
  · intro hb
    have : ¬ a < b := by
      intro hab
      exact ha_max hab hb
    exact le_of_not_gt this
  · intro hb
    exact hsLower hb ha_mem

private instance finiteChainT0Space (n : ℕ) : T0Space (WithUpperSet (Fin (n + 1))) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  apply Iic_injective
  simpa [inseparable_iff_closure_eq, IsUpperSet.closure_singleton] using hxy

private instance finiteChainQuasiSober (n : ℕ) : QuasiSober (WithUpperSet (Fin (n + 1))) where
  sober {S} hS hSclosed := by
    obtain ⟨a, ha : S = Set.Iic a⟩ := finiteChain_closed_eq_Iic n ⟨S, hS, hSclosed⟩
    refine ⟨a, isGenericPoint_def.2 ?_⟩
    rw [IsUpperSet.closure_singleton, ha.symm]

-- Proof sketch: the irreducible closed subsets of this Alexandrov chain are exactly the nonempty
-- initial segments, and the maximal strict chains of those initial segments have length `n`.
/-- The `(n + 1)`-point Alexandrov chain `WithUpperSet (Fin (n + 1))` has topological Krull
dimension `n`. -/
theorem topologicalKrullDim_withUpperSet_fin_succ (n : ℕ) :
    topologicalKrullDim (WithUpperSet (Fin (n + 1))) = n := by
  let e : IrreducibleCloseds (WithUpperSet (Fin (n + 1))) ≃o Fin (n + 1) :=
    (show IrreducibleCloseds (WithUpperSet (Fin (n + 1))) ≃o
        Specialization (WithUpperSet (Fin (n + 1))) from irreducibleSetEquivPoints).trans
      (orderIsoSpecializationWithUpperSetTopology (Fin (n + 1))).symm
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso e]
  simpa using krullDim_fin_succ n

def withUpperSetHomeomorphOfOrderIso {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) : WithUpperSet α ≃ₜ WithUpperSet β where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_def.2 fun _ hs ↦ IsUpperSet.preimage hs e.monotone
  continuous_invFun := continuous_def.2 fun _ hs ↦ IsUpperSet.preimage hs e.symm.monotone

noncomputable def propOrderIsoFinTwo : Prop ≃o Fin 2 where
  toFun p := by
    classical
    exact if p then 1 else 0
  invFun i := i = 1
  left_inv p := by
    classical
    by_cases hp : p <;> simp [hp]
  right_inv i := by
    classical
    fin_cases i <;> simp
  map_rel_iff' := by
    intro p q
    classical
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

noncomputable def propOrderIsoSpecialization : Prop ≃o Specialization Prop where
  toEquiv := Specialization.toEquiv
  map_rel_iff' := by
    intro p q
    simp [IsUpperSet.specializes_iff_le]

/-- The canonical Sierpiński space `Prop` is homeomorphic to the two-point Alexandrov chain
`WithUpperSet (Fin 2)`. Under this identification, `False` is the closed point and `True` is the
generic point. -/
noncomputable def sierpinskiHomeomorphTwoPointChain : Prop ≃ₜ WithUpperSet (Fin 2) :=
  (homeoWithUpperSetTopologyorderIso Prop).trans
    (withUpperSetHomeomorphOfOrderIso (propOrderIsoSpecialization.symm.trans propOrderIsoFinTwo))

/-- A subset of the canonical Sierpiński space is open exactly when it is `∅`, `{True}`, or
`univ`. -/
theorem isOpen_sierpinskiSpace_iff (s : Set Prop) :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = univ := by
  rw [isOpen_iff_isUpperSet]
  constructor
  · intro hs
    by_cases hFalse : False ∈ s
    · right
      right
      ext p
      by_cases hp : p
      · have hTrue : True ∈ s := hs (by simp) hFalse
        simp [hp, hTrue]
      · simp [hp, hFalse]
    · by_cases hTrue : True ∈ s
      · right
        left
        ext p
        by_cases hp : p <;> simp [hp, hFalse, hTrue]
      · left
        ext p
        by_cases hp : p <;> simp [hp, hFalse, hTrue]
  · rintro (rfl | rfl | rfl)
    · exact isUpperSet_empty
    · simpa only [isOpen_iff_isUpperSet] using (isOpen_singleton_true : IsOpen ({True} : Set Prop))
    · exact isUpperSet_univ

-- Proof sketch: transport the chain computation for `WithUpperSet (Fin 2)` across the canonical
-- Sierpiński-space homeomorphism above.
/-- Example 5.10.4: the canonical Sierpiński space `Prop`, whose open sets are exactly `∅`,
`{True}`, and `univ`, has topological Krull dimension `1`. -/
theorem sierpinskiSpace_topologicalKrullDim : topologicalKrullDim Prop = 1 := by
  calc
    topologicalKrullDim Prop = topologicalKrullDim (WithUpperSet (Fin 2)) := by
      simpa using IsHomeomorph.topologicalKrullDim_eq
        (sierpinskiHomeomorphTwoPointChain : Prop → WithUpperSet (Fin 2))
        sierpinskiHomeomorphTwoPointChain.isHomeomorph
    _ = 1 := by
      simpa using topologicalKrullDim_withUpperSet_fin_succ 1
