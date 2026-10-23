module

public import Mathlib.Topology.Algebra.Group.GroupTopology
public import Mathlib.Topology.CompactOpen
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open scoped Topology
open ContinuousMap Topology

universe u

/- Domain-style sampling for compact-open automorphism groups:
- primary domain: compact-open topology on self-homeomorphism spaces, together with the
  discrete-space bridge to permutation groups;
- sampled owner declarations:
  `ContinuousMap.compactOpen`,
  `ContinuousMap.continuous_comp'`,
  `ContinuousMonoidHom.isInducing_toContinuousMap`,
  `Homeomorph.ofDiscrete`;
- core/canonical owner: the self-homeomorphism type `E ≃ₜ E`, viewed inside the compact-open
  function space `C(E, E)`;
- primitive data: the group structure on `E ≃ₜ E` and the canonical forgetful map
  `(E ≃ₜ E) → C(E, E)`;
- derived API: the discrete-space bridge `Equiv.Perm E ≃ E ≃ₜ E` coming from
  `Homeomorph.ofDiscrete`, and the induced topological-group structure in the discrete case.

Layer triage:
- `source-facing`: Example 5.30.2, asserting that the compact-open topology on `Aut(E)` makes the
  self-homeomorphism group into a topological group;
- `core/canonical`: the compact-open topology and composition on `ContinuousMap`;
- `bridge/view`: the discrete identification `Homeomorph.ofDiscrete : Equiv.Perm E → E ≃ₜ E`.

This item should keep `E ≃ₜ E` as the public owner of `Aut(E)`, package the compact-open choice as
an explicit group topology on that owner, and relegate permutations to a thin induced-topology
bridge rather than a second ambient owner.
-/

section

variable {E : Type u} [TopologicalSpace E]

instance : Group (E ≃ₜ E) where
  one := Homeomorph.refl E
  mul f g := g.trans f
  inv := Homeomorph.symm
  mul_assoc f g h := by
    ext x
    rfl
  one_mul f := by
    ext x
    rfl
  mul_one f := by
    ext x
    rfl
  inv_mul_cancel f := by
    ext x
    exact Homeomorph.symm_apply_apply f x

/-- The compact-open topology on the self-homeomorphism group, induced from the ambient
compact-open self-map space `C(E, E)`. -/
abbrev homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E) :=
  TopologicalSpace.induced ((↑) : (E ≃ₜ E) → C(E, E)) ContinuousMap.compactOpen

end

section

variable {E : Type u} [TopologicalSpace E] [DiscreteTopology E]

/-- For a discrete space, a permutation is canonically a self-homeomorphism. -/
def permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E) where
  toFun := Homeomorph.ofDiscrete
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem continuous_apply_homeomorph (x : E) :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    Continuous fun h : E ≃ₜ E ↦ h x := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
  let e : C(E, E) ≃ₜ (E → E) := ContinuousMap.homeoFnOfDiscrete
  have hcont : Continuous (((↑) : (E ≃ₜ E) → C(E, E))) :=
    continuous_induced_dom
  simpa using (continuous_apply x).comp (e.continuous.comp hcont)

private theorem continuous_inv_homeomorphCompactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    Continuous fun h : E ≃ₜ E ↦ h⁻¹ := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
  refine continuous_induced_rng.2 ?_
  let e : C(E, E) ≃ₜ (E → E) := ContinuousMap.homeoFnOfDiscrete
  refine e.isInducing.continuous_iff.2 ?_
  refine continuous_pi fun x : E ↦ ?_
  rw [continuous_discrete_rng]
  intro y
  convert (isOpen_discrete {x}).preimage (continuous_apply_homeomorph y) using 1
  ext h
  simpa [eq_comm] using (h.symm_apply_eq : h⁻¹ x = y ↔ x = h y)

/-- For a discrete space `E`, the compact-open topology on the homeomorphism group `E ≃ₜ E`
is a group topology. -/
def homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E) where
  toTopologicalSpace := homeomorphCompactOpenTopology
  toIsTopologicalGroup := by
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenTopology : TopologicalSpace (E ≃ₜ E))
    refine
      { continuous_mul := by
          have hcont : Continuous (((↑) : (E ≃ₜ E) → C(E, E))) :=
            continuous_induced_dom
          have hfst : Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦ (p.2 : C(E, E)) :=
            hcont.comp continuous_snd
          have hsnd : Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦ (p.1 : C(E, E)) :=
            hcont.comp continuous_fst
          refine continuous_induced_rng.2 ?_
          have hpair :
              Continuous fun p : (E ≃ₜ E) × (E ≃ₜ E) ↦
                ((p.2 : C(E, E)), (p.1 : C(E, E))) :=
            hfst.prodMk hsnd
          simpa using (ContinuousMap.continuous_comp'.comp hpair)
        continuous_inv := continuous_inv_homeomorphCompactOpen }

/-- Example 5.30.2: for a discrete space `E`, the compact-open topology on the self-homeomorphism
group `E ≃ₜ E` makes `Aut(E)` into a topological group. -/
theorem selfHomeomorphGroup_isTopologicalGroup_compactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    IsTopologicalGroup (E ≃ₜ E) :=
by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  exact (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toIsTopologicalGroup

/-- Under the discrete identification `Equiv.Perm E ≃ E ≃ₜ E`, the permutation presentation
inherits the compact-open topology as the induced bridge topology from the canonical owner
`E ≃ₜ E`. -/
theorem permutationGroup_compactOpen_isHomeomorph :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    letI : TopologicalSpace (Equiv.Perm E) :=
      TopologicalSpace.induced
        ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
    IsHomeomorph ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  letI : TopologicalSpace (Equiv.Perm E) :=
    TopologicalSpace.induced
      ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
  refine (isHomeomorph_iff_isEmbedding_surjective).2 ?_
  refine ⟨⟨⟨rfl⟩, ?_⟩, ?_⟩
  · intro σ τ hστ
    change Homeomorph.ofDiscrete σ = Homeomorph.ofDiscrete τ at hστ
    exact congrArg Homeomorph.toEquiv hστ
  · intro h
    refine ⟨h.toEquiv, ?_⟩
    ext x
    rfl

/-- Bridge form of Example 5.30.2: under the discrete identification
`Equiv.Perm E ≃ E ≃ₜ E`, the permutation model carries the induced compact-open group topology. -/
theorem permutationGroup_isTopologicalGroup_compactOpen :
    letI : TopologicalSpace (E ≃ₜ E) :=
      (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
    letI : TopologicalSpace (Equiv.Perm E) :=
      TopologicalSpace.induced
        ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
    IsTopologicalGroup (Equiv.Perm E) := by
  letI : TopologicalSpace (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toTopologicalSpace
  letI : IsTopologicalGroup (E ≃ₜ E) :=
    (homeomorphCompactOpenGroupTopology : GroupTopology (E ≃ₜ E)).toIsTopologicalGroup
  letI : TopologicalSpace (Equiv.Perm E) :=
    TopologicalSpace.induced
      ((permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E)) : Equiv.Perm E → E ≃ₜ E) inferInstance
  exact topologicalGroup_induced (permToHomeomorph : Equiv.Perm E →* (E ≃ₜ E))

end
