/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open QuotientGroup
open Topology

variable {G : Type u} [Group G]
variable {H K : O(G)}
variable {X : Type v} [TopologicalSpace X] [MulAction G X]

section Topological

variable [TopologicalSpace G] [DiscreteTopology G]

/-- For a discrete topological group, every quotient `G ⧸ H` is discrete. -/
instance quotientGroup_discreteTopology (H : Subgroup G) : DiscreteTopology (G ⧸ H) :=
  QuotientGroup.discreteTopology (isOpen_discrete (H : Set G))

/-- The compact-open space of continuous `G`-equivariant maps from `G ⧸ H` to `X`. -/
abbrev equivariantContinuousMapSpace (H : O(G)) (X : Type v) [TopologicalSpace X]
    [MulAction G X] :=
  { f : C(G ⧸ H, X) // ∀ g : G, ∀ q : G ⧸ H, f (g • q) = g • f q }

end Topological

/-- An `H`-fixed point of `X` has stabilizer containing `H`. -/
-- Proof sketch: unfold `MulAction.fixedPoints`; the `H`-fixed hypothesis says exactly that every
-- `h : H` fixes `x`, which is the defining condition for membership in the ambient stabilizer.
theorem fixedPoints_le_stabilizer (x : MulAction.fixedPoints H X) :
    H ≤ MulAction.stabilizer G (x : X) := by
  -- Translate the fixed-point condition into the stabilizer membership condition.
  intro h hh
  rw [MulAction.mem_stabilizer_iff]
  exact (MulAction.mem_fixedPoints.mp x.2) ⟨h, hh⟩

/-- The function on `G ⧸ H` determined by an `H`-fixed point `x`, namely `gH ↦ g • x`. -/
def fixedPointsOrbitMap (x : MulAction.fixedPoints H X) : G ⧸ H → X :=
  fun q ↦
    MulAction.ofQuotientStabilizer G (x : X)
      (Subgroup.quotientMapOfLE (fixedPoints_le_stabilizer x) q)

/-- Helper for Problem 3.9.5: on a representative `gH`, the orbit map attached to `x`
is exactly `g • x`. -/
theorem fixedPointsOrbitMap_apply_mk (x : MulAction.fixedPoints H X) (g : G) :
    fixedPointsOrbitMap x ((g : G) : G ⧸ H) = g • (x : X) := by
  -- Evaluate the quotient-stabilizer map on the representative `g`.
  simp [fixedPointsOrbitMap, Subgroup.quotientMapOfLE_apply_mk,
    MulAction.ofQuotientStabilizer_mk]

/-- The orbit-map formula attached to an `H`-fixed point is `G`-equivariant. -/
-- Proof sketch: both `quotientMapOfLE` and `MulAction.ofQuotientStabilizer` respect the left
-- `G`-action on quotient sets, so their composite does as well.
theorem fixedPointsOrbitMap_equivariant (x : MulAction.fixedPoints H X)
    (g : G) (q : G ⧸ H) :
    fixedPointsOrbitMap x (g • q) = g • fixedPointsOrbitMap x q := by
  -- Push the action through the quotient map and then through the quotient-stabilizer map.
  unfold fixedPointsOrbitMap
  rw [Subgroup.quotientMapOfLE_smul]
  simpa using
    (MulAction.ofQuotientStabilizer_smul G (x : X) g
      (Subgroup.quotientMapOfLE (fixedPoints_le_stabilizer x) q))

/-- The orbit map attached to an `H`-fixed point sends the identity coset to that point. -/
-- Proof sketch: the quotient map induced by `H ≤ stab(x)` fixes the identity coset, and
-- `MulAction.ofQuotientStabilizer` sends that identity coset to `x`.
theorem fixedPointsOrbitMap_apply_one (x : MulAction.fixedPoints H X) :
    fixedPointsOrbitMap x ((1 : G) : G ⧸ H) = x := by
  -- Specialize the representative formula to the identity coset.
  simpa using fixedPointsOrbitMap_apply_mk (H := H) x (1 : G)

section Topological

variable [TopologicalSpace G]

/-- Evaluating a `G`-equivariant map `G ⧸ H → X` at the identity coset gives an `H`-fixed point
of `X`. -/
-- Proof sketch: for `h : H`, the coset `hH` equals the identity coset in `G ⧸ H`; apply
-- equivariance of `f` to this equality.
theorem equivariantContinuousMapSpace_evalOne_mem_fixedPoints
    (f : equivariantContinuousMapSpace H X) :
    f.1 ((1 : G) : G ⧸ H) ∈ MulAction.fixedPoints H X := by
  rw [MulAction.mem_fixedPoints]
  intro h
  -- Every `h ∈ H` fixes the identity coset in `G ⧸ H`.
  have hh : (h : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    simpa using
      (QuotientGroup.eq.mpr (show ((h : G)⁻¹ * 1) ∈ H by
        simp [show ((h : G)⁻¹) ∈ (H : Subgroup G) from (H : Subgroup G).inv_mem h.2]) :
          ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H))
  -- Equivariance transports that fixedness to the value of `f` at `1H`.
  calc
    (h : G) • f.1 ((1 : G) : G ⧸ H) = f.1 ((h : G) • ((1 : G) : G ⧸ H)) := by
      symm
      exact f.2 (h : G) (((1 : G) : G ⧸ H))
    _ = f.1 ((1 : G) : G ⧸ H) := by
      simp [hh]

/-- Evaluation at the identity coset sends an equivariant continuous map to its corresponding
`H`-fixed point. -/
def equivariantContinuousMapSpaceEvalOne (f : equivariantContinuousMapSpace H X) :
    MulAction.fixedPoints H X :=
  ⟨f.1 ((1 : G) : G ⧸ H), equivariantContinuousMapSpace_evalOne_mem_fixedPoints f⟩

/-- Evaluation at the identity coset is continuous on the equivariant mapping space. -/
-- Proof sketch: compose the subtype inclusion into `C(G ⧸ H, X)` with the standard continuous
-- evaluation map at the point `1H`.
theorem equivariantContinuousMapSpaceEvalOne_continuous :
    Continuous
      (equivariantContinuousMapSpaceEvalOne :
        equivariantContinuousMapSpace H X → MulAction.fixedPoints H X) := by
  -- First prove continuity of the underlying evaluation map into `X`.
  simpa [equivariantContinuousMapSpaceEvalOne] using
    (Continuous.subtype_mk
      ((continuous_eval_const ((1 : G) : G ⧸ H)).comp continuous_subtype_val)
      fun f => equivariantContinuousMapSpace_evalOne_mem_fixedPoints f)

section Discrete

variable [DiscreteTopology G]

/-- The map `gH ↦ g • x` is continuous because the quotient `G ⧸ H` is discrete. -/
-- Proof sketch: once `G ⧸ H` is given the discrete topology, every function out of it is
-- continuous.
theorem fixedPointsOrbitMap_continuous (x : MulAction.fixedPoints H X) :
    Continuous (fixedPointsOrbitMap x) := by
  letI : DiscreteTopology (G ⧸ H) := quotientGroup_discreteTopology (H := (H : Subgroup G))
  -- Every map out of a discrete space is continuous.
  exact continuous_of_discreteTopology

/-- An `H`-fixed point determines a continuous `G`-equivariant map `G ⧸ H → X`. -/
def fixedPointsToEquivariantContinuousMap (x : MulAction.fixedPoints H X) :
    equivariantContinuousMapSpace H X :=
  ⟨⟨fixedPointsOrbitMap x, fixedPointsOrbitMap_continuous x⟩,
    fixedPointsOrbitMap_equivariant x⟩

/-- Evaluating the orbit map attached to an `H`-fixed point recovers that point. -/
-- Proof sketch: unfold `equivariantContinuousMapSpaceEvalOne` and apply
-- `fixedPointsOrbitMap_apply_one`.
theorem fixedPointsToEquivariantContinuousMap_evalOne (x : MulAction.fixedPoints H X) :
    equivariantContinuousMapSpaceEvalOne (fixedPointsToEquivariantContinuousMap x) = x := by
  -- Compare the two fixed points by their underlying points of `X`.
  apply Subtype.ext
  simpa [equivariantContinuousMapSpaceEvalOne, fixedPointsToEquivariantContinuousMap] using
    fixedPointsOrbitMap_apply_one (H := H) x

/-- An equivariant continuous map is determined by its value on the identity coset. -/
-- Proof sketch: every coset has the form `g • 1H`, so equivariance forces the value at `gH` to be
-- `g • f(1H)`, which is exactly the orbit map attached to `f(1H)`.
theorem fixedPointsToEquivariantContinuousMap_right_inv
    (f : equivariantContinuousMapSpace H X) :
    fixedPointsToEquivariantContinuousMap (equivariantContinuousMapSpaceEvalOne f) = f := by
  -- Compare the two equivariant maps pointwise on quotient representatives.
  apply Subtype.ext
  ext q
  refine Quotient.inductionOn' q ?_
  intro g
  calc
    (fixedPointsToEquivariantContinuousMap (equivariantContinuousMapSpaceEvalOne f)).1
        (g : G ⧸ H) = g • (equivariantContinuousMapSpaceEvalOne f : X) := by
          simp [fixedPointsToEquivariantContinuousMap, fixedPointsOrbitMap_apply_mk]
    _ = g • f.1 ((1 : G) : G ⧸ H) := by
          rfl
    _ = f.1 (g • ((1 : G) : G ⧸ H)) := by
          exact (f.2 g (((1 : G) : G ⧸ H))).symm
    _ = f.1 (g : G ⧸ H) := by
          simp

/-- Evaluation at the identity coset gives the canonical equivalence between equivariant
continuous maps `G ⧸ H → X` and the `H`-fixed point space of `X`. -/
noncomputable def equivariantContinuousMapSpaceEquivFixedPoints :
    equivariantContinuousMapSpace H X ≃ MulAction.fixedPoints H X where
  toFun := equivariantContinuousMapSpaceEvalOne
  invFun := fixedPointsToEquivariantContinuousMap
  left_inv := fixedPointsToEquivariantContinuousMap_right_inv
  right_inv := fixedPointsToEquivariantContinuousMap_evalOne

/-- Helper for Problem 3.9.5: evaluation of the orbit-map family at a fixed coset is continuous
in the fixed point. -/
theorem fixedPointsOrbitMap_eval_continuous [ContinuousConstSMul G X] (q : G ⧸ H) :
    Continuous fun x : MulAction.fixedPoints H X => fixedPointsOrbitMap x q := by
  -- Reduce to quotient representatives, where the map is `x ↦ g • x`.
  refine Quotient.inductionOn' q ?_
  intro g
  simpa [fixedPointsOrbitMap_apply_mk] using
    (continuous_const_smul g).comp continuous_subtype_val

/-- The orbit-map construction is continuous from the `H`-fixed point space into the equivariant
mapping space. -/
-- Proof sketch: the action map `(g, x) ↦ g • x` is continuous in `x` for each fixed `g`, so the
-- family `x ↦ (gH ↦ g • x)` is continuous as a map into the compact-open function space.

theorem fixedPointsToEquivariantContinuousMap_continuous [ContinuousConstSMul G X] :
    Continuous
      (fixedPointsToEquivariantContinuousMap :
        MulAction.fixedPoints H X → equivariantContinuousMapSpace H X) := by
  letI : DiscreteTopology (G ⧸ H) := quotientGroup_discreteTopology (H := (H : Subgroup G))
  -- First build continuity of the underlying family into the plain function space.
  have hfun : Continuous fun x : MulAction.fixedPoints H X => fixedPointsOrbitMap x := by
    exact continuous_pi fun q ↦ fixedPointsOrbitMap_eval_continuous (H := H) (X := X) q
  -- Transport that continuity across the discrete-domain homeomorphism to `C(G ⧸ H, X)`.
  have hcont :
      Continuous fun x : MulAction.fixedPoints H X =>
        ContinuousMap.homeoFnOfDiscrete.symm (fixedPointsOrbitMap x) := by
    exact ContinuousMap.homeoFnOfDiscrete.symm.continuous.comp hfun
  -- Finally restrict to the equivariant subspace using the algebraic equivariance lemma.
  simpa [fixedPointsToEquivariantContinuousMap] using
    (Continuous.subtype_mk hcont fun x => fixedPointsOrbitMap_equivariant x)

/-- Problem 3.9.5 (1): for a `G`-space `X`, the space of `G`-maps `G ⧸ H → X` is naturally
homeomorphic to the `H`-fixed point space `X^H`. -/
noncomputable def equivariantContinuousMapSpaceHomeomorphFixedPoints [ContinuousConstSMul G X] :
    equivariantContinuousMapSpace H X ≃ₜ MulAction.fixedPoints H X where
  toEquiv := equivariantContinuousMapSpaceEquivFixedPoints
  continuous_toFun := equivariantContinuousMapSpaceEvalOne_continuous
  continuous_invFun := fixedPointsToEquivariantContinuousMap_continuous

/-- The homeomorphism of Problem 3.9.5 (1) evaluates an equivariant map at the identity coset. -/
@[simp] theorem equivariantContinuousMapSpaceHomeomorphFixedPoints_apply
    [ContinuousConstSMul G X] (f : equivariantContinuousMapSpace H X) :
    equivariantContinuousMapSpaceHomeomorphFixedPoints f =
      equivariantContinuousMapSpaceEvalOne f :=
  rfl

end Discrete
end Topological

/- Problem 3.9.5 (2): in particular, the orbit-category morphism set
`O(G/H, G/K)` is canonically equivalent to the `H`-fixed point set `(G ⧸ K)^H`. -/
/- This is exactly `Subgroup.orbitCategoryHomEquivFixedPoints`. -/
#check
  (Subgroup.orbitCategoryHomEquivFixedPoints :
    ∀ H K : O(G), (H ⟶ K) ≃ MulAction.fixedPoints H (G ⧸ K))
