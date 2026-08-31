module

public import stacks_project.Chap05.Definition_5_11_4
public import stacks_project.Chap05.Definition_5_20_1
public import stacks_project.Chap05.Definition_5_9_1
public import stacks_project.Chap05.Lemma_5_8_16
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
meta import Mathlib.Tactic.Attr.Register
import stacks_project.Chap05.Lemma_5_11_5
import stacks_project.Chap05.Lemma_5_8_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Order Specialization

variable {X : Type u} [TopologicalSpace X] [TopologicalSpace.LocallyNoetherianSpace X]
  [QuasiSober X] [T0Space X] [CatenarySpace X]

/- Domain-style sampling for local existence of dimension functions:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived codimension owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood owner: `TopologicalSpace.LocallyNoetherianSpace.exists_open`
- open-subspace locality owners: `IsLocallyClosed.sober` and `IsLocallyClosed.catenarySpace`

Layer triage:
- `source-facing`: Lemma 5.20.4, asserting existence of a local dimension function near a point
- `core/canonical`: `IsDimensionFunction`, `LocallyNoetherianSpace`, `QuasiSober`, and
  `CatenarySpace`
- `bridge/view`: restriction to a suitable open neighborhood, then construction of an
  integer-valued function on that open subspace

Primitive data versus derived API:
- primitive data already belongs to the owner abstractions `IsDimensionFunction`,
  `LocallyNoetherianSpace`, and `CatenarySpace`
- this file should therefore keep only the source-facing existential theorem on an open subspace,
  rather than introducing a local wrapper for a neighborhood together with its function
-/

omit [TopologicalSpace.LocallyNoetherianSpace X] [QuasiSober X] [T0Space X] [CatenarySpace X] in
/-- Helper for Lemma 5.20.4: transporting a dimension function across a homeomorphism preserves
the dimension-function axioms. -/
theorem Homeomorph.isDimensionFunction_comp_symm {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) {δ : X → ℤ} (hδ : IsDimensionFunction δ) :
    IsDimensionFunction (fun y : Y ↦ δ (e.symm y)) where
  strict_of_specializes := by
    intro y z hyz hyz_ne
    -- Pull the specialization relation back along the inverse homeomorphism.
    exact hδ.strict_of_specializes (hyz.map e.symm.continuous) fun h =>
      hyz_ne <| by
        simpa using congrArg e h
  eq_add_one_of_immediateSpecialization := by
    intro y z hyz
    -- Immediate specializations are preserved because both directions of the homeomorphism are
    -- continuous.
    have hyz_pullback : IsImmediateSpecialization (e.symm y) (e.symm z) := by
      refine ⟨hyz.specializes.map e.symm.continuous, ?_, ?_⟩
      · intro h
        exact hyz.ne <| by
          simpa using congrArg e h
      · intro w hyw hwz
        have hyw' : y ⤳ e w := by
          simpa using hyw.map e.continuous
        have hwz' : e w ⤳ z := by
          simpa using hwz.map e.continuous
        rcases hyz.eq_or_eq hyw' hwz' with h | h
        · left
          simpa using congrArg e.symm h
        · right
          simpa using congrArg e.symm h
    simpa using hδ.eq_add_one_of_immediateSpecialization hyz_pullback

/-- Helper for Lemma 5.20.4: on a sober `T₀` space, irreducible closed subsets identify with
points in the specialization order. -/
private noncomputable def irreducible_closeds_equiv_specialization_points :
    IrreducibleCloseds X ≃o Specialization X := by
  letI : PartialOrder X := specializationOrder X
  let eX : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints (α := X)
  let eS : X ≃o Specialization X :=
    { toEquiv := toEquiv
      map_rel_iff' := by
        intro x y
        rfl }
  exact eX.trans eS

/-- Helper for Lemma 5.20.4: the irreducible-closed/point equivalence sends a point closure to the
original point. -/
@[simp] private theorem irreducible_closeds_equiv_specialization_points_apply_pointClosure
    (x : X) :
    irreducible_closeds_equiv_specialization_points (X := X) (toIrreducibleCloseds x) =
      toEquiv x := by
  letI : PartialOrder X := specializationOrder X
  change toEquiv ((irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds x)) = toEquiv x
  exact congrArg toEquiv ((irreducibleSetEquivPoints (α := X)).right_inv x)

/-- Helper for Lemma 5.20.4: strict containment of irreducible closed subsets gives positive
relative codimension. -/
private theorem codimBetween_pos_of_lt {T T' : IrreducibleCloseds X} (hTT' : T < T') :
    0 < codimBetween T T' hTT'.le := by
  -- Rewrite relative codimension as the coheight of the bottom element in `[T, T']`.
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  change 0 < coheight (⊥ : Set.Icc T T')
  exact coheight_pos_of_lt_top hTT'

/-- Helper for Lemma 5.20.4: a cover relation contributes exactly one unit of relative
codimension once relative codimension is finite. -/
private theorem codimBetween_eq_one_of_covBy
    (hfinite : ∀ ⦃A B : IrreducibleCloseds X⦄ (hAB : A ≤ B), codimBetween A B hAB < ⊤)
    {T T' : IrreducibleCloseds X} (hTT' : T ⋖ T') :
    codimBetween T T' hTT'.le = 1 := by
  -- Route correction: exclude codimension `≥ 2` by producing an intermediate irreducible closed
  -- subset, which contradicts that `T ⋖ T'`.
  have hfin : codimBetween T T' hTT'.le < ⊤ := hfinite hTT'.le
  have hpos : 0 < codimBetween T T' hTT'.le := codimBetween_pos_of_lt hTT'.1
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin.ne
  have hone_lt : (1 : ℕ∞) < codimBetween T T' hTT'.le := by
    cases n with
    | zero =>
        exfalso
        rw [← hn] at hpos
        exact (lt_irrefl _ hpos).elim
    | succ n =>
        cases n with
        | zero =>
            exfalso
            have hone : codimBetween T T' hTT'.le = 1 := by
              simpa using hn.symm
            exact hne hone
        | succ n =>
            rw [← hn]
            exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
  let _ : Fact (T ≤ T') := ⟨hTT'.le⟩
  obtain ⟨U, hTU, hUcoh⟩ :=
    (coe_lt_coheight_iff hfin).1 <| by
      simpa using hone_lt
  have hU_ne_top : U ≠ (⊤ : Set.Icc T T') := by
    intro hU
    simp [hU] at hUcoh
  have hU_lt_top : U < (⊤ : Set.Icc T T') := lt_of_le_of_ne le_top hU_ne_top
  exact ((not_covBy_iff hTT'.1).2 ⟨U.1, by simpa using hTU, by simpa using hU_lt_top⟩) hTT'

/-- Helper for Lemma 5.20.4: a proper specialization induces strict containment of the associated
point closures. -/
private theorem pointClosure_lt_of_proper_specializes {x y : X} (hxy : x ⤳ y) (hxy_ne : x ≠ y) :
    toIrreducibleCloseds y < toIrreducibleCloseds x := by
  refine lt_of_le_of_ne hxy.toIrreducibleCloseds_le ?_
  intro hEq
  exact hxy_ne ((inseparable_iff_eq).1 <| (toIrreducibleCloseds_eq_iff_inseparable).1 hEq.symm)

/-- Helper for Lemma 5.20.4: the relative codimension between point closures is positive for a
proper specialization. -/
theorem pointClosure_codim_pos_of_proper_specializes {x y : X} (hxy : x ⤳ y) (hxy_ne : x ≠ y) :
    0 <
      codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
        hxy.toIrreducibleCloseds_le := by
  -- Proper specialization makes the target point closure strictly smaller.
  exact codimBetween_pos_of_lt (pointClosure_lt_of_proper_specializes hxy hxy_ne)

/-- Helper for Lemma 5.20.4: the relative codimension between point closures is exactly one for an
immediate specialization. -/
theorem pointClosure_codim_eq_one_of_immediateSpecialization {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
      hxy.specializes.toIrreducibleCloseds_le = 1 := by
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  have hcov_points : toEquiv y ⋖ toEquiv x := (isImmediateSpecialization_iff_covBy).1 hxy
  have hcov :
      toIrreducibleCloseds y ⋖ toIrreducibleCloseds x := by
    have hy : e (toIrreducibleCloseds y) = toEquiv y := by
      simp [e]
    have hx : e (toIrreducibleCloseds x) = toEquiv x := by
      simp [e]
    refine (apply_covBy_apply_iff e).1 ?_
    rw [hy, hx]
    exact hcov_points
  -- A cover relation in the irreducible-closed poset contributes one unit of codimension.
  exact codimBetween_eq_one_of_covBy
    (fun _ _ hAB ↦ CatenarySpace.finite_codimBetween (X := X) hAB) hcov

/-- Helper for Lemma 5.20.4: mapping an irreducible closed subset of a closed subtype back to the
ambient space stays inside that closed subset of the ambient space. -/
private theorem irreducibleClosed_map_subtype_subset {S : Set X} (hS : IsClosed S)
    (T : IrreducibleCloseds S) :
    ((IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T :
        IrreducibleCloseds X) : Set X) ⊆ S := by
  -- The mapped subset is the closure of an image already contained in `S`.
  rw [IrreducibleCloseds.coe_map]
  refine closure_minimal ?_ hS
  rintro z ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 5.20.4: bundle the ambient irreducible component through a point as an
irreducible closed subset. -/
private noncomputable def ambientIrreducibleComponent (x : X) : IrreducibleCloseds X :=
  ⟨irreducibleComponent x, (irreducibleComponent_mem_irreducibleComponents x).1,
    isClosed_irreducibleComponent⟩

/-- Helper for Lemma 5.20.4: a point belongs to its ambient irreducible component. -/
private theorem ambientIrreducibleComponent_mem (x : X) :
    x ∈ (ambientIrreducibleComponent x : Set X) :=
  mem_irreducibleComponent

/-- Helper for Lemma 5.20.4: a point closure is contained in any irreducible closed subset that
contains the point. -/
private theorem pointClosure_le_of_mem {T : IrreducibleCloseds X} {x : X}
    (hx : x ∈ (T : Set X)) : toIrreducibleCloseds x ≤ T := by
  -- Specializations out of `x` stay inside every closed subset containing `x`.
  intro z hz
  exact (specializes_iff_mem_closure.mpr hz).mem_closed T.isClosed hx

/-- Helper for Lemma 5.20.4: on an irreducible catenary space, shifting codimension to the top
irreducible closed subset gives an integer-valued candidate for a dimension function. -/
private noncomputable def topIrreducibleClosed [IrreducibleSpace X] : IrreducibleCloseds X :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩

/-- Helper for Lemma 5.20.4: every point closure lies in the top irreducible closed subset of an
irreducible space. -/
private theorem pointClosure_le_topIrreducibleClosed [IrreducibleSpace X] (x : X) :
    toIrreducibleCloseds x ≤ topIrreducibleClosed (X := X) :=
  pointClosure_le_of_mem (by simp [topIrreducibleClosed])

/-- Helper for Lemma 5.20.4: the codimension shift inside a fixed irreducible closed subset,
normalized to vanish at the base point `x`. -/
private noncomputable def codimShiftIn (x : X) (T : IrreducibleCloseds X) (hxT : x ∈ (T : Set X))
    (y : X) (hyT : y ∈ (T : Set X)) : ℤ :=
  -(ENat.toNat
      (codimBetween (toIrreducibleCloseds y) T (pointClosure_le_of_mem hyT)) : ℤ) +
    (ENat.toNat
      (codimBetween (toIrreducibleCloseds x) T (pointClosure_le_of_mem hxT)) : ℤ)

/-- Helper for Lemma 5.20.4: on an irreducible catenary space, shifting codimension to the top
irreducible closed subset gives an integer-valued candidate for a dimension function. -/
private noncomputable def codim_shift_to_top [IrreducibleSpace X] (x : X) : X → ℤ :=
  fun y ↦
    -(ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
          (pointClosure_le_topIrreducibleClosed (X := X) y)) : ℤ) +
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds x) (topIrreducibleClosed (X := X))
          (pointClosure_le_topIrreducibleClosed (X := X) x)) : ℤ)

/-- Helper for Lemma 5.20.4: the codimension shift to the top irreducible closed subset is a
dimension function on an irreducible catenary space. -/
private theorem codim_shift_to_top_isDimensionFunction [IrreducibleSpace X] (x : X) :
    IsDimensionFunction (codim_shift_to_top (X := X) x) where
  strict_of_specializes := by
    intro y z hyz hyz_ne
    -- Additivity in the chain `closure {z} ⊆ closure {y} ⊆ ⊤` isolates the positive codimension
    -- between the point closures.
    have hyz_add :
        codimBetween (toIrreducibleCloseds z) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) z) =
          codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le +
            codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
              (pointClosure_le_topIrreducibleClosed (X := X) y) := by
      simpa using
        (CatenarySpace.codimBetween_additive (X := X) hyz.toIrreducibleCloseds_le
          (pointClosure_le_topIrreducibleClosed (X := X) y))
    have hpos :
        0 < codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
          hyz.toIrreducibleCloseds_le :=
      pointClosure_codim_pos_of_proper_specializes hyz hyz_ne
    have hfinite :
        codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
            hyz.toIrreducibleCloseds_le <
          ⊤ :=
      CatenarySpace.finite_codimBetween hyz.toIrreducibleCloseds_le
    have htop_finite :
        codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) y) <
          ⊤ :=
      CatenarySpace.finite_codimBetween
        (pointClosure_le_topIrreducibleClosed (X := X) y)
    have hnat :
        0 <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le) := by
      exact Nat.pos_of_ne_zero fun hzero ↦
        hpos.ne' <| by
          rw [← ENat.coe_toNat hfinite.ne, hzero]
          rfl
    dsimp [codim_shift_to_top]
    rw [hyz_add, ENat.toNat_add hfinite.ne htop_finite.ne]
    have hnat_int :
        (0 : ℤ) <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.toIrreducibleCloseds_le) := by
      exact_mod_cast hnat
    omega
  eq_add_one_of_immediateSpecialization := by
    intro y z hyz
    -- Along an immediate specialization, the isolated point-closure codimension is exactly one.
    have hyz_add :
        codimBetween (toIrreducibleCloseds z) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) z) =
          codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
              hyz.specializes.toIrreducibleCloseds_le +
            codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
              (pointClosure_le_topIrreducibleClosed (X := X) y) := by
      simpa using
        (CatenarySpace.codimBetween_additive (X := X) hyz.specializes.toIrreducibleCloseds_le
          (pointClosure_le_topIrreducibleClosed (X := X) y))
    have hone :
        codimBetween (toIrreducibleCloseds z) (toIrreducibleCloseds y)
          hyz.specializes.toIrreducibleCloseds_le = 1 :=
      pointClosure_codim_eq_one_of_immediateSpecialization hyz
    have htop_finite :
        codimBetween (toIrreducibleCloseds y) (topIrreducibleClosed (X := X))
            (pointClosure_le_topIrreducibleClosed (X := X) y) <
          ⊤ :=
      CatenarySpace.finite_codimBetween
        (pointClosure_le_topIrreducibleClosed (X := X) y)
    dsimp [codim_shift_to_top]
    rw [hyz_add, hone, ENat.toNat_add (by simp) htop_finite.ne, ENat.toNat_one]
    omega

/-- Helper for Lemma 5.20.4: shrink around `x` so that every ambient irreducible component and
every relevant component of a pairwise overlap through a point of the neighborhood also contains
`x`. -/
private theorem exists_component_overlap_neighborhood [NoetherianSpace X] (x : X) :
    ∃ U : Opens X, x ∈ U ∧
      (∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z) ∧
      (∀ {y Z Z'}, y ∈ U → Z ∈ irreducibleComponents X → Z' ∈ irreducibleComponents X →
        y ∈ Z → y ∈ Z' →
        ∃ C : IrreducibleCloseds X, (C : Set X) ⊆ Z ∩ Z' ∧ x ∈ (C : Set X) ∧
          y ∈ (C : Set X)) := by
  classical
  let _ : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let overlapSet (i j : irreducibleComponents X) : Set X := (i : Set X) ∩ (j : Set X)
  let overlapComponent (i j : irreducibleComponents X) (k : irreducibleComponents (overlapSet i j)) :
      IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : overlapSet i j → X) continuous_subtype_val
      ⟨(k : Set (overlapSet i j)), k.2.1,
        isClosed_of_mem_irreducibleComponents (k : Set (overlapSet i j)) k.2⟩
  let Uset : Set X :=
    (⋂ i : irreducibleComponents X,
      if x ∈ (i : Set X) then (Set.univ : Set X) else ((i : Set X)ᶜ)) ∩
    ⋂ i : irreducibleComponents X,
      ⋂ j : irreducibleComponents X,
        ⋂ k : irreducibleComponents (overlapSet i j),
          if x ∈ (overlapComponent i j k : Set X) then (Set.univ : Set X)
          else ((overlapComponent i j k : Set X)ᶜ)
  have hUset_open : IsOpen Uset := by
    refine IsOpen.inter ?_ ?_
    · -- Delete ambient irreducible components that miss `x`.
      refine isOpen_iInter_of_finite ?_
      intro i
      by_cases hxI : x ∈ (i : Set X)
      · simp [hxI]
      · simpa [hxI] using
          (isClosed_of_mem_irreducibleComponents (i : Set X) i.2).isOpen_compl
    · -- For each pair of ambient components, also delete overlap components missing `x`.
      refine isOpen_iInter_of_finite ?_
      intro i
      refine isOpen_iInter_of_finite ?_
      intro j
      let _ : Finite (irreducibleComponents (overlapSet i j)) :=
        NoetherianSpace.finite_irreducibleComponents.to_subtype
      refine isOpen_iInter_of_finite ?_
      intro k
      by_cases hxK : x ∈ (overlapComponent i j k : Set X)
      · simp [hxK]
      · simpa [hxK] using (overlapComponent i j k).isClosed.isOpen_compl
  let U : Opens X := ⟨Uset, hUset_open⟩
  have hxU : x ∈ U := by
    change x ∈ Uset
    constructor
    · refine Set.mem_iInter.2 ?_
      intro i
      by_cases hxI : x ∈ (i : Set X)
      · simp [hxI]
      · simp [hxI]
    · refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro j
      let _ : Finite (irreducibleComponents (overlapSet i j)) :=
        NoetherianSpace.finite_irreducibleComponents.to_subtype
      refine Set.mem_iInter.2 ?_
      intro k
      by_cases hxK : x ∈ (overlapComponent i j k : Set X)
      · simp [hxK]
      · simp [hxK]
  refine ⟨U, hxU, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y Z hyU hZ hyZ
    let i : irreducibleComponents X := ⟨Z, hZ⟩
    have hyi : y ∈ if x ∈ (i : Set X) then (Set.univ : Set X) else ((i : Set X)ᶜ) := by
      exact Set.mem_iInter.mp hyU.1 i
    by_cases hxZ : x ∈ Z
    · exact hxZ
    · have hy_not : y ∈ (Z : Set X)ᶜ := by
        simpa [i, hxZ] using hyi
      exact False.elim (hy_not hyZ)
  · intro y Z Z' hyU hZ hZ' hyZ hyZ'
    let i : irreducibleComponents X := ⟨Z, hZ⟩
    let j : irreducibleComponents X := ⟨Z', hZ'⟩
    let S : Set X := overlapSet i j
    let yS : S := ⟨y, ⟨hyZ, hyZ'⟩⟩
    let k : irreducibleComponents S :=
      ⟨irreducibleComponent yS, irreducibleComponent_mem_irreducibleComponents yS⟩
    let C : IrreducibleCloseds X := overlapComponent i j k
    have hyC : y ∈ (C : Set X) := by
      -- The chosen overlap component contains the point `y`.
      change y ∈ closure ((Subtype.val : S → X) '' ((k : Set S) : Set S))
      exact subset_closure ⟨yS, mem_irreducibleComponent, rfl⟩
    have hfactor :
        y ∈ if x ∈ (C : Set X) then (Set.univ : Set X) else ((C : Set X)ᶜ) := by
      exact Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hyU.2 i) j) k
    have hxC : x ∈ (C : Set X) := by
      by_cases hxC : x ∈ (C : Set X)
      · exact hxC
      · have hy_not : y ∈ ((C : Set X)ᶜ) := by
          simpa [hxC] using hfactor
        exact False.elim (hy_not hyC)
    have hCsub : (C : Set X) ⊆ Z ∩ Z' := by
      -- The mapped overlap component still lives inside the ambient pairwise intersection.
      have hSclosed : IsClosed S := by
        exact (isClosed_of_mem_irreducibleComponents (i : Set X) i.2).inter
          (isClosed_of_mem_irreducibleComponents (j : Set X) j.2)
      have hsubset : (C : Set X) ⊆ S := irreducibleClosed_map_subtype_subset hSclosed _
      simpa [S, overlapSet, i, j] using hsubset
    exact ⟨C, hCsub, hxC, hyC⟩

/-- Helper for Lemma 5.20.4: on the overlap of two ambient irreducible components through `y`, the
codimension-shift expression does not depend on which component is chosen, provided both components
contain the distinguished base point `x` and a common overlap component through `x` and `y`. -/
private theorem codim_shift_eq_of_overlap_component {x y : X} {Z Z' : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X)
    (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hxZ' : x ∈ Z') (hyZ' : y ∈ Z')
    {C : IrreducibleCloseds X} (hCZ : (C : Set X) ⊆ Z ∩ Z') (hxC : x ∈ (C : Set X))
    (hyC : y ∈ (C : Set X)) :
    codimShiftIn x ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents _ hZ⟩ hxZ y hyZ =
      codimShiftIn x ⟨Z', hZ'.1, isClosed_of_mem_irreducibleComponents _ hZ'⟩ hxZ' y hyZ' := by
  let TZ : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents _ hZ⟩
  let TZ' : IrreducibleCloseds X := ⟨Z', hZ'.1, isClosed_of_mem_irreducibleComponents _ hZ'⟩
  have hCy : toIrreducibleCloseds y ≤ C := pointClosure_le_of_mem hyC
  have hCx : toIrreducibleCloseds x ≤ C := pointClosure_le_of_mem hxC
  -- Additivity along `closure {y} ⊆ C ⊆ Z` and `closure {x} ⊆ C ⊆ Z` exposes the same middle
  -- codimension term, which cancels.
  have hy_add_Z :
      codimBetween (toIrreducibleCloseds y) TZ (pointClosure_le_of_mem hyZ) =
        codimBetween (toIrreducibleCloseds y) C hCy +
          codimBetween C TZ (fun z hz ↦ (hCZ hz).1) := by
    simpa [TZ] using
      (CatenarySpace.codimBetween_additive (X := X) hCy (fun z hz ↦ (hCZ hz).1))
  have hx_add_Z :
      codimBetween (toIrreducibleCloseds x) TZ (pointClosure_le_of_mem hxZ) =
        codimBetween (toIrreducibleCloseds x) C hCx +
          codimBetween C TZ (fun z hz ↦ (hCZ hz).1) := by
    simpa [TZ] using
      (CatenarySpace.codimBetween_additive (X := X) hCx (fun z hz ↦ (hCZ hz).1))
  have hy_add_Z' :
      codimBetween (toIrreducibleCloseds y) TZ' (pointClosure_le_of_mem hyZ') =
        codimBetween (toIrreducibleCloseds y) C hCy +
          codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) := by
    simpa [TZ'] using
      (CatenarySpace.codimBetween_additive (X := X) hCy (fun z hz ↦ (hCZ hz).2))
  have hx_add_Z' :
      codimBetween (toIrreducibleCloseds x) TZ' (pointClosure_le_of_mem hxZ') =
        codimBetween (toIrreducibleCloseds x) C hCx +
          codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) := by
    simpa [TZ'] using
      (CatenarySpace.codimBetween_additive (X := X) hCx (fun z hz ↦ (hCZ hz).2))
  have hCy_finite : codimBetween (toIrreducibleCloseds y) C hCy < ⊤ :=
    CatenarySpace.finite_codimBetween hCy
  have hCx_finite : codimBetween (toIrreducibleCloseds x) C hCx < ⊤ :=
    CatenarySpace.finite_codimBetween hCx
  have hCZT_finite : codimBetween C TZ (fun z hz ↦ (hCZ hz).1) < ⊤ :=
    CatenarySpace.finite_codimBetween _
  have hCZ'T_finite : codimBetween C TZ' (fun z hz ↦ (hCZ hz).2) < ⊤ :=
    CatenarySpace.finite_codimBetween _
  dsimp [codimShiftIn]
  rw [hy_add_Z, hx_add_Z, hy_add_Z', hx_add_Z']
  rw [ENat.toNat_add hCy_finite.ne hCZT_finite.ne, ENat.toNat_add hCx_finite.ne hCZT_finite.ne,
    ENat.toNat_add hCy_finite.ne hCZ'T_finite.ne,
    ENat.toNat_add hCx_finite.ne hCZ'T_finite.ne]
  omega

/-- Helper for Lemma 5.20.4: on a neighborhood satisfying the ambient-component condition, define
the codimension shift using the ambient irreducible component of each point. -/
private noncomputable def componentCodimShift {U : Opens X} (x : X)
    (hcomponent : ∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z) :
    U → ℤ :=
  fun u ↦
    codimShiftIn x (ambientIrreducibleComponent (u : X))
      (hcomponent u.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
        (ambientIrreducibleComponent_mem (u : X)))
      (u : X) (ambientIrreducibleComponent_mem (u : X))

/-- Helper for Lemma 5.20.4: once the neighborhood has the overlap property, the ambient
componentwise codimension-shift function computes specialization differences by the codimension
between point closures. -/
private theorem codim_shift_sub_eq_pointClosure_codim {U : Opens X} (x : X)
    (hcomponent : ∀ {y Z}, y ∈ U → Z ∈ irreducibleComponents X → y ∈ Z → x ∈ Z)
    (hoverlap : ∀ {y Z Z'}, y ∈ U → Z ∈ irreducibleComponents X → Z' ∈ irreducibleComponents X →
      y ∈ Z → y ∈ Z' →
      ∃ C : IrreducibleCloseds X, (C : Set X) ⊆ Z ∩ Z' ∧ x ∈ (C : Set X) ∧
        y ∈ (C : Set X)) :
    ∀ {u v : U} (huv : u ⤳ v),
      componentCodimShift (X := X) x hcomponent u -
          componentCodimShift (X := X) x hcomponent v =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ) := by
  intro u v huv
  have huvX : (u : X) ⤳ v := (subtype_specializes_iff u v).1 huv
  have hxComp_u : x ∈ (ambientIrreducibleComponent (u : X) : Set X) :=
    hcomponent u.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
      (ambientIrreducibleComponent_mem (u : X))
  have hvComp_u : (v : X) ∈ (ambientIrreducibleComponent (u : X) : Set X) :=
    huvX.mem_closed (ambientIrreducibleComponent (u : X)).isClosed
      (ambientIrreducibleComponent_mem (u : X))
  have hvComp_v : (v : X) ∈ (ambientIrreducibleComponent (v : X) : Set X) :=
    ambientIrreducibleComponent_mem (v : X)
  -- Rewrite the `v`-term so both codimension shifts are computed in the same ambient component.
  obtain ⟨C, hCsub, hxC, hvC⟩ :=
    hoverlap v.2 (irreducibleComponent_mem_irreducibleComponents (u : X))
      (irreducibleComponent_mem_irreducibleComponents (v : X)) hvComp_u hvComp_v
  have hrewrite :
      codimShiftIn x (ambientIrreducibleComponent (v : X))
          (hcomponent v.2 (irreducibleComponent_mem_irreducibleComponents (v : X))
            (ambientIrreducibleComponent_mem (v : X)))
          (v : X) (ambientIrreducibleComponent_mem (v : X)) =
        codimShiftIn x (ambientIrreducibleComponent (u : X)) hxComp_u (v : X) hvComp_u := by
    simpa [ambientIrreducibleComponent] using
      (codim_shift_eq_of_overlap_component
        (X := X)
        (hZ := irreducibleComponent_mem_irreducibleComponents (v : X))
        (hZ' := irreducibleComponent_mem_irreducibleComponents (u : X))
        (hxZ := hcomponent v.2 (irreducibleComponent_mem_irreducibleComponents (v : X))
          (ambientIrreducibleComponent_mem (v : X)))
        (hyZ := ambientIrreducibleComponent_mem (v : X))
        (hxZ' := hxComp_u)
        (hyZ' := hvComp_u)
        (hCZ := by simpa [Set.inter_comm] using hCsub)
        (hxC := hxC)
        (hyC := hvC))
  have huv_add :
      codimBetween (toIrreducibleCloseds (v : X)) (ambientIrreducibleComponent (u : X))
          (pointClosure_le_of_mem hvComp_u) =
        codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
            huvX.toIrreducibleCloseds_le +
          codimBetween (toIrreducibleCloseds (u : X)) (ambientIrreducibleComponent (u : X))
            (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))) := by
    -- Additivity in the chain `closure {v} ⊆ closure {u} ⊆ IrrComp(u)` gives the claimed
    -- difference formula.
    simpa [ambientIrreducibleComponent] using
      (CatenarySpace.codimBetween_additive (X := X) huvX.toIrreducibleCloseds_le
        (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))))
  have huv_finite :
      codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          huvX.toIrreducibleCloseds_le <
        ⊤ :=
    CatenarySpace.finite_codimBetween huvX.toIrreducibleCloseds_le
  have huComp_finite :
      codimBetween (toIrreducibleCloseds (u : X)) (ambientIrreducibleComponent (u : X))
          (pointClosure_le_of_mem (ambientIrreducibleComponent_mem (u : X))) <
        ⊤ :=
    CatenarySpace.finite_codimBetween _
  dsimp [componentCodimShift]
  rw [hrewrite]
  dsimp [codimShiftIn]
  rw [huv_add, ENat.toNat_add huv_finite.ne huComp_finite.ne]
  omega

/-- Helper for Lemma 5.20.4: an immediate specialization inside an open subset is still immediate
after forgetting the subtype. -/
private theorem ambient_immediate_specialization {U : Opens X} {u v : U}
    (huv : IsImmediateSpecialization u v) : IsImmediateSpecialization (u : X) v := by
  refine ⟨(subtype_specializes_iff u v).1 huv.specializes, ?_, ?_⟩
  · intro h
    exact huv.ne (Subtype.ext h)
  · intro z huz hzv
    have hzU : z ∈ (U : Set X) := hzv.mem_open U.2 v.2
    let zU : U := ⟨z, hzU⟩
    have huzU : u ⤳ zU := (subtype_specializes_iff u zU).2 huz
    have hzUv : zU ⤳ v := (subtype_specializes_iff zU v).2 hzv
    rcases huv.eq_or_eq huzU hzUv with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h

/-- Helper for Lemma 5.20.4: the ambient codimension-shift function on the chosen neighborhood
satisfies the dimension-function axioms. -/
private theorem codim_shift_isDimensionFunction {U : Opens X} (δ : U → ℤ)
    (hsub : ∀ {u v : U} (huv : u ⤳ v), δ u - δ v =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
          ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ)) :
    IsDimensionFunction δ where
  strict_of_specializes := by
    intro u v huv huv_ne
    have huvX : (u : X) ⤳ v := (subtype_specializes_iff u v).1 huv
    -- Proper specialization gives positive point-closure codimension, so the difference is
    -- positive.
    have hpos :=
      pointClosure_codim_pos_of_proper_specializes huvX fun h ↦ huv_ne (Subtype.ext h)
    have hfinite :=
      CatenarySpace.finite_codimBetween huvX.toIrreducibleCloseds_le
    have hnat :
        0 <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
              huvX.toIrreducibleCloseds_le) := by
      exact Nat.pos_of_ne_zero fun hzero ↦
        hpos.ne' <| by
          rw [← ENat.coe_toNat hfinite.ne, hzero]
          rfl
    have hnat_int :
        (0 : ℤ) <
          ENat.toNat
            (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
              huvX.toIrreducibleCloseds_le) := by
      exact_mod_cast hnat
    have hsub_uv := hsub huv
    linarith
  eq_add_one_of_immediateSpecialization := by
    intro u v huv
    -- Immediate specializations in the open subtype remain immediate in the ambient space.
    have huvX : IsImmediateSpecialization (u : X) v := ambient_immediate_specialization huv
    have hsub_uv : δ u - δ v = 1 := by
      have hsub_uv := hsub huv.specializes
      rw [pointClosure_codim_eq_one_of_immediateSpecialization huvX] at hsub_uv
      simpa using hsub_uv
    linarith

/-- Helper for Lemma 5.20.4: in the Noetherian case, the source proof shrinks around `x` so that a
componentwise codimension shift defines a dimension function. -/
private theorem exists_open_neighborhood_with_dimensionFunction_of_noetherian
    [NoetherianSpace X] (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := by
  classical
  -- Route correction: the proof stays in ambient irreducible components of `X`, then shrinks the
  -- open neighborhood until the componentwise codimension shifts agree on every overlap.
  obtain ⟨U, hxU, hcomponent, hoverlap⟩ :=
    exists_component_overlap_neighborhood (X := X) x
  let δ : U → ℤ := componentCodimShift (X := X) x hcomponent
  have hsub :
      ∀ {u v : U} (huv : u ⤳ v), δ u - δ v =
        (ENat.toNat
          (codimBetween (toIrreducibleCloseds (v : X)) (toIrreducibleCloseds (u : X))
            ((subtype_specializes_iff u v).1 huv).toIrreducibleCloseds_le) : ℤ) :=
    codim_shift_sub_eq_pointClosure_codim (X := X) x hcomponent hoverlap
  have hδ : IsDimensionFunction δ := codim_shift_isDimensionFunction δ hsub
  exact ⟨U, hxU, δ, hδ⟩

-- Proof sketch: choose a Noetherian open neighbourhood of `x` using local Noetherianity, solve the
-- problem inside that open subspace, and then transport the resulting dimension function back to
-- the corresponding ambient open subset through the canonical open embedding.
/-- Lemma 5.20.4: in a locally Noetherian, sober, catenary space, every point has an open
neighbourhood whose induced topology admits a dimension function. -/
theorem exists_open_neighborhood_with_dimensionFunction (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := by
  rcases LocallyNoetherianSpace.exists_open x with ⟨N, hxN, hN_noetherian⟩
  let xN : N := ⟨x, hxN⟩
  letI : NoetherianSpace N := hN_noetherian
  letI : QuasiSober N := N.2.isLocallyClosed.quasiSober
  letI : CatenarySpace N := N.2.isLocallyClosed.catenarySpace
  obtain ⟨V, hxV, δ, hδ⟩ :=
    exists_open_neighborhood_with_dimensionFunction_of_noetherian (X := N) xN
  let f : V → X := fun v ↦ v.1.1
  have hfV : Topology.IsOpenEmbedding (fun v : V ↦ (v : N)) := V.isOpenEmbedding'
  have hfN : Topology.IsOpenEmbedding (fun n : N ↦ (n : X)) := N.isOpenEmbedding'
  have hf : Topology.IsOpenEmbedding f := by
    simpa [f] using hfN.comp hfV
  let W : Opens X := ⟨Set.range f, hf.isOpen_range⟩
  have hxW : x ∈ W := by
    exact ⟨⟨xN, hxV⟩, rfl⟩
  let e0 : (Set.univ : Set V) ≃ₜ (f '' (Set.univ : Set V)) :=
    hf.isEmbedding.homeomorphImage Set.univ
  let e1 : V ≃ₜ (Set.univ : Set V) := (Homeomorph.Set.univ V).symm
  let e2 : (f '' (Set.univ : Set V)) ≃ₜ W := Homeomorph.setCongr (by
    ext z
    constructor
    · intro hz
      simpa [W] using hz
    · intro hz
      simpa [W] using hz)
  let e : V ≃ₜ W := e1.trans (e0.trans e2)
  let δW : W → ℤ := fun w ↦ δ (e.symm w)
  have hδW : IsDimensionFunction δW := e.isDimensionFunction_comp_symm hδ
  -- The open subset produced inside the Noetherian neighbourhood pushes forward to an ambient
  -- open neighbourhood of `x`.
  exact ⟨W, hxW, δW, hδW⟩
