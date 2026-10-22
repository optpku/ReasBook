/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Fact_1_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Remark_2_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open TopologicalSpace
open scoped InnerProductSpace Topology

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_Ioo_isTopologicalBasis :
    IsTopologicalBasis {s : Set ℝ | ∃ a b, s = Set.Ioo a b} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, rfl⟩
    exact isOpen_Ioo
  · intro x s hx hs
    rcases mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hs hx) with
      ⟨a, b, hxIoo, hsubset⟩
    exact ⟨Set.Ioo a b, ⟨a, b, rfl⟩, hxIoo, hsubset⟩

/-- The weakly open half-space cut out by the scalar inequality `⟪x, u⟫ < η` in the weak
topology. -/
private def weakOpenHalfSpace [CompleteSpace H] (u : H) (η : ℝ) : Set (WeakSpace ℝ H) :=
  {x | ⟪(toWeakSpace ℝ H).symm x, u⟫_ℝ < η}

private def IsFiniteWeakOpenHalfSpaceIntersection [CompleteSpace H]
    (s : Set (WeakSpace ℝ H)) : Prop :=
  ∃ ι : Type u, ∃ F : Finset ι, ∃ u : ι → H, ∃ η : ι → ℝ,
    s = ⋂ i ∈ F, weakOpenHalfSpace (u i) (η i)

private theorem isOpen_weakOpenHalfSpace [CompleteSpace H] (u : H) (η : ℝ) :
    IsOpen (weakOpenHalfSpace u η) := by
  simpa [weakOpenHalfSpace] using
    IsOpen.preimage (weakSpace_continuous_inner_right u) isOpen_Iio

private theorem basisElem_isFiniteWeakOpenHalfSpaceIntersection [CompleteSpace H]
    {U : StrongDual ℝ H → Set ℝ} {F : Finset (StrongDual ℝ H)}
    (hU : ∀ l, l ∈ F → U l ∈ ({s : Set ℝ | ∃ a b, s = Set.Ioo a b} : Set (Set ℝ))) :
    IsFiniteWeakOpenHalfSpaceIntersection
      (((fun x : WeakSpace ℝ H ↦ fun l ↦ l ((toWeakSpace ℝ H).symm x)) ⁻¹'
        ((F : Set (StrongDual ℝ H)).pi U) : Set (WeakSpace ℝ H))) := by
  classical
  let J := {l // l ∈ F} × Bool
  have hIoo : ∀ l : {l // l ∈ F}, ∃ a b, U l.1 = Set.Ioo a b := by
    intro l
    exact hU l.1 l.2
  choose a b hab using hIoo
  refine ⟨J, Finset.univ, ?_, ?_, ?_⟩
  · intro j
    exact
      if j.2 then
        (InnerProductSpace.toDual ℝ H).symm j.1.1
      else
        -((InnerProductSpace.toDual ℝ H).symm j.1.1)
  · intro j
    exact if j.2 then b j.1 else -(a j.1)
  · ext x
    simp [weakOpenHalfSpace, Set.pi_def]
    constructor
    · intro hx j
      rcases j with ⟨⟨l, hl⟩, jflag⟩
      have hUl : U l = Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := hab ⟨l, hl⟩
      have hxIoo : l ((toWeakSpace ℝ H).symm x) ∈ Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := by
        rw [← hUl]
        exact hx l hl
      have hxl :
          a ⟨l, hl⟩ < ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ ∧
            ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              b ⟨l, hl⟩ := by
        simpa [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using hxIoo
      by_cases hflag : jflag = true
      · simp [hflag, hxl.2]
      · have :
            -⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              -a ⟨l, hl⟩ := by
          linarith
        simp [hflag, inner_neg_right, this]
    · intro hx l hl
      have hupper := hx ⟨⟨l, hl⟩, true⟩
      have hlower := hx ⟨⟨l, hl⟩, false⟩
      have hlower' :
          a ⟨l, hl⟩ < ⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ := by
        have :
            -⟪(toWeakSpace ℝ H).symm x, (InnerProductSpace.toDual ℝ H).symm l⟫_ℝ <
              -a ⟨l, hl⟩ := by
          simpa [inner_neg_right] using hlower
        linarith
      have hUl : U l = Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := hab ⟨l, hl⟩
      have hxIoo :
          l ((toWeakSpace ℝ H).symm x) ∈ Set.Ioo (a ⟨l, hl⟩) (b ⟨l, hl⟩) := by
        simpa [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using ⟨hlower', hupper⟩
      rw [hUl]
      exact hxIoo

private theorem isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections
    [CompleteSpace H] {s : Set (WeakSpace ℝ H)} :
    IsOpen s ↔
      ∃ T : Set (Set (WeakSpace ℝ H)),
        s = ⋃₀ T ∧ ∀ t ∈ T, IsFiniteWeakOpenHalfSpaceIntersection t := by
  classical
  let e : WeakSpace ℝ H → StrongDual ℝ H → ℝ :=
    fun x l ↦ l ((toWeakSpace ℝ H).symm x)
  let B : Set (Set (StrongDual ℝ H → ℝ)) :=
    {S | ∃ U : StrongDual ℝ H → Set ℝ, ∃ F : Finset (StrongDual ℝ H),
      (∀ l, l ∈ F → U l ∈ ({s : Set ℝ | ∃ a b, s = Set.Ioo a b} : Set (Set ℝ))) ∧
        S = (F : Set (StrongDual ℝ H)).pi U}
  have hB :
      IsTopologicalBasis (t := inferInstance) ((fun a ↦ e ⁻¹' a) '' B) := by
    exact (isTopologicalBasis_pi fun _ : StrongDual ℝ H ↦ real_Ioo_isTopologicalBasis).induced e
  constructor
  · intro hs
    rcases hB.open_eq_sUnion hs with ⟨T, hTB, hTs⟩
    refine ⟨T, hTs, ?_⟩
    intro t ht
    rcases hTB ht with ⟨S, hS, rfl⟩
    rcases hS with ⟨U, F, hU, rfl⟩
    exact basisElem_isFiniteWeakOpenHalfSpaceIntersection hU
  · rintro ⟨T, rfl, hT⟩
    refine isOpen_sUnion fun t ht ↦ ?_
    rcases hT t ht with ⟨ι, F, u, η, rfl⟩
    exact isOpen_biInter_finset fun i hi ↦ isOpen_weakOpenHalfSpace (u i) (η i)

/-- Text 2.0.13 (1): a subset of a real Hilbert space is weakly open iff it is a union of finite
intersections of weakly open half-spaces, and canonically this means that its image in
`WeakSpace ℝ H` is open. -/
theorem isOpen_image_toWeakSpace_iff_exists_sUnion_eq_biInter_inner_halfSpace
    [CompleteSpace H] {C : Set H} :
    IsOpen ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∃ S : Set (Set H), C = ⋃₀ S ∧
        ∀ s ∈ S, ∃ ι : Type u, ∃ F : Finset ι, ∃ u : ι → H, ∃ η : ι → ℝ,
          s = ⋂ i ∈ F, {x : H | ⟪x, u i⟫_ℝ < η i} := by
  classical
  constructor
  · intro hC
    rcases
      isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections.mp hC with
      ⟨T, hTunion, hT⟩
    refine ⟨{s : Set H | ∃ t ∈ T, s = (toWeakSpace ℝ H).symm '' t}, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        have hxImage : toWeakSpace ℝ H x ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
          ⟨x, hx, rfl⟩
        rw [hTunion] at hxImage
        rcases Set.mem_sUnion.mp hxImage with ⟨t, htT, hxt⟩
        exact
          Set.mem_sUnion.mpr
            ⟨(toWeakSpace ℝ H).symm '' t, ⟨t, htT, rfl⟩, ⟨toWeakSpace ℝ H x, hxt, by simp⟩⟩
      · rintro ⟨s, ⟨t, htT, rfl⟩, hx⟩
        rcases hx with ⟨y, hy, rfl⟩
        have hyImage : y ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) := by
          rw [hTunion]
          exact Set.mem_sUnion.mpr ⟨t, htT, hy⟩
        rcases hyImage with ⟨z, hz, rfl⟩
        simpa using hz
    · intro s hs
      rcases hs with ⟨t, htT, rfl⟩
      rcases hT t htT with ⟨ι, F, u, η, rfl⟩
      refine ⟨ι, F, u, η, ?_⟩
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = toWeakSpace ℝ H x := by
          simpa using congrArg (toWeakSpace ℝ H) hyx
        simpa [weakOpenHalfSpace, this] using hy
      · intro hx
        refine ⟨toWeakSpace ℝ H x, ?_, by simp⟩
        simpa [weakOpenHalfSpace] using hx
  · rintro ⟨S, hSunion, hS⟩
    let T : Set (Set (WeakSpace ℝ H)) :=
      {t | ∃ s ∈ S, t = (toWeakSpace ℝ H) '' s}
    have hTunion : ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) = ⋃₀ T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hSunion] at hx
        rcases Set.mem_sUnion.mp hx with ⟨s, hsS, hxs⟩
        exact Set.mem_sUnion.mpr ⟨(toWeakSpace ℝ H) '' s, ⟨s, hsS, rfl⟩, ⟨x, hxs, rfl⟩⟩
      · rintro ⟨t, ⟨s, hsS, rfl⟩, hy⟩
        rcases hy with ⟨x, hx, rfl⟩
        refine ⟨x, ?_, rfl⟩
        rw [hSunion]
        exact Set.mem_sUnion.mpr ⟨s, hsS, hx⟩
    have hT : ∀ t ∈ T, IsFiniteWeakOpenHalfSpaceIntersection t := by
      intro t ht
      rcases ht with ⟨s, hsS, rfl⟩
      rcases hS s hsS with ⟨ι, F, u, η, rfl⟩
      refine ⟨ι, F, u, η, ?_⟩
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [weakOpenHalfSpace] using hx
      · intro hy
        refine ⟨(toWeakSpace ℝ H).symm y, ?_, by simp⟩
        simpa [weakOpenHalfSpace] using hy
    exact
      isOpen_iff_exists_sUnion_of_finiteWeakOpenHalfSpaceIntersections.mpr ⟨T, hTunion, hT⟩

/- Text 2.0.13: for a real Hilbert space, weak convergence is convergence in `WeakSpace ℝ H`,
equivalently coordinatewise convergence of inner products against fixed vectors. -/
recall weakConvergence_iff_forall_tendsto_inner_right

/-- Text 2.0.13 (3), weak-closedness clause: a subset of a real Hilbert space is weakly closed iff
it contains the weak limit of every directed net in the set. -/
theorem isClosed_image_toWeakSpace_iff_forall_net_tendsto
    {C : Set H} :
    IsClosed ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∀ ⦃A : Type u⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (ξ : A → H) (x : H),
        (∀ a, ξ a ∈ C) →
          Tendsto (fun a ↦ toWeakSpace ℝ H (ξ a)) atTop (𝓝 (toWeakSpace ℝ H x)) →
            x ∈ C := by
  constructor
  · intro hC A _ _ _ ξ x hξ hlim
    have hxImage :
        ∀ a, toWeakSpace ℝ H (ξ a) ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) := by
      intro a
      exact ⟨ξ a, hξ a, rfl⟩
    have hxClosed :
        toWeakSpace ℝ H x ∈ ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
      hC.mem_of_tendsto hlim (Eventually.of_forall hxImage)
    rcases hxClosed with ⟨y, hy, hyx⟩
    simpa using (toWeakSpace ℝ H).injective hyx ▸ hy
  · intro hC
    rw [← closure_subset_iff_isClosed]
    intro y hy
    rcases (toWeakSpace ℝ H).surjective y with ⟨x, rfl⟩
    rcases (mem_closure_iff_exists_net_tendsto).1 hy with ⟨A, _, _, _, ξ, hξ⟩
    let ζ : A → H := fun a ↦ (toWeakSpace ℝ H).symm (ξ a)
    have hζ : ∀ a, ζ a ∈ C := by
      intro a
      rcases hmem : ξ a with ⟨y, hy⟩
      rcases hy with ⟨z, hz, rfl⟩
      have hEq : ζ a = z := by simp [ζ, hmem]
      exact hEq ▸ hz
    have hlim :
        Tendsto (fun a ↦ toWeakSpace ℝ H (ζ a)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
      simpa [ζ] using hξ
    exact ⟨x, hC ζ x hζ hlim, rfl⟩

/-- Text 2.0.13 (3), weak-compactness clause: a subset of a real Hilbert space is weakly compact
iff every directed net in the set admits a weakly convergent subnet whose limit still belongs to
the set. -/
theorem isCompact_image_toWeakSpace_iff_forall_net_exists_subnet_tendsto
    {C : Set H} :
    IsCompact ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) ↔
      ∀ ⦃A : Type u⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (ξ : A → H),
        (∀ a, ξ a ∈ C) →
          ∃ x ∈ C, ∃ (B : Type*) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
            (φ : B → A),
            Monotone φ ∧ Tendsto φ atTop atTop ∧
              Tendsto (fun b ↦ toWeakSpace ℝ H (ξ (φ b))) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  constructor
  · intro hC A _ _ _ ξ hξ
    have hcompact :
        EveryNetHasConvergentSubnetIn ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H)) :=
      (isCompact_iff_everyNetHasConvergentSubnetIn
        ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H))).1 hC
    rcases hcompact (fun a ↦ toWeakSpace ℝ H (ξ a)) (fun a ↦ ⟨ξ a, hξ a, rfl⟩) with
      ⟨y, hyC, B, _, _, _, φ, hφmono, hφtop, hφtend⟩
    rcases hyC with ⟨x, hx, rfl⟩
    exact ⟨x, hx, B, inferInstance, inferInstance, inferInstance, φ, hφmono, hφtop, hφtend⟩
  · intro hC
    refine
      (isCompact_iff_everyNetHasConvergentSubnetIn
        ((toWeakSpace ℝ H) '' C : Set (WeakSpace ℝ H))).2 ?_
    intro A _ _ _ ξ hξ
    let ζ : A → H := fun a ↦ (toWeakSpace ℝ H).symm (ξ a)
    have hζ : ∀ a, ζ a ∈ C := by
      intro a
      rcases hξ a with ⟨x, hx, hxEq⟩
      have hEq : ζ a = x := by
        simpa [ζ] using (congrArg (toWeakSpace ℝ H).symm hxEq).symm
      exact hEq ▸ hx
    rcases hC ζ hζ with ⟨x, hx, B, _, _, _, φ, hφmono, hφtop, hφtend⟩
    refine ⟨toWeakSpace ℝ H x, ⟨x, hx, rfl⟩, B, inferInstance, inferInstance, inferInstance,
      φ, hφmono, hφtop, ?_⟩
    simpa [ζ, Function.comp] using hφtend
