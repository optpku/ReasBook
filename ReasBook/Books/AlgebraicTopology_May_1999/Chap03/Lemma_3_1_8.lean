/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Assumption_3_1_4
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5
import AlgebraicTopology_May_1999.Chap03.Example_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {E : Type u} {A : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

/-- The projection from a connected component of the pullback of `p` along `f` to the base `A`. -/
def pullbackComponentProj (p : E → B) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    { x : Function.Pullback p f // ConnectedComponents.mk x = D } → A :=
  fun x ↦ Function.Pullback.snd x.1

/-- Helper for Lemma 3.1.8: the pullback projection to the base is continuous. -/
-- This is the ambient continuity fact used to build evenly covered neighborhoods for the
-- pullback projection.
private theorem continuous_pullback_snd {p : E → B} (f : C(A, B)) :
    Continuous (fun x : Function.Pullback p f ↦ x.1.2) := by
  fun_prop

/-- Helper for Lemma 3.1.8: an evenly covered neighborhood for `p` pulls back to an evenly covered
neighborhood for the pullback projection. -/
-- The homeomorphism over the pulled-back neighborhood is obtained by keeping the `A`-coordinate
-- and using the original trivialization on the `E`-coordinate.
theorem pullbackSnd_isEvenlyCovered {p : E → B} (f : C(A, B)) (a : A)
    (I := p ⁻¹' ({f a} : Set B)) [DiscreteTopology I] {V : Set B}
    (haV : f a ∈ V) (hV : IsOpen V) (H : p ⁻¹' V ≃ₜ V × I)
    (hH : ∀ e, (H e).1.1 = p e) :
    IsEvenlyCovered (fun x : Function.Pullback p f ↦ x.1.2) a I := by
  have hU : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  have hqU : IsOpen ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) := by
    simpa using hU.preimage (continuous_pullback_snd f)
  let toFun :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) →
        (f ⁻¹' V) × I :=
    fun x ↦
      let hxV : p x.1.1.1 ∈ V := by
        have hxU : f x.1.1.2 ∈ V := x.2
        simpa [x.1.2] using hxU
      (⟨x.1.1.2, x.2⟩, (H ⟨x.1.1.1, hxV⟩).2)
  let invBase : (f ⁻¹' V) × I → Function.Pullback p f :=
    fun y ↦
      let z : p ⁻¹' V := H.symm (⟨f y.1.1, y.1.2⟩, y.2)
      let hz : p z.1 = f y.1.1 := by
        have hzH : H z = (⟨f y.1.1, y.1.2⟩, y.2) := H.apply_symm_apply _
        simpa [hzH] using (hH z).symm
      ⟨(z.1, y.1.1), hz⟩
  have hInvMem :
      ∀ y : (f ⁻¹' V) × I,
        invBase y ∈ (fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V) := by
    intro y
    simp [invBase]
  let invFun :
      (f ⁻¹' V) × I →
        ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) :=
    fun y ↦ ⟨invBase y, hInvMem y⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let z : p ⁻¹' V := by
      have hxV : p x.1.1.1 ∈ V := by
        have hxU : f x.1.1.2 ∈ V := x.2
        simpa [x.1.2] using hxU
      exact ⟨x.1.1.1, hxV⟩
    have hzfst : (⟨f x.1.1.2, x.2⟩ : V) = (H z).1 := by
      apply Subtype.ext
      simpa [z, hH z] using x.1.2.symm
    have hzsymm : H.symm (⟨f x.1.1.2, x.2⟩, (H z).2) = z := by
      have hpair : (⟨f x.1.1.2, x.2⟩, (H z).2) = H z := Prod.ext hzfst rfl
      simp [hpair, z]
    ext <;> simp [toFun, invFun, invBase, z, hzsymm]
  have hRight : Function.RightInverse invFun toFun := by
    intro y
    simp [toFun, invFun, invBase]
  let e :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' (f ⁻¹' V)) ≃ₜ
        (f ⁻¹' V) × I :=
    { toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        dsimp [toFun]
        fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ hInvMem
        dsimp [invBase]
        fun_prop }
  refine ⟨inferInstance, f ⁻¹' V, haV, hU, hqU, e, ?_⟩
  intro x
  rfl

/-- Helper for Lemma 3.1.8: the projection from the full pullback to `A` is surjective. -/
-- Surjectivity is immediate because `p` is surjective and the pullback condition only asks for a
-- point of the fiber of `p` over `f a`.
theorem pullbackSnd_surjective {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B)) :
    Function.Surjective (fun x : Function.Pullback p f ↦ x.1.2) := by
  intro a
  rcases hp.surjective (f a) with ⟨e, he⟩
  exact ⟨⟨(e, a), he⟩, rfl⟩

/-- Helper for Lemma 3.1.8: the projection from the full pullback to `A` is a covering map. -/
-- Each evenly covered neighborhood for `p` over `f a` pulls back to an evenly covered
-- neighborhood for the pullback projection over `a`, and then the fiber is identified with the
-- actual pullback fiber over `a`.
theorem pullbackSnd_isCoveringMap {p : E → B} (hp : IsPathConnectedCoveringMap p)
    (f : C(A, B)) : IsCoveringMap (fun x : Function.Pullback p f ↦ x.1.2) := by
  intro a
  rcases hp.2 (f a) with ⟨_hdisc, V, haV, hV, _hVPath, _hpV, H, hH⟩
  let toFiber :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) →
        (p ⁻¹' ({f a} : Set B)) :=
    fun x ↦
      let hxa : x.1.1.2 = a := Set.mem_singleton_iff.mp x.2
      ⟨x.1.1.1, by simpa [hxa] using x.1.2⟩
  let fromFiberBase : (p ⁻¹' ({f a} : Set B)) → Function.Pullback p f :=
    fun y ↦
      let hy : p y.1 = f a := Set.mem_singleton_iff.mp y.2
      ⟨(y.1, a), hy⟩
  have hFromFiberMem :
      ∀ y : p ⁻¹' ({f a} : Set B),
        fromFiberBase y ∈ (fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A) := by
    intro y
    simp [fromFiberBase]
  let fromFiber :
      (p ⁻¹' ({f a} : Set B)) →
        ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) :=
    fun y ↦ ⟨fromFiberBase y, hFromFiberMem y⟩
  have hLeftFiber : Function.LeftInverse fromFiber toFiber := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hxa : x.1.1.2 = a := Set.mem_singleton_iff.mp x.2
    ext <;> simp [toFiber, fromFiber, fromFiberBase, hxa]
  have hRightFiber : Function.RightInverse fromFiber toFiber := by
    intro y
    apply Subtype.ext
    simp [toFiber, fromFiber, fromFiberBase]
  let hFiber :
      ((fun x : Function.Pullback p f ↦ x.1.2) ⁻¹' ({a} : Set A)) ≃ₜ
        (p ⁻¹' ({f a} : Set B)) :=
    { toFun := toFiber
      invFun := fromFiber
      left_inv := hLeftFiber
      right_inv := hRightFiber
      continuous_toFun := by
        dsimp [toFiber]
        fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ hFromFiberMem
        dsimp [fromFiberBase]
        fun_prop }
  exact (pullbackSnd_isEvenlyCovered (f := f) (a := a) (I := p ⁻¹' ({f a} : Set B))
      haV hV H hH).of_fiber_homeomorph
    hFiber.symm

/-- Helper for Lemma 3.1.8: the full pullback projection is a path-connected covering map. -/
-- Once the pullback projection is known to be a covering map, Example 3.1.7 upgrades it to the
-- path-connected covering-map notion because the base `A` is locally path connected.
theorem pullbackSnd_isPathConnectedCoveringMap [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B)) :
    IsPathConnectedCoveringMap (fun x : Function.Pullback p f ↦ x.1.2) :=
  (pullbackSnd_isCoveringMap hp f).isPathConnectedCoveringMap (pullbackSnd_surjective hp f)

/-- Helper for Lemma 3.1.8: the connected-component label is constant along one local sheet. -/
-- A local sheet is the image of a path-connected open set under a continuous section, so its image
-- in `ConnectedComponents X` is forced to be constant.
theorem component_constant_on_sheet {X : Type*} [TopologicalSpace X] {q : X → A} {U : Set A}
    {I : Type*} [TopologicalSpace I] (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × I)
    (i : I) (u₀ u : U) :
    ConnectedComponents.mk ((H.symm (u₀, i)).1) = ConnectedComponents.mk ((H.symm (u, i)).1) := by
  let c : C(U, ConnectedComponents X) :=
    ⟨fun u ↦ ConnectedComponents.mk ((H.symm (u, i)).1), by
      refine ConnectedComponents.continuous_coe.comp ?_
      have hpair : Continuous fun u : U ↦ (u, i) := by
        fun_prop
      exact continuous_subtype_val.comp (H.symm.continuous.comp hpair)⟩
  have hConnected : IsConnected U := hUPath.isConnected
  letI : ConnectedSpace U := (isConnected_iff_connectedSpace).mp hConnected
  have hsubset := c.continuous.image_connectedComponent_subset u₀
  have hu : c u ∈ c '' connectedComponent u₀ := by
    rw [PreconnectedSpace.connectedComponent_eq_univ u₀]
    exact ⟨u, by simp, rfl⟩
  have hmem : c u ∈ connectedComponent (c u₀) := hsubset hu
  have hEq : c u = c u₀ := by
    simpa [c, connectedComponent_eq_singleton (c u₀)] using hmem
  exact hEq.symm

/-- Helper for Lemma 3.1.8: belonging to the chosen connected component is constant along a single
local sheet, so it can be checked at the basepoint of the trivialization. -/
-- This rewrites the component predicate on `U × (q ⁻¹' {a})` into one depending only on the
-- sheet index.
theorem sheet_component_iff_at_basepoint {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (u : U) (i : q ⁻¹' ({a} : Set A)) :
    ConnectedComponents.mk ((H.symm (u, i)).1) = D ↔
      ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D := by
  -- The component label does not change as we move in the same local sheet.
  have hsheet :
      ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) =
        ConnectedComponents.mk ((H.symm (u, i)).1) :=
    component_constant_on_sheet hUPath H i ⟨a, haU⟩ u
  simpa [hsheet]

/-- Helper for Lemma 3.1.8: restricting a local trivialization of the full pullback to one
connected component yields a product trivialization over that component. -/
-- The only extra bookkeeping is that the allowed sheets are exactly the ones whose basepoint lies
-- in the chosen connected component.
theorem component_restricted_preimage_homeomorph {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (hH : ∀ x, (H x).1.1 = q x) :
    ∃ h :
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ U } ≃ₜ
          U × { i : q ⁻¹' ({a} : Set A) //
            ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D },
      ∀ x, (h x).1.1 = q x.1 := by
  let e₀ :
      { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ U } ≃ₜ
        { x : q ⁻¹' U // ConnectedComponents.mk x.1 = D } :=
    { toFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro x
        cases x
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let e₁ :
      { x : q ⁻¹' U // ConnectedComponents.mk x.1 = D } ≃ₜ
        { y : U × (q ⁻¹' ({a} : Set A)) //
          ConnectedComponents.mk ((H.symm y).1) = D } :=
    H.subtype fun x => by
      simp
  let e₂ :
      { y : U × (q ⁻¹' ({a} : Set A)) //
          ConnectedComponents.mk ((H.symm y).1) = D } ≃ₜ
        U × { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } :=
    { toFun := fun y ↦
        ⟨y.1.1, ⟨y.1.2,
          (sheet_component_iff_at_basepoint (D := D) haU hUPath H y.1.1 y.1.2).mp y.2⟩⟩
      invFun := fun y ↦
        ⟨(y.1, y.2.1),
          (sheet_component_iff_at_basepoint (D := D) haU hUPath H y.1 y.2.1).mpr y.2.2⟩
      left_inv := by
        intro y
        cases y
        rfl
      right_inv := by
        intro y
        cases y
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  -- First reassociate the nested subtype, then restrict `H`, then rewrite the predicate so it
  -- depends only on the sheet index.
  refine ⟨e₀.trans (e₁.trans e₂), ?_⟩
  intro x
  simpa [e₀, e₁, e₂] using hH ⟨x.1.1, x.2⟩

/-- Helper for Lemma 3.1.8: the allowed sheet indices in the restricted trivialization are
homeomorphic to the actual fiber of the component projection over the basepoint. -/
-- Evaluating a chosen sheet at the basepoint gives the desired fiber point, and the inverse reads
-- off the sheet index from the ambient trivialization.
theorem sheet_index_homeomorph_component_fiber {X : Type*} [TopologicalSpace X] {q : X → A}
    {U : Set A} {a : A} (D : ConnectedComponents X) (haU : a ∈ U)
    (hUPath : IsPathConnected U) (H : q ⁻¹' U ≃ₜ U × (q ⁻¹' ({a} : Set A)))
    (hH : ∀ x, (H x).1.1 = q x) :
    Nonempty (
      { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } ≃ₜ
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) }) := by
  let toFun :
      { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } →
        { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } :=
    fun i ↦
      let x : X := (H.symm (⟨a, haU⟩, i.1)).1
      have hxD : ConnectedComponents.mk x = D := i.2
      have hqa : q x ∈ ({a} : Set A) := by
        have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
          simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
            (H.apply_symm_apply (⟨a, haU⟩, i.1))
        simpa [x] using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'
      ⟨⟨x, hxD⟩, hqa⟩
  let invFun :
      { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } →
        { i : q ⁻¹' ({a} : Set A) //
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } :=
    fun x ↦
      let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
      let hxU : q x.1.1 ∈ U := by
        simpa [hxa] using haU
      let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
      have hxSheet :
          ConnectedComponents.mk ((H.symm ((H ⟨x.1.1, hxU⟩).1, i)).1) = D := by
        have hxBack : H.symm ((H ⟨x.1.1, hxU⟩).1, i) = ⟨x.1.1, hxU⟩ := by
          simp [i]
        simpa [hxBack] using x.1.2
      ⟨i,
        (sheet_component_iff_at_basepoint (D := D) haU hUPath H (H ⟨x.1.1, hxU⟩).1 i).mp
          hxSheet⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro i
    apply Subtype.ext
    have hsecond :
        (H ⟨(H.symm (⟨a, haU⟩, i.1)).1, by
          have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
            simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
              (H.apply_symm_apply (⟨a, haU⟩, i.1))
          simpa using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'⟩).2 = i.1 := by
      simpa using congrArg Prod.snd (H.apply_symm_apply (⟨a, haU⟩, i.1))
    simpa [toFun, invFun, hsecond]
  have hRight : Function.RightInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
    let hxU : q x.1.1 ∈ U := by
      simpa [hxa] using haU
    let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
    have hfst : (H ⟨x.1.1, hxU⟩).1 = ⟨a, haU⟩ := by
      apply Subtype.ext
      simpa [hxa] using hH ⟨x.1.1, hxU⟩
    have hxBack :
        H.symm (⟨a, haU⟩, i) = ⟨x.1.1, hxU⟩ := by
      rw [← hfst]
      simp [i]
    simpa [toFun, invFun, hxa, hxU, i, hxBack]
  -- The two maps are continuous because they are assembled from `H` and subtype projections.
  refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        have hpair : Continuous fun i :
            { i : q ⁻¹' ({a} : Set A) //
              ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
            ((⟨a, haU⟩, i.1) : U × (q ⁻¹' ({a} : Set A))) := by
          fun_prop
        have hBase :
            Continuous fun i :
                { i : q ⁻¹' ({a} : Set A) //
                  ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
              (H.symm (⟨a, haU⟩, i.1)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        have hSub :
            Continuous fun i :
                { i : q ⁻¹' ({a} : Set A) //
                  ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D } =>
              (⟨(H.symm (⟨a, haU⟩, i.1)).1, i.2⟩ :
                { y : X // ConnectedComponents.mk y = D }) := by
          exact Continuous.subtype_mk hBase (fun i ↦ i.2)
        exact Continuous.subtype_mk hSub fun i ↦ by
          have hqa' : ((H (H.symm (⟨a, haU⟩, i.1)))).1.1 = a := by
            simp
          simpa [toFun] using (hH (H.symm (⟨a, haU⟩, i.1))).symm.trans hqa'
      continuous_invFun := by
        have hxU :
            ∀ x : { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) },
              q x.1.1 ∈ U := by
          intro x
          have hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
          simpa [hxa] using haU
        have hBase :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              x.1.1 := by
          exact continuous_subtype_val.comp continuous_subtype_val
        have hLift :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              (⟨x.1.1, hxU x⟩ : q ⁻¹' U) := by
          exact Continuous.subtype_mk hBase hxU
        have hSecond :
            Continuous fun x :
                { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              (H ⟨x.1.1, hxU x⟩).2 := by
          have hComp : Continuous fun x :
              { x : { y : X // ConnectedComponents.mk y = D } // q x.1 ∈ ({a} : Set A) } =>
              H ⟨x.1.1, hxU x⟩ := H.continuous.comp hLift
          exact continuous_snd.comp hComp
        exact Continuous.subtype_mk hSecond fun x ↦ by
          let hxa : q x.1.1 = a := Set.mem_singleton_iff.mp x.2
          let hxU : q x.1.1 ∈ U := by
            simpa [hxa] using haU
          let i : q ⁻¹' ({a} : Set A) := (H ⟨x.1.1, hxU⟩).2
          have hxSheet :
              ConnectedComponents.mk ((H.symm ((H ⟨x.1.1, hxU⟩).1, i)).1) = D := by
            have hxBack : H.symm ((H ⟨x.1.1, hxU⟩).1, i) = ⟨x.1.1, hxU⟩ := by
              simp [i]
            simpa [hxBack] using x.1.2
          simpa [invFun, hxa, hxU, i] using
            (sheet_component_iff_at_basepoint (D := D) haU hUPath H (H ⟨x.1.1, hxU⟩).1 i).mp
              hxSheet }⟩

/-- Lemma 3.1.8: if `D` is a connected component of the pullback of a cover `p : E → B` along a
continuous map `f : A → B`, then the projection `D → A` is again a cover. -/
-- Proof sketch: pull back the path-connected evenly covered neighborhoods supplied by `hp` along
-- `f`, obtaining a covering projection from the full pullback to `A`. Then restrict that
-- projection to the connected component `D`; in the connected locally path-connected base `A`, the
-- image of `D` is clopen, hence all of `A`, and the restricted projection is again a
-- path-connected covering map.
theorem pullbackComponentProj_isPathConnectedCoveringMap [ConnectedSpace A]
    [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    IsPathConnectedCoveringMap (pullbackComponentProj p f D) := by
  let q : Function.Pullback p f → A := fun x ↦ x.1.2
  let s : Set A := Set.range (pullbackComponentProj p f D)
  have hq : IsPathConnectedCoveringMap q := pullbackSnd_isPathConnectedCoveringMap hp f
  have hsClopen : IsClopen s := by
    have hsComplOpen : IsOpen sᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro a ha
      rcases hq.2 a with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
      refine mem_nhds_iff.mpr ⟨U, ?_, hU, haU⟩
      intro b hbU hbRange
      rcases hbRange with ⟨x, rfl⟩
      have hxU : x.1 ∈ q ⁻¹' U := by
        simpa [pullbackComponentProj, q] using hbU
      let i := (H ⟨x.1, hxU⟩).2
      have hsheet :
          ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) =
            ConnectedComponents.mk ((H.symm ((H ⟨x.1, hxU⟩).1, i)).1) :=
        component_constant_on_sheet hUPath H i ⟨a, haU⟩ (H ⟨x.1, hxU⟩).1
      have hxD :
          ConnectedComponents.mk ((H.symm ((H ⟨x.1, hxU⟩).1, i)).1) = D := by
        have hxBack : H.symm ((H ⟨x.1, hxU⟩).1, i) = ⟨x.1, hxU⟩ := by
          simp [i]
        simpa [hxBack] using x.2
      have haRange : a ∈ s := by
        refine ⟨⟨(H.symm (⟨a, haU⟩, i)).1, ?_⟩, ?_⟩
        · exact hsheet.trans hxD
        · have hfst :
              (H (H.symm (⟨a, haU⟩, i))).1 = ⟨a, haU⟩ := by
            simpa using congrArg Prod.fst (H.apply_symm_apply (⟨a, haU⟩, i))
          have hqa : q ((H.symm (⟨a, haU⟩, i)).1) = a := by
            have hqa' : ((H (H.symm (⟨a, haU⟩, i)))).1.1 = a := by
              simpa using congrArg (fun y : U × (q ⁻¹' ({a} : Set A)) => y.1.1)
                (H.apply_symm_apply (⟨a, haU⟩, i))
            simpa [q] using (hH (H.symm (⟨a, haU⟩, i))).symm.trans hqa'
          simpa [s, pullbackComponentProj, q] using hqa
      exact ha haRange
    have hsOpen : IsOpen s := by
      rw [isOpen_iff_mem_nhds]
      intro a ha
      rcases ha with ⟨x, rfl⟩
      rcases hq.2 (pullbackComponentProj p f D x) with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
      refine mem_nhds_iff.mpr ⟨U, ?_, hU, haU⟩
      intro b hbU
      let i := (H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).2
      have hsheet :
          ConnectedComponents.mk ((H.symm (⟨b, hbU⟩, i)).1) =
            ConnectedComponents.mk ((H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1,
              i)).1) :=
        component_constant_on_sheet hUPath H i ⟨b, hbU⟩
          (H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1
      have hxD :
          ConnectedComponents.mk
              ((H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1, i)).1) = D := by
        have hxBack :
            H.symm ((H ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩).1, i) =
              ⟨x.1, by simpa [pullbackComponentProj, q] using haU⟩ := by
          simp [i]
        simpa [hxBack] using x.2
      refine ⟨⟨(H.symm (⟨b, hbU⟩, i)).1, hsheet.trans hxD⟩, ?_⟩
      have hfst :
          (H (H.symm (⟨b, hbU⟩, i))).1 = ⟨b, hbU⟩ := by
        simpa using congrArg Prod.fst (H.apply_symm_apply (⟨b, hbU⟩, i))
      have hqb : q ((H.symm (⟨b, hbU⟩, i)).1) = b := by
        have hqb' : ((H (H.symm (⟨b, hbU⟩, i)))).1.1 = b := by
          simpa using congrArg (fun y : U × (q ⁻¹' ({pullbackComponentProj p f D x} : Set A)) =>
            y.1.1) (H.apply_symm_apply (⟨b, hbU⟩, i))
        simpa [q] using (hH (H.symm (⟨b, hbU⟩, i))).symm.trans hqb'
      simpa [s, pullbackComponentProj, q] using hqb
    exact ⟨isOpen_compl_iff.mp hsComplOpen, hsOpen⟩
  have hsNonempty : s.Nonempty := by
    rcases ConnectedComponents.surjective_coe D with ⟨x, hxD⟩
    refine ⟨pullbackComponentProj p f D ⟨x, hxD⟩, ?_⟩
    exact ⟨⟨x, hxD⟩, rfl⟩
  have hsUniv : s = Set.univ := hsClopen.eq_univ hsNonempty
  have hsurj : Function.Surjective (pullbackComponentProj p f D) := by
    intro a
    have ha : a ∈ s := by simpa [hsUniv]
    simpa [s] using ha
  have hcov : IsCoveringMap (pullbackComponentProj p f D) := by
    intro a
    rcases hq.2 a with ⟨_hdisc, U, haU, hU, hUPath, _hqU, H, hH⟩
    let T :=
      { i : q ⁻¹' ({a} : Set A) //
        ConnectedComponents.mk ((H.symm (⟨a, haU⟩, i)).1) = D }
    rcases component_restricted_preimage_homeomorph (D := D) haU hUPath H hH with
      ⟨Hcomp, hHcomp⟩
    classical
    let hFiber :=
      Classical.choice (sheet_index_homeomorph_component_fiber (D := D) haU hUPath H hH)
    -- The local model is the restricted trivialization of the full pullback over `U`.
    have hEvenlyCoveredT : IsEvenlyCovered (pullbackComponentProj p f D) a T := by
      refine ⟨inferInstance, U, haU, hU, ?_, ?_, ?_⟩
      · have hproj : Continuous (pullbackComponentProj p f D) := by
          simpa [pullbackComponentProj, q] using
            (continuous_pullback_snd f).comp continuous_subtype_val
        simpa using hU.preimage hproj
      · simpa [T, pullbackComponentProj, q] using Hcomp
      · intro x
        simpa [pullbackComponentProj, q, T] using hHcomp x
    -- The restricted sheet index set is homeomorphic to the actual fiber over `a`.
    have hFiber' :
        T ≃ₜ (pullbackComponentProj p f D ⁻¹' ({a} : Set A)) := by
      simpa [T, pullbackComponentProj, q] using hFiber
    exact hEvenlyCoveredT.of_fiber_homeomorph hFiber'
  exact hcov.isPathConnectedCoveringMap hsurj

/-- The projection from a connected component of the pullback of a cover is a covering map in the
mathlib sense. -/
-- Proof sketch: apply `IsPathConnectedCoveringMap.isCoveringMap` to
-- `pullbackComponentProj_isPathConnectedCoveringMap`.
theorem pullbackComponentProj_isCoveringMap [ConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → B} (hp : IsPathConnectedCoveringMap p) (f : C(A, B))
    (D : ConnectedComponents (Function.Pullback p f)) :
    IsCoveringMap (pullbackComponentProj p f D) := by
  -- Once the component projection is known to be path-connected covering, the ordinary covering
  -- map statement is just the forgetful direction from Definition 3.1.5.
  exact (pullbackComponentProj_isPathConnectedCoveringMap hp f D).isCoveringMap
