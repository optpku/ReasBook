/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part13

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-!
Helpers for Theorem 35.7.

Most of the work is translating the two-variable saddle statement into two one-variable convex
statements that can be fed to the Chapter 24 pointwise-limit theorem, and then translating the
resulting one-variable subdifferential inclusions back into the product saddle subdifferential.
-/

/-- Helper for Theorem 35.7: an ambient-open convex set is relatively open convex (in the
affine-span topology) in the sense of Section 35. -/
lemma helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hsConv : Convex ℝ s) (hsOpen : IsOpen s) :
    IsRelativelyOpenConvex s := by
  refine ⟨hsConv, ?_⟩
  -- The inclusion map from the affine span is continuous, so preimages of open sets are open.
  simpa using hsOpen.preimage (continuous_subtype_val : Continuous fun x : affineSpan ℝ s => (x : E))

/-- Helper for Theorem 35.7: relative openness in the affine-span topology is preserved under a
continuous linear equivalence. -/
lemma helperForTheorem_35_7_isRelativelyOpenConvex_image_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) {s : Set E} (hs : IsRelativelyOpenConvex s) :
    IsRelativelyOpenConvex (e '' s) := by
  classical
  refine ⟨?_, ?_⟩
  · -- Convexity is preserved by affine images.
    simpa using hs.1.affine_image e.toLinearEquiv.toAffineEquiv.toAffineMap
  · -- Transport relative openness along the induced homeomorphism between the affine spans.
    let eAff : E ≃ᵃ[ℝ] F := e.toAffineEquiv
    have hspan_mem :
        ∀ x : E, x ∈ affineSpan ℝ s ↔ e x ∈ affineSpan ℝ (e '' s) := by
      intro x
      have hcomap :
          AffineSubspace.comap (↑eAff : E →ᵃ[ℝ] F) (affineSpan ℝ ((eAff : E → F) '' s)) =
            affineSpan ℝ s := by
        -- `affineSpan` commutes with comap along an affine equivalence.
        simpa [eAff, Set.preimage_image_eq s e.injective] using
          (AffineSubspace.comap_span (f := eAff) (s := ((eAff : E → F) '' s)))
      -- Membership in the affine span is exactly membership in the corresponding comap.
      calc
        x ∈ affineSpan ℝ s ↔
            x ∈ AffineSubspace.comap (↑eAff : E →ᵃ[ℝ] F) (affineSpan ℝ ((eAff : E → F) '' s)) := by
          simpa [hcomap]
        _ ↔ eAff x ∈ affineSpan ℝ ((eAff : E → F) '' s) := by
          simpa [AffineSubspace.mem_comap]
        _ ↔ e x ∈ affineSpan ℝ (e '' s) := by
          simpa [eAff]
    let hspan : affineSpan ℝ s ≃ₜ affineSpan ℝ (e '' s) :=
      Homeomorph.subtype e.toHomeomorph (fun x => hspan_mem x)
    -- Use the homeomorphism between affine spans to transfer openness.
    have hopen_pre :
        IsOpen (hspan ⁻¹' ((fun y : affineSpan ℝ (e '' s) => (y : F)) ⁻¹' (e '' s))) := by
      -- The preimage is the original relatively open set.
      have : hspan ⁻¹' ((fun y : affineSpan ℝ (e '' s) => (y : F)) ⁻¹' (e '' s)) =
          ((fun x : affineSpan ℝ s => (x : E)) ⁻¹' s) := by
        ext x
        have hpreim : (e ⁻¹' (e '' s)) = s := by
          simpa using (Equiv.preimage_image e.toEquiv s)
        -- Reduce to `e x ∈ e '' s ↔ x ∈ s`.
        simpa [hspan, Set.preimage, hpreim]
      simpa [this] using hs.2
    -- Now push openness forward.
    exact (hspan.isOpen_preimage).1 hopen_pre

/-- Helper for Theorem 35.7: from pointwise convergence at every point, the family is pointwise
bounded on `C × D` in the sense required by Theorem 35.2. -/
lemma helperForTheorem_35_7_pointwiseBoundedFamilyOn_of_pointwiseTendsto
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hpoint :
      ∀ u₀ ∈ C, ∀ v₀ ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ v₀) Filter.atTop (nhds (K u₀ v₀))) :
    Function.PointwiseBoundedFamilyOn (fun i : ℕ => Function.uncurry (KSeq i)) (C ×ˢ D) := by
  intro p hp
  have ht :
      Filter.Tendsto (fun i : ℕ => KSeq i p.1 p.2) Filter.atTop (nhds (K p.1 p.2)) :=
    hpoint p.1 hp.1 p.2 hp.2
  -- A convergent sequence has bounded image on some tail set; adjoining the finite initial
  -- segment yields boundedness of the full range.
  rcases Metric.exists_isBounded_image_of_tendsto ht with ⟨s, hsAtTop, hsBdd⟩
  rcases (Filter.mem_atTop_sets.1 hsAtTop) with ⟨N, hNs⟩
  -- Split the range into a finite initial segment and the bounded tail image.
  have hInitFinite :
      (Set.range fun i : {i : ℕ // i < N} => KSeq i.1 p.1 p.2).Finite :=
    (Set.finite_range _)
  have hInitBdd :
      Bornology.IsBounded (Set.range fun i : {i : ℕ // i < N} => KSeq i.1 p.1 p.2) :=
    hInitFinite.isBounded
  have hTailSub :
      (Set.range fun i : {i : ℕ // N ≤ i} => KSeq i.1 p.1 p.2) ⊆ (fun i : ℕ => KSeq i p.1 p.2) '' s := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    refine ⟨i.1, ?_, rfl⟩
    exact hNs i.1 i.2
  have hTailBdd :
      Bornology.IsBounded (Set.range fun i : {i : ℕ // N ≤ i} => KSeq i.1 p.1 p.2) :=
    hsBdd.subset hTailSub
  have hRangeSub :
      (Set.range fun i : ℕ => KSeq i p.1 p.2) ⊆
        (Set.range fun i : {i : ℕ // i < N} => KSeq i.1 p.1 p.2) ∪
          (Set.range fun i : {i : ℕ // N ≤ i} => KSeq i.1 p.1 p.2) := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    by_cases hi : i < N
    · left
      refine ⟨⟨i, hi⟩, rfl⟩
    · right
      refine ⟨⟨i, le_of_not_gt hi⟩, rfl⟩
  exact (hInitBdd.union hTailBdd).subset hRangeSub

/-- Helper for Theorem 35.7: the inverse of a product continuous linear equivalence carries a
product set to the product of the inverse images on each factor. -/
lemma helperForTheorem_35_7_prodCongr_symm_image_prod
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (eE : E ≃L[ℝ] E') (eF : F ≃L[ℝ] F')
    (A : Set E') (B : Set F') :
    (ContinuousLinearEquiv.prodCongr eE eF).symm '' (A ×ˢ B) = (eE.symm '' A) ×ˢ (eF.symm '' B) := by
  -- Expand product membership on both sides and rewrite the inverse map coordinatewise.
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hqA, hqB⟩
    constructor
    · refine ⟨q.1, hqA, ?_⟩
      simp [ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply]
    · refine ⟨q.2, hqB, ?_⟩
      simp [ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply]
  · rintro ⟨hpA, hpB⟩
    rcases hpA with ⟨a, ha, haEq⟩
    rcases hpB with ⟨b, hb, hbEq⟩
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    -- Identify the inverse map coordinatewise.
    ext
    · simpa [ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply] using haEq
    · simpa [ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply] using hbEq

/-- Helper for Theorem 35.7: Pi-type wrapper around Theorem 35.2. This transports the statement
from `EuclideanSpace ℝ (Fin k)` to the Pi-model `Fin k → ℝ` via the canonical linear isometry. -/
lemma helperForTheorem_35_7_section35_theorem35_2_on_pi
    {I : Type*} {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : I → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ i, IsRealConcaveConvexOn C D (K i))
    (hWitness :
      ∃ C' : Set (Fin m → ℝ),
        ∃ D' : Set (Fin n → ℝ),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (K i)) (C' ×ˢ D')) :
    ∀ S : Set ((Fin m → ℝ) × (Fin n → ℝ)),
      S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
        Function.UniformlyBoundedFamilyOn (fun i => Function.uncurry (K i)) S ∧
          Function.EquiLipschitzFamilyOn (fun i => Function.uncurry (K i)) S := by
  -- Route correction: `EuclideanSpace ℝ (Fin k)` is not definitional equal to the plain function
  -- type `Fin k → ℝ` here. To reuse `section35_theorem35_2` we must transport the statement
  -- along the canonical linear isometry between these models of `ℝ^k`.
  classical
  -- Set up the canonical continuous linear equivalences between the Euclidean and Pi models.
  let e_m : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)
  let e_n : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)
  let eProd : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    ContinuousLinearEquiv.prodCongr e_m e_n
  have heProd_symm : eProd.symm = (e_m.symm.prodCongr e_n.symm) := by
    rfl
  -- Transport the relatively open convex sets to EuclideanSpace via the inverse map.
  let C0 : Set (EuclideanSpace ℝ (Fin m)) := e_m.symm '' C
  let D0 : Set (EuclideanSpace ℝ (Fin n)) := e_n.symm '' D
  have hC0 : IsRelativelyOpenConvex C0 := by
    -- Relative openness is invariant under continuous linear equivalences.
    simpa [C0] using
      helperForTheorem_35_7_isRelativelyOpenConvex_image_continuousLinearEquiv
        (e := e_m.symm) (s := C) hC
  have hD0 : IsRelativelyOpenConvex D0 := by
    simpa [D0] using
      helperForTheorem_35_7_isRelativelyOpenConvex_image_continuousLinearEquiv
        (e := e_n.symm) (s := D) hD
  -- Transport the kernel family to EuclideanSpace.
  let K0 : I → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x y => K i (e_m x) (e_n y)
  have hC0_pre : C0 = (e_m ⁻¹' C) := by
    -- `e_m.symm '' C = e_m ⁻¹' C` for an equivalence.
    simpa [C0] using (Equiv.image_eq_preimage (e_m.symm.toEquiv) C)
  have hD0_pre : D0 = (e_n ⁻¹' D) := by
    simpa [D0] using (Equiv.image_eq_preimage (e_n.symm.toEquiv) D)
  have hK0 : ∀ i, IsRealConcaveConvexOn C0 D0 (K0 i) := by
    intro i
    constructor
    · intro y hy
      -- Concavity in the first variable is preserved by precomposing with the affine map `e_m`.
      rcases hy with ⟨y0, hy0, rfl⟩
      have hconc : ConcaveOn ℝ C (fun x => K i x y0) := (hK i).1 y0 hy0
      have hconc' :=
        (ConcaveOn.comp_affineMap (g := e_m.toLinearEquiv.toAffineEquiv.toAffineMap)
          (s := C) hconc)
      -- The domain `C0` is the preimage of `C` under `e_m`.
      simpa [K0, hC0_pre, Function.comp] using hconc'
    · intro x hx
      rcases hx with ⟨x0, hx0, rfl⟩
      have hconv : ConvexOn ℝ D (fun y => K i x0 y) := (hK i).2 x0 hx0
      have hconv' :=
        (ConvexOn.comp_affineMap (g := e_n.toLinearEquiv.toAffineEquiv.toAffineMap)
          (s := D) hconv)
      simpa [K0, hD0_pre, Function.comp] using hconv'
  -- Transport the witness sets and the hull inclusion.
  rcases hWitness with ⟨C', D', hC'sub, hD'sub, hHull, hpb⟩
  let C0' : Set (EuclideanSpace ℝ (Fin m)) := e_m.symm '' C'
  let D0' : Set (EuclideanSpace ℝ (Fin n)) := e_n.symm '' D'
  have hC0'sub : C0' ⊆ C0 := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    exact ⟨u, hC'sub hu, rfl⟩
  have hD0'sub : D0' ⊆ D0 := by
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact ⟨v, hD'sub hv, rfl⟩
  have hImageCD : eProd.symm '' (C ×ˢ D) = (C0 ×ˢ D0) := by
    -- The product equivalence acts coordinatewise, so product sets transport factorwise.
    simpa [C0, D0] using
      helperForTheorem_35_7_prodCongr_symm_image_prod
        (eE := e_m) (eF := e_n) (A := C) (B := D)
  have hImageC'D' : eProd.symm '' (C' ×ˢ D') = (C0' ×ˢ D0') := by
    -- The same coordinatewise transport works for the witness product set.
    simpa [C0', D0'] using
      helperForTheorem_35_7_prodCongr_symm_image_prod
        (eE := e_m) (eF := e_n) (A := C') (B := D')
  have hHull0 :
      C0 ×ˢ D0 ⊆ convexHull ℝ (closure (C0' ×ˢ D0')) := by
    -- Push the hull inclusion through the affine equivalence `eProd.symm`.
    intro p hp
    have hp' : p ∈ eProd.symm '' (C ×ˢ D) := by
      simpa [hImageCD] using hp
    rcases hp' with ⟨q, hqCD, rfl⟩
    have hqHull : q ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull hqCD
    have himage_mem :
        eProd.symm q ∈ eProd.symm '' convexHull ℝ (closure (C' ×ˢ D')) :=
      ⟨q, hqHull, rfl⟩
    have hEq :
        eProd.symm '' convexHull ℝ (closure (C' ×ˢ D')) =
          convexHull ℝ (closure (C0' ×ˢ D0')) := by
      calc
        eProd.symm '' convexHull ℝ (closure (C' ×ˢ D')) =
            convexHull ℝ (eProd.symm '' closure (C' ×ˢ D')) := by
          simpa [eProd] using
            (AffineMap.image_convexHull
              (f := eProd.symm.toLinearEquiv.toAffineEquiv.toAffineMap)
              (s := closure (C' ×ˢ D')))
        _ = convexHull ℝ (closure (eProd.symm '' (C' ×ˢ D'))) := by
          simpa using congrArg (fun t => convexHull ℝ t) (eProd.symm.toHomeomorph.image_closure (C' ×ˢ D'))
        _ = convexHull ℝ (closure (C0' ×ˢ D0')) := by
          simpa [hImageC'D']
    simpa [hEq] using himage_mem
  have hpb0 :
      Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (K0 i)) (C0' ×ˢ D0') := by
    intro p hp
    rcases hp with ⟨hpC, hpD⟩
    rcases hpC with ⟨u, hu, huEq⟩
    rcases hpD with ⟨v, hv, hvEq⟩
    -- Rewrite the point `p` into split form.
    have hpEq : p = (e_m.symm u, e_n.symm v) := by
      refine Prod.ext ?_ ?_
      · simpa using huEq.symm
      · simpa using hvEq.symm
    subst hpEq
    -- This is exactly the original pointwise boundedness.
    have : Bornology.IsBounded (Set.range fun i : I => K i u v) := by
      simpa [Function.uncurry] using hpb (u, v) ⟨hu, hv⟩
    simpa [K0] using this
  have hWitness0 :
      ∃ C' : Set (EuclideanSpace ℝ (Fin m)),
        ∃ D' : Set (EuclideanSpace ℝ (Fin n)),
          C' ⊆ C0 ∧
          D' ⊆ D0 ∧
          C0 ×ˢ D0 ⊆ convexHull ℝ (closure (C' ×ˢ D')) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (K0 i)) (C' ×ˢ D') := by
    refine ⟨C0', D0', hC0'sub, hD0'sub, ?_, hpb0⟩
    simpa [C0', D0'] using hHull0
  -- Finally, apply Theorem 35.2 in EuclideanSpace and transport the conclusions back to the
  -- Pi-model using `eProd.symm`.
  intro S hSsub hSclosed hSbdd
  let S0 : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := eProd.symm '' S
  have hS0sub : S0 ⊆ C0 ×ˢ D0 := by
    -- Membership in `S0` comes from a point of `S`, hence from a point of `C × D`.
    intro p hp
    rcases hp with ⟨q, hqS, rfl⟩
    have hqCD : q ∈ C ×ˢ D := hSsub hqS
    have : eProd.symm q ∈ eProd.symm '' (C ×ˢ D) := ⟨q, hqCD, rfl⟩
    simpa [hImageCD] using this
  have hS0closed : IsClosed S0 := by
    -- `S0` is the preimage of `S` under the continuous equivalence `eProd`.
    have hEq : S0 = eProd ⁻¹' S := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        simpa [Set.preimage]
      · intro hpS
        refine ⟨eProd p, ?_, ?_⟩
        · simpa [Set.preimage] using hpS
        · simp
    simpa [hEq] using hSclosed.preimage eProd.continuous
  have hS0bdd : Bornology.IsBounded S0 :=
    (eProd.symm.lipschitz.isBounded_image hSbdd)
  have h35 :=
    section35_theorem35_2 (I := I) (m := m) (n := n) (C := C0) (D := D0) (K := K0)
      hC0 hD0 hK0 hWitness0 S0 hS0sub hS0closed hS0bdd
  -- Uniform bounds transfer by changing variables along `eProd.symm`.
  have hUbdd : Function.UniformlyBoundedFamilyOn (fun i => Function.uncurry (K i)) S := by
    rcases h35.1 with ⟨α₁, α₂, hα⟩
    refine ⟨α₁, α₂, ?_⟩
    intro i q hqS
    have : eProd.symm q ∈ S0 := ⟨q, hqS, rfl⟩
    have h := hα i (eProd.symm q) this
    simpa [K0, Function.uncurry, eProd] using h
  -- Equi-Lipschitz transfer: compose with the Lipschitz map `eProd.symm`.
  have hEqui : Function.EquiLipschitzFamilyOn (fun i => Function.uncurry (K i)) S := by
    rcases h35.2 with ⟨L, hL⟩
    refine ⟨L * ‖(↑eProd.symm : ( (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) )‖₊, ?_⟩
    intro i
    have hInner :
        LipschitzOnWith ‖(↑eProd.symm : ( (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ]
          (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) )‖₊ (eProd.symm : _ → _) S :=
      (eProd.symm.lipschitz.lipschitzOnWith (s := S))
    have hMaps : Set.MapsTo (eProd.symm : _ → _) S S0 := by
      intro q hqS
      exact ⟨q, hqS, rfl⟩
    -- Compose the Euclidean Lipschitz bound with `eProd.symm`.
    have hComp :=
      (hL i).comp hInner hMaps
    -- Rewrite the composed function into the original kernel.
    simpa [K0, Function.uncurry, eProd, S0, Function.comp] using hComp
  exact ⟨hUbdd, hEqui⟩

/-- Helper for Theorem 35.7: extend a real convex function on a convex set by `⊤` outside the
set, obtaining a global `EReal` convex function (and recording finiteness on the set). -/
lemma helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
    {n : ℕ} {s : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ConvexOn ℝ s f) :
    let F : (Fin n → ℝ) → EReal := fun x => if x ∈ s then ((f x : ℝ) : EReal) else (⊤ : EReal)
    ConvexFunction F ∧ (∀ x ∈ s, F x ≠ (⊤ : EReal) ∧ F x ≠ (⊥ : EReal)) := by
  classical
  intro F
  refine ⟨?_, ?_⟩
  · -- Show convexity of the global epigraph of the `⊤`-extension.
    -- The epigraph is exactly the real epigraph over `s` because outside `s` the value is `⊤`.
    refine (show Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (f := F)) from ?_)
    intro p hp q hq a b ha hb hab
    have hp_mem : p.1 ∈ s := by
      by_contra hnot
      have : (⊤ : EReal) ≤ ((p.2 : ℝ) : EReal) := by
        simpa [epigraph, F, hnot] using hp.2
      exact (not_top_le_coe p.2) this
    have hq_mem : q.1 ∈ s := by
      by_contra hnot
      have : (⊤ : EReal) ≤ ((q.2 : ℝ) : EReal) := by
        simpa [epigraph, F, hnot] using hq.2
      exact (not_top_le_coe q.2) this
    have hr_mem : (a • p.1 + b • q.1) ∈ s :=
      hf.1 hp_mem hq_mem ha hb hab
    have hp_le : f p.1 ≤ p.2 := by
      -- Rewrite the epigraph inequality at a finite point into a real inequality.
      have : ((f p.1 : ℝ) : EReal) ≤ ((p.2 : ℝ) : EReal) := by
        simpa [epigraph, F, hp_mem] using hp.2
      exact (EReal.coe_le_coe_iff).1 this
    have hq_le : f q.1 ≤ q.2 := by
      have : ((f q.1 : ℝ) : EReal) ≤ ((q.2 : ℝ) : EReal) := by
        simpa [epigraph, F, hq_mem] using hq.2
      exact (EReal.coe_le_coe_iff).1 this
    have hf_conv :
        f (a • p.1 + b • q.1) ≤ a * f p.1 + b * f q.1 :=
      hf.2 hp_mem hq_mem ha hb hab
    have hlin :
        a * f p.1 + b * f q.1 ≤ a * p.2 + b * q.2 := by
      nlinarith [hp_le, hq_le, ha, hb]
    have hfinal : f (a • p.1 + b • q.1) ≤ a * p.2 + b * q.2 :=
      le_trans hf_conv hlin
    -- Package the convex combination point back into the epigraph.
    constructor
    · change True
      trivial
    -- Rewrite the epigraph inequality using `F` and the established real bound.
    have : ((f (a • p.1 + b • q.1) : ℝ) : EReal) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal) := by
      exact (EReal.coe_le_coe_iff).2 hfinal
    simpa [epigraph, F, hr_mem, smul_add, add_assoc, add_left_comm, add_comm, mul_assoc,
      mul_left_comm, mul_comm] using this
  · intro x hx
    -- On the base set, the extension takes a real value, hence is finite.
    simp [F, hx, EReal.coe_ne_top, EReal.coe_ne_bot]

/-- Helper for Theorem 35.7: the moving-slice pointwise convergence needed to apply the Chapter 24
pointwise-limit theorem to the one-variable convex slices. -/
lemma helperForTheorem_35_7_pointwiseTendsto_movingSlices
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hKSeq : ∀ i : ℕ, IsRealConcaveConvexOn C D (KSeq i))
    (hpoint :
      ∀ u₀ ∈ C, ∀ v₀ ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ v₀) Filter.atTop (nhds (K u₀ v₀)))
    {u : Fin m → ℝ} {v : Fin n → ℝ} (hu : u ∈ C) (hv : v ∈ D)
    (uSeq : ℕ → Fin m → ℝ) (vSeq : ℕ → Fin n → ℝ)
    (huSeq : ∀ i : ℕ, uSeq i ∈ C) (hvSeq : ∀ i : ℕ, vSeq i ∈ D)
    (huSeq_tendsto : Filter.Tendsto uSeq Filter.atTop (nhds u))
    (hvSeq_tendsto : Filter.Tendsto vSeq Filter.atTop (nhds v)) :
    (∀ u₀ ∈ C,
      Filter.Tendsto (fun i : ℕ => KSeq i u₀ (vSeq i)) Filter.atTop (nhds (K u₀ v))) ∧
    (∀ v₀ ∈ D,
      Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) v₀) Filter.atTop (nhds (K u v₀))) := by
  classical
  -- We will apply Theorem 35.2 (via the Pi wrapper) on small closed balls inside the open sets.
  have hCrel : IsRelativelyOpenConvex C :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen (hsConv := hC_conv) (hsOpen := hC_open)
  have hDrel : IsRelativelyOpenConvex D :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen (hsConv := hD_conv) (hsOpen := hD_open)
  -- The pointwise convergence implies pointwise boundedness on `C × D`.
  have hpb :
      Function.PointwiseBoundedFamilyOn (fun i : ℕ => Function.uncurry (KSeq i)) (C ×ˢ D) := by
    intro p hp
    have ht :
        Filter.Tendsto (fun i : ℕ => KSeq i p.1 p.2) Filter.atTop (nhds (K p.1 p.2)) :=
      hpoint p.1 hp.1 p.2 hp.2
    exact
      helperForTheorem_5_24_8_boundedRange_of_tendsto_real ht
  have hHull :
      C ×ˢ D ⊆ convexHull ℝ (closure (C ×ˢ D)) := by
    intro p hp
    exact (subset_convexHull ℝ (closure (C ×ˢ D))) (subset_closure hp)
  have hWitness :
      ∃ C' : Set (Fin m → ℝ),
        ∃ D' : Set (Fin n → ℝ),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C' ×ˢ D') := by
    refine ⟨C, D, subset_rfl, subset_rfl, ?_, ?_⟩
    · simpa using hHull
    · simpa using hpb
  -- Choose radii so that the relevant closed balls stay inside `C` and `D`.
  obtain ⟨rD, hrDpos, hrDsub⟩ :
      ∃ rD : ℝ, 0 < rD ∧ Metric.closedBall v rD ⊆ D := by
    rcases Metric.isOpen_iff.1 hD_open v hv with ⟨r, hrpos, hrball⟩
    have hr2pos : 0 < r / 2 := by nlinarith
    refine ⟨r / 2, hr2pos, ?_⟩
    intro y hy
    have hr2lt : r / 2 < r := by nlinarith
    have : y ∈ Metric.ball v r := Metric.closedBall_subset_ball hr2lt hy
    exact hrball this
  obtain ⟨rC, hrCpos, hrCsub⟩ :
      ∃ rC : ℝ, 0 < rC ∧ Metric.closedBall u rC ⊆ C := by
    rcases Metric.isOpen_iff.1 hC_open u hu with ⟨r, hrpos, hrball⟩
    have hr2pos : 0 < r / 2 := by nlinarith
    refine ⟨r / 2, hr2pos, ?_⟩
    intro x hx
    have hr2lt : r / 2 < r := by nlinarith
    have : x ∈ Metric.ball u r := Metric.closedBall_subset_ball hr2lt hx
    exact hrball this
  -- The moving sequences eventually stay in these closed balls.
  have hvSeq_ball : ∀ᶠ i in Filter.atTop, vSeq i ∈ Metric.closedBall v rD := by
    have : ∀ᶠ i in Filter.atTop, vSeq i ∈ Metric.ball v rD :=
      hvSeq_tendsto.eventually (Metric.ball_mem_nhds v hrDpos)
    -- A tail in the open ball is also in the closed ball.
    filter_upwards [this] with i hi
    exact Metric.mem_closedBall.2 (le_of_lt hi)
  have huSeq_ball : ∀ᶠ i in Filter.atTop, uSeq i ∈ Metric.closedBall u rC := by
    have : ∀ᶠ i in Filter.atTop, uSeq i ∈ Metric.ball u rC :=
      huSeq_tendsto.eventually (Metric.ball_mem_nhds u hrCpos)
    filter_upwards [this] with i hi
    exact Metric.mem_closedBall.2 (le_of_lt hi)
  -- First component: fixed `u₀` with moving `vSeq i`.
  have hfirst :
      ∀ u₀ ∈ C,
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ (vSeq i)) Filter.atTop (nhds (K u₀ v)) := by
    intro u₀ hu₀
    -- Apply Theorem 35.2 on the slice set `{u₀} × closedBall v rD` to get an equi-Lipschitz bound.
    let S : Set ((Fin m → ℝ) × (Fin n → ℝ)) := ({u₀} : Set (Fin m → ℝ)) ×ˢ Metric.closedBall v rD
    have hSsub : S ⊆ C ×ˢ D := by
      intro p hp
      rcases hp with ⟨hpU, hpV⟩
      have hpU' : p.1 = u₀ := by simpa using hpU
      subst hpU'
      refine ⟨hu₀, hrDsub hpV⟩
    have hSclosed : IsClosed S := by
      simpa [S] using (isClosed_singleton.prod Metric.isClosed_closedBall)
    have hSbdd : Bornology.IsBounded S := by
      simpa [S] using (Bornology.isBounded_singleton.prod Metric.isBounded_closedBall)
    have hLipFam :=
      (helperForTheorem_35_7_section35_theorem35_2_on_pi
        (I := ℕ) (m := m) (n := n) (C := C) (D := D) (K := KSeq)
        hCrel hDrel hKSeq hWitness) S hSsub hSclosed hSbdd
    rcases hLipFam.2 with ⟨L, hL⟩
    -- Control the moving-point error by Lipschitzness on `S`, then use an `ε`-estimate to show it
    -- converges to `0`.
    have hDiffTendsto :
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ (vSeq i) - KSeq i u₀ v) Filter.atTop (nhds 0) := by
      -- First, obtain a uniform Lipschitz bound on the slice set `S`.
      have hDistBound :
          ∀ᶠ i in Filter.atTop,
            dist (KSeq i u₀ (vSeq i)) (KSeq i u₀ v) ≤ (L : ℝ) * dist (vSeq i) v := by
        filter_upwards [hvSeq_ball] with i hvi
        have hmemU : u₀ ∈ ({u₀} : Set (Fin m → ℝ)) := by simp
        have hmem1 : (u₀, vSeq i) ∈ S := ⟨hmemU, hvi⟩
        have hmemV : v ∈ Metric.closedBall v rD := Metric.mem_closedBall_self (le_of_lt hrDpos)
        have hmem2 : (u₀, v) ∈ S := ⟨hmemU, hmemV⟩
        have hdist :=
          (hL i).dist_le_mul (x := (u₀, vSeq i)) (y := (u₀, v)) hmem1 hmem2
        -- On the product, the distance reduces to the distance on the second factor.
        simpa [S, Prod.dist_eq, dist_self, max_eq_right] using hdist
      -- Convert to convergence to `0` using the metric characterization of `Tendsto`.
      refine (Metric.tendsto_nhds.2 ?_)
      intro ε hε
      have hdist0 :
          Filter.Tendsto (fun i : ℕ => dist (vSeq i) v) Filter.atTop (nhds 0) := by
        have hvconst : Filter.Tendsto (fun _ : ℕ => v) Filter.atTop (nhds v) := tendsto_const_nhds
        have hdistvv :
            Filter.Tendsto (fun i : ℕ => dist (vSeq i) v) Filter.atTop (nhds (dist v v)) :=
          hvSeq_tendsto.dist hvconst
        simpa [dist_self] using hdistvv
      -- Choose a small enough neighborhood so that the Lipschitz control is below `ε`.
      have hMpos : 0 < ((L : ℝ) + 1) := by
        have hLnonneg : 0 ≤ (L : ℝ) := L.property
        linarith
      have hsmall :
          ∀ᶠ i in Filter.atTop, dist (vSeq i) v < ε / ((L : ℝ) + 1) := by
        have hεdiv : 0 < ε / ((L : ℝ) + 1) := div_pos hε hMpos
        have h' := (Metric.tendsto_nhds.1 hdist0) (ε / ((L : ℝ) + 1)) hεdiv
        -- `dist (dist (vSeq i) v) 0 < δ` is just `dist (vSeq i) v < δ` since distances are nonnegative.
        filter_upwards [h'] with i hi
        simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg : 0 ≤ dist (vSeq i) v)] using hi
      filter_upwards [hDistBound, hsmall] with i hBound hiSmall
      -- Use `dist_eq_norm` to work with the difference-to-zero target.
      have hε' : (L : ℝ) * dist (vSeq i) v < ε := by
        have hle : (L : ℝ) * dist (vSeq i) v ≤ (L : ℝ) * (ε / ((L : ℝ) + 1)) := by
          have hnonneg : 0 ≤ (L : ℝ) := L.property
          exact mul_le_mul_of_nonneg_left (le_of_lt hiSmall) hnonneg
        have hstrict : (L : ℝ) * (ε / ((L : ℝ) + 1)) < ε := by
          -- Since `L / (L+1) < 1`, we have `L * (ε/(L+1)) < ε`.
          have hfrac : (L : ℝ) / ((L : ℝ) + 1) < 1 := by
            have hdenpos : 0 < ((L : ℝ) + 1) := by nlinarith [L.property]
            have : (L : ℝ) < (L : ℝ) + 1 := by nlinarith
            simpa [div_lt_one hdenpos] using this
          have : (L : ℝ) * (ε / ((L : ℝ) + 1)) = ε * ((L : ℝ) / ((L : ℝ) + 1)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          -- Conclude by multiplying the strict inequality by `ε > 0`.
          have hmul : ε * ((L : ℝ) / ((L : ℝ) + 1)) < ε * 1 := by
            exact mul_lt_mul_of_pos_left hfrac hε
          simpa [this] using hmul
        exact lt_of_le_of_lt hle hstrict
      have hDistLt : dist (KSeq i u₀ (vSeq i)) (KSeq i u₀ v) < ε :=
        lt_of_le_of_lt hBound hε'
      -- Finish by rewriting the distance to `0` in terms of the original difference.
      simpa [Real.dist_eq, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hDistLt
    have hFixed :
        Filter.Tendsto (fun i : ℕ => KSeq i u₀ v) Filter.atTop (nhds (K u₀ v)) :=
      hpoint u₀ hu₀ v hv
    -- Combine fixed-point convergence with vanishing moving-point error.
    have hSum :
        Filter.Tendsto
            (fun i : ℕ => KSeq i u₀ v + (KSeq i u₀ (vSeq i) - KSeq i u₀ v))
            Filter.atTop
            (nhds (K u₀ v + 0)) :=
      hFixed.add hDiffTendsto
    have hSum' :
        Filter.Tendsto
            (fun i : ℕ => KSeq i u₀ v + (KSeq i u₀ (vSeq i) - KSeq i u₀ v))
            Filter.atTop
            (nhds (K u₀ v)) := by
      simpa [add_zero] using hSum
    -- Rewrite the sum back to the moving sequence.
    refine Filter.Tendsto.congr' ?_ hSum'
    filter_upwards with i
    ring
  -- Second component: fixed `v₀` with moving `uSeq i`.
  have hsecond :
      ∀ v₀ ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) v₀) Filter.atTop (nhds (K u v₀)) := by
    intro v₀ hv₀
    let S : Set ((Fin m → ℝ) × (Fin n → ℝ)) := Metric.closedBall u rC ×ˢ ({v₀} : Set (Fin n → ℝ))
    have hSsub : S ⊆ C ×ˢ D := by
      intro p hp
      rcases hp with ⟨hpU, hpV⟩
      have hpV' : p.2 = v₀ := by simpa using hpV
      subst hpV'
      refine ⟨hrCsub hpU, hv₀⟩
    have hSclosed : IsClosed S := by
      simpa [S] using (Metric.isClosed_closedBall.prod isClosed_singleton)
    have hSbdd : Bornology.IsBounded S := by
      simpa [S] using (Metric.isBounded_closedBall.prod Bornology.isBounded_singleton)
    have hLipFam :=
      (helperForTheorem_35_7_section35_theorem35_2_on_pi
        (I := ℕ) (m := m) (n := n) (C := C) (D := D) (K := KSeq)
        hCrel hDrel hKSeq hWitness) S hSsub hSclosed hSbdd
    rcases hLipFam.2 with ⟨L, hL⟩
    have hDiffTendsto :
        Filter.Tendsto (fun i : ℕ => KSeq i (uSeq i) v₀ - KSeq i u v₀) Filter.atTop (nhds 0) := by
      -- As above, use a Lipschitz bound plus an `ε`-estimate.
      have hDistBound :
          ∀ᶠ i in Filter.atTop,
            dist (KSeq i (uSeq i) v₀) (KSeq i u v₀) ≤ (L : ℝ) * dist (uSeq i) u := by
        filter_upwards [huSeq_ball] with i hui
        have hmemV : v₀ ∈ ({v₀} : Set (Fin n → ℝ)) := by simp
        have hmem1 : (uSeq i, v₀) ∈ S := ⟨hui, hmemV⟩
        have hmemU : u ∈ Metric.closedBall u rC := Metric.mem_closedBall_self (le_of_lt hrCpos)
        have hmem2 : (u, v₀) ∈ S := ⟨hmemU, hmemV⟩
        have hdist :=
          (hL i).dist_le_mul (x := (uSeq i, v₀)) (y := (u, v₀)) hmem1 hmem2
        simpa [S, Prod.dist_eq, dist_self, max_eq_left] using hdist
      refine (Metric.tendsto_nhds.2 ?_)
      intro ε hε
      have hdist0 :
          Filter.Tendsto (fun i : ℕ => dist (uSeq i) u) Filter.atTop (nhds 0) := by
        have huconst : Filter.Tendsto (fun _ : ℕ => u) Filter.atTop (nhds u) := tendsto_const_nhds
        have hdistuu :
            Filter.Tendsto (fun i : ℕ => dist (uSeq i) u) Filter.atTop (nhds (dist u u)) :=
          huSeq_tendsto.dist huconst
        simpa [dist_self] using hdistuu
      have hMpos : 0 < ((L : ℝ) + 1) := by
        have hLnonneg : 0 ≤ (L : ℝ) := L.property
        linarith
      have hsmall :
          ∀ᶠ i in Filter.atTop, dist (uSeq i) u < ε / ((L : ℝ) + 1) := by
        have hεdiv : 0 < ε / ((L : ℝ) + 1) := div_pos hε hMpos
        have h' := (Metric.tendsto_nhds.1 hdist0) (ε / ((L : ℝ) + 1)) hεdiv
        filter_upwards [h'] with i hi
        simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg : 0 ≤ dist (uSeq i) u)] using hi
      filter_upwards [hDistBound, hsmall] with i hBound hiSmall
      have hε' : (L : ℝ) * dist (uSeq i) u < ε := by
        have hle : (L : ℝ) * dist (uSeq i) u ≤ (L : ℝ) * (ε / ((L : ℝ) + 1)) := by
          have hnonneg : 0 ≤ (L : ℝ) := L.property
          exact mul_le_mul_of_nonneg_left (le_of_lt hiSmall) hnonneg
        have hstrict : (L : ℝ) * (ε / ((L : ℝ) + 1)) < ε := by
          have hfrac : (L : ℝ) / ((L : ℝ) + 1) < 1 := by
            have hdenpos : 0 < ((L : ℝ) + 1) := by nlinarith [L.property]
            have : (L : ℝ) < (L : ℝ) + 1 := by nlinarith
            simpa [div_lt_one hdenpos] using this
          have : (L : ℝ) * (ε / ((L : ℝ) + 1)) = ε * ((L : ℝ) / ((L : ℝ) + 1)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          have hmul : ε * ((L : ℝ) / ((L : ℝ) + 1)) < ε * 1 := by
            exact mul_lt_mul_of_pos_left hfrac hε
          simpa [this] using hmul
        exact lt_of_le_of_lt hle hstrict
      have hDistLt : dist (KSeq i (uSeq i) v₀) (KSeq i u v₀) < ε :=
        lt_of_le_of_lt hBound hε'
      simpa [Real.dist_eq, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hDistLt
    have hFixed :
        Filter.Tendsto (fun i : ℕ => KSeq i u v₀) Filter.atTop (nhds (K u v₀)) :=
      hpoint u hu v₀ hv₀
    have hSum :=
      hFixed.add hDiffTendsto
    have hSum' :
        Filter.Tendsto
            (fun i : ℕ => KSeq i u v₀ + (KSeq i (uSeq i) v₀ - KSeq i u v₀))
            Filter.atTop
            (nhds (K u v₀)) := by
      simpa [add_zero] using hSum
    refine Filter.Tendsto.congr' ?_ hSum'
    filter_upwards with i
    ring
  exact ⟨hfirst, hsecond⟩

/-- Helper for Theorem 35.7: convert a `limsup` inequality under negation into a `liminf`
inequality for `EReal` sequences. -/
lemma helperForTheorem_35_7_ereal_liminf_of_limsup_neg
    {a : ℕ → EReal} {b : EReal}
    (h : Filter.limsup (fun i : ℕ => -a i) Filter.atTop ≤ -b) :
    b ≤ Filter.liminf a Filter.atTop := by
  -- Rewrite `limsup (-a)` using the `EReal` negation lemma, then flip the inequality.
  have h0 : Filter.limsup (-a) Filter.atTop ≤ -b := by
    simpa using h
  have h' : -Filter.liminf a Filter.atTop ≤ -b := by
    simpa [EReal.limsup_neg] using h0
  exact (EReal.neg_le_neg_iff).1 h'

/-- Helper for Theorem 35.7: bridge the real directional-derivative packaging
`realFirstVariableDirectionalDerivativeValue`/`realSecondVariableDirectionalDerivativeValue` to the
Chapter 23/24 upper directional derivative `upperDirectionalDerivativeAt` of the corresponding
`EReal` convex extensions. -/
lemma helperForTheorem_35_7_realDirectionalDerivativeValue_bridges
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    {u : Fin m → ℝ} {v : Fin n → ℝ} (hu : u ∈ C) (hv : v ∈ D)
    (u' : Fin m → ℝ) (v' : Fin n → ℝ) :
    let f : (Fin m → ℝ) → EReal :=
      fun x => if x ∈ C then ((-(K x v) : ℝ) : EReal) else (⊤ : EReal)
    let g : (Fin n → ℝ) → EReal :=
      fun y => if y ∈ D then ((K u y : ℝ) : EReal) else (⊤ : EReal)
    (((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) =
        -upperDirectionalDerivativeAt f u u') ∧
      (((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) =
        upperDirectionalDerivativeAt g v v') := by
  classical
  intro f g
  -- Step 1 (first variable): identify the real directional derivative package as the negative of
  -- the `EReal` upper directional derivative of the `⊤`-extension of the convex slice `x ↦ -K x v`.
  have hf_convOn : ConvexOn ℝ C (fun x => (-(K x v) : ℝ)) := (hK.1 v hv).neg
  have hfExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := C) (f := fun x => (-(K x v) : ℝ)) hf_convOn
  have hf_conv : ConvexFunction f := by
    simpa [f] using hfExt.1
  have hf_finite : ∀ x ∈ C, f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    simpa [f] using hfExt.2
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := hf_finite u hu
  have hDf_finite_all :
      (∀ y : Fin m → ℝ,
        upperDirectionalDerivativeAt f u y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt f u y ≠ (⊥ : EReal)) := by
    -- This is exactly the "finite directional derivatives on an open convex set" lemma from Chapter 24,
    -- specialized to the constant sequence `fSeq i = f`.
    let fSeq : ℕ → (Fin m → ℝ) → EReal := fun _ => f
    let uSeq0 : ℕ → Fin m → ℝ := fun _ => u
    have hfSeq : ∀ i : ℕ, ConvexFunction (fSeq i) := by
      intro i
      simpa [fSeq] using hf_conv
    have hfSeq_finite : ∀ i : ℕ, ∀ x ∈ C, fSeq i x ≠ (⊤ : EReal) ∧ fSeq i x ≠ (⊥ : EReal) := by
      intro i x hx
      simpa [fSeq] using hf_finite x hx
    have hfinite :=
      helperForTheorem_5_24_8_directionalDerivative_finite_at_limit_and_sequence
        (n := m) (C := C) hC_open hC_conv hf_conv hf_finite fSeq hfSeq hfSeq_finite hu uSeq0
        (fun _ => hu)
    exact hfinite.1
  have hbridgeFirst :
      ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) =
        -upperDirectionalDerivativeAt f u u' := by
    -- The slice directional difference quotients converge to the upper directional derivative.
    rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf_conv u hfu with
      ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
    have hTendstoE :
        Filter.Tendsto (directionalDifferenceQuotientAt f u u') (𝓝[>] (0 : ℝ))
          (nhds (upperDirectionalDerivativeAt f u u')) := (hdir u').2.1
    -- For small `t > 0`, we have `u + t u' ∈ C` (openness), so the `⊤`-extension agrees with `-K`.
    have hcontWithin :
        ContinuousWithinAt (fun t : ℝ => u + t • u') (Set.Ioi (0 : ℝ)) (0 : ℝ) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
    have htend :
        Filter.Tendsto (fun t : ℝ => u + t • u') (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds u) := by
      have hMaps : Set.MapsTo (fun t : ℝ => u + t • u') (Set.Ioi (0 : ℝ)) (Set.univ : Set (Fin m → ℝ)) := by
        intro t ht
        trivial
      -- `nhdsWithin (f 0) univ` is just `nhds (f 0)`.
      simpa using (hcontWithin.tendsto_nhdsWithin hMaps)
    have hmemC : ∀ᶠ t in (𝓝[>] (0 : ℝ)), u + t • u' ∈ C :=
      htend.eventually (hC_open.mem_nhds hu)
    have htpos : ∀ᶠ t in (𝓝[>] (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ) := by
      simpa [Filter.Eventually] using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    have hquot_event :
        directionalDifferenceQuotientAt f u u' =ᶠ[(𝓝[>] (0 : ℝ))]
          (fun t : ℝ => ((-(realSaddleDirectionalDifferenceQuotientAt K u v u' 0 t) : ℝ) : EReal)) := by
      filter_upwards [hmemC, htpos] with t htC htpos
      have htne : (t : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.mp htpos)
      -- Unfold the difference quotient and rewrite it as a coerced real quotient; then reduce to a
      -- real identity.
      have hstep :
          directionalDifferenceQuotientAt f u u' t =
            (((( -(K (u + t • u') v) : ℝ) - (-(K u v) : ℝ)) / t : ℝ) : EReal) := by
        -- Inside `C`, the `⊤`-extension is exactly the real coercion of `-K`.
        simp [directionalDifferenceQuotientAt, f, htC, hu]
        -- Rewrite the coerced negations back into negated coercions so that `EReal.coe_sub` applies.
        rw [← EReal.coe_neg (K (u + t • u') v)]
        rw [← EReal.coe_neg (K u v)]
        -- Rewrite the EReal subtraction/division into coerced real subtraction/division.
        rw [← EReal.coe_sub (-(K (u + t • u') v) : ℝ) (-(K u v) : ℝ)]
        rw [← EReal.coe_div ((-(K (u + t • u') v) : ℝ) - (-(K u v) : ℝ)) t]
        -- Normalize the real numerator.
        simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      -- Finish by comparing the coerced real numerators.
      rw [hstep]
      apply (EReal.coe_eq_coe_iff).2
      -- Unfold the saddle quotient (note `v + t • 0 = v`) and clear denominators.
      simp [realSaddleDirectionalDifferenceQuotientAt, sub_eq_add_neg]
      field_simp [htne]
      ring
    have hDfinite : upperDirectionalDerivativeAt f u u' ≠ (⊤ : EReal) ∧
        upperDirectionalDerivativeAt f u u' ≠ (⊥ : EReal) := hDf_finite_all u'
    let r : ℝ := (upperDirectionalDerivativeAt f u u').toReal
    have hrcoe : ((r : ℝ) : EReal) = upperDirectionalDerivativeAt f u u' := by
      simpa [r] using EReal.coe_toReal hDfinite.1 hDfinite.2
    -- Convert the `EReal` limit statement into a real limit statement.
    have hTendstoE' :
        Filter.Tendsto
          (fun t : ℝ => ((-(realSaddleDirectionalDifferenceQuotientAt K u v u' 0 t) : ℝ) : EReal))
          (𝓝[>] (0 : ℝ)) (nhds ((r : ℝ) : EReal)) := by
      have hTendstoE'' : Filter.Tendsto (directionalDifferenceQuotientAt f u u') (𝓝[>] (0 : ℝ))
          (nhds ((r : ℝ) : EReal)) := by
        simpa [hrcoe] using hTendstoE
      exact Filter.Tendsto.congr' hquot_event hTendstoE''
    have hTendstoRealNeg :
        Filter.Tendsto
          (fun t : ℝ => (-(realSaddleDirectionalDifferenceQuotientAt K u v u' 0 t) : ℝ))
          (𝓝[>] (0 : ℝ)) (nhds r) :=
      (EReal.tendsto_coe).1 hTendstoE'
    have hTendstoReal :
        Filter.Tendsto
          (realSaddleDirectionalDifferenceQuotientAt K u v u' 0)
          (𝓝[>] (0 : ℝ)) (nhds (-r)) := by
      simpa using hTendstoRealNeg.neg
    -- The defining set is a singleton, since limits in `ℝ` are unique.
    have hHas : HasRealSaddleDirectionalDerivativeAt K u v u' 0 (-r) := hTendstoReal
    have hUnique :
        ∀ {L1 L2 : ℝ},
          HasRealSaddleDirectionalDerivativeAt K u v u' 0 L1 →
          HasRealSaddleDirectionalDerivativeAt K u v u' 0 L2 → L1 = L2 := by
      intro L1 L2 h1 h2
      exact tendsto_nhds_unique h1 h2
    have hSetEq :
        {L : ℝ | HasRealSaddleDirectionalDerivativeAt K u v u' 0 L} = ({-r} : Set ℝ) := by
      ext L
      constructor
      · intro hL
        have : L = -r := hUnique hL hHas
        simpa [this]
      · intro hL
        have : L = -r := by simpa using hL
        simpa [this] using hHas
    have hValue : realFirstVariableDirectionalDerivativeValue K u v u' = -r := by
      simp [realFirstVariableDirectionalDerivativeValue, hSetEq]
    -- Translate back to the `EReal` upper derivative.
    calc
      ((realFirstVariableDirectionalDerivativeValue K u v u' : ℝ) : EReal) =
          ((-r : ℝ) : EReal) := by simpa [hValue]
      _ = -((r : ℝ) : EReal) := by simp
      _ = -upperDirectionalDerivativeAt f u u' := by simpa [hrcoe]

  -- Step 2 (second variable): the same argument without a sign flip on the convex slice `y ↦ K u y`.
  have hg_convOn : ConvexOn ℝ D (fun y => (K u y : ℝ)) := hK.2 u hu
  have hgExt :=
    helperForTheorem_35_7_convexFunction_ite_top_extension_of_convexOn
      (s := D) (f := fun y => (K u y : ℝ)) hg_convOn
  have hg_conv : ConvexFunction g := by
    simpa [g] using hgExt.1
  have hg_finite : ∀ y ∈ D, g y ≠ (⊤ : EReal) ∧ g y ≠ (⊥ : EReal) := by
    simpa [g] using hgExt.2
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := hg_finite v hv
  have hDg_finite_all :
      (∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt g v y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt g v y ≠ (⊥ : EReal)) := by
    let gSeq : ℕ → (Fin n → ℝ) → EReal := fun _ => g
    let vSeq0 : ℕ → Fin n → ℝ := fun _ => v
    have hgSeq : ∀ i : ℕ, ConvexFunction (gSeq i) := by
      intro i
      simpa [gSeq] using hg_conv
    have hgSeq_finite :
        ∀ i : ℕ, ∀ y ∈ D, gSeq i y ≠ (⊤ : EReal) ∧ gSeq i y ≠ (⊥ : EReal) := by
      intro i y hy
      simpa [gSeq] using hg_finite y hy
    have hfinite :=
      helperForTheorem_5_24_8_directionalDerivative_finite_at_limit_and_sequence
        (n := n) (C := D) hD_open hD_conv hg_conv hg_finite gSeq hgSeq hgSeq_finite hv vSeq0
        (fun _ => hv)
    exact hfinite.1
  have hbridgeSecond :
      ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) =
        upperDirectionalDerivativeAt g v v' := by
    rcases convex_directionalDerivative_monotone_exists_and_sublinear g hg_conv v hgv with
      ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
    have hTendstoE :
        Filter.Tendsto (directionalDifferenceQuotientAt g v v') (𝓝[>] (0 : ℝ))
          (nhds (upperDirectionalDerivativeAt g v v')) := (hdir v').2.1
    have hcontWithin :
        ContinuousWithinAt (fun t : ℝ => v + t • v') (Set.Ioi (0 : ℝ)) (0 : ℝ) :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
    have htend :
        Filter.Tendsto (fun t : ℝ => v + t • v') (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds v) := by
      have hMaps : Set.MapsTo (fun t : ℝ => v + t • v') (Set.Ioi (0 : ℝ)) (Set.univ : Set (Fin n → ℝ)) := by
        intro t ht
        trivial
      simpa using (hcontWithin.tendsto_nhdsWithin hMaps)
    have hmemD : ∀ᶠ t in (𝓝[>] (0 : ℝ)), v + t • v' ∈ D :=
      htend.eventually (hD_open.mem_nhds hv)
    have htpos : ∀ᶠ t in (𝓝[>] (0 : ℝ)), t ∈ Set.Ioi (0 : ℝ) := by
      simpa [Filter.Eventually] using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
    have hquot_event :
        directionalDifferenceQuotientAt g v v' =ᶠ[(𝓝[>] (0 : ℝ))]
          (fun t : ℝ => ((realSaddleDirectionalDifferenceQuotientAt K u v 0 v' t : ℝ) : EReal)) := by
      filter_upwards [hmemD, htpos] with t htD htpos
      have htne : (t : ℝ) ≠ 0 := ne_of_gt (Set.mem_Ioi.mp htpos)
      have hstep :
          directionalDifferenceQuotientAt g v v' t =
            ((((K u (v + t • v') : ℝ) - (K u v : ℝ)) / t : ℝ) : EReal) := by
        simp [directionalDifferenceQuotientAt, g, htD, hv]
        rw [← EReal.coe_sub (K u (v + t • v') : ℝ) (K u v : ℝ)]
        rw [← EReal.coe_div ((K u (v + t • v') : ℝ) - (K u v : ℝ)) t]
      rw [hstep]
      apply (EReal.coe_eq_coe_iff).2
      -- Unfold the saddle quotient at direction `(0, v')` and simplify.
      simp [realSaddleDirectionalDifferenceQuotientAt, htne, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm]
    have hDfinite : upperDirectionalDerivativeAt g v v' ≠ (⊤ : EReal) ∧
        upperDirectionalDerivativeAt g v v' ≠ (⊥ : EReal) := hDg_finite_all v'
    let r : ℝ := (upperDirectionalDerivativeAt g v v').toReal
    have hrcoe : ((r : ℝ) : EReal) = upperDirectionalDerivativeAt g v v' := by
      simpa [r] using EReal.coe_toReal hDfinite.1 hDfinite.2
    have hTendstoE' :
        Filter.Tendsto
          (fun t : ℝ => ((realSaddleDirectionalDifferenceQuotientAt K u v 0 v' t : ℝ) : EReal))
          (𝓝[>] (0 : ℝ)) (nhds ((r : ℝ) : EReal)) := by
      have hTendstoE'' : Filter.Tendsto (directionalDifferenceQuotientAt g v v') (𝓝[>] (0 : ℝ))
          (nhds ((r : ℝ) : EReal)) := by
        simpa [hrcoe] using hTendstoE
      exact Filter.Tendsto.congr' hquot_event hTendstoE''
    have hTendstoReal :
        Filter.Tendsto (realSaddleDirectionalDifferenceQuotientAt K u v 0 v')
          (𝓝[>] (0 : ℝ)) (nhds r) :=
      (EReal.tendsto_coe).1 hTendstoE'
    have hHas : HasRealSaddleDirectionalDerivativeAt K u v 0 v' r := hTendstoReal
    have hUnique :
        ∀ {L1 L2 : ℝ},
          HasRealSaddleDirectionalDerivativeAt K u v 0 v' L1 →
          HasRealSaddleDirectionalDerivativeAt K u v 0 v' L2 → L1 = L2 := by
      intro L1 L2 h1 h2
      exact tendsto_nhds_unique h1 h2
    have hSetEq :
        {L : ℝ | HasRealSaddleDirectionalDerivativeAt K u v 0 v' L} = ({r} : Set ℝ) := by
      ext L
      constructor
      · intro hL
        have : L = r := hUnique hL hHas
        simpa [this]
      · intro hL
        have : L = r := by simpa using hL
        simpa [this] using hHas
    have hValue : realSecondVariableDirectionalDerivativeValue K u v v' = r := by
      simp [realSecondVariableDirectionalDerivativeValue, hSetEq]
    calc
      ((realSecondVariableDirectionalDerivativeValue K u v v' : ℝ) : EReal) =
          ((r : ℝ) : EReal) := by simpa [hValue]
      _ = upperDirectionalDerivativeAt g v v' := by simpa [hrcoe]

  exact ⟨hbridgeFirst, hbridgeSecond⟩


end Section35
end Chap07
