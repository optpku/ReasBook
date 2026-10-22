/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part8

open scoped Pointwise

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Helper for Theorem 6.29.4: if `F` is proper, then the domain of the Section 29 graph closure
projects into the closure of `dom F`. -/
lemma helperForTheorem_6_29_4_projection_domain_upper_bound_for_graphClosure
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1) :
    bifunctionEffectiveDomain
        (helperForTheorem_6_29_4_define_section29_bifunctionClosure F) ⊆
      closure (bifunctionEffectiveDomain F.1) := by
  let g : (Fin (m + n) → ℝ) → EReal :=
    helperForTheorem_6_29_4_coordinateGraphFunction F
  let domg : Set (Fin (m + n) → ℝ) := effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g
  let domcl : Set (Fin (m + n) → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (convexFunctionClosure g)
  let A : (Fin (m + n) → ℝ) → (Fin m → ℝ) := fun z i => z (Fin.castAdd n i)
  have hgproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g :=
    helperForTheorem_6_29_4_coordinateGraphFunction_proper F hproper
  have hclosure :
      ∀ z : Fin (m + n) → ℝ, z ∈ domcl → z ∈ closure domg := by
    intro z hz
    let e := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))
    have hzE :
        e.symm z ∈
          (fun x : EuclideanSpace Real (Fin (m + n)) => (x : Fin (m + n) → ℝ)) ⁻¹' domcl := by
      simpa [e] using hz
    have hzEclosure :
        e.symm z ∈
          closure
            ((fun x : EuclideanSpace Real (Fin (m + n)) => (x : Fin (m + n) → ℝ)) ⁻¹' domg) :=
      domcl_subset_closure_domf (f := g) hgproper hzE
    have hpre :
        ((fun x : EuclideanSpace Real (Fin (m + n)) => (x : Fin (m + n) → ℝ)) ⁻¹' domg) =
          e.symm '' domg := by
      simpa [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
        (ContinuousLinearEquiv.image_eq_preimage_symm (e := e.symm) (s := domg)).symm
    have hzImageClosure : e.symm z ∈ closure (e.symm '' domg) := by
      simpa [hpre] using hzEclosure
    have himageClosure :
        e '' closure (e.symm '' domg) ⊆ closure (e '' (e.symm '' domg)) :=
      image_closure_subset_closure_image (h := e.continuous)
    have hzClosureImage : z ∈ closure (e '' (e.symm '' domg)) := by
      refine himageClosure ?_
      exact ⟨e.symm z, hzImageClosure, by simp [e]⟩
    simpa using hzClosureImage
  intro u hu
  rcases
      (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
        (F := helperForTheorem_6_29_4_define_section29_bifunctionClosure F) (u := u)).1 hu with
    ⟨x, hx⟩
  have hz_domcl : Fin.append u x ∈ domcl := by
    -- The finite section witness exactly says the packed point belongs to `dom (cl g)`.
    change Fin.append u x ∈
      effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (convexFunctionClosure g)
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    simpa [g, helperForTheorem_6_29_4_define_section29_bifunctionClosure] using hx
  have hz_closure_domg : Fin.append u x ∈ closure domg := by
    exact hclosure (Fin.append u x) hz_domcl
  have hAclosure :
      A '' closure domg ⊆ closure (A '' domg) :=
    image_closure_subset_closure_image (h := by
      -- The first-coordinate projection is continuous.
      fun_prop)
  have hu_image_closure : u ∈ A '' closure domg := by
    refine ⟨Fin.append u x, hz_closure_domg, ?_⟩
    ext i
    simp [A]
  have hu_closure : u ∈ closure (A '' domg) := hAclosure hu_image_closure
  -- Replace the projected graph domain by `dom F` using the earlier projection description.
  rw [helperForTheorem_6_29_4_projection_coordinateGraphEffectiveDomain F] at hu_closure
  exact hu_closure

/-- Helper for Theorem 6.29.4: a relative-interior point of `dom F` should lift to a relative-
interior point of the packed graph domain lying above the same perturbation vector. -/
lemma helperForTheorem_6_29_4_coordinateGraph_riLift_of_mem_riProjection
    {m n : ℕ} (F : ConvexBifunction m n) {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1)) :
    ∃ x0 : Fin n → ℝ,
      Fin.append u x0 ∈
        euclideanRelativeInterior_fin (m + n)
          (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
            (helperForTheorem_6_29_4_coordinateGraphFunction F)) := by
  classical
  let domg : Set (Fin (m + n) → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
      (helperForTheorem_6_29_4_coordinateGraphFunction F)
  let eM : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
  let eN : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  let eMN : EuclideanSpace Real (Fin (m + n)) ≃L[Real] (Fin (m + n) → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))
  let C : Set (EuclideanSpace Real (Fin (m + n))) := eMN.symm '' domg
  let D : Set (EuclideanSpace Real (Fin m)) :=
    {y | Set.Nonempty {z : EuclideanSpace Real (Fin n) |
      eMN.symm (Fin.append (eM y) (eN z)) ∈ C}}
  have hdomgConv : Convex ℝ domg := by
    -- The packed graph function is convex, so its effective domain is convex.
    exact effectiveDomain_convex
      (S := (Set.univ : Set (Fin (m + n) → ℝ)))
      (f := helperForTheorem_6_29_4_coordinateGraphFunction F)
      (by simpa [ConvexFunction] using helperForTheorem_6_29_4_coordinateGraphFunction_convex F)
  have hCconv : Convex ℝ C := by
    -- Transport convexity from `dom g` to its Euclidean-coordinate image.
    simpa [C] using hdomgConv.linear_image eMN.symm.toLinearMap
  have hD_eq : D = eM.symm '' bifunctionEffectiveDomain F.1 := by
    -- The base projection of the packed graph domain is exactly `dom F`.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz⟩
      refine ⟨eM y, ?_, by simp [eM]⟩
      rw [← helperForTheorem_6_29_4_projection_coordinateGraphEffectiveDomain (F := F)]
      refine ⟨Fin.append (eM y) (eN z), ?_, by
        ext i
        simp⟩
      simpa [C] using hz
    · rintro ⟨u', hu', rfl⟩
      rcases
          (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
            (F := F.1) (u := u')).1 hu' with
        ⟨x, hx⟩
      refine ⟨eN.symm x, ?_⟩
      change eMN.symm (Fin.append u' x) ∈ C
      exact ⟨Fin.append u' x, by
        change
          Fin.append u' x ∈
            effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
              (helperForTheorem_6_29_4_coordinateGraphFunction F)
        rw [effectiveDomain_eq]
        refine ⟨by simp, ?_⟩
        simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx, rfl⟩
  have hu' : eM.symm u ∈ euclideanRelativeInterior m (eM.symm '' bifunctionEffectiveDomain F.1) := by
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := bifunctionEffectiveDomain F.1) (x := u)).1 hu
  have huE : eM.symm u ∈ euclideanRelativeInterior m D := by
    -- Rewrite the projected relative-interior hypothesis into Euclidean coordinates.
    simpa [hD_eq] using hu'
  have huDom : u ∈ bifunctionEffectiveDomain F.1 := by
    -- Relative-interior membership gives ordinary domain membership.
    have huDomE : eM.symm u ∈ eM.symm '' bifunctionEffectiveDomain F.1 :=
      (euclideanRelativeInterior_subset_closure m
        (eM.symm '' bifunctionEffectiveDomain F.1)).1 hu'
    rcases huDomE with ⟨u', hu', huEq⟩
    have hEq : u' = u := by
      simpa [eM] using huEq
    simpa [hEq] using hu'
  have hfiber_nonempty :
      ({z : EuclideanSpace Real (Fin n) |
        eMN.symm (Fin.append u (eN z)) ∈ C}).Nonempty := by
    -- Choose any finite value in the `u`-section to witness the fiber is nonempty.
    rcases
        (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
          (F := F.1) (u := u)).1 huDom with
      ⟨x, hx⟩
    refine ⟨eN.symm x, ?_⟩
    exact ⟨Fin.append u x, by
      change
        Fin.append u x ∈
          effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
            (helperForTheorem_6_29_4_coordinateGraphFunction F)
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx, rfl⟩
  have hfiber_conv : Convex ℝ {z : EuclideanSpace Real (Fin n) |
        eMN.symm (Fin.append u (eN z)) ∈ C} := by
    have hfiber_eq :
        {z : EuclideanSpace Real (Fin n) | eMN.symm (Fin.append u (eN z)) ∈ C} =
          eN.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F.1 u) := by
      ext z
      constructor
      · intro hz
        refine ⟨eN z, ?_, by simp [eN]⟩
        rcases hz with ⟨w, hw, hwEq⟩
        have hEq : w = Fin.append u (eN z) := by
          apply eMN.symm.injective
          simpa using hwEq
        subst hEq
        rw [effectiveDomain_eq]
        refine ⟨by simp, ?_⟩
        have hw_ne_top :
            helperForTheorem_6_29_4_coordinateGraphFunction F (Fin.append u (eN z)) ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin (m + n) → ℝ)))
            (f := helperForTheorem_6_29_4_coordinateGraphFunction F) hw
        exact lt_top_iff_ne_top.mpr (by
          simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hw_ne_top)
      · rintro ⟨x, hx, rfl⟩
        rw [effectiveDomain_eq] at hx
        refine ⟨Fin.append u x, ?_, ?_⟩
        · change
            Fin.append u x ∈
              effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
                (helperForTheorem_6_29_4_coordinateGraphFunction F)
          rw [effectiveDomain_eq]
          refine ⟨by simp, ?_⟩
          simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx.2
        · simp
    -- Identify the fiber with the section effective domain and transport convexity across `eN`.
    rw [hfiber_eq]
    simpa using
      (effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ))) (f := F.1 u)
        (by
          intro p hp q hq a b ha hb hab
          have hgraph := proposition_29_1 (F := F.1) F.2 u p.1 q.1 a b ha hb hab
          have hp' : F.1 u p.1 ≤ (p.2 : EReal) := by
            simpa [epigraph] using hp.2
          have hq' : F.1 u q.1 ≤ (q.2 : EReal) := by
            simpa [epigraph] using hq.2
          have hmulp :
              ((a : ℝ) : EReal) * F.1 u p.1 ≤ ((a : ℝ) : EReal) * (p.2 : EReal) := by
            exact mul_le_mul_of_nonneg_left hp' (by exact_mod_cast ha)
          have hmulq :
              ((b : ℝ) : EReal) * F.1 u q.1 ≤ ((b : ℝ) : EReal) * (q.2 : EReal) := by
            exact mul_le_mul_of_nonneg_left hq' (by exact_mod_cast hb)
          refine ⟨by trivial, ?_⟩
          exact le_trans hgraph (add_le_add hmulp hmulq))).linear_image eN.symm.toLinearMap
  rcases
      euclideanRelativeInterior_nonempty_of_convex_of_nonempty hfiber_conv hfiber_nonempty with
    ⟨xE, hxEri⟩
  have hsection :=
    (euclideanRelativeInterior_mem_iff_relativeInterior_section
      (m := m) (p := n) (C := C) hCconv (eM.symm u) xE)
  have hxPacked :
      eMN.symm (Fin.append u (eN xE)) ∈ euclideanRelativeInterior (m + n) C := by
    -- Combine the base `ri(dom F)` point with a fiber `ri` point using the section theorem.
    exact (hsection).2 ⟨huE, hxEri⟩
  refine ⟨eN xE, ?_⟩
  -- Return from Euclidean coordinates to the original `Fin` coordinates.
  refine (mem_euclideanRelativeInterior_fin_iff
    (n := m + n) (C := domg) (x := Fin.append u (eN xE))).2 ?_
  simpa [C, eM, eN, eMN] using hxPacked

/-- Helper for Theorem 6.29.4: properness of the packed graph function implies properness of the
original bifunction because packing and unpacking preserve both finiteness and the `≠ ⊥`
branch. -/
lemma helperForTheorem_6_29_4_properBifunction_of_coordinateGraphFunction_proper
    {m n : ℕ} (F : ConvexBifunction m n)
    (hgproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (helperForTheorem_6_29_4_coordinateGraphFunction F)) :
    IsProperBifunction F.1 := by
  rw [properConvexFunctionOn_iff_effectiveDomain_nonempty_finite] at hgproper
  rcases hgproper with ⟨_hgconv, hdomne, hfinite⟩
  refine ⟨?_, ?_⟩
  · intro p
    -- Properness on `univ` gives `≠ ⊥` on-domain, and outside the effective domain this is
    -- automatic by definition.
    by_cases hzDom :
        Fin.append p.1 p.2 ∈
          effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
            (helperForTheorem_6_29_4_coordinateGraphFunction F)
    · exact by
        have hneBot' := (hfinite (Fin.append p.1 p.2) hzDom).1
        simpa [graphFunction, helperForTheorem_6_29_4_coordinateGraphFunction] using hneBot'
    · have hneBot' :=
          not_mem_effectiveDomain_imp_ne_bot
            (S := (Set.univ : Set (Fin (m + n) → ℝ)))
            (f := helperForTheorem_6_29_4_coordinateGraphFunction F)
            (x := Fin.append p.1 p.2) (by simp) hzDom
      simpa [graphFunction, helperForTheorem_6_29_4_coordinateGraphFunction] using hneBot'
  · rcases hdomne with ⟨z, hz⟩
    have hzFinite :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin (m + n) → ℝ)))
        (f := helperForTheorem_6_29_4_coordinateGraphFunction F) hz
    refine ⟨((fun i => z (Fin.castAdd n i)), fun j => z (Fin.natAdd m j)), ?_⟩
    -- Unpacking a finite packed graph point gives the required finite bifunction value.
    simpa [graphFunction, helperForTheorem_6_29_4_coordinateGraphFunction] using hzFinite

/-- Helper for Theorem 6.29.4: the packed relative-interior witness above `u` should translate
to the exact `ri` input needed for closure under linear precomposition by `x ↦ Fin.append 0 x`.
-/
lemma helperForTheorem_6_29_4_affineSlice_riWitness_of_mem_ri_domain
    {m n : ℕ} (F : ConvexBifunction m n) {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1)) :
    ∃ x0 : Fin n → ℝ,
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm (Fin.append (0 : Fin m → ℝ) x0) ∈
        euclideanRelativeInterior (m + n)
          (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm
            (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
              (fun z => helperForTheorem_6_29_4_coordinateGraphFunction F
                (z + Fin.append u 0)))) := by
  classical
  let g : (Fin (m + n) → ℝ) → EReal := helperForTheorem_6_29_4_coordinateGraphFunction F
  let domg : Set (Fin (m + n) → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g
  let e : EuclideanSpace Real (Fin (m + n)) ≃L[Real] (Fin (m + n) → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))
  let a : Fin (m + n) → ℝ := Fin.append u 0
  let aE : EuclideanSpace Real (Fin (m + n)) := e.symm a
  let T : EuclideanSpace Real (Fin (m + n)) ≃ᵃ[Real] EuclideanSpace Real (Fin (m + n)) :=
    AffineEquiv.constVAdd ℝ (EuclideanSpace Real (Fin (m + n))) (-aE)
  rcases
      helperForTheorem_6_29_4_coordinateGraph_riLift_of_mem_riProjection
        (F := F) hu with
    ⟨x0, hx0ri⟩
  have hx0riE : e.symm (Fin.append u x0) ∈ euclideanRelativeInterior (m + n) (e.symm '' domg) := by
    -- Convert the packed relative-interior witness into Euclidean coordinates.
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := m + n) (C := domg) (x := Fin.append u x0)).1 hx0ri
  have hT_apply : ∀ z : EuclideanSpace Real (Fin (m + n)), T z = z - aE := by
    -- The chosen affine equivalence is translation by `-a`.
    intro z
    simp [T, sub_eq_add_neg, add_comm]
  have himage :
      e.symm '' effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (fun z => g (z + a)) =
        T '' (e.symm '' domg) := by
    -- Translating the argument by `a` translates the effective domain by `-a`.
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨e.symm (w + a), ?_, ?_⟩
      · exact ⟨w + a, by simpa [domg, effectiveDomain_eq] using hw, rfl⟩
      · apply e.injective
        simp [hT_apply, aE, e, sub_eq_add_neg]
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨w, hw, rfl⟩
      refine ⟨w - a, ?_, ?_⟩
      · simpa [domg, effectiveDomain_eq, sub_eq_add_neg]
          using hw
      · simp [hT_apply, aE, e, sub_eq_add_neg]
  have htranslated :
      e.symm (Fin.append (0 : Fin m → ℝ) x0) ∈
        euclideanRelativeInterior (m + n)
          (e.symm '' effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (fun z => g (z + a))) := by
    have hriImage :
        euclideanRelativeInterior (m + n) (T '' (e.symm '' domg)) =
          T '' euclideanRelativeInterior (m + n) (e.symm '' domg) :=
      euclideanRelativeInterior_image_affineEquiv (n := m + n) (C := e.symm '' domg) (e := T)
    have hmemImage :
        T (e.symm (Fin.append u x0)) ∈
          euclideanRelativeInterior (m + n) (T '' (e.symm '' domg)) := by
      -- Translate the known `ri(dom g)` point by `-a`.
      rw [hriImage]
      exact ⟨e.symm (Fin.append u x0), hx0riE, rfl⟩
    have hmemImage' :
        T (e.symm (Fin.append u x0)) ∈
          euclideanRelativeInterior (m + n)
            (e.symm '' effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) (fun z => g (z + a))) := by
      simpa [himage] using hmemImage
    have happend_sub :
        Fin.append u x0 - a = Fin.append (0 : Fin m → ℝ) x0 := by
      ext i
      cases Nat.lt_or_ge i.1 m with
      | inl hi =>
          simp [a, Fin.append, Fin.addCases, hi, Pi.sub_apply]
      | inr hi =>
          let j : Fin n := ⟨i.1 - m, by omega⟩
          have hj' : Fin.natAdd m j = i := by
            ext
            simp [j]
            omega
          have hj : i = Fin.natAdd m j := hj'.symm
          rw [hj]
          simp [a, Fin.append, Pi.sub_apply]
    have hshift :
        T (e.symm (Fin.append u x0)) =
          e.symm (Fin.append (0 : Fin m → ℝ) x0) := by
      apply e.injective
      simpa [hT_apply, aE, e, sub_eq_add_neg, happend_sub]
    simpa [hshift] using hmemImage'
  refine ⟨x0, ?_⟩
  -- The translated packed point is exactly the precomposition witness required later.
  simpa [g, e] using htranslated

/-- Helper for Theorem 6.29.4: once the translated affine-slice witness is available, closure
commutes with slicing the packed graph function along the fiber over `u`. -/
lemma helperForTheorem_6_29_4_affineSlice_convexFunctionClosure_eq
    {m n : ℕ} (F : ConvexBifunction m n) {u : Fin m → ℝ}
    (hproper : IsProperBifunction F.1)
    (hu : u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1)) :
    convexFunctionClosure (fun x : Fin n → ℝ =>
        helperForTheorem_6_29_4_coordinateGraphFunction F (Fin.append u x)) =
      fun x => convexFunctionClosure
        (helperForTheorem_6_29_4_coordinateGraphFunction F) (Fin.append u x) := by
  let g : (Fin (m + n) → ℝ) → EReal :=
    helperForTheorem_6_29_4_coordinateGraphFunction F
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun x => Fin.append (0 : Fin m → ℝ) x
      map_add' := by
        intro x y
        ext i
        cases Nat.lt_or_ge i.1 m with
        | inl hi =>
            simp [Fin.append, Fin.addCases, hi, Pi.add_apply]
        | inr hi =>
            let j : Fin n := ⟨i.1 - m, by omega⟩
            have hj' : Fin.natAdd m j = i := by
              ext
              simp [j]
              omega
            have hj : i = Fin.natAdd m j := hj'.symm
            rw [hj]
            simp [Pi.add_apply]
      map_smul' := by
        intro a x
        ext i
        cases Nat.lt_or_ge i.1 m with
        | inl hi =>
            simp [Fin.append, Fin.addCases, hi, Pi.smul_apply]
        | inr hi =>
            let j : Fin n := ⟨i.1 - m, by omega⟩
            have hj' : Fin.natAdd m j = i := by
              ext
              simp [j]
              omega
            have hj : i = Fin.natAdd m j := hj'.symm
            rw [hj]
            simp [Pi.smul_apply] }
  have hgproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g :=
    helperForTheorem_6_29_4_coordinateGraphFunction_proper F hproper
  rcases
      helperForTheorem_6_29_4_affineSlice_riWitness_of_mem_ri_domain
        (F := F) hu with
    ⟨x0, hx0ri⟩
  have hprecomp :
      convexFunctionClosure (fun x : Fin n → ℝ =>
          (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) (A x)) =
        fun x =>
          convexFunctionClosure (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) (A x) := by
    -- Apply the Chapter 2 precomposition theorem at the translated packed graph function.
    exact
      convexFunctionClosure_precomp_linearMap_eq
        (g := fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0))
        (hgproper :=
          helperForTheorem_6_29_4_translate_properConvexFunctionOn
            hgproper (Fin.append u 0))
        (A := A) ⟨x0, hx0ri⟩
  have htranslate :
      convexFunctionClosure (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) =
        fun z => convexFunctionClosure g (z + Fin.append u 0) :=
    helperForTheorem_6_29_4_translate_convexFunctionClosure_eq
      hgproper (Fin.append u 0)
  have hslice_eq :
      (fun x' : Fin n → ℝ => g (Fin.append u x')) =
        fun x' : Fin n → ℝ => (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) (A x') := by
    funext x'
    have hxEq :
        A x' + Fin.append u 0 = Fin.append u x' := by
      ext i
      cases Nat.lt_or_ge i.1 m with
      | inl hi =>
          simp [A, Fin.append, Fin.addCases, hi, Pi.add_apply]
      | inr hi =>
          let j : Fin n := ⟨i.1 - m, by omega⟩
          have hj' : Fin.natAdd m j = i := by
            ext
            simp [j]
            omega
          have hj : i = Fin.natAdd m j := hj'.symm
          rw [hj]
          rw [Pi.add_apply]
          rw [show A x' = Fin.append (0 : Fin m → ℝ) x' by rfl]
          simp [Fin.append]
    simp [hxEq]
  have hprecomp' :
      convexFunctionClosure (fun x : Fin n → ℝ => g (Fin.append u x)) =
        fun x => convexFunctionClosure (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) (A x) := by
    simpa [hslice_eq] using hprecomp
  -- Both sides are the same function after expanding the affine slice `x ↦ Fin.append u x`.
  funext x
  have hxEq :
      A x + Fin.append u 0 = Fin.append u x := by
    ext i
    cases Nat.lt_or_ge i.1 m with
    | inl hi =>
        simp [A, Fin.append, Fin.addCases, hi, Pi.add_apply]
    | inr hi =>
        let j : Fin n := ⟨i.1 - m, by omega⟩
        have hj' : Fin.natAdd m j = i := by
          ext
          simp [j]
          omega
        have hj : i = Fin.natAdd m j := hj'.symm
        rw [hj]
        rw [Pi.add_apply]
        rw [show A x = Fin.append (0 : Fin m → ℝ) x by rfl]
        simp [Fin.append]
  calc
    convexFunctionClosure (fun x' : Fin n → ℝ => g (Fin.append u x')) x
        = convexFunctionClosure (fun z : Fin (m + n) → ℝ => g (z + Fin.append u 0)) (A x) :=
          congrFun hprecomp' x
    _ = (fun z => convexFunctionClosure g (z + Fin.append u 0)) (A x) := by
          simp [htranslate]
    _ = convexFunctionClosure g (Fin.append u x) := by
          simp [hxEq]

/-- Helper for Theorem 6.29.4: if one point in the `u`-section has value `⊥`, then both the
section closure and the closure of the section collapse to the constant `⊥` function. -/
lemma helperForTheorem_6_29_4_section_eq_of_exists_botValue
    {m n : ℕ} (F : ConvexBifunction m n) (u : Fin m → ℝ)
    (hbot : ∃ x0 : Fin n → ℝ, F.1 u x0 = (⊥ : EReal)) :
    helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
      convexFunctionClosure (F.1 u) := by
  rcases hbot with ⟨x0, hx0bot⟩
  have hgraphClosure :
      convexFunctionClosure (helperForTheorem_6_29_4_coordinateGraphFunction F) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := helperForTheorem_6_29_4_coordinateGraphFunction F)
      ⟨Fin.append u x0, by
        simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx0bot⟩
  have hsectionClosure :
      convexFunctionClosure (F.1 u) = fun _ : Fin n → ℝ => (⊥ : EReal) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := F.1 u) ⟨x0, hx0bot⟩
  -- Evaluate both collapsed closures pointwise.
  funext x
  simp [helperForTheorem_6_29_4_define_section29_bifunctionClosure, hgraphClosure, hsectionClosure]

/-- Helper for Theorem 6.29.4: if the bifunction is not proper, then every `u ∈ ri (dom F)`
should admit a section point where the value is already `⊥`. -/
lemma helperForTheorem_6_29_4_section_botWitness_of_nonproper_on_riProjection
    {m n : ℕ} (F : ConvexBifunction m n) {u : Fin m → ℝ}
    (hnotproper : ¬ IsProperBifunction F.1)
    (hu : u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1)) :
    ∃ x0 : Fin n → ℝ, F.1 u x0 = (⊥ : EReal) := by
  let g : (Fin (m + n) → ℝ) → EReal := helperForTheorem_6_29_4_coordinateGraphFunction F
  have hgconv :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    simpa [ConvexFunction] using helperForTheorem_6_29_4_coordinateGraphFunction_convex F
  have hgimproper : ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    refine ⟨hgconv, ?_⟩
    intro hgproper
    exact hnotproper
      (helperForTheorem_6_29_4_properBifunction_of_coordinateGraphFunction_proper
        (F := F) hgproper)
  rcases
      helperForTheorem_6_29_4_coordinateGraph_riLift_of_mem_riProjection
        (F := F) hu with
    ⟨x0, hx0ri⟩
  have hpreim :
      ((fun z : EuclideanSpace Real (Fin (m + n)) => (z : Fin (m + n) → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g) =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm ''
          effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
      (ContinuousLinearEquiv.image_eq_preimage_symm
        (e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm)
        (s := effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g)).symm
  have hx0riE :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm (Fin.append u x0) ∈
        euclideanRelativeInterior (m + n)
          ((fun z : EuclideanSpace Real (Fin (m + n)) => (z : Fin (m + n) → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g) :=
    by
      have hx0riE' :=
        (mem_euclideanRelativeInterior_fin_iff
      (n := m + n)
      (C := effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) g)
      (x := Fin.append u x0)).1 hx0ri
      simpa [hpreim] using hx0riE'
  have hbotPacked :
      g (Fin.append u x0) = (⊥ : EReal) := by
    -- Improper convex functions are `⊥` throughout the relative interior of their effective
    -- domain.
    simpa using
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
        (f := g) hgimproper
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m + n))).symm (Fin.append u x0))
        hx0riE
  exact ⟨x0, by simpa [g, helperForTheorem_6_29_4_coordinateGraphFunction] using hbotPacked⟩

/-- Helper for Theorem 6.29.4: on `ri (dom F)`, the section closure identity and the
perturbation identity follow from the proper/nonproper split. -/
lemma helperForTheorem_6_29_4_section_and_perturbation_eq_on_riProjection
    {m n : ℕ} (F : ConvexBifunction m n) :
    (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
        helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
          convexFunctionClosure (F.1 u)) ∧
      (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
        helperForTheorem_6_29_4_closurePerturbationFunction F u =
          generalizedConvexProgramPerturbationFunction F u) := by
  have hSectionEq :
      ∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
        helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
          convexFunctionClosure (F.1 u) := by
    intro u hu
    by_cases hproper : IsProperBifunction F.1
    · -- In the proper branch, closure commutes with the affine slice of the packed graph.
      funext x
      have hslice :=
        congrFun
          (helperForTheorem_6_29_4_affineSlice_convexFunctionClosure_eq
            (F := F) hproper hu) x
      simpa [helperForTheorem_6_29_4_define_section29_bifunctionClosure,
        helperForTheorem_6_29_4_coordinateGraphFunction] using hslice.symm
    · -- In the improper branch, a single `⊥` section value collapses both closures.
      exact
        helperForTheorem_6_29_4_section_eq_of_exists_botValue F u
          (helperForTheorem_6_29_4_section_botWitness_of_nonproper_on_riProjection
            (F := F) hproper hu)
  constructor
  · exact hSectionEq
  · intro u hu
    have hsection :
        helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
          convexFunctionClosure (F.1 u) :=
      hSectionEq u hu
    -- Rewrite both perturbation infima using the already-established section equality.
    calc
      helperForTheorem_6_29_4_closurePerturbationFunction F u
          = iInf (fun x : Fin n → ℝ =>
              helperForTheorem_6_29_4_define_section29_bifunctionClosure F u x) := by
              rw [helperForTheorem_6_29_4_closurePerturbationFunction, sInf_range]
      _ = iInf (fun x : Fin n → ℝ => convexFunctionClosure (F.1 u) x) := by
              simp [hsection]
      _ = iInf (fun x : Fin n → ℝ => F.1 u x) := by
              symm
              exact iInf_convexFunctionClosure_eq (f := F.1 u)
      _ = generalizedConvexProgramPerturbationFunction F u := by
              rw [generalizedConvexProgramPerturbationFunction, sInf_range]
              simp [generalizedConvexProgramPerturbation, generalizedConvexProgram]

/-- Theorem 6.29.4: the Section 29 closure of a convex bifunction should agree with the closure
of each section on `ri (dom F)`, preserve the perturbation infimum there, and for proper `F`
have domain between `dom F` and `closure (dom F)`. -/
theorem theorem_29_4_convex_bifunction_closure_section_and_domain
    {m n : ℕ} (F : ConvexBifunction m n) :
    (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
        helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
          convexFunctionClosure (F.1 u)) ∧
      (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
        helperForTheorem_6_29_4_closurePerturbationFunction F u =
          generalizedConvexProgramPerturbationFunction F u) ∧
      (IsProperBifunction F.1 →
        bifunctionEffectiveDomain F.1 ⊆
            bifunctionEffectiveDomain
              (helperForTheorem_6_29_4_define_section29_bifunctionClosure F) ∧
          bifunctionEffectiveDomain
              (helperForTheorem_6_29_4_define_section29_bifunctionClosure F) ⊆
            closure (bifunctionEffectiveDomain F.1)) := by
  have hSectionAndInf :
      (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
          helperForTheorem_6_29_4_define_section29_bifunctionClosure F u =
            convexFunctionClosure (F.1 u)) ∧
        (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
          helperForTheorem_6_29_4_closurePerturbationFunction F u =
            generalizedConvexProgramPerturbationFunction F u) :=
    helperForTheorem_6_29_4_section_and_perturbation_eq_on_riProjection F
  refine ⟨hSectionAndInf.1, hSectionAndInf.2, ?_⟩
  intro _hproper
  refine ⟨helperForTheorem_6_29_4_projection_domain_inclusion_left F, ?_⟩
  -- Project the closure-domain inclusion for the packed graph function back to perturbations.
  exact helperForTheorem_6_29_4_projection_domain_upper_bound_for_graphClosure F _hproper

/-- Helper for Corollary 6.29.4: the perturbation function of a generalized convex program. -/
noncomputable abbrev helperForCorollary_6_29_4_perturbationFunction {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin m → ℝ) → EReal :=
  generalizedConvexProgramPerturbationFunction F

/-- Helper for Corollary 6.29.4: strong or strict consistency puts the origin in the relative
interior of the perturbation effective domain. -/
lemma helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n)
    (hconsistent :
      generalizedConvexProgramStronglyConsistent F ∨
        generalizedConvexProgramStrictlyConsistent F) :
    (0 : Fin m → ℝ) ∈
      euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (helperForCorollary_6_29_4_perturbationFunction F)) := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 identifies the effective domain of the perturbation function with `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  rcases hconsistent with hstrong | hstrict
  · -- The strong-consistency branch is already the required relative-interior statement.
    simpa [p, hdom] using hstrong
  · have hri :
        (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hstrict
    -- The strict-consistency branch first drops from interior to relative interior.
    simpa [p, hdom] using hri

/-- Helper for Corollary 6.29.4: relative-interior consistency forces a subgradient of the
perturbation function at the origin. -/
lemma helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ))
            (helperForCorollary_6_29_4_perturbationFunction F))) :
    Set.Nonempty
      (subdifferentialAt (helperForCorollary_6_29_4_perturbationFunction F) 0) := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  by_contra hEmpty
  have h23 :=
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      p hpConv 0 hpFinite).2 hEmpty
  rcases convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite with
    ⟨_hdir, _hpos, _hconv, hzero, _hsymm⟩
  have hbot :
      upperDirectionalDerivativeAt p 0 0 = (⊥ : EReal) := by
    simpa using (h23.2 0 hri).1
  have hzeroBot : ((0 : ℝ) : EReal) = (⊥ : EReal) := by
    exact hzero.symm.trans hbot
  exact EReal.coe_ne_bot 0 hzeroBot

/-- Helper for Corollary 6.29.4: the Euclideanized perturbation subdifferential is exactly the
negated image of the Kuhn--Tucker set. -/
lemma helperForCorollary_6_29_4_subdifferentialPreimage_eq_negImage_kuhnTuckerSet
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    ((dotProductEquiv ℝ (Fin m)) ⁻¹'
        subdifferentialAt (helperForCorollary_6_29_4_perturbationFunction F) 0) =
      (fun uStar : Fin m → ℝ => -uStar) ''
        {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  ext v
  constructor
  · intro hv
    have hvEuclidean : v ∈ euclideanSubdifferentialAt p 0 := by
      simpa [p, euclideanSubdifferentialAt] using hv
    have hKT : IsKuhnTuckerVector F (-v) := by
      have hiff :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2
          hfinite (-v)
      have hnegv : -(-v) ∈ euclideanSubdifferentialAt p 0 := by
        simpa using hvEuclidean
      exact hiff.2 hnegv
    refine ⟨-v, hKT, ?_⟩
    simp
  · rintro ⟨uStar, huStar, hv⟩
    subst hv
    have hiff :=
      (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2
        hfinite uStar
    have huEuclidean : -uStar ∈ euclideanSubdifferentialAt p 0 := hiff.1 huStar
    simpa [p, euclideanSubdifferentialAt] using huEuclidean

/-- Helper for Corollary 6.29.4: negating every point of a set negates the support-function
argument. -/
lemma helperForCorollary_6_29_4_supportFunction_negImage_eq_supportFunction_neg
    {m : ℕ} (U : Set (Fin m → ℝ)) (u : Fin m → ℝ) :
    supportFunctionEReal ((fun uStar : Fin m → ℝ => -uStar) '' U) u =
      supportFunctionEReal U (-u) := by
  classical
  have hset :
      {z : EReal |
          ∃ v ∈ ((fun uStar : Fin m → ℝ => -uStar) '' U),
            z = ((dotProduct v u : ℝ) : EReal)} =
        {z : EReal |
          ∃ uStar ∈ U,
            z = ((dotProduct uStar (-u) : ℝ) : EReal)} := by
    ext z
    constructor
    · rintro ⟨v, hv, hz⟩
      rcases hv with ⟨uStar, huStar, hv⟩
      subst hv
      refine ⟨uStar, huStar, ?_⟩
      simpa [dotProduct_comm] using hz
    · rintro ⟨uStar, huStar, hz⟩
      refine ⟨-uStar, ?_, ?_⟩
      · exact ⟨uStar, huStar, rfl⟩
      · simpa [dotProduct_comm] using hz
  -- The two support functions are the same supremum written with opposite signs.
  rw [supportFunctionEReal, supportFunctionEReal]
  exact congrArg sSup hset

/-- Helper for Corollary 6.29.4: the origin directional derivative is the support function of the
Kuhn--Tucker set evaluated at the negated direction. -/
lemma helperForCorollary_6_29_4_directionalDerivative_eq_supportFunction_negKuhnTuckerSet
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ))
            (helperForCorollary_6_29_4_perturbationFunction F))) :
    ∀ u : Fin m → ℝ,
      generalizedConvexProgramOriginDirectionalDerivative F u =
        supportFunctionEReal {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} (-u) := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  let U : Set (Fin m → ℝ) := {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hsub :
      Set.Nonempty (subdifferentialAt p 0) :=
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin F hfinite hri
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      p hpConv 0 hpFinite).1 hsub
  have hDirEq :
      ∀ u : Fin m → ℝ,
        upperDirectionalDerivativeAt p 0 u = subdifferentialSupportAt p 0 u := by
    have h23_4 :=
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        p hproper 0).2.1) hri
    exact h23_4.2.2.2
  intro u
  -- Theorem 23.4 identifies the derivative with the support of the perturbation subdifferential.
  calc
    generalizedConvexProgramOriginDirectionalDerivative F u = upperDirectionalDerivativeAt p 0 u := by
      rfl
    _ = subdifferentialSupportAt p 0 u := hDirEq u
    _ =
        supportFunctionEReal
          (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt p 0)) u := by
          symm
          exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq p 0 u
    _ = supportFunctionEReal ((fun uStar : Fin m → ℝ => -uStar) '' U) u := by
          rw [helperForCorollary_6_29_4_subdifferentialPreimage_eq_negImage_kuhnTuckerSet
            F hfinite]
    _ = supportFunctionEReal U (-u) :=
          helperForCorollary_6_29_4_supportFunction_negImage_eq_supportFunction_neg U u

/-- Helper for Corollary 6.29.4: the support function at `-u` is the negative infimum of the
pairings with `u`. -/
lemma helperForCorollary_6_29_4_supportFunction_neg_eq_neg_sInf_pairings
    {m : ℕ} (U : Set (Fin m → ℝ)) (u : Fin m → ℝ) :
    supportFunctionEReal U (-u) =
      -sInf (((fun r : ℝ => (r : EReal)) ''
        Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u) U) : Set EReal) := by
  classical
  let S : Set EReal :=
    ((fun r : ℝ => (r : EReal)) '' Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u) U)
  have hset :
      {z : EReal | ∃ x ∈ U, z = ((dotProduct x (-u) : ℝ) : EReal)} =
        (fun z : EReal => -z) '' S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((dotProduct x u : ℝ) : EReal), ?_, ?_⟩
      · refine ⟨dotProduct x u, ?_, rfl⟩
        exact ⟨x, hx, rfl⟩
      · simp [dotProduct_comm]
    · rintro ⟨w, hwS, hz⟩
      rcases hwS with ⟨r, hrS, hrw⟩
      rcases hrS with ⟨x, hx, hrx⟩
      subst hrw
      subst hrx
      refine ⟨x, hx, ?_⟩
      simpa [dotProduct_comm] using hz.symm
  have hpre :
      OrderDual.toDual ⁻¹' (EReal.negOrderIso '' S) = (fun z : EReal => -z) '' S := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hwS, hwz⟩
      refine ⟨w, hwS, ?_⟩
      simpa [EReal.negOrderIso] using hwz
    · rintro ⟨w, hwS, hwz⟩
      refine ⟨w, hwS, ?_⟩
      simpa [EReal.negOrderIso] using hwz
  have hnegS :
      OrderDual.ofDual (sInf (EReal.negOrderIso '' S)) = -sInf S := by
    have hmapSInf :
        EReal.negOrderIso (sInf S) = sInf (EReal.negOrderIso '' S) := by
      calc
        EReal.negOrderIso (sInf S) = ⨅ a ∈ S, EReal.negOrderIso a :=
          EReal.negOrderIso.map_sInf S
        _ = sInf (EReal.negOrderIso '' S) := by
          rw [sInf_image]
    calc
      OrderDual.ofDual (sInf (EReal.negOrderIso '' S)) =
          OrderDual.ofDual (EReal.negOrderIso (sInf S)) := by
            rw [← hmapSInf]
      _ = -sInf S := by
          rfl
  -- Negating the pairing set turns the support supremum into an `EReal` infimum.
  calc
    supportFunctionEReal U (-u)
        = sSup {z : EReal | ∃ x ∈ U, z = ((dotProduct x (-u) : ℝ) : EReal)} := by
          rfl
    _ = sSup ((fun z : EReal => -z) '' S) := by rw [hset]
    _ = sSup (OrderDual.toDual ⁻¹' (EReal.negOrderIso '' S)) := by
          rw [← hpre]
    _ = OrderDual.ofDual (sInf (EReal.negOrderIso '' S)) := by
          exact (ofDual_sInf (s := EReal.negOrderIso '' S)).symm
    _ = -sInf S := hnegS
    _ = -sInf (((fun r : ℝ => (r : EReal)) ''
          Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u) U) : Set EReal) := by
          rfl

-- Proof sketch: convert consistency into `0 ∈ ri (dom p)` for the perturbation function `p`,
-- use the Chapter 23 relative-interior criterion to obtain a subgradient at the origin, identify
-- that subgradient fiber with the negated Kuhn--Tucker set, and finally rewrite the resulting
-- support value as a negative infimum of pairings.
/-- Corollary 6.29.4: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`. Suppose that the
optimal value in the associated generalized convex program `(P)` is finite and that `(P)` is
strongly consistent or strictly consistent. Then `(P)` has a Kuhn--Tucker vector, and

`(inf F)'(0; u) = -inf { ⟪uStar, u⟫ | uStar ∈ U* }`

for every direction `u`, where `U*` is the set of all Kuhn--Tucker vectors for `(P)`. -/
theorem generalizedConvexProgram_exists_kuhnTuckerVector_and_originDirectionalDerivative_eq_neg_sInf
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hconsistent :
      generalizedConvexProgramStronglyConsistent F ∨
        generalizedConvexProgramStrictlyConsistent F) :
    (∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ∧
      ∀ u : Fin m → ℝ,
        generalizedConvexProgramOriginDirectionalDerivative F u =
          -sInf
            (((fun r : ℝ => (r : EReal)) ''
              Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u)
                {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}) : Set EReal) := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  let U : Set (Fin m → ℝ) := {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}
  have hri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
    helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain F hconsistent
  have hsub :
      Set.Nonempty (subdifferentialAt p 0) :=
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin F hfinite hri
  have hUne : U.Nonempty := by
    rcases hsub with ⟨g, hg⟩
    have hgEuclidean : ((dotProductEquiv ℝ (Fin m)).symm g) ∈ euclideanSubdifferentialAt p 0 := by
      simpa [p, euclideanSubdifferentialAt] using hg
    let uStar : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm g)
    have huStar :
        IsKuhnTuckerVector F uStar := by
      have hiff :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2
          hfinite uStar
      have huEuclidean : -uStar ∈ euclideanSubdifferentialAt p 0 := by
        simpa [uStar] using hgEuclidean
      exact hiff.2 huEuclidean
    exact ⟨uStar, huStar⟩
  constructor
  · -- Transport the subgradient witness through Theorem 6.29.1 to obtain a Kuhn--Tucker vector.
    exact hUne
  · intro u
    -- First identify the derivative with the support of the Kuhn--Tucker set at `-u`.
    calc
      generalizedConvexProgramOriginDirectionalDerivative F u
          = supportFunctionEReal U (-u) :=
            helperForCorollary_6_29_4_directionalDerivative_eq_supportFunction_negKuhnTuckerSet
              F hfinite hri u
      _ = -sInf
            (((fun r : ℝ => (r : EReal)) ''
              Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u) U) : Set EReal) :=
            helperForCorollary_6_29_4_supportFunction_neg_eq_neg_sInf_pairings U u


end Section29
end Chap06
