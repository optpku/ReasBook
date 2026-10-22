/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part3

open scoped Topology

section Chap05
section Section23

/-- Helper for Theorem 23.4: the Euclidean-space coercion preimage of a set in `Fin n → ℝ`
matches the image under the inverse Euclidean equivalence. -/
lemma helperForTheorem_23_4_preimage_eq_symmImage {n : ℕ} (C : Set (Fin n → ℝ)) :
    ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹' C) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' C := by
  ext z
  constructor
  · intro hz
    exact ⟨(z : Fin n → ℝ), hz, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    simpa

/-- Helper for Theorem 23.4: off the effective domain, a proper convex function has no
subgradients. -/
lemma helperForTheorem_23_4_subdifferential_empty_of_not_mem_effectiveDomain
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ)
    (hx : x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :
    subdifferentialAt f x = ∅ := by
  classical
  rcases section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hproper with ⟨z0, hz0⟩
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro g hg
  have hz0_ne_top :
      f z0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hz0
  have hx_ne_top : f x ≠ (⊤ : EReal) := by
    intro hx_top
    have hineq : f z0 ≥ f x + ((g (z0 - x) : ℝ) : EReal) := hg z0
    have htop_le : (⊤ : EReal) ≤ f z0 := by
      have htop_rhs : f x + ((g (z0 - x) : ℝ) : EReal) = (⊤ : EReal) := by
        rw [hx_top]
        simpa using (EReal.top_add_coe (g (z0 - x)))
      exact htop_rhs ▸ hineq
    exact hz0_ne_top ((top_le_iff.mp htop_le))
  have hx_mem : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.mpr hx_ne_top)
  exact hx hx_mem

/-- Helper for Theorem 23.4: Corollary 6.4.1 transported from `EuclideanSpace ℝ (Fin n)` back to
`Fin n → ℝ`. -/
lemma helperForTheorem_23_4_mem_interior_iff_forall_exists_add_smul_mem
    {n : ℕ} (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (x : Fin n → ℝ) :
    x ∈ interior C ↔
      ∀ y : Fin n → ℝ, ∃ ε > (0 : ℝ), x + ε • y ∈ C := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hpreimage :
      e.toHomeomorph ⁻¹' C = e.symm '' C := by
    ext u
    constructor
    · intro hu
      exact ⟨e u, hu, by simp [e]⟩
    · rintro ⟨v, hv, rfl⟩
      simpa [e]
  have hxInterior :
      x ∈ interior C ↔ e.symm x ∈ interior (e.symm '' C) := by
    have hpre :
        e.toHomeomorph ⁻¹' interior C = interior (e.symm '' C) := by
      calc
        e.toHomeomorph ⁻¹' interior C = interior (e.toHomeomorph ⁻¹' C) :=
          e.toHomeomorph.preimage_interior (s := C)
        _ = interior (e.symm '' C) := by rw [hpreimage]
    constructor
    · intro hx_int
      have hx_pre : e.symm x ∈ e.toHomeomorph ⁻¹' interior C := by
        simpa [Set.mem_preimage, e] using hx_int
      rw [hpre] at hx_pre
      exact hx_pre
    · intro hx_int
      have hx_pre : e.symm x ∈ e.toHomeomorph ⁻¹' interior C := by
        rw [hpre]
        exact hx_int
      simpa [Set.mem_preimage, e] using hx_pre
  have hconvE : Convex ℝ (e.symm '' C) := by
    simpa [Set.image_image] using
      hC.linear_image (e.symm : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hEuclid :
      e.symm x ∈ interior (e.symm '' C) ↔
        ∀ yE : EuclideanSpace ℝ (Fin n),
          ∃ ε > (0 : ℝ), e.symm x + ε • yE ∈ e.symm '' C :=
    euclidean_interior_iff_forall_exists_add_smul_mem n (e.symm '' C) hconvE (e.symm x)
  have htransport :
      (∀ yE : EuclideanSpace ℝ (Fin n),
          ∃ ε > (0 : ℝ), e.symm x + ε • yE ∈ e.symm '' C) ↔
        (∀ y : Fin n → ℝ, ∃ ε > (0 : ℝ), x + ε • y ∈ C) := by
    constructor
    · intro h y
      rcases h (e.symm y) with ⟨ε, hε, hmem⟩
      rcases hmem with ⟨v, hv, hvEq⟩
      have hv' : v = x + ε • y := by
        simpa [e, map_add, map_smul] using congrArg e hvEq
      subst hv'
      exact ⟨ε, hε, hv⟩
    · intro h yE
      rcases h (e yE) with ⟨ε, hε, hmem⟩
      refine ⟨ε, hε, ?_⟩
      refine ⟨x + ε • e yE, hmem, ?_⟩
      simp [e, map_add, map_smul]
  exact hxInterior.trans (hEuclid.trans htransport)

/-- Helper for Theorem 23.4: relative-interior points admit subgradients. -/
lemma helperForTheorem_23_4_nonempty_subdifferential_of_mem_relativeInterior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    Set.Nonempty (subdifferentialAt f x) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxriE :
      (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    by
      have hxri' :=
        (mem_euclideanRelativeInterior_fin_iff (n := n)
          (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x)).1 hxri
      rw [helperForTheorem_23_4_preimage_eq_symmImage]
      exact hxri'
  have hxFiniteRaw :=
    properConvexFunctionOn_ne_top_on_ri_effectiveDomain (f := f) hproper
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) hxriE
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := ⟨hxFiniteRaw.2, hxFiniteRaw.1⟩
  by_contra hEmpty
  have h23 :=
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      f hf x hxFinite).2 hEmpty
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdir, _hpos, _hconv, hzero, _hsymm⟩
  have hbot : upperDirectionalDerivativeAt f x 0 = (⊥ : EReal) := by
    simpa using (h23.2 x hxri).1
  exact EReal.coe_ne_bot (0 : ℝ) (hzero.symm.trans hbot)

/-- Helper for Theorem 23.4: interior points have finite directional derivatives from above. -/
lemma helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    ∀ y : Fin n → ℝ, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
    interior_subset hxInt
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
    exact ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxDom,
      hproper.2.2 x (by simp)⟩
  intro y
  rcases
      (helperForTheorem_23_4_mem_interior_iff_forall_exists_add_smul_mem
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hdomConv x).1 hxInt y with
    ⟨ε, hε, hεDom⟩
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
  have hQ_bdd :
      BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp
  have hquot_ne_top : f (x + ε • y) ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hεDom
  have hquot_lt_top :
      directionalDifferenceQuotientAt f x y ε < (⊤ : EReal) := by
    have hquot_ne_top' : directionalDifferenceQuotientAt f x y ε ≠ (⊤ : EReal) := by
      have hnum_ne_top : f (x + ε • y) - f x ≠ (⊤ : EReal) := by
        rw [sub_eq_add_neg]
        exact EReal.add_ne_top hquot_ne_top (by simpa using hxFinite.2)
      intro htop
      have hnum_eq : f (x + ε • y) - f x = (⊤ : EReal) := by
        have hmul :=
          (EReal.div_eq_iff (a := (⊤ : EReal)) (b := (ε : EReal))
            (c := f (x + ε • y) - f x) (by simp) (by simp)
            (by exact_mod_cast hε.ne')).1 htop
        simpa using hmul.trans (EReal.top_mul_of_pos (by exact_mod_cast hε))
      exact hnum_ne_top hnum_eq
    exact lt_top_iff_ne_top.mpr hquot_ne_top'
  have hle :
      upperDirectionalDerivativeAt f x y ≤ directionalDifferenceQuotientAt f x y ε := by
    rw [(hdir y).2.2]
    exact csInf_le hQ_bdd ⟨ε, hε, rfl⟩
  exact ne_of_lt (lt_of_le_of_lt hle hquot_lt_top)

/-- Helper for Theorem 23.4: if all directional derivatives avoid `⊤`, then the base point lies in
the interior of the effective domain. -/
lemma helperForTheorem_23_4_mem_interior_of_directionalDerivative_ne_top
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hfiniteTop : ∀ y : Fin n → ℝ, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal)) :
    x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  have hdomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
  apply
    (helperForTheorem_23_4_mem_interior_iff_forall_exists_add_smul_mem
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hdomConv x).2
  intro y
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
  let Q : Set EReal :=
    (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t
  have hQ_nonempty : Q.Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f x y 1, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hsInf_lt_top : sInf Q < (⊤ : EReal) := by
    rw [← (hdir y).2.2]
    exact lt_top_iff_ne_top.mpr (hfiniteTop y)
  rcases exists_lt_of_csInf_lt hQ_nonempty hsInf_lt_top with ⟨q, hqQ, hq_lt_top⟩
  rcases hqQ with ⟨t, ht, rfl⟩
  have ht' : 0 < t := ht
  have hxt_ne_top : f (x + t • y) ≠ (⊤ : EReal) := by
    intro htop
    have : directionalDifferenceQuotientAt f x y t = (⊤ : EReal) := by
      rw [directionalDifferenceQuotientAt, htop]
      simpa [hx.1] using (EReal.top_div_of_pos_ne_top (by exact_mod_cast ht') (by simp))
    exact this.not_lt hq_lt_top
  refine ⟨t, ht', ?_⟩
  simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.mpr hxt_ne_top)

/-- Helper for Theorem 23.4: a nonempty subdifferential forces `f x` to be finite. -/
lemma helperForTheorem_23_4_finiteAt_of_subdifferentiable
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
  refine ⟨?_, hproper.2.2 x (by simp)⟩
  let xStar : Module.Dual ℝ (Fin n → ℝ) := Classical.choose hsub
  have hxStar : xStar ∈ subdifferentialAt f x := Classical.choose_spec hsub
  obtain ⟨z0, r0, hz0⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := f) hproper
  intro htop
  have hineq : f z0 ≥ f x + ((xStar (z0 - x) : ℝ) : EReal) := hxStar z0
  rw [htop, hz0] at hineq
  have htopLe : (⊤ : EReal) ≤ (r0 : EReal) := by
    have htopAdd :
        (⊤ : EReal) + ((xStar (z0 - x) : ℝ) : EReal) = (⊤ : EReal) :=
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    exact htopAdd ▸ hineq
  simp at htopLe

/-- Helper for Theorem 23.4: a nonempty subdifferential makes the directional derivative proper. -/
lemma helperForTheorem_23_4_upperDirectionalDerivative_proper_of_subdifferentiable
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite := helperForTheorem_23_4_finiteAt_of_subdifferentiable f hproper x hsub
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdirData, _hpos, hconvD, hzero, _hsymm⟩
  rcases hsub with ⟨g, hg⟩
  refine (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
    (S := (Set.univ : Set (Fin n → ℝ))) (f := D)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · simpa [ConvexFunction, D] using hconvD
  · refine ⟨0, ⟨0, ?_⟩⟩
    refine ⟨Set.mem_univ 0, ?_⟩
    simp [D, hzero]
  · intro y hy
    constructor
    · have hminor : ((g y : ℝ) : EReal) ≤ D y :=
        le_upperDirectionalDerivative_of_mem_subdifferential f hproper g hg y
      intro hybot
      exact (EReal.bot_lt_coe (g y)).not_ge (hybot ▸ hminor)
    · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := D) hy

/-- Helper for Theorem 23.4: interior points lie in the relative interior. -/
lemma helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hxInt : x ∈ interior C) :
    x ∈ euclideanRelativeInterior_fin n C := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hpreimage :
      e.toHomeomorph ⁻¹' C = e.symm '' C := by
    ext u
    constructor
    · intro hu
      exact ⟨e u, hu, by simp [e]⟩
    · rintro ⟨v, hv, rfl⟩
      simpa [e]
  have hxIntE : e.symm x ∈ interior (e.symm '' C) := by
    have hxPre : e.symm x ∈ e.toHomeomorph ⁻¹' interior C := by
      simpa [Set.mem_preimage, e] using hxInt
    have hpre :
        e.toHomeomorph ⁻¹' interior C = interior (e.symm '' C) := by
      calc
        e.toHomeomorph ⁻¹' interior C = interior (e.toHomeomorph ⁻¹' C) :=
          e.toHomeomorph.preimage_interior (s := C)
        _ = interior (e.symm '' C) := by rw [hpreimage]
    rw [hpre] at hxPre
    exact hxPre
  have hxI : e.symm x ∈ intrinsicInterior ℝ (e.symm '' C) :=
    interior_subset_intrinsicInterior hxIntE
  exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).2
    (intrinsicInterior_subset_euclideanRelativeInterior n (e.symm '' C) hxI)

/-- Helper for Theorem 23.4: if the subdifferential is nonempty and bounded, then every
directional derivative is finite from above. -/
lemma helperForTheorem_23_4_directionalDerivative_ne_top_of_nonempty_bounded_subdifferential
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn Set.univ f) (x : Fin n → ℝ)
    (hsub : Set.Nonempty (subdifferentialAt f x))
    (hCbd : Bornology.IsBounded ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) :
    ∀ y : Fin n → ℝ, upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let C : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite := helperForTheorem_23_4_finiteAt_of_subdifferentiable f hproper x hsub
  have hDproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) D :=
    helperForTheorem_23_4_upperDirectionalDerivative_proper_of_subdifferentiable
      f hproper x hsub
  rcases hsub with ⟨g, hg⟩
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite g
  have hCne : Set.Nonempty C := by
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
    simpa [C] using hg
  have hsupportEq :
      ∀ y : Fin n → ℝ, subdifferentialSupportAt f x y = supportFunctionEReal C y := by
    intro y
    symm
    exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
  have hclosureEq : convexFunctionClosure D = subdifferentialSupportAt f x := by
    simpa [D] using h23_2.2.2.2
  have hclosureFinite :
      ∀ y : Fin n → ℝ,
        convexFunctionClosure D y ≠ (⊤ : EReal) ∧
          convexFunctionClosure D y ≠ (⊥ : EReal) := by
    intro y
    constructor
    · rw [hclosureEq, hsupportEq y]
      exact section13_supportFunctionEReal_ne_top_of_isBounded (C := C) hCbd y
    · rw [hclosureEq, hsupportEq y]
      exact section13_supportFunctionEReal_ne_bot_of_nonempty (C := C) hCne y
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdirData, _hpos, hconvD, _hzero, _hsymm⟩
  have hdomcl_univ :
      ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure D)) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext z
    constructor
    · intro _hz
      simp
    · intro _hz
      have hzTop : convexFunctionClosure D (z : Fin n → ℝ) ≠ (⊤ : EReal) :=
        (hclosureFinite (z : Fin n → ℝ)).1
      simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.mpr hzTop)
  have hriEq :
      euclideanRelativeInterior n
        ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure D)) =
      euclideanRelativeInterior n
        ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := by
    simpa [D] using
      (convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
        (f := D) hDproper).2.2.2.1
  have hriDomD_univ :
      euclideanRelativeInterior n
        ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    calc
      euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) =
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure D)) := by
              symm
              exact hriEq
      _ = euclideanRelativeInterior n (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
            rw [hdomcl_univ]
      _ = Set.univ := by
            rw [euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ
              (n := n) (C := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (by simp)]
            simp
  have hriSub :
      euclideanRelativeInterior n
        ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) ⊆
      ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) :=
    (euclideanRelativeInterior_subset_closure n
      ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) D)).1
  intro y
  have hyRi :
      e.symm y ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := by
    simpa [hriDomD_univ]
  have hyDom :
      e.symm y ∈
        ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := hriSub hyRi
  exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := D) hyDom

/-- Helper for Theorem 23.4: on `ri (dom f)`, the directional derivative is closed proper and
agrees with the support function of the subdifferential. -/
lemma helperForTheorem_23_4_directionalDerivative_regularity_of_mem_relativeInterior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    Set.Nonempty (subdifferentialAt f x) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) ∧
      ClosedConvexFunction (upperDirectionalDerivativeAt f x) ∧
      convexFunctionClosure (upperDirectionalDerivativeAt f x) =
        upperDirectionalDerivativeAt f x ∧
      ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let domD : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) D
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let domDE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' domD
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hsub :=
    helperForTheorem_23_4_nonempty_subdifferential_of_mem_relativeInterior f hproper x hxri
  have hxriE :
      (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    have hxri' :=
      (mem_euclideanRelativeInterior_fin_iff (n := n)
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x)).1 hxri
    rw [helperForTheorem_23_4_preimage_eq_symmImage]
    exact hxri'
  have hxFiniteRaw :=
    properConvexFunctionOn_ne_top_on_ri_effectiveDomain (f := f) hproper
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) hxriE
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := ⟨hxFiniteRaw.2, hxFiniteRaw.1⟩
  rcases hsub with ⟨g, hg⟩
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite g
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hdirData, hposD, hconvD, hzeroD, _hsymmD⟩
  have hDproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) D :=
    helperForTheorem_23_4_upperDirectionalDerivative_proper_of_subdifferentiable
      f hproper x ⟨g, hg⟩
  have hdomDConv : Convex ℝ domD :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := D) hconvD
  have h0ri :
      (0 : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n domD := by
    simpa using
      (helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative
        f hf x x hxFinite hxri)
  have hdomDEConv : Convex ℝ domDE := by
    simpa [domDE] using
      (Convex.affine_image (f := e.symm.toAffineMap) hdomDConv)
  have h0riE :
      e.symm (0 : Fin n → ℝ) ∈ euclideanRelativeInterior n domDE := by
    simpa [domDE] using
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := domD) (x := (0 : Fin n → ℝ))).1 h0ri
  have hdomDENe : domDE.Nonempty := by
    refine ⟨e.symm (0 : Fin n → ℝ), ?_⟩
    exact (euclideanRelativeInterior_subset_closure n domDE).1 h0riE
  have hdomD_cone_nonneg :
      ∀ {r : ℝ}, 0 ≤ r → ∀ {y : Fin n → ℝ}, y ∈ domD → r • y ∈ domD := by
    intro r hr y hy
    rcases lt_or_eq_of_le hr with hrpos | rfl
    · have hyTop : D y ≠ (⊤ : EReal) := by
        exact (lt_top_iff_ne_top.mp (by simpa [domD, effectiveDomain_eq] using hy))
      have hmulTop : ((r : ℝ) : EReal) * D y ≠ (⊤ : EReal) := by
        refine (EReal.mul_ne_top _ _).2 ?_
        refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inl (by exact_mod_cast hr),
          Or.inl (EReal.coe_ne_top _), Or.inr hyTop⟩
      have hrtop : D (r • y) < (⊤ : EReal) := by
        have hEq : D (r • y) = ((r : ℝ) : EReal) * D y := by
          simpa [D] using hposD y r hrpos
        rw [hEq]
        exact lt_top_iff_ne_top.mpr hmulTop
      simpa [domD, effectiveDomain_eq] using hrtop
    · simpa [domD, effectiveDomain_eq, D, hzeroD]
  have hdomDE_cone_nonneg :
      ∀ {r : ℝ}, 0 ≤ r → ∀ {u : EuclideanSpace ℝ (Fin n)}, u ∈ domDE → r • u ∈ domDE := by
    intro r hr u hu
    rcases hu with ⟨y, hy, rfl⟩
    refine ⟨r • y, hdomD_cone_nonneg hr hy, ?_⟩
    simp [e, map_smul]
  have hdomDE_symm :
      ∀ {u : EuclideanSpace ℝ (Fin n)}, u ∈ domDE → -u ∈ domDE := by
    intro u hu
    rcases
        (euclideanRelativeInterior_iff_forall_exists_affine_combination_mem n domDE
          hdomDEConv hdomDENe (0 : EuclideanSpace ℝ (Fin n))).1 h0riE u hu with
      ⟨μ, hμ, hmem⟩
    have hμ1 : 0 < μ - 1 := by
      linarith
    have hnegScaled : (-(μ - 1)) • u ∈ domDE := by
      simpa using hmem
    have hscaled :
        (μ - 1)⁻¹ • ((-(μ - 1)) • u) ∈ domDE :=
      hdomDE_cone_nonneg (inv_nonneg.mpr (le_of_lt hμ1)) hnegScaled
    have hscaled' : (((μ - 1)⁻¹ * (-(μ - 1))) : ℝ) • u ∈ domDE := by
      simpa [smul_smul] using hscaled
    have hcoef : (μ - 1)⁻¹ * (-(μ - 1)) = (-1 : ℝ) := by
      field_simp [ne_of_gt hμ1]
    rw [hcoef] at hscaled'
    simpa using hscaled'
  have hdomD_symm :
      ∀ {y : Fin n → ℝ}, y ∈ domD → -y ∈ domD := by
    intro y hy
    have hyE : e.symm y ∈ domDE := by
      exact ⟨y, hy, rfl⟩
    have hnegE : e.symm (-y) ∈ domDE := by
      simpa [e.map_neg] using hdomDE_symm hyE
    rcases hnegE with ⟨v, hv, hvEq⟩
    have : v = -y := by
      exact e.symm.injective hvEq
    simpa [this] using hv
  have hdomD_add :
      ∀ {y z : Fin n → ℝ}, y ∈ domD → z ∈ domD → y + z ∈ domD := by
    intro y z hy hz
    have hmid : midpoint ℝ y z ∈ domD := Convex.midpoint_mem hdomDConv hy hz
    have hscaled : (2 : ℝ) • (((1 / 2 : ℝ) • y) + (1 / 2 : ℝ) • z) ∈ domD :=
      hdomD_cone_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by simpa [midpoint_eq_smul_add] using hmid)
    simpa [smul_add, smul_smul] using hscaled
  have hdomD_smul :
      ∀ {r : ℝ} {y : Fin n → ℝ}, y ∈ domD → r • y ∈ domD := by
    intro r y hy
    by_cases hr : 0 ≤ r
    · exact hdomD_cone_nonneg hr hy
    · have hnonneg : 0 ≤ -r := by linarith
      have hposPart : (-r) • y ∈ domD := hdomD_cone_nonneg hnonneg hy
      have hnegPart : -((-r) • y) ∈ domD := hdomD_symm hposPart
      simpa [smul_smul] using hnegPart
  let S : Submodule ℝ (Fin n → ℝ) :=
    { carrier := domD
      zero_mem' := by
        simpa [domD, effectiveDomain_eq, D, hzeroD]
      add_mem' := by
        intro y z hy hz
        exact hdomD_add hy hz
      smul_mem' := by
        intro r y hy
        exact hdomD_smul hy }
  have hdomDAff : IsAffineSet n domD := by
    simpa [S] using isAffineSet_of_submodule n S
  have hDclosed : ClosedConvexFunction D :=
    properConvexFunction_closed_of_affine_effectiveDomain (n := n) (f := D) hDproper hdomDAff
  have hDnotBot : ∀ y : Fin n → ℝ, D y ≠ (⊥ : EReal) := by
    intro y
    exact hDproper.2.2 y (by simp)
  have hclEq : convexFunctionClosure D = D :=
    convexFunctionClosure_eq_of_closedConvexFunction (f := D) hDclosed hDnotBot
  refine ⟨⟨g, hg⟩, hDproper, hDclosed, hclEq, ?_⟩
  intro y
  calc
    D y = convexFunctionClosure D y := by
      symm
      exact congrFun hclEq y
    _ = subdifferentialSupportAt f x y := by
      exact congrFun (by simpa [D] using h23_2.2.2.2) y

/-- Theorem 23.4: Let `f` be a proper convex function. If `x ∉ dom f`, then the
subdifferential `∂f(x)` is empty. If `x ∈ ri (dom f)`, then `∂f(x)` is nonempty, the directional
derivative function `y ↦ f'(x; y)` is a closed proper convex function, and for every direction `y`
it equals the support function `δ^*(y | ∂f(x))`. Finally, `∂f(x)` is nonempty and bounded if and
only if `x ∈ interior (dom f)`; in that case `f'(x; y)` is finite for every `y`. -/
theorem subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) (x : Fin n → ℝ) :
    (x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f →
      subdifferentialAt f x = ∅) ∧
    (x ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
      Set.Nonempty (subdifferentialAt f x) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) ∧
        convexFunctionClosure (upperDirectionalDerivativeAt f x) = upperDirectionalDerivativeAt f x ∧
        ∀ y : Fin n → ℝ,
          upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y) ∧
    (((Set.Nonempty (subdifferentialAt f x) ∧
          Bornology.IsBounded ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) ↔
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∧
      (x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        ∀ y : Fin n → ℝ,
          upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) ∧
            upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal))) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let C : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  refine ⟨?_, ?_, ?_⟩
  · intro hxOff
    -- The off-domain clause is exactly the first helper lemma.
    exact helperForTheorem_23_4_subdifferential_empty_of_not_mem_effectiveDomain f hproper x hxOff
  · intro hxri
    rcases
        helperForTheorem_23_4_directionalDerivative_regularity_of_mem_relativeInterior
          f hproper x hxri with
      ⟨hsub, hDproper, _hDclosed, hclEq, hDirEq⟩
    exact ⟨hsub, hDproper, hclEq, hDirEq⟩
  · refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hsub, hCbd⟩
        have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
          helperForTheorem_23_4_finiteAt_of_subdifferentiable f hproper x hsub
        have hfiniteTop : ∀ y : Fin n → ℝ, D y ≠ (⊤ : EReal) :=
          helperForTheorem_23_4_directionalDerivative_ne_top_of_nonempty_bounded_subdifferential
            f hproper x hsub hCbd
        -- Route correction: boundedness gives finiteness of the support function, which is the
        -- right input for the interior characterization.
        exact helperForTheorem_23_4_mem_interior_of_directionalDerivative_ne_top f hf x hxFinite hfiniteTop
      · intro hxInt
        have hfiniteTop :
            ∀ y : Fin n → ℝ, D y ≠ (⊤ : EReal) :=
          helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior f hproper x hxInt
        have hxri :
            x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
          helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hxInt
        rcases
            helperForTheorem_23_4_directionalDerivative_regularity_of_mem_relativeInterior
              f hproper x hxri with
          ⟨hsub, _hDproper, _hDclosed, _hclEq, hDirEq⟩
        rcases hsub with ⟨g, hg⟩
        have hsupportFinite :
            ∀ y : Fin n → ℝ,
              supportFunctionEReal C y ≠ (⊤ : EReal) ∧
                supportFunctionEReal C y ≠ (⊥ : EReal) := by
          intro y
          have hDirEqSupport : D y = supportFunctionEReal C y := by
            calc
              D y = subdifferentialSupportAt f x y := hDirEq y
              _ = supportFunctionEReal C y := by
                symm
                exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
          refine ⟨?_, ?_⟩
          · rw [← hDirEqSupport]
            exact hfiniteTop y
          · exact
              section13_supportFunctionEReal_ne_bot_of_nonempty (C := C)
                ⟨(dotProductEquiv ℝ (Fin n)).symm g, by simpa [C] using hg⟩ y
        refine ⟨⟨g, hg⟩, ?_⟩
        exact section13_isBounded_of_supportFunctionEReal_finite (C := C) hsupportFinite
    · intro hxInt y
      have hfiniteTop :
          ∀ z : Fin n → ℝ, D z ≠ (⊤ : EReal) :=
        helperForTheorem_23_4_directionalDerivative_ne_top_of_mem_interior f hproper x hxInt
      have hxri :
          x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
        helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
          (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hxInt
      rcases
          helperForTheorem_23_4_directionalDerivative_regularity_of_mem_relativeInterior
            f hproper x hxri with
        ⟨hsub, _hDproper, _hDclosed, _hclEq, hDirEqAll⟩
      rcases hsub with ⟨g, hg⟩
      have hDirEq : D y = supportFunctionEReal C y := by
        calc
          D y = subdifferentialSupportAt f x y := hDirEqAll y
          _ = supportFunctionEReal C y := by
            symm
            exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
      refine ⟨hfiniteTop y, ?_⟩
      simpa [D, hDirEq] using
        (section13_supportFunctionEReal_ne_bot_of_nonempty (C := C)
          ⟨(dotProductEquiv ℝ (Fin n)).symm g, by simpa [C] using hg⟩ y)

end Section23
end Chap05
