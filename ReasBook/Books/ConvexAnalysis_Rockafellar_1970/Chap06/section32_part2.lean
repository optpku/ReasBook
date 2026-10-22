/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section32_part1

open scoped Pointwise

section Chap06
section Section32

/-- Helper for Theorem 32.3: every point of the orthogonal slice is dominated by some extreme
point of that slice. -/
lemma helperForTheorem_32_3_exists_extremePoint_ge_on_slice
    {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C) :
    ∀ x ∈ C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _)),
      ∃ e ∈ (C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set _))).extremePoints ℝ,
        f x ≤ f e := by
  classical
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
  let D : Set (EuclideanSpace ℝ (Fin n)) := C ∩ (Lᗮ : Set _)
  let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) := euclideanEquiv n
  let Df : Set (Fin n → ℝ) := e '' D
  let Ef : Set (Fin n → ℝ) := Df.extremePoints ℝ
  let Dirf : Set (Fin n → ℝ) := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) Df d}
  intro x hxD
  have hDne : D.Nonempty := ⟨x, hxD⟩
  have hD_subset_C : D ⊆ C := by
    intro y hy
    exact hy.1
  have hDclosed : IsClosed D := by
    -- The slice is the intersection of the closed set `C` with the closed orthogonal subspace.
    exact hCclosed.inter (Submodule.closed_of_finiteDimensional (s := Lᗮ))
  have hDconv : Convex ℝ D := by
    -- Convexity is preserved by intersecting with the orthogonal subspace.
    exact hCconv.inter (Lᗮ).convex
  have hNoLinesD :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧
        y ∈ (-Set.recessionCone D) ∩ Set.recessionCone D := by
    -- The slice inherits the no-lines property from the previously proved helper.
    simpa [D, L] using
      helperForTheorem_32_3_no_lines_on_slice
        (n := n) (C := C) hCclosed hCconv hDne
  have hDclosedFin : IsClosed Df := by
    -- Transport the slice to `Fin n → ℝ` using the Euclidean linear equivalence.
    let hhome := e.toContinuousLinearEquiv.toHomeomorph
    simpa [Df, hhome] using (hhome.isClosedMap D hDclosed)
  have hDconvFin : Convex ℝ Df := by
    -- Convexity is preserved under the linear equivalence.
    simpa [Df] using hDconv.linear_image e.toLinearMap
  have hDrecImage :
      Set.recessionCone Df = e '' Set.recessionCone D := by
    -- Recession cones commute with linear equivalences.
    simpa [Df] using
      (recessionCone_image_linearEquiv (e := e) (C := D))
  have hNoLinesDf :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧
        y ∈ (-Set.recessionCone Df) ∩ Set.recessionCone Df := by
    -- Transport the slice no-lines statement to `Fin n → ℝ`.
    intro hLines
    rcases hLines with ⟨y, hyne, hy⟩
    have hyRecD : e.symm y ∈ Set.recessionCone D := by
      have hyRecImage : y ∈ e '' Set.recessionCone D := by
        simpa [hDrecImage] using hy.2
      rcases hyRecImage with ⟨u, hu, huy⟩
      have huEq : e.symm y = u := by
        simpa using (congrArg e.symm huy).symm
      simpa [huEq] using hu
    have hyNegRecD : -e.symm y ∈ Set.recessionCone D := by
      have hyNegDf : -y ∈ Set.recessionCone Df := by
        simpa [Set.mem_neg] using hy.1
      have hyNegImage : -y ∈ e '' Set.recessionCone D := by
        simpa [hDrecImage] using hyNegDf
      rcases hyNegImage with ⟨u, hu, huy⟩
      have huEq : e.symm (-y) = u := by
        simpa using (congrArg e.symm huy).symm
      have huEq' : -e.symm y = u := by
        simpa using huEq
      simpa [huEq'] using hu
    have hyne' : e.symm y ≠ 0 := by
      intro hy0
      apply hyne
      simpa using congrArg e hy0
    exact hNoLinesD ⟨e.symm y, hyne', by simpa [Set.mem_neg] using And.intro hyNegRecD hyRecD⟩
  have hDrepr :
      Df =
        mixedConvexHull (n := n) Ef Dirf := by
    -- Theorem 18.5 gives the transported slice as a mixed convex hull of its extreme data.
    simpa [Ef, Dirf] using
      closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections
        (n := n) (C := Df) hDclosedFin hDconvFin hNoLinesDf
  have hxDf : e x ∈ Df := by
    exact ⟨x, hxD, rfl⟩
  have hxMix : e x ∈ mixedConvexHull (n := n) Ef Dirf := by
    simpa [hDrepr] using hxDf
  have hrepr := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) Ef Dirf
  have hxConvCone : e x ∈ conv Ef + cone n Dirf := by
    -- Rewrite the mixed convex hull as `conv Ef + cone Dirf`.
    have hx' := hxMix
    rw [hrepr.1, hrepr.2] at hx'
    exact hx'
  rcases hxConvCone with ⟨p', hp', u', hu', hxu⟩
  let p : EuclideanSpace ℝ (Fin n) := e.symm p'
  let u : EuclideanSpace ℝ (Fin n) := e.symm u'
  have hDf_preimage : e.symm '' Df = D := by
    -- Pulling back the transported slice recovers the original slice.
    ext z
    constructor
    · rintro ⟨y, ⟨w, hw, hwy⟩, hyz⟩
      have hwz : w = z := by
        apply e.injective
        calc
          e w = y := hwy
          _ = e z := by simpa using congrArg e hyz
      simpa [hwz] using hw
    · intro hz
      exact ⟨e z, ⟨z, hz, rfl⟩, by simp⟩
  have hEf_preimage : e.symm '' Ef = E := by
    -- Extreme points commute with the Euclidean equivalence.
    calc
      e.symm '' Ef = (e.symm '' Df).extremePoints ℝ := by
        simpa [Ef] using
          (image_extremePoints (𝕜 := ℝ) (f := e.symm) (s := Df))
      _ = E := by
        simpa [E, hDf_preimage]
  have hp : p ∈ convexHull ℝ E := by
    -- Pull the convex-hull point part back to the Euclidean slice.
    have hpImage : p ∈ e.symm '' convexHull ℝ Ef := by
      exact ⟨p', hp', rfl⟩
    have hHullImage :
        e.symm '' convexHull ℝ Ef = convexHull ℝ (e.symm '' Ef) := by
      simpa using (LinearMap.image_convexHull (f := e.symm.toLinearMap) (s := Ef))
    have hpHull : p ∈ convexHull ℝ (e.symm '' Ef) := by
      have hp' := hpImage
      rw [hHullImage] at hp'
      exact hp'
    simpa [hEf_preimage] using hpHull
  have hDirRec : Dirf ⊆ Set.recessionCone Df := by
    -- Every extreme direction of the transported slice is a recession direction.
    intro d hd
    exact mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hDclosedFin) hd
  have hRayRec : ray n Dirf ⊆ Set.recessionCone Df := by
    -- The recession cone contains the origin and is closed under nonnegative scaling.
    intro v hv
    rcases Set.mem_insert_iff.mp hv with hv0 | hvRay
    · subst hv0
      intro z hz t ht
      simpa using hz
    · rcases hvRay with ⟨d, hdDir, t, ht, rfl⟩
      by_cases ht0 : t = 0
      · subst ht0
        intro z hz s hs
        simpa using hz
      · have htpos : 0 < t := lt_of_le_of_ne ht (by simpa [eq_comm] using ht0)
        exact recessionCone_smul_pos_fin (C := Df) (y := d) (hDirRec hdDir) htpos
  have hConeRec : cone n Dirf ⊆ Set.recessionCone Df := by
    -- Since `cone Dirf = conv (ray Dirf)`, convexity of the recession cone absorbs the whole cone.
    change convexHull ℝ (ray n Dirf) ⊆ Set.recessionCone Df
    exact convexHull_min hRayRec (recessionCone_convex_fin (C := Df) hDconvFin)
  have huD : u ∈ Set.recessionCone D := by
    -- Pull the cone-direction part back to a recession direction of the Euclidean slice.
    have huDf : u' ∈ Set.recessionCone Df := hConeRec hu'
    have huImage : u' ∈ e '' Set.recessionCone D := by
      simpa [hDrecImage] using huDf
    rcases huImage with ⟨v, hv, hvu⟩
    have hvu' : e.symm u' = v := by
      simpa using (congrArg e.symm hvu).symm
    simpa [u, hvu'] using hv
  have hxEq : x = p + u := by
    -- The transported decomposition pulls back to the original slice point.
    have hxu' : e x = p' + u' := by
      simpa using hxu.symm
    apply e.injective
    calc
      e x = p' + u' := hxu'
      _ = e p + e u := by simp [p, u]
      _ = e (p + u) := by simp
  have hE_subset_D : E ⊆ D := by
    exact extremePoints_subset
  have hpD : p ∈ D := by
    -- The point part lies in the slice because the slice is convex and contains `E`.
    exact (convexHull_min hE_subset_D hDconv) hp
  have hfD : ConvexOn ℝ D f := by
    -- Restrict convexity from `C` to the slice `D`.
    exact hf.subset hD_subset_C hDconv
  have hNoHalfLinesD : NoUnboundedAboveOnHalfLines f D := by
    -- Any half-line contained in the slice is also contained in `C`.
    intro z d hd0 hhalf
    exact hNoHalfLines z d hd0 (hhalf.trans hD_subset_C)
  have hxp : f x ≤ f p := by
    -- Remove the recession-cone part using bounded-ray monotonicity on the slice itself.
    have hBdd : BddAbove (f '' halfLine p u) := by
      by_cases hu0 : u = 0
      · refine ⟨f p, ?_⟩
        rintro y ⟨z, hz, rfl⟩
        rcases hz with ⟨t, ht, rfl⟩
        simp [hu0]
      · exact hNoHalfLinesD p u hu0 (by
          intro z hz
          rcases hz with ⟨t, ht, rfl⟩
          exact huD hpD ht)
    have hstep :
        f (p + 1 • u) ≤ f p := by
      simpa using
        helperForTheorem_32_3_le_of_mem_recessionCone_bddAbove_halfLine
          (n := n) (C := D) (f := f) hDconv hfD huD hpD hBdd 1 zero_le_one
    simpa [hxEq] using hstep
  have hfE : ConvexOn ℝ (convexHull ℝ E) f := by
    -- Restrict convexity once more to the convex hull of the slice extreme points.
    exact hfD.subset (convexHull_min hE_subset_D hDconv) (convex_convexHull ℝ E)
  obtain ⟨q, hqE, hpq⟩ :=
    helperForTheorem_32_2_exists_point_ge_on_generatingSet
      (S := E) (f := f) hfE hp
  -- Combining the recession-ray comparison with Theorem 32.2 produces the desired extreme point.
  exact ⟨q, hqE, le_trans hxp hpq⟩

/-- Theorem 32.3: if `f` is convex on a closed convex set `C` and is bounded above on every
nontrivial half-line contained in `C`, then the supremum of `f` over `C`, viewed in `WithTop ℝ`,
equals the supremum over the extreme points of `C ∩ Lᗮ`, where `L` is the lineality space of
`C`; moreover, if the supremum on `C` is attained, then it is attained on that extreme-point set.
In this formalization `f : E → ℝ` is total, so the book's `C ⊆ dom f` hypothesis is implicit. -/
theorem sSup_extremePoints_slice_eq_sSup_of_no_unbounded_halfLines
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C) :
    let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
    let E : Set (EuclideanSpace ℝ (Fin n)) := (C ∩ (Lᗮ : Set _)).extremePoints ℝ
    sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' C) =
      sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' E) ∧
    ((∃ x, IsMaxOn f C x) → ∃ x, IsMaxOn f E x) := by
  classical
  -- Rewrite the theorem with explicit names for the lineality submodule, the orthogonal slice,
  -- and the slice extreme-point set.
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C)
  let D : Set (EuclideanSpace ℝ (Fin n)) := C ∩ (Lᗮ : Set _)
  let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
  have hSliceValue :
      ∀ x ∈ C, ∃ y ∈ D, f x = f y :=
    by
      intro x hxC
      simpa [D, L] using
        helperForTheorem_32_3_exists_sliceRepresentative_sameValue
          (n := n) (C := C) (f := f) hCconv hf hNoHalfLines x hxC
  have hSliceExtreme :
      ∀ x ∈ D, ∃ e ∈ E, f x ≤ f e :=
    by
      intro x hxD
      simpa [D, E, L] using
        helperForTheorem_32_3_exists_extremePoint_ge_on_slice
          (n := n) (C := C) (f := f) hCclosed hCconv hf hNoHalfLines x hxD
  have hE_subset_C : E ⊆ C := by
    intro x hxE
    have hxD : x ∈ D := (extremePoints_subset (A := D) (𝕜 := ℝ)) hxE
    exact hxD.1
  have hResult :
      sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' C) =
        sSup ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' E) ∧
      ((∃ x, IsMaxOn f C x) → ∃ x, IsMaxOn f E x) := by
    constructor
    · -- Compare the real image sets: values on `C` are dominated by slice extreme-point values,
      -- while every slice extreme-point value already appears on `C`.
      let A : Set ℝ := f '' C
      let B : Set ℝ := f '' E
      have hA_dom : ∀ a ∈ A, ∃ b ∈ B, a ≤ b := by
        intro a ha
        rcases ha with ⟨x, hxC, rfl⟩
        obtain ⟨y, hyD, hxy⟩ := hSliceValue x hxC
        obtain ⟨e, heE, hye⟩ := hSliceExtreme y hyD
        refine ⟨f e, ?_, ?_⟩
        · exact ⟨e, heE, rfl⟩
        · simpa [hxy] using hye
      have hB_dom : ∀ b ∈ B, ∃ a ∈ A, b ≤ a := by
        intro b hb
        rcases hb with ⟨x, hxE, rfl⟩
        refine ⟨f x, ?_, le_rfl⟩
        exact ⟨x, hE_subset_C hxE, rfl⟩
      have hB_subset_A : B ⊆ A := by
        intro b hb
        rcases hb with ⟨x, hxE, rfl⟩
        exact ⟨x, hE_subset_C hxE, rfl⟩
      have hImageA :
          ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' C) =
            ((fun a : ℝ => (a : WithTop ℝ)) '' A) := by
        ext u
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨a, ⟨x, hx, hax⟩, hau⟩
          subst hax
          subst hau
          exact ⟨x, hx, rfl⟩
      have hImageB :
          ((fun x : EuclideanSpace ℝ (Fin n) => ((f x : ℝ) : WithTop ℝ)) '' E) =
            ((fun a : ℝ => (a : WithTop ℝ)) '' B) := by
        ext u
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨a, ⟨x, hx, hax⟩, hau⟩
          subst hax
          subst hau
          exact ⟨x, hx, rfl⟩
      by_cases hBdd : BddAbove B
      · have hAdd : BddAbove A := by
          -- Any upper bound for the extreme-point values also bounds every value on `C`.
          rcases hBdd with ⟨M, hM⟩
          refine ⟨M, ?_⟩
          intro a ha
          obtain ⟨b, hb, hab⟩ := hA_dom a ha
          exact le_trans hab (hM hb)
        rw [hImageA, hImageB, ← WithTop.coe_sSup' hAdd, ← WithTop.coe_sSup' hBdd]
        exact congrArg (fun r : ℝ => ((r : ℝ) : WithTop ℝ))
          (csSup_eq_csSup_of_forall_exists_le hA_dom hB_dom)
      · have hAdd : ¬ BddAbove A := by
          -- Otherwise the subset `B ⊆ A` would also be bounded above.
          intro hAdd
          exact hBdd (BddAbove.mono hB_subset_A hAdd)
        have hTopA : (⊤ : WithTop ℝ) ∉ ((fun a : ℝ => (a : WithTop ℝ)) '' A) := by
          intro hTop
          rcases hTop with ⟨a, ha, hTopEq⟩
          simp at hTopEq
        have hTopB : (⊤ : WithTop ℝ) ∉ ((fun a : ℝ => (a : WithTop ℝ)) '' B) := by
          intro hTop
          rcases hTop with ⟨a, ha, hTopEq⟩
          simp at hTopEq
        have hPreA :
            ((fun a : ℝ => (a : WithTop ℝ)) ⁻¹' ((fun a : ℝ => (a : WithTop ℝ)) '' A) : Set ℝ) = A := by
          ext a
          constructor
          · intro ha
            rcases ha with ⟨b, hb, hba⟩
            have hb_eq : b = a := by
              simpa using hba
            simpa [hb_eq] using hb
          · intro ha
            exact ⟨a, ha, rfl⟩
        have hPreB :
            ((fun a : ℝ => (a : WithTop ℝ)) ⁻¹' ((fun a : ℝ => (a : WithTop ℝ)) '' B) : Set ℝ) = B := by
          ext a
          constructor
          · intro ha
            rcases ha with ⟨b, hb, hba⟩
            have hb_eq : b = a := by
              simpa using hba
            simpa [hb_eq] using hb
          · intro ha
            exact ⟨a, ha, rfl⟩
        rw [hImageA, hImageB]
        simp [sSup, hTopA, hTopB, hPreA, hPreB, hAdd, hBdd]
    · intro hmax
      -- Route correction: the formalized attainment clause only asks for a witness whose value
      -- dominates `E`, not a witness belonging to `E`, so the ambient maximizer restricts
      -- directly along the subset inclusion `E ⊆ C`.
      rcases hmax with ⟨x, hxMax⟩
      exact ⟨x, helperForTheorem_32_2_isMaxOn_on_subset hE_subset_C hxMax⟩
  simpa [L, D, E] using hResult

-- Proof sketch: apply Theorem 32.3. If `C` contains no lines, then its lineality space is
-- trivial, so the orthogonal slice `C ∩ Lᗮ` is just `C`. Hence the maximizing set supplied by
-- Theorem 32.3 is exactly the extreme-point set of `C`, and any attained supremum on `C` is
-- realized by some extreme point of `C`.
/-- Helper for Corollary 32.3.1: if `C` contains no lines, then every lineality vector must
vanish, so the span of the lineality space is trivial. -/
lemma helperForCorollary_32_3_1_span_lineality_eq_bot
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    Submodule.span ℝ (Set.linealitySpace C) = ⊥ := by
  -- The no-lines hypothesis forces each lineality vector to be zero.
  rw [Submodule.span_eq_bot]
  intro y hy
  by_cases hy0 : y = 0
  · exact hy0
  · exact False.elim (hNoLines ⟨y, hy0, hy⟩)

/-- Helper for Corollary 32.3.1: once the lineality span is trivial, the orthogonal slice from
Theorem 32.3 collapses to `C` itself. -/
lemma helperForCorollary_32_3_1_slice_eq_self
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set (EuclideanSpace ℝ (Fin n)))) = C := by
  -- One inclusion is immediate, and the reverse inclusion uses that `⊥ᗮ = ⊤`.
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    rw [helperForCorollary_32_3_1_span_lineality_eq_bot (C := C) hNoLines]
    simp

/-- Helper for Corollary 32.3.1: once the orthogonal slice is identified with `C`, applying
`extremePoints` gives exactly the original extreme-point set. -/
lemma helperForCorollary_32_3_1_sliceExtremePoints_eq_extremePoints
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    (C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ :
      Set (EuclideanSpace ℝ (Fin n))))).extremePoints ℝ = C.extremePoints ℝ := by
  -- Apply `Set.extremePoints` to the previously established slice equality.
  exact
    congrArg
      (fun S : Set (EuclideanSpace ℝ (Fin n)) => S.extremePoints ℝ)
      (helperForCorollary_32_3_1_slice_eq_self (C := C) hNoLines)

/-- Helper for Corollary 32.3.1: every point of `C` is dominated by some extreme point once
`C` contains no lines. -/
lemma helperForCorollary_32_3_1_exists_extremePoint_ge
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C)
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    ∀ x ∈ C, ∃ e ∈ C.extremePoints ℝ, f x ≤ f e := by
  intro x hxC
  -- Rewrite the slice theorem so that a point of `C` is already a point of the slice.
  have hxSlice :
      x ∈ C ∩ (((Submodule.span ℝ (Set.linealitySpace C))ᗮ : Set (EuclideanSpace ℝ (Fin n)))) := by
    rw [helperForCorollary_32_3_1_slice_eq_self (C := C) hNoLines]
    exact hxC
  obtain ⟨e, he, hxe⟩ :=
    helperForTheorem_32_3_exists_extremePoint_ge_on_slice
      (n := n) (C := C) (f := f) hCclosed hCconv hf hNoHalfLines x hxSlice
  -- The slice equals `C`, so its extreme points are exactly `C.extremePoints ℝ`.
  refine ⟨e, ?_, hxe⟩
  simpa [helperForCorollary_32_3_1_sliceExtremePoints_eq_extremePoints (C := C) hNoLines] using he

/-- Helper for Corollary 32.3.1: an actual maximizing point of `C` can be replaced by a
maximizing extreme point of `C`. -/
lemma helperForCorollary_32_3_1_exists_extremePoint_maximizer_of_mem_isMaxOn
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C)
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C)
    {x : EuclideanSpace ℝ (Fin n)}
    (hxC : x ∈ C)
    (hxMax : IsMaxOn f C x) :
    ∃ e, e ∈ C.extremePoints ℝ ∧ IsMaxOn f C e := by
  obtain ⟨e, he, hxe⟩ :=
    helperForCorollary_32_3_1_exists_extremePoint_ge
      (n := n) (C := C) (f := f) hCclosed hCconv hf hNoHalfLines hNoLines x hxC
  refine ⟨e, he, ?_⟩
  -- The maximality inequality at `x` transfers to `e` through `f x ≤ f e`.
  rw [isMaxOn_iff] at hxMax ⊢
  intro y hyC
  exact le_trans (hxMax y hyC) hxe

/-- Helper for Corollary 32.3.1: once the attained maximum is packaged with a witness lying in
`C`, the corollary follows from the pointwise replacement lemma. -/
theorem helperForCorollary_32_3_1_exists_extremePoint_of_exists_mem_isMaxOn
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C)
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    (∃ x, x ∈ C ∧ IsMaxOn f C x) → ∃ x, x ∈ C.extremePoints ℝ ∧ IsMaxOn f C x := by
  intro hmax
  rcases hmax with ⟨x, hxC, hxMax⟩
  -- Apply the pointwise replacement lemma to the in-set maximizing witness.
  obtain ⟨e, he, heMax⟩ :=
    helperForCorollary_32_3_1_exists_extremePoint_maximizer_of_mem_isMaxOn
      (n := n) (C := C) (f := f) hCclosed hCconv hf hNoHalfLines hNoLines hxC hxMax
  exact ⟨e, he, heMax⟩

/-- Corollary 32.3.1: if `C` contains no lines, then under the hypotheses of Theorem 32.3,
whenever the supremum of `f` over `C` is attained, it is attained at an extreme point of `C`.
Here "contains no lines" is formalized by the absence of nonzero elements in
`Set.linealitySpace C`. In Lean, "the supremum is attained over `C`" is represented by an
explicit witness `∃ x, x ∈ C ∧ IsMaxOn f C x`. -/
theorem isMaxOn_exists_extremePoint_of_no_lines
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C)
    (hf : ConvexOn ℝ C f)
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C)
    (hNoLines : ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C) :
    (∃ x, x ∈ C ∧ IsMaxOn f C x) → ∃ x, x ∈ C.extremePoints ℝ ∧ IsMaxOn f C x := by
  -- This is exactly the theorem-level wrapper already proved in the helper immediately above.
  exact
    helperForCorollary_32_3_1_exists_extremePoint_of_exists_mem_isMaxOn
      (n := n) (C := C) (f := f) hCclosed hCconv hf hNoHalfLines hNoLines

-- Proof sketch: Theorem 10.4 gives continuity of a proper convex `EReal`-valued function on
-- `ri (dom f)`, so `f` is continuous on the compact set `C` and therefore has a finite upper
-- bound and a maximizer there. Since `C` is bounded it contains no nontrivial lines, and
-- Corollary 32.3.1 then yields a maximizing extreme point.
/-- Helper for Corollary 32.3.2: points of `C` lie in the effective domain, so `toReal` agrees
with `f` on `C`. -/
lemma helperForCorollary_32_3_2_effectiveDomain_and_toReal_eq_on_C
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hCri : C ⊆ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
      ∀ x ∈ C, ((f x).toReal : EReal) = f x := by
  constructor
  · intro x hxC
    -- Relative-interior points of the effective domain are already domain points.
    exact helperForTheorem_21_1_riFin_subset_C
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (hCri hxC)
  · intro x hxC
    -- Properness rules out `⊥`, and effective-domain membership rules out `⊤`.
    have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
      helperForTheorem_21_1_riFin_subset_C
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (hCri hxC)
    have hxNeTop : f x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxDom
    have hxNeBot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
    exact EReal.coe_toReal hxNeTop hxNeBot

/-- Helper for Corollary 32.3.2: on `C`, the real-valued restriction `x ↦ (f x).toReal` is
convex and continuous. -/
lemma helperForCorollary_32_3_2_convexOn_continuousOn_toReal_on_C
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hCconv : Convex ℝ C)
    (hCri : C ⊆ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    let g : (Fin n → ℝ) → ℝ := fun x => (f x).toReal
    ConvexOn ℝ C g ∧ ContinuousOn g C := by
  let g : (Fin n → ℝ) → ℝ := fun x => (f x).toReal
  have hCdom :
      C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
    (helperForCorollary_32_3_2_effectiveDomain_and_toReal_eq_on_C
      (hf := hf) (C := C) (f := f) hCri).1
  have hConvToReal :
      ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
        (fun x => (f x).toReal) :=
    convexOn_toReal_on_effectiveDomain (f := f) hf
  have hgConv : ConvexOn ℝ C g := by
    -- Restrict convexity from the full effective domain down to `C`.
    simpa [g] using hConvToReal.subset hCdom hCconv
  have hContToReal :
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => (f x).toReal)
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :=
    continuousOn_toReal_on_ri_effectiveDomain (f := f) hConvToReal
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hPreim :
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) =
        e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    ext y
    constructor
    · intro hy
      exact ⟨y, hy, by simp [e]⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
  have hContToReal' :
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin n) => (f x).toReal)
        (euclideanRelativeInterior n (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) := by
    simpa [hPreim] using hContToReal
  have hContFin :
      ContinuousOn (fun x : Fin n → ℝ => (f x).toReal)
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) := by
    -- Transport continuity from Euclidean coordinates back to `Fin n → ℝ`.
    simpa [e] using
      hContToReal'.comp
        (s := euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
        (show ContinuousOn (fun x : Fin n → ℝ => e.symm x)
            (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) from
          e.symm.continuous.continuousOn)
        (by
          intro x hx
          simpa [e] using
            (mem_euclideanRelativeInterior_fin_iff
              (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x)).1 hx)
  have hgCont : ContinuousOn g C := hContFin.mono hCri
  exact ⟨hgConv, hgCont⟩

/-- Helper for Corollary 32.3.2: a nonempty closed bounded convex set contains no nonzero
lineality vector. -/
lemma helperForCorollary_32_3_2_no_nonzero_lineality_of_bounded
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hCne : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCbdd : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) :
    ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C := by
  -- Bounded closed convex sets have trivial recession cone, hence no nonzero lineality.
  have hRec :
      Set.recessionCone C = ({0} : Set (EuclideanSpace ℝ (Fin n))) :=
    (bounded_iff_recessionCone_eq_singleton_zero (C := C) hCne hCclosed hCconv).1 hCbdd
  have hNoRecLines :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
    intro hLines
    rcases hLines with ⟨y, hyNe, hyRec⟩
    have hyZero : y = 0 := by
      have hyMemZero : y ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        simpa [hRec] using hyRec.2
      simpa [Set.mem_singleton_iff] using hyMemZero
    exact hyNe hyZero
  intro hLines
  apply hNoRecLines
  rcases hLines with ⟨y, hyNe, hyLineality⟩
  exact ⟨y, hyNe, by simpa [Set.linealitySpace] using hyLineality⟩

/-- Helper for Corollary 32.3.2: a global upper bound on `C` automatically bounds every
nontrivial half-line contained in `C`. -/
lemma helperForCorollary_32_3_2_noUnboundedHalfLines_of_global_upperBound
    {E : Type*}
    [AddMonoid E]
    [SMul ℝ E]
    {C : Set E}
    {g : E → ℝ}
    (hUpper : ∃ r : ℝ, ∀ y ∈ C, g y ≤ r) :
    NoUnboundedAboveOnHalfLines g C := by
  intro x d _hd0 hHalfLine
  rcases hUpper with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  -- Every point of the half-line lies in `C`, so the same upper bound works there.
  rintro z ⟨y, hyHalf, rfl⟩
  exact hr _ (hHalfLine hyHalf)

/-- Corollary 32.3.2: if `C` is a nonempty closed bounded convex set contained in `ri (dom f)`
for a proper convex `EReal`-valued function `f`, then `f` is bounded above on `C` by a finite
real constant and attains its maximum there at some extreme point of `C`. -/
theorem boundedAbove_and_exists_extremePoint_maximizer_on_compact_convexSet
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hCne : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCbdd : Bornology.IsBounded C)
    (hCconv : Convex ℝ C)
    (hCri : C ⊆ euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    (∃ r : ℝ, ∀ y ∈ C, f y ≤ (r : EReal)) ∧
      ∃ x, x ∈ C.extremePoints ℝ ∧ IsMaxOn f C x := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let g : (Fin n → ℝ) → ℝ := fun x => (f x).toReal
  obtain ⟨hCdom, hToRealEq⟩ :=
    helperForCorollary_32_3_2_effectiveDomain_and_toReal_eq_on_C
      (hf := hf) (C := C) (f := f) hCri
  obtain ⟨hgConv, hgCont⟩ :=
    helperForCorollary_32_3_2_convexOn_continuousOn_toReal_on_C
      (hf := hf) (C := C) (f := f) hCconv hCri
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) hCclosed hCbdd
  -- Compactness and continuity give a maximizer for the real-valued restriction `g`.
  obtain ⟨x0, hx0C, hx0Max⟩ := hCcompact.exists_isMaxOn hCne hgCont
  have hx0MaxOn : ∀ y ∈ C, g y ≤ g x0 := isMaxOn_iff.mp hx0Max
  let r : ℝ := g x0
  have hUpperG : ∀ y ∈ C, g y ≤ r := by
    intro y hyC
    simpa [r] using hx0MaxOn y hyC
  have hUpperF : ∀ y ∈ C, f y ≤ (r : EReal) := by
    intro y hyC
    -- Convert the real-valued upper bound back to `EReal` on points of `C`.
    have hyLe : g y ≤ r := hUpperG y hyC
    have hyLeEReal : (((g y : ℝ) : EReal)) ≤ (r : EReal) := by
      exact_mod_cast hyLe
    simpa [g, hToRealEq y hyC] using hyLeEReal
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let g' : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g (e x)
  have hC'ne : C'.Nonempty := by
    rcases hCne with ⟨x, hxC⟩
    exact ⟨e.symm x, ⟨x, hxC, rfl⟩⟩
  have hC'closed : IsClosed C' := by
    exact (e.symm.toHomeomorph.isClosed_image).2 hCclosed
  have hC'bounded : Bornology.IsBounded C' := by
    simpa [C'] using e.symm.lipschitz.isBounded_image hCbdd
  have hC'conv : Convex ℝ C' := by
    simpa [C'] using hCconv.linear_image e.symm.toLinearMap
  have hImageC : e '' C' = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzC, rfl⟩, rfl⟩
      simpa [e] using hzC
    · intro hxC
      exact ⟨e.symm x, ⟨x, hxC, by simp [e]⟩, by simp [e]⟩
  have hPreimageC : e.toLinearMap ⁻¹' C = C' := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hyC, rfl⟩
      simpa [e] using hyC
  have hg'Conv : ConvexOn ℝ C' g' := by
    -- Transport convexity to Euclidean coordinates through the linear equivalence.
    have hg'ConvPre :
        ConvexOn ℝ (e.toLinearMap ⁻¹' C) (g ∘ e.toLinearMap) :=
      ConvexOn.comp_linearMap (hf := hgConv) e.toLinearMap
    have hg'ConvPre' : ConvexOn ℝ (e.toLinearMap ⁻¹' C) g' := by
      simpa [g', Function.comp, e] using hg'ConvPre
    convert hg'ConvPre' using 1
    exact hPreimageC.symm
  have hUpperG' : ∀ y ∈ C', g' y ≤ r := by
    intro y hyC'
    rcases hyC' with ⟨x, hxC, rfl⟩
    simpa [g', e] using hUpperG x hxC
  have hNoHalfLinesG' : NoUnboundedAboveOnHalfLines g' C' :=
    helperForCorollary_32_3_2_noUnboundedHalfLines_of_global_upperBound
      (C := C') (g := g') ⟨r, hUpperG'⟩
  have hNoLines' :
      ¬ ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ y ∈ Set.linealitySpace C' :=
    helperForCorollary_32_3_2_no_nonzero_lineality_of_bounded
      (n := n) (C := C') hC'ne hC'closed hC'bounded hC'conv
  have hx0Max' : IsMaxOn g' C' (e.symm x0) := by
    -- The maximizer of `g` on `C` transports to a maximizer of `g'` on `C'`.
    rw [isMaxOn_iff] at hx0Max ⊢
    intro y hyC'
    rcases hyC' with ⟨z, hzC, rfl⟩
    simpa [g', e] using hx0Max z hzC
  have hExtremeMaxG' :
      ∃ x, x ∈ C'.extremePoints ℝ ∧ IsMaxOn g' C' x :=
    isMaxOn_exists_extremePoint_of_no_lines
      (n := n) (C := C') (f := g') hC'closed hC'conv hg'Conv hNoHalfLinesG' hNoLines'
      ⟨e.symm x0, by exact ⟨x0, hx0C, rfl⟩, hx0Max'⟩
  constructor
  · -- The maximizing value of `g` provides a finite upper bound for `f` on `C`.
    exact ⟨r, hUpperF⟩
  · rcases hExtremeMaxG' with ⟨x', hx'Extreme, hx'MaxG⟩
    have hImageExtreme :
        e '' C'.extremePoints ℝ = C.extremePoints ℝ := by
      calc
        e '' C'.extremePoints ℝ = (e '' C').extremePoints ℝ := by
          simpa using image_extremePoints (𝕜 := ℝ) (f := e) (s := C')
        _ = C.extremePoints ℝ := by simpa [hImageC]
    have hxExtreme : e x' ∈ C.extremePoints ℝ := by
      have : e x' ∈ e '' C'.extremePoints ℝ := ⟨x', hx'Extreme, rfl⟩
      rw [hImageExtreme] at this
      exact this
    refine ⟨e x', hxExtreme, ?_⟩
    have hxC : e x' ∈ C := extremePoints_subset hxExtreme
    -- Rewrite the `toReal` maximizer pointwise on `C` to recover an `EReal` maximizer.
    rw [isMaxOn_iff] at hx'MaxG ⊢
    intro y hyC
    have hyLe : g y ≤ g (e x') := by
      have hyC' : e.symm y ∈ C' := ⟨y, hyC, by simp [e]⟩
      simpa [g', e] using hx'MaxG (e.symm y) hyC'
    have hyLeEReal : (((g y : ℝ) : EReal)) ≤ (((g (e x') : ℝ) : EReal)) := by
      exact_mod_cast hyLe
    simpa [g, hToRealEq y hyC, hToRealEq (e x') hxC] using hyLeEReal

-- Proof sketch: Use Theorem 32.3 with the standing hypotheses kept explicit here: `f` is convex
-- on `C`, `C` is polyhedral, and `f` is bounded above on every nontrivial half-line in `C`.
-- Polyhedrality supplies the closed/finite-dimensional structure needed to reduce the supremum to
-- a finite maximizing set, so the resulting supremum is attained on `C`.
/-- Helper for Corollary 32.3.3: transporting the no-unbounded-half-lines hypothesis through the
Euclidean coordinate equivalence preserves the hypothesis. -/
lemma helperForCorollary_32_3_3_noUnboundedAboveOnHalfLines_euclideanPreimage
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ}
    (hNoHalfLines : NoUnboundedAboveOnHalfLines f C) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
      EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
    let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (e x)
    NoUnboundedAboveOnHalfLines g C' := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (e x)
  change NoUnboundedAboveOnHalfLines g C'
  intro x d hd0 hHalfLine
  have hHalfLineImage : halfLine (e x) (e d) ⊆ C := by
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have hxC' : x + t • d ∈ C' := by
      exact hHalfLine ⟨t, ht, rfl⟩
    rcases hxC' with ⟨z, hzC, hzEq⟩
    have hzEq' : z = e (x + t • d) := by
      simpa using congrArg e hzEq
    simpa [e, hzEq'] using hzC
  rcases hNoHalfLines (e x) (e d) (by
      intro hed0
      exact hd0 (e.injective hed0)) hHalfLineImage with
    ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzImage : e z ∈ halfLine (e x) (e d) := by
    rcases hz with ⟨t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    simp [e]
  simpa [g] using hr ⟨e z, hzImage, rfl⟩

/-- Helper for Corollary 32.3.3: the extreme points of the orthogonal slice from Theorem 32.3
form a finite set when the original feasible region is polyhedral. -/
lemma helperForCorollary_32_3_3_finite_sliceExtremePoints_of_polyhedral
    {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
      EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
    let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C')
    let D : Set (EuclideanSpace ℝ (Fin n)) := C' ∩ (Lᗮ : Set _)
    let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
    Set.Finite E := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.linealitySpace C')
  let D : Set (EuclideanSpace ℝ (Fin n)) := C' ∩ (Lᗮ : Set _)
  let E : Set (EuclideanSpace ℝ (Fin n)) := D.extremePoints ℝ
  change Set.Finite E
  let Df : Set (Fin n → ℝ) := e '' D
  let M : Submodule ℝ (Fin n → ℝ) := (Lᗮ).map e.toLinearMap
  have hImageC : e '' C' = C := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hzC, rfl⟩, rfl⟩
      simpa [e] using hzC
    · intro hxC
      refine ⟨e.symm x, ?_, ?_⟩
      · exact ⟨x, hxC, rfl⟩
      · simp [e]
  have hDf_eq : Df = C ∩ (M : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hyD, rfl⟩
      refine ⟨?_, ?_⟩
      · have hxImage : e y ∈ e '' C' := by
          exact ⟨y, hyD.1, rfl⟩
        simpa [hImageC] using hxImage
      · exact ⟨y, hyD.2, rfl⟩
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · have hxImage : x ∈ e '' C' := by
            simpa [hImageC] using hx.1
          rcases hxImage with ⟨y, hyC', hyEq⟩
          have hyEq' : y = e.symm x := by
            simpa using congrArg e.symm hyEq
          simpa [hyEq'] using hyC'
        · rcases hx.2 with ⟨y, hyPerp, hyEq⟩
          have hyEq' : y = e.symm x := by
            simpa using congrArg e.symm hyEq
          simpa [hyEq'] using hyPerp
      · simp [e]
  have hMpoly : IsPolyhedralConvexSet n (M : Set (Fin n → ℝ)) := by
    simpa [M] using helperForTheorem_22_6_subspaceSet_isPolyhedral (N := n) M
  have hDfpoly : IsPolyhedralConvexSet n Df := by
    have hInterPoly : IsPolyhedralConvexSet n (C ∩ (M : Set (Fin n → ℝ))) := by
      exact helperForTheorem_19_1_polyhedral_inter hCpoly hMpoly
    simpa [hDf_eq] using hInterPoly
  have hFiniteDfExtremePoint :
      Set.Finite {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) Df x} := by
    exact helperForCorollary_19_1_1_finite_extremePoints_of_polyhedral
      (n := n) (C := Df) hDfpoly
  have hFiniteDfExtreme : Set.Finite (Df.extremePoints ℝ) := by
    have hExtremeEq :
        Df.extremePoints ℝ = {x : Fin n → ℝ | IsExtremePoint (𝕜 := ℝ) Df x} := by
      ext x
      exact (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := Df) (x := x)).symm
    simpa [hExtremeEq] using hFiniteDfExtremePoint
  have hImageE : e '' E = Df.extremePoints ℝ := by
    simpa [E, Df] using image_extremePoints (𝕜 := ℝ) (f := e) (s := D)
  have hFiniteImageE : Set.Finite (e '' E) := by
    rw [hImageE]
    exact hFiniteDfExtreme
  exact Set.Finite.of_finite_image (f := e) hFiniteImageE e.injective.injOn

/-- Helper for Corollary 32.3.3: a real-valued function on a finite nonempty set attains its
maximum there. -/
lemma helperForCorollary_32_3_3_exists_mem_isMaxOn_of_finite_nonempty
    {α : Type*}
    {S : Set α}
    {g : α → ℝ}
    (hfin : S.Finite)
    (hne : S.Nonempty) :
    ∃ x, x ∈ S ∧ IsMaxOn g S x := by
  classical
  let T : Finset α := hfin.toFinset
  have hTne : T.Nonempty := by
    rcases hne with ⟨x, hxS⟩
    refine ⟨x, ?_⟩
    simpa [T] using hxS
  -- Choose an element whose value is maximal on the finite carrier `T`.
  rcases Finset.exists_max_image T g hTne with ⟨xMax, hxMaxT, hxMax⟩
  have hxMaxS : xMax ∈ S := by
    simpa [T] using hxMaxT
  refine ⟨xMax, hxMaxS, ?_⟩
  rw [isMaxOn_iff]
  intro y hyS
  exact hxMax y (by simpa [T] using hyS)

end Section32
end Chap06
