/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part13

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- An affine set in `ℝⁿ` is polyhedral. This local copy keeps the `Theorem 20.1`
binary original-route helper independent of later Section 20 files. -/
lemma helperForTheorem_20_1_affineSet_polyhedral_local
    {n : ℕ} {M : Set (Fin n → ℝ)}
    (hMaff : IsAffineSet n M) :
    IsPolyhedralConvexSet n M := by
  rcases (affineSet_iff_eq_mulVec (m := 0) (n := n) (b := (0 : Fin 0 → ℝ)) (B := 0)).2
      M hMaff with
    ⟨m, b, B, hMrepr⟩
  have hFiberEq :
      {x : Fin n → ℝ | B.mulVec x = b} =
        {x : Fin n → ℝ | ∀ i : Fin m, x ⬝ᵥ B i = b i} := by
    ext x
    constructor
    · intro hx i
      have hxi := congrArg (fun f : Fin m → ℝ => f i) hx
      simpa [Matrix.mulVec, dotProduct_comm] using hxi
    · intro hx
      ext i
      simpa [Matrix.mulVec, dotProduct_comm] using hx i
  have hFiberPoly :
      IsPolyhedralConvexSet n {x : Fin n → ℝ | B.mulVec x = b} := by
    have hEqPoly :
        IsPolyhedralConvexSet n {x : Fin n → ℝ | ∀ i : Fin m, x ⬝ᵥ B i = b i} := by
      simpa using
        (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
          n m 0 (fun i : Fin m => B i) b
          (fun j : Fin 0 => (0 : Fin n → ℝ)) (fun j : Fin 0 => (0 : ℝ)))
    simpa [hFiberEq] using hEqPoly
  simpa [hMrepr] using hFiberPoly

/-- The affine span of any subset of `ℝⁿ` is polyhedral. -/
lemma helperForTheorem_20_1_affineSpan_polyhedral_local
    {n : ℕ} (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n (affineSpan ℝ C : Set (Fin n → ℝ)) := by
  exact
    helperForTheorem_20_1_affineSet_polyhedral_local
      (n := n)
      ((isAffineSet_iff_affineSubspace n (affineSpan ℝ C : Set (Fin n → ℝ))).2
        ⟨affineSpan ℝ C, rfl⟩)

/-- Helper for Theorem 20.1: once the binary bridge `p + q` is exact and every
binary witness lifts to a full-index witness, the `0 < k < m` branch is finished
by identifying the binary infimal convolution with the full family one. -/
lemma helperForTheorem_20_1_finish_kPos_kLt_branch_from_binaryBridge
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (p q : (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hsumSplit : (fun x => ∑ i, f i x) = (fun x => p x + q x))
    (hbinaryEq :
      fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
    (hbinaryAtt :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = ⊤ ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)
    (hbinaryWitnessLift :
      ∀ {xStar y : Fin n → ℝ},
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
          fenchelConjugate n p (xStar - y) + fenchelConjugate n q y →
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  have hsumConjEqBinary :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := by
    calc
      fenchelConjugate n (fun x => ∑ i, f i x) =
          fenchelConjugate n (fun x => p x + q x) := by
            rw [hsumSplit]
      _ = infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := hbinaryEq
  have hbinaryLeFull :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
    intro xStar
    unfold infimalConvolutionFamily
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨xStarFamily, hsumFamily, rfl⟩
    have hsumConjLe :
        fenchelConjugate n (fun x => ∑ i, f i x) xStar ≤
          ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
      unfold fenchelConjugate
      refine sSup_le ?_
      rintro _ ⟨x, rfl⟩
      have hdot :
          x ⬝ᵥ xStar = ∑ i, x ⬝ᵥ xStarFamily i := by
        calc
          x ⬝ᵥ xStar = x ⬝ᵥ (∑ i, xStarFamily i) := by simpa [hsumFamily]
          _ = ∑ i, x ⬝ᵥ xStarFamily i := by
                simpa using
                  (dotProduct_sum (u := x) (s := (Finset.univ : Finset (Fin m)))
                    (v := fun i : Fin m => xStarFamily i))
      have hcoeDot :
          (((x ⬝ᵥ xStar : ℝ) : EReal)) =
            ∑ i, (((x ⬝ᵥ xStarFamily i : ℝ) : EReal)) := by
        calc
          (((x ⬝ᵥ xStar : ℝ) : EReal)) = (((∑ i, x ⬝ᵥ xStarFamily i : ℝ) : EReal)) := by
            simp [hdot]
          _ = ∑ i, (((x ⬝ᵥ xStarFamily i : ℝ) : EReal)) := by
            exact
              section16_coe_finset_sum (s := Finset.univ)
                (b := fun i : Fin m => x ⬝ᵥ xStarFamily i)
      have hbot_i : ∀ i : Fin m, f i x ≠ (⊥ : EReal) := by
        intro i
        exact (hproper i).2.2 x (by simp)
      have hneg :
          -(∑ i, f i x) = ∑ i, -(f i x) := by
        exact
          section16_neg_sum_eq_sum_neg (s := (Finset.univ : Finset (Fin m)))
            (b := fun i : Fin m => f i x) (fun i _ => hbot_i i)
      have hsumDot :
          (((x ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x) =
            ∑ i, ((((x ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x)) := by
        calc
          (((x ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x) =
              (((x ⬝ᵥ xStar : ℝ) : EReal)) + -(∑ i, f i x) := by
                simp [sub_eq_add_neg]
          _ = (∑ i, (((x ⬝ᵥ xStarFamily i : ℝ) : EReal))) + -(∑ i, f i x) := by
                simp [hcoeDot]
          _ = (∑ i, (((x ⬝ᵥ xStarFamily i : ℝ) : EReal))) + ∑ i, -(f i x) := by
                simp [hneg]
          _ = ∑ i, ((((x ⬝ᵥ xStarFamily i : ℝ) : EReal)) + -(f i x)) := by
                rw [← Finset.sum_add_distrib]
          _ = ∑ i, ((((x ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x)) := by
                simp [sub_eq_add_neg]
      have hbound_each :
          ∀ i : Fin m,
            (((x ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x) ≤
              fenchelConjugate n (f i) (xStarFamily i) := by
        intro i
        unfold fenchelConjugate
        exact le_sSup ⟨x, rfl⟩
      have hbound_sum :
          ∑ i, ((((x ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x)) ≤
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hbound_each i
      calc
        (((x ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x) =
            ∑ i, ((((x ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x)) := hsumDot
        _ ≤ ∑ i, fenchelConjugate n (f i) (xStarFamily i) := hbound_sum
    have hsumConjLe' :
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
          ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
      simpa [hsumConjEqBinary] using hsumConjLe
    exact hsumConjLe'
  have hfullLeBinary :
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ≤
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := by
    intro xStar
    rcases hbinaryAtt xStar with htop | ⟨y, hy⟩
    · rcases
        helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
          (p := p) (q := q) (xStar := xStar) htop with
        ⟨y, hy⟩
      rcases hbinaryWitnessLift hy with ⟨xStarFamily, hsumFamily, hvalueFamily⟩
      unfold infimalConvolutionFamily
      refine le_trans (sInf_le ⟨xStarFamily, hsumFamily, rfl⟩) ?_
      exact hvalueFamily.symm.le
    · rcases hbinaryWitnessLift hy with ⟨xStarFamily, hsumFamily, hvalueFamily⟩
      unfold infimalConvolutionFamily
      refine le_trans (sInf_le ⟨xStarFamily, hsumFamily, rfl⟩) ?_
      exact hvalueFamily.symm.le
  have hfullEqBinary' :
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := by
    funext xStar
    exact le_antisymm (hfullLeBinary xStar) (hbinaryLeFull xStar)
  refine ⟨?_, ?_⟩
  · calc
      fenchelConjugate n (fun x => ∑ i, f i x) =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := hsumConjEqBinary
      _ = infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := hfullEqBinary'.symm
  · intro xStar
    rcases hbinaryAtt xStar with htop | ⟨y, hy⟩
    · rcases
        helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
          (p := p) (q := q) (xStar := xStar) htop with
        ⟨y, hy⟩
      rcases hbinaryWitnessLift hy with ⟨xStarFamily, hsumFamily, hvalueFamily⟩
      refine ⟨xStarFamily, hsumFamily, ?_⟩
      calc
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
              simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hfullEqBinary'
        _ = ∑ i, fenchelConjugate n (f i) (xStarFamily i) := hvalueFamily
    · rcases hbinaryWitnessLift hy with ⟨xStarFamily, hsumFamily, hvalueFamily⟩
      refine ⟨xStarFamily, hsumFamily, ?_⟩
      calc
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
              simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hfullEqBinary'
        _ = ∑ i, fenchelConjugate n (f i) (xStarFamily i) := hvalueFamily

/-- Helper for Theorem 20.1: the missing mixed two-block binary bridge under
`dom(p) ∩ ri(dom(q)) ≠ ∅` can be closed by the textbook route.

For the non-`riInter` case, set `M = aff(dom q)` and `h = δ_M + p`. One computes
`h*` from the all-polyhedral case on `(δ_M, p)`, computes `(h + q)*` from Section 16
using `ri(dom h) ∩ ri(dom q) ≠ ∅`, and then collapses the `δ_M*`-part against `q*`.
This produces the reverse inequality and an attained split for `(p, q)`, which,
combined with the already available forward inequality, yields the exact bridge. -/
lemma helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  classical
  by_cases hriInter :
      Set.Nonempty
        (euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))
  · exact
      helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_of_riInter
        (p := p) (q := q) hproperP hproperQ hriInter
  · rcases hnonemptyDomInterRi with ⟨x0E, hx0Ppre, hx0QriPre⟩
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
      EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let x0 : Fin n → ℝ := e x0E
    let Qdom : Set (Fin n → ℝ) :=
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) q
    let QdomE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' Qdom
    have hQdomE :
        QdomE =
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' Qdom) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [e, Qdom]
      · intro hy
        refine ⟨(y : Fin n → ℝ), ?_, ?_⟩
        · simpa [Qdom] using hy
        · simp [e]
    have hx0P : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p := by
      simpa [x0, e, Set.mem_preimage] using hx0Ppre
    have hx0Qri_intrE :
        e.symm x0 ∈ intrinsicInterior ℝ QdomE := by
      have hx0QriE :
          e.symm x0 ∈ euclideanRelativeInterior n QdomE := by
        simpa [x0, e, hQdomE, Qdom, Set.mem_preimage] using hx0QriPre
      simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := QdomE)] using hx0QriE
    have hx0Q : x0 ∈ Qdom := by
      have hx0QmemE : e.symm x0 ∈ QdomE := intrinsicInterior_subset hx0Qri_intrE
      rcases hx0QmemE with ⟨z, hz, hzx⟩
      have hzEq : z = x0 := e.symm.injective hzx
      simpa [hzEq] using hz
    letI : Nonempty ↥(affineSpan ℝ Qdom) := ⟨⟨x0, subset_affineSpan (k := ℝ) (s := Qdom) hx0Q⟩⟩
    have hriQdomE :
        intrinsicInterior ℝ QdomE = e.symm '' intrinsicInterior ℝ Qdom := by
      simpa [QdomE] using
        (ContinuousLinearEquiv.image_intrinsicInterior (e := e.symm) (s := Qdom))
    have hx0Qri :
        x0 ∈ intrinsicInterior ℝ Qdom := by
      have hx0Img :
          e.symm x0 ∈ e.symm '' intrinsicInterior ℝ Qdom := by
        simpa [hriQdomE] using hx0Qri_intrE
      rcases hx0Img with ⟨z, hz, hzx⟩
      have hzEq : z = x0 := e.symm.injective hzx
      simpa [hzEq] using hz
    let M : AffineSubspace ℝ (Fin n → ℝ) :=
      affineSpan ℝ Qdom
    let indM : (Fin n → ℝ) → EReal := indicatorFunction (M : Set (Fin n → ℝ))
    let h : (Fin n → ℝ) → EReal := fun x => indM x + p x
    have hx0M : x0 ∈ (M : Set (Fin n → ℝ)) := by
      exact subset_affineSpan (k := ℝ) (s := Qdom) hx0Q
    have hdomQsubsetM :
        Qdom ⊆ (M : Set (Fin n → ℝ)) := by
      intro x hx
      exact subset_affineSpan (k := ℝ) (s := Qdom) hx
    have hMpolySet : IsPolyhedralConvexSet n (M : Set (Fin n → ℝ)) := by
      simpa [M] using
        helperForTheorem_20_1_affineSpan_polyhedral_local
          (n := n) Qdom
    have hpolyIndM : IsPolyhedralConvexFunction n indM := by
      simpa [indM] using
        helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hMpolySet
    have hproperIndM :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) indM := by
      have hMconv : Convex ℝ (M : Set (Fin n → ℝ)) := AffineSubspace.convex (Q := M)
      have hMne : ((M : Set (Fin n → ℝ))).Nonempty := by
        exact ⟨x0, hx0M⟩
      simpa [indM] using
        section16_properConvexFunctionOn_indicatorFunction_univ hMconv hMne
    have hindM_add_q_eq_q :
        (fun x => indM x + q x) = q := by
      funext x
      by_cases hxM : x ∈ (M : Set (Fin n → ℝ))
      · simp [indM, indicatorFunction, hxM]
      · have hxQtop : q x = (⊤ : EReal) := by
          by_contra hxQtop
          have hxDomQ : x ∈ Qdom := by
            have hxlt : q x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxQtop
            simpa [Qdom, effectiveDomain_eq] using
              (show x ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ q y < (⊤ : EReal)} from
                ⟨by simp, hxlt⟩)
          exact hxM (hdomQsubsetM hxDomQ)
        simp [indM, indicatorFunction, hxM, hxQtop]
    have hsumHQ_eq :
        (fun x => h x + q x) = (fun x => p x + q x) := by
      funext x
      by_cases hxM : x ∈ (M : Set (Fin n → ℝ))
      · calc
          h x + q x = (((0 : EReal) + p x) + q x) := by
            have hind : indM x = (0 : EReal) := by simp [indM, indicatorFunction, hxM]
            simp [h, hind, add_assoc]
          _ = p x + q x := by simp
      · have hxQtop : q x = (⊤ : EReal) := by
          by_contra hxQtop
          have hxDomQ : x ∈ Qdom := by
            have hxlt : q x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxQtop
            simpa [Qdom, effectiveDomain_eq] using
              (show x ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ q y < (⊤ : EReal)} from
                ⟨by simp, hxlt⟩)
          exact hxM (hdomQsubsetM hxDomQ)
        have hhTop : h x = (⊤ : EReal) := by
          have hpbot : p x ≠ (⊥ : EReal) := hproperP.2.2 x (by simp)
          have hind : indM x = (⊤ : EReal) := by simp [indM, indicatorFunction, hxM]
          simpa [h, hind] using (EReal.top_add_of_ne_bot (x := p x) hpbot)
        have hqbot : q x ≠ (⊥ : EReal) := hproperQ.2.2 x (by simp)
        have hpbot : p x ≠ (⊥ : EReal) := hproperP.2.2 x (by simp)
        calc
          h x + q x = (⊤ : EReal) + q x := by rw [hhTop]
          _ = (⊤ : EReal) := by
                simpa [hxQtop] using (EReal.top_add_of_ne_bot (x := q x) hqbot)
          _ = p x + q x := by
                simpa [hxQtop] using (EReal.add_top_of_ne_bot (x := p x) hpbot).symm
    let fH : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases indM (fun _ => p) i
    have hfH0 : fH 0 = indM := by
      funext x
      change Fin.cases indM (fun _ => p) (⟨0, by decide⟩ : Fin 2) x = indM x
      rfl
    have hfH1 : fH 1 = p := by
      funext x
      change Fin.cases indM (fun _ => p) (⟨1, by decide⟩ : Fin 2) x = p x
      rfl
    have hpolyH : ∀ i : Fin 2, IsPolyhedralConvexFunction n (fH i) := by
      intro i
      fin_cases i
      · simpa [fH] using hpolyIndM
      · simpa [fH] using hpolyP
    have hproperHFamily :
        ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fH i) := by
      intro i
      fin_cases i
      · simpa [fH] using hproperIndM
      · simpa [fH] using hproperP
    have hdomHFamily :
        Set.Nonempty
          (⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fH i)) := by
      refine ⟨x0, Set.mem_iInter.2 ?_⟩
      intro i
      fin_cases i
      · simpa [fH, indM, effectiveDomain_indicatorFunction_eq, Set.mem_preimage] using hx0M
      · simpa [fH] using hx0P
    have hHstarEqFamily :
        fenchelConjugate n (fun x => ∑ i : Fin 2, fH i x) =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fH i)) := by
      exact
        fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
          (f := fH) hpolyH hproperHFamily hdomHFamily
    have hHstarAtt :
        ∀ zStar : Fin n → ℝ,
          ∃ u y1 : Fin n → ℝ,
            u + y1 = zStar ∧
              fenchelConjugate n h zStar =
                fenchelConjugate n indM u + fenchelConjugate n p y1 := by
      intro zStar
      rcases
          infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
            (f := fH) (hpoly := hpolyH) (hproper := hproperHFamily) (hdom := hdomHFamily)
            (hmPos := by decide) (xStar := zStar) with
        ⟨xStarFamily, hsum, hval⟩
      refine ⟨xStarFamily 0, xStarFamily 1, ?_, ?_⟩
      · simpa [Fin.sum_univ_two] using hsum
      · calc
          fenchelConjugate n h zStar =
              fenchelConjugate n (fun x => ∑ i : Fin 2, fH i x) zStar := by
                have hsumH : h = fun x => ∑ i : Fin 2, fH i x := by
                  funext x
                  rw [Fin.sum_univ_two, hfH0, hfH1]
                rw [hsumH]
          _ = infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fH i)) zStar := by
                exact congrArg (fun g : (Fin n → ℝ) → EReal => g zStar) hHstarEqFamily
          _ = ∑ i : Fin 2, fenchelConjugate n (fH i) (xStarFamily i) := by
                simpa using hval
          _ = fenchelConjugate n indM (xStarFamily 0) +
                fenchelConjugate n p (xStarFamily 1) := by
                rw [Fin.sum_univ_two]
                change fenchelConjugate n indM (xStarFamily 0) +
                    fenchelConjugate n (fH 1) (xStarFamily 1) =
                  fenchelConjugate n indM (xStarFamily 0) +
                    fenchelConjugate n p (xStarFamily 1)
                rw [hfH1]
    have hproperH :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
      have hsumExists :
          ∃ x : Fin n → ℝ, (∑ i : Fin 2, fH i x) ≠ (⊤ : EReal) := by
        refine ⟨x0, ?_⟩
        have hx0PnotTop :
            p x0 ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := p) hx0P
        simpa [fH, Fin.sum_univ_two, indM, indicatorFunction, hx0M] using hx0PnotTop
      simpa [h, fH, Fin.sum_univ_two] using
        (properConvexFunctionOn_sum_of_exists_ne_top (f := fH) hproperHFamily hsumExists)
    have hdomH_eq :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) h =
          (M : Set (Fin n → ℝ)) ∩ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p := by
      ext x
      constructor
      · intro hx
        have hhNotTop :
            h x ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := h) hx
        have hxM : x ∈ (M : Set (Fin n → ℝ)) := by
          by_contra hxM
          have hhTop : h x = (⊤ : EReal) := by
            have hpbot : p x ≠ (⊥ : EReal) := hproperP.2.2 x (by simp)
            have hind : indM x = (⊤ : EReal) := by simp [indM, indicatorFunction, hxM]
            simpa [h, hind] using (EReal.top_add_of_ne_bot (x := p x) hpbot)
          exact hhNotTop hhTop
        have hxP : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p := by
          have hpNotTop : p x ≠ (⊤ : EReal) := by
            intro hpTop
            have hhTop : h x = (⊤ : EReal) := by
              have hind : indM x = (0 : EReal) := by simp [indM, indicatorFunction, hxM]
              show indM x + p x = (⊤ : EReal)
              rw [hind, zero_add, hpTop]
            exact hhNotTop hhTop
          have hplt : p x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hpNotTop
          simpa [effectiveDomain_eq] using
            (show x ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ p y < (⊤ : EReal)} from
              ⟨by simp, hplt⟩)
        exact ⟨hxM, hxP⟩
      · rintro ⟨hxM, hxP⟩
        have hpNotTop :
            p x ≠ (⊤ : EReal) :=
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := p) hxP
        have hhNotTop : h x ≠ (⊤ : EReal) := by
          have hind : indM x = (0 : EReal) := by simp [indM, indicatorFunction, hxM]
          have hhEq : h x = p x := by
            show indM x + p x = p x
            rw [hind, zero_add]
          rw [hhEq]
          exact hpNotTop
        have hhlt : h x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hhNotTop
        simpa [effectiveDomain_eq] using
          (show x ∈ {y : Fin n → ℝ | y ∈ Set.univ ∧ h y < (⊤ : EReal)} from
            ⟨by simp, hhlt⟩)
    have hriInterHQ :
        Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                Qdom)) := by
      let C : Set (Fin n → ℝ) := (M : Set (Fin n → ℝ)) ∩ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p
      let CE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
      letI : Nonempty ↥(affineSpan ℝ C) := ⟨⟨x0, subset_affineSpan (k := ℝ) (s := C) ⟨hx0M, hx0P⟩⟩⟩
      letI : Nonempty ↥(affineSpan ℝ CE) := by
        refine ⟨⟨e.symm x0, ?_⟩⟩
        exact subset_affineSpan (k := ℝ) (s := CE) ⟨x0, ⟨hx0M, hx0P⟩, by simp [e]⟩
      letI : Nonempty ↥(affineSpan ℝ QdomE) := by
        refine ⟨⟨e.symm x0, ?_⟩⟩
        exact subset_affineSpan (k := ℝ) (s := QdomE) ⟨x0, hx0Q, by simp [e]⟩
      have hCE :
          intrinsicInterior ℝ CE = e.symm '' intrinsicInterior ℝ C := by
        simpa [CE] using
          (ContinuousLinearEquiv.image_intrinsicInterior (e := e.symm) (s := C))
      have hCE_pre :
          CE =
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa [e]
        · intro hy
          refine ⟨(y : Fin n → ℝ), ?_, ?_⟩
          · simpa using hy
          · simp [e]
      have hCconv : Convex ℝ C := by
        exact (AffineSubspace.convex (Q := M)).inter
          (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := p) hproperP.1)
      have hCne : C.Nonempty := ⟨x0, hx0M, hx0P⟩
      obtain ⟨U, hUopen, hUeq⟩ :=
        exists_isOpen_inter_affineSpan_eq_intrinsicInterior n Qdom
      have hx0U : x0 ∈ U := by
        have hx0riQ' :
            x0 ∈ U ∩ (affineSpan ℝ Qdom : Set (Fin n → ℝ)) := by
          simpa [M, hUeq] using hx0Qri
        exact hx0riQ'.1
      have hx0C : x0 ∈ C := ⟨hx0M, hx0P⟩
      have hx0clI : x0 ∈ closure (intrinsicInterior ℝ C) := by
        have hclosure :
            closure C ⊆ closure (intrinsicInterior ℝ C) := by
          simpa using
            closure_subset_closure_intrinsicInterior_of_convex_nonempty
              (n := n) (C := C) hCconv hCne
        exact hclosure (subset_closure hx0C)
      have hUI : (U ∩ intrinsicInterior ℝ C).Nonempty := by
        exact
          (mem_closure_iff_nhds.1 hx0clI) U
            (IsOpen.mem_nhds hUopen hx0U)
      rcases hUI with ⟨y, hyU, hyriC⟩
      have hyC : y ∈ C := intrinsicInterior_subset hyriC
      have hyQri :
          y ∈ intrinsicInterior ℝ Qdom := by
        have hyUM :
            y ∈ U ∩ (affineSpan ℝ Qdom : Set (Fin n → ℝ)) := by
          exact ⟨hyU, by simpa [M] using hyC.1⟩
        simpa [hUeq] using hyUM
      have hyriCE :
          e.symm y ∈ intrinsicInterior ℝ CE := by
        have hyImg : e.symm y ∈ e.symm '' intrinsicInterior ℝ C := by
          exact ⟨y, hyriC, by simp [e]⟩
        simpa [hCE] using hyImg
      have hyriQdomE :
          e.symm y ∈ intrinsicInterior ℝ QdomE := by
        have hyImg : e.symm y ∈ e.symm '' intrinsicInterior ℝ Qdom := by
          exact ⟨y, hyQri, by simp [e]⟩
        simpa [hriQdomE] using hyImg
      have hyriCE' :
          e.symm y ∈ euclideanRelativeInterior n CE := by
        simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)] using hyriCE
      have hyriQdomE' :
          e.symm y ∈ euclideanRelativeInterior n QdomE := by
        simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := QdomE)] using hyriQdomE
      refine ⟨e.symm y, ?_, ?_⟩
      · simpa [Set.mem_preimage, hdomH_eq, C, CE, hCE_pre] using hyriCE'
      · simpa [Set.mem_preimage, Qdom, QdomE, hQdomE] using hyriQdomE'
    have hHQBridge :
        (fenchelConjugate n (fun x => h x + q x) =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q)) ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar =
                fenchelConjugate n h (xStar - y) + fenchelConjugate n q y) := by
      exact
        helperForTheorem_20_1_binary_exact_topOrAttained_polyLeft_domRi_via_section16
          (p := h) (q := q) hproperH hproperQ hriInterHQ
    have hriInterIndQ :
        Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) indM)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                Qdom)) := by
      refine ⟨x0E, ?_, ?_⟩
      · have hx0MEri :
            x0E ∈ euclideanRelativeInterior n
              (((M.map e.symm.toAffineMap : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
                Set (EuclideanSpace ℝ (Fin n)))) := by
          have hx0ME :
              x0E ∈
                ((M.map e.symm.toAffineMap : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
                  Set (EuclideanSpace ℝ (Fin n))) := by
            have hx0Map :
                e.symm x0 ∈
                  ((M.map e.symm.toAffineMap :
                    AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
                    Set (EuclideanSpace ℝ (Fin n))) := by
              exact
                (AffineSubspace.mem_map_iff_mem_of_injective
                  (f := e.symm.toAffineMap) (x := x0) (s := M)
                  (hf := e.symm.injective)).2 hx0M
            simpa [x0, e] using hx0Map
          rw [euclideanRelativeInterior_affineSubspace_eq]
          exact hx0ME
        have hMapEq :
            ((fun a : Fin n → ℝ => e.symm a) '' (M : Set (Fin n → ℝ))) =
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' (M : Set (Fin n → ℝ))) := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            simpa [e]
          · intro hy
            refine ⟨(y : Fin n → ℝ), ?_, ?_⟩
            · simpa using hy
            · simp [e]
        simpa [indM, effectiveDomain_indicatorFunction_eq, Set.mem_preimage, hMapEq] using hx0MEri
      · simpa [Qdom] using hx0QriPre
    have hIndQEq :
        fenchelConjugate n q =
          infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) := by
      calc
        fenchelConjugate n q =
            fenchelConjugate n (fun x => indM x + q x) := by
              simpa [hindM_add_q_eq_q]
        _ =
            infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) := by
              exact
                (helperForTheorem_20_1_binary_exact_topOrAttained_polyLeft_domRi_via_section16
                  (p := indM) (q := q) hproperIndM hproperQ hriInterIndQ).1
    have hnonemptyDomInterRi' :
        Set.Nonempty
          (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
      exact ⟨x0E, hx0Ppre, hx0QriPre⟩
    have hforwardLe :
        fenchelConjugate n (fun x => p x + q x) ≤
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := by
      exact
        helperForTheorem_20_1_binary_conjugate_le_infimalConvolution_of_polyLeft_domRi
          (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi'
    have hIndQCandidate :
        ∀ y y2 : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) y2 ≤
            fenchelConjugate n indM (y2 - y) + fenchelConjugate n q y := by
      intro y y2
      unfold infimalConvolution
      refine sInf_le ?_
      refine ⟨y2 - y, y, ?_, rfl⟩
      ext i
      simp
    have hInfCandidate :
        ∀ xStar y2 : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
            fenchelConjugate n p (xStar - y2) + fenchelConjugate n q y2 := by
      intro xStar y2
      unfold infimalConvolution
      refine sInf_le ?_
      refine ⟨xStar - y2, y2, ?_, rfl⟩
      ext i
      simp
    have hswapAdd :
        ∀ a b c : EReal, a + (b + c) = b + a + c := by
      intro a b c
      rw [← add_assoc, add_comm a b]
    have hreverseLe :
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x) := by
      intro xStar
      rcases hHQBridge.2 xStar with htop | ⟨y, hyInf⟩
      · rcases
          helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
            (p := h) (q := q) (xStar := xStar) htop with
          ⟨y, hy⟩
        have hyEq :
            fenchelConjugate n (fun x => p x + q x) xStar =
              fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
          calc
            fenchelConjugate n (fun x => p x + q x) xStar =
                fenchelConjugate n (fun x => h x + q x) xStar := by
                  rw [hsumHQ_eq]
            _ = infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hHQBridge.1
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := hy
        rcases hHstarAtt (xStar - y) with ⟨u, y1, huSum, huVal⟩
        let y2 : Fin n → ℝ := u + y
        have hy2sub : y2 - y = u := by
          ext i
          simp [y2]
        have hy1split : xStar - y2 = y1 := by
          ext i
          have hcoord := congrArg (fun v : Fin n → ℝ => v i) huSum
          simp [y2] at hcoord ⊢
          linarith
        have hqLe :
            fenchelConjugate n q y2 ≤
              fenchelConjugate n indM u + fenchelConjugate n q y := by
          calc
            fenchelConjugate n q y2 =
                infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) y2 := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g y2) hIndQEq
            _ ≤ fenchelConjugate n indM (y2 - y) + fenchelConjugate n q y := by
                  exact hIndQCandidate y y2
            _ = fenchelConjugate n indM u + fenchelConjugate n q y := by
                  simp [hy2sub]
        have hCandidateLe :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              fenchelConjugate n (fun x => p x + q x) xStar := by
          calc
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
                fenchelConjugate n p y1 +
                  (fenchelConjugate n indM u + fenchelConjugate n q y) := by
                    gcongr
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
                  rw [huVal]
                  simpa using
                    hswapAdd (fenchelConjugate n p y1)
                      (fenchelConjugate n indM u) (fenchelConjugate n q y)
            _ = fenchelConjugate n (fun x => p x + q x) xStar := hyEq.symm
        have hInfLe :
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
              fenchelConjugate n p y1 + fenchelConjugate n q y2 := by
          simpa [hy1split] using (hInfCandidate xStar y2)
        exact le_trans hInfLe hCandidateLe
      · have hyEq :
            fenchelConjugate n (fun x => p x + q x) xStar =
              fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
          calc
            fenchelConjugate n (fun x => p x + q x) xStar =
                fenchelConjugate n (fun x => h x + q x) xStar := by
                  rw [hsumHQ_eq]
            _ = infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hHQBridge.1
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := hyInf
        rcases hHstarAtt (xStar - y) with ⟨u, y1, huSum, huVal⟩
        let y2 : Fin n → ℝ := u + y
        have hy2sub : y2 - y = u := by
          ext i
          simp [y2]
        have hy1split : xStar - y2 = y1 := by
          ext i
          have hcoord := congrArg (fun v : Fin n → ℝ => v i) huSum
          simp [y2] at hcoord ⊢
          linarith
        have hqLe :
            fenchelConjugate n q y2 ≤
              fenchelConjugate n indM u + fenchelConjugate n q y := by
          calc
            fenchelConjugate n q y2 =
                infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) y2 := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g y2) hIndQEq
            _ ≤ fenchelConjugate n indM (y2 - y) + fenchelConjugate n q y := by
                  exact hIndQCandidate y y2
            _ = fenchelConjugate n indM u + fenchelConjugate n q y := by
                  simp [hy2sub]
        have hCandidateLe :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              fenchelConjugate n (fun x => p x + q x) xStar := by
          calc
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
                fenchelConjugate n p y1 +
                  (fenchelConjugate n indM u + fenchelConjugate n q y) := by
                    gcongr
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
                  rw [huVal]
                  simpa using
                    hswapAdd (fenchelConjugate n p y1)
                      (fenchelConjugate n indM u) (fenchelConjugate n q y)
            _ = fenchelConjugate n (fun x => p x + q x) xStar := hyEq.symm
        have hInfLe :
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
              fenchelConjugate n p y1 + fenchelConjugate n q y2 := by
          simpa [hy1split] using (hInfCandidate xStar y2)
        exact le_trans hInfLe hCandidateLe
    have hUniversal :
        ∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y := by
      intro xStar
      rcases hHQBridge.2 xStar with htop | ⟨y, hyInf⟩
      · rcases
          helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
            (p := h) (q := q) (xStar := xStar) htop with
          ⟨y, hy⟩
        have hyEq :
            fenchelConjugate n (fun x => p x + q x) xStar =
              fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
          calc
            fenchelConjugate n (fun x => p x + q x) xStar =
                fenchelConjugate n (fun x => h x + q x) xStar := by
                  rw [hsumHQ_eq]
            _ = infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hHQBridge.1
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := hy
        rcases hHstarAtt (xStar - y) with ⟨u, y1, huSum, huVal⟩
        let y2 : Fin n → ℝ := u + y
        have hy2sub : y2 - y = u := by
          ext i
          simp [y2]
        have hy1split : xStar - y2 = y1 := by
          ext i
          have hcoord := congrArg (fun v : Fin n → ℝ => v i) huSum
          simp [y2] at hcoord ⊢
          linarith
        have hqLe :
            fenchelConjugate n q y2 ≤
              fenchelConjugate n indM u + fenchelConjugate n q y := by
          calc
            fenchelConjugate n q y2 =
                infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) y2 := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g y2) hIndQEq
            _ ≤ fenchelConjugate n indM (y2 - y) + fenchelConjugate n q y := by
                  exact hIndQCandidate y y2
            _ = fenchelConjugate n indM u + fenchelConjugate n q y := by
                  simp [hy2sub]
        have hCandidateLe :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              fenchelConjugate n (fun x => p x + q x) xStar := by
          calc
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
                fenchelConjugate n p y1 +
                  (fenchelConjugate n indM u + fenchelConjugate n q y) := by
                    gcongr
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
                  rw [huVal]
                  simpa using
                    hswapAdd (fenchelConjugate n p y1)
                      (fenchelConjugate n indM u) (fenchelConjugate n q y)
            _ = fenchelConjugate n (fun x => p x + q x) xStar := hyEq.symm
        have hInfLe :
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
              fenchelConjugate n p y1 + fenchelConjugate n q y2 := by
          simpa [hy1split] using (hInfCandidate xStar y2)
        have hCandidateLeInf :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
          exact le_trans hCandidateLe (hforwardLe xStar)
        refine ⟨y2, ?_⟩
        calc
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p y1 + fenchelConjugate n q y2 :=
                le_antisymm hInfLe hCandidateLeInf
          _ = fenchelConjugate n p (xStar - y2) + fenchelConjugate n q y2 := by
                rw [← hy1split]
      · rcases hHstarAtt (xStar - y) with ⟨u, y1, huSum, huVal⟩
        let y2 : Fin n → ℝ := u + y
        have hy2sub : y2 - y = u := by
          ext i
          simp [y2]
        have hy1split : xStar - y2 = y1 := by
          ext i
          have hcoord := congrArg (fun v : Fin n → ℝ => v i) huSum
          simp [y2] at hcoord ⊢
          linarith
        have hyEq :
            fenchelConjugate n (fun x => p x + q x) xStar =
              fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
          calc
            fenchelConjugate n (fun x => p x + q x) xStar =
                fenchelConjugate n (fun x => h x + q x) xStar := by
                  rw [hsumHQ_eq]
            _ = infimalConvolution (fenchelConjugate n h) (fenchelConjugate n q) xStar := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hHQBridge.1
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := hyInf
        have hqLe :
            fenchelConjugate n q y2 ≤
              fenchelConjugate n indM u + fenchelConjugate n q y := by
          calc
            fenchelConjugate n q y2 =
                infimalConvolution (fenchelConjugate n indM) (fenchelConjugate n q) y2 := by
                  exact congrArg (fun g : (Fin n → ℝ) → EReal => g y2) hIndQEq
            _ ≤ fenchelConjugate n indM (y2 - y) + fenchelConjugate n q y := by
                  exact hIndQCandidate y y2
            _ = fenchelConjugate n indM u + fenchelConjugate n q y := by
                  simp [hy2sub]
        have hCandidateLe :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              fenchelConjugate n (fun x => p x + q x) xStar := by
          calc
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
                fenchelConjugate n p y1 +
                  (fenchelConjugate n indM u + fenchelConjugate n q y) := by
                    gcongr
            _ = fenchelConjugate n h (xStar - y) + fenchelConjugate n q y := by
                  rw [huVal]
                  simpa using
                    hswapAdd (fenchelConjugate n p y1)
                      (fenchelConjugate n indM u) (fenchelConjugate n q y)
            _ = fenchelConjugate n (fun x => p x + q x) xStar := hyEq.symm
        have hInfLe :
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≤
              fenchelConjugate n p y1 + fenchelConjugate n q y2 := by
          simpa [hy1split] using (hInfCandidate xStar y2)
        have hCandidateLeInf :
            fenchelConjugate n p y1 + fenchelConjugate n q y2 ≤
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
          exact le_trans hCandidateLe (hforwardLe xStar)
        refine ⟨y2, ?_⟩
        calc
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p y1 + fenchelConjugate n q y2 :=
                le_antisymm hInfLe hCandidateLeInf
          _ = fenchelConjugate n p (xStar - y2) + fenchelConjugate n q y2 := by
                rw [← hy1split]
    have hreverseNeTop :
        (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
      refine ⟨hreverseLe, ?_⟩
      intro xStar _hneTop
      exact hUniversal xStar
    exact
      helperForTheorem_20_1_exact_topOrAttained_of_forward_reverse_and_neTopAttainment
        (p := p) (q := q) hforwardLe hreverseNeTop.1 hreverseNeTop.2

/-- Helper for Theorem 20.1: in the branch `0 < k < m`, the head/tail filtered
split yields a binary bridge (`p + q`), whose exact/top-or-attained package and
blockwise attainment lift close the full-family conclusion. -/
lemma helperForTheorem_20_1_case_kPos_kLt_from_binaryBridge
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hk : k ≤ m)
    (hmPos : 0 < m)
    (hkPos : 0 < k)
    (hklt : k < m)
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // k ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  classical
  let p : (Fin n → ℝ) → EReal :=
    fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x
  let q : (Fin n → ℝ) → EReal :=
    fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x
  have hclosureEq :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        convexFunctionClosure
          (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) :=
    helperForTheorem_20_1_closure_refinement_of_mixed_assumptions
      (f := f) hpoly hproper hdom_ri
  have hsumSplit : (fun x => ∑ i, f i x) = (fun x => p x + q x) := by
    funext x
    have hfilterTailEq :
        Finset.univ.filter (fun i : Fin m => ¬ i.1 < k) =
          Finset.univ.filter (fun i : Fin m => k ≤ i.1) := by
      ext i
      simp [Nat.not_lt]
    calc
      ∑ i : Fin m, f i x =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), f i x) := by
            simpa using
              (Finset.sum_filter_add_sum_filter_not
                (s := (Finset.univ : Finset (Fin m)))
                (p := fun i : Fin m => i.1 < k)
                (f := fun i : Fin m => f i x)).symm
      _ =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) := by
            rw [hfilterTailEq]
      _ = p x + q x := by
            simp [p, q]
  have htwoBlockData :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q ∧
      (∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
            euclideanRelativeInterior n
              ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) := by
    simpa [p, q] using
      helperForTheorem_20_1_twoBlock_proper_and_domRiWitness_of_mixed_hypothesis
        (f := f) (hproper := hproper) (hdom_ri := hdom_ri)
  have hproperP :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p := htwoBlockData.1
  have hproperQ :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := htwoBlockData.2.1
  have hdomRiWitnessBlock :
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
            euclideanRelativeInterior n
              ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    htwoBlockData.2.2
  have hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    helperForTheorem_20_1_nonempty_preimageDom_inter_riPreimage_of_domRiWitnessBlock
      (p := p) (q := q) hdomRiWitnessBlock
  rcases hdom_ri with ⟨x0E, hx0E⟩
  have hdomHead :
      Set.Nonempty
        (⋂ i : {i : Fin m // i.1 < k},
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)) := by
    refine ⟨(x0E : Fin n → ℝ), Set.mem_iInter.2 ?_⟩
    intro i
    have hLeft :
        x0E ∈
          ⋂ j : {j : Fin m // j.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.1
    have hxPre :
        x0E ∈
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)) := by
      simpa using (Set.mem_iInter.mp hLeft) i
    simpa [Set.mem_preimage] using hxPre
  have hriTail :
      Set.Nonempty
        (⋂ i : {i : Fin m // k ≤ i.1},
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1))) := by
    refine ⟨x0E, Set.mem_iInter.2 ?_⟩
    intro i
    have hRight :
        x0E ∈
          ⋂ j : {j : Fin m // k ≤ j.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.2
    simpa using (Set.mem_iInter.mp hRight) i
  have hpolyMem :
      ∀ i : Fin m, i ∈ ({i : Fin m | i.1 < k} : Set (Fin m)) →
        IsPolyhedralConvexFunction n (f i) := by
    intro i hi
    exact hpoly i hi
  have hdomIpoly :
      Set.Nonempty
        (⋂ i : {i : Fin m // i ∈ ({i : Fin m | i.1 < k} : Set (Fin m))},
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)) := by
    simpa using hdomHead
  let i0 : Fin m := ⟨0, hmPos⟩
  have hi0 : i0 ∈ ({i : Fin m | i.1 < k} : Set (Fin m)) := by
    simpa [i0] using hkPos
  have hIpolyNonempty : ({i : Fin m | i.1 < k} : Set (Fin m)) ≠ ∅ := by
    exact Set.nonempty_iff_ne_empty.mp ⟨i0, hi0⟩
  have hpolyP :
      IsPolyhedralConvexFunction n p := by
    simpa [p] using
      helperForTheorem_20_1_polyhedral_filteredBlock_of_membership_polyhedral
        (f := f) (Ipoly := ({i : Fin m | i.1 < k} : Set (Fin m))) (hpolyMem := hpolyMem)
        (hproper := hproper) (hdom := hdomIpoly)
        (hIpolyNonempty := hIpolyNonempty)
  have hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = ⊤ ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    _root_.helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  have hheadBlockAttained :
      ∀ xHead : Fin n → ℝ,
        ∃ headFamily : {i : Fin m // i.1 < k} → Fin n → ℝ,
          (∑ i, headFamily i) = xHead ∧
            fenchelConjugate n p xHead =
              ∑ i : {i : Fin m // i.1 < k},
                fenchelConjugate n (f i.1) (headFamily i) := by
    intro xHead
    simpa [p] using
      helperForTheorem_20_1_headBlock_conjugate_attained_by_headFamily
        (f := f) (hk := hk) (hkPos := hkPos) hpoly hproper hdomHead xHead
  have htailBlockAttained :
      ∀ xTail : Fin n → ℝ,
        ∃ tailFamily : {i : Fin m // k ≤ i.1} → Fin n → ℝ,
          (∑ i, tailFamily i) = xTail ∧
            fenchelConjugate n q xTail =
              ∑ i : {i : Fin m // k ≤ i.1},
                fenchelConjugate n (f i.1) (tailFamily i) := by
    intro xTail
    simpa [q] using
      helperForTheorem_20_1_tailBlock_conjugate_attained_by_tailFamily
        (f := f) (hklt := hklt) hproper hriTail xTail
  have hbinaryWitnessLift :
      ∀ {xStar y : Fin n → ℝ},
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
          fenchelConjugate n p (xStar - y) + fenchelConjugate n q y →
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
    intro xStar y hbinaryValue
    exact
      helperForTheorem_20_1_fullFamily_attained_of_binarySplit_and_blockAttainment
        (f := f) (p := p) (q := q) hheadBlockAttained htailBlockAttained hbinaryValue
  exact
    _root_.helperForTheorem_20_1_finish_kPos_kLt_branch_from_binaryBridge
      (f := f) (p := p) (q := q) (hproper := hproper)
      hsumSplit hbinaryBridge.1 hbinaryBridge.2 hbinaryWitnessLift

/-- Theorem 20.1: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`, assume
`f₁, …, fₖ` are polyhedral, and assume
`0 < m`, and assume
`(⋂_{i < k} dom fᵢ) ∩ (⋂_{k ≤ i < m} ri (dom fᵢ))` is nonempty.
Then `(f₁ + ⋯ + fₘ)^* = (f₁^* □ ⋯ □ fₘ^*)`, and for each `x*` the infimum
defining `(f₁^* □ ⋯ □ fₘ^*)(x*)` is attained by some decomposition
`x* = ∑ i xᵢ*`. -/
theorem fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hk : k ≤ m)
    (hmPos : 0 < m)
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // k ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  by_cases hk0 : k = 0
  · exact
      helperForTheorem_20_1_case_kEqZero_from_section16
        (f := f) (hk0 := hk0) (hmPos := hmPos)
        (hproper := hproper) (hdom_ri := hdom_ri)
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkm : k = m
    · exact
        helperForTheorem_20_1_case_kEqm_from_allPoly_refinement
          (f := f) (hkm := hkm) (hmPos := hmPos)
          (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)
    · have hklt : k < m := lt_of_le_of_ne hk hkm
      exact
        helperForTheorem_20_1_case_kPos_kLt_from_binaryBridge
          (f := f) (hk := hk) (hmPos := hmPos) (hkPos := hkPos) (hklt := hklt)
          (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)

/-- Corollary 20.1.1: Let `f₁, …, fₘ` be closed proper convex functions on `ℝⁿ`,
`f₁, …, f_k` are polyhedral. If

`dom f₁^* ∩ ⋯ ∩ dom f_k^* ∩ ri (dom f_{k+1}^*) ∩ ⋯ ∩ ri (dom fₘ^*) ≠ ∅`,

and `0 < m`,

then `f₁ □ ⋯ □ fₘ` is closed proper convex, and for every `x` the infimum in the
definition of `f₁ □ ⋯ □ fₘ` at `x` is attained. -/
theorem infimalConvolutionFamily_closedProper_and_attained_of_closedProper_polyhedral_and_nonempty_iInter_domConj_first_iInter_ri_domConj_rest
    {n m k : ℕ} (hk : k ≤ m) (f : Fin m → (Fin n → ℝ) → EReal)
    (hclosed : ∀ i, ClosedConvexFunction (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hdomStar_riStar :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))))
          ∩
          (⋂ i : {i : Fin m // k ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))))))
    (hmPos : 0 < m) :
    ClosedConvexFunction (infimalConvolutionFamily f) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (infimalConvolutionFamily f) ∧
      ∀ x : Fin n → ℝ,
        ∃ xFamily : Fin m → Fin n → ℝ,
          (∑ i, xFamily i) = x ∧
            infimalConvolutionFamily f x = ∑ i, f i (xFamily i) := by
  have hpolyConj : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (fenchelConjugate n (f i)) := by
    intro i hi
    exact (polyhedralConvexFunction_fenchelConjugate n (f i)) (hpoly i hi)
  have hproperConj :
      ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
    intro i
    simpa using (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hproper i))
  have hdomConj :
      Set.Nonempty
        (⋂ i : Fin m,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) := by
    rcases hdomStar_riStar with ⟨x0E, hx0E⟩
    refine ⟨(x0E : Fin n → ℝ), Set.mem_iInter.2 ?_⟩
    intro i
    by_cases hi : i.1 < k
    · have hLeft :
          x0E ∈
            ⋂ j : {j : Fin m // j.1 < k},
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f j))) :=
        hx0E.1
      have hxPre :
          x0E ∈
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) := by
        simpa using (Set.mem_iInter.mp hLeft) ⟨i, hi⟩
      simpa [Set.mem_preimage] using hxPre
    · have hkLe : k ≤ i.1 := Nat.le_of_not_gt hi
      have hRight :
          x0E ∈
            ⋂ j : {j : Fin m // k ≤ j.1},
              euclideanRelativeInterior n
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f j))) :=
        hx0E.2
      have hxri :
          x0E ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) := by
        simpa using (Set.mem_iInter.mp hRight) ⟨i, hkLe⟩
      have hxPre :
          x0E ∈
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) :=
        (euclideanRelativeInterior_subset_closure n
          (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))))).1 hxri
      simpa [Set.mem_preimage] using hxPre
  have hproperSumConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i, fenchelConjugate n (f i) x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := fun i => fenchelConjugate n (f i)) (hproper := hproperConj) (hdom := hdomConj)
  have hthm :
      fenchelConjugate n (fun x => ∑ i, fenchelConjugate n (f i) x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (fenchelConjugate n (f i))) ∧
      ∀ x : Fin n → ℝ,
        ∃ xFamily : Fin m → Fin n → ℝ,
          (∑ i, xFamily i) = x ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (fenchelConjugate n (f i))) x =
              ∑ i, fenchelConjugate n (fenchelConjugate n (f i)) (xFamily i) := by
    simpa using
      (fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
        (f := fun i => fenchelConjugate n (f i)) (hk := hk) (hmPos := hmPos)
        (hpoly := hpolyConj) (hproper := hproperConj) (hdom_ri := hdomStar_riStar))
  have hbiconj :
      ∀ i : Fin m, fenchelConjugate n (fenchelConjugate n (f i)) = f i := by
    intro i
    have hcl :
        clConv n (f i) = f i :=
      clConv_eq_of_closedProperConvex (n := n) (f := f i) (hf_closed := (hclosed i).2)
        (hf_proper := hproper i)
    calc
      fenchelConjugate n (fenchelConjugate n (f i)) = clConv n (f i) := by
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f i))
      _ = f i := hcl
  have hEqInf :
      fenchelConjugate n (fun x => ∑ i, fenchelConjugate n (f i) x) =
        infimalConvolutionFamily f := by
    calc
      fenchelConjugate n (fun x => ∑ i, fenchelConjugate n (f i) x) =
          infimalConvolutionFamily (fun i => fenchelConjugate n (fenchelConjugate n (f i))) :=
        hthm.1
      _ = infimalConvolutionFamily f := by
        simp [hbiconj]
  have hclosedInf : ClosedConvexFunction (infimalConvolutionFamily f) := by
    have hclosedConjSum :
        ClosedConvexFunction (fenchelConjugate n (fun x => ∑ i, fenchelConjugate n (f i) x)) :=
      ⟨(fenchelConjugate_closedConvex (n := n) (f := fun x => ∑ i, fenchelConjugate n (f i) x)).2,
        (fenchelConjugate_closedConvex (n := n) (f := fun x => ∑ i, fenchelConjugate n (f i) x)).1⟩
    simpa [hEqInf] using hclosedConjSum
  have hproperInf :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (infimalConvolutionFamily f) := by
    have hproperConjSumConj :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fenchelConjugate n (fun x => ∑ i, fenchelConjugate n (f i) x)) :=
      proper_fenchelConjugate_of_proper (n := n) (f := fun x => ∑ i, fenchelConjugate n (f i) x)
        hproperSumConj
    simpa [hEqInf] using hproperConjSumConj
  refine ⟨hclosedInf, hproperInf, ?_⟩
  intro x
  rcases hthm.2 x with ⟨xFamily, hsum, hval⟩
  refine ⟨xFamily, hsum, ?_⟩
  simpa [hbiconj] using hval

end Section20
end Chap04
