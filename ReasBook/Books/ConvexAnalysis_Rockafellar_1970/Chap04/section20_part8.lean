/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part7

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Theorem 20.1: in the strict-tail branch `k < m`, the conjugate of the
filtered tail-block sum is attained by a decomposition over the tail index subtype. -/
lemma helperForTheorem_20_1_tailBlock_conjugate_attained_by_tailFamily
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hklt : k < m)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hriTail :
      Set.Nonempty
        (⋂ i : {i : Fin m // k ≤ i.1},
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1))))
    (xTail : Fin n → ℝ) :
    ∃ tailFamily : {i : Fin m // k ≤ i.1} → Fin n → ℝ,
      (∑ i, tailFamily i) = xTail ∧
        fenchelConjugate n
            (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) xTail =
          ∑ i : {i : Fin m // k ≤ i.1},
            fenchelConjugate n (f i.1) (tailFamily i) := by
  classical
  let J : Type := {i : Fin m // k ≤ i.1}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let kTail : ℕ := Fintype.card J
  let eJ : J ≃ Fin kTail := Fintype.equivFin J
  let fFin : Fin kTail → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperFin :
      ∀ i : Fin kTail,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin, fJ] using hproper (eJ.symm i).1
  have hriFin :
      Set.Nonempty
        (⋂ i : Fin kTail,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i))) := by
    rcases hriTail with ⟨x0E, hx0E⟩
    refine ⟨x0E, Set.mem_iInter.2 ?_⟩
    intro i
    simpa [fFin, fJ] using (Set.mem_iInter.mp hx0E) (eJ.symm i)
  have hsec16 :
      fenchelConjugate n (fun x => ∑ i : Fin kTail, fFin i x) =
        infimalConvolutionFamily (fun i : Fin kTail => fenchelConjugate n (fFin i)) ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolutionFamily (fun i : Fin kTail => fenchelConjugate n (fFin i)) xStar = ⊤ ∨
            ∃ xStarFamily : Fin kTail → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                (∑ i, fenchelConjugate n (fFin i) (xStarFamily i)) =
                  infimalConvolutionFamily (fun i : Fin kTail => fenchelConjugate n (fFin i))
                    xStar) :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := fFin) hproperFin hriFin
  have hsumFinToJ :
      (fun x => ∑ i : Fin kTail, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin kTail => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => k ≤ i.1)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin kTail, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  have hJnonempty : Nonempty J := by
    refine ⟨⟨⟨k, hklt⟩, le_rfl⟩⟩
  have hkTailPos : 0 < kTail := by
    simpa [kTail] using (Fintype.card_pos_iff.mpr hJnonempty)
  have htailFinWitness :
      ∃ tailFinFamily : Fin kTail → Fin n → ℝ,
        (∑ i, tailFinFamily i) = xTail ∧
          (∑ i, fenchelConjugate n (fFin i) (tailFinFamily i)) =
            infimalConvolutionFamily (fun i : Fin kTail => fenchelConjugate n (fFin i)) xTail := by
    rcases hsec16.2 xTail with htop | hatt
    · exact
        section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
          (n := n) (m := kTail) hkTailPos
          (g := fun i : Fin kTail => fenchelConjugate n (fFin i))
          (xStar := xTail) htop
    · exact hatt
  rcases htailFinWitness with ⟨tailFinFamily, hsumTailFin, hvalTailFin⟩
  let tailFamily : J → Fin n → ℝ := fun j => tailFinFamily (eJ j)
  have hsumTailJ : (∑ j : J, tailFamily j) = xTail := by
    calc
      (∑ j : J, tailFamily j) =
          ∑ i : Fin kTail, tailFamily (eJ.symm i) := by
            simpa [tailFamily] using
              (Fintype.sum_equiv eJ
                (fun j : J => tailFamily j)
                (fun i : Fin kTail => tailFamily (eJ.symm i))
                (by intro j; simp [tailFamily]))
      _ = ∑ i : Fin kTail, tailFinFamily i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [tailFamily]
      _ = xTail := hsumTailFin
  have hsumConjJEqFin :
      (∑ j : J, fenchelConjugate n (f j.1) (tailFamily j)) =
        ∑ i : Fin kTail, fenchelConjugate n (fFin i) (tailFinFamily i) := by
    calc
      (∑ j : J, fenchelConjugate n (f j.1) (tailFamily j)) =
          ∑ i : Fin kTail, fenchelConjugate n (f (eJ.symm i).1) (tailFamily (eJ.symm i)) := by
            simpa using
              (Fintype.sum_equiv eJ
                (fun j : J => fenchelConjugate n (f j.1) (tailFamily j))
                (fun i : Fin kTail =>
                  fenchelConjugate n (f (eJ.symm i).1) (tailFamily (eJ.symm i)))
                (by intro j; simp))
      _ = ∑ i : Fin kTail, fenchelConjugate n (fFin i) (tailFinFamily i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [fFin, fJ, tailFamily]
  refine ⟨tailFamily, hsumTailJ, ?_⟩
  have hconjTailFin :
      fenchelConjugate n (fun x => ∑ i : Fin kTail, fFin i x) xTail =
        ∑ i : Fin kTail, fenchelConjugate n (fFin i) (tailFinFamily i) := by
    calc
      fenchelConjugate n (fun x => ∑ i : Fin kTail, fFin i x) xTail =
          infimalConvolutionFamily (fun i : Fin kTail => fenchelConjugate n (fFin i)) xTail := by
            simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xTail) hsec16.1
      _ = ∑ i : Fin kTail, fenchelConjugate n (fFin i) (tailFinFamily i) := hvalTailFin.symm
  calc
    fenchelConjugate n
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) xTail =
      fenchelConjugate n (fun x => ∑ i : Fin kTail, fFin i x) xTail := by
        simpa [hsumFinToFilter] using
          congrArg (fun g : (Fin n → ℝ) → EReal => g xTail) hsumFinToFilter.symm
    _ = ∑ i : Fin kTail, fenchelConjugate n (fFin i) (tailFinFamily i) := hconjTailFin
    _ = ∑ i : J, fenchelConjugate n (f i.1) (tailFamily i) := hsumConjJEqFin.symm

/-- Helper for Theorem 20.1: a binary split witness together with attained head and
tail block conjugate values lifts to an attained full-family split witness. -/
lemma helperForTheorem_20_1_fullFamily_attained_of_binarySplit_and_blockAttainment
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (p q : (Fin n → ℝ) → EReal)
    (hheadBlockAttained :
      ∀ xHead : Fin n → ℝ,
        ∃ headFamily : {i : Fin m // i.1 < k} → Fin n → ℝ,
          (∑ i, headFamily i) = xHead ∧
            fenchelConjugate n p xHead =
              ∑ i : {i : Fin m // i.1 < k},
                fenchelConjugate n (f i.1) (headFamily i))
    (htailBlockAttained :
      ∀ xTail : Fin n → ℝ,
        ∃ tailFamily : {i : Fin m // k ≤ i.1} → Fin n → ℝ,
          (∑ i, tailFamily i) = xTail ∧
            fenchelConjugate n q xTail =
              ∑ i : {i : Fin m // k ≤ i.1},
                fenchelConjugate n (f i.1) (tailFamily i))
    {xStar y : Fin n → ℝ}
    (hbinaryValue :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
        fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
          ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  rcases hheadBlockAttained (xStar - y) with ⟨headFamily, hHeadSum, hHeadVal⟩
  rcases htailBlockAttained y with ⟨tailFamily, hTailSum, hTailVal⟩
  have hHeadTail : (xStar - y) + y = xStar := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rcases
      helperForTheorem_20_1_liftWitness_polyBlock_tailBlock_to_fullFamily_with_valueSum
        (f := f) (headFamily := headFamily) (tailFamily := tailFamily)
        (hHeadSum := hHeadSum) (hTailSum := hTailSum) (hHeadTail := hHeadTail) with
    ⟨xStarFamily, hsumFamily, hsumValue⟩
  refine ⟨xStarFamily, hsumFamily, ?_⟩
  calc
    infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
        fenchelConjugate n p (xStar - y) + fenchelConjugate n q y := hbinaryValue
    _ =
        (∑ i : {i : Fin m // i.1 < k}, fenchelConjugate n (f i.1) (headFamily i)) +
        (∑ i : {i : Fin m // k ≤ i.1}, fenchelConjugate n (f i.1) (tailFamily i)) := by
          rw [hHeadVal, hTailVal]
    _ = ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
          simpa using hsumValue.symm

/-- Helper for Theorem 20.1: under a mixed two-block `dom/ri` qualification with
polyhedral left block, both block-domain preimages have nonempty relative interior,
and the effective domain of the two-block sum is nonempty. -/
lemma helperForTheorem_20_1_binary_block_ri_and_sumDomain_nonempty_of_polyLeft_domRi
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
    (Set.Nonempty
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p))
      ∧
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
      ∧
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x)) := by
  have hriBoth :
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p))
      ∧
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    helperForTheorem_20_0_4_nonempty_ri_inter_of_polyhedral_left_and_nonempty_dom_inter_ri_right
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  have hsumDomNonempty :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x)) :=
    helperForTheorem_20_0_4_nonempty_effectiveDomain_sum_of_nonempty_dom_left_inter_ri_right
      (p := p) (q := q) hproperP hproperQ hnonemptyDomInterRi
  exact ⟨hriBoth, hsumDomNonempty⟩

/-- Helper for Theorem 20.1: mixed two-block exact conjugate/infimal-convolution
bridge with top-or-attained alternatives under `dom(p) ∩ ri(dom(q))` and a
polyhedral left block. -/
lemma helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_of_riInter
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hriInter :
      Set.Nonempty
        (euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = ⊤ ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  exact
    helperForTheorem_20_1_binary_exact_topOrAttained_polyLeft_domRi_via_section16
      (p := p) (q := q) hproperP hproperQ hriInter

/-- Helper for Theorem 20.1: a mixed two-block `dom/ri` witness with polyhedral left
block yields the binary closure-level conjugate/infimal-convolution identity. -/
lemma helperForTheorem_20_1_binary_closure_conjugate_eq_closure_infimalConvolution_of_polyLeft_domRi
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
    fenchelConjugate n (fun x => p x + q x) =
      convexFunctionClosure
        (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases p (fun _ => q) i
  have hpolyTwo :
      ∀ i : Fin 2, i.1 < 1 → IsPolyhedralConvexFunction n (fTwo i) := by
    intro i hi
    fin_cases i
    · simpa [fTwo] using hpolyP
    · exact False.elim (Nat.not_lt.mpr (Nat.le_refl 1) hi)
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproperP
    · simpa [fTwo] using hproperQ
  have hdomRiTwo :
      Set.Nonempty
        ((⋂ i : {i : Fin 2 // i.1 < 1},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
          ∩
          (⋂ i : {i : Fin 2 // 1 ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
    rcases hnonemptyDomInterRi with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine And.intro ?_ ?_
    · refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · simpa [fTwo] using hx0.1
      · exact False.elim (Nat.not_lt.mpr (Nat.le_refl 1) hi)
    · refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · exact False.elim (Nat.not_le.mpr (Nat.zero_lt_one) hi)
      · simpa [fTwo] using hx0.2
  have hclosureTwo :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) =
        convexFunctionClosure
          (infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))) :=
    helperForTheorem_20_1_closure_refinement_of_mixed_assumptions
      (f := fTwo) (k := 1) hpolyTwo hproperTwo hdomRiTwo
  simpa [fTwo, Fin.sum_univ_two, infimalConvolution_eq_infimalConvolutionFamily_two] using
    hclosureTwo

/-- Helper for Theorem 20.1: the mixed two-block `dom/ri` witness yields properness
of the two-block sum. -/
lemma helperForTheorem_20_1_binary_sum_proper_of_nonempty_dom_inter_ri
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
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
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases p (fun _ => q) i
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproperP
    · simpa [fTwo] using hproperQ
  have hsumDomNonempty :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x)) :=
    helperForTheorem_20_0_4_nonempty_effectiveDomain_sum_of_nonempty_dom_left_inter_ri_right
      (p := p) (q := q) hproperP hproperQ hnonemptyDomInterRi
  have hsumExists : ∃ x : Fin n → ℝ, (∑ i : Fin 2, fTwo i x) ≠ (⊤ : EReal) := by
    rcases hsumDomNonempty with ⟨x0, hx0DomSum⟩
    refine ⟨x0, ?_⟩
    have hx0NotTop :
        (fun x => p x + q x) x0 ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
        (f := fun x => p x + q x) (x := x0) hx0DomSum
    simpa [fTwo, Fin.sum_univ_two] using hx0NotTop
  have hproperSumTwo :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin 2, fTwo i x) :=
    properConvexFunctionOn_sum_of_exists_ne_top (f := fTwo) hproperTwo hsumExists
  simpa [fTwo, Fin.sum_univ_two] using hproperSumTwo

/-- Helper for Theorem 20.1: under the mixed two-block `dom/ri` qualification with
polyhedral left block, the binary Fenchel-conjugate side is bounded above by the
binary infimal-convolution side. -/
lemma helperForTheorem_20_1_binary_conjugate_le_infimalConvolution_of_polyLeft_domRi
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
    fenchelConjugate n (fun x => p x + q x) ≤
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) := by
  have hclosure :
      fenchelConjugate n (fun x => p x + q x) =
        convexFunctionClosure
          (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) :=
    helperForTheorem_20_1_binary_closure_conjugate_eq_closure_infimalConvolution_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  intro xStar
  calc
    fenchelConjugate n (fun x => p x + q x) xStar =
        convexFunctionClosure
          (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) xStar := by
            exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hclosure
    _ ≤ infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar :=
      (convexFunctionClosure_le_self
        (f := infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))) xStar

/-- Helper for Theorem 20.1: for proper two-block data, the binary infimal
convolution of conjugates is convex. -/
lemma helperForTheorem_20_1_binary_infimalConvolution_convex_of_proper
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q) :
    ConvexFunction (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases p (fun _ => q) i
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproperP
    · simpa [fTwo] using hproperQ
  have hconvFamily :
      ConvexFunction
        (infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))) :=
    section16_convexFunction_infimalConvolutionFamily_conjugates (f := fTwo) hproperTwo
  simpa [fTwo, infimalConvolution_eq_infimalConvolutionFamily_two] using hconvFamily

/-- Helper for Theorem 20.1: if the binary infimal-convolution value is `⊤`, then
it is attained by a split of the form `(x⋆ - y, y)`. -/
lemma helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
    {n : ℕ} (p q : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ)
    (htop :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal)) :
    ∃ y : Fin n → ℝ,
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
        fenchelConjugate n p (xStar - y) + fenchelConjugate n q y := by
  let g : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => if i = 0 then fenchelConjugate n p else fenchelConjugate n q
  have htwoPos : 0 < (2 : ℕ) := by decide
  have htopFam :
      infimalConvolutionFamily g xStar = (⊤ : EReal) := by
    simpa [g, infimalConvolution_eq_infimalConvolutionFamily_two] using htop
  rcases
      section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
        (n := n) (m := 2) htwoPos (g := g) (xStar := xStar) htopFam with
    ⟨xStarFamily, hsum, hval⟩
  have hsumTwo : xStarFamily 0 + xStarFamily 1 = xStar := by
    simpa [Fin.sum_univ_two] using hsum
  have hsplit : xStarFamily 0 = xStar - xStarFamily 1 := by
    ext j
    have hsumTwoj : xStarFamily 0 j + xStarFamily 1 j = xStar j := by
      simpa using congrArg (fun v : Fin n → ℝ => v j) hsumTwo
    have hsplitj : xStarFamily 0 j = xStar j - xStarFamily 1 j := by
      linarith
    simpa [Pi.sub_apply] using hsplitj
  refine ⟨xStarFamily 1, ?_⟩
  calc
    infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
        infimalConvolutionFamily g xStar := by
          simpa [g, infimalConvolution_eq_infimalConvolutionFamily_two]
    _ = ∑ i : Fin 2, g i (xStarFamily i) := by
          simpa using hval.symm
    _ = g 0 (xStarFamily 0) + g 1 (xStarFamily 1) := by
          simp [Fin.sum_univ_two]
    _ = fenchelConjugate n p (xStarFamily 0) + fenchelConjugate n q (xStarFamily 1) := by
          simp [g]
    _ = fenchelConjugate n p (xStar - xStarFamily 1) + fenchelConjugate n q (xStarFamily 1) := by
          rw [hsplit]

/-- Helper for Theorem 20.1: under mixed `dom/ri` qualification with polyhedral left
block, one always has the forward binary inequality and a witness in the `⊤`-value
case for the binary infimal convolution. -/
lemma helperForTheorem_20_1_forwardLe_and_topWitness_of_polyLeft_domRi
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
    (fenchelConjugate n (fun x => p x + q x) ≤
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_20_1_binary_conjugate_le_infimalConvolution_of_polyLeft_domRi
        (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  · intro xStar htop
    exact
      helperForTheorem_20_1_binary_attainmentWitness_of_top_infimalConvolution
        (p := p) (q := q) (xStar := xStar) htop

/-- Helper for Theorem 20.1: mixed two-block exact conjugate/infimal-convolution
bridge follows from the two inequalities plus non-`⊤` attainment for the binary
infimal convolution values. -/
lemma helperForTheorem_20_1_exact_topOrAttained_of_forward_reverse_and_neTopAttainment
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hforwardLe :
      fenchelConjugate n (fun x => p x + q x) ≤
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q))
    (hreverseLe :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
    (hneTopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :
    (fenchelConjugate n (fun x => p x + q x) =
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = ⊤ ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  refine ⟨le_antisymm hforwardLe hreverseLe, ?_⟩
  intro xStar
  by_cases htop :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal)
  · exact Or.inl htop
  · exact Or.inr (hneTopAttained xStar htop)

/-- Helper for Theorem 20.1: under mixed `dom/ri` qualification with polyhedral left
block, every `⊤`-valued binary infimal-convolution point admits a split witness in
`(x⋆ - y, y)` form. -/
lemma helperForTheorem_20_1_nonriInterCore_topCase_attainment_of_polyLeft_domRi
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
    ∀ xStar : Fin n → ℝ,
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y := by
  exact
    (helperForTheorem_20_1_forwardLe_and_topWitness_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi).2

/-- Helper for Theorem 20.1: combining top-case attainment with non-`⊤` attainment
gives universal split-attainment for the binary infimal convolution. -/
lemma helperForTheorem_20_1_nonriInterCore_universalAttainment_of_topCase_and_neTopCase
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (htopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)
    (hneTopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :
    ∀ xStar : Fin n → ℝ,
      ∃ y : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
          fenchelConjugate n p (xStar - y) + fenchelConjugate n q y := by
  intro xStar
  by_cases htop :
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal)
  · exact htopAttained xStar htop
  · exact hneTopAttained xStar htop

/-- Helper for Theorem 20.1: once top-case attainment is available, non-`⊤`
attainment is equivalent to universal split-attainment for the binary infimal
convolution. -/
lemma helperForTheorem_20_1_nonriInterCore_neTopAttainment_iff_universalAttainment_of_topCase
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (htopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :
    (∀ xStar : Fin n → ℝ,
      infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)
      ↔
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  constructor
  · intro hneTopAttained
    exact
      helperForTheorem_20_1_nonriInterCore_universalAttainment_of_topCase_and_neTopCase
        (p := p) (q := q) htopAttained hneTopAttained
  · intro huniversalAttained
    intro xStar _hneTop
    exact huniversalAttained xStar

/-- Helper for Theorem 20.1: under a fixed top-case attainment map, the non-`riInter`
core target is equivalent to proving reverse inequality together with universal
split-attainment. -/
lemma helperForTheorem_20_1_nonriInterCore_goal_iff_reverseLe_and_universalAttainment_of_topCase
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (htopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :
    ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  constructor
  · rintro ⟨hreverseLe, hneTopAttained⟩
    refine ⟨hreverseLe, ?_⟩
    exact
      (helperForTheorem_20_1_nonriInterCore_neTopAttainment_iff_universalAttainment_of_topCase
        (p := p) (q := q) htopAttained).1 hneTopAttained
  · rintro ⟨hreverseLe, huniversalAttained⟩
    refine ⟨hreverseLe, ?_⟩
    exact
      (helperForTheorem_20_1_nonriInterCore_neTopAttainment_iff_universalAttainment_of_topCase
        (p := p) (q := q) htopAttained).2 huniversalAttained

/-- Helper for Theorem 20.1: a reverse inequality together with universal
split-attainment immediately yields the required reverse inequality plus
non-`⊤` split-attainment condition. -/
lemma helperForTheorem_20_1_nonriInterCore_neTopAttainment_of_reverseLe_and_universalAttainment
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hreverseAndUniversal :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  rcases hreverseAndUniversal with ⟨hreverseLe, huniversalAttained⟩
  refine ⟨hreverseLe, ?_⟩
  intro xStar _hneTop
  exact huniversalAttained xStar

/-- Helper for Theorem 20.1: under mixed `dom/ri` assumptions with a polyhedral
left block, the reverse-plus-universal binary goal is equivalent to reverse plus
non-`⊤` attainment because top-case attainment is already available. -/
lemma helperForTheorem_20_1_mixed_two_block_goal_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
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
    ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  have htopAttained :
      ∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y :=
    helperForTheorem_20_1_nonriInterCore_topCase_attainment_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  exact
    (helperForTheorem_20_1_nonriInterCore_goal_iff_reverseLe_and_universalAttainment_of_topCase
      (p := p) (q := q) htopAttained).symm

/-- Helper for Theorem 20.1: in the mixed two-block `dom/ri` setting with a
polyhedral left block, the isolated core bridge
`reverseLe + non-⊤ attainment` upgrades to
`reverseLe + universal split-attainment`. -/
lemma helperForTheorem_20_1_mixed_two_block_reverseLe_and_universalAttainment_of_polyLeft_domRi_of_core
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
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hgoalIff :
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
        ↔
        ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
          fenchelConjugate n (fun x => p x + q x))
          ∧
          (∀ xStar : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
              ∃ y : Fin n → ℝ,
                infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                  fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :=
    helperForTheorem_20_1_mixed_two_block_goal_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  exact hgoalIff.2 hcore

/-- Helper for Theorem 20.1: core non-`riInter` binary bridge under
`dom(p) ∩ ri(dom(q))` with polyhedral left block, providing reverse inequality
and non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_binary_goal_iff_reverseLe_and_universalAttainment_of_polyLeft_domRi
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
    ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y))
      ↔
      ((infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) := by
  exact
    (helperForTheorem_20_1_mixed_two_block_goal_iff_reverseLe_and_neTopAttainment_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi).symm

/-- Helper for Theorem 20.1: core non-`riInter` binary bridge under
`dom(p) ∩ ri(dom(q))` with polyhedral left block, providing reverse inequality
and non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_of_riInter
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
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hriInter :
      Set.Nonempty
        (euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = ⊤ ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) :=
    helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_of_riInter
      (p := p) (q := q) hproperP hproperQ hriInter
  have hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
    refine ⟨?_, ?_⟩
    · intro xStar
      have hbinaryEqAt :
          fenchelConjugate n (fun x => p x + q x) xStar =
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
        exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hbinaryBridge.1
      exact le_of_eq hbinaryEqAt.symm
    · intro xStar hneTop
      rcases hbinaryBridge.2 xStar with htop | hsplit
      · exact (hneTop htop).elim
      · exact hsplit
  exact
    helperForTheorem_20_1_mixed_two_block_reverseLe_and_universalAttainment_of_polyLeft_domRi_of_core
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi hcore

/-- Helper for Theorem 20.1: in zero dimension, nonempty relative interiors of the
left and right effective-domain preimages force a nonempty relative-interior
intersection. -/
lemma helperForTheorem_20_1_nonempty_ri_inter_of_zero_dim_of_nonempty_each_ri
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hn0 : n = 0)
    (hriLeft :
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)))
    (hriRight :
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    Set.Nonempty
      (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
        ∩
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  rcases hriLeft with ⟨xLeft, hxLeft⟩
  rcases hriRight with ⟨xRight, hxRight⟩
  have hxEq : xLeft = xRight := by
    haveI : Subsingleton (EuclideanSpace ℝ (Fin n)) := by
      cases hn0
      infer_instance
    exact Subsingleton.elim xLeft xRight
  have hxRightAtLeft :
      xLeft ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
    simpa [hxEq] using hxRight
  exact ⟨xLeft, ⟨hxLeft, hxRightAtLeft⟩⟩

/-- Helper for Theorem 20.1: core non-`riInter` binary bridge under
`dom(p) ∩ ri(dom(q))` with polyhedral left block, providing reverse inequality
and non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInter_binary_reverseLe_and_universalAttainment_of_polyLeft_domRi_posDim_of_core
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnPos : 0 < n)
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
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hnotRiInter :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    (hcore :
      (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
        fenchelConjugate n (fun x => p x + q x))
        ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
            ∃ y : Fin n → ℝ,
              infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
                fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        ∃ y : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  have _hnPos_use : 0 < n := hnPos
  have _hnotRiInter_use :
      ¬ Set.Nonempty
          (euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
            ∩
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    hnotRiInter
  exact
    (helperForTheorem_20_1_nonriInter_binary_goal_iff_reverseLe_and_universalAttainment_of_polyLeft_domRi
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi).1 hcore

/-- Helper for Theorem 20.1: in the positive-dimensional non-`riInter` binary
branch, an exact/top-or-attained bridge yields reverse inequality together with
non-`⊤` split-attainment. -/
lemma helperForTheorem_20_1_nonriInterCore_reverseLe_and_neTopAttainment_of_exact_topOrAttained_binary_posDim
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hbinaryBridge :
      (fenchelConjugate n (fun x => p x + q x) =
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar = (⊤ : EReal) ∨
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y)) :
    (infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) ≤
      fenchelConjugate n (fun x => p x + q x))
      ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar ≠ (⊤ : EReal) →
          ∃ y : Fin n → ℝ,
            infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
              fenchelConjugate n p (xStar - y) + fenchelConjugate n q y) := by
  refine ⟨?_, ?_⟩
  · intro xStar
    have hEqAt :
        fenchelConjugate n (fun x => p x + q x) xStar =
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar := by
      exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hbinaryBridge.1
    exact le_of_eq hEqAt.symm
  · intro xStar hneTop
    rcases hbinaryBridge.2 xStar with htop | hsplit
    · exact (hneTop htop).elim
    · exact hsplit


end Section20
end Chap04
