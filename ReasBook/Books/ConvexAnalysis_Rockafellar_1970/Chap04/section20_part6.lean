/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part5

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Theorem 20.0.4: from a mixed `dom/ri` witness and properness,
the left effective-domain preimage has nonempty relative interior. -/
lemma helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_left_of_nonempty_dom_inter_ri_right
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    Set.Nonempty
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)) := by
  have hconvPPreimage :
      Convex ℝ
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)) :=
    helperForTheorem_20_0_4_convex_preimage_effectiveDomain_of_proper
      (p := p) hproperP
  have hnonemptyPPreimage :
      Set.Nonempty
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) :=
    helperForTheorem_20_0_4_nonempty_preimage_effectiveDomain_left_of_nonempty_dom_inter_ri_right
      (p := p) (q := q) hnonemptyDomInterRi
  exact
    euclideanRelativeInterior_nonempty_of_convex_of_nonempty hconvPPreimage hnonemptyPPreimage

/-- Helper for Theorem 20.0.4: from a nonempty mixed intersection,
the right effective-domain preimage has nonempty relative interior. -/
lemma helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_right_of_nonempty_dom_inter_ri_right
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    Set.Nonempty
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  rcases hnonemptyDomInterRi with ⟨x0E, hx0E⟩
  exact ⟨x0E, hx0E.2⟩

/-- Helper for Theorem 20.0.4: a mixed `dom/ri` witness yields nonempty relative
interiors for both effective-domain preimages. -/
lemma helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_both_of_nonempty_dom_inter_ri_right
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    Set.Nonempty
      (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p))
      ∧
      Set.Nonempty
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_left_of_nonempty_dom_inter_ri_right
        (p := p) (q := q) hproperP hnonemptyDomInterRi
  · exact
      helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_right_of_nonempty_dom_inter_ri_right
        (p := p) (q := q) hnonemptyDomInterRi

/-- Helper for Theorem 20.0.4: mixed two-block closure bridge from a polyhedral left
block and a `dom/ri` witness. -/
lemma helperForTheorem_20_0_4_nonempty_ri_inter_of_polyhedral_left_and_nonempty_dom_inter_ri_right
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
    Set.Nonempty
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p))
    ∧
    Set.Nonempty
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  have _ : IsPolyhedralConvexFunction n p := hpolyP
  have _ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := hproperQ
  exact
    helperForTheorem_20_0_4_nonempty_ri_preimage_effectiveDomain_both_of_nonempty_dom_inter_ri_right
      (p := p) (q := q) hproperP hnonemptyDomInterRi

/-- Helper for Theorem 20.0.4: mixed two-block closure bridge from a polyhedral left
block and a `dom/ri` witness. -/
lemma helperForTheorem_20_0_4_ri_transfer_of_polyhedral_left_and_dom_ri_witness
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hdomRiWitness :
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    Set.Nonempty
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
        ∩
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  have hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    helperForTheorem_20_0_4_nonempty_preimageDom_inter_riPreimage_of_dom_ri_witness
      (p := p) (q := q) hdomRiWitness
  have _ : IsPolyhedralConvexFunction n p := hpolyP
  have _ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p := hproperP
  have _ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := hproperQ
  exact hnonemptyDomInterRi

/-- Helper for Theorem 20.0.4: a nonempty mixed preimage intersection gives a common
effective-domain point for the left and right summands. -/
lemma helperForTheorem_20_0_4_exists_common_effectiveDomain_point_of_nonempty_dom_left_inter_ri_right
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) q := by
  rcases hnonemptyDomInterRi with ⟨x0E, hx0E⟩
  refine ⟨(x0E : Fin n → ℝ), ?_, ?_⟩
  · simpa [Set.mem_preimage] using hx0E.1
  · have hx0MemQPreimage :
      x0E ∈
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
      exact
        (euclideanRelativeInterior_subset_closure n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)).1 hx0E.2
    simpa [Set.mem_preimage] using hx0MemQPreimage

/-- Helper for Theorem 20.0.4: the mixed left-domain/right-relative-interior witness
implies the two-block sum has a nonempty effective domain. -/
lemma helperForTheorem_20_0_4_nonempty_effectiveDomain_sum_of_nonempty_dom_left_inter_ri_right
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
    Set.Nonempty
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x)) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases p (fun _ => q) i
  have hnotbotTwo :
      ∀ i : Fin 2, ∀ x : Fin n → ℝ, fTwo i x ≠ (⊥ : EReal) := by
    intro i x
    have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    fin_cases i
    · simpa [fTwo] using (hproperP.2.2 x hxUniv)
    · simpa [fTwo] using (hproperQ.2.2 x hxUniv)
  have hdomEq :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ∑ i : Fin 2, fTwo i x) =
        ⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i) :=
    effectiveDomain_sum_eq_iInter_univ (f := fTwo) hnotbotTwo
  rcases
    helperForTheorem_20_0_4_exists_common_effectiveDomain_point_of_nonempty_dom_left_inter_ri_right
      (p := p) (q := q) hnonemptyDomInterRi with ⟨x0, hx0DomP, hx0DomQ⟩
  have hx0Inter :
      x0 ∈ ⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    refine Set.mem_iInter.2 ?_
    intro i
    fin_cases i
    · simpa [fTwo] using hx0DomP
    · simpa [fTwo] using hx0DomQ
  have hx0DomSum :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ∑ i : Fin 2, fTwo i x) := by
    exact hdomEq.symm ▸ hx0Inter
  refine ⟨x0, ?_⟩
  simpa [fTwo, Fin.sum_univ_two] using hx0DomSum

/-- Helper for Theorem 20.0.4: package the mixed witness consequences needed by
the local two-block closure bridge. -/
lemma helperForTheorem_20_0_4_domRiWitness_and_nonempty_effectiveDomainSum_of_nonempty_dom_left_inter_ri_right
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
    (∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)))
    ∧
    Set.Nonempty
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => p x + q x)) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_20_0_4_extract_dom_ri_witness_of_nonempty_preimageDom_inter_riPreimage
        (p := p) (q := q) hnonemptyDomInterRi
  · exact
      helperForTheorem_20_0_4_nonempty_effectiveDomain_sum_of_nonempty_dom_left_inter_ri_right
        (p := p) (q := q) hproperP hproperQ hnonemptyDomInterRi

/-- Helper for Theorem 20.0.4: dependency-closed mixed two-block bridge from a
left-domain/right-relative-interior witness. -/
lemma helperForTheorem_20_0_4_closed_left_and_mixed_data_of_polyhedral_left
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
    ClosedConvexFunction p ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q ∧
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  have hclP : convexFunctionClosure p = p :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (n := n) (g := p) hpolyP hproperP
  have hclosedP : ClosedConvexFunction p := by
    simpa [hclP] using
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := p) hproperP).1.1
  exact ⟨hclosedP, hproperQ, hnonemptyDomInterRi⟩

/-- Helper for Theorem 20.0.4: rewrite the left summand using closure-equals-self
for a polyhedral proper left block. -/
lemma helperForTheorem_20_0_4_left_add_eq_leftClosure_add_of_polyhedral_proper
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p) :
    (fun x => p x + convexFunctionClosure q x) =
      (fun x => convexFunctionClosure p x + convexFunctionClosure q x) := by
  have hclP : convexFunctionClosure p = p :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (n := n) (g := p) hpolyP hproperP
  funext x
  simpa [hclP]

/-- Helper for Theorem 20.0.4: under a closed-left/proper-right mixed `dom/ri`
witness, the sum `p + cl q` is closed convex. -/
lemma helperForTheorem_20_0_4_sum_with_right_closure_closed_of_mixed_dom_ri
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hclosedP : ClosedConvexFunction p)
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
    ClosedConvexFunction (fun x => p x + convexFunctionClosure q x) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases p (fun _ => convexFunctionClosure q) i
  have hproperQcl :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure q) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := q) hproperQ).1.2
  have hproperTwo :
      ∀ i : Fin 2,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproperP
    · simpa [fTwo] using hproperQcl
  have hclosedQcl : ClosedConvexFunction (convexFunctionClosure q) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := q) hproperQ).1.1
  have hclosedTwo : ∀ i : Fin 2, ClosedConvexFunction (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hclosedP
    · simpa [fTwo] using hclosedQcl
  rcases
    helperForTheorem_20_0_4_exists_common_effectiveDomain_point_of_nonempty_dom_left_inter_ri_right
      (p := p) (q := q) hnonemptyDomInterRi with ⟨x0, hx0DomP, hx0DomQ⟩
  have hpxNotTop : p x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
      (f := p) (x := x0) hx0DomP
  have hqNotTop : q x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
      (f := q) (x := x0) hx0DomQ
  have hqclLe : convexFunctionClosure q x0 ≤ q x0 :=
    (convexFunctionClosure_le_self (f := q)) x0
  have hqclNotTop : convexFunctionClosure q x0 ≠ (⊤ : EReal) := by
    have hqLtTop : q x0 < (⊤ : EReal) := lt_top_iff_ne_top.mpr hqNotTop
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hqclLe hqLtTop)
  have hsumNotTop : (∑ i : Fin 2, fTwo i x0) ≠ (⊤ : EReal) := by
    refine finset_sum_ne_top_of_forall (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i : Fin 2 => fTwo i x0) ?_
    intro i hi
    fin_cases i
    · simpa [fTwo] using hpxNotTop
    · simpa [fTwo] using hqclNotTop
  have hsumClosedPack :=
    (sum_closed_proper_convex_recession_and_closure
      (f := fTwo) (f0_plus := fun _ => fun _ => (0 : EReal)) hproperTwo).1
      hclosedTwo ⟨x0, hsumNotTop⟩
  simpa [fTwo, Fin.sum_univ_two] using hsumClosedPack.1

/-- Helper for Theorem 20.0.4: dependency-closed mixed two-block bridge from a
left-domain/right-relative-interior witness. -/
lemma helperForTheorem_20_0_4_mixed_two_block_sumClosure_eq_closure_sum_of_nonempty_dom_left_inter_ri_right
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
    (fun x => convexFunctionClosure p x + convexFunctionClosure q x) =
      convexFunctionClosure (fun x => p x + q x) := by
  rcases
    helperForTheorem_20_0_4_closed_left_and_mixed_data_of_polyhedral_left
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi with
    ⟨hclosedP, hproperQ', hnonemptyDomInterRi'⟩
  have _ : ClosedConvexFunction p := hclosedP
  have _ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := hproperQ'
  have _ :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := hnonemptyDomInterRi'
  have hleftRewrite :
      (fun x => p x + convexFunctionClosure q x) =
        (fun x => convexFunctionClosure p x + convexFunctionClosure q x) :=
    helperForTheorem_20_0_4_left_add_eq_leftClosure_add_of_polyhedral_proper
      (p := p) (q := q) hpolyP hproperP
  have hsumWithRightClosureClosed :
      ClosedConvexFunction (fun x => p x + convexFunctionClosure q x) :=
    helperForTheorem_20_0_4_sum_with_right_closure_closed_of_mixed_dom_ri
      (p := p) (q := q) hclosedP hproperP hproperQ' hnonemptyDomInterRi'
  calc
    (fun x => convexFunctionClosure p x + convexFunctionClosure q x) =
        (fun x => p x + convexFunctionClosure q x) := hleftRewrite.symm
    _ = convexFunctionClosure (fun x => p x + q x) := by
      by_cases
          hriInter :
            Set.Nonempty
              (euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
                ∩
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))
      · let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
          fun i => Fin.cases p (fun _ => q) i
        have hfTwoZero : fTwo 0 = p := by
          rfl
        have hfTwoOne : fTwo 1 = q := by
          rfl
        have hproperTwo :
            ∀ i : Fin 2,
              ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
          intro i
          fin_cases i
          · simpa [fTwo] using hproperP
          · simpa [fTwo] using hproperQ'
        have hriTwo :
            Set.Nonempty
              (⋂ i : Fin 2,
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i))) := by
          rcases hriInter with ⟨x0, hx0⟩
          refine ⟨x0, Set.mem_iInter.2 ?_⟩
          intro i
          fin_cases i
          · simpa [fTwo] using hx0.1
          · simpa [fTwo] using hx0.2
        have hsumTwo :
            (fun x => ∑ i : Fin 2, convexFunctionClosure (fTwo i) x) =
              convexFunctionClosure (fun x => ∑ i : Fin 2, fTwo i x) :=
          section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
            (f := fTwo) hproperTwo hriTwo
        calc
          (fun x => p x + convexFunctionClosure q x) =
              (fun x => convexFunctionClosure p x + convexFunctionClosure q x) :=
            hleftRewrite
          _ = (fun x => ∑ i : Fin 2, convexFunctionClosure (fTwo i) x) := by
            funext x
            rw [Fin.sum_univ_two]
            simpa [hfTwoZero, hfTwoOne]
          _ = convexFunctionClosure (fun x => ∑ i : Fin 2, fTwo i x) := hsumTwo
          _ = convexFunctionClosure (fun x => p x + q x) := by
            congr 1
            funext x
            rw [Fin.sum_univ_two]
            simpa [hfTwoZero, hfTwoOne]
      · have hImageEq :
            (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
                epigraph (Set.univ : Set (Fin n → ℝ))
                  (fun x => p x + convexFunctionClosure q x)) :
                Set (Fin (n + 1) → ℝ)) =
            (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
                  epigraph (Set.univ : Set (Fin n → ℝ))
                    (convexFunctionClosure (fun x => p x + q x))) :
                  Set (Fin (n + 1) → ℝ)) := by
            refine Set.Subset.antisymm ?_ ?_
            · have hproperQcl :
                  ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                    (convexFunctionClosure q) :=
                (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
                  (f := q) hproperQ').1.2
              have hnonemptyEffectiveDomainSum :
                  Set.Nonempty
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                      (fun x => p x + q x)) :=
                helperForTheorem_20_0_4_nonempty_effectiveDomain_sum_of_nonempty_dom_left_inter_ri_right
                  (p := p) (q := q) hproperP hproperQ' hnonemptyDomInterRi'
              let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
                fun i => Fin.cases p (fun _ => q) i
              have hproperTwo :
                  ∀ i : Fin 2,
                    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
                intro i
                fin_cases i
                · simpa [fTwo] using hproperP
                · simpa [fTwo] using hproperQ'
              have hproperSum :
                  ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                    (fun x => p x + q x) := by
                have hsumExists : ∃ x : Fin n → ℝ, (∑ i : Fin 2, fTwo i x) ≠ (⊤ : EReal) := by
                  rcases hnonemptyEffectiveDomainSum with ⟨x0, hx0DomSum⟩
                  refine ⟨x0, ?_⟩
                  have hx0NotTop :
                      (fun x => p x + q x) x0 ≠ (⊤ : EReal) :=
                    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
                      (f := fun x => p x + q x) (x := x0) hx0DomSum
                  simpa [fTwo, Fin.sum_univ_two] using hx0NotTop
                have hproperSumPack :
                    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                      (fun x => ∑ i : Fin 2, fTwo i x) :=
                  properConvexFunctionOn_sum_of_exists_ne_top (f := fTwo) hproperTwo hsumExists
                simpa [fTwo, Fin.sum_univ_two] using hproperSumPack
              have hclosureSumClosed :
                  ClosedConvexFunction (convexFunctionClosure (fun x => p x + q x)) :=
                (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
                  (f := fun x => p x + q x) hproperSum).1.1
              have hclosureSum_le_sumWithRightClosure :
                  convexFunctionClosure (fun x => p x + q x) ≤
                    (fun x => p x + convexFunctionClosure q x) := by
                intro y
                rcases hnonemptyDomInterRi' with ⟨x0E, hx0E⟩
                let yE : EuclideanSpace ℝ (Fin n) :=
                  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm y
                let seg : ℝ → (Fin n → ℝ) :=
                  fun t => (1 - t) • x0E.ofLp + t • yE.ofLp
                have hsegCont : Continuous seg := by
                  refine
                    ((continuous_const.sub continuous_id).smul continuous_const).add
                      (continuous_id.smul continuous_const)
                have hlimSeg :
                    Filter.Tendsto seg
                      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
                      (nhds yE.ofLp) := by
                  have hlimSeg' :
                      Filter.Tendsto seg (nhds (1 : ℝ))
                        (nhds ((1 - (1 : ℝ)) • x0E.ofLp + (1 : ℝ) • yE.ofLp)) :=
                    hsegCont.continuousAt.tendsto
                  exact
                    (by
                      simpa [seg] using tendsto_nhdsWithin_of_tendsto_nhds hlimSeg')
                have hlimP :
                    Filter.Tendsto
                      (fun t : ℝ => p (seg t))
                      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
                      (nhds (p yE.ofLp)) := by
                  simpa [seg] using
                    (closedProperConvexFunction_eq_limit_along_segment
                      (f := p) hclosedP hproperP (x := x0E) hx0E.1 yE)
                have hlimQ :
                    Filter.Tendsto
                      (fun t : ℝ => q (seg t))
                      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
                      (nhds (convexFunctionClosure q yE.ofLp)) := by
                  simpa [seg] using
                    ((convexFunctionClosure_eq_limit_along_segment
                      (f := q) (x := x0E) hx0E.2).1 hproperQ' yE)
                have hp_notBot : p yE.ofLp ≠ (⊥ : EReal) :=
                  hproperP.2.2 yE.ofLp (by simp)
                have hqcl_notBot : convexFunctionClosure q yE.ofLp ≠ (⊥ : EReal) :=
                  hproperQcl.2.2 yE.ofLp (by simp)
                have hlimSum :
                    Filter.Tendsto
                      (fun t : ℝ => p (seg t) + q (seg t))
                      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
                      (nhds (p yE.ofLp + convexFunctionClosure q yE.ofLp)) := by
                  have hcont :
                      ContinuousAt (fun z : EReal × EReal => z.1 + z.2)
                        (p yE.ofLp, convexFunctionClosure q yE.ofLp) :=
                    EReal.continuousAt_add
                      (h := Or.inr hqcl_notBot)
                      (h' := Or.inl hp_notBot)
                  have hpair :
                      Filter.Tendsto
                        (fun t : ℝ => (p (seg t), q (seg t)))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
                        (nhds (p yE.ofLp, convexFunctionClosure q yE.ofLp)) := by
                    simpa [nhds_prod_eq] using hlimP.prodMk hlimQ
                  simpa [Function.comp] using hcont.tendsto.comp hpair
                have hlsWithin :
                    LowerSemicontinuousWithinAt
                      (fun t : ℝ => convexFunctionClosure (fun x => p x + q x) (seg t))
                      (Set.Iio (1 : ℝ)) (1 : ℝ) := by
                  exact
                    (hclosureSumClosed.2.comp_continuous hsegCont).lowerSemicontinuousWithinAt
                      (Set.Iio (1 : ℝ)) (1 : ℝ)
                have hleLiminfClosure :
                    convexFunctionClosure (fun x => p x + q x) yE.ofLp ≤
                      Filter.liminf
                        (fun t : ℝ => convexFunctionClosure (fun x => p x + q x) (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) := by
                  simpa [seg] using hlsWithin.le_liminf
                have hclLeEventually :
                    ∀ᶠ t : ℝ in nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)),
                      convexFunctionClosure (fun x => p x + q x) (seg t) ≤
                        p (seg t) + q (seg t) := by
                  refine Filter.Eventually.of_forall ?_
                  intro t
                  exact (convexFunctionClosure_le_self (f := fun x => p x + q x)) (seg t)
                have hleLiminf :
                    Filter.liminf
                        (fun t : ℝ => convexFunctionClosure (fun x => p x + q x) (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) ≤
                      Filter.liminf
                        (fun t : ℝ => p (seg t) + q (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) :=
                  Filter.liminf_le_liminf hclLeEventually
                have hnb :
                    (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))).NeBot :=
                  nhdsWithin_Iio_neBot (H := le_rfl)
                have hliminfSum :
                    Filter.liminf
                        (fun t : ℝ => p (seg t) + q (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) =
                      p yE.ofLp + convexFunctionClosure q yE.ofLp := by
                  letI : (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))).NeBot := hnb
                  exact hlimSum.liminf_eq
                calc
                  convexFunctionClosure (fun x => p x + q x) y =
                      convexFunctionClosure (fun x => p x + q x) yE.ofLp := by
                        simp [yE]
                  _ ≤
                      Filter.liminf
                        (fun t : ℝ => convexFunctionClosure (fun x => p x + q x) (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) := hleLiminfClosure
                  _ ≤
                      Filter.liminf
                        (fun t : ℝ => p (seg t) + q (seg t))
                        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) := hleLiminf
                  _ = p yE.ofLp + convexFunctionClosure q yE.ofLp := hliminfSum
                  _ = p y + convexFunctionClosure q y := by simp [yE]
              intro z hz
              rcases hz with ⟨u, hu, rfl⟩
              refine ⟨u, ?_, rfl⟩
              rcases hu with ⟨hu_univ, hu_epi⟩
              refine ⟨hu_univ, ?_⟩
              exact le_trans (hclosureSum_le_sumWithRightClosure u.1) hu_epi
            · intro z hz
              rcases hz with ⟨u, hu, rfl⟩
              refine ⟨u, ?_, rfl⟩
              rcases hu with ⟨hu_univ, hu_epi⟩
              refine ⟨hu_univ, ?_⟩
              have hproperQcl :
                  ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                    (convexFunctionClosure q) :=
                (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
                  (f := q) hproperQ').1.2
              have hsumWithRightClosure_notBot :
                  ∀ x : Fin n → ℝ,
                    (fun x => p x + convexFunctionClosure q x) x ≠ (⊥ : EReal) := by
                intro x
                have hp_notBot : p x ≠ (⊥ : EReal) :=
                  hproperP.2.2 x (by simp)
                have hqcl_notBot : convexFunctionClosure q x ≠ (⊥ : EReal) :=
                  hproperQcl.2.2 x (by simp)
                have hsum_notBot :
                    (∑ i : Fin 2,
                      (Fin.cases (p x) (fun _ => convexFunctionClosure q x) i)) ≠
                      (⊥ : EReal) := by
                  refine
                    finset_sum_ne_bot_of_forall
                      (s := (Finset.univ : Finset (Fin 2)))
                      (f := fun i : Fin 2 =>
                        Fin.cases (p x) (fun _ => convexFunctionClosure q x) i) ?_
                  intro i hi
                  fin_cases i
                  · simpa using hp_notBot
                  · simpa using hqcl_notBot
                simpa [Fin.sum_univ_two] using hsum_notBot
              have hsumWithRightClosure_eq_closure :
                  convexFunctionClosure (fun x => p x + convexFunctionClosure q x) =
                    (fun x => p x + convexFunctionClosure q x) :=
                convexFunctionClosure_eq_of_closedConvexFunction
                  (f := fun x => p x + convexFunctionClosure q x)
                  hsumWithRightClosureClosed hsumWithRightClosure_notBot
              have hsumWithRightClosure_le_sum :
                  (fun x => p x + convexFunctionClosure q x) ≤
                    (fun x => p x + q x) := by
                intro x
                exact add_le_add le_rfl ((convexFunctionClosure_le_self (f := q)) x)
              have hsumWithRightClosure_le_closureSum :
                  (fun x => p x + convexFunctionClosure q x) ≤
                    convexFunctionClosure (fun x => p x + q x) := by
                have hmono :
                    convexFunctionClosure (fun x => p x + convexFunctionClosure q x) ≤
                      convexFunctionClosure (fun x => p x + q x) :=
                  convexFunctionClosure_mono
                    (f1 := fun x => p x + convexFunctionClosure q x)
                    (f2 := fun x => p x + q x)
                    hsumWithRightClosure_le_sum
                intro x
                simpa [hsumWithRightClosure_eq_closure] using hmono x
              exact le_trans (hsumWithRightClosure_le_closureSum u.1) hu_epi
        exact
          helperForText_19_0_9_transformedImageCoord_eq_implies_function_eq
            (hImageEq := hImageEq)

/-- Helper for Theorem 20.0.4: from a common relative-interior point of the two
effective domains, the two-block sum-of-closures identity follows by Section 16. -/
lemma helperForTheorem_20_0_4_two_block_sumClosure_eq_closure_sum_of_nonempty_ri_inter
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
    (fun x => convexFunctionClosure p x + convexFunctionClosure q x) =
      convexFunctionClosure (fun x => p x + q x) := by
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases p (fun _ => q) i
  have hfTwoZero : fTwo 0 = p := by
    rfl
  have hfTwoOne : fTwo 1 = q := by
    rfl
  have hproperTwo :
      ∀ i : Fin 2,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hproperP
    · simpa [fTwo] using hproperQ
  have hriTwo :
      Set.Nonempty
        (⋂ i : Fin 2,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i))) := by
    rcases hriInter with ⟨x0, hx0⟩
    refine ⟨x0, Set.mem_iInter.2 ?_⟩
    intro i
    fin_cases i
    · simpa [fTwo] using hx0.1
    · simpa [fTwo] using hx0.2
  have hsumTwo :
      (fun x => ∑ i : Fin 2, convexFunctionClosure (fTwo i) x) =
        convexFunctionClosure (fun x => ∑ i : Fin 2, fTwo i x) :=
    section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
      (f := fTwo) hproperTwo hriTwo
  calc
    (fun x => convexFunctionClosure p x + convexFunctionClosure q x) =
        (fun x => ∑ i : Fin 2, convexFunctionClosure (fTwo i) x) := by
      funext x
      rw [Fin.sum_univ_two]
      simpa [hfTwoZero, hfTwoOne]
    _ = convexFunctionClosure (fun x => ∑ i : Fin 2, fTwo i x) := hsumTwo
    _ = convexFunctionClosure (fun x => p x + q x) := by
      congr 1
      funext x
      rw [Fin.sum_univ_two]
      simpa [hfTwoZero, hfTwoOne]

/-- Helper for Theorem 20.0.4: mixed two-block closure bridge from a polyhedral left
block and a `dom/ri` witness. -/
lemma helperForTheorem_20_0_4_mixed_two_block_closure_add_of_polyhedral_left_dom_and_ri_right_of_nonempty_leftBlock
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hpolyP : IsPolyhedralConvexFunction n p)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p)
    (hproperQ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q)
    (hdomRiWitness :
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    (fun x => p x + convexFunctionClosure q x) =
      convexFunctionClosure (fun x => p x + q x) := by
  have hnonemptyDomInterRi :
      Set.Nonempty
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)
          ∩
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) :=
    helperForTheorem_20_0_4_ri_transfer_of_polyhedral_left_and_dom_ri_witness
      (p := p) (q := q) hpolyP hproperP hproperQ hdomRiWitness
  have hsumClosure :
      (fun x => convexFunctionClosure p x + convexFunctionClosure q x) =
        convexFunctionClosure (fun x => p x + q x) :=
    helperForTheorem_20_0_4_mixed_two_block_sumClosure_eq_closure_sum_of_nonempty_dom_left_inter_ri_right
      (p := p) (q := q) hpolyP hproperP hproperQ hnonemptyDomInterRi
  calc
    (fun x => p x + convexFunctionClosure q x) =
        (fun x => convexFunctionClosure p x + convexFunctionClosure q x) :=
      helperForTheorem_20_0_4_left_add_eq_leftClosure_add_of_polyhedral_proper
        (p := p) (q := q) hpolyP hproperP
    _ = convexFunctionClosure (fun x => p x + q x) := hsumClosure

/-- Helper for Theorem 20.0.4: reduced mixed bridge after splitting into poly/nonpoly
filter blocks. -/
lemma helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered_of_Ipoly_empty
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))))
    (hIpolyEmpty : Ipoly = ∅) :
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
      convexFunctionClosure
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  have hleftFilter :
      Finset.univ.filter (fun i : Fin m => i ∈ Ipoly) = ∅ := by
    ext i
    simp [hIpolyEmpty]
  have hnonpoly :
      (fun x =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    simpa using
      helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
  calc
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
      funext x
      simp [hleftFilter]
    _ =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) :=
      hnonpoly
    _ =
        convexFunctionClosure
          (fun x =>
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
      simp [hleftFilter]

/-- Helper for Theorem 20.0.4: reduced mixed bridge after splitting into poly/nonpoly
filter blocks. -/
lemma helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x =>
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
      convexFunctionClosure
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  classical
  by_cases hIpolyEmpty : Ipoly = ∅
  · exact
      helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered_of_Ipoly_empty
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri) hIpolyEmpty
  ·
    let p : (Fin n → ℝ) → EReal :=
      fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x
    let q : (Fin n → ℝ) → EReal :=
      fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x
    have hqClosure :
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
          convexFunctionClosure q := by
      simpa [q] using
        helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hpPack :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p ∧
          ∃ x0 : Fin n → ℝ,
            x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p := by
      simpa [p] using
        helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
          (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
    have hcore :
        (fun x => p x + convexFunctionClosure q x) =
          convexFunctionClosure (fun x => p x + q x) := by
      rcases hpPack with ⟨hproperP, _hdomP⟩
      have hpolyP :
          IsPolyhedralConvexFunction n p := by
        simpa [p] using
          helperForTheorem_20_0_4_poly_filter_block_isPolyhedral_of_nonempty
            (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper)
            (hdom_ri := hdom_ri) (hIpolyNonempty := hIpolyEmpty)
      have hdomRiWitness :
          ∃ x0 : Fin n → ℝ,
            x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
            (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
              euclideanRelativeInterior n
                ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
        simpa [p, q] using
          helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
            (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
      have hproperQ :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) q := by
        simpa [q] using
          helperForTheorem_20_0_4_nonpoly_filter_block_proper
            (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_ri)
      exact
        helperForTheorem_20_0_4_mixed_two_block_closure_add_of_polyhedral_left_dom_and_ri_right_of_nonempty_leftBlock
          (p := p) (q := q) hpolyP hproperP hproperQ hdomRiWitness
    have hleft :
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
          (fun x => p x + convexFunctionClosure q x) := by
      funext x
      have hqAt :
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
            convexFunctionClosure q x := by
        simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g x) hqClosure
      simp [p, hqAt]
    calc
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) =
          (fun x => p x + convexFunctionClosure q x) := hleft
      _ = convexFunctionClosure (fun x => p x + q x) := hcore
      _ =
          convexFunctionClosure
            (fun x =>
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
        simp [p, q]

lemma helperForTheorem_20_0_4_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_mixed
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
      convexFunctionClosure (fun x => ∑ i, f i x) := by
  classical
  rcases
    helperForTheorem_20_0_4_splitSums_poly_nonpoly_blocks
      (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper)
      with ⟨hsplitClosure, hsplitRaw⟩
  calc
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
        (fun x =>
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) :=
      hsplitClosure
    _ =
        convexFunctionClosure
          (fun x =>
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
            (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) :=
      helperForTheorem_20_0_4_mixedQualification_sumClosure_bridge_filtered
        (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)
    _ = convexFunctionClosure (fun x => ∑ i, f i x) := by
      simpa [hsplitRaw.symm]


end Section20
end Chap04
