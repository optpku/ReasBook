/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part4

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Theorem 20.0.4: mixed two-block closure bridge from a polyhedral left
block and a `dom/ri` witness. -/
lemma helperForTheorem_20_0_4_mem_preimage_effectiveDomain_of_equivSymm
    {n : ℕ} (p : (Fin n → ℝ) → EReal) {x0 : Fin n → ℝ}
    (hx0DomP : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) :
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) := by
  simpa using hx0DomP

/-- Helper for Theorem 20.0.4: the `WithLp.toLp` image description of an effective
domain agrees with the Euclidean-space preimage description. -/
lemma helperForTheorem_20_0_4_image_effectiveDomain_eq_preimage_effectiveDomain
    {n : ℕ} (q : (Fin n → ℝ) → EReal) :
    ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) =
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    simpa [WithLp.ofLp_toLp] using hx'
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · simpa using hx
    · simpa [WithLp.toLp_ofLp]

/-- Helper for Theorem 20.0.4: a mixed `dom/ri` witness yields a point in the
left effective domain preimage and in the right relative-interior preimage. -/
lemma helperForTheorem_20_0_4_exists_preimageDom_and_riPreimage_point_of_dom_ri_witness
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hdomRiWitness :
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) p ∧
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q))) :
    ∃ x0E : EuclideanSpace ℝ (Fin n),
      x0E ∈
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) ∧
        x0E ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
  rcases hdomRiWitness with ⟨x0, hx0DomP, hx0RiQImage⟩
  let x0E : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0
  have hqImageEqPreimage :
      ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) =
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) :=
    helperForTheorem_20_0_4_image_effectiveDomain_eq_preimage_effectiveDomain
      (q := q)
  have hx0RiQPreimage :
      x0E ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
    simpa [x0E, hqImageEqPreimage] using hx0RiQImage
  have hx0MemPPreimage :
      x0E ∈
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) := by
    simpa [x0E] using
      helperForTheorem_20_0_4_mem_preimage_effectiveDomain_of_equivSymm
        (p := p) (x0 := x0) hx0DomP
  exact ⟨x0E, hx0MemPPreimage, hx0RiQPreimage⟩

/-- Helper for Theorem 20.0.4: a nonempty mixed preimage intersection yields an
explicit mixed `dom/ri` witness in the original coordinates. -/
lemma helperForTheorem_20_0_4_extract_dom_ri_witness_of_nonempty_preimageDom_inter_riPreimage
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
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
  rcases hnonemptyDomInterRi with ⟨x0E, hx0E⟩
  refine ⟨(x0E : Fin n → ℝ), hx0E.1, ?_⟩
  have hqImageEqPreimage :
      ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) =
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) :=
    helperForTheorem_20_0_4_image_effectiveDomain_eq_preimage_effectiveDomain
      (q := q)
  have hx0EriImage :
      x0E ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q)) := by
    simpa [hqImageEqPreimage] using hx0E.2
  have hx0Esymm :
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm (x0E : Fin n → ℝ) = x0E := by
    simp
  simpa [hx0Esymm] using hx0EriImage

/-- Helper for Theorem 20.0.4: a mixed `dom/ri` witness induces a nonempty
intersection of the left effective-domain preimage and the right relative-interior
preimage. -/
lemma helperForTheorem_20_0_4_nonempty_preimageDom_inter_riPreimage_of_dom_ri_witness
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
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
  rcases
      helperForTheorem_20_0_4_exists_preimageDom_and_riPreimage_point_of_dom_ri_witness
        (p := p) (q := q) hdomRiWitness with
    ⟨x0E, hx0MemPPreimage, hx0RiQPreimage⟩
  exact ⟨x0E, ⟨hx0MemPPreimage, hx0RiQPreimage⟩⟩

/-- Helper for Theorem 20.0.4: mixed two-block closure bridge from a polyhedral left
block and a `dom/ri` witness. -/
lemma helperForTheorem_20_0_4_convex_preimage_effectiveDomain_of_proper
    {n : ℕ} (p : (Fin n → ℝ) → EReal)
    (hproperP : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) p) :
    Convex ℝ
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) p)) := by
  have hconvDom :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := p) hproperP.1
  simpa using
    hconvDom.linear_preimage ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).toLinearMap)

/-- Helper for Theorem 20.0.4: from a nonempty mixed intersection,
the left effective-domain preimage is nonempty. -/
lemma helperForTheorem_20_0_4_nonempty_preimage_effectiveDomain_left_of_nonempty_dom_inter_ri_right
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
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) := by
  rcases hnonemptyDomInterRi with ⟨x0E, hx0E⟩
  exact ⟨x0E, hx0E.1⟩

end Section20
end Chap04
