/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part12

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Theorem 20.1: in the `k = 0` branch, the mixed hypothesis reduces
to a full relative-interior qualification, so Section 16 gives equality and the
top-case can be converted to an attainment witness using `0 < m`. -/
lemma helperForTheorem_20_1_case_kEqZero_from_section16
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hk0 : k = 0)
    (hmPos : 0 < m)
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
  rcases hdom_ri with ⟨x0E, hx0E⟩
  have hriAll :
      Set.Nonempty
        (⋂ i : Fin m,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
    refine ⟨x0E, Set.mem_iInter.2 ?_⟩
    intro i
    have hRight :
        x0E ∈
          ⋂ j : {j : Fin m // k ≤ j.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.2
    have hkLe : k ≤ i.1 := by
      simpa [hk0] using (Nat.zero_le i.1)
    simpa using (Set.mem_iInter.mp hRight) ⟨i, hkLe⟩
  have hsec16 :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      (∀ xStar : Fin n → ℝ,
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar) :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := f) hproper hriAll
  refine ⟨hsec16.1, ?_⟩
  intro xStar
  rcases hsec16.2 xStar with htop | hatt
  · rcases
      section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
        (n := n) (m := m) hmPos
        (g := fun i => fenchelConjugate n (f i))
        (xStar := xStar) htop with
      ⟨xStarFamily, hsumFamily, hvalueFamily⟩
    refine ⟨xStarFamily, hsumFamily, ?_⟩
    simpa using hvalueFamily.symm
  · rcases hatt with ⟨xStarFamily, hsumFamily, hvalueFamily⟩
    refine ⟨xStarFamily, hsumFamily, ?_⟩
    simpa using hvalueFamily.symm

/-- Helper for Theorem 20.1: in the `k = m` branch, all summands are polyhedral
and the mixed witness yields a common domain point, so the polyhedral refinement
with attainment applies directly. -/
lemma helperForTheorem_20_1_case_kEqm_from_allPoly_refinement
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hkm : k = m)
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
  rcases
      helperForTheorem_20_1_allPoly_data_of_k_eq_m
        (f := f) hkm hpoly hdom_ri with
    ⟨hpolyAll, hdomAll⟩
  refine ⟨?_, ?_⟩
  · exact
      fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
        (f := f) hpolyAll hproper hdomAll
  · intro xStar
    exact
      infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
        (f := f) (hpoly := hpolyAll) (hproper := hproper) (hdom := hdomAll)
        (hmPos := hmPos) (xStar := xStar)

end Section20
end Chap04
