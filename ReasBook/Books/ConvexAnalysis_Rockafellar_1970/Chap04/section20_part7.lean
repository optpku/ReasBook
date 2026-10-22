/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part6

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Theorem 20.0.4: Let `f₁, …, fₘ` be proper convex functions on `ℝⁿ`, let
`I_poly` be the set of indices for which `fᵢ` is polyhedral, and let
`I_gen = I_polyᶜ`. If

`(⋂_{i ∈ I_poly} dom fᵢ) ∩ (⋂_{i ∈ I_gen} ri (dom fᵢ)) ≠ ∅`,

then

`(f₁ + ⋯ + fₘ)^* = cl (f₁^* □ ⋯ □ fₘ^*)`.

Here `dom fᵢ` is `effectiveDomain univ (f i)`, `ri` is `euclideanRelativeInterior`,
`^*` is `fenchelConjugate`, `□` is `infimalConvolutionFamily`, and `cl` is
`convexFunctionClosure`. -/
theorem fenchelConjugate_sum_eq_convexFunctionClosure_infimalConvolutionFamily_of_nonempty_iInter_dom_poly_iInter_ri_nonpoly
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
    fenchelConjugate n (fun x => ∑ i, f i x) =
      convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  have hsum :
      (fun x => ∑ i, convexFunctionClosure (f i) x) =
        convexFunctionClosure (fun x => ∑ i, f i x) :=
    helperForTheorem_20_0_4_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_mixed
      (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) (hdom_ri := hdom_ri)
  calc
    fenchelConjugate n (fun x => ∑ i, f i x) =
        fenchelConjugate n (convexFunctionClosure (fun x => ∑ i, f i x)) := by
          symm
          simpa using
            (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := fun x => ∑ i, f i x))
    _ = fenchelConjugate n (fun x => ∑ i, convexFunctionClosure (f i) x) := by
          simpa [hsum]
    _ = convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
          simpa using
            (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
              (f := f) hproper)

/-- Helper for Theorem 20.1: with an empty index family in positive dimension,
universal split-attainment for the conjugate infimal-convolution family is impossible. -/
lemma helperForTheorem_20_1_exists_nonzero_dualVector_of_pos_dim
    {n : ℕ} (hn : 0 < n) :
    ∃ xStar : Fin n → ℝ, xStar ≠ 0 := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => if i = i0 then (1 : ℝ) else 0, ?_⟩
  intro hxStarZero
  have hAtI0 : (if i0 = i0 then (1 : ℝ) else 0) = (0 : Fin n → ℝ) i0 := by
    exact congrArg (fun g => g i0) hxStarZero
  have hOneEqZero : (1 : ℝ) = 0 := by
    simpa using hAtI0
  exact one_ne_zero hOneEqZero

/-- Helper for Theorem 20.1: any `Fin 0` decomposition of dual vectors sums to zero. -/
lemma helperForTheorem_20_1_sum_dualFamily_eq_zero_of_empty_index
    {n : ℕ} (xStarFamily : Fin 0 → Fin n → ℝ) :
    (∑ i, xStarFamily i) = 0 := by
  simp

/-- Helper for Theorem 20.1: with an empty index family in positive dimension,
universal split-attainment for the conjugate infimal-convolution family is impossible. -/
lemma helperForTheorem_20_1_not_universalAttainment_of_empty_index_of_pos_dim
    {n : ℕ} (hn : 0 < n) (f : Fin 0 → (Fin n → ℝ) → EReal) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hAtt
  rcases helperForTheorem_20_1_exists_nonzero_dualVector_of_pos_dim (n := n) hn with
    ⟨xStar, hxStarNeZero⟩
  rcases hAtt xStar with ⟨xStarFamily, hsum, _⟩
  have hsumZero : (∑ i, xStarFamily i) = 0 :=
    helperForTheorem_20_1_sum_dualFamily_eq_zero_of_empty_index
      (n := n) xStarFamily
  have hxStarZero : xStar = 0 := hsum.symm.trans hsumZero
  exact hxStarNeZero hxStarZero

/-- Helper for Theorem 20.1: in the empty-index case, universal split-attainment
forces zero ambient dimension. -/
lemma helperForTheorem_20_1_dim_eq_zero_of_empty_index_of_universalAttainment
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal)
    (hAtt :
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    n = 0 := by
  by_contra hnZero
  exact
    (helperForTheorem_20_1_not_universalAttainment_of_empty_index_of_pos_dim
      (n := n) (Nat.pos_of_ne_zero hnZero) (f := f)) hAtt

/-- Helper for Theorem 20.1: the concrete empty-index one-dimensional branch
already contradicts universal split-attainment. -/
lemma helperForTheorem_20_1_universalAttainment_impossible_of_empty_index_dim_one
    (f : Fin 0 → (Fin 1 → ℝ) → EReal) :
    ¬ (∀ xStar : Fin 1 → ℝ,
        ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
              ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  exact
    helperForTheorem_20_1_not_universalAttainment_of_empty_index_of_pos_dim
      (n := 1) (by decide) (f := f)

/-- Helper for Theorem 20.1: when `m = k = 0`, the mixed `dom/ri`
qualification set is all of `EuclideanSpace ℝ (Fin n)`, hence nonempty. -/
lemma helperForTheorem_20_1_nonempty_hdom_ri_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) :
    Set.Nonempty
      ((⋂ i : {i : Fin 0 // i.1 < 0},
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
        ∩
        (⋂ i : {i : Fin 0 // 0 ≤ i.1},
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) := by
  refine ⟨0, ?_⟩
  simp

/-- Helper for Theorem 20.1: there is a one-dimensional empty-index branch
that satisfies the structural hypotheses while universal split-attainment fails. -/
lemma helperForTheorem_20_1_exists_empty_index_dim_one_counterexample :
    ∃ f : Fin 0 → (Fin 1 → ℝ) → EReal,
      (∀ i : Fin 0, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      Set.Nonempty
        ((⋂ i : {i : Fin 0 // i.1 < 0},
            ((fun x : EuclideanSpace ℝ (Fin 1) => (x : Fin 1 → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin 0 // 0 ≤ i.1},
            euclideanRelativeInterior 1
              ((fun x : EuclideanSpace ℝ (Fin 1) => (x : Fin 1 → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)))) ∧
      ¬ (∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  refine ⟨(fun i => nomatch i), ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · exact
      helperForTheorem_20_1_nonempty_hdom_ri_of_empty_index
        (n := 1) (f := fun i => nomatch i)
  · exact
      helperForTheorem_20_1_universalAttainment_impossible_of_empty_index_dim_one
        (f := fun i => nomatch i)

/-- Helper for Theorem 20.1: in the admissible one-dimensional empty-index branch,
the full theorem conclusion cannot hold because its attainment conjunct fails. -/
lemma helperForTheorem_20_1_fullConclusion_impossible_of_empty_index_dim_one
    (f : Fin 0 → (Fin 1 → ℝ) → EReal)
    (hNotAtt :
      ¬ (∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i))) :
    ¬ (fenchelConjugate 1 (fun x => ∑ i, f i x) =
          infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
        ∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  intro hFull
  exact hNotAtt hFull.2

/-- Helper for Theorem 20.1: there is an admissible one-dimensional empty-index
branch satisfying the hypotheses while the full conclusion fails. -/
lemma helperForTheorem_20_1_exists_admissible_branch_failing_full_conclusion :
    ∃ f : Fin 0 → (Fin 1 → ℝ) → EReal,
      (0 : ℕ) ≤ 0 ∧
      (∀ i : Fin 0, i.1 < 0 → IsPolyhedralConvexFunction 1 (f i)) ∧
      (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      Set.Nonempty
        ((⋂ i : {i : Fin 0 // i.1 < 0},
            ((fun x : EuclideanSpace ℝ (Fin 1) => (x : Fin 1 → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin 0 // 0 ≤ i.1},
            euclideanRelativeInterior 1
              ((fun x : EuclideanSpace ℝ (Fin 1) => (x : Fin 1 → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)))) ∧
      ¬ (fenchelConjugate 1 (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
          ∀ xStar : Fin 1 → ℝ,
            ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                  ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  rcases helperForTheorem_20_1_exists_empty_index_dim_one_counterexample with
    ⟨f, hproper, hdom_ri, hNotAtt⟩
  refine ⟨f, Nat.le_refl 0, ?_, hproper, hdom_ri, ?_⟩
  · intro i
    exact Fin.elim0 i
  · exact
      helperForTheorem_20_1_fullConclusion_impossible_of_empty_index_dim_one
        (f := f) hNotAtt

/-- Helper for Theorem 20.1: the admissible empty-index one-dimensional branch
refutes any parameter-uniform version of the theorem's full conclusion. -/
lemma helperForTheorem_20_1_not_forall_instances_of_full_conclusion :
    ¬ (∀ {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal),
          k ≤ m →
          (∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i)) →
          (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) →
          Set.Nonempty
            ((⋂ i : {i : Fin m // i.1 < k},
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
              ∩
              (⋂ i : {i : Fin m // k ≤ i.1},
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) →
          (fenchelConjugate n (fun x => ∑ i, f i x) =
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
            ∀ xStar : Fin n → ℝ,
              ∃ xStarFamily : Fin m → Fin n → ℝ,
                (∑ i, xStarFamily i) = xStar ∧
                  infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                    ∑ i, fenchelConjugate n (f i) (xStarFamily i))) := by
  intro hAll
  rcases helperForTheorem_20_1_exists_admissible_branch_failing_full_conclusion with
    ⟨f, hk, hpoly, hproper, hdom_ri, hNotFull⟩
  exact hNotFull (hAll (n := 1) (m := 0) (k := 0) f hk hpoly hproper hdom_ri)

/-- Helper for Theorem 20.1: in the branch `k = m`, all summands are polyhedral
and the mixed `dom/ri` witness yields a common effective-domain point. -/
lemma helperForTheorem_20_1_allPoly_data_of_k_eq_m
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hkm : k = m)
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
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
    (∀ i : Fin m, IsPolyhedralConvexFunction n (f i)) ∧
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact hpoly i (by simpa [hkm] using i.2)
  · rcases hdom_ri with ⟨x0E, hx0E⟩
    refine ⟨(x0E : Fin n → ℝ), ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    have hLeft :
        x0E ∈
          ⋂ j : {j : Fin m // j.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.1
    have hik : i.1 < k := by
      simpa [hkm] using i.2
    have hx0Mem :
        x0E ∈
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
      simpa using (Set.mem_iInter.mp hLeft) ⟨i, hik⟩
    simpa [Set.mem_preimage] using hx0Mem

/-- Helper for Theorem 20.1: from the textbook mixed assumptions, one obtains the
closure-level refinement `f* = cl(□ fᵢ*)` by indexing polyhedral terms via their
actual predicate. -/
lemma helperForTheorem_20_1_closure_refinement_of_mixed_assumptions
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
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
      convexFunctionClosure
        (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  classical
  let Ipoly : Set (Fin m) := fun i => IsPolyhedralConvexFunction n (f i)
  have hpolyIpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i) := by
    intro i
    rfl
  have hdom_riIpoly :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) := by
    rcases hdom_ri with ⟨x0E, hx0E⟩
    refine ⟨x0E, ?_⟩
    refine And.intro ?_ ?_
    · refine Set.mem_iInter.2 ?_
      intro i
      by_cases hik : i.1.1 < k
      · have hLeft :
            x0E ∈
              ⋂ j : {j : Fin m // j.1 < k},
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
          hx0E.1
        simpa using (Set.mem_iInter.mp hLeft) ⟨i.1, hik⟩
      · have hkLe : k ≤ i.1.1 := Nat.le_of_not_gt hik
        have hRight :
            x0E ∈
              ⋂ j : {j : Fin m // k ≤ j.1},
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
          hx0E.2
        have hx0Ri :
            x0E ∈
              euclideanRelativeInterior n
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)) := by
          simpa using (Set.mem_iInter.mp hRight) ⟨i.1, hkLe⟩
        exact
          (euclideanRelativeInterior_subset_closure n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)))).1 hx0Ri
    · refine Set.mem_iInter.2 ?_
      intro i
      have hNotLt : ¬ i.1.1 < k := by
        intro hik
        exact i.2 (hpoly i.1 hik)
      have hkLe : k ≤ i.1.1 := Nat.le_of_not_gt hNotLt
      have hRight :
          x0E ∈
            ⋂ j : {j : Fin m // k ≤ j.1},
              euclideanRelativeInterior n
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
        hx0E.2
      simpa using (Set.mem_iInter.mp hRight) ⟨i.1, hkLe⟩
  exact
    fenchelConjugate_sum_eq_convexFunctionClosure_infimalConvolutionFamily_of_nonempty_iInter_dom_poly_iInter_ri_nonpoly
      (f := f) (Ipoly := Ipoly) (hpoly := hpolyIpoly) (hproper := hproper)
      (hdom_ri := hdom_riIpoly)

/-- Helper for Theorem 20.1: the mixed textbook hypothesis yields a witness lying in
the effective domain of the filtered polyhedral block and in the relative interior of
the filtered tail block. -/
lemma helperForTheorem_20_1_nonempty_mixed_dom_ri_for_Ipoly_lt
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
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
    Set.Nonempty
      ((⋂ i : {i : Fin m // i ∈ ({i : Fin m | i.1 < k} : Set (Fin m))},
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
        ∩
        (⋂ i : {i : Fin m // i ∉ ({i : Fin m | i.1 < k} : Set (Fin m))},
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) := by
  rcases hdom_ri with ⟨x0E, hx0E⟩
  refine ⟨x0E, ?_⟩
  refine And.intro ?_ ?_
  · refine Set.mem_iInter.2 ?_
    intro i
    have hLeft :
        x0E ∈
          ⋂ j : {j : Fin m // j.1 < k},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.1
    simpa using (Set.mem_iInter.mp hLeft) ⟨i.1, i.2⟩
  · refine Set.mem_iInter.2 ?_
    intro i
    have hkLe : k ≤ i.1.1 := Nat.le_of_not_gt i.2
    have hRight :
        x0E ∈
          ⋂ j : {j : Fin m // k ≤ j.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j)) :=
      hx0E.2
    simpa using (Set.mem_iInter.mp hRight) ⟨i.1, hkLe⟩

/-- Helper for Theorem 20.1: the mixed textbook hypothesis yields a witness lying in
the effective domain of the filtered polyhedral block and in the relative interior of
the filtered tail block. -/
lemma helperForTheorem_20_1_exists_dom_poly_and_ri_tail_filtered_sum_witness
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
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
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) ∧
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x))) := by
  let Ipoly : Set (Fin m) := {i : Fin m | i.1 < k}
  have hdom_riIpoly :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :=
    helperForTheorem_20_1_nonempty_mixed_dom_ri_for_Ipoly_lt
      (f := f) (hdom_ri := hdom_ri)
  have hfilterTailEq :
      Finset.univ.filter (fun i : Fin m => i ∉ Ipoly) =
        Finset.univ.filter (fun i : Fin m => k ≤ i.1) := by
    ext i
    simp [Ipoly]
  simpa [Ipoly, hfilterTailEq] using
    helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
      (f := f) (Ipoly := Ipoly) (hproper := hproper)
      (hdom_ri := hdom_riIpoly)

/-- Helper for Theorem 20.1: the mixed textbook assumptions produce proper filtered
head/tail block sums and a mixed `dom/ri` witness for those two blocks. -/
lemma helperForTheorem_20_1_twoBlock_proper_and_domRiWitness_of_mixed_hypothesis
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
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
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) ∧
      (∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) ∧
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
            euclideanRelativeInterior n
              ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                  (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x)))) := by
  let Ipoly : Set (Fin m) := {i : Fin m | i.1 < k}
  have hdom_riIpoly :
      Set.Nonempty
        ((⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
          ∩
          (⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) :=
    helperForTheorem_20_1_nonempty_mixed_dom_ri_for_Ipoly_lt
      (f := f) (hdom_ri := hdom_ri)
  have hproperP :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    exact
      (helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_riIpoly)).1
  have hfilterTailEq :
      Finset.univ.filter (fun i : Fin m => i ∉ Ipoly) =
        Finset.univ.filter (fun i : Fin m => k ≤ i.1) := by
    ext i
    simp [Ipoly]
  have hproperQ :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x) := by
    simpa [Ipoly, hfilterTailEq] using
      helperForTheorem_20_0_4_nonpoly_filter_block_proper
        (f := f) (Ipoly := Ipoly) (hproper := hproper) (hdom_ri := hdom_riIpoly)
  have hdomRiWitnessBlock :
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) ∧
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
            euclideanRelativeInterior n
              ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
                (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                  (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), f i x))) := by
    simpa [Ipoly] using
      helperForTheorem_20_1_exists_dom_poly_and_ri_tail_filtered_sum_witness
        (f := f) (hproper := hproper) (hdom_ri := hdom_ri)
  exact ⟨by simpa [Ipoly] using hproperP, hproperQ, hdomRiWitnessBlock⟩

/-- Helper for Theorem 20.1: a mixed two-block `dom/ri` witness yields a nonempty
intersection of left-domain preimage and right-relative-interior preimage. -/
lemma helperForTheorem_20_1_nonempty_preimageDom_inter_riPreimage_of_domRiWitnessBlock
    {n : ℕ} (p q : (Fin n → ℝ) → EReal)
    (hdomRiWitnessBlock :
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
  exact
    helperForTheorem_20_0_4_nonempty_preimageDom_inter_riPreimage_of_dom_ri_witness
      (p := p) (q := q) hdomRiWitnessBlock

/-- Helper for Theorem 20.1: splitting by the index predicates `i < k` and
`k ≤ i` rewrites a full finite sum of piecewise-defined values into two subtype sums. -/
lemma helperForTheorem_20_1_sum_piecewise_lt_ge
    {m k : ℕ} {α : Type*} [AddCommMonoid α]
    (headVal : {i : Fin m // i.1 < k} → α)
    (tailVal : {i : Fin m // k ≤ i.1} → α) :
    (∑ i : Fin m,
        if hi : i.1 < k then headVal ⟨i, hi⟩ else tailVal ⟨i, Nat.le_of_not_gt hi⟩) =
      (∑ i : {i : Fin m // i.1 < k}, headVal i) +
      (∑ i : {i : Fin m // k ≤ i.1}, tailVal i) := by
  classical
  let splitVal : Fin m → α := fun i =>
    if hi : i.1 < k then headVal ⟨i, hi⟩ else tailVal ⟨i, Nat.le_of_not_gt hi⟩
  have hsplit :
      (∑ i : Fin m, splitVal i) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), splitVal i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), splitVal i) := by
    simpa [splitVal] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i.1 < k) (f := splitVal)).symm
  have hheadFilter :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), splitVal i) =
        ∑ i : {i : Fin m // i.1 < k}, headVal i := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), splitVal i) =
          ∑ i : {i : Fin m // i.1 < k}, splitVal i.1 := by
            symm
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin m)))
                (p := fun i : Fin m => i.1 < k) (f := splitVal))
      _ = ∑ i : {i : Fin m // i.1 < k}, headVal i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [splitVal, i.2]
  have hfilterTailEq :
      Finset.univ.filter (fun i : Fin m => ¬ i.1 < k) =
        Finset.univ.filter (fun i : Fin m => k ≤ i.1) := by
    ext i
    simp [Nat.not_lt]
  have htailFilter :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), splitVal i) =
        ∑ i : {i : Fin m // k ≤ i.1}, tailVal i := by
    calc
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), splitVal i) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => k ≤ i.1), splitVal i) := by
            rw [hfilterTailEq]
      _ = ∑ i : {i : Fin m // k ≤ i.1}, splitVal i.1 := by
            symm
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin m)))
                (p := fun i : Fin m => k ≤ i.1) (f := splitVal))
      _ = ∑ i : {i : Fin m // k ≤ i.1}, tailVal i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hnot : ¬ i.1.1 < k := Nat.not_lt_of_ge i.2
            simp [splitVal, hnot]
  calc
    (∑ i : Fin m,
        if hi : i.1 < k then headVal ⟨i, hi⟩ else tailVal ⟨i, Nat.le_of_not_gt hi⟩) =
        ∑ i : Fin m, splitVal i := by
          simp [splitVal]
    _ =
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), splitVal i) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), splitVal i) :=
      hsplit
    _ = (∑ i : {i : Fin m // i.1 < k}, headVal i) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.1 < k), splitVal i) := by
      rw [hheadFilter]
    _ = (∑ i : {i : Fin m // i.1 < k}, headVal i) +
          (∑ i : {i : Fin m // k ≤ i.1}, tailVal i) := by
      rw [htailFilter]

/-- Helper for Theorem 20.1: combine a poly-block split family and a tail-block split
family into one full-index split family with the prescribed total sum. -/
lemma helperForTheorem_20_1_liftWitness_polyBlock_tailBlock_to_fullFamily
    {n m k : ℕ} {xStar xHead xTail : Fin n → ℝ}
    (headFamily : {i : Fin m // i.1 < k} → Fin n → ℝ)
    (tailFamily : {i : Fin m // k ≤ i.1} → Fin n → ℝ)
    (hHeadSum : (∑ i, headFamily i) = xHead)
    (hTailSum : (∑ i, tailFamily i) = xTail)
    (hHeadTail : xHead + xTail = xStar) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar := by
  let xStarFamily : Fin m → Fin n → ℝ := fun i =>
    if hi : i.1 < k then headFamily ⟨i, hi⟩ else tailFamily ⟨i, Nat.le_of_not_gt hi⟩
  refine ⟨xStarFamily, ?_⟩
  calc
    (∑ i, xStarFamily i) =
        (∑ i : {i : Fin m // i.1 < k}, headFamily i) +
        (∑ i : {i : Fin m // k ≤ i.1}, tailFamily i) := by
          simpa [xStarFamily] using
            helperForTheorem_20_1_sum_piecewise_lt_ge
              (m := m) (k := k) (headVal := headFamily) (tailVal := tailFamily)
    _ = xHead + xTail := by
          simp [hHeadSum, hTailSum]
    _ = xStar := hHeadTail

/-- Helper for Theorem 20.1: lifting head/tail split families to a full-index split
family preserves both the total dual sum and the corresponding split conjugate-value
sum identity. -/
lemma helperForTheorem_20_1_liftWitness_polyBlock_tailBlock_to_fullFamily_with_valueSum
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    {xStar xHead xTail : Fin n → ℝ}
    (headFamily : {i : Fin m // i.1 < k} → Fin n → ℝ)
    (tailFamily : {i : Fin m // k ≤ i.1} → Fin n → ℝ)
    (hHeadSum : (∑ i, headFamily i) = xHead)
    (hTailSum : (∑ i, tailFamily i) = xTail)
    (hHeadTail : xHead + xTail = xStar) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
          (∑ i : {i : Fin m // i.1 < k}, fenchelConjugate n (f i.1) (headFamily i)) +
          (∑ i : {i : Fin m // k ≤ i.1}, fenchelConjugate n (f i.1) (tailFamily i)) := by
  let xStarFamily : Fin m → Fin n → ℝ := fun i =>
    if hi : i.1 < k then headFamily ⟨i, hi⟩ else tailFamily ⟨i, Nat.le_of_not_gt hi⟩
  refine ⟨xStarFamily, ?_, ?_⟩
  · calc
      (∑ i, xStarFamily i) =
          (∑ i : {i : Fin m // i.1 < k}, headFamily i) +
          (∑ i : {i : Fin m // k ≤ i.1}, tailFamily i) := by
            simpa [xStarFamily] using
              helperForTheorem_20_1_sum_piecewise_lt_ge
                (m := m) (k := k) (headVal := headFamily) (tailVal := tailFamily)
      _ = xHead + xTail := by
            simp [hHeadSum, hTailSum]
      _ = xStar := hHeadTail
  · have hsumConjSplit :
        (∑ i : Fin m,
            if hi : i.1 < k then
              fenchelConjugate n (f i) (headFamily ⟨i, hi⟩)
            else
              fenchelConjugate n (f i) (tailFamily ⟨i, Nat.le_of_not_gt hi⟩)) =
          (∑ i : {i : Fin m // i.1 < k}, fenchelConjugate n (f i.1) (headFamily i)) +
            (∑ i : {i : Fin m // k ≤ i.1}, fenchelConjugate n (f i.1) (tailFamily i)) :=
      helperForTheorem_20_1_sum_piecewise_lt_ge
        (m := m) (k := k)
        (headVal := fun i : {i : Fin m // i.1 < k} =>
          fenchelConjugate n (f i.1) (headFamily i))
        (tailVal := fun i : {i : Fin m // k ≤ i.1} =>
          fenchelConjugate n (f i.1) (tailFamily i))
    calc
      (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
          (∑ i : Fin m,
            if hi : i.1 < k then
              fenchelConjugate n (f i) (headFamily ⟨i, hi⟩)
            else
              fenchelConjugate n (f i) (tailFamily ⟨i, Nat.le_of_not_gt hi⟩)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hik : i.1 < k
            · simp [xStarFamily, hik]
            · simp [xStarFamily, hik]
      _ =
          (∑ i : {i : Fin m // i.1 < k}, fenchelConjugate n (f i.1) (headFamily i)) +
            (∑ i : {i : Fin m // k ≤ i.1}, fenchelConjugate n (f i.1) (tailFamily i)) :=
        hsumConjSplit

/-- Helper for Theorem 20.1: under a two-block relative-interior qualification,
Section 16 gives exact binary conjugate/infimal-convolution equality and split
attainment in `(x⋆ - y, y)` form. -/
lemma helperForTheorem_20_1_binary_exact_topOrAttained_polyLeft_domRi_via_section16
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
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases p (fun _ => q) i
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
  have hsec16 :
      (fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i))) ∧
        (∀ xStar : Fin n → ℝ,
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) xStar = ⊤ ∨
            ∃ xStarFamily : Fin 2 → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                (∑ i, fenchelConjugate n (fTwo i) (xStarFamily i)) =
                  infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) xStar) :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := fTwo) hproperTwo hriTwo
  refine And.intro ?_ ?_
  · simpa [fTwo, Fin.sum_univ_two, infimalConvolution_eq_infimalConvolutionFamily_two] using hsec16.1
  · intro xStar
    rcases hsec16.2 xStar with htop | hatt
    · exact Or.inl (by
        simpa [fTwo, infimalConvolution_eq_infimalConvolutionFamily_two] using htop)
    · rcases hatt with ⟨xStarFamily, hsum, hval⟩
      refine Or.inr ?_
      refine ⟨xStarFamily 1, ?_⟩
      have hsum' : xStarFamily 0 + xStarFamily 1 = xStar := by
        simpa [Fin.sum_univ_two] using hsum
      have hsplit : xStar - xStarFamily 1 = xStarFamily 0 := by
        apply (sub_eq_iff_eq_add).2
        simpa [add_comm, add_left_comm, add_assoc] using hsum'.symm
      have hval' :
          fenchelConjugate n p (xStar - xStarFamily 1) + fenchelConjugate n q (xStarFamily 1) =
            infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) xStar := by
        simpa [fTwo, Fin.sum_univ_two, hsplit] using hval
      have hInfEq :
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) =
            infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) := by
        calc
          infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) =
              infimalConvolutionFamily
                (fun i : Fin 2 => if i = 0 then fenchelConjugate n p else fenchelConjugate n q) := by
                  exact
                    infimalConvolution_eq_infimalConvolutionFamily_two
                      (f := fenchelConjugate n p) (g := fenchelConjugate n q)
          _ = infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) := by
                congr 1
                funext i
                fin_cases i <;> rfl
      calc
        infimalConvolution (fenchelConjugate n p) (fenchelConjugate n q) xStar =
            infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) xStar := by
              exact congrArg (fun g : (Fin n → ℝ) → EReal => g xStar) hInfEq
        _ = fenchelConjugate n p (xStar - xStarFamily 1) + fenchelConjugate n q (xStarFamily 1) :=
          hval'.symm

/-- Helper for Theorem 20.1: a nonempty filtered index block whose members are
polyhedral gives a polyhedral filtered block-sum. -/
lemma helperForTheorem_20_1_polyhedral_filteredBlock_of_membership_polyhedral
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpolyMem : ∀ i : Fin m, i ∈ Ipoly → IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : {i : Fin m // i ∈ Ipoly},
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hIpolyNonempty : Ipoly ≠ ∅) :
    IsPolyhedralConvexFunction n
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∈ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hpolyJ : ∀ j : J, IsPolyhedralConvexFunction n (fJ j) := by
    intro j
    simpa [fJ] using hpolyMem j.1 j.2
  have hpolyFin : ∀ i : Fin k, IsPolyhedralConvexFunction n (fFin i) := by
    intro i
    simpa [fFin] using hpolyJ (eJ.symm i)
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproper (eJ.symm i).1
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdom with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    simpa [fFin] using (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hkPos : 0 < k := by
    rcases Set.nonempty_iff_ne_empty.mpr hIpolyNonempty with ⟨i0, hi0⟩
    have hJnonempty : Nonempty J := ⟨⟨i0, hi0⟩⟩
    simpa [k] using (Fintype.card_pos_iff.mpr hJnonempty)
  have hpolySumFin :
      IsPolyhedralConvexFunction n (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_polyhedralSum_of_polyhedral_nonempty_iInter_effectiveDomain
      (f := fFin) (hpoly := hpolyFin) (hproper := hproperFin)
      (hdom := hdomFin) (hmPos := hkPos)
  have hsumFinToJ :
      (fun x => ∑ i : Fin k, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin k => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin k, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  simpa [hsumFinToFilter] using hpolySumFin

/-- Helper for Theorem 20.1: in the positive-head-index branch, the conjugate of the
filtered polyhedral head-block sum is attained by a decomposition over the head index
subtype. -/
lemma helperForTheorem_20_1_headBlock_conjugate_attained_by_headFamily
    {n m k : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hk : k ≤ m) (hkPos : 0 < k)
    (hpoly : ∀ i : Fin m, i.1 < k → IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdomHead :
      Set.Nonempty
        (⋂ i : {i : Fin m // i.1 < k},
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i.1)))
    (xHead : Fin n → ℝ) :
    ∃ headFamily : {i : Fin m // i.1 < k} → Fin n → ℝ,
      (∑ i, headFamily i) = xHead ∧
        fenchelConjugate n
            (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) xHead =
          ∑ i : {i : Fin m // i.1 < k},
            fenchelConjugate n (f i.1) (headFamily i) := by
  classical
  let J : Type := {i : Fin m // i.1 < k}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let kHead : ℕ := Fintype.card J
  let eJ : J ≃ Fin kHead := Fintype.equivFin J
  let fFin : Fin kHead → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hpolyFin : ∀ i : Fin kHead, IsPolyhedralConvexFunction n (fFin i) := by
    intro i
    simpa [fFin, fJ] using hpoly (eJ.symm i).1 (eJ.symm i).2
  have hproperFin :
      ∀ i : Fin kHead, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin, fJ] using hproper (eJ.symm i).1
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin kHead, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomHead with ⟨x0, hx0⟩
    refine ⟨x0, Set.mem_iInter.2 ?_⟩
    intro i
    simpa [fFin, fJ] using (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hmPos : 0 < m := lt_of_lt_of_le hkPos hk
  have hJnonempty : Nonempty J := by
    refine ⟨⟨⟨0, hmPos⟩, ?_⟩⟩
    simpa using hkPos
  have hkHeadPos : 0 < kHead := by
    simpa [kHead] using (Fintype.card_pos_iff.mpr hJnonempty)
  have hconjEqFin :
      fenchelConjugate n (fun x => ∑ i : Fin kHead, fFin i x) =
        infimalConvolutionFamily (fun i : Fin kHead => fenchelConjugate n (fFin i)) :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
      (f := fFin) (hpoly := hpolyFin) (hproper := hproperFin) (hdom := hdomFin)
  have hsumFinToJ :
      (fun x => ∑ i : Fin kHead, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin kHead => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hsumJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i.1 < k)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin kHead, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  rcases
      infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
        (f := fFin) (hpoly := hpolyFin) (hproper := hproperFin) (hdom := hdomFin)
        (hmPos := hkHeadPos) (xStar := xHead) with
    ⟨xHeadFin, hsumHeadFin, hvalHeadFin⟩
  let headFamily : J → Fin n → ℝ := fun j => xHeadFin (eJ j)
  have hsumHeadJ : (∑ j : J, headFamily j) = xHead := by
    calc
      (∑ j : J, headFamily j) =
          ∑ i : Fin kHead, headFamily (eJ.symm i) := by
            simpa [headFamily] using
              (Fintype.sum_equiv eJ
                (fun j : J => headFamily j)
                (fun i : Fin kHead => headFamily (eJ.symm i))
                (by intro j; simp [headFamily]))
      _ = ∑ i : Fin kHead, xHeadFin i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [headFamily]
      _ = xHead := hsumHeadFin
  have hsumConjJEqFin :
      (∑ j : J, fenchelConjugate n (f j.1) (headFamily j)) =
        ∑ i : Fin kHead, fenchelConjugate n (fFin i) (xHeadFin i) := by
    calc
      (∑ j : J, fenchelConjugate n (f j.1) (headFamily j)) =
          ∑ i : Fin kHead, fenchelConjugate n (f (eJ.symm i).1) (headFamily (eJ.symm i)) := by
            simpa using
              (Fintype.sum_equiv eJ
                (fun j : J => fenchelConjugate n (f j.1) (headFamily j))
                (fun i : Fin kHead =>
                  fenchelConjugate n (f (eJ.symm i).1) (headFamily (eJ.symm i)))
                (by intro j; simp))
      _ = ∑ i : Fin kHead, fenchelConjugate n (fFin i) (xHeadFin i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [fFin, fJ, headFamily]
  refine ⟨headFamily, hsumHeadJ, ?_⟩
  have hconjHeadFin :
      fenchelConjugate n (fun x => ∑ i : Fin kHead, fFin i x) xHead =
        ∑ i : Fin kHead, fenchelConjugate n (fFin i) (xHeadFin i) := by
    calc
      fenchelConjugate n (fun x => ∑ i : Fin kHead, fFin i x) xHead =
          infimalConvolutionFamily (fun i : Fin kHead => fenchelConjugate n (fFin i)) xHead := by
            simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g xHead) hconjEqFin
      _ = ∑ i : Fin kHead, fenchelConjugate n (fFin i) (xHeadFin i) := hvalHeadFin
  calc
    fenchelConjugate n
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < k), f i x) xHead =
      fenchelConjugate n (fun x => ∑ i : Fin kHead, fFin i x) xHead := by
        simpa [hsumFinToFilter] using
          congrArg (fun g : (Fin n → ℝ) → EReal => g xHead) hsumFinToFilter.symm
    _ = ∑ i : Fin kHead, fenchelConjugate n (fFin i) (xHeadFin i) := hconjHeadFin
    _ = ∑ i : J, fenchelConjugate n (f i.1) (headFamily i) := hsumConjJEqFin.symm


end Section20
end Chap04
