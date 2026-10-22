/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part1

open scoped BigOperators Pointwise

section Chap04
section Section20
/-- Helper for Corollary 20.0.3: with an empty index family, any split-sum attainment
witness for the conjugate infimal convolution forces the target vector to be zero. -/
lemma helperForCorollary_20_0_3_attainment_target_eq_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ}
    (hAtt :
      ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    xStar = (0 : Fin n → ℝ) := by
  exact
    helperForCorollary_20_0_2_attainmentWitness_target_eq_zero_of_index_empty
      (g := fun i => fenchelConjugate n (f i)) (xStar := xStar) hAtt

/-- Helper for Corollary 20.0.3: for an empty index family, the split-attainment
condition is equivalent to the target covector being zero. -/
lemma helperForCorollary_20_0_3_exists_attainmentWitness_iff_target_eq_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    (∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      xStar = (0 : Fin n → ℝ) := by
  constructor
  · intro hAtt
    exact
      helperForCorollary_20_0_3_attainment_target_eq_zero_of_empty_index
        (f := f) (xStar := xStar) hAtt
  · intro hxStar
    subst hxStar
    exact
      helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
        (g := fun i => fenchelConjugate n (f i))

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target
covector makes attainment-witness existence equivalent to False. -/
lemma helperForCorollary_20_0_3_exists_attainmentWitness_iff_false_of_empty_index_of_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ)
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    (∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      False := by
  constructor
  · intro hAtt
    have hxStarZero : xStar = (0 : Fin n → ℝ) :=
      (helperForCorollary_20_0_3_exists_attainmentWitness_iff_target_eq_zero_of_empty_index
        (f := f) (xStar := xStar)).1 hAtt
    exact hxStar hxStarZero
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target
cannot admit any split-sum decomposition. -/
lemma helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
    {n : ℕ} {xStar : Fin n → ℝ}
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar := by
  intro hSplit
  rcases hSplit with ⟨xStarFamily, hsum⟩
  have hsumZero : (∑ i, xStarFamily i) = (0 : Fin n → ℝ) := by
    simp
  have hxStarZero : xStar = (0 : Fin n → ℝ) := hsum.symm.trans hsumZero
  exact hxStar hxStarZero

/-- Helper for Corollary 20.0.3: with an empty index family, a nonzero target cannot
admit an attainment witness for the conjugate infimal convolution split. -/
lemma helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ}
    (hxStar : xStar ≠ (0 : Fin n → ℝ)) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  intro hAtt
  rcases hAtt with ⟨xStarFamily, hsum, _hattain⟩
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := n) (xStar := xStar) hxStar ⟨xStarFamily, hsum⟩

/-- Helper for Corollary 20.0.3: if an empty-index model has at least one nonzero
covector, then the universal attainment claim is impossible. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_exists_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal)
    (hne : ∃ xStar : Fin n → ℝ, xStar ≠ (0 : Fin n → ℝ)) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hAll
  rcases hne with ⟨xStar, hxStar⟩
  exact
    helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
      (f := f) (xStar := xStar) hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: in dimension one, the constant-one covector is nonzero. -/
lemma helperForCorollary_20_0_3_unitCovector_ne_zero :
    (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
  intro h
  have h0 : (1 : ℝ) = 0 := by
    simpa using congrArg (fun g : Fin 1 → ℝ => g 0) h
  norm_num at h0

/-- Helper for Corollary 20.0.3: in any nonzero dimension, the constant-one covector
is nonzero. -/
lemma helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    (fun _ : Fin n => (1 : ℝ)) ≠ (0 : Fin n → ℝ) := by
  intro h
  have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
  let i0 : Fin n := ⟨0, hnPos⟩
  have h0 : (1 : ℝ) = 0 := by
    simpa using congrArg (fun g : Fin n → ℝ => g i0) h
  norm_num at h0

/-- Helper for Corollary 20.0.3: in nonzero dimension there exists a nonzero covector. -/
lemma helperForCorollary_20_0_3_exists_nonzero_covector_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    ∃ xStar : Fin n → ℝ, xStar ≠ (0 : Fin n → ℝ) := by
  refine ⟨fun _ : Fin n => (1 : ℝ), ?_⟩
  exact
    helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
      (n := n) hnZero

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
one cannot decompose every covector as a `Fin 0`-indexed split sum. -/
lemma helperForCorollary_20_0_3_universal_splitSum_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (hnZero : n ≠ 0) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar) := by
  rcases
    helperForCorollary_20_0_3_exists_nonzero_covector_of_dim_ne_zero
      (n := n) hnZero with ⟨xStar, hxStar⟩
  intro hAll
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := n) (xStar := xStar) hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the constant-one covector admits no attainment witness for the conjugate split. -/
lemma helperForCorollary_20_0_3_no_attainment_witness_for_constOne_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = (fun _ : Fin n => (1 : ℝ)) ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i))
            (fun _ : Fin n => (1 : ℝ)) =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  exact
    helperForCorollary_20_0_3_no_attainment_witness_of_empty_index_of_ne_zero
      (f := f)
      (xStar := fun _ : Fin n => (1 : ℝ))
      (helperForCorollary_20_0_3_constOneCovector_ne_zero_of_dim_ne_zero
        (n := n) hnZero)

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the constant-one covector is an explicit target with no attainment witness. -/
lemma helperForCorollary_20_0_3_exists_counterexample_no_attainment_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ∃ xStar : Fin n → ℝ,
      ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  refine ⟨fun _ : Fin n => (1 : ℝ), ?_⟩
  exact
    helperForCorollary_20_0_3_no_attainment_witness_for_constOne_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the universal attainment claim is impossible. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  rcases
    helperForCorollary_20_0_3_exists_counterexample_no_attainment_of_empty_index_of_dim_ne_zero
      (f := f) hnZero with ⟨xStar, hxStar⟩
  exact
    fun hAll => hxStar (hAll xStar)

/-- Helper for Corollary 20.0.3: in the empty-index case, if universal attainment
holds, then the ambient dimension must be zero. -/
lemma helperForCorollary_20_0_3_dim_eq_zero_of_empty_index_of_universalAttainment
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal)
    (hAll :
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) :
    n = 0 := by
  by_contra hnZero
  exact
    (helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero) hAll

/-- Helper for Corollary 20.0.3: with an empty index family, universal attainment fails
already for the one-dimensional constant-one target covector. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index
    (f : Fin 0 → (Fin 1 → ℝ) → EReal) :
    ¬ (∀ xStar : Fin 1 → ℝ,
        ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
              ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (n := 1) (f := f) Nat.one_ne_zero

/-- Helper for Corollary 20.0.3: in zero dimension, every covector is zero. -/
lemma helperForCorollary_20_0_3_covector_eq_zero_of_dim_zero
    (xStar : Fin 0 → ℝ) :
    xStar = (0 : Fin 0 → ℝ) := by
  ext i
  exact Fin.elim0 i

/-- Helper for Corollary 20.0.3: with an empty index family, universal attainment
is equivalent to the ambient dimension being zero. -/
lemma helperForCorollary_20_0_3_universalAttainment_iff_dim_zero_of_empty_index
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) :
    (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) ↔
      n = 0 := by
  constructor
  · intro hAll
    exact
      helperForCorollary_20_0_3_dim_eq_zero_of_empty_index_of_universalAttainment
        (f := f) hAll
  · intro hnZero
    subst hnZero
    intro xStar
    have hxStarZero : xStar = (0 : Fin 0 → ℝ) :=
      helperForCorollary_20_0_3_covector_eq_zero_of_dim_zero xStar
    simpa [hxStarZero] using
      (helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
        (g := fun i => fenchelConjugate 0 (f i)))

/-- Helper for Corollary 20.0.3: with an empty index family and nonzero dimension,
the full refinement-plus-universal-attainment conclusion is impossible. -/
lemma helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0) :
    ¬ (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          ∃ xStarFamily : Fin 0 → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hConclusion
  exact
    (helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero) hConclusion.2

/-- Helper for Corollary 20.0.3: there is explicit empty-index data satisfying
all hypotheses while universal attainment fails in dimension one. -/
lemma helperForCorollary_20_0_3_exists_hypotheses_without_universalAttainment
    :
    ∃ f : Fin 0 → (Fin 1 → ℝ) → EReal,
      (∀ i, IsPolyhedralConvexFunction 1 (f i)) ∧
      (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) ∧
      ¬ (∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · simpa using
      (Set.nonempty_univ : Set.Nonempty (Set.univ : Set (Fin 1 → ℝ)))
  · exact
      helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index
        (f := fun i => Fin.elim0 i)

/-- Helper for Corollary 20.0.3: in the concrete branch `m = 0`, `n = 1`,
the standard hypotheses do not imply universal split-attainment. -/
lemma helperForCorollary_20_0_3_not_imp_universalAttainment_in_empty_index_dim_one
    :
    ¬ (∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        ∀ xStar : Fin 1 → ℝ,
          ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  intro hImp
  rcases helperForCorollary_20_0_3_exists_hypotheses_without_universalAttainment with
    ⟨f, hpoly, hproper, hdom, hNotAll⟩
  exact hNotAll (hImp f hpoly hproper hdom)

/-- Helper for Corollary 20.0.3: in the concrete branch `m = 0`, `n = 1`,
the full refinement-plus-universal-attainment conclusion cannot follow from the
standard hypotheses. -/
lemma helperForCorollary_20_0_3_not_imp_full_refinement_and_universalAttainment_in_empty_index_dim_one
    :
    ¬ (∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        fenchelConjugate 1 (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
          ∀ xStar : Fin 1 → ℝ,
            ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                  ∑ i, fenchelConjugate 1 (f i) (xStarFamily i)) := by
  intro hImp
  exact
    helperForCorollary_20_0_3_not_imp_universalAttainment_in_empty_index_dim_one
      (fun f hpoly hproper hdom => (hImp f hpoly hproper hdom).2)

/-- Helper for Corollary 20.0.3: the hypotheses do not imply the full
refinement-plus-universal-attainment conclusion in all dimensions/index sizes.
The branch `n = 1`, `m = 0` gives a concrete obstruction. -/
lemma helperForCorollary_20_0_3_not_forall_dimensions_refinement_and_universalAttainment
    :
    ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → ℝ) → EReal),
        (∀ i, IsPolyhedralConvexFunction n (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) →
        fenchelConjugate n (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
          ∀ xStar : Fin n → ℝ,
            ∃ xStarFamily : Fin m → Fin n → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                  ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  intro hAll
  have hDimOne :
      ∀ f : Fin 0 → (Fin 1 → ℝ) → EReal,
        (∀ i, IsPolyhedralConvexFunction 1 (f i)) →
        (∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        Set.Nonempty
          (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (f i)) →
        fenchelConjugate 1 (fun x => ∑ i, f i x) =
            infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) ∧
          ∀ xStar : Fin 1 → ℝ,
            ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
              (∑ i, xStarFamily i) = xStar ∧
                infimalConvolutionFamily (fun i => fenchelConjugate 1 (f i)) xStar =
                  ∑ i, fenchelConjugate 1 (f i) (xStarFamily i) := by
    intro f hpoly hproper hdom
    exact hAll 1 0 f hpoly hproper hdom
  exact
    helperForCorollary_20_0_3_not_imp_full_refinement_and_universalAttainment_in_empty_index_dim_one
      hDimOne

/-- Helper for Corollary 20.0.3: in the branch `m = 0`, `n = 1`, the constant-one
target covector cannot be represented as a `Fin 0`-indexed split sum. -/
lemma helperForCorollary_20_0_3_no_split_sum_for_unitCovector_of_empty_index
    :
    ¬ ∃ xStarFamily : Fin 0 → Fin 1 → ℝ,
        (∑ i, xStarFamily i) = (fun _ : Fin 1 => (1 : ℝ)) := by
  exact
    helperForCorollary_20_0_3_no_split_sum_decomposition_of_empty_index_of_ne_zero
      (n := 1)
      (xStar := fun _ : Fin 1 => (1 : ℝ))
      helperForCorollary_20_0_3_unitCovector_ne_zero

/-- Helper for Corollary 20.0.3: in the branch `m = 0` and `n ≠ 0`,
the standard polyhedral/proper/domain hypotheses still do not imply universal
split-attainment. -/
lemma helperForCorollary_20_0_3_universalAttainment_impossible_under_hypotheses_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0)
    (_hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (_hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (_hdom :
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: in the branch `m = 0` and `n ≠ 0`,
the full refinement-plus-universal-attainment conclusion is incompatible even
under the standard polyhedral/proper/domain hypotheses. -/
lemma helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_under_hypotheses_of_empty_index_of_dim_ne_zero
    {n : ℕ} (f : Fin 0 → (Fin n → ℝ) → EReal) (hnZero : n ≠ 0)
    (_hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (_hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (_hdom :
      Set.Nonempty
        (⋂ i : Fin 0, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ¬ (fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
        ∀ xStar : Fin n → ℝ,
          ∃ xStarFamily : Fin 0 → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
                ∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
  exact
    helperForCorollary_20_0_3_refinement_and_universalAttainment_impossible_of_empty_index_of_dim_ne_zero
      (f := f) hnZero

/-- Helper for Corollary 20.0.3: when `0 < m`, each covector admits an attaining split
for the infimal convolution of conjugates. -/
theorem helperForCorollary_20_0_3_attainment_for_each_xStar_of_pos_m
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    ∀ xStar : Fin n → ℝ,
      ∃ xStarFamily : Fin m → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
            ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  intro xStar
  exact
    infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
      (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
      (hmPos := hmPos) (xStar := xStar)

/-- Helper for Corollary 20.0.3: if the index family is nonempty (`0 < m`), then the
polyhedral sum-conjugate identity and universal attainment conclusion both hold. -/
theorem helperForCorollary_20_0_3_refinement_and_attainment_of_pos_m
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  refine And.intro ?_ ?_
  · exact
      fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
  · intro xStar
    exact
      helperForCorollary_20_0_3_attainment_for_each_xStar_of_pos_m
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
        (hmPos := hmPos) xStar

/-- Corollary 20.0.3: In the polyhedral case, Theorem 20.0.1 yields the
sum-conjugate/infimal-convolution identity without closure, under the simpler condition
dom f₁ ∩ ⋯ ∩ dom fₘ ≠ ∅, and the infimum in the infimal convolution is attained. -/
theorem polyhedral_refinement_fenchelConjugate_sum_eq_infimalConvolutionFamily_and_attainment
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) ∧
      ∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  exact
    helperForCorollary_20_0_3_refinement_and_attainment_of_pos_m
      (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom) (hmPos := hmPos)


end Section20
end Chap04
