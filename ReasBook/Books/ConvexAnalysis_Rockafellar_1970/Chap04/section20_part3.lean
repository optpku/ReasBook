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
/-- Helper for Theorem 20.0.4: any proper polyhedral convex function equals its
convex-function closure. -/
lemma helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
    {n : ℕ} (g : (Fin n → ℝ) → EReal)
    (hpoly : IsPolyhedralConvexFunction n g)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    convexFunctionClosure g = g := by
  have hclosed : ClosedConvexFunction g :=
    helperForCorollary_19_1_2_closed_of_polyhedral_proper
      (f := g) hpoly hproper
  have hbot : ∀ x : Fin n → ℝ, g x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  exact convexFunctionClosure_eq_of_closedConvexFunction (f := g) hclosed hbot

/-- Helper for Theorem 20.0.4: every summand indexed by `Ipoly` is closed proper
polyhedral, hence equal to its convex-function closure. -/
lemma helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_mem_Ipoly
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (i : Fin m) (hi : i ∈ Ipoly) :
    convexFunctionClosure (f i) = f i := by
  exact
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (g := f i) ((hpoly i).1 hi) (hproper i)

/-- Helper for Theorem 20.0.4: unpack a witness from the mixed
`dom/ri`-intersection assumption into pointwise membership facts. -/
lemma helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
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
    ∃ x0 : EuclideanSpace ℝ (Fin n),
      (∀ i : Fin m, i ∈ Ipoly →
          x0 ∈ ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) ∧
      (∀ i : Fin m, i ∉ Ipoly →
          x0 ∈ euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  rcases hdom_ri with ⟨x0, hx0⟩
  rcases hx0 with ⟨hxLeft, hxRight⟩
  refine ⟨x0, ?_, ?_⟩
  · intro i hi
    have hxLeft :
        x0 ∈
          ⋂ i : {i : Fin m // i ∈ Ipoly},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      hxLeft
    exact (Set.mem_iInter.mp hxLeft) ⟨i, hi⟩
  · intro i hi
    have hxRight :
        x0 ∈
          ⋂ i : {i : Fin m // i ∉ Ipoly},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
      hxRight
    exact (Set.mem_iInter.mp hxRight) ⟨i, hi⟩

/-- Helper for Theorem 20.0.4: mixed `dom/ri` qualification should identify the
sum-of-closures with the closure of the sum. -/
lemma helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly
    {α : Type*} [AddCommMonoid α] {m : ℕ}
    (Ipoly : Set (Fin m)) [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (g : Fin m → α) :
    (∑ i, g i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), g i) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), g i) := by
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin m)))
      (p := fun i : Fin m => i ∈ Ipoly) (f := g)).symm

/-- Helper for Theorem 20.0.4: rewrite both full sums into `Ipoly` and `Ipolyᶜ`
filter blocks, and remove closures on the polyhedral block. -/
lemma helperForTheorem_20_0_4_splitSums_poly_nonpoly_blocks
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
    [DecidablePred (fun i : Fin m => i ∈ Ipoly)]
    (hpoly : ∀ i : Fin m, i ∈ Ipoly ↔ IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    (fun x => ∑ i, convexFunctionClosure (f i) x) =
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x)) ∧
    (fun x => ∑ i, f i x) =
      (fun x =>
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x)) := by
  refine And.intro ?_ ?_
  · funext x
    have hsplit :
        (∑ i, convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) :=
      helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly (Ipoly := Ipoly)
        (g := fun i : Fin m => convexFunctionClosure (f i) x)
    have hpolyBlock :
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hiIpoly : i ∈ Ipoly := (Finset.mem_filter.mp hi).2
      simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g x)
        (helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_mem_Ipoly
          (f := f) (Ipoly := Ipoly) (hpoly := hpoly) (hproper := hproper) i hiIpoly)
    calc
      (∑ i, convexFunctionClosure (f i) x) =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), convexFunctionClosure (f i) x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) :=
        hsplit
      _ =
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
        rw [hpolyBlock]
  · funext x
    exact
      helperForTheorem_20_0_4_sum_split_filter_poly_nonpoly
        (Ipoly := Ipoly) (g := fun i : Fin m => f i x)

/-- Helper for Theorem 20.0.4: the mixed hypothesis yields nonempty intersection of
relative interiors on the nonpolyhedral block. -/
lemma helperForTheorem_20_0_4_nonpoly_hri_nonempty_iInter
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
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
    Set.Nonempty
      (⋂ i : {i : Fin m // i ∉ Ipoly},
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, _hxPoly, hxNonpoly⟩
  refine ⟨x0, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  exact hxNonpoly i.1 i.2

/-- Helper for Theorem 20.0.4: the mixed qualification provides a common
effective-domain point for all nonpolyhedral indices. -/
lemma helperForTheorem_20_0_4_nonpoly_common_effectiveDomain_point
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) (Ipoly : Set (Fin m))
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
    Set.Nonempty
      (⋂ i : {i : Fin m // i ∉ Ipoly},
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, _hxPoly, hxNonpoly⟩
  refine ⟨(x0 : Fin n → ℝ), ?_⟩
  refine Set.mem_iInter.2 ?_
  intro i
  have hxri :
      x0 ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
    hxNonpoly i.1 i.2
  have hxpre :
      x0 ∈
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
    (euclideanRelativeInterior_subset_closure n
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))).1 hxri
  simpa [Set.mem_preimage] using hxpre

/-- Helper for Theorem 20.0.4: the filtered nonpolyhedral block is proper,
using the common effective-domain point extracted from the mixed qualification. -/
lemma helperForTheorem_20_0_4_nonpoly_filter_block_proper
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
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∉ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hdomJ :
      Set.Nonempty
        (⋂ j : J, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j)) := by
    simpa [J, fJ] using
      helperForTheorem_20_0_4_nonpoly_common_effectiveDomain_point
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri)
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hproperSumFin :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := fFin) (hproper := hproperFin) (hdom := hdomFin)
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
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hsumFinToFilter :
      (fun x => ∑ i : Fin k, fFin i x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) :=
    hsumFinToJ.trans hsumJToFilter
  simpa [hsumFinToFilter] using hproperSumFin

/-- Helper for Theorem 20.0.4: the nonpolyhedral filtered block satisfies the
Section 16 closure-of-sum identity under the extracted `ri` qualification. -/
lemma helperForTheorem_20_0_4_nonpoly_filter_block_sumClosure_eq_closure_sum
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
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    (fun x =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
      convexFunctionClosure
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∉ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hriJ :
      Set.Nonempty
        (⋂ j : J,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j))) := by
    simpa [J, fJ] using
      helperForTheorem_20_0_4_nonpoly_hri_nonempty_iInter
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri)
  have hriFin :
      Set.Nonempty
        (⋂ i : Fin k,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i))) := by
    rcases hriJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hsumFin :=
    section16_sum_convexFunctionClosure_eq_convexFunctionClosure_sum_of_nonempty_iInter_ri_effectiveDomain
      (f := fFin) hproperFin hriFin
  have hleftFinToJ :
      (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) =
        (fun x => ∑ j : J, convexFunctionClosure (fJ j) x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => convexFunctionClosure (fJ j) x)
        (fun i : Fin k => convexFunctionClosure (fJ (eJ.symm i)) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hleftJToFilter :
      (fun x => ∑ j : J, convexFunctionClosure (fJ j) x) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => convexFunctionClosure (f i) x))
  have hrightFinToJ :
      (fun x => ∑ i : Fin k, fFin i x) = (fun x => ∑ j : J, fJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eJ
        (fun j : J => fJ j x)
        (fun i : Fin k => fJ (eJ.symm i) x)
        (by intro j; simp)
    simpa [fFin] using hsumEq.symm
  have hrightJToFilter :
      (fun x => ∑ j : J, fJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [J, fJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hleft :
      (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) =
        (fun x =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) := by
    exact hleftFinToJ.trans hleftJToFilter
  have hright :
      convexFunctionClosure (fun x => ∑ i : Fin k, fFin i x) =
        convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    congr 1
    exact hrightFinToJ.trans hrightJToFilter
  calc
    (fun x =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), convexFunctionClosure (f i) x) =
        (fun x => ∑ i : Fin k, convexFunctionClosure (fFin i) x) := hleft.symm
    _ = convexFunctionClosure (fun x => ∑ i : Fin k, fFin i x) := hsumFin
    _ = convexFunctionClosure
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := hright

/-- Helper for Theorem 20.0.4: the polyhedral filtered block is proper and has a
domain witness extracted from the mixed qualification point. -/
lemma helperForTheorem_20_0_4_poly_filter_block_proper_and_dom_witness
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
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) ∧
      ∃ x0 : Fin n → ℝ,
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
  classical
  let J : Type := {i : Fin m // i ∈ Ipoly}
  let fJ : J → (Fin n → ℝ) → EReal := fun j => f j.1
  let k : ℕ := Fintype.card J
  let eJ : J ≃ Fin k := Fintype.equivFin J
  let fFin : Fin k → (Fin n → ℝ) → EReal := fun i => fJ (eJ.symm i)
  have hproperJ :
      ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fJ j) := by
    intro j
    simpa [fJ] using hproper j.1
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproperJ (eJ.symm i)
  have hdomJ :
      Set.Nonempty
        (⋂ j : J, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j)) := by
    rcases
      helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, hxPoly, _hxNonpoly⟩
    refine ⟨(x0 : Fin n → ℝ), ?_⟩
    refine Set.mem_iInter.2 ?_
    intro j
    simpa [J, fJ] using hxPoly j.1 j.2
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hproperSumFin :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := fFin) (hproper := hproperFin) (hdom := hdomFin)
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
  have hproperPoly :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    simpa [hsumFinToFilter] using hproperSumFin
  refine ⟨hproperPoly, ?_⟩
  have hdomPoly :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x)) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ)))
      (f := fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x)).1 hproperPoly.2.1
  rcases hdomPoly with ⟨x0, hx0⟩
  exact ⟨x0, hx0⟩

/-- Helper for Theorem 20.0.4: the mixed qualification yields a single witness that
lies in the polyhedral filtered-block effective domain and in the relative interior
of the nonpolyhedral filtered-block effective domain. -/
lemma helperForTheorem_20_0_4_exists_dom_poly_and_ri_nonpoly_filtered_sum_witness
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
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))))) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) ∧
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x0 ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x))) := by
  classical
  rcases
    helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
      (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0E, hxPoly, hxNonpoly⟩
  let Jpoly : Type := {i : Fin m // i ∈ Ipoly}
  let fPolyJ : Jpoly → (Fin n → ℝ) → EReal := fun j => f j.1
  let kPoly : ℕ := Fintype.card Jpoly
  let ePoly : Jpoly ≃ Fin kPoly := Fintype.equivFin Jpoly
  let fPolyFin : Fin kPoly → (Fin n → ℝ) → EReal := fun i => fPolyJ (ePoly.symm i)
  have hnotbotPolyJ :
      ∀ j : Jpoly, ∀ x : Fin n → ℝ, fPolyJ j x ≠ (⊥ : EReal) := by
    intro j x
    exact (hproper j.1).2.2 x (by simp)
  have hnotbotPolyFin :
      ∀ i : Fin kPoly, ∀ x : Fin n → ℝ, fPolyFin i x ≠ (⊥ : EReal) := by
    intro i x
    simpa [fPolyFin] using hnotbotPolyJ (ePoly.symm i) x
  have hx0PolyInter :
      ((x0E : Fin n → ℝ) ∈
        ⋂ j : Jpoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyJ j)) := by
    refine Set.mem_iInter.2 ?_
    intro j
    have hxj :
        x0E ∈ ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f j.1)) :=
      hxPoly j.1 j.2
    simpa [fPolyJ, Set.mem_preimage] using hxj
  have hdomEqPoly :
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i : Fin kPoly, fPolyFin i x) =
        ⋂ i : Fin kPoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyFin i) :=
    effectiveDomain_sum_eq_iInter_univ (f := fPolyFin) hnotbotPolyFin
  have hx0PolyInterFin :
      ((x0E : Fin n → ℝ) ∈
        ⋂ i : Fin kPoly,
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPolyFin i)) := by
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0PolyInter) (ePoly.symm i)
  have hx0PolyDomFin :
      (x0E : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin kPoly, fPolyFin i x) := by
    exact hdomEqPoly.symm ▸ hx0PolyInterFin
  have hsumPolyFinToJ :
      (fun x => ∑ i : Fin kPoly, fPolyFin i x) =
        (fun x => ∑ j : Jpoly, fPolyJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv ePoly
        (fun j : Jpoly => fPolyJ j x)
        (fun i : Fin kPoly => fPolyJ (ePoly.symm i) x)
        (by intro j; simp)
    simpa [fPolyFin] using hsumEq.symm
  have hsumPolyJToFilter :
      (fun x => ∑ j : Jpoly, fPolyJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    funext x
    simpa [Jpoly, fPolyJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∈ Ipoly)
        (f := fun i : Fin m => f i x))
  have hx0PolyDom :
      (x0E : Fin n → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∈ Ipoly), f i x) := by
    simpa [hsumPolyFinToJ, hsumPolyJToFilter] using hx0PolyDomFin
  let Jnonpoly : Type := {i : Fin m // i ∉ Ipoly}
  let fNonpolyJ : Jnonpoly → (Fin n → ℝ) → EReal := fun j => f j.1
  let kNonpoly : ℕ := Fintype.card Jnonpoly
  let eNonpoly : Jnonpoly ≃ Fin kNonpoly := Fintype.equivFin Jnonpoly
  let fNonpolyFin : Fin kNonpoly → (Fin n → ℝ) → EReal :=
    fun i => fNonpolyJ (eNonpoly.symm i)
  have htoLp :
      ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm :
        (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) =
      (fun a : Fin n → ℝ => WithLp.toLp 2 a) := rfl
  have hproperNonpolyFin :
      ∀ i : Fin kNonpoly,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i) := by
    intro i
    simpa [fNonpolyFin] using hproper (eNonpoly.symm i).1
  have hx0NonpolyInter :
      x0E ∈
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) := by
    refine Set.mem_iInter.2 ?_
    intro i
    have hxi :
        x0E ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f (eNonpoly.symm i).1)) :=
      hxNonpoly (eNonpoly.symm i).1 (eNonpoly.symm i).2
    simpa [fNonpolyFin, fNonpolyJ] using hxi
  have hx0NonpolyInterImage :
      x0E ∈
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) := by
    refine Set.mem_iInter.2 ?_
    intro i
    have hxiPre :
        x0E ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) :=
      (Set.mem_iInter.mp hx0NonpolyInter) i
    have hseti :
        ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) =
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
      · intro hx
        refine ⟨(x : Fin n → ℝ), hx, ?_⟩
        simp
    simpa [hseti] using hxiPre
  have hriNonpolyImage :
      Set.Nonempty
        (⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i)))) :=
    ⟨x0E, hx0NonpolyInterImage⟩
  have hriEqNonpolyImage :
      euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x))) =
        ⋂ i : Fin kNonpoly,
          euclideanRelativeInterior n
            ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fNonpolyFin i))) := by
    simpa [htoLp] using
      (ri_effectiveDomain_sum_eq_iInter (f := fNonpolyFin) hproperNonpolyFin) hriNonpolyImage
  have hx0NonpolyRiImageFin :
      x0E ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x))) := by
    exact hriEqNonpolyImage.symm ▸ hx0NonpolyInterImage
  have hsumNonpolyFinToJ :
      (fun x => ∑ i : Fin kNonpoly, fNonpolyFin i x) =
        (fun x => ∑ j : Jnonpoly, fNonpolyJ j x) := by
    funext x
    have hsumEq :=
      Fintype.sum_equiv eNonpoly
        (fun j : Jnonpoly => fNonpolyJ j x)
        (fun i : Fin kNonpoly => fNonpolyJ (eNonpoly.symm i) x)
        (by intro j; simp)
    simpa [fNonpolyFin] using hsumEq.symm
  have hsumNonpolyJToFilter :
      (fun x => ∑ j : Jnonpoly, fNonpolyJ j x) =
        (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x) := by
    funext x
    simpa [Jnonpoly, fNonpolyJ] using
      (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Fin m)))
        (p := fun i : Fin m => i ∉ Ipoly)
        (f := fun i : Fin m => f i x))
  have hx0NonpolyRiImage :
      x0E ∈
        euclideanRelativeInterior n
          ((fun a : Fin n → ℝ => WithLp.toLp 2 a) ''
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ Ipoly), f i x))) := by
    simpa [hsumNonpolyFinToJ, hsumNonpolyJToFilter] using hx0NonpolyRiImageFin
  refine ⟨(x0E : Fin n → ℝ), hx0PolyDom, ?_⟩
  simpa using hx0NonpolyRiImage

/-- Helper for Theorem 20.0.4: if `Ipoly` is nonempty, then the filtered
polyhedral block-sum is a polyhedral convex function. -/
lemma helperForTheorem_20_0_4_poly_filter_block_isPolyhedral_of_nonempty
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
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))))
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
    simpa [fJ] using (hpoly j.1).1 j.2
  have hpolyFin : ∀ i : Fin k, IsPolyhedralConvexFunction n (fFin i) := by
    intro i
    simpa [fFin] using hpolyJ (eJ.symm i)
  have hproperFin :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFin i) := by
    intro i
    simpa [fFin] using hproper (eJ.symm i).1
  have hdomJ :
      Set.Nonempty
        (⋂ j : J, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fJ j)) := by
    rcases
      helperForTheorem_20_0_4_extract_witness_mixed_dom_ri
        (f := f) (Ipoly := Ipoly) (hdom_ri := hdom_ri) with ⟨x0, hxPoly, _hxNonpoly⟩
    refine ⟨(x0 : Fin n → ℝ), ?_⟩
    refine Set.mem_iInter.2 ?_
    intro j
    simpa [J, fJ] using hxPoly j.1 j.2
  have hdomFin :
      Set.Nonempty
        (⋂ i : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFin i)) := by
    rcases hdomJ with ⟨x0, hx0⟩
    refine ⟨x0, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    exact (Set.mem_iInter.mp hx0) (eJ.symm i)
  have hkPos : 0 < k := by
    rcases Set.nonempty_iff_ne_empty.mpr hIpolyNonempty with ⟨i0, hi0⟩
    have hJnonempty : Nonempty J := ⟨⟨i0, hi0⟩⟩
    simpa [k] using (Fintype.card_pos_iff.mpr hJnonempty)
  have hpolySumFin :
      IsPolyhedralConvexFunction n (fun x => ∑ i : Fin k, fFin i x) :=
    helperForCorollary_20_0_2_polyhedralSum_of_polyhedral_nonempty_iInter_effectiveDomain
      (f := fFin) (hpoly := hpolyFin) (hproper := hproperFin) (hdom := hdomFin)
      (hmPos := hkPos)
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


end Section20
end Chap04
