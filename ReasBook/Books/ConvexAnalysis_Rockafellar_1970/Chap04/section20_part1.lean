/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part1

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Theorem 20.0.1: each polyhedral proper summand equals its convex-function closure. -/
lemma helperForTheorem_20_0_1_convexFunctionClosure_eq_self_eachSummand
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    ∀ i : Fin m, convexFunctionClosure (f i) = f i := by
  intro i
  have hclosed : ClosedConvexFunction (f i) :=
    helperForCorollary_19_1_2_closed_of_polyhedral_proper
      (f := f i) (hpoly i) (hproper i)
  have hbot : ∀ x : Fin n → ℝ, f i x ≠ (⊥ : EReal) := by
    intro x
    exact (hproper i).2.2 x (by simp)
  exact convexFunctionClosure_eq_of_closedConvexFunction (f := f i) hclosed hbot

/-- Helper for Theorem 20.0.1: Theorem 16.4.2 rewrites to a closure identity after removing
closures on each polyhedral summand. -/
lemma helperForTheorem_20_0_1_main_rewrite_from_section16
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  simpa [helperForTheorem_20_0_1_convexFunctionClosure_eq_self_eachSummand
      (f := f) (hpoly := hpoly) (hproper := hproper)] using
    (section16_fenchelConjugate_sum_convexFunctionClosure_eq_convexFunctionClosure_infimalConvolutionFamily
      (f := f) hproper)

/-- Helper for Theorem 20.0.1: a common effective-domain point gives a finite lower bound, hence
the infimal convolution of conjugates never takes the value `⊥`. -/
lemma helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_ne_bot
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ∀ xStar : Fin n → ℝ,
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar ≠ (⊥ : EReal) := by
  classical
  rcases hdom with ⟨x0, hx0⟩
  intro xStar
  have hbot_i : ∀ i : Fin m, f i x0 ≠ (⊥ : EReal) := by
    intro i
    exact (hproper i).2.2 x0 (by simp)
  have htop_i : ∀ i : Fin m, f i x0 ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
      (f := f i) ((Set.mem_iInter.mp hx0) i)
  have hsum_real :
      (∑ i, f i x0) =
        (((∑ i, (f i x0).toReal) : ℝ) : EReal) := by
    calc
      (∑ i, f i x0) = ∑ i, (((f i x0).toReal : ℝ) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := htop_i i) (hBot := hbot_i i)
      _ = (((∑ i, (f i x0).toReal) : ℝ) : EReal) := by
        symm
        exact section16_coe_finset_sum (s := Finset.univ) (b := fun i : Fin m => (f i x0).toReal)
  have hlower :
      (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x0) ≤
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
    unfold infimalConvolutionFamily
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨xStarFamily, hsum, rfl⟩
    have hsumDot :
        (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x0) =
          ∑ i, ((((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x0)) := by
      have hdot : x0 ⬝ᵥ xStar = ∑ i, x0 ⬝ᵥ xStarFamily i := by
        calc
          x0 ⬝ᵥ xStar = x0 ⬝ᵥ (∑ i, xStarFamily i) := by simp [hsum]
          _ = ∑ i, x0 ⬝ᵥ xStarFamily i := by
              simpa using
                (dotProduct_sum (u := x0) (s := (Finset.univ : Finset (Fin m)))
                  (v := fun i : Fin m => xStarFamily i))
      have hcoeDot :
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) =
            ∑ i, (((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal) ) := by
        calc
          (((x0 ⬝ᵥ xStar : ℝ) : EReal)) = (((∑ i, x0 ⬝ᵥ xStarFamily i : ℝ) : EReal)) := by
            simp [hdot]
          _ = ∑ i, (((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal)) := by
            exact section16_coe_finset_sum (s := Finset.univ)
              (b := fun i : Fin m => x0 ⬝ᵥ xStarFamily i)
      have hneg :
          -(∑ i, f i x0) = ∑ i, -(f i x0) := by
        exact section16_neg_sum_eq_sum_neg (s := (Finset.univ : Finset (Fin m)))
          (b := fun i : Fin m => f i x0) (fun i _ => hbot_i i)
      calc
        (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x0)
            = (((x0 ⬝ᵥ xStar : ℝ) : EReal)) + -(∑ i, f i x0) := by simp [sub_eq_add_neg]
        _ = (∑ i, (((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal))) + -(∑ i, f i x0) := by
            simp [hcoeDot]
        _ = (∑ i, (((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal))) + ∑ i, -(f i x0) := by
            simp [hneg]
        _ = ∑ i, ((((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal)) + -(f i x0)) := by
            rw [← Finset.sum_add_distrib]
        _ = ∑ i, ((((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x0)) := by
            simp [sub_eq_add_neg]
    have hbound_each :
        ∀ i : Fin m,
          (((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x0) ≤ fenchelConjugate n (f i) (xStarFamily i) := by
      intro i
      unfold fenchelConjugate
      exact le_sSup ⟨x0, rfl⟩
    have hbound_sum :
        ∑ i, ((((x0 ⬝ᵥ xStarFamily i : ℝ) : EReal) - f i x0)) ≤
          ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hbound_each i
    exact hsumDot ▸ hbound_sum
  intro hbot
  have hle_bot : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x0) ≤ (⊥ : EReal) := by
    simpa [hbot] using hlower
  have hbot_eq : (((x0 ⬝ᵥ xStar : ℝ) : EReal) - ∑ i, f i x0) = (⊥ : EReal) :=
    le_antisymm hle_bot bot_le
  have hne : ((((x0 ⬝ᵥ xStar : ℝ) : EReal) - (((∑ i, (f i x0).toReal : ℝ) : EReal))) ≠
      (⊥ : EReal)) := by
    intro hbot'
    have htop : ((((∑ i, (f i x0).toReal : ℝ) : EReal)) = (⊤ : EReal)) :=
      section16_coe_sub_eq_bot_iff_eq_top (a := x0 ⬝ᵥ xStar) hbot'
    exact EReal.coe_ne_top _ htop
  exact hne (by simpa [hsum_real] using hbot_eq)

/-- Helper for Theorem 20.0.1: closure-removal on the infimal convolution side. -/
lemma helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_exists_nonTop
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    ∃ xStar : Fin n → ℝ,
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar ≠ (⊤ : EReal) := by
  classical
  have hproperConj :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
    intro i
    simpa using (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hproper i))
  choose xStar0 r0 hx0 using
    (fun i : Fin m =>
      properConvexFunctionOn_exists_finite_point
        (n := n) (f := fenchelConjugate n (f i)) (hproperConj i))
  let xStar : Fin n → ℝ := ∑ i, xStar0 i
  refine ⟨xStar, ?_⟩
  have hsInf_le :
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar ≤
        ∑ i, fenchelConjugate n (f i) (xStar0 i) := by
    unfold infimalConvolutionFamily
    refine sInf_le ?_
    refine ⟨xStar0, ?_, rfl⟩
    simp [xStar]
  have hsum_real :
      (∑ i, fenchelConjugate n (f i) (xStar0 i)) =
        (((∑ i, r0 i) : ℝ) : EReal) := by
    calc
      (∑ i, fenchelConjugate n (f i) (xStar0 i)) = ∑ i, (((r0 i : ℝ) : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (hx0 i)
      _ = (((∑ i, r0 i) : ℝ) : EReal) := by
        symm
        exact section16_coe_finset_sum (s := Finset.univ) (b := fun i : Fin m => r0 i)
  have hsum_ne_top :
      (∑ i, fenchelConjugate n (f i) (xStar0 i)) ≠ (⊤ : EReal) := by
    intro htop
    have htop' : ((((∑ i, r0 i) : ℝ) : EReal)) = (⊤ : EReal) := by
      simp [hsum_real] at htop
    exact EReal.coe_ne_top _ htop'
  intro htop
  have htop_le : (⊤ : EReal) ≤ ∑ i, fenchelConjugate n (f i) (xStar0 i) := by
    simpa [htop] using hsInf_le
  have hsum_top : (∑ i, fenchelConjugate n (f i) (xStar0 i)) = (⊤ : EReal) :=
    top_unique htop_le
  exact hsum_ne_top hsum_top

/-- Helper for Theorem 20.0.1: under the common-domain hypothesis, the conjugate
infimal convolution family is proper. -/
lemma helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_proper
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  let g : (Fin n → ℝ) → EReal := infimalConvolutionFamily (fun i => fenchelConjugate n (f i))
  have hconv : ConvexFunction g := by
    simpa [g] using
      (section16_convexFunction_infimalConvolutionFamily_conjugates (f := f) hproper)
  have hneBot : ∀ xStar : Fin n → ℝ, g xStar ≠ (⊥ : EReal) := by
    intro xStar
    simpa [g] using
      (helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_ne_bot
        (f := f) (hproper := hproper) (hdom := hdom) xStar)
  rcases
      helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_exists_nonTop
        (f := f) (hproper := hproper) with
    ⟨xStar0, hxStar0⟩
  have hxStar0_mem : xStar0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
    have hxStar0_lt : g xStar0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxStar0
    have hxStar0_mem' :
        xStar0 ∈ {x | x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ g x < (⊤ : EReal)} := by
      exact ⟨by simp, hxStar0_lt⟩
    simpa [effectiveDomain_eq] using hxStar0_mem'
  have hneDom : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    exact ⟨xStar0, hxStar0_mem⟩
  refine
    (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
      (S := (Set.univ : Set (Fin n → ℝ))) (f := g)).2 ?_
  refine ⟨?_, hneDom, ?_⟩
  · simpa [ConvexFunction] using hconv
  · intro x hx
    refine ⟨hneBot x, ?_⟩
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx

/-- Helper for Theorem 20.0.1: from a common effective-domain point for a `Fin (k+1)` family,
obtain one for its tail `Fin k` subfamily. -/
lemma helperForTheorem_20_0_1_nonempty_iInter_effectiveDomain_tail
    {n k : ℕ} (f : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (hdom :
      Set.Nonempty
        (⋂ i : Fin (k + 1), effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    Set.Nonempty
      (⋂ j : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f (Fin.succ j))) := by
  rcases hdom with ⟨x0, hx0⟩
  refine ⟨x0, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro j
  exact (Set.mem_iInter.mp hx0) (Fin.succ j)

/-- Helper for Theorem 20.0.1: rewrite a split sum over `Fin (k+1)` as head plus tail. -/
lemma helperForTheorem_20_0_1_sum_headTail_rewrite
    {n k : ℕ} (xStarFamily : Fin (k + 1) → Fin n → ℝ) :
    (∑ i, xStarFamily i) = xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) := by
  simpa using (Fin.sum_univ_succ (f := xStarFamily))

/-- Helper for Theorem 20.0.1: the binary head-tail infimal convolution is bounded above by
the full family infimal convolution. -/
lemma helperForTheorem_20_0_1_infimalConvolution_headTail_le_infimalConvolutionFamily
    {n k : ℕ} (g : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) :
    infimalConvolution (g 0)
      (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
      infimalConvolutionFamily g xStar := by
  classical
  unfold infimalConvolutionFamily
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨xStarFamily, hsum, rfl⟩
  have hsumHeadTail :
      xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) = xStar := by
    calc
      xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) = ∑ i, xStarFamily i := by
        symm
        exact helperForTheorem_20_0_1_sum_headTail_rewrite
          (n := n) (k := k) (xStarFamily := xStarFamily)
      _ = xStar := hsum
  have htail_le :
      infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
        (∑ j : Fin k, xStarFamily (Fin.succ j)) ≤
        ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) := by
    unfold infimalConvolutionFamily
    refine sInf_le ?_
    refine ⟨(fun j : Fin k => xStarFamily (Fin.succ j)), rfl, rfl⟩
  have hheadTail_le :
      infimalConvolution (g 0)
        (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
        g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) := by
    unfold infimalConvolution
    refine sInf_le ?_
    refine ⟨xStarFamily 0, ∑ j : Fin k, xStarFamily (Fin.succ j), hsumHeadTail, rfl⟩
  have hadd_le :
      g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) ≤
        g 0 (xStarFamily 0) +
          ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htail_le (g 0 (xStarFamily 0))
  calc
    infimalConvolution (g 0)
        (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
        g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) := hheadTail_le
    _ ≤ g 0 (xStarFamily 0) +
          ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) := hadd_le
    _ = ∑ i, g i (xStarFamily i) := by
      symm
      simpa using
        (Fin.sum_univ_succ
          (f := fun i : Fin (k + 1) => g i (xStarFamily i)))

/-- Helper for Theorem 20.0.1: for the conjugate family under the common-domain hypothesis, the
full-family infimal convolution is bounded above by the head-tail binary infimal convolution. -/
lemma helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_le_infimalConvolution_headTail
    {n k : ℕ} (f : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin (k + 1), effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (xStar : Fin n → ℝ) :
    infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar ≤
      infimalConvolution
        (fenchelConjugate n (f 0))
        (fun y =>
          infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y)
        xStar := by
  classical
  unfold infimalConvolution
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨x0, y, hxy, rfl⟩
  let fTail : Fin k → (Fin n → ℝ) → EReal := fun j => f (Fin.succ j)
  have hproperTail :
      ∀ j, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTail j) := by
    intro j
    simpa [fTail] using hproper (Fin.succ j)
  have hdomTail :
      Set.Nonempty
        (⋂ j : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTail j)) := by
    simpa [fTail] using
      helperForTheorem_20_0_1_nonempty_iInter_effectiveDomain_tail
        (f := f) (hdom := hdom)
  have htailNeBot :
      ∀ y' : Fin n → ℝ,
        infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (fTail j)) y' ≠ (⊥ : EReal) := by
    intro y'
    exact
      helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_ne_bot
        (f := fTail) (hproper := hproperTail) (hdom := hdomTail) y'
  let A : Set EReal :=
    {w : EReal |
      ∃ xStarFamily : Fin (k + 1) → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          w = ∑ i, fenchelConjugate n (f i) (xStarFamily i)}
  let T : Set EReal :=
    {w : EReal |
      ∃ tailFamily : Fin k → Fin n → ℝ,
        (∑ j, tailFamily j) = y ∧
          w = ∑ j, fenchelConjugate n (f (Fin.succ j)) (tailFamily j)}
  change sInf A ≤
    fenchelConjugate n (f 0) x0 +
      infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y
  have hA_le_head_add_tail :
      ∀ t : EReal, t ∈ T → sInf A ≤ fenchelConjugate n (f 0) x0 + t := by
    intro t ht
    rcases ht with ⟨tailFamily, hTailSum, rfl⟩
    let xStarFamily : Fin (k + 1) → Fin n → ℝ :=
      Fin.cases (motive := fun _ : Fin (k + 1) => Fin n → ℝ) x0 tailFamily
    have hsumFull : (∑ i, xStarFamily i) = xStar := by
      calc
        (∑ i, xStarFamily i) = x0 + ∑ j : Fin k, tailFamily j := by
          simpa [xStarFamily] using
            (helperForTheorem_20_0_1_sum_headTail_rewrite
              (n := n) (k := k) (xStarFamily := xStarFamily))
        _ = x0 + y := by simp [hTailSum]
        _ = xStar := hxy
    have hmemA :
        (∑ i, fenchelConjugate n (f i) (xStarFamily i)) ∈ A := by
      refine ⟨xStarFamily, hsumFull, rfl⟩
    have hsInf_le :
        sInf A ≤ ∑ i, fenchelConjugate n (f i) (xStarFamily i) := sInf_le hmemA
    have hsumValue :
        (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
          fenchelConjugate n (f 0) x0 +
            ∑ j : Fin k, fenchelConjugate n (f (Fin.succ j)) (tailFamily j) := by
      simpa [xStarFamily] using
        (Fin.sum_univ_succ
          (f := fun i : Fin (k + 1) => fenchelConjugate n (f i) (xStarFamily i)))
    exact hsumValue ▸ hsInf_le
  have htailDef :
      infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y = sInf T := by
    rfl
  have hheadNeBot : fenchelConjugate n (f 0) x0 ≠ (⊥ : EReal) := by
    exact
      (proper_fenchelConjugate_of_proper (n := n) (f := f 0) (hproper 0)).2.2 x0 (by simp)
  by_cases hheadTop : fenchelConjugate n (f 0) x0 = (⊤ : EReal)
  · have htailNeBot' :
      infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y ≠ (⊥ : EReal) := by
      simpa [fTail] using htailNeBot y
    have hrightTop :
        fenchelConjugate n (f 0) x0 +
            infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y =
          (⊤ : EReal) := by
      simpa [hheadTop] using
        (EReal.top_add_of_ne_bot (x := infimalConvolutionFamily
          (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y) htailNeBot')
    have hsInfA_le_top : sInf A ≤ (⊤ : EReal) := le_top
    rw [hrightTop]
    exact hsInfA_le_top
  · let r : ℝ := (fenchelConjugate n (f 0) x0).toReal
    have hheadCoe :
        fenchelConjugate n (f 0) x0 = ((r : ℝ) : EReal) := by
      change fenchelConjugate n (f 0) x0 = (((fenchelConjugate n (f 0) x0).toReal : ℝ) : EReal)
      exact
        helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hheadTop) (hBot := hheadNeBot)
    have hsub_le_t : ∀ t : EReal, t ∈ T → sInf A - (r : EReal) ≤ t := by
      intro t ht
      have hsInfA_le_head_t :
          sInf A ≤ fenchelConjugate n (f 0) x0 + t := hA_le_head_add_tail t ht
      have hsInfA_le_r_t :
          sInf A ≤ (r : EReal) + t := by simpa [hheadCoe]
        using hsInfA_le_head_t
      have hsInfA_le_t_r : sInf A ≤ t + (r : EReal) := by
        simpa [add_comm, add_left_comm, add_assoc] using hsInfA_le_r_t
      exact EReal.sub_le_of_le_add hsInfA_le_t_r
    have hsub_le_sInfT : sInf A - (r : EReal) ≤ sInf T := by
      refine le_sInf ?_
      intro t ht
      exact hsub_le_t t ht
    have hsInfA_le_sInfT_add_r : sInf A ≤ sInf T + (r : EReal) := by
      exact
        (EReal.sub_le_iff_le_add
          (h₁ := Or.inl (EReal.coe_ne_bot r))
          (h₂ := Or.inl (EReal.coe_ne_top r))).1 hsub_le_sInfT
    have hsInfA_le_r_add_sInfT : sInf A ≤ (r : EReal) + sInf T := by
      simpa [add_comm, add_left_comm, add_assoc] using hsInfA_le_sInfT_add_r
    simpa [hheadCoe, htailDef] using hsInfA_le_r_add_sInfT

/-- Helper for Theorem 20.0.1: head-tail decomposition equality for the conjugate family. -/
lemma helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_headTail_eq_infimalConvolution
    {n k : ℕ} (f : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin (k + 1), effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) =
      infimalConvolution
        (fenchelConjugate n (f 0))
        (fun y =>
          infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (f (Fin.succ j))) y) := by
  funext xStar
  apply le_antisymm
  · exact
      helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_le_infimalConvolution_headTail
        (f := f) (hproper := hproper) (hdom := hdom) (xStar := xStar)
  · exact
      helperForTheorem_20_0_1_infimalConvolution_headTail_le_infimalConvolutionFamily
        (g := fun i => fenchelConjugate n (f i)) (xStar := xStar)

/-- Helper for Theorem 20.0.1: under polyhedral/proper/common-domain assumptions, the infimal
convolution family of conjugates is polyhedral. -/
lemma helperForTheorem_20_0_1_polyhedral_infimalConvolutionFamily_fenchelConjugate_of_polyhedral_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    IsPolyhedralConvexFunction n (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  classical
  induction m with
  | zero =>
      have hEqZero :
          infimalConvolutionFamily (fun i : Fin 0 => fenchelConjugate n (f i)) =
            indicatorFunction ({0} : Set (Fin n → ℝ)) := by
        funext x
        by_cases hx : x = 0
        · subst hx
          simp [infimalConvolutionFamily, indicatorFunction]
        · have hx' : ¬ (0 : Fin n → ℝ) = x := by
            simpa [eq_comm] using hx
          simp [infimalConvolutionFamily, indicatorFunction, hx, hx']
      have hpolyZeroSet : IsPolyhedralConvexSet n ({0} : Set (Fin n → ℝ)) := by
        simpa using (helperForTheorem_19_1_zero_set_polyhedral (m := n))
      have hpolyIndicator :
          IsPolyhedralConvexFunction n (indicatorFunction ({0} : Set (Fin n → ℝ))) :=
        helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
          (hCpoly := hpolyZeroSet)
      simpa [hEqZero] using hpolyIndicator
  | succ k ih =>
      let fTail : Fin k → (Fin n → ℝ) → EReal := fun j => f (Fin.succ j)
      let headConj : (Fin n → ℝ) → EReal := fenchelConjugate n (f 0)
      let tailConj : (Fin n → ℝ) → EReal :=
        fun y => infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (fTail j)) y
      have hpolyTail : ∀ j, IsPolyhedralConvexFunction n (fTail j) := by
        intro j
        simpa [fTail] using hpoly (Fin.succ j)
      have hproperTail :
          ∀ j, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTail j) := by
        intro j
        simpa [fTail] using hproper (Fin.succ j)
      have hdomTail :
          Set.Nonempty
            (⋂ j : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTail j)) := by
        simpa [fTail] using
          helperForTheorem_20_0_1_nonempty_iInter_effectiveDomain_tail
            (f := f) (hdom := hdom)
      have hpolyTailConj :
          IsPolyhedralConvexFunction n
            (infimalConvolutionFamily (fun j : Fin k => fenchelConjugate n (fTail j))) :=
        ih (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail) (hdom := hdomTail)
      have hproperHeadConj :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) headConj := by
        simpa [headConj] using
          (proper_fenchelConjugate_of_proper (n := n) (f := f 0) (hproper 0))
      have hproperTailConj :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) tailConj := by
        simpa [tailConj, fTail] using
          (helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_proper
            (f := fTail) (hproper := hproperTail) (hdom := hdomTail))
      have hpolyHeadConj : IsPolyhedralConvexFunction n headConj := by
        simpa [headConj] using
          (polyhedralConvexFunction_fenchelConjugate n (f 0) (hpoly 0))
      have hpolyHeadTail :
          IsPolyhedralConvexFunction n (infimalConvolution headConj tailConj) := by
        exact
          (polyhedralConvexFunction_infimalConvolution n headConj tailConj
            hpolyHeadConj hpolyTailConj hproperHeadConj hproperTailConj).1
      have hheadTailEq :
          infimalConvolutionFamily (fun i : Fin (k + 1) => fenchelConjugate n (f i)) =
            infimalConvolution headConj tailConj := by
        simpa [headConj, tailConj, fTail] using
          (helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_headTail_eq_infimalConvolution
            (f := f) (hproper := hproper) (hdom := hdom))
      simpa [hheadTailEq] using hpolyHeadTail

/-- Helper for Theorem 20.0.1: closure-removal on the infimal convolution side. -/
lemma helperForTheorem_20_0_1_convexFunctionClosure_rhs_eq_self
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
  let g : (Fin n → ℝ) → EReal := infimalConvolutionFamily (fun i => fenchelConjugate n (f i))
  have hproperG :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [g] using
      (helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_proper
        (f := f) (hproper := hproper) (hdom := hdom))
  have hclosedG : ClosedConvexFunction g := by
    refine helperForCorollary_19_1_2_closed_of_polyhedral_proper ?_ hproperG
    have hpolyG :
        IsPolyhedralConvexFunction n
          (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) :=
      helperForTheorem_20_0_1_polyhedral_infimalConvolutionFamily_fenchelConjugate_of_polyhedral_nonempty_iInter_effectiveDomain
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
    simpa [g] using hpolyG
  have hnotBot : ∀ x : Fin n → ℝ, g x ≠ (⊥ : EReal) := by
    intro x
    exact hproperG.2.2 x (by simp)
  simpa [g] using
    (convexFunctionClosure_eq_of_closedConvexFunction (f := g) hclosedG hnotBot)

/-- Theorem 20.0.1: Let f₁, …, fₘ be proper polyhedral convex functions on ℝⁿ with
dom f₁ ∩ ⋯ ∩ dom fₘ ≠ ∅ (formalized as nonempty intersection of effective domains on univ).
Then the Fenchel conjugate of their pointwise sum equals the infimal convolution of their
Fenchel conjugates. -/
theorem fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    fenchelConjugate n (fun x => ∑ i, f i x) =
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) := by
  calc
    fenchelConjugate n (fun x => ∑ i, f i x) =
        convexFunctionClosure (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) :=
      helperForTheorem_20_0_1_main_rewrite_from_section16
        (f := f) (hpoly := hpoly) (hproper := hproper)
    _ = infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) :=
      helperForTheorem_20_0_1_convexFunctionClosure_rhs_eq_self
        (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)

/-- Helper for Corollary 20.0.2: for an empty index family, the split sum is the zero vector. -/
lemma helperForCorollary_20_0_2_sum_eq_zero_of_index_empty
    {n : ℕ} (xStarFamily : Fin 0 → Fin n → ℝ) :
    (∑ i, xStarFamily i) = (0 : Fin n → ℝ) := by
  simp

/-- Helper for Corollary 20.0.2: with empty index set, no nonzero vector has a split-sum
decomposition. -/
lemma helperForCorollary_20_0_2_no_decomposition_of_nonzero_of_index_empty
    {n : ℕ} {xStar : Fin n → ℝ} (hxStar : xStar ≠ 0) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ, (∑ i, xStarFamily i) = xStar := by
  intro hdecomp
  rcases hdecomp with ⟨xStarFamily, hsum⟩
  have hsum_zero : (∑ i, xStarFamily i) = (0 : Fin n → ℝ) :=
    helperForCorollary_20_0_2_sum_eq_zero_of_index_empty (xStarFamily := xStarFamily)
  have hxStar_zero : xStar = (0 : Fin n → ℝ) := by
    calc
      xStar = ∑ i, xStarFamily i := by simpa using hsum.symm
      _ = (0 : Fin n → ℝ) := hsum_zero
  exact hxStar hxStar_zero

/-- Helper for Corollary 20.0.2: when `0 < n`, there exists a nonzero vector in
`Fin n → ℝ`. -/
lemma helperForCorollary_20_0_2_exists_nonzero_vector_of_pos
    {n : ℕ} (hn : 0 < n) :
    ∃ xStar : Fin n → ℝ, xStar ≠ 0 := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => if i = i0 then (1 : ℝ) else 0, ?_⟩
  intro hx
  have hvalue : (1 : ℝ) = 0 := by
    simpa [i0] using congrArg (fun v : Fin n → ℝ => v i0) hx
  exact one_ne_zero hvalue

/-- Helper for Corollary 20.0.2: when `n = 0`, every vector in `Fin n → ℝ` is zero. -/
lemma helperForCorollary_20_0_2_eq_zero_of_n_eq_zero
    {n : ℕ} (hn : n = 0) (xStar : Fin n → ℝ) :
    xStar = 0 := by
  subst hn
  ext i
  exact Fin.elim0 i

/-- Helper for Corollary 20.0.2: when `m = 0` and `0 < n`, it is impossible to
decompose every target vector as a split sum indexed by `Fin 0`. -/
lemma helperForCorollary_20_0_2_not_forall_exists_decomposition_of_index_empty_of_pos
    {n : ℕ} (hn : 0 < n) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ, (∑ i, xStarFamily i) = xStar) := by
  intro hall
  rcases helperForCorollary_20_0_2_exists_nonzero_vector_of_pos (n := n) hn with
    ⟨xStar, hxStar⟩
  rcases hall xStar with ⟨xStarFamily, hsum⟩
  exact
    (helperForCorollary_20_0_2_no_decomposition_of_nonzero_of_index_empty
      (xStar := xStar) hxStar) ⟨xStarFamily, hsum⟩

/-- Helper for Corollary 20.0.2: for an empty index family, the family infimal convolution
is `0` exactly at the zero vector and `⊤` otherwise. -/
lemma helperForCorollary_20_0_2_infimalConvolutionFamily_eq_if_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    infimalConvolutionFamily (n := n) (m := 0) g xStar =
      (if xStar = 0 then (0 : EReal) else ⊤) := by
  by_cases hx : xStar = 0
  · subst hx
    simp [infimalConvolutionFamily]
  · have hx' : ¬ (0 : Fin n → ℝ) = xStar := by
      simpa [eq_comm] using hx
    simp [infimalConvolutionFamily, hx, hx']

/-- Helper for Corollary 20.0.2: for an empty index family, every nonzero target has infimal
convolution value `⊤`. -/
lemma helperForCorollary_20_0_2_infimalConvolutionFamily_eq_top_of_nonzero_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ} (hxStar : xStar ≠ 0) :
    infimalConvolutionFamily (n := n) (m := 0) g xStar = (⊤ : EReal) := by
  simpa [hxStar] using
    (helperForCorollary_20_0_2_infimalConvolutionFamily_eq_if_of_index_empty
      (g := g) (xStar := xStar))

/-- Helper for Corollary 20.0.2: when `m = 0` and `0 < n`, universal attainment with a
split-sum decomposition is impossible (independently of the function family values). -/
lemma helperForCorollary_20_0_2_not_forall_attainment_of_index_empty_of_pos
    {n : ℕ} (hn : 0 < n) (g : Fin 0 → (Fin n → ℝ) → EReal) :
    ¬ (∀ xStar : Fin n → ℝ,
        ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (n := n) (m := 0) g xStar =
              ∑ i, g i (xStarFamily i)) := by
  intro hall
  rcases helperForCorollary_20_0_2_exists_nonzero_vector_of_pos (n := n) hn with
    ⟨xStar, hxStar⟩
  rcases hall xStar with ⟨xStarFamily, hsum, _⟩
  exact
    (helperForCorollary_20_0_2_no_decomposition_of_nonzero_of_index_empty
      (xStar := xStar) hxStar) ⟨xStarFamily, hsum⟩

/-- Helper for Corollary 20.0.2: with empty index set, a nonzero target cannot admit an
attainment witness in split-sum form. -/
lemma helperForCorollary_20_0_2_no_attainmentWitness_of_nonzero_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ} (hxStar : xStar ≠ 0) :
    ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        infimalConvolutionFamily (n := n) (m := 0) g xStar =
          ∑ i, g i (xStarFamily i) := by
  intro hAtt
  rcases hAtt with ⟨xStarFamily, hsum, _⟩
  exact
    (helperForCorollary_20_0_2_no_decomposition_of_nonzero_of_index_empty
      (xStar := xStar) hxStar) ⟨xStarFamily, hsum⟩

/-- Helper for Corollary 20.0.2: when `m = 0` and `0 < n`, there exists a target vector
without a split-sum attainment witness. -/
lemma helperForCorollary_20_0_2_exists_counterexample_attainment_of_index_empty_of_pos
    {n : ℕ} (hn : 0 < n) (g : Fin 0 → (Fin n → ℝ) → EReal) :
    ∃ xStar : Fin n → ℝ,
      ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (n := n) (m := 0) g xStar =
            ∑ i, g i (xStarFamily i) := by
  rcases helperForCorollary_20_0_2_exists_nonzero_vector_of_pos (n := n) hn with
    ⟨xStar, hxStar⟩
  refine ⟨xStar, ?_⟩
  exact
    helperForCorollary_20_0_2_no_attainmentWitness_of_nonzero_of_index_empty
      (g := g) (xStar := xStar) hxStar

/-- Helper for Corollary 20.0.2: when `m = 0` and `0 < n`, there exists a nonzero target
vector that has no split-sum attainment witness for the conjugate family. -/
lemma helperForCorollary_20_0_2_exists_nonzero_counterexample_for_fenchelFamily_of_index_empty_of_pos
    {n : ℕ} (hn : 0 < n) (f : Fin 0 → (Fin n → ℝ) → EReal) :
    ∃ xStar : Fin n → ℝ,
      xStar ≠ 0 ∧
        ¬ ∃ xStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
              ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  rcases helperForCorollary_20_0_2_exists_nonzero_vector_of_pos (n := n) hn with
    ⟨xStar, hxStar⟩
  refine ⟨xStar, hxStar, ?_⟩
  exact
    helperForCorollary_20_0_2_no_attainmentWitness_of_nonzero_of_index_empty
      (g := fun i => fenchelConjugate n (f i)) (xStar := xStar) hxStar

/-- Helper for Corollary 20.0.2: when `m = 0` and `0 < n`, universal split-sum
attainment fails for the conjugate family. -/
lemma helperForCorollary_20_0_2_not_forall_attainment_for_fenchelFamily_of_index_empty_of_pos
    {n : ℕ} (hn : 0 < n) (f : Fin 0 → (Fin n → ℝ) → EReal) :
    ¬ (∀ yStar : Fin n → ℝ,
        ∃ yStarFamily : Fin 0 → Fin n → ℝ,
          (∑ i, yStarFamily i) = yStar ∧
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) yStar =
              ∑ i, fenchelConjugate n (f i) (yStarFamily i)) := by
  intro hall
  rcases
      helperForCorollary_20_0_2_exists_nonzero_counterexample_for_fenchelFamily_of_index_empty_of_pos
        (n := n) hn (f := f) with
    ⟨yStar, _, hyNoWitness⟩
  exact hyNoWitness (hall yStar)

/-- Helper for Corollary 20.0.2: with empty index set, any split-sum attainment witness
forces the target vector to be zero. -/
lemma helperForCorollary_20_0_2_attainmentWitness_target_eq_zero_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) {xStar : Fin n → ℝ}
    (hAtt :
      ∃ xStarFamily : Fin 0 → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          infimalConvolutionFamily (n := n) (m := 0) g xStar =
            ∑ i, g i (xStarFamily i)) :
    xStar = (0 : Fin n → ℝ) := by
  rcases hAtt with ⟨xStarFamily, hsum, _⟩
  calc
    xStar = ∑ i, xStarFamily i := by simpa using hsum.symm
    _ = (0 : Fin n → ℝ) :=
      helperForCorollary_20_0_2_sum_eq_zero_of_index_empty (xStarFamily := xStarFamily)

/-- Helper for Corollary 20.0.2: with empty index set and zero target, a split-sum
attainment witness exists. -/
lemma helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) :
    ∃ xStarFamily : Fin 0 → Fin n → ℝ,
      (∑ i, xStarFamily i) = (0 : Fin n → ℝ) ∧
        infimalConvolutionFamily (n := n) (m := 0) g (0 : Fin n → ℝ) =
          ∑ i, g i (xStarFamily i) := by
  refine ⟨(fun _ => (0 : Fin n → ℝ)), ?_, ?_⟩
  · simp
  ·
    have hInfZero :
        infimalConvolutionFamily (n := n) (m := 0) g (0 : Fin n → ℝ) =
          (0 : EReal) := by
      simpa using
        (helperForCorollary_20_0_2_infimalConvolutionFamily_eq_if_of_index_empty
          (g := g) (xStar := (0 : Fin n → ℝ)))
    have hSumZero :
        (∑ i, g i ((fun _ => (0 : Fin n → ℝ)) i)) = (0 : EReal) := by
      simp
    calc
      infimalConvolutionFamily (n := n) (m := 0) g (0 : Fin n → ℝ) =
          (0 : EReal) := hInfZero
      _ = ∑ i, g i ((fun _ => (0 : Fin n → ℝ)) i) := by
          simp

/-- Helper for Corollary 20.0.2: with empty index set, a split-sum attainment witness exists
exactly at the zero target. -/
lemma helperForCorollary_20_0_2_exists_attainmentWitness_iff_target_eq_zero_of_index_empty
    {n : ℕ} (g : Fin 0 → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    (∃ xStarFamily : Fin 0 → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        infimalConvolutionFamily (n := n) (m := 0) g xStar =
          ∑ i, g i (xStarFamily i)) ↔
      xStar = 0 := by
  constructor
  · intro hAtt
    exact
      helperForCorollary_20_0_2_attainmentWitness_target_eq_zero_of_index_empty
        (n := n) (g := g) (xStar := xStar) hAtt
  · intro hxStar
    subst hxStar
    exact
      helperForCorollary_20_0_2_exists_attainmentWitness_of_zero_of_index_empty
        (n := n) (g := g)

/-- Helper for Corollary 20.0.2: if the infimal-convolution value is not `⊤` and one has
the standard `⊤`-or-attainment alternative, then an attainment witness exists in the
orientation used by the corollary statement. -/
lemma helperForCorollary_20_0_2_exists_attainment_of_ne_top_of_top_or_exists
    {n m : ℕ} (g : Fin m → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ)
    (hTopOrAttained :
      infimalConvolutionFamily g xStar = ⊤ ∨
        ∃ xStarFamily : Fin m → Fin n → ℝ,
          (∑ i, xStarFamily i) = xStar ∧
            (∑ i, g i (xStarFamily i)) = infimalConvolutionFamily g xStar)
    (htop : infimalConvolutionFamily g xStar ≠ (⊤ : EReal)) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        infimalConvolutionFamily g xStar = ∑ i, g i (xStarFamily i) := by
  rcases hTopOrAttained with htopEq | hAttained
  · exact (htop htopEq).elim
  · rcases hAttained with ⟨xStarFamily, hsum, hval⟩
    refine ⟨xStarFamily, hsum, ?_⟩
    simpa using hval.symm

/-- Helper for Corollary 20.0.2: rewrite a split sum over `Fin (k+1)` as head plus tail. -/
lemma helperForCorollary_20_0_2_sum_headTail_rewrite
    {n k : ℕ} (xStarFamily : Fin (k + 1) → Fin n → ℝ) :
    (∑ i, xStarFamily i) = xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) := by
  simpa using (Fin.sum_univ_succ (f := xStarFamily))

/-- Helper for Corollary 20.0.2: from a head point and a tail family summing to `y`,
build a full `Fin (k+1)` split family and rewrite its value-sum in head-tail form. -/
lemma helperForCorollary_20_0_2_liftWitness_from_headTail
    {n k : ℕ} (g : Fin (k + 1) → (Fin n → ℝ) → EReal)
    {xStar x0 y : Fin n → ℝ}
    (tailFamily : Fin k → Fin n → ℝ)
    (hHeadTail : x0 + y = xStar)
    (hTailSum : (∑ j, tailFamily j) = y) :
    ∃ xStarFamily : Fin (k + 1) → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        (∑ i, g i (xStarFamily i)) =
          g 0 x0 + ∑ j : Fin k, g (Fin.succ j) (tailFamily j) := by
  let xStarFamily : Fin (k + 1) → Fin n → ℝ :=
    Fin.cases (motive := fun _ : Fin (k + 1) => Fin n → ℝ) x0 tailFamily
  refine ⟨xStarFamily, ?_, ?_⟩
  · calc
      (∑ i, xStarFamily i) =
          x0 + ∑ j : Fin k, tailFamily j := by
            simpa using
              (helperForCorollary_20_0_2_sum_headTail_rewrite
                (n := n) (k := k) (xStarFamily := xStarFamily))
      _ = x0 + y := by simp [hTailSum]
      _ = xStar := hHeadTail
  · simpa using
      (Fin.sum_univ_succ
        (f := fun i : Fin (k + 1) => g i (xStarFamily i)))

/-- Helper for Corollary 20.0.2: from a common effective-domain point for a `Fin (k+1)`
family, obtain one for its tail `Fin k` subfamily. -/
lemma helperForCorollary_20_0_2_nonempty_iInter_effectiveDomain_tail
    {n k : ℕ} (f : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (hdom :
      Set.Nonempty
        (⋂ i : Fin (k + 1), effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    Set.Nonempty
      (⋂ j : Fin k, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f (Fin.succ j))) := by
  rcases hdom with ⟨x0, hx0⟩
  refine ⟨x0, ?_⟩
  refine Set.mem_iInter.2 ?_
  intro j
  exact (Set.mem_iInter.mp hx0) (Fin.succ j)

/-- Helper for Corollary 20.0.2: the pointwise sum `x ↦ ∑ i, f i x` is proper whenever the
summands are proper and their effective domains have a common point. -/
lemma helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => ∑ i, f i x) := by
  rcases hdom with ⟨x0, hx0⟩
  have hbot_i : ∀ i : Fin m, f i x0 ≠ (⊥ : EReal) := by
    intro i
    exact (hproper i).2.2 x0 (by simp)
  have htop_i : ∀ i : Fin m, f i x0 ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
      (f := f i) ((Set.mem_iInter.mp hx0) i)
  have hsum_real :
      (∑ i, f i x0) = (((∑ i, (f i x0).toReal) : ℝ) : EReal) := by
    calc
      (∑ i, f i x0) = ∑ i, (((f i x0).toReal : ℝ) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := htop_i i) (hBot := hbot_i i)
      _ = (((∑ i, (f i x0).toReal) : ℝ) : EReal) := by
        symm
        exact section16_coe_finset_sum
          (s := Finset.univ) (b := fun i : Fin m => (f i x0).toReal)
  have hsum_ne_top : (∑ i, f i x0) ≠ (⊤ : EReal) := by
    intro htop
    have htop' : ((((∑ i, (f i x0).toReal) : ℝ) : EReal)) = (⊤ : EReal) := by
      simp [hsum_real] at htop
    exact EReal.coe_ne_top _ htop'
  exact properConvexFunctionOn_sum_of_exists_ne_top
    (f := f) hproper ⟨x0, hsum_ne_top⟩

/-- Helper for Corollary 20.0.2: under Theorem 20.0.1 hypotheses, the family infimal
convolution of conjugates is proper. -/
lemma helperForCorollary_20_0_2_properInfConjFamily_of_polyhedral_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (infimalConvolutionFamily (fun i => fenchelConjugate n (f i))) := by
  have hproperSum :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => ∑ i, f i x) :=
    helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
      (f := f) (hproper := hproper) (hdom := hdom)
  have hproperConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (fun x => ∑ i, f i x)) :=
    proper_fenchelConjugate_of_proper (n := n) (f := fun x => ∑ i, f i x) hproperSum
  have hEq :
      fenchelConjugate n (fun x => ∑ i, f i x) =
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
      (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
  simpa [hEq] using hproperConj

/-- Helper for Corollary 20.0.2: the binary head-tail infimal convolution is bounded above by
the full family infimal convolution. -/
lemma helperForCorollary_20_0_2_infimalConvolution_headTail_le_infimalConvolutionFamily
    {n k : ℕ} (g : Fin (k + 1) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) :
    infimalConvolution (g 0)
      (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
      infimalConvolutionFamily g xStar := by
  classical
  unfold infimalConvolutionFamily
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨xStarFamily, hsum, rfl⟩
  have hsumHeadTail :
      xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) = xStar := by
    calc
      xStarFamily 0 + ∑ j : Fin k, xStarFamily (Fin.succ j) = ∑ i, xStarFamily i := by
        symm
        exact helperForCorollary_20_0_2_sum_headTail_rewrite
          (n := n) (k := k) (xStarFamily := xStarFamily)
      _ = xStar := hsum
  have htail_le :
      infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
        (∑ j : Fin k, xStarFamily (Fin.succ j)) ≤
        ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) := by
    unfold infimalConvolutionFamily
    refine sInf_le ?_
    refine ⟨(fun j : Fin k => xStarFamily (Fin.succ j)), rfl, rfl⟩
  have hheadTail_le :
      infimalConvolution (g 0)
        (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
        g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) := by
    unfold infimalConvolution
    refine sInf_le ?_
    refine ⟨xStarFamily 0, ∑ j : Fin k, xStarFamily (Fin.succ j), hsumHeadTail, rfl⟩
  have hadd_le :
      g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) ≤
        g 0 (xStarFamily 0) +
          ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htail_le (g 0 (xStarFamily 0))
  calc
    infimalConvolution (g 0)
        (fun y => infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j)) y) xStar ≤
        g 0 (xStarFamily 0) +
          infimalConvolutionFamily (fun j : Fin k => g (Fin.succ j))
            (∑ j : Fin k, xStarFamily (Fin.succ j)) := hheadTail_le
    _ ≤ g 0 (xStarFamily 0) +
          ∑ j : Fin k, g (Fin.succ j) (xStarFamily (Fin.succ j)) := hadd_le
    _ = ∑ i, g i (xStarFamily i) := by
      symm
      simpa using
        (Fin.sum_univ_succ
          (f := fun i : Fin (k + 1) => g i (xStarFamily i)))

/-- Helper for Corollary 20.0.2: for a nonempty family of proper polyhedral summands with a
common effective-domain point, the pointwise sum is polyhedral. -/
lemma helperForCorollary_20_0_2_polyhedralSum_of_polyhedral_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m) :
    IsPolyhedralConvexFunction n (fun x => ∑ i, f i x) := by
  classical
  cases m with
  | zero =>
      exact (Nat.not_lt_zero 0 hmPos).elim
  | succ m =>
      cases m with
      | zero =>
          simpa using hpoly (0 : Fin 1)
      | succ k =>
          let fTail : Fin (k + 1) → (Fin n → ℝ) → EReal := fun j => f (Fin.succ j)
          have hpolyTail : ∀ j, IsPolyhedralConvexFunction n (fTail j) := by
            intro j
            simpa [fTail] using hpoly (Fin.succ j)
          have hproperTail :
              ∀ j, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTail j) := by
            intro j
            simpa [fTail] using hproper (Fin.succ j)
          have hdomTail :
              Set.Nonempty
                (⋂ j : Fin (k + 1),
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTail j)) := by
            exact
              helperForCorollary_20_0_2_nonempty_iInter_effectiveDomain_tail
                (f := f) (hdom := hdom)
          have hmTailPos : 0 < k + 1 := Nat.succ_pos _
          have hpolyTailSum :
              IsPolyhedralConvexFunction n (fun x => ∑ j : Fin (k + 1), fTail j x) :=
            helperForCorollary_20_0_2_polyhedralSum_of_polyhedral_nonempty_iInter_effectiveDomain
              (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail)
              (hdom := hdomTail) (hmPos := hmTailPos)
          have hpolyAdd :
              IsPolyhedralConvexFunction n
                (fun x => f 0 x + ∑ j : Fin (k + 1), fTail j x) := by
            exact
              polyhedralConvexFunction_add_of_proper
                n (f 0)
                (fun x => ∑ j : Fin (k + 1), fTail j x)
                (hpoly (0 : Fin (k + 2))) hpolyTailSum
                (hproper (0 : Fin (k + 2)))
                (helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
                  (f := fTail) (hproper := hproperTail) (hdom := hdomTail))
          have hsumRewrite :
              (fun x => ∑ i : Fin (k + 2), f i x) =
                (fun x => f 0 x + ∑ j : Fin (k + 1), fTail j x) := by
            funext x
            simp [fTail, Fin.sum_univ_succ]
          simpa [hsumRewrite] using hpolyAdd

/-- Helper for Corollary 20.0.2: under the hypotheses of Theorem 20.0.1 and `0 < m`,
the family infimal-convolution value is either `⊤` or attained in split-sum form. -/
lemma helperForCorollary_20_0_2_topOrAttained_of_polyhedral_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m)
    (xStar : Fin n → ℝ) :
    infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
      ∃ xStarFamily : Fin m → Fin n → ℝ,
        (∑ i, xStarFamily i) = xStar ∧
          (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
            infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
  classical
  cases m with
  | zero =>
      exact (Nat.not_lt_zero 0 hmPos).elim
  | succ m =>
      cases m with
      | zero =>
          refine Or.inr ?_
          refine ⟨fun _ => xStar, ?_, ?_⟩
          · simp
          · unfold infimalConvolutionFamily
            apply le_antisymm
            · refine le_sInf ?_
              intro z hz
              rcases hz with ⟨xStarFamily, hsum, rfl⟩
              simp at hsum
              simp [hsum]
            · refine sInf_le ?_
              refine ⟨fun _ => xStar, ?_, rfl⟩
              simp
      | succ k =>
          let fTail : Fin (k + 1) → (Fin n → ℝ) → EReal :=
            fun j => f (Fin.succ j)
          let headConj : (Fin n → ℝ) → EReal := fenchelConjugate n (f 0)
          let tailConj : (Fin n → ℝ) → EReal :=
            fun y => infimalConvolutionFamily (fun j : Fin (k + 1) => fenchelConjugate n (fTail j)) y
          let headTailInf : (Fin n → ℝ) → EReal := infimalConvolution headConj tailConj
          have hpolyTail : ∀ j, IsPolyhedralConvexFunction n (fTail j) := by
            intro j
            simpa [fTail] using hpoly (Fin.succ j)
          have hproperTail :
              ∀ j, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTail j) := by
            intro j
            simpa [fTail] using hproper (Fin.succ j)
          have hdomTail :
              Set.Nonempty
                (⋂ j : Fin (k + 1),
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTail j)) := by
            exact
              helperForCorollary_20_0_2_nonempty_iInter_effectiveDomain_tail
                (f := f) (hdom := hdom)
          have hmTailPos : 0 < k + 1 := Nat.succ_pos _
          have htailEq :
              fenchelConjugate n (fun x => ∑ j : Fin (k + 1), fTail j x) = tailConj := by
            simpa [tailConj] using
              (fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
                (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail) (hdom := hdomTail))
          have hpolyTailSum :
              IsPolyhedralConvexFunction n (fun x => ∑ j : Fin (k + 1), fTail j x) := by
            exact
              helperForCorollary_20_0_2_polyhedralSum_of_polyhedral_nonempty_iInter_effectiveDomain
                (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail)
                (hdom := hdomTail) (hmPos := hmTailPos)
          have hpolyTailConj :
              IsPolyhedralConvexFunction n
                (fenchelConjugate n (fun x => ∑ j : Fin (k + 1), fTail j x)) := by
            exact
              polyhedralConvexFunction_fenchelConjugate n
                (fun x => ∑ j : Fin (k + 1), fTail j x) hpolyTailSum
          have hpolyTailInf : IsPolyhedralConvexFunction n tailConj := by
            simpa [htailEq] using hpolyTailConj
          have hproperTailInf :
              ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) tailConj := by
            simpa [tailConj] using
              (helperForCorollary_20_0_2_properInfConjFamily_of_polyhedral_nonempty_iInter_effectiveDomain
                (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail) (hdom := hdomTail))
          have hpolyHeadConj : IsPolyhedralConvexFunction n headConj := by
            simpa [headConj] using
              (polyhedralConvexFunction_fenchelConjugate n (f 0) (hpoly 0))
          have hproperHeadConj :
              ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) headConj := by
            simpa [headConj] using
              (proper_fenchelConjugate_of_proper (n := n) (f := f 0) (hproper 0))
          have hheadTail_le :
              headTailInf xStar ≤
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
            simpa [headTailInf, headConj, tailConj, fTail] using
              helperForCorollary_20_0_2_infimalConvolution_headTail_le_infimalConvolutionFamily
                (g := fun i => fenchelConjugate n (f i)) (xStar := xStar)
          have hbinaryNeBot : headTailInf xStar ≠ (⊥ : EReal) := by
            let fPair : Fin 2 → (Fin n → ℝ) → EReal :=
              fun i => if i = 0 then f 0 else fun x => ∑ j : Fin (k + 1), fTail j x
            have hproperTailSum :
                ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                  (fun x => ∑ j : Fin (k + 1), fTail j x) :=
              helperForCorollary_20_0_2_properSum_of_commonEffectiveDomain
                (f := fTail) (hproper := hproperTail) (hdom := hdomTail)
            have hproperPair :
                ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fPair i) := by
              intro i
              fin_cases i
              · simpa [fPair] using hproper (0 : Fin (k + 2))
              · simpa [fPair] using hproperTailSum
            rcases hdom with ⟨x0, hx0⟩
            have hx0Tail_i :
                ∀ j : Fin (k + 1),
                  x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTail j) := by
              intro j
              simpa [fTail] using (Set.mem_iInter.mp hx0) (Fin.succ j)
            have htopTail_i : ∀ j : Fin (k + 1), fTail j x0 ≠ (⊤ : EReal) := by
              intro j
              exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ)))
                (f := fTail j) (hx0Tail_i j)
            have hbotTail_i : ∀ j : Fin (k + 1), fTail j x0 ≠ (⊥ : EReal) := by
              intro j
              have hx0_univ : x0 ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
              exact hproperTail j |>.2.2 x0 hx0_univ
            have hsumTail_real :
                (∑ j : Fin (k + 1), fTail j x0) =
                  (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal) := by
              calc
                (∑ j : Fin (k + 1), fTail j x0) =
                    ∑ j : Fin (k + 1), (((fTail j x0).toReal : ℝ) : EReal) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                        (hTop := htopTail_i j) (hBot := hbotTail_i j)
                _ = (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal) := by
                    symm
                    exact section16_coe_finset_sum (s := Finset.univ)
                      (b := fun j : Fin (k + 1) => (fTail j x0).toReal)
            have hsumTail_ne_top :
                (∑ j : Fin (k + 1), fTail j x0) ≠ (⊤ : EReal) := by
              intro htop
              have htop' :
                  (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal) = (⊤ : EReal) := by
                simp [hsumTail_real] at htop
              exact EReal.coe_ne_top _ htop'
            have hx0Head :
                x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPair 0) := by
              simpa [fPair] using (Set.mem_iInter.mp hx0) (0 : Fin (k + 2))
            have hx0Tail :
                x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPair 1) := by
              refine ⟨∑ j : Fin (k + 1), (fTail j x0).toReal, ?_⟩
              change
                x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧
                  fPair 1 x0 ≤ (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal)
              have hx0_univ : x0 ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
              refine And.intro hx0_univ ?_
              calc
                fPair 1 x0 = (∑ j : Fin (k + 1), fTail j x0) := by simp [fPair]
                _ = (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal) := hsumTail_real
                _ ≤ (((∑ j : Fin (k + 1), (fTail j x0).toReal) : ℝ) : EReal) := le_rfl
            have hdomPair :
                Set.Nonempty
                  (⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPair i)) := by
              refine ⟨x0, ?_⟩
              refine Set.mem_iInter.2 ?_
              intro i
              fin_cases i
              · exact hx0Head
              · exact hx0Tail
            have hpairNeBot :
                infimalConvolutionFamily (fun i => fenchelConjugate n (fPair i)) xStar ≠
                  (⊥ : EReal) :=
              helperForTheorem_20_0_1_infimalConvolutionFamily_fenchelConjugate_ne_bot
                (f := fPair) (hproper := hproperPair) (hdom := hdomPair) xStar
            have hpairEq :
                infimalConvolutionFamily (fun i => fenchelConjugate n (fPair i)) =
                  infimalConvolution
                    (fenchelConjugate n (f 0))
                    (fenchelConjugate n (fun x => ∑ j : Fin (k + 1), fTail j x)) := by
              simpa [fPair] using
                (infimalConvolution_eq_infimalConvolutionFamily_two
                  (f := fenchelConjugate n (f 0))
                  (g := fenchelConjugate n (fun x => ∑ j : Fin (k + 1), fTail j x))).symm
            have hpairNeBot' :
                infimalConvolution
                    (fenchelConjugate n (f 0))
                    (fenchelConjugate n (fun x => ∑ j : Fin (k + 1), fTail j x))
                    xStar ≠ (⊥ : EReal) := by
              simpa [hpairEq] using hpairNeBot
            simpa [headTailInf, headConj, tailConj, htailEq] using hpairNeBot'
          have hbinaryAttained :
              ∃ y : Fin n → ℝ, headTailInf xStar = headConj (xStar - y) + tailConj y := by
            by_cases hbinaryTop : headTailInf xStar = (⊤ : EReal)
            · exact
                helperForCorollary_19_3_4_attainment_of_top_value
                  (f₁ := headConj) (f₂ := tailConj) (x := xStar) hbinaryTop
            · have hbinaryReal :
                  headTailInf xStar = (((headTailInf xStar).toReal : ℝ) : EReal) :=
                helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                  (hTop := hbinaryTop) (hBot := hbinaryNeBot)
              exact
                helperForCorollary_19_3_4_attainment_of_finite_value
                  (f₁ := headConj) (f₂ := tailConj)
                  (hf₁poly := hpolyHeadConj) (hf₂poly := hpolyTailInf)
                  (hproper₁ := hproperHeadConj) (hproper₂ := hproperTailInf)
                  (x := xStar) (r := (headTailInf xStar).toReal) hbinaryReal
          rcases hbinaryAttained with ⟨y, hbinaryEq⟩
          have htailTopOrAttainedY :
              tailConj y = ⊤ ∨
                ∃ xStarTail : Fin (k + 1) → Fin n → ℝ,
                  (∑ j, xStarTail j) = y ∧
                    (∑ j, fenchelConjugate n (fTail j) (xStarTail j)) = tailConj y := by
            exact
              helperForCorollary_20_0_2_topOrAttained_of_polyhedral_nonempty_iInter_effectiveDomain
                (f := fTail) (hpoly := hpolyTail) (hproper := hproperTail) (hdom := hdomTail)
                (hmPos := hmTailPos) (xStar := y)
          have htailWitness :
              ∃ xStarTail : Fin (k + 1) → Fin n → ℝ,
                (∑ j, xStarTail j) = y ∧
                  (∑ j, fenchelConjugate n (fTail j) (xStarTail j)) = tailConj y := by
            rcases htailTopOrAttainedY with htailTop | htailAttained
            · exact
                section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
                  (n := n) (m := k + 1) hmTailPos
                  (g := fun j => fenchelConjugate n (fTail j)) (xStar := y) htailTop
            · exact htailAttained
          rcases htailWitness with ⟨tailFamily, htailSum, htailVal⟩
          have hHeadTailEq : (xStar - y) + y = xStar := by
            simp [sub_eq_add_neg, add_left_comm, add_comm]
          rcases
            helperForCorollary_20_0_2_liftWitness_from_headTail
              (g := fun i => fenchelConjugate n (f i))
              (tailFamily := tailFamily)
              (hHeadTail := hHeadTailEq)
              (hTailSum := htailSum) with
            ⟨xStarFamily, hsumFamily, hsumValue⟩
          have hsumEqHeadTail :
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) = headTailInf xStar := by
            calc
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                  headConj (xStar - y) +
                    ∑ j : Fin (k + 1), fenchelConjugate n (fTail j) (tailFamily j) := by
                      simpa [headConj, fTail] using hsumValue
              _ = headConj (xStar - y) + tailConj y := by
                    simp [htailVal]
              _ = headTailInf xStar := hbinaryEq.symm
          have hfamilyLeWitness :
              infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar ≤
                (∑ i, fenchelConjugate n (f i) (xStarFamily i)) := by
            unfold infimalConvolutionFamily
            exact sInf_le ⟨xStarFamily, hsumFamily, rfl⟩
          have hvalueEq :
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
            apply le_antisymm
            · calc
                (∑ i, fenchelConjugate n (f i) (xStarFamily i)) = headTailInf xStar :=
                  hsumEqHeadTail
                _ ≤ infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar :=
                  hheadTail_le
            · simpa using hfamilyLeWitness
          exact Or.inr ⟨xStarFamily, hsumFamily, hvalueEq⟩

/-- Corollary 20.0.2: Under the hypotheses of Theorem 20.0.1 and `0 < m`,
for each `x⋆ ∈ ℝ^n`
there exists a decomposition `x⋆ = ∑ i, x⋆ᵢ` such that
`(f₁^* ⋄ ⋯ ⋄ fₘ^*)(x⋆) = ∑ i, fᵢ^*(x⋆ᵢ)`, i.e. the infimum in the
definition of the infimal convolution of the conjugates is attained. -/
theorem infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
    {n m : ℕ} (f : Fin m → (Fin n → ℝ) → EReal)
    (hpoly : ∀ i, IsPolyhedralConvexFunction n (f i))
    (hproper : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom :
      Set.Nonempty
        (⋂ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    (hmPos : 0 < m)
    (xStar : Fin n → ℝ) :
    ∃ xStarFamily : Fin m → Fin n → ℝ,
      (∑ i, xStarFamily i) = xStar ∧
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar =
          ∑ i, fenchelConjugate n (f i) (xStarFamily i) := by
  classical
  by_cases htop :
      infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = (⊤ : EReal)
  · rcases
      section16_attainment_when_infimalConvolutionFamily_eq_top_of_pos
        (n := n) (m := m) hmPos
        (g := fun i => fenchelConjugate n (f i)) (xStar := xStar) htop with
      ⟨xStarFamily, hsum, hval⟩
    refine ⟨xStarFamily, hsum, ?_⟩
    simpa using hval.symm
  · have hTopOrAttained :
        infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar = ⊤ ∨
          ∃ xStarFamily : Fin m → Fin n → ℝ,
            (∑ i, xStarFamily i) = xStar ∧
              (∑ i, fenchelConjugate n (f i) (xStarFamily i)) =
                infimalConvolutionFamily (fun i => fenchelConjugate n (f i)) xStar := by
      exact
        helperForCorollary_20_0_2_topOrAttained_of_polyhedral_nonempty_iInter_effectiveDomain
          (f := f) (hpoly := hpoly) (hproper := hproper) (hdom := hdom)
          (hmPos := hmPos) (xStar := xStar)
    exact
      helperForCorollary_20_0_2_exists_attainment_of_ne_top_of_top_or_exists
        (g := fun i => fenchelConjugate n (f i)) (xStar := xStar)
        hTopOrAttained htop

end Section20
end Chap04
