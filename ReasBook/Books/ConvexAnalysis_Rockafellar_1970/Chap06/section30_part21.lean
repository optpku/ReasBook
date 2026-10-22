/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part20

section Chap06
section Section30

/-- Helper for Theorem 6.30.22: at fixed `x`, expanding the enlarged adjoint integrand isolates
the `x₀` block, the `(u, xShift)` block, and the constant term `-⟪x, x*⟫`. -/
lemma helperForTheorem_6_30_22_fixedX_integrand_split
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (x xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (x0 : Fin n → ℝ) (u : Fin m → ℝ) (xShift : Fin m → Fin n → ℝ) :
    enlargedPerturbationProgramBifunction f0 f
        ({ u := u, x0 := x0, xShift := xShift } : EnlargedPerturbationParameter m n) x -
      (((x ⬝ᵥ xStar : ℝ) : EReal)) +
      (((enlargedPerturbationDualPairing
          ({ u := u, x0 := x0, xShift := xShift } : EnlargedPerturbationParameter m n) wStar :
            ℝ) : EReal)) =
    (f0 (x - x0) + (((x0 ⬝ᵥ wStar.x0Star : ℝ) : EReal))) +
      (indicatorFunction (enlargedPerturbationProgramFeasibleSet f
          ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
            EnlargedPerturbationParameter m n)) x +
        (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
        ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) +
      (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
  have hpairing :
      (((enlargedPerturbationDualPairing
          ({ u := u, x0 := x0, xShift := xShift } : EnlargedPerturbationParameter m n) wStar :
            ℝ) : EReal)) =
        (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
          (((x0 ⬝ᵥ wStar.x0Star : ℝ) : EReal)) +
          ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) := by
    have hsum :
        ((((∑ i : Fin m, (xShift i ⬝ᵥ wStar.xShiftStar i : ℝ)) : ℝ) : EReal)) =
          ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) := by
      simpa using
        helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe
          (s := Finset.univ) (r := fun i : Fin m => xShift i ⬝ᵥ wStar.xShiftStar i)
    -- Expand the real pairing and rewrite its finite translated-coordinate sum inside `EReal`.
    rw [enlargedPerturbationDualPairing]
    calc
      ((((u ⬝ᵥ wStar.uStar : ℝ) + (x0 ⬝ᵥ wStar.x0Star : ℝ) +
            ∑ i : Fin m, (xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : ℝ) : EReal)) =
          ((((u ⬝ᵥ wStar.uStar : ℝ) + (x0 ⬝ᵥ wStar.x0Star : ℝ) : ℝ) : EReal)) +
            ((((∑ i : Fin m, (xShift i ⬝ᵥ wStar.xShiftStar i : ℝ)) : ℝ) : EReal)) := by
              rw [EReal.coe_add]
      _ =
          ((((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
              (((x0 ⬝ᵥ wStar.x0Star : ℝ) : EReal))) +
            ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) := by
              rw [EReal.coe_add, hsum]
      _ =
          (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
            (((x0 ⬝ᵥ wStar.x0Star : ℝ) : EReal)) +
            ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) := by
              simp [add_assoc]
  -- Unfold the bifunction and regroup the three independent blocks of the integrand.
  rw [enlargedPerturbationProgramBifunction, hpairing]
  simp [enlargedPerturbationProgramFeasibleSet, sub_eq_add_neg,
    EReal.coe_add, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 6.30.22: on the nonnegative branch, the finite sum of negated scaled
Fenchel conjugates is the negation of the finite conjugate sum. -/
lemma helperForTheorem_6_30_22_sum_neg_scaledConjugates_eq_neg_sum
    {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    (∑ i : Fin m,
        -fenchelConjugate n
          (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
          (wStar.xShiftStar i)) =
      -(∑ i : Fin m,
        fenchelConjugate n
          (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
          (wStar.xShiftStar i)) := by
  let scaledConj : Fin m → EReal := fun i =>
    fenchelConjugate n
      (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
      (wStar.xShiftStar i)
  have hscaled_ne_bot : ∀ i : Fin m, scaledConj i ≠ (⊥ : EReal) := by
    -- Properness of each scaled block rules out `-∞` for its Fenchel conjugate.
    intro i
    have hproperFi : ProperConvexERealFunction (F := Fin n → ℝ) (f i) :=
      helperForLemma_26_2_properConvexERealFunction (hf i)
    have hscaledOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z)) := by
      simpa using
        helperForTheorem_6_30_21_properConvexFunctionOn_univ_mul_of_nonneg
          (f := f i) (hf := hproperFi) (hlam := hnonneg i)
    have hscaled : ProperConvexERealFunction (F := Fin n → ℝ)
        (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z)) :=
      helperForLemma_26_2_properConvexERealFunction hscaledOn
    exact helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
      (hf := hscaled.1) (xStar := wStar.xShiftStar i)
  -- Push the finite negation through the `Fin m`-sum once the `⊥` obstruction is excluded.
  have hneg :
      -(∑ i : Fin m, scaledConj i) =
        ∑ i : Fin m, (-scaledConj i) := by
    exact section16_neg_sum_eq_sum_neg
      (s := Finset.univ) (b := scaledConj) (by
        intro i hi
        exact hscaled_ne_bot i)
  simpa [scaledConj] using hneg.symm

/-- Helper for Theorem 6.30.22: on the nonnegative branch, the explicit dual objective can be
packaged as the head negative conjugate plus the finite sum of the negated scaled tail
conjugates. -/
lemma helperForTheorem_6_30_22_dualObjective_eq_headPlusSumNegScaledConjugates
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    enlargedPerturbationDualObjective f0 f wStar =
      -fenchelConjugate n f0 wStar.x0Star +
        ∑ i : Fin m,
          -fenchelConjugate n
            (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
            (wStar.xShiftStar i) := by
  -- Rewrite the tail subtraction as addition of the negated finite conjugate sum.
  rw [enlargedPerturbationDualObjective, sub_eq_add_neg,
    helperForTheorem_6_30_22_sum_neg_scaledConjugates_eq_neg_sum
      (f := f) (hf := hf) (wStar := wStar) (hnonneg := hnonneg)]

/-- Helper for Theorem 6.30.22: for fixed `x`, the inner infimum over enlarged perturbation
parameters collapses to the linear translation term plus the explicit dual objective. -/
lemma helperForTheorem_6_30_22_fixedX_parameterInf_eq_linearPlusDualObjective
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    (x xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    (⨅ w : EnlargedPerturbationParameter m n,
        enlargedPerturbationProgramBifunction f0 f w x -
          (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal))) =
      (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
        enlargedPerturbationDualObjective f0 f wStar := by
  let x0Block : (Fin n → ℝ) → EReal := fun x0 =>
    f0 (x - x0) + (((x0 ⬝ᵥ wStar.x0Star : ℝ) : EReal))
  let uShiftBlock : (Fin m → ℝ) → (Fin m → Fin n → ℝ) → EReal := fun u xShift =>
    indicatorFunction (enlargedPerturbationProgramFeasibleSet f
        ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
          EnlargedPerturbationParameter m n)) x +
      (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
      ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))
  let uShiftBlockProd :
      ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) → EReal := fun q =>
    uShiftBlock q.1 q.2
  have hx0_dom_nonempty :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0) := by
    -- Properness of `f₀` supplies one finite point for the `x₀`-block.
    exact (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f0)).mp hf0.2.1
  have hfinite_x0 :
      ∃ x0 : Fin n → ℝ, x0Block x0 < (⊤ : EReal) := by
    rcases hx0_dom_nonempty with ⟨z, hz_dom⟩
    refine ⟨x - z, ?_⟩
    have hz_top : f0 z < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hz_dom
    have hsum_lt_top :
        f0 z + ((((x - z) ⬝ᵥ wStar.x0Star : ℝ) : EReal)) < (⊤ : EReal) := by
      exact EReal.add_lt_top (ne_of_lt hz_top) (EReal.coe_ne_top _)
    -- Choosing `x₀ = x - z` makes the translated argument equal to the finite witness `z`.
    simpa [x0Block, sub_eq_add_neg] using hsum_lt_top
  have hfinite_uShift :
      ∃ q : (Fin m → ℝ) × (Fin m → Fin n → ℝ), uShiftBlockProd q < (⊤ : EReal) := by
    let u0 : Fin m → ℝ := fun i => (f i x).toReal
    let xShift0 : Fin m → Fin n → ℝ := fun _ => 0
    have hx_feas :
        x ∈ enlargedPerturbationProgramFeasibleSet f
          ({ u := u0, x0 := (0 : Fin n → ℝ), xShift := xShift0 } :
            EnlargedPerturbationParameter m n) := by
      -- The threshold `u0 i = (fᵢ x).toReal` makes every constraint active at `x`.
      intro i
      have hx_dom :
          x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
        rw [hdom i]
        simp
      have hx_top : f i x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hx_dom
      have hle :
          f i x ≤ (((u0 i : ℝ) : EReal)) := by
        simpa [u0] using EReal.le_coe_toReal (x := f i x) ((lt_top_iff_ne_top).1 hx_top)
      simpa [u0, xShift0] using hle
    refine ⟨(u0, xShift0), ?_⟩
    have hvalue :
        uShiftBlockProd (u0, xShift0) = (((u0 ⬝ᵥ wStar.uStar : ℝ) : EReal)) := by
      -- At the witness, the indicator vanishes and the translated-coordinate sum is zero.
      simp [uShiftBlockProd, uShiftBlock, u0, xShift0, indicatorFunction, hx_feas]
    rw [hvalue]
    exact (lt_top_iff_ne_top).2 (EReal.coe_ne_top _)
  have htop :
      ∀ i : Fin m, ∀ y : Fin n → ℝ, f i y < (⊤ : EReal) := by
    -- The full-domain hypothesis turns every point into a finite evaluation point.
    intro i y
    have hy_mem :
        y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
      rw [hdom i]
      simp
    simpa [effectiveDomain_eq] using hy_mem
  have hsplit_integrand :
      (⨅ w : EnlargedPerturbationParameter m n,
          enlargedPerturbationProgramBifunction f0 f w x -
            (((x ⬝ᵥ xStar : ℝ) : EReal)) +
            (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal))) =
        (⨅ u : Fin m → ℝ,
          ⨅ x0 : Fin n → ℝ,
            ⨅ xShift : Fin m → Fin n → ℝ,
              x0Block x0 + uShiftBlock u xShift +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
    -- Expand the inner integrand so the `x₀`-block and `(u, xShift)`-block become explicit.
    rw [helperForTheorem_6_30_22_iInf_parameter_eq_nestedBlocks
      (H := fun w : EnlargedPerturbationParameter m n =>
        enlargedPerturbationProgramBifunction f0 f w x -
          (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal)))]
    refine iInf_congr ?_
    intro u
    refine iInf_congr ?_
    intro x0
    refine iInf_congr ?_
    intro xShift
    -- This is exactly the pointwise block decomposition established earlier.
    simpa [x0Block, uShiftBlock, add_assoc, add_left_comm, add_comm] using
      helperForTheorem_6_30_22_fixedX_integrand_split
        (f0 := f0) (f := f) (x := x) (xStar := xStar) (wStar := wStar)
        (x0 := x0) (u := u) (xShift := xShift)
  have hswap_x0 :
      (⨅ u : Fin m → ℝ,
          ⨅ x0 : Fin n → ℝ,
            ⨅ xShift : Fin m → Fin n → ℝ,
              x0Block x0 + uShiftBlock u xShift +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
        (⨅ x0 : Fin n → ℝ,
          ⨅ u : Fin m → ℝ,
            ⨅ xShift : Fin m → Fin n → ℝ,
              x0Block x0 + uShiftBlock u xShift +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
    -- Commute the `u` and `x₀` infima by reindexing their product.
    rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested
      (H := fun u : Fin m → ℝ => fun x0 : Fin n → ℝ =>
        ⨅ xShift : Fin m → Fin n → ℝ,
          x0Block x0 + uShiftBlock u xShift +
            (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
    have hCommute :
        (⨅ p : (Fin m → ℝ) × (Fin n → ℝ),
            ⨅ xShift : Fin m → Fin n → ℝ,
              x0Block p.2 + uShiftBlock p.1 xShift +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
          (⨅ p : (Fin n → ℝ) × (Fin m → ℝ),
            ⨅ xShift : Fin m → Fin n → ℝ,
              x0Block p.1 + uShiftBlock p.2 xShift +
                (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
      refine (Equiv.iInf_congr (Equiv.prodComm (Fin m → ℝ) (Fin n → ℝ)) ?_)
      intro p
      rfl
    rw [hCommute]
    rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
      (H := fun x0 : Fin n → ℝ => fun u : Fin m → ℝ =>
        ⨅ xShift : Fin m → Fin n → ℝ,
          x0Block x0 + uShiftBlock u xShift +
            (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
  have hpack_uShift :
      (⨅ u : Fin m → ℝ,
          ⨅ xShift : Fin m → Fin n → ℝ,
            uShiftBlock u xShift) =
        ∑ i : Fin m,
          ((((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) -
            fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i)) := by
    -- Collapse the `(u, xShift)` block first to the translated family, then blockwise.
    calc
      (⨅ u : Fin m → ℝ,
          ⨅ xShift : Fin m → Fin n → ℝ,
            uShiftBlock u xShift) =
          (⨅ q : (Fin m → ℝ) × (Fin m → Fin n → ℝ), uShiftBlockProd q) := by
              symm
              exact helperForTheorem_6_30_22_iInf_prod_eq_nested
                (H := uShiftBlock)
      _ =
          (⨅ u : Fin m → ℝ,
            ⨅ xShift : Fin m → Fin n → ℝ,
              uShiftBlock u xShift) := by
              exact helperForTheorem_6_30_22_iInf_prod_eq_nested
                (H := uShiftBlock)
      _ =
          (⨅ u : Fin m → ℝ,
            ⨅ xShift : Fin m → Fin n → ℝ,
              indicatorFunction (enlargedPerturbationProgramFeasibleSet f
                  ({ u := u, x0 := (0 : Fin n → ℝ), xShift := xShift } :
                    EnlargedPerturbationParameter m n)) x +
                (((u ⬝ᵥ wStar.uStar : ℝ) : EReal)) +
                ∑ i : Fin m, (((xShift i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) := by
              simp [uShiftBlock]
      _ =
          (⨅ y : Fin m → Fin n → ℝ,
            ∑ i : Fin m,
              ((((wStar.uStar i : ℝ) : EReal) * f i (x - y i)) +
                (((y i ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)))) := by
              exact helperForTheorem_6_30_22_uBlock_iInf_eq_translatedConstraintFamily
                (f := f) (hf := hf) (hdom := hdom) (x := x) (wStar := wStar)
                (hnonneg := hnonneg)
      _ =
          ∑ i : Fin m,
            ((((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) -
              fenchelConjugate n
                (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
                (wStar.xShiftStar i)) := by
              exact helperForTheorem_6_30_22_familyTranslatedAffine_iInf_eq_sum_linear_minus_fenchel
                (f := f) (x := x) (p := wStar.xShiftStar)
                (lam := wStar.uStar) (hlam := hnonneg) (htop := htop)
  have hsum_split :
      (∑ i : Fin m,
          ((((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) -
            fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i))) =
        (∑ i : Fin m, (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal))) +
          ∑ i : Fin m,
            -fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i) := by
    -- Separate the translated linear terms from the conjugate constants.
    simp [sub_eq_add_neg, Finset.sum_add_distrib]
  -- Collapse the `x₀`-block and the `(u, xShift)`-block independently, then collect the linear
  -- and constant contributions into the final displayed formula.
  calc
    (⨅ w : EnlargedPerturbationParameter m n,
        enlargedPerturbationProgramBifunction f0 f w x -
          (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal))) =
      (⨅ x0 : Fin n → ℝ,
        ⨅ u : Fin m → ℝ,
          ⨅ xShift : Fin m → Fin n → ℝ,
            x0Block x0 + uShiftBlock u xShift +
              (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
            rw [hsplit_integrand, hswap_x0]
    _ =
      ((⨅ x0 : Fin n → ℝ, x0Block x0) +
          (⨅ u : Fin m → ℝ, ⨅ xShift : Fin m → Fin n → ℝ, uShiftBlock u xShift)) +
        ((-(x ⬝ᵥ xStar) : ℝ) : EReal) := by
            calc
              (⨅ x0 : Fin n → ℝ,
                  ⨅ u : Fin m → ℝ,
                    ⨅ xShift : Fin m → Fin n → ℝ,
                      x0Block x0 + uShiftBlock u xShift +
                        (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) =
                (⨅ x0 : Fin n → ℝ,
                  ⨅ q : (Fin m → ℝ) × (Fin m → Fin n → ℝ),
                    x0Block x0 + uShiftBlockProd q +
                      (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) := by
                        refine iInf_congr ?_
                        intro x0
                        symm
                        exact helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := fun u : Fin m → ℝ => fun xShift : Fin m → Fin n → ℝ =>
                            x0Block x0 + uShiftBlock u xShift +
                              (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))
              _ =
                ((⨅ x0 : Fin n → ℝ, x0Block x0) +
                    (⨅ q : (Fin m → ℝ) × (Fin m → Fin n → ℝ), uShiftBlockProd q)) +
                  ((-(x ⬝ᵥ xStar) : ℝ) : EReal) := by
                        rw [← helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := fun x0 : Fin n → ℝ =>
                            fun q : (Fin m → ℝ) × (Fin m → Fin n → ℝ) =>
                              x0Block x0 + uShiftBlockProd q +
                                (((-(x ⬝ᵥ xStar) : ℝ) : EReal)))]
                        rw [helperForTheorem_6_30_22_twoFactor_iInf_add_realConst
                          (F := x0Block) (G := uShiftBlockProd)
                          (c := -(x ⬝ᵥ xStar : ℝ))
                          hfinite_x0 hfinite_uShift]
              _ =
                ((⨅ x0 : Fin n → ℝ, x0Block x0) +
                    (⨅ u : Fin m → ℝ, ⨅ xShift : Fin m → Fin n → ℝ, uShiftBlock u xShift)) +
                  ((-(x ⬝ᵥ xStar) : ℝ) : EReal) := by
                        rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
                          (H := uShiftBlock)]
    _ =
      ((((x ⬝ᵥ wStar.x0Star : ℝ) : EReal)) - fenchelConjugate n f0 wStar.x0Star) +
        (∑ i : Fin m,
          ((((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) -
            fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i))) +
        (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) := by
            rw [helperForTheorem_6_30_22_translatedAffineBlock_iInf_eq_linear_minus_fenchel
              (g := f0) (x := x) (p := wStar.x0Star)]
            rw [hpack_uShift]
    _ =
      ((((x ⬝ᵥ wStar.x0Star : ℝ) : EReal)) +
          ∑ i : Fin m, (((x ⬝ᵥ wStar.xShiftStar i : ℝ) : EReal)) +
          (((-(x ⬝ᵥ xStar) : ℝ) : EReal))) +
        (-fenchelConjugate n f0 wStar.x0Star +
          ∑ i : Fin m,
            -fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i)) := by
            rw [hsum_split]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ =
      (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
        (-fenchelConjugate n f0 wStar.x0Star +
          ∑ i : Fin m,
            -fenchelConjugate n
              (fun z => (((wStar.uStar i : ℝ) : EReal) * f i z))
              (wStar.xShiftStar i)) := by
            rw [helperForTheorem_6_30_22_translationLinearTerms_collect
              (x := x) (xStar := xStar) (wStar := wStar)]
    _ =
      (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
        enlargedPerturbationDualObjective f0 f wStar := by
            rw [← helperForTheorem_6_30_22_dualObjective_eq_headPlusSumNegScaledConjugates
              (f0 := f0) (f := f) (hf := hf) (wStar := wStar)
              (hnonneg := hnonneg)]

/-- Helper for Theorem 6.30.22: on the branch `u* ≥ 0`, the enlarged adjoint rewrites to a free
linear term in `x` plus the explicit dual objective. -/
lemma helperForTheorem_6_30_22_adjoint_rewrite_of_nonnegativeMultipliers
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    (xStar : Fin n → ℝ) (wStar : EnlargedPerturbationDualParameter m n)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i) :
    adjointOfEnlargedPerturbationProgram f0 f xStar wStar =
      sInf (Set.range fun x : Fin n → ℝ =>
        (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
          enlargedPerturbationDualObjective f0 f wStar) := by
  -- Rewrite the adjoint as an outer infimum over `x`, and collapse the inner parameter infimum
  -- pointwise by the fixed-`x` assembly lemma proved just above.
  rw [adjointOfEnlargedPerturbationProgram, sInf_range]
  have hCommute :
      (⨅ p : EnlargedPerturbationParameter m n × (Fin n → ℝ),
          enlargedPerturbationProgramBifunction f0 f p.1 p.2 -
            (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((enlargedPerturbationDualPairing p.1 wStar : ℝ) : EReal))) =
        (⨅ p : (Fin n → ℝ) × EnlargedPerturbationParameter m n,
          enlargedPerturbationProgramBifunction f0 f p.2 p.1 -
            (((p.1 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((enlargedPerturbationDualPairing p.2 wStar : ℝ) : EReal))) := by
    refine (Equiv.iInf_congr
      (Equiv.prodComm (EnlargedPerturbationParameter m n) (Fin n → ℝ)) ?_)
    intro p
    rfl
  calc
    (⨅ p : EnlargedPerturbationParameter m n × (Fin n → ℝ),
        enlargedPerturbationProgramBifunction f0 f p.1 p.2 -
          (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing p.1 wStar : ℝ) : EReal))) =
      (⨅ p : (Fin n → ℝ) × EnlargedPerturbationParameter m n,
        enlargedPerturbationProgramBifunction f0 f p.2 p.1 -
          (((p.1 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((enlargedPerturbationDualPairing p.2 wStar : ℝ) : EReal))) := hCommute
    _ =
      (⨅ x : Fin n → ℝ,
        ⨅ w : EnlargedPerturbationParameter m n,
          enlargedPerturbationProgramBifunction f0 f w x -
            (((x ⬝ᵥ xStar : ℝ) : EReal)) +
            (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal))) := by
              rw [helperForTheorem_6_30_22_iInf_prod_eq_nested
                (H := fun x : Fin n → ℝ => fun w : EnlargedPerturbationParameter m n =>
                  enlargedPerturbationProgramBifunction f0 f w x -
                    (((x ⬝ᵥ xStar : ℝ) : EReal)) +
                    (((enlargedPerturbationDualPairing w wStar : ℝ) : EReal)))]
    _ =
      (⨅ x : Fin n → ℝ,
        (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
          enlargedPerturbationDualObjective f0 f wStar) := by
              refine iInf_congr ?_
              intro x
              exact helperForTheorem_6_30_22_fixedX_parameterInf_eq_linearPlusDualObjective
                (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom)
                (x := x) (xStar := xStar) (wStar := wStar) (hnonneg := hnonneg)
    _ =
      sInf (Set.range fun x : Fin n → ℝ =>
        (((x ⬝ᵥ (enlargedPerturbationDualTranslationSum wStar - xStar) : ℝ) : EReal)) +
          enlargedPerturbationDualObjective f0 f wStar) := by
              rw [sInf_range]

/-- Helper for Theorem 6.30.22: on the dual-feasible branch `u* ≥ 0` and
`x₀* + ⋯ + x_m* = x*`, the enlarged adjoint equals the explicit dual objective. -/
lemma helperForTheorem_6_30_22_adjoint_eq_dualObjective_of_dualFeasible
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    {xStar : Fin n → ℝ} {wStar : EnlargedPerturbationDualParameter m n}
    (hfeas : enlargedPerturbationDualFeasible xStar wStar) :
    adjointOfEnlargedPerturbationProgram f0 f xStar wStar =
      enlargedPerturbationDualObjective f0 f wStar := by
  -- First rewrite the adjoint into the free linear term plus the explicit dual objective.
  rw [helperForTheorem_6_30_22_adjoint_rewrite_of_nonnegativeMultipliers
    (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom)
    (xStar := xStar) (wStar := wStar) (hnonneg := hfeas.1)]
  -- On the feasible branch the linear coefficient vanishes, so the ranged family is constant.
  simp [hfeas.2]

/-- Helper for Theorem 6.30.22: if the dual parameter is not feasible, then the enlarged adjoint
value is `-∞`. The negative-multiplier subcase is already handled here; the remaining blocker is
the nonnegative translation-mismatch branch. -/
lemma helperForTheorem_6_30_22_adjoint_eq_bot_of_not_dualFeasible
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ)
    {xStar : Fin n → ℝ} {wStar : EnlargedPerturbationDualParameter m n}
    (hnotfeas : ¬ enlargedPerturbationDualFeasible xStar wStar) :
    adjointOfEnlargedPerturbationProgram f0 f xStar wStar = (⊥ : EReal) := by
  by_cases hnonneg : ∀ i : Fin m, 0 ≤ wStar.uStar i
  · have htranslation_ne : enlargedPerturbationDualTranslationSum wStar ≠ xStar := by
      -- On the nonnegative branch, infeasibility can only come from the failed balance equation.
      intro hEq
      exact hnotfeas ⟨hnonneg, hEq⟩
    have hMismatch : enlargedPerturbationDualTranslationSum wStar - xStar ≠ 0 := by
      -- A zero difference would force the missing balance equality.
      intro hzero
      apply htranslation_ne
      exact sub_eq_zero.mp hzero
    -- Rewrite the adjoint by the nonnegative-branch formula and use the nonzero linear term to
    -- drive the infimum to `⊥`.
    rw [helperForTheorem_6_30_22_adjoint_rewrite_of_nonnegativeMultipliers
      (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom)
      (xStar := xStar) (wStar := wStar) (hnonneg := hnonneg)]
    exact helperForTheorem_6_30_22_sInf_linear_plus_nonTopConst_eq_bot_of_ne_zero
      (b := enlargedPerturbationDualTranslationSum wStar - xStar)
      (c := enlargedPerturbationDualObjective f0 f wStar)
      hMismatch
      (helperForTheorem_6_30_22_dualObjective_ne_top_of_nonnegative
        (f0 := f0) (f := f) (hf0 := hf0) (hf := hf)
        (wStar := wStar) (hnonneg := hnonneg))
  · -- Route correction: isolate the negative-multiplier case as a finished ray argument and send
    -- only the genuinely nonnegative branch through the translation-mismatch rewrite.
    push_neg at hnonneg
    exact helperForTheorem_6_30_22_adjoint_eq_bot_of_exists_negativeMultiplier
      (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom)
      (xStar := xStar) (wStar := wStar) hnonneg

/-- Helper for Theorem 6.30.22: branchwise formula for the enlarged adjoint together with the
dual-value description at `x* = 0`. -/
theorem helperForTheorem_6_30_22_adjoint_branch_formulas_and_dualProgramValue
    {m n : ℕ}
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom : ∀ i : Fin m, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) = Set.univ) :
    (∀ xStar : Fin n → ℝ, ∀ wStar : EnlargedPerturbationDualParameter m n,
        (enlargedPerturbationDualFeasible xStar wStar →
          adjointOfEnlargedPerturbationProgram f0 f xStar wStar =
            enlargedPerturbationDualObjective f0 f wStar) ∧
        (¬ enlargedPerturbationDualFeasible xStar wStar →
          adjointOfEnlargedPerturbationProgram f0 f xStar wStar = (⊥ : EReal))) ∧
      dualProgramValueOfEnlargedPerturbationProgram f0 f =
        sSup {v : EReal | ∃ wStar : EnlargedPerturbationDualParameter m n,
          enlargedPerturbationDualFeasible (0 : Fin n → ℝ) wStar ∧
            v = enlargedPerturbationDualObjective f0 f wStar} := by
  constructor
  · intro xStar wStar
    constructor
    · -- The feasible branch is exactly the explicit adjoint formula.
      intro hfeas
      exact
        helperForTheorem_6_30_22_adjoint_eq_dualObjective_of_dualFeasible
          (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom) hfeas
    · -- The infeasible branch is handled by the `-∞` lemma.
      intro hnotfeas
      exact
        helperForTheorem_6_30_22_adjoint_eq_bot_of_not_dualFeasible
          (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom) hnotfeas
  · -- Compare the `sSup` over all dual parameters with the `sSup` over the feasible branch.
    rw [dualProgramValueOfEnlargedPerturbationProgram]
    refine le_antisymm ?_ ?_
    · rw [sSup_le_iff]
      intro v hv
      rcases hv with ⟨wStar, rfl⟩
      by_cases hfeas : enlargedPerturbationDualFeasible (0 : Fin n → ℝ) wStar
      · -- A feasible dual parameter contributes exactly its explicit dual objective value.
        have hEq :
            adjointOfEnlargedPerturbationProgram f0 f (0 : Fin n → ℝ) wStar =
              enlargedPerturbationDualObjective f0 f wStar :=
          helperForTheorem_6_30_22_adjoint_eq_dualObjective_of_dualFeasible
            (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom) hfeas
        calc
          adjointOfEnlargedPerturbationProgram f0 f (0 : Fin n → ℝ) wStar
              = enlargedPerturbationDualObjective f0 f wStar := hEq
          _ ≤ sSup {v : EReal | ∃ wStar : EnlargedPerturbationDualParameter m n,
                enlargedPerturbationDualFeasible (0 : Fin n → ℝ) wStar ∧
                  v = enlargedPerturbationDualObjective f0 f wStar} := by
              refine le_sSup ?_
              exact ⟨wStar, hfeas, rfl⟩
      · -- An infeasible dual parameter contributes only `⊥`, which is below every supremum.
        change adjointOfEnlargedPerturbationProgram f0 f (0 : Fin n → ℝ) wStar ≤
          sSup {v : EReal | ∃ wStar : EnlargedPerturbationDualParameter m n,
            enlargedPerturbationDualFeasible (0 : Fin n → ℝ) wStar ∧
              v = enlargedPerturbationDualObjective f0 f wStar}
        rw [helperForTheorem_6_30_22_adjoint_eq_bot_of_not_dualFeasible
          (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom) hfeas]
        exact bot_le
    · rw [sSup_le_iff]
      intro v hv
      rcases hv with ⟨wStar, hfeas, rfl⟩
      -- Every feasible objective value is realized by the corresponding adjoint value.
      have hEq :
          adjointOfEnlargedPerturbationProgram f0 f (0 : Fin n → ℝ) wStar =
            enlargedPerturbationDualObjective f0 f wStar :=
        helperForTheorem_6_30_22_adjoint_eq_dualObjective_of_dualFeasible
          (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (hdom := hdom) hfeas
      calc
        enlargedPerturbationDualObjective f0 f wStar
            = adjointOfEnlargedPerturbationProgram f0 f (0 : Fin n → ℝ) wStar := hEq.symm
        _ ≤ sSup (Set.range fun wStar : EnlargedPerturbationDualParameter m n =>
              adjointOfEnlargedPerturbationProgram f0 f 0 wStar) := by
            refine le_sSup ?_
            exact ⟨wStar, rfl⟩


end Section30
end Chap06
