/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part8

section Chap04
section Section21

/-- Helper for Theorem 21.4: nonpositivity on `dom g*` forces monotonicity of `g` along the
corresponding primal direction. This is the `Theorem 13.3` recession-direction step packaged in
the exact form needed for the two-block separator argument. -/
lemma helperForTheorem_21_4_ray_antitone_of_nonpositive_effectiveDomain_fenchelConjugate
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hgClosed : IsClosed {p : (Fin n → ℝ) × ℝ | g p.1 ≤ (p.2 : EReal)})
    (d : Fin n → ℝ)
    (hNonpos :
      ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g),
        dotProduct xStar d ≤ 0) :
    ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → g (x + t • d) ≤ g x := by
  have hSuppLeZero :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) d ≤
        ((0 : ℝ) : EReal) := by
    exact
      (section13_supportFunctionEReal_le_coe_iff
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g))
        (y := d) (μ := 0)).2 hNonpos
  have hClosedConv : ClosedConvexFunction g := by
    refine ⟨?_, helperForTheorem_21_3_lowerSemicontinuous_of_closedEpigraph (f := g) (hfClosed := hgClosed)⟩
    simpa [ConvexFunction] using hgProper.1
  have hRecFun :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) =
        recessionFunction g := by
    exact
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := g) hClosedConv hgProper
  have hRecCone : d ∈ recessionConeEReal (F := (Fin n → ℝ)) g := by
    have hrec_le : recessionFunction g d ≤ (0 : EReal) := by
      simpa [hRecFun] using hSuppLeZero
    have hrecE_le : recessionFunctionEReal (F := (Fin n → ℝ)) g d ≤ (0 : EReal) := by
      simpa [recessionFunctionEReal, recessionFunction, erealDom, effectiveDomain_eq] using hrec_le
    simpa [recessionConeEReal] using hrecE_le
  rcases
      helperForTheorem_21_3_recessionConeEReal_eq_recessionCone_some_nonempty_sublevel
        (f := g) (hfProper := hgProper) (hfClosed := hgClosed) with
    ⟨α, hα_nonempty, hRecEq⟩
  have hdRec : d ∈ Set.recessionCone {x : Fin n → ℝ | g x ≤ (α : EReal)} := by
    simpa [hRecEq] using hRecCone
  exact
    helperForTheorem_21_3_sublevel_ray_antitone
      (f := g) (hfProper := hgProper) (hfClosed := hgClosed)
      (α := α) hα_nonempty hdRec

/-- Helper for Theorem 21.4: when the affine-feasible block is empty, a Helly-small affine
subfamily already admits a nonnegative weighted sum with a uniform positive lower bound. -/
lemma helperForTheorem_21_4_affineBlock_realSeparation_on_subtype
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hAempty :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)) = ∅) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → {i : I // i ∈ I0}, ∃ w : Fin m → ℝ,
        (∀ j : Fin m, 0 ≤ w j) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, ε ≤ ∑ j : Fin m, w j * (Classical.choose (hAffine (idx j).1 (idx j).2) x) := by
  -- Route correction: the empty branch is now split into Helly extraction first, followed by
  -- the finite affine separation step that is still missing.
  rcases
      helperForTheorem_21_4_emptyAffineFeasibleSet_has_small_infeasible_affineBlock
        f I0 hAffine hAempty with
    ⟨m, hm, idx, hidx, hSmallGap⟩
  let _ := hidx
  -- The remaining work is now a pure finite affine-separation core on the extracted block.
  rcases helperForTheorem_21_4_positive_margin_of_small_infeasible_affineBlock
      (f := f) I0 idx hAffine hSmallGap with ⟨w, hwNonneg, ε, hε, hmargin⟩
  exact ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩

/-- Helper for Theorem 21.4: if the affine-feasible block is empty, the finite affine block
alone already yields a sparse global margin witness indexed by `{i // i ∈ I₀}`. -/
lemma helperForTheorem_21_4_affineBlock_gap_of_empty_affineFeasibleSet_to_affineBlockSubtype_sparseFiniteDual_margin
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hAempty :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)) = ∅) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → {i : I // i ∈ I0}, ∃ w : Fin m → ℝ,
        (∀ j : Fin m, 0 ≤ w j) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
  -- Route correction: once the affine-feasible set is empty, the only remaining work is the
  -- affine-only finite separation on a Helly-small subtype-indexed block.
  rcases helperForTheorem_21_4_affineBlock_realSeparation_on_subtype f I0 hAffine hAempty with
    ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩
  refine ⟨m, hm, idx, w, hwNonneg, ε, hε, ?_⟩
  intro x
  have hReal :
      ε ≤ ∑ j : Fin m, w j * Classical.choose (hAffine (idx j).1 (idx j).2) x := hmargin x
  have hEReal :
      ((ε : ℝ) : EReal) ≤
        (((∑ j : Fin m, w j * Classical.choose (hAffine (idx j).1 (idx j).2) x : ℝ) : ℝ) : EReal) := by
    exact_mod_cast hReal
  calc
    ((ε : ℝ) : EReal)
        ≤ (((∑ j : Fin m, w j * Classical.choose (hAffine (idx j).1 (idx j).2) x : ℝ) : ℝ) : EReal) :=
          hEReal
    _ = ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
          calc
            (((∑ j : Fin m, w j * Classical.choose (hAffine (idx j).1 (idx j).2) x : ℝ) : ℝ) : EReal)
                = ∑ j : Fin m, (((w j * Classical.choose (hAffine (idx j).1 (idx j).2) x : ℝ) : EReal)) := by
                    exact helperForTheorem_21_1_coe_finset_sum_real
                      (s := (Finset.univ : Finset (Fin m)))
                      (g := fun j : Fin m => w j * Classical.choose (hAffine (idx j).1 (idx j).2) x)
            _ = ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [Classical.choose_spec (hAffine (idx j).1 (idx j).2) x]
                  simp [EReal.coe_mul]

/-- Tail helper reused from the original-route endgame: once the positively homogeneous hull
hits `⊥` at the origin, the convex-hull family already has strictly negative value at `0`. -/
lemma helperForTheorem_21_4_convexHullConjugate_origin_neg_of_posHomHull_zero_bot
    {n : ℕ}
    (h : (Fin n → ℝ) → EReal)
    (hhConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hhFinite : ∃ x : Fin n → ℝ, h x ≠ (⊤ : EReal))
    (hk0_bot :
      positivelyHomogeneousConvexFunctionGenerated h (0 : Fin n → ℝ) = (⊥ : EReal)) :
    h (0 : Fin n → ℝ) < (0 : EReal) := by
  let k : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated h
  by_contra hh0_nonneg
  have hh0_nonneg' : (0 : EReal) ≤ h 0 := le_of_not_gt hh0_nonneg
  have hk0_repr :
      k 0 =
        sInf
          {z : EReal |
            ∃ lam : ℝ, 0 ≤ lam ∧ z = rightScalarMultiple h lam (0 : Fin n → ℝ)} := by
    simpa [k] using
      (infimumRepresentation_posHomogeneousHull (n := n) (h := h) hhConvOn hhFinite).1
        (0 : Fin n → ℝ)
  rcases hhFinite with ⟨x0, hx0_ne_top⟩
  have hx0_dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    have hx0_lt : h x0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx0_ne_top
    simpa [effectiveDomain_eq] using
      (show x0 ∈ {x : Fin n → ℝ | x ∈ Set.univ ∧ h x < (⊤ : EReal)} from
        ⟨by simp, hx0_lt⟩)
  have hne_epi_h :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → ℝ)) h) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ))) (f := h)).2 ⟨x0, hx0_dom⟩
  have hsInf_nonneg :
      (0 : EReal) ≤
        sInf
          {z : EReal |
            ∃ lam : ℝ, 0 ≤ lam ∧ z = rightScalarMultiple h lam (0 : Fin n → ℝ)} := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨lam, hlam, rfl⟩
    by_cases hlam0 : lam = 0
    · simp [hlam0, rightScalarMultiple_zero_eval (f := h) hne_epi_h (0 : Fin n → ℝ)]
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
      have hmul_nonneg :
          (0 : EReal) ≤ ((lam : ℝ) : EReal) * h 0 := by
        exact mul_nonneg (by exact_mod_cast le_of_lt hlam_pos) hh0_nonneg'
      simpa [rightScalarMultiple_pos (f := h) (lam := lam) hhConvOn hlam_pos] using hmul_nonneg
  have hk0_nonneg : (0 : EReal) ≤ k 0 := by
    simpa [hk0_repr] using hsInf_nonneg
  have : (0 : EReal) ≤ (⊥ : EReal) := by
    simpa [k, hk0_bot] using hk0_nonneg
  exact (not_le_of_gt (EReal.bot_lt_coe 0)) this

/-- A local weakening of Theorem 13.5 tailored to the `21.4` proof: convexity plus a single
finite point already identify the closure of the positively homogeneous hull with the support
function of the `0`-sublevel set of the conjugate. -/
lemma helperForTheorem_21_4_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
    {n : ℕ}
    (h : (Fin n → ℝ) → EReal)
    (hhConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hhFinite : ∃ x : Fin n → ℝ, h x ≠ (⊤ : EReal)) :
    clConv n (positivelyHomogeneousConvexFunctionGenerated h) =
      supportFunctionEReal {xStar : Fin n → ℝ | fenchelConjugate n h xStar ≤ (0 : EReal)} := by
  classical
  let k : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated h
  have hkmax :
      (∃ C : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (C : Set ((Fin n → ℝ) × ℝ)) =
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k ∧
        (0 : (Fin n → ℝ) × ℝ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k ∧
        PositivelyHomogeneous k ∧
        k 0 ≤ 0 ∧
        k ≤ h) ∧
      (∀ u : (Fin n → ℝ) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) u →
        u 0 ≤ 0 →
        u ≤ h →
        u ≤ k) := by
    simpa [k] using (maximality_posHomogeneousHull (n := n) (h := h) hhConvOn)
  have hk_pos : PositivelyHomogeneous k := hkmax.2.1.2.1
  have hk_conv : ConvexFunction k := by
    simpa [ConvexFunction] using hkmax.2.1.1
  have hk_le : k ≤ h := hkmax.2.1.2.2.2
  have hnotTop : ¬ ∀ x : Fin n → ℝ, k x = (⊤ : EReal) := by
    rcases hhFinite with ⟨x0, hx0_ne_top⟩
    intro hall
    have : (⊤ : EReal) ≤ h x0 := by
      simpa [hall x0] using (hk_le x0)
    exact hx0_ne_top (top_le_iff.mp this)
  obtain ⟨C, _hCclosed, _hCconv, hcl, hCeq⟩ :=
    clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
      (n := n) k hk_pos hk_conv hnotTop
  have hCeq' :
      C = {xStar : Fin n → ℝ | fenchelConjugate n h xStar ≤ (0 : EReal)} := by
    calc
      C =
          {xStar : Fin n → ℝ |
            ∀ x : Fin n → ℝ, ((dotProduct x xStar : ℝ) : EReal) ≤ k x} := hCeq
      _ =
          {xStar : Fin n → ℝ |
            ∀ x : Fin n → ℝ, ((dotProduct x xStar : ℝ) : EReal) ≤ h x} := by
          simpa [k] using
            (section13_setOf_forall_dotProduct_le_posHomGenerated_eq
              (n := n) (f := h) hhConvOn)
      _ = {xStar : Fin n → ℝ | fenchelConjugate n h xStar ≤ (0 : EReal)} := by
          simpa using
            (section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero
              (n := n) h)
  simpa [hCeq', k] using hcl

/-- The `21.3` tail localized: if the `0`-sublevel of `h*` is empty and the origin lies in
`ri (dom k)` for the positively homogeneous hull `k` of `h`, then `k(0) = -∞`. -/
lemma helperForTheorem_21_4_posHomHull_zero_bot_of_empty_conjugate_sublevel_and_zero_mem_ri
    {n : ℕ}
    (h : (Fin n → ℝ) → EReal)
    (hhConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hhFinite : ∃ x : Fin n → ℝ, h x ≠ (⊤ : EReal))
    (hsublevel_empty :
      {x : Fin n → ℝ | fenchelConjugate n h x ≤ (0 : EReal)} = (∅ : Set (Fin n → ℝ)))
    (h0ri :
      (0 : EuclideanSpace ℝ (Fin n)) ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (positivelyHomogeneousConvexFunctionGenerated h))) :
    positivelyHomogeneousConvexFunctionGenerated h (0 : Fin n → ℝ) = (⊥ : EReal) := by
  let k : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated h
  have hkmax :
      (∃ C : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (C : Set ((Fin n → ℝ) × ℝ)) =
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k ∧
        (0 : (Fin n → ℝ) × ℝ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k ∧
        PositivelyHomogeneous k ∧
        k 0 ≤ 0 ∧
        k ≤ h) ∧
      (∀ u : (Fin n → ℝ) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) u →
        u 0 ≤ 0 →
        u ≤ h →
        u ≤ k) := by
    simpa [k] using (maximality_posHomogeneousHull (n := n) (h := h) hhConvOn)
  have hkConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k := hkmax.2.1.1
  have hkPos : PositivelyHomogeneous k := hkmax.2.1.2.1
  have hk0le : k 0 ≤ 0 := hkmax.2.1.2.2.1
  have hkLe : k ≤ h := hkmax.2.1.2.2.2
  have hkConv : ConvexFunction k := by
    simpa [ConvexFunction] using hkConvOn
  have hk0_ne_top : k 0 ≠ (⊤ : EReal) := by
    intro hk0_top
    have : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [hk0_top] using hk0le
    exact (not_top_le_coe 0) this
  have hnotTop : ¬ ∀ x : Fin n → ℝ, k x = (⊤ : EReal) := by
    intro hall
    exact hk0_ne_top (hall 0)
  obtain ⟨Ck, _hCkclosed, _hCkconv, hcl, hCkEq⟩ :=
    clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
      (n := n) k hkPos hkConv hnotTop
  have hCkEq' :
      Ck = {xStar : Fin n → ℝ | fenchelConjugate n h xStar ≤ (0 : EReal)} := by
    calc
      Ck =
          {xStar : Fin n → ℝ |
            ∀ x : Fin n → ℝ, ((dotProduct x xStar : ℝ) : EReal) ≤ k x} := hCkEq
      _ =
          {xStar : Fin n → ℝ |
            ∀ x : Fin n → ℝ, ((dotProduct x xStar : ℝ) : EReal) ≤ h x} := by
          simpa [k] using
            (section13_setOf_forall_dotProduct_le_posHomGenerated_eq
              (n := n) (f := h) hhConvOn)
      _ = {xStar : Fin n → ℝ | fenchelConjugate n h xStar ≤ (0 : EReal)} := by
          simpa using
            (section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero
              (n := n) h)
  have hclBot : clConv n k = fun _ : Fin n → ℝ => (⊥ : EReal) := by
    funext x
    calc
      clConv n k x = supportFunctionEReal Ck x := by
        simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g x) hcl
      _ = supportFunctionEReal (∅ : Set (Fin n → ℝ)) x := by
        simp [hCkEq', hsublevel_empty]
      _ = (⊥ : EReal) := by
        simp [supportFunctionEReal]
  have hclEqClosure : clConv n k = convexFunctionClosure k := by
    calc
      clConv n k = fenchelConjugate n (fenchelConjugate n k) := by
        symm
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := k))
      _ = convexFunctionClosure k := by
        simpa using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := n) (f := k) hkConv)
  by_cases hproperK : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k
  · have hkagree :
        convexFunctionClosure k 0 = k 0 :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := k) hproperK).2 0 h0ri
    have hcl0 :
        convexFunctionClosure k 0 = (⊥ : EReal) := by
      have := congrArg (fun g : (Fin n → ℝ) → EReal => g 0) hclEqClosure
      simpa [hclBot] using this.symm
    exact hkagree.symm.trans hcl0
  · have himproperK :
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k := ⟨hkConvOn, hproperK⟩
    have hkagree :
        convexFunctionClosure k 0 = k 0 :=
      convexFunctionClosure_agrees_on_ri_of_improper (f := k) himproperK 0 h0ri
    have hcl0 :
        convexFunctionClosure k 0 = (⊥ : EReal) := by
      have := congrArg (fun g : (Fin n → ℝ) → EReal => g 0) hclEqClosure
      simpa [hclBot] using this.symm
    exact hkagree.symm.trans hcl0

/-- Helper for Theorem 21.4: reflection across the origin in the primal variable negates the
dual argument under Fenchel conjugation. -/
lemma helperForTheorem_21_4_fenchelConjugate_precomp_neg
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n (fun z : Fin n → ℝ => g (-z)) =
      fun xStar : Fin n → ℝ => fenchelConjugate n g (-xStar) := by
  classical
  funext xStar
  calc
    fenchelConjugate n (fun z : Fin n → ℝ => g (-z)) xStar
        =
          iSup
            (fun z : Fin n → ℝ =>
              (((z ⬝ᵥ xStar : ℝ) : EReal)) - g (-z)) := by
            simp [fenchelConjugate_eq_iSup]
    _ =
          iSup
            (fun z : Fin n → ℝ =>
              ((((-z) ⬝ᵥ xStar : ℝ) : EReal)) - g (-(-z))) := by
            symm
            exact
              iSup_comp_neg
                (g := fun z : Fin n → ℝ => (((z ⬝ᵥ xStar : ℝ) : EReal)) - g (-z))
    _ =
          iSup
            (fun z : Fin n → ℝ =>
              (((z ⬝ᵥ (-xStar) : ℝ) : EReal)) - g z) := by
            refine iSup_congr ?_
            intro z
            simp
    _ = fenchelConjugate n g (-xStar) := by
          simp [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 21.4: if the right block `k₁` is improper and there is a point in
`effectiveDomain g ∩ ri(effectiveDomain k₁)`, then any convex positively homogeneous minorant
of both `z ↦ g (-z)` and `k₁` must satisfy `k(0) = ⊥`. This packages the easy branch of the
textbook two-block argument so the main theorem can focus on the proper `k₁` case. -/
lemma helperForTheorem_21_4_zero_bot_of_improper_rightBlock
    {n : ℕ}
    (g k1 kAll : (Fin n → ℝ) → EReal)
    (hdomK1ne :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1).Nonempty)
    (hk1ConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1)
    (hkAllConvOn :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) kAll)
    (hkAll0le : kAll 0 ≤ 0)
    (hkAllLeK1 : kAll ≤ k1)
    (hgUpper : ∀ z : Fin n → ℝ, kAll (-z) ≤ g z)
    (hInterNonempty :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∩
        intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)).Nonempty)
    (hproperK1 :
      ¬ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1) :
    kAll 0 = (⊥ : EReal) := by
  have himproperK1 :
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) k1 := ⟨hk1ConvOn, hproperK1⟩
  rcases hInterNonempty with ⟨z0, hz0_dom_g, hz0ri⟩
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let Ck1E : Set (EuclideanSpace ℝ (Fin n)) :=
    ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)
  have hz0riE :
      e.symm z0 ∈ euclideanRelativeInterior n Ck1E := by
    letI :
        Nonempty ↥(affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1)) := by
      rcases hdomK1ne with ⟨x, hx⟩
      exact ⟨⟨x, subset_affineSpan (k := ℝ)
        (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) hx⟩⟩
    letI :
        Nonempty ↥(affineSpan ℝ Ck1E) := by
      rcases hdomK1ne with ⟨x, hx⟩
      have hxE : e.symm x ∈ Ck1E := by
        simpa [Ck1E, e] using hx
      refine ⟨⟨e.symm x, ?_⟩⟩
      exact subset_affineSpan (k := ℝ) (s := Ck1E) hxE
    have hriCk1 :
        intrinsicInterior ℝ Ck1E =
          e.symm '' intrinsicInterior ℝ
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
      have hCk1E :
          Ck1E = e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1 := by
        ext y
        constructor
        · intro hy
          refine ⟨(y : Fin n → ℝ), hy, ?_⟩
          simp [e]
        · rintro ⟨x, hx, rfl⟩
          simpa [Ck1E, e] using hx
      simpa [hCk1E] using
        (ContinuousLinearEquiv.image_intrinsicInterior
          (e := e.symm)
          (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1))
    have hz0ri_intrE :
        e.symm z0 ∈ intrinsicInterior ℝ Ck1E := by
      have hImg :
          e.symm z0 ∈
            e.symm '' intrinsicInterior ℝ
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) k1) := by
        exact ⟨z0, hz0ri, by simp [e]⟩
      simpa [hriCk1] using hImg
    simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n)
      (C := Ck1E), Ck1E] using hz0ri_intrE
  have hz0_g_ne_top : g z0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hz0_dom_g
  have hz0_k1_bot : k1 z0 = (⊥ : EReal) := by
    simpa using
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
        (f := k1) himproperK1 (e.symm z0) hz0riE
  have hkAll_z0_bot : kAll z0 = (⊥ : EReal) := by
    exact le_antisymm
      (le_trans (hkAllLeK1 z0) (by simpa [hz0_k1_bot]))
      bot_le
  have hkAll0_le_bot : kAll 0 ≤ (⊥ : EReal) := by
    let μz : ℝ := (g z0).toReal
    have hμz : kAll (-z0) ≤ (μz : EReal) := by
      have hle2 : g z0 ≤ (μz : EReal) := by
        exact EReal.le_coe_toReal (x := g z0) hz0_g_ne_top
      exact le_trans (hgUpper z0) hle2
    by_cases hkAll0_bot : kAll 0 = (⊥ : EReal)
    · simpa [hkAll0_bot]
    · have hkAll0_ne_bot : kAll 0 ≠ (⊥ : EReal) := hkAll0_bot
      have hkAll0_ne_top : kAll 0 ≠ (⊤ : EReal) := by
        intro hkAll0_top
        have : (⊤ : EReal) ≤ (0 : EReal) := by simpa [hkAll0_top] using hkAll0le
        exact not_top_le_coe 0 this
      let r : ℝ := (kAll 0).toReal
      have hkAll0_coe : ((r : ℝ) : EReal) = kAll 0 := by
        simpa [r] using (EReal.coe_toReal (x := kAll 0) hkAll0_ne_top hkAll0_ne_bot)
      obtain ⟨N, hNgt⟩ : ∃ N : ℕ, μz - 2 * r < (N : ℝ) := by
        exact exists_nat_gt (μz - 2 * r)
      have hN :
          kAll 0 ≤ (((μz - (N : ℝ)) / 2 : ℝ) : EReal) := by
        have hz0_le_negN : kAll z0 ≤ ((-(N : ℝ)) : EReal) := by
          simpa [hkAll_z0_bot] using (bot_le : (⊥ : EReal) ≤ ((-(N : ℝ)) : EReal))
        have hhalf :=
          epigraph_combo_ineq_aux
            (S := (Set.univ : Set (Fin n → ℝ))) (f := kAll)
            hkAllConvOn
            (x := -z0) (y := z0) (μ := μz) (v := -(N : ℝ)) (t := (1 / 2 : ℝ))
            (by simp) (by simp) hμz hz0_le_negN
            (by norm_num) (by norm_num)
        have hmid : ((1 - (1 / 2 : ℝ)) • (-z0) + (1 / 2 : ℝ) • z0) = 0 := by
          ext i
          simp [smul_eq_mul]
          ring
        have hrhs :
            ((((1 - (1 / 2 : ℝ)) * μz + (1 / 2 : ℝ) * (-(N : ℝ)) : ℝ)) : EReal) =
              ((((μz - (N : ℝ)) / 2 : ℝ)) : EReal) := by
          have hreal :
              ((1 - (1 / 2 : ℝ)) * μz + (1 / 2 : ℝ) * (-(N : ℝ)) : ℝ) =
                ((μz - (N : ℝ)) / 2 : ℝ) := by
            ring
          exact congrArg (fun t : ℝ => (t : EReal)) hreal
        have hhalf' :
            kAll 0 ≤
              ((((1 - (1 / 2 : ℝ)) * μz + (1 / 2 : ℝ) * (-(N : ℝ)) : ℝ)) : EReal) := by
          rw [hmid] at hhalf
          exact hhalf
        rw [hrhs] at hhalf'
        exact hhalf'
      have hNreal :
          r ≤ (μz - (N : ℝ)) / 2 := by
        have : ((r : ℝ) : EReal) ≤ (((μz - (N : ℝ)) / 2 : ℝ) : EReal) := by
          rw [hkAll0_coe]
          exact hN
        exact EReal.coe_le_coe_iff.mp this
      have hlt : (μz - (N : ℝ)) / 2 < r := by
        linarith only [hNgt]
      have hfalse : False := by
        exact (not_lt_of_ge hNreal) hlt
      exact False.elim hfalse
  exact le_antisymm hkAll0_le_bot bot_le

-- Proof sketch: specialize mathlib's finite-dimensional `Convex.helly_theorem'` to the
-- Euclidean space `Fin n → ℝ` and the finite index set `Fin m`, taking `Finset.univ` as the full
-- family and using the assumed nonempty intersections for all subfamilies of size at most `n + 1`.
/-- Theorem 21.6: a finite family of convex sets in `ℝⁿ` has nonempty total intersection if
every subcollection of cardinality at most `n + 1` has nonempty intersection, even without any
closedness assumption. -/
theorem theorem21_6_helly_theorem_for_finite_convex_families
    {n m : ℕ}
    (C : Fin m → Set (Fin n → ℝ))
    (hConvex : ∀ i : Fin m, Convex ℝ (C i))
    (hSmallIntersection :
      ∀ s : Finset (Fin m), s.card ≤ n + 1 → (⋂ i ∈ s, C i).Nonempty) :
    (⋂ i : Fin m, C i).Nonempty := by
  classical
  -- Route correction: specialize the existing finite-dimensional Helly theorem directly instead
  -- of rebuilding a bespoke finite-family intersection argument.
  -- Apply mathlib's Helly theorem to the full finite family indexed by `Finset.univ`.
  have hHelly :
      (⋂ i ∈ (Finset.univ : Finset (Fin m)), C i).Nonempty :=
    Convex.helly_theorem' (𝕜 := ℝ) (E := Fin n → ℝ)
      (F := C) (s := (Finset.univ : Finset (Fin m)))
      (by
        -- Every member of the family is convex by the theorem hypothesis.
        intro i hi
        exact hConvex i)
      (by
        -- The textbook small-intersection hypothesis matches Helly's cardinality premise once
        -- the ambient dimension of `Fin n → ℝ` is simplified to `n`.
        intro s hs hcard
        have hs_card : s.card ≤ n + 1 := by
          simpa [Module.finrank_fin_fun] using hcard
        exact hSmallIntersection s hs_card)
  -- Simplify the iterated intersection over `Finset.univ` to the total intersection.
  simpa using hHelly

-- Proof sketch: intersect `C` with each strict or weak sublevel set
-- `\{x | fᵢ(x) < 0\}` or `\{x | gⱼ(x) ≤ 0\}`; convexity of the functions makes every such set
-- convex, so Theorem 21.6 applies to the resulting finite family of convex sets.
/-- Corollary 21.6.1: let `f₁, …, fₖ` and `g₁, …, gₗ` be convex functions on `ℝⁿ`, interpreted as
the strict inequalities `fᵢ(x) < 0` and the weak inequalities `gⱼ(x) ≤ 0`. If every subsystem of
at most `n + 1` of these inequalities has a solution in the convex set `C`, then the whole mixed
system has a solution in `C`. The cases of all strict or all weak inequalities are recovered by
taking `l = 0` or `k = 0`. -/
theorem corollary21_6_1_helly_for_finite_convex_inequalities_on_convex_set
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (fStrict : Fin k → (Fin n → ℝ) → ℝ)
    (hfStrict : ∀ i : Fin k, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fWeak : Fin l → (Fin n → ℝ) → ℝ)
    (hfWeak : ∀ j : Fin l, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fWeak j))
    (hSmallFeasible :
      ∀ s : Finset (Fin k ⊕ Fin l), s.card ≤ n + 1 →
        ∃ x : Fin n → ℝ,
          x ∈ C ∧
            (∀ i : Fin k, Sum.inl i ∈ s → fStrict i x < 0) ∧
              ∀ j : Fin l, Sum.inr j ∈ s → fWeak j x ≤ 0) :
    ∃ x : Fin n → ℝ,
      x ∈ C ∧
        (∀ i : Fin k, fStrict i x < 0) ∧
          ∀ j : Fin l, fWeak j x ≤ 0 := by
  classical
  by_cases hidx : Nonempty (Fin k ⊕ Fin l)
  · let A : (Fin k ⊕ Fin l) → Set (Fin n → ℝ) := fun
      | Sum.inl i => C ∩ {x | fStrict i x < 0}
      | Sum.inr j => C ∩ {x | fWeak j x ≤ 0}
    have hAConvex : ∀ t : Fin k ⊕ Fin l, Convex ℝ (A t) := by
      intro t
      cases t with
      | inl i =>
          -- Each strict constraint contributes a convex strict sublevel set inside `C`.
          simpa [A] using hC.inter ((hfStrict i).convex_lt (0 : ℝ))
      | inr j =>
          -- Each weak constraint contributes a convex weak sublevel set inside `C`.
          simpa [A] using hC.inter ((hfWeak j).convex_le (0 : ℝ))
    have hSmallIntersection :
        ∀ s : Finset (Fin k ⊕ Fin l), s.card ≤ n + 1 → (⋂ t ∈ s, A t).Nonempty := by
      intro s hs
      rcases hSmallFeasible s hs with ⟨x, hxC, hxStrict, hxWeak⟩
      refine ⟨x, ?_⟩
      -- The subsystem witness belongs to every selected constraint set simultaneously.
      refine Set.mem_iInter.2 ?_
      intro t
      refine Set.mem_iInter.2 ?_
      intro ht
      cases t with
      | inl i =>
          have hxAi : x ∈ C ∩ {x | fStrict i x < 0} := ⟨hxC, hxStrict i ht⟩
          simpa [A] using hxAi
      | inr j =>
          have hxAj : x ∈ C ∩ {x | fWeak j x ≤ 0} := ⟨hxC, hxWeak j ht⟩
          simpa [A] using hxAj
    have hHelly :
        (⋂ t ∈ (Finset.univ : Finset (Fin k ⊕ Fin l)), A t).Nonempty := by
      -- Apply finite-dimensional Helly to the mixed family of convex feasible sets.
      refine Convex.helly_theorem' (𝕜 := ℝ) (E := Fin n → ℝ)
        (F := A) (s := (Finset.univ : Finset (Fin k ⊕ Fin l))) ?_ ?_
      · intro t ht
        exact hAConvex t
      · intro s hsSub hsCard
        have hsCard' : s.card ≤ n + 1 := by
          simpa [Module.finrank_fin_fun] using hsCard
        exact hSmallIntersection s hsCard'
    have hGlobalIntersection : (⋂ t : Fin k ⊕ Fin l, A t).Nonempty := by
      simpa using hHelly
    rcases hGlobalIntersection with ⟨x, hxAll⟩
    rcases hidx with ⟨t0⟩
    have hxAt0 : x ∈ A t0 := Set.mem_iInter.1 hxAll t0
    have hxC : x ∈ C := by
      -- Any one index recovers the ambient membership `x ∈ C`.
      cases t0 with
      | inl i =>
          have hxSet : x ∈ C ∩ {x | fStrict i x < 0} := by
            simpa [A] using hxAt0
          exact hxSet.1
      | inr j =>
          have hxSet : x ∈ C ∩ {x | fWeak j x ≤ 0} := by
            simpa [A] using hxAt0
          exact hxSet.1
    have hStrictAll : ∀ i : Fin k, fStrict i x < 0 := by
      intro i
      -- Membership in the global intersection gives the strict inequality for every `i`.
      have hxAi : x ∈ A (Sum.inl i) := Set.mem_iInter.1 hxAll (Sum.inl i)
      have hxSet : x ∈ C ∩ {x | fStrict i x < 0} := by
        simpa [A] using hxAi
      exact hxSet.2
    have hWeakAll : ∀ j : Fin l, fWeak j x ≤ 0 := by
      intro j
      -- The same unpacking yields every weak inequality.
      have hxAj : x ∈ A (Sum.inr j) := Set.mem_iInter.1 hxAll (Sum.inr j)
      have hxSet : x ∈ C ∩ {x | fWeak j x ≤ 0} := by
        simpa [A] using hxAj
      exact hxSet.2
    exact ⟨x, hxC, hStrictAll, hWeakAll⟩
  · rcases hSmallFeasible ∅ (by simp) with ⟨x, hxC, _, _⟩
    refine ⟨x, hxC, ?_, ?_⟩
    · intro i
      -- If the mixed index type is empty, there are no strict constraints to check.
      exact False.elim (hidx ⟨Sum.inl i⟩)
    · intro j
      -- The weak side is vacuous for the same reason.
      exact False.elim (hidx ⟨Sum.inr j⟩)

-- Proof sketch: apply the sparse-certificate extraction route from Theorem 21.3/21.4 to the
-- dual branch produced in Theorem 21.1 or Theorem 21.2, then repackage the resulting sparse
-- `Finsupp` witness as ordinary coefficient families on the original finite index sets.
/-- Helper for Corollary 21.6.2: if a finite convex family in `ℝⁿ` has empty total
intersection, then some subfamily of cardinality at most `n + 1` already has empty
intersection. -/
lemma helperForCorollary_21_6_2_small_infeasible_subfamily_of_empty_finite_convex_intersection
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set (Fin n → ℝ))
    (hConvex : ∀ i : ι, Convex ℝ (A i))
    (hEmpty : ¬ (⋂ i : ι, A i).Nonempty) :
    ∃ s : Finset ι, 0 < s.card ∧ s.card ≤ n + 1 ∧ ¬ (⋂ i ∈ s, A i).Nonempty := by
  classical
  by_cases hExists :
      ∃ s : Finset ι, 0 < s.card ∧ s.card ≤ n + 1 ∧ ¬ (⋂ i ∈ s, A i).Nonempty
  · exact hExists
  · exfalso
    have hAllSmall :
        ∀ s : Finset ι, s.card ≤ n + 1 → (⋂ i ∈ s, A i).Nonempty := by
      intro s hs
      by_cases hsPos : 0 < s.card
      · by_contra hsEmpty
        exact hExists ⟨s, hsPos, hs, hsEmpty⟩
      · have hsZero : s.card = 0 := Nat.eq_zero_of_not_pos hsPos
        have hsEmptySet : s = ∅ := Finset.card_eq_zero.1 hsZero
        simpa [hsEmptySet]
    have hAll :
        (⋂ i : ι, A i).Nonempty := by
      -- Route correction: use the already proved finite-dimensional Helly theorem, then
      -- negate the conclusion to extract the desired small infeasible subsystem.
      simpa using
        (Convex.helly_theorem' (𝕜 := ℝ) (E := Fin n → ℝ)
          (F := A) (s := (Finset.univ : Finset ι))
          (by
            intro i hi
            exact hConvex i)
          (by
            intro s hs hcard
            exact hAllSmall s (by simpa [Module.finrank_fin_fun] using hcard)))
    exact hEmpty hAll

/-- Helper for Corollary 21.6.2: if a selected finite subfamily of the Theorem 21.1 strict
constraints is already infeasible on `C`, then Theorem 21.1 yields a dual certificate
supported on that subfamily alone. -/
lemma helperForCorollary_21_6_2_sparse_dual_for_selected_theorem21_1_subfamily
    {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (s : Finset (Fin m))
    (hsPos : 0 < s.card)
    (hsCard : s.card ≤ n + 1)
    (hNotStrict :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : Fin m, i ∈ s → f i x < (0 : EReal)) :
    ∃ l : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ l i) ∧
        (∃ i : Fin m, l i ≠ 0) ∧
          ((Finset.univ : Finset (Fin m)).filter fun i => l i ≠ 0).card ≤ s.card ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x) := by
  classical
  let p : ℕ := s.card
  have hpPos : 0 < p := by
    simpa [p] using hsPos
  let e : s ≃ Fin p := Finset.equivFin s
  let idx : Fin p → Fin m := fun j => (e.symm j : Fin m)
  let g : Fin p → (Fin n → ℝ) → EReal := fun j => f (idx j)
  have hg : ∀ j, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g j) := by
    intro j
    exact hf (idx j)
  have hdom_g :
      ∀ j, euclideanRelativeInterior_fin n C ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (g j) := by
    intro j
    simpa [g] using hdom_ri (idx j)
  have hNotStrictSelected :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ j : Fin p, g j x < (0 : EReal) := by
    intro hSelected
    apply hNotStrict
    rcases hSelected with ⟨x, hxC, hxSelected⟩
    refine ⟨x, hxC, ?_⟩
    intro i hi
    let j : Fin p := e ⟨i, hi⟩
    simpa [g, idx, j] using hxSelected j
  have hAlt :=
    theorem21_convex_inequality_alternative C hC hpPos g hg hdom_g
  rw [xor_def] at hAlt
  have hSelectedDual :
      ∃ w : Fin p → ℝ,
        (∀ j : Fin p, 0 ≤ w j) ∧
          (∃ j : Fin p, w j ≠ 0) ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤ ∑ j : Fin p, ((w j : ℝ) : EReal) * g j x) := by
    rcases hAlt with hSelectedPrimal | hSelectedDual
    · exact False.elim (hNotStrictSelected hSelectedPrimal.1)
    · exact hSelectedDual.1
  rcases hSelectedDual with ⟨w, hwNonneg, hwNonzero, hmargin⟩
  let l : Fin m → ℝ := fun i =>
    if hi : i ∈ s then w (e ⟨i, hi⟩) else 0
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simp [l, hi, hwNonneg]
    · simp [l, hi]
  · rcases hwNonzero with ⟨j0, hj0⟩
    refine ⟨idx j0, ?_⟩
    have hidxMem : idx j0 ∈ s := (e.symm j0).2
    simp [l, idx, hidxMem, hj0]
  · have hSupportSubset :
        ((Finset.univ : Finset (Fin m)).filter fun i => l i ≠ 0) ⊆ s := by
      intro i hi
      by_contra hiNotMem
      have : l i = 0 := by
        simp [l, hiNotMem]
      exact (Finset.mem_filter.1 hi).2 this
    exact Finset.card_le_card hSupportSubset
  · intro x hxC
    have hsumSelected :
        (∑ j : Fin p, ((w j : ℝ) : EReal) * g j x) =
          Finset.sum s (fun i => ((l i : ℝ) : EReal) * f i x) := by
      calc
        (∑ j : Fin p, ((w j : ℝ) : EReal) * g j x) =
            ∑ i : s, ((l i.1 : ℝ) : EReal) * f i.1 x := by
              refine (Fintype.sum_equiv e.symm
                (fun j : Fin p => ((w j : ℝ) : EReal) * g j x)
                (fun i : s => ((l i.1 : ℝ) : EReal) * f i.1 x) ?_)
              intro j
              have hidxMem : idx j ∈ s := (e.symm j).2
              simp [g, idx, l, hidxMem]
        _ = Finset.sum s (fun i => ((l i : ℝ) : EReal) * f i x) := by
              simpa using
                (Finset.sum_attach s (fun i : Fin m => ((l i : ℝ) : EReal) * f i x))
    have hsumFull :
        Finset.sum s (fun i => ((l i : ℝ) : EReal) * f i x) =
          ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
      refine Finset.sum_subset (by intro i hi; simp) ?_
      intro i hiUniv hiNotMem
      simp [l, hiNotMem]
    calc
      (0 : EReal) ≤ ∑ j : Fin p, ((w j : ℝ) : EReal) * g j x := hmargin x hxC
      _ = Finset.sum s (fun i => ((l i : ℝ) : EReal) * f i x) := hsumSelected
      _ = ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := hsumFull
end Section21
end Chap04
