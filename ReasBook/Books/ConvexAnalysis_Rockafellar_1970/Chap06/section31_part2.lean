/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part1

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.2: a nonnegative affine minorant of the zero-balance slice gap already
encodes a dual vector `xStar`, because evaluating the minorant on each defect slice `u - v`
directly compares the Fenchel integrands of `f` and `g`. -/
lemma helperForLemma_31_0_2_dualWitnessOfNonnegativeSliceGapMinorant {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (ℓ : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hMinorant :
      ∀ z : Fin n → ℝ, (ℓ z : EReal) ≤ helperForLemma_31_0_2_zeroBalanceSliceGap α f g z)
    (hNonnegAtZero : 0 ≤ ℓ 0) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  rcases affineMap_exists_dotProduct_sub (h := ℓ) with ⟨xStar, β, hrepr⟩
  have hβ_nonpos : β ≤ 0 := by
    -- Evaluate the affine representation at the origin to read off the intercept sign.
    have hZero : ℓ 0 = -β := by simpa using hrepr (0 : Fin n → ℝ)
    linarith
  rcases properConvexFunctionOn_exists_finite_point (n := n) (f := g) hg with ⟨v, gv, hgv⟩
  have hvG : v ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
    refine ⟨gv, ?_⟩
    rw [mem_epigraph_univ_iff]
    simpa [hgv]
  let μv : ℝ := v ⬝ᵥ xStar + β - α - gv
  have hFenchelF : fenchelConjugate n f xStar ≤ (μv : EReal) := by
    -- Fix the lower slice at the finite point `v`; every admissible `u` then gives an affine
    -- upper bound on the Fenchel integrand of `f`.
    refine (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μv)).2 ?_
    intro u
    by_cases huF : u ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
    · have hSliceUpper :
          helperForLemma_31_0_2_zeroBalanceSliceGap α f g (u - v) ≤
            f u - ((α : EReal) + g v) := by
        simpa using
          helperForLemma_31_0_2_zeroBalanceSliceGap_le_of_admissiblePair
            (α := α) (z := u - v) (u := u) (v := v) rfl huF hvG
      have hSliceMinor :
          (ℓ (u - v) : EReal) ≤ f u - ((α : EReal) + g v) :=
        le_trans (hMinorant (u - v)) hSliceUpper
      have hgv_ne_bot : g v ≠ (⊥ : EReal) := by
        simpa [hgv] using (EReal.coe_ne_bot gv)
      have hShifted_ne_bot : (α : EReal) + g v ≠ (⊥ : EReal) :=
        add_ne_bot_of_notbot (by simp) hgv_ne_bot
      have hfu_ne_top : f u ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) huF
      have hTranslate :
          (ℓ (u - v) : EReal) + ((α : EReal) + g v) ≤ f u :=
        (EReal.le_sub_iff_add_le
          (Or.inl hShifted_ne_bot)
          (Or.inr hfu_ne_top)).1 hSliceMinor
      have hRewrite :
          (((u ⬝ᵥ xStar - μv : ℝ) : EReal)) =
            (ℓ (u - v) : EReal) + ((α : EReal) + g v) := by
        calc
          (((u ⬝ᵥ xStar - μv : ℝ) : EReal))
              = ((u ⬝ᵥ xStar - v ⬝ᵥ xStar - β + α + gv : ℝ) : EReal) := by
                  congr 1
                  dsimp [μv]
                  ring
          _ = ((((u - v) ⬝ᵥ xStar - β + α + gv : ℝ) : EReal)) := by
                  congr 1
                  simp [dotProduct_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = (ℓ (u - v) : EReal) + ((α : EReal) + g v) := by
                  rw [hrepr (u - v), hgv]
                  simp [EReal.coe_add, add_assoc]
      simpa [hRewrite] using hTranslate
    · have hfu_top : f u = (⊤ : EReal) := by
        by_contra hfu_ne_top
        apply huF
        rw [effectiveDomain_eq]
        exact ⟨by simp, lt_top_iff_ne_top.mpr hfu_ne_top⟩
      simp [hfu_top]
  have hGapAtV :
      ((α - β : ℝ) : EReal) ≤
        (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) - fenchelConjugate n f xStar := by
    have hAdd :
        ((α - β : ℝ) : EReal) + fenchelConjugate n f xStar ≤
          (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) := by
      calc
        ((α - β : ℝ) : EReal) + fenchelConjugate n f xStar
            ≤ ((α - β : ℝ) : EReal) + (μv : EReal) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_right hFenchelF (((α - β : ℝ) : EReal))
        _ = (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) := by
              calc
                ((α - β : ℝ) : EReal) + (μv : EReal)
                    = ((α - β + μv : ℝ) : EReal) := by simp [EReal.coe_add]
                _ = ((v ⬝ᵥ xStar - gv : ℝ) : EReal) := by
                      congr 1
                      dsimp [μv]
                      ring
                _ = (((v ⬝ᵥ xStar : ℝ) : EReal) - (gv : EReal)) := by simp
                _ = (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) := by rw [hgv]
    have hGapTerm_eq :
        (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) = ((v ⬝ᵥ xStar - gv : ℝ) : EReal) := by
      rw [hgv]
      simp
    have hAddReal :
        ((α - β : ℝ) : EReal) + fenchelConjugate n f xStar ≤
          ((v ⬝ᵥ xStar - gv : ℝ) : EReal) := by
      simpa [hGapTerm_eq] using hAdd
    have hRealGap_ne_bot :
        (((v ⬝ᵥ xStar : ℝ) : EReal) - (gv : EReal)) ≠ (⊥ : EReal) := by
      simpa [EReal.coe_sub] using (EReal.coe_ne_bot (v ⬝ᵥ xStar - gv))
    have hRealGap_ne_top :
        (((v ⬝ᵥ xStar : ℝ) : EReal) - (gv : EReal)) ≠ (⊤ : EReal) := by
      simpa [EReal.coe_sub] using (EReal.coe_ne_top (v ⬝ᵥ xStar - gv))
    have hGapReal :
        ((α - β : ℝ) : EReal) ≤
          ((v ⬝ᵥ xStar - gv : ℝ) : EReal) - fenchelConjugate n f xStar := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inr hRealGap_ne_bot)
          (Or.inr hRealGap_ne_top)).2 hAddReal
    simpa [hGapTerm_eq] using hGapReal
  have hFenchelG :
      (((v ⬝ᵥ xStar : ℝ) : EReal) - g v) ≤ fenchelConjugate n g xStar := by
    -- The point `v` itself is one admissible term in the defining supremum of `g*`.
    unfold fenchelConjugate
    exact le_sSup ⟨v, rfl⟩
  have hGap :
      ((α - β : ℝ) : EReal) ≤
        fenchelConjugate n g xStar - fenchelConjugate n f xStar := by
    exact le_trans hGapAtV (EReal.sub_le_sub hFenchelG le_rfl)
  have hAlpha :
      (α : EReal) ≤ ((α - β : ℝ) : EReal) := by
    exact_mod_cast (by linarith)
  exact ⟨xStar, le_trans hAlpha hGap⟩

/-- Helper for Lemma 31.0.2: for the one-dimensional quadratic self-pair, the unit-defect
zero-balance slice attains every negative integer value, so the slice-gap route cannot admit a
global finite affine minorant. -/
lemma helperForLemma_31_0_2_selfQuadraticZeroBalanceSliceGap_unit_le_negNat
    (N : ℕ) :
    helperForLemma_31_0_2_zeroBalanceSliceGap
        (n := 1) 0
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        (fun _ : Fin 1 => (1 : ℝ)) ≤
      ((-(N : ℝ) : ℝ) : EReal) := by
  let u : Fin 1 → ℝ := fun _ => (1 - (N : ℝ)) / 2
  let v : Fin 1 → ℝ := fun _ => -((N : ℝ) + 1) / 2
  have hEq : u - v = (fun _ : Fin 1 => (1 : ℝ)) := by
    ext i
    fin_cases i
    simp [u, v]
    ring
  have huDom :
      u ∈ effectiveDomain
        (Set.univ : Set (Fin 1 → ℝ))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    -- The quadratic test function is finite at every point, so the chosen upper witness is in its
    -- effective domain.
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    exact lt_top_iff_ne_top.mpr (EReal.coe_ne_top (((1 - (N : ℝ)) / 2)^2))
  have hvDom :
      v ∈ effectiveDomain
        (Set.univ : Set (Fin 1 → ℝ))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    -- The same finiteness argument applies to the lower witness.
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    exact lt_top_iff_ne_top.mpr (EReal.coe_ne_top ((-((N : ℝ) + 1) / 2)^2))
  have hSlice :
      helperForLemma_31_0_2_zeroBalanceSliceGap
          (n := 1) 0
          (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
          (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
          (fun _ : Fin 1 => (1 : ℝ)) ≤
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) u -
          ((0 : EReal) +
            (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) v) :=
    helperForLemma_31_0_2_zeroBalanceSliceGap_le_of_admissiblePair
      (α := 0) (z := (fun _ : Fin 1 => (1 : ℝ))) (u := u) (v := v) hEq huDom hvDom
  -- Evaluating the admissible pair `(u, v)` gives the exact value `u^2 - v^2 = -N`.
  have hValue :
      ((u 0)^2 : ℝ) - (v 0)^2 = -(N : ℝ) := by
    dsimp [u, v]
    ring
  have hValueE :
      (((u 0)^2 - (v 0)^2 : ℝ) : EReal) = ((-(N : ℝ) : ℝ) : EReal) := by
    exact_mod_cast hValue
  calc
    helperForLemma_31_0_2_zeroBalanceSliceGap
        (n := 1) 0
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))
        (fun _ : Fin 1 => (1 : ℝ))
        ≤
      (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) u -
        ((0 : EReal) +
          (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) v) := hSlice
    _ = (((u 0)^2 - (v 0)^2 : ℝ) : EReal) := by
      simp [u, v, EReal.coe_add, EReal.coe_sub]
    _ = ((-(N : ℝ) : ℝ) : EReal) := hValueE

/-- Helper for Lemma 31.0.2: the quadratic self-pair already refutes the global affine-sandwich
route `g + α ≤ h ≤ f`, so the remaining bridge has to produce the dual witness directly. -/
lemma helperForLemma_31_0_2_selfQuadraticRefutesAffineSandwichRoute :
    ¬ ∃ h : AffineMap ℝ (Fin 1 → ℝ) ℝ,
      (∀ x : Fin 1 → ℝ, (((x 0)^2 : ℝ) : EReal) ≤ (h x : EReal)) ∧
        (∀ x : Fin 1 → ℝ, (h x : EReal) ≤ (((x 0)^2 : ℝ) : EReal)) := by
  rintro ⟨h, hLower, hUpper⟩
  rcases affineMap_exists_dotProduct_sub (h := h) with ⟨xStar, β, hrepr⟩
  let x0 : Fin 1 → ℝ := 0
  let x1 : Fin 1 → ℝ := fun _ => 1
  let x2 : Fin 1 → ℝ := fun _ => 2
  have h0leE : (h x0 : EReal) ≤ (0 : EReal) := by
    simpa [x0] using hUpper x0
  have h0geE : (0 : EReal) ≤ (h x0 : EReal) := by
    simpa [x0] using hLower x0
  have h0le : h x0 ≤ 0 := by
    exact_mod_cast h0leE
  have h0ge : 0 ≤ h x0 := by
    exact_mod_cast h0geE
  have h0eq : h x0 = 0 := le_antisymm h0le h0ge
  have hrepr0 : h x0 = -β := by
    simpa [x0, dotProduct] using hrepr x0
  have hBetaZero : β = 0 := by
    linarith
  have h1leE : (h x1 : EReal) ≤ (1 : EReal) := by
    simpa [x1] using hUpper x1
  have h1geE : (1 : EReal) ≤ (h x1 : EReal) := by
    simpa [x1] using hLower x1
  have h1le : h x1 ≤ 1 := by
    exact_mod_cast h1leE
  have h1ge : 1 ≤ h x1 := by
    exact_mod_cast h1geE
  have h1eq : h x1 = 1 := le_antisymm h1le h1ge
  have hrepr1 : h x1 = xStar 0 - β := by
    simpa [x1, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hrepr x1
  have hStarOne : xStar 0 = 1 := by
    linarith
  have h2leE : (h x2 : EReal) ≤ ((((2 : ℝ)^2 : ℝ) : EReal)) := by
    simpa [x2] using hUpper x2
  have h2geE : ((((2 : ℝ)^2 : ℝ) : EReal)) ≤ (h x2 : EReal) := by
    simpa [x2] using hLower x2
  have h2eqE : (h x2 : EReal) = ((((2 : ℝ)^2 : ℝ) : EReal)) := le_antisymm h2leE h2geE
  have hrepr2 : h x2 = 2 * xStar 0 - β := by
    simpa [x2, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hrepr x2
  have h2calc : h x2 = 2 := by
    linarith
  -- Comparing the value at `2` with the quadratic upper/lower bounds forces `2 = 4`.
  have h2eqReal : (2 : ℝ) = 4 := by
    have h2eqE' : ((2 : ℝ) : EReal) = ((4 : ℝ) : EReal) := by
      calc
        ((2 : ℝ) : EReal) = (h x2 : EReal) := by exact_mod_cast h2calc.symm
        _ = ((((2 : ℝ)^2 : ℝ) : EReal) ) := h2eqE
        _ = ((4 : ℝ) : EReal) := by norm_num
    exact_mod_cast h2eqE'
  norm_num at h2eqReal

/-- Helper for Lemma 31.0.2: after discarding the false affine-sandwich route, the remaining
truthful bridge is the direct dual-witness statement coming from the relative-interior
qualification. -/
lemma helperForLemma_31_0_2_directDualWitnessFromRiQualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- Route correction: the affine-sandwich helper is false even for `f = g = x ↦ x^2`,
  -- as the previous lemma shows, so we extract `xStar` directly from conjugate order.
  let _ := hZeroDomDiffRi
  -- First rewrite the primal lower bound into the global shifted inequality `g + α ≤ f`.
  have hShiftedAll : ∀ x : Fin n → ℝ, (α : EReal) + g x ≤ f x := by
    intro x
    by_cases hgx_top : g x = (⊤ : EReal)
    · exfalso
      have : (α : EReal) ≤ (⊥ : EReal) := by
        simpa [hgx_top] using hPointwise x
      simpa using this
    · have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
        rw [effectiveDomain_eq]
        exact ⟨by simp, (lt_top_iff_ne_top).2 hgx_top⟩
      exact
        helperForLemma_31_0_2_shiftedPointwiseBoundOnEffectiveDomain
          (f := f) (g := g) α hg hPointwise hxDom
  let gShift : (Fin n → ℝ) → EReal := fun x => g x + (α : EReal)
  have hShiftedOrder : gShift ≤ f := by
    intro x
    simpa [gShift, add_comm] using hShiftedAll x
  -- Antitonicity of Fenchel conjugation turns the pointwise primal order into a dual upper bound.
  have hConjugateUpper :
      ∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar ≤ fenchelConjugate n g xStar - (α : EReal) := by
    intro xStar
    calc
      fenchelConjugate n f xStar ≤ fenchelConjugate n gShift xStar :=
        (fenchelConjugate_antitone n) hShiftedOrder xStar
      _ = fenchelConjugate n g xStar - (α : EReal) := by
        simpa [gShift] using
          congrArg (fun h => h xStar) (section16_fenchelConjugate_add_const g α)
  -- Properness of `g*` supplies one dual point where `g*` has a finite real value.
  have hgStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) :=
    proper_fenchelConjugate_of_proper (n := n) (f := g) hg
  obtain ⟨xStar, r, hxStarFin⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := fenchelConjugate n g) hgStar
  refine ⟨xStar, ?_⟩
  -- Specialize the dual upper bound at that finite dual point.
  have hAtWitness :
      fenchelConjugate n f xStar ≤ fenchelConjugate n g xStar - (α : EReal) :=
    hConjugateUpper xStar
  have hfStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hfStar_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) := hfStar.2.2 xStar (by simp)
  have hfStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    have hUpperFinite :
        fenchelConjugate n f xStar ≤ ((r - α : ℝ) : EReal) := by
      simpa [hxStarFin] using hAtWitness
    intro htop
    have hleTop : (⊤ : EReal) ≤ ((r - α : ℝ) : EReal) := by
      simpa [htop] using hUpperFinite
    have hEq : (((r - α : ℝ) : EReal)) = (⊤ : EReal) := by
      simpa using hleTop
    exact (EReal.coe_ne_top (r - α)) hEq
  have hAdd :
      (α : EReal) + fenchelConjugate n f xStar ≤ fenchelConjugate n g xStar := by
    have :
        fenchelConjugate n f xStar + (α : EReal) ≤ fenchelConjugate n g xStar :=
      (EReal.le_sub_iff_add_le (Or.inl (by simp)) (Or.inl (by simp))).1 hAtWitness
    simpa [add_comm] using this
  -- Move `f* xStar` back to the right to obtain the required dual gap.
  exact
    (EReal.le_sub_iff_add_le (Or.inl hfStar_ne_bot) (Or.inl hfStar_ne_top)).2 hAdd

/-- Helper for Lemma 31.0.2: the packed lifted balance generator set is nonempty whenever `f` is
proper, because the encoding preserves the finite upper generator produced from `f`. -/
lemma helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet_nonempty {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g).Nonempty := by
  -- Push the existing nonempty lifted generator through the coordinate-packing map.
  rcases
      helperForLemma_31_0_2_liftedBalanceGeneratorSet_nonempty
        (α := α) (f := f) (g := g) hf with
    ⟨z, hz⟩
  refine ⟨prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (z.2.1, z.2.2), z.1), ?_⟩
  exact ⟨z, hz, rfl⟩

/-- Helper for Lemma 31.0.2: once the encoded negative vertical vector is excluded from the raw
lifted balance cone hull, Corollary 11.5.2 yields a separating half-space whose coefficients
decode to the affine-sandwich data `(a, b, t)`. -/
lemma helperForLemma_31_0_2_existsHalfspaceContaining_encodedLiftedBalanceCone {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)))
    (hNotMem :
      helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n) ∉
        (ConvexCone.hull ℝ
          (helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g) :
          Set (Fin (n + 2) → ℝ))) :
    ∃ a : ℝ, ∃ b : Fin n → ℝ, ∃ t : ℝ,
      t < 0 ∧
        (∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
          a + x ⬝ᵥ b + t * μ ≤ 0) ∧
        (∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          -a - x ⬝ᵥ b + t * (-(α + (g x).toReal)) ≤ 0) := by
  let S : Set (Fin (n + 2) → ℝ) := helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g
  let K : Set (Fin (n + 2) → ℝ) := (ConvexCone.hull ℝ S : Set (Fin (n + 2) → ℝ))
  have hSne : S.Nonempty :=
    helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet_nonempty
      (α := α) (f := f) (g := g) hf
  have hKne : K.Nonempty := by
    rcases hSne with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa [K] using (ConvexCone.subset_hull (R := ℝ) (s := S) hy)
  have hKconv : Convex ℝ K := by
    simpa [K] using (ConvexCone.hull ℝ S).convex
  have hKcone : IsConeSet (n + 2) K := by
    intro y hy s hs
    simpa [K] using (ConvexCone.hull ℝ S).smul_mem hs hy
  -- Route correction: the closure/ball route is false, so we separate the forbidden point from
  -- the raw convex cone hull and only then use the cone structure to homogenize the bound.
  obtain ⟨H, hsep⟩ :=
    cor11_5_2_exists_hyperplaneSeparatesProperly_point
      (n := n + 2) (C := K)
      (a := helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n))
      hKne hKconv (by simpa [K] using hNotMem)
  rcases hyperplaneSeparatesProperly_oriented (n + 2) H
      ({helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)} : Set (Fin (n + 2) → ℝ))
      K hsep with
    ⟨w, β, hw0, hH, hForbidden_ge, hKleβ, hproper⟩
  have hbdd : BddAbove ((fun y : Fin (n + 2) → ℝ => dotProduct y w) '' K) :=
    bddAbove_image_dotProduct_of_forall_le
      (n := n + 2) (C := K) w β (fun y hy => hKleβ y hy)
  have hKle : ∀ y ∈ K, dotProduct y w ≤ 0 :=
    thm11_7_dotProduct_le_zero_of_isConeSet_of_bddAbove
      (n := n + 2) (C := K) hKcone (b := w) hbdd
  let q : (Fin (n + 1) → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n + 1)).symm w
  let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm q.1
  have hdotPacked :
      ∀ (lam : ℝ) (x : Fin n → ℝ) (μ : ℝ),
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            w =
          x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
    intro lam x μ
    calc
      dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
          w
          =
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            (prodLinearEquiv_append_coord (n := n + 1) q) := by
              simp [q]
      _ =
        dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 + lam * q.2 := by
          simpa [q] using
            helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
              (n := n + 1)
              (p := (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
              (q := q)
      _ = x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
          have hInner :
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 =
                x ⬝ᵥ p.1 + μ * p.2 := by
            calc
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1
                  =
                dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ))
                  (prodLinearEquiv_append_coord (n := n) p) := by
                    simp [p]
              _ = x ⬝ᵥ p.1 + μ * p.2 := by
                  simpa [p] using
                    helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                      (n := n) (p := (x, μ)) (q := p)
          rw [hInner]
  have hGeneratorLe :
      ∀ y ∈ S, dotProduct y w ≤ 0 := by
    intro y hy
    exact hKle y (by simpa [K] using (ConvexCone.subset_hull (R := ℝ) (s := S) hy))
  have htle : p.2 ≤ 0 := by
    have hImageNonempty : ((fun y : Fin (n + 2) → ℝ => dotProduct y w) '' K).Nonempty := by
      simpa using hKne.image (fun y : Fin (n + 2) → ℝ => dotProduct y w)
    have hsSup :
        sSup ((fun y : Fin (n + 2) → ℝ => dotProduct y w) '' K) = (0 : ℝ) :=
      thm11_7_sSup_image_dotProduct_eq_zero_of_isConeSet
        (n := n + 2) (C := K) hKne hKcone w hbdd
    have h0leβ : (0 : ℝ) ≤ β := by
      have hSupLeβ :
          sSup ((fun y : Fin (n + 2) → ℝ => dotProduct y w) '' K) ≤ β := by
        refine csSup_le hImageNonempty ?_
        intro r hr
        rcases hr with ⟨y, hyK, rfl⟩
        exact hKleβ y hyK
      simpa [hsSup] using hSupLeβ
    have hForbidden_nonneg :
        (0 : ℝ) ≤ dotProduct (helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)) w := by
      exact le_trans h0leβ (hForbidden_ge _ (by simp))
    have hDotForbidden :
        dotProduct (helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)) w = -p.2 := by
      simpa [helperForLemma_31_0_2_encodedNegativeVerticalPoint, hdotPacked, p, q]
        using hdotPacked (0 : ℝ) 0 (-1 : ℝ)
    rw [hDotForbidden] at hForbidden_nonneg
    linarith
  have hDotForbidden :
      dotProduct (helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)) w = -p.2 := by
    simpa [helperForLemma_31_0_2_encodedNegativeVerticalPoint, hdotPacked, p, q]
      using hdotPacked (0 : ℝ) 0 (-1 : ℝ)
  have htneg : p.2 < 0 := by
    by_contra hNotNeg
    have ht0 : p.2 = 0 := le_antisymm htle (not_lt.mp hNotNeg)
    let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
    let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
    rcases hri with ⟨x0, hx0F_ri, hx0G_ri⟩
    have hx0F : x0 ∈ domF := by
      exact
        helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
          (by simpa [domF] using hx0F_ri)
    have hx0G : x0 ∈ domG := by
      exact
        helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
          (by simpa [domG] using hx0G_ri)
    have hx0F_intr_raw :
        x0 ∈ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hx0F_ri
      exact hx0F_ri
    have hx0G_intr_raw :
        x0 ∈ intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
      rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hx0G_ri
      exact hx0G_ri
    have hdomF_conv : Convex ℝ domF :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf.1
    have hdomG_conv : Convex ℝ domG :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hg.1
    have hUpperDomF : ∀ {x : Fin n → ℝ}, x ∈ domF → q.2 + x ⬝ᵥ p.1 ≤ 0 := by
      intro x hxF
      have hfx_ne_top : f x ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
      have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      let μ : ℝ := (f x).toReal
      have hμ_eq : f x = (μ : EReal) := by
        simpa [μ] using (EReal.coe_toReal (x := f x) hfx_ne_top hfx_ne_bot).symm
      have hy :
          prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)) ∈ S :=
        helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_upper
          (α := α) (f := f) (g := g) (x := x) (μ := μ) (by simpa [hμ_eq])
      have hyLe : dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)))
            w ≤ 0 :=
        hGeneratorLe _ hy
      rw [hdotPacked (1 : ℝ) x μ, ht0] at hyLe
      simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hyLe
    have hLowerDomG : ∀ {x : Fin n → ℝ}, x ∈ domG → 0 ≤ q.2 + x ⬝ᵥ p.1 := by
      intro x hxG
      have hy :
          prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)) ∈ S :=
        helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_lower
          (α := α) (f := f) (g := g) (x := x) hxG
      have hyLe : dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)))
            w ≤ 0 :=
        hGeneratorLe _ hy
      rw [hdotPacked (-1 : ℝ) (-x) (-(α + (g x).toReal)), ht0] at hyLe
      rw [neg_dotProduct, neg_one_mul] at hyLe
      linarith
    have hx0Eq : x0 ⬝ᵥ p.1 = -q.2 := by
      have hx0Upper : q.2 + x0 ⬝ᵥ p.1 ≤ 0 := hUpperDomF hx0F
      have hx0Lower : 0 ≤ q.2 + x0 ⬝ᵥ p.1 := hLowerDomG hx0G
      linarith
    let Hdom : Set (Fin n → ℝ) := {x : Fin n → ℝ | x ⬝ᵥ p.1 = -q.2}
    have hx0Hdom : x0 ∈ Hdom := by
      simp [Hdom, hx0Eq]
    have hDomF_subset_Hdom : domF ⊆ Hdom := by
      by_cases hb : p.1 = 0
      · intro x hxF
        have hEq0 : q.2 = 0 := by
          simpa [hb] using hx0Eq
        simp [Hdom, hb, hEq0]
      · by_contra hNotSubset
        have hSupport :
            IsSupportingHyperplane n domF Hdom := by
          refine ⟨p.1, -q.2, hb, rfl, ?_, ?_⟩
          · intro x hxF
            have hxLe : q.2 + x ⬝ᵥ p.1 ≤ 0 := hUpperDomF hxF
            linarith
          · exact ⟨x0, hx0F, by simpa [Hdom] using hx0Hdom⟩
        have hExists :
            ∃ H0, IsNontrivialSupportingHyperplane n domF H0 ∧ ({x0} : Set (Fin n → ℝ)) ⊆ H0 := by
          refine ⟨Hdom, ⟨hSupport, hNotSubset⟩, ?_⟩
          intro x hx
          simpa using (Set.mem_singleton_iff.mp hx ▸ hx0Hdom)
        have hiff :=
          exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior
            (n := n) domF ({x0} : Set (Fin n → ℝ)) hdomF_conv (Set.singleton_nonempty x0)
            (convex_singleton x0) (by simp [hx0F])
        have hdisj : Disjoint ({x0} : Set (Fin n → ℝ)) (intrinsicInterior ℝ domF) :=
          hiff.1 hExists
        have hdisj_raw :
            Disjoint ({x0} : Set (Fin n → ℝ))
              (intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) := by
          exact (by
            dsimp [domF] at hdisj
            exact hdisj)
        exact (Set.disjoint_singleton_left.mp hdisj_raw) hx0F_intr_raw
    have hDomG_subset_Hdom : domG ⊆ Hdom := by
      by_cases hb : p.1 = 0
      · intro x hxG
        have hEq0 : q.2 = 0 := by
          simpa [hb] using hx0Eq
        simp [Hdom, hb, hEq0]
      · by_contra hNotSubset
        have hSupport :
            IsSupportingHyperplane n domG Hdom := by
          refine ⟨-p.1, q.2, by simpa using neg_ne_zero.mpr hb, ?_, ?_, ?_⟩
          · ext x
            constructor <;> intro hx <;> simp [Hdom] at hx ⊢ <;> linarith
          · intro x hxG
            have hxLe : 0 ≤ q.2 + x ⬝ᵥ p.1 := hLowerDomG hxG
            have : x ⬝ᵥ (-p.1) ≤ q.2 := by
              simpa [neg_dotProduct] using (show -(x ⬝ᵥ p.1) ≤ q.2 by linarith)
            exact this
          · refine ⟨x0, hx0G, ?_⟩
            have : -(x0 ⬝ᵥ p.1) = q.2 := by
              linarith [hx0Eq]
            simpa [neg_dotProduct] using this
        have hExists :
            ∃ H0, IsNontrivialSupportingHyperplane n domG H0 ∧ ({x0} : Set (Fin n → ℝ)) ⊆ H0 := by
          refine ⟨Hdom, ⟨hSupport, hNotSubset⟩, ?_⟩
          intro x hx
          simpa using (Set.mem_singleton_iff.mp hx ▸ hx0Hdom)
        have hiff :=
          exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior
            (n := n) domG ({x0} : Set (Fin n → ℝ)) hdomG_conv (Set.singleton_nonempty x0)
            (convex_singleton x0) (by simp [hx0G])
        have hdisj : Disjoint ({x0} : Set (Fin n → ℝ)) (intrinsicInterior ℝ domG) :=
          hiff.1 hExists
        have hdisj_raw :
            Disjoint ({x0} : Set (Fin n → ℝ))
              (intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) := by
          exact (by
            dsimp [domG] at hdisj
            exact hdisj)
        exact (Set.disjoint_singleton_left.mp hdisj_raw) hx0G_intr_raw
    have hβ_nonneg : (0 : ℝ) ≤ β := by
      by_contra hβneg
      rcases hKne with ⟨y0, hy0K⟩
      have hy0le0 : dotProduct y0 w ≤ 0 := hKle y0 hy0K
      by_cases hy0zero : dotProduct y0 w = 0
      · have hy0β : dotProduct y0 w ≤ β := hKleβ y0 hy0K
        rw [hy0zero] at hy0β
        linarith
      · have hy0neg : dotProduct y0 w < 0 := lt_of_le_of_ne hy0le0 hy0zero
        let t : ℝ := β / (2 * dotProduct y0 w)
        have htpos : 0 < t := by
          dsimp [t]
          have hβlt : β < 0 := lt_of_not_ge hβneg
          have hdenlt : 2 * dotProduct y0 w < 0 := by linarith
          exact div_pos_of_neg_of_neg hβlt hdenlt
        have htyK : t • y0 ∈ K := hKcone y0 hy0K t htpos
        have hScaled : dotProduct (t • y0) w ≤ β := hKleβ _ htyK
        have hScaled' : t * dotProduct y0 w ≤ β := by
          simpa [dotProduct_smul, smul_eq_mul] using hScaled
        have hy0_ne : dotProduct y0 w ≠ 0 := hy0zero
        have hHalf : t * dotProduct y0 w = β / 2 := by
          dsimp [t]
          field_simp [hy0_ne]
        have hβlt : β < β / 2 := by
          linarith [lt_of_not_ge hβneg]
        have hHalfLe : β / 2 ≤ β := by
          simpa [hHalf] using hScaled'
        exact (not_le_of_gt hβlt) hHalfLe
    have hβ_nonpos : β ≤ 0 := by
      have hForbid : β ≤
          dotProduct (helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)) w :=
        hForbidden_ge _ (by simp)
      rw [hDotForbidden, ht0] at hForbid
      simpa using hForbid
    have hβ0 : β = 0 := le_antisymm hβ_nonpos hβ_nonneg
    have hDotEqZeroOnGenerators : ∀ y ∈ S, dotProduct y w = 0 := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨x, μ, rfl, hμ⟩ | ⟨x, hxG, rfl⟩
      · have hxF : x ∈ domF := by
          refine ⟨μ, ?_⟩
          rw [mem_epigraph_univ_iff]
          exact hμ
        have hxHdom : x ∈ Hdom := hDomF_subset_Hdom hxF
        rw [hdotPacked (1 : ℝ) x μ, ht0]
        have hxEq' : x ⬝ᵥ p.1 = -q.2 := by
          simpa [Hdom] using hxHdom
        linarith
      · have hxHdom : x ∈ Hdom := hDomG_subset_Hdom hxG
        rw [hdotPacked (-1 : ℝ) (-x) (-(α + (g x).toReal)), ht0]
        rw [neg_dotProduct, neg_one_mul]
        have hxEq' : x ⬝ᵥ p.1 = -q.2 := by
          simpa [Hdom] using hxHdom
        linarith
    have hDotEqZeroOnK : ∀ y ∈ K, dotProduct y w = 0 := by
      intro y hyK
      have hyCG : y ∈ convexConeGenerated (n + 2) S := by
        have hyInsert :
            y ∈ Set.insert (0 : Fin (n + 2) → ℝ)
              ((ConvexCone.hull ℝ S : ConvexCone ℝ (Fin (n + 2) → ℝ)) : Set (Fin (n + 2) → ℝ)) :=
          (Set.mem_insert_iff).2 (Or.inr (by simpa [K] using hyK))
        simpa [convexConeGenerated] using hyInsert
      rcases
          mem_convexConeGenerated_imp_exists_nonnegLinearCombination_le
            (n := n + 2) (T := S) hSne hyCG with
        ⟨k, _hk, v, c, hv, _hc, hyEq⟩
      have hsum :
          dotProduct (∑ j, c j • v j) w = ∑ j, c j * dotProduct (v j) w := by
        calc
          dotProduct (∑ j, c j • v j) w = ∑ j, dotProduct (c j • v j) w := by
            simpa using
              (sum_dotProduct (s := (Finset.univ : Finset (Fin k)))
                (u := fun j => c j • v j) (v := w))
          _ = ∑ j, c j * dotProduct (v j) w := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [dotProduct_smul, smul_eq_mul]
      calc
        dotProduct y w = dotProduct (∑ j, c j • v j) w := by simpa [hyEq]
        _ = ∑ j, c j * dotProduct (v j) w := hsum
        _ = 0 := by
              refine Finset.sum_eq_zero ?_
              intro j hj
              simp [hDotEqZeroOnGenerators (v j) (hv j)]
    have hForbidden_subset_H : ({helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n)} :
        Set (Fin (n + 2) → ℝ)) ⊆ H := by
      intro y hy
      have hyEq :
          y = helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n) := by
        simpa using hy
      subst hyEq
      simpa [hH, hβ0, hDotForbidden, ht0]
    have hK_subset_H : K ⊆ H := by
      intro y hyK
      rw [hH, hβ0]
      exact hDotEqZeroOnK y hyK
    exact hproper ⟨hForbidden_subset_H, hK_subset_H⟩
  refine ⟨q.2, p.1, p.2, htneg, ?_, ?_⟩
  · intro x μ hμ
    -- Evaluate the containing half-space on the encoded upper generator.
    have hy :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)) ∈ S :=
      helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_upper
        (α := α) (f := f) (g := g) (x := x) (μ := μ) hμ
    have hyLe : dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)))
          w ≤ 0 :=
      hGeneratorLe _ hy
    rw [hdotPacked (1 : ℝ) x μ] at hyLe
    rw [one_mul, mul_comm μ p.2] at hyLe
    linarith
  · intro x hx
    -- Evaluate the containing half-space on the repaired exact lower generator.
    have hy :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)) ∈ S :=
      helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_lower
        (α := α) (f := f) (g := g) (x := x) hx
    have hyLe : dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)))
          w ≤ 0 :=
      hGeneratorLe _ hy
    rw [hdotPacked (-1 : ℝ) (-x) (-(α + (g x).toReal))] at hyLe
    rw [neg_dotProduct, neg_one_mul, mul_comm (-(α + (g x).toReal)) p.2] at hyLe
    linarith

/-- Helper for Lemma 31.0.2: coefficients `(a, b, t)` with `t < 0` satisfying the packed
generator inequalities normalize to an affine sandwich `g + α ≤ h ≤ f`. -/
lemma helperForLemma_31_0_2_affineSandwichOfHalfspaceCoefficients {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {a : ℝ} {b : Fin n → ℝ} {t : ℝ} (ht : t < 0)
    (hUpper : ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
      a + x ⬝ᵥ b + t * μ ≤ 0)
    (hLower : ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
      -a - x ⬝ᵥ b + t * (-(α + (g x).toReal)) ≤ 0) :
    ∃ h : AffineMap ℝ (Fin n → ℝ) ℝ,
      (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
        (α : EReal) + g x ≤ (h x : EReal)) ∧
        (∀ x : Fin n → ℝ, (h x : EReal) ≤ f x) := by
  let hAff : AffineMap ℝ (Fin n → ℝ) ℝ :=
    (((-1 / t : ℝ) • dotProductLinear n b).toAffineMap) -
      AffineMap.const ℝ (Fin n → ℝ) (a / t)
  have hAff_repr :
      ∀ x : Fin n → ℝ, hAff x = -(a + x ⬝ᵥ b) / t := by
    intro x
    simp [hAff, dotProductLinear, div_eq_mul_inv, sub_eq_add_neg]
    ring
  refine ⟨hAff, ?_, ?_⟩
  · intro x hx
    -- On `dom g`, choose the exact real lower slice and divide the separator inequality by `t < 0`.
    have hgx_ne_top : g x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx
    have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    let gx : ℝ := (g x).toReal
    have hgx_eq : g x = (gx : EReal) := by
      simpa [gx] using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
    let s : ℝ := α + gx
    have hs_eq : (α : EReal) + g x = (s : EReal) := by
      simp [s, hgx_eq, EReal.coe_add]
    have hSlice : -a - x ⬝ᵥ b + t * (-s) ≤ 0 := by
      -- The repaired lower generator already uses the exact finite slice on `dom g`.
      simpa [s, gx] using hLower (x := x) hx
    have hNumerator : -(a + x ⬝ᵥ b) ≤ s * t := by
      have hSlice' : -a - x ⬝ᵥ b - t * s ≤ 0 := by
        simpa [mul_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSlice
      linarith
    have hReal : s ≤ hAff x := by
      rw [hAff_repr x]
      exact (le_div_iff_of_neg ht).2 (by simpa [mul_comm] using hNumerator)
    have hCoe : ((s : ℝ) : EReal) ≤ (hAff x : EReal) := by
      exact_mod_cast hReal
    calc
      (α : EReal) + g x = (s : EReal) := hs_eq
      _ ≤ (hAff x : EReal) := hCoe
  · intro x
    -- For `f x < ⊤`, choose the exact real upper slice; if `f x = ⊤`, the upper sandwich is trivial.
    by_cases hfx_top : f x = (⊤ : EReal)
    · simpa [hfx_top]
    · have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      let μ : ℝ := (f x).toReal
      have hμ_eq : f x = (μ : EReal) := by
        simpa [μ] using (EReal.coe_toReal (x := f x) hfx_top hfx_ne_bot).symm
      have hSlice : a + x ⬝ᵥ b + t * μ ≤ 0 := by
        exact hUpper (x := x) (μ := μ) (by simpa [hμ_eq])
      have hNumerator : μ * t ≤ -(a + x ⬝ᵥ b) := by
        have hSlice' : a + x ⬝ᵥ b + μ * t ≤ 0 := by
          simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hSlice
        linarith
      have hReal : hAff x ≤ μ := by
        rw [hAff_repr x]
        exact (div_le_iff_of_neg ht).2 hNumerator
      have hCoe : (hAff x : EReal) ≤ (μ : EReal) := by
        exact_mod_cast hReal
      calc
        (hAff x : EReal) ≤ (μ : EReal) := hCoe
        _ = f x := hμ_eq.symm

/-- Helper for Lemma 31.0.2: an affine upper bound `h ≤ f` controls `f*` by the affine
intercept. -/
lemma helperForLemma_31_0_2_fenchelConjugateUpperBound_of_affineUpperBound {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (h : AffineMap ℝ (Fin n → ℝ) ℝ)
    {xStar : Fin n → ℝ} {β : ℝ}
    (hrepr : ∀ x : Fin n → ℝ, h x = x ⬝ᵥ xStar - β)
    (hUpper : ∀ x : Fin n → ℝ, (h x : EReal) ≤ f x) :
    fenchelConjugate n f xStar ≤ (β : EReal) := by
  -- Rewrite the affine map into the standard dot-product form expected by the conjugate lemma.
  refine (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := β)).2 ?_
  intro x
  -- The affine majorant hypothesis is exactly the required pointwise comparison after rewriting.
  simpa [hrepr x] using hUpper x

/-- Helper for Lemma 31.0.2: an affine lower bound `g + α ≤ h` forces `g*` to dominate the
shifted affine intercept `α + β`. -/
lemma helperForLemma_31_0_2_fenchelConjugateLowerBound_of_affineLowerBound {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (α : ℝ) (h : AffineMap ℝ (Fin n → ℝ) ℝ)
    {xStar : Fin n → ℝ} {β : ℝ}
    (hrepr : ∀ x : Fin n → ℝ, h x = x ⬝ᵥ xStar - β)
    (hLower : ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
      (α : EReal) + g x ≤ (h x : EReal)) :
    ((α + β : ℝ) : EReal) ≤ fenchelConjugate n g xStar := by
  -- Choose a point where `g` is finite so the domain-restricted lower bound applies.
  obtain ⟨x0, r0, hx0Val⟩ :=
    properConvexFunctionOn_exists_finite_point (n := n) (f := g) hg
  have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
    refine ⟨r0, ?_⟩
    rw [mem_epigraph_univ_iff]
    simpa [hx0Val]
  have hgx0_ne_bot : g x0 ≠ (⊥ : EReal) := hg.2.2 x0 (by simp)
  have hgx0_ne_top : g x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx0Dom
  -- Rewrite the affine lower bound at `x₀` into the dot-product form that feeds the conjugate.
  have hLowerAtX0 :
      (α : EReal) + g x0 ≤ (((x0 ⬝ᵥ xStar : ℝ) : EReal) - (β : EReal)) := by
    simpa [hrepr x0, sub_eq_add_neg, EReal.coe_add, add_assoc, add_left_comm, add_comm] using
      hLower x0 hx0Dom
  -- Move `β` to the left-hand side so the target becomes a single-point conjugate estimate.
  have hShifted :
      (((α + β : ℝ) : EReal) + g x0) ≤ ((x0 ⬝ᵥ xStar : ℝ) : EReal) := by
    have hβ :
        ((α : EReal) + g x0) + (β : EReal) ≤ ((x0 ⬝ᵥ xStar : ℝ) : EReal) :=
      (EReal.le_sub_iff_add_le
        (Or.inl (by simp))
        (Or.inl (by simp))).1 hLowerAtX0
    simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hβ
  -- Convert the pointwise inequality into the corresponding lower bound on `g* xStar`.
  have hPoint :
      ((α + β : ℝ) : EReal) ≤ ((x0 ⬝ᵥ xStar : ℝ) : EReal) - g x0 := by
    exact
      (EReal.le_sub_iff_add_le
        (Or.inl hgx0_ne_bot)
        (Or.inl hgx0_ne_top)).2 hShifted
  have hTermLe :
      (((x0 ⬝ᵥ xStar : ℝ) : EReal) - g x0) ≤ fenchelConjugate n g xStar := by
    unfold fenchelConjugate
    exact le_sSup ⟨x0, rfl⟩
  exact le_trans hPoint hTermLe

/-- Helper for Lemma 31.0.2: any affine sandwich `g + α ≤ h ≤ f` yields a dual witness
`xStar` with `g* xStar - f* xStar ≥ α`. -/
lemma helperForLemma_31_0_2_affineSandwichYieldsDualWitness {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (α : ℝ) (h : AffineMap ℝ (Fin n → ℝ) ℝ)
    (hLower : ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
      (α : EReal) + g x ≤ (h x : EReal))
    (hUpper : ∀ x : Fin n → ℝ, (h x : EReal) ≤ f x) :
    ∃ xStar : Fin n → ℝ, fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  rcases affineMap_exists_dotProduct_sub (h := h) with ⟨xStar, β, hrepr⟩
  refine ⟨xStar, ?_⟩
  -- Convert the upper sandwich inequality into the usual conjugate upper bound for `f*`.
  have hF :
      fenchelConjugate n f xStar ≤ (β : EReal) :=
    helperForLemma_31_0_2_fenchelConjugateUpperBound_of_affineUpperBound
      (n := n) (f := f) h hrepr hUpper
  -- Convert the lower sandwich inequality into the corresponding conjugate lower bound for `g*`.
  have hG :
      ((α + β : ℝ) : EReal) ≤ fenchelConjugate n g xStar :=
    helperForLemma_31_0_2_fenchelConjugateLowerBound_of_affineLowerBound
      (n := n) (g := g) hg α h hrepr hLower
  -- Rearranging the two conjugate estimates leaves the desired dual gap `α`.
  have hGapToBeta :
      (α : EReal) ≤ fenchelConjugate n g xStar - (β : EReal) := by
    have hb1 :
        ((β : ℝ) : EReal) ≠ ⊥ ∨ fenchelConjugate n g xStar ≠ ⊥ :=
      Or.inl (by simp)
    have hb2 :
        ((β : ℝ) : EReal) ≠ ⊤ ∨ fenchelConjugate n g xStar ≠ ⊤ :=
      Or.inl (by simp)
    exact
      (EReal.le_sub_iff_add_le hb1 hb2).2
        (by simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hG)
  have hBetaToF :
      fenchelConjugate n g xStar - (β : EReal) ≤
        fenchelConjugate n g xStar - fenchelConjugate n f xStar := by
    -- Making the subtrahend smaller can only increase the extended-real difference.
    exact EReal.sub_le_sub le_rfl hF
  exact le_trans hGapToBeta hBetaToF

/-- Helper for Lemma 31.0.2: once the relative-interior qualification is packaged as a direct
dual-witness bridge, it closes the target theorem immediately. -/
lemma helperForLemma_31_0_2_dualWitnessFromRiQualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- Route correction: the global affine-sandwich intermediary is false, so use the truthful
  -- direct dual-witness bridge instead.
  exact
    helperForLemma_31_0_2_directDualWitnessFromRiQualification
      (α := α) (f := f) (g := g) hf hg hPointwise hZeroDomDiffRi


end Section31
end Chap06
