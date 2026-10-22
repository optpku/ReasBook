/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part6

section Chap06
section Section27
/-- Helper for Theorem 6.27.6: every admissible epigraph/auxiliary pair gives an explicit upper
bound on the zero-balance slice gap at its horizontal defect. -/
lemma helperForTheorem_6_27_6_zeroBalanceSliceGap_le_of_admissiblePair
    {n : ℕ} (α : ℝ) {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    {p q : (Fin n → ℝ) × ℝ} {z : Fin n → ℝ}
    (hp : p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h)
    (hq : q ∈ constrainedMinimumAuxiliarySet h C)
    (hz : p.1 - q.1 = z) :
    helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z ≤ ((p.2 - q.2 : ℝ) : EReal) := by
  -- Evaluate the defining infimum at the chosen admissible pair.
  rw [helperForTheorem_6_27_6_zeroBalanceSliceGap]
  refine iInf_le_of_le ⟨p, hp⟩ ?_
  refine iInf_le_of_le ⟨q, hq⟩ ?_
  simp [hz]

/-- Helper for Theorem 6.27.6: the zero-balance slice gap vanishes at the attained contact point
because the contact pair realizes zero horizontal defect and zero vertical gap. -/
lemma helperForTheorem_6_27_6_zeroBalanceSliceGap_eq_zero_at_origin
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    helperForTheorem_6_27_6_zeroBalanceSliceGap α h C 0 = 0 := by
  have hNonneg :
      (0 : EReal) ≤ helperForTheorem_6_27_6_zeroBalanceSliceGap α h C 0 :=
    helperForTheorem_6_27_6_zeroBalanceSliceGap_nonnegative_at_zero
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hUpper :
      helperForTheorem_6_27_6_zeroBalanceSliceGap α h C 0 ≤ (0 : EReal) := by
    simpa using
      helperForTheorem_6_27_6_zeroBalanceSliceGap_le_of_admissiblePair
        (α := α) (h := h) (C := C) (p := (xBar, α)) (q := (xBar, α))
        hContactEpi hContactAux (by simp)
  exact le_antisymm hUpper hNonneg

/-- Helper for Theorem 6.27.6: translate the feasible set so that the minimizing contact point
`xBar` becomes the origin. -/
def helperForTheorem_6_27_6_translatedFeasibleSet {n : ℕ}
    (C : Set (Fin n → ℝ)) (xBar : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | xBar + u ∈ C}

/-- Helper for Theorem 6.27.6: after translating by `xBar`, the feasible set remains nonempty,
closed, and convex. -/
lemma helperForTheorem_6_27_6_translatedFeasibleSet_geometry
    {n : ℕ} {C : Set (Fin n → ℝ)} {xBar : Fin n → ℝ}
    (hxBarC : xBar ∈ C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C) :
    (0 : Fin n → ℝ) ∈ helperForTheorem_6_27_6_translatedFeasibleSet C xBar ∧
      IsClosed (helperForTheorem_6_27_6_translatedFeasibleSet C xBar) ∧
      Convex ℝ (helperForTheorem_6_27_6_translatedFeasibleSet C xBar) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The contact point translates to the origin.
    simpa [helperForTheorem_6_27_6_translatedFeasibleSet] using hxBarC
  · -- Translation is continuous, so closedness pulls back from `C`.
    have hcont : Continuous (fun u : Fin n → ℝ => xBar + u) :=
      continuous_const.add continuous_id
    simpa [helperForTheorem_6_27_6_translatedFeasibleSet] using hCclosed.preimage hcont
  · -- Convex combinations commute with the fixed translation by `xBar`.
    intro u hu v hv a b ha hb hab
    change xBar + (a • u + b • v) ∈ C
    have huC : xBar + u ∈ C := hu
    have hvC : xBar + v ∈ C := hv
    have hrewrite :
        a • (xBar + u) + b • (xBar + v) = xBar + (a • u + b • v) := by
      ext i
      calc
        a * (xBar i + u i) + b * (xBar i + v i)
            = (a + b) * xBar i + (a * u i + b * v i) := by ring
        _ = xBar i + (a * u i + b * v i) := by simp [hab]
    rw [← hrewrite]
    exact hCconvex huC hvC ha hb hab

/-- Helper for Theorem 6.27.6: the zero-balance slice gap is the translated infimum of the
translated-difference function over the feasible translate of `C`. -/
lemma helperForTheorem_6_27_6_zeroBalanceSliceGap_eq_translatedDifference_sInf
    {n : ℕ} {h : (Fin n → ℝ) → EReal} {C : Set (Fin n → ℝ)}
    (α : ℝ) {xBar : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x)
    (hxBar : h xBar = (α : EReal))
    (z : Fin n → ℝ) :
    helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z =
      sInf {r : EReal |
        ∃ y : Fin n → ℝ,
          y ∈ Set.image
              (fun u : Fin n → ℝ => u + z)
              (helperForTheorem_6_27_6_translatedFeasibleSet C xBar) ∧
            r = translatedDifferenceFunctionAt h xBar y} := by
  classical
  let D : Set (Fin n → ℝ) := helperForTheorem_6_27_6_translatedFeasibleSet C xBar
  let S : Set EReal :=
    {r : EReal |
      ∃ y : Fin n → ℝ, y ∈ Set.image (fun u : Fin n → ℝ => u + z) D ∧
        r = translatedDifferenceFunctionAt h xBar y}
  have hxBar_ne_top : h xBar ≠ (⊤ : EReal) := by
    simpa [hxBar] using (EReal.coe_ne_top α)
  have hxBar_ne_bot : h xBar ≠ (⊥ : EReal) := hproper.2.2 xBar (by simp)
  apply le_antisymm
  · -- Every translated witness gives one admissible epigraph/auxiliary pair on the `z`-slice.
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨y, hyImage, rfl⟩
    rcases hyImage with ⟨u, huD, rfl⟩
    have huC : xBar + u ∈ C := by
      simpa [D, helperForTheorem_6_27_6_translatedFeasibleSet] using huD
    have hAuxEq :
        constrainedMinimumAuxiliarySet h C = {q : (Fin n → ℝ) × ℝ | q.1 ∈ C ∧ q.2 ≤ α} :=
      helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
        (h := h) (C := C) α hxBarC hα_lower hxBar
    have hqAux : (xBar + u, α) ∈ constrainedMinimumAuxiliarySet h C := by
      rw [hAuxEq]
      exact ⟨huC, le_rfl⟩
    by_cases htop : h (xBar + (u + z)) = (⊤ : EReal)
    · -- If the translated-difference value is `⊤`, the infimum bound is automatic.
      have htopGap :
          translatedDifferenceFunctionAt h xBar (u + z) = (⊤ : EReal) := by
        rw [translatedDifferenceFunctionAt, htop, hxBar]
        simp
      simpa [htopGap]
    · -- Otherwise choose the real epigraph height `μ = h (xBar + (u + z)).toReal`.
      let μ : ℝ := (h (xBar + (u + z))).toReal
      have hμ : h (xBar + (u + z)) = (μ : EReal) := by
        have hnotbot : h (xBar + (u + z)) ≠ (⊥ : EReal) :=
          hproper.2.2 (xBar + (u + z)) (by simp)
        simpa [μ] using (EReal.coe_toReal (x := h (xBar + (u + z))) htop hnotbot).symm
      have hpEpi : (xBar + (u + z), μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h := by
        rw [mem_epigraph_univ_iff]
        simpa [hμ]
      have hzPair : (xBar + (u + z)) - (xBar + u) = z := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hGap :
          helperForTheorem_6_27_6_zeroBalanceSliceGap α h C z ≤ ((μ - α : ℝ) : EReal) := by
        simpa using
          helperForTheorem_6_27_6_zeroBalanceSliceGap_le_of_admissiblePair
            (α := α) (h := h) (C := C)
            (p := (xBar + (u + z), μ)) (q := (xBar + u, α))
            hpEpi hqAux hzPair
      have hTranslate :
          translatedDifferenceFunctionAt h xBar (u + z) = ((μ - α : ℝ) : EReal) := by
        rw [translatedDifferenceFunctionAt, hxBar, hμ]
        simp [EReal.coe_sub]
      exact hGap.trans_eq hTranslate.symm
  · -- Each admissible pair controls the translated infimum from above.
    rw [helperForTheorem_6_27_6_zeroBalanceSliceGap]
    refine le_iInf ?_
    intro p
    refine le_iInf ?_
    intro q
    by_cases hzPair : p.1.1 - q.1.1 = z
    · have hAuxEq :
          constrainedMinimumAuxiliarySet h C = {q : (Fin n → ℝ) × ℝ | q.1 ∈ C ∧ q.2 ≤ α} :=
        helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
          (h := h) (C := C) α hxBarC hα_lower hxBar
      have hqText : q.1 ∈ {q : (Fin n → ℝ) × ℝ | q.1 ∈ C ∧ q.2 ≤ α} := by
        simpa [hAuxEq] using q.2
      have hqC : q.1.1 ∈ C := hqText.1
      have hqLeAlpha : q.1.2 ≤ α := hqText.2
      have hpLe : h p.1.1 ≤ (p.1.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 p.2
      have hp_ne_top : h p.1.1 ≠ (⊤ : EReal) := by
        intro hp_top
        have : (⊤ : EReal) ≤ (p.1.2 : EReal) := by simpa [hp_top] using hpLe
        exact (not_top_le_coe p.1.2) this
      have hp_ne_bot : h p.1.1 ≠ (⊥ : EReal) := hproper.2.2 p.1.1 (by simp)
      let μp : ℝ := (h p.1.1).toReal
      have hμp : h p.1.1 = (μp : EReal) := by
        simpa [μp] using (EReal.coe_toReal (x := h p.1.1) hp_ne_top hp_ne_bot).symm
      have hpRealLe : μp ≤ p.1.2 := by
        have : ((μp : ℝ) : EReal) ≤ (p.1.2 : EReal) := by simpa [hμp] using hpLe
        exact_mod_cast this
      have hGapReal : μp - α ≤ p.1.2 - q.1.2 := by
        linarith
      have huD : q.1.1 - xBar ∈ D := by
        simpa [D, helperForTheorem_6_27_6_translatedFeasibleSet, sub_eq_iff_eq_add] using hqC
      have hImage :
          p.1.1 - xBar ∈ Set.image (fun u : Fin n → ℝ => u + z) D := by
        refine ⟨q.1.1 - xBar, huD, ?_⟩
        have : q.1.1 - xBar + z = p.1.1 - xBar := by
          calc
            q.1.1 - xBar + z = q.1.1 - xBar + (p.1.1 - q.1.1) := by rw [hzPair]
            _ = p.1.1 - xBar := by
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hTranslateLe :
          translatedDifferenceFunctionAt h xBar (p.1.1 - xBar) ≤
            ((p.1.2 - q.1.2 : ℝ) : EReal) := by
        have hcancel : xBar + (p.1.1 - xBar) = p.1.1 := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [translatedDifferenceFunctionAt, hcancel, hxBar, hμp]
        have : ((μp - α : ℝ) : EReal) ≤ ((p.1.2 - q.1.2 : ℝ) : EReal) := by
          exact_mod_cast hGapReal
        simpa [EReal.coe_sub] using this
      have hInfLe :
          sInf S ≤ translatedDifferenceFunctionAt h xBar (p.1.1 - xBar) := by
        refine sInf_le ?_
        exact ⟨p.1.1 - xBar, hImage, rfl⟩
      exact le_trans hInfLe (by simpa [S, hzPair] using hTranslateLe)
    · -- Off the exact slice, the branch contributes `⊤`, so the infimum bound is immediate.
      simp [hzPair]

/-- Helper for Theorem 6.27.6: every nonnegative vertical gap on the exact zero-balance slice is
already realized by one upper contact generator and one lower contact generator. -/
lemma helperForTheorem_6_27_6_nonnegativeGap_has_rawEncodedConeWitness
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    helperForTheorem_6_27_6_encodedZeroBalancePoint (n := n) δ ∈
      ConvexCone.hull ℝ
        (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) := by
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hRaisedEpi :
      (xBar, α + δ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_epigraph_vertical_upward_closed
      (h := h) (p := (xBar, α)) hContactEpi hδ
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  have hUpper :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ)) ∈
        helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C :=
    helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_upper
      (h := h) (C := C) (p := (xBar, α + δ)) hRaisedEpi
  have hLower :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ)) ∈
        helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C :=
    helperForTheorem_6_27_6_mem_encodedSeparatorGeneratorSet_lower
      (h := h) (C := C) (q := (xBar, α)) hContactAux
  have hUpperHull :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ)) ∈
        ConvexCone.hull ℝ
          (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :=
    ConvexCone.subset_hull (R := ℝ) (s := _) hUpper
  have hLowerHull :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ)) ∈
        ConvexCone.hull ℝ
          (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :=
    ConvexCone.subset_hull (R := ℝ) (s := _) hLower
  have hSum :
      helperForTheorem_6_27_6_encodedZeroBalancePoint (n := n) δ =
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ)) +
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ)) := by
    symm
    calc
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ)) +
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ))
          =
      prodLinearEquiv_append_coord (n := n + 1)
          ((prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ)) +
            (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ))) := by
              simpa using
                ((prodLinearEquiv_append_coord (n := n + 1)).map_add
                  (prodLinearEquiv_append_coord (n := n) (xBar, α + δ), (1 : ℝ))
                  (prodLinearEquiv_append_coord (n := n) (-xBar, -α), (-1 : ℝ))).symm
      _ =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) ((xBar, α + δ) + (-xBar, -α)), (0 : ℝ)) := by
            simpa using
              congrArg (fun z => prodLinearEquiv_append_coord (n := n + 1) (z, (0 : ℝ)))
                (((prodLinearEquiv_append_coord (n := n)).map_add
                  (xBar, α + δ) (-xBar, -α)).symm)
      _ =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (0, δ), (0 : ℝ)) := by
            congr 1
            ext <;> simp
      _ = helperForTheorem_6_27_6_encodedZeroBalancePoint (n := n) δ := by
            rw [helperForTheorem_6_27_6_encodedZeroBalancePoint]
  -- Summing the two contact generators realizes the desired exact zero-balance point.
  rw [hSum]
  exact (ConvexCone.hull ℝ (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C)).add_mem
    hUpperHull hLowerHull

/-- Helper for Theorem 6.27.6: every point of a generated convex cone is a finite nonnegative
conic combination of generators. -/
lemma helperForTheorem_6_27_6_mem_hull_imp_exists_conicCombination
    {N : ℕ} {S : Set (Fin N → ℝ)} {z : Fin N → ℝ}
    (hz : z ∈ ConvexCone.hull ℝ S) :
    ∃ m : ℕ, ∃ v : Fin m → Fin N → ℝ, ∃ lam : Fin m → ℝ,
      (∀ i, v i ∈ S) ∧ (∀ i, 0 ≤ lam i) ∧ z = ∑ i, lam i • v i := by
  classical
  let Krep : ConvexCone ℝ (Fin N → ℝ) :=
    { carrier :=
        {y | ∃ m : ℕ, ∃ v : Fin m → Fin N → ℝ, ∃ lam : Fin m → ℝ,
            (∀ i, v i ∈ S) ∧ (∀ i, 0 ≤ lam i) ∧ y = ∑ i, lam i • v i}
      smul_mem' := by
        intro t ht y hy
        rcases hy with ⟨m, v, lam, hv, hlam, rfl⟩
        refine ⟨m, v, fun i => t * lam i, hv, ?_, ?_⟩
        · intro i
          exact mul_nonneg (le_of_lt ht) (hlam i)
        · simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
              (f := fun i => lam i • v i) (r := t))
      add_mem' := by
        intro x hx y hy
        rcases hx with ⟨m₁, v₁, lam₁, hv₁, hlam₁, rfl⟩
        rcases hy with ⟨m₂, v₂, lam₂, hv₂, hlam₂, rfl⟩
        refine ⟨m₁ + m₂, Fin.append v₁ v₂, Fin.append lam₁ lam₂, ?_, ?_, ?_⟩
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro j
            simpa [Fin.append_left] using hv₁ j
          · intro j
            simpa [Fin.append_right] using hv₂ j
        · intro i
          refine Fin.addCases ?_ ?_ i
          · intro j
            simpa [Fin.append_left] using hlam₁ j
          · intro j
            simpa [Fin.append_right] using hlam₂ j
        · simpa using
            (Fin.sum_univ_add (f := fun i => (Fin.append lam₁ lam₂ i) • (Fin.append v₁ v₂ i))).symm
    }
  have hsubset : S ⊆ (Krep : Set (Fin N → ℝ)) := by
    intro y hy
    refine ⟨1, fun _ => y, fun _ => (1 : ℝ), ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      simpa using hy
    · intro i
      fin_cases i
      norm_num
    · simp
  have hsubset' :
      (ConvexCone.hull ℝ S : Set (Fin N → ℝ)) ⊆ (Krep : Set (Fin N → ℝ)) := by
    intro y hy
    exact (ConvexCone.hull_min (s := S) (C := Krep) hsubset) hy
  exact hsubset' hz

/-- Helper for Theorem 6.27.6: split a packed raw conic combination into upper and lower families
indexed by one common finite set, using zero weights on the inactive branch. -/
lemma helperForTheorem_6_27_6_splitRawConicCombination_into_upperLowerMasses
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    {z : Fin n → ℝ} {δ : ℝ}
    (hMem :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (z, δ), (0 : ℝ)) ∈
        ConvexCone.hull ℝ
          (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C)) :
    ∃ m : ℕ, ∃ p q : Fin m → (Fin n → ℝ) × ℝ, ∃ lam mu : Fin m → ℝ,
      (∀ i, p i ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h) ∧
      (∀ i, q i ∈ constrainedMinimumAuxiliarySet h C) ∧
      (∀ i, 0 ≤ lam i) ∧ (∀ i, 0 ≤ mu i) ∧
      z = ∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1 ∧
      δ = ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2 ∧
      ∑ i, lam i = ∑ i, mu i := by
  classical
  let packUpper : ((Fin n → ℝ) × ℝ) → Fin (n + 2) → ℝ := fun r =>
    prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ))
  let packLower : ((Fin n → ℝ) × ℝ) → Fin (n + 2) → ℝ := fun r =>
    prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ))
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  rcases helperForTheorem_6_27_6_mem_hull_imp_exists_conicCombination
      (S := helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) hMem with
    ⟨m, v, c, hv, hc_nonneg, hsum⟩
  let branch :
      ∀ i : Fin m,
        Sum
          {r : (Fin n → ℝ) × ℝ //
            r ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h ∧ v i = packUpper r}
          {r : (Fin n → ℝ) × ℝ //
            r ∈ constrainedMinimumAuxiliarySet h C ∧ v i = packLower r} :=
    fun i =>
      if hUpper :
          ∃ r ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h, v i = packUpper r then
        Sum.inl
          ⟨Classical.choose hUpper, (Classical.choose_spec hUpper).1,
            (Classical.choose_spec hUpper).2⟩
      else
        let hLower : ∃ r ∈ constrainedMinimumAuxiliarySet h C, v i = packLower r := by
          rcases hv i with hU | hL
          · exact False.elim (hUpper hU)
          · exact hL
        Sum.inr
          ⟨Classical.choose hLower, (Classical.choose_spec hLower).1,
            (Classical.choose_spec hLower).2⟩
  let p : Fin m → (Fin n → ℝ) × ℝ := fun i =>
    match branch i with
    | Sum.inl r => r.1
    | Sum.inr _ => (xBar, α)
  let q : Fin m → (Fin n → ℝ) × ℝ := fun i =>
    match branch i with
    | Sum.inl _ => (xBar, α)
    | Sum.inr r => r.1
  let lam : Fin m → ℝ := fun i =>
    match branch i with
    | Sum.inl _ => c i
    | Sum.inr _ => 0
  let mu : Fin m → ℝ := fun i =>
    match branch i with
    | Sum.inl _ => 0
    | Sum.inr _ => c i
  have hp : ∀ i, p i ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h := by
    intro i
    -- On an upper branch we keep the original epigraph point; otherwise we use the contact point.
    unfold p
    cases hbi : branch i with
    | inl r =>
        simpa [hbi] using r.2.1
    | inr r =>
        simpa [hbi] using hContactEpi
  have hq : ∀ i, q i ∈ constrainedMinimumAuxiliarySet h C := by
    intro i
    -- On a lower branch we keep the original auxiliary point; otherwise we use the contact point.
    unfold q
    cases hbi : branch i with
    | inl r =>
        simpa [hbi] using hContactAux
    | inr r =>
        simpa [hbi] using r.2.1
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    -- The split keeps the original nonnegative weight on upper generators and zero otherwise.
    unfold lam
    cases hbi : branch i with
    | inl r =>
        simpa [hbi] using hc_nonneg i
    | inr r =>
        simp [hbi]
  have hmu : ∀ i, 0 ≤ mu i := by
    intro i
    -- The split keeps the original nonnegative weight on lower generators and zero otherwise.
    unfold mu
    cases hbi : branch i with
    | inl r =>
        simp [hbi]
    | inr r =>
        simpa [hbi] using hc_nonneg i
  have hterm :
      ∀ i,
        c i • v i =
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n)
              (lam i • (p i).1 - mu i • (q i).1,
                lam i * (p i).2 - mu i * (q i).2),
              lam i - mu i) := by
    intro i
    -- Each packed generator contributes exactly one signed upper/lower term after the split.
    cases hbi : branch i with
    | inl r =>
        rcases r with ⟨r, hrMem, hrEq⟩
        calc
          c i • v i = c i • packUpper r := by rw [hrEq]
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (c i • (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ))) := by
                  symm
                  simpa [packUpper] using
                    ((prodLinearEquiv_append_coord (n := n + 1)).map_smul
                      (c i) (prodLinearEquiv_append_coord (n := n) (r.1, r.2), (1 : ℝ)))
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (c i • prodLinearEquiv_append_coord (n := n) (r.1, r.2), c i) := by
                  simp [smul_eq_mul]
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (prodLinearEquiv_append_coord (n := n) (c i • r.1, c i * r.2), c i) := by
                  apply congrArg
                    (fun x => prodLinearEquiv_append_coord (n := n + 1) (x, c i))
                  -- Rewrite the horizontal block using linearity of the inner packing map.
                  change c i • prodLinearEquiv_append_coord (n := n) (r.1, r.2) =
                    prodLinearEquiv_append_coord (n := n) (c i • (r.1, r.2))
                  symm
                  exact (prodLinearEquiv_append_coord (n := n)).map_smul (c i) (r.1, r.2)
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (prodLinearEquiv_append_coord (n := n)
                  (lam i • (p i).1 - mu i • (q i).1,
                    lam i * (p i).2 - mu i * (q i).2),
                  lam i - mu i) := by
                    simp [packUpper, p, q, lam, mu, hbi]
    | inr r =>
        rcases r with ⟨r, hrMem, hrEq⟩
        calc
          c i • v i = c i • packLower r := by rw [hrEq]
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (c i • (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ))) := by
                  symm
                  simpa [packLower] using
                    ((prodLinearEquiv_append_coord (n := n + 1)).map_smul
                      (c i) (prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), (-1 : ℝ)))
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (c i • prodLinearEquiv_append_coord (n := n) (-r.1, -r.2), -c i) := by
                  simp [smul_eq_mul]
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (prodLinearEquiv_append_coord (n := n) (-(c i • r.1), -(c i * r.2)), -c i) := by
                  apply congrArg
                    (fun x => prodLinearEquiv_append_coord (n := n + 1) (x, -c i))
                  -- The lower generator is the negative of an auxiliary point, so the same
                  -- linearity argument applies after pushing the minus sign into the packed pair.
                  simpa [smul_eq_mul, smul_neg] using
                    ((prodLinearEquiv_append_coord (n := n)).map_smul (c i) (-r.1, -r.2)).symm
          _ =
              prodLinearEquiv_append_coord (n := n + 1)
                (prodLinearEquiv_append_coord (n := n)
                  (lam i • (p i).1 - mu i • (q i).1,
                    lam i * (p i).2 - mu i * (q i).2),
                  lam i - mu i) := by
                    simp [packLower, p, q, lam, mu, hbi]
  have hpacked :
      ∑ i, c i • v i =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n)
            (∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1,
              ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2),
            ∑ i, lam i - ∑ i, mu i) := by
    -- Sum the split single-generator identities and regroup the linear coordinates.
    calc
      ∑ i, c i • v i
          = ∑ i,
              prodLinearEquiv_append_coord (n := n + 1)
                (prodLinearEquiv_append_coord (n := n)
                  (lam i • (p i).1 - mu i • (q i).1,
                    lam i * (p i).2 - mu i * (q i).2),
                  lam i - mu i) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    exact hterm i
      _ =
          prodLinearEquiv_append_coord (n := n + 1)
            (∑ i,
              (prodLinearEquiv_append_coord (n := n)
                (lam i • (p i).1 - mu i • (q i).1,
                  lam i * (p i).2 - mu i * (q i).2),
                lam i - mu i)) := by
                  symm
                  exact map_sum (prodLinearEquiv_append_coord (n := n + 1)).toLinearMap
                    (fun i =>
                      (prodLinearEquiv_append_coord (n := n)
                        (lam i • (p i).1 - mu i • (q i).1,
                          lam i * (p i).2 - mu i * (q i).2),
                        lam i - mu i))
                    (Finset.univ : Finset (Fin m))
      _ =
          prodLinearEquiv_append_coord (n := n + 1)
            ((∑ i,
                prodLinearEquiv_append_coord (n := n)
                  (lam i • (p i).1 - mu i • (q i).1,
                    lam i * (p i).2 - mu i * (q i).2)),
              ∑ i, (lam i - mu i)) := by
                refine congrArg (prodLinearEquiv_append_coord (n := n + 1)) ?_
                refine Prod.ext ?_ ?_
                · -- The first outer coordinate collects the packed horizontal/vertical blocks.
                  simpa using
                    (Prod.fst_sum (s := (Finset.univ : Finset (Fin m)))
                      (f := fun i =>
                        (prodLinearEquiv_append_coord (n := n)
                          (lam i • (p i).1 - mu i • (q i).1,
                            lam i * (p i).2 - mu i * (q i).2),
                          lam i - mu i)))
                · -- The last coordinate records the common signed mass.
                  simpa using
                    (Prod.snd_sum (s := (Finset.univ : Finset (Fin m)))
                      (f := fun i =>
                        (prodLinearEquiv_append_coord (n := n)
                          (lam i • (p i).1 - mu i • (q i).1,
                            lam i * (p i).2 - mu i * (q i).2),
                          lam i - mu i)))
      _ =
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n)
              (∑ i, (lam i • (p i).1 - mu i • (q i).1),
                ∑ i, (lam i * (p i).2 - mu i * (q i).2)),
              ∑ i, (lam i - mu i)) := by
                let g : Fin m → (Fin n → ℝ) × ℝ := fun i =>
                  (lam i • (p i).1 - mu i • (q i).1,
                    lam i * (p i).2 - mu i * (q i).2)
                refine congrArg
                  (fun x =>
                    prodLinearEquiv_append_coord (n := n + 1) (x, ∑ i, (lam i - mu i))) ?_
                have hpair :
                    (∑ i, (lam i • (p i).1 - mu i • (q i).1),
                      ∑ i, (lam i * (p i).2 - mu i * (q i).2)) =
                      ∑ i, g i := by
                  refine Prod.ext ?_ ?_
                  · -- The first component is the sum of the horizontal defects.
                    simpa [g] using
                      (Prod.fst_sum (s := (Finset.univ : Finset (Fin m))) (f := g)).symm
                  · -- The second component is the sum of the vertical defects.
                    simpa [g] using
                      (Prod.snd_sum (s := (Finset.univ : Finset (Fin m))) (f := g)).symm
                rw [hpair]
                symm
                exact map_sum (prodLinearEquiv_append_coord (n := n)).toLinearMap g
                  (Finset.univ : Finset (Fin m))
      _ =
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n)
              (∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1,
                ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2),
              ∑ i, lam i - ∑ i, mu i) := by
                congr 1 <;> simp [Finset.sum_sub_distrib]
  have hEqPacked :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (z, δ), (0 : ℝ)) =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n)
            (∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1,
              ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2),
            ∑ i, lam i - ∑ i, mu i) := by
    -- Compare the original packed sum with its split-and-regrouped form.
    calc
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (z, δ), (0 : ℝ))
          = ∑ i, c i • v i := hsum
      _ =
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n)
            (∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1,
              ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2),
            ∑ i, lam i - ∑ i, mu i) := hpacked
  have hOuter :=
    (prodLinearEquiv_append_coord (n := n + 1)).injective hEqPacked
  have hFirst :
      prodLinearEquiv_append_coord (n := n) (z, δ) =
        prodLinearEquiv_append_coord (n := n)
          (∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1,
            ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2) := by
    simpa using congrArg Prod.fst hOuter
  have hSecond :
      (0 : ℝ) = ∑ i, lam i - ∑ i, mu i := by
    simpa using congrArg Prod.snd hOuter
  have hCoords := (prodLinearEquiv_append_coord (n := n)).injective hFirst
  refine ⟨m, p, q, lam, mu, hp, hq, hlam, hmu, ?_, ?_, ?_⟩
  · simpa using congrArg Prod.fst hCoords
  · simpa using congrArg Prod.snd hCoords
  · linarith

/-- Helper for Theorem 6.27.6: a raw zero-balance cone point comes from one common mass times an
epigraph point minus an auxiliary point. -/
lemma helperForTheorem_6_27_6_rawZeroBalanceHullPoint_decomposes_with_commonMass
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCconvex : Convex ℝ C)
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal))
    {z : Fin n → ℝ} {δ : ℝ}
    (hMem :
      prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (z, δ), (0 : ℝ)) ∈
        ConvexCone.hull ℝ
          (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C)) :
    ∃ τ : ℝ, 0 ≤ τ ∧
      ∃ p : (Fin n → ℝ) × ℝ, p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h ∧
      ∃ q : (Fin n → ℝ) × ℝ, q ∈ constrainedMinimumAuxiliarySet h C ∧
        z = τ • (p.1 - q.1) ∧ δ = τ * (p.2 - q.2) := by
  classical
  have hContactEpi :
      (xBar, α) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
    helperForTheorem_6_27_6_contactPoint_mem_epigraph (h := h) α hxBar
  have hContactAux :
      (xBar, α) ∈ constrainedMinimumAuxiliarySet h C :=
    helperForTheorem_6_27_6_contactPoint_mem_auxiliarySet
      (h := h) (C := C) α hxBarC hα_lower hxBar
  rcases helperForTheorem_6_27_6_splitRawConicCombination_into_upperLowerMasses
      (h := h) (C := C) α hxBarC hα_lower hxBar hMem with
    ⟨m, p, q, lam, mu, hp, hq, hlam, hmu, hzEq, hδEq, hMassEq⟩
  let τ : ℝ := ∑ i, lam i
  have hτ_nonneg : 0 ≤ τ := by
    -- The common mass is the sum of nonnegative upper weights.
    exact Finset.sum_nonneg (fun i hi => hlam i)
  refine ⟨τ, hτ_nonneg, ?_⟩
  by_cases hτ_zero : τ = 0
  · -- Zero common mass forces every coefficient to vanish, so the contact pair works on both sides.
    have hlam_zero_univ :
        ∀ i ∈ (Finset.univ : Finset (Fin m)), lam i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hlam i)).1 hτ_zero
    have hlam_zero : ∀ i, lam i = 0 := by
      intro i
      exact hlam_zero_univ i (by simp)
    have hmu_sum_zero : ∑ i, mu i = 0 := by
      have hμsum : ∑ i, mu i = τ := by
        simpa [τ] using hMassEq.symm
      rw [hμsum, hτ_zero]
    have hmu_zero_univ :
        ∀ i ∈ (Finset.univ : Finset (Fin m)), mu i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hmu i)).1 hmu_sum_zero
    have hmu_zero : ∀ i, mu i = 0 := by
      intro i
      exact hmu_zero_univ i (by simp)
    have hz_zero : z = 0 := by
      calc
        z = ∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1 := hzEq
        _ = (0 : Fin n → ℝ) - 0 := by simp [hlam_zero, hmu_zero]
        _ = 0 := by simp
    have hδ_zero : δ = 0 := by
      calc
        δ = ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2 := hδEq
        _ = 0 - 0 := by simp [hlam_zero, hmu_zero]
        _ = 0 := by ring
    refine ⟨(xBar, α), hContactEpi, (xBar, α), hContactAux, ?_, ?_⟩
    · simpa [τ, hτ_zero, hz_zero]
    · simpa [τ, hτ_zero, hδ_zero]
  · -- Positive common mass lets us normalize the finite families into two barycenters.
    have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ_zero)
    have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
    have hμsum : ∑ i, mu i = τ := by
      simpa [τ] using hMassEq.symm
    let wlam : Fin m → ℝ := fun i => lam i / τ
    let wmu : Fin m → ℝ := fun i => mu i / τ
    have hwlam_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ wlam i := by
      intro i hi
      exact div_nonneg (hlam i) hτ_nonneg
    have hwmu_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ wmu i := by
      intro i hi
      exact div_nonneg (hmu i) hτ_nonneg
    have hwlam_sum : ∑ i, wlam i = 1 := by
      calc
        ∑ i, wlam i = ∑ i, lam i * τ⁻¹ := by
          simp [wlam, div_eq_mul_inv]
        _ = (∑ i, lam i) * τ⁻¹ := by
          rw [Finset.sum_mul]
        _ = τ * τ⁻¹ := by simp [τ]
        _ = 1 := by field_simp [hτ_ne]
    have hwmu_sum : ∑ i, wmu i = 1 := by
      calc
        ∑ i, wmu i = ∑ i, mu i * τ⁻¹ := by
          simp [wmu, div_eq_mul_inv]
        _ = (∑ i, mu i) * τ⁻¹ := by
          rw [Finset.sum_mul]
        _ = τ * τ⁻¹ := by simp [hμsum]
        _ = 1 := by field_simp [hτ_ne]
    have hEpiConvex : Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) h) := by
      simpa [ConvexFunctionOn] using
        (hproper.1 : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    have hAuxEq :
        constrainedMinimumAuxiliarySet h C = {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} :=
      helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
        (h := h) (C := C) α hxBarC hα_lower hxBar
    have hAuxProd :
        {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} = C ×ˢ Set.Iic α := by
      ext r
      simp
    have hAuxConv : Convex ℝ (constrainedMinimumAuxiliarySet h C) := by
      rw [hAuxEq, hAuxProd]
      exact hCconvex.prod (convex_Iic α)
    let pBar : (Fin n → ℝ) × ℝ := ∑ i, wlam i • p i
    let qBar : (Fin n → ℝ) × ℝ := ∑ i, wmu i • q i
    have hpBar :
        pBar ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) h :=
      hEpiConvex.sum_mem (t := Finset.univ) (w := wlam) (z := p) hwlam_nonneg hwlam_sum
        (by intro i hi; exact hp i)
    have hqBar :
        qBar ∈ constrainedMinimumAuxiliarySet h C :=
      hAuxConv.sum_mem (t := Finset.univ) (w := wmu) (z := q) hwmu_nonneg hwmu_sum
        (by intro i hi; exact hq i)
    have hpBar_fst : pBar.1 = ∑ i, wlam i • (p i).1 := by
      -- Read off the horizontal coordinate of the weighted epigraph barycenter.
      simpa [pBar] using
        (Prod.fst_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i => wlam i • p i))
    have hqBar_fst : qBar.1 = ∑ i, wmu i • (q i).1 := by
      -- The same coordinate formula holds for the auxiliary barycenter.
      simpa [qBar] using
        (Prod.fst_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i => wmu i • q i))
    have hpBar_snd : pBar.2 = ∑ i, wlam i * (p i).2 := by
      -- The vertical coordinate is the weighted sum of the original heights.
      simpa [pBar, smul_eq_mul] using
        (Prod.snd_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i => wlam i • p i))
    have hqBar_snd : qBar.2 = ∑ i, wmu i * (q i).2 := by
      -- The auxiliary heights average in the same way.
      simpa [qBar, smul_eq_mul] using
        (Prod.snd_sum (s := (Finset.univ : Finset (Fin m))) (f := fun i => wmu i • q i))
    have hτp₁ : τ • pBar.1 = ∑ i, lam i • (p i).1 := by
      calc
        τ • pBar.1 = τ • ∑ i, wlam i • (p i).1 := by rw [hpBar_fst]
        _ = ∑ i, τ • (wlam i • (p i).1) := by
              simpa using
                (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
                  (f := fun i => wlam i • (p i).1) (r := τ))
        _ = ∑ i, lam i • (p i).1 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hscale : τ * wlam i = lam i := by
                calc
                  τ * wlam i = τ * (lam i / τ) := by rfl
                  _ = lam i := by field_simp [hτ_ne]
              calc
                τ • (wlam i • (p i).1) = (τ * wlam i) • (p i).1 := by simp [smul_smul]
                _ = lam i • (p i).1 := by rw [hscale]
    have hτq₁ : τ • qBar.1 = ∑ i, mu i • (q i).1 := by
      calc
        τ • qBar.1 = τ • ∑ i, wmu i • (q i).1 := by rw [hqBar_fst]
        _ = ∑ i, τ • (wmu i • (q i).1) := by
              simpa using
                (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
                  (f := fun i => wmu i • (q i).1) (r := τ))
        _ = ∑ i, mu i • (q i).1 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hscale : τ * wmu i = mu i := by
                calc
                  τ * wmu i = τ * (mu i / τ) := by rfl
                  _ = mu i := by field_simp [hτ_ne]
              calc
                τ • (wmu i • (q i).1) = (τ * wmu i) • (q i).1 := by simp [smul_smul]
                _ = mu i • (q i).1 := by rw [hscale]
    have hτp₂ : τ * pBar.2 = ∑ i, lam i * (p i).2 := by
      calc
        τ * pBar.2 = τ * ∑ i, wlam i * (p i).2 := by rw [hpBar_snd]
        _ = ∑ i, τ * (wlam i * (p i).2) := by rw [Finset.mul_sum]
        _ = ∑ i, lam i * (p i).2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hscale : τ * wlam i = lam i := by
                calc
                  τ * wlam i = τ * (lam i / τ) := by rfl
                  _ = lam i := by field_simp [hτ_ne]
              calc
                τ * (wlam i * (p i).2) = (τ * wlam i) * (p i).2 := by ring
                _ = lam i * (p i).2 := by rw [hscale]
    have hτq₂ : τ * qBar.2 = ∑ i, mu i * (q i).2 := by
      calc
        τ * qBar.2 = τ * ∑ i, wmu i * (q i).2 := by rw [hqBar_snd]
        _ = ∑ i, τ * (wmu i * (q i).2) := by rw [Finset.mul_sum]
        _ = ∑ i, mu i * (q i).2 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hscale : τ * wmu i = mu i := by
                calc
                  τ * wmu i = τ * (mu i / τ) := by rfl
                  _ = mu i := by field_simp [hτ_ne]
              calc
                τ * (wmu i * (q i).2) = (τ * wmu i) * (q i).2 := by ring
                _ = mu i * (q i).2 := by rw [hscale]
    refine ⟨pBar, hpBar, qBar, hqBar, ?_, ?_⟩
    · calc
        z = ∑ i, lam i • (p i).1 - ∑ i, mu i • (q i).1 := hzEq
        _ = τ • pBar.1 - τ • qBar.1 := by rw [hτp₁, hτq₁]
        _ = τ • (pBar.1 - qBar.1) := by simp [smul_sub]
    · calc
        δ = ∑ i, lam i * (p i).2 - ∑ i, mu i * (q i).2 := hδEq
        _ = τ * pBar.2 - τ * qBar.2 := by rw [hτp₂, hτq₂]
        _ = τ * (pBar.2 - qBar.2) := by ring

/-- Helper for Theorem 6.27.6: a raw zero-balance cone point can only have nonnegative vertical
gap. -/
lemma helperForTheorem_6_27_6_rawZeroBalancePoint_yields_nonnegativeGap
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    ∀ {δ : ℝ},
      helperForTheorem_6_27_6_encodedZeroBalancePoint (n := n) δ ∈
          ConvexCone.hull ℝ
            (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) →
        0 ≤ δ := by
  intro δ hMem
  have hDecomp :=
    helperForTheorem_6_27_6_rawZeroBalanceHullPoint_decomposes_with_commonMass
      (h := h) (C := C) hproper hCconvex α hxBarC hα_lower hxBar
      (z := 0) (δ := δ)
      (by simpa [helperForTheorem_6_27_6_encodedZeroBalancePoint] using hMem)
  rcases hDecomp with ⟨τ, hτ_nonneg, p, hp, q, hq, hZero, hGapEq⟩
  by_cases hτ_zero : τ = 0
  · -- Zero common mass forces the vertical gap to vanish as well.
    rw [hτ_zero] at hGapEq
    linarith
  · have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ_zero)
    have hpEqq : p.1 = q.1 := by
      have hScaled :
          τ • (p.1 - q.1) = (0 : Fin n → ℝ) := by
        simpa using hZero.symm
      exact sub_eq_zero.mp ((smul_eq_zero.mp hScaled).resolve_left hτ_zero)
    have hpEpi : h p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
    have hAuxEq :
        constrainedMinimumAuxiliarySet h C = {r : (Fin n → ℝ) × ℝ | r.1 ∈ C ∧ r.2 ≤ α} :=
      helperForTheorem_6_27_6_auxiliarySet_eq_textbookForm
        (h := h) (C := C) α hxBarC hα_lower hxBar
    have hqTextbook : q.1 ∈ C ∧ q.2 ≤ α := by
      simpa [hAuxEq] using hq
    have hqLeP_ereal : ((q.2 : ℝ) : EReal) ≤ ((p.2 : ℝ) : EReal) := by
      calc
        ((q.2 : ℝ) : EReal) ≤ ((α : ℝ) : EReal) := by
          exact_mod_cast hqTextbook.2
        _ ≤ h q.1 := hα_lower q.1 hqTextbook.1
        _ ≤ h p.1 := by simpa [hpEqq]
        _ ≤ (p.2 : EReal) := hpEpi
    have hqLeP : q.2 ≤ p.2 := by
      exact_mod_cast hqLeP_ereal
    have hGapNonneg : 0 ≤ p.2 - q.2 := sub_nonneg.mpr hqLeP
    have hτgap_nonneg : 0 ≤ τ * (p.2 - q.2) := mul_nonneg hτ_nonneg hGapNonneg
    simpa [hGapEq] using hτgap_nonneg

/-- Helper for Theorem 6.27.6: the raw cone route excludes the packed negative vertical vector
from the encoded separator cone. -/
lemma helperForTheorem_6_27_6_negativeVertical_not_mem_encodedSeparatorCone
    {n : ℕ} (h : (Fin n → ℝ) → EReal) (C : Set (Fin n → ℝ))
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hCne : Set.Nonempty C) (hCclosed : IsClosed C) (hCconvex : Convex ℝ C)
    (α : ℝ) {xBar : Fin n → ℝ} (hxBarC : xBar ∈ C)
    (hα_lower : ∀ x ∈ C, (α : EReal) ≤ h x) (hxBar : h xBar = (α : EReal)) :
    helperForTheorem_6_27_6_encodedNegativeVerticalPoint (n := n) ∉
      (ConvexCone.hull ℝ
        (helperForTheorem_6_27_6_encodedSeparatorGeneratorSet h C) :
          Set (Fin (n + 2) → ℝ)) := by
  intro hMem
  -- Reduce the forbidden vector to the exact raw zero-balance statement with `δ = -1`.
  have hNonneg :
      0 ≤ (-1 : ℝ) :=
    helperForTheorem_6_27_6_rawZeroBalancePoint_yields_nonnegativeGap
      (h := h) (C := C) hclosed hproper hCne hCclosed hCconvex α hxBarC hα_lower hxBar
      (by
        simpa [helperForTheorem_6_27_6_encodedZeroBalancePoint,
          helperForTheorem_6_27_6_encodedNegativeVerticalPoint] using hMem)
  linarith


end Section27
end Chap06
