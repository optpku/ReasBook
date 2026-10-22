/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part8

section Chap06
section Section27

/-- Helper for Corollary 6.27.3: for a fixed affine line, the feasible scalar set
`{s | x + s • y ∈ C}` is a closed convex subset of `ℝ`, hence one of the standard closed
interval/ray cases. -/
lemma helperForCorollary_6_27_3_scalarFeasibleSet_intervalCases
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCpoly : IsPolyhedralConvexSet n C)
    (x y : Fin n → ℝ) :
    let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
    IsClosed T ∧ Convex ℝ T ∧
      (T = ∅ ∨ T = Set.Icc (sInf T) (sSup T) ∨ T = Set.Ici (sInf T) ∨
        T = Set.Iic (sSup T) ∨ T = Set.univ) := by
  let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
  have hCclosed : IsClosed C :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C) hCpoly
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTclosed : IsClosed T := by
    let L : ℝ → Fin n → ℝ := fun s => x + s • y
    have hcont : Continuous L := by
      continuity
    -- The line slice is the continuous preimage of the closed feasible set.
    simpa [T, L] using hCclosed.preimage hcont
  have hTconv : Convex ℝ T := by
    intro s hs t ht a b ha hb hab
    have hsC : x + s • y ∈ C := hs
    have htC : x + t • y ∈ C := ht
    have hcomb : a • (x + s • y) + b • (x + t • y) = x + (a • s + b • t) • y := by
      have hb' : b = 1 - a := by
        linarith
      subst b
      ext i
      simp [smul_eq_mul]
      ring
    have hmem : a • (x + s • y) + b • (x + t • y) ∈ C := hCconv hsC htC ha hb hab
    -- Convexity of `C` along the ambient line gives convexity of the scalar slice.
    change x + (a • s + b • t) • y ∈ C
    rw [← hcomb]
    exact hmem
  have hTpre : IsPreconnected T := hTconv.isPreconnected
  refine ⟨hTclosed, hTconv, ?_⟩
  by_cases hTempty : T = ∅
  · exact Or.inl hTempty
  · have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hTempty
    by_cases hBelow : BddBelow T <;> by_cases hAbove : BddAbove T
    · -- A nonempty bounded closed convex subset of `ℝ` is a closed interval.
      exact
        Or.inr (Or.inl
          (eq_Icc_csInf_csSup_of_connected_bdd_closed
            ⟨hTne, hTpre⟩ hBelow hAbove hTclosed))
    · have hsInfMem : sInf T ∈ T := hTclosed.csInf_mem hTne hBelow
      have hsubsetInterior : Set.Ioi (sInf T) ⊆ T := hTpre.Ioi_csInf_subset hBelow hAbove
      have hsubsetLeft : T ⊆ Set.Ici (sInf T) := by
        intro s hs
        exact csInf_le hBelow hs
      have hsubsetRight : Set.Ici (sInf T) ⊆ T := by
        intro s hs
        have hsle : sInf T ≤ s := hs
        rcases eq_or_lt_of_le hsle with hseq | hslt
        · simpa [hseq] using hsInfMem
        · exact hsubsetInterior hslt
      -- If the slice is unbounded above but bounded below, it is a closed ray.
      exact
        Or.inr (Or.inr (Or.inl
          (Set.Subset.antisymm hsubsetLeft hsubsetRight)))
    · have hsSupMem : sSup T ∈ T := hTclosed.csSup_mem hTne hAbove
      have hsubsetInterior : Set.Iio (sSup T) ⊆ T := hTpre.Iio_csSup_subset hBelow hAbove
      have hsubsetLeft : T ⊆ Set.Iic (sSup T) := by
        intro s hs
        exact le_csSup hAbove hs
      have hsubsetRight : Set.Iic (sSup T) ⊆ T := by
        intro s hs
        have hsle : s ≤ sSup T := hs
        rcases eq_or_lt_of_le hsle with hseq | hslt
        · simpa [hseq] using hsSupMem
        · exact hsubsetInterior hslt
      -- The symmetric case is a closed left ray.
      exact
        Or.inr (Or.inr (Or.inr (Or.inl
          (Set.Subset.antisymm hsubsetLeft hsubsetRight))))
    · -- If neither side is bounded, connectedness forces the whole line.
      exact Or.inr (Or.inr (Or.inr (Or.inr (hTpre.eq_univ_of_unbounded hBelow hAbove))))

/-- Helper for Corollary 6.27.3: if one affine line contains no feasible point where `h` is
finite, then the indicator extension is identically `⊤` on that line, so the line infimum is
attained trivially. -/
lemma helperForCorollary_6_27_3_scalarSlice_allTop_attainment
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ))
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (x y : Fin n → ℝ)
    (hNoFinite : ¬ ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal)) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  have hlineTop : ∀ s : ℝ, g (x + s • y) = (⊤ : EReal) := by
    intro s
    by_cases hsC : x + s • y ∈ C
    · -- On feasible points, the absence of finite values forces `h = ⊤`.
      have hsTop : h (x + s • y) = (⊤ : EReal) := by
        by_contra hsNotTop
        apply hNoFinite
        exact ⟨s, hsC, lt_top_iff_ne_top.mpr hsNotTop⟩
      simp [hg, indicatorFunction, hsC, hsTop]
    · -- Off the feasible slice, the indicator term is `⊤`, so the sum is `⊤`.
      have hsBot : h (x + s • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
      simp [hg, indicatorFunction, hsC, hsBot]
  refine ⟨0, ?_⟩
  apply le_antisymm
  · -- Since every value on the line is `⊤`, the chosen point is below the line infimum.
    refine le_iInf ?_
    intro s
    simp [hlineTop s]
  · -- The converse inequality is the universal bound `inf ≤ value at 0`.
    simpa [hlineTop 0] using (iInf_le (fun s : ℝ => g (x + s • y)) 0)

/-- Helper for Corollary 6.27.3: when the scalar feasible slice
`{s | x + s • y ∈ C}` is a bounded closed interval, compact lower-semicontinuous minimization on
that interval yields a linewise minimizer of the indicator extension. -/
lemma helperForCorollary_6_27_3_boundedScalarSlice_attainment
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ))
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) {a b : ℝ}
    (hT : {s : ℝ | x + s • y ∈ C} = Set.Icc a b)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal)) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  let φ : ℝ → EReal := fun s => g (x + s • y)
  rcases hFinite with ⟨s0, hs0C, hs0Top⟩
  have hs0Icc : s0 ∈ Set.Icc a b := by
    have hs0T : s0 ∈ {s : ℝ | x + s • y ∈ C} := by
      simpa using hs0C
    rw [hT] at hs0T
    exact hs0T
  have hφlsc : LowerSemicontinuous φ := by
    let L : ℝ → Fin n → ℝ := fun s => x + s • y
    have hcont : Continuous L := by
      continuity
    -- Restrict lower semicontinuity of `g` along the continuous affine line map.
    simpa [φ, L] using hgClosed.2.comp_continuous hcont
  obtain ⟨t, htIcc, htMin⟩ :=
    (hφlsc.lowerSemicontinuousOn (Set.Icc a b)).exists_isMinOn ⟨s0, hs0Icc⟩ isCompact_Icc
  refine ⟨t, ?_⟩
  apply le_antisymm
  · -- On the bounded feasible interval, `t` is minimal; off the interval, the indicator term
    -- forces the scalar restriction to be `⊤`.
    refine le_iInf ?_
    intro s
    by_cases hsC : x + s • y ∈ C
    · have hsIcc : s ∈ Set.Icc a b := by
        have hsT : s ∈ {s : ℝ | x + s • y ∈ C} := by
          simpa using hsC
        rw [hT] at hsT
        exact hsT
      exact (isMinOn_iff.mp htMin) s hsIcc
    · have hsBot : h (x + s • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
      simp [hg, indicatorFunction, hsC, hsBot]
  · -- Any line infimum is below the value at the minimizing parameter.
    exact iInf_le φ t

end Section27
end Chap06
