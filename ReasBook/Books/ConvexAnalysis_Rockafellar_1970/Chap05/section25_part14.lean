/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part13

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Corollary 25.7.1: pointwise convergence on a finite set is eventually uniform on
that finite set. -/
lemma helperForCorollary_25_7_1_eventually_uniformOn_finite
    {α : Type*} {gSeq : ℕ → α → ℝ} {g : α → ℝ} {s : Finset α} {ε : ℝ} (hε : 0 < ε)
    (hpointwise :
      ∀ x ∈ s, Filter.Tendsto (fun i : ℕ => gSeq i x) Filter.atTop (nhds (g x))) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ s, |gSeq n x - g x| < ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty set has no points to control.
      exact Filter.Eventually.of_forall (by
        intro n x hx
        exact (Finset.notMem_empty x hx).elim)
  | @insert x s hx ih =>
      -- Control the newly inserted point and combine it with the induction hypothesis.
      have hxPointwise :
          Filter.Tendsto (fun i : ℕ => gSeq i x) Filter.atTop (nhds (g x)) :=
        hpointwise x (by simp)
      have hxEventually : ∀ᶠ n : ℕ in Filter.atTop, |gSeq n x - g x| < ε := by
        have hball : Metric.ball (g x) ε ∈ nhds (g x) := Metric.ball_mem_nhds (g x) hε
        simpa [Real.dist_eq] using hxPointwise.eventually hball
      have hsPointwise :
          ∀ y ∈ s, Filter.Tendsto (fun i : ℕ => gSeq i y) Filter.atTop (nhds (g y)) := by
        intro y hy
        exact hpointwise y (by simp [hy])
      filter_upwards [hxEventually, ih hsPointwise] with n hnx hns y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hnx
      · exact hns y hy'

/-- Helper for Corollary 25.7.1: on a compact interval, pointwise convergence of monotone scalar
functions to a continuous limit is automatically uniform. -/
lemma helperForCorollary_25_7_1_tendstoUniformlyOn_Icc_of_pointwise_tendsto_monotoneOn
    {gSeq : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmonoSeq : ∀ i : ℕ, MonotoneOn (gSeq i) (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hpointwise :
      ∀ x ∈ Set.Icc a b,
        Filter.Tendsto (fun i : ℕ => gSeq i x) Filter.atTop (nhds (g x))) :
    TendstoUniformlyOn gSeq g Filter.atTop (Set.Icc a b) := by
  let K : Set ℝ := Set.Icc a b
  have hKcompact : IsCompact K := isCompact_Icc
  have huc : UniformContinuousOn g K := hKcompact.uniformContinuousOn_of_continuous hgcont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- First choose a spatial scale on which the limit function oscillates by less than `ε / 3`.
  have hεthirdpos : 0 < ε / 3 := by
    positivity
  rcases (Metric.uniformContinuousOn_iff.mp huc) (ε / 3) hεthirdpos with ⟨δ, hδpos, hδ⟩
  have hδhalf_pos : 0 < δ / 2 := by
    positivity
  rcases hKcompact.elim_nhds_subcover (fun x => Metric.ball x (δ / 2)) (by
      intro x hx
      exact Metric.ball_mem_nhds x hδhalf_pos) with ⟨t, htK, hcover⟩
  let L : ℝ → ℝ := fun y => max a (y - δ / 2)
  let R : ℝ → ℝ := fun y => min b (y + δ / 2)
  have hLmem : ∀ y ∈ t, L y ∈ K := by
    intro y hy
    have hyK : y ∈ K := htK y hy
    have hδhalf_nonneg : 0 ≤ δ / 2 := by
      positivity
    constructor
    · exact le_max_left _ _
    · refine max_le_iff.2 ?_
      constructor
      · exact hab
      · have hsub : y - δ / 2 ≤ y := by
          linarith
        exact hsub.trans hyK.2
  have hRmem : ∀ y ∈ t, R y ∈ K := by
    intro y hy
    have hyK : y ∈ K := htK y hy
    have hδhalf_nonneg : 0 ≤ δ / 2 := by
      positivity
    constructor
    · refine le_min_iff.2 ?_
      constructor
      · exact hab
      · have hadd : y ≤ y + δ / 2 := by
          linarith
        exact hyK.1.trans hadd
    · exact min_le_left _ _
  let sPts : Finset ℝ := t.image L ∪ t.image R
  have hsMem : ∀ z ∈ sPts, z ∈ K := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzL | hzR
    · rcases Finset.mem_image.mp hzL with ⟨y, hyt, rfl⟩
      exact hLmem y hyt
    · rcases Finset.mem_image.mp hzR with ⟨y, hyt, rfl⟩
      exact hRmem y hyt
  have hendpointEventually :
      ∀ᶠ n : ℕ in Filter.atTop, ∀ z ∈ sPts, |gSeq n z - g z| < ε / 3 :=
    -- Only finitely many clipped endpoints appear, so the new finite-set helper applies.
    helperForCorollary_25_7_1_eventually_uniformOn_finite hεthirdpos (fun z hz =>
      hpointwise z (hsMem z hz))
  filter_upwards [hendpointEventually] with n hn x hx
  have hxK : x ∈ K := by
    simpa [K] using hx
  have hxCover : ∃ y ∈ t, x ∈ Metric.ball y (δ / 2) := by
    simpa [K, Set.mem_iUnion] using hcover hxK
  rcases hxCover with ⟨y, hyt, hxy⟩
  have hyK : y ∈ K := htK y hyt
  have hxyAbs : |x - y| < δ / 2 := by
    simpa [Real.dist_eq] using hxy
  have hxyLeft : y - δ / 2 < x := by
    have hAbsLeft := (abs_lt.mp hxyAbs).1
    linarith
  have hxyRight : x < y + δ / 2 := by
    have hAbsRight := (abs_lt.mp hxyAbs).2
    linarith
  have hLx : L y ≤ x := by
    -- The left endpoint of the covering interval lies to the left of `x`.
    refine max_le_iff.2 ?_
    constructor
    · exact hxK.1
    · exact hxyLeft.le
  have hxR : x ≤ R y := by
    -- The right endpoint of the covering interval lies to the right of `x`.
    refine le_min_iff.2 ?_
    constructor
    · exact hxK.2
    · exact hxyRight.le
  have hdistL : dist x (L y) < δ := by
    -- Both `x` and the clipped left endpoint stay within one `δ`-window.
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hLx)]
    have hLy : y - δ / 2 ≤ L y := le_max_right _ _
    linarith
  have hdistR : dist x (R y) < δ := by
    -- The same estimate holds for the clipped right endpoint.
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxR)]
    have hRy : R y ≤ y + δ / 2 := min_le_right _ _
    linarith
  have hLmemY : L y ∈ K := hLmem y hyt
  have hRmemY : R y ∈ K := hRmem y hyt
  have hdistL' : dist (L y) x < δ := by
    simpa [dist_comm] using hdistL
  have hdistR' : dist (R y) x < δ := by
    simpa [dist_comm] using hdistR
  have hLg : dist (g (L y)) (g x) < ε / 3 :=
    hδ (L y) hLmemY x hxK hdistL'
  have hRg : dist (g (R y)) (g x) < ε / 3 :=
    hδ (R y) hRmemY x hxK hdistR'
  have hLyMem : L y ∈ sPts := by
    have hLyImage : L y ∈ t.image L := Finset.mem_image.mpr ⟨y, hyt, rfl⟩
    exact Finset.mem_union.mpr (Or.inl hLyImage)
  have hRyMem : R y ∈ sPts := by
    have hRyImage : R y ∈ t.image R := Finset.mem_image.mpr ⟨y, hyt, rfl⟩
    exact Finset.mem_union.mpr (Or.inr hRyImage)
  have hleftLower : g (L y) - ε / 3 < gSeq n (L y) := by
    -- The eventual endpoint control converts absolute error into a one-sided lower bound.
    have hAbsLeft := (abs_lt.mp (hn (L y) hLyMem)).1
    linarith
  have hrightUpper : gSeq n (R y) < g (R y) + ε / 3 := by
    -- The right endpoint gives the matching one-sided upper bound.
    have hAbsRight := (abs_lt.mp (hn (R y) hRyMem)).2
    linarith
  have hxLower : g x - ε < gSeq n x := by
    -- Monotonicity squeezes `gSeq n x` below from the left endpoint, while continuity of `g`
    -- keeps `g x` close to `g (L y)`.
    have hLg' : |g (L y) - g x| < ε / 3 := by
      simpa [Real.dist_eq] using hLg
    have hLgLower := (abs_lt.mp hLg').1
    have hLgToLeft : g x - ε / 3 < g (L y) := by
      linarith
    have hLowerAtL : g x - 2 * ε / 3 < gSeq n (L y) := by
      linarith
    have hmono := hmonoSeq n hLmemY hxK hLx
    linarith
  have hxUpper : gSeq n x < g x + ε := by
    -- The same squeeze from the right endpoint controls the upper error.
    have hRg' : |g (R y) - g x| < ε / 3 := by
      simpa [Real.dist_eq] using hRg
    have hRgUpper := (abs_lt.mp hRg').2
    have hRgToRight : g (R y) < g x + ε / 3 := by
      linarith
    have hUpperAtR : gSeq n (R y) < g x + 2 * ε / 3 := by
      linarith
    have hmono := hmonoSeq n hxK hRmemY hxR
    linarith
  have habs : |gSeq n x - g x| < ε := by
    refine abs_lt.mpr ?_
    constructor <;> linarith
  simpa [Real.dist_eq, abs_sub_comm] using habs

/-- Corollary 25.7.1: let `I ⊆ ℝ` be an open interval, encoded here as an open convex set. If
`f` and the sequence `f_i` are finite convex functions on `I`, each differentiable on `I`, and
`f_i t → f t` for every `t ∈ I`, then `deriv (f_i) t → deriv f t` for every `t ∈ I`. Moreover,
for every closed bounded subinterval `Set.Icc a b ⊆ I`, the convergence of the derivatives is
uniform on `Set.Icc a b`. -/
theorem convexOn_openInterval_tendsto_deriv_and_tendstoUniformlyOn_Icc_of_pointwise_convergent
    {I : Set ℝ} {f : ℝ → ℝ} (fSeq : ℕ → ℝ → ℝ)
    (hIopen : IsOpen I) (hIconv : Convex ℝ I) (hf : ConvexOn ℝ I f)
    (hfdiff : DifferentiableOn ℝ f I)
    (hSeqConvex : ∀ i : ℕ, ConvexOn ℝ I (fSeq i))
    (hSeqDiff : ∀ i : ℕ, DifferentiableOn ℝ (fSeq i) I)
    (hpointwise :
      ∀ t : ℝ, t ∈ I →
        Filter.Tendsto (fun i : ℕ => fSeq i t) Filter.atTop (nhds (f t))) :
    (∀ t : ℝ, t ∈ I →
      Filter.Tendsto (fun i : ℕ => deriv (fSeq i) t) Filter.atTop (nhds (deriv f t))) ∧
      ∀ ⦃a b : ℝ⦄, a ≤ b → Set.Icc a b ⊆ I →
        TendstoUniformlyOn (fun i t => deriv (fSeq i) t) (deriv f) Filter.atTop (Set.Icc a b) :=
  by
  constructor
  · -- The pointwise statement is exactly the one-dimensional specialization of Theorem 25.7.
    exact
      helperForCorollary_25_7_1_pointwise_deriv_tendsto_of_theorem_25_7
        (fSeq := fSeq) hIopen hIconv hf hfdiff hSeqConvex hSeqDiff hpointwise
  · intro a b hab hIcc
    -- Theorem 25.3 gives continuity and monotonicity of the limit derivative on the compact
    -- interval, and likewise for every approximating derivative.
    have hfRegular :
        ContinuousOn (deriv f) (Set.Icc a b) ∧ MonotoneOn (deriv f) (Set.Icc a b) :=
      helperForCorollary_25_7_1_deriv_continuousOn_Icc_and_monotoneOn
        hIopen hIconv hf hfdiff hab hIcc
    have hSeqMono :
        ∀ i : ℕ, MonotoneOn (deriv (fSeq i)) (Set.Icc a b) := by
      intro i
      exact
        (helperForCorollary_25_7_1_deriv_continuousOn_Icc_and_monotoneOn
          hIopen hIconv (hSeqConvex i) (hSeqDiff i) hab hIcc).2
    have hpointwiseDeriv :
        ∀ x ∈ Set.Icc a b,
          Filter.Tendsto (fun i : ℕ => deriv (fSeq i) x) Filter.atTop (nhds (deriv f x)) := by
      intro x hx
      have hxI : x ∈ I := hIcc hx
      exact
        helperForCorollary_25_7_1_pointwise_deriv_tendsto_of_theorem_25_7
          (fSeq := fSeq) hIopen hIconv hf hfdiff hSeqConvex hSeqDiff hpointwise x hxI
    -- Monotonicity in the spatial variable upgrades the pointwise convergence to uniform
    -- convergence on the compact interval.
    exact
      helperForCorollary_25_7_1_tendstoUniformlyOn_Icc_of_pointwise_tendsto_monotoneOn
        hab hSeqMono hfRegular.1 hpointwiseDeriv

end Section25
end Chap05
