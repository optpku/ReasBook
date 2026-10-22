/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part15

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Corollary 35.7.1: membership in the split Euclidean closed ball controls the
`Pi`-norm of each coordinate component. -/
lemma helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall
    {m n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {du : Fin m → ℝ} {dv : Fin n → ℝ}
    (hmem :
      ((du, dv) : (Fin m → ℝ) × (Fin n → ℝ)) ∈
        splitEuclideanClosedBall (m := m) (n := n) r) :
    ‖du‖ ≤ r ∧ ‖dv‖ ≤ r := by
  classical
  -- Unpack the split-ball inequality.
  have hmem' :
      (∑ i : Fin m, du i ^ (2 : ℕ)) + ∑ j : Fin n, dv j ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
    simpa [splitEuclideanClosedBall] using hmem
  -- First coordinate: each term `du i^2` is bounded by the total sum, hence by `r^2`.
  have hdv_sum_nonneg : 0 ≤ ∑ j : Fin n, dv j ^ (2 : ℕ) := by
    exact Finset.sum_nonneg (fun j _ => sq_nonneg (dv j))
  have hsum_du_le :
      (∑ i : Fin m, du i ^ (2 : ℕ)) ≤ r ^ (2 : ℕ) := by
    exact le_trans (le_add_of_nonneg_right hdv_sum_nonneg) hmem'
  have hdu_coord : ∀ i : Fin m, ‖du i‖ ≤ r := by
    intro i
    have hterm_le_sum :
        du i ^ (2 : ℕ) ≤ ∑ k : Fin m, du k ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun k : Fin m => du k ^ (2 : ℕ))
        (fun k _ => sq_nonneg (du k)) (Finset.mem_univ i)
    have hsq : du i ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := le_trans hterm_le_sum hsum_du_le
    have habs : |du i| ≤ r := abs_le_of_sq_le_sq hsq hr
    simpa [Real.norm_eq_abs] using habs
  have hdu_norm : ‖du‖ ≤ r := (pi_norm_le_iff_of_nonneg hr).2 hdu_coord
  -- Second coordinate: symmetric argument.
  have hdu_sum_nonneg : 0 ≤ ∑ i : Fin m, du i ^ (2 : ℕ) := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (du i))
  have hsum_dv_le :
      (∑ j : Fin n, dv j ^ (2 : ℕ)) ≤ r ^ (2 : ℕ) := by
    -- `∑ dv^2 ≤ (∑ du^2) + (∑ dv^2) ≤ r^2`.
    exact le_trans (le_add_of_nonneg_left hdu_sum_nonneg) hmem'
  have hdv_coord : ∀ j : Fin n, ‖dv j‖ ≤ r := by
    intro j
    have hterm_le_sum :
        dv j ^ (2 : ℕ) ≤ ∑ k : Fin n, dv k ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun k : Fin n => dv k ^ (2 : ℕ))
        (fun k _ => sq_nonneg (dv k)) (Finset.mem_univ j)
    have hsq : dv j ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := le_trans hterm_le_sum hsum_dv_le
    have habs : |dv j| ≤ r := abs_le_of_sq_le_sq hsq hr
    simpa [Real.norm_eq_abs] using habs
  have hdv_norm : ‖dv‖ ≤ r := (pi_norm_le_iff_of_nonneg hr).2 hdv_coord
  exact ⟨hdu_norm, hdv_norm⟩

/-- Helper for Corollary 35.7.1: the first-variable `liminf` inequality from Theorem 35.7 implies
lower semicontinuity of `(u, v) ↦ K'(u, v; u', 0)` on `C ×ˢ D`. -/
lemma helperForCorollary_35_7_1_lowerSemicontinuousOn_firstDirectionalDerivative
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (u' : Fin m → ℝ) :
    LowerSemicontinuousOn
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        realFirstVariableDirectionalDerivativeValue K p.1 p.2 u')
      (C ×ˢ D) := by
  classical
  intro p hp a ha
  let s : Set ((Fin m → ℝ) × (Fin n → ℝ)) := C ×ˢ D
  -- Contradiction setup: if the strict lower bound `a < f p` does not hold eventually in `𝓝[s] p`,
  -- then we can extract a sequence in `s` converging to `p` whose values stay `≤ a`.
  by_contra hLower
  have hfreq_not_lt :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        ¬ a <
          realFirstVariableDirectionalDerivativeValue K q.1 q.2 u' :=
    Filter.not_eventually.1 hLower
  have hfreq :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        realFirstVariableDirectionalDerivativeValue K q.1 q.2 u' ≤ a := by
    exact hfreq_not_lt.mono (fun q hq => le_of_not_gt hq)
  have hfreq_mem :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        realFirstVariableDirectionalDerivativeValue K q.1 q.2 u' ≤ a ∧ q ∈ s := by
    exact hfreq.and_eventually eventually_mem_nhdsWithin
  rcases Filter.exists_seq_forall_of_frequently hfreq_mem with ⟨pSeq, hpSeq_tendsto, hpSeq_spec⟩
  have hpSeq_le :
      ∀ i : ℕ,
        realFirstVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 u' ≤ a := by
    intro i
    exact (hpSeq_spec i).1
  have hpSeq_mem : ∀ i : ℕ, pSeq i ∈ s := by
    intro i
    exact (hpSeq_spec i).2
  have hpSeq_tendsto_nhds : Filter.Tendsto pSeq Filter.atTop (nhds p) :=
    hpSeq_tendsto.mono_right nhdsWithin_le_nhds
  -- Project the sequence to coordinates and apply the constant-sequence specialization of Theorem 35.7.
  have hp_mem' : p.1 ∈ C ∧ p.2 ∈ D := by
    simpa [s] using hp
  have huSeq_mem : ∀ i : ℕ, (pSeq i).1 ∈ C := by
    intro i
    have : pSeq i ∈ C ×ˢ D := by
      simpa [s] using hpSeq_mem i
    simpa using this.1
  have hvSeq_mem : ∀ i : ℕ, (pSeq i).2 ∈ D := by
    intro i
    have : pSeq i ∈ C ×ˢ D := by
      simpa [s] using hpSeq_mem i
    simpa using this.2
  have huSeq_tendsto :
      Filter.Tendsto (fun i : ℕ => (pSeq i).1) Filter.atTop (nhds p.1) := by
    simpa using (continuous_fst.tendsto p).comp hpSeq_tendsto_nhds
  have hvSeq_tendsto :
      Filter.Tendsto (fun i : ℕ => (pSeq i).2) Filter.atTop (nhds p.2) := by
    simpa using (continuous_snd.tendsto p).comp hpSeq_tendsto_nhds
  have hAsymp :=
    helperForCorollary_35_7_1_constantSequence_asymptotics
      (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK
      (u := p.1) (v := p.2) hp_mem'.1 hp_mem'.2
      (fun i : ℕ => (pSeq i).1) (fun i : ℕ => (pSeq i).2)
      huSeq_mem hvSeq_mem huSeq_tendsto hvSeq_tendsto
  have hfp_le_liminf :
      ((realFirstVariableDirectionalDerivativeValue K p.1 p.2 u' : ℝ) : EReal) ≤
        Filter.liminf
          (fun i : ℕ =>
            ((realFirstVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 u' : ℝ) : EReal))
          Filter.atTop := by
    -- This is exactly the first clause of the constant-sequence specialization.
    simpa using (hAsymp.1 u')
  have hliminf_le_a :
      Filter.liminf
          (fun i : ℕ =>
            ((realFirstVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 u' : ℝ) : EReal))
          Filter.atTop ≤
        ((a : ℝ) : EReal) := by
    -- Since the sequence stays `≤ a`, its `liminf` is also `≤ a`.
    have hfreq_le :
        ∃ᶠ i : ℕ in Filter.atTop,
          ((realFirstVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 u' : ℝ) : EReal) ≤
            ((a : ℝ) : EReal) := by
      refine Filter.Frequently.of_forall ?_
      intro i
      exact (EReal.coe_le_coe_iff).2 (hpSeq_le i)
    exact Filter.liminf_le_of_frequently_le hfreq_le
  have hfp_le_a :
      ((realFirstVariableDirectionalDerivativeValue K p.1 p.2 u' : ℝ) : EReal) ≤ ((a : ℝ) : EReal) :=
    le_trans hfp_le_liminf hliminf_le_a
  have haE :
      ((a : ℝ) : EReal) <
        ((realFirstVariableDirectionalDerivativeValue K p.1 p.2 u' : ℝ) : EReal) :=
    (EReal.coe_lt_coe_iff).2 ha
  exact (not_lt_of_ge hfp_le_a) haE

/-- Helper for Corollary 35.7.1: the second-variable `limsup` inequality from Theorem 35.7 implies
upper semicontinuity of `(u, v) ↦ K'(u, v; 0, v')` on `C ×ˢ D`. -/
lemma helperForCorollary_35_7_1_upperSemicontinuousOn_secondDirectionalDerivative
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (v' : Fin n → ℝ) :
    UpperSemicontinuousOn
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        realSecondVariableDirectionalDerivativeValue K p.1 p.2 v')
      (C ×ˢ D) := by
  classical
  intro p hp a ha
  let s : Set ((Fin m → ℝ) × (Fin n → ℝ)) := C ×ˢ D
  -- Contradiction setup: if the strict upper bound `f p < a` fails eventually in `𝓝[s] p`,
  -- extract a sequence in `s` converging to `p` whose values stay `≥ a`.
  by_contra hUpper
  have hfreq_not_lt :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        ¬ realSecondVariableDirectionalDerivativeValue K q.1 q.2 v' < a :=
    Filter.not_eventually.1 hUpper
  have hfreq :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        a ≤ realSecondVariableDirectionalDerivativeValue K q.1 q.2 v' := by
    exact hfreq_not_lt.mono (fun q hq => le_of_not_gt hq)
  have hfreq_mem :
      ∃ᶠ q : (Fin m → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        a ≤ realSecondVariableDirectionalDerivativeValue K q.1 q.2 v' ∧ q ∈ s := by
    exact hfreq.and_eventually eventually_mem_nhdsWithin
  rcases Filter.exists_seq_forall_of_frequently hfreq_mem with ⟨pSeq, hpSeq_tendsto, hpSeq_spec⟩
  have hpSeq_ge :
      ∀ i : ℕ,
        a ≤ realSecondVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 v' := by
    intro i
    exact (hpSeq_spec i).1
  have hpSeq_mem : ∀ i : ℕ, pSeq i ∈ s := by
    intro i
    exact (hpSeq_spec i).2
  have hpSeq_tendsto_nhds : Filter.Tendsto pSeq Filter.atTop (nhds p) :=
    hpSeq_tendsto.mono_right nhdsWithin_le_nhds
  -- Project to coordinates and apply the constant-sequence specialization of Theorem 35.7.
  have hp_mem' : p.1 ∈ C ∧ p.2 ∈ D := by
    simpa [s] using hp
  have huSeq_mem : ∀ i : ℕ, (pSeq i).1 ∈ C := by
    intro i
    have : pSeq i ∈ C ×ˢ D := by
      simpa [s] using hpSeq_mem i
    simpa using this.1
  have hvSeq_mem : ∀ i : ℕ, (pSeq i).2 ∈ D := by
    intro i
    have : pSeq i ∈ C ×ˢ D := by
      simpa [s] using hpSeq_mem i
    simpa using this.2
  have huSeq_tendsto :
      Filter.Tendsto (fun i : ℕ => (pSeq i).1) Filter.atTop (nhds p.1) := by
    simpa using (continuous_fst.tendsto p).comp hpSeq_tendsto_nhds
  have hvSeq_tendsto :
      Filter.Tendsto (fun i : ℕ => (pSeq i).2) Filter.atTop (nhds p.2) := by
    simpa using (continuous_snd.tendsto p).comp hpSeq_tendsto_nhds
  have hAsymp :=
    helperForCorollary_35_7_1_constantSequence_asymptotics
      (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK
      (u := p.1) (v := p.2) hp_mem'.1 hp_mem'.2
      (fun i : ℕ => (pSeq i).1) (fun i : ℕ => (pSeq i).2)
      huSeq_mem hvSeq_mem huSeq_tendsto hvSeq_tendsto
  have hlimsup_le_fp :
      Filter.limsup
          (fun i : ℕ =>
            ((realSecondVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 v' : ℝ) :
              EReal))
          Filter.atTop ≤
        ((realSecondVariableDirectionalDerivativeValue K p.1 p.2 v' : ℝ) : EReal) := by
    simpa using (hAsymp.2.1 v')
  have ha_le_limsup :
      ((a : ℝ) : EReal) ≤
        Filter.limsup
          (fun i : ℕ =>
            ((realSecondVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 v' : ℝ) :
              EReal))
          Filter.atTop := by
    -- Since the sequence stays `≥ a`, its `limsup` is also `≥ a`.
    have hfreq_le :
        ∃ᶠ i : ℕ in Filter.atTop,
          ((a : ℝ) : EReal) ≤
            ((realSecondVariableDirectionalDerivativeValue K (pSeq i).1 (pSeq i).2 v' : ℝ) :
              EReal) := by
      refine Filter.Frequently.of_forall ?_
      intro i
      exact (EReal.coe_le_coe_iff).2 (hpSeq_ge i)
    exact Filter.le_limsup_of_frequently_le hfreq_le
  have hfp_ge_a :
      ((a : ℝ) : EReal) ≤ ((realSecondVariableDirectionalDerivativeValue K p.1 p.2 v' : ℝ) : EReal) :=
    le_trans (le_trans ha_le_limsup hlimsup_le_fp) le_rfl
  have haE :
      ((realSecondVariableDirectionalDerivativeValue K p.1 p.2 v' : ℝ) : EReal) < ((a : ℝ) : EReal) :=
    (EReal.coe_lt_coe_iff).2 ha
  exact (not_lt_of_ge hfp_ge_a) haE

/-- Helper for Corollary 35.7.1: the eventual saddle-subdifferential inclusion from Theorem 35.7
upgrades to a uniform split-ball neighborhood around any base point `(u, v) ∈ C ×ˢ D`. -/
lemma helperForCorollary_35_7_1_local_saddleSubdifferential_subset
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    {u : Fin m → ℝ} (hu : u ∈ C)
    {v : Fin n → ℝ} (hv : v ∈ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Fin m → ℝ, x ∈ C → ∀ y : Fin n → ℝ, y ∈ D →
        ((x - u), (y - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) δ →
          realSaddleSubdifferentialOn C D K x y ⊆
            Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
              (realSaddleSubdifferentialOn C D K u v)
              (splitEuclideanClosedBall (m := m) (n := n) ε) := by
  classical
  -- Target set for the inclusion at the base point `(u, v)`.
  let targetSet : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
    Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
      (realSaddleSubdifferentialOn C D K u v)
      (splitEuclideanClosedBall (m := m) (n := n) ε)
  -- Argue by contradiction, producing a shrinking split-ball counterexample sequence.
  by_contra hLocal
  push_neg at hLocal
  let δSeq : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have hδSeq_pos : ∀ k : ℕ, 0 < δSeq k := by
    intro k
    dsimp [δSeq]
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    exact one_div_pos.2 hkpos
  have hbad :
      ∀ k : ℕ,
        ∃ p : (Fin m → ℝ) × (Fin n → ℝ),
          p.1 ∈ C ∧ p.2 ∈ D ∧
            ((p.1 - u), (p.2 - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) (δSeq k) ∧
              ¬ (realSaddleSubdifferentialOn C D K p.1 p.2 ⊆ targetSet) := by
    intro k
    rcases hLocal (δSeq k) (hδSeq_pos k) with ⟨x, hxC, y, hyD, hmem, hnot⟩
    refine ⟨(x, y), hxC, hyD, ?_, ?_⟩
    · simpa using hmem
    · simpa [targetSet] using hnot
  choose pSeq hpSeq_memC hpSeq_memD hpSeq_memBall hpSeq_bad using hbad
  let xSeq : ℕ → Fin m → ℝ := fun k => (pSeq k).1
  let ySeq : ℕ → Fin n → ℝ := fun k => (pSeq k).2
  have hxSeq_mem : ∀ k, xSeq k ∈ C := by
    intro k
    simpa [xSeq] using hpSeq_memC k
  have hySeq_mem : ∀ k, ySeq k ∈ D := by
    intro k
    simpa [ySeq] using hpSeq_memD k
  have hdist_bound_x :
      ∀ k, dist (xSeq k) u ≤ δSeq k := by
    intro k
    have hδnonneg : 0 ≤ δSeq k := le_of_lt (hδSeq_pos k)
    have hbounds :=
      helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall (m := m) (n := n)
        (r := δSeq k) hδnonneg (du := xSeq k - u) (dv := ySeq k - v) (by
          -- The split-ball membership is part of the counterexample data.
          simpa [xSeq, ySeq] using hpSeq_memBall k)
    have hnorm : ‖xSeq k - u‖ ≤ δSeq k := hbounds.1
    simpa [dist_eq_norm] using hnorm
  have hdist_bound_y :
      ∀ k, dist (ySeq k) v ≤ δSeq k := by
    intro k
    have hδnonneg : 0 ≤ δSeq k := le_of_lt (hδSeq_pos k)
    have hbounds :=
      helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall (m := m) (n := n)
        (r := δSeq k) hδnonneg (du := xSeq k - u) (dv := ySeq k - v) (by
          simpa [xSeq, ySeq] using hpSeq_memBall k)
    have hnorm : ‖ySeq k - v‖ ≤ δSeq k := hbounds.2
    simpa [dist_eq_norm] using hnorm
  have hδSeq_tendsto_zero : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) := by
    -- Radii `δₖ = 1/(k+1)` shrink to `0`.
    have hbase :
        Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [δSeq] using hbase
  have hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds u) := by
    -- Control `dist (xₖ, u)` by `δₖ` and squeeze.
    have hdist_tendsto :
        Filter.Tendsto (fun k => dist (xSeq k) u) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun _ => dist_nonneg) hdist_bound_x hδSeq_tendsto_zero
    simpa using (tendsto_iff_dist_tendsto_zero.2 hdist_tendsto)
  have hySeq_tendsto : Filter.Tendsto ySeq Filter.atTop (nhds v) := by
    have hdist_tendsto :
        Filter.Tendsto (fun k => dist (ySeq k) v) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun _ => dist_nonneg) hdist_bound_y hδSeq_tendsto_zero
    simpa using (tendsto_iff_dist_tendsto_zero.2 hdist_tendsto)
  -- Apply the eventual inclusion from Theorem 35.7 to the shrinking counterexample sequence.
  have hAsymp :=
    helperForCorollary_35_7_1_constantSequence_asymptotics
      (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK
      (u := u) (v := v) hu hv xSeq ySeq hxSeq_mem hySeq_mem hxSeq_tendsto hySeq_tendsto
  rcases hAsymp.2.2 ε hε with ⟨i0, hi0⟩
  have hgood :
      realSaddleSubdifferentialOn C D K (xSeq i0) (ySeq i0) ⊆ targetSet := by
    have hraw := hi0 i0 le_rfl
    simpa [targetSet] using hraw
  exact hpSeq_bad i0 hgood

-- Proof sketch: apply Theorem 35.7 to the constant sequence `Kᵢ = K`. The liminf and limsup
-- inequalities then give lower semicontinuity of `(u, v) ↦ K'(u, v; u', 0)` and upper
-- semicontinuity of `(u, v) ↦ K'(u, v; 0, v')` on `C × D`. The eventual inclusion of
-- subdifferentials for the constant sequence yields, for each base point `(u, v)` and `ε > 0`,
-- a radius `δ > 0` such that all nearby points `(x, y) ∈ C × D` satisfy
-- `∂K(x, y) ⊆ ∂K(u, v) + ε B`.
/-- Corollary 35.7.1: let `C × D` be an open convex set in `ℝ^m × ℝ^n`, and let `K` be a
concave-convex real-valued function on `C × D`. Then for each direction `u' ∈ ℝ^m`, the map
`(u, v) ↦ K'(u, v; u', 0)` is lower semicontinuous on `C × D`; for each direction `v' ∈ ℝ^n`,
the map `(u, v) ↦ K'(u, v; 0, v')` is upper semicontinuous on `C × D`. Moreover, for every
`(u, v) ∈ C × D` and every `ε > 0`, there exists `δ > 0` such that whenever `(x, y) ∈ C × D`
and `((x - u), (y - v))` lies in the closed Euclidean ball of radius `δ`, one has
`∂K(x, y) ⊆ ∂K(u, v) + ε B`. -/
theorem section35_corollary35_7_1
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K) :
    (∀ u' : Fin m → ℝ,
      LowerSemicontinuousOn
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          realFirstVariableDirectionalDerivativeValue K p.1 p.2 u')
        (C ×ˢ D)) ∧
    (∀ v' : Fin n → ℝ,
      UpperSemicontinuousOn
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          realSecondVariableDirectionalDerivativeValue K p.1 p.2 v')
        (C ×ˢ D)) ∧
    (∀ ⦃u : Fin m → ℝ⦄, u ∈ C → ∀ ⦃v : Fin n → ℝ⦄, v ∈ D → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ x : Fin m → ℝ, x ∈ C → ∀ y : Fin n → ℝ, y ∈ D →
          ((x - u), (y - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) δ →
            realSaddleSubdifferentialOn C D K x y ⊆
              Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
                (realSaddleSubdifferentialOn C D K u v)
                (splitEuclideanClosedBall (m := m) (n := n) ε)) := by
  classical
  -- The corollary is a direct packaging of Theorem 35.7 specialized to the constant sequence `Kᵢ = K`.
  refine ⟨?_, ?_, ?_⟩
  · intro u'
    -- Lower semicontinuity comes from the `liminf` inequality in Theorem 35.7.
    exact
      helperForCorollary_35_7_1_lowerSemicontinuousOn_firstDirectionalDerivative
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK u'
  · intro v'
    -- Upper semicontinuity comes from the `limsup` inequality in Theorem 35.7.
    exact
      helperForCorollary_35_7_1_upperSemicontinuousOn_secondDirectionalDerivative
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK v'
  · intro u hu v hv ε hε
    -- The eventual inclusion from Theorem 35.7 becomes a uniform neighborhood statement by
    -- contradiction with a shrinking split-ball counterexample sequence.
    exact
      helperForCorollary_35_7_1_local_saddleSubdifferential_subset
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv ε hε


end Section35
end Chap07
