/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part5

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Helper for Theorem 35.6: along any admissible positive null sequence, the diagonal
second-variable increment is eventually bounded above by the second-axis split-kernel value plus
an arbitrary error. -/
lemma helperForTheorem_35_6_movingSecondIncrement_eventually_le_axisSecondKernel
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (hAxisSecond :
      ∀ v'', IsSaddleDirectionalDerivativeAt K u v 0 v'' (Kdir 0 v'' : EReal))
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in Filter.atTop,
      (((K (u + τ i • u') (v + τ i • v') - K (u + τ i • u') v) / (τ i : EReal)).toReal : ℝ) ≤
        Kdir 0 v' + ε := by
  let σ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hσWithin :
      Filter.Tendsto σ Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun k => by
      dsimp [σ]
      simpa [Set.mem_Ioi] using (show 0 < 1 / ((k : ℝ) + 1) by positivity)
  have hAxisSecondReal :
      Filter.Tendsto
        (fun k => (((K u (v + σ k • v') - K u v) / (σ k : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (Kdir 0 v')) := by
    have hAxisSecondE :
        Filter.Tendsto
          (fun k => saddleDirectionalDifferenceQuotientAt K u v 0 v' (σ k))
          Filter.atTop
          (nhds ((Kdir 0 v' : ℝ) : EReal)) :=
      (hAxisSecond v').2.2.comp hσWithin
    have hAxisSecondToReal :
        Filter.Tendsto
          (fun k => (saddleDirectionalDifferenceQuotientAt K u v 0 v' (σ k)).toReal)
          Filter.atTop
          (nhds (Kdir 0 v')) := by
      simpa using
        (EReal.tendsto_toReal
          (a := ((Kdir 0 v' : ℝ) : EReal)) (by simp) (by simp)).comp hAxisSecondE
    simpa [saddleDirectionalDifferenceQuotientAt] using hAxisSecondToReal
  have hAxisUpper :
      ∀ᶠ k in Filter.atTop,
        (((K u (v + σ k • v') - K u v) / (σ k : EReal)).toReal : ℝ) <
          Kdir 0 v' + ε / 2 :=
    hAxisSecondReal (Iio_mem_nhds (by linarith))
  rcases Filter.eventually_atTop.1 hAxisUpper with ⟨N, hN⟩
  let η : ℝ := σ N
  have hηpos : 0 < η := by
    dsimp [η, σ]
    positivity
  have hηle : η ≤ 1 := by
    dsimp [η, σ]
    refine (one_div_le (show 0 < ((N : ℝ) + 1) by positivity) (show 0 < (1 : ℝ) by positivity)).2 ?_
    have : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      exact le_add_of_nonneg_left (show (0 : ℝ) ≤ N by positivity)
    simpa using this
  have hBaseEta :
      (((K u (v + η • v') - K u v) / (η : EReal)).toReal : ℝ) < Kdir 0 v' + ε / 2 := by
    have := hN N le_rfl
    simpa [η, σ] using this
  have hMovedEta :
      Filter.Tendsto
        (fun i =>
          (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (((K u (v + η • v') - K u v) / (η : EReal)).toReal : ℝ)) :=
    helperForTheorem_35_6_fixedStepMovedSecondIncrement_tendsto_baseSecondQuotient
      (C := C) (D := D) (K := K)
      hC_open hD_open hC_conv hD_conv hK hFinite hu hv
      hτpos hτle hτtendsto hu' hηpos hηle hv'
  have hMovedEtaUpper :
      ∀ᶠ i in Filter.atTop,
        (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ) <
          (((K u (v + η • v') - K u v) / (η : EReal)).toReal : ℝ) + ε / 2 :=
    hMovedEta (Iio_mem_nhds (by linarith))
  have hTauLtEta : ∀ᶠ i in Filter.atTop, τ i < η := by
    have hNhds : Set.Iio η ∈ nhds (0 : ℝ) := Iio_mem_nhds hηpos
    exact hτtendsto hNhds
  filter_upwards [hMovedEtaUpper, hTauLtEta] with i hiMoved hiTau
  have huu' : u + u' ∈ C := hu'
  have huStep : u + τ i • u' ∈ C := by
    have hrewrite : u + τ i • u' = (1 - τ i) • u + τ i • (u + u') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the translated first-variable point in `C`.
    rw [hrewrite]
    exact hC_conv hu huu' (by linarith [hτle i]) (hτpos i).le (by linarith)
  let g : (Fin n → ℝ) → EReal := fun z => K (u + τ i • u') z
  have hg : ConvexFunction g := by
    -- Fixing the translated first argument preserves convexity in the second variable.
    simpa [g] using hK.2 (u + τ i • u')
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The base point of the translated second slice is still finite.
    simpa [g] using hFinite (u + τ i • u') huStep v hv
  have hmono : MonotoneOn (directionalDifferenceQuotientAt g v v') (Set.Ioi (0 : ℝ)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear g hg v hgv).1 v' |>.1
  have hquot_le :
      directionalDifferenceQuotientAt g v v' (τ i) ≤
        directionalDifferenceQuotientAt g v v' η :=
    hmono (by simpa using hτpos i) (by simpa using hηpos) hiTau.le
  have hvv' : v + v' ∈ D := hv'
  have hvDiag : v + τ i • v' ∈ D := by
    have hrewrite : v + τ i • v' = (1 - τ i) • v + τ i • (v + v') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the diagonal second-variable point in `D`.
    rw [hrewrite]
    exact hD_conv hv hvv' (by linarith [hτle i]) (hτpos i).le (by linarith)
  have hvEta : v + η • v' ∈ D := by
    have hrewrite : v + η • v' = (1 - η) • v + η • (v + v') := by
      ext j
      simp [smul_add]
      ring
    -- The chosen fixed step `η` stays on the same segment in `D`.
    rw [hrewrite]
    exact hD_conv hv hvv' (by linarith [hηle]) hηpos.le (by linarith)
  have hDiagFinite :
      directionalDifferenceQuotientAt g v v' (τ i) ≠ (⊤ : EReal) ∧
        directionalDifferenceQuotientAt g v v' (τ i) ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_9_secantQuotient_finite
      (f := g) (x := v) (u := v') (t := τ i) hgv
      (by simpa [g] using hFinite (u + τ i • u') huStep (v + τ i • v') hvDiag)
      (hτpos i)
  have hEtaFinite :
      directionalDifferenceQuotientAt g v v' η ≠ (⊤ : EReal) ∧
        directionalDifferenceQuotientAt g v v' η ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_9_secantQuotient_finite
      (f := g) (x := v) (u := v') (t := η) hgv
      (by simpa [g] using hFinite (u + τ i • u') huStep (v + η • v') hvEta)
      hηpos
  have hquot_le_real :
      (((K (u + τ i • u') (v + τ i • v') - K (u + τ i • u') v) / (τ i : EReal)).toReal : ℝ) ≤
        (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ) := by
    exact
      EReal.toReal_le_toReal
        (by simpa [g, directionalDifferenceQuotientAt] using hquot_le)
        hDiagFinite.2 hEtaFinite.1
  have hMovedBase :
      (((K (u + τ i • u') (v + η • v') - K (u + τ i • u') v) / (η : EReal)).toReal : ℝ) <
        Kdir 0 v' + ε := by
    linarith
  linarith

/-- Helper for Theorem 35.6: along any admissible positive null sequence, the diagonal
first-variable increment is eventually bounded below by the first-axis split-kernel value minus
an arbitrary error. -/
lemma helperForTheorem_35_6_axisFirstKernel_le_eventually_movingFirstIncrement
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (hAxisFirst :
      ∀ u'', IsSaddleDirectionalDerivativeAt K u v u'' 0 (Kdir u'' 0 : EReal))
    {τ : ℕ → ℝ}
    (hτpos : ∀ i, 0 < τ i) (hτle : ∀ i, τ i ≤ 1)
    (hτtendsto : Filter.Tendsto τ Filter.atTop (nhds (0 : ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ)))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in Filter.atTop,
      Kdir u' 0 - ε ≤
        (((K (u + τ i • u') (v + τ i • v') - K u (v + τ i • v')) / (τ i : EReal)).toReal : ℝ) := by
  let σ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hσWithin :
      Filter.Tendsto σ Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun k => by
      dsimp [σ]
      simpa [Set.mem_Ioi] using (show 0 < 1 / ((k : ℝ) + 1) by positivity)
  have hAxisFirstReal :
      Filter.Tendsto
        (fun k => (((K (u + σ k • u') v - K u v) / (σ k : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (Kdir u' 0)) := by
    have hAxisFirstE :
        Filter.Tendsto
          (fun k => saddleDirectionalDifferenceQuotientAt K u v u' 0 (σ k))
          Filter.atTop
          (nhds ((Kdir u' 0 : ℝ) : EReal)) :=
      (hAxisFirst u').2.2.comp hσWithin
    have hAxisFirstToReal :
        Filter.Tendsto
          (fun k => (saddleDirectionalDifferenceQuotientAt K u v u' 0 (σ k)).toReal)
          Filter.atTop
          (nhds (Kdir u' 0)) := by
      simpa using
        (EReal.tendsto_toReal
          (a := ((Kdir u' 0 : ℝ) : EReal)) (by simp) (by simp)).comp hAxisFirstE
    simpa [saddleDirectionalDifferenceQuotientAt] using hAxisFirstToReal
  have hAxisLower :
      ∀ᶠ k in Filter.atTop,
        Kdir u' 0 - ε / 2 <
          (((K (u + σ k • u') v - K u v) / (σ k : EReal)).toReal : ℝ) :=
    hAxisFirstReal (Ioi_mem_nhds (by linarith))
  rcases Filter.eventually_atTop.1 hAxisLower with ⟨N, hN⟩
  let η : ℝ := σ N
  have hηpos : 0 < η := by
    dsimp [η, σ]
    positivity
  have hηle : η ≤ 1 := by
    dsimp [η, σ]
    refine (one_div_le (show 0 < ((N : ℝ) + 1) by positivity) (show 0 < (1 : ℝ) by positivity)).2 ?_
    have : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      exact le_add_of_nonneg_left (show (0 : ℝ) ≤ N by positivity)
    simpa using this
  have hBaseEta :
      Kdir u' 0 - ε / 2 <
        (((K (u + η • u') v - K u v) / (η : EReal)).toReal : ℝ) := by
    have := hN N le_rfl
    simpa [η, σ] using this
  have hMovedEta :
      Filter.Tendsto
        (fun i =>
          (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (((K (u + η • u') v - K u v) / (η : EReal)).toReal : ℝ)) :=
    helperForTheorem_35_6_fixedStepMovedFirstIncrement_tendsto_baseFirstQuotient
      (C := C) (D := D) (K := K)
      hC_open hD_open hC_conv hD_conv hK hFinite hu hv
      hτpos hτle hτtendsto hv' hηpos hηle hu'
  have hMovedEtaLower :
      ∀ᶠ i in Filter.atTop,
        (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) >
          (((K (u + η • u') v - K u v) / (η : EReal)).toReal : ℝ) - ε / 2 :=
    hMovedEta (Ioi_mem_nhds (by linarith))
  have hTauLtEta : ∀ᶠ i in Filter.atTop, τ i < η := by
    have hNhds : Set.Iio η ∈ nhds (0 : ℝ) := Iio_mem_nhds hηpos
    exact hτtendsto hNhds
  filter_upwards [hMovedEtaLower, hTauLtEta] with i hiMoved hiTau
  have hvv' : v + v' ∈ D := hv'
  have hvStep : v + τ i • v' ∈ D := by
    have hrewrite : v + τ i • v' = (1 - τ i) • v + τ i • (v + v') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the translated second-variable point in `D`.
    rw [hrewrite]
    exact hD_conv hv hvv' (by linarith [hτle i]) (hτpos i).le (by linarith)
  let f : (Fin m → ℝ) → EReal := fun x => -K x (v + τ i • v')
  have hf : ConvexFunction f := by
    -- Fixing the translated second argument preserves convexity after negation.
    simpa [f] using hK.1 (v + τ i • v')
  have hfu : f u ≠ (⊤ : EReal) ∧ f u ≠ (⊥ : EReal) := by
    have hbase : K u (v + τ i • v') ≠ (⊤ : EReal) ∧ K u (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite u hu (v + τ i • v') hvStep
    exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩
  have hmono : MonotoneOn (directionalDifferenceQuotientAt f u u') (Set.Ioi (0 : ℝ)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf u hfu).1 u' |>.1
  have hquot_le :
      directionalDifferenceQuotientAt f u u' (τ i) ≤
        directionalDifferenceQuotientAt f u u' η :=
    hmono (by simpa using hτpos i) (by simpa using hηpos) hiTau.le
  have huu' : u + u' ∈ C := hu'
  have huDiag : u + τ i • u' ∈ C := by
    have hrewrite : u + τ i • u' = (1 - τ i) • u + τ i • (u + u') := by
      ext j
      simp [smul_add]
      ring
    -- Convexity keeps the diagonal first-variable point in `C`.
    rw [hrewrite]
    exact hC_conv hu huu' (by linarith [hτle i]) (hτpos i).le (by linarith)
  have huEta : u + η • u' ∈ C := by
    have hrewrite : u + η • u' = (1 - η) • u + η • (u + u') := by
      ext j
      simp [smul_add]
      ring
    -- The chosen fixed step `η` stays on the same segment in `C`.
    rw [hrewrite]
    exact hC_conv hu huu' (by linarith [hηle]) hηpos.le (by linarith)
  have hDiagFinite :
      directionalDifferenceQuotientAt f u u' (τ i) ≠ (⊤ : EReal) ∧
        directionalDifferenceQuotientAt f u u' (τ i) ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_9_secantQuotient_finite
      (f := f) (x := u) (u := u') (t := τ i) hfu
      (by
        have hbase : K (u + τ i • u') (v + τ i • v') ≠ (⊤ : EReal) ∧
            K (u + τ i • u') (v + τ i • v') ≠ (⊥ : EReal) :=
          hFinite (u + τ i • u') huDiag (v + τ i • v') hvStep
        exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩)
      (hτpos i)
  have hfDiagStep :
      f (u + τ i • u') ≠ (⊤ : EReal) ∧ f (u + τ i • u') ≠ (⊥ : EReal) := by
    have hbase : K (u + τ i • u') (v + τ i • v') ≠ (⊤ : EReal) ∧
        K (u + τ i • u') (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite (u + τ i • u') huDiag (v + τ i • v') hvStep
    exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩
  have hEtaFinite :
      directionalDifferenceQuotientAt f u u' η ≠ (⊤ : EReal) ∧
        directionalDifferenceQuotientAt f u u' η ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_9_secantQuotient_finite
      (f := f) (x := u) (u := u') (t := η) hfu
      (by
        have hbase : K (u + η • u') (v + τ i • v') ≠ (⊤ : EReal) ∧
            K (u + η • u') (v + τ i • v') ≠ (⊥ : EReal) :=
          hFinite (u + η • u') huEta (v + τ i • v') hvStep
        exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩)
      hηpos
  have hfEtaStep :
      f (u + η • u') ≠ (⊤ : EReal) ∧ f (u + η • u') ≠ (⊥ : EReal) := by
    have hbase : K (u + η • u') (v + τ i • v') ≠ (⊤ : EReal) ∧
        K (u + η • u') (v + τ i • v') ≠ (⊥ : EReal) :=
      hFinite (u + η • u') huEta (v + τ i • v') hvStep
    exact ⟨by simpa [f] using hbase.2, by simpa [f] using hbase.1⟩
  have hquot_le_real :
      (directionalDifferenceQuotientAt f u u' (τ i)).toReal ≤
        (directionalDifferenceQuotientAt f u u' η).toReal := by
    exact EReal.toReal_le_toReal hquot_le hDiagFinite.2 hEtaFinite.1
  have hdiagRewrite :
      (directionalDifferenceQuotientAt f u u' (τ i)).toReal =
        -(((K (u + τ i • u') (v + τ i • v') - K u (v + τ i • v')) / (τ i : EReal)).toReal : ℝ) := by
    have hleft :
        -directionalDifferenceQuotientAt f u u' (τ i) =
          ((K (u + τ i • u') (v + τ i • v') - K u (v + τ i • v')) / (τ i : EReal)) := by
      rw [directionalDifferenceQuotientAt, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
      rw [EReal.neg_sub (Or.inl hfDiagStep.2) (Or.inr hfu.1)]
      rw [← EReal.div_eq_inv_mul]
      simp [f, sub_eq_add_neg]
    have hdiagReal :
        (((K (u + τ i • u') (v + τ i • v') - K u (v + τ i • v')) / (τ i : EReal)).toReal : ℝ) =
          -(directionalDifferenceQuotientAt f u u' (τ i)).toReal := by
      simpa using congrArg EReal.toReal hleft.symm
    linarith
  have hEtaRewrite :
      (directionalDifferenceQuotientAt f u u' η).toReal =
        -(((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) := by
    have hleft :
        -directionalDifferenceQuotientAt f u u' η =
          ((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)) := by
      rw [directionalDifferenceQuotientAt, EReal.div_eq_inv_mul, neg_mul_eq_mul_neg]
      rw [EReal.neg_sub (Or.inl hfEtaStep.2) (Or.inr hfu.1)]
      rw [← EReal.div_eq_inv_mul]
      simp [f, sub_eq_add_neg]
    have hEtaReal :
        (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) =
          -(directionalDifferenceQuotientAt f u u' η).toReal := by
      simpa using congrArg EReal.toReal hleft.symm
    linarith
  have hfixed_le_diag :
      (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) ≤
        (((K (u + τ i • u') (v + τ i • v') - K u (v + τ i • v')) / (τ i : EReal)).toReal : ℝ) := by
    linarith
  have hMovedBase :
      Kdir u' 0 - ε <
        (((K (u + η • u') (v + τ i • v') - K u (v + τ i • v')) / (η : EReal)).toReal : ℝ) := by
    linarith
  linarith

/-- Helper for Theorem 35.6: along every sequence approaching `0` through positive steps, the
real mixed quotient converges to the split-kernel value. -/
lemma helperForTheorem_35_6_mixedQuotient_toReal_tendsto_splitKernelAlongNullSeq
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (hAxisFirst :
      ∀ u'', IsSaddleDirectionalDerivativeAt K u v u'' 0 (Kdir u'' 0 : EReal))
    (hAxisSecond :
      ∀ v'', IsSaddleDirectionalDerivativeAt K u v 0 v'' (Kdir 0 v'' : EReal))
    (hKdir_split : ∀ u'' v'', Kdir u'' v'' = Kdir u'' 0 + Kdir 0 v'')
    {τ : ℕ → ℝ}
    (hτWithin : Filter.Tendsto τ Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    Filter.Tendsto
      (fun i => (saddleDirectionalDifferenceQuotientAt K u v u' v' (τ i)).toReal)
      Filter.atTop
      (nhds (Kdir u' v')) := by
  obtain ⟨hτtendsto, hτeventPos⟩ := tendsto_nhdsWithin_iff.mp hτWithin
  have hτeventLe : ∀ᶠ i in Filter.atTop, τ i ≤ 1 := by
    -- Eventually the positive null sequence lies inside the short-step range used by the local helpers.
    have hτeventLt : ∀ᶠ i in Filter.atTop, τ i < 1 :=
      hτtendsto (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact Filter.Eventually.mono hτeventLt fun _ hi => le_of_lt hi
  rcases Filter.eventually_atTop.1 (hτeventPos.and hτeventLe) with ⟨N, hN⟩
  let σ : ℕ → ℝ := fun i => τ (i + N)
  have hσWithin :
      Filter.Tendsto σ Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- Shifting to a tail keeps the same right-limit at `0`.
    simpa [σ] using hτWithin.comp (Filter.tendsto_add_atTop_nat N)
  have hσtendsto : Filter.Tendsto σ Filter.atTop (nhds (0 : ℝ)) :=
    (tendsto_nhdsWithin_iff.mp hσWithin).1
  have hσpos : ∀ i, 0 < σ i := by
    intro i
    exact (hN (i + N) (le_add_of_nonneg_left (Nat.zero_le i))).1
  have hσle : ∀ i, σ i ≤ 1 := by
    intro i
    exact (hN (i + N) (le_add_of_nonneg_left (Nat.zero_le i))).2
  have hAxisFirstReal :
      Filter.Tendsto
        (fun i => (((K (u + σ i • u') v - K u v) / (σ i : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (Kdir u' 0)) := by
    have hAxisFirstE :
        Filter.Tendsto
          (fun i => saddleDirectionalDifferenceQuotientAt K u v u' 0 (σ i))
          Filter.atTop
          (nhds ((Kdir u' 0 : ℝ) : EReal)) :=
      (hAxisFirst u').2.2.comp hσWithin
    have hAxisFirstToReal :
        Filter.Tendsto
          (fun i => (saddleDirectionalDifferenceQuotientAt K u v u' 0 (σ i)).toReal)
          Filter.atTop
          (nhds (Kdir u' 0)) := by
      simpa using
        (EReal.tendsto_toReal
          (a := ((Kdir u' 0 : ℝ) : EReal)) (by simp) (by simp)).comp hAxisFirstE
    simpa [saddleDirectionalDifferenceQuotientAt] using hAxisFirstToReal
  have hAxisSecondReal :
      Filter.Tendsto
        (fun i => (((K u (v + σ i • v') - K u v) / (σ i : EReal)).toReal : ℝ))
        Filter.atTop
        (nhds (Kdir 0 v')) := by
    have hAxisSecondE :
        Filter.Tendsto
          (fun i => saddleDirectionalDifferenceQuotientAt K u v 0 v' (σ i))
          Filter.atTop
          (nhds ((Kdir 0 v' : ℝ) : EReal)) :=
      (hAxisSecond v').2.2.comp hσWithin
    have hAxisSecondToReal :
        Filter.Tendsto
          (fun i => (saddleDirectionalDifferenceQuotientAt K u v 0 v' (σ i)).toReal)
          Filter.atTop
          (nhds (Kdir 0 v')) := by
      simpa using
        (EReal.tendsto_toReal
          (a := ((Kdir 0 v' : ℝ) : EReal)) (by simp) (by simp)).comp hAxisSecondE
    simpa [saddleDirectionalDifferenceQuotientAt] using hAxisSecondToReal
  have hShifted :
      Filter.Tendsto
        (fun i => (saddleDirectionalDifferenceQuotientAt K u v u' v' (σ i)).toReal)
        Filter.atTop
        (nhds (Kdir u' v')) := by
    -- The mixed quotient is squeezed between the split-kernel value plus or minus an arbitrary error.
    rw [tendsto_order]
    constructor
    · intro a ha
      let ε : ℝ := (Kdir u' v' - a) / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hAxisLower :
          ∀ᶠ i in Filter.atTop,
            Kdir 0 v' - ε <
              (((K u (v + σ i • v') - K u v) / (σ i : EReal)).toReal : ℝ) :=
        hAxisSecondReal (Ioi_mem_nhds (by linarith : Kdir 0 v' - ε < Kdir 0 v'))
      have hMovedLower :
          ∀ᶠ i in Filter.atTop,
            Kdir u' 0 - ε ≤
              (((K (u + σ i • u') (v + σ i • v') - K u (v + σ i • v')) /
                  (σ i : EReal)).toReal : ℝ) :=
        helperForTheorem_35_6_axisFirstKernel_le_eventually_movingFirstIncrement
          (C := C) (D := D) (K := K) (Kdir := Kdir)
          hC_open hD_open hC_conv hD_conv hK hFinite hu hv
          hAxisFirst hσpos hσle hσtendsto hv' hu' hε
      filter_upwards [hAxisLower, hMovedLower] with i hiAxis hiMoved
      rcases
          helperForTheorem_35_6_mixedQuotient_eq_axisPlusMovedIncrements
            (C := C) (D := D) (K := K)
            hC_open hD_open hC_conv hD_conv hFinite hu hv
            (t := σ i) (hσpos i) (hσle i) hu' hv' with
        ⟨_hFirstSplit, hSecondSplit⟩
      -- Use the decomposition through the moved first increment to get the lower bound.
      have hSplit := hKdir_split u' v'
      have hLower :
          a <
            (((K u (v + σ i • v') - K u v) / (σ i : EReal)).toReal : ℝ) +
              (((K (u + σ i • u') (v + σ i • v') - K u (v + σ i • v')) /
                  (σ i : EReal)).toReal : ℝ) := by
        dsimp [ε] at hiAxis hiMoved ⊢
        linarith
      simpa [hSecondSplit] using hLower
    · intro b hb
      let ε : ℝ := (b - Kdir u' v') / 2
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hAxisUpper :
          ∀ᶠ i in Filter.atTop,
            (((K (u + σ i • u') v - K u v) / (σ i : EReal)).toReal : ℝ) <
              Kdir u' 0 + ε :=
        hAxisFirstReal (Iio_mem_nhds (by linarith : Kdir u' 0 < Kdir u' 0 + ε))
      have hMovedUpper :
          ∀ᶠ i in Filter.atTop,
            (((K (u + σ i • u') (v + σ i • v') - K (u + σ i • u') v) /
                (σ i : EReal)).toReal : ℝ) ≤
              Kdir 0 v' + ε :=
        helperForTheorem_35_6_movingSecondIncrement_eventually_le_axisSecondKernel
          (C := C) (D := D) (K := K) (Kdir := Kdir)
          hC_open hD_open hC_conv hD_conv hK hFinite hu hv
          hAxisSecond hσpos hσle hσtendsto hu' hv' hε
      filter_upwards [hAxisUpper, hMovedUpper] with i hiAxis hiMoved
      rcases
          helperForTheorem_35_6_mixedQuotient_eq_axisPlusMovedIncrements
            (C := C) (D := D) (K := K)
            hC_open hD_open hC_conv hD_conv hFinite hu hv
            (t := σ i) (hσpos i) (hσle i) hu' hv' with
        ⟨hFirstSplit, _hSecondSplit⟩
      -- The symmetric decomposition through the moved second increment gives the upper bound.
      have hSplit := hKdir_split u' v'
      have hUpper :
          (((K (u + σ i • u') v - K u v) / (σ i : EReal)).toReal : ℝ) +
              (((K (u + σ i • u') (v + σ i • v') - K (u + σ i • u') v) /
                  (σ i : EReal)).toReal : ℝ) <
            b := by
        dsimp [ε] at hiAxis hiMoved ⊢
        linarith
      simpa [hFirstSplit] using hUpper
  -- Remove the finite prefix that was only introduced to enforce the short-step hypotheses globally.
  exact (Filter.tendsto_add_atTop_iff_nat N).1 (by simpa [σ] using hShifted)

/-- Helper for Theorem 35.6: every direction can be shrunk by a positive factor into the
translated direction domains of the open patch `C × D`. -/
lemma helperForTheorem_35_6_exists_posScale_mem_translatedDomains
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (u' : Fin m → ℝ) (v' : Fin n → ℝ) :
    ∃ ρ : ℝ,
      0 < ρ ∧
      ρ • u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)) ∧
      ρ • v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ)) := by
  have hCuNhds : C ∈ nhds u := hC_open.mem_nhds hu
  have hDvNhds : D ∈ nhds v := hD_open.mem_nhds hv
  rcases Metric.mem_nhds_iff.mp hCuNhds with ⟨εu, hεu, hBallu⟩
  rcases Metric.mem_nhds_iff.mp hDvNhds with ⟨εv, hεv, hBallv⟩
  rcases
      helperForText_35_5_5_exists_delta_line_subset_ball
        (x := u) (w := u') hεu with
    ⟨δu, hδu, hLineu⟩
  rcases
      helperForText_35_5_5_exists_delta_line_subset_ball
        (x := v) (w := v') hεv with
    ⟨δv, hδv, hLinev⟩
  let ρ : ℝ := min δu δv / 2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    have hMinPos : 0 < min δu δv := lt_min hδu hδv
    positivity
  have hρltu : ρ < δu := by
    dsimp [ρ]
    have hHalf : min δu δv / 2 < min δu δv := by
      nlinarith [show (0 : ℝ) < min δu δv by exact lt_min hδu hδv]
    exact lt_of_lt_of_le hHalf (min_le_left _ _)
  have hρltv : ρ < δv := by
    dsimp [ρ]
    have hHalf : min δu δv / 2 < min δu δv := by
      nlinarith [show (0 : ℝ) < min δu δv by exact lt_min hδu hδv]
    exact lt_of_lt_of_le hHalf (min_le_right _ _)
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · -- The shortened first direction stays inside the open ball around `u`, hence inside `C`.
    have huBall : u + ρ • u' ∈ Metric.ball u εu :=
      hLineu ρ ⟨hρpos.le, hρltu⟩
    exact hBallu huBall
  · -- The same shrinking argument places the second direction inside `D`.
    have hvBall : v + ρ • v' ∈ Metric.ball v εv :=
      hLinev ρ ⟨hρpos.le, hρltv⟩
    exact hBallv hvBall

/-- Helper for Theorem 35.6: on admissible translated directions, the real mixed quotient has the
full right-limit `Kdir u' v'` along `nhdsWithin 0 (0, ∞)`. -/
lemma helperForTheorem_35_6_mixedQuotient_toReal_tendsto_splitKernelWithin
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (hAxisFirst :
      ∀ u'', IsSaddleDirectionalDerivativeAt K u v u'' 0 (Kdir u'' 0 : EReal))
    (hAxisSecond :
      ∀ v'', IsSaddleDirectionalDerivativeAt K u v 0 v'' (Kdir 0 v'' : EReal))
    (hKdir_split : ∀ u'' v'', Kdir u'' v'' = Kdir u'' 0 + Kdir 0 v'')
    {u' : Fin m → ℝ}
    (hu' : u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    {v' : Fin n → ℝ}
    (hv' : v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    Filter.Tendsto
      (fun t : ℝ => (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (Kdir u' v')) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro τ hτWithin
  -- The sequential null-sequence lemma already gives the mixed limit on every admissible pair.
  simpa [Function.comp] using
    helperForTheorem_35_6_mixedQuotient_toReal_tendsto_splitKernelAlongNullSeq
      (C := C) (D := D) (K := K) (Kdir := Kdir)
      hC_open hD_open hC_conv hD_conv hK hFinite hu hv
      hAxisFirst hAxisSecond hKdir_split hτWithin hu' hv'

/-- Helper for Theorem 35.6: after shrinking to the eventual region `0 < t < ρ`, the mixed
quotient in direction `(u', v')` is exactly the rescaled admissible quotient in direction
`(ρ • u', ρ • v')` evaluated at step `t / ρ`. -/
lemma helperForTheorem_35_6_reparametrize_mixedQuotient_by_posScale
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hFinite :
      ∀ u ∈ C, ∀ v ∈ D, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    {u' : Fin m → ℝ} {v' : Fin n → ℝ}
    {ρ : ℝ} (hρpos : 0 < ρ)
    (huρ : ρ • u' ∈ ({u'' : Fin m → ℝ | u + u'' ∈ C} : Set (Fin m → ℝ)))
    (hvρ : ρ • v' ∈ ({v'' : Fin n → ℝ | v + v'' ∈ D} : Set (Fin n → ℝ))) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal =
        (1 / ρ) *
          (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal := by
  have hLtRho : Set.Iio ρ ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio ρ, Iio_mem_nhds hρpos, ?_⟩
    intro t ht
    exact ht.1
  filter_upwards [self_mem_nhdsWithin, hLtRho] with t ht_pos ht_lt
  have hρne : ρ ≠ 0 := hρpos.ne'
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have ht_div_pos : 0 < t / ρ := div_pos ht_pos hρpos
  have ht_div_le : t / ρ ≤ 1 := by
    rw [div_le_one hρpos]
    exact le_of_lt ht_lt
  have hStepU :
      u + (t / ρ) • (ρ • u') = u + t • u' := by
    have hmul : (t / ρ) * ρ = t := by
      field_simp [hρne]
    calc
      u + (t / ρ) • (ρ • u') = u + (((t / ρ) * ρ) • u') := by rw [smul_smul]
      _ = u + t • u' := by simp [hmul]
  have hStepV :
      v + (t / ρ) • (ρ • v') = v + t • v' := by
    have hmul : (t / ρ) * ρ = t := by
      field_simp [hρne]
    calc
      v + (t / ρ) • (ρ • v') = v + (((t / ρ) * ρ) • v') := by rw [smul_smul]
      _ = v + t • v' := by simp [hmul]
  have hMixedFinite :
      K (u + t • u') (v + t • v') ≠ (⊤ : EReal) ∧
        K (u + t • u') (v + t • v') ≠ (⊥ : EReal) := by
    -- The rescaled admissible step lands at the same mixed point as the original quotient.
    simpa [hStepU, hStepV] using
      (helperForTheorem_35_6_scaledStep_finiteValues
        (C := C) (D := D) (K := K)
        hC_open hD_open hC_conv hD_conv hFinite hu hv
        (t := t / ρ) ht_div_pos ht_div_le huρ hvρ)
  have hBaseFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFinite u hu v hv
  have hOrigReal :
      (saddleDirectionalDifferenceQuotientAt K u v u' v' t).toReal =
        ((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / t := by
    rw [saddleDirectionalDifferenceQuotientAt, EReal.div_eq_inv_mul, EReal.toReal_mul]
    rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hBaseFinite.1 hBaseFinite.2]
    have hInv : ((t : EReal)⁻¹).toReal = t⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  have hScaledReal :
      (saddleDirectionalDifferenceQuotientAt K u v (ρ • u') (ρ • v') (t / ρ)).toReal =
        ((K (u + t • u') (v + t • v')).toReal - (K u v).toReal) / (t / ρ) := by
    rw [saddleDirectionalDifferenceQuotientAt, hStepU, hStepV, EReal.div_eq_inv_mul,
      EReal.toReal_mul]
    rw [EReal.toReal_sub hMixedFinite.1 hMixedFinite.2 hBaseFinite.1 hBaseFinite.2]
    have hInv : (((t / ρ : ℝ) : EReal)⁻¹).toReal = (t / ρ)⁻¹ := by
      rw [← EReal.coe_inv]
      simp
    rw [hInv]
    ring
  -- Both sides reduce to the same explicit real quotient after canceling the factor `ρ`.
  rw [hOrigReal, hScaledReal]
  field_simp [hρne, ht_ne]

/-- Helper for Theorem 35.6: if a subsequential limit has the correct second marginal and the
correct first-axis values, then the textbook splitting formula forces equality with `Kdir` on the
translated direction domain. -/
lemma helperForTheorem_35_6_subseqLimit_eq_splitKernel_of_secondMarginal
    {m n : ℕ}
    {CU : Set (Fin m → ℝ)} {DV : Set (Fin n → ℝ)}
    {L Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hAxisFirst : ∀ u' ∈ CU, L u' 0 = Kdir u' 0)
    (hSecondMarginal :
      ∀ u' ∈ CU, ∀ v' ∈ DV, L u' v' - L u' 0 = Kdir 0 v')
    (hSplit : ∀ u' v', Kdir u' v' = Kdir u' 0 + Kdir 0 v') :
    ∀ u' ∈ CU, ∀ v' ∈ DV, L u' v' = Kdir u' v' := by
  intro u' hu' v' hv'
  -- Substitute the known second marginal and the first-axis value, then compare with the split
  -- formula for `Kdir`.
  have hAxis : L u' 0 = Kdir u' 0 := hAxisFirst u' hu'
  have hMarg : L u' v' - L u' 0 = Kdir 0 v' := hSecondMarginal u' hu' v' hv'
  have hSplit' : Kdir u' v' = Kdir u' 0 + Kdir 0 v' := hSplit u' v'
  linarith

/-- Helper for Theorem 35.6: symmetrically, the first marginal together with the second-axis
values already determines the whole subsequential limit on `CU × DV`. -/
lemma helperForTheorem_35_6_subseqLimit_eq_splitKernel_of_firstMarginal
    {m n : ℕ}
    {CU : Set (Fin m → ℝ)} {DV : Set (Fin n → ℝ)}
    {L Kdir : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hAxisSecond : ∀ v' ∈ DV, L 0 v' = Kdir 0 v')
    (hFirstMarginal :
      ∀ u' ∈ CU, ∀ v' ∈ DV, L u' v' - L 0 v' = Kdir u' 0)
    (hSplit : ∀ u' v', Kdir u' v' = Kdir u' 0 + Kdir 0 v') :
    ∀ u' ∈ CU, ∀ v' ∈ DV, L u' v' = Kdir u' v' := by
  intro u' hu' v' hv'
  -- The symmetric marginal identity determines the same split value.
  have hAxis : L 0 v' = Kdir 0 v' := hAxisSecond v' hv'
  have hMarg : L u' v' - L 0 v' = Kdir u' 0 := hFirstMarginal u' hu' v' hv'
  have hSplit' : Kdir u' v' = Kdir u' 0 + Kdir 0 v' := hSplit u' v'
  linarith


end Section35
end Chap07
