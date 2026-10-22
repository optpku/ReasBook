/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.8: once the admissible fixed-step quotient convergence is available,
the monotonicity/sInf description of directional derivatives yields the limsup inequality. -/
lemma helperForTheorem_5_24_8_limsup_le_upperDirectionalDerivative_via_sInf
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C)
    (hx_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)))
    (y : Fin n → ℝ) (ySeq : ℕ → Fin n → ℝ)
    (hy_tendsto : Filter.Tendsto ySeq Filter.atTop (nhds y)) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
      Filter.atTop ≤ upperDirectionalDerivativeAt f x y := by
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := hf_finite x hx
  have hxSeqFinite : ∀ i, fSeq i (xSeq i) ≠ (⊤ : EReal) ∧ fSeq i (xSeq i) ≠ (⊥ : EReal) := by
    intro i
    exact hfSeq_finite i (xSeq i) (hxSeq i)
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
  have himage_nonempty :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t).Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f x y 1, ?_⟩
    exact ⟨1, by simpa, rfl⟩
  rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y (hdirData y).1]
  refine le_csInf himage_nonempty ?_
  rintro q ⟨s, hspos, rfl⟩
  rcases helperForTheorem_5_24_8_exists_small_step_mem_open hCopen hx (y := y) hspos with
    ⟨t, htpos, htle, ht_mem⟩
  have hstep_tendsto :
      Filter.Tendsto (fun i => xSeq i + t • ySeq i) Filter.atTop (nhds (x + t • y)) := by
    -- The translated moving points converge to the translated limit point.
    simpa using hx_tendsto.add (hy_tendsto.const_smul t)
  have hstep_mem :
      ∀ᶠ i in Filter.atTop, xSeq i + t • ySeq i ∈ C :=
    hstep_tendsto (hCopen.mem_nhds ht_mem)
  have hstepFinite :
      ∀ᶠ i in Filter.atTop,
        fSeq i (xSeq i + t • ySeq i) ≠ (⊤ : EReal) ∧
          fSeq i (xSeq i + t • ySeq i) ≠ (⊥ : EReal) := by
    filter_upwards [hstep_mem] with i hi
    exact hfSeq_finite i _ hi
  have hquot :=
    helperForTheorem_5_24_8_fixedStepQuotient_tendsto
      hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hx_tendsto hpoint
      ySeq hy_tendsto htpos ht_mem hstep_mem
  have htFinite : f (x + t • y) ≠ (⊤ : EReal) ∧ f (x + t • y) ≠ (⊥ : EReal) :=
    hf_finite (x + t • y) ht_mem
  have hquot_t :
      directionalDifferenceQuotientAt f x y t =
        ((((f (x + t • y)).toReal - (f x).toReal) / t : ℝ) : EReal) := by
    -- At the admissible step, both endpoint values are finite, so the extended-real quotient
    -- reduces to the ordinary real secant quotient.
    simp [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal htFinite.1 htFinite.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  have hlimsup_t :
      Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
        Filter.atTop ≤ directionalDifferenceQuotientAt f x y t := by
    rw [hquot_t]
    exact
      helperForTheorem_5_24_8_limsup_le_fixedStepRealQuotient
        fSeq hfSeq xSeq ySeq hxSeqFinite htpos hstepFinite hquot
  have hmonoStep :
      directionalDifferenceQuotientAt f x y t ≤ directionalDifferenceQuotientAt f x y s :=
    (hdirData y).1 htpos hspos htle
  exact le_trans hlimsup_t hmonoStep

/-- Helper for Theorem 5.24.8: a subgradient inequality tested on the signed standard basis
controls the corresponding coordinates of the representing vector. -/
lemma helperForTheorem_5_24_8_subgradient_coordinate_bounds_in_signed_basis
    {n : ℕ} {g : (Fin n → ℝ) → EReal} (hg : ConvexFunction g)
    {z : Fin n → ℝ} (hzFinite : g z ≠ (⊤ : EReal) ∧ g z ≠ (⊥ : EReal))
    {v : Fin n → ℝ} (hv : dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt g z)
    (j : Fin n) :
    (((v j : ℝ) : EReal) ≤ upperDirectionalDerivativeAt g z (Pi.single j 1)) ∧
      (((-(v j) : ℝ) : EReal) ≤
        upperDirectionalDerivativeAt g z (-(Pi.single j 1 : Fin n → ℝ))) := by
  -- Rewrite subgradient membership as the directional-minorant property from Section 23.
  have hminorant :
      ∀ y : Fin n → ℝ,
        (((dotProductEquiv ℝ (Fin n) v) y : ℝ) : EReal) ≤ upperDirectionalDerivativeAt g z y :=
    by
      have hiff :=
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          g hg z hzFinite (dotProductEquiv ℝ (Fin n) v)).1
      exact hiff.1 hv
  constructor
  · -- Evaluating on `e_j` reads off the `j`th coordinate of `v`.
    simpa [dotProductEquiv_apply_apply] using hminorant (Pi.single j 1)
  · -- Evaluating on `-e_j` gives the corresponding lower-coordinate control.
    simpa [dotProductEquiv_apply_apply] using
      hminorant (-(Pi.single j 1 : Fin n → ℝ))

/-- Helper for Theorem 5.24.8: a bad subgradient sequence along a strict-mono bad index sequence
admits a convergent further subsequence, because the signed basis limsup bounds force one common
closed ball. -/
lemma helperForTheorem_5_24_8_badSubgradient_convergent_subseq_of_basis_limsup
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C)
    (hlimsup :
      ∀ y : Fin n → ℝ, ∀ ySeq : ℕ → Fin n → ℝ,
        Filter.Tendsto ySeq Filter.atTop (nhds y) →
          Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
            Filter.atTop ≤ upperDirectionalDerivativeAt f x y)
    (Aε : Set (Fin n → ℝ))
    (ι : ℕ → ℕ) (hι : StrictMono ι)
    (vBad : ℕ → Fin n → ℝ)
    (hvBadSub :
      ∀ k, dotProductEquiv ℝ (Fin n) (vBad k) ∈ subdifferentialAt (fSeq (ι k)) (xSeq (ι k)))
    (hvBadOut : ∀ k, vBad k ∉ Aε) :
    ∃ N : ℕ, ∃ φ : ℕ → ℕ, ∃ v : Fin n → ℝ,
      StrictMono φ ∧
      Filter.Tendsto (fun k => vBad (N + φ k)) Filter.atTop (nhds v) ∧
      (∀ k,
        dotProductEquiv ℝ (Fin n) (vBad (N + φ k)) ∈
          subdifferentialAt (fSeq (ι (N + φ k))) (xSeq (ι (N + φ k)))) ∧
      (∀ k, vBad (N + φ k) ∉ Aε) := by
  let basisPos : Fin n → ℝ := fun j =>
    |(upperDirectionalDerivativeAt f x (Pi.single j 1)).toReal| + 1
  let basisNeg : Fin n → ℝ := fun j =>
    |(upperDirectionalDerivativeAt f x (-(Pi.single j 1 : Fin n → ℝ))).toReal| + 1
  let radiusTerm : Fin n → ℝ := fun j => max (basisPos j) (basisNeg j)
  let R : ℝ := ∑ j, radiusTerm j
  have hR_nonneg : 0 ≤ R := by
    -- The radius is a sum of positive signed-basis bounds.
    refine Finset.sum_nonneg ?_
    intro j hj
    have hPos_nonneg : 0 ≤ basisPos j := by
      positivity
    exact le_trans hPos_nonneg (le_max_left _ _)
  have hdirFinite :=
    helperForTheorem_5_24_8_directionalDerivative_finite_at_limit_and_sequence
      hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq
  have hxSeqFinite : ∀ k,
      fSeq (ι k) (xSeq (ι k)) ≠ (⊤ : EReal) ∧
        fSeq (ι k) (xSeq (ι k)) ≠ (⊥ : EReal) := by
    intro k
    exact hfSeq_finite (ι k) (xSeq (ι k)) (hxSeq (ι k))
  have hradius_le_sum : ∀ j : Fin n, radiusTerm j ≤ R := by
    intro j
    exact
      Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := radiusTerm)
        (fun i _ => by
          have hPos_nonneg : 0 ≤ basisPos i := by
            positivity
          exact le_trans hPos_nonneg (le_max_left _ _))
        (by simp)
  have hcoordEventually : ∀ j : Fin n, ∀ᶠ k in Filter.atTop, ‖vBad k j‖ ≤ R := by
    intro j
    let e : Fin n → ℝ := Pi.single j 1
    have hlimitPosFinite :
        upperDirectionalDerivativeAt f x e ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt f x e ≠ (⊥ : EReal) := hdirFinite.1 e
    have hlimitNegFinite :
        upperDirectionalDerivativeAt f x (-e) ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt f x (-e) ≠ (⊥ : EReal) := hdirFinite.1 (-e)
    have hsubseqLimsupPos :
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) e)
            Filter.atTop ≤
          upperDirectionalDerivativeAt f x e := by
      calc
        -- Expose the subsequence explicitly as a composition before applying `limsup_comp`.
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) e)
            Filter.atTop =
            Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) e)
              (Filter.map ι Filter.atTop) := by
                change Filter.limsup
                    ((fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) e) ∘ ι)
                    Filter.atTop =
                  Filter.limsup
                    (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) e)
                    (Filter.map ι Filter.atTop)
                simpa using
                  (Filter.limsup_comp
                    (u := fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) e)
                    (v := ι) (f := Filter.atTop))
        _ ≤ Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) e)
              Filter.atTop := by
                exact Filter.limsup_le_limsup_of_le hι.tendsto_atTop
        _ ≤ upperDirectionalDerivativeAt f x e := by
          exact hlimsup e (fun _ => e) (by simpa using Filter.tendsto_const_nhds)
    have hsubseqLimsupNeg :
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) (-e))
            Filter.atTop ≤
          upperDirectionalDerivativeAt f x (-e) := by
      calc
        -- The same filter transport works for the negative signed basis direction.
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) (-e))
            Filter.atTop =
            Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (-e))
              (Filter.map ι Filter.atTop) := by
                change Filter.limsup
                    ((fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (-e)) ∘ ι)
                    Filter.atTop =
                  Filter.limsup
                    (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (-e))
                    (Filter.map ι Filter.atTop)
                simpa using
                  (Filter.limsup_comp
                    (u := fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (-e))
                    (v := ι) (f := Filter.atTop))
        _ ≤ Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (-e))
              Filter.atTop := by
                exact Filter.limsup_le_limsup_of_le hι.tendsto_atTop
        _ ≤ upperDirectionalDerivativeAt f x (-e) := by
          exact hlimsup (-e) (fun _ => -e) (by simpa using Filter.tendsto_const_nhds)
    have hlimitPosLt :
        upperDirectionalDerivativeAt f x e < ((basisPos j : ℝ) : EReal) := by
      rw [show upperDirectionalDerivativeAt f x e =
          (((upperDirectionalDerivativeAt f x e).toReal : ℝ) : EReal) by
            simp [EReal.coe_toReal hlimitPosFinite.1 hlimitPosFinite.2]]
      exact_mod_cast
        (lt_of_le_of_lt (le_abs_self _)
          (lt_add_of_pos_right _ zero_lt_one))
    have hlimitNegLt :
        upperDirectionalDerivativeAt f x (-e) < ((basisNeg j : ℝ) : EReal) := by
      rw [show upperDirectionalDerivativeAt f x (-e) =
          (((upperDirectionalDerivativeAt f x (-e)).toReal : ℝ) : EReal) by
            simp [EReal.coe_toReal hlimitNegFinite.1 hlimitNegFinite.2]]
      exact_mod_cast
        (lt_of_le_of_lt (le_abs_self _)
          (lt_add_of_pos_right _ zero_lt_one))
    have hposEvent :
        ∀ᶠ k in Filter.atTop,
          upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) e <
            ((basisPos j : ℝ) : EReal) :=
      Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hsubseqLimsupPos hlimitPosLt)
    have hnegEvent :
        ∀ᶠ k in Filter.atTop,
          upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) (-e) <
            ((basisNeg j : ℝ) : EReal) :=
      Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hsubseqLimsupNeg hlimitNegLt)
    filter_upwards [hposEvent, hnegEvent] with k hkPos hkNeg
    have hcoordBounds :=
      helperForTheorem_5_24_8_subgradient_coordinate_bounds_in_signed_basis
        (hg := hfSeq (ι k)) (z := xSeq (ι k)) (hzFinite := hxSeqFinite k) (hv := hvBadSub k) j
    have hupperCoord_lt : vBad k j < basisPos j := by
      exact_mod_cast (lt_of_le_of_lt hcoordBounds.1 hkPos)
    have hnegCoord_lt : -(vBad k j) < basisNeg j := by
      exact_mod_cast (lt_of_le_of_lt hcoordBounds.2 hkNeg)
    have hupperCoord : vBad k j ≤ basisPos j := hupperCoord_lt.le
    have hnegCoord : -(vBad k j) ≤ basisNeg j := hnegCoord_lt.le
    have hupperRadius : vBad k j ≤ radiusTerm j :=
      le_trans hupperCoord (le_max_left _ _)
    have hlowerRadius : -(radiusTerm j) ≤ vBad k j := by
      have hnegRadius : -(vBad k j) ≤ radiusTerm j :=
        le_trans hnegCoord (le_max_right _ _)
      linarith
    have hnormCoord : ‖vBad k j‖ ≤ radiusTerm j := by
      simpa [Real.norm_eq_abs] using (abs_le.2 ⟨hlowerRadius, hupperRadius⟩)
    exact le_trans hnormCoord (hradius_le_sum j)
  have hcoordAll :
      ∀ᶠ k in Filter.atTop, ∀ j : Fin n, ‖vBad k j‖ ≤ R := by
    have hfiniteAll :
        ∀ᶠ k in Filter.atTop, ∀ j ∈ (Finset.univ : Finset (Fin n)), ‖vBad k j‖ ≤ R := by
      exact
        (Finset.eventually_all
          (I := (Finset.univ : Finset (Fin n)))
          (l := Filter.atTop)
          (p := fun j k => ‖vBad k j‖ ≤ R)).2
          (by
            intro j hj
            simpa using hcoordEventually j)
    filter_upwards [hfiniteAll] with k hk j
    exact hk j (by simp)
  have hnormEventually : ∀ᶠ k in Filter.atTop, ‖vBad k‖ ≤ R := by
    filter_upwards [hcoordAll] with k hk
    exact (pi_norm_le_iff_of_nonneg (x := (vBad k : Fin n → ℝ)) (r := R) hR_nonneg).2 hk
  rcases Filter.eventually_atTop.mp hnormEventually with ⟨N, hN⟩
  let tail : ℕ → Fin n → ℝ := fun k => vBad (N + k)
  have htailMem : ∀ k, tail k ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
    intro k
    have hnorm : ‖vBad (N + k)‖ ≤ R := hN (N + k) (Nat.le_add_right N k)
    simpa [tail, Metric.mem_closedBall] using hnorm
  rcases (isCompact_closedBall (0 : Fin n → ℝ) R).tendsto_subseq htailMem with
    ⟨v, _hvBall, φ, hφ, hφ_tendsto⟩
  refine ⟨N, φ, v, hφ, ?_, ?_, ?_⟩
  · -- The compactness step gives convergence of the tailed bad subgradients.
    simpa [tail, Function.comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hφ_tendsto
  · -- Subgradient membership is preserved along the chosen tail and subsequence.
    intro k
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hvBadSub (N + φ k)
  · -- The same is true for the badness condition.
    intro k
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hvBadOut (N + φ k)

/-- Helper for Theorem 5.24.8: a convergent subsequence of subgradients whose directional
minorants are controlled by the limsup bound has its limit in `∂ f(x)`. -/
lemma helperForTheorem_5_24_8_clusterPoint_mem_subdifferential_of_directional_bounds
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C)
    (hlimsup :
      ∀ y : Fin n → ℝ, ∀ ySeq : ℕ → Fin n → ℝ,
        Filter.Tendsto ySeq Filter.atTop (nhds y) →
          Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
            Filter.atTop ≤ upperDirectionalDerivativeAt f x y)
    (ι : ℕ → ℕ) (hι : StrictMono ι)
    (vSeq : ℕ → Fin n → ℝ) {v : Fin n → ℝ}
    (hv_tendsto : Filter.Tendsto vSeq Filter.atTop (nhds v))
    (hvSub :
      ∀ k, dotProductEquiv ℝ (Fin n) (vSeq k) ∈
        subdifferentialAt (fSeq (ι k)) (xSeq (ι k))) :
    dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x := by
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := hf_finite x hx
  have hxSeqFinite : ∀ k,
      fSeq (ι k) (xSeq (ι k)) ≠ (⊤ : EReal) ∧
        fSeq (ι k) (xSeq (ι k)) ≠ (⊥ : EReal) := by
    intro k
    exact hfSeq_finite (ι k) (xSeq (ι k)) (hxSeq (ι k))
  have hsubgradientIff :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite (dotProductEquiv ℝ (Fin n) v)
  -- Show that the limit vector keeps the directional-minorant inequalities in every direction.
  have hminorant :
      ∀ y : Fin n → ℝ,
        (((dotProductEquiv ℝ (Fin n) v) y : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y := by
    intro y
    have hdot_tendsto_real :
        Filter.Tendsto (fun k => dotProduct (vSeq k) y) Filter.atTop (nhds (dotProduct v y)) := by
      -- The pairing with a fixed direction is continuous, so it respects the vector limit.
      have hcont : Continuous fun w : Fin n → ℝ => dotProduct w y := by
        continuity
      simpa using hcont.continuousAt.tendsto.comp hv_tendsto
    have hdot_tendsto :
        Filter.Tendsto
            (fun k => (((dotProduct (vSeq k) y : ℝ) : EReal)))
            Filter.atTop
            (nhds (((dotProduct v y : ℝ) : EReal))) :=
      helperForTheorem_5_24_8_tendsto_coe_of_tendsto hdot_tendsto_real
    have hpointwise :
        ∀ k,
          (((dotProduct (vSeq k) y : ℝ) : EReal)) ≤
            upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) y := by
      intro k
      have hminorantK :
          ∀ z : Fin n → ℝ,
            (((dotProductEquiv ℝ (Fin n) (vSeq k)) z : ℝ) : EReal) ≤
              upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) z :=
        by
          have hiff :=
            (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
              (fSeq (ι k)) (hfSeq (ι k)) (xSeq (ι k)) (hxSeqFinite k)
              (dotProductEquiv ℝ (Fin n) (vSeq k))).1
          exact hiff.1 (hvSub k)
      simpa [dotProductEquiv_apply_apply] using hminorantK y
    have hsubseqLimsup :
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) y)
            Filter.atTop ≤
          upperDirectionalDerivativeAt f x y := by
      calc
        -- Transport the limsup bound from the original sequence to the strict-mono subsequence.
        Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) y)
            Filter.atTop =
            Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) y)
              (Filter.map ι Filter.atTop) := by
                change Filter.limsup
                    ((fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) y) ∘ ι)
                    Filter.atTop =
                  Filter.limsup
                    (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) y)
                    (Filter.map ι Filter.atTop)
                simpa using
                  (Filter.limsup_comp
                    (u := fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) y)
                    (v := ι) (f := Filter.atTop))
        _ ≤ Filter.limsup
              (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) y)
              Filter.atTop := by
                exact Filter.limsup_le_limsup_of_le hι.tendsto_atTop
        _ ≤ upperDirectionalDerivativeAt f x y := by
          exact hlimsup y (fun _ => y) (by simpa using Filter.tendsto_const_nhds)
    calc
      (((dotProductEquiv ℝ (Fin n) v) y : ℝ) : EReal) =
          Filter.limsup (fun k => (((dotProduct (vSeq k) y : ℝ) : EReal))) Filter.atTop := by
            symm
            simpa [dotProductEquiv_apply_apply] using hdot_tendsto.limsup_eq
      _ ≤ Filter.limsup
            (fun k => upperDirectionalDerivativeAt (fSeq (ι k)) (xSeq (ι k)) y)
            Filter.atTop := by
              exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hpointwise)
      _ ≤ upperDirectionalDerivativeAt f x y := hsubseqLimsup
  -- Convert the directional inequalities back to subgradient membership.
  exact hsubgradientIff.1.2 hminorant

/-- Helper for Theorem 5.24.8: after the directional-derivative limsup inequality is known in
every direction, a bad subgradient subsequence contradicts the closedness of `∂ f (x)`. -/
lemma helperForTheorem_5_24_8_eventual_subdifferential_subset_of_limsup
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C)
    (hx_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z)))
    (hlimsup :
      ∀ y : Fin n → ℝ, ∀ ySeq : ℕ → Fin n → ℝ,
        Filter.Tendsto ySeq Filter.atTop (nhds y) →
          Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
            Filter.atTop ≤ upperDirectionalDerivativeAt f x y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ i0 : ℕ, ∀ i ≥ i0,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fSeq i) (xSeq i)) ⊆
        Set.image2 (fun u v => u + v)
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
          {v : Fin n → ℝ | ‖v‖ ≤ ε} := by
  let targetSet : Set (Fin n → ℝ) :=
    Set.image2 (fun u v => u + v)
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
      {v : Fin n → ℝ | ‖v‖ ≤ ε}
  by_contra hfail
  have hnotEventually :
      ¬ ∀ᶠ i in Filter.atTop,
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fSeq i) (xSeq i)) ⊆ targetSet := by
    -- Negating the eventual inclusion gives infinitely many bad indices.
    simpa [Filter.eventually_atTop, targetSet] using hfail
  have hfreqBad :
      ∃ᶠ i in Filter.atTop,
        ¬ (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fSeq i) (xSeq i)) ⊆ targetSet) :=
    (Filter.not_eventually).1 hnotEventually
  rcases Filter.extraction_of_frequently_atTop hfreqBad with ⟨ι, hι, hbadι⟩
  have hbadWitness :
      ∀ k, ∃ v : Fin n → ℝ,
        v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fSeq (ι k)) (xSeq (ι k))) ∧
          v ∉ targetSet := by
    intro k
    simpa [Set.not_subset] using hbadι k
  choose vBad hvBadSub hvBadOut using hbadWitness
  rcases
      helperForTheorem_5_24_8_badSubgradient_convergent_subseq_of_basis_limsup
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hlimsup targetSet
        ι hι vBad hvBadSub hvBadOut with
    ⟨N, φ, v, hφ, hv_tendsto, hvSubTail, hvOutTail⟩
  have hshiftφ : StrictMono (fun k => N + φ k) := by
    intro a b hab
    exact Nat.add_lt_add_left (hφ hab) N
  have hιTail : StrictMono (fun k => ι (N + φ k)) :=
    hι.comp hshiftφ
  have hv_mem_subdiff :
      dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x :=
    helperForTheorem_5_24_8_clusterPoint_mem_subdifferential_of_directional_bounds
      hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hlimsup
      (fun k => ι (N + φ k)) hιTail (fun k => vBad (N + φ k)) hv_tendsto hvSubTail
  have hv_mem_preimage :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
    simpa using hv_mem_subdiff
  have hnearTarget :
      ∀ᶠ k in Filter.atTop, vBad (N + φ k) ∈ targetSet := by
    -- Once the bad subsequence converges to a genuine subgradient, the `ε`-ball catches it.
    have hnear :
        ∀ᶠ k in Filter.atTop, vBad (N + φ k) ∈ Metric.closedBall v ε :=
      hv_tendsto (Metric.closedBall_mem_nhds v hε)
    filter_upwards [hnear] with k hk
    have hball : ‖vBad (N + φ k) - v‖ ≤ ε := by
      simpa [Metric.mem_closedBall] using hk
    exact
      ⟨v, hv_mem_preimage, vBad (N + φ k) - v, hball, by abel⟩
  have havoidTarget :
      ∀ᶠ k in Filter.atTop, vBad (N + φ k) ∉ targetSet :=
    Filter.Eventually.of_forall hvOutTail
  have hFalse : ∀ᶠ k in (Filter.atTop : Filter ℕ), False := by
    filter_upwards [hnearTarget, havoidTarget] with k hkMem hkNot
    exact hkNot hkMem
  rw [Filter.eventually_atTop] at hFalse
  rcases hFalse with ⟨K, hK⟩
  exact hK K le_rfl

/-- Theorem 5.24.8: let `f` be a convex function on `ℝ^n` that is finite on an open convex set
`C ⊆ ℝ^n`, and let `fᵢ` be convex functions on `ℝ^n` that are finite on `C`, converging
pointwise to `f` on `C`. If `x ∈ C`,
`xᵢ ∈ C` with `xᵢ → x`, and `yᵢ → y`, then
`limsup fᵢ'(xᵢ; yᵢ) ≤ f'(x; y)`. Moreover, for every `ε > 0`, the subdifferentials
`∂ fᵢ(xᵢ)` are eventually contained in `∂ f(x) + ε B`; in Lean this inclusion is written after
identifying covectors with vectors via `dotProductEquiv ℝ (Fin n)`. -/
theorem convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
    {n : ℕ} {C : Set (Fin n → ℝ)} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : (Fin n → ℝ) → EReal} (hf : ConvexFunction f)
    (hf_finite : ∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (fSeq : ℕ → (Fin n → ℝ) → EReal) (hfSeq : ∀ i, ConvexFunction (fSeq i))
    (hfSeq_finite : ∀ i, ∀ z ∈ C, fSeq i z ≠ (⊤ : EReal) ∧ fSeq i z ≠ (⊥ : EReal))
    {x : Fin n → ℝ} (hx : x ∈ C) (xSeq : ℕ → Fin n → ℝ) (hxSeq : ∀ i, xSeq i ∈ C)
    (hx_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds x))
    (hpoint : ∀ z ∈ C, Filter.Tendsto (fun i => fSeq i z) Filter.atTop (nhds (f z))) :
    (∀ y : Fin n → ℝ, ∀ ySeq : ℕ → Fin n → ℝ,
      Filter.Tendsto ySeq Filter.atTop (nhds y) →
        Filter.limsup (fun i => upperDirectionalDerivativeAt (fSeq i) (xSeq i) (ySeq i))
          Filter.atTop ≤ upperDirectionalDerivativeAt f x y) ∧
      ∀ ε : ℝ, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0,
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fSeq i) (xSeq i)) ⊆
          Set.image2 (fun u v => u + v)
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
            {v : Fin n → ℝ | ‖v‖ ≤ ε} := by
  constructor
  · intro y ySeq hy_tendsto
    -- First isolate the limsup inequality as the Chapter 10 analytic step plus the Chapter 23
    -- monotonicity/`sInf` packaging.
    exact
      helperForTheorem_5_24_8_limsup_le_upperDirectionalDerivative_via_sInf
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hx_tendsto hpoint
        y ySeq hy_tendsto
  · intro ε hε
    -- Then feed that directional control into the standard bad-subgradient subsequence argument.
    exact
      helperForTheorem_5_24_8_eventual_subdifferential_subset_of_limsup
        hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hx_tendsto hpoint
        (fun y ySeq hy_tendsto =>
          helperForTheorem_5_24_8_limsup_le_upperDirectionalDerivative_via_sInf
            hCopen hCconv hf hf_finite fSeq hfSeq hfSeq_finite hx xSeq hxSeq hx_tendsto hpoint
            y ySeq hy_tendsto)
        ε hε


end Section24
end Chap05
