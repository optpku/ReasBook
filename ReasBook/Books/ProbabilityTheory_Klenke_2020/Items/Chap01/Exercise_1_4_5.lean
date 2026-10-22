/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Exercise 1.4.5: a real-valued map is continuous on `C` once every rational open
interval has an open preimage in the subspace topology on `C`. -/
lemma continuousOn_of_preimage_eq_open_inter_rat {f : ℝ → ℝ} {C : Set ℝ}
    (hopen :
      ∀ a b : ℚ, a < b → ∃ U : Set ℝ, IsOpen U ∧ C ∩ f ⁻¹' Set.Ioo (a : ℝ) (b : ℝ) = C ∩ U) :
    ContinuousOn f C := by
  -- We prove continuity of the restricted map by checking preimages of a rational interval basis.
  rw [continuousOn_iff_continuous_restrict]
  refine Real.isTopologicalBasis_Ioo_rat.continuous_iff.2 ?_
  intro s hs
  rcases Set.mem_iUnion.1 hs with ⟨a, hs⟩
  rcases Set.mem_iUnion.1 hs with ⟨b, hs⟩
  rcases Set.mem_iUnion.1 hs with ⟨hab, hs⟩
  rw [Set.mem_singleton_iff] at hs
  subst hs
  rcases hopen a b hab with ⟨U, hUOpen, hEq⟩
  have hPreimage :
      (C.restrict f) ⁻¹' Set.Ioo (a : ℝ) (b : ℝ) = Subtype.val ⁻¹' U := by
    ext x
    constructor
    · intro hx
      have hx' : x.1 ∈ C ∩ f ⁻¹' Set.Ioo (a : ℝ) (b : ℝ) := ⟨x.2, hx⟩
      rw [hEq] at hx'
      exact hx'.2
    · intro hx
      have hx' : x.1 ∈ C ∩ U := ⟨x.2, hx⟩
      rw [← hEq] at hx'
      exact hx'.2
  rw [hPreimage]
  exact hUOpen.preimage continuous_subtype_val

/-- Helper for Exercise 1.4.5: the standard cover of `ℝ` by closed unit intervals with integer
endpoints is locally finite. -/
lemma locallyFinite_Icc_intCast_add_one : LocallyFinite (fun z : ℤ ↦ Set.Icc (z : ℝ) (z + 1)) := by
  intro x
  let n : ℤ := Int.floor x
  refine ⟨Set.Ioo (x - 1 / 2) (x + 1 / 2), ?_, ?_⟩
  · -- The symmetric open interval of radius `1/2` is a neighborhood of `x`.
    refine isOpen_Ioo.mem_nhds ?_
    constructor <;> linarith
  · -- Any unit interval meeting that neighborhood has index among `n - 1, n, n + 1`.
    refine (Set.finite_Icc (n - 1) (n + 1)).subset ?_
    intro z hz
    rcases hz with ⟨y, hy, hy'⟩
    have hfloor_le : (n : ℝ) ≤ x := Int.floor_le x
    have hx_lt : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
    have hy_upper : y < (n : ℝ) + 3 / 2 := by
      have hx_upper : x + 1 / 2 < (n : ℝ) + 3 / 2 := by
        linarith
      exact lt_trans hy'.2 hx_upper
    have hz_lt_real : (z : ℝ) < ((n + 2 : ℤ) : ℝ) := by
      have hz_mid : (z : ℝ) < (n : ℝ) + 3 / 2 := lt_of_le_of_lt hy.1 hy_upper
      have hbound : (n : ℝ) + 3 / 2 < ((n + 2 : ℤ) : ℝ) := by norm_num
      exact lt_trans hz_mid hbound
    have hz_lt : z < n + 2 := by
      exact_mod_cast hz_lt_real
    have hy_lower : (n : ℝ) - 1 / 2 < y := by
      have hx_lower : (n : ℝ) - 1 / 2 ≤ x - 1 / 2 := by
        linarith
      exact lt_of_le_of_lt hx_lower hy'.1
    have hz_ge_real : (((n - 1 : ℤ) : ℝ)) < (((z + 1 : ℤ) : ℝ)) := by
      have hz_mid : (n : ℝ) - 1 / 2 < (z : ℝ) + 1 := lt_of_lt_of_le hy_lower hy.2
      have hbound : (((n - 1 : ℤ) : ℝ)) < (n : ℝ) - 1 / 2 := by norm_num
      have hz_mid' : (n : ℝ) - 1 / 2 < (((z + 1 : ℤ) : ℝ)) := by
        simpa using hz_mid
      exact lt_trans hbound hz_mid'
    have hz_ge : n - 1 < z + 1 := by
      exact_mod_cast hz_ge_real
    constructor
    · omega
    · omega

/-- Helper for Exercise 1.4.5: an encodable family with geometric measure bounds has union measure
bounded by the corresponding geometric series. -/
lemma volume_iUnion_le_of_geometric_bound {ι : Type*} [Encodable ι] {s : ι → Set ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hs : ∀ i : ι, volume (s i) < ENNReal.ofReal (c / 2 ^ Encodable.encode i)) :
    volume (⋃ i, s i) ≤ ENNReal.ofReal (2 * c) := by
  have hgeom_nat :
      (fun n : ℕ ↦ (2 * c) / 2 / 2 ^ n) = fun n : ℕ ↦ c / 2 ^ n := by
    funext n
    ring_nf
  have hsummable_nat : Summable (fun n : ℕ ↦ c / 2 ^ n) := by
    simpa [hgeom_nat] using (summable_geometric_two' (2 * c))
  have hsummable_idx : Summable (fun i : ι ↦ c / 2 ^ Encodable.encode i) := by
    exact hsummable_nat.comp_injective Encodable.encode_injective
  have hreal_le :
      (∑' i : ι, c / 2 ^ Encodable.encode i) ≤ ∑' n : ℕ, c / 2 ^ n :=
    tsum_comp_le_tsum_of_inj hsummable_nat (by
      intro n
      positivity) Encodable.encode_injective
  have htsum_nat : ∑' n : ℕ, c / 2 ^ n = 2 * c := by
    simpa [hgeom_nat] using (tsum_geometric_two' (2 * c))
  calc
    volume (⋃ i, s i) ≤ ∑' i : ι, volume (s i) := measure_iUnion_le _
    _ ≤ ∑' i : ι, ENNReal.ofReal (c / 2 ^ Encodable.encode i) := by
      exact ENNReal.tsum_le_tsum fun i ↦ (hs i).le
    _ = ENNReal.ofReal (∑' i : ι, c / 2 ^ Encodable.encode i) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg (by
        intro i
        positivity) hsummable_idx
    _ ≤ ENNReal.ofReal (∑' n : ℕ, c / 2 ^ n) := ENNReal.ofReal_le_ofReal hreal_le
    _ = ENNReal.ofReal (2 * c) := by rw [htsum_nat]

/-- Helper for Exercise 1.4.5: on a closed unit interval, a measurable real-valued map is
continuous on a closed large-measure subset. -/
lemma Measurable.exists_isClosed_continuousOn_Icc_diff_lt_of_pos {f : ℝ → ℝ} (hf : Measurable f)
    (a : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : Set ℝ,
      C ⊆ Set.Icc (a : ℝ) (a + 1) ∧
        IsClosed C ∧
        ContinuousOn f C ∧
        volume (Set.Icc (a : ℝ) (a + 1) \ C) < ENNReal.ofReal δ := by
  classical
  let I : Set ℝ := Set.Icc (a : ℝ) (a + 1)
  let ι : Type := {ab : ℚ × ℚ // ab.1 < ab.2}
  let B : ι → Set ℝ := fun i ↦ Set.Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)
  let step : ι → ℝ := fun i ↦ δ / 16 / 2 ^ Encodable.encode i
  have hstep_pos : ∀ i : ι, 0 < step i := by
    intro i
    dsimp [step]
    positivity
  have hstep_nonneg : ∀ i : ι, 0 ≤ step i := by
    intro i
    exact le_of_lt (hstep_pos i)
  have hA_measurable : ∀ i : ι, MeasurableSet (I ∩ f ⁻¹' B i) := by
    intro i
    refine measurableSet_Icc.inter ?_
    exact hf (isOpen_Ioo.measurableSet)
  have hA_ne_top : ∀ i : ι, volume (I ∩ f ⁻¹' B i) ≠ ⊤ := by
    intro i
    have hfinite : volume (I ∩ f ⁻¹' B i) < ⊤ := by
      have hI : volume I < ⊤ := by
        dsimp [I]
        rw [Real.volume_Icc]
        norm_num
      exact (measure_mono (Set.inter_subset_left : I ∩ f ⁻¹' B i ⊆ I)).trans_lt hI
    exact hfinite.ne
  have hClosedApprox : ∀ i : ι, ∃ F : Set ℝ,
      F ⊆ I ∩ f ⁻¹' B i ∧ IsClosed F ∧ volume ((I ∩ f ⁻¹' B i) \ F) < ENNReal.ofReal (step i) := by
    intro i
    have hstep_ne : ENNReal.ofReal (step i) ≠ 0 := by
      have : 0 < ENNReal.ofReal (step i) := by positivity
      exact this.ne'
    exact (hA_measurable i).exists_isClosed_diff_lt (hA_ne_top i) hstep_ne
  choose F hFsub hFclosed hFmeasure using hClosedApprox
  have hOpenApprox : ∀ i : ι, ∃ U : Set ℝ,
      I ∩ f ⁻¹' B i ⊆ U ∧ IsOpen U ∧ volume (U \ (I ∩ f ⁻¹' B i)) < ENNReal.ofReal (step i) := by
    intro i
    have hstep_ne : ENNReal.ofReal (step i) ≠ 0 := by
      have : 0 < ENNReal.ofReal (step i) := by positivity
      exact this.ne'
    rcases (hA_measurable i).exists_isOpen_diff_lt (hA_ne_top i) hstep_ne with
      ⟨U, hUsub, hUopen, _hUfinite, hUmeasure⟩
    exact ⟨U, hUsub, hUopen, hUmeasure⟩
  choose U hUsub hUopen hUmeasure using hOpenApprox
  let bad : ι → Set ℝ := fun i ↦ U i \ F i
  let C : Set ℝ := I \ ⋃ i, bad i
  have hCsub : C ⊆ I := by
    intro x hx
    exact hx.1
  have hCclosed : IsClosed C := by
    -- The bad sets are open, so removing their union from the closed interval keeps a closed set.
    have hBadOpen : ∀ i : ι, IsOpen (bad i) := by
      intro i
      simpa [bad, Set.diff_eq, Set.inter_comm] using (hUopen i).inter (hFclosed i).isOpen_compl
    have hUnionOpen : IsOpen (⋃ i, bad i) := isOpen_iUnion hBadOpen
    dsimp [C, I]
    simpa [Set.diff_eq, Set.inter_assoc] using (isClosed_Icc.inter hUnionOpen.isClosed_compl)
  have hPreimageEq :
      ∀ i : ι, C ∩ f ⁻¹' B i = C ∩ U i := by
    intro i
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      exact hUsub i ⟨hCsub hx.1, hx.2⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxC : x ∈ C := hx.1
      have hxNotBad : x ∉ bad i := by
        intro hbad
        exact hxC.2 (Set.mem_iUnion.2 ⟨i, hbad⟩)
      have hxF : x ∈ F i := by
        by_contra hxF
        exact hxNotBad ⟨hx.2, hxF⟩
      exact (hFsub i hxF).2
  have hCcont : ContinuousOn f C := by
    -- The rational intervals form a basis, and on `C` their preimages are relatively open.
    refine continuousOn_of_preimage_eq_open_inter_rat ?_
    intro q r hqr
    let i : ι := ⟨(q, r), hqr⟩
    refine ⟨U i, hUopen i, ?_⟩
    simpa [B, i] using hPreimageEq i
  have hbad_measure :
      ∀ i : ι, volume (bad i) < ENNReal.ofReal (δ / 8 / 2 ^ Encodable.encode i) := by
    intro i
    have hsubset :
        bad i ⊆ (U i \ (I ∩ f ⁻¹' B i)) ∪ ((I ∩ f ⁻¹' B i) \ F i) := by
      intro x hx
      by_cases hxA : x ∈ I ∩ f ⁻¹' B i
      · exact Or.inr ⟨hxA, hx.2⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    calc
      volume (bad i) ≤ volume ((U i \ (I ∩ f ⁻¹' B i)) ∪ ((I ∩ f ⁻¹' B i) \ F i)) := by
        exact measure_mono hsubset
      _ ≤ volume (U i \ (I ∩ f ⁻¹' B i)) + volume ((I ∩ f ⁻¹' B i) \ F i) := measure_union_le _ _
      _ < ENNReal.ofReal (step i) + ENNReal.ofReal (step i) := by
        exact ENNReal.add_lt_add (hUmeasure i) (hFmeasure i)
      _ = ENNReal.ofReal (δ / 8 / 2 ^ Encodable.encode i) := by
        rw [← ENNReal.ofReal_add (hstep_nonneg i) (hstep_nonneg i)]
        dsimp [step]
        ring_nf
  have hdiff_subset : I \ C ⊆ ⋃ i, bad i := by
    intro x hx
    have hxC : x ∉ C := hx.2
    by_contra hxBad
    exact hxC ⟨hx.1, hxBad⟩
  have hbadUnion : volume (⋃ i : ι, bad i) ≤ ENNReal.ofReal (δ / 4) := by
    simpa [show 2 * (δ / 8) = δ / 4 by ring_nf] using
      volume_iUnion_le_of_geometric_bound (ι := ι) (s := bad) (c := δ / 8) (by positivity)
        hbad_measure
  refine ⟨C, hCsub, hCclosed, hCcont, ?_⟩
  calc
    volume (I \ C) ≤ volume (⋃ i, bad i) := measure_mono hdiff_subset
    _ ≤ ENNReal.ofReal (δ / 4) := hbadUnion
    _ < ENNReal.ofReal δ := by
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 (by linarith)

/-- Exercise 1.4.5: Lusin's theorem for a Borel measurable map `f : ℝ → ℝ`, asserting that for
every `ε > 0` there is a closed set `C` with `volume Cᶜ < ENNReal.ofReal ε` such that `f` is
continuous on `C` in the relative topology. -/
-- Proof sketch: First prove the claim for indicator functions using inner regularity of Lebesgue
-- measure. Then approximate `f` by simple functions and choose a closed set on which the
-- approximations converge uniformly, so the limit is continuous there.
theorem Measurable.exists_isClosed_continuousOn_compl_lt_of_pos {f : ℝ → ℝ} (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set ℝ, IsClosed C ∧ ContinuousOn f C ∧ volume Cᶜ < ENNReal.ofReal ε := by
  classical
  let I : ℤ → Set ℝ := fun z ↦ Set.Icc (z : ℝ) (z + 1)
  have hlocal :
      ∀ z : ℤ, ∃ C : Set ℝ,
        C ⊆ I z ∧ IsClosed C ∧ ContinuousOn f C ∧
          volume (I z \ C) < ENNReal.ofReal (ε / 4 / 2 ^ Encodable.encode z) := by
    intro z
    have hbudget : 0 < ε / 4 / 2 ^ Encodable.encode z := by
      positivity
    simpa [I] using hf.exists_isClosed_continuousOn_Icc_diff_lt_of_pos z hbudget
  choose C hCsub hCclosed hCcont hCmeasure using hlocal
  let K : Set ℝ := ⋃ z : ℤ, C z
  have hlocIntervals : LocallyFinite I := by
    simpa [I] using locallyFinite_Icc_intCast_add_one
  have hlocC : LocallyFinite C := hlocIntervals.subset hCsub
  have hKclosed : IsClosed K := by
    simpa [K] using hlocC.isClosed_iUnion hCclosed
  have hKcont : ContinuousOn f K := by
    simpa [K] using hlocC.continuousOn_iUnion hCclosed hCcont
  have hcover : (⋃ z : ℤ, I z) = Set.univ := by
    simpa [I] using (iUnion_Icc_intCast ℝ)
  have hcompl_subset : Kᶜ ⊆ ⋃ z : ℤ, I z \ C z := by
    intro x hx
    have hxCover : x ∈ ⋃ z : ℤ, I z := by
      rw [hcover]
      trivial
    rcases Set.mem_iUnion.1 hxCover with ⟨z, hz⟩
    refine Set.mem_iUnion.2 ⟨z, ?_⟩
    refine ⟨hz, ?_⟩
    intro hxC
    exact hx (Set.mem_iUnion.2 ⟨z, hxC⟩)
  have hglobalUnion :
      volume (⋃ z : ℤ, I z \ C z) ≤ ENNReal.ofReal (ε / 2) := by
    simpa [show 2 * (ε / 4) = ε / 2 by ring_nf] using
      volume_iUnion_le_of_geometric_bound (ι := ℤ) (s := fun z ↦ I z \ C z) (c := ε / 4)
        (by positivity) hCmeasure
  refine ⟨K, hKclosed, hKcont, ?_⟩
  calc
    volume Kᶜ ≤ volume (⋃ z : ℤ, I z \ C z) := measure_mono hcompl_subset
    _ ≤ ENNReal.ofReal (ε / 2) := hglobalUnion
    _ < ENNReal.ofReal ε := by
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
