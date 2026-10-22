/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u}

/-- Helper for the Lusin-type continuity criterion: a real-valued map is continuous on `C` once
every rational open
interval has an open preimage in the subspace topology on `C`. -/
lemma continuousOn_of_preimage_eq_open_inter_rat [TopologicalSpace Ω] {f : Ω → ℝ} {C : Set Ω}
    (hopen :
      ∀ a b : ℚ, a < b → ∃ U : Set Ω, IsOpen U ∧ C ∩ f ⁻¹' Set.Ioo (a : ℝ) (b : ℝ) = C ∩ U) :
    ContinuousOn f C := by
  -- We prove continuity of the restricted map by checking a rational interval basis.
  rw [continuousOn_iff_continuous_restrict]
  refine (Real.isTopologicalBasis_Ioo_rat).continuous_iff.2 ?_
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

/-- Helper for the Lusin-type continuity criterion: an encodable family with geometric measure
bounds has union measure
bounded by the corresponding geometric series. -/
lemma measure_iUnion_le_of_geometric_bound [MeasurableSpace Ω] {ι : Type*} [Encodable ι]
    {μ : Measure Ω}
    {s : ι → Set Ω} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ i : ι, μ (s i) < ENNReal.ofReal (c / 2 ^ Encodable.encode i)) :
    μ (⋃ i, s i) ≤ ENNReal.ofReal (2 * c) := by
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
    μ (⋃ i, s i) ≤ ∑' i : ι, μ (s i) := measure_iUnion_le _
    _ ≤ ∑' i : ι, ENNReal.ofReal (c / 2 ^ Encodable.encode i) := by
      exact ENNReal.tsum_le_tsum fun i ↦ (hs i).le
    _ = ENNReal.ofReal (∑' i : ι, c / 2 ^ Encodable.encode i) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg (by
        intro i
        positivity) hsummable_idx
    _ ≤ ENNReal.ofReal (∑' n : ℕ, c / 2 ^ n) := ENNReal.ofReal_le_ofReal hreal_le
    _ = ENNReal.ofReal (2 * c) := by rw [htsum_nat]

/-- Helper for the finite-measure compact form of Lusin's theorem: a measurable real-valued map on
a Polish space is continuous on a
compact set whose complement has arbitrarily small finite measure. -/
lemma Measurable.exists_isCompact_continuousOn_compl_lt_of_pos [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set Ω, IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  classical
  let ι : Type := {ab : ℚ × ℚ // ab.1 < ab.2}
  let B : ι → Set ℝ := fun i ↦ Set.Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)
  let step : ι → ℝ := fun i ↦ ε / 16 / 2 ^ Encodable.encode i
  have hstep_pos : ∀ i : ι, 0 < step i := by
    intro i
    dsimp [step]
    positivity
  have hstep_nonneg : ∀ i : ι, 0 ≤ step i := by
    intro i
    exact le_of_lt (hstep_pos i)
  have hεhalf : 0 < ENNReal.ofReal (ε / 2) := by
    positivity
  -- We first choose a compact core with small complement.
  obtain ⟨S, hScompact, hScompl⟩ :=
    exists_isCompact_closure_measure_compl_lt μ (ENNReal.ofReal (ε / 2)) hεhalf
  let T : Set Ω := closure S
  have hTcompact : IsCompact T := by
    simpa [T] using hScompact
  have hTmeas : MeasurableSet T := hTcompact.measurableSet
  have hTcompl : μ Tᶜ < ENNReal.ofReal (ε / 2) := by
    refine (measure_mono ?_).trans_lt hScompl
    exact Set.compl_subset_compl.2 subset_closure
  let A : ι → Set Ω := fun i ↦ T ∩ f ⁻¹' B i
  have hAmeas : ∀ i : ι, MeasurableSet (A i) := by
    intro i
    exact hTmeas.inter (hf (isOpen_Ioo.measurableSet))
  have hAneTop : ∀ i : ι, μ (A i) ≠ ⊤ := by
    intro i
    exact measure_ne_top μ (A i)
  -- We approximate each rational-interval preimage from inside by a compact set.
  have hCompactApprox :
      ∀ i : ι, ∃ F : Set Ω,
        F ⊆ A i ∧ IsCompact F ∧ μ (A i \ F) < ENNReal.ofReal (step i) := by
    intro i
    have hstep_ne : ENNReal.ofReal (step i) ≠ 0 := by
      positivity
    exact (hAmeas i).exists_isCompact_diff_lt (hAneTop i) hstep_ne
  choose F hFsub hFcompact hFmeasure using hCompactApprox
  -- We also approximate from outside by open sets with the same error budget.
  have hOpenApprox :
      ∀ i : ι, ∃ U : Set Ω,
        A i ⊆ U ∧ IsOpen U ∧ μ (U \ A i) < ENNReal.ofReal (step i) := by
    intro i
    have hstep_ne : ENNReal.ofReal (step i) ≠ 0 := by
      positivity
    rcases (hAmeas i).exists_isOpen_diff_lt (hAneTop i) hstep_ne with
      ⟨U, hAU, hUopen, _hUfinite, hUmeasure⟩
    exact ⟨U, hAU, hUopen, hUmeasure⟩
  choose U hUsub hUopen hUmeasure using hOpenApprox
  let bad : ι → Set Ω := fun i ↦ U i \ F i
  let K : Set Ω := T \ ⋃ i, bad i
  have hKsub : K ⊆ T := by
    intro x hx
    exact hx.1
  have hBadOpen : ∀ i : ι, IsOpen (bad i) := by
    intro i
    exact (hUopen i).sdiff (hFcompact i).isClosed
  have hKclosed : IsClosed K := by
    exact hTcompact.isClosed.sdiff (isOpen_iUnion hBadOpen)
  have hKcompact : IsCompact K := hTcompact.of_isClosed_subset hKclosed hKsub
  have hPreimageEq :
      ∀ i : ι, K ∩ f ⁻¹' B i = K ∩ U i := by
    intro i
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      exact hUsub i ⟨hKsub hx.1, hx.2⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxNotBad : x ∉ bad i := by
        intro hbad
        exact hx.1.2 (Set.mem_iUnion.2 ⟨i, hbad⟩)
      have hxF : x ∈ F i := by
        by_contra hxF
        exact hxNotBad ⟨hx.2, hxF⟩
      exact (hFsub i hxF).2
  have hKcont : ContinuousOn f K := by
    -- The rational intervals form a basis, and on `K` their preimages are relatively open.
    refine continuousOn_of_preimage_eq_open_inter_rat ?_
    intro q r hqr
    let i : ι := ⟨(q, r), hqr⟩
    refine ⟨U i, hUopen i, ?_⟩
    simpa [B, i] using hPreimageEq i
  have hbad_measure :
      ∀ i : ι, μ (bad i) < ENNReal.ofReal (ε / 8 / 2 ^ Encodable.encode i) := by
    intro i
    have hsubset :
        bad i ⊆ (U i \ A i) ∪ (A i \ F i) := by
      intro x hx
      by_cases hxA : x ∈ A i
      · exact Or.inr ⟨hxA, hx.2⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    calc
      μ (bad i) ≤ μ ((U i \ A i) ∪ (A i \ F i)) := measure_mono hsubset
      _ ≤ μ (U i \ A i) + μ (A i \ F i) := measure_union_le _ _
      _ < ENNReal.ofReal (step i) + ENNReal.ofReal (step i) := by
        exact ENNReal.add_lt_add (hUmeasure i) (hFmeasure i)
      _ = ENNReal.ofReal (ε / 8 / 2 ^ Encodable.encode i) := by
        rw [← ENNReal.ofReal_add (hstep_nonneg i) (hstep_nonneg i)]
        dsimp [step]
        ring_nf
  have hdiff_subset : T \ K ⊆ ⋃ i, bad i := by
    intro x hx
    have hxK : x ∉ K := hx.2
    by_contra hxBad
    exact hxK ⟨hx.1, hxBad⟩
  have hTdiffK : μ (T \ K) ≤ ENNReal.ofReal (ε / 4) := by
    calc
      μ (T \ K) ≤ μ (⋃ i : ι, bad i) := measure_mono hdiff_subset
      _ ≤ ENNReal.ofReal (ε / 4) := by
        simpa [show 2 * (ε / 8) = ε / 4 by ring_nf] using
          measure_iUnion_le_of_geometric_bound (by positivity) hbad_measure
  refine ⟨K, hKcompact, ?_, hKcont⟩
  have hKcompl_eq : Kᶜ = Tᶜ ∪ (T \ K) := by
    ext x
    by_cases hxT : x ∈ T <;> simp [K, hxT]
  calc
    μ Kᶜ = μ (Tᶜ ∪ (T \ K)) := by rw [hKcompl_eq]
    _ ≤ μ Tᶜ + μ (T \ K) := measure_union_le _ _
    _ ≤ μ Tᶜ + ENNReal.ofReal (ε / 4) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hTdiffK (μ Tᶜ)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) :=
      ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hTcompl
    _ = ENNReal.ofReal (ε / 2 + ε / 4) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal ε := by
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Helper for the finite-measure compact form of Lusin's theorem: an a.e.-measurable real-valued
map admits compact large-measure
continuity sets after removing a small open neighborhood of the null disagreement set with a
measurable representative. -/
lemma AEMeasurable.exists_isCompact_continuousOn_compl_lt_of_pos [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hfm : AEMeasurable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set Ω, IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  classical
  let g : Ω → ℝ := hfm.mk f
  have hεhalf : 0 < ε / 2 := by
    linarith
  -- We first apply the measurable Lusin theorem to a measurable representative.
  obtain ⟨K₀, hK₀compact, hK₀compl, hK₀cont⟩ :=
    (hfm.measurable_mk.exists_isCompact_continuousOn_compl_lt_of_pos hεhalf :
      ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal (ε / 2) ∧ ContinuousOn g K)
  let D : Set Ω := {x | f x ≠ g x}
  have hDnull : μ D = 0 := by
    simpa [D, ae_iff] using hfm.ae_eq_mk
  obtain ⟨S, hDS, hSmeas, hSnull⟩ := exists_measurable_superset_of_null hDnull
  have hεhalf_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    positivity
  -- We enlarge the null disagreement set by a small open neighborhood.
  have hS_ne_top : μ S ≠ ⊤ := by
    simp [hSnull]
  obtain ⟨O, hSO, hOopen, _hOfinite, hOdiff⟩ :=
    hSmeas.exists_isOpen_diff_lt hS_ne_top hεhalf_ne
  have hOmeasure : μ O < ENNReal.ofReal (ε / 2) := by
    calc
      μ O = μ ((O \ S) ∪ S) := by rw [Set.diff_union_of_subset hSO]
      _ ≤ μ (O \ S) + μ S := measure_union_le _ _
      _ = μ (O \ S) := by simp [hSnull]
      _ < ENNReal.ofReal (ε / 2) := hOdiff
  let K : Set Ω := K₀ \ O
  have hKsub : K ⊆ K₀ := by
    intro x hx
    exact hx.1
  have hKcompact : IsCompact K := by
    simpa [K, Set.diff_eq, Set.inter_assoc] using hK₀compact.inter_right hOopen.isClosed_compl
  have hEqOn : Set.EqOn f g K := by
    intro x hx
    have hxNotO : x ∉ O := hx.2
    by_contra hneq
    exact hxNotO (hSO (hDS hneq))
  have hKcont : ContinuousOn f K := by
    -- On `K`, the original function equals the measurable representative pointwise.
    exact (hK₀cont.mono hKsub).congr hEqOn
  refine ⟨K, hKcompact, ?_, hKcont⟩
  have hKcompl_eq : Kᶜ = K₀ᶜ ∪ O := by
    ext x
    by_cases hxK₀ : x ∈ K₀ <;> simp [K, hxK₀]
  calc
    μ Kᶜ = μ (K₀ᶜ ∪ O) := by rw [hKcompl_eq]
    _ ≤ μ K₀ᶜ + μ O := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hK₀compl hOmeasure
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf

/-- Helper for the finite-measure compact form of Lusin's theorem: continuity on compact
large-measure pieces for every error budget
implies almost-everywhere measurability. -/
lemma aemeasurable_of_forall_exists_isCompact_continuousOn_compl_lt [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ}
    (h :
      ∀ ε > 0, ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K) :
    AEMeasurable f μ := by
  classical
  have hlocal :
      ∀ n : ℕ, ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧ ContinuousOn f K := by
    intro n
    have hεn : 0 < (1 / (n + 1 : ℝ)) := by
      positivity
    exact h (1 / (n + 1 : ℝ)) hεn
  choose K hKcompact hKcompl hKcont using hlocal
  let A : Set Ω := ⋃ n : ℕ, K n
  have hKmeas : ∀ n : ℕ, MeasurableSet (K n) := fun n ↦ (hKcompact n).measurableSet
  have hAmeas : MeasurableSet A := MeasurableSet.iUnion hKmeas
  have hArestrict : AEMeasurable f (μ.restrict A) := by
    -- Each compact piece gives a measurable restriction, and the union preserves this.
    refine AEMeasurable.iUnion fun n ↦ ?_
    let g : Ω → ℝ := (K n).piecewise f fun _ ↦ 0
    have hg_meas : Measurable g := by
      exact (hKcont n).measurable_piecewise continuousOn_const (hKmeas n)
    have hg_eq : g =ᵐ[μ.restrict (K n)] f := by
      simpa [g] using
        (piecewise_ae_eq_restrict (hKmeas n) :
          Set.piecewise (K n) f (fun _ ↦ (0 : ℝ)) =ᵐ[μ.restrict (K n)] f)
    exact ⟨g, hg_meas, hg_eq.symm⟩
  have hAcompl_zero : μ Aᶜ = 0 := by
    by_contra hAcompl
    have hAcompl_ne_top : μ Aᶜ ≠ ⊤ := measure_ne_top μ Aᶜ
    have hAcompl_pos : 0 < (μ Aᶜ).toReal := ENNReal.toReal_pos hAcompl hAcompl_ne_top
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hAcompl_pos
    have hsubset : Aᶜ ⊆ (K n)ᶜ := by
      intro x hx hxKn
      exact hx (Set.mem_iUnion.2 ⟨n, hxKn⟩)
    have hlt : μ Aᶜ < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      exact (measure_mono hsubset).trans_lt (hKcompl n)
    have hlt_real : (μ Aᶜ).toReal < 1 / (n + 1 : ℝ) := by
      have hεn : 0 < (1 / (n + 1 : ℝ)) := by
        positivity
      exact (ENNReal.ofReal_lt_ofReal_iff hεn).1 (by
        simpa [ENNReal.ofReal_toReal hAcompl_ne_top] using hlt)
    linarith
  have hAae : A =ᵐ[μ] Set.univ := by
    filter_upwards [compl_mem_ae_iff.2 hAcompl_zero] with x hx
    have hxA : x ∈ A := by
      simpa using hx
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦ hxA⟩
  have hIndicator : A.indicator f =ᵐ[μ] f := by
    simpa using (indicator_ae_eq_of_ae_eq_set hAae : A.indicator f =ᵐ[μ] Set.univ.indicator f)
  exact (aemeasurable_congr hIndicator).1 ((aemeasurable_indicator_iff hAmeas).2 hArestrict)

/-
Analogy recall: no canonical `σ`-finite compact-complement version of Lusin's theorem is used in
this file. The compact formulation therefore stays on the finite-measure auxiliary theorem, while
the labeled repair uses the valid `σ`-finite closed-set globalization.
-/

/-- Auxiliary finite-measure form of Lusin's theorem: for a finite Borel measure on a Polish space,
a
real-valued map is almost-everywhere measurable if and only if it is continuous on a compact set
whose complement has arbitrarily small measure. -/
theorem aemeasurable_iff_forall_exists_isCompact_continuousOn_compl_lt
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) :
    AEMeasurable f μ ↔
      ∀ ε > 0, ∃ K : Set Ω,
        IsCompact K ∧ μ Kᶜ < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  constructor
  · -- The forward implication is the finite-measure Lusin theorem proved above.
    intro hfm ε hε
    exact hfm.exists_isCompact_continuousOn_compl_lt_of_pos hε
  · -- The reverse implication is the compact large-measure criterion proved above.
    intro hcompact
    exact aemeasurable_of_forall_exists_isCompact_continuousOn_compl_lt hcompact

/-- Helper for the closed-set globalization of Lusin's theorem: continuity on closed large-measure
pieces for every error budget
implies almost-everywhere measurability. -/
lemma aemeasurable_of_forall_exists_isClosed_continuousOn_compl_lt [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (h :
      ∀ ε > 0, ∃ F : Set Ω,
        IsClosed F ∧ μ Fᶜ < ENNReal.ofReal ε ∧ ContinuousOn f F) :
    AEMeasurable f μ := by
  classical
  have hlocal :
      ∀ n : ℕ, ∃ F : Set Ω,
        IsClosed F ∧ μ Fᶜ < ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧ ContinuousOn f F := by
    intro n
    have hεn : 0 < (1 / (n + 1 : ℝ)) := by
      positivity
    exact h (1 / (n + 1 : ℝ)) hεn
  choose F hFclosed hFcompl hFcont using hlocal
  let A : Set Ω := ⋃ n : ℕ, F n
  have hFmeas : ∀ n : ℕ, MeasurableSet (F n) := fun n ↦ (hFclosed n).measurableSet
  have hAmeas : MeasurableSet A := MeasurableSet.iUnion hFmeas
  have hArestrict : AEMeasurable f (μ.restrict A) := by
    -- Each closed continuity piece is measurable on the restricted measure,
    -- and the union keeps it so.
    refine AEMeasurable.iUnion fun n ↦ ?_
    let g : Ω → ℝ := (F n).piecewise f fun _ ↦ 0
    have hg_meas : Measurable g := by
      exact (hFcont n).measurable_piecewise continuousOn_const (hFmeas n)
    have hg_eq : g =ᵐ[μ.restrict (F n)] f := by
      simpa [g] using
        (piecewise_ae_eq_restrict (hFmeas n) :
          Set.piecewise (F n) f (fun _ ↦ (0 : ℝ)) =ᵐ[μ.restrict (F n)] f)
    exact ⟨g, hg_meas, hg_eq.symm⟩
  have hAcompl_ne_top : μ Aᶜ ≠ ⊤ := by
    have hsubset : Aᶜ ⊆ (F 0)ᶜ := by
      intro x hx hxF
      exact hx (Set.mem_iUnion.2 ⟨0, hxF⟩)
    exact (((measure_mono hsubset).trans_lt (hFcompl 0)).trans_le ENNReal.ofReal_lt_top.le).ne
  have hAcompl_zero : μ Aᶜ = 0 := by
    by_contra hAcompl
    have hAcompl_pos : 0 < (μ Aᶜ).toReal := ENNReal.toReal_pos hAcompl hAcompl_ne_top
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hAcompl_pos
    have hsubset : Aᶜ ⊆ (F n)ᶜ := by
      intro x hx hxFn
      exact hx (Set.mem_iUnion.2 ⟨n, hxFn⟩)
    have hlt : μ Aᶜ < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      exact (measure_mono hsubset).trans_lt (hFcompl n)
    have hlt_real : (μ Aᶜ).toReal < 1 / (n + 1 : ℝ) := by
      have hεn : 0 < (1 / (n + 1 : ℝ)) := by
        positivity
      exact (ENNReal.ofReal_lt_ofReal_iff hεn).1 (by
        simpa [ENNReal.ofReal_toReal hAcompl_ne_top] using hlt)
    linarith
  have hAae : A =ᵐ[μ] Set.univ := by
    filter_upwards [compl_mem_ae_iff.2 hAcompl_zero] with x hx
    have hxA : x ∈ A := by
      simpa using hx
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦ hxA⟩
  have hIndicator : A.indicator f =ᵐ[μ] f := by
    simpa using (indicator_ae_eq_of_ae_eq_set hAae : A.indicator f =ᵐ[μ] Set.univ.indicator f)
  exact (aemeasurable_congr hIndicator).1 ((aemeasurable_indicator_iff hAmeas).2 hArestrict)

/-- Helper for the closed-set globalization of Lusin's theorem: a measurable real-valued map on a
Polish space with a weakly
regular `σ`-finite measure is continuous on a closed set whose complement has arbitrarily small
measure. -/
lemma Measurable.exists_isClosed_continuousOn_compl_lt_of_pos [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    [Measure.WeaklyRegular μ] {f : Ω → ℝ} (hf : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Set Ω, IsClosed F ∧ μ Fᶜ < ENNReal.ofReal ε ∧ ContinuousOn f F := by
  classical
  let ι : Type := {ab : ℚ × ℚ // ab.1 < ab.2}
  let B : ι → Set ℝ := fun i ↦ Set.Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)
  let step : ι × ℕ → ℝ := fun j ↦ ε / 8 / 2 ^ Encodable.encode j
  have hstep_pos : ∀ j : ι × ℕ, 0 < step j := by
    intro j
    dsimp [step]
    positivity
  have hstep_nonneg : ∀ j : ι × ℕ, 0 ≤ step j := by
    intro j
    exact le_of_lt (hstep_pos j)
  let A : ι × ℕ → Set Ω := fun j ↦ spanningSets μ j.2 ∩ f ⁻¹' B j.1
  have hAmeas : ∀ j : ι × ℕ, MeasurableSet (A j) := by
    intro j
    exact (measurableSet_spanningSets μ j.2).inter (hf isOpen_Ioo.measurableSet)
  have hAneTop : ∀ j : ι × ℕ, μ (A j) ≠ ⊤ := by
    intro j
    exact ((measure_mono Set.inter_subset_left).trans_lt (measure_spanningSets_lt_top μ j.2)).ne
  -- We first approximate each rational slice from inside by a closed set.
  have hClosedApprox :
      ∀ j : ι × ℕ, ∃ C : Set Ω,
        C ⊆ A j ∧ IsClosed C ∧ μ (A j \ C) < ENNReal.ofReal (step j) := by
    intro j
    have hstep_ne : ENNReal.ofReal (step j) ≠ 0 := by
      positivity
    exact (hAmeas j).exists_isClosed_diff_lt (hAneTop j) hstep_ne
  choose C hCsub hCclosed hCmeasure using hClosedApprox
  -- We also approximate each slice from outside by an open set with the same budget.
  have hOpenApprox :
      ∀ j : ι × ℕ, ∃ U : Set Ω,
        A j ⊆ U ∧ IsOpen U ∧ μ (U \ A j) < ENNReal.ofReal (step j) := by
    intro j
    have hstep_ne : ENNReal.ofReal (step j) ≠ 0 := by
      positivity
    rcases (hAmeas j).exists_isOpen_diff_lt (hAneTop j) hstep_ne with
      ⟨U, hAU, hUopen, _hUfinite, hUmeasure⟩
    exact ⟨U, hAU, hUopen, hUmeasure⟩
  choose U hUsub hUopen hUmeasure using hOpenApprox
  let bad : ι × ℕ → Set Ω := fun j ↦ U j \ C j
  let F : Set Ω := (⋃ j : ι × ℕ, bad j)ᶜ
  have hBadOpen : ∀ j : ι × ℕ, IsOpen (bad j) := by
    intro j
    exact (hUopen j).sdiff (hCclosed j)
  have hFclosed : IsClosed F := by
    simpa [F] using (isOpen_iUnion hBadOpen).isClosed_compl
  have hPreimageEq :
      ∀ i : ι, F ∩ f ⁻¹' B i = F ∩ ⋃ n : ℕ, U (i, n) := by
    intro i
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hxSpan : x ∈ ⋃ n : ℕ, spanningSets μ n := by
        simp [iUnion_spanningSets μ]
      rcases Set.mem_iUnion.1 hxSpan with ⟨n, hxn⟩
      exact Set.mem_iUnion.2 ⟨n, hUsub (i, n) ⟨hxn, hx.2⟩⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      rcases Set.mem_iUnion.1 hx.2 with ⟨n, hxnU⟩
      have hxNotUnion : x ∉ ⋃ j : ι × ℕ, bad j := by
        simpa [F] using hx.1
      have hxNotBad : x ∉ bad (i, n) := by
        intro hxBad
        exact hxNotUnion (Set.mem_iUnion.2 ⟨(i, n), hxBad⟩)
      have hxC : x ∈ C (i, n) := by
        by_contra hxC
        exact hxNotBad ⟨hxnU, hxC⟩
      exact (hCsub (i, n) hxC).2
  have hFcont : ContinuousOn f F := by
    -- The rational intervals remain relatively open on the complement of the bad union.
    refine continuousOn_of_preimage_eq_open_inter_rat ?_
    intro q r hqr
    let i : ι := ⟨(q, r), hqr⟩
    refine ⟨⋃ n : ℕ, U (i, n), isOpen_iUnion fun n ↦ hUopen (i, n), ?_⟩
    simpa [i, B] using hPreimageEq i
  have hBadMeasure :
      ∀ j : ι × ℕ, μ (bad j) < ENNReal.ofReal (ε / 4 / 2 ^ Encodable.encode j) := by
    intro j
    have hsubset :
        bad j ⊆ (U j \ A j) ∪ (A j \ C j) := by
      intro x hx
      by_cases hxA : x ∈ A j
      · exact Or.inr ⟨hxA, hx.2⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    calc
      μ (bad j) ≤ μ ((U j \ A j) ∪ (A j \ C j)) := measure_mono hsubset
      _ ≤ μ (U j \ A j) + μ (A j \ C j) := measure_union_le _ _
      _ < ENNReal.ofReal (step j) + ENNReal.ofReal (step j) := by
        exact ENNReal.add_lt_add (hUmeasure j) (hCmeasure j)
      _ = ENNReal.ofReal (ε / 4 / 2 ^ Encodable.encode j) := by
        rw [← ENNReal.ofReal_add (hstep_nonneg j) (hstep_nonneg j)]
        dsimp [step]
        ring_nf
  have hFcompl_le : μ Fᶜ ≤ ENNReal.ofReal (ε / 2) := by
    simpa [F, show 2 * (ε / 4) = ε / 2 by ring_nf] using
      @measure_iUnion_le_of_geometric_bound Ω _ (ι × ℕ) _ μ bad (ε / 4) (by positivity)
        hBadMeasure
  refine ⟨F, hFclosed, ?_, hFcont⟩
  exact lt_of_le_of_lt hFcompl_le <| (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Helper for the closed-set globalization of Lusin's theorem: a locally finite `σ`-finite
almost-everywhere
measurable real-valued map admits closed large-measure continuity sets. -/
lemma AEMeasurable.exists_isClosed_continuousOn_compl_lt_of_pos [TopologicalSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    [IsLocallyFiniteMeasure μ]
    {f : Ω → ℝ} (hfm : AEMeasurable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Set Ω, IsClosed F ∧ μ Fᶜ < ENNReal.ofReal ε ∧ ContinuousOn f F := by
  classical
  let g : Ω → ℝ := hfm.mk f
  have hεhalf : 0 < ε / 2 := by
    linarith
  -- Route correction: the measurable representative is handled by the weakly regular measurable
  -- theorem, and we only remove a small open neighborhood of the disagreement set afterwards.
  obtain ⟨F₀, hF₀closed, hF₀compl, hF₀cont⟩ :=
    (hfm.measurable_mk.exists_isClosed_continuousOn_compl_lt_of_pos hεhalf :
      ∃ F : Set Ω,
        IsClosed F ∧ μ Fᶜ < ENNReal.ofReal (ε / 2) ∧ ContinuousOn g F)
  let D : Set Ω := {x | f x ≠ g x}
  have hDnull : μ D = 0 := by
    simpa [D, ae_iff] using hfm.ae_eq_mk
  obtain ⟨S, hDS, hSmeas, hSnull⟩ := exists_measurable_superset_of_null hDnull
  have hεhalf_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    positivity
  have hS_ne_top : μ S ≠ ⊤ := by
    simp [hSnull]
  -- We cover the null disagreement set by a small open set and delete it from the closed core.
  obtain ⟨O, hSO, hOopen, _hOfinite, hOdiff⟩ :=
    hSmeas.exists_isOpen_diff_lt hS_ne_top hεhalf_ne
  have hOmeasure : μ O < ENNReal.ofReal (ε / 2) := by
    calc
      μ O = μ ((O \ S) ∪ S) := by rw [Set.diff_union_of_subset hSO]
      _ ≤ μ (O \ S) + μ S := measure_union_le _ _
      _ = μ (O \ S) := by simp [hSnull]
      _ < ENNReal.ofReal (ε / 2) := hOdiff
  let F : Set Ω := F₀ \ O
  have hFclosed : IsClosed F := by
    simpa [F, Set.diff_eq] using hF₀closed.inter hOopen.isClosed_compl
  have hEqOn : Set.EqOn f g F := by
    intro x hx
    have hxNotO : x ∉ O := hx.2
    by_contra hneq
    exact hxNotO (hSO (hDS hneq))
  have hFcont : ContinuousOn f F := by
    -- On the final closed set, the original function agrees with the continuous representative.
    exact (hF₀cont.mono fun _ hx ↦ hx.1).congr hEqOn
  refine ⟨F, hFclosed, ?_, hFcont⟩
  have hFcompl_eq : Fᶜ = F₀ᶜ ∪ O := by
    ext x
    by_cases hxF₀ : x ∈ F₀ <;> simp [F, hxF₀]
  calc
    μ Fᶜ = μ (F₀ᶜ ∪ O) := by rw [hFcompl_eq]
    _ ≤ μ F₀ᶜ + μ O := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hF₀compl hOmeasure
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf

/-- Auxiliary closed-set globalization of Lusin's theorem: over a locally finite `σ`-finite Borel
measure,
replacing the compact large-measure set by a closed one yields a valid globalization of Lusin's
theorem. -/
theorem aemeasurable_iff_forall_exists_isClosed_continuousOn_compl_lt
    [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (f : Ω → ℝ) :
    AEMeasurable f μ ↔
      ∀ ε > 0, ∃ F : Set Ω,
        IsClosed F ∧ μ Fᶜ < ENNReal.ofReal ε ∧ ContinuousOn f F := by
  constructor
  · -- The missing forward direction is exactly the sigma-finite closed-set Lusin helper above.
    intro hfm ε hε
    exact hfm.exists_isClosed_continuousOn_compl_lt_of_pos hε
  · -- The reverse implication only needs measurability on a full-measure union of closed pieces.
    intro hclosed
    exact aemeasurable_of_forall_exists_isClosed_continuousOn_compl_lt hclosed

/-- Exercise 13.1.3 (Lusin's theorem): the textbook compact-complement formulation is false for
general infinite `σ`-finite measures, so the source-facing repair records the valid closed-set
globalization. For a locally finite `σ`-finite Borel measure on a Polish space, a real-valued map
is almost-everywhere equal to a Borel measurable map if and only if it is continuous on closed
sets whose complements have arbitrarily small measure. -/
theorem exercise_13_1_3 [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (f : Ω → ℝ) :
    AEMeasurable f μ ↔
      ∀ ε > 0, ∃ F : Set Ω,
        IsClosed F ∧ μ Fᶜ < ENNReal.ofReal ε ∧ ContinuousOn f F := by
  -- The exercise is exactly the closed-set globalization proved immediately above.
  simpa using aemeasurable_iff_forall_exists_isClosed_continuousOn_compl_lt μ f
