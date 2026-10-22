/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Exercise_1_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_53

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ENNReal symmDiff BigOperators

namespace MeasureTheory

universe u

variable {Ω : Type u}

/-- Data of a countable pairwise disjoint semiring cover of `A` whose excess over `A` has
`μ`-measure less than `ENNReal.ofReal ε`. -/
structure DisjointSemiringCoverApproximation
    (𝒜 : Set (Set Ω)) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (A : Set Ω) (ε : ℝ) where
  cover : ℕ → Set Ω
  cover_mem : ∀ n, cover n ∈ 𝒜
  pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (cover i) (cover j))
  subset_iUnion : A ⊆ ⋃ n, cover n
  measure_diff_lt : μ ((⋃ n, cover n) \ A) < ENNReal.ofReal ε

/-- Data of a finite pairwise disjoint semiring approximation to `A` whose symmetric-difference
measure is less than `ENNReal.ofReal ε`. -/
structure FiniteDisjointSemiringApproximation
    (𝒜 : Set (Set Ω)) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (A : Set Ω) (ε : ℝ) where
  size : ℕ
  cover : Fin size → Set Ω
  cover_mem : ∀ i, cover i ∈ 𝒜
  pairwise_disjoint : Pairwise (fun i j ↦ Disjoint (cover i) (cover j))
  measure_symmDiff_lt : μ (A ∆ ⋃ i, cover i) < ENNReal.ofReal ε

/-- Data of a measurable sandwich for `A` by sets from `MeasurableSpace.generateFrom 𝒜`
with null `μ`-measure gap. -/
structure GenerateFromNullSandwich
    (𝒜 : Set (Set Ω)) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (A : Set Ω) where
  lower : Set Ω
  upper : Set Ω
  lower_measurable : MeasurableSet[MeasurableSpace.generateFrom 𝒜] lower
  upper_measurable : MeasurableSet[MeasurableSpace.generateFrom 𝒜] upper
  lower_subset : lower ⊆ A
  upper_subset : A ⊆ upper
  measure_diff_eq_zero : μ (upper \ lower) = 0

/-- Helper for Theorem 1.65: after truncating an approximation `t` to a set `U`, the new
symmetric difference with `A` is controlled by the discarded tail `A \ U` together with the error
inside `U`. -/
lemma symmDiff_inter_subset_union_symmDiff_inter (A t U : Set Ω) :
    A ∆ (t ∩ U) ⊆ (A \ U) ∪ ((A ∩ U) ∆ (t ∩ U)) := by
  -- We split according to whether a point lies in the truncation set `U`.
  intro x hx
  by_cases hxU : x ∈ U
  · -- Inside `U`, the symmetric difference is exactly the local error on `A ∩ U`.
    simp [Set.symmDiff_def, hxU] at hx ⊢
    exact hx
  · -- Outside `U`, only the discarded part of `A` can contribute.
    simp [Set.symmDiff_def, hxU] at hx ⊢
    exact hx

/-- Helper for Theorem 1.65: the restriction of `μ` to the semiring `𝒜` vanishes on `∅`. -/
lemma measure_on_semiring_empty {𝒜 : Set (Set Ω)}
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) :
    μ ∅ = 0 :=
  measure_empty

/-- Helper for Theorem 1.65: the restriction of `μ` to the semiring `𝒜` is finitely additive on
finite pairwise disjoint unions that stay in `𝒜`. -/
lemma measure_on_semiring_sUnion {𝒜 : Set (Set Ω)} (_h𝒜 : IsSetSemiring 𝒜)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (I : Finset (Set Ω)) (hI : ↑I ⊆ 𝒜)
    (hdis : PairwiseDisjoint (I : Set (Set Ω)) id) (_hUnion : ⋃₀ ↑I ∈ 𝒜) :
    μ (⋃₀ ↑I) = ∑ s ∈ I, μ s := by
  classical
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  -- Every semiring member is measurable in `σ(𝒜)`, so finite additivity of `μ` applies.
  simpa [sUnion_eq_biUnion] using
    (measure_biUnion_finset (μ := μ) hdis fun s hs ↦
      MeasurableSpace.measurableSet_generateFrom (hI hs))

/-- Helper for Theorem 1.65: `μ` restricted to the semiring `𝒜` defines an additive content. -/
noncomputable def measure_on_semiring {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) :
    AddContent ℝ≥0∞ 𝒜 where
  toFun := fun s ↦ μ s
  empty' := measure_on_semiring_empty μ
  sUnion' := measure_on_semiring_sUnion h𝒜 μ

/-- Helper for Theorem 1.65: the semiring content induced by `μ` is `σ`-subadditive because `μ`
is countably subadditive on arbitrary unions. -/
lemma measure_on_semiring_isSigmaSubadditive {𝒜 : Set (Set Ω)}
    (h𝒜 : IsSetSemiring 𝒜) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) :
    (measure_on_semiring h𝒜 μ).IsSigmaSubadditive := by
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  intro f hf hf_union
  -- The ambient measure already satisfies the required countable subadditivity estimate.
  simpa [measure_on_semiring] using measure_iUnion_le (μ := μ) f

/-- Helper for Theorem 1.65: extending the semiring content `s ↦ μ s` by Carathéodory recovers the
original measure `μ`. -/
lemma measure_on_semiring_extension_eq {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) (hσ : μ.FiniteSpanningSetsIn 𝒜) :
    @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) (measure_on_semiring h𝒜 μ)
      h𝒜 le_rfl (measure_on_semiring_isSigmaSubadditive h𝒜 μ) = μ := by
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  -- Both measures agree on the generating semiring and are finite on the spanning family `hσ`.
  refine eq_of_eq_on_semiring_of_spanning_cover (μ := (measure_on_semiring h𝒜 μ).measure h𝒜 le_rfl
    (measure_on_semiring_isSigmaSubadditive h𝒜 μ)) (ν := μ) h𝒜
    (measure_on_semiring h𝒜 μ) hσ.set hσ.set_mem ?_ hσ.spanning ?_ ?_
  · intro n
    -- On the spanning family, the semiring content is exactly `μ`.
    simpa [measure_on_semiring] using hσ.finite n
  · intro s hs
    -- The canonical extension agrees with the content on each semiring member.
    simpa [measure_on_semiring] using
      AddContent.measure_eq (m := measure_on_semiring h𝒜 μ) (hC := h𝒜) (hC_gen := rfl)
        (m_sigma_subadd := measure_on_semiring_isSigmaSubadditive h𝒜 μ) hs
  · intro s hs
    rfl

/-- Helper for Theorem 1.65: on measurable sets of finite measure, the outer-measure infimum
formula yields a semiring cover whose total `μ`-mass is within `ε` of `μ A`. -/
lemma exists_semiring_cover_tsum_lt_of_measurable_of_lt_top {𝒜 : Set (Set Ω)}
    (h𝒜 : IsSetSemiring 𝒜) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hσ : μ.FiniteSpanningSetsIn 𝒜) {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.generateFrom 𝒜] A) (hμA : μ A < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ → Set Ω, (∀ n, s n ∈ 𝒜) ∧ A ⊆ ⋃ n, s n ∧
      ∑' n, μ (s n) < μ A + ENNReal.ofReal ε := by
  classical
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  let m := measure_on_semiring h𝒜 μ
  have hm_sigma : m.IsSigmaSubadditive := measure_on_semiring_isSigmaSubadditive h𝒜 μ
  have hμ_eq : m.measure h𝒜 le_rfl hm_sigma = μ :=
    measure_on_semiring_extension_eq h𝒜 μ hσ
  have houter_eq : inducedOuterMeasure (fun s hs ↦ m s) h𝒜.empty_mem addContent_empty A = μ A := by
    -- On `σ(𝒜)`, the induced outer measure agrees with the Carathéodory extension, hence with `μ`.
    calc
      inducedOuterMeasure (fun s hs ↦ m s) h𝒜.empty_mem addContent_empty A
          = m.measureCaratheodory h𝒜 hm_sigma A := by
              rw [AddContent.measureCaratheodory_eq_inducedOuterMeasure]
      _ = m.measure h𝒜 le_rfl hm_sigma A := by
            rw [AddContent.measure, trim_measurableSet_eq]
            exact hA
      _ = μ A := by rw [hμ_eq]
  have hlt :
      inducedOuterMeasure (fun s hs ↦ m s) h𝒜.empty_mem addContent_empty A
        < μ A + ENNReal.ofReal ε := by
    -- The positive error budget lets us choose a cover below `μ A + ε`.
    rw [houter_eq]
    exact ENNReal.lt_add_right hμA.ne ((ENNReal.ofReal_ne_zero_iff).2 hε)
  rw [class_inducedOuterMeasure_eq_iInf_coverings 𝒜
      (fun s : Subtype (fun t : Set Ω ↦ t ∈ 𝒜) ↦ m s.1) h𝒜.empty_mem addContent_empty A] at hlt
  simp only [iInf_lt_iff, exists_prop] at hlt
  rcases hlt with ⟨s, hs_mem, hsub, hs_lt⟩
  exact ⟨s, hs_mem, hsub, by simpa [m] using hs_lt⟩

/-- Helper for Theorem 1.65: a near-minimal semiring cover of a finite-measure measurable set has
small excess over the set itself. -/
lemma exists_semiring_cover_measure_diff_lt_of_measurable_of_lt_top {𝒜 : Set (Set Ω)}
    (h𝒜 : IsSetSemiring 𝒜) (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hσ : μ.FiniteSpanningSetsIn 𝒜) {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.generateFrom 𝒜] A) (hμA : μ A < ∞)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℕ → Set Ω, (∀ n, s n ∈ 𝒜) ∧ A ⊆ ⋃ n, s n ∧
      μ ((⋃ n, s n) \ A) < ENNReal.ofReal ε := by
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  obtain ⟨s, hs_mem, hsub, hsum_lt⟩ :=
    exists_semiring_cover_tsum_lt_of_measurable_of_lt_top h𝒜 μ hσ hA hμA ε hε
  have hUnion_meas : MeasurableSet (⋃ n, s n) := by
    exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom (hs_mem n)
  have hUnion_eq :
      (⋃ n, s n) = A ∪ ((⋃ n, s n) \ A) := by
    -- Because the cover contains `A`, the remaining part is exactly the excess of the cover.
    ext x
    constructor
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩
    · intro hx
      rcases hx with hxA | hx
      · exact hsub hxA
      · exact hx.1
  have hUnion_lt : μ (⋃ n, s n) < μ A + ENNReal.ofReal ε := by
    -- The measure of the union is bounded by the total mass of the covering family.
    exact lt_of_le_of_lt (measure_iUnion_le (μ := μ) s) hsum_lt
  have hUnion_measure :
      μ (⋃ n, s n) = μ A + μ ((⋃ n, s n) \ A) := by
    -- Split the cover into the target set and the excess part.
    have hsplit :
        μ (A ∪ ((⋃ n, s n) \ A)) = μ A + μ ((⋃ n, s n) \ A) :=
      measure_union disjoint_sdiff_right (hUnion_meas.diff hA)
    calc
      μ (⋃ n, s n) = μ (A ∪ ((⋃ n, s n) \ A)) := congrArg μ hUnion_eq
      _ = μ A + μ ((⋃ n, s n) \ A) := hsplit
  refine ⟨s, hs_mem, hsub, ?_⟩
  -- Cancel the finite quantity `μ A` from the previous strict inequality.
  exact (ENNReal.add_lt_add_iff_left hμA.ne).1 <| by simpa [hUnion_measure] using hUnion_lt

-- Proof sketch: decompose the sigma-finite measure into finite-measure pieces using
-- `FiniteSpanningSetsIn`, cover each measurable slice by semiring sets with arbitrarily small
-- excess using the induced outer-measure definition, then disjointify the resulting countable
-- family inside the semiring.
/-- Theorem 1.65 (1): If `A` is measurable in `σ(𝒜)` and `μ` is `σ`-finite on the semiring `𝒜`,
then `A` admits a countable pairwise disjoint cover by sets of `𝒜` whose excess over `A` has
arbitrarily small `μ`-measure. -/
theorem exists_disjoint_semiring_cover_measure_diff_lt {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) (hσ : μ.FiniteSpanningSetsIn 𝒜)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.generateFrom 𝒜] A)
    (ε : ℝ) (hε : 0 < ε) :
    Nonempty (DisjointSemiringCoverApproximation 𝒜 μ A ε) := by
  classical
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  -- Route correction: for part (1) we must approximate the finite-measure slices `A ∩ hσ.set n`
  -- individually, because the direct near-minimal-cover argument only applies to finite-measure
  -- sets.
  let δ : ℕ → ℝ := fun n ↦ (ε / 2) / 2 / 2 ^ n
  have hδ_pos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hslice :
      ∀ n, ∃ s : ℕ → Set Ω, (∀ m, s m ∈ 𝒜) ∧ A ∩ hσ.set n ⊆ ⋃ m, s m ∧
        μ ((⋃ m, s m) \ (A ∩ hσ.set n)) < ENNReal.ofReal (δ n) := by
    intro n
    -- Each slice `A ∩ hσ.set n` has finite measure because it lies inside the finite spanning set.
    refine exists_semiring_cover_measure_diff_lt_of_measurable_of_lt_top h𝒜 μ hσ
      (hA.inter (MeasurableSpace.measurableSet_generateFrom (hσ.set_mem n))) ?_ (δ n) (hδ_pos n)
    exact lt_of_le_of_lt (measure_mono (inter_subset_right : A ∩ hσ.set n ⊆ hσ.set n)) (hσ.finite n)
  choose s hs_mem hs_subset hs_diff using hslice
  let c : ℕ → Set Ω := fun k ↦ s k.unpair.1 k.unpair.2
  have hc_mem : ∀ k, c k ∈ 𝒜 := by
    intro k
    exact hs_mem k.unpair.1 k.unpair.2
  have hA_subset_c : A ⊆ ⋃ k, c k := by
    -- Each point of `A` lies in some spanning slice and then in that slice's semiring cover.
    intro x hxA
    have hx_span : x ∈ ⋃ n, hσ.set n := by simpa [hσ.spanning]
    rcases mem_iUnion.mp hx_span with ⟨n, hxn⟩
    have hx_slice : x ∈ A ∩ hσ.set n := ⟨hxA, hxn⟩
    have hx_cover : x ∈ ⋃ m, s n m := hs_subset n hx_slice
    rcases mem_iUnion.mp hx_cover with ⟨m, hxm⟩
    refine mem_iUnion.2 ⟨Nat.pair n m, ?_⟩
    simpa [c, Nat.unpair_pair] using hxm
  have hdiff_subset :
      (⋃ k, c k) \ A ⊆ ⋃ n, ((⋃ m, s n m) \ (A ∩ hσ.set n)) := by
    -- A point outside `A` that lies in the flattened cover already belongs to the excess of the
    -- unique slice from which it came.
    intro x hx
    rcases mem_iUnion.mp hx.1 with ⟨k, hxk⟩
    refine mem_iUnion.2 ⟨k.unpair.1, ?_⟩
    refine ⟨?_, ?_⟩
    · exact mem_iUnion.2 ⟨k.unpair.2, by simpa [c] using hxk⟩
    · intro hxA
      exact hx.2 hxA.1
  obtain ⟨d, hd⟩ := exists_disjoint_iUnion_eq_iUnion_of_isSetSemiring h𝒜 c hc_mem
  have hgeom_sum :
      (∑' n, ENNReal.ofReal (δ n)) = ENNReal.ofReal (ε / 2) := by
    -- The geometric error budget sums to `ε / 2`.
    have hδ_nonneg : ∀ n, 0 ≤ δ n := fun n ↦ (hδ_pos n).le
    rw [← ENNReal.ofReal_tsum_of_nonneg hδ_nonneg (summable_geometric_two' (ε / 2))]
    simpa [δ] using congrArg ENNReal.ofReal (tsum_geometric_two' (ε / 2))
  have hExcess_le :
      μ ((⋃ k, c k) \ A) ≤ ENNReal.ofReal (ε / 2) := by
    -- Summing the slice errors bounds the total excess of the flattened cover.
    calc
      μ ((⋃ k, c k) \ A)
          ≤ μ (⋃ n, ((⋃ m, s n m) \ (A ∩ hσ.set n))) := measure_mono hdiff_subset
      _ ≤ ∑' n, μ ((⋃ m, s n m) \ (A ∩ hσ.set n)) := measure_iUnion_le (μ := μ) _
      _ ≤ ∑' n, ENNReal.ofReal (δ n) := by
            gcongr with n
            exact (hs_diff n).le
      _ = ENNReal.ofReal (ε / 2) := hgeom_sum
  have hhalf_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    have hreal : ε / 2 < ε := by linarith
    exact ENNReal.ofReal_lt_ofReal_iff hε |>.2 hreal
  refine ⟨⟨d, hd.mem, hd.pairwiseDisjoint, ?_, ?_⟩⟩
  · -- Disjointification preserves the union of the flattened cover.
    simpa [hd.iUnion_eq] using hA_subset_c
  · -- The union equality transfers the excess estimate from `c` to the disjoint family `d`.
    have hiUnion_eq : (⋃ n, d n) = ⋃ n, c n := hd.iUnion_eq
    calc
      μ ((⋃ n, d n) \ A) = μ ((⋃ n, c n) \ A) := by rw [hiUnion_eq]
      _ ≤ ENNReal.ofReal (ε / 2) := hExcess_le
      _ < ENNReal.ofReal ε := hhalf_lt

-- Proof sketch: first approximate `A` in measure by a set in the ring generated by finite unions
-- of semiring members, using sigma-finiteness on `𝒜`; then rewrite that finite union as a finite
-- pairwise disjoint union of semiring sets via the semiring disjointification theorem.
/-- Theorem 1.65 (2): If `A` is measurable with finite `μ`-measure and `μ` is `σ`-finite on the
semiring `𝒜`, then `A` can be approximated in symmetric-difference measure by a finite pairwise
disjoint union of sets from `𝒜`. -/
theorem exists_finite_disjoint_semiring_approximation_symmDiff_lt
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜)) (hσ : μ.FiniteSpanningSetsIn 𝒜)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.generateFrom 𝒜] A)
    (hμA : μ A < ∞) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (FiniteDisjointSemiringApproximation 𝒜 μ A ε) := by
  classical
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  let T : ℕ → Set Ω := fun n ↦ ⋃ k ∈ Set.Iic n, hσ.set k
  have hT_mono : Monotone T := by
    -- The accumulated spanning sets are increasing by construction.
    intro m n hmn x hx
    simp only [T, mem_iUnion] at hx ⊢
    rcases hx with ⟨k, hk, hxk⟩
    exact ⟨k, le_trans hk hmn, hxk⟩
  have hT_union : (⋃ n, T n) = univ := by
    -- Every spanning-set piece appears in the corresponding accumulated union.
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases mem_iUnion.1 (show x ∈ ⋃ n, hσ.set n from by simp [hσ.spanning]) with ⟨n, hxn⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      simp only [T, mem_iUnion]
      exact ⟨n, by simp, hxn⟩
  have hT_supClosure (n : ℕ) : T n ∈ supClosure 𝒜 := by
    -- A finite union of semiring pieces belongs to the ring generated by the semiring.
    have hEq : T n = Finset.sup (Set.finite_Iic n).toFinset hσ.set := by
      ext x
      simp [T]
    rw [hEq]
    refine supClosed_supClosure.finsetSup_mem (t := (Set.finite_Iic n).toFinset)
      (by simp) ?_
    intro k hk
    exact subset_supClosure (hσ.set_mem k)
  have hT_meas (n : ℕ) : MeasurableSet (T n) :=
    measurableSet_generateFrom_of_mem_supClosure (hT_supClosure n)
  have hT_finite (n : ℕ) : μ (T n) < ∞ := by
    -- Each accumulated union has finite measure because it is a finite union of finite-measure
    -- spanning pieces.
    simpa [T] using measure_biUnion_lt_top (Set.finite_Iic n) (fun k _ ↦ hσ.finite k)
  have hAT_mono : Monotone (fun n ↦ A ∩ T n) := by
    -- Intersecting the increasing accumulated sequence with `A` preserves monotonicity.
    intro m n hmn
    exact inter_subset_inter_right A (hT_mono hmn)
  have hAT_tendsto := tendsto_measure_iUnion_atTop (μ := μ) hAT_mono
  have hAT_union : (⋃ n, A ∩ T n) = A := by
    -- Since the accumulated spanning sets cover the whole space, their intersections with `A`
    -- cover exactly `A`.
    ext x
    constructor
    · intro hx
      exact mem_of_mem_inter_left <| (mem_iUnion.mp hx).choose_spec
    · intro hxA
      have hxT : x ∈ ⋃ n, T n := by simpa [hT_union]
      rcases mem_iUnion.mp hxT with ⟨n, hxn⟩
      exact mem_iUnion.2 ⟨n, ⟨hxA, hxn⟩⟩
  rw [hAT_union] at hAT_tendsto
  change Filter.Tendsto (fun n ↦ μ (A ∩ T n)) Filter.atTop (nhds (μ A)) at hAT_tendsto
  rw [← ENNReal.tendsto_toReal_iff
    (fun n ↦ ne_top_of_le_ne_top hμA.ne (measure_mono (inter_subset_left : A ∩ T n ⊆ A)))
    hμA.ne] at hAT_tendsto
  have hε_half : 0 < ε / 2 := by
    linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hAT_tendsto (ε / 2) hε_half
  have hA_tail :
      μ (A \ T N) < ENNReal.ofReal (ε / 2) := by
    -- The finite-measure truncation `A ∩ T N` captures almost all of `A`.
    have hdiff : A \ T N = A \ (A ∩ T N) := by
      ext x
      simp
    rw [hdiff]
    rw [measure_diff (inter_subset_left : A ∩ T N ⊆ A)
      ((hA.inter (hT_meas N)).nullMeasurableSet)
      (ne_top_of_le_ne_top hμA.ne (measure_mono (inter_subset_left : A ∩ T N ⊆ A))),
      ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.sub_ne_top hμA.ne),
      ENNReal.toReal_sub_of_le (measure_mono (inter_subset_left : A ∩ T N ⊆ A)) hμA.ne]
    have hdist : dist (μ A).toReal (μ (A ∩ T N)).toReal < ε / 2 := by
      simpa [dist_comm] using hN N le_rfl
    have htoReal_le : (μ (A ∩ T N)).toReal ≤ (μ A).toReal :=
      ENNReal.toReal_mono hμA.ne (measure_mono (inter_subset_left : A ∩ T N ⊆ A))
    simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htoReal_le)] using hdist
  letI : IsFiniteMeasure (μ.restrict (T N)) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply' (hT_meas N)] using hT_finite N
  have hcount_cover :
      ∃ D : Set (Set Ω), D.Countable ∧ D ⊆ 𝒜 ∧ (μ.restrict (T N)) (⋃₀ D)ᶜ = 0 := by
    -- The original sigma-finite spanning family still covers `T N` modulo null sets after
    -- restriction.
    refine ⟨Set.range hσ.set, Set.countable_range _, ?_, ?_⟩
    · intro s hs
      rcases hs with ⟨n, rfl⟩
      exact hσ.set_mem n
    · rw [Measure.restrict_apply' (hT_meas N)]
      simp [hσ.spanning]
  obtain ⟨t, ht_mem, ht_symmDiff⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
      (μ := μ.restrict (T N)) h𝒜 hcount_cover rfl (hA.inter (hT_meas N))
      (by positivity : 0 < ENNReal.ofReal (ε / 2))
  let t' := t ∩ T N
  have ht_meas : MeasurableSet t :=
    measurableSet_generateFrom_of_mem_supClosure ht_mem
  have ht'_mem : t' ∈ supClosure 𝒜 :=
    h𝒜.isSetRing_supClosure.inter_mem ht_mem (hT_supClosure N)
  have ht'_symmDiff :
      μ ((A ∩ T N) ∆ t') < ENNReal.ofReal (ε / 2) := by
    -- Under the restricted finite measure, only the part of `t` inside `T N` contributes.
    have hsymm_meas : MeasurableSet (t ∆ (A ∩ T N)) :=
      ht_meas.symmDiff (hA.inter (hT_meas N))
    have hsymm_restrict : μ ((t ∆ (A ∩ T N)) ∩ T N) < ENNReal.ofReal (ε / 2) := by
      have hsymm_restrict' := ht_symmDiff
      rw [Measure.restrict_apply' (hT_meas N)] at hsymm_restrict'
      exact hsymm_restrict'
    simpa [t', inter_symmDiff_distrib_right, inter_assoc, symmDiff_comm] using hsymm_restrict
  have hsymmDiff_lt : μ (A ∆ t') < ENNReal.ofReal ε := by
    -- Route correction: instead of approximating `A` directly in a finite measure space, first
    -- truncate to a large finite-measure piece `T N`, approximate there, and then add back the
    -- discarded tail `A \ T N`.
    calc
      μ (A ∆ t')
        ≤ μ ((A \ T N) ∪ ((A ∩ T N) ∆ t')) := by
            exact measure_mono (symmDiff_inter_subset_union_symmDiff_inter A t (T N))
      _ ≤ μ (A \ T N) + μ ((A ∩ T N) ∆ t') := measure_union_le _ _
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            exact ENNReal.add_lt_add hA_tail ht'_symmDiff
      _ = ENNReal.ofReal ε := by
            have hε_half_nonneg : 0 ≤ ε / 2 := by
              linarith
            rw [← ENNReal.ofReal_add hε_half_nonneg hε_half_nonneg]
            ring_nf
  rcases h𝒜.mem_supClosure_iff.mp ht'_mem with ⟨P, hP_parts⟩
  let e : P.parts ≃ Fin P.parts.card := P.parts.equivFin
  have hcover_mem (i : Fin P.parts.card) : (((e.symm i : P.parts) : Set Ω)) ∈ 𝒜 := by
    exact hP_parts (e.symm i).property
  have hcover_disjoint :
      Pairwise (fun i j : Fin P.parts.card ↦
        Disjoint (((e.symm i : P.parts) : Set Ω)) (((e.symm j : P.parts) : Set Ω))) := by
    -- Distinct parts of a finpartition are disjoint.
    intro i j hij
    exact P.disjoint (e.symm i).property (e.symm j).property
      (by simpa using e.symm.injective.ne hij)
  have hcover_union : (⋃ i : Fin P.parts.card, (((e.symm i : P.parts) : Set Ω))) = t' := by
    -- Reindex the partition parts by `Fin`.
    have hparts_union : (⋃ s ∈ P.parts, s) = t' := by
      simpa [Finset.sup_set_eq_biUnion] using P.sup_parts
    ext x
    constructor
    · intro hx
      have hx' : x ∈ ⋃ s ∈ P.parts, s := by
        rcases mem_iUnion.mp hx with ⟨i, hxi⟩
        exact mem_iUnion.2
          ⟨((e.symm i : P.parts) : Set Ω), mem_iUnion.2 ⟨(e.symm i).property, hxi⟩⟩
      exact hparts_union ▸ hx'
    · intro hx
      have hx' : x ∈ ⋃ s ∈ P.parts, s := hparts_union.symm ▸ hx
      rcases mem_iUnion.mp hx' with ⟨s, hs⟩
      rcases mem_iUnion.mp hs with ⟨hsP, hxs⟩
      exact mem_iUnion.2 ⟨e ⟨s, hsP⟩, by simpa [e] using hxs⟩
  refine ⟨⟨P.parts.card, fun i ↦ ((e.symm i : P.parts) : Set Ω), hcover_mem,
    hcover_disjoint, ?_⟩⟩
  simpa [hcover_union] using hsymmDiff_lt

-- Proof sketch: for the outer measure induced by the semiring content, approximate a
-- Carathéodory-measurable set from above and below by sets in `σ(𝒜)` with arbitrarily small
-- outer-measure error on finite spanning pieces, then pass to intersections and complements to
-- obtain a measurable sandwich differing by a null set.
/-- Helper for Theorem 1.65: on `generateFrom 𝒜`-measurable sets, the induced outer measure of the
content `m` agrees with the trimmed measure `μ`. -/
lemma inducedOuterMeasure_eq_measure_of_generateFrom_measurable
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜) (m : AddContent ℝ≥0∞ 𝒜)
    (hm_sigma : m.IsSigmaSubadditive)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hμ :
      μ = @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) m h𝒜 le_rfl hm_sigma)
    {E : Set Ω} (hE : MeasurableSet[MeasurableSpace.generateFrom 𝒜] E) :
    inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty E = μ E := by
  letI : MeasurableSpace Ω := MeasurableSpace.generateFrom 𝒜
  -- Rewrite the induced outer measure through the Carathéodory extension and then trim back to
  -- `generateFrom 𝒜`.
  calc
    inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty E
        = m.measureCaratheodory h𝒜 hm_sigma E := by
            rw [AddContent.measureCaratheodory_eq_inducedOuterMeasure]
    _ = m.measure h𝒜 le_rfl hm_sigma E := by
          rw [AddContent.measure, trim_measurableSet_eq]
          exact hE
    _ = μ E := by rw [hμ]

/-- Helper for Theorem 1.65: on a finite-measure measurable slice `E`, a Carathéodory-measurable
set `A` admits a `generateFrom 𝒜`-measurable superset of `A ∩ E` whose excess has arbitrarily
small induced outer measure. -/
lemma exists_generateFrom_superset_of_caratheodory_slice_diff_lt
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜) (m : AddContent ℝ≥0∞ 𝒜)
    (hm_sigma : m.IsSigmaSubadditive)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hμ :
      μ = @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) m h𝒜 le_rfl hm_sigma)
    {A E : Set Ω}
    (hE : MeasurableSet[MeasurableSpace.generateFrom 𝒜] E)
    (hμE : μ E < ∞)
    (hA : MeasurableSet[(inducedOuterMeasure (fun s _ ↦ m s)
      h𝒜.empty_mem addContent_empty).caratheodory] A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T, MeasurableSet[MeasurableSpace.generateFrom 𝒜] T ∧ A ∩ E ⊆ T ∧
      inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty (T \ (A ∩ E)) <
        ENNReal.ofReal δ := by
  let ν : OuterMeasure Ω := inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty
  have hslice_meas : MeasurableSet[ν.caratheodory] (A ∩ E) := by
    -- The slice is Carathéodory-measurable because `A` is and `E` already lies in `σ(𝒜)`.
    exact hA.inter (AddContent.isCaratheodory_inducedOuterMeasure h𝒜 m E hE)
  have hνE : ν E < ∞ := by
    -- The induced outer measure agrees with `μ` on the measurable slice carrier `E`.
    rw [inducedOuterMeasure_eq_measure_of_generateFrom_measurable h𝒜 m hm_sigma μ hμ hE]
    exact hμE
  have hνslice_lt_top : ν (A ∩ E) < ∞ := by
    -- Monotonicity transfers finiteness from `E` to the slice `A ∩ E`.
    exact lt_of_le_of_lt (ν.mono inter_subset_right) hνE
  have hlt : ν (A ∩ E) < ν (A ∩ E) + ENNReal.ofReal δ := by
    -- The positive error budget gives room to choose a nearly optimal semiring cover.
    exact ENNReal.lt_add_right hνslice_lt_top.ne ((ENNReal.ofReal_ne_zero_iff).2 hδ)
  rw [class_inducedOuterMeasure_eq_iInf_coverings 𝒜
      (fun s : Subtype (fun t : Set Ω ↦ t ∈ 𝒜) ↦ m s.1) h𝒜.empty_mem addContent_empty (A ∩ E)] at hlt
  have hνslice_eq :
      (⨅ (cover : ℕ → Set Ω) (hcover : ∀ n, cover n ∈ 𝒜) (_ : A ∩ E ⊆ ⋃ n, cover n),
        ∑' n, m (cover n)) = ν (A ∩ E) := by
    simpa [ν] using
      (class_inducedOuterMeasure_eq_iInf_coverings 𝒜
        (fun s : Subtype (fun t : Set Ω ↦ t ∈ 𝒜) ↦ m s.1) h𝒜.empty_mem addContent_empty (A ∩ E)).symm
  simp only [iInf_lt_iff, exists_prop] at hlt
  rcases hlt with ⟨s, hs_mem, hs_sub, hs_lt⟩
  have hs_lt' : ∑' n, m (s n) < ν (A ∩ E) + ENNReal.ofReal δ := by
    simpa [hνslice_eq] using hs_lt
  refine ⟨⋃ n, s n, ?_, hs_sub, ?_⟩
  · -- The union of semiring sets is measurable in `σ(𝒜)`.
    exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom (hs_mem n)
  · have hle_union : ν (⋃ n, s n) ≤ ∑' n, m (s n) := by
      -- Replace the outer measure of semiring members by the original content and use
      -- countable subadditivity.
      calc
        ν (⋃ n, s n) ≤ ∑' n, ν (s n) := measure_iUnion_le (μ := ν) s
        _ = ∑' n, m (s n) := by
              congr with n
              exact AddContent.inducedOuterMeasure_eq h𝒜 m hm_sigma (hs_mem n)
    have hadd := (OuterMeasure.isCaratheodory_iff ν).mp hslice_meas (⋃ n, s n)
    have hsplit : ν (⋃ n, s n) = ν ((⋃ n, s n) ∩ (A ∩ E)) + ν ((⋃ n, s n) \ (A ∩ E)) := by
      -- Carathéodory additivity splits the union into the slice and its excess.
      simpa [ν] using hadd
    have hsubset_eq : ((⋃ n, s n) ∩ (A ∩ E)) = A ∩ E := by
      exact inter_eq_right.mpr hs_sub
    have hcalc : ν (A ∩ E) + ν ((⋃ n, s n) \ (A ∩ E)) < ν (A ∩ E) + ENNReal.ofReal δ := by
      calc
        ν (A ∩ E) + ν ((⋃ n, s n) \ (A ∩ E))
            = ν ((⋃ n, s n) ∩ (A ∩ E)) + ν ((⋃ n, s n) \ (A ∩ E)) := by rw [hsubset_eq]
        _ = ν (⋃ n, s n) := hsplit.symm
        _ ≤ ∑' n, m (s n) := hle_union
        _ < ν (A ∩ E) + ENNReal.ofReal δ := hs_lt'
    exact (ENNReal.add_lt_add_iff_left hνslice_lt_top.ne).mp hcalc

/-- Helper for Theorem 1.65: an `ℝ≥0∞` value bounded by every reciprocal `1 / (k + 1)` must be
zero. -/
lemma ennreal_eq_zero_of_le_inv_succ {x : ℝ≥0∞}
    (hx : ∀ k : ℕ, x ≤ ENNReal.ofReal (1 / (k + 1 : ℝ))) :
    x = 0 := by
  by_contra hx0
  have hx_le_one : x ≤ 1 := by
    simpa using hx 0
  have hx_ne_top : x ≠ ∞ := ne_top_of_le_ne_top (by simp) hx_le_one
  have hx_toReal_pos : 0 < x.toReal := ENNReal.toReal_pos hx0 hx_ne_top
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx_toReal_pos
  have hxk := hx k
  have hnonneg : 0 ≤ 1 / (k + 1 : ℝ) := by
    positivity
  rw [ENNReal.le_ofReal_iff_toReal_le hx_ne_top hnonneg] at hxk
  exact not_lt_of_ge hxk hk

/-- Helper for Theorem 1.65: a Carathéodory-measurable set has a `generateFrom 𝒜`-measurable
upper hull with induced outer-measure-null excess. -/
lemma exists_generateFrom_upper_hull_null_of_caratheodory_measurable
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜) (m : AddContent ℝ≥0∞ 𝒜)
    (hm_sigma : m.IsSigmaSubadditive)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hμ :
      μ = @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) m h𝒜 le_rfl hm_sigma)
    (hσ : μ.FiniteSpanningSetsIn 𝒜)
    {A : Set Ω}
    (hA : MeasurableSet[(inducedOuterMeasure (fun s _ ↦ m s)
      h𝒜.empty_mem addContent_empty).caratheodory] A) :
    ∃ Aplus, MeasurableSet[MeasurableSpace.generateFrom 𝒜] Aplus ∧ A ⊆ Aplus ∧
      inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty (Aplus \ A) = 0 := by
  let ν : OuterMeasure Ω := inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty
  let δ : ℕ → ℕ → ℝ := fun k n ↦ (((1 : ℝ) / (k + 1 : ℝ)) / 2) / 2 ^ n
  have hδ_pos : ∀ k n, 0 < δ k n := by
    intro k n
    dsimp [δ]
    positivity
  have hslice :
      ∀ k n, ∃ T, MeasurableSet[MeasurableSpace.generateFrom 𝒜] T ∧ A ∩ hσ.set n ⊆ T ∧
        ν (T \ (A ∩ hσ.set n)) < ENNReal.ofReal (δ k n) := by
    intro k n
    -- Approximate each finite-measure slice `A ∩ hσ.set n` with geometric budget `δ k n`.
    refine exists_generateFrom_superset_of_caratheodory_slice_diff_lt h𝒜 m hm_sigma μ hμ
      (MeasurableSpace.measurableSet_generateFrom (hσ.set_mem n)) (hσ.finite n) hA (hδ_pos k n)
  choose T hT_meas hT_subset hT_diff using hslice
  let Aseq : ℕ → Set Ω := fun k ↦ ⋃ n, T k n
  have hAseq_meas : ∀ k, MeasurableSet[MeasurableSpace.generateFrom 𝒜] (Aseq k) := by
    intro k
    -- Each approximating hull is a countable union of measurable slice supersets.
    exact MeasurableSet.iUnion fun n ↦ hT_meas k n
  have hA_subset_Aseq : ∀ k, A ⊆ Aseq k := by
    intro k x hxA
    -- Every point of `A` lies in some finite spanning set and hence in the corresponding slice
    -- hull.
    have hx_span : x ∈ ⋃ n, hσ.set n := by simpa [hσ.spanning]
    rcases mem_iUnion.mp hx_span with ⟨n, hxn⟩
    exact mem_iUnion.2 ⟨n, hT_subset k n ⟨hxA, hxn⟩⟩
  have hAseq_diff_le : ∀ k, ν (Aseq k \ A) ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) := by
    intro k
    have hsubset : (Aseq k \ A) ⊆ ⋃ n, (T k n \ (A ∩ hσ.set n)) := by
      -- A point outside `A` can only contribute to the excess coming from its originating slice.
      intro x hx
      rcases mem_iUnion.mp hx.1 with ⟨n, hxn⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      refine ⟨hxn, ?_⟩
      intro hxAhn
      exact hx.2 hxAhn.1
    calc
      ν (Aseq k \ A) ≤ ν (⋃ n, (T k n \ (A ∩ hσ.set n))) := ν.mono hsubset
      _ ≤ ∑' n, ν (T k n \ (A ∩ hσ.set n)) := measure_iUnion_le (μ := ν) _
      _ ≤ ∑' n, ENNReal.ofReal (δ k n) := by
            gcongr with n
            exact (hT_diff k n).le
      _ = ENNReal.ofReal (1 / (k + 1 : ℝ)) := by
            have hδ_nonneg : ∀ n : ℕ, 0 ≤ δ k n := fun n ↦ (hδ_pos k n).le
            rw [← ENNReal.ofReal_tsum_of_nonneg hδ_nonneg
              (summable_geometric_two' ((1 : ℝ) / (k + 1 : ℝ)))]
            simpa [δ] using congrArg ENNReal.ofReal
              (tsum_geometric_two' ((1 : ℝ) / (k + 1 : ℝ)))
  refine ⟨⋂ k, Aseq k, MeasurableSet.iInter hAseq_meas, ?_, ?_⟩
  · -- Intersecting the measurable hulls preserves the inclusion `A ⊆ Aplus`.
    intro x hxA
    exact mem_iInter.2 fun k ↦ hA_subset_Aseq k hxA
  · -- The geometric bounds force the excess of the intersection to vanish.
    apply ennreal_eq_zero_of_le_inv_succ
    intro k
    refine le_trans (ν.mono ?_) (hAseq_diff_le k)
    intro x hx
    exact ⟨mem_iInter.mp hx.1 k, hx.2⟩

/-- Helper for Theorem 1.65: a Carathéodory-measurable set has a `generateFrom 𝒜`-measurable
lower hull with induced outer-measure-null defect. -/
lemma exists_generateFrom_lower_hull_null_of_caratheodory_measurable
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜) (m : AddContent ℝ≥0∞ 𝒜)
    (hm_sigma : m.IsSigmaSubadditive)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hμ :
      μ = @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) m h𝒜 le_rfl hm_sigma)
    (hσ : μ.FiniteSpanningSetsIn 𝒜)
    {A : Set Ω}
    (hA : MeasurableSet[(inducedOuterMeasure (fun s _ ↦ m s)
      h𝒜.empty_mem addContent_empty).caratheodory] A) :
    ∃ Aminus, MeasurableSet[MeasurableSpace.generateFrom 𝒜] Aminus ∧ Aminus ⊆ A ∧
      inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty (A \ Aminus) = 0 := by
  obtain ⟨B, hB_meas, hAc_subset_B, hB_diff_zero⟩ :=
    exists_generateFrom_upper_hull_null_of_caratheodory_measurable h𝒜 m hm_sigma μ hμ hσ
      (A := Aᶜ) (by simpa using hA.compl)
  refine ⟨Bᶜ, hB_meas.compl, ?_, ?_⟩
  · -- Complementing an upper hull of `Aᶜ` produces a lower hull of `A`.
    exact compl_subset_comm.mp hAc_subset_B
  · -- The missing part of the lower hull is exactly the excess of the upper hull of `Aᶜ`.
    have hset : A \ Bᶜ = B \ Aᶜ := by
      ext x
      simp [and_comm]
    rw [hset]
    exact hB_diff_zero

/-- Theorem 1.65 (3): For the outer measure induced by a sigma-subadditive additive content on the
semiring `𝒜`, every Carathéodory-measurable set is sandwiched between two sets of `σ(𝒜)` whose
difference has `μ`-measure zero, where `μ` is the induced measure on `σ(𝒜)`. -/
theorem exists_generateFrom_sandwich_of_caratheodory_measurable
    {𝒜 : Set (Set Ω)} (h𝒜 : IsSetSemiring 𝒜) (m : AddContent ℝ≥0∞ 𝒜)
    (hm_sigma : m.IsSigmaSubadditive)
    (μ : @Measure Ω (MeasurableSpace.generateFrom 𝒜))
    (hμ :
      μ = @AddContent.measure Ω 𝒜 (MeasurableSpace.generateFrom 𝒜) m h𝒜 le_rfl hm_sigma)
    (hσ : μ.FiniteSpanningSetsIn 𝒜)
    {A : Set Ω}
    (hA : MeasurableSet[(inducedOuterMeasure (fun s _ ↦ m s)
      h𝒜.empty_mem addContent_empty).caratheodory] A) :
    Nonempty (GenerateFromNullSandwich 𝒜 μ A) := by
  let ν : OuterMeasure Ω := inducedOuterMeasure (fun s _ ↦ m s) h𝒜.empty_mem addContent_empty
  obtain ⟨Aplus, hAplus_meas, hA_subset_Aplus, hAplus_diff_zero⟩ :=
    exists_generateFrom_upper_hull_null_of_caratheodory_measurable h𝒜 m hm_sigma μ hμ hσ hA
  obtain ⟨Aminus, hAminus_meas, hAminus_subset_A, hAminus_diff_zero⟩ :=
    exists_generateFrom_lower_hull_null_of_caratheodory_measurable h𝒜 m hm_sigma μ hμ hσ hA
  refine ⟨⟨Aminus, Aplus, hAminus_meas, hAplus_meas, hAminus_subset_A, hA_subset_Aplus, ?_⟩⟩
  have hgap_meas : MeasurableSet[MeasurableSpace.generateFrom 𝒜] (Aplus \ Aminus) :=
    hAplus_meas.diff hAminus_meas
  have hsubset :
      Aplus \ Aminus ⊆ (Aplus \ A) ∪ (A \ Aminus) := by
    -- Route correction: the final gap is controlled by the union of the two one-sided null gaps,
    -- not by trying to compare `Aplus \ Aminus` directly with one side only.
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inr ⟨hxA, hx.2⟩
    · exact Or.inl ⟨hx.1, hxA⟩
  have hν_gap_zero : ν (Aplus \ Aminus) = 0 := by
    -- The outer measure of the measurable gap is bounded by a union of two null sets.
    refine le_antisymm ?_ (zero_le _)
    calc
      ν (Aplus \ Aminus) ≤ ν ((Aplus \ A) ∪ (A \ Aminus)) := ν.mono hsubset
      _ ≤ ν (Aplus \ A) + ν (A \ Aminus) := measure_union_le _ _
      _ = 0 := by rw [hAplus_diff_zero, hAminus_diff_zero, zero_add]
  -- Rewrite the induced outer measure of the measurable gap back to `μ`.
  calc
    μ (Aplus \ Aminus)
        = ν (Aplus \ Aminus) := by
            dsimp [ν]
            symm
            exact inducedOuterMeasure_eq_measure_of_generateFrom_measurable h𝒜 m hm_sigma μ hμ
              hgap_meas
    _ = 0 := hν_gap_zero

end MeasureTheory
