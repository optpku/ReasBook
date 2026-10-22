/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap08.section02_part1

section Chap08
section Section02

/-- Helper for Theorem 8.3: every rational number fails a fixed-exponent
Diophantine lower bound with a strictly positive constant. -/
lemma helperForTheorem_8_3_not_diophantineExponent_of_rat
    {τ : ℝ} (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ¬ helperForTheorem_8_3_diophantineExponent τ ((p : ℝ) / (q : ℝ)) := by
  intro hx
  rcases hx with ⟨c, hc, hbound⟩
  have hbound_self :
      |((p : ℝ) / (q : ℝ)) - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := hbound p q hq
  have hle_zero : c / (q : ℝ) ^ τ ≤ 0 := by
    have hge_zero : (0 : ℝ) ≥ c / (q : ℝ) ^ τ := by
      simpa using hbound_self
    exact hge_zero
  have hq_pos_real : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hpow_pos : (0 : ℝ) < (q : ℝ) ^ τ := Real.rpow_pos_of_pos hq_pos_real τ
  have hdiv_pos : 0 < c / (q : ℝ) ^ τ := div_pos hc hpow_pos
  exact (not_le_of_gt hdiv_pos) hle_zero

/-- Helper for Theorem 8.3: every rational number lies in the complement of the
fixed-exponent Diophantine set. -/
lemma helperForTheorem_8_3_rat_mem_complement
    {τ : ℝ} (r : ℚ) :
    (r : ℝ) ∈ {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  change ¬ helperForTheorem_8_3_diophantineExponent τ (r : ℝ)
  have hr : ((r.num : ℝ) / (r.den : ℝ)) = (r : ℝ) := by
    exact_mod_cast (Rat.num_div_den r)
  have hrat : ¬ helperForTheorem_8_3_diophantineExponent τ ((r.num : ℝ) / (r.den : ℝ)) := by
    exact helperForTheorem_8_3_not_diophantineExponent_of_rat
      (τ := τ) (p := r.num) (q := r.den) (hq := Rat.den_pos r)
  simpa [hr] using hrat

/-- Helper for Theorem 8.3: the embedded rationals form a subset of the
fixed-exponent complement. -/
lemma helperForTheorem_8_3_range_rat_subset_complement
    {τ : ℝ} :
    Set.range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  intro x hx
  rcases hx with ⟨r, rfl⟩
  exact helperForTheorem_8_3_rat_mem_complement (τ := τ) r

/-- Helper for Theorem 8.3: every integer belongs to the complement of the
fixed-exponent Diophantine set. -/
lemma helperForTheorem_8_3_int_mem_complement
    {τ : ℝ} (p : ℤ) :
    (p : ℝ) ∈ {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  change ¬ helperForTheorem_8_3_diophantineExponent τ (p : ℝ)
  have hq1 : (0 : ℕ) < 1 := by
    decide
  simpa using
    helperForTheorem_8_3_not_diophantineExponent_of_rat (τ := τ) (p := p) (q := 1) hq1

/-- Helper for Theorem 8.3: the complement of the fixed-exponent Diophantine set is
nonempty (for instance, it contains rational numbers). -/
lemma helperForTheorem_8_3_complement_nonempty
    {τ : ℝ} :
    Set.Nonempty {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  refine ⟨0, ?_⟩
  simpa using helperForTheorem_8_3_int_mem_complement (τ := τ) (p := (0 : ℤ))

/-- Helper for Theorem 8.3: the complement of the fixed-exponent Diophantine set is
infinite because it contains every integer. -/
lemma helperForTheorem_8_3_complement_infinite
    {τ : ℝ} :
    Set.Infinite {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  have hsubset :
      Set.range ((↑) : ℤ → ℝ) ⊆ {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    exact helperForTheorem_8_3_int_mem_complement (τ := τ) p
  have hIntRangeInfinite : (Set.range ((↑) : ℤ → ℝ)).Infinite := by
    exact Set.infinite_range_of_injective (f := ((↑) : ℤ → ℝ)) Int.cast_injective
  exact Set.Infinite.mono hsubset hIntRangeInfinite

/-- Helper for Theorem 8.3: negating the fixed-exponent Diophantine lower-bound is
equivalent to saying that every positive constant is violated by some rational
approximation. -/
lemma helperForTheorem_8_3_not_diophantineExponent_iff_forall_pos_constant_exists_close_rational
    {τ x : ℝ} :
    ¬ helperForTheorem_8_3_diophantineExponent τ x ↔
      ∀ c : ℝ, 0 < c →
        ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧
          |x - (p : ℝ) / (q : ℝ)| < c / (q : ℝ) ^ τ := by
  constructor
  · intro hnot c hc
    by_contra hcontra
    have hbound :
        ∀ p : ℤ, ∀ q : ℕ, 0 < q →
          |x - (p : ℝ) / (q : ℝ)| ≥ c / (q : ℝ) ^ τ := by
      intro p q hq
      have hnotlt :
          ¬ |x - (p : ℝ) / (q : ℝ)| < c / (q : ℝ) ^ τ := by
        intro hlt
        exact hcontra ⟨p, q, hq, hlt⟩
      exact le_of_not_gt hnotlt
    exact hnot ⟨c, hc, hbound⟩
  · intro hforall hdioph
    rcases hdioph with ⟨c, hc, hbound⟩
    rcases hforall c hc with ⟨p, q, hq, hlt⟩
    exact (not_lt_of_ge (hbound p q hq)) hlt

/-- Helper for Theorem 8.3: if `τ ≤ τ'`, then the complement of the `τ'`-Diophantine
set is contained in the complement of the `τ`-Diophantine set. -/
lemma helperForTheorem_8_3_complement_antitone_in_exponent
    {τ τ' : ℝ} (hττ' : τ ≤ τ') :
    {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ' x} ⊆
      {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  intro x hx
  intro hxτ
  exact hx
    (helperForTheorem_8_3_monotone_in_exponent
      (τ := τ) (τ' := τ') (x := x) hττ' hxτ)

/-- Helper for Theorem 8.3: the complement-measure is antitone with respect to
the Diophantine exponent. -/
lemma helperForTheorem_8_3_volume_complement_antitone_in_exponent
    {τ τ' : ℝ} (hττ' : τ ≤ τ') :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ' x} ≤
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} := by
  exact MeasureTheory.measure_mono
    (helperForTheorem_8_3_complement_antitone_in_exponent (τ := τ) (τ' := τ') hττ')

/-- Helper for Theorem 8.3: if a fixed exponent `τ > 1` Diophantine lower bound holds
Lebesgue-almost everywhere, then `IsDiophantineReal` also holds almost everywhere. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_of_ae_diophantineExponent_gt_one
    {τ : ℝ} (hτ : 1 < τ)
    (hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
  filter_upwards [hae] with x hx
  exact helperForTheorem_8_3_isDiophantineReal_of_diophantineExponent_gt_one hτ hx

/-- Helper for Theorem 8.3: an almost-everywhere fixed-exponent bound with `τ > 1`
forces the complement of `IsDiophantineReal` to have Lebesgue measure zero. -/
lemma helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_ae_diophantineExponent_gt_one
    {τ : ℝ} (hτ : 1 < τ)
    (hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) :
    MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  have haeDioph : ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
    exact helperForTheorem_8_3_ae_isDiophantineReal_of_ae_diophantineExponent_gt_one
      (τ := τ) hτ hae
  simpa [MeasureTheory.ae_iff] using haeDioph

/-- Helper for Theorem 8.3: a full-measure fixed-exponent Diophantine pair with `τ > 1`
implies that `IsDiophantineReal` holds almost everywhere. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair
    {τ : ℝ} (hτ : 1 < τ)
    (hpair : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
  exact helperForTheorem_8_3_ae_isDiophantineReal_of_ae_diophantineExponent_gt_one
    (τ := τ) hτ hpair.2

/-- Helper for Theorem 8.3: a full-measure fixed-exponent Diophantine pair with `τ > 1`
forces the non-diophantine set to have measure zero. -/
lemma helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair
    {τ : ℝ} (hτ : 1 < τ)
    (hpair : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  exact helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_ae_diophantineExponent_gt_one
    (τ := τ) hτ hpair.2

/-- Helper for Theorem 8.3: at exponent `τ = 2`, the origin fails the fixed-exponent
Diophantine lower bound. -/
lemma helperForTheorem_8_3_zero_not_diophantineExponent_two :
    ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) 0 := by
  simpa using helperForTheorem_8_3_int_mem_complement (τ := (2 : ℝ)) (p := (0 : ℤ))

/-- Helper for Theorem 8.3: at exponent `τ = 2`, every integer lies in the complement
of the fixed-exponent Diophantine set. -/
lemma helperForTheorem_8_3_int_mem_complement_two
    (p : ℤ) :
    (p : ℝ) ∈ {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} := by
  exact helperForTheorem_8_3_int_mem_complement (τ := (2 : ℝ)) (p := p)

/-- Helper for Theorem 8.3: at exponent `τ = 2`, the complement of the fixed-exponent
Diophantine set is nonempty. -/
lemma helperForTheorem_8_3_complement_nonempty_two :
    Set.Nonempty {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} := by
  exact helperForTheorem_8_3_complement_nonempty (τ := (2 : ℝ))

/-- Helper for Theorem 8.3: a full-measure fixed-exponent pair at `τ = 2` implies
`IsDiophantineReal` almost everywhere. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair_two
    (hpair : MeasureTheory.volume
      {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x)) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
  have htwo : 1 < (2 : ℝ) := by
    norm_num
  exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair
    (τ := (2 : ℝ)) htwo hpair

/-- Helper for Theorem 8.3: a full-measure fixed-exponent pair at `τ = 2` forces
the non-diophantine set to have Lebesgue measure zero. -/
lemma helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair_two
    (hpair : MeasureTheory.volume
      {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x)) :
    MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  have htwo : 1 < (2 : ℝ) := by
    norm_num
  exact helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair
    (τ := (2 : ℝ)) htwo hpair

/-- Helper for Theorem 8.3: at `τ = 2`, a full-measure fixed-exponent pair yields
both almost-everywhere `IsDiophantineReal` and measure-zero non-diophantine complement. -/
lemma helperForTheorem_8_3_consequences_of_full_measure_pair_two
    (hpair : MeasureTheory.volume
      {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x)) :
    (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) ∧
      MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  refine ⟨?_, ?_⟩
  · exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair_two hpair
  · exact helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair_two hpair

/-- Helper for Theorem 8.3: any universal fixed-exponent full-measure claim for
all `τ > 1` specializes to the case `τ = 2`. -/
lemma helperForTheorem_8_3_full_measure_pair_two_of_universal_fixed_exponent_claim
    (hall :
      ∀ τ : ℝ, 1 < τ →
        MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
          (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume,
        helperForTheorem_8_3_diophantineExponent (2 : ℝ) x) := by
  have htwo : (1 : ℝ) < (2 : ℝ) := by
    norm_num
  exact hall (2 : ℝ) htwo

/-- Helper for Theorem 8.3: a universal fixed-exponent full-measure claim would
imply `IsDiophantineReal` almost everywhere by specializing to `τ = 2`. -/
lemma helperForTheorem_8_3_ae_isDiophantineReal_of_universal_fixed_exponent_claim
    (hall :
      ∀ τ : ℝ, 1 < τ →
        MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
          (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
  have hpair_two :
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x) := by
    exact helperForTheorem_8_3_full_measure_pair_two_of_universal_fixed_exponent_claim hall
  exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair_two hpair_two

/-- Helper for Theorem 8.3: a universal fixed-exponent full-measure claim would
force the non-diophantine set to have Lebesgue measure zero. -/
lemma helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_universal_fixed_exponent_claim
    (hall :
      ∀ τ : ℝ, 1 < τ →
        MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
          (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  have hpair_two :
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x) := by
    exact helperForTheorem_8_3_full_measure_pair_two_of_universal_fixed_exponent_claim hall
  exact helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair_two hpair_two

/-- Helper for Theorem 8.3: a universal fixed-exponent full-measure claim yields both
almost-everywhere `IsDiophantineReal` and measure-zero non-diophantine complement. -/
lemma helperForTheorem_8_3_consequences_of_universal_fixed_exponent_claim
    (hall :
      ∀ τ : ℝ, 1 < τ →
        MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
          (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) ∧
      MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  have hpair_two :
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent (2 : ℝ) x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume,
          helperForTheorem_8_3_diophantineExponent (2 : ℝ) x) := by
    exact helperForTheorem_8_3_full_measure_pair_two_of_universal_fixed_exponent_claim hall
  exact helperForTheorem_8_3_consequences_of_full_measure_pair_two hpair_two

/-- Helper for Theorem 8.3: once the fixed-exponent complement has measure zero, one
gets both the almost-everywhere exponent-`τ` bound and almost-everywhere
`IsDiophantineReal` (for `τ > 1`). -/
lemma helperForTheorem_8_3_ae_consequences_of_volume_complement_zero
    {τ : ℝ} (hτ : 1 < τ)
    (hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0) :
    (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) := by
  have hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x := by
    exact helperForTheorem_8_3_ae_of_volume_complement_zero (τ := τ) hnull
  have haeDioph : ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
    exact helperForTheorem_8_3_ae_isDiophantineReal_of_ae_diophantineExponent_gt_one
      (τ := τ) hτ hae
  exact ⟨hae, haeDioph⟩

/-- Helper for Theorem 8.3: for a fixed exponent `τ > 1`, the theorem's target
full-measure pair follows from the null-complement statement. -/
lemma helperForTheorem_8_3_full_measure_pair_of_hτ_and_volume_complement_zero
    {τ : ℝ} (hτ : 1 < τ)
    (hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) := by
  have hconsequences :
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) := by
    exact helperForTheorem_8_3_ae_consequences_of_volume_complement_zero (τ := τ) hτ hnull
  exact ⟨hnull, hconsequences.1⟩

/-- Helper for Theorem 8.3: for a fixed exponent `τ > 1`, proving the theorem's
target pair is equivalent to proving the null-complement statement. -/
lemma helperForTheorem_8_3_full_measure_pair_iff_volume_complement_zero_of_gt_one
    {τ : ℝ} (hτ : 1 < τ) :
    (MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) ↔
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
  constructor
  · intro hpair
    exact hpair.1
  · intro hnull
    exact helperForTheorem_8_3_full_measure_pair_of_hτ_and_volume_complement_zero
      (τ := τ) hτ hnull

/-- Helper for Theorem 8.3: from a fixed exponent `τ > 1` null-complement statement,
one obtains both the theorem's target full-measure pair and almost-everywhere
`IsDiophantineReal`. -/
lemma helperForTheorem_8_3_target_pair_and_ae_isDiophantineReal_of_hτ_and_volume_complement_zero
    {τ : ℝ} (hτ : 1 < τ)
    (hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0) :
    (MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) := by
  have hpair :
      MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) := by
    exact helperForTheorem_8_3_full_measure_pair_of_hτ_and_volume_complement_zero
      (τ := τ) hτ hnull
  have haeDioph : ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
    exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair
      (τ := τ) hτ hpair
  exact ⟨hpair, haeDioph⟩

/-- Helper for Theorem 8.3: for `τ > 1`, augmenting the theorem's target pair with the
derived almost-everywhere `IsDiophantineReal` consequence is equivalent to the target
pair itself. -/
lemma helperForTheorem_8_3_target_pair_iff_target_pair_and_ae_isDiophantineReal
    {τ : ℝ} (hτ : 1 < τ) :
    (MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) ↔
      ((MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) ∧
        (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x)) := by
  constructor
  · intro hpair
    have haeDioph : ∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x := by
      exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair
        (τ := τ) hτ hpair
    exact ⟨hpair, haeDioph⟩
  · intro haugmented
    exact haugmented.1

/-- Helper for Theorem 8.3: for a fixed exponent `τ > 1`, the theorem's target pair
implies both almost-everywhere `IsDiophantineReal` and measure-zero
non-`IsDiophantineReal` complement. -/
lemma helperForTheorem_8_3_consequences_of_target_pair
    {τ : ℝ} (hτ : 1 < τ)
    (hpair : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x)) :
    (∀ᵐ x : ℝ ∂MeasureTheory.volume, IsDiophantineReal x) ∧
      MeasureTheory.volume {x : ℝ | ¬ IsDiophantineReal x} = 0 := by
  refine ⟨?_, ?_⟩
  · exact helperForTheorem_8_3_ae_isDiophantineReal_of_full_measure_pair
      (τ := τ) hτ hpair
  · exact helperForTheorem_8_3_volume_not_isDiophantineReal_zero_of_full_measure_pair
      (τ := τ) hτ hpair

/-- Helper for Theorem 8.3: a nonrational real has a uniform positive lower bound for
`|x - p/q|` against all integers `p` and all positive denominators `q ≤ N`; with
`τ ≥ 0`, this yields a bound of the form `c / q^τ`. -/
lemma helperForTheorem_8_3_positive_lower_bound_for_bounded_denominators_nonrat
    {τ x : ℝ} (hτ : 0 ≤ τ)
    (hx_nonrat : x ∉ Set.range ((↑) : ℚ → ℝ))
    (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → q ≤ N →
        c / (q : ℝ) ^ τ ≤ |x - (p : ℝ) / (q : ℝ)| := by
  have hx_ne_rat : ∀ q : ℚ, x ≠ (q : ℝ) := by
    intro q hq
    exact hx_nonrat ⟨q, hq.symm⟩
  have hx_irr : Irrational x := by
    refine (irrational_iff_ne_rational x).2 ?_
    intro a b hb
    have hq : x ≠ (((a : ℚ) / (b : ℚ) : ℚ) : ℝ) := hx_ne_rat ((a : ℚ) / (b : ℚ))
    have hcast : ((((a : ℚ) / (b : ℚ)) : ℚ) : ℝ) = (a : ℝ) / (b : ℝ) := by
      norm_cast
    simpa [hcast] using hq
  let S : Set ℝ :=
    {ε : ℝ | ∀ q : ℕ, q ≤ N → ∀ p : ℤ, ε ≤ dist x ((p : ℤ) / (q : ℕ))}
  have hS_nhds : S ∈ nhds (0 : ℝ) := by
    simpa [S] using hx_irr.eventually_forall_le_dist_cast_div_of_denom_le N
  rcases Metric.mem_nhds_iff.mp hS_nhds with ⟨ε, hεpos, hεball⟩
  have hhalf_mem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hhalf_nonneg : 0 ≤ ε / 2 := by linarith
    have habs : |ε / 2| = ε / 2 := abs_of_nonneg hhalf_nonneg
    rw [sub_zero, habs]
    linarith
  have hhalf_in_S : ε / 2 ∈ S := hεball hhalf_mem
  have hhalf_pos : 0 < ε / 2 := by linarith
  refine ⟨ε / 2, hhalf_pos, ?_⟩
  intro p q hq hqN
  have hdist : ε / 2 ≤ dist x ((p : ℤ) / (q : ℕ)) := hhalf_in_S q hqN p
  have hhalf_nonneg : 0 ≤ ε / 2 := by linarith
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.2 hq)
  have hqpow_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ τ := by
    exact Real.one_le_rpow hqge1 hτ
  have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ τ := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast hq
    exact Real.rpow_pos_of_pos hqpos τ
  have hmul : ε / 2 ≤ (ε / 2) * (q : ℝ) ^ τ := by
    calc
      ε / 2 = (ε / 2) * 1 := by ring
      _ ≤ (ε / 2) * (q : ℝ) ^ τ := mul_le_mul_of_nonneg_left hqpow_ge1 hhalf_nonneg
  have hdiv_le : (ε / 2) / (q : ℝ) ^ τ ≤ ε / 2 := by
    exact (div_le_iff₀ hqpow_pos).2 hmul
  calc
    (ε / 2) / (q : ℝ) ^ τ ≤ ε / 2 := hdiv_le
    _ ≤ dist x ((p : ℤ) / (q : ℕ)) := hdist
    _ = |x - (p : ℝ) / (q : ℝ)| := by simpa [Real.dist_eq]

/-- Helper for Theorem 8.3: for nonrational `x` and nonnegative exponent `τ`, failure of
the fixed-exponent Diophantine lower bound implies `LiouvilleWith τ x`. -/
lemma helperForTheorem_8_3_liouvilleWith_of_not_diophantineExponent_nonrat
    {τ x : ℝ} (hτ : 0 ≤ τ)
    (hx_nonrat : x ∉ Set.range ((↑) : ℚ → ℝ))
    (hnot : ¬ helperForTheorem_8_3_diophantineExponent τ x) :
    LiouvilleWith τ x := by
  have hclose :
      ∀ c : ℝ, 0 < c →
        ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧
          |x - (p : ℝ) / (q : ℝ)| < c / (q : ℝ) ^ τ :=
    (helperForTheorem_8_3_not_diophantineExponent_iff_forall_pos_constant_exists_close_rational
      (τ := τ) (x := x)).1 hnot
  refine ⟨1, ?_⟩
  refine Filter.frequently_atTop.2 ?_
  intro N
  rcases helperForTheorem_8_3_positive_lower_bound_for_bounded_denominators_nonrat
      (τ := τ) (x := x) hτ hx_nonrat N with ⟨cN, hcN, hboundN⟩
  let c : ℝ := min (cN / 2) 1
  have hcN_half_pos : 0 < cN / 2 := by linarith
  have hc_pos : 0 < c := by
    exact lt_min hcN_half_pos zero_lt_one
  rcases hclose c hc_pos with ⟨p, q, hq, hlt⟩
  have hq_gt : N < q := by
    by_contra hq_not_gt
    have hq_le : q ≤ N := le_of_not_gt hq_not_gt
    have hqpow_pos : (0 : ℝ) < (q : ℝ) ^ τ := by
      have hqposR : (0 : ℝ) < (q : ℝ) := by
        exact_mod_cast hq
      exact Real.rpow_pos_of_pos hqposR τ
    have hq_lt_cN : c / (q : ℝ) ^ τ < cN / (q : ℝ) ^ τ := by
      have hc_lt_cN : c < cN := by
        have hc_le_half : c ≤ cN / 2 := min_le_left _ _
        have hc_half_lt : cN / 2 < cN := by linarith
        exact lt_of_le_of_lt hc_le_half hc_half_lt
      exact div_lt_div_of_pos_right hc_lt_cN hqpow_pos
    have hq_ge_cN : cN / (q : ℝ) ^ τ ≤ |x - (p : ℝ) / (q : ℝ)| :=
      hboundN p q hq hq_le
    have hq_ge_c : c / (q : ℝ) ^ τ ≤ |x - (p : ℝ) / (q : ℝ)| :=
      le_trans (le_of_lt hq_lt_cN) hq_ge_cN
    exact (not_lt_of_ge hq_ge_c) hlt
  have hqposR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hqpow_nonneg : (0 : ℝ) ≤ (q : ℝ) ^ τ := by
    exact le_of_lt (Real.rpow_pos_of_pos hqposR τ)
  have hc_le_one : c ≤ 1 := min_le_right _ _
  have hlt_one : |x - (p : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ τ := by
    have hdiv_le : c / (q : ℝ) ^ τ ≤ 1 / (q : ℝ) ^ τ :=
      div_le_div_of_nonneg_right hc_le_one hqpow_nonneg
    exact lt_of_lt_of_le hlt hdiv_le
  have hneq : x ≠ (p : ℝ) / (q : ℝ) := by
    intro hEq
    apply hx_nonrat
    refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
    have hcast : (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) = (p : ℝ) / (q : ℝ) := by
      norm_cast
    exact hcast.trans hEq.symm
  refine ⟨q, le_of_lt hq_gt, ?_⟩
  exact ⟨p, hneq, hlt_one⟩

/-- Helper for Theorem 8.3: the complement of the fixed-exponent Diophantine set is
contained in the union of the embedded rationals and the fixed-exponent Liouville set
(for nonnegative exponent). -/
lemma helperForTheorem_8_3_complement_subset_rat_or_liouvilleWith
    {τ : ℝ} (hτ : 0 ≤ τ) :
    {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} ⊆
      Set.range ((↑) : ℚ → ℝ) ∪ {x : ℝ | LiouvilleWith τ x} := by
  intro x hx
  by_cases hxrat : x ∈ Set.range ((↑) : ℚ → ℝ)
  · exact Or.inl hxrat
  · exact Or.inr
      (helperForTheorem_8_3_liouvilleWith_of_not_diophantineExponent_nonrat
        (τ := τ) (x := x) hτ hxrat hx)

/-- Helper for Theorem 8.3: for `τ > 2`, the complement of the fixed-exponent
Diophantine set has Lebesgue measure zero. -/
lemma helperForTheorem_8_3_volume_complement_zero_of_gt_two
    {τ : ℝ} (hτ : 2 < τ) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
  have hτ_nonneg : 0 ≤ τ := by linarith
  have hsubset :
      {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} ⊆
        Set.range ((↑) : ℚ → ℝ) ∪ {x : ℝ | LiouvilleWith τ x} :=
    helperForTheorem_8_3_complement_subset_rat_or_liouvilleWith (τ := τ) hτ_nonneg
  have hRnull : MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ)) = 0 := by
    exact Set.Countable.measure_zero (Set.countable_range ((↑) : ℚ → ℝ)) MeasureTheory.volume
  have hLnull : MeasureTheory.volume {x : ℝ | LiouvilleWith τ x} = 0 := by
    exact helperForProposition_8_6_volume_setOf_liouvilleWith_zero (p := τ) hτ
  have hUnionNull :
      MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ) ∪ {x : ℝ | LiouvilleWith τ x}) = 0 := by
    rw [MeasureTheory.measure_union_null hRnull hLnull]
  exact MeasureTheory.measure_mono_null hsubset hUnionNull

/-- Theorem 8.3: if `τ > 2`, then the set of real numbers `x` for which there exists
`c(x) > 0` such that `|x - p/q| ≥ c(x) / q^τ` for all `p ∈ ℤ` and `q ∈ ℕ` with `q > 0`
has full Lebesgue measure; equivalently, this Diophantine bound holds for
Lebesgue-almost every real `x`. -/
theorem theorem_8_3_full_measure_diophantine_exponent
    {τ : ℝ} (hτ : 2 < τ) :
    MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 ∧
      (∀ᵐ x : ℝ ∂MeasureTheory.volume, helperForTheorem_8_3_diophantineExponent τ x) := by
  have hτ_one : 1 < τ := by linarith
  have hnull : MeasureTheory.volume {x : ℝ | ¬ helperForTheorem_8_3_diophantineExponent τ x} = 0 := by
    exact helperForTheorem_8_3_volume_complement_zero_of_gt_two (τ := τ) hτ
  exact helperForTheorem_8_3_full_measure_pair_of_hτ_and_volume_complement_zero
    (τ := τ) hτ_one hnull

/-- Helper for Proposition 8.7: the shifted geometric series with ratio `1/2` is finite in
`ℝ≥0∞`. -/
lemma helperForProposition_8_7_geometric_series_ne_top :
    (∑' n : ℕ, (1 / 2 : ENNReal) ^ (n + 1)) ≠ ⊤ := by
  have hgeom :
      (∑' n : ℕ, (1 / 2 : ENNReal) ^ (n + 1)) =
        (1 / 2 : ENNReal) * (1 - (1 / 2 : ENNReal))⁻¹ := by
    simpa using ENNReal.tsum_geometric_add_one (1 / 2 : ENNReal)
  have hhalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ := by
    simp
  have hsub_ne_zero : (1 - (1 / 2 : ENNReal)) ≠ 0 := by
    norm_num
  have hinv_ne_top : ((1 - (1 / 2 : ENNReal))⁻¹) ≠ ⊤ := (ENNReal.inv_ne_top).2 hsub_ne_zero
  rw [hgeom]
  exact ENNReal.mul_ne_top hhalf_ne_top hinv_ne_top

/-- Helper for Proposition 8.7: Markov/Chebyshev gives the superlevel-set measure bound
`m({x | 2^{-(n+1)} ≤ f_{n+1}(x)}) ≤ 2^{-(n+1)}`. -/
lemma helperForProposition_8_7_superlevel_measure_bound
    (f : ℕ → ℝ → ℝ)
    (hmeas : ∀ n : ℕ, AEMeasurable (f n) MeasureTheory.volume)
    (hintegral :
      ∀ n : ℕ, 1 ≤ n →
        (∫⁻ x : ℝ, ENNReal.ofReal (f n x) ∂MeasureTheory.volume) ≤
          (1 / 4 : ENNReal) ^ n)
    (n : ℕ) :
    MeasureTheory.volume
        {x : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) x)} ≤
      ((1 / 2 : ENNReal) ^ (n + 1)) := by
  have hhalf_ne_zero : (1 / 2 : ENNReal) ≠ 0 := by
    norm_num
  have hhalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ := by
    simp
  have hhalf_pow_ne_zero : ((1 / 2 : ENNReal) ^ (n + 1)) ≠ 0 := by
    exact pow_ne_zero _ hhalf_ne_zero
  have hhalf_pow_ne_top : ((1 / 2 : ENNReal) ^ (n + 1)) ≠ ⊤ := by
    exact ENNReal.pow_ne_top hhalf_ne_top
  have hmarkov :=
    MeasureTheory.meas_ge_le_lintegral_div
      ((hmeas (n + 1)).ennreal_ofReal) hhalf_pow_ne_zero hhalf_pow_ne_top
  have hIntBound :
      (∫⁻ x : ℝ, ENNReal.ofReal (f (n + 1) x) ∂MeasureTheory.volume) ≤
        (1 / 4 : ENNReal) ^ (n + 1) := by
    exact hintegral (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hquarter_pow :
      (1 / 4 : ENNReal) ^ (n + 1) =
        ((1 / 2 : ENNReal) ^ (n + 1)) * ((1 / 2 : ENNReal) ^ (n + 1)) := by
    have hquarter_eq : (1 / 4 : ENNReal) = (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
      have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by
        norm_num
      have htwo_ne_top : (2 : ENNReal) ≠ ⊤ := by
        simp
      calc
        (1 / 4 : ENNReal) = (4 : ENNReal)⁻¹ := by
          simp [one_div]
        _ = ((2 : ENNReal) * (2 : ENNReal))⁻¹ := by
          norm_num
        _ = (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv (a := (2 : ENNReal)) (b := (2 : ENNReal))
            (Or.inl htwo_ne_zero) (Or.inl htwo_ne_top)]
        _ = (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
          simp [one_div]
    calc
      (1 / 4 : ENNReal) ^ (n + 1)
          = ((1 / 2 : ENNReal) * (1 / 2 : ENNReal)) ^ (n + 1) := by
            simp [hquarter_eq]
      _ = ((1 / 2 : ENNReal) ^ (n + 1)) * ((1 / 2 : ENNReal) ^ (n + 1)) := by
            simpa using (mul_pow (1 / 2 : ENNReal) (1 / 2 : ENNReal) (n + 1))
  calc
    MeasureTheory.volume
        {x : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) x)}
        ≤ (∫⁻ x : ℝ, ENNReal.ofReal (f (n + 1) x) ∂MeasureTheory.volume) /
          ((1 / 2 : ENNReal) ^ (n + 1)) := hmarkov
    _ ≤ ((1 / 4 : ENNReal) ^ (n + 1)) / ((1 / 2 : ENNReal) ^ (n + 1)) := by
          exact ENNReal.div_le_div_right hIntBound ((1 / 2 : ENNReal) ^ (n + 1))
    _ = (((1 / 2 : ENNReal) ^ (n + 1)) * ((1 / 2 : ENNReal) ^ (n + 1))) /
          ((1 / 2 : ENNReal) ^ (n + 1)) := by
          rw [hquarter_pow]
    _ = ((1 / 2 : ENNReal) ^ (n + 1)) := by
          simpa [mul_comm] using ENNReal.mul_div_cancel_right hhalf_pow_ne_zero hhalf_pow_ne_top

/-- Helper for Proposition 8.7: the limsup of superlevel sets has Lebesgue measure zero. -/
lemma helperForProposition_8_7_volume_limsup_zero
    (A : ℕ → Set ℝ)
    (hA : ∀ n : ℕ, MeasureTheory.volume (A n) ≤ (1 / 2 : ENNReal) ^ (n + 1)) :
    MeasureTheory.volume (Filter.limsup A Filter.atTop) = 0 := by
  refine MeasureTheory.measure_limsup_atTop_eq_zero
    (ne_top_of_le_ne_top helperForProposition_8_7_geometric_series_ne_top (ENNReal.tsum_le_tsum hA))

/-- Helper for Proposition 8.7: outside the limsup superlevel set, one eventually has the
pointwise bound `f_{n+1}(x) ≤ 2^{-(n+1)}`. -/
lemma helperForProposition_8_7_eventually_upper_bound_outside_limsup
    (f : ℕ → ℝ → ℝ)
    (hnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ f n x)
    (x : ℝ)
    (hx : x ∉ Filter.limsup
      (fun n : ℕ => {y : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) y)})
      Filter.atTop) :
    ∀ᶠ n : ℕ in Filter.atTop, f (n + 1) x ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have hx_not_frequently : ¬ ∃ᶠ n : ℕ in Filter.atTop,
      x ∈ {y : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) y)} := by
    simpa [Filter.mem_limsup_iff_frequently_mem] using hx
  have hx_eventually_not : ∀ᶠ n : ℕ in Filter.atTop,
      x ∉ {y : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) y)} :=
    (Filter.not_frequently).1 hx_not_frequently
  refine hx_eventually_not.mono ?_
  intro n hxn
  have hlt_enn : ENNReal.ofReal (f (n + 1) x) < (1 / 2 : ENNReal) ^ (n + 1) := by
    exact lt_of_not_ge hxn
  have hhalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ := by
    simp
  have hhalf_pow_ne_top : ((1 / 2 : ENNReal) ^ (n + 1)) ≠ ⊤ := by
    exact ENNReal.pow_ne_top hhalf_ne_top
  have hlt_real : f (n + 1) x < ((1 / 2 : ENNReal) ^ (n + 1)).toReal := by
    have hlt_toReal :
        (ENNReal.ofReal (f (n + 1) x)).toReal < ((1 / 2 : ENNReal) ^ (n + 1)).toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hhalf_pow_ne_top).2 hlt_enn
    simpa [ENNReal.toReal_ofReal (hnonneg (n + 1) x)] using hlt_toReal
  have hpow_toReal : ((1 / 2 : ENNReal) ^ (n + 1)).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
    simp [ENNReal.toReal_pow]
  exact le_of_lt (hpow_toReal ▸ hlt_real)

/-- Helper for Proposition 8.7: an eventual geometric bound on the shifted sequence implies
`f_n(x) → 0`. -/
lemma helperForProposition_8_7_tendsto_shifted_then_unshift
    (f : ℕ → ℝ → ℝ)
    (x : ℝ)
    (hnonneg : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ f n y)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop, f (n + 1) x ≤ (1 / 2 : ℝ) ^ (n + 1)) :
    Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (nhds (0 : ℝ)) := by
  have hpow_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (0 : ℝ)) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpow_shift_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)
      (l := nhds (0 : ℝ)) 1).2 hpow_tendsto
  have hshift_tendsto :
      Filter.Tendsto (fun n : ℕ => f (n + 1) x) Filter.atTop (nhds (0 : ℝ)) := by
    refine squeeze_zero' ?_ hbound hpow_shift_tendsto
    exact Filter.Eventually.of_forall (fun n : ℕ => hnonneg (n + 1) x)
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => f n x)
    (l := nhds (0 : ℝ)) 1).1 hshift_tendsto

/-- Proposition 8.7: if `(f_n)_{n ≥ 1}` are nonnegative Lebesgue measurable functions
on `ℝ` with `∫⁻ f_n dm ≤ 4^{-n}` for all `n ≥ 1`, then for every `ε > 0` there exists
a Lebesgue measurable set `E` with `m(E) ≤ ε` such that `f_n x → 0` for all
`x ∈ ℝ \ E`. -/
theorem proposition_8_7_tendsto_zero_outside_small_exceptional_set
    (f : ℕ → ℝ → ℝ)
    (hmeas : ∀ n : ℕ, AEMeasurable (f n) MeasureTheory.volume)
    (hnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ f n x)
    (hintegral :
      ∀ n : ℕ, 1 ≤ n →
        (∫⁻ x : ℝ, ENNReal.ofReal (f n x) ∂MeasureTheory.volume) ≤
          (1 / 4 : ENNReal) ^ n) :
    ∀ ε : ℝ, 0 < ε →
      ∃ E : Set ℝ,
        MeasurableSet E ∧
        MeasureTheory.volume E ≤ ENNReal.ofReal ε ∧
        ∀ x ∈ Eᶜ, Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (nhds (0 : ℝ)) := by
  intro ε hε
  let A : ℕ → Set ℝ := fun n : ℕ =>
    {x : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) x)}
  have hA :
      ∀ n : ℕ, MeasureTheory.volume (A n) ≤ (1 / 2 : ENNReal) ^ (n + 1) := by
    intro n
    dsimp [A]
    exact helperForProposition_8_7_superlevel_measure_bound f hmeas hintegral n
  have hlimsup_zero : MeasureTheory.volume (Filter.limsup A Filter.atTop) = 0 := by
    exact helperForProposition_8_7_volume_limsup_zero A hA
  let E : Set ℝ := MeasureTheory.toMeasurable MeasureTheory.volume (Filter.limsup A Filter.atTop)
  have hE_meas : MeasurableSet E := by
    exact MeasureTheory.measurableSet_toMeasurable MeasureTheory.volume (Filter.limsup A Filter.atTop)
  have hE_zero : MeasureTheory.volume E = 0 := by
    dsimp [E]
    rw [MeasureTheory.measure_toMeasurable]
    exact hlimsup_zero
  refine ⟨E, hE_meas, ?_, ?_⟩
  · rw [hE_zero]
    positivity
  · intro x hxE
    have hx_not_E : x ∉ E := by
      simpa [Set.mem_compl_iff] using hxE
    have hx_not_limsup : x ∉ Filter.limsup A Filter.atTop := by
      intro hx_limsup
      exact hx_not_E (MeasureTheory.subset_toMeasurable MeasureTheory.volume (Filter.limsup A Filter.atTop) hx_limsup)
    have hx_not_limsup_superlevel :
        x ∉ Filter.limsup
          (fun n : ℕ =>
            {y : ℝ | ((1 / 2 : ENNReal) ^ (n + 1)) ≤ ENNReal.ofReal (f (n + 1) y)})
          Filter.atTop := by
      simpa [A] using hx_not_limsup
    have hbound :
        ∀ᶠ n : ℕ in Filter.atTop, f (n + 1) x ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      exact helperForProposition_8_7_eventually_upper_bound_outside_limsup
        f hnonneg x hx_not_limsup_superlevel
    exact helperForProposition_8_7_tendsto_shifted_then_unshift f x hnonneg hbound

/-- Helper for Theorem 8.4: measurable functions on `[0,1]` are strongly measurable. -/
lemma helperForTheorem_8_4_stronglyMeasurable_seq_on_Icc
    (f : ℕ → Set.Icc (0 : ℝ) 1 → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (f n)) :
    ∀ n : ℕ, MeasureTheory.StronglyMeasurable (f n) := by
  intro n
  exact (hmeas n).stronglyMeasurable

/-- Helper for Theorem 8.4: pointwise convergence to zero implies almost-everywhere
convergence to the zero function on `[0,1]`. -/
lemma helperForTheorem_8_4_ae_tendsto_zero_on_Icc
    (f : ℕ → Set.Icc (0 : ℝ) 1 → ℝ)
    (hlim : ∀ x : Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (nhds 0)) :
    ∀ᵐ x : Set.Icc (0 : ℝ) 1 ∂MeasureTheory.volume,
      Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop
        (nhds ((fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ)) x)) := by
  refine Filter.Eventually.of_forall ?_
  intro x
  simpa using hlim x

/-- Helper for Theorem 8.4: Egorov's theorem on the finite-measure space `[0,1]`. -/
lemma helperForTheorem_8_4_apply_mathlib_egorov_finite_measure
    (f : ℕ → Set.Icc (0 : ℝ) 1 → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (f n))
    (hlim : ∀ x : Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Set (Set.Icc (0 : ℝ) 1),
      MeasurableSet E ∧
      MeasureTheory.volume E ≤ ENNReal.ofReal ε ∧
      TendstoUniformlyOn (fun n : ℕ => f n) (fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ))
        Filter.atTop Eᶜ := by
  have hstrong :
      ∀ n : ℕ, MeasureTheory.StronglyMeasurable (f n) := by
    exact helperForTheorem_8_4_stronglyMeasurable_seq_on_Icc f hmeas
  have hae :
      ∀ᵐ x : Set.Icc (0 : ℝ) 1 ∂MeasureTheory.volume,
        Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop
          (nhds ((fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ)) x)) := by
    exact helperForTheorem_8_4_ae_tendsto_zero_on_Icc f hlim
  simpa using
    (MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'
      (μ := MeasureTheory.volume)
      (f := fun n : ℕ => f n)
      (g := fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ))
      hstrong
      MeasureTheory.stronglyMeasurable_const
      hae
      hε)

/-- Theorem 8.4 (Egoroff on `[0,1]`): if `(f_n)` are measurable and nonnegative on
`[0,1]` and satisfy `f_n(x) → 0` for every `x ∈ [0,1]`, then for every `ε > 0` there
exists a measurable `E ⊆ [0,1]` with `m(E) ≤ ε` such that `f_n → 0` uniformly on
`[0,1] \ E`. -/
theorem theorem_8_4_egoroff_on_unit_interval
    (f : ℕ → Set.Icc (0 : ℝ) 1 → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (f n))
    (hnonneg : ∀ n : ℕ, ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ f n x)
    (hlim : ∀ x : Set.Icc (0 : ℝ) 1,
      Filter.Tendsto (fun n : ℕ => f n x) Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ E : Set (Set.Icc (0 : ℝ) 1),
        MeasurableSet E ∧
        MeasureTheory.volume E ≤ ENNReal.ofReal ε ∧
        TendstoUniformlyOn (fun n : ℕ => f n) (fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ))
          Filter.atTop Eᶜ := by
  intro ε hε
  exact helperForTheorem_8_4_apply_mathlib_egorov_finite_measure f hmeas hlim hε

/-- Helper for Proposition 8.8: rewrite the shifted diagonal term into Kronecker-delta
form. -/
lemma helperForProposition_8_8_shiftedDiagonal_term_eq_ite_eq
    (n m : ℕ) :
    (((if m + 1 = n + 1 then (1 : NNReal) else 0) : NNReal) : ℝ) =
      (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ) := by
  by_cases h : m = n
  · subst h
    simp
  · simp [h]

/-- Helper for Proposition 8.8: each row of the diagonal indicator has sum `1`. -/
lemma helperForProposition_8_8_row_hasSum_one
    (n : ℕ) :
    HasSum (fun m : ℕ => (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ)) 1 := by
  have hzero :
      ∀ m : ℕ, m ≠ n →
        (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ) = 0 := by
    intro m hm
    simp [hm]
  have hsingle :
      HasSum
        (fun m : ℕ => (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ))
        ((((if n = n then (1 : NNReal) else 0) : NNReal) : ℝ)) := by
    exact hasSum_single n hzero
  simpa using hsingle

/-- Helper for Proposition 8.8: each fixed column converges pointwise to `0`. -/
lemma helperForProposition_8_8_column_tendsto_zero
    (m : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (((if n = m then (1 : NNReal) else 0) : NNReal) : ℝ))
      Filter.atTop (nhds 0) := by
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        (0 : ℝ) = (((if n = m then (1 : NNReal) else 0) : NNReal) : ℝ) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨m + 1, ?_⟩
    intro n hn
    have hne : n ≠ m := by
      intro hnm
      exact Nat.not_succ_le_self m (hnm ▸ hn)
    simp [hne]
  exact Filter.Tendsto.congr' hevent tendsto_const_nhds

/-- Helper for Proposition 8.8: the row sums converge to `1`. -/
lemma helperForProposition_8_8_rowSum_tendsto_one :
    Filter.Tendsto
      (fun n : ℕ => ∑' m : ℕ, (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ))
      Filter.atTop (nhds 1) := by
  have hEventuallyEq :
      (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop]
        (fun n : ℕ => ∑' m : ℕ, (((if m = n then (1 : NNReal) else 0) : NNReal) : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro n
    symm
    exact (helperForProposition_8_8_row_hasSum_one n).tsum_eq
  exact Filter.Tendsto.congr' hEventuallyEq tendsto_const_nhds

/-- Helper for Proposition 8.8: the sum of the pointwise limit function `0` is `0`. -/
lemma helperForProposition_8_8_tsum_of_pointwise_limits_eq_zero :
    (∑' _ : ℕ, (0 : ℝ)) = 0 := by
  exact tsum_zero

/-- Proposition 8.8: there exists a bounded function `f : ℕ × ℕ → ℝ≥0` such that
(i) for every `n`, the series `∑_{m=1}^∞ f(n,m)` converges;
(ii) for every `m`, the limit `lim_{n→∞} f(n,m)` exists;
(iii) nevertheless, the limit of row sums is not equal to the sum of pointwise limits. -/
theorem proposition_8_8_exists_bounded_nonnegative_function_with_noncommuting_limit_and_series :
    ∃ f : ℕ × ℕ → NNReal,
      (∃ C : NNReal, ∀ n m : ℕ, f (n, m) ≤ C) ∧
      (∀ n : ℕ, Summable (fun m : ℕ => (f (n, m + 1) : ℝ))) ∧
      (∀ m : ℕ, ∃ l : ℝ, Filter.Tendsto (fun n : ℕ => (f (n, m + 1) : ℝ)) Filter.atTop (nhds l)) ∧
      (∃ g : ℕ → ℝ,
        (∀ m : ℕ, Filter.Tendsto (fun n : ℕ => (f (n, m + 1) : ℝ)) Filter.atTop (nhds (g m))) ∧
        Summable g ∧
        (∃ L : ℝ,
          Filter.Tendsto (fun n : ℕ => ∑' m : ℕ, (f (n, m + 1) : ℝ)) Filter.atTop (nhds L) ∧
          L ≠ ∑' m : ℕ, g m)) := by
  let f : ℕ × ℕ → NNReal := fun p => if p.2 = p.1 + 1 then 1 else 0
  refine ⟨f, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨(1 : NNReal), ?_⟩
    intro n m
    by_cases h : m = n + 1
    · simp [f, h]
    · simp [f, h]
  · intro n
    have hrow : HasSum (fun m : ℕ => (f (n, m + 1) : ℝ)) 1 := by
      simpa [f, helperForProposition_8_8_shiftedDiagonal_term_eq_ite_eq] using
        (helperForProposition_8_8_row_hasSum_one n)
    exact hrow.summable
  · intro m
    refine ⟨0, ?_⟩
    simpa [f, helperForProposition_8_8_shiftedDiagonal_term_eq_ite_eq, eq_comm] using
      (helperForProposition_8_8_column_tendsto_zero m)
  · refine ⟨fun _ : ℕ => (0 : ℝ), ?_, ?_, ?_⟩
    · intro m
      simpa [f, helperForProposition_8_8_shiftedDiagonal_term_eq_ite_eq, eq_comm] using
        (helperForProposition_8_8_column_tendsto_zero m)
    · exact summable_zero
    · refine ⟨1, ?_, ?_⟩
      · simpa [f, helperForProposition_8_8_shiftedDiagonal_term_eq_ite_eq] using
          helperForProposition_8_8_rowSum_tendsto_one
      · rw [helperForProposition_8_8_tsum_of_pointwise_limits_eq_zero]
        exact one_ne_zero


end Section02
end Chap08
