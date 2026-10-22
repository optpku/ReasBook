/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

variable (n : ℕ) (p q : I)

private theorem absolutelyContinuous_count (μ : Measure ℕ) : μ ≪ Measure.count := by
  refine Measure.AbsolutelyContinuous.mk fun s _ hs0 ↦ ?_
  rw [Measure.count_eq_zero_iff] at hs0
  rw [hs0, measure_empty]

private theorem rnDeriv_ae_eq_singleton (μ : Measure ℕ) :
    μ.rnDeriv Measure.count =ᵐ[Measure.count] fun k : ℕ ↦ μ {k} := by
  have hμ : Measure.count.withDensity (fun k : ℕ ↦ μ {k}) = μ := by
    rw [count_withDensity, Measure.sum_smul_dirac]
  simpa [hμ] using
    (Measure.rnDeriv_withDensity Measure.count (measurable_of_countable (fun k : ℕ ↦ μ {k})))

/-- Zero trials give the deterministic binomial law at `0`. -/
-- Proof sketch: `Set.Iio 0 = ∅`, so the defining Bernoulli product measure is supported on the
-- unique subset `∅`, and `Set.ncard ∅ = 0`.
@[simp] theorem binomial_zero_left :
    Bin(0, p) = Measure.dirac 0 := by
  let μ : Measure ℕ := Bin(0, p)
  have h_id : HasLaw id μ μ := HasLaw.id
  have hμ0 : ∀ᵐ k ∂μ, k = 0 := by
    filter_upwards [ae_le_of_hasLaw_binomial h_id] with k hk
    exact Nat.eq_zero_of_le_zero hk
  have h_restrict : μ.restrict ({0} : Set ℕ) = μ := by
    exact Measure.restrict_eq_self_of_ae_mem (by simpa [μ] using hμ0)
  have hsmul : μ = μ {0} • Measure.dirac 0 := by
    exact h_restrict.symm.trans (Measure.restrict_singleton μ 0)
  have hprob : μ {0} = 1 := by
    have h_univ := congrArg (fun ν : Measure ℕ ↦ ν Set.univ) hsmul
    simpa [μ] using h_univ.symm
  rw [show Bin(0, p) = μ by rfl, hsmul, hprob, one_smul]

/-- The endpoint parameter `p = 0` gives the deterministic binomial law at `0`. -/
-- Proof sketch: for parameter `0`, the underlying set-Bernoulli law is `dirac ∅`, and mapping by
-- `Set.ncard` sends `∅` to `0`.
@[simp] theorem binomial_zero_right :
    Bin(n, (0 : I)) = Measure.dirac 0 := by
  rw [ProbabilityTheory.binomial, setBernoulli_zero]
  simp

/-- The endpoint parameter `p = 1` gives the deterministic binomial law at `n`. -/
-- Proof sketch: for parameter `1`, the underlying set-Bernoulli law is `dirac (Set.Iio n)`, and
-- `Set.ncard (Set.Iio n) = n`.
@[simp] theorem binomial_one_right :
    Bin(n, (1 : I)) = Measure.dirac n := by
  rw [ProbabilityTheory.binomial, setBernoulli_one]
  simp

/-- Helper for Exercise 7.4.2: the subsets of `Set.Iio n` with cardinality `k` are exactly the
coercions of `((Finset.range n).powersetCard k)`. -/
private lemma cardinalityEvent_eq_image_powersetCardRange (n k : ℕ) :
    {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} =
      ((((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ)) : Set (Set ℕ)) := by
  classical
  -- Convert finite subsets of `Set.Iio n` to `Finset`s and back.
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hsub, hcard⟩
    let hsfin : s.Finite := (Set.finite_Iio n).subset hsub
    refine Finset.mem_coe.2 <| Finset.mem_image.2 ?_
    refine ⟨hsfin.toFinset, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        simpa [Set.mem_Iio, hsfin.coe_toFinset] using hsub (by simpa [hsfin.coe_toFinset] using hx)
      · rw [← Set.ncard_coe_finset, hsfin.coe_toFinset, hcard]
    · simp [hsfin.coe_toFinset]
  · intro hs
    rcases Finset.mem_coe.1 hs with hs
    rcases Finset.mem_image.1 hs with ⟨t, ht, rfl⟩
    rw [Finset.mem_powersetCard] at ht
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_range.mp (ht.1 (by simpa using hx))
    · simpa using ht.2

/-- Helper for Exercise 7.4.2: the `setBernoulli` law on `Set.Iio n` assigns the usual binomial
mass to the event that the chosen subset has cardinality `k`, viewed in `ℝ`. -/
private lemma setBernoulliIio_apply_card_toReal (n k : ℕ) (p : I) :
    (setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k}).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  classical
  -- Rewrite the cardinality event as a finite image of `powersetCard`.
  change (setBer(Set.Iio n, p)).real {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} = _
  rw [cardinalityEvent_eq_image_powersetCardRange]
  let A : Finset (Set ℕ) := (((Finset.range n).powersetCard k).image ((↑) : Finset ℕ → Set ℕ))
  rw [← MeasureTheory.sum_measureReal_singleton (μ := setBer(Set.Iio n, p)) A]
  have hterm :
      ∀ s ∈ A,
        (setBer(Set.Iio n, p)).real {s} = (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
    intro s hs
    have hs' : ∃ t, t ∈ (Finset.range n).powersetCard k ∧ ((↑t : Set ℕ) = s) := by
      simpa [A] using hs
    rcases hs' with ⟨t, ht, rfl⟩
    rw [Finset.mem_powersetCard] at ht
    have hsubset : (↑t : Set ℕ) ⊆ Set.Iio n := by
      intro x hx
      exact Finset.mem_range.mp (ht.1 (by simpa using hx))
    have hsingle :
        (setBer(Set.Iio n, p)).real {(↑t : Set ℕ)} =
          (p : ℝ) ^ (↑t : Set ℕ).ncard * (1 - (p : ℝ)) ^ ((Set.Iio n \ (↑t : Set ℕ)).ncard) := by
      -- Evaluate each singleton mass with `setBernoulli_singleton`.
      rw [measureReal_def,
        ProbabilityTheory.setBernoulli_singleton (s := (↑t : Set ℕ)) (u := Set.Iio n)
          (p := p) hsubset (Set.finite_Iio n), ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_pow]
      · simp
    simpa [Set.ncard_coe_finset, Set.ncard_diff hsubset, Set.ncard_Iio_nat, ht.2] using hsingle
  have hcardA : A.card = Nat.choose n k := by
    -- Count the cardinality-`k` subsets of `range n`.
    unfold A
    rw [Finset.card_image_of_injective _ Finset.coe_injective]
    simpa using (Finset.card_powersetCard k (Finset.range n))
  calc
    ∑ s ∈ A, (setBer(Set.Iio n, p)).real {s}
      = ∑ s ∈ A, (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact hterm s hs
    _ = (A.card : ℝ) * ((p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
          rw [hcardA]
          ring

/-- Helper for Exercise 7.4.2: the singleton masses of the binomial law are given by the standard
choose formula, viewed in `ℝ`. -/
private lemma binomial_apply_singleton_toReal (n k : ℕ) (p : I) :
    (Bin(n, p) ({k} : Set ℕ)).toReal =
      (Nat.choose n k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  -- Rewrite the `Bin(n, p)` singleton as the cardinality event under `setBer(Set.Iio n, p)`.
  rw [ProbabilityTheory.binomial, Measure.map_apply measurable_ncard (measurableSet_singleton k)]
  have hpreimage :
      Set.ncard ⁻¹' ({k} : Set ℕ) = {s : Set ℕ | s.ncard = k} := by
    ext s
    simp
  rw [hpreimage]
  have hμ :
      setBer(Set.Iio n, p) {s : Set ℕ | s.ncard = k} =
        setBer(Set.Iio n, p) {s : Set ℕ | s ⊆ Set.Iio n ∧ s.ncard = k} := by
    -- Outside `Set.Iio n`, the `setBernoulli` law has zero mass.
    refine measure_congr ?_
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Set.Iio n) (p := p)] with s hs
    apply propext
    constructor
    · intro hk
      exact ⟨hs, hk⟩
    · intro hk
      exact hk.2
  rw [hμ]
  exact setBernoulliIio_apply_card_toReal n k p

/-- Helper for Exercise 7.4.2: on `ℕ`, absolute continuity is equivalent to preserving null
singleton atoms. -/
private theorem absolutelyContinuous_iff_forall_singleton {μ ν : Measure ℕ} :
    μ ≪ ν ↔ ∀ k : ℕ, ν ({k} : Set ℕ) = 0 → μ ({k} : Set ℕ) = 0 := by
  constructor
  · -- Any absolutely continuous measure sends every `ν`-null singleton to a `μ`-null singleton.
    intro h k hk
    exact h hk
  · -- On a countable space, nullity of a measurable set is equivalent to nullity of its atoms.
    intro h
    refine Measure.AbsolutelyContinuous.mk fun s _ hs0 ↦ ?_
    rw [MeasureTheory.measure_null_iff_singleton (Set.to_countable s)] at hs0 ⊢
    intro k hk
    exact h k (hs0 k hk)

/-- Helper for Exercise 7.4.2: atoms above `n` lie outside the support of `Bin(n, p)`. -/
private lemma binomial_apply_singleton_eq_zero_of_lt {k : ℕ} (hk : n < k) :
    Bin(n, p) ({k} : Set ℕ) = 0 := by
  -- Rewrite the singleton mass by the explicit binomial formula and kill the choose factor.
  have hreal : (Bin(n, p) ({k} : Set ℕ)).toReal = 0 := by
    rw [binomial_apply_singleton_toReal]
    rw [Nat.choose_eq_zero_of_lt hk]
    simp
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_ne_top _ _)

/-- Helper for Exercise 7.4.2: for interior parameters, every atom `{k}` with `k ≤ n` has
positive `Bin(n, p)` mass. -/
private lemma binomial_apply_singleton_ne_zero_of_le_of_ne_zero_of_ne_one {k : ℕ} (hk : k ≤ n)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    Bin(n, p) ({k} : Set ℕ) ≠ 0 := by
  -- Inside the support range, each factor in the explicit binomial formula is nonzero.
  have hp0' : (p : ℝ) ≠ 0 := by
    simpa using hp0
  have hp1' : (1 - (p : ℝ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hp1''
    apply hp1
    exact Subtype.ext hp1''.symm
  have hreal : (Bin(n, p) ({k} : Set ℕ)).toReal ≠ 0 := by
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hpow0 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp0'
    have hpow1 : (1 - (p : ℝ)) ^ (n - k) ≠ 0 := pow_ne_zero (n - k) hp1'
    rw [binomial_apply_singleton_toReal]
    exact mul_ne_zero (mul_ne_zero hchoose hpow0) hpow1
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- Helper for Exercise 7.4.2: the right endpoint atom `{n}` has positive mass whenever `p ≠ 0`.
-/
private lemma binomial_apply_singleton_self_ne_zero (hp0 : p ≠ 0) :
    Bin(n, p) ({n} : Set ℕ) ≠ 0 := by
  -- At `k = n`, the explicit formula reduces to `p ^ n`.
  have hp0' : (p : ℝ) ≠ 0 := by
    simpa using hp0
  have hreal : (Bin(n, p) ({n} : Set ℕ)).toReal ≠ 0 := by
    rw [binomial_apply_singleton_toReal, Nat.choose_self, Nat.sub_self, pow_zero]
    simpa using mul_ne_zero one_ne_zero (pow_ne_zero n hp0')
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- Helper for Exercise 7.4.2: the left endpoint atom `{0}` has positive mass whenever `p ≠ 1`.
-/
private lemma binomial_apply_singleton_zero_ne_zero (hp1 : p ≠ 1) :
    Bin(n, p) ({0} : Set ℕ) ≠ 0 := by
  -- At `k = 0`, the explicit formula reduces to `(1 - p) ^ n`.
  have hp1' : (1 - (p : ℝ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hp1''
    apply hp1
    exact Subtype.ext hp1''.symm
  have hreal : (Bin(n, p) ({0} : Set ℕ)).toReal ≠ 0 := by
    rw [binomial_apply_singleton_toReal, Nat.choose_zero_right, pow_zero]
    simpa [Nat.sub_zero] using
      mul_ne_zero (show (1 : ℝ) * 1 ≠ 0 by norm_num) (pow_ne_zero n hp1')
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- Helper for Exercise 7.4.2: if `q` is strictly between `0` and `1`, then `Bin(n, p)` is
absolutely continuous with respect to `Bin(n, q)`. -/
private theorem binomial_absolutelyContinuous_of_ne_zero_ne_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    Bin(n, p) ≪ Bin(n, q) := by
  -- Reduce absolute continuity to the atomwise support comparison on `ℕ`.
  rw [absolutelyContinuous_iff_forall_singleton]
  intro k hk
  by_cases hk' : k ≤ n
  · exfalso
    exact
      binomial_apply_singleton_ne_zero_of_le_of_ne_zero_of_ne_one (n := n) (p := q) hk' hq0 hq1 hk
  · -- Outside `{0, ..., n}`, both binomial laws vanish.
    exact binomial_apply_singleton_eq_zero_of_lt (n := n) (p := p) (lt_of_not_ge hk')

/-- Exercise 7.4.2: the binomial law `Bin(n, p)` is absolutely continuous with respect to
`Bin(n, q)` exactly in the trivial case `n = 0`, or else when the degenerate endpoint values of
`q` force the same endpoint values for `p`. -/
-- Proof sketch: identify when the support of `Bin(n, p)` is contained in the support of
-- `Bin(n, q)`. For `n = 0` both laws equal `dirac 0`, while for `n > 0` the only
-- obstructions come from the degenerate endpoint cases `q = 0` and `q = 1`.
theorem binomial_absolutelyContinuous_iff :
    Bin(n, p) ≪ Bin(n, q) ↔
      n = 0 ∨ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  constructor
  · intro h
    by_cases hn : n = 0
    · -- For zero trials, both binomial laws are the same deterministic measure.
      exact Or.inl hn
    · refine Or.inr ?_
      constructor
      · intro hq0
        by_cases hp0 : p = 0
        · exact hp0
        · -- If `q = 0`, the atom `{n}` is null under `Bin(n, q)` but not under `Bin(n, p)`.
          have hq_atom : Bin(n, q) ({n} : Set ℕ) = 0 := by
            rw [hq0, binomial_zero_right]
            simp [hn]
          have hp_atom : Bin(n, p) ({n} : Set ℕ) ≠ 0 :=
            binomial_apply_singleton_self_ne_zero (n := n) (p := p) hp0
          exact (hp_atom (h hq_atom)).elim
      · intro hq1
        by_cases hp1 : p = 1
        · exact hp1
        · -- If `q = 1`, the atom `{0}` is null under `Bin(n, q)` but not under `Bin(n, p)`.
          have hq_atom : Bin(n, q) ({0} : Set ℕ) = 0 := by
            rw [hq1, binomial_one_right]
            simp [hn]
          have hp_atom : Bin(n, p) ({0} : Set ℕ) ≠ 0 :=
            binomial_apply_singleton_zero_ne_zero (n := n) (p := p) hp1
          exact (hp_atom (h hq_atom)).elim
  · intro h
    rcases h with hn | hq
    · -- Zero trials reduce both laws to the same Dirac mass.
      simpa [hn] using (show Measure.dirac 0 ≪ Measure.dirac 0 from Measure.AbsolutelyContinuous.rfl)
    · by_cases hq0 : q = 0
      · -- When `q = 0`, the hypothesis forces `p = 0`, so both measures coincide.
        have hp0 : p = 0 := hq.1 hq0
        simpa [hq0, hp0] using
          (show Measure.dirac 0 ≪ Measure.dirac 0 from Measure.AbsolutelyContinuous.rfl)
      · by_cases hq1 : q = 1
        · -- When `q = 1`, the hypothesis forces `p = 1`, so both measures coincide.
          have hp1 : p = 1 := hq.2 hq1
          simpa [hq1, hp1] using
            (show Measure.dirac n ≪ Measure.dirac n from Measure.AbsolutelyContinuous.rfl)
        · -- The remaining case is the interior-parameter support comparison.
          exact binomial_absolutelyContinuous_of_ne_zero_ne_one (n := n) (p := p) (q := q) hq0 hq1

/-- The Radon--Nikodym derivative of one binomial law with respect to another is the ratio of
their singleton masses, almost everywhere with respect to the reference binomial law. -/
-- Proof sketch: on the countable measurable space `ℕ`, evaluate the Radon--Nikodym identity on
-- singleton sets and rewrite the resulting atoms as the singleton masses of the two binomial
-- measures.
theorem binomial_rnDeriv_ae_eq_singleton_ratio :
    (Bin(n, p)).rnDeriv (Bin(n, q)) =ᵐ[Bin(n, q)] fun k : ℕ ↦
      Bin(n, p) {k} / Bin(n, q) {k} := by
  let μ : Measure ℕ := Bin(n, p)
  let ν : Measure ℕ := Bin(n, q)
  have hμc : μ ≪ Measure.count := absolutelyContinuous_count μ
  have hνc : ν ≪ Measure.count := absolutelyContinuous_count ν
  have h_div :
      μ.rnDeriv ν =ᵐ[ν] fun k : ℕ ↦ μ.rnDeriv Measure.count k / ν.rnDeriv Measure.count k :=
    Measure.rnDeriv_eq_div hμc hνc
  have hμ_count : (fun k ↦ μ.rnDeriv Measure.count k) =ᵐ[ν] fun k ↦ μ {k} :=
    Measure.AbsolutelyContinuous.ae_eq hνc (rnDeriv_ae_eq_singleton μ)
  have hν_count : (fun k ↦ ν.rnDeriv Measure.count k) =ᵐ[ν] fun k ↦ ν {k} :=
    Measure.AbsolutelyContinuous.ae_eq hνc (rnDeriv_ae_eq_singleton ν)
  filter_upwards [h_div, hμ_count, hν_count] with k h1 h2 h3
  rw [h2, h3] at h1
  simpa [μ, ν] using h1
