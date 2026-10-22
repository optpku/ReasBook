/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {f : Ω → ℝ≥0∞}

-- Proof sketch: take the canonical approximating sequence `SimpleFunc.eapprox f`; it is monotone
-- by `SimpleFunc.monotone_eapprox`, and its pointwise supremum is `f` by
-- `SimpleFunc.iSup_coe_eapprox`.
/-- Theorem 1.96 (1): a measurable function `f : Ω → [0,∞]` is the pointwise supremum of an
increasing sequence of nonnegative simple functions. -/
theorem exists_monotone_simpleFunc_iSup_eq_of_measurable (hf : Measurable f) :
    ∃ fs : ℕ → SimpleFunc Ω ℝ≥0∞, Monotone fs ∧ (⨆ n, ⇑(fs n)) = f := by
  -- Use the canonical monotone approximation of an `ℝ≥0∞`-valued measurable function.
  refine ⟨SimpleFunc.eapprox f, SimpleFunc.monotone_eapprox f, ?_⟩
  -- Mathlib identifies the pointwise supremum of these approximants with `f`.
  exact SimpleFunc.iSup_coe_eapprox hf

/-- Helper for Theorem 1.96: a nonnegative simple function is the finite sum of its values times
the indicators of the corresponding singleton fibers. -/
lemma simpleFunc_coe_eq_sum_indicator_preimage_singleton (s : SimpleFunc Ω NNReal) :
    (fun ω ↦ (s ω : ℝ≥0∞)) =
      fun ω ↦ ∑ r ∈ s.range, ((s ⁻¹' ({r} : Set NNReal)).indicator (fun _ ↦ (r : ℝ≥0∞)) ω) := by
  classical
  -- At each point, exactly the fiber corresponding to the value `s ω` contributes.
  funext ω
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  rw [Finset.sum_eq_single_of_mem (s ω) (s.mem_range_self ω)]
  · simp
  · intro b hb hbs
    by_cases h : s ω = b
    · exact False.elim (hbs h.symm)
    · simp [h]

/-- Helper for Theorem 1.96: the simple increments `SimpleFunc.eapproxDiff f n` yield a
sigma-indexed indicator expansion of `f`. -/
lemma tsum_indicator_sigma_of_eapproxDiff (hf : Measurable f) :
    f = fun ω ↦
      ∑' i : Σ n, {r // r ∈ (SimpleFunc.eapproxDiff f n).range},
        (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
          (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω) := by
  -- Rewrite the increment series as a sigma-sum, then expand each simple increment by its range.
  funext ω
  calc
    f ω = ∑' n, ((SimpleFunc.eapproxDiff f n ω : NNReal) : ℝ≥0∞) := by
      symm
      exact SimpleFunc.tsum_eapproxDiff f hf ω
    _ = ∑' n, ∑ r ∈ (SimpleFunc.eapproxDiff f n).range,
          (((SimpleFunc.eapproxDiff f n) ⁻¹' ({r} : Set NNReal)).indicator
            (fun _ ↦ (r : ℝ≥0∞)) ω) := by
      refine tsum_congr fun n => ?_
      -- Decompose the `n`-th simple increment into its singleton fibers.
      simpa using congrArg (fun g : Ω → ℝ≥0∞ => g ω)
        (simpleFunc_coe_eq_sum_indicator_preimage_singleton (s := SimpleFunc.eapproxDiff f n))
    _ = ∑' n, ∑' r : {r // r ∈ (SimpleFunc.eapproxDiff f n).range},
          (((SimpleFunc.eapproxDiff f n) ⁻¹' ({r.1} : Set NNReal)).indicator
            (fun _ ↦ (r.1 : ℝ≥0∞)) ω) := by
      refine tsum_congr fun n => ?_
      -- Convert the finite range sum into a `tsum` over the finite subtype.
      exact (Finset.tsum_subtype ((SimpleFunc.eapproxDiff f n).range)
        (fun r : NNReal ↦
          (((SimpleFunc.eapproxDiff f n) ⁻¹' ({r} : Set NNReal)).indicator
            (fun _ ↦ (r : ℝ≥0∞)) ω))).symm
    _ = ∑' i : Σ n, {r // r ∈ (SimpleFunc.eapproxDiff f n).range},
          (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
            (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω) := by
      -- Collapse the iterated series into a single sigma-indexed series.
      symm
      simpa using
        (ENNReal.tsum_sigma' (fun i : Σ n, {r // r ∈ (SimpleFunc.eapproxDiff f n).range} ↦
          (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
            (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω)))

/-- Helper for Theorem 1.96: reindex the sigma-indexed indicator family coming from
`SimpleFunc.eapproxDiff` by `ℕ` using `Encodable.encode`. -/
lemma reindex_sigma_indicator_family_to_nat :
    ∃ (A : ℕ → Set Ω) (α : ℕ → ℝ≥0∞), (∀ n, MeasurableSet (A n)) ∧
      (fun ω ↦
        ∑' i : Σ n, {r // r ∈ (SimpleFunc.eapproxDiff f n).range},
          (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
            (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω))
        = fun ω ↦ ∑' n, (A n).indicator (fun _ ↦ α n) ω := by
  classical
  let ι := Σ n : ℕ, {r : NNReal // r ∈ (SimpleFunc.eapproxDiff f n).range}
  letI : ∀ n, Fintype {r : NNReal // r ∈ (SimpleFunc.eapproxDiff f n).range} :=
    fun n => Finset.fintypeCoeSort (SimpleFunc.eapproxDiff f n).range
  letI : ∀ n, Encodable {r : NNReal // r ∈ (SimpleFunc.eapproxDiff f n).range} :=
    fun n => Fintype.toEncodable _
  let e : ι ≃ Set.range (Encodable.encode : ι → ℕ) := Encodable.equivRangeEncode ι
  let A : ℕ → Set Ω := fun m =>
    match Encodable.decode₂ ι m with
    | some i =>
        ((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal))
    | none => ∅
  let α : ℕ → ℝ≥0∞ := fun m =>
    match Encodable.decode₂ ι m with
    | some i => (i.2.1 : ℝ≥0∞)
    | none => 0
  refine ⟨A, α, ?_, ?_⟩
  · intro m
    cases h : Encodable.decode₂ ι m with
    | none =>
        simp [A, h]
    | some i =>
        -- Each nonzero term is again a singleton fiber of an approximation increment.
        simpa [A, h] using
          (SimpleFunc.eapproxDiff f i.1).measurableSet_preimage ({i.2.1} : Set NNReal)
  · funext ω
    let termNat : ℕ → ℝ≥0∞ := fun m => (A m).indicator (fun _ ↦ α m) ω
    have hterm :
        Set.indicator (Set.range (Encodable.encode : ι → ℕ)) termNat = termNat := by
      funext m
      by_cases hm : m ∈ Set.range (Encodable.encode : ι → ℕ)
      · simp [Set.indicator_of_mem, hm]
      · have hnone : Encodable.decode₂ ι m = none := by
          by_contra hne
          exact hm ((Encodable.decode₂_ne_none_iff).1 hne)
        simp [Set.indicator_of_notMem, hm, termNat, A, α, hnone]
    have hsub :
        (∑' m : Set.range (Encodable.encode : ι → ℕ), termNat m.1) = ∑' m, termNat m := by
      -- Off the encoded range, the reindexed term is definitionally zero.
      calc
        (∑' m : Set.range (Encodable.encode : ι → ℕ), termNat m.1) =
            ∑' m, Set.indicator (Set.range (Encodable.encode : ι → ℕ)) termNat m := by
          simpa using (tsum_subtype (s := Set.range (Encodable.encode : ι → ℕ)) termNat)
        _ = ∑' m, termNat m := by rw [hterm]
    have hdecode :
        ∀ m : Set.range (Encodable.encode : ι → ℕ), Encodable.decode₂ ι m.1 = some (e.symm m) := by
      intro m
      have hencode : Encodable.encode (e.symm m) = m.1 := by
        exact congrArg Subtype.val (e.apply_symm_apply m)
      simpa [hencode] using (Encodable.encodek₂ (e.symm m))
    have hterm_sub :
        (fun m : Set.range (Encodable.encode : ι → ℕ) => termNat m.1) =
          fun m : Set.range (Encodable.encode : ι → ℕ) =>
            (((SimpleFunc.eapproxDiff f (e.symm m).1) ⁻¹' ({(e.symm m).2.1} : Set NNReal)).indicator
              (fun _ ↦ ((e.symm m).2.1 : ℝ≥0∞)) ω) := by
      funext m
      simp [termNat, A, α, hdecode m]
    have heq :
        (∑' m : Set.range (Encodable.encode : ι → ℕ), termNat m.1) =
          ∑' i : ι,
            (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
              (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω) := by
      -- The encoded range is equivalent to the original sigma index set.
      rw [hterm_sub]
      simpa using
        (Equiv.tsum_eq e.symm
          (fun i : ι ↦
            (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
              (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω)))
    calc
      (∑' i : ι,
          (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
            (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω)) =
          ∑' m : Set.range (Encodable.encode : ι → ℕ), termNat m.1 := by
        exact heq.symm
      _ = ∑' m, termNat m := hsub

-- Proof sketch: start from the monotone approximation by `SimpleFunc.eapprox`, write the
-- successive differences `SimpleFunc.eapproxDiff f n` as finite sums of constants times
-- indicators of measurable sets, and reindex the resulting countable family.
/-- Theorem 1.96 (2): a measurable function `f : Ω → [0,∞]` can be written as a countable sum of
nonnegative constants times indicators of measurable sets. -/
theorem exists_indicator_tsum_eq_of_measurable (hf : Measurable f) :
    ∃ (A : ℕ → Set Ω) (α : ℕ → ℝ≥0∞), (∀ n, MeasurableSet (A n)) ∧
      f = fun ω ↦ ∑' n, (A n).indicator (fun _ ↦ α n) ω := by
  rcases reindex_sigma_indicator_family_to_nat (f := f) with ⟨A, α, hA, hreindex⟩
  refine ⟨A, α, hA, ?_⟩
  -- First identify `f` with the sigma-indexed indicator expansion, then reindex by `ℕ`.
  calc
    f = fun ω ↦
      ∑' i : Σ n, {r // r ∈ (SimpleFunc.eapproxDiff f n).range},
        (((SimpleFunc.eapproxDiff f i.1) ⁻¹' ({i.2.1} : Set NNReal)).indicator
          (fun _ ↦ (i.2.1 : ℝ≥0∞)) ω) := tsum_indicator_sigma_of_eapproxDiff (f := f) hf
    _ = fun ω ↦ ∑' n, (A n).indicator (fun _ ↦ α n) ω := hreindex
