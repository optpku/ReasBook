/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_2_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InformationTheory MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

section EmpiricalCounts

variable {S : Type u} [DecidableEq S]

/-- The number of coordinates of a word `x : Fin n → S` equal to the symbol `a`. -/
def empiricalCount (n : ℕ) (x : Fin n → S) (a : S) : ℕ :=
  Fintype.card {i // x i = a}

/-- Helper for Lemma 23.12: on a finite alphabet, the empirical counts sum to the word length. -/
theorem sum_empiricalCount [Fintype S] (n : ℕ) (x : Fin n → S) :
    ∑ a, empiricalCount n x a = n := by
  let f : Fin n → S := x
  have hMapsTo :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).MapsTo f (Finset.univ : Finset S) :=
    fun _ _ ↦ Finset.mem_univ _
  -- Proof comment: partition the coordinates by their image under `x`.
  calc
    ∑ a, empiricalCount n x a = ∑ a, (Finset.univ.filter fun i : Fin n ↦ x i = a).card := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa [empiricalCount] using
        (Fintype.card_of_subtype (Finset.univ.filter fun i : Fin n ↦ x i = a)
          (fun i ↦ by simp))
    _ = n := by
      simpa [f] using (Finset.card_eq_sum_card_fiberwise hMapsTo).symm

end EmpiricalCounts

section EmpiricalSets

variable {S : Type u} [MeasurableSpace S]

-- Internal bridge from the source-facing `ℕ` indexing of Chapter 23 to the Chapter 12 owner
-- `empiricalDistributionTuple`, which is indexed by `ℕ+`.
private noncomputable abbrev empiricalWordDistribution {n : ℕ} (hn : n ≠ 0) (x : Fin n → S) :
    ProbabilityMeasure S :=
  let x' : Fin (Nat.toPNat n (Nat.pos_of_ne_zero hn)) → S := x
  empiricalDistributionTuple x'

/-- The event that a word of length `n` has empirical distribution `ν`. For `n = 0` this event is
empty, so the associated set of empirical distributions is empty as well. This is the
`source-facing` event attached to the Chapter 12 owner `empiricalDistributionTuple` on a
singleton-measurable alphabet. -/
def empiricalDistributionEvent [MeasurableSingletonClass S]
    (n : ℕ) (ν : ProbabilityMeasure S) : Set (Fin n → S) :=
  if hn : n = 0 then ∅ else
    fun x ↦ empiricalWordDistribution hn x = ν

/-- Helper for Lemma 23.12: the deterministic empirical law of a word gives each singleton the
normalized coordinate count of that symbol. -/
theorem empiricalWordDistribution_apply_singleton [DecidableEq S] [MeasurableSingletonClass S]
    {n : ℕ} (hn : n ≠ 0) (x : Fin n → S) (a : S) :
    (empiricalWordDistribution hn x : Measure S) {a} =
      ((empiricalCount n x a : ℕ) : ENNReal) / (n : ENNReal) := by
  have hCount :
      (∑ i : Fin n, (Measure.dirac (x i)) {a}) = empiricalCount n x a := by
    -- Proof comment: the singleton mass of each Dirac term is the indicator of the equality
    -- `x i = a`, so the total sum is the cardinality of the matching fiber.
    simpa [Pi.single_apply, empiricalCount, Fintype.card_subtype] using
      (Finset.sum_boole (s := Finset.univ) (p := fun i : Fin n ↦ x i = a))
  have hMeasure :
      (empiricalWordDistribution hn x : Measure S) =
        (n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (x i) := by
    -- Proof comment: specialize the owner formula for deterministic tuples to the current word.
    simpa [empiricalWordDistribution, empiricalDistributionTuple] using
      empiricalDistribution_toMeasure (Nat.toPNat n (Nat.pos_of_ne_zero hn))
        (fun i (_ : Unit) ↦ x i) ()
  rw [hMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  -- Proof comment: evaluating the finite sum of Dirac masses on `{a}` counts the matching
  -- coordinates exactly once.
  rw [hCount]
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm]

-- Proof sketch: unfold `empiricalDistributionEvent`.
-- For `n ≠ 0`, membership is exactly the pointwise equality between `ν` and the normalized
-- coordinate counts, while for `n = 0` the event is empty.
/-- Membership in `empiricalDistributionEvent n ν` is the pointwise normalized-count condition when
`n ≠ 0`. -/
theorem mem_empiricalDistributionEvent_iff [DecidableEq S] [MeasurableSingletonClass S] [Countable S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S} :
    x ∈ empiricalDistributionEvent n ν ↔
      n ≠ 0 ∧
        ∀ a : S, (ν : Measure S) {a} = ((empiricalCount n x a : ℕ) : ENNReal) / (n : ENNReal) := by
  classical
  by_cases hn : n = 0
  · simp [empiricalDistributionEvent, hn]
  · constructor
    · intro hx
      have hx' : empiricalWordDistribution hn x = ν := by
        simpa [empiricalDistributionEvent, hn] using hx
      refine ⟨hn, ?_⟩
      intro a
      -- Proof comment: compare the empirical law and `ν` on the singleton `{a}`.
      simpa [hx'] using empiricalWordDistribution_apply_singleton hn x a
    · rintro ⟨hn0, hCount⟩
      have hPmf :
          ((ν : Measure S).toPMF) = ((empiricalWordDistribution hn0 x : Measure S).toPMF) := by
        ext a
        rw [Measure.toPMF_apply, Measure.toPMF_apply, hCount a]
        exact (empiricalWordDistribution_apply_singleton hn0 x a).symm
      have hMeasure : (ν : Measure S) = (empiricalWordDistribution hn0 x : Measure S) := by
        -- Proof comment: on a singleton-measurable space, a probability measure is recovered from
        -- its point masses via `toPMF`.
        simpa [Measure.toPMF_toMeasure] using congrArg PMF.toMeasure hPmf
      have hx' : empiricalWordDistribution hn0 x = ν :=
        ProbabilityMeasure.toMeasure_injective hMeasure.symm
      simpa [empiricalDistributionEvent, hn0] using hx'

/-- The set `E_n` of empirical distributions realized by words of length `n`. -/
def empiricalDistributions [MeasurableSingletonClass S] (n : ℕ) : Set (ProbabilityMeasure S) :=
  fun ν ↦ ∃ x : Fin n → S, x ∈ empiricalDistributionEvent n ν

-- Proof sketch: unfold `empiricalDistributions`; this is exactly the existential realization of
-- the empirical-distribution event by some word of length `n`.
/-- A probability measure belongs to `empiricalDistributions n` exactly when it is realized
by some word of length `n`. -/
theorem mem_empiricalDistributions_iff [MeasurableSingletonClass S]
    (n : ℕ) (ν : ProbabilityMeasure S) :
    ν ∈ empiricalDistributions n ↔ ∃ x : Fin n → S, x ∈ empiricalDistributionEvent n ν := Iff.rfl

end EmpiricalSets

section FiniteAlphabet

/-- The combinatorial lower prefactor `(n + 1)^{-#S}`. -/
def empiricalLowerPrefactor (S : Type u) [Fintype S] (n : ℕ) : ENNReal :=
  ((n + 1 : ℕ) : ENNReal)⁻¹ ^ Fintype.card S

-- Proof sketch: unfold `empiricalLowerPrefactor` as the canonical power `((n + 1)⁻¹)^(#S)` and
-- rewrite that power as the product of `Fintype.card S` copies of `(n + 1)⁻¹`.
/-- Expanding `empiricalLowerPrefactor S n` gives the finite product form of `(n + 1)^{-#S}`. -/
theorem empiricalLowerPrefactor_def (S : Type u) [Fintype S] (n : ℕ) :
    empiricalLowerPrefactor S n =
      Finset.univ.prod fun _ : Fin (Fintype.card S) ↦ ((n + 1 : ℕ) : ENNReal)⁻¹ := by
  rw [empiricalLowerPrefactor]
  exact (Fin.prod_const (Fintype.card S) (((n + 1 : ℕ) : ENNReal)⁻¹)).symm

end FiniteAlphabet

section MeasureLayer

variable {S : Type u} [MeasurableSpace S]

/-- Helper for Lemma 23.12: after encoding a finite alphabet by `Fin (Fintype.card S)`, the
imported multinomial count is exactly the empirical count of the decoded symbol. -/
theorem multinomialCount_encoded_eq_empiricalCount [Fintype S] [DecidableEq S]
    (n : ℕ) (y : Fin n → S) (i : Fin (Fintype.card S)) :
    multinomialCount (fun j (ω : Fin n → S) ↦ Fintype.equivFin S (ω j)) y i =
      empiricalCount n y ((Fintype.equivFin S).symm i) := by
  calc
    multinomialCount (fun j (ω : Fin n → S) ↦ Fintype.equivFin S (ω j)) y i
      = (Finset.univ.filter fun j : Fin n ↦ y j = (Fintype.equivFin S).symm i).card := by
          unfold multinomialCount
          congr
          ext j
          constructor
          · intro hj
            exact (Fintype.equivFin S).injective (by simpa using hj)
          · intro hj
            simpa [hj]
    _ = empiricalCount n y ((Fintype.equivFin S).symm i) := by
      simpa [empiricalCount] using
        (Fintype.card_of_subtype
          (Finset.univ.filter fun j : Fin n ↦ y j = (Fintype.equivFin S).symm i)
          (fun j ↦ by simp)).symm

/-- The probability that an i.i.d. word with letter law `μ` has empirical distribution `ν`. -/
def empiricalDistributionProbability [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ)
    (ν : ProbabilityMeasure S) : ENNReal :=
  ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) : Measure (Fin n → S))
    (empiricalDistributionEvent n ν)

-- Proof sketch: unfold `empiricalDistributionProbability`; it is the measure of the empirical-law
-- event under the product law `ProbabilityMeasure.pi (fun _ : Fin n ↦ μ)`.
/-- Expanding `empiricalDistributionProbability μ n ν` gives the product-law mass of the event that
the empirical distribution equals `ν`. -/
theorem empiricalDistributionProbability_def
    [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ) (ν : ProbabilityMeasure S) :
    empiricalDistributionProbability μ n ν =
      ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
        Measure (Fin n → S)) (empiricalDistributionEvent n ν) := rfl

/-- Helper for Lemma 23.12: once one realizing word is fixed, the empirical-law event is exactly
the histogram level set determined by that word. -/
theorem empiricalDistributionEvent_eq_countLevelSet
    [DecidableEq S] [MeasurableSingletonClass S] [Countable S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν) :
    empiricalDistributionEvent n ν = {y : Fin n → S | empiricalCount n y = empiricalCount n x} := by
  ext y
  constructor
  · intro hy
    obtain ⟨hn, hyCount⟩ := mem_empiricalDistributionEvent_iff.mp hy
    obtain ⟨_, hxCount⟩ := mem_empiricalDistributionEvent_iff.mp hx
    ext a
    have hDiv :
        (((empiricalCount n y a : ℕ) : ENNReal) / (n : ENNReal)) =
          (((empiricalCount n x a : ℕ) : ENNReal) / (n : ENNReal)) := by
      rw [← hyCount a, ← hxCount a]
    have hnENN : (n : ENNReal) ≠ 0 := by
      exact_mod_cast hn
    have hMul := congrArg (fun t : ENNReal ↦ (n : ENNReal) * t) hDiv
    have hEqENN :
        (((empiricalCount n y a : ℕ) : ENNReal)) =
          (((empiricalCount n x a : ℕ) : ENNReal)) := by
      simpa [ENNReal.mul_div_cancel hnENN (ENNReal.natCast_ne_top n)] using hMul
    exact_mod_cast hEqENN
  · intro hy
    change empiricalCount n y = empiricalCount n x at hy
    obtain ⟨hn, hxCount⟩ := mem_empiricalDistributionEvent_iff.mp hx
    refine mem_empiricalDistributionEvent_iff.mpr ?_
    refine ⟨hn, ?_⟩
    intro a
    rw [hxCount a, congrArg (fun k : S → ℕ ↦ k a) hy]

/-- Helper for Lemma 23.12: after encoding the finite alphabet by `Fin (Fintype.card S)`, the
empirical-distribution event becomes the singleton level set of the encoded multinomial count. -/
theorem empiricalDistributionEvent_eq_encodedMultinomialSingleton
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν) :
    empiricalDistributionEvent n ν =
      {y : Fin n → S |
        multinomialCount (fun j (ω : Fin n → S) ↦ Fintype.equivFin S (ω j)) y =
          fun i : Fin (Fintype.card S) ↦ empiricalCount n x ((Fintype.equivFin S).symm i)} := by
  -- Route correction: separate the empirical-event transport from the product-law transport, so
  -- the exact multinomial theorem can read the encoded singleton event directly.
  rw [empiricalDistributionEvent_eq_countLevelSet hx]
  ext y
  constructor
  · intro hy
    -- Proof comment: the encoded histogram records exactly the empirical counts of the decoded
    -- symbols, so equal count functions give the encoded singleton identity coordinatewise.
    ext i
    have hcoord :=
      congrArg (fun k : S → ℕ ↦ k ((Fintype.equivFin S).symm i)) hy
    simpa [multinomialCount_encoded_eq_empiricalCount] using hcoord
  · intro hy
    -- Proof comment: decode each encoded coordinate at `Fintype.equivFin S a` to recover the
    -- original empirical counts on the alphabet `S`.
    ext a
    have hcoord :=
      congrArg (fun k : Fin (Fintype.card S) → ℕ ↦ k (Fintype.equivFin S a)) hy
    simpa [multinomialCount_encoded_eq_empiricalCount] using hcoord

/-- Helper for Lemma 23.12: the encoded coordinate maps under the product law are independent and
each has the pushed-forward one-letter law. -/
theorem encodedCoordinateHasLaw
    [Fintype S] [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ) :
    iIndepFun
        (fun j (ω : Fin n → S) ↦ Fintype.equivFin S (ω j))
        ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
          Measure (Fin n → S)) ∧
      ∀ j : Fin n,
        HasLaw
          (fun ω : Fin n → S ↦ Fintype.equivFin S (ω j))
          ((((μ : Measure S).toPMF).map (Fintype.equivFin S)).toMeasure)
          ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
            Measure (Fin n → S)) := by
  classical
  let P : Measure (Fin n → S) :=
    ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
      Measure (Fin n → S))
  let e : S → Fin (Fintype.card S) := Fintype.equivFin S
  have he_meas : Measurable e := measurable_of_finite e
  constructor
  · -- Proof comment: the product coordinates are independent, and composing every coordinate with
    -- the fixed encoding map preserves that finite-product independence.
    simpa [P, e] using
      (iIndepFun_pi
        (μ := fun _ : Fin n ↦ (μ : Measure S))
        (X := fun _ : Fin n ↦ e)
        (fun _ ↦ he_meas.aemeasurable))
  · intro j
    have hEval : HasLaw (Function.eval j) (μ : Measure S) P := by
      -- Proof comment: under the product law, every coordinate evaluation has the original
      -- one-letter law `μ`.
      simpa [P] using
        (MeasurePreserving.hasLaw
          (measurePreserving_eval (μ := fun _ : Fin n ↦ (μ : Measure S)) j))
    have hEncode :
        HasLaw e ((((μ : Measure S).toPMF).map e).toMeasure) (μ : Measure S) := by
      -- Proof comment: pushing `μ` forward along the encoding map is exactly the mapped PMF
      -- converted back to a measure.
      refine ⟨he_meas.aemeasurable, ?_⟩
      calc
        (μ : Measure S).map e = ((((μ : Measure S).toPMF).toMeasure).map e) := by
          rw [Measure.toPMF_toMeasure]
        _ = ((((μ : Measure S).toPMF).map e).toMeasure) := by
          simpa using (PMF.toMeasure_map (p := ((μ : Measure S).toPMF)) (f := e) he_meas)
    simpa [P, e, Function.comp] using (HasLaw.comp hEncode hEval)

/-- Helper for Lemma 23.12: once a realizing word `x` is fixed, the empirical-distribution event
has the exact multinomial mass of the encoded histogram of `x`. -/
theorem empiricalDistributionProbability_eq_multinomialMass
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {μ ν : ProbabilityMeasure S} {n : ℕ} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν) :
    empiricalDistributionProbability μ n ν =
      (Nat.multinomial Finset.univ
        (fun i : Fin (Fintype.card S) ↦
          empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
        ∏ i : Fin (Fintype.card S),
          ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) i) ^
            empiricalCount n x ((Fintype.equivFin S).symm i) := by
  classical
  let P : Measure (Fin n → S) :=
    ((ProbabilityMeasure.pi fun _ : Fin n ↦ μ : ProbabilityMeasure (Fin n → S)) :
      Measure (Fin n → S))
  let e : S → Fin (Fintype.card S) := Fintype.equivFin S
  let X : Fin n → (Fin n → S) → Fin (Fintype.card S) := fun j ω ↦ e (ω j)
  let k : Fin (Fintype.card S) → ℕ := fun i ↦ empiricalCount n x ((Fintype.equivFin S).symm i)
  have hk : ∑ i, k i = n := by
    -- Proof comment: the encoded histogram is just a reindexing of the empirical counts of `x`.
    have hReindex :
        (∑ a : S, empiricalCount n x a) =
          ∑ i : Fin (Fintype.card S), empiricalCount n x ((Fintype.equivFin S).symm i) := by
      refine Fintype.sum_equiv (Fintype.equivFin S)
        (fun a : S ↦ empiricalCount n x a)
        (fun i : Fin (Fintype.card S) ↦ empiricalCount n x ((Fintype.equivFin S).symm i)) ?_
      intro a
      simp
    calc
      ∑ i, k i = ∑ a : S, empiricalCount n x a := by
        simpa [k] using hReindex.symm
      _ = n := sum_empiricalCount n x
  obtain ⟨hIndep, hLaw⟩ := encodedCoordinateHasLaw (μ := μ) (n := n)
  -- Proof comment: rewrite the empirical-distribution event as the encoded singleton count event
  -- and apply the imported multinomial point-mass theorem to the encoded coordinates.
  rw [empiricalDistributionProbability_def,
    empiricalDistributionEvent_eq_encodedMultinomialSingleton (x := x) hx]
  simpa [P, X, e, k] using
    (multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
      ((((μ : Measure S).toPMF).map e)) X hIndep hLaw k hk)

/-- Helper for Lemma 23.12: under a realizing word `x`, the encoded singleton mass of `ν`
coincides with the normalized empirical count of the decoded symbol. -/
theorem encodedHistogramMass_eq_countRatio
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν)
    (i : Fin (Fintype.card S)) :
    ((((ν : Measure S).toPMF).map (Fintype.equivFin S)) i) =
      ((empiricalCount n x ((Fintype.equivFin S).symm i) : ℕ) : ENNReal) / (n : ENNReal) := by
  let e : S → Fin (Fintype.card S) := Fintype.equivFin S
  obtain ⟨_, hCount⟩ := mem_empiricalDistributionEvent_iff.mp hx
  -- Proof comment: decode the encoded singleton by `Fintype.equivFin` and then use the empirical
  -- singleton-mass formula already recorded in `mem_empiricalDistributionEvent_iff`.
  calc
    ((((ν : Measure S).toPMF).map e) i)
        = ∑ a : S, if i = e a then ((ν : Measure S).toPMF) a else 0 := by
            rw [PMF.map_apply, tsum_fintype]
            exact Finset.sum_congr rfl (fun a _ ↦ by simp)
    _ = ((ν : Measure S).toPMF) ((Fintype.equivFin S).symm i) := by
          rw [Finset.sum_eq_single ((Fintype.equivFin S).symm i)]
          · simp [e]
          · intro a ha hne
            have hei : e a ≠ i := by
              intro hei
              apply hne
              exact (Fintype.equivFin S).injective (by simpa [e] using hei)
            by_cases hEq : i = e a
            · exact False.elim (hei hEq.symm)
            · simp [hEq]
          · intro hmem
            simp at hmem
    _ = (ν : Measure S) {(Fintype.equivFin S).symm i} := by
          rw [Measure.toPMF_apply]
    _ = ((empiricalCount n x ((Fintype.equivFin S).symm i) : ℕ) : ENNReal) / (n : ENNReal) :=
          hCount _

/-- Helper for Lemma 23.12: encoding a finite alphabet by `Fintype.equivFin` preserves the
singleton mass of a probability measure. -/
theorem toPMF_map_equivFin_apply
    [Fintype S] [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (a : S) :
    ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) (Fintype.equivFin S a)) =
      (μ : Measure S) {a} := by
  classical
  -- Proof comment: the encoded atom `Fintype.equivFin S a` has the unique preimage `a`.
  calc
    ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) (Fintype.equivFin S a))
        = ∑ b : S,
            if Fintype.equivFin S a = Fintype.equivFin S b then ((μ : Measure S).toPMF) b else 0 := by
            rw [PMF.map_apply, tsum_fintype]
            exact Finset.sum_congr rfl (fun b _ ↦ by simp)
    _ = ((μ : Measure S).toPMF) a := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hba
            have hne : Fintype.equivFin S a ≠ Fintype.equivFin S b := by
              intro hEq
              exact hba ((Fintype.equivFin S).injective hEq.symm)
            simp [hne]
          · intro ha
            simp at ha
    _ = (μ : Measure S) {a} := by
          rw [Measure.toPMF_apply]

/-- Helper for Lemma 23.12: on a finite singleton-measurable alphabet, failure of
`(ν : Measure S) ≪ (μ : Measure S)` is witnessed by a singleton with zero `μ`-mass and nonzero
`ν`-mass. -/
theorem exists_singleton_mass_witness_of_not_absolutelyContinuous
    [Fintype S] [MeasurableSingletonClass S]
    (μ ν : ProbabilityMeasure S) (h_not_ac : ¬ (ν : Measure S) ≪ (μ : Measure S)) :
    ∃ a : S, (μ : Measure S) {a} = 0 ∧ (ν : Measure S) {a} ≠ 0 := by
  classical
  by_contra hNoWitness
  have hSingleton :
      ∀ a : S, (μ : Measure S) {a} = 0 → (ν : Measure S) {a} = 0 := by
    intro a hμa
    by_contra hνa
    exact hNoWitness ⟨a, hμa, hνa⟩
  have h_ac : (ν : Measure S) ≪ (μ : Measure S) := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hμs
    rw [← Measure.tsum_indicator_apply_singleton (μ := (ν : Measure S)) s hs]
    rw [ENNReal.tsum_eq_zero]
    intro a
    by_cases ha : a ∈ s
    · have hμsingle : (μ : Measure S) {a} = 0 := by
        apply le_antisymm
        · exact le_trans (measure_mono (Set.singleton_subset_iff.mpr ha)) (by simpa [hμs])
        · exact bot_le
      simp [Set.indicator_of_mem ha, hSingleton a hμsingle]
    · simp [Set.indicator_of_notMem ha]
  exact h_not_ac h_ac

/-- Helper for Lemma 23.12: if `ν` is not absolutely continuous with respect to `μ`, then every
word realizing `ν` has zero product-law mass under `μ`. -/
theorem empiricalDistributionProbability_eq_zero_of_not_absolutelyContinuous
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {μ ν : ProbabilityMeasure S} {n : ℕ} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν)
    (h_not_ac : ¬ (ν : Measure S) ≪ (μ : Measure S)) :
    empiricalDistributionProbability μ n ν = 0 := by
  classical
  obtain ⟨a, hμa, hνa⟩ :=
    exists_singleton_mass_witness_of_not_absolutelyContinuous μ ν h_not_ac
  obtain ⟨hn, hCount⟩ := mem_empiricalDistributionEvent_iff.mp hx
  have hCountNeZero : empiricalCount n x a ≠ 0 := by
    intro hZero
    have hZeroRatio :
        ((empiricalCount n x a : ℕ) : ENNReal) / (n : ENNReal) = 0 := by
      simp [hZero]
    have hνzero : (ν : Measure S) {a} = 0 := (hCount a).trans hZeroRatio
    exact hνa hνzero
  have hEncodedZero :
      ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) (Fintype.equivFin S a)) = 0 := by
    simpa [hμa] using toPMF_map_equivFin_apply (μ := μ) a
  have hProdZero :
      (∏ i : Fin (Fintype.card S),
          ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) i) ^
            empiricalCount n x ((Fintype.equivFin S).symm i)) = 0 := by
    refine Finset.prod_eq_zero_iff.mpr ?_
    refine ⟨Fintype.equivFin S a, Finset.mem_univ _, ?_⟩
    simpa [hEncodedZero, hCountNeZero]
  calc
    empiricalDistributionProbability μ n ν
      = (Nat.multinomial Finset.univ
          (fun i : Fin (Fintype.card S) ↦
            empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
          ∏ i : Fin (Fintype.card S),
            ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) i) ^
              empiricalCount n x ((Fintype.equivFin S).symm i) := by
          rw [empiricalDistributionProbability_eq_multinomialMass (μ := μ) hx]
    _ = 0 := by
          rw [hProdZero]
          simp

/-- Helper for Lemma 23.12: the multinomial weights on all encoded histograms of total mass `n`
sum to `1`. -/
theorem multinomialHistogramMass_sum_eq_one
    {m n : ℕ} (p : PMF (Fin m)) :
    Finset.sum (Finset.piAntidiag Finset.univ n)
        (fun ℓ ↦ (Nat.multinomial Finset.univ ℓ : ENNReal) * ∏ i : Fin m, p i ^ ℓ i) = 1 := by
  have hp_sum : ∑ i : Fin m, p i = 1 := by
    simpa using ((tsum_fintype fun i : Fin m ↦ p i).symm.trans p.tsum_coe)
  -- Proof comment: expand `(∑ i, p i)^n` by the multinomial theorem and use that a PMF has total
  -- mass `1`.
  calc
    Finset.sum (Finset.piAntidiag Finset.univ n)
        (fun ℓ ↦ (Nat.multinomial Finset.univ ℓ : ENNReal) * ∏ i : Fin m, p i ^ ℓ i)
      = (∑ i : Fin m, p i) ^ n := by
          symm
          simpa using
            (Finset.sum_pow_eq_sum_piAntidiag
              (s := Finset.univ)
              (f := fun i : Fin m ↦ (p i : ENNReal))
              n)
    _ = 1 ^ n := by
          rw [hp_sum]
    _ = 1 := by
          simp

/-- Helper for Lemma 23.12: the encoded histograms with total count `n` are at most `(n + 1)^m`
in number. -/
theorem encodedHistogramFamily_card_le (m n : ℕ) :
    Nat.card {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} ≤ (n + 1) ^ m := by
  classical
  let f : {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} → (Fin m → Fin (n + 1)) := fun ℓ i ↦
    ⟨ℓ.1 i, by
      have hle : ℓ.1 i ≤ ∑ j : Fin m, ℓ.1 j := by
        simpa using (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (by simp : i ∈ Finset.univ))
      exact Nat.lt_succ_iff.mpr (hle.trans (by simpa [ℓ.2]))⟩
  have hf : Function.Injective f := by
    intro ℓ₁ ℓ₂ h
    apply Subtype.ext
    funext i
    simpa [f] using congrArg Fin.val (congrFun h i)
  have hfinite : Finite {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} := Finite.of_injective f hf
  letI : Fintype {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} := Fintype.ofFinite _
  -- Proof comment: each admissible histogram chooses one value in `Fin (n + 1)` for every
  -- encoded symbol, because every coordinate is bounded by the total count `n`.
  have hcard :
      Fintype.card {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} ≤ Fintype.card (Fin m → Fin (n + 1)) :=
    Fintype.card_le_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using hcard

/-- Helper for Lemma 23.12: if one atom of a finite PMF dominates all the others, then that atom
is at least the uniform average `1 / Fintype.card α`. -/
private theorem pmfValue_ge_inv_card_of_ge_all {α : Type*} [Fintype α]
    (p : PMF α) (a : α) (hmax : ∀ b : α, p b ≤ p a) :
    ((Fintype.card α : ℕ) : ENNReal)⁻¹ ≤ p a := by
  letI : Nonempty α := ⟨a⟩
  have hsum : ∑ b : α, p b = (1 : ENNReal) := by
    -- Proof comment: on a finite state space, the PMF sum is the finite sum of all atom masses.
    simpa using (p.tsum_coe : ∑' b : α, p b = 1)
  have hle : ∑ b : α, p b ≤ ∑ _b : α, p a := by
    -- Proof comment: replace each atom by the dominating value `p a`.
    exact Finset.sum_le_sum fun b _ ↦ hmax b
  have hmul : (1 : ENNReal) ≤ (Fintype.card α : ENNReal) * p a := by
    -- Proof comment: the dominating value controls the whole finite sum by `card α` copies of
    -- itself.
    rw [← hsum]
    simpa using hle
  have hcard_ne_zero : ((Fintype.card α : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact
    (ENNReal.inv_le_iff_le_mul (fun _ ↦ hcard_ne_zero) (by simp)).2 hmul

/-- Helper for Lemma 23.12: a dominant encoded histogram mass is bounded below by the prefactor
`(n + 1)^{-m}` coming from the number of possible encoded histograms. -/
private theorem encodedHistogramMass_ge_lowerPrefactor_of_ge_all {m n : ℕ}
    (p : PMF {ℓ : Fin m → ℕ // ∑ i, ℓ i = n})
    (k : {ℓ : Fin m → ℕ // ∑ i, ℓ i = n})
    (hmax : ∀ ℓ : {ℓ : Fin m → ℕ // ∑ i, ℓ i = n}, p ℓ ≤ p k) :
    empiricalLowerPrefactor (Fin m) n ≤ p k := by
  classical
  let f : {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} → (Fin m → Fin (n + 1)) := fun ℓ i ↦
    ⟨ℓ.1 i, by
      have hle : ℓ.1 i ≤ ∑ j : Fin m, ℓ.1 j := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (by simp : i ∈ Finset.univ))
      exact Nat.lt_succ_iff.mpr (hle.trans (by simpa [ℓ.2]))⟩
  have hf : Function.Injective f := by
    intro ℓ₁ ℓ₂ h
    apply Subtype.ext
    funext i
    simpa [f] using congrArg Fin.val (congrFun h i)
  letI : Finite {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} := Finite.of_injective f hf
  letI : Fintype {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} := Fintype.ofFinite _
  have havg :
      (((Fintype.card {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} : ℕ) : ENNReal)⁻¹) ≤ p k :=
    pmfValue_ge_inv_card_of_ge_all p k hmax
  have hcard :
      Fintype.card {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} ≤ (n + 1) ^ m := by
    -- Proof comment: compare the histogram PMF support size with the previously established
    -- cardinality bound on encoded count vectors.
    simpa [Nat.card_eq_fintype_card] using encodedHistogramFamily_card_le m n
  have hinv :
      (((n + 1) ^ m : ℕ) : ENNReal)⁻¹ ≤
        ((Fintype.card {ℓ : Fin m → ℕ // ∑ i, ℓ i = n} : ℕ) : ENNReal)⁻¹ := by
    exact ENNReal.inv_le_inv' (by exact_mod_cast hcard)
  -- Proof comment: a dominant atom is at least the reciprocal of the histogram family size, and
  -- that family size is at most `(n + 1)^m`.
  simpa [empiricalLowerPrefactor, ENNReal.inv_pow] using le_trans hinv havg

/-- Helper for Lemma 23.12: every coordinate of a sub-probability mass function is finite. -/
private theorem pmfCoordinate_ne_top_of_tsum_le_one {E : Type*} (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Proof comment: each coordinate is bounded by the total mass, hence by `1`.
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hq_le_one ENNReal.one_lt_top)

/-- Helper for Lemma 23.12: on the positive-support branch, the pointwise logarithmic gap splits
into the KL remainder plus the linear correction `p_e - q_e`. -/
private theorem crossEntropyGapTermIdentity {E : Type*} (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) =
      (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) +
        (p e).toReal - (q e).toReal := by
  by_cases hp : p e = 0
  · -- Proof comment: off the support of `p`, the identity collapses to the `klFun 0 = 1` case.
    simp [hp, klFun_zero]
  · -- Proof comment: on the support, positivity of both masses lets us rewrite through
    -- `log (p_e / q_e)`.
    have hq' : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
    have hq_top : q e ≠ ⊤ := pmfCoordinate_ne_top_of_tsum_le_one q hq e
    have hp_toReal : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hq_toReal : 0 < (q e).toReal := ENNReal.toReal_pos hq' hq_top
    rw [klFun_apply]
    rw [ENNReal.toReal_div, Real.log_div hp_toReal.ne' hq_toReal.ne']
    field_simp [hq_toReal.ne']
    ring

/-- Helper for Lemma 23.12: on a countable discrete space, `p.toMeasure` is the weighted counting
measure with density `p / q` over the comparison measure `Measure.count.withDensity q`. -/
private theorem pmfToMeasure_eq_withDensityComparison {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    p.toMeasure = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
  let ν : Measure E := Measure.count.withDensity q
  calc
    p.toMeasure = Measure.count.withDensity (fun e ↦ (p e : ENNReal)) := by
      -- Proof comment: rewrite `p.toMeasure` itself as a weighted counting measure.
      refine Measure.ext fun s hs ↦ ?_
      rw [p.toMeasure_apply hs, withDensity_apply _ hs]
      rw [← lintegral_indicator hs (fun e ↦ (p e : ENNReal)), lintegral_count]
    _ = (Measure.count.withDensity q).withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      -- Proof comment: compose the comparison density `q` with the explicit Radon-Nikodym factor
      -- `p / q`.
      rw [← withDensity_mul (Measure.count : Measure E)]
      · refine withDensity_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro e
        by_cases hp : p e = 0
        · simp [hp]
        · have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
          have hq_top : q e ≠ ⊤ := pmfCoordinate_ne_top_of_tsum_le_one q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hq_top, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · exact measurable_of_finite q
      · exact measurable_of_finite (fun e ↦ (p e : ENNReal) / q e)
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Lemma 23.12: the discrete KL divergence against a comparison mass function equals
the finite sum of the pointwise KL remainders. -/
private theorem discreteKlDiv_eq_gapSeries {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E] [Fintype E]
    (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    let ν : Measure E := Measure.count.withDensity q
    klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- Proof comment: the comparison measure is finite because its total mass is at most `1`.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  have hpν : p.toMeasure ≪ ν := by
    rw [pmfToMeasure_eq_withDensityComparison p q hq hnozero]
    exact withDensity_absolutelyContinuous _ _
  change klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal))
  rw [klDiv_eq_lintegral_klFun_of_ac hpν]
  have hrn : p.toMeasure.rnDeriv ν =ᵐ[ν] fun e ↦ (p e : ENNReal) / q e := by
    rw [pmfToMeasure_eq_withDensityComparison p q hq hnozero]
    exact Measure.rnDeriv_withDensity ν (measurable_of_finite _)
  have hfun :
      (fun x ↦ ENNReal.ofReal (klFun (p.toMeasure.rnDeriv ν x).toReal)) =ᵐ[ν]
        fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
    -- Proof comment: replace the Radon-Nikodym derivative by the explicit density `p / q`.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hq_top : q e ≠ ⊤ := pmfCoordinate_ne_top_of_tsum_le_one q hq e
    have hq_toReal_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) =
          ENNReal.ofReal (q e).toReal *
            ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [ENNReal.ofReal_toReal hq_top]
      _ = ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [← ENNReal.ofReal_mul hq_toReal_nonneg]
  · fun_prop
  · fun_prop

/-- Helper for Lemma 23.12: splitting a multinomial coefficient along the first coordinate of
`Fin (m + 1)` produces the expected binomial head factor and the tail multinomial coefficient. -/
private theorem multinomialFinSuccSplit (m n r : ℕ) (k : Fin m → ℕ)
    (hk : r + ∑ i : Fin m, k i = n) :
    Nat.multinomial Finset.univ (Fin.cons r k) = n.choose r * Nat.multinomial Finset.univ k := by
  let k' : Fin (m + 1) → ℕ := Fin.cons r k
  let p : ℕ := ∏ i : Fin m, Nat.factorial (k i)
  have hp_pos : 0 < Nat.factorial r * p := by
    -- Proof comment: factorials are positive, so we can cancel the common denominator after
    -- rewriting both multinomial coefficients via `Nat.multinomial_spec`.
    refine Nat.mul_pos (Nat.factorial_pos _) ?_
    refine Finset.prod_pos ?_
    intro i _
    exact Nat.factorial_pos _
  have hprod :
      (∏ i : Fin (m + 1), Nat.factorial (k' i)) =
        Nat.factorial r * p := by
    -- Proof comment: the factorial product over `Fin (m + 1)` splits into the head factorial and
    -- the tail factorial product over `Fin m`.
    simp [k', p, Fin.prod_univ_succ]
  have hsum : ∑ i : Fin (m + 1), k' i = n := by
    -- Proof comment: the multinomial total is the head count `r` plus the tail total.
    simpa [k', Fin.sum_univ_succ] using hk
  have htailSpec :
      Nat.factorial (∑ i : Fin m, k i) = p * Nat.multinomial Finset.univ k := by
    -- Proof comment: this is the tail multinomial coefficient written with the shared
    -- denominator abbreviation `p`.
    simpa [p, mul_comm, mul_left_comm, mul_assoc] using
      (Nat.multinomial_spec (s := Finset.univ) (f := k)).symm
  apply Nat.mul_left_cancel hp_pos
  -- Proof comment: convert both multinomial coefficients to factorial form, then identify the
  -- common binomial factor `n.choose r` via `Nat.add_choose_mul_factorial_mul_factorial`.
  calc
    (Nat.factorial r * p) * Nat.multinomial Finset.univ (Fin.cons r k)
        = (∏ i : Fin (m + 1), Nat.factorial (k' i)) *
            Nat.multinomial Finset.univ (Fin.cons r k) := by
            rw [hprod]
    _ = Nat.factorial (∑ i : Fin (m + 1), k' i) := by
          simpa [k'] using (Nat.multinomial_spec (s := Finset.univ) (f := k'))
    _ = Nat.factorial n := by
          rw [hsum]
    _ = n.choose r * (Nat.factorial (∑ i : Fin m, k i) * Nat.factorial r) := by
          simpa [hk, add_comm, add_left_comm, add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            (Nat.add_choose_mul_factorial_mul_factorial (∑ i : Fin m, k i) r).symm
    _ = n.choose r * (Nat.factorial r * (p * Nat.multinomial Finset.univ k)) := by
          rw [htailSpec]
          dsimp [p]
          ac_rfl
    _ = (Nat.factorial r * p) * (n.choose r * Nat.multinomial Finset.univ k) := by
          ac_rfl

/-- Helper for Lemma 23.12: on `Fin (m + 1)`, the lower prefactor splits into one head factor and
the tail prefactor on `Fin m`. -/
private theorem empiricalLowerPrefactor_finSucc (m n : ℕ) :
    empiricalLowerPrefactor (Fin (m + 1)) n =
      ((n + 1 : ℕ) : ENNReal)⁻¹ * empiricalLowerPrefactor (Fin m) n := by
  -- Proof comment: this is the power identity `a^(m + 1) = a * a^m` for the common base
  -- `((n + 1 : ℕ) : ENNReal)⁻¹`.
  simp [empiricalLowerPrefactor, pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- Helper for Lemma 23.12: the self-binomial parameter `r / n` lies in `[0, 1]` whenever
`r ≤ n` and `n ≠ 0`. -/
private theorem selfBinomialParameter_le_one {n r : ℕ} (hn : n ≠ 0) (hr : r ≤ n) :
    ((r : NNReal) / (n : NNReal) : NNReal) ≤ 1 := by
  -- Proof comment: divide the inequality `r ≤ n` by the nonnegative denominator `n`.
  exact div_le_one_of_le₀ (by exact_mod_cast hr) (by positivity)

/-- Helper for Lemma 23.12: complementing the self-binomial parameter rewrites to the normalized
tail count `(n - r) / n`. -/
private theorem selfBinomialParameter_compl {n r : ℕ} (hn : n ≠ 0) (hr : r ≤ n) :
    (1 - ((r : NNReal) / (n : NNReal) : NNReal)) = ((n - r : ℕ) : NNReal) / (n : NNReal) := by
  have hle : ((r : NNReal) / (n : NNReal) : NNReal) ≤ 1 :=
    selfBinomialParameter_le_one hn hr
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  apply NNReal.coe_injective
  -- Proof comment: after coercing to `ℝ`, this is the elementary identity
  -- `1 - r / n = (n - r) / n`.
  rw [NNReal.coe_sub hle, NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, Nat.cast_sub hr]
  field_simp [hn']

/-- Helper for Lemma 23.12: converting a normalized count ratio `c / n` from `ENNReal` to `ℝ`
gives the expected real quotient. -/
private theorem countRatio_toReal_eq {n c : ℕ} (hn : n ≠ 0) :
    ((((c : ℕ) : ENNReal) / (n : ENNReal)).toReal) = (c : ℝ) / n := by
  have hnENN : (n : ENNReal) ≠ 0 := by
    exact_mod_cast hn
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- Helper for Lemma 23.12: the owner binomial parameter `r / n` in `NNReal` coerces to the
chapter's normalized count ratio in `ENNReal`. -/
private theorem selfBinomialOwnerRatio_eq_countRatio {n r : ℕ} (hn : n ≠ 0) :
    ((((r : NNReal) / (n : NNReal) : NNReal) : ENNReal)) =
      (((r : ℕ) : ENNReal) / (n : ENNReal)) := by
  have hright : ((((r : ℕ) : ENNReal) / (n : ENNReal)).toReal) = (r : ℝ) / n :=
    countRatio_toReal_eq (n := n) (c := r) hn
  -- Proof comment: both finite `ENNReal` ratios have the same real value `r / n`, so they are
  -- equal without unfolding the owner binomial API further.
  refine
    (ENNReal.toReal_eq_toReal_iff'
      ENNReal.coe_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top r) (by exact_mod_cast hn))).mp ?_
  simpa using hright.symm

/-- Helper for Lemma 23.12: before the realized count `r`, the binomial coefficient relation
forces the head factor `r` to dominate the tail factor `n - r`. -/
private theorem choose_mul_tail_le_choose_succ_mul_head {n r j : ℕ}
    (hj : j < r) (hr : r ≤ n) :
    (n.choose j) * (n - r) ≤ (n.choose (j + 1)) * r := by
  have htail : n - r ≤ n - j := by
    omega
  have hhead : j + 1 ≤ r := by
    omega
  calc
    (n.choose j) * (n - r) ≤ (n.choose j) * (n - j) := by
      exact Nat.mul_le_mul_left _ htail
    _ = (n.choose (j + 1)) * (j + 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (Nat.choose_succ_right_eq n j).symm
    _ ≤ (n.choose (j + 1)) * r := by
      exact Nat.mul_le_mul_left _ hhead

/-- Helper for Lemma 23.12: after the realized count `r`, the complementary tail factor `n - r`
dominates the head factor `r`. -/
private theorem choose_succ_mul_head_le_choose_mul_tail {n r j : ℕ}
    (hrj : r ≤ j) (hj : j < n) :
    (n.choose (j + 1)) * r ≤ (n.choose j) * (n - r) := by
  have hhead : r ≤ j + 1 := by
    omega
  have htail : n - j ≤ n - r := by
    omega
  calc
    (n.choose (j + 1)) * r ≤ (n.choose (j + 1)) * (j + 1) := by
      exact Nat.mul_le_mul_left _ hhead
    _ = (n.choose j) * (n - j) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using Nat.choose_succ_right_eq n j
    _ ≤ (n.choose j) * (n - r) := by
      exact Nat.mul_le_mul_left _ htail

/-- Helper for Lemma 23.12: the `j`-th atom of the binomial law with self-parameter `r / n`. -/
private def binomialSelfMass (n r j : ℕ) : ENNReal :=
  (n.choose j : ENNReal) *
    (((r : ℕ) : ENNReal) / (n : ENNReal)) ^ j *
      ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ (n - j))

/-- Helper for Lemma 23.12: before the realized count `r`, the self-binomial mass is monotone
nondecreasing along adjacent Pascal-row steps. -/
private theorem binomialSelfMass_adjacent_le {n r j : ℕ}
    (hn : n ≠ 0) (hr : r ≤ n) (hj : j < r) :
    binomialSelfMass n r j ≤ binomialSelfMass n r (j + 1) := by
  let a : ENNReal := ((r : ℕ) : ENNReal) / (n : ENNReal)
  let b : ENNReal := ((n - r : ℕ) : ENNReal) / (n : ENNReal)
  have hsplit : n - j = (n - (j + 1)) + 1 := by
    omega
  have hinnerNat :
      (n.choose j) * (n - r) ≤ (n.choose (j + 1)) * r :=
    choose_mul_tail_le_choose_succ_mul_head (n := n) (r := r) (j := j) hj hr
  have hinner :
      (n.choose j : ENNReal) * b ≤ (n.choose (j + 1) : ENNReal) * a := by
    have hcast :
        ((((n.choose j) * (n - r) : ℕ) : ENNReal)) ≤
          ((((n.choose (j + 1)) * r : ℕ) : ENNReal)) := by
      exact_mod_cast hinnerNat
    have hlhs :
        (n.choose j : ENNReal) * b =
          ((((n.choose j) * (n - r) : ℕ) : ENNReal) / (n : ENNReal)) := by
      dsimp [b]
      calc
        (n.choose j : ENNReal) * (((n - r : ℕ) : ENNReal) / (n : ENNReal))
          = (n : ENNReal)⁻¹ * ((n.choose j : ENNReal) * ((n - r : ℕ) : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              ac_rfl
        _ = ((((n.choose j) * (n - r) : ℕ) : ENNReal) / (n : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              norm_num [Nat.cast_mul]
    have hrhs :
        (n.choose (j + 1) : ENNReal) * a =
          ((((n.choose (j + 1)) * r : ℕ) : ENNReal) / (n : ENNReal)) := by
      dsimp [a]
      calc
        (n.choose (j + 1) : ENNReal) * (((r : ℕ) : ENNReal) / (n : ENNReal))
          = (n : ENNReal)⁻¹ * ((n.choose (j + 1) : ENNReal) * ((r : ℕ) : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              ac_rfl
        _ = ((((n.choose (j + 1)) * r : ℕ) : ENNReal) / (n : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              norm_num [Nat.cast_mul]
    rw [hlhs, hrhs]
    exact ENNReal.div_le_div_right hcast (n : ENNReal)
  -- Proof comment: isolate the common factor `a^j * b^(n - (j + 1))`, then compare the remaining
  -- adjacent Pascal-row terms via the already separated natural-number inequality.
  calc
    binomialSelfMass n r j
      = (a ^ j * b ^ (n - (j + 1))) * ((n.choose j : ENNReal) * b) := by
          simp [binomialSelfMass, a, b, hsplit, pow_add, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (a ^ j * b ^ (n - (j + 1))) * ((n.choose (j + 1) : ENNReal) * a) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_right' hinner (a ^ j * b ^ (n - (j + 1))))
    _ = binomialSelfMass n r (j + 1) := by
          simp [binomialSelfMass, a, b, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 23.12: after the realized count `r`, the self-binomial mass is monotone
nonincreasing along adjacent Pascal-row steps. -/
private theorem binomialSelfMass_adjacent_ge {n r j : ℕ}
    (hn : n ≠ 0) (hr : r ≤ n) (hrj : r ≤ j) (hj : j < n) :
    binomialSelfMass n r (j + 1) ≤ binomialSelfMass n r j := by
  let a : ENNReal := ((r : ℕ) : ENNReal) / (n : ENNReal)
  let b : ENNReal := ((n - r : ℕ) : ENNReal) / (n : ENNReal)
  have hsplit : n - j = (n - (j + 1)) + 1 := by
    omega
  have hinnerNat :
      (n.choose (j + 1)) * r ≤ (n.choose j) * (n - r) :=
    choose_succ_mul_head_le_choose_mul_tail (n := n) (r := r) (j := j) hrj hj
  have hinner :
      (n.choose (j + 1) : ENNReal) * a ≤ (n.choose j : ENNReal) * b := by
    have hcast :
        ((((n.choose (j + 1)) * r : ℕ) : ENNReal)) ≤
          ((((n.choose j) * (n - r) : ℕ) : ENNReal)) := by
      exact_mod_cast hinnerNat
    have hlhs :
        (n.choose (j + 1) : ENNReal) * a =
          ((((n.choose (j + 1)) * r : ℕ) : ENNReal) / (n : ENNReal)) := by
      dsimp [a]
      calc
        (n.choose (j + 1) : ENNReal) * (((r : ℕ) : ENNReal) / (n : ENNReal))
          = (n : ENNReal)⁻¹ * ((n.choose (j + 1) : ENNReal) * ((r : ℕ) : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              ac_rfl
        _ = ((((n.choose (j + 1)) * r : ℕ) : ENNReal) / (n : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              norm_num [Nat.cast_mul]
    have hrhs :
        (n.choose j : ENNReal) * b =
          ((((n.choose j) * (n - r) : ℕ) : ENNReal) / (n : ENNReal)) := by
      dsimp [b]
      calc
        (n.choose j : ENNReal) * (((n - r : ℕ) : ENNReal) / (n : ENNReal))
          = (n : ENNReal)⁻¹ * ((n.choose j : ENNReal) * ((n - r : ℕ) : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              ac_rfl
        _ = ((((n.choose j) * (n - r) : ℕ) : ENNReal) / (n : ENNReal)) := by
              rw [ENNReal.div_eq_inv_mul]
              norm_num [Nat.cast_mul]
    rw [hlhs, hrhs]
    exact ENNReal.div_le_div_right hcast (n : ENNReal)
  -- Proof comment: factor out the same common tail term as in the increasing branch, then apply
  -- the adjacent Pascal-row comparison in the opposite direction.
  calc
    binomialSelfMass n r (j + 1)
      = (a ^ j * b ^ (n - (j + 1))) * ((n.choose (j + 1) : ENNReal) * a) := by
          simp [binomialSelfMass, a, b, pow_succ, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (a ^ j * b ^ (n - (j + 1))) * ((n.choose j : ENNReal) * b) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_right' hinner (a ^ j * b ^ (n - (j + 1))))
    _ = binomialSelfMass n r j := by
          simp [binomialSelfMass, a, b, hsplit, pow_add, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 23.12: the self-binomial atom at `r` dominates every other atom in the same
row. -/
private theorem binomialSelfMass_isMode {n r j : ℕ}
    (hn : n ≠ 0) (hr : r ≤ n) (hj : j ≤ n) :
    binomialSelfMass n r j ≤ binomialSelfMass n r r := by
  have hleft :
      ∀ d : ℕ, d ≤ r → binomialSelfMass n r (r - d) ≤ binomialSelfMass n r r := by
    intro d hd
    induction d with
    | zero =>
        simp
    | succ d ih =>
        have hd' : d ≤ r := Nat.le_trans (Nat.le_succ d) hd
        have hstep :
            binomialSelfMass n r (r - (d + 1)) ≤ binomialSelfMass n r (r - d) := by
          have hjlt : r - (d + 1) < r := by
            omega
          have hsub : r - (d + 1) + 1 = r - d := by
            omega
          simpa [hsub] using
            binomialSelfMass_adjacent_le (n := n) (r := r) (j := r - (d + 1)) hn hr hjlt
        exact hstep.trans (ih hd')
  have hright :
      ∀ d : ℕ, r + d ≤ n → binomialSelfMass n r (r + d) ≤ binomialSelfMass n r r := by
    intro d hd
    induction d with
    | zero =>
        simp
    | succ d ih =>
        have hd' : r + d ≤ n := by omega
        have hstep :
            binomialSelfMass n r (r + (d + 1)) ≤ binomialSelfMass n r (r + d) := by
          have hjlt : r + d < n := by omega
          have hrj : r ≤ r + d := by omega
          simpa [Nat.add_assoc] using
            binomialSelfMass_adjacent_ge (n := n) (r := r) (j := r + d) hn hr hrj hjlt
        exact hstep.trans (ih hd')
  by_cases hjr : j ≤ r
  · let d := r - j
    have hd : d ≤ r := Nat.sub_le _ _
    have hEq : r - d = j := by
      dsimp [d]
      omega
    simpa [d, hEq] using hleft d hd
  · let d := j - r
    have hd : r + d ≤ n := by
      dsimp [d]
      omega
    have hEq : r + d = j := by
      dsimp [d]
      omega
    simpa [d, hEq] using hright d hd

/-- Helper for Lemma 23.12: `binomialSelfMass` is the owner `PMF.binomial` atom at the same
coordinate. -/
private theorem binomialSelfMass_eq_binomial_apply {n r j : ℕ}
    (hn : n ≠ 0) (hr : r ≤ n) (hj : j ≤ n) :
    binomialSelfMass n r j =
      PMF.binomial (((r : NNReal) / (n : NNReal) : NNReal))
        (selfBinomialParameter_le_one hn hr) n (Fin.ofNat (n + 1) j) := by
  have hhead :
      ((((r : NNReal) / (n : NNReal) : NNReal) : ENNReal)) =
        (((r : ℕ) : ENNReal) / (n : ENNReal)) :=
    selfBinomialOwnerRatio_eq_countRatio (n := n) (r := r) hn
  have htail :
      ((((1 - ((r : NNReal) / (n : NNReal) : NNReal)) : NNReal) : ENNReal)) =
        (((n - r : ℕ) : ENNReal) / (n : ENNReal)) := by
    -- Proof comment: the owner complement parameter is the same normalized tail count.
    simpa [selfBinomialParameter_compl (n := n) (r := r) hn hr] using
      (selfBinomialOwnerRatio_eq_countRatio (n := n) (r := n - r) hn)
  -- Route correction: use the owner binomial atom formula directly and normalize only the head
  -- and tail ratio spellings, instead of introducing a broader transport layer.
  calc
    binomialSelfMass n r j
      = ((((r : NNReal) / (n : NNReal) : NNReal) : ENNReal)) ^ j *
          ((((1 - ((r : NNReal) / (n : NNReal) : NNReal)) : NNReal) : ENNReal) ^ (n - j)) *
            (n.choose j : ℕ) := by
              rw [binomialSelfMass, hhead, htail]
              ac_rfl
    _ = PMF.binomial (((r : NNReal) / (n : NNReal) : NNReal))
          (selfBinomialParameter_le_one hn hr) n (Fin.ofNat (n + 1) j) := by
            simpa [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj), mul_assoc, mul_left_comm, mul_comm] using
              (PMF.binomial_apply (((r : NNReal) / (n : NNReal) : NNReal))
                (selfBinomialParameter_le_one hn hr) n (Fin.ofNat (n + 1) j)).symm

/-- Helper for Lemma 23.12: the realized self-binomial atom is at least the reciprocal of the
support size `n + 1`. -/
private theorem binomialSelfMass_ge_inv_succ {n r : ℕ}
    (hn : n ≠ 0) (hr : r ≤ n) :
    ((n + 1 : ℕ) : ENNReal)⁻¹ ≤ binomialSelfMass n r r := by
  let p : PMF (Fin (n + 1)) :=
    PMF.binomial (((r : NNReal) / (n : NNReal) : NNReal)) (selfBinomialParameter_le_one hn hr) n
  have hmax : ∀ b : Fin (n + 1), p b ≤ p (Fin.ofNat (n + 1) r) := by
    intro b
    have hb : (b : ℕ) ≤ n := Nat.le_of_lt_succ b.2
    -- Proof comment: transport the mode estimate for the custom self-binomial formula to the
    -- owner PMF coordinates via `binomialSelfMass_eq_binomial_apply`.
    calc
      p b = binomialSelfMass n r b := by
        simpa [p] using
          (binomialSelfMass_eq_binomial_apply (n := n) (r := r) (j := b) hn hr hb).symm
      _ ≤ binomialSelfMass n r r := binomialSelfMass_isMode hn hr hb
      _ = p (Fin.ofNat (n + 1) r) := by
        simpa [p] using
          (binomialSelfMass_eq_binomial_apply (n := n) (r := r) (j := r) hn hr hr)
  -- Proof comment: a maximal atom of a finite PMF is at least the reciprocal of the support
  -- size, here `n + 1`.
  calc
    ((n + 1 : ℕ) : ENNReal)⁻¹ = ((Fintype.card (Fin (n + 1)) : ℕ) : ENNReal)⁻¹ := by simp
    _ ≤ p (Fin.ofNat (n + 1) r) := pmfValue_ge_inv_card_of_ge_all p (Fin.ofNat (n + 1) r) hmax
    _ = binomialSelfMass n r r := by
      simpa [p] using
        (binomialSelfMass_eq_binomial_apply (n := n) (r := r) (j := r) hn hr hr).symm

/-- Helper for Lemma 23.12: the lower prefactor is antitone in the sample size parameter. -/
private theorem empiricalLowerPrefactor_antitone (m a b : ℕ) (hab : a ≤ b) :
    empiricalLowerPrefactor (Fin m) b ≤ empiricalLowerPrefactor (Fin m) a := by
  have hbase :
      (((b + 1 : ℕ) : ENNReal)⁻¹) ≤ (((a + 1 : ℕ) : ENNReal)⁻¹) := by
    exact ENNReal.inv_le_inv' (by exact_mod_cast Nat.succ_le_succ hab)
  -- Proof comment: both prefactors are powers of the same inverse base, so antitonicity in `n`
  -- reduces to antitonicity of the inverse base itself.
  simpa [empiricalLowerPrefactor] using (ENNReal.pow_le_pow_left (n := m) hbase)

/-- Helper for Lemma 23.12: factoring each tail coordinate ratio `k i / n` through the normalized
tail mass `(n - r) / n` pulls out the common power `((n - r) / n)^(n - r)` from the whole
product. -/
private theorem tailCountProductFactor {m n r : ℕ} (k : Fin m → ℕ)
    (hsum_tail : ∑ i, k i = n - r) (htail : n - r ≠ 0) :
    ∏ i : Fin m, (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i =
      ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ (n - r)) *
        ∏ i : Fin m, (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i := by
  have htailENN : ((n - r : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast htail
  -- Proof comment: rewrite each factor `k i / n` as the common tail ratio `((n - r) / n)` times
  -- the normalized tail coordinate `k i / (n - r)`.
  calc
    ∏ i : Fin m, (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i
      = ∏ i : Fin m,
          (((((n - r : ℕ) : ENNReal) / (n : ENNReal)) *
              (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal))) ^ k i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            congr 1
            symm
            calc
              (((n - r : ℕ) : ENNReal) / (n : ENNReal)) *
                  (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal))
                  = (n : ENNReal)⁻¹ *
                      (((n - r : ℕ) : ENNReal) *
                        ((((n - r : ℕ) : ENNReal)⁻¹) * ((k i : ℕ) : ENNReal))) := by
                          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
                          ac_rfl
              _ = (n : ENNReal)⁻¹ * ((k i : ENNReal)) := by
                    rw [ENNReal.mul_inv_cancel_left htailENN (ENNReal.natCast_ne_top _)]
              _ = (((k i : ℕ) : ENNReal) / (n : ENNReal)) := by
                    rw [ENNReal.div_eq_inv_mul]
    _ = ∏ i : Fin m,
          ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ k i) *
            ((((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          rw [mul_pow]
    _ = (∏ i : Fin m, ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ k i)) *
          ∏ i : Fin m, ((((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          rw [Finset.prod_mul_distrib]
    _ = ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ (∑ i : Fin m, k i)) *
          ∏ i : Fin m, ((((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ = ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ (n - r)) *
          ∏ i : Fin m, ((((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          rw [hsum_tail]

/-- Helper for Lemma 23.12: splitting the encoded self-histogram at the first coordinate factors
the mass into the self-binomial head and the normalized tail self-histogram mass. -/
private theorem encodedSelfHistogramMassFinSuccFactor {m n r : ℕ} (k : Fin m → ℕ)
    (hk : r + ∑ i : Fin m, k i = n) (htail : n - r ≠ 0) :
    (Nat.multinomial Finset.univ (Fin.cons r k) : ENNReal) *
        ∏ i : Fin (m + 1),
          (((((Fin.cons r k : Fin (m + 1) → ℕ) i) : ℕ) : ENNReal) / (n : ENNReal)) ^
            (((Fin.cons r k : Fin (m + 1) → ℕ) i) : ℕ)
      =
    binomialSelfMass n r r *
      ((Nat.multinomial Finset.univ k : ENNReal) *
        ∏ i : Fin m, (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
  have hsum_tail : ∑ i : Fin m, k i = n - r := by
    omega
  -- Proof comment: split the head coordinate off from both the multinomial coefficient and the
  -- histogram product, then rewrite the tail product with `tailCountProductFactor`.
  calc
    (Nat.multinomial Finset.univ (Fin.cons r k) : ENNReal) *
        ∏ i : Fin (m + 1),
          (((((Fin.cons r k : Fin (m + 1) → ℕ) i) : ℕ) : ENNReal) / (n : ENNReal)) ^
            (((Fin.cons r k : Fin (m + 1) → ℕ) i) : ℕ)
      = ((n.choose r : ENNReal) * (Nat.multinomial Finset.univ k : ENNReal)) *
          ((((r : ℕ) : ENNReal) / (n : ENNReal)) ^ r *
            ∏ i : Fin m, (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i) := by
            rw [multinomialFinSuccSplit m n r k hk]
            simp [Fin.prod_univ_succ, mul_assoc, mul_left_comm, mul_comm]
    _ = ((n.choose r : ENNReal) *
          ((((r : ℕ) : ENNReal) / (n : ENNReal)) ^ r) *
          ((((n - r : ℕ) : ENNReal) / (n : ENNReal)) ^ (n - r))) *
        ((Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i : Fin m, (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          rw [tailCountProductFactor k hsum_tail htail]
          ac_rfl
    _ = binomialSelfMass n r r *
        ((Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i : Fin m, (((k i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ k i) := by
          simp [binomialSelfMass, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 23.12: the self-law exact histogram mass is bounded below by the combinatorial
prefactor `(n + 1)^{-m}`. -/
private theorem encodedSelfHistogramMass_ge_lowerPrefactor :
    ∀ {m n : ℕ} (k : Fin m → ℕ), (∑ i, k i = n) →
      empiricalLowerPrefactor (Fin m) n ≤
        (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i : Fin m, (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i
  | 0, n, k, hk => by
      have hn0 : n = 0 := by simpa using hk.symm
      subst n
      simp [empiricalLowerPrefactor]
  | m + 1, n, k, hk => by
      let r : ℕ := k 0
      let kTail : Fin m → ℕ := fun i ↦ k i.succ
      have hkSplit : r + ∑ i : Fin m, kTail i = n := by
        -- Proof comment: split the total histogram count into the head coordinate and the tail
        -- coordinates on `Fin m`.
        simpa [r, kTail, Fin.sum_univ_succ] using hk
      have hkCons : k = Fin.cons r kTail := by
        -- Proof comment: every histogram on `Fin (m + 1)` is exactly its head count together
        -- with the tail histogram on `Fin m`.
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      by_cases htail : n - r = 0
      · have hr : r = n := by
          omega
        have hsum_tail : ∑ i : Fin m, kTail i = 0 := by
          omega
        have hkTailZero : kTail = fun _ : Fin m ↦ 0 := by
          funext i
          have hle : kTail i ≤ ∑ j : Fin m, kTail j := by
            simpa using
              (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (by simp : i ∈ Finset.univ))
          rw [hsum_tail] at hle
          exact Nat.eq_zero_of_le_zero hle
        have hkDeg : k = Fin.cons n (fun _ : Fin m ↦ 0) := by
          calc
            k = Fin.cons r kTail := hkCons
            _ = Fin.cons n (fun _ : Fin m ↦ 0) := by simp [hr, hkTailZero]
        have hmass_one :
            (Nat.multinomial Finset.univ k : ENNReal) *
                ∏ i : Fin (m + 1), (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i
              = 1 := by
          -- Proof comment: when the whole count sits in the head coordinate, the multinomial
          -- coefficient and every tail factor are trivial, so the exact mass is `1`.
          rw [hkDeg]
          have hheadMult :
              Nat.multinomial Finset.univ (Fin.cons n (fun _ : Fin m ↦ 0)) = 1 := by
            have hspec :
                Nat.factorial n =
                  Nat.factorial n *
                    Nat.multinomial Finset.univ (Fin.cons n (fun _ : Fin m ↦ 0)) := by
              simpa [Fin.sum_univ_succ, Fin.prod_univ_succ] using
                (Nat.multinomial_spec (s := Finset.univ)
                  (f := Fin.cons n (fun _ : Fin m ↦ 0))).symm
            have hspec' :
                Nat.factorial n * 1 =
                  Nat.factorial n *
                    Nat.multinomial Finset.univ (Fin.cons n (fun _ : Fin m ↦ 0)) := by
              simpa using hspec
            exact (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) hspec').symm
          have hratio : ((n : ENNReal) / (n : ENNReal)) ^ n = 1 := by
            by_cases hn0 : n = 0
            · simp [hn0]
            · rw [ENNReal.div_self (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n), one_pow]
          simp [Fin.prod_univ_succ, hheadMult, hratio]
        have hpref_le_one :
            empiricalLowerPrefactor (Fin (m + 1)) n ≤ 1 := by
          -- Proof comment: the prefactor decreases with `n`, so it is bounded by its value `1`
          -- at sample size `0`.
          calc
            empiricalLowerPrefactor (Fin (m + 1)) n
              ≤ empiricalLowerPrefactor (Fin (m + 1)) 0 :=
                empiricalLowerPrefactor_antitone (m + 1) 0 n (Nat.zero_le _)
            _ = 1 := by simp [empiricalLowerPrefactor]
        rwa [hmass_one]
      · have hn : n ≠ 0 := by
          intro hn0
          exact htail (by simp [hn0, r])
        have hr : r ≤ n := by
          omega
        have hsum_tail : ∑ i : Fin m, kTail i = n - r := by
          omega
        have htailLower :
            empiricalLowerPrefactor (Fin m) (n - r) ≤
              (Nat.multinomial Finset.univ kTail : ENNReal) *
                ∏ i : Fin m, (((kTail i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ kTail i :=
          encodedSelfHistogramMass_ge_lowerPrefactor kTail hsum_tail
        have hsplit :
            (Nat.multinomial Finset.univ k : ENNReal) *
                ∏ i : Fin (m + 1), (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i
              =
            binomialSelfMass n r r *
              ((Nat.multinomial Finset.univ kTail : ENNReal) *
                ∏ i : Fin m, (((kTail i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ kTail i) := by
          simpa [hkCons] using
            encodedSelfHistogramMassFinSuccFactor (m := m) (n := n) (r := r) kTail hkSplit htail
        -- Proof comment: the head factor contributes at least `(n + 1)⁻¹`, while the recursive
        -- tail mass contributes at least the lower prefactor at size `n - r`, which dominates the
        -- tail prefactor at size `n`.
        calc
          empiricalLowerPrefactor (Fin (m + 1)) n
            = ((n + 1 : ℕ) : ENNReal)⁻¹ * empiricalLowerPrefactor (Fin m) n := by
                rw [empiricalLowerPrefactor_finSucc]
          _ ≤ ((n + 1 : ℕ) : ENNReal)⁻¹ * empiricalLowerPrefactor (Fin m) (n - r) := by
                exact mul_le_mul_left' (empiricalLowerPrefactor_antitone m (n - r) n (Nat.sub_le _ _)) _
          _ ≤ binomialSelfMass n r r * empiricalLowerPrefactor (Fin m) (n - r) := by
                exact mul_le_mul_right' (binomialSelfMass_ge_inv_succ hn hr) _
          _ ≤ binomialSelfMass n r r *
                ((Nat.multinomial Finset.univ kTail : ENNReal) *
                  ∏ i : Fin m, (((kTail i : ℕ) : ENNReal) / ((n - r : ℕ) : ENNReal)) ^ kTail i) := by
                exact mul_le_mul_left' htailLower _
          _ = (Nat.multinomial Finset.univ k : ENNReal) *
                ∏ i : Fin (m + 1), (((k i : ℕ) : ENNReal) / (n : ENNReal)) ^ k i := by
                rw [hsplit]

/-- Helper for Lemma 23.12: the self-law probability of a realized empirical histogram is bounded
below by the prefactor `(n + 1)^{-#S}`. -/
private theorem selfEmpiricalDistributionProbability_ge_lowerPrefactor
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν) :
    empiricalLowerPrefactor S n ≤ empiricalDistributionProbability ν n ν := by
  have hk :
      ∑ i : Fin (Fintype.card S),
        empiricalCount n x ((Fintype.equivFin S).symm i) = n := by
    have hReindex :
        (∑ a : S, empiricalCount n x a) =
          ∑ i : Fin (Fintype.card S), empiricalCount n x ((Fintype.equivFin S).symm i) := by
      refine Fintype.sum_equiv (Fintype.equivFin S)
        (fun a : S ↦ empiricalCount n x a)
        (fun i : Fin (Fintype.card S) ↦ empiricalCount n x ((Fintype.equivFin S).symm i)) ?_
      intro a
      simp
    calc
      ∑ i : Fin (Fintype.card S), empiricalCount n x ((Fintype.equivFin S).symm i)
        = ∑ a : S, empiricalCount n x a := by
            simpa using hReindex.symm
      _ = n := sum_empiricalCount n x
  have hbound :
      empiricalLowerPrefactor (Fin (Fintype.card S)) n ≤
        (Nat.multinomial Finset.univ
          (fun i : Fin (Fintype.card S) ↦
            empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
          ∏ i : Fin (Fintype.card S),
            (((empiricalCount n x ((Fintype.equivFin S).symm i) : ℕ) : ENNReal) /
              (n : ENNReal)) ^
              empiricalCount n x ((Fintype.equivFin S).symm i) :=
    encodedSelfHistogramMass_ge_lowerPrefactor
      (fun i : Fin (Fintype.card S) ↦ empiricalCount n x ((Fintype.equivFin S).symm i)) hk
  -- Proof comment: rewrite the exact self-law mass in encoded coordinates, replace every encoded
  -- singleton mass by the normalized empirical count, and apply the encoded lower bound.
  calc
    empiricalLowerPrefactor S n = empiricalLowerPrefactor (Fin (Fintype.card S)) n := by
      simp [empiricalLowerPrefactor]
    _ ≤
        (Nat.multinomial Finset.univ
          (fun i : Fin (Fintype.card S) ↦
            empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
          ∏ i : Fin (Fintype.card S),
            (((empiricalCount n x ((Fintype.equivFin S).symm i) : ℕ) : ENNReal) /
              (n : ENNReal)) ^
              empiricalCount n x ((Fintype.equivFin S).symm i) := hbound
    _ = empiricalDistributionProbability ν n ν := by
        rw [empiricalDistributionProbability_eq_multinomialMass (μ := ν) hx]
        refine congrArg (fun t : ENNReal ↦
          (Nat.multinomial Finset.univ
            (fun i : Fin (Fintype.card S) ↦
              empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) * t) ?_
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [encodedHistogramMass_eq_countRatio (x := x) hx i]

/-- Helper for Lemma 23.12: the exact multinomial mass can be rewritten directly as the
multinomial coefficient times the singleton-mass product on the original alphabet `S`. -/
private theorem empiricalDistributionProbability_eq_multinomialMass_prod_singleton
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {μ ν : ProbabilityMeasure S} {n : ℕ} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν) :
    empiricalDistributionProbability μ n ν =
      (Nat.multinomial Finset.univ
        (fun i : Fin (Fintype.card S) ↦
          empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
        ∏ a : S, ((μ : Measure S) {a}) ^ empiricalCount n x a := by
  let k : Fin (Fintype.card S) → ℕ := fun i ↦ empiricalCount n x ((Fintype.equivFin S).symm i)
  -- Proof comment: first rewrite the exact mass using the encoded alphabet `Fin (Fintype.card S)`.
  calc
    empiricalDistributionProbability μ n ν
      = (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i : Fin (Fintype.card S),
            ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) i) ^ k i := by
            simpa [k] using empiricalDistributionProbability_eq_multinomialMass (μ := μ) (x := x) hx
    _ = (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i : Fin (Fintype.card S),
            ((μ : Measure S) {(Fintype.equivFin S).symm i}) ^ k i := by
            refine congrArg (fun t : ENNReal ↦ (Nat.multinomial Finset.univ k : ENNReal) * t) ?_
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [show ((((μ : Measure S).toPMF).map (Fintype.equivFin S)) i) =
                (μ : Measure S) {(Fintype.equivFin S).symm i} by
                simpa using toPMF_map_equivFin_apply (μ := μ) ((Fintype.equivFin S).symm i)]
    _ = (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ a : S, ((μ : Measure S) {a}) ^ empiricalCount n x a := by
            refine congrArg (fun t : ENNReal ↦ (Nat.multinomial Finset.univ k : ENNReal) * t) ?_
            simpa [k] using
              (Equiv.prod_comp (Fintype.equivFin S).symm
                (fun a : S ↦ ((μ : Measure S) {a}) ^ empiricalCount n x a))

/-- Helper for Lemma 23.12: on a finite singleton-measurable alphabet, absolute continuity
identifies the KL divergence with the finite sum of its singleton gap terms. -/
private theorem klDiv_eq_sum_gapSeriesTerm_of_absolutelyContinuous
    [Fintype S] [MeasurableSingletonClass S]
    (μ ν : ProbabilityMeasure S) (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    klDiv (ν : Measure S) (μ : Measure S) =
      ∑ a : S,
        ENNReal.ofReal
          (((μ : Measure S) {a}).toReal *
            klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) := by
  classical
  let p : PMF S := (ν : Measure S).toPMF
  let q : S → ENNReal := fun a ↦ (μ : Measure S) {a}
  have hq : (∑' a : S, q a) ≤ 1 := by
    -- Proof comment: the comparison singleton masses are exactly the PMF weights of `μ`.
    exact le_of_eq (by simpa [q, Measure.toPMF_apply] using (PMF.tsum_coe ((μ : Measure S).toPMF)))
  have hnozero : ∀ a ∈ p.support, q a ≠ 0 := by
    -- Proof comment: absolute continuity forces positive `ν`-atoms to sit over positive `μ`-atoms.
    intro a ha
    intro hqa
    have hνa : (ν : Measure S) {a} = 0 := h_ac hqa
    exact (PMF.mem_support_iff p a).1 ha (by simpa [p, Measure.toPMF_apply] using hνa)
  have hqMeasure : Measure.count.withDensity q = (μ : Measure S) := by
    -- Proof comment: on a finite singleton-measurable alphabet, weighting counting measure by the
    -- singleton masses `μ {a}` reconstructs `μ` itself.
    ext s hs
    rw [withDensity_apply _ hs, ← lintegral_indicator hs q, lintegral_count]
    simpa [q, Measure.toPMF_apply] using
      (((μ : Measure S).toPMF).toMeasure_apply_fintype s).symm
  -- Proof comment: this is exactly the private discrete-PMF KL expansion, now rewritten back to
  -- the ambient measure `(μ : Measure S)` via `hqMeasure`.
  calc
    klDiv (ν : Measure S) (μ : Measure S)
      = ∑' a : S,
          ENNReal.ofReal ((q a).toReal * klFun (((p a : ENNReal) / q a).toReal)) := by
            simpa [p, q, Measure.toPMF_apply, hqMeasure] using
              discreteKlDiv_eq_gapSeries p q hq hnozero
    _ = ∑ a : S,
          ENNReal.ofReal
            (((μ : Measure S) {a}).toReal *
              klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) := by
            rw [tsum_fintype]
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [p, q, Measure.toPMF_apply]

/-- Helper for Lemma 23.12: on a finite singleton-measurable alphabet, absolute continuity
rewrites the KL divergence as the finite singleton logarithmic ratio sum. -/
private theorem klDiv_toReal_eq_sum_logRatio_of_absolutelyContinuous
    [Fintype S] [MeasurableSingletonClass S]
    (μ ν : ProbabilityMeasure S) (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    (klDiv (ν : Measure S) (μ : Measure S)).toReal =
      ∑ a : S,
        ((ν : Measure S) {a}).toReal *
          (Real.log ((ν : Measure S) {a}).toReal - Real.log ((μ : Measure S) {a}).toReal) := by
  classical
  let p : PMF S := (ν : Measure S).toPMF
  let q : S → ENNReal := fun a ↦ (μ : Measure S) {a}
  have hq : (∑' a : S, q a) ≤ 1 := by
    -- Proof comment: the comparison singleton masses sum to `1` because they come from `μ`.
    exact le_of_eq <| by
      simpa [q, Measure.toPMF_apply] using (PMF.tsum_coe ((μ : Measure S).toPMF))
  have hnozero : ∀ a ∈ p.support, q a ≠ 0 := by
    -- Proof comment: every atom in the support of `ν` must lie over a positive `μ`-atom.
    intro a ha
    intro hqa
    have hνa : (ν : Measure S) {a} = 0 := h_ac hqa
    exact (PMF.mem_support_iff p a).1 ha (by simpa [p, Measure.toPMF_apply] using hνa)
  have hterm_ne_top :
      ∀ a ∈ (Finset.univ : Finset S),
        ENNReal.ofReal
            (((μ : Measure S) {a}).toReal *
              klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) ≠ ⊤ := by
    intro a ha
    exact ENNReal.ofReal_ne_top
  have hklReal :=
    congrArg ENNReal.toReal
      (klDiv_eq_sum_gapSeriesTerm_of_absolutelyContinuous (μ := μ) (ν := ν) h_ac)
  rw [ENNReal.toReal_sum hterm_ne_top] at hklReal
  have hklGap :
      (klDiv (ν : Measure S) (μ : Measure S)).toReal =
        ∑ a : S,
          ((μ : Measure S) {a}).toReal *
            klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal) := by
    refine hklReal.trans ?_
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg
      (klFun_nonneg ENNReal.toReal_nonneg))]
  have hμmass :
      ∑ a : S, ((μ : Measure S) {a}).toReal = 1 := by
    calc
      ∑ a : S, ((μ : Measure S) {a}).toReal
        = ∑ a : S, ((((μ : Measure S).toPMF) a : ENNReal)).toReal := by
            simp [Measure.toPMF_apply]
      _ = (∑ a : S, (((μ : Measure S).toPMF) a : ENNReal)).toReal := by
            symm
            refine ENNReal.toReal_sum ?_
            intro a ha
            exact PMF.apply_ne_top _ _
      _ = (∑' a : S, ((μ : Measure S).toPMF) a).toReal := by rw [tsum_fintype]
      _ = 1 := by
            simpa using congrArg ENNReal.toReal (PMF.tsum_coe ((μ : Measure S).toPMF))
  have hνmass :
      ∑ a : S, ((ν : Measure S) {a}).toReal = 1 := by
    calc
      ∑ a : S, ((ν : Measure S) {a}).toReal
        = ∑ a : S, ((((ν : Measure S).toPMF) a : ENNReal)).toReal := by
            simp [Measure.toPMF_apply]
      _ = (∑ a : S, (((ν : Measure S).toPMF) a : ENNReal)).toReal := by
            symm
            refine ENNReal.toReal_sum ?_
            intro a ha
            exact PMF.apply_ne_top _ _
      _ = (∑' a : S, ((ν : Measure S).toPMF) a).toReal := by rw [tsum_fintype]
      _ = 1 := by
            simpa using congrArg ENNReal.toReal (PMF.tsum_coe ((ν : Measure S).toPMF))
  -- Proof comment: rewrite each finite KL term through `crossEntropyGapTermIdentity`, then the
  -- linear correction cancels because both singleton-mass sums are `1`.
  calc
    (klDiv (ν : Measure S) (μ : Measure S)).toReal
      = ∑ a : S,
          (((μ : Measure S) {a}).toReal *
            klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) := hklGap
    _ = ∑ a : S,
          ((((ν : Measure S) {a}).toReal *
              (Real.log ((ν : Measure S) {a}).toReal -
                Real.log ((μ : Measure S) {a}).toReal)) +
            (((μ : Measure S) {a}).toReal - ((ν : Measure S) {a}).toReal)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hterm := crossEntropyGapTermIdentity p q hq hnozero a
          have hterm' :
              (q a).toReal * klFun (((p a : ENNReal) / q a).toReal) =
                (p a).toReal * (Real.log (p a).toReal - Real.log (q a).toReal) +
                  ((q a).toReal - (p a).toReal) := by
            linarith [hterm]
          simpa [p, q, Measure.toPMF_apply] using hterm'
    _ = (∑ a : S,
          ((ν : Measure S) {a}).toReal *
            (Real.log ((ν : Measure S) {a}).toReal - Real.log ((μ : Measure S) {a}).toReal)) +
          ((∑ a : S, ((μ : Measure S) {a}).toReal) - (∑ a : S, ((ν : Measure S) {a}).toReal)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a : S,
          ((ν : Measure S) {a}).toReal *
            (Real.log ((ν : Measure S) {a}).toReal - Real.log ((μ : Measure S) {a}).toReal) := by
          rw [hμmass, hνmass]
          ring

/-- Helper for Lemma 23.12: if the atom masses of `ν` are the normalized counts of a realized
histogram, then the corresponding singleton-mass product for `μ` is obtained by scaling the
singleton-mass product for `ν` by `exp (-n * klDiv)`. -/
private theorem singletonMassProduct_eq_expNegKlFactor
    [Fintype S] [MeasurableSingletonClass S]
    {μ ν : ProbabilityMeasure S} {n : ℕ} (c : S → ℕ)
    (hn : n ≠ 0)
    (hcount : ∀ a : S, (ν : Measure S) {a} = ((c a : ℕ) : ENNReal) / (n : ENNReal))
    (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    ENNReal.ofReal
        (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal)) *
        ∏ a : S, ((ν : Measure S) {a}) ^ c a
      =
    ∏ a : S, ((μ : Measure S) {a}) ^ c a := by
  classical
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  have hcountReal :
      ∀ a : S, ((ν : Measure S) {a}).toReal = (c a : ℝ) / n := by
    intro a
    rw [hcount a]
    simpa using countRatio_toReal_eq (n := n) (c := c a) hn
  have hexponent :
      -(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal =
        ∑ a : S,
          (c a : ℝ) *
            (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal) := by
    rw [klDiv_toReal_eq_sum_logRatio_of_absolutelyContinuous (μ := μ) (ν := ν) h_ac]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    -- Proof comment: only the scalar coefficient `((ν {a}).toReal)` is rewritten to `c a / n`;
    -- the logarithmic term stays on the original singleton masses.
    have hterm :
        -(n : ℝ) *
            (((ν : Measure S) {a}).toReal *
              (Real.log ((ν : Measure S) {a}).toReal -
                Real.log ((μ : Measure S) {a}).toReal)) =
          (c a : ℝ) *
            (Real.log ((μ : Measure S) {a}).toReal -
              Real.log ((ν : Measure S) {a}).toReal) := by
      rw [hcountReal a]
      field_simp [hnReal]
      ring
    exact hterm
  have hμatom_ne_top : ∀ a : S, (μ : Measure S) {a} ≠ ⊤ := by
    intro a
    have hle :
        (μ : Measure S) {a} ≤ (μ : Measure S) Set.univ := by
      exact measure_mono (by intro x hx; simp)
    have hone : (μ : Measure S) Set.univ = 1 := by simp
    exact ne_of_lt (lt_of_le_of_lt (hone ▸ hle) ENNReal.one_lt_top)
  have hνatom_ne_top : ∀ a : S, (ν : Measure S) {a} ≠ ⊤ := by
    intro a
    have hle :
        (ν : Measure S) {a} ≤ (ν : Measure S) Set.univ := by
      exact measure_mono (by intro x hx; simp)
    have hone : (ν : Measure S) Set.univ = 1 := by simp
    exact ne_of_lt (lt_of_le_of_lt (hone ▸ hle) ENNReal.one_lt_top)
  have hfactor :
      ∀ a : S,
        ENNReal.ofReal
            (Real.exp
              ((c a : ℝ) *
                (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal))) *
            ((ν : Measure S) {a}) ^ c a
          =
        ((μ : Measure S) {a}) ^ c a := by
    intro a
    by_cases hca : c a = 0
    · -- Proof comment: zero-count coordinates contribute the trivial factor `1`.
      simp [hca]
    · have hc_pos : 0 < c a := Nat.pos_of_ne_zero hca
      have hνatom_ne_zero : (ν : Measure S) {a} ≠ 0 := by
        rw [hcount a, ENNReal.div_ne_zero]
        exact ⟨by exact_mod_cast hca, ENNReal.natCast_ne_top n⟩
      have hμatom_ne_zero : (μ : Measure S) {a} ≠ 0 := by
        intro hμ0
        exact hνatom_ne_zero (h_ac hμ0)
      have hνreal_pos : 0 < ((ν : Measure S) {a}).toReal := by
        rw [hcountReal a]
        positivity
      have hμreal_pos : 0 < ((μ : Measure S) {a}).toReal :=
        ENNReal.toReal_pos hμatom_ne_zero (hμatom_ne_top a)
      have hexp :
          Real.exp
              ((c a : ℝ) *
                (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal))
            =
          ((((μ : Measure S) {a}).toReal / ((ν : Measure S) {a}).toReal) ^ c a) := by
        rw [show ((c a : ℝ) *
            (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal)) =
              (c a : ℕ) *
                (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal) by
              norm_num]
        rw [Real.exp_nat_mul, Real.exp_sub, Real.exp_log hμreal_pos, Real.exp_log hνreal_pos]
      have hratio :
          ENNReal.ofReal
              (((μ : Measure S) {a}).toReal / ((ν : Measure S) {a}).toReal)
            =
          (μ : Measure S) {a} / (ν : Measure S) {a} := by
        rw [ENNReal.ofReal_div_of_pos hνreal_pos, ENNReal.ofReal_toReal (hμatom_ne_top a),
          ENNReal.ofReal_toReal (hνatom_ne_top a)]
      -- Proof comment: on positive-count coordinates, the exponential factor is exactly the
      -- ratio `(μ {a} / ν {a}) ^ c a`, so multiplying by `ν {a} ^ c a` cancels to `μ {a} ^ c a`.
      calc
        ENNReal.ofReal
            (Real.exp
              ((c a : ℝ) *
                (Real.log ((μ : Measure S) {a}).toReal - Real.log ((ν : Measure S) {a}).toReal))) *
            ((ν : Measure S) {a}) ^ c a
          = ENNReal.ofReal
              ((((μ : Measure S) {a}).toReal / ((ν : Measure S) {a}).toReal) ^ c a) *
              ((ν : Measure S) {a}) ^ c a := by
                rw [hexp]
        _ = (ENNReal.ofReal
              (((μ : Measure S) {a}).toReal / ((ν : Measure S) {a}).toReal)) ^ c a *
              ((ν : Measure S) {a}) ^ c a := by
                rw [ENNReal.ofReal_pow]
                positivity
        _ = (((μ : Measure S) {a} / (ν : Measure S) {a}) ^ c a) * ((ν : Measure S) {a}) ^ c a := by
                rw [hratio]
        _ = (((μ : Measure S) {a} / (ν : Measure S) {a}) * (ν : Measure S) {a}) ^ c a := by
                rw [← mul_pow]
        _ = ((μ : Measure S) {a}) ^ c a := by
                congr 1
                exact ENNReal.div_mul_cancel hνatom_ne_zero (hνatom_ne_top a)
  -- Proof comment: rewrite the global exponential factor as a finite product and then cancel
  -- each atomwise ratio against the corresponding `ν`-mass power.
  calc
    ENNReal.ofReal
        (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal)) *
        ∏ a : S, ((ν : Measure S) {a}) ^ c a
      = (∏ a : S,
          ENNReal.ofReal
            (Real.exp
              ((c a : ℝ) *
                (Real.log ((μ : Measure S) {a}).toReal -
                  Real.log ((ν : Measure S) {a}).toReal)))) *
          ∏ a : S, ((ν : Measure S) {a}) ^ c a := by
            rw [hexponent, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
            intro a ha
            exact Real.exp_nonneg _
    _ = ∏ a : S,
          (ENNReal.ofReal
              (Real.exp
                ((c a : ℝ) *
                  (Real.log ((μ : Measure S) {a}).toReal -
                    Real.log ((ν : Measure S) {a}).toReal))) *
            ((ν : Measure S) {a}) ^ c a) := by
            rw [Finset.prod_mul_distrib]
    _ = ∏ a : S, ((μ : Measure S) {a}) ^ c a := by
            refine Finset.prod_congr rfl ?_
            intro a ha
            exact hfactor a

/-- Helper for Lemma 23.12: once the KL divergence is finite, the real exponential factor agrees
with the `EReal.exp` surface used in the statement. -/
private theorem ennrealExp_eq_erealExp_negNatMulKlDiv
    {μ ν : ProbabilityMeasure S} {n : ℕ}
    (hkl_ne_top : klDiv (ν : Measure S) (μ : Measure S) ≠ ⊤) :
    ENNReal.ofReal
        (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal)) =
      EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
  calc
    ENNReal.ofReal
        (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal))
      = EReal.exp ((-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal : ℝ) : EReal) := by
          rw [EReal.exp_coe]
    _ = EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
          congr 1
          rw [← EReal.coe_ennreal_toReal hkl_ne_top]
          norm_num [EReal.coe_mul]

/-- Helper for Lemma 23.12: on the absolutely continuous branch, the exact `μ`-mass of a realized
empirical histogram is the self-law mass times `exp (-n * klDiv)`. -/
private theorem empiricalDistributionProbability_eq_selfProbability_mul_expNegKl
    [Fintype S] [DecidableEq S] [MeasurableSingletonClass S]
    {μ ν : ProbabilityMeasure S} {n : ℕ} {x : Fin n → S}
    (hx : x ∈ empiricalDistributionEvent n ν)
    (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    empiricalDistributionProbability μ n ν =
      empiricalDistributionProbability ν n ν *
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
  obtain ⟨hn, hcount⟩ := mem_empiricalDistributionEvent_iff.mp hx
  have hkl_ne_top : klDiv (ν : Measure S) (μ : Measure S) ≠ ⊤ := by
    rw [klDiv_eq_sum_gapSeriesTerm_of_absolutelyContinuous (μ := μ) (ν := ν) h_ac]
    simpa using
      (ENNReal.sum_ne_top).2 (fun a (_ : a ∈ (Finset.univ : Finset S)) ↦
        (ENNReal.ofReal_ne_top :
          ENNReal.ofReal
              (((μ : Measure S) {a}).toReal *
                klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) ≠ ⊤))
  -- Proof comment: rewrite both exact histogram masses with the same multinomial coefficient,
  -- use the KL product identity to swap the singleton products, and then convert the
  -- exponential factor to the `EReal.exp` surface from the statement.
  calc
    empiricalDistributionProbability μ n ν
      = (Nat.multinomial Finset.univ
          (fun i : Fin (Fintype.card S) ↦
            empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
          ∏ a : S, ((μ : Measure S) {a}) ^ empiricalCount n x a := by
            simpa using
              empiricalDistributionProbability_eq_multinomialMass_prod_singleton
                (μ := μ) (ν := ν) (x := x) hx
    _ = (Nat.multinomial Finset.univ
          (fun i : Fin (Fintype.card S) ↦
            empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) *
          (ENNReal.ofReal
              (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal)) *
            ∏ a : S, ((ν : Measure S) {a}) ^ empiricalCount n x a) := by
            refine congrArg (fun t : ENNReal ↦
              (Nat.multinomial Finset.univ
                (fun i : Fin (Fintype.card S) ↦
                  empiricalCount n x ((Fintype.equivFin S).symm i)) : ENNReal) * t) ?_
            simpa using
              (singletonMassProduct_eq_expNegKlFactor
                (μ := μ) (ν := ν) (n := n) (c := fun a : S ↦ empiricalCount n x a)
                hn hcount h_ac).symm
    _ = ENNReal.ofReal
          (Real.exp (-(n : ℝ) * (klDiv (ν : Measure S) (μ : Measure S)).toReal)) *
          empiricalDistributionProbability ν n ν := by
            rw [empiricalDistributionProbability_eq_multinomialMass_prod_singleton
              (μ := ν) (ν := ν) (x := x) hx]
            ac_rfl
    _ = empiricalDistributionProbability ν n ν *
          EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
            rw [mul_comm,
              ennrealExp_eq_erealExp_negNatMulKlDiv (μ := μ) (ν := ν) (n := n) hkl_ne_top]

-- Proof sketch: count the words with empirical law `ν` by multinomial coefficients, rewrite the
-- common product weight as `exp (-n * H(ν | μ))`, then bound the multinomial multiplicity between
-- `empiricalLowerPrefactor n * exp (n * H(ν))` and `exp (n * H(ν))`.
/-- Lemma 23.12: for every `n` and every empirical distribution `ν ∈ E_n`, the probability that an
i.i.d. sample with one-letter law `μ` has empirical distribution `ν` is bounded below by
`(n + 1)^{-#S} exp (-n H(ν | μ))` and above by `exp (-n H(ν | μ))`, where the relative entropy is
the canonical Kullback-Leibler divergence `klDiv (ν : Measure S) (μ : Measure S)`. -/
theorem empiricalDistributionProbability_sanov_bounds
    [Fintype S] [MeasurableSingletonClass S]
    (μ : ProbabilityMeasure S) (n : ℕ) (ν : ProbabilityMeasure S)
    (hν : ν ∈ empiricalDistributions n) :
    empiricalLowerPrefactor S n *
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) ≤
      empiricalDistributionProbability μ n ν ∧
      empiricalDistributionProbability μ n ν ≤
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
  classical
  obtain ⟨x, hx⟩ := hν
  by_cases h_ac : (ν : Measure S) ≪ (μ : Measure S)
  · have hratio :=
        empiricalDistributionProbability_eq_selfProbability_mul_expNegKl
          (μ := μ) (ν := ν) (x := x) hx h_ac
    have hselfLower :
        empiricalLowerPrefactor S n ≤ empiricalDistributionProbability ν n ν :=
      selfEmpiricalDistributionProbability_ge_lowerPrefactor (S := S) (x := x) hx
    have hselfUpper : empiricalDistributionProbability ν n ν ≤ 1 := by
      rw [empiricalDistributionProbability_def]
      calc
        (((ProbabilityMeasure.pi fun _ : Fin n ↦ ν : ProbabilityMeasure (Fin n → S)) :
            Measure (Fin n → S)) (empiricalDistributionEvent n ν))
          ≤ (((ProbabilityMeasure.pi fun _ : Fin n ↦ ν : ProbabilityMeasure (Fin n → S)) :
              Measure (Fin n → S)) Set.univ) := by
                exact measure_mono (by intro y hy; simp)
        _ = 1 := by simp
    constructor
    · calc
        empiricalLowerPrefactor S n *
            EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal)))
          ≤ empiricalDistributionProbability ν n ν *
              EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
                exact mul_le_mul_right' hselfLower _
        _ = empiricalDistributionProbability μ n ν := by
              simpa [mul_comm] using hratio.symm
    · calc
        empiricalDistributionProbability μ n ν
          = empiricalDistributionProbability ν n ν *
              EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
                simpa [mul_comm] using hratio
        _ ≤ 1 *
              EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
                exact mul_le_mul_right' hselfUpper _
        _ = EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
              simp
  · have hprob_zero :
        empiricalDistributionProbability μ n ν = 0 :=
      empiricalDistributionProbability_eq_zero_of_not_absolutelyContinuous (μ := μ) hx h_ac
    obtain ⟨hn, _⟩ := mem_empiricalDistributionEvent_iff.mp hx
    have hkl_top : klDiv (ν : Measure S) (μ : Measure S) = ⊤ := by
      rw [klDiv_eq_lintegral_klFun]
      simp [h_ac]
    have hMulTop : (n : EReal) * (⊤ : EReal) = ⊤ := by
      have hnpos : (0 : EReal) < (n : EReal) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      exact EReal.mul_top_of_pos hnpos
    have hExpZero :
        EReal.exp (-((n : EReal) * (klDiv (ν : Measure S) (μ : Measure S) : EReal))) = 0 := by
      rw [hkl_top]
      change EReal.exp (-((n : EReal) * (⊤ : EReal))) = 0
      rw [hMulTop]
      change EReal.exp (⊥ : EReal) = 0
      rfl
    constructor
    · simpa [hprob_zero, hExpZero]
    · simpa [hprob_zero, hExpZero]

end MeasureLayer

end ProbabilityTheory
