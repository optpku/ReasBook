/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter InformationTheory MeasureTheory
open scoped BigOperators Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {S : Type v} [MeasurableSpace S]

/-- The underlying measure of the empirical distribution of the first `n + 1` sample values is the
normalized sum of the Dirac masses at those values. This is the Chapter 23 sequence-indexed
specialization of the owner theorem `empiricalDistribution_toMeasure` from Definition 12.25. -/
theorem empiricalMeasure_toMeasure (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) :
    (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure S) =
      ((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ i : Fin (n + 1), Measure.dirac (X i ω) := by
  simpa [Nat.succPNat, Nat.succ_eq_add_one] using
    (@empiricalDistribution_toMeasure Ω S _ _ (Nat.succPNat n) (fun i ↦ X i) ω)

section FiniteAlphabet

variable [TopologicalSpace S] [DiscreteTopology S] [BorelSpace S]

-- Proof sketch: on a finite discrete alphabet, each singleton mass of `empiricalMeasure X n` is a
-- finite average of measurable indicator functions of the events `{ω | X i ω = a}`; measurability
-- of the probability-measure-valued map follows from this finite coordinate description.
/-- The empirical-measure map is measurable for measurable coordinate maps into a finite discrete
alphabet. -/
theorem measurable_empiricalMeasure [Fintype S]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)) := by
  have hPrefix :
      Measurable (fun ω : Ω ↦ fun i : Fin (Nat.succPNat n) ↦ X i ω) := by
    -- Proof comment: the finite prefix map is measurable coordinatewise, so the whole tuple map
    -- is measurable into the finite product.
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simpa using hX (i : ℕ)
  have hTuple :
      Measurable (fun x : Fin (Nat.succPNat n) → S ↦ empiricalDistributionTuple x) := by
    -- Proof comment: on the finite discrete tuple space, every map into `ProbabilityMeasure S`
    -- is measurable.
    exact measurable_of_finite _
  -- Proof comment: the empirical measure is the composition of the measurable prefix tuple map
  -- with the deterministic tuple-level empirical-distribution constructor.
  simpa [empiricalDistributionTuple] using
    hTuple.comp hPrefix

/-- The law of the empirical measure `ξ_n(X)` under the reference probability measure `P`. -/
noncomputable def empiricalMeasureLaw [Fintype S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    ProbabilityMeasure (ProbabilityMeasure S) :=
  ProbabilityMeasure.map ⟨P, inferInstance⟩
    (measurable_empiricalMeasure X hX n).aemeasurable

-- Proof sketch: unfold `empiricalMeasureLaw`; it is defined as the pushforward of `P` by the
-- empirical-measure map `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)`.
/-- Expanding `empiricalMeasureLaw P X hX n` gives the pushforward of `P` by the empirical-measure
map `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)`. -/
theorem empiricalMeasureLaw_def [Fintype S] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    empiricalMeasureLaw P X hX n =
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (measurable_empiricalMeasure X hX n).aemeasurable := by
  -- Proof comment: `empiricalMeasureLaw` is defined as this pushforward, so unfolding the
  -- definition closes the goal.
  rfl

/-- Helper for Theorem 23.13: every finite prefix of the i.i.d. sample sequence has the product
law of the common one-letter marginal `μ`. -/
private theorem iidPrefixHasLawPi [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (n : ℕ) :
    HasLaw (fun ω : Ω ↦ fun i : Fin (n + 1) ↦ X i.1 ω)
      (Measure.pi fun _ : Fin (n + 1) ↦ (μ : Measure S)) P := by
  have hX0Law : HasLaw (X 0) (μ : Measure S) P := by
    -- Proof comment: the common one-letter law is exactly the pushforward of `P` by `X 0`.
    refine ⟨(hX 0).aemeasurable, ?_⟩
    simpa using congrArg (fun ν : ProbabilityMeasure S ↦ (ν : Measure S)) hμ
  have hPrefixIndep : iIndepFun (fun i : Fin (n + 1) ↦ X i.1) P := by
    -- Proof comment: independence of the full sequence restricts to the first `n + 1`
    -- coordinates.
    simpa using hindep.precomp Fin.val_injective
  have hPrefixLaw : ∀ i : Fin (n + 1), HasLaw (fun ω ↦ X i.1 ω) (μ : Measure S) P := by
    -- Proof comment: identical distribution transfers the law of `X 0` to each prefix
    -- coordinate.
    intro i
    exact (hident i.1).symm.hasLaw hX0Law
  refine ⟨aemeasurable_pi_lambda _ fun i ↦ (hPrefixLaw i).aemeasurable, ?_⟩
  -- Proof comment: finite independence identifies the joint pushforward with the product of the
  -- one-coordinate pushforwards.
  have hMap :
      Measure.map (fun ω : Ω ↦ fun i : Fin (n + 1) ↦ X i.1 ω) P =
        Measure.pi fun i : Fin (n + 1) ↦ Measure.map (fun ω ↦ X i.1 ω) P := by
    simpa using
      (iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hPrefixLaw i).aemeasurable).1 hPrefixIndep
  rw [hMap]
  congr 1
  funext i
  exact (hPrefixLaw i).map_eq

/-- Helper for Theorem 23.13: the deterministic empirical distribution of a tuple records each
singleton mass as the normalized empirical count of that symbol. -/
private theorem empiricalDistributionTuple_apply_singleton [Fintype S] [DecidableEq S]
    (n : ℕ) (x : Fin (n + 1) → S) (a : S) :
    (empiricalDistributionTuple (n := Nat.succPNat n) x : Measure S) {a} =
      ((empiricalCount (n + 1) x a : ℕ) : ENNReal) / ((n + 1 : ℕ) : ENNReal) := by
  have hCount :
      (∑ i : Fin (n + 1), (Measure.dirac (x i)) {a}) = empiricalCount (n + 1) x a := by
    -- Proof comment: the singleton mass of each Dirac term is the indicator of the equality
    -- `x i = a`, so summing those masses counts the matching coordinates.
    simpa [Pi.single_apply, empiricalCount, Fintype.card_subtype] using
      (Finset.sum_boole (s := Finset.univ) (p := fun i : Fin (n + 1) ↦ x i = a))
  have hMeasure :
      (empiricalDistributionTuple (n := Nat.succPNat n) x : Measure S) =
        (((n + 1 : ℕ) : ENNReal)⁻¹ • ∑ i : Fin (n + 1), Measure.dirac (x i)) := by
    -- Proof comment: specialize the Chapter 12 averaged-Dirac formula to the deterministic tuple
    -- `x`.
    simpa [empiricalDistributionTuple, Nat.succPNat, Nat.succ_eq_add_one] using
      (empiricalDistribution_toMeasure (Nat.succPNat n) (fun i (_ : Unit) ↦ x i) ())
  rw [hMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  -- Proof comment: after evaluating the finite sum on `{a}`, the remaining identity is exactly
  -- the empirical-count formula `hCount`.
  rw [hCount]
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm]

/-- Helper for Theorem 23.13: for words of length `n + 1`, the Chapter 23 empirical-distribution
event coincides with equality to the tuple-level empirical distribution. -/
private theorem mem_empiricalDistributionEvent_succ_iff [Fintype S] [DecidableEq S]
    {n : ℕ} {ν : ProbabilityMeasure S} {x : Fin (n + 1) → S} :
    x ∈ empiricalDistributionEvent (n + 1) ν ↔
      empiricalDistributionTuple (n := Nat.succPNat n) x = ν := by
  constructor
  · intro hx
    apply ProbabilityMeasure.toMeasure_injective
    have hPmf :
        ((ν : Measure S).toPMF) =
          ((empiricalDistributionTuple (n := Nat.succPNat n) x : Measure S).toPMF) := by
      ext a
      obtain ⟨_, hCount⟩ := mem_empiricalDistributionEvent_iff.mp hx
      rw [Measure.toPMF_apply, Measure.toPMF_apply, hCount a]
      exact (empiricalDistributionTuple_apply_singleton (n := n) x a).symm
    simpa [Measure.toPMF_toMeasure] using (congrArg PMF.toMeasure hPmf).symm
  · intro hTuple
    refine mem_empiricalDistributionEvent_iff.mpr ?_
    refine ⟨Nat.succ_ne_zero n, ?_⟩
    intro a
    -- Proof comment: after identifying `ν` with the tuple empirical law, the singleton masses are
    -- exactly the normalized empirical counts from the previous helper.
    simpa [hTuple] using empiricalDistributionTuple_apply_singleton (n := n) x a

/-- Helper for Theorem 23.13: evaluating `empiricalMeasureLaw` on a measurable set transports the
problem to the product law on the first `n + 1` coordinates. -/
private theorem empiricalMeasureLaw_apply_eq_productLaw_preimage
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (s : Set (ProbabilityMeasure S)) (hs : MeasurableSet s) (n : ℕ) :
    ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s) =
      ((Measure.pi fun _ : Fin (n + 1) ↦ (μ : Measure S)))
        {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s} := by
  have hPrefix :
      Measurable (fun ω : Ω ↦ fun i : Fin (n + 1) ↦ X i.1 ω) := by
    -- Proof comment: the tuple of the first `n + 1` coordinates is measurable coordinatewise.
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    simpa using hX i.1
  have hTuple :
      Measurable (fun x : Fin (n + 1) → S ↦ empiricalDistributionTuple (n := Nat.succPNat n) x) := by
    -- Proof comment: the tuple space is finite, so every function out of it is measurable.
    exact measurable_of_finite _
  have hTarget :
      MeasurableSet {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s} :=
    hTuple hs
  have hLaw :=
    iidPrefixHasLawPi (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ n
  have hPrefixApply :
      P ((fun ω : Ω ↦ fun i : Fin (n + 1) ↦ X i.1 ω) ⁻¹'
          {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s}) =
        ((Measure.pi fun _ : Fin (n + 1) ↦ (μ : Measure S)))
          {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s} := by
    -- Proof comment: transport the measurable tuple event along the prefix law identified in
    -- `iidPrefixHasLawPi`.
    simpa [Measure.map_apply hPrefix hTarget] using
      congrArg
        (fun m : Measure (Fin (n + 1) → S) ↦
          m {x : Fin (n + 1) → S |
            empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s})
        hLaw.map_eq
  -- Route correction: move the law comparison to tuple preimages instead of codomain singletons
  -- in `ProbabilityMeasure S`; that avoids the measurable-singleton bottleneck entirely.
  calc
    ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s)
        = P ((fun ω : Ω ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) ⁻¹' s) := by
            rw [empiricalMeasureLaw_def]
            simpa using
              (ProbabilityMeasure.map_apply'
                ⟨P, inferInstance⟩
                ((measurable_empiricalMeasure X hX n).aemeasurable)
                hs)
    _ = P ((fun ω : Ω ↦ fun i : Fin (n + 1) ↦ X i.1 ω) ⁻¹'
          {x : Fin (n + 1) → S |
            empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s}) := by
            rfl
    _ = ((Measure.pi fun _ : Fin (n + 1) ↦ (μ : Measure S)))
          {x : Fin (n + 1) → S |
            empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s} := hPrefixApply

/-- Helper for Theorem 23.13: the number of empirical distributions realized by words of length
`n + 1` is bounded by the polynomial histogram count `(n + 2) ^ #S`. -/
private theorem finiteRealizedEmpiricalDistributions [Fintype S]
    (n : ℕ) :
    Finite {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} := by
  classical
  let witness : {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} → Fin (n + 1) → S :=
    fun ν ↦ Classical.choose ((mem_empiricalDistributions_iff (n + 1) ν.1).mp ν.2)
  let encodedCounts :
      {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} →
        {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} :=
    fun ν ↦
      ⟨fun i ↦ empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i), by
        have hReindex :
            (∑ a : S, empiricalCount (n + 1) (witness ν) a) =
              ∑ i : Fin (Fintype.card S),
                empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i) := by
          refine Fintype.sum_equiv (Fintype.equivFin S)
            (fun a : S ↦ empiricalCount (n + 1) (witness ν) a)
            (fun i : Fin (Fintype.card S) ↦
              empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i)) ?_
          intro a
          simp
        calc
          ∑ i : Fin (Fintype.card S),
              empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i)
              = ∑ a : S, empiricalCount (n + 1) (witness ν) a := by
                  simpa using hReindex.symm
          _ = n + 1 := sum_empiricalCount (n + 1) (witness ν)⟩
  have hInjective : Function.Injective encodedCounts := by
    intro ν₁ ν₂ hCounts
    apply Subtype.ext
    have hVal :
        (encodedCounts ν₁).1 = (encodedCounts ν₂).1 := congrArg Subtype.val hCounts
    have hx₁ :
        witness ν₁ ∈ empiricalDistributionEvent (n + 1) ν₁.1 :=
      Classical.choose_spec ((mem_empiricalDistributions_iff (n + 1) ν₁.1).mp ν₁.2)
    have hx₂ :
        witness ν₂ ∈ empiricalDistributionEvent (n + 1) ν₂.1 :=
      Classical.choose_spec ((mem_empiricalDistributions_iff (n + 1) ν₂.1).mp ν₂.2)
    have hTuple :
        empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₁) =
          empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) := by
      apply ProbabilityMeasure.toMeasure_injective
      have hPmf :
          (((empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₁) :
              ProbabilityMeasure S) : Measure S).toPMF) =
            (((empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) :
              ProbabilityMeasure S) : Measure S).toPMF) := by
        ext a
        have hCountEq :
            empiricalCount (n + 1) (witness ν₁) a = empiricalCount (n + 1) (witness ν₂) a := by
          have hCoord :=
            congrArg
              (fun k : Fin (Fintype.card S) → ℕ ↦ k (Fintype.equivFin S a))
              hVal
          simpa [encodedCounts, witness] using hCoord
        rw [Measure.toPMF_apply, Measure.toPMF_apply,
          empiricalDistributionTuple_apply_singleton (n := n) (witness ν₁) a,
          empiricalDistributionTuple_apply_singleton (n := n) (witness ν₂) a,
          hCountEq]
      simpa [Measure.toPMF_toMeasure] using congrArg PMF.toMeasure hPmf
    calc
      ν₁.1 = empiricalDistributionTuple (witness ν₁) := by
        simpa using (mem_empiricalDistributionEvent_succ_iff.mp hx₁).symm
      _ = empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) := hTuple
      _ = ν₂.1 := mem_empiricalDistributionEvent_succ_iff.mp hx₂
  let histogramEmbedding :
      {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} →
        Fin (Fintype.card S) → Fin (n + 2) :=
    fun ℓ i ↦
      ⟨ℓ.1 i, by
        have hle : ℓ.1 i ≤ ∑ j : Fin (Fintype.card S), ℓ.1 j := by
          simpa using
            (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (by simp : i ∈ Finset.univ))
        exact Nat.lt_succ_iff.mpr (hle.trans (by simpa [ℓ.2]))⟩
  have hHistogramEmbedding :
      Function.Injective histogramEmbedding := by
    intro ℓ₁ ℓ₂ hEq
    apply Subtype.ext
    funext i
    simpa [histogramEmbedding] using congrArg Fin.val (congrFun hEq i)
  letI : Finite {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} :=
    Finite.of_injective histogramEmbedding hHistogramEmbedding
  -- Proof comment: realized empirical laws inject into the finite family of histograms on `S`.
  exact Finite.of_injective encodedCounts hInjective

/-- Helper for Theorem 23.13: the number of empirical distributions realized by words of length
`n + 1` is bounded by the polynomial histogram count `(n + 2) ^ #S`. -/
private theorem empiricalDistributionsCard_le [Fintype S]
    (n : ℕ) :
    Nat.card {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} ≤
      (n + 2) ^ Fintype.card S := by
  classical
  let witness : {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} → Fin (n + 1) → S :=
    fun ν ↦ Classical.choose ((mem_empiricalDistributions_iff (n + 1) ν.1).mp ν.2)
  let encodedCounts :
      {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)} →
        {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} :=
    fun ν ↦
      ⟨fun i ↦ empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i), by
        have hReindex :
            (∑ a : S, empiricalCount (n + 1) (witness ν) a) =
              ∑ i : Fin (Fintype.card S),
                empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i) := by
          refine Fintype.sum_equiv (Fintype.equivFin S)
            (fun a : S ↦ empiricalCount (n + 1) (witness ν) a)
            (fun i : Fin (Fintype.card S) ↦
              empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i)) ?_
          intro a
          simp
        calc
          ∑ i : Fin (Fintype.card S),
              empiricalCount (n + 1) (witness ν) ((Fintype.equivFin S).symm i)
              = ∑ a : S, empiricalCount (n + 1) (witness ν) a := by
                  simpa using hReindex.symm
          _ = n + 1 := sum_empiricalCount (n + 1) (witness ν)⟩
  have hInjective : Function.Injective encodedCounts := by
    intro ν₁ ν₂ hCounts
    apply Subtype.ext
    have hVal :
        (encodedCounts ν₁).1 = (encodedCounts ν₂).1 := congrArg Subtype.val hCounts
    have hx₁ :
        witness ν₁ ∈ empiricalDistributionEvent (n + 1) ν₁.1 :=
      Classical.choose_spec ((mem_empiricalDistributions_iff (n + 1) ν₁.1).mp ν₁.2)
    have hx₂ :
        witness ν₂ ∈ empiricalDistributionEvent (n + 1) ν₂.1 :=
      Classical.choose_spec ((mem_empiricalDistributions_iff (n + 1) ν₂.1).mp ν₂.2)
    have hTuple :
        empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₁) =
          empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) := by
      apply ProbabilityMeasure.toMeasure_injective
      have hPmf :
          (((empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₁) :
              ProbabilityMeasure S) : Measure S).toPMF) =
            (((empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) :
              ProbabilityMeasure S) : Measure S).toPMF) := by
        ext a
        have hCountEq :
            empiricalCount (n + 1) (witness ν₁) a = empiricalCount (n + 1) (witness ν₂) a := by
          have hCoord :=
            congrArg
              (fun k : Fin (Fintype.card S) → ℕ ↦ k (Fintype.equivFin S a))
              hVal
          simpa [encodedCounts, witness] using hCoord
        rw [Measure.toPMF_apply, Measure.toPMF_apply,
          empiricalDistributionTuple_apply_singleton (n := n) (witness ν₁) a,
          empiricalDistributionTuple_apply_singleton (n := n) (witness ν₂) a,
          hCountEq]
      simpa [Measure.toPMF_toMeasure] using congrArg PMF.toMeasure hPmf
    calc
      ν₁.1 = empiricalDistributionTuple (witness ν₁) := by
        simpa using (mem_empiricalDistributionEvent_succ_iff.mp hx₁).symm
      _ = empiricalDistributionTuple (n := Nat.succPNat n) (witness ν₂) := hTuple
      _ = ν₂.1 := mem_empiricalDistributionEvent_succ_iff.mp hx₂
  let histogramEmbedding :
      {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} →
        Fin (Fintype.card S) → Fin (n + 2) :=
    fun ℓ i ↦
      ⟨ℓ.1 i, by
        have hle : ℓ.1 i ≤ ∑ j : Fin (Fintype.card S), ℓ.1 j := by
          simpa using
            (Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (by simp : i ∈ Finset.univ))
        exact Nat.lt_succ_iff.mpr (hle.trans (by simpa [ℓ.2]))⟩
  have hHistogramEmbedding :
      Function.Injective histogramEmbedding := by
    intro ℓ₁ ℓ₂ hEq
    apply Subtype.ext
    funext i
    simpa [histogramEmbedding] using congrArg Fin.val (congrFun hEq i)
  letI : Finite {ℓ : Fin (Fintype.card S) → ℕ // ∑ i, ℓ i = n + 1} :=
    Finite.of_injective histogramEmbedding hHistogramEmbedding
  -- Proof comment: inject realized empirical distributions into the encoded histogram family and
  -- apply the existing polynomial cardinality bound from Lemma 23.12.
  exact
    le_trans
      (Nat.card_le_card_of_injective encodedCounts hInjective)
      (by simpa using encodedHistogramFamily_card_le (Fintype.card S) (n + 1))

/-- Helper for Theorem 23.13: the singleton mass of a probability measure varies continuously in
the weak topology on a finite discrete alphabet. -/
private theorem continuous_singletonMassReal [Fintype S] (a : S) :
    Continuous fun ν : ProbabilityMeasure S ↦ (ν : Measure S).real {a} := by
  classical
  let f : BoundedContinuousFunction S ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun x : S ↦ if x = a then 1 else 0) 1 <| by
        intro x
        by_cases hx : x = a
        · simpa [hx]
        · simpa [hx]
  have hEq :
      (fun ν : ProbabilityMeasure S ↦ (ν : Measure S).real {a}) =
        fun ν : ProbabilityMeasure S ↦ ∫ x, f x ∂(ν : Measure S) := by
    funext ν
    -- Proof comment: on a finite discrete alphabet, the integral is the finite weighted sum of
    -- point masses, and only the singleton `{a}` contributes.
    rw [MeasureTheory.integral_fintype (μ := (ν : Measure S)) (f := fun x : S ↦ f x)
      (BoundedContinuousFunction.integrable (ν : Measure S) f)]
    simp [f, smul_eq_mul]
  rw [hEq]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

/-- Helper for Theorem 23.13: coordinatewise convergence of singleton masses determines weak
convergence of probability measures on a finite discrete alphabet. -/
private theorem tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto
    [Fintype S]
    {νn : ℕ → ProbabilityMeasure S} {ν : ProbabilityMeasure S}
    (hνn : ∀ a : S,
      Tendsto (fun n ↦ (νn n : Measure S).real {a}) atTop
        (𝓝 ((ν : Measure S).real {a}))) :
    Tendsto νn atTop (𝓝 ν) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hIntegral (ρ : ProbabilityMeasure S) :
      ∫ x, f x ∂(ρ : Measure S) = ∑ a : S, (ρ : Measure S).real {a} * f a := by
    -- Proof comment: on a finite discrete alphabet, the Bochner integral is the finite weighted
    -- sum of the singleton masses.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := (ρ : Measure S)) (f := fun x : S ↦ f x)
        (BoundedContinuousFunction.integrable (ρ : Measure S) f))
  rw [show (fun n ↦ ∫ x, f x ∂(νn n : Measure S)) =
      fun n ↦ ∑ a : S, (νn n : Measure S).real {a} * f a by
        funext n
        exact hIntegral (νn n)]
  rw [show ∫ x, f x ∂(ν : Measure S) =
      ∑ a : S, (ν : Measure S).real {a} * f a by
        exact hIntegral ν]
  -- Proof comment: every test integral is a finite sum of convergent singleton-mass coordinates.
  exact tendsto_finset_sum _ fun a _ ↦ by
    simpa [mul_comm] using (hνn a).const_mul (f a)

/-- Helper for Theorem 23.13: the coordinate mass function in the discrete KL expansion is never
infinite once the total mass is at most `1`. -/
private theorem pmfCoordinate_neTop_of_tsum_le_one {E : Type*} (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Proof comment: each coordinate is bounded by the total mass and hence by `1`.
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hq_le_one ENNReal.one_lt_top)

/-- Helper for Theorem 23.13: a discrete PMF is the comparison measure
`Measure.count.withDensity q` weighted by the density `p / q` on the support of `p`. -/
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
          have hqTop : q e ≠ ⊤ := pmfCoordinate_neTop_of_tsum_le_one q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hqTop, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · exact measurable_of_finite q
      · exact measurable_of_finite (fun e ↦ (p e : ENNReal) / q e)
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Theorem 23.13: on a discrete finite alphabet, the KL divergence against a
comparison mass function is the sum of the pointwise KL terms. -/
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
    -- Proof comment: replace the Radon-Nikodym derivative by its explicit discrete density.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hqTop : q e ≠ ⊤ := pmfCoordinate_neTop_of_tsum_le_one q hq e
    have hqReal_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) =
          ENNReal.ofReal (q e).toReal * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
            rw [ENNReal.ofReal_toReal hqTop]
      _ = ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
            rw [← ENNReal.ofReal_mul hqReal_nonneg]
  · exact measurable_of_finite q
  · exact measurable_of_finite (fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)))

/-- Helper for Theorem 23.13: the textbook singleton KL summand written with real singleton
masses agrees with the discrete `q * klFun (p / q)` term. -/
private def singletonKlTerm [Fintype S] (μ ν : ProbabilityMeasure S) (a : S) : ENNReal :=
  ENNReal.ofReal
    (((μ : Measure S).real {a}) * klFun (((ν : Measure S).real {a}) / ((μ : Measure S).real {a})))

/-- Helper for Theorem 23.13: on the absolutely continuous branch, the discrete KL summand rewrites
to the public singleton-mass term. -/
private theorem singletonKlTerm_eq_gapSeriesTerm_of_absolutelyContinuous
    [Fintype S] {μ ν : ProbabilityMeasure S} (h_ac : (ν : Measure S) ≪ (μ : Measure S)) (a : S) :
    ENNReal.ofReal
        (((μ : Measure S) {a}).toReal *
          klFun ((((ν : Measure S) {a}) / ((μ : Measure S) {a})).toReal)) =
      singletonKlTerm μ ν a := by
  by_cases hμa : (μ : Measure S) {a} = 0
  · have hνa : (ν : Measure S) {a} = 0 := h_ac hμa
    -- Proof comment: absolute continuity forces the numerator to vanish on `μ`-null atoms.
    simp [singletonKlTerm, hμa, hνa]
  · -- Proof comment: on positive `μ`-atoms, `ENNReal.toReal_div` converts the ratio to ordinary
    -- real division.
    simp [singletonKlTerm, Measure.real, ENNReal.toReal_div]

/-- Helper for Theorem 23.13: absolute continuity is enough to rewrite the finite-alphabet KL
divergence as the sum of the singleton KL terms. -/
private theorem klDiv_eq_sum_singletonKlTerm_of_absolutelyContinuous
    [Fintype S] (μ ν : ProbabilityMeasure S) (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    klDiv (ν : Measure S) (μ : Measure S) = ∑ a : S, singletonKlTerm μ ν a := by
  classical
  let p : PMF S := (ν : Measure S).toPMF
  let q : S → ENNReal := fun a ↦ (μ : Measure S) {a}
  have hq : (∑' a : S, q a) ≤ 1 := by
    -- Proof comment: the comparison singleton masses are exactly the PMF weights of `μ`, whose
    -- total mass is `1`.
    exact le_of_eq (by simpa [q, Measure.toPMF_apply] using (PMF.tsum_coe ((μ : Measure S).toPMF)))
  have hnozero : ∀ a ∈ p.support, q a ≠ 0 := by
    -- Proof comment: absolute continuity forces every atom in the support of `ν` to lie over a
    -- positive `μ`-atom.
    intro a ha
    intro hqa
    have hνa : (ν : Measure S) {a} = 0 := h_ac hqa
    exact (PMF.mem_support_iff p a).1 ha (by simpa [p, Measure.toPMF_apply] using hνa)
  have hqMeasure : Measure.count.withDensity q = (μ : Measure S) := by
    -- Proof comment: the counting measure with singleton weights `q a = μ {a}` reconstructs the
    -- original finite discrete probability measure `μ`.
    ext s hs
    rw [withDensity_apply _ hs, ← lintegral_indicator hs q, lintegral_count]
    simpa [q, Measure.toPMF_apply] using
      (((μ : Measure S).toPMF).toMeasure_apply_fintype s).symm
  -- Proof comment: the PMF/counting-measure KL expansion matches the public singleton-mass
  -- formula term by term.
  calc
    klDiv (ν : Measure S) (μ : Measure S)
      = ∑' a : S, ENNReal.ofReal ((q a).toReal * klFun (((p a : ENNReal) / q a).toReal)) := by
          simpa [p, q, Measure.toPMF_apply, hqMeasure] using
            discreteKlDiv_eq_gapSeries p q hq hnozero
    _ = ∑ a : S, singletonKlTerm μ ν a := by
          rw [tsum_fintype]
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [p, q, Measure.toPMF_apply] using
            singletonKlTerm_eq_gapSeriesTerm_of_absolutelyContinuous (μ := μ) (ν := ν) h_ac a

/-- Helper for Theorem 23.13: the public singleton KL sum always gives a lower bound for the full
relative entropy. -/
private theorem sum_singletonKlTerm_le_klDiv [Fintype S]
    (μ ν : ProbabilityMeasure S) :
    (∑ a : S, singletonKlTerm μ ν a) ≤ klDiv (ν : Measure S) (μ : Measure S) := by
  by_cases h_ac : (ν : Measure S) ≪ (μ : Measure S)
  · rw [klDiv_eq_sum_singletonKlTerm_of_absolutelyContinuous μ ν h_ac]
  · have htop : klDiv (ν : Measure S) (μ : Measure S) = ⊤ := by
      rw [klDiv_eq_lintegral_klFun]
      simp [h_ac]
    simpa [htop]

/-- Helper for Theorem 23.13: each singleton KL term depends continuously on the underlying
probability measure. -/
private theorem continuous_singletonKlTerm [Fintype S]
    (μ : ProbabilityMeasure S) (a : S) :
    Continuous fun ν : ProbabilityMeasure S ↦ singletonKlTerm μ ν a := by
  -- Proof comment: `singletonKlTerm` is a fixed continuous real expression of the singleton-mass
  -- coordinate.
  unfold singletonKlTerm
  exact ENNReal.continuous_ofReal.comp <|
    continuous_const.mul <|
      continuous_klFun.comp <|
        (continuous_singletonMassReal (a := a)).div_const _

-- Proof sketch: `InformationTheory.klDiv` is the canonical relative entropy on measures, and on a
-- finite discrete alphabet it is lower semicontinuous in the weak topology on probability
-- measures.
/-- The relative-entropy rate function `ν ↦ klDiv ν μ` is lower semicontinuous on the space of
probability measures on a finite discrete alphabet. -/
theorem lowerSemicontinuous_relativeEntropyRate
    [Fintype S]
    (μ : ProbabilityMeasure S) :
    LowerSemicontinuous
      (fun ν : ProbabilityMeasure S ↦ klDiv (ν : Measure S) (μ : Measure S)) := by
  classical
  let g : ProbabilityMeasure S → ENNReal := fun ν ↦ ∑ a : S, singletonKlTerm μ ν a
  have hg_cont : Continuous g := by
    -- Proof comment: on a finite alphabet, the finite singleton KL sum is a finite sum of
    -- continuous coordinate terms.
    refine continuous_finset_sum _ fun a _ ↦ ?_
    simpa [g] using continuous_singletonKlTerm (μ := μ) a
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  refine isOpen_iff_mem_nhds.2 ?_
  intro ν hy
  by_cases h_ac : (ν : Measure S) ≪ (μ : Measure S)
  · have hEq : klDiv (ν : Measure S) (μ : Measure S) = g ν := by
      simpa [g] using klDiv_eq_sum_singletonKlTerm_of_absolutelyContinuous μ ν h_ac
    have hy' : y < g ν := by simpa [hEq] using hy
    have hMem : ν ∈ g ⁻¹' Set.Ioi y := by simpa [g] using hy'
    -- Proof comment: on the finite branch, the continuous singleton KL sum gives an open
    -- superlevel neighborhood, and this neighborhood sits inside the KL superlevel set because
    -- the sum is a global lower bound for `klDiv`.
    refine Filter.mem_of_superset ((hg_cont.lowerSemicontinuous.isOpen_preimage y).mem_nhds hMem) ?_
    intro ρ hρ
    exact lt_of_lt_of_le hρ (sum_singletonKlTerm_le_klDiv μ ρ)
  · obtain ⟨a, hμa, hνa⟩ :=
      exists_singleton_mass_witness_of_not_absolutelyContinuous μ ν h_ac
    have hkl_top : klDiv (ν : Measure S) (μ : Measure S) = ⊤ := by
      rw [klDiv_eq_lintegral_klFun]
      simp [h_ac]
    have hy_top : y < (⊤ : ENNReal) := by simpa [hkl_top] using hy
    have hνa_pos : 0 < (ν : Measure S).real {a} := by
      exact ENNReal.toReal_pos hνa (measure_ne_top _ _)
    have hMem :
        ν ∈ (fun ρ : ProbabilityMeasure S ↦ (ρ : Measure S).real {a}) ⁻¹' Set.Ioi 0 := by
      simpa using hνa_pos
    -- Proof comment: if a `μ`-null singleton keeps positive mass, absolute continuity still
    -- fails, so the KL divergence stays equal to `⊤` on that neighborhood.
    refine Filter.mem_of_superset
      (((continuous_singletonMassReal (a := a)).isOpen_preimage _ isOpen_Ioi).mem_nhds hMem) ?_
    intro ρ hρ
    have hρa_pos : 0 < (ρ : Measure S).real {a} := by simpa using hρ
    have hρa_ne : (ρ : Measure S) {a} ≠ 0 := by
      intro hρa_zero
      simpa [Measure.real, hρa_zero] using hρa_pos.ne'
    have hρ_not_ac : ¬ (ρ : Measure S) ≪ (μ : Measure S) := by
      intro hρ_ac
      exact hρa_ne (hρ_ac hμa)
    have hρ_top : klDiv (ρ : Measure S) (μ : Measure S) = ⊤ := by
      rw [klDiv_eq_lintegral_klFun]
      simp [hρ_not_ac]
    simpa [hρ_top] using hy_top

/-- Helper for Theorem 23.13: a single empirical distribution inside a measurable target set
already contributes to the empirical-measure law of that set. -/
private theorem empiricalDistributionProbability_le_empiricalMeasureLaw_of_mem
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (s : Set (ProbabilityMeasure S)) (hs : MeasurableSet s)
    {ν : ProbabilityMeasure S} (hνs : ν ∈ s) (n : ℕ) :
    empiricalDistributionProbability μ (n + 1) ν ≤
      ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s) := by
  classical
  let productLaw : Measure (Fin (n + 1) → S) :=
    ((ProbabilityMeasure.pi fun _ : Fin (n + 1) ↦ μ :
      ProbabilityMeasure (Fin (n + 1) → S)) : Measure (Fin (n + 1) → S))
  let targetSet : Set (Fin (n + 1) → S) :=
    {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s}
  have hEventSubset :
      empiricalDistributionEvent (n + 1) ν ⊆ targetSet := by
    intro x hx
    -- Proof comment: on the empirical-distribution event, the tuple empirical law is exactly `ν`,
    -- so membership of `ν` in `s` forces membership of the tuple in the target preimage.
    have hTuple : empiricalDistributionTuple (n := Nat.succPNat n) x = ν :=
      mem_empiricalDistributionEvent_succ_iff.mp hx
    simpa [targetSet, hTuple] using hνs
  -- Proof comment: compare the single empirical-distribution event with the full preimage of `s`
  -- under the tuple empirical-law map, then transport that preimage back to `empiricalMeasureLaw`.
  calc
    empiricalDistributionProbability μ (n + 1) ν
      = productLaw (empiricalDistributionEvent (n + 1) ν) := by
          rw [empiricalDistributionProbability_def]
    _ ≤ productLaw targetSet :=
          measure_mono hEventSubset
    _ = ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s) := by
          symm
          exact empiricalMeasureLaw_apply_eq_productLaw_preimage
            (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ s hs n

/-- Helper for Theorem 23.13: on a finite discrete alphabet, vanishing on every `μ`-null
singleton is enough for absolute continuity with respect to `μ`. -/
private theorem absolutelyContinuous_of_nullSingletonImp
    [Fintype S]
    (μ ν : ProbabilityMeasure S)
    (hNull : ∀ a : S, (μ : Measure S) {a} = 0 → (ν : Measure S) {a} = 0) :
    (ν : Measure S) ≪ (μ : Measure S) := by
  by_contra hNotAc
  -- Proof comment: failure of absolute continuity is witnessed by a `μ`-null singleton carrying
  -- positive `ν`-mass, contradicting the singleton implication hypothesis.
  obtain ⟨a, hμa, hνa⟩ :=
    exists_singleton_mass_witness_of_not_absolutelyContinuous μ ν hNotAc
  exact hνa (hNull a hμa)

/-- Helper for Theorem 23.13: the polynomial histogram bound contributes a vanishing
`(n + 1)⁻¹ log` correction on the large-deviation scale. -/
private theorem scaledLogHistogramCardBound_tendsto_zero
    [Fintype S] :
    Tendsto
      (fun n : ℕ ↦
        ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)))
      atTop (𝓝 0) := by
  have hEq :
      (fun n : ℕ ↦
        ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))) =
        fun n : ℕ ↦
          (((Fintype.card S : ℝ) * Real.log (n + 2) / (n + 1) : ℝ) : EReal) := by
    funext n
    have hLog :
        ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)) =
          (Real.log ((((n + 2) ^ Fintype.card S : ℕ) : ℝ)) : EReal) := by
      -- Proof comment: the histogram factor is a positive finite natural number, so its
      -- `ENNReal.log` is the ordinary real logarithm viewed inside `EReal`.
      exact ENNReal.log_pos_real (by simp) (by simp)
    calc
      ((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))
          = ((n + 1 : ℝ) : EReal)⁻¹ *
              (Real.log ((((n + 2) ^ Fintype.card S : ℕ) : ℝ)) : EReal) := by
                rw [hLog]
      _ = ((Real.log ((((n + 2) ^ Fintype.card S : ℕ) : ℝ)) / (n + 1) : ℝ) : EReal) := by
            rw [mul_comm]
            rfl
      _ = (((Fintype.card S : ℝ) * Real.log (n + 2) / (n + 1) : ℝ) : EReal) := by
            congr 1
            rw [Nat.cast_pow, Real.log_pow]
            simp [Nat.cast_add, Nat.cast_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hLogDiv :
      Tendsto (fun n : ℕ ↦ Real.log (n + 2) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    -- Proof comment: logarithmic growth is negligible compared with the linear scale `n + 1`,
    -- after shifting the standard real asymptotic theorem by `2`.
    convert
        (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
          (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop) using 1
    ext n
    rw [Function.comp, pow_one, one_mul]
    congr 1
    ring
  have hReal :
      Tendsto
        (fun n : ℕ ↦ (Fintype.card S : ℝ) * (Real.log (n + 2) / (n + 1 : ℝ)))
        atTop (𝓝 0) := by
    -- Proof comment: multiplying the vanishing logarithmic correction by the constant alphabet
    -- size still tends to `0`.
    simpa using hLogDiv.const_mul (Fintype.card S : ℝ)
  rw [hEq]
  exact
    (continuous_coe_real_ereal.tendsto 0).comp <| by
      simpa [mul_div_assoc] using hReal

/-- Helper for Theorem 23.13: the closed-branch empirical-measure mass is controlled by the
finite family of realized empirical histograms. -/
private theorem empiricalMeasureLaw_apply_le_histogramUpper
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (s : Set (ProbabilityMeasure S)) (hs : MeasurableSet s) (n : ℕ) :
    ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s) ≤
      (((n + 2) ^ Fintype.card S : ℕ) : ENNReal) *
        EReal.exp (-((n + 1 : EReal) *
          sInf ((fun ν : ProbabilityMeasure S ↦
            (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s))) := by
  classical
  let productLaw : Measure (Fin (n + 1) → S) :=
    ((ProbabilityMeasure.pi fun _ : Fin (n + 1) ↦ μ :
      ProbabilityMeasure (Fin (n + 1) → S)) : Measure (Fin (n + 1) → S))
  let realizedEmpiricalDistributions :=
    {ν : ProbabilityMeasure S // ν ∈ empiricalDistributions (n + 1)}
  let targetSet : Set (Fin (n + 1) → S) :=
    {x : Fin (n + 1) → S | empiricalDistributionTuple (n := Nat.succPNat n) x ∈ s}
  letI : Finite realizedEmpiricalDistributions :=
    finiteRealizedEmpiricalDistributions (S := S) n
  letI : Fintype realizedEmpiricalDistributions :=
    Fintype.ofFinite realizedEmpiricalDistributions
  have hTargetSet :
      targetSet =
        ⋃ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
          empiricalDistributionEvent (n + 1) ν.1.1 := by
    ext x
    constructor
    · intro hx
      -- Proof comment: every tuple realizing a law in `s` belongs to the exact event of its own
      -- empirical distribution, and that law is one of the finitely many realized histograms.
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨⟨empiricalDistributionTuple (n := Nat.succPNat n) x, ?_⟩, ?_⟩, ?_⟩
      · exact (mem_empiricalDistributions_iff (n + 1)
          (empiricalDistributionTuple (n := Nat.succPNat n) x)).2
          ⟨x, mem_empiricalDistributionEvent_succ_iff.mpr rfl⟩
      · simpa [targetSet] using hx
      · exact mem_empiricalDistributionEvent_succ_iff.mpr rfl
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨ν, hν⟩
      -- Proof comment: conversely, every tuple in one of those exact events has empirical law
      -- equal to the indexing histogram, hence lands back in the tuple preimage of `s`.
      have hTuple : empiricalDistributionTuple (n := Nat.succPNat n) x = ν.1.1 :=
        mem_empiricalDistributionEvent_succ_iff.mp hν
      simpa [targetSet, hTuple] using ν.2
  have hFiniteUnion :
      productLaw targetSet ≤
        ∑ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
          productLaw (empiricalDistributionEvent (n + 1) ν.1.1) := by
    -- Proof comment: the tuple preimage is covered by a finite union of exact empirical-law
    -- events, so subadditivity bounds its mass by the sum of those event masses.
    calc
      productLaw targetSet
        = productLaw
            (⋃ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
              empiricalDistributionEvent (n + 1) ν.1.1) := by
                rw [hTargetSet]
      _ ≤ ∑ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
            productLaw (empiricalDistributionEvent (n + 1) ν.1.1) := by
              simpa using
                (measure_iUnion_fintype_le productLaw
                  (fun ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s} ↦
                    empiricalDistributionEvent (n + 1) ν.1.1))
  have hTermBound (ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s}) :
      productLaw (empiricalDistributionEvent (n + 1) ν.1.1) ≤
        EReal.exp (-((n + 1 : EReal) *
          sInf ((fun ρ : ProbabilityMeasure S ↦
            (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s))) := by
    obtain ⟨_, hUpper⟩ :=
      empiricalDistributionProbability_sanov_bounds
        (μ := μ) (n := n + 1) (ν := ν.1.1) ν.1.2
    have hInf :
        sInf ((fun ρ : ProbabilityMeasure S ↦
            (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s) ≤
          (klDiv (ν.1.1 : Measure S) (μ : Measure S) : EReal) := by
      exact sInf_le ⟨ν.1.1, ν.2, rfl⟩
    have hMul :
        (n + 1 : EReal) *
            sInf ((fun ρ : ProbabilityMeasure S ↦
              (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s) ≤
          (n + 1 : EReal) * (klDiv (ν.1.1 : Measure S) (μ : Measure S) : EReal) := by
      exact mul_le_mul_of_nonneg_left hInf (by exact_mod_cast Nat.zero_le (n + 1))
    have hExp :
        EReal.exp (-((n + 1 : EReal) * (klDiv (ν.1.1 : Measure S) (μ : Measure S) : EReal))) ≤
          EReal.exp (-((n + 1 : EReal) *
            sInf ((fun ρ : ProbabilityMeasure S ↦
              (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s))) := by
      rw [EReal.exp_neg, EReal.exp_neg]
      exact ENNReal.inv_le_inv' (EReal.exp_monotone hMul)
    exact le_trans (by simpa [productLaw, empiricalDistributionProbability_def] using hUpper) hExp
  have hCardBound :
      Fintype.card {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s} ≤
        (n + 2) ^ Fintype.card S := by
    -- Proof comment: the index family is a subtype of the finite set of realized empirical laws,
    -- whose cardinality is already bounded by the polynomial histogram count.
    exact le_trans
      (Fintype.card_subtype_le (fun ρ : realizedEmpiricalDistributions ↦ ρ.1 ∈ s))
      (by
        simpa [realizedEmpiricalDistributions, Nat.card_eq_fintype_card] using
          empiricalDistributionsCard_le (S := S) n)
  -- Proof comment: transport the empirical-measure law to the tuple product law, sum over the
  -- finitely many realized histograms inside `s`, and compress the resulting constant sum by the
  -- histogram-count bound.
  calc
    ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s)
      = productLaw targetSet := by
          exact empiricalMeasureLaw_apply_eq_productLaw_preimage
            (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ s hs n
    _ ≤ ∑ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
          productLaw (empiricalDistributionEvent (n + 1) ν.1.1) :=
        hFiniteUnion
    _ ≤ ∑ ν : {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s},
          EReal.exp (-((n + 1 : EReal) *
            sInf ((fun ρ : ProbabilityMeasure S ↦
              (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s))) := by
            exact Finset.sum_le_sum fun ν _ ↦ hTermBound ν
    _ = (Fintype.card {ρ : realizedEmpiricalDistributions // ρ.1 ∈ s} : ENNReal) *
          EReal.exp (-((n + 1 : EReal) *
            sInf ((fun ρ : ProbabilityMeasure S ↦
              (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((n + 2) ^ Fintype.card S : ℕ) : ENNReal) *
          EReal.exp (-((n + 1 : EReal) *
            sInf ((fun ρ : ProbabilityMeasure S ↦
              (klDiv (ρ : Measure S) (μ : Measure S) : EReal)) '' s))) := by
            gcongr

/-- Helper for Theorem 23.13: on a finite discrete alphabet, closed subsets of
`ProbabilityMeasure S` are measurable for the inherited Giry sigma-algebra.

TODO: identify the weak topology on `ProbabilityMeasure S` with the induced finite coordinate
topology given by singleton masses, then conclude `OpensMeasurableSpace (ProbabilityMeasure S)`. -/
private theorem closedMeasurableSet_probabilityMeasureFiniteAlphabet
    [Fintype S] {s : Set (ProbabilityMeasure S)} (hs : IsClosed s) :
    MeasurableSet s := by
  classical
  -- Route correction: the closed branch cannot use `hs.measurableSet` directly because the
  -- inherited measurable space on `ProbabilityMeasure S` is not yet known to contain all weak
  -- Borel sets. The missing bridge is exactly this finite-alphabet measurability lemma.
  let coordinateMass : ProbabilityMeasure S → S → ℝ :=
    fun ν a ↦ (ν : Measure S).real {a}
  have hCoordinateMass_cont : Continuous coordinateMass := by
    -- Proof comment: every coordinate is the continuous singleton-mass map, so the product map
    -- into the finite coordinate space is continuous.
    refine continuous_pi ?_
    intro a
    simpa [coordinateMass] using continuous_singletonMassReal (S := S) a
  have hCoordinateMass_injective : Function.Injective coordinateMass := by
    intro ν₁ ν₂ hEq
    apply ProbabilityMeasure.toMeasure_injective
    have hPmf :
        ((ν₁ : Measure S).toPMF) = ((ν₂ : Measure S).toPMF) := by
      ext a
      have hSingleton :
          (ν₁ : Measure S) {a} = (ν₂ : Measure S) {a} := by
        -- Proof comment: equality of the coordinate map is exactly equality of all singleton
        -- masses after converting back from `Measure.real`.
        have hReal := congrArg ENNReal.ofReal (congrFun hEq a)
        simpa [coordinateMass, Measure.real] using hReal
      simpa [Measure.toPMF_apply] using hSingleton
    -- Proof comment: on a countable singleton-measurable space, a probability measure is
    -- determined by its `PMF` of singleton masses.
    simpa [Measure.toPMF_toMeasure] using congrArg PMF.toMeasure hPmf
  have hCoordinateMass_closedEmbedding : Topology.IsClosedEmbedding coordinateMass :=
    hCoordinateMass_cont.isClosedEmbedding hCoordinateMass_injective
  have hCoordinateMass_measurable : Measurable coordinateMass := by
    -- Proof comment: the Giry measurable space is generated by coordinate evaluations on
    -- measurable sets, and each singleton is measurable on the discrete alphabet.
    refine measurable_pi_lambda _ ?_
    intro a
    exact
      ((Measure.measurable_coe (measurableSet_singleton a)).ennreal_toReal).comp
        measurable_subtype_coe
  have hImageMeasurable : MeasurableSet (coordinateMass '' s) := by
    -- Proof comment: the closed image sits in the finite-dimensional coordinate simplex, so it is
    -- Borel measurable there.
    exact
      ((hCoordinateMass_closedEmbedding.isClosed_iff_image_isClosed).1 hs).measurableSet
  have hPreimage :
      s = coordinateMass ⁻¹' (coordinateMass '' s) := by
    -- Proof comment: injectivity identifies `s` with the preimage of its coordinate image.
    ext ν
    constructor
    · intro hν
      exact ⟨ν, hν, rfl⟩
    · intro hν
      rcases hν with ⟨ν', hν', hEqν⟩
      simpa [hCoordinateMass_injective hEqν] using hν'
  rw [hPreimage]
  exact hCoordinateMass_measurable hImageMeasurable

/-- Helper for Theorem 23.13: after taking logarithms and dividing by `n + 1`, the histogram
upper bound splits into the vanishing polynomial correction and the rate term. -/
private theorem scaledLog_empiricalMeasureLaw_le_histogramUpper
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (s : Set (ProbabilityMeasure S)) (hs : MeasurableSet s) (n : ℕ) :
    ((n + 1 : ℝ) : EReal)⁻¹ *
        (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) ≤
      (((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))) +
        (-sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)) := by
  let rateInf : EReal :=
    sInf ((fun ν : ProbabilityMeasure S ↦
      (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)
  have hBound :=
    empiricalMeasureLaw_apply_le_histogramUpper
      (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ s hs n
  have hLog :
      (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) ≤
        ENNReal.log
          ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal) *
            EReal.exp (-((n + 1 : EReal) * rateInf))) := by
    -- Proof comment: `ENNReal.log` is monotone, so the histogram upper bound survives after
    -- taking logarithms.
    exact ENNReal.log_le_log hBound
  have hScaled :
      ((n + 1 : ℝ) : EReal)⁻¹ *
          (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) ≤
        ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log
            ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal) *
              EReal.exp (-((n + 1 : EReal) * rateInf))) := by
    -- Proof comment: multiplying by the positive factor `(n + 1)⁻¹` preserves the logarithmic
    -- inequality.
    exact mul_le_mul_of_nonneg_left hLog <| EReal.inv_nonneg_of_nonneg <| by positivity
  refine hScaled.trans_eq ?_
  have hCancelCast : (n + 1 : EReal) = ((n + 1 : ℝ) : EReal) := rfl
  have hDenom_pos : (0 : EReal) < ((n + 1 : ℝ) : EReal) := by
    exact_mod_cast (Nat.succ_pos n)
  have hDenom_bot : (((n + 1 : ℝ) : EReal)) ≠ ⊥ := by
    exact EReal.coe_ne_bot (n + 1 : ℝ)
  have hDenom_top : (((n + 1 : ℝ) : EReal)) ≠ ⊤ := by
    exact EReal.coe_ne_top (n + 1 : ℝ)
  have hDenom_zero : (((n + 1 : ℝ) : EReal)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hInv_ne_top : (((n + 1 : ℝ) : EReal)⁻¹) ≠ ⊤ := (EReal.inv_lt_top _).ne
  -- Proof comment: `log (cardinality factor * exponential rate)` splits additively, and the
  -- factor `(n + 1)⁻¹` cancels against the exponential scale term.
  rw [ENNReal.log_mul_add, EReal.log_exp]
  rw [EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.inv_nonneg_of_nonneg (by positivity)) hInv_ne_top]
  calc
    ((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)) +
        ((n + 1 : ℝ) : EReal)⁻¹ * (-((n + 1 : EReal) * rateInf))
      = ((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)) +
          ((((n + 1 : ℝ) : EReal)⁻¹ * (((n + 1 : ℝ) : EReal) * (-rateInf)))) := by
            rw [hCancelCast, neg_mul_eq_mul_neg]
    _ = ((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)) +
          (-rateInf) := by
            congr 1
            calc
              ((n + 1 : ℝ) : EReal)⁻¹ * (((n + 1 : ℝ) : EReal) * (-rateInf))
                = ((((n + 1 : ℝ) : EReal) * (-rateInf)) / (((n + 1 : ℝ) : EReal))) := by
                    rw [← EReal.div_eq_inv_mul]
              _ = (((n + 1 : ℝ) : EReal) * (((-rateInf) / ((n + 1 : ℝ) : EReal)))) := by
                    rw [← EReal.mul_div]
              _ = -rateInf := by
                    rw [EReal.mul_div_cancel hDenom_bot hDenom_top hDenom_zero]
    _ =
        (((n + 1 : ℝ) : EReal)⁻¹ *
            ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))) +
          (-sInf ((fun ν : ProbabilityMeasure S ↦
            (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)) := by
              simp [rateInf]

/-- Helper for Theorem 23.13: on a finite alphabet, the real singleton masses of a probability
measure sum to `1`. -/
private theorem sum_singletonMassReal_eq_one
    [Fintype S] (ν : ProbabilityMeasure S) :
    ∑ a : S, (ν : Measure S).real {a} = 1 := by
  let f : BoundedContinuousFunction S ℝ := 1
  have hIntegral :
      ∫ x, f x ∂(ν : Measure S) = ∑ a : S, (ν : Measure S).real {a} * f a := by
    -- Proof comment: on a finite discrete alphabet, the integral of a bounded test function is
    -- the finite sum of the singleton masses weighted by the function values.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := (ν : Measure S)) (f := fun x : S ↦ f x)
        (BoundedContinuousFunction.integrable (ν : Measure S) f))
  -- Proof comment: the constant-one test function integrates to the total mass `1`.
  calc
    ∑ a : S, (ν : Measure S).real {a}
      = ∑ a : S, (ν : Measure S).real {a} * f a := by simp [f]
    _ = ∫ x, f x ∂(ν : Measure S) := hIntegral.symm
    _ = 1 := by simp [f]

/-- Helper for Theorem 23.13: every count vector on a finite alphabet with total mass `n + 1`
is realized by a word of length `n + 1`. -/
private theorem existsWordOfEmpiricalCounts
    [Fintype S] [DecidableEq S]
    (n : ℕ) (k : S → ℕ) (hk : ∑ a, k a = n + 1) :
    ∃ x : Fin (n + 1) → S, ∀ a : S, empiricalCount (n + 1) x a = k a := by
  classical
  let s : Sym S (n + 1) := (Sym.equivNatSumOfFintype S (n + 1)).symm ⟨k, hk⟩
  let v : List.Vector S (n + 1) :=
    ⟨(s : Multiset S).toList, by simp [Sym.card_coe]⟩
  refine ⟨v.get, ?_⟩
  intro a
  have hCount :
      empiricalCount (n + 1) v.get a = v.toList.count a := by
    -- Proof comment: rewrite the empirical count as the multiplicity of `a` in the canonical
    -- word list associated with the vector `v`.
    simpa [empiricalCount, Fintype.card_subtype] using
      Fin.card_filter_univ_eq_vector_get_eq_count a v
  -- Proof comment: the symmetric word attached to `k` has exactly the prescribed multiplicities.
  calc
    empiricalCount (n + 1) v.get a = v.toList.count a := hCount
    _ = (s : Multiset S).count a := by
          rw [show v.toList = (s : Multiset S).toList by rfl]
          rw [← Multiset.coe_count]
          exact congrArg (Multiset.count a) (Multiset.coe_toList (s : Multiset S))
    _ = k a := by
          simpa [s] using
            (Sym.coe_equivNatSumOfFintype_apply_apply (α := S) (n := n + 1) s a).symm

/-- Helper for Theorem 23.13: the logarithmic contribution of the Sanov lower prefactor vanishes
after scaling by `n + 1`. -/
private theorem scaledLogLowerPrefactor_tendsto_zero
    [Fintype S] :
    Tendsto
      (fun n : ℕ ↦
        ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log (empiricalLowerPrefactor S (n + 1)))
      atTop (𝓝 0) := by
  have hEq :
      (fun n : ℕ ↦
        ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log (empiricalLowerPrefactor S (n + 1))) =
        fun n : ℕ ↦
          -(((n + 1 : ℝ) : EReal)⁻¹ *
            ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))) := by
    funext n
    have hPrefactor :
        empiricalLowerPrefactor S (n + 1) =
          ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)⁻¹) := by
      simp [empiricalLowerPrefactor, ENNReal.inv_pow, Nat.add_assoc]
    rw [hPrefactor, ENNReal.log_inv, mul_neg]
  -- Proof comment: the lower prefactor is the inverse polynomial factor from the upper bound, so
  -- its scaled logarithm is the negative of the already-controlled histogram correction.
  rw [hEq]
  simpa using (scaledLogHistogramCardBound_tendsto_zero (S := S)).neg

/-- Helper for Theorem 23.13: flooring `(n + 1) p` and dividing back by `n + 1` converges to
`p`. -/
private theorem floorRatio_floorMul_tendsto
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto
      (fun n : ℕ ↦ (Nat.floor (((n + 1 : ℕ) : ℝ) * p) : ℝ) / (n + 1))
      atTop (𝓝 p) := by
  -- Proof comment: this is the standard `⌊x p⌋ / x → p` limit, specialized to the shifted
  -- natural scale `x = n + 1`.
  have hShift :
      Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  simpa [Nat.cast_add, Nat.cast_one, mul_comm] using
    ((tendsto_nat_floor_mul_div_atTop hp).comp hShift)

/-- Helper for Theorem 23.13: on the absolutely continuous face of the finite simplex, one can
round the singleton masses to integer counts of total mass `n + 1` while preserving every
`μ`-null coordinate. -/
private theorem roundedEmpiricalCountsOfAbsolutelyContinuousMeasure
    [Fintype S]
    (μ ν : ProbabilityMeasure S)
    (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    ∃ k : ℕ → S → ℕ,
      (∀ n, ∑ a, k n a = n + 1) ∧
      (∀ a n, (μ : Measure S) {a} = 0 → k n a = 0) ∧
      (∀ a, Tendsto (fun n ↦ (k n a : ℝ) / (n + 1)) atTop
        (𝓝 ((ν : Measure S).real {a}))) := by
  classical
  let m : S → ℝ := fun a ↦ (ν : Measure S).real {a}
  have hm_nonneg : ∀ a : S, 0 ≤ m a := by
    intro a
    exact ENNReal.toReal_nonneg
  have hBaseExists : ∃ a0 : S, (μ : Measure S) {a0} ≠ 0 := by
    by_contra hBase
    have hZero : ∀ a : S, (μ : Measure S) {a} = 0 := by
      intro a
      by_contra hμa
      exact hBase ⟨a, hμa⟩
    have hSumZero : ∑ a : S, (μ : Measure S).real {a} = 0 := by
      simp [Measure.real, hZero]
    have hSumOne := sum_singletonMassReal_eq_one (S := S) μ
    linarith
  rcases hBaseExists with ⟨a0, hμa0⟩
  let offCount : ℕ → S → ℕ :=
    fun n a ↦ Nat.floor (((n + 1 : ℕ) : ℝ) * m a)
  let k : ℕ → S → ℕ :=
    fun n a ↦
      if a = a0 then
        (n + 1) - Finset.sum (Finset.univ.erase a0) (fun b ↦ offCount n b)
      else
        offCount n a
  have hMassOff_le_one :
      Finset.sum (Finset.univ.erase a0) m ≤ 1 := by
    have hSplit :
        m a0 + Finset.sum (Finset.univ.erase a0) m = 1 := by
      calc
        m a0 + Finset.sum (Finset.univ.erase a0) m = ∑ a : S, m a := by
          simpa using
            (Finset.sum_erase_add (s := Finset.univ) (by simp) (f := m))
        _ = 1 := by
          simpa [m] using sum_singletonMassReal_eq_one (S := S) ν
    have hm_a0_nonneg : 0 ≤ m a0 := hm_nonneg a0
    linarith
  have hOffSum_le (n : ℕ) :
      Finset.sum (Finset.univ.erase a0) (offCount n) ≤ n + 1 := by
    have hReal :
        ((Finset.sum (Finset.univ.erase a0) (offCount n) : ℕ) : ℝ) ≤ n + 1 := by
      calc
        ((Finset.sum (Finset.univ.erase a0) (offCount n) : ℕ) : ℝ)
            = Finset.sum (Finset.univ.erase a0) (fun b ↦ (offCount n b : ℝ)) := by
                simp
        _ ≤ Finset.sum (Finset.univ.erase a0) (fun b ↦ (((n + 1 : ℕ) : ℝ) * m b)) := by
              refine Finset.sum_le_sum ?_
              intro b hb
              exact_mod_cast Nat.floor_le (mul_nonneg (by positivity) (hm_nonneg b))
        _ = ((n + 1 : ℕ) : ℝ) * Finset.sum (Finset.univ.erase a0) m := by
              rw [Finset.mul_sum]
        _ ≤ ((n + 1 : ℕ) : ℝ) * 1 := by
              gcongr
        _ = n + 1 := by
              norm_num
    exact_mod_cast hReal
  have hk_sum (n : ℕ) : ∑ a : S, k n a = n + 1 := by
    have hEraseEq :
        Finset.sum (Finset.univ.erase a0) (k n) =
          Finset.sum (Finset.univ.erase a0) (offCount n) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have ha0 : a ≠ a0 := by
        simpa using ha
      simp [k, offCount, ha0]
    have hDecomp :
        Finset.sum (Finset.univ.erase a0) (k n) + k n a0 = ∑ a : S, k n a := by
      exact Finset.sum_erase_add (s := Finset.univ) (a := a0) (f := k n) (by simp)
    calc
      ∑ a : S, k n a = Finset.sum (Finset.univ.erase a0) (k n) + k n a0 := hDecomp.symm
      _ = Finset.sum (Finset.univ.erase a0) (offCount n) + k n a0 := by
            rw [hEraseEq]
      _ = k n a0 + Finset.sum (Finset.univ.erase a0) (offCount n) := by
            rw [add_comm]
      _ = ((n + 1) - Finset.sum (Finset.univ.erase a0) (offCount n)) +
            Finset.sum (Finset.univ.erase a0) (offCount n) := by
              simp [k, offCount]
      _ = n + 1 := Nat.sub_add_cancel (hOffSum_le n)
  have hk_null (a : S) (n : ℕ) (hμa : (μ : Measure S) {a} = 0) :
      k n a = 0 := by
    by_cases ha0 : a = a0
    · exact False.elim (hμa0 (ha0 ▸ hμa))
    · have hνa : (ν : Measure S) {a} = 0 := h_ac hμa
      have hm_a : m a = 0 := by
        simp [m, Measure.real, hνa]
      simp [k, offCount, ha0, hm_a]
  have hk_off_tendsto {a : S} (ha : a ≠ a0) :
      Tendsto (fun n ↦ (k n a : ℝ) / (n + 1)) atTop (𝓝 (m a)) := by
    -- Proof comment: away from the distinguished coordinate, the counts are just the floored
    -- multiples of the target singleton mass.
    simpa [k, offCount, ha] using floorRatio_floorMul_tendsto (p := m a) (hm_nonneg a)
  have hk_base_eq (n : ℕ) :
      (k n a0 : ℝ) / (n + 1) =
        1 - Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ) / (n + 1)) := by
    have hNat :
        k n a0 + Finset.sum (Finset.univ.erase a0) (k n) = n + 1 := by
      calc
        k n a0 + Finset.sum (Finset.univ.erase a0) (k n) = ∑ a : S, k n a := by
          simpa [add_comm] using
            (Finset.sum_erase_add (s := Finset.univ) (by simp) (f := k n))
        _ = n + 1 := hk_sum n
    have hReal :
        (k n a0 : ℝ) + Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ)) = n + 1 := by
      exact_mod_cast hNat
    have hDenom : (n + 1 : ℝ) ≠ 0 := by positivity
    have hDiv :
        (k n a0 : ℝ) / (n + 1) +
            Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ) / (n + 1)) =
          1 := by
      calc
        (k n a0 : ℝ) / (n + 1) +
            Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ) / (n + 1))
            = (((k n a0 : ℝ) + Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ))) /
                (n + 1)) := by
                  rw [add_div, Finset.sum_div]
        _ = (n + 1) / (n + 1 : ℝ) := by rw [hReal]
        _ = 1 := by field_simp [hDenom]
    linarith
  have hm_base_eq :
      m a0 = 1 - Finset.sum (Finset.univ.erase a0) m := by
    have hSplit :
        m a0 + Finset.sum (Finset.univ.erase a0) m = 1 := by
      calc
        m a0 + Finset.sum (Finset.univ.erase a0) m = ∑ a : S, m a := by
          simpa using
            (Finset.sum_erase_add (s := Finset.univ) (by simp) (f := m))
        _ = 1 := by
          simpa [m] using sum_singletonMassReal_eq_one (S := S) ν
    linarith
  have hk_base_tendsto :
      Tendsto (fun n ↦ (k n a0 : ℝ) / (n + 1)) atTop (𝓝 (m a0)) := by
    have hOffSumTendsto :
        Tendsto
          (fun n ↦ Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ) / (n + 1)))
          atTop
          (𝓝 (Finset.sum (Finset.univ.erase a0) m)) := by
      refine tendsto_finset_sum _ ?_
      intro b hb
      exact hk_off_tendsto (by simpa using hb)
    have hEq :
        (fun n ↦ (k n a0 : ℝ) / (n + 1)) =
          fun n ↦ 1 - Finset.sum (Finset.univ.erase a0) (fun b ↦ (k n b : ℝ) / (n + 1)) := by
      funext n
      exact hk_base_eq n
    rw [hEq, hm_base_eq]
    -- Proof comment: the distinguished coordinate is recovered from the simplex identity `sum = 1`
    -- after proving convergence of every other coordinate.
    exact tendsto_const_nhds.sub hOffSumTendsto
  refine ⟨k, hk_sum, ?_, ?_⟩
  · intro a n hμa
    exact hk_null a n hμa
  · intro a
    by_cases ha : a = a0
    · subst ha
      simpa [m] using hk_base_tendsto
    · simpa [m] using hk_off_tendsto ha

/-- Helper for Theorem 23.13: the rounded count vectors can be realized by empirical
distributions that converge back to the absolutely continuous witness and preserve every
`μ`-null singleton. -/
private theorem empiricalApproximationOfAbsolutelyContinuousMeasure
    [Fintype S]
    (μ ν : ProbabilityMeasure S)
    (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    ∃ νn : ℕ → ProbabilityMeasure S,
      (∀ n, νn n ∈ empiricalDistributions (n + 1)) ∧
      (∀ a, Tendsto (fun n ↦ (νn n : Measure S).real {a}) atTop
        (𝓝 ((ν : Measure S).real {a}))) ∧
      Tendsto νn atTop (𝓝 ν) ∧
      (∀ a n, (μ : Measure S) {a} = 0 → (νn n : Measure S) {a} = 0) := by
  classical
  obtain ⟨k, hkSum, hkNull, hkTendsto⟩ :=
    roundedEmpiricalCountsOfAbsolutelyContinuousMeasure (μ := μ) (ν := ν) h_ac
  let x : ∀ n : ℕ, Fin (n + 1) → S :=
    fun n ↦ Classical.choose (existsWordOfEmpiricalCounts (S := S) n (k n) (hkSum n))
  let νn : ℕ → ProbabilityMeasure S :=
    fun n ↦ empiricalDistributionTuple (n := Nat.succPNat n) (x n)
  have hxCount (n : ℕ) :
      ∀ a : S, empiricalCount (n + 1) (x n) a = k n a :=
    Classical.choose_spec (existsWordOfEmpiricalCounts (S := S) n (k n) (hkSum n))
  have hMassReal_eq (n : ℕ) (a : S) :
      (νn n : Measure S).real {a} = (k n a : ℝ) / (n + 1) := by
    -- Proof comment: the realized tuple has exactly the prescribed empirical counts, so the
    -- singleton masses are the normalized counts from the previous rounding step.
    dsimp [νn]
    rw [Measure.real, empiricalDistributionTuple_apply_singleton (n := n) (x := x n) a, hxCount n a,
      ENNReal.toReal_div, ENNReal.toReal_natCast]
    congr 1
    simpa [Nat.cast_add, Nat.cast_one] using (ENNReal.toReal_natCast (n + 1))
  have hCoordReal (a : S) :
      Tendsto (fun n ↦ (νn n : Measure S).real {a}) atTop
        (𝓝 ((ν : Measure S).real {a})) := by
    have hEq :
        (fun n ↦ (νn n : Measure S).real {a}) =
          fun n ↦ (k n a : ℝ) / (n + 1) := by
      funext n
      exact hMassReal_eq n a
    rw [hEq]
    exact hkTendsto a
  refine ⟨νn, ?_, ?_, ?_, ?_⟩
  · intro n
    refine (mem_empiricalDistributions_iff (n + 1) (νn n)).2 ?_
    refine ⟨x n, ?_⟩
    exact mem_empiricalDistributionEvent_succ_iff.mpr rfl
  · intro a
    exact hCoordReal a
  · -- Proof comment: on a finite discrete alphabet, coordinatewise convergence of singleton
  -- masses is exactly weak convergence of probability measures.
    exact tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto hCoordReal
  · intro a n hμa
    dsimp [νn]
    rw [empiricalDistributionTuple_apply_singleton (n := n) (x := x n) a, hxCount n a, hkNull a n hμa]
    simp

/-- Helper for Theorem 23.13: on the fixed absolutely continuous face of the finite simplex, KL
divergence is continuous along coordinatewise convergence of singleton masses. -/
private theorem klDiv_tendsto_of_singletonMassApproximation
    [Fintype S]
    (μ ν : ProbabilityMeasure S) {νn : ℕ → ProbabilityMeasure S}
    (h_ac : (ν : Measure S) ≪ (μ : Measure S))
    (h_ac_n : ∀ n, (νn n : Measure S) ≪ (μ : Measure S))
    (hCoord : ∀ a, Tendsto (fun n ↦ (νn n : Measure S).real {a}) atTop
      (𝓝 ((ν : Measure S).real {a}))) :
    Tendsto (fun n ↦ klDiv (νn n : Measure S) (μ : Measure S)) atTop
      (𝓝 (klDiv (ν : Measure S) (μ : Measure S))) := by
  have hTendsto : Tendsto νn atTop (𝓝 ν) :=
    tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto hCoord
  have hEqSeq :
      (fun n ↦ klDiv (νn n : Measure S) (μ : Measure S)) =
        fun n ↦ ∑ a : S, singletonKlTerm μ (νn n) a := by
    funext n
    simpa using klDiv_eq_sum_singletonKlTerm_of_absolutelyContinuous μ (νn n) (h_ac_n n)
  rw [hEqSeq, show klDiv (ν : Measure S) (μ : Measure S) = ∑ a : S, singletonKlTerm μ ν a by
    simpa using klDiv_eq_sum_singletonKlTerm_of_absolutelyContinuous μ ν h_ac]
  -- Proof comment: after rewriting KL as a finite sum of the singleton terms, continuity of each
  -- coordinate term reduces the convergence to `tendsto_finset_sum`.
  exact tendsto_finset_sum _ fun a _ ↦
    ((continuous_singletonKlTerm (μ := μ) a).tendsto ν).comp hTendsto

/-- Helper for Theorem 23.13: a single empirical witness inside an open target set gives a lower
bound on the scaled logarithmic empirical-measure mass. -/
private theorem scaledLog_empiricalMeasureLaw_ge_openWitness
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ)
    (s : Set (ProbabilityMeasure S)) (hs : MeasurableSet s) (n : ℕ)
    {ν : ProbabilityMeasure S} (hνs : ν ∈ s) (hνemp : ν ∈ empiricalDistributions (n + 1))
    (h_ac : (ν : Measure S) ≪ (μ : Measure S)) :
    (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
        (-(klDiv (ν : Measure S) (μ : Measure S) : EReal)) ≤
      ((n + 1 : ℝ) : EReal)⁻¹ *
        (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) := by
  let rate : ENNReal := klDiv (ν : Measure S) (μ : Measure S)
  have hEventLower :
      empiricalLowerPrefactor S (n + 1) * EReal.exp (-((n + 1 : EReal) * (rate : EReal))) ≤
        ((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s) := by
    obtain ⟨hLower, _⟩ :=
      empiricalDistributionProbability_sanov_bounds
        (μ := μ) (n := n + 1) (ν := ν) hνemp
    have hLowerRate :
        empiricalLowerPrefactor S (n + 1) * EReal.exp (-((n + 1 : EReal) * (rate : EReal))) ≤
          empiricalDistributionProbability μ (n + 1) ν := by
      simpa [rate] using hLower
    exact le_trans hLowerRate
      (empiricalDistributionProbability_le_empiricalMeasureLaw_of_mem
        (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ s hs hνs n)
  have hLog :
      ENNReal.log
          (empiricalLowerPrefactor S (n + 1) *
            EReal.exp (-((n + 1 : EReal) * (rate : EReal)))) ≤
        (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) := by
    -- Proof comment: monotonicity of `ENNReal.log` transports the lower event-mass estimate to a
    -- logarithmic lower estimate.
    exact ENNReal.log_le_log hEventLower
  have hScaled :
      ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log
            (empiricalLowerPrefactor S (n + 1) *
              EReal.exp (-((n + 1 : EReal) * (rate : EReal)))) ≤
        ((n + 1 : ℝ) : EReal)⁻¹ *
          (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) := by
    exact mul_le_mul_of_nonneg_left hLog <| EReal.inv_nonneg_of_nonneg <| by positivity
  have hCancelCast : (n + 1 : EReal) = ((n + 1 : ℝ) : EReal) := rfl
  have hDenom_bot : (((n + 1 : ℝ) : EReal)) ≠ ⊥ := by
    exact EReal.coe_ne_bot (n + 1 : ℝ)
  have hDenom_top : (((n + 1 : ℝ) : EReal)) ≠ ⊤ := by
    exact EReal.coe_ne_top (n + 1 : ℝ)
  have hDenom_zero : (((n + 1 : ℝ) : EReal)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hInv_ne_top : (((n + 1 : ℝ) : EReal)⁻¹) ≠ ⊤ := (EReal.inv_lt_top _).ne
  have hLeft :
      ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log
            (empiricalLowerPrefactor S (n + 1) *
              EReal.exp (-((n + 1 : EReal) * (rate : EReal)))) =
        (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
          (-(rate : EReal)) := by
  -- Proof comment: split the logarithm of the lower bound into the prefactor correction and the
  -- exponential KL term, then cancel the factor `(n + 1)⁻¹ * (n + 1)`.
    rw [ENNReal.log_mul_add, EReal.log_exp]
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.inv_nonneg_of_nonneg (by positivity)) hInv_ne_top]
    calc
      (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
          (((n + 1 : ℝ) : EReal)⁻¹ * (-((n + 1 : EReal) * (rate : EReal))))
        = (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
            ((((n + 1 : ℝ) : EReal)⁻¹ * (((n + 1 : ℝ) : EReal) * (-(rate : EReal))))) := by
              rw [hCancelCast, neg_mul_eq_mul_neg]
      _ = (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
            (-(rate : EReal)) := by
              congr 1
              calc
                ((n + 1 : ℝ) : EReal)⁻¹ * (((n + 1 : ℝ) : EReal) * (-(rate : EReal)))
                  = ((((n + 1 : ℝ) : EReal) * (-(rate : EReal))) /
                      (((n + 1 : ℝ) : EReal))) := by
                        rw [← EReal.div_eq_inv_mul]
                _ = (((n + 1 : ℝ) : EReal) * (((-(rate : EReal)) / ((n + 1 : ℝ) : EReal)))) := by
                      rw [← EReal.mul_div]
                _ = -(rate : EReal) := by
                      rw [EReal.mul_div_cancel hDenom_bot hDenom_top hDenom_zero]
  calc
    (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
        (-(rate : EReal))
      = ((n + 1 : ℝ) : EReal)⁻¹ *
          ENNReal.log
            (empiricalLowerPrefactor S (n + 1) *
              EReal.exp (-((n + 1 : EReal) * (rate : EReal)))) := hLeft.symm
    _ ≤ ((n + 1 : ℝ) : EReal)⁻¹ *
          (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) := hScaled

-- Proof sketch: use the combinatorial estimates for single empirical measures from the preceding
-- lemma, identify the exponential cost with the relative entropy `klDiv`, and pass from exact
-- empirical measures to arbitrary open sets via approximation inside the finite-dimensional
-- simplex.
/-- Theorem 23.13: Sanov's theorem. For i.i.d. `S`-valued random variables with common law `μ`, the
distributions of the empirical measures satisfy the large-deviation upper bound on closed sets and
the lower bound on open sets; in the chapter's `0`-based indexing, the `n`th empirical measure
uses the first `n + 1` samples, so the speed is `n + 1`, and the rate function is the relative
entropy `ν ↦ klDiv (ν : Measure S) (μ : Measure S)`. -/
theorem sanov_empiricalMeasure_largeDeviations
    [Fintype S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (μ : ProbabilityMeasure S)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hμ : ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX 0).aemeasurable = μ) :
    (∀ s : Set (ProbabilityMeasure S), IsClosed s →
      Filter.limsup
          (fun n : ℕ ↦
            ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
          atTop
        ≤ -sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)) ∧
      ∀ s : Set (ProbabilityMeasure S), IsOpen s →
        -sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s) ≤
          Filter.liminf
            (fun n : ℕ ↦
              ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
            atTop := by
  constructor
  · intro s hsClosed
    let rateInf : EReal :=
      sInf ((fun ν : ProbabilityMeasure S ↦
        (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)
    let upperBound : ℕ → EReal :=
      fun n ↦
        (((n + 1 : ℝ) : EReal)⁻¹ *
            ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal))) +
          (-rateInf)
    have hPointwise :
        ∀ n : ℕ,
          ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) ≤
            upperBound n := by
      intro n
      -- Proof comment: the closed-set branch uses the measurable-set fact `hsClosed.measurableSet`
      -- to feed the histogram upper bound into the scaled-log helper.
      simpa [upperBound, rateInf] using
        scaledLog_empiricalMeasureLaw_le_histogramUpper
          (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ
          s (closedMeasurableSet_probabilityMeasureFiniteAlphabet (S := S) hsClosed) n
    have hUpperTendsto : Tendsto upperBound atTop (𝓝 (-rateInf)) := by
      -- Proof comment: the polynomial histogram factor contributes the vanishing correction from
      -- `scaledLogHistogramCardBound_tendsto_zero`, so the whole upper envelope converges to the
      -- negative rate infimum.
      have hPair :
          Tendsto
            (fun n : ℕ ↦
              ((((n + 1 : ℝ) : EReal)⁻¹ *
                  ENNReal.log ((((n + 2) ^ Fintype.card S : ℕ) : ENNReal)),
                -rateInf)))
            atTop (𝓝 (0, -rateInf)) :=
        Filter.Tendsto.prodMk_nhds
          (scaledLogHistogramCardBound_tendsto_zero (S := S))
          tendsto_const_nhds
      have hAdd :=
        (EReal.continuousAt_add (p := (0, -rateInf)) (Or.inl (by simp)) (Or.inl (by simp))).tendsto
      simpa [upperBound, rateInf] using hAdd.comp hPair
    calc
      Filter.limsup
          (fun n : ℕ ↦
            ((n + 1 : ℝ) : EReal)⁻¹ *
              (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
          atTop
        ≤ Filter.limsup upperBound atTop := by
            exact Filter.limsup_le_limsup (Eventually.of_forall hPointwise)
      _ = -rateInf := hUpperTendsto.limsup_eq
      _ = -sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s) := by
            simp [rateInf]
  · intro s hsOpen
    by_cases hRateTop :
        sInf ((fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s) = ⊤
    · -- Proof comment: if the open-set rate infimum is `⊤`, then the lower bound is immediate
      -- because the left-hand side is `-⊤ = ⊥`.
      simpa [hRateTop] using
        (bot_le :
          (⊥ : EReal) ≤
            Filter.liminf
              (fun n : ℕ ↦
                ((n + 1 : ℝ) : EReal)⁻¹ *
                  (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log))
              atTop)
    · -- Proof comment: the nontrivial open branch has been reduced to the real missing
      -- approximation step from the re-plan is now packaged into a local support-preserving
      -- empirical approximation theorem, so the lower bound becomes a standard liminf witness
      -- argument.
      have hsMeasurable : MeasurableSet s := by
        have hComplMeas :
            MeasurableSet sᶜ :=
          closedMeasurableSet_probabilityMeasureFiniteAlphabet (S := S) hsOpen.isClosed_compl
        simpa using hComplMeas.compl
      have hsNonempty : s.Nonempty := by
        by_cases hsEmpty : s = ∅
        · simp [hsEmpty] at hRateTop
        · exact Set.nonempty_iff_ne_empty.mpr hsEmpty
      rw [Filter.le_liminf_iff']
      intro y hy
      by_cases hyBot : y = ⊥
      · exact Filter.Eventually.of_forall fun n ↦ by simp [hyBot]
      have hImageNonempty :
          ((fun ν : ProbabilityMeasure S ↦
            (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s).Nonempty :=
        hsNonempty.image fun ν : ProbabilityMeasure S ↦
          (klDiv (ν : Measure S) (μ : Measure S) : EReal)
      have hyInf :
          sInf ((fun ν : ProbabilityMeasure S ↦
            (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s) < -y := by
        simpa using EReal.neg_strictAnti hy
      obtain ⟨z, hzInf, hzy⟩ := exists_between hyInf
      obtain ⟨ν, hνImage, hνz⟩ :=
        exists_lt_of_csInf_lt
          (s := (fun ν : ProbabilityMeasure S ↦
            (klDiv (ν : Measure S) (μ : Measure S) : EReal)) '' s)
          hImageNonempty hzInf
      rcases hνImage with ⟨ν, hνs, rfl⟩
      have hyRate :
          y < -((klDiv (ν : Measure S) (μ : Measure S) : EReal)) := by
        have hyz : y < -z := by
          simpa using EReal.neg_strictAnti hzy
        have hzν : -z < -((klDiv (ν : Measure S) (μ : Measure S) : EReal)) := by
          simpa using EReal.neg_strictAnti hνz
        exact hyz.trans hzν
      have hNegyTop : -y < ⊤ := by
        exact lt_top_iff_ne_top.mpr (by simpa using hyBot)
      have hzTop : z < ⊤ := hzy.trans hNegyTop
      have hRateTopWitness :
          ((klDiv (ν : Measure S) (μ : Measure S) : EReal)) ≠ ⊤ :=
        ne_top_of_lt (hνz.trans hzTop)
      have h_ac : (ν : Measure S) ≪ (μ : Measure S) := by
        by_contra hNotAc
        have hTop :
            (klDiv (ν : Measure S) (μ : Measure S) : EReal) = ⊤ := by
          rw [klDiv_eq_lintegral_klFun]
          simp [hNotAc]
        exact hRateTopWitness hTop
      obtain ⟨νn, hEmp, hCoord, hTendsto, hNull⟩ :=
        empiricalApproximationOfAbsolutelyContinuousMeasure (μ := μ) (ν := ν) h_ac
      have hEventuallyMem : ∀ᶠ n in atTop, νn n ∈ s :=
        hTendsto.eventually (hsOpen.mem_nhds hνs)
      have hAc_n : ∀ n, (νn n : Measure S) ≪ (μ : Measure S) := by
        intro n
        exact absolutelyContinuous_of_nullSingletonImp μ (νn n) (fun a hμa ↦ hNull a n hμa)
      have hKl :
          Tendsto
            (fun n ↦ klDiv (νn n : Measure S) (μ : Measure S))
            atTop
            (𝓝 (klDiv (ν : Measure S) (μ : Measure S))) :=
        klDiv_tendsto_of_singletonMassApproximation
          (μ := μ) (ν := ν) h_ac hAc_n hCoord
      have hKlEReal :
          Tendsto
            (fun n ↦ (klDiv (νn n : Measure S) (μ : Measure S) : EReal))
            atTop
            (𝓝 ((klDiv (ν : Measure S) (μ : Measure S) : EReal))) := by
        exact continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hKl
      let lowerWitness : ℕ → EReal :=
        fun n ↦
          (((n + 1 : ℝ) : EReal)⁻¹ * ENNReal.log (empiricalLowerPrefactor S (n + 1))) +
            (-(klDiv (νn n : Measure S) (μ : Measure S) : EReal))
      have hEventuallyCompare :
          ∀ᶠ n in atTop,
            lowerWitness n ≤
              ((n + 1 : ℝ) : EReal)⁻¹ *
                (((empiricalMeasureLaw P X hX n : Measure (ProbabilityMeasure S)) s).log) := by
        filter_upwards [hEventuallyMem] with n hns
        simpa [lowerWitness] using
          scaledLog_empiricalMeasureLaw_ge_openWitness
            (P := P) (X := X) (hX := hX) (μ := μ) hindep hident hμ
            s hsMeasurable n hns (hEmp n) (hAc_n n)
      have hRateFinite : klDiv (ν : Measure S) (μ : Measure S) ≠ ⊤ := by
        simpa using hRateTopWitness
      have hNegKl :
          Tendsto
            (fun n ↦ -((klDiv (νn n : Measure S) (μ : Measure S) : EReal)))
            atTop
            (𝓝 (-((klDiv (ν : Measure S) (μ : Measure S) : EReal)))) := by
        exact continuous_neg.continuousAt.tendsto.comp hKlEReal
      have hLowerTendsto :
          Tendsto lowerWitness atTop (𝓝 (-((klDiv (ν : Measure S) (μ : Measure S) : EReal)))) := by
        have hPair :
            Tendsto
              (fun n : ℕ ↦
                ((((n + 1 : ℝ) : EReal)⁻¹ *
                    ENNReal.log (empiricalLowerPrefactor S (n + 1)),
                  -((klDiv (νn n : Measure S) (μ : Measure S) : EReal)))))
              atTop
              (𝓝 (0, -((klDiv (ν : Measure S) (μ : Measure S) : EReal)))) :=
          Filter.Tendsto.prodMk_nhds
            (scaledLogLowerPrefactor_tendsto_zero (S := S))
            hNegKl
        have hAdd :=
          (EReal.continuousAt_add
            (p := (0, -((klDiv (ν : Measure S) (μ : Measure S) : EReal))))
            (Or.inl (by simp))
            (Or.inl (by simpa using hRateFinite))).tendsto
        simpa [lowerWitness] using hAdd.comp hPair
      have hyLower :
          y < Filter.liminf lowerWitness atTop := by
        rw [hLowerTendsto.liminf_eq]
        exact hyRate
      have hEventuallyLower : ∀ᶠ n in atTop, y < lowerWitness n :=
        eventually_lt_of_lt_liminf hyLower
      filter_upwards [hEventuallyLower, hEventuallyCompare] with n hyn hcomp
      exact hyn.le.trans hcomp

end FiniteAlphabet

end ProbabilityTheory
