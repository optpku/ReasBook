/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_55
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Mathlib

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ProbabilityTheory BoundedContinuousFunction

noncomputable section

universe u v

namespace ProbabilityTheory

section GenericAmbient

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]

/-- Helper for Theorem 17.56: the admissible off-diagonal costs of couplings of `P` and `Q`. -/
private def couplingOffDiagonalCostSet
    {β : Type*} [MeasurableSpace β] [MetricSpace β] [BorelSpace β] [PolishSpace β]
    [MeasurableEq β]
    (P Q : ProbabilityMeasure β) : Set ℝ :=
  {r : ℝ | ∃ π : ProbabilityMeasure (β × β),
      IsCoupling π P Q ∧
        r = (((π : Measure (β × β))
          (((Set.univ : Set (β × β)) \ Set.diagonal β))).toReal)}

/-- Helper for Theorem 17.56: the product law already gives one admissible off-diagonal cost. -/
private theorem couplingOffDiagonalCostSet_nonempty
    {β : Type*} [MeasurableSpace β] [MetricSpace β] [BorelSpace β] [PolishSpace β]
    [MeasurableEq β]
    (P Q : ProbabilityMeasure β) :
    (couplingOffDiagonalCostSet P Q).Nonempty := by
  refine ⟨(((P.prod Q : ProbabilityMeasure (β × β)) : Measure (β × β))
      (((Set.univ : Set (β × β)) \ Set.diagonal β))).toReal, ?_⟩
  exact ⟨P.prod Q, isCoupling_prod P Q, rfl⟩

/-- Helper for Theorem 17.56: a strict total-variation bound produces a coupling whose
off-diagonal mass is strictly smaller than the same bound. -/
theorem existsCouplingOfSmallOffDiagonalMass
    {β : Type*} [MeasurableSpace β] [MetricSpace β] [BorelSpace β] [PolishSpace β]
    [MeasurableEq β]
    (P Q : ProbabilityMeasure β) {ε : ℝ}
    (hε : totalVariationDistance P Q < ε) :
    ∃ π : ProbabilityMeasure (β × β),
      IsCoupling π P Q ∧
        (((π : Measure (β × β))
          (((Set.univ : Set (β × β)) \ Set.diagonal β))).toReal < ε) := by
  let S := couplingOffDiagonalCostSet P Q
  have hS_eq : totalVariationDistance P Q = sInf S := by
    simpa [S, couplingOffDiagonalCostSet] using
      totalVariationDistance_eq_sInf_couplings_offDiagonal P Q
  have hS_lt : sInf S < ε := by
    simpa [hS_eq] using hε
  -- Proof comment: once the infimum of coupling costs is strictly below `ε`, some concrete
  -- coupling must already lie below `ε`.
  obtain ⟨r, hrS, hrlt⟩ := exists_lt_of_csInf_lt
    (couplingOffDiagonalCostSet_nonempty P Q) hS_lt
  rcases hrS with ⟨π, hπ, rfl⟩
  exact ⟨π, hπ, hrlt⟩

/-- Helper for Theorem 17.56: the normalized restriction of `μ` to the fiber `ρ ⁻¹' {a}`. -/
private def normalizedFiberLaw [Nonempty E]
    (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) : ProbabilityMeasure E :=
  (μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).normalize

/-- Helper for Theorem 17.56: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_apply
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t)
    {s : Set E} (hs : MeasurableSet s) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) *
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E) s)) =
      ((μ : Measure E).restrict (ρ ⁻¹' {a})) s := by
  -- Proof comment: apply the finite-measure identity `mass • normalize = self` to the measurable
  -- set `s`, so the coercion boundary is crossed only once at the apply level.
  simpa [normalizedFiberLaw, FiniteMeasure.restrict_measure_eq, hs, smul_eq_mul] using
    congrArg (fun ν : FiniteMeasure E ↦ ((ν : Measure E) s))
      ((MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize
        (μ := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a}))).symm)

/-- Helper for Theorem 17.56: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_eq_restrict
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E))) =
      (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
  -- Proof comment: once the apply-level normalization bridge is available, the whole-measure
  -- statement is just extensionality on measurable sets.
  ext s hs
  simpa [smul_eq_mul] using
    fiberMass_smul_normalizedFiberLaw_apply (μ := μ) (ρ := ρ) a hs

/-- Helper for Theorem 17.56: given a label path, sample from the normalized fiber determined by
its `k`th label coordinate. -/
private noncomputable def normalizedFiberKernel [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) :
    Kernel t E where
  toFun a := normalizedFiberLaw μ ρ a
  measurable' := by
    let g : t → Measure E := fun a ↦ (normalizedFiberLaw μ ρ a : Measure E)
    have hg : Measurable g := measurable_of_finite g
    -- Proof comment: the finite label alphabet makes the ambient fiber kernel measurable by the
    -- standard `measurable_of_finite` bridge.
    simpa [g]
      using hg

/-- Helper for Theorem 17.56: evaluating the finite-label fiber kernel just recovers the
corresponding normalized ambient fiber law. -/
@[simp] private theorem normalizedFiberKernel_apply [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) (a : t) :
    normalizedFiberKernel μ ρ a = (normalizedFiberLaw μ ρ a : Measure E) :=
  rfl

/-- Helper for Theorem 17.56: the finite-label normalized-fiber kernel is Markov because every
fiber law is already a probability measure. -/
private instance instIsMarkovKernelNormalizedFiberKernel [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) :
    IsMarkovKernel (normalizedFiberKernel μ ρ) := by
  refine ⟨fun a ↦ ?_⟩
  -- Proof comment: each finite-label fiber is literally the probability measure
  -- `normalizedFiberLaw μ ρ a`.
  change IsProbabilityMeasure (normalizedFiberLaw μ ρ a : Measure E)
  infer_instance

/-- Helper for Theorem 17.56: given a label path, sample from the normalized fiber determined by
its `k`th label coordinate. -/
private noncomputable def normalizedFiberKernelAt [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    Kernel (ℕ → t) E where
  toFun ω := normalizedFiberLaw μ ρ (ω k)
  measurable' := by
    let g : t → Measure E := fun a ↦ (normalizedFiberLaw μ ρ a : Measure E)
    have hg : Measurable g := measurable_of_finite g
    -- Proof comment: the kernel depends on the path only through one finite-coordinate label, so
    -- measurability is just `measurable_of_finite` composed with coordinate evaluation.
    simpa [g, Function.comp] using hg.comp (measurable_pi_apply k)

/-- Helper for Theorem 17.56: evaluating the finite-label normalized-fiber kernel just recovers
the corresponding normalized fiber law. -/
@[simp] private theorem normalizedFiberKernelAt_apply [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) (ω : ℕ → t) :
    normalizedFiberKernelAt μ ρ k ω = (normalizedFiberLaw μ ρ (ω k) : Measure E) :=
  rfl

/-- Helper for Theorem 17.56: `normalizedFiberKernelAt` is the finite-label fiber kernel pulled
back along the `k`th coordinate evaluation map on the label path. -/
private theorem normalizedFiberKernelAt_eq_comap [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    normalizedFiberKernelAt μ ρ k =
      (normalizedFiberKernel μ ρ).comap (fun ω : ℕ → t ↦ ω k) (measurable_pi_apply k) := by
  rfl

/-- Helper for Theorem 17.56: the finite-label normalized-fiber kernel is Markov because every
fiber law is already a probability measure. -/
private instance instIsMarkovKernelNormalizedFiberKernelAt [Nonempty E]
    {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    IsMarkovKernel (normalizedFiberKernelAt μ ρ k) := by
  refine ⟨fun ω ↦ ?_⟩
  -- Proof comment: each kernel value is literally the probability measure
  -- `normalizedFiberLaw μ ρ (ω k)`.
  change IsProbabilityMeasure (normalizedFiberLaw μ ρ (ω k) : Measure E)
  infer_instance

/-- Helper for Theorem 17.56: summing the fiberwise normalized restrictions with their fiber
masses reconstructs the original measure. -/
private theorem sum_smul_normalizedFiberLaw_eq
    [Nonempty E] {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) :
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
      (μ : Measure E) := by
  have hpairwise : (Set.univ : Set t).Pairwise
      (Function.onFun Disjoint fun a : t ↦ ρ ⁻¹' {a}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 ?_
    intro x hxa hxb
    have hxa' : ρ x = a := by simpa using hxa
    have hxb' : ρ x = b := by simpa using hxb
    exact hab (hxa'.symm.trans hxb')
  have hrestrict :
      ((μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a})) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
    simpa [FiniteMeasure.restrict_measure_eq] using
      congrArg (fun ν : FiniteMeasure E ↦ (ν : Measure E))
        (MeasureTheory.FiniteMeasure.restrict_biUnion_finset
          (μ := μ.toFiniteMeasure) (T := Finset.univ) (s := fun a : t ↦ ρ ⁻¹' {a})
          (by simpa using hpairwise)
          (fun a ↦ hρmeas (measurableSet_singleton a)))
  have hUnion :
      (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) = Set.univ := by
    ext x
    simp
  calc
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using fiberMass_smul_normalizedFiberLaw_eq_restrict (μ := μ) (ρ := ρ) a
    _ = (μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) := by
      simpa using hrestrict.symm
    _ = (μ : Measure E) := by
      rw [hUnion, Measure.restrict_univ]

/-- Helper for Theorem 17.56: the measurable representative map pushes a probability measure
forward to a probability measure on the finite representative subtype. -/
private abbrev representativeMapLaw
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) :
    ProbabilityMeasure t :=
  μ.map (f := ρ) hρmeas.aemeasurable

/-- Helper for Theorem 17.56: the singleton masses of a finite coupling are the row and column
totals of its atom masses. -/
private theorem mapCouplingSingletonMarginals {t : Set E} [Fintype t]
    {P Q : ProbabilityMeasure E} {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    (∀ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a})) ∧
      (∀ b : t, ∑ a : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b})) := by
  rcases hν with ⟨hfst, hsnd⟩
  constructor
  · intro a
    -- Proof comment: evaluate the first marginal identity on the singleton `{a}` and rewrite the
    -- preimage of `{a}` under `Prod.fst` as the finite row sum of atoms.
    have hfstSingleton := congrArg (fun μ : Measure t ↦ μ {a}) hfst
    simpa [Measure.fst_apply, MeasureTheory.measure_preimage_fst_singleton_eq_sum] using
      hfstSingleton
  · intro b
    -- Proof comment: the second marginal identity gives the analogous column-sum formula.
    have hsndSingleton := congrArg (fun μ : Measure t ↦ μ {b}) hsnd
    simpa [Measure.snd_apply, MeasureTheory.measure_preimage_snd_singleton_eq_sum] using
      hsndSingleton

/-- Helper for Theorem 17.56: the mass of a quantization fiber equals the singleton mass of the
pushforward measure at that representative. -/
private theorem fiberMass_eq_mapSingleton
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
      (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
  -- Proof comment: the restricted finite measure has mass equal to the fiber mass, and that fiber
  -- mass is exactly the singleton mass of the pushforward.
  calc
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
        ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
      simpa using congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
        ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))
    _ = (μ : Measure E) (ρ ⁻¹' {a}) := by
      simp
    _ = (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
      symm
      simpa [representativeMapLaw] using
        (MeasureTheory.ProbabilityMeasure.map_apply' (ν := μ) (f := ρ) hρmeas.aemeasurable
          (A := {a}) (measurableSet_singleton a))

/-- Helper for Theorem 17.56: composing the finite-label fiber kernel with the representative
label law recovers the original ambient measure. -/
private theorem normalizedFiberKernel_comp_representativeMapLaw_eq [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E) (hρmeas : Measurable ρ) :
    (normalizedFiberKernel μ ρ) ∘ₘ
        (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) =
      (μ : Measure E) := by
  calc
    (normalizedFiberKernel μ ρ) ∘ₘ
        (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) =
        ∑ a : t,
          (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) •
            (((normalizedFiberKernel μ ρ a) : Measure E)) := by
          rw [Measure.comp_eq_sum_of_countable]
          simp [Measure.sum_fintype]
    _ =
        ∑ a : t,
          (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) •
            (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp
    _ =
        ∑ a : t,
          (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) •
            (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [← fiberMass_eq_mapSingleton (μ := μ) (hρmeas := hρmeas) a]
    _ = (μ : Measure E) := by
          simpa using sum_smul_normalizedFiberLaw_eq (μ := μ) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.56: if the `k`th label marginal of `Plabel` is the representative law of
`μ`, then sampling from the normalized fiber over that coordinate recovers `μ`. -/
private theorem normalizedFiberKernelAt_comp_eq_of_marginal [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E) (hρmeas : Measurable ρ)
    {Plabel : ProbabilityMeasure (ℕ → t)} {k : ℕ}
    (hk :
      Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) :
    (normalizedFiberKernelAt μ ρ k) ∘ₘ (Plabel : Measure (ℕ → t)) = (μ : Measure E) := by
  -- Proof comment: `normalizedFiberKernelAt` only reads the `k`th label coordinate, so after
  -- rewriting it as a pullback kernel the problem collapses to the representative marginal at time
  -- `k`.
  calc
    (normalizedFiberKernelAt μ ρ k) ∘ₘ (Plabel : Measure (ℕ → t)) =
        ((normalizedFiberKernel μ ρ) ∘ₖ
            Kernel.deterministic (fun ω : ℕ → t ↦ ω k) (measurable_pi_apply k)) ∘ₘ
          (Plabel : Measure (ℕ → t)) := by
          rw [normalizedFiberKernelAt_eq_comap, ← Kernel.comp_deterministic_eq_comap]
    _ =
        (normalizedFiberKernel μ ρ) ∘ₘ
          (Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t))) := by
          rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map]
    _ = (normalizedFiberKernel μ ρ) ∘ₘ
          (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) := by
          rw [hk]
    _ = (μ : Measure E) := by
          exact normalizedFiberKernel_comp_representativeMapLaw_eq
            (μ := μ) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.56: the label-path/base-state composition product keeps the original
label path as its first marginal. -/
private theorem fst_compProd_normalizedFiberKernelAt [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E)
    (Plabel : ProbabilityMeasure (ℕ → t)) (k : ℕ) :
    Measure.map Prod.fst
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      (Plabel : Measure (ℕ → t)) := by
  -- Proof comment: the first marginal of a composition product is always the original base
  -- measure, independently of the chosen fiber kernel.
  simpa [Measure.fst] using
    (Measure.fst_compProd
      (μ := (Plabel : Measure (ℕ → t))) (κ := normalizedFiberKernelAt μ ρ k))

/-- Helper for Theorem 17.56: if the `k`th label marginal of `Plabel` matches the representative
law of `μ`, then the second marginal of the label-path/base-state composition product is exactly
`μ`. -/
private theorem snd_compProd_normalizedFiberKernelAt_eq_of_marginal [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E) (hρmeas : Measurable ρ)
    {Plabel : ProbabilityMeasure (ℕ → t)} {k : ℕ}
    (hk :
      Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) :
    Measure.map Prod.snd
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      (μ : Measure E) := by
  -- Proof comment: pushing the second coordinate out of the composition product turns it into the
  -- kernel composition handled by the previous marginal-recovery theorem.
  rw [← Measure.snd]
  rw [Measure.snd_compProd]
  exact normalizedFiberKernelAt_comp_eq_of_marginal
    (μ := μ) (ρ := ρ) hρmeas hk

/-- Helper for Theorem 17.56: if the `k`th label marginal of `Plabel` matches the representative
law of `μ`, then the label-path/base-state composition product has exactly the expected two
marginals. -/
private theorem compProd_normalizedFiberKernelAt_marginals [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E)
    (hρmeas : Measurable ρ) {Plabel : ProbabilityMeasure (ℕ → t)} {k : ℕ}
    (hk :
      Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) :
    Measure.map Prod.fst
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      (Plabel : Measure (ℕ → t)) ∧
    Measure.map Prod.snd
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      (μ : Measure E) := by
  constructor
  · -- Proof comment: the first marginal of the composition product is always the original label
    -- path law, independently of the fiber kernel.
    exact fst_compProd_normalizedFiberKernelAt (μ := μ) (Plabel := Plabel) k
  · -- Proof comment: the second marginal is the ambient law recovered from the matched `k`th
    -- label marginal by the normalized-fiber reconstruction lemma.
    exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
      (μ := μ) (ρ := ρ) hρmeas hk

/-- Helper for Theorem 17.56: a coupling of the quantized pushforwards induces a finite sum of
product fiber laws on `E × E`. -/
private def liftedMapCoupling [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) (ρ : E → t) (ν : ProbabilityMeasure (t × t)) :
    Measure (E × E) :=
  ∑ a : t, ∑ b : t,
    (((ν : Measure (t × t)) {(a, b)}) •
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))))

/-- Helper for Theorem 17.56: the lifted finite-cell coupling has first marginal `P`. -/
private theorem liftedMapCoupling_fst_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν) = (P : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, _⟩
  -- Proof comment: `Prod.fst` turns each product cell into its first factor because the second
  -- normalized fiber law is a probability measure of total mass `1`.
  calc
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_fst_prod]
    _ = ∑ a : t, (∑ b : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ a : t, (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a}) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [hrows a]
    _ = ∑ a : t, (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a]
    _ = (P : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := P) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.56: the lifted finite-cell coupling has second marginal `Q`. -/
private theorem liftedMapCoupling_snd_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν) = (Q : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨_, hcols⟩
  -- Proof comment: the second marginal is the symmetric column-sum version of the first marginal
  -- calculation.
  calc
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_snd_prod]
    _ = ∑ b : t, ∑ a : t,
          ((ν : Measure (t × t)) {(a, b)}) •
            (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [Finset.sum_comm]
    _ = ∑ b : t, (∑ a : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ b : t, (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b}) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [hcols b]
    _ = ∑ b : t, (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b]
    _ = (Q : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := Q) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.56: inside the fiber of `a`, the preimage of a set `s` containing `a`
is the whole fiber. -/
private theorem preimage_inter_fiber_eq_fiber_of_mem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∈ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = ρ ⁻¹' {a} := by
  -- Proof comment: every point in the fiber already maps to `a`, so membership in `s` is
  -- automatic once `a ∈ s`.
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hxEq : ρ x = a := by simpa using hx
    refine ⟨?_, hx⟩
    simpa [hxEq] using hsa

/-- Helper for Theorem 17.56: if `a ∉ s`, then the preimage of `s` is disjoint from the fiber of
`a`. -/
private theorem preimage_inter_fiber_eq_empty_of_notMem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∉ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = (∅ : Set E) := by
  -- Proof comment: a point cannot simultaneously map to `a` and to a set excluding `a`.
  ext x
  constructor
  · intro hx
    have hxEq : ρ x = a := by simpa using hx.2
    have ha_mem : a ∈ s := by simpa [hxEq] using hx.1
    exact (hsa ha_mem).elim
  · intro hx
    simp at hx

/-- Helper for Theorem 17.56: pushing the restriction of `μ` to the fiber `ρ ⁻¹' {a}` forward
along `ρ` gives the scalar Dirac mass at `a` weighted by the fiber mass. -/
private theorem measure_map_restrict_fiber_eq_smul_dirac
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) (a : t) :
    Measure.map ρ ((μ : Measure E).restrict (ρ ⁻¹' {a})) =
      ((μ : Measure E) (ρ ⁻¹' {a})) • Measure.dirac a := by
  ext s hs
  by_cases hsa : a ∈ s
  · -- Proof comment: on a measurable set containing `a`, intersecting with the fiber leaves the
    -- full fiber, so the pushforward mass is exactly the fiber mass.
    rw [Measure.map_apply hρmeas hs, Measure.restrict_apply (hρmeas hs)]
    rw [preimage_inter_fiber_eq_fiber_of_mem hsa]
    simp [hsa]
  · -- Proof comment: if `a ∉ s`, the preimage of `s` misses the fiber completely, so both sides
    -- are zero.
    rw [Measure.map_apply hρmeas hs, Measure.restrict_apply (hρmeas hs)]
    rw [preimage_inter_fiber_eq_empty_of_notMem hsa]
    simp [hsa]

/-- Helper for Theorem 17.56: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    {s : Set t} (hs : MeasurableSet s) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) s =
      Measure.dirac a s := by
  let ν : FiniteMeasure E := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})
  have hmass :
      (μ : Measure E) (ρ ⁻¹' {a}) = ((ν.mass : ℝ≥0∞)) := by
    -- Proof comment: the fiber mass is exactly the mass of the restricted finite measure.
    calc
      (μ : Measure E) (ρ ⁻¹' {a}) = ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
        simp
      _ = ((ν.mass : ℝ≥0∞)) := by
        simpa [ν] using
          (congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
            ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))).symm
  have hν_ne : ν ≠ 0 := by
    -- Proof comment: positive fiber mass rules out the zero finite measure, so normalization
    -- reduces to scalar rescaling of the restricted fiber measure.
    intro hν
    have hν_mass_zero : ((ν.mass : ℝ≥0∞)) = 0 := by simpa [hν]
    exact ha <| by simpa [hmass] using hν_mass_zero
  -- Proof comment: rewrite the normalized fiber law as the inverse-mass scaling of the restricted
  -- fiber measure, then evaluate on `ρ ⁻¹' s` and split according to whether `s` contains `a`.
  rw [Measure.map_apply hρmeas hs]
  rw [normalizedFiberLaw, ν.toMeasure_normalize_eq_of_nonzero hν_ne, Measure.smul_apply]
  rw [show ((ν : Measure E) (ρ ⁻¹' s)) = ((μ : Measure E).restrict (ρ ⁻¹' {a}) (ρ ⁻¹' s)) by
        rfl]
  rw [Measure.restrict_apply (hρmeas hs)]
  by_cases hsa : a ∈ s
  · rw [preimage_inter_fiber_eq_fiber_of_mem hsa, hmass]
    have hν_mass_nnreal_ne : ν.mass ≠ 0 := by
      exact (MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne
    have hν_mass_ne : ((ν.mass : ℝ≥0∞)) ≠ 0 := by
      exact ENNReal.coe_ne_zero.2 ((MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne)
    have hν_univ_eq : ((ν : Measure E) Set.univ) = ((ν.mass : ℝ≥0∞)) := by
      simpa using (MeasureTheory.FiniteMeasure.ennreal_mass (μ := ν)).symm
    simp [hsa]
    rw [hν_univ_eq]
    rw [ENNReal.coe_inv hν_mass_nnreal_ne]
    exact ENNReal.inv_mul_cancel hν_mass_ne (by simp)
  · rw [preimage_inter_fiber_eq_empty_of_notMem hsa]
    simp [hsa]

/-- Helper for Theorem 17.56: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) =
      Measure.dirac a := by
  -- Proof comment: the measure equality is now the direct extensional wrapper around the
  -- apply-level normalization bridge.
  ext s hs
  simpa using map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    (μ := μ) (hρmeas := hρmeas) a ha hs

/-- Helper for Theorem 17.56: if both fiber masses are nonzero, then pushing the corresponding
product fiber law forward by the pair of representatives gives the Dirac mass at that pair. -/
private theorem map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] {t : Set E} (P Q : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) (a b : t)
    (ha :
      (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    (hb :
      (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))) =
        Measure.dirac (a, b) := by
  -- Proof comment: rewrite the pair pushforward as the product of the two marginal
  -- pushforwards, then collapse both factors to Dirac masses on their representatives.
  have hmap :
      Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
          ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
              ProbabilityMeasure (E × E)) : Measure (E × E))) =
        (Measure.map ρ (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E))).prod
          (Measure.map ρ (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E))) := by
    simpa using
      (Measure.map_prod_map
        (μa := (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)))
        (μc := (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)))
        hρmeas hρmeas).symm
  rw [hmap]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := P) (hρmeas := hρmeas) a ha]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := Q) (hρmeas := hρmeas) b hb]
  exact Measure.dirac_prod_dirac

/-- Helper for Theorem 17.56: pushing the lifted finite-cell coupling forward by the pair of
representatives recovers the original finite coupling `ν`. -/
private theorem liftedMapCoupling_map_representatives_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
      (ν : Measure (t × t)) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, hcols⟩
  have hpair_meas : Measurable (fun z : E × E ↦ (ρ z.1, ρ z.2)) := by
    fun_prop
  have hcell_zero_of_left_mass_zero :
      ∀ a b : t,
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b ha0
    -- Proof comment: if the `a`-fiber has zero mass, then the whole `a`-row of the coupling has
    -- zero mass, so in particular the `(a,b)` cell coefficient vanishes.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) := by
      exact Finset.single_le_sum
        (f := fun b' : t ↦ ((ν : Measure (t × t)) {(a, b')}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ b)
    have hrow0 :
        ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) = 0 := by
      rw [hrows a, ← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a, ha0]
    exact le_antisymm (by simpa [hrow0] using hle) bot_le
  have hcell_zero_of_right_mass_zero :
      ∀ a b : t,
        (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b hb0
    -- Proof comment: the same singleton-sum argument on columns kills cells whose `b`-fiber has
    -- zero `Q`-mass.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) := by
      exact Finset.single_le_sum
        (f := fun a' : t ↦ ((ν : Measure (t × t)) {(a', b)}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ a)
    have hcol0 :
        ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) = 0 := by
      rw [hcols b, ← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b, hb0]
    exact le_antisymm (by simpa [hcol0] using hle) bot_le
  have hcell :
      ∀ a b : t,
        Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
            ((((ν : Measure (t × t)) {(a, b)}) •
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))))) =
          ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
    intro a b
    by_cases ha0 :
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0
    · have hcoeff_zero := hcell_zero_of_left_mass_zero a b ha0
      -- Proof comment: a zero row coefficient annihilates the whole mapped cell.
      have hmap_smul :
          Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
              ((((ν : Measure (t × t)) {(a, b)}) •
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))))) =
            ((ν : Measure (t × t)) {(a, b)}) •
              Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))) := by
        simpa using
          (Measure.map_smul
            (((ν : Measure (t × t)) {(a, b)}))
            ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                ProbabilityMeasure (E × E)) : Measure (E × E)))
            (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
      rw [hmap_smul]
      simp [hcoeff_zero]
    · by_cases hb0 :
          (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0
      · have hcoeff_zero := hcell_zero_of_right_mass_zero a b hb0
        -- Proof comment: a zero column coefficient gives the symmetric annihilation.
        have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        simp [hcoeff_zero]
      · -- Proof comment: when both fiber masses are positive, the mapped product cell collapses
        -- to the Dirac mass at the representative pair.
        have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        rw [map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
          (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) a b ha0 hb0]
  -- Proof comment: after each cell has been identified with its weighted Dirac mass, the whole
  -- lifted pushforward is the canonical sum-of-Diracs expansion of `ν` on the finite target.
  calc
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
        ∑ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro b hb
      simpa using hcell a b
    _ = ∑ p : t × t, ((ν : Measure (t × t)) {p}) • Measure.dirac p := by
      simpa [Fintype.sum_prod_type]
    _ = (ν : Measure (t × t)) := by
      simpa [Measure.sum_fintype] using
        (Measure.sum_smul_dirac (μ := (ν : Measure (t × t))))

/-- Helper for Theorem 17.56: a finite coupling of the representative laws lifts to an ambient
coupling of the original laws while preserving the representative pair map. -/
private theorem liftedRepresentativeCoupling
    [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    ∃ π : ProbabilityMeasure (E × E),
      IsCoupling π P Q ∧
        Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (π : Measure (E × E)) =
          (ν : Measure (t × t)) := by
  let π : ProbabilityMeasure (E × E) :=
    { val := liftedMapCoupling P Q ρ ν
      property := by
        -- Proof comment: the first marginal already has total mass one, so the lifted measure is
        -- automatically a probability measure.
        have hmass :
            (liftedMapCoupling P Q ρ ν) Set.univ = 1 := by
          calc
            (liftedMapCoupling P Q ρ ν) Set.univ =
                (Measure.map Prod.fst (liftedMapCoupling P Q ρ ν)) Set.univ := by
                  rw [Measure.map_apply measurable_fst]
                  · simp
                  · simp
            _ = (P : Measure E) Set.univ := by
                  rw [liftedMapCoupling_fst_eq
                    (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν]
            _ = 1 := by simp
        exact IsProbabilityMeasure.mk hmass }
  refine ⟨π, ?_, ?_⟩
  · constructor
    · -- Proof comment: the first marginal identity is built into the lifted fiber decomposition.
      simpa [π] using
        liftedMapCoupling_fst_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν
    · -- Proof comment: the second marginal identity is the symmetric companion.
      simpa [π] using
        liftedMapCoupling_snd_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν
  · -- Proof comment: the representative-pair pushforward remembers exactly the original finite
    -- coupling `ν`.
    simpa [π] using
      liftedMapCoupling_map_representatives_eq
        (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν

/-- Helper for Theorem 17.56: each finite prefix space has a canonical measurable projection to
its time-`0` coordinate. -/
private def prefixHead {β : Type*} [MeasurableSpace β] (n : ℕ) :
    (Π _ : Finset.Iic n, β) → β :=
  fun z ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩

/-- Helper for Theorem 17.56: the head-coordinate projection on each prefix space is measurable. -/
private theorem measurable_prefixHead {β : Type*} [MeasurableSpace β] (n : ℕ) :
    Measurable (prefixHead (β := β) n) := by
  let i0 : Finset.Iic n := ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩
  simpa [prefixHead] using
    (measurable_pi_apply i0)

/-- Helper for Theorem 17.56: from each finite history, the next-step kernel only reads the head
coordinate. -/
private def headIndexedHistoryKernel {β : Type*} [MeasurableSpace β]
    (κ : ℕ → Kernel β β) :
    (n : ℕ) → Kernel (Π _ : Finset.Iic n, β) β :=
  fun n ↦ Kernel.comap (κ n) (prefixHead (β := β) n) (measurable_prefixHead (β := β) n)

/-- Helper for Theorem 17.56: if each `κ n` is Markov, then the head-indexed history kernels are
also Markov. -/
private instance instIsMarkovKernelHeadIndexedHistoryKernel
    {β : Type*} [MeasurableSpace β] (κ : ℕ → Kernel β β) [∀ n, IsMarkovKernel (κ n)] :
    ∀ n, IsMarkovKernel (headIndexedHistoryKernel κ n) := by
  intro n
  dsimp [headIndexedHistoryKernel]
  infer_instance

/-- Helper for Theorem 17.56: a trajectory law whose transition kernels only read the initial
coordinate keeps the time-`0` marginal equal to the starting law. -/
private theorem headIndexedTrajMeasure_map_eval_zero
    {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel β β) [∀ n, IsMarkovKernel (κ n)] :
    let P : Measure (ℕ → β) :=
      Kernel.trajMeasure (X := fun _ : ℕ ↦ β) μ (headIndexedHistoryKernel κ)
    P.map (Function.eval 0) = μ := by
  let η := headIndexedHistoryKernel κ
  let P : Measure (ℕ → β) := Kernel.trajMeasure (X := fun _ : ℕ ↦ β) μ η
  have hprefix :
      P.map (Preorder.frestrictLe 0) =
        μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ β)).symm := by
    -- Proof comment: the zeroth prefix of the trajectory measure is exactly the singleton
    -- history built from the starting law `μ`.
    have hprefix0 :=
      Kernel.trajMeasure_map_frestrictLe (X := fun _ : ℕ ↦ β) (μ₀ := μ) (κ := η) 0
    simpa [P, Kernel.partialTraj_self] using hprefix0
  calc
    P.map (Function.eval 0) =
        (P.map (Preorder.frestrictLe 0)).map
          (fun z : Finset.Iic 0 → β ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = μ := by
          rw [hprefix, Measure.map_map (by fun_prop) (by fun_prop)]
          ext s hs
          rw [Measure.map_apply (by fun_prop) hs]
          have hpre :
              ((fun z : Finset.Iic 0 → β ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
                (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ β)).symm) ⁻¹' s = s := by
            ext x
            simp
          rw [hpre]

/-- Helper for Theorem 17.56: pushing a composition-product with a `Kernel.comap` through the
base map recovers the ambient composition-product. -/
private theorem compProd_map_base_eq_compProd
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ]
    (f : A → B) (hf : Measurable f)
    (κ : Kernel B C) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ Kernel.comap κ f hf).map (Prod.map f id)) =
      μ.map f ⊗ₘ κ := by
  -- Proof comment: rewrite the composition-product as a kernel composition, push the base map
  -- through the product kernel, and then reassemble the transported composition-product.
  calc
    ((μ ⊗ₘ Kernel.comap κ f hf).map (Prod.map f id)) =
        (Kernel.deterministic (Prod.map f id) (by fun_prop)) ∘ₘ
          (μ ⊗ₘ Kernel.comap κ f hf) := by
            rw [Measure.deterministic_comp_eq_map]
    _ = ((Kernel.deterministic (Prod.map f id) (by fun_prop)) ∘ₖ
          (Kernel.id ×ₖ Kernel.comap κ f hf)) ∘ₘ μ := by
            rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc]
    _ = (((Kernel.id ×ₖ Kernel.comap κ f hf).map (Prod.map f id)) ∘ₘ μ) := by
            rw [Kernel.deterministic_comp_eq_map]
    _ = (((Kernel.id.map f) ×ₖ Kernel.comap κ f hf) ∘ₘ μ) := by
            rw [Kernel.map_prod_eq (κ := Kernel.id) (η := Kernel.comap κ f hf) hf]
    _ = (((Kernel.id.comap f hf) ×ₖ Kernel.comap κ f hf) ∘ₘ μ) := by
            rw [Kernel.id_map hf, Kernel.id_comap hf]
    _ = (((Kernel.id ×ₖ κ).comap f hf) ∘ₘ μ) := by
            rw [Kernel.comap_prod]
    _ = (((Kernel.id ×ₖ κ) ∘ₖ Kernel.deterministic f hf) ∘ₘ μ) := by
            rw [Kernel.comp_deterministic_eq_comap]
    _ = ((Kernel.id ×ₖ κ) ∘ₘ ((Kernel.deterministic f hf) ∘ₘ μ)) := by
            rw [← Measure.comp_assoc]
    _ = ((Kernel.id ×ₖ κ) ∘ₘ μ.map f) := by
            rw [Measure.deterministic_comp_eq_map]
    _ = μ.map f ⊗ₘ κ := by
            rw [Measure.compProd_eq_comp_prod]

/-- Helper for Theorem 17.56: the trajectory measure driven by head-indexed kernels. -/
private abbrev headIndexedPathMeasure
    {β : Type*} [MeasurableSpace β]
    (μ : Measure β) (κ : ℕ → Kernel β β) [∀ n, IsMarkovKernel (κ n)] :
    Measure (ℕ → β) :=
  Kernel.trajMeasure (X := fun _ : ℕ ↦ β) μ (headIndexedHistoryKernel κ)

/-- Helper for Theorem 17.56: package the prefix up to time `n` together with time `n + 1`. -/
private def prefixAndNext
    {β : Type*} [MeasurableSpace β] (n : ℕ) :
    (ℕ → β) → (Π _ : Finset.Iic n, β) × β :=
  fun ω ↦ (Preorder.frestrictLe n ω, ω (n + 1))

/-- Helper for Theorem 17.56: package time `0` together with time `n + 1`. -/
private def headAndNext
    {β : Type*} (n : ℕ) : (ℕ → β) → β × β :=
  fun ω ↦ (ω 0, ω (n + 1))

/-- Helper for Theorem 17.56: a path law on finite representative labels canonically lifts to
ambient pair laws at every time once the head and coordinate label marginals are fixed. -/
private theorem existsLiftedRepresentativePairLawsOfPathLabelLaw
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E]
    {t : Set E} [Fintype t]
    {ρ : E → t} (hρmeas : Measurable ρ)
    (P0 : ProbabilityMeasure E) (Pn : ℕ → ProbabilityMeasure E)
    (Plabel : ProbabilityMeasure (ℕ → t))
    (hhead :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw P0 hρmeas : ProbabilityMeasure t) : Measure t))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (Plabel : Measure (ℕ → t)) =
          ((representativeMapLaw (Pn n) hρmeas : ProbabilityMeasure t) : Measure t)) :
    ∃ π : ℕ → ProbabilityMeasure (E × E),
      ∀ n : ℕ,
        IsCoupling (π n) P0 (Pn n) ∧
          Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (π n : Measure (E × E)) =
            Measure.map (headAndNext (β := t) n) (Plabel : Measure (ℕ → t)) := by
  have hpair :
      ∀ n : ℕ,
        ∃ πn : ProbabilityMeasure (E × E),
          IsCoupling πn P0 (Pn n) ∧
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (πn : Measure (E × E)) =
              Measure.map (headAndNext (β := t) n) (Plabel : Measure (ℕ → t)) := by
    intro n
    have hheadAndNextMeas : Measurable (headAndNext (β := t) n) := by
      -- Proof comment: `headAndNext` is the product of two evaluation maps on the label path.
      fun_prop
    let νlabel : ProbabilityMeasure (t × t) :=
      Plabel.map
        (f := headAndNext (β := t) n) hheadAndNextMeas.aemeasurable
    have hνlabel :
        IsCoupling νlabel (representativeMapLaw P0 hρmeas)
          (representativeMapLaw (Pn n) hρmeas) := by
      constructor
      · -- Proof comment: the first marginal of the label pair law is the time-`0` label law.
        change
          Measure.map Prod.fst
              (Measure.map (headAndNext (β := t) n) (Plabel : Measure (ℕ → t))) =
            ((representativeMapLaw P0 hρmeas : ProbabilityMeasure t) : Measure t)
        rw [Measure.map_map measurable_fst]
        · simpa [headAndNext, Function.comp] using hhead
        · exact hheadAndNextMeas
      · -- Proof comment: the second marginal is the time-`n + 1` label law.
        change
          Measure.map Prod.snd
              (Measure.map (headAndNext (β := t) n) (Plabel : Measure (ℕ → t))) =
            ((representativeMapLaw (Pn n) hρmeas : ProbabilityMeasure t) : Measure t)
        rw [Measure.map_map measurable_snd]
        · simpa [headAndNext, Function.comp] using hcoord n
        · exact hheadAndNextMeas
    -- Proof comment: once the finite label pair law is identified, the existing fiber-lifting API
    -- already turns it into an ambient coupling with the same representative pair map.
    simpa [νlabel] using
      liftedRepresentativeCoupling
        (P := P0) (Q := Pn n) (ρ := ρ) (hρmeas := hρmeas) hνlabel
  choose π hπ using hpair
  exact ⟨π, hπ⟩

/-- Helper for Theorem 17.56: the off-diagonal subset of `t × t` is measurable whenever equality
is measurable on `t`. -/
private theorem measurableSet_offDiagonal
    {t : Type*} [MeasurableSpace t] [MeasurableEq t] :
    MeasurableSet {p : t × t | p.1 ≠ p.2} := by
  have hdiagEq : MeasurableSet ({p : t × t | p.1 = p.2} : Set (t × t)) := by
    simpa [Set.diagonal] using (measurableSet_diagonal : MeasurableSet (Set.diagonal t))
  -- Proof comment: the off-diagonal is just the complement of the measurable diagonal.
  convert hdiagEq.compl using 1

/-- Helper for Theorem 17.56: if label equality forces ambient distance at most `r`, then the
ambient `r`-bad set is contained in the preimage of the label off-diagonal. -/
private theorem badMass_le_labelOffDiagonal_of_eq_imp_dist_le
    {E t : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    [MeasurableSpace t] [MeasurableEq t]
    {ρ : E → t} (hρmeas : Measurable ρ)
    {π : ProbabilityMeasure (E × E)} {ν : ProbabilityMeasure (t × t)} {r : ℝ}
    (hmap :
      Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (π : Measure (E × E)) =
        (ν : Measure (t × t)))
    (hdiam : ∀ ⦃x y : E⦄, ρ x = ρ y → dist x y ≤ r) :
    (π : Measure (E × E)) {z | r < dist z.1 z.2} ≤
      (ν : Measure (t × t)) {p | p.1 ≠ p.2} := by
  have hpairMeas : Measurable (fun z : E × E ↦ (ρ z.1, ρ z.2)) := by
    -- Proof comment: the label-pair map is measurable coordinatewise.
    fun_prop
  have hneq : MeasurableSet {p : t × t | p.1 ≠ p.2} := by
    exact measurableSet_offDiagonal (t := t)
  have hsubset :
      {z : E × E | r < dist z.1 z.2} ⊆
        (fun z : E × E ↦ (ρ z.1, ρ z.2)) ⁻¹' {p : t × t | p.1 ≠ p.2} := by
    intro z hz
    -- Proof comment: if two ambient points share the same label, the diameter control excludes
    -- membership in the bad-distance event.
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro hEq
    exact (not_lt_of_ge (hdiam hEq)) hz
  calc
    (π : Measure (E × E)) {z | r < dist z.1 z.2} ≤
        (π : Measure (E × E))
          ((fun z : E × E ↦ (ρ z.1, ρ z.2)) ⁻¹' {p : t × t | p.1 ≠ p.2}) := by
          exact measure_mono hsubset
    _ = Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (π : Measure (E × E))
          {p : t × t | p.1 ≠ p.2} := by
          symm
          exact Measure.map_apply hpairMeas hneq
    _ = (ν : Measure (t × t)) {p | p.1 ≠ p.2} := by rw [hmap]

/-- Helper for Theorem 17.56: a label path law can be lifted to ambient pair couplings whose
dyadic bad masses are controlled by the label off-diagonal probabilities. -/
private theorem existsLiftedRepresentativePairLawsWithBadMassControl
    [Nonempty E] {t : Set E} [Fintype t] [MeasurableEq t]
    {ρ : E → t} (hρmeas : Measurable ρ)
    (P0 : ProbabilityMeasure E) (Pn : ℕ → ProbabilityMeasure E)
    (Plabel : ProbabilityMeasure (ℕ → t))
    (hhead :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw P0 hρmeas : ProbabilityMeasure t) : Measure t))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (Plabel : Measure (ℕ → t)) =
          ((representativeMapLaw (Pn n) hρmeas : ProbabilityMeasure t) : Measure t))
    {r : ℝ}
    (hdiam : ∀ ⦃x y : E⦄, ρ x = ρ y → dist x y ≤ r) :
    ∃ π : ℕ → ProbabilityMeasure (E × E),
      ∀ n : ℕ,
        IsCoupling (π n) P0 (Pn n) ∧
          (π n : Measure (E × E)) {z | r < dist z.1 z.2} ≤
            (Measure.map (headAndNext (β := t) n) (Plabel : Measure (ℕ → t)))
              {p | p.1 ≠ p.2} := by
  obtain ⟨π, hπ⟩ :=
    existsLiftedRepresentativePairLawsOfPathLabelLaw
      (hρmeas := hρmeas) P0 Pn Plabel hhead hcoord
  refine ⟨π, ?_⟩
  intro n
  rcases hπ n with ⟨hCoupling, hmap⟩
  have hheadAndNextMeas : Measurable (headAndNext (β := t) n) := by
    -- Proof comment: the time-`0`/time-`n+1` label pair is measurable by coordinate evaluation on
    -- the finite path space.
    fun_prop
  let νlabel : ProbabilityMeasure (t × t) :=
    Plabel.map
      (f := headAndNext (β := t) n) hheadAndNextMeas.aemeasurable
  refine ⟨hCoupling, ?_⟩
  -- Proof comment: once the ambient pair remembers exactly the label pair law, the bad-mass
  -- estimate is the generic label-off-diagonal transport lemma.
  exact badMass_le_labelOffDiagonal_of_eq_imp_dist_le
    (hρmeas := hρmeas) (π := π n) (ν := νlabel) (r := r)
    (by simpa [νlabel] using hmap) hdiam

/-- Helper for Theorem 17.56: split a successor history into its prefix and final state. -/
private noncomputable def succHistoryEquivLocal
    {β : Type*} [MeasurableSpace β] (n : ℕ) :
    (Π _ : Finset.Iic (n + 1), β) ≃ᵐ ((Π _ : Finset.Iic n, β) × β) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ β) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n).symm)

/-- Helper for Theorem 17.56: `succHistoryEquivLocal` records the truncated prefix together with
the final state of a successor history. -/
@[simp] private theorem succHistoryEquivLocal_apply
    {β : Type*} [MeasurableSpace β] (n : ℕ)
    (z : Π _ : Finset.Iic (n + 1), β) :
    succHistoryEquivLocal (β := β) n z =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ β) (Nat.le_succ n) z,
        z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: unfold the measurable equivalence and read off its two coordinates.
  rfl

/-- Helper for Theorem 17.56: gluing a prefix history and one-point tail and then splitting again
recovers the stored pair. -/
@[simp] private theorem succHistoryEquivLocal_apply_IicProdIoc
    {β : Type*} [MeasurableSpace β] (n : ℕ)
    (z : (Π _ : Finset.Iic n, β) × (Π _ : Finset.Ioc n (n + 1), β)) :
    succHistoryEquivLocal (β := β) n
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ β) n (n + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n).symm z := by
  rcases z with ⟨z₁, z₂⟩
  ext i
  · -- Proof comment: the first component is exactly the stored prefix restriction.
    simpa [succHistoryEquivLocal_apply] using
      congrFun
        (congrFun
          (frestrictLe₂_comp_IicProdIoc (X := fun _ : ℕ ↦ β) (hab := Nat.le_succ n))
          (z₁, z₂))
        i
  · -- Proof comment: the second component is the unique coordinate in the singleton tail.
    simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Theorem 17.56: package the pointwise normalization of `succHistoryEquivLocal` as the
function equality consumed by `Kernel.map_comp_right`. -/
private theorem succHistoryEquivLocal_comp_IicProdIoc
    {β : Type*} [MeasurableSpace β] (n : ℕ) :
    succHistoryEquivLocal (β := β) n ∘
        _root_.IicProdIoc (X := fun _ : ℕ ↦ β) n (n + 1) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n).symm := by
  -- Proof comment: the previous pointwise identity is exactly the composed-map normal form needed
  -- for the kernel rewrite.
  funext z
  simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc (β := β) n z

/-- Helper for Theorem 17.56: after splitting a one-step partial trajectory through
`succHistoryEquivLocal`, the result is the stored prefix together with the next-step kernel. -/
private theorem partialTraj_succ_self_map_succHistoryEquivLocal
    {β : Type*} [MeasurableSpace β] {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, β) β)
    [IsSFiniteKernel
      ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n))] :
    ((ProbabilityTheory.Kernel.partialTraj
        (X := fun _ : ℕ ↦ β) (κ := κhist) n (n + 1)).map
        (succHistoryEquivLocal (β := β) n) :
          Kernel (Π _ : Finset.Iic n, β)
            ((Π _ : Finset.Iic n, β) × β)) =
      Kernel.id ×ₖ κhist n := by
  -- Proof comment: rewrite the one-step partial trajectory by `partialTraj_succ_self`, then
  -- collapse the singleton tail coordinate through `succHistoryEquivLocal`.
  rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
  rw [← Kernel.map_comp_right
    (κ := Kernel.id ×ₖ
      ((κhist n).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n)))
    (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ β) n (n + 1))
    (g := succHistoryEquivLocal (β := β) n)
    measurable_IicProdIoc
    (by fun_prop)]
  rw [succHistoryEquivLocal_comp_IicProdIoc (β := β) n]
  rw [← Kernel.map_prod_map _ _ measurable_id
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n)).measurable]
  rw [Kernel.map_id]
  rw [← Kernel.map_comp_right
    (κ := κhist n)
    (f := MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n)
    (g := (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n).symm)
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n).measurable
    (MeasurableEquiv.symm
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ β) n)).measurable]
  simpa using Kernel.map_id (κhist n)

/-- Helper for Theorem 17.56: `prefixAndNext` is the successor-history split applied to the
canonical prefix of length `n + 1`. -/
private theorem prefixAndNext_eq_succHistoryEquivLocal_comp_frestrictLe
    {β : Type*} [MeasurableSpace β] (n : ℕ) :
    prefixAndNext (β := β) n =
      succHistoryEquivLocal (β := β) n ∘ Preorder.frestrictLe (n + 1) := by
  funext ω
  ext i
  · -- Proof comment: the prefix component is the restriction of the longer history to `Iic n`.
    simp [prefixAndNext, succHistoryEquivLocal_apply, Preorder.frestrictLe]
  · -- Proof comment: the terminal component is exactly time `n + 1`.
    simp [prefixAndNext, succHistoryEquivLocal_apply, Preorder.frestrictLe]

/-- Helper for Theorem 17.56: under the head-indexed trajectory law, the pair consisting of the
prefix up to time `n` and time `n + 1` is the composition-product of the prefix law with the
head-indexed next-step kernel. -/
private theorem headIndexedPathMeasure_map_prefixAndNext
    {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel β β) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) :
    (headIndexedPathMeasure μ κ).map (prefixAndNext n) =
      ((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)) ⊗ₘ
        headIndexedHistoryKernel κ n := by
  let η := headIndexedHistoryKernel κ
  let μ0 : Measure (Π _ : Finset.Iic 0, β) :=
    μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ β)).symm
  have hprefixLong :
      (headIndexedPathMeasure μ κ).map (Preorder.frestrictLe (n + 1)) =
        (ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)) ∘ₘ μ0 := by
    simpa [headIndexedPathMeasure, η, μ0] using
      (ProbabilityTheory.Kernel.trajMeasure_map_frestrictLe
        (X := fun _ : ℕ ↦ β) (μ₀ := μ) (κ := η) (n := n + 1))
  have hprefixShort :
      (headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n) =
        (ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n) ∘ₘ μ0 := by
    simpa [headIndexedPathMeasure, η, μ0] using
      (ProbabilityTheory.Kernel.trajMeasure_map_frestrictLe
        (X := fun _ : ℕ ↦ β) (μ₀ := μ) (κ := η) (n := n))
  have hkernelSplit :
      ((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)).map
        (succHistoryEquivLocal (β := β) n)) =
        (Kernel.id ×ₖ η n) ∘ₖ
          ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n := by
    -- Proof comment: factor the long partial trajectory through the final one-step update and
    -- normalize that terminal update with the previous one-step split lemma.
    calc
      ((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)).map
          (succHistoryEquivLocal (β := β) n)) =
          (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η n (n + 1)) ∘ₖ
              ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n).map
                (succHistoryEquivLocal (β := β) n)) := by
            rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
              (X := fun _ : ℕ ↦ β) (κ := η) (a := 0) (b := n) (Nat.zero_le n)]
      _ =
          ((((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η n (n + 1)).map
              (succHistoryEquivLocal (β := β) n))) ∘ₖ
                ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n) := by
            rw [Kernel.map_comp]
      _ =
          (Kernel.id ×ₖ η n) ∘ₖ
            ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n := by
            rw [partialTraj_succ_self_map_succHistoryEquivLocal (β := β) (κhist := η)]
  calc
    (headIndexedPathMeasure μ κ).map (prefixAndNext n) =
        ((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe (n + 1))).map
          (succHistoryEquivLocal (β := β) n) := by
            rw [prefixAndNext_eq_succHistoryEquivLocal_comp_frestrictLe (β := β) n]
            rw [Measure.map_map
              (succHistoryEquivLocal (β := β) n).measurable (by fun_prop)]
    _ =
        ((((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)) ∘ₘ μ0)).map
          (succHistoryEquivLocal (β := β) n)) := by
            rw [hprefixLong]
    _ =
        (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)).map
          (succHistoryEquivLocal (β := β) n)) ∘ₘ μ0) := by
            -- Proof comment: express the outer map as composition with the deterministic kernel,
            -- then push that deterministic kernel through the trajectory kernel.
            calc
              Measure.map (succHistoryEquivLocal (β := β) n)
                  (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)) ∘ₘ
                    μ0)) =
                  (Kernel.deterministic (succHistoryEquivLocal (β := β) n)
                    (succHistoryEquivLocal (β := β) n).measurable) ∘ₘ
                      (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1))
                        ∘ₘ μ0)) := by
                    symm
                    simpa using
                      (Measure.deterministic_comp_eq_map
                        (μ := ((ProbabilityTheory.Kernel.partialTraj
                          (X := fun _ : ℕ ↦ β) η 0 (n + 1)) ∘ₘ μ0))
                        (f := succHistoryEquivLocal (β := β) n)
                        ((succHistoryEquivLocal (β := β) n).measurable))
              _ =
                  (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 (n + 1)).map
                    (succHistoryEquivLocal (β := β) n)) ∘ₘ μ0) := by
                    rw [Measure.comp_assoc, Kernel.deterministic_comp_eq_map]
    _ =
        ((((Kernel.id ×ₖ η n) ∘ₖ
          ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n)) ∘ₘ μ0) := by
            rw [hkernelSplit]
    _ =
        ((Kernel.id ×ₖ η n) ∘ₘ
          ((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n) ∘ₘ μ0)) := by
            rw [← Measure.comp_assoc]
    _ =
        (((ProbabilityTheory.Kernel.partialTraj (X := fun _ : ℕ ↦ β) η 0 n) ∘ₘ μ0) ⊗ₘ η n) := by
            rw [Measure.compProd_eq_comp_prod]
    _ =
        ((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)) ⊗ₘ η n := by
            rw [hprefixShort]

/-- Helper for Theorem 17.56: under the head-indexed trajectory law, the pair consisting of time
`0` and time `n + 1` has the composition-product law `μ ⊗ₘ κ n`. -/
private theorem headIndexedPathMeasure_map_headAndNext
    {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel β β) [∀ n, IsMarkovKernel (κ n)]
    (n : ℕ) :
    Measure.map (headAndNext n) (headIndexedPathMeasure μ κ) = μ ⊗ₘ κ n := by
  have hprefixHead :
      (((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)).map
        (prefixHead (β := β) n)) = μ := by
    -- Proof comment: extracting the head from the length-`n` prefix is the same as reading the
    -- time-`0` coordinate of the full trajectory.
    rw [Measure.map_map (measurable_prefixHead (β := β) n) (by fun_prop)]
    simpa [headIndexedPathMeasure, prefixHead, Function.comp] using
      (headIndexedTrajMeasure_map_eval_zero (β := β) (μ := μ) (κ := κ))
  have hdecompose :
      headAndNext (β := β) n =
        Prod.map (prefixHead (β := β) n) (id : β → β) ∘ prefixAndNext (β := β) n := by
    -- Proof comment: the pair `(ω 0, ω (n + 1))` is obtained by taking the head of the stored
    -- prefix and pairing it with the terminal state.
    funext ω
    simp [headAndNext, prefixAndNext, prefixHead]
  calc
    Measure.map (headAndNext n) (headIndexedPathMeasure μ κ) =
        (Measure.map (Prod.map (prefixHead (β := β) n) (id : β → β))
          (Measure.map (prefixAndNext n) (headIndexedPathMeasure μ κ))) := by
            have hprodMap :
                Measurable (Prod.map (prefixHead (β := β) n) (id : β → β)) := by
              exact Measurable.prodMap (measurable_prefixHead (β := β) n) measurable_id
            rw [hdecompose, Measure.map_map hprodMap (by fun_prop)]
    _ =
        Measure.map (Prod.map (prefixHead (β := β) n) (id : β → β))
          ((((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)) ⊗ₘ
            headIndexedHistoryKernel κ n)) := by
              rw [headIndexedPathMeasure_map_prefixAndNext (β := β) (μ := μ) (κ := κ) n]
    _ =
        ((((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)).map
          (prefixHead (β := β) n)) ⊗ₘ κ n) := by
            simpa [headIndexedHistoryKernel] using
              (compProd_map_base_eq_compProd
                (((headIndexedPathMeasure μ κ).map (Preorder.frestrictLe n)))
                (prefixHead (β := β) n)
                (measurable_prefixHead (β := β) n)
                (κ n))
    _ = μ ⊗ₘ κ n := by rw [hprefixHead]

/-- Helper for Theorem 17.56: the closed dyadic tail event on Hilbert-cube path space asking that
all coordinates from time `N + 1` onward stay within the dyadic radius `(1 / 2)^m` of time `0`. -/
private def dyadicTailEvent (m N : ℕ) : Set (ℕ → (ℕ → unitInterval)) :=
  {ω | ∀ n ≥ N,
      @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤ (1 / 2 : ℝ) ^ m}

/-- Helper for Theorem 17.56: the dyadic tail events increase with the threshold index, so
continuity from below can recover a deterministic high-probability tail cutoff from an almost-sure
eventual dyadic bound. -/
private theorem monotone_dyadicTailEvent (m : ℕ) :
    Monotone (dyadicTailEvent m) := by
  intro N M hNM ω hω n hn
  exact hω n (le_trans hNM hn)

/-- Helper for Theorem 17.56: on any label path space, `labelTailEvent N` records that all
coordinates from time `N + 1` onward agree with time `0`. -/
private def labelTailEvent {α : Type*} (N : ℕ) : Set (ℕ → α) :=
  {ω | ∀ n ≥ N, ω (n + 1) = ω 0}

/-- Helper for Theorem 17.56: the label tail events form an increasing family in the threshold
index, so continuity from below can later recover a deterministic high-probability tail cutoff. -/
private theorem monotone_labelTailEvent {α : Type*} :
    Monotone (labelTailEvent (α := α)) := by
  intro N M hNM ω hω n hn
  exact hω n (le_trans hNM hn)

/-- Helper for Theorem 17.56: eventual equality with time `0` is a measurable path event on any
measurable label space with measurable equality. -/
private theorem measurableSet_labelTailEvent
    {α : Type*} [MeasurableSpace α] [MeasurableEq α] (N : ℕ) :
    MeasurableSet (labelTailEvent (α := α) N) := by
  let tailSlice : Set.Ici N → Set (ℕ → α) := fun n ↦ {ω | ω (n.1 + 1) = ω 0}
  have htailSlice :
      ∀ n : Set.Ici N, MeasurableSet (tailSlice n) := by
    intro n
    have hpairMeas : Measurable fun ω : ℕ → α ↦ (ω (n.1 + 1), ω 0) := by
      fun_prop
    -- Proof comment: equality of two measurable coordinates is the preimage of the diagonal.
    simpa [tailSlice, Set.diagonal] using measurableSet_diagonal.preimage hpairMeas
  have hrewrite :
      labelTailEvent (α := α) N = ⋂ n : Set.Ici N, tailSlice n := by
    ext ω
    simp [labelTailEvent, tailSlice]
  -- Proof comment: the full tail event is the countable intersection of the fixed-time equality
  -- slices.
  rw [hrewrite]
  exact MeasurableSet.iInter htailSlice

/-- Helper for Theorem 17.56: on a discrete label space, the tail event `labelTailEvent N` is
closed, so Portmanteau can test it along weakly convergent label-path laws. -/
private theorem isClosed_labelTailEvent_discrete
    {α : Type*} [TopologicalSpace α] [DiscreteTopology α] (N : ℕ) :
    IsClosed (labelTailEvent (α := α) N) := by
  let tailSlice : Set.Ici N → Set (ℕ → α) := fun n ↦ {ω | ω (n.1 + 1) = ω 0}
  have htailSlice :
      ∀ n : Set.Ici N, IsClosed (tailSlice n) := by
    intro n
    have hnext : Continuous fun ω : ℕ → α ↦ ω (n.1 + 1) :=
      continuous_apply (n.1 + 1)
    have hzero : Continuous fun ω : ℕ → α ↦ ω 0 :=
      continuous_apply 0
    -- Proof comment: on a discrete target, equality of two continuous coordinates is a closed
    -- condition.
    simpa [tailSlice] using isClosed_eq hnext hzero
  have hrewrite :
      labelTailEvent (α := α) N = ⋂ n : Set.Ici N, tailSlice n := by
    ext ω
    simp [labelTailEvent, tailSlice]
  -- Proof comment: the tail event is the countable intersection of the fixed-time equality
  -- slices.
  rw [hrewrite]
  exact isClosed_iInter htailSlice

/-- Helper for Theorem 17.56: a fixed deterministic label-tail cutoff survives weak limits of
discrete label-path laws, after weakening the strict finite-stage bound to a non-strict limit
bound. -/
private theorem le_labelTailEvent_of_tendsto_of_eventually_lt
    {α : Type*} [MeasurableSpace α] [MeasurableEq α] [TopologicalSpace α] [DiscreteTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] [HasOuterApproxClosed α]
    {Pseq : ℕ → ProbabilityMeasure (ℕ → α)} {P : ProbabilityMeasure (ℕ → α)}
    (hP : Tendsto Pseq atTop (𝓝 P)) {N : ℕ} {c : ℝ≥0∞}
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        c < (Pseq n : Measure (ℕ → α)) (labelTailEvent (α := α) N)) :
    c ≤ (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
  let tail : Set (ℕ → α) := labelTailEvent (α := α) N
  have hclosed : IsClosed tail := by
    simpa [tail] using isClosed_labelTailEvent_discrete (α := α) N
  have hlimsup :
      atTop.limsup (fun n ↦ (Pseq n : Measure (ℕ → α)) tail) ≤
        (P : Measure (ℕ → α)) tail := by
    -- Proof comment: once the threshold `N` is fixed, Portmanteau applies directly to the closed
    -- tail event `tail`.
    simpa [tail] using
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hP hclosed
  have hfreq :
      ∃ᶠ n : ℕ in atTop, c ≤ (Pseq n : Measure (ℕ → α)) tail := by
    exact hbound.frequently.mono fun n hn ↦ hn.le
  have hleLimsup :
      c ≤ atTop.limsup (fun n ↦ (Pseq n : Measure (ℕ → α)) tail) := by
    -- Proof comment: an eventual strict lower bound is in particular a frequent non-strict lower
    -- bound, so the limsup cannot fall below `c`.
    exact le_limsup_of_frequently_le hfreq
  exact le_trans hleLimsup hlimsup

/-- Helper for Theorem 17.56: a fixed deterministic dyadic label-tail cutoff survives weak limits
of discrete label-path laws, with one dyadic step of slack turning Portmanteau's non-strict limit
bound back into the strict estimate needed later. -/
private theorem labelTailCutoff_of_tendsto_with_fixedThreshold
    {α : Type*} [MeasurableSpace α] [MeasurableEq α] [TopologicalSpace α] [DiscreteTopology α]
    [SecondCountableTopology α] [OpensMeasurableSpace α] [HasOuterApproxClosed α]
    {Pseq : ℕ → ProbabilityMeasure (ℕ → α)} {P : ProbabilityMeasure (ℕ → α)}
    (hP : Tendsto Pseq atTop (𝓝 P)) {N r : ℕ}
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0∞)) <
          (Pseq n : Measure (ℕ → α)) (labelTailEvent (α := α) N)) :
    (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
      (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
  have hlimit :
      (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0∞)) ≤
        (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
    -- Proof comment: once the cutoff index `N` is fixed, the closed-set Portmanteau lemma gives
    -- the non-strict lower bound at the shifted dyadic budget `r + 1`.
    exact le_labelTailEvent_of_tendsto_of_eventually_lt hP hbound
  have hdyadicStep :
      (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0∞)) := by
    have hpow :
        ((1 / 2 : ℝ≥0) ^ (r + 2)) < ((1 / 2 : ℝ≥0) ^ (r + 1)) := by
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        mul_lt_of_lt_one_right
          (show 0 < (1 / 2 : ℝ≥0) ^ (r + 1) by positivity)
          (by norm_num : (1 / 2 : ℝ≥0) < 1)
    have hle1 : ((1 / 2 : ℝ≥0) ^ (r + 1)) ≤ 1 := by
      exact pow_le_one₀ (n := r + 1)
        (by positivity : 0 ≤ (1 / 2 : ℝ≥0))
        (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
    have hle2 : ((1 / 2 : ℝ≥0) ^ (r + 2)) ≤ 1 := by
      exact pow_le_one₀ (n := r + 2)
        (by positivity : 0 ≤ (1 / 2 : ℝ≥0))
        (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
    have hsub :
        (1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) <
          (1 - ((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0) := by
      exact tsub_lt_tsub_left_of_le hle1 hpow
    have hsubENN :
        (((1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) : ℝ≥0∞)) <
          (((1 - ((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0) : ℝ≥0∞)) := by
      exact_mod_cast hsub
    -- Proof comment: subtract the strictly smaller dyadic error from `1`; this is where the one
    -- extra dyadic step creates room to recover a strict limit inequality.
    simpa [ENNReal.coe_sub] using hsubENN
  exact lt_of_lt_of_le hdyadicStep hlimit

/-- Helper for Theorem 17.56: once a label path is eventually constant relative to time `0`
almost surely, some deterministic tail threshold already has probability larger than `1 - ε`. -/
private theorem exists_labelTailEvent_highProb_of_ae_eventuallyEq
    {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    {P : ProbabilityMeasure (ℕ → α)}
    (hevent :
      ∀ᵐ ω ∂(P : Measure (ℕ → α)), ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ,
      (1 : ℝ≥0∞) - ε < (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
  intro ε hε
  have hUnionAe :
      ∀ᵐ ω ∂(P : Measure (ℕ → α)), ω ∈ ⋃ N : ℕ, labelTailEvent (α := α) N := by
    filter_upwards [hevent] with ω hω
    rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
    exact Set.mem_iUnion.2 ⟨N, by simpa [labelTailEvent] using hN⟩
  have hUnionProb :
      (P : Measure (ℕ → α)) (⋃ N : ℕ, labelTailEvent (α := α) N) = 1 := by
    rw [← mem_ae_iff_prob_eq_one
      (MeasurableSet.iUnion fun N ↦ measurableSet_labelTailEvent (α := α) N)]
    exact hUnionAe
  have hUnionEq :
      (P : Measure (ℕ → α)) (⋃ N : ℕ, labelTailEvent (α := α) N) =
        ⨆ N : ℕ, (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
    exact (monotone_labelTailEvent (α := α)).measure_iUnion
  have hltUnion :
      (1 : ℝ≥0∞) - ε <
        (P : Measure (ℕ → α)) (⋃ N : ℕ, labelTailEvent (α := α) N) := by
    rw [hUnionProb]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.coe_ne_zero.2 (ne_of_gt hε))
  rw [hUnionEq] at hltUnion
  rcases lt_iSup_iff.mp hltUnion with ⟨N, hN⟩
  exact ⟨N, hN⟩

/-- Helper for Theorem 17.56: if one can beat every dyadic error budget by some deterministic
tail cutoff, then the path is eventually constant relative to time `0` almost surely. -/
private theorem aeEventuallyEq_ofDyadicLabelTailCutoffs
    {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    {P : ProbabilityMeasure (ℕ → α)}
    (hcutoff :
      ∀ r : ℕ, ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (P : Measure (ℕ → α)) (labelTailEvent (α := α) N)) :
    ∀ᵐ ω ∂(P : Measure (ℕ → α)), ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
  let unionTail : Set (ℕ → α) := ⋃ N : ℕ, labelTailEvent (α := α) N
  have hUnionMeas : MeasurableSet unionTail := by
    exact MeasurableSet.iUnion fun N ↦ measurableSet_labelTailEvent (α := α) N
  have hUnionEq :
      (P : Measure (ℕ → α)) unionTail =
        ⨆ N : ℕ, (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) := by
    simpa [unionTail] using
      (monotone_labelTailEvent (α := α)).measure_iUnion (μ := (P : Measure (ℕ → α)))
  have hUnionUpper :
      (P : Measure (ℕ → α)) unionTail ≤ 1 := by
    calc
      (P : Measure (ℕ → α)) unionTail ≤ (P : Measure (ℕ → α)) Set.univ := by
        exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hUnionLower :
      ∀ r : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) ≤
          (P : Measure (ℕ → α)) unionTail := by
    intro r
    rcases hcutoff r with ⟨N, hN⟩
    refine le_trans hN.le ?_
    exact measure_mono (by intro ω hω; exact Set.mem_iUnion.2 ⟨N, hω⟩)
  have hUnionNeTop : (P : Measure (ℕ → α)) unionTail ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hUnionUpper ENNReal.one_lt_top)
  have hpowNN :
      Tendsto (fun r : ℕ ↦ ((1 / 2 : ℝ≥0) ^ (r + 1))) atTop (𝓝 0) := by
    -- Proof comment: the dyadic error budgets tend to `0`.
    simpa using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (show (1 / 2 : ℝ≥0) < 1 by norm_num)).comp
        (tendsto_add_atTop_nat 1)
  have hpowReal :
      Tendsto (fun r : ℕ ↦ (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    exact NNReal.tendsto_coe.2 hpowNN
  have honeMinus :
      Tendsto (fun r : ℕ ↦ 1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hpowReal
  have hUnionLowerReal :
      ∀ r : ℕ,
        1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ) <
          ((P : Measure (ℕ → α)) unionTail).toReal := by
    intro r
    have hltENN :
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (P : Measure (ℕ → α)) unionTail := by
      exact lt_of_lt_of_le (Classical.choose_spec (hcutoff r)) <|
        measure_mono (by
          intro ω hω
          exact Set.mem_iUnion.2 ⟨Classical.choose (hcutoff r), hω⟩)
    have hltENN' :
        ((↑(1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) : ℝ≥0∞)) <
          (P : Measure (ℕ → α)) unionTail := by
      simpa [ENNReal.coe_sub] using hltENN
    have hpowLeOne :
        ((1 / 2 : ℝ≥0) ^ (r + 1)) ≤ 1 := by
      exact pow_le_one₀ (by positivity : 0 ≤ (1 / 2 : ℝ≥0)) (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
    -- Proof comment: convert the ENNReal lower bound into an ordinary real inequality so the
    -- limit argument can use the standard real topology.
    have hltReal :
        (((1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) : ℝ)) <
          ((P : Measure (ℕ → α)) unionTail).toReal := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hUnionNeTop).1 <| by
        simpa using hltENN'
    have hsubReal :
        (((1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0)) : ℝ) =
          1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ) := by
      simpa using (NNReal.coe_sub hpowLeOne)
    rwa [hsubReal] at hltReal
  have hUnionToRealGeOne :
      1 ≤ ((P : Measure (ℕ → α)) unionTail).toReal := by
    exact le_of_tendsto_of_tendsto' honeMinus tendsto_const_nhds fun r ↦
      (hUnionLowerReal r).le
  have hUnionToRealLeOne :
      ((P : Measure (ℕ → α)) unionTail).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top hUnionUpper
  have hUnionProb :
      (P : Measure (ℕ → α)) unionTail = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).1 <|
      le_antisymm hUnionToRealLeOne hUnionToRealGeOne
  have hUnionAe :
      ∀ᵐ ω ∂(P : Measure (ℕ → α)), ω ∈ unionTail := by
    exact (mem_ae_iff_prob_eq_one hUnionMeas).2 hUnionProb
  -- Proof comment: membership in the increasing union of the deterministic tail events is
  -- exactly eventual equality with time `0`.
  filter_upwards [hUnionAe] with ω hω
  rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, hN⟩

/-- Helper for Theorem 17.56: if equality of coarse labels forces the dyadic metric bound, then a
label-tail event on the projected path implies the ambient dyadic tail event. -/
private theorem mem_dyadicTailEvent_of_labelTailEvent
    {α : Type*} {ρ : (ℕ → unitInterval) → α} {m N : ℕ}
    {ω : ℕ → (ℕ → unitInterval)}
    (hdiam :
      ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m)
    (hω : (fun n : ℕ ↦ ρ (ω n)) ∈ labelTailEvent (α := α) N) :
    ω ∈ dyadicTailEvent m N := by
  intro n hn
  exact hdiam (hω n hn)

/-- Helper for Theorem 17.56: once `n` lies beyond the deterministic tail cutoff `N`, the
time-`0`/time-`n+1` off-diagonal event is contained in the complement of `labelTailEvent N`. -/
private theorem headAndNext_offDiagonal_le_compl_labelTailEvent
    {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    (Plabel : ProbabilityMeasure (ℕ → α)) {N n : ℕ} (hNn : N ≤ n) :
    (Measure.map (headAndNext (β := α) n) (Plabel : Measure (ℕ → α)))
        {p : α × α | p.1 ≠ p.2} ≤
      (Plabel : Measure (ℕ → α)) (labelTailEvent (α := α) N)ᶜ := by
  have hheadAndNextMeas : Measurable (headAndNext (β := α) n) := by
    -- Proof comment: `headAndNext` is the product of two measurable coordinate evaluations.
    fun_prop
  rw [Measure.map_apply hheadAndNextMeas (measurableSet_offDiagonal (t := α))]
  refine measure_mono ?_
  intro ω hω htail
  -- Proof comment: on `labelTailEvent N`, the coordinate `n + 1` already agrees with time `0`,
  -- so the corresponding pair cannot lie off the diagonal.
  exact hω ((htail n hNn).symm)

/-- Helper for Theorem 17.56: the dyadic tail events are closed, so they are the right Portmanteau
test sets for the compactness endgame. -/
private theorem isClosed_dyadicTailEvent (m N : ℕ) :
    IsClosed (dyadicTailEvent m N) := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let tailSlice : Set.Ici N → Set (ℕ → (ℕ → unitInterval)) :=
    fun n ↦ {ω |
      @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n.1 + 1)) (ω 0) ≤ (1 / 2 : ℝ) ^ m}
  have htailSlice :
      ∀ n : Set.Ici N, IsClosed (tailSlice n) := by
    intro n
    have hnext : Continuous fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n.1 + 1) :=
      continuous_apply (n.1 + 1)
    have hzero : Continuous fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0 :=
      continuous_apply 0
    -- Proof comment: each fixed-time dyadic constraint is the inverse image of a closed ray under
    -- the continuous distance-to-time-zero map.
    simpa [tailSlice] using
      (isClosed_le (hnext.dist hzero) continuous_const)
  have hrewrite :
      dyadicTailEvent m N = ⋂ n : Set.Ici N, tailSlice n := by
    ext ω
    simp [dyadicTailEvent, tailSlice]
  -- Proof comment: the full tail event is the countable intersection of the fixed-time closed
  -- dyadic constraints.
  rw [hrewrite]
  exact isClosed_iInter htailSlice

/-- Helper for Theorem 17.56: if dyadic closeness to time `0` holds eventually almost surely at a
fixed scale, then one deterministic tail threshold already has probability larger than `1 - ε`. -/
private theorem exists_dyadicTailEvent_highProb_of_ae_eventuallyDistLe
    {P : ProbabilityMeasure (ℕ → (ℕ → unitInterval))} {m : ℕ}
    (hevent :
      ∀ᵐ ω ∂(P : Measure (ℕ → (ℕ → unitInterval))),
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
            (1 / 2 : ℝ) ^ m) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ,
      (1 : ℝ≥0∞) - ε <
        (P : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  intro ε hε
  have hUnionAe :
      ∀ᵐ ω ∂(P : Measure (ℕ → (ℕ → unitInterval))),
        ω ∈ ⋃ N : ℕ, dyadicTailEvent m N := by
    filter_upwards [hevent] with ω hω
    rcases Filter.eventually_atTop.1 hω with ⟨N, hN⟩
    exact Set.mem_iUnion.2 ⟨N, by simpa [dyadicTailEvent] using hN⟩
  have hUnionProb :
      (P : Measure (ℕ → (ℕ → unitInterval))) (⋃ N : ℕ, dyadicTailEvent m N) = 1 := by
    rw [← mem_ae_iff_prob_eq_one
      (MeasurableSet.iUnion fun N ↦ (isClosed_dyadicTailEvent m N).measurableSet)]
    exact hUnionAe
  have hUnionEq :
      (P : Measure (ℕ → (ℕ → unitInterval))) (⋃ N : ℕ, dyadicTailEvent m N) =
        ⨆ N : ℕ, (P : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
    exact (monotone_dyadicTailEvent m).measure_iUnion
  have hltUnion :
      (1 : ℝ≥0∞) - ε <
        (P : Measure (ℕ → (ℕ → unitInterval))) (⋃ N : ℕ, dyadicTailEvent m N) := by
    rw [hUnionProb]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (ENNReal.coe_ne_zero.2 (ne_of_gt hε))
  rw [hUnionEq] at hltUnion
  rcases lt_iSup_iff.mp hltUnion with ⟨N, hN⟩
  exact ⟨N, hN⟩

/-- Helper for Theorem 17.56: evaluating a `headAndNext` pair law on the dyadic bad set rewrites
the path bad event to the canonical pair-event spelling, with `dist_comm` built in. -/
private theorem headAndNext_preimage_badPair
    (m n : ℕ) :
    headAndNext (β := ℕ → unitInterval) n ⁻¹'
        ({z : (ℕ → unitInterval) × (ℕ → unitInterval) |
          (1 / 2 : ℝ) ^ m <
            @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2}) =
      {ω | (1 / 2 : ℝ) ^ m <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0)} := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  -- Proof comment: `headAndNext` stores `(ω 0, ω (n + 1))`, so `dist_comm` is the only
  -- normalization needed to match the path-side spelling.
  ext ω
  change
    ((1 / 2 : ℝ) ^ m <
      @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω 0) (ω (n + 1))) ↔
      ((1 / 2 : ℝ) ^ m <
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0))
  have hd :
      @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) =
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω 0) (ω (n + 1)) :=
    by simpa using
      (dist_comm (ω (n + 1)) (ω 0) :
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) =
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω 0) (ω (n + 1)))
  constructor
  · intro h
    exact hd ▸ h
  · intro h
    exact hd ▸ h

/-- Helper for Theorem 17.56: evaluating a `headAndNext` pair law on the dyadic bad set rewrites
the path bad event to the canonical pair-event spelling, with `dist_comm` built in. -/
private theorem measure_headAndNext_badPair_eq
    {P : Measure (ℕ → (ℕ → unitInterval))}
    {π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))}
    (m n : ℕ)
    (hpair :
      Measure.map (headAndNext (β := ℕ → unitInterval) n) P = π) :
    P {ω | (1 / 2 : ℝ) ^ m <
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0)} =
      π {z | (1 / 2 : ℝ) ^ m <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  rw [← hpair]
  rw [Measure.map_apply (by fun_prop)]
  · -- Proof comment: the set-level normalization is isolated in
    -- `headAndNext_preimage_badPair`, so callers never have to rebuild the same `ext` proof.
    rw [headAndNext_preimage_badPair]
  ·
    -- Proof comment: the dyadic bad pair set is the preimage of the open ray `Ioi` under the
    -- continuous distance map on pairs.
    change MeasurableSet
      ({z : (ℕ → unitInterval) × (ℕ → unitInterval) |
        (1 / 2 : ℝ) ^ m < dist z.1 z.2})
    exact
      (isOpen_lt
        (f := fun _ : (ℕ → unitInterval) × (ℕ → unitInterval) ↦ ((1 / 2 : ℝ) ^ m))
        (g := fun z : (ℕ → unitInterval) × (ℕ → unitInterval) ↦ dist z.1 z.2)
        continuous_const (continuous_fst.dist continuous_snd)).measurableSet

/-- Helper for Theorem 17.56: if a path law has known pair marginals at every time, then the
complement of the dyadic tail event is controlled by the sum of the corresponding pairwise bad
masses. -/
private theorem measure_compl_dyadicTailEvent_le_tsum_pairBadMass
    {P : ProbabilityMeasure (ℕ → (ℕ → unitInterval))}
    {π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval))}
    (hpair :
      ∀ n : ℕ,
        Measure.map (headAndNext (β := ℕ → unitInterval) n)
          (P : Measure (ℕ → (ℕ → unitInterval))) =
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))))
    (m N : ℕ) :
    (P : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)ᶜ ≤
      ∑' k : ℕ,
        ((π (N + k) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
          {z | (1 / 2 : ℝ) ^ m <
              @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2}) := by
  let tailBadSlice : ℕ → Set (ℕ → (ℕ → unitInterval)) :=
    fun k ↦
      {ω | (1 / 2 : ℝ) ^ m <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω ((N + k) + 1)) (ω 0)}
  have hsubset :
      (dyadicTailEvent m N)ᶜ ⊆ ⋃ k : ℕ, tailBadSlice k := by
    intro ω hω
    have hω' :
        ∃ n ≥ N,
          ¬ @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
            (1 / 2 : ℝ) ^ m := by
      simpa [dyadicTailEvent, Set.mem_setOf_eq, not_forall, _root_.not_imp] using hω
    rcases hω' with ⟨n, hnN, hbad⟩
    have hbad' :
        (1 / 2 : ℝ) ^ m <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) := by
      exact lt_of_not_ge hbad
    have hindex : (N + (n - N)) + 1 = n + 1 := by
      rw [Nat.add_sub_of_le hnN]
    refine Set.mem_iUnion.2 ⟨n - N, ?_⟩
    -- Proof comment: a tail-event failure is witnessed by one concrete bad time, which lands in
    -- the corresponding bad slice after rewriting that time as `N + (n - N)`.
    simpa [tailBadSlice, hindex] using hbad'
  calc
    (P : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)ᶜ ≤
        (P : Measure (ℕ → (ℕ → unitInterval))) (⋃ k : ℕ, tailBadSlice k) := by
          exact measure_mono hsubset
    _ ≤ ∑' k : ℕ, (P : Measure (ℕ → (ℕ → unitInterval))) (tailBadSlice k) := by
          exact measure_iUnion_le tailBadSlice
    _ =
        ∑' k : ℕ,
          ((π (N + k) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
            {z | (1 / 2 : ℝ) ^ m <
                @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2}) := by
          congr with k
          -- Proof comment: the tail slice is the canonical bad path event at time `N + k`, so
          -- the shared `headAndNext` bridge rewrites it in one step.
          simpa [tailBadSlice] using
            (measure_headAndNext_badPair_eq
              (P := (P : Measure (ℕ → (ℕ → unitInterval))))
              (π := (π (N + k) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))))
              (m := m) (n := N + k) (hpair (N + k)))

/-- Helper for Theorem 17.56: probability laws on the compact Hilbert-cube path space always admit
a weakly convergent subsequence. -/
private theorem existsConvergentSubsequenceOfHilbertCubePathLaws
    (P : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval))) :
    ∃ Q : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (P ∘ φ) atTop (𝓝 Q) := by
  letI : CompactSpace (ProbabilityMeasure (ℕ → (ℕ → unitInterval))) := inferInstance
  -- Proof comment: compactness of the probability-measure space on a compact path space gives the
  -- subsequence extraction needed for the stage-law limit argument.
  obtain ⟨Q, φ, hφ, hφlim⟩ := CompactSpace.tendsto_subseq P
  exact ⟨Q, φ, hφ, by simpa [Function.comp] using hφlim⟩

/-- Helper for Theorem 17.56: weak convergence of Hilbert-cube path laws passes to every fixed
time coordinate by continuity of evaluation. -/
private theorem tendsto_hilbertCubePathLaw_eval
    {P : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval))}
    {Q : ProbabilityMeasure (ℕ → (ℕ → unitInterval))}
    (hP : Tendsto P atTop (𝓝 Q)) (k : ℕ) :
    Tendsto
      (fun n ↦
        (P n).map
          (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
          (continuous_apply k).measurable.aemeasurable)
      atTop
      (𝓝
        (Q.map
          (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
          (continuous_apply k).measurable.aemeasurable)) := by
  -- Proof comment: the compactness endgame will compare fixed-time marginals after extracting a
  -- convergent subsequence of stage laws, and continuity of `ω ↦ ω k` is the only bridge needed.
  simpa using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q hP (continuous_apply k)

/-- Helper for Theorem 17.56: a measure-level pushforward identity upgrades directly to the
corresponding probability-measure identity. -/
private theorem probabilityMeasureMap_eq_of_measureMap_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}
    {f : α → β} (hf : AEMeasurable f (μ : Measure α))
    (hmap : Measure.map f (μ : Measure α) = (ν : Measure β)) :
    μ.map hf = ν := by
  -- Proof comment: `ProbabilityMeasure.toMeasure_injective` lets the probability-level equality
  -- reuse the already established measure-level pushforward identity verbatim.
  apply ProbabilityMeasure.toMeasure_injective
  simpa using hmap

/-- Helper for Theorem 17.56: mapping an `ULift`-transported law back down along a measurable
observable recovers the original pushforward law. -/
private theorem measure_map_uliftUp_preimage_down
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) :
    (Measure.map ULift.up μ) (ULift.down ⁻¹' s) = μ s := by
  rw [Measure.map_apply measurable_up]
  · have hup : ULift.up ⁻¹' (ULift.down ⁻¹' s) = s := by
      ext ω
      rfl
    -- Proof comment: lifting and then projecting back down leaves measurable events unchanged.
    rw [hup]
  · exact measurableSet_preimage measurable_down hs

/-- Helper for Theorem 17.56: mapping an `ULift`-transported law back down along a measurable
observable recovers the original pushforward law. -/
private theorem measure_map_uliftUp_comp_down
    {Ω : Type*} [MeasurableSpace Ω]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω) {f : Ω → α} (hf : Measurable f) :
    Measure.map (fun ω : ULift Ω ↦ f ω.down) (Measure.map ULift.up μ) =
      Measure.map f μ := by
  -- Proof comment: `ULift.up` followed by `ω ↦ f ω.down` is literally the original observable.
  rw [Measure.map_map (f := ULift.up) (g := fun ω : ULift Ω ↦ f ω.down)
    (hf.comp measurable_down) measurable_up]
  change Measure.map (fun ω : Ω ↦ f ω) μ = Measure.map f μ
  rfl

/-- Helper for Theorem 17.56: once a fixed coordinate law is eventually constant along a weakly
convergent subsequence of Hilbert-cube path laws, the same coordinate law holds for the limit. -/
private theorem limitEvalLaw_eq_of_eventuallyConstant
    {P : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval))}
    {Q : ProbabilityMeasure (ℕ → (ℕ → unitInterval))}
    {η : ProbabilityMeasure (ℕ → unitInterval)}
    (hP : Tendsto P atTop (𝓝 Q)) (k : ℕ)
    (hconst :
      ∀ᶠ j : ℕ in atTop,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
          (P j : Measure (ℕ → (ℕ → unitInterval))) =
            (η : Measure (ℕ → unitInterval))) :
    Q.map
        (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
        (continuous_apply k).measurable.aemeasurable =
      η := by
  have hmapTendsto :
      Tendsto
        (fun j ↦
          (P j).map
            (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
            (continuous_apply k).measurable.aemeasurable)
        atTop
        (𝓝
          (Q.map
            (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
            (continuous_apply k).measurable.aemeasurable)) :=
    tendsto_hilbertCubePathLaw_eval hP k
  have hconst' :
      Tendsto
        (fun j ↦
          (P j).map
            (f := fun ω : ℕ → (ℕ → unitInterval) ↦ ω k)
            (continuous_apply k).measurable.aemeasurable)
        atTop
        (𝓝 η) := by
    refine tendsto_const_nhds.congr' ?_
    exact hconst.mono fun j hj ↦
      by
        simpa using
          (probabilityMeasureMap_eq_of_measureMap_eq
            (hf := (continuous_apply k).measurable.aemeasurable) hj).symm
  -- Proof comment: the pushed-forward subsequence has both the weak limit predicted by continuity
  -- of evaluation and the eventual constant limit `η`, so uniqueness of limits identifies them.
  exact tendsto_nhds_unique hmapTendsto hconst'

/-- Helper for Theorem 17.56: once a stage family of path laws has the exact fixed-time marginals
and its closed dyadic tail events converge to full mass, compactness and Portmanteau extract the
final Hilbert-cube realization. -/
private theorem existsHilbertCubeDyadicTailRealizationOfStageLaws
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)))
    (Nstage : ℕ → ℕ)
    (hhead :
      ∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval)))
    (hdyadic :
      ∀ m : ℕ,
        Tendsto
          (fun J ↦
            (Pstage J : Measure (ℕ → (ℕ → unitInterval)))
              (dyadicTailEvent m (Nstage m)))
          atTop (𝓝 (1 : ℝ≥0∞))) :
    ∃ (Ω : Type v) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  let Ω0 := ℕ → (ℕ → unitInterval)
  obtain ⟨Q, φ, hφmono, hφtendsto⟩ :=
    existsConvergentSubsequenceOfHilbertCubePathLaws Pstage
  have hφ_atTop : Tendsto φ atTop atTop :=
    tendsto_atTop_mono (StrictMono.id_le hφmono) tendsto_id
  have hQhead :
      Q.map
          (f := fun ω : Ω0 ↦ ω 0)
          (continuous_apply 0).measurable.aemeasurable =
        ν := by
    -- Proof comment: the time-`0` marginal is constant all along the subsequence, so the shared
    -- marginal-extraction helper identifies the limit law immediately.
    exact limitEvalLaw_eq_of_eventuallyConstant hφtendsto 0 <|
      Filter.Eventually.of_forall fun j ↦ hhead (φ j)
  have hQcoord :
      ∀ n : ℕ,
        Q.map
            (f := fun ω : Ω0 ↦ ω (n + 1))
            (continuous_apply (n + 1)).measurable.aemeasurable =
          νn n := by
    intro n
    -- Proof comment: after the subsequence index dominates `n`, the time-`n + 1` marginal is
    -- constant as well, so the same marginal-extraction helper applies.
    exact limitEvalLaw_eq_of_eventuallyConstant hφtendsto (n + 1) <| by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨n, fun j hj ↦ ?_⟩
      have hle : n ≤ φ j := le_trans hj (StrictMono.id_le hφmono j)
      exact hcoord n (φ j) hle
  have hQtail :
      ∀ m : ℕ,
        (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) = 1 := by
    intro m
    have hclosed : IsClosed (dyadicTailEvent m (Nstage m)) :=
      isClosed_dyadicTailEvent m (Nstage m)
    have hseq :
        Tendsto
          (fun j ↦
            (Pstage (φ j) : Measure Ω0)
              (dyadicTailEvent m (Nstage m)))
          atTop (𝓝 (1 : ℝ≥0∞)) := by
      exact (hdyadic m).comp hφ_atTop
    have hlimsup :
        atTop.limsup
            (fun j ↦
              (Pstage (φ j) : Measure Ω0)
                (dyadicTailEvent m (Nstage m))) ≤
          (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) := by
      exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hφtendsto hclosed
    have hge :
        (1 : ℝ≥0∞) ≤ (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) := by
      simpa [hseq.limsup_eq] using hlimsup
    have hle :
        (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) ≤ 1 := by
      calc
        (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) ≤ (Q : Measure Ω0) Set.univ := by
          exact measure_mono (by
            intro ω hω
            trivial)
        _ = 1 := by simp
    exact le_antisymm hle hge
  let Ω : Type v := ULift.{v} Ω0
  let P : ProbabilityMeasure Ω := Q.map measurable_up.aemeasurable
  let Y : Ω → ℕ → unitInterval := fun ω ↦ ω.down 0
  let Yn : ℕ → Ω → ℕ → unitInterval := fun n ω ↦ ω.down (n + 1)
  have hY : HasLaw Y ν P := by
    refine ⟨((continuous_apply 0).measurable.comp measurable_down).aemeasurable, ?_⟩
    -- Route correction: avoid the unstable `HasLaw.comp`/`ULift.down` transport and rewrite the
    -- law directly in the normal form `P = Measure.map ULift.up Q`.
    calc
      Measure.map Y (P : Measure Ω) =
          Measure.map (fun ω : Ω0 ↦ ω 0) (Q : Measure Ω0) := by
            rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
            simpa [Y] using
              (measure_map_uliftUp_comp_down
                (μ := (Q : Measure Ω0))
                (f := fun ω : Ω0 ↦ ω 0)
                (continuous_apply 0).measurable)
      _ = (ν : Measure (ℕ → unitInterval)) := by
            simpa using congrArg
              (fun ρ : ProbabilityMeasure (ℕ → unitInterval) ↦ (ρ : Measure (ℕ → unitInterval)))
              hQhead
  have hYn : ∀ n : ℕ, HasLaw (Yn n) (νn n) P := by
    intro n
    refine ⟨((continuous_apply (n + 1)).measurable.comp measurable_down).aemeasurable, ?_⟩
    -- Proof comment: every coordinate law is transported by the same direct `Measure.map` bridge.
    calc
      Measure.map (Yn n) (P : Measure Ω) =
          Measure.map (fun ω : Ω0 ↦ ω (n + 1)) (Q : Measure Ω0) := by
            rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
            simpa [Yn] using
              (measure_map_uliftUp_comp_down
                (μ := (Q : Measure Ω0))
                (f := fun ω : Ω0 ↦ ω (n + 1))
                (continuous_apply (n + 1)).measurable)
      _ = (νn n : Measure (ℕ → unitInterval)) := by
            simpa using congrArg
              (fun ρ : ProbabilityMeasure (ℕ → unitInterval) ↦ (ρ : Measure (ℕ → unitInterval)))
              (hQcoord n)
  have htail :
      ∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
            (1 / 2 : ℝ) ^ m := by
    intro m
    have hmem :
        ∀ᵐ ω ∂(P : Measure Ω), ω.down ∈ dyadicTailEvent m (Nstage m) := by
      refine (mem_ae_iff_prob_eq_one ?_).2 ?_
      · exact measurableSet_preimage measurable_down
          (isClosed_dyadicTailEvent m (Nstage m)).measurableSet
      · -- Proof comment: push the closed event back through `ULift.up` instead of transporting
        -- the law forward through `ULift.down`.
        rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
        calc
          (Measure.map ULift.up (Q : Measure Ω0)) (ULift.down ⁻¹' dyadicTailEvent m (Nstage m)) =
              (Q : Measure Ω0) (dyadicTailEvent m (Nstage m)) := by
                exact measure_map_uliftUp_preimage_down
                  (μ := (Q : Measure Ω0))
                  (s := dyadicTailEvent m (Nstage m))
                  (hs := (isClosed_dyadicTailEvent m (Nstage m)).measurableSet)
          _ = 1 := hQtail m
    filter_upwards [hmem] with ω hω
    have hω' :
        ∀ n ≥ Nstage m,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω.down (n + 1)) (ω.down 0) ≤
            (1 / 2 : ℝ) ^ m := by
      simpa [dyadicTailEvent] using hω
    -- Proof comment: full mass on the closed dyadic tail event is exactly the eventual pointwise
    -- dyadic control required by the compact-core realization statement.
    refine Filter.eventually_atTop.2 ⟨Nstage m, fun n hn ↦ ?_⟩
    simpa [Y, Yn] using hω' n hn
  refine ⟨Ω, inferInstance, P, Y, Yn, hY, hYn, htail⟩

/-- Helper for Theorem 17.56: the compactness endgame only needs approximate lower bounds on
closed dyadic tail events; Portmanteau upgrades those approximate bounds to probability-one mass on
the monotone tail union in the limiting path law. -/
private theorem existsHilbertCubeDyadicTailRealizationOfApproxStageLaws
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)))
    (hhead :
      ∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval)))
    (hdyadic :
      ∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
          (1 : ℝ≥0∞) - ε <
            (Pstage J : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) :
    ∃ (Ω : Type v) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  let Ω0 := ℕ → (ℕ → unitInterval)
  obtain ⟨Q, φ, hφmono, hφtendsto⟩ :=
    existsConvergentSubsequenceOfHilbertCubePathLaws Pstage
  have hφ_atTop : Tendsto φ atTop atTop :=
    tendsto_atTop_mono (StrictMono.id_le hφmono) tendsto_id
  have hQhead :
      Q.map
          (f := fun ω : Ω0 ↦ ω 0)
          (continuous_apply 0).measurable.aemeasurable =
        ν := by
    -- Proof comment: the time-`0` marginal is fixed along the whole stage family, so the weak
    -- limit keeps that same head law.
    exact limitEvalLaw_eq_of_eventuallyConstant hφtendsto 0 <|
      Filter.Eventually.of_forall fun j ↦ hhead (φ j)
  have hQcoord :
      ∀ n : ℕ,
        Q.map
            (f := fun ω : Ω0 ↦ ω (n + 1))
            (continuous_apply (n + 1)).measurable.aemeasurable =
          νn n := by
    intro n
    -- Proof comment: once the subsequence index dominates `n`, the time-`n + 1` marginal is
    -- again constant, so the same shared limit-extraction lemma yields the target law.
    exact limitEvalLaw_eq_of_eventuallyConstant hφtendsto (n + 1) <| by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨n, fun j hj ↦ ?_⟩
      have hle : n ≤ φ j := le_trans hj (StrictMono.id_le hφmono j)
      exact hcoord n (φ j) hle
  have hQtailApprox :
      ∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ,
          (1 : ℝ≥0∞) - ε ≤
            (Q : Measure Ω0) (dyadicTailEvent m N) := by
    intro m ε hε
    obtain ⟨N, hNstage⟩ := hdyadic m ε hε
    have hclosed : IsClosed (dyadicTailEvent m N) :=
      isClosed_dyadicTailEvent m N
    have hlimsup :
        atTop.limsup
            (fun j ↦
              (Pstage (φ j) : Measure Ω0) (dyadicTailEvent m N)) ≤
          (Q : Measure Ω0) (dyadicTailEvent m N) := by
      exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hφtendsto hclosed
    have htailSeq :
        ∀ᶠ j : ℕ in atTop,
          (1 : ℝ≥0∞) - ε ≤
            (Pstage (φ j) : Measure Ω0) (dyadicTailEvent m N) := by
      -- Proof comment: the stage-family lower bound survives along the compactness subsequence.
      exact (hφ_atTop.eventually hNstage).mono fun j hj ↦ le_of_lt hj
    have hlower :
        (1 : ℝ≥0∞) - ε ≤
          atTop.limsup
            (fun j ↦
              (Pstage (φ j) : Measure Ω0) (dyadicTailEvent m N)) := by
      exact le_limsup_of_frequently_le htailSeq.frequently
    exact ⟨N, hlower.trans hlimsup⟩
  have hQtail :
      ∀ m : ℕ,
        (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) = 1 := by
    intro m
    have hle :
        (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) ≤ 1 := by
      calc
        (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) ≤ (Q : Measure Ω0) Set.univ := by
          exact measure_mono (by
            intro ω hω
            trivial)
        _ = 1 := by simp
    have hge :
        (1 : ℝ≥0∞) ≤ (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) := by
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε hfinite
      let δ : ℝ≥0 := min ε 1
      have hδpos : 0 < δ := lt_min hε zero_lt_one
      obtain ⟨N, hN⟩ := hQtailApprox m δ hδpos
      have hmono :
          (Q : Measure Ω0) (dyadicTailEvent m N) ≤
            (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) := by
        exact measure_mono <| Set.subset_iUnion (fun N ↦ dyadicTailEvent m N) N
      have hlower :
          (1 : ℝ≥0∞) - δ ≤
            (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) := by
        exact le_trans hN hmono
      have hδle_one : (δ : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast (show δ ≤ (1 : ℝ≥0) from min_le_right ε 1)
      have hδleε : (δ : ℝ≥0∞) ≤ ε := by
        exact_mod_cast (show δ ≤ ε from min_le_left ε 1)
      have hsumδ :
          (1 : ℝ≥0∞) ≤
            (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) + δ := by
        simpa [tsub_add_cancel_of_le hδle_one] using add_le_add_right hlower δ
      exact le_trans hsumδ (add_le_add_right hδleε _)
    exact le_antisymm hle hge
  let Ω : Type v := ULift.{v} Ω0
  let P : ProbabilityMeasure Ω := Q.map measurable_up.aemeasurable
  let Y : Ω → ℕ → unitInterval := fun ω ↦ ω.down 0
  let Yn : ℕ → Ω → ℕ → unitInterval := fun n ω ↦ ω.down (n + 1)
  have hY : HasLaw Y ν P := by
    refine ⟨((continuous_apply 0).measurable.comp measurable_down).aemeasurable, ?_⟩
    -- Route correction: keep the witness law in the single spelling world
    -- `P = Measure.map ULift.up Q` and rewrite by `Measure.map_map`.
    calc
      Measure.map Y (P : Measure Ω) =
          Measure.map (fun ω : Ω0 ↦ ω 0) (Q : Measure Ω0) := by
            rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
            simpa [Y] using
              (measure_map_uliftUp_comp_down
                (μ := (Q : Measure Ω0))
                (f := fun ω : Ω0 ↦ ω 0)
                (continuous_apply 0).measurable)
      _ = (ν : Measure (ℕ → unitInterval)) := by
            simpa using congrArg
              (fun ρ : ProbabilityMeasure (ℕ → unitInterval) ↦ (ρ : Measure (ℕ → unitInterval)))
              hQhead
  have hYn : ∀ n : ℕ, HasLaw (Yn n) (νn n) P := by
    intro n
    refine ⟨((continuous_apply (n + 1)).measurable.comp measurable_down).aemeasurable, ?_⟩
    -- Proof comment: every coordinate law is transported by the same direct `Measure.map` bridge.
    calc
      Measure.map (Yn n) (P : Measure Ω) =
          Measure.map (fun ω : Ω0 ↦ ω (n + 1)) (Q : Measure Ω0) := by
            rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
            simpa [Yn] using
              (measure_map_uliftUp_comp_down
                (μ := (Q : Measure Ω0))
                (f := fun ω : Ω0 ↦ ω (n + 1))
                (continuous_apply (n + 1)).measurable)
      _ = (νn n : Measure (ℕ → unitInterval)) := by
            simpa using congrArg
              (fun ρ : ProbabilityMeasure (ℕ → unitInterval) ↦ (ρ : Measure (ℕ → unitInterval)))
              (hQcoord n)
  have htail :
      ∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
            (1 / 2 : ℝ) ^ m := by
    intro m
    have hmem :
        ∀ᵐ ω ∂(P : Measure Ω),
          ω.down ∈ ⋃ N : ℕ, dyadicTailEvent m N := by
      refine (mem_ae_iff_prob_eq_one ?_).2 ?_
      · exact measurableSet_preimage measurable_down
          (MeasurableSet.iUnion fun N ↦ (isClosed_dyadicTailEvent m N).measurableSet)
      ·
        rw [show (P : Measure Ω) = Measure.map ULift.up (Q : Measure Ω0) by rfl]
        calc
          (Measure.map ULift.up (Q : Measure Ω0))
              (ULift.down ⁻¹' ⋃ N : ℕ, dyadicTailEvent m N) =
            (Q : Measure Ω0) (⋃ N : ℕ, dyadicTailEvent m N) := by
              exact measure_map_uliftUp_preimage_down
                (μ := (Q : Measure Ω0))
                (s := ⋃ N : ℕ, dyadicTailEvent m N)
                (hs := MeasurableSet.iUnion fun N ↦ (isClosed_dyadicTailEvent m N).measurableSet)
          _ = 1 := hQtail m
    filter_upwards [hmem] with ω hω
    rcases Set.mem_iUnion.1 hω with ⟨N, hωN⟩
    have hω' :
        ∀ n ≥ N,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω.down (n + 1)) (ω.down 0) ≤
            (1 / 2 : ℝ) ^ m := by
      simpa [dyadicTailEvent] using hωN
    -- Proof comment: membership in one tail event from the monotone union is exactly the desired
    -- eventual dyadic bound.
    refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    simpa [Y, Yn] using hω' n hn
  refine ⟨Ω, inferInstance, P, Y, Yn, hY, hYn, htail⟩

/-- Helper for Theorem 17.56: once one has a family of Hilbert-cube pair laws with common first
marginal and summable dyadic bad masses, the owner `condKernel` and `headIndexedPathMeasure`
machinery already produces the required path realization with dyadic tail control. -/
private theorem existsHilbertCubeDyadicTailRealizationOfSummablePairLaws
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)))
    (hfst :
      ∀ n : ℕ,
        Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (ν : Measure (ℕ → unitInterval)))
    (hsnd :
      ∀ n : ℕ,
        Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval)))
    (hbad :
      ∀ m : ℕ,
        (∑' n,
            ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
              {z | (1 / 2 : ℝ) ^ m <
                  @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2})) ≠ ∞) :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let κ : ℕ → Kernel (ℕ → unitInterval) (ℕ → unitInterval) :=
    fun n ↦ (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel
  let Pm : Measure (ℕ → (ℕ → unitInterval)) :=
    headIndexedPathMeasure (β := ℕ → unitInterval) (μ := (ν : Measure (ℕ → unitInterval))) κ
  have hPm : IsProbabilityMeasure Pm := by
    dsimp [Pm]
    infer_instance
  let P : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) := ⟨Pm, hPm⟩
  let Y : (ℕ → (ℕ → unitInterval)) → ℕ → unitInterval := fun ω ↦ ω 0
  let Yn : ℕ → (ℕ → (ℕ → unitInterval)) → ℕ → unitInterval := fun n ω ↦ ω (n + 1)
  let bad : ℕ → ℕ → Set (ℕ → (ℕ → unitInterval)) :=
    fun m n ↦ {ω | (1 / 2 : ℝ) ^ m < dist (ω (n + 1)) (ω 0)}
  have hpair :
      ∀ n : ℕ,
        Measure.map (headAndNext (β := ℕ → unitInterval) n)
            (P : Measure (ℕ → (ℕ → unitInterval))) =
          (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
    intro n
    -- Proof comment: disintegrate each pair law over its first marginal and then feed the
    -- resulting kernels into the owner head-indexed path-law formula.
    calc
      Measure.map (headAndNext (β := ℕ → unitInterval) n)
          (P : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ⊗ₘ κ n := by
          simpa [P, Pm, κ] using
            (headIndexedPathMeasure_map_headAndNext
              (β := ℕ → unitInterval)
              (μ := (ν : Measure (ℕ → unitInterval))) (κ := κ) n)
      _ =
          (Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))) ⊗ₘ
              ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel) := by
            rw [← hfst n]
      _ = (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
            simpa [κ] using
              ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).disintegrate
                ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel))
  have hY :
      HasLaw Y ν P := by
    refine ⟨by
      dsimp [Y]
      exact (measurable_pi_apply 0).aemeasurable, ?_⟩
    -- Proof comment: time `0` of the head-indexed trajectory law keeps the original base law.
    change Measure.map (Function.eval 0) (P : Measure (ℕ → (ℕ → unitInterval))) =
      (ν : Measure (ℕ → unitInterval))
    simpa [P, Pm, κ, Y] using
      (headIndexedTrajMeasure_map_eval_zero
        (β := ℕ → unitInterval) (μ := (ν : Measure (ℕ → unitInterval))) (κ := κ))
  have hYn :
      ∀ n : ℕ, HasLaw (Yn n) (νn n) P := by
    intro n
    refine ⟨by
      dsimp [Yn]
      exact (measurable_pi_apply (n + 1)).aemeasurable, ?_⟩
    -- Proof comment: time `n + 1` is the second marginal of the pair law recovered by
    -- `headIndexedPathMeasure_map_headAndNext`.
    calc
      Measure.map (Yn n) (P : Measure (ℕ → (ℕ → unitInterval))) =
          Measure.map Prod.snd
            (Measure.map (headAndNext (β := ℕ → unitInterval) n)
              (P : Measure (ℕ → (ℕ → unitInterval)))) := by
                rw [Measure.map_map measurable_snd (by fun_prop)]
                rfl
      _ =
          Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
              rw [hpair n]
      _ = (νn n : Measure (ℕ → unitInterval)) := hsnd n
  have hbadMeasure :
      ∀ m n,
        (P : Measure (ℕ → (ℕ → unitInterval))) (bad m n) =
          ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
            {z | (1 / 2 : ℝ) ^ m < dist z.1 z.2}) := by
    intro m n
    -- Proof comment: reuse the shared `headAndNext` bad-event bridge instead of rebuilding the
    -- same preimage extensionality argument locally.
    simpa [bad] using
      (measure_headAndNext_badPair_eq
        (P := (P : Measure (ℕ → (ℕ → unitInterval))))
        (π := (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))))
        (m := m) (n := n) (hpair n))
  have hbadPm :
      ∀ m : ℕ,
        (∑' n, (P : Measure (ℕ → (ℕ → unitInterval))) (bad m n)) ≠ ∞ := by
    intro m
    have hbadFun :
        (fun n ↦ (P : Measure (ℕ → (ℕ → unitInterval))) (bad m n)) =
          (fun n ↦
            ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
              {z | (1 / 2 : ℝ) ^ m < dist z.1 z.2})) := by
      funext n
      exact hbadMeasure m n
    rw [hbadFun]
    exact hbad m
  have htail :
      ∀ m : ℕ, ∀ᵐ ω ∂(P : Measure (ℕ → (ℕ → unitInterval))),
        ∀ᶠ n : ℕ in atTop, dist (Yn n ω) (Y ω) ≤ (1 / 2 : ℝ) ^ m := by
    intro m
    -- Proof comment: Borel-Cantelli upgrades summable bad-event masses to eventual dyadic
    -- control along almost every path.
    filter_upwards [MeasureTheory.ae_eventually_notMem (μ := (P : Measure (ℕ → (ℕ → unitInterval))))
      (s := bad m) (hbadPm m)] with ω hω
    exact hω.mono fun n hn ↦ not_lt.mp hn
  refine ⟨ℕ → (ℕ → ↥unitInterval), inferInstance, P, Y, Yn, hY, hYn, ?_⟩
  simpa [Y, Yn] using htail

/-- Helper for Theorem 17.56: on a finite discrete alphabet, the singleton-mass functional is
continuous in the weak topology. -/
private theorem continuousFiniteDiscreteSingletonMassReal
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α] (a : α) :
    Continuous fun ρ : ProbabilityMeasure α ↦ (ρ : Measure α).real {a} := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let f : BoundedContinuousFunction α ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun x : α ↦ if x = a then 1 else 0) 1 <| by
        intro x
        by_cases hx : x = a
        · simp [hx]
        · simp [hx]
  have hEq :
      (fun ρ : ProbabilityMeasure α ↦ (ρ : Measure α).real {a}) =
        fun ρ : ProbabilityMeasure α ↦ ∫ x, f x ∂(ρ : Measure α) := by
    funext ρ
    -- Proof comment: on a finite discrete alphabet, only the singleton `{a}` contributes to the
    -- integral of the indicator test function `f`.
    rw [MeasureTheory.integral_fintype (μ := (ρ : Measure α)) (f := fun x : α ↦ f x)
      (BoundedContinuousFunction.integrable (ρ : Measure α) f)]
    simp [f, smul_eq_mul]
  rw [hEq]
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

/-- Helper for Theorem 17.56: on a finite discrete alphabet, weak convergence is already
determined by convergence of the singleton masses. -/
private theorem tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    {νn : ℕ → ProbabilityMeasure α} {ν : ProbabilityMeasure α}
    (hνn :
      ∀ a : α,
        Tendsto (fun n ↦ (νn n : Measure α).real {a}) atTop
          (𝓝 ((ν : Measure α).real {a}))) :
    Tendsto νn atTop (𝓝 ν) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hIntegral (ρ : ProbabilityMeasure α) :
      ∫ x, f x ∂(ρ : Measure α) = ∑ a : α, (ρ : Measure α).real {a} * f a := by
    -- Proof comment: on a finite discrete alphabet, every bounded continuous test integral is a
    -- finite weighted sum of singleton masses.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := (ρ : Measure α)) (f := fun x : α ↦ f x)
        (BoundedContinuousFunction.integrable (ρ : Measure α) f))
  rw [show (fun n ↦ ∫ x, f x ∂(νn n : Measure α)) =
      fun n ↦ ∑ a : α, (νn n : Measure α).real {a} * f a by
        funext n
        exact hIntegral (νn n)]
  rw [show ∫ x, f x ∂(ν : Measure α) =
      ∑ a : α, (ν : Measure α).real {a} * f a by
        exact hIntegral ν]
  -- Proof comment: once the integrals are expanded as finite sums, convergence is coordinatewise.
  exact tendsto_finset_sum _ fun a _ ↦ by
    simpa [mul_comm] using (hνn a).const_mul (f a)

/-- Helper for Theorem 17.56: weak convergence on the Hilbert cube pushes through every fixed
finite measurable label map whose singleton fibers have `ν`-null frontier. -/
private theorem tendstoFiniteDiscretePushforward_of_nullFrontierSingletons
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {q : (ℕ → unitInterval) → α} (hq : Measurable q)
    (hfrontier : ∀ a : α, (ν : Measure (ℕ → unitInterval)) (frontier (q ⁻¹' {a})) = 0) :
    Tendsto (fun n ↦ (νn n).map hq.aemeasurable) atTop (𝓝 (ν.map hq.aemeasurable)) := by
  classical
  refine tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto ?_
  intro a
  have hmass :
      Tendsto
        (fun n ↦
          (((νn n).map hq.aemeasurable : ProbabilityMeasure α) : Measure α) {a})
        atTop
        (𝓝 ((((ν.map hq.aemeasurable : ProbabilityMeasure α) : Measure α) {a}))) := by
    have hpreimage :
        Tendsto
          (fun n ↦ (νn n : Measure (ℕ → unitInterval)) (q ⁻¹' {a}))
          atTop
          (𝓝 ((ν : Measure (ℕ → unitInterval)) (q ⁻¹' {a}))) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hνn (hfrontier a)
    -- Proof comment: the pushforward singleton mass is exactly the mass of the corresponding
    -- quantizer fiber, so Portmanteau applies directly to that fiber.
    rw [show (fun n ↦
        (((νn n).map hq.aemeasurable : ProbabilityMeasure α) : Measure α) {a}) =
        fun n ↦ (νn n : Measure (ℕ → unitInterval)) (q ⁻¹' {a}) by
          funext n
          rw [ProbabilityMeasure.map_apply' (ν := νn n) (f := q) hq.aemeasurable
            (MeasurableSet.singleton a)]]
    rw [show (((ν.map hq.aemeasurable : ProbabilityMeasure α) : Measure α) {a}) =
        (ν : Measure (ℕ → unitInterval)) (q ⁻¹' {a}) by
          rw [ProbabilityMeasure.map_apply' (ν := ν) (f := q) hq.aemeasurable
            (MeasurableSet.singleton a)]]
    exact hpreimage
  -- Proof comment: every finite pushforward law is determined by its singleton masses.
  have hsingleton_ne_top :
      (((ν.map hq.aemeasurable : ProbabilityMeasure α) : Measure α)
        ({a} : Set α)) ≠ ∞ :=
    measure_ne_top _ _
  exact
    (ENNReal.continuousAt_toReal hsingleton_ne_top).tendsto.comp <|
      by simpa [Measure.real_def] using hmass

/-- Helper for Theorem 17.56: adding finitely many fiber constraints preserves the null-frontier
property because the frontier of a finite intersection sits inside the union of the coordinate
frontiers. -/
private theorem nullFrontier_biInter_finset
    (μ : Measure (ℕ → unitInterval)) {ι : Type*} (s : Finset ι)
    {A : ι → Set (ℕ → unitInterval)}
    (hfrontier : ∀ i : ι, μ (frontier (A i)) = 0) :
    μ (frontier (⋂ i ∈ s, A i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty family intersects to `univ`, whose frontier is empty.
      simp
  | @insert i s his ih =>
      have hsubset' :
          frontier ((⋂ j ∈ s, A j) ∩ A i) ⊆
            frontier (⋂ j ∈ s, A j) ∩ closure (A i) ∪
              closure (⋂ j ∈ s, A j) ∩ frontier (A i) :=
        frontier_inter_subset _ _
      have hsubset :
          frontier ((⋂ j ∈ s, A j) ∩ A i) ⊆
            frontier (⋂ j ∈ s, A j) ∪ frontier (A i) := by
        intro x hx
        rcases hsubset' hx with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr hx.2
      have hunion :
          μ (frontier (⋂ j ∈ s, A j) ∪ frontier (A i)) = 0 :=
        measure_union_null ih (hfrontier i)
      -- Proof comment: the new frontier contributes only through the previous frontier and the
      -- newly added coordinate frontier, both of which already have zero mass.
      simpa [Finset.set_biInter_insert, his, Set.inter_assoc, Set.inter_left_comm,
        Set.inter_comm] using
        measure_mono_null hsubset hunion

/-- Helper for Theorem 17.56: the fiber of a finite product label map is exactly the finite
intersection of the coordinate singleton fibers. -/
private theorem preimage_singleton_piLabel_eq_biInter
    {ι : Type*} [Fintype ι] {α : ι → Type*}
    {q : ∀ i, (ℕ → unitInterval) → α i} (a : ∀ i, α i) :
    (fun x i ↦ q i x) ⁻¹' {a} = ⋂ i ∈ (Finset.univ : Finset ι), q i ⁻¹' {a i} := by
  -- Proof comment: equality in a finite product is coordinatewise equality.
  ext x
  simp [funext_iff]

/-- Helper for Theorem 17.56: once each coordinate quantizer has singleton fibers with
`ν`-null frontier, the finite product stage label map inherits the same null-frontier property on
every singleton fiber. -/
private theorem nullFrontier_piLabelFiber_of_nullFrontierSingletons
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    {ι : Type*} [Fintype ι] {α : ι → Type*}
    {q : ∀ i, (ℕ → unitInterval) → α i}
    (hfrontier :
      ∀ i : ι, ∀ a : α i,
        (ν : Measure (ℕ → unitInterval)) (frontier (q i ⁻¹' {a})) = 0) :
    ∀ a : ∀ i, α i,
      (ν : Measure (ℕ → unitInterval))
        (frontier ((fun x i ↦ q i x) ⁻¹' {a})) = 0 := by
  classical
  intro a
  have hbiInter :
      (ν : Measure (ℕ → unitInterval))
        (frontier (⋂ i ∈ (Finset.univ : Finset ι), q i ⁻¹' {a i})) = 0 :=
    nullFrontier_biInter_finset
      (μ := (ν : Measure (ℕ → unitInterval)))
      (s := Finset.univ)
      (A := fun i ↦ q i ⁻¹' {a i})
      (hfrontier := fun i ↦ hfrontier i (a i))
  -- Proof comment: rewrite the product fiber as the finite intersection of its coordinate fibers.
  simpa [preimage_singleton_piLabel_eq_biInter (q := q) a] using hbiInter

/-- Helper for Theorem 17.56: the finite stage-`J` quantizer alphabet is the product of the
first `J + 1` dyadic quantizer alphabets. -/
private abbrev StageLabel (k : ℕ → ℕ) (J : ℕ) :=
  ∀ i : Fin (J + 1), Fin (k i.1)

/-- Helper for Theorem 17.56: bundle the coordinate quantizers `q m` into one stage label map on
the first `J + 1` dyadic scales. -/
private def stageLabelMap
    {k : ℕ → ℕ} (q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)) (J : ℕ) :
    (ℕ → unitInterval) → StageLabel k J :=
  fun x i ↦ q i.1 x

/-- Helper for Theorem 17.56: the bundled stage label map is measurable because each coordinate
quantizer is measurable. -/
private theorem measurable_stageLabelMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ) :
    Measurable (stageLabelMap (k := k) q J) := by
  -- Proof comment: finite-product measurability is checked one coordinate at a time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [stageLabelMap] using hq i.1

/-- Helper for Theorem 17.56: every singleton fiber of the bundled stage label map has
`ν`-null frontier once the coordinate singleton fibers do. -/
private theorem stageLabelMap_nullFrontier_of_nullFrontierSingletons
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    ∀ a : StageLabel k J,
      (ν : Measure (ℕ → unitInterval))
        (frontier (stageLabelMap (k := k) q J ⁻¹' {a})) = 0 := by
  intro a
  -- Proof comment: the bundled fiber is a finite intersection of coordinate singleton fibers, so
  -- the previously proved finite-intersection null-frontier lemma applies directly.
  simpa [StageLabel, stageLabelMap] using
    (nullFrontier_piLabelFiber_of_nullFrontierSingletons
      (ν := ν)
      (α := fun i : Fin (J + 1) ↦ Fin (k i.1))
      (q := fun i : Fin (J + 1) ↦ q i.1)
      (hfrontier := fun i ↦ hfrontier i.1) a)

/-- Helper for Theorem 17.56: projecting the bundled stage label map to coordinate `m ≤ J`
recovers the original scale-`m` quantizer exactly. -/
private theorem stageLabelMap_apply_coord
    {k : ℕ → ℕ} (q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m))
    {J m : ℕ} (hm : m ≤ J) :
    (fun x ↦ stageLabelMap (k := k) q J x ⟨m, Nat.lt_succ_of_le hm⟩) = q m := by
  -- Proof comment: the bundled map stores the `m`th quantizer as its `m`th coordinate by
  -- definition, so the projection is definitional.
  rfl

/-- Helper for Theorem 17.56: drop the last coordinate of a stage label. This is the canonical
prefix projection from stage `J + 1` to stage `J`. -/
private def stageLabelTruncate
    {k : ℕ → ℕ} (J : ℕ) : StageLabel k (J + 1) → StageLabel k J :=
  fun a i ↦ a i.castSucc

/-- Helper for Theorem 17.56: the stage truncation map is measurable because it is a finite
product coordinate projection. -/
private theorem measurable_stageLabelTruncate
    {k : ℕ → ℕ} (J : ℕ) :
    Measurable (stageLabelTruncate (k := k) J) := by
  -- Proof comment: finite-product measurability again reduces to coordinate evaluations.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [stageLabelTruncate] using measurable_pi_apply i.castSucc

/-- Helper for Theorem 17.56: truncating a stage label built from quantizers simply forgets the
last quantizer and recovers the shorter bundled stage map. -/
private theorem stageLabelTruncate_comp_stageLabelMap
    {k : ℕ → ℕ} (q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)) (J : ℕ) :
    stageLabelTruncate (k := k) J ∘ stageLabelMap (k := k) q (J + 1) =
      stageLabelMap (k := k) q J := by
  -- Proof comment: both sides evaluate each prefix coordinate with the same quantizer `q i.1`.
  funext x i
  rfl

/-- Helper for Theorem 17.56: a successor-stage label is exactly a prefix stage label together
with one new last coordinate. -/
private def stageLabelSuccEquiv
    {k : ℕ → ℕ} (J : ℕ) :
    StageLabel k (J + 1) ≃ StageLabel k J × Fin (k (J + 1)) where
  toFun a := (stageLabelTruncate (k := k) J a, a (Fin.last (J + 1)))
  invFun b := Fin.snoc b.1 b.2
  left_inv a := by
    -- Proof comment: splitting a successor-stage label into its prefix and final coordinate and
    -- then gluing them back with `Fin.snoc` recovers the original label coordinatewise.
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [stageLabelTruncate]
    | cast i =>
        simp [stageLabelTruncate]
  right_inv b := by
    -- Proof comment: the inverse recovers both the stored prefix and the stored final coordinate
    -- by the standard `Fin.init`/`Fin.snoc` identities.
    rcases b with ⟨a, c⟩
    ext <;> simp [stageLabelTruncate]

/-- Helper for Theorem 17.56: under `stageLabelSuccEquiv`, the first component is exactly the
canonical stage truncation. -/
@[simp] private theorem stageLabelSuccEquiv_fst
    {k : ℕ → ℕ} (J : ℕ) (a : StageLabel k (J + 1)) :
    (stageLabelSuccEquiv (k := k) J a).1 = stageLabelTruncate (k := k) J a := by
  -- Proof comment: the first component of the product normal form is definitionally the prefix
  -- stage label.
  rfl

/-- Helper for Theorem 17.56: under `stageLabelSuccEquiv`, the second component is the new last
coordinate. -/
@[simp] private theorem stageLabelSuccEquiv_snd
    {k : ℕ → ℕ} (J : ℕ) (a : StageLabel k (J + 1)) :
    (stageLabelSuccEquiv (k := k) J a).2 = a (Fin.last (J + 1)) := by
  -- Proof comment: the successor-stage product normal form stores the new coordinate as its
  -- second component by construction.
  rfl

/-- Helper for Theorem 17.56: rebuilding a successor-stage label from its prefix and last
coordinate via `stageLabelSuccEquiv.symm` is just `Fin.snoc`. -/
@[simp] private theorem stageLabelSuccEquiv_symm_apply
    {k : ℕ → ℕ} (J : ℕ) (a : StageLabel k J) (c : Fin (k (J + 1))) :
    (stageLabelSuccEquiv (k := k) J).symm (a, c) = Fin.snoc a c := by
  -- Proof comment: the inverse direction of the product normal form is the tuple constructor
  -- that appends the new coordinate at the end.
  rfl

/-- Helper for Theorem 17.56: once the coarse prefix and the new last coordinate both stabilize
along the tail, the reconstructed successor-stage labels stabilize as well. -/
private theorem eventuallyEq_stageLabelSucc_of_components
    {k : ℕ → ℕ} (J : ℕ)
    {ξ : ℕ → StageLabel k J} {ζ : ℕ → Fin (k (J + 1))} :
    (∀ᶠ n : ℕ in atTop, ξ (n + 1) = ξ 0) →
      (∀ᶠ n : ℕ in atTop, ζ (n + 1) = ζ 0) →
      ∀ᶠ n : ℕ in atTop,
        (stageLabelSuccEquiv (k := k) J).symm (ξ (n + 1), ζ (n + 1)) =
          (stageLabelSuccEquiv (k := k) J).symm (ξ 0, ζ 0) := by
  intro hξ hζ
  -- Proof comment: after both components are frozen, the successor-stage label is frozen because
  -- `stageLabelSuccEquiv.symm` rebuilds it componentwise.
  filter_upwards [hξ, hζ] with n hnξ hnζ
  simp [hnξ, hnζ]

/-- Helper for Theorem 17.56: the preceding tail-stabilization statement can be applied
pointwise on an almost-sure set of paths. -/
private theorem ae_eventuallyEq_stageLabelSucc_of_components
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {k : ℕ → ℕ} (J : ℕ)
    {ξ : Ω → ℕ → StageLabel k J} {ζ : Ω → ℕ → Fin (k (J + 1))} :
    (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ξ ω (n + 1) = ξ ω 0) →
      (∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ζ ω (n + 1) = ζ ω 0) →
      ∀ᵐ ω ∂P,
        ∀ᶠ n : ℕ in atTop,
          (stageLabelSuccEquiv (k := k) J).symm (ξ ω (n + 1), ζ ω (n + 1)) =
            (stageLabelSuccEquiv (k := k) J).symm (ξ ω 0, ζ ω 0) := by
  intro hξ hζ
  -- Proof comment: apply the one-path tail lemma on the almost-sure set where both component
  -- tails are already available.
  filter_upwards [hξ, hζ] with ω hωξ hωζ
  exact eventuallyEq_stageLabelSucc_of_components (k := k) J hωξ hωζ

/-- Helper for Theorem 17.56: under the successor-stage product normal form, quantizing at stage
`J + 1` is exactly the pair consisting of the stage-`J` quantization and the new last
coordinate. -/
private theorem stageLabelSuccEquiv_comp_stageLabelMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (J : ℕ) :
    stageLabelSuccEquiv (k := k) J ∘ stageLabelMap (k := k) q (J + 1) =
      fun x ↦ (stageLabelMap (k := k) q J x, q (J + 1) x) := by
  -- Proof comment: the first component is the truncation of the fine stage label, while the
  -- second component is the newly appended quantized coordinate.
  funext x
  ext i
  · simp [stageLabelSuccEquiv, stageLabelTruncate, stageLabelMap]
  · simp [stageLabelMap, stageLabelSuccEquiv]

/-- Helper for Theorem 17.56: pushing a law forward by the successor-stage label map and then
splitting it with `stageLabelSuccEquiv` is the same as pushing forward directly to the product
of the coarse stage label and the new last coordinate. -/
private theorem measurable_successorStagePairMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ) :
    Measurable (fun x : ℕ → unitInterval ↦ (stageLabelMap (k := k) q J x, q (J + 1) x)) := by
  -- Proof comment: the successor-stage pair map is just the product of the already measurable
  -- coarse stage-label map and the measurable last-coordinate quantizer.
  exact
    (measurable_stageLabelMap (k := k) (q := q) hq J).prodMk (hq (J + 1))

/-- Helper for Theorem 17.56: pushing a law forward by the successor-stage label map and then
splitting it with `stageLabelSuccEquiv` is the same as pushing forward directly to the product
of the coarse stage label and the new last coordinate. -/
private theorem map_stageLabelSuccEquiv_stageLabelMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ) (μ : Measure (ℕ → unitInterval)) :
    Measure.map (stageLabelSuccEquiv (k := k) J)
        (Measure.map (stageLabelMap (k := k) q (J + 1)) μ) =
      Measure.map (fun x ↦ (stageLabelMap (k := k) q J x, q (J + 1) x)) μ := by
  -- Proof comment: once the function-level normal form is fixed, the pushforward identity is
  -- just one `Measure.map_map` normalization.
  rw [Measure.map_map (measurable_of_finite (stageLabelSuccEquiv (k := k) J))
    (measurable_stageLabelMap (k := k) (q := q) hq (J + 1))]
  simp [stageLabelSuccEquiv_comp_stageLabelMap]

/-- Helper for Theorem 17.56: after splitting a successor-stage quantized law into its coarse
prefix and new last coordinate, the two product marginals are exactly the expected stage-`J`
quantized law and the final quantizer output. -/
private theorem successorStageJointLawSpec
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ) (μ : Measure (ℕ → unitInterval)) :
    Measure.map Prod.fst
        (Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (stageLabelMap (k := k) q (J + 1)) μ)) =
      Measure.map (stageLabelMap (k := k) q J) μ ∧
    Measure.map Prod.snd
        (Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (stageLabelMap (k := k) q (J + 1)) μ)) =
      Measure.map (q (J + 1)) μ := by
  have hpairMeas :
      Measurable (fun x ↦ (stageLabelMap (k := k) q J x, q (J + 1) x)) :=
    measurable_successorStagePairMap (k := k) (q := q) hq J
  constructor
  · -- Proof comment: the first product component is exactly the stage-`J` quantization, so one
    -- `Measure.map_map` normalization recovers the coarse law.
    calc
      Measure.map Prod.fst
          (Measure.map (stageLabelSuccEquiv (k := k) J)
            (Measure.map (stageLabelMap (k := k) q (J + 1)) μ)) =
        Measure.map Prod.fst
          (Measure.map (fun x ↦ (stageLabelMap (k := k) q J x, q (J + 1) x)) μ) := by
            rw [map_stageLabelSuccEquiv_stageLabelMap (k := k) (q := q) hq J μ]
      _ = Measure.map (stageLabelMap (k := k) q J) μ := by
            rw [Measure.map_map measurable_fst hpairMeas]
            rfl
  · -- Proof comment: the second product component is literally the new last-coordinate quantizer.
    calc
      Measure.map Prod.snd
          (Measure.map (stageLabelSuccEquiv (k := k) J)
            (Measure.map (stageLabelMap (k := k) q (J + 1)) μ)) =
        Measure.map Prod.snd
          (Measure.map (fun x ↦ (stageLabelMap (k := k) q J x, q (J + 1) x)) μ) := by
            rw [map_stageLabelSuccEquiv_stageLabelMap (k := k) (q := q) hq J μ]
      _ = Measure.map (q (J + 1)) μ := by
            rw [Measure.map_map measurable_snd hpairMeas]
            rfl

/-- Helper for Theorem 17.56: the explicit successor-stage convergence hypothesis remains valid
after moving to the `stageLabelSuccEquiv` product normal form. -/
private theorem successorStageJointLawTendsto
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ)
    (hSuccTendsto :
      Tendsto
        (fun n ↦
          (νn n).map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
        atTop
        (𝓝
          (ν.map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)))) :
    Tendsto
      (fun n ↦
        ((νn n).map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
          ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))
      atTop
      (𝓝
        ((ν.map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
          ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))) := by
  let e : StageLabel k (J + 1) → StageLabel k J × Fin (k (J + 1)) :=
    stageLabelSuccEquiv (k := k) J
  have heCont : Continuous e := by
    -- Proof comment: the successor-stage alphabet and its product normal form are finite
    -- discrete spaces, so the equivalence map is automatically continuous.
    exact continuous_of_discreteTopology
  -- Proof comment: map the already-assumed successor-stage convergence through the fixed product
  -- normal form once, so later rowwise arguments can stay in `(prefix, last)` coordinates.
  simpa [e] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦
        (νn n).map
          ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
      (ν.map
        ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
      hSuccTendsto heCont

/-- Helper for Theorem 17.56: append the distinguished zero label at the new last coordinate of a
stage label. This is the canonical section of `stageLabelTruncate` once the new alphabet is
nonempty. -/
private def stageLabelZeroExtension
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) :
    StageLabel k J → StageLabel k (J + 1) :=
  fun a ↦ Fin.snoc a ⟨0, hnext⟩

/-- Helper for Theorem 17.56: the canonical zero extension of a stage label is measurable because
its codomain is finite. -/
private theorem measurable_stageLabelZeroExtension
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) :
    Measurable (stageLabelZeroExtension (k := k) J hnext) := by
  -- Proof comment: maps into the finite successor-stage alphabet are measurable automatically.
  exact measurable_of_finite _

/-- Helper for Theorem 17.56: truncating the canonical zero extension recovers the original stage
label. -/
@[simp] private theorem stageLabelTruncate_zeroExtension
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) (a : StageLabel k J) :
    stageLabelTruncate (k := k) J (stageLabelZeroExtension (k := k) J hnext a) = a := by
  -- Proof comment: `stageLabelTruncate` forgets exactly the new final coordinate inserted by
  -- `stageLabelZeroExtension`.
  ext i
  simp [stageLabelTruncate, stageLabelZeroExtension]

/-- Helper for Theorem 17.56: the canonical zero extension of stage labels is injective because
stage truncation is its left inverse. -/
private theorem stageLabelZeroExtension_injective
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) :
    Function.Injective (stageLabelZeroExtension (k := k) J hnext) := by
  -- Proof comment: applying `stageLabelTruncate` after zero extension recovers the original
  -- stage label, so two zero extensions can only agree if their sources already agree.
  intro a b hab
  simpa using congrArg (stageLabelTruncate (k := k) J) hab

/-- Helper for Theorem 17.56: extend a whole stage-label path by appending the zero label at the
new final coordinate of every time slice. -/
private def stageLabelZeroExtensionPath
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) :
    (ℕ → StageLabel k J) → (ℕ → StageLabel k (J + 1)) :=
  fun ω n ↦ stageLabelZeroExtension (k := k) J hnext (ω n)

/-- Helper for Theorem 17.56: the coordinatewise zero-extension of stage-label paths is
measurable. -/
private theorem measurable_stageLabelZeroExtensionPath
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) :
    Measurable (stageLabelZeroExtensionPath (k := k) J hnext) := by
  -- Proof comment: measurability on path space reduces to measurability of each time
  -- coordinate, where the one-step zero extension is already measurable.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact (measurable_stageLabelZeroExtension (k := k) J hnext).comp (measurable_pi_apply n)

/-- Helper for Theorem 17.56: truncate a stage-label path by dropping the last coordinate at every
time slice. -/
private def stageLabelTruncatePath
    {k : ℕ → ℕ} (J : ℕ) :
    (ℕ → StageLabel k (J + 1)) → (ℕ → StageLabel k J) :=
  fun ω n ↦ stageLabelTruncate (k := k) J (ω n)

/-- Helper for Theorem 17.56: the coordinatewise stage truncation map on path space is
measurable. -/
private theorem measurable_stageLabelTruncatePath
    {k : ℕ → ℕ} (J : ℕ) :
    Measurable (stageLabelTruncatePath (k := k) J) := by
  -- Proof comment: the pathwise truncation is measurable because each time coordinate is the
  -- measurable one-step truncation already isolated above.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact (measurable_stageLabelTruncate (k := k) J).comp (measurable_pi_apply n)

/-- Helper for Theorem 17.56: apply the bundled stage quantizer coordinatewise to an ambient
Hilbert-cube path. -/
private def stageLabelPathMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (J : ℕ) :
    (ℕ → (ℕ → unitInterval)) → (ℕ → StageLabel k J) :=
  fun ω n ↦ stageLabelMap (k := k) q J (ω n)

/-- Helper for Theorem 17.56: the pathwise bundled stage quantizer is measurable because each
time coordinate is measured by the finite stage map. -/
private theorem measurable_stageLabelPathMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ) :
    Measurable (stageLabelPathMap (k := k) (q := q) J) := by
  -- Proof comment: measurability on path space again reduces to measurability of each time
  -- coordinate, where the bundled stage map is already measurable.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact
    (measurable_stageLabelMap (k := k) (q := q) hq J).comp
      (measurable_pi_apply n)

/-- Helper for Theorem 17.56: truncating the pathwise successor-stage quantizer simply forgets
the last quantizer at every time and recovers the shorter stage path map. -/
@[simp] private theorem stageLabelTruncatePath_comp_stageLabelPathMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (J : ℕ) :
    stageLabelTruncatePath (k := k) J ∘ stageLabelPathMap (k := k) (q := q) (J + 1) =
      stageLabelPathMap (k := k) (q := q) J := by
  -- Proof comment: the one-step stage truncation identity already holds pointwise on every
  -- ambient state, so the pathwise statement is just function extensionality in two variables.
  funext ω n
  exact congrFun (stageLabelTruncate_comp_stageLabelMap (k := k) q J) (ω n)

/-- Helper for Theorem 17.56: the same stage-truncation compatibility holds after pushing an
ambient path law through the pathwise stage maps. -/
private theorem stageLabelTruncatePath_probabilityMap_stageLabelPathMap
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (μ : ProbabilityMeasure (ℕ → (ℕ → unitInterval))) :
    (μ.map ((measurable_stageLabelPathMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
        (f := stageLabelTruncatePath (k := k) J)
        (measurable_stageLabelTruncatePath (k := k) J).aemeasurable =
      μ.map ((measurable_stageLabelPathMap (k := k) (q := q) hq J).aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: after coercing to ordinary measures, the two probability laws are related by
  -- one `Measure.map_map` normalization and the pathwise truncation identity above.
  change
    Measure.map (stageLabelTruncatePath (k := k) J)
        (Measure.map (stageLabelPathMap (k := k) (q := q) (J + 1))
          (μ : Measure (ℕ → (ℕ → unitInterval)))) =
      Measure.map (stageLabelPathMap (k := k) (q := q) J)
        (μ : Measure (ℕ → (ℕ → unitInterval)))
  rw [Measure.map_map
    (measurable_stageLabelTruncatePath (k := k) J)
    (measurable_stageLabelPathMap (k := k) (q := q) hq (J + 1))]
  simpa [Function.comp] using
    congrArg
      (fun f : (ℕ → (ℕ → unitInterval)) → (ℕ → StageLabel k J) ↦ Measure.map f μ)
      (stageLabelTruncatePath_comp_stageLabelPathMap (k := k) (q := q) J)

/-- Helper for Theorem 17.56: truncating a coordinatewise zero-extended path recovers the original
stage-label path. -/
@[simp] private theorem stageLabelTruncatePath_zeroExtensionPath
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) (ω : ℕ → StageLabel k J) :
    stageLabelTruncatePath (k := k) J
        (stageLabelZeroExtensionPath (k := k) J hnext ω) = ω := by
  -- Proof comment: the pointwise truncation/extension identities assemble into the pathwise
  -- identity by function extensionality.
  funext n
  exact stageLabelTruncate_zeroExtension (k := k) J hnext (ω n)

/-- Helper for Theorem 17.56: coordinatewise zero extension preserves the label-tail event
exactly. -/
private theorem stageLabelZeroExtensionPath_mem_labelTailEvent_iff
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) {N : ℕ}
    {ω : ℕ → StageLabel k J} :
    stageLabelZeroExtensionPath (k := k) J hnext ω ∈ labelTailEvent N ↔
      ω ∈ labelTailEvent N := by
  constructor
  · intro hω n hn
    exact stageLabelZeroExtension_injective (k := k) J hnext (hω n hn)
  · intro hω n hn
    exact congrArg (stageLabelZeroExtension (k := k) J hnext) (hω n hn)

/-- Helper for Theorem 17.56: pushing a path law forward by coordinatewise zero extension does not
change the probability of the label-tail event. -/
private theorem stageLabelZeroExtensionPath_map_labelTailEvent
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1)) {N : ℕ}
    (μ : Measure (ℕ → StageLabel k J)) :
    Measure.map (stageLabelZeroExtensionPath (k := k) J hnext) μ
        (labelTailEvent N) =
      μ (labelTailEvent N) := by
  -- Proof comment: the pathwise zero extension preserves tail-event membership exactly, so the
  -- pushforward measure sees the same tail event probability.
  rw [Measure.map_apply
      (measurable_stageLabelZeroExtensionPath (k := k) J hnext)
      (measurableSet_labelTailEvent (α := StageLabel k (J + 1)) N)]
  refine congrArg (fun s : Set (ℕ → StageLabel k J) ↦ μ s) ?_
  ext ω
  simpa [Set.mem_preimage] using
    (stageLabelZeroExtensionPath_mem_labelTailEvent_iff (k := k) J hnext
      (N := N) (ω := ω))

/-- Helper for Theorem 17.56: pushing a stage-label path law forward by coordinatewise zero
extension and then truncating it again recovers the original path law. -/
private theorem stageLabelTruncatePath_map_zeroExtensionPath
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1))
    (μ : Measure (ℕ → StageLabel k J)) :
    Measure.map (stageLabelTruncatePath (k := k) J)
        (Measure.map (stageLabelZeroExtensionPath (k := k) J hnext) μ) = μ := by
  -- Proof comment: the two path maps compose to the identity, so functoriality of
  -- `Measure.map` collapses the round trip immediately.
  have hcomp :
      stageLabelTruncatePath (k := k) J ∘ stageLabelZeroExtensionPath (k := k) J hnext = id := by
    funext ω
    exact stageLabelTruncatePath_zeroExtensionPath (k := k) J hnext ω
  rw [Measure.map_map
      (measurable_stageLabelTruncatePath (k := k) J)
      (measurable_stageLabelZeroExtensionPath (k := k) J hnext)]
  simpa [hcomp] using (Measure.map_id (μ := μ))

/-- Helper for Theorem 17.56: the same round-trip identity holds at the probability-measure
level. -/
private theorem stageLabelTruncatePath_probabilityMap_zeroExtensionPath
    {k : ℕ → ℕ} (J : ℕ) (hnext : 0 < k (J + 1))
    (μ : ProbabilityMeasure (ℕ → StageLabel k J)) :
    (μ.map ((measurable_stageLabelZeroExtensionPath (k := k) J hnext).aemeasurable)).map
        (f := stageLabelTruncatePath (k := k) J)
        (measurable_stageLabelTruncatePath (k := k) J).aemeasurable =
      μ := by
  -- Proof comment: after coercing back to ordinary measures, this is exactly the round-trip
  -- pushforward identity just proved on path space.
  apply ProbabilityMeasure.toMeasure_injective
  simpa using
    stageLabelTruncatePath_map_zeroExtensionPath
      (k := k) J hnext (μ := (μ : Measure (ℕ → StageLabel k J)))

/-- Helper for Theorem 17.56: the stage-`J + 1` pushforward projects under truncation to the
stage-`J` pushforward. -/
private theorem stageLabelTruncate_map_stageLabelPushforward
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ) (μ : Measure (ℕ → unitInterval)) :
    Measure.map (stageLabelTruncate (k := k) J)
        (Measure.map (stageLabelMap (k := k) q (J + 1)) μ) =
      Measure.map (stageLabelMap (k := k) q J) μ := by
  -- Proof comment: rewrite the double pushforward as one composed pushforward, then collapse the
  -- composition with the definitional truncation identity.
  rw [Measure.map_map
      (measurable_stageLabelTruncate (k := k) J)
      (measurable_stageLabelMap (k := k) (q := q) hq (J + 1))]
  simpa [Function.comp] using
    congrArg (fun f : (ℕ → unitInterval) → StageLabel k J ↦ Measure.map f μ)
      (stageLabelTruncate_comp_stageLabelMap (k := k) q J)

/-- Helper for Theorem 17.56: the same truncation compatibility holds at the probability-measure
level. -/
private theorem stageLabelTruncate_probabilityMap_stageLabelPushforward
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (μ : ProbabilityMeasure (ℕ → unitInterval)) :
    (μ.map ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
        (f := stageLabelTruncate (k := k) J)
        (measurable_stageLabelTruncate (k := k) J).aemeasurable =
      μ.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable) := by
  -- Proof comment: after coercing to measures, the probability statement is exactly the measure
  -- pushforward identity already proved above.
  apply ProbabilityMeasure.toMeasure_injective
  simpa using
    stageLabelTruncate_map_stageLabelPushforward
      (k := k) (q := q) hq J (μ := (μ : Measure (ℕ → unitInterval)))

/-- Helper for Theorem 17.56: eventual constancy of a successor-stage label path survives after
dropping the final stage coordinate. -/
private theorem stageLabelTruncatePath_mem_labelTailEvent
    {k : ℕ → ℕ} (J : ℕ) {N : ℕ}
    {ω : ℕ → StageLabel k (J + 1)}
    (hω : ω ∈ labelTailEvent (α := StageLabel k (J + 1)) N) :
    stageLabelTruncatePath (k := k) J ω ∈ labelTailEvent (α := StageLabel k J) N := by
  -- Proof comment: once the finer labels agree with time `0`, applying stage truncation to both
  -- sides preserves that agreement at the coarser stage.
  intro n hn
  exact congrArg (stageLabelTruncate (k := k) J) (hω n hn)

/-- Helper for Theorem 17.56: truncating successor-stage labels can only increase the probability
of the coarse eventual-constancy event. -/
private theorem le_stageLabelTruncatePath_map_labelTailEvent
    {k : ℕ → ℕ} (J : ℕ) {N : ℕ}
    (μ : Measure (ℕ → StageLabel k (J + 1))) :
    μ (labelTailEvent (α := StageLabel k (J + 1)) N) ≤
      Measure.map (stageLabelTruncatePath (k := k) J) μ
        (labelTailEvent (α := StageLabel k J) N) := by
  have hsubset :
      labelTailEvent (α := StageLabel k (J + 1)) N ⊆
        (stageLabelTruncatePath (k := k) J) ⁻¹'
          labelTailEvent (α := StageLabel k J) N := by
    intro ω hω
    simpa [Set.mem_preimage] using
      stageLabelTruncatePath_mem_labelTailEvent (k := k) J (N := N) hω
  calc
    μ (labelTailEvent (α := StageLabel k (J + 1)) N) ≤
        μ ((stageLabelTruncatePath (k := k) J) ⁻¹'
          labelTailEvent (α := StageLabel k J) N) := by
          exact measure_mono hsubset
    _ = Measure.map (stageLabelTruncatePath (k := k) J) μ
          (labelTailEvent (α := StageLabel k J) N) := by
          symm
          exact Measure.map_apply
            (measurable_stageLabelTruncatePath (k := k) J)
            (measurableSet_labelTailEvent (α := StageLabel k J) N)

/-- Helper for Theorem 17.56: the truncated probability law of a successor-stage path law has the
expected coarse head and time-coordinate marginals. -/
private theorem stageLabelTruncatePath_probabilityMap_marginals
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval))) :
    Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
        ((((PlabelSucc.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            ProbabilityMeasure (ℕ → StageLabel k J)) : Measure (ℕ → StageLabel k J))) =
      Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
    (∀ n : ℕ,
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          ((((PlabelSucc.map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
              ProbabilityMeasure (ℕ → StageLabel k J)) : Measure (ℕ → StageLabel k J))) =
        Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) := by
  constructor
  · -- Proof comment: the head coordinate of the truncated path is the head successor label
    -- followed by one-step stage truncation, so the existing pushforward compatibility closes it.
    have hheadComp :
        (fun ω : ℕ → StageLabel k J ↦ ω 0) ∘ stageLabelTruncatePath (k := k) J =
          stageLabelTruncate (k := k) J ∘
            (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0) := by
      funext ω
      rfl
    calc
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          ((((PlabelSucc.map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
              ProbabilityMeasure (ℕ → StageLabel k J)) : Measure (ℕ → StageLabel k J))) =
          Measure.map ((fun ω : ℕ → StageLabel k J ↦ ω 0) ∘
              stageLabelTruncatePath (k := k) J)
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
              change Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
                (Measure.map (stageLabelTruncatePath (k := k) J)
                  (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
                _
              rw [Measure.map_map
                (measurable_pi_apply 0)
                (measurable_stageLabelTruncatePath (k := k) J)]
      _ = Measure.map (stageLabelTruncate (k := k) J ∘
            (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0))
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
            rw [hheadComp]
      _ = Measure.map (stageLabelTruncate (k := k) J)
            (Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
              (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) := by
            rw [Measure.map_map
              (measurable_stageLabelTruncate (k := k) J)
              (measurable_pi_apply 0)]
      _ = Measure.map (stageLabelTruncate (k := k) J)
            (Measure.map (stageLabelMap (k := k) q (J + 1))
              (ν : Measure (ℕ → unitInterval))) := by rw [hhead]
      _ = Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval)) := by
            exact stageLabelTruncate_map_stageLabelPushforward
              (k := k) (q := q) hq J (μ := (ν : Measure (ℕ → unitInterval)))
  · intro n
    -- Proof comment: the same transport applies at every later time coordinate `n + 1`.
    have hcoordComp :
        (fun ω : ℕ → StageLabel k J ↦ ω (n + 1)) ∘ stageLabelTruncatePath (k := k) J =
          stageLabelTruncate (k := k) J ∘
            (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1)) := by
      funext ω
      rfl
    calc
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          ((((PlabelSucc.map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
              ProbabilityMeasure (ℕ → StageLabel k J)) : Measure (ℕ → StageLabel k J))) =
          Measure.map ((fun ω : ℕ → StageLabel k J ↦ ω (n + 1)) ∘
              stageLabelTruncatePath (k := k) J)
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
              change Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
                (Measure.map (stageLabelTruncatePath (k := k) J)
                  (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
                _
              rw [Measure.map_map
                (measurable_pi_apply (n + 1))
                (measurable_stageLabelTruncatePath (k := k) J)]
      _ = Measure.map (stageLabelTruncate (k := k) J ∘
            (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1)))
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
            rw [hcoordComp]
      _ = Measure.map (stageLabelTruncate (k := k) J)
            (Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
              (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) := by
            rw [Measure.map_map
              (measurable_stageLabelTruncate (k := k) J)
              (measurable_pi_apply (n + 1))]
      _ = Measure.map (stageLabelTruncate (k := k) J)
            (Measure.map (stageLabelMap (k := k) q (J + 1))
              (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval)) := by
            exact stageLabelTruncate_map_stageLabelPushforward
              (k := k) (q := q) hq J (μ := (νn n : Measure (ℕ → unitInterval)))

/-- Helper for Theorem 17.56: a deterministic tail cutoff for a successor-stage label law also
works after truncating that law to the previous stage. -/
private theorem stageLabelTruncatePath_probabilityMap_tailLowerBound
    {k : ℕ → ℕ} (J : ℕ) {ε : ℝ≥0} {N : ℕ}
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)))
    (htail :
      (1 : ℝ≥0∞) - ε <
        (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))
          (labelTailEvent (α := StageLabel k (J + 1)) N)) :
    (1 : ℝ≥0∞) - ε <
      ((((PlabelSucc.map
        (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
          ProbabilityMeasure (ℕ → StageLabel k J)) : Measure (ℕ → StageLabel k J))
        (labelTailEvent (α := StageLabel k J) N)) := by
  -- Proof comment: truncation only forgets coordinates, so the coarse tail event has at least as
  -- much mass as the finer one.
  refine lt_of_lt_of_le htail ?_
  simpa using
    le_stageLabelTruncatePath_map_labelTailEvent
      (k := k) J
      (μ := (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))))

/-- Helper for Theorem 17.56: project a stage-`J` label path to its coarse coordinate `m ≤ J`. -/
private def projectStageLabelPath
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J) :
    (ℕ → StageLabel k J) → (ℕ → Fin (k m)) :=
  fun ω n ↦ ω n ⟨m, Nat.lt_succ_of_le hm⟩

/-- Helper for Theorem 17.56: the coarse-coordinate projection on stage-label path space is
measurable. -/
private theorem measurable_projectStageLabelPath
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J) :
    Measurable (projectStageLabelPath (k := k) (J := J) (m := m) hm) := by
  -- Proof comment: every output coordinate is just evaluation of the stage-label path at time `n`
  -- followed by the fixed stage-coordinate projection `m`.
  refine measurable_pi_lambda _ ?_
  intro n
  exact
    (measurable_pi_apply (a := (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (J + 1)))).comp
      (measurable_pi_apply n)

/-- Helper for Theorem 17.56: the probability law obtained by projecting a stage-`J` label path
to its coarse coordinate `m ≤ J`. -/
private abbrev projectedStageLabelPathLaw
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J)) :
    ProbabilityMeasure (ℕ → Fin (k m)) :=
  Plabel.map
    (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable

/-- Helper for Theorem 17.56: if `m ≤ J`, then projecting a successor-stage label path to the
coarse coordinate `m` agrees with first truncating the path to stage `J` and then projecting. -/
private theorem projectStageLabelPath_succ_eq_comp_stageLabelTruncatePath
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J) :
    projectStageLabelPath (k := k) (J := J + 1) (m := m) (Nat.le_succ_of_le hm) =
      projectStageLabelPath (k := k) (J := J) (m := m) hm ∘
        stageLabelTruncatePath (k := k) J := by
  -- Proof comment: both sides read the same `m`th coordinate at each time slice; the right-hand
  -- side merely exposes the one-step stage truncation explicitly before the projection.
  funext ω n
  rfl

/-- Helper for Theorem 17.56: truncating a successor-stage law does not change any coarse
projected path law below the truncated stage. -/
private theorem projectedStageLabelPathLaw_map_stageLabelTruncatePath
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J)
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1))) :
    projectedStageLabelPathLaw
        (k := k) (J := J + 1) (m := m) (Nat.le_succ_of_le hm) PlabelSucc =
      projectedStageLabelPathLaw
        (k := k) (J := J) (m := m) hm
          (PlabelSucc.map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  -- Proof comment: after normalizing both probability measures to `Measure.map`, the claim is
  -- exactly the composition identity from the previous lemma followed by `Measure.map_map`.
  calc
    ((projectedStageLabelPathLaw
        (k := k) (J := J + 1) (m := m) (Nat.le_succ_of_le hm) PlabelSucc :
          ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m))) =
      Measure.map
        (projectStageLabelPath (k := k) (J := J + 1) (m := m) (Nat.le_succ_of_le hm))
        (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
          rfl
    _ =
      Measure.map
        ((projectStageLabelPath (k := k) (J := J) (m := m) hm) ∘
          stageLabelTruncatePath (k := k) J)
        (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
          rw [projectStageLabelPath_succ_eq_comp_stageLabelTruncatePath (k := k) hm]
    _ =
      Measure.map
        (projectStageLabelPath (k := k) (J := J) (m := m) hm)
        (Measure.map
          (stageLabelTruncatePath (k := k) J)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) := by
          symm
          exact Measure.map_map
            (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm)
            (measurable_stageLabelTruncatePath (k := k) J)
    _ =
      ((projectedStageLabelPathLaw
          (k := k) (J := J) (m := m) hm
          (PlabelSucc.map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m))) := by
            rfl

/-- Helper for Theorem 17.56: if a full stage-label path is eventually constant from index `N`
onward, then every fixed coarse coordinate path is eventually constant from the same index. -/
private theorem projectStageLabelPath_mem_labelTailEvent
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J) {N : ℕ}
    {ω : ℕ → StageLabel k J}
    (hω : ω ∈ labelTailEvent (α := StageLabel k J) N) :
    projectStageLabelPath (k := k) (J := J) (m := m) hm ω ∈
      labelTailEvent (α := Fin (k m)) N := by
  intro n hn
  -- Proof comment: the projected coarse path reads the same fixed stage coordinate at every time,
  -- so eventual equality of the full labels immediately descends to that coordinate.
  simpa [projectStageLabelPath] using
    congrArg (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩) (hω n hn)

/-- Helper for Theorem 17.56: a deterministic full stage-label tail cutoff also gives the same
coarse projected tail cutoff at every coordinate `m ≤ J`. -/
private theorem projectStageLabelPath_probabilityMap_tailLowerBound
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J) {ε : ℝ≥0} {N : ℕ}
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J))
          (labelTailEvent (α := StageLabel k J) N)) :
    (1 : ℝ≥0∞) - ε <
      (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
        Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := by
  have hsubset :
      labelTailEvent (α := StageLabel k J) N ⊆
        projectStageLabelPath (k := k) (J := J) (m := m) hm ⁻¹'
          labelTailEvent (α := Fin (k m)) N := by
    intro ω hω
    simpa [Set.mem_preimage] using
      projectStageLabelPath_mem_labelTailEvent (k := k) hm (N := N) hω
  -- Proof comment: projecting to one coarse coordinate only forgets information, so the coarse
  -- fixed-threshold tail event contains the full stage-label tail event.
  refine lt_of_lt_of_le htail ?_
  calc
    (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) ≤
        (Plabel : Measure (ℕ → StageLabel k J))
          (projectStageLabelPath (k := k) (J := J) (m := m) hm ⁻¹'
            labelTailEvent (α := Fin (k m)) N) := by
          exact measure_mono hsubset
    _ =
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
          Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := by
          exact
            (Measure.map_apply
              (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm)
              (measurableSet_labelTailEvent (α := Fin (k m)) N)).symm

/-- Helper for Theorem 17.56: truncating one successor-stage label path law produces the previous
stage law with the same exact marginals and the same deterministic label-tail cutoff. -/
private theorem existsPreviousStageLabelPathLawWithTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval)))
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))
          (labelTailEvent (α := StageLabel k (J + 1)) N)) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J))
          (labelTailEvent (α := StageLabel k J) N) := by
  let Plabel : ProbabilityMeasure (ℕ → StageLabel k J) :=
    PlabelSucc.map (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
  have hmarginals :=
    stageLabelTruncatePath_probabilityMap_marginals
      (k := k) (q := q) hq J ν νn PlabelSucc hhead hcoord
  have htail' :=
    stageLabelTruncatePath_probabilityMap_tailLowerBound
      (k := k) J (PlabelSucc := PlabelSucc) htail
  -- Proof comment: the one-step truncation API already packages both the marginal transport and
  -- the monotonicity of the eventual-constancy event.
  exact ⟨Plabel, hmarginals.1, hmarginals.2, htail'⟩

/-- Helper for Theorem 17.56: truncating a top-stage label path law down to any earlier stage
preserves its exact marginals and the same deterministic label-tail cutoff. -/
private theorem existsStageLabelPrefixLawWithTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    {J M : ℕ} (hJM : J ≤ M)
    (PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M))
    (hheadTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)))
    (hcoordTop :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval)))
    {ε : ℝ≥0} {N : ℕ}
    (htailTop :
      (1 : ℝ≥0∞) - ε <
        (PlabelTop : Measure (ℕ → StageLabel k M))
          (labelTailEvent (α := StageLabel k M) N)) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J))
          (labelTailEvent (α := StageLabel k J) N) := by
  induction hJM generalizing ε N with
  | refl =>
      -- Proof comment: no truncation is needed at the top stage, so the original law already
      -- has the required specification.
      exact ⟨PlabelTop, hheadTop, hcoordTop, htailTop⟩
  | @step M hJM ih =>
      rcases existsPreviousStageLabelPathLawWithTailCutoff
          ν νn (hq := hq) M PlabelTop hheadTop hcoordTop htailTop with
        ⟨PlabelMid, hheadMid, hcoordMid, htailMid⟩
      -- Proof comment: peel off one final stage coordinate, then iterate the same argument down
      -- the remaining truncation chain.
      exact ih PlabelMid hheadMid hcoordMid htailMid

/-- Helper for Theorem 17.56: the equality needed to cast a coarse label into the `m`th
coordinate of a stage label. -/
private theorem stageLabelSection_castEq
    {k : ℕ → ℕ} {J m : ℕ} (i : Fin (J + 1)) (h : m = i.1) :
    k m = k i.1 :=
  congrArg k h

/-- Helper for Theorem 17.56: fill a stage label by prescribing coordinate `m` and setting every
other coordinate to `0`. This is the canonical right inverse of the `m`th stage projection. -/
private def stageLabelSection
    {k : ℕ → ℕ} {J m : ℕ}
    (hk : ∀ i : Fin (J + 1), 0 < k i.1) :
    Fin (k m) → StageLabel k J :=
  fun a i ↦
    if h : m = i.1 then
      Fin.cast (stageLabelSection_castEq (k := k) i h) a
    else
      ⟨0, hk i⟩

/-- Helper for Theorem 17.56: the canonical stage section really is a right inverse to the
`m`th coordinate projection. -/
@[simp] private theorem stageLabelSection_apply_coord
    {k : ℕ → ℕ} {J m : ℕ}
    (hk : ∀ i : Fin (J + 1), 0 < k i.1) (hm : m ≤ J) (a : Fin (k m)) :
    stageLabelSection (k := k) (J := J) (m := m) hk a ⟨m, Nat.lt_succ_of_le hm⟩ = a := by
  -- Proof comment: at the distinguished coordinate, the section uses the identity cast and
  -- therefore returns the prescribed coarse label verbatim.
  simp [stageLabelSection, stageLabelSection_castEq]

/-- Helper for Theorem 17.56: the canonical stage section is measurable because its codomain is a
finite product of finite discrete spaces. -/
private theorem measurable_stageLabelSection
    {k : ℕ → ℕ} {J m : ℕ}
    (hk : ∀ i : Fin (J + 1), 0 < k i.1) :
    Measurable (stageLabelSection (k := k) (J := J) (m := m) hk) := by
  -- Proof comment: any map into the finite stage alphabet is measurable by the standard
  -- `measurable_of_finite` bridge.
  exact measurable_of_finite _

/-- Helper for Theorem 17.56: pushing a coarse label law forward through the canonical stage
section and then projecting back to coordinate `m` recovers the original coarse law. -/
private theorem stageLabelSection_project_map_eq
    {k : ℕ → ℕ} {J m : ℕ}
    (hk : ∀ i : Fin (J + 1), 0 < k i.1) (hm : m ≤ J)
    (μ : Measure (Fin (k m))) :
    Measure.map (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩)
        (Measure.map (stageLabelSection (k := k) (J := J) (m := m) hk) μ) =
      μ := by
  -- Proof comment: once the stage section has been identified as a right inverse, the pushforward
  -- identity is just functoriality of `Measure.map`.
  have hcomp :
      (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩) ∘
          stageLabelSection (k := k) (J := J) (m := m) hk = id := by
    funext a
    simpa [Function.comp] using stageLabelSection_apply_coord (k := k) (J := J) (m := m) hk hm a
  rw [Measure.map_map (measurable_pi_apply ⟨m, Nat.lt_succ_of_le hm⟩)
      (measurable_stageLabelSection (k := k) (J := J) (m := m) hk)]
  simpa [hcomp] using (Measure.map_id (μ := μ))

/-- Helper for Theorem 17.56: pushing a Hilbert-cube law forward by the bundled stage quantizer
and then reading coordinate `m ≤ J` gives the same coarse pushforward as applying `q m`
directly. -/
private theorem stageLabelPushforward_project_eq_coarsePushforward
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) {J m : ℕ} (hm : m ≤ J)
    (μ : Measure (ℕ → unitInterval)) :
    Measure.map (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩)
        (Measure.map (stageLabelMap (k := k) q J) μ) =
      Measure.map (q m) μ := by
  -- Proof comment: the stage-label coordinate projection is measurable, so the claim is just
  -- functoriality of `Measure.map` plus the definitional coordinate formula for `stageLabelMap`.
  have hcomp :
      (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩) ∘
          stageLabelMap (k := k) q J = q m := by
    funext x
    exact congrFun (stageLabelMap_apply_coord (k := k) q hm) x
  rw [Measure.map_map (measurable_pi_apply ⟨m, Nat.lt_succ_of_le hm⟩)
      (measurable_stageLabelMap (k := k) (q := q) hq J)]
  simpa [hcomp]

/-- Helper for Theorem 17.56: the same stage-to-coarse projection identity holds directly on
probability measures. -/
private theorem stageLabelProbabilityMap_project_eq_coarsePushforward
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) {J m : ℕ} (hm : m ≤ J)
    (μ : ProbabilityMeasure (ℕ → unitInterval)) :
    (μ.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)).map
        (f := fun a : StageLabel k J ↦ a (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (J + 1)))
        ((measurable_pi_apply (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (J + 1))).aemeasurable) =
      μ.map (hq m).aemeasurable := by
  -- Proof comment: after coercing both sides to measures, the probability-level statement is the
  -- same stage/coarse pushforward identity proved just above.
  apply ProbabilityMeasure.toMeasure_injective
  simpa using
    stageLabelPushforward_project_eq_coarsePushforward
      (k := k) (q := q) hq hm (μ := (μ : Measure (ℕ → unitInterval)))

/-- Helper for Theorem 17.56: literal successor-stage truncation compatibility forces all later
coarse projected laws to agree with the stage-`m` projected law. -/
private theorem projectedStageLabelPathLaw_eq_of_compatibleFamily
    {k : ℕ → ℕ}
    (PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hcompat :
      ∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
    ∀ {m J : ℕ} (hm : m ≤ J),
      (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm (PlabelStage J) :
        Measure (ℕ → Fin (k m))) =
        (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl (PlabelStage m) :
          Measure (ℕ → Fin (k m))) := by
  intro m J hm
  induction hm with
  | refl =>
      rfl
  | @step J hm ih =>
      calc
        (projectedStageLabelPathLaw
            (k := k) (J := J + 1) (m := m) (Nat.le_succ_of_le hm) (PlabelStage (J + 1)) :
            Measure (ℕ → Fin (k m))) =
          (projectedStageLabelPathLaw
            (k := k) (J := J) (m := m) hm
            ((PlabelStage (J + 1)).map
              (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
              Measure (ℕ → Fin (k m))) := by
                simpa using
                  congrArg
                    (fun ρ : ProbabilityMeasure (ℕ → Fin (k m)) ↦
                      (ρ : Measure (ℕ → Fin (k m))))
                    (projectedStageLabelPathLaw_map_stageLabelTruncatePath
                      (k := k) (J := J) (m := m) hm (PlabelStage (J + 1)))
        _ =
          (projectedStageLabelPathLaw
            (k := k) (J := J) (m := m) hm (PlabelStage J) :
              Measure (ℕ → Fin (k m))) := by
                rw [hcompat J]
        _ =
          (projectedStageLabelPathLaw
            (k := k) (J := m) (m := m) le_rfl (PlabelStage m) :
              Measure (ℕ → Fin (k m))) := ih

/-- Helper for Theorem 17.56: if a stage-`J` label path is eventually constant, then any coarse
coordinate path `m ≤ J` is eventually constant as well. -/
private theorem ae_eventuallyEq_projectStageLabelPath_of_ae_eventuallyEq
    {k : ℕ → ℕ} {J m : ℕ} (hm : m ≤ J)
    {Plabel : ProbabilityMeasure (ℕ → StageLabel k J)}
    (hevent :
      ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    ∀ᵐ ω ∂(projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
      Measure (ℕ → Fin (k m))),
      (∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let projectedEvent : Set (ℕ → Fin (k m)) :=
    {ω | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0}
  have hprojectedEventMeas : MeasurableSet projectedEvent := by
    have hrewrite :
        projectedEvent = ⋃ N : ℕ, labelTailEvent (α := Fin (k m)) N := by
      ext ω
      simp [projectedEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦ measurableSet_labelTailEvent (α := Fin (k m)) N
  -- Proof comment: eventual equality of full stage labels survives after reading only the fixed
  -- coarse coordinate `m` at each time.
  refine (MeasureTheory.ae_map_iff
    (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable
    hprojectedEventMeas).2 ?_
  filter_upwards [hevent] with ω hω
  simpa [projectedEvent, projectStageLabelPath] using
    hω.mono fun n hn ↦
      congrArg (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩) hn

/-- Helper for Theorem 17.56: once the coarse projected laws of a stage-label family stabilize to
the stage-`m` coarse law, one deterministic coarse tail cutoff works uniformly for all later
stages. -/
private theorem uniformLabelTailCutoff_ofCompatibleStageLabelFamily
    {k : ℕ → ℕ} (m : ℕ)
    (PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hcompat :
      ∀ J : ℕ, ∀ hmJ : m ≤ J,
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
          Measure (ℕ → Fin (k m))) =
          (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl (PlabelStage m) :
            Measure (ℕ → Fin (k m))))
    (hevent :
      ∀ᵐ ω ∂(PlabelStage m : Measure (ℕ → StageLabel k m)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ J : ℕ, ∀ hmJ : m ≤ J,
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := by
  intro ε hε
  let PmCoarse : ProbabilityMeasure (ℕ → Fin (k m)) :=
    projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl (PlabelStage m)
  have hPmEvent :
      ∀ᵐ ω ∂(PmCoarse : Measure (ℕ → Fin (k m))),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
    -- Proof comment: project the almost-sure eventual equality event from the stage-`m` path
    -- law down to its coarse `m`th coordinate path law.
    simpa [PmCoarse] using
      ae_eventuallyEq_projectStageLabelPath_of_ae_eventuallyEq
        (k := k) (J := m) (m := m) le_rfl (Plabel := PlabelStage m) hevent
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := Fin (k m)) (P := PmCoarse) hPmEvent ε hε
  refine ⟨N, ?_⟩
  intro J hmJ
  -- Proof comment: every later coarse projection law agrees exactly with the stage-`m` coarse
  -- law, so the deterministic cutoff found at stage `m` transfers verbatim to all later stages.
  rw [hcompat J hmJ]
  simpa [PmCoarse] using hN

/-- Helper for Theorem 17.56: the uniform coarse cutoff from a compatible stage-label family can
be repackaged as the eventual-atTop estimate needed in the final stage-family assembly. -/
private theorem eventually_projectedLabelTail_highProb
    {k : ℕ → ℕ} (m : ℕ)
    (PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hcompat :
      ∀ J : ℕ, ∀ hmJ : m ≤ J,
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
          Measure (ℕ → Fin (k m))) =
          (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl (PlabelStage m) :
            Measure (ℕ → Fin (k m))))
    (hevent :
      ∀ᵐ ω ∂(PlabelStage m : Measure (ℕ → StageLabel k m)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
      ∀ hmJ : m ≤ J,
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := by
  obtain ⟨N, hN⟩ :=
    uniformLabelTailCutoff_ofCompatibleStageLabelFamily
      (k := k) (m := m) PlabelStage hcompat hevent ε hε
  -- Proof comment: the stronger uniform-in-`J` cutoff theorem immediately implies the weaker
  -- eventual-atTop form needed later by the ambient-lift assembly.
  refine ⟨N, Filter.Eventually.of_forall ?_⟩
  intro J hmJ
  exact hN J hmJ

/-- Helper for Theorem 17.56: once the stage-`m` member of a compatible stage-label family carries
the full dyadic cutoff table, the eventual-atTop coarse projected cutoff follows without any
further compactness work. -/
private theorem eventually_projectedLabelTail_highProb_ofCompatibleStageLabelCutoffs
    {k : ℕ → ℕ} (m : ℕ)
    (PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hcompat :
      ∀ J : ℕ, ∀ hmJ : m ≤ J,
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
          Measure (ℕ → Fin (k m))) =
          (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl (PlabelStage m) :
            Measure (ℕ → Fin (k m))))
    (hcutoff :
      ∀ r : ℕ, ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (PlabelStage m : Measure (ℕ → StageLabel k m))
            (labelTailEvent (α := StageLabel k m) N))
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
      ∀ hmJ : m ≤ J,
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ (PlabelStage J) :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := by
  have hevent :
      ∀ᵐ ω ∂(PlabelStage m : Measure (ℕ → StageLabel k m)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
    -- Proof comment: the dyadic cutoff table is exactly the hypothesis needed by the generic
    -- stage-label eventual-equality criterion.
    exact aeEventuallyEq_ofDyadicLabelTailCutoffs hcutoff
  -- Proof comment: after upgrading the cutoff table to almost-sure eventual equality, the
  -- existing compatible-family cutoff transfer theorem applies verbatim.
  exact eventually_projectedLabelTail_highProb
    (k := k) m PlabelStage hcompat hevent hε

/-- Helper for Theorem 17.56: projecting a stage-label path law to one coarse coordinate preserves
the expected head and time-coordinate marginals. -/
private theorem projectStageLabelPath_probabilityMap_marginals
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) {J m : ℕ} (hm : m ≤ J)
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) :
    Measure.map (fun ω : ℕ → Fin (k m) ↦ ω 0)
        ((((Plabel.map
          (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable) :
            ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m)))) =
      Measure.map (q m) (ν : Measure (ℕ → unitInterval)) ∧
    (∀ n : ℕ,
      Measure.map (fun ω : ℕ → Fin (k m) ↦ ω (n + 1))
          ((((Plabel.map
            (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable) :
              ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m)))) =
        Measure.map (q m) (νn n : Measure (ℕ → unitInterval))) := by
  constructor
  · let idx : Fin (J + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    have hheadComp :
        (fun ω : ℕ → Fin (k m) ↦ ω 0) ∘
            projectStageLabelPath (k := k) (J := J) (m := m) hm =
          (fun a : StageLabel k J ↦ a idx) ∘
            (fun ω : ℕ → StageLabel k J ↦ ω 0) := by
      funext ω
      rfl
    calc
      Measure.map (fun ω : ℕ → Fin (k m) ↦ ω 0)
          ((((Plabel.map
            (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable) :
              ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m)))) =
        Measure.map ((fun ω : ℕ → Fin (k m) ↦ ω 0) ∘
            projectStageLabelPath (k := k) (J := J) (m := m) hm)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            change Measure.map (fun ω : ℕ → Fin (k m) ↦ ω 0)
              (Measure.map (projectStageLabelPath (k := k) (J := J) (m := m) hm)
                (Plabel : Measure (ℕ → StageLabel k J))) = _
            rw [Measure.map_map (measurable_pi_apply 0)
              (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm)]
      _ = Measure.map (fun a : StageLabel k J ↦ a idx)
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [hheadComp]
              symm
              exact Measure.map_map
                (measurable_pi_apply idx) (measurable_pi_apply 0)
      _ = Measure.map (fun a : StageLabel k J ↦ a idx)
            (Measure.map (stageLabelMap (k := k) q J)
              (ν : Measure (ℕ → unitInterval))) := by
              rw [hhead]
      _ = Measure.map (q m) (ν : Measure (ℕ → unitInterval)) := by
            exact stageLabelPushforward_project_eq_coarsePushforward
              (k := k) (q := q) hq hm (μ := (ν : Measure (ℕ → unitInterval)))
  · intro n
    let idx : Fin (J + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    have hcoordComp :
        (fun ω : ℕ → Fin (k m) ↦ ω (n + 1)) ∘
            projectStageLabelPath (k := k) (J := J) (m := m) hm =
          (fun a : StageLabel k J ↦ a idx) ∘
            (fun ω : ℕ → StageLabel k J ↦ ω (n + 1)) := by
      funext ω
      rfl
    calc
      Measure.map (fun ω : ℕ → Fin (k m) ↦ ω (n + 1))
          ((((Plabel.map
            (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable) :
              ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m)))) =
        Measure.map ((fun ω : ℕ → Fin (k m) ↦ ω (n + 1)) ∘
            projectStageLabelPath (k := k) (J := J) (m := m) hm)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            change Measure.map (fun ω : ℕ → Fin (k m) ↦ ω (n + 1))
              (Measure.map (projectStageLabelPath (k := k) (J := J) (m := m) hm)
                (Plabel : Measure (ℕ → StageLabel k J))) = _
            rw [Measure.map_map (measurable_pi_apply (n + 1))
              (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm)]
      _ = Measure.map (fun a : StageLabel k J ↦ a idx)
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [hcoordComp]
              symm
              exact Measure.map_map
                (measurable_pi_apply idx) (measurable_pi_apply (n + 1))
      _ = Measure.map (fun a : StageLabel k J ↦ a idx)
            (Measure.map (stageLabelMap (k := k) q J)
              (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (q m) (νn n : Measure (ℕ → unitInterval)) := by
            exact stageLabelPushforward_project_eq_coarsePushforward
              (k := k) (q := q) hq hm (μ := (νn n : Measure (ℕ → unitInterval)))

/-- Helper for Theorem 17.56: weak convergence on the Hilbert cube pushes through the bundled
finite stage label map whenever each coordinate singleton fiber has `ν`-null frontier. -/
private theorem tendstoStageLabelPushforward_of_nullFrontierSingletons
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    Tendsto
      (fun n ↦
        (νn n).map
          ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable))
      atTop
      (𝓝
        (ν.map
          ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable))) := by
  let QJ : (ℕ → unitInterval) → StageLabel k J := stageLabelMap (k := k) q J
  have hQJ : Measurable QJ := measurable_stageLabelMap (k := k) (q := q) hq J
  have hQJFrontier :
      ∀ a : StageLabel k J,
        (ν : Measure (ℕ → unitInterval)) (frontier (QJ ⁻¹' {a})) = 0 :=
    stageLabelMap_nullFrontier_of_nullFrontierSingletons
      (ν := ν) (k := k) (q := q) hfrontier J
  -- Proof comment: the bundled stage alphabet is finite discrete, so the generic pushforward
  -- Portmanteau lemma applies once the measurability and null-frontier fiber facts are packaged.
  simpa [QJ] using
    (tendstoFiniteDiscretePushforward_of_nullFrontierSingletons
      (ν := ν) (νn := νn) hνn (q := QJ) hQJ hQJFrontier)

/-- Helper for Theorem 17.56: finite unions of sets with `ν`-null frontier still have
`ν`-null frontier. -/
private theorem nullFrontier_biUnion_finset
    (ν : Measure (ℕ → unitInterval)) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {A : ι → Set (ℕ → unitInterval)}
    (hfrontier : ∀ i : ι, ν (frontier (A i)) = 0) :
    ν (frontier (⋃ i ∈ s, A i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty union is empty, so its frontier is empty as well.
      simp
  | @insert i s his ih =>
      have hsubset' :
          frontier (A i ∪ ⋃ j ∈ s, A j) ⊆
            frontier (A i) ∩ closure (⋃ j ∈ s, A j)ᶜ ∪
              closure (A i)ᶜ ∩ frontier (⋃ j ∈ s, A j) :=
        frontier_union_subset _ _
      have hsubset :
          frontier (A i ∪ ⋃ j ∈ s, A j) ⊆ frontier (A i) ∪ frontier (⋃ j ∈ s, A j) := by
        intro x hx
        rcases hsubset' hx with hx' | hx'
        · exact Or.inl hx'.1
        · exact Or.inr hx'.2
      have hunion :
          ν (frontier (A i) ∪ frontier (⋃ j ∈ s, A j)) = 0 :=
        measure_union_null (hfrontier i) ih
      -- Proof comment: the new frontier sits inside the union of the old frontiers, so its mass
      -- stays zero by monotonicity.
      simpa [Finset.set_biUnion_insert, his] using measure_mono_null hsubset hunion

/-- Helper for Theorem 17.56: every dyadic scale on the Hilbert cube admits a finite measurable
quantizer whose singleton fibers have `ν`-null frontier and whose fibers have diameter at most
that dyadic scale. -/
private theorem existsDyadicHilbertCubeQuantizer
    (ν : ProbabilityMeasure (ℕ → unitInterval)) (m : ℕ) :
    ∃ k : ℕ, 0 < k ∧
      ∃ q : (ℕ → unitInterval) → Fin k,
        Measurable q ∧
        (∀ a : Fin k,
          (ν : Measure (ℕ → unitInterval)) (frontier (q ⁻¹' {a})) = 0) ∧
        (∀ x y : ℕ → unitInterval, q x = q y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m) := by
  classical
  letI : MetricSpace (ℕ → unitInterval) := PiCountable.metricSpace
  let ε : ℝ := ((1 / 2 : ℝ) ^ m) / 4
  have hε : 0 < ε := by
    positivity
  have hcompact : IsCompact (Set.univ : Set (ℕ → unitInterval)) := isCompact_univ
  obtain ⟨t, -, htfin, hcover⟩ := hcompact.finite_cover_balls hε
  let s : Finset (ℕ → unitInterval) := htfin.toFinset
  have hs_nonempty : s.Nonempty := by
    let x : ℕ → unitInterval := fun _ ↦ 0
    have hxcover : x ∈ ⋃ y ∈ t, Metric.ball y ε := hcover (by simp)
    rcases Set.mem_iUnion₂.mp hxcover with ⟨y, hyt, -⟩
    refine ⟨y, ?_⟩
    simpa [s] using (Set.Finite.mem_toFinset htfin).2 hyt
  let k : ℕ := s.card
  have hk : 0 < k := Finset.card_pos.2 hs_nonempty
  let c : Fin k → (ℕ → unitInterval) := fun i ↦ (s.equivFin.symm i : (ℕ → unitInterval))
  let B : Fin k → Set (ℕ → unitInterval) := fun i ↦ Metric.ball (c i) ε
  have hcoverBall : ∀ x : ℕ → unitInterval, ∃ i : Fin k, x ∈ B i := by
    intro x
    have hxcover : x ∈ ⋃ y ∈ t, Metric.ball y ε := hcover (by simp)
    rcases Set.mem_iUnion₂.mp hxcover with ⟨y, hyt, hxy⟩
    have hyS : y ∈ s := by
      simpa [s] using (Set.Finite.mem_toFinset htfin).2 hyt
    let i : Fin k := s.equivFin ⟨y, hyS⟩
    refine ⟨i, ?_⟩
    simpa [B, c, i]
  have hthick :
      ∀ i : Fin k,
        ∃ r ∈ Set.Ioo 0 ε,
          (ν : Measure (ℕ → unitInterval)) (frontier (Metric.thickening r (B i))) = 0 := by
    intro i
    exact MeasureTheory.exists_null_frontier_thickening
      (μ := (ν : Measure (ℕ → unitInterval))) (s := B i) hε
  choose r hr using hthick
  let U : Fin k → Set (ℕ → unitInterval) := fun i ↦ Metric.thickening (r i) (B i)
  let prev : Fin k → Finset (Fin k) := fun i ↦ Finset.univ.filter fun j ↦ j < i
  let A : Fin k → Set (ℕ → unitInterval) := fun i ↦ U i \ ⋃ j ∈ prev i, U j
  have hrpos : ∀ i : Fin k, 0 < r i := fun i ↦ (hr i).1.1
  have hrlt : ∀ i : Fin k, r i < ε := fun i ↦ (hr i).1.2
  have hfrontierU :
      ∀ i : Fin k,
        (ν : Measure (ℕ → unitInterval)) (frontier (U i)) = 0 := fun i ↦ (hr i).2
  have hU_meas : ∀ i : Fin k, MeasurableSet (U i) := fun i ↦
    Metric.isOpen_thickening.measurableSet
  have hA_meas : ∀ i : Fin k, MeasurableSet (A i) := by
    intro i
    -- Proof comment: each disjointized cell is one thickened ball minus a finite union of earlier
    -- thickened balls.
    exact (hU_meas i).diff <|
      Finset.measurableSet_biUnion (prev i) fun j _ ↦ hU_meas j
  have hball_subset_U : ∀ i : Fin k, B i ⊆ U i := by
    intro i x hx
    -- Proof comment: every ball is contained in its positive-radius thickening by choosing the
    -- same witness point.
    exact Metric.mem_thickening_iff.mpr ⟨x, hx, by simpa using hrpos i⟩
  have hcoverU : ∀ x : ℕ → unitInterval, ∃ i : Fin k, x ∈ U i := by
    intro x
    rcases hcoverBall x with ⟨i, hxi⟩
    exact ⟨i, hball_subset_U i hxi⟩
  have hfrontierPrev :
      ∀ i : Fin k,
        (ν : Measure (ℕ → unitInterval)) (frontier (⋃ j ∈ prev i, U j)) = 0 := by
    intro i
    exact nullFrontier_biUnion_finset
      (ν := (ν : Measure (ℕ → unitInterval))) (s := prev i) (A := U) hfrontierU
  have hfrontierA :
      ∀ i : Fin k,
        (ν : Measure (ℕ → unitInterval)) (frontier (A i)) = 0 := by
    intro i
    let V : Set (ℕ → unitInterval) := ⋃ j ∈ prev i, U j
    have hsubset' :
        frontier (U i ∩ Vᶜ) ⊆
          frontier (U i) ∩ closure Vᶜ ∪ closure (U i) ∩ frontier Vᶜ :=
      frontier_inter_subset _ _
    have hsubset :
        frontier (U i ∩ Vᶜ) ⊆ frontier (U i) ∪ frontier V := by
      intro x hx
      rcases hsubset' hx with hx' | hx'
      · exact Or.inl hx'.1
      · exact Or.inr (by simpa [frontier_compl] using hx'.2)
    have hunion :
        (ν : Measure (ℕ → unitInterval)) (frontier (U i) ∪ frontier V) = 0 :=
      measure_union_null (hfrontierU i) (by simpa [V] using hfrontierPrev i)
    -- Proof comment: disjointizing by subtracting earlier cells only adds the frontier of the
    -- earlier union, whose `ν`-mass is already zero.
    simpa [A, Set.diff_eq, V] using measure_mono_null hsubset hunion
  have hA_disjoint : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hxj.2 <|
        Set.mem_iUnion₂.mpr ⟨i, by simpa [prev, hijlt], hxi.1⟩
    · exact hxi.2 <|
        Set.mem_iUnion₂.mpr ⟨j, by simpa [prev, hjilt], hxj.1⟩
  have hcoverA : ∀ x : ℕ → unitInterval, ∃ i : Fin k, x ∈ A i := by
    intro x
    let Sx : Finset (Fin k) := Finset.univ.filter fun i ↦ x ∈ U i
    have hSx_nonempty : Sx.Nonempty := by
      rcases hcoverU x with ⟨i, hxi⟩
      exact ⟨i, by simp [Sx, hxi]⟩
    let i : Fin k := Sx.min' hSx_nonempty
    refine ⟨i, ?_⟩
    have hxiU : x ∈ U i := by
      exact (Finset.mem_filter.mp (Finset.min'_mem Sx hSx_nonempty)).2
    refine ⟨hxiU, ?_⟩
    intro hxprev
    rcases Set.mem_iUnion₂.mp hxprev with ⟨j, hjprev, hxjU⟩
    have hjSx : j ∈ Sx := by
      simp [Sx, hxjU]
    have hle : i ≤ j := Finset.min'_le Sx j hjSx
    have hjlt : j < i := (Finset.mem_filter.mp hjprev).2
    exact not_lt_of_ge hle hjlt
  let ι : Type := {i : Fin k // (A i).Nonempty}
  let SA : ι → Set (ℕ → unitInterval) := fun i ↦ A i.1
  have hSA_disjoint : Pairwise (Function.onFun Disjoint SA) := by
    intro i j hij
    have hij' : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    simpa [SA] using hA_disjoint hij'
  have hSA_cover : ∀ x : ℕ → unitInterval, ∃ i : ι, x ∈ SA i := by
    intro x
    rcases hcoverA x with ⟨i, hxi⟩
    exact ⟨⟨i, ⟨x, hxi⟩⟩, hxi⟩
  let hs : IndexedPartition SA := IndexedPartition.mk' SA hSA_disjoint (fun i ↦ i.2) hSA_cover
  let q0 : (ℕ → unitInterval) → ι := hs.piecewise fun i _ ↦ i
  let q : (ℕ → unitInterval) → Fin k := fun x ↦ (q0 x).1
  have hq0_meas : Measurable q0 := by
    -- Proof comment: the partition index is measurable because it is the piecewise glueing of
    -- constant indices on the measurable cells.
    simpa [q0] using
      hs.measurable_piecewise (fun i ↦ hA_meas i.1) (fun i ↦ measurable_const)
  have hq_meas : Measurable q := by
    have hcoe : Measurable (fun i : ι ↦ (i : Fin k)) := measurable_of_finite _
    exact hcoe.comp hq0_meas
  have hq_mem : ∀ x : ℕ → unitInterval, x ∈ A (q x) := by
    intro x
    -- Proof comment: by construction, the partition index of `x` points to the unique cell
    -- containing `x`.
    simpa [SA, q, q0, IndexedPartition.piecewise_apply] using hs.mem_index x
  have hqfiber : ∀ a : Fin k, q ⁻¹' {a} = A a := by
    intro a
    ext x
    constructor
    · intro hx
      have hqa : q x = a := by simpa using hx
      simpa [hqa] using hq_mem x
    · intro hxa
      let ia : ι := ⟨a, ⟨x, hxa⟩⟩
      have hindex : hs.index x = ia := by
        exact (hs.mem_iff_index_eq).mp (by simpa [SA] using hxa)
      change (hs.index x).1 = a
      simpa [hindex, ia, q, q0, IndexedPartition.piecewise_apply]
  have hU_subset_ball :
      ∀ i : Fin k, U i ⊆ Metric.ball (c i) (r i + ε) := by
    intro i
    simpa [U, B] using Metric.thickening_ball (c i) (r i) ε
  have hdiam :
      ∀ x y : ℕ → unitInterval, q x = q y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
    intro x y hxy
    have hxA : x ∈ A (q x) := hq_mem x
    have hyA : y ∈ A (q x) := by simpa [hxy] using hq_mem y
    have hxball : x ∈ Metric.ball (c (q x)) (r (q x) + ε) :=
      hU_subset_ball (q x) hxA.1
    have hyball : y ∈ Metric.ball (c (q x)) (r (q x) + ε) :=
      hU_subset_ball (q x) hyA.1
    have hxdist : dist x (c (q x)) < r (q x) + ε := by
      simpa [Metric.mem_ball] using hxball
    have hydist : dist y (c (q x)) < r (q x) + ε := by
      simpa [Metric.mem_ball] using hyball
    have hfour : 4 * ε = (1 / 2 : ℝ) ^ m := by
      dsimp [ε]
      ring
    have hsum :
        dist x (c (q x)) + dist y (c (q x)) < (1 / 2 : ℝ) ^ m := by
      nlinarith [hxdist, hydist, hrlt (q x), hfour]
    have htri : dist x y ≤ dist x (c (q x)) + dist y (c (q x)) :=
      dist_triangle_right _ _ _
    exact le_of_lt (lt_of_le_of_lt htri hsum)
  -- Proof comment: the disjointized finite thickening partition gives the required measurable
  -- finite quantizer, and each cell lies inside one controlled thickened ball.
  refine ⟨k, hk, q, hq_meas, ?_, hdiam⟩
  intro a
  simpa [hqfiber a] using hfrontierA a

/-- Helper for Theorem 17.56: weak convergence on a finite discrete alphabet makes every
singleton mass uniformly close after one tail index. -/
private theorem eventuallyUniformFiniteDiscreteSingletonMassRealClose
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    {μn : ℕ → ProbabilityMeasure α} {μ : ProbabilityMeasure α}
    (hμn : Tendsto μn atTop (𝓝 μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : α,
      |(μn n : Measure α).real {a} - (μ : Measure α).real {a}| < ε := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  have hcoord :
      ∀ a : α,
        ∀ᶠ n : ℕ in atTop,
          |(μn n : Measure α).real {a} - (μ : Measure α).real {a}| < ε := by
    intro a
    have hmass :
        Tendsto (fun n : ℕ ↦ (μn n : Measure α).real {a}) atTop
          (𝓝 ((μ : Measure α).real {a})) :=
      ((continuousFiniteDiscreteSingletonMassReal (a := a)).tendsto μ).comp hμn
    -- Proof comment: continuity of each singleton-mass coordinate turns weak convergence into an
    -- eventual real-valued bound on that coordinate.
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 hmass) ε hε
  choose N hN using fun a : α => Filter.eventually_atTop.1 (hcoord a)
  let N0 : ℕ := Finset.univ.sup N
  refine ⟨N0, ?_⟩
  intro n hn a
  -- Proof comment: finitely many singleton coordinates are controlled simultaneously by taking
  -- the maximum of their individual tail indices.
  exact hN a n (le_trans (Finset.le_sup (f := N) (Finset.mem_univ a)) hn)

/-- Helper for Theorem 17.56: the previous uniform singleton-mass control also gives a pointwise
tail lower bound on every finite discrete coordinate mass. -/
private theorem eventuallyFiniteDiscreteSingletonMassReal_lowerBound
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    {μn : ℕ → ProbabilityMeasure α} {μ : ProbabilityMeasure α}
    (hμn : Tendsto μn atTop (𝓝 μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : α,
      (μ : Measure α).real {a} - ε ≤ (μn n : Measure α).real {a} := by
  obtain ⟨N, hN⟩ := eventuallyUniformFiniteDiscreteSingletonMassRealClose hμn hε
  refine ⟨N, ?_⟩
  intro n hn a
  have ha : |(μn n : Measure α).real {a} - (μ : Measure α).real {a}| < ε := hN n hn a
  -- Proof comment: the absolute-value estimate immediately yields the one-sided lower bound that
  -- will feed the later common-core mass construction.
  linarith [abs_lt.mp ha |>.1]

/-- Helper for Theorem 17.56: a finite discrete law on `Fin k` can be viewed as a constant-row
stochastic matrix whose row entries are the singleton masses of that law. -/
private def singletonMassMatrix {k : ℕ} (μ : ProbabilityMeasure (Fin k)) :
    Fin k → Fin k → ℝ≥0∞ :=
  fun _ j ↦ (μ : Measure (Fin k)) {j}

/-- Helper for Theorem 17.56: the singleton-mass matrix of a finite discrete law is stochastic. -/
private theorem singletonMassMatrix_isStochastic {k : ℕ} (μ : ProbabilityMeasure (Fin k)) :
    IsStochasticMatrix (singletonMassMatrix μ) := by
  intro i
  -- Proof comment: on a finite discrete space, summing the singleton masses recovers the total
  -- mass `1` of the probability measure.
  calc
    ∑' j : Fin k, singletonMassMatrix μ i j = ∑' j : Fin k, (μ : Measure (Fin k)) {j} := by
      simp [singletonMassMatrix]
    _ = (μ : Measure (Fin k)) Set.univ := by
      symm
      simpa using (μ : Measure (Fin k)).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
    _ = 1 := by simp

/-- Helper for Theorem 17.56: the unit-interval simulator from `Example_17_19` realizes an
arbitrary law on `Fin k` once the stochastic matrix is chosen to have constant singleton-mass
rows. -/
private theorem hasLaw_stochasticMatrixSimulationStateOfProbabilityMeasure
    {k : ℕ} (i : Fin k) (μ : ProbabilityMeasure (Fin k)) :
    HasLaw (stochasticMatrixSimulationState (singletonMassMatrix μ) i) μ
      (volume : Measure unitInterval) := by
  have hsim :
      HasLaw (stochasticMatrixSimulationState (singletonMassMatrix μ) i)
        (discreteMatrixKernel (singletonMassMatrix μ) i) (volume : Measure unitInterval) :=
    hasLaw_stochasticMatrixSimulationState (singletonMassMatrix μ)
      (singletonMassMatrix_isStochastic μ) i
  refine ⟨hsim.aemeasurable, ?_⟩
  calc
    Measure.map (stochasticMatrixSimulationState (singletonMassMatrix μ) i)
        (volume : Measure unitInterval) =
      discreteMatrixKernel (singletonMassMatrix μ) i := hsim.map_eq
    _ = (μ : Measure (Fin k)) := by
      refine Measure.ext_of_singleton ?_
      intro j
      rw [discreteMatrixKernel_apply_singleton_local]
      simp [singletonMassMatrix]

/-- Helper for Theorem 17.56: weak convergence of finite discrete laws implies convergence of all
simulation cutoffs in the common unit-interval representation. -/
private theorem tendsto_stochasticMatrixSimulationCumulative_singletonMassMatrix
    {k : ℕ} (i : Fin k) {μn : ℕ → ProbabilityMeasure (Fin k)}
    {μ : ProbabilityMeasure (Fin k)} (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∀ r : Fin (k + 1),
      Tendsto
        (fun n ↦
          stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i r)
        atTop
        (𝓝 (stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r)) := by
  intro r
  induction r using Fin.induction with
  | zero =>
      -- Proof comment: the initial cutoff is always the empty partial sum.
      simp [stochasticMatrixSimulationCumulative_zero]
  | succ r ih =>
      have hmass :
          Tendsto (fun n ↦ ((μn n : Measure (Fin k)) {r}).toReal) atTop
            (𝓝 (((μ : Measure (Fin k)) {r}).toReal)) :=
        ((continuousFiniteDiscreteSingletonMassReal (a := r)).tendsto μ).comp hμn
      have hsucc_n :
          (fun n ↦
            stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i r.succ) =
            fun n ↦
              stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i r.castSucc +
                ((μn n : Measure (Fin k)) {r}).toReal := by
        funext n
        simpa [stochasticMatrixSimulationCumulative, singletonMassMatrix] using
          (Fin.partialSum_succ (fun j : Fin k ↦ ((μn n : Measure (Fin k)) {j}).toReal) r)
      have hsucc :
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r.succ =
            stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r.castSucc +
              (((μ : Measure (Fin k)) {r}).toReal) := by
        simpa [stochasticMatrixSimulationCumulative, singletonMassMatrix] using
          (Fin.partialSum_succ (fun j : Fin k ↦ (((μ : Measure (Fin k)) {j}).toReal)) r)
      -- Proof comment: every later cutoff is the previous cutoff plus one singleton mass, so the
      -- convergence follows from the induction hypothesis and singleton-mass convergence.
      simpa [hsucc_n, hsucc] using ih.add hmass

/-- Helper for Theorem 17.56: weak convergence of finite discrete laws makes all simulation
cutoffs uniformly close after one deterministic tail index. -/
private theorem eventuallyUniform_stochasticMatrixSimulationCumulative_close
    {k : ℕ} (i : Fin k) {μn : ℕ → ProbabilityMeasure (Fin k)}
    {μ : ProbabilityMeasure (Fin k)} (hμn : Tendsto μn atTop (𝓝 μ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : Fin (k + 1),
      |stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i r -
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r| < ε := by
  have hcoord :
      ∀ r : Fin (k + 1),
        ∀ᶠ n : ℕ in atTop,
          |stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i r -
              stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r| < ε := by
    intro r
    have htend :=
      tendsto_stochasticMatrixSimulationCumulative_singletonMassMatrix
        (i := i) (μn := μn) (μ := μ) hμn r
    -- Proof comment: each cutoff is a real-valued coordinate of a finite family, so ordinary
    -- metric convergence gives one eventual absolute-error bound for that coordinate.
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 htend) ε hε
  choose N hN using fun r : Fin (k + 1) => Filter.eventually_atTop.1 (hcoord r)
  let N0 : ℕ := Finset.univ.sup N
  refine ⟨N0, ?_⟩
  intro n hn r
  -- Proof comment: finitely many cutoff coordinates are controlled simultaneously by taking the
  -- maximum of their individual tail indices.
  exact hN r n (le_trans (Finset.le_sup (f := N) (Finset.mem_univ r)) hn)

/-- Helper for Theorem 17.56: if every cutoff of the approximating simulator stays uniformly close
to the corresponding cutoff of the limit simulator, then any driver point with a fixed positive
gap from the limit cutoffs produces the same simulated state. -/
private theorem stochasticMatrixSimulationState_eq_of_uniformCutoffClose_of_boundaryGap
    {k : ℕ} (i : Fin k) {μ μ' : ProbabilityMeasure (Fin k)} {u : unitInterval} {ε : ℝ}
    (hε : 0 < ε)
    (hgap :
      ∀ r : Fin (k + 1),
        ε ≤ |(u : ℝ) -
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r|)
    (hclose :
      ∀ r : Fin (k + 1),
        |stochasticMatrixSimulationCumulative (singletonMassMatrix μ') i r -
            stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r| < ε) :
    stochasticMatrixSimulationState (singletonMassMatrix μ') i u =
      stochasticMatrixSimulationState (singletonMassMatrix μ) i u := by
  have hu_ne_one : (u : ℝ) ≠ 1 := by
    intro hu1
    have hlastGap := hgap (Fin.last k)
    have hlast :
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i (Fin.last k) = 1 := by
      simpa using
        stochasticMatrixSimulationCumulative_last_eq_one (singletonMassMatrix μ)
          (singletonMassMatrix_isStochastic μ) i
    rw [hu1, hlast, sub_self, abs_zero] at hlastGap
    linarith
  have hu_lt : (u : ℝ) < 1 := by
    exact lt_of_le_of_ne u.2.2 hu_ne_one
  let j : Fin k := stochasticMatrixSimulationState (singletonMassMatrix μ) i u
  have hu_interval :
      (u : ℝ) ∈ stochasticMatrixSimulationInterval (singletonMassMatrix μ) i j := by
    -- Proof comment: first normalize the limit simulator state into membership in its
    -- defining half-open interval.
    exact
      (stochasticMatrixSimulationState_eq_iff (singletonMassMatrix μ)
        (singletonMassMatrix_isStochastic μ) i j u hu_lt).1 rfl
  have hlower_le :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc ≤ (u : ℝ) :=
    (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix μ) i j).1 hu_interval |>.1
  have hupper_lt :
      (u : ℝ) < stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ :=
    (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix μ) i j).1 hu_interval |>.2
  have hgapLower :
      ε ≤ |(u : ℝ) -
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc| :=
    hgap j.castSucc
  have hgapUpper :
      ε ≤ |(u : ℝ) -
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ| :=
    hgap j.succ
  have hlower_margin :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc + ε ≤ (u : ℝ) := by
    -- Proof comment: the lower cutoff sits at least `ε` below `u`, because equality is excluded
    -- by the boundary-gap hypothesis.
    have hgapLower' :
        ε ≤ (u : ℝ) -
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc := by
      simpa [abs_of_nonneg (sub_nonneg.mpr hlower_le)] using hgapLower
    linarith
  have hupper_margin :
      (u : ℝ) ≤
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ - ε := by
    -- Proof comment: the upper cutoff sits at least `ε` above `u`, again by the boundary gap.
    have hgapUpper' :
        ε ≤
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ - (u : ℝ) := by
      simpa [abs_of_neg (sub_neg.mpr hupper_lt)] using hgapUpper
    linarith
  have hlower_lt :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ') i j.castSucc < (u : ℝ) := by
    have hcloseLower := hclose j.castSucc
    have hcloseLower' :
        |stochasticMatrixSimulationCumulative (singletonMassMatrix μ') i j.castSucc -
            stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc| < ε := by
      simpa [abs_sub_comm] using hcloseLower
    -- Proof comment: the new lower cutoff can move by less than `ε`, so it stays below `u`.
    linarith [hlower_margin, (abs_lt.mp hcloseLower').2]
  have hupper_lt' :
      (u : ℝ) <
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ') i j.succ := by
    have hcloseUpper := hclose j.succ
    have hcloseUpper' :
        |stochasticMatrixSimulationCumulative (singletonMassMatrix μ') i j.succ -
            stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ| < ε := by
      simpa [abs_sub_comm] using hcloseUpper
    -- Proof comment: the new upper cutoff also moves by less than `ε`, so it remains above `u`.
    linarith [hupper_margin, (abs_lt.mp hcloseUpper').1]
  have hu_interval' :
      (u : ℝ) ∈ stochasticMatrixSimulationInterval (singletonMassMatrix μ') i j := by
    exact
      (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix μ') i j).2
        ⟨le_of_lt hlower_lt, hupper_lt'⟩
  have hstate' :
      stochasticMatrixSimulationState (singletonMassMatrix μ') i u = j := by
    -- Proof comment: once the same interval still contains `u`, the approximating simulator
    -- returns the same label.
    exact
      (stochasticMatrixSimulationState_eq_iff (singletonMassMatrix μ')
        (singletonMassMatrix_isStochastic μ') i j u hu_lt).2 hu_interval'
  simpa [j] using hstate'

/-- Helper for Theorem 17.56: a fixed positive gap from every limit cutoff upgrades the pointwise
finite-discrete simulator stabilization to one deterministic tail index. -/
private theorem eventually_stochasticMatrixSimulationState_eq_limit_of_boundaryGap
    {k : ℕ} (i : Fin k) {μn : ℕ → ProbabilityMeasure (Fin k)}
    {μ : ProbabilityMeasure (Fin k)} (hμn : Tendsto μn atTop (𝓝 μ))
    {u : unitInterval} {ε : ℝ} (hε : 0 < ε)
    (hgap :
      ∀ r : Fin (k + 1),
        ε ≤ |(u : ℝ) -
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r|) :
    ∀ᶠ n : ℕ in atTop,
      stochasticMatrixSimulationState (singletonMassMatrix (μn n)) i u =
        stochasticMatrixSimulationState (singletonMassMatrix μ) i u := by
  obtain ⟨N, hN⟩ :=
    eventuallyUniform_stochasticMatrixSimulationCumulative_close
      (i := i) (μn := μn) (μ := μ) hμn hε
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  -- Proof comment: after the uniform cutoff error has dropped below the chosen boundary gap, the
  -- simulators agree by the deterministic interval-preservation lemma.
  exact stochasticMatrixSimulationState_eq_of_uniformCutoffClose_of_boundaryGap
    (i := i) (μ := μ) (μ' := μn n) (u := u) hε hgap (hN n hn)

/-- Helper for Theorem 17.56: the boundary cutoffs of the common unit-interval simulator for a
finite discrete law form a finite exceptional set. -/
private def simulationBoundarySet {k : ℕ} (i : Fin k) (μ : ProbabilityMeasure (Fin k)) :
    Set unitInterval :=
  Set.range fun r : Fin (k + 1) ↦
    ⟨stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r,
      (stochasticMatrixSimulationCumulative_memUnitInterval (singletonMassMatrix μ)
        (singletonMassMatrix_isStochastic μ) i r).1,
      (stochasticMatrixSimulationCumulative_memUnitInterval (singletonMassMatrix μ)
        (singletonMassMatrix_isStochastic μ) i r).2⟩

/-- Helper for Theorem 17.56: the simulator boundary set is finite because it is indexed by
`Fin (k + 1)`. -/
private theorem simulationBoundarySet_finite {k : ℕ} (i : Fin k)
    (μ : ProbabilityMeasure (Fin k)) :
    (simulationBoundarySet i μ).Finite := by
  -- Proof comment: the boundary set is the range of a function out of a finite type.
  exact Set.finite_range _

/-- Helper for Theorem 17.56: membership in the simulator boundary set is exactly equality with
one of the cumulative cutoffs. -/
private theorem mem_simulationBoundarySet_iff {k : ℕ} (i : Fin k)
    (μ : ProbabilityMeasure (Fin k)) {u : unitInterval} :
    u ∈ simulationBoundarySet i μ ↔
      ∃ r : Fin (k + 1),
        (u : ℝ) =
          stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i r := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    simpa using hr.symm

/-- Helper for Theorem 17.56: away from the finitely many boundary cutoffs of the limit law, the
common unit-interval simulator eventually produces the same finite label for every approximating
law. -/
private theorem eventually_stochasticMatrixSimulationState_eq_limit
    {k : ℕ} (i : Fin k) {μn : ℕ → ProbabilityMeasure (Fin k)}
    {μ : ProbabilityMeasure (Fin k)} (hμn : Tendsto μn atTop (𝓝 μ))
    {u : unitInterval} (hu : u ∉ simulationBoundarySet i μ) :
    ∀ᶠ n : ℕ in atTop,
      stochasticMatrixSimulationState (singletonMassMatrix (μn n)) i u =
        stochasticMatrixSimulationState (singletonMassMatrix μ) i u := by
  have hu_ne_one : u ≠ (1 : unitInterval) := by
    intro hu1
    apply hu
    rw [mem_simulationBoundarySet_iff]
    refine ⟨Fin.last k, ?_⟩
    rw [hu1]
    simpa using
      (stochasticMatrixSimulationCumulative_last_eq_one (singletonMassMatrix μ)
        (singletonMassMatrix_isStochastic μ) i).symm
  have hu_lt : (u : ℝ) < 1 := by
    exact lt_of_le_of_ne u.2.2 fun huval ↦ hu_ne_one (Subtype.ext huval)
  let j : Fin k := stochasticMatrixSimulationState (singletonMassMatrix μ) i u
  have hu_interval :
      (u : ℝ) ∈ stochasticMatrixSimulationInterval (singletonMassMatrix μ) i j := by
    exact
      (stochasticMatrixSimulationState_eq_iff (singletonMassMatrix μ)
        (singletonMassMatrix_isStochastic μ) i j u hu_lt).1 rfl
  have hlower_le :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc ≤ (u : ℝ) :=
    (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix μ) i j).1 hu_interval |>.1
  have hlower_ne :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc ≠ (u : ℝ) := by
    intro hEq
    apply hu
    rw [mem_simulationBoundarySet_iff]
    exact ⟨j.castSucc, hEq.symm⟩
  have hlower_lt :
      stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.castSucc < (u : ℝ) :=
    lt_of_le_of_ne hlower_le hlower_ne
  have hupper_lt :
      (u : ℝ) <
        stochasticMatrixSimulationCumulative (singletonMassMatrix μ) i j.succ :=
    (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix μ) i j).1 hu_interval |>.2
  have hlower_event :
      ∀ᶠ n : ℕ in atTop,
        stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i j.castSucc <
          (u : ℝ) := by
    exact
      (tendsto_stochasticMatrixSimulationCumulative_singletonMassMatrix
        (i := i) (μn := μn) (μ := μ) hμn j.castSucc) (Iio_mem_nhds hlower_lt)
  have hupper_event :
      ∀ᶠ n : ℕ in atTop,
        (u : ℝ) <
          stochasticMatrixSimulationCumulative (singletonMassMatrix (μn n)) i j.succ := by
    exact
      (tendsto_stochasticMatrixSimulationCumulative_singletonMassMatrix
        (i := i) (μn := μn) (μ := μ) hμn j.succ) (Ioi_mem_nhds hupper_lt)
  filter_upwards [hlower_event, hupper_event] with n hnLower hnUpper
  -- Proof comment: once the two adjacent cutoff inequalities stabilize, `u` stays in the same
  -- half-open interval for every later simulator and hence produces the same label `j`.
  have hu_interval_n :
      (u : ℝ) ∈ stochasticMatrixSimulationInterval (singletonMassMatrix (μn n)) i j := by
    exact
      (mem_stochasticMatrixSimulationInterval_iff (singletonMassMatrix (μn n)) i j).2
        ⟨le_of_lt hnLower, hnUpper⟩
  have hstate_n :
      stochasticMatrixSimulationState (singletonMassMatrix (μn n)) i u = j := by
    exact
      (stochasticMatrixSimulationState_eq_iff (singletonMassMatrix (μn n))
        (singletonMassMatrix_isStochastic (μn n)) i j u hu_lt).2 hu_interval_n
  simpa [j] using
    hstate_n

/-- Helper for Theorem 17.56: a convergent sequence of finite discrete laws on `Fin k` admits a
single common-driver realization whose coordinates are eventually constant almost surely. -/
private theorem existsFiniteDiscreteSkorohodPathLawFin
    {k : ℕ} (i : Fin k) {μn : ℕ → ProbabilityMeasure (Fin k)}
    {μ : ProbabilityMeasure (Fin k)} (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → Fin k) (Yn : ℕ → Ω → Fin k),
      HasLaw Y μ P ∧
        (∀ n : ℕ, HasLaw (Yn n) (μn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), ∀ᶠ n : ℕ in atTop, Yn n ω = Y ω) := by
  let Pm : Measure unitInterval := volume
  have hPm : IsProbabilityMeasure Pm := by
    -- Proof comment: the canonical volume measure on `unitInterval` already has total mass `1`.
    dsimp [Pm]
    infer_instance
  let P : ProbabilityMeasure unitInterval := ⟨Pm, hPm⟩
  let Y : unitInterval → Fin k := stochasticMatrixSimulationState (singletonMassMatrix μ) i
  let Yn : ℕ → unitInterval → Fin k :=
    fun n ↦ stochasticMatrixSimulationState (singletonMassMatrix (μn n)) i
  have hY : HasLaw Y μ P := by
    -- Proof comment: the constant-row simulator realizes the limit law directly on the common
    -- unit-interval driver space.
    simpa [P, Pm, Y] using
      (hasLaw_stochasticMatrixSimulationStateOfProbabilityMeasure (i := i) μ)
  have hYn : ∀ n : ℕ, HasLaw (Yn n) (μn n) P := by
    intro n
    -- Proof comment: the same simulator construction realizes every approximating law on the
    -- same driver space.
    simpa [P, Pm, Yn] using
      (hasLaw_stochasticMatrixSimulationStateOfProbabilityMeasure (i := i) (μ := μn n))
  have hboundaryZero : (P : Measure unitInterval) (simulationBoundarySet i μ) = 0 := by
    -- Proof comment: only finitely many cumulative cutoffs can be boundary points, and finite
    -- subsets of the atomless unit interval have zero volume.
    simpa [P, Pm] using
      (simulationBoundarySet_finite i μ).countable.measure_zero (μ := (volume : Measure unitInterval))
  have hgood :
      ∀ᵐ u ∂(P : Measure unitInterval), u ∉ simulationBoundarySet i μ := by
    -- Proof comment: outside the boundary set, the approximating simulators eventually agree with
    -- the limit simulator.
    simpa using (compl_mem_ae_iff.2 hboundaryZero)
  refine ⟨↥unitInterval, inferInstance, P, Y, Yn, hY, hYn, ?_⟩
  filter_upwards [hgood] with u hu
  -- Proof comment: for each non-boundary driver point, the earlier simulator stabilization lemma
  -- gives one deterministic tail index after which every label is constant.
  simpa [Y, Yn] using
    (eventually_stochasticMatrixSimulationState_eq_limit (i := i) (μn := μn) (μ := μ) hμn hu)

/-- Helper for Theorem 17.56: the finite-discrete Skorohod simulator is invariant under
re-encoding the alphabet by `Fintype.equivFin`, so later quantizer constructions can keep their
natural finite subtype target instead of introducing a bespoke `Fin k` wrapper at every step. -/
private theorem existsFiniteDiscreteSkorohodPathLaw
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    (a : α) {μn : ℕ → ProbabilityMeasure α}
    {μ : ProbabilityMeasure α} (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → α) (Yn : ℕ → Ω → α),
      HasLaw Y μ P ∧
        (∀ n : ℕ, HasLaw (Yn n) (μn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), ∀ᶠ n : ℕ in atTop, Yn n ω = Y ω) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  have heMeas : Measurable e := by
    -- Proof comment: on a discrete finite alphabet every encoding map is measurable.
    fun_prop
  have heSymmMeas : Measurable e.symm := by
    -- Proof comment: the decoding map is measurable for the same discrete-topology reason.
    fun_prop
  let μfin : ProbabilityMeasure (Fin (Fintype.card α)) := μ.map heMeas.aemeasurable
  let μnfin : ℕ → ProbabilityMeasure (Fin (Fintype.card α)) :=
    fun n ↦ (μn n).map heMeas.aemeasurable
  have hμfin : Tendsto μnfin atTop (𝓝 μfin) := by
    have heCont : Continuous e := by
      -- Proof comment: continuity is automatic on the discrete source space.
      fun_prop
    -- Proof comment: encode the finite laws by `equivFin`; weak convergence is preserved by the
    -- continuous pushforward.
    simpa [μnfin, μfin] using
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦ μn n) μ hμn heCont)
  obtain ⟨Ω, mΩ, P, Yfin, Ynfin, hYfin, hYnfin, heventFin⟩ :=
    existsFiniteDiscreteSkorohodPathLawFin (i := e a) hμfin
  have hdecode : HasLaw e.symm μ μfin := by
    refine ⟨heSymmMeas.aemeasurable, ?_⟩
    -- Proof comment: decoding after the `equivFin` encoding recovers the original limit law.
    change Measure.map e.symm (Measure.map e (μ : Measure α)) = (μ : Measure α)
    rw [Measure.map_map heSymmMeas heMeas]
    simpa [Function.comp, e]
  have hdecode_n : ∀ n : ℕ, HasLaw e.symm (μn n) (μnfin n) := by
    intro n
    refine ⟨heSymmMeas.aemeasurable, ?_⟩
    -- Proof comment: each approximating encoded law decodes back to its original alphabet law.
    change Measure.map e.symm (Measure.map e (μn n : Measure α)) = (μn n : Measure α)
    rw [Measure.map_map heSymmMeas heMeas]
    simpa [Function.comp, e]
  refine ⟨Ω, mΩ, P, e.symm ∘ Yfin, fun n ↦ e.symm ∘ Ynfin n, ?_, ?_, ?_⟩
  · -- Proof comment: compose the encoded realization with the decoder to recover the limit law on
    -- the original finite alphabet.
    simpa [Function.comp] using HasLaw.comp hdecode hYfin
  · intro n
    -- Proof comment: the same decoder transports every approximating coordinate law.
    simpa [Function.comp] using HasLaw.comp (hdecode_n n) (hYnfin n)
  · filter_upwards [heventFin] with ω hω
    -- Proof comment: eventual equality is preserved when both coordinates are decoded by the same
    -- injective equivalence.
    exact hω.mono fun n hn ↦ by simpa [Function.comp, hn]

/-- Helper for Theorem 17.56: the finite-discrete Skorohod realization can be repackaged as one
path law whose time-`0` coordinate has law `λ`, whose time-`n + 1` coordinate has law `λn n`,
and whose labels are eventually constant almost surely. -/
private theorem existsFiniteDiscreteLabelPathLaw
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    (a : α) {μn : ℕ → ProbabilityMeasure α}
    {μ : ProbabilityMeasure α} (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∃ Plabel : ProbabilityMeasure (ℕ → α),
      Measure.map (fun ω : ℕ → α ↦ ω 0) (Plabel : Measure (ℕ → α)) =
        (μ : Measure α) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → α ↦ ω (n + 1)) (Plabel : Measure (ℕ → α)) =
          (μn n : Measure α)) ∧
      (∀ᵐ ω ∂(Plabel : Measure (ℕ → α)), ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  obtain ⟨Ω, mΩ, P, Y, Yn, hY, hYn, hevent⟩ :=
    existsFiniteDiscreteSkorohodPathLaw (a := a) hμn
  let Z : Ω → ℕ → α := fun ω n ↦
    match n with
    | 0 => Y ω
    | m + 1 => Yn m ω
  let hZ : AEMeasurable Z (P : Measure Ω) := by
    -- Proof comment: every path coordinate is one of the already-controlled random variables
    -- `Y` or `Yn m`, so `aemeasurable_pi_lambda` packages them into one path-valued map.
    refine aemeasurable_pi_lambda Z ?_
    intro n
    cases n with
    | zero =>
        simpa [Z] using hY.aemeasurable
    | succ m =>
        simpa [Z] using (hYn m).aemeasurable
  let Plabel : ProbabilityMeasure (ℕ → α) := P.map hZ
  refine ⟨Plabel, ?_, ?_, ?_⟩
  · -- Proof comment: time `0` of the path is exactly the limit coordinate `Y`.
    calc
      Measure.map (fun ω : ℕ → α ↦ ω 0) (Plabel : Measure (ℕ → α)) =
          Measure.map ((fun ω : ℕ → α ↦ ω 0) ∘ Z) (P : Measure Ω) := by
            simpa [Plabel] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (P : Measure Ω))
                (g := fun ω : ℕ → α ↦ ω 0) (f := Z)
                (measurable_pi_apply 0).aemeasurable hZ)
      _ = (μ : Measure α) := by
            simpa [Function.comp, Z] using hY.map_eq
  · intro n
    -- Proof comment: time `n + 1` of the packaged path is exactly the approximating
    -- coordinate `Yn n`.
    calc
      Measure.map (fun ω : ℕ → α ↦ ω (n + 1)) (Plabel : Measure (ℕ → α)) =
          Measure.map ((fun ω : ℕ → α ↦ ω (n + 1)) ∘ Z) (P : Measure Ω) := by
            simpa [Plabel] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (P : Measure Ω))
                (g := fun ω : ℕ → α ↦ ω (n + 1)) (f := Z)
                (measurable_pi_apply (n + 1)).aemeasurable hZ)
      _ = (μn n : Measure α) := by
            simpa [Function.comp, Z] using (hYn n).map_eq
  · let heventMeas :
        MeasurableSet {ω : ℕ → α | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0} := by
      have hrewrite :
          {ω : ℕ → α | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0} =
            ⋃ N : ℕ, labelTailEvent (α := α) N := by
        ext ω
        simp [labelTailEvent, Filter.eventually_atTop]
      rw [hrewrite]
      exact MeasurableSet.iUnion fun N ↦ measurableSet_labelTailEvent (α := α) N
    -- Proof comment: transport the almost-sure tail event through the path map `Z`.
    exact (MeasureTheory.ae_map_iff hZ heventMeas).2 <| by
      -- Proof comment: eventual equality of `Yn n` with `Y` becomes eventual equality of the
      -- packaged path with its time-`0` coordinate.
      simpa [Z] using hevent

/-- Helper for Theorem 17.56: for one fixed dyadic scale, the quantizer pushforwards admit a
single coarse label path law with a deterministic high-probability tail cutoff. -/
private theorem existsCoarseLabelPathLawWithTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    (m : ℕ) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧
      ∃ q : (ℕ → unitInterval) → Fin k,
        Measurable q ∧
        (∀ a : Fin k,
          (ν : Measure (ℕ → unitInterval)) (frontier (q ⁻¹' {a})) = 0) ∧
        (∀ x y : ℕ → unitInterval, q x = q y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m) ∧
        ∃ Plabel : ProbabilityMeasure (ℕ → Fin k),
          Measure.map (fun ω : ℕ → Fin k ↦ ω 0) (Plabel : Measure (ℕ → Fin k)) =
            Measure.map q (ν : Measure (ℕ → unitInterval)) ∧
          (∀ n : ℕ,
            Measure.map (fun ω : ℕ → Fin k ↦ ω (n + 1)) (Plabel : Measure (ℕ → Fin k)) =
              Measure.map q (νn n : Measure (ℕ → unitInterval))) ∧
          ∃ N : ℕ,
            (1 : ℝ≥0∞) - ε < (Plabel : Measure (ℕ → Fin k)) (labelTailEvent N) := by
  obtain ⟨k, hk, q, hq, hfrontier, hdiam⟩ := existsDyadicHilbertCubeQuantizer ν m
  let lambda : ProbabilityMeasure (Fin k) := ν.map hq.aemeasurable
  let lambdaSeq : ℕ → ProbabilityMeasure (Fin k) := fun n ↦ (νn n).map hq.aemeasurable
  have hlambdaSeq : Tendsto lambdaSeq atTop (𝓝 lambda) := by
    -- Proof comment: the fixed-scale quantizer has measurable singleton fibers with `ν`-null
    -- frontier, so weak convergence pushes forward to the finite label alphabet.
    simpa [lambdaSeq, lambda] using
      (tendstoFiniteDiscretePushforward_of_nullFrontierSingletons
        (ν := ν) (νn := νn) hνn (q := q) hq hfrontier)
  obtain ⟨Plabel, hhead, hcoord, hevent⟩ :=
    existsFiniteDiscreteLabelPathLaw (a := ⟨0, hk⟩) hlambdaSeq
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (P := Plabel) hevent ε hε
  -- Proof comment: the fixed-scale discrete Skorohod path law already supplies the one
  -- deterministic coarse cutoff needed later for the stage-compatible lift.
  refine ⟨k, hk, q, hq, hfrontier, hdiam, Plabel, ?_, ?_, N, hN⟩
  · simpa [lambda] using hhead
  · intro n
    simpa [lambdaSeq] using hcoord n

/-- Helper for Theorem 17.56: choose one dyadic Hilbert-cube quantizer at every scale once and
for all. -/
private theorem existsDyadicHilbertCubeQuantizerTower
    (ν : ProbabilityMeasure (ℕ → unitInterval)) :
    ∃ k : ℕ → ℕ, (∀ m : ℕ, 0 < k m) ∧
      ∃ q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m),
        (∀ m : ℕ, Measurable (q m)) ∧
        (∀ m : ℕ, ∀ a : Fin (k m),
          (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) ∧
        (∀ m : ℕ, ∀ x y : ℕ → unitInterval, q m x = q m y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m) := by
  classical
  choose k hk q hq hfrontier hdiam using
    fun m : ℕ ↦ existsDyadicHilbertCubeQuantizer ν m
  -- Proof comment: choice packages the already proved one-scale quantizers into one tower that
  -- the later stage-label construction can reuse uniformly across all stages.
  exact ⟨k, hk, q, hq, hfrontier, hdiam⟩

/-- Helper for Theorem 17.56: for one fixed bundled stage alphabet, weak convergence of the
stage-label pushforwards yields a discrete path law with exact time marginals and one deterministic
tail cutoff. -/
private theorem existsStageLabelPathLawWithTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      ∃ N : ℕ,
        (1 : ℝ≥0∞) - ε <
          (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) := by
  letI : Fintype (StageLabel k J) := Fintype.ofFinite (StageLabel k J)
  let lambda : ProbabilityMeasure (StageLabel k J) :=
    ν.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  let lambdaSeq : ℕ → ProbabilityMeasure (StageLabel k J) := fun n ↦
    (νn n).map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  have hlambdaSeq : Tendsto lambdaSeq atTop (𝓝 lambda) := by
    -- Proof comment: the bundled stage alphabet is finite discrete, so the pushforward
    -- Portmanteau lemma applies once the singleton-frontier hypotheses are packaged coordinatewise.
    simpa [lambdaSeq, lambda] using
      (tendstoStageLabelPushforward_of_nullFrontierSingletons
        (ν := ν) (νn := νn) hνn (k := k) (q := q) hq hfrontier J)
  let a0 : StageLabel k J := fun i ↦ ⟨0, hk i.1⟩
  obtain ⟨Plabel, hhead, hcoord, hevent⟩ :=
    existsFiniteDiscreteLabelPathLaw (α := StageLabel k J) (a := a0) hlambdaSeq
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := StageLabel k J) (P := Plabel) hevent ε hε
  -- Proof comment: once the stage-label pushforwards are realized on one common discrete path
  -- space, the eventual equality event immediately upgrades to one deterministic tail cutoff.
  refine ⟨Plabel, ?_, ?_, N, ?_⟩
  · simpa [lambda] using hhead
  · intro n
    simpa [lambdaSeq] using hcoord n
  · simpa using hN

/-- Helper for Theorem 17.56: choose one stage-label path law for the bundled stage alphabet from
the finite-discrete Skorohod theorem. -/
private noncomputable def chosenStageLabelPathLaw
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    ProbabilityMeasure (ℕ → StageLabel k J) := by
  letI : Fintype (StageLabel k J) := Fintype.ofFinite (StageLabel k J)
  let lambda : ProbabilityMeasure (StageLabel k J) :=
    ν.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  let lambdaSeq : ℕ → ProbabilityMeasure (StageLabel k J) := fun n ↦
    (νn n).map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  have hlambdaSeq : Tendsto lambdaSeq atTop (𝓝 lambda) := by
    -- Proof comment: the bundled stage alphabet is finite discrete, so weak convergence pushes
    -- through the measurable stage-label map once the singleton-frontier condition is available.
    simpa [lambdaSeq, lambda] using
      (tendstoStageLabelPushforward_of_nullFrontierSingletons
        (ν := ν) (νn := νn) hνn (k := k) (q := q) hq hfrontier J)
  let a0 : StageLabel k J := fun i ↦ ⟨0, hk i.1⟩
  exact Classical.choose (existsFiniteDiscreteLabelPathLaw (α := StageLabel k J) (a := a0) hlambdaSeq)

/-- Helper for Theorem 17.56: the chosen bundled stage-label path law has the exact head law, the
exact time-coordinate laws, and almost-sure eventual equality. -/
private theorem chosenStageLabelPathLaw_spec
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
        (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J :
          Measure (ℕ → StageLabel k J)) =
      Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
    (∀ n : ℕ,
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J :
            Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
    (∀ᵐ ω ∂(chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J :
        Measure (ℕ → StageLabel k J)), ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  letI : Fintype (StageLabel k J) := Fintype.ofFinite (StageLabel k J)
  let lambda : ProbabilityMeasure (StageLabel k J) :=
    ν.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  let lambdaSeq : ℕ → ProbabilityMeasure (StageLabel k J) := fun n ↦
    (νn n).map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
  have hlambdaSeq : Tendsto lambdaSeq atTop (𝓝 lambda) := by
    -- Proof comment: this is the same fixed-stage pushforward convergence used in the chosen-law
    -- definition, restated here so the specification can be read off from `Classical.choose`.
    simpa [lambdaSeq, lambda] using
      (tendstoStageLabelPushforward_of_nullFrontierSingletons
        (ν := ν) (νn := νn) hνn (k := k) (q := q) hq hfrontier J)
  let a0 : StageLabel k J := fun i ↦ ⟨0, hk i.1⟩
  -- Proof comment: the chosen stage law is exactly the witness returned by the finite-discrete
  -- Skorohod path theorem on the bundled stage alphabet.
  simpa [chosenStageLabelPathLaw, lambda, lambdaSeq, a0] using
    (Classical.choose_spec
      (existsFiniteDiscreteLabelPathLaw (α := StageLabel k J) (a := a0) hlambdaSeq))

/-- Helper for Theorem 17.56: on a finite discrete alphabet, almost-sure eventual equality with
time `0` forces the coordinate laws to converge to the head law. -/
private theorem tendsto_eval_probabilityMeasure_of_ae_eventuallyEq
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [Finite α]
    {P : ProbabilityMeasure (ℕ → α)}
    (hevent :
      ∀ᵐ ω ∂(P : Measure (ℕ → α)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    Tendsto
      (fun n ↦ P.map ((measurable_pi_apply (n + 1)).aemeasurable))
      atTop
      (𝓝 (P.map (measurable_pi_apply 0).aemeasurable)) := by
  classical
  refine tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto ?_
  intro a
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let δ : ℝ := min (ε / 2) 1
  have hδ_pos : 0 < δ := by
    refine lt_min ?_ zero_lt_one
    positivity
  let εcut : ℝ≥0 := ⟨δ, le_of_lt hδ_pos⟩
  have hεcut_pos : 0 < εcut := hδ_pos
  obtain ⟨N, hNtail⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := α) (P := P) hevent εcut hεcut_pos
  have htail_le_one :
      (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) ≤ 1 := by
    simpa using
      (measure_mono (Set.subset_univ (labelTailEvent (α := α) N)) :
        (P : Measure (ℕ → α)) (labelTailEvent (α := α) N) ≤
          (P : Measure (ℕ → α)) Set.univ)
  have hεcut_le_one : (εcut : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (show εcut ≤ (1 : ℝ≥0) by
      change δ ≤ 1
      exact min_le_right _ _)
  refine ⟨N, fun n hn ↦ ?_⟩
  let disagree : Set (ℕ → α) := {ω | ω (n + 1) ≠ ω 0}
  have hdisagree_subset :
      disagree ⊆ (labelTailEvent (α := α) N)ᶜ := by
    intro ω hω htail
    exact hω (htail n hn)
  have htailCompl_lt :
      (P : Measure (ℕ → α)) (labelTailEvent (α := α) N)ᶜ < εcut := by
    rw [prob_compl_eq_one_sub (μ := (P : Measure (ℕ → α)))
      (measurableSet_labelTailEvent (α := α) N)]
    rw [ENNReal.sub_lt_iff_lt_right (measure_ne_top _ _) htail_le_one, add_comm]
    rw [ENNReal.sub_lt_iff_lt_right ENNReal.coe_ne_top hεcut_le_one, add_comm] at hNtail
    simpa [add_comm] using hNtail
  have hdisagree_lt :
      (P : Measure (ℕ → α)) disagree < εcut := by
    exact lt_of_le_of_lt (measure_mono hdisagree_subset) htailCompl_lt
  have hdisagree_toReal_lt : ((P : Measure (ℕ → α)) disagree).toReal < ε := by
    have hdisagree_toReal_lt_cut : ((P : Measure (ℕ → α)) disagree).toReal < εcut := by
      exact
        (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.coe_ne_top).2
          hdisagree_lt
    have hεcut_lt : (εcut : ℝ) < ε := by
      have hδ_le_half : δ ≤ ε / 2 := min_le_left _ _
      have hhalf_lt : ε / 2 < ε := by
        linarith
      exact lt_of_le_of_lt hδ_le_half hhalf_lt
    exact lt_of_lt_of_le hdisagree_toReal_lt_cut hεcut_lt.le
  let Aₙ : Set (ℕ → α) := {ω | ω (n + 1) = a}
  let A₀ : Set (ℕ → α) := {ω | ω 0 = a}
  have hAₙ_subset :
      Aₙ ⊆ A₀ ∪ disagree := by
    intro ω hωA
    by_cases hω0 : ω 0 = a
    · exact Or.inl hω0
    · exact Or.inr (by
        intro hEq
        exact hω0 (hEq.symm.trans hωA))
  have hA₀_subset :
      A₀ ⊆ Aₙ ∪ disagree := by
    intro ω hωA
    by_cases hωn : ω (n + 1) = a
    · exact Or.inl hωn
    · exact Or.inr (by
        intro hEq
        exact hωn (hEq.trans hωA))
  have hAₙ_le :
      (P : Measure (ℕ → α)) Aₙ ≤
        (P : Measure (ℕ → α)) A₀ + (P : Measure (ℕ → α)) disagree := by
    calc
      (P : Measure (ℕ → α)) Aₙ ≤ (P : Measure (ℕ → α)) (A₀ ∪ disagree) := by
        exact measure_mono hAₙ_subset
      _ ≤ (P : Measure (ℕ → α)) A₀ + (P : Measure (ℕ → α)) disagree := by
        exact measure_union_le A₀ disagree
  have hA₀_le :
      (P : Measure (ℕ → α)) A₀ ≤
        (P : Measure (ℕ → α)) Aₙ + (P : Measure (ℕ → α)) disagree := by
    calc
      (P : Measure (ℕ → α)) A₀ ≤ (P : Measure (ℕ → α)) (Aₙ ∪ disagree) := by
        exact measure_mono hA₀_subset
      _ ≤ (P : Measure (ℕ → α)) Aₙ + (P : Measure (ℕ → α)) disagree := by
        exact measure_union_le Aₙ disagree
  have hAₙ_toReal_le :
      ((P : Measure (ℕ → α)) Aₙ).toReal ≤
        ((P : Measure (ℕ → α)) A₀).toReal + ((P : Measure (ℕ → α)) disagree).toReal := by
    have hAₙ_toReal_le' :
        ((P : Measure (ℕ → α)) Aₙ).toReal ≤
          (((P : Measure (ℕ → α)) A₀) + ((P : Measure (ℕ → α)) disagree)).toReal := by
      exact
        (ENNReal.toReal_le_toReal
          (measure_ne_top _ _) (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)).2
          hAₙ_le
    simpa [ENNReal.toReal_add, measure_ne_top] using hAₙ_toReal_le'
  have hA₀_toReal_le :
      ((P : Measure (ℕ → α)) A₀).toReal ≤
        ((P : Measure (ℕ → α)) Aₙ).toReal + ((P : Measure (ℕ → α)) disagree).toReal := by
    have hA₀_toReal_le' :
        ((P : Measure (ℕ → α)) A₀).toReal ≤
          (((P : Measure (ℕ → α)) Aₙ) + ((P : Measure (ℕ → α)) disagree)).toReal := by
      exact
        (ENNReal.toReal_le_toReal
          (measure_ne_top _ _) (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)).2
          hA₀_le
    simpa [ENNReal.toReal_add, measure_ne_top] using hA₀_toReal_le'
  have hmass_abs :
      |((P : Measure (ℕ → α)) Aₙ).toReal - ((P : Measure (ℕ → α)) A₀).toReal| <
        ε := by
    have hle_abs :
        |((P : Measure (ℕ → α)) Aₙ).toReal - ((P : Measure (ℕ → α)) A₀).toReal| ≤
          ((P : Measure (ℕ → α)) disagree).toReal := by
      refine abs_sub_le_iff.2 ?_
      constructor <;> linarith
    exact lt_of_le_of_lt hle_abs hdisagree_toReal_lt
  have hmass_n :
      ((((P.map ((measurable_pi_apply (n + 1)).aemeasurable)) : ProbabilityMeasure α) :
          Measure α) {a}) =
        (P : Measure (ℕ → α)) Aₙ := by
    rw [ProbabilityMeasure.map_apply' (ν := P) (f := fun ω : ℕ → α ↦ ω (n + 1))
      (measurable_pi_apply (n + 1)).aemeasurable (A := {a}) (MeasurableSet.singleton a)]
    rfl
  have hmass_0 :
      ((((P.map (measurable_pi_apply 0).aemeasurable) : ProbabilityMeasure α) :
          Measure α) {a}) =
        (P : Measure (ℕ → α)) A₀ := by
    rw [ProbabilityMeasure.map_apply' (ν := P) (f := fun ω : ℕ → α ↦ ω 0)
      (measurable_pi_apply 0).aemeasurable (A := {a}) (MeasurableSet.singleton a)]
    rfl
  calc
    |((Measure.map (fun ω : ℕ → α ↦ ω (n + 1)) (P : Measure (ℕ → α))) {a}).toReal
        - ((Measure.map (fun ω : ℕ → α ↦ ω 0) (P : Measure (ℕ → α))) {a}).toReal| =
        |((P : Measure (ℕ → α)) Aₙ).toReal - ((P : Measure (ℕ → α)) A₀).toReal| := by
          rw [Measure.map_apply (measurable_pi_apply (n + 1)) (measurableSet_singleton a)]
          rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton a)]
          rfl
    _ < ε := hmass_abs

/-- Helper for Theorem 17.56: truncating the chosen stage-`J + 1` law already gives a valid
stage-`J` witness with the exact bundled marginals and the same almost-sure eventual equality
event. -/
private theorem chosenStageLabelPathLaw_truncate_spec
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
        ((((chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)).map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            ProbabilityMeasure (ℕ → StageLabel k J)) :
          Measure (ℕ → StageLabel k J)) =
      Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
    (∀ n : ℕ,
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          ((((chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
              ProbabilityMeasure (ℕ → StageLabel k J)) :
            Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
    (∀ᵐ ω ∂((((chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)).map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            ProbabilityMeasure (ℕ → StageLabel k J)) :
          Measure (ℕ → StageLabel k J)),
      ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)
  let PlabelTrunc : ProbabilityMeasure (ℕ → StageLabel k J) :=
    PlabelSucc.map (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
  have hPlabelSucc :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelSucc : Measure (ℕ → StageLabel k (J + 1))),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: expand the chosen successor-stage law once so the truncation argument can
    -- reuse its packaged bundled marginals and eventual-equality event.
    simpa [PlabelSucc] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier (J + 1)
  have hmarginals :=
    stageLabelTruncatePath_probabilityMap_marginals
      (k := k) (q := q) hq J ν νn PlabelSucc hPlabelSucc.1 hPlabelSucc.2.1
  let truncatedEvent : Set (ℕ → StageLabel k J) :=
    {ω | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0}
  have htruncatedEventMeas : MeasurableSet truncatedEvent := by
    have hrewrite :
        truncatedEvent = ⋃ N : ℕ, labelTailEvent (α := StageLabel k J) N := by
      ext ω
      simp [truncatedEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      measurableSet_labelTailEvent (α := StageLabel k J) N
  have heventTrunc :
      ∀ᵐ ω ∂(PlabelTrunc : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
    -- Proof comment: eventual equality of the chosen successor-stage law survives after
    -- coordinatewise stage truncation because the truncation map is applied to both times.
    refine (MeasureTheory.ae_map_iff
      (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
      htruncatedEventMeas).2 ?_
    filter_upwards [hPlabelSucc.2.2] with ω hω
    simpa [truncatedEvent, stageLabelTruncatePath] using
      hω.mono fun n hn ↦ congrArg (stageLabelTruncate (k := k) J) hn
  -- Proof comment: the truncated chosen law already satisfies the exact stage-`J` witness
  -- interface, so the remaining frontier is only to identify it with the separately chosen law at
  -- stage `J`.
  exact ⟨hmarginals.1, hmarginals.2, by simpa [PlabelTrunc] using heventTrunc⟩

/-- Helper for Theorem 17.56: the literal truncation of the chosen successor-stage law already
has a full dyadic label-tail cutoff table. -/
private theorem chosenStageLabelPathLaw_truncate_cutoffTable
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) :
    ∀ r : ℕ, ∃ N : ℕ,
      (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
        ((((chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)).map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            ProbabilityMeasure (ℕ → StageLabel k J)) :
          Measure (ℕ → StageLabel k J))
          (labelTailEvent (α := StageLabel k J) N) := by
  intro r
  let PlabelTrunc : ProbabilityMeasure (ℕ → StageLabel k J) :=
    ((chosenStageLabelPathLaw ν νn hνn hk hq hfrontier (J + 1)).map
      (measurable_stageLabelTruncatePath (k := k) J).aemeasurable)
  have htruncSpec :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (PlabelTrunc : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelTrunc : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelTrunc : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: unfold the literal truncation once so the generic eventual-equality cutoff
    -- theorem can be applied to a named stage-`J` law.
    simpa [PlabelTrunc] using
      chosenStageLabelPathLaw_truncate_spec ν νn hνn hk hq hfrontier J
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := StageLabel k J) (P := PlabelTrunc) htruncSpec.2.2
      ((1 / 2 : ℝ≥0) ^ (r + 1)) (by positivity)
  -- Proof comment: the truncated successor law is already eventually constant almost surely, so
  -- the standard discrete tail-cutoff extractor yields one deterministic threshold at budget `r`.
  exact ⟨N, by simpa [PlabelTrunc] using hN⟩

/-- Helper for Theorem 17.56: truncating one successor-stage label path law produces the previous
stage law with the same exact marginals and the same almost-sure eventual equality event. -/
private theorem existsPreviousStageLabelPathLawWithEventuallyEq
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval)))
    (hevent :
      ∀ᵐ ω ∂(PlabelSucc : Measure (ℕ → StageLabel k (J + 1))),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let Plabel : ProbabilityMeasure (ℕ → StageLabel k J) :=
    PlabelSucc.map (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
  have hmarginals :=
    stageLabelTruncatePath_probabilityMap_marginals
      (k := k) (q := q) hq J ν νn PlabelSucc hhead hcoord
  let truncatedEvent : Set (ℕ → StageLabel k J) :=
    {ω | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0}
  have htruncatedEventMeas : MeasurableSet truncatedEvent := by
    have hrewrite :
        truncatedEvent = ⋃ N : ℕ, labelTailEvent (α := StageLabel k J) N := by
      ext ω
      simp [truncatedEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      measurableSet_labelTailEvent (α := StageLabel k J) N
  have heventTrunc :
      ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
    -- Proof comment: eventual equality survives after stage truncation because the same
    -- coordinatewise map is applied to both times being compared.
    refine (MeasureTheory.ae_map_iff
      (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
      htruncatedEventMeas).2 ?_
    filter_upwards [hevent] with ω hω
    simpa [truncatedEvent, stageLabelTruncatePath] using
      hω.mono fun n hn ↦ congrArg (stageLabelTruncate (k := k) J) hn
  -- Proof comment: the one-step truncation map already transports the exact marginals, and the
  -- previous paragraph shows that it also preserves the eventual-equality event.
  exact ⟨Plabel, hmarginals.1, hmarginals.2, heventTrunc⟩

/-- Helper for Theorem 17.56: truncating any finite top-stage label path law down to an earlier
stage preserves its exact bundled marginals and almost-sure eventual equality. -/
private theorem existsStageLabelPrefixLawWithEventuallyEq
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    {J M : ℕ} (hJM : J ≤ M)
    (PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M))
    (hheadTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)))
    (hcoordTop :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval)))
    (heventTop :
      ∀ᵐ ω ∂(PlabelTop : Measure (ℕ → StageLabel k M)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  induction hJM with
  | refl =>
      -- Proof comment: when no coordinates are removed, the original top-stage law is already the
      -- desired prefix law.
      exact ⟨PlabelTop, hheadTop, hcoordTop, heventTop⟩
  | @step M hJM ih =>
      rcases existsPreviousStageLabelPathLawWithEventuallyEq
          ν νn (hq := hq) M PlabelTop hheadTop hcoordTop heventTop with
        ⟨PlabelMid, hheadMid, hcoordMid, heventMid⟩
      -- Proof comment: peel off one last stage coordinate and iterate the same argument along the
      -- remaining truncation chain.
      exact ih PlabelMid hheadMid hcoordMid heventMid

/-- Helper for Theorem 17.56: truncating one successor-stage label path law preserves any indexed
family of deterministic tail lower bounds. -/
private noncomputable abbrev existsPreviousStageLabelPathLawWithTailLowerBounds
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    {ι : Type*} (ε : ι → ℝ≥0) (Ncutoff : ι → ℕ)
    (PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval)))
    (htail :
      ∀ i : ι,
        (1 : ℝ≥0∞) - ε i <
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))
            (labelTailEvent (α := StageLabel k (J + 1)) (Ncutoff i))) :
    Σ' Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ i : ι,
        (1 : ℝ≥0∞) - ε i <
          (Plabel : Measure (ℕ → StageLabel k J))
            (labelTailEvent (α := StageLabel k J) (Ncutoff i))) := by
  let Plabel : ProbabilityMeasure (ℕ → StageLabel k J) :=
    PlabelSucc.map (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
  have hmarginals :=
    stageLabelTruncatePath_probabilityMap_marginals
      (k := k) (q := q) hq J ν νn PlabelSucc hhead hcoord
  have htailTrunc :
      ∀ i : ι,
        (1 : ℝ≥0∞) - ε i <
          (Plabel : Measure (ℕ → StageLabel k J))
            (labelTailEvent (α := StageLabel k J) (Ncutoff i)) := by
    intro i
    -- Proof comment: every stored threshold survives one truncation step because forgetting the
    -- last stage coordinate only enlarges the corresponding tail event.
    exact stageLabelTruncatePath_probabilityMap_tailLowerBound
      (k := k) (J := J) (ε := ε i) (N := Ncutoff i) PlabelSucc (htail i)
  -- Proof comment: the truncation map transports the exact marginals, and the previous paragraph
  -- keeps the whole indexed cutoff table unchanged.
  exact ⟨Plabel, hmarginals.1, hmarginals.2, htailTrunc⟩

/-- Helper for Theorem 17.56: every chosen top-stage law yields a whole finite truncation chain of
prefix laws whose bundled marginals are exact and whose paths are almost surely eventually
constant. -/
private theorem finiteCompatibleStageTruncationChain
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {J M : ℕ} (hJM : J ≤ M) :
    ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier M
  have hPlabelTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelTop : Measure (ℕ → StageLabel k M)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: unfold the chosen top-stage witness once, then hand the truncation work to
    -- the generic prefix lemma proved just above.
    simpa [PlabelTop] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier M
  -- Proof comment: the finite truncation chain is obtained by repeatedly applying the generic
  -- one-step truncation lemma to the chosen top-stage witness.
  exact existsStageLabelPrefixLawWithEventuallyEq
    ν νn (hq := hq) hJM PlabelTop hPlabelTop.1 hPlabelTop.2.1 hPlabelTop.2.2

/-- Helper for Theorem 17.56: every member of the finite truncation chain also admits a
deterministic dyadic tail cutoff with probability larger than
`1 - ((1 / 2 : ℝ≥0) ^ (r + 1))`. -/
private theorem finiteCompatibleStageTruncationChain_cutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {J M r : ℕ} (hJM : J ≤ M) :
    ∃ N : ℕ, ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) := by
  rcases finiteCompatibleStageTruncationChain
      ν νn hνn hk hq hfrontier hJM with
    ⟨Plabel, hhead, hcoord, hevent⟩
  let ε : ℝ≥0 := (1 / 2 : ℝ≥0) ^ (r + 1)
  have hε : 0 < ε := by
    -- Proof comment: the dyadic budget is strictly positive, so the generic tail-cutoff lemma
    -- applies directly to the stage-`J` path law.
    dsimp [ε]
    positivity
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := StageLabel k J) (P := Plabel) hevent ε hε
  -- Proof comment: combine the already constructed finite truncation-chain witness with the
  -- deterministic cutoff supplied by the stagewise eventual-equality event.
  exact ⟨N, Plabel, hhead, hcoord, by simpa [ε] using hN⟩

/-- Helper for Theorem 17.56: for one fixed top stage `M`, the finite truncation-chain API yields
prefix laws at every `J ≤ M` together with exact marginals, almost-sure eventual equality, and a
whole dyadic cutoff table for budgets indexed by `r ≤ R`. -/
private theorem finiteStageLabelPrefixFamilyWithCutoffTable
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (M R : ℕ) :
    ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
      (∀ J : Fin (M + 1),
        Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
            (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
          Measure.map (stageLabelMap (k := k) q J.1) (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : Fin (M + 1), ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
            (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
          Measure.map (stageLabelMap (k := k) q J.1) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : Fin (M + 1),
        ∀ᵐ ω ∂(PlabelRect J : Measure (ℕ → StageLabel k J.1)),
          ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) ∧
      (∀ J : Fin (M + 1), ∀ r : Fin (R + 1),
        ∃ N : ℕ,
          (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
            (PlabelRect J : Measure (ℕ → StageLabel k J.1))
              (labelTailEvent (α := StageLabel k J.1) N)) := by
  classical
  let PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1) := fun J ↦
    Classical.choose <|
      finiteCompatibleStageTruncationChain
        ν νn hνn hk hq hfrontier (Nat.le_of_lt_succ J.2)
  refine ⟨PlabelRect, ?_, ?_, ?_, ?_⟩
  · intro J
    -- Proof comment: each finite prefix law was chosen from the truncation-chain theorem, so its
    -- head marginal is exactly the bundled stage-`J` pushforward of `ν`.
    exact (Classical.choose_spec <|
      finiteCompatibleStageTruncationChain
        ν νn hνn hk hq hfrontier (Nat.le_of_lt_succ J.2)).1
  · intro J n
    -- Proof comment: the same chosen-prefix witness also carries every time-`n + 1` marginal of
    -- the approximating sequence.
    exact (Classical.choose_spec <|
      finiteCompatibleStageTruncationChain
        ν νn hνn hk hq hfrontier (Nat.le_of_lt_succ J.2)).2.1 n
  · intro J
    -- Proof comment: the finite truncation-chain witness already packages almost-sure eventual
    -- equality with time `0`, which later drives deterministic cutoff extraction.
    exact (Classical.choose_spec <|
      finiteCompatibleStageTruncationChain
        ν νn hνn hk hq hfrontier (Nat.le_of_lt_succ J.2)).2.2
  · intro J r
    let ε : ℝ≥0 := (1 / 2 : ℝ≥0) ^ (r.1 + 1)
    have hε : 0 < ε := by
      -- Proof comment: the dyadic budget is strictly positive, so the generic cutoff lemma
      -- applies to the chosen prefix law at stage `J`.
      dsimp [ε]
      positivity
    obtain ⟨N, hN⟩ :=
      exists_labelTailEvent_highProb_of_ae_eventuallyEq
        (α := StageLabel k J.1) (P := PlabelRect J)
        ((Classical.choose_spec <|
          finiteCompatibleStageTruncationChain
            ν νn hνn hk hq hfrontier (Nat.le_of_lt_succ J.2)).2.2)
        ε hε
    -- Proof comment: the stagewise eventual-equality event gives one deterministic tail threshold
    -- for every requested dyadic budget.
    exact ⟨N, by simpa [ε] using hN⟩

/-- Helper for Theorem 17.56: package the finite prefix-stage witnesses together with one explicit
cutoff table `Nrect` so the later compactness step can talk about a single finite rectangle of
compatible stage-label path laws. -/
private theorem existsCompatibleStageLabelPrefixFamilyOfTop
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    {M R : ℕ}
    (PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M))
    (hheadTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)))
    (hcoordTop :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval)))
    (Ntop : Fin (R + 1) → ℕ)
    (htailTop :
      ∀ r : Fin (R + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (PlabelTop : Measure (ℕ → StageLabel k M))
            (labelTailEvent (α := StageLabel k M) (Ntop r))) :
    ∃ PlabelRect : ∀ J : ℕ, J ≤ M → ProbabilityMeasure (ℕ → StageLabel k J),
      PlabelRect M le_rfl = PlabelTop ∧
      (∀ J (hJ : J ≤ M),
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelRect J hJ : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J (hJ : J ≤ M), ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelRect J hJ : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J (hJ : J ≤ M), ∀ r : Fin (R + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (PlabelRect J hJ : Measure (ℕ → StageLabel k J))
            (labelTailEvent (α := StageLabel k J) (Ntop r))) ∧
      (∀ J (hJ : J < M),
        PlabelRect J (Nat.le_of_lt hJ) =
          (PlabelRect (J + 1) (Nat.succ_le_of_lt hJ)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  let motive : (J : ℕ) → J ≤ M → Sort _ := fun J _ ↦
    Σ' Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ r : Fin (R + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (Plabel : Measure (ℕ → StageLabel k J))
            (labelTailEvent (α := StageLabel k J) (Ntop r)))
  let of_succ :
      ∀ J (hJ : J < M), motive (J + 1) (Nat.succ_le_of_lt hJ) →
        motive J (Nat.le_of_lt hJ) := by
    intro J hJ ih
    -- Proof comment: return the one-step truncation witness directly so the predecessor law keeps
    -- the literal truncation-map normal form produced by the prefix API.
    exact
      existsPreviousStageLabelPathLawWithTailLowerBounds
        ν νn (hq := hq) J
        (ε := fun r : Fin (R + 1) ↦ ((1 / 2 : ℝ≥0) ^ (r.1 + 1)))
        Ntop ih.1 ih.2.1 ih.2.2.1 ih.2.2.2
  let self : motive M le_rfl := ⟨PlabelTop, hheadTop, hcoordTop, htailTop⟩
  let prefixData : ∀ J : ℕ, ∀ hJ : J ≤ M, motive J hJ := fun J hJ ↦
    Nat.decreasingInduction (motive := motive) of_succ self hJ
  let PlabelRect : ∀ J : ℕ, J ≤ M → ProbabilityMeasure (ℕ → StageLabel k J) :=
    fun J hJ ↦ (prefixData J hJ).1
  refine ⟨PlabelRect, ?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: at the top stage the decreasing induction starts from the original law.
    simpa [PlabelRect, prefixData, self] using
      congrArg Sigma.fst
        (Nat.decreasingInduction_self (motive := motive) of_succ self)
  · intro J hJ
    -- Proof comment: every head marginal is stored directly in the inductive family data.
    exact (prefixData J hJ).2.1
  · intro J hJ n
    -- Proof comment: the same family data carries all time-`n + 1` marginals unchanged.
    exact (prefixData J hJ).2.2.1 n
  · intro J hJ r
    -- Proof comment: the shared cutoff table `Ntop` was propagated through each truncation step.
    exact (prefixData J hJ).2.2.2 r
  · intro J hJ
    -- Proof comment: `Nat.decreasingInduction` records the predecessor stage exactly as the
    -- truncation of the successor stage, giving literal compatibility with no extra transport.
    have hprefixDataSuccMap :
        (of_succ J hJ (prefixData (J + 1) (Nat.succ_le_of_lt hJ))).1 =
          ((prefixData (J + 1) (Nat.succ_le_of_lt hJ)).1).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable := by
      -- Proof comment: unfold the one-step predecessor constructor once; its first component is
      -- definitionally the truncation pushforward supplied by the one-step prefix API.
      simpa [of_succ, existsPreviousStageLabelPathLawWithTailLowerBounds]
    have hstep :
        (prefixData J (Nat.le_of_lt hJ)).1 =
          (of_succ J hJ (prefixData (J + 1) (Nat.succ_le_of_lt hJ))).1 := by
      exact
        congrArg (fun z ↦ z.1)
          (Nat.decreasingInduction_succ_left
            (motive := motive) of_succ self
            (smn := Nat.succ_le_of_lt hJ) (mn := Nat.le_of_lt hJ))
    calc
      PlabelRect J (Nat.le_of_lt hJ) =
          (of_succ J hJ (prefixData (J + 1) (Nat.succ_le_of_lt hJ))).1 := by
            simpa [PlabelRect, prefixData] using hstep
      _ =
          (PlabelRect (J + 1) (Nat.succ_le_of_lt hJ)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable := by
              simpa [PlabelRect] using hprefixDataSuccMap

/-- Helper for Theorem 17.56: for one fixed top stage `M`, the chosen stage-`M` law already
generates a finite rectangle of prefix laws with exact marginals, literal successor truncation
compatibility, and one shared deterministic cutoff table. -/
private theorem finiteCompatibleStageLabelTruncationRectangle
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (M R : ℕ) :
    ∃ Nrect : Fin (R + 1) → ℕ,
      ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
        (∀ J : Fin (M + 1),
          Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
              (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
            Measure.map (stageLabelMap (k := k) q J.1) (ν : Measure (ℕ → unitInterval))) ∧
        (∀ J : Fin (M + 1), ∀ n : ℕ,
          Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
              (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
            Measure.map (stageLabelMap (k := k) q J.1) (νn n : Measure (ℕ → unitInterval))) ∧
        (∀ J : Fin (M + 1), ∀ r : Fin (R + 1),
          (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
            (PlabelRect J : Measure (ℕ → StageLabel k J.1))
              (labelTailEvent (α := StageLabel k J.1) (Nrect r))) ∧
        (∀ J : Fin M,
          PlabelRect ⟨J.1, Nat.lt_succ_of_lt J.2⟩ =
            (PlabelRect ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩).map
              (measurable_stageLabelTruncatePath (k := k) J.1).aemeasurable) := by
  classical
  let PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier M
  have hPlabelTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelTop : Measure (ℕ → StageLabel k M)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: the chosen top-stage law already packages the exact bundled marginals and
    -- eventual equality needed for the compatible finite rectangle.
    simpa [PlabelTop] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier M
  let Nrect : Fin (R + 1) → ℕ := fun r ↦
    Classical.choose <|
      exists_labelTailEvent_highProb_of_ae_eventuallyEq
        (α := StageLabel k M) (P := PlabelTop) hPlabelTop.2.2
        ((1 / 2 : ℝ≥0) ^ (r.1 + 1)) <| by
          positivity
  have htailTop :
      ∀ r : Fin (R + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (PlabelTop : Measure (ℕ → StageLabel k M))
            (labelTailEvent (α := StageLabel k M) (Nrect r)) := by
    intro r
    -- Proof comment: choose one deterministic top-stage cutoff for each dyadic budget once and
    -- reuse it across the whole finite truncation rectangle.
    exact Classical.choose_spec <|
      exists_labelTailEvent_highProb_of_ae_eventuallyEq
        (α := StageLabel k M) (P := PlabelTop) hPlabelTop.2.2
        ((1 / 2 : ℝ≥0) ^ (r.1 + 1)) <| by
          positivity
  rcases existsCompatibleStageLabelPrefixFamilyOfTop
      ν νn (hq := hq) (M := M) (R := R) PlabelTop hPlabelTop.1 hPlabelTop.2.1
      Nrect htailTop with
    ⟨PlabelRectNat, htop, hhead, hcoord, htail, hcompat⟩
  let PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1) := fun J ↦
    PlabelRectNat J.1 (Nat.le_of_lt_succ J.2)
  refine ⟨Nrect, PlabelRect, ?_, ?_, ?_, ?_⟩
  · intro J
    -- Proof comment: the finite-indexed family is just the natural-number family restricted to
    -- stages `J ≤ M`, so the head marginal formula is inherited verbatim.
    exact hhead J.1 (Nat.le_of_lt_succ J.2)
  · intro J n
    -- Proof comment: the same restriction keeps every time-coordinate marginal unchanged.
    exact hcoord J.1 (Nat.le_of_lt_succ J.2) n
  · intro J r
    -- Proof comment: all finite stages use the same chosen dyadic cutoff table `Nrect`.
    exact htail J.1 (Nat.le_of_lt_succ J.2) r
  · intro J
    -- Proof comment: successor compatibility on `Fin M` is the natural-number compatibility
    -- statement specialized to `J.1 < M`.
    exact hcompat J.1 J.2

private theorem finiteCompatibleStageLabelWitnessRectangle
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (M R : ℕ) :
    ∃ Nrect : ∀ J : Fin (M + 1), Fin (R + 1) → ℕ,
      ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
        (∀ J : Fin (M + 1),
          Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
              (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
            Measure.map (stageLabelMap (k := k) q J.1) (ν : Measure (ℕ → unitInterval))) ∧
        (∀ J : Fin (M + 1), ∀ n : ℕ,
          Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
              (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
            Measure.map (stageLabelMap (k := k) q J.1) (νn n : Measure (ℕ → unitInterval))) ∧
        (∀ J : Fin (M + 1),
          ∀ᵐ ω ∂(PlabelRect J : Measure (ℕ → StageLabel k J.1)),
            ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) ∧
        (∀ J : Fin (M + 1), ∀ r : Fin (R + 1),
          (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
            (PlabelRect J : Measure (ℕ → StageLabel k J.1))
              (labelTailEvent (α := StageLabel k J.1) (Nrect J r))) := by
  classical
  rcases finiteStageLabelPrefixFamilyWithCutoffTable
      ν νn hνn hk hq hfrontier M R with
    ⟨PlabelRect, hhead, hcoord, hevent, hcutoff⟩
  let Nrect : ∀ J : Fin (M + 1), Fin (R + 1) → ℕ := fun J r ↦
    Classical.choose (hcutoff J r)
  refine ⟨Nrect, PlabelRect, hhead, hcoord, hevent, ?_⟩
  intro J r
  -- Proof comment: every finite-budget cutoff was already available existentially; `Nrect`
  -- just records those witnesses in one table that can later be frozen during compactness.
  exact Classical.choose_spec (hcutoff J r)

/-- Helper for Theorem 17.56: use the standard `PiCountable.metricSpace` on the Hilbert cube
before invoking Wasserstein or Lévy-Prokhorov API on that space. -/
private instance instHilbertCubeMetricSpace : MetricSpace (ℕ → unitInterval) :=
  PiCountable.metricSpace

/-- Helper for Theorem 17.56: a small transport budget on one Hilbert-cube coupling forces the
corresponding dyadic bad event to have small mass by Markov's inequality. -/
private theorem badMass_lt_of_transportCost_lt
    {π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval))}
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hcost :
      ∫⁻ z : (ℕ → unitInterval) × (ℕ → unitInterval),
          ENNReal.ofReal (@Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2)
            ∂(π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) <
        ENNReal.ofReal (r * ε)) :
    (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
      {z | r ≤ @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
        ENNReal.ofReal ε := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let bad : Set ((ℕ → unitInterval) × (ℕ → unitInterval)) := {z | r ≤ dist z.1 z.2}
  have hcost' :
      ∫⁻ z : (ℕ → unitInterval) × (ℕ → unitInterval),
          ENNReal.ofReal (dist z.1 z.2)
            ∂(π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) <
        ENNReal.ofReal (r * ε) := by
    simpa using hcost
  have hdistMeas : Measurable fun z : (ℕ → unitInterval) × (ℕ → unitInterval) ↦ dist z.1 z.2 :=
    (continuous_fst.dist continuous_snd).measurable
  have hmeasCost :
      Measurable fun z : (ℕ → unitInterval) × (ℕ → unitInterval) ↦
        ENNReal.ofReal (dist z.1 z.2) := by
    exact hdistMeas.ennreal_ofReal
  have hmarkov :
      ENNReal.ofReal r *
          (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) bad ≤
        ∫⁻ z : (ℕ → unitInterval) × (ℕ → unitInterval),
          ENNReal.ofReal (dist z.1 z.2)
            ∂(π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
    -- Proof comment: on the bad set the distance is at least `r`, so the transport integral
    -- dominates `r` times the bad-event mass.
    simpa [bad, hr.le] using
      (MeasureTheory.mul_meas_ge_le_lintegral hmeasCost (ENNReal.ofReal r)
        (μ := (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))))
  have hmul_lt :
      ENNReal.ofReal r *
          (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) bad <
        ENNReal.ofReal r * ENNReal.ofReal ε := by
    refine lt_of_le_of_lt hmarkov ?_
    simpa [ENNReal.ofReal_mul, hr.le, hε.le, mul_assoc] using hcost'
  have hr_ne_zero : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  simpa [bad, mul_comm] using
    (ENNReal.mul_lt_mul_iff_right hr_ne_zero ENNReal.ofReal_ne_top).1 hmul_lt

/-- Helper for Theorem 17.56: whenever the Wasserstein cost is already below the scale-budget
product `r * ε`, one may choose an actual coupling whose `r`-bad mass is below `ε`. -/
private theorem existsCouplingOfSmallBadMass_of_wassersteinDistance_lt
    (P Q : ProbabilityMeasure (ℕ → unitInterval)) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hW :
      wassersteinDistance P Q < ENNReal.ofReal (r * ε)) :
    ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
      IsCoupling π P Q ∧
        (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
          {z | r ≤ @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
            ENNReal.ofReal ε := by
  let π0 : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)) := P.prod Q
  have hπ0 : IsCoupling π0 P Q := isCoupling_prod P Q
  let S : Set ℝ≥0∞ :=
    Set.range fun π : {π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)) //
        IsCoupling π P Q} ↦
      ∫⁻ z : (ℕ → unitInterval) × (ℕ → unitInterval),
          ENNReal.ofReal (@Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2)
            ∂((π.1 : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval))) :
              Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
  have hS_nonempty : S.Nonempty := by
    refine ⟨∫⁻ z : (ℕ → unitInterval) × (ℕ → unitInterval),
        ENNReal.ofReal (@Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2)
          ∂(π0 : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))), ?_⟩
    exact ⟨⟨π0, hπ0⟩, rfl⟩
  have hsInf_lt : sInf S < ENNReal.ofReal (r * ε) := by
    simpa [S, wassersteinDistance] using hW
  obtain ⟨c, hcS, hc_lt⟩ := exists_lt_of_csInf_lt hS_nonempty hsInf_lt
  rcases hcS with ⟨⟨π, hπ⟩, rfl⟩
  -- Proof comment: choose a concrete coupling whose transport cost lies below the strict
  -- Wasserstein budget, then convert that transport bound into a bad-mass bound.
  exact ⟨π, hπ, badMass_lt_of_transportCost_lt (π := π) hr hε hc_lt⟩

/-- Helper for Theorem 17.56: weak convergence on the Hilbert cube is equivalent to convergence to
`0` for the explicit Lévy-Prokhorov distance. -/
private theorem tendsto_levyProkhorovDist_zero_of_tendsto
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    Tendsto
      (fun n ↦
        levyProkhorovDist (νn n : Measure (ℕ → unitInterval))
          (ν : Measure (ℕ → unitInterval)))
      atTop (𝓝 0) := by
  let hhomeo :=
    MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph (Ω := (ℕ → unitInterval))
  have hLP :
      Tendsto (fun n ↦ hhomeo (νn n)) atTop (𝓝 (hhomeo ν)) := by
    -- Proof comment: the homeomorphism from weak convergence to the Lévy-Prokhorov metric turns
    -- the original weak convergence hypothesis into ordinary metric convergence.
    exact hhomeo.continuous_toFun.continuousAt.tendsto.comp hνn
  have hdist :
      Tendsto (fun n ↦ dist (hhomeo (νn n)) (hhomeo ν)) atTop (𝓝 0) := by
    -- Proof comment: metric convergence is equivalent to the distance-to-limit going to `0`.
    exact tendsto_iff_dist_tendsto_zero.1 hLP
  simpa [hhomeo, MeasureTheory.LevyProkhorov.dist_probabilityMeasure_def] using hdist

/-- Helper for Theorem 17.56: each fixed dyadic Lévy-Prokhorov budget eventually controls the
whole tail of the approximating sequence. -/
private theorem existsTailIndex_lt_levyProkhorovDist_pow
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) (m : ℕ) :
    ∃ N : ℕ,
      ∀ n ≥ N,
        levyProkhorovDist (νn n : Measure (ℕ → unitInterval))
          (ν : Measure (ℕ → unitInterval)) <
            (1 / 2 : ℝ) ^ (m + 1) := by
  have hpow : 0 < (1 / 2 : ℝ) ^ (m + 1) := by
    positivity
  have htail :
      ∀ᶠ n : ℕ in atTop,
        levyProkhorovDist (νn n : Measure (ℕ → unitInterval))
          (ν : Measure (ℕ → unitInterval)) <
            (1 / 2 : ℝ) ^ (m + 1) := by
    exact (tendsto_levyProkhorovDist_zero_of_tendsto ν νn hνn) (Iio_mem_nhds hpow)
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ hN n hn⟩

/-- Helper for Theorem 17.56: at each fixed dyadic scale, weak convergence eventually provides
actual couplings whose dyadic bad masses lie below any prescribed positive budget. -/
private theorem existsTailCouplingsOfSmallDyadicBadMassWithBudget
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    ∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ,
        ∀ n ≥ N,
          ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
            IsCoupling π ν (νn n) ∧
              (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                {z | (1 / 2 : ℝ) ^ m <
                    @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} < ε := by
  classical
  intro m ε hε
  by_cases hε_le_one : ε ≤ 1
  · obtain ⟨k, hk, q, hq, _hfrontier, hdiam, Plabel, hhead, hcoord, N, hN⟩ :=
      existsCoarseLabelPathLawWithTailCutoff ν νn hνn m ε hε
    let x0 : ℕ → unitInterval := fun _ ↦ 0
    let used : Set (Fin k) := Set.range q
    let defaultUsed : used := ⟨q x0, ⟨x0, rfl⟩⟩
    let chooseRepresentative : used → (ℕ → unitInterval) := fun a ↦ Classical.choose a.2
    have hchooseRepresentative :
        ∀ a : used, q (chooseRepresentative a) = a.1 := by
      intro a
      exact Classical.choose_spec a.2
    have hchooseRepresentative_injective : Function.Injective chooseRepresentative := by
      intro a b hab
      apply Subtype.ext
      have hqeq := congrArg q hab
      simpa [hchooseRepresentative a, hchooseRepresentative b] using hqeq
    let t : Set (ℕ → unitInterval) := Set.range chooseRepresentative
    letI : Fintype t := Fintype.ofFinite t
    let embedUsed : used → t := fun a ↦ ⟨chooseRepresentative a, ⟨a, rfl⟩⟩
    have hembedUsed_injective : Function.Injective embedUsed := by
      intro a b hab
      apply hchooseRepresentative_injective
      exact Subtype.mk.inj hab
    let labelToRepresentative : Fin k → t := fun a ↦
      if ha : a ∈ used then
        embedUsed ⟨a, ha⟩
      else
        embedUsed defaultUsed
    have hlabelToRepresentative_meas : Measurable labelToRepresentative := by
      exact measurable_of_finite _
    let ρ : (ℕ → unitInterval) → t := fun x ↦ labelToRepresentative (q x)
    have hρ_eq :
        ∀ x : ℕ → unitInterval, ρ x = embedUsed ⟨q x, ⟨x, rfl⟩⟩ := by
      intro x
      simp [ρ, labelToRepresentative, used]
    have hρ_meas : Measurable ρ := by
      exact hlabelToRepresentative_meas.comp hq
    have hρ_diam :
        ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
      intro x y hxy
      have husedEq :
          (⟨q x, ⟨x, rfl⟩⟩ : used) = ⟨q y, ⟨y, rfl⟩⟩ := by
        apply hembedUsed_injective
        simpa [hρ_eq x, hρ_eq y] using hxy
      exact hdiam x y (congrArg Subtype.val husedEq)
    let pathToRepresentative : (ℕ → Fin k) → (ℕ → t) := fun ω n ↦ labelToRepresentative (ω n)
    have hpathToRepresentative_meas : Measurable pathToRepresentative := by
      refine measurable_pi_lambda pathToRepresentative ?_
      intro n
      exact hlabelToRepresentative_meas.comp (measurable_pi_apply n)
    let PlabelRep : ProbabilityMeasure (ℕ → t) :=
      Plabel.map hpathToRepresentative_meas.aemeasurable
    have hheadRep :
        Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
      -- Proof comment: evaluate the mapped representative path law at time `0`, then collapse
      -- the two successive pushforwards to the representative map `ρ`.
      calc
        Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
            Measure.map ((fun ω : ℕ → t ↦ ω 0) ∘ pathToRepresentative)
              (Plabel : Measure (ℕ → Fin k)) := by
                simpa [PlabelRep] using
                  (AEMeasurable.map_map_of_aemeasurable
                    (μ := (Plabel : Measure (ℕ → Fin k)))
                    (g := fun ω : ℕ → t ↦ ω 0)
                    (f := pathToRepresentative)
                    (measurable_pi_apply 0).aemeasurable
                    hpathToRepresentative_meas.aemeasurable)
        _ = Measure.map labelToRepresentative
              (Measure.map (fun ω : ℕ → Fin k ↦ ω 0) (Plabel : Measure (ℕ → Fin k))) := by
                rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply 0)]
                rfl
        _ = Measure.map labelToRepresentative (Measure.map q (ν : Measure (ℕ → unitInterval))) := by
                rw [hhead]
        _ = Measure.map (labelToRepresentative ∘ q) (ν : Measure (ℕ → unitInterval)) := by
                rw [Measure.map_map hlabelToRepresentative_meas hq]
        _ = ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
                rfl
    have hcoordRep :
        ∀ n : ℕ,
          Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
            ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
      intro n
      -- Proof comment: the same pushforward normalization works at every time `n + 1`.
      calc
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
            Measure.map ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ pathToRepresentative)
              (Plabel : Measure (ℕ → Fin k)) := by
                simpa [PlabelRep] using
                  (AEMeasurable.map_map_of_aemeasurable
                    (μ := (Plabel : Measure (ℕ → Fin k)))
                    (g := fun ω : ℕ → t ↦ ω (n + 1))
                    (f := pathToRepresentative)
                    (measurable_pi_apply (n + 1)).aemeasurable
                    hpathToRepresentative_meas.aemeasurable)
        _ = Measure.map labelToRepresentative
              (Measure.map (fun ω : ℕ → Fin k ↦ ω (n + 1)) (Plabel : Measure (ℕ → Fin k))) := by
                rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply (n + 1))]
                rfl
        _ = Measure.map labelToRepresentative
              (Measure.map q (νn n : Measure (ℕ → unitInterval))) := by
                rw [hcoord n]
        _ = Measure.map (labelToRepresentative ∘ q) (νn n : Measure (ℕ → unitInterval)) := by
                rw [Measure.map_map hlabelToRepresentative_meas hq]
        _ = ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
                rfl
    have htailRep :
        (1 : ℝ≥0∞) - ε <
          (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
      have hsubset :
          labelTailEvent (α := Fin k) N ⊆
            pathToRepresentative ⁻¹' labelTailEvent (α := t) N := by
        intro ω hω
        intro n hn
        simpa [pathToRepresentative] using congrArg labelToRepresentative (hω n hn)
      calc
        (1 : ℝ≥0∞) - ε < (Plabel : Measure (ℕ → Fin k)) (labelTailEvent N) := hN
        _ ≤ (Plabel : Measure (ℕ → Fin k))
              (pathToRepresentative ⁻¹' labelTailEvent (α := t) N) := by
                exact measure_mono hsubset
        _ = (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
                symm
                exact Measure.map_apply hpathToRepresentative_meas
                  (measurableSet_labelTailEvent (α := t) N)
    obtain ⟨π, hπ⟩ :=
      existsLiftedRepresentativePairLawsWithBadMassControl
        (hρmeas := hρ_meas) ν νn PlabelRep hheadRep hcoordRep hρ_diam
    refine ⟨N, ?_⟩
    intro n hn
    refine ⟨π n, (hπ n).1, ?_⟩
    have hbad_le :
        (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
            {z | (1 / 2 : ℝ) ^ m <
                @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} ≤
          (Measure.map (headAndNext (β := t) n) (PlabelRep : Measure (ℕ → t)))
            {p | p.1 ≠ p.2} := by
      exact (hπ n).2
    have hoffDiag_le :
        (Measure.map (headAndNext (β := t) n) (PlabelRep : Measure (ℕ → t)))
            {p : t × t | p.1 ≠ p.2} ≤
          (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N)ᶜ := by
      exact headAndNext_offDiagonal_le_compl_labelTailEvent PlabelRep hn
    have hlabel_le_one :
        (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) ≤ 1 := by
      simpa using
        (measure_mono (Set.subset_univ (labelTailEvent (α := t) N)) :
          (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) ≤
            (PlabelRep : Measure (ℕ → t)) Set.univ)
    have hε_le_one' : (ε : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast hε_le_one
    have htailCompl_lt :
        (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N)ᶜ < ε := by
      rw [prob_compl_eq_one_sub (μ := (PlabelRep : Measure (ℕ → t)))
        (measurableSet_labelTailEvent (α := t) N)]
      rw [ENNReal.sub_lt_iff_lt_right (measure_ne_top _ _) hlabel_le_one, add_comm]
      rw [ENNReal.sub_lt_iff_lt_right ENNReal.coe_ne_top hε_le_one', add_comm] at htailRep
      simpa [add_comm] using htailRep
    exact lt_of_le_of_lt (le_trans hbad_le hoffDiag_le) htailCompl_lt
  · have hε_big : (1 : ℝ≥0) < ε := lt_of_not_ge hε_le_one
    refine ⟨0, ?_⟩
    intro n _hn
    refine ⟨ν.prod (νn n), isCoupling_prod ν (νn n), ?_⟩
    have hprob :
        (ν.prod (νn n) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
            {z | (1 / 2 : ℝ) ^ m <
                @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} ≤ 1 := by
      calc
        (ν.prod (νn n) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
            {z | (1 / 2 : ℝ) ^ m <
                @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} ≤
            (ν.prod (νn n) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) Set.univ := by
              exact measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    have hε_big' : (1 : ℝ≥0∞) < (ε : ℝ≥0∞) := by
      exact_mod_cast hε_big
    exact lt_of_le_of_lt hprob hε_big'

/-- Helper for Theorem 17.56: at each fixed dyadic scale, weak convergence eventually provides
actual couplings whose dyadic bad masses are uniformly small. -/
private theorem existsTailCouplingsOfSmallDyadicBadMass
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    ∀ m : ℕ,
      ∃ N : ℕ,
        ∀ n ≥ N,
          ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
            IsCoupling π ν (νn n) ∧
              (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                  {z | (1 / 2 : ℝ) ^ m <
                      @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
                    ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  intro m
  let ε : ℝ≥0 := ⟨(1 / 2 : ℝ) ^ m, by positivity⟩
  have hε : 0 < ε := by
    change 0 < ((1 / 2 : ℝ) ^ m)
    positivity
  -- Proof comment: specialize the arbitrary-budget theorem to the canonical dyadic budget
  -- `ε = (1 / 2)^m`.
  obtain ⟨N, hN⟩ :=
    existsTailCouplingsOfSmallDyadicBadMassWithBudget ν νn hνn m ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨π, hπ, hbad⟩
  refine ⟨π, hπ, ?_⟩
  simpa [ε, ENNReal.ofReal_eq_coe_nnreal] using hbad

/-- Helper for Theorem 17.56: a coarser dyadic bad event is contained in every finer dyadic bad
event, because the finer threshold is smaller. -/
private theorem dyadicBadEvent_monoScale
    {m r : ℕ} (hmr : m ≤ r) :
    {z : (ℕ → unitInterval) × (ℕ → unitInterval) |
        (1 / 2 : ℝ) ^ m <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} ⊆
      {z : (ℕ → unitInterval) × (ℕ → unitInterval) |
        (1 / 2 : ℝ) ^ r <
          @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} := by
  intro z hz
  have hpow : (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ m := by
    exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hmr
  -- Proof comment: replacing the coarser threshold by the smaller finer one only weakens the
  -- bad-event inequality.
  exact lt_of_le_of_lt hpow hz

/-- Helper for Theorem 17.56: the measure of the dyadic bad event is monotone in the scale
parameter. -/
private theorem dyadicBadMass_monoScale
    {π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval))}
    {m r : ℕ} (hmr : m ≤ r) :
    (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
        {z | (1 / 2 : ℝ) ^ m <
            @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} ≤
      (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
        {z | (1 / 2 : ℝ) ^ r <
            @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} := by
  -- Proof comment: after isolating the set inclusion once, the measure comparison is immediate.
  exact measure_mono (dyadicBadEvent_monoScale hmr)

/-- Helper for Theorem 17.56: once weak convergence gives small bad mass at a finer dyadic
scale `r`, the same coupling bound automatically controls every coarser scale `m ≤ r`. -/
private theorem existsTailCouplingsOfSmallDyadicBadMass_monoScale
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {m r : ℕ} (hmr : m ≤ r) :
    ∃ N : ℕ,
      ∀ n ≥ N,
        ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
          IsCoupling π ν (νn n) ∧
            (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                {z | (1 / 2 : ℝ) ^ m <
                    @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
              ENNReal.ofReal ((1 / 2 : ℝ) ^ r) := by
  obtain ⟨N, hN⟩ := existsTailCouplingsOfSmallDyadicBadMass ν νn hνn r
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨π, hπ, hbad⟩
  refine ⟨π, hπ, ?_⟩
  -- Proof comment: the finer-scale bad-mass estimate already dominates the coarser bad event.
  exact lt_of_le_of_lt (dyadicBadMass_monoScale (π := π) hmr) hbad

/-- Helper for Theorem 17.56: from a state `(L, x)` consisting of a stored finite label path `L`
and one ambient Hilbert-cube point `x`, the frozen-label-state kernel keeps `L` fixed and resamples
the ambient component from the normalized fiber over the `k`th stored label. -/
private noncomputable def frozenLabelStateKernel
    {t : Set (ℕ → unitInterval)} [Fintype t]
    (μ : ProbabilityMeasure (ℕ → unitInterval)) (ρ : (ℕ → unitInterval) → t) (k : ℕ) :
    Kernel ((ℕ → t) × (ℕ → unitInterval)) ((ℕ → t) × (ℕ → unitInterval)) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
    Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst

/-- Helper for Theorem 17.56: the frozen-label-state kernel keeps the stored label path as its
first marginal. -/
private theorem fst_frozenLabelStateKernel
    {t : Set (ℕ → unitInterval)} [Fintype t]
    (μ : ProbabilityMeasure (ℕ → unitInterval)) (ρ : (ℕ → unitInterval) → t) (k : ℕ) :
    Kernel.fst (frozenLabelStateKernel μ ρ k) =
      Kernel.deterministic Prod.fst measurable_fst := by
  -- Proof comment: `frozenLabelStateKernel` is a product kernel whose first factor is already the
  -- deterministic stored-label projection, so `Kernel.fst` collapses immediately.
  simpa [frozenLabelStateKernel] using
    (Kernel.fst_prod
      (κ := Kernel.deterministic Prod.fst measurable_fst)
      (η := Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst))

/-- Helper for Theorem 17.56: the second marginal of the frozen-label-state kernel is exactly the
normalized-fiber kernel read from the stored label path. -/
private theorem snd_frozenLabelStateKernel
    {t : Set (ℕ → unitInterval)} [Fintype t]
    (μ : ProbabilityMeasure (ℕ → unitInterval)) (ρ : (ℕ → unitInterval) → t) (k : ℕ) :
    Kernel.snd (frozenLabelStateKernel μ ρ k) =
      Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst := by
  -- Proof comment: the second marginal of the product kernel is exactly the resampling kernel,
  -- because the deterministic first factor is Markov.
  simpa [frozenLabelStateKernel] using
    (Kernel.snd_prod
      (κ := Kernel.deterministic Prod.fst measurable_fst)
      (η := Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst))

/-- Helper for Theorem 17.56: sampling a representative label and then resampling from the
corresponding normalized fiber produces a pair whose representative coordinates lie on the
diagonal. -/
private theorem representativePairMap_compProd_normalizedFiberKernel_eq_diagonal [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E) (hρmeas : Measurable ρ) :
    Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
        ((((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) ⊗ₘ
          normalizedFiberKernel μ ρ) : Measure (t × E)) =
      Measure.map (fun a : t ↦ (a, a))
        (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) := by
  let μrep : Measure t := ((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)
  have hpairMeas : Measurable (fun z : t × E ↦ (z.1, ρ z.2)) := by
    -- Proof comment: the representative-pair map is measurable coordinatewise.
    fun_prop
  -- Proof comment: expand the composition product over the finite base alphabet, identify each
  -- cell with a weighted diagonal Dirac mass, and repackage the resulting finite sum as the
  -- diagonal pushforward of the representative law.
  calc
    Measure.map (fun z : t × E ↦ (z.1, ρ z.2)) (μrep ⊗ₘ normalizedFiberKernel μ ρ) =
        ∑ a : t,
          Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
            (μrep {a} • (((Kernel.id ×ₖ normalizedFiberKernel μ ρ) a : Measure (t × E)))) := by
          rw [Measure.compProd_eq_comp_prod, Measure.comp_eq_sum_of_countable]
          rw [Measure.map_sum hpairMeas.aemeasurable, Measure.sum_fintype]
    _ = ∑ a : t, μrep {a} • Measure.dirac (a, a) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          by_cases ha0 : μrep {a} = 0
          · -- Proof comment: zero-mass cells disappear immediately after the scalar factor is
            -- pulled through the map.
            simp [ha0]
          · have hmass_ne :
                (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0 := by
              rw [fiberMass_eq_mapSingleton (μ := μ) (hρmeas := hρmeas) a]
              exact ha0
            have hkernel_eq :
                (((Kernel.id ×ₖ normalizedFiberKernel μ ρ) a : Measure (t × E))) =
                  (Measure.dirac a).prod (((normalizedFiberKernel μ ρ a) : Measure E)) := by
              ext s hs
              rw [Kernel.id_prod_apply' (κ := normalizedFiberKernel μ ρ) (a := a) hs]
              rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hs]
            have hcell :
                Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
                    (((Kernel.id ×ₖ normalizedFiberKernel μ ρ) a : Measure (t × E))) =
                  Measure.dirac (a, a) := by
              calc
                Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
                    (((Kernel.id ×ₖ normalizedFiberKernel μ ρ) a : Measure (t × E))) =
                    Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
                      ((Measure.dirac a).prod
                        (((normalizedFiberKernel μ ρ a) : Measure E))) := by
                          rw [hkernel_eq]
                _ =
                    (Measure.map (id : t → t) (Measure.dirac a)).prod
                      (Measure.map ρ (((normalizedFiberKernel μ ρ a) : Measure E))) := by
                        simpa using
                          (Measure.map_prod_map
                            (μa := Measure.dirac a)
                            (μc := (((normalizedFiberKernel μ ρ a) : Measure E)))
                            measurable_id hρmeas).symm
                _ = (Measure.dirac a).prod (Measure.dirac a) := by
                      rw [Measure.map_id]
                      exact congrArg (fun ν : Measure t ↦ (Measure.dirac a).prod ν)
                        (map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
                          (μ := μ) (hρmeas := hρmeas) a hmass_ne)
                _ = Measure.dirac (a, a) := by
                      simpa using Measure.dirac_prod_dirac
            rw [Measure.map_smul, hcell]
    _ = (Kernel.deterministic (fun a : t ↦ (a, a)) (by fun_prop)) ∘ₘ μrep := by
          rw [Measure.comp_eq_sum_of_countable, Measure.sum_fintype]
          refine Finset.sum_congr rfl ?_
          intro a ha
          rfl
    _ = Measure.map (fun a : t ↦ (a, a)) μrep := by
          rw [Measure.deterministic_comp_eq_map]

/-- Helper for Theorem 17.56: after first reading the stored label at coordinate `k`, the
label/state composition product pushes forward to the diagonal law of that coordinate. -/
private theorem representativeMap_headAndNext_eq_diagonal_of_frozenLabelState [Nonempty E]
    {t : Set E} [Fintype t] {ρ : E → t} (μ : ProbabilityMeasure E) (hρmeas : Measurable ρ)
    {Plabel : ProbabilityMeasure (ℕ → t)} {k : ℕ}
    (hk :
      Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t)) =
        ((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t)) :
    Measure.map (fun z : (ℕ → t) × E ↦ (z.1 k, ρ z.2))
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      Measure.map (fun a : t ↦ (a, a))
        (Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t))) := by
  have hbase :
      Measure.map (fun z : (ℕ → t) × E ↦ (z.1 k, z.2))
          (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
            Measure ((ℕ → t) × E)) =
        (Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t))) ⊗ₘ
          normalizedFiberKernel μ ρ := by
    -- Proof comment: `normalizedFiberKernelAt` is the coordinate pullback of the finite-label
    -- fiber kernel, so mapping the base path to coordinate `k` removes the pullback.
    simpa [normalizedFiberKernelAt_eq_comap] using
      (compProd_map_base_eq_compProd
        (μ := (Plabel : Measure (ℕ → t)))
        (f := fun ω : ℕ → t ↦ ω k)
        (hf := measurable_pi_apply k)
        (κ := normalizedFiberKernel μ ρ))
  -- Proof comment: after collapsing the base path to its `k`th coordinate, the previous
  -- diagonal pair theorem applies verbatim.
  calc
    Measure.map (fun z : (ℕ → t) × E ↦ (z.1 k, ρ z.2))
        (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
          Measure ((ℕ → t) × E)) =
      Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
        (Measure.map (fun z : (ℕ → t) × E ↦ (z.1 k, z.2))
          (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ ρ k) :
            Measure ((ℕ → t) × E))) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ =
      Measure.map (fun z : t × E ↦ (z.1, ρ z.2))
        ((Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t))) ⊗ₘ
          normalizedFiberKernel μ ρ) := by
            rw [hbase]
    _ =
      Measure.map (fun a : t ↦ (a, a))
        (Measure.map (fun ω : ℕ → t ↦ ω k) (Plabel : Measure (ℕ → t))) := by
            rw [hk]
            exact representativePairMap_compProd_normalizedFiberKernel_eq_diagonal
              (μ := μ) (ρ := ρ) hρmeas

/-- Helper for Theorem 17.56: if a pair-valued random variable has diagonal pushforward law, then
its two coordinates agree almost surely. -/
private theorem ae_eq_of_map_eq_diagonal
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableEq α]
    {P : Measure Ω} {L X : Ω → α} {μ : Measure α}
    (hLXmeas : Measurable fun ω : Ω ↦ (L ω, X ω))
    (hmap :
      Measure.map (fun ω : Ω ↦ (L ω, X ω)) P =
        Measure.map (fun a : α ↦ (a, a)) μ) :
    ∀ᵐ ω ∂P, L ω = X ω := by
  -- Proof comment: the complement of the diagonal has zero mass under any diagonal pushforward,
  -- so the original pair must land on the diagonal almost surely.
  rw [ae_iff]
  calc
    P {ω | L ω ≠ X ω}
        = Measure.map (fun ω : Ω ↦ (L ω, X ω)) P {p : α × α | p.1 ≠ p.2} := by
            symm
            exact Measure.map_apply hLXmeas (measurableSet_offDiagonal (t := α))
    _ = Measure.map (fun a : α ↦ (a, a)) μ {p : α × α | p.1 ≠ p.2} := by
          rw [hmap]
    _ = 0 := by
          rw [Measure.map_apply (by fun_prop) (measurableSet_offDiagonal (t := α))]
          simp

/-- Helper for Theorem 17.56: countably many almost-sure coordinate equalities assemble into an
almost-sure equality of the whole path. -/
private theorem ae_path_eq_of_forall_ae_eq
    {Ω α : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℕ → α}
    (hcoord : ∀ k : ℕ, ∀ᵐ ω ∂P, f ω k = g ω k) :
    ∀ᵐ ω ∂P, f ω = g ω := by
  -- Proof comment: `ae_all_iff` packages the coordinatewise equalities into one full-path
  -- equality event, and then function extensionality closes the pointwise statement.
  filter_upwards [ae_all_iff.2 hcoord] with ω hω
  funext k
  exact hω k

/-- Helper for Theorem 17.56: if every coordinate pair map is almost surely diagonal, then the
whole projected path agrees almost surely with the stored label path. -/
private theorem ae_path_eq_of_forall_map_eq_diagonal
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableEq α]
    {P : Measure Ω} {L X : Ω → ℕ → α}
    (hmeas : ∀ k : ℕ, Measurable fun ω : Ω ↦ (L ω k, X ω k))
    (hdiag :
      ∀ k : ℕ, ∃ μk : Measure α,
        Measure.map (fun ω : Ω ↦ (L ω k, X ω k)) P =
          Measure.map (fun a : α ↦ (a, a)) μk) :
    ∀ᵐ ω ∂P, L ω = X ω := by
  have hcoord : ∀ k : ℕ, ∀ᵐ ω ∂P, L ω k = X ω k := by
    intro k
    rcases hdiag k with ⟨μk, hμk⟩
    -- Proof comment: each coordinate pair map has diagonal pushforward law, so the two
    -- coordinate projections agree almost surely by the scalar diagonal lemma.
    exact ae_eq_of_map_eq_diagonal (P := P)
      (L := fun ω ↦ L ω k) (X := fun ω ↦ X ω k)
      (μ := μk) (hLXmeas := hmeas k) hμk
  -- Proof comment: once every coordinate agrees almost surely, the full paths agree almost surely.
  exact ae_path_eq_of_forall_ae_eq hcoord

/-- Helper for Theorem 17.56: any stagewise family of pair couplings with common first marginal
induces a path law whose head law is exact, whose coordinates up to stage `J` have the prescribed
laws, and whose dyadic tail-event complement is bounded by the corresponding tail sum of pairwise
bad masses. -/
private theorem existsHilbertCubeStageLawOfPairCouplings
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (J : ℕ)
    (π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)))
    (hfst :
      ∀ n : ℕ,
        Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (ν : Measure (ℕ → unitInterval)))
    (hsnd :
      ∀ n : ℕ, n ≤ J →
        Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) :
    ∃ Pstage : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m N : ℕ,
        (Pstage : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)ᶜ ≤
          ∑' k : ℕ,
            ((π (N + k) : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
              {z | (1 / 2 : ℝ) ^ m <
                  @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2})) := by
  let κ : ℕ → Kernel (ℕ → unitInterval) (ℕ → unitInterval) :=
    fun n ↦ (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel
  let Pm : Measure (ℕ → (ℕ → unitInterval)) :=
    headIndexedPathMeasure (β := ℕ → unitInterval) (μ := (ν : Measure (ℕ → unitInterval))) κ
  have hPm : IsProbabilityMeasure Pm := by
    -- Proof comment: the head-indexed path measure is a probability measure because it starts
    -- from the probability law `ν` and uses Markov kernels at every step.
    dsimp [Pm]
    infer_instance
  let Pstage : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) := ⟨Pm, hPm⟩
  have hpair :
      ∀ n : ℕ,
        Measure.map (headAndNext (β := ℕ → unitInterval) n)
            (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
          (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
    intro n
    -- Proof comment: disintegrating each pair law over its first marginal matches the
    -- owner `headIndexedPathMeasure_map_headAndNext` normal form exactly.
    calc
      Measure.map (headAndNext (β := ℕ → unitInterval) n)
          (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ⊗ₘ κ n := by
          simpa [Pstage, Pm, κ] using
            (headIndexedPathMeasure_map_headAndNext
              (β := ℕ → unitInterval)
              (μ := (ν : Measure (ℕ → unitInterval))) (κ := κ) n)
      _ =
          (Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))) ⊗ₘ
              ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel) := by
            rw [← hfst n]
      _ = (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
            simpa [κ] using
              ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).disintegrate
                ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))).condKernel))
  refine ⟨Pstage, ?_, ?_, ?_⟩
  · -- Proof comment: time `0` of the head-indexed path law keeps the base marginal `ν`.
    change Measure.map (Function.eval 0) (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
      (ν : Measure (ℕ → unitInterval))
    simpa [Pstage, Pm, κ] using
      (headIndexedTrajMeasure_map_eval_zero
        (β := ℕ → unitInterval) (μ := (ν : Measure (ℕ → unitInterval))) (κ := κ))
  · intro n hn
    -- Proof comment: for `n ≤ J`, the `(n + 1)`st coordinate is the second marginal of the
    -- recovered pair law at time `n`.
    have hheadAndNextComp :
        Prod.snd ∘ headAndNext (β := ℕ → unitInterval) n =
          (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1)) := by
      funext ω
      rfl
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map Prod.snd
          (Measure.map (headAndNext (β := ℕ → unitInterval) n)
            (Pstage : Measure (ℕ → (ℕ → unitInterval)))) := by
            rw [Measure.map_map measurable_snd (by fun_prop)]
            rw [hheadAndNextComp]
      _ =
          Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) := by
              rw [hpair n]
      _ = (νn n : Measure (ℕ → unitInterval)) := hsnd n hn
  · intro m N
    -- Proof comment: once the pair marginals are normalized by `hpair`, the dyadic-tail
    -- complement estimate is exactly the owner tail-measure lemma proved earlier.
    exact measure_compl_dyadicTailEvent_le_tsum_pairBadMass hpair m N

/-- Helper for Theorem 17.56: pushing a probability law forward along the diagonal map gives the
canonical self-coupling with both marginals equal to the original law. -/
private def diagonalSelfCoupling {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure β) : ProbabilityMeasure (β × β) :=
  μ.map (f := fun x ↦ (x, x)) (measurable_id.prodMk measurable_id).aemeasurable

/-- Helper for Theorem 17.56: the first marginal of the diagonal self-coupling is the original
law. -/
@[simp] private theorem fst_diagonalSelfCoupling {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure β) :
    Measure.map Prod.fst (diagonalSelfCoupling μ : Measure (β × β)) = (μ : Measure β) := by
  -- Proof comment: both pushforwards collapse to `id` after one `Measure.map_map` normalization.
  calc
    Measure.map Prod.fst (diagonalSelfCoupling μ : Measure (β × β)) =
        Measure.map (Prod.fst ∘ fun x : β ↦ (x, x)) (μ : Measure β) := by
          simpa [diagonalSelfCoupling] using
            (Measure.map_map (μ := (μ : Measure β))
              measurable_fst (measurable_id.prodMk measurable_id))
    _ =
        Measure.map (fun x : β ↦ x) (μ : Measure β) := by
          rfl
    _ = (μ : Measure β) := by
          simpa using (Measure.map_id (μ := (μ : Measure β)))

/-- Helper for Theorem 17.56: the second marginal of the diagonal self-coupling is the original
law. -/
@[simp] private theorem snd_diagonalSelfCoupling {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure β) :
    Measure.map Prod.snd (diagonalSelfCoupling μ : Measure (β × β)) = (μ : Measure β) := by
  -- Proof comment: the same normalization works for the second coordinate projection.
  calc
    Measure.map Prod.snd (diagonalSelfCoupling μ : Measure (β × β)) =
        Measure.map (Prod.snd ∘ fun x : β ↦ (x, x)) (μ : Measure β) := by
          simpa [diagonalSelfCoupling] using
            (Measure.map_map (μ := (μ : Measure β))
              measurable_snd (measurable_id.prodMk measurable_id))
    _ =
        Measure.map (fun x : β ↦ x) (μ : Measure β) := by
          rfl
    _ = (μ : Measure β) := by
          simpa using (Measure.map_id (μ := (μ : Measure β)))

/-- Helper for Theorem 17.56: the diagonal pushforward of a probability law is a genuine
self-coupling. -/
private theorem isCoupling_diagonalSelfCoupling {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure β) :
    IsCoupling (diagonalSelfCoupling μ) μ μ := by
  exact ⟨fst_diagonalSelfCoupling μ, snd_diagonalSelfCoupling μ⟩

/-- Helper for Theorem 17.56: the dyadic bad set has zero mass under the diagonal self-coupling,
because every sampled pair is exactly `(x, x)`. -/
private theorem diagonalSelfCoupling_badMass_eq_zero
    (μ : ProbabilityMeasure (ℕ → unitInterval)) (m : ℕ) :
    (diagonalSelfCoupling μ : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
        {z | (1 / 2 : ℝ) ^ m <
            @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} = 0 := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let bad : Set ((ℕ → unitInterval) × (ℕ → unitInterval)) :=
    {z | (1 / 2 : ℝ) ^ m <
        @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2}
  have hmeas :
      MeasurableSet bad :=
    (isOpen_lt
      (f := fun _ : (ℕ → unitInterval) × (ℕ → unitInterval) ↦ ((1 / 2 : ℝ) ^ m))
      (g := fun z : (ℕ → unitInterval) × (ℕ → unitInterval) ↦ dist z.1 z.2)
      continuous_const (continuous_fst.dist continuous_snd)).measurableSet
  -- Proof comment: after pulling back through the diagonal map, the bad set becomes empty
  -- because `dist x x = 0`.
  have hpreimage :
      (fun x : ℕ → unitInterval ↦ (x, x)) ⁻¹' bad = ∅ := by
    ext x
    simp [bad]
  calc
    (diagonalSelfCoupling μ : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) bad =
        (μ : Measure (ℕ → unitInterval)) ((fun x : ℕ → unitInterval ↦ (x, x)) ⁻¹' bad) := by
          simpa [diagonalSelfCoupling] using
            (Measure.map_apply
              (μ := (μ : Measure (ℕ → unitInterval)))
              (f := fun x : ℕ → unitInterval ↦ (x, x))
              (s := bad)
              (measurable_id.prodMk measurable_id)
              hmeas)
    _ = 0 := by
          rw [hpreimage]
          simp

/-- Helper for Theorem 17.56: the dyadic tail-coupling input already constructs, for each finite
stage `J`, one Hilbert-cube path law with the exact prefix marginals required by the compactness
extraction step. -/
private theorem existsHilbertCubeStageLawOfDyadicTailCouplings
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hpairTail :
      ∀ m : ℕ,
        ∃ N : ℕ,
          ∀ n ≥ N,
            ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
              IsCoupling π ν (νn n) ∧
                (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                  {z | (1 / 2 : ℝ) ^ m <
                      @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
                    ENNReal.ofReal ((1 / 2 : ℝ) ^ m))
    (J : ℕ) :
    ∃ Pstage : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pstage : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) := by
  obtain ⟨N, hN⟩ := hpairTail J
  let π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)) := fun n ↦
    if hn : n ≤ J then
      if hNn : N ≤ n then
        Classical.choose (hN n hNn)
      else
        ν.prod (νn n)
    else
      diagonalSelfCoupling ν
  have hfst :
      ∀ n : ℕ,
        Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (ν : Measure (ℕ → unitInterval)) := by
    intro n
    by_cases hn : n ≤ J
    · by_cases hNn : N ≤ n
      · -- Proof comment: on the dyadic tail, reuse the chosen coupling delivered by `hpairTail`.
        simpa [π, hn, hNn] using (Classical.choose_spec (hN n hNn)).1.1
      · -- Proof comment: before the dyadic tail starts, the product coupling still has the
        -- required first marginal `ν`.
        simpa [π, hn, hNn] using (isCoupling_prod ν (νn n)).1
    · -- Proof comment: beyond the finite stage, a trivial product coupling is enough because only
      -- the common first marginal matters, and the diagonal self-coupling is the sharper choice.
      simpa [π, hn] using (isCoupling_diagonalSelfCoupling ν).1
  have hsnd :
      ∀ n : ℕ, n ≤ J →
        Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval)) := by
    intro n hn
    by_cases hNn : N ≤ n
    · -- Proof comment: on the tail segment, the chosen coupling also carries the prescribed
      -- second marginal `νn n`.
      simpa [π, hn, hNn] using (Classical.choose_spec (hN n hNn)).1.2
    · -- Proof comment: before the tail cutoff, the product coupling again supplies the exact
      -- second marginal needed for the finite prefix.
      simpa [π, hn, hNn] using (isCoupling_prod ν (νn n)).2
  obtain ⟨Pstage, hhead, hcoord, _htail⟩ :=
    existsHilbertCubeStageLawOfPairCouplings ν νn J π hfst hsnd
  exact ⟨Pstage, hhead, hcoord⟩

/-- Helper for Theorem 17.56: choosing the previous stage law separately for each `J` already
stabilizes the exact head and finite-prefix marginals of the approximate stage family. -/
private theorem existsExactHilbertCubeStageFamilyOfDyadicTailCouplings
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hpairTail :
      ∀ m : ℕ,
        ∃ N : ℕ,
          ∀ n ≥ N,
            ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
              IsCoupling π ν (νn n) ∧
                (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                  {z | (1 / 2 : ℝ) ^ m <
                      @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
                    ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) :
    ∃ Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) := by
  classical
  let Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)) := fun J ↦
    Classical.choose (existsHilbertCubeStageLawOfDyadicTailCouplings ν νn hpairTail J)
  refine ⟨Pstage, ?_, ?_⟩
  · intro J
    -- Proof comment: for each finite stage, reuse the chosen stage law and read off its head
    -- marginal from the specification returned by
    -- `existsHilbertCubeStageLawOfDyadicTailCouplings`.
    exact (Classical.choose_spec
      (existsHilbertCubeStageLawOfDyadicTailCouplings ν νn hpairTail J)).1
  · intro n J hn
    -- Proof comment: the same chosen stage law already carries every prefix marginal `ω (n + 1)`
    -- for `n ≤ J`; only the quantifier order changes in the family statement.
    exact (Classical.choose_spec
      (existsHilbertCubeStageLawOfDyadicTailCouplings ν νn hpairTail J)).2 n hn

/-- Helper for Theorem 17.56: any scale-wise small-budget coupling API can be reorganized along
one strict schedule of cutoff indices, so later block arguments can work with a fixed increasing
family of tail thresholds. -/
private theorem existsStrictMonoDyadicBudgetSchedule
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hpairBudget :
      ∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N,
            ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
              IsCoupling π ν (νn n) ∧
                (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                  {z | (1 / 2 : ℝ) ^ m <
                      @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} < ε) :
    ∃ B : ℕ → ℕ, StrictMono B ∧
      ∀ r : ℕ,
        ∀ n ≥ B r,
          ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
            IsCoupling π ν (νn n) ∧
              (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                {z | (1 / 2 : ℝ) ^ r <
                    @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
                  ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) := by
  classical
  let budget : ℕ → ℝ≥0 := fun r ↦ (1 / 2 : ℝ≥0) ^ (r + 1)
  have hbudget_pos : ∀ r : ℕ, 0 < budget r := by
    intro r
    dsimp [budget]
    positivity
  let cutoff : ℕ → ℕ := fun r ↦
    Classical.choose (hpairBudget r (budget r) (hbudget_pos r))
  let B : ℕ → ℕ := fun r ↦ Finset.sum (Finset.range (r + 1)) fun i ↦ cutoff i + 1
  refine ⟨B, ?_, ?_⟩
  · -- Proof comment: each successor stage adds the strictly positive term
    -- `cutoff (r + 1) + 1`, so the cumulative schedule is strictly increasing.
    refine strictMono_nat_of_lt_succ ?_
    intro r
    rw [show B (r + 1) =
      Finset.sum (Finset.range (r + 2)) (fun i ↦ cutoff i + 1) by rfl, Finset.sum_range_succ]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  · intro r n hn
    have hcutoff_le : cutoff r ≤ B r := by
      -- Proof comment: the cumulative schedule `B r` contains the summand `cutoff r + 1`,
      -- so it certainly dominates the original cutoff at scale `r`.
      have hcutoff_succ_le : cutoff r ≤ cutoff r + 1 := Nat.le_succ _
      have hsum_le : cutoff r + 1 ≤ B r := by
        rw [show B r =
          Finset.sum (Finset.range (r + 1)) (fun i ↦ cutoff i + 1) by rfl, Finset.sum_range_succ]
        simpa [Nat.add_comm] using
          (Nat.le_add_left (Finset.sum (Finset.range r) fun i ↦ cutoff i + 1) (cutoff r + 1))
      exact le_trans hcutoff_succ_le hsum_le
    have hpairAtR :=
      Classical.choose_spec (hpairBudget r (budget r) (hbudget_pos r))
    rcases hpairAtR n (le_trans hcutoff_le hn) with ⟨π, hπ, hmass⟩
    refine ⟨π, hπ, ?_⟩
    simpa [budget] using hmass

/-- Helper for Theorem 17.56: forgetting the unused ambient base point and the duplicated stored
label path in the frozen-label state pair law recovers the canonical label/ambient composition
product. -/
private theorem statePairMap_eq_labelKernelCompProd
    {t : Set (ℕ → unitInterval)} [Fintype t]
    (Plabel : ProbabilityMeasure (ℕ → t))
    (μ0 μ1 : ProbabilityMeasure (ℕ → unitInterval))
    (ρ : (ℕ → unitInterval) → t) (k : ℕ) :
    Measure.map
        (fun z :
          (((ℕ → t) × (ℕ → unitInterval)) × ((ℕ → t) × (ℕ → unitInterval))) ↦
            (z.1.1, z.2.2))
        (((((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ0 ρ 0) :
            Measure ((ℕ → t) × (ℕ → unitInterval))) ⊗ₘ
          frozenLabelStateKernel μ1 ρ k) :
            Measure
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval)))) =
      (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ1 ρ k) :
        Measure ((ℕ → t) × (ℕ → unitInterval))) := by
  let Pbase : Measure ((ℕ → t) × (ℕ → unitInterval)) :=
    (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ0 ρ 0) :
      Measure ((ℕ → t) × (ℕ → unitInterval)))
  let dropRepeatedLabel :
      (((ℕ → t) × (ℕ → unitInterval)) × ((ℕ → t) × (ℕ → unitInterval))) →
        (((ℕ → t) × (ℕ → unitInterval)) × (ℕ → unitInterval)) :=
    fun z ↦ (z.1, z.2.2)
  let projectStatePair :
      (((ℕ → t) × (ℕ → unitInterval)) × (ℕ → unitInterval)) →
        ((ℕ → t) × (ℕ → unitInterval)) :=
    fun z ↦ (z.1.1, z.2)
  -- Local instance justification (kernel): `Measure.compProd_map` needs the output kernel to be
  -- `SFinite`, and the frozen-label kernel is definitionally a product of `SFinite` kernels.
  letI : IsSFiniteKernel (frozenLabelStateKernel μ1 ρ k) := by
    dsimp [frozenLabelStateKernel]
    infer_instance
  have hfactor :
      (fun z :
        (((ℕ → t) × (ℕ → unitInterval)) × ((ℕ → t) × (ℕ → unitInterval))) ↦
          (z.1.1, z.2.2)) =
        projectStatePair ∘ dropRepeatedLabel := by
    funext z
    rfl
  have hdrop :
      Measure.map dropRepeatedLabel
          ((Pbase ⊗ₘ frozenLabelStateKernel μ1 ρ k) :
            Measure
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval)))) =
        Pbase ⊗ₘ (frozenLabelStateKernel μ1 ρ k).map Prod.snd := by
    simpa [dropRepeatedLabel] using
      (Measure.compProd_map
        (μ := Pbase) (κ := frozenLabelStateKernel μ1 ρ k) measurable_snd).symm
  have hproject :
      Measure.map projectStatePair
          (Pbase ⊗ₘ Kernel.comap (normalizedFiberKernelAt μ1 ρ k) Prod.fst measurable_fst) =
        (Measure.map Prod.fst Pbase) ⊗ₘ normalizedFiberKernelAt μ1 ρ k := by
    simpa [projectStatePair] using
      (compProd_map_base_eq_compProd
        (μ := Pbase)
        (f := Prod.fst)
        (hf := measurable_fst)
        (κ := normalizedFiberKernelAt μ1 ρ k))
  -- Proof comment: first discard the duplicated stored label path from the kernel output, then
  -- push the remaining base-label projection through the composition product.
  calc
    Measure.map
        (fun z :
          (((ℕ → t) × (ℕ → unitInterval)) × ((ℕ → t) × (ℕ → unitInterval))) ↦
            (z.1.1, z.2.2))
        ((Pbase ⊗ₘ frozenLabelStateKernel μ1 ρ k) :
          Measure
            (((ℕ → t) × (ℕ → unitInterval)) ×
              ((ℕ → t) × (ℕ → unitInterval)))) =
      Measure.map projectStatePair
        (Measure.map dropRepeatedLabel
          ((Pbase ⊗ₘ frozenLabelStateKernel μ1 ρ k) :
            Measure
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))))) := by
          rw [hfactor, Measure.map_map (by fun_prop) (by fun_prop)]
    _ =
      Measure.map projectStatePair
        (Pbase ⊗ₘ (frozenLabelStateKernel μ1 ρ k).map Prod.snd) := by
          rw [hdrop]
    _ =
      Measure.map projectStatePair
        (Pbase ⊗ₘ Kernel.comap (normalizedFiberKernelAt μ1 ρ k) Prod.fst measurable_fst) := by
          rw [← Kernel.snd_eq, snd_frozenLabelStateKernel]
    _ =
      (Measure.map Prod.fst Pbase) ⊗ₘ normalizedFiberKernelAt μ1 ρ k := by
          rw [hproject]
    _ =
      (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ1 ρ k) :
        Measure ((ℕ → t) × (ℕ → unitInterval))) := by
          rw [fst_compProd_normalizedFiberKernelAt (μ := μ0) (Plabel := Plabel) (ρ := ρ) 0]

private theorem existsAmbientPathLawOfRepresentative
    {t : Set (ℕ → unitInterval)} [Fintype t] [MeasurableEq t]
    {ρ : (ℕ → unitInterval) → t} (hρ_meas : Measurable ρ)
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (PlabelRep : ProbabilityMeasure (ℕ → t))
    (hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t))
    (hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ fun n ↦ ρ (ω n))
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (PlabelRep : Measure (ℕ → t)) := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let μ0 : Measure ((ℕ → t) × (ℕ → unitInterval)) :=
    (((PlabelRep : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt ν ρ 0) :
      Measure ((ℕ → t) × (ℕ → unitInterval)))
  letI : IsProbabilityMeasure μ0 := by
    dsimp [μ0]
    infer_instance
  let κ :
      ℕ → Kernel ((ℕ → t) × (ℕ → unitInterval))
        ((ℕ → t) × (ℕ → unitInterval)) :=
    fun n ↦ frozenLabelStateKernel (νn n) ρ (n + 1)
  have hκMarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    simpa [κ, frozenLabelStateKernel] using
      (inferInstance :
        IsMarkovKernel
          ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ
            Kernel.comap (normalizedFiberKernelAt (νn n) ρ (n + 1))
              Prod.fst measurable_fst))
  letI : ∀ n, IsMarkovKernel (κ n) := hκMarkov
  let PstateMeasure : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))) :=
    headIndexedPathMeasure
      (β := ((ℕ → t) × (ℕ → unitInterval))) μ0 κ
  have hPstateMeasure : IsProbabilityMeasure PstateMeasure := by
    dsimp [PstateMeasure]
    infer_instance
  let Pstate : ProbabilityMeasure (ℕ → ((ℕ → t) × (ℕ → unitInterval))) :=
    ⟨PstateMeasure, hPstateMeasure⟩
  let ambientPath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → (ℕ → unitInterval)) :=
    fun ξ n ↦ (ξ n).2
  have hAmbientPathMeas : Measurable ambientPath := by
    refine measurable_pi_lambda ambientPath ?_
    intro n
    fun_prop
  let Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) :=
    Pstate.map hAmbientPathMeas.aemeasurable
  have hstateHead :
      Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) = μ0 := by
    -- Proof comment: the head-indexed state path starts from the base composition-product law.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedTrajMeasure_map_eval_zero
        (β := ((ℕ → t) × (ℕ → unitInterval))) (μ := μ0) (κ := κ))
  have hstatePair :
      ∀ n : ℕ,
        Measure.map
            (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
          μ0 ⊗ₘ κ n := by
    intro n
    -- Proof comment: every time-`0`/time-`n + 1` state pair is the base law composed with the
    -- corresponding frozen-label transition kernel.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedPathMeasure_map_headAndNext
        (β := ((ℕ → t) × (ℕ → unitInterval))) (μ := μ0) (κ := κ) n)
  have hheadInf :
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) := by
    -- Proof comment: reading the ambient head from the lifted state path is just the second
    -- marginal of the base composition-product law.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ (ξ 0).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map (measurable_pi_apply 0) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
              rw [Measure.map_map measurable_snd (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.snd μ0 := by rw [hstateHead]
      _ = (ν : Measure (ℕ → unitInterval)) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := ν) (ρ := ρ) hρ_meas hheadRep
  have hcoordInf :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval)) := by
    intro n
    -- Proof comment: at time `n + 1`, forget the unused base ambient point and the duplicated
    -- stored label path, then recover the ambient marginal from the normalized-fiber law.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ (ξ (n + 1)).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map (measurable_pi_apply (n + 1)) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1, z.2.2))
            (Measure.map
              (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))) := by
              rw [Measure.map_map measurable_snd (by fun_prop)]
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1, z.2.2))
            (μ0 ⊗ₘ κ n)) := by
              rw [hstatePair n]
      _ =
        Measure.map Prod.snd
          ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
            normalizedFiberKernelAt (νn n) ρ (n + 1)) :
              Measure ((ℕ → t) × (ℕ → unitInterval)))) := by
              rw [statePairMap_eq_labelKernelCompProd
                (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n) (ρ := ρ) (k := n + 1)]
      _ = (νn n : Measure (ℕ → unitInterval)) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := νn n) (ρ := ρ) hρ_meas (hcoordRep n)
  let storedLabelPath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → t) :=
    fun ξ k ↦ (ξ 0).1 k
  let ambientRepresentativePath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → t) :=
    fun ξ k ↦ ρ ((ξ k).2)
  have hstoredLaw :
      Measure.map storedLabelPath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: the stored label path is frozen from time `0`, so its law is exactly the
    -- original representative-label path law.
    calc
      Measure.map storedLabelPath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
        Measure.map Prod.fst
          (Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
              rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.fst μ0 := by rw [hstateHead]
      _ = (PlabelRep : Measure (ℕ → t)) := by
            exact fst_compProd_normalizedFiberKernelAt
              (μ := ν) (Plabel := PlabelRep) (ρ := ρ) 0
  have hdiag :
      ∀ k : ℕ, ∃ μk : Measure t,
        Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ k, ambientRepresentativePath ξ k))
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
          Measure.map (fun a : t ↦ (a, a)) μk := by
    intro k
    cases k with
    | zero =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at time `0`, the base composition-product law already identifies the
        -- stored label and the representative of the sampled ambient point.
        have hcomp :
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ 0, ambientRepresentativePath ξ 0)) =
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2)) ∘
                (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
                (storedLabelPath ξ 0, ambientRepresentativePath ξ 0))
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
            Measure.map (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2))
              (Measure.map
                (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
                  simpa [hcomp] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                      (g := fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2))
                      (f := fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
                      (by fun_prop) (measurable_pi_apply 0)).symm
          _ = Measure.map (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2)) μ0 := by
                rw [hstateHead]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := ν) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := 0) hheadRep
    | succ n =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at later times, the frozen-label state pair still remembers the same
        -- time-`0` label path while the new ambient point is resampled from the matching fiber.
        have hcompHead :
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1))) =
              (fun z :
                (((ℕ → t) × (ℕ → unitInterval)) ×
                  ((ℕ → t) × (ℕ → unitInterval))) ↦
                    (z.1.1 (n + 1), ρ z.2.2)) ∘
                headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n := by
          rfl
        have hcompProject :
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1 (n + 1), ρ z.2.2)) =
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2)) ∘
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2)) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
                (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1)))
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
            Measure.map
              (fun z :
                (((ℕ → t) × (ℕ → unitInterval)) ×
                  ((ℕ → t) × (ℕ → unitInterval))) ↦
                    (z.1.1 (n + 1), ρ z.2.2))
              (Measure.map
                (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
                  simpa [hcompHead] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                      (g := fun z :
                        (((ℕ → t) × (ℕ → unitInterval)) ×
                          ((ℕ → t) × (ℕ → unitInterval))) ↦
                            (z.1.1 (n + 1), ρ z.2.2))
                      (f := headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                      (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2))
                (Measure.map
                  (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                  (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))) := by
                    simpa [hcompProject] using
                      (Measure.map_map
                        (μ := Measure.map
                          (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                        (g := fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
                        (f := fun z :
                          (((ℕ → t) × (ℕ → unitInterval)) ×
                            ((ℕ → t) × (ℕ → unitInterval))) ↦
                              (z.1.1, z.2.2))
                        (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2))
                (μ0 ⊗ₘ κ n)) := by
                    rw [hstatePair n]
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
                normalizedFiberKernelAt (νn n) ρ (n + 1)) :
                  Measure ((ℕ → t) × (ℕ → unitInterval)))) := by
                    rw [statePairMap_eq_labelKernelCompProd
                      (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n) (ρ := ρ)
                      (k := n + 1)]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω (n + 1))
                  (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := νn n) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := n + 1)
                  (hcoordRep n)
  have hlabelAgreement :
      ∀ᵐ ξ ∂(Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))),
        storedLabelPath ξ = ambientRepresentativePath ξ := by
    -- Proof comment: the diagonal pair laws at every coordinate assemble into one almost-sure
    -- equality of the whole stored-label path and the representative path of the ambient sample.
    exact ae_path_eq_of_forall_map_eq_diagonal
      (P := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
      (L := storedLabelPath) (X := ambientRepresentativePath)
      (fun k ↦ by fun_prop) hdiag
  have hlabelAgreementAE :
      storedLabelPath =ᵐ[(Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))]
        ambientRepresentativePath := hlabelAgreement
  let representativePath :
      (ℕ → (ℕ → unitInterval)) → (ℕ → t) :=
    fun ω n ↦ ρ (ω n)
  have hRepresentativePathMeas : Measurable representativePath := by
    refine measurable_pi_lambda representativePath ?_
    intro n
    exact hρ_meas.comp (measurable_pi_apply n)
  have hrepresentativeLaw :
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: mapping the ambient path through `ρ` agrees almost surely with the frozen
    -- stored label path, whose law is exactly `PlabelRep`.
    calc
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map ambientRepresentativePath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map hRepresentativePathMeas hAmbientPathMeas]
            rfl
      _ = Measure.map storedLabelPath
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
              exact Measure.map_congr hlabelAgreementAE.symm
      _ = (PlabelRep : Measure (ℕ → t)) := hstoredLaw
  exact ⟨Pinf, hheadInf, hcoordInf, hrepresentativeLaw⟩

/-- Helper for Theorem 17.56: over an arbitrary ambient space `E`, the frozen representative-state
kernel keeps the stored finite label path fixed and resamples the ambient point from the matching
normalized fiber. -/
private noncomputable def frozenRepresentativeStateKernel
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E] {t : Set E} [Fintype t]
    (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    Kernel ((ℕ → t) × E) ((ℕ → t) × E) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
    Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst

/-- Helper for Theorem 17.56: the generic frozen representative-state kernel preserves the stored
label path as its first marginal. -/
private theorem fst_frozenRepresentativeStateKernel
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E] {t : Set E} [Fintype t]
    (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    Kernel.fst (frozenRepresentativeStateKernel (E := E) μ ρ k) =
      Kernel.deterministic Prod.fst measurable_fst := by
  -- Proof comment: the first factor of the product kernel is already the deterministic stored
  -- label projection, so `Kernel.fst` collapses immediately.
  simpa [frozenRepresentativeStateKernel] using
    (Kernel.fst_prod
      (κ := Kernel.deterministic Prod.fst measurable_fst)
      (η := Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst))

/-- Helper for Theorem 17.56: the second marginal of the generic frozen representative-state
kernel is exactly the normalized-fiber kernel read from the stored label path. -/
private theorem snd_frozenRepresentativeStateKernel
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E] {t : Set E} [Fintype t]
    (μ : ProbabilityMeasure E) (ρ : E → t) (k : ℕ) :
    Kernel.snd (frozenRepresentativeStateKernel (E := E) μ ρ k) =
      Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst := by
  -- Proof comment: the second factor of the product kernel is the only part that resamples the
  -- ambient point, so `Kernel.snd` returns it unchanged.
  simpa [frozenRepresentativeStateKernel] using
    (Kernel.snd_prod
      (κ := Kernel.deterministic Prod.fst measurable_fst)
      (η := Kernel.comap (normalizedFiberKernelAt μ ρ k) Prod.fst measurable_fst))

/-- Helper for Theorem 17.56: for an arbitrary ambient space `E`, forgetting the unused stored
ambient point and the duplicated label path from one frozen-state step recovers the canonical
label/fiber composition product. -/
private theorem statePairMap_eq_labelKernelCompProd_generic
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E] {t : Set E} [Fintype t]
    (Plabel : ProbabilityMeasure (ℕ → t))
    (μ0 μ1 : ProbabilityMeasure E)
    (ρ : E → t) (k : ℕ) :
    Measure.map
        (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
          (z.1.1, z.2.2))
        (((((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ0 ρ 0) :
            Measure ((ℕ → t) × E)) ⊗ₘ
          frozenRepresentativeStateKernel (E := E) μ1 ρ k) :
            Measure (((ℕ → t) × E) × ((ℕ → t) × E))) =
      (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ1 ρ k) :
        Measure ((ℕ → t) × E)) := by
  let Pbase : Measure ((ℕ → t) × E) :=
    (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ0 ρ 0) :
      Measure ((ℕ → t) × E))
  let dropRepeatedLabel :
      (((ℕ → t) × E) × ((ℕ → t) × E)) → (((ℕ → t) × E) × E) :=
    fun z ↦ (z.1, z.2.2)
  let projectStatePair : (((ℕ → t) × E) × E) → ((ℕ → t) × E) :=
    fun z ↦ (z.1.1, z.2)
  -- Local instance justification (kernel): `Measure.compProd_map` needs the output kernel to be
  -- `SFinite`, and the frozen representative-state kernel is definitionally a product of
  -- `SFinite` kernels.
  letI : IsSFiniteKernel (frozenRepresentativeStateKernel (E := E) μ1 ρ k) := by
    dsimp [frozenRepresentativeStateKernel]
    infer_instance
  have hfactor :
      (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2)) =
        projectStatePair ∘ dropRepeatedLabel := by
    funext z
    rfl
  have hdrop :
      Measure.map dropRepeatedLabel
          ((Pbase ⊗ₘ frozenRepresentativeStateKernel (E := E) μ1 ρ k) :
            Measure (((ℕ → t) × E) × ((ℕ → t) × E))) =
        Pbase ⊗ₘ
          (frozenRepresentativeStateKernel (E := E) μ1 ρ k).map Prod.snd := by
    simpa [dropRepeatedLabel] using
      (Measure.compProd_map
        (μ := Pbase)
        (κ := frozenRepresentativeStateKernel (E := E) μ1 ρ k)
        measurable_snd).symm
  have hproject :
      Measure.map projectStatePair
          (Pbase ⊗ₘ Kernel.comap (normalizedFiberKernelAt μ1 ρ k) Prod.fst measurable_fst) =
        (Measure.map Prod.fst Pbase) ⊗ₘ normalizedFiberKernelAt μ1 ρ k := by
    simpa [projectStatePair] using
      (compProd_map_base_eq_compProd
        (μ := Pbase)
        (f := Prod.fst)
        (hf := measurable_fst)
        (κ := normalizedFiberKernelAt μ1 ρ k))
  -- Proof comment: first drop the duplicated stored label path from the kernel output, then push
  -- the remaining base-label projection through the composition product.
  calc
    Measure.map
        (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2))
        ((Pbase ⊗ₘ frozenRepresentativeStateKernel (E := E) μ1 ρ k) :
          Measure (((ℕ → t) × E) × ((ℕ → t) × E))) =
      Measure.map projectStatePair
        (Measure.map dropRepeatedLabel
          ((Pbase ⊗ₘ frozenRepresentativeStateKernel (E := E) μ1 ρ k) :
            Measure (((ℕ → t) × E) × ((ℕ → t) × E)))) := by
          rw [hfactor, Measure.map_map (by fun_prop) (by fun_prop)]
    _ =
      Measure.map projectStatePair
        (Pbase ⊗ₘ
          (frozenRepresentativeStateKernel (E := E) μ1 ρ k).map Prod.snd) := by
          rw [hdrop]
    _ =
      Measure.map projectStatePair
        (Pbase ⊗ₘ Kernel.comap (normalizedFiberKernelAt μ1 ρ k) Prod.fst measurable_fst) := by
          rw [← Kernel.snd_eq, snd_frozenRepresentativeStateKernel (E := E) (μ := μ1)
            (ρ := ρ) (k := k)]
    _ =
      (Measure.map Prod.fst Pbase) ⊗ₘ normalizedFiberKernelAt μ1 ρ k := by
          rw [hproject]
    _ =
      (((Plabel : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt μ1 ρ k) :
        Measure ((ℕ → t) × E)) := by
          rw [fst_compProd_normalizedFiberKernelAt (μ := μ0) (Plabel := Plabel) (ρ := ρ) 0]

/-- Helper for Theorem 17.56: a representative-label path law on any ambient space `E` lifts to
an ambient path law with the exact coordinate marginals while recovering the stored representative
path after applying the representative map coordinatewise. -/
private theorem existsPathLawOfRepresentative
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [Nonempty E]
    {t : Set E} [Fintype t] [MeasurableEq t]
    {ρ : E → t} (hρ_meas : Measurable ρ)
    (ν : ProbabilityMeasure E)
    (νn : ℕ → ProbabilityMeasure E)
    (PlabelRep : ProbabilityMeasure (ℕ → t))
    (hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t))
    (hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → E),
      Measure.map (fun ω : ℕ → E ↦ ω 0) (Pinf : Measure (ℕ → E)) = (ν : Measure E) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → E ↦ ω (n + 1)) (Pinf : Measure (ℕ → E)) =
          (νn n : Measure E)) ∧
      Measure.map (fun ω : ℕ → E ↦ fun n ↦ ρ (ω n)) (Pinf : Measure (ℕ → E)) =
        (PlabelRep : Measure (ℕ → t)) := by
  let μ0 : Measure ((ℕ → t) × E) :=
    (((PlabelRep : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt ν ρ 0) :
      Measure ((ℕ → t) × E))
  letI : IsProbabilityMeasure μ0 := by
    dsimp [μ0]
    infer_instance
  let κ : ℕ → Kernel ((ℕ → t) × E) ((ℕ → t) × E) :=
    fun n ↦ frozenRepresentativeStateKernel (E := E) (νn n) ρ (n + 1)
  have hκMarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    simpa [κ, frozenRepresentativeStateKernel] using
      (inferInstance :
        IsMarkovKernel
          ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ
            Kernel.comap (normalizedFiberKernelAt (νn n) ρ (n + 1))
              Prod.fst measurable_fst))
  letI : ∀ n, IsMarkovKernel (κ n) := hκMarkov
  let PstateMeasure : Measure (ℕ → ((ℕ → t) × E)) :=
    headIndexedPathMeasure (β := ((ℕ → t) × E)) μ0 κ
  have hPstateMeasure : IsProbabilityMeasure PstateMeasure := by
    dsimp [PstateMeasure]
    infer_instance
  let Pstate : ProbabilityMeasure (ℕ → ((ℕ → t) × E)) :=
    ⟨PstateMeasure, hPstateMeasure⟩
  let ambientPath : (ℕ → ((ℕ → t) × E)) → (ℕ → E) := fun ξ n ↦ (ξ n).2
  have hAmbientPathMeas : Measurable ambientPath := by
    refine measurable_pi_lambda ambientPath ?_
    intro n
    fun_prop
  let Pinf : ProbabilityMeasure (ℕ → E) :=
    Pstate.map hAmbientPathMeas.aemeasurable
  have hstateHead :
      Measure.map
          (fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0)
          (Pstate : Measure (ℕ → ((ℕ → t) × E))) = μ0 := by
    -- Proof comment: the head-indexed state path starts from the base composition-product law.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedTrajMeasure_map_eval_zero
        (β := ((ℕ → t) × E)) (μ := μ0) (κ := κ))
  have hstatePair :
      ∀ n : ℕ,
        Measure.map
            (headAndNext (β := ((ℕ → t) × E)) n)
            (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
          μ0 ⊗ₘ κ n := by
    intro n
    -- Proof comment: every time-`0`/time-`n + 1` state pair is the base law composed with the
    -- corresponding frozen representative-state kernel.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedPathMeasure_map_headAndNext
        (β := ((ℕ → t) × E)) (μ := μ0) (κ := κ) n)
  have hheadInf :
      Measure.map (fun ω : ℕ → E ↦ ω 0) (Pinf : Measure (ℕ → E)) = (ν : Measure E) := by
    -- Proof comment: reading the ambient head from the lifted state path is the second marginal
    -- of the base composition-product law.
    calc
      Measure.map (fun ω : ℕ → E ↦ ω 0) (Pinf : Measure (ℕ → E)) =
        Measure.map (fun ξ : ℕ → ((ℕ → t) × E) ↦ (ξ 0).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × E))) := by
            rw [show (Pinf : Measure (ℕ → E)) =
              Measure.map ambientPath (Pstate : Measure (ℕ → ((ℕ → t) × E))) by rfl]
            rw [Measure.map_map (measurable_pi_apply 0) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map (fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × E)))) := by
              rw [Measure.map_map measurable_snd (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.snd μ0 := by rw [hstateHead]
      _ = (ν : Measure E) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := ν) (ρ := ρ) hρ_meas hheadRep
  have hcoordInf :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → E ↦ ω (n + 1)) (Pinf : Measure (ℕ → E)) =
          (νn n : Measure E) := by
    intro n
    -- Proof comment: at time `n + 1`, forget the unused stored ambient point and the duplicated
    -- label path, then recover the ambient marginal from the normalized-fiber law.
    calc
      Measure.map (fun ω : ℕ → E ↦ ω (n + 1)) (Pinf : Measure (ℕ → E)) =
        Measure.map (fun ξ : ℕ → ((ℕ → t) × E) ↦ (ξ (n + 1)).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × E))) := by
            rw [show (Pinf : Measure (ℕ → E)) =
              Measure.map ambientPath (Pstate : Measure (ℕ → ((ℕ → t) × E))) by rfl]
            rw [Measure.map_map (measurable_pi_apply (n + 1)) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2))
            (Measure.map (headAndNext (β := ((ℕ → t) × E)) n)
              (Pstate : Measure (ℕ → ((ℕ → t) × E))))) := by
              rw [Measure.map_map measurable_snd (by fun_prop)]
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2))
            (μ0 ⊗ₘ κ n)) := by
              rw [hstatePair n]
      _ =
        Measure.map Prod.snd
          ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
            normalizedFiberKernelAt (νn n) ρ (n + 1)) :
              Measure ((ℕ → t) × E))) := by
              rw [statePairMap_eq_labelKernelCompProd_generic
                (E := E) (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n)
                (ρ := ρ) (k := n + 1)]
      _ = (νn n : Measure E) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := νn n) (ρ := ρ) hρ_meas (hcoordRep n)
  let storedLabelPath : (ℕ → ((ℕ → t) × E)) → (ℕ → t) := fun ξ k ↦ (ξ 0).1 k
  let ambientRepresentativePath : (ℕ → ((ℕ → t) × E)) → (ℕ → t) :=
    fun ξ k ↦ ρ ((ξ k).2)
  have hstoredLaw :
      Measure.map storedLabelPath (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: the stored label path is frozen from time `0`, so its law is exactly the
    -- original representative-label path law.
    calc
      Measure.map storedLabelPath (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
        Measure.map Prod.fst
          (Measure.map (fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × E)))) := by
              rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.fst μ0 := by rw [hstateHead]
      _ = (PlabelRep : Measure (ℕ → t)) := by
            exact fst_compProd_normalizedFiberKernelAt
              (μ := ν) (Plabel := PlabelRep) (ρ := ρ) 0
  have hdiag :
      ∀ k : ℕ, ∃ μk : Measure t,
        Measure.map
            (fun ξ : ℕ → ((ℕ → t) × E) ↦
              (storedLabelPath ξ k, ambientRepresentativePath ξ k))
            (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
          Measure.map (fun a : t ↦ (a, a)) μk := by
    intro k
    cases k with
    | zero =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at time `0`, the base composition-product law already identifies the
        -- stored label and the representative of the sampled ambient point.
        have hcomp :
            (fun ξ : ℕ → ((ℕ → t) × E) ↦
              (storedLabelPath ξ 0, ambientRepresentativePath ξ 0)) =
              (fun z : (ℕ → t) × E ↦ (z.1 0, ρ z.2)) ∘
                (fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × E) ↦
                (storedLabelPath ξ 0, ambientRepresentativePath ξ 0))
              (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
            Measure.map (fun z : (ℕ → t) × E ↦ (z.1 0, ρ z.2))
              (Measure.map (fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0)
                (Pstate : Measure (ℕ → ((ℕ → t) × E)))) := by
                  simpa [hcomp] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × E))))
                      (g := fun z : (ℕ → t) × E ↦ (z.1 0, ρ z.2))
                      (f := fun ξ : ℕ → ((ℕ → t) × E) ↦ ξ 0)
                      (by fun_prop) (measurable_pi_apply 0)).symm
          _ = Measure.map (fun z : (ℕ → t) × E ↦ (z.1 0, ρ z.2)) μ0 := by
                rw [hstateHead]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := ν) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := 0) hheadRep
    | succ n =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at later times, the frozen representative-state pair still remembers
        -- the time-`0` label path while the ambient point is resampled from the matching fiber.
        have hcompHead :
            (fun ξ : ℕ → ((ℕ → t) × E) ↦
              (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1))) =
              (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
                (z.1.1 (n + 1), ρ z.2.2)) ∘
                headAndNext (β := ((ℕ → t) × E)) n := by
          rfl
        have hcompProject :
            (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
              (z.1.1 (n + 1), ρ z.2.2)) =
              (fun z : (ℕ → t) × E ↦ (z.1 (n + 1), ρ z.2)) ∘
                (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2)) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × E) ↦
                (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1)))
              (Pstate : Measure (ℕ → ((ℕ → t) × E))) =
            Measure.map
              (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
                (z.1.1 (n + 1), ρ z.2.2))
              (Measure.map (headAndNext (β := ((ℕ → t) × E)) n)
                (Pstate : Measure (ℕ → ((ℕ → t) × E)))) := by
                  simpa [hcompHead] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × E))))
                      (g := fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
                        (z.1.1 (n + 1), ρ z.2.2))
                      (f := headAndNext (β := ((ℕ → t) × E)) n)
                      (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × E ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2))
                (Measure.map (headAndNext (β := ((ℕ → t) × E)) n)
                  (Pstate : Measure (ℕ → ((ℕ → t) × E))))) := by
                    simpa [hcompProject] using
                      (Measure.map_map
                        (μ := Measure.map (headAndNext (β := ((ℕ → t) × E)) n)
                          (Pstate : Measure (ℕ → ((ℕ → t) × E))))
                        (g := fun z : (ℕ → t) × E ↦ (z.1 (n + 1), ρ z.2))
                        (f := fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦
                          (z.1.1, z.2.2))
                        (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × E ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z : (((ℕ → t) × E) × ((ℕ → t) × E)) ↦ (z.1.1, z.2.2))
                (μ0 ⊗ₘ κ n)) := by
                    rw [hstatePair n]
          _ = Measure.map
              (fun z : (ℕ → t) × E ↦ (z.1 (n + 1), ρ z.2))
              ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
                normalizedFiberKernelAt (νn n) ρ (n + 1)) :
                  Measure ((ℕ → t) × E))) := by
                    rw [statePairMap_eq_labelKernelCompProd_generic
                      (E := E) (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n)
                      (ρ := ρ) (k := n + 1)]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω (n + 1))
                  (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := νn n) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := n + 1)
                  (hcoordRep n)
  have hlabelAgreement :
      ∀ᵐ ξ ∂(Pstate : Measure (ℕ → ((ℕ → t) × E))),
        storedLabelPath ξ = ambientRepresentativePath ξ := by
    -- Proof comment: the diagonal pair laws at every coordinate assemble into one almost-sure
    -- equality of the whole stored-label path and the representative path of the ambient sample.
    exact ae_path_eq_of_forall_map_eq_diagonal
      (P := (Pstate : Measure (ℕ → ((ℕ → t) × E))))
      (L := storedLabelPath) (X := ambientRepresentativePath)
      (fun k ↦ by fun_prop) hdiag
  have hlabelAgreementAE :
      storedLabelPath =ᵐ[(Pstate : Measure (ℕ → ((ℕ → t) × E)))]
        ambientRepresentativePath := hlabelAgreement
  let representativePath : (ℕ → E) → (ℕ → t) := fun ω n ↦ ρ (ω n)
  have hRepresentativePathMeas : Measurable representativePath := by
    refine measurable_pi_lambda representativePath ?_
    intro n
    exact hρ_meas.comp (measurable_pi_apply n)
  have hrepresentativeLaw :
      Measure.map representativePath (Pinf : Measure (ℕ → E)) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: mapping the ambient path through `ρ` agrees almost surely with the frozen
    -- stored label path, whose law is exactly `PlabelRep`.
    calc
      Measure.map representativePath (Pinf : Measure (ℕ → E)) =
        Measure.map ambientRepresentativePath
          (Pstate : Measure (ℕ → ((ℕ → t) × E))) := by
            rw [show (Pinf : Measure (ℕ → E)) =
              Measure.map ambientPath (Pstate : Measure (ℕ → ((ℕ → t) × E))) by rfl]
            rw [Measure.map_map hRepresentativePathMeas hAmbientPathMeas]
            rfl
      _ = Measure.map storedLabelPath
            (Pstate : Measure (ℕ → ((ℕ → t) × E))) := by
              exact Measure.map_congr hlabelAgreementAE.symm
      _ = (PlabelRep : Measure (ℕ → t)) := hstoredLaw
  exact ⟨Pinf, hheadInf, hcoordInf, hrepresentativeLaw⟩

/-- Helper for Theorem 17.56: one fixed representative-label path law canonically lifts to a
single ambient Hilbert-cube path law with the exact coordinate marginals and the same deterministic
tail cutoff. -/
-- Route correction: a fixed ambient witness is extracted separately below so the final stage
-- family no longer depends on one chosen tail cutoff.
private theorem existsAmbientPathLawOfRepresentativeTail
    {t : Set (ℕ → unitInterval)} [Fintype t] [MeasurableEq t]
    {ρ : (ℕ → unitInterval) → t} (hρ_meas : Measurable ρ)
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (PlabelRep : ProbabilityMeasure (ℕ → t))
    (hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t))
    (hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t))
    {m : ℕ} {ε : ℝ≥0} {N : ℕ}
    (hρ_diam :
      ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m)
    (htailRep :
      (1 : ℝ≥0∞) - ε <
        (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  letI : PseudoMetricSpace (ℕ → unitInterval) := PiCountable.pseudoMetricSpace
  let μ0 : Measure ((ℕ → t) × (ℕ → unitInterval)) :=
    (((PlabelRep : Measure (ℕ → t)) ⊗ₘ normalizedFiberKernelAt ν ρ 0) :
      Measure ((ℕ → t) × (ℕ → unitInterval)))
  letI : IsProbabilityMeasure μ0 := by
    dsimp [μ0]
    infer_instance
  let κ :
      ℕ → Kernel ((ℕ → t) × (ℕ → unitInterval))
        ((ℕ → t) × (ℕ → unitInterval)) :=
    fun n ↦ frozenLabelStateKernel (νn n) ρ (n + 1)
  have hκMarkov : ∀ n, IsMarkovKernel (κ n) := by
    intro n
    simpa [κ, frozenLabelStateKernel] using
      (inferInstance :
        IsMarkovKernel
          ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ
            Kernel.comap (normalizedFiberKernelAt (νn n) ρ (n + 1))
              Prod.fst measurable_fst))
  letI : ∀ n, IsMarkovKernel (κ n) := hκMarkov
  let PstateMeasure : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))) :=
    headIndexedPathMeasure
      (β := ((ℕ → t) × (ℕ → unitInterval))) μ0 κ
  have hPstateMeasure : IsProbabilityMeasure PstateMeasure := by
    dsimp [PstateMeasure]
    infer_instance
  let Pstate : ProbabilityMeasure (ℕ → ((ℕ → t) × (ℕ → unitInterval))) :=
    ⟨PstateMeasure, hPstateMeasure⟩
  let ambientPath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → (ℕ → unitInterval)) :=
    fun ξ n ↦ (ξ n).2
  have hAmbientPathMeas : Measurable ambientPath := by
    refine measurable_pi_lambda ambientPath ?_
    intro n
    fun_prop
  let Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) :=
    Pstate.map hAmbientPathMeas.aemeasurable
  have hstateHead :
      Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) = μ0 := by
    -- Proof comment: the head-indexed state path starts from the base composition-product law.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedTrajMeasure_map_eval_zero
        (β := ((ℕ → t) × (ℕ → unitInterval))) (μ := μ0) (κ := κ))
  have hstatePair :
      ∀ n : ℕ,
        Measure.map
            (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
          μ0 ⊗ₘ κ n := by
    intro n
    -- Proof comment: every time-`0`/time-`n + 1` state pair is the base law composed with the
    -- corresponding frozen-label transition kernel.
    simpa [Pstate, PstateMeasure, μ0, κ] using
      (headIndexedPathMeasure_map_headAndNext
        (β := ((ℕ → t) × (ℕ → unitInterval))) (μ := μ0) (κ := κ) n)
  have hheadInf :
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) := by
    -- Proof comment: reading the ambient head from the lifted state path is just the second
    -- marginal of the base composition-product law.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ (ξ 0).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map (measurable_pi_apply 0) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
              rw [Measure.map_map measurable_snd (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.snd μ0 := by rw [hstateHead]
      _ = (ν : Measure (ℕ → unitInterval)) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := ν) (ρ := ρ) hρ_meas hheadRep
  have hcoordInf :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval)) := by
    intro n
    -- Proof comment: at time `n + 1`, forget the unused base ambient point and the duplicated
    -- stored label path, then recover the ambient marginal from the normalized-fiber law.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map
          (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ (ξ (n + 1)).2)
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map (measurable_pi_apply (n + 1)) hAmbientPathMeas]
            rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1, z.2.2))
            (Measure.map
              (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))) := by
              rw [Measure.map_map measurable_snd (by fun_prop)]
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              rfl
      _ =
        Measure.map Prod.snd
          (Measure.map
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1, z.2.2))
            (μ0 ⊗ₘ κ n)) := by
              rw [hstatePair n]
      _ =
        Measure.map Prod.snd
          ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
            normalizedFiberKernelAt (νn n) ρ (n + 1)) :
              Measure ((ℕ → t) × (ℕ → unitInterval)))) := by
              rw [statePairMap_eq_labelKernelCompProd
                (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n) (ρ := ρ) (k := n + 1)]
      _ = (νn n : Measure (ℕ → unitInterval)) := by
            exact snd_compProd_normalizedFiberKernelAt_eq_of_marginal
              (μ := νn n) (ρ := ρ) hρ_meas (hcoordRep n)
  let storedLabelPath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → t) :=
    fun ξ k ↦ (ξ 0).1 k
  let ambientRepresentativePath :
      (ℕ → ((ℕ → t) × (ℕ → unitInterval))) → (ℕ → t) :=
    fun ξ k ↦ ρ ((ξ k).2)
  have hstoredLabelPathMeas :
      Measurable storedLabelPath := by
    refine measurable_pi_lambda storedLabelPath ?_
    intro k
    fun_prop
  have hambientRepresentativePathMeas :
      Measurable ambientRepresentativePath := by
    refine measurable_pi_lambda ambientRepresentativePath ?_
    intro k
    exact hρ_meas.comp <| measurable_snd.comp (measurable_pi_apply k)
  have hstoredLaw :
      Measure.map storedLabelPath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: the stored label path is frozen from time `0`, so its law is exactly the
    -- original representative-label path law.
    calc
      Measure.map storedLabelPath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
        Measure.map Prod.fst
          (Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
              rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]
              rfl
      _ = Measure.map Prod.fst μ0 := by rw [hstateHead]
      _ = (PlabelRep : Measure (ℕ → t)) := by
            exact fst_compProd_normalizedFiberKernelAt
              (μ := ν) (Plabel := PlabelRep) (ρ := ρ) 0
  have hdiag :
      ∀ k : ℕ, ∃ μk : Measure t,
        Measure.map
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ k, ambientRepresentativePath ξ k))
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
          Measure.map (fun a : t ↦ (a, a)) μk := by
    intro k
    cases k with
    | zero =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at time `0`, the base composition-product law already identifies the
        -- stored label and the representative of the sampled ambient point.
        have hcomp :
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ 0, ambientRepresentativePath ξ 0)) =
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2)) ∘
                (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
                (storedLabelPath ξ 0, ambientRepresentativePath ξ 0))
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
            Measure.map (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2))
              (Measure.map
                (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
                  simpa [hcomp] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                      (g := fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2))
                      (f := fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦ ξ 0)
                      (by fun_prop) (measurable_pi_apply 0)).symm
          _ = Measure.map (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 0, ρ z.2)) μ0 := by
                rw [hstateHead]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := ν) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := 0) hheadRep
    | succ n =>
        refine ⟨Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)), ?_⟩
        -- Proof comment: at later times, the frozen-label state pair still remembers the same
        -- time-`0` label path while the new ambient point is resampled from the matching fiber.
        have hcompHead :
            (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
              (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1))) =
              (fun z :
                (((ℕ → t) × (ℕ → unitInterval)) ×
                  ((ℕ → t) × (ℕ → unitInterval))) ↦
                    (z.1.1 (n + 1), ρ z.2.2)) ∘
                headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n := by
          rfl
        have hcompProject :
            (fun z :
              (((ℕ → t) × (ℕ → unitInterval)) ×
                ((ℕ → t) × (ℕ → unitInterval))) ↦
                  (z.1.1 (n + 1), ρ z.2.2)) =
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2)) ∘
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2)) := by
          rfl
        calc
          Measure.map
              (fun ξ : ℕ → ((ℕ → t) × (ℕ → unitInterval)) ↦
                (storedLabelPath ξ (n + 1), ambientRepresentativePath ξ (n + 1)))
              (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) =
            Measure.map
              (fun z :
                (((ℕ → t) × (ℕ → unitInterval)) ×
                  ((ℕ → t) × (ℕ → unitInterval))) ↦
                    (z.1.1 (n + 1), ρ z.2.2))
              (Measure.map
                (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))) := by
                  simpa [hcompHead] using
                    (Measure.map_map
                      (μ := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                      (g := fun z :
                        (((ℕ → t) × (ℕ → unitInterval)) ×
                          ((ℕ → t) × (ℕ → unitInterval))) ↦
                            (z.1.1 (n + 1), ρ z.2.2))
                      (f := headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                      (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2))
                (Measure.map
                  (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                  (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))) := by
                    simpa [hcompProject] using
                      (Measure.map_map
                        (μ := Measure.map
                          (headAndNext (β := ((ℕ → t) × (ℕ → unitInterval))) n)
                          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
                        (g := fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
                        (f := fun z :
                          (((ℕ → t) × (ℕ → unitInterval)) ×
                            ((ℕ → t) × (ℕ → unitInterval))) ↦
                              (z.1.1, z.2.2))
                        (by fun_prop) (by fun_prop)).symm
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              (Measure.map
                (fun z :
                  (((ℕ → t) × (ℕ → unitInterval)) ×
                    ((ℕ → t) × (ℕ → unitInterval))) ↦
                      (z.1.1, z.2.2))
                (μ0 ⊗ₘ κ n)) := by
                    rw [hstatePair n]
          _ = Measure.map
              (fun z : (ℕ → t) × (ℕ → unitInterval) ↦ (z.1 (n + 1), ρ z.2))
              ((((PlabelRep : Measure (ℕ → t)) ⊗ₘ
                normalizedFiberKernelAt (νn n) ρ (n + 1)) :
                  Measure ((ℕ → t) × (ℕ → unitInterval)))) := by
                    rw [statePairMap_eq_labelKernelCompProd
                      (Plabel := PlabelRep) (μ0 := ν) (μ1 := νn n) (ρ := ρ)
                      (k := n + 1)]
          _ = Measure.map (fun a : t ↦ (a, a))
                (Measure.map (fun ω : ℕ → t ↦ ω (n + 1))
                  (PlabelRep : Measure (ℕ → t))) := by
                exact representativeMap_headAndNext_eq_diagonal_of_frozenLabelState
                  (μ := νn n) (ρ := ρ) hρ_meas (Plabel := PlabelRep) (k := n + 1)
                  (hcoordRep n)
  have hlabelAgreement :
      ∀ᵐ ξ ∂(Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))),
        storedLabelPath ξ = ambientRepresentativePath ξ := by
    -- Proof comment: the diagonal pair laws at every coordinate assemble into one almost-sure
    -- equality of the whole stored-label path and the representative path of the ambient sample.
    exact ae_path_eq_of_forall_map_eq_diagonal
      (P := (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))))
      (L := storedLabelPath) (X := ambientRepresentativePath)
      (fun k ↦ by fun_prop) hdiag
  have hlabelAgreementAE :
      storedLabelPath =ᵐ[(Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval))))]
        ambientRepresentativePath := hlabelAgreement
  let representativePath :
      (ℕ → (ℕ → unitInterval)) → (ℕ → t) :=
    fun ω n ↦ ρ (ω n)
  have hRepresentativePathMeas : Measurable representativePath := by
    refine measurable_pi_lambda representativePath ?_
    intro n
    exact hρ_meas.comp (measurable_pi_apply n)
  have hrepresentativeLaw :
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: mapping the ambient path through `ρ` agrees almost surely with the frozen
    -- stored label path, whose law is exactly `PlabelRep`.
    calc
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map ambientRepresentativePath
          (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
            rw [show (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
              Measure.map ambientPath
                (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) by rfl]
            rw [Measure.map_map hRepresentativePathMeas hAmbientPathMeas]
            rfl
      _ = Measure.map storedLabelPath
            (Pstate : Measure (ℕ → ((ℕ → t) × (ℕ → unitInterval)))) := by
              exact Measure.map_congr hlabelAgreementAE.symm
      _ = (PlabelRep : Measure (ℕ → t)) := hstoredLaw
  have htailRepresentative :
      (1 : ℝ≥0∞) - ε <
        Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (labelTailEvent (α := t) N) := by
    rw [hrepresentativeLaw]
    exact htailRep
  have htailInf :
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
    have hsubset :
        representativePath ⁻¹' labelTailEvent (α := t) N ⊆ dyadicTailEvent m N := by
      intro ω hω
      exact mem_dyadicTailEvent_of_labelTailEvent (ρ := ρ) (m := m) (N := N) hρ_diam hω
    -- Proof comment: once the ambient representative path lies in the label tail event, the
    -- dyadic tail event follows pointwise from the diameter control.
    refine lt_of_lt_of_le htailRepresentative ?_
    calc
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (labelTailEvent (α := t) N) =
        (Pinf : Measure (ℕ → (ℕ → unitInterval)))
          (representativePath ⁻¹' labelTailEvent (α := t) N) := by
            exact Measure.map_apply hRepresentativePathMeas
              (measurableSet_labelTailEvent (α := t) N)
      _ ≤ (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
            exact measure_mono hsubset
  exact ⟨Pinf, hheadInf, hcoordInf, htailInf⟩

/-- Helper for Theorem 17.56: one fixed stage-label path law can be lifted to an ambient
Hilbert-cube path law with the same deterministic tail cutoff at scale `J`. -/
private theorem existsAmbientPathLawOfStageLabelTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N) := by
  classical
  let x0 : ℕ → unitInterval := fun _ ↦ 0
  let used : Set (StageLabel k J) := Set.range (stageLabelMap (k := k) q J)
  let defaultUsed : used := ⟨stageLabelMap (k := k) q J x0, ⟨x0, rfl⟩⟩
  let chooseRepresentative : used → (ℕ → unitInterval) := fun a ↦ Classical.choose a.2
  have hchooseRepresentative :
      ∀ a : used,
        stageLabelMap (k := k) q J (chooseRepresentative a) = a.1 := by
    intro a
    exact Classical.choose_spec a.2
  have hchooseRepresentative_injective :
      Function.Injective chooseRepresentative := by
    intro a b hab
    apply Subtype.ext
    have hqeq := congrArg (stageLabelMap (k := k) q J) hab
    simpa [hchooseRepresentative a, hchooseRepresentative b] using hqeq
  let t : Set (ℕ → unitInterval) := Set.range chooseRepresentative
  letI : Fintype t := Fintype.ofFinite t
  let embedUsed : used → t := fun a ↦ ⟨chooseRepresentative a, ⟨a, rfl⟩⟩
  have hembedUsed_injective : Function.Injective embedUsed := by
    intro a b hab
    apply hchooseRepresentative_injective
    exact Subtype.mk.inj hab
  let labelToRepresentative : StageLabel k J → t := fun a ↦
    if ha : a ∈ used then
      embedUsed ⟨a, ha⟩
    else
      embedUsed defaultUsed
  have hlabelToRepresentative_meas : Measurable labelToRepresentative := by
    exact measurable_of_finite _
  let ρ : (ℕ → unitInterval) → t := fun x ↦
    labelToRepresentative (stageLabelMap (k := k) q J x)
  have hρ_eq :
      ∀ x : ℕ → unitInterval,
        ρ x = embedUsed ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩ := by
    intro x
    simp [ρ, labelToRepresentative, used]
  have hρ_meas : Measurable ρ := by
    exact hlabelToRepresentative_meas.comp
      (measurable_stageLabelMap (k := k) (q := q) hq J)
  have hρ_diam :
      ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J := by
    intro x y hxy
    have husedEq :
        (⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩ : used) =
          ⟨stageLabelMap (k := k) q J y, ⟨y, rfl⟩⟩ := by
      apply hembedUsed_injective
      simpa [hρ_eq x, hρ_eq y] using hxy
    exact hstageDiam (congrArg Subtype.val husedEq)
  let pathToRepresentative : (ℕ → StageLabel k J) → (ℕ → t) := fun ω n ↦
    labelToRepresentative (ω n)
  have hpathToRepresentative_meas : Measurable pathToRepresentative := by
    refine measurable_pi_lambda pathToRepresentative ?_
    intro n
    exact hlabelToRepresentative_meas.comp (measurable_pi_apply n)
  let PlabelRep : ProbabilityMeasure (ℕ → t) :=
    Plabel.map hpathToRepresentative_meas.aemeasurable
  have hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
    -- Proof comment: evaluating the mapped representative path at time `0` simply re-expresses
    -- the given stage-label head law through the chosen finite representative section.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω 0) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω 0)
                (f := pathToRepresentative)
                (measurable_pi_apply 0).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply 0)]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (ν : Measure (ℕ → unitInterval))) := by
              rw [hhead]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
    intro n
    -- Proof comment: the same pushforward normalization works at every later time coordinate.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω (n + 1))
                (f := pathToRepresentative)
                (measurable_pi_apply (n + 1)).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_pi_apply (n + 1))]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have htailRep :
      (1 : ℝ≥0∞) - ε <
        (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
    have hsubset :
        labelTailEvent (α := StageLabel k J) N ⊆
          pathToRepresentative ⁻¹' labelTailEvent (α := t) N := by
      intro ω hω
      intro n hn
      simpa [pathToRepresentative] using congrArg labelToRepresentative (hω n hn)
    calc
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J))
          (labelTailEvent (α := StageLabel k J) N) := htail
      _ ≤ (Plabel : Measure (ℕ → StageLabel k J))
            (pathToRepresentative ⁻¹' labelTailEvent (α := t) N) := by
              exact measure_mono hsubset
      _ = (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
              symm
              exact Measure.map_apply hpathToRepresentative_meas
                (measurableSet_labelTailEvent (α := t) N)
  exact existsAmbientPathLawOfRepresentativeTail
    (t := t) (ρ := ρ) hρ_meas (ν := ν) (νn := νn) (PlabelRep := PlabelRep)
    hheadRep hcoordRep (m := J) (ε := ε) (N := N) hρ_diam htailRep

/-- Helper for Theorem 17.56: one stage-label path law canonically determines a single ambient
Hilbert-cube path law, and every later label-tail cutoff transfers to that fixed ambient law. -/
private theorem existsAmbientPathLawOfStageLabel
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ {ε : ℝ≥0} {N : ℕ},
        (1 : ℝ≥0∞) - ε <
          (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) →
        (1 : ℝ≥0∞) - ε <
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N)) ∧
      (∀ {m : ℕ} (hm : m ≤ J) {ε : ℝ≥0} {N : ℕ},
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) →
        (1 : ℝ≥0∞) - ε <
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) := by
  classical
  let x0 : ℕ → unitInterval := fun _ ↦ 0
  let used : Set (StageLabel k J) := Set.range (stageLabelMap (k := k) q J)
  have hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J := by
    intro x y hxy
    exact hdiam J x y <| by
      simpa using
        congrArg (fun a : StageLabel k J ↦ a ⟨J, Nat.lt_succ_self J⟩) hxy
  let defaultUsed : used := ⟨stageLabelMap (k := k) q J x0, ⟨x0, rfl⟩⟩
  let chooseRepresentative : used → (ℕ → unitInterval) := fun a ↦ Classical.choose a.2
  have hchooseRepresentative :
      ∀ a : used,
        stageLabelMap (k := k) q J (chooseRepresentative a) = a.1 := by
    intro a
    exact Classical.choose_spec a.2
  have hchooseRepresentative_injective :
      Function.Injective chooseRepresentative := by
    intro a b hab
    apply Subtype.ext
    have hqeq := congrArg (stageLabelMap (k := k) q J) hab
    simpa [hchooseRepresentative a, hchooseRepresentative b] using hqeq
  let t : Set (ℕ → unitInterval) := Set.range chooseRepresentative
  letI : Fintype t := Fintype.ofFinite t
  let embedUsed : used → t := fun a ↦ ⟨chooseRepresentative a, ⟨a, rfl⟩⟩
  have hembedUsed_injective : Function.Injective embedUsed := by
    intro a b hab
    apply hchooseRepresentative_injective
    exact Subtype.mk.inj hab
  let labelToRepresentative : StageLabel k J → t := fun a ↦
    if ha : a ∈ used then
      embedUsed ⟨a, ha⟩
    else
      embedUsed defaultUsed
  have hlabelToRepresentative_meas : Measurable labelToRepresentative := by
    exact measurable_of_finite _
  let ρ : (ℕ → unitInterval) → t := fun x ↦
    labelToRepresentative (stageLabelMap (k := k) q J x)
  have hρ_eq :
      ∀ x : ℕ → unitInterval,
        ρ x = embedUsed ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩ := by
    intro x
    simp [ρ, labelToRepresentative, used]
  have hρ_meas : Measurable ρ := by
    exact hlabelToRepresentative_meas.comp
      (measurable_stageLabelMap (k := k) (q := q) hq J)
  have hρ_diam :
      ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J := by
    intro x y hxy
    have husedEq :
        (⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩ : used) =
          ⟨stageLabelMap (k := k) q J y, ⟨y, rfl⟩⟩ := by
      apply hembedUsed_injective
      simpa [hρ_eq x, hρ_eq y] using hxy
    exact hstageDiam (congrArg Subtype.val husedEq)
  let pathToRepresentative : (ℕ → StageLabel k J) → (ℕ → t) := fun ω n ↦
    labelToRepresentative (ω n)
  have hpathToRepresentative_meas : Measurable pathToRepresentative := by
    refine measurable_pi_lambda pathToRepresentative ?_
    intro n
    exact hlabelToRepresentative_meas.comp (measurable_pi_apply n)
  let PlabelRep : ProbabilityMeasure (ℕ → t) :=
    Plabel.map hpathToRepresentative_meas.aemeasurable
  have hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
    -- Proof comment: evaluating the mapped representative path at time `0` simply re-expresses
    -- the given stage-label head law through the chosen finite representative section.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω 0) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω 0)
                (f := pathToRepresentative)
                (measurable_pi_apply 0).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply 0)]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (ν : Measure (ℕ → unitInterval))) := by
              rw [hhead]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
    intro n
    -- Proof comment: the same pushforward normalization works at every later time coordinate.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω (n + 1))
                (f := pathToRepresentative)
                (measurable_pi_apply (n + 1)).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_pi_apply (n + 1))]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  obtain ⟨Pinf, hheadInf, hcoordInf, hrepresentativeLaw⟩ :=
    existsAmbientPathLawOfRepresentative
      (t := t) (ρ := ρ) hρ_meas (ν := ν) (νn := νn) (PlabelRep := PlabelRep)
      hheadRep hcoordRep
  let representativePath : (ℕ → (ℕ → unitInterval)) → (ℕ → t) := fun ω n ↦ ρ (ω n)
  have hRepresentativePathMeas : Measurable representativePath := by
    refine measurable_pi_lambda representativePath ?_
    intro n
    exact hρ_meas.comp (measurable_pi_apply n)
  have htailTransfer :
      ∀ {ε : ℝ≥0} {N : ℕ},
        (1 : ℝ≥0∞) - ε <
          (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) →
        (1 : ℝ≥0∞) - ε <
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N) := by
    intro ε N htail
    have htailRep :
        (1 : ℝ≥0∞) - ε <
          (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
      have hsubset :
          labelTailEvent (α := StageLabel k J) N ⊆
            pathToRepresentative ⁻¹' labelTailEvent (α := t) N := by
        intro ω hω
        intro n hn
        simpa [pathToRepresentative] using congrArg labelToRepresentative (hω n hn)
      calc
        (1 : ℝ≥0∞) - ε <
          (Plabel : Measure (ℕ → StageLabel k J))
            (labelTailEvent (α := StageLabel k J) N) := htail
        _ ≤ (Plabel : Measure (ℕ → StageLabel k J))
              (pathToRepresentative ⁻¹' labelTailEvent (α := t) N) := by
                exact measure_mono hsubset
        _ = (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
                symm
                exact Measure.map_apply hpathToRepresentative_meas
                  (measurableSet_labelTailEvent (α := t) N)
    have htailRepresentative :
        (1 : ℝ≥0∞) - ε <
          Measure.map representativePath
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) (labelTailEvent (α := t) N) := by
      simpa [representativePath] using hrepresentativeLaw ▸ htailRep
    have hsubset :
        representativePath ⁻¹' labelTailEvent (α := t) N ⊆ dyadicTailEvent J N := by
      intro ω hω
      exact mem_dyadicTailEvent_of_labelTailEvent (ρ := ρ) (m := J) (N := N) hρ_diam hω
    refine lt_of_lt_of_le htailRepresentative ?_
    calc
      Measure.map representativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (labelTailEvent (α := t) N) =
        (Pinf : Measure (ℕ → (ℕ → unitInterval)))
          (representativePath ⁻¹' labelTailEvent (α := t) N) := by
            exact Measure.map_apply hRepresentativePathMeas
              (measurableSet_labelTailEvent (α := t) N)
      _ ≤ (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N) := by
            exact measure_mono hsubset
  have hprojectedTailTransfer :
      ∀ {m : ℕ} (hm : m ≤ J) {ε : ℝ≥0} {N : ℕ},
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) →
        (1 : ℝ≥0∞) - ε <
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
    intro m hm ε N htail
    let coarseRepresentative : t → Fin (k m) := fun a ↦ q m a.1
    have hcoarseRepresentative_meas : Measurable coarseRepresentative := by
      exact measurable_of_finite _
    let coarseRepresentativePath : (ℕ → t) → (ℕ → Fin (k m)) := fun ω n ↦
      coarseRepresentative (ω n)
    have hcoarseRepresentativePath_meas : Measurable coarseRepresentativePath := by
      refine measurable_pi_lambda coarseRepresentativePath ?_
      intro n
      exact hcoarseRepresentative_meas.comp (measurable_pi_apply n)
    have hcoarseRepresentative_eq :
        ∀ x : ℕ → unitInterval, coarseRepresentative (ρ x) = q m x := by
      intro x
      have hcoordEq :
          q m (chooseRepresentative
            ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩) =
            q m x := by
        simpa using
          congrArg (fun a : StageLabel k J ↦ a ⟨m, Nat.lt_succ_of_le hm⟩)
            (hchooseRepresentative ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩)
      simpa [coarseRepresentative, ρ, labelToRepresentative, used] using hcoordEq
    have hcoarseRepresentative_diam :
        ∀ ⦃x y : ℕ → unitInterval⦄,
          coarseRepresentative (ρ x) = coarseRepresentative (ρ y) →
            @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
      intro x y hxy
      have hqeq : q m x = q m y := by
        calc
          q m x = coarseRepresentative (ρ x) := (hcoarseRepresentative_eq x).symm
          _ = coarseRepresentative (ρ y) := hxy
          _ = q m y := hcoarseRepresentative_eq y
      exact hdiam m x y hqeq
    have husedMeas : MeasurableSet used := by
      exact Set.toFinite used |>.measurableSet
    have husedCoord :
        ∀ n : ℕ, ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)), ω n ∈ used := by
      intro n
      cases n with
      | zero =>
          have husedProb :
              Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
                  (Plabel : Measure (ℕ → StageLabel k J)) used = 1 := by
            calc
              Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
                  (Plabel : Measure (ℕ → StageLabel k J)) used =
                Measure.map (stageLabelMap (k := k) q J)
                  (ν : Measure (ℕ → unitInterval)) used := by
                    rw [hhead]
              _ = (ν : Measure (ℕ → unitInterval))
                    ((stageLabelMap (k := k) q J) ⁻¹' used) := by
                      rw [Measure.map_apply
                        (measurable_stageLabelMap (k := k) (q := q) hq J) husedMeas]
              _ = 1 := by simp [used]
          have hpreProb :
              (Plabel : Measure (ℕ → StageLabel k J))
                  ((fun ω : ℕ → StageLabel k J ↦ ω 0) ⁻¹' used) = 1 := by
            calc
              (Plabel : Measure (ℕ → StageLabel k J))
                  ((fun ω : ℕ → StageLabel k J ↦ ω 0) ⁻¹' used) =
                Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
                  (Plabel : Measure (ℕ → StageLabel k J)) used := by
                    symm
                    exact Measure.map_apply (measurable_pi_apply 0) husedMeas
              _ = 1 := husedProb
          simpa using
            (mem_ae_iff_prob_eq_one ((measurable_pi_apply 0) husedMeas)).2 hpreProb
      | succ l =>
          have husedProb :
              Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (l + 1))
                  (Plabel : Measure (ℕ → StageLabel k J)) used = 1 := by
            calc
              Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (l + 1))
                  (Plabel : Measure (ℕ → StageLabel k J)) used =
                Measure.map (stageLabelMap (k := k) q J)
                  (νn l : Measure (ℕ → unitInterval)) used := by
                    rw [hcoord l]
              _ = (νn l : Measure (ℕ → unitInterval))
                    ((stageLabelMap (k := k) q J) ⁻¹' used) := by
                      rw [Measure.map_apply
                        (measurable_stageLabelMap (k := k) (q := q) hq J) husedMeas]
              _ = 1 := by simp [used]
          have hpreProb :
              (Plabel : Measure (ℕ → StageLabel k J))
                  ((fun ω : ℕ → StageLabel k J ↦ ω (l + 1)) ⁻¹' used) = 1 := by
            calc
              (Plabel : Measure (ℕ → StageLabel k J))
                  ((fun ω : ℕ → StageLabel k J ↦ ω (l + 1)) ⁻¹' used) =
                Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (l + 1))
                  (Plabel : Measure (ℕ → StageLabel k J)) used := by
                    symm
                    exact Measure.map_apply (measurable_pi_apply (l + 1)) husedMeas
              _ = 1 := husedProb
          simpa using
            (mem_ae_iff_prob_eq_one ((measurable_pi_apply (l + 1)) husedMeas)).2 hpreProb
    have husedAll :
        ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)), ∀ n : ℕ, ω n ∈ used := by
      exact ae_all_iff.2 husedCoord
    have hcoarseRepresentative_used :
        ∀ {a : StageLabel k J}, a ∈ used →
          coarseRepresentative (labelToRepresentative a) = a ⟨m, Nat.lt_succ_of_le hm⟩ := by
      intro a ha
      rcases ha with ⟨x, rfl⟩
      have hcoordEq :
          q m (chooseRepresentative
            ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩) =
            q m x := by
        simpa using
          congrArg (fun b : StageLabel k J ↦ b ⟨m, Nat.lt_succ_of_le hm⟩)
            (hchooseRepresentative ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩)
      simpa [coarseRepresentative, labelToRepresentative, used] using hcoordEq
    have hcoarsePathEq :
        (fun ω : ℕ → StageLabel k J ↦
          coarseRepresentativePath (pathToRepresentative ω)) =ᵐ[
            (Plabel : Measure (ℕ → StageLabel k J))]
          projectStageLabelPath (k := k) (J := J) (m := m) hm := by
      filter_upwards [husedAll] with ω hω
      funext n
      simpa [coarseRepresentativePath, pathToRepresentative, projectStageLabelPath] using
        hcoarseRepresentative_used (a := ω n) (hω n)
    have hcoarseRepLaw :
        Measure.map coarseRepresentativePath
            (PlabelRep : Measure (ℕ → t)) =
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
            Measure (ℕ → Fin (k m))) := by
      calc
        Measure.map coarseRepresentativePath
            (PlabelRep : Measure (ℕ → t)) =
          Measure.map (coarseRepresentativePath ∘ pathToRepresentative)
            (Plabel : Measure (ℕ → StageLabel k J)) := by
              simpa [PlabelRep] using
                (Measure.map_map hcoarseRepresentativePath_meas hpathToRepresentative_meas)
        _ = Measure.map (projectStageLabelPath (k := k) (J := J) (m := m) hm)
              (Plabel : Measure (ℕ → StageLabel k J)) := by
                exact Measure.map_congr hcoarsePathEq
        _ =
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
            Measure (ℕ → Fin (k m))) := by
              rfl
    let coarseAmbientRepresentativePath :
        (ℕ → (ℕ → unitInterval)) → (ℕ → Fin (k m)) := fun ω n ↦
      coarseRepresentative (representativePath ω n)
    have hcoarseAmbientRepresentativePath_meas :
        Measurable coarseAmbientRepresentativePath := by
      refine measurable_pi_lambda coarseAmbientRepresentativePath ?_
      intro n
      exact hcoarseRepresentative_meas.comp <|
        (measurable_pi_apply n).comp hRepresentativePathMeas
    have hcoarseAmbientLaw :
        Measure.map coarseAmbientRepresentativePath
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          Measure.map coarseRepresentativePath
            (PlabelRep : Measure (ℕ → t)) := by
      calc
        Measure.map coarseAmbientRepresentativePath
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          Measure.map coarseRepresentativePath
            (Measure.map representativePath
              (Pinf : Measure (ℕ → (ℕ → unitInterval)))) := by
                rw [Measure.map_map hcoarseRepresentativePath_meas hRepresentativePathMeas]
                rfl
        _ = Measure.map coarseRepresentativePath
              (PlabelRep : Measure (ℕ → t)) := by
                rw [hrepresentativeLaw]
    have htailRepresentative :
        (1 : ℝ≥0∞) - ε <
          Measure.map coarseAmbientRepresentativePath
            (Pinf : Measure (ℕ → (ℕ → unitInterval)))
              (labelTailEvent (α := Fin (k m)) N) := by
      calc
        (1 : ℝ≥0∞) - ε <
          (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
            Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N) := htail
        _ =
          Measure.map coarseRepresentativePath
            (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := Fin (k m)) N) := by
              rw [hcoarseRepLaw]
        _ =
          Measure.map coarseAmbientRepresentativePath
            (Pinf : Measure (ℕ → (ℕ → unitInterval)))
              (labelTailEvent (α := Fin (k m)) N) := by
                rw [← hcoarseAmbientLaw]
    have hsubset :
        coarseAmbientRepresentativePath ⁻¹' labelTailEvent (α := Fin (k m)) N ⊆
          dyadicTailEvent m N := by
      intro ω hω
      exact mem_dyadicTailEvent_of_labelTailEvent
        (ρ := fun x ↦ coarseRepresentative (ρ x))
        (m := m) (N := N) hcoarseRepresentative_diam hω
    refine lt_of_lt_of_le htailRepresentative ?_
    calc
      Measure.map coarseAmbientRepresentativePath
          (Pinf : Measure (ℕ → (ℕ → unitInterval)))
            (labelTailEvent (α := Fin (k m)) N) =
        (Pinf : Measure (ℕ → (ℕ → unitInterval)))
          (coarseAmbientRepresentativePath ⁻¹' labelTailEvent (α := Fin (k m)) N) := by
            exact Measure.map_apply hcoarseAmbientRepresentativePath_meas
              (measurableSet_labelTailEvent (α := Fin (k m)) N)
      _ ≤ (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
            exact measure_mono hsubset
  exact ⟨Pinf, hheadInf, hcoordInf,
    fun {ε} {N} htail ↦ htailTransfer htail,
    fun {m} hm {ε} {N} htail ↦ hprojectedTailTransfer hm htail⟩

/-- Helper for Theorem 17.56: package the fixed ambient witness from
`existsAmbientPathLawOfStageLabel` as a named probability law. -/
private noncomputable def ambientStageLabelPathLaw
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i) :
    ProbabilityMeasure (ℕ → (ℕ → unitInterval)) :=
  Classical.choose <|
    existsAmbientPathLawOfStageLabel
      (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel hhead hcoord hdiam

/-- Helper for Theorem 17.56: the fixed ambient stage witness has the exact time-`0` marginal
prescribed by the stage-label input law. -/
private theorem ambientStageLabelPathLaw_head
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i) :
    Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
        (ambientStageLabelPathLaw
          (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
          hhead hcoord hdiam :
            Measure (ℕ → (ℕ → unitInterval))) =
      (ν : Measure (ℕ → unitInterval)) := by
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabel
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam).1

/-- Helper for Theorem 17.56: the fixed ambient stage witness preserves every exact coordinate
marginal from the stage-label input law. -/
private theorem ambientStageLabelPathLaw_coord
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i) :
    ∀ n : ℕ,
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (ambientStageLabelPathLaw
            (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
            hhead hcoord hdiam :
              Measure (ℕ → (ℕ → unitInterval))) =
        (νn n : Measure (ℕ → unitInterval)) := by
  intro n
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabel
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam).2.1 n

/-- Helper for Theorem 17.56: every stage-label tail cutoff transfers to the same fixed ambient
stage witness, rather than forcing a fresh existential witness for each cutoff. -/
private theorem ambientStageLabelPathLaw_dyadicTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    (1 : ℝ≥0∞) - ε <
      (ambientStageLabelPathLaw
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam :
          Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N) := by
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabel
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam).2.2.1 htail

/-- Helper for Theorem 17.56: every coarse projected stage-label tail cutoff also transfers to
the same fixed ambient stage witness, with no need to rebuild a separate ambient law. -/
private theorem ambientStageLabelPathLaw_projected_dyadicTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    {m : ℕ} (hm : m ≤ J) {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm Plabel :
          Measure (ℕ → Fin (k m))) (labelTailEvent (α := Fin (k m)) N)) :
    (1 : ℝ≥0∞) - ε <
      (ambientStageLabelPathLaw
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam :
          Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  -- Proof comment: the fourth component of the fixed ambient witness specification records the
  -- coarse projected tail-transfer statement directly.
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabel
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hdiam).2.2.2 hm htail

/-- Helper for Theorem 17.56: the ambient representative-lift construction can be chosen so that
mapping the ambient witness back through the stage quantizer exactly recovers the prescribed
stage-label path law. -/
private theorem existsAmbientPathLawOfStageLabelWithRecovery
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      Measure.map (stageLabelPathMap (k := k) (q := q) J)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (Plabel : Measure (ℕ → StageLabel k J)) := by
  classical
  let x0 : ℕ → unitInterval := fun _ ↦ 0
  let used : Set (StageLabel k J) := Set.range (stageLabelMap (k := k) q J)
  let defaultUsed : used := ⟨stageLabelMap (k := k) q J x0, ⟨x0, rfl⟩⟩
  let chooseRepresentative : used → (ℕ → unitInterval) := fun a ↦ Classical.choose a.2
  have hchooseRepresentative :
      ∀ a : used,
        stageLabelMap (k := k) q J (chooseRepresentative a) = a.1 := by
    intro a
    exact Classical.choose_spec a.2
  have hchooseRepresentative_injective :
      Function.Injective chooseRepresentative := by
    intro a b hab
    apply Subtype.ext
    have hqeq := congrArg (stageLabelMap (k := k) q J) hab
    simpa [hchooseRepresentative a, hchooseRepresentative b] using hqeq
  let t : Set (ℕ → unitInterval) := Set.range chooseRepresentative
  letI : Fintype t := Fintype.ofFinite t
  let embedUsed : used → t := fun a ↦ ⟨chooseRepresentative a, ⟨a, rfl⟩⟩
  have hembedUsed_injective : Function.Injective embedUsed := by
    intro a b hab
    apply hchooseRepresentative_injective
    exact Subtype.mk.inj hab
  let labelToRepresentative : StageLabel k J → t := fun a ↦
    if ha : a ∈ used then
      embedUsed ⟨a, ha⟩
    else
      embedUsed defaultUsed
  have hlabelToRepresentative_meas : Measurable labelToRepresentative := by
    exact measurable_of_finite _
  let ρ : (ℕ → unitInterval) → t := fun x ↦
    labelToRepresentative (stageLabelMap (k := k) q J x)
  have hρ_eq :
      ∀ x : ℕ → unitInterval,
        ρ x = embedUsed ⟨stageLabelMap (k := k) q J x, ⟨x, rfl⟩⟩ := by
    intro x
    simp [ρ, labelToRepresentative, used]
  have hρ_meas : Measurable ρ := by
    exact hlabelToRepresentative_meas.comp
      (measurable_stageLabelMap (k := k) (q := q) hq J)
  let pathToRepresentative : (ℕ → StageLabel k J) → (ℕ → t) := fun ω n ↦
    labelToRepresentative (ω n)
  have hpathToRepresentative_meas : Measurable pathToRepresentative := by
    refine measurable_pi_lambda pathToRepresentative ?_
    intro n
    exact hlabelToRepresentative_meas.comp (measurable_pi_apply n)
  let PlabelRep : ProbabilityMeasure (ℕ → t) :=
    Plabel.map hpathToRepresentative_meas.aemeasurable
  have hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
    -- Proof comment: rewrite the head marginal of the representative path law through the
    -- original stage-label head marginal and the chosen representative section.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω 0) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω 0)
                (f := pathToRepresentative)
                (measurable_pi_apply 0).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply 0)]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (ν : Measure (ℕ → unitInterval))) := by
              rw [hhead]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
    intro n
    -- Proof comment: the same representative pushforward normalization works at every later
    -- time coordinate.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → StageLabel k J)))
                (g := fun ω : ℕ → t ↦ ω (n + 1))
                (f := pathToRepresentative)
                (measurable_pi_apply (n + 1)).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (Plabel : Measure (ℕ → StageLabel k J))) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_pi_apply (n + 1))]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map (stageLabelMap (k := k) q J)
              (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (labelToRepresentative ∘ stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  obtain ⟨Pinf, hheadInf, hcoordInf, hrepresentativeLaw⟩ :=
    existsAmbientPathLawOfRepresentative
      (t := t) (ρ := ρ) hρ_meas (ν := ν) (νn := νn) (PlabelRep := PlabelRep)
      hheadRep hcoordRep
  let representativeToLabel : t → StageLabel k J := fun a ↦ stageLabelMap (k := k) q J a.1
  have hrepresentativeToLabel_meas : Measurable representativeToLabel := by
    exact measurable_of_finite _
  let representativeToLabelPath : (ℕ → t) → (ℕ → StageLabel k J) := fun ω n ↦
    representativeToLabel (ω n)
  have hrepresentativeToLabelPath_meas : Measurable representativeToLabelPath := by
    refine measurable_pi_lambda representativeToLabelPath ?_
    intro n
    exact hrepresentativeToLabel_meas.comp (measurable_pi_apply n)
  have hrepresentativeToLabel_embedUsed :
      ∀ a : used, representativeToLabel (embedUsed a) = a.1 := by
    intro a
    simpa [representativeToLabel, embedUsed] using hchooseRepresentative a
  have husedMeas : MeasurableSet used := by
    exact (Set.toFinite used).measurableSet
  have husedCoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω n)
            (Plabel : Measure (ℕ → StageLabel k J)) used = 1 := by
    intro n
    cases n with
    | zero =>
        calc
          Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (Plabel : Measure (ℕ → StageLabel k J)) used =
            Measure.map (stageLabelMap (k := k) q J)
              (ν : Measure (ℕ → unitInterval)) used := by
                rw [hhead]
          _ = 1 := by
                rw [Measure.map_apply
                  (measurable_stageLabelMap (k := k) (q := q) hq J) husedMeas]
                simp [used]
    | succ n =>
        calc
          Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (Plabel : Measure (ℕ → StageLabel k J)) used =
            Measure.map (stageLabelMap (k := k) q J)
              (νn n : Measure (ℕ → unitInterval)) used := by
                rw [hcoord n]
          _ = 1 := by
                rw [Measure.map_apply
                  (measurable_stageLabelMap (k := k) (q := q) hq J) husedMeas]
                simp [used]
  have husedAE :
      ∀ n : ℕ, ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)), ω n ∈ used := by
    intro n
    have hpre :
        (Plabel : Measure (ℕ → StageLabel k J))
          ((fun ω : ℕ → StageLabel k J ↦ ω n) ⁻¹' used) = 1 := by
      rw [← Measure.map_apply (measurable_pi_apply n) husedMeas]
      exact husedCoord n
    exact (MeasureTheory.mem_ae_iff_prob_eq_one
      ((measurable_pi_apply n) husedMeas)).2 hpre
  have husedPathAE :
      ∀ᵐ ω ∂(Plabel : Measure (ℕ → StageLabel k J)), ∀ n : ℕ, ω n ∈ used := by
    exact ae_all_iff.2 husedAE
  have hpathRecoveryAE :
      representativeToLabelPath ∘ pathToRepresentative =ᵐ[(Plabel : Measure (ℕ → StageLabel k J))]
        id := by
    -- Proof comment: the representative encoding is injective on the stage labels that actually
    -- occur under `Plabel`, because every coordinate lies in the quantizer image almost surely.
    filter_upwards [husedPathAE] with ω hω
    funext n
    have hωn : ω n ∈ used := hω n
    have hlabel :
        labelToRepresentative (ω n) = embedUsed ⟨ω n, hωn⟩ := by
      simp [labelToRepresentative, hωn]
    calc
      representativeToLabelPath (pathToRepresentative ω) n =
        representativeToLabel (labelToRepresentative (ω n)) := rfl
      _ = representativeToLabel (embedUsed ⟨ω n, hωn⟩) := by rw [hlabel]
      _ = ω n := by
            simpa using hrepresentativeToLabel_embedUsed ⟨ω n, hωn⟩
  have hPlabelRecovery :
      Measure.map representativeToLabelPath (PlabelRep : Measure (ℕ → t)) =
        (Plabel : Measure (ℕ → StageLabel k J)) := by
    -- Proof comment: map the representative path law back through the chosen section and use the
    -- almost-sure left-inverse relation on the support of `Plabel`.
    calc
      Measure.map representativeToLabelPath (PlabelRep : Measure (ℕ → t)) =
        Measure.map representativeToLabelPath
          (Measure.map pathToRepresentative (Plabel : Measure (ℕ → StageLabel k J))) := by
            rfl
      _ = Measure.map (representativeToLabelPath ∘ pathToRepresentative)
            (Plabel : Measure (ℕ → StageLabel k J)) := by
              rw [Measure.map_map hrepresentativeToLabelPath_meas hpathToRepresentative_meas]
      _ = Measure.map id (Plabel : Measure (ℕ → StageLabel k J)) := by
            exact Measure.map_congr hpathRecoveryAE
      _ = (Plabel : Measure (ℕ → StageLabel k J)) := by simp
  have hstageLabelPathMap_eq :
      representativeToLabelPath ∘ (fun ω : ℕ → (ℕ → unitInterval) ↦ fun n ↦ ρ (ω n)) =
        stageLabelPathMap (k := k) (q := q) J := by
    -- Proof comment: decoding the representative path of an ambient trajectory is pointwise the
    -- same as applying the bundled stage quantizer coordinatewise.
    funext ω n
    have hρω :
        ρ (ω n) = embedUsed ⟨stageLabelMap (k := k) q J (ω n), ⟨ω n, rfl⟩⟩ := hρ_eq (ω n)
    calc
      representativeToLabelPath (fun m ↦ ρ (ω m)) n =
        representativeToLabel (ρ (ω n)) := rfl
      _ = representativeToLabel
            (embedUsed ⟨stageLabelMap (k := k) q J (ω n), ⟨ω n, rfl⟩⟩) := by
              rw [hρω]
      _ = stageLabelMap (k := k) q J (ω n) := by
            simpa using hrepresentativeToLabel_embedUsed
              ⟨stageLabelMap (k := k) q J (ω n), ⟨ω n, rfl⟩⟩
  have hstageRecovery :
      Measure.map (stageLabelPathMap (k := k) (q := q) J)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (Plabel : Measure (ℕ → StageLabel k J)) := by
    -- Proof comment: first map the ambient path to its representative path law, then decode that
    -- representative path back to the original stage-label law.
    calc
      Measure.map (stageLabelPathMap (k := k) (q := q) J)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        Measure.map
          (representativeToLabelPath ∘
            (fun ω : ℕ → (ℕ → unitInterval) ↦ fun n ↦ ρ (ω n)))
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) := by
            rw [hstageLabelPathMap_eq]
      _ = Measure.map representativeToLabelPath
            (Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ fun n ↦ ρ (ω n))
              (Pinf : Measure (ℕ → (ℕ → unitInterval)))) := by
              symm
              exact Measure.map_map hrepresentativeToLabelPath_meas <| by
                refine measurable_pi_lambda _ ?_
                intro n
                exact hρ_meas.comp (measurable_pi_apply n)
      _ = Measure.map representativeToLabelPath (PlabelRep : Measure (ℕ → t)) := by
            rw [hrepresentativeLaw]
      _ = (Plabel : Measure (ℕ → StageLabel k J)) := hPlabelRecovery
  exact ⟨Pinf, hheadInf, hcoordInf, hstageRecovery⟩

/-- Helper for Theorem 17.56: package the single-scale ambient witness from
`existsAmbientPathLawOfStageLabelTail` as a named probability law. -/
private noncomputable def ambientStageLabelPathLawOfTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    ProbabilityMeasure (ℕ → (ℕ → unitInterval)) :=
  Classical.choose <|
    existsAmbientPathLawOfStageLabelTail
      (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
      hhead hcoord hstageDiam (ε := ε) (N := N) htail

/-- Helper for Theorem 17.56: the packaged ambient single-scale witness has the exact time-`0`
marginal prescribed by the stage-label input law. -/
private theorem ambientStageLabelPathLawOfTail_head
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
        (ambientStageLabelPathLawOfTail
          (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
          hhead hcoord hstageDiam htail :
            Measure (ℕ → (ℕ → unitInterval))) =
      (ν : Measure (ℕ → unitInterval)) := by
  -- Proof comment: `ambientStageLabelPathLawOfTail` is defined by choosing the ambient witness
  -- from `existsAmbientPathLawOfStageLabelTail`, so its head law is the first component of that
  -- packaged specification.
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabelTail
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hstageDiam (ε := ε) (N := N) htail).1

/-- Helper for Theorem 17.56: the packaged ambient single-scale witness preserves every exact
coordinate marginal from the stage-label input law. -/
private theorem ambientStageLabelPathLawOfTail_coord
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    ∀ n : ℕ,
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (ambientStageLabelPathLawOfTail
            (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
            hhead hcoord hstageDiam htail :
              Measure (ℕ → (ℕ → unitInterval))) =
        (νn n : Measure (ℕ → unitInterval)) := by
  intro n
  -- Proof comment: the chosen witness carries the whole coordinate-law package, so every time
  -- `n + 1` marginal is read off from the second component of `choose_spec`.
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabelTail
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hstageDiam (ε := ε) (N := N) htail).2.1 n

/-- Helper for Theorem 17.56: the packaged ambient single-scale witness carries the same dyadic
tail cutoff as the stage-label input law. -/
private theorem ambientStageLabelPathLawOfTail_dyadicTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    (hstageDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q J x = stageLabelMap (k := k) q J y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ J)
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N)) :
    (1 : ℝ≥0∞) - ε <
      (ambientStageLabelPathLawOfTail
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hstageDiam htail :
          Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent J N) := by
  -- Proof comment: the third component of the same `choose_spec` record is the transported
  -- dyadic tail estimate for the ambient law.
  exact
    (Classical.choose_spec <|
      existsAmbientPathLawOfStageLabelTail
        (ν := ν) (νn := νn) (k := k) (q := q) hq J Plabel
        hhead hcoord hstageDiam (ε := ε) (N := N) htail).2.2

/-- Helper for Theorem 17.56: one fixed coarse-label path law with a deterministic label-tail
cutoff lifts directly to an ambient Hilbert-cube path law with the same dyadic cutoff. -/
private theorem existsAmbientPathLawOfCoarseLabelTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ} {q : (ℕ → unitInterval) → Fin k}
    (hq : Measurable q)
    (Plabel : ProbabilityMeasure (ℕ → Fin k))
    (hhead :
      Measure.map (fun ω : ℕ → Fin k ↦ ω 0)
          (Plabel : Measure (ℕ → Fin k)) =
        Measure.map q (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → Fin k ↦ ω (n + 1))
            (Plabel : Measure (ℕ → Fin k)) =
          Measure.map q (νn n : Measure (ℕ → unitInterval)))
    {m : ℕ} {ε : ℝ≥0} {N : ℕ}
    (hdiam :
      ∀ ⦃x y : ℕ → unitInterval⦄, q x = q y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m)
    (htail :
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → Fin k)) (labelTailEvent (α := Fin k) N)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  classical
  let x0 : ℕ → unitInterval := fun _ ↦ 0
  let used : Set (Fin k) := Set.range q
  let defaultUsed : used := ⟨q x0, ⟨x0, rfl⟩⟩
  let chooseRepresentative : used → (ℕ → unitInterval) := fun a ↦ Classical.choose a.2
  have hchooseRepresentative :
      ∀ a : used, q (chooseRepresentative a) = a.1 := by
    intro a
    exact Classical.choose_spec a.2
  have hchooseRepresentative_injective : Function.Injective chooseRepresentative := by
    intro a b hab
    apply Subtype.ext
    have hqeq := congrArg q hab
    simpa [hchooseRepresentative a, hchooseRepresentative b] using hqeq
  let t : Set (ℕ → unitInterval) := Set.range chooseRepresentative
  letI : Fintype t := Fintype.ofFinite t
  let embedUsed : used → t := fun a ↦ ⟨chooseRepresentative a, ⟨a, rfl⟩⟩
  have hembedUsed_injective : Function.Injective embedUsed := by
    intro a b hab
    apply hchooseRepresentative_injective
    exact Subtype.mk.inj hab
  let labelToRepresentative : Fin k → t := fun a ↦
    if ha : a ∈ used then
      embedUsed ⟨a, ha⟩
    else
      embedUsed defaultUsed
  have hlabelToRepresentative_meas : Measurable labelToRepresentative := by
    exact measurable_of_finite _
  let ρ : (ℕ → unitInterval) → t := fun x ↦ labelToRepresentative (q x)
  have hρ_eq :
      ∀ x : ℕ → unitInterval, ρ x = embedUsed ⟨q x, ⟨x, rfl⟩⟩ := by
    intro x
    simp [ρ, labelToRepresentative, used]
  have hρ_meas : Measurable ρ := by
    exact hlabelToRepresentative_meas.comp hq
  have hρ_diam :
      ∀ ⦃x y : ℕ → unitInterval⦄, ρ x = ρ y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
    intro x y hxy
    have husedEq :
        (⟨q x, ⟨x, rfl⟩⟩ : used) =
          ⟨q y, ⟨y, rfl⟩⟩ := by
      apply hembedUsed_injective
      simpa [hρ_eq x, hρ_eq y] using hxy
    exact hdiam (congrArg Subtype.val husedEq)
  let pathToRepresentative : (ℕ → Fin k) → (ℕ → t) := fun ω n ↦
    labelToRepresentative (ω n)
  have hpathToRepresentative_meas : Measurable pathToRepresentative := by
    refine measurable_pi_lambda pathToRepresentative ?_
    intro n
    exact hlabelToRepresentative_meas.comp (measurable_pi_apply n)
  let PlabelRep : ProbabilityMeasure (ℕ → t) :=
    Plabel.map hpathToRepresentative_meas.aemeasurable
  have hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
    -- Proof comment: evaluating the representative path at time `0` simply re-expresses the
    -- coarse-label head law through the chosen representative section.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω 0) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → Fin k)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → Fin k)))
                (g := fun ω : ℕ → t ↦ ω 0)
                (f := pathToRepresentative)
                (measurable_pi_apply 0).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → Fin k ↦ ω 0) (Plabel : Measure (ℕ → Fin k))) := by
              rw [Measure.map_map hlabelToRepresentative_meas (measurable_pi_apply 0)]
              rfl
      _ = Measure.map labelToRepresentative (Measure.map q (ν : Measure (ℕ → unitInterval))) := by
              rw [hhead]
      _ = Measure.map (labelToRepresentative ∘ q) (ν : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas hq]
      _ = ((representativeMapLaw ν hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
    intro n
    -- Proof comment: the same representative pushforward normalization works at every later
    -- coordinate `n + 1`.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
        Measure.map ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ pathToRepresentative)
          (Plabel : Measure (ℕ → Fin k)) := by
            simpa [PlabelRep] using
              (AEMeasurable.map_map_of_aemeasurable
                (μ := (Plabel : Measure (ℕ → Fin k)))
                (g := fun ω : ℕ → t ↦ ω (n + 1))
                (f := pathToRepresentative)
                (measurable_pi_apply (n + 1)).aemeasurable
                hpathToRepresentative_meas.aemeasurable)
      _ = Measure.map labelToRepresentative
            (Measure.map (fun ω : ℕ → Fin k ↦ ω (n + 1)) (Plabel : Measure (ℕ → Fin k))) := by
              rw [Measure.map_map hlabelToRepresentative_meas
                (measurable_pi_apply (n + 1))]
              rfl
      _ = Measure.map labelToRepresentative
            (Measure.map q (νn n : Measure (ℕ → unitInterval))) := by
              rw [hcoord n]
      _ = Measure.map (labelToRepresentative ∘ q) (νn n : Measure (ℕ → unitInterval)) := by
              rw [Measure.map_map hlabelToRepresentative_meas hq]
      _ = ((representativeMapLaw (νn n) hρ_meas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have htailRep :
      (1 : ℝ≥0∞) - ε <
        (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
    have hsubset :
        labelTailEvent (α := Fin k) N ⊆
          pathToRepresentative ⁻¹' labelTailEvent (α := t) N := by
      intro ω hω
      intro n hn
      simpa [pathToRepresentative] using congrArg labelToRepresentative (hω n hn)
    calc
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → Fin k)) (labelTailEvent (α := Fin k) N) := htail
      _ ≤ (Plabel : Measure (ℕ → Fin k))
            (pathToRepresentative ⁻¹' labelTailEvent (α := t) N) := by
              exact measure_mono hsubset
      _ = (PlabelRep : Measure (ℕ → t)) (labelTailEvent (α := t) N) := by
              symm
              exact Measure.map_apply hpathToRepresentative_meas
                (measurableSet_labelTailEvent (α := t) N)
  exact existsAmbientPathLawOfRepresentativeTail
    (t := t) (ρ := ρ) hρ_meas (ν := ν) (νn := νn) (PlabelRep := PlabelRep)
    hheadRep hcoordRep (m := m) (ε := ε) (N := N) hρ_diam htailRep

/-- Helper for Theorem 17.56: if a stage-`J` label path law has a deterministic coarse tail
cutoff after projecting to coordinate `m ≤ J`, then its ambient lift has the corresponding dyadic
tail cutoff at scale `m`. -/
private theorem existsAmbientPathLawOfProjectedStageLabelTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    {J m : ℕ} (hm : m ≤ J)
    (Plabel : ProbabilityMeasure (ℕ → StageLabel k J))
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)))
    (hcoord :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)))
    {ε : ℝ≥0} {N : ℕ}
    (htail :
      (1 : ℝ≥0∞) - ε <
        ((((Plabel.map
          (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable) :
            ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m)))
          (labelTailEvent (α := Fin (k m)) N))) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  let Pcoarse : ProbabilityMeasure (ℕ → Fin (k m)) :=
    Plabel.map
      (measurable_projectStageLabelPath (k := k) (J := J) (m := m) hm).aemeasurable
  have hcoarseMarginals :=
    projectStageLabelPath_probabilityMap_marginals
      (k := k) (q := q) hq hm ν νn Plabel hhead hcoord
  have hcoarseDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄, q m x = q m y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
    intro x y hxy
    exact hdiam m x y hxy
  -- Proof comment: once the projected coarse-label path law has the correct marginals, the
  -- dedicated coarse ambient-lift theorem turns its deterministic label cutoff into the target
  -- dyadic cutoff.
  rcases hcoarseMarginals with ⟨hheadCoarse, hcoordCoarse⟩
  exact existsAmbientPathLawOfCoarseLabelTail
    (ν := ν) (νn := νn) (q := q m) (hq := hq m) (Plabel := Pcoarse)
    hheadCoarse hcoordCoarse (m := m) (ε := ε) (N := N) hcoarseDiam htail

/-- Helper for Theorem 17.56: a deterministic top-stage label-tail cutoff already yields the same
dyadic cutoff at any earlier scale after truncating away the unused finer stage coordinates. -/
private theorem existsAmbientPathLawOfStageLabelPrefixTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    {m M : ℕ} (hm : m ≤ M)
    (PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M))
    (hheadTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)))
    (hcoordTop :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval)))
    {ε : ℝ≥0} {N : ℕ}
    (htailTop :
      (1 : ℝ≥0∞) - ε <
        (PlabelTop : Measure (ℕ → StageLabel k M))
          (labelTailEvent (α := StageLabel k M) N)) :
    ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  rcases existsStageLabelPrefixLawWithTailCutoff
      ν νn (hq := hq) hm PlabelTop hheadTop hcoordTop htailTop with
    ⟨PlabelCoarse, hheadCoarse, hcoordCoarse, htailCoarse⟩
  have hcoarseDiam :
      ∀ ⦃x y : ℕ → unitInterval⦄,
        stageLabelMap (k := k) q m x = stageLabelMap (k := k) q m y →
          @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ m := by
    intro x y hxy
    exact hdiam m x y <| by
      simpa using congrArg (fun a : StageLabel k m ↦ a ⟨m, Nat.lt_succ_self m⟩) hxy
  -- Proof comment: after truncating down to the coarse stage `m`, the existing ambient lift for
  -- a fixed stage law turns the preserved label-tail cutoff into the desired dyadic cutoff.
  exact existsAmbientPathLawOfStageLabelTail
    (ν := ν) (νn := νn) (k := k) (q := q) hq m PlabelCoarse
    hheadCoarse hcoordCoarse hcoarseDiam htailCoarse

/-- Helper for Theorem 17.56: projecting the chosen bundled stage-label path law to a coarse
coordinate `m ≤ J` keeps the exact coarse marginals and the almost-sure eventual equality event. -/
private theorem projectedChosenStageLabelPathLaw_spec
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {J m : ℕ} (hm : m ≤ J) :
    Measure.map (fun ω : ℕ → Fin (k m) ↦ ω 0)
        ((projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm
          (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) :
            ProbabilityMeasure (ℕ → Fin (k m))) :
          Measure (ℕ → Fin (k m))) =
      Measure.map (q m) (ν : Measure (ℕ → unitInterval)) ∧
    (∀ n : ℕ,
      Measure.map (fun ω : ℕ → Fin (k m) ↦ ω (n + 1))
          ((projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm
            (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) :
              ProbabilityMeasure (ℕ → Fin (k m))) :
            Measure (ℕ → Fin (k m))) =
        Measure.map (q m) (νn n : Measure (ℕ → unitInterval))) ∧
    (∀ᵐ ω ∂((projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm
        (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) :
          ProbabilityMeasure (ℕ → Fin (k m))) : Measure (ℕ → Fin (k m))),
      ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let PlabelJ : ProbabilityMeasure (ℕ → StageLabel k J) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J
  have hPlabelJ :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (PlabelJ : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelJ : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelJ : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: unfold the chosen stage law only once so the coarse projection proof can
    -- reuse the packaged exact marginals and eventual equality event.
    simpa [PlabelJ] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier J
  have hmarginals :=
    projectStageLabelPath_probabilityMap_marginals
      (k := k) (q := q) hq hm ν νn PlabelJ hPlabelJ.1 hPlabelJ.2.1
  have hevent :=
    ae_eventuallyEq_projectStageLabelPath_of_ae_eventuallyEq
      (k := k) (J := J) (m := m) hm (Plabel := PlabelJ) hPlabelJ.2.2
  -- Proof comment: the coarse path law is just the fixed-coordinate image of `PlabelJ`, so its
  -- head/coordinate marginals and eventual equality are inherited from the stage law directly.
  exact ⟨hmarginals.1, hmarginals.2, hevent⟩

/-- Helper for Theorem 17.56: for a fixed chosen stage law and a fixed coarse scale `m ≤ J`, one
can already build an ambient Hilbert-cube path law with exact marginals and one dyadic tail
cutoff at scale `m`. -/
private theorem existsAmbientPathLawOfChosenProjectedStageTail
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    {J m : ℕ} (hm : m ≤ J) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N) := by
  let PlabelJ : ProbabilityMeasure (ℕ → StageLabel k J) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J
  have hPlabelJ :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (PlabelJ : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelJ : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelJ : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: keep the chosen stage law in one named spelling so the ambient single-scale
    -- lift can consume its exact marginal package without re-expanding `Classical.choose`.
    simpa [PlabelJ] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier J
  have hprojected :=
    projectedChosenStageLabelPathLaw_spec
      ν νn hνn hk hq hfrontier hm
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := Fin (k m))
      (P := projectedStageLabelPathLaw (k := k) (J := J) (m := m) hm PlabelJ)
      hprojected.2.2 ε hε
  -- Proof comment: once the chosen stage law has a deterministic coarse cutoff at scale `m`, the
  -- existing projected-stage ambient lift turns it into the desired dyadic cutoff.
  rcases existsAmbientPathLawOfProjectedStageLabelTail
      (ν := ν) (νn := νn) (k := k) (q := q) hq hdiam hm PlabelJ
      hPlabelJ.1 hPlabelJ.2.1 (ε := ε) (N := N) hN with
    ⟨Pinf, hheadInf, hcoordInf, htailInf⟩
  exact ⟨N, Pinf, hheadInf, hcoordInf, htailInf⟩

/-- Helper for Theorem 17.56: every chosen bundled stage-label path law already has one
deterministic high-probability label-tail cutoff. -/
private theorem existsChosenStageLabelPathLaw_tailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (J : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ,
      (1 : ℝ≥0∞) - ε <
        (chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J :
          Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) := by
  let PlabelJ : ProbabilityMeasure (ℕ → StageLabel k J) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J
  have hPlabelJ :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (PlabelJ : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelJ : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelJ : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: expose the chosen stage law's packaged eventual-equality event once, then
    -- feed it directly to the generic deterministic cutoff lemma.
    simpa [PlabelJ] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier J
  exact exists_labelTailEvent_highProb_of_ae_eventuallyEq
    (α := StageLabel k J) (P := PlabelJ) hPlabelJ.2.2 ε hε

/-- Helper for Theorem 17.56: truncating the chosen top-stage law down to any earlier stage keeps
the exact prefix marginals and one deterministic tail cutoff from the top stage. -/
private theorem existsChosenStageLabelPrefixLawWithTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {J M : ℕ} (hJM : J ≤ M) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ Plabel : ProbabilityMeasure (ℕ → StageLabel k J),
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (Plabel : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (Plabel : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))) ∧
      (1 : ℝ≥0∞) - ε <
        (Plabel : Measure (ℕ → StageLabel k J)) (labelTailEvent (α := StageLabel k J) N) := by
  let PlabelTop : ProbabilityMeasure (ℕ → StageLabel k M) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier M
  have hPlabelTop :
      Measure.map (fun ω : ℕ → StageLabel k M ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k M)) =
        Measure.map (stageLabelMap (k := k) q M) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k M ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k M)) =
          Measure.map (stageLabelMap (k := k) q M) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelTop : Measure (ℕ → StageLabel k M)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: keep the top-stage witness in one spelling so the prefix extraction only
    -- needs the canonical exact-marginal package.
    simpa [PlabelTop] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier M
  obtain ⟨N, hN⟩ :=
    existsChosenStageLabelPathLaw_tailCutoff
      ν νn hνn hk hq hfrontier M hε
  rcases existsStageLabelPrefixLawWithTailCutoff
      ν νn (hq := hq) hJM PlabelTop hPlabelTop.1 hPlabelTop.2.1 hN with
    ⟨Plabel, hhead, hcoord, htail⟩
  -- Proof comment: the finite prefix-chain API now turns the chosen top-stage cutoff into a
  -- lower-stage witness without changing the shared deterministic threshold.
  exact ⟨N, Plabel, hhead, hcoord, htail⟩

/-- Helper for Theorem 17.56: any single Hilbert-cube realization with exact coordinate laws and
almost-sure dyadic control already yields a constant approximate stage family. -/
private theorem existsApproximateHilbertCubeStageFamily_of_realization.{w}
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval)) :
    (∃ (Ω : Type w) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m)) →
    ∃ Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
          (1 : ℝ≥0∞) - ε <
            (Pstage J : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) := by
  intro hreal
  rcases hreal with ⟨Ω, mΩ, P, Y, Yn, hY, hYn, hevent⟩
  let Z : Ω → ℕ → (ℕ → unitInterval) := fun ω n ↦
    match n with
    | 0 => Y ω
    | l + 1 => Yn l ω
  let hZ : AEMeasurable Z (P : Measure Ω) := by
    -- Proof comment: every path coordinate is one of the already-controlled random variables
    -- `Y` or `Yn l`, so `aemeasurable_pi_lambda` packages them into one path-valued map.
    refine aemeasurable_pi_lambda Z ?_
    intro n
    cases n with
    | zero =>
        simpa [Z] using hY.aemeasurable
    | succ l =>
        simpa [Z] using (hYn l).aemeasurable
  let Ppath : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) := P.map hZ
  have hpathEvent :
      ∀ m : ℕ, ∀ᵐ ω ∂(Ppath : Measure (ℕ → (ℕ → unitInterval))),
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
            (1 / 2 : ℝ) ^ m := by
    intro m
    let hEventMeas :
        MeasurableSet {ω : ℕ → (ℕ → unitInterval) |
          ∀ᶠ n : ℕ in atTop,
            @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
              (1 / 2 : ℝ) ^ m} := by
      have hrewrite :
          {ω : ℕ → (ℕ → unitInterval) |
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
                (1 / 2 : ℝ) ^ m} =
            ⋃ N : ℕ, dyadicTailEvent m N := by
        ext ω
        simp [dyadicTailEvent, Filter.eventually_atTop]
      rw [hrewrite]
      exact MeasurableSet.iUnion fun N ↦ (isClosed_dyadicTailEvent m N).measurableSet
    -- Proof comment: transport the almost-sure dyadic control from the original realization to
    -- the packaged path law `Ppath`.
    exact (MeasureTheory.ae_map_iff hZ hEventMeas).2 <| by
      simpa [Z] using hevent m
  refine ⟨fun _ ↦ Ppath, ?_⟩
  constructor
  · intro J
    -- Proof comment: the constant stage family keeps the exact time-`0` law because `Z 0 = Y`.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Ppath : Measure (ℕ → (ℕ → unitInterval))) =
          Measure.map ((fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0) ∘ Z)
            (P : Measure Ω) := by
              simpa [Ppath] using
                (AEMeasurable.map_map_of_aemeasurable
                  (μ := (P : Measure Ω))
                  (g := fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0) (f := Z)
                  (measurable_pi_apply 0).aemeasurable hZ)
      _ = (ν : Measure (ℕ → unitInterval)) := by
            simpa [Function.comp, Z] using hY.map_eq
  constructor
  · intro n J hn
    -- Proof comment: the same path map stores `Yn n` at time `n + 1`, so every stage inherits
    -- the required `n`th coordinate law; the side condition `n ≤ J` is unused for the constant
    -- family but preserved to match the target API.
    calc
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Ppath : Measure (ℕ → (ℕ → unitInterval))) =
          Measure.map ((fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1)) ∘ Z)
            (P : Measure Ω) := by
              simpa [Ppath] using
                (AEMeasurable.map_map_of_aemeasurable
                  (μ := (P : Measure Ω))
                  (g := fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1)) (f := Z)
                  (measurable_pi_apply (n + 1)).aemeasurable hZ)
      _ = (νn n : Measure (ℕ → unitInterval)) := by
            simpa [Function.comp, Z] using (hYn n).map_eq
  · intro m ε hε
    obtain ⟨N, hN⟩ :=
      exists_dyadicTailEvent_highProb_of_ae_eventuallyDistLe
        (P := Ppath) (m := m) (hpathEvent m) ε hε
    -- Proof comment: once one deterministic dyadic cutoff works for the single path law `Ppath`,
    -- it works eventually for the constant family by trivial eventual constancy.
    exact ⟨N, Filter.Eventually.of_forall fun J ↦ hN⟩

/-- Helper for Theorem 17.56: metric convergence already gives eventual dyadic distance bounds at
every fixed scale. -/
private theorem eventuallyDyadicDistLe_of_tendsto
    {α : Type*} [MetricSpace α] {f : ℕ → α} {x : α}
    (h : Tendsto f atTop (𝓝 x)) :
    ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, dist (f n) x ≤ (1 / 2 : ℝ) ^ m := by
  intro m
  have hpos : 0 < (1 / 2 : ℝ) ^ m := by
    positivity
  -- Proof comment: `Metric.tendsto_atTop` gives the strict dyadic bound, and `≤` is the
  -- monotone closure needed by the downstream tail-event API.
  rcases Metric.tendsto_atTop.1 h ((1 / 2 : ℝ) ^ m) hpos with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ le_of_lt (hN n hn)⟩

/-- Helper for Theorem 17.56: almost-sure metric convergence upgrades scale by scale to the
eventual dyadic bounds consumed by the stage-family constructor. -/
private theorem aeEventuallyDyadicDistLe_of_aeTendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {Y : Ω → ℕ → unitInterval} {Yn : ℕ → Ω → ℕ → unitInterval}
    (h :
      ∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω))) :
    ∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
      ∀ᶠ n : ℕ in atTop,
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
          (1 / 2 : ℝ) ^ m := by
  intro m
  -- Proof comment: after fixing the dyadic scale, the pointwise metric adapter can be lifted
  -- through the almost-sure convergence event by a single `filter_upwards`.
  filter_upwards [h] with ω hω
  exact eventuallyDyadicDistLe_of_tendsto hω m

/-- Helper for Theorem 17.56: dyadic eventual distance bounds at every scale already force
metric convergence. -/
private theorem tendsto_of_forall_dyadic_eventually_dist_le
    {α : Type*} [PseudoMetricSpace α] {f : ℕ → α} {x : α}
    (h :
      ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, dist (f n) x ≤ (1 / 2 : ℝ) ^ m) :
    Tendsto f atTop (𝓝 x) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hpow :
      Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hsmall :
      ∀ᶠ m : ℕ in atTop, (1 / 2 : ℝ) ^ m < ε := by
    exact hpow (Iio_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hsmall with ⟨m, hm⟩
  have hmε : (1 / 2 : ℝ) ^ m < ε := hm m le_rfl
  -- Proof comment: once one dyadic radius lies below `ε`, the corresponding eventual dyadic
  -- bound upgrades directly to the metric neighborhood bound required for convergence.
  filter_upwards [h m] with n hn
  exact lt_of_le_of_lt hn hmε

/-- Helper for Theorem 17.56: almost-sure dyadic eventual distance bounds at every scale already
upgrade to almost-sure metric convergence. -/
private theorem aeTendsto_of_forall_dyadic_eventually_dist_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℕ → unitInterval} {Yn : ℕ → Ω → ℕ → unitInterval}
    (h :
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
            (1 / 2 : ℝ) ^ m) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω)) := by
  -- Proof comment: `ae_all_iff` packages the scale-wise dyadic bounds pointwise, so the
  -- generic dyadic-to-metric convergence bridge can close the result pathwise.
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact tendsto_of_forall_dyadic_eventually_dist_le hω

/-- Helper for Theorem 17.56: any direct Hilbert-cube realization with almost-sure metric
convergence can be repackaged into the dyadic eventual form used by the compact-core consumer. -/
private theorem existsHilbertCubeDirectDyadicRealization_of_aeTendsto.{w}
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval)) :
    (∃ (Ω : Type w) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω)))) →
    ∃ (Ω : Type w) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  intro hreal
  rcases hreal with ⟨Ω, mΩ, P, Y, Yn, hY, hYn, hTendsto⟩
  refine ⟨Ω, mΩ, P, Y, Yn, hY, hYn, ?_⟩
  -- Proof comment: the only additional work beyond a direct Skorohod realization is to replace
  -- almost-sure metric convergence by the scale-wise dyadic eventual bounds consumed later.
  exact aeEventuallyDyadicDistLe_of_aeTendsto hTendsto

/-- Helper for Theorem 17.56: a direct Hilbert-cube realization with almost-sure metric
convergence already implies the approximate stage family consumed by the compactness step. -/
private theorem existsApproximateHilbertCubeStageFamily_of_aeTendsto.{w}
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval)) :
    (∃ (Ω : Type w) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω)))) →
    ∃ Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
          (1 : ℝ≥0∞) - ε <
            (Pstage J : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) := by
  intro hreal
  -- Proof comment: first normalize the direct realization into the dyadic eventual form already
  -- consumed by the constant-family constructor, then reuse that constructor verbatim.
  exact existsApproximateHilbertCubeStageFamily_of_realization ν νn <|
    existsHilbertCubeDirectDyadicRealization_of_aeTendsto ν νn hreal

/-- Helper for Theorem 17.56: a single summable family of Hilbert-cube pair couplings already
produces the direct almost-sure realization needed by the approximate-stage constructor. -/
private theorem existsHilbertCubeDirectRealization_of_summablePairLaws
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hpair :
      ∃ π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
        (∀ n : ℕ, IsCoupling (π n) ν (νn n)) ∧
          (∀ m : ℕ,
            (∑' n,
              ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                {z | (1 / 2 : ℝ) ^ m <
                    @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2})) ≠ ∞)) :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Yn n ω) atTop (𝓝 (Y ω))) := by
  rcases hpair with ⟨π, hπ, hbad⟩
  have hfst :
      ∀ n : ℕ,
        Measure.map Prod.fst
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (ν : Measure (ℕ → unitInterval)) := by
    intro n
    exact (hπ n).1
  have hsnd :
      ∀ n : ℕ,
        Measure.map Prod.snd
            (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval)) := by
    intro n
    exact (hπ n).2
  rcases existsHilbertCubeDyadicTailRealizationOfSummablePairLaws ν νn π hfst hsnd hbad with
    ⟨Ω, mΩ, P, Y, Yn, hY, hYn, hdyadic⟩
  refine ⟨Ω, mΩ, P, Y, Yn, hY, hYn, ?_⟩
  -- Proof comment: the owner dyadic realization theorem already gives the scale-wise eventual
  -- bounds, so only the generic dyadic-to-metric bridge remains.
  exact aeTendsto_of_forall_dyadic_eventually_dist_le hdyadic

/-- Helper for Theorem 17.56: the compatible-prefix compactness extractor can also expose the
subsequence that converges to the limiting stage family at each fixed stage. -/
private theorem existsCompatibleStageLabelFamily_ofPrefixRectanglesWithSubseq
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (fallback : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hprefixRect :
      ∀ M : ℕ,
        ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
          (∀ J : Fin (M + 1),
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (ν : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin (M + 1), ∀ n : ℕ,
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (νn n : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin M,
            PlabelRect ⟨J.1, Nat.lt_succ_of_lt J.2⟩ =
              (PlabelRect ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩).map
                (measurable_stageLabelTruncatePath (k := k) J.1).aemeasurable)) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ J : ℕ,
        Tendsto
          (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose (hprefixRect (φ n))) ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              fallback J)
          atTop (𝓝 (PlabelStage J))) ∧
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  classical
  let familySeq : ℕ → ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J) := fun M J ↦
    if hJ : J ≤ M then
      (Classical.choose (hprefixRect M)) ⟨J, Nat.lt_succ_of_le hJ⟩
    else
      fallback J
  letI : CompactSpace (∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J)) := inferInstance
  obtain ⟨PlabelStage, φ, hφmono, hφtendsto⟩ := CompactSpace.tendsto_subseq familySeq
  refine ⟨PlabelStage, φ, hφmono, ?_, ?_, ?_, ?_⟩
  · intro J
    -- Proof comment: the product-space compactness subsequence converges coordinatewise, and
    -- here the coordinate is exactly the stage-`J` law needed later for Portmanteau arguments.
    simpa [familySeq, Function.comp] using
      (continuous_apply J).continuousAt.tendsto.comp hφtendsto
  · intro J
    let target : ProbabilityMeasure (StageLabel k J) :=
      ν.map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
    have hstageTendsto :
        Tendsto (fun n ↦ familySeq (φ n) J) atTop (𝓝 (PlabelStage J)) := by
      -- Proof comment: convergence in the product family space is coordinatewise convergence of
      -- the stage laws.
      simpa [Function.comp] using
        (continuous_apply J).continuousAt.tendsto.comp hφtendsto
    have hmapTendsto :
        Tendsto
          (fun n ↦
            (familySeq (φ n) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω 0)
              (continuous_apply 0).measurable.aemeasurable)
          atTop
          (𝓝
            ((PlabelStage J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω 0)
              (continuous_apply 0).measurable.aemeasurable)) := by
      simpa using
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun n ↦ familySeq (φ n) J) (PlabelStage J) hstageTendsto (continuous_apply 0)
    have hconst :
        ∀ᶠ n : ℕ in atTop,
          (familySeq (φ n) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω 0)
              (continuous_apply 0).measurable.aemeasurable =
            target := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨J, fun n hn ↦ ?_⟩
      have hle : J ≤ φ n := le_trans hn (StrictMono.id_le hφmono n)
      have hheadRect :=
        (Classical.choose_spec (hprefixRect (φ n))).1 ⟨J, Nat.lt_succ_of_le hle⟩
      have hheadEq :
          Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
              (familySeq (φ n) J : Measure (ℕ → StageLabel k J)) =
            (target : Measure (StageLabel k J)) := by
        simpa [familySeq, target, hle] using hheadRect
      exact probabilityMeasureMap_eq_of_measureMap_eq
        (hf := (continuous_apply 0).measurable.aemeasurable) hheadEq
    have hconstTendsto :
        Tendsto
          (fun n ↦
            (familySeq (φ n) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω 0)
              (continuous_apply 0).measurable.aemeasurable)
          atTop (𝓝 target) := by
      refine tendsto_const_nhds.congr' ?_
      exact hconst.mono fun n hn ↦ hn.symm
    have hEq :
        (PlabelStage J).map
            (f := fun ω : ℕ → StageLabel k J ↦ ω 0)
            (continuous_apply 0).measurable.aemeasurable =
          target := by
      exact tendsto_nhds_unique hmapTendsto hconstTendsto
    simpa [target] using
      congrArg
        (fun ρ : ProbabilityMeasure (StageLabel k J) ↦
          (ρ : Measure (StageLabel k J))) hEq
  · intro J n
    let target : ProbabilityMeasure (StageLabel k J) :=
      (νn n).map ((measurable_stageLabelMap (k := k) (q := q) hq J).aemeasurable)
    have hstageTendsto :
        Tendsto (fun l ↦ familySeq (φ l) J) atTop (𝓝 (PlabelStage J)) := by
      -- Proof comment: the coordinate projection of the compactness subsequence converges at each
      -- fixed stage `J`.
      simpa [Function.comp] using
        (continuous_apply J).continuousAt.tendsto.comp hφtendsto
    have hmapTendsto :
        Tendsto
          (fun l ↦
            (familySeq (φ l) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (continuous_apply (n + 1)).measurable.aemeasurable)
          atTop
          (𝓝
            ((PlabelStage J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (continuous_apply (n + 1)).measurable.aemeasurable)) := by
      simpa using
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun l ↦ familySeq (φ l) J) (PlabelStage J) hstageTendsto
          (continuous_apply (n + 1))
    have hconst :
        ∀ᶠ l : ℕ in atTop,
          (familySeq (φ l) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (continuous_apply (n + 1)).measurable.aemeasurable =
            target := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨J, fun l hl ↦ ?_⟩
      have hle : J ≤ φ l := le_trans hl (StrictMono.id_le hφmono l)
      have hcoordRect :=
        (Classical.choose_spec (hprefixRect (φ l))).2.1
          ⟨J, Nat.lt_succ_of_le hle⟩ n
      have hcoordEq :
          Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (familySeq (φ l) J : Measure (ℕ → StageLabel k J)) =
            (target : Measure (StageLabel k J)) := by
        simpa [familySeq, target, hle] using hcoordRect
      exact probabilityMeasureMap_eq_of_measureMap_eq
        (hf := (continuous_apply (n + 1)).measurable.aemeasurable) hcoordEq
    have hconstTendsto :
        Tendsto
          (fun l ↦
            (familySeq (φ l) J).map
              (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
              (continuous_apply (n + 1)).measurable.aemeasurable)
          atTop (𝓝 target) := by
      refine tendsto_const_nhds.congr' ?_
      exact hconst.mono fun l hl ↦ hl.symm
    have hEq :
        (PlabelStage J).map
            (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (continuous_apply (n + 1)).measurable.aemeasurable =
          target := by
      exact tendsto_nhds_unique hmapTendsto hconstTendsto
    simpa [target] using
      congrArg
        (fun ρ : ProbabilityMeasure (StageLabel k J) ↦
          (ρ : Measure (StageLabel k J))) hEq
  · intro J
    have hstageTendsto :
        Tendsto (fun n ↦ familySeq (φ n) J) atTop (𝓝 (PlabelStage J)) := by
      -- Proof comment: the compactness subsequence converges coordinatewise at every fixed stage.
      simpa [Function.comp] using
        (continuous_apply J).continuousAt.tendsto.comp hφtendsto
    have hsuccTendsto :
        Tendsto (fun n ↦ familySeq (φ n) (J + 1)) atTop (𝓝 (PlabelStage (J + 1))) := by
      simpa [Function.comp] using
        (continuous_apply (J + 1)).continuousAt.tendsto.comp hφtendsto
    have hcontTruncate :
        Continuous (stageLabelTruncatePath (k := k) J) := by
      -- Proof comment: stage truncation is coordinatewise and the target stage alphabet is
      -- finite discrete, so continuity is pointwise automatic.
      refine continuous_pi fun n ↦ ?_
      have hcontStageTruncate : Continuous (stageLabelTruncate (k := k) J) :=
        continuous_of_discreteTopology
      simpa [stageLabelTruncatePath] using
        hcontStageTruncate.comp (continuous_apply n)
    have hmapTendsto :
        Tendsto
          (fun n ↦
            (familySeq (φ n) (J + 1)).map
              (f := stageLabelTruncatePath (k := k) J)
              hcontTruncate.measurable.aemeasurable)
          atTop
          (𝓝
            ((PlabelStage (J + 1)).map
              (f := stageLabelTruncatePath (k := k) J)
              hcontTruncate.measurable.aemeasurable)) := by
      simpa using
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
          (fun n ↦ familySeq (φ n) (J + 1)) (PlabelStage (J + 1)) hsuccTendsto
          hcontTruncate
    have heqEvent :
        ∀ᶠ n : ℕ in atTop,
          familySeq (φ n) J =
            (familySeq (φ n) (J + 1)).map
              (measurable_stageLabelTruncatePath (k := k) J).aemeasurable := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨J + 1, fun n hn ↦ ?_⟩
      have hleSucc : J + 1 ≤ φ n := le_trans hn (StrictMono.id_le hφmono n)
      have hlt : J < φ n := Nat.lt_of_lt_of_le (Nat.lt_succ_self J) hleSucc
      have hle : J ≤ φ n := Nat.le_of_lt hlt
      have hcompatRect :=
        (Classical.choose_spec (hprefixRect (φ n))).2.2 ⟨J, hlt⟩
      simpa [familySeq, hle, hleSucc] using hcompatRect
    have hmapTendsto' :
        Tendsto
          (fun n ↦ familySeq (φ n) J)
          atTop
          (𝓝
            ((PlabelStage (J + 1)).map
              (f := stageLabelTruncatePath (k := k) J)
              hcontTruncate.measurable.aemeasurable)) := by
      refine hmapTendsto.congr' ?_
      exact heqEvent.mono fun n hn ↦ hn.symm
    exact tendsto_nhds_unique hstageTendsto hmapTendsto'

/-- Helper for Theorem 17.56: compatible finite prefix rectangles with exact bundled marginals
admit one global compatible stage-label family, extracted by compactness on the product family
space. -/
private theorem existsCompatibleStageLabelFamily_ofPrefixRectangles
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (fallback : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J))
    (hprefixRect :
      ∀ M : ℕ,
        ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
          (∀ J : Fin (M + 1),
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (ν : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin (M + 1), ∀ n : ℕ,
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (νn n : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin M,
            PlabelRect ⟨J.1, Nat.lt_succ_of_lt J.2⟩ =
              (PlabelRect ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩).map
                (measurable_stageLabelTruncatePath (k := k) J.1).aemeasurable)) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  obtain ⟨PlabelStage, _, _, _, hhead, hcoord, hcompat⟩ :=
    existsCompatibleStageLabelFamily_ofPrefixRectanglesWithSubseq
      ν νn (hq := hq) fallback hprefixRect
  -- Proof comment: the subsequence itself is only an internal compactness witness; downstream
  -- consumers of the extractor only need the limiting family and its exact compatibility laws.
  exact ⟨PlabelStage, hhead, hcoord, hcompat⟩

/-- Helper for Theorem 17.56: an exact-index family of couplings with geometric dyadic budgets
already yields the summable bad-mass family required by the direct realization API. -/
private theorem existsSummableDyadicBadMassCouplingFamily_ofExactIndexBudgets
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hbudget :
      ∀ n : ℕ,
        ∃ π : ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
          IsCoupling π ν (νn n) ∧
            ∀ m : ℕ, m ≤ n →
              (π : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
                {z | (1 / 2 : ℝ) ^ m <
                    @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2} <
                  ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1))) :
    ∃ π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)),
      (∀ n : ℕ, IsCoupling (π n) ν (νn n)) ∧
        (∀ m : ℕ,
          (∑' n,
            ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
              {z | (1 / 2 : ℝ) ^ m <
                  @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2})) ≠ ∞) := by
  classical
  let π : ℕ → ProbabilityMeasure ((ℕ → unitInterval) × (ℕ → unitInterval)) :=
    fun n ↦ Classical.choose (hbudget n)
  refine ⟨π, ?_, ?_⟩
  · intro n
    -- Proof comment: the chosen coupling at time `n` already has the exact prescribed marginals.
    exact (Classical.choose_spec (hbudget n)).1
  · intro m
    let bad : ℕ → ENNReal := fun n ↦
      ((π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval)))
        {z | (1 / 2 : ℝ) ^ m <
            @Dist.dist (ℕ → unitInterval) PiCountable.dist z.1 z.2})
    let C : ℝ := (2 : ℝ) ^ (m + 1)
    have hgeomSummable : Summable (fun n : ℕ ↦ C * (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [C, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        (summable_geometric_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show (1 / 2 : ℝ) < 1 by norm_num)).mul_left (C * (1 / 2 : ℝ))
    have hdom :
        ∀ n : ℕ, bad n ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (n + 1)) := by
      intro n
      by_cases hnm : n < m
      · have hprob :
          bad n ≤ 1 := by
            calc
              bad n ≤ (π n : Measure ((ℕ → unitInterval) × (ℕ → unitInterval))) Set.univ := by
                exact measure_mono (Set.subset_univ _)
              _ = 1 := by
                simp [bad]
        have hbound :
            (1 : ℝ) ≤ C * (1 / 2 : ℝ) ^ (n + 1) := by
          have hnle : n + 1 ≤ m + 1 := Nat.succ_le_succ (Nat.le_of_lt hnm)
          have hpow :
              (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
            exact pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
              (by norm_num : (1 / 2 : ℝ) ≤ 1) hnle
          calc
            (1 : ℝ) = C * (1 / 2 : ℝ) ^ (m + 1) := by
              rw [show C = (2 : ℝ) ^ (m + 1) by rfl, ← mul_pow]
              norm_num
            _ ≤ C * (1 / 2 : ℝ) ^ (n + 1) := by
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
        calc
          bad n ≤ 1 := hprob
          _ = ENNReal.ofReal (1 : ℝ) := by norm_num
          _ ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (n + 1)) := by
            exact ENNReal.ofReal_le_ofReal hbound
      · have hnm' : m ≤ n := Nat.le_of_not_gt hnm
        have hbad :=
          (Classical.choose_spec (hbudget n)).2 m hnm'
        have hC_ge_one : (1 : ℝ) ≤ C := by
          dsimp [C]
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hscale :
            (1 / 2 : ℝ) ^ (n + 1) ≤ C * (1 / 2 : ℝ) ^ (n + 1) := by
          exact le_mul_of_one_le_left
            (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 1)) hC_ge_one
        calc
          bad n ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := le_of_lt hbad
          _ ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (n + 1)) := by
            exact ENNReal.ofReal_le_ofReal hscale
    have htsum_le :
        (∑' n, bad n) ≤ ∑' n, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (n + 1)) := by
      exact ENNReal.tsum_le_tsum hdom
    exact ne_of_lt <|
      lt_of_le_of_lt htsum_le hgeomSummable.tsum_ofReal_lt_top

/-- Helper for Theorem 17.56: one finite compatible stage-label rectangle already yields a single
ambient Hilbert-cube path law carrying the whole finite dyadic cutoff table. -/
private theorem existsAmbientPathLawWithFiniteDyadicCutoffTable
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (hdiam :
      ∀ i : ℕ, ∀ x y : ℕ → unitInterval, q i x = q i y →
        @Dist.dist (ℕ → unitInterval) PiCountable.dist x y ≤ (1 / 2 : ℝ) ^ i)
    (R : ℕ) :
    ∃ Nrect : Fin (R + 1) → ℕ,
      ∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (ν : Measure (ℕ → unitInterval)) ∧
        (∀ n : ℕ,
          Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
              (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) ∧
        (∀ m r : Fin (R + 1),
          (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m.1 (Nrect r))) := by
  classical
  let PlabelTop : ProbabilityMeasure (ℕ → StageLabel k R) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier R
  have hPlabelTop :
      Measure.map (fun ω : ℕ → StageLabel k R ↦ ω 0)
          (PlabelTop : Measure (ℕ → StageLabel k R)) =
        Measure.map (stageLabelMap (k := k) q R) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k R ↦ ω (n + 1))
            (PlabelTop : Measure (ℕ → StageLabel k R)) =
          Measure.map (stageLabelMap (k := k) q R) (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(PlabelTop : Measure (ℕ → StageLabel k R)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: keep the chosen top-stage witness in one spelling so the compatible prefix
    -- family and the fixed ambient lift can both reuse its exact marginals and eventual equality.
    simpa [PlabelTop] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier R
  let Nrect : Fin (R + 1) → ℕ := fun r ↦
    Classical.choose <|
      exists_labelTailEvent_highProb_of_ae_eventuallyEq
        (α := StageLabel k R) (P := PlabelTop) hPlabelTop.2.2
        ((1 / 2 : ℝ≥0) ^ (r.1 + 1)) <| by
          positivity
  have htailTop :
      ∀ r : Fin (R + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (PlabelTop : Measure (ℕ → StageLabel k R))
            (labelTailEvent (α := StageLabel k R) (Nrect r)) := by
    intro r
    -- Proof comment: freeze one deterministic top-stage cutoff for each dyadic budget so the
    -- whole finite prefix rectangle can reuse the same cutoff table.
    exact Classical.choose_spec <|
      exists_labelTailEvent_highProb_of_ae_eventuallyEq
        (α := StageLabel k R) (P := PlabelTop) hPlabelTop.2.2
        ((1 / 2 : ℝ≥0) ^ (r.1 + 1)) <| by
          positivity
  rcases existsCompatibleStageLabelPrefixFamilyOfTop
      ν νn (hq := hq) (M := R) (R := R) PlabelTop hPlabelTop.1 hPlabelTop.2.1
      Nrect htailTop with
    ⟨PlabelRect, htop, hheadRect, hcoordRect, htailRect, hcompatRect⟩
  let Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)) :=
    ambientStageLabelPathLaw
      (ν := ν) (νn := νn) (k := k) (q := q) hq R PlabelTop
      hPlabelTop.1 hPlabelTop.2.1 hdiam
  have hprojEqNat :
      ∀ {m j : ℕ} (hmR : m ≤ R) (hmj : m ≤ j) (hjR : j ≤ R),
        (projectedStageLabelPathLaw (k := k) (J := j) (m := m) hmj
          (PlabelRect j hjR) : Measure (ℕ → Fin (k m))) =
        (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl
          (PlabelRect m hmR) : Measure (ℕ → Fin (k m))) := by
    intro m j hmR hmj hjR
    rcases Nat.exists_eq_add_of_le hmj with ⟨d, rfl⟩
    have hhmj : hmj = Nat.le_add_right m d := Subsingleton.elim _ _
    subst hhmj
    induction d with
    | zero =>
        have hhjR : hjR = hmR := Subsingleton.elim _ _
        subst hhjR
        rfl
    | succ d ih =>
        have hprev : m ≤ m + d := Nat.le_add_right m d
        have hprevR : m + d ≤ R := Nat.le_of_succ_le hjR
        have hlt : m + d < R := Nat.lt_of_succ_le hjR
        have hsucc :
            Nat.le_add_right m (d + 1) = Nat.le_succ_of_le hprev := Subsingleton.elim _ _
        calc
          (projectedStageLabelPathLaw (k := k) (J := m + d + 1) (m := m)
              (Nat.le_add_right m (d + 1)) (PlabelRect (m + d + 1) hjR) :
                Measure (ℕ → Fin (k m))) =
            (projectedStageLabelPathLaw (k := k) (J := m + d) (m := m)
              hprev
              ((PlabelRect (m + d + 1) hjR).map
                (measurable_stageLabelTruncatePath (k := k) (m + d)).aemeasurable) :
                  Measure (ℕ → Fin (k m))) := by
                simpa [hsucc] using
                  congrArg
                    (fun ρ : ProbabilityMeasure (ℕ → Fin (k m)) ↦
                      (ρ : Measure (ℕ → Fin (k m))))
                    (projectedStageLabelPathLaw_map_stageLabelTruncatePath
                      (k := k) (J := m + d) (m := m)
                      hprev (PlabelRect (m + d + 1) hjR))
          _ =
            (projectedStageLabelPathLaw (k := k) (J := m + d) (m := m)
              hprev (PlabelRect (m + d) hprevR) :
                Measure (ℕ → Fin (k m))) := by
                rw [← hcompatRect (m + d) hlt]
          _ =
            (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl
              (PlabelRect m hmR) : Measure (ℕ → Fin (k m))) := ih hprevR
  refine ⟨Nrect, Pinf, ?_, ?_, ?_⟩
  · -- Proof comment: the fixed ambient witness preserves the head marginal of the chosen top
    -- stage law by construction.
    simpa [Pinf] using
      ambientStageLabelPathLaw_head
        (ν := ν) (νn := νn) (k := k) (q := q) hq R PlabelTop
        hPlabelTop.1 hPlabelTop.2.1 hdiam
  · intro n
    -- Proof comment: the same ambient witness preserves every time-`n + 1` marginal of the
    -- approximating sequence.
    simpa [Pinf] using
      ambientStageLabelPathLaw_coord
        (ν := ν) (νn := νn) (k := k) (q := q) hq R PlabelTop
        hPlabelTop.1 hPlabelTop.2.1 hdiam n
  · intro m r
    have hmR : m.1 ≤ R := Nat.le_of_lt_succ m.2
    have hprojEqTop :
        (projectedStageLabelPathLaw (k := k) (J := R) (m := m.1) hmR PlabelTop :
          Measure (ℕ → Fin (k m.1))) =
          (projectedStageLabelPathLaw (k := k) (J := m.1) (m := m.1) le_rfl
            (PlabelRect m.1 hmR) : Measure (ℕ → Fin (k m.1))) := by
      rw [← htop]
      exact hprojEqNat (m := m.1) hmR hmR le_rfl
    have hprojectedTail :
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
          (projectedStageLabelPathLaw (k := k) (J := R) (m := m.1) hmR PlabelTop :
            Measure (ℕ → Fin (k m.1))) (labelTailEvent (α := Fin (k m.1)) (Nrect r)) := by
      have hstageTail :
          (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r.1 + 1)) : ℝ≥0∞)) <
            (PlabelRect m.1 hmR : Measure (ℕ → StageLabel k m.1))
              (labelTailEvent (α := StageLabel k m.1) (Nrect r)) :=
        htailRect m.1 hmR r
      have hcoarseTail :=
        projectStageLabelPath_probabilityMap_tailLowerBound
          (k := k) (J := m.1) (m := m.1) le_rfl (PlabelRect m.1 hmR) hstageTail
      rw [hprojEqTop]
      exact hcoarseTail
    -- Proof comment: the shared rectangle cutoff table first descends to the coarse projected
    -- top-stage law, and then the fixed ambient witness transports that same cutoff to the
    -- dyadic tail event at scale `m`.
    simpa [Pinf] using
      ambientStageLabelPathLaw_projected_dyadicTail
        (ν := ν) (νn := νn) (k := k) (q := q) hq R PlabelTop
        hPlabelTop.1 hPlabelTop.2.1 hdiam hmR hprojectedTail

/-- Helper for Theorem 17.56: if one fixed ambient Hilbert-cube path law satisfies every dyadic
error budget at a given scale `m`, then the corresponding path coordinate converges at that scale
almost surely. -/
private theorem ae_eventuallyDistLe_ofDyadicTailCutoffs
    (P : ProbabilityMeasure (ℕ → (ℕ → unitInterval))) (m : ℕ)
    (hcutoff :
      ∀ r : ℕ, ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (P : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) :
    ∀ᵐ ω ∂(P : Measure (ℕ → (ℕ → unitInterval))),
      ∀ᶠ n : ℕ in atTop,
        @Dist.dist (ℕ → unitInterval) PiCountable.dist (ω (n + 1)) (ω 0) ≤
          (1 / 2 : ℝ) ^ m := by
  let unionTail : Set (ℕ → (ℕ → unitInterval)) := ⋃ N : ℕ, dyadicTailEvent m N
  have hUnionMeas : MeasurableSet unionTail := by
    exact MeasurableSet.iUnion fun N ↦ (isClosed_dyadicTailEvent m N).measurableSet
  have hUnionUpper :
      (P : Measure (ℕ → (ℕ → unitInterval))) unionTail ≤ 1 := by
    calc
      (P : Measure (ℕ → (ℕ → unitInterval))) unionTail ≤
          (P : Measure (ℕ → (ℕ → unitInterval))) Set.univ := by
            exact measure_mono (by intro ω hω; simp)
      _ = 1 := by simp
  have hUnionNeTop :
      (P : Measure (ℕ → (ℕ → unitInterval))) unionTail ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hUnionUpper ENNReal.one_lt_top)
  have hUnionLower :
      ∀ r : ℕ,
        1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ) <
          ((P : Measure (ℕ → (ℕ → unitInterval))) unionTail).toReal := by
    intro r
    have hltENN :
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (P : Measure (ℕ → (ℕ → unitInterval))) unionTail := by
      exact lt_of_lt_of_le (Classical.choose_spec (hcutoff r)) <|
        measure_mono (by
          intro ω hω
          exact Set.mem_iUnion.2 ⟨Classical.choose (hcutoff r), hω⟩)
    have hltENN' :
        ((↑(1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) : ℝ≥0∞)) <
          (P : Measure (ℕ → (ℕ → unitInterval))) unionTail := by
      simpa [ENNReal.coe_sub] using hltENN
    have hpowLeOne :
        ((1 / 2 : ℝ≥0) ^ (r + 1)) ≤ 1 := by
      exact pow_le_one₀ (by positivity : 0 ≤ (1 / 2 : ℝ≥0))
        (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)
    have hltReal :
        (((1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0) : ℝ)) <
          ((P : Measure (ℕ → (ℕ → unitInterval))) unionTail).toReal := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hUnionNeTop).1 <| by
        simpa using hltENN'
    have hsubReal :
        (((1 - ((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0)) : ℝ) =
          1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ) := by
      simpa using (NNReal.coe_sub hpowLeOne)
    rwa [hsubReal] at hltReal
  have hpowNN :
      Tendsto (fun r : ℕ ↦ ((1 / 2 : ℝ≥0) ^ (r + 1))) atTop (𝓝 0) := by
    -- Proof comment: the dyadic error budgets again tend to `0`, so the real lower bounds on the
    -- union event approach `1`.
    simpa using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (show (1 / 2 : ℝ≥0) < 1 by norm_num)).comp
        (tendsto_add_atTop_nat 1)
  have hpowReal :
      Tendsto (fun r : ℕ ↦ (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    exact NNReal.tendsto_coe.2 hpowNN
  have honeMinus :
      Tendsto (fun r : ℕ ↦ 1 - (((1 / 2 : ℝ≥0) ^ (r + 1) : ℝ≥0) : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hpowReal
  have hUnionToRealGeOne :
      1 ≤ ((P : Measure (ℕ → (ℕ → unitInterval))) unionTail).toReal := by
    exact le_of_tendsto_of_tendsto' honeMinus tendsto_const_nhds fun r ↦
      (hUnionLower r).le
  have hUnionToRealLeOne :
      ((P : Measure (ℕ → (ℕ → unitInterval))) unionTail).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top hUnionUpper
  have hUnionProb :
      (P : Measure (ℕ → (ℕ → unitInterval))) unionTail = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).1 <|
      le_antisymm hUnionToRealLeOne hUnionToRealGeOne
  have hUnionAe :
      ∀ᵐ ω ∂(P : Measure (ℕ → (ℕ → unitInterval))), ω ∈ unionTail := by
    exact (mem_ae_iff_prob_eq_one hUnionMeas).2 hUnionProb
  -- Proof comment: membership in the union of deterministic dyadic tail events is exactly the
  -- desired eventual metric control at the fixed scale `m`.
  filter_upwards [hUnionAe] with ω hω
  rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
  exact Filter.eventually_atTop.2 ⟨N, hN⟩

/-- Helper for Theorem 17.56: one ambient Hilbert-cube path law with exact coordinate marginals
and a full dyadic cutoff table already yields the direct dyadic realization consumed by the
constant-family adapter. -/
private theorem existsHilbertCubeDirectDyadicRealization_ofCutoffTable
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval)) :
    (∃ Pinf : ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
        (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
            (Pinf : Measure (ℕ → (ℕ → unitInterval))) =
          (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m r : ℕ, ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (Pinf : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N))) →
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  intro hambient
  rcases hambient with ⟨Pinf, hheadInf, hcoordInf, hcutoff⟩
  let Y : (ℕ → (ℕ → unitInterval)) → ℕ → unitInterval := fun ω ↦ ω 0
  let Yn : ℕ → (ℕ → (ℕ → unitInterval)) → ℕ → unitInterval := fun n ω ↦ ω (n + 1)
  have hY : HasLaw Y ν Pinf := by
    refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
    simpa [Y] using hheadInf
  have hYn : ∀ n : ℕ, HasLaw (Yn n) (νn n) Pinf := by
    intro n
    refine ⟨(measurable_pi_apply (n + 1)).aemeasurable, ?_⟩
    simpa [Yn] using hcoordInf n
  have hdyadic :
      ∀ m : ℕ, ∀ᵐ ω ∂(Pinf : Measure (ℕ → (ℕ → unitInterval))),
        ∀ᶠ n : ℕ in atTop,
          @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
            (1 / 2 : ℝ) ^ m := by
    intro m
    -- Proof comment: the full dyadic cutoff table for the fixed ambient law implies probability
    -- one of the union of deterministic tail events at every fixed scale.
    exact ae_eventuallyDistLe_ofDyadicTailCutoffs Pinf m (hcutoff m)
  exact ⟨ℕ → (ℕ → unitInterval), inferInstance, Pinf, Y, Yn, hY, hYn, hdyadic⟩

/-- Helper for Theorem 17.56: the finite compatible rectangles built from the chosen stage laws
already compactly extract one global compatible stage-label family with exact marginals. -/
private theorem existsCompatibleChosenStageLabelFamilyWithSubseq
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ J : ℕ,
        Tendsto
          (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose <|
                Classical.choose_spec <|
                  finiteCompatibleStageLabelTruncationRectangle
                    ν νn hνn hk hq hfrontier (φ n) (φ n))
                ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J)
          atTop (𝓝 (PlabelStage J))) ∧
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  let hprefixRect :
      ∀ M : ℕ,
        ∃ PlabelRect : ∀ J : Fin (M + 1), ProbabilityMeasure (ℕ → StageLabel k J.1),
          (∀ J : Fin (M + 1),
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω 0)
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (ν : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin (M + 1), ∀ n : ℕ,
            Measure.map (fun ω : ℕ → StageLabel k J.1 ↦ ω (n + 1))
                (PlabelRect J : Measure (ℕ → StageLabel k J.1)) =
              Measure.map (stageLabelMap (k := k) q J.1)
                (νn n : Measure (ℕ → unitInterval))) ∧
          (∀ J : Fin M,
            PlabelRect ⟨J.1, Nat.lt_succ_of_lt J.2⟩ =
              (PlabelRect ⟨J.1 + 1, Nat.succ_lt_succ J.2⟩).map
                (measurable_stageLabelTruncatePath (k := k) J.1).aemeasurable) := by
    intro M
    rcases finiteCompatibleStageLabelTruncationRectangle
        ν νn hνn hk hq hfrontier M M with
      ⟨Nrect, PlabelRect, hheadRect, hcoordRect, htailRect, hcompatRect⟩
    -- Proof comment: keep the finite rectangle in the same spelling used by the compactness
    -- extractor, but retain the underlying subsequence later instead of discarding it
    -- immediately.
    exact ⟨PlabelRect, hheadRect, hcoordRect, hcompatRect⟩
  -- Proof comment: this is the same compactness extraction as the simpler compatible-family
  -- theorem, but it keeps the convergent subsequence visible so downstream cutoff proofs can work
  -- with an explicit limiting route.
  rcases existsCompatibleStageLabelFamily_ofPrefixRectanglesWithSubseq
      ν νn (hq := hq)
      (fun J ↦ chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) hprefixRect with
    ⟨PlabelStage, φ, hφmono, hφtendsto, hheadStage, hcoordStage, hcompatStage⟩
  have hφtendstoRect :
      ∀ J : ℕ,
        Tendsto
          (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose <|
                Classical.choose_spec <|
                  finiteCompatibleStageLabelTruncationRectangle
                    ν νn hνn hk hq hfrontier (φ n) (φ n))
                ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J)
          atTop (𝓝 (PlabelStage J)) := by
    intro J
    -- Proof comment: the stronger extractor already converges for the finite-rectangle spelling
    -- encoded by `hprefixRect`; unfolding that spelling yields the theorem-local rectangle API.
    have hEq :
        (fun n ↦
          if hJ : J ≤ φ n then
            (Classical.choose <|
              Classical.choose_spec <|
                finiteCompatibleStageLabelTruncationRectangle
                  ν νn hνn hk hq hfrontier (φ n) (φ n))
              ⟨J, Nat.lt_succ_of_le hJ⟩
          else
            chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) =
    (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose (hprefixRect (φ n))) ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J) := by
      funext n
      split_ifs with hJ
      · sorry
      · rfl
    rw [hEq]
    exact hφtendsto J
  exact ⟨PlabelStage, φ, hφmono, hφtendstoRect,
    hheadStage, hcoordStage, hcompatStage⟩

/-- Helper for Theorem 17.56: the finite compatible rectangles built from the chosen stage laws
already compactly extract one global compatible stage-label family with exact marginals. -/
private theorem existsCompatibleChosenStageLabelFamily
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) := by
  obtain ⟨PlabelStage, φ, hφmono, hφtendsto, hheadStage, hcoordStage, hcompatStage⟩ :=
    existsCompatibleChosenStageLabelFamilyWithSubseq
      ν νn hνn hk hq hfrontier
  -- Proof comment: downstream consumers of the simpler API only need the limiting compatible
  -- family; the explicit subsequence is now available from the stronger helper above when the
  -- cutoff-preservation proof needs it.
  exact ⟨PlabelStage, hheadStage, hcoordStage, hcompatStage⟩

/-- Helper for Theorem 17.56: along the compactness subsequence, the stage-`m` approximant is
the stage-`m` member of the finite rectangle at top stage `φ n` whenever that branch is active,
and otherwise it falls back to the chosen stage-`m` law. -/
private abbrev compactnessStageApproximation
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    (φ : ℕ → ℕ) (m n : ℕ) :
    ProbabilityMeasure (ℕ → StageLabel k m) :=
  if hm : m ≤ φ n then
    Classical.choose
      (Classical.choose_spec
        (finiteCompatibleStageLabelTruncationRectangle
          ν νn hνn hk hq hfrontier (φ n) (φ n)))
      ⟨m, Nat.lt_succ_of_le hm⟩
  else
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier m

/-- Helper for Theorem 17.56: once `n` already dominates the fixed stage `m`, the compactness
stage approximant is literally the `m`th member of the rectangle built at top stage `φ n`. -/
private theorem compactnessStageApproximation_eq_rect
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {φ : ℕ → ℕ} (hφmono : StrictMono φ) {m n : ℕ} (hmn : m ≤ n) :
    compactnessStageApproximation ν νn hνn hk hq hfrontier φ m n =
      Classical.choose
        (Classical.choose_spec
          (finiteCompatibleStageLabelTruncationRectangle
            ν νn hνn hk hq hfrontier (φ n) (φ n)))
        ⟨m, Nat.lt_succ_of_le (le_trans hmn (StrictMono.id_le hφmono n))⟩ := by
  have hmφ : m ≤ φ n := le_trans hmn (StrictMono.id_le hφmono n)
  -- Proof comment: on the tail where `φ n` already covers stage `m`, the fallback branch of the
  -- approximant abbreviation disappears definitionally.
  simp [compactnessStageApproximation, hmφ]

/-- Helper for Theorem 17.56: the subsequence convergence recorded by the compatible-family
extractor can be restated using the named compactness stage approximant. -/
private theorem compactnessStageApproximation_tendsto
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J)}
    {φ : ℕ → ℕ}
    (hφtendsto :
      ∀ J : ℕ,
        Tendsto
          (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose <|
                Classical.choose_spec <|
                  finiteCompatibleStageLabelTruncationRectangle
                    ν νn hνn hk hq hfrontier (φ n) (φ n))
                ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J)
          atTop (𝓝 (PlabelStage J))) :
    ∀ J : ℕ,
      Tendsto
        (fun n ↦ compactnessStageApproximation ν νn hνn hk hq hfrontier φ J n)
        atTop (𝓝 (PlabelStage J)) := by
  intro J
  -- Proof comment: the new abbreviation is only a spelling change for the subsequence extractor,
  -- so the original convergence statement rewrites directly.
  simpa [compactnessStageApproximation] using hφtendsto J

/-- Helper for Theorem 17.56: once a deterministic label-tail threshold `N` has already been
frozen along the compactness subsequence at stage `m`, the fixed-threshold Portmanteau step
transfers the shifted dyadic cutoff to the limit stage law `PlabelStage m`. -/
private theorem compactnessStageApproximation_limitCutoff_of_eventually_fixedThreshold
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J)}
    {φ : ℕ → ℕ}
    (hφtendsto :
      ∀ J : ℕ,
        Tendsto
          (fun n ↦
            if hJ : J ≤ φ n then
              (Classical.choose <|
                Classical.choose_spec <|
                  finiteCompatibleStageLabelTruncationRectangle
                    ν νn hνn hk hq hfrontier (φ n) (φ n))
                ⟨J, Nat.lt_succ_of_le hJ⟩
            else
              chosenStageLabelPathLaw ν νn hνn hk hq hfrontier J)
          atTop (𝓝 (PlabelStage J)))
    {m r N : ℕ}
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 2)) : ℝ≥0∞)) <
          ((compactnessStageApproximation
              ν νn hνn hk hq hfrontier φ m n :
              ProbabilityMeasure (ℕ → StageLabel k m)) :
            Measure (ℕ → StageLabel k m))
            (labelTailEvent (α := StageLabel k m) N)) :
    (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
      (PlabelStage m : Measure (ℕ → StageLabel k m))
        (labelTailEvent (α := StageLabel k m) N) := by
  -- Proof comment: after rewriting the subsequence convergence using the named approximant, the
  -- fixed-threshold Portmanteau helper applies directly at stage `m`.
  exact labelTailCutoff_of_tendsto_with_fixedThreshold
    (compactnessStageApproximation_tendsto
      ν νn hνn hk hq hfrontier hφtendsto m)
    hbound

/-- Helper for Theorem 17.56: along the compactness subsequence produced by the compatible
chosen-stage extractor, every fixed stage-`m` approximant already inherits one dyadic label-tail
cutoff from its finite rectangle once `φ n` dominates both `m` and the budget scale `r`. -/
private theorem eventually_compactnessStageApproximation_hasTailCutoff
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0)
    {φ : ℕ → ℕ} (hφmono : StrictMono φ) (m r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          ((compactnessStageApproximation
              ν νn hνn hk hq hfrontier φ m n :
              ProbabilityMeasure (ℕ → StageLabel k m)) :
            Measure (ℕ → StageLabel k m))
            (labelTailEvent (α := StageLabel k m) N) := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨max m r, fun n hn ↦ ?_⟩
  have hm_n : m ≤ n := le_trans (le_max_left m r) hn
  have hr_n : r ≤ n := le_trans (le_max_right m r) hn
  have hm : m ≤ φ n := le_trans hm_n (StrictMono.id_le hφmono n)
  have hr : r ≤ φ n := le_trans hr_n (StrictMono.id_le hφmono n)
  let hrect :=
    finiteCompatibleStageLabelTruncationRectangle
      ν νn hνn hk hq hfrontier (φ n) (φ n)
  let Nrect : Fin (φ n + 1) → ℕ := Classical.choose hrect
  let PlabelRect : ∀ J : Fin (φ n + 1), ProbabilityMeasure (ℕ → StageLabel k J.1) :=
    Classical.choose (Classical.choose_spec hrect)
  have htailRect :
      ∀ J : Fin (φ n + 1), ∀ s : Fin (φ n + 1),
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (s.1 + 1)) : ℝ≥0∞)) <
          (PlabelRect J : Measure (ℕ → StageLabel k J.1))
            (labelTailEvent (α := StageLabel k J.1) (Nrect s)) :=
    (Classical.choose_spec (Classical.choose_spec hrect)).2.2.1
  refine ⟨Nrect ⟨r, Nat.lt_succ_of_le hr⟩, ?_⟩
  -- Proof comment: once `φ n` is large enough, the compactness approximant at stage `m` is
  -- literally the `m`th member of the finite rectangle built at top stage `φ n`, so the shared
  -- rectangle cutoff table applies directly.
  rw [compactnessStageApproximation_eq_rect
    ν νn hνn hk hq hfrontier hφmono hm_n]
  exact
    htailRect ⟨m, Nat.lt_succ_of_le hm⟩ ⟨r, Nat.lt_succ_of_le hr⟩

/-- Helper for Theorem 17.56: one stage-`J` top law together with the exact bundled marginals and
the almost-sure eventual-equality event needed by the recursive compatible-family route. -/
private structure StageLabelTopLawData
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ} {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m)) (J : ℕ) where
  law : ProbabilityMeasure (ℕ → StageLabel k J)
  head :
    Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
        (law : Measure (ℕ → StageLabel k J)) =
      Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval))
  coord :
    ∀ n : ℕ,
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          (law : Measure (ℕ → StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval))
  eventuallyEq :
    ∀ᵐ ω ∂(law : Measure (ℕ → StageLabel k J)),
      ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0

/-- Helper for Theorem 17.56: a probability measure can only live on a nonempty type. -/
private theorem nonempty_of_probabilityMeasure
    {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α) :
    Nonempty α := by
  exact MeasureTheory.nonempty_of_isProbabilityMeasure (μ := (μ : Measure α))

/-- Helper for Theorem 17.56: if the successor-stage bundled label law exists, then the new last
alphabet `Fin (k (J + 1))` is nonempty. -/
private theorem positive_lastCoordinateCard_of_stageLabelProbabilityMeasure
    {k : ℕ → ℕ} (J : ℕ)
    (μ : ProbabilityMeasure (StageLabel k (J + 1))) :
    0 < k (J + 1) := by
  obtain ⟨a⟩ := nonempty_of_probabilityMeasure μ
  -- Proof comment: evaluating a stage label at the final index directly exhibits one element of
  -- the last-coordinate alphabet.
  exact
    lt_of_lt_of_le (Nat.zero_lt_succ _)
      (Nat.succ_le_of_lt (a (Fin.last (J + 1))).isLt)

/-- Helper for Theorem 17.56: before enforcing fine-stage eventual equality, one can already
construct a stage-`J + 1` path law with the exact fine one-time marginals and literal truncation
back to the prescribed stage-`J` top law. -/
private theorem existsSuccessorStageLabelPathLawOverTop_marginals
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ)
    (dataJ : StageLabelTopLawData ν νn (k := k) (q := q) hq J) :
    ∃ PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)),
      dataJ.law =
        PlabelSucc.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable ∧
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval))) := by
  let μFine : ProbabilityMeasure (StageLabel k (J + 1)) :=
    ν.map ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)
  let μFineSeq : ℕ → ProbabilityMeasure (StageLabel k (J + 1)) := fun n ↦
    (νn n).map ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)
  have hnext : 0 < k (J + 1) := by
    -- Proof comment: the fine one-time marginal is a probability measure on
    -- `StageLabel k (J + 1)`, so the new last coordinate cannot be empty.
    exact positive_lastCoordinateCard_of_stageLabelProbabilityMeasure (k := k) J μFine
  let t : Set (StageLabel k (J + 1)) := Set.range (stageLabelZeroExtension (k := k) J hnext)
  letI : Fintype t := Fintype.ofFinite t
  let encodeCoarse : StageLabel k J → t := fun a ↦
    ⟨stageLabelZeroExtension (k := k) J hnext a, ⟨a, rfl⟩⟩
  let coarseRepresentativePath : (ℕ → StageLabel k J) → (ℕ → t) := fun ω n ↦ encodeCoarse (ω n)
  have hcoarseRepresentativePathMeas : Measurable coarseRepresentativePath := by
    refine measurable_pi_lambda coarseRepresentativePath ?_
    intro n
    exact (measurable_of_finite encodeCoarse).comp (measurable_pi_apply n)
  let ρFine : StageLabel k (J + 1) → t := fun a ↦
    ⟨stageLabelZeroExtension (k := k) J hnext (stageLabelTruncate (k := k) J a),
      ⟨stageLabelTruncate (k := k) J a, rfl⟩⟩
  have hρFineMeas : Measurable ρFine := by
    exact measurable_of_finite _
  let representativeValPath : (ℕ → t) → (ℕ → StageLabel k (J + 1)) := fun ω n ↦ (ω n).1
  have hrepresentativeValPathMeas : Measurable representativeValPath := by
    refine measurable_pi_lambda representativeValPath ?_
    intro n
    exact measurable_subtype_coe.comp (measurable_pi_apply n)
  let representativePath : (ℕ → StageLabel k (J + 1)) → (ℕ → t) := fun ω n ↦ ρFine (ω n)
  have hrepresentativePathMeas : Measurable representativePath := by
    refine measurable_pi_lambda representativePath ?_
    intro n
    exact hρFineMeas.comp (measurable_pi_apply n)
  have hρFine_stageLabelMap :
      ρFine ∘ stageLabelMap (k := k) q (J + 1) =
        encodeCoarse ∘ stageLabelMap (k := k) q J := by
    -- Proof comment: applying the representative map to a fine stage label means truncating it to
    -- stage `J` and then reinserting the distinguished last coordinate.
    funext x
    apply Subtype.ext
    simpa [ρFine, encodeCoarse] using
      congrArg (stageLabelZeroExtension (k := k) J hnext)
        (congrFun (stageLabelTruncate_comp_stageLabelMap (k := k) q J) x)
  let PlabelRep : ProbabilityMeasure (ℕ → t) :=
    dataJ.law.map hcoarseRepresentativePathMeas.aemeasurable
  have hheadRep :
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        ((representativeMapLaw μFine hρFineMeas : ProbabilityMeasure t) : Measure t) := by
    -- Proof comment: the representative head law is just the prescribed coarse head law, pushed
    -- through the zero-extension section and identified with the fine head law via truncation.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω 0) (PlabelRep : Measure (ℕ → t)) =
        Measure.map
          ((fun ω : ℕ → t ↦ ω 0) ∘ coarseRepresentativePath)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (Measure.map_map (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
                (f := coarseRepresentativePath) (g := fun ω : ℕ → t ↦ ω 0)
                (measurable_pi_apply 0) hcoarseRepresentativePathMeas)
      _ =
        Measure.map
          (encodeCoarse ∘ fun ω : ℕ → StageLabel k J ↦ ω 0)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rfl
      _ =
        Measure.map encodeCoarse
          (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (dataJ.law : Measure (ℕ → StageLabel k J))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
                  (f := fun ω : ℕ → StageLabel k J ↦ ω 0) (g := encodeCoarse)
                  (measurable_of_finite encodeCoarse) (measurable_pi_apply 0))
      _ = Measure.map encodeCoarse
          (Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) := by
              rw [dataJ.head]
      _ = Measure.map (encodeCoarse ∘ stageLabelMap (k := k) q J)
          (ν : Measure (ℕ → unitInterval)) := by
            rw [Measure.map_map (measurable_of_finite encodeCoarse)
              (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = Measure.map (ρFine ∘ stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)) := by
            rw [hρFine_stageLabelMap]
      _ = Measure.map ρFine
          (Measure.map (stageLabelMap (k := k) q (J + 1))
            (ν : Measure (ℕ → unitInterval))) := by
            symm
            rw [Measure.map_map hρFineMeas
              (measurable_stageLabelMap (k := k) (q := q) hq (J + 1))]
      _ = ((representativeMapLaw μFine hρFineMeas : ProbabilityMeasure t) : Measure t) := by
            rfl
  have hcoordRep :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
          ((representativeMapLaw (μFineSeq n) hρFineMeas : ProbabilityMeasure t) : Measure t) := by
    intro n
    -- Proof comment: the same representative normalization applies to every later time
    -- coordinate.
    calc
      Measure.map (fun ω : ℕ → t ↦ ω (n + 1)) (PlabelRep : Measure (ℕ → t)) =
        Measure.map
          ((fun ω : ℕ → t ↦ ω (n + 1)) ∘ coarseRepresentativePath)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            simpa [PlabelRep] using
              (Measure.map_map (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
                (f := coarseRepresentativePath) (g := fun ω : ℕ → t ↦ ω (n + 1))
                (measurable_pi_apply (n + 1)) hcoarseRepresentativePathMeas)
      _ =
        Measure.map
          (encodeCoarse ∘ fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rfl
      _ =
        Measure.map encodeCoarse
          (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (dataJ.law : Measure (ℕ → StageLabel k J))) := by
              symm
              simpa [Function.comp] using
                (Measure.map_map (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
                  (f := fun ω : ℕ → StageLabel k J ↦ ω (n + 1)) (g := encodeCoarse)
                  (measurable_of_finite encodeCoarse) (measurable_pi_apply (n + 1)))
      _ = Measure.map encodeCoarse
          (Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) := by
              rw [dataJ.coord n]
      _ = Measure.map (encodeCoarse ∘ stageLabelMap (k := k) q J)
          (νn n : Measure (ℕ → unitInterval)) := by
            rw [Measure.map_map (measurable_of_finite encodeCoarse)
              (measurable_stageLabelMap (k := k) (q := q) hq J)]
      _ = Measure.map (ρFine ∘ stageLabelMap (k := k) q (J + 1))
          (νn n : Measure (ℕ → unitInterval)) := by
            rw [hρFine_stageLabelMap]
      _ = Measure.map ρFine
          (Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval))) := by
            symm
            rw [Measure.map_map hρFineMeas
              (measurable_stageLabelMap (k := k) (q := q) hq (J + 1))]
      _ = ((representativeMapLaw (μFineSeq n) hρFineMeas : ProbabilityMeasure t) : Measure t) := by
            rfl
  let eStage : StageLabel k (J + 1) ≃ Fin (Fintype.card (StageLabel k (J + 1))) :=
    Fintype.equivFin (StageLabel k (J + 1))
  letI : MetricSpace (Fin (Fintype.card (StageLabel k (J + 1)))) :=
    MetricSpace.induced (fun i : Fin (Fintype.card (StageLabel k (J + 1))) ↦ (i : ℕ))
      Fin.val_injective inferInstance
  letI : MetricSpace (StageLabel k (J + 1)) :=
    MetricSpace.induced eStage eStage.injective inferInstance
  letI : BorelSpace (StageLabel k (J + 1)) := inferInstance
  let eStageIso : StageLabel k (J + 1) ≃ᵢ Fin (Fintype.card (StageLabel k (J + 1))) :=
    { toEquiv := eStage
      isometry_toFun := by
        intro x y
        rfl }
  letI : CompleteSpace (StageLabel k (J + 1)) :=
    eStageIso.completeSpace
  letI : SecondCountableTopology (StageLabel k (J + 1)) := inferInstance
  letI : Nonempty (StageLabel k (J + 1)) := nonempty_of_probabilityMeasure μFine
  obtain ⟨PlabelSucc, hheadSucc, hcoordSucc, hrepresentativeSucc⟩ :=
    existsPathLawOfRepresentative
      (E := StageLabel k (J + 1)) (t := t) (ρ := ρFine) hρFineMeas
      μFine μFineSeq PlabelRep hheadRep hcoordRep
  have hcoarseRepresentativeLaw :
      Measure.map representativeValPath
          (Measure.map representativePath
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
        Measure.map representativeValPath (PlabelRep : Measure (ℕ → t)) := by
    -- Proof comment: after the generic representative-path lift, coercing the representative
    -- labels back to actual successor-stage labels yields the same zero-extended coarse path law.
    rw [hrepresentativeSucc]
  have hrepresentativePath_val :
      representativeValPath ∘ representativePath =
        stageLabelZeroExtensionPath (k := k) J hnext ∘
          stageLabelTruncatePath (k := k) J := by
    -- Proof comment: coercing the representative of a successor label just zero-extends its
    -- stage-`J` truncation.
    funext ω
    funext n
    rfl
  have hcoarseRepresentativePath_val :
      representativeValPath ∘ coarseRepresentativePath =
        stageLabelZeroExtensionPath (k := k) J hnext := by
    -- Proof comment: the stored representative path is literally the coordinatewise zero
    -- extension of the coarse path.
    funext ω
    funext n
    rfl
  have hzeroCompat :
      Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
          (Measure.map (stageLabelTruncatePath (k := k) J)
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
        Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
    -- Proof comment: coercing the representative-path equality back to stage labels shows that
    -- both measures have the same zero-extended coarse path law.
    calc
      Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
          (Measure.map (stageLabelTruncatePath (k := k) J)
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
        Measure.map (representativeValPath ∘ representativePath)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
            rw [hrepresentativePath_val, Measure.map_map
              (measurable_stageLabelZeroExtensionPath (k := k) J hnext)
              (measurable_stageLabelTruncatePath (k := k) J)]
      _ =
        Measure.map representativeValPath
          (Measure.map representativePath
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) := by
            symm
            rw [Measure.map_map hrepresentativeValPathMeas hrepresentativePathMeas]
      _ =
        Measure.map representativeValPath (PlabelRep : Measure (ℕ → t)) := by
            exact hcoarseRepresentativeLaw
      _ =
        Measure.map (representativeValPath ∘ coarseRepresentativePath)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rw [show (PlabelRep : Measure (ℕ → t)) =
              Measure.map coarseRepresentativePath
                (dataJ.law : Measure (ℕ → StageLabel k J)) by
                  rfl]
            symm
            rw [Measure.map_map hrepresentativeValPathMeas hcoarseRepresentativePathMeas]
      _ =
        Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rw [hcoarseRepresentativePath_val]
  have hcompatMeasure :
      Measure.map (stageLabelTruncatePath (k := k) J)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        (dataJ.law : Measure (ℕ → StageLabel k J)) := by
    -- Proof comment: applying stage truncation to the common zero-extended law recovers the
    -- original coarse path law because truncation is a left inverse of zero extension.
    calc
      Measure.map (stageLabelTruncatePath (k := k) J)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelTruncatePath (k := k) J)
          (Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
            (Measure.map (stageLabelTruncatePath (k := k) J)
              (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))))) := by
              symm
              exact stageLabelTruncatePath_map_zeroExtensionPath
                (k := k) J hnext
                (μ := Measure.map (stageLabelTruncatePath (k := k) J)
                  (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))))
      _ =
        Measure.map (stageLabelTruncatePath (k := k) J)
          (Measure.map (stageLabelZeroExtensionPath (k := k) J hnext)
            (dataJ.law : Measure (ℕ → StageLabel k J))) := by
              rw [hzeroCompat]
      _ = (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            exact stageLabelTruncatePath_map_zeroExtensionPath
              (k := k) J hnext (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
  refine ⟨PlabelSucc, ?_, hheadSucc, hcoordSucc⟩
  apply ProbabilityMeasure.toMeasure_injective
  simpa using hcompatMeasure.symm

/-- Helper for Theorem 17.56: under a product law `μ × volume`, pairing the first component with
the finite-discrete simulator for the row law `κ a` gives the expected singleton masses. -/
private theorem measurable_stochasticMatrixSimulationStateOfProbabilityMeasure
    {k : ℕ} (i : Fin k) (μ : ProbabilityMeasure (Fin k)) :
    Measurable (stochasticMatrixSimulationState (singletonMassMatrix μ) i) := by
  classical
  refine measurable_to_countable' ?_
  intro j
  change MeasurableSet
    {u : unitInterval | stochasticMatrixSimulationState (singletonMassMatrix μ) i u = j}
  exact
    measurableSet_preimage_stochasticMatrixSimulationState
      (singletonMassMatrix μ) (singletonMassMatrix_isStochastic μ) i j

/-- Helper for Theorem 17.56: on a finite prefix alphabet, the rowwise simulator depending on the
current prefix state is measurable. -/
private theorem measurable_prefixSimulator
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    {k : ℕ} (κ : α → ProbabilityMeasure (Fin k)) (i : Fin k) :
    Measurable
      (fun z : α × unitInterval ↦
        stochasticMatrixSimulationState (singletonMassMatrix (κ z.1)) i z.2) := by
  classical
  refine measurable_to_countable' ?_
  intro b
  have hfiber :
      ((fun z : α × unitInterval ↦
          stochasticMatrixSimulationState (singletonMassMatrix (κ z.1)) i z.2) ⁻¹' {b}) =
        ⋃ a : α, ({a} : Set α) ×ˢ
          {u : unitInterval |
            stochasticMatrixSimulationState (singletonMassMatrix (κ a)) i u = b} := by
    ext z
    constructor
    · intro hz
      refine Set.mem_iUnion.2 ?_
      refine ⟨z.1, ?_⟩
      simpa using hz
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨a, ha⟩
      rcases ha with ⟨hza, hzb⟩
      rcases hza
      simpa using hzb
  rw [hfiber]
  exact MeasurableSet.iUnion fun a ↦
    (measurableSet_singleton a).prod
      (measurableSet_preimage_stochasticMatrixSimulationState
        (singletonMassMatrix (κ a)) (singletonMassMatrix_isStochastic (κ a)) i b)

private theorem map_prefixSimulator_apply_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    {k : ℕ} (μ : ProbabilityMeasure α) (κ : α → ProbabilityMeasure (Fin k))
    (i : Fin k) (a : α) (b : Fin k) :
    Measure.map
        (fun z : α × unitInterval ↦
          (z.1, stochasticMatrixSimulationState (singletonMassMatrix (κ z.1)) i z.2))
        (((μ : Measure α).prod volume) : Measure (α × unitInterval)) {(a, b)} =
      (μ : Measure α) {a} * ((κ a : Measure (Fin k)) {b}) := by
  have hsim :
      Measure.map (stochasticMatrixSimulationState (singletonMassMatrix (κ a)) i)
          (volume : Measure unitInterval) =
        ((κ a : ProbabilityMeasure (Fin k)) : Measure (Fin k)) := by
    simpa using
      (hasLaw_stochasticMatrixSimulationStateOfProbabilityMeasure
        (i := i) (μ := κ a)).map_eq
  have hpreimage :
      (fun z : α × unitInterval ↦
        (z.1, stochasticMatrixSimulationState (singletonMassMatrix (κ z.1)) i z.2)) ⁻¹'
          ({(a, b)} : Set (α × Fin k)) =
        ({a} : Set α) ×ˢ
          {u : unitInterval |
            stochasticMatrixSimulationState (singletonMassMatrix (κ a)) i u = b} := by
    ext z
    constructor
    · intro hz
      rcases Prod.mk.inj hz with ⟨hza, hzb⟩
      rcases hza
      simp [hzb]
    · rintro ⟨hza, hzb⟩
      rcases hza
      simpa using congrArg (fun u ↦ (z.1, u)) hzb
  have hsimApply :
      (volume : Measure unitInterval)
          {u : unitInterval |
            stochasticMatrixSimulationState (singletonMassMatrix (κ a)) i u = b} =
        ((κ a : Measure (Fin k)) {b}) := by
    have hmapApply := congrArg (fun ν : Measure (Fin k) ↦ ν {b}) hsim
    simpa [Measure.map_apply
      (measurable_stochasticMatrixSimulationStateOfProbabilityMeasure i (κ a))
      (measurableSet_singleton b)] using hmapApply
  have hpairMeas :
      Measurable
        (fun z : α × unitInterval ↦
          (z.1, stochasticMatrixSimulationState (singletonMassMatrix (κ z.1)) i z.2)) := by
    exact measurable_fst.prodMk (measurable_prefixSimulator κ i)
  -- Proof comment: the pair preimage of the singleton `{(a, b)}` is the product of the prefix
  -- singleton `{a}` with the simulator fiber over `b`, so the product measure factors exactly.
  rw [Measure.map_apply hpairMeas (MeasurableSet.singleton (a, b))]
  rw [hpreimage, Measure.prod_prod, hsimApply]

/-- Helper for Theorem 17.56: on a finite measurable singleton space, a measure is already
determined by its singleton masses. -/
private theorem measure_eq_of_forall_singleton
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    {μ ν : Measure α} (h : ∀ a : α, μ {a} = ν {a}) :
    μ = ν := by
  exact Measure.ext_of_singleton h

/-- Helper for Theorem 17.56: a probability law on the successor-stage joint normal form forces
the new last-coordinate alphabet to be nonempty. -/
private theorem positive_lastCoordinateCard_of_successorJointProbabilityMeasure
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))) :
    0 < k (J + 1) := by
  obtain ⟨z⟩ := nonempty_of_probabilityMeasure jointLaw
  -- Proof comment: any point in the joint law carries a concrete element of
  -- `Fin (k (J + 1))`, so that alphabet cannot be empty.
  exact lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt z.2.isLt)

/-- Helper for Theorem 17.56: after splitting a successor-stage joint law into coarse prefix and
new last coordinate, the conditional row law is the normalized fiber over the coarse prefix,
pushed forward to `Prod.snd`. -/
private noncomputable def successorStageLastCoordinateKernel
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))) :
    StageLabel k J → ProbabilityMeasure (Fin (k (J + 1))) :=
  letI : Nonempty (StageLabel k J × Fin (k (J + 1))) := nonempty_of_probabilityMeasure jointLaw
  let i : Fin (k (J + 1)) :=
    ⟨0, positive_lastCoordinateCard_of_successorJointProbabilityMeasure (k := k) J jointLaw⟩
  let encode :
      StageLabel k J → Set.range (fun a : StageLabel k J ↦ (a, i)) :=
    fun a ↦ ⟨(a, i), ⟨a, rfl⟩⟩
  let prefixCode :
      StageLabel k J × Fin (k (J + 1)) →
        Set.range (fun a : StageLabel k J ↦ (a, i)) :=
    fun z ↦ encode z.1
  fun a ↦
    (normalizedFiberLaw jointLaw prefixCode (encode a)).map measurable_snd.aemeasurable

/-- Helper for Theorem 17.56: the conditional last-coordinate kernel recovers the singleton
atoms of the successor-stage joint law from its coarse-prefix marginal. -/
private theorem jointLaw_singleton_eq_map_fst_mul_successorStageLastCoordinateKernel
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (a : StageLabel k J) (b : Fin (k (J + 1))) :
    (((jointLaw.map measurable_fst.aemeasurable :
        ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) *
        ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
          Measure (Fin (k (J + 1)))) {b}) =
      (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) {(a, b)} := by
  letI : Nonempty (StageLabel k J × Fin (k (J + 1))) := nonempty_of_probabilityMeasure jointLaw
  let i0 : Fin (k (J + 1)) :=
    ⟨0, positive_lastCoordinateCard_of_successorJointProbabilityMeasure (k := k) J jointLaw⟩
  let encode :
      StageLabel k J → Set.range (fun a : StageLabel k J ↦ (a, i0)) :=
    fun a ↦ ⟨(a, i0), ⟨a, rfl⟩⟩
  let prefixCode :
      StageLabel k J × Fin (k (J + 1)) →
        Set.range (fun a : StageLabel k J ↦ (a, i0)) :=
    fun z ↦ encode z.1
  -- Local instance justification (finite discrete Polish structure): the normalized-fiber API
  -- below is stated for Polish ambient spaces, so we equip the finite prefix and last-coordinate
  -- alphabets with the induced metric from `ℕ`.
  let ePrefix : StageLabel k J ≃ Fin (Fintype.card (StageLabel k J)) :=
    Fintype.equivFin (StageLabel k J)
  letI : MetricSpace (Fin (Fintype.card (StageLabel k J))) :=
    MetricSpace.induced (fun i : Fin (Fintype.card (StageLabel k J)) ↦ (i : ℕ))
      Fin.val_injective inferInstance
  letI : MetricSpace (StageLabel k J) :=
    MetricSpace.induced ePrefix ePrefix.injective inferInstance
  letI : BorelSpace (StageLabel k J) := inferInstance
  let ePrefixIso : StageLabel k J ≃ᵢ Fin (Fintype.card (StageLabel k J)) :=
    { toEquiv := ePrefix
      isometry_toFun := by
        intro x y
        rfl }
  letI : CompleteSpace (StageLabel k J) := ePrefixIso.completeSpace
  letI : SecondCountableTopology (StageLabel k J) := inferInstance
  letI : MetricSpace (Fin (k (J + 1))) :=
    MetricSpace.induced (fun i : Fin (k (J + 1)) ↦ (i : ℕ))
      Fin.val_injective inferInstance
  letI : BorelSpace (Fin (k (J + 1))) := inferInstance
  letI : CompleteSpace (Fin (k (J + 1))) := inferInstance
  letI : SecondCountableTopology (Fin (k (J + 1))) := inferInstance
  let fiberLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) :=
    normalizedFiberLaw jointLaw prefixCode (encode a)
  let fiberMeasure : Measure (StageLabel k J × Fin (k (J + 1))) := fiberLaw
  have hmass :
      (((jointLaw.toFiniteMeasure.restrict (prefixCode ⁻¹' {encode a})).mass : ℝ≥0∞)) =
        (((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) := by
    calc
      (((jointLaw.toFiniteMeasure.restrict (prefixCode ⁻¹' {encode a})).mass : ℝ≥0∞)) =
          (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) (prefixCode ⁻¹' {encode a}) := by
            simpa using congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
              ((jointLaw.toFiniteMeasure).restrict_mass (prefixCode ⁻¹' {encode a}))
      _ =
          (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) (Prod.fst ⁻¹' {a}) := by
            congr 1
            ext z
            simp [prefixCode, encode]
      _ =
          (((jointLaw.map measurable_fst.aemeasurable :
              ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) := by
            symm
            simpa using
              (Measure.map_apply (μ := (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))))
                measurable_fst (measurableSet_singleton a))
  have hkernel :
      ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
          Measure (Fin (k (J + 1)))) {b}) =
        fiberMeasure (Prod.snd ⁻¹' {b}) := by
    -- Proof comment: unfold the row-kernel definition once so the last-coordinate singleton is a
    -- direct `Prod.snd` pushforward of the normalized fiber law.
    dsimp [successorStageLastCoordinateKernel, i0, encode, prefixCode, fiberLaw, fiberMeasure]
    simpa using
      (Measure.map_apply
        (μ := ((normalizedFiberLaw jointLaw prefixCode (encode a) :
          ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))) :
            Measure (StageLabel k J × Fin (k (J + 1)))))
        measurable_snd (measurableSet_singleton b))
  have hsnd :
      MeasurableSet
        ((Prod.snd : StageLabel k J × Fin (k (J + 1)) → Fin (k (J + 1))) ⁻¹'
          ({b} : Set (Fin (k (J + 1))))) :=
    measurable_snd (measurableSet_singleton b)
  calc
    (((jointLaw.map measurable_fst.aemeasurable :
        ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) *
        ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
          Measure (Fin (k (J + 1)))) {b}) =
      (((jointLaw.toFiniteMeasure.restrict (prefixCode ⁻¹' {encode a})).mass : ℝ≥0∞) *
        ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
          Measure (Fin (k (J + 1)))) {b})) := by
            rw [hmass]
    _ =
      (((jointLaw.toFiniteMeasure.restrict (prefixCode ⁻¹' {encode a})).mass : ℝ≥0∞) *
        fiberMeasure (Prod.snd ⁻¹' {b})) := by
          rw [hkernel]
    _ =
      (((jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))).restrict
          (prefixCode ⁻¹' {encode a})) (Prod.snd ⁻¹' {b})) := by
            simpa [fiberLaw, fiberMeasure, smul_eq_mul] using
              fiberMass_smul_normalizedFiberLaw_apply
                (μ := jointLaw) (ρ := prefixCode) (a := encode a) (s := Prod.snd ⁻¹' {b}) hsnd
    _ = (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) {(a, b)} := by
          rw [Measure.restrict_apply hsnd]
          congr 1
          ext z
          rcases z with ⟨x, y⟩
          simp [prefixCode, encode]
          constructor
          · rintro ⟨hy, hx⟩
            exact ⟨hx, hy⟩
          · rintro ⟨hx, hy⟩
            exact ⟨hy, hx⟩

/-- Helper for Theorem 17.56: simulating the conditional last-coordinate kernel over the coarse
prefix marginal reconstructs the full successor-stage joint law. -/
private theorem map_prefixSimulator_eq_successorJointLaw
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (i : Fin (k (J + 1))) :
    Measure.map
        (fun z : StageLabel k J × unitInterval ↦
          (z.1, stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J jointLaw z.1)) i z.2))
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).prod volume) :
          Measure (StageLabel k J × unitInterval)) =
      (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) := by
  -- Proof comment: on the finite successor-stage alphabet, both measures are determined by their
  -- singleton masses, and those singleton masses were computed in the previous two lemmas.
  apply measure_eq_of_forall_singleton
  intro z
  rcases z with ⟨a, b⟩
  calc
    Measure.map
        (fun z : StageLabel k J × unitInterval ↦
          (z.1, stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J jointLaw z.1)) i z.2))
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).prod volume) :
          Measure (StageLabel k J × unitInterval)) {(a, b)} =
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) *
        ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
          Measure (Fin (k (J + 1)))) {b}) := by
          simpa using
            map_prefixSimulator_apply_singleton
              (μ := jointLaw.map measurable_fst.aemeasurable)
              (κ := successorStageLastCoordinateKernel (k := k) J jointLaw) i a b
    _ =
      (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) {(a, b)} := by
        exact
          jointLaw_singleton_eq_map_fst_mul_successorStageLastCoordinateKernel
            (k := k) J jointLaw a b

/-- Helper for Theorem 17.56: the explicit successor-stage convergence hypothesis already implies
convergence of the new last-coordinate quantizer laws. -/
private theorem successorStageLastCoordinatePushforwardTendsto
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ)
    (hSuccTendsto :
      Tendsto
        (fun n ↦
          (νn n).map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
        atTop
        (𝓝
          (ν.map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)))) :
    Tendsto
      (fun n ↦ (νn n).map ((hq (J + 1)).aemeasurable))
      atTop
      (𝓝 (ν.map ((hq (J + 1)).aemeasurable))) := by
  let jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) :=
    ((ν.map
        ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
      ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))
  let jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) :=
    fun n ↦
      (((νn n).map
          ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
        ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))
  have hjointLawSeq : Tendsto jointLawSeq atTop (𝓝 jointLaw) := by
    -- Proof comment: move the fine-stage convergence once into the product normal form so that
    -- projecting to the new last coordinate is a single continuous pushforward.
    simpa [jointLaw, jointLawSeq] using
      successorStageJointLawTendsto ν νn hq J hSuccTendsto
  have hsnd :
      Tendsto
        (fun n ↦ (jointLawSeq n).map measurable_snd.aemeasurable)
        atTop
        (𝓝 (jointLaw.map measurable_snd.aemeasurable)) := by
    -- Proof comment: after the joint laws converge in product form, the last-coordinate laws
    -- converge by continuity of `Prod.snd` on the finite discrete alphabet.
    simpa [jointLaw, jointLawSeq] using
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        jointLawSeq jointLaw hjointLawSeq continuous_snd)
  have hjointLawSeq_snd :
      ∀ n : ℕ,
        (jointLawSeq n).map measurable_snd.aemeasurable =
          (νn n).map ((hq (J + 1)).aemeasurable) := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    simpa [jointLawSeq] using
      (successorStageJointLawSpec (k := k) (q := q) hq J
        (νn n : Measure (ℕ → unitInterval))).2
  have hjointLaw_snd :
      jointLaw.map measurable_snd.aemeasurable =
        ν.map ((hq (J + 1)).aemeasurable) := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa [jointLaw] using
      (successorStageJointLawSpec (k := k) (q := q) hq J
        (ν : Measure (ℕ → unitInterval))).2
  simpa [hjointLawSeq_snd, hjointLaw_snd] using hsnd

/-- Helper for Theorem 17.56: on a finite coarse alphabet, the common unit-interval driver avoids
the simulator boundary determined by the time-`0` coarse prefix almost surely. -/
private theorem ae_avoid_rowSimulationBoundary_at_timeZero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    {k : ℕ} (P : Measure (ℕ → α)) (κ : α → ProbabilityMeasure (Fin k)) (i : Fin k) :
    ∀ᵐ z ∂((P.prod volume) : Measure ((ℕ → α) × unitInterval)),
      z.2 ∉ simulationBoundarySet i (κ (z.1 0)) := by
  classical
  let bad : Set ((ℕ → α) × unitInterval) :=
    ⋃ a : α, ({ω : ℕ → α | ω 0 = a} ×ˢ simulationBoundarySet i (κ a))
  have hbad :
      {z : (ℕ → α) × unitInterval | z.2 ∈ simulationBoundarySet i (κ (z.1 0))} = bad := by
    ext z
    simp [bad]
  have hbadMeas : MeasurableSet bad := by
    change MeasurableSet
      (⋃ a : α, (((fun ω : ℕ → α ↦ ω 0) ⁻¹' ({a} : Set α)) ×ˢ simulationBoundarySet i (κ a)))
    exact MeasurableSet.iUnion fun a ↦
      ((measurable_pi_apply 0) (measurableSet_singleton a)).prod
        (simulationBoundarySet_finite i (κ a)).measurableSet
  have hgoodMeas :
      MeasurableSet
        {z : (ℕ → α) × unitInterval | z.2 ∉ simulationBoundarySet i (κ (z.1 0))} := by
    rw [show {z : (ℕ → α) × unitInterval |
        z.2 ∉ simulationBoundarySet i (κ (z.1 0))} = badᶜ by
          ext z
          simp [bad]]
    exact hbadMeas.compl
  rw [Measure.ae_prod_iff_ae_ae hgoodMeas]
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hzero :
      (volume : Measure unitInterval) (simulationBoundarySet i (κ (ω 0))) = 0 := by
    -- Proof comment: each boundary set is finite, and finite subsets of `unitInterval` have
    -- zero `volume`.
    simpa using
      (simulationBoundarySet_finite i (κ (ω 0))).countable.measure_zero
        (μ := (volume : Measure unitInterval))
  simpa using (compl_mem_ae_iff.2 hzero)

/-- Helper for Theorem 17.56: the common driver avoids the simulator boundary of the conditional
last-coordinate law extracted from the successor-stage joint normal form. -/
private theorem ae_avoid_successorStageLastCoordinateBoundary
    {k : ℕ → ℕ} (J : ℕ)
    (P : Measure (ℕ → StageLabel k J))
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (i : Fin (k (J + 1))) :
    ∀ᵐ z ∂((P.prod volume) : Measure ((ℕ → StageLabel k J) × unitInterval)),
      z.2 ∉ simulationBoundarySet i
        (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0)) := by
  -- Proof comment: specialize the generic finite-alphabet boundary-null statement to the
  -- conditional row laws coming from the successor-stage joint law.
  exact ae_avoid_rowSimulationBoundary_at_timeZero
    (P := P) (κ := successorStageLastCoordinateKernel (k := k) J jointLaw) i

/-- Helper for Theorem 17.56: once the coarse prefix has frozen and the last-coordinate row laws
at that frozen prefix converge, the common-driver finite simulator stabilizes to its limit away
from the boundary set of the limiting row law. -/
private theorem eventuallyEq_rowwiseSimulator_of_eventuallyEq_prefix
    {α : Type*} {k : ℕ} (i : Fin k)
    {κn : ℕ → α → ProbabilityMeasure (Fin k)}
    {κ : α → ProbabilityMeasure (Fin k)}
    {ω : ℕ → α} {u : unitInterval}
    (hω : ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0)
    (hκ : Tendsto (fun n ↦ κn n (ω 0)) atTop (𝓝 (κ (ω 0))))
    (hu : u ∉ simulationBoundarySet i (κ (ω 0))) :
    ∀ᶠ n : ℕ in atTop,
      stochasticMatrixSimulationState (singletonMassMatrix (κn n (ω (n + 1)))) i u =
        stochasticMatrixSimulationState (singletonMassMatrix (κ (ω 0))) i u := by
  have hsim :
      ∀ᶠ n : ℕ in atTop,
        stochasticMatrixSimulationState (singletonMassMatrix (κn n (ω 0))) i u =
          stochasticMatrixSimulationState (singletonMassMatrix (κ (ω 0))) i u := by
    -- Proof comment: at the frozen prefix `ω 0`, this is exactly the earlier one-row simulator
    -- stabilization theorem.
    exact eventually_stochasticMatrixSimulationState_eq_limit
      (i := i) (μn := fun n ↦ κn n (ω 0)) (μ := κ (ω 0)) hκ hu
  -- Proof comment: once the prefix path agrees with `ω 0`, the rowwise simulator sees the same
  -- law sequence as in the fixed-prefix stabilization lemma.
  filter_upwards [hω, hsim] with n hnω hnsim
  simpa [hnω] using hnsim

/-- Helper for Theorem 17.56: on a finite alphabet, a sampled point belongs almost surely to an
atom with positive singleton mass. -/
private theorem ae_nonzeroSingletonMass_of_finiteProbabilityMeasure
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
    (ρ : ProbabilityMeasure α) :
    ∀ᵐ a ∂(ρ : Measure α), ((ρ : Measure α) {a}) ≠ 0 := by
  classical
  let s : Set α := {a | ((ρ : Measure α) {a}) = 0}
  have hs :
      (ρ : Measure α) s = 0 := by
    let fs : Finset α := s.toFinite.toFinset
    have hfs : (fs : Set α) = s := by
      simp [fs]
    calc
      (ρ : Measure α) s = (ρ : Measure α) fs := by
        rw [hfs]
      _ = ∑ x ∈ fs, (ρ : Measure α) {x} := by
        simpa [fs] using
          (MeasureTheory.sum_measure_singleton (μ := (ρ : Measure α)) (s := fs)).symm
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hx' : x ∈ s := by
          rwa [← hfs]
        simpa [s] using hx'
  have hcompl : ∀ᵐ a ∂(ρ : Measure α), a ∉ s := by
    exact compl_mem_ae_iff.2 hs
  -- Proof comment: outside the null set of zero atoms, the sampled singleton mass is nonzero.
  filter_upwards [hcompl] with a ha
  simpa [s] using ha

/-- Helper for Theorem 17.56: a positive coarse-prefix atom rewrites each row singleton of the
successor-stage kernel as a quotient of joint singleton masses. -/
private theorem successorStageLastCoordinateKernel_real_singleton_eq_div
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (a : StageLabel k J) (b : Fin (k (J + 1)))
    (ha :
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) ≠ 0) :
    ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
      Measure (Fin (k (J + 1)))).real {b}) =
      ((jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))).real {(a, b)}) /
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).real {a})) := by
  have hmul :=
    jointLaw_singleton_eq_map_fst_mul_successorStageLastCoordinateKernel
      (k := k) J jointLaw a b
  have hmulReal :
      ((((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).real {a}) *
          ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
            Measure (Fin (k (J + 1)))).real {b})) =
        ((jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))).real {(a, b)}) := by
    -- Proof comment: after applying `ENNReal.toReal`, the multiplicative atom identity becomes an
    -- ordinary real equality.
    simpa [Measure.real_def] using congrArg ENNReal.toReal hmul
  have hdenom :
      ((((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).real {a})) ≠ 0 := by
    exact
      (MeasureTheory.measureReal_ne_zero_iff
        (μ := (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))))
        (s := ({a} : Set (StageLabel k J)))
        (h := measure_ne_top _ _)).2 ha
  -- Proof comment: divide the real atom identity by the positive coarse-prefix singleton mass.
  exact (eq_div_iff hdenom).2 <| by
    simpa [mul_comm] using hmulReal

/-- Helper for Theorem 17.56: if the joint laws and their coarse marginals converge and the limit
prefix atom at `a` is positive, then the conditional last-coordinate row law at `a` converges. -/
private theorem tendsto_successorStageLastCoordinateKernel_of_nonzeroPrefix
    {k : ℕ → ℕ} (J : ℕ)
    {jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))}
    {jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))}
    {a : StageLabel k J}
    (hjoint : Tendsto jointLawSeq atTop (𝓝 jointLaw))
    (hprefix :
      Tendsto
        (fun n ↦ (jointLawSeq n).map measurable_fst.aemeasurable)
        atTop
        (𝓝 (jointLaw.map measurable_fst.aemeasurable)))
    (ha :
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) ≠ 0) :
    Tendsto
      (fun n ↦ successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) a)
      atTop
      (𝓝 (successorStageLastCoordinateKernel (k := k) J jointLaw a)) := by
  refine tendstoProbabilityMeasure_of_forall_singletonMassReal_tendsto ?_
  intro b
  let num : ℕ → ℝ := fun n ↦
    (jointLawSeq n : Measure (StageLabel k J × Fin (k (J + 1)))).real {(a, b)}
  let den : ℕ → ℝ := fun n ↦
    (((jointLawSeq n).map measurable_fst.aemeasurable :
      ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).real {a}
  let num0 : ℝ :=
    (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))).real {(a, b)}
  let den0 : ℝ :=
    (((jointLaw.map measurable_fst.aemeasurable :
      ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).real {a})
  have hnum :
      Tendsto num atTop (𝓝 num0) := by
    have hcont :=
      continuousFiniteDiscreteSingletonMassReal
        (α := StageLabel k J × Fin (k (J + 1))) (a := (a, b))
    -- Proof comment: the joint laws live on a finite discrete product alphabet, so singleton
    -- masses are continuous test functionals there.
    change
      Tendsto
        ((fun ρ : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) ↦
          (ρ : Measure (StageLabel k J × Fin (k (J + 1)))).real {(a, b)}) ∘ jointLawSeq)
        atTop (𝓝 num0)
    simpa [num0, Function.comp] using (hcont.tendsto jointLaw).comp hjoint
  have hden :
      Tendsto den atTop (𝓝 den0) := by
    have hcont :=
      continuousFiniteDiscreteSingletonMassReal (α := StageLabel k J) (a := a)
    -- Proof comment: the same finite-discrete continuity applies to the coarse-prefix marginals.
    change
      Tendsto
        ((fun ρ : ProbabilityMeasure (StageLabel k J) ↦
          (ρ : Measure (StageLabel k J)).real {a}) ∘
          fun n ↦ (jointLawSeq n).map measurable_fst.aemeasurable)
        atTop (𝓝 den0)
    simpa [den0, Function.comp] using
      (hcont.tendsto (jointLaw.map measurable_fst.aemeasurable)).comp hprefix
  have hden0_ne : den0 ≠ 0 := by
    exact
      (MeasureTheory.measureReal_ne_zero_iff
        (μ := (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))))
        (s := ({a} : Set (StageLabel k J)))
        (h := measure_ne_top _ _)).2 <| by
          simpa [den0] using ha
  have hden0_pos : 0 < den0 := by
    have hnonneg : 0 ≤ den0 := by positivity
    exact lt_of_le_of_ne hnonneg (Ne.symm hden0_ne)
  have hdenEventually : ∀ᶠ n : ℕ in atTop, den n ≠ 0 := by
    have hclose :
        ∀ᶠ n : ℕ in atTop, |den n - den0| < den0 / 2 := by
      simpa [Real.dist_eq] using
        (Metric.tendsto_atTop.1 hden) (den0 / 2) (by positivity)
    -- Proof comment: convergence to a positive singleton mass forces eventual positivity of the
    -- approximating coarse-prefix atoms, so the quotient formula is eventually valid.
    filter_upwards [hclose] with n hn
    have hgt : den0 / 2 < den n := by
      have hlt := (abs_lt.mp hn).1
      linarith
    exact ne_of_gt (lt_trans (by positivity) hgt)
  have hformula :
      ∀ᶠ n : ℕ in atTop,
        ((successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) a :
          Measure (Fin (k (J + 1)))).real {b}) =
          num n / den n := by
    filter_upwards [hdenEventually] with n hn
    have hn' :
        (((jointLawSeq n).map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a} ≠ 0 := by
      exact
        (MeasureTheory.measureReal_ne_zero_iff
          (μ := (((jointLawSeq n).map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)))
          (s := ({a} : Set (StageLabel k J)))
          (h := measure_ne_top _ _)).1 <| by
            simpa [den] using hn
    -- Proof comment: once the approximating coarse-prefix atom is nonzero, each row singleton is
    -- the explicit real quotient proved above.
    simpa [num, den] using
      successorStageLastCoordinateKernel_real_singleton_eq_div
        (k := k) J (jointLawSeq n) a b hn'
  have hquot :
      Tendsto (fun n ↦ num n / den n) atTop (𝓝 (num0 / den0)) := by
    exact hnum.div hden hden0_ne
  have hlimitFormula :
      ((successorStageLastCoordinateKernel (k := k) J jointLaw a :
        Measure (Fin (k (J + 1)))).real {b}) =
        num0 / den0 := by
    simpa [num0, den0] using
      successorStageLastCoordinateKernel_real_singleton_eq_div
        (k := k) J jointLaw a b ha
  -- Proof comment: replace the conditional row singleton masses by their eventual quotient normal
  -- form, then pass to the limit by ordinary real division.
  exact (tendsto_congr' hformula).2 <| by
    simpa [hlimitFormula] using hquot

/-- Helper for Theorem 17.56: once the time-`0` coarse law of a path measure matches the coarse
prefix marginal of `jointLaw`, the positive-prefix row-law convergence theorem packages into an
almost-everywhere statement over the frozen prefix `ω 0`. -/
private theorem ae_tendsto_successorStageLastCoordinateKernel_atTimeZero
    {k : ℕ → ℕ} (J : ℕ)
    {P : ProbabilityMeasure (ℕ → StageLabel k J)}
    {jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))}
    {jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1)))}
    (hhead :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (P : Measure (ℕ → StageLabel k J)) =
        (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))))
    (hjoint : Tendsto jointLawSeq atTop (𝓝 jointLaw))
    (hprefix :
      Tendsto
        (fun n ↦ (jointLawSeq n).map measurable_fst.aemeasurable)
        atTop
        (𝓝 (jointLaw.map measurable_fst.aemeasurable))) :
    ∀ᵐ ω ∂(P : Measure (ℕ → StageLabel k J)),
      Tendsto
        (fun n ↦ successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (ω 0))
        atTop
        (𝓝 (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0))) := by
  let good : Set (StageLabel k J) :=
    {a |
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) {a}) ≠ 0}
  have hgoodMeas : MeasurableSet good := by
    classical
    exact (Set.toFinite good).measurableSet
  have hgood :
      ∀ᵐ a ∂(((jointLaw.map measurable_fst.aemeasurable :
        ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))), a ∈ good := by
    -- Proof comment: the frozen coarse prefix lands almost surely in the positive-mass support of
    -- the limiting coarse marginal.
    simpa [good] using
      ae_nonzeroSingletonMass_of_finiteProbabilityMeasure
        (jointLaw.map measurable_fst.aemeasurable)
  have htimeZero :
      ∀ᵐ ω ∂(P : Measure (ℕ → StageLabel k J)), ω 0 ∈ good := by
    have hgood' :
        ∀ᵐ a ∂(Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0) (P : Measure (ℕ → StageLabel k J))),
          a ∈ good := by
      simpa [hhead] using hgood
    exact
      (MeasureTheory.ae_map_iff
        (measurable_pi_apply 0).aemeasurable hgoodMeas).1 hgood'
  -- Proof comment: at every frozen prefix with positive limiting mass, the fixed-prefix row-law
  -- convergence theorem applies directly.
  filter_upwards [htimeZero] with ω hω
  exact
    tendsto_successorStageLastCoordinateKernel_of_nonzeroPrefix
      (k := k) J hjoint hprefix hω

/-- Helper for Theorem 17.56: if the `t`th coarse coordinate of a path law already has the first
marginal of `jointLaw`, then simulating the row kernel at that coordinate reconstructs `jointLaw`
on the `(prefix,last)` product normal form. -/
private theorem map_successorStagePrefixSimulator_of_marginal
    {k : ℕ → ℕ} (J : ℕ)
    (P : ProbabilityMeasure (ℕ → StageLabel k J))
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (i : Fin (k (J + 1))) (t : ℕ)
    (hP :
      Measure.map (fun ω : ℕ → StageLabel k J ↦ ω t)
          (P : Measure (ℕ → StageLabel k J)) =
        (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)))) :
    Measure.map
        (fun z : (ℕ → StageLabel k J) × unitInterval ↦
          (z.1 t,
            stochasticMatrixSimulationState
              (singletonMassMatrix
                (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 t))) i z.2))
        (((P : Measure (ℕ → StageLabel k J)).prod volume) :
          Measure ((ℕ → StageLabel k J) × unitInterval)) =
      (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) := by
  let state :
      (ℕ → StageLabel k J) × unitInterval → StageLabel k J × unitInterval :=
    fun z ↦ (z.1 t, z.2)
  let simulate :
      StageLabel k J × unitInterval → StageLabel k J × Fin (k (J + 1)) :=
    fun z ↦
      (z.1,
        stochasticMatrixSimulationState
          (singletonMassMatrix
            (successorStageLastCoordinateKernel (k := k) J jointLaw z.1)) i z.2)
  have hsimulateMeas : Measurable simulate := by
    exact measurable_fst.prodMk
      (measurable_prefixSimulator
        (κ := successorStageLastCoordinateKernel (k := k) J jointLaw) i)
  have hstateMeas : Measurable state := by
    fun_prop
  have hstateMap :
      Measure.map state
          (((P : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval)) =
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).prod volume) :
          Measure (StageLabel k J × unitInterval)) := by
    -- Proof comment: reading the `t`th coarse coordinate and keeping the common driver turns the
    -- product path law into the product of the required coarse marginal with `volume`.
    calc
      Measure.map state
          (((P : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval)) =
        Measure.map (Prod.map (fun ω : ℕ → StageLabel k J ↦ ω t) id)
          (((P : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval)) := by
              rfl
      _ =
        (Measure.map (fun ω : ℕ → StageLabel k J ↦ ω t)
            (P : Measure (ℕ → StageLabel k J))).prod
          (Measure.map id (volume : Measure unitInterval)) := by
            rw [Measure.map_prod_map _ _ (measurable_pi_apply t) measurable_id]
      _ =
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).prod volume) :
          Measure (StageLabel k J × unitInterval)) := by
            simpa [hP]
  -- Proof comment: after the base product law is normalized to the correct coarse marginal, the
  -- explicit simulator theorem reconstructs the prescribed joint law.
  calc
    Measure.map
        (fun z : (ℕ → StageLabel k J) × unitInterval ↦
          (z.1 t,
            stochasticMatrixSimulationState
              (singletonMassMatrix
                (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 t))) i z.2))
        (((P : Measure (ℕ → StageLabel k J)).prod volume) :
          Measure ((ℕ → StageLabel k J) × unitInterval)) =
    Measure.map simulate
      (Measure.map state
        (((P : Measure (ℕ → StageLabel k J)).prod volume) :
          Measure ((ℕ → StageLabel k J) × unitInterval))) := by
            symm
            exact Measure.map_map hsimulateMeas hstateMeas
    _ =
      Measure.map simulate
        ((((jointLaw.map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)).prod volume) :
          Measure (StageLabel k J × unitInterval)) := by
            rw [hstateMap]
    _ = (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) := by
          simpa [simulate] using
            map_prefixSimulator_eq_successorJointLaw (k := k) J jointLaw i

/-- Helper for Theorem 17.56: once the coarse prefix freezes and the conditional row laws at that
frozen prefix converge, the common-driver last-coordinate simulator is eventually constant. -/
private theorem ae_eventuallyEq_lastCoordinate_of_successorPrefixSimulator
    {k : ℕ → ℕ} (J : ℕ)
    (P : ProbabilityMeasure (ℕ → StageLabel k J))
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (i : Fin (k (J + 1)))
    (hprefixEvent :
      ∀ᵐ ω ∂(P : Measure (ℕ → StageLabel k J)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0)
    (hrow :
      ∀ᵐ ω ∂(P : Measure (ℕ → StageLabel k J)),
        Tendsto
          (fun n ↦ successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (ω 0))
          atTop
          (𝓝 (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0)))) :
    ∀ᵐ z ∂(((P : Measure (ℕ → StageLabel k J)).prod volume) :
      Measure ((ℕ → StageLabel k J) × unitInterval)),
      ∀ᶠ n : ℕ in atTop,
        stochasticMatrixSimulationState
          (singletonMassMatrix
            (successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (z.1 (n + 1)))) i z.2 =
          stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0))) i z.2 := by
  let simulatedPath :
      ((ℕ → StageLabel k J) × unitInterval) → ℕ → Fin (k (J + 1)) :=
    fun z n ↦
      match n with
      | 0 =>
          stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0))) i z.2
      | n + 1 =>
          stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (z.1 (n + 1)))) i z.2
  have hsimulatedPathMeas : Measurable simulatedPath := by
    refine measurable_pi_lambda simulatedPath ?_
    intro n
    cases n with
    | zero =>
        let state0 : ((ℕ → StageLabel k J) × unitInterval) → StageLabel k J × unitInterval :=
          fun z ↦ (z.1 0, z.2)
        have hstate0 : Measurable state0 := by
          fun_prop
        simpa [simulatedPath, state0] using
          (measurable_prefixSimulator
            (κ := successorStageLastCoordinateKernel (k := k) J jointLaw) i).comp hstate0
    | succ n =>
        let staten : ((ℕ → StageLabel k J) × unitInterval) → StageLabel k J × unitInterval :=
          fun z ↦ (z.1 (n + 1), z.2)
        have hstaten : Measurable staten := by
          fun_prop
        simpa [simulatedPath, staten] using
          (measurable_prefixSimulator
            (κ := successorStageLastCoordinateKernel (k := k) J (jointLawSeq n)) i).comp hstaten
  let lastEvent :
      Set ((ℕ → StageLabel k J) × unitInterval) :=
    {z | ∀ᶠ n : ℕ in atTop, simulatedPath z (n + 1) = simulatedPath z 0}
  have hlastEventMeas : MeasurableSet lastEvent := by
    have hrewrite :
        lastEvent =
          ⋃ N : ℕ,
            simulatedPath ⁻¹'
              (labelTailEvent (α := Fin (k (J + 1))) N) := by
      ext z
      simp [lastEvent, simulatedPath, labelTailEvent, Filter.eventually_atTop]
    -- Proof comment: the last-coordinate tail event is the pullback of the usual
    -- `labelTailEvent` along the measurable simulated finite path.
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      hsimulatedPathMeas (measurableSet_labelTailEvent (α := Fin (k (J + 1))) N)
  rw [Measure.ae_prod_iff_ae_ae hlastEventMeas]
  filter_upwards [hprefixEvent, hrow] with ω hωprefix hωrow
  have hboundary :
      ∀ᵐ u ∂(volume : Measure unitInterval),
        u ∉ simulationBoundarySet i
          (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0)) := by
    have hzero :
        (volume : Measure unitInterval)
            (simulationBoundarySet i
              (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0))) = 0 := by
      -- Proof comment: for a fixed frozen prefix, the limiting simulator boundary is finite, so
      -- it has zero `volume`.
      simpa using
        (simulationBoundarySet_finite i
          (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0))).countable.measure_zero
          (μ := (volume : Measure unitInterval))
    simpa using (compl_mem_ae_iff.2 hzero)
  -- Proof comment: after freezing the coarse prefix, almost every common driver avoids the
  -- limiting boundary, so the rowwise simulator stabilization theorem applies pathwise.
  filter_upwards [hboundary] with u hu
  simpa [lastEvent, simulatedPath] using
    eventuallyEq_rowwiseSimulator_of_eventuallyEq_prefix
      (i := i) hωprefix hωrow hu

/-- Helper for Theorem 17.56: literal truncation compatibility transports the already proved
stage-`J` eventual-equality event to the coarse component of any successor-stage law. -/
private theorem ae_eventuallyEq_truncate_of_successorCompat
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ)
    (dataJ : StageLabelTopLawData ν νn (k := k) (q := q) hq J)
    {PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1))}
    (hcompat :
      dataJ.law =
        PlabelSucc.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
    ∀ᵐ ω ∂(PlabelSucc : Measure (ℕ → StageLabel k (J + 1))),
      ∀ᶠ n : ℕ in atTop,
        stageLabelTruncate (k := k) J (ω (n + 1)) =
          stageLabelTruncate (k := k) J (ω 0) := by
  let truncatedEvent : Set (ℕ → StageLabel k J) :=
    {ξ | ∀ᶠ n : ℕ in atTop, ξ (n + 1) = ξ 0}
  have htruncatedEventMeas : MeasurableSet truncatedEvent := by
    have hrewrite :
        truncatedEvent = ⋃ N : ℕ, labelTailEvent (α := StageLabel k J) N := by
      ext ξ
      simp [truncatedEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      measurableSet_labelTailEvent (α := StageLabel k J) N
  have hmapped' :
      ∀ᵐ ξ ∂(dataJ.law : Measure (ℕ → StageLabel k J)), ξ ∈ truncatedEvent := by
    simpa [truncatedEvent] using dataJ.eventuallyEq
  have hmapped :
      ∀ᵐ ξ ∂((PlabelSucc.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) :
            Measure (ℕ → StageLabel k J)),
        ξ ∈ truncatedEvent := by
    simpa [hcompat] using hmapped'
  have hbase :
      ∀ᵐ ω ∂(PlabelSucc : Measure (ℕ → StageLabel k (J + 1))),
        stageLabelTruncatePath (k := k) J ω ∈ truncatedEvent := by
    exact
      (MeasureTheory.ae_map_iff
        (measurable_stageLabelTruncatePath (k := k) J).aemeasurable
        htruncatedEventMeas).1 hmapped
  -- Proof comment: the coarse successor path is the stage-`J` truncation of the fine path, so
  -- the transported event states eventual equality of those truncations with time `0`.
  simpa [truncatedEvent, stageLabelTruncatePath] using hbase

/-- Helper for Theorem 17.56: each coordinate of the simulated last-coordinate path is measurable
for the common-driver successor-stage construction. -/
private theorem measurable_successorStageSimulatedLastCoordinate
    {k : ℕ → ℕ} (J : ℕ)
    (jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))))
    (i : Fin (k (J + 1))) (n : ℕ) :
    Measurable
      (fun z : (ℕ → StageLabel k J) × unitInterval ↦
        match n with
        | 0 =>
            stochasticMatrixSimulationState
              (singletonMassMatrix
                (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0))) i z.2
        | n + 1 =>
            stochasticMatrixSimulationState
              (singletonMassMatrix
                (successorStageLastCoordinateKernel (k := k) J
                  (jointLawSeq n) (z.1 (n + 1)))) i z.2) := by
  cases n with
  | zero =>
      let state0 : ((ℕ → StageLabel k J) × unitInterval) → StageLabel k J × unitInterval :=
        fun z ↦ (z.1 0, z.2)
      have hstate0 : Measurable state0 := by
        fun_prop
      -- Proof comment: at time `0`, the simulator depends only on the frozen coarse head and the
      -- common driver coordinate.
      simpa [state0] using
        (measurable_prefixSimulator
          (κ := successorStageLastCoordinateKernel (k := k) J jointLaw) i).comp hstate0
  | succ n =>
      let staten : ((ℕ → StageLabel k J) × unitInterval) → StageLabel k J × unitInterval :=
        fun z ↦ (z.1 (n + 1), z.2)
      have hstaten : Measurable staten := by
        fun_prop
      -- Proof comment: at later times, the simulator uses the same measurable interface applied
      -- to the `n`th approximating row law.
      simpa [staten] using
        (measurable_prefixSimulator
          (κ := successorStageLastCoordinateKernel (k := k) J (jointLawSeq n)) i).comp hstaten

/-- Helper for Theorem 17.56: `stageLabelSuccEquiv` turns the reconstructed successor path back
into its coarse prefix and simulated last coordinate. -/
@[simp] private theorem stageLabelSuccEquiv_successorPath_apply
    {k : ℕ → ℕ} (J : ℕ)
    (ζ : ((ℕ → StageLabel k J) × unitInterval) → ℕ → Fin (k (J + 1)))
    (z : (ℕ → StageLabel k J) × unitInterval) (n : ℕ) :
    stageLabelSuccEquiv (k := k) J
      ((fun y m ↦
          (stageLabelSuccEquiv (k := k) J).symm (y.1 m, ζ y m)) z n) =
        (z.1 n, ζ z n) := by
  -- Proof comment: the successor-stage equivalence is the chosen normal form for the rebuilt
  -- path, so applying it cancels the `symm` constructor immediately.
  simpa using
    (stageLabelSuccEquiv (k := k) J).apply_symm_apply (z.1 n, ζ z n)

/-- Helper for Theorem 17.56: truncating the reconstructed successor path recovers the original
coarse path exactly. -/
private theorem stageLabelTruncatePath_successorPath
    {k : ℕ → ℕ} (J : ℕ)
    (ζ : ((ℕ → StageLabel k J) × unitInterval) → ℕ → Fin (k (J + 1)))
    (z : (ℕ → StageLabel k J) × unitInterval) :
    stageLabelTruncatePath (k := k) J
      (fun n ↦ (stageLabelSuccEquiv (k := k) J).symm (z.1 n, ζ z n)) = z.1 := by
  -- Proof comment: apply the product normal form coordinatewise, then read off the first
  -- component to recover the coarse stage-label path.
  funext n
  exact congrArg Prod.fst
    (stageLabelSuccEquiv_successorPath_apply (k := k) J ζ z n)

/-- Helper for Theorem 17.56: extend a prescribed stage-`J` top law to one stage higher while
keeping literal truncation compatibility, the exact bundled marginals, and almost-sure eventual
equality. -/
private theorem existsSuccessorStageLabelPathLawOverTop
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    {k : ℕ → ℕ}
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (J : ℕ)
    (hSuccTendsto :
      Tendsto
        (fun n ↦
          (νn n).map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
        atTop
        (𝓝
          (ν.map
            ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))))
    (dataJ : StageLabelTopLawData ν νn (k := k) (q := q) hq J) :
    ∃ dataSucc : StageLabelTopLawData ν νn (k := k) (q := q) hq (J + 1),
      dataJ.law =
        dataSucc.law.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable := by
  -- Route correction: the original recursive statement was too weak. Any successor-stage witness
  -- would force the stage-`J + 1` coordinate laws to converge to the head law by
  -- `tendsto_eval_probabilityMeasure_of_ae_eventuallyEq`, so the needed successor-stage
  -- pushforward convergence is now made explicit in the hypotheses.
  let jointLaw : ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) :=
    ((ν.map
        ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
      ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))
  let jointLawSeq : ℕ → ProbabilityMeasure (StageLabel k J × Fin (k (J + 1))) :=
    fun n ↦
      (((νn n).map
          ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable)).map
        ((measurable_of_finite (stageLabelSuccEquiv (k := k) J)).aemeasurable))
  have hjoint :
      Tendsto jointLawSeq atTop (𝓝 jointLaw) := by
    -- Proof comment: move the assumed fine-stage convergence into the `(prefix,last)` product
    -- normal form once so the rowwise simulator argument can stay entirely finite-state.
    simpa [jointLaw, jointLawSeq] using
      successorStageJointLawTendsto ν νn hq J hSuccTendsto
  have hprefixHead :
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))) =
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
    -- Proof comment: the first marginal of the limit joint law is exactly the prescribed
    -- stage-`J` head law.
    calc
      (((jointLaw.map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J))) =
        Measure.map (stageLabelMap (k := k) q J) (ν : Measure (ℕ → unitInterval)) := by
          simpa [jointLaw] using
            (successorStageJointLawSpec (k := k) (q := q) hq J
              (ν : Measure (ℕ → unitInterval))).1
      _ =
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rw [dataJ.head]
  have hprefixCoord :
      ∀ n : ℕ,
        (((jointLawSeq n).map measurable_fst.aemeasurable :
            ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) =
          Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (dataJ.law : Measure (ℕ → StageLabel k J)) := by
    intro n
    -- Proof comment: the same first-marginal identification holds at every later time slice.
    calc
      (((jointLawSeq n).map measurable_fst.aemeasurable :
          ProbabilityMeasure (StageLabel k J)) : Measure (StageLabel k J)) =
        Measure.map (stageLabelMap (k := k) q J) (νn n : Measure (ℕ → unitInterval)) := by
          simpa [jointLawSeq] using
            (successorStageJointLawSpec (k := k) (q := q) hq J
              (νn n : Measure (ℕ → unitInterval))).1
      _ =
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
            rw [dataJ.coord n]
  have hprefix :
      Tendsto
        (fun n ↦ (jointLawSeq n).map measurable_fst.aemeasurable)
        atTop
        (𝓝 (jointLaw.map measurable_fst.aemeasurable)) := by
    -- Proof comment: the coarse-prefix marginals of the joint laws are exactly the time
    -- evaluations of the already constructed stage-`J` path law, so `dataJ.eventuallyEq`
    -- supplies the needed convergence.
    have hprefixCoordPM :
        ∀ n : ℕ,
          (jointLawSeq n).map measurable_fst.aemeasurable =
            dataJ.law.map (measurable_pi_apply (n + 1)).aemeasurable := by
      intro n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using hprefixCoord n
    have hprefixHeadPM :
        jointLaw.map measurable_fst.aemeasurable =
          dataJ.law.map (measurable_pi_apply 0).aemeasurable := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa using hprefixHead
    simpa [hprefixCoordPM, hprefixHeadPM] using
      tendsto_eval_probabilityMeasure_of_ae_eventuallyEq
        (P := dataJ.law) dataJ.eventuallyEq
  have hrow :
      ∀ᵐ ω ∂(dataJ.law : Measure (ℕ → StageLabel k J)),
        Tendsto
          (fun n ↦ successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (ω 0))
          atTop
          (𝓝 (successorStageLastCoordinateKernel (k := k) J jointLaw (ω 0))) := by
    -- Proof comment: after isolating the positive-mass support at time `0`, the conditional row
    -- laws converge atomwise by the explicit quotient formula.
    exact
      ae_tendsto_successorStageLastCoordinateKernel_atTimeZero
        (k := k) J hprefixHead.symm hjoint hprefix
  let i0 : Fin (k (J + 1)) :=
    ⟨0, positive_lastCoordinateCard_of_successorJointProbabilityMeasure (k := k) J jointLaw⟩
  let simulatedLastCoordinate :
      ((ℕ → StageLabel k J) × unitInterval) → ℕ → Fin (k (J + 1)) :=
    fun z n ↦
      match n with
      | 0 =>
          stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0))) i0 z.2
      | n + 1 =>
          stochasticMatrixSimulationState
            (singletonMassMatrix
              (successorStageLastCoordinateKernel (k := k) J (jointLawSeq n) (z.1 (n + 1)))) i0 z.2
  let successorPath :
      ((ℕ → StageLabel k J) × unitInterval) → ℕ → StageLabel k (J + 1) :=
    fun z n ↦
      (stageLabelSuccEquiv (k := k) J).symm (z.1 n, simulatedLastCoordinate z n)
  have hsuccessorPathMeas : Measurable successorPath := by
    refine measurable_pi_lambda successorPath ?_
    intro n
    have hfirst :
        Measurable (fun z : (ℕ → StageLabel k J) × unitInterval ↦ z.1 n) := by
      exact (measurable_pi_apply n).comp measurable_fst
    have hsecond :
        Measurable (fun z : (ℕ → StageLabel k J) × unitInterval ↦ simulatedLastCoordinate z n) := by
      -- Proof comment: the successor-stage last coordinate uses the same measurable simulator
      -- interface as the earlier rowwise construction, but it is stated directly at the local
      -- normal form needed in this theorem.
      simpa [simulatedLastCoordinate] using
        measurable_successorStageSimulatedLastCoordinate
          (k := k) J jointLaw jointLawSeq i0 n
    have hpair :
        Measurable
          (fun z : (ℕ → StageLabel k J) × unitInterval ↦
            (z.1 n, simulatedLastCoordinate z n)) := by
      exact hfirst.prodMk hsecond
    simpa [successorPath] using
      (measurable_of_finite (stageLabelSuccEquiv (k := k) J).symm).comp hpair
  let unitIntervalProb : ProbabilityMeasure unitInterval :=
    ⟨volume, by infer_instance⟩
  let PlabelSucc : ProbabilityMeasure (ℕ → StageLabel k (J + 1)) :=
    (dataJ.law.prod unitIntervalProb).map hsuccessorPathMeas.aemeasurable
  have hcompat :
      dataJ.law =
        PlabelSucc.map
          (measurable_stageLabelTruncatePath (k := k) J).aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    -- Proof comment: truncating the explicitly reconstructed successor-stage path just returns the
    -- original coarse path, so the product source projects back to `dataJ.law`.
    calc
      (dataJ.law : Measure (ℕ → StageLabel k J)) =
        Measure.map Prod.fst
          ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval))) := by
              simpa using
                (Measure.map_fst_prod
                  (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
                  (ν := (volume : Measure unitInterval))).symm
      _ =
        Measure.map (stageLabelTruncatePath (k := k) J)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) := by
            rw [show (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
              Measure.map successorPath
                ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
                  Measure ((ℕ → StageLabel k J) × unitInterval))) by
                    rfl]
            rw [Measure.map_map
              (measurable_stageLabelTruncatePath (k := k) J)
              hsuccessorPathMeas]
            congr 1
            funext z
            -- Proof comment: the named truncation interface keeps this step at the coarse path
            -- level instead of expanding the entire successor-stage constructor in place.
            simpa [successorPath] using
              (stageLabelTruncatePath_successorPath
                (k := k) J simulatedLastCoordinate z).symm
  have hstageLabelSuccMeasEmb :
      MeasurableEmbedding (stageLabelSuccEquiv (k := k) J) := by
    refine ⟨(stageLabelSuccEquiv (k := k) J).injective, Measurable.of_discrete, ?_⟩
    intro s hs
    exact MeasurableSet.of_discrete
  have hheadSucc :
      Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
          (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
        Measure.map (stageLabelMap (k := k) q (J + 1))
          (ν : Measure (ℕ → unitInterval)) := by
    apply (MeasurableEmbedding.map_injective hstageLabelSuccMeasEmb)
    -- Proof comment: after moving the head law to `(prefix,last)` coordinates, the explicit
    -- simulator reconstructs the prescribed limit joint law, and `stageLabelSuccEquiv` maps the
    -- target stage-`J + 1` quantizer law to the same joint law.
    calc
      Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω 0)
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
        Measure.map
          (fun z : (ℕ → StageLabel k J) × unitInterval ↦
            (z.1 0,
              stochasticMatrixSimulationState
                (singletonMassMatrix
                  (successorStageLastCoordinateKernel (k := k) J jointLaw (z.1 0))) i0 z.2))
          ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval))) := by
              rw [show (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
                Measure.map successorPath
                  ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
                    Measure ((ℕ → StageLabel k J) × unitInterval))) by
                      rfl]
              rw [Measure.map_map
                (measurable_pi_apply 0)
                hsuccessorPathMeas]
              rw [Measure.map_map
                (measurable_of_finite (stageLabelSuccEquiv (k := k) J))
                ((measurable_pi_apply 0).comp hsuccessorPathMeas)]
              congr 1
              funext z
              -- Proof comment: normalize the head of the reconstructed successor path through the
              -- product equivalence once and reuse that normal form in the measure transport.
              simpa [successorPath] using
                stageLabelSuccEquiv_successorPath_apply
                  (k := k) J simulatedLastCoordinate z 0
      _ = (jointLaw : Measure (StageLabel k J × Fin (k (J + 1)))) := by
            exact
              map_successorStagePrefixSimulator_of_marginal
                (k := k) J dataJ.law jointLaw i0 0 hprefixHead.symm
      _ =
        Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (stageLabelMap (k := k) q (J + 1))
            (ν : Measure (ℕ → unitInterval))) := by
              rfl
  have hcoordSucc :
      ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
          Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval)) := by
    intro n
    apply (MeasurableEmbedding.map_injective hstageLabelSuccMeasEmb)
    -- Proof comment: the later time coordinates are handled by the same simulator identity, now
    -- with the `n`th joint law from the convergent successor-stage sequence.
    calc
      Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (fun ω : ℕ → StageLabel k (J + 1) ↦ ω (n + 1))
            (PlabelSucc : Measure (ℕ → StageLabel k (J + 1)))) =
        Measure.map
          (fun z : (ℕ → StageLabel k J) × unitInterval ↦
            (z.1 (n + 1),
              stochasticMatrixSimulationState
                (singletonMassMatrix
                  (successorStageLastCoordinateKernel (k := k) J
                    (jointLawSeq n) (z.1 (n + 1)))) i0 z.2))
          ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
            Measure ((ℕ → StageLabel k J) × unitInterval))) := by
              rw [show (PlabelSucc : Measure (ℕ → StageLabel k (J + 1))) =
                Measure.map successorPath
                  ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
                    Measure ((ℕ → StageLabel k J) × unitInterval))) by
                      rfl]
              rw [Measure.map_map
                (measurable_pi_apply (n + 1))
                hsuccessorPathMeas]
              rw [Measure.map_map
                (measurable_of_finite (stageLabelSuccEquiv (k := k) J))
                ((measurable_pi_apply (n + 1)).comp hsuccessorPathMeas)]
              congr 1
              funext z
              -- Proof comment: the same normalization handles each later coordinate, now with
              -- the `n`th approximating joint law.
              simpa [successorPath] using
                stageLabelSuccEquiv_successorPath_apply
                  (k := k) J simulatedLastCoordinate z (n + 1)
      _ = (jointLawSeq n : Measure (StageLabel k J × Fin (k (J + 1)))) := by
            exact
              map_successorStagePrefixSimulator_of_marginal
                (k := k) J dataJ.law (jointLawSeq n) i0 (n + 1) (hprefixCoord n).symm
      _ =
        Measure.map (stageLabelSuccEquiv (k := k) J)
          (Measure.map (stageLabelMap (k := k) q (J + 1))
            (νn n : Measure (ℕ → unitInterval))) := by
              rfl
  let coarseEvent : Set (ℕ → StageLabel k J) :=
    {ω | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0}
  have hcoarseEventMeas : MeasurableSet coarseEvent := by
    have hrewrite :
        coarseEvent = ⋃ N : ℕ, labelTailEvent (α := StageLabel k J) N := by
      ext ω
      simp [coarseEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      measurableSet_labelTailEvent (α := StageLabel k J) N
  have htruncEvent :
      ∀ᵐ z ∂((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
        Measure ((ℕ → StageLabel k J) × unitInterval))), z.1 ∈ coarseEvent := by
    -- Proof comment: the coarse eventual-equality event only depends on the first coordinate of
    -- the product source, so it pulls back directly from `dataJ.eventuallyEq`.
    have htruncEventMap :
        ∀ᵐ ω ∂(dataJ.law : Measure (ℕ → StageLabel k J)), ω ∈ coarseEvent := by
      simpa [coarseEvent] using dataJ.eventuallyEq
    have hfstMap :
        Measure.map Prod.fst
            ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
              Measure ((ℕ → StageLabel k J) × unitInterval))) =
          (dataJ.law : Measure (ℕ → StageLabel k J)) := by
      simpa using
        (Measure.map_fst_prod
          (μ := (dataJ.law : Measure (ℕ → StageLabel k J)))
          (ν := (volume : Measure unitInterval)))
    have htruncEventMap' :
        ∀ᵐ ξ ∂(Measure.map Prod.fst
            ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
              Measure ((ℕ → StageLabel k J) × unitInterval)))), ξ ∈ coarseEvent := by
      simpa [hfstMap] using htruncEventMap
    exact
      (MeasureTheory.ae_map_iff measurable_fst.aemeasurable hcoarseEventMeas).1 htruncEventMap'
  have hlastEvent :
      ∀ᵐ z ∂((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
        Measure ((ℕ → StageLabel k J) × unitInterval))),
        ∀ᶠ n : ℕ in atTop,
          simulatedLastCoordinate z (n + 1) = simulatedLastCoordinate z 0 := by
    -- Proof comment: the only genuinely new work is the stabilization of the simulated last
    -- coordinate along the frozen coarse prefix.
    simpa [simulatedLastCoordinate] using
      ae_eventuallyEq_lastCoordinate_of_successorPrefixSimulator
        (k := k) J dataJ.law jointLaw jointLawSeq i0 dataJ.eventuallyEq hrow
  let successorEvent : Set (ℕ → StageLabel k (J + 1)) :=
    {ω | ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0}
  have hsuccessorEventMeas : MeasurableSet successorEvent := by
    have hrewrite :
        successorEvent = ⋃ N : ℕ, labelTailEvent (α := StageLabel k (J + 1)) N := by
      ext ω
      simp [successorEvent, labelTailEvent, Filter.eventually_atTop]
    rw [hrewrite]
    exact MeasurableSet.iUnion fun N ↦
      measurableSet_labelTailEvent (α := StageLabel k (J + 1)) N
  have heventBase :
      ∀ᵐ z ∂((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
        Measure ((ℕ → StageLabel k J) × unitInterval))),
        ∀ᶠ n : ℕ in atTop, successorPath z (n + 1) = successorPath z 0 := by
    -- Proof comment: once both the coarse prefix and the simulated last coordinate are frozen,
    -- `stageLabelSuccEquiv.symm` rebuilds a frozen successor-stage label path.
    exact
      ae_eventuallyEq_stageLabelSucc_of_components
        (P := ((((dataJ.law : Measure (ℕ → StageLabel k J)).prod volume) :
          Measure ((ℕ → StageLabel k J) × unitInterval))))
        (k := k) J
        (ξ := fun z n ↦ z.1 n)
        (ζ := simulatedLastCoordinate)
        (by simpa [coarseEvent] using htruncEvent)
        hlastEvent
  have heventSucc :
      ∀ᵐ ω ∂(PlabelSucc : Measure (ℕ → StageLabel k (J + 1))),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0 := by
    -- Proof comment: the explicit successor-stage path law is a pushforward of the product source,
    -- so the reconstructed tail event transfers through `Measure.map`.
    exact (MeasureTheory.ae_map_iff hsuccessorPathMeas.aemeasurable hsuccessorEventMeas).2 <| by
      simpa [successorEvent, successorPath] using heventBase
  exact ⟨
    { law := PlabelSucc
      head := hheadSucc
      coord := hcoordSucc
      eventuallyEq := heventSucc },
    hcompat⟩

/-- Helper for Theorem 17.56: the chosen stage-`0` law is the base object for the recursive
compatible-family construction. -/
private noncomputable abbrev existsStageLabelTopLawDataZero
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) :
    StageLabelTopLawData ν νn (k := k) (q := q) hq 0 := by
  let law0 : ProbabilityMeasure (ℕ → StageLabel k 0) :=
    chosenStageLabelPathLaw ν νn hνn hk hq hfrontier 0
  have hspec0 :
      Measure.map (fun ω : ℕ → StageLabel k 0 ↦ ω 0)
          (law0 : Measure (ℕ → StageLabel k 0)) =
        Measure.map (stageLabelMap (k := k) q 0) (ν : Measure (ℕ → unitInterval)) ∧
      (∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k 0 ↦ ω (n + 1))
            (law0 : Measure (ℕ → StageLabel k 0)) =
          Measure.map (stageLabelMap (k := k) q 0)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ᵐ ω ∂(law0 : Measure (ℕ → StageLabel k 0)),
        ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
    -- Proof comment: unfold the chosen stage-`0` witness once so the recursive base stores the
    -- exact bundled marginals and eventual-equality event in a stable owner API.
    simpa [law0] using
      chosenStageLabelPathLaw_spec ν νn hνn hk hq hfrontier 0
  exact
    { law := law0
      head := hspec0.1
      coord := hspec0.2.1
      eventuallyEq := hspec0.2.2 }

/-- Helper for Theorem 17.56: recursively extending the stage top laws yields a compatible family
whose every stage still has almost-sure eventual equality with time `0`. -/
private theorem existsCompatibleStageLabelFamilyWithEventuallyEq
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) ∧
      (∀ J : ℕ,
        ∀ᵐ ω ∂(PlabelStage J : Measure (ℕ → StageLabel k J)),
          ∀ᶠ n : ℕ in atTop, ω (n + 1) = ω 0) := by
  let stageData : ∀ J : ℕ, StageLabelTopLawData ν νn (k := k) (q := q) hq J :=
    Nat.rec
      (motive := fun J => StageLabelTopLawData ν νn (k := k) (q := q) hq J)
      (existsStageLabelTopLawDataZero ν νn hνn hk hq hfrontier)
      (fun J dataJ ↦
        let hSuccTendsto :
            Tendsto
              (fun n ↦
                (νn n).map
                  ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))
              atTop
              (𝓝
                (ν.map
                  ((measurable_stageLabelMap (k := k) (q := q) hq (J + 1)).aemeasurable))) :=
          tendstoStageLabelPushforward_of_nullFrontierSingletons
            ν νn hνn hq hfrontier (J + 1)
        Classical.choose <|
          existsSuccessorStageLabelPathLawOverTop
            ν νn (k := k) (q := q) hq J hSuccTendsto dataJ)
  refine ⟨fun J ↦ (stageData J).law, ?_, ?_, ?_, ?_⟩
  · intro J
    -- Proof comment: every recursive stage remembers its exact head marginal as part of the
    -- stored top-law data, so the final family reads it off directly.
    exact (stageData J).head
  · intro J n
    -- Proof comment: the same stored top-law data carries every time-`n + 1` marginal
    -- unchanged.
    exact (stageData J).coord n
  · intro J
    let hsucc :=
      existsSuccessorStageLabelPathLawOverTop
        ν νn (k := k) (q := q) hq J
        (tendstoStageLabelPushforward_of_nullFrontierSingletons
          ν νn hνn hq hfrontier (J + 1))
        (stageData J)
    -- Proof comment: the recursive successor witness stores literal truncation compatibility, so
    -- the final family inherits that compatibility stage by stage.
    simpa [stageData, hsucc] using (Classical.choose_spec hsucc)
  · intro J
    -- Proof comment: each recursive stage also stores the almost-sure eventual-equality event
    -- needed later for the deterministic cutoff extraction.
    exact (stageData J).eventuallyEq

/-- Helper for Theorem 17.56: the direct stage-family route only needs one extra owner theorem
showing that the recursive compatible stage-label family carries the full dyadic cutoff table. -/
private theorem existsCompatibleChosenStageLabelFamilyWithCutoffTable
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν))
    {k : ℕ → ℕ} (hk : ∀ m : ℕ, 0 < k m)
    {q : ∀ m : ℕ, (ℕ → unitInterval) → Fin (k m)}
    (hq : ∀ m : ℕ, Measurable (q m))
    (hfrontier :
      ∀ m : ℕ, ∀ a : Fin (k m),
        (ν : Measure (ℕ → unitInterval)) (frontier (q m ⁻¹' {a})) = 0) :
    ∃ PlabelStage : ∀ J : ℕ, ProbabilityMeasure (ℕ → StageLabel k J),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω 0)
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ, ∀ n : ℕ,
        Measure.map (fun ω : ℕ → StageLabel k J ↦ ω (n + 1))
            (PlabelStage J : Measure (ℕ → StageLabel k J)) =
          Measure.map (stageLabelMap (k := k) q J)
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ J : ℕ,
        PlabelStage J =
          (PlabelStage (J + 1)).map
            (measurable_stageLabelTruncatePath (k := k) J).aemeasurable) ∧
      (∀ m r : ℕ, ∃ N : ℕ,
        (1 : ℝ≥0∞) - ((↑((1 / 2 : ℝ≥0) ^ (r + 1)) : ℝ≥0∞)) <
          (PlabelStage m : Measure (ℕ → StageLabel k m))
            (labelTailEvent (α := StageLabel k m) N)) := by
  obtain ⟨PlabelStage, hheadStage, hcoordStage, hcompatStage, heventStage⟩ :=
    existsCompatibleStageLabelFamilyWithEventuallyEq
      ν νn hνn hk hq hfrontier
  refine ⟨PlabelStage, hheadStage, hcoordStage, hcompatStage, ?_⟩
  intro m r
  let ε : ℝ≥0 := (1 / 2 : ℝ≥0) ^ (r + 1)
  have hε : 0 < ε := by
    -- Proof comment: the dyadic error budget is strictly positive, so the generic deterministic
    -- tail-cutoff lemma can be applied directly at stage `m`.
    dsimp [ε]
    positivity
  obtain ⟨N, hN⟩ :=
    exists_labelTailEvent_highProb_of_ae_eventuallyEq
      (α := StageLabel k m) (P := PlabelStage m) (heventStage m) ε hε
  -- Proof comment: once each stage top law is almost surely eventually constant, its full dyadic
  -- cutoff table is recovered directly by the generic label-tail extraction theorem.
  exact ⟨N, by simpa [ε] using hN⟩

/-- Helper for Theorem 17.56: once the compatible extracted stage-label family carries the full
stage-level cutoff table, the ambient stage-law transport closes the approximate-stage-family
statement directly. -/
private theorem existsApproximateHilbertCubeStageFamily_ofCompatibleChosenStages
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    ∃ Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
          (1 : ℝ≥0∞) - ε <
            (Pstage J : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) := by
  obtain ⟨k, hk, q, hq, hfrontier, hdiam⟩ := existsDyadicHilbertCubeQuantizerTower ν
  obtain ⟨PlabelStage, hheadStage, hcoordStage, hcompatStage, hcutoffStage⟩ :=
    existsCompatibleChosenStageLabelFamilyWithCutoffTable
      ν νn hνn hk hq hfrontier
  have hprojCompat :
      ∀ {m J : ℕ} (hmJ : m ≤ J),
        (projectedStageLabelPathLaw (k := k) (J := J) (m := m) hmJ
          (PlabelStage J) : Measure (ℕ → Fin (k m))) =
          (projectedStageLabelPathLaw (k := k) (J := m) (m := m) le_rfl
            (PlabelStage m) : Measure (ℕ → Fin (k m))) := by
    intro m J hmJ
    -- Proof comment: literal successor truncation compatibility is exactly the hypothesis needed
    -- by the existing coarse-projection normalization theorem.
    exact projectedStageLabelPathLaw_eq_of_compatibleFamily
      (k := k) PlabelStage hcompatStage hmJ
  let Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)) := fun J ↦
    ambientStageLabelPathLaw
      (ν := ν) (νn := νn) (k := k) (q := q) hq J (PlabelStage J)
      (hheadStage J) (hcoordStage J) hdiam
  refine ⟨Pstage, ?_, ?_, ?_⟩
  · intro J
    -- Proof comment: each ambient stage law preserves the exact head marginal packaged in the
    -- compatible stage-label family.
    simpa [Pstage] using
      ambientStageLabelPathLaw_head
        (ν := ν) (νn := νn) (k := k) (q := q) hq J (PlabelStage J)
        (hheadStage J) (hcoordStage J) hdiam
  · intro n J hnJ
    -- Proof comment: the same fixed ambient stage law preserves every time-`n + 1` marginal.
    simpa [Pstage] using
      ambientStageLabelPathLaw_coord
        (ν := ν) (νn := νn) (k := k) (q := q) hq J (PlabelStage J)
        (hheadStage J) (hcoordStage J) hdiam n
  · intro m ε hε
    obtain ⟨N, hN⟩ :=
      eventually_projectedLabelTail_highProb_ofCompatibleStageLabelCutoffs
        (k := k) m PlabelStage
        (fun J hmJ ↦ hprojCompat hmJ)
        (hcutoffStage m) hε
    refine ⟨N, ?_⟩
    -- Proof comment: first freeze the coarse projected cutoff at scale `m`, then transport it
    -- through the ambient stage witness for every sufficiently large `J`.
    filter_upwards [hN, Filter.eventually_atTop.2 ⟨m, fun J hJ ↦ hJ⟩] with J hJ hmJ
    exact ambientStageLabelPathLaw_projected_dyadicTail
      (ν := ν) (νn := νn) (k := k) (q := q) hq J (PlabelStage J)
      (hheadStage J) (hcoordStage J) hdiam (m := m) hmJ
      (ε := ε) (N := N) (hJ hmJ)

/-- Helper for Theorem 17.56: the only remaining compact-core frontier is the approximate stage
family whose fixed-time marginals are exact and whose dyadic tail events are eventually
high-probability. -/
private theorem existsApproximateHilbertCubeStageFamily
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    ∃ Pstage : ℕ → ProbabilityMeasure (ℕ → (ℕ → unitInterval)),
      (∀ J : ℕ,
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω 0)
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (ν : Measure (ℕ → unitInterval))) ∧
      (∀ n J : ℕ, n ≤ J →
        Measure.map (fun ω : ℕ → (ℕ → unitInterval) ↦ ω (n + 1))
          (Pstage J : Measure (ℕ → (ℕ → unitInterval))) =
            (νn n : Measure (ℕ → unitInterval))) ∧
      (∀ m : ℕ, ∀ ε : ℝ≥0, 0 < ε →
        ∃ N : ℕ, ∀ᶠ J : ℕ in atTop,
          (1 : ℝ≥0∞) - ε <
            (Pstage J : Measure (ℕ → (ℕ → unitInterval))) (dyadicTailEvent m N)) := by
  -- Route correction: stop routing through the stronger ambient-cutoff-table theorem. The live
  -- frontier is now the smaller owner theorem that the compatible extracted stage-label family
  -- inherits the stage-level cutoff table needed by the direct ambient stage-family transport.
  exact existsApproximateHilbertCubeStageFamily_ofCompatibleChosenStages ν νn hνn

/-- Helper for Theorem 17.56: the remaining theorem-local frontier is the compact Hilbert-cube
realization with dyadic tail control. -/
theorem existsHilbertCubeDyadicTailRealization
    (ν : ProbabilityMeasure (ℕ → unitInterval))
    (νn : ℕ → ProbabilityMeasure (ℕ → unitInterval))
    (hνn : Tendsto νn atTop (𝓝 ν)) :
    ∃ (Ω : Type v) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (Y : Ω → ℕ → unitInterval) (Yn : ℕ → Ω → ℕ → unitInterval),
      HasLaw Y ν P ∧
        (∀ n : ℕ, HasLaw (Yn n) (νn n) P) ∧
        (∀ m : ℕ, ∀ᵐ ω ∂(P : Measure Ω),
            ∀ᶠ n : ℕ in atTop,
              @Dist.dist (ℕ → unitInterval) PiCountable.dist (Yn n ω) (Y ω) ≤
                (1 / 2 : ℝ) ^ m) := by
  -- Route correction: the compact core is now isolated in this theorem-local support file,
  -- instead of living as one large inline block in the main theorem wrapper.
  -- Proof comment: the compactness/Portmanteau extraction step is now packaged in
  -- `existsHilbertCubeDyadicTailRealizationOfApproxStageLaws`, so the only remaining frontier is
  -- the upstream approximate stage-law constructor.
  have hstageFamily := existsApproximateHilbertCubeStageFamily ν νn hνn
  rcases hstageFamily with ⟨Pstage, hhead, hcoord, hdyadic⟩
  exact existsHilbertCubeDyadicTailRealizationOfApproxStageLaws
    ν νn Pstage hhead hcoord hdyadic

end GenericAmbient

end ProbabilityTheory
