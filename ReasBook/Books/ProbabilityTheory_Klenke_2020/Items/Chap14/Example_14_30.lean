/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval
open unitInterval

private noncomputable def coinTossingMeasure (n : ℕ) (p : ↑I) : Measure (Fin n → Bool) :=
  Measure.pi fun _ : Fin n ↦
    (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure

/-- Helper for Example 14.30: reflection on `[0,1]` rewrites the complementary Bernoulli mass as
the reflected parameter `σ p`. -/
private lemma one_sub_toNNReal_eq_toNNReal_symm (p : ↑I) :
    1 - toNNReal p = toNNReal (σ p) := by
  -- The involution `σ` exchanges the two coordinates in the identity `p + (1 - p) = 1`.
  apply tsub_eq_of_eq_add
  rw [unitInterval.toNNReal_symm_add_toNNReal]

/-- Helper for Example 14.30: the Bernoulli atom masses on `Bool` vary measurably with the
parameter `p ∈ [0,1]`. -/
private lemma bernoulliBoolAtomMeasurable (b : Bool) :
    Measurable
      (fun p : ↑I ↦ ((PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure) {b}) := by
  cases b with
  | false =>
      -- Rewrite the `false` atom through the reflection `σ` so that only `toNNReal` remains.
      simpa [one_sub_toNNReal_eq_toNNReal_symm, PMF.toMeasure_apply_singleton,
        PMF.bernoulli_apply] using
        (unitInterval.toNNReal_continuous.measurable.comp unitInterval.measurable_symm)
  | true =>
      -- The `true` atom is exactly the parameter `p`.
      simpa [PMF.toMeasure_apply_singleton, PMF.bernoulli_apply] using
        unitInterval.toNNReal_continuous.measurable

/-- Helper for Example 14.30: the mass of each singleton in `{0,1}^n` is a measurable function of
the Bernoulli parameter. -/
private lemma coinTossingSingletonMassMeasurable (n : ℕ) (ω : Fin n → Bool) :
    Measurable (fun p : ↑I ↦ coinTossingMeasure n p {ω}) := by
  -- Rewrite singleton masses of the product measure as a finite product of coordinate atom masses.
  simpa [coinTossingMeasure] using
    (Finset.measurable_prod (s := Finset.univ) fun i _ ↦ bernoulliBoolAtomMeasurable (ω i))

/-- Helper for Example 14.30: on the finite state space `Fin n → Bool`, every measurable set mass
is the finite sum of its singleton masses. -/
private lemma coinTossingMeasure_apply_eq_sumSingletons (n : ℕ) (s : Set (Fin n → Bool)) (p : ↑I) :
    coinTossingMeasure n p s =
      Finset.sum (s.toFinite.toFinset) fun ω ↦ coinTossingMeasure n p {ω} := by
  classical
  -- Replace the set by the finite union of its singleton atoms.
  let t : Finset (Fin n → Bool) := s.toFinite.toFinset
  have hUnion : (⋃ ω ∈ t, ({ω} : Set (Fin n → Bool))) = s := by
    simp [t]
  rw [← hUnion]
  -- The atoms are pairwise disjoint, so the measure is a finite sum.
  have hBiUnion :
      coinTossingMeasure n p (⋃ ω ∈ t, ({ω} : Set (Fin n → Bool))) =
        Finset.sum t fun ω ↦ coinTossingMeasure n p {ω} := by
    exact
      (measure_biUnion_finset (μ := coinTossingMeasure n p)
        (s := t) (f := fun ω ↦ ({ω} : Set (Fin n → Bool)))
        (fun ω _ τ _ hωτ ↦ Set.disjoint_singleton.2 hωτ)
        (fun ω _ ↦ measurableSet_singleton ω))
  simp [t] at hBiUnion ⊢

/-- Helper for Example 14.30: every measurable set in `{0,1}^n` has measurable mass under the
Bernoulli product family. -/
private lemma coinTossingSetMassMeasurable (n : ℕ) (s : Set (Fin n → Bool)) :
    Measurable (fun p : ↑I ↦ coinTossingMeasure n p s) := by
  -- After decomposing `s` into finitely many atoms, measurability follows from finite sums.
  have hsum :
      (fun p : ↑I ↦ coinTossingMeasure n p s) =
        fun p : ↑I ↦ Finset.sum (s.toFinite.toFinset) fun ω ↦ coinTossingMeasure n p {ω} := by
    funext p
    exact coinTossingMeasure_apply_eq_sumSingletons n s p
  rw [hsum]
  exact Finset.measurable_sum (s := s.toFinite.toFinset) fun ω _ ↦
    coinTossingSingletonMassMeasurable n ω

/-- Example 14.30: the family of Bernoulli product measures depends measurably on the parameter
`p ∈ [0,1]`, so it defines a stochastic kernel from `[0,1]` to `{0,1}^n`. -/
-- Proof sketch: On the finite space `Fin n → Bool`, it is enough to check measurability of the
-- mass of each measurable set, and those masses are finite polynomial expressions in `p`.
private theorem coinTossingMeasure_measurable (n : ℕ) : Measurable (coinTossingMeasure n) := by
  -- Measure-valued measurability reduces to measurability of every measurable set mass.
  refine Measure.measurable_measure.mpr fun s hs ↦ ?_
  exact coinTossingSetMassMeasurable n s

/-- The stochastic kernel sending `p ∈ [0,1]` to the `n`-fold Bernoulli product law with
success probability `p`. -/
noncomputable def coinTossingKernel (n : ℕ) : Kernel ↑I (Fin n → Bool) :=
  ⟨coinTossingMeasure n, coinTossingMeasure_measurable n⟩

/-- At parameter `p`, `coinTossingKernel n` is the Bernoulli product measure on `Fin n → Bool`
with success probability `p`. -/
@[simp]
theorem coinTossingKernel_apply (n : ℕ) (p : ↑I) :
    coinTossingKernel n p =
      Measure.pi fun _ : Fin n ↦
        (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure :=
  rfl

/-- The joint measure from Example 14.30 obtained by choosing a uniform parameter `p ∈ [0,1]`
and, conditionally on `p`, sampling `n` independent Bernoulli variables with success probability
`p`. Here `{0,1}^n` is represented by `Fin n → Bool`. -/
noncomputable def coinTossingUniformMixture (n : ℕ) : Measure (↑I × (Fin n → Bool)) :=
  (volume : Measure ↑I) ⊗ₘ coinTossingKernel n

/-- The Bernoulli product family defines a Markov kernel from `[0,1]` to `{0,1}^n`. -/
-- Proof sketch: Each fiber is a product of probability measures on `Bool`, so every fiber has
-- total mass `1`; the kernel measurability is exactly `coinTossingMeasure_measurable`.
theorem coinTossingKernel_isMarkovKernel (n : ℕ) :
    IsMarkovKernel (coinTossingKernel n) := by
  refine ⟨fun p ↦ ?_⟩
  simpa [coinTossingKernel_apply] using
    (inferInstance : IsProbabilityMeasure
      (Measure.pi fun _ : Fin n ↦
        (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).toMeasure))

/-- The Bernoulli product kernel carries the canonical Markov-kernel instance. -/
instance (n : ℕ) : IsMarkovKernel (coinTossingKernel n) :=
  coinTossingKernel_isMarkovKernel n

/-- The first coordinate under the joint mixture law is uniformly distributed on `[0,1]`. -/
-- Proof sketch: The first marginal of a composition-product `μ ⊗ₘ κ` is `μ`, so the first
-- coordinate has law `volume` on the unit interval.
theorem coinTossingUniformMixture_fst_hasLaw (n : ℕ) :
    HasLaw Prod.fst (volume : Measure ↑I) (coinTossingUniformMixture n) where
  map_eq := by
    change (coinTossingUniformMixture n).fst = (volume : Measure ↑I)
    exact Measure.fst_compProd (volume : Measure ↑I) (coinTossingKernel n)

/-- The joint measure of the example is itself a probability measure. -/
-- Proof sketch: `volume` on the unit interval is a probability measure, and the previous theorem
-- upgrades `coinTossingKernel n` to a Markov kernel; then `μ ⊗ₘ κ` is a probability measure.
theorem coinTossingUniformMixture_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (coinTossingUniformMixture n) := by
  simpa [coinTossingUniformMixture] using
    (inferInstance : IsProbabilityMeasure ((volume : Measure ↑I) ⊗ₘ coinTossingKernel n))

/-- The second marginal of the joint law is the mixture of the Bernoulli product kernel against
the uniform parameter measure. -/
-- Proof sketch: This is the standard `snd_compProd` identity for composition-products of a measure
-- and a kernel, applied to the concrete joint measure of this example.
theorem coinTossingUniformMixture_snd_eq (n : ℕ) :
    (coinTossingUniformMixture n).snd = coinTossingKernel n ∘ₘ (volume : Measure ↑I) := by
  change (((volume : Measure ↑I) ⊗ₘ coinTossingKernel n).snd =
    coinTossingKernel n ∘ₘ (volume : Measure ↑I))
  exact Measure.snd_compProd (volume : Measure ↑I) (coinTossingKernel n)
