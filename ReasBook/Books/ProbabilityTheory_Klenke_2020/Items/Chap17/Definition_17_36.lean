/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/-
Layering for Definition 17.36:
- `IsIrreducibleMarkovChain` and `IsWeaklyIrreducibleMarkovChain` remain the source-facing
  Chapter 17 positivity predicates for `F[P, X]`.
- `Kernel.IsIrreducible (Measure.count) _` is the core/canonical owner notion for discrete kernels;
  its `n = 0` case explains why off-diagonal communication is often the right bridge formulation.
- `greenFunctionFrom` is the owner abstraction for positive-time visit counts; its `N = 1`
  specialization is used only in the realization-scoped bridge theorem below.
-/

/-- Definition 17.36: a discrete Markov chain is irreducible if every state `y` is reached from
every starting state `x` with strictly positive ever-hit probability `F(x,y)`. -/
def IsIrreducibleMarkovChain (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x y : E, 0 < (F[P, X]) x y

/-- A discrete Markov chain is weakly irreducible if for every pair of states at least one of the
two directed ever-hit probabilities is strictly positive. -/
def IsWeaklyIrreducibleMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ x y : E, 0 < (F[P, X]) x y + (F[P, X]) y x

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Helper for Definition 17.36: a positive positive-time Green mass yields a concrete positive
singleton transition mass at some positive time. -/
lemma existsPosStepMass_of_greenFunctionFrom_one_pos
    {κ : ℕ → Kernel E E} (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization κ P X] {x y : E}
    (hxy : 0 < (G[P, X; 1]) x y) :
    ∃ n : ℕ, 0 < n ∧ 0 < (κ n) x ({y} : Set E) := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: expand `G[P, X; 1]` into the nonnegative series of positive-time singleton
  -- events and extract one strictly positive summand.
  have hterm :
      ∃ n : ℕ, 0 < (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} := by
    by_contra hnot
    have hzero :
        ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro n
      exact le_antisymm (le_of_not_gt fun hn ↦ hnot ⟨n, hn⟩) bot_le
    rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hproc x y, hzero] at hxy
    exact lt_irrefl _ hxy
  rcases hterm with ⟨n, hn⟩
  have hnpos : 0 < n := by
    by_contra hnpos
    have hzeroEvent :
        (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = 0 := by
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      simp
    exact hzeroEvent.not_gt hn
  have hstep :
      (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} = (κ n) x ({y} : Set E) := by
    have hpreimage : {ω | 0 < n ∧ X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp [hnpos]
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x n]
  have hmass : 0 < (κ n) x ({y} : Set E) := by
    simpa [hstep] using hn
  exact ⟨n, hnpos, hmass⟩

/-- Helper for Definition 17.36: a positive singleton transition mass at a positive time forces
the positive-time Green function to be positive. -/
lemma greenFunctionFrom_one_pos_of_posStepMass
    {κ : ℕ → Kernel E E} (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization κ P X] {x y : E} {n : ℕ}
    (hn : 0 < n) (hstep : 0 < (κ n) x ({y} : Set E)) :
    0 < (G[P, X; 1]) x y := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hproc : IsStochasticProcess X := fun m ↦ hReal.measurable_process m
  -- Proof comment: the time-`n` singleton event is one nonzero summand in the Green-series
  -- expansion, so the whole series is positive.
  rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hproc x y]
  have hterm :
      0 < (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} := by
    have hpreimage : {ω | 0 < n ∧ X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp [hn]
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x n]
    simpa using hstep
  exact lt_of_lt_of_le hterm (ENNReal.le_tsum n)

/-- Helper for Definition 17.36: composing two positive singleton masses yields a positive
singleton mass for the composed kernel. -/
lemma compSingletonMass_pos_of_posSingletonMass
    {κ η : Kernel E E} {x y z : E}
    (hxy : 0 < κ x ({y} : Set E)) (hyz : 0 < η y ({z} : Set E)) :
    0 < (η ∘ₖ κ) x ({z} : Set E) := by
  have hmeas : Measurable fun w : E ↦ η w ({z} : Set E) :=
    Kernel.measurable_coe η (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : E ↦ η w ({z} : Set E) := by
    simpa [Function.mem_support] using hyz.ne'
  have hsupportPos :
      0 < (κ x) (Function.support fun w : E ↦ η w ({z} : Set E)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the support already contains the
  -- intermediate state carrying positive tail mass.
  rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Definition 17.36: off-diagonal positivity of `G[P, X; 1]` forces diagonal
positivity as well. -/
lemma selfGreenFunctionFrom_one_pos_of_offDiagonal
    {κ : ℕ → Kernel E E} (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization κ P X]
    (hoff : ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y) :
    ∀ x : E, 0 < (G[P, X; 1]) x x := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  intro x
  by_cases hsub : Subsingleton E
  · -- Proof comment: on a subsingleton state space the time-`1` singleton event is the whole
    -- space, so its kernel mass is positive immediately.
    have hstep : 0 < (κ 1) x ({x} : Set E) := by
      rw [← hReal.transition_eq x 1]
      rw [Measure.map_apply (hReal.measurable_process 1) (MeasurableSet.singleton x)]
      have hpreimage : X 1 ⁻¹' ({x} : Set E) = Set.univ := by
        ext ω
        simp [hsub.elim (X 1 ω) x]
      rw [hpreimage]
      simp
    have hone : 0 < (1 : ℕ) := by simp
    exact greenFunctionFrom_one_pos_of_posStepMass P X hone hstep
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨y, hyx⟩ := exists_ne x
    rcases existsPosStepMass_of_greenFunctionFrom_one_pos (κ := κ) P X (hoff hyx.symm) with
      ⟨n, hn, hxy⟩
    rcases existsPosStepMass_of_greenFunctionFrom_one_pos (κ := κ) P X (hoff hyx) with
      ⟨m, hm, hyxMass⟩
    have hreturn : 0 < (κ (n + m)) x ({x} : Set E) := by
      have hcomp :
          0 < ((κ m) ∘ₖ (κ n)) x ({x} : Set E) :=
        compSingletonMass_pos_of_posSingletonMass hxy hyxMass
      simpa [hReal.semigroup.comp_eq n m] using hcomp
    exact greenFunctionFrom_one_pos_of_posStepMass P X (add_pos hn hm) hreturn

-- Proof sketch: under the realization semantics, off-diagonal communication is the kernel-style
-- notion; convert it pointwise to `G[P, X; 1]` via
-- `greenFunctionFrom_one_pos_iff_everHitsProbability_pos`.
/-- Auxiliary bridge: for a measurable Markov-process realization started from its initial state,
the source-facing irreducibility predicate is equivalent to strict positivity of the positive-time
Green function `G[P, X; 1] x y` on off-diagonal pairs. -/
theorem isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
    {κ : ℕ → Kernel E E} (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization κ P X] :
    IsIrreducibleMarkovChain P X ↔
      ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
  let hReal : IsMarkovProcessRealization κ P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  constructor
  · intro hirr x y hxy
    -- Proof comment: irreducibility gives positivity of `F[P, X]`; the owner bridge turns that
    -- directly into positivity of `G[P, X; 1]`.
    exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).2 (hirr x y)
  · intro hgreen x y
    by_cases hxy : x = y
    · subst hxy
      have hdiag : 0 < (G[P, X; 1]) x x :=
        selfGreenFunctionFrom_one_pos_of_offDiagonal (κ := κ) P X hgreen x
      -- Proof comment: after recovering the diagonal Green positivity, the same owner bridge
      -- converts back to the ever-hit probability.
      exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x x).1 hdiag
    · -- Proof comment: the off-diagonal case is exactly the hypothesis `hgreen`.
      exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x y).1 (hgreen hxy)

end MeasurableState

-- Proof sketch: if every directed ever-hit probability is positive, then for each pair `(x, y)`
-- the sum `F(x,y) + F(y,x)` is positive as well.
/-- Every irreducible Markov chain is weakly irreducible. -/
theorem isWeaklyIrreducibleMarkovChain_of_isIrreducibleMarkovChain
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (h : IsIrreducibleMarkovChain P X) :
    IsWeaklyIrreducibleMarkovChain P X := by
  intro x y
  -- Proof comment: the first summand is already strictly positive, and the second summand is a
  -- nonnegative probability.
  exact add_pos_of_pos_of_nonneg (h x y) MeasureTheory.measureReal_nonneg

end ProbabilityTheory
