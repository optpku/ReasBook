/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section RecurrentOrTransient

variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

include p P X

/- Theorem 17.37 (1) is source-facing: its main irreducibility hypothesis is the chapter API
`IsIrreducibleMarkovChain P X`. The discrete-kernel irreducibility of `discreteMatrixKernel p`
is the concrete model-specific bridge to that source-facing notion. -/

-- Proof sketch: apply kernel irreducibility to singleton state sets, then use the realization
-- marginal identity `(P x).map (X n) = (discreteMatrixKernel p ^ n) x` to obtain a positive-time
-- hit of each state from every initial state.
/-- The discrete-kernel irreducibility of the transition matrix yields the Chapter 17
irreducibility predicate for any realization of that chain. -/
theorem isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsIrreducibleMarkovChain P X := by
  have hgreen :
      ∀ ⦃x y : E⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure E) ({y} : Set E) := by
      simp
    -- Proof comment: irreducibility of the owner kernel produces a positive singleton mass at a
    -- positive time, and the positive-time Green function records exactly those positive-time
    -- visits in aggregate.
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E)
        (discreteMatrixKernel p)).irreducible
        (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzero : ((discreteMatrixKernel p ^ 0) x) ({y} : Set E) = 0 := by
        change (Kernel.id x) ({y} : Set E) = 0
        simp [Kernel.id_apply, hxy]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun m ↦ discreteMatrixKernel p ^ m) P X hnpos hn
  -- Proof comment: the Chapter 17 irreducibility predicate is equivalent to off-diagonal
  -- positivity of the positive-time Green function.
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).2 hgreen

omit [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] in
omit [MeasurableSpace E] [DiscreteMeasurableSpace E] p in
/-- Helper for Theorem 17.37: if a state is not recurrent, then it is transient. -/
private lemma isTransientState_of_not_isRecurrentState
    {x : E} (hx : ¬ IsRecurrentState P X x) :
    IsTransientState P X x := by
  have hxx_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: the return probability is always at most `1`, so failure of the recurrent
  -- identity forces it to be strictly smaller than `1`.
  rw [IsTransientState]
  by_contra hnot_transient
  have hxx_ge_one : 1 ≤ (F[P, X]) x x := le_of_not_gt hnot_transient
  have hxx_eq_one : (F[P, X]) x x = 1 := le_antisymm hxx_le_one hxx_ge_one
  exact hx <| by simpa [IsRecurrentState] using hxx_eq_one

/-- Helper for Theorem 17.37: irreducibility forces the discrete state space to be countable. -/
private lemma countable_of_isIrreducibleMarkovChain
    (hirr : IsIrreducibleMarkovChain P X) :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E :=
      fun n ↦ {y : E | 0 < ((discreteMatrixKernel p ^ n) x₀) ({y} : Set E)}
    have hreachable_countable : ∀ n : ℕ, (reachable n).Countable := by
      intro n
      let μ : Measure E := ((discreteMatrixKernel p ^ n) x₀)
      let hReal : IsMarkovProcessRealization
          (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
      letI : IsMarkovKernel (discreteMatrixKernel p ^ n) := hReal.semigroup.isMarkovKernel n
      letI : IsProbabilityMeasure μ := inferInstance
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        let hReal : IsMarkovProcessRealization
            (fun k : ℕ ↦ discreteMatrixKernel p ^ k) P X := inferInstance
        let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
        have hgreen : 0 < (G[P, X; 1]) x₀ y := by
          exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc x₀ y).2
            (hirr x₀ y)
        rcases existsPosStepMass_of_greenFunctionFrom_one_pos
            (κ := fun n ↦ discreteMatrixKernel p ^ n) P X hgreen with ⟨n, _, hmass⟩
        exact Set.mem_iUnion.2 ⟨n, by simpa [reachable] using hmass⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

-- Proof sketch: once irreducibility forces `E` to be countable, Theorem 17.35 transports
-- recurrence along the strictly positive ever-hit probabilities given by `hirr`.
/-- Theorem 17.37 (1): an irreducible discrete Markov chain is either recurrent or transient. -/
theorem irreducibleMarkovChain_recurrent_or_transient
    (hirr : IsIrreducibleMarkovChain P X) :
    IsRecurrentMarkovChain P X ∨ ∀ x : E, IsTransientState P X x := by
  classical
  letI : Countable E := countable_of_isIrreducibleMarkovChain
    (p := p) (P := P) (X := X) hirr
  by_cases hE : IsEmpty E
  · left
    intro x
    exact False.elim (hE.false x)
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    by_cases hx₀ : IsRecurrentState P X x₀
    · left
      intro y
      -- Proof comment: specialize Theorem 17.35 to the realized discrete-kernel semigroup so
      -- instance search uses the existing `IsMarkovProcessRealization` witness.
      exact isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) hx₀ (hirr x₀ y)
    · right
      intro y
      apply isTransientState_of_not_isRecurrentState (P := P) (X := X)
      intro hy
      -- Proof comment: the same discrete-kernel specialization transports recurrence back from
      -- `y` to the base state `x₀`, contradicting the nonrecurrent branch assumption.
      exact hx₀ <|
        isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
          (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) hy (hirr y x₀)

-- Proof sketch: first pass from the discrete-kernel irreducibility of `p` to the source-facing
-- chapter predicate `IsIrreducibleMarkovChain P X`, then apply Theorem 17.37 (1).
/-- The kernel-style specialization of Theorem 17.37 (1) for realizations of a stochastic matrix.
-/
theorem irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    IsRecurrentMarkovChain P X ∨ ∀ x : E, IsTransientState P X x :=
  irreducibleMarkovChain_recurrent_or_transient (p := p) (P := P) (X := X)
    (isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X)

end RecurrentOrTransient

section NoAbsorbingState

variable [Nontrivial E]
variable (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

include p P X

omit [Nontrivial E] in
/-- Helper for Theorem 17.37: any one-step transition matrix realized by `X` is stochastic. -/
private lemma stochasticMatrix_of_realization :
    IsStochasticMatrix p := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  letI : IsMarkovKernel ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) :=
    hReal.semigroup.isMarkovKernel 1
  intro x
  -- Proof comment: the time-`1` kernel of the realization is Markov, so its row at `x` has total
  -- mass `1`; for the discrete matrix kernel that total mass is exactly `∑' y, p x y`.
  calc
    ∑' y : E, p x y = discreteMatrixKernel p x Set.univ := by
      symm
      rw [discreteMatrixKernel_univ]
    _ = ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ := by
      simp
    _ = 1 := by
      simpa using
        (measure_univ :
          ((fun n : ℕ ↦ discreteMatrixKernel p ^ n) 1) x Set.univ = 1)

/-- Helper for Theorem 17.37: an absorbing state's one-step row has zero off-diagonal entries. -/
private lemma absorbingState_entry_eq_zero_offDiagonal
    {x y : E} (habs : IsAbsorbingState p x) (hy : y ≠ x) :
    p x y = 0 := by
  classical
  have hp : IsStochasticMatrix p := stochasticMatrix_of_realization (p := p) (P := P) (X := X)
  have hsplit :
      ∑' z : E, p x z = p x x + ∑' z : E, ite (z = x) 0 (p x z) :=
    ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ p x z) x
  have htail_eq :
      1 + ∑' z : E, ite (z = x) 0 (p x z) = 1 := by
    calc
      1 + ∑' z : E, ite (z = x) 0 (p x z) = p x x + ∑' z : E, ite (z = x) 0 (p x z) := by
            rw [habs]
      _ = ∑' z : E, p x z := hsplit.symm
      _ = 1 := hp x
  have htail_zero : ∑' z : E, ite (z = x) 0 (p x z) = 0 := by
    have htail_eq' : 1 + ∑' z : E, ite (z = x) 0 (p x z) = 1 + 0 := by
      simpa using htail_eq
    exact WithTop.add_left_cancel (show (1 : ℝ≥0∞) ≠ ⊤ by simp) htail_eq'
  have hterm_le : ite (y = x) 0 (p x y) ≤ ∑' z : E, ite (z = x) 0 (p x z) := ENNReal.le_tsum y
  have hterm_zero : ite (y = x) 0 (p x y) = 0 :=
    le_antisymm (by simpa [htail_zero] using hterm_le) bot_le
  simpa [hy] using hterm_zero

/-- Helper for Theorem 17.37: an absorbing state makes its one-step row law equal to `δ_x`. -/
private lemma absorbingState_oneStepLaw_eq_dirac
    {x : E} (habs : IsAbsorbingState p x) :
    discreteMatrixKernel p x = Measure.dirac x := by
  classical
  refine Measure.ext fun s hs ↦ ?_
  -- Proof comment: expand the discrete kernel row as the sum of weighted Dirac masses, then use
  -- that every off-diagonal coefficient is zero and the diagonal coefficient is `1`.
  calc
    discreteMatrixKernel p x s = ∑' z : E, p x z * Measure.dirac z s := by
      rw [discreteMatrixKernel_apply, Measure.sum_apply _ hs]
      refine tsum_congr fun z ↦ ?_
      simpa [smul_eq_mul] using (Measure.smul_apply (p x z) (Measure.dirac z) s)
    _ = p x x * Measure.dirac x s + ∑' z : E, ite (z = x) 0 (p x z * Measure.dirac z s) := by
          exact ENNReal.tsum_eq_add_tsum_ite (f := fun z : E ↦ p x z * Measure.dirac z s) x
    _ = p x x * Measure.dirac x s + 0 := by
          have htail_zero :
              ∑' z : E, ite (z = x) 0 (p x z * Measure.dirac z s) = 0 := by
            rw [ENNReal.tsum_eq_zero]
            intro z
            by_cases hz : z = x
            · simp [hz]
            · simp [hz, absorbingState_entry_eq_zero_offDiagonal
                (p := p) (P := P) (X := X) habs hz]
          rw [htail_zero]
    _ = p x x * Measure.dirac x s := by simp
    _ = Measure.dirac x s := by
          rw [habs, one_mul]

/-- Helper for Theorem 17.37: an absorbing state stays at `x` at every deterministic time. -/
private lemma absorbingState_nStepLaw_eq_dirac
    {x : E} (habs : IsAbsorbingState p x) :
    ∀ n : ℕ, ((discreteMatrixKernel p ^ n) x) = Measure.dirac x := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: time `0` is the deterministic start law.
      ext s hs
      change (Kernel.id x) s = Measure.dirac x s
      simp [Kernel.id_apply]
  | succ n ihn =>
      let hReal : IsMarkovProcessRealization
          (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X := inferInstance
      -- Proof comment: compose the time-`n` Dirac law with the one-step absorbing row law.
      ext s hs
      calc
        ((discreteMatrixKernel p ^ (n + 1)) x) s
          = (((discreteMatrixKernel p ^ 1) ∘ₖ (discreteMatrixKernel p ^ n)) x) s := by
              rw [← hReal.semigroup.comp_eq n 1]
        _ = (((discreteMatrixKernel p) ∘ₖ (discreteMatrixKernel p ^ n)) x) s := by
              simp
        _ = ∫⁻ z, (discreteMatrixKernel p z) s ∂(((discreteMatrixKernel p ^ n) x)) := by
              rw [Kernel.comp_apply' _ _ _ hs]
        _ = ∫⁻ z, (discreteMatrixKernel p z) s ∂(Measure.dirac x) := by
              rw [ihn]
        _ = (discreteMatrixKernel p x) s := by
              rw [lintegral_dirac]
        _ = Measure.dirac x s := by
              rw [absorbingState_oneStepLaw_eq_dirac (p := p) (P := P) (X := X) habs]

/-- Helper for Theorem 17.37: from an absorbing state, the positive-time Green function vanishes
off the diagonal. -/
private lemma absorbingState_greenFunctionFrom_one_eq_zero_offDiagonal
    {x y : E} (habs : IsAbsorbingState p x) (hy : y ≠ x) :
    (G[P, X; 1]) x y = 0 := by
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let hX : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  -- Proof comment: each positive-time transition law is already `δ_x`, so every off-diagonal
  -- positive-time Green summand vanishes.
  rw [greenFunctionFrom_one_eq_tsum_positiveStateProbabilities P X hX x y]
  rw [ENNReal.tsum_eq_zero]
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hxy : x ≠ y := by
      intro h
      exact hy h.symm
    have hpreimage : {ω | 0 < n ∧ X n ω = y} = X n ⁻¹' ({y} : Set E) := by
      ext ω
      simp [hnpos]
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x n]
    rw [absorbingState_nStepLaw_eq_dirac (p := p) (P := P) (X := X) habs n]
    simp [hxy]

/- Theorem 17.37 (2) is source-facing: its main irreducibility hypothesis is again the chapter API
`IsIrreducibleMarkovChain P X`. The discrete-kernel irreducibility of `discreteMatrixKernel p`
remains only the concrete bridge to that source-facing statement. -/

-- Proof sketch: if `x` were absorbing and `E` had a second point `y`, then irreducibility would
-- force a positive-probability path from `x` to `{y}`, but the absorbing property prevents the
-- chain from ever leaving `x`.
omit [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] in
omit p P X in
/-- Theorem 17.37 (2): if the irreducible discrete state space has at least two points, then the
transition matrix has no absorbing state. -/
theorem irreducibleMarkovChain_has_no_absorbing_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (hirr : IsIrreducibleMarkovChain P X) :
    ∀ x : E, ¬ IsAbsorbingState p x := by
  intro x habs
  obtain ⟨y, hy⟩ := exists_ne x
  have hgreen_pos : 0 < (G[P, X; 1]) x y := by
    exact
      (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
        (κ := fun n ↦ discreteMatrixKernel p ^ n) P X).1 hirr (by
          intro h
          exact hy h.symm)
  have hgreen_zero : (G[P, X; 1]) x y = 0 :=
    absorbingState_greenFunctionFrom_one_eq_zero_offDiagonal
      (p := p) (P := P) (X := X) habs hy
  rw [hgreen_zero] at hgreen_pos
  exact lt_irrefl _ hgreen_pos

-- Proof sketch: pass from the discrete-kernel irreducibility of `p` to the chapter predicate
-- `IsIrreducibleMarkovChain P X`, then apply Theorem 17.37 (2).
omit [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] in
omit p P X in
/-- The kernel-style specialization of Theorem 17.37 (2) for realizations of a stochastic matrix.
-/
theorem irreducibleMarkovChain_has_no_absorbing_state_of_discreteMatrixKernel_isIrreducible
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)] :
    ∀ x : E, ¬ IsAbsorbingState p x := by
  -- Proof comment: this specialization just supplies the source-facing irreducibility predicate
  -- from the owner-kernel irreducibility hypothesis.
  have hirr : IsIrreducibleMarkovChain P X :=
    isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible
      (p := p) (P := P) (X := X)
  exact irreducibleMarkovChain_has_no_absorbing_state (p := p) (P := P) (X := X) hirr

end NoAbsorbingState

end ProbabilityTheory
