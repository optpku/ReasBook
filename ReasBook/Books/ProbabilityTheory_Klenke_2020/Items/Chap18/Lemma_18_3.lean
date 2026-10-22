/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- `HasEventualPeriodResidue κ x y L` means that, from some threshold on, every sufficiently
large integer in the residue class `L` modulo `statePeriod κ x` belongs to the transition-time set
`positiveTransitionStepSet κ x y`. -/
def HasEventualPeriodResidue (κ : Kernel E E) (x y : E) (L : ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, n * statePeriod κ x + L ∈ positiveTransitionStepSet κ x y

-- Proof sketch: this is just the definition of `HasEventualPeriodResidue`.
/-- Unfolding `HasEventualPeriodResidue` gives the threshold after which the whole residue class
lies in `positiveTransitionStepSet κ x y`. -/
theorem hasEventualPeriodResidue_iff (κ : Kernel E E) (x y : E) (L : ℕ) :
    HasEventualPeriodResidue κ x y L ↔
      ∃ n₀ : ℕ, ∀ n ≥ n₀, n * statePeriod κ x + L ∈ positiveTransitionStepSet κ x y := by
  -- Proof comment: this theorem is only the definition of `HasEventualPeriodResidue`.
  rfl

section

variable (κ : Kernel E E) [IsMarkovKernel κ]
variable [Kernel.IsIrreducible (Measure.count : Measure E) κ]

/-- Helper for Lemma 18.3: an irreducible discrete Markov kernel has countable state space,
because every state lies in the countable union of the positive singleton supports of the iterated
kernel rows from one reference point. -/
private theorem isMarkovKernel_pow (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
      simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
  | succ n ih =>
      letI : IsMarkovKernel (κ ^ n) := ih
      have hcomp : IsMarkovKernel ((κ ^ n) ∘ₖ κ) := inferInstance
      simpa [pow_succ] using
        hcomp

/-- Helper for Lemma 18.3: an irreducible discrete Markov kernel has countable state space,
because every state lies in the countable union of the positive singleton supports of the iterated
kernel rows from one reference point. -/
private theorem countableOfIrreducibleCountKernel
    (κ : Kernel E E) [IsMarkovKernel κ]
    [Kernel.IsIrreducible (Measure.count : Measure E) κ] :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E := fun n ↦ {y : E | 0 < (κ ^ n) x₀ ({y} : Set E)}
    have hreachable_countable : ∀ n, (reachable n).Countable := by
      intro n
      let μ : Measure E := (κ ^ n) x₀
      -- Proof comment: an `n`-step law is a probability measure, so only countably many
      -- singletons can carry positive mass.
      have hμ_ne_top : μ Set.univ ≠ ⊤ := by
        letI : IsMarkovKernel (κ ^ n) := isMarkovKernel_pow (κ := κ) n
        have hμ_univ : μ Set.univ = 1 := by
          simpa [μ] using
            ((inferInstance : IsMarkovKernel (κ ^ n)).isProbabilityMeasure x₀).measure_univ
        simpa [hμ_univ]
      have hiUnion_singletons : (⋃ y : E, ({y} : Set E)) = Set.univ := by
        ext y
        simp
      have hμ_ne_top_iUnion : μ (⋃ y : E, ({y} : Set E)) ≠ ⊤ := by
        simpa [hiUnion_singletons] using hμ_ne_top
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz)
            hμ_ne_top_iUnion)
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
          simp
        -- Proof comment: irreducibility reaches every singleton from the reference state.
        rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
            (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x₀ with
          ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa [reachable] using hn⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Lemma 18.3: irreducibility for counting measure yields a positive-probability
transition time between any two states. -/
private theorem existsMemPositiveTransitionStepSetOfIrreducible (x y : E) :
    ∃ n : ℕ, n ∈ positiveTransitionStepSet κ x y := by
  have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
    simp
  -- Proof comment: apply irreducibility to the singleton target `{y}`.
  rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
      (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with
    ⟨n, hn⟩
  exact ⟨n, by simpa [mem_positiveTransitionStepSet_iff] using hn⟩

/-- Helper for Lemma 18.3: positive transition times compose additively. -/
private theorem mem_positiveTransitionStepSet_add
    {x y z : E} {m n : ℕ}
    (hxy : m ∈ positiveTransitionStepSet κ x y)
    (hyz : n ∈ positiveTransitionStepSet κ y z) :
    m + n ∈ positiveTransitionStepSet κ x z := by
  rw [mem_positiveTransitionStepSet_iff] at hxy hyz ⊢
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton_pos :
      0 <
        ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) := by
    -- Proof comment: restricting the Chapman-Kolmogorov integral to `{y}` isolates the positive
    -- contribution of the intermediate state `y`.
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton_pos (by simpa [Measure.restrict_univ] using hmono)

/-- Helper for Lemma 18.3: some one-step transition from `x` has positive singleton mass. -/
private theorem existsPositiveOneStepTransition (x : E) :
    ∃ y : E, 1 ∈ positiveTransitionStepSet κ x y := by
  classical
  letI : Countable E := countableOfIrreducibleCountKernel (κ := κ)
  let mass : E → ℝ≥0∞ := fun y ↦ κ x ({y} : Set E)
  have hmass : ∑' y : E, mass y = 1 := by
    -- Proof comment: on a countable discrete space, the row mass is the sum of its singleton
    -- masses, and Markov kernels give total mass `1`.
    have hcount :
        ∫⁻ y, (1 : ℝ≥0∞) ∂(κ x) = ∑' y : E, mass y := by
      simpa [mass, mul_comm] using
        (MeasureTheory.lintegral_countable' (μ := κ x) (f := fun _ : E ↦ (1 : ℝ≥0∞)))
    calc
      ∑' y : E, mass y = ∫⁻ y, (1 : ℝ≥0∞) ∂(κ x) := by
        simpa using hcount.symm
      _ = (κ x) Set.univ := by simp
      _ = 1 := by
        simpa using ((inferInstance : IsMarkovKernel κ).isProbabilityMeasure x).measure_univ
  by_contra hnone
  have hzero : ∀ y : E, mass y = 0 := by
    intro y
    by_contra hy
    have hy_pos : 0 < mass y := bot_lt_iff_ne_bot.mpr hy
    exact hnone ⟨y, by simpa [pow_one, mem_positiveTransitionStepSet_iff] using hy_pos⟩
  have hmass_zero : ∑' y : E, mass y = 0 := by
    simp [hzero]
  have hcontr : (1 : ℝ≥0∞) = 0 := by
    simpa [hmass] using hmass_zero
  simpa using hcontr

/-- Helper for Lemma 18.3: irreducibility gives a positive self-return time at every state. -/
private theorem existsPosSelfReturnStep (x : E) :
    ∃ n : ℕ, 0 < n ∧ n ∈ positiveTransitionStepSet κ x x := by
  rcases existsPositiveOneStepTransition (κ := κ) x with ⟨y, hxy⟩
  rcases existsMemPositiveTransitionStepSetOfIrreducible (κ := κ) y x with ⟨n, hyx⟩
  -- Proof comment: follow one positive step out of `x` by any positive path back to `x`.
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  simpa [Nat.add_comm] using
    (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := x) hxy hyx)

/-- Helper for Lemma 18.3: under irreducibility every state period is positive. -/
private theorem one_le_statePeriod (x : E) :
    1 ≤ statePeriod κ x := by
  let S : Set ℕ := {d : ℕ | ∀ n ∈ positiveTransitionStepSet κ x x, d ∣ n}
  rcases existsPosSelfReturnStep (κ := κ) x with ⟨n, hn_pos, hn⟩
  have hS_bddAbove : BddAbove S := by
    refine ⟨n, ?_⟩
    intro d hd
    exact Nat.le_of_dvd hn_pos (hd n hn)
  have hone_mem : 1 ∈ S := by
    intro m hm
    exact one_dvd m
  -- Proof comment: `1` is always a common divisor, while any positive return time bounds all
  -- common divisors from above.
  exact by
    rw [statePeriod]
    exact le_csSup hS_bddAbove hone_mem

/-- Helper for Lemma 18.3: irreducibility transfers divisibility of return times from `x` to `y`.
-/
private theorem statePeriod_dvd_statePeriod_of_irreducible (x y : E) :
    statePeriod κ x ∣ statePeriod κ y := by
  rcases existsMemPositiveTransitionStepSetOfIrreducible (κ := κ) x y with ⟨m, hxy⟩
  rcases existsMemPositiveTransitionStepSetOfIrreducible (κ := κ) y x with ⟨n, hyx⟩
  rcases eventually_positive_self_return_probability_at_period_multiples κ y with ⟨n₀, hn₀⟩
  let dx := statePeriod κ x
  let dy := statePeriod κ y
  have hyy₀ : n₀ * dy ∈ positiveTransitionStepSet κ y y := by
    simpa [dy] using hn₀ le_rfl
  have hyy₁ : (n₀ + 1) * dy ∈ positiveTransitionStepSet κ y y := by
    simpa [dy] using hn₀ (Nat.le_succ n₀)
  have hxy₀ : m + n₀ * dy ∈ positiveTransitionStepSet κ x y := by
    simpa [dy, Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := y) hxy hyy₀)
  have hxy₁ : m + (n₀ + 1) * dy ∈ positiveTransitionStepSet κ x y := by
    simpa [dy, Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := y) hxy hyy₁)
  have hxx₀ : m + n₀ * dy + n ∈ positiveTransitionStepSet κ x x := by
    simpa [Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := x) hxy₀ hyx)
  have hxx₁ : m + (n₀ + 1) * dy + n ∈ positiveTransitionStepSet κ x x := by
    simpa [Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := x) hxy₁ hyx)
  have hdx₀ : dx ∣ m + n₀ * dy + n := by
    simpa [dx] using statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hxx₀
  have hdx₁ : dx ∣ m + (n₀ + 1) * dy + n := by
    simpa [dx] using statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hxx₁
  have hdx₁' : dx ∣ (m + n₀ * dy + n) + dy := by
    -- Proof comment: the two composed return times differ by exactly one period at `y`.
    simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdx₁
  have hsum : dx ∣ dy + (m + n₀ * dy + n) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdx₁'
  have hsub : dx ∣ (dy + (m + n₀ * dy + n)) - (m + n₀ * dy + n) := Nat.dvd_sub hsum hdx₀
  have hsub_eq : (dy + (m + n₀ * dy + n)) - (m + n₀ * dy + n) = dy := by
    omega
  simpa [hsub_eq] using hsub

-- Proof sketch: choose connecting times in `positiveTransitionStepSet κ x y` and
-- `positiveTransitionStepSet κ y x`, compose them with large return multiples at `x` and `y`, and
-- deduce each period divides the other by the same argument as in the textbook proof.
/-- Lemma 18.3 (1): assertion (i), namely that in the irreducible setting all state periods
coincide. -/
theorem statePeriod_eq (x y : E) :
    statePeriod κ x = statePeriod κ y := by
  have hxy : statePeriod κ x ∣ statePeriod κ y :=
    statePeriod_dvd_statePeriod_of_irreducible (κ := κ) x y
  have hyx : statePeriod κ y ∣ statePeriod κ x :=
    statePeriod_dvd_statePeriod_of_irreducible (κ := κ) y x
  -- Proof comment: the textbook divisibility argument is symmetric in `x` and `y`.
  exact Nat.dvd_antisymm hxy hyx

-- Proof sketch: pick one time `m ∈ positiveTransitionStepSet κ x y` from irreducibility, divide
-- `m` by the common period, and compose with sufficiently large return multiples at `x` to see
-- that one residue class modulo `statePeriod κ x` eventually lies in
-- `positiveTransitionStepSet κ x y`.
/-- Lemma 18.3 (2): assertion (ii), namely that for every pair of states there is an eventual
residue class modulo the common period describing `positiveTransitionStepSet κ x y`. -/
theorem exists_eventual_period_residue (x y : E) :
    ∃ Lxy : ℕ, Lxy < statePeriod κ x ∧ HasEventualPeriodResidue κ x y Lxy := by
  rcases existsMemPositiveTransitionStepSetOfIrreducible (κ := κ) x y with ⟨m, hxy⟩
  rcases eventually_positive_self_return_probability_at_period_multiples κ x with ⟨n₀, hn₀⟩
  let d := statePeriod κ x
  let q := m / d
  let r := m % d
  have hd_pos : 0 < d := by
    exact lt_of_lt_of_le Nat.zero_lt_one (one_le_statePeriod (κ := κ) x)
  refine ⟨r, by simpa [r, d] using Nat.mod_lt m hd_pos, ?_⟩
  refine ⟨n₀ + q, ?_⟩
  intro n hn
  have hq_le_n : q ≤ n := by
    exact le_trans (Nat.le_add_left q n₀) hn
  have hlarge : n₀ ≤ n - q := by
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn)
  have hxx : (n - q) * d ∈ positiveTransitionStepSet κ x x := by
    simpa [d] using hn₀ hlarge
  have hxy' : (n - q) * d + m ∈ positiveTransitionStepSet κ x y := by
    simpa [Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := x) (z := y) hxx hxy)
  -- Proof comment: Euclidean division rewrites the shifted time into the target residue class.
  have hm : m = q * d + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod m d).symm
  have hrewrite : (n - q) * d + m = n * d + r := by
    rw [hm]
    rw [← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hq_le_n]
  simpa [d, r, hrewrite] using hxy'

-- Proof sketch: if two residues in `{0, ..., statePeriod κ x - 1}` both occur eventually in
-- `positiveTransitionStepSet κ x y`, compose them with an eventual return class from
-- `positiveTransitionStepSet κ y x` and use divisibility by the period to force the two residues
-- to be equal.
/-- Lemma 18.3 (3): the residue from assertion (ii) is uniquely determined in
`{0, ..., statePeriod κ x - 1}`. -/
theorem eventual_period_residue_unique
    {x y : E} {L L' : ℕ}
    (hL_lt : L < statePeriod κ x)
    (hL'_lt : L' < statePeriod κ x)
    (hL : HasEventualPeriodResidue κ x y L)
    (hL' : HasEventualPeriodResidue κ x y L') :
    L = L' := by
  rcases exists_eventual_period_residue (κ := κ) y x with ⟨Lyx, _, hLyx⟩
  rcases hL with ⟨nL, hnL⟩
  rcases hL' with ⟨nL', hnL'⟩
  rcases hLyx with ⟨nLyx, hnLyx⟩
  let d := statePeriod κ x
  let N := max (max nL nL') nLyx
  have hN_L : nL ≤ N := by
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN_L' : nL' ≤ N := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN_yx : nLyx ≤ N := by
    exact Nat.le_max_right _ _
  have hperiod_y : statePeriod κ y = d := by
    simpa [d] using statePeriod_eq (κ := κ) y x
  have hxyL : N * d + L ∈ positiveTransitionStepSet κ x y := by
    -- Proof comment: evaluate the eventual `L`-residue at the common threshold `N`.
    simpa [d] using hnL N hN_L
  have hxyL' : N * d + L' ∈ positiveTransitionStepSet κ x y := by
    -- Proof comment: the second candidate residue also occurs at the same common threshold.
    simpa [d] using hnL' N hN_L'
  have hyx : N * d + Lyx ∈ positiveTransitionStepSet κ y x := by
    -- Proof comment: rewrite the backward residue to the common modulus `d`.
    simpa [d, hperiod_y] using hnLyx N hN_yx
  have hxxL : (N * d + L) + (N * d + Lyx) ∈ positiveTransitionStepSet κ x x := by
    -- Proof comment: composing the forward and backward times yields a return time to `x`.
    exact
      mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := x) hxyL hyx
  have hxxL' : (N * d + L') + (N * d + Lyx) ∈ positiveTransitionStepSet κ x x := by
    -- Proof comment: the same composition works for the second candidate residue.
    exact
      mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := x) hxyL' hyx
  have hLLyx : Nat.ModEq d (L + Lyx) 0 := by
    have hdvd₀ :
        d ∣ (N * d + L) + (N * d + Lyx) := by
      simpa [d] using statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hxxL
    have hdvd :
        d ∣ (L + Lyx) + (N * d + N * d) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd₀
    have hmul : d ∣ N * d + N * d := by
      exact dvd_add
        (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
        (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
    -- Proof comment: removing the common multiple of `d` leaves only the residue sum.
    apply Nat.modEq_zero_iff_dvd.mpr
    have hsub : d ∣ ((L + Lyx) + (N * d + N * d)) - (N * d + N * d) := Nat.dvd_sub hdvd hmul
    have hsub_eq : ((L + Lyx) + (N * d + N * d)) - (N * d + N * d) = L + Lyx := by
      omega
    simpa [hsub_eq] using hsub
  have hL'Lyx : Nat.ModEq d (L' + Lyx) 0 := by
    have hdvd₀ :
        d ∣ (N * d + L') + (N * d + Lyx) := by
      simpa [d] using statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hxxL'
    have hdvd :
        d ∣ (L' + Lyx) + (N * d + N * d) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd₀
    have hmul : d ∣ N * d + N * d := by
      exact dvd_add
        (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
        (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
    -- Proof comment: the second composed return time yields the same modular reduction.
    apply Nat.modEq_zero_iff_dvd.mpr
    have hsub : d ∣ ((L' + Lyx) + (N * d + N * d)) - (N * d + N * d) := Nat.dvd_sub hdvd hmul
    have hsub_eq : ((L' + Lyx) + (N * d + N * d)) - (N * d + N * d) = L' + Lyx := by
      omega
    simpa [hsub_eq] using hsub
  have hmod : Nat.ModEq d L L' := by
    -- Proof comment: cancel the shared backward residue `Lyx` from the two modular identities.
    exact Nat.ModEq.add_right_cancel' Lyx (hLLyx.trans hL'Lyx.symm)
  exact hmod.eq_of_lt_of_lt hL_lt hL'_lt

-- Proof sketch: combine eventual representatives for `(x,y)`, `(y,z)`, and `(z,x)` using kernel
-- composition; the resulting large return times from `x` to itself are divisible by the common
-- period, so the sum of the three residues is `0` modulo that period.
/-- Lemma 18.3 (4): the eventual residues satisfy the cocycle relation
`L_xy + L_yz + L_zx ≡ 0 [MOD d]`. -/
theorem eventual_period_residue_cocycle
    {x y z : E} {Lxy Lyz Lzx : ℕ}
    (hxy_lt : Lxy < statePeriod κ x)
    (hyz_lt : Lyz < statePeriod κ y)
    (hzx_lt : Lzx < statePeriod κ z)
    (hxy : HasEventualPeriodResidue κ x y Lxy)
    (hyz : HasEventualPeriodResidue κ y z Lyz)
    (hzx : HasEventualPeriodResidue κ z x Lzx) :
    Nat.ModEq (statePeriod κ x) (Lxy + Lyz + Lzx) 0 := by
  rcases hxy with ⟨nxy, hnxy⟩
  rcases hyz with ⟨nyz, hnyz⟩
  rcases hzx with ⟨nzx, hnzx⟩
  let d := statePeriod κ x
  let N := max (max nxy nyz) nzx
  have hN_xy : nxy ≤ N := by
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN_yz : nyz ≤ N := by
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN_zx : nzx ≤ N := by
    exact Nat.le_max_right _ _
  have hperiod_y : statePeriod κ y = d := by
    simpa [d] using statePeriod_eq (κ := κ) y x
  have hperiod_z : statePeriod κ z = d := by
    simpa [d] using statePeriod_eq (κ := κ) z x
  have hxyN : N * d + Lxy ∈ positiveTransitionStepSet κ x y := by
    -- Proof comment: evaluate the `(x,y)` eventual residue at the common threshold.
    simpa [d] using hnxy N hN_xy
  have hyzN : N * d + Lyz ∈ positiveTransitionStepSet κ y z := by
    -- Proof comment: rewrite the `(y,z)` residue to the common period `d`.
    simpa [d, hperiod_y] using hnyz N hN_yz
  have hzxN : N * d + Lzx ∈ positiveTransitionStepSet κ z x := by
    -- Proof comment: rewrite the `(z,x)` residue to the same common period.
    simpa [d, hperiod_z] using hnzx N hN_zx
  have hxz : (N * d + Lxy) + (N * d + Lyz) ∈ positiveTransitionStepSet κ x z := by
    -- Proof comment: first compose the `(x,y)` and `(y,z)` transition times.
    exact mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := y) (z := z) hxyN hyzN
  have hxx :
      ((N * d + Lxy) + (N * d + Lyz)) + (N * d + Lzx) ∈ positiveTransitionStepSet κ x x := by
    -- Proof comment: composing once more closes the loop and returns to `x`.
    simpa [Nat.add_assoc] using
      (mem_positiveTransitionStepSet_add (κ := κ) (x := x) (y := z) (z := x) hxz hzxN)
  have hreturn :
      Nat.ModEq d (Lxy + Lyz + Lzx) 0 := by
    have hdvd₀ :
        d ∣ ((N * d + Lxy) + (N * d + Lyz)) + (N * d + Lzx) := by
      simpa [d] using statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hxx
    have hdvd :
        d ∣ (Lxy + Lyz + Lzx) + (N * d + (N * d + N * d)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdvd₀
    have hmul : d ∣ N * d + (N * d + N * d) := by
      exact dvd_add
        (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
        (dvd_add
          (by simpa [Nat.mul_comm] using (dvd_mul_right d N))
          (by simpa [Nat.mul_comm] using (dvd_mul_right d N)))
    -- Proof comment: discarding the common multiple of `d` leaves the cocycle residue relation.
    apply Nat.modEq_zero_iff_dvd.mpr
    have hsub :
        d ∣ ((Lxy + Lyz + Lzx) + (N * d + (N * d + N * d))) - (N * d + (N * d + N * d)) :=
      Nat.dvd_sub hdvd hmul
    have hsub_eq :
        ((Lxy + Lyz + Lzx) + (N * d + (N * d + N * d))) - (N * d + (N * d + N * d)) =
          Lxy + Lyz + Lzx := by
      omega
    simpa [hsub_eq] using hsub
  exact hreturn

end

end ProbabilityTheory
