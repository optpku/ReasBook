/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_2
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- A family `C : ZMod d → Set E` is a cyclic class decomposition for the period-`d` discrete
Markov kernel `p` when the textbook classes `E_i = C i` are nonempty, pairwise disjoint, cover
the whole state space, and one-step transitions move from class `i` to class `i + 1`. -/
def IsPeriodicClassFamily (p : Kernel E E) {d : ℕ+} (C : ZMod d → Set E) : Prop :=
  (∀ i : ZMod d, (C i).Nonempty) ∧
    (Pairwise fun i j ↦ Disjoint (C i) (C j)) ∧
    (⋃ i, C i) = Set.univ ∧
    ∀ ⦃x y : E⦄ ⦃i : ZMod d⦄, (p x) {y} > 0 → x ∈ C i → y ∈ C (i + 1)

section

variable (p : Kernel E E) [IsMarkovKernel p]
variable [Kernel.IsIrreducible (Measure.count : Measure E) p]

/-- Helper for Theorem 18.4: an irreducible count-measure kernel can only live on a countable
state space, because every state is reached in finitely many steps from a fixed base point and
each iterated row has only countably many positive singleton masses. -/
private theorem countableOfIrreducibleCountKernel
    (κ : Kernel E E) [IsMarkovKernel κ] [Kernel.IsIrreducible (Measure.count : Measure E) κ] :
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
      have hμ_univ : μ Set.univ = 1 := by
        dsimp [μ]
        induction n with
        | zero =>
            change (Kernel.id x₀) Set.univ = 1
            simp [Kernel.id_apply]
        | succ n ihn =>
            rw [Kernel.pow_succ_apply_eq_lintegral κ n x₀ MeasurableSet.univ]
            simp [ihn]
      letI : IsFiniteMeasure μ := ⟨by simpa [hμ_univ]⟩
      -- Proof comment: each `n`-step law is a probability measure, so only countably many
      -- singletons can carry positive mass.
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
        have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
          simp
        -- Proof comment: irreducibility reaches every singleton in finitely many steps.
        rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
            (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x₀ with
          ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa [reachable] using hn⟩
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Theorem 18.4: positive singleton transitions compose across kernel powers. -/
private theorem positiveSingletonComp [Countable E]
    {κ : Kernel E E} {m n : ℕ} {x y z : E}
    (hxy : 0 < (κ ^ m) x ({y} : Set E))
    (hyz : 0 < (κ ^ n) y ({z} : Set E)) :
    0 < (κ ^ (m + n)) x ({z} : Set E) := by
  -- Proof comment: expand the Chapman-Kolmogorov integral and keep the positive contribution from
  -- the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hterm_pos :
      0 < (κ ^ n) y ({z} : Set E) * ((κ ^ m) x) ({y} : Set E) :=
    ENNReal.mul_pos hyz.ne' hxy.ne'
  have hsum_pos :
      0 <
        ∑' u : E,
          (κ ^ n) u ({z} : Set E) * ((κ ^ m) x) ({u} : Set E) := by
    exact lt_of_lt_of_le hterm_pos (ENNReal.le_tsum y)
  simpa [MeasureTheory.lintegral_countable', mul_comm] using hsum_pos

/-- Helper for Theorem 18.4: irreducibility for counting measure reaches every singleton target in
finitely many steps. -/
private theorem existsMemPositiveTransitionStepSetOfIrreducible
    (x y : E) :
    ∃ n : ℕ, n ∈ positiveTransitionStepSet p x y := by
  have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
    simp
  -- Proof comment: apply irreducibility to the singleton target `{y}`.
  rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) p).irreducible
      (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with
    ⟨n, hn⟩
  exact ⟨n, by simpa [mem_positiveTransitionStepSet_iff] using hn⟩

/-- Helper for Theorem 18.4: positive transition times compose additively. -/
private theorem add_mem_positiveTransitionStepSet [Countable E]
    {m n : ℕ} {x y z : E}
    (hxy : m ∈ positiveTransitionStepSet p x y)
    (hyz : n ∈ positiveTransitionStepSet p y z) :
    m + n ∈ positiveTransitionStepSet p x z := by
  -- Proof comment: rewrite step-set membership as positivity of singleton masses and compose the
  -- two positive kernel powers.
  rw [mem_positiveTransitionStepSet_iff] at hxy hyz ⊢
  exact positiveSingletonComp (κ := p) hxy hyz

/-- Helper for Theorem 18.4: every row of a countable discrete Markov kernel has a singleton with
positive mass. -/
private theorem existsPositiveSingletonSuccessor [Countable E]
    (x : E) :
    ∃ y : E, 0 < p x ({y} : Set E) := by
  classical
  by_contra hsucc
  have hzero : ∀ y : E, p x ({y} : Set E) = 0 := by
    intro y
    exact bot_unique (not_lt.mp fun hy ↦ hsucc ⟨y, hy⟩)
  have hmass_zero : (p x) Set.univ = 0 := by
    calc
      (p x) Set.univ = ∫⁻ y, (1 : ℝ≥0∞) ∂(p x) := by simp
      _ = ∑' y : E, (1 : ℝ≥0∞) * (p x) ({y} : Set E) := by
            simpa using (MeasureTheory.lintegral_countable' (μ := p x)
              (f := fun _ : E ↦ (1 : ℝ≥0∞)))
      _ = 0 := by
            rw [ENNReal.tsum_eq_zero]
            intro y
            simp [hzero y]
  have hmass_one : (p x) Set.univ = 1 := by
    simpa using (inferInstance : IsProbabilityMeasure (p x)).measure_univ
  exact one_ne_zero (hmass_one.symm.trans hmass_zero)

/-- Helper for Theorem 18.4: a positive `(n + 1)`-step singleton transition contains an
intermediate state after `n` steps. -/
private theorem existsPositiveTransitionMidpoint [Countable E]
    {n : ℕ} {x z : E}
    (hxz : 0 < (p ^ (n + 1)) x ({z} : Set E)) :
    ∃ y : E, 0 < (p ^ n) x ({y} : Set E) ∧ 0 < p y ({z} : Set E) := by
  rw [Kernel.pow_succ_apply_eq_lintegral p n x (measurableSet_singleton z)] at hxz
  have htsum_pos :
      0 <
        ∑' u : E,
          p u ({z} : Set E) * ((p ^ n) x) ({u} : Set E) := by
    simpa [MeasureTheory.lintegral_countable', mul_comm] using hxz
  classical
  by_contra hmid
  have hterm_zero :
      ∀ u : E, p u ({z} : Set E) * ((p ^ n) x) ({u} : Set E) = 0 := by
    intro u
    by_cases hxu : 0 < (p ^ n) x ({u} : Set E)
    · have huz : ¬ 0 < p u ({z} : Set E) := by
        intro huz
        exact hmid ⟨u, hxu, huz⟩
      have huz_zero : p u ({z} : Set E) = 0 := bot_unique (not_lt.mp huz)
      simp [huz_zero]
    · have hxu_zero : (p ^ n) x ({u} : Set E) = 0 := bot_unique (not_lt.mp hxu)
      simp [hxu_zero]
  have htsum_zero :
      ∑' u : E,
        p u ({z} : Set E) * ((p ^ n) x) ({u} : Set E) = 0 := by
    exact ENNReal.tsum_eq_zero.mpr hterm_zero
  exact htsum_pos.ne' htsum_zero

/-- Helper for Theorem 18.4: class membership in a cyclic decomposition advances by `n` along any
positive `n`-step singleton transition. -/
  private theorem periodicClassFamily_mem_of_positiveTransitionStepSet [Countable E]
    {d : ℕ+} {C : ZMod d → Set E} (hC : IsPeriodicClassFamily p C)
    {x y : E} {i : ZMod d} {n : ℕ} :
    n ∈ positiveTransitionStepSet p x y → x ∈ C i → y ∈ C (i + n) := by
  intro hn hx
  induction n generalizing x y i with
  | zero =>
      have hxy : x = y := by
        by_cases hxy : x = y
        · exact hxy
        · rw [mem_positiveTransitionStepSet_iff, pow_zero] at hn
          change 0 < Kernel.id x ({y} : Set E) at hn
          rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton y)] at hn
          simp [hxy] at hn
      simpa [hxy] using hx
  | succ n ih =>
      have hxy_pos : 0 < (p ^ (n + 1)) x ({y} : Set E) := by
        simpa [mem_positiveTransitionStepSet_iff] using hn
      rcases existsPositiveTransitionMidpoint (p := p) hxy_pos with ⟨z, hxz, hzy⟩
      have hz_mem :
          z ∈ C (i + n) :=
        ih (by simpa [mem_positiveTransitionStepSet_iff] using hxz) hx
      have hy_mem : y ∈ C ((i + n) + 1) :=
        hC.2.2.2 hzy hz_mem
      simpa [Nat.cast_add, add_assoc] using hy_mem

/-- Helper for Theorem 18.4: in a cyclic class decomposition, one state cannot lie in two
different classes. -/
private theorem periodicClassFamily_index_eq_of_mem
    {d : ℕ+} {C : ZMod d → Set E} (hC : IsPeriodicClassFamily p C)
    {x : E} {i j : ZMod d}
    (hxi : x ∈ C i) (hxj : x ∈ C j) :
    i = j := by
  by_contra hij
  exact (Set.disjoint_left.mp (hC.2.1 hij) hxi hxj).elim

-- Proof sketch: choose a reference state `x₀`, define `E_i` by the congruence class modulo `d`
-- of the length of a path from `x₀` to `x`, and use irreducibility together with the period
-- condition to show that this is well defined, covers all states, and is advanced by one-step
-- transitions.
/-- Theorem 18.4 (1): if a discrete Markov kernel on a nonempty discrete state space is
irreducible and has period `d`, then its state space admits a cyclic decomposition into `d`
pairwise disjoint classes that are advanced by one-step transitions. -/
theorem exists_periodicClassDecomposition
    [Nonempty E] (d : ℕ+) (hperiod : HasPeriod p d) :
    ∃ C : ZMod d → Set E, IsPeriodicClassFamily p C := by
  classical
  letI : Countable E := countableOfIrreducibleCountKernel p
  let x₀ : E := Classical.choice ‹Nonempty E›
  let path : ℕ → E := Nat.rec x₀ fun _ x ↦ Classical.choose (existsPositiveSingletonSuccessor (p := p) x)
  have path_step :
      ∀ n : ℕ, 0 < p (path n) ({path (n + 1)} : Set E) := by
    intro n
    exact Classical.choose_spec (existsPositiveSingletonSuccessor (p := p) (path n))
  have path_mem :
      ∀ n : ℕ, n ∈ positiveTransitionStepSet p x₀ (path n) := by
    intro n
    induction n with
    | zero =>
        -- Proof comment: the base state is reached from itself in zero steps.
        have hx₀_self : 0 ∈ positiveTransitionStepSet p x₀ x₀ := by
          rw [mem_positiveTransitionStepSet_iff, pow_zero]
          change 0 < Kernel.id x₀ ({x₀} : Set E)
          rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x₀)]
          simp
        simpa [path] using hx₀_self
    | succ n ihn =>
        have hstep : 1 ∈ positiveTransitionStepSet p (path n) (path (n + 1)) := by
          simpa [mem_positiveTransitionStepSet_iff] using path_step n
        -- Proof comment: append the chosen one-step successor to the existing `n`-step path.
        simpa [Nat.succ_eq_add_one] using
          add_mem_positiveTransitionStepSet (p := p) ihn hstep
  let C : ZMod d → Set E := fun i ↦
    {x : E | ∃ n : ℕ, n ∈ positiveTransitionStepSet p x₀ x ∧ (n : ZMod d) = i}
  refine ⟨C, ?_⟩
  constructor
  · intro i
    -- Proof comment: iterate one-step successors from `x₀` to realize each class index.
    refine ⟨path i.val, ?_⟩
    change ∃ n : ℕ, n ∈ positiveTransitionStepSet p x₀ (path i.val) ∧ (n : ZMod d) = i
    exact ⟨i.val, path_mem i.val, by simpa using ZMod.natCast_zmod_val i⟩
  constructor
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases (show ∃ n : ℕ, n ∈ positiveTransitionStepSet p x₀ x ∧ (n : ZMod d) = i from hxi) with
      ⟨m, hm, hm_mod⟩
    rcases (show ∃ n : ℕ, n ∈ positiveTransitionStepSet p x₀ x ∧ (n : ZMod d) = j from hxj) with
      ⟨n, hn, hn_mod⟩
    rcases existsMemPositiveTransitionStepSetOfIrreducible (p := p) x x₀ with ⟨r, hr⟩
    have hmr : m + r ∈ positiveTransitionStepSet p x₀ x₀ :=
      add_mem_positiveTransitionStepSet (p := p) hm hr
    have hnr : n + r ∈ positiveTransitionStepSet p x₀ x₀ :=
      add_mem_positiveTransitionStepSet (p := p) hn hr
    have hmr_mod : Nat.ModEq d (m + r) 0 := by
      rw [Nat.modEq_zero_iff_dvd]
      simpa [hperiod x₀] using
        statePeriod_dvd_of_mem_positiveTransitionStepSet p x₀ hmr
    have hnr_mod : Nat.ModEq d (n + r) 0 := by
      rw [Nat.modEq_zero_iff_dvd]
      simpa [hperiod x₀] using
        statePeriod_dvd_of_mem_positiveTransitionStepSet p x₀ hnr
    have hmn_mod : Nat.ModEq d m n := by
      exact Nat.ModEq.add_right_cancel' r (hmr_mod.trans hnr_mod.symm)
    have hmn_cast : (m : ZMod d) = (n : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff m n d).2 hmn_mod
    exact hij <| by
      calc
        i = (m : ZMod d) := hm_mod.symm
        _ = (n : ZMod d) := hmn_cast
        _ = j := hn_mod
  constructor
  · ext x
    constructor
    · intro _
      simp
    · intro _
      rcases existsMemPositiveTransitionStepSetOfIrreducible (p := p) x₀ x with ⟨n, hn⟩
      refine Set.mem_iUnion.mpr ⟨(n : ZMod d), ?_⟩
      change ∃ m : ℕ, m ∈ positiveTransitionStepSet p x₀ x ∧ (m : ZMod d) = (n : ZMod d)
      exact ⟨n, hn, rfl⟩
  · intro x y i hxy hx
    rcases (show ∃ n : ℕ, n ∈ positiveTransitionStepSet p x₀ x ∧ (n : ZMod d) = i from hx) with
      ⟨n, hn, hn_mod⟩
    have hstep : 1 ∈ positiveTransitionStepSet p x y := by
      simpa [mem_positiveTransitionStepSet_iff] using hxy
    have hny : n + 1 ∈ positiveTransitionStepSet p x₀ y :=
      add_mem_positiveTransitionStepSet (p := p) hn hstep
    -- Route correction: use reachability times modulo `d` directly instead of the broken
    -- imported eventual-residue API.
    change ∃ m : ℕ, m ∈ positiveTransitionStepSet p x₀ y ∧ (m : ZMod d) = i + 1
    refine ⟨n + 1, hny, ?_⟩
    calc
      ((n + 1 : ℕ) : ZMod d) = (n : ZMod d) + 1 := by simp [Nat.cast_add]
      _ = i + 1 := by rw [hn_mod]

-- Proof sketch: fix one state and compare any two decompositions by the class containing that
-- state. Irreducibility forces every other state to lie in the class predicted by the path length
-- modulo `d`, so the two decompositions can differ only by one global cyclic shift.
/-- Theorem 18.4 (2): for an irreducible discrete Markov kernel, any two cyclic decompositions of
the state space indexed by `ZMod d` differ by a cyclic permutation of the class labels. -/
theorem periodicClassDecomposition_unique_up_to_cyclicShift
    (d : ℕ+) (C₁ C₂ : ZMod d → Set E)
    (hC₁ : IsPeriodicClassFamily p C₁) (hC₂ : IsPeriodicClassFamily p C₂) :
    ∃ k : ZMod d, ∀ i : ZMod d, C₁ i = C₂ (i + k) := by
  classical
  letI : Countable E := countableOfIrreducibleCountKernel p
  rcases hC₁.1 0 with ⟨x₀, hx₀C₁⟩
  have hx₀C₂_cover : x₀ ∈ ⋃ i : ZMod d, C₂ i := by
    simpa [hC₂.2.2.1] using (show x₀ ∈ (Set.univ : Set E) by simp)
  rcases Set.mem_iUnion.mp hx₀C₂_cover with ⟨k, hx₀C₂⟩
  refine ⟨k, ?_⟩
  intro i
  ext x
  constructor
  · intro hx
    rcases existsMemPositiveTransitionStepSetOfIrreducible (p := p) x₀ x with ⟨n, hn⟩
    have hxC₁_n :
        x ∈ C₁ ((0 : ZMod d) + n) :=
      periodicClassFamily_mem_of_positiveTransitionStepSet (p := p) hC₁
        hn hx₀C₁
    have hn_eq_i : (n : ZMod d) = i := by
      simpa using periodicClassFamily_index_eq_of_mem (p := p) hC₁ hxC₁_n hx
    have hxC₂_n :
        x ∈ C₂ (k + n) :=
      periodicClassFamily_mem_of_positiveTransitionStepSet (p := p) hC₂
        hn hx₀C₂
    simpa [add_comm, add_left_comm, add_assoc, hn_eq_i] using hxC₂_n
  · intro hx
    rcases existsMemPositiveTransitionStepSetOfIrreducible (p := p) x₀ x with ⟨n, hn⟩
    have hxC₂_n :
        x ∈ C₂ (k + n) :=
      periodicClassFamily_mem_of_positiveTransitionStepSet (p := p) hC₂
        hn hx₀C₂
    have hk_add_eq : k + (n : ZMod d) = i + k := by
      simpa [add_comm, add_left_comm, add_assoc] using
        periodicClassFamily_index_eq_of_mem (p := p) hC₂ hxC₂_n hx
    have hn_eq_i : (n : ZMod d) = i := by
      simpa [add_comm, add_left_comm, add_assoc] using hk_add_eq
    have hxC₁_n :
        x ∈ C₁ ((0 : ZMod d) + n) :=
      periodicClassFamily_mem_of_positiveTransitionStepSet (p := p) hC₁
        hn hx₀C₁
    simpa [hn_eq_i] using hxC₁_n

end

end ProbabilityTheory
