/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Helper for Lemma 18.2: the zero-step transition always returns a state to itself. -/
private theorem zero_mem_positiveTransitionStepSet_self
    (κ : Kernel E E) (x : E) :
    0 ∈ positiveTransitionStepSet κ x x := by
  -- Proof comment: at time `0`, the kernel power is the identity kernel, so the singleton mass at
  -- `x` is exactly `1`.
  rw [mem_positiveTransitionStepSet_iff, pow_zero]
  change 0 < Kernel.id x ({x} : Set E)
  simp [Kernel.id_apply]

/-- Helper for Lemma 18.2: positive transition times compose under Chapman-Kolmogorov. -/
private theorem add_mem_positiveTransitionStepSet
    {κ : Kernel E E} {m n : ℕ} {x y z : E}
    (hxy : m ∈ positiveTransitionStepSet κ x y)
    (hyz : n ∈ positiveTransitionStepSet κ y z) :
    m + n ∈ positiveTransitionStepSet κ x z := by
  -- Proof comment: expand the `(m + n)`-step transition as a kernel integral and keep the
  -- positive contribution coming from the intermediate singleton `{y}`.
  rw [mem_positiveTransitionStepSet_iff] at hxy hyz ⊢
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton_pos :
      0 <
        ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set E), (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set E) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton_pos (by simpa [Measure.restrict_univ] using hmono)

/-- Helper for Lemma 18.2: the additive closure of the self-return times adds no new elements. -/
private theorem mem_positiveTransitionStepSet_self_of_mem_closure
    (κ : Kernel E E) (x : E) {n : ℕ}
    (hn : n ∈ AddSubmonoid.closure (positiveTransitionStepSet κ x x)) :
    n ∈ positiveTransitionStepSet κ x x := by
  -- Proof comment: the self-return times already contain `0` and are closed under addition, so
  -- closure induction reduces directly to the generating set.
  refine AddSubmonoid.closure_induction
      (fun m hm ↦ hm)
      (zero_mem_positiveTransitionStepSet_self κ x)
      (fun a b _ _ ha hb ↦ add_mem_positiveTransitionStepSet ha hb)
      hn

/-- Helper for Lemma 18.2: the period `statePeriod κ x` is the gcd of the self-return times. -/
private theorem statePeriod_eq_setGcd_selfReturnTimes
    (κ : Kernel E E) (x : E) :
    statePeriod κ x = Nat.setGcd (positiveTransitionStepSet κ x x) := by
  let S : Set ℕ := positiveTransitionStepSet κ x x
  let T : Set ℕ := {d : ℕ | ∀ n ∈ S, d ∣ n}
  by_cases hzero : Nat.setGcd S = 0
  · -- Proof comment: if the gcd is `0`, then every return time in `S` is `0`, so every natural
    -- number is a common divisor and the `ℕ`-supremum convention forces the period to be `0`.
    have hS_zero : S ⊆ {0} := Nat.setGcd_eq_zero_iff.mp hzero
    have hT_univ : T = Set.univ := by
      ext d
      constructor
      · intro _
        simp
      · intro _
        simp only [T, Set.mem_setOf_eq]
        intro n hn
        simpa [Set.mem_singleton_iff.mp (hS_zero hn)] using dvd_zero d
    have hT_not_bddAbove : ¬ BddAbove T := by
      simpa [hT_univ] using (not_bddAbove_univ : ¬ BddAbove (Set.univ : Set ℕ))
    simpa [statePeriod, S, T, hzero] using (Nat.sSup_of_not_bddAbove (s := T) hT_not_bddAbove)
  · -- Proof comment: once the gcd is nonzero, the common-divisor set is bounded above by any
    -- nonzero return time, so the period supremum becomes the maximal common divisor.
    have hT_nonempty : T.Nonempty := by
      refine ⟨1, ?_⟩
      intro n hn
      exact one_dvd n
    have hT_bddAbove : BddAbove T := by
      rcases Nat.exists_ne_zero_of_setGcd_ne_zero hzero with ⟨m, hmS, hm0⟩
      refine ⟨m, ?_⟩
      intro d hd
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hd m hmS)
    have hstate_mem : statePeriod κ x ∈ T := by
      simpa [statePeriod, S, T] using (Nat.sSup_mem hT_nonempty hT_bddAbove : sSup T ∈ T)
    have hsetGcd_mem : Nat.setGcd S ∈ T := by
      intro n hn
      exact Nat.setGcd_dvd_of_mem hn
    have hsetGcd_le : Nat.setGcd S ≤ statePeriod κ x := by
      simpa [statePeriod, S, T] using (le_csSup hT_bddAbove hsetGcd_mem : Nat.setGcd S ≤ sSup T)
    have hstate_le : statePeriod κ x ≤ Nat.setGcd S := by
      have hstate_dvd : statePeriod κ x ∣ Nat.setGcd S :=
        Nat.dvd_setGcd_iff.mpr hstate_mem
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hstate_dvd
    exact le_antisymm hstate_le hsetGcd_le

-- Proof sketch: choose finitely many positive return times whose gcd is `statePeriod κ x`; the
-- Chapman-Kolmogorov semigroup law makes the positive return-time set at `x` closed under
-- addition, and the Frobenius coin-problem argument then shows that every sufficiently large
-- multiple of `statePeriod κ x` is a nonnegative combination of those return times and hence again
-- lies in `positiveTransitionStepSet κ x x`.
/-- Lemma 18.2: all sufficiently large multiples of the period `statePeriod κ x` are positive
self-return times of `x`, that is, they eventually belong to
`positiveTransitionStepSet κ x x`. By `mem_positiveTransitionStepSet_iff`, this is equivalent to
the positivity of the corresponding self-return probabilities. -/
theorem eventually_positive_self_return_probability_at_period_multiples
    (κ : Kernel E E) (x : E) :
    ∃ n_x : ℕ, ∀ ⦃n : ℕ⦄, n_x ≤ n →
      n * statePeriod κ x ∈ positiveTransitionStepSet κ x x :=
  by
  by_cases hperiod_zero : statePeriod κ x = 0
  · -- Proof comment: if the period vanishes, then every multiple is `0`, and the zero-step return
    -- time already belongs to the self-return-time set.
    refine ⟨0, ?_⟩
    intro n hn
    simpa [hperiod_zero] using zero_mem_positiveTransitionStepSet_self κ x
  · let S : Set ℕ := positiveTransitionStepSet κ x x
    -- Proof comment: for positive period, large enough integers divisible by the gcd lie in the
    -- additive closure of `S`, and large multiples of the period satisfy that divisibility.
    obtain ⟨n_x, hn_x⟩ := Nat.exists_mem_closure_of_ge S
    refine ⟨n_x, ?_⟩
    intro n hn
    have hmul_ge : n_x ≤ n * statePeriod κ x := by
      calc
        n_x ≤ n := hn
        _ ≤ n * statePeriod κ x := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hperiod_zero)
    have hclosure :
        n * statePeriod κ x ∈ AddSubmonoid.closure S := by
      -- Proof comment: rewrite the period as the gcd of `S`, then apply the numerical semigroup
      -- eventual-membership theorem at the multiple `n * statePeriod κ x`.
      have hdiv : Nat.setGcd S ∣ n * statePeriod κ x := by
        rw [← statePeriod_eq_setGcd_selfReturnTimes κ x]
        exact dvd_mul_of_dvd_right (dvd_refl (statePeriod κ x)) n
      exact hn_x (n * statePeriod κ x) hmul_ge hdiv
    -- Proof comment: the closure bridge turns eventual closure membership back into actual
    -- membership in the positive self-return-time set.
    simpa [S] using mem_positiveTransitionStepSet_self_of_mem_closure κ x hclosure

end ProbabilityTheory
