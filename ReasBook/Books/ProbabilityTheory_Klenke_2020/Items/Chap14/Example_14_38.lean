/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory MeasurableEquiv ProbabilityTheory Preorder
open ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The state space at time `i`, represented by the finite set `{0, ..., n + i}`. -/
abbrev polyaUrnState (n : ℕ) (i : ℕ) := Fin (n + i + 1)

/-- The deterministic initial red-count state `k` at time `0`. -/
def polyaUrnInitialState (n k : ℕ) (hk : k ≤ n) : polyaUrnState n 0 :=
  ⟨k, Nat.lt_succ_of_le hk⟩

/-- The one-step state-space transition kernel of the Pólya urn from time `i` to time `i + 1`. -/
noncomputable def polyaUrnTransitionKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    Kernel (polyaUrnState n i) (polyaUrnState n (i + 1)) where
  toFun current :=
  let _ : NeZero (n + i : ℝ≥0∞) :=
    ⟨by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hn (Nat.le_add_right n i))⟩
  let p : ℝ≥0∞ := ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞)
  p • Measure.dirac current.succ + (1 - p) • Measure.dirac current.castSucc
  measurable' := Measurable.of_discrete

/-- The stage-`i` transition kernel of the Pólya-urn trajectory, obtained from the state-space
kernel by reading the current count from the last coordinate of the prefix. -/
noncomputable def polyaUrnStepKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    Kernel (Π j : Finset.Iic i, polyaUrnState n j) (polyaUrnState n (i + 1)) :=
  Kernel.comap
    (polyaUrnTransitionKernel n hn i)
    (fun x : Π j : Finset.Iic i, polyaUrnState n j ↦ x ⟨i, mem_Iic.2 le_rfl⟩)
    Measurable.of_discrete

/-- Helper for Example 14.38: each fiber of `polyaUrnTransitionKernel` is the expected
two-point measure concentrated on staying put or gaining one red ball. -/
lemma polyaUrnTransitionKernel_apply (n : ℕ) (hn : 0 < n) (i : ℕ)
    (current : polyaUrnState n i) :
    polyaUrnTransitionKernel n hn i current =
      let p : ℝ≥0∞ := ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞)
      p • Measure.dirac current.succ + (1 - p) • Measure.dirac current.castSucc := by
  -- This is the explicit fiber formula encoded in the kernel definition.
  rfl

/-- Helper for Example 14.38: the coefficient of the upward jump in the Pólya-urn transition
is bounded by `1`. -/
lemma polyaUrnTransitionWeight_le_one (n : ℕ) (hn : 0 < n) (i : ℕ)
    (current : polyaUrnState n i) :
    ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞) ≤ 1 := by
  -- The current red-ball count cannot exceed the total number of balls at time `i`.
  have hcurrent :
      ((current : ℕ) : ℝ≥0∞) ≤ (n + i : ℝ≥0∞) := by
    exact_mod_cast Nat.le_of_lt_succ current.2
  have hdenom_ne_zero : (n + i : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hn (Nat.le_add_right n i))
  -- Dividing both numerator and denominator by the same positive finite quantity reduces to `1`.
  calc
    ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞) ≤
        (n + i : ℝ≥0∞) / (n + i : ℝ≥0∞) :=
      ENNReal.div_le_div_right hcurrent (n + i : ℝ≥0∞)
    _ = 1 := ENNReal.div_self hdenom_ne_zero (by simp)

/-- Helper for Example 14.38: every explicit two-point transition fiber has total mass `1`. -/
lemma polyaUrnTransitionFiber_measure_univ (n : ℕ) (hn : 0 < n) (i : ℕ)
    (current : polyaUrnState n i) :
    ((((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞)) • Measure.dirac current.succ +
        (1 - (((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞))) • Measure.dirac current.castSucc)
      Set.univ = 1 := by
  let p : ℝ≥0∞ := ((current : ℕ) : ℝ≥0∞) / (n + i : ℝ≥0∞)
  have hp_le_one : p ≤ 1 := by
    simpa [p] using polyaUrnTransitionWeight_le_one n hn i current
  -- Both Dirac measures assign mass `1` to `Set.univ`, so only `p + (1 - p)` remains.
  simp [p, Measure.add_apply, Measure.smul_apply, hp_le_one, add_tsub_cancel_of_le hp_le_one]

-- Proof sketch: for a current state `xᵢ`, the transition measure is supported on the two
-- states `xᵢ.castSucc` and `xᵢ.succ`. Its total mass is
-- `xᵢ / (n + i) + (1 - xᵢ / (n + i)) = 1`.
instance polyaUrnTransitionKernel_isMarkovKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    IsMarkovKernel (polyaUrnTransitionKernel n hn i) where
  isProbabilityMeasure current := by
    -- Rewrite the fiber as the explicit two-point transition measure.
    rw [polyaUrnTransitionKernel_apply]
    refine ⟨?_⟩
    -- Its total mass is exactly the computation carried out in the helper lemma above.
    simpa using polyaUrnTransitionFiber_measure_univ n hn i current

instance polyaUrnStepKernel_isMarkovKernel (n : ℕ) (hn : 0 < n) (i : ℕ) :
    IsMarkovKernel (polyaUrnStepKernel n hn i) := by
  dsimp [polyaUrnStepKernel]
  infer_instance

section

variable (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)

/-- Example 14.38: the path-space law of Pólya's urn with `n > 0` initial balls, `k` of them
red, and reinforcement by returning the sampled ball together with one additional ball of the same
color. Here `Ωᵢ = {0, ..., n + i}` is represented by `Fin (n + i + 1)`. -/
noncomputable def polyaUrnTrajectoryMeasure :
    Measure (∀ i : ℕ, polyaUrnState n i) :=
  trajMeasure (Measure.dirac (polyaUrnInitialState n k hk)) (polyaUrnStepKernel n hn)

/-- The finite-dimensional law up to time `i`, obtained as the marginal of the full Pólya-urn
trajectory law on the first `i + 1` coordinates. -/
noncomputable def polyaUrnFiniteLawUpTo (i : ℕ) :
    Measure (Π j : Finset.Iic i, polyaUrnState n j) :=
  (polyaUrnTrajectoryMeasure n k hn hk).map (frestrictLe i)

/-- The Pólya-urn trajectory law is a probability measure. -/
theorem polyaUrnTrajectoryMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (polyaUrnTrajectoryMeasure n k hn hk) := by
  dsimp [polyaUrnTrajectoryMeasure]
  infer_instance

/-- The finite-dimensional laws `Pᵢ` are the marginals of the full Pólya-urn trajectory law on the
first `i + 1` coordinates. -/
theorem polyaUrnFiniteLawUpTo_eq_map_trajectoryMeasure
    (i : ℕ) :
    polyaUrnFiniteLawUpTo n k hn hk i =
      (polyaUrnTrajectoryMeasure n k hn hk).map (frestrictLe i) :=
  rfl

/-- The finite-dimensional marginal law agrees with the iterated textbook kernel construction from
the deterministic initial state. -/
theorem polyaUrnFiniteLawUpTo_eq_partialTraj_comp_initialMeasure
    (i : ℕ) :
    polyaUrnFiniteLawUpTo n k hn hk i =
      (partialTraj (polyaUrnStepKernel n hn) 0 i) ∘ₘ
        (Measure.dirac (polyaUrnInitialState n k hk)).map (piUnique _).symm := by
  simpa [polyaUrnFiniteLawUpTo, polyaUrnTrajectoryMeasure] using
    (trajMeasure_map_frestrictLe
      (Measure.dirac (polyaUrnInitialState n k hk))
      (polyaUrnStepKernel n hn) i)

end

end
