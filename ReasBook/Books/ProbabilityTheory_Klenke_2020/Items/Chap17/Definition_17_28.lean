/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} {E : Type v}

/- Layering for Definition 17.28:
- `hittingAfter` is the core/canonical owner abstraction for first hitting times of a process into
  a subset.
- The textbook entrance time `τ_x^1` is the singleton specialization `hittingAfter X {x} 1`.
- The recursively defined family `iteratedEntranceTime` and the probability `everHitsProbability`
  remain source-facing declarations built on that owner abstraction, with `F[P, X] x y` as the
  textbook notation for the latter. -/

/- Canonical recall: the positive-time entrance time into a state is the singleton specialization
of `MeasureTheory.hittingAfter` started at time `1`. -/
recall MeasureTheory.hittingAfter

/-- The positive entrance-time family `k ↦ τ_x^k` of the path `X` into the state `x`. The first
entrance time `τ_x^1` is the singleton hitting time `hittingAfter X ({x} : Set E) 1`, and each
successor stage is the next visit to `x` after the previous entrance time. -/
def iteratedEntranceTime (X : ℕ → Ω → E) (x : E) : ℕ+ → Ω → ℕ∞ :=
  fun k ↦
    PNat.recOn k
      (hittingAfter X ({x} : Set E) 1)
      (fun _ τ ω ↦
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' {n : ℕ | τ ω < n ∧ X n ω = x}))

scoped notation:arg "τ_[" X ", " x "]^" k:arg => iteratedEntranceTime X x k

-- Proof sketch: specialize `hittingAfter_eq_top_iff` to the singleton `{x}` and negate.
/-- The positive-time entrance time into `x` is finite exactly when the path hits `x` at some
strictly positive time. -/
theorem hittingAfter_singleton_lt_top_iff (X : ℕ → Ω → E) (x : E) (ω : Ω) :
    hittingAfter X ({x} : Set E) 1 ω < ⊤ ↔ ∃ n : ℕ, 0 < n ∧ X n ω = x := by
  constructor
  · intro h
    by_contra hhit
    have htop : hittingAfter X ({x} : Set E) 1 ω = ⊤ := by
      refine (hittingAfter_eq_top_iff).2 ?_
      intro j hj hjx
      exact hhit ⟨j, by simpa using hj, by simpa [Set.mem_singleton_iff] using hjx⟩
    simp [htop] at h
  · rintro ⟨n, hn, hnx⟩
    have hle : hittingAfter X ({x} : Set E) 1 ω ≤ n := by
      refine hittingAfter_le_of_mem ?_ ?_
      · simpa using hn
      · simpa [Set.mem_singleton_iff] using hnx
    exact lt_of_le_of_lt hle (by simp)

-- Proof sketch: unfold `iteratedEntranceTime` at `1`; the base case is defined to be the first
-- entrance time.
/-- The first member `τ_x^1` of the entrance-time family is the singleton hitting time
`hittingAfter X ({x} : Set E) 1`. -/
theorem iteratedEntranceTime_one (X : ℕ → Ω → E) (x : E) :
    τ_[X, x]^1 = hittingAfter X ({x} : Set E) 1 := by
  simp [iteratedEntranceTime]

-- Proof sketch: unfold the recursive definition at `k + 1`; the next entrance time is the
-- infimum of all visits to `x` strictly after the previous entrance time.
/-- The successor step of the entrance-time recursion takes the next visit to `x` after the
previous entrance time. -/
theorem iteratedEntranceTime_succ (X : ℕ → Ω → E) (x : E) (k : ℕ+) (ω : Ω) :
    (τ_[X, x]^(k + 1)) ω =
      sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' {n : ℕ | (τ_[X, x]^k) ω < n ∧ X n ω = x}) := by
  simp [iteratedEntranceTime]

section

variable [MeasurableSpace Ω]

/-- The probability under the law `P x` that the path `X` ever visits `y` after time `0`. -/
def everHitsProbability (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ :=
  (P x : Measure Ω).real {ω | (τ_[X, y]^1) ω < ⊤}

notation "F[" P ", " X "]" => everHitsProbability P X

-- Proof sketch: unfold `everHitsProbability` and rewrite the finiteness of the singleton hitting
-- time using `hittingAfter_singleton_lt_top_iff`.
/-- The ever-hit probability is the probability of the positive-time hitting event
`{ω | ∃ n > 0, X n ω = y}` under `P x`. -/
theorem everHitsProbability_def (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) :
    (F[P, X]) x y = (P x : Measure Ω).real {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} := by
  change (P x : Measure Ω).real {ω | hittingAfter X ({y} : Set E) 1 ω < ⊤} =
      (P x : Measure Ω).real {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y}
  congr 1
  ext ω
  exact hittingAfter_singleton_lt_top_iff X y ω

end

end ProbabilityTheory
