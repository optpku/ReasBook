/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Nat.Fib.Basic

-- Semantic recall: the repository already uses `Nat.fib` in Chapter 2, and the source sequence
-- is the shifted canonical owner `k ↦ Nat.fib (k + 1)`.
/-- Chapter02 Definition 2.3-extra-1: the Fibonacci sequence from the text is the shifted
canonical sequence `k ↦ Nat.fib (k + 1)`, so that `fibonacciSequence 0 = 1` and
`fibonacciSequence 1 = 1`. -/
abbrev fibonacciSequence (k : ℕ) : ℕ :=
  Nat.fib (k + 1)

/-- `fibonacciSequence` is the source-facing shifted view of the canonical owner `Nat.fib`. -/
@[simp] theorem fibonacciSequence_eq_fib_succ (k : ℕ) :
    fibonacciSequence k = Nat.fib (k + 1) :=
  rfl

/-- The shifted Fibonacci sequence starts with value `1` at index `0`. -/
@[simp] theorem fibonacciSequence_zero :
    fibonacciSequence 0 = 1 := by
  rfl

/-- The shifted Fibonacci sequence also has value `1` at index `1`. -/
@[simp] theorem fibonacciSequence_one :
    fibonacciSequence 1 = 1 := by
  rfl

/-- The shifted Fibonacci sequence satisfies the Fibonacci recurrence in the canonical
`k + 2` form. -/
theorem fibonacciSequence_add_two (k : ℕ) :
    fibonacciSequence (k + 2) = fibonacciSequence k + fibonacciSequence (k + 1) := by
  have h :
      Nat.fib ((k + 1) + 2) = Nat.fib (k + 1) + Nat.fib ((k + 1) + 1) := Nat.fib_add_two
  simpa [fibonacciSequence, add_assoc, add_left_comm, add_comm] using
    h

/-- For every `k ≥ 1`, the shifted Fibonacci sequence satisfies the textbook recurrence
`fibonacciSequence (k + 1) = fibonacciSequence k + fibonacciSequence (k - 1)`. -/
theorem fibonacciSequence_recurrence (k : ℕ) (hk : 1 ≤ k) :
    fibonacciSequence (k + 1) = fibonacciSequence k + fibonacciSequence (k - 1) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
  simpa [add_assoc, add_left_comm, add_comm] using fibonacciSequence_add_two m
