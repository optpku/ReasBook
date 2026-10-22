/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: use induction on the positive generation index. The base case is the defining
-- identity `ψ_1 = ψ_{Z_1}`. For the induction step, use the recursion
-- `ψ_{Z_{n+1}} = ψ ∘ ψ_{Z_n}` from Theorem 3.8 together with the recursion satisfied by
-- `ψ^[n]`.
/-- Helper for Lemma 3.10: the shifted positive-index invariant matches the recursion from
Theorem 3.8. -/
lemma iterate_eq_generationProbabilityGeneratingFunction_succ
    {α : Type u} (ψ : α → α) (ψZ : ℕ → α → α) (h_base : ψZ 1 = ψ)
    (h_step : ∀ n : ℕ, 1 ≤ n → ψZ (n + 1) = ψ ∘ ψZ n) :
    ∀ m : ℕ, ψ^[m + 1] = ψZ (m + 1) := by
  intro m
  induction m with
  | zero =>
      -- The induction starts at generation `1`, where both sides are the original pgf `ψ`.
      calc
        ψ^[0 + 1] = ψ := by simp
        _ = ψZ 1 := by simpa using h_base.symm
  | succ m ih =>
      -- Advancing one generation uses the same composition recursion on both sides.
      calc
        ψ^[m.succ + 1] = ψ ∘ ψ^[m + 1] := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            (Function.iterate_succ' (f := ψ) (n := m + 1))
        _ = ψ ∘ ψZ (m + 1) := by rw [ih]
        _ = ψZ (m + 1 + 1) := by
          symm
          exact h_step (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
        _ = ψZ (m.succ + 1) := by simp [Nat.succ_eq_add_one, Nat.add_assoc]

/-- Lemma 3.10: if `ψZ n` denotes the probability generating function `ψ_{Z_n}` of the `n`-th
generation size and satisfies the branching-process recursion from Theorem 3.8, then
`ψ^[n] = ψZ n` for every positive generation index `n`, i.e. `ψ_n = ψ_{Z_n}`. -/
theorem iterate_eq_generationProbabilityGeneratingFunction
    {α : Type u} (ψ : α → α) (ψZ : ℕ → α → α) (h_base : ψZ 1 = ψ)
    (h_step : ∀ n : ℕ, 1 ≤ n → ψZ (n + 1) = ψ ∘ ψZ n) :
    ∀ n : ℕ, 1 ≤ n → ψ^[n] = ψZ n := by
  intro n hn
  -- Every positive index is a successor, so the shifted induction invariant applies directly.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [Nat.succ_eq_add_one] using
    iterate_eq_generationProbabilityGeneratingFunction_succ ψ ψZ h_base h_step m
