import Mathlib

open Function

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this environment, so this file uses the canonical mathlib iterate notation
-- `(N^[t]) P` for the textbook closure `N^t`.

namespace Monotone

/-- A `1`-indexed sequence whose successor terms are bounded by a monotone endomap is bounded by
the corresponding iterates of that endomap. -/
theorem seq_le_iterate_of_succ
    {α : Type*} [Preorder α] {f : α → α} (hf : Monotone f)
    {x : α} {s : ℕ → α}
    (h1 : s 1 ≤ f x)
    (hs : ∀ n : ℕ, 1 ≤ n → s (n + 1) ≤ f (s n))
    {n : ℕ}
    (hn : 1 ≤ n) :
    s n ≤ (f^[n]) x := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  let x' : ℕ → α := fun m ↦ s (m + 1)
  let y' : ℕ → α := fun m ↦ (f^[m]) (f x)
  have h0 : x' 0 ≤ y' 0 := by
    simpa [x', y'] using h1
  have hx : ∀ m < k, x' (m + 1) ≤ f (x' m) := by
    intro m hm
    simpa [x', Nat.add_assoc] using hs (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  have hy : ∀ m < k, f (y' m) ≤ y' (m + 1) := by
    intro m hm
    simp [y', Function.iterate_succ_apply']
  simpa [x', y', Function.iterate_succ_apply, Nat.add_comm] using hf.seq_le_seq k h0 hx hy

end Monotone

section Theorem1011

variable {α : Type*}

/-- Theorem 10.11. For any ambient type `α`, let `P : Set α`, let `N` be a monotone one-step
operator on subsets of `α`, and let `S t` denote a `1`-indexed relaxation sequence. If
`S 1 ⊆ N P` and each successive level satisfies `S (t + 1) ⊆ N (S t)`, then every positive level
is contained in the corresponding iterate `N^t = (N^[t]) P`. The textbook Sherali-Adams statement
for `P ⊆ ℝ^n` is the specialization `α := Fin n → ℝ`. -/
theorem sherali_adams_relaxation_subset_n_iterate
    (P : Set α)
    (N : Set α → Set α)
    (S : ℕ → Set α)
    (hN_mono : Monotone N)
    (hS_one : S 1 ⊆ N P)
    (hS_step : ∀ t : ℕ, 1 ≤ t → S (t + 1) ⊆ N (S t))
    {t : ℕ}
    (ht : 1 ≤ t) :
    S t ⊆ (N^[t]) P :=
  hN_mono.seq_le_iterate_of_succ hS_one hS_step ht

end Theorem1011
