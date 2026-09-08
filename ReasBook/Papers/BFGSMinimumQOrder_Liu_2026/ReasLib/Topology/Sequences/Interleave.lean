module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter

public section

open Filter
open scoped Topology

/-- If the even and odd subsequences of a sequence converge to the same point,
the whole sequence converges to that point. -/
theorem tendsto_of_tendsto_even_odd {α : Type*} [TopologicalSpace α] {u : ℕ → α} {L : α}
    (he : Tendsto (fun n ↦ u (2 * n)) atTop (𝓝 L))
    (ho : Tendsto (fun n ↦ u (2 * n + 1)) atTop (𝓝 L)) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_forall_eventually_mem] at he ho ⊢
  intro s hs
  have he' : ∀ᶠ n in atTop, u (2 * n) ∈ s := he s hs
  have ho' : ∀ᶠ n in atTop, u (2 * n + 1) ∈ s := ho s hs
  obtain ⟨Ne, hNe⟩ := (eventually_atTop.mp he')
  obtain ⟨No, hNo⟩ := (eventually_atTop.mp ho')
  apply eventually_atTop.mpr
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · apply hNe k
    have hdouble : 2 * max Ne No ≤ 2 * k := by
      exact (Nat.le_succ (2 * max Ne No)).trans hn
    exact (Nat.le_max_left Ne No).trans
      (Nat.le_of_mul_le_mul_left hdouble Nat.two_pos)
  · apply hNo k
    have hdouble : 2 * max Ne No ≤ 2 * k :=
      Nat.add_le_add_iff_right.mp hn
    exact (Nat.le_max_right Ne No).trans
      (Nat.le_of_mul_le_mul_left hdouble Nat.two_pos)
