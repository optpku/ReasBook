module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import ReasLib.Topology.Sequences.Interleave

public section

open Filter

/-- An eventual property of both the even and odd subsequences is eventual for the
whole sequence. -/
theorem eventually_atTop_of_even_odd {p : ℕ → Prop}
    (heven : ∀ᶠ n in atTop, p (2 * n))
    (hodd : ∀ᶠ n in atTop, p (2 * n + 1)) :
    ∀ᶠ n in atTop, p n := by
  obtain ⟨Neven, hNeven⟩ := eventually_atTop.mp heven
  obtain ⟨Nodd, hNodd⟩ := eventually_atTop.mp hodd
  apply eventually_atTop.mpr
  refine ⟨2 * max Neven Nodd + 1, ?_⟩
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · apply hNeven k
    have hdouble : 2 * max Neven Nodd ≤ 2 * k :=
      (Nat.le_succ (2 * max Neven Nodd)).trans hn
    exact (Nat.le_max_left Neven Nodd).trans
      (Nat.le_of_mul_le_mul_left hdouble Nat.two_pos)
  · apply hNodd k
    have hdouble : 2 * max Neven Nodd ≤ 2 * k :=
      Nat.add_le_add_iff_right.mp hn
    exact (Nat.le_max_right Neven Nodd).trans
      (Nat.le_of_mul_le_mul_left hdouble Nat.two_pos)

namespace Asymptotics

/-- Big-O bounds on the even and odd subsequences combine to a Big-O bound on the
whole sequence. -/
theorem IsBigO.of_even_odd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℕ → E} {g : ℕ → F}
    (heven : (fun n ↦ f (2 * n)) =O[atTop] fun n ↦ g (2 * n))
    (hodd : (fun n ↦ f (2 * n + 1)) =O[atTop] fun n ↦ g (2 * n + 1)) :
    f =O[atTop] g := by
  obtain ⟨Ceven, hCeven⟩ := heven.bound
  obtain ⟨Codd, hCodd⟩ := hodd.bound
  apply IsBigO.of_bound (max Ceven Codd)
  apply eventually_atTop_of_even_odd
  · filter_upwards [hCeven] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left Ceven Codd) (norm_nonneg _))
  · filter_upwards [hCodd] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right Ceven Codd) (norm_nonneg _))

/-- Little-o bounds on the even and odd subsequences combine to a little-o bound on
the whole sequence. -/
theorem IsLittleO.of_even_odd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℕ → E} {g : ℕ → F}
    (heven : (fun n ↦ f (2 * n)) =o[atTop] fun n ↦ g (2 * n))
    (hodd : (fun n ↦ f (2 * n + 1)) =o[atTop] fun n ↦ g (2 * n + 1)) :
    f =o[atTop] g := by
  rw [isLittleO_iff] at heven hodd ⊢
  intro c hc
  exact eventually_atTop_of_even_odd (heven hc) (hodd hc)

/-- Asymptotic equivalences on the even and odd subsequences combine to an asymptotic
equivalence on the whole sequence. -/
theorem IsEquivalent.of_even_odd {E : Type*} [NormedAddCommGroup E] {f g : ℕ → E}
    (heven : (fun n ↦ f (2 * n)) ~[atTop] fun n ↦ g (2 * n))
    (hodd : (fun n ↦ f (2 * n + 1)) ~[atTop] fun n ↦ g (2 * n + 1)) :
    f ~[atTop] g := by
  rw [IsEquivalent]
  apply IsLittleO.of_even_odd
  · simpa only [Pi.sub_def] using heven.isLittleO
  · simpa only [Pi.sub_def] using hodd.isLittleO

end Asymptotics
