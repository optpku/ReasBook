module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

open scoped BigOperators

namespace CuttingStock

variable {m : ℕ}

/-- The cutting patterns of width bound `W` for item widths `w`, namely the vectors
`s : Fin m → ℕ` satisfying `∑ i, w i * s i ≤ W`. -/
def patterns (W : ℕ) (w : Fin m → ℕ) : Set (Fin m → ℕ) :=
  {s | ∑ i, w i * s i ≤ W}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean
Membership in `patterns W w` is exactly the width inequality `∑ i, w i * s i ≤ W`. -/
theorem mem_patterns_iff
    (W : ℕ) (w : Fin m → ℕ) (s : Fin m → ℕ) :
    s ∈ patterns W w ↔ ∑ i, w i * s i ≤ W := by
  -- Unfolding the set of patterns exposes exactly the defining width inequality.
  unfold patterns
  rfl

attribute [simp] mem_patterns_iff

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
the zero vector is a cutting pattern for every width bound. -/
@[simp] lemma zero_mem_patterns (W : ℕ) (w : Fin m → ℕ) :
    (0 : Fin m → ℕ) ∈ patterns W w := by
  -- The defining total vanishes coordinatewise, leaving the natural-number lower bound.
  simp only [mem_patterns_iff, Pi.zero_apply, Nat.mul_zero, Finset.sum_const_zero, Nat.zero_le]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
every set of cutting patterns is nonempty. -/
lemma patterns_nonempty (W : ℕ) (w : Fin m → ℕ) : (patterns W w).Nonempty := by
  -- The zero multiplicity vector supplies a canonical witness.
  exact ⟨0, zero_mem_patterns W w⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
a vector fails to be a cutting pattern exactly when its total width exceeds the bound. -/
@[simp] lemma not_mem_patterns_iff (W : ℕ) (w : Fin m → ℕ) (s : Fin m → ℕ) :
    s ∉ patterns W w ↔ W < ∑ i, w i * s i := by
  -- Negate the defining inequality and use the strict-order characterization on naturals.
  simp only [mem_patterns_iff, Nat.not_le]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
membership in the set of cutting patterns is monotone in the width bound. -/
lemma mem_patterns_mono {W Wnext : ℕ} (h : W ≤ Wnext) {w : Fin m → ℕ} {s : Fin m → ℕ}
    (hs : s ∈ patterns W w) : s ∈ patterns Wnext w := by
  -- Expose the total-width invariant and enlarge only its upper bound.
  rw [mem_patterns_iff] at hs ⊢
  exact hs.trans h

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
increasing the width bound preserves every cutting pattern. -/
lemma patterns_mono {W Wnext : ℕ} (h : W ≤ Wnext) (w : Fin m → ℕ) :
    patterns W w ⊆ patterns Wnext w := by
  -- Apply pointwise membership monotonicity to obtain the set inclusion.
  intro s hs
  exact mem_patterns_mono h hs

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
decreasing item widths can only enlarge the set of cutting patterns. -/
lemma patterns_antitone_widths {W : ℕ} {w wnext : Fin m → ℕ} (h : ∀ i, w i ≤ wnext i) :
    patterns W wnext ⊆ patterns W w := by
  -- Compare weighted coordinates, then preserve the common width bound.
  intro s hs
  rw [mem_patterns_iff] at hs ⊢
  refine (Finset.sum_le_sum ?_).trans hs
  intro i _
  exact Nat.mul_le_mul_right (s i) (h i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
decreasing every item multiplicity preserves membership in the set of cutting patterns. -/
lemma mem_patterns_of_le {W : ℕ} {w s t : Fin m → ℕ} (hst : ∀ i, s i ≤ t i)
    (ht : t ∈ patterns W w) : s ∈ patterns W w := by
  -- Compare each weighted coordinate, sum those comparisons, and retain the common bound.
  rw [mem_patterns_iff] at ht ⊢
  refine (Finset.sum_le_sum ?_).trans ht
  intro i _
  exact Nat.mul_le_mul_left (w i) (hst i)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Patterns.lean:
when every item has width zero, every multiplicity vector is a cutting pattern. -/
@[simp] lemma patterns_zero_widths (W : ℕ) :
    patterns W (0 : Fin m → ℕ) = Set.univ := by
  -- Reduce membership on both sides; the total width is identically zero.
  ext s
  simp only [mem_patterns_iff, Pi.zero_apply, Nat.zero_mul, Finset.sum_const_zero,
    Nat.zero_le, Set.mem_univ]

end CuttingStock

#print axioms CuttingStock.mem_patterns_iff

end
