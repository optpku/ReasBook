import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section Example815

variable {m : ℕ}

/-- The cutting patterns of width bound `W` for item widths `w`. -/
def cutting_patterns (W : ℕ) (w : Fin m → ℕ) : Set (Fin m → ℕ) :=
  {s | ∑ i, w i * s i ≤ W}

/-- Membership in `cutting_patterns W w` is exactly the width inequality
`∑ i, w_i s_i ≤ W`. -/
@[simp] theorem mem_cutting_patterns_iff
    (W : ℕ) (w : Fin m → ℕ) (s : Fin m → ℕ) :
    s ∈ cutting_patterns W w ↔ ∑ i, w i * s i ≤ W :=
  Iff.rfl

/-- The single-roll block feasible set `Q` from Example 8.15, written with the binary variable as
the natural number `η ∈ {0,1}` and the cut counts as a vector `ζ : Fin m → ℕ`. -/
def cutting_stock_block (W : ℕ) (w : Fin m → ℕ) : Set (ℕ × (Fin m → ℕ)) :=
  {q | q.1 ≤ 1 ∧ ∑ i, w i * q.2 i ≤ W * q.1}

/-- Membership in `cutting_stock_block W w` means that `η` is binary and that the total width cut
from the roll does not exceed `W η`. -/
@[simp] theorem mem_cutting_stock_block_iff
    (W : ℕ) (w : Fin m → ℕ) (q : ℕ × (Fin m → ℕ)) :
    q ∈ cutting_stock_block W w ↔ q.1 ≤ 1 ∧ ∑ i, w i * q.2 i ≤ W * q.1 :=
  Iff.rfl

/-- The Gilmore-Gomory feasible set over a finite family `patterns` of cutting patterns. -/
def gilmore_gomory_feasible_set
    (b : Fin m → ℕ) (patterns : Finset (Fin m → ℕ)) : Set ((Fin m → ℕ) → ℕ) :=
  {x | ∀ i, b i ≤ patterns.sum (fun s ↦ s i * x s)}

/-- Membership in `gilmore_gomory_feasible_set b patterns` is exactly the demand system
`b_i ≤ ∑_s s_i x_s` for each width class `i`. -/
@[simp] theorem mem_gilmore_gomory_feasible_set_iff
    (b : Fin m → ℕ) (patterns : Finset (Fin m → ℕ)) (x : (Fin m → ℕ) → ℕ) :
    x ∈ gilmore_gomory_feasible_set b patterns ↔
      ∀ i, b i ≤ patterns.sum (fun s ↦ s i * x s) :=
  Iff.rfl

/-- The Gilmore-Gomory objective counts the total number of stock rolls used by the pattern-count
vector `x`. -/
def gilmore_gomory_objective
    (patterns : Finset (Fin m → ℕ)) (x : (Fin m → ℕ) → ℕ) : ℕ :=
  patterns.sum x

/-- The objective `gilmore_gomory_objective patterns x` is the sum of the pattern multiplicities
over the chosen cutting patterns. -/
@[simp] theorem gilmore_gomory_objective_eq
    (patterns : Finset (Fin m → ℕ)) (x : (Fin m → ℕ) → ℕ) :
    gilmore_gomory_objective patterns x = patterns.sum x :=
  rfl

/-- The Gilmore-Gomory feasible set with the extra roll-bound constraint `∑_s x_s ≤ p`. -/
def gilmore_gomory_feasible_set_with_roll_bound
    (b : Fin m → ℕ) (patterns : Finset (Fin m → ℕ)) (p : ℕ) :
    Set ((Fin m → ℕ) → ℕ) :=
  {x | x ∈ gilmore_gomory_feasible_set b patterns ∧ gilmore_gomory_objective patterns x ≤ p}

/-- Membership in `gilmore_gomory_feasible_set_with_roll_bound b patterns p` means satisfying the
demand inequalities together with the bound `∑_s x_s ≤ p`. -/
@[simp] theorem mem_gilmore_gomory_feasible_set_with_roll_bound_iff
    (b : Fin m → ℕ) (patterns : Finset (Fin m → ℕ)) (p : ℕ) (x : (Fin m → ℕ) → ℕ) :
    x ∈ gilmore_gomory_feasible_set_with_roll_bound b patterns p ↔
      x ∈ gilmore_gomory_feasible_set b patterns ∧ gilmore_gomory_objective patterns x ≤ p :=
  Iff.rfl

/-- Helper for Example 8.15: if a feasible block point has first coordinate `0`, then every cut
count vanishes because the weighted width sum is a sum of nonnegative terms equal to `0`. -/
lemma secondComponent_eq_zero_of_mem_block_zero
    (W : ℕ) (w : Fin m → ℕ)
    (hw : ∀ i, 0 < w i)
    {ζ : Fin m → ℕ}
    (hζ : (0, ζ) ∈ cutting_stock_block W w) :
    ζ = 0 := by
  -- The block constraint collapses to a zero weighted sum when the roll is unused.
  have hsum_le : ∑ i, w i * ζ i ≤ W * 0 :=
    (mem_cutting_stock_block_iff W w (0, ζ)).mp hζ |>.2
  have hsum_zero : ∑ i, w i * ζ i = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    simpa using hsum_le
  -- A sum of nonnegative natural numbers is zero only when every term is zero.
  have hterm_zero : ∀ i, w i * ζ i = 0 := by
    intro i
    have hdecomp :
        w i * ζ i + (Finset.univ.erase i).sum (fun j : Fin m ↦ w j * ζ j) =
          ∑ j, w j * ζ j := by
      simpa using
        (Finset.univ.add_sum_erase (fun j : Fin m ↦ w j * ζ j) (Finset.mem_univ i))
    have hsingle :
        w i * ζ i ≤ ∑ j, w j * ζ j := by
      rw [← hdecomp]
      exact Nat.le_add_right _ _
    have hle_zero : w i * ζ i ≤ 0 := by
      rw [hsum_zero] at hsingle
      exact hsingle
    exact le_antisymm hle_zero (Nat.zero_le _)
  -- Positivity of each width removes the `w i = 0` branch from `Nat.mul_eq_zero`.
  funext i
  rcases Nat.mul_eq_zero.mp (hterm_zero i) with hwi | hζi
  · exact False.elim ((Nat.ne_of_gt (hw i)) hwi)
  · exact hζi

/-- Helper for Example 8.15: a feasible block point with first coordinate `1` gives a cutting
pattern. -/
lemma mem_cutting_patterns_of_mem_block_one
    (W : ℕ) (w : Fin m → ℕ)
    {ζ : Fin m → ℕ}
    (hζ : (1, ζ) ∈ cutting_stock_block W w) :
    ζ ∈ cutting_patterns W w := by
  -- With `η = 1`, the block width bound is exactly the cutting-pattern inequality.
  have hwidth : ∑ i, w i * ζ i ≤ W * 1 :=
    (mem_cutting_stock_block_iff W w (1, ζ)).mp hζ |>.2
  have hpattern_width : ∑ i, w i * ζ i ≤ W := by
    simpa using hwidth
  exact (mem_cutting_patterns_iff W w ζ).2 hpattern_width

/-- Helper for Example 8.15: every cutting pattern yields a feasible block point with first
coordinate `1`. -/
lemma mem_cutting_stock_block_of_pattern
    (W : ℕ) (w : Fin m → ℕ)
    {s : Fin m → ℕ}
    (hs : s ∈ cutting_patterns W w) :
    (1, s) ∈ cutting_stock_block W w := by
  -- The pattern inequality is exactly the block inequality for a used roll.
  have hbinary : (1 : ℕ) ≤ 1 := le_rfl
  have hwidth : ∑ i, w i * s i ≤ W * 1 := by
    have hs' : ∑ i, w i * s i ≤ W := (mem_cutting_patterns_iff W w s).mp hs
    simpa using hs'
  exact (mem_cutting_stock_block_iff W w (1, s)).2 ⟨hbinary, hwidth⟩

/-- Example 8.15 (1). If every requested width is positive, then the points of the single-roll
block `Q` are exactly the zero vector `(0, 0)` and the points `(1, s)` indexed by cutting patterns
`s` satisfying `∑ i, w_i s_i ≤ W`. -/
theorem example_8_15_block_points
    (W : ℕ) (w : Fin m → ℕ)
    (hw : ∀ i, 0 < w i)
    (q : ℕ × (Fin m → ℕ)) :
    q ∈ cutting_stock_block W w ↔
      q = (0, 0) ∨ ∃ s ∈ cutting_patterns W w, q = (1, s) := by
  constructor
  · rintro hq
    rcases q with ⟨η, ζ⟩
    -- The binary first coordinate leaves only the zero-roll and one-roll cases.
    have hmem : η ≤ 1 ∧ ∑ i, w i * ζ i ≤ W * η :=
      (mem_cutting_stock_block_iff W w (η, ζ)).mp hq
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hmem.1 with hη | hη
    · -- If the roll is unused, the zero-sum helper forces every cut count to vanish.
      left
      subst hη
      have hblock_zero : (0, ζ) ∈ cutting_stock_block W w :=
        (mem_cutting_stock_block_iff W w (0, ζ)).2 hmem
      have hζ : ζ = 0 := secondComponent_eq_zero_of_mem_block_zero W w hw hblock_zero
      simp [hζ]
    · -- If the roll is used, its cut vector is exactly a cutting pattern.
      right
      subst hη
      have hblock_one : (1, ζ) ∈ cutting_stock_block W w :=
        (mem_cutting_stock_block_iff W w (1, ζ)).2 hmem
      have hpattern : ζ ∈ cutting_patterns W w :=
        mem_cutting_patterns_of_mem_block_one W w hblock_one
      refine ⟨ζ, hpattern, rfl⟩
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · -- The zero vector is feasible because both the binary and width constraints are trivial.
      have hzero_width : ∑ i, w i * (0 : Fin m → ℕ) i ≤ W * 0 := by
        simp
      exact (mem_cutting_stock_block_iff W w (0, 0)).2 ⟨Nat.zero_le 1, hzero_width⟩
    · -- A cutting pattern gives a feasible single-roll block point.
      exact mem_cutting_stock_block_of_pattern W w hs

/-- Example 8.15 (2). If `p` is an upper bound on the number of stock rolls used by every
Gilmore-Gomory feasible pattern-count vector, then the additional constraint
`∑_s x_s ≤ p` is redundant. -/
theorem example_8_15_redundant_roll_bound
    (b : Fin m → ℕ) (patterns : Finset (Fin m → ℕ)) (p : ℕ)
    (hupper :
      ∀ ⦃x : (Fin m → ℕ) → ℕ⦄,
        x ∈ gilmore_gomory_feasible_set b patterns →
          gilmore_gomory_objective patterns x ≤ p) :
    gilmore_gomory_feasible_set_with_roll_bound b patterns p =
      gilmore_gomory_feasible_set b patterns := by
  ext x
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, hupper hx⟩

end Example815
