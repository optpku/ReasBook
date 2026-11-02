import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_1_example_8_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- This file reuses the Chapter 8 Boolean `0`-`1` owner `bool_entry` from Example 8.14.
-- The block-diagonal Lagrangian layer remains local because the generic Section 8.1 owners are
-- stated on a single `Fin n` index type, while this exercise is naturally dependent block-indexed.

section Exercise83

variable {p q : ℕ}
variable {n m : Fin p → ℕ}

noncomputable local instance blockBinaryPatternsDecidable
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (j : Fin p) :
    DecidablePred (fun x : Fin (n j) → Bool ↦ B j *ᵥ (bool_entry ∘ x) ≤ b j) :=
  Classical.decPred _

/-- The block set `Q_j` of binary vectors satisfying the nice constraints `B_j x^j ≤ b^j`. -/
noncomputable def block_binary_patterns
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (j : Fin p) : Finset (Fin (n j) → Bool) :=
  Finset.univ.filter (fun x ↦ B j *ᵥ (bool_entry ∘ x) ≤ b j)

/-- Membership in `block_binary_patterns B b j` is exactly the block inequality
`B_j x^j ≤ b^j` for the corresponding binary pattern. -/
theorem mem_block_binary_patterns_iff
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (j : Fin p)
    (x : Fin (n j) → Bool) :
    x ∈ block_binary_patterns B b j ↔
      B j *ᵥ (bool_entry ∘ x) ≤ b j := by
  simp [block_binary_patterns]

/-- The reduced `j`th block objective `(c^j - λ D_j) v` evaluated at a binary pattern `v`. -/
noncomputable def block_diagonal_reduced_objective
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ)
    (j : Fin p)
    (v : Fin (n j) → Bool) : ℝ :=
  (∑ i, c j i * bool_entry (v i)) -
    lam ⬝ᵥ (fun k ↦ ∑ i, D j k i * bool_entry (v i))

/-- The `j`th block contribution `max_{v ∈ Q_j} (c^j - λ D_j) v`, represented as the supremum of
the reduced block objective over `Q_j`. The codomain `WithBot ℝ` records the value `⊥` when the
block set `Q_j` is empty. -/
noncomputable def block_diagonal_lagrangian_block_value
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ)
    (j : Fin p) : WithBot ℝ :=
  sSup
    ((fun v ↦ ((block_diagonal_reduced_objective D c lam j v : ℝ) : WithBot ℝ)) ''
      (block_binary_patterns B b j : Set (Fin (n j) → Bool)))

/-- `block_diagonal_lagrangian_block_value B b D c λ j` unfolds to the supremum of the reduced
objective over the `j`th block set `Q_j`. -/
theorem block_diagonal_lagrangian_block_value_eq_sSup
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ)
    (j : Fin p) :
    block_diagonal_lagrangian_block_value B b D c lam j =
      sSup
        ((fun v ↦ ((block_diagonal_reduced_objective D c lam j v : ℝ) : WithBot ℝ)) ''
          (block_binary_patterns B b j : Set (Fin (n j) → Bool))) := rfl

/-- The product set `∏_j Q_j` of feasible block patterns. -/
noncomputable def block_binary_pattern_family
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ) : Set ((j : Fin p) → Fin (n j) → Bool) :=
  Set.pi Set.univ fun j ↦ (block_binary_patterns B b j : Set (Fin (n j) → Bool))

/-- Membership in `block_binary_pattern_family B b` means that every block component lies in the
corresponding feasible binary-pattern set `Q_j`. -/
theorem mem_block_binary_pattern_family_iff
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (x : (j : Fin p) → Fin (n j) → Bool) :
    x ∈ block_binary_pattern_family B b ↔
      ∀ j, x j ∈ block_binary_patterns B b j := by
  simp [block_binary_pattern_family]

/-- Helper for Exercise 8.3: the feasible block family `∏_j Q_j` is exactly the dependent product
finset `Fintype.piFinset (block_binary_patterns B b)` viewed as a set. -/
theorem block_binary_pattern_family_eq_piFinset
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ) :
    block_binary_pattern_family B b =
      (Fintype.piFinset (block_binary_patterns B b) : Set ((j : Fin p) → Fin (n j) → Bool)) := by
  -- Both sides encode the same pointwise feasibility condition on each block component.
  ext x
  simp [mem_block_binary_pattern_family_iff]

/-- The Lagrangian relaxation value obtained by dualizing the complicating constraints
`∑_j D_j x^j ≤ d` while keeping each block inside `Q_j`. -/
noncomputable def block_diagonal_lagrangian_relaxation_value
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ) : WithBot ℝ :=
  sSup
    ((fun x ↦ ((((lam ⬝ᵥ d) + ∑ j, block_diagonal_reduced_objective D c lam j (x j)) : ℝ) :
      WithBot ℝ)) ''
      block_binary_pattern_family B b)

/-- `block_diagonal_lagrangian_relaxation_value B b D d c λ` unfolds to the supremum of the
penalized objective over the product family `∏_j Q_j`. -/
theorem block_diagonal_lagrangian_relaxation_value_eq_sSup
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ) :
    block_diagonal_lagrangian_relaxation_value B b D d c lam =
      sSup
        ((fun x ↦ ((((lam ⬝ᵥ d) + ∑ j, block_diagonal_reduced_objective D c lam j (x j)) : ℝ) :
          WithBot ℝ)) ''
          block_binary_pattern_family B b) := rfl

/-- Helper for Exercise 8.3: a separable real objective over a finite dependent product attains its
maximum by combining blockwise maximizers, so the product maximum is the sum of the block maxima. -/
theorem piFinset_sup'_add_sum_eq_add_sum_sup'
    {α : Fin p → Type*}
    (S : (j : Fin p) → Finset (α j))
    (hS : ∀ j, (S j).Nonempty)
    (a : ℝ)
    (g : (j : Fin p) → α j → ℝ) :
    (Fintype.piFinset S).sup' (Fintype.piFinset_nonempty.2 hS)
        (fun x ↦ a + ∑ j, g j (x j)) =
      a + ∑ j, (S j).sup' (hS j) (g j) := by
  classical
  apply le_antisymm
  · -- Every feasible tuple is bounded by the sum of the blockwise maxima.
    refine Finset.sup'_le (s := Fintype.piFinset S) (H := Fintype.piFinset_nonempty.2 hS)
      (f := fun x ↦ a + ∑ j, g j (x j)) ?_
    intro x hx
    have hsum :
        ∑ j, g j (x j) ≤ ∑ j, (S j).sup' (hS j) (g j) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact Finset.le_sup' (f := g j) (Fintype.mem_piFinset.1 hx j)
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hsum a
  · -- Choosing a maximizer in every block produces a tuple that attains the global maximum.
    have hmax : ∀ j, ∃ v ∈ S j, (S j).sup' (hS j) (g j) = g j v := by
      intro j
      simpa [eq_comm] using
        (Finset.exists_mem_eq_sup' (s := S j) (H := hS j) (f := g j))
    choose x hxmem hxeq using hmax
    have hx : x ∈ Fintype.piFinset S := Fintype.mem_piFinset.2 hxmem
    calc
      a + ∑ j, (S j).sup' (hS j) (g j)
          = a + ∑ j, g j (x j) := by simp [hxeq]
      _ ≤ (Fintype.piFinset S).sup' (Fintype.piFinset_nonempty.2 hS)
            (fun y ↦ a + ∑ j, g j (y j)) :=
        Finset.le_sup' (f := fun y ↦ a + ∑ j, g j (y j)) hx

/-- Helper for Exercise 8.3: when `Q_j` is nonempty, the `j`th block value is the coercion of the
finite real maximum of the reduced block objective over `Q_j`. -/
theorem block_diagonal_lagrangian_block_value_eq_coe_sup'
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ)
    (j : Fin p)
    (hQj : (block_binary_patterns B b j).Nonempty) :
    block_diagonal_lagrangian_block_value B b D c lam j =
      (((block_binary_patterns B b j).sup' hQj
          (block_diagonal_reduced_objective D c lam j) : ℝ) : WithBot ℝ) := by
  -- A finite nonempty supremum in `WithBot ℝ` is the coercion of the corresponding real maximum.
  have hcoerced :
      (((block_binary_patterns B b j).sup' hQj
          (block_diagonal_reduced_objective D c lam j) : ℝ) : WithBot ℝ) =
        (block_binary_patterns B b j).sup' hQj
          (fun v ↦ ((block_diagonal_reduced_objective D c lam j v : ℝ) : WithBot ℝ)) := by
    rw [Finset.coe_sup' (s := block_binary_patterns B b j) (H := hQj)
      (f := block_diagonal_reduced_objective D c lam j), Finset.sup'_eq_sup hQj]
    rfl
  calc
    block_diagonal_lagrangian_block_value B b D c lam j
        = (block_binary_patterns B b j).sup' hQj
            (fun v ↦ ((block_diagonal_reduced_objective D c lam j v : ℝ) : WithBot ℝ)) := by
            rw [block_diagonal_lagrangian_block_value_eq_sSup]
            symm
            exact Finset.sup'_eq_csSup_image (s := block_binary_patterns B b j) hQj
              (fun v ↦ ((block_diagonal_reduced_objective D c lam j v : ℝ) : WithBot ℝ))
    _ = (((block_binary_patterns B b j).sup' hQj
          (block_diagonal_reduced_objective D c lam j) : ℝ) : WithBot ℝ) := by
          symm
          exact hcoerced

/-- Helper for Exercise 8.3: when every `Q_j` is nonempty, the block-diagonal relaxation value is
the coercion of a finite real maximum over the dependent product `∏_j Q_j`. -/
theorem block_diagonal_lagrangian_relaxation_value_eq_coe_sup'
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ)
    (hQ : ∀ j, (block_binary_patterns B b j).Nonempty) :
    block_diagonal_lagrangian_relaxation_value B b D d c lam =
      (((Fintype.piFinset (block_binary_patterns B b)).sup'
          (Fintype.piFinset_nonempty.2 hQ)
          (fun x ↦ (lam ⬝ᵥ d) + ∑ j, block_diagonal_reduced_objective D c lam j (x j)) : ℝ) :
        WithBot ℝ) := by
  -- Rewrite the feasible family as a finite product finset before collapsing the `sSup` to `sup'`.
  have hPi : (Fintype.piFinset (block_binary_patterns B b)).Nonempty :=
    Fintype.piFinset_nonempty.2 hQ
  have hcoerced :
      (((Fintype.piFinset (block_binary_patterns B b)).sup' hPi
          (fun x ↦ (lam ⬝ᵥ d) + ∑ j,
            block_diagonal_reduced_objective D c lam j (x j)) : ℝ) : WithBot ℝ) =
        (Fintype.piFinset (block_binary_patterns B b)).sup' hPi
          (fun x ↦ (((lam ⬝ᵥ d) + ∑ j,
            block_diagonal_reduced_objective D c lam j (x j) : ℝ) : WithBot ℝ)) := by
    rw [Finset.coe_sup' (s := Fintype.piFinset (block_binary_patterns B b)) (H := hPi)
      (f := fun x ↦ (lam ⬝ᵥ d) + ∑ j,
        block_diagonal_reduced_objective D c lam j (x j)), Finset.sup'_eq_sup hPi]
    rfl
  calc
    block_diagonal_lagrangian_relaxation_value B b D d c lam
        = (Fintype.piFinset (block_binary_patterns B b)).sup' hPi
            (fun x ↦ (((lam ⬝ᵥ d) + ∑ j, block_diagonal_reduced_objective D c lam j (x j) : ℝ) :
              WithBot ℝ)) := by
            rw [block_diagonal_lagrangian_relaxation_value_eq_sSup,
              block_binary_pattern_family_eq_piFinset]
            symm
            exact Finset.sup'_eq_csSup_image (s := Fintype.piFinset (block_binary_patterns B b))
              hPi (fun x ↦ (((lam ⬝ᵥ d) + ∑ j,
                block_diagonal_reduced_objective D c lam j (x j) : ℝ) : WithBot ℝ))
    _ = (((Fintype.piFinset (block_binary_patterns B b)).sup'
          (Fintype.piFinset_nonempty.2 hQ)
          (fun x ↦ (lam ⬝ᵥ d) + ∑ j, block_diagonal_reduced_objective D c lam j (x j)) : ℝ) :
          WithBot ℝ) := by
          symm
          exact hcoerced

/-- Exercise 8.3. For fixed multiplier vector `λ`, the block-diagonal relaxation separates into
the constant term `λ d` plus the sum of the independent block maxima
`max_{v ∈ Q_j} (c^j - λ D_j) v`. -/
theorem block_diagonal_lagrangian_relaxation_value_eq_sum_block_values
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ)
    (lam : Fin q → ℝ) :
    block_diagonal_lagrangian_relaxation_value B b D d c lam =
      ((lam ⬝ᵥ d : ℝ) : WithBot ℝ) +
        ∑ j, block_diagonal_lagrangian_block_value B b D c lam j := by
  classical
  by_cases hQ : ∀ j, (block_binary_patterns B b j).Nonempty
  · -- Route correction: instead of unfolding the whole product, rewrite both sides to finite
    -- maxima and separate the real-valued product maximum by choosing blockwise maximizers.
    calc
      block_diagonal_lagrangian_relaxation_value B b D d c lam
          = ((((lam ⬝ᵥ d) + ∑ j, (block_binary_patterns B b j).sup' (hQ j)
                (block_diagonal_reduced_objective D c lam j)) : ℝ) : WithBot ℝ) := by
              rw [block_diagonal_lagrangian_relaxation_value_eq_coe_sup' (B := B) (b := b)
                (D := D) (d := d) (c := c) (lam := lam) hQ]
              rw [piFinset_sup'_add_sum_eq_add_sum_sup' (S := block_binary_patterns B b) (hS := hQ)
                (a := lam ⬝ᵥ d) (g := fun j ↦ block_diagonal_reduced_objective D c lam j)]
      _ = ((lam ⬝ᵥ d : ℝ) : WithBot ℝ) +
            ∑ j, (((block_binary_patterns B b j).sup' (hQ j)
              (block_diagonal_reduced_objective D c lam j) : ℝ) : WithBot ℝ) := by
            simp
      _ = ((lam ⬝ᵥ d : ℝ) : WithBot ℝ) +
            ∑ j, block_diagonal_lagrangian_block_value B b D c lam j := by
            have hblock :
                ∀ j, (((block_binary_patterns B b j).sup' (hQ j)
                  (block_diagonal_reduced_objective D c lam j) : ℝ) : WithBot ℝ) =
                    block_diagonal_lagrangian_block_value B b D c lam j := by
              intro j
              symm
              exact block_diagonal_lagrangian_block_value_eq_coe_sup' (B := B) (b := b)
                (D := D) (c := c) (lam := lam) (j := j) (hQj := hQ j)
            simp [hblock]
  · -- If one block set is empty, then both the product family and the corresponding block value
    -- are empty, so both sides collapse to `⊥`.
    push Not at hQ
    rcases hQ with ⟨j0, hj0Empty⟩
    have hPiEmpty : Fintype.piFinset (block_binary_patterns B b) = ∅ := by
      exact Fintype.piFinset_eq_empty.2 ⟨j0, hj0Empty⟩
    have hj0Bot : block_diagonal_lagrangian_block_value B b D c lam j0 = ⊥ := by
      -- The empty block contributes no feasible reduced objective values.
      rw [block_diagonal_lagrangian_block_value_eq_sSup, hj0Empty]
      simp
    have hsumBot : ∑ j, block_diagonal_lagrangian_block_value B b D c lam j = ⊥ := by
      -- Isolating the empty block forces the whole finite sum to be `⊥`.
      rw [← Finset.sum_erase_add (a := j0) Finset.univ
        (fun j ↦ block_diagonal_lagrangian_block_value B b D c lam j) (Finset.mem_univ j0)]
      rw [hj0Bot]
      simp
    calc
      block_diagonal_lagrangian_relaxation_value B b D d c lam = ⊥ := by
        -- The whole product family is empty as soon as one block family is empty.
        rw [block_diagonal_lagrangian_relaxation_value_eq_sSup,
          block_binary_pattern_family_eq_piFinset, hPiEmpty]
        simp
      _ = ((lam ⬝ᵥ d : ℝ) : WithBot ℝ) +
            ∑ j, block_diagonal_lagrangian_block_value B b D c lam j := by
          rw [hsumBot]
          simp

/-- The Lagrangian dual value `z_LD`, represented as the infimum of the block-diagonal relaxation
values over all nonnegative multiplier vectors `λ`. -/
noncomputable def block_diagonal_lagrangian_dual_value
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ) : WithBot ℝ :=
  sInf
    ((fun lam : Fin q → ℝ ↦ block_diagonal_lagrangian_relaxation_value B b D d c lam) ''
      Set.Ici (0 : Fin q → ℝ))

/-- `block_diagonal_lagrangian_dual_value B b D d c` unfolds to the infimum of the block-diagonal
relaxation values over all nonnegative multipliers `λ`. -/
theorem block_diagonal_lagrangian_dual_value_eq_sInf
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ) :
    block_diagonal_lagrangian_dual_value B b D d c =
      sInf
        ((fun lam : Fin q → ℝ ↦ block_diagonal_lagrangian_relaxation_value B b D d c lam) ''
          Set.Ici (0 : Fin q → ℝ)) := rfl

/-- Corollary for Exercise 8.3: for a binary block-diagonal problem with nice block constraints
`B_j x^j ≤ b^j` and complicating constraints `∑_j D_j x^j ≤ d`, where
`Q_j = block_binary_patterns B b j`, the Lagrangian dual value is the infimum over all
nonnegative multipliers `λ` of `λ d + ∑_j max_{v ∈ Q_j} (c^j - λ D_j) v`. -/
theorem block_diagonal_lagrangian_dual_value_eq_inf_sum_block_values
    (B : (j : Fin p) → Matrix (Fin (m j)) (Fin (n j)) ℝ)
    (b : (j : Fin p) → Fin (m j) → ℝ)
    (D : (j : Fin p) → Matrix (Fin q) (Fin (n j)) ℝ)
    (d : Fin q → ℝ)
    (c : (j : Fin p) → Fin (n j) → ℝ) :
    block_diagonal_lagrangian_dual_value B b D d c =
      sInf
        ((fun lam : Fin q → ℝ ↦
            ((lam ⬝ᵥ d : ℝ) : WithBot ℝ) +
              ∑ j, block_diagonal_lagrangian_block_value B b D c lam j) ''
          Set.Ici (0 : Fin q → ℝ)) := by
  simp [block_diagonal_lagrangian_dual_value,
    block_diagonal_lagrangian_relaxation_value_eq_sum_block_values]

end Exercise83
