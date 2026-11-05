/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_2.ch4_sec4_3_2_remark_4_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section Exercise64

variable {m n : ℕ}

/-- The row-sum residue vector obtained from the first `t` variables of the nonnegative integer
assignment `x`. -/
def exercise_6_4_partial_residue
    (a : Matrix (Fin m) (Fin n) ℚ)
    (t : Fin (n + 1))
    (x : Fin n → ℕ) : Fin m → ℚ :=
  fun i ↦
    Int.fract
      (Finset.sum (Finset.univ.filter fun j : Fin n ↦ j.1 < t.1) fun j ↦ a i j * (x j : ℚ))

/-- A concrete common modulus for the rational data of Exercise 6.4, obtained by multiplying all
row-right-hand-side denominators and all matrix-entry denominators. -/
def exercise_6_4_modulus
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : ℕ :=
  (∏ i, (b i).den) * ∏ i, ∏ j, (a i j).den

/-- The bounded residue representatives used by the staged graph of Exercise 6.4. -/
abbrev exercise_6_4_bounded_assignment
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :=
  Fin n → Fin (exercise_6_4_modulus a b)

/-- The finite stage-`t` state space obtained by restricting each variable to a bounded
representative modulo the common data modulus. -/
def exercise_6_4_state_space_at
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1)) : Finset (Fin m → ℚ) :=
  Finset.univ.image fun x : exercise_6_4_bounded_assignment a b ↦
    exercise_6_4_partial_residue a t (fun j ↦ (x j : ℕ))

/-- The zero residue vector belongs to the initial stage-state space. -/
theorem exercise_6_4_zero_residue_mem_state_space
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    (fun _ : Fin m ↦ (0 : ℚ)) ∈ exercise_6_4_state_space_at a b 0 := by
  classical
  have hmod : 0 < exercise_6_4_modulus a b := by
    unfold exercise_6_4_modulus
    positivity
  let x : exercise_6_4_bounded_assignment a b := fun _ ↦ ⟨0, hmod⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨x, by simp [x], ?_⟩
  ext i
  simp [x, exercise_6_4_partial_residue]

/-- Helper for Exercise 6.4: the common modulus is positive because it is a product of positive
rational denominators. -/
theorem exercise_6_4_modulus_pos
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    0 < exercise_6_4_modulus a b := by
  -- Every denominator is positive, so the defining product is positive as well.
  unfold exercise_6_4_modulus
  positivity

/-- Helper for Exercise 6.4: each matrix-entry denominator divides the common modulus. -/
theorem exercise_6_4_matrixEntry_den_dvd_modulus
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (j : Fin n) :
    (a i j).den ∣ exercise_6_4_modulus a b := by
  -- The entry denominator appears as a factor in the matrix-denominator product.
  unfold exercise_6_4_modulus
  have h_inner : (a i j).den ∣ ∏ j' : Fin n, (a i j').den := by
    exact Finset.dvd_prod_of_mem (fun j' : Fin n ↦ (a i j').den)
      (by simp : j ∈ (Finset.univ : Finset (Fin n)))
  have h_outer : (∏ j' : Fin n, (a i j').den) ∣ ∏ i' : Fin m, ∏ j' : Fin n, (a i' j').den := by
    exact Finset.dvd_prod_of_mem (fun i' : Fin m ↦ ∏ j' : Fin n, (a i' j').den)
      (by simp : i ∈ (Finset.univ : Finset (Fin m)))
  exact dvd_trans (dvd_trans h_inner h_outer) (dvd_mul_left _ _)

/-- Helper for Exercise 6.4: multiplying any matrix entry by the common modulus produces an
integer. -/
theorem exercise_6_4_matrixEntry_mul_modulus_eq_int
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (i : Fin m)
    (j : Fin n) :
    ∃ z : ℤ, a i j * (exercise_6_4_modulus a b : ℚ) = z := by
  rcases exercise_6_4_matrixEntry_den_dvd_modulus a b i j with ⟨k, hk⟩
  -- Clear the denominator by factoring the common modulus through `(a i j).den`.
  refine ⟨(a i j).num * k, ?_⟩
  calc
    a i j * (exercise_6_4_modulus a b : ℚ)
        = a i j * (((a i j).den * k : ℕ) : ℚ) := by rw [hk]
    _ = (a i j * (a i j).den) * k := by rw [Nat.cast_mul, mul_assoc]
    _ = ((a i j).num : ℚ) * k := by rw [Rat.mul_den_eq_num]
    _ = ((a i j).num * k : ℤ) := by norm_num

/-- Helper for Exercise 6.4: reducing each variable modulo the common modulus leaves every stage
residue unchanged. -/
theorem exercise_6_4_partial_residue_mod_modulus
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1))
    (x : Fin n → ℕ) :
    exercise_6_4_partial_residue a t x =
      exercise_6_4_partial_residue a t
        (fun j ↦ x j % exercise_6_4_modulus a b) := by
  let M := exercise_6_4_modulus a b
  ext i
  let s := Finset.univ.filter (fun j : Fin n ↦ j.1 < t.1)
  classical
  let z : Fin n → ℤ := fun j ↦
    Classical.choose (exercise_6_4_matrixEntry_mul_modulus_eq_int a b i j) *
      (((x j : ℕ) : ℤ) / ((M : ℕ) : ℤ))
  have hz :
      ∀ j : Fin n,
        a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ) = z j := by
    intro j
    dsimp [z]
    have hzij := Classical.choose_spec (exercise_6_4_matrixEntry_mul_modulus_eq_int a b i j)
    calc
      a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ) =
          ((Classical.choose (exercise_6_4_matrixEntry_mul_modulus_eq_int a b i j) : ℤ) : ℚ) *
            ((((x j : ℕ) : ℤ) / ((M : ℕ) : ℤ) : ℤ) : ℚ) := by
        simpa [M, mul_assoc, Int.natCast_ediv] using
          congrArg (fun q : ℚ => q * ((x j / M : ℕ) : ℚ)) hzij
      _ =
          ((Classical.choose (exercise_6_4_matrixEntry_mul_modulus_eq_int a b i j) *
              (((x j : ℕ) : ℤ) / ((M : ℕ) : ℤ)) : ℤ) : ℚ) := by
        rw [Int.cast_mul]
  have hsplit :
      Finset.sum s (fun j ↦ a i j * (x j : ℚ)) =
        Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ)) +
          Finset.sum s (fun j ↦ a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ)) := by
    -- Split each variable into its residue modulo `M` plus a multiple of `M`.
    calc
      Finset.sum s (fun j ↦ a i j * (x j : ℚ)) =
          Finset.sum s
            (fun j ↦
              a i j * ((x j % M : ℕ) : ℚ) +
                a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hxj :
            (x j : ℚ) = ((x j % M + M * (x j / M) : ℕ) : ℚ) := by
          exact_mod_cast (Nat.mod_add_div (x j) M).symm
        calc
          a i j * (x j : ℚ) = a i j * (((x j % M + M * (x j / M) : ℕ) : ℚ)) := by rw [hxj]
          _ =
              a i j * ((x j % M : ℕ) : ℚ) +
                a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ) := by
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
      _ =
          Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ)) +
            Finset.sum s (fun j ↦ a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ)) := by
        rw [Finset.sum_add_distrib]
  have hfract :
      Int.fract (Finset.sum s (fun j ↦ a i j * (x j : ℚ))) =
        Int.fract (Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ))) := by
    -- The difference between the two sums is an integer-valued correction term.
    refine (Int.fract_eq_fract).2 ?_
    refine ⟨Finset.sum s z, ?_⟩
    calc
      Finset.sum s (fun j ↦ a i j * (x j : ℚ)) -
          Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ)) =
          (Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ)) +
              Finset.sum s (fun j ↦ a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ))) -
            Finset.sum s (fun j ↦ a i j * ((x j % M : ℕ) : ℚ)) := by
        rw [hsplit]
      _ =
          Finset.sum s (fun j ↦ a i j * (M : ℚ) * ((x j / M : ℕ) : ℚ)) := by
        ring
      _ = Finset.sum s (fun j ↦ ((z j : ℤ) : ℚ)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hz j
      _ = ((Finset.sum s z : ℤ) : ℚ) := by
        simp
  simpa [exercise_6_4_partial_residue, s] using hfract

/-- Helper for Exercise 6.4: the stage residue of every bounded assignment is one of the explicit
finite states. -/
theorem exercise_6_4_partial_residue_mem_state_space_of_bounded
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1))
    (x : exercise_6_4_bounded_assignment a b) :
    exercise_6_4_partial_residue a t (fun j ↦ (x j : ℕ)) ∈
      exercise_6_4_state_space_at a b t := by
  classical
  -- Package the bounded assignment itself as the witness for the image definition.
  refine Finset.mem_image.mpr ?_
  exact ⟨x, by simp, rfl⟩

/-- Part (1) of Exercise 6.4. The modulo-`1` row-sum vector of every nonnegative
integer assignment lies in the explicit finite set
`exercise_6_4_state_space_at a b (Fin.last n)`, so only finitely many different
sums `∑_{j ∈ N} a_{ij} x_j` can occur modulo `1`. -/
theorem exercise_6_4_finitely_many_mod_one_row_sums
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : Fin n → ℕ) :
    exercise_6_4_partial_residue a (Fin.last n) x ∈
      exercise_6_4_state_space_at a b (Fin.last n) := by
  classical
  let M := exercise_6_4_modulus a b
  have hM : 0 < M := exercise_6_4_modulus_pos a b
  let xmod : exercise_6_4_bounded_assignment a b :=
    fun j ↦ ⟨x j % M, Nat.mod_lt _ hM⟩
  -- Replace `x` by its bounded representatives modulo the common modulus.
  have hres :
      exercise_6_4_partial_residue a (Fin.last n) x =
        exercise_6_4_partial_residue a (Fin.last n) (fun j ↦ (xmod j : ℕ)) := by
    simpa [xmod, M] using
      exercise_6_4_partial_residue_mod_modulus a b (Fin.last n) x
  rw [hres]
  -- The reduced assignment is itself one of the finite witnesses defining the state space.
  exact exercise_6_4_partial_residue_mem_state_space_of_bounded a b (Fin.last n) xmod

/-- The right-hand-side residue vector `b mod 1` from Exercise 6.4. -/
def exercise_6_4_rhs_residue (b : Fin m → ℚ) : Fin m → ℚ :=
  fun i ↦ Int.fract (b i)

/-- A nonnegative integer assignment is feasible for the Exercise 6.4 congruence system when its
row sums agree with `b` modulo `1`. -/
def exercise_6_4_is_feasible_solution
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : Fin n → ℕ) : Prop :=
  exercise_6_4_partial_residue a (Fin.last n) x = exercise_6_4_rhs_residue b

/-- The linear objective value `∑_{j ∈ N} c_j x_j` of a nonnegative integer assignment. -/
def exercise_6_4_objective
    (c : Fin n → ℚ)
    (x : Fin n → ℕ) : ℝ :=
  ∑ j, (c j : ℝ) * (x j : ℝ)

/-- A bounded representative assignment is feasible when its residue vector satisfies the same
Exercise 6.4 congruence system. -/
def exercise_6_4_is_bounded_feasible_solution
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b) : Prop :=
  exercise_6_4_is_feasible_solution a b (fun j ↦ (x j : ℕ))

/-- The objective value of a bounded representative assignment in the staged graph model of
Exercise 6.4. -/
def exercise_6_4_bounded_objective
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b) : ℝ :=
  exercise_6_4_objective c (fun j ↦ (x j : ℕ))

/-- Updating a residue vector by choosing the value `u` for the variable indexed by `j`. -/
def exercise_6_4_step_residue
    (a : Matrix (Fin m) (Fin n) ℚ)
    (j : Fin n)
    (r : Fin m → ℚ)
    (u : ℕ) : Fin m → ℚ :=
  fun i ↦ Int.fract (r i + a i j * (u : ℚ))

/-- The stage-`j + 1` partial residue is obtained from the stage-`j` residue by adding the
contribution of the variable indexed by `j` and taking fractional parts. -/
theorem exercise_6_4_partial_residue_succ
    (a : Matrix (Fin m) (Fin n) ℚ)
    (j : Fin n)
    (x : Fin n → ℕ) :
    exercise_6_4_partial_residue a j.succ x =
      exercise_6_4_step_residue a j
        (exercise_6_4_partial_residue a j.castSucc x) (x j) := by
  ext i
  have hcastSucc :
      Finset.univ.filter (fun k : Fin n ↦ k.1 < j.castSucc.1) = Finset.Iio j := by
    ext k
    simp [Finset.mem_Iio]
  have hsucc :
      Finset.univ.filter (fun k : Fin n ↦ k.1 < j.succ.1) = Finset.Iic j := by
    ext k
    simp [Finset.mem_Iic]
  rw [exercise_6_4_partial_residue, hsucc, exercise_6_4_step_residue]
  conv_rhs =>
    rw [exercise_6_4_partial_residue, hcastSucc]
  rw [← Finset.Iio_insert j, Finset.sum_insert Finset.notMem_Iio_self, add_comm]
  refine (Int.fract_eq_fract).2 ?_
  refine ⟨Int.floor (Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)), ?_⟩
  calc
    ((Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)) + a i j * (x j : ℚ)) -
          (Int.fract (Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)) +
            a i j * (x j : ℚ)) =
        (Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)) -
          Int.fract (Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)) := by
      ring
    _ = Int.floor (Finset.sum (Finset.Iio j) fun k ↦ a i k * (x k : ℚ)) := by simp

/-- If `r` is a stage-`j` residue state and `u` is a bounded representative for the next
variable, then the updated residue vector is a stage-`j + 1` state. -/
theorem exercise_6_4_step_residue_mem_state_space
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (j : Fin n)
    (r : exercise_6_4_state_space_at a b j.castSucc)
    (u : Fin (exercise_6_4_modulus a b)) :
    exercise_6_4_step_residue a j r u ∈
      exercise_6_4_state_space_at a b j.succ := by
  classical
  rcases r with ⟨r, hr⟩
  rcases Finset.mem_image.mp (by
      change r ∈
          Finset.univ.image
            (fun x : exercise_6_4_bounded_assignment a b ↦
              exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ)))
      simpa [exercise_6_4_state_space_at] using hr) with
    ⟨x, -, hx⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨Function.update x j u, by simp, ?_⟩
  rw [exercise_6_4_partial_residue_succ]
  have hupdate :
      exercise_6_4_partial_residue a j.castSucc
          (fun k ↦ ((Function.update x j u) k : ℕ)) =
        exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ)) := by
    ext i
    have hcastSucc :
        Finset.univ.filter (fun k : Fin n ↦ k.1 < j.castSucc.1) = Finset.Iio j := by
      ext k
      simp [Finset.mem_Iio]
    rw [exercise_6_4_partial_residue, exercise_6_4_partial_residue, hcastSucc]
    refine congrArg Int.fract ?_
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_ne : k ≠ j := ne_of_lt (Finset.mem_Iio.mp hk)
    by_cases hkj : k = j
    · exact (hk_ne hkj).elim
    · simp [Function.update, hkj]
  rw [hupdate, hx]
  simp

/-- The terminal stage states whose residue vector already equals the right-hand side `b mod 1`. -/
def exercise_6_4_terminal_states
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    Finset (exercise_6_4_state_space_at a b (Fin.last n)) :=
  (exercise_6_4_state_space_at a b (Fin.last n)).attach.filter fun r ↦
    r = exercise_6_4_rhs_residue b

/-- Helper for Exercise 6.4: membership in the terminal-state finset is exactly equality with the
right-hand-side residue vector. -/
theorem exercise_6_4_mem_terminal_states_iff
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (r : exercise_6_4_state_space_at a b (Fin.last n)) :
    r ∈ exercise_6_4_terminal_states a b ↔
      (r : Fin m → ℚ) = exercise_6_4_rhs_residue b := by
  -- The terminal states are precisely the attached final-stage states satisfying this equality.
  simp [exercise_6_4_terminal_states]

/-- The stage vertices of the Exercise 6.4 shortest-path graph together with a distinguished sink
node `none`. -/
abbrev exercise_6_4_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :=
  Option (Σ t : Fin (n + 1), exercise_6_4_state_space_at a b t)

/-- The nonterminal arcs choose the next variable value modulo the common data modulus; the
terminal arcs connect a final-stage state matching `b mod 1` to the sink. -/
abbrev exercise_6_4_arc
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :=
  (Σ j : Fin n, exercise_6_4_state_space_at a b j.castSucc ×
      Fin (exercise_6_4_modulus a b)) ⊕
    exercise_6_4_terminal_states a b

/-- The distinguished source vertex of the staged shortest-path graph for Exercise 6.4. -/
def exercise_6_4_source_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : exercise_6_4_vertex a b :=
  some ⟨0, ⟨(fun _ : Fin m ↦ (0 : ℚ)), exercise_6_4_zero_residue_mem_state_space a b⟩⟩

/-- The distinguished sink vertex of the staged shortest-path graph for Exercise 6.4. -/
def exercise_6_4_sink_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : exercise_6_4_vertex a b :=
  none

/-- The head-stage state reached by a nonterminal arc in the Exercise 6.4 residue graph. -/
def exercise_6_4_step_target
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (e : Σ j : Fin n, exercise_6_4_state_space_at a b j.castSucc ×
        Fin (exercise_6_4_modulus a b)) :
    Σ t : Fin (n + 1), exercise_6_4_state_space_at a b t :=
  ⟨e.1.succ, ⟨exercise_6_4_step_residue a e.1 e.2.1 e.2.2,
    exercise_6_4_step_residue_mem_state_space a b e.1 e.2.1 e.2.2⟩⟩

/-- The tail map of the Exercise 6.4 staged shortest-path graph. -/
def exercise_6_4_arc_tail
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    exercise_6_4_arc a b → exercise_6_4_vertex a b
  | Sum.inl e => some ⟨e.1.castSucc, e.2.1⟩
  | Sum.inr e => some ⟨Fin.last n, e.1⟩

/-- The head map of the Exercise 6.4 staged shortest-path graph. -/
def exercise_6_4_arc_head
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    exercise_6_4_arc a b → exercise_6_4_vertex a b
  | Sum.inl e => some (exercise_6_4_step_target a b e)
  | Sum.inr _ => exercise_6_4_sink_vertex a b

/-- The arc-length function induced by the objective coefficients `c` on the Exercise 6.4 graph. -/
def exercise_6_4_arc_length
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ) :
    exercise_6_4_arc a b → ℝ
  | Sum.inl e => (c e.1 : ℝ) * ((e.2.2 : ℕ) : ℝ)
  | Sum.inr _ => 0

/-- The concrete shortest-path instance attached to Exercise 6.4, using the staged residue graph,
the stage-`0` zero-residue source, the terminal sink, and arc lengths induced by the objective
coefficients `c`. -/
def exercise_6_4_shortest_path_problem
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ) :
    ShortestPathLinearProgram (exercise_6_4_vertex a b) (exercise_6_4_arc a b) where
  tail := exercise_6_4_arc_tail a b
  head := exercise_6_4_arc_head a b
  s := exercise_6_4_source_vertex a b
  t := exercise_6_4_sink_vertex a b
  length := exercise_6_4_arc_length a b c

@[simp] theorem exercise_6_4_shortest_path_problem_s
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ) :
    (exercise_6_4_shortest_path_problem a b c).s = exercise_6_4_source_vertex a b := rfl

@[simp] theorem exercise_6_4_shortest_path_problem_t
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ) :
    (exercise_6_4_shortest_path_problem a b c).t = exercise_6_4_sink_vertex a b := rfl

@[simp] theorem exercise_6_4_shortest_path_problem_tail
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (e : exercise_6_4_arc a b) :
    (exercise_6_4_shortest_path_problem a b c).tail e = exercise_6_4_arc_tail a b e := rfl

@[simp] theorem exercise_6_4_shortest_path_problem_head
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (e : exercise_6_4_arc a b) :
    (exercise_6_4_shortest_path_problem a b c).head e = exercise_6_4_arc_head a b e := rfl

@[simp] theorem exercise_6_4_shortest_path_problem_length
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (e : exercise_6_4_arc a b) :
    (exercise_6_4_shortest_path_problem a b c).length e = exercise_6_4_arc_length a b c e := rfl

/-- Helper for Exercise 6.4: the suffix objective beginning at stage `t` is the contribution of
all variables whose stage has not yet been traversed. -/
def exercise_6_4_stage_objective
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (t : Fin (n + 1))
    (x : exercise_6_4_bounded_assignment a b) : ℝ :=
  Finset.sum (Finset.univ.filter fun j : Fin n ↦ t.1 ≤ j.1) fun j ↦
    (c j : ℝ) * ((x j : ℕ) : ℝ)

/-- Helper for Exercise 6.4: once the walk reaches the final stage, no objective contribution
remains. -/
theorem exercise_6_4_stage_objective_last
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b) :
    exercise_6_4_stage_objective (a := a) (b := b) c (Fin.last n) x = 0 := by
  -- No index in `Fin n` lies at or beyond the final stage.
  have hfilter :
      Finset.univ.filter (fun j : Fin n ↦ (Fin.last n : Fin (n + 1)).1 ≤ j.1) = ∅ := by
    ext j
    simp [not_le_of_gt j.2]
  rw [exercise_6_4_stage_objective, hfilter]
  simp

/-- Helper for Exercise 6.4: the suffix objective at stage `j.castSucc` splits into the stage-`j`
arc cost plus the remaining suffix objective. -/
theorem exercise_6_4_stage_objective_castSucc
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n) :
    exercise_6_4_stage_objective (a := a) (b := b) c j.castSucc x =
      (c j : ℝ) * ((x j : ℕ) : ℝ) +
        exercise_6_4_stage_objective (a := a) (b := b) c j.succ x := by
  have hfilter :
      Finset.univ.filter (fun k : Fin n ↦ j.castSucc.1 ≤ k.1) =
        insert j (Finset.univ.filter fun k : Fin n ↦ j.succ.1 ≤ k.1) := by
    ext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
      omega
  -- Split the current-stage term from the strictly later suffix.
  rw [exercise_6_4_stage_objective, hfilter, Finset.sum_insert]
  · simp [exercise_6_4_stage_objective]
  · simp

/-- Helper for Exercise 6.4: the stage-`0` suffix objective is the full bounded objective. -/
theorem exercise_6_4_stage_objective_zero
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b) :
    exercise_6_4_stage_objective (a := a) (b := b) c 0 x =
      exercise_6_4_bounded_objective a b c x := by
  -- Every variable index belongs to the stage-`0` suffix.
  simp [exercise_6_4_stage_objective, exercise_6_4_bounded_objective, exercise_6_4_objective]

/-- Helper for Exercise 6.4: the partial residue at stage `0` is always the zero vector. -/
theorem exercise_6_4_partial_residue_zero
    (a : Matrix (Fin m) (Fin n) ℚ)
    (x : exercise_6_4_bounded_assignment a b) :
    exercise_6_4_partial_residue a 0 (fun j ↦ (x j : ℕ)) = fun _ : Fin m ↦ (0 : ℚ) := by
  -- The stage-`0` filter is empty, so each row sum is zero before taking the fractional part.
  ext i
  simp [exercise_6_4_partial_residue]

/-- Helper for Exercise 6.4: the canonical vertex at stage `t` records the residue produced by a
bounded assignment after traversing the first `t` stages. -/
def exercise_6_4_stage_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1))
    (x : exercise_6_4_bounded_assignment a b) : exercise_6_4_vertex a b :=
  some ⟨t,
    ⟨exercise_6_4_partial_residue a t (fun j ↦ (x j : ℕ)),
      exercise_6_4_partial_residue_mem_state_space_of_bounded a b t x⟩⟩

/-- Helper for Exercise 6.4: equal stage residues determine the same canonical stage vertex. -/
theorem exercise_6_4_stage_vertex_eq_of_residue_eq
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1))
    (x y : exercise_6_4_bounded_assignment a b)
    (hres :
      exercise_6_4_partial_residue a t (fun j ↦ (x j : ℕ)) =
        exercise_6_4_partial_residue a t (fun j ↦ (y j : ℕ))) :
    exercise_6_4_stage_vertex a b t x = exercise_6_4_stage_vertex a b t y := by
  -- Reduce the packaged vertex equality to equality of the underlying residue functions.
  simpa [exercise_6_4_stage_vertex, hres]

/-- Helper for Exercise 6.4: the stage-`t` partial residue depends only on coordinates whose
index is strictly smaller than `t`. -/
theorem exercise_6_4_partial_residue_eq_of_eqOn_prefix
    (a : Matrix (Fin m) (Fin n) ℚ)
    (t : Fin (n + 1))
    (x y : Fin n → ℕ)
    (hxy : ∀ j : Fin n, j.1 < t.1 → x j = y j) :
    exercise_6_4_partial_residue a t x =
      exercise_6_4_partial_residue a t y := by
  -- Compare the filtered row sums term-by-term on the prefix that stage `t` can see.
  ext i
  unfold exercise_6_4_partial_residue
  refine congrArg Int.fract ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hxy j]
  simpa using (Finset.mem_filter.mp hj).2

/-- Helper for Exercise 6.4: bounded assignments with the same prefix define the same canonical
stage vertex. -/
theorem exercise_6_4_stage_vertex_eq_of_eqOn_prefix
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (t : Fin (n + 1))
    (x y : exercise_6_4_bounded_assignment a b)
    (hxy : ∀ j : Fin n, j.1 < t.1 → x j = y j) :
    exercise_6_4_stage_vertex a b t x =
      exercise_6_4_stage_vertex a b t y := by
  -- Convert prefix agreement of bounded values into equality of the visible partial residues.
  apply exercise_6_4_stage_vertex_eq_of_residue_eq
  exact exercise_6_4_partial_residue_eq_of_eqOn_prefix a t
    (fun j ↦ (x j : ℕ)) (fun j ↦ (y j : ℕ))
    (fun j hj ↦ by simpa using congrArg Fin.val (hxy j hj))

/-- Helper for Exercise 6.4: every bounded assignment realizes the distinguished source vertex at
stage `0`. -/
theorem exercise_6_4_source_vertex_eq_stage_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b) :
    exercise_6_4_source_vertex a b = exercise_6_4_stage_vertex a b 0 x := by
  have hzero := exercise_6_4_partial_residue_zero (a := a) (b := b) x
  -- The stage-`0` canonical residue is exactly the zero residue used to define the source.
  simpa [exercise_6_4_source_vertex, exercise_6_4_stage_vertex, hzero]

/-- Helper for Exercise 6.4: changing the current stage variable leaves the preceding partial
residue unchanged. -/
theorem exercise_6_4_partial_residue_castSucc_update
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (j : Fin n)
    (x : exercise_6_4_bounded_assignment a b)
    (u : Fin (exercise_6_4_modulus a b)) :
    exercise_6_4_partial_residue a j.castSucc (fun k ↦ ((Function.update x j u) k : ℕ)) =
      exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ)) := by
  -- Stage `j.castSucc` only sums indices strictly smaller than `j`, so updating `j` itself is
  -- invisible to that partial residue.
  ext i
  have hcastSucc :
      Finset.univ.filter (fun k : Fin n ↦ k.1 < j.castSucc.1) = Finset.Iio j := by
    ext k
    simp [Finset.mem_Iio]
  rw [exercise_6_4_partial_residue, exercise_6_4_partial_residue, hcastSucc]
  refine congrArg Int.fract ?_
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_ne : k ≠ j := ne_of_lt (Finset.mem_Iio.mp hk)
  simp [Function.update, hk_ne]

/-- Helper for Exercise 6.4: updating coordinate `j` changes the next-stage residue exactly by the
step-residue formula. -/
theorem exercise_6_4_partial_residue_succ_update
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n)
    (u : Fin (exercise_6_4_modulus a b)) :
    exercise_6_4_partial_residue a j.succ (fun k ↦ ((Function.update x j u) k : ℕ)) =
      exercise_6_4_step_residue a j
        (exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ))) u := by
  -- First rewrite the updated next-stage residue in owner normal form.
  calc
    exercise_6_4_partial_residue a j.succ (fun k ↦ ((Function.update x j u) k : ℕ)) =
        exercise_6_4_step_residue a j
          (exercise_6_4_partial_residue a j.castSucc
            (fun k ↦ ((Function.update x j u) k : ℕ)))
          ((Function.update x j u) j) := by
      simpa using
        exercise_6_4_partial_residue_succ a j (fun k ↦ ((Function.update x j u) k : ℕ))
    _ =
        exercise_6_4_step_residue a j
          (exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ))) u := by
      rw [exercise_6_4_partial_residue_castSucc_update a b j x u]
      simp [Function.update]

/-- Helper for Exercise 6.4: after updating stage `j` to the bounded value `u`, the canonical
stage-`j + 1` vertex is exactly the head reached by that choice. -/
theorem exercise_6_4_stage_vertex_succ_update
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n)
    (u : Fin (exercise_6_4_modulus a b)) :
    exercise_6_4_stage_vertex a b j.succ (Function.update x j u) =
      some
        ⟨j.succ,
          ⟨exercise_6_4_step_residue a j
              (exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ))) u,
            exercise_6_4_step_residue_mem_state_space a b j
              ⟨exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ)),
                exercise_6_4_partial_residue_mem_state_space_of_bounded a b j.castSucc x⟩
              u⟩⟩ := by
  -- Route correction: compare underlying residues first, then let proof irrelevance handle the
  -- packaged sigma/subtype vertex.
  have hres :
      exercise_6_4_partial_residue a j.succ
        (fun k ↦ ((Function.update x j u) k : ℕ)) =
        exercise_6_4_step_residue a j
          (exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ))) u :=
    exercise_6_4_partial_residue_succ_update a b x j u
  simpa [exercise_6_4_stage_vertex, hres]

/-- Helper for Exercise 6.4: the canonical nonterminal arc at stage `j` uses the residue already
generated by the bounded assignment and labels the arc by the chosen bounded value `x j`. -/
def exercise_6_4_step_arc
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n) : exercise_6_4_arc a b :=
  Sum.inl
    ⟨j,
      ⟨⟨exercise_6_4_partial_residue a j.castSucc (fun k ↦ (x k : ℕ)),
          exercise_6_4_partial_residue_mem_state_space_of_bounded a b j.castSucc x⟩,
        x j⟩⟩

/-- Helper for Exercise 6.4: the canonical nonterminal arc starts at the corresponding canonical
stage vertex. -/
theorem exercise_6_4_step_arc_tail
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n) :
    exercise_6_4_arc_tail a b (exercise_6_4_step_arc a b x j) =
      exercise_6_4_stage_vertex a b j.castSucc x := by
  -- The step arc is constructed from the stage-`j` residue state of `x`.
  rfl

/-- Helper for Exercise 6.4: the canonical nonterminal arc lands at the next canonical stage
vertex of the same bounded assignment. -/
theorem exercise_6_4_step_arc_head
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n) :
    exercise_6_4_arc_head a b (exercise_6_4_step_arc a b x j) =
      exercise_6_4_stage_vertex a b j.succ x := by
  -- The stage-`j + 1` residue of `x` is obtained by taking the step labeled by `x j`.
  simpa [exercise_6_4_step_arc, exercise_6_4_arc_head, exercise_6_4_step_target,
    exercise_6_4_stage_vertex_succ_update] using
    (exercise_6_4_stage_vertex_succ_update a b x j (x j)).symm

/-- Helper for Exercise 6.4: the canonical nonterminal arc contributes exactly the stage-`j`
objective term. -/
theorem exercise_6_4_step_arc_length
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (j : Fin n) :
    exercise_6_4_arc_length a b c (exercise_6_4_step_arc a b x j) =
      (c j : ℝ) * ((x j : ℕ) : ℝ) := by
  -- The arc length was defined precisely from the chosen stage label.
  rfl

/-- Helper for Exercise 6.4: feasibility says the canonical final-stage state belongs to the
terminal-state filter. -/
theorem exercise_6_4_terminal_state_mem
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) :
    ⟨exercise_6_4_partial_residue a (Fin.last n) (fun j ↦ (x j : ℕ)),
      exercise_6_4_partial_residue_mem_state_space_of_bounded a b (Fin.last n) x⟩ ∈
      exercise_6_4_terminal_states a b := by
  -- Read terminal-state membership through the cleaned equality interface.
  rw [exercise_6_4_mem_terminal_states_iff]
  simpa [exercise_6_4_is_bounded_feasible_solution, exercise_6_4_is_feasible_solution] using hx

/-- Helper for Exercise 6.4: the canonical terminal arc is the unique final-stage arc witnessing
feasibility of a bounded assignment. -/
def exercise_6_4_terminal_arc
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) : exercise_6_4_arc a b :=
  Sum.inr
    ⟨⟨exercise_6_4_partial_residue a (Fin.last n) (fun j ↦ (x j : ℕ)),
        exercise_6_4_partial_residue_mem_state_space_of_bounded a b (Fin.last n) x⟩,
      exercise_6_4_terminal_state_mem a b x hx⟩

/-- Helper for Exercise 6.4: the canonical terminal arc starts at the canonical final-stage
vertex. -/
theorem exercise_6_4_terminal_arc_tail
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) :
    exercise_6_4_arc_tail a b (exercise_6_4_terminal_arc a b x hx) =
      exercise_6_4_stage_vertex a b (Fin.last n) x := by
  -- The terminal arc is built from the canonical final-stage state of `x`.
  rfl

/-- Helper for Exercise 6.4: the canonical terminal arc ends at the distinguished sink. -/
theorem exercise_6_4_terminal_arc_head
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) :
    exercise_6_4_arc_head a b (exercise_6_4_terminal_arc a b x hx) =
      exercise_6_4_sink_vertex a b := by
  -- Terminal arcs are defined to point directly to the sink.
  rfl

/-- Helper for Exercise 6.4: the canonical terminal arc has zero length. -/
theorem exercise_6_4_terminal_arc_length
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) :
    exercise_6_4_arc_length a b c (exercise_6_4_terminal_arc a b x hx) = 0 := by
  -- The terminal arc carries no objective cost.
  rfl

/-- Helper for Exercise 6.4: no arc leaves the sink vertex, so every walk from the sink to itself
is empty. -/
theorem exercise_6_4_walk_from_sink_nil
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (p : List (exercise_6_4_arc a b))
    (hwalk :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (exercise_6_4_sink_vertex a b) (exercise_6_4_sink_vertex a b) p) :
    p = [] := by
  cases p with
  | nil =>
      rfl
  | cons e p =>
      rcases hwalk with ⟨htail, _⟩
      -- No Exercise 6.4 arc has tail equal to the sink vertex `none`.
      cases e <;> cases htail

/-- Helper for Exercise 6.4: a final-stage canonical vertex that belongs to the terminal-state
filter already satisfies the congruence system. -/
theorem exercise_6_4_feasible_of_terminal_stage_vertex
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (r : exercise_6_4_state_space_at a b (Fin.last n))
    (hvertex : exercise_6_4_stage_vertex a b (Fin.last n) x = some ⟨Fin.last n, r⟩)
    (hr : r ∈ exercise_6_4_terminal_states a b) :
    exercise_6_4_is_bounded_feasible_solution a b x := by
  have hrhs : (r : Fin m → ℚ) = exercise_6_4_rhs_residue b :=
    (exercise_6_4_mem_terminal_states_iff a b r).1 hr
  have hstage :
      exercise_6_4_partial_residue a (Fin.last n) (fun j ↦ (x j : ℕ)) = (r : Fin m → ℚ) := by
    -- Strip the sigma/subtype packaging from the canonical final-stage vertex equality.
    have hstate :
        (⟨exercise_6_4_partial_residue a (Fin.last n) (fun j ↦ (x j : ℕ)),
          exercise_6_4_partial_residue_mem_state_space_of_bounded a b (Fin.last n) x⟩ :
            exercise_6_4_state_space_at a b (Fin.last n)) = r := by
      simpa [exercise_6_4_stage_vertex] using hvertex
    exact congrArg (fun z : exercise_6_4_state_space_at a b (Fin.last n) => (z : Fin m → ℚ))
      hstate
  -- Terminal-state membership rewrites the final-stage residue to `b mod 1`.
  unfold exercise_6_4_is_bounded_feasible_solution exercise_6_4_is_feasible_solution
  exact hstage.trans hrhs

/-- Helper for Exercise 6.4: every vertex visited by a directed walk from stage `t` is either the
sink or a stage vertex with index at least `t`. -/
theorem exercise_6_4_walkVerticesFrom_stage_lower_bound
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (t : Fin (n + 1))
    (r : exercise_6_4_state_space_at a b t)
    (p : List (exercise_6_4_arc a b))
    (hwalk :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (some ⟨t, r⟩) (exercise_6_4_sink_vertex a b) p) :
    ∀ w ∈ (exercise_6_4_shortest_path_problem a b c).walkVerticesFrom (some ⟨t, r⟩) p,
      w = exercise_6_4_sink_vertex a b ∨
        ∃ s, ∃ r' : exercise_6_4_state_space_at a b s, w = some ⟨s, r'⟩ ∧ t.1 ≤ s.1 := by
  induction p generalizing t r with
  | nil =>
      intro w hw
      -- The empty walk visits only its starting stage vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom] at hw
      subst hw
      exact Or.inr ⟨t, r, rfl, le_rfl⟩
  | cons e p ih =>
      rcases hwalk with ⟨htail, hrest⟩
      intro w hw
      rw [ShortestPathLinearProgram.walkVerticesFrom] at hw
      rcases List.mem_cons.1 hw with rfl | hwTail
      · exact Or.inr ⟨t, r, rfl, le_rfl⟩
      · cases e with
        | inl e =>
            cases htail
            let rnext : exercise_6_4_state_space_at a b e.1.succ :=
              ⟨exercise_6_4_step_residue a e.1 e.2.1 e.2.2,
                exercise_6_4_step_residue_mem_state_space a b e.1 e.2.1 e.2.2⟩
            have hrest' :
                (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
                  (some ⟨e.1.succ, rnext⟩) (exercise_6_4_sink_vertex a b) p := by
              simpa [exercise_6_4_shortest_path_problem, exercise_6_4_arc_head,
                exercise_6_4_step_target, rnext] using hrest
            -- Every later visited nonterminal vertex lies in a stage strictly after `e.1.castSucc`.
            rcases ih (t := e.1.succ) (r := rnext) hrest' w hwTail with hsink | hstage
            · exact Or.inl hsink
            · rcases hstage with ⟨s, r', hwEq, hsle⟩
              have hsucc_le : e.1.castSucc.1 + 1 ≤ s.1 := by
                simpa using hsle
              exact Or.inr ⟨s, r', hwEq, by omega⟩
        | inr e =>
            cases htail
            have hpnil := exercise_6_4_walk_from_sink_nil a b c p hrest
            subst hpnil
            -- After a terminal arc, the only remaining visited vertex is the sink itself.
            left
            simpa [ShortestPathLinearProgram.walkVerticesFrom, exercise_6_4_sink_vertex] using hwTail

/-- Helper for Exercise 6.4: every directed walk from a stage vertex to the sink is automatically
vertex-simple because stages strictly increase until the sink is reached. -/
theorem exercise_6_4_walkVerticesFrom_stage_nodup
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (t : Fin (n + 1))
    (r : exercise_6_4_state_space_at a b t)
    (p : List (exercise_6_4_arc a b))
    (hwalk :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (some ⟨t, r⟩) (exercise_6_4_sink_vertex a b) p) :
    ((exercise_6_4_shortest_path_problem a b c).walkVerticesFrom (some ⟨t, r⟩) p).Nodup := by
  induction p generalizing t r with
  | nil =>
      -- The empty walk visits exactly one vertex.
      simp [ShortestPathLinearProgram.walkVerticesFrom]
  | cons e p ih =>
      rcases hwalk with ⟨htail, hrest⟩
      rw [ShortestPathLinearProgram.walkVerticesFrom]
      refine List.nodup_cons.mpr ?_
      constructor
      · intro hmem
        cases e with
        | inl e =>
            cases htail
            let rnext : exercise_6_4_state_space_at a b e.1.succ :=
              ⟨exercise_6_4_step_residue a e.1 e.2.1 e.2.2,
                exercise_6_4_step_residue_mem_state_space a b e.1 e.2.1 e.2.2⟩
            have hrest' :
                (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
                  (some ⟨e.1.succ, rnext⟩) (exercise_6_4_sink_vertex a b) p := by
              simpa [exercise_6_4_shortest_path_problem, exercise_6_4_arc_head,
                exercise_6_4_step_target, rnext] using hrest
            have hbound :=
              exercise_6_4_walkVerticesFrom_stage_lower_bound a b c e.1.succ rnext p hrest'
                (some ⟨e.1.castSucc, e.2.1⟩) hmem
            rcases hbound with hsink | ⟨s, r', hwEq, hsle⟩
            · cases hsink
            · cases hwEq
              have hnot : ¬ e.1.succ.1 ≤ e.1.castSucc.1 := by
                simpa using Nat.not_succ_le_self e.1.1
              exact hnot hsle
        | inr e =>
            cases htail
            have hpnil := exercise_6_4_walk_from_sink_nil a b c p hrest
            subst hpnil
            have hsink :
                some ⟨Fin.last n, e.1⟩ = exercise_6_4_arc_head a b (Sum.inr e) := by
              simpa [ShortestPathLinearProgram.walkVerticesFrom] using hmem
            simp [exercise_6_4_arc_head, exercise_6_4_sink_vertex] at hsink
      · cases e with
        | inl e =>
            cases htail
            let rnext : exercise_6_4_state_space_at a b e.1.succ :=
              ⟨exercise_6_4_step_residue a e.1 e.2.1 e.2.2,
                exercise_6_4_step_residue_mem_state_space a b e.1 e.2.1 e.2.2⟩
            have hrest' :
                (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
                  (some ⟨e.1.succ, rnext⟩) (exercise_6_4_sink_vertex a b) p := by
              simpa [exercise_6_4_shortest_path_problem, exercise_6_4_arc_head,
                exercise_6_4_step_target, rnext] using hrest
            exact ih (t := e.1.succ) (r := rnext) hrest'
        | inr e =>
            cases htail
            have hpnil := exercise_6_4_walk_from_sink_nil a b c p hrest
            subst hpnil
            simp [ShortestPathLinearProgram.walkVerticesFrom]

/-- Helper for Exercise 6.4: starting from any canonical stage vertex of a feasible bounded
assignment, there is a directed suffix walk to the sink whose length is the remaining suffix
objective. -/
theorem exercise_6_4_forward_walk_from_stage
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x)
    (t : Fin (n + 1)) :
    ∃ p : List (exercise_6_4_arc a b),
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
          (exercise_6_4_stage_vertex a b t x) (exercise_6_4_sink_vertex a b) p ∧
        (exercise_6_4_shortest_path_problem a b c).pathLength p =
          exercise_6_4_stage_objective (a := a) (b := b) c t x := by
  induction t using Fin.reverseInduction with
  | last =>
      refine ⟨[exercise_6_4_terminal_arc a b x hx], ?_, ?_⟩
      · -- At the final stage, the canonical terminal arc reaches the sink in one step.
        refine ⟨exercise_6_4_terminal_arc_tail a b x hx, ?_⟩
        simpa [ShortestPathLinearProgram.IsDirectedWalkFromTo,
          exercise_6_4_terminal_arc_head]
      · -- The terminal arc has zero length, matching the empty suffix objective.
        simp [ShortestPathLinearProgram.pathLength, exercise_6_4_terminal_arc_length,
          exercise_6_4_stage_objective_last]
  | cast j ih =>
      rcases ih with ⟨p, hwalk, hlen⟩
      refine ⟨exercise_6_4_step_arc a b x j :: p, ?_, ?_⟩
      · -- Prefix the recursive suffix walk by the canonical stage-`j` step arc.
        refine ⟨exercise_6_4_step_arc_tail a b x j, ?_⟩
        simpa [exercise_6_4_step_arc_head a b x j] using hwalk
      · -- The prefixed path length is the current arc cost plus the remaining suffix objective.
        calc
          (exercise_6_4_shortest_path_problem a b c).pathLength (exercise_6_4_step_arc a b x j :: p) =
              exercise_6_4_arc_length a b c (exercise_6_4_step_arc a b x j) +
                (exercise_6_4_shortest_path_problem a b c).pathLength p := by
            simp [ShortestPathLinearProgram.pathLength]
          _ =
              (c j : ℝ) * ((x j : ℕ) : ℝ) +
                exercise_6_4_stage_objective (a := a) (b := b) c j.succ x := by
            rw [exercise_6_4_step_arc_length, hlen]
          _ = exercise_6_4_stage_objective (a := a) (b := b) c j.castSucc x := by
            simpa [exercise_6_4_stage_objective_castSucc]

/-- Helper for Exercise 6.4: any directed walk from a canonical stage vertex to the sink decodes
to a bounded feasible assignment whose remaining suffix objective equals the walk length. -/
theorem exercise_6_4_reverse_walk_from_stage
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (t : Fin (n + 1))
    (r : exercise_6_4_state_space_at a b t)
    (p : List (exercise_6_4_arc a b))
    (x₀ : exercise_6_4_bounded_assignment a b)
    (hvertex : exercise_6_4_stage_vertex a b t x₀ = some ⟨t, r⟩)
    (hwalk :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (some ⟨t, r⟩) (exercise_6_4_sink_vertex a b) p) :
    ∃ x : exercise_6_4_bounded_assignment a b,
      (∀ k : Fin n, k.1 < t.1 → x k = x₀ k) ∧
        exercise_6_4_is_bounded_feasible_solution a b x ∧
          exercise_6_4_stage_vertex a b t x = some ⟨t, r⟩ ∧
            (exercise_6_4_shortest_path_problem a b c).pathLength p =
              exercise_6_4_stage_objective (a := a) (b := b) c t x := by
  induction p generalizing t r x₀ with
  | nil =>
      -- A canonical stage vertex is never the sink, so the empty walk case is impossible.
      simp [ShortestPathLinearProgram.IsDirectedWalkFromTo, exercise_6_4_sink_vertex] at hwalk
  | cons e p ih =>
      rcases hwalk with ⟨htail, hrest⟩
      cases e with
      | inl e =>
          cases htail
          let x₁ : exercise_6_4_bounded_assignment a b := Function.update x₀ e.1 e.2.2
          let r₁ : exercise_6_4_state_space_at a b e.1.succ :=
            ⟨exercise_6_4_step_residue a e.1 e.2.1 e.2.2,
              exercise_6_4_step_residue_mem_state_space a b e.1 e.2.1 e.2.2⟩
          have hprefixResidue :
              exercise_6_4_partial_residue a e.1.castSucc (fun k ↦ (x₀ k : ℕ)) =
                (e.2.1 : Fin m → ℚ) := by
            -- The carried witness `x₀` realizes the stage state attached to the first arc.
            have hstate :
                (⟨exercise_6_4_partial_residue a e.1.castSucc (fun k ↦ (x₀ k : ℕ)),
                  exercise_6_4_partial_residue_mem_state_space_of_bounded a b e.1.castSucc x₀⟩ :
                    exercise_6_4_state_space_at a b e.1.castSucc) = e.2.1 := by
              simpa [exercise_6_4_stage_vertex] using hvertex
            exact congrArg
              (fun z : exercise_6_4_state_space_at a b e.1.castSucc => (z : Fin m → ℚ)) hstate
          have hvertex₁ :
              exercise_6_4_stage_vertex a b e.1.succ x₁ = some ⟨e.1.succ, r₁⟩ := by
            -- Route correction: rewrite the head state through the carried witness before recursing.
            simpa [x₁, r₁, exercise_6_4_step_target, hprefixResidue] using
              exercise_6_4_stage_vertex_succ_update a b x₀ e.1 e.2.2
          have hrest' :
              (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
                (some ⟨e.1.succ, r₁⟩) (exercise_6_4_sink_vertex a b) p := by
            simpa [exercise_6_4_arc_head, exercise_6_4_step_target, r₁] using hrest
          rcases ih (t := e.1.succ) (r := r₁) (x₀ := x₁) hvertex₁ hrest' with
            ⟨x, hprefix, hfeas, hstage, hlen⟩
          refine ⟨x, ?_, hfeas, ?_, ?_⟩
          · -- Earlier coordinates stay fixed because the first update only touches index `e.1`.
            intro k hk
            have hk' : k.1 < e.1.succ.1 := by
              exact lt_trans hk (Nat.lt_succ_self _)
            have hk_ne : k ≠ e.1 := ne_of_lt hk
            calc
              x k = x₁ k := hprefix k hk'
              _ = x₀ k := by
                simp [x₁, hk_ne]
          · -- Prefix agreement transfers the canonical stage-`e.1.castSucc` vertex back to `x`.
            calc
              exercise_6_4_stage_vertex a b e.1.castSucc x =
                  exercise_6_4_stage_vertex a b e.1.castSucc x₀ := by
                exact exercise_6_4_stage_vertex_eq_of_eqOn_prefix a b e.1.castSucc x x₀
                  (fun k hk ↦ by
                    have hk' : k.1 < e.1.succ.1 := by
                      exact lt_trans hk (Nat.lt_succ_self _)
                    have hk_ne : k ≠ e.1 := ne_of_lt hk
                    calc
                      x k = x₁ k := hprefix k hk'
                      _ = x₀ k := by
                        simp [x₁, hk_ne])
              _ = some ⟨e.1.castSucc, e.2.1⟩ := hvertex
          · -- The first arc contributes coordinate `e.1`, and the recursive tail is the suffix.
            have hxj : x e.1 = e.2.2 := by
              have hjlt : e.1.1 < e.1.succ.1 := by simpa
              calc
                x e.1 = x₁ e.1 := hprefix e.1 hjlt
                _ = e.2.2 := by simp [x₁]
            calc
              (exercise_6_4_shortest_path_problem a b c).pathLength (Sum.inl e :: p) =
                  exercise_6_4_arc_length a b c (Sum.inl e) +
                    (exercise_6_4_shortest_path_problem a b c).pathLength p := by
                simp [ShortestPathLinearProgram.pathLength]
              _ =
                  (c e.1 : ℝ) * ((e.2.2 : ℕ) : ℝ) +
                    exercise_6_4_stage_objective (a := a) (b := b) c e.1.succ x := by
                rw [hlen]
                rfl
              _ =
                  (c e.1 : ℝ) * ((x e.1 : ℕ) : ℝ) +
                    exercise_6_4_stage_objective (a := a) (b := b) c e.1.succ x := by
                rw [hxj]
              _ = exercise_6_4_stage_objective (a := a) (b := b) c e.1.castSucc x := by
                symm
                simpa [exercise_6_4_stage_objective_castSucc]
      | inr e =>
          cases htail
          have hpnil := exercise_6_4_walk_from_sink_nil a b c p hrest
          subst hpnil
          refine ⟨x₀, ?_, ?_, hvertex, ?_⟩
          · -- No earlier coordinate changes occur in the terminal branch.
            intro k hk
            rfl
          · -- Terminal-state membership closes feasibility at the final stage.
            exact exercise_6_4_feasible_of_terminal_stage_vertex a b x₀ e.1 hvertex e.2
          · -- A terminal arc has zero length, matching the final-stage suffix objective.
            simp [ShortestPathLinearProgram.pathLength, exercise_6_4_arc_length,
              exercise_6_4_stage_objective_last]

/-- Part (2) of Exercise 6.4. Every bounded feasible representative assignment
yields an `s,t`-path of the same length as its objective value in the staged
shortest-path formulation `exercise_6_4_shortest_path_problem a b c`. -/
theorem exercise_6_4_shortest_path_formulation_forward
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (x : exercise_6_4_bounded_assignment a b)
    (hx : exercise_6_4_is_bounded_feasible_solution a b x) :
    ∃ p : List (exercise_6_4_arc a b),
      (exercise_6_4_shortest_path_problem a b c).IsStPath p ∧
        (exercise_6_4_shortest_path_problem a b c).pathLength p =
          exercise_6_4_bounded_objective a b c x :=
  by
  let r0 : exercise_6_4_state_space_at a b 0 :=
    ⟨(fun _ : Fin m ↦ (0 : ℚ)), exercise_6_4_zero_residue_mem_state_space a b⟩
  rcases exercise_6_4_forward_walk_from_stage a b c x hx 0 with ⟨p, hwalk, hlen⟩
  have hsource0 : exercise_6_4_stage_vertex a b 0 x = some ⟨0, r0⟩ := by
    simpa [r0, exercise_6_4_source_vertex] using
      (exercise_6_4_source_vertex_eq_stage_vertex a b x).symm
  have hwalk0 :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (some ⟨0, r0⟩) (exercise_6_4_sink_vertex a b) p := by
    simpa [hsource0] using hwalk
  have hnodup :
      ((exercise_6_4_shortest_path_problem a b c).walkVerticesFrom (some ⟨0, r0⟩) p).Nodup :=
    exercise_6_4_walkVerticesFrom_stage_nodup a b c 0 r0 p hwalk0
  refine ⟨p, ?_, ?_⟩
  · -- The staged walk from the source is an `s,t`-path because the visited vertices are nodup.
    change (exercise_6_4_shortest_path_problem a b c).IsStWalk p ∧
      ((exercise_6_4_shortest_path_problem a b c).walkVerticesFrom
        ((exercise_6_4_shortest_path_problem a b c).s) p).Nodup
    constructor
    · simpa [ShortestPathLinearProgram.IsStWalk, exercise_6_4_shortest_path_problem_s,
        exercise_6_4_shortest_path_problem_t, exercise_6_4_source_vertex, r0] using hwalk0
    · simpa [exercise_6_4_shortest_path_problem_s, exercise_6_4_source_vertex, r0] using hnodup
  · -- The source-stage suffix objective is the full bounded objective.
    simpa [exercise_6_4_stage_objective_zero] using hlen

/-- Exercise 6.4 (3). Every `s,t`-path in the staged shortest-path formulation
`exercise_6_4_shortest_path_problem a b c` yields a bounded feasible representative assignment
with the same objective value. -/
theorem exercise_6_4_shortest_path_formulation_reverse
    (a : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (c : Fin n → ℚ)
    (p : List (exercise_6_4_arc a b))
    (hp : (exercise_6_4_shortest_path_problem a b c).IsStPath p) :
    ∃ x : exercise_6_4_bounded_assignment a b,
      exercise_6_4_is_bounded_feasible_solution a b x ∧
        exercise_6_4_bounded_objective a b c x =
          (exercise_6_4_shortest_path_problem a b c).pathLength p :=
  by
  let x₀ : exercise_6_4_bounded_assignment a b := fun _ ↦ ⟨0, exercise_6_4_modulus_pos a b⟩
  let r₀ : exercise_6_4_state_space_at a b 0 :=
    ⟨(fun _ : Fin m ↦ (0 : ℚ)), exercise_6_4_zero_residue_mem_state_space a b⟩
  have hvertex₀ : exercise_6_4_stage_vertex a b 0 x₀ = some ⟨0, r₀⟩ := by
    -- The all-zero bounded assignment realizes the canonical source vertex.
    simpa [x₀, r₀, exercise_6_4_source_vertex] using
      (exercise_6_4_source_vertex_eq_stage_vertex a b x₀).symm
  have hwalk :
      (exercise_6_4_shortest_path_problem a b c).IsDirectedWalkFromTo
        (some ⟨0, r₀⟩) (exercise_6_4_sink_vertex a b) p := by
    -- Read the `s,t`-path witness as a directed walk from the explicit source stage vertex.
    simpa [ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk,
      exercise_6_4_shortest_path_problem_s, exercise_6_4_shortest_path_problem_t,
      exercise_6_4_source_vertex, r₀] using hp.1
  rcases exercise_6_4_reverse_walk_from_stage a b c 0 r₀ p x₀ hvertex₀ hwalk with
    ⟨x, -, hfeas, -, hlen⟩
  refine ⟨x, hfeas, ?_⟩
  -- Stage `0` sees the full objective, so the decoded walk length is the bounded objective value.
  simpa [exercise_6_4_stage_objective_zero] using hlen.symm

end Exercise64
