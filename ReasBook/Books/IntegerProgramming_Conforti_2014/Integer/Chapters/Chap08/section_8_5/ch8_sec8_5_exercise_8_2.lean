import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1

open scoped Matrix

section Exercise82

variable {m₁ m₂ n p : ℕ}

/-- The index set of the first `p` coordinates of `Fin n`. -/
abbrev mixed_integer_prefix_indices (hp : p ≤ n) : Finset (Fin n) :=
  Finset.univ.image (Fin.castLEEmb hp)

/-- Integrality on `mixed_integer_prefix_indices hp` is exactly integrality of the first `p`
coordinates. -/
theorem integral_on_mixed_integer_prefix_indices_iff
    (hp : p ≤ n)
    (x : Fin n → ℝ) :
    (∀ j ∈ mixed_integer_prefix_indices hp, ∃ z : ℤ, x j = (z : ℝ)) ↔
      ∀ j : Fin p, ∃ z : ℤ, x (Fin.castLE hp j) = (z : ℝ) := by
  constructor
  · intro hx j
    exact hx (Fin.castLE hp j) (by
      simp [mixed_integer_prefix_indices])
  · intro hx j hj
    rcases Finset.mem_image.mp hj with ⟨k, -, hk⟩
    simpa [mixed_integer_prefix_indices] using hk ▸ hx k

/-- The easy block `Q = {x ∈ ℝ^n_+ | A₂ x ≤ b², x₁, ..., x_p ∈ ℤ}` obtained by keeping the nice
constraints, the nonnegativity constraints, and the explicit integrality conditions on the first
`p` variables. -/
def mixed_integer_equality_lagrangian_base_set
    (hp : p ≤ n)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set (Fin n → ℝ) :=
  mixed_integer_feasible_set A₂ b₂ (mixed_integer_prefix_indices hp) ∩
    {x : Fin n → ℝ | 0 ≤ x}

/-- Membership in `mixed_integer_equality_lagrangian_base_set hp A₂ b₂` is exactly the conjunction
of the nice constraints `A₂ x ≤ b²`, integrality of the first `p` coordinates, and nonnegativity
of all coordinates. -/
theorem mem_mixed_integer_equality_lagrangian_base_set_iff
    (hp : p ≤ n)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (x : Fin n → ℝ) :
    x ∈ mixed_integer_equality_lagrangian_base_set hp A₂ b₂ ↔
      A₂ *ᵥ x ≤ b₂ ∧ (∀ j : Fin p, ∃ z : ℤ, x (Fin.castLE hp j) = (z : ℝ)) ∧ 0 ≤ x := by
  constructor
  · rintro ⟨hx_mixed, hx_nonneg⟩
    rcases (mem_mixed_integer_feasible_set_iff A₂ b₂ (mixed_integer_prefix_indices hp) x).1 hx_mixed
      with ⟨hA₂, hInt⟩
    exact ⟨hA₂, (integral_on_mixed_integer_prefix_indices_iff hp x).1 hInt, hx_nonneg⟩
  · rintro ⟨hA₂, hInt, hx_nonneg⟩
    refine ⟨?_, hx_nonneg⟩
    exact (mem_mixed_integer_feasible_set_iff A₂ b₂ (mixed_integer_prefix_indices hp) x).2
      ⟨hA₂, (integral_on_mixed_integer_prefix_indices_iff hp x).2 hInt⟩

/-- The original feasible set
`{x ∈ ℝ^n_+ | A₁ x = b¹, A₂ x ≤ b², x₁, ..., x_p ∈ ℤ}` from Exercise 8.2. -/
def mixed_integer_equality_feasible_set
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set (Fin n → ℝ) :=
  standard_equality_form A₁ b₁ ∩
    mixed_integer_feasible_set A₂ b₂ (mixed_integer_prefix_indices hp)

/-- Membership in `mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂` is exactly the conjunction
of the equality constraints `A₁ x = b¹`, the nice inequalities `A₂ x ≤ b²`, integrality of the
first `p` coordinates, and nonnegativity. -/
theorem mem_mixed_integer_equality_feasible_set_iff
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (x : Fin n → ℝ) :
    x ∈ mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂ ↔
      A₁ *ᵥ x = b₁ ∧
        A₂ *ᵥ x ≤ b₂ ∧
          (∀ j : Fin p, ∃ z : ℤ, x (Fin.castLE hp j) = (z : ℝ)) ∧
            0 ≤ x := by
  constructor
  · rintro ⟨hx_eq, hx_mixed⟩
    rcases (mem_standard_equality_form_iff).1 hx_eq with ⟨hEq, hx_nonneg⟩
    rcases (mem_mixed_integer_feasible_set_iff A₂ b₂ (mixed_integer_prefix_indices hp) x).1 hx_mixed
      with ⟨hA₂, hInt⟩
    exact ⟨hEq, hA₂, (integral_on_mixed_integer_prefix_indices_iff hp x).1 hInt, hx_nonneg⟩
  · rintro ⟨hEq, hA₂, hInt, hx_nonneg⟩
    refine ⟨?_, ?_⟩
    · exact (mem_standard_equality_form_iff).2 ⟨hEq, hx_nonneg⟩
    · exact (mem_mixed_integer_feasible_set_iff A₂ b₂ (mixed_integer_prefix_indices hp) x).2
        ⟨hA₂, (integral_on_mixed_integer_prefix_indices_iff hp x).2 hInt⟩

/-- The source integer-program value `z_I`, expressed on the canonical Chapter 8 `EReal` value
layer as the Section 8.1 `integer_program_value` specialization with no extra complicating
inequalities beyond the Exercise 8.2 feasible set. -/
noncomputable abbrev mixed_integer_equality_integer_program_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) : EReal :=
  integer_program_value (0 : Matrix (Fin 0) (Fin n) ℝ) (0 : Fin 0 → ℝ) c
    (mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂)

/-- `mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c` is exactly the canonical
Section 8.1 `integer_program_value` applied to the Exercise 8.2 feasible set. -/
theorem mixed_integer_equality_integer_program_value_eq_integer_program_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c =
      integer_program_value (0 : Matrix (Fin 0) (Fin n) ℝ) (0 : Fin 0 → ℝ) c
        (mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂) :=
  rfl

/-- `mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c` unfolds to the supremum of
the objective over `mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂`. -/
theorem mixed_integer_equality_integer_program_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c =
      sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂) := by
  simp [mixed_integer_equality_integer_program_value, integer_program_value,
    lagrangian_integer_feasible_set]

/-- The Lagrangian relaxation obtained by dualizing the complicating equalities `A₁ x = b¹` while
keeping the nice mixed-integer set `Q`: it maximizes
`c x + λ (b¹ - A₁ x)` over `Q`, with unrestricted multiplier vector `λ`. -/
noncomputable abbrev mixed_integer_equality_lagrangian_relaxation_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ) : EReal :=
  lagrangian_relaxation_value A₁ b₁ c (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) lam

/-- `mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c λ` is exactly the
canonical Section 8.1 `lagrangian_relaxation_value` applied to the Exercise 8.2 mixed-integer
base set. -/
theorem mixed_integer_equality_lagrangian_relaxation_value_eq_lagrangian_relaxation_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ) :
    mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      lagrangian_relaxation_value A₁ b₁ c
        (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) lam :=
  rfl

/-- `mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c λ` unfolds to the
supremum of the equality-penalized objective over
`mixed_integer_equality_lagrangian_base_set hp A₂ b₂`. -/
theorem mixed_integer_equality_lagrangian_relaxation_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ) :
    mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      sSup
        ((fun x : Fin n → ℝ ↦
            ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal)) ''
          mixed_integer_equality_lagrangian_base_set hp A₂ b₂) :=
  lagrangian_relaxation_value_eq_sSup A₁ b₁ c
    (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) lam

/-- Helper for Exercise 8.2: every feasible point of the equality-constrained mixed-integer
problem belongs to the Lagrangian base set obtained by dropping the complicating equalities. -/
private lemma mixed_integer_equality_feasible_set_subset_lagrangian_base_set
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) :
    mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂ ⊆
      mixed_integer_equality_lagrangian_base_set hp A₂ b₂ := by
  intro x hx
  -- Forget the equality block and keep the nice constraints, integrality, and nonnegativity.
  rcases (mem_mixed_integer_equality_feasible_set_iff hp A₁ b₁ A₂ b₂ x).1 hx with
    ⟨-, hA₂, hInt, hx_nonneg⟩
  exact (mem_mixed_integer_equality_lagrangian_base_set_iff hp A₂ b₂ x).2
    ⟨hA₂, hInt, hx_nonneg⟩

/-- Helper for Exercise 8.2: on the original feasible set, the equality slack `b₁ - A₁ *ᵥ x`
vanishes coordinatewise. -/
private lemma mixed_integer_equality_slack_eq_zero_of_mem_feasible
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂) :
    b₁ - A₁ *ᵥ x = 0 := by
  -- Extract the exact equality block and rewrite the slack function one coordinate at a time.
  rcases (mem_mixed_integer_equality_feasible_set_iff hp A₁ b₁ A₂ b₂ x).1 hx with
    ⟨hEq, -, -, -⟩
  ext i
  have hEqi : (A₁ *ᵥ x) i = b₁ i :=
    congrArg (fun y => y i) hEq
  simpa using sub_eq_zero.mpr hEqi.symm

/-- Helper for Exercise 8.2: each original feasible point contributes an objective value bounded
above by the equality-constraint Lagrangian relaxation value. -/
private lemma objective_le_mixed_integer_equality_lagrangian_relaxation_value_of_mem_feasible
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ mixed_integer_equality_feasible_set hp A₁ b₁ A₂ b₂) :
    ((c ⬝ᵥ x : ℝ) : EReal) ≤
      mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
  -- Insert the feasible point into the relaxation supremum over the base set.
  have hxBase :
      x ∈ mixed_integer_equality_lagrangian_base_set hp A₂ b₂ :=
    mixed_integer_equality_feasible_set_subset_lagrangian_base_set hp A₁ b₁ A₂ b₂ hx
  have hRelax :=
    lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c
      (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) lam hxBase
  -- The equality block forces zero slack, so the Lagrangian penalty disappears.
  have hslack : b₁ - A₁ *ᵥ x = 0 :=
    mixed_integer_equality_slack_eq_zero_of_mem_feasible hp A₁ b₁ A₂ b₂ hx
  simpa [hslack] using hRelax

/-- Exercise 8.2. For every multiplier vector `λ ∈ ℝ^{m₁}`, the equality-constraint Lagrangian
relaxation obtained from the mixed-integer base set
`{x ∈ ℝ^n_+ | A₂ x ≤ b², x₁, ..., x_p ∈ ℤ}` bounds the original value `z_I` from above. This is
the analogue of Proposition 8.1 for complicating equations, where no sign restriction on `λ` is
needed because the penalty term vanishes on every feasible point. -/
theorem mixed_integer_equality_integer_program_value_le_lagrangian_relaxation_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ) :
    mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c ≤
      mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam := by
  -- Rewrite the primal value as the supremum over feasible-point objective values.
  rw [mixed_integer_equality_integer_program_value_eq_sSup]
  -- Bound each feasible witness by the pointwise Lagrangian estimate with zero equality slack.
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact
    objective_le_mixed_integer_equality_lagrangian_relaxation_value_of_mem_feasible
      hp A₁ b₁ A₂ b₂ c lam hx

/-- The reversed-inequality wrapper for Exercise 8.2, packaged in `≥` form. -/
theorem mixed_integer_equality_lagrangian_relaxation_value_ge_integer_program_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ) :
    mixed_integer_equality_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam ≥
      mixed_integer_equality_integer_program_value hp A₁ b₁ A₂ b₂ c :=
  mixed_integer_equality_integer_program_value_le_lagrangian_relaxation_value
    hp A₁ b₁ A₂ b₂ c lam

end Exercise82
