import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1

section Theorem640

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "IntAssignment" => Rq →₀ ℤ

/-- The value of the group-relaxation validity inequality associated to `π` at the finitely
supported integer assignment `x`. -/
def gomory_group_validity_value
    (π : Rq → ℝ)
    (x : IntAssignment) : ℝ :=
  x.sum (fun r n ↦ (n : ℝ) * π r)

/-- Expanding `gomory_group_validity_value π x` gives the sum `∑_r π(r) x(r)` over the finite
support of `x`. -/
@[simp] theorem gomory_group_validity_value_eq
    (π : Rq → ℝ)
    (x : IntAssignment) :
    gomory_group_validity_value π x =
      x.sum (fun r n ↦ (n : ℝ) * π r) :=
  rfl

/-- The equality set `E(π)` consists of the points of `G_f` that are tight for the valid
inequality defined by `π`. -/
def gomory_group_equality_set
    (f : Rq)
    (π : Rq → ℝ) : Set IntAssignment :=
  {x |
    x ∈ pure_integer_feasible_set f ∧
      gomory_group_validity_value π x = 1}

/-- Membership in `gomory_group_equality_set f π` means belonging to `G_f` and satisfying the
tightness equation `∑_r π(r) x(r) = 1`. -/
theorem mem_gomory_group_equality_set_iff
    {f : Rq} {π : Rq → ℝ} {x : IntAssignment} :
    x ∈ gomory_group_equality_set f π ↔
      x ∈ pure_integer_feasible_set f ∧
        gomory_group_validity_value π x = 1 :=
  Iff.rfl

/-- The solution set of the equalities `E(π)`: a coefficient function `π'` is a solution when it
is equal to `1` on every tight point of `π`. -/
def solves_gomory_group_equality_system
    (f : Rq)
    (π π' : Rq → ℝ) : Prop :=
  ∀ ⦃x : IntAssignment⦄, x ∈ gomory_group_equality_set f π →
    gomory_group_validity_value π' x = 1

/-- A solution of the equality system `E(π)` evaluates to `1` on each point of `E(π)`. -/
theorem solves_gomory_group_equality_system.apply
    {f : Rq} {π π' : Rq → ℝ}
    (hπ' : solves_gomory_group_equality_system f π π')
    {x : IntAssignment}
    (hx : x ∈ gomory_group_equality_set f π) :
    gomory_group_validity_value π' x = 1 :=
  hπ' hx

/-- The solution set of the equalities `E(π)`: a coefficient function `π'` is a solution when it
is equal to `1` on every tight point of `π`. -/
def gomory_group_equality_solution_set
    (f : Rq)
    (π : Rq → ℝ) : Set (Rq → ℝ) :=
  {π' | solves_gomory_group_equality_system f π π'}

/-- Membership in `gomory_group_equality_solution_set f π` is exactly the condition of solving all
equalities from `E(π)`. -/
theorem mem_gomory_group_equality_solution_set_iff
    {f : Rq} {π π' : Rq → ℝ} :
    π' ∈ gomory_group_equality_solution_set f π ↔
      solves_gomory_group_equality_system f π π' :=
  Iff.rfl

/-- The equality set `E(π)` determines `π` among valid functions when every valid `π'` whose
equality set contains `E(π)` coincides with `π`. -/
def gomory_group_equality_set_determines_valid_function
    (f : Rq)
    (π : Rq → ℝ) : Prop :=
  ∀ {π' : Rq → ℝ},
    pure_integer_valid_function f π' →
    gomory_group_equality_set f π ⊆ gomory_group_equality_set f π' →
    π' = π

/-- A determining equality set identifies every valid function whose equality set contains it. -/
theorem gomory_group_equality_set_determines_valid_function.eq_of_subset_equality_set
    {f : Rq} {π π' : Rq → ℝ}
    (hπ : gomory_group_equality_set_determines_valid_function f π)
    (hπ' : pure_integer_valid_function f π')
    (hsubset : gomory_group_equality_set f π ⊆ gomory_group_equality_set f π') :
    π' = π :=
  hπ hπ' hsubset

/-- The equality system `E(π)` has `π` as its unique solution. -/
def gomory_group_equality_solution_set_has_unique_solution
    (f : Rq)
    (π : Rq → ℝ) : Prop :=
  ∀ {π' : Rq → ℝ},
    π' ∈ gomory_group_equality_solution_set f π →
    π' = π

/-- A unique solution of `E(π)` must coincide with `π`. -/
theorem gomory_group_equality_solution_set_has_unique_solution.eq
    {f : Rq} {π π' : Rq → ℝ}
    (hπ : gomory_group_equality_solution_set_has_unique_solution f π)
    (hπ' : π' ∈ gomory_group_equality_solution_set f π) :
    π' = π :=
  hπ hπ'

/-- A function `π` defines a facet of `G_f` when it is valid and every valid function whose
equality set contains `E(π)` coincides with `π`. -/
class defines_facet_of_gomory_group_relaxation
    (f : Rq)
    (π : Rq → ℝ) : Prop extends pure_integer_valid_function f π where
  /-- Every valid function whose equality set contains `E(π)` is equal to `π`. -/
  eq_of_subset_equality_set {π' : Rq → ℝ}
      (hπ' : pure_integer_valid_function f π')
      (hsubset : gomory_group_equality_set f π ⊆ gomory_group_equality_set f π') :
      π' = π

/-- `defines_facet_of_gomory_group_relaxation f π` unfolds to validity of `π` together with
uniqueness among valid functions having all equalities of `π`. -/
theorem defines_facet_of_gomory_group_relaxation_iff
    {f : Rq} {π : Rq → ℝ} :
    defines_facet_of_gomory_group_relaxation f π ↔
      pure_integer_valid_function f π ∧
        gomory_group_equality_set_determines_valid_function f π := by
  constructor
  · intro hπ
    refine ⟨{ nonneg := hπ.nonneg, one_le_sum := hπ.one_le_sum }, ?_⟩
    intro π' hπ' hsubset
    exact hπ.eq_of_subset_equality_set hπ' hsubset
  · rintro ⟨hπ, hfacet⟩
    refine
      { nonneg := hπ.nonneg
        one_le_sum := hπ.one_le_sum
        eq_of_subset_equality_set := ?_ }
    intro π' hπ' hsubset
    exact hfacet hπ' hsubset

/-- Every function is a solution of its own equality set. -/
theorem self_mem_gomory_group_equality_solution_set
    {f : Rq} {π : Rq → ℝ} :
    π ∈ gomory_group_equality_solution_set f π := by
  intro x hx
  exact hx.2

/-- If a valid function is the unique solution of its equality set, then it defines a facet
of `G_f`. -/
theorem valid_gomory_group_function_defines_facet_of_unique_equality_solution
    {f : Rq}
    {π : Rq → ℝ}
    (hπ : pure_integer_valid_function f π)
    (hE : gomory_group_equality_solution_set_has_unique_solution f π) :
    defines_facet_of_gomory_group_relaxation f π := by
  rw [defines_facet_of_gomory_group_relaxation_iff]
  refine ⟨hπ, ?_⟩
  intro π' hπ' hsubset
  apply hE.eq
  rw [mem_gomory_group_equality_solution_set_iff]
  intro x hx
  exact (hsubset hx).2

/-- Theorem 6.40 (Facet Theorem). Let `π` be a minimal valid function. If the set of equalities
`E(π)` has no other solution than `π` itself, then `π` defines a facet of `G_f`. -/
theorem minimal_valid_gomory_group_function_defines_facet_of_unique_equality_solution
    {f : Rq}
    {π : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hE : gomory_group_equality_solution_set_has_unique_solution f π) :
    defines_facet_of_gomory_group_relaxation f π :=
  valid_gomory_group_function_defines_facet_of_unique_equality_solution
    { nonneg := hπ.nonneg, one_le_sum := hπ.one_le_sum } hE

end Theorem640
