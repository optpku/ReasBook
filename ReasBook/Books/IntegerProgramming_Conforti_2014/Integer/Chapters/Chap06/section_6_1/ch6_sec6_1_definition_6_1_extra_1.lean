import Mathlib

open scoped BigOperators

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so the declarations below follow the local mixed-integer-set and
-- `convexHull ℝ` precedent directly.

section Definition61Extra1

variable {n p : ℕ}

/-- The nonbasic index set `N` is the complement in `Fin n` of the basic indices `B ⊆ Fin p`,
embedded into the first `p` coordinates of `Fin n`. -/
def corner_nonbasic_indices (hp : p ≤ n) (B : Finset (Fin p)) : Finset (Fin n) :=
  Finset.univ \ B.image (Fin.castLEEmb hp)

/-- Membership in `corner_nonbasic_indices hp B` means not belonging to the embedded basic index
set. -/
@[simp] theorem mem_corner_nonbasic_indices_iff
    (hp : p ≤ n) (B : Finset (Fin p)) (j : Fin n) :
    j ∈ corner_nonbasic_indices hp B ↔ j ∉ B.image (Fin.castLEEmb hp) := by
  simp [corner_nonbasic_indices]

/-- The embedded mixed-integer lattice `ℤ^p × ℝ^(n - p)` inside `ℝ^n`, using the first `p`
coordinates as the integral block. -/
def mixed_integer_prefix_lattice (hp : p ≤ n) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin p, ∃ z : ℤ, x (Fin.castLE hp i) = (z : ℝ)}

/-- Membership in `mixed_integer_prefix_lattice hp` means coordinatewise integrality on the
first `p` coordinates. -/
@[simp] theorem mem_mixed_integer_prefix_lattice_iff
    (hp : p ≤ n) (x : Fin n → ℝ) :
    x ∈ mixed_integer_prefix_lattice hp ↔
      ∀ i : Fin p, ∃ z : ℤ, x (Fin.castLE hp i) = (z : ℝ) := Iff.rfl

/-- The tableau equations
`x_i = \bar b_i - \sum_{j \in N} \bar a_{ij} x_j`
for the basic indices `i ∈ B`. -/
def tableau_equations
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) : Set (Fin n → ℝ) :=
  {x |
    ∀ i ∈ B,
      x (Fin.castLE hp i) =
        (barb i : ℝ) -
          ∑ j ∈ corner_nonbasic_indices hp B, (barA i j : ℝ) * x j}

/-- Membership in `tableau_equations hp B barA barb` is exactly the tableau equation system on
the basic indices. -/
@[simp] theorem mem_tableau_equations_iff
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (x : Fin n → ℝ) :
    x ∈ tableau_equations hp B barA barb ↔
      ∀ i ∈ B,
        x (Fin.castLE hp i) =
          (barb i : ℝ) -
            ∑ j ∈ corner_nonbasic_indices hp B, (barA i j : ℝ) * x j := Iff.rfl

/-- The rewritten mixed-integer tableau system with equations
`x_i = \bar b_i - \sum_{j \in N} \bar a_{ij} x_j` for `i ∈ B`, integrality on the first `p`
coordinates, and nonnegativity on all variables. This is the source feasible set (6.1) expressed
in the tableau form (6.2). -/
def tableau_mixed_integer_set
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) : Set (Fin n → ℝ) :=
  tableau_equations hp B barA barb ∩
    (mixed_integer_prefix_lattice hp ∩ {x | ∀ j : Fin n, 0 ≤ x j})

/-- Membership in `tableau_mixed_integer_set hp B barA barb` is exactly the tableau equations,
integrality on the first `p` coordinates, and nonnegativity on every variable. -/
@[simp] theorem mem_tableau_mixed_integer_set_iff
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (x : Fin n → ℝ) :
    x ∈ tableau_mixed_integer_set hp B barA barb ↔
      (∀ i ∈ B,
        x (Fin.castLE hp i) =
          (barb i : ℝ) -
            ∑ j ∈ corner_nonbasic_indices hp B, (barA i j : ℝ) * x j) ∧
        x ∈ mixed_integer_prefix_lattice hp ∧
        ∀ j : Fin n, 0 ≤ x j := Iff.rfl

/-- Gomory's corner relaxation keeps the tableau equations and the integrality constraints on the
first `p` coordinates, but retains nonnegativity only on the nonbasic variables `j ∈ N`. -/
def gomory_corner_relaxation
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) : Set (Fin n → ℝ) :=
  tableau_equations hp B barA barb ∩
    (mixed_integer_prefix_lattice hp ∩ {x | ∀ j ∈ corner_nonbasic_indices hp B, 0 ≤ x j})

/-- Membership in `gomory_corner_relaxation hp B barA barb` is exactly the tableau equations,
integrality on the first `p` coordinates, and nonnegativity on the nonbasic variables. -/
@[simp] theorem mem_gomory_corner_relaxation_iff
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (x : Fin n → ℝ) :
    x ∈ gomory_corner_relaxation hp B barA barb ↔
      (∀ i ∈ B,
        x (Fin.castLE hp i) =
          (barb i : ℝ) -
            ∑ j ∈ corner_nonbasic_indices hp B, (barA i j : ℝ) * x j) ∧
        x ∈ mixed_integer_prefix_lattice hp ∧
        ∀ j ∈ corner_nonbasic_indices hp B, 0 ≤ x j := Iff.rfl

/-- Definition 6.1-extra-1. After rewriting the mixed-integer system relative to a feasible basis
whose basic variables are all among the first `p` integer coordinates, the corner polyhedron
relative to `B` is the convex hull of the feasible solutions of Gomory's relaxation (6.3). -/
def corner_polyhedron
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) : Set (Fin n → ℝ) :=
  convexHull ℝ (gomory_corner_relaxation hp B barA barb)

/-- `corner_polyhedron hp B barA barb` is, by definition, the convex hull of Gomory's corner
relaxation. -/
theorem corner_polyhedron_eq_convexHull
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) :
    corner_polyhedron hp B barA barb =
      convexHull ℝ (gomory_corner_relaxation hp B barA barb) := rfl

/-- Every feasible point of the original rewritten mixed-integer tableau set belongs to the corner
polyhedron, so any inequality valid for the corner polyhedron is valid for the set (6.1). -/
theorem tableau_mixed_integer_set_subset_corner_polyhedron
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ) :
    tableau_mixed_integer_set hp B barA barb ⊆ corner_polyhedron hp B barA barb := by
  intro x hx
  apply subset_convexHull ℝ (gomory_corner_relaxation hp B barA barb)
  rcases hx with ⟨hx_eq, hx_int, hx_nonneg⟩
  exact ⟨hx_eq, hx_int, fun j _ ↦ hx_nonneg j⟩

end Definition61Extra1
