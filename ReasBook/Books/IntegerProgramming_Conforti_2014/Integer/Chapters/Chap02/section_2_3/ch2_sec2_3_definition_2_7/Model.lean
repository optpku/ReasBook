module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Order
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_3.ch2_sec2_3_definition_2_7.Patterns

public section

namespace CuttingStock

variable {m : ℕ}

/-- The finitely supported integer pattern-count families indexed by `patterns W w`. -/
abbrev Assignment (W : ℕ) (w : Fin m → ℕ) : Type :=
  patterns W w →₀ ℕ

/-- A pattern-count family `x` is feasible when, for every item type `i`, the total number cut
across all used patterns is at least the demand `b i`. -/
def feasible
    (W : ℕ) (w b : Fin m → ℕ) (x : Assignment W w) : Prop :=
  ∀ i, b i ≤ x.sum (fun s n ↦ (s : Fin m → ℕ) i * n)

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean
Unfolding characterization of cutting-stock feasibility in terms of the demand-cover inequalities
`b i ≤ ∑ s, s i * x s`. -/
theorem feasible_iff
    {W : ℕ} {w b : Fin m → ℕ} {x : Assignment W w} :
    feasible W w b x ↔ ∀ i, b i ≤ x.sum (fun s n ↦ (s : Fin m → ℕ) i * n) := by
  -- Unfolding `feasible` leaves the displayed demand-cover inequalities unchanged.
  rfl

attribute [simp] feasible_iff

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: pointwise larger
finitely supported coefficients have larger naturally weighted sums. -/
theorem weightedFinsuppSum_mono
    {ι : Type*} (weight : ι → ℕ) {x y : ι →₀ ℕ} (hxy : x ≤ y) :
    x.sum (fun i n ↦ weight i * n) ≤ y.sum (fun i n ↦ weight i * n) := by
  -- Multiplication by each natural weight is monotone and sends a zero coefficient to zero.
  classical
  exact Finsupp.sum_le_sum_index hxy
    (fun i _ ↦ monotone_mul_left_of_nonneg (Nat.zero_le (weight i)))
    (fun i _ ↦ Nat.mul_zero (weight i))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: feasibility is
preserved when every pattern multiplicity is increased. -/
theorem feasible_mono
    {W : ℕ} {w b : Fin m → ℕ} {x y : Assignment W w}
    (hxy : x ≤ y) (hx : feasible W w b x) : feasible W w b y := by
  -- Expose feasibility and compare each weighted demand-cover sum pointwise.
  rw [feasible_iff] at hx ⊢
  intro i
  exact (hx i).trans
    (weightedFinsuppSum_mono (fun s : patterns W w ↦ (s : Fin m → ℕ) i) hxy)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: adding any pattern-count
assignment to a feasible assignment preserves feasibility. -/
theorem feasible_add_right
    {W : ℕ} {w b : Fin m → ℕ} (x y : Assignment W w) (hx : feasible W w b x) :
    feasible W w b (x + y) := by
  -- The original assignment is pointwise bounded by the assignment obtained after adding `y`.
  apply feasible_mono _ hx
  intro s
  exact Nat.le_add_right (x s) (y s)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the zero assignment is
feasible exactly when every demand is zero. -/
@[simp] theorem feasible_zero_iff
    {W : ℕ} {w b : Fin m → ℕ} :
    feasible W w b (0 : Assignment W w) ↔ ∀ i, b i = 0 := by
  -- Unfold feasibility, evaluate each empty weighted sum, and normalize the natural inequality.
  rw [feasible_iff]
  simp only [Finsupp.sum_zero_index, Nat.le_zero]

/-- The feasible set of the pattern-based cutting-stock formulation. -/
def feasibleSet
    (W : ℕ) (w b : Fin m → ℕ) : Set (Assignment W w) :=
  {x | feasible W w b x}

/-- Membership in `feasibleSet W w b` is exactly cutting-stock feasibility. -/
@[simp] theorem mem_feasibleSet_iff
    {W : ℕ} {w b : Fin m → ℕ} {x : Assignment W w} :
    x ∈ feasibleSet W w b ↔ feasible W w b x := by
  -- Membership in the defining set-builder reduces to its feasibility predicate.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the zero assignment
belongs to the feasible set exactly when every demand is zero. -/
@[simp] theorem zero_mem_feasibleSet_iff
    {W : ℕ} {w b : Fin m → ℕ} :
    (0 : Assignment W w) ∈ feasibleSet W w b ↔ ∀ i, b i = 0 := by
  -- Reduce set membership to feasibility and use the established zero-assignment criterion.
  rw [mem_feasibleSet_iff, feasible_zero_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the feasible set is
upward closed under pointwise increases in pattern multiplicities. -/
theorem mem_feasibleSet_of_le
    {W : ℕ} {w b : Fin m → ℕ} {x y : Assignment W w}
    (hx : x ∈ feasibleSet W w b) (hxy : x ≤ y) : y ∈ feasibleSet W w b := by
  -- Translate membership to feasibility and apply its established monotonicity.
  rw [mem_feasibleSet_iff] at hx ⊢
  exact feasible_mono hxy hx

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: membership in the
feasible set is equivalent to satisfying every demand-cover inequality. -/
@[simp] theorem mem_feasibleSet_iff_demand_covered
    {W : ℕ} {w b : Fin m → ℕ} {x : Assignment W w} :
    x ∈ feasibleSet W w b ↔
      ∀ i, b i ≤ x.sum (fun s n ↦ (s : Fin m → ℕ) i * n) := by
  -- Pass from set membership to feasibility, then expose its defining inequalities.
  rw [mem_feasibleSet_iff, feasible_iff]

/-- The pattern-based cutting-stock objective counts the total number of rolls used by the
finitely supported pattern-count family `x`. -/
def objective
    {W : ℕ} {w : Fin m → ℕ} (x : Assignment W w) : ℕ :=
  x.sum (fun _ n ↦ n)

/-- The objective `objective x` is the sum of the pattern multiplicities appearing in `x`. -/
@[simp] theorem objective_eq_sum
    {W : ℕ} {w : Fin m → ℕ} (x : Assignment W w) :
    objective x = x.sum (fun _ n ↦ n) := by
  -- Unfolding `objective` leaves precisely the displayed finitely supported sum.
  rfl

/-- The zero pattern-count family has objective value zero. -/
@[simp] theorem objective_zero
    {W : ℕ} {w : Fin m → ℕ} :
    objective (0 : Assignment W w) = 0 := by
  -- Reduce the objective to the empty finitely supported sum.
  simp only [objective, Finsupp.sum_zero_index]

/-- A singleton assignment uses exactly its recorded number of rolls. -/
@[simp] theorem objective_single
    {W : ℕ} {w : Fin m → ℕ} (s : patterns W w) (n : ℕ) :
    objective (Finsupp.single s n) = n := by
  -- Reduce the objective to the sole nonzero pattern multiplicity.
  simp only [objective, Finsupp.sum_single_index]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the objective is
additive on pattern-count assignments. -/
@[simp] theorem objective_add
    {W : ℕ} {w : Fin m → ℕ} (x y : Assignment W w) :
    objective (x + y) = objective x + objective y := by
  -- View each summand as the identity additive homomorphism and distribute the sum.
  simpa only [objective] using
    (Finsupp.sum_hom_add_index (f := x) (g := y) (fun _ ↦ AddMonoidHom.id ℕ))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: increasing pattern
multiplicities cannot decrease the number of rolls used. -/
theorem objective_mono
    {W : ℕ} {w : Fin m → ℕ} {x y : Assignment W w} (hxy : x ≤ y) :
    objective x ≤ objective y := by
  -- Regard the objective as a weighted sum with every pattern assigned unit weight.
  simpa only [objective, one_mul] using
    (weightedFinsuppSum_mono (fun _ : patterns W w ↦ 1) hxy)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the cutting-stock
objective bundled as an additive monoid homomorphism. -/
def objectiveAddMonoidHom
    {W : ℕ} {w : Fin m → ℕ} : Assignment W w →+ ℕ :=
  -- Package the established zero and addition computations into the canonical additive API.
  { toFun := objective
    map_zero' := objective_zero
    map_add' := objective_add }

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: evaluating the bundled
objective agrees with `objective`. -/
@[simp] theorem objectiveAddMonoidHom_apply
    {W : ℕ} {w : Fin m → ℕ} (x : Assignment W w) :
    objectiveAddMonoidHom x = objective x := by
  -- The bundled homomorphism has `objective` as its underlying function.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the objective
commutes with natural scalar multiplication of assignments. -/
@[simp] theorem objective_nsmul
    {W : ℕ} {w : Fin m → ℕ} (n : ℕ) (x : Assignment W w) :
    objective (n • x) = n * objective x := by
  -- Induct on the number of repeated additions, using the zero and additive computations.
  induction n with
  | zero =>
      simp only [zero_nsmul, objective_zero, zero_mul]
  | succ n inductionHypothesis =>
      rw [succ_nsmul, objective_add, inductionHypothesis, Nat.succ_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_3/ch2_sec2_3_definition_2_7/Model.lean`: the objective
preserves finite sums of pattern-count assignments. -/
@[simp] theorem objective_finset_sum
    {W : ℕ} {w : Fin m → ℕ} {ι : Type*} (s : Finset ι) (f : ι → Assignment W w) :
    objective (s.sum f) = s.sum (fun i ↦ objective (f i)) := by
  -- Apply the generic finite-sum law to the bundled objective homomorphism.
  simpa only [objectiveAddMonoidHom_apply] using
    (map_sum objectiveAddMonoidHom f s)

end CuttingStock

end

#print axioms CuttingStock.feasible_iff
#print axioms CuttingStock.weightedFinsuppSum_mono
#print axioms CuttingStock.feasible_mono
#print axioms CuttingStock.feasible_add_right
#print axioms CuttingStock.feasible_zero_iff
#print axioms CuttingStock.zero_mem_feasibleSet_iff
#print axioms CuttingStock.mem_feasibleSet_of_le
#print axioms CuttingStock.objective_mono
