import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_28

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * source-facing owner kept here: `splitClosure`
-- * core/canonical owners reused here:
--   `polyhedron_le_set`, `split_branch_lower`, `split_branch_upper`, `split_hull`,
--   `split_closure`
-- * companion/view layer kept here:
--   `mixed_integer_feasible_set`, `Split`, `split_polyhedron`, `IsSplitInequality`
-- Semantic recall note: no direct mathlib owner surfaced for these mixed-integer splits; local
-- Chapter 5 precedent packages supported nonzero split data, while zero splits are accounted for
-- at the closure level because they contribute only the ambient polyhedron.

section SplitInequalities

variable {m n : ℕ}

/-- For `P = {x : ℝ^n | A x ≤ b}` and an index set `I` of integer
variables, the mixed-integer feasible set consists of the points of `P` whose `I`-coordinates are
integral. -/
def mixed_integer_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩
    {x : Fin n → ℝ | ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)}

/-- Membership in `mixed_integer_feasible_set A b I` is the conjunction of the polyhedral
constraints `A x ≤ b` and the integrality of the coordinates indexed by `I`. -/
theorem mem_mixed_integer_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ mixed_integer_feasible_set A b I ↔
      A *ᵥ x ≤ b ∧ ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ) :=
  Iff.rfl

/-- The scalar product `π x` of an integer vector `π` with a real vector `x`, viewed in `ℝ`. -/
def split_dot (π : Fin n → ℤ) (x : Fin n → ℝ) : ℝ :=
  (fun j ↦ (π j : ℝ)) ⬝ᵥ x

/-- `split_dot π x` is the finite sum `∑ j, π_j x_j` over the coordinates. -/
theorem split_dot_eq_sum
    (π : Fin n → ℤ)
    (x : Fin n → ℝ) :
    split_dot π x = ∑ j : Fin n, (π j : ℝ) * x j := by
  -- Unfold the dot product once to expose the coordinate sum formula.
  simp [split_dot, dotProduct]

/-- The open strip `π₀ < π x < π₀ + 1` associated with integral split data `(π, π₀)`. -/
def split_strip
    (π : Fin n → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  split_dot π ⁻¹' Set.Ioo (π0 : ℝ) ((π0 : ℝ) + 1)

/-- Membership in `split_strip π π0` is exactly the strict double inequality
`π₀ < π x < π₀ + 1`. -/
theorem mem_split_strip_iff
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ} :
    x ∈ split_strip π π0 ↔
      (π0 : ℝ) < split_dot π x ∧ split_dot π x < (π0 : ℝ) + 1 :=
  Iff.rfl

/-- The lower branch `{x ∈ P | π x ≤ π₀}` of the split disjunction attached to `(π, π₀)`. -/
def split_branch_lower
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  P ∩ {x : Fin n → ℝ | split_dot π x ≤ (π0 : ℝ)}

/-- Membership in `split_branch_lower P π π0` means belonging to `P` and satisfying `π x ≤ π₀`. -/
theorem mem_split_branch_lower_iff
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ} :
    x ∈ split_branch_lower P π π0 ↔ x ∈ P ∧ split_dot π x ≤ (π0 : ℝ) :=
  Iff.rfl

/-- The upper branch `{x ∈ P | π₀ + 1 ≤ π x}` of the split disjunction attached to `(π, π₀)`. -/
def split_branch_upper
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  P ∩ {x : Fin n → ℝ | (π0 : ℝ) + 1 ≤ split_dot π x}

/-- Membership in `split_branch_upper P π π0` means belonging to `P` and satisfying
`π₀ + 1 ≤ π x`. -/
theorem mem_split_branch_upper_iff
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {π0 : ℤ}
    {x : Fin n → ℝ} :
    x ∈ split_branch_upper P π π0 ↔ x ∈ P ∧ (π0 : ℝ) + 1 ≤ split_dot π x :=
  Iff.rfl

/-- The split hull `P^(π, π₀)` is the convex hull of the lower and upper split branches. -/
def split_hull
    (P : Set (Fin n → ℝ))
    (π : Fin n → ℤ)
    (π0 : ℤ) : Set (Fin n → ℝ) :=
  convexHull ℝ (split_branch_lower P π π0 ∪ split_branch_upper P π π0)

/-- Auxiliary pure-integer specialization: `P^split` is the intersection of all split hulls cut
out by nonzero integral split vectors when every coordinate is indexed as integral. -/
def split_closure (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  ⋂ π : {π : Fin n → ℤ // π ≠ 0}, ⋂ π0 : ℤ, split_hull P π.1 π0

namespace SplitHullNotation

scoped notation:max P "^(" π ", " π0 ")" => split_hull P π π0
scoped notation:max P "^split" => split_closure P

end SplitHullNotation

open scoped SplitHullNotation

/-- In the pure-integer case, membership in `P^split` means belonging to every split hull
`P^(π, π₀)` cut out by nonzero integral split data. -/
@[simp] theorem mem_split_closure_iff
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ P^split ↔ ∀ π : {π : Fin n → ℤ // π ≠ 0}, ∀ π0 : ℤ, x ∈ P^(π, π0) := by
  simp [split_closure]

/-- A split for the mixed-integer index set `I` is a pair `(π, π₀) ∈ ℤ^n × ℤ` whose coefficient
vector vanishes on the continuous-variable indices and whose coefficient vector is nonzero.
The source wording allows the zero vector, but zero splits contribute only the ambient polyhedron,
so the reusable owner packages the supported nonzero data. -/
structure Split (I : Finset (Fin n)) where
  π : Fin n → ℤ
  π0 : ℤ
  nonzero : π ≠ 0
  zero_on_continuous : ∀ j ∈ Iᶜ, π j = 0

/-- A split can be used as its integer coefficient vector `π`. -/
instance (I : Finset (Fin n)) : CoeFun (Split I) (fun _ ↦ Fin n → ℤ) where
  coe s := s.π

namespace Split

/-- The coefficient vector of a split vanishes on the coordinates outside the integer index set
`I`. -/
theorem coeff_eq_zero_of_not_mem
    {I : Finset (Fin n)}
    (s : Split I)
    {j : Fin n}
    (hj : j ∉ I) :
    s j = 0 :=
  s.zero_on_continuous j (by simpa using hj)

end Split

/-- Helper for Definition 5.1-extra-1: a supported split only sums over the integer-variable
indices `I`. -/
lemma splitDot_eq_sum_filterIntegerIndices
    (I : Finset (Fin n))
    (s : Split I)
    (x : Fin n → ℝ) :
    split_dot s x = I.sum (fun j ↦ (s j : ℝ) * x j) := by
  -- Rewrite the dot product as the full finite sum, then show the complementary coordinates
  -- vanish because a split has zero coefficients on continuous variables.
  rw [split_dot_eq_sum]
  calc
    ∑ j : Fin n, (s j : ℝ) * x j
        = I.sum (fun j ↦ (s j : ℝ) * x j) + Iᶜ.sum (fun j ↦ (s j : ℝ) * x j) := by
            simpa using
              (Finset.sum_add_sum_compl (s := I) (f := fun j : Fin n ↦ (s j : ℝ) * x j)).symm
    _ = I.sum (fun j ↦ (s j : ℝ) * x j) := by
          have hcompl :
              Iᶜ.sum (fun j ↦ (s j : ℝ) * x j) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j hj
            simp [s.coeff_eq_zero_of_not_mem, show j ∉ I by simpa using hj]
          rw [hcompl, add_zero]

/-- If `x` is integral on the coordinates indexed by `I`, then the split scalar product `π x` is
an integer for every split over `I`. -/
theorem split_dot_integral_of_integral_coordinates
    (I : Finset (Fin n))
    (s : Split I)
    {x : Fin n → ℝ}
    (hx : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)) :
    ∃ z : ℤ, split_dot s x = (z : ℝ) := by
  classical
  -- Sum the chosen witnesses over `I.attach` so each summand carries its membership proof.
  let zI : {j // j ∈ I} → ℤ := fun j ↦ Classical.choose (hx j.1 j.2)
  have hzI : ∀ j : {j // j ∈ I}, x j.1 = (zI j : ℝ) := by
    intro j
    exact Classical.choose_spec (hx j.1 j.2)
  refine ⟨I.attach.sum (fun j ↦ s j.1 * zI j), ?_⟩
  rw [splitDot_eq_sum_filterIntegerIndices]
  calc
    I.sum (fun j ↦ (s j : ℝ) * x j)
        = I.attach.sum (fun j ↦ (s j.1 : ℝ) * x j.1) := by
            simpa using
              (Finset.sum_attach I (fun j : Fin n ↦ (s j : ℝ) * x j)).symm
    _ = I.attach.sum (fun j ↦ (((s j.1) * zI j : ℤ) : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hzI j]
      simp only [Int.cast_mul]
    _ = ((I.attach.sum (fun j ↦ s j.1 * zI j) : ℤ) : ℝ) := by
          simp

/-- Every point of the mixed-integer feasible set satisfies one side of the split disjunction. -/
theorem mixed_integer_feasible_set_subset_split_union
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (s : Split I) :
    mixed_integer_feasible_set A b I ⊆
      split_branch_lower (polyhedron_le_set A b) s s.π0 ∪
        split_branch_upper (polyhedron_le_set A b) s s.π0 := by
  intro x hx
  -- Points of the mixed-integer set stay in the ambient polyhedron and have integral split value.
  rcases (mem_mixed_integer_feasible_set_iff A b I x).1 hx with ⟨hxP, hxInt⟩
  rcases split_dot_integral_of_integral_coordinates I s hxInt with ⟨z, hz⟩
  by_cases hle : z ≤ s.π0
  · left
    -- The integer split value lies on the lower side of the disjunction.
    refine (mem_split_branch_lower_iff).2 ⟨hxP, ?_⟩
    have hleR : (z : ℝ) ≤ (s.π0 : ℝ) := by
      exact_mod_cast hle
    simpa [hz] using hleR
  · right
    -- Otherwise the integer split value is at least `π₀ + 1`, so the upper branch applies.
    have hgt : s.π0 < z := lt_of_not_ge hle
    have hge : s.π0 + 1 ≤ z := Int.add_one_le_iff.mpr hgt
    refine (mem_split_branch_upper_iff).2 ⟨hxP, ?_⟩
    have hgeR : (s.π0 : ℝ) + 1 ≤ (z : ℝ) := by
      exact_mod_cast hge
    simpa [hz] using hgeR

/-- For a split `s = (π, π₀)`, the split polyhedron `P^(π, π₀)` is the convex hull of
`Π₁ ∪ Π₂`. -/
abbrev split_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {I : Finset (Fin n)}
    (s : Split I) : Set (Fin n → ℝ) :=
  (polyhedron_le_set A b)^(s, s.π0)

/-- Membership in `split_polyhedron A b s` means membership in the split hull of the matrix
polyhedron `polyhedron_le_set A b` cut out by `s`. -/
@[simp] theorem mem_split_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {I : Finset (Fin n)}
    {s : Split I}
    {x : Fin n → ℝ} :
    x ∈ split_polyhedron A b s ↔ x ∈ (polyhedron_le_set A b)^(s, s.π0) :=
  Iff.rfl

/-- The convex hull of the mixed-integer feasible set is contained in every split polyhedron. -/
theorem convexHull_mixed_integer_feasible_set_subset_split_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (s : Split I) :
    convexHull ℝ (mixed_integer_feasible_set A b I) ⊆ split_polyhedron A b s := by
  -- The mixed-integer set already lies in the split-branch union, so its convex hull lies in the
  -- convex hull of that union.
  simpa [split_polyhedron, split_hull] using
    convexHull_mono (mixed_integer_feasible_set_subset_split_union A b I s)

/-- An inequality `α x ≤ β` is a split inequality for `(A, b, I)` if
there exists a split `s` such that the inequality is valid for both split sets `Π₁` and `Π₂`. -/
def IsSplitInequality
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) : Prop :=
  ∃ s : Split I,
    is_valid_inequality
      (split_branch_lower (polyhedron_le_set A b) s s.π0 ∪
        split_branch_upper (polyhedron_le_set A b) s s.π0)
      α β

/-- Helper for Definition 5.1-extra-1: validity of a linear inequality is unchanged by taking the
convex hull of the underlying set. -/
lemma is_valid_inequality_convexHull_iff
    {S : Set (Fin n → ℝ)}
    {α : Fin n → ℝ}
    {β : ℝ} :
    is_valid_inequality (convexHull ℝ S) α β ↔ is_valid_inequality S α β := by
  constructor
  · -- Any inequality valid on the convex hull is valid on the original set by inclusion.
    intro hvalid
    rw [is_valid_inequality_iff] at hvalid ⊢
    intro x hx
    exact hvalid (subset_convexHull ℝ S hx)
  · -- Conversely, the feasible halfspace is convex, so it contains the whole convex hull.
    intro hvalid
    rw [is_valid_inequality_iff] at hvalid ⊢
    intro x hx
    have hsubset : S ⊆ {y : Fin n → ℝ | α ⬝ᵥ y ≤ β} := by
      intro y hy
      exact hvalid hy
    have hhalfspace :
        Convex ℝ {y : Fin n → ℝ | α ⬝ᵥ y ≤ β} := by
      intro u hu v hv a c ha hc hac
      have hu' : α ⬝ᵥ u ≤ β := by
        simpa using hu
      have hv' : α ⬝ᵥ v ≤ β := by
        simpa using hv
      calc
        α ⬝ᵥ (a • u + c • v) = a * (α ⬝ᵥ u) + c * (α ⬝ᵥ v) := by
          simp [dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]
        _ ≤ a * β + c * β := by
          have hau : a * (α ⬝ᵥ u) ≤ a * β := by
            nlinarith [hu', ha]
          have hcv : c * (α ⬝ᵥ v) ≤ c * β := by
            nlinarith [hv', hc]
          linarith
        _ = β := by
          calc
            a * β + c * β = (a + c) * β := by ring
            _ = β := by rw [hac, one_mul]
    exact convexHull_min hsubset hhalfspace hx

/-- A split inequality is equivalently an inequality valid for `P^(π, π₀)` for some split
`(π, π₀)`. -/
theorem isSplitInequality_iff_valid_on_split_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ) :
    IsSplitInequality A b I α β ↔
      ∃ s : Split I, is_valid_inequality (split_polyhedron A b s) α β := by
  constructor
  · intro hsplit
    rcases hsplit with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simpa [IsSplitInequality, split_polyhedron, split_hull] using
      (is_valid_inequality_convexHull_iff
        (S := split_branch_lower (polyhedron_le_set A b) s s.π0 ∪
          split_branch_upper (polyhedron_le_set A b) s s.π0)
        (α := α) (β := β)).2 hs
  · intro hvalid
    rcases hvalid with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    simpa [IsSplitInequality, split_polyhedron, split_hull] using
      (is_valid_inequality_convexHull_iff
        (S := split_branch_lower (polyhedron_le_set A b) s s.π0 ∪
          split_branch_upper (polyhedron_le_set A b) s s.π0)
        (α := α) (β := β)).1 hs

/-- Definition 5.1-extra-1. The split closure of `P = {x : ℝ^n | A x ≤ b}` relative to the
integer-coordinate set `I` is the intersection of `P` with the split polyhedra `P^(π, π₀)` over
all supported nonzero splits for `I`; this matches the source definition because the omitted zero
splits contribute only `P` itself. -/
def splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩ ⋂ s : Split I, split_polyhedron A b s

/-- Membership in the split closure means belonging to the ambient polyhedron and to every split
polyhedron cut out by supported nonzero split data on `I`. -/
@[simp] theorem mem_splitClosure_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (x : Fin n → ℝ) :
    x ∈ splitClosure A b I ↔
      x ∈ polyhedron_le_set A b ∧ ∀ s : Split I, x ∈ split_polyhedron A b s := by
  simp [splitClosure]

/-- The convex hull of the mixed-integer feasible set is contained in the split closure. -/
theorem convexHull_mixed_integer_feasible_set_subset_splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    convexHull ℝ (mixed_integer_feasible_set A b I) ⊆ splitClosure A b I := by
  intro x hx
  -- Membership in the split closure is the ambient-polyhedron condition plus all split-hull
  -- conditions.
  rw [mem_splitClosure_iff]
  constructor
  · -- The whole mixed-integer feasible set lies in `polyhedron_le_set A b`, and that ambient
    -- polyhedron is convex.
    have hsubset :
        mixed_integer_feasible_set A b I ⊆ polyhedron_le_set A b := by
      intro y hy
      exact (mem_mixed_integer_feasible_set_iff A b I y).1 hy |>.1
    exact convexHull_min hsubset (polyhedron_le_set_convex A b) hx
  · -- Every split polyhedron already contains the convex hull of the mixed-integer feasible set.
    intro s
    exact convexHull_mixed_integer_feasible_set_subset_split_polyhedron A b I s hx

/-- The split closure is contained in the original polyhedron `P = {x : ℝ^n | A x ≤ b}`. -/
theorem splitClosure_subset_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n)) :
    splitClosure A b I ⊆ polyhedron_le_set A b := by
  intro x hx
  -- The ambient polyhedron is the first conjunct in the split-closure definition.
  exact (mem_splitClosure_iff A b I x).1 hx |>.1

end SplitInequalities
