import Mathlib.Analysis.Convex.Combination
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_39.LiftedPolyhedron

open scoped BigOperators Matrix

namespace Disjunctive

/-- The bounded lifted disjunctive relaxation with selector block in `[0, 1]^k`. -/
def boundedLiftedRelaxation
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) :=
  {p |
    p ∈ balas_lifted_polyhedron m A b ∧
      (∀ i : Fin k, 0 ≤ p.2.1 i ∧ p.2.1 i ≤ p.2.2 i • u i) ∧
      (∀ i : Fin k, p.2.2 i ≤ 1)}

/-- Membership in `boundedLiftedRelaxation m A b u` is the Balas lifted polyhedron together with
the bounding inequalities `0 ≤ yⁱ ≤ xᵢ uⁱ` and `xᵢ ≤ 1`. -/
theorem mem_boundedLiftedRelaxation_iff_mem_balas_lifted_polyhedron
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    (y : Fin n → ℝ)
    (yParts : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    (y, yParts, x) ∈ boundedLiftedRelaxation m A b u ↔
      (y, yParts, x) ∈ balas_lifted_polyhedron m A b ∧
        (∀ i : Fin k, 0 ≤ yParts i ∧ yParts i ≤ x i • u i) ∧
        (∀ i : Fin k, x i ≤ 1) :=
  Iff.rfl

/-- Membership in `boundedLiftedRelaxation m A b u` is exactly the bounded lifted system with the
selector block relaxed to `[0, 1]^k` and total selector mass `1`. -/
theorem mem_boundedLiftedRelaxation_iff
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    (y : Fin n → ℝ)
    (yParts : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    (y, yParts, x) ∈ boundedLiftedRelaxation m A b u ↔
      (∑ i : Fin k, yParts i = y) ∧
        (∀ i : Fin k, A i *ᵥ yParts i ≤ x i • b i) ∧
        (∀ i : Fin k, 0 ≤ yParts i ∧ yParts i ≤ x i • u i) ∧
        (∀ i : Fin k, 0 ≤ x i ∧ x i ≤ 1) ∧
        (∑ i : Fin k, x i = (1 : ℝ)) := by
  constructor
  · rintro ⟨hLifted, hBounds, hUpper⟩
    rcases (mem_balas_lifted_polyhedron_iff m A b y yParts x).1 hLifted with
      ⟨hineq, hsum, hSelectorSum, hNonneg⟩
    exact ⟨hsum, hineq, hBounds, fun i ↦ ⟨hNonneg i, hUpper i⟩, hSelectorSum⟩
  · rintro ⟨hsum, hineq, hBounds, hSelectorBox, hSelectorSum⟩
    exact ⟨(mem_balas_lifted_polyhedron_iff m A b y yParts x).2
        ⟨hineq, hsum, hSelectorSum, fun i ↦ (hSelectorBox i).1⟩,
      hBounds, fun i ↦ (hSelectorBox i).2⟩

/-- The bounded one-hot lifted disjunctive set with selector block in `{0, 1}^k`. -/
def boundedLiftedSet
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) :=
  {p |
    p ∈ boundedLiftedRelaxation m A b u ∧
      ∀ i : Fin k, p.2.2 i = 0 ∨ p.2.2 i = 1}

/-- Membership in `boundedLiftedSet m A b u` is the relaxed bounded lift together with binary
selector coordinates. -/
theorem mem_boundedLiftedSet_iff_mem_boundedLiftedRelaxation
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    (y : Fin n → ℝ)
    (yParts : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    (y, yParts, x) ∈ boundedLiftedSet m A b u ↔
      (y, yParts, x) ∈ boundedLiftedRelaxation m A b u ∧
        (∀ i : Fin k, x i = 0 ∨ x i = 1) :=
  Iff.rfl

/-- The bounded one-hot lifted set sits inside its relaxed bounded lift. -/
theorem boundedLiftedSet_subset_boundedLiftedRelaxation
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    boundedLiftedSet m A b u ⊆ boundedLiftedRelaxation m A b u := by
  intro p hp
  exact (mem_boundedLiftedSet_iff_mem_boundedLiftedRelaxation m A b u p.1 p.2.1 p.2.2).1 hp |>.1

/-- Membership in `boundedLiftedSet m A b u` is exactly the bounded lifted system with binary
selector coordinates and one active selector in total. -/
theorem mem_boundedLiftedSet_iff
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    (y : Fin n → ℝ)
    (yParts : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ) :
    (y, yParts, x) ∈ boundedLiftedSet m A b u ↔
      (∑ i : Fin k, yParts i = y) ∧
        (∀ i : Fin k, A i *ᵥ yParts i ≤ x i • b i) ∧
        (∀ i : Fin k, 0 ≤ yParts i ∧ yParts i ≤ x i • u i) ∧
        (∀ i : Fin k, x i = 0 ∨ x i = 1) ∧
        (∑ i : Fin k, x i = (1 : ℝ)) := by
  constructor
  · rintro ⟨hRelaxed, hBinary⟩
    rcases (mem_boundedLiftedRelaxation_iff m A b u y yParts x).1 hRelaxed with
      ⟨hsum, hineq, hBounds, hSelectorBox, hSelectorSum⟩
    exact ⟨hsum, hineq, hBounds, hBinary, hSelectorSum⟩
  · rintro ⟨hsum, hineq, hBounds, hBinary, hSelectorSum⟩
    have hSelectorBox : ∀ i : Fin k, 0 ≤ x i ∧ x i ≤ 1 := by
      intro i
      rcases hBinary i with hxi | hxi
      · constructor <;> simp [hxi]
      · constructor <;> simp [hxi]
    exact ⟨(mem_boundedLiftedRelaxation_iff m A b u y yParts x).2
        ⟨hsum, hineq, hBounds, hSelectorBox, hSelectorSum⟩,
      hBinary⟩

/-- Helper for Proposition 2.20: the one-hot witness attached to selector `i`, with the active
block normalized by `(x i)⁻¹`. -/
private noncomputable def oneHotBoundedLiftedPoint
    {n k : ℕ}
    (yParts : Fin k → Fin n → ℝ)
    (x : Fin k → ℝ)
    (i : Fin k) :
    ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) :=
  ((x i)⁻¹ • yParts i, Pi.single i ((x i)⁻¹ • yParts i), Pi.single i (1 : ℝ))

/-- Helper for Proposition 2.20: the bounded lifted relaxation is convex. -/
lemma convex_boundedLiftedRelaxation
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    Convex ℝ (boundedLiftedRelaxation m A b u) := by
  intro p hp q hq a c ha hc hac
  rcases p with ⟨x, xParts, δ⟩
  rcases q with ⟨y, yParts, ε⟩
  rw [mem_boundedLiftedRelaxation_iff m A b u] at hp hq ⊢
  rcases hp with ⟨hsumX, hineqX, hBoundsX, hδBox, hδsum⟩
  rcases hq with ⟨hsumY, hineqY, hBoundsY, hεBox, hεsum⟩
  let zParts : Fin k → Fin n → ℝ := fun i ↦ a • xParts i + c • yParts i
  let ζ : Fin k → ℝ := fun i ↦ a * δ i + c * ε i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The block decomposition equation is preserved by convex combination.
    calc
      ∑ i : Fin k, zParts i = ∑ i : Fin k, (a • xParts i + c • yParts i) := by
        rfl
      _ = a • ∑ i : Fin k, xParts i + c • ∑ i : Fin k, yParts i := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = a • x + c • y := by
        rw [hsumX, hsumY]
  · -- Each matrix inequality is preserved rowwise by the same convex combination.
    intro i j
    have hxij : (A i *ᵥ xParts i) j ≤ δ i * b i j := by
      simpa [Pi.smul_apply, smul_eq_mul] using hineqX i j
    have hyij : (A i *ᵥ yParts i) j ≤ ε i * b i j := by
      simpa [Pi.smul_apply, smul_eq_mul] using hineqY i j
    have hax : a * (A i *ᵥ xParts i) j ≤ a * (δ i * b i j) := by
      exact mul_le_mul_of_nonneg_left hxij ha
    have hcy : c * (A i *ᵥ yParts i) j ≤ c * (ε i * b i j) := by
      exact mul_le_mul_of_nonneg_left hyij hc
    have hsum := add_le_add hax hcy
    simpa [zParts, ζ, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      left_distrib, right_distrib, mul_add, add_mul, mul_assoc] using hsum
  · -- The box bounds are also preserved componentwise.
    intro i
    constructor
    · intro j
      exact add_nonneg (mul_nonneg ha ((hBoundsX i).1 j)) (mul_nonneg hc ((hBoundsY i).1 j))
    · intro j
      have hxij : xParts i j ≤ δ i * u i j := by
        simpa [Pi.smul_apply, smul_eq_mul] using (hBoundsX i).2 j
      have hyij : yParts i j ≤ ε i * u i j := by
        simpa [Pi.smul_apply, smul_eq_mul] using (hBoundsY i).2 j
      have hax : a * xParts i j ≤ a * (δ i * u i j) := by
        exact mul_le_mul_of_nonneg_left hxij ha
      have hcy : c * yParts i j ≤ c * (ε i * u i j) := by
        exact mul_le_mul_of_nonneg_left hyij hc
      have hsum := add_le_add hax hcy
      simpa [zParts, ζ, Pi.smul_apply, smul_eq_mul, left_distrib, right_distrib, mul_add,
        add_mul, mul_assoc] using hsum
  · -- The selector interval constraints remain in `[0, 1]`.
    intro i
    constructor
    · exact add_nonneg (mul_nonneg ha (hδBox i).1) (mul_nonneg hc (hεBox i).1)
    · have hax : a * δ i ≤ a * 1 := by
        exact mul_le_mul_of_nonneg_left (hδBox i).2 ha
      have hcy : c * ε i ≤ c * 1 := by
        exact mul_le_mul_of_nonneg_left (hεBox i).2 hc
      have hsum := add_le_add hax hcy
      have hsum' : a * δ i + c * ε i ≤ a + c := by
        simpa [mul_one] using hsum
      calc
        a * δ i + c * ε i ≤ a + c := hsum'
        _ = 1 := hac
  · -- The selectors still sum to one.
    calc
      ∑ i : Fin k, ζ i = ∑ i : Fin k, (a * δ i + c * ε i) := by
        rfl
      _ = a * ∑ i : Fin k, δ i + c * ∑ i : Fin k, ε i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = 1 := by
        simpa [hδsum, hεsum] using hac

/-- Helper for Proposition 2.20: a relaxed block vanishes when its selector coordinate is zero. -/
private lemma part_eq_zero_of_selector_eq_zero
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    {y : Fin n → ℝ}
    {yParts : Fin k → Fin n → ℝ}
    {x : Fin k → ℝ}
    (hRelaxed : (y, yParts, x) ∈ boundedLiftedRelaxation m A b u)
    {i : Fin k}
    (hxi : x i = 0) :
    yParts i = 0 := by
  rcases (mem_boundedLiftedRelaxation_iff m A b u y yParts x).1 hRelaxed with
    ⟨-, -, hBounds, -, -⟩
  -- The lower and upper bounds squeeze every coordinate of the block to zero.
  ext j
  have hLower : 0 ≤ yParts i j := (hBounds i).1 j
  have hUpper : yParts i j ≤ 0 := by
    simpa [hxi, Pi.smul_apply, smul_eq_mul] using (hBounds i).2 j
  exact le_antisymm hUpper hLower

/-- Helper for Proposition 2.20: scaling an active relaxed block by `(x i)⁻¹` preserves the box
constraints `0 ≤ · ≤ u i`. -/
private lemma scaled_part_mem_box_of_positive_selector
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    {y : Fin n → ℝ}
    {yParts : Fin k → Fin n → ℝ}
    {x : Fin k → ℝ}
    (hRelaxed : (y, yParts, x) ∈ boundedLiftedRelaxation m A b u)
    {i : Fin k}
    (hxi : 0 < x i) :
    0 ≤ (x i)⁻¹ • yParts i ∧ (x i)⁻¹ • yParts i ≤ u i := by
  rcases (mem_boundedLiftedRelaxation_iff m A b u y yParts x).1 hRelaxed with
    ⟨-, -, hBounds, _, _⟩
  constructor
  · -- Positivity survives scaling by a positive inverse.
    intro j
    exact mul_nonneg (inv_nonneg.2 (le_of_lt hxi)) ((hBounds i).1 j)
  · -- Divide the upper bound by the positive selector.
    intro j
    have hij : yParts i j ≤ x i * u i j := by
      simpa [Pi.smul_apply, smul_eq_mul] using (hBounds i).2 j
    have hdiv : yParts i j / x i ≤ u i j := by
      refine (div_le_iff₀ hxi).2 ?_
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hij
    simpa [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hdiv

/-- Helper for Proposition 2.20: the normalized one-hot witness of a positive selector belongs to
the bounded one-hot lifted set. -/
private lemma oneHotPoint_mem_boundedLiftedSet_of_pos
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ)
    {y : Fin n → ℝ}
    {yParts : Fin k → Fin n → ℝ}
    {x : Fin k → ℝ}
    (hRelaxed : (y, yParts, x) ∈ boundedLiftedRelaxation m A b u)
    {i : Fin k}
    (hxi : 0 < x i) :
    oneHotBoundedLiftedPoint yParts x i ∈ boundedLiftedSet m A b u := by
  rcases (mem_boundedLiftedRelaxation_iff_mem_balas_lifted_polyhedron m A b u y yParts x).1
      hRelaxed with ⟨hLifted, -, -⟩
  rw [mem_boundedLiftedSet_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Only the active block contributes to the reconstructed first component.
    ext j
    rw [Fintype.sum_eq_single i]
    · simp [oneHotBoundedLiftedPoint]
    · intro l hli
      simp [oneHotBoundedLiftedPoint, hli]
  · -- The active block satisfies the scaled input inequalities, and all others are zero.
    intro l
    by_cases hli : l = i
    · subst hli
      simpa [oneHotBoundedLiftedPoint] using
        scaled_part_mem_input_polyhedron_of_positive_delta m A b hLifted hxi
    · simp [oneHotBoundedLiftedPoint, hli]
  · -- The active block satisfies the scaled box bounds, and inactive blocks are zero.
    intro l
    by_cases hli : l = i
    · subst hli
      simpa [oneHotBoundedLiftedPoint] using
        scaled_part_mem_box_of_positive_selector m A b u hRelaxed hxi
    · constructor <;> simp [oneHotBoundedLiftedPoint, hli]
  · -- The selector vector is one-hot, hence binary.
    intro l
    by_cases hli : l = i <;> simp [oneHotBoundedLiftedPoint, hli]
  · -- The one-hot selector vector sums to one.
    rw [Fintype.sum_eq_single i]
    · simp [oneHotBoundedLiftedPoint]
    · intro l hli
      simp [oneHotBoundedLiftedPoint, hli]

/-- Helper for Proposition 2.20: every relaxed bounded point is a convex combination of the
one-hot points attached to its positive selectors. -/
lemma boundedLiftedRelaxation_subset_convexHull_boundedLiftedSet
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    boundedLiftedRelaxation m A b u ⊆ convexHull ℝ (boundedLiftedSet m A b u) := by
  intro p hp
  rcases p with ⟨y, yParts, x⟩
  rcases (mem_boundedLiftedRelaxation_iff m A b u y yParts x).1 hp with
    ⟨hsum, -, -, hxBox, hxsum⟩
  classical
  let s : Finset (Fin k) := Finset.univ.filter fun i ↦ 0 < x i
  let z : Fin k → ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) :=
    fun i ↦ oneHotBoundedLiftedPoint yParts x i
  have hzMem : ∀ i ∈ s, z i ∈ boundedLiftedSet m A b u := by
    intro i hi
    have hxi : 0 < x i := by
      simpa [s] using (Finset.mem_filter.1 hi).2
    simpa [z] using oneHotPoint_mem_boundedLiftedSet_of_pos m A b u hp hxi
  have hweights_nonneg : ∀ i ∈ s, 0 ≤ x i := by
    intro i hi
    exact (hxBox i).1
  have hweights_sum : Finset.sum s x = (1 : ℝ) := by
    have hzero_not_pos :
        Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hnotpos : ¬ 0 < x i := by
        simpa using (Finset.mem_filter.1 hi).2
      exact le_antisymm (le_of_not_gt hnotpos) (hxBox i).1
    have hpartition :
        Finset.sum s x + Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) x =
          ∑ i : Fin k, x i := by
      simpa [s] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i : Fin k ↦ 0 < x i) x)
    calc
      Finset.sum s x =
          Finset.sum s x + Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) x := by
        rw [hzero_not_pos, add_zero]
      _ = ∑ i : Fin k, x i := hpartition
      _ = 1 := hxsum
  have hrecover :
      ∀ i : Fin k, x i • ((x i)⁻¹ • yParts i) = yParts i := by
    intro i
    by_cases hxi : 0 < x i
    · -- On active selectors, multiplying by the selector undoes the normalization.
      simp [smul_smul, hxi.ne', one_smul]
    · -- On inactive selectors, both the selector and the block vanish.
      have hxi0 : x i = 0 := le_antisymm (le_of_not_gt hxi) (hxBox i).1
      have hyi0 : yParts i = 0 := part_eq_zero_of_selector_eq_zero m A b u hp hxi0
      simp [hxi0, hyi0]
  have hweighted_eq_total :
      Finset.sum s (fun i ↦ x i • z i) = ∑ i : Fin k, x i • z i := by
    have hzero_not_pos :
        Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) (fun i ↦ x i • z i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hnotpos : ¬ 0 < x i := by
        simpa using (Finset.mem_filter.1 hi).2
      have hxi0 : x i = 0 := le_antisymm (le_of_not_gt hnotpos) (hxBox i).1
      simp [z, hxi0]
    have hpartition :
        Finset.sum s (fun i ↦ x i • z i) +
            Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) (fun i ↦ x i • z i) =
          ∑ i : Fin k, x i • z i := by
      simpa [s] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i : Fin k ↦ 0 < x i) (fun i ↦ x i • z i))
    calc
      Finset.sum s (fun i ↦ x i • z i) =
          Finset.sum s (fun i ↦ x i • z i) +
            Finset.sum (Finset.univ.filter (fun i : Fin k ↦ ¬ 0 < x i)) (fun i ↦ x i • z i) := by
        rw [hzero_not_pos, add_zero]
      _ = ∑ i : Fin k, x i • z i := hpartition
  have hfirst_term : ∀ i : Fin k, x i • (z i).1 = yParts i := by
    intro i
    simpa [z, oneHotBoundedLiftedPoint] using hrecover i
  have hpart_term :
      ∀ i : Fin k, x i • (z i).2.1 = fun j : Fin k ↦ if i = j then yParts i else 0 := by
    intro i
    ext j l
    by_cases hji : i = j
    · subst j
      have hrecj : (x i • ((x i)⁻¹ • yParts i)) l = yParts i l := by
        exact congrArg (fun f : Fin n → ℝ ↦ f l) (hrecover i)
      simpa [z, oneHotBoundedLiftedPoint, Pi.smul_apply, smul_eq_mul] using hrecj
    · simp [z, oneHotBoundedLiftedPoint, hji, Pi.smul_apply, smul_eq_mul]
  have hselector_term :
      ∀ i : Fin k, x i • (z i).2.2 = x i • fun j : Fin k ↦ if i = j then 1 else 0 := by
    intro i
    ext j
    by_cases hji : i = j <;> simp [z, oneHotBoundedLiftedPoint, hji, Pi.smul_apply, smul_eq_mul]
  have hrepr_total : ∑ i : Fin k, x i • z i = (y, yParts, x) := by
    refine Prod.ext ?_ ?_
    · -- The first component recovers `y = ∑ i yⁱ`.
      ext j
      let evalFirst : ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) →+ ℝ :=
        { toFun := fun p ↦ p.1 j
          map_zero' := rfl
          map_add' := by
            intro p q
            rfl }
      have hmap :
          ((∑ i : Fin k, x i • z i).1) j = ∑ i : Fin k, (x i • (z i).1) j := by
        change evalFirst (∑ i : Fin k, x i • z i) = ∑ i : Fin k, evalFirst (x i • z i)
        rw [map_sum]
      calc
        ((∑ i : Fin k, x i • z i).1) j = ∑ i : Fin k, (x i • (z i).1) j := hmap
        _ = ∑ i : Fin k, yParts i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact congrArg (fun f : Fin n → ℝ ↦ f j) (hfirst_term i)
        _ = y j := by
          simpa using congrArg (fun f : Fin n → ℝ ↦ f j) hsum
    · refine Prod.ext ?_ ?_
      · -- The part family recovers by summing the weighted one-hot blocks.
        ext j l
        let evalPart : ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) →+ ℝ :=
          { toFun := fun p ↦ p.2.1 j l
            map_zero' := rfl
            map_add' := by
              intro p q
              rfl }
        have hmap :
            ((∑ i : Fin k, x i • z i).2.1 j) l =
              ∑ i : Fin k, ((x i • (z i).2.1) j) l := by
          change evalPart (∑ i : Fin k, x i • z i) = ∑ i : Fin k, evalPart (x i • z i)
          rw [map_sum]
        calc
          ((∑ i : Fin k, x i • z i).2.1 j) l = ∑ i : Fin k, ((x i • (z i).2.1) j) l := hmap
          _ = ∑ i : Fin k, ((fun j' : Fin k ↦ if i = j' then yParts i else 0) j) l := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact congrArg (fun f : Fin k → Fin n → ℝ ↦ f j l) (hpart_term i)
          _ = yParts j l := by
            rw [Fintype.sum_eq_single j]
            · simp
            · intro i hij
              simp [hij]
      · -- The selector family recovers by summing the weighted coordinate vectors.
        ext j
        let evalSelector : ((Fin n → ℝ) × (Fin k → Fin n → ℝ) × (Fin k → ℝ)) →+ ℝ :=
          { toFun := fun p ↦ p.2.2 j
            map_zero' := rfl
            map_add' := by
              intro p q
              rfl }
        have hmap :
            ((∑ i : Fin k, x i • z i).2.2) j = ∑ i : Fin k, ((x i • (z i).2.2) j) := by
          change evalSelector (∑ i : Fin k, x i • z i) = ∑ i : Fin k, evalSelector (x i • z i)
          rw [map_sum]
        calc
          ((∑ i : Fin k, x i • z i).2.2) j = ∑ i : Fin k, ((x i • (z i).2.2) j) := hmap
          _ = ∑ i : Fin k, (x i • (fun j : Fin k ↦ if i = j then 1 else 0) j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact congrArg (fun f : Fin k → ℝ ↦ f j) (hselector_term i)
          _ = x j := by
            rw [Fintype.sum_eq_single j]
            · simp
            · intro i hij
              simp [hij]
  have hsum_mem :
      Finset.sum s (fun i ↦ x i • z i) ∈ convexHull ℝ (boundedLiftedSet m A b u) := by
    -- The positive-selector support points lie in the set, so their weighted sum stays in the hull.
    exact (convex_convexHull ℝ (boundedLiftedSet m A b u)).sum_mem hweights_nonneg hweights_sum
      (fun i hi ↦ (subset_convexHull ℝ (boundedLiftedSet m A b u)) (hzMem i hi))
  -- The weighted sum equals the original point, so the point lies in the convex hull.
  have hrepr : Finset.sum s (fun i ↦ x i • z i) = (y, yParts, x) := by
    rw [hweighted_eq_total, hrepr_total]
  exact hrepr ▸ hsum_mem

/-- Proposition 2.20. The convex hull of the bounded one-hot lifted disjunctive set equals the
same lifted system with the selector block relaxed from `{0, 1}^k` to `[0, 1]^k`. -/
theorem convexHull_boundedLiftedSet_eq_relaxation
    {n k : ℕ}
    (m : Fin k → ℕ)
    (A : ∀ i : Fin k, Matrix (Fin (m i)) (Fin n) ℝ)
    (b : ∀ i : Fin k, Fin (m i) → ℝ)
    (u : Fin k → Fin n → ℝ) :
    convexHull ℝ (boundedLiftedSet m A b u) = boundedLiftedRelaxation m A b u := by
  apply le_antisymm
  · -- Every one-hot bounded point is already relaxed, and the relaxation is convex.
    exact convexHull_min
      (boundedLiftedSet_subset_boundedLiftedRelaxation m A b u)
      (convex_boundedLiftedRelaxation m A b u)
  · -- Every relaxed point is the convex combination of its positive-selector one-hot witnesses.
    exact boundedLiftedRelaxation_subset_convexHull_boundedLiftedSet m A b u

end Disjunctive
