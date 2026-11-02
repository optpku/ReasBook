import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this file reuses
-- mathlib's `dotProduct` notation `⬝ᵥ` together with the chapter-local `polytope_skeleton` owner
-- for vertex adjacency.

/-- Starting from the negative-cost coordinates, toggle `j` exactly when needed to obtain even
parity. -/
noncomputable def exercise_3_4_even_parity_indices {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Finset (Fin n) :=
  let I := Finset.univ.filter fun i ↦ c i < 0
  if Even I.card then I else if j ∈ I then I.erase j else insert j I

/-- The explicit `0,1` vector obtained from the even-parity index set. -/
noncomputable def exercise_3_4_even_parity_optimizer {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Fin n → ℝ :=
  fun i ↦ if i ∈ exercise_3_4_even_parity_indices c j then 1 else 0

/-- If a global minimizing vertex of `P` already lies in `S`, then it is optimal for the objective
restricted to `S`. -/
theorem global_vertex_optimal_on_vertex_subset
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {S : Set (P.extremePoints ℝ)}
    (c : Fin n → ℝ)
    {v : P.extremePoints ℝ}
    (hvmin : ∀ x : P.extremePoints ℝ, c ⬝ᵥ v ≤ c ⬝ᵥ x)
    (hvS : v ∈ S) :
    v ∈ S ∧ ∀ x ∈ S, c ⬝ᵥ v ≤ c ⬝ᵥ x := by
  refine ⟨hvS, ?_⟩
  intro x hxS
  exact hvmin x

/-- Exercise 3.4 (1), outside-vertex step. If every adjacent vertex of `v` lies in `S`, each
vertex of `S` is no better than some vertex adjacent to `v`, and `v'` minimizes the objective
among the vertices adjacent to `v`, then `v'` is optimal for the objective restricted to `S`. -/
theorem optimize_over_vertex_subset_by_global_then_adjacent
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (S : Set (P.extremePoints ℝ))
    (c : Fin n → ℝ)
    {v v' : P.extremePoints ℝ}
    (hcover : ∀ ⦃y : P.extremePoints ℝ⦄, (polytope_skeleton P).Adj v y → y ∈ S)
    (hv'adj : (polytope_skeleton P).Adj v v')
    (hv'min : ∀ y : P.extremePoints ℝ, (polytope_skeleton P).Adj v y → c ⬝ᵥ v' ≤ c ⬝ᵥ y)
    (hdom : ∀ x ∈ S, ∃ y : P.extremePoints ℝ, (polytope_skeleton P).Adj v y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) :
    v' ∈ S ∧ ∀ x ∈ S, c ⬝ᵥ v' ≤ c ⬝ᵥ x := by
  refine ⟨hcover hv'adj, ?_⟩
  intro x hxS
  rcases hdom x hxS with ⟨y, hyadj, hyx⟩
  exact (hv'min y hyadj).trans hyx

/-- Helper for Exercise 3.4: on a `0,1` vector, the dot product is the sum over the coordinates
equal to `1`. -/
lemma dotProduct_eq_sum_one_coordinates_of_mem_zero_one_cube
    {n : ℕ} (c : Fin n → ℝ) {x : Fin n → ℝ} (hx : x ∈ zero_one_cube n) :
    c ⬝ᵥ x = Finset.sum (Finset.univ.filter (fun i : Fin n ↦ x i = 1)) c := by
  classical
  -- Replace each coordinate contribution by `c i` or `0` according to whether `x i = 1`.
  calc
    c ⬝ᵥ x = ∑ i, if x i = 1 then c i else 0 := by
      unfold dotProduct
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases (mem_zero_one_cube_iff.mp hx) i with hxi | hxi
      · simp [hxi]
      · simp [hxi]
    _ = Finset.sum (Finset.univ.filter (fun i : Fin n ↦ x i = 1)) c := by
      rw [Finset.sum_filter]

/-- Helper for Exercise 3.4: the `1`-coordinates of the explicit optimizer are exactly its chosen
index set. -/
lemma exercise_3_4_even_parity_optimizer_one_coordinates
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Finset.univ.filter (fun i : Fin n ↦ exercise_3_4_even_parity_optimizer c j i = 1) =
      exercise_3_4_even_parity_indices c j := by
  classical
  -- The optimizer is the indicator function of the chosen index set.
  ext i
  by_cases hi : i ∈ exercise_3_4_even_parity_indices c j
  · simp [exercise_3_4_even_parity_optimizer, hi]
  · simp [exercise_3_4_even_parity_optimizer, hi]

/-- Helper for Exercise 3.4: the explicit optimizer is a `0,1` vector. -/
lemma exercise_3_4_even_parity_optimizer_mem_zero_one_cube
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    exercise_3_4_even_parity_optimizer c j ∈ zero_one_cube n := by
  classical
  rw [mem_zero_one_cube_iff]
  -- Each coordinate is defined by an indicator, so it is automatically `0` or `1`.
  intro i
  by_cases hi : i ∈ exercise_3_4_even_parity_indices c j
  · right
    simp [exercise_3_4_even_parity_optimizer, hi]
  · left
    simp [exercise_3_4_even_parity_optimizer, hi]

/-- Helper for Exercise 3.4: the chosen support has even cardinality. -/
lemma exercise_3_4_even_parity_indices_even_card
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    Even (exercise_3_4_even_parity_indices c j).card := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0
  by_cases hEvenI : Even I.card
  · -- If the negative-cost support already has even size, nothing is toggled.
    simpa [exercise_3_4_even_parity_indices, I, hEvenI]
  · have hOddI : Odd I.card := Nat.not_even_iff_odd.mp hEvenI
    by_cases hjI : j ∈ I
    · -- Removing one negative-cost coordinate flips odd cardinality to even.
      have hEraseEven : Even (I.erase j).card := by
        rw [Finset.card_erase_of_mem hjI]
        simpa using hOddI.tsub_odd odd_one
      simpa [exercise_3_4_even_parity_indices, I, hEvenI, hjI] using hEraseEven
    · -- Inserting one new coordinate also flips odd cardinality to even.
      have hInsertEven : Even (insert j I).card := by
        rw [Finset.card_insert_of_notMem hjI]
        simpa using hOddI.add_one
      simpa [exercise_3_4_even_parity_indices, I, hEvenI, hjI] using hInsertEven

/-- Helper for Exercise 3.4: the negative-cost support minimizes the objective among all supports
without the parity constraint. -/
lemma negative_cost_support_sum_le_sum
    {n : ℕ} (c : Fin n → ℝ) (T : Finset (Fin n)) :
    let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0;
    Finset.sum I c ≤ Finset.sum T c := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0
  have hIdecomp : Finset.sum I c = Finset.sum (I \ T) c + Finset.sum (I ∩ T) c := by
    -- Split the negative-cost support into the part kept by `T` and the part omitted by `T`.
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter I T), Finset.sdiff_union_inter]
  have hTdecomp : Finset.sum T c = Finset.sum (T \ I) c + Finset.sum (T ∩ I) c := by
    -- Split `T` into the negative coordinates and the nonnegative coordinates it adds.
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T I), Finset.sdiff_union_inter]
  have hISdiffNonpos : Finset.sum (I \ T) c ≤ 0 := by
    -- Every coordinate removed from `I` still has negative cost.
    refine Finset.sum_nonpos fun i hi ↦ ?_
    exact le_of_lt ((Finset.mem_filter.mp (show i ∈ I from (Finset.mem_sdiff.mp hi).1)).2)
  have hTSdiffNonneg : 0 ≤ Finset.sum (T \ I) c := by
    -- Every coordinate added outside `I` has nonnegative cost.
    refine Finset.sum_nonneg fun i hi ↦ ?_
    exact not_lt.mp fun hlt ↦ (Finset.mem_sdiff.mp hi).2 (by simp [I, hlt])
  calc
    Finset.sum I c = Finset.sum (I \ T) c + Finset.sum (I ∩ T) c := hIdecomp
    _ ≤ 0 + Finset.sum (I ∩ T) c := by gcongr
    _ = Finset.sum (I ∩ T) c := by ring
    _ = Finset.sum (T ∩ I) c := by rw [Finset.inter_comm]
    _ ≤ Finset.sum (T \ I) c + Finset.sum (T ∩ I) c := by linarith
    _ = Finset.sum T c := hTdecomp.symm

/-- Helper for Exercise 3.4: the chosen even-parity support has the same objective as the
negative-cost support in the even case, and incurs exactly one `|c j|` penalty in the odd case. -/
lemma exercise_3_4_even_parity_indices_sum
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0;
    Finset.sum (exercise_3_4_even_parity_indices c j) c =
      if Even I.card then Finset.sum I c else Finset.sum I c + |c j| := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0
  by_cases hEvenI : Even I.card
  · -- No toggle is needed when the negative-cost support already has even size.
    simp [exercise_3_4_even_parity_indices, I, hEvenI]
  · by_cases hjI : j ∈ I
    · -- Removing `j` deletes the negative term `c j`, so the objective increases by `|c j|`.
      have hjNeg : c j < 0 := (Finset.mem_filter.mp hjI).2
      have hErase :
          Finset.sum (I.erase j) c = Finset.sum I c + |c j| := by
        have hsum := Finset.sum_erase_add I c hjI
        have hAbs : |c j| = -c j := abs_of_neg hjNeg
        linarith
      simpa [exercise_3_4_even_parity_indices, I, hEvenI, hjI] using hErase
    · -- Inserting `j` adds the nonnegative term `c j`, which equals `|c j|`.
      have hjNonneg : 0 ≤ c j := not_lt.mp fun hjNeg ↦
        hjI (by simp [I, hjNeg])
      have hInsert :
          Finset.sum (insert j I) c = Finset.sum I c + |c j| := by
        rw [Finset.sum_insert hjI]
        have hAbs : |c j| = c j := abs_of_nonneg hjNonneg
        linarith
      simpa [exercise_3_4_even_parity_indices, I, hEvenI, hjI, add_comm] using hInsert

/-- Helper for Exercise 3.4: when the negative-cost support has odd size, any even-cardinality
support pays at least one minimum-absolute-cost toggle. -/
lemma odd_negative_cost_support_sum_add_min_abs_le_sum_of_even_card
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n)
    (hj : ∀ i, |c j| ≤ |c i|) (T : Finset (Fin n))
    (hIodd :
      ¬ Even ((Finset.univ.filter fun i : Fin n ↦ c i < 0).card))
    (hTeven : Even T.card) :
    let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0;
    Finset.sum I c + |c j| ≤ Finset.sum T c := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0
  have hTneI : T ≠ I := by
    -- Different parities force `T` to differ from the odd negative-cost support.
    intro hTI
    subst hTI
    exact hIodd hTeven
  have hIinter_le : Finset.sum I c ≤ Finset.sum (T ∩ I) c := by
    have hIdecomp : Finset.sum I c = Finset.sum (I \ T) c + Finset.sum (I ∩ T) c := by
      -- Split `I` into the coordinates kept by `T` and the negative ones omitted by `T`.
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter I T), Finset.sdiff_union_inter]
    have hISdiffNonpos : Finset.sum (I \ T) c ≤ 0 := by
      refine Finset.sum_nonpos fun i hi ↦ ?_
      exact le_of_lt ((Finset.mem_filter.mp (show i ∈ I from (Finset.mem_sdiff.mp hi).1)).2)
    calc
      Finset.sum I c = Finset.sum (I \ T) c + Finset.sum (I ∩ T) c := hIdecomp
      _ ≤ 0 + Finset.sum (I ∩ T) c := by gcongr
      _ = Finset.sum (I ∩ T) c := by ring
      _ = Finset.sum (T ∩ I) c := by rw [Finset.inter_comm]
  by_cases hTI : (T \ I).Nonempty
  · rcases hTI with ⟨k, hk⟩
    have hkNonneg : 0 ≤ c k := by
      exact not_lt.mp fun hlt ↦ (Finset.mem_sdiff.mp hk).2 (by simp [I, hlt])
    have hTailNonneg : 0 ≤ Finset.sum ((T \ I).erase k) c := by
      -- All remaining terms in `T \ I` are still nonnegative.
      refine Finset.sum_nonneg fun i hi ↦ ?_
      exact not_lt.mp fun hlt ↦ (Finset.mem_sdiff.mp ((Finset.mem_erase.mp hi).2)).2
        (by simp [I, hlt])
    have hkLe : c k ≤ Finset.sum (T \ I) c := by
      have hsum := Finset.sum_erase_add (T \ I) c hk
      linarith
    have hMinLe : |c j| ≤ c k := by
      calc
        |c j| ≤ |c k| := hj k
        _ = c k := abs_of_nonneg hkNonneg
    have hTdecomp : Finset.sum T c = Finset.sum (T \ I) c + Finset.sum (T ∩ I) c := by
      -- Split `T` into the nonnegative extra coordinates and the negative coordinates.
      rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T I), Finset.sdiff_union_inter]
    calc
      Finset.sum I c + |c j| ≤ Finset.sum (T ∩ I) c + Finset.sum (T \ I) c := by
        linarith
      _ = Finset.sum T c := by
        rw [add_comm, hTdecomp]
  · have hTIEmpty : T \ I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTI
    have hTsubI : T ⊆ I := by
      -- If `T \ I` is empty, every element of `T` already belongs to `I`.
      intro i hiT
      by_contra hiI
      have : i ∈ T \ I := by simp [hiT, hiI]
      rw [hTIEmpty] at this
      simpa using this
    have hITNonempty : (I \ T).Nonempty := by
      by_contra hIT
      apply hTneI
      have hITEmpty : I \ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIT
      ext i
      by_cases hiT : i ∈ T
      · have hiI : i ∈ I := hTsubI hiT
        simp [hiT, hiI]
      · have hiI : i ∉ I := by
          intro hiI
          have : i ∈ I \ T := by simp [hiI, hiT]
          rw [hITEmpty] at this
          simpa using this
        simp [hiT, hiI]
    rcases hITNonempty with ⟨k, hk⟩
    have hkNeg : c k < 0 := (Finset.mem_filter.mp (show k ∈ I from (Finset.mem_sdiff.mp hk).1)).2
    have hTailNonpos : Finset.sum ((I \ T).erase k) c ≤ 0 := by
      -- All remaining omitted coordinates are still negative.
      refine Finset.sum_nonpos fun i hi ↦ ?_
      exact le_of_lt ((Finset.mem_filter.mp (show i ∈ I from (Finset.mem_sdiff.mp ((Finset.mem_erase.mp hi).2)).1)).2)
    have hSumLe : Finset.sum (I \ T) c ≤ c k := by
      have hsum := Finset.sum_erase_add (I \ T) c hk
      linarith
    have hMinLe : |c j| ≤ -c k := by
      calc
        |c j| ≤ |c k| := hj k
        _ = -c k := abs_of_neg hkNeg
    have hIdecomp : Finset.sum I c = Finset.sum (I \ T) c + Finset.sum T c := by
      -- Because `T ⊆ I`, the intersection term in the standard decomposition is exactly `T`.
      rw [← Finset.sum_union (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset hTsubI]
    have hPenalty : Finset.sum (I \ T) c ≤ -|c j| := by
      linarith
    calc
      Finset.sum I c + |c j| = (Finset.sum (I \ T) c + Finset.sum T c) + |c j| := by
        rw [hIdecomp]
      _ ≤ Finset.sum T c := by
        linarith

/-- Exercise 3.4 (2). Choosing all negative-cost coordinates and, when their number is odd,
toggling a coordinate `j` of minimum absolute cost yields an optimal `0,1` vector with an even
number of `1`s. -/
theorem even_parity_zero_one_optimizer_spec
    {n : ℕ}
    (c : Fin n → ℝ)
    (j : Fin n)
    (hj : ∀ i, |c j| ≤ |c i|) :
    let S : Set (Fin n → ℝ) :=
      {x ∈ zero_one_cube n | Even ((Finset.univ.filter fun i : Fin n ↦ x i = 1).card)};
    exercise_3_4_even_parity_optimizer c j ∈ S ∧
      ∀ x ∈ S, c ⬝ᵥ exercise_3_4_even_parity_optimizer c j ≤ c ⬝ᵥ x := by
  classical
  let S : Set (Fin n → ℝ) :=
    {x ∈ zero_one_cube n | Even ((Finset.univ.filter fun i : Fin n ↦ x i = 1).card)}
  let I : Finset (Fin n) := Finset.univ.filter fun i ↦ c i < 0
  have hOptCube : exercise_3_4_even_parity_optimizer c j ∈ zero_one_cube n :=
    exercise_3_4_even_parity_optimizer_mem_zero_one_cube c j
  have hOptSupport :
      Finset.univ.filter (fun i : Fin n ↦ exercise_3_4_even_parity_optimizer c j i = 1) =
        exercise_3_4_even_parity_indices c j :=
    exercise_3_4_even_parity_optimizer_one_coordinates c j
  have hOptEven :
      Even ((Finset.univ.filter fun i : Fin n ↦ exercise_3_4_even_parity_optimizer c j i = 1).card) := by
    -- The support description reduces parity to the chosen index set.
    rw [hOptSupport]
    exact exercise_3_4_even_parity_indices_even_card c j
  have hOptSum :
      c ⬝ᵥ exercise_3_4_even_parity_optimizer c j =
        Finset.sum (exercise_3_4_even_parity_indices c j) c := by
    -- Rewrite the optimizer objective as the sum over its chosen support.
    rw [dotProduct_eq_sum_one_coordinates_of_mem_zero_one_cube c hOptCube, hOptSupport]
  refine ⟨?_, ?_⟩
  · -- The optimizer is feasible: it is a `0,1` vector with even support size.
    exact ⟨hOptCube, hOptEven⟩
  · intro x hxS
    rcases hxS with ⟨hxCube, hxEven⟩
    have hxSum :
        c ⬝ᵥ x = Finset.sum (Finset.univ.filter (fun i : Fin n ↦ x i = 1)) c :=
      dotProduct_eq_sum_one_coordinates_of_mem_zero_one_cube c hxCube
    by_cases hEvenI : Even I.card
    · -- If the negative-cost support already has even size, it is feasible and optimal.
      have hChosen :
          Finset.sum (exercise_3_4_even_parity_indices c j) c = Finset.sum I c := by
        rw [exercise_3_4_even_parity_indices_sum (c := c) (j := j)]
        simp [I, hEvenI]
      have hMin :
          Finset.sum I c ≤ Finset.sum (Finset.univ.filter (fun i : Fin n ↦ x i = 1)) c := by
        simpa [I] using
          negative_cost_support_sum_le_sum c
            (Finset.univ.filter fun i : Fin n ↦ x i = 1)
      rw [hOptSum, hChosen, hxSum]
      exact hMin
    · -- If the negative-cost support has odd size, every feasible support pays one minimum toggle.
      have hChosen :
          Finset.sum (exercise_3_4_even_parity_indices c j) c =
            Finset.sum I c + |c j| := by
        rw [exercise_3_4_even_parity_indices_sum (c := c) (j := j)]
        simp [I, hEvenI]
      have hMin :
          Finset.sum I c + |c j| ≤
            Finset.sum (Finset.univ.filter (fun i : Fin n ↦ x i = 1)) c := by
        simpa [I] using
          odd_negative_cost_support_sum_add_min_abs_le_sum_of_even_card c j hj
            (Finset.univ.filter fun i : Fin n ↦ x i = 1) hEvenI hxEven
      rw [hOptSum, hChosen, hxSum]
      exact hMin
