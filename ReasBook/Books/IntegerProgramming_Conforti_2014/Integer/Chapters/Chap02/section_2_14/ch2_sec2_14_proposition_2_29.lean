import Mathlib.Analysis.Convex.Exposed
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped IntegerVectorNotation Matrix

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: the real-valued
indicator of a finite coordinate support. -/
private def zeroOneIndicator {r : ℕ} (S : Finset (Fin r)) : Fin r → ℝ :=
  fun i ↦ if i ∈ S then 1 else 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: a support indicator lies
in the zero-one cube, has the prescribed support, and is integral. -/
private lemma zeroOneIndicator_spec {r : ℕ} (S : Finset (Fin r)) :
    zeroOneIndicator S ∈ zero_one_cube r ∧
      Finset.univ.filter (fun i ↦ zeroOneIndicator S i = 1) = S ∧
      zeroOneIndicator S ∈ ℤ^r := by
  constructor
  · -- Each coordinate is definitionally either zero or one.
    rw [mem_zero_one_cube_iff]
    intro i
    by_cases hi : i ∈ S
    · exact Or.inr (if_pos hi)
    · exact Or.inl (if_neg hi)
  · constructor
    · -- Filtering the coordinates equal to one recovers exactly the support.
      ext i
      simp [zeroOneIndicator]
    · -- The two possible coordinate values are integer casts.
      rw [mem_integerVectors_iff_forall]
      intro i
      by_cases hi : i ∈ S
      · simp [zeroOneIndicator, hi]
      · simp [zeroOneIndicator, hi]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: extend a support by a
last coordinate exactly when its original cardinality is even. -/
private def oddParityCompletion {k : ℕ} (S : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  if Even S.card then insert (Fin.last k) (S.map Fin.castSuccEmb) else S.map Fin.castSuccEmb

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: every completed support
has odd cardinality. -/
private lemma oddParityCompletion_odd {k : ℕ} (S : Finset (Fin k)) :
    Odd (oddParityCompletion S).card := by
  by_cases hEven : Even S.card
  · -- In the even case, adjoining the new last coordinate flips parity.
    rw [oddParityCompletion, if_pos hEven,
      Finset.card_insert_of_notMem, Finset.card_map]
    · exact hEven.add_one
    · intro hlast
      rcases Finset.mem_map.mp hlast with ⟨i, _, hi⟩
      exact i.castSucc_ne_last hi
  · -- In the odd case, the embedding preserves cardinality.
    rw [oddParityCompletion, if_neg hEven, Finset.card_map]
    exact Nat.not_even_iff_odd.mp hEven

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: completion preserves
membership at every original coordinate. -/
private lemma mem_oddParityCompletion_castSucc_iff {k : ℕ}
    (S : Finset (Fin k)) (i : Fin k) :
    i.castSucc ∈ oddParityCompletion S ↔ i ∈ S := by
  -- The embedded coordinates are unaffected by the optional last-coordinate insertion.
  by_cases hEven : Even S.card
  · simp [oddParityCompletion, hEven]
  · simp [oddParityCompletion, hEven]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: odd-parity completion is
injective on finite supports. -/
private lemma oddParityCompletion_injective {k : ℕ} :
    Function.Injective (oddParityCompletion : Finset (Fin k) → Finset (Fin (k + 1))) := by
  intro S T hST
  -- Recover the original supports by testing their embedded coordinates.
  ext i
  rw [← mem_oddParityCompletion_castSucc_iff S i, hST,
    mem_oddParityCompletion_castSucc_iff T i]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: moving a coordinate from
one odd support to another yields two even supports whose indicator sum is unchanged. -/
private lemma not_commonStrictViolation_of_mem_notMem
    {r : ℕ} (c : Fin r → ℝ) (d : ℝ) (S T : Finset (Fin r)) (j : Fin r)
    (hSOdd : Odd S.card) (hTOdd : Odd T.card) (hjS : j ∈ S) (hjT : j ∉ T)
    (hvalid : ∀ U : Finset (Fin r), Even U.card → c ⬝ᵥ zeroOneIndicator U ≤ d)
    (hSStrict : d < c ⬝ᵥ zeroOneIndicator S)
    (hTStrict : d < c ⬝ᵥ zeroOneIndicator T) : False := by
  have hEraseEven : Even (S.erase j).card := by
    -- Removing the chosen coordinate changes the odd cardinality by one.
    rw [Finset.card_erase_of_mem hjS]
    exact hSOdd.tsub_odd odd_one
  have hInsertEven : Even (insert j T).card := by
    -- Adding the absent coordinate likewise changes odd cardinality by one.
    rw [Finset.card_insert_of_notMem hjT]
    exact hTOdd.add_one
  have hIndicatorSum :
      zeroOneIndicator (S.erase j) + zeroOneIndicator (insert j T) =
        zeroOneIndicator S + zeroOneIndicator T := by
    -- Pointwise, the moved coordinate contributes once on either side and all others are fixed.
    funext i
    by_cases hij : i = j
    · subst i
      simp [zeroOneIndicator, hjS, hjT]
    · simp [zeroOneIndicator, hij]
  have hDotSum :
      c ⬝ᵥ zeroOneIndicator (S.erase j) + c ⬝ᵥ zeroOneIndicator (insert j T) =
        c ⬝ᵥ zeroOneIndicator S + c ⬝ᵥ zeroOneIndicator T := by
    -- Linearity transports the pointwise indicator identity to the row evaluation.
    rw [← dotProduct_add, hIndicatorSum, dotProduct_add]
  -- The two valid even points cannot average to two strictly violating odd points.
  linarith [hvalid (S.erase j) hEraseEven, hvalid (insert j T) hInsertEven]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean`: one inequality valid on
all even supports cannot strictly exclude two distinct odd supports. -/
private lemma oddSupports_eq_of_commonStrictViolation
    {r : ℕ} (c : Fin r → ℝ) (d : ℝ) (S T : Finset (Fin r))
    (hSOdd : Odd S.card) (hTOdd : Odd T.card)
    (hvalid : ∀ U : Finset (Fin r), Even U.card → c ⬝ᵥ zeroOneIndicator U ≤ d)
    (hSStrict : d < c ⬝ᵥ zeroOneIndicator S)
    (hTStrict : d < c ⬝ᵥ zeroOneIndicator T) : S = T := by
  by_contra hST
  have hdiff :
      (∃ j ∈ S, j ∉ T) ∨ ∃ j ∈ T, j ∉ S := by
    -- Unequal finite supports differ in at least one of the two orientations.
    by_cases hSubset : S ⊆ T
    · right
      exact Finset.not_subset.mp (fun hReverse ↦ hST (Finset.Subset.antisymm hSubset hReverse))
    · left
      exact Finset.not_subset.mp hSubset
  rcases hdiff with ⟨j, hjS, hjT⟩ | ⟨j, hjT, hjS⟩
  · exact not_commonStrictViolation_of_mem_notMem c d S T j hSOdd hTOdd hjS hjT
      hvalid hSStrict hTStrict
  · exact not_commonStrictViolation_of_mem_notMem c d T S j hTOdd hSOdd hjT hjS
      hvalid hTStrict hSStrict

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_29.lean

Proposition 2.29. If a polyhedron `polyhedron_le_set A b` has pure-integer points exactly the
even-parity vectors in `zero_one_cube n`, and each row of `A *ᵥ x ≤ b` defines a facet of that
polyhedron, then the system has at least `2 ^ (n - 1)` inequalities. -/
theorem row_count_lower_bound_of_evenParityZeroOneIntegerPoints
    {m n : ℕ}
    (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hInt :
      pure_integer_points (polyhedron_le_set A b) =
        {x ∈ zero_one_cube n | Even ((Finset.univ.filter fun i : Fin n ↦ x i = 1).card)})
    (hfacetRows :
      ∀ i : Fin m,
        is_facet (polyhedron_le_set A b) (face_set (polyhedron_le_set A b) (A i) (b i))) :
    2 ^ (n - 1) ≤ m := by
  classical
  cases n with
  | zero =>
      -- The lower bound on the dimension rules out the empty-coordinate case.
      omega
  | succ k =>
      have hNotPolyhedron (S : Finset (Fin k)) :
          zeroOneIndicator (oddParityCompletion S) ∉ polyhedron_le_set A b := by
        intro hPolyhedron
        have hPure :
            zeroOneIndicator (oddParityCompletion S) ∈
              pure_integer_points (polyhedron_le_set A b) := by
          -- Feasibility and integrality would make this odd indicator a pure-integer point.
          exact (mem_pure_integer_points_iff).2
            ⟨hPolyhedron, (zeroOneIndicator_spec (oddParityCompletion S)).2.2⟩
        rw [hInt] at hPure
        rcases hPure with ⟨_, hEven⟩
        rw [(zeroOneIndicator_spec (oddParityCompletion S)).2.1] at hEven
        exact (Nat.not_even_iff_odd.mpr (oddParityCompletion_odd S)) hEven
      have hViolation (S : Finset (Fin k)) :
          ∃ i : Fin m,
            b i < A i ⬝ᵥ zeroOneIndicator (oddParityCompletion S) := by
        -- Nonfeasibility supplies a defining row that is strictly violated.
        have hNotSystem := hNotPolyhedron S
        rw [mem_polyhedron_le_set_iff] at hNotSystem
        simpa only [Pi.le_def, not_forall, not_le, Matrix.mulVec] using hNotSystem
      choose selectedRow hSelectedRow using hViolation
      have hSelectedRowInjective : Function.Injective selectedRow := by
        intro S T hRows
        have hvalid (U : Finset (Fin (k + 1))) (hUEven : Even U.card) :
            A (selectedRow S) ⬝ᵥ zeroOneIndicator U ≤ b (selectedRow S) := by
          have hPureEven :
              zeroOneIndicator U ∈ pure_integer_points (polyhedron_le_set A b) := by
            -- The equality `hInt` places every even zero-one indicator in the polyhedron.
            rw [hInt]
            refine ⟨(zeroOneIndicator_spec U).1, ?_⟩
            simpa [(zeroOneIndicator_spec U).2.1] using hUEven
          have hPolyhedron := (mem_pure_integer_points_iff.mp hPureEven).1
          exact (mem_polyhedron_le_set_iff.mp hPolyhedron) (selectedRow S)
        have hTStrict :
            b (selectedRow S) <
              A (selectedRow S) ⬝ᵥ zeroOneIndicator (oddParityCompletion T) := by
          -- A collision identifies the two selected row inequalities.
          rw [hRows]
          exact hSelectedRow T
        have hCompleted : oddParityCompletion S = oddParityCompletion T := by
          -- The averaging lemma forbids two different odd supports at one selected row.
          exact oddSupports_eq_of_commonStrictViolation
            (A (selectedRow S)) (b (selectedRow S))
            (oddParityCompletion S) (oddParityCompletion T)
            (oddParityCompletion_odd S) (oddParityCompletion_odd T)
            hvalid (hSelectedRow S) hTStrict
        exact oddParityCompletion_injective hCompleted
      have hCard := Fintype.card_le_of_injective selectedRow hSelectedRowInjective
      -- The domain is the power set of `Fin k`, so its cardinality is `2 ^ k`.
      simpa [Fintype.card_finset] using hCard
