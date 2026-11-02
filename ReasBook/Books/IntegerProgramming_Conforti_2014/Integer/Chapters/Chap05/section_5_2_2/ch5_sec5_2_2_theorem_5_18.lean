import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_theorem_1_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_theorem_5_18.FaceDescent

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Theorem518

variable {n : ℕ}

/-- Helper for Theorem 5.18: the pure-integer Chvátal closure is monotone under set inclusion. -/
lemma pureIntegerChvatalClosure_mono
    {P Q : Set (Fin n → ℝ)}
    (hPQ : P ⊆ Q) :
    pure_integer_chvatal_closure P ⊆ pure_integer_chvatal_closure Q := by
  intro x hx
  rw [mem_pure_integer_chvatal_closure_iff] at hx ⊢
  -- Keep the ambient membership and restrict every valid inequality on `Q` to `P`.
  refine ⟨hPQ hx.1, ?_⟩
  intro c d hvalidQ
  exact hx.2 c d (fun y hyP ↦ hvalidQ (hPQ hyP))

/-- Helper for Theorem 5.18: the dot product of an integral row with an integral point is an
integer. -/
lemma exists_int_dotProduct_of_mem_integerVectors
    {c : Fin n → ℤ}
    {x : Fin n → ℝ}
    (hx_int : x ∈ integerVectors n) :
    ∃ z : ℤ, (fun i ↦ (c i : ℝ)) ⬝ᵥ x = (z : ℝ) := by
  rw [mem_integerVectors_iff_forall] at hx_int
  choose z hz using hx_int
  -- Rewrite coordinatewise using the integral coordinates of `x`.
  refine ⟨c ⬝ᵥ z, ?_⟩
  calc
    (fun i ↦ (c i : ℝ)) ⬝ᵥ x = ∑ i : Fin n, (c i : ℝ) * x i := by
      simp [dotProduct]
    _ = ∑ i : Fin n, (c i : ℝ) * (z i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hz i]
    _ = ((∑ i : Fin n, c i * z i : ℤ) : ℝ) := by
          simp
    _ = ((c ⬝ᵥ z : ℤ) : ℝ) := by
          simp [dotProduct]

/-- Helper for Theorem 5.18: if `P` is a rational polyhedron, then its pure-integer hull is still
contained in `P`. -/
lemma pureIntegerHull_subset_of_rationalPolyhedron
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    pure_integer_hull P ⊆ P := by
  have hP_polyhedron : is_polyhedron P := by
    rcases hP_rational with ⟨m, A, b, rfl⟩
    exact ⟨m, A.map (Rat.castHom ℝ), fun i ↦ (b i : ℝ), rfl⟩
  have hP_convex : Convex ℝ P :=
    convex_of_is_polyhedron hP_polyhedron
  -- The generators `P ∩ ℤ^n` already lie in `P`, so convexity absorbs the hull.
  rw [pure_integer_hull_eq_convexHull]
  intro x hx
  exact convexHull_min (fun y hy ↦ hy.1) hP_convex hx

/-- Helper for Theorem 5.18: the pure-integer hull is already a fixed point of one Chvátal step. -/
lemma pureIntegerChvatalClosure_pureIntegerHull_eq
    (P : Set (Fin n → ℝ)) :
    pure_integer_chvatal_closure (pure_integer_hull P) = pure_integer_hull P := by
  ext x
  rw [mem_pure_integer_chvatal_closure_iff]
  constructor
  · intro hx
    -- Closure membership records ambient membership as its first conjunct.
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro c d hvalid
    have hvalid_on_points :
        is_valid_inequality (pure_integer_points P) (fun i ↦ (c i : ℝ)) d := by
      -- First restrict validity from the convex hull to the generating integer points.
      simpa [pure_integer_hull] using
        (is_valid_inequality_convexHull_iff
          (S := pure_integer_points P)
          (α := fun i ↦ (c i : ℝ))
          (β := d)).1 hvalid
    have hrounded_on_points :
        is_valid_inequality
          (pure_integer_points P)
          (fun i ↦ (c i : ℝ))
          (((Int.floor d : ℤ) : ℝ)) := by
      intro y hy
      rcases (mem_pure_integer_points_iff.mp hy) with ⟨_, hy_int⟩
      rcases exists_int_dotProduct_of_mem_integerVectors (c := c) hy_int with ⟨z, hz⟩
      have hy_le : (fun i ↦ (c i : ℝ)) ⬝ᵥ y ≤ d :=
        hvalid_on_points hy
      have hz_le : z ≤ Int.floor d := by
        rw [hz] at hy_le
        exact Int.le_floor.mpr hy_le
      have hz_le_real : (z : ℝ) ≤ (((Int.floor d : ℤ) : ℝ)) := by
        exact_mod_cast hz_le
      simpa [hz] using hz_le_real
    have hrounded_on_hull :
        is_valid_inequality
          (pure_integer_hull P)
          (fun i ↦ (c i : ℝ))
          (((Int.floor d : ℤ) : ℝ)) := by
      -- Then promote the rounded bound back from the generators to the hull.
      simpa [pure_integer_hull] using
        (is_valid_inequality_convexHull_iff
          (S := pure_integer_points P)
          (α := fun i ↦ (c i : ℝ))
          (β := (((Int.floor d : ℤ) : ℝ)))).2 hrounded_on_points
    exact hrounded_on_hull hx

/-- Helper for Theorem 5.18: every iterate of the pure-integer Chvátal closure still contains the
pure-integer hull of a rational polyhedron. -/
lemma pureIntegerHull_subset_iterate
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∀ s : ℕ, pure_integer_hull P ⊆ (pure_integer_chvatal_closure^[s]) P
  | 0 => by
      -- At time `0`, this is exactly the basic inclusion `P_I ⊆ P`.
      exact pureIntegerHull_subset_of_rationalPolyhedron P hP_rational
  | s + 1 => by
      intro x hx
      have hs_subset :
          pure_integer_hull P ⊆ (pure_integer_chvatal_closure^[s]) P :=
        pureIntegerHull_subset_iterate P hP_rational s
      have hx_closure : x ∈ pure_integer_chvatal_closure (pure_integer_hull P) := by
        -- Replace the hull by its fixed-point Chvátal closure before using monotonicity.
        simpa [pureIntegerChvatalClosure_pureIntegerHull_eq P] using hx
      have hmono :
          pure_integer_chvatal_closure (pure_integer_hull P) ⊆
            pure_integer_chvatal_closure ((pure_integer_chvatal_closure^[s]) P) :=
        pureIntegerChvatalClosure_mono hs_subset
      simpa [Function.iterate_succ_apply'] using hmono hx_closure

/-- Helper for Theorem 5.18: membership in a later iterate descends to any earlier iterate. -/
lemma mem_iteratePureIntegerChvatalClosure_of_le
    (Q : Set (Fin n → ℝ))
    {s t : ℕ}
    (hst : s ≤ t)
    {x : Fin n → ℝ}
    (hx : x ∈ (pure_integer_chvatal_closure^[t]) Q) :
    x ∈ (pure_integer_chvatal_closure^[s]) Q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  -- Normalize the iterate once and then drop the later suffix by monotonicity of the chain.
  have hxIter :
      x ∈ (pure_integer_chvatal_closure^[k]) ((pure_integer_chvatal_closure^[s]) Q) := by
    simpa [Function.iterate_add_apply, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
  exact iteratePureIntegerChvatalClosure_subset ((pure_integer_chvatal_closure^[s]) Q) k hxIter

/-- Helper for Theorem 5.18: if `aff(P)` has no integer point, then the pure-integer hull is
already empty. -/
lemma pureIntegerHull_eq_empty_of_noAffineIntegerPoint
    (P : Set (Fin n → ℝ))
    (h_no_affine_integer :
      ¬ ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty) :
    pure_integer_hull P = ∅ := by
  refine Set.eq_empty_iff_forall_not_mem.mpr ?_
  intro x hx
  have hPoints_nonempty : (pure_integer_points P).Nonempty :=
    (pureIntegerHull_nonempty_iff_pureIntegerPoints_nonempty P).1 ⟨x, hx⟩
  rcases hPoints_nonempty with ⟨y, hyP, hyInt⟩
  exact h_no_affine_integer ⟨y, ⟨subset_affineSpan ℝ P hyP, hyInt⟩⟩

/-- Helper for Theorem 5.18: if `aff(P)` contains no integer point, then one Chvátal step already
cuts the whole rational polyhedron away. -/
lemma pureIntegerChvatalClosure_eq_empty_of_noAffineIntegerPoint
    (P : Set (Fin n → ℝ))
    (_hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_no_affine_integer :
      ¬ ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty) :
    pure_integer_chvatal_closure P = ∅ := by
  classical
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  let B : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let br : Fin m → ℝ := fun i ↦ (b i : ℝ)
  let Ieq : Set (Fin m) := implicit_equality_indices B br
  let IeqRows := {i : Fin m // i ∈ Ieq}
  let e : Fin (Fintype.card IeqRows) ≃ IeqRows := (Fintype.equivFin IeqRows).symm
  let AeqQ : Matrix (Fin (Fintype.card IeqRows)) (Fin n) ℚ := fun i j ↦ A (e i).1 j
  let beqQ : Fin (Fintype.card IeqRows) → ℚ := fun i ↦ b (e i).1
  have h_no_integer_solution :
      ¬ RationalLinearSystem.hasIntegerSolution AeqQ beqQ := by
    intro hHas
    rcases (RationalLinearSystem.hasIntegerSolution_iff AeqQ beqQ).1 hHas with ⟨xInt, hxyQ⟩
    have hxy :
        (AeqQ.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (xInt j : ℝ)) =
          fun i ↦ (beqQ i : ℝ) := by
      funext i
      simp [Matrix.mulVec, dotProduct]
      exact_mod_cast congrArg (fun f ↦ f i) hxyQ
    have hxEq :
        implicit_equality_matrix B br *ᵥ (fun j ↦ (xInt j : ℝ)) =
          implicit_equality_rhs B br := by
      funext i
      have hi := congrFun hxy (e.symm i)
      simpa [AeqQ, beqQ, B, br, IeqRows, e, Matrix.mulVec,
        implicit_equality_matrix, implicit_equality_rhs] using hi
    have hxAff :
        (fun j ↦ (xInt j : ℝ)) ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) := by
      rw [hP_eq]
      rw [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set B br]
      exact hxEq
    have hxInt :
        (fun j ↦ (xInt j : ℝ)) ∈ integerVectors n := by
      rw [mem_integerVectors_iff_forall]
      intro j
      exact ⟨xInt j, rfl⟩
    exact h_no_affine_integer ⟨fun j ↦ (xInt j : ℝ), ⟨hxAff, hxInt⟩⟩
  obtain ⟨u, hu_int_mem, hu_rhs_nonint⟩ :=
    (RationalLinearSystem.integerFarkasLemma AeqQ beqQ).1 h_no_integer_solution
  have hu_int :
      ∀ j : Fin n, (u ᵥ* (AeqQ.map (Rat.castHom ℝ))) j ∈ Set.range (Int.cast : ℤ → ℝ) := by
    simpa [mem_integerVectors_iff_forall] using hu_int_mem
  let c : Fin n → ℤ := fun j ↦ Classical.choose (hu_int j)
  have hc_eq :
      u ᵥ* (AeqQ.map (Rat.castHom ℝ)) = fun j ↦ (c j : ℝ) := by
    funext j
    exact (Classical.choose_spec (hu_int j)).symm
  have hvalue_eq :
      ∀ x ∈ P, (fun j ↦ (c j : ℝ)) ⬝ᵥ x = u ⬝ᵥ (fun i ↦ (beqQ i : ℝ)) := by
    intro x hxP
    rw [hP_eq] at hxP
    have hxAff :
        x ∈ (affineSpan ℝ (polyhedron_le_set B br) : Set (Fin n → ℝ)) := by
      exact subset_affineSpan ℝ (polyhedron_le_set B br) hxP
    have hxEq :
        implicit_equality_matrix B br *ᵥ x = implicit_equality_rhs B br := by
      rwa [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set B br] at hxAff
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ x
          = (u ᵥ* (AeqQ.map (Rat.castHom ℝ))) ⬝ᵥ x := by rw [hc_eq]
      _ = u ⬝ᵥ ((AeqQ.map (Rat.castHom ℝ)) *ᵥ x) := by
            rw [Matrix.dotProduct_mulVec]
      _ = u ⬝ᵥ (fun i ↦ (beqQ i : ℝ)) := by
            congr 1
            funext i
            have hi := congrFun hxEq (e i)
            simpa [AeqQ, beqQ, B, br, IeqRows, e, Matrix.mulVec,
              implicit_equality_matrix, implicit_equality_rhs] using hi
  have hvalid :
      is_valid_inequality P (fun j ↦ (c j : ℝ)) (u ⬝ᵥ (fun i ↦ (beqQ i : ℝ))) := by
    intro x hxP
    -- The implicit-equality multiplier turns the whole polyhedron into one equality slice.
    exact le_of_eq (hvalue_eq x hxP)
  have hfloor_lt :
      ((Int.floor (u ⬝ᵥ fun i ↦ (beqQ i : ℝ)) : ℤ) : ℝ) <
        u ⬝ᵥ (fun i ↦ (beqQ i : ℝ)) := by
    simpa using (Int.floor_lt_self_iff.2 hu_rhs_nonint)
  ext x
  rw [mem_pure_integer_chvatal_closure_iff]
  constructor
  · intro hx
    have hx_eq :
        (fun j ↦ (c j : ℝ)) ⬝ᵥ x = u ⬝ᵥ (fun i ↦ (beqQ i : ℝ)) :=
      hvalue_eq x hx.1
    have hx_cut :=
      hx.2 c (u ⬝ᵥ (fun i ↦ (beqQ i : ℝ))) hvalid
    rw [hx_eq] at hx_cut
    exact (not_le_of_gt hfloor_lt) hx_cut
  · intro hx
    exact False.elim hx

/-- Helper for Theorem 5.18: finitely many rowwise iterate witnesses assemble into one common
iterate contained in the pure-integer hull. -/
lemma iteratePureIntegerChvatalClosure_subset_pureIntegerHull_of_rowwiseWitness
    (Q : Set (Fin n → ℝ))
    {m : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    (hSystem : IsPureIntegerHullIntegralSystem Q A b)
    (hRowWitness :
      ∀ i : Fin m,
        ∃ t : ℕ,
          is_valid_inequality
            ((pure_integer_chvatal_closure^[t]) Q)
            (fun j ↦ (A i j : ℝ))
            ((b i : ℤ) : ℝ)) :
    ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q ⊆ pure_integer_hull Q := by
  classical
  choose rowTime hrowValid using hRowWitness
  let T : ℕ := Finset.univ.sup rowTime
  refine ⟨T, ?_⟩
  intro x hx
  rw [hSystem.hull_eq]
  refine ⟨?_, ?_⟩
  · rw [mem_polyhedron_le_set_iff]
    intro i
    have hi_le : rowTime i ≤ T := by
      exact Finset.le_sup (Finset.mem_univ i)
    -- Route correction: use one monotonicity helper instead of repeating `iterate_add` transport
    -- inside the main theorem for every hull row.
    have hxEarlier : x ∈ (pure_integer_chvatal_closure^[rowTime i]) Q :=
      mem_iteratePureIntegerChvatalClosure_of_le Q hi_le hx
    exact hrowValid i hxEarlier
  · exact subset_affineSpan ℝ Q (iteratePureIntegerChvatalClosure_subset Q T hx)

/-- Helper for Theorem 5.18: the nonpositive attainment step is the source proof's strong
dimension induction. -/
theorem existsIterateEqPureIntegerHull_aux
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) P = pure_integer_hull P := by
  classical
  have hDimInd :
      ∀ d : ℕ, ∀ Q : Set (Fin n → ℝ),
        is_rational_polyhedron Q →
        polyhedronDim Q = d →
        ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro Q hQ_rational hQ_dim
        by_cases hQ_empty : Q = ∅
        · refine ⟨0, ?_⟩
          rw [hQ_empty]
          ext x
          simp [pure_integer_hull, pure_integer_points]
        · have hQ_nonempty : Q.Nonempty := Set.nonempty_iff_ne_empty.mpr hQ_empty
          by_cases h_affine_integer :
              ((affineSpan ℝ Q : Set (Fin n → ℝ)) ∩ integerVectors n).Nonempty
          · obtain ⟨m, A, b, hSystem⟩ :=
              exists_integral_matrix_system_for_pure_integer_hull
                Q hQ_nonempty hQ_rational h_affine_integer
            -- Route correction: package the rowwise descent times behind one supremum witness so
            -- the main induction no longer normalizes `Function.iterate_add_apply` at each row.
            have hRowWitness :
                ∀ i : Fin m,
                  ∃ t : ℕ,
                    is_valid_inequality
                      ((pure_integer_chvatal_closure^[t]) Q)
                      (fun j ↦ (A i j : ℝ))
                      ((b i : ℤ) : ℝ) :=
              existsIterateValidInequality_of_integralHullRow
                d
                (fun d' hd' ↦ ih d' hd')
                Q
                hQ_rational
                hQ_dim
                hSystem
            obtain ⟨T, hSubsetHull⟩ :=
              iteratePureIntegerChvatalClosure_subset_pureIntegerHull_of_rowwiseWitness
                Q hSystem hRowWitness
            refine ⟨T, Set.Subset.antisymm hSubsetHull (pureIntegerHull_subset_iterate Q hQ_rational T)⟩
          · have hClosureEmpty :
                pure_integer_chvatal_closure Q = ∅ :=
              pureIntegerChvatalClosure_eq_empty_of_noAffineIntegerPoint
                Q hQ_nonempty hQ_rational h_affine_integer
            have hHullEmpty : pure_integer_hull Q = ∅ :=
              pureIntegerHull_eq_empty_of_noAffineIntegerPoint Q h_affine_integer
            refine ⟨1, ?_⟩
            simpa [Function.iterate_succ_apply', hClosureEmpty, hHullEmpty]
  exact hDimInd (polyhedronDim P) P hP_rational rfl

/-- Theorem 5.18. Let `P` be a rational polyhedron. Then there exists a positive integer `t`
such that `P^(t) = P_I`, represented here by
`(pure_integer_chvatal_closure^[t]) P = pure_integer_hull P`. -/
theorem exists_positive_iterate_chvatalClosure_eq_pure_integer_hull
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ t : ℕ, 0 < t ∧ (pure_integer_chvatal_closure^[t]) P = pure_integer_hull P := by
  obtain ⟨T, hT⟩ := existsIterateEqPureIntegerHull_aux P hP_rational
  -- Shift the nonnegative witness by one step, which fixes the already attained integer hull.
  refine ⟨T + 1, Nat.succ_pos _, ?_⟩
  simpa [Function.iterate_succ_apply', hT, pureIntegerChvatalClosure_pureIntegerHull_eq P]

/-- Helper for Theorem 5.18: once some iterate of `closure` reaches `pure_integer_hull P`, there
is a minimal iterate with that property, hence an `is_iterate_rank_of_polyhedron` witness. -/
lemma existsIterateRankOfExistsEqIntegerHull
    {closure : Set (Fin n → ℝ) → Set (Fin n → ℝ)}
    {P : Set (Fin n → ℝ)}
    (hWitness : ∃ t : ℕ, (closure^[t]) P = pure_integer_hull P) :
    ∃ t : ℕ, is_iterate_rank_of_polyhedron closure P t := by
  classical
  -- Minimize among the iterates that already attain the integer hull.
  refine ⟨Nat.find hWitness, ?_⟩
  rw [is_iterate_rank_of_polyhedron_iff]
  refine ⟨Nat.find_spec hWitness, ?_⟩
  intro j hj
  intro hj_eq
  exact Nat.not_le_of_gt hj (Nat.find_min' hWitness hj_eq)

/-- Companion canonical form of Theorem 5.18. A rational polyhedron has a minimal iterate index
at which the pure-integer Chvátal closure reaches `P_I`; the Chapter 5 owner for that minimal
attainment is `is_iterate_rank_of_polyhedron`. -/
theorem exists_chvatal_rank_of_rational_polyhedron
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ t : ℕ, is_iterate_rank_of_polyhedron pure_integer_chvatal_closure P t := by
  -- First use Theorem 5.18 to obtain some iterate reaching the integer hull.
  obtain ⟨t, _, ht_eq⟩ :=
    exists_positive_iterate_chvatalClosure_eq_pure_integer_hull P hP_rational
  -- Then minimize the attaining iterate to package the canonical rank owner.
  exact
    existsIterateRankOfExistsEqIntegerHull
      (closure := pure_integer_chvatal_closure)
      (P := P)
      ⟨t, ht_eq⟩

end Theorem518
