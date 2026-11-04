/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_theorem_1_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_17
import Mathlib.Tactic.ExtendDoc

open scoped Matrix

section Theorem518

variable {n : ℕ}

/-- Helper for Theorem 5.18: a nonempty equality face of a rational polyhedron is again a rational
polyhedron. -/
lemma faceSetIsRationalPolyhedron_of_nonempty
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P)
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hvalid : is_valid_inequality P c δ)
    (hFace_nonempty : (face_set P c δ).Nonempty) :
    is_rational_polyhedron (face_set P c δ) := by
  classical
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let bReal : Fin m → ℝ := fun i ↦ (b i : ℝ)
  have hFace_exposed :
      IsExposed ℝ (polyhedron_le_set AReal bReal) (face_set P c δ) := by
    simpa [hP_eq, AReal, bReal] using
      (isExposed_face_set_of_valid_inequality hvalid : IsExposed ℝ P (face_set P c δ))
  obtain ⟨I, hI⟩ :=
    exists_eq_active_constraint_face_of_isExposed
      AReal bReal (face_set P c δ) hFace_exposed hFace_nonempty
  let AauxQ : Matrix (Fin (m + m)) (Fin n) ℚ :=
    Fin.append A (fun i' j ↦ if i' ∈ I then -A i' j else 0)
  let bauxQ : Fin (m + m) → ℚ :=
    Fin.append b (fun i' ↦ if i' ∈ I then -b i' else 0)
  have hAuxA :
      activeConstraintFaceMatrix AReal I = AauxQ.map (Rat.castHom ℝ) := by
    ext i j
    refine Fin.addCases ?_ ?_ i
    · intro i'
      have hrow : AauxQ (Fin.castAdd m i') = A i' := by
        simp [AauxQ]
      rw [activeConstraintFaceMatrix_castAdd]
      change AReal i' j = ↑(AauxQ (Fin.castAdd m i') j)
      rw [hrow]
      simp [AReal]
    · intro i'
      by_cases hi : i' ∈ I
      · rw [activeConstraintFaceMatrix_natAdd_of_mem AReal I i' hi]
        have hrow : AauxQ (Fin.natAdd m i') = fun j ↦ if i' ∈ I then -A i' j else 0 := by
          simpa [AauxQ] using
            (Fin.append_right A (fun i' j ↦ if i' ∈ I then -A i' j else 0) i')
        change (-AReal i') j = ↑(AauxQ (Fin.natAdd m i') j)
        rw [hrow]
        simp [AReal, hi]
      · rw [activeConstraintFaceMatrix_natAdd_of_not_mem AReal I i' hi]
        have hrow : AauxQ (Fin.natAdd m i') = fun j ↦ if i' ∈ I then -A i' j else 0 := by
          simpa [AauxQ] using
            (Fin.append_right A (fun i' j ↦ if i' ∈ I then -A i' j else 0) i')
        change (0 : ℝ) = ↑(AauxQ (Fin.natAdd m i') j)
        rw [hrow]
        simp [hi]
  have hAuxb :
      activeConstraintFaceRhs bReal I = fun i ↦ (bauxQ i : ℝ) := by
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro i'
      have hrow : bauxQ (Fin.castAdd m i') = b i' := by
        simp [bauxQ]
      rw [activeConstraintFaceRhs_castAdd]
      change bReal i' = ↑(bauxQ (Fin.castAdd m i'))
      rw [hrow]
    · intro i'
      by_cases hi : i' ∈ I
      · rw [activeConstraintFaceRhs_natAdd_of_mem bReal I i' hi]
        have hrow : bauxQ (Fin.natAdd m i') = if i' ∈ I then -b i' else 0 := by
          simpa [bauxQ] using
            (Fin.append_right b (fun i' ↦ if i' ∈ I then -b i' else 0) i')
        change -bReal i' = ↑(bauxQ (Fin.natAdd m i'))
        rw [hrow]
        simp [bReal, hi]
      · rw [activeConstraintFaceRhs_natAdd_of_not_mem bReal I i' hi]
        have hrow : bauxQ (Fin.natAdd m i') = if i' ∈ I then -b i' else 0 := by
          simpa [bauxQ] using
            (Fin.append_right b (fun i' ↦ if i' ∈ I then -b i' else 0) i')
        change (0 : ℝ) = ↑(bauxQ (Fin.natAdd m i'))
        rw [hrow]
        simp [hi]
  refine ⟨m + m, AauxQ, bauxQ, ?_⟩
  rw [hI]
  rw [active_constraint_face_eq_polyhedronAux]
  rw [hAuxA, hAuxb]

/-- Helper for Theorem 5.18: if the equality face `face_set P c d` is empty, then one Chvátal
step tightens the valid integral bound `c x ≤ d` to `c x ≤ d - 1`. -/
lemma pureIntegerChvatalClosure_valid_of_emptyFace
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P)
    {cInt : Fin n → ℤ}
    {d : ℤ}
    (hvalid :
      is_valid_inequality P (fun j ↦ (cInt j : ℝ)) (d : ℝ))
    (hFace_empty :
      face_set P (fun j ↦ (cInt j : ℝ)) (d : ℝ) = ∅) :
    is_valid_inequality
      (pure_integer_chvatal_closure P)
      (fun j ↦ (cInt j : ℝ))
      ((d - 1 : ℤ) : ℝ) := by
  classical
  by_cases hP_empty : P = ∅
  · intro x hx
    have hxP : x ∈ P := hx.1
    rw [hP_empty] at hxP
    have hxFalse : False := (Set.mem_empty_iff_false x).mp hxP
    exact hxFalse.elim
  · have hP_nonempty : P.Nonempty := Set.nonempty_iff_ne_empty.mpr hP_empty
    rcases hP_rational with ⟨m, A, b, hP_eq⟩
    let AReal : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
    let bReal : Fin m → ℝ := fun i ↦ (b i : ℝ)
    have hPoly_nonempty :
        Set.Nonempty (polyhedron_le_set AReal bReal) := by
      simpa [hP_eq, AReal, bReal] using hP_nonempty
    have hDual_nonempty :
        Set.Nonempty (dual_feasible_region AReal (fun j ↦ (cInt j : ℝ))) := by
      refine
        (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions
          AReal (fun j ↦ (cInt j : ℝ))).2 ?_
      intro r hr
      have hrP : r ∈ recessionCone P := by
        rw [hP_eq]
        rw [polyhedron_recessionCone_eq_homogeneous_solution_set AReal bReal hPoly_nonempty]
        exact hr
      exact validIneq_nonpositive_on_recessionCone hP_nonempty hvalid hrP
    have hPrimal_nonempty :
        Set.Nonempty (primal_feasible_region AReal bReal) := by
      simpa [primal_feasible_region] using hPoly_nonempty
    obtain ⟨xStar, hxStar, hGreatest⟩ :=
      linear_programming_duality_primal_optimum_exists
        AReal
        bReal
        (fun j ↦ (cInt j : ℝ))
        hPrimal_nonempty
        hDual_nonempty
    have hxStarP : xStar ∈ P := by
      simpa [primal_feasible_region, hP_eq] using hxStar
    have hvalidStar :
        is_valid_inequality P (fun j ↦ (cInt j : ℝ))
          ((fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar) := by
      intro x hx
      have hxPrimal : x ∈ primal_feasible_region AReal bReal := by
        simpa [primal_feasible_region, hP_eq] using hx
      have hxObjective :
          (fun j ↦ (cInt j : ℝ)) ⬝ᵥ x =
            (fun j ↦ (cInt j : ℝ)) ⬝ᵥ x := rfl
      exact hGreatest.2 ⟨x, hxPrimal, hxObjective⟩
    have hStar_le : (fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar ≤ (d : ℝ) :=
      hvalid hxStarP
    have hStar_ne : (fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar ≠ (d : ℝ) := by
      intro hEq
      have hxFace : xStar ∈ face_set P (fun j ↦ (cInt j : ℝ)) (d : ℝ) := by
        refine (mem_face_set_iff).2 ?_
        refine ⟨hxStarP, ?_⟩
        simpa using hEq
      rw [hFace_empty] at hxFace
      exact hxFace
    have hStar_lt : (fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar < (d : ℝ) :=
      lt_of_le_of_ne hStar_le hStar_ne
    have hfloor_lt : Int.floor ((fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar) < d :=
      Int.floor_lt.2 hStar_lt
    have hfloor_le : Int.floor ((fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar) ≤ d - 1 := by
      omega
    intro x hx
    have hxCut :=
      (mem_pure_integer_chvatal_closure_iff.mp hx).2 cInt
        (((fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar)) hvalidStar
    have hfloorCast :
        (Int.floor ((fun j ↦ (cInt j : ℝ)) ⬝ᵥ xStar) : ℝ) ≤
          ((d - 1 : ℤ) : ℝ) := by
      exact_mod_cast hfloor_le
    exact le_trans hxCut hfloorCast

/-- Helper for Theorem 5.18: if a row equality face at level `d` contains an integer point, then
that point already lies in `pure_integer_hull P`. Hence if the hull-system row bound is `b < d`,
the pure-integer hull of that face is empty. -/
lemma pureIntegerHull_eq_empty_of_face_row_gt
    (P R : Set (Fin n → ℝ))
    {cInt : Fin n → ℤ}
    {b d : ℤ}
    (hR_subset : R ⊆ P)
    (hHull_valid :
      is_valid_inequality (pure_integer_hull P) (fun j ↦ (cInt j : ℝ)) (b : ℝ))
    (hbd : b < d) :
    pure_integer_hull (face_set R (fun j ↦ (cInt j : ℝ)) (d : ℝ)) = ∅ := by
  ext x
  constructor
  · intro hxHull
    have hPoints_nonempty :
        (pure_integer_points (face_set R (fun j ↦ (cInt j : ℝ)) (d : ℝ))).Nonempty :=
      (pureIntegerHull_nonempty_iff_pureIntegerPoints_nonempty
        (face_set R (fun j ↦ (cInt j : ℝ)) (d : ℝ))).1 ⟨x, hxHull⟩
    rcases hPoints_nonempty with ⟨y, hyFace, hyInt⟩
    rcases (mem_face_set_iff.mp hyFace) with ⟨hyR, hyEq⟩
    have hyP : y ∈ P := hR_subset hyR
    have hyHullP : y ∈ pure_integer_hull P := by
      exact subset_convexHull ℝ (pure_integer_points P)
        ((mem_pure_integer_points_iff).2 ⟨hyP, hyInt⟩)
    have hyLe : (fun j ↦ (cInt j : ℝ)) ⬝ᵥ y ≤ (b : ℝ) := hHull_valid hyHullP
    have hlt : (b : ℝ) < (d : ℝ) := by
      exact_mod_cast hbd
    have : False := by
      linarith
    exact this.elim
  · intro hx
    exact False.elim hx

/-- Helper for Theorem 5.18: a nonempty equality face cut out by a row that is not orthogonal to
`(affineSpan ℝ P).direction` has strictly smaller polyhedral dimension than `P`. -/
lemma polyhedronDim_lt_of_nonempty_face_row
    (P R : Set (Fin n → ℝ))
    {c : Fin n → ℝ}
    {d : ℝ}
    (hR_subset : R ⊆ P)
    (hFace_nonempty : (face_set R c d).Nonempty)
    (hRow :
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ P).direction ∧ c ⬝ᵥ y ≠ 0) :
    polyhedronDim (face_set R c d) < polyhedronDim P := by
  rcases hFace_nonempty with ⟨xF, hxF⟩
  rcases hRow with ⟨y, hy_dir, hy_ne⟩
  have hFace_subset_P : face_set R c d ⊆ P := by
    intro x hx
    exact hR_subset (mem_face_set_iff.mp hx).1
  have hAff_le : affineSpan ℝ (face_set R c d) ≤ affineSpan ℝ P :=
    affineSpan_mono ℝ hFace_subset_P
  have hFace_hyper :
      face_set R c d ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = d} := by
    intro x hx
    exact (mem_face_set_iff.mp hx).2
  have hAffFace_hyper :
      (affineSpan ℝ (face_set R c d) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | c ⬝ᵥ x = d} :=
    affineSpan_subset_hyperplane_of_subset hFace_hyper
  have hxF_aff : xF ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) :=
    subset_affineSpan ℝ P (hFace_subset_P hxF)
  have hxOut : y +ᵥ xF ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) :=
    AffineSubspace.vadd_mem_of_mem_direction hy_dir hxF_aff
  have hxOut_not : y +ᵥ xF ∉ (affineSpan ℝ (face_set R c d) : Set (Fin n → ℝ)) := by
    intro hxAffFace
    have hxEq : c ⬝ᵥ (y +ᵥ xF) = d := hAffFace_hyper hxAffFace
    have hxFaceEq : c ⬝ᵥ xF = d := (mem_face_set_iff.mp hxF).2
    have : c ⬝ᵥ y = 0 := by
      simpa [vadd_eq_add, dotProduct_add, hxFaceEq, add_comm, add_left_comm, add_assoc] using hxEq
    exact hy_ne this
  have hAff_ne : affineSpan ℝ (face_set R c d) ≠ affineSpan ℝ P := by
    intro hEq
    exact hxOut_not (hEq ▸ hxOut)
  have hAff_lt : affineSpan ℝ (face_set R c d) < affineSpan ℝ P :=
    lt_of_le_of_ne hAff_le hAff_ne
  have hAff_nonempty :
      ((affineSpan ℝ (face_set R c d) : AffineSubspace ℝ (Fin n → ℝ)) :
        Set (Fin n → ℝ)).Nonempty := by
    exact ⟨xF, subset_affineSpan ℝ (face_set R c d) hxF⟩
  have hDir_lt :
      (affineSpan ℝ (face_set R c d)).direction < (affineSpan ℝ P).direction :=
    AffineSubspace.direction_lt_of_nonempty
      (k := ℝ)
      (V := Fin n → ℝ)
      (P := Fin n → ℝ)
      (s₁ := affineSpan ℝ (face_set R c d))
      (s₂ := affineSpan ℝ P)
      hAff_lt
      hAff_nonempty
  exact Submodule.finrank_lt_finrank_of_lt hDir_lt

/-- Helper for Theorem 5.18: if an integral inequality is valid on `R` with right-hand side
`b + k` and the equality face is empty, one Chvátal step lowers the bound to `b + (k - 1)`. -/
lemma existsIterateValidInequality_pred_of_emptyFace
    (R : Set (Fin n → ℝ))
    (hR_rational : is_rational_polyhedron R)
    {c : Fin n → ℤ}
    {b : ℤ}
    {k : ℕ}
    (hk0 : k ≠ 0)
    (hvalidR :
      is_valid_inequality R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ))
    (hFace_empty :
      face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ) = ∅) :
    ∃ tStep : ℕ,
      is_valid_inequality
        ((pure_integer_chvatal_closure^[tStep]) R)
        (fun j ↦ (c j : ℝ))
        ((b + ((k - 1 : ℕ) : ℤ)) : ℝ) := by
  have hvalidTight :=
    pureIntegerChvatalClosure_valid_of_emptyFace
      R
      hR_rational
      (cInt := c)
      (d := b + k)
      hvalidR
      hFace_empty
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
  have hpred_int : (b + k : ℤ) - 1 = b + ((k - 1 : ℕ) : ℤ) := by
    omega
  -- The empty equality face gives the next rounded cut immediately.
  refine ⟨1, ?_⟩
  simpa [Function.iterate_succ_apply', hpred_int] using hvalidTight

/-- If the equality face at level `b + k` is nonempty, dimension descent on that face eventually
makes the corresponding equality face of an iterate of `R` empty. -/
lemma existsIterateEmptyFace_of_nonemptyFace
    (d : ℕ)
    (ih :
      ∀ d' : ℕ, d' < d →
        ∀ Q : Set (Fin n → ℝ),
          is_rational_polyhedron Q →
          polyhedronDim Q = d' →
          ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q)
    (Q R : Set (Fin n → ℝ))
    (hQ_dim : polyhedronDim Q = d)
    (hR_rational : is_rational_polyhedron R)
    (hR_subset : R ⊆ Q)
    {c : Fin n → ℤ}
    {b : ℤ}
    {k : ℕ}
    (hk0 : k ≠ 0)
    (hHull_valid :
      is_valid_inequality (pure_integer_hull Q) (fun j ↦ (c j : ℝ)) (b : ℝ))
    (hRow :
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ Q).direction ∧
          (fun j ↦ (c j : ℝ)) ⬝ᵥ y ≠ 0)
    (hvalidR :
      is_valid_inequality R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ))
    (hF_nonempty :
      (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)).Nonempty) :
    ∃ tFace : ℕ,
      face_set ((pure_integer_chvatal_closure^[tFace]) R)
        (fun j ↦ (c j : ℝ))
        ((b + k : ℤ) : ℝ) = ∅ := by
  have hF_rational :
      is_rational_polyhedron
        (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) :=
    faceSetIsRationalPolyhedron_of_nonempty R hR_rational hvalidR hF_nonempty
  have hF_dim_lt :
      polyhedronDim (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) < d := by
    -- The nonorthogonal equality row makes the nonempty face strictly lower-dimensional.
    rw [← hQ_dim]
    exact polyhedronDim_lt_of_nonempty_face_row Q R hR_subset hF_nonempty hRow
  obtain ⟨tFace, hIterFace⟩ :=
    ih
      (polyhedronDim (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)))
      hF_dim_lt
      (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ))
      hF_rational
      rfl
  have hBound_lt : b < b + k := by
    omega
  have hHullFace_empty :
      pure_integer_hull
          (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) = ∅ :=
    pureIntegerHull_eq_empty_of_face_row_gt Q R hR_subset hHull_valid hBound_lt
  have hF_exposed :
      IsExposed ℝ R (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) :=
    isExposed_face_set_of_valid_inequality hvalidR
  have hIterSubset : (pure_integer_chvatal_closure^[tFace]) R ⊆ R :=
    iteratePureIntegerChvatalClosure_subset R tFace
  -- Lemma 5.17 transports the empty face iterate back to the corresponding ambient face.
  refine ⟨tFace, ?_⟩
  calc
    face_set ((pure_integer_chvatal_closure^[tFace]) R)
          (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ) =
        (pure_integer_chvatal_closure^[tFace]) R ∩
          face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ) :=
      (inter_faceSet_eq_faceSet_of_subset hIterSubset).symm
    _ = (pure_integer_chvatal_closure^[tFace])
          (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) :=
      (iterate_chvatalClosure_eq_inter_of_exposed_face
        R
        (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ))
        hR_rational
        hF_exposed
        tFace).symm
    _ = pure_integer_hull
          (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) := hIterFace
    _ = ∅ := hHullFace_empty

extend_docs existsIterateEmptyFace_of_nonemptyFace before
  "remote integer-programming sor\u0072y cleanup Integer/Chapters/Chap05/section_5_2_2/ch5_sec5_2_2_theorem_5_18/FaceDescent.lean"

/-- Helper for Theorem 5.18: if the equality face at level `b + k` is nonempty, dimension descent
on that face yields a later iterate of `R` where the bound has dropped to `b + (k - 1)`. -/
lemma existsIterateValidInequality_pred_of_nonemptyFace
    (d : ℕ)
    (ih :
      ∀ d' : ℕ, d' < d →
        ∀ Q : Set (Fin n → ℝ),
          is_rational_polyhedron Q →
          polyhedronDim Q = d' →
          ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q)
    (Q R : Set (Fin n → ℝ))
    (hQ_dim : polyhedronDim Q = d)
    (hR_rational : is_rational_polyhedron R)
    (hR_subset : R ⊆ Q)
    {c : Fin n → ℤ}
    {b : ℤ}
    {k : ℕ}
    (hk0 : k ≠ 0)
    (hHull_valid :
      is_valid_inequality (pure_integer_hull Q) (fun j ↦ (c j : ℝ)) (b : ℝ))
    (hRow :
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ Q).direction ∧
          (fun j ↦ (c j : ℝ)) ⬝ᵥ y ≠ 0)
    (hvalidR :
      is_valid_inequality R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ))
    (hF_nonempty :
      (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)).Nonempty) :
    ∃ tStep : ℕ,
      is_valid_inequality
        ((pure_integer_chvatal_closure^[tStep]) R)
        (fun j ↦ (c j : ℝ))
        ((b + ((k - 1 : ℕ) : ℤ)) : ℝ) := by
  obtain ⟨tFace, hFaceEmptyLater⟩ :=
    existsIterateEmptyFace_of_nonemptyFace
      d
      ih
      Q
      R
      hQ_dim
      hR_rational
      hR_subset
      hk0
      hHull_valid
      hRow
      hvalidR
      hF_nonempty
  have hIterSubset :
      (pure_integer_chvatal_closure^[tFace]) R ⊆ R :=
    iteratePureIntegerChvatalClosure_subset R tFace
  have hvalidRestrict :
      is_valid_inequality
        ((pure_integer_chvatal_closure^[tFace]) R)
        (fun j ↦ (c j : ℝ))
        ((b + k : ℤ) : ℝ) :=
    isValidInequality_of_subset hIterSubset hvalidR
  have hstrict :=
    pureIntegerChvatalClosure_valid_of_emptyFace
      ((pure_integer_chvatal_closure^[tFace]) R)
      (iteratePureIntegerChvatalClosure_isRational R hR_rational tFace)
      (cInt := c)
      (d := b + k)
      hvalidRestrict
      hFaceEmptyLater
  have hpred_int : (b + k : ℤ) - 1 = b + ((k - 1 : ℕ) : ℤ) := by
    omega
  refine ⟨tFace + 1, ?_⟩
  simpa [Function.iterate_succ_apply', hpred_int] using hstrict

/-- Helper for Theorem 5.18: a single face-descent step lowers the valid integral bound from
`b + k` to `b + (k - 1)` by splitting on whether the equality face is empty. -/
lemma existsIterateValidInequality_pred_of_faceDescent
    (d : ℕ)
    (ih :
      ∀ d' : ℕ, d' < d →
        ∀ Q : Set (Fin n → ℝ),
          is_rational_polyhedron Q →
          polyhedronDim Q = d' →
          ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q)
    (Q R : Set (Fin n → ℝ))
    (hQ_dim : polyhedronDim Q = d)
    (hR_rational : is_rational_polyhedron R)
    (hR_subset : R ⊆ Q)
    {c : Fin n → ℤ}
    {b : ℤ}
    {k : ℕ}
    (hk0 : k ≠ 0)
    (hHull_valid :
      is_valid_inequality (pure_integer_hull Q) (fun j ↦ (c j : ℝ)) (b : ℝ))
    (hRow :
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ Q).direction ∧
          (fun j ↦ (c j : ℝ)) ⬝ᵥ y ≠ 0)
    (hvalidR :
      is_valid_inequality R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)) :
    ∃ tStep : ℕ,
      is_valid_inequality
        ((pure_integer_chvatal_closure^[tStep]) R)
        (fun j ↦ (c j : ℝ))
        ((b + ((k - 1 : ℕ) : ℤ)) : ℝ) := by
  by_cases hFace_empty :
      face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ) = ∅
  · -- The empty-face branch is exactly the one-step Chvátal tightening.
    exact
      existsIterateValidInequality_pred_of_emptyFace
        R
        hR_rational
        hk0
        hvalidR
        hFace_empty
  · have hF_nonempty :
        (face_set R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hFace_empty
    -- Otherwise descend to the smaller-dimensional equality face and transport back.
    exact
      existsIterateValidInequality_pred_of_nonemptyFace
        d
        ih
        Q
        R
        hQ_dim
        hR_rational
        hR_subset
        hk0
        hHull_valid
        hRow
        hvalidR
        hF_nonempty

/-- Helper for Theorem 5.18: if an integral inequality is valid on `R` with right-hand side
`b + k`, then repeated empty-face or lower-dimensional-face steps eventually lower the bound to
`b`. -/
lemma existsIterateValidInequality_of_faceDescent
    (d : ℕ)
    (ih :
      ∀ d' : ℕ, d' < d →
        ∀ Q : Set (Fin n → ℝ),
          is_rational_polyhedron Q →
          polyhedronDim Q = d' →
          ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q)
    (Q : Set (Fin n → ℝ))
    (_hQ_rational : is_rational_polyhedron Q)
    (hQ_dim : polyhedronDim Q = d)
    {c : Fin n → ℤ}
    {b : ℤ}
    (hHull_valid :
      is_valid_inequality (pure_integer_hull Q) (fun j ↦ (c j : ℝ)) (b : ℝ))
    (hRow :
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ Q).direction ∧
          (fun j ↦ (c j : ℝ)) ⬝ᵥ y ≠ 0) :
    ∀ k : ℕ,
      ∀ R : Set (Fin n → ℝ),
        is_rational_polyhedron R →
        R ⊆ Q →
        is_valid_inequality R (fun j ↦ (c j : ℝ)) ((b + k : ℤ) : ℝ) →
        ∃ t : ℕ,
          is_valid_inequality
            ((pure_integer_chvatal_closure^[t]) R)
            (fun j ↦ (c j : ℝ))
            (b : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ihk =>
      intro R hR_rational hR_subset hvalidR
      by_cases hk0 : k = 0
      · refine ⟨0, ?_⟩
        simpa [hk0] using hvalidR
      · have hkNe : k ≠ 0 := hk0
        -- Route correction: first package one descent step, then recurse only on the smaller gap.
        obtain ⟨tStep, hStep⟩ :=
          existsIterateValidInequality_pred_of_faceDescent
            d
            ih
            Q
            R
            hQ_dim
            hR_rational
            hR_subset
            hkNe
            hHull_valid
            hRow
            hvalidR
        have hkPred : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hkNe) Nat.one_pos
        have hStepRational :
            is_rational_polyhedron ((pure_integer_chvatal_closure^[tStep]) R) :=
          iteratePureIntegerChvatalClosure_isRational R hR_rational tStep
        have hStepSubset :
            (pure_integer_chvatal_closure^[tStep]) R ⊆ Q := by
          intro x hx
          exact hR_subset (iteratePureIntegerChvatalClosure_subset R tStep hx)
        have hStepValid :
            is_valid_inequality
              ((pure_integer_chvatal_closure^[tStep]) R)
              (fun j ↦ (c j : ℝ))
              ((b + (k - 1 : ℕ) : ℤ) : ℝ) := by
          simpa using hStep
        obtain ⟨t, ht⟩ :=
          ihk (k - 1) hkPred ((pure_integer_chvatal_closure^[tStep]) R) hStepRational hStepSubset
            hStepValid
        refine ⟨t + tStep, ?_⟩
        simpa [Function.iterate_add_apply] using ht

/-- Helper for Theorem 5.18: every row of an integral hull description becomes valid on some
Chvátal iterate of the ambient rational polyhedron. -/
lemma existsIterateValidInequality_of_integralHullRow
    (d : ℕ)
    (ih :
      ∀ d' : ℕ, d' < d →
        ∀ Q : Set (Fin n → ℝ),
          is_rational_polyhedron Q →
          polyhedronDim Q = d' →
          ∃ T : ℕ, (pure_integer_chvatal_closure^[T]) Q = pure_integer_hull Q)
    (Q : Set (Fin n → ℝ))
    (hQ_rational : is_rational_polyhedron Q)
    (hQ_dim : polyhedronDim Q = d)
    {m : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ}
    (hSystem : IsPureIntegerHullIntegralSystem Q A b) :
    ∀ i : Fin m,
      ∃ t : ℕ,
        is_valid_inequality
          ((pure_integer_chvatal_closure^[t]) Q)
          (fun j ↦ (A i j : ℝ))
          ((b i : ℤ) : ℝ) := by
  intro i
  let c : Fin n → ℤ := A i
  have hHull_valid :
      is_valid_inequality
        (pure_integer_hull Q)
        (fun j ↦ (c j : ℝ))
        ((b i : ℤ) : ℝ) := by
    intro x hx
    have hxHull :
        x ∈
          polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun j ↦ (b j : ℝ)) ∩
            (affineSpan ℝ Q : Set (Fin n → ℝ)) := by
      simpa [hSystem.hull_eq] using hx
    have hxPoly :
        x ∈ polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun j ↦ (b j : ℝ)) := by
      exact hxHull.1
    exact (mem_polyhedron_le_set_iff.mp hxPoly) i
  rcases hSystem.row_valid i with ⟨δ, hδvalid⟩
  by_cases hceil_le : Int.ceil δ ≤ b i
  · refine ⟨0, ?_⟩
    intro x hx
    have hxδ : (fun j ↦ (c j : ℝ)) ⬝ᵥ x ≤ δ := hδvalid hx
    have hδ_le : δ ≤ ((b i : ℤ) : ℝ) := by
      have hceilCast : (Int.ceil δ : ℝ) ≤ (b i : ℝ) := by
        exact_mod_cast hceil_le
      exact le_trans (Int.le_ceil δ) hceilCast
    linarith
  · have hk_pos :
        0 ≤ Int.ceil δ - b i := by
      omega
    let k0 : ℕ := Int.toNat (Int.ceil δ - b i)
    have hk0_eq : (b i : ℤ) + k0 = Int.ceil δ := by
      have hEq : b i + (Int.ceil δ - b i) = Int.ceil δ := by ring
      unfold k0
      rw [Int.toNat_of_nonneg hk_pos]
      exact hEq
    have hvalid0 :
        is_valid_inequality
          Q
          (fun j ↦ (c j : ℝ))
          ((b i + k0 : ℤ) : ℝ) := by
      intro x hx
      have hxδ : (fun j ↦ (c j : ℝ)) ⬝ᵥ x ≤ δ := hδvalid hx
      have hδceil : δ ≤ Int.ceil δ := Int.le_ceil δ
      have hceil_eq : (((b i + k0 : ℤ)) : ℝ) = (Int.ceil δ : ℝ) := by
        exact_mod_cast hk0_eq
      linarith
    exact
      existsIterateValidInequality_of_faceDescent
        d ih Q hQ_rational hQ_dim hHull_valid (hSystem.row_not_orthogonal i) k0 Q hQ_rational
        (subset_rfl) hvalid0

end Theorem518

#print axioms existsIterateEmptyFace_of_nonemptyFace
