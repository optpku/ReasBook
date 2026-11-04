/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.LinearSystem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_theorem_3_35
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1.Polyhedron

section Theorem338

open scoped BigOperators Matrix

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean: evaluation of a polynomial
with natural coefficients is monotone. -/
private lemma polynomialNatEval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  -- Split into constants, sums, and positive-degree monomials.
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c a b hab
    -- A constant polynomial takes the same value at both inputs.
    simp
  · intro q r hq hr a b hab
    -- Addition preserves the two induction inequalities.
    simpa only [Polynomial.eval_add] using Nat.add_le_add (hq hab) (hr hab)
  · intro k c _ a b hab
    -- Powers preserve order, and multiplication by the coefficient preserves it again.
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab (k + 1))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean: an entrywise bound controls
the encoding size of a finite rational linear system. -/
private lemma rationalLinearSystemEncodingSize_le_entryBound
    {m n K : ℕ} (B : Matrix (Fin m) (Fin n) ℚ) (c : Fin m → ℚ)
    (hB : ∀ i j, EncodingSize.rational (B i j) ≤ K)
    (hc : ∀ i, EncodingSize.rational (c i) ≤ K) :
    rational_linear_system_encoding_size B c ≤ (m * n + m) * K := by
  -- Bound each of the two finite sums independently, then count their entries.
  have hmatrix : rational_matrix_encoding_size B ≤ m * n * K := by
    rw [rational_matrix_encoding_size]
    simp only [EncodingSize.rationalVector_eq_sum]
    calc
      ∑ i : Fin m, ∑ j : Fin n, EncodingSize.rational (B i j) ≤
          ∑ _i : Fin m, ∑ _j : Fin n, K := by
            exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hB i j
      _ = m * n * K := by simp [Nat.mul_assoc]
  have hvector : EncodingSize.rationalVector c ≤ m * K := by
    rw [EncodingSize.rationalVector_eq_sum]
    calc
      ∑ i : Fin m, EncodingSize.rational (c i) ≤ ∑ _i : Fin m, K := by
        exact Finset.sum_le_sum fun i _ ↦ hc i
      _ = m * K := by simp
  rw [rational_linear_system_encoding_size]
  calc
    rational_matrix_encoding_size B + EncodingSize.rationalVector c ≤
        m * n * K + m * K := Nat.add_le_add hmatrix hvector
    _ = (m * n + m) * K := by rw [Nat.add_mul]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean: a set carrying an extreme
singleton ray has trivial lineality space. -/
private lemma isPointed_of_isExtremeRayOfCone
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} {r : E} (hr : IsExtremeRayOfCone C r) :
    is_pointed C := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro z hz
  have hedge := (isExtremeRayOfCone_iff.mp hr).isExtreme
  have hzero_ray : (0 : E) ∈ (PointedCone.hull ℝ ({r} : Set E) : Set E) := by
    exact (PointedCone.hull ℝ ({r} : Set E)).zero_mem
  have hzero_C : (0 : E) ∈ C := hedge.subset hzero_ray
  have hz_C : z ∈ C := by
    have := (mem_linealitySpace_iff.mp hz) hzero_C (1 : ℝ)
    simpa using this
  have hnegz_C : -z ∈ C := by
    have := (mem_linealitySpace_iff.mp hz) hzero_C (-1 : ℝ)
    simpa using this
  have hzero_segment : (0 : E) ∈ openSegment ℝ (-z) z := by
    simpa using (mem_openSegment_sub_add (0 : E) z)
  have hz_ray := hedge.right_mem_of_mem_openSegment hnegz_C hz_C hzero_ray hzero_segment
  have hnegz_ray := hedge.left_mem_of_mem_openSegment hnegz_C hz_C hzero_ray hzero_segment
  rcases mem_singletonRayHull_iff.mp hz_ray with ⟨a, ha, hza⟩
  rcases mem_singletonRayHull_iff.mp hnegz_ray with ⟨c, hc, hnegzc⟩
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr
  have hac : a + c = 0 := by
    have hsmul : (a + c) • r = 0 := by
      calc
        (a + c) • r = z + -z := by rw [add_smul, ← hza, ← hnegzc]
        _ = 0 := add_neg_cancel z
    exact (smul_eq_zero.mp hsmul).resolve_right hr_ne
  have ha_zero : a = 0 := by
    linarith
  simpa [ha_zero] using hza

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean: an extreme ray of a
recession cone forces the underlying set to be nonempty. -/
private lemma nonempty_of_isExtremeRayOfRecessionCone
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {r : E} (hr : IsExtremeRayOfCone (recessionCone P) r) :
    P.Nonempty := by
  by_contra hP
  have hr_lineality : r ∈ linealitySpace (recessionCone P) := by
    rw [mem_linealitySpace_iff]
    intro z hz a
    rw [mem_recessionCone_iff]
    intro x hx
    exact False.elim (hP ⟨x, hx⟩)
  have hr_zero :=
    (is_pointed_iff_eq_zero_of_mem_linealitySpace.mp
      (isPointed_of_isExtremeRayOfCone hr)) r hr_lineality
  exact extremeRay_ne_zero hr hr_zero

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean: adjoining a row that does
not annihilate a vector to independent rows that do annihilate it preserves independence. -/
private lemma linearIndependent_finCons_of_dotProduct_ne_zero
    {k : ℕ} {rows : Fin k → Fin (k + 1) → ℝ} {u x : Fin (k + 1) → ℝ}
    (hrows : LinearIndependent ℝ rows)
    (hrows_zero : ∀ i, rows i ⬝ᵥ x = 0)
    (hu : u ⬝ᵥ x ≠ 0) :
    LinearIndependent ℝ (Fin.cons u rows) := by
  refine hrows.finCons ?_
  intro hu_span
  have hu_zero : u ⬝ᵥ x = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu_span
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hrows_zero i
    · simp
    · intro y z _ _ hy hz
      simp [add_dotProduct, hy, hz]
    · intro a y _ hy
      simp [smul_dotProduct, hy]
  exact hu hu_zero

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap03/section_3_13/ch3_sec3_13_theorem_3_38.lean.

Theorem 3.38 (1). For a rational polyhedron
`P = rational_matrix_polyhedron A b` whose coefficients have encoding size at most `L`, every
vertex `x ∈ P.extremePoints ℝ` has a rational coordinate vector whose encoding size is bounded by
a uniform polynomial in `n + L`.

The source states this for pointed polyhedra; that hypothesis is redundant for the vertex bound,
so the public API omits it. -/
theorem rational_vertices_have_polynomially_bounded_encoding_size
    : ∃ π : Polynomial ℕ,
        ∀ {m n : ℕ}
          (A : Matrix (Fin m) (Fin n) ℚ)
          (b : Fin m → ℚ)
          (L : ℕ)
          (_hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
          (_hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
          (x : Fin n → ℝ),
          x ∈ (rational_matrix_polyhedron A b).extremePoints ℝ →
            ∃ v : Fin n → ℚ,
              x = (fun k ↦ (v k : ℝ)) ∧
                EncodingSize.rationalVector v ≤ π.eval (n + L) := by
  obtain ⟨p, hp⟩ := square_rational_linear_system_has_small_rational_solution
  refine ⟨p.comp ((Polynomial.X + 3) ^ 3), ?_⟩
  intro m n A b L hA hb x hx
  -- A vertex supplies a square subsystem of active, linearly independent rows.
  have hx_mem : x ∈ rational_matrix_polyhedron A b :=
    (mem_extremePoints_iff_left.mp hx).1
  obtain ⟨I, hI_active, hI_independent⟩ :=
    (mem_extremePoints_iff_exists_active_linearlyIndependent_rows
      (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hx_mem).mp hx
  let B : Matrix (Fin n) (Fin n) ℚ := fun i j ↦ A (I i) j
  let c : Fin n → ℚ := fun i ↦ b (I i)
  have hx_system : (B.map (Rat.castHom ℝ)).mulVec x = fun i ↦ (c i : ℝ) := by
    funext i
    simpa [B, c, Matrix.mulVec] using hI_active i
  obtain ⟨v, hv_system, hv_size⟩ := hp n B c ⟨x, hx_system⟩
  have hB_independent : LinearIndependent ℝ (B.map (Rat.castHom ℝ)).row := by
    simpa [B, Matrix.row] using hI_independent
  have hB_injective : Function.Injective (B.map (Rat.castHom ℝ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.linearIndependent_rows_iff_isUnit.mp hB_independent)
  have hv_system_real :
      (B.map (Rat.castHom ℝ)).mulVec (fun j ↦ (v j : ℝ)) = fun i ↦ (c i : ℝ) := by
    funext i
    calc
      ((B.map (Rat.castHom ℝ)).mulVec (fun j ↦ (v j : ℝ))) i =
          ((B.mulVec v) i : ℝ) := (RingHom.map_mulVec (Rat.castHom ℝ) B v i).symm
      _ = (c i : ℝ) := by rw [hv_system]
  have hx_eq : x = fun j ↦ (v j : ℝ) :=
    hB_injective (hx_system.trans hv_system_real.symm)
  -- Count the selected coefficients, then dominate that count by one cubic in `n + L`.
  have hsystem_size : rational_linear_system_encoding_size B c ≤ (n + L + 3) ^ 3 := by
    have hB_entries : ∀ i j, EncodingSize.rational (B i j) ≤ L := by
      intro i j
      simpa [B] using hA (I i) j
    have hc_entries : ∀ i, EncodingSize.rational (c i) ≤ L := by
      intro i
      simpa [c] using hb (I i)
    have hentries : rational_linear_system_encoding_size B c ≤ (n * n + n) * L :=
      rationalLinearSystemEncodingSize_le_entryBound B c hB_entries hc_entries
    have hn : n ≤ n + L + 3 := by omega
    have hn1 : n + 1 ≤ n + L + 3 := by omega
    have hL : L ≤ n + L + 3 := by omega
    calc
      rational_linear_system_encoding_size B c ≤ (n * n + n) * L := hentries
      _ = n * (n + 1) * L := by ring
      _ ≤ (n + L + 3) * (n + L + 3) * (n + L + 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul hn hn1) hL
      _ = (n + L + 3) ^ 3 := by ring
  refine ⟨v, hx_eq, hv_size.trans ?_⟩
  calc
    p.eval (rational_linear_system_encoding_size B c) ≤ p.eval ((n + L + 3) ^ 3) :=
      polynomialNatEval_monotone p hsystem_size
    _ = (p.comp ((Polynomial.X + 3) ^ 3)).eval (n + L) := by
      simp [Polynomial.eval_comp]

/-- Theorem 3.38 (2). For a rational polyhedron
`P = rational_matrix_polyhedron A b` whose coefficients have encoding size at most `L`, every
extreme ray generator `r` admits a positive real rescaling whose rational coordinates have
encoding size bounded by a uniform polynomial in `n + L`.

The source states this for pointed polyhedra; that hypothesis is redundant for the encoding bound
on an already chosen extreme ray, so the public API omits it. -/
theorem rational_extreme_rays_have_polynomially_bounded_rescaled_encoding_size
    : ∃ π : Polynomial ℕ,
        ∀ {m n : ℕ}
          (A : Matrix (Fin m) (Fin n) ℚ)
          (b : Fin m → ℚ)
          (L : ℕ)
          (_hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
          (_hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
          (r : Fin n → ℝ),
          IsExtremeRayOfPolyhedron (rational_matrix_polyhedron A b) r →
            ∃ t : ℝ, 0 < t ∧
              ∃ r' : Fin n → ℚ,
                (fun k ↦ (r' k : ℝ)) = t • r ∧
                  EncodingSize.rationalVector r' ≤ π.eval (n + L) := by
  classical
  obtain ⟨p, hp⟩ := square_rational_linear_system_has_small_rational_solution
  refine ⟨p.comp ((Polynomial.X + 3) ^ 3), ?_⟩
  intro m n A b L hA _hb r hr
  -- Identify the recession cone with the homogeneous rational matrix cone.
  have hP_nonempty : (rational_matrix_polyhedron A b).Nonempty :=
    nonempty_of_isExtremeRayOfRecessionCone (isExtremeRayOfPolyhedron_iff.mp hr)
  have hrecession :
      recessionCone (rational_matrix_polyhedron A b) =
        matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
    simpa [rational_matrix_polyhedron, matrix_polyhedral_cone] using
      polyhedron_recessionCone_eq_homogeneous_solution_set
        (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hP_nonempty
  have hr_cone : IsExtremeRayOfCone (matrix_polyhedral_cone (A.map (Rat.castHom ℝ))) r := by
    rw [← hrecession]
    exact isExtremeRayOfPolyhedron_iff.mp hr
  have hr_ne : r ≠ 0 := extremeRay_ne_zero hr_cone
  have hr_mem : r ∈ matrix_polyhedral_cone (A.map (Rat.castHom ℝ)) := by
    have hr_generator : r ∈ ({r} : Set (Fin n → ℝ)) := Set.mem_singleton r
    have hr_ray :
        r ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
      PointedCone.subset_hull hr_generator
    exact (isExtremeRayOfCone_iff.mp hr_cone).isExtreme.subset
      hr_ray
  have hcone_pointed : is_pointed (matrix_polyhedral_cone (A.map (Rat.castHom ℝ))) :=
    isPointed_of_isExtremeRayOfCone hr_cone
  obtain ⟨I, hI_active, hI_independent⟩ :=
    (matrix_polyhedral_cone_extreme_ray_iff_exists_active_linearlyIndependent_rows
      (A.map (Rat.castHom ℝ)) hcone_pointed hr_mem hr_ne).mp hr_cone
  cases n with
  | zero =>
      exact (hr_ne (Subsingleton.elim r 0)).elim
  | succ k =>
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hr_ne
      have hj_ne : r j ≠ 0 := hj
      let ε : ℚ := if 0 < r j then 1 else -1
      let t : ℝ := if 0 < r j then (r j)⁻¹ else -(r j)⁻¹
      have ht_pos : 0 < t := by
        by_cases hj_pos : 0 < r j
        · simp only [t, if_pos hj_pos]
          exact inv_pos.mpr hj_pos
        · have hj_neg : r j < 0 := lt_of_le_of_ne (le_of_not_gt hj_pos) hj_ne
          simpa [t, hj_pos] using neg_pos.mpr (inv_neg''.mpr hj_neg)
      have ht_coord : t * r j = (ε : ℝ) := by
        by_cases hj_pos : 0 < r j
        · simp [t, ε, hj_pos, hj_ne]
        · simp [t, ε, hj_pos, hj_ne]
      let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
        Fin.cons (Pi.single j 1) (fun i l ↦ A (I i) l)
      let c : Fin (k + 1) → ℚ := Fin.cons ε (fun _ ↦ 0)
      have hhead_dot : (Pi.single j (1 : ℝ)) ⬝ᵥ r = r j := by
        rw [dotProduct, Finset.sum_eq_single j]
        · simp
        · intro l _ hlj
          simp [hlj]
        · simp
      have htail_zero :
          ∀ i : Fin k, (fun l ↦ (A (I i) l : ℝ)) ⬝ᵥ r = 0 := by
        intro i
        simpa [Matrix.mulVec] using hI_active i
      have hhead_ne : (Pi.single j (1 : ℝ)) ⬝ᵥ r ≠ 0 := by
        rw [hhead_dot]
        exact hj_ne
      have hreal_rows_independent :
          LinearIndependent ℝ
            (Fin.cons (Pi.single j (1 : ℝ)) (fun i l ↦ (A (I i) l : ℝ))) := by
        exact linearIndependent_finCons_of_dotProduct_ne_zero hI_independent htail_zero
          hhead_ne
      have hB_cast :
          B.map (Rat.castHom ℝ) =
            Fin.cons (Pi.single j (1 : ℝ)) (fun i l ↦ (A (I i) l : ℝ)) := by
        ext i l
        refine Fin.cases ?_ (fun _ ↦ ?_) i
        · by_cases hlj : l = j
          · simp [B, hlj]
          · simp [B, hlj]
        · simp [B]
      have hB_independent : LinearIndependent ℝ (B.map (Rat.castHom ℝ)).row := by
        rw [hB_cast]
        exact hreal_rows_independent
      have hB_zero : (B.map (Rat.castHom ℝ)) 0 = Pi.single j (1 : ℝ) := by
        simpa using congrFun hB_cast 0
      have hB_succ :
          ∀ i : Fin k, (B.map (Rat.castHom ℝ)) i.succ = fun l ↦ (A (I i) l : ℝ) := by
        intro i
        simpa using congrFun hB_cast i.succ
      have hB_injective : Function.Injective (B.map (Rat.castHom ℝ)).mulVec :=
        Matrix.mulVec_injective_iff_isUnit.mpr
          (Matrix.linearIndependent_rows_iff_isUnit.mp hB_independent)
      have hscaled_system :
          (B.map (Rat.castHom ℝ)).mulVec (t • r) = fun i ↦ (c i : ℝ) := by
        funext i
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · rw [Matrix.mulVec, hB_zero]
          simp only [dotProduct_smul, smul_eq_mul]
          rw [hhead_dot, ht_coord]
          simp [c]
        · rw [Matrix.mulVec, hB_succ]
          simp only [dotProduct_smul, smul_eq_mul]
          rw [htail_zero]
          simp [c]
      obtain ⟨r', hr'_system, hr'_size⟩ := hp (k + 1) B c ⟨t • r, hscaled_system⟩
      have hr'_system_real :
          (B.map (Rat.castHom ℝ)).mulVec (fun l ↦ (r' l : ℝ)) = fun i ↦ (c i : ℝ) := by
        funext i
        calc
          ((B.map (Rat.castHom ℝ)).mulVec (fun l ↦ (r' l : ℝ))) i =
              ((B.mulVec r') i : ℝ) :=
                (RingHom.map_mulVec (Rat.castHom ℝ) B r' i).symm
          _ = (c i : ℝ) := by rw [hr'_system]
      have hr'_eq : (fun l ↦ (r' l : ℝ)) = t • r :=
        hB_injective (hr'_system_real.trans hscaled_system.symm)
      -- The normalization row has size at most three; all other entries retain the input bound.
      have hB_entries :
          ∀ i l, EncodingSize.rational (B i l) ≤ L + 3 := by
        have hL_le : L ≤ L + 3 := by omega
        intro i l
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · dsimp [B]
          by_cases hlj : l = j
          · simp [hlj, EncodingSize.rational_eq]
          · simp [hlj, EncodingSize.rational_eq]
        · exact (hA (I i) l).trans hL_le
      have hc_entries : ∀ i, EncodingSize.rational (c i) ≤ L + 3 := by
        intro i
        refine Fin.cases ?_ (fun _ ↦ ?_) i
        · dsimp [c, ε]
          split_ifs <;> norm_num [EncodingSize.rational_eq]
        · norm_num [c, EncodingSize.rational_eq]
      have hsystem_size :
          rational_linear_system_encoding_size B c ≤ (k + 1 + L + 3) ^ 3 := by
        have hentries :
            rational_linear_system_encoding_size B c ≤
              ((k + 1) * (k + 1) + (k + 1)) * (L + 3) :=
          rationalLinearSystemEncodingSize_le_entryBound B c hB_entries hc_entries
        have hn : k + 1 ≤ k + 1 + L + 3 := by omega
        have hn1 : k + 1 + 1 ≤ k + 1 + L + 3 := by omega
        have hL : L + 3 ≤ k + 1 + L + 3 := by omega
        calc
          rational_linear_system_encoding_size B c ≤
              ((k + 1) * (k + 1) + (k + 1)) * (L + 3) := hentries
          _ = (k + 1) * (k + 1 + 1) * (L + 3) := by ring
          _ ≤ (k + 1 + L + 3) * (k + 1 + L + 3) * (k + 1 + L + 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul hn hn1) hL
          _ = (k + 1 + L + 3) ^ 3 := by ring
      refine ⟨t, ht_pos, r', hr'_eq, hr'_size.trans ?_⟩
      calc
        p.eval (rational_linear_system_encoding_size B c) ≤
            p.eval ((k + 1 + L + 3) ^ 3) := polynomialNatEval_monotone p hsystem_size
        _ = (p.comp ((Polynomial.X + 3) ^ 3)).eval (k + 1 + L) := by
          simp [Polynomial.eval_comp]

end Theorem338

#print axioms rational_vertices_have_polynomially_bounded_encoding_size
#print axioms rational_extreme_rays_have_polynomially_bounded_rescaled_encoding_size
