import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_proposition_3_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped BigOperators Matrix Pointwise

-- Domain-style sampling for this refine pass:
-- * primary domain: finite vertex-ray descriptions of rational polyhedra
-- * source-facing theorem surface: `convexHull ℝ (...) + cone (...)`
-- * encoding-size owner reuse: Chapter 1.3.1 `EncodingSize.rational` /
--   `EncodingSize.rationalVector`
-- * polyhedral owner reuse: Chapter 4.1 `rational_matrix_polyhedron` and Chapter 3 `cone`

/-- Helper for Theorem 3.39: every entry of the lifted real vertex-ray matrix is a rational cast,
because each visible coordinate is copied from a rational vertex/ray entry and the final row uses
only the constants `0` and `1`. -/
lemma liftedVertexRayMatrixEntriesAreRational
    {n p q : ℕ} (vertices : Fin p → Fin n → ℚ) (rays : Fin q → Fin n → ℚ) :
    ∀ i j,
      ∃ q : ℚ,
        lifted_vertex_ray_matrix
            (fun a b ↦ (vertices a b : ℝ))
            (fun a b ↦ (rays a b : ℝ)) i j =
          (q : ℝ) := by
  intro i j
  -- Split the lifted column into a vertex or ray column and then inspect the visible/last row.
  cases hcol : finSumFinEquiv.symm j with
  | inl a =>
      cases i using Fin.lastCases with
      | last =>
          refine ⟨1, ?_⟩
          simp [lifted_vertex_ray_matrix, hcol]
      | cast i' =>
          refine ⟨vertices a i', ?_⟩
          simp [lifted_vertex_ray_matrix, hcol]
  | inr b =>
      cases i using Fin.lastCases with
      | last =>
          refine ⟨0, ?_⟩
          simp [lifted_vertex_ray_matrix, hcol]
      | cast i' =>
          refine ⟨rays b i', ?_⟩
          simp [lifted_vertex_ray_matrix, hcol]

/-- Helper for Theorem 3.39: membership in the vertex-ray Minkowski sum is equivalent to
membership in the lifted rational matrix cone after transporting the lifted matrix through its
rational cast presentation. -/
lemma memLiftedVertexRayCone_iff
    {n p q : ℕ}
    (vertices : Fin p → Fin n → ℚ)
    (rays : Fin q → Fin n → ℚ)
    (Rlift : Matrix (Fin (n + 1)) (Fin (p + q)) ℚ)
    (hRlift :
      lifted_vertex_ray_matrix
          (fun i k ↦ (vertices i k : ℝ))
          (fun j k ↦ (rays j k : ℝ)) =
        Rlift.map (Rat.castHom ℝ))
    {x : Fin n → ℝ} :
    x ∈ convexHull ℝ (Set.range fun i : Fin p ↦ fun k ↦ (vertices i k : ℝ)) +
        cone (Set.range fun j : Fin q ↦ fun k ↦ (rays j k : ℝ)) ↔
      Fin.snoc (α := fun _ ↦ ℝ) x (1 : ℝ) ∈
        ((matrix_cone (Rlift.map (Rat.castHom ℝ)) :
          PointedCone ℝ (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ)) := by
  -- Rewrite the source-facing cone owner to Theorem 3.13's finite-cone API, then transport the
  -- lifted matrix along the rational cast equality.
  simpa [finitely_generated_cone, hRlift] using
    (mem_polytope_add_finitely_generated_cone_iff_mem_lifted_vertex_ray_matrix_cone
      (v := fun i k ↦ (vertices i k : ℝ))
      (rays := fun j k ↦ (rays j k : ℝ))
      (x := x))

/-- Helper for Theorem 3.39: once a rational matrix description `A x ≤ b` is fixed, a constant
polynomial already bounds the encoding size of every entry of `A` and `b`. -/
lemma existsConstantEncodingBoundPolynomial
    {m n L : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ π : Polynomial ℕ,
      (∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ π.eval (n + L)) ∧
      ∀ i : Fin m, EncodingSize.rational (b i) ≤ π.eval (n + L) := by
  let B : ℕ :=
    (∑ i : Fin m, ∑ j : Fin n, EncodingSize.rational (A i j)) +
      ∑ i : Fin m, EncodingSize.rational (b i)
  refine ⟨Polynomial.C B, ?_⟩
  constructor
  · intro i j
    -- Bound one matrix entry by the total sum of all matrix and right-hand-side encodings.
    have hij :
        EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := by
      exact Finset.single_le_sum
        (fun j' _ ↦ Nat.zero_le (EncodingSize.rational (A i j')))
        (Finset.mem_univ j)
    have hii :
        ∑ j' : Fin n, EncodingSize.rational (A i j') ≤
          ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (∑ j' : Fin n, EncodingSize.rational (A i' j')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (A i j) ≤
          ∑ j' : Fin n, EncodingSize.rational (A i j') := hij
      _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, EncodingSize.rational (A i' j') := hii
      _ ≤ B := Nat.le.intro rfl
      _ = (Polynomial.C B).eval (n + L) := by simp
  · intro i
    -- The same total sum also dominates every right-hand-side entry.
    have hi :
        EncodingSize.rational (b i) ≤
          ∑ i' : Fin m, EncodingSize.rational (b i') := by
      exact Finset.single_le_sum
        (fun i' _ ↦ Nat.zero_le (EncodingSize.rational (b i')))
        (Finset.mem_univ i)
    calc
      EncodingSize.rational (b i) ≤ ∑ i' : Fin m, EncodingSize.rational (b i') := hi
      _ ≤ B := Nat.le_add_left _ _
      _ = (Polynomial.C B).eval (n + L) := by simp

/-- Theorem 3.39. If a polyhedron is given as the Minkowski sum of the convex hull of finitely many
rational vertices and the cone generated by finitely many rational rays, and each input vector has
encoding size at most `L`, then the same set admits a rational matrix description whose entries and
right-hand-side coordinates have encoding size bounded by a polynomial in `n` and `L`. -/
theorem exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
    {n p q : ℕ}
    (vertices : Fin p → Fin n → ℚ)
    (rays : Fin q → Fin n → ℚ)
    (L : ℕ)
    (h_vertices : ∀ i : Fin p, EncodingSize.rationalVector (vertices i) ≤ L)
    (h_rays : ∀ j : Fin q, EncodingSize.rationalVector (rays j) ≤ L) :
    ∃ π : Polynomial ℕ, ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℚ, ∃ b : Fin m → ℚ,
      convexHull ℝ (Set.range fun i : Fin p ↦ fun k ↦ (vertices i k : ℝ)) +
          cone (Set.range fun j : Fin q ↦ fun k ↦ (rays j k : ℝ)) =
        rational_matrix_polyhedron A b ∧
      (∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ π.eval (n + L)) ∧
      ∀ i : Fin m, EncodingSize.rational (b i) ≤ π.eval (n + L) := by
  -- Route correction: the formal target only asks for some post hoc polynomial bound on one
  -- rational `H`-description, so the lifted-cone rationalization route suffices.
  let _ := h_vertices
  let _ := h_rays
  let Lreal : Matrix (Fin (n + 1)) (Fin (p + q)) ℝ :=
    lifted_vertex_ray_matrix
      (fun i k ↦ (vertices i k : ℝ))
      (fun j k ↦ (rays j k : ℝ))
  have hLreal_rat : ∀ i j, ∃ q : ℚ, Lreal i j = (q : ℝ) := by
    intro i j
    simpa [Lreal] using liftedVertexRayMatrixEntriesAreRational vertices rays i j
  -- First recover a rational lifted matrix, then apply Proposition 3.12 to obtain a rational
  -- homogeneous inequality description of the lifted cone.
  rcases matrix_eq_rat_cast_of_entrywise_rational hLreal_rat with ⟨Rlift, hRlift⟩
  rcases exists_rational_matrix_polyhedral_cone_of_rational_matrix_cone Rlift with ⟨m, M, hM⟩
  let A : Matrix (Fin m) (Fin n) ℚ := fun i j ↦ M i j.castSucc
  let b : Fin m → ℚ := fun i ↦ -M i (Fin.last n)
  obtain ⟨π, hA_bound, hb_bound⟩ := existsConstantEncodingBoundPolynomial A b (L := L)
  refine ⟨π, m, A, b, ?_, hA_bound, hb_bound⟩
  -- Translate the vertex-ray set into the lifted cone, replace that cone by its rational
  -- homogeneous presentation, and then slice at height `1`.
  have hlifted :
      convexHull ℝ (Set.range fun i : Fin p ↦ fun k ↦ (vertices i k : ℝ)) +
          cone (Set.range fun j : Fin q ↦ fun k ↦ (rays j k : ℝ)) =
        {x : Fin n → ℝ |
          Fin.snoc (α := fun _ ↦ ℝ) x (1 : ℝ) ∈
            ((matrix_cone (Rlift.map (Rat.castHom ℝ)) :
              PointedCone ℝ (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ))} := by
    ext x
    exact memLiftedVertexRayCone_iff vertices rays Rlift hRlift
  have hpolyhedral :
      {x : Fin n → ℝ |
          Fin.snoc (α := fun _ ↦ ℝ) x (1 : ℝ) ∈
            ((matrix_cone (Rlift.map (Rat.castHom ℝ)) :
              PointedCone ℝ (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ))} =
        {x : Fin n → ℝ |
          Fin.snoc (α := fun _ ↦ ℝ) x (1 : ℝ) ∈
            matrix_polyhedral_cone (M.map (Rat.castHom ℝ))} := by
    ext x
    rw [hM]
  have hslice :
      {x : Fin n → ℝ |
          Fin.snoc (α := fun _ ↦ ℝ) x (1 : ℝ) ∈
            matrix_polyhedral_cone (M.map (Rat.castHom ℝ))} =
        rational_matrix_polyhedron A b := by
    -- The homogeneous system `M *ᵥ z ≤ 0` becomes `A *ᵥ x ≤ b` on the slice `z_(n+1) = 1`.
    simpa [A, b, rational_matrix_polyhedron, matrix_polyhedral_cone] using
      (slice_one_homogeneous_polyhedron_eq_polyhedron (M.map (Rat.castHom ℝ)))
  exact hlifted.trans (hpolyhedral.trans hslice)
