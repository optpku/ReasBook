import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_lemma_5_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_theorem_3_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_corollary_4_31
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_proposition_5_2

open scoped IntegerVectorNotation Matrix Pointwise

section Lemma516

variable {n : ℕ}

/-- An integral matrix system that cuts out `pure_integer_hull P` inside `aff(P)` and whose rows
have the geometric properties required in Lemma 5.16. -/
class IsPureIntegerHullIntegralSystem
    (P : Set (Fin n → ℝ))
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : Prop where
  /-- The casted matrix system defines the pure-integer hull inside `aff(P)`. -/
  hull_eq :
    pure_integer_hull P =
      polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) ∩
        (affineSpan ℝ P : Set (Fin n → ℝ))
  /-- Every defining row is not orthogonal to the direction of `aff(P)`. -/
  row_not_orthogonal :
    ∀ i : Fin m,
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ P).direction ∧
          (fun j : Fin n ↦ (A i j : ℝ)) ⬝ᵥ y ≠ 0
  /-- Every defining row admits some real bound that is valid for `P`. -/
  row_valid :
    ∀ i : Fin m,
      ∃ d : ℝ, is_valid_inequality P (fun j : Fin n ↦ (A i j : ℝ)) d

/-- `IsPureIntegerHullIntegralSystem P A b` unpacks to the defining equality for
`pure_integer_hull P` together with the two rowwise conditions from Lemma 5.16. -/
theorem isPureIntegerHullIntegralSystem_iff
    {P : Set (Fin n → ℝ)}
    {m : ℕ}
    {A : Matrix (Fin m) (Fin n) ℤ}
    {b : Fin m → ℤ} :
    IsPureIntegerHullIntegralSystem P A b ↔
      pure_integer_hull P =
          polyhedron_le_set (A.map (Int.castRingHom ℝ)) (fun i ↦ (b i : ℝ)) ∩
            (affineSpan ℝ P : Set (Fin n → ℝ)) ∧
        (∀ i : Fin m,
          ∃ y : Fin n → ℝ,
            y ∈ (affineSpan ℝ P).direction ∧
              (fun j : Fin n ↦ (A i j : ℝ)) ⬝ᵥ y ≠ 0) ∧
        ∀ i : Fin m,
          ∃ d : ℝ, is_valid_inequality P (fun j : Fin n ↦ (A i j : ℝ)) d := by
  constructor
  · intro h
    exact ⟨h.hull_eq, h.row_not_orthogonal, h.row_valid⟩
  · rintro ⟨hull_eq, row_not_orthogonal, row_valid⟩
    exact ⟨hull_eq, row_not_orthogonal, row_valid⟩

/-- Helper for Lemma 5.16: nonemptiness of `pure_integer_hull P` is equivalent to nonemptiness of
the underlying pure-integer point set. -/
lemma pureIntegerHull_nonempty_iff_pureIntegerPoints_nonempty
    (P : Set (Fin n → ℝ)) :
    (pure_integer_hull P).Nonempty ↔ (pure_integer_points P).Nonempty := by
  -- The pure-integer hull is a convex hull, and convex hulls are nonempty exactly when their
  -- generating set is nonempty.
  rw [pure_integer_hull_eq_convexHull]
  exact convexHull_nonempty_iff

/-- Helper for Lemma 5.16: the pure-integer hull stays inside `aff(P)`. -/
lemma pureIntegerHull_subset_affineSpan
    (P : Set (Fin n → ℝ)) :
    pure_integer_hull P ⊆ (affineSpan ℝ P : Set (Fin n → ℝ)) := by
  rw [pure_integer_hull_eq_convexHull]
  -- The generators already lie in `P`, hence inside `aff(P)`, and convexity closes the hull.
  refine convexHull_min ?_ (show Convex ℝ (affineSpan ℝ P : Set (Fin n → ℝ)) from
    (affineSpan ℝ P).convex)
  intro x hx
  exact subset_affineSpan ℝ P hx.1

/-- Helper for Lemma 5.16: regard `P ⊆ ℝ^n` as a mixed set with no continuous block. -/
def pureAsMixedSet (P : Set (Fin n → ℝ)) : Set (MixedRealPoint n 0) :=
  {xy | xy.1 ∈ P}

/-- Helper for Lemma 5.16: flattening a point with zero continuous block recovers the original
vector. -/
lemma appendEquiv_zeroContinuousBlock
    (x : Fin n → ℝ) :
    Fin.appendEquiv n 0 (x, 0) = x := by
  -- With no continuous coordinates, `Fin.appendEquiv` only sees the integer block.
  ext i
  simpa [Fin.appendEquiv] using Fin.append_left x (0 : Fin 0 → ℝ) i

/-- Helper for Lemma 5.16: flattening any mixed point with zero continuous block recovers its
integer part. -/
lemma appendEquiv_zero_eq_fst
    (xy : MixedRealPoint n 0) :
    Fin.appendEquiv n 0 xy = xy.1 := by
  -- The continuous block has type `Fin 0 → ℝ`, so the flattening map discards it.
  ext i
  simpa [Fin.appendEquiv] using Fin.append_left xy.1 xy.2 i

/-- Helper for Lemma 5.16: flattening `pureAsMixedSet P` gives back `P`. -/
lemma image_pureAsMixedSet_eq
    (P : Set (Fin n → ℝ)) :
    Fin.appendEquiv n 0 '' pureAsMixedSet P = P := by
  ext x
  constructor
  · rintro ⟨xy, hxy, hxy_eq⟩
    -- The flattened image only remembers the first coordinate block.
    rcases xy with ⟨x', y'⟩
    have hx' : x' = x := by
      ext i
      have hi := congrFun hxy_eq i
      calc
        x' i = Fin.append x' y' i := by simpa using (Fin.append_left x' y' i).symm
        _ = x i := hi
    simpa [pureAsMixedSet] using hx' ▸ hxy
  · intro hx
    -- Reinsert the unique zero continuous block to return to the mixed ambient space.
    refine ⟨(x, 0), ?_, appendEquiv_zeroContinuousBlock x⟩
    simpa [pureAsMixedSet] using hx

/-- Helper for Lemma 5.16: the mixed-integer points of `pureAsMixedSet P` flatten to the pure
integer points of `P`. -/
lemma image_mixedIntegerPoints_pureAsMixedSet_eq
    (P : Set (Fin n → ℝ)) :
    Fin.appendEquiv n 0 '' mixed_integer_points (pureAsMixedSet P) = pure_integer_points P := by
  ext x
  constructor
  · rintro ⟨xy, hxy, hxy_eq⟩
    -- Unpack the mixed-integer condition into feasibility in `P` and integrality of `x`.
    rcases xy with ⟨x', y'⟩
    have hx' : x' = x := by
      ext i
      have hi := congrFun hxy_eq i
      calc
        x' i = Fin.append x' y' i := by simpa using (Fin.append_left x' y' i).symm
        _ = x i := hi
    rcases (mem_mixed_integer_points_iff.mp hxy) with ⟨hxyP, hxyInt⟩
    have hxP : x ∈ P := by
      simpa [pureAsMixedSet] using hx' ▸ hxyP
    have hxInt : x ∈ ℤ^n := by
      rw [mem_mixed_integer_lattice_iff] at hxyInt
      simpa [hx'] using hxyInt
    exact (mem_pure_integer_points_iff).2 ⟨hxP, hxInt⟩
  · intro hx
    -- The pure integer point becomes a mixed-integer point with zero continuous block.
    refine ⟨(x, 0), ?_, appendEquiv_zeroContinuousBlock x⟩
    rcases (mem_pure_integer_points_iff.mp hx) with ⟨hxP, hxInt⟩
    refine (mem_mixed_integer_points_iff).2 ?_
    refine ⟨by simpa [pureAsMixedSet] using hxP, ?_⟩
    simpa [mem_mixed_integer_lattice_iff] using hxInt

/-- Helper for Lemma 5.16: Corollary 4.31 specializes to a decomposition of
`pure_integer_points P` as finitely many rational polytope pieces plus one integral cone. -/
lemma pureIntegerPointsZeroAuxDecomposition
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ k q : ℕ,
      ∃ Q : Fin k → Set (Fin n → ℝ),
        ∃ r : Fin q → Fin n → ℤ,
          (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
            pure_integer_points P = (⋃ i : Fin k, Q i) + integral_intcone r := by
  have hMixed : is_rational_mixed_polyhedron (pureAsMixedSet P) := by
    -- The zero continuous block turns the flattened mixed set back into the original polyhedron.
    change is_rational_polyhedron (Fin.appendEquiv n 0 '' pureAsMixedSet P)
    simpa [image_pureAsMixedSet_eq] using hP_rational
  rcases
    mixed_integer_points_eq_iUnion_rational_polytopes_add_intcone
      (n := n) (p := 0) (pureAsMixedSet P) hMixed with
    ⟨k, q, Qmixed, r, hQmixed, hdecomp⟩
  let Q : Fin k → Set (Fin n → ℝ) := fun i ↦ Fin.appendEquiv n 0 '' Qmixed i
  let rFlat : Fin q → Fin n → ℤ := fun j ↦ (r j).1
  have hgen :
      (fun j : Fin q ↦ Fin.append (r j).1 (r j).2) = rFlat := by
    funext j
    ext i
    simpa [rFlat] using (Fin.append_left (r j).1 (r j).2 i)
  have hQ : ∀ i : Fin k, (Q i).IsRationalPolytope := by
    intro i
    -- Mixed rationality is defined by rationality after the same flattening map.
    simpa [Q, is_mixed_rational_polytope] using hQmixed i
  have hImage :
      Fin.appendEquiv n 0 '' ((⋃ i : Fin k, Qmixed i) + mixed_integer_intcone r) =
        (⋃ i : Fin k, Q i) + integral_intcone rFlat := by
    ext u
    constructor
    · rintro ⟨xy, hxy, rfl⟩
      rcases hxy with ⟨a, ha, b, hb, rfl⟩
      rcases Set.mem_iUnion.1 ha with ⟨i, hai⟩
      have hb' : Fin.appendEquiv n 0 b ∈ integral_intcone rFlat := by
        rcases hb with ⟨v, hv, rfl⟩
        rw [hgen] at hv
        simpa using hv
      refine Set.mem_add.2 ⟨Fin.appendEquiv n 0 a, ?_, Fin.appendEquiv n 0 b, hb', ?_⟩
      · exact Set.mem_iUnion.2 ⟨i, ⟨a, hai, rfl⟩⟩
      · -- Rewriting everything through the first coordinate avoids zero-block transport noise.
        rw [appendEquiv_zero_eq_fst, appendEquiv_zero_eq_fst, appendEquiv_zero_eq_fst]
        rfl
    · rintro ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩
      rcases Set.mem_iUnion.1 hu₁ with ⟨i, hu₁⟩
      rcases hu₁ with ⟨a, ha, rfl⟩
      have hu₂' : (Fin.appendEquiv n 0).symm u₂ ∈ mixed_integer_intcone r := by
        refine ⟨u₂, ?_, rfl⟩
        rw [hgen]
        simpa using hu₂
      refine ⟨a + (Fin.appendEquiv n 0).symm u₂, ?_, ?_⟩
      · exact Set.mem_add.2 ⟨a, Set.mem_iUnion.2 ⟨i, ha⟩, (Fin.appendEquiv n 0).symm u₂, hu₂', rfl⟩
      · calc
          Fin.appendEquiv n 0 (a + (Fin.appendEquiv n 0).symm u₂)
              = Fin.appendEquiv n 0 a + Fin.appendEquiv n 0 ((Fin.appendEquiv n 0).symm u₂) := by
                  -- The flattening map keeps only the first coordinate, so addition is immediate.
                  rw [appendEquiv_zero_eq_fst, appendEquiv_zero_eq_fst,
                    appendEquiv_zero_eq_fst]
                  rfl
          _ = Fin.appendEquiv n 0 a + u₂ := by simp
          _ = u := hu_eq
  refine ⟨k, q, Q, rFlat, hQ, ?_⟩
  -- Flatten the mixed decomposition back to the pure ambient space.
  calc
    pure_integer_points P = Fin.appendEquiv n 0 '' mixed_integer_points (pureAsMixedSet P) := by
      symm
      exact image_mixedIntegerPoints_pureAsMixedSet_eq P
    _ = Fin.appendEquiv n 0 '' ((⋃ i : Fin k, Qmixed i) + mixed_integer_intcone r) := by
      rw [hdecomp]
    _ = (⋃ i : Fin k, Q i) + integral_intcone rFlat := hImage

/-- Helper for Lemma 5.16: clearing denominators in each augmented rational row rewrites a
`rational_matrix_polyhedron` as one integral real matrix system. -/
lemma existsIntegralPresentationOfRationalMatrixPolyhedron
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ Aint : Matrix (Fin m) (Fin n) ℤ,
      ∃ bint : Fin m → ℤ,
        rational_matrix_polyhedron A b =
          polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
  let augmentedRow : Fin m → Fin (n + 1) → ℚ :=
    fun i ↦ Fin.append (A i) (fun _ ↦ b i)
  let rowDen : Fin m → ℕ := fun i ↦ rational_vector_common_denominator (augmentedRow i)
  let Aint : Matrix (Fin m) (Fin n) ℤ :=
    fun i j ↦ common_denominator_scaled_vector (augmentedRow i) (Fin.castAdd 1 j)
  let bint : Fin m → ℤ :=
    fun i ↦ common_denominator_scaled_vector (augmentedRow i) (Fin.natAdd n 0)
  refine ⟨Aint, bint, ?_⟩
  ext x
  rw [mem_rational_matrix_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hx i
    have hden_ne_zero : rowDen i ≠ 0 :=
      rationalVectorCommonDenominator_ne_zero (v := augmentedRow i)
    have hden_pos : 0 < (rowDen i : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hden_ne_zero
    have hrowScaled :
        (fun j ↦ (Aint i j : ℝ)) = (rowDen i : ℝ) • fun j ↦ (A i j : ℝ) := by
      funext j
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.castAdd 1 j)
      simpa [Aint, augmentedRow] using hscaled
    have hrhsScaled :
        (bint i : ℝ) = (rowDen i : ℝ) * (b i : ℝ) := by
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.natAdd n 0)
      simpa [bint, augmentedRow] using hscaled
    have hmulScaled :
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i =
          (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
      calc
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
            = (fun j ↦ (Aint i j : ℝ)) ⬝ᵥ x := by
                simp [Matrix.mulVec]
        _ = ((rowDen i : ℝ) • fun j ↦ (A i j : ℝ)) ⬝ᵥ x := by
              rw [hrowScaled]
        _ = (rowDen i : ℝ) * ((fun j ↦ (A i j : ℝ)) ⬝ᵥ x) := by
              simp [dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc]
        _ = (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
              simp [Matrix.mulVec]
    -- Multiplying a valid rational row by its positive denominator preserves the inequality.
    change ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ (bint i : ℝ)
    rw [hmulScaled, hrhsScaled]
    exact mul_le_mul_of_nonneg_left (hx i) hden_pos.le
  · intro hx i
    have hden_ne_zero : rowDen i ≠ 0 :=
      rationalVectorCommonDenominator_ne_zero (v := augmentedRow i)
    have hden_pos : 0 < (rowDen i : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hden_ne_zero
    have hrowScaled :
        (fun j ↦ (Aint i j : ℝ)) = (rowDen i : ℝ) • fun j ↦ (A i j : ℝ) := by
      funext j
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.castAdd 1 j)
      simpa [Aint, augmentedRow] using hscaled
    have hrhsScaled :
        (bint i : ℝ) = (rowDen i : ℝ) * (b i : ℝ) := by
      have hscaled := congrFun (commonDenominatorScaledVector_eq_smul_real (v := augmentedRow i))
        (Fin.natAdd n 0)
      simpa [bint, augmentedRow] using hscaled
    have hmulScaled :
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i =
          (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
      calc
        ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
            = (fun j ↦ (Aint i j : ℝ)) ⬝ᵥ x := by
                simp [Matrix.mulVec]
        _ = ((rowDen i : ℝ) • fun j ↦ (A i j : ℝ)) ⬝ᵥ x := by
              rw [hrowScaled]
        _ = (rowDen i : ℝ) * ((fun j ↦ (A i j : ℝ)) ⬝ᵥ x) := by
              simp [dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc]
        _ = (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) := by
              simp [Matrix.mulVec]
    have hscaledLe :
        (rowDen i : ℝ) * (((A.map (Rat.castHom ℝ)) *ᵥ x) i) ≤
          (rowDen i : ℝ) * (b i : ℝ) := by
      have hx' : ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i ≤ (bint i : ℝ) := hx i
      rw [hmulScaled, hrhsScaled] at hx'
      exact hx'
    -- Divide by the same positive denominator to recover the original rational row.
    nlinarith

/-- Helper for Lemma 5.16: the convex hull of a finite union of rational polytopes is again a
rational polytope. -/
lemma convexHullRangeIsRationalPolytopeOfFintype
    {k : ℕ}
    {ι : Type*}
    [Finite ι]
    (vertex : ι → Fin k → ℚ) :
    (convexHull ℝ (Set.range fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ))).IsRationalPolytope := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j i ↦ vertex (e j) i, ?_⟩
  ext x
  constructor
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin k ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin k ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin k ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx

/-- Helper for Lemma 5.16: the convex hull of a finite union of rational polytopes is again a
rational polytope. -/
lemma convexHullIUnionIsRationalPolytope
    {d k : ℕ}
    (Q : Fin k → Set (Fin d → ℝ))
    (hQ : ∀ i, (Q i).IsRationalPolytope) :
    (convexHull ℝ (⋃ i : Fin k, Q i)).IsRationalPolytope := by
  classical
  -- Replace the finite union by the range of all chosen rational vertices at once.
  choose m vertex hvertex using hQ
  let allVertices : Sigma (fun i : Fin k ↦ Fin (m i)) → Fin d → ℚ :=
    fun a ↦ vertex a.1 a.2
  have hvertex_subset :
      Set.range (fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
          fun j : Fin d ↦ (allVertices a j : ℝ)) ⊆
        ⋃ i : Fin k, Q i := by
    rintro x ⟨a, rfl⟩
    have hx :
        (fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) ∈
          convexHull ℝ (Set.range fun t : Fin (m a.1) ↦ fun j : Fin d ↦ (vertex a.1 t j : ℝ)) :=
      subset_convexHull ℝ _ ⟨a.2, rfl⟩
    rw [← hvertex a.1] at hx
    exact Set.mem_iUnion.2 ⟨a.1, hx⟩
  have hiUnion_subset :
      (⋃ i : Fin k, Q i) ⊆
        convexHull ℝ
          (Set.range fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
            fun j : Fin d ↦ (allVertices a j : ℝ)) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
    rw [hvertex i] at hx
    refine (convexHull_mono ?_) hx
    rintro y ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  have hEq :
      convexHull ℝ (⋃ i : Fin k, Q i) =
        convexHull ℝ
          (Set.range fun a : Sigma (fun i : Fin k ↦ Fin (m i)) ↦
            fun j : Fin d ↦ (allVertices a j : ℝ)) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hiUnion_subset (convex_convexHull ℝ _)
    · refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro x hx
      exact subset_convexHull ℝ _ (hvertex_subset hx)
  -- The range of finitely many rational vertices is the canonical rational-polytope surface.
  rw [hEq]
  exact convexHullRangeIsRationalPolytopeOfFintype allVertices

/-- Helper for Lemma 5.16: the convex hull of an integral cone is the real cone generated by the
same integral rays. -/
lemma integralIntconeCastSucc_subset
    {k q : ℕ} (r : Fin (q + 1) → Fin k → ℤ) :
    integral_intcone (fun j : Fin q ↦ fun i : Fin k ↦ r j.castSucc i) ⊆
      integral_intcone r := by
  intro u hu
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, ha⟩
  refine (mem_integral_intcone_iff).2 ?_
  let a' : Fin (q + 1) → ℕ := Fin.snoc a 0
  refine ⟨a', ?_⟩
  rw [ha]
  ext i
  rw [Fin.sum_univ_castSucc]
  simp [a', Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Lemma 5.16: every listed generator belongs to its integral cone. -/
lemma generator_mem_integralIntcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) :
    (fun i ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  -- Use the one-hot coefficient family supported at `j`.
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨Pi.single j 1, ?_⟩
  classical
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    ext i'
    simp [hc]
  · simp

/-- Helper for Lemma 5.16: a natural multiple of one generator already lies in the integral cone.
-/
lemma nat_smul_generator_mem_integralIntcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) (m : ℕ) :
    (m : ℝ) • (fun i : Fin k ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  -- Encode the natural multiple directly in the coefficient family.
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun t ↦ if t = j then m else 0, ?_⟩
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

/-- Helper for Lemma 5.16: the integral cone is closed under addition. -/
lemma add_mem_integralIntcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ integral_intcone r)
    (hv : v ∈ integral_intcone r) :
    u + v ∈ integral_intcone r := by
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integral_intcone_iff).1 hv with ⟨b, rfl⟩
  -- Add the two natural coefficient families pointwise.
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun j ↦ a j + b j, ?_⟩
  simp [Nat.cast_add, add_smul, Finset.sum_add_distrib]

/-- Helper for Lemma 5.16: translating the convex hull of the integral cone by another integral
cone element keeps the point inside the same convex hull. -/
lemma add_mem_convexHull_integralIntcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ convexHull ℝ (integral_intcone r))
    (hv : v ∈ integral_intcone r) :
    u + v ∈ convexHull ℝ (integral_intcone r) := by
  have htranslate_subset :
      v +ᵥ integral_intcone r ⊆ integral_intcone r := by
    rintro w ⟨z, hz, rfl⟩
    simpa [Pi.vadd_def, vadd_eq_add, add_comm] using
      add_mem_integralIntcone (r := r) hv hz
  have htranslate_hull :
      v +ᵥ convexHull ℝ (integral_intcone r) ⊆ convexHull ℝ (integral_intcone r) := by
    rw [← convexHull_vadd]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro w hw
    exact subset_convexHull ℝ _ (htranslate_subset hw)
  have huv :
      u + v ∈ v +ᵥ convexHull ℝ (integral_intcone r) := by
    rw [Set.mem_vadd_set]
    refine ⟨u, hu, ?_⟩
    ext i
    simp [vadd_eq_add, add_comm]
  exact htranslate_hull huv

/-- Helper for Lemma 5.16: every fractional combination of the integral generators already lies in
the convex hull of their integral cone. -/
lemma fractionalCombination_mem_convexHull_integralIntcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (μ : Fin q → ℝ)
    (hμ_nonneg : ∀ j : Fin q, 0 ≤ μ j)
    (hμ_le_one : ∀ j : Fin q, μ j ≤ 1) :
    (∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ))) ∈
      convexHull ℝ (integral_intcone r) := by
  induction q with
  | zero =>
      simpa using
        (subset_convexHull ℝ (integral_intcone r) (by
          exact (mem_integral_intcone_iff).2 ⟨fun _ ↦ 0, by simp⟩))
  | succ q ih =>
      let rInit : Fin q → Fin k → ℤ := fun j i ↦ r j.castSucc i
      let μInit : Fin q → ℝ := fun j ↦ μ j.castSucc
      have hbase_small :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone rInit) := by
        exact ih rInit μInit (fun j ↦ hμ_nonneg j.castSucc) (fun j ↦ hμ_le_one j.castSucc)
      have hbase :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone r) := by
        refine convexHull_min ?_ (convex_convexHull ℝ _) hbase_small
        intro u hu
        exact subset_convexHull ℝ _ (integralIntconeCastSucc_subset (r := r) hu)
      let lastRay : Fin k → ℝ := fun i ↦ (r (Fin.last q) i : ℝ)
      have hbase_plus :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) + lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        exact add_mem_convexHull_integralIntcone
          (r := r) hbase (generator_mem_integralIntcone r (Fin.last q))
      have hlast :
          μ (Fin.last q) ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ_nonneg _, hμ_le_one _⟩
      have hfinal :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) +
              μ (Fin.last q) • lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        exact (convex_convexHull ℝ (integral_intcone r)).add_smul_mem hbase hbase_plus hlast
      simpa [rInit, μInit, lastRay, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        add_comm, add_left_comm, add_assoc] using hfinal

/-- Helper for Lemma 5.16: the convex hull of an integral cone is the real cone generated by the
same integral rays. -/
lemma convexHullIntegralIntcone_eqFinitelyGeneratedCone
    {k q : ℕ}
    (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_intcone r) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · intro u hu
      rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
      refine (mem_finitely_generated_cone_iff).2 ?_
      refine ⟨fun j ↦ (a j : ℝ), ?_, rfl⟩
      intro j
      positivity
    · simpa [finitely_generated_cone] using
        cone_convex (R := ℝ) (Set.range fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ))
  · intro u hu
    rcases (mem_finitely_generated_cone_iff).1 hu with ⟨μ, hμ_nonneg, hrepr⟩
    have hintPart :
        (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          integral_intcone r := by
      exact (mem_integral_intcone_iff).2 ⟨fun j ↦ ⌊μ j⌋₊, rfl⟩
    have hfracPart :
        (∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          convexHull ℝ (integral_intcone r) := by
      exact fractionalCombination_mem_convexHull_integralIntcone
        r
        (fun j ↦ Int.fract (μ j))
        (fun j ↦ Int.fract_nonneg (μ j))
        (fun j ↦ (Int.fract_lt_one (μ j)).le)
    have hsplit :
        u =
          (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
            ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
      calc
        u = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              ((((⌊μ j⌋₊ : ℕ) : ℝ) + Int.fract (μ j)) • (fun i : Fin k ↦ (r j i : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [natCast_floor_eq_intCast_floor (hμ_nonneg j), Int.floor_add_fract]
        _ = (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
              ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
              simp [add_smul, Finset.sum_add_distrib]
    rw [hsplit]
    simpa [add_comm] using add_mem_convexHull_integralIntcone hfracPart hintPart

/-- Helper for Lemma 5.16: adding a natural multiple of an integral vector preserves integrality.
-/
lemma integerVectors_add_nat_smul_of_integral
    {k : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ integerVectors k)
    (z : Fin k → ℤ)
    (m : ℕ) :
    (fun i : Fin k ↦ x i + (m : ℝ) * (z i : ℝ)) ∈ integerVectors k := by
  rcases (mem_integerVectors_iff (x := x)).1 hx with ⟨a, ha⟩
  -- Lift the translated point back to the obvious integer witness.
  refine (mem_integerVectors_iff (x := fun i : Fin k ↦ x i + (m : ℝ) * (z i : ℝ))).2 ?_
  refine ⟨fun i ↦ a i + (m : ℤ) * z i, ?_⟩
  ext i
  simp [ha, mul_comm]

/-- Helper for Lemma 5.16: natural-translate closure of one feasible point already gives a
recession direction for a polyhedron. -/
lemma mem_recessionCone_of_natTranslateMem
    {k m : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    {x₀ r : Fin k → ℝ}
    (hx₀ : x₀ ∈ polyhedron_le_set A b)
    (htranslate : ∀ t : ℕ, x₀ + (t : ℝ) • r ∈ polyhedron_le_set A b) :
    r ∈ recessionCone (polyhedron_le_set A b) := by
  have h_nonempty : Set.Nonempty (polyhedron_le_set A b) := ⟨x₀, hx₀⟩
  rw [polyhedron_recessionCone_eq_homogeneous_solution_set A b h_nonempty]
  intro i
  by_contra hri
  have hri_pos : 0 < (A *ᵥ r) i := lt_of_not_ge hri
  obtain ⟨t, ht⟩ := exists_nat_gt ((b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i)
  have hxt : x₀ + (t : ℝ) • r ∈ polyhedron_le_set A b := htranslate t
  have hrow : (A *ᵥ x₀) i + (t : ℝ) * (A *ᵥ r) i ≤ b i := by
    simpa [polyhedron_le_set, Matrix.mulVec_add, Matrix.mulVec_smul] using hxt i
  have hmul : b i - (A *ᵥ x₀) i + 1 < (t : ℝ) * (A *ᵥ r) i := by
    have ht' : ((b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i) < (t : ℝ) := by
      exact_mod_cast ht
    exact (div_lt_iff₀ hri_pos).1 ht'
  linarith

/-- Helper for Lemma 5.16: if every listed generator is a recession direction, then the whole
finitely generated cone lies in the recession cone. -/
lemma finitelyGeneratedCone_subset_recessionCone_of_generator_mem
    {k q : ℕ}
    {Q : Set (Fin k → ℝ)}
    {rays : Fin q → Fin k → ℝ}
    (hgen : ∀ j : Fin q, rays j ∈ recessionCone Q) :
    finitely_generated_cone rays ⊆ recessionCone Q := by
  intro x hx
  rcases (mem_finitely_generated_cone_iff).1 hx with ⟨μ, hμ_nonneg, rfl⟩
  -- The recession directions form a pointed cone, so nonnegative combinations stay inside.
  have hterm :
      ∀ j : Fin q, μ j • rays j ∈ recessionCone Q := by
    intro j
    exact smul_mem_recessionCone (hgen j) (hμ_nonneg j)
  have hsum :
      ∑ j : Fin q, μ j • rays j ∈
        ((recessionPointedCone ℝ Q : PointedCone ℝ (Fin k → ℝ)) : Set (Fin k → ℝ)) := by
    exact Submodule.sum_mem (recessionPointedCone ℝ Q) (fun j _ ↦ hterm j)
  simpa using hsum

/-- Helper for Lemma 5.16: the decomposition from Corollary 4.31 yields a rational polyhedron
presentation of `pure_integer_hull P`. -/
lemma pureIntegerHullIsRationalPolyhedron
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    is_rational_polyhedron (pure_integer_hull P) := by
  rcases pureIntegerPointsZeroAuxDecomposition P hP_rational with
    ⟨k, q, Q, r, hQ, hdecomp⟩
  have hU_rational :
      (convexHull ℝ (⋃ i : Fin k, Q i)).IsRationalPolytope :=
    convexHullIUnionIsRationalPolytope Q hQ
  rcases hU_rational with ⟨t, vertices, hvertices⟩
  let raysQ : Fin q → Fin n → ℚ := fun j i ↦ (r j i : ℚ)
  let L : ℕ :=
    max
      ((Finset.univ : Finset (Fin t)).sup fun i ↦ EncodingSize.rationalVector (vertices i))
      ((Finset.univ : Finset (Fin q)).sup fun j ↦ EncodingSize.rationalVector (raysQ j))
  have hvertices_bound :
      ∀ i : Fin t, EncodingSize.rationalVector (vertices i) ≤ L := by
    intro i
    -- The chosen constant bound dominates all finitely many vertex encodings.
    have hi :
        EncodingSize.rationalVector (vertices i) ≤
          (Finset.univ : Finset (Fin t)).sup
            (fun j ↦ EncodingSize.rationalVector (vertices j)) := by
      simpa using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin t)))
          (f := fun j ↦ EncodingSize.rationalVector (vertices j))
          (b := i)
          (by simp))
    exact le_trans hi (Nat.le_max_left _ _)
  have hrays_bound :
      ∀ j : Fin q, EncodingSize.rationalVector (raysQ j) ≤ L := by
    intro j
    -- The same constant bound also dominates the integral rays after casting to `ℚ`.
    have hj :
        EncodingSize.rationalVector (raysQ j) ≤
          (Finset.univ : Finset (Fin q)).sup
            (fun t ↦ EncodingSize.rationalVector (raysQ t)) := by
      simpa using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin q)))
          (f := fun t ↦ EncodingSize.rationalVector (raysQ t))
          (b := j)
          (by simp))
    exact le_trans hj (Nat.le_max_right _ _)
  rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
      vertices raysQ L hvertices_bound hrays_bound with
    ⟨π, m, A, b, hrepr, -, -⟩
  refine ⟨m, A, b, ?_⟩
  -- Rewrite the pure-integer hull to the canonical `conv + cone` form consumed by Theorem 3.39.
  calc
    pure_integer_hull P = convexHull ℝ (pure_integer_points P) := rfl
    _ = convexHull ℝ ((⋃ i : Fin k, Q i) + integral_intcone r) := by rw [hdecomp]
    _ = convexHull ℝ (⋃ i : Fin k, Q i) + convexHull ℝ (integral_intcone r) := by
          rw [convexHull_add]
    _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ)) +
          convexHull ℝ (integral_intcone r) := by
            rw [hvertices]
    _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ)) +
          finitely_generated_cone (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ)) := by
            rw [convexHullIntegralIntcone_eqFinitelyGeneratedCone]
    _ = rational_matrix_polyhedron A b := by
          simpa [raysQ, finitely_generated_cone] using hrepr

/-- Helper for Lemma 5.16: in the nonempty case, `pure_integer_hull P` and `P` have the same
recession cone. -/
lemma pureIntegerHullRecessionCone_eq
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (hPI_nonempty : (pure_integer_hull P).Nonempty) :
    recessionCone (pure_integer_hull P) = recessionCone P := by
  rcases pureIntegerHull_nonempty_iff_pureIntegerPoints_nonempty P |>.1 hPI_nonempty with
    ⟨x₀, hx₀⟩
  rcases (mem_pure_integer_points_iff.mp hx₀) with ⟨hx₀P, hx₀Int⟩
  rcases pureIntegerPointsZeroAuxDecomposition P hP_rational with
    ⟨k, q, Q, r, hQ, hdecomp⟩
  rcases pureIntegerHullIsRationalPolyhedron P hP_rational with
    ⟨mH, AH, bH, hHull_eq⟩
  rcases hP_rational with ⟨mP, AP, bP, hP_eq⟩
  have hHull_nonempty_poly :
      Set.Nonempty (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
    simpa [hHull_eq] using hPI_nonempty
  have hP_nonempty_poly :
      Set.Nonempty (polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ))) := by
    simpa [hP_eq] using hP_nonempty
  have hU_rational :
      (convexHull ℝ (⋃ i : Fin k, Q i)).IsRationalPolytope :=
    convexHullIUnionIsRationalPolytope Q hQ
  rcases hU_rational with ⟨t, vertices, hvertices⟩
  have hHull_repr :
      polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) =
        convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ)) +
          finitely_generated_cone (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ)) := by
    -- Normalize the hull decomposition once on the canonical `conv + cone` surface.
    calc
      polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))
          = pure_integer_hull P := hHull_eq.symm
      _ = convexHull ℝ (pure_integer_points P) := rfl
      _ = convexHull ℝ ((⋃ i : Fin k, Q i) + integral_intcone r) := by rw [hdecomp]
      _ = convexHull ℝ (⋃ i : Fin k, Q i) + convexHull ℝ (integral_intcone r) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ)) +
            convexHull ℝ (integral_intcone r) := by
              rw [hvertices]
      _ = convexHull ℝ (Set.range fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ)) +
            finitely_generated_cone (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ)) := by
              rw [convexHullIntegralIntcone_eqFinitelyGeneratedCone]
  have hHull_rec :
      recessionCone (pure_integer_hull P) =
        finitely_generated_cone (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ)) := by
    -- Compute the hull recession cone from the finite `conv + cone` presentation.
    calc
      recessionCone (pure_integer_hull P)
          = recessionCone
              (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
                rw [hHull_eq]
      _ = finitely_generated_cone (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ)) := by
            exact
              polyhedron_recessionCone_eq_finitely_generated_cone
                (AH.map (Rat.castHom ℝ))
                (fun i ↦ (bH i : ℝ))
                (fun i : Fin t ↦ fun u : Fin n ↦ (vertices i u : ℝ))
                (fun j : Fin q ↦ fun u : Fin n ↦ (r j u : ℝ))
                hHull_nonempty_poly
                hHull_repr
  have hrays_mem_P :
      ∀ j : Fin q, (fun u : Fin n ↦ (r j u : ℝ)) ∈ recessionCone P := by
    intro j
    rcases Set.mem_add.1 (by simpa [hdecomp] using hx₀) with ⟨u₀, hu₀, c₀, hc₀, hx₀_eq⟩
    have hx₀_poly : x₀ ∈ polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) := by
      simpa [hP_eq] using hx₀P
    have htranslate :
        ∀ t : ℕ,
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) ∈
            polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ)) := by
      intro t
      have hc₀' :
          c₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) ∈ integral_intcone r := by
        exact
          add_mem_integralIntcone
            hc₀
            (nat_smul_generator_mem_integralIntcone r j t)
      have hx_translate_decomp :
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) ∈
            (⋃ i : Fin k, Q i) + integral_intcone r := by
        refine Set.mem_add.2 ⟨u₀, hu₀, c₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)), hc₀', ?_⟩
        calc
          u₀ + (c₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)))
              = (u₀ + c₀) + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) := by
                  abel
          _ = x₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) := by
                rw [hx₀_eq]
      have hx_translate_pure :
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) ∈ pure_integer_points P := by
        rw [hdecomp]
        exact hx_translate_decomp
      have hx_translate_P :
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (r j u : ℝ)) ∈ P :=
        (mem_pure_integer_points_iff.mp hx_translate_pure).1
      simpa [hP_eq] using hx_translate_P
    have hrec_poly :
        (fun u : Fin n ↦ (r j u : ℝ)) ∈
          recessionCone
            (polyhedron_le_set (AP.map (Rat.castHom ℝ)) (fun i ↦ (bP i : ℝ))) := by
      exact
        mem_recessionCone_of_natTranslateMem
          (AP.map (Rat.castHom ℝ))
          (fun i ↦ (bP i : ℝ))
          hx₀_poly
          htranslate
    simpa [hP_eq] using hrec_poly
  have hHull_subset_P :
      recessionCone (pure_integer_hull P) ⊆ recessionCone P := by
    rw [hHull_rec]
    exact finitelyGeneratedCone_subset_recessionCone_of_generator_mem hrays_mem_P
  rcases
      existsIntegralRecessionGeneratorsOfRationalPolyhedron
        P hP_nonempty ⟨mP, AP, bP, hP_eq⟩ with
    ⟨qP, raysP, hP_rec⟩
  have hx₀Hull : x₀ ∈ pure_integer_hull P := by
    change x₀ ∈ convexHull ℝ (pure_integer_points P)
    exact subset_convexHull ℝ _ hx₀
  have hx₀Hull_poly :
      x₀ ∈ polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) := by
    simpa [hHull_eq] using hx₀Hull
  have hraysP_mem_hull :
      ∀ j : Fin qP, (fun u : Fin n ↦ (raysP j u : ℝ)) ∈ recessionCone (pure_integer_hull P) := by
    intro j
    have hjP :
        (fun u : Fin n ↦ (raysP j u : ℝ)) ∈ recessionCone P := by
      rw [hP_rec]
      exact
        (mem_finitely_generated_cone_iff).2
          ⟨Pi.single j 1, by
            intro t
            by_cases ht : t = j
            · subst ht
              simp
            · simp [Pi.single, ht], by
            ext u
            rw [Finset.sum_eq_single j]
            · simp [Pi.single]
            · intro t _ ht
              simp [Pi.single, ht]
            · simp [Pi.single]⟩
    rw [mem_recessionCone_iff] at hjP
    have htranslate :
        ∀ t : ℕ,
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (raysP j u : ℝ)) ∈
            polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ)) := by
      intro t
      have hx_translate_P :
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (raysP j u : ℝ)) ∈ P :=
        hjP hx₀P t (by positivity)
      have hx_translate_int :
          (fun i : Fin n ↦
            (x₀ + (t : ℝ) • (fun u : Fin n ↦ (raysP j u : ℝ))) i) ∈ integerVectors n := by
        simpa [Pi.add_apply, Pi.smul_apply, mul_comm, add_comm, add_left_comm, add_assoc] using
          integerVectors_add_nat_smul_of_integral
            hx₀Int
            (raysP j)
            t
      have hx_translate_hull :
          x₀ + (t : ℝ) • (fun u : Fin n ↦ (raysP j u : ℝ)) ∈ pure_integer_hull P := by
        rw [pure_integer_hull_eq_convexHull]
        exact
          subset_convexHull ℝ _
            ((mem_pure_integer_points_iff).2 ⟨hx_translate_P, hx_translate_int⟩)
      simpa [hHull_eq] using hx_translate_hull
    have hrec_poly :
        (fun u : Fin n ↦ (raysP j u : ℝ)) ∈
          recessionCone
            (polyhedron_le_set (AH.map (Rat.castHom ℝ)) (fun i ↦ (bH i : ℝ))) := by
      exact
        mem_recessionCone_of_natTranslateMem
          (AH.map (Rat.castHom ℝ))
          (fun i ↦ (bH i : ℝ))
          hx₀Hull_poly
          htranslate
    simpa [hHull_eq] using hrec_poly
  have hP_subset_hull :
      recessionCone P ⊆ recessionCone (pure_integer_hull P) := by
    rw [hP_rec]
    exact finitelyGeneratedCone_subset_recessionCone_of_generator_mem hraysP_mem_hull
  exact Set.Subset.antisymm hHull_subset_P hP_subset_hull

/-- Helper for Lemma 5.16: a linear form that vanishes on the direction of `aff(P)` is constant on
`aff(P)`. -/
lemma dotProduct_eq_of_mem_affineSpan_of_orthogonal_direction
    (P : Set (Fin n → ℝ))
    {c x x₀ : Fin n → ℝ}
    (hc :
      ∀ y : Fin n → ℝ, y ∈ (affineSpan ℝ P).direction → c ⬝ᵥ y = 0)
    (hx : x ∈ (affineSpan ℝ P : Set (Fin n → ℝ)))
    (hx₀ : x₀ ∈ (affineSpan ℝ P : Set (Fin n → ℝ))) :
    c ⬝ᵥ x = c ⬝ᵥ x₀ := by
  -- The difference of two affine-span points lies in the direction subspace.
  have hdir : x - x₀ ∈ (affineSpan ℝ P).direction := by
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀]
    simpa [vsub_eq_sub] using hx
  have hzero : c ⬝ᵥ (x - x₀) = 0 := hc (x - x₀) hdir
  -- Expanding the dot product over the difference shows the two values coincide.
  have hdot : c ⬝ᵥ (x - x₀) = c ⬝ᵥ x - c ⬝ᵥ x₀ := by
    simp [dotProduct_sub]
  linarith

lemma existsValidBoundOfNonpositiveOnRecessionCone
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    {c : Fin n → ℝ}
    (hc :
      ∀ r : Fin n → ℝ, r ∈ recessionCone P → c ⬝ᵥ r ≤ 0) :
    ∃ d : ℝ, is_valid_inequality P c d := by
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  have hPoly_nonempty :
      Set.Nonempty (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
    simpa [hP_eq] using hP_nonempty
  have hDual_nonempty :
      Set.Nonempty (dual_feasible_region (A.map (Rat.castHom ℝ)) c) := by
    refine
      (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions
        (A.map (Rat.castHom ℝ)) c).2 ?_
    intro r hr
    have hrP :
        r ∈ recessionCone
          (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
      rw [polyhedron_recessionCone_eq_homogeneous_solution_set
        (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)) hPoly_nonempty]
      exact hr
    exact hc r (by simpa [hP_eq] using hrP)
  obtain ⟨xStar, hxStar, hGreatest⟩ :=
    linear_programming_duality_primal_optimum_exists
      (A.map (Rat.castHom ℝ))
      (fun i ↦ (b i : ℝ))
      c
      (by simpa [primal_feasible_region] using hPoly_nonempty)
      hDual_nonempty
  refine ⟨c ⬝ᵥ xStar, ?_⟩
  intro x hx
  -- The primal optimum returned by LP duality bounds every feasible point.
  exact hGreatest.2 ⟨x, by simpa [primal_feasible_region, hP_eq] using hx, rfl⟩

/-- Helper for Lemma 5.16: in the nonempty case, one can clear denominators in a rational
presentation of `pure_integer_hull P`, discard the rows orthogonal to `aff(P)`, and keep a valid
integral system. -/
lemma existsIntegralSystemOfNonemptyPureIntegerHull
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (hPI_nonempty : (pure_integer_hull P).Nonempty) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℤ,
      IsPureIntegerHullIntegralSystem P A b := by
  have hPurePoints_nonempty : (pure_integer_points P).Nonempty :=
    (pureIntegerHull_nonempty_iff_pureIntegerPoints_nonempty P).1 hPI_nonempty
  have hDecomp :
      ∃ k q : ℕ,
        ∃ Q : Fin k → Set (Fin n → ℝ),
          ∃ r : Fin q → Fin n → ℤ,
            (∀ i : Fin k, (Q i).IsRationalPolytope) ∧
              pure_integer_points P = (⋃ i : Fin k, Q i) + integral_intcone r :=
    pureIntegerPointsZeroAuxDecomposition P hP_rational
  have hHull_rational : is_rational_polyhedron (pure_integer_hull P) :=
    pureIntegerHullIsRationalPolyhedron P hP_rational
  have hHull_recession :
      recessionCone (pure_integer_hull P) = recessionCone P :=
    pureIntegerHullRecessionCone_eq P hP_nonempty hP_rational hPI_nonempty
  rcases hHull_rational with ⟨mQ, AQ, bQ, hHull_eqQ⟩
  rcases existsIntegralPresentationOfRationalMatrixPolyhedron AQ bQ with
    ⟨Aint, bint, hInt_eq⟩
  have hHull_eq_int :
      pure_integer_hull P =
        polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
    -- First package the rational presentation as `rational_matrix_polyhedron`, then clear
    -- denominators rowwise.
    calc
      pure_integer_hull P = rational_matrix_polyhedron AQ bQ := by
        simpa [rational_matrix_polyhedron] using hHull_eqQ
      _ = polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := hInt_eq
  classical
  obtain ⟨x₀, hx₀_hull⟩ := hPI_nonempty
  have hx₀_aff : x₀ ∈ (affineSpan ℝ P : Set (Fin n → ℝ)) :=
    pureIntegerHull_subset_affineSpan P hx₀_hull
  have hx₀_poly :
      x₀ ∈ polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
    simpa [hHull_eq_int] using hx₀_hull
  let keptRows :=
    {i : Fin mQ //
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ P).direction ∧
          (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ y ≠ 0}
  let e : Fin (Fintype.card keptRows) ≃ keptRows := (Fintype.equivFin keptRows).symm
  let A : Matrix (Fin (Fintype.card keptRows)) (Fin n) ℤ :=
    fun i j ↦ Aint (e i).1 j
  let b : Fin (Fintype.card keptRows) → ℤ :=
    fun i ↦ bint (e i).1
  refine ⟨Fintype.card keptRows, A, b, ?_⟩
  refine
    { hull_eq := ?_
      row_not_orthogonal := ?_
      row_valid := ?_ }
  · -- Route correction: discard only rows that are constant on `aff(P)`.
    ext x
    constructor
    · intro hx
      refine ⟨?_, pureIntegerHull_subset_affineSpan P hx⟩
      rw [mem_polyhedron_le_set_iff]
      intro i
      have hx_full :
          x ∈ polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun j ↦ (bint j : ℝ)) := by
        simpa [hHull_eq_int] using hx
      exact by
        simpa [A, b, e] using (mem_polyhedron_le_set_iff.mp hx_full) (e i).1
    · rintro ⟨hx_keep, hx_aff⟩
      have hx_full :
          x ∈ polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun i ↦ (bint i : ℝ)) := by
        rw [mem_polyhedron_le_set_iff]
        intro i
        by_cases hi :
            ∃ y : Fin n → ℝ,
              y ∈ (affineSpan ℝ P).direction ∧
                (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ y ≠ 0
        · let ikeep : keptRows := ⟨i, hi⟩
          have hx_keep' := (mem_polyhedron_le_set_iff.mp hx_keep) (e.symm ikeep)
          calc
            ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
                = ((A.map (Int.castRingHom ℝ)) *ᵥ x) (e.symm ikeep) := by
                    simp [A, e, ikeep, Matrix.mulVec]
            _ ≤ (b (e.symm ikeep) : ℝ) := hx_keep'
            _ = (bint i : ℝ) := by
                  simp [b, e, ikeep]
        · have hi_const :
              ∀ y : Fin n → ℝ,
                y ∈ (affineSpan ℝ P).direction →
                  (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ y = 0 := by
            intro y hy
            by_contra hy_ne
            exact hi ⟨y, hy, hy_ne⟩
          have hsame :
              (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ x =
                (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ x₀ :=
            dotProduct_eq_of_mem_affineSpan_of_orthogonal_direction
              P hi_const hx_aff hx₀_aff
          have hx₀_row :
              ((Aint.map (Int.castRingHom ℝ)) *ᵥ x₀) i ≤ (bint i : ℝ) :=
            (mem_polyhedron_le_set_iff.mp hx₀_poly) i
          calc
            ((Aint.map (Int.castRingHom ℝ)) *ᵥ x) i
                = (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ x := by
                    simp [Matrix.mulVec]
            _ = (fun j : Fin n ↦ (Aint i j : ℝ)) ⬝ᵥ x₀ := hsame
            _ = ((Aint.map (Int.castRingHom ℝ)) *ᵥ x₀) i := by
                  simp [Matrix.mulVec]
            _ ≤ (bint i : ℝ) := hx₀_row
      simpa [hHull_eq_int] using hx_full
  · intro i
    -- The retained-row index was defined exactly by nonorthogonality to `aff(P)`.
    rcases (e i).2 with ⟨y, hy, hy_ne⟩
    refine ⟨y, hy, ?_⟩
    simpa [A, e] using hy_ne
  · intro i
    let c : Fin n → ℝ := fun j ↦ (Aint (e i).1 j : ℝ)
    have hHull_nonempty : (pure_integer_hull P).Nonempty := ⟨x₀, hx₀_hull⟩
    have hvalid_hull : is_valid_inequality (pure_integer_hull P) c ((bint (e i).1 : ℤ) : ℝ) := by
      intro x hx
      have hx_poly :
          x ∈ polyhedron_le_set (Aint.map (Int.castRingHom ℝ)) (fun j ↦ (bint j : ℝ)) := by
        simpa [hHull_eq_int] using hx
      exact (mem_polyhedron_le_set_iff.mp hx_poly) (e i).1
    have hnonpos :
        ∀ r : Fin n → ℝ, r ∈ recessionCone P → c ⬝ᵥ r ≤ 0 := by
      intro r hr
      have hr_hull : r ∈ recessionCone (pure_integer_hull P) := by
        simpa [hHull_recession] using hr
      exact validIneq_nonpositive_on_recessionCone hHull_nonempty hvalid_hull hr_hull
    obtain ⟨d, hd⟩ :=
      existsValidBoundOfNonpositiveOnRecessionCone P hP_nonempty hP_rational hnonpos
    refine ⟨d, ?_⟩
    simpa [A, e, c] using hd

/-- Helper for Lemma 5.16: in the empty branch, the affine direction is strictly larger than the
span of the recession cone, so one can choose a direction vector outside that span. -/
lemma existsDirectionOutsideRecessionSpan
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ ℤ^n).Nonempty)
    (hPI_empty : pure_integer_hull P = ∅) :
    ∃ y : Fin n → ℝ,
      y ∈ (affineSpan ℝ P).direction ∧
        y ∉ Submodule.span ℝ (recessionCone P) := by
  let K : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (recessionCone P)
  let D : Submodule ℝ (Fin n → ℝ) := (affineSpan ℝ P).direction
  have hKD : K ≤ D := by
    -- Every recession direction lies in the affine direction, so the same holds for its span.
    rw [Submodule.span_le]
    intro r hr
    rcases hP_rational with ⟨m, A, b, hP_eq⟩
    have hr' :
        r ∈ recessionCone
          (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))) := by
      simpa [hP_eq] using hr
    have hdir' :
        r ∈
          (affineSpan ℝ
            (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ)))).direction :=
      recessionCone_subset_affineSpan_direction
        (A.map (Rat.castHom ℝ))
        (fun i ↦ (b i : ℝ))
        (by simpa [hP_eq] using hP_nonempty)
        hr'
    simpa [K, D, hP_eq] using hdir'
  have hdim_lt :
      Module.finrank ℝ K < Module.finrank ℝ D := by
    simpa [K, D] using
      finrank_span_recessionCone_lt_finrank_direction_affineSpan_of_pure_integer_hull_eq_empty
        P hP_nonempty hP_rational h_affine_integer hPI_empty
  have hD_not_le_K : ¬ D ≤ K := by
    intro hDK
    have hDK_eq : D = K := le_antisymm hDK hKD
    have hdim_eq : Module.finrank ℝ K = Module.finrank ℝ D := by
      rw [hDK_eq]
    exact (Nat.ne_of_lt hdim_lt) hdim_eq
  -- A strict finrank gap gives an actual direction vector that escapes the recession span.
  by_contra hno
  apply hD_not_le_K
  intro y hyD
  by_contra hyK
  exact hno ⟨y, hyD, hyK⟩

/-- Helper for Lemma 5.16: if `0 ∈ S`, then every point of `affineSpan ℝ S` already lies in the
linear span of `S`. -/
lemma affineSpan_subset_span_of_zero_mem
    (S : Set (Fin n → ℝ))
    (h0S : (0 : Fin n → ℝ) ∈ S) :
    (affineSpan ℝ S : Set (Fin n → ℝ)) ⊆ Submodule.span ℝ S := by
  intro x hx
  -- Use `0` as the affine base point so affine-hull membership becomes a direction statement.
  have h0Aff : (0 : Fin n → ℝ) ∈ affineSpan ℝ S := subset_affineSpan ℝ S h0S
  have hxDir : x - 0 ∈ (affineSpan ℝ S).direction :=
    AffineSubspace.vsub_mem_direction hx h0Aff
  have hdir : (affineSpan ℝ S).direction = Submodule.span ℝ S := by
    -- When `0 ∈ S`, the vector span is represented directly by the original points of `S`.
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0S]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [vsub_eq_sub] using hz
    · intro hy
      exact ⟨y, hy, by simp [vsub_eq_sub]⟩
  simpa [hdir] using hxDir

/-- Helper for Lemma 5.16: a point outside the span of a homogeneous rational polyhedron violates
some implicit-equality row of its defining system. -/
lemma existsImplicitEqualityRowNotVanishingOnOutsidePoint
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    {y : Fin n → ℝ}
    (hy :
      y ∉ Submodule.span ℝ
        (polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun _ ↦ (0 : ℝ)))) :
    ∃ i : {i // i ∈ implicit_equality_indices (A.map (Rat.castHom ℝ)) (fun _ ↦ (0 : ℝ))},
      ((implicit_equality_matrix (A.map (Rat.castHom ℝ)) (fun _ ↦ (0 : ℝ))) *ᵥ y) i ≠ 0 := by
  let B : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let C : Set (Fin n → ℝ) := polyhedron_le_set B (fun _ ↦ (0 : ℝ))
  have h0C : (0 : Fin n → ℝ) ∈ C := by
    -- The homogeneous system is always feasible at the origin.
    change B *ᵥ (0 : Fin n → ℝ) ≤ fun _ ↦ (0 : ℝ)
    intro i
    simp
  by_contra hno
  push Not at hno
  have hyImplicit :
      implicit_equality_matrix B (fun _ ↦ (0 : ℝ)) *ᵥ y =
        implicit_equality_rhs B (fun _ ↦ (0 : ℝ)) := by
    -- If every implicit row vanishes on `y`, then `y` satisfies the implicit subsystem.
    funext i
    have hi_zero :
        ((implicit_equality_matrix B (fun _ ↦ (0 : ℝ))) *ᵥ y) i = 0 := hno i
    simpa [implicit_equality_rhs_apply] using hi_zero
  have hyAff : y ∈ (affineSpan ℝ C : Set (Fin n → ℝ)) := by
    -- Chapter 3.17 identifies the affine hull of a polyhedron with its implicit equalities.
    rw [affineSpan_linear_inequality_solution_set_eq_implicit_equality_solution_set
      B (fun _ ↦ (0 : ℝ))]
    exact hyImplicit
  exact hy (affineSpan_subset_span_of_zero_mem C h0C hyAff)

/-- Helper for Lemma 5.16: the empty-branch separator can be chosen rational before the final
denominator clearing step. -/
lemma existsRationalDirectionOrthogonalRecession
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ ℤ^n).Nonempty)
    (hPI_empty : pure_integer_hull P = ∅) :
    ∃ aQ : Fin n → ℚ,
      ∃ y : Fin n → ℝ,
        y ∈ (affineSpan ℝ P).direction ∧
          (fun i ↦ (aQ i : ℝ)) ⬝ᵥ y ≠ 0 ∧
          ∀ r : Fin n → ℝ,
            r ∈ recessionCone P → (fun i ↦ (aQ i : ℝ)) ⬝ᵥ r = 0 := by
  obtain ⟨y, hyD, hyK⟩ :=
    existsDirectionOutsideRecessionSpan
      P hP_nonempty hP_rational h_affine_integer hPI_empty
  rcases hP_rational with ⟨m, A, b, hP_eq⟩
  let B : Matrix (Fin m) (Fin n) ℝ := A.map (Rat.castHom ℝ)
  let C : Set (Fin n → ℝ) := polyhedron_le_set B (fun _ ↦ (0 : ℝ))
  have hP_nonempty_poly :
      Set.Nonempty (polyhedron_le_set B (fun i ↦ (b i : ℝ))) := by
    simpa [B, hP_eq] using hP_nonempty
  have hrec_eq : recessionCone P = C := by
    -- Rewrite the recession cone through the homogeneous system attached to a rational
    -- presentation of `P`.
    calc
      recessionCone P = recessionCone (polyhedron_le_set B (fun i ↦ (b i : ℝ))) := by
        simp [B, hP_eq]
      _ = {r : Fin n → ℝ | B *ᵥ r ≤ 0} := by
        rw [polyhedron_recessionCone_eq_homogeneous_solution_set B (fun i ↦ (b i : ℝ))
          hP_nonempty_poly]
      _ = {r : Fin n → ℝ | B *ᵥ r ≤ fun _ ↦ (0 : ℝ)} := by
        ext r
        constructor <;> intro hr <;> simpa using hr
      _ = C := by
        rfl
  have hyC :
      y ∉ Submodule.span ℝ C := by
    simpa [C, hrec_eq] using hyK
  obtain ⟨i, hi_nonzero⟩ := existsImplicitEqualityRowNotVanishingOnOutsidePoint A hyC
  refine ⟨A i.1, y, hyD, ?_, ?_⟩
  · -- Route correction: choose a violating implicit row of the homogeneous recession system
    -- instead of rationalizing an arbitrary real functional.
    have hrow_nonzero : (B *ᵥ y) i.1 ≠ 0 := by
      simpa [implicit_equality_mulVec_apply] using hi_nonzero
    simpa [B, Matrix.mulVec, dotProduct] using hrow_nonzero
  · intro r hr
    have hi_imp : is_implicit_equality B (fun _ ↦ (0 : ℝ)) i.1 :=
      (mem_implicit_equality_indices_iff B (fun _ ↦ (0 : ℝ)) i.1).1 i.2
    have hrC : r ∈ C := by
      simpa [hrec_eq, C] using hr
    have hrow_zero : (B *ᵥ r) i.1 = 0 := by
      -- Implicit rows vanish on every recession direction because the homogeneous system has
      -- right-hand side `0`.
      have hr_le : B *ᵥ r ≤ fun _ ↦ (0 : ℝ) := by
        simpa [C, mem_polyhedron_le_set_iff] using hrC
      simpa using hi_imp hr_le
    simpa [B, Matrix.mulVec, dotProduct] using hrow_zero

lemma existsIntegralSystemOfEmptyPureIntegerHull
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ ℤ^n).Nonempty)
    (hPI_empty : pure_integer_hull P = ∅) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℤ,
      IsPureIntegerHullIntegralSystem P A b := by
  obtain ⟨aQ, y, hy_dir, hay_ne_zero, haQ_rec⟩ :=
    existsRationalDirectionOrthogonalRecession
      P hP_nonempty hP_rational h_affine_integer hPI_empty
  rcases h_affine_integer with ⟨z, hz_aff, hz_int⟩
  rcases (mem_integerVectors_iff (x := z)).1 hz_int with ⟨zInt, hzInt_eq⟩
  let d : ℕ := rational_vector_common_denominator aQ
  let a : Fin n → ℤ := common_denominator_scaled_vector aQ
  let aReal : Fin n → ℝ := fun i ↦ (a i : ℝ)
  let A : Matrix (Fin 2) (Fin n) ℤ :=
    fun i j ↦ if i = 0 then a j else -a j
  let b : Fin 2 → ℤ :=
    fun i ↦ if i = 0 then a ⬝ᵥ zInt - 1 else -(a ⬝ᵥ zInt)
  have hd_ne_zero : d ≠ 0 :=
    rationalVectorCommonDenominator_ne_zero (v := aQ)
  have hd_real_ne_zero : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_ne_zero
  have haReal_eq :
      aReal = (d : ℝ) • fun i ↦ (aQ i : ℝ) := by
    simpa [aReal, a] using commonDenominatorScaledVector_eq_smul_real (v := aQ)
  have haReal_ne : aReal ≠ 0 := by
    -- Clearing denominators preserves nonzeroness because the common denominator is positive.
    intro hzero
    rw [haReal_eq] at hzero
    have haQ_zero : (fun i ↦ (aQ i : ℝ)) = 0 :=
      (smul_eq_zero.mp hzero).resolve_left hd_real_ne_zero
    exact hay_ne_zero (by simp [haQ_zero])
  have hayReal_ne_zero : aReal ⬝ᵥ y ≠ 0 := by
    rw [haReal_eq]
    intro hzero
    apply hay_ne_zero
    have hscaled_zero :
        (d : ℝ) * ((fun i ↦ (aQ i : ℝ)) ⬝ᵥ y) = 0 := by
      simpa [dotProduct, Finset.mul_sum, mul_assoc] using hzero
    exact (mul_eq_zero.mp hscaled_zero).resolve_left hd_real_ne_zero
  have haReal_rec :
      ∀ r : Fin n → ℝ, r ∈ recessionCone P → aReal ⬝ᵥ r = 0 := by
    intro r hr
    calc
      aReal ⬝ᵥ r = ((d : ℝ) • fun i ↦ (aQ i : ℝ)) ⬝ᵥ r := by rw [haReal_eq]
      _ = (d : ℝ) * ((fun i ↦ (aQ i : ℝ)) ⬝ᵥ r) := by
            simp [dotProduct, Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [haQ_rec r hr, mul_zero]
  have hz_dot :
      aReal ⬝ᵥ z = ((a ⬝ᵥ zInt : ℤ) : ℝ) := by
    rw [hzInt_eq]
    simp [aReal, dotProduct]
  refine ⟨2, A, b, ?_⟩
  refine
    { hull_eq := ?_
      row_not_orthogonal := ?_
      row_valid := ?_ }
  · ext x
    constructor
    · intro hx
      simp [hPI_empty] at hx
    · rintro ⟨hx_poly, -⟩
      have hx0 : ((A.map (Int.castRingHom ℝ)) *ᵥ x) 0 ≤ (b 0 : ℝ) :=
        (mem_polyhedron_le_set_iff.mp hx_poly) 0
      have hx1 : ((A.map (Int.castRingHom ℝ)) *ᵥ x) 1 ≤ (b 1 : ℝ) :=
        (mem_polyhedron_le_set_iff.mp hx_poly) 1
      have hx0' : aReal ⬝ᵥ x ≤ ((a ⬝ᵥ zInt : ℤ) : ℝ) - 1 := by
        simpa [A, b, aReal, Matrix.mulVec, dotProduct] using hx0
      have hx1' : ((a ⬝ᵥ zInt : ℤ) : ℝ) ≤ aReal ⬝ᵥ x := by
        have hx1'' := hx1
        simp [A, b, Matrix.mulVec, dotProduct] at hx1''
        simpa [aReal, dotProduct] using hx1''
      exfalso
      have hx0'' : aReal ⬝ᵥ x < ((a ⬝ᵥ zInt : ℤ) : ℝ) := by
        have hstep : ((a ⬝ᵥ zInt : ℤ) : ℝ) - 1 < ((a ⬝ᵥ zInt : ℤ) : ℝ) := by
          norm_num
        exact lt_of_le_of_lt hx0' hstep
      exact (not_lt_of_ge hx1') hx0''
  · intro i
    -- Each of the two contradictory rows uses the same affine-direction witness `y`.
    refine ⟨y, hy_dir, ?_⟩
    fin_cases i
    · simpa [A, aReal] using hayReal_ne_zero
    · have hrow1 :
          (fun j : Fin n ↦ (A 1 j : ℝ)) = fun j ↦ -(aReal j) := by
        funext j
        simp [A, aReal]
      change (fun j : Fin n ↦ (A 1 j : ℝ)) ⬝ᵥ y ≠ 0
      rw [hrow1]
      simpa [dotProduct, Finset.sum_neg_distrib] using neg_ne_zero.mpr hayReal_ne_zero
  · intro i
    fin_cases i
    · obtain ⟨δ, hδ⟩ :=
        existsValidBoundOfNonpositiveOnRecessionCone
          P hP_nonempty hP_rational
          (c := aReal)
          (fun r hr ↦ by simp [haReal_rec r hr])
      refine ⟨δ, ?_⟩
      change is_valid_inequality P aReal δ
      exact hδ
    · obtain ⟨δ, hδ⟩ :=
        existsValidBoundOfNonpositiveOnRecessionCone
          P hP_nonempty hP_rational
          (c := fun j ↦ -(aReal j))
          (fun r hr ↦ by
            have hzero := haReal_rec r hr
            have hneg_zero : (fun j ↦ -(aReal j)) ⬝ᵥ r = 0 := by
              simpa [dotProduct, Finset.sum_neg_distrib, hzero]
            exact le_of_eq hneg_zero)
      have hrow1 :
          (fun j : Fin n ↦ (A 1 j : ℝ)) = fun j ↦ -(aReal j) := by
        funext j
        simp [A, aReal]
      refine ⟨δ, ?_⟩
      simpa [hrow1] using hδ

/-- Lemma 5.16. Let `P ⊆ ℝ^n` be a nonempty rational polyhedron such that
`aff(P) ∩ ℤ^n ≠ ∅`. Then `P_I`, represented here by `pure_integer_hull P`, admits an integral
description `pure_integer_hull P = {x : A x ≤ b} ∩ aff(P)` in which every row of `A` is not
orthogonal to `(affineSpan ℝ P).direction` and admits some valid upper bound on `P`. -/
theorem exists_integral_matrix_system_for_pure_integer_hull
    (P : Set (Fin n → ℝ))
    (hP_nonempty : P.Nonempty)
    (hP_rational : is_rational_polyhedron P)
    (h_affine_integer :
      ((affineSpan ℝ P : Set (Fin n → ℝ)) ∩ ℤ^n).Nonempty) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℤ,
      IsPureIntegerHullIntegralSystem P A b := by
  classical
  -- Route correction: follow the source proof's split on whether `pure_integer_hull P` is empty.
  by_cases hPI_empty : pure_integer_hull P = ∅
  · exact
      existsIntegralSystemOfEmptyPureIntegerHull
        (n := n) P hP_nonempty hP_rational h_affine_integer hPI_empty
  · have hPI_nonempty : (pure_integer_hull P).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hPI_empty
    exact
      existsIntegralSystemOfNonemptyPureIntegerHull
        (n := n) P hP_nonempty hP_rational hPI_nonempty

end Lemma516
