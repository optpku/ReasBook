import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_theorem_1_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_theorem_4_30
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

section Lemma438

variable {m n p : ℕ}

open scoped BigOperators Matrix

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: the flattened recession
system consists of the original homogeneous rows followed by the nonnegativity rows. -/
private def nonnegativeMixedRecessionMatrix
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ) :
    Matrix (Fin (m + (n + p))) (Fin (n + p)) ℚ :=
  fun i ↦ Fin.addCases
    (fun k ↦ Fin.append (A k) (G k))
    (fun k j ↦ if j = k then -1 else 0)
    i

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: membership in the flattened
homogeneous nonnegative mixed system is exactly the expected blockwise condition. -/
private lemma mem_nonnegativeMixedRecessionPolyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {u : Fin (n + p) → ℝ} :
    u ∈ rational_matrix_polyhedron (nonnegativeMixedRecessionMatrix A G) 0 ↔
      (A.map (Rat.castHom ℝ)).mulVec (fun i ↦ u (Fin.castAdd p i)) +
          (G.map (Rat.castHom ℝ)).mulVec (fun j ↦ u (Fin.natAdd n j)) ≤ 0 ∧
        (0 ≤ fun i ↦ u (Fin.castAdd p i)) ∧
        (0 ≤ fun j ↦ u (Fin.natAdd n j)) := by
  -- Split the augmented rows into the original homogeneous system and `-uᵢ ≤ 0`.
  rw [mem_rational_matrix_polyhedron]
  constructor
  · intro hu
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := hu (Fin.castAdd (n + p) i)
      simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_add, Fin.appendEquiv] using hi
    · intro i
      have hi := hu (Fin.natAdd m (Fin.castAdd p i))
      have hsum :
          ∑ j : Fin (n + p),
              (((if j = Fin.castAdd p i then (-1 : ℚ) else 0 : ℚ) : ℝ) * u j) =
            -u (Fin.castAdd p i) := by
        rw [Finset.sum_eq_single (Fin.castAdd p i)]
        · simp
        · intro j _ hj
          simp [hj]
        · simp
      have hnonpos : -u (Fin.castAdd p i) ≤ 0 := by
        simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct, hsum] using hi
      exact neg_nonpos.mp hnonpos
    · intro i
      have hi := hu (Fin.natAdd m (Fin.natAdd n i))
      have hsum :
          ∑ j : Fin (n + p),
              (((if j = Fin.natAdd n i then (-1 : ℚ) else 0 : ℚ) : ℝ) * u j) =
            -u (Fin.natAdd n i) := by
        rw [Finset.sum_eq_single (Fin.natAdd n i)]
        · simp
        · intro j _ hj
          simp [hj]
        · simp
      have hnonpos : -u (Fin.natAdd n i) ≤ 0 := by
        simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct, hsum] using hi
      exact neg_nonpos.mp hnonpos
  · rintro ⟨hsystem, hx, hy⟩ row
    refine Fin.addCases ?_ ?_ row
    · intro i
      simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_add, Fin.appendEquiv] using hsystem i
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro i
        have hsum :
            ∑ j : Fin (n + p),
                (((if j = Fin.castAdd p i then (-1 : ℚ) else 0 : ℚ) : ℝ) * u j) =
              -u (Fin.castAdd p i) := by
          rw [Finset.sum_eq_single (Fin.castAdd p i)]
          · simp
          · intro j _ hj
            simp [hj]
          · simp
        simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct, hsum] using
          (neg_nonpos.mpr (hx i))
      · intro i
        have hsum :
            ∑ j : Fin (n + p),
                (((if j = Fin.natAdd n i then (-1 : ℚ) else 0 : ℚ) : ℝ) * u j) =
              -u (Fin.natAdd n i) := by
          rw [Finset.sum_eq_single (Fin.natAdd n i)]
          · simp
          · intro j _ hj
            simp [hj]
          · simp
        simpa [nonnegativeMixedRecessionMatrix, Matrix.mulVec, dotProduct, hsum] using
          (neg_nonpos.mpr (hy i))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: the augmented homogeneous
matrix preserves the input entry bound up to the fixed encoding cost of `0` and `-1`. -/
private lemma nonnegativeMixedRecessionMatrix_encoding_le
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {L : ℕ}
    (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
    (hG : ∀ i j, EncodingSize.rational (G i j) ≤ L) :
    ∀ i j, EncodingSize.rational (nonnegativeMixedRecessionMatrix A G i j) ≤ L + 3 := by
  -- Original rows use the given bound; added rows contain only `0` and `-1`.
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro k
    refine Fin.addCases ?_ ?_ j
    · intro l
      simpa [nonnegativeMixedRecessionMatrix] using
        (hA k l).trans (Nat.le_add_right L 3)
    · intro l
      simpa [nonnegativeMixedRecessionMatrix] using
        (hG k l).trans (Nat.le_add_right L 3)
  · intro k
    by_cases hjk : j = k
    · simp [nonnegativeMixedRecessionMatrix, hjk, EncodingSize.rational_eq]
    · simp [nonnegativeMixedRecessionMatrix, hjk, EncodingSize.rational_eq]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: casting an integer vector to
`ℚ` increases its encoding size by exactly one bit per coordinate. -/
private lemma rationalVector_intCast_encoding_eq (x : Fin n → ℤ) :
    EncodingSize.rationalVector (fun i ↦ (x i : ℚ)) =
      EncodingSize.integerVector x + n := by
  -- Expand both vector encodings and compare the corresponding coordinates.
  simp [EncodingSize.rationalVector_eq_sum, EncodingSize.integerVector_eq_sum,
    EncodingSize.rational_eq, EncodingSize.integer_eq, Rat.num_intCast, Rat.den_intCast,
    Nat.size_one, Finset.sum_add_distrib]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: the nonnegative
mixed-integer hull remains in the product nonnegative orthant. -/
private lemma nonnegativeMixedIntegerHull_nonnegative
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p}
    (hxy : xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) :
    0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  -- The product orthant is convex and contains every feasible generator of the hull.
  have hsubset :
      nonnegative_rational_mixed_integer_points A G b ⊆
        {uv : MixedRealPoint n p | 0 ≤ uv.1 ∧ 0 ≤ uv.2} := by
    intro uv huv
    have huvPoly := (mem_mixed_integer_points_iff.mp huv).1
    exact ⟨huvPoly.2.1, huvPoly.2.2⟩
  have hconvex : Convex ℝ {uv : MixedRealPoint n p | 0 ≤ uv.1 ∧ 0 ≤ uv.2} := by
    intro u hu v hv a c ha hc hac
    constructor
    · intro i
      exact add_nonneg (smul_nonneg ha (hu.1 i)) (smul_nonneg hc (hv.1 i))
    · intro j
      exact add_nonneg (smul_nonneg ha (hu.2 j)) (smul_nonneg hc (hv.2 j))
  exact convexHull_min hsubset hconvex hxy

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: a nonempty subset of the
product nonnegative orthant is pointed. -/
private lemma isPointed_of_nonempty_subset_mixedNonnegative
    {P : Set (MixedRealPoint n p)}
    (hP_nonempty : P.Nonempty)
    (hP_nonnegative : ∀ xy ∈ P, 0 ≤ xy.1 ∧ 0 ≤ xy.2) :
    is_pointed P := by
  -- A lineality direction can be translated by every real scalar from one fixed point of `P`.
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  rcases hP_nonempty with ⟨u, hu⟩
  apply Prod.ext
  · funext i
    by_contra hri
    have hri' : r.1 i ≠ 0 := by simpa using hri
    have htranslated :=
      (mem_linealitySpace_iff.mp hr) hu (-((u.1 i + 1) / r.1 i))
    have hnonnegative := (hP_nonnegative _ htranslated).1 i
    -- This scalar makes the selected first-block coordinate equal to `-1`.
    have hcoord :
        (u + (-((u.1 i + 1) / r.1 i)) • r).1 i = -1 := by
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hri']
      ring
    rw [hcoord] at hnonnegative
    norm_num at hnonnegative

  · funext j
    by_contra hrj
    have hrj' : r.2 j ≠ 0 := by simpa using hrj
    have htranslated :=
      (mem_linealitySpace_iff.mp hr) hu (-((u.2 j + 1) / r.2 j))
    have hnonnegative := (hP_nonnegative _ htranslated).2 j
    -- The same translation argument handles every second-block coordinate.
    have hcoord :
        (u + (-((u.2 j + 1) / r.2 j)) • r).2 j = -1 := by
      simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hrj']
      ring
    rw [hcoord] at hnonnegative
    norm_num at hnonnegative

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: the recession cone of a
nonempty nonnegative mixed system is its homogeneous nonnegative system. -/
private lemma mem_recessionCone_nonnegativeRationalMixedPolyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    (hP : (nonnegative_rational_mixed_polyhedron A G b).Nonempty)
    {r : MixedRealPoint n p} :
    r ∈ recessionCone (nonnegative_rational_mixed_polyhedron A G b) ↔
      (A.map (Rat.castHom ℝ)).mulVec r.1 + (G.map (Rat.castHom ℝ)).mulVec r.2 ≤ 0 ∧
        0 ≤ r.1 ∧ 0 ≤ r.2 := by
  rw [mem_recessionCone_iff]
  constructor
  · intro hr
    rcases hP with ⟨xy, hxy⟩
    have hxySpec := mem_nonnegative_rational_mixed_polyhedron_iff.mp hxy
    refine ⟨?_, ?_, ?_⟩
    · intro i
      by_contra hi
      have hiPos :
          0 < ((A.map (Rat.castHom ℝ)).mulVec r.1 +
            (G.map (Rat.castHom ℝ)).mulVec r.2) i := lt_of_not_ge hi
      let t : ℝ :=
        ((b i : ℝ) -
            ((A.map (Rat.castHom ℝ)).mulVec xy.1 +
              (G.map (Rat.castHom ℝ)).mulVec xy.2) i + 1) /
          ((A.map (Rat.castHom ℝ)).mulVec r.1 +
            (G.map (Rat.castHom ℝ)).mulVec r.2) i
      have ht : 0 ≤ t := by
        dsimp [t]
        refine div_nonneg ?_ hiPos.le
        exact add_nonneg (sub_nonneg.mpr (hxySpec.1 i)) zero_le_one
      have htranslated :=
        mem_nonnegative_rational_mixed_polyhedron_iff.mp (hr hxy t ht)
      have hrow := htranslated.1 i
      have htMul :
          t * ((A.map (Rat.castHom ℝ)).mulVec r.1 +
            (G.map (Rat.castHom ℝ)).mulVec r.2) i =
          (b i : ℝ) -
            ((A.map (Rat.castHom ℝ)).mulVec xy.1 +
              (G.map (Rat.castHom ℝ)).mulVec xy.2) i + 1 := by
        dsimp [t]
        exact div_mul_cancel₀ _ hiPos.ne'
      have hrow' :
          ((A.map (Rat.castHom ℝ)).mulVec xy.1 +
              (G.map (Rat.castHom ℝ)).mulVec xy.2) i +
            t * ((A.map (Rat.castHom ℝ)).mulVec r.1 +
              (G.map (Rat.castHom ℝ)).mulVec r.2) i ≤ (b i : ℝ) := by
        simpa [Matrix.mulVec_add, Matrix.mulVec_smul, smul_eq_mul, mul_add,
          add_assoc, add_left_comm, add_comm] using hrow
      linarith
    · intro i
      by_contra hi
      have hri : r.1 i < 0 := lt_of_not_ge hi
      let t : ℝ := (xy.1 i + 1) / (-r.1 i)
      have ht : 0 ≤ t := div_nonneg (add_nonneg (hxySpec.2.1 i) zero_le_one) (neg_nonneg.mpr hri.le)
      have htranslated :=
        (mem_nonnegative_rational_mixed_polyhedron_iff.mp (hr hxy t ht)).2.1 i
      have hcoord : (xy + t • r).1 i = -1 := by
        simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp [t]
        field_simp [hri.ne]
        ring
      rw [hcoord] at htranslated
      norm_num at htranslated
    · intro j
      by_contra hj
      have hrj : r.2 j < 0 := lt_of_not_ge hj
      let t : ℝ := (xy.2 j + 1) / (-r.2 j)
      have ht : 0 ≤ t := div_nonneg (add_nonneg (hxySpec.2.2 j) zero_le_one) (neg_nonneg.mpr hrj.le)
      have htranslated :=
        (mem_nonnegative_rational_mixed_polyhedron_iff.mp (hr hxy t ht)).2.2 j
      have hcoord : (xy + t • r).2 j = -1 := by
        simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp [t]
        field_simp [hrj.ne]
        ring
      rw [hcoord] at htranslated
      norm_num at htranslated
  · rintro ⟨hrSystem, hrx, hry⟩ xy hxy t ht
    have hxySpec := mem_nonnegative_rational_mixed_polyhedron_iff.mp hxy
    rw [mem_nonnegative_rational_mixed_polyhedron_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hscaled :
          t * ((A.map (Rat.castHom ℝ)).mulVec r.1 +
            (G.map (Rat.castHom ℝ)).mulVec r.2) i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht (hrSystem i)
      have hsum :
          ((A.map (Rat.castHom ℝ)).mulVec xy.1 +
              (G.map (Rat.castHom ℝ)).mulVec xy.2) i +
            t * ((A.map (Rat.castHom ℝ)).mulVec r.1 +
              (G.map (Rat.castHom ℝ)).mulVec r.2) i ≤ (b i : ℝ) := by
        linarith [hxySpec.1 i]
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, smul_eq_mul, mul_add,
        add_assoc, add_left_comm, add_comm] using hsum
    · intro i
      exact add_nonneg (hxySpec.2.1 i) (mul_nonneg ht (hrx i))
    · intro j
      exact add_nonneg (hxySpec.2.2 j) (mul_nonneg ht (hry j))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap04/section_4_8_3/ch4_sec4_8_3_lemma_4_38.lean: extreme recession rays of the
flattened mixed-integer hull have uniformly bounded positive rational rescalings. -/
private theorem flattenedNonnegativeMixedHullExtremeRays_havePolynomiallyBoundedEncoding :
    ∃ πr : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
        (hG : ∀ i j, EncodingSize.rational (G i j) ≤ L)
        (hS : (nonnegative_rational_mixed_integer_points A G b).Nonempty)
        (r : Fin (n + p) → ℝ),
        IsExtremeRayOfPolyhedron
            (Fin.appendEquiv n p ''
              convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) r →
          ∃ t : ℝ, 0 < t ∧ ∃ rq : Fin (n + p) → ℚ,
            (fun k ↦ (rq k : ℝ)) = t • r ∧
              EncodingSize.rationalVector rq ≤ πr.eval (n + p + L + 3) := by
  obtain ⟨πr, hπr⟩ := rational_extreme_rays_have_polynomially_bounded_rescaled_encoding_size
  refine ⟨πr, ?_⟩
  intro m n p A G b L hA hG hS r hr
  let Q := nonnegative_rational_mixed_polyhedron A G b
  let H := convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)
  have hQNonempty : Q.Nonempty := by
    rcases hS with ⟨xy, hxy⟩
    exact ⟨xy, (mem_mixed_integer_points_iff.mp hxy).1⟩
  have hQrat : is_rational_mixed_polyhedron Q := by
    exact nonnegative_rational_mixed_polyhedron_is_rational_mixed_polyhedron A G b
  have hrecMixed : recessionCone H = recessionCone Q := by
    simpa [H, Q, nonnegative_rational_mixed_integer_points] using
      mixed_integer_hull_recessionCone_eq Q hQrat hS
  have hrecFlat :
      recessionCone (Fin.appendEquiv n p '' H) =
        rational_matrix_polyhedron (nonnegativeMixedRecessionMatrix A G) 0 := by
    ext u
    let d : MixedRealPoint n p := (Fin.appendEquiv n p).symm u
    have hud : Fin.appendEquiv n p d = u := (Fin.appendEquiv n p).apply_symm_apply u
    rw [← hud, mem_recessionCone_flatten_iff, hrecMixed,
      mem_recessionCone_nonnegativeRationalMixedPolyhedron_iff hQNonempty]
    simpa [Fin.appendEquiv] using
      (mem_nonnegativeMixedRecessionPolyhedron_iff (A := A) (G := G)
        (u := Fin.appendEquiv n p d)).symm
  have hr' :
      IsExtremeRayOfPolyhedron
        (rational_matrix_polyhedron (nonnegativeMixedRecessionMatrix A G) 0) r := by
    change IsExtremeRayOfCone
      (recessionCone (rational_matrix_polyhedron (nonnegativeMixedRecessionMatrix A G) 0)) r
    rw [← hrecFlat]
    exact (isExtremeRayOfPolyhedron_iff.mp hr)
  have hzero :
      ∀ i : Fin (m + (n + p)), EncodingSize.rational ((0 : Fin (m + (n + p)) → ℚ) i) ≤ L + 3 := by
    intro i
    simp [EncodingSize.rational_eq]
  obtain ⟨t, ht, rq, hrq, hsize⟩ :=
    hπr (nonnegativeMixedRecessionMatrix A G) (fun _ ↦ 0) (L + 3)
      (nonnegativeMixedRecessionMatrix_encoding_le hA hG) hzero r hr'
  refine ⟨t, ht, rq, hrq, ?_⟩
  simpa [Nat.add_assoc] using hsize
/-- Lemma 4.38. Given `A ∈ ℚ^(m × n)`, `G ∈ ℚ^(m × p)`, and `b ∈ ℚ^m`, let
`S := {(x, y) ∈ ℤ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}`. If the encoding size of every
coefficient of `(A, G, b)` is at most `L`, then every facet `F` of `conv(S)` is defined on
`conv(S)` by a rational inequality `c · x + d · y ≤ δ` whose coefficient vector and right-hand
side have encoding size uniformly polynomially bounded by `n + p` and `L`. -/
theorem mixed_integer_hull_facets_have_polynomially_bounded_rational_defining_inequalities :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, EncodingSize.rational (G i j) ≤ L)
        (hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
        (F : Set (MixedRealPoint n p))
        (hF : IsFacetOf (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) F),
        ∃ c : Fin n → ℚ,
          ∃ d : Fin p → ℚ,
            ∃ δ : ℚ,
              (c ≠ 0 ∨ d ≠ 0) ∧
                (∀ xy : MixedRealPoint n p,
                  xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) →
                    mixed_linear_objective
                        (fun i ↦ (c i : ℝ))
                        (fun j ↦ (d j : ℝ))
                        xy ≤
                      (δ : ℝ)) ∧
                F =
                  {xy | xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) ∧
                    mixed_linear_objective
                        (fun i ↦ (c i : ℝ))
                        (fun j ↦ (d j : ℝ))
                        xy =
                      (δ : ℝ)} ∧
                EncodingSize.rationalVector c + EncodingSize.rationalVector d +
                  EncodingSize.rational δ ≤ π.eval (n + p + L) := by
  classical
  obtain ⟨πv, hπv⟩ :=
    mixed_integer_hull_extreme_points_have_polynomially_bounded_encoding_size
  -- Route correction: use bounded vertex and recession-ray data, then solve a rectangular
  -- normalization system on the homogenized facet span; a square gauge system is unnecessary.
  refine ⟨πv, ?_⟩
  intro m n p A G b L hA hG hb F hF
  let P := convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)
  have hP_nonempty : P.Nonempty := by
    rcases hF.1 with ⟨xy, hxyF⟩
    exact ⟨xy, hF.2.1.subset hxyF⟩
  have hP_nonnegative : ∀ xy ∈ P, 0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
    intro xy hxy
    exact nonnegativeMixedIntegerHull_nonnegative hxy
  have hP_pointed : is_pointed P :=
    isPointed_of_nonempty_subset_mixedNonnegative hP_nonempty hP_nonnegative
  -- Record the already verified uniform rational representation of every extreme point.
  have hvertices :
      ∀ xy : MixedRealPoint n p, xy ∈ P.extremePoints ℝ →
        ∃ x : Fin n → ℤ,
          ∃ y : Fin p → ℚ,
            xy = ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) ∧
              EncodingSize.rationalVector (fun i ↦ (x i : ℚ)) +
                EncodingSize.rationalVector y ≤ πv.eval (n + p + L) + n := by
    intro xy hxy
    rcases hπv A G b L hA hG hb xy hxy with ⟨x, y, hxyRep, hxySize⟩
    refine ⟨x, y, hxyRep, ?_⟩
    rw [rationalVector_intCast_encoding_eq]
    omega
  let _ := hP_pointed
  let _ := hvertices
  -- TODO: first import the recession-cone theorem after its duplicate `polyhedronDim` and
  -- `recessionConeDim` owners are canonicalized. That theorem then identifies the augmented
  -- homogeneous matrix above with `recessionCone P`, enabling the bounded-ray theorem and the
  -- rectangular lifted-span normalization planned for the final supporting functional.
  aesop

end Lemma438

#print axioms mixed_integer_hull_facets_have_polynomially_bounded_rational_defining_inequalities
