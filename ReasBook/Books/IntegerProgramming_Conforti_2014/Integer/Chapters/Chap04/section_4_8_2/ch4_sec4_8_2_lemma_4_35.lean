import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.CommonDenominator
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_38
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_corollary_3_42
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tools such as
-- `lean_leansearch`, so the statement below follows the local Chapter 1 encoding conventions and
-- the Chapter 4 product-coordinate model for mixed-integer feasible sets.

section Lemma435

variable {m n p : ℕ}

open scoped BigOperators Matrix

/-- The nonnegative mixed polyhedron
`{(x, y) ∈ ℝ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}` attached to rational data `A`,
`G`, and `b`, expressed as a source-facing nonnegativity specialization of the Chapter 4.1
mixed-polyhedron owner. -/
def nonnegative_rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Set (MixedRealPoint n p) :=
  {xy | xy ∈ rational_mixed_polyhedron A G b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2}

/-- The mixed-integer feasible set
`{(x, y) ∈ ℤ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}` inside `ℝ^n × ℝ^p`, obtained
from the canonical mixed-integer-points owner applied to the nonnegative mixed polyhedron. -/
def nonnegative_rational_mixed_integer_points
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Set (MixedRealPoint n p) :=
  mixed_integer_points (nonnegative_rational_mixed_polyhedron A G b)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the flattened coefficient matrix for a nonnegative rational mixed system. -/
private def nonnegativeMixedFlatMatrix
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ) :
    Matrix (Fin (m + (n + p))) (Fin (n + p)) ℚ :=
  fun i ↦ Fin.addCases
    (fun k ↦ Fin.append (A k) (G k))
    (fun k j ↦ if j = k then -1 else 0)
    i

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the flattened right-hand side for a nonnegative rational mixed system. -/
private def nonnegativeMixedFlatRhs
    (b : Fin m → ℚ) : Fin (m + (n + p)) → ℚ :=
  Fin.addCases b (fun _ ↦ 0)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the explicit flattened system presents exactly the original inequalities and coordinatewise
nonnegativity conditions. -/
private lemma memNonnegativeMixedFlatPolyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {u : Fin (n + p) → ℝ} :
    u ∈ rational_matrix_polyhedron (nonnegativeMixedFlatMatrix A G)
        (nonnegativeMixedFlatRhs b) ↔
      (Fin.appendEquiv n p).symm u ∈ nonnegative_rational_mixed_polyhedron A G b := by
  rw [mem_rational_matrix_polyhedron]
  constructor
  · intro hu
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := hu (Fin.castAdd (n + p) i)
      simpa [nonnegativeMixedFlatMatrix, nonnegativeMixedFlatRhs, Matrix.mulVec,
        dotProduct, Fin.sum_univ_add, Fin.appendEquiv] using hi
    · intro j
      have hj := hu (Fin.natAdd m (Fin.castAdd p j))
      have hsum :
          ∑ k : Fin (n + p),
              (((if k = Fin.castAdd p j then (-1 : ℚ) else 0 : ℚ) : ℝ) * u k) =
            -u (Fin.castAdd p j) := by
        rw [Finset.sum_eq_single (Fin.castAdd p j)]
        · simp
        · intro k _ hk
          simp [hk]
        · simp
      have hj' : -u (Fin.castAdd p j) ≤ 0 := by
        simpa [nonnegativeMixedFlatMatrix, nonnegativeMixedFlatRhs, Matrix.mulVec,
          dotProduct, Fin.appendEquiv, hsum] using hj
      exact neg_nonpos.mp hj'
    · intro j
      have hj := hu (Fin.natAdd m (Fin.natAdd n j))
      have hsum :
          ∑ k : Fin (n + p),
              (((if k = Fin.natAdd n j then (-1 : ℚ) else 0 : ℚ) : ℝ) * u k) =
            -u (Fin.natAdd n j) := by
        rw [Finset.sum_eq_single (Fin.natAdd n j)]
        · simp
        · intro k _ hk
          simp [hk]
        · simp
      have hj' : -u (Fin.natAdd n j) ≤ 0 := by
        simpa [nonnegativeMixedFlatMatrix, nonnegativeMixedFlatRhs, Matrix.mulVec,
          dotProduct, Fin.appendEquiv, hsum] using hj
      exact neg_nonpos.mp hj'
  · rintro ⟨hmain, hx, hy⟩
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro i
      simpa [nonnegativeMixedFlatMatrix, nonnegativeMixedFlatRhs, Matrix.mulVec,
        dotProduct, Fin.sum_univ_add, Fin.appendEquiv] using hmain i
    · intro k
      have hk : 0 ≤ u k := by
        refine Fin.addCases ?_ ?_ k
        · intro j
          simpa [Fin.appendEquiv] using hx j
        · intro j
          simpa [Fin.appendEquiv] using hy j
      have hsum :
          ∑ j : Fin (n + p),
              (((if j = k then (-1 : ℚ) else 0 : ℚ) : ℝ) * u j) = -u k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          simp [hj]
        · simp
      simpa [nonnegativeMixedFlatMatrix, nonnegativeMixedFlatRhs, Matrix.mulVec,
        dotProduct, hsum] using (neg_nonpos.mpr hk)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the augmented flattened system has the same entry bound up to the fixed cost of `0` and `-1`. -/
private lemma nonnegativeMixedFlatMatrix_encoding_le
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {L : ℕ}
    (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
    (hG : ∀ i j, EncodingSize.rational (G i j) ≤ L) :
    ∀ i j, EncodingSize.rational (nonnegativeMixedFlatMatrix A G i j) ≤ L + 3 := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro k
    refine Fin.addCases ?_ ?_ j
    · intro l
      simpa [nonnegativeMixedFlatMatrix] using
        (hA k l).trans (Nat.le_add_right L 3)
    · intro l
      simpa [nonnegativeMixedFlatMatrix] using
        (hG k l).trans (Nat.le_add_right L 3)
  · intro k
    by_cases hjk : j = k
    · simp [nonnegativeMixedFlatMatrix, hjk, EncodingSize.rational_eq]
    · simp [nonnegativeMixedFlatMatrix, hjk, EncodingSize.rational_eq]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the augmented flattened right-hand side has the same entry bound up to a fixed constant. -/
private lemma nonnegativeMixedFlatRhs_encoding_le
    {b : Fin m → ℚ} {n p L : ℕ}
    (hb : ∀ i, EncodingSize.rational (b i) ≤ L) :
    ∀ i, EncodingSize.rational (nonnegativeMixedFlatRhs (n := n) (p := p) b i) ≤ L + 3 := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro k
    simpa [nonnegativeMixedFlatRhs] using
      (hb k).trans (Nat.le_add_right L 3)
  · intro k
    simp [nonnegativeMixedFlatRhs, EncodingSize.rational_eq]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
every rational matrix polyhedron is convex. -/
private lemma rationalMatrixPolyhedron_convex
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    Convex ℝ (rational_matrix_polyhedron A b) := by
  intro x hx y hy a c ha hc hac i
  calc
    ((A.map (Rat.castHom ℝ)) *ᵥ (a • x + c • y)) i =
        a * ((A.map (Rat.castHom ℝ)) *ᵥ x) i +
          c * ((A.map (Rat.castHom ℝ)) *ᵥ y) i := by
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        ∑ j, (A i j : ℝ) * (a * x j + c * y j) =
            ∑ j, (a * ((A i j : ℝ) * x j) + c * ((A i j : ℝ) * y j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        _ = a * ∑ j, (A i j : ℝ) * x j + c * ∑ j, (A i j : ℝ) * y j := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ a * (b i : ℝ) + c * (b i : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = (b i : ℝ) := by rw [← add_mul, hac, one_mul]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
a nonempty polyhedron contained in the nonnegative orthant is pointed. -/
private lemma isPointed_of_nonempty_of_nonnegative
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_nonnegative : ∀ u ∈ P, 0 ≤ u) :
    is_pointed P := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  rcases hP_nonempty with ⟨u, hu⟩
  funext i
  by_contra hri
  have hri' : r i ≠ 0 := by simpa using hri
  have htranslated :=
    (mem_linealitySpace_iff.mp hr) hu (-((u i + 1) / r i))
  have hnonnegative := hP_nonnegative _ htranslated i
  have hcoord :
      (u + (-((u i + 1) / r i)) • r) i = -1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hri']
    ring
  rw [hcoord] at hnonnegative
  norm_num at hnonnegative

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the common denominator of a rational vector is positive. -/
private lemma rationalVectorCommonDenominator_pos
    {d : ℕ} (v : Fin d → ℚ) :
    0 < rational_vector_common_denominator v := by
  -- Every coordinate denominator is positive, so their finite least common multiple is nonzero.
  have hden :
      ∀ i ∈ (Finset.univ : Finset (Fin d)), (v i).den ≠ 0 := by
    intro i _
    exact Nat.ne_of_gt (Rat.den_pos (v i))
  have hne : rational_vector_common_denominator v ≠ 0 := by
    rw [rational_vector_common_denominator]
    exact Finset.lcm_ne_zero_iff.mpr hden
  exact Nat.pos_of_ne_zero hne

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
clearing a rational vector's common denominator agrees with real scalar multiplication. -/
private lemma commonDenominatorScaledVector_eq_smul_real
    {d : ℕ} (v : Fin d → ℚ) :
    (fun i ↦ (common_denominator_scaled_vector v i : ℝ)) =
      (rational_vector_common_denominator v : ℝ) • (fun i ↦ (v i : ℝ)) := by
  -- Cast the existing rational identity coordinatewise to the reals.
  ext i
  have hi := congrFun (common_denominator_scaled_vector_eq_smul v) i
  have hi' := congrArg (Rat.castHom ℝ) hi
  simpa only [map_intCast, map_mul, map_natCast, Pi.smul_apply, smul_eq_mul] using hi'

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
every recession direction of a nonempty set in the nonnegative orthant is coordinatewise
nonnegative. -/
private lemma recessionDirection_nonnegative_of_nonnegative
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP_nonempty : P.Nonempty)
    (hP_nonnegative : ∀ u ∈ P, 0 ≤ u)
    {r : Fin d → ℝ} (hr : r ∈ recessionCone P) :
    0 ≤ r := by
  -- A negative coordinate would become negative after translating a feasible point far enough.
  rcases hP_nonempty with ⟨u, hu⟩
  intro i
  by_contra hri
  have hri_neg : r i < 0 := lt_of_not_ge hri
  let a : ℝ := (u i + 1) / (-r i)
  have ha : 0 ≤ a := by
    dsimp [a]
    have hui : 0 ≤ u i := hP_nonnegative u hu i
    have hnum : 0 ≤ u i + 1 := by linarith
    exact div_nonneg hnum (neg_nonneg.mpr hri_neg.le)
  have htranslated := (mem_recessionCone_iff.mp hr) hu a ha
  have hcoordinate := hP_nonnegative _ htranslated i
  have hri_ne : r i ≠ 0 := ne_of_lt hri_neg
  have hcoord : (u + a • r) i = -1 := by
    dsimp [a]
    change u i + ((u i + 1) / (-r i)) * r i = -1
    field_simp [hri_ne]
    ring
  rw [hcoord] at hcoordinate
  norm_num at hcoordinate

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
subtracting part of one coefficient in a nonnegative recession decomposition preserves
feasibility. -/
private lemma sub_scaledRay_mem_of_decomposition
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} {q : ℕ}
    (r : Fin q → E) (c : Fin q → ℝ)
    (hv : v ∈ P)
    (hr : ∀ j, r j ∈ recessionCone P)
    (hc : ∀ j, 0 ≤ c j)
    (hu : u = v + ∑ j, c j • r j)
    (j : Fin q) {t : ℝ} (htc : t ≤ c j) :
    u - t • r j ∈ P := by
  -- Separate the selected summand and keep the remainder inside the recession cone.
  have htail :
      ∑ k ∈ (Finset.univ.erase j), c k • r k ∈ recessionCone P := by
    change ∑ k ∈ (Finset.univ.erase j), c k • r k ∈ recessionPointedCone ℝ P
    exact Submodule.sum_mem _ fun k _ ↦ smul_mem_recessionCone (hr k) (hc k)
  have hhead : (c j - t) • r j ∈ recessionCone P :=
    smul_mem_recessionCone (hr j) (sub_nonneg.mpr htc)
  have hdirection :
      (c j - t) • r j + ∑ k ∈ (Finset.univ.erase j), c k • r k ∈
        recessionCone P := by
    change (c j - t) • r j + ∑ k ∈ (Finset.univ.erase j), c k • r k ∈
      recessionPointedCone ℝ P
    exact add_mem hhead htail
  have htranslated := (mem_recessionCone_iff.mp hdirection) hv 1 zero_le_one
  have hsum :
      ∑ k, c k • r k = c j • r j + ∑ k ∈ (Finset.univ.erase j), c k • r k := by
    rw [add_comm]
    exact (Finset.sum_erase_add Finset.univ (fun k ↦ c k • r k) (Finset.mem_univ j)).symm
  have heq : u - t • r j =
      v + ((c j - t) • r j + ∑ k ∈ (Finset.univ.erase j), c k • r k) := by
    rw [hu, hsum]
    module
  rw [heq]
  simpa only [one_smul] using htranslated

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the real absolute value of a rational is strictly smaller than two to its encoding size. -/
private lemma abs_ratCast_lt_twoPow_encoding (q : ℚ) :
    |(q : ℝ)| < (2 : ℝ) ^ EncodingSize.rational q := by
  -- The positive denominator can only decrease the numerator's absolute value.
  have hden : (1 : ℝ) ≤ (q.den : ℝ) := by
    exact_mod_cast q.den_pos
  have hnum :
      ((q.num.natAbs : ℕ) : ℝ) < (2 : ℝ) ^ Nat.size q.num.natAbs := by
    exact_mod_cast Nat.lt_size_self q.num.natAbs
  have hquotient :
      ((q.num.natAbs : ℕ) : ℝ) / (q.den : ℝ) ≤
        (q.num.natAbs : ℕ) := by
    exact div_le_self (Nat.cast_nonneg q.num.natAbs) hden
  have hpow :
      (2 : ℝ) ^ Nat.size q.num.natAbs ≤
        (2 : ℝ) ^ EncodingSize.rational q := by
    apply pow_le_pow_right₀ (by norm_num)
    simp only [EncodingSize.rational_eq]
    omega
  rw [Rat.cast_def, abs_div]
  have hnumAbs : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [← Int.cast_abs]
    simp
  rw [hnumAbs, abs_of_nonneg (Nat.cast_nonneg q.den)]
  exact lt_of_le_of_lt hquotient (lt_of_lt_of_le hnum hpow)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
a coarse binary-size bound for a nonnegative integer dominated by one vertex term and finitely
many ray terms. -/
private lemma integerEncoding_le_of_lt_twoPow_add_mul
    (z V q R : ℕ)
    (hz : z < 2 ^ V + q * 2 ^ R) :
    Nat.size z + 1 ≤ V + q + R + 4 := by
  -- Dominate both summands by a common power of two and apply the characterization of `Nat.size`.
  have hq : q < 2 ^ (q + 1) := by
    exact lt_of_lt_of_le q.lt_two_pow_self
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right q 1))
  have hleft : 2 ^ V ≤ 2 ^ (V + q + R + 2) := by
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hright : q * 2 ^ R < 2 ^ (V + q + R + 2) := by
    calc
      q * 2 ^ R < 2 ^ (q + 1) * 2 ^ R := Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ = 2 ^ (q + 1 + R) := by rw [← pow_add]
      _ ≤ 2 ^ (V + q + R + 2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
  have hzpow : z < 2 ^ (V + q + R + 3) := by
    calc
      z < 2 ^ V + q * 2 ^ R := hz
      _ < 2 ^ (V + q + R + 2) + 2 ^ (V + q + R + 2) :=
        Nat.add_lt_add_of_le_of_lt hleft hright
      _ = 2 ^ (V + q + R + 3) := by rw [← two_mul, ← pow_succ']
  have hsize : Nat.size z ≤ V + q + R + 3 := Nat.size_le.mpr hzpow
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
concatenating the two blocks of a mixed point is linear. -/
private lemma mixedPointFlattening_isLinearMap :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  constructor
  · intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the canonical linear equivalence that concatenates the two blocks of a mixed point. -/
private abbrev mixedPointFlattening (n p : ℕ) :
    MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
  (Fin.appendEquiv n p).toLinearEquiv mixedPointFlattening_isLinearMap

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the canonical mixed-point linear equivalence agrees with `Fin.appendEquiv`. -/
private lemma mixedPointFlattening_apply (xy : MixedRealPoint n p) :
    mixedPointFlattening n p xy = Fin.appendEquiv n p xy := by
  rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
flattened mixed-integer membership is ambient flattened feasibility plus integrality of the first
coordinate block. -/
private lemma mem_image_nonnegativeMixedIntegerPoints_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ} {u : Fin (n + p) → ℝ} :
    u ∈ mixedPointFlattening n p '' nonnegative_rational_mixed_integer_points A G b ↔
      u ∈ rational_matrix_polyhedron (nonnegativeMixedFlatMatrix A G)
          (nonnegativeMixedFlatRhs b) ∧
        (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    have hparts := mem_mixed_integer_points_iff.mp hxy
    constructor
    · rw [memNonnegativeMixedFlatPolyhedron_iff]
      simpa [mixedPointFlattening_apply] using hparts.1
    · rw [mem_mixed_integer_lattice_iff] at hparts
      simpa [mixedPointFlattening_apply, Fin.appendEquiv, Function.comp_def] using hparts.2
  · rintro ⟨huP, huInt⟩
    let xy : MixedRealPoint n p := (Fin.appendEquiv n p).symm u
    have hxyP : xy ∈ nonnegative_rational_mixed_polyhedron A G b := by
      exact memNonnegativeMixedFlatPolyhedron_iff.mp huP
    have hxyInt : xy ∈ mixed_integer_lattice n p := by
      rw [mem_mixed_integer_lattice_iff]
      simpa [xy, Fin.appendEquiv, Function.comp_def] using huInt
    refine ⟨xy, mem_mixed_integer_points_iff.mpr ⟨hxyP, hxyInt⟩, ?_⟩
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [xy, mixedPointFlattening_apply, Fin.appendEquiv]
    · intro j
      simp [xy, mixedPointFlattening_apply, Fin.appendEquiv]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the selector row on the first flattened block evaluates to its selected coordinate. -/
private lemma sumFirstBlockSelectorRow_eq_active
    (u : Fin (n + p) → ℝ) (i : Fin n) (c : ℚ) :
    ∑ j : Fin (n + p),
        (((Fin.append
            (fun l : Fin n ↦ if l = i then c else 0)
            (fun _ : Fin p ↦ 0) j : ℚ) : ℝ) * u j) =
      (c : ℝ) * u (Fin.castAdd p i) := by
  -- Split the two coordinate blocks and collapse the unique nonzero term in the first block.
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the flattened nonnegative system augmented by paired selector rows fixing the integral block. -/
private def fixedIntegerBlockFlatMatrix
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ) :
    Matrix (Fin ((m + (n + p)) + (n + n))) (Fin (n + p)) ℚ :=
  fun i ↦ Fin.addCases
    (nonnegativeMixedFlatMatrix A G)
    (Fin.addCases
      (fun i' ↦ Fin.append (fun j ↦ if j = i' then 1 else 0) (fun _ ↦ 0))
      (fun i' ↦ Fin.append (fun j ↦ if j = i' then -1 else 0) (fun _ ↦ 0)))
    i

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the right-hand side of the flattened system whose first block is fixed to `x`. -/
private def fixedIntegerBlockFlatRhs
    (b : Fin m → ℚ) (x : Fin n → ℤ) :
    Fin ((m + (n + p)) + (n + n)) → ℚ :=
  fun i ↦ Fin.addCases
    (nonnegativeMixedFlatRhs b)
    (Fin.addCases (fun i' ↦ x i') (fun i' ↦ -(x i')))
    i

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the lower selector row of the fixed-block matrix is the negative first-block selector. -/
private lemma fixedIntegerBlockFlatMatrix_lowerRow
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ) (i : Fin n) :
    fixedIntegerBlockFlatMatrix A G
        (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) =
      Fin.append (fun j ↦ if j = i then -1 else 0) (fun _ ↦ 0) := by
  funext j
  rw [fixedIntegerBlockFlatMatrix, Fin.addCases_right, Fin.addCases_right]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the lower selector row evaluates to the negative selected coordinate. -/
private lemma fixedIntegerBlockFlatMatrix_lowerRow_mulVec
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ) (u : Fin (n + p) → ℝ) (i : Fin n) :
    (((fixedIntegerBlockFlatMatrix A G).map (Rat.castHom ℝ)) *ᵥ u)
        (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) =
      (-1 : ℝ) * u (Fin.castAdd p i) := by
  rw [Matrix.mulVec, dotProduct]
  calc
    ∑ j,
        ((fixedIntegerBlockFlatMatrix A G
          (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) j : ℚ) : ℝ) * u j =
        ∑ j,
          ((Fin.append (fun l ↦ if l = i then -1 else 0) (fun _ ↦ 0) j : ℚ) : ℝ) *
            u j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [congrFun (fixedIntegerBlockFlatMatrix_lowerRow A G i) j]
    _ = (-1 : ℝ) * u (Fin.castAdd p i) := by
      simpa using sumFirstBlockSelectorRow_eq_active u i (-1)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the two selector right-hand sides are the prescribed integer coordinate and its negative. -/
private lemma fixedIntegerBlockFlatRhs_selectorRows
    (b : Fin m → ℚ) (x : Fin n → ℤ) (i : Fin n) :
    fixedIntegerBlockFlatRhs (p := p) b x
        (Fin.natAdd (m + (n + p)) (Fin.castAdd n i)) = (x i : ℚ) ∧
      fixedIntegerBlockFlatRhs (p := p) b x
        (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) = -(x i : ℚ) := by
  constructor
  · rw [fixedIntegerBlockFlatRhs, Fin.addCases_right, Fin.addCases_left]
  · rw [fixedIntegerBlockFlatRhs, Fin.addCases_right, Fin.addCases_right]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
membership in the fixed-block augmented system is ambient feasibility together with equality of
the first block to the prescribed integer vector. -/
private lemma mem_fixedIntegerBlockFlatPolyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ} {x : Fin n → ℤ} {u : Fin (n + p) → ℝ} :
    u ∈ rational_matrix_polyhedron (fixedIntegerBlockFlatMatrix A G)
        (fixedIntegerBlockFlatRhs b x) ↔
      u ∈ rational_matrix_polyhedron (nonnegativeMixedFlatMatrix A G)
          (nonnegativeMixedFlatRhs b) ∧
        ∀ i : Fin n, u (Fin.castAdd p i) = (x i : ℝ) := by
  rw [mem_rational_matrix_polyhedron]
  constructor
  · intro hu
    constructor
    · rw [mem_rational_matrix_polyhedron]
      intro row
      have hrow := hu (Fin.castAdd (n + n) row)
      simpa [fixedIntegerBlockFlatMatrix, fixedIntegerBlockFlatRhs, Matrix.mulVec,
        dotProduct] using hrow
    · intro i
      have hupper := hu (Fin.natAdd (m + (n + p)) (Fin.castAdd n i))
      have hlower := hu (Fin.natAdd (m + (n + p)) (Fin.natAdd n i))
      have hupper' : u (Fin.castAdd p i) ≤ (x i : ℝ) := by
        have hrow :
            (((fixedIntegerBlockFlatMatrix A G).map (Rat.castHom ℝ)) *ᵥ u)
                (Fin.natAdd (m + (n + p)) (Fin.castAdd n i)) =
              u (Fin.castAdd p i) := by
          simpa [fixedIntegerBlockFlatMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
            using sumFirstBlockSelectorRow_eq_active u i 1
        simpa only [hrow, (fixedIntegerBlockFlatRhs_selectorRows (p := p) b x i).1,
          Rat.cast_intCast] using hupper
      have hlower' : -(u (Fin.castAdd p i)) ≤ -(x i : ℝ) := by
        have hrow :
            (((fixedIntegerBlockFlatMatrix A G).map (Rat.castHom ℝ)) *ᵥ u)
                (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          exact fixedIntegerBlockFlatMatrix_lowerRow_mulVec A G u i
        simpa only [hrow, (fixedIntegerBlockFlatRhs_selectorRows (p := p) b x i).2,
          neg_one_mul, Rat.cast_neg, Rat.cast_intCast] using hlower
      exact le_antisymm hupper' (neg_le_neg_iff.mp hlower')
  · rintro ⟨hu, hfixed⟩
    rw [mem_rational_matrix_polyhedron] at hu
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro s
      have hs := hu s
      simpa [fixedIntegerBlockFlatMatrix, fixedIntegerBlockFlatRhs, Matrix.mulVec,
        dotProduct] using hs
    · intro row'
      refine Fin.addCases ?_ ?_ row'
      · intro i
        have hrow :
            (((fixedIntegerBlockFlatMatrix A G).map (Rat.castHom ℝ)) *ᵥ u)
                (Fin.natAdd (m + (n + p)) (Fin.castAdd n i)) =
              u (Fin.castAdd p i) := by
          simpa [fixedIntegerBlockFlatMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
            using sumFirstBlockSelectorRow_eq_active u i 1
        simp only [hrow, hfixed i,
          (fixedIntegerBlockFlatRhs_selectorRows (p := p) b x i).1, Rat.cast_intCast]
        exact le_rfl
      · intro i
        have hrow :
            (((fixedIntegerBlockFlatMatrix A G).map (Rat.castHom ℝ)) *ᵥ u)
                (Fin.natAdd (m + (n + p)) (Fin.natAdd n i)) =
              (-1 : ℝ) * u (Fin.castAdd p i) := by
          exact fixedIntegerBlockFlatMatrix_lowerRow_mulVec A G u i
        simp only [hrow, hfixed i,
          (fixedIntegerBlockFlatRhs_selectorRows (p := p) b x i).2, neg_one_mul,
          Rat.cast_neg, Rat.cast_intCast]
        exact le_rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
casting an integer to a rational adds at most the one denominator bit to its encoding. -/
private lemma rationalIntCast_encoding_le (z : ℤ) :
    EncodingSize.rational (z : ℚ) ≤ EncodingSize.integer z + 1 := by
  -- Integer casts have denominator one and preserve the numerator's absolute value.
  simp [EncodingSize.rational_eq, EncodingSize.integer_eq]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the fixed-block augmented system has a uniform entrywise encoding bound. -/
private lemma fixedIntegerBlockFlatSystem_encoding_le
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ} {x : Fin n → ℤ} {L B : ℕ}
    (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
    (hG : ∀ i j, EncodingSize.rational (G i j) ≤ L)
    (hb : ∀ i, EncodingSize.rational (b i) ≤ L)
    (hx : EncodingSize.integerVector x ≤ B) :
    (∀ i j, EncodingSize.rational (fixedIntegerBlockFlatMatrix A G i j) ≤ L + B + 4) ∧
      ∀ i,
        EncodingSize.rational (fixedIntegerBlockFlatRhs (n := n) (p := p) b x i) ≤
          L + B + 4 := by
  -- Base-system rows use the existing `L + 3` estimate; selector rows contain only `0`, `1`,
  -- and `-1`.
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro row
      have hbase :
          EncodingSize.rational (nonnegativeMixedFlatMatrix A G row j) ≤ L + 3 :=
        nonnegativeMixedFlatMatrix_encoding_le hA hG row j
      have hbound :
          EncodingSize.rational (nonnegativeMixedFlatMatrix A G row j) ≤ L + B + 4 :=
        hbase.trans (by omega)
      simpa [fixedIntegerBlockFlatMatrix] using hbound
    · intro row
      refine Fin.addCases ?_ ?_ row
      · intro k
        refine Fin.addCases ?_ ?_ j
        · intro l
          by_cases h : l = k
          · simp [fixedIntegerBlockFlatMatrix, h, EncodingSize.rational_eq]
          · simp [fixedIntegerBlockFlatMatrix, h, EncodingSize.rational_eq]
        · intro l
          simp [fixedIntegerBlockFlatMatrix, EncodingSize.rational_eq]
      · intro k
        refine Fin.addCases ?_ ?_ j
        · intro l
          by_cases h : l = k
          · subst l
            rw [fixedIntegerBlockFlatMatrix_lowerRow]
            simp [EncodingSize.rational_eq]
          · rw [fixedIntegerBlockFlatMatrix_lowerRow]
            simp [h, EncodingSize.rational_eq]
        · intro l
          rw [fixedIntegerBlockFlatMatrix_lowerRow]
          simp [EncodingSize.rational_eq]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro row
      have hbase :
          EncodingSize.rational
              (nonnegativeMixedFlatRhs (n := n) (p := p) b row) ≤ L + 3 :=
        nonnegativeMixedFlatRhs_encoding_le hb row
      have hbound :
          EncodingSize.rational
              (nonnegativeMixedFlatRhs (n := n) (p := p) b row) ≤ L + B + 4 :=
        hbase.trans (by omega)
      simpa [fixedIntegerBlockFlatRhs] using hbound
    · intro row
      refine Fin.addCases ?_ ?_ row
      · intro k
        have hk : EncodingSize.integer (x k) ≤ EncodingSize.integerVector x := by
          rw [EncodingSize.integerVector_eq_sum]
          exact Finset.single_le_sum
            (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
              Nat.zero_le (EncodingSize.integer (x i)))
            (Finset.mem_univ k)
        have hcast := rationalIntCast_encoding_le (x k)
        rw [(fixedIntegerBlockFlatRhs_selectorRows b x k).1]
        exact hcast.trans (by omega)
      · intro k
        have hk : EncodingSize.integer (x k) ≤ EncodingSize.integerVector x := by
          rw [EncodingSize.integerVector_eq_sum]
          exact Finset.single_le_sum
            (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
              Nat.zero_le (EncodingSize.integer (x i)))
            (Finset.mem_univ k)
        have hcast := rationalIntCast_encoding_le (-x k)
        have hneg : EncodingSize.integer (-x k) = EncodingSize.integer (x k) := by
          simp [EncodingSize.integer_eq]
        rw [hneg] at hcast
        rw [(fixedIntegerBlockFlatRhs_selectorRows b x k).2]
        simpa only [Rat.cast_intCast] using hcast.trans (by omega)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
a linear equivalence sends an extreme point to an extreme point of the image. -/
private lemma LinearEquiv.map_mem_extremePoints
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) {P : Set E} {x : E}
    (hx : x ∈ P.extremePoints ℝ) :
    e x ∈ (e '' P).extremePoints ℝ := by
  rw [← image_extremePoints e P]
  exact ⟨x, hx, rfl⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
   an extreme point of the mixed-integer hull has an integral first block. -/
lemma integralBlock_of_extremeMixedHull
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p}
    (hxy : xy ∈
      (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ) :
    ∃ x : Fin n → ℤ, xy.1 = fun i ↦ (x i : ℝ) := by
  -- Extreme points of a convex hull lie in the generating mixed-integer set.
  have hmem : xy ∈ nonnegative_rational_mixed_integer_points A G b :=
    extremePoints_convexHull_subset hxy
  -- Unpack mixed-integer membership and then the canonical lattice characterization.
  have hlat : xy ∈ mixed_integer_lattice n p :=
    (mem_mixed_integer_points_iff.mp hmem).2
  rw [mem_mixed_integer_lattice_iff] at hlat
  rcases (mem_integerVectors_iff.mp hlat) with ⟨x, hx⟩
  exact ⟨x, by simpa [Function.comp_def] using hx⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
fixing the integral block turns a mixed-hull vertex into a vertex of the augmented rational
polyhedron. -/
private lemma memExtremePoints_fixedIntegerBlockFlatPolyhedron
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ} {x : Fin n → ℤ} {xy : MixedRealPoint n p}
    (hxy : xy ∈
      (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ)
    (hx : xy.1 = fun i ↦ (x i : ℝ)) :
    mixedPointFlattening n p xy ∈
      (rational_matrix_polyhedron (fixedIntegerBlockFlatMatrix A G)
        (fixedIntegerBlockFlatRhs b x)).extremePoints ℝ := by
  let e := mixedPointFlattening n p
  let S := nonnegative_rational_mixed_integer_points A G b
  let Pfix := rational_matrix_polyhedron (fixedIntegerBlockFlatMatrix A G)
    (fixedIntegerBlockFlatRhs b x)
  have hflatExtreme : e xy ∈ (convexHull ℝ (e '' S)).extremePoints ℝ := by
    have himage := LinearEquiv.map_mem_extremePoints e hxy
    have hconv : e '' convexHull ℝ S = convexHull ℝ (e '' S) := by
      simpa using LinearMap.image_convexHull
        (e : MixedRealPoint n p →ₗ[ℝ] (Fin (n + p) → ℝ)) S
    rw [hconv] at himage
    exact himage
  have hfixSubset : Pfix ⊆ e '' S := by
    intro u hu
    have hspec := mem_fixedIntegerBlockFlatPolyhedron_iff.mp hu
    let uv : MixedRealPoint n p := e.symm u
    have huv_eq : (Fin.appendEquiv n p).symm u = uv := by
      apply (Fin.appendEquiv n p).injective
      rw [Equiv.apply_symm_apply]
      calc
        u = e uv := (e.apply_symm_apply u).symm
        _ = Fin.appendEquiv n p uv := mixedPointFlattening_apply uv
    have huvP : uv ∈ nonnegative_rational_mixed_polyhedron A G b := by
      rw [← huv_eq]
      exact memNonnegativeMixedFlatPolyhedron_iff.mp hspec.1
    have huvFirst : uv.1 = fun i ↦ (x i : ℝ) := by
      funext i
      have happly : e uv = u := e.apply_symm_apply u
      have hcoord := congrFun happly (Fin.castAdd p i)
      rw [mixedPointFlattening_apply] at hcoord
      simpa [Fin.appendEquiv] using hcoord.trans (hspec.2 i)
    have huvLattice : uv ∈ mixed_integer_lattice n p := by
      rw [mem_mixed_integer_lattice_iff, mem_integerVectors_iff]
      exact ⟨x, by simpa [Function.comp_def] using huvFirst⟩
    have huvS : uv ∈ S := by
      exact mem_mixed_integer_points_iff.mpr ⟨huvP, huvLattice⟩
    exact ⟨uv, huvS, e.apply_symm_apply u⟩
  rw [mem_extremePoints_iff_left] at hflatExtreme ⊢
  refine ⟨?_, ?_⟩
  · rw [mem_fixedIntegerBlockFlatPolyhedron_iff]
    constructor
    · have hxyMem : xy ∈ S := extremePoints_convexHull_subset hxy
      have hxyP := (mem_mixed_integer_points_iff.mp hxyMem).1
      rw [memNonnegativeMixedFlatPolyhedron_iff]
      have hflat := mixedPointFlattening_apply xy
      rw [hflat]
      simpa using hxyP
    · intro i
      rw [mixedPointFlattening_apply]
      simpa [Fin.appendEquiv] using congrFun hx i
  · intro u hu v hv hsegment
    exact hflatExtreme.2 u
      (subset_convexHull ℝ (e '' S) (hfixSubset hu)) v
      (subset_convexHull ℝ (e '' S) (hfixSubset hv)) hsegment

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean:
the integral block of every mixed-hull vertex has uniformly polynomially bounded encoding size. -/
private lemma existsPolynomialIntegralBlockEncodingBound :
    ∃ πx : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i j, EncodingSize.rational (A i j) ≤ L)
        (hG : ∀ i j, EncodingSize.rational (G i j) ≤ L)
        (hb : ∀ i, EncodingSize.rational (b i) ≤ L)
        (xy : MixedRealPoint n p)
        (hxy : xy ∈
          (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ)
        (x : Fin n → ℤ)
        (hx : xy.1 = fun i ↦ (x i : ℝ)),
        EncodingSize.integerVector x ≤ πx.eval (n + p + L) := by
  classical
  obtain ⟨πv, hπv⟩ := rational_vertices_have_polynomially_bounded_encoding_size
  obtain ⟨πr, hπr⟩ :=
    rational_extreme_rays_have_polynomially_bounded_rescaled_encoding_size
  let shift : Polynomial ℕ := Polynomial.X + Polynomial.C 3
  let vertexBound : Polynomial ℕ := πv.comp shift
  let rayBound : Polynomial ℕ := πr.comp shift
  let πx : Polynomial ℕ :=
    Polynomial.X *
      (vertexBound + Polynomial.X * rayBound + Polynomial.X + Polynomial.C 4)
  refine ⟨πx, ?_⟩
  intro m n p A G b L hA hG hb xy hxy x hx
  let P : Set (Fin (n + p) → ℝ) :=
    rational_matrix_polyhedron (nonnegativeMixedFlatMatrix A G) (nonnegativeMixedFlatRhs b)
  let u : Fin (n + p) → ℝ := mixedPointFlattening n p xy
  let T : ℕ := n + p + L
  let V : ℕ := πv.eval (T + 3)
  let R : ℕ := πr.eval (T + 3)
  have hflatA :
      ∀ i j, EncodingSize.rational (nonnegativeMixedFlatMatrix A G i j) ≤ L + 3 :=
    nonnegativeMixedFlatMatrix_encoding_le hA hG
  have hflatb :
      ∀ i, EncodingSize.rational (nonnegativeMixedFlatRhs b i) ≤ L + 3 :=
    nonnegativeMixedFlatRhs_encoding_le (n := n) (p := p) hb
  have hxyMem : xy ∈ nonnegative_rational_mixed_integer_points A G b :=
    extremePoints_convexHull_subset hxy
  have huImage :
      u ∈ mixedPointFlattening n p '' nonnegative_rational_mixed_integer_points A G b :=
    ⟨xy, hxyMem, rfl⟩
  have huSpec := mem_image_nonnegativeMixedIntegerPoints_iff.mp huImage
  have huP : u ∈ P := huSpec.1
  have huInt : (fun i : Fin n ↦ u (Fin.castAdd p i)) ∈ integerVectors n := huSpec.2
  have hP_nonempty : P.Nonempty := ⟨u, huP⟩
  have hP_nonnegative : ∀ w ∈ P, 0 ≤ w := by
    intro w hw
    have hw' := memNonnegativeMixedFlatPolyhedron_iff.mp hw
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [Fin.appendEquiv] using hw'.2.1 i
    · intro j
      simpa [Fin.appendEquiv] using hw'.2.2 j
  have hP_polyhedron : is_polyhedron P := by
    exact ⟨m + (n + p), (nonnegativeMixedFlatMatrix A G).map (Rat.castHom ℝ),
      fun i ↦ (nonnegativeMixedFlatRhs b i : ℝ), rfl⟩
  have hP_pointed : is_pointed P :=
    isPointed_of_nonempty_of_nonnegative hP_nonempty hP_nonnegative
  have huExtreme :
      u ∈
        (convexHull ℝ
          (mixedPointFlattening n p ''
            nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ := by
    have himage := LinearEquiv.map_mem_extremePoints (mixedPointFlattening n p) hxy
    have hconv :
        mixedPointFlattening n p ''
            convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) =
          convexHull ℝ
            (mixedPointFlattening n p '' nonnegative_rational_mixed_integer_points A G b) := by
      simpa using LinearMap.image_convexHull
        (mixedPointFlattening n p :
          MixedRealPoint n p →ₗ[ℝ] (Fin (n + p) → ℝ))
        (nonnegative_rational_mixed_integer_points A G b)
    rw [hconv] at himage
    exact himage
  rcases exists_vertex_convex_combination_add_extreme_ray_conic_combination
      hP_polyhedron hP_pointed huP with
    ⟨vertexPart, vertices, hvertices, _hverticesIndependent, hvertexPart,
      _hverticesCard, q, rays, hrays, _hraysIndependent, hqSpan,
      coeff, hcoeff, huDecomp⟩
  have hq : q ≤ n + p := by
    calc
      q ≤ Module.finrank ℝ (Submodule.span ℝ (recessionCone P)) := hqSpan
      _ ≤ Module.finrank ℝ (Fin (n + p) → ℝ) := Submodule.finrank_le _
      _ = n + p := by simp
  choose vertexQ hvertexQ hvertexQSize using
    fun w : ↑vertices ↦
      hπv (nonnegativeMixedFlatMatrix A G) (nonnegativeMixedFlatRhs b) (L + 3)
        hflatA hflatb w (hvertices w.property)
  choose scale hscalePos rayQ hrayQ hrayQSize using
    fun j : Fin q ↦
      hπr (nonnegativeMixedFlatMatrix A G) (nonnegativeMixedFlatRhs b) (L + 3)
        hflatA hflatb (rays j) (hrays j)
  let rayInt : Fin q → Fin (n + p) → ℤ :=
    fun j ↦ common_denominator_scaled_vector (rayQ j)
  let rayScale : Fin q → ℝ :=
    fun j ↦ (rational_vector_common_denominator (rayQ j) : ℝ) * scale j
  have hrayScalePos : ∀ j, 0 < rayScale j := by
    intro j
    exact mul_pos (by exact_mod_cast rationalVectorCommonDenominator_pos (rayQ j)) (hscalePos j)
  have hrayInt_eq :
      ∀ j, (fun k ↦ (rayInt j k : ℝ)) = rayScale j • rays j := by
    intro j
    calc
      (fun k ↦ (rayInt j k : ℝ)) =
          (rational_vector_common_denominator (rayQ j) : ℝ) •
            (fun k ↦ (rayQ j k : ℝ)) := by
              simpa [rayInt] using commonDenominatorScaledVector_eq_smul_real (rayQ j)
      _ = (rational_vector_common_denominator (rayQ j) : ℝ) •
            (scale j • rays j) := by rw [hrayQ j]
      _ = rayScale j • rays j := by rw [smul_smul]
  have hrayIntSize :
      ∀ j, EncodingSize.integerVector (rayInt j) ≤ (n + p) * R := by
    intro j
    calc
      EncodingSize.integerVector (rayInt j) ≤
          (n + p) * EncodingSize.rationalVector (rayQ j) := by
            simpa [rayInt] using common_denominator_scaled_vector_encoding_size_le (rayQ j)
      _ ≤ (n + p) * R := by
        apply Nat.mul_le_mul_left
        simpa [R, T, Nat.add_assoc] using hrayQSize j
  have hrayNonnegative : ∀ j, 0 ≤ rays j := by
    intro j
    exact recessionDirection_nonnegative_of_nonnegative hP_nonempty hP_nonnegative
      (isExtremeRayOfPolyhedron_mem_recessionCone (hrays j))
  have hrayIntNonnegative : ∀ j k, 0 ≤ rayInt j k := by
    intro j k
    have hreal : (0 : ℝ) ≤ (rayInt j k : ℝ) := by
      have hcoord := congrFun (hrayInt_eq j) k
      simp only [Pi.smul_apply, smul_eq_mul] at hcoord
      rw [hcoord]
      exact mul_nonneg (hrayScalePos j).le (hrayNonnegative j k)
    exact_mod_cast hreal
  have hcoeff_lt : ∀ j, coeff j < rayScale j := by
    intro j
    by_contra hnot
    have hscale_le : rayScale j ≤ coeff j := le_of_not_gt hnot
    have hminusP : u - (fun k ↦ (rayInt j k : ℝ)) ∈ P := by
      have hminus := sub_scaledRay_mem_of_decomposition rays coeff
        (P := P) (u := u) (v := vertexPart)
        (convexHull_min (fun w hw ↦ extremePoints_subset (hvertices hw))
          (rationalMatrixPolyhedron_convex
            (nonnegativeMixedFlatMatrix A G) (nonnegativeMixedFlatRhs b)) hvertexPart)
        (fun k ↦ isExtremeRayOfPolyhedron_mem_recessionCone (hrays k)) hcoeff huDecomp j
        hscale_le
      rw [← hrayInt_eq j] at hminus
      exact hminus
    have hplusP : u + (fun k ↦ (rayInt j k : ℝ)) ∈ P := by
      have hzRec : (fun k ↦ (rayInt j k : ℝ)) ∈ recessionCone P := by
        rw [hrayInt_eq j]
        exact smul_mem_recessionCone
          (isExtremeRayOfPolyhedron_mem_recessionCone (hrays j)) (hrayScalePos j).le
      simpa using (mem_recessionCone_iff.mp hzRec) huP 1 zero_le_one
    have huFirst : ∀ i : Fin n, u (Fin.castAdd p i) = (x i : ℝ) := by
      intro i
      dsimp [u]
      rw [mixedPointFlattening_apply]
      simpa [Fin.appendEquiv] using congrFun hx i
    have hminusInt :
        (fun i : Fin n ↦
          (u - fun k ↦ (rayInt j k : ℝ)) (Fin.castAdd p i)) ∈ integerVectors n := by
      rw [mem_integerVectors_iff]
      refine ⟨fun i ↦ x i - rayInt j (Fin.castAdd p i), ?_⟩
      funext i
      simp [huFirst i]
    have hplusInt :
        (fun i : Fin n ↦
          (u + fun k ↦ (rayInt j k : ℝ)) (Fin.castAdd p i)) ∈ integerVectors n := by
      rw [mem_integerVectors_iff]
      refine ⟨fun i ↦ x i + rayInt j (Fin.castAdd p i), ?_⟩
      funext i
      simp [huFirst i]
    have hminusImage :
        u - (fun k ↦ (rayInt j k : ℝ)) ∈
          mixedPointFlattening n p '' nonnegative_rational_mixed_integer_points A G b :=
      mem_image_nonnegativeMixedIntegerPoints_iff.mpr ⟨hminusP, hminusInt⟩
    have hplusImage :
        u + (fun k ↦ (rayInt j k : ℝ)) ∈
          mixedPointFlattening n p '' nonnegative_rational_mixed_integer_points A G b :=
      mem_image_nonnegativeMixedIntegerPoints_iff.mpr ⟨hplusP, hplusInt⟩
    have hminusEq :
        u - (fun k ↦ (rayInt j k : ℝ)) = u :=
      (mem_extremePoints_iff_left.mp huExtreme).2 _
        (subset_convexHull ℝ _ hminusImage) _
        (subset_convexHull ℝ _ hplusImage)
        (mem_openSegment_sub_add u (fun k ↦ (rayInt j k : ℝ)))
    have hrayIntZero : (fun k ↦ (rayInt j k : ℝ)) = 0 := sub_eq_self.mp hminusEq
    have hscaledZero : rayScale j • rays j = 0 := by
      rw [← hrayInt_eq j]
      exact hrayIntZero
    have hrayZero : rays j = 0 := (smul_eq_zero.mp hscaledZero).resolve_left
      (ne_of_gt (hrayScalePos j))
    exact (extremeRay_ne_zero (isExtremeRayOfPolyhedron_iff.mp (hrays j))) hrayZero
  have hvertexCoordinate :
      ∀ k : Fin (n + p), vertexPart k < (2 : ℝ) ^ V := by
    intro k
    have hhalfspace : Convex ℝ {w : Fin (n + p) → ℝ | w k < (2 : ℝ) ^ V} := by
      simpa using convex_halfSpace_lt
        (LinearMap.proj k : (Fin (n + p) → ℝ) →ₗ[ℝ] ℝ).isLinear
        ((2 : ℝ) ^ V)
    refine convexHull_min ?_ hhalfspace hvertexPart
    intro w hw
    let ws : ↑vertices := ⟨w, hw⟩
    have hcoordSize : EncodingSize.rational (vertexQ ws k) ≤ V := by
      have hone :
          EncodingSize.rational (vertexQ ws k) ≤
            EncodingSize.rationalVector (vertexQ ws) := by
        rw [EncodingSize.rationalVector_eq_sum]
        exact Finset.single_le_sum
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + p)))) ↦
            Nat.zero_le (EncodingSize.rational (vertexQ ws i)))
          (Finset.mem_univ k)
      exact hone.trans (by simpa [V, T, Nat.add_assoc] using hvertexQSize ws)
    have hpow :
        (2 : ℝ) ^ EncodingSize.rational (vertexQ ws k) ≤ (2 : ℝ) ^ V :=
      pow_le_pow_right₀ (by norm_num) hcoordSize
    calc
      w k = (vertexQ ws k : ℝ) := congrFun (hvertexQ ws) k
      _ ≤ |(vertexQ ws k : ℝ)| := le_abs_self _
      _ < (2 : ℝ) ^ EncodingSize.rational (vertexQ ws k) :=
        abs_ratCast_lt_twoPow_encoding _
      _ ≤ (2 : ℝ) ^ V := hpow
  have hcoordinateEncoding :
      ∀ i : Fin n,
        EncodingSize.integer (x i) ≤ V + (n + p) * R + (n + p) + 4 := by
    intro i
    let k : Fin (n + p) := Fin.castAdd p i
    have huFirst : u k = (x i : ℝ) := by
      dsimp [u]
      rw [mixedPointFlattening_apply]
      simpa [k, Fin.appendEquiv] using congrFun hx i
    have hterm : ∀ j, coeff j * rays j k ≤ (rayInt j k : ℝ) := by
      intro j
      have hz := congrFun (hrayInt_eq j) k
      simp only [Pi.smul_apply, smul_eq_mul] at hz
      rw [hz]
      exact mul_le_mul_of_nonneg_right (hcoeff_lt j).le (hrayNonnegative j k)
    have hsum :
        ∑ j, coeff j * rays j k ≤ ∑ j, (rayInt j k : ℝ) :=
      Finset.sum_le_sum fun j _ ↦ hterm j
    have hrayCoordinate : ∀ j, (rayInt j k).natAbs < 2 ^ ((n + p) * R) := by
      intro j
      have hentry : EncodingSize.integer (rayInt j k) ≤
          EncodingSize.integerVector (rayInt j) := by
        rw [EncodingSize.integerVector_eq_sum]
        exact Finset.single_le_sum
          (fun l (_ : l ∈ (Finset.univ : Finset (Fin (n + p)))) ↦
            Nat.zero_le (EncodingSize.integer (rayInt j l)))
          (Finset.mem_univ k)
      have hsize : Nat.size (rayInt j k).natAbs ≤ (n + p) * R := by
        have := hentry.trans (hrayIntSize j)
        simp only [EncodingSize.integer_eq] at this
        omega
      exact Nat.lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by decide) hsize)
    have hrayCast : ∀ j, (rayInt j k : ℝ) < (2 : ℝ) ^ ((n + p) * R) := by
      intro j
      have hnonneg := hrayIntNonnegative j k
      have hcoord := hrayCoordinate j
      have hnatCast :
          ((rayInt j k).natAbs : ℝ) < (2 : ℝ) ^ ((n + p) * R) := by
        exact_mod_cast hcoord
      calc
        (rayInt j k : ℝ) = |(rayInt j k : ℝ)| :=
          (abs_of_nonneg (Int.cast_nonneg hnonneg)).symm
        _ = ((rayInt j k).natAbs : ℝ) := by
          rw [← Int.cast_abs]
          exact (Nat.cast_natAbs (rayInt j k)).symm
        _ < (2 : ℝ) ^ ((n + p) * R) := hnatCast
    have hsumBound :
        ∑ j, (rayInt j k : ℝ) ≤ (q : ℝ) * (2 : ℝ) ^ ((n + p) * R) := by
      calc
        ∑ j, (rayInt j k : ℝ) ≤ ∑ _j : Fin q, (2 : ℝ) ^ ((n + p) * R) :=
          Finset.sum_le_sum fun j _ ↦ (hrayCast j).le
        _ = (q : ℝ) * (2 : ℝ) ^ ((n + p) * R) := by simp
    have hrealBound :
        (x i : ℝ) < (2 : ℝ) ^ V + (q : ℝ) * (2 : ℝ) ^ ((n + p) * R) := by
      calc
        (x i : ℝ) = vertexPart k + ∑ j, coeff j * rays j k := by
          rw [← huFirst]
          have hcoord := congrFun huDecomp k
          simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
        _ ≤ vertexPart k + ∑ j, (rayInt j k : ℝ) := add_le_add_right hsum _
        _ < (2 : ℝ) ^ V + ∑ j, (rayInt j k : ℝ) :=
          add_lt_add_left (hvertexCoordinate k) _
        _ ≤ (2 : ℝ) ^ V + (q : ℝ) * (2 : ℝ) ^ ((n + p) * R) :=
          add_le_add_right hsumBound _
    have hxiNonnegative : 0 ≤ x i := by
      have huNonnegative : (0 : ℝ) ≤ u k := hP_nonnegative u huP k
      rw [huFirst] at huNonnegative
      simpa only [Int.cast_nonneg_iff] using huNonnegative
    have hnatBound :
        (x i).natAbs < 2 ^ V + q * 2 ^ ((n + p) * R) := by
      have hcastNatAbs : ((x i).natAbs : ℝ) = (x i : ℝ) := by
        calc
          ((x i).natAbs : ℝ) = ((|x i| : ℤ) : ℝ) := Nat.cast_natAbs (x i)
          _ = |(x i : ℝ)| := Int.cast_abs
          _ = (x i : ℝ) := abs_of_nonneg (Int.cast_nonneg hxiNonnegative)
      have hrealNatAbs :
          ((x i).natAbs : ℝ) <
            (((2 ^ V + q * 2 ^ ((n + p) * R) : ℕ) : ℝ)) := by
        rw [hcastNatAbs]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hrealBound
      exact_mod_cast hrealNatAbs
    have henc := integerEncoding_le_of_lt_twoPow_add_mul
      (x i).natAbs V q ((n + p) * R) hnatBound
    simp only [EncodingSize.integer_eq]
    exact henc.trans (by omega)
  have hintegerVector :
      EncodingSize.integerVector x ≤
        n * (V + (n + p) * R + (n + p) + 4) := by
    rw [EncodingSize.integerVector_eq_sum]
    calc
      ∑ i : Fin n, EncodingSize.integer (x i) ≤
          ∑ _i : Fin n, (V + (n + p) * R + (n + p) + 4) :=
        Finset.sum_le_sum fun i _ ↦ hcoordinateEncoding i
      _ = n * (V + (n + p) * R + (n + p) + 4) := by simp
  have hn : n ≤ T := by omega
  have hd : n + p ≤ T := by omega
  have hinside :
      V + (n + p) * R + (n + p) + 4 ≤ V + T * R + T + 4 := by
    exact Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right R hd) V) hd) 4
  calc
    EncodingSize.integerVector x ≤
        n * (V + (n + p) * R + (n + p) + 4) := hintegerVector
    _ ≤ T * (V + T * R + T + 4) := Nat.mul_le_mul hn hinside
    _ = πx.eval T := by
      simp [πx, vertexBound, rayBound, shift, V, R, Polynomial.eval_comp, T,
        Nat.add_assoc, Nat.mul_add, Nat.add_mul]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_8_2/ch4_sec4_8_2_lemma_4_35.lean

Lemma 4.35.

There is a uniform polynomial bound such that, for every rational mixed system
`A x + G y ≤ b` with nonnegativity constraints and entrywise encoding bound `L`, every vertex of
the mixed-integer hull `conv(S)` admits an integral `x`-block and a rational `y`-block whose
total encoding size is bounded by that polynomial evaluated at `n + p + L`. -/
theorem mixed_integer_hull_extreme_points_have_polynomially_bounded_encoding_size :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, EncodingSize.rational (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, EncodingSize.rational (G i j) ≤ L)
        (hb : ∀ i : Fin m, EncodingSize.rational (b i) ≤ L)
        (xy : MixedRealPoint n p)
        (hxy :
          xy ∈
            (convexHull ℝ
              (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ),
        ∃ x : Fin n → ℤ,
          ∃ y : Fin p → ℚ,
            xy = ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) ∧
              EncodingSize.integerVector x + EncodingSize.rationalVector y ≤
                π.eval (n + p + L) := by
    classical
    obtain ⟨πx, hπx⟩ := existsPolynomialIntegralBlockEncodingBound
    obtain ⟨πv, hπv⟩ := rational_vertices_have_polynomially_bounded_encoding_size
    let π : Polynomial ℕ :=
      πx + πv.comp (Polynomial.X + πx + Polynomial.C 4)
    refine ⟨π, ?_⟩
    intro m n p A G b L hA hG hb xy hxy
    -- Combine the integral-block certificate with the fixed-fiber vertex certificate.
    -- First control the integral block by the pointed vertex-and-ray decomposition.
    rcases integralBlock_of_extremeMixedHull hxy with ⟨x, hx⟩
    have hxSize : EncodingSize.integerVector x ≤ πx.eval (n + p + L) :=
      hπx A G b L hA hG hb xy hxy x hx
    have hfixedBounds :=
      fixedIntegerBlockFlatSystem_encoding_le hA hG hb hxSize
    have hfixedExtreme :=
      memExtremePoints_fixedIntegerBlockFlatPolyhedron hxy hx
    -- The fixed-block fiber is an ordinary rational polyhedron, so Theorem 3.38 supplies all
    -- rational coordinates with a uniform encoding bound.
    rcases hπv
        (fixedIntegerBlockFlatMatrix A G) (fixedIntegerBlockFlatRhs b x)
        (L + πx.eval (n + p + L) + 4) hfixedBounds.1 hfixedBounds.2
        (mixedPointFlattening n p xy) hfixedExtreme with
      ⟨v, hv, hvSize⟩
    let y : Fin p → ℚ := fun j ↦ v (Fin.natAdd n j)
    have hxyRepresentation :
        xy = ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) := by
      apply Prod.ext
      · exact hx
      · funext j
        have hj := congrFun hv (Fin.natAdd n j)
        rw [mixedPointFlattening_apply] at hj
        simpa [y, Fin.appendEquiv] using hj
    have hySize : EncodingSize.rationalVector y ≤ EncodingSize.rationalVector v := by
      rw [EncodingSize.rationalVector_eq_sum, EncodingSize.rationalVector_eq_sum,
        Fin.sum_univ_add]
      exact Nat.le_add_left _ _
    refine ⟨x, y, hxyRepresentation, ?_⟩
    calc
      EncodingSize.integerVector x + EncodingSize.rationalVector y ≤
          πx.eval (n + p + L) + EncodingSize.rationalVector v :=
        Nat.add_le_add hxSize hySize
      _ ≤ πx.eval (n + p + L) +
          πv.eval ((n + p) + (L + πx.eval (n + p + L) + 4)) :=
        Nat.add_le_add_left hvSize _
      _ = π.eval (n + p + L) := by
        simp [π, Polynomial.eval_comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Lemma435

#print axioms mixed_integer_hull_extreme_points_have_polynomially_bounded_encoding_size
