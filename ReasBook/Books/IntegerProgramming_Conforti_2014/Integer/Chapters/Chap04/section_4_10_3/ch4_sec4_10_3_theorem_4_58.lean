/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_lemma_4_52
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_1

open scoped BigOperators Matrix Matrix.Norms.Elementwise NonnegativeRankNotation

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 4.58: an auxiliary proof-side relaxation by rank-one matrices in
`[0, 1]^(m × n)`, represented as outer products `Matrix.vecMulVec x y` with both factors in the
unit box. This includes the zero matrix via `x = 0` or `y = 0`. -/
def isUnitBoxRankOneMatrix
    {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ x : Fin m → ℝ,
    ∃ y : Fin n → ℝ,
      (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
      (∀ j, 0 ≤ y j ∧ y j ≤ 1) ∧
      R = Matrix.vecMulVec x y

/-- Helper for Theorem 4.58: the theorem-local `α`, implemented as the supremum of the trace
pairings of `W` with all `0/1` rectangle indicators `rectangle_indicator I J`. This includes the
zero rectangle via `I = ∅` or `J = ∅`, matching the source-facing relaxation used in the proof. -/
noncomputable def rectangle_trace_max
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup
    {x |
      ∃ I : Set (Fin m),
        ∃ J : Set (Fin n),
          Matrix.trace (W * (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ)ᵀ) = x}

/-- Helper for Theorem 4.58: an auxiliary proof-side relaxation allowing all rank-one matrices in
`[0, 1]^(m × n)` and hence the zero matrix. This is used only in the proof route before rounding
to `0/1` rectangle indicators. -/
private noncomputable def rectangle_trace_relaxed_max
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup
    {x |
      ∃ R : Matrix (Fin m) (Fin n) ℝ,
        isUnitBoxRankOneMatrix R ∧
          Matrix.trace (W * Rᵀ) = x}

-- Semantic search found no dedicated existing owner for the source's rectangle maximum, so this
-- file uses a local rectangle-indicator supremum over all rectangles, including the zero one.
/-- Helper for Theorem 4.58: `rectangle_trace_max W` is the greatest trace pairing of `W` with a
rectangle indicator `rectangle_indicator I J`, allowing `I` or `J` to be empty so the zero
rectangle is included. -/
theorem rectangle_trace_max_isGreatest
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) :
    IsGreatest
      {x |
        ∃ I : Set (Fin m),
          ∃ J : Set (Fin n),
            Matrix.trace (W * (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ)ᵀ) = x}
      (rectangle_trace_max W) := by
  classical
  let rectangleValue : Set (Fin m) × Set (Fin n) → ℝ :=
    fun IJ ↦ Matrix.trace (W * (rectangle_indicator IJ.1 IJ.2 : Matrix (Fin m) (Fin n) ℝ)ᵀ)
  have hset :
      {x |
        ∃ I : Set (Fin m),
          ∃ J : Set (Fin n),
            Matrix.trace (W * (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ)ᵀ) = x} =
        Set.range rectangleValue := by
    ext x
    constructor
    · rintro ⟨I, J, hIJ⟩
      exact ⟨⟨I, J⟩, by simpa [rectangleValue] using hIJ⟩
    · rintro ⟨⟨I, J⟩, hIJ⟩
      exact ⟨I, J, by simpa [rectangleValue] using hIJ⟩
  obtain ⟨IJmax, hmax⟩ := Finite.exists_max rectangleValue
  have hgreatestRange : IsGreatest (Set.range rectangleValue) (rectangleValue IJmax) := by
    refine ⟨⟨IJmax, rfl⟩, ?_⟩
    rintro _ ⟨IJ, rfl⟩
    exact hmax IJ
  have hvalue :
      rectangleValue IJmax = rectangle_trace_max W := by
    simpa [rectangle_trace_max, hset] using hgreatestRange.csSup_eq.symm
  rcases IJmax with ⟨Imax, Jmax⟩
  refine ⟨?_, ?_⟩
  · exact ⟨Imax, Jmax, by simpa [rectangleValue] using hvalue⟩
  · rintro x ⟨I, J, rfl⟩
    calc
      Matrix.trace (W * (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ)ᵀ)
          ≤ rectangleValue (Imax, Jmax) := hmax (I, J)
      _ = rectangle_trace_max W := by simpa [rectangleValue] using hvalue

/-- Helper for Theorem 4.58: any greatest value of the theorem-local rectangle maximum for `W` is
`rectangle_trace_max W`. -/
theorem rectangle_trace_max_eq_of_isGreatest
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {alpha : ℝ}
    (halpha :
      IsGreatest
        {x |
          ∃ I : Set (Fin m),
            ∃ J : Set (Fin n),
              Matrix.trace (W * (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ)ᵀ) = x}
        alpha) :
    rectangle_trace_max W = alpha := by
  -- Both sides are the supremum of the same finite set of rectangle trace values.
  simpa [rectangle_trace_max] using halpha.csSup_eq

/-- Helper for Theorem 4.58: tracing `W` against a rank-one outer product rewrites as the
dot product of `x` with `W *ᵥ y`. -/
lemma trace_mul_vecMulVec_transpose_eq_dotProduct_mulVec
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ)
    (y : Fin n → ℝ) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) = (W *ᵥ y) ⬝ᵥ x := by
  -- Move the transpose inside the outer product and collapse the trace of the resulting
  -- rank-one matrix.
  rw [Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]

/-- Helper for Theorem 4.58: the same trace pairing can also be rewritten as the dot product of
`y` with the row-vector `x ᵥ* W`. -/
lemma trace_mul_vecMulVec_transpose_eq_dotProduct_vecMul
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ)
    (y : Fin n → ℝ) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) = y ⬝ᵥ (x ᵥ* W) := by
  -- Cyclically permute the trace to make the expression linear in `y`.
  rw [Matrix.trace_mul_comm, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.trace_vecMulVec]

/-- Helper for Theorem 4.58: a linear form on `[0, 1]^k` is bounded above by rounding each
coordinate to `1` when its coefficient is nonnegative and to `0` otherwise. -/
lemma dotProduct_le_dotProduct_nonnegativeRound
    {k : ℕ}
    (c x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    c ⬝ᵥ x ≤ c ⬝ᵥ (fun i ↦ if 0 ≤ c i then (1 : ℝ) else 0) := by
  -- Compare the two dot products entrywise and sum the coordinatewise inequalities.
  unfold dotProduct
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hci : 0 ≤ c i
  · have hxi : x i ≤ 1 := (hx i).2
    simp [hci]
    nlinarith
  · have hci' : c i < 0 := lt_of_not_ge hci
    have hx0 : 0 ≤ x i := (hx i).1
    simp [hci]
    nlinarith

/-- Helper for Theorem 4.58: the `0/1` outer product of row and column indicators is exactly the
rectangle indicator matrix. -/
lemma vecMulVec_indicator_eq_rectangleIndicator
    {m n : ℕ}
    (I : Set (Fin m))
    (J : Set (Fin n)) :
    Matrix.vecMulVec
        (fun i ↦ if i ∈ I then (1 : ℝ) else 0)
        (fun j ↦ if j ∈ J then (1 : ℝ) else 0) =
      (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ) := by
  -- Both matrices are the same `0/1` indicator of `I × J`.
  ext i j
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ J <;>
    simp [Matrix.vecMulVec, rectangle_indicator, hi, hj]

/-- Helper for Theorem 4.58: the relaxed rank-one witness values are uniformly bounded above by
the entrywise `ℓ¹` norm of `W`. -/
lemma rectangle_trace_relaxed_values_bddAbove
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    :
    BddAbove
      {z |
        ∃ R : Matrix (Fin m) (Fin n) ℝ,
          isUnitBoxRankOneMatrix R ∧ Matrix.trace (W * Rᵀ) = z} := by
  refine ⟨∑ i, ∑ j, |W i j|, ?_⟩
  rintro z ⟨R, ⟨xR, yR, hxR, hyR, rfl⟩, rfl⟩
  calc
    Matrix.trace (W * (Matrix.vecMulVec xR yR)ᵀ)
        = (W *ᵥ yR) ⬝ᵥ xR := trace_mul_vecMulVec_transpose_eq_dotProduct_mulVec W xR yR
    _ = ∑ i, (∑ j, W i j * yR j) * xR i := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, |∑ j, W i j * yR j| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      by_cases hrow : 0 ≤ ∑ j, W i j * yR j
      · have hxi : xR i ≤ 1 := (hxR i).2
        rw [abs_of_nonneg hrow]
        nlinarith
      · have hxi0 : 0 ≤ xR i := (hxR i).1
        have hnonpos : (∑ j, W i j * yR j) * xR i ≤ 0 := by
          nlinarith [lt_of_not_ge hrow]
        exact hnonpos.trans (abs_nonneg _)
    _ ≤ ∑ i, ∑ j, |W i j| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine le_trans (Finset.abs_sum_le_sum_abs (fun j ↦ W i j * yR j) Finset.univ) ?_
      refine Finset.sum_le_sum ?_
      intro j hj
      have hyj0 : 0 ≤ yR j := (hyR j).1
      have hyj1 : yR j ≤ 1 := (hyR j).2
      rw [abs_mul, abs_of_nonneg hyj0]
      nlinarith [abs_nonneg (W i j)]

/-- Helper for Theorem 4.58: for fixed `x`, rounding `y` by the sign pattern of `x ᵥ* W` does not
decrease the trace pairing. -/
lemma trace_vecMulVec_le_trace_vecMulVec_roundRight
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin m → ℝ}
    {y : Fin n → ℝ}
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤
      Matrix.trace
        (W *
          (Matrix.vecMulVec x (fun j ↦ if 0 ≤ (x ᵥ* W) j then (1 : ℝ) else 0))ᵀ) := by
  -- Rewrite the objective so the right factor appears linearly, then apply coordinate rounding.
  calc
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ)
        = (x ᵥ* W) ⬝ᵥ y := by
          rw [trace_mul_vecMulVec_transpose_eq_dotProduct_vecMul, dotProduct_comm]
    _ ≤
        (x ᵥ* W) ⬝ᵥ (fun j ↦ if 0 ≤ (x ᵥ* W) j then (1 : ℝ) else 0) :=
          dotProduct_le_dotProduct_nonnegativeRound (x ᵥ* W) y hy
    _ =
        Matrix.trace
          (W * (Matrix.vecMulVec x (fun j ↦ if 0 ≤ (x ᵥ* W) j then (1 : ℝ) else 0))ᵀ) := by
          rw [trace_mul_vecMulVec_transpose_eq_dotProduct_vecMul, dotProduct_comm]

/-- Helper for Theorem 4.58: once the right factor is fixed, rounding `x` by the sign pattern of
`W *ᵥ y` also does not decrease the trace pairing. -/
lemma trace_vecMulVec_le_trace_vecMulVec_roundLeft
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin m → ℝ}
    {y : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤
      Matrix.trace
        (W *
          (Matrix.vecMulVec (fun i ↦ if 0 ≤ (W *ᵥ y) i then (1 : ℝ) else 0) y)ᵀ) := by
  -- Rewrite the objective so the left factor appears linearly, then apply the same rounding step.
  calc
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ)
        = (W *ᵥ y) ⬝ᵥ x := trace_mul_vecMulVec_transpose_eq_dotProduct_mulVec W x y
    _ ≤
        (W *ᵥ y) ⬝ᵥ (fun i ↦ if 0 ≤ (W *ᵥ y) i then (1 : ℝ) else 0) :=
          dotProduct_le_dotProduct_nonnegativeRound (W *ᵥ y) x hx
    _ =
        Matrix.trace
          (W * (Matrix.vecMulVec (fun i ↦ if 0 ≤ (W *ᵥ y) i then (1 : ℝ) else 0) y)ᵀ) := by
          rw [trace_mul_vecMulVec_transpose_eq_dotProduct_mulVec]

/-- Helper for Theorem 4.58: every rank-one matrix with entries in `[0, 1]` is bounded by the
theorem-local rectangle maximum after the source's two successive rounding steps. -/
lemma trace_vecMulVec_le_rectangle_trace_max_of_unitBox
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin m → ℝ}
    {y : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤ rectangle_trace_max W := by
  let J : Set (Fin n) := {j | 0 ≤ (x ᵥ* W) j}
  let y' : Fin n → ℝ := fun j ↦ if j ∈ J then (1 : ℝ) else 0
  let I : Set (Fin m) := {i | 0 ≤ (W *ᵥ y') i}
  let x' : Fin m → ℝ := fun i ↦ if i ∈ I then (1 : ℝ) else 0
  have hroundRight :
      Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤
        Matrix.trace (W * (Matrix.vecMulVec x y')ᵀ) := by
    -- First round the right factor using the coefficients coming from `x ᵥ* W`.
    simpa [J, y'] using trace_vecMulVec_le_trace_vecMulVec_roundRight W (x := x) (y := y) hy
  have hroundLeft :
      Matrix.trace (W * (Matrix.vecMulVec x y')ᵀ) ≤
        Matrix.trace (W * (Matrix.vecMulVec x' y')ᵀ) := by
    -- Then round the left factor using the coefficients coming from `W *ᵥ y'`.
    simpa [I, x'] using trace_vecMulVec_le_trace_vecMulVec_roundLeft W (x := x) (y := y') hx
  have hindicator :
      Matrix.vecMulVec x' y' = (rectangle_indicator I J : Matrix (Fin m) (Fin n) ℝ) := by
    -- The two rounded `0/1` vectors define exactly the corresponding rectangle indicator.
    simpa [I, J, x', y'] using vecMulVec_indicator_eq_rectangleIndicator I J
  have hrectangle :
      Matrix.trace (W * (Matrix.vecMulVec x' y')ᵀ) ≤ rectangle_trace_max W := by
    -- The fully rounded witness is an actual rectangle, hence bounded by the rectangle maximum.
    rw [hindicator]
    exact (rectangle_trace_max_isGreatest W).2 ⟨I, J, rfl⟩
  calc
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ)
        ≤ Matrix.trace (W * (Matrix.vecMulVec x y')ᵀ) := hroundRight
    _ ≤ Matrix.trace (W * (Matrix.vecMulVec x' y')ᵀ) := hroundLeft
    _ ≤ rectangle_trace_max W := hrectangle

/-- Helper for Theorem 4.58: the relaxed rank-one maximum is bounded by the rectangle maximum via
the source-faithful rounding argument. -/
lemma rectangle_trace_relaxed_max_le_rectangle_trace_max
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) :
    rectangle_trace_relaxed_max W ≤ rectangle_trace_max W := by
  have hne :
      {z |
        ∃ R : Matrix (Fin m) (Fin n) ℝ,
          isUnitBoxRankOneMatrix R ∧ Matrix.trace (W * Rᵀ) = z}.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, by simp⟩
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro j
      simp
    · ext i j
      simp [Matrix.vecMulVec]
  -- Every relaxed witness rounds to a genuine rectangle without decreasing its value.
  refine csSup_le hne ?_
  intro z hz
  rcases hz with ⟨R, ⟨x, y, hx, hy, rfl⟩, rfl⟩
  exact trace_vecMulVec_le_rectangle_trace_max_of_unitBox W hx hy

/-- Helper for Theorem 4.58: the relaxed maximum is nonnegative because the zero rank-one witness
is admissible. -/
lemma rectangle_trace_relaxed_max_nonneg
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ rectangle_trace_relaxed_max W := by
  have hzero :
      (0 : ℝ) ∈
        {z |
          ∃ R : Matrix (Fin m) (Fin n) ℝ,
            isUnitBoxRankOneMatrix R ∧ Matrix.trace (W * Rᵀ) = z} := by
    refine ⟨0, ?_, by simp⟩
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro j
      simp
    · ext i j
      simp [Matrix.vecMulVec]
  -- The relaxation contains the zero witness, so its supremum is at least zero.
  exact le_csSup (rectangle_trace_relaxed_values_bddAbove W) hzero

/-- Helper for Theorem 4.58: every rank-one matrix with entries in `[0, 1]` has trace pairing
with `W` bounded by the relaxed rectangle maximum that also admits the zero outer product. -/
lemma trace_vecMulVec_le_rectangle_trace_relaxed_max_of_unitBox
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin m → ℝ}
    {y : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤ rectangle_trace_relaxed_max W := by
  -- The current rank-one witness lies in the relaxation, so its value is below the supremum.
  exact le_csSup
    (rectangle_trace_relaxed_values_bddAbove W)
    ⟨Matrix.vecMulVec x y, ⟨x, y, hx, hy, rfl⟩, rfl⟩

/-- Helper for Theorem 4.58: scaling a nonnegative rank-one summand down to the unit box bounds its
trace pairing by `rectangle_trace_relaxed_max W` times the product of its sup norms. -/
lemma trace_vecMulVec_le_rectangle_trace_relaxed_max_mul_norm_mul_norm_of_nonnegative
    {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    {u : Fin m → ℝ}
    {v : Fin n → ℝ}
    (hu : ∀ i, 0 ≤ u i)
    (hv : ∀ j, 0 ≤ v j) :
    Matrix.trace (W * (Matrix.vecMulVec u v)ᵀ) ≤
      rectangle_trace_relaxed_max W * (‖u‖ * ‖v‖) := by
  by_cases hu0 : ‖u‖ = 0
  · have hu_eq_zero : u = 0 := norm_eq_zero.mp hu0
    subst u
    simp
  · by_cases hv0 : ‖v‖ = 0
    · have hv_eq_zero : v = 0 := norm_eq_zero.mp hv0
      subst v
      simp
    · have hu_pos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
      have hv_pos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0)
      let x : Fin m → ℝ := fun i ↦ u i / ‖u‖
      let y : Fin n → ℝ := fun j ↦ v j / ‖v‖
      have hxbox : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
        intro i
        refine ⟨div_nonneg (hu i) hu_pos.le, ?_⟩
        have hui_norm : ‖u i‖ ≤ ‖u‖ := by
          rw [Pi.norm_def]
          exact_mod_cast
            (Finset.le_sup (s := Finset.univ) (f := fun b ↦ ‖u b‖₊) (b := i) (hb := by simp))
        have hui_le : u i ≤ ‖u‖ := by
          simpa [abs_of_nonneg (hu i)] using hui_norm
        change u i / ‖u‖ ≤ 1
        rw [div_eq_mul_inv]
        have h_inv_nonneg : 0 ≤ ‖u‖⁻¹ := inv_nonneg.mpr hu_pos.le
        have hmul : u i * ‖u‖⁻¹ ≤ ‖u‖ * ‖u‖⁻¹ :=
          mul_le_mul_of_nonneg_right hui_le h_inv_nonneg
        simpa [hu0, mul_assoc] using hmul
      have hybox : ∀ j, 0 ≤ y j ∧ y j ≤ 1 := by
        intro j
        refine ⟨div_nonneg (hv j) hv_pos.le, ?_⟩
        have hvj_norm : ‖v j‖ ≤ ‖v‖ := by
          rw [Pi.norm_def]
          exact_mod_cast
            (Finset.le_sup (s := Finset.univ) (f := fun b ↦ ‖v b‖₊) (b := j) (hb := by simp))
        have hvj_le : v j ≤ ‖v‖ := by
          simpa [abs_of_nonneg (hv j)] using hvj_norm
        change v j / ‖v‖ ≤ 1
        rw [div_eq_mul_inv]
        have h_inv_nonneg : 0 ≤ ‖v‖⁻¹ := inv_nonneg.mpr hv_pos.le
        have hmul : v j * ‖v‖⁻¹ ≤ ‖v‖ * ‖v‖⁻¹ :=
          mul_le_mul_of_nonneg_right hvj_le h_inv_nonneg
        simpa [hv0, mul_assoc] using hmul
      have hu_scale : u = ‖u‖ • x := by
        funext i
        dsimp [x]
        field_simp [hu0]
      have hv_scale : v = ‖v‖ • y := by
        funext j
        dsimp [y]
        field_simp [hv0]
      have hvec :
          Matrix.vecMulVec u v = (‖u‖ * ‖v‖) • Matrix.vecMulVec x y := by
        calc
          Matrix.vecMulVec u v = Matrix.vecMulVec (‖u‖ • x) v := by
            conv_lhs => rw [hu_scale]
          _ = ‖u‖ • Matrix.vecMulVec x v := by rw [Matrix.smul_vecMulVec]
          _ = ‖u‖ • Matrix.vecMulVec x (‖v‖ • y) := by
            conv_lhs =>
              arg 2
              rw [hv_scale]
          _ = ‖u‖ • (‖v‖ • Matrix.vecMulVec x y) := by rw [Matrix.vecMulVec_smul]
          _ = (‖u‖ * ‖v‖) • Matrix.vecMulVec x y := by rw [smul_smul]
      have hunit :
          Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) ≤ rectangle_trace_relaxed_max W :=
        trace_vecMulVec_le_rectangle_trace_relaxed_max_of_unitBox W hxbox hybox
      have hscale_nonneg : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg u) (norm_nonneg v)
      have hscaled :
          Matrix.trace (W * (Matrix.vecMulVec u v)ᵀ) =
            (‖u‖ * ‖v‖) * Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) := by
        rw [hvec, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      calc
        Matrix.trace (W * (Matrix.vecMulVec u v)ᵀ)
            = (‖u‖ * ‖v‖) * Matrix.trace (W * (Matrix.vecMulVec x y)ᵀ) := hscaled
        _ ≤ (‖u‖ * ‖v‖) * rectangle_trace_relaxed_max W :=
          mul_le_mul_of_nonneg_left hunit hscale_nonneg
        _ = rectangle_trace_relaxed_max W * (‖u‖ * ‖v‖) := by ring

/-- Helper for Theorem 4.58: in a sum of entrywise-nonnegative outer products, the norm product of
each summand is bounded by the ambient entrywise sup norm. -/
lemma outerProductScale_le_entrywiseNorm_of_nonnegative_sum
    {m n t : ℕ}
    {S : Matrix (Fin m) (Fin n) ℝ}
    {U : Fin t → Fin m → ℝ}
    {V : Fin t → Fin n → ℝ}
    (hU : ∀ h i, 0 ≤ U h i)
    (hV : ∀ h j, 0 ≤ V h j)
    (hS : S = ∑ h, Matrix.vecMulVec (U h) (V h)) :
    ∀ h, ‖U h‖ * ‖V h‖ ≤ ‖S‖ := by
  intro h
  by_cases hm : m = 0
  · have hUh : ‖U h‖ = 0 := by
      -- If there are no row indices, every row factor is the zero function.
      subst hm
      simp [Pi.norm_def]
    simp [hUh]
  · by_cases hn : n = 0
    · have hVh : ‖V h‖ = 0 := by
        -- If there are no column indices, every column factor is the zero function.
        subst hn
        simp [Pi.norm_def]
      simp [hVh]
    · have hm_pos : 0 < m := Nat.pos_iff_ne_zero.mpr hm
      have hn_pos : 0 < n := Nat.pos_iff_ne_zero.mpr hn
      let i0 : Fin m := ⟨0, hm_pos⟩
      let j0 : Fin n := ⟨0, hn_pos⟩
      let _ : Nonempty (Fin m) := ⟨i0⟩
      let _ : Nonempty (Fin n) := ⟨j0⟩
      obtain ⟨iMax, hiMax⟩ := Finite.exists_max (fun i : Fin m ↦ U h i)
      obtain ⟨jMax, hjMax⟩ := Finite.exists_max (fun j : Fin n ↦ V h j)
      have hU_norm : ‖U h‖ = U h iMax := by
        -- The row factor is nonnegative, so its sup norm is attained at a maximizing coordinate.
        calc
          ‖U h‖ = ↑(Finset.univ.sup fun i : Fin m ↦ ‖U h i‖₊) := Pi.norm_def (U h)
          _ = ↑‖U h iMax‖₊ := by
            congr 1
            apply le_antisymm
            · refine Finset.sup_le ?_
              intro i hi
              simpa [Real.nnnorm_of_nonneg (hU h i), Real.nnnorm_of_nonneg (hU h iMax)] using
                hiMax i
            · exact Finset.le_sup (f := fun i : Fin m ↦ ‖U h i‖₊) (by simp)
          _ = U h iMax := by
            simpa [Real.nnnorm_of_nonneg (hU h iMax)] using
              (NNReal.coe_mk (U h iMax) (hU h iMax))
      have hV_norm : ‖V h‖ = V h jMax := by
        -- The same maximizing-coordinate argument applies to the column factor.
        calc
          ‖V h‖ = ↑(Finset.univ.sup fun j : Fin n ↦ ‖V h j‖₊) := Pi.norm_def (V h)
          _ = ↑‖V h jMax‖₊ := by
            congr 1
            apply le_antisymm
            · refine Finset.sup_le ?_
              intro j hj
              simpa [Real.nnnorm_of_nonneg (hV h j), Real.nnnorm_of_nonneg (hV h jMax)] using
                hjMax j
            · exact Finset.le_sup (f := fun j : Fin n ↦ ‖V h j‖₊) (by simp)
          _ = V h jMax := by
            simpa [Real.nnnorm_of_nonneg (hV h jMax)] using
              (NNReal.coe_mk (V h jMax) (hV h jMax))
      have h_entry_le : U h iMax * V h jMax ≤ S iMax jMax := by
        -- Compare the chosen rank-one entry with the corresponding entry of the whole sum.
        rw [hS]
        have hsum :
            (∑ h', Matrix.vecMulVec (U h') (V h')) iMax jMax =
              ∑ h', U h' iMax * V h' jMax := by
          simpa [Matrix.vecMulVec] using
            (Matrix.sum_apply iMax jMax Finset.univ (fun h' ↦ Matrix.vecMulVec (U h') (V h')))
        rw [hsum]
        simpa using
          (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun h' : Fin t ↦ U h' iMax * V h' jMax)
            (fun h' _ ↦ mul_nonneg (hU h' iMax) (hV h' jMax))
            (by simp : h ∈ Finset.univ))
      have hS_nonneg : 0 ≤ S iMax jMax := by
        -- The ambient entry is nonnegative because it dominates a nonnegative summand entry.
        exact le_trans (mul_nonneg (hU h iMax) (hV h jMax)) h_entry_le
      -- Route correction: instead of searching for a global norm lemma on rank-one factors,
      -- evaluate the maximizing summand entry and then bound that entry by the matrix sup norm.
      calc
        ‖U h‖ * ‖V h‖ = U h iMax * V h jMax := by rw [hU_norm, hV_norm]
        _ ≤ S iMax jMax := h_entry_le
        _ = ‖S iMax jMax‖ := by rw [Real.norm_of_nonneg hS_nonneg]
        _ ≤ ‖S‖ := Matrix.norm_entry_le_entrywise_sup_norm S

/-- Helper for Theorem 4.58: proof-oriented multiplication estimate using the local quantity
`rectangle_trace_relaxed_max W` before comparing it to the source rectangle maximum `α`. -/
private theorem trace_le_nonnegative_rank_mul_alpha_mul_entrywise_norm_aux
    {m n : ℕ}
    (S : Matrix.Nonnegative (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (W * Sᵀ) ≤
      (rank₊ S : ℝ) *
        (rectangle_trace_relaxed_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) := by
  obtain ⟨U, V, hU, hV, hS⟩ := (nonnegative_rank_isLeast_nonnegative_rank_one_sum_count S).1
  have hterm :
      ∀ h : Fin (rank₊ S),
        Matrix.trace (W * (Matrix.vecMulVec (U h) (V h))ᵀ) ≤
          rectangle_trace_relaxed_max W * (‖U h‖ * ‖V h‖) := by
    intro h
    -- Apply the normalized unit-box bound to each nonnegative rank-one summand.
    exact trace_vecMulVec_le_rectangle_trace_relaxed_max_mul_norm_mul_norm_of_nonnegative W
      (hU h) (hV h)
  have hscale :
      ∀ h : Fin (rank₊ S),
        ‖U h‖ * ‖V h‖ ≤ ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖ :=
    outerProductScale_le_entrywiseNorm_of_nonnegative_sum hU hV hS
  have hrelax_nonneg : 0 ≤ rectangle_trace_relaxed_max W :=
    rectangle_trace_relaxed_max_nonneg W
  calc
    Matrix.trace (W * Sᵀ)
        = Matrix.trace (W * (∑ h, Matrix.vecMulVec (U h) (V h))ᵀ) := by
            simpa using
              congrArg
                (fun A : Matrix (Fin m) (Fin n) ℝ ↦ Matrix.trace (W * Aᵀ))
                hS
    _ = Matrix.trace (W * ∑ h, (Matrix.vecMulVec (U h) (V h))ᵀ) := by
          rw [Matrix.transpose_sum]
    _ = Matrix.trace (∑ h, W * (Matrix.vecMulVec (U h) (V h))ᵀ) := by
          rw [Matrix.mul_sum]
    _ = ∑ h, Matrix.trace (W * (Matrix.vecMulVec (U h) (V h))ᵀ) := by
          rw [Matrix.trace_sum]
    _ ≤ ∑ h, rectangle_trace_relaxed_max W * (‖U h‖ * ‖V h‖) := by
          refine Finset.sum_le_sum ?_
          intro h hh
          exact hterm h
    _ ≤ ∑ h, rectangle_trace_relaxed_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖ := by
          refine Finset.sum_le_sum ?_
          intro h hh
          exact mul_le_mul_of_nonneg_left (hscale h) hrelax_nonneg
    _ = (rank₊ S : ℝ) *
          (rectangle_trace_relaxed_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_left_comm]

/-- Theorem 4.58. Let `S` be an `m × n` nonnegative matrix and let `t` be its nonnegative rank.
Then, for every `m × n` matrix `W`,
`⟪W, S⟫ ≤ t * (α * ||S||_∞)` for the source inner product
`⟪W, S⟫ = Matrix.trace (W * Sᵀ)`, where `α` is represented by `rectangle_trace_max W`, the
maximum trace pairing with all `0/1` rectangle indicators `rectangle_indicator I J`, including the
zero rectangle obtained from an empty row or column set. The entrywise `∞`-norm surface is written
explicitly as the sup norm of the underlying function
`fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j`. -/
theorem trace_le_nonnegative_rank_mul_alpha_mul_entrywise_norm
    {m n : ℕ}
    (S : Matrix.Nonnegative (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (W * Sᵀ) ≤
      (rank₊ S : ℝ) *
        (rectangle_trace_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) := by
  have haux := trace_le_nonnegative_rank_mul_alpha_mul_entrywise_norm_aux S W
  have hnorm_nonneg :
      0 ≤ ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖ := norm_nonneg _
  have hcompare :
      rectangle_trace_relaxed_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖ ≤
        rectangle_trace_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖ := by
    -- Replace the relaxed maximum by the genuine rectangle maximum after the rounding lemma.
    exact mul_le_mul_of_nonneg_right
      (rectangle_trace_relaxed_max_le_rectangle_trace_max W)
      hnorm_nonneg
  have hrank_nonneg : 0 ≤ (rank₊ S : ℝ) := by
    exact_mod_cast Nat.zero_le (rank₊ S)
  calc
    Matrix.trace (W * Sᵀ)
        ≤ (rank₊ S : ℝ) *
            (rectangle_trace_relaxed_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) :=
          haux
    _ ≤ (rank₊ S : ℝ) *
          (rectangle_trace_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) := by
            exact mul_le_mul_of_nonneg_left hcompare hrank_nonneg

/-- Quotient-form corollary of the multiplicative lower bound above, under an explicit positivity
assumption on the denominator. -/
theorem nonnegative_rank_ge_trace_div_alpha_mul_entrywise_norm
    {m n : ℕ}
    (S : Matrix.Nonnegative (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin m) (Fin n) ℝ)
    (hden :
      0 < rectangle_trace_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) :
    (rank₊ S : ℝ) ≥
      Matrix.trace (W * Sᵀ) /
        (rectangle_trace_max W * ‖fun i j ↦ (S : Matrix (Fin m) (Fin n) ℝ) i j‖) := by
  -- Divide the multiplicative inequality by the positive denominator.
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using
    (div_le_iff₀ hden).2 (trace_le_nonnegative_rank_mul_alpha_mul_entrywise_norm S W)
