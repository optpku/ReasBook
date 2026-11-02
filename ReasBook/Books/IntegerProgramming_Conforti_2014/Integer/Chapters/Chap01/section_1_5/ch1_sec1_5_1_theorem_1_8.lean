module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_7
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_lemma_1_3

@[expose] public section

open scoped BigOperators
open scoped Matrix

open Matrix

variable {n : ℕ}

/-- The gcd of the coefficients of an integer row vector. -/
def coefficientGcd (a : Fin n → ℤ) : ℤ :=
  Finset.univ.gcd a

/-- Every coefficient of an integer row vector is divisible by `coefficientGcd a`. -/
theorem coefficientGcd_dvd (a : Fin n → ℤ) (i : Fin n) :
    coefficientGcd a ∣ a i := by
  -- Unfold the coefficient gcd and read off the divisibility property from the finset gcd.
  rw [coefficientGcd]
  exact Finset.gcd_dvd (by simp)

/-- Helper for Theorem 1.8: adjoining one head coordinate identifies the coefficient gcd with the
gcd of the new head entry and the old tail coefficient gcd. -/
theorem coefficientGcd_cons (x : ℤ) (xs : Fin n → ℤ) :
    coefficientGcd (Fin.cons x xs) = (Int.gcd x (coefficientGcd xs) : ℤ) := by
  -- Compare the two gcds by divisibility: the row gcd divides both the new head and the old tail
  -- gcd, and conversely the binary gcd is exactly the gcd of the decomposed index set.
  have huniv :
      (Finset.univ : Finset (Fin (n + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    cases i using Fin.cases <;> simp
  rw [coefficientGcd, huniv, Finset.gcd_insert, Finset.gcd_image, coefficientGcd]
  simpa using (Int.coe_gcd x (coefficientGcd xs)).symm

/-- Helper for Theorem 1.8: a Bézout witness for the tail extends to one for a new head
coordinate by the binary extended gcd coefficients. -/
lemma exists_sum_mul_eq_coefficientGcd_cons
    (x : ℤ)
    (xs : Fin n → ℤ)
    (u : Fin n → ℤ)
    (hu : (∑ i : Fin n, xs i * u i) = coefficientGcd xs) :
    ∃ v : Fin (n + 1) → ℤ, (∑ i : Fin (n + 1), ((Fin.cons x xs : Fin (n + 1) → ℤ) i) * v i) =
      coefficientGcd (Fin.cons x xs) := by
  let v : Fin (n + 1) → ℤ :=
    Fin.cons (Int.gcdA x (coefficientGcd xs))
      (fun i ↦ Int.gcdB x (coefficientGcd xs) * u i)
  refine ⟨v, ?_⟩
  -- Split off the head summand, then factor the common Bézout coefficient from the tail sum.
  calc
    (∑ i : Fin (n + 1),
        ((Fin.cons x xs : Fin (n + 1) → ℤ) i) * v i) =
          x * Int.gcdA x (coefficientGcd xs) +
            ∑ i : Fin n, xs i * (Int.gcdB x (coefficientGcd xs) * u i) := by
              rw [Fin.sum_univ_succ]
              simp [v]
    _ =
          x * Int.gcdA x (coefficientGcd xs) +
            Int.gcdB x (coefficientGcd xs) * ∑ i : Fin n, xs i * u i := by
              congr 1
              calc
                ∑ i : Fin n, xs i * (Int.gcdB x (coefficientGcd xs) * u i)
                    =
                      ∑ i : Fin n, Int.gcdB x (coefficientGcd xs) * (xs i * u i) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                _ = Int.gcdB x (coefficientGcd xs) * ∑ i : Fin n, xs i * u i := by
                      rw [Finset.mul_sum]
    _ =
          x * Int.gcdA x (coefficientGcd xs) +
            Int.gcdB x (coefficientGcd xs) * coefficientGcd xs := by
              rw [hu]
    _ = coefficientGcd (Fin.cons x xs) := by
          rw [coefficientGcd_cons, Int.gcd_eq_gcd_ab]
          ring

/-- The coefficient gcd is an integer linear combination of the coefficients. -/
theorem exists_sum_mul_eq_coefficientGcd (a : Fin n → ℤ) :
    ∃ u : Fin n → ℤ, (∑ i : Fin n, a i * u i) = coefficientGcd a := by
  induction n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      -- In the empty dimension, both the sum and the coefficient gcd are zero.
      simp [coefficientGcd]
  | succ n ih =>
      rcases ih (Fin.tail a) with ⟨u, hu⟩
      rcases exists_sum_mul_eq_coefficientGcd_cons (a 0) (Fin.tail a) u hu with ⟨v, hv⟩
      -- Rewrite `a` as its head-tail decomposition and reuse the successor witness.
      refine ⟨v, ?_⟩
      simpa [Fin.cons_self_tail] using hv

/-- A nonzero integer row vector has nonzero coefficient gcd. -/
theorem coefficientGcd_ne_zero_of_nonzero (a : Fin n → ℤ) (ha : a ≠ 0) :
    coefficientGcd a ≠ 0 := by
  intro hg
  -- If the finset gcd vanished, every coordinate vanished, contradicting `a ≠ 0`.
  rw [coefficientGcd, Finset.gcd_eq_zero_iff] at hg
  apply ha
  funext i
  exact hg i (by simp)

/-- The coefficient-gcd normal form row `(coefficientGcd a, 0, ..., 0)`. -/
def coefficientGcdNormalFormRow (a : Fin n → ℤ) : Fin n → ℤ :=
  fun j ↦ if j.1 = 0 then coefficientGcd a else 0

/-- Helper for Theorem 1.8: on `Fin (n + 1)`, the coefficient-gcd normal form row is
`Fin.cons (coefficientGcd a) 0`. -/
theorem coefficientGcdNormalFormRow_eq_cons (a : Fin (n + 1) → ℤ) :
    coefficientGcdNormalFormRow a =
      (Fin.cons (coefficientGcd a) (fun _ : Fin n ↦ 0) : Fin (n + 1) → ℤ) := by
  -- The defining `if` keeps the head coordinate and zeroes every tail coordinate.
  ext j
  cases j using Fin.cases with
  | zero =>
      simp [coefficientGcdNormalFormRow]
  | succ j =>
      simp [coefficientGcdNormalFormRow]

/-- Helper for Theorem 1.8: lifting a tail square matrix to one dimension higher fixes the head
coordinate and applies the original matrix on the tail. -/
def liftTailMatrix (S : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons
    (Fin.cons 1 (fun _ : Fin n ↦ 0))
    (fun i ↦ Fin.cons 0 (fun j ↦ S i j))

/-- Helper for Theorem 1.8: the lifted tail matrix carries a head-tail row vector by fixing the
head coordinate and applying the original tail action. -/
theorem vecMul_liftTailMatrix
    (x : ℤ)
    (xs : Fin n → ℤ)
    (S : Matrix (Fin n) (Fin n) ℤ) :
    (Fin.cons x xs) ᵥ* liftTailMatrix S = Fin.cons x (xs ᵥ* S) := by
  -- The lifted matrix has only the identity entry in the head column and the original `S` block
  -- in the tail columns, so the row action splits cleanly into head and tail pieces.
  ext j
  cases j using Fin.cases with
  | zero =>
      simp [liftTailMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  | succ j =>
      simp [liftTailMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- Helper for Theorem 1.8: lifting a tail inverse gives an inverse for the lifted tail matrix. -/
theorem liftTailMatrix_mul
    {S V : Matrix (Fin n) (Fin n) ℤ}
    (hSV : S * V = 1) :
    liftTailMatrix S * liftTailMatrix V = 1 := by
  -- Entrywise, the head row and column behave like the identity and the tail block multiplies as
  -- `S * V`.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [liftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      | succ j =>
          simp [liftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ, eq_comm]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          simp [liftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ, eq_comm]
      | succ j =>
          simpa [liftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] using
            congrArg (fun M : Matrix (Fin n) (Fin n) ℤ ↦ M i j) hSV

/-- Helper for Theorem 1.8: extending a `2 × 2` matrix by the identity on the remaining tail
coordinates acts only on the first two coordinates. -/
def liftHeadMatrix (U : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  Fin.cons
    (Fin.cons (U 0 0) (Fin.cons (U 0 1) (fun _ : Fin n ↦ 0)))
    (Fin.cons
      (Fin.cons (U 1 0) (Fin.cons (U 1 1) (fun _ : Fin n ↦ 0)))
      (fun i ↦ Fin.cons 0 (Fin.cons 0 (fun j ↦ if i = j then 1 else 0))))

/-- Helper for Theorem 1.8: the head-step lift preserves multiplication by extending a `2 × 2`
inverse with the identity on the tail. -/
theorem liftHeadMatrix_mul
    {U W : Matrix (Fin 2) (Fin 2) ℤ}
    (hUW : U * W = 1) :
    liftHeadMatrix (n := n) U * liftHeadMatrix (n := n) W = 1 := by
  -- The first two coordinates multiply as `U * W`, while the remaining coordinates see only the
  -- identity tail block.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simpa [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using
            congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 0 0) hUW
      | succ j =>
          cases j using Fin.cases with
          | zero =>
              simpa [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using
                congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 0 1) hUW
          | succ j =>
              have hzero : ¬ (0 : Fin (n + 2)) = j.succ.succ := by
                simpa [eq_comm] using (Fin.succ_ne_zero j.succ)
              simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hzero]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              simpa [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using
                congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 1 0) hUW
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  simpa [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ] using
                    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M 1 1) hUW
              | succ j =>
                  have hone : ¬ (1 : Fin (n + 2)) = j.succ.succ := by
                    simpa [eq_comm, Fin.succ_zero_eq_one] using (Fin.succ_succ_ne_one j)
                  simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hone]
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              have hone : ¬ i.succ.succ = (1 : Fin (n + 2)) := by
                simpa [Fin.succ_zero_eq_one] using (Fin.succ_succ_ne_one i)
              simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hone]
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  have hone : ¬ i.succ.succ = (1 : Fin (n + 2)) := by
                    simpa [Fin.succ_zero_eq_one] using (Fin.succ_succ_ne_one i)
                  simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hone]
              | succ j =>
                  by_cases hij : i = j
                  · subst hij
                    simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
                  · simp [liftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, hij]

/-- Helper for Theorem 1.8: the lifted head matrix acts on the first two coordinates by the given
`2 × 2` row action and leaves the remaining tail coordinates unchanged at zero. -/
theorem vecMul_liftHeadMatrix
    (x g : ℤ)
    (U : Matrix (Fin 2) (Fin 2) ℤ) :
    (Fin.cons x (Fin.cons g (fun _ : Fin n ↦ 0))) ᵥ* liftHeadMatrix (n := n) U =
      Fin.cons (((![x, g] : Fin 2 → ℤ) ᵥ* U) 0)
        (Fin.cons (((![x, g] : Fin 2 → ℤ) ᵥ* U) 1) (fun _ : Fin n ↦ 0)) := by
  -- Only the first two coordinates of the input are nonzero, so the lifted matrix reproduces the
  -- `2 × 2` row action on that active block.
  ext j
  cases j using Fin.cases with
  | zero =>
      simp [liftHeadMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  | succ j =>
      cases j using Fin.cases with
      | zero =>
          simp [liftHeadMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
      | succ j =>
          simp [liftHeadMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

/-- Helper for Theorem 1.8: the normalized row evaluates on a head-tail vector by keeping only
the first coordinate. -/
theorem normalFormRow_dot_cons
    (a : Fin (n + 1) → ℤ)
    (t : ℤ)
    (z : Fin n → ℤ) :
    coefficientGcdNormalFormRow a ⬝ᵥ Fin.cons t z = coefficientGcd a * t := by
  -- In the normal form row, all tail entries are zero.
  rw [coefficientGcdNormalFormRow_eq_cons]
  simp [dotProduct, Fin.sum_univ_succ]

/-- Helper for Theorem 1.8: the Bézout head step can be extended by the identity on the tail to
collapse the first two active coordinates to the coefficient gcd normal form. -/
theorem exists_unimodular_headGcdStep
    (x : ℤ)
    (xs : Fin (n + 1) → ℤ) :
    ∃ R Rinv : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ,
      R * Rinv = 1 ∧
      Rinv * R = 1 ∧
      (Fin.cons x (coefficientGcdNormalFormRow xs)) ᵥ* R =
        coefficientGcdNormalFormRow (Fin.cons x xs) := by
  by_cases hzero : x = 0 ∧ coefficientGcd xs = 0
  · refine ⟨1, 1, by simp, by simp, ?_⟩
    -- When both active coordinates vanish, the identity matrix already gives the target normal
    -- form because the new coefficient gcd is zero.
    rw [coefficientGcdNormalFormRow_eq_cons, coefficientGcdNormalFormRow_eq_cons,
      coefficientGcd_cons, hzero.1, hzero.2]
    ext j
    cases j using Fin.cases with
    | zero =>
        simp
    | succ j =>
        cases j using Fin.cases with
        | zero =>
            simp
        | succ j =>
            simp
  · have hnot : x ≠ 0 ∨ coefficientGcd xs ≠ 0 := by
      by_cases hx : x = 0
      · right
        intro hg
        exact hzero ⟨hx, hg⟩
      · exact Or.inl hx
    rcases Int.existsGLTwoVecMul_eq_gcd_zero x (coefficientGcd xs) hnot with ⟨U, hU⟩
    refine ⟨liftHeadMatrix (n := n) (U : Matrix (Fin 2) (Fin 2) ℤ),
      liftHeadMatrix (n := n) ((↑(U⁻¹)) : Matrix (Fin 2) (Fin 2) ℤ), ?_, ?_, ?_⟩
    · -- Extend the inverse coming from the `GL` witness by the identity on the tail.
      exact liftHeadMatrix_mul (n := n) (by simp)
    · -- The other multiplication order is identical.
      exact liftHeadMatrix_mul (n := n) (by simp)
    · -- First reduce the lifted action to the original `2 × 2` Bézout step, then identify the
      -- resulting first coordinate with the coefficient gcd of the longer row.
      calc
        (Fin.cons x (coefficientGcdNormalFormRow xs)) ᵥ*
            liftHeadMatrix (n := n) (U : Matrix (Fin 2) (Fin 2) ℤ) =
            Fin.cons (((![x, coefficientGcd xs] : Fin 2 → ℤ) ᵥ* (U : Matrix (Fin 2) (Fin 2) ℤ)) 0)
              (Fin.cons
                (((![x, coefficientGcd xs] : Fin 2 → ℤ) ᵥ* (U : Matrix (Fin 2) (Fin 2) ℤ)) 1)
                (fun _ : Fin n ↦ 0)) := by
              simpa [coefficientGcdNormalFormRow_eq_cons] using
                vecMul_liftHeadMatrix (n := n) x (coefficientGcd xs)
                  (U : Matrix (Fin 2) (Fin 2) ℤ)
        _ = Fin.cons ((Int.gcd x (coefficientGcd xs) : ℤ))
              (Fin.cons 0 (fun _ : Fin n ↦ 0)) := by
              simpa using
                congrArg
                  (fun w : Fin 2 → ℤ ↦
                    (Fin.cons (w 0) (Fin.cons (w 1) (fun _ : Fin n ↦ 0)) : Fin (n + 2) → ℤ)) hU
        _ = coefficientGcdNormalFormRow (Fin.cons x xs) := by
              rw [coefficientGcdNormalFormRow_eq_cons, coefficientGcd_cons]
              ext j
              cases j using Fin.cases with
              | zero =>
                  simp
              | succ j =>
                  cases j using Fin.cases with
                  | zero =>
                      simp
                  | succ j =>
                      simp

/-- Integer solvability of a one-row equation is equivalent to divisibility by `coefficientGcd a`.
-/
theorem intDot_exists_iff_dvd_coefficientGcd
    (a : Fin n → ℤ)
    (c : ℤ) :
    (∃ x : Fin n → ℤ, a ⬝ᵥ x = c) ↔ coefficientGcd a ∣ c := by
  constructor
  · rintro ⟨x, rfl⟩
    -- Every summand is divisible by the coefficient gcd, so their sum is as well.
    refine Finset.dvd_sum ?_
    intro i hi
    exact dvd_mul_of_dvd_left (coefficientGcd_dvd a i) (x i)
  · rintro ⟨k, hk⟩
    rcases exists_sum_mul_eq_coefficientGcd a with ⟨u, hu⟩
    refine ⟨fun i ↦ k * u i, ?_⟩
    -- Scale a Bézout expression for `coefficientGcd a` by the quotient `k`.
    calc
      a ⬝ᵥ (fun i ↦ k * u i) = ∑ i : Fin n, k * (a i * u i) := by
        simp [dotProduct, mul_assoc, mul_left_comm, mul_comm]
      _ = k * ∑ i : Fin n, a i * u i := by
        rw [Finset.mul_sum]
      _ = k * coefficientGcd a := by rw [hu]
      _ = c := by simpa [mul_comm] using hk.symm

/-- Theorem 1.8 (1): the equation `a x = c` with `x : Fin n → ℤ` is solvable exactly when `c`
comes from an integer divisible by `coefficientGcd a`. -/
theorem realDot_exists_iff
    (a : Fin n → ℤ)
    (c : ℝ) :
    (∃ x : Fin n → ℤ, ((a ⬝ᵥ x : ℤ) : ℝ) = c) ↔
      ∃ z : ℤ, (z : ℝ) = c ∧ coefficientGcd a ∣ z := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a ⬝ᵥ x, hx, ?_⟩
    exact (intDot_exists_iff_dvd_coefficientGcd a (a ⬝ᵥ x)).1 ⟨x, rfl⟩
  · rintro ⟨z, rfl, hz⟩
    rcases (intDot_exists_iff_dvd_coefficientGcd a z).2 hz with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact_mod_cast hx

/-- Helper for Theorem 1.8: the normal-form witness can be built together with an integral
two-sided inverse. -/
theorem exists_unimodular_normalFormAux
    (a : Fin n → ℤ) :
    ∃ T V : Matrix (Fin n) (Fin n) ℤ,
      T * V = 1 ∧
      V * T = 1 ∧
      a ᵥ* T = coefficientGcdNormalFormRow a := by
  induction n with
  | zero =>
      refine ⟨1, 1, by simp, by simp, ?_⟩
      -- On the empty index type, every row is definitionally zero.
      ext i
      exact Fin.elim0 i
  | succ m ih =>
      cases m with
      | zero =>
          let s : ℤ := if 0 ≤ a 0 then 1 else -1
          refine ⟨fun _ _ ↦ s, fun _ _ ↦ s, ?_, ?_, ?_⟩
          · -- In dimension `1`, the sign-correction scalar is its own inverse.
            ext i j
            fin_cases i
            fin_cases j
            by_cases hs : 0 ≤ a 0
            · simp [s, hs, Matrix.mul_apply, Fin.sum_univ_one]
            · simp [s, hs, Matrix.mul_apply, Fin.sum_univ_one]
          · -- The reverse multiplication order is identical in size `1`.
            ext i j
            fin_cases i
            fin_cases j
            by_cases hs : 0 ≤ a 0
            · simp [s, hs, Matrix.mul_apply, Fin.sum_univ_one]
            · simp [s, hs, Matrix.mul_apply, Fin.sum_univ_one]
          · -- Multiply by the sign correction to turn the unique entry into its normalization.
            ext j
            fin_cases j
            by_cases hs : 0 ≤ a 0
            · simp [s, hs, Matrix.vecMul, dotProduct, coefficientGcdNormalFormRow,
                coefficientGcd]
              simpa [Int.abs_eq_normalize] using (abs_of_nonneg hs).symm
            · have hneg : a 0 < 0 := lt_of_not_ge hs
              simp [s, hs, Matrix.vecMul, dotProduct, coefficientGcdNormalFormRow, coefficientGcd,
                mul_comm]
              simpa [Int.abs_eq_normalize] using (abs_of_neg hneg).symm
      | succ n =>
          refine Fin.consCases ?_ a
          intro x xs
          rcases ih xs with ⟨S, V, hSV, hVS, hSform⟩
          have hLiftForm :
              (Fin.cons x xs) ᵥ* liftTailMatrix S = Fin.cons x (coefficientGcdNormalFormRow xs) := by
            -- First separate the head and tail action, then plug in the inductive normal form.
            rw [vecMul_liftTailMatrix, hSform]
          rcases exists_unimodular_headGcdStep (n := n) x xs with
            ⟨R, Rinv, hRRinv, hRinvR, hRform⟩
          refine ⟨liftTailMatrix S * R, Rinv * liftTailMatrix V, ?_, ?_, ?_⟩
          · -- Compose the lifted tail inverse with the head-step inverse.
            calc
              (liftTailMatrix S * R) * (Rinv * liftTailMatrix V) =
                  liftTailMatrix S * (R * (Rinv * liftTailMatrix V)) := by
                    rw [Matrix.mul_assoc]
              _ = liftTailMatrix S * ((R * Rinv) * liftTailMatrix V) := by
                    simp [Matrix.mul_assoc]
              _ = liftTailMatrix S * (R * Rinv) * liftTailMatrix V := by
                    simp [Matrix.mul_assoc]
              _ = liftTailMatrix S * liftTailMatrix V := by rw [hRRinv, Matrix.mul_one]
              _ = 1 := liftTailMatrix_mul hSV
          · -- The reverse multiplication order is analogous.
            calc
              (Rinv * liftTailMatrix V) * (liftTailMatrix S * R) =
                  Rinv * (liftTailMatrix V * (liftTailMatrix S * R)) := by
                    rw [Matrix.mul_assoc]
              _ = Rinv * ((liftTailMatrix V * liftTailMatrix S) * R) := by
                    simp [Matrix.mul_assoc]
              _ = Rinv * (liftTailMatrix V * liftTailMatrix S) * R := by
                    simp [Matrix.mul_assoc]
              _ = Rinv * R := by rw [liftTailMatrix_mul hVS, Matrix.mul_one]
              _ = 1 := hRinvR
          · -- The main row action is the lifted tail normalizer followed by the Bézout head step.
            calc
              (Fin.cons x xs) ᵥ* (liftTailMatrix S * R) =
                  ((Fin.cons x xs) ᵥ* liftTailMatrix S) ᵥ* R := by
                    rw [Matrix.vecMul_vecMul]
              _ = (Fin.cons x (coefficientGcdNormalFormRow xs)) ᵥ* R := by rw [hLiftForm]
              _ = coefficientGcdNormalFormRow (Fin.cons x xs) := hRform

/-- Theorem 1.8 (2): an integer row can be carried by a unimodular change of variables to
`coefficientGcdNormalFormRow a`, i.e. `(coefficientGcd a, 0, ..., 0)`. -/
theorem exists_unimodular_normalForm
    (a : Fin n → ℤ) :
    ∃ T : Matrix (Fin n) (Fin n) ℤ,
      IsUnit T.det ∧
        a ᵥ* T = coefficientGcdNormalFormRow a := by
  rcases exists_unimodular_normalFormAux a with ⟨T, V, hTV, hVT, hform⟩
  refine ⟨T, ?_, hform⟩
  -- Convert the explicit two-sided inverse into unimodularity.
  exact (Matrix.isUnit_det_iff_exists_int_inverse T).2 ⟨V, hTV, hVT⟩

/-- Theorem 1.8 (3): once `a ᵥ* T = (coefficientGcd a, 0, ..., 0)`, every integral solution of
`a x = c` is obtained by applying `T` to a vector with first coordinate `c / coefficientGcd a`. -/
theorem solutionSet_eq_range_insertNth
    (a : Fin (n + 1) → ℤ)
    (ha : a ≠ 0)
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hT : IsUnit T.det)
    (hform : a ᵥ* T = coefficientGcdNormalFormRow a)
    (c : ℤ)
    (hc : coefficientGcd a ∣ c) :
    {x : Fin (n + 1) → ℤ | a ⬝ᵥ x = c} =
      Set.range (fun z : Fin n → ℤ ↦
        (T *ᵥ (Fin.cons (c / coefficientGcd a) z) : Fin (n + 1) → ℤ)) := by
  rcases (Matrix.isUnit_det_iff_exists_int_inverse T).1 hT with ⟨V, hTV, hVT⟩
  have hg_ne : coefficientGcd a ≠ 0 := coefficientGcd_ne_zero_of_nonzero a ha
  ext x
  constructor
  · intro hx
    let y : Fin (n + 1) → ℤ := V *ᵥ x
    have hxTy : x = T *ᵥ y := by
      -- Transport the solution through the integral inverse of `T`.
      calc
        x = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) *ᵥ x := by simp
        _ = (T * V) *ᵥ x := by rw [hTV]
        _ = T *ᵥ (V *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    have hyEq : coefficientGcdNormalFormRow a ⬝ᵥ y = c := by
      -- Rewrite the original equation through the normal-form row.
      calc
        coefficientGcdNormalFormRow a ⬝ᵥ y = (a ᵥ* T) ⬝ᵥ y := by rw [hform]
        _ = a ⬝ᵥ (T *ᵥ y) := by rw [← Matrix.dotProduct_mulVec]
        _ = a ⬝ᵥ x := by rw [hxTy]
        _ = c := hx
    have hyMul : coefficientGcd a * y 0 = c := by
      -- Evaluate the normal-form row on `y` by separating the first coordinate.
      calc
        coefficientGcd a * y 0 =
            coefficientGcdNormalFormRow a ⬝ᵥ Fin.cons (y 0) (Fin.tail y) := by
              symm
              simpa using normalFormRow_dot_cons a (y 0) (Fin.tail y)
        _ = coefficientGcdNormalFormRow a ⬝ᵥ y := by rw [Fin.cons_self_tail]
        _ = c := hyEq
    have hy0 : c / coefficientGcd a = y 0 := by
      -- Since `coefficientGcd a ≠ 0`, divide the recovered first-coordinate identity by it.
      exact Int.ediv_eq_of_eq_mul_left hg_ne (by simpa [mul_comm] using hyMul.symm)
    have hyCons : Fin.cons (c / coefficientGcd a) (Fin.tail y) = y := by
      rw [hy0, Fin.cons_self_tail]
    refine ⟨Fin.tail y, ?_⟩
    calc
      T *ᵥ Fin.cons (c / coefficientGcd a) (Fin.tail y) = T *ᵥ y := by rw [hyCons]
      _ = x := hxTy.symm
  · rintro ⟨z, rfl⟩
    -- Every parametrized vector solves the equation because the normal-form row keeps only the
    -- first coordinate, and the divisibility hypothesis makes that coordinate integral.
    calc
      a ⬝ᵥ (T *ᵥ Fin.cons (c / coefficientGcd a) z) =
          (a ᵥ* T) ⬝ᵥ Fin.cons (c / coefficientGcd a) z := by
            rw [Matrix.dotProduct_mulVec]
      _ = coefficientGcdNormalFormRow a ⬝ᵥ Fin.cons (c / coefficientGcd a) z := by rw [hform]
      _ = coefficientGcd a * (c / coefficientGcd a) := normalFormRow_dot_cons a _ z
      _ = c := by simpa [mul_comm] using Int.ediv_mul_cancel hc

end
