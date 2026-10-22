/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_1.Spectrum
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_7.AffineKrylov
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_7.Error
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

open QuadraticOptimization
open scoped Matrix.Energy

namespace ConjugateGradient

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Helper for Theorem 3.7: the initial affine-Krylov generator
`A.toEuclideanLin f₀ + b` is the matrix image of the initial error. -/
theorem initialGradient_eq_toEuclideanLin_initialError
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    A.toEuclideanLin f₀ + b = A.toEuclideanLin (initialError A b f₀) := by
  -- Rewrite the initial error through the exact minimizer and move the critical-point equation.
  calc
    A.toEuclideanLin f₀ + b
        = A.toEuclideanLin f₀ - A.toEuclideanLin (quadraticFunctionalMinimizer b A) := by
          have hcrit :
              A.toEuclideanLin (quadraticFunctionalMinimizer b A) = -b := by
            exact eq_neg_iff_add_eq_zero.mpr <|
              by simpa [add_comm] using
                QuadraticOptimization.quadraticFunctionalMinimizer_isCriticalPoint b A hA
          rw [hcrit, sub_eq_add_neg, neg_neg]
    _ = A.toEuclideanLin (initialError A b f₀) := by
          rw [initialError, QuadraticOptimization.error_eq_sub, LinearMap.map_sub]

/-- Helper for Theorem 3.7: the current quadratic error splits into the
displacement from `f₀` plus the initial error. -/
theorem error_eq_displacement_add_initialError
    (A : Matrix n n ℝ) (b f₀ f : EuclideanSpace ℝ n) :
    QuadraticOptimization.error A b f = (f - f₀) + initialError A b f₀ := by
  -- Expand both errors against the same minimizer and regroup the differences.
  rw [QuadraticOptimization.error_eq_sub, initialError, QuadraticOptimization.error_eq_sub]
  abel

/-- Helper for Theorem 3.7: every vector in the affine Krylov slice has error
`q(A) (initialError A b f₀)` for some normalized polynomial of degree `≤ v`. -/
theorem error_eq_aeval_initialError_of_mem_affineKrylovSubspace
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ)
    {f : EuclideanSpace ℝ n} (hf : f ∈ affineKrylovSubspace A b f₀ v) :
    ∃ q : Polynomial ℝ,
      q.eval 0 = 1 ∧
      q.degree ≤ v ∧
      QuadraticOptimization.error A b f =
        (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) := by
  rw [mem_affineKrylovSubspace_iff] at hf
  rcases (Krylov.mem_subspace_iff A (A.toEuclideanLin f₀ + b) (f - f₀) v).1 hf with
    ⟨p, hpdeg, hp_eq⟩
  let q : Polynomial ℝ := 1 + p * Polynomial.X
  refine ⟨q, ?_, ?_, ?_⟩
  · -- The normalizing condition comes from the constant term of `1 + p * X`.
    simp [q]
  · -- Multiplying by `X` raises the degree by one, so adding the constant term keeps degree `≤ v`.
    by_cases hp : p = 0
    · simp [q, hp]
    · have hpnat : p.natDegree < v :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
      have hpXnat : (p * Polynomial.X).natDegree ≤ v := by
        simpa [Polynomial.natDegree_mul_X hp] using Nat.succ_le_of_lt hpnat
      exact Polynomial.degree_add_le_of_degree_le
        (Polynomial.degree_one_le.trans Nat.WithBot.coe_nonneg)
        (Polynomial.degree_le_of_natDegree_le hpXnat)
  · -- Rewrite the affine displacement through the Krylov polynomial and then repackage it as `q(A)`.
    calc
      QuadraticOptimization.error A b f = (f - f₀) + initialError A b f₀ := by
        exact error_eq_displacement_add_initialError A b f₀ f
      _ = (Polynomial.aeval A.toEuclideanLin p) (A.toEuclideanLin (initialError A b f₀)) +
            initialError A b f₀ := by
            rw [hp_eq, initialGradient_eq_toEuclideanLin_initialError A b f₀ hA]
      _ = (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) := by
            simp [q, Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_X,
              Module.End.mul_apply, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 3.7: every normalized polynomial candidate determines an
admissible affine-Krylov competitor. -/
theorem normalizedPolynomialCandidate_mem_affineKrylovSubspace
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ)
    (q : Polynomial ℝ) (hq0 : q.eval 0 = 1) (hqdeg : q.degree ≤ v) :
    quadraticFunctionalMinimizer b A +
        (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) ∈
      affineKrylovSubspace A b f₀ v := by
  rw [mem_affineKrylovSubspace_iff]
  have hcoeff0 : q.coeff 0 = 1 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hq0
  have hXdvd : Polynomial.X ∣ q - 1 := by
    refine Polynomial.X_dvd_iff.2 ?_
    simpa [hcoeff0]
  rcases hXdvd with ⟨p, hp_eq⟩
  have hfactor : q - 1 = Polynomial.X * p := by
    simpa [Polynomial.C_1] using hp_eq
  have hpdeg : p.degree < v := by
    by_cases hp : p = 0
    · simpa [hp]
    · have hqsubdeg : (q - 1).degree ≤ v := by
        exact (Polynomial.degree_sub_le q 1).trans <|
          max_le hqdeg (Polynomial.degree_one_le.trans Nat.WithBot.coe_nonneg)
      have hpXnat : (p * Polynomial.X).natDegree ≤ v := by
        apply Polynomial.natDegree_le_of_degree_le
        simpa [hfactor, Polynomial.X_mul] using hqsubdeg
      have hpnat : p.natDegree < v := by
        exact Nat.lt_of_succ_le <| by simpa [Polynomial.natDegree_mul_X hp] using hpXnat
      exact (Polynomial.natDegree_lt_iff_degree_lt hp).1 hpnat
  -- Express the competitor displacement from `f₀` as the Krylov polynomial `p(A)` applied to the generator.
  refine (Krylov.mem_subspace_iff A (A.toEuclideanLin f₀ + b)
    (quadraticFunctionalMinimizer b A +
      (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) - f₀) v).2 ?_
  refine ⟨p, hpdeg, ?_⟩
  calc
    quadraticFunctionalMinimizer b A +
        (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) - f₀
        = (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) -
            initialError A b f₀ := by
              simp [initialError, QuadraticOptimization.error_eq_sub, sub_eq_add_neg,
                add_assoc, add_left_comm, add_comm]
    _ = (Polynomial.aeval A.toEuclideanLin (q - 1)) (initialError A b f₀) := by
          simp [Polynomial.aeval_sub]
    _ = (Polynomial.aeval A.toEuclideanLin (Polynomial.X * p)) (initialError A b f₀) := by
          rw [hfactor]
    _ = (Polynomial.aeval A.toEuclideanLin (p * Polynomial.X)) (initialError A b f₀) := by
          rw [Polynomial.X_mul]
    _ = (Polynomial.aeval A.toEuclideanLin p) (A.toEuclideanLin (initialError A b f₀)) := by
          simp [Polynomial.aeval_mul, Polynomial.aeval_X, Module.End.mul_apply]
    _ = (Polynomial.aeval A.toEuclideanLin p) (A.toEuclideanLin f₀ + b) := by
          rw [← initialGradient_eq_toEuclideanLin_initialError A b f₀ hA]

/-- Helper for Theorem 3.7: matrix Krylov subspaces are monotone in the step
index. -/
theorem krylovSubspace_mono
    (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) {v w : ℕ} (hvw : v ≤ w) :
    Krylov.subspace A x v ≤ Krylov.subspace A x w := by
  -- Reuse the same polynomial witness, since `degree p < v` also implies `degree p < w`.
  intro y hy
  rcases (Krylov.mem_subspace_iff A x y v).1 hy with ⟨p, hpdeg, hp⟩
  refine (Krylov.mem_subspace_iff A x y w).2 ⟨p, lt_of_lt_of_le hpdeg (by exact_mod_cast hvw), hp⟩

/-- Helper for Theorem 3.7: the initial Krylov generator belongs to every
successor Krylov slice. -/
theorem generator_mem_krylovSubspace_succ
    (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) (v : ℕ) :
    x ∈ Krylov.subspace A x (v + 1) := by
  -- Use the constant polynomial `1` in the polynomial-membership characterization.
  refine (Krylov.mem_subspace_iff A x x (v + 1)).2 ?_
  refine ⟨1, ?_, ?_⟩
  · simpa using (show (0 : WithBot ℕ) < (v + 1 : ℕ) by
      exact_mod_cast Nat.succ_pos v)
  · simp

/-- Helper for Theorem 3.7: applying `A` to a vector in the `v`th Krylov slice
lands in the next slice. -/
theorem toEuclideanLin_mem_krylovSubspace_succ
    (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) (v : ℕ)
    (hy : y ∈ Krylov.subspace A x v) :
    A.toEuclideanLin y ∈ Krylov.subspace A x (v + 1) := by
  rcases (Krylov.mem_subspace_iff A x y v).1 hy with ⟨p, hpdeg, rfl⟩
  -- Multiplying the witness polynomial by `X` shifts the Krylov order by one.
  refine (Krylov.mem_subspace_iff A x _ (v + 1)).2 ?_
  refine ⟨Polynomial.X * p, ?_, ?_⟩
  · by_cases hp : p = 0
    · simp [hp]
    · have hpnat : p.natDegree < v :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
      have hmul_nat : (p * Polynomial.X).natDegree ≤ v := by
        simpa [Polynomial.natDegree_mul_X hp] using Nat.succ_le_of_lt hpnat
      exact lt_of_le_of_lt
        (by simpa [Polynomial.X_mul] using Polynomial.degree_le_of_natDegree_le hmul_nat)
        (show (v : WithBot ℕ) < (v + 1 : ℕ) by
          exact_mod_cast Nat.lt_succ_self v)
  · simp [Polynomial.aeval_mul, Polynomial.aeval_X, Module.End.mul_apply]

/-- Helper for Theorem 3.7: the quadratic gradient at any affine-Krylov
competitor belongs to the next Krylov slice. -/
theorem gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSubspace
    (A : Matrix n n ℝ) (b f₀ f : EuclideanSpace ℝ n) (v : ℕ)
    (hf : f ∈ affineKrylovSubspace A b f₀ v) :
    A.toEuclideanLin f + b ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) := by
  rw [mem_affineKrylovSubspace_iff] at hf
  have hdisp :
      f - f₀ ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) v := by
    simpa [vsub_eq_sub] using hf
  have hbase :
      A.toEuclideanLin f₀ + b ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) :=
    generator_mem_krylovSubspace_succ A (A.toEuclideanLin f₀ + b) v
  have himage :
      A.toEuclideanLin (f - f₀) ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) :=
    toEuclideanLin_mem_krylovSubspace_succ A (A.toEuclideanLin f₀ + b) (f - f₀) v hdisp
  -- Expand the gradient around `f₀` and combine the two Krylov-membership pieces.
  have hadd :
      (A.toEuclideanLin f₀ + b) + A.toEuclideanLin (f - f₀) ∈
        Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) :=
    Submodule.add_mem _ hbase himage
  simpa [LinearMap.map_sub, add_assoc, add_left_comm, add_comm] using hadd

/-- Helper for Theorem 3.7: each stored conjugate-gradient gradient agrees with
the true quadratic gradient at the stored solution. -/
theorem iterateGradient_eq_quadraticGradient
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ,
      (iterates A b f₀ v).gradient = A.toEuclideanLin ((iterates A b f₀ v).solution) + b := by
  intro v
  induction v with
  | zero =>
      -- The initial state stores exactly the quadratic gradient at `f₀`.
      simp
  | succ v ih =>
      -- Rewrite one CG step and use linearity of `A.toEuclideanLin`.
      simp [iterates_succ, nextGradient_eq, nextSolution_eq, appliedDirection_eq, ih,
        LinearMap.map_add, LinearMap.map_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 3.7: the iterate solution and direction satisfy the
expected affine-Krylov and Krylov-membership recurrences. -/
private theorem iterateAffineDirectionBundle
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ,
      (iterates A b f₀ v).solution ∈ affineKrylovSubspace A b f₀ v ∧
        (iterates A b f₀ v).direction ∈
          Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) := by
  intro v
  induction v with
  | zero =>
      constructor
      · -- The initial solution is the affine base point itself.
        rw [mem_affineKrylovSubspace_iff]
        simpa [vsub_eq_sub] using
          (show (0 : EuclideanSpace ℝ n) ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) 0 from
            Submodule.zero_mem _)
      · -- The initial direction is the negative of the Krylov generator.
        simpa using
          Submodule.neg_mem
            (Krylov.subspace A (A.toEuclideanLin f₀ + b) 1)
            (generator_mem_krylovSubspace_succ A (A.toEuclideanLin f₀ + b) 0)
  | succ v ih =>
      rcases ih with ⟨hsolution, hdirection⟩
      have hnextSolution :
          (iterates A b f₀ (v + 1)).solution ∈ affineKrylovSubspace A b f₀ (v + 1) := by
        -- Update the affine displacement by adding the current search direction.
        rw [mem_affineKrylovSubspace_iff] at hsolution ⊢
        have hsolution_mono :
            (iterates A b f₀ v).solution - f₀ ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) :=
          krylovSubspace_mono A (A.toEuclideanLin f₀ + b) (Nat.le_succ v) hsolution
        have hnext :
            ((iterates A b f₀ v).solution - f₀) +
                stepSize A (iterates A b f₀ v) • (iterates A b f₀ v).direction ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) :=
          Submodule.add_mem _ hsolution_mono (Submodule.smul_mem _ _ hdirection)
        -- Convert the algebraic displacement into the affine-membership form.
        simpa [vsub_eq_sub, iterates_succ, nextSolution_eq, sub_eq_add_neg, add_assoc,
          add_left_comm, add_comm]
          using hnext
      constructor
      · exact hnextSolution
      · -- The new direction is a combination of the new gradient and the old direction.
        have hnextGradient_eq :
            nextGradient A (iterates A b f₀ v) =
              A.toEuclideanLin ((iterates A b f₀ (v + 1)).solution) + b := by
          simpa [iterates_succ] using iterateGradient_eq_quadraticGradient A b f₀ (v + 1)
        have hnextGradient_mem :
            nextGradient A (iterates A b f₀ v) ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 2) := by
          -- Identify the new stored gradient with the quadratic gradient of the new iterate.
          rw [hnextGradient_eq]
          exact
            gradient_mem_krylovSubspace_succ_of_mem_affineKrylovSubspace A b f₀
              (iterates A b f₀ (v + 1)).solution (v + 1) hnextSolution
        have hdirection_mono :
            (iterates A b f₀ v).direction ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 2) :=
          krylovSubspace_mono A (A.toEuclideanLin f₀ + b) (Nat.le_succ (v + 1)) hdirection
        have hcomb :
            -nextGradient A (iterates A b f₀ v) +
                beta A (iterates A b f₀ v) • (iterates A b f₀ v).direction ∈
              Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 2) :=
          Submodule.add_mem _
            (Submodule.neg_mem _ hnextGradient_mem)
            (Submodule.smul_mem _ _ hdirection_mono)
        simpa [iterates_succ, nextDirection_eq] using hcomb

/-- Helper for Theorem 3.7: every conjugate-gradient solution iterate stays in
the expected affine Krylov slice. -/
theorem iterateSolution_mem_affineKrylov
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ,
      (iterates A b f₀ v).solution ∈ affineKrylovSubspace A b f₀ v := by
  intro v
  exact (iterateAffineDirectionBundle A b f₀ v).1

/-- Helper for Theorem 3.7: every conjugate-gradient search direction belongs to
the next Krylov slice generated by the initial gradient. -/
theorem iterateDirection_mem_krylovSubspaceSucc
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ,
      (iterates A b f₀ v).direction ∈
        Krylov.subspace A (A.toEuclideanLin f₀ + b) (v + 1) := by
  intro v
  exact (iterateAffineDirectionBundle A b f₀ v).2

/-- Helper for Theorem 3.7: a vanishing conjugate-gradient gradient forces the
stored search direction to vanish at the same iterate. -/
theorem iterateDirection_eq_zero_of_gradient_eq_zero
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ,
      (iterates A b f₀ v).gradient = 0 →
        (iterates A b f₀ v).direction = 0 := by
  intro v hgradient
  cases v with
  | zero =>
      -- At the initial state the direction is the negative gradient.
      simpa [iterates_zero, init_direction, init_gradient] using congrArg Neg.neg hgradient
  | succ v =>
      -- On successor iterates the Fletcher-Reeves coefficient collapses when the new gradient vanishes.
      simp [iterates_succ, step_gradient] at hgradient
      simpa [iterates_succ, step_direction, nextDirection_eq, beta_eq, hgradient]
        using hgradient

/-- Helper for Theorem 3.7: `directionSpan A b f₀ v` is the finite span of the
first `v` conjugate-gradient search directions. -/
private def directionSpan
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (v : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ n) :=
  Submodule.span ℝ (Set.range fun j : Fin v => (iterates A b f₀ j.1).direction)

/-- Helper for Theorem 3.7: enlarging the truncation index only enlarges the
finite span of search directions. -/
private theorem directionSpan_mono
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) {v w : ℕ} (hvw : v ≤ w) :
    directionSpan A b f₀ v ≤ directionSpan A b f₀ w := by
  -- Embed each `Fin v` index into `Fin w` and reuse the same search direction.
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span <|
    Set.mem_range.2 ⟨⟨j.1, lt_of_lt_of_le j.2 hvw⟩, rfl⟩

/-- Helper for Theorem 3.7: the `v`th search direction is one of the generators
of `directionSpan A b f₀ (v + 1)`. -/
private theorem iterateDirection_mem_directionSpan
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (v : ℕ) :
    (iterates A b f₀ v).direction ∈ directionSpan A b f₀ (v + 1) := by
  -- Choose the canonical generator indexed by `v : Fin (v + 1)`.
  exact Submodule.subset_span <|
    Set.mem_range.2 ⟨⟨v, Nat.lt_succ_self v⟩, rfl⟩

/-- Helper for Theorem 3.7: every nonzero search direction has a strictly
positive quadratic denominator in the CG step-size formula. -/
private theorem iterateDirection_denominator_pos
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) {v : ℕ}
    (hdir : (iterates A b f₀ v).direction ≠ 0) :
    0 < inner ℝ ((iterates A b f₀ v).direction) (appliedDirection A (iterates A b f₀ v)) := by
  have hpos :
      0 < inner ℝ (A.toEuclideanLin ((iterates A b f₀ v).direction))
          ((iterates A b f₀ v).direction) := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply] using
      hA.dotProduct_mulVec_pos (x := ((iterates A b f₀ v).direction).ofLp)
        (by simpa using hdir)
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hden_eq :
      inner ℝ (A.toEuclideanLin ((iterates A b f₀ v).direction))
          ((iterates A b f₀ v).direction) =
        inner ℝ ((iterates A b f₀ v).direction) (appliedDirection A (iterates A b f₀ v)) := by
    simpa [appliedDirection_eq] using
      hsymm ((iterates A b f₀ v).direction) ((iterates A b f₀ v).direction)
  exact hden_eq ▸ hpos

/-- Helper for Theorem 3.7: each iterate packages the current gradient-direction
pair and the one-step orthogonality relation for the next gradient. -/
private theorem iterateGradientDirectionOrthogonalityBundle
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ v : ℕ,
      inner ℝ ((iterates A b f₀ v).gradient) ((iterates A b f₀ v).direction) =
          -‖(iterates A b f₀ v).gradient‖ ^ 2 ∧
        inner ℝ ((iterates A b f₀ (v + 1)).gradient) ((iterates A b f₀ v).direction) = 0 := by
  intro v
  induction v with
  | zero =>
      have hself :
          inner ℝ ((iterates A b f₀ 0).gradient) ((iterates A b f₀ 0).direction) =
            -‖(iterates A b f₀ 0).gradient‖ ^ 2 := by
        have hgrad0 :
            (iterates A b f₀ 0).gradient = A.toEuclideanLin f₀ + b := by
          simp [iterates_zero, init_gradient]
        have hdir0 :
            (iterates A b f₀ 0).direction = -(A.toEuclideanLin f₀ + b) := by
          simp [iterates_zero, init_direction]
        -- The initial search direction is the negative initial gradient.
        calc
          inner ℝ ((iterates A b f₀ 0).gradient) ((iterates A b f₀ 0).direction)
              = inner ℝ (A.toEuclideanLin f₀ + b) (-(A.toEuclideanLin f₀ + b)) := by
                  rw [hgrad0, hdir0]
          _ = -‖A.toEuclideanLin f₀ + b‖ ^ 2 := by
                rw [inner_neg_right, real_inner_self_eq_norm_sq]
          _ = -‖(iterates A b f₀ 0).gradient‖ ^ 2 := by rw [hgrad0]
      refine ⟨hself, ?_⟩
      by_cases hdir : (iterates A b f₀ 0).direction = 0
      · -- In the zero-direction branch, the next gradient pairs trivially with `p₀ = 0`.
        rw [hdir]
        simp
      · let σ := iterates A b f₀ 0
        have hden :
            0 < inner ℝ σ.direction (appliedDirection A σ) :=
          iterateDirection_denominator_pos A b f₀ hA hdir
        have hstep :
            stepSize A σ * inner ℝ σ.direction (appliedDirection A σ) = delta σ := by
          -- Multiply the step-size quotient back by its denominator.
          rw [stepSize_eq]
          field_simp [hden.ne']
        -- Expand the next gradient once and then cancel the line-search term.
        calc
          inner ℝ ((iterates A b f₀ 1).gradient) ((iterates A b f₀ 0).direction)
              = inner ℝ σ.gradient σ.direction +
                  stepSize A σ * inner ℝ (appliedDirection A σ) σ.direction := by
                    change
                      inner ℝ (σ.gradient + stepSize A σ • appliedDirection A σ) σ.direction =
                        inner ℝ σ.gradient σ.direction +
                          stepSize A σ * inner ℝ (appliedDirection A σ) σ.direction
                    rw [inner_add_left, real_inner_smul_left]
          _ = -‖σ.gradient‖ ^ 2 +
                stepSize A σ * inner ℝ σ.direction (appliedDirection A σ) := by
                  rw [hself, real_inner_comm]
          _ = -‖σ.gradient‖ ^ 2 + delta σ := by rw [hstep]
          _ = 0 := by simp [delta_eq]
  | succ v ih =>
      rcases ih with ⟨hself_prev, horth_prev⟩
      have hself :
          inner ℝ ((iterates A b f₀ (v + 1)).gradient) ((iterates A b f₀ (v + 1)).direction) =
            -‖(iterates A b f₀ (v + 1)).gradient‖ ^ 2 := by
        let g := (iterates A b f₀ (v + 1)).gradient
        let p := (iterates A b f₀ v).direction
        have hdir_eq :
            (iterates A b f₀ (v + 1)).direction = -g + beta A (iterates A b f₀ v) • p := by
          simp [g, p, iterates_succ, step_direction, nextDirection_eq]
        -- Rewrite the new direction as `-gᵥ₊₁ + βᵥ pᵥ` and use the previous-step orthogonality.
        calc
          inner ℝ ((iterates A b f₀ (v + 1)).gradient) ((iterates A b f₀ (v + 1)).direction)
              = inner ℝ g (-g + beta A (iterates A b f₀ v) • p) := by
                  simpa [g] using congrArg
                    (fun x => inner ℝ ((iterates A b f₀ (v + 1)).gradient) x) hdir_eq
          _ =
              inner ℝ g (-g) +
              inner ℝ g (beta A (iterates A b f₀ v) • p) := by
                  rw [inner_add_right]
          _ = -‖g‖ ^ 2 + beta A (iterates A b f₀ v) * inner ℝ g p := by
                simp [inner_smul_right]
          _ = -‖g‖ ^ 2 := by
                rw [horth_prev, mul_zero, add_zero]
          _ = -‖(iterates A b f₀ (v + 1)).gradient‖ ^ 2 := by simp [g]
      refine ⟨hself, ?_⟩
      by_cases hdir : (iterates A b f₀ (v + 1)).direction = 0
      · -- If the new direction vanishes, the next orthogonality statement is immediate.
        rw [hdir]
        simp
      · let σ := iterates A b f₀ (v + 1)
        have hden :
            0 < inner ℝ σ.direction (appliedDirection A σ) :=
          iterateDirection_denominator_pos A b f₀ hA hdir
        have hstep :
            stepSize A σ * inner ℝ σ.direction (appliedDirection A σ) = delta σ := by
          -- Multiply the current step-size quotient back by its denominator.
          rw [stepSize_eq]
          field_simp [hden.ne']
        -- The one-step update cancels exactly against the current self-inner identity.
        calc
          inner ℝ ((iterates A b f₀ (v + 2)).gradient) ((iterates A b f₀ (v + 1)).direction)
              = inner ℝ σ.gradient σ.direction +
                  stepSize A σ * inner ℝ (appliedDirection A σ) σ.direction := by
                    change
                      inner ℝ (σ.gradient + stepSize A σ • appliedDirection A σ) σ.direction =
                        inner ℝ σ.gradient σ.direction +
                          stepSize A σ * inner ℝ (appliedDirection A σ) σ.direction
                    rw [inner_add_left, real_inner_smul_left]
          _ = -‖σ.gradient‖ ^ 2 +
                stepSize A σ * inner ℝ σ.direction (appliedDirection A σ) := by
                  rw [hself, real_inner_comm]
          _ = -‖σ.gradient‖ ^ 2 + delta σ := by rw [hstep]
          _ = 0 := by simp [delta_eq]

/-- Helper for Theorem 3.7: every stored gradient lies in the finite span of
the search directions revealed up to that iterate. -/
private theorem iterateGradient_mem_directionSpan
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    ∀ v : ℕ, (iterates A b f₀ v).gradient ∈ directionSpan A b f₀ (v + 1) := by
  intro v
  induction v with
  | zero =>
      -- The initial gradient is the negative of the first search direction.
      simpa [iterates_zero, init_gradient, init_direction] using
        Submodule.neg_mem (directionSpan A b f₀ 1) (iterateDirection_mem_directionSpan A b f₀ 0)
  | succ v ih =>
      have hdir_prev :
          (iterates A b f₀ v).direction ∈ directionSpan A b f₀ (v + 2) :=
        directionSpan_mono A b f₀ (Nat.le_succ (v + 1))
          (iterateDirection_mem_directionSpan A b f₀ v)
      have hdir_curr :
          (iterates A b f₀ (v + 1)).direction ∈ directionSpan A b f₀ (v + 2) :=
        iterateDirection_mem_directionSpan A b f₀ (v + 1)
      have hgrad_eq :
          (iterates A b f₀ (v + 1)).gradient =
            -((iterates A b f₀ (v + 1)).direction) +
              beta A (iterates A b f₀ v) • (iterates A b f₀ v).direction := by
        -- Unfold only the current direction field and rearrange the resulting affine identity.
        rw [iterates_succ, step_gradient, step_direction, nextDirection_eq]
        abel
      rw [hgrad_eq]
      exact Submodule.add_mem (directionSpan A b f₀ (v + 2))
        (Submodule.neg_mem _ hdir_curr)
        (Submodule.smul_mem _ _ hdir_prev)

/-- Helper for Theorem 3.7: applying `A` to the current search direction lands
in the next finite span of search directions. -/
private theorem iterateAppliedDirection_mem_directionSpanSucc
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ v : ℕ,
      A.toEuclideanLin ((iterates A b f₀ v).direction) ∈ directionSpan A b f₀ (v + 2) := by
  intro v
  by_cases hdir : (iterates A b f₀ v).direction = 0
  · -- The zero-direction branch is immediate.
    simp [hdir]
  · have hgrad_ne : (iterates A b f₀ v).gradient ≠ 0 := by
      intro hgrad
      exact hdir (iterateDirection_eq_zero_of_gradient_eq_zero A b f₀ v hgrad)
    have hstep_ne : stepSize A (iterates A b f₀ v) ≠ 0 := by
      have hnum_ne : delta (iterates A b f₀ v) ≠ 0 := by
        simp [delta_eq, hgrad_ne]
      exact div_ne_zero hnum_ne (iterateDirection_denominator_pos A b f₀ hA hdir).ne'
    have hgrad_curr :
        (iterates A b f₀ v).gradient ∈ directionSpan A b f₀ (v + 2) :=
      directionSpan_mono A b f₀ (Nat.le_succ (v + 1))
        (iterateGradient_mem_directionSpan A b f₀ v)
    have hgrad_next :
        (iterates A b f₀ (v + 1)).gradient ∈ directionSpan A b f₀ (v + 2) :=
      iterateGradient_mem_directionSpan A b f₀ (v + 1)
    have hdiff :
        (iterates A b f₀ (v + 1)).gradient - (iterates A b f₀ v).gradient ∈
          directionSpan A b f₀ (v + 2) :=
      Submodule.sub_mem _ hgrad_next hgrad_curr
    have hstep :
        stepSize A (iterates A b f₀ v) • A.toEuclideanLin ((iterates A b f₀ v).direction) =
          (iterates A b f₀ (v + 1)).gradient - (iterates A b f₀ v).gradient := by
      -- Rearrange the one-step gradient update into a pure difference identity.
      calc
        stepSize A (iterates A b f₀ v) • A.toEuclideanLin ((iterates A b f₀ v).direction)
            = nextGradient A (iterates A b f₀ v) - (iterates A b f₀ v).gradient := by
                simp [nextGradient_eq, appliedDirection_eq, sub_eq_add_neg, add_left_comm, add_comm]
        _ = (iterates A b f₀ (v + 1)).gradient - (iterates A b f₀ v).gradient := by
              simp [iterates_succ]
    have happly_eq :
        A.toEuclideanLin ((iterates A b f₀ v).direction) =
          (stepSize A (iterates A b f₀ v))⁻¹ •
            ((iterates A b f₀ (v + 1)).gradient - (iterates A b f₀ v).gradient) := by
      rw [← hstep, inv_smul_smul₀ hstep_ne]
    -- Scale the already-controlled gradient difference by the inverse step size.
    rw [happly_eq]
    exact Submodule.smul_mem _ _ hdiff

/-- Helper for Theorem 3.7: applying `A` to a vector from the finite search
direction span raises the span index by one. -/
private theorem toEuclideanLin_mem_directionSpanSucc
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ {v : ℕ} {h : EuclideanSpace ℝ n},
      h ∈ directionSpan A b f₀ v →
        A.toEuclideanLin h ∈ directionSpan A b f₀ (v + 1) := by
  intro v h hh
  have hle :
      directionSpan A b f₀ v ≤ (directionSpan A b f₀ (v + 1)).comap (A.toEuclideanLin) := by
    -- It suffices to check the span generators, because `comap` is a submodule.
    rw [directionSpan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    change A.toEuclideanLin ((iterates A b f₀ j.1).direction) ∈ directionSpan A b f₀ (v + 1)
    have happly :
        A.toEuclideanLin ((iterates A b f₀ j.1).direction) ∈ directionSpan A b f₀ (j.1 + 2) :=
      iterateAppliedDirection_mem_directionSpanSucc A b f₀ hA j.1
    -- Transport the generator-specific image into the larger target span.
    exact directionSpan_mono A b f₀ (Nat.succ_le_succ (Nat.succ_le_of_lt j.2)) happly
  exact hle hh

/-- Helper for Theorem 3.7: the `v`th Krylov slice generated by the initial
gradient is contained in the finite span of the first `v` CG directions. -/
private theorem krylovSubspace_le_directionSpan
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ v : ℕ,
      Krylov.subspace A (A.toEuclideanLin f₀ + b) v ≤ directionSpan A b f₀ v := by
  intro v
  intro y hy
  rw [Krylov.subspace_eq_submodule] at hy
  rcases (Krylov.mem_submodule_iff A.toEuclideanLin (A.toEuclideanLin f₀ + b) y v).1 hy with
    ⟨p, hpdeg, rfl⟩
  have hgenerator :
      ∀ k : ℕ,
        (A.toEuclideanLin ^ k) (A.toEuclideanLin f₀ + b) ∈ directionSpan A b f₀ (k + 1) := by
    intro k
    induction k with
    | zero =>
        -- The first Krylov generator is the negative initial direction.
        simpa [iterates_zero, init_gradient, init_direction] using
          Submodule.neg_mem (directionSpan A b f₀ 1) (iterateDirection_mem_directionSpan A b f₀ 0)
    | succ k hk =>
        -- One more application of `A` raises the direction span index by one.
        have hpow_eq :
            (A.toEuclideanLin ^ (k + 1)) (A.toEuclideanLin f₀ + b) =
              A.toEuclideanLin ((A.toEuclideanLin ^ k) (A.toEuclideanLin f₀ + b)) := by
          simpa [pow_succ', Module.End.mul_apply]
        rw [hpow_eq]
        exact toEuclideanLin_mem_directionSpanSucc A b f₀ hA hk
  have hgenerator_le :
      ∀ {k : ℕ}, k < v →
        (A.toEuclideanLin ^ k) (A.toEuclideanLin f₀ + b) ∈ directionSpan A b f₀ v := by
    intro k hk
    exact directionSpan_mono A b f₀ (Nat.succ_le_of_lt hk) (hgenerator k)
  -- Expand the polynomial witness into finitely many Krylov generators and place each one in the span.
  rw [Polynomial.aeval_def, ← Polynomial.sum_monomial_eq p, Polynomial.eval₂_sum,
    Polynomial.sum_def]
  simpa [Polynomial.eval₂_monomial, Module.End.mul_apply] using
    (Submodule.sum_mem (directionSpan A b f₀ v) fun n hn => by
      have hnv : n < v := WithBot.coe_lt_coe.mp <|
        lt_of_le_of_lt (Polynomial.le_degree_of_mem_supp n hn) hpdeg
      have hpow :
          (A.toEuclideanLin ^ n) (A.toEuclideanLin f₀ + b) ∈ directionSpan A b f₀ v :=
        hgenerator_le hnv
      simpa [LinearMap.map_add, smul_add] using
        (Submodule.smul_mem (directionSpan A b f₀ v) (p.coeff n) hpow))

/-- Helper for Theorem 3.7: each CG iterate simultaneously has gradient
orthogonal to the revealed search-direction span and current direction
`A`-conjugate to that same span. -/
private theorem iterateGradientDirectionSpanOrthogonalityBundle
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ v : ℕ,
      (∀ {h : EuclideanSpace ℝ n},
          h ∈ directionSpan A b f₀ v →
            inner ℝ ((iterates A b f₀ v).gradient) h = 0) ∧
        ∀ {h : EuclideanSpace ℝ n},
          h ∈ directionSpan A b f₀ v →
            inner ℝ ((iterates A b f₀ v).direction) (A.toEuclideanLin h) = 0 := by
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  intro v
  induction v with
  | zero =>
      constructor
      · intro h hh
        -- The zeroth direction span is trivial, so every inner product vanishes there.
        have hh0 : h = 0 := by
          simpa [directionSpan] using hh
        simp [hh0]
      · intro h hh
        -- The same trivial-span argument handles the conjugacy component.
        have hh0 : h = 0 := by
          simpa [directionSpan] using hh
        simp [hh0]
  | succ v ih =>
      rcases ih with ⟨hgrad_prev, hdir_prev⟩
      let σ := iterates A b f₀ v
      let gNext := (iterates A b f₀ (v + 1)).gradient
      let pCurr := σ.direction
      let pNext := (iterates A b f₀ (v + 1)).direction
      have hgrad_curr :
          ∀ {h : EuclideanSpace ℝ n},
            h ∈ directionSpan A b f₀ (v + 1) →
              inner ℝ gNext h = 0 := by
        intro h hh
        -- Induct over the finite span generators and split off the newest direction.
        rw [directionSpan] at hh
        refine Submodule.span_induction (fun x hx ↦ ?_) (by simp)
          (fun x y _ _ hx hy ↦ by rw [inner_add_right, hx, hy, add_zero])
          (fun a x _ hx ↦ by rw [inner_smul_right, hx, mul_zero]) hh
        rcases hx with ⟨j, rfl⟩
        obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
        · have hi_mem_small :
              (iterates A b f₀ i).direction ∈ directionSpan A b f₀ (i.1 + 1) :=
            iterateDirection_mem_directionSpan A b f₀ i.1
          have hi_mem :
              (iterates A b f₀ i).direction ∈ directionSpan A b f₀ v :=
            directionSpan_mono A b f₀ (Nat.succ_le_of_lt i.2) hi_mem_small
          have hAi_mem :
              A.toEuclideanLin ((iterates A b f₀ i).direction) ∈
                directionSpan A b f₀ (v + 1) :=
            toEuclideanLin_mem_directionSpanSucc A b f₀ hA hi_mem
          -- Expand the gradient update; old directions are killed by the induction hypotheses.
          calc
            inner ℝ gNext ((iterates A b f₀ i).direction)
                = inner ℝ σ.gradient ((iterates A b f₀ i).direction) +
                    stepSize A σ *
                      inner ℝ (appliedDirection A σ) ((iterates A b f₀ i).direction) := by
                    change
                      inner ℝ (σ.gradient + stepSize A σ • appliedDirection A σ)
                        ((iterates A b f₀ i).direction) =
                          inner ℝ σ.gradient ((iterates A b f₀ i).direction) +
                            stepSize A σ *
                              inner ℝ (appliedDirection A σ)
                                ((iterates A b f₀ i).direction)
                    rw [inner_add_left, real_inner_smul_left]
            _ = 0 +
                  stepSize A σ *
                    inner ℝ σ.direction
                      (A.toEuclideanLin ((iterates A b f₀ i).direction)) := by
                  rw [hgrad_prev hi_mem]
                  rw [show inner ℝ (appliedDirection A σ) ((iterates A b f₀ i).direction) =
                      inner ℝ σ.direction (A.toEuclideanLin ((iterates A b f₀ i).direction)) by
                        simpa [σ, appliedDirection_eq] using
                          hsymm σ.direction ((iterates A b f₀ i).direction)]
            _ = 0 := by
                  rw [hdir_prev hi_mem]
                  simp
        · -- The newest generator is exactly the one-step orthogonality relation.
          simpa [gNext, pCurr, σ] using
            (iterateGradientDirectionOrthogonalityBundle A b f₀ hA v).2
      have hnextDirection_conjugate_current :
          inner ℝ pNext (A.toEuclideanLin pCurr) = 0 := by
        by_cases hdir : pCurr = 0
        · -- If the current direction vanishes, the claimed conjugacy is immediate.
          simp [pCurr, pNext, hdir]
        · have hden :
              0 < inner ℝ pCurr (A.toEuclideanLin pCurr) := by
            simpa [σ, pCurr, appliedDirection_eq] using
              iterateDirection_denominator_pos A b f₀ hA hdir
          have hgrad_ne : σ.gradient ≠ 0 := by
            intro hzero
            exact hdir (iterateDirection_eq_zero_of_gradient_eq_zero A b f₀ v hzero)
          have hstep_ne : stepSize A σ ≠ 0 := by
            have hnum_ne : delta σ ≠ 0 := by
              simp [delta_eq, hgrad_ne]
            exact div_ne_zero hnum_ne hden.ne'
          have hgrad_prev_mem :
              σ.gradient ∈ directionSpan A b f₀ (v + 1) :=
            iterateGradient_mem_directionSpan A b f₀ v
          have horth_prev_grad : inner ℝ gNext σ.gradient = 0 :=
            hgrad_curr hgrad_prev_mem
          have hgrad_prev_eq :
              σ.gradient =
                gNext - stepSize A σ • A.toEuclideanLin pCurr := by
            -- Rearrange the one-step gradient recurrence into the previous gradient.
            rw [show gNext = nextGradient A σ by simp [gNext, σ, iterates_succ]]
            simp [nextGradient_eq, appliedDirection_eq, pCurr, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm]
          have hgrad_mul :
              stepSize A σ * inner ℝ gNext (A.toEuclideanLin pCurr) = ‖gNext‖ ^ 2 := by
            -- Orthogonality of `gᵥ₊₁` to `gᵥ` identifies the critical mixed term.
            have hrelation :
                ‖gNext‖ ^ 2 -
                    stepSize A σ * inner ℝ gNext (A.toEuclideanLin pCurr) = 0 := by
              calc
                ‖gNext‖ ^ 2 -
                    stepSize A σ * inner ℝ gNext (A.toEuclideanLin pCurr)
                    = inner ℝ gNext gNext -
                        stepSize A σ * inner ℝ gNext (A.toEuclideanLin pCurr) := by
                          rw [real_inner_self_eq_norm_sq]
                _ = inner ℝ gNext
                      (gNext - stepSize A σ • A.toEuclideanLin pCurr) := by
                        rw [inner_sub_right, inner_smul_right]
                _ = inner ℝ gNext σ.gradient := by rw [hgrad_prev_eq]
                _ = 0 := horth_prev_grad
            nlinarith
          have hstep_mul :
              stepSize A σ * inner ℝ pCurr (A.toEuclideanLin pCurr) = delta σ := by
            -- Multiply the step-size quotient back by its positive denominator.
            calc
              stepSize A σ * inner ℝ pCurr (A.toEuclideanLin pCurr)
                  = (delta σ / inner ℝ pCurr (A.toEuclideanLin pCurr)) *
                      inner ℝ pCurr (A.toEuclideanLin pCurr) := by
                        simp [stepSize_eq, pCurr, appliedDirection_eq]
              _ = delta σ := by
                    field_simp [hden.ne']
          have hbeta_mul :
              beta A σ * delta σ = ‖gNext‖ ^ 2 := by
            -- The Fletcher-Reeves coefficient exactly records the new squared gradient norm.
            calc
              beta A σ * delta σ
                  = (‖gNext‖ ^ 2 / delta σ) * delta σ := by
                        simp [beta_eq, gNext, σ, iterates_succ]
              _ = ‖gNext‖ ^ 2 := by
                    field_simp [delta_eq, hgrad_ne]
          have hmul :
              stepSize A σ * inner ℝ pNext (A.toEuclideanLin pCurr) = 0 := by
            -- Multiply the target conjugacy equation by the nonzero step size and simplify.
            calc
              stepSize A σ * inner ℝ pNext (A.toEuclideanLin pCurr)
                  = stepSize A σ *
                      (-inner ℝ gNext (A.toEuclideanLin pCurr) +
                        beta A σ * inner ℝ pCurr (A.toEuclideanLin pCurr)) := by
                          congr 1
                          calc
                            inner ℝ pNext (A.toEuclideanLin pCurr)
                                = inner ℝ (-gNext + beta A σ • pCurr)
                                    (A.toEuclideanLin pCurr) := by
                                      simp [pNext, gNext, pCurr, σ, iterates_succ,
                                        step_direction, nextDirection_eq]
                            _ = -inner ℝ gNext (A.toEuclideanLin pCurr) +
                                  beta A σ * inner ℝ pCurr (A.toEuclideanLin pCurr) := by
                                    rw [inner_add_left, inner_neg_left, real_inner_smul_left]
              _ = -(stepSize A σ * inner ℝ gNext (A.toEuclideanLin pCurr)) +
                    beta A σ *
                      (stepSize A σ * inner ℝ pCurr (A.toEuclideanLin pCurr)) := by
                    ring
              _ = -‖gNext‖ ^ 2 + beta A σ * delta σ := by
                    rw [hgrad_mul, hstep_mul]
              _ = 0 := by
                    rw [hbeta_mul]
                    ring
          exact (mul_eq_zero.mp hmul).resolve_left hstep_ne
      have hdir_curr :
          ∀ {h : EuclideanSpace ℝ n},
            h ∈ directionSpan A b f₀ (v + 1) →
              inner ℝ pNext (A.toEuclideanLin h) = 0 := by
        intro h hh
        -- Repeat the span induction, now using the already-established gradient orthogonality.
        rw [directionSpan] at hh
        refine Submodule.span_induction (fun x hx ↦ ?_) (by simp)
          (fun x y _ _ hx hy ↦ by rw [LinearMap.map_add, inner_add_right, hx, hy, add_zero])
          (fun a x _ hx ↦ by rw [LinearMap.map_smul, inner_smul_right, hx, mul_zero]) hh
        rcases hx with ⟨j, rfl⟩
        obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
        · have hi_mem_small :
              (iterates A b f₀ i).direction ∈ directionSpan A b f₀ (i.1 + 1) :=
            iterateDirection_mem_directionSpan A b f₀ i.1
          have hi_mem :
              (iterates A b f₀ i).direction ∈ directionSpan A b f₀ v :=
            directionSpan_mono A b f₀ (Nat.succ_le_of_lt i.2) hi_mem_small
          have hAi_mem :
              A.toEuclideanLin ((iterates A b f₀ i).direction) ∈
                directionSpan A b f₀ (v + 1) :=
            toEuclideanLin_mem_directionSpanSucc A b f₀ hA hi_mem
          -- Expand the direction update; both resulting terms vanish on old generators.
          calc
            inner ℝ pNext (A.toEuclideanLin ((iterates A b f₀ i).direction))
                = -inner ℝ gNext (A.toEuclideanLin ((iterates A b f₀ i).direction)) +
                    beta A σ *
                      inner ℝ pCurr (A.toEuclideanLin ((iterates A b f₀ i).direction)) := by
                    calc
                      inner ℝ pNext (A.toEuclideanLin ((iterates A b f₀ i).direction))
                          = inner ℝ (-gNext + beta A σ • pCurr)
                              (A.toEuclideanLin ((iterates A b f₀ i).direction)) := by
                                simp [pNext, gNext, pCurr, σ, iterates_succ,
                                  step_direction, nextDirection_eq]
                      _ = -inner ℝ gNext (A.toEuclideanLin ((iterates A b f₀ i).direction)) +
                            beta A σ *
                              inner ℝ pCurr
                                (A.toEuclideanLin ((iterates A b f₀ i).direction)) := by
                                  rw [inner_add_left, inner_neg_left, real_inner_smul_left]
            _ = 0 := by
                  rw [hgrad_curr hAi_mem, hdir_prev hi_mem]
                  simp
        · -- The newest generator is handled by the scalar cancellation above.
          simpa [pCurr, pNext, σ, appliedDirection_eq] using hnextDirection_conjugate_current
      exact ⟨hgrad_curr, hdir_curr⟩

/-- Helper for Theorem 3.7: the current stored gradient is orthogonal to the
finite span of all earlier search directions. -/
private theorem iterateGradient_orthogonal_directionSpan
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ {v : ℕ} {h : EuclideanSpace ℝ n},
      h ∈ directionSpan A b f₀ v →
        inner ℝ ((iterates A b f₀ v).gradient) h = 0 := by
  intro v h hh
  -- Project the bundled orthogonality/conjugacy invariant to its gradient component.
  exact (iterateGradientDirectionSpanOrthogonalityBundle A b f₀ hA v).1 hh

/-- Helper for Theorem 3.7: the stored gradient at iterate `v` is orthogonal to
the `v`th Krylov slice generated by the initial gradient. -/
theorem iterateGradient_orthogonal_krylovSubspace
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) :
    ∀ {v : ℕ} {h : EuclideanSpace ℝ n},
      h ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) v →
        inner ℝ ((iterates A b f₀ v).gradient) h = 0 := by
  intro v h hh
  -- Route correction: first move from Krylov membership to the finite direction span, then use
  -- the bundled direction-span orthogonality established above.
  exact iterateGradient_orthogonal_directionSpan A b f₀ hA
    (krylovSubspace_le_directionSpan A b f₀ hA v hh)

/-- Helper for Theorem 3.7: the quadratic objective gap is half the squared
`A`-energy error from the exact minimizer. -/
theorem quadraticGap_eq_half_energyNormErrorSq
    (c : ℝ) (b : EuclideanSpace ℝ n) (A : Matrix n n ℝ) (hA : A.PosDef)
    (f : EuclideanSpace ℝ n) :
    quadraticFunctional c b A f =
      quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
        (1 / 2 : ℝ) * (QuadraticOptimization.energyNormError A b hA f) ^ 2 := by
  have hf :
      f = quadraticFunctionalMinimizer b A + QuadraticOptimization.error A b f := by
    -- Expand the error and regroup the resulting difference.
    rw [QuadraticOptimization.error_eq_sub]
    abel
  have hinner_nonneg :
      0 ≤
        inner ℝ
          (A.toEuclideanLin (QuadraticOptimization.error A b f))
          (QuadraticOptimization.error A b f) :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef _
  have hsq :
      (QuadraticOptimization.energyNormError A b hA f) ^ 2 =
        inner ℝ
          (A.toEuclideanLin (QuadraticOptimization.error A b f))
          (QuadraticOptimization.error A b f) := by
    -- Rewrite the squared energy norm as the quadratic form induced by `A`.
    rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner,
      Matrix.energyInner_eq, Real.sq_sqrt hinner_nonneg]
  -- Translate the quadratic functional from the minimizer by the current error vector.
  calc
    quadraticFunctional c b A f =
        quadraticFunctional c b A
          (quadraticFunctionalMinimizer b A + QuadraticOptimization.error A b f) := by
          simpa using congrArg (quadraticFunctional c b A) hf
    _ =
        quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
          (1 / 2 : ℝ) *
            inner ℝ
              (A.toEuclideanLin (QuadraticOptimization.error A b f))
              (QuadraticOptimization.error A b f) := by
          simpa using
            QuadraticOptimization.quadraticFunctional_translate_eq_base_add_half_inner
              c b A (by simpa using hA.isHermitian)
              (f0 := quadraticFunctionalMinimizer b A)
              (h := QuadraticOptimization.error A b f)
              (QuadraticOptimization.quadraticFunctionalMinimizer_isCriticalPoint b A hA)
    _ =
        quadraticFunctional c b A (quadraticFunctionalMinimizer b A) +
          (1 / 2 : ℝ) * (QuadraticOptimization.energyNormError A b hA f) ^ 2 := by
          rw [hsq]

/-- Theorem 3.7 (1). The `v`th conjugate-gradient iterate belongs to
`affineKrylovSubspace A b f₀ v` and minimizes the `A`-energy distance to the
exact solution `quadraticFunctionalMinimizer b A = -(A⁻¹).toEuclideanLin b`
there. -/
theorem solution_isAffineKrylovMinimizer
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    (iterates A b f₀ v).solution ∈ affineKrylovSubspace A b f₀ v ∧
      IsMinOn
        (QuadraticOptimization.energyNormError A b hA)
        (affineKrylovSubspace A b f₀ v)
        (iterates A b f₀ v).solution := by
  constructor
  · -- The iterate admissibility is already handled by the split recurrence helper.
    exact iterateSolution_mem_affineKrylov A b f₀ v
  · -- Reduce minimality to the quadratic objective gap on the affine Krylov slice.
    rw [isMinOn_iff]
    intro f hf
    let solution := (iterates A b f₀ v).solution
    have hsolution_mem :
        solution ∈ affineKrylovSubspace A b f₀ v :=
      iterateSolution_mem_affineKrylov A b f₀ v
    have hf_affine : f ∈ affineKrylovSubspace A b f₀ v := hf
    have hf_krylov :
        f - f₀ ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) v := by
      rw [mem_affineKrylovSubspace_iff] at hf_affine
      simpa [vsub_eq_sub] using hf_affine
    have hsolution_krylov :
        solution - f₀ ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) v := by
      rw [mem_affineKrylovSubspace_iff] at hsolution_mem
      simpa [vsub_eq_sub] using hsolution_mem
    have hdisplacement :
        f - solution ∈ Krylov.subspace A (A.toEuclideanLin f₀ + b) v := by
      have hsub :
          (f - f₀) - (solution - f₀) ∈
            Krylov.subspace A (A.toEuclideanLin f₀ + b) v :=
        Submodule.sub_mem _ hf_krylov hsolution_krylov
      have hrewrite : (f - f₀) - (solution - f₀) = f - solution := by
        abel
      exact hrewrite ▸ hsub
    have hlinear_zero :
        inner ℝ (b + A.toEuclideanLin solution) (f - solution) = 0 := by
      -- Convert the orthogonality statement from the stored gradient to the quadratic gradient.
      simpa [solution, iterateGradient_eq_quadraticGradient A b f₀ v, add_assoc, add_left_comm,
        add_comm] using
        iterateGradient_orthogonal_krylovSubspace A b f₀ hA
          (v := v) (h := f - solution) hdisplacement
    have hremainder_nonneg :
        0 ≤ (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin (f - solution)) (f - solution) := by
      have hinner_nonneg :
          0 ≤ inner ℝ (A.toEuclideanLin (f - solution)) (f - solution) :=
        Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hA.posSemidef (f - solution)
      nlinarith
    have hquadratic_le :
        quadraticFunctional 0 b A solution ≤ quadraticFunctional 0 b A f := by
      have hrewrite :
          solution + (f - solution) = f := by
        simp [solution]
      have hincrement :
          quadraticFunctional 0 b A f =
            quadraticFunctional 0 b A solution +
              inner ℝ (b + A.toEuclideanLin solution) (f - solution) +
              (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin (f - solution)) (f - solution) := by
        calc
          quadraticFunctional 0 b A f
              = quadraticFunctional 0 b A (solution + (f - solution)) := by
                  rw [hrewrite]
          _ = quadraticFunctional 0 b A solution +
                inner ℝ (b + A.toEuclideanLin solution) (f - solution) +
                (1 / 2 : ℝ) * inner ℝ (A.toEuclideanLin (f - solution)) (f - solution) := by
                simpa using
                  QuadraticOptimization.quadraticFunctional_increment_eq_base_add_linear_add_half_inner
                    0 b A (f0 := solution) (h := f - solution) (by simpa using hA.isHermitian)
      rw [hincrement, hlinear_zero]
      nlinarith
    have hgap_solution := quadraticGap_eq_half_energyNormErrorSq 0 b A hA solution
    have hgap_f := quadraticGap_eq_half_energyNormErrorSq 0 b A hA f
    have hsolution_nonneg : 0 ≤ QuadraticOptimization.energyNormError A b hA solution := by
      rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner]
      exact Real.sqrt_nonneg _
    have hf_nonneg : 0 ≤ QuadraticOptimization.energyNormError A b hA f := by
      rw [QuadraticOptimization.energyNormError_eq, Matrix.energyNorm_eq_sqrt_energyInner]
      exact Real.sqrt_nonneg _
    -- Compare the quadratic gaps and convert the resulting squared inequality to the norm inequality.
    nlinarith [hquadratic_le, hgap_solution, hgap_f, hsolution_nonneg, hf_nonneg]

/-- The admissibility clause of Theorem 3.7 (1). -/
theorem solution_mem_affineKrylovSubspace
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    (iterates A b f₀ v).solution ∈ affineKrylovSubspace A b f₀ v :=
  iterateSolution_mem_affineKrylov A b f₀ v

/-- The minimality clause of Theorem 3.7 (1). -/
theorem solution_isMinOn_affineKrylov
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    IsMinOn
      (QuadraticOptimization.energyNormError A b hA)
      (affineKrylovSubspace A b f₀ v)
      (iterates A b f₀ v).solution :=
  (solution_isAffineKrylovMinimizer A b f₀ hA v).2

/-- Theorem 3.7 (2). The `v`th conjugate-gradient error is the image of the
initial error under a polynomial in `A` of degree at most `v` normalized by
`q(0) = 1`. -/
theorem error_eq_aeval_initialError
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    ∃ q : Polynomial ℝ,
      q.eval 0 = 1 ∧
      q.degree ≤ v ∧
      error A b f₀ v = (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) := by
  -- Apply the affine-to-polynomial bridge to the verified affine-Krylov membership of the iterate.
  simpa [ConjugateGradient.error] using
    error_eq_aeval_initialError_of_mem_affineKrylovSubspace A b f₀ hA v
      (solution_mem_affineKrylovSubspace A b f₀ hA v)

/-- Theorem 3.7 (3). Among all degree-`≤ v` polynomials with `q(0) = 1`, the
`A`-energy norm of the conjugate-gradient error is minimal. -/
theorem energyNorm_error_le_aeval_initialError
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ)
    (q : Polynomial ℝ) (hq0 : q.eval 0 = 1) (hqdeg : q.degree ≤ v) :
    energyNormError A b f₀ hA v ≤
      ‖(Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀)‖_[A, hA] :=
    by
      -- Compare the CG iterate against the affine-Krylov competitor induced by the normalized polynomial.
      have hcandidate_mem :
          quadraticFunctionalMinimizer b A +
              (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀) ∈
            affineKrylovSubspace A b f₀ v :=
        normalizedPolynomialCandidate_mem_affineKrylovSubspace A b f₀ hA v q hq0 hqdeg
      have hmin := solution_isMinOn_affineKrylov A b f₀ hA v
      rw [isMinOn_iff] at hmin
      have hmin_compare :=
        hmin
          (quadraticFunctionalMinimizer b A +
            (Polynomial.aeval A.toEuclideanLin q) (initialError A b f₀))
          hcandidate_mem
      -- Rewrite the objective value at the polynomial competitor as the `A`-energy norm of its error vector.
      rw [ConjugateGradient.energyNormError_eq, ConjugateGradient.error,
        QuadraticOptimization.error_eq_sub]
      simpa [QuadraticOptimization.energyNormError_eq, QuadraticOptimization.error_eq_sub,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmin_compare

end ConjugateGradient
