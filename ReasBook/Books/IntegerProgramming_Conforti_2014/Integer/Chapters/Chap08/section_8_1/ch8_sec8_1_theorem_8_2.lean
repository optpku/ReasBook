/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Matrix.ToLin
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_theorem_1_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_remark_3_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_easy_block_feasible_set
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntegerVectorNotation Matrix

section Theorem82

variable {m₁ n : ℕ}

/-- Helper for Theorem 8.2: the integral-data easy block
`{x ∈ ℝ^n_+ | A₂ x ≤ b²}` attached to integer data `A₂` and `b₂`. -/
def integral_easy_block_feasible_set
    {m₂ : ℕ}
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ) : Set (Fin n → ℝ) :=
  easy_block_feasible_set (A₂.map (Int.castRingHom ℝ)) (fun i ↦ (b₂ i : ℝ))

/-- `HasEasyBlockIntegerOrigin Q` means that `Q` is exactly the set of pure-integer points of
some Section 8.1 easy block with integral data. This restores the rational/integral source
meaning of `Q` used in Theorem 8.2. -/
def HasEasyBlockIntegerOrigin
    (Q : Set (Fin n → ℝ)) : Prop :=
  ∃ m₂ : ℕ, ∃ A₂ : Matrix (Fin m₂) (Fin n) ℤ, ∃ b₂ : Fin m₂ → ℤ,
    Q = pure_integer_points (integral_easy_block_feasible_set A₂ b₂)

/-- The convex-hull feasible region `{x : A₁ x ≤ b₁, x ∈ conv(Q)}` appearing in Theorem 8.2. -/
abbrev convex_hull_feasible_set
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (Q : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  lagrangian_integer_feasible_set A₁ b₁ (convexHull ℝ Q)

/-- Membership in `convex_hull_feasible_set A₁ b₁ Q` means belonging to `conv(Q)` and satisfying
the complicating inequalities `A₁ x ≤ b₁`. -/
theorem mem_convex_hull_feasible_set_iff
    {A₁ : Matrix (Fin m₁) (Fin n) ℝ}
    {b₁ : Fin m₁ → ℝ}
    {Q : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} :
    x ∈ convex_hull_feasible_set A₁ b₁ Q ↔
      x ∈ convexHull ℝ Q ∧ A₁ *ᵥ x ≤ b₁ := by
  rw [convex_hull_feasible_set, mem_lagrangian_integer_feasible_set_iff]

/-- The Lagrangian dual value `z_LD = min_{lambda ≥ 0} z_LR(lambda)` over the original base set
`Q`, recorded in `EReal` so the Chapter 8 value conventions allow both infeasibility and
unbounded-above relaxations. -/
noncomputable def lagrangian_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) : EReal :=
  sInf
    ((fun lam : Fin m₁ → ℝ ↦
        lagrangian_relaxation_value A₁ b₁ c Q lam) ''
      Set.Ici (0 : Fin m₁ → ℝ))

/-- `lagrangian_dual_value A₁ b₁ c Q` unfolds to the infimum of the Lagrangian-relaxation values
over the original set `Q` and the nonnegative orthant. -/
theorem lagrangian_dual_value_eq_sInf
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    lagrangian_dual_value A₁ b₁ c Q =
      sInf
        ((fun lam : Fin m₁ → ℝ ↦
            lagrangian_relaxation_value A₁ b₁ c Q lam) ''
          Set.Ici (0 : Fin m₁ → ℝ)) :=
  rfl

/-- Helper for Theorem 8.2: every point of `convexHull ℝ Q` has penalized objective value at
most the Lagrangian relaxation value computed over the original set `Q`. -/
theorem lagrangian_objective_le_lagrangian_relaxation_value_of_mem_convex_hull
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ Q) :
    ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) ≤
      lagrangian_relaxation_value A₁ b₁ c Q lam := by
  let α : Fin n → ℝ := c - lam ᵥ* A₁
  let linearObjective : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ α
  have hlinearObjectiveConvex : ConvexOn ℝ Set.univ linearObjective := by
    simpa [linearObjective] using
      (LinearMap.convexOn linearObjective (s := Set.univ) convex_univ)
  have hpenalizedConvex :
      ConvexOn ℝ Set.univ (fun y : Fin n → ℝ ↦ linearObjective y + lam ⬝ᵥ b₁) := by
    simpa using hlinearObjectiveConvex.add_const (lam ⬝ᵥ b₁)
  -- A convex objective on `conv(Q)` is bounded above by one of its values on `Q`.
  obtain ⟨y, hyQ, hxy⟩ :=
    ConvexOn.exists_ge_of_mem_convexHull hpenalizedConvex
      (show Q ⊆ Set.univ by intro z hz; trivial)
      hx
  have hx_penalized :
      linearObjective x + lam ⬝ᵥ b₁ =
        c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := by
    calc
      linearObjective x + lam ⬝ᵥ b₁ =
          (c - lam ᵥ* A₁) ⬝ᵥ x + lam ⬝ᵥ b₁ := by
            rfl
      _ = (c ⬝ᵥ x - (lam ᵥ* A₁) ⬝ᵥ x) + lam ⬝ᵥ b₁ := by
            rw [sub_dotProduct]
      _ = c ⬝ᵥ x + (lam ⬝ᵥ b₁ - lam ⬝ᵥ (A₁ *ᵥ x)) := by
            rw [Matrix.dotProduct_mulVec]
            ring
      _ = c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := by
            rw [dotProduct_sub]
  have hy_penalized :
      linearObjective y + lam ⬝ᵥ b₁ =
        c ⬝ᵥ y + lam ⬝ᵥ (b₁ - A₁ *ᵥ y) := by
    calc
      linearObjective y + lam ⬝ᵥ b₁ =
          (c - lam ᵥ* A₁) ⬝ᵥ y + lam ⬝ᵥ b₁ := by
            rfl
      _ = (c ⬝ᵥ y - (lam ᵥ* A₁) ⬝ᵥ y) + lam ⬝ᵥ b₁ := by
            rw [sub_dotProduct]
      _ = c ⬝ᵥ y + (lam ⬝ᵥ b₁ - lam ⬝ᵥ (A₁ *ᵥ y)) := by
            rw [Matrix.dotProduct_mulVec]
            ring
      _ = c ⬝ᵥ y + lam ⬝ᵥ (b₁ - A₁ *ᵥ y) := by
            rw [dotProduct_sub]
  have hy_relax :
      ((linearObjective y + lam ⬝ᵥ b₁ : ℝ) : EReal) ≤
        lagrangian_relaxation_value A₁ b₁ c Q lam := by
    -- Reinsert the witness `y ∈ Q` into the defining supremum for `z_LR(λ)`.
    rw [hy_penalized]
    exact lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c Q lam hyQ
  -- Cast the convexity comparison to `EReal`, then rewrite back to the penalized objective.
  have hx_relax :
      ((linearObjective x + lam ⬝ᵥ b₁ : ℝ) : EReal) ≤
        lagrangian_relaxation_value A₁ b₁ c Q lam := by
    exact
      (show ((linearObjective x + lam ⬝ᵥ b₁ : ℝ) : EReal) ≤
          ((linearObjective y + lam ⬝ᵥ b₁ : ℝ) : EReal) by
        exact_mod_cast hxy).trans hy_relax
  simpa [hx_penalized] using hx_relax

/-- Helper for Theorem 8.2: the convexified feasible optimum is always bounded above by the
Lagrangian dual value over the original base set `Q`. -/
theorem integer_program_value_on_convex_hull_le_lagrangian_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    integer_program_value A₁ b₁ c (convexHull ℝ Q) ≤
      lagrangian_dual_value A₁ b₁ c Q := by
  -- Rewrite both owners so the proof can compare feasible-point values with every multiplier.
  rw [integer_program_value_eq_sSup, lagrangian_dual_value_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨lam, hlam, rfl⟩
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hplain :
      ((c ⬝ᵥ x : ℝ) : EReal) ≤
        ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) := by
    -- Feasibility makes the Lagrangian penalty nonnegative for every `λ ≥ 0`.
    exact_mod_cast
      (objective_le_lagrangian_objective_of_mem_feasible
        A₁ b₁ c (convexHull ℝ Q) lam hlam hx)
  -- The penalized objective at a convexified feasible point is bounded by the original
  -- relaxation value over `Q`.
  exact hplain.trans
    (lagrangian_objective_le_lagrangian_relaxation_value_of_mem_convex_hull
      A₁ b₁ c Q lam hx.1)

/-- Helper for Theorem 8.2: the penalized objective can be rewritten as the dualized objective
for `c - λ A₁` plus the constant term `λ b₁`. -/
lemma penalizedObjective_eq_dualizedObjective
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin m₁ → ℝ)
    (x : Fin n → ℝ) :
    c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) =
      (c - lam ᵥ* A₁) ⬝ᵥ x + lam ⬝ᵥ b₁ := by
  calc
    c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x)
        = c ⬝ᵥ x + (lam ⬝ᵥ b₁ - lam ⬝ᵥ (A₁ *ᵥ x)) := by
            rw [dotProduct_sub]
    _ = c ⬝ᵥ x + (lam ⬝ᵥ b₁ - (lam ᵥ* A₁) ⬝ᵥ x) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (c - lam ᵥ* A₁) ⬝ᵥ x + lam ⬝ᵥ b₁ := by
          rw [sub_dotProduct]
          ring

/-- Helper for Theorem 8.2: convexifying the base set does not change the Lagrangian relaxation
value because the penalized objective is affine. -/
theorem lagrangianRelaxationValue_eq_convexHull
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) :
    lagrangian_relaxation_value A₁ b₁ c Q lam =
      lagrangian_relaxation_value A₁ b₁ c (convexHull ℝ Q) lam := by
  apply le_antisymm
  · -- The convex hull only enlarges the candidate set, so the original supremum cannot increase.
    rw [lagrangian_relaxation_value_eq_sSup, lagrangian_relaxation_value_eq_sSup]
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_sSup ⟨x, subset_convexHull ℝ Q hx, rfl⟩
  · -- Every convexified candidate is already bounded by the original relaxation value.
    rw [lagrangian_relaxation_value_eq_sSup]
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact
      lagrangian_objective_le_lagrangian_relaxation_value_of_mem_convex_hull
        A₁ b₁ c Q lam hx

/-- Helper for Theorem 8.2: regard a pure subset of `ℝ^n` as a mixed set with no continuous
coordinates. -/
def pureAsMixedSet (P : Set (Fin n → ℝ)) : Set (MixedRealPoint n 0) :=
  {xy | xy.1 ∈ P}

/-- Helper for Theorem 8.2: flattening a zero-continuous-block point recovers the original
vector. -/
lemma appendEquiv_zeroContinuousBlock
    (x : Fin n → ℝ) :
    Fin.appendEquiv n 0 (x, 0) = x := by
  -- With no continuous coordinates, `Fin.appendEquiv` only reads the first block.
  ext i
  simpa [Fin.appendEquiv] using Fin.append_left x (0 : Fin 0 → ℝ) i

/-- Helper for Theorem 8.2: flattening the mixed-integer points of the zero-block wrapper gives
back the pure-integer points. -/
lemma image_mixedIntegerPoints_pureAsMixedSet_eq
    (P : Set (Fin n → ℝ)) :
    Fin.appendEquiv n 0 '' mixed_integer_points (pureAsMixedSet P) = pure_integer_points P := by
  ext x
  constructor
  · rintro ⟨xy, hxy, hxy_eq⟩
    rcases xy with ⟨x', y'⟩
    have hx' : x' = x := by
      ext i
      have hi := congrFun hxy_eq i
      calc
        x' i = Fin.append x' y' i := by simpa using (Fin.append_left x' y' i).symm
        _ = x i := hi
    rcases (mem_mixed_integer_points_iff.mp hxy) with ⟨hxyP, hxyInt⟩
    have hxP : x ∈ P := by
      -- Only the first block survives the zero-block flattening.
      simpa [pureAsMixedSet] using hx' ▸ hxyP
    have hxInt : x ∈ ℤ^n := by
      rw [mem_mixed_integer_lattice_iff] at hxyInt
      simpa using hx' ▸ hxyInt
    exact (mem_pure_integer_points_iff).2 ⟨hxP, hxInt⟩
  · intro hx
    rcases (mem_pure_integer_points_iff.mp hx) with ⟨hxP, hxInt⟩
    refine ⟨(x, 0), ?_, appendEquiv_zeroContinuousBlock x⟩
    -- Reinsert the unique zero continuous block to return to the mixed ambient space.
    refine (mem_mixed_integer_points_iff).2 ?_
    refine ⟨by simpa [pureAsMixedSet] using hxP, ?_⟩
    rw [mem_mixed_integer_lattice_iff]
    simpa using hxInt

/-- Helper for Theorem 8.2: a rational matrix polyhedron becomes the corresponding rational mixed
polyhedron when the continuous block has size zero. -/
lemma pureAsMixedSet_eq_rationalMixedPolyhedronZeroBlock
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    pureAsMixedSet (rational_matrix_polyhedron A b) =
      rational_mixed_polyhedron A (0 : Matrix (Fin m) (Fin 0) ℚ) b := by
  ext xy
  rcases xy with ⟨x, y⟩
  have hy0 : y = 0 := by
    ext i
    exact Fin.elim0 i
  -- Route correction: keep the `p = 0` transport local instead of reopening the old Chapter 5
  -- hull route.
  simp [pureAsMixedSet, mem_rational_matrix_polyhedron, mem_rational_mixed_polyhedron_iff, hy0]

/-- Helper for Theorem 8.2: flattening a rational mixed polyhedron with zero continuous block
recovers the corresponding rational matrix polyhedron. -/
lemma image_rationalMixedPolyhedron_zeroContinuousBlock_eq
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin 0) ℚ)
    (b : Fin m → ℚ) :
    Fin.appendEquiv n 0 '' rational_mixed_polyhedron A G b = rational_matrix_polyhedron A b := by
  ext x
  constructor
  · rintro ⟨xy, hxy, hxy_eq⟩
    rcases xy with ⟨x', y'⟩
    have hy0 : y' = 0 := by
      ext i
      exact Fin.elim0 i
    have hx' : x' = x := by
      ext i
      have hi := congrFun hxy_eq i
      calc
        x' i = Fin.append x' y' i := by simpa using (Fin.append_left x' y' i).symm
        _ = x i := hi
    -- The zero-size continuous block contributes nothing to the mixed inequality system.
    have hxPoly : x' ∈ rational_matrix_polyhedron A b := by
      rw [mem_rational_matrix_polyhedron]
      rw [mem_rational_mixed_polyhedron_iff] at hxy
      simpa [hy0] using hxy
    exact hx' ▸ hxPoly
  · intro hx
    refine ⟨(x, 0), ?_, appendEquiv_zeroContinuousBlock x⟩
    -- Reintroduce the unique zero continuous block on the mixed side.
    simpa [rational_matrix_polyhedron, rational_mixed_polyhedron]
      using hx

/-- Helper for Theorem 8.2: stacking the easy-block inequalities with the nonnegativity rows gives
the rational matrix presentation of an integral easy block. -/
def integralEasyBlockConstraintMatrix
    {m₂ : ℕ}
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ) :
    Matrix (Fin (m₂ + n)) (Fin n) ℚ :=
  (Matrix.fromRows (A₂.map (Int.castRingHom ℚ)) (-(1 : Matrix (Fin n) (Fin n) ℚ))).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

/-- Helper for Theorem 8.2: the stacked right-hand side for the rational presentation of an
integral easy block is `(b², 0)`. -/
def integralEasyBlockConstraintRhs
    {m₂ : ℕ}
    (b₂ : Fin m₂ → ℤ) :
    Fin (m₂ + n) → ℚ :=
  Sum.elim (fun i ↦ (b₂ i : ℚ)) (fun _ ↦ 0) ∘ finSumFinEquiv.symm

/-- Helper for Theorem 8.2: an integral easy block is a rational matrix polyhedron after stacking
its inequality rows with the nonnegativity rows. -/
lemma integralEasyBlockFeasibleSet_eq_rationalMatrixPolyhedron
    {m₂ : ℕ}
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ) :
    integral_easy_block_feasible_set A₂ b₂ =
      rational_matrix_polyhedron
        (integralEasyBlockConstraintMatrix A₂)
        (integralEasyBlockConstraintRhs b₂) := by
  ext x
  constructor
  · intro hx
    rw [mem_rational_matrix_polyhedron]
    rw [integral_easy_block_feasible_set, mem_easy_block_feasible_set_iff] at hx
    intro i
    cases h : finSumFinEquiv.symm i with
    | inl r =>
        simpa [integralEasyBlockConstraintMatrix, integralEasyBlockConstraintRhs, h, Matrix.mulVec,
          dotProduct]
          using hx.1 r
    | inr s =>
        have hsEq : ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ) s j : ℝ) * x j) = x s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro j _ hjs
            have hne : ¬ s = j := by
              simpa [eq_comm] using hjs
            simp [hne]
          · simp
        have hs : 0 ≤ ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ) s j : ℝ) * x j) := by
          simpa [hsEq] using hx.2 s
        simpa [integralEasyBlockConstraintMatrix, integralEasyBlockConstraintRhs, h, Matrix.mulVec,
          dotProduct]
          using hs
  · rw [mem_rational_matrix_polyhedron]
    intro hx
    rw [integral_easy_block_feasible_set, mem_easy_block_feasible_set_iff]
    refine ⟨?_, ?_⟩
    · intro r
      let i : Fin (m₂ + n) := finSumFinEquiv (Sum.inl r)
      have hi := hx i
      simpa [integralEasyBlockConstraintMatrix, integralEasyBlockConstraintRhs, i, Matrix.mulVec,
        dotProduct]
        using hi
    · intro s
      let i : Fin (m₂ + n) := finSumFinEquiv (Sum.inr s)
      have hi := hx i
      have hsEq : ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ) s j : ℝ) * x j) = x s := by
        rw [Finset.sum_eq_single s]
        · simp
        · intro j _ hjs
          have hne : ¬ s = j := by
            simpa [eq_comm] using hjs
          simp [hne]
        · simp
      simpa [integralEasyBlockConstraintMatrix, integralEasyBlockConstraintRhs, i, Matrix.mulVec,
        dotProduct, hsEq]
        using hi

/-- Helper for Theorem 8.2: if `Q` is the pure-integer point set of an integral easy block, then
`convexHull ℝ Q` admits a rational matrix presentation. -/
lemma easyBlockIntegerOrigin_convexHull_eq_polyhedronLeSet
    {Q : Set (Fin n → ℝ)}
    (hQ : HasEasyBlockIntegerOrigin Q) :
    ∃ p : ℕ, ∃ C : Matrix (Fin p) (Fin n) ℚ, ∃ d : Fin p → ℚ,
      convexHull ℝ Q = polyhedron_le_set (C.map (Rat.castHom ℝ)) (fun i ↦ (d i : ℝ)) := by
  rcases hQ with ⟨m₂, A₂, b₂, rfl⟩
  have hMixedRational :
      is_rational_mixed_polyhedron
        (pureAsMixedSet (integral_easy_block_feasible_set A₂ b₂)) := by
    -- Package the rational pure system as a mixed system with zero continuous block.
    rw [integralEasyBlockFeasibleSet_eq_rationalMatrixPolyhedron]
    rw [pureAsMixedSet_eq_rationalMixedPolyhedronZeroBlock]
    exact
      (is_rational_mixed_polyhedron_iff).2
        ⟨m₂ + n, integralEasyBlockConstraintMatrix A₂, 0, integralEasyBlockConstraintRhs b₂, rfl⟩
  rcases
      (is_rational_mixed_polyhedron_iff).mp
        (Theorem15Support.mixed_integer_hull_is_rational_mixed_polyhedron_local
          (P := pureAsMixedSet (integral_easy_block_feasible_set A₂ b₂))
          hMixedRational) with
    ⟨p, C, G, d, hHullMixed⟩
  refine ⟨p, C, d, ?_⟩
  have hHullImage :
      Fin.appendEquiv n 0 ''
          convexHull ℝ
            (mixed_integer_points (pureAsMixedSet (integral_easy_block_feasible_set A₂ b₂))) =
        Fin.appendEquiv n 0 '' rational_mixed_polyhedron C G d := by
    -- Flatten the mixed hull back into the original `ℝ^n` ambient space.
    exact congrArg (fun S ↦ Fin.appendEquiv n 0 '' S) hHullMixed
  rw [Theorem15Support.appendEquiv_image_convexHull,
    image_mixedIntegerPoints_pureAsMixedSet_eq,
    image_rationalMixedPolyhedron_zeroContinuousBlock_eq] at hHullImage
  simpa [rational_matrix_polyhedron] using hHullImage

/-- Helper for Theorem 8.2: once `convexHull ℝ Q` has a rational matrix presentation, the
convex-hull feasible region is exactly the primal region of the stacked system. -/
lemma convexHullFeasibleSet_eq_stackedPrimalRegion
    {p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (Q : Set (Fin n → ℝ))
    (C : Matrix (Fin p) (Fin n) ℚ)
    (d : Fin p → ℚ)
    (hconv :
      convexHull ℝ Q =
        polyhedron_le_set (C.map (Rat.castHom ℝ)) (fun i ↦ (d i : ℝ))) :
    let stackedA :
        Matrix (Fin (m₁ + p)) (Fin n) ℝ :=
      (Matrix.fromRows A₁ (C.map (Rat.castHom ℝ))).submatrix finSumFinEquiv.symm (Equiv.refl _)
    let stackedb : Fin (m₁ + p) → ℝ :=
      Sum.elim b₁ (fun i ↦ (d i : ℝ)) ∘ finSumFinEquiv.symm
    convex_hull_feasible_set A₁ b₁ Q = primal_feasible_region stackedA stackedb := by
  intro stackedA stackedb
  let CReal : Matrix (Fin p) (Fin n) ℝ := C.map (Rat.castHom ℝ)
  let dReal : Fin p → ℝ := fun i ↦ (d i : ℝ)
  ext x
  have hmul :=
    Matrix.submatrix_mulVec_equiv
      (Matrix.fromRows A₁ CReal)
      x
      finSumFinEquiv.symm
      (Equiv.refl _)
  rw [mem_convex_hull_feasible_set_iff, mem_primal_feasible_region_iff]
  constructor
  · rintro ⟨hxConv, hxA⟩
    have hxC : CReal *ᵥ x ≤ dReal := by
      -- Rewrite convex-hull membership through the chosen matrix presentation.
      rw [hconv] at hxConv
      simpa [CReal, dReal, polyhedron_le_set] using hxConv
    have hxRows : (Matrix.fromRows A₁ CReal) *ᵥ x ≤ Sum.elim b₁ dReal := by
      intro r
      cases r with
      | inl i =>
          simpa [Matrix.fromRows_mulVec] using hxA i
      | inr j =>
          simpa [Matrix.fromRows_mulVec] using hxC j
    intro r
    have hrow := hxRows (finSumFinEquiv.symm r)
    have hEq :
        (stackedA *ᵥ x) r = ((Matrix.fromRows A₁ CReal) *ᵥ x) (finSumFinEquiv.symm r) := by
      simpa [stackedA] using congrFun hmul r
    have hRhs : stackedb r = (Sum.elim b₁ dReal) (finSumFinEquiv.symm r) := by
      simp [stackedb, dReal]
    rw [hEq, hRhs]
    exact hrow
  · intro hx
    have hxRows : (Matrix.fromRows A₁ CReal) *ᵥ x ≤ Sum.elim b₁ dReal := by
      intro r
      have hrow := hx (finSumFinEquiv r)
      have hEq :
          (stackedA *ᵥ x) (finSumFinEquiv r) = ((Matrix.fromRows A₁ CReal) *ᵥ x) r := by
        simpa [stackedA] using congrFun hmul (finSumFinEquiv r)
      have hRhs : stackedb (finSumFinEquiv r) = (Sum.elim b₁ dReal) r := by
        simp [stackedb, dReal]
      rw [hEq, hRhs] at hrow
      exact hrow
    have hxA : A₁ *ᵥ x ≤ b₁ := by
      -- Read the `A₁` rows back from the stacked primal constraints.
      intro i
      simpa [Matrix.fromRows_mulVec] using hxRows (Sum.inl i)
    have hxC : CReal *ᵥ x ≤ dReal := by
      -- Read the hull-presentation rows back from the stacked primal constraints.
      intro j
      simpa [Matrix.fromRows_mulVec] using hxRows (Sum.inr j)
    refine ⟨?_, hxA⟩
    rw [hconv]
    simpa [CReal, dReal, polyhedron_le_set] using hxC

/-- Helper for Theorem 8.2: every feasible dual certificate of the stacked hull LP gives an upper
bound on the Lagrangian dual value. -/
lemma stackedDualObjective_ge_lagrangianDualValue
    {p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (C : Matrix (Fin p) (Fin n) ℚ)
    (d : Fin p → ℚ)
    (hconv :
      convexHull ℝ Q =
        polyhedron_le_set (C.map (Rat.castHom ℝ)) (fun i ↦ (d i : ℝ)))
    (u : Fin (m₁ + p) → ℝ) :
    let stackedA :
        Matrix (Fin (m₁ + p)) (Fin n) ℝ :=
      (Matrix.fromRows A₁ (C.map (Rat.castHom ℝ))).submatrix finSumFinEquiv.symm (Equiv.refl _)
    let stackedb : Fin (m₁ + p) → ℝ :=
      Sum.elim b₁ (fun i ↦ (d i : ℝ)) ∘ finSumFinEquiv.symm
    u ∈ dual_feasible_region stackedA c →
      lagrangian_dual_value A₁ b₁ c Q ≤ ((u ⬝ᵥ stackedb : ℝ) : EReal) := by
  intro stackedA stackedb hu
  let CReal : Matrix (Fin p) (Fin n) ℝ := C.map (Rat.castHom ℝ)
  let dReal : Fin p → ℝ := fun i ↦ (d i : ℝ)
  let lam : Fin m₁ → ℝ := fun i ↦ u (Fin.castAdd p i)
  let mu : Fin p → ℝ := fun i ↦ u (Fin.natAdd m₁ i)
  rcases (mem_dual_feasible_region_iff stackedA c u).mp hu with ⟨huEq, huNonneg⟩
  have hlamNonneg : 0 ≤ lam := by
    -- The first block inherits nonnegativity from the stacked multiplier.
    intro i
    exact huNonneg (Fin.castAdd p i)
  have hmuNonneg : 0 ≤ mu := by
    -- The second block inherits nonnegativity from the stacked multiplier.
    intro i
    exact huNonneg (Fin.natAdd m₁ i)
  have hvecSplit :
      lam ᵥ* A₁ + mu ᵥ* CReal = c := by
    -- Split the stacked row equation into the `A₁` and `C` blocks.
    have hvec :=
      Matrix.submatrix_vecMul_equiv
        (Matrix.fromRows A₁ CReal)
        u
        finSumFinEquiv.symm
        (Equiv.refl _)
    have huSplit :
        (u ∘ finSumFinEquiv) ᵥ* Matrix.fromRows A₁ CReal = c := by
      ext j
      calc
        ((u ∘ finSumFinEquiv) ᵥ* Matrix.fromRows A₁ CReal) j = (u ᵥ* stackedA) j := by
            symm
            simpa [stackedA] using congrFun hvec j
        _ = c j := congrFun huEq j
    have hlamEq : ((u ∘ finSumFinEquiv) ∘ Sum.inl) = lam := by
      funext i
      rfl
    have hmuEq : ((u ∘ finSumFinEquiv) ∘ Sum.inr) = mu := by
      funext i
      rfl
    ext j
    simpa [Matrix.vecMul_fromRows, hlamEq, hmuEq] using congrFun huSplit j
  have hmuDual :
      mu ∈ dual_feasible_region CReal (c - lam ᵥ* A₁) := by
    -- Move the `A₁` block to the right-hand side to obtain a dual certificate for `C x ≤ d`.
    rw [mem_dual_feasible_region_iff]
    refine ⟨?_, hmuNonneg⟩
    ext j
    have hj := congrFun hvecSplit j
    exact (eq_sub_iff_add_eq).2 <| by simpa [Pi.sub_apply, add_comm] using hj
  have hstackedObjective :
      u ⬝ᵥ stackedb = lam ⬝ᵥ b₁ + mu ⬝ᵥ dReal := by
    -- The stacked right-hand side splits exactly as `(b₁, d)`.
    rw [dotProduct, dotProduct, dotProduct, Fin.sum_univ_add]
    simp [lam, mu, stackedb, dReal]
  have hRelaxLe :
      lagrangian_relaxation_value A₁ b₁ c (convexHull ℝ Q) lam ≤
        ((u ⬝ᵥ stackedb : ℝ) : EReal) := by
    -- Bound every convexified candidate by weak duality for the hull presentation `C x ≤ d`.
    rw [lagrangian_relaxation_value_eq_sSup]
    refine sSup_le ?_
    rintro _ ⟨x, hxConv, rfl⟩
    have hxC : CReal *ᵥ x ≤ dReal := by
      rw [hconv] at hxConv
      simpa [CReal, dReal, polyhedron_le_set] using hxConv
    have hxPrimal : x ∈ primal_feasible_region CReal dReal :=
      (mem_primal_feasible_region_iff CReal dReal x).2 hxC
    have hweak :
        (c - lam ᵥ* A₁) ⬝ᵥ x ≤ mu ⬝ᵥ dReal :=
      weak_duality_feasible_pair CReal dReal (c - lam ᵥ* A₁) hxPrimal hmuDual
    have hpenalized :
        c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) ≤ lam ⬝ᵥ b₁ + mu ⬝ᵥ dReal := by
      rw [penalizedObjective_eq_dualizedObjective A₁ b₁ c lam x]
      linarith
    have hpenalizedE :
        ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) ≤
          ((lam ⬝ᵥ b₁ + mu ⬝ᵥ dReal : ℝ) : EReal) := by
      exact_mod_cast hpenalized
    simpa [hstackedObjective] using hpenalizedE
  have hLamInfs :
      lagrangian_dual_value A₁ b₁ c Q ≤ lagrangian_relaxation_value A₁ b₁ c Q lam := by
    -- The dual value is the infimum over all nonnegative multipliers, so it is below the
    -- relaxation value at the particular feasible multiplier `lam`.
    rw [lagrangian_dual_value_eq_sInf]
    exact sInf_le ⟨lam, hlamNonneg, rfl⟩
  have hRelaxQLe :
      lagrangian_relaxation_value A₁ b₁ c Q lam ≤ ((u ⬝ᵥ stackedb : ℝ) : EReal) := by
    rw [lagrangianRelaxationValue_eq_convexHull A₁ b₁ c Q lam]
    exact hRelaxLe
  exact hLamInfs.trans hRelaxQLe

/-- Theorem 8.2. Let `Q` be the pure-integer points of a Section 8.1 easy block
`{x ∈ ℝ^n_+ | A₂ x ≤ b²}`. Assume `{x : A₁ x ≤ b¹, x ∈ conv(Q)}` is nonempty. Then the
Lagrangian dual value `z_LD` equals the optimal value of maximizing `c x` over
`{x : A₁ x ≤ b¹, x ∈ conv(Q)}`. -/
theorem lagrangian_dual_value_eq_integer_program_value_on_convex_hull
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (hQ : HasEasyBlockIntegerOrigin Q)
    (hfeas : Set.Nonempty (convex_hull_feasible_set A₁ b₁ Q)) :
    lagrangian_dual_value A₁ b₁ c Q =
      integer_program_value A₁ b₁ c (convexHull ℝ Q) := by
  refine le_antisymm ?_ (integer_program_value_on_convex_hull_le_lagrangian_dual_value A₁ b₁ c Q)
  rcases easyBlockIntegerOrigin_convexHull_eq_polyhedronLeSet (n := n) hQ with
    ⟨p, C, d, hconv⟩
  let stackedA :
      Matrix (Fin (m₁ + p)) (Fin n) ℝ :=
    (Matrix.fromRows A₁ (C.map (Rat.castHom ℝ))).submatrix finSumFinEquiv.symm (Equiv.refl _)
  let stackedb : Fin (m₁ + p) → ℝ :=
    Sum.elim b₁ (fun i ↦ (d i : ℝ)) ∘ finSumFinEquiv.symm
  have hRegion :
      convex_hull_feasible_set A₁ b₁ Q = primal_feasible_region stackedA stackedb := by
    -- Rewrite the convex-hull feasible set as the primal region of the stacked hull LP.
    simpa [stackedA, stackedb] using
      (convexHullFeasibleSet_eq_stackedPrimalRegion (p := p) A₁ b₁ Q C d hconv)
  have hPrimalNonempty : Set.Nonempty (primal_feasible_region stackedA stackedb) := by
    rw [← hRegion]
    exact hfeas
  have hDuality :
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb) =
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := by
    -- Strong duality applies because the stacked primal region is nonempty.
    exact linear_program_duality_eq_except_both_empty stackedA stackedb c (Or.inl hPrimalNonempty)
  have hDualUpper :
      lagrangian_dual_value A₁ b₁ c Q ≤
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := by
    -- Every stacked dual feasible point yields an upper bound on the Lagrangian dual value.
    refine le_sInf ?_
    rintro _ ⟨u, hu, rfl⟩
    simpa [stackedA, stackedb] using
      (stackedDualObjective_ge_lagrangianDualValue (p := p) A₁ b₁ c Q C d hconv u hu)
  have hPrimalValue :
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb) =
        integer_program_value A₁ b₁ c (convexHull ℝ Q) := by
    -- The stacked primal objective is the original convex-hull objective after rewriting the
    -- feasible region.
    calc
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb)
          =
        sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            convex_hull_feasible_set A₁ b₁ Q) := by
              rw [← hRegion]
      _ = integer_program_value A₁ b₁ c (convexHull ℝ Q) := by
            rw [integer_program_value_eq_sSup]
  calc
    lagrangian_dual_value A₁ b₁ c Q ≤
        sInf
          ((fun u : Fin (m₁ + p) → ℝ ↦ ((u ⬝ᵥ stackedb : ℝ) : EReal)) ''
            dual_feasible_region stackedA c) := hDualUpper
    _ =
        sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region stackedA stackedb) := hDuality.symm
    _ = integer_program_value A₁ b₁ c (convexHull ℝ Q) := hPrimalValue

/-- If `Q` comes from the pure-integer points of a Section 8.1 easy block and the convexified
feasible objective image already has an attained maximum, then that maximum is the Lagrangian dual
value. -/
theorem lagrangian_dual_value_is_max_on_convex_hull_feasible_region
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (hQ : HasEasyBlockIntegerOrigin Q)
    (hmax :
      IsGreatest
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          convex_hull_feasible_set A₁ b₁ Q)
        (integer_program_value A₁ b₁ c (convexHull ℝ Q))) :
    IsGreatest
      ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
        convex_hull_feasible_set A₁ b₁ Q)
      (lagrangian_dual_value A₁ b₁ c Q) := by
  have hfeas : Set.Nonempty (convex_hull_feasible_set A₁ b₁ Q) := by
    rcases hmax.1 with ⟨x, hx, _⟩
    exact ⟨x, hx⟩
  -- Transport the attained maximum value across the main equality theorem.
  simpa [lagrangian_dual_value_eq_integer_program_value_on_convex_hull A₁ b₁ c Q hQ hfeas]
    using hmax

end Theorem82
