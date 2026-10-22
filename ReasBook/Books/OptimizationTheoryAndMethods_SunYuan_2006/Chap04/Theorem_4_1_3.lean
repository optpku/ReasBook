/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_1_2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Filter.Extr

open Matrix
open scoped BigOperators

noncomputable section

-- Domain sampling for this item:
-- * chapter owner for method data: `GeneralConjugateDirectionMethod`
-- * core/canonical owner for `G`-conjugacy: `Matrix.IsConjugateFamily`
-- * core/canonical owners for minimization, one-dimensional line-search profiles, affine search
--   spaces, and positive definiteness:
--   `IsMinOn`, `lineSearchObjective`, `AffineSubspace`, `Matrix.PosDef`
-- * bridge/view here: `IsQuadraticConjugateDirectionMethod` and the search-space membership
--   theorem recovering the textbook coefficient form from the affine-subspace owner

section

variable {n : ℕ}

local notation "Vector" => ConjugateDirectionPoint n

/-- The quadratic objective `x ↦ (1 / 2) * xᵀ G x + bᵀ x + c` with Hessian `G`. -/
def quadraticObjective (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ) (x : Vector) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (Matrix.toEuclideanLin G x) + dotProduct b x + c

/-- Evaluating `quadraticObjective G b c` means substituting `x` into the explicit quadratic
formula `1 / 2 * xᵀ G x + bᵀ x + c`. -/
theorem quadraticObjective_apply (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (x : Vector) :
    quadraticObjective G b c x =
      (1 / 2 : ℝ) * dotProduct x (Matrix.toEuclideanLin G x) + dotProduct b x + c := by
  -- This is the defining formula of `quadraticObjective`.
  rfl

/-- Helper for Chapter04 Theorem 4.1.3: for a symmetric matrix `G`, the centered quadratic core
`x ↦ (1 / 2) * xᵀ G x` has Fréchet derivative `G x`. -/
theorem quadraticObjective_hasFDerivAt_selfAdjoint_core
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) (x : Vector) :
    HasFDerivAt
      (fun y : Vector ↦ (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin G y))
      (InnerProductSpace.toDual ℝ Vector (Matrix.toEuclideanLin G x)) x := by
  let T : Vector →L[ℝ] Vector := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)
  have hHermitian : G.IsHermitian := by
    simpa [Matrix.isHermitian_iff_isSymm] using hG
  have hSymmLin' : (Matrix.toEuclideanLin G).IsSymmetric := by
    exact (Matrix.isSymmetric_toEuclideanLin_iff (A := G)).2 hHermitian
  have hSymmLin : (T : Vector →ₗ[ℝ] Vector).IsSymmetric := by
    simpa [T] using hSymmLin'
  -- Route correction: use the symmetric-operator derivative of `reApplyInnerSelf` directly,
  -- then rewrite it back to the textbook quadratic core.
  have hCore :
      HasStrictFDerivAt (fun y : Vector ↦ T.reApplyInnerSelf y) (2 • innerSL ℝ (T x)) x :=
    hSymmLin.hasStrictFDerivAt_reApplyInnerSelf x
  have hScaled :
      HasFDerivAt (fun y : Vector ↦ (1 / 2 : ℝ) * T.reApplyInnerSelf y)
        ((1 / 2 : ℝ) • (2 • innerSL ℝ (T x))) x :=
    hCore.hasFDerivAt.const_mul (1 / 2 : ℝ)
  -- Rewrite both the scalar quadratic core and the derivative into `dotProduct`/`toDual` form.
  have hFun :
      (fun y : Vector ↦ (1 / 2 : ℝ) * T.reApplyInnerSelf y) =
        (fun y : Vector ↦ (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin G y)) := by
    funext y
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp [T, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hDeriv :
      ((1 / 2 : ℝ) • (2 • innerSL ℝ (T x))) =
        InnerProductSpace.toDual ℝ Vector (Matrix.toEuclideanLin G x) := by
    ext y
    simp [T, InnerProductSpace.toDual_apply_apply]
  rw [hFun, hDeriv] at hScaled
  exact hScaled

/-- A symmetric quadratic objective has gradient `G x + b`. -/
theorem hasGradientAt_quadraticObjective
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (hG : G.IsSymm) (x : Vector) :
    HasGradientAt (quadraticObjective G b c) (Matrix.toEuclideanLin G x + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hQuadratic :=
    quadraticObjective_hasFDerivAt_selfAdjoint_core G hG x
  have hLinear :
      HasFDerivAt (fun y : Vector ↦ dotProduct b y)
        (InnerProductSpace.toDual ℝ Vector b) x := by
    -- The affine term is already a continuous linear functional.
    convert (InnerProductSpace.toDual ℝ Vector b).hasFDerivAt (x := x) using 1
    ext y
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
  -- Add the quadratic core, the linear term, and the constant term.
  have hFun :
      quadraticObjective G b c =
        (fun y : Vector ↦ (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin G y)) +
          ((fun y : Vector ↦ dotProduct b y) + fun _ : Vector ↦ c) := by
    funext y
    simp [quadraticObjective, add_assoc, add_left_comm, add_comm]
  have hDeriv :
      InnerProductSpace.toDual ℝ Vector (Matrix.toEuclideanLin G x + b) =
        InnerProductSpace.toDual ℝ Vector (Matrix.toEuclideanLin G x) +
          (InnerProductSpace.toDual ℝ Vector b + 0) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, add_assoc, add_left_comm, add_comm]
  rw [hFun, hDeriv]
  exact hQuadratic.add (hLinear.add (hasFDerivAt_const c x))

/-- The gradient of a symmetric quadratic objective is `G x + b`. -/
theorem gradient_quadraticObjective
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (hG : G.IsSymm) (x : Vector) :
    gradient (quadraticObjective G b c) x = Matrix.toEuclideanLin G x + b :=
  (hasGradientAt_quadraticObjective G b c hG x).gradient

/-- The affine search space `x₀ + span{d 0, ..., d i}`, expressed through the canonical span
subspace owner based at `x₀` with direction `span{d 0, ..., d i}`. -/
def conjugateDirectionSearchSpace (x0 : Vector) (d : ℕ → Vector) (i : ℕ) :
    AffineSubspace ℝ Vector :=
  AffineSubspace.mk' x0 (Submodule.span ℝ (Set.range (fun j : Fin (i + 1) ↦ d j)))

/-- Membership in the affine search space `x₀ + span{d 0, ..., d i}` is equivalent to having
an explicit representation `x = x0 + ∑ j, β j • d j` using the first `i + 1` directions. -/
theorem mem_conjugateDirectionSearchSpace_iff (x0 : Vector) (d : ℕ → Vector)
    (i : ℕ) (x : Vector) :
    x ∈ conjugateDirectionSearchSpace x0 d i ↔
      ∃ β : Fin (i + 1) → ℝ, x = x0 + ∑ j : Fin (i + 1), β j • d j := by
  rw [conjugateDirectionSearchSpace, AffineSubspace.mem_mk']
  constructor
  · intro hx
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    -- Turn the span witness for `x - x0` back into the affine-coordinate formula for `x`.
    simpa [vsub_eq_sub, vadd_eq_add, add_assoc, add_left_comm, add_comm] using
      (congrArg (fun v : Vector ↦ v +ᵥ x0) hβ).symm
  · rintro ⟨β, hβ⟩
    -- Conversely, the affine-coordinate formula says exactly that `x - x0` lies in the span.
    have hx :
        x -ᵥ x0 = ∑ j : Fin (i + 1), β j • d j := by
      simpa [vsub_eq_sub, vadd_eq_add] using congrArg (fun y : Vector ↦ y -ᵥ x0) hβ
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mpr ⟨β, hx.symm⟩

/-- Helper for Chapter04 Theorem 4.1.3: a positive-definite real matrix is symmetric, so the
quadratic objective has the expected linear gradient formula at every iterate. -/
theorem posDef_isSymm
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) :
    G.IsSymm := by
  -- Positive definiteness packages Hermitian symmetry, which is ordinary symmetry over `ℝ`.
  simpa [Matrix.isHermitian_iff_isSymm] using (show G.IsHermitian from hG.1)

/-- A quadratic conjugate-direction method is a Chapter 4 general conjugate-direction run for
`quadraticObjective G b c` whose conjugacy matrix is the Hessian `G`, whose first `n` stages
are generated, and whose first `n` line searches are exact on the whole affine line. -/
structure IsQuadraticConjugateDirectionMethod
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)) : Prop where
  posDef : G.PosDef
  matrix_eq : A.G = G
  generated (k : ℕ) (hk : k < n) : A.ε < ‖A.g k‖
  exactLineSearch (k : ℕ) (hk : k < n) :
    IsMinOn
      (lineSearchObjective (quadraticObjective G b c) (A k) (A.d k))
      Set.univ
      (A.α k)

/-- The theorem-specific quadratic predicate equips the owner matrix `A.G` with positive
definiteness via the Hessian identification `A.G = G`. -/
theorem IsQuadraticConjugateDirectionMethod.method_posDef
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) :
    A.G.PosDef := by
  simpa [hMethod.matrix_eq] using hMethod.posDef

/-- The first `n` directions in a quadratic conjugate-direction method form the canonical
`G`-conjugate family coming from the Chapter 4 owner theorem. -/
theorem IsQuadraticConjugateDirectionMethod.conjugateFamily
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) :
    G.IsConjugateFamily (fun i : Fin n ↦ A.d i) := by
  letI : Fact A.G.PosDef := ⟨hMethod.method_posDef⟩
  have hfamily : A.G.IsConjugateFamily (fun i : Fin n ↦ A.d i) :=
    A.isConjugateFamily_prefix fun j hj ↦
      hMethod.generated j (Nat.lt_trans (Nat.lt_succ_self j) hj)
  simpa [hMethod.matrix_eq] using hfamily

/-- A conjugate-direction run uses nonzero search directions on the first `n` stages. -/
theorem IsQuadraticConjugateDirectionMethod.direction_ne
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {k : ℕ} (hk : k < n) :
    A.d k ≠ 0 := by
  simpa using hMethod.conjugateFamily.nonzero ⟨k, hk⟩

/-- A conjugate-direction run has pairwise `G`-conjugate first `n` search directions. -/
theorem IsQuadraticConjugateDirectionMethod.conjugate
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A)
    {i j : ℕ} (hij : i < j) (hj : j < n) :
    dotProduct (A.d i) (G.mulVec (A.d j)) = 0 := by
  have hfamily :=
    Matrix.isConjugateFamily_iff.mp hMethod.conjugateFamily
  exact hfamily.2 ⟨i, Nat.lt_trans hij hj⟩ ⟨j, hj⟩ (by
    intro h
    exact Nat.ne_of_lt hij (congrArg Fin.val h))

/-- A nonterminal conjugate-direction step uses a nonzero search direction, exact line search,
and the standard iterate update. -/
theorem IsQuadraticConjugateDirectionMethod.step
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {k : ℕ} (hk : k < n) :
    A.d k ≠ 0 ∧
      IsMinOn
        (lineSearchObjective (quadraticObjective G b c) (A k) (A.d k))
        Set.univ
        (A.α k) ∧
        A (k + 1) = A k + A.α k • A.d k := by
  refine ⟨hMethod.direction_ne hk, hMethod.exactLineSearch k hk, ?_⟩
  simpa using A.update k (hMethod.generated k hk)

/-- The predicate `IsQuadraticConjugateDirectionMethod` is proof-irrelevant. -/
instance isQuadraticConjugateDirectionMethod_subsingleton
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)} :
    Subsingleton (IsQuadraticConjugateDirectionMethod G b c A) := inferInstance

/-- Helper for Chapter04 Theorem 4.1.3: along a quadratic conjugate-direction step, the next
gradient differs from the current one by the Hessian action on the accepted displacement. -/
theorem quadratic_gradient_step_eq
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {k : ℕ} (hk : k < n) :
    A.g (k + 1) = A.g k + A.α k • Matrix.toEuclideanLin G (A.d k) := by
  have hGsymm : G.IsSymm := posDef_isSymm hMethod.posDef
  rcases hMethod.step hk with ⟨_, _, hUpdate⟩
  have hgk : A.g k = Matrix.toEuclideanLin G (A k) + b := by
    -- Identify the recorded gradient with the explicit quadratic gradient at stage `k`.
    calc
      A.g k = gradient (quadraticObjective G b c) (A k) := by
        symm
        exact (A.hasGradientAt k).gradient
      _ = Matrix.toEuclideanLin G (A k) + b := gradient_quadraticObjective G b c hGsymm (A k)
  have hgk1 : A.g (k + 1) = Matrix.toEuclideanLin G (A (k + 1)) + b := by
    -- The same identification applies at the updated iterate.
    calc
      A.g (k + 1) = gradient (quadraticObjective G b c) (A (k + 1)) := by
        symm
        exact (A.hasGradientAt (k + 1)).gradient
      _ = Matrix.toEuclideanLin G (A (k + 1)) + b :=
        gradient_quadraticObjective G b c hGsymm (A (k + 1))
  -- Substitute the iterate update and use linearity of `Matrix.toEuclideanLin`.
  calc
    A.g (k + 1) = Matrix.toEuclideanLin G (A (k + 1)) + b := hgk1
    _ = Matrix.toEuclideanLin G (A k + A.α k • A.d k) + b := by rw [hUpdate]
    _ = Matrix.toEuclideanLin G (A k) + A.α k • Matrix.toEuclideanLin G (A.d k) + b := by
      simp
    _ = A.g k + A.α k • Matrix.toEuclideanLin G (A.d k) := by
      rw [hgk]
      abel

/-- Helper for Chapter04 Theorem 4.1.3: the exact line search at stage `k` makes the next
gradient orthogonal to the current search direction `d k`. -/
theorem lineSearch_gradient_orthogonal_current_direction
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {k : ℕ} (hk : k < n) :
    dotProduct (A.g (k + 1)) (A.d k) = 0 := by
  rcases hMethod.step hk with ⟨_, hMin, hUpdate⟩
  have hLocalMin :
      IsLocalMin (lineSearchObjective (quadraticObjective G b c) (A k) (A.d k)) (A.α k) := by
    -- A global minimum on `Set.univ` is, in particular, a local minimum.
    exact hMin.isLocalMin <| by simpa using (Set.mem_univ (A.α k))
  have hDerivZero :
      deriv (lineSearchObjective (quadraticObjective G b c) (A k) (A.d k)) (A.α k) = 0 :=
    hLocalMin.deriv_eq_zero
  have hGrad :
      HasGradientAt (quadraticObjective G b c) (A.g (k + 1)) (A k + A.α k • A.d k) := by
    -- Rewrite the recorded next gradient onto the accepted line-search point.
    simpa [hUpdate] using A.hasGradientAt (k + 1)
  have hDeriv :
      deriv (lineSearchObjective (quadraticObjective G b c) (A k) (A.d k)) (A.α k) =
        dotProduct (A.g (k + 1)) (A.d k) := by
    -- The derivative of the line-search profile is the gradient pairing with the direction.
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      hGrad.deriv_lineSearchObjective_apply
  rw [hDeriv] at hDerivZero
  exact hDerivZero

/-- Helper for Chapter04 Theorem 4.1.3: the textbook invariant `(4.1.2)` holds, namely the
stage-`i` gradient is orthogonal to every previously used search direction. -/
theorem quadratic_gradient_orthogonal_to_previous_directions
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) :
    ∀ {i j : ℕ}, i ≤ n → j < i → dotProduct (A.g i) (A.d j) = 0
  | 0, j, _, hj => (Nat.not_lt_zero _ hj).elim
  | i + 1, j, hi, hj => by
      have hk : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hj'
      · -- This is the `j = i` case from the textbook: exact line search gives stationarity.
        simpa using lineSearch_gradient_orthogonal_current_direction hMethod hk
      · have hPrev : dotProduct (A.g i) (A.d j) = 0 :=
          quadratic_gradient_orthogonal_to_previous_directions hMethod (Nat.le_of_succ_le hi) hj'
        have hConj : dotProduct (A.d j) (G.mulVec (A.d i)) = 0 :=
          hMethod.conjugate hj' hk
        -- For `j < i`, expand `g_(i+1)` using the quadratic gradient step and kill the new term
        -- by `G`-conjugacy.
        calc
          dotProduct (A.g (i + 1)) (A.d j) =
              dotProduct (A.g i + A.α i • Matrix.toEuclideanLin G (A.d i)) (A.d j) := by
                exact congrArg (fun v : Vector => dotProduct v (A.d j))
                  (quadratic_gradient_step_eq hMethod hk)
          _ = dotProduct (A.d j) (A.g i + A.α i • Matrix.toEuclideanLin G (A.d i)) := by
                simpa using
                  (dotProduct_comm (A.g i + A.α i • Matrix.toEuclideanLin G (A.d i)) (A.d j))
          _ = dotProduct (A.d j) (A.g i) +
                dotProduct (A.d j) (A.α i • Matrix.toEuclideanLin G (A.d i)) := by
                rw [dotProduct_add]
          _ = dotProduct (A.g i) (A.d j) +
                A.α i * dotProduct (A.d j) (G.mulVec (A.d i)) := by
                rw [dotProduct_smul, dotProduct_comm (A.d j) (A.g i)]
                simp
          _ = 0 := by simp [hPrev, hConj]

/-- Helper for Chapter04 Theorem 4.1.3: expanding the quadratic objective at a reference point
splits the value at `x + s` into the old value, the gradient pairing, and the quadratic
remainder `1 / 2 * sᵀ G s`. -/
theorem quadraticObjective_eq_at_reference_add_gradient_displacement
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (hG : G.IsSymm) (x s : Vector) :
    quadraticObjective G b c (x + s) =
      quadraticObjective G b c x +
        dotProduct ((gradient (quadraticObjective G b c) x : Vector)) s +
        (1 / 2 : ℝ) * dotProduct s (G.mulVec s) := by
  have hcross : dotProduct x (G.mulVec s) = dotProduct s (G.mulVec x) := by
    -- Symmetry lets us identify the two mixed terms in the quadratic expansion.
    simpa [hG.eq] using Matrix.dotProduct_transpose_mulVec G x s
  -- Expand `f (x + s)` directly and collapse the symmetric cross terms.
  rw [quadraticObjective_apply, quadraticObjective_apply, gradient_quadraticObjective G b c hG x]
  simp [dotProduct_add, dotProduct_comm, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
    hcross]
  ring

/-- Helper for Chapter04 Theorem 4.1.3: if a vector lies in the span of the first `m` search
directions, then the stage-`m` gradient is orthogonal to it. -/
theorem dotProduct_gradient_eq_zero_of_mem_prefix_span
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {m : ℕ} (hm : m ≤ n)
    {s : Vector}
    (hs : s ∈ Submodule.span ℝ (Set.range (fun j : Fin m ↦ A.d j))) :
    dotProduct (A.g m) s = 0 := by
  rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hs with ⟨β, hβ⟩
  have hβ' : (∑ j : Fin m, β j • A.d j).ofLp = s.ofLp := by
    simpa using congrArg (fun v : Vector ↦ v.ofLp) hβ
  have hsum : (∑ j : Fin m, β j • A.d j).ofLp = ∑ j : Fin m, β j • (A.d j).ofLp := by
    simp
  -- Expand the span element into coordinates and apply the textbook invariant termwise.
  calc
    dotProduct (A.g m) s = (A.g m).ofLp ⬝ᵥ ∑ j : Fin m, β j • (A.d j).ofLp := by
      rw [← hβ', hsum]
    _ = ∑ j : Fin m, β j * dotProduct (A.g m) (A.d j) := by
      simp [dotProduct_sum, dotProduct_smul]
    _ = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      simp [quadratic_gradient_orthogonal_to_previous_directions hMethod hm j.is_lt]

/-- Helper for Chapter04 Theorem 4.1.3: the iterate produced after stage `i` lies in the affine
search space generated by the initial point and the first `i + 1` directions. -/
theorem iterate_mem_conjugateDirectionSearchSpace
    {G : Matrix (Fin n) (Fin n) ℝ} {b : Vector} {c : ℝ}
    {A : GeneralConjugateDirectionMethod n (quadraticObjective G b c)}
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {i : ℕ} (hi : i < n) :
    A (i + 1) ∈ conjugateDirectionSearchSpace A.x0 A.d i := by
  induction i with
  | zero =>
      rcases hMethod.step hi with ⟨_, _, hUpdate⟩
      rw [mem_conjugateDirectionSearchSpace_iff]
      refine ⟨fun _ : Fin 1 ↦ A.α 0, ?_⟩
      -- The first accepted step is exactly `x₀ + α₀ d₀`.
      simpa [A.x_zero] using hUpdate
  | succ i ih =>
      have hPrev :
          A (i + 1) ∈ conjugateDirectionSearchSpace A.x0 A.d i :=
        ih (Nat.lt_of_succ_lt hi)
      rcases hMethod.step hi with ⟨_, _, hUpdate⟩
      rw [mem_conjugateDirectionSearchSpace_iff] at hPrev ⊢
      rcases hPrev with ⟨β, hβ⟩
      refine ⟨Fin.snoc β (A.α (i + 1)), ?_⟩
      -- Append the new step coefficient to the previously accumulated affine coordinates.
      simpa [hUpdate, hβ, Fin.sum_univ_castSucc, add_assoc] using
        (rfl : A.x0 + ∑ j : Fin (i + 2), (Fin.snoc β (A.α (i + 1)) j) • A.d j =
          A.x0 + ∑ j : Fin (i + 2), (Fin.snoc β (A.α (i + 1)) j) • A.d j)

/-- Chapter04 Theorem 4.1.3 (1): for a quadratic objective with positive-definite Hessian `G`,
the conjugate direction method has terminated by stage `n`, and the iterate `A n` is a global
minimizer after the first `n` exact line searches. -/
theorem conjugateDirectionMethod_terminates
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (A : GeneralConjugateDirectionMethod n (quadraticObjective G b c))
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) :
    A.terminatedAt n ∧ IsMinOn (quadraticObjective G b c) Set.univ (A n) := by
  have hGsymm : G.IsSymm := posDef_isSymm hMethod.posDef
  have hLinInd :
      LinearIndependent ℝ (fun i : Fin n ↦ (A.d i).ofLp) := by
    exact Matrix.linearIndependent_of_isConjugateFamily hMethod.posDef hMethod.conjugateFamily
  have hSpanUnderlying :
      Submodule.span ℝ (Set.range (fun i : Fin n ↦ (A.d i).ofLp)) = ⊤ := by
    refine hLinInd.span_eq_top_of_card_eq_finrank' ?_
    simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)).symm
  have hSpan :
      Submodule.span ℝ (Set.range (fun i : Fin n ↦ A.d i)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx' : x.ofLp ∈ Submodule.span ℝ (Set.range (fun i : Fin n ↦ (A.d i).ofLp)) := by
      rw [hSpanUnderlying]
      exact Submodule.mem_top
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hx' with ⟨β, hβ⟩
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mpr ⟨β, ?_⟩
    ext i
    simpa using congrArg (fun v : Fin n → ℝ ↦ v i) hβ
  have hgn_mem :
      A.g n ∈ Submodule.span ℝ (Set.range (fun i : Fin n ↦ A.d i)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hgn_orth :
      dotProduct (A.g n) (A.g n) = 0 :=
    dotProduct_gradient_eq_zero_of_mem_prefix_span hMethod le_rfl hgn_mem
  have hgn_zero : A.g n = 0 := by
    simpa using dotProduct_self_eq_zero.mp hgn_orth
  have hTerminate : A.terminatedAt n := by
    -- Vanishing gradient implies the norm-based stopping test at stage `n`.
    rw [A.terminatedAt_iff]
    simpa [hgn_zero] using (le_of_lt A.eps_pos)
  have hGlobalMin : IsMinOn (quadraticObjective G b c) Set.univ (A n) := by
    -- Every displacement from `A n` lies in the full span of the first `n` directions.
    simp [IsMinOn]
    intro x
    change quadraticObjective G b c (A n) ≤ quadraticObjective G b c x
    have hs_mem :
        x - A n ∈ Submodule.span ℝ (Set.range (fun i : Fin n ↦ A.d i)) := by
      rw [hSpan]
      exact Submodule.mem_top
    have hs_orth :
        dotProduct (A.g n) (x - A n) = 0 :=
      dotProduct_gradient_eq_zero_of_mem_prefix_span hMethod le_rfl hs_mem
    have hExpand :
        quadraticObjective G b c x =
          quadraticObjective G b c (A n) +
            dotProduct (A.g n) (x - A n) +
            (1 / 2 : ℝ) * dotProduct (x - A n) (G.mulVec (x - A n)) := by
      -- Expand the quadratic objective around the terminal iterate.
      simpa [sub_eq_add_neg, add_assoc, (A.hasGradientAt n).gradient] using
        quadraticObjective_eq_at_reference_add_gradient_displacement G b c hGsymm
          (A n) (x - A n)
    have hNonneg :
        0 ≤ (1 / 2 : ℝ) * dotProduct (x - A n) (G.mulVec (x - A n)) := by
      have hQuadNonneg :
          0 ≤ dotProduct (x - A n) (G.mulVec (x - A n)) :=
        hMethod.posDef.posSemidef.dotProduct_mulVec_nonneg (x - A n)
      nlinarith
    -- The linear term vanishes by span orthogonality, and the quadratic remainder is nonnegative.
    rw [hExpand]
    nlinarith [hNonneg, hs_orth]
  exact ⟨hTerminate, hGlobalMin⟩

/-- Chapter04 Theorem 4.1.3 (2): for each `i < n`, the iterate `x (i + 1)` minimizes the
quadratic objective on the affine space generated by the initial point `x₀ = A.x0` and the
directions `d 0, ..., d i`. -/
theorem conjugateDirectionMethod_iterate_isMinOn_searchSpace
    (G : Matrix (Fin n) (Fin n) ℝ) (b : Vector) (c : ℝ)
    (A : GeneralConjugateDirectionMethod n (quadraticObjective G b c))
    (hMethod : IsQuadraticConjugateDirectionMethod G b c A) {i : ℕ} (hi : i < n) :
    IsMinOn (quadraticObjective G b c) (conjugateDirectionSearchSpace A.x0 A.d i) (A (i + 1)) :=
  by
  have hGsymm : G.IsSymm := posDef_isSymm hMethod.posDef
  have hIterate :
      A (i + 1) ∈ conjugateDirectionSearchSpace A.x0 A.d i :=
    iterate_mem_conjugateDirectionSearchSpace hMethod hi
  -- Compare any search-space point to the accepted iterate by its displacement in the direction
  -- span, then use the quadratic expansion and the textbook orthogonality invariant.
  simp [IsMinOn]
  intro x hx
  change quadraticObjective G b c (A (i + 1)) ≤ quadraticObjective G b c x
  have hs_mem :
      x - A (i + 1) ∈ Submodule.span ℝ (Set.range (fun j : Fin (i + 1) ↦ A.d j)) := by
    simpa [conjugateDirectionSearchSpace, AffineSubspace.direction_mk'] using
      AffineSubspace.vsub_mem_direction hx hIterate
  have hs_orth :
      dotProduct (A.g (i + 1)) (x - A (i + 1)) = 0 :=
    dotProduct_gradient_eq_zero_of_mem_prefix_span hMethod (Nat.succ_le_of_lt hi) hs_mem
  have hExpand :
      quadraticObjective G b c x =
        quadraticObjective G b c (A (i + 1)) +
          dotProduct (A.g (i + 1)) (x - A (i + 1)) +
          (1 / 2 : ℝ) * dotProduct (x - A (i + 1)) (G.mulVec (x - A (i + 1))) := by
    -- Expand at the current iterate so the displacement lies in the known search-space span.
    simpa [sub_eq_add_neg, add_assoc, (A.hasGradientAt (i + 1)).gradient] using
      quadraticObjective_eq_at_reference_add_gradient_displacement G b c hGsymm
        (A (i + 1)) (x - A (i + 1))
  have hNonneg :
      0 ≤ (1 / 2 : ℝ) * dotProduct (x - A (i + 1)) (G.mulVec (x - A (i + 1))) := by
    have hQuadNonneg :
        0 ≤ dotProduct (x - A (i + 1)) (G.mulVec (x - A (i + 1))) :=
      hMethod.posDef.posSemidef.dotProduct_mulVec_nonneg (x - A (i + 1))
    nlinarith
  rw [hExpand]
  nlinarith [hNonneg, hs_orth]

end
