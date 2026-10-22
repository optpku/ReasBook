/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Matrix
open Matrix.PosDef

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.13 is `source-facing`: the genuine new content here is the affine-range
description of the conjugate of a positive-semidefinite quadratic together with the source-facing
range witness for the finite branch. The `core/canonical` owners for the quadratic itself and for
the Euclidean Fenchel conjugate on `ℝ^n` are already `quadratic_affine_function` and
`conjugate_function_primal` / `f∗`, so this file stays on the canonical
`EuclideanSpace ℝ (Fin n)` owner surface instead of introducing local identity-matrix instance
plumbing or a choice-built pseudoinverse wrapper. -/

recall quadratic_affine_function
recall conjugate_function_primal

/-- The affine set `b + Range(A)` appearing in the conjugate formula for a convex quadratic. -/
def quadratic_affine_range
    (A : Matrix (Fin n) (Fin n) ℝ) (b : E) : Set E :=
  {y | y - b ∈ LinearMap.range A.toEuclideanLin}

/-- Membership in `quadratic_affine_range A b` is equivalent to the translated vector `y - b`
lying in `Range(A)`. -/
@[simp] theorem mem_quadratic_affine_range_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (b y : E) :
    y ∈ quadratic_affine_range A b ↔ y - b ∈ LinearMap.range A.toEuclideanLin :=
  Iff.rfl

/-- Helper for Proposition 4.13: on Euclidean space, the inner product equals the coordinate dot
product. -/
private lemma inner_eq_dotProduct (y x : E) :
    inner ℝ y x = dotProduct y x := by
  -- On Euclidean space, the inner-product pairing is the coordinate dot product.
  simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct y x)

/-- Helper for Proposition 4.13: the `EReal` supremum of a real-valued range equals a point value
exactly when that point is a global maximizer. -/
lemma erealSsupCoeRangeEq_iff_isMaxOn (φ : E → ℝ) (x : E) :
    sSup (Set.range fun z : E ↦ ((φ z : ℝ) : EReal)) = (φ x : EReal) ↔
      IsMaxOn φ Set.univ x := by
  -- Translate the supremum identity into the pointwise order condition on all arguments.
  rw [isMaxOn_univ_iff]
  constructor
  · intro hs z
    have hz : ((φ z : ℝ) : EReal) ≤ sSup (Set.range fun w : E ↦ ((φ w : ℝ) : EReal)) :=
      le_sSup (Set.mem_range_self z)
    rw [hs] at hz
    exact EReal.coe_le_coe_iff.mp hz
  · intro hx
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨z, rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hx z)
    · exact le_sSup (Set.mem_range_self x)

/-- Helper for Proposition 4.13: along a kernel ray of `A`, the quadratic Fenchel objective
reduces to an affine function of the scalar parameter. -/
lemma quadraticAffineObjective_on_kernel_ray
    (A : Matrix (Fin n) (Fin n) ℝ) (b y v : E) (c α : ℝ) (hv : A *ᵥ v = 0) :
    dotProduct y (α • v) - quadratic_affine_function A b c (α • v) =
      α * dotProduct (y - b) v - c := by
  have hsub : b.ofLp - y.ofLp = -((y - b).ofLp) := by
    ext i
    simp
  -- Rewrite the objective once, then use the kernel hypothesis to kill the quadratic term.
  rw [quadraticAffineObjective_rewrite, Matrix.mulVec_smul, hv, smul_zero, dotProduct_zero,
    mul_zero, dotProduct_smul, hsub, neg_dotProduct]
  rw [show α • -((y - b).ofLp ⬝ᵥ v.ofLp) = α * -((y - b).ofLp ⬝ᵥ v.ofLp) by rfl]
  ring

/-- For a positive semidefinite real matrix, every `y ∈ Range(A)` has a unique preimage that also
lies in `Range(A)`. This is the source-facing range version of the Moore--Penrose inverse. -/
theorem quadratic_positive_semidefinite_range_preimage_existsUnique
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (y : E)
    (hy : y ∈ LinearMap.range A.toEuclideanLin) :
    ∃! x : E, x ∈ LinearMap.range A.toEuclideanLin ∧ A *ᵥ x = y := by
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.isHermitian
  rcases hy with ⟨x0, rfl⟩
  obtain ⟨xRange, hxRange, z, hzOrth, hx0⟩ :=
    (LinearMap.range A.toEuclideanLin).exists_add_mem_mem_orthogonal x0
  have hzKer : z ∈ LinearMap.ker A.toEuclideanLin := by
    simpa [hsymm.orthogonal_range] using hzOrth
  have hzZero : A.toEuclideanLin z = 0 := LinearMap.mem_ker.mp hzKer
  have hxRangeEq : A *ᵥ xRange.ofLp = (A.toEuclideanLin x0).ofLp := by
    have hxRangeEqEuclid : A.toEuclideanLin xRange = A.toEuclideanLin x0 := by
      -- The orthogonal complement component lies in the kernel, so only the range part matters.
      calc
        A.toEuclideanLin xRange = A.toEuclideanLin xRange + A.toEuclideanLin z := by
          rw [hzZero, add_zero]
        _ = A.toEuclideanLin (xRange + z) := by
          rw [LinearMap.map_add]
        _ = A.toEuclideanLin x0 := by
          rw [hx0]
    simpa using congrArg WithLp.ofLp hxRangeEqEuclid
  refine ⟨xRange, ⟨hxRange, hxRangeEq⟩, ?_⟩
  intro x hx
  have hdisj : Disjoint (LinearMap.range A.toEuclideanLin) (LinearMap.ker A.toEuclideanLin) := by
    simpa [hsymm.orthogonal_range] using (LinearMap.range A.toEuclideanLin).orthogonal_disjoint
  have hsubRange : x - xRange ∈ LinearMap.range A.toEuclideanLin := by
    exact sub_mem hx.1 hxRange
  have hsubKer : x - xRange ∈ LinearMap.ker A.toEuclideanLin := by
    rw [LinearMap.mem_ker]
    -- Equal images force the difference to lie in the kernel.
    calc
      A.toEuclideanLin (x - xRange) = A.toEuclideanLin x - A.toEuclideanLin xRange := by
        rw [LinearMap.map_sub]
      _ = 0 := by
        ext i
        simp [hx.2, hxRangeEq]
  have hsubZero : x - xRange = 0 := by
    have hsubMem :
        x - xRange ∈ LinearMap.range A.toEuclideanLin ⊓ LinearMap.ker A.toEuclideanLin :=
      ⟨hsubRange, hsubKer⟩
    have hbot :
        LinearMap.range A.toEuclideanLin ⊓ LinearMap.ker A.toEuclideanLin = ⊥ :=
      disjoint_iff.mp hdisj
    have hbotMem : x - xRange ∈ (⊥ : Submodule ℝ E) := by
      simpa [hbot] using hsubMem
    simpa using hbotMem
  exact sub_eq_zero.mp hsubZero

-- Proof sketch: rewrite `f∗ y` as the supremum of the concave quadratic
-- `x ↦ -1 / 2 xᵀ A x + (y - b)ᵀ x - c`. If `A *ᵥ x = y - b` with `x ∈ Range(A)`, then the
-- stationarity equation holds on the affine range branch, so evaluating the objective at that
-- witness gives the supremum value.
/-- On the affine-range branch of Proposition 4.13, any witness `x ∈ Range(A)` satisfying
`A *ᵥ x = y - b` realizes the finite conjugate value. -/
theorem convex_quadratic_function_conjugate_eq_of_mem_quadratic_affine_range
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (b y x : E) (c : ℝ)
    (hx : x ∈ LinearMap.range A.toEuclideanLin) (hAx : A *ᵥ x = y - b) :
    ((fun z : E ↦ (quadratic_affine_function A b c z : EReal))∗) y =
      (((1 / 2 : ℝ) * dotProduct (y - b) x - c : ℝ) : EReal) := by
  have _hx : x ∈ LinearMap.range A.toEuclideanLin := hx
  let ψ : E → ℝ :=
    fun z ↦ (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c
  let φ : E → ℝ :=
    fun z ↦ inner ℝ y z - quadratic_affine_function A b c z
  have hmaxPsi : IsMaxOn ψ Set.univ x := by
    rw [isMaxOn_univ_iff]
    intro z
    have hnonneg : 0 ≤ dotProduct (z - x) (A *ᵥ (z - x)) := by
      simpa using hA.dotProduct_mulVec_nonneg (z - x)
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * dotProduct (z - x) (A *ᵥ (z - x)) := by
      nlinarith
    have hsquare :=
      rewrittenQuadraticObjective_completeSquare A b y c x z hA.isHermitian hAx
    -- Completing the square reduces maximality to PSD nonnegativity of the remainder.
    have hlePsi : ψ z ≤ ψ x := by
      have hrewrite :
          ψ z = ψ x - (1 / 2 : ℝ) * dotProduct (z - x) (A *ᵥ (z - x)) := by
        simpa [ψ] using hsquare
      calc
        ψ z = ψ x - (1 / 2 : ℝ) * dotProduct (z - x) (A *ᵥ (z - x)) := hrewrite
        _ ≤ ψ x := by
          nlinarith
    exact hlePsi
  have hmax : IsMaxOn φ Set.univ x := by
    rw [isMaxOn_univ_iff] at hmaxPsi ⊢
    intro z
    have hφz : φ z = ψ z := by
      dsimp [φ, ψ]
      rw [inner_eq_dotProduct y z, quadraticAffineObjective_rewrite]
    have hφx : φ x = ψ x := by
      dsimp [φ, ψ]
      rw [inner_eq_dotProduct y x, quadraticAffineObjective_rewrite]
    rw [hφz, hφx]
    exact hmaxPsi z
  have hsup :
      sSup (Set.range fun z : E ↦
        (((inner ℝ y z : ℝ) : EReal) -
          (quadratic_affine_function A b c z : EReal))) =
        (φ x : EReal) := by
    -- The primal conjugate is the supremum of the affine-minus-quadratic objective.
    simpa [φ, EReal.coe_sub] using
      (erealSsupCoeRangeEq_iff_isMaxOn φ x).2 hmax
  have hvalue : φ x =
        (1 / 2 : ℝ) * dotProduct (y - b) x - c := by
    have hsub : b.ofLp - y.ofLp = -((y - b).ofLp) := by
      ext i
      simp
    -- Substitute the stationarity equation to collapse the quadratic expression.
    dsimp [φ]
    rw [inner_eq_dotProduct y x, quadraticAffineObjective_rewrite, hAx, hsub,
      neg_dotProduct, dotProduct_comm x (y - b)]
    have hd : (y.ofLp - b.ofLp) ⬝ᵥ x.ofLp = (y - b).ofLp ⬝ᵥ x.ofLp := rfl
    rw [hd]
    ring_nf
  -- Evaluate the primal conjugate by identifying the supremum with the value at the maximizer.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  calc
    sSup (Set.range fun z : E ↦
        (((inner ℝ y z : ℝ) : EReal) -
          (quadratic_affine_function A b c z : EReal))) =
        (φ x : EReal) :=
      hsup
    _ = (((1 / 2 : ℝ) * dotProduct (y - b) x - c : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hvalue

-- Proof sketch: if `y - b ∉ Range(A)`, choose a null vector with positive pairing against
-- `y - b`; along its scalar multiples the Fenchel objective tends to `∞`, so the supremum is `⊤`.
/-- Outside the affine set `b + Range(A)`, the conjugate of the positive-semidefinite quadratic is
`∞`. -/
theorem convex_quadratic_function_conjugate_eq_top_of_not_mem_quadratic_affine_range
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (b y : E) (c : ℝ)
    (hy : y ∉ quadratic_affine_range A b) :
    ((fun z : E ↦ (quadratic_affine_function A b c z : EReal))∗) y = ⊤ := by
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.isHermitian
  have hyRange : y - b ∉ LinearMap.range A.toEuclideanLin := by
    simpa [mem_quadratic_affine_range_iff] using hy
  obtain ⟨u, huRange, z, hzOrth, hydecomp⟩ :=
    (LinearMap.range A.toEuclideanLin).exists_add_mem_mem_orthogonal (y - b)
  have hzKer : z ∈ LinearMap.ker A.toEuclideanLin := by
    simpa [hsymm.orthogonal_range] using hzOrth
  have hAz : A *ᵥ z.ofLp = 0 := by
    simpa using congrArg WithLp.ofLp (LinearMap.mem_ker.mp hzKer)
  have hzNe : z ≠ 0 := by
    intro hzZero
    apply hyRange
    have hyEq : y - b = u := by
      simpa [hzZero] using hydecomp
    exact hyEq ▸ huRange
  have huz : dotProduct u z = 0 := by
    have huzInner : inner ℝ u z = 0 :=
      Submodule.inner_right_of_mem_orthogonal huRange hzOrth
    rw [inner_eq_dotProduct] at huzInner
    exact huzInner
  have hyz : dotProduct (y - b) z = dotProduct z z := by
    -- The decomposition into range and orthogonal kernel parts isolates the positive slope.
    calc
      dotProduct (y - b) z = dotProduct (u + z) z := by rw [hydecomp]
      _ = dotProduct u z + dotProduct z z := by
        simp [add_dotProduct]
      _ = dotProduct z z := by rw [huz, zero_add]
  have hp : 0 < dotProduct (y - b) z := by
    have hzNonneg : 0 ≤ dotProduct z z := by
      simpa using (dotProduct_self_star_nonneg (z.ofLp : Fin n → ℝ))
    have hzNeZero : dotProduct z z ≠ 0 := by
      intro hzZero
      apply hzNe
      ext i
      simpa using congrArg (fun v : Fin n → ℝ ↦ v i) (dotProduct_self_eq_zero.mp hzZero)
    have hzPos : 0 < dotProduct z z := lt_of_le_of_ne hzNonneg hzNeZero.symm
    rwa [hyz]
  rw [conjugate_function_primal_apply, conjugate_function_apply, EReal.eq_top_iff_forall_lt]
  intro r
  let α : ℝ := (r + c + 1) / dotProduct (y - b) z
  have hα :
      α * dotProduct (y - b) z = r + c + 1 := by
    have hd : dotProduct (y - b) z ≠ 0 := hp.ne'
    calc
      α * dotProduct (y - b) z =
          ((r + c + 1) / dotProduct (y - b) z) * dotProduct (y - b) z := by
        rfl
      _ = r + c + 1 := by
        field_simp [hd]
  have hlt : r < α * dotProduct (y - b) z - c := by
    rw [hα]
    linarith
  have hobj :
      dotProduct y (α • z) - quadratic_affine_function A b c (α • z) =
        α * dotProduct (y - b) z - c := by
    -- Along a kernel ray, the objective becomes affine with positive slope.
    exact quadraticAffineObjective_on_kernel_ray A b y z c α hAz
  have hltE :
      (r : EReal) <
        (((dotProduct y (α • z) - quadratic_affine_function A b c (α • z) : ℝ) : EReal)) := by
    refine EReal.coe_lt_coe_iff.mpr ?_
    rw [hobj]
    exact hlt
  calc
    (r : EReal) <
        (((dotProduct y (α • z) - quadratic_affine_function A b c (α • z) : ℝ) : EReal)) :=
      hltE
    _ = (((inner ℝ y (α • z) : ℝ) : EReal) -
          (quadratic_affine_function A b c (α • z) : EReal)) := by
      rw [EReal.coe_sub, inner_eq_dotProduct y (α • z)]
      simp
    _ ≤ sSup (Set.range fun x : E ↦
        (((inner ℝ y x : ℝ) : EReal) -
          (quadratic_affine_function A b c x : EReal))) := by
      exact le_sSup ⟨α • z, rfl⟩

-- Proof sketch: rewrite the conjugate as the supremum of the concave quadratic
-- `x ↦ -1 / 2 xᵀ A x + (y - b)ᵀ x - c`. On the affine range branch, choose any witness
-- `x ∈ Range(A)` with `A *ᵥ x = y - b`; the uniqueness theorem above makes the resulting value
-- canonical. Off the affine range, the companion theorem gives the `∞` branch.
/-- Proposition 4.13: for the convex quadratic `f(x) = 1/2 xᵀ A x + bᵀ x + c` with `A`
positive semidefinite, the Fenchel conjugate equals `1/2 (y - b)ᵀ A† (y - b) - c` on
`b + Range(A)` and equals `∞` outside that affine range. On the finite branch, the factor
`A† (y - b)` is represented source-faithfully by any witness `x ∈ Range(A)` satisfying
`A *ᵥ x = y - b`. -/
theorem convex_quadratic_function_conjugate_eq
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (b y : E) (c : ℝ) :
    (y ∈ quadratic_affine_range A b →
      ∃ x : E,
        x ∈ LinearMap.range A.toEuclideanLin ∧
          A *ᵥ x = y - b ∧
          ((fun z : E ↦ (quadratic_affine_function A b c z : EReal))∗) y =
            (((1 / 2 : ℝ) * dotProduct (y - b) x - c : ℝ) : EReal)) ∧
      (y ∉ quadratic_affine_range A b →
        ((fun z : E ↦ (quadratic_affine_function A b c z : EReal))∗) y = ⊤) := by
  constructor
  · intro hy
    have hyRange : y - b ∈ LinearMap.range A.toEuclideanLin := by
      simpa [mem_quadratic_affine_range_iff] using hy
    rcases
        quadratic_positive_semidefinite_range_preimage_existsUnique A hA (y - b) hyRange with
      ⟨x, hx, _⟩
    refine ⟨x, hx.1, hx.2, ?_⟩
    -- Reuse the finite affine-range branch at the selected range witness.
    exact
      convex_quadratic_function_conjugate_eq_of_mem_quadratic_affine_range
        A hA b y x c hx.1 hx.2
  · intro hy
    -- Outside the affine range, the kernel-ray argument gives the `∞` branch directly.
    exact
      convex_quadratic_function_conjugate_eq_top_of_not_mem_quadratic_affine_range
        A hA b y c hy

end
