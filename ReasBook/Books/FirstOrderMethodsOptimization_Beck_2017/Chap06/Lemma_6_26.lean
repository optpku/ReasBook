/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_13
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_24
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Matrix
open scoped RealInnerProductSpace
open WithLp (toLp ofLp)

/- Lemma 6.26 is `source-facing`: it records explicit singleton formulas for the Chapter 6
projection owner `P[C]` from Theorem 6.24 on five standard closed convex subsets of `ℝ^n`. The
source formulas are Euclidean orthogonal projections, so the coordinate cases are stated on
`EuclideanSpace ℝ ι` and expose coordinates through `ofLp`; raw function spaces `ι → ℝ` carry
Lean's default `Pi` norm and would state a different projection problem. The item is split into
five atomic projection identities rather than packaged into one conjunction-valued statement. For
the box case, the source-facing owner is Chapter 1's `Box[ℓ,u]` pulled back along `ofLp`; the
pointwise interval `Set.Icc` is only the canonical finite-endpoint view, obtained through
`box_eq_Icc`, while the scalar clamping still uses the owner-level interval projection
`Set.projIcc`. The affine-system special case reuses the Chapter 2 owner
`affine_linear_constraint_set`, again pulled back along `ofLp` to the Euclidean owner. -/

section

variable {ι : Type*} [Fintype ι]

local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι

/-- Helper for Lemma 6.26: the orthant truncation residual has nonpositive scalar product with any
nonnegative scalar displacement. -/
lemma posPart_sub_mul_nonpos_of_nonneg (x y : ℝ) (hy : 0 ≤ y) :
    (x - x⁺) * (y - x⁺) ≤ 0 := by
  by_cases hx : 0 ≤ x
  · rw [posPart_eq_self.2 hx]
    simp
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [posPart_eq_zero.2 hx']
    simpa using mul_nonpos_of_nonpos_of_nonneg hx' hy

/-- Helper for Lemma 6.26: the scalar interval projection residual has nonpositive product with
every feasible scalar direction in the interval. -/
lemma projIcc_sub_mul_nonpos_of_mem_Icc
    (l u x y : ℝ) (hlu : l ≤ u) (hy : y ∈ Set.Icc l u) :
    (x - ((Set.projIcc l u hlu x : Set.Icc l u) : ℝ)) *
      (y - ((Set.projIcc l u hlu x : Set.Icc l u) : ℝ)) ≤ 0 := by
  by_cases hxl : x ≤ l
  · rw [Set.projIcc_of_le_left hlu hxl]
    simp
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxl) (sub_nonneg.mpr hy.1)
  · by_cases hux : u ≤ x
    · rw [Set.projIcc_of_right_le hlu hux]
      simp
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hux) (sub_nonpos.mpr hy.2)
    · have hx_mem : x ∈ Set.Icc l u := by
        exact ⟨le_of_not_ge hxl, le_of_not_ge hux⟩
      rw [Set.projIcc_of_mem (h := hlu) hx_mem]
      simp

-- Proof sketch: minimize the Euclidean distance to `x` coordinatewise over the orthant. Each
-- scalar minimization over `[0, ∞)` is solved by truncating `x i` below at `0`, which yields the
-- coordinatewise positive part.
/-- Lemma 6.26 (1): the orthogonal projection onto the nonnegative orthant in `ℝ^n`, represented
on the Euclidean owner `EuclideanSpace ℝ ι`, is the singleton containing the coordinatewise
positive part of `x`. -/
lemma projection_mapping_nonnegativeOrthant_eq_singleton_coordinatewisePosPart (x : E) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' Set.Ici (0 : X))] x =
      {WithLp.toLp (p := (2 : ENNReal)) x.ofLp⁺} :=
  by
  let C : Set E := ((fun y : E ↦ y.ofLp) ⁻¹' Set.Ici (0 : X))
  let p : E := WithLp.toLp (p := (2 : ENNReal)) x.ofLp⁺
  have hconvexX : Convex ℝ (Set.Ici (0 : X)) := convex_Ici (0 : X)
  have hconvex : Convex ℝ C := by
    simpa [C] using
      hconvexX.linear_preimage ((WithLp.linearEquiv (2 : ENNReal) ℝ X).toLinearMap)
  have hp_mem : p ∈ C := by
    -- The coordinatewise positive part is feasible because every coordinate is nonnegative.
    simpa [C, p, Pi.le_def] using fun i ↦ posPart_nonneg (x.ofLp i)
  have hp_inner :
      ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0 := by
    intro y hy
    have hy_nonneg : ∀ i, 0 ≤ y.ofLp i := by
      simpa [C, Pi.le_def] using hy
    -- Route correction: package the coordinatewise sign split through the Hilbert variational
    -- criterion instead of re-summing squared distances by hand.
    calc
      inner ℝ (x - p) (y - p) =
          ∑ i, (x.ofLp i - x.ofLp⁺ i) * (y.ofLp i - x.ofLp⁺ i) := by
            change
              inner ℝ
                  (WithLp.toLp (p := (2 : ENNReal)) (x.ofLp - x.ofLp⁺))
                  (WithLp.toLp (p := (2 : ENNReal)) (y.ofLp - x.ofLp⁺)) =
                _
            simpa [dotProduct, mul_comm, mul_left_comm, mul_assoc] using
              (EuclideanSpace.inner_toLp_toLp (x.ofLp - x.ofLp⁺) (y.ofLp - x.ofLp⁺))
      _ ≤ 0 := by
        exact Finset.sum_nonpos fun i _ ↦
          posPart_sub_mul_nonpos_of_nonneg (x.ofLp i) (y.ofLp i) (hy_nonneg i)
  have hp_proj : p ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hp_mem, ?_⟩
    intro y hy
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hy_inner := hp_inner y hy
      have hdecomp : ‖x - y‖ ^ 2 =
          ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
        have hxy : x - y = (x - p) - (y - p) := by
          abel_nf
        simpa using (by
          rw [hxy, @norm_sub_sq ℝ E _ _] :
            ‖x - y‖ ^ 2 =
              ‖x - p‖ ^ 2 - 2 * RCLike.re (inner ℝ (x - p) (y - p)) + ‖y - p‖ ^ 2)
      calc
        ‖x - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) := by
          linarith
        _ ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
          nlinarith [sq_nonneg ‖y - p‖]
        _ = ‖x - y‖ ^ 2 := by
          rw [hdecomp]
    have hnorm_le : ‖x - p‖ ≤ ‖x - y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    simpa [norm_sub_rev] using hnorm_le
  have hsub : (P[C] x).Subsingleton :=
    projection_mapping_subsingleton C hconvex x
  simpa [C, p] using hsub.eq_singleton_of_mem hp_proj

-- Proof sketch: the squared-distance objective over the box `Box[ℓ,u]` separates by coordinates.
-- each coordinate, the scalar minimizer is the canonical interval projection `Set.projIcc` of
-- `x i` to `[l i, u i]`, so the projected point is obtained by applying `Set.projIcc`
-- coordinatewise.
/-- Lemma 6.26 (2): for a real coordinate box, the orthogonal projection is the singleton given by
the coordinatewise interval projection `Set.projIcc` of `x` onto `[l i, u i]` in the finite
Euclidean owner `EuclideanSpace ℝ ι`. -/
lemma projection_mapping_box_eq_singleton_coordinatewiseClamp
    (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i) (x : E) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' Box[(fun i ↦ (l i : EReal)), fun i ↦ (u i : EReal)])] x =
      {WithLp.toLp (p := (2 : ENNReal))
        (fun i ↦ ((Set.projIcc (l i) (u i) (hlu i) (x.ofLp i) : Set.Icc (l i) (u i)) : ℝ))} :=
  by
  let C : Set E :=
    ((fun y : E ↦ y.ofLp) ⁻¹' Box[(fun i ↦ (l i : EReal)), fun i ↦ (u i : EReal)])
  let p : E := WithLp.toLp (p := (2 : ENNReal))
    (fun i ↦ ((Set.projIcc (l i) (u i) (hlu i) (x.ofLp i) : Set.Icc (l i) (u i)) : ℝ))
  have hconvexX :
      Convex ℝ (Box[(fun i ↦ (l i : EReal)), fun i ↦ (u i : EReal)] : Set X) := by
    simpa [box_eq_Icc] using (convex_Icc l u)
  have hconvex : Convex ℝ C := by
    simpa [C] using
      hconvexX.linear_preimage ((WithLp.linearEquiv (2 : ENNReal) ℝ X).toLinearMap)
  have hp_mem_Icc : p.ofLp ∈ Set.Icc l u := by
    -- Every coordinate clamp lies in its defining interval.
    refine ⟨?_, ?_⟩
    · intro i
      exact (Set.projIcc (l i) (u i) (hlu i) (x.ofLp i)).2.1
    · intro i
      exact (Set.projIcc (l i) (u i) (hlu i) (x.ofLp i)).2.2
  have hp_mem : p ∈ C := by
    simpa [C, box_eq_Icc] using hp_mem_Icc
  have hp_inner :
      ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0 := by
    intro y hy
    have hy_mem_Icc : y.ofLp ∈ Set.Icc l u := by
      simpa [C, box_eq_Icc] using hy
    have hy_mem : ∀ i, y.ofLp i ∈ Set.Icc (l i) (u i) := by
      simpa [Set.mem_Icc, Pi.le_def, forall_and] using hy_mem_Icc
    -- Compare each coordinate against the scalar interval clamp and sum the resulting
    -- nonpositive products.
    calc
      inner ℝ (x - p) (y - p) =
          ∑ i,
            (x.ofLp i -
                ((Set.projIcc (l i) (u i) (hlu i) (x.ofLp i) : Set.Icc (l i) (u i)) : ℝ)) *
              (y.ofLp i -
                ((Set.projIcc (l i) (u i) (hlu i) (x.ofLp i) : Set.Icc (l i) (u i)) : ℝ)) := by
            change
              inner ℝ
                  (WithLp.toLp (p := (2 : ENNReal)) (x.ofLp - p.ofLp))
                  (WithLp.toLp (p := (2 : ENNReal)) (y.ofLp - p.ofLp)) =
                _
            simpa [dotProduct, mul_comm, mul_left_comm, mul_assoc] using
              (EuclideanSpace.inner_toLp_toLp (x.ofLp - p.ofLp) (y.ofLp - p.ofLp))
      _ ≤ 0 := by
        exact Finset.sum_nonpos fun i _ ↦
          projIcc_sub_mul_nonpos_of_mem_Icc
            (l i) (u i) (x.ofLp i) (y.ofLp i) (hlu i) (hy_mem i)
  have hp_proj : p ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hp_mem, ?_⟩
    intro y hy
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hy_inner := hp_inner y hy
      have hdecomp : ‖x - y‖ ^ 2 =
          ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
        have hxy : x - y = (x - p) - (y - p) := by
          abel_nf
        simpa using (by
          rw [hxy, @norm_sub_sq ℝ E _ _] :
            ‖x - y‖ ^ 2 =
              ‖x - p‖ ^ 2 - 2 * RCLike.re (inner ℝ (x - p) (y - p)) + ‖y - p‖ ^ 2)
      calc
        ‖x - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) := by
          linarith
        _ ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
          nlinarith [sq_nonneg ‖y - p‖]
        _ = ‖x - y‖ ^ 2 := by
          rw [hdecomp]
    have hnorm_le : ‖x - p‖ ≤ ‖x - y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    simpa [norm_sub_rev] using hnorm_le
  have hsub : (P[C] x).Subsingleton :=
    projection_mapping_subsingleton C hconvex x
  simpa [C, p] using hsub.eq_singleton_of_mem hp_proj

/-- The pointwise-interval view of Lemma 6.26 (2), obtained from `Box[ℓ,u] = Set.Icc ℓ u`. -/
lemma projection_mapping_Icc_eq_singleton_coordinatewiseClamp
    (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i) (x : E) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' Set.Icc l u)] x =
      {WithLp.toLp (p := (2 : ENNReal))
        (fun i ↦ ((Set.projIcc (l i) (u i) (hlu i) (x.ofLp i) : Set.Icc (l i) (u i)) : ℝ))} := by
  simpa [box_eq_Icc] using
    projection_mapping_box_eq_singleton_coordinatewiseClamp l u hlu x

end

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "X" => κ → ℝ
local notation "E" => EuclideanSpace ℝ κ
local notation "F" => ι → ℝ
local instance instDecidableEqLemma626 : DecidableEq ι := Classical.decEq ι

/-- Helper for Lemma 6.26: the affine correction point satisfies the linear equations
`A y = b`. -/
lemma affine_correction_mulVec_eq
    (A : Matrix ι κ ℝ) (hAA : Invertible (A * Aᵀ)) (b : F) (x : X) :
    A *ᵥ (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) = b := by
  letI : Invertible (A * Aᵀ) := hAA
  -- Solve the stationarity system by multiplying the residual with `A`.
  calc
    A *ᵥ (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) =
        A *ᵥ x - A *ᵥ (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) := by
          rw [Matrix.mulVec_sub]
    _ = A *ᵥ x - ((A * Aᵀ) *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) := by
          rw [Matrix.mulVec_mulVec]
    _ = A *ᵥ x - (A *ᵥ x - b) := by
          have hmul : A * Aᵀ * (A * Aᵀ)⁻¹ = (1 : Matrix ι ι ℝ) := by
            simpa using (mul_inv_cancel_of_invertible (A * Aᵀ))
          rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    _ = b := by
          abel_nf

/-- Helper for Lemma 6.26: the affine-correction residual lies in the row space of `A`, hence it
is orthogonal to every feasible displacement. -/
lemma affine_correction_residual_orthogonal_to_feasible_directions
    (A : Matrix ι κ ℝ) (hAA : Invertible (A * Aᵀ)) (b : F) (x y : X)
    (hy : A *ᵥ y = b) :
    dotProduct
      (y - (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))))
      (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) = 0 := by
  letI : Invertible (A * Aᵀ) := hAA
  have hp : A *ᵥ (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) = b := by
    simpa using affine_correction_mulVec_eq A hAA b x
  -- Feasible displacements lie in `ker A`, while the residual is in `range Aᵀ`.
  calc
    dotProduct
        (y - (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))))
        (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b))) =
          (y - (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b)))) ᵥ* Aᵀ ⬝ᵥ
            (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b)) := by
            rw [Matrix.dotProduct_mulVec]
    _ = A *ᵥ (y - (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b)))) ⬝ᵥ
          (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b)) := by
            rw [Matrix.vecMul_transpose]
    _ = 0 := by
          have hker :
              A *ᵥ (y - (x - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x - b)))) = 0 := by
            rw [Matrix.mulVec_sub, hy, hp, sub_self]
          rw [hker]
          simp

-- Proof sketch: solve the equality-constrained quadratic minimization by Lagrange multipliers.
-- The stationarity equation gives the affine correction by `Aᵀ ν`, and solving
-- `(A Aᵀ) ν = A x - b` yields the displayed matrix formula because `A Aᵀ` is invertible.
/-- Lemma 6.26 (3): if `A Aᵀ` is invertible, then the orthogonal projection onto the affine set
`affine_linear_constraint_set A b = {y : A y = b}` is the singleton given by the standard affine
correction
`x - Aᵀ (A Aᵀ)⁻¹ (A x - b)`. -/
lemma projection_mapping_affine_linear_constraint_set_eq_singleton_affineCorrection
    (A : Matrix ι κ ℝ) (hAA : Invertible (A * Aᵀ)) (b : F) (x : E) :
    P[((fun y : E ↦ y.ofLp) ⁻¹' affine_linear_constraint_set A b)] x =
      {WithLp.toLp (p := (2 : ENNReal))
        (x.ofLp - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b)))} :=
  by
  let C : Set E := ((fun y : E ↦ y.ofLp) ⁻¹' affine_linear_constraint_set A b)
  let p0 : X := x.ofLp - Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b))
  let p : E := WithLp.toLp (p := (2 : ENNReal)) p0
  have hconvexX : Convex ℝ (affine_linear_constraint_set A b : Set X) := by
    simpa [affine_linear_constraint_set] using
      (convex_singleton b).linear_preimage A.mulVecLin
  have hconvex : Convex ℝ C := by
    simpa [C] using
      hconvexX.linear_preimage ((WithLp.linearEquiv (2 : ENNReal) ℝ X).toLinearMap)
  have hp_memX : p0 ∈ affine_linear_constraint_set A b := by
    -- The explicit correction enforces the affine equations exactly.
    simpa [affine_linear_constraint_set, p0] using
      affine_correction_mulVec_eq A hAA b x.ofLp
  have hp_mem : p ∈ C := by
    simpa [C, p, p0] using hp_memX
  have hp_inner :
      ∀ y ∈ C, inner ℝ (x - p) (y - p) ≤ 0 := by
    intro y hy
    have hy_feasible : A *ᵥ y.ofLp = b := by
      simpa [C, affine_linear_constraint_set] using hy
    have horth :
        dotProduct (y.ofLp - p0) (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b))) = 0 := by
      simpa [p0] using
        affine_correction_residual_orthogonal_to_feasible_directions
          A hAA b x.ofLp y.ofLp hy_feasible
    have hx_sub :
        x - p = WithLp.toLp (p := (2 : ENNReal))
          (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b))) := by
      ext i
      simp [p, p0]
    have hy_sub :
        y - p = WithLp.toLp (p := (2 : ENNReal)) (y.ofLp - p0) := by
      ext i
      simp [p, p0]
    -- Translate the row-space/kernel orthogonality back to the Euclidean inner product.
    calc
      inner ℝ (x - p) (y - p) =
          dotProduct (y.ofLp - p0) (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b))) := by
            rw [hx_sub, hy_sub]
            simpa [dotProduct] using
              (EuclideanSpace.inner_toLp_toLp
                (Aᵀ *ᵥ (((A * Aᵀ)⁻¹) *ᵥ (A *ᵥ x.ofLp - b)))
                (y.ofLp - p0))
      _ = 0 := horth
      _ ≤ 0 := le_rfl
  have hp_proj : p ∈ P[C] x := by
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hp_mem, ?_⟩
    intro y hy
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hy_inner := hp_inner y hy
      have hdecomp : ‖x - y‖ ^ 2 =
          ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
        have hxy : x - y = (x - p) - (y - p) := by
          abel_nf
        simpa using (by
          rw [hxy, @norm_sub_sq ℝ E _ _] :
            ‖x - y‖ ^ 2 =
              ‖x - p‖ ^ 2 - 2 * RCLike.re (inner ℝ (x - p) (y - p)) + ‖y - p‖ ^ 2)
      calc
        ‖x - p‖ ^ 2 ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) := by
          linarith
        _ ≤ ‖x - p‖ ^ 2 - 2 * inner ℝ (x - p) (y - p) + ‖y - p‖ ^ 2 := by
          nlinarith [sq_nonneg ‖y - p‖]
        _ = ‖x - y‖ ^ 2 := by
          rw [hdecomp]
    have hnorm_le : ‖x - p‖ ≤ ‖x - y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    simpa [norm_sub_rev] using hnorm_le
  have hsub : (P[C] x).Subsingleton :=
    projection_mapping_subsingleton C hconvex x
  simpa [C, p, p0] using hsub.eq_singleton_of_mem hp_proj

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 6.26: outside a closed ball, the radial truncation point lies on the ball. -/
lemma radial_retraction_mem_closedBall_of_lt_norm
    (c x : E) (r : ℝ) (hr : 0 ≤ r) (hx : r < ‖x - c‖) :
    c + (r / ‖x - c‖) • (x - c) ∈ Metric.closedBall c r := by
  have hnorm_pos : 0 < ‖x - c‖ := by
    linarith
  -- Compute the radius of the radial truncation directly from the scalar factor.
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖(c + (r / ‖x - c‖) • (x - c)) - c‖ = ‖(r / ‖x - c‖) • (x - c)‖ := by
      abel_nf
    _ = |r / ‖x - c‖| * ‖x - c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = (r / ‖x - c‖) * ‖x - c‖ := by
      rw [abs_of_nonneg]
      exact div_nonneg hr hnorm_pos.le
    _ = r := by
      field_simp [hnorm_pos.ne']
  exact le_rfl

/-- Helper for Lemma 6.26: outside a closed ball, radial truncation is at least as close as any
other feasible point. -/
lemma radial_retraction_distance_le_of_mem_closedBall
    (c x y : E) (r : ℝ) (hr : 0 ≤ r) (hy : y ∈ Metric.closedBall c r) (hx : r < ‖x - c‖) :
    ‖x - (c + (r / ‖x - c‖) • (x - c))‖ ≤ ‖x - y‖ := by
  have hnorm_pos : 0 < ‖x - c‖ := by
    linarith
  have hxp : ‖x - (c + (r / ‖x - c‖) • (x - c))‖ = ‖x - c‖ - r := by
    have hrepr :
        x - (c + (r / ‖x - c‖) • (x - c)) = (1 - r / ‖x - c‖) • (x - c) := by
      calc
        x - (c + (r / ‖x - c‖) • (x - c)) = (x - c) - (r / ‖x - c‖) • (x - c) := by
          abel_nf
        _ = (1 - r / ‖x - c‖) • (x - c) := by
          calc
            (x - c) - (r / ‖x - c‖) • (x - c) =
                (1 : ℝ) • (x - c) + (-(r / ‖x - c‖)) • (x - c) := by
                  rw [one_smul, sub_eq_add_neg, neg_smul]
            _ = (1 + -(r / ‖x - c‖)) • (x - c) := by
              rw [← add_smul]
            _ = (1 - r / ‖x - c‖) • (x - c) := by
              ring_nf
    have habs : |1 - r / ‖x - c‖| = 1 - r / ‖x - c‖ := by
      apply abs_of_nonneg
      have hdiv : r / ‖x - c‖ < 1 := by
        rw [div_lt_iff₀ hnorm_pos]
        linarith
      linarith
    -- The correction stays on the ray through `x - c`, so its norm collapses to a scalar identity.
    rw [hrepr, norm_smul, Real.norm_eq_abs, habs]
    have hscalar : (1 - r / ‖x - c‖) * ‖x - c‖ = ‖x - c‖ - r := by
      field_simp [hnorm_pos.ne']
    simpa using hscalar
  have hy_le : ‖y - c‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm, norm_sub_rev] using hy
  have htriangle : ‖x - c‖ ≤ ‖x - y‖ + ‖y - c‖ := by
    -- Compare `x - c` with the decomposition through the feasible competitor `y`.
    calc
      ‖x - c‖ = ‖(x - y) + (y - c)‖ := by
        abel_nf
      _ ≤ ‖x - y‖ + ‖y - c‖ := norm_add_le _ _
  have hlower : ‖x - c‖ - r ≤ ‖x - y‖ := by
    linarith
  rw [hxp]
  exact hlower

-- Proof sketch: split into the two cases `‖x - c‖ ≤ r` and `‖x - c‖ > r`. Inside the ball, the
-- minimizer is `x`; outside, the radial point on the sphere minimizes the distance by the reverse
-- triangle inequality, and strict convexity of the inner-product norm gives uniqueness. These two
-- cases combine into the displayed `max` formula.
/-- Lemma 6.26 (4): in a real inner-product space, the orthogonal projection onto a closed ball of
nonnegative radius is the singleton given by radial truncation toward the center. -/
lemma projection_mapping_closedBall_eq_singleton_radialRetraction
    (c x : E) (r : ℝ) (hr : 0 ≤ r) :
    P[Metric.closedBall c r] x = {c + (r / max ‖x - c‖ r) • (x - c)} := by
  by_cases hx : ‖x - c‖ ≤ r
  · have hp_eq : c + (r / max ‖x - c‖ r) • (x - c) = x := by
      by_cases hxc : x = c
      · simp [hxc]
      · have hr_pos : 0 < r := by
          have hnorm_pos : 0 < ‖x - c‖ := by
            exact norm_pos_iff.mpr (sub_ne_zero.mpr hxc)
          linarith
        rw [max_eq_right hx, div_self (show r ≠ 0 by linarith), one_smul]
        have hcancel : c + (x - c) = x := by
          abel_nf
        exact hcancel
    have hp_proj : x ∈ P[Metric.closedBall c r] x := by
      -- Inside the ball, the base point already minimizes the distance to itself.
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨?_, ?_⟩
      · simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm, norm_sub_rev] using hx
      · intro y hy
        simp
    have hsub :
        (P[Metric.closedBall c r] x).Subsingleton :=
      projection_mapping_subsingleton (Metric.closedBall c r) (convex_closedBall c r) x
    simpa [hp_eq] using hsub.eq_singleton_of_mem hp_proj
  · have hx' : r < ‖x - c‖ := by
      exact lt_of_not_ge hx
    have hmax : max ‖x - c‖ r = ‖x - c‖ := by
      exact max_eq_left (le_of_lt hx')
    have hp_proj : c + (r / ‖x - c‖) • (x - c) ∈ P[Metric.closedBall c r] x := by
      -- Outside the ball, the radial truncation is feasible and dominates every other feasible
      -- competitor by the triangle inequality comparison with the center.
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨radial_retraction_mem_closedBall_of_lt_norm c x r hr hx', ?_⟩
      intro y hy
      simpa [norm_sub_rev] using
        radial_retraction_distance_le_of_mem_closedBall c x y r hr hy hx'
    have hsub :
        (P[Metric.closedBall c r] x).Subsingleton :=
      projection_mapping_subsingleton (Metric.closedBall c r) (convex_closedBall c r) x
    simpa [hmax] using hsub.eq_singleton_of_mem hp_proj

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 6.26: a half-space is convex because the defining inner-product inequality is
preserved under convex combinations. -/
private lemma convex_halfSpace_owner (a : E) (α : ℝ) : Convex ℝ (halfSpace a α) := by
  intro x hx y hy t₁ t₂ ht₁ ht₂ hsum
  rw [mem_halfSpace_iff] at hx hy ⊢
  -- Push the convex combination through the linear functional `u ↦ ⟪a, u⟫`.
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  calc
    t₁ * inner ℝ a x + t₂ * inner ℝ a y ≤ t₁ * α + t₂ * α := by
      gcongr
    _ = (t₁ + t₂) * α := by
      ring
    _ = α := by
      rw [hsum, one_mul]

/-- Helper for Lemma 6.26: on the active branch of the half-space projection formula, the affine
correction lands on the boundary hyperplane. -/
private lemma halfSpace_active_correction_mem
    (a x : E) (α : ℝ) (ha : a ≠ 0) :
    x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) ∈ halfSpace a α := by
  have hnorm_sq_ne : ‖a‖ ^ (2 : ℕ) ≠ 0 := by
    positivity
  -- Evaluate the inner product after subtracting the normal-direction correction.
  rw [mem_halfSpace_iff]
  calc
    inner ℝ a (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a)) =
        inner ℝ a x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * inner ℝ a a) := by
          rw [inner_sub_right, real_inner_smul_right]
    _ = inner ℝ a x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖ ^ (2 : ℕ)) := by
          rw [real_inner_self_eq_norm_sq]
    _ = α := by
          have hcancel :
              (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖ ^ (2 : ℕ)) = inner ℝ a x - α := by
            field_simp [hnorm_sq_ne]
          linarith
  exact le_rfl

/-- Helper for Lemma 6.26: on the active branch, the normal correction is no farther from `x`
than any feasible point of the half-space. -/
private lemma halfSpace_active_correction_distance_le
    (a x y : E) (α : ℝ) (ha : a ≠ 0) (hy : y ∈ halfSpace a α) (hx : α < inner ℝ a x) :
    ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ ≤ ‖x - y‖ := by
  have hnorm_pos : 0 < ‖a‖ := by
    exact norm_pos_iff.mpr ha
  have hy_inner : inner ℝ a y ≤ α := by
    exact mem_halfSpace_iff.mp hy
  have hnum_le : inner ℝ a x - α ≤ ‖a‖ * ‖x - y‖ := by
    have hxy : inner ℝ a x - α ≤ inner ℝ a (x - y) := by
      rw [inner_sub_right]
      linarith
    exact le_trans hxy (real_inner_le_norm _ _)
  have hcorrection :
      ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ =
        (inner ℝ a x - α) / ‖a‖ := by
    -- The correction vector is a nonnegative scalar multiple of the normal `a`.
    calc
      ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ =
          ‖(((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a)‖ := by
            abel_nf
      _ = |((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ))| * ‖a‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖) := by
            rw [abs_of_nonneg]
            exact div_nonneg (by linarith) (by positivity)
      _ = (inner ℝ a x - α) / ‖a‖ := by
            field_simp [show ‖a‖ ≠ 0 by positivity]
  have hdiv : (inner ℝ a x - α) / ‖a‖ ≤ ‖x - y‖ := by
    rw [div_le_iff₀ hnorm_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_le
  rw [hcorrection]
  exact hdiv

-- Proof sketch: again split into the feasible and infeasible cases. If `⟪a, x⟫ ≤ α`, then `x` is
-- already in `halfSpace a α`. Otherwise project onto the boundary hyperplane
-- `aᵀ y = α`, which gives the correction
-- `((aᵀ x - α) / ‖a‖²) a`; inserting the positive part combines the two cases.
/-- Lemma 6.26 (5): for a nontrivial closed half-space `halfSpace a α`, the orthogonal
projection is the singleton obtained by subtracting the positive-part affine violation in the
normal direction `a`. -/
private lemma projection_mapping_halfSpace_eq_singleton_positivePartCorrection
    (a x : E) (α : ℝ) (ha : a ≠ 0) :
    P[halfSpace a α] x =
      {x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a)} := by
  by_cases hx : inner ℝ a x ≤ α
  · have hp_proj : x ∈ P[halfSpace a α] x := by
      -- On the feasible branch, the point is already in the half-space and minimizes distance
      -- trivially.
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨?_, ?_⟩
      · rw [mem_halfSpace_iff]
        exact hx
      · intro y hy
        simp
    have hp_eq : x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a) = x := by
      have hpos : (⟪a, x⟫ - α)⁺ = 0 := by
        simp [sub_nonpos.mpr hx]
      rw [hpos, zero_div, zero_smul, sub_zero]
    have hsub :
        (P[halfSpace a α] x).Subsingleton :=
      projection_mapping_subsingleton (halfSpace a α) (convex_halfSpace_owner a α) x
    simpa [hp_eq] using hsub.eq_singleton_of_mem hp_proj
  · have hviol : α < inner ℝ a x := by
      exact lt_of_not_ge hx
    have hp_proj : x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) ∈ P[halfSpace a α] x := by
      -- On the active branch, use the boundary correction and compare with every feasible point
      -- through the defining half-space inequality and Cauchy-Schwarz.
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨halfSpace_active_correction_mem a x α ha, ?_⟩
      intro y hy
      simpa [norm_sub_rev] using
        halfSpace_active_correction_distance_le a x y α ha hy hviol
    have hp_eq :
        x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a) =
          x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) := by
      have hpos : (⟪a, x⟫ - α)⁺ = inner ℝ a x - α := by
        simp [sub_nonneg.mpr hviol.le]
      rw [hpos]
    have hsub :
        (P[halfSpace a α] x).Subsingleton :=
      projection_mapping_subsingleton (halfSpace a α) (convex_halfSpace_owner a α) x
    simpa [hp_eq] using hsub.eq_singleton_of_mem hp_proj

end
