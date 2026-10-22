/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators
open scoped EllipsoidNotation
open scoped Pointwise
open scoped PositiveDefMatrixNorm
open scoped SupportFunction

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 7.6 lies in the Chapter 7 finite-family ellipsoid-rounding domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the unit ellipsoid;
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing owner of radius-parametrized
  ellipsoids;
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner for the pair of inner/outer
  ellipsoid containments;
- `weightedPrimalAverage` in `Chap07/Proposition_7_30`, a nearby Chapter 7 mean construction for
  finite families.

Best owner abstraction:
- source-facing: Lemma 7.6's empirical ellipsoid rounding of `convexHull ℝ (Set.range a)`;
- core/canonical: `IsBetaRounding` together with the underlying ellipsoid owners
  `affineEllipsoid` and `matrixEllipsoid`;
- bridge/view: the explicit arithmetic-mean and empirical-matrix formulas below.

Primitive data:
- the vertex family `a : Fin m → E`.

Derived API:
- the arithmetic mean of the vertices;
- the radius `√(m (m - 1))`;
- the normalized empirical shape matrix;
- the resulting `IsBetaRounding` witness for the convex hull.

The main duplicate wheel in the previous version was the conjunction-shaped theorem statement:
its two conclusions are exactly the fields of `IsBetaRounding`. This file now states the result at
that owner level and keeps the coordinate formulas only as supporting definitions.
-/

/-- The arithmetic mean of the vertices `a i`. -/
def polytopeArithmeticMean (a : Fin m → E) : E :=
  (m : ℝ)⁻¹ • ∑ i : Fin m, a i

/-- The outer-radius parameter `R = √(m (m - 1))` used in the empirical ellipsoid bound. -/
def polytopeRoundingRadius (m : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * (m - 1 : ℕ))

/-- The empirical covariance-shape matrix
`R⁻² ∑ᵢ (aᵢ - â) (aᵢ - â)ᵀ` attached to the vertex family `a`. -/
def polytopeRoundingMatrix (a : Fin m → E) : Matrix (Fin n) (Fin n) ℝ :=
  ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ •
    ∑ i : Fin m,
      Matrix.vecMulVec
        (a i - polytopeArithmeticMean a)
        (a i - polytopeArithmeticMean a)

/-- Helper for Lemma 7.6: the centered vertex family has zero sum, and nonempty interior of the
convex hull forces those centered vertices to span the ambient space. -/
lemma centeredVertices_zeroSum_spanTop_of_interiorNonempty
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
    (∑ i : Fin m, u i = 0) ∧ Submodule.span ℝ (Set.range u) = ⊤ := by
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  have hmean_mul : (m : ℝ) • polytopeArithmeticMean a = ∑ i : Fin m, a i := by
    -- Expand the arithmetic mean and collapse the scalar factor `m`.
    by_cases hm : m = 0
    · subst hm
      simp [polytopeArithmeticMean]
    · simpa [nsmul_eq_mul, polytopeArithmeticMean, hm]
  have hzero_sum : ∑ i : Fin m, u i = 0 := by
    -- The centered vectors sum to zero by the defining formula for the arithmetic mean.
    calc
      ∑ i : Fin m, u i
          = ∑ i : Fin m, a i - ∑ i : Fin m, polytopeArithmeticMean a := by
              simp [u, Finset.sum_sub_distrib]
      _ = ∑ i : Fin m, a i - m • polytopeArithmeticMean a := by
            simp
      _ = ∑ i : Fin m, a i - (m : ℝ) • polytopeArithmeticMean a := by
            simpa using
              congrArg
                (fun t : E ↦ ∑ i : Fin m, a i - t)
                (Nat.cast_smul_eq_nsmul (R := ℝ) m (polytopeArithmeticMean a)).symm
      _ = 0 := by
            rw [hmean_mul]
            simp
  have haff : affineSpan ℝ (Set.range a) = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior hinterior
  have hspan_top : Submodule.span ℝ (Set.range u) = ⊤ := by
    -- It is enough to show that only the zero vector is orthogonal to every centered vertex.
    have horth_bot : (Submodule.span ℝ (Set.range u))ᗮ = ⊥ := by
      ext x
      constructor
      · intro hx
        rw [Submodule.mem_orthogonal] at hx
        let K : Submodule ℝ E :=
          { carrier := {v : E | inner ℝ v x = 0}
            zero_mem' := by simp
            add_mem' := by
              intro v w hv hw
              have hv' : inner ℝ v x = 0 := hv
              have hw' : inner ℝ w x = 0 := hw
              change inner ℝ (v + w) x = 0
              simpa [inner_add_left, hv', hw']
            smul_mem' := by
              intro c v hv
              have hv' : inner ℝ v x = 0 := hv
              change inner ℝ (c • v) x = 0
              simpa [real_inner_smul_left, hv'] }
        let Q : AffineSubspace ℝ E :=
          AffineSubspace.mk' (polytopeArithmeticMean a) K
        have hu_zero : ∀ i : Fin m, inner ℝ (u i) x = 0 := by
          intro i
          exact hx (u i) (Submodule.subset_span ⟨i, rfl⟩)
        have hrange : Set.range a ⊆ (Q : Set E) := by
          intro y hy
          rcases hy with ⟨i, rfl⟩
          change a i ∈ AffineSubspace.mk' (polytopeArithmeticMean a) K
          rw [AffineSubspace.mem_mk']
          change inner ℝ (u i) x = 0
          exact hu_zero i
        have hQ_top : Q = ⊤ := by
          have hle : affineSpan ℝ (Set.range a) ≤ Q :=
            (affineSpan_le).2 hrange
          have htop_le : (⊤ : AffineSubspace ℝ E) ≤ Q := by
            simpa [haff] using hle
          exact top_le_iff.mp htop_le
        have hK_top : K = ⊤ := by
          simpa [Q, AffineSubspace.direction_mk'] using
            congrArg AffineSubspace.direction hQ_top
        have hx_mem : x ∈ K := by
          simpa [hK_top] using (show x ∈ (⊤ : Submodule ℝ E) by simp)
        have hxx : inner ℝ x x = 0 := by
          simpa [K] using hx_mem
        have hx_zero : x = 0 := by
          simpa using inner_self_eq_zero.mp hxx
        simpa [hx_zero]
      · intro hx
        have hx_zero : x = 0 := by simpa using hx
        simpa [hx_zero] using
          (show (0 : E) ∈ (Submodule.span ℝ (Set.range u))ᗮ from Submodule.zero_mem _)
    exact (Submodule.orthogonal_eq_bot_iff.mp horth_bot)
  exact ⟨hzero_sum, hspan_top⟩

/-- Helper for Lemma 7.6: outside the degenerate `Subsingleton E` branch, nonempty interior of the
convex hull forces the index family to contain at least two vertices. -/
lemma two_le_card_of_interior_nonempty_of_nontrivial
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    2 ≤ m := by
  have haff : affineSpan ℝ (Set.range a) = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior hinterior
  by_cases hm0 : m = 0
  · subst hm0
    simpa [convexHull_empty] using hinterior
  by_cases hm1 : m = 1
  · have hsubsingleton : (Set.range a).Subsingleton := by
      intro x hx y hy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      have : i = j := by
        subst hm1
        exact Subsingleton.elim _ _
      simpa [this]
    have : Subsingleton E :=
      AffineSubspace.subsingleton_of_subsingleton_span_eq_top hsubsingleton haff
    exfalso
    exact (not_nontrivial_iff_subsingleton.mpr this) ‹Nontrivial E›
  omega

/-- Helper for Lemma 7.6: in the nontrivial branch, the rounding radius `√(m (m - 1))` is
strictly positive. -/
lemma polytopeRoundingRadius_pos_of_interior_nonempty
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    0 < polytopeRoundingRadius m := by
  have hm : 2 ≤ m :=
    two_le_card_of_interior_nonempty_of_nontrivial a hinterior
  have hm_pos : 0 < (m : ℝ) := by positivity
  have hm_sub_nat : 1 ≤ m - 1 := by omega
  have hm_sub_pos : 0 < (((m - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hm_sub_nat
  have hprod_pos : 0 < (m : ℝ) * (m - 1 : ℕ) := by
    nlinarith [hm_pos, hm_sub_pos]
  exact Real.sqrt_pos_of_pos hprod_pos

/-- Helper for Lemma 7.6: the empirical rounding matrix acts as the normalized sum of the centered
rank-one maps `x ↦ ⟪uᵢ, x⟫ uᵢ`. -/
private lemma polytopeRoundingMatrix_toEuclideanLin_eq_scaled_sum_smul
    (a : Fin m → E) (x : E) :
    (polytopeRoundingMatrix a).toEuclideanLin x =
      ∑ i : Fin m,
        ((((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
            inner ℝ (a i - polytopeArithmeticMean a) x)) •
          (a i - polytopeArithmeticMean a) := by
  -- Route correction: rewrite the owner matrix action into the centered rank-one form once so the
  -- later quadratic-form and positivity arguments can stay on the same normal form.
  ext p
  -- Expand the empirical matrix action entrywise and pull the normalization factor through the sum.
  simp [polytopeRoundingMatrix, Matrix.toEuclideanLin_apply, Matrix.vecMulVec_mulVec, inner,
    dotProduct, mul_assoc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- Commute the real factors inside the centered score before closing by ring arithmetic.
  have hswap :
      ∑ j : Fin n,
          ((a i).ofLp j - (polytopeArithmeticMean a).ofLp j) * x.ofLp j =
        ∑ j : Fin n,
          x.ofLp j * ((a i).ofLp j - (polytopeArithmeticMean a).ofLp j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hswap]
  ring

/-- Helper for Lemma 7.6: the quadratic form of the empirical rounding matrix is the normalized
sum of the squared centered scores `⟪aᵢ - â, x⟫²`. -/
private lemma polytopeRoundingMatrix_quadratic_eq_scaled_sum_inner_sq
    (a : Fin m → E) (x : E) :
    inner ℝ ((polytopeRoundingMatrix a).toEuclideanLin x) x =
      ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
        ∑ i : Fin m, (inner ℝ (a i - polytopeArithmeticMean a) x) ^ (2 : ℕ) := by
  -- First rewrite the matrix action by the centered rank-one expansion.
  rw [polytopeRoundingMatrix_toEuclideanLin_eq_scaled_sum_smul]
  -- Then each summand becomes the expected squared score.
  rw [sum_inner]
  calc
    ∑ i : Fin m,
        inner ℝ
          (((((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
              inner ℝ (a i - polytopeArithmeticMean a) x)) •
            (a i - polytopeArithmeticMean a))
          x
        =
          ∑ i : Fin m,
            ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
              (inner ℝ (a i - polytopeArithmeticMean a) x) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [real_inner_smul_left]
          ring
    _ =
        ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
          ∑ i : Fin m, (inner ℝ (a i - polytopeArithmeticMean a) x) ^ (2 : ℕ) := by
          simpa using
            (Finset.mul_sum (s := Finset.univ)
              (f := fun i : Fin m ↦ (inner ℝ (a i - polytopeArithmeticMean a) x) ^ (2 : ℕ))
              (a := ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹)).symm

/-- Helper for Lemma 7.6: a spanning family has a nonzero inner-product score against every
nonzero test vector. -/
private lemma exists_inner_ne_zero_of_span_eq_top
    (u : Fin m → E) (hspan : Submodule.span ℝ (Set.range u) = ⊤) {x : E} (hx : x ≠ 0) :
    ∃ i : Fin m, inner ℝ (u i) x ≠ 0 := by
  by_contra hnone
  push Not at hnone
  -- If every score vanishes, then `x` is orthogonal to the span of the centered family.
  have hx_orth : x ∈ (Submodule.span ℝ (Set.range u))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        simpa using hnone i
    | zero =>
        simp
    | add y z hy hz hy_zero hz_zero =>
        simp [inner_add_left, hy_zero, hz_zero]
    | smul c y hy hy_zero =>
        simp [real_inner_smul_left, hy_zero]
  have hx_bot : x ∈ (⊥ : Submodule ℝ E) := by
    rw [← Submodule.top_orthogonal_eq_bot]
    simpa [hspan] using hx_orth
  exact hx (by simpa using hx_bot)

/-- Helper for Lemma 7.6: nonempty interior of the polytope makes the empirical rounding matrix
positive definite. -/
lemma polytopeRoundingMatrix_posDef
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    (polytopeRoundingMatrix a).PosDef := by
  by_cases hsub : Subsingleton E
  · letI := hsub
    have htranspose :
        (polytopeRoundingMatrix a)ᵀ = polytopeRoundingMatrix a := by
      rw [polytopeRoundingMatrix, Matrix.transpose_smul, Matrix.transpose_sum]
      simp
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simpa [Matrix.IsHermitian, Matrix.IsSymm] using htranspose
    · intro x hx
      have hx_zero :
          (EuclideanSpace.equiv (Fin n) ℝ).symm x = 0 :=
        Subsingleton.elim _ _
      exfalso
      apply hx
      simpa using congrArg (EuclideanSpace.equiv (Fin n) ℝ) hx_zero
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
    have hcentered :
        (∑ i : Fin m, u i = 0) ∧ Submodule.span ℝ (Set.range u) = ⊤ :=
      centeredVertices_zeroSum_spanTop_of_interiorNonempty a hinterior
    have hR_pos : 0 < polytopeRoundingRadius m :=
      polytopeRoundingRadius_pos_of_interior_nonempty a hinterior
    have htranspose :
        (polytopeRoundingMatrix a)ᵀ = polytopeRoundingMatrix a := by
      rw [polytopeRoundingMatrix, Matrix.transpose_smul, Matrix.transpose_sum]
      simp
    -- Convert positivity of the centered quadratic form into the matrix owner API.
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · -- The empirical matrix is symmetric because each centered rank-one summand is symmetric.
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using htranspose
    · intro x hx
      let xE : E := (EuclideanSpace.equiv (Fin n) ℝ).symm x
      have hxE : xE ≠ 0 := by
        intro hxE_zero
        apply hx
        simpa [xE] using congrArg (EuclideanSpace.equiv (Fin n) ℝ) hxE_zero
      obtain ⟨i, hi_ne⟩ :=
        exists_inner_ne_zero_of_span_eq_top u hcentered.2 hxE
      have hscale_pos : 0 < ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ := by
        positivity
      have hterm_nonneg :
          ∀ j : Fin m, 0 ≤ (inner ℝ (u j) xE) ^ (2 : ℕ) := by
        intro j
        positivity
      have hterm_pos : 0 < (inner ℝ (u i) xE) ^ (2 : ℕ) := by
        have hterm_nonzero : (inner ℝ (u i) xE) ^ (2 : ℕ) ≠ 0 := by
          exact pow_ne_zero 2 hi_ne
        exact lt_of_le_of_ne (hterm_nonneg i) (Ne.symm hterm_nonzero)
      have hle :
          (inner ℝ (u i) xE) ^ (2 : ℕ) ≤
            ∑ j : Fin m, (inner ℝ (u j) xE) ^ (2 : ℕ) := by
        simpa using
          (Finset.single_le_sum
            (fun j _ ↦ hterm_nonneg j)
            (Finset.mem_univ i) :
              (fun j : Fin m ↦ (inner ℝ (u j) xE) ^ (2 : ℕ)) i ≤
                ∑ j : Fin m, (fun j : Fin m ↦ (inner ℝ (u j) xE) ^ (2 : ℕ)) j)
      have hsum_pos :
          0 < ∑ j : Fin m, (inner ℝ (u j) xE) ^ (2 : ℕ) := by
        exact lt_of_lt_of_le hterm_pos hle
      have hquad_pos :
          0 < inner ℝ ((polytopeRoundingMatrix a).toEuclideanLin xE) xE := by
        rw [polytopeRoundingMatrix_quadratic_eq_scaled_sum_inner_sq]
        simpa [u] using mul_pos hscale_pos hsum_pos
      have hdot :
          inner ℝ xE ((polytopeRoundingMatrix a).toEuclideanLin xE) =
            x ⬝ᵥ polytopeRoundingMatrix a *ᵥ x := by
        change ((polytopeRoundingMatrix a).toEuclideanLin xE).ofLp ⬝ᵥ star xE.ofLp =
          x ⬝ᵥ polytopeRoundingMatrix a *ᵥ x
        rw [Matrix.toEuclideanLin_apply, dotProduct_comm]
        simp [xE]
      calc
        0 < inner ℝ xE ((polytopeRoundingMatrix a).toEuclideanLin xE) := by
              simpa [real_inner_comm] using hquad_pos
        _ = x ⬝ᵥ polytopeRoundingMatrix a *ᵥ x := hdot

/-- Helper for Lemma 7.6: translating by the arithmetic mean identifies the centered convex hull
with the original convex hull of the vertices. -/
lemma sub_mean_mem_convexHull_centeredVertices_iff
    (a : Fin m → E) (y : E) :
    let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
    y - polytopeArithmeticMean a ∈ convexHull ℝ (Set.range u) ↔
      y ∈ convexHull ℝ (Set.range a) := by
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  have hrange : Set.range a = polytopeArithmeticMean a +ᵥ Set.range u := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change ∃ p ∈ Set.range u, polytopeArithmeticMean a + p = a i
      refine ⟨u i, ⟨i, rfl⟩, ?_⟩
      simp [u, add_assoc]
    · intro hz
      change ∃ p ∈ Set.range u, polytopeArithmeticMean a + p = z at hz
      rcases hz with ⟨p, ⟨i, rfl⟩, hp⟩
      exact ⟨i, by simpa [u, add_assoc] using hp⟩
  have htranslate :
      convexHull ℝ (Set.range a) =
        polytopeArithmeticMean a +ᵥ convexHull ℝ (Set.range u) := by
    -- Translate the centered hull by the arithmetic mean before comparing memberships.
    simpa [hrange] using
      (convexHull_vadd (polytopeArithmeticMean a) (Set.range u))
  -- Move the target membership across the translation equivalence.
  constructor
  · intro hy
    have hy' : y ∈ polytopeArithmeticMean a +ᵥ convexHull ℝ (Set.range u) := by
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm] using hy
    simpa [htranslate] using hy'
  · intro hy
    have hy' : y ∈ polytopeArithmeticMean a +ᵥ convexHull ℝ (Set.range u) := by
      simpa [htranslate] using hy
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using hy'

/-- Helper for Lemma 7.6: the centered Chapter 7 pullback seminorm attached to `a`. -/
private def centeredPullbackSeminorm (a : Fin m → E) : Seminorm ℝ E :=
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  Seminorm.comp
    (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
    (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
      (LinearMap.pi fun i ↦ (innerSL ℝ (u i)).toLinearMap))

/-- Helper for Lemma 7.6: a nonempty finite range has support value `0` at the origin. -/
private lemma supportFunction_range_toReal_zero
    [Nonempty (Fin m)] (b : Fin m → E) :
    (ξ[Set.range b] (0 : E)).toReal = 0 := by
  -- Expand the finite-range support value and note that every inner product with `0` vanishes.
  rw [supportFunction_range_toReal_eq_sSup_inner (a := b) (x := (0 : E))]
  simp

/-- Helper for Lemma 7.6: the centered pullback seminorm is exactly the rounding radius times the
positive-definite matrix norm of the empirical matrix. -/
private lemma centeredPullbackSeminorm_eq_radius_mul_positiveDefMatrixNorm
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty)
    (x : E) :
    centeredPullbackSeminorm a x =
      polytopeRoundingRadius m *
        ‖x‖[⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩] := by
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  let G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef} :=
    ⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩
  have hR_pos : 0 < polytopeRoundingRadius m :=
    polytopeRoundingRadius_pos_of_interior_nonempty a hinterior
  have hs_nonneg :
      0 ≤ ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ) := by
    exact Finset.sum_nonneg fun i _ ↦ by positivity
  have hquadratic_nonneg :
      0 ≤ inner ℝ ((polytopeRoundingMatrix a).toEuclideanLin x) x := by
    have hPosLin : (polytopeRoundingMatrix a).toEuclideanLin.IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  have hpullback :
      centeredPullbackSeminorm a x =
        Real.sqrt (∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ)) := by
    -- Expand the centered pullback seminorm along the finite row map built from the centered
    -- vertices.
    simpa [centeredPullbackSeminorm, u] using
      (pullbackSeminorm_eq_sqrt_sum_inner_sq (a := u) (x := x))
  have hmatrixNorm :
      ‖x‖[G] =
        Real.sqrt
          (((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
            ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ)) := by
    -- Rewrite the empirical matrix norm through the quadratic form of the centered rank-one sum.
    rw [positiveDefMatrixNorm_def G, polytopeRoundingMatrix_quadratic_eq_scaled_sum_inner_sq]
  have hleft_sq :
      (centeredPullbackSeminorm a x) ^ (2 : ℕ) =
        ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ) := by
    rw [hpullback, Real.sq_sqrt hs_nonneg]
  have hright_sq :
      (polytopeRoundingRadius m *
          ‖x‖[⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩]) ^
        (2 : ℕ) =
        ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ) := by
    have hnorm_sq :
        (‖x‖[G]) ^ (2 : ℕ) =
          ((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
            ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ) := by
      rw [hmatrixNorm, Real.sq_sqrt]
      positivity
    calc
      (polytopeRoundingRadius m * ‖x‖[G]) ^ (2 : ℕ)
          = (polytopeRoundingRadius m) ^ (2 : ℕ) * (‖x‖[G]) ^ (2 : ℕ) := by
              ring
      _ =
          (polytopeRoundingRadius m) ^ (2 : ℕ) *
            (((polytopeRoundingRadius m) ^ (2 : ℕ))⁻¹ *
              ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ)) := by
              rw [hnorm_sq]
      _ = ∑ i : Fin m, (inner ℝ (u i) x) ^ (2 : ℕ) := by
            field_simp [pow_ne_zero 2 hR_pos.ne']
  have hleft_nonneg : 0 ≤ centeredPullbackSeminorm a x := by
    positivity
  have hright_nonneg :
      0 ≤
        polytopeRoundingRadius m *
          ‖x‖[⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩] := by
    positivity
  -- Both sides are nonnegative and have the same square, so the scalar normalization matches.
  nlinarith [hleft_sq, hright_sq, hleft_nonneg, hright_nonneg]

/-- Helper for Lemma 7.6: a point in the centered unit empirical ellipsoid defines a small
supporting functional for the centered pullback seminorm. -/
private lemma toDual_mem_smallCenteredPullbackDualBall_of_mem_unitEllipsoid
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty)
    {y : E}
    (hy : y ∈ W[1]((polytopeRoundingMatrix a))) :
    (InnerProductSpace.toDual ℝ E y) ∈
      dualClosedBall (centeredPullbackSeminorm a) (1 / polytopeRoundingRadius m) := by
  let G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef} :=
    ⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩
  have hR_pos : 0 < polytopeRoundingRadius m :=
    polytopeRoundingRadius_pos_of_interior_nonempty a hinterior
  have hy_dual : ‖y‖[G,*] ≤ 1 := by
    -- Rewrite centered ellipsoid membership as the corresponding empirical dual-norm bound.
    rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le G.2] at hy
  rw [mem_dualClosedBall_iff]
  intro x
  have hGnorm :
      ‖x‖[⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩] = ‖x‖[G] := by
    rfl
  have hx_nonneg : 0 ≤ ‖x‖[G] := by
    positivity
  have hscale :
      (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x = ‖x‖[G] := by
    -- Normalize the centered pullback seminorm to the empirical matrix norm once.
    rw [centeredPullbackSeminorm_eq_radius_mul_positiveDefMatrixNorm a hinterior x, hGnorm]
    field_simp [hR_pos.ne']
  have hupper :
      inner ℝ y x ≤ (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x := by
    calc
      inner ℝ y x ≤ ‖y‖[G,*] * ‖x‖[G] :=
        by
          simpa [G] using
            (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G.1 G.2) x y)
      _ ≤ 1 * ‖x‖[G] := by
            exact mul_le_mul_of_nonneg_right hy_dual hx_nonneg
      _ = ‖x‖[G] := by ring
      _ = (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x := by
            symm
            exact hscale
  have hneg_upper :
      -inner ℝ y x ≤ (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x := by
    calc
      -inner ℝ y x = inner ℝ y (-x) := by simp
      _ ≤ ‖y‖[G,*] * ‖-x‖[G] :=
            by
              simpa [G] using
                (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G.1 G.2) (-x) y)
      _ = ‖y‖[G,*] * ‖x‖[G] := by simp
      _ ≤ 1 * ‖x‖[G] := by
            exact mul_le_mul_of_nonneg_right hy_dual hx_nonneg
      _ = ‖x‖[G] := by ring
      _ = (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x := by
            symm
            exact hscale
  -- Convert the two directional pairing bounds into the absolute-value dual-ball inequality.
  have habs :
      |inner ℝ y x| ≤ (1 / polytopeRoundingRadius m) * centeredPullbackSeminorm a x :=
    abs_le.mpr ⟨by linarith [hneg_upper], hupper⟩
  simpa [InnerProductSpace.toDual_apply_apply] using habs

/-- Helper for Lemma 7.6: a centered pullback dual-ball bound of radius `1` transports to the
outer empirical ellipsoid of radius `polytopeRoundingRadius m`. -/
private lemma mem_centeredOuterEllipsoid_of_toDual_mem_dualBall_one
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty)
    {z : E}
    (hz :
      (InnerProductSpace.toDual ℝ E z) ∈ dualClosedBall (centeredPullbackSeminorm a) 1) :
    z ∈ W[(polytopeRoundingRadius m)]((polytopeRoundingMatrix a)) := by
  let G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef} :=
    ⟨polytopeRoundingMatrix a, polytopeRoundingMatrix_posDef a hinterior⟩
  have hR_pos : 0 < polytopeRoundingRadius m :=
    polytopeRoundingRadius_pos_of_interior_nonempty a hinterior
  rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le G.2]
  rw [positiveDefMatrixNorm_dualNorm_apply]
  refine csSup_le ?_ ?_
  · refine ⟨0, 0, ?_⟩
    constructor
    · change ‖(0 : E)‖[G] ≤ 1
      simp
    · simp
  · rintro _ ⟨x, hxunit, rfl⟩
    have hg_apply :
        |inner ℝ z x| ≤ centeredPullbackSeminorm a x := by
      simpa [InnerProductSpace.toDual_apply_apply] using
        (mem_dualClosedBall_iff (centeredPullbackSeminorm a) 1
          (InnerProductSpace.toDual ℝ E z)).1 hz x
    have hx_nonneg : 0 ≤ ‖x‖[G] := by
      positivity
    calc
      inner ℝ z x ≤ |inner ℝ z x| := le_abs_self _
      _ ≤ centeredPullbackSeminorm a x := hg_apply
      _ = polytopeRoundingRadius m * ‖x‖[G] :=
            centeredPullbackSeminorm_eq_radius_mul_positiveDefMatrixNorm a hinterior x
      _ ≤ polytopeRoundingRadius m * 1 := by
            exact mul_le_mul_of_nonneg_left hxunit (le_of_lt hR_pos)
      _ = polytopeRoundingRadius m := by ring

/-- Helper for Lemma 7.6: the centered unit empirical ellipsoid lies in the centered convex hull
of the vertices. -/
private lemma centeredUnitEllipsoidSubsetConvexHullCenteredVertices
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    W[1]((polytopeRoundingMatrix a)) ⊆
      convexHull ℝ (Set.range fun i : Fin m ↦ a i - polytopeArithmeticMean a) := by
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  let C : Set E := convexHull ℝ (Set.range u)
  have hm : 2 ≤ m :=
    two_le_card_of_interior_nonempty_of_nontrivial a hinterior
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm_pos
  have hzero_support : (ξ[Set.range u] (0 : E)).toReal = 0 :=
    supportFunction_range_toReal_zero u
  have hcentered :
      (∑ i : Fin m, u i = 0) ∧ Submodule.span ℝ (Set.range u) = ⊤ :=
    centeredVertices_zeroSum_spanTop_of_interiorNonempty a hinterior
  have hm1 : 1 ≤ m := by
    omega
  let p : Seminorm ℝ E :=
    Seminorm.comp
      (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
      (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
        (LinearMap.pi fun i ↦ (innerSL ℝ (u i)).toLinearMap))
  have hp : p = centeredPullbackSeminorm a := by
    rfl
  have hsmallBall :
      dualClosedBall
          (centeredPullbackSeminorm a)
          (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ⊆
        {g : StrongDual ℝ E |
          ∀ y : E, (ξ[Set.range u] (0 : E)).toReal + g y ≤ (ξ[Set.range u] y).toReal} := by
    -- Route correction: use the one-way ellipsoid-to-dual-ball transport, then stay on the
    -- support-function surface supplied by Lemma 7.1 for the centered family.
    have hsmallBall' :
        dualClosedBall p (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) ⊆
          {g : StrongDual ℝ E |
            ∀ y : E, (ξ[Set.range u] (0 : E)).toReal + g y ≤ (ξ[Set.range u] y).toReal} :=
      small_dualClosedBall_subset_supporting_functionals (a := u) hm hcentered.1
    simpa [hp] using hsmallBall'
  have hC_nonempty : C.Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hm_pos
    exact ⟨u i, subset_convexHull ℝ (Set.range u) (Set.mem_range_self i)⟩
  have hC_compact : IsCompact C := by
    exact Set.Finite.isCompact_convexHull
      (𝕜 := ℝ) (s := Set.range u) (Set.finite_range u)
  have hC_closed : IsClosed C := hC_compact.isClosed
  have hC_convex : Convex ℝ C := convex_convexHull ℝ (Set.range u)
  intro y hy
  have hyDual :
      (InnerProductSpace.toDual ℝ E y) ∈
        dualClosedBall (centeredPullbackSeminorm a) (1 / polytopeRoundingRadius m) :=
    toDual_mem_smallCenteredPullbackDualBall_of_mem_unitEllipsoid a hinterior hy
  have hyDual' :
      (InnerProductSpace.toDual ℝ E y) ∈
        dualClosedBall
          (centeredPullbackSeminorm a)
          (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) := by
    simpa [polytopeRoundingRadius, Nat.cast_sub hm1] using hyDual
  have hy_support :
      ∀ z : E, (ξ[Set.range u] (0 : E)).toReal + inner ℝ y z ≤ (ξ[Set.range u] z).toReal := by
    intro z
    simpa [InnerProductSpace.toDual_apply_apply] using (hsmallBall hyDual') z
  have hsingleton_subset : ({y} : Set E) ⊆ C := by
    refine subset_of_supportFunction_le_on_domain ({y} : Set E) C hC_nonempty hC_closed hC_convex ?_
    intro x hxdom
    obtain ⟨s, hsC, hsMax⟩ :=
      hC_compact.exists_isMaxOn hC_nonempty
        (show ContinuousOn (fun z : E ↦ inner ℝ z x) C from by fun_prop)
    have hs_support :
        (ξ[C] x).toReal = inner ℝ s x := by
      -- Replace the support value of the compact centered hull by a maximizing hull point.
      have hmaxE : IsMaxOn (fun z : E ↦ (((inner ℝ z x : ℝ)) : EReal)) C s := by
        intro z hz
        show (((inner ℝ z x : ℝ)) : EReal) ≤ (((inner ℝ s x : ℝ)) : EReal)
        exact_mod_cast hsMax hz
      have hs_lub :
          IsLUB ((fun z : E ↦ ((inner ℝ z x : ℝ) : EReal)) '' C) ((inner ℝ s x : ℝ) : EReal) := by
        simpa [isMaxOn_iff] using hmaxE.isLUB hsC
      rw [supportFunction_apply, hs_lub.csSup_eq ⟨((inner ℝ s x : ℝ) : EReal), ⟨s, hsC, rfl⟩⟩]
      simp
    have hpoint_support :
        inner ℝ y x ≤ (ξ[C] x).toReal := by
      have hrange_support :
          inner ℝ y x ≤ (ξ[Set.range u] x).toReal := by
        linarith [hy_support x, hzero_support]
      have hconvex_eq :
          ξ[C] x = ξ[Set.range u] x := by
        simpa [C] using
          congrArg (fun f : E → EReal ↦ f x) (supportFunction_convexHull_eq (Q := Set.range u))
      rw [hconvex_eq]
      exact hrange_support
    have hinner_le_max : inner ℝ y x ≤ inner ℝ s x := by
      calc
        inner ℝ y x ≤ (ξ[C] x).toReal := hpoint_support
        _ = inner ℝ s x := hs_support
    rw [supportFunction_apply, supportFunction_apply]
    have hsingleton :
        sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' ({y} : Set E)) =
          ((inner ℝ y x : ℝ) : EReal) := by
      simp
    rw [hsingleton]
    exact (show ((inner ℝ y x : ℝ) : EReal) ≤ ((inner ℝ s x : ℝ) : EReal) by
      exact_mod_cast hinner_le_max).trans <| le_sSup ⟨s, hsC, rfl⟩
  exact hsingleton_subset (by simp)

/-- Helper for Lemma 7.6: the centered convex hull is contained in the centered outer empirical
ellipsoid of radius `polytopeRoundingRadius m`. -/
private lemma convexHullCenteredVerticesSubsetCenteredOuterEllipsoid
    [Nontrivial E]
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    convexHull ℝ (Set.range fun i : Fin m ↦ a i - polytopeArithmeticMean a) ⊆
      W[(polytopeRoundingRadius m)]((polytopeRoundingMatrix a)) := by
  let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
  have hm : 2 ≤ m :=
    two_le_card_of_interior_nonempty_of_nontrivial a hinterior
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm_pos
  have hzero_support : (ξ[Set.range u] (0 : E)).toReal = 0 :=
    supportFunction_range_toReal_zero u
  intro z hz
  change z ∈ convexHull ℝ (Set.range u) at hz
  let C : Set E := convexHull ℝ (Set.range u)
  have hC_nonempty : C.Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hm_pos
    exact ⟨u i, subset_convexHull ℝ (Set.range u) (Set.mem_range_self i)⟩
  have hC_compact : IsCompact C := by
    exact Set.Finite.isCompact_convexHull
      (𝕜 := ℝ) (s := Set.range u) (Set.finite_range u)
  let p : Seminorm ℝ E :=
    Seminorm.comp
      (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
      (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
        (LinearMap.pi fun i ↦ (innerSL ℝ (u i)).toLinearMap))
  have hp : p = centeredPullbackSeminorm a := by
    rfl
  have hz_support :
      ∀ y : E, (ξ[Set.range u] (0 : E)).toReal + inner ℝ z y ≤ (ξ[Set.range u] y).toReal := by
    intro y
    obtain ⟨s, hsC, hsMax⟩ :=
      hC_compact.exists_isMaxOn hC_nonempty
        (show ContinuousOn (fun w : E ↦ inner ℝ w y) C from by fun_prop)
    have hs_support :
        (ξ[C] y).toReal = inner ℝ s y := by
      have hmaxE : IsMaxOn (fun w : E ↦ (((inner ℝ w y : ℝ)) : EReal)) C s := by
        intro w hw
        show (((inner ℝ w y : ℝ)) : EReal) ≤ (((inner ℝ s y : ℝ)) : EReal)
        exact_mod_cast hsMax hw
      have hs_lub :
          IsLUB ((fun w : E ↦ ((inner ℝ w y : ℝ) : EReal)) '' C) ((inner ℝ s y : ℝ) : EReal) := by
        simpa [isMaxOn_iff] using hmaxE.isLUB hsC
      rw [supportFunction_apply, hs_lub.csSup_eq ⟨((inner ℝ s y : ℝ) : EReal), ⟨s, hsC, rfl⟩⟩]
      simp
    have hconvex_support :
        inner ℝ z y ≤ (ξ[C] y).toReal := by
      calc
        inner ℝ z y ≤ inner ℝ s y := hsMax hz
        _ = (ξ[C] y).toReal := by symm; exact hs_support
    have hsupport_eq :
        (ξ[C] y).toReal = (ξ[Set.range u] y).toReal := by
      have hconvex_eq :
          ξ[C] y = ξ[Set.range u] y := by
        simpa [C] using
          congrArg (fun f : E → EReal ↦ f y) (supportFunction_convexHull_eq (Q := Set.range u))
      rw [hconvex_eq]
    have hrange_support :
        inner ℝ z y ≤ (ξ[Set.range u] y).toReal := by
      calc
        inner ℝ z y ≤ (ξ[C] y).toReal := hconvex_support
        _ = (ξ[Set.range u] y).toReal := hsupport_eq
    calc
      (ξ[Set.range u] (0 : E)).toReal + inner ℝ z y = inner ℝ z y := by
        rw [hzero_support]
        ring
      _ ≤ (ξ[Set.range u] y).toReal := hrange_support
  have hzDual :
      (InnerProductSpace.toDual ℝ E z) ∈ dualClosedBall (centeredPullbackSeminorm a) 1 := by
    -- The centered hull point is already a supporting functional at the origin of the centered
    -- support function, so Lemma 7.1 places it in the unit pullback dual ball.
    have hzDual' :
        (InnerProductSpace.toDual ℝ E z) ∈ dualClosedBall p 1 := by
      simpa [p, InnerProductSpace.toDual_apply_apply] using
        (supporting_functional_mem_dualClosedBall_one
          (a := u) (g := InnerProductSpace.toDual ℝ E z) hm_pos hz_support)
    simpa [hp] using hzDual'
  exact mem_centeredOuterEllipsoid_of_toDual_mem_dualBall_one a hinterior hzDual

-- Proof sketch: compare support functions. For the outer inclusion, compute the support function of
-- the ellipsoid with shape `polytopeRoundingMatrix a` and bound it below by the maximum over the
-- vertices. For the inner inclusion, use the zero-sum relation among the centered support values
-- and optimize their squared sum under the upper bound by the maximal component.
/-- Lemma 7.6: if the convex hull of the vertices `a i` has nonempty interior, then the empirical
ellipsoid centered at the arithmetic mean gives a
`polytopeRoundingRadius m`-rounding of that convex hull. -/
theorem convexHull_range_between_empirical_ellipsoids_of_interior_nonempty
    (a : Fin m → E)
    (hinterior : (interior (convexHull ℝ (Set.range a))).Nonempty) :
    IsBetaRounding
      (convexHull ℝ (Set.range a))
      (polytopeRoundingRadius m)
      (polytopeRoundingMatrix a)
      (polytopeArithmeticMean a) := by
  classical
  by_cases hsub : Subsingleton E
  · -- In the degenerate zero-dimensional branch, every relevant set is the unique point.
    letI := hsub
    have hconv_nonempty : (convexHull ℝ (Set.range a)).Nonempty :=
      hinterior.mono interior_subset
    rcases (convexHull_nonempty_iff.mp hconv_nonempty) with ⟨z, ⟨i, rfl⟩⟩
    refine ⟨?_, ?_⟩
    · intro y hy
      have hy_eq : y = a i := Subsingleton.elim _ _
      have hi_mem : a i ∈ convexHull ℝ (Set.range a) :=
        subset_convexHull ℝ (Set.range a) (Set.mem_range_self i)
      simpa [hy_eq] using hi_mem
    · intro y hy
      have hy_eq : y = polytopeArithmeticMean a := Subsingleton.elim _ _
      have hcenter_mem :
          polytopeArithmeticMean a ∈
            matrixEllipsoid
              (polytopeRoundingMatrix a)
              (polytopeArithmeticMean a)
              (polytopeRoundingRadius m) := by
        have hR_nonneg : 0 ≤ polytopeRoundingRadius m :=
          Real.sqrt_nonneg _
        rw [mem_matrixEllipsoid_iff]
        simpa using hR_nonneg
      simpa [hy_eq] using hcenter_mem
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    let u : Fin m → E := fun i ↦ a i - polytopeArithmeticMean a
    have hG : (polytopeRoundingMatrix a).PosDef :=
      polytopeRoundingMatrix_posDef a hinterior
    have hinner_centered :
        W[1]((polytopeRoundingMatrix a)) ⊆ convexHull ℝ (Set.range u) :=
      centeredUnitEllipsoidSubsetConvexHullCenteredVertices a hinterior
    have houter_centered :
        convexHull ℝ (Set.range u) ⊆ W[(polytopeRoundingRadius m)]((polytopeRoundingMatrix a)) :=
      convexHullCenteredVerticesSubsetCenteredOuterEllipsoid a hinterior
    refine ⟨?_, ?_⟩
    · intro y hy
      -- Route correction: prove the inner inclusion in centered coordinates and translate back by
      -- the arithmetic mean only once at the end.
      have hy_matrix :
          y ∈ W[1]((polytopeArithmeticMean a), (polytopeRoundingMatrix a)) := by
        simpa [matrixEllipsoid_one_eq_affineEllipsoid] using hy
      have hy_centered :
          y - polytopeArithmeticMean a ∈ W[1]((polytopeRoundingMatrix a)) := by
        rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hG]
        rwa [mem_matrixEllipsoid_iff_dualNorm_le hG] at hy_matrix
      exact
        (sub_mean_mem_convexHull_centeredVertices_iff (a := a) (y := y)).mp
          (hinner_centered hy_centered)
    · intro y hy
      -- Translate the original hull point to centered coordinates, apply the centered outer
      -- inclusion, and rewrite back to the mean-centered ellipsoid owner.
      have hy_centered :
          y - polytopeArithmeticMean a ∈ convexHull ℝ (Set.range u) :=
        (sub_mean_mem_convexHull_centeredVertices_iff (a := a) (y := y)).mpr hy
      have hy_outer_centered :
          y - polytopeArithmeticMean a ∈
            W[(polytopeRoundingRadius m)]((polytopeRoundingMatrix a)) :=
        houter_centered hy_centered
      rw [mem_matrixEllipsoid_iff_dualNorm_le hG]
      rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hG] at hy_outer_centered
      simpa using hy_outer_centered

end
