/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

universe u

noncomputable section

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local notation "E" => ι → ℝ

/- Definition 4.4 is `source-facing`: it specializes the chapter owner
`conjugate_function` to the explicit quadratic-affine map on a finite real product `ι → ℝ`,
specializing to `ℝ^n` when `ι = Fin n`. The labeled entry packages the positive-definite
max/attainment form of equation `(4.4.7)`, while the owner-level `sSup` formulas remain companion
API. -/

-- Semantic recall: mathlib uses `Matrix.PosDef` for the source hypothesis `A ∈ 𝕊_{++}^n`, and
-- the chapter's source-facing max formulas are expressed via `IsGreatest` on the objective range.

/-- The quadratic-affine function
`x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on a finite real product, specializing to `ℝ^n` for
`ι = Fin n`. -/
def quadratic_affine_function (A : Matrix ι ι ℝ) (b : E) (c : ℝ) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (A *ᵥ x) + dotProduct b x + c

end

section

variable {ι : Type u} [Fintype ι]

local notation "E" => ι → ℝ

/-- Evaluating `quadratic_affine_function A b c` at `x` gives
`(1 / 2) xᵀ A x + bᵀ x + c`. -/
@[simp] theorem quadratic_affine_function_apply (A : Matrix ι ι ℝ) (b x : E) (c : ℝ) :
    quadratic_affine_function A b c x =
      (1 / 2 : ℝ) * dotProduct x (A *ᵥ x) + dotProduct b x + c :=
  by
    classical
    rfl

/-- Helper for Definition 4.4: rewriting the affine-minus-quadratic integrand gives the
textbook objective from equation `(4.4.7)`. -/
lemma quadraticAffineObjective_rewrite (A : Matrix ι ι ℝ) (b y x : E) (c : ℝ) :
    dotProduct y x - quadratic_affine_function A b c x =
      (-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c := by
  -- Expand the quadratic-affine term once, then regroup the linear pieces.
  rw [quadratic_affine_function_apply, sub_dotProduct]
  ring_nf

/-- Helper for Definition 4.4: a Hermitian real matrix can be moved across the Euclidean
dot product. -/
lemma dotProduct_mulVec_swap_of_isHermitian
    (A : Matrix ι ι ℝ) (hHerm : A.IsHermitian) (u v : E) :
    dotProduct u (A *ᵥ v) = dotProduct (A *ᵥ u) v := by
  -- Replace the left action by the transpose action, then use Hermitian symmetry.
  have htranspose : Aᵀ *ᵥ u = A *ᵥ u := by
    simpa using congrArg (fun M : Matrix ι ι ℝ ↦ M *ᵥ u) hHerm
  calc
    dotProduct u (A *ᵥ v) = dotProduct (Aᵀ *ᵥ u) v := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose (A := Aᵀ) (x := u),
        Matrix.transpose_transpose]
    _ = dotProduct (A *ᵥ u) v := by
      rw [htranspose]

/-- Helper for Definition 4.4: the `EReal` supremum of a real-valued range equals a point value
exactly when that point is a global maximizer. -/
lemma ereal_sSup_coe_range_eq_iff_isMaxOn (φ : E → ℝ) (x : E) :
    sSup (Set.range fun z : E ↦ ((φ z : ℝ) : EReal)) = (φ x : EReal) ↔
      IsMaxOn φ Set.univ x := by
  -- Translate the supremum statement into the pointwise order condition on all `z`.
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

end

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

local notation "E" => ι → ℝ

/-- Helper for Definition 4.4: once `A *ᵥ xStar = y - b`, the rewritten objective differs from
its value at `xStar` by the negative quadratic remainder. -/
lemma rewrittenQuadraticObjective_completeSquare
    (A : Matrix ι ι ℝ) (b y : E) (c : ℝ) (xStar x : E)
    (hHerm : A.IsHermitian) (hxStar : A *ᵥ xStar = y - b) :
    (-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c =
      ((-(1 / 2 : ℝ)) * dotProduct xStar (A *ᵥ xStar) - dotProduct (b - y) xStar - c) -
        (1 / 2 : ℝ) * dotProduct (x - xStar) (A *ᵥ (x - xStar)) := by
  -- Rewrite the mixed terms using the stationarity equation at `xStar`.
  have hcross₁ : dotProduct x (A *ᵥ xStar) = dotProduct (y - b) x := by
    calc
      dotProduct x (A *ᵥ xStar) = dotProduct x (y - b) := by
        simpa [hxStar]
      _ = dotProduct (y - b) x := by
        rw [dotProduct_comm]
  have hcross₂ : dotProduct xStar (A *ᵥ x) = dotProduct (y - b) x := by
    rw [dotProduct_mulVec_swap_of_isHermitian A hHerm xStar x, hxStar]
  have hself : dotProduct xStar (A *ᵥ xStar) = dotProduct (y - b) xStar := by
    calc
      dotProduct xStar (A *ᵥ xStar) = dotProduct xStar (y - b) := by
        simpa [hxStar]
      _ = dotProduct (y - b) xStar := by
        rw [dotProduct_comm]
  have hexpand :
      dotProduct (x - xStar) (A *ᵥ (x - xStar)) =
        dotProduct x (A *ᵥ x) - dotProduct x (A *ᵥ xStar) -
          dotProduct xStar (A *ᵥ x) + dotProduct xStar (A *ᵥ xStar) := by
    -- Expand the quadratic remainder into the four standard bilinear terms.
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
    ring_nf
  -- Expand the remainder term and collect the quadratic, linear, and constant pieces.
  rw [sub_dotProduct, sub_dotProduct, hexpand]
  rw [hcross₁, hcross₂, hself]
  rw [sub_dotProduct, sub_dotProduct]
  ring_nf

/-- Helper for Definition 4.4: a positive-definite matrix makes the rewritten quadratic objective
attain its global maximum at the inverse solve point `A⁻¹ *ᵥ (y - b)`. -/
lemma rewrittenQuadraticObjective_isGreatest_of_posDef
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (b y : E) (c : ℝ) :
    IsGreatest
      (Set.range fun z : E ↦
        (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c)
      ((-(1 / 2 : ℝ)) * dotProduct (A⁻¹ *ᵥ (y - b)) (A *ᵥ (A⁻¹ *ᵥ (y - b))) -
        dotProduct (b - y) (A⁻¹ *ᵥ (y - b)) - c) := by
  let _ : Invertible A := hA.isUnit.invertible
  let xStar : E := A⁻¹ *ᵥ (y - b)
  have hxStar : A *ᵥ xStar = y - b := by
    -- The explicit maximizer solves the linear stationarity equation by matrix inversion.
    calc
      A *ᵥ xStar = A *ᵥ (A⁻¹ *ᵥ (y - b)) := by
        rfl
      _ = (A * A⁻¹) *ᵥ (y - b) := by
        rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix ι ι ℝ) *ᵥ (y - b) := by
        rw [Matrix.mul_inv_of_invertible]
      _ = y - b := by
        rw [Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · exact ⟨xStar, rfl⟩
  · rintro _ ⟨x, rfl⟩
    have hnonneg : 0 ≤ dotProduct (x - xStar) (A *ᵥ (x - xStar)) := by
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg (x - xStar)
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * dotProduct (x - xStar) (A *ᵥ (x - xStar)) := by
      nlinarith
    have hsquare :=
      rewrittenQuadraticObjective_completeSquare A b y c xStar x hA.isHermitian hxStar
    -- The complete-square identity reduces the upper-bound claim to nonnegativity.
    linarith

-- Proof sketch: apply `conjugate_function_apply` to the `EReal`-valued lift of
-- `quadratic_affine_function A b c`. The coordinate pairing identified by `dotProductEquiv`
-- evaluates to `dotProduct y x`, yielding the displayed supremum formula.
/-- Evaluating the Fenchel conjugate of `quadratic_affine_function A b c` at `y` gives the
defining `sSup` of the values `yᵀ x - (1 / 2) xᵀ A x - bᵀ x - c`. -/
theorem quadratic_affine_function_conjugate_apply (A : Matrix ι ι ℝ)
    (b y : E) (c : ℝ) :
    conjugate_function (fun x : E ↦ (quadratic_affine_function A b c x : EReal))
        (dotProductEquiv ℝ ι y) =
      sSup (Set.range fun x : E ↦
        ((dotProduct y x - quadratic_affine_function A b c x : ℝ) : EReal)) := by
  -- Compare the two defining suprema by identifying the dual pairing with `dotProduct`.
  rw [conjugate_function_apply]
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simp [dotProductEquiv]
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simp [dotProductEquiv]

-- Proof sketch: start from `quadratic_affine_function_conjugate_apply` and regroup the real
-- integrand by distributivity to rewrite `yᵀ x - bᵀ x` as `-(b - y)ᵀ x`.
/-- Companion rewrite: for `f(x) = (1 / 2) xᵀ A x + bᵀ x + c` on `ι → ℝ`, hence on `ℝ^n` when
`ι = Fin n`, the conjugate `f*(y)` is the supremum of the rewritten objective from equation
`(4.4.7)`, namely `-(1 / 2) xᵀ A x - (b - y)ᵀ x - c`. -/
theorem quadratic_affine_function_conjugate_apply_rewrite (A : Matrix ι ι ℝ)
    (b y : E) (c : ℝ) :
    conjugate_function (fun x : E ↦ (quadratic_affine_function A b c x : EReal))
        (dotProductEquiv ℝ ι y) =
      sSup (Set.range fun x : E ↦
        (((-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c : ℝ) :
          EReal)) := by
  -- Rewrite the range pointwise using the textbook normalization `(4.4.7)`.
  rw [quadratic_affine_function_conjugate_apply]
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    exact congrArg (fun t : ℝ ↦ (t : EReal)) (quadraticAffineObjective_rewrite A b y x c).symm
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    exact congrArg (fun t : ℝ ↦ (t : EReal)) (quadraticAffineObjective_rewrite A b y x c)

-- Proof sketch: this is the quadratic specialization of the chapter bridge from conjugate values
-- to `IsMaxOn`, after rewriting the affine-minus-quadratic objective into equation `(4.4.7)`.
/-- Companion bridge: evaluating the conjugate of `quadratic_affine_function A b c` at `y`
equals the value of the rewritten objective at `x` if and only if `x` is an argmax of that
objective on the whole finite product space. -/
theorem quadratic_affine_function_conjugate_eq_iff_isMaxOn
    (A : Matrix ι ι ℝ) (b y : E) (c : ℝ) (x : E) :
    conjugate_function (fun z : E ↦ (quadratic_affine_function A b c z : EReal))
        (dotProductEquiv ℝ ι y) =
      (((-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c : ℝ) : EReal) ↔
      IsMaxOn
        (fun z : E ↦
          (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c)
        Set.univ x := by
  -- Pass from the rewritten `sSup` formula to the standard `IsMaxOn` characterization.
  rw [quadratic_affine_function_conjugate_apply_rewrite]
  simpa using
    ereal_sSup_coe_range_eq_iff_isMaxOn
      (fun z : E ↦ (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c) x

-- Proof sketch: combine `quadratic_affine_function_conjugate_apply_rewrite` with positive-definite
-- attainment of the quadratic objective. The hypothesis `hA : A.PosDef` is the formal
-- `A ∈ 𝕊_{++}^n` assumption needed for existence of a maximizer, and the maximized integrand is
-- exactly the rewritten objective from equation `(4.4.7)`.
/-- Definition 4.4: if `A ∈ 𝕊_{++}^n` and
`f(x) = (1 / 2) xᵀ A x + bᵀ x + c`, then for every `y` the conjugate `f*(y)` is the maximum of
the rewritten objective from equation `(4.4.7)`,
`x ↦ -(1 / 2) xᵀ A x - (b - y)ᵀ x - c`, and that maximum is attained. -/
theorem quadratic_affine_function_conjugate_attainsMaximum
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (b y : E) (c : ℝ) :
    ∃ x : E,
      conjugate_function (fun z : E ↦ (quadratic_affine_function A b c z : EReal))
          (dotProductEquiv ℝ ι y) =
        (((-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c : ℝ) : EReal) ∧
      IsGreatest
        (Set.range fun z : E ↦
          (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c)
        ((-(1 / 2 : ℝ)) * dotProduct x (A *ᵥ x) - dotProduct (b - y) x - c) := by
  let x : E := A⁻¹ *ᵥ (y - b)
  have hgreatest := rewrittenQuadraticObjective_isGreatest_of_posDef A hA b y c
  have hmax :
      IsMaxOn
        (fun z : E ↦
          (-(1 / 2 : ℝ)) * dotProduct z (A *ᵥ z) - dotProduct (b - y) z - c)
        Set.univ x := by
    -- Turn the range-level greatest-element certificate into the pointwise max condition.
    rw [isMaxOn_univ_iff]
    intro z
    exact hgreatest.2 (Set.mem_range_self z)
  refine ⟨x, ?_, ?_⟩
  · -- The local argmax bridge identifies the conjugate value with the objective at `x`.
    exact (quadratic_affine_function_conjugate_eq_iff_isMaxOn A b y c x).2 hmax
  · simpa [x] using hgreatest

end
