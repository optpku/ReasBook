/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped ConvexAnalysis BInducedNorm

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-smoothing / dual-norm domain.

Relevant sampled declarations in this domain:
- `fenchelSmoothApproximation` in `Chap06/Definition_6_2`, the chapter owner for the quadratically
  regularized Fenchel supremum;
- `fenchelSmoothApproximation_apply` in `Chap06/Definition_6_2`, the owner evaluation theorem;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the canonical dual object feeding the smoothing
  construction;
- `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the finite-value domain of an
  `EReal`-valued function.

Best owner abstraction:
- source-facing: the approximation-error bound for `fenchelSmoothApproximation`;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: its zero-penalty specialization, which is exactly the unsmoothed Fenchel supremum
  model used in the textbook statement.

Primitive data:
- `B : BilinForm ℝ E` with positive-definiteness;
- `f : E → EReal`;
- the smoothing parameter `μ`, the radius bound `L`, and the dual-domain bound `hdual`.

Derived API:
- the zero-penalty expansion `fenchelSmoothApproximation_zero_apply`;
- the owner-level comparison with the zero-penalty specialization
  `fenchelSmoothApproximation_zero_bounds`;
- the source-facing approximation-error theorem below.

Source/core/bridge triage:
- source-facing: the error estimate itself;
- core/canonical: `fenchelSmoothApproximation`;
- bridge/view: the theorem identifying the unsmoothed Fenchel supremum with the `μ = 0`
  specialization of that owner, and the source-facing bridge from that owner-level comparison back
  to `f x`.

This item does not introduce a second unsmoothed owner. The previous local
`fenchelApproximationMaximand` / `fenchelApproximation` pair duplicated the Chapter 6 owner
`fenchelSmoothApproximation`; the unsmoothed model is only the zero-penalty specialization of that
owner, so this file now exposes it only as a bridge theorem.
-/

/-- Setting the smoothing parameter to `0` recovers the unsmoothed Fenchel supremum model. -/
@[simp] theorem fenchelSmoothApproximation_zero_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (x : E) :
    fenchelSmoothApproximation B f 0 x =
      sSup ((fun s : Dual ℝ E ↦ (s x : EReal) - fenchelConjugate f s) ''
        dom (fenchelConjugate f)) := by
  simp [fenchelSmoothApproximation, fenchelSmoothApproximationMaximand]

/-- Helper for Text 6 1 1 Smoothing Approximation Error: the bilinear-form dual norm is
nonnegative. -/
private lemma bilinForm_dualNorm_nonneg
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (s : Dual ℝ E) :
    0 ≤ ‖s‖[B,*] := by
  have hPos : B.toQuadraticMap.PosDef := Fact.out
  let A : BilinForm ℝ E := B.toQuadraticMap.associated
  have hA_diag : ∀ x : E, A x x = B x x := by
    intro x
    simpa [A, LinearMap.BilinMap.toQuadraticMap_apply] using
      (QuadraticMap.associated_eq_self_apply ℝ B.toQuadraticMap x)
  have hA_symm : A.IsSymm := by
    exact ⟨QuadraticMap.associated_isSymm ℝ B.toQuadraticMap⟩
  have hA_pos : A.toQuadraticMap.PosDef := by
    intro x hx
    -- The associated bilinear form has the same quadratic map as `B`.
    simpa [LinearMap.BilinMap.toQuadraticMap_apply, hA_diag x] using (hPos x hx)
  have hdual_eq : ‖s‖[B,*] = ‖s‖*[A | hA_pos] := by
    -- Both dual norms are support functions over the same primal unit ball.
    rw [LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall,
      LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      simpa [LinearMap.BilinForm.primalSeminorm_apply, hA_diag x] using hx
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      simpa [LinearMap.BilinForm.primalSeminorm_apply, hA_diag x] using hx
  -- Switch to the symmetric associated form, where the inverse-pairing formula gives
  -- nonnegativity via `Real.sqrt_nonneg`.
  rw [hdual_eq]
  rw [A.dualNorm_apply hA_symm hA_pos s]
  exact Real.sqrt_nonneg _

/-- Helper for Text 6 1 1 Smoothing Approximation Error: adding the quadratic penalty can only
decrease the Fenchel smoothing maximand. -/
private lemma fenchel_smooth_maximand_le_zero_penalty
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) (s : Dual ℝ E) :
    fenchelSmoothApproximationMaximand B f μ x s ≤
      fenchelSmoothApproximationMaximand B f 0 x s := by
  have hpen_nonneg : 0 ≤ (((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hpen_nonneg_ereal :
      (0 : EReal) ≤ ((((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hpen_nonneg
  -- Peel off the nonnegative penalty from the common affine-Fenchel part.
  have hle :
      fenchelSmoothApproximationMaximand B f 0 x s ≤
        fenchelSmoothApproximationMaximand B f 0 x s +
          ((((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
    exact le_add_of_nonneg_right hpen_nonneg_ereal
  exact EReal.sub_le_of_le_add (by simpa [fenchelSmoothApproximationMaximand] using hle)

/-- Helper for Text 6 1 1 Smoothing Approximation Error: on the dual domain, removing the
quadratic penalty changes the maximand by at most the fixed budget `((μ * L^2) / 2 : NNReal)`. -/
private lemma zero_penalty_maximand_le_fenchel_smooth_maximand_add_budget
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) {μ L : NNReal} (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L) :
    fenchelSmoothApproximationMaximand B f 0 x s ≤
      fenchelSmoothApproximationMaximand B f μ x s +
        (((μ * L ^ 2) / 2 : NNReal) : EReal) := by
  have hnorm_nonneg : 0 ≤ ‖s‖[B,*] := bilinForm_dualNorm_nonneg B s
  have hsq : ‖s‖[B,*] ^ 2 ≤ (L : ℝ) ^ 2 := by
    nlinarith [hdual s hs, hnorm_nonneg, L.2]
  have hcoeff_nonneg : 0 ≤ (μ : ℝ) / 2 := by
    positivity
  have hpen_le :
      ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 ≤
        (((μ * L ^ 2) / 2 : NNReal) : ℝ) := by
    have hscaled :
        ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 ≤
          ((μ : ℝ) / 2) * (L : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq hcoeff_nonneg
    calc
      ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 ≤ ((μ : ℝ) / 2) * (L : ℝ) ^ 2 := hscaled
      _ = (((μ * L ^ 2) / 2 : NNReal) : ℝ) := by
        ring_nf
        simp [NNReal.coe_mul, NNReal.coe_pow]
  have hreal :
      ((s x : ℝ) - (fenchelConjugate f s).toReal - ((0 : ℝ) / 2) * ‖s‖[B,*] ^ 2) ≤
        ((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2) +
          (((μ * L ^ 2) / 2 : NNReal) : ℝ) := by
    -- The domain bound controls the lost quadratic penalty on the real surface.
    linarith
  rw [fenchelSmoothApproximationMaximand_eq_coe B f 0 x hs,
    fenchelSmoothApproximationMaximand_eq_coe B f μ x hs]
  have hcast :
      ((((s x : ℝ) - (fenchelConjugate f s).toReal - ((0 : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ)) :
          EReal) ≤
        (((((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2) +
            (((μ * L ^ 2) / 2 : NNReal) : ℝ) : ℝ)) : EReal) := by
    exact_mod_cast hreal
  calc
    ((((s x : ℝ) - (fenchelConjugate f s).toReal - ((0 : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ)) :
        EReal) ≤
      (((((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2) +
          (((μ * L ^ 2) / 2 : NNReal) : ℝ) : ℝ)) : EReal) := hcast
    _ =
        ((((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ)) :
            EReal) + (((μ * L ^ 2) / 2 : NNReal) : EReal) := by
          rfl

-- Proof sketch: the upper bound follows because the smoothed maximand is obtained from the
-- unsmoothed one by subtracting the nonnegative penalty `(μ / 2) ‖s‖[B,*]^2`.
-- For the lower bound, use the domain estimate `‖s‖[B,*] ≤ L` on every dual point
-- contributing to the
-- supremum, so the penalization removes at most `(μ * L^2) / 2` from the Fenchel representation
-- of `f`.
/-- Under the dual-domain radius bound `‖s‖[B,*] ≤ L`, the zero-penalty specialization dominates
every smoothed value and differs from it by at most `((μ * L^2) / 2 : NNReal)`. This is the
owner-level smoothing comparison, before identifying the zero-penalty value with `f x`. -/
theorem fenchelSmoothApproximation_zero_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L) :
    fenchelSmoothApproximation B f 0 x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        fenchelSmoothApproximation B f 0 x - ((μ * L ^ 2) / 2 : NNReal) := by
  let S0 := fenchelSmoothApproximationMaximand B f 0 x '' dom (fenchelConjugate f)
  let Sμ := fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f)
  let budget : EReal := (((μ * L ^ 2) / 2 : NNReal) : EReal)
  have hsSup_upper : sSup Sμ ≤ sSup S0 := by
    -- Compare the two supremum sets pointwise via the nonnegative quadratic penalty.
    refine sSup_le ?_
    rintro y ⟨s, hs, rfl⟩
    exact
      (fenchel_smooth_maximand_le_zero_penalty B f μ x s).trans
        (le_sSup (Set.mem_image_of_mem _ hs))
  have hsSup_lower :
      sSup S0 ≤ sSup Sμ + budget := by
    -- Each zero-penalty value is within the uniform budget of its smoothed counterpart.
    refine sSup_le ?_
    rintro y ⟨s, hs, rfl⟩
    have hsμ_mem :
        fenchelSmoothApproximationMaximand B f μ x s ∈ Sμ :=
      Set.mem_image_of_mem _ hs
    have hsμ_le :
        fenchelSmoothApproximationMaximand B f μ x s ≤ sSup Sμ :=
      le_sSup hsμ_mem
    have hsμ_budget :
        fenchelSmoothApproximationMaximand B f μ x s + budget ≤ budget + sSup Sμ := by
      simpa [budget, add_comm, add_left_comm, add_assoc] using add_le_add_left hsμ_le budget
    exact
      (zero_penalty_maximand_le_fenchel_smooth_maximand_add_budget
          (μ := μ) (L := L) B f x hs hdual).trans
        (by simpa [budget, add_comm, add_left_comm, add_assoc] using hsμ_budget)
  constructor
  · simpa [fenchelSmoothApproximation_apply, S0, Sμ] using hsSup_upper
  · have hsSup_lower' :
        fenchelSmoothApproximation B f 0 x ≤
          fenchelSmoothApproximation B f μ x + budget := by
      simpa [fenchelSmoothApproximation_apply, S0, Sμ] using hsSup_lower
    have hbudget_ne_bot : budget ≠ ⊥ := by
      change (((((μ * L ^ 2) / 2 : NNReal) : ℝ)) : EReal) ≠ ⊥
      exact EReal.coe_ne_bot _
    have hbudget_ne_top : budget ≠ ⊤ := by
      change (((((μ * L ^ 2) / 2 : NNReal) : ℝ)) : EReal) ≠ ⊤
      exact EReal.coe_ne_top _
    -- Repackage the shifted supremum estimate into the target subtraction form.
    exact
      (EReal.sub_le_iff_le_add
        (.inl hbudget_ne_bot)
        (.inl hbudget_ne_top)).2
        (by simpa [budget] using hsSup_lower')

-- Proof sketch: apply the owner-level comparison `fenchelSmoothApproximation_zero_bounds` and
-- rewrite its zero-penalty endpoint with the source-facing representation hypothesis `hf`.
/-- Text 6 1 1 Smoothing Approximation Error: if `f` is represented by the Fenchel supremum model
associated to its Fenchel conjugate at `x`, equivalently by the zero-penalty specialization of
`fenchelSmoothApproximation` at that point, and every `s ∈ dom (fenchelConjugate f)` satisfies
the dual estimate
`‖s‖[B,*] ≤ L`, then the smoothed approximation `f_μ` lies between `f` and
`f - (μ * L^2) / 2` on the canonical `EReal` surface. -/
theorem fenchelSmoothApproximation_error_bounds
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal)
    {μ L : NNReal}
    (x : E)
    (hf : f x = fenchelSmoothApproximation B f 0 x)
    (hdual : ∀ s ∈ dom (fenchelConjugate f), ‖s‖[B,*] ≤ L)
    :
    f x ≥ fenchelSmoothApproximation B f μ x ∧
      fenchelSmoothApproximation B f μ x ≥
        f x - ((μ * L ^ 2) / 2 : NNReal) := by
  simpa [hf] using fenchelSmoothApproximation_zero_bounds B f x hdual

end
