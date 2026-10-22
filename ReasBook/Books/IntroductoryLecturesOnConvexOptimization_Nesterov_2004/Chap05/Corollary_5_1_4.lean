/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Corollary 5.1.4 lies in the Chapter 5 self-concordance / one-dimensional slice domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner for
  self-concordance on an open convex domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`, the canonical
  local norm owner;
* `associatedUnivariateFunctionDomain` from `Chap05/Definition_5_0_12`, the source-facing owner
  for the reciprocal local-norm slice domain.

Best owner abstraction:
* source-facing: the natural parameter domain of the associated univariate reciprocal local-norm
  function along `t ↦ x + t • h`;
* core/canonical: the Hessian local norm `‖h‖[f; x + t • h]`;
* bridge/view: the textbook expansion
  `0 < inner ℝ h ((fderiv ℝ (∇ f) (x + t • h)) h)`.

Primitive data:
* a domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`;
* a self-concordant objective `f`;
* a base point `x`;
* a direction `h` with positive local norm at `x`.

Derived API:
* the slice-domain owner `associatedUnivariateFunctionDomain dom f x h`;
* the interval inclusion corollary below, exposed as an owner-level method of
  `IsSelfConcordantOnWith`.

This corollary therefore reuses `associatedUnivariateFunctionDomain` directly as its public owner
and introduces no parallel local slice-domain alias. Its theorem surface follows the surrounding
Chapter 5 owner pattern by living in `namespace IsSelfConcordantOnWith`.
-/

namespace IsSelfConcordantOnWith

/-- Helper for Corollary 5 1 4: at a domain point of a self-concordant function, the Hessian
local norm scales by the absolute value of the scalar. -/
private theorem hessianLocalNorm_smul_eq_abs
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {z u : E} (hz : z ∈ dom) (a : ℝ) :
    ‖a • u‖[f; z] = |a| * ‖u‖[f; z] := by
  have hquad : 0 ≤ inner ℝ u (hessian f z u) := hself.hessian_posSemidef hz u
  -- Rewrite the scaled quadratic form before taking square roots.
  calc
    ‖a • u‖[f; z] = Real.sqrt ((a * a) * inner ℝ u (hessian f z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f z u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[f; z] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

-- Proof sketch: restrict `f` to the affine slice `t ↦ x + t • h`. Under the source-faithful
-- positivity hypothesis `0 < (Mf : ℝ) * ‖h‖[f; x]`, self-concordance bounds the derivative of the
-- reciprocal local norm by `Mf`, so the reciprocal local norm stays positive on the displayed
-- interval; equivalently, the associated univariate function remains defined there.
/-- Corollary 5 1 4: if `f` is self-concordant on an open convex domain `dom` and `x ∈ dom`,
then the natural domain of the associated univariate function
`t ↦ (⟪∇² f (x + t • h) h, h⟫)^{-1/2}` contains the interval
`(-1 / (M_f ‖h‖[f; x]), 1 / (M_f ‖h‖[f; x]))` whenever the reciprocal radius is well-defined,
that is, under `0 < (M_f : ℝ) * ‖h‖[f; x]`. -/
theorem associatedUnivariateFunctionDomain_contains_interval
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) {x h : E} (hx : x ∈ dom)
    (hMh : 0 < (Mf : ℝ) * ‖h‖[f; x]) :
    Set.Ioo (-(1 / ((Mf : ℝ) * ‖h‖[f; x]))) (1 / ((Mf : ℝ) * ‖h‖[f; x])) ⊆
      associatedUnivariateFunctionDomain dom f x h := by
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have hnormx_nonneg : 0 ≤ ‖h‖[f; x] := hessianLocalNorm_nonneg f x h
  have hMf_pos : 0 < (Mf : ℝ) := by
    nlinarith
  have hnormx_pos : 0 < ‖h‖[f; x] := by
    nlinarith
  intro t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · -- At the base point, the defining positivity hypothesis gives the slice-domain membership.
    exact
      (mem_associatedUnivariateFunctionDomain_iff dom f x h 0).2
        ⟨by simpa, by simpa using hnormx_pos⟩
  · have habs :
        |t| < 1 / ((Mf : ℝ) * ‖h‖[f; x]) := by
      rw [abs_lt]
      constructor
      · linarith [ht.1]
      · exact ht.2
    have hdisp_mul_lt : |t| * ((Mf : ℝ) * ‖h‖[f; x]) < 1 := by
      exact (lt_div_iff₀ hMh).1 habs
    have hdisp_lt : |t| * ‖h‖[f; x] < 1 / (Mf : ℝ) := by
      exact
        (lt_div_iff₀ hMf_pos).2
          (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdisp_mul_lt)
    have hy_dikin : x + t • h ∈ openDikinEllipsoid f x (1 / (Mf : ℝ)) := by
      -- Convert the interval bound on `t` into the Dikin-radius bound for the displacement
      -- `t • h`.
      rw [mem_openDikinEllipsoid_iff]
      calc
        ‖(x + t • h) - x‖[f; x] = ‖t • h‖[f; x] := by simp
        _ = |t| * ‖h‖[f; x] := hessianLocalNorm_smul_eq_abs hself hx t
        _ < 1 / (Mf : ℝ) := hdisp_lt
    have hy : x + t • h ∈ dom :=
      hself.openDikinEllipsoid_inv_constant_subset hx hy_dikin
    have hdisp_base_pos : 0 < ‖(x + t • h) - x‖[f; x] := by
      -- The base local norm of the displacement is positive because `t ≠ 0` and `‖h‖[f; x] > 0`.
      calc
        0 < |t| * ‖h‖[f; x] := by
          exact mul_pos (abs_pos.mpr ht0) hnormx_pos
        _ = ‖t • h‖[f; x] := (hessianLocalNorm_smul_eq_abs hself hx t).symm
        _ = ‖(x + t • h) - x‖[f; x] := by simp
    have hdisp_nonneg : 0 ≤ ‖(x + t • h) - x‖[f; x] :=
      hessianLocalNorm_nonneg f x ((x + t • h) - x)
    have hden_pos :
        0 < 1 + (Mf : ℝ) * ‖(x + t • h) - x‖[f; x] := by
      nlinarith
    have hdisp_y_lower :
        ‖(x + t • h) - x‖[f; x + t • h] ≥
          ‖(x + t • h) - x‖[f; x] /
            (1 + (Mf : ℝ) * ‖(x + t • h) - x‖[f; x]) :=
      hself.displacement_localNorm_lower_bound hx hy
    have hdisp_y_pos : 0 < ‖(x + t • h) - x‖[f; x + t • h] := by
      have hrhs_pos :
          0 <
            ‖(x + t • h) - x‖[f; x] /
              (1 + (Mf : ℝ) * ‖(x + t • h) - x‖[f; x]) := by
        exact div_pos hdisp_base_pos hden_pos
      exact lt_of_lt_of_le hrhs_pos hdisp_y_lower
    have hnormy_nonneg : 0 ≤ ‖h‖[f; x + t • h] :=
      hessianLocalNorm_nonneg f (x + t • h) h
    have hnormy_pos : 0 < ‖h‖[f; x + t • h] := by
      have hscaled_pos : 0 < |t| * ‖h‖[f; x + t • h] := by
        calc
          0 < ‖(x + t • h) - x‖[f; x + t • h] := hdisp_y_pos
          _ = ‖t • h‖[f; x + t • h] := by simp
          _ = |t| * ‖h‖[f; x + t • h] := hessianLocalNorm_smul_eq_abs hself hy t
      have habs_pos : 0 < |t| := abs_pos.mpr ht0
      nlinarith
    -- The affine point lies in `dom`, and the displacement lower bound keeps the local norm
    -- positive there.
    exact (mem_associatedUnivariateFunctionDomain_iff dom f x h t).2 ⟨hy, hnormy_pos⟩

end IsSelfConcordantOnWith

end
