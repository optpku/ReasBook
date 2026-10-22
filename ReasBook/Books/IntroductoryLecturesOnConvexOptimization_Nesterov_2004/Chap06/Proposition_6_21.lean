/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped BigOperators Pointwise

universe u

variable {ι : Type*} [Fintype ι]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "G" => ι ⊕ ι
local notation "E₂" => PiLp 1 (fun _ : G ↦ ℝ)

/- Proposition 6.21 lies in the operator-norm bridge domain for the same row data that feed the
Chapter 6 owner `maxAbsoluteValueOptimizationObjective`.

Primary domain:
- canonical operator norms of continuous linear maps `E →L[ℝ] E₂`;
- the finite `ℓ¹` norm on `PiLp 1`;
- the signed row stack `a_i, -a_i` indexed by `ι ⊕ ι`, viewed through canonical product assembly.

Sampled owner-style declarations:
- `maxAbsoluteValueOptimizationObjective` in `Definition_6_21`, the nearby source-facing Chapter 6
  owner for the max-absolute-value optimization data;
- `ContinuousLinearMap.pi`, the canonical owner assembling a finite family of continuous linear
  functionals into a product-valued continuous linear map;
- `PiLp.continuousLinearEquiv`, the canonical equivalence between a finite product and the
  corresponding `PiLp` space;
- `ContinuousLinearMap.sSup_sphere_eq_norm`, the canonical operator-norm support formula.

Best owner abstraction:
- source-facing: the signed stacking operator-norm identity attached to the row family `a`;
- core/canonical: the ambient norm `‖·‖` on the canonical stacked map expression;
- bridge/view: the pointwise `ℓ¹` norm formula for that canonical stack.

Primitive data:
- a finite row family `a : ι → StrongDual ℝ E`.

Derived API:
- the source-facing signed stack `signedRowStack a`;
- the canonical stacked-map expression implementing `signedRowStack`, built from
  `ContinuousLinearMap.pi` and `PiLp.continuousLinearEquiv`;
- its pointwise `ℓ¹` norm identity;
- the operator-norm equality and the source bounds from Proposition 6.21.

Source/core/bridge triage:
- source-facing: `signedRowStack` together with
  `signedRowStack_opNorm_eq_two_mul_sSup_abs_rowSum` and `signedRowStack_opNorm_bounds`;
- core/canonical: `ContinuousLinearMap.pi`, `PiLp.continuousLinearEquiv`, and the ambient
  operator norm;
- bridge/view: `signedRowStack_norm_eq_two_mul_sum_abs`.

This file therefore introduces the source-facing signed stack only once, as the short bridge
`signedRowStack a`, and states Proposition 6.21 on that owner surface. Its implementation remains
the canonical composition of `ContinuousLinearMap.pi` with `PiLp.continuousLinearEquiv`.
-/

/-- The canonical signed stack `Â[a]` attached to the row family `a`, with coordinates `aᵢ` and
`-aᵢ` on the signed index set `ι ⊕ ι`. -/
abbrev signedRowStack (a : ι → StrongDual ℝ E) : E →L[ℝ] E₂ :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : G ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim a (-a)))

local notation "Â[" a "]" => signedRowStack a

-- Proof sketch: expand the `ℓ¹` norm in `PiLp 1`; the signed stack has coordinates
-- `a_i x` and `-a_i x` over `ι ⊕ ι`, so the absolute values add to
-- `2 * ∑ j, |a j x|`.
/-- For the canonical signed stack attached to the row family `a`, the `ℓ¹` norm of the image of
`x` is twice the sum of the absolute row evaluations. -/
theorem signedRowStack_norm_eq_two_mul_sum_abs
    (a : ι → StrongDual ℝ E) (x : E) :
    ‖Â[a] x‖ = 2 * ∑ j, |a j x| := by
  -- Expand the `PiLp 1` norm and split the signed coordinates into the two copies of `ι`.
  simp [signedRowStack, PiLp.norm_eq_sum, Fintype.sum_sum_type, two_mul, Real.norm_eq_abs,
    abs_neg]

-- Proof sketch: combine `signedRowStack_norm_eq_two_mul_sum_abs` with
-- `ContinuousLinearMap.sSup_sphere_eq_norm` for the canonical stacked map.
/-- Proposition 6.21: the operator norm of the canonical signed stack equals twice the supremum
over the unit sphere of the sum of the absolute row evaluations. -/
theorem signedRowStack_opNorm_eq_two_mul_sSup_abs_rowSum
    (a : ι → StrongDual ℝ E) :
    ‖Â[a]‖ =
      2 * sSup ((fun x : E ↦ ∑ j, |a j x|) '' sphere (0 : E) 1) := by
  let S : Set ℝ := (fun x : E ↦ ∑ j, |a j x|) '' sphere (0 : E) 1
  -- Rewrite the operator norm as the supremum of the pointwise stacked norms on the unit sphere.
  calc
    ‖Â[a]‖ = sSup ((fun x : E ↦ ‖Â[a] x‖) '' sphere (0 : E) 1) := by
      simpa using (ContinuousLinearMap.sSup_sphere_eq_norm (Â[a])).symm
    _ = sSup ((2 : ℝ) • S) := by
      -- Each pointwise stacked norm is exactly `2` times the absolute-row sum at the same `x`.
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨∑ j, |a j x|, ⟨x, hx, rfl⟩, ?_⟩
        simpa [smul_eq_mul] using (signedRowStack_norm_eq_two_mul_sum_abs a x).symm
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨x, hx, by simpa [smul_eq_mul] using signedRowStack_norm_eq_two_mul_sum_abs a x⟩
    _ = 2 * sSup S := by
      simpa [smul_eq_mul] using
        (Real.sSup_smul_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) S)

/-- Helper for Proposition 6.21: one row contribution is bounded by the full absolute row sum. -/
lemma single_row_abs_le_abs_rowSum
    (a : ι → StrongDual ℝ E) (j : ι) (x : E) :
    |a j x| ≤ ∑ i, |a i x| := by
  -- Compare the `j`-th term with the full nonnegative finite sum.
  simpa using
    (Finset.single_le_sum
      (f := fun i : ι ↦ |a i x|)
      (fun i _ ↦ abs_nonneg (a i x))
      (Finset.mem_univ j))

/-- Helper for Proposition 6.21: on the unit sphere, the absolute row sum is bounded by the sum
of the row operator norms. -/
lemma abs_rowSum_le_sum_rowNorm_on_sphere
    (a : ι → StrongDual ℝ E) {x : E} (hx : x ∈ sphere (0 : E) 1) :
    ∑ j, |a j x| ≤ ∑ j, ‖a j‖ := by
  have hxnorm : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx
  -- Bound each row evaluation by the row norm and sum the coordinatewise estimates.
  refine Finset.sum_le_sum fun j _ ↦ ?_
  calc
    |a j x| = ‖a j x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖a j‖ * ‖x‖ := (a j).le_opNorm x
    _ = ‖a j‖ := by simp [hxnorm]

-- Proof sketch: use Proposition 6.21 together with `∑ i |a_i x| ≥ |a_j x|` for each `j` and the
-- bound `|a_j x| ≤ ‖a_j‖` on the unit sphere.
/-- Proposition 6.21 yields the source lower and upper bounds
`2 * max_j ‖a_j‖ ≤ ‖Â‖ ≤ 2 * ∑ j ‖a_j‖` for the canonical signed stack `Â`. -/
theorem signedRowStack_opNorm_bounds
    (a : ι → StrongDual ℝ E) [Nonempty ι] :
    2 * Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ ‖a j‖) ≤ ‖Â[a]‖ ∧
      ‖Â[a]‖ ≤ 2 * ∑ j, ‖a j‖ := by
  have hrow_bound : ∀ j : ι, 2 * ‖a j‖ ≤ ‖Â[a]‖ := by
    intro j
    have hscaled : ‖(2 : ℝ) • a j‖ ≤ ‖Â[a]‖ := by
      refine ContinuousLinearMap.opNorm_le_bound ((2 : ℝ) • a j) (by positivity) ?_
      intro x
      calc
        ‖((2 : ℝ) • a j) x‖ = 2 * |a j x| := by
          simp [Real.norm_eq_abs]
        _ ≤ ‖Â[a] x‖ := by
          calc
            2 * |a j x| ≤ 2 * ∑ i, |a i x| := by
              exact mul_le_mul_of_nonneg_left (single_row_abs_le_abs_rowSum a j x) (by norm_num)
            _ = ‖Â[a] x‖ := (signedRowStack_norm_eq_two_mul_sum_abs a x).symm
        _ ≤ ‖Â[a]‖ * ‖x‖ := (Â[a]).le_opNorm x
    simpa [norm_smul] using hscaled
  constructor
  · obtain ⟨j, -, hsup⟩ :=
      Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun j : ι ↦ ‖a j‖)
    calc
      2 * Finset.univ.sup' Finset.univ_nonempty (fun j : ι ↦ ‖a j‖) = 2 * ‖a j‖ := by
        rw [hsup]
      _ ≤ ‖Â[a]‖ := hrow_bound j
  · -- Bound the stacked map pointwise by the row-norm sum and apply the operator-norm criterion.
    calc
      ‖Â[a]‖ ≤ 2 * ∑ j, ‖a j‖ := by
        refine ContinuousLinearMap.opNorm_le_bound (Â[a]) (by positivity) ?_
        intro x
        calc
          ‖Â[a] x‖ = 2 * ∑ j, |a j x| := signedRowStack_norm_eq_two_mul_sum_abs a x
          _ ≤ 2 * ∑ j, ‖a j‖ * ‖x‖ := by
            gcongr with j
            calc
              |a j x| = ‖a j x‖ := by rw [Real.norm_eq_abs]
              _ ≤ ‖a j‖ * ‖x‖ := (a j).le_opNorm x
          _ = 2 * ∑ j, ‖a j‖ * ‖x‖ := rfl
          _ = 2 * ((∑ j, ‖a j‖) * ‖x‖) := by rw [Finset.sum_mul]
          _ = (2 * ∑ j, ‖a j‖) * ‖x‖ := by ring

end
