/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Matrix
open PointedCone

noncomputable section

section

variable {m n : ℕ}

/-- The cone cut out by the coordinatewise inequalities `A *ᵥ x ≤ 0`, realized as the preimage of
the positive cone under the matrix linear map. -/
abbrev matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) : PointedCone ℝ (Fin n → ℝ) :=
  (positive ℝ (Fin m → ℝ)).comap (-A).mulVecLin

/-- The Euclidean-dual realization of `transpose_nonnegative_cone A`, transported along
`dotProductEquiv ℝ (Fin n)`. -/
abbrev transpose_nonnegative_dual_cone (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (Module.Dual ℝ (Fin n → ℝ)) :=
  ((transpose_nonnegative_cone A).map (dotProductEquiv ℝ (Fin n)) :
    PointedCone ℝ (Module.Dual ℝ (Fin n → ℝ)))

@[simp]
theorem mem_matrix_nonpositive_cone (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ matrix_nonpositive_cone A ↔ A *ᵥ x ≤ (0 : Fin m → ℝ) := by
  simp [matrix_nonpositive_cone]

@[simp]
theorem mem_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Module.Dual ℝ (Fin n → ℝ)) :
    y ∈ transpose_nonnegative_dual_cone A ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), dotProductEquiv ℝ (Fin n) (Aᵀ *ᵥ z) = y := by
  change
    y ∈ ((transpose_nonnegative_cone A).map (dotProductEquiv ℝ (Fin n)) :
      PointedCone ℝ (Module.Dual ℝ (Fin n → ℝ))) ↔
      ∃ z ∈ Set.Ici (0 : Fin m → ℝ), dotProductEquiv ℝ (Fin n) (Aᵀ *ᵥ z) = y
  rw [mem_map]
  constructor
  · rintro ⟨v, hv, hy⟩
    rcases (mem_transpose_nonnegative_cone A v).mp hv with ⟨z, hz, rfl⟩
    exact ⟨z, hz, hy⟩
  · rintro ⟨z, hz, hy⟩
    exact ⟨Aᵀ *ᵥ z, (mem_transpose_nonnegative_cone A _).2 ⟨z, hz, rfl⟩, hy⟩

-- Proof sketch: rewrite membership in
-- `polar_cone (matrix_nonpositive_cone A)` as the implication
-- `A *ᵥ x ≤ 0 → dotProduct y x ≤ 0` for every `x`; then use the bridge
-- `farkas_lemma_second_formulation_iff_mem_transpose_nonnegative_cone` to identify the
-- representing vector with
-- the owner-side image of the positive cone under `Aᵀ.mulVecLin`, and finally transport along
-- `dotProductEquiv ℝ (Fin n)`.
/-- Helper for Example 2.7: the coordinate representative of a dual vector evaluates on `x` by the
usual dot product. -/
theorem dotProduct_dotProductEquiv_symm_apply
    (y : Module.Dual ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    dotProduct ((dotProductEquiv ℝ (Fin n)).symm y) x = y x := by
  -- Evaluate the identity `dotProductEquiv.symm_apply_apply` at the point `x`.
  have hpair :
      (dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm y)) x = y x := by
    exact congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f x)
      ((dotProductEquiv ℝ (Fin n)).apply_symm_apply y)
  -- Unfold `dotProductEquiv` once to expose the coordinate pairing.
  simpa [dotProductEquiv] using hpair

/-- Helper for Example 2.7: membership in the polar cone of `matrix_nonpositive_cone A` is the
Farkas-style implication written in coordinates through `dotProductEquiv ℝ (Fin n)`. -/
theorem mem_polar_cone_matrix_nonpositive_cone_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Module.Dual ℝ (Fin n → ℝ)) :
    y ∈ (matrix_nonpositive_cone A).polarCone ↔
      ∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) →
        dotProduct ((dotProductEquiv ℝ (Fin n)).symm y) x ≤ 0 := by
  constructor
  · intro hy x hx
    -- Convert polar membership into a bound on the pairing with every feasible `x`.
    have hy' : y ∈ polar_cone (matrix_nonpositive_cone A : Set (Fin n → ℝ)) :=
      (PointedCone.mem_polarCone _ _).mp hy
    have hyx : y x ≤ 0 :=
      (mem_polar_cone _ _).mp hy' x ((mem_matrix_nonpositive_cone A x).2 hx)
    -- Rewrite the dual evaluation in coordinates through `dotProductEquiv`.
    simpa [dotProduct_dotProductEquiv_symm_apply] using hyx
  · intro hy
    apply (PointedCone.mem_polarCone _ _).2
    rw [mem_polar_cone]
    intro x hx
    -- Turn set membership back into the matrix inequality hypothesis expected by Farkas.
    have hyx :
        dotProduct ((dotProductEquiv ℝ (Fin n)).symm y) x ≤ 0 :=
      hy x ((mem_matrix_nonpositive_cone A x).1 hx)
    -- Transport the coordinate pairing back to the dual evaluation.
    simpa [dotProduct_dotProductEquiv_symm_apply] using hyx

/-- Helper for Example 2.7: the Farkas implication for the representing vector of `y` is exactly
membership of `y` in the Euclidean-dual transpose cone. -/
theorem farkasImplication_iff_memTransposeNonnegativeDualCone
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Module.Dual ℝ (Fin n → ℝ)) :
    (∀ x : Fin n → ℝ, A *ᵥ x ≤ (0 : Fin m → ℝ) →
        dotProduct ((dotProductEquiv ℝ (Fin n)).symm y) x ≤ 0) ↔
      y ∈ transpose_nonnegative_dual_cone A := by
  constructor
  · intro hy
    -- Farkas gives a nonnegative multiplier whose transpose image represents `y`.
    rcases (farkas_lemma_second_formulation ((dotProductEquiv ℝ (Fin n)).symm y) A).mp hy with
      ⟨z, hz, hzEq⟩
    rw [mem_transpose_nonnegative_dual_cone]
    refine ⟨z, hz, ?_⟩
    -- Apply `dotProductEquiv` to move the certificate into the dual space.
    simpa using congrArg (dotProductEquiv ℝ (Fin n)) hzEq
  · intro hy
    rw [mem_transpose_nonnegative_dual_cone] at hy
    rcases hy with ⟨z, hz, hzEq⟩
    -- Pull the dual certificate back to coordinates before invoking Farkas.
    have hzEq' : Aᵀ *ᵥ z = (dotProductEquiv ℝ (Fin n)).symm y := by
      simpa using congrArg ((dotProductEquiv ℝ (Fin n)).symm) hzEq
    exact
      (farkas_lemma_second_formulation ((dotProductEquiv ℝ (Fin n)).symm y) A).mpr
        ⟨z, hz, hzEq'⟩

/-- The polar cone of the matrix inequality set consists exactly of Euclidean-dual vectors of the
form `Aᵀ *ᵥ λ` with `λ ≥ 0`. -/
theorem polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrix_nonpositive_cone A).polarCone = transpose_nonnegative_dual_cone A := by
  -- Route correction: keep the proof at the set-membership/API level and only transport through
  -- `dotProductEquiv` once, instead of unfolding the pointed-cone constructions in the main goal.
  ext y
  change y ∈ (matrix_nonpositive_cone A).polarCone ↔ y ∈ transpose_nonnegative_dual_cone A
  -- Chain the polar-cone normalization with the Farkas membership bridge.
  rw [mem_polar_cone_matrix_nonpositive_cone_iff]
  rw [farkasImplication_iff_memTransposeNonnegativeDualCone]

-- Proof sketch: combine the cone-case identity `σ_K = δ_{Kᵒ}` with the explicit description of
-- `polar_cone (matrix_nonpositive_cone A)` from
-- `polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone`.
/-- Example 2.7: for `S = {x : ℝ^n | A *ᵥ x ≤ 0}`, the support function `σ_S` is the indicator
function of the Euclidean-dual image `{(Aᵀ *ᵥ λ) | λ ∈ ℝ^m_+}`. -/
theorem support_function_matrix_nonpositive_cone_eq_indicator_transpose_nonnegative_dual_cone
    (A : Matrix (Fin m) (Fin n) ℝ) :
    σ_ (matrix_nonpositive_cone A) = δ_(transpose_nonnegative_dual_cone A) :=
    by
  -- Then apply the cone support-function identity and rewrite the polar cone explicitly.
  calc
    σ_ (matrix_nonpositive_cone A)
        = δ_((matrix_nonpositive_cone A).polarCone) :=
          by
            simpa using
              PointedCone.support_function_eq_indicatorFunction_polarCone
                (matrix_nonpositive_cone A)
    _ = δ_(transpose_nonnegative_dual_cone A) := by
          congr 1
          simpa using
            polar_cone_matrix_nonpositive_cone_eq_transpose_nonnegative_dual_cone A

end
