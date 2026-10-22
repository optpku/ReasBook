/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open WithLp (ofLp toLp)
open scoped Pointwise

section

variable {n : ℕ} [Nonempty (Fin n)]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)))

/-- Helper for Example 6.49: the transported standard simplex is nonempty. -/
lemma transported_stdSimplex_nonempty : (Δ : Set E).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  refine ⟨toLp 2 (Pi.single i 1), ?_⟩
  exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, rfl⟩

/-- Helper for Example 6.49: transporting the standard simplex through `toLp 2` preserves
convexity. -/
lemma convex_transported_stdSimplex : Convex ℝ (Δ : Set E) := by
  show Convex ℝ
    (((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap) ''
      (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)))
  exact
    (convex_stdSimplex ℝ (Fin n)).linear_image
      ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap)

/-- Helper for Example 6.49: the transported standard simplex is closed. -/
lemma isClosed_transported_stdSimplex : IsClosed (Δ : Set E) := by
  have hcompact : IsCompact (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) :=
    isCompact_stdSimplex ℝ (Fin n)
  show IsClosed ((fun z : Fin n → ℝ ↦ toLp 2 z) '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)))
  exact
    (hcompact.image
      (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ))).isClosed

/-- Helper for Example 6.49: the coordinatewise maximum is the support function of the transported
standard simplex in Euclidean coordinates. -/
lemma coordinatewiseMax_eq_support_function_primal_transported_stdSimplex
    (y : E) :
    (coordinatewiseMax y.ofLp : EReal) = σ[Δ] y := by
  calc
    (coordinatewiseMax y.ofLp : EReal)
        = support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) y.ofLp) := by
          simpa using coordinatewiseMax_eq_support_function_stdSimplex (x := y.ofLp)
    _ = σ[Δ] y := by
      -- Rewrite both support functions as suprema over their defining pairing images.
      rw [support_function_eq_sSup, support_function_apply]
      -- The coordinate pairing is exactly the Euclidean inner product after transporting by `toLp`.
      congr 1
      ext a
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨toLp 2 z, ?_, ?_⟩
        · exact ⟨z, hz, rfl⟩
        · change ((inner ℝ y (toLp 2 z) : ℝ) : EReal) =
            (((dotProductEquiv ℝ (Fin n) y.ofLp) z : ℝ) : EReal)
          rw [show inner ℝ y (toLp 2 z) = dotProduct y.ofLp z by
            simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp y.ofLp z)]
          simp [dotProductEquiv]
      · rintro ⟨u, hu, rfl⟩
        rcases hu with ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (((dotProductEquiv ℝ (Fin n) y.ofLp) z : ℝ) : EReal) =
          ((inner ℝ y (toLp 2 z) : ℝ) : EReal)
        rw [show inner ℝ y (toLp 2 z) = dotProduct y.ofLp z by
          simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp y.ofLp z)]
        simp [dotProductEquiv]

/-- Helper for Example 6.49: the scaled coordinatewise-max penalty is the scaled support function
of the transported standard simplex. -/
lemma coordinatewiseMax_penalty_eq_smul_support_function_primal_transported_stdSimplex
    (lam : ℝ) :
    (fun y : E ↦ (lam : EReal) * (coordinatewiseMax y.ofLp : EReal)) =
      (((lam : ℝ) : EReal) • σ[Δ]) := by
  funext y
  -- Evaluate the pointwise scalar action and substitute the support-function bridge.
  rw [Pi.smul_apply, coordinatewiseMax_eq_support_function_primal_transported_stdSimplex]
  simp [smul_eq_mul]

/- Example 6.49 is `source-facing`: the textbook object is the coordinatewise maximum on `ℝ^n`.
Domain sampling shows that the correct owner abstraction is the intrinsic Euclidean product
`EuclideanSpace ℝ (Fin n)`, not the coordinate model `Fin n → ℝ`, because the chapter's proximal
support-function formula already lives on the inner-product owner from Theorem 6.46. The
`bridge/view` ingredients are `coordinatewiseMax` from Chapter 3, the simplex support-function
identity `coordinatewiseMax_eq_support_function_stdSimplex` from Chapter 4, and the coordinate
realization `y.ofLp`. The primitive data are only `λ > 0` and `x`; the simplex projection set is
derived owner-level data and should not be repackaged. -/

-- Proof sketch: rewrite `coordinatewiseMax` as the support function of `stdSimplex ℝ (Fin n)`
-- using `coordinatewiseMax_eq_support_function_stdSimplex`, transport that support function along
-- `toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)`, and then specialize Theorem 6.46 to the
-- simplex image `toLp 2 '' stdSimplex ℝ (Fin n)`. Rewriting the resulting singleton formula
-- through the set-valued projection notation gives the displayed affine-image identity.
/-- Example 6.49: on the intrinsic Euclidean product `EuclideanSpace ℝ (Fin n)`, hence on
`ℝ^n`, the proximal mapping of `y ↦ λ max_i y_i` at `x` is the affine image of the projection
set onto the transported standard simplex `Δ = toLp 2 '' stdSimplex ℝ (Fin n)` under
`u ↦ x - λ • u`. This is the chapter's set-valued rendering of the textbook identity
`prox_{λ max(·)}(x) = x - λ P_{Δ_n}(x / λ)`. -/
theorem prox_coordinatewiseMax_eq_sub_smul_projection_mapping_stdSimplex
    (lam : ℝ) (hlam : 0 < lam) (x : E) :
    prox[fun y : E ↦ (lam : EReal) * (coordinatewiseMax y.ofLp : EReal)] x =
      Set.image (fun u : E ↦ x - lam • u) (P[Δ] (lam⁻¹ • x)) := by
  let lamPos : PosReal := ⟨lam, hlam⟩
  have hprox_support :
      prox[fun y : E ↦ (lam : EReal) * (coordinatewiseMax y.ofLp : EReal)] x =
        {x - lam •
          (metricProjectionOfComplete Δ transported_stdSimplex_nonempty
            isClosed_transported_stdSimplex.isComplete
            convex_transported_stdSimplex (lam⁻¹ • x) : E)} := by
    -- Rewrite the penalty as a scaled support function and invoke Theorem 6.46.
    rw [coordinatewiseMax_penalty_eq_smul_support_function_primal_transported_stdSimplex]
    simpa [lamPos] using
      prox_support_function_eq_singleton_sub_smul_metricProjection
        (C := Δ)
        (hC_nonempty := transported_stdSimplex_nonempty)
        (hC_complete := isClosed_transported_stdSimplex.isComplete)
        (hC_convex := convex_transported_stdSimplex)
        lamPos x
  have hproj :
      P[Δ] (lam⁻¹ • x) =
        {(metricProjectionOfComplete Δ transported_stdSimplex_nonempty
            isClosed_transported_stdSimplex.isComplete
            convex_transported_stdSimplex (lam⁻¹ • x) : E)} := by
    -- Rewrite the set-valued projection as the singleton of the metric projection.
    simpa [projectionPoint_eq_metricProjectionOfComplete
      (C := Δ)
      (hC_nonempty := transported_stdSimplex_nonempty)
      (hC_complete := isClosed_transported_stdSimplex.isComplete)
      (hC_convex := convex_transported_stdSimplex)
      (hC_closed := isClosed_transported_stdSimplex)
      (lam⁻¹ • x)] using
        projection_mapping_eq_singleton_of_nonempty_closed_convex
          (C := Δ)
          (hC_nonempty := transported_stdSimplex_nonempty)
          (hC_closed := isClosed_transported_stdSimplex)
          (hC_convex := convex_transported_stdSimplex)
          (lam⁻¹ • x)
  rw [hprox_support, hproj, Set.image_singleton]

end
