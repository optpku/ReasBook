/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Lemma 5.4.5.1 lies in the chapter's Euclidean ellipsoid / affine-support domain.

Sampled owner-style declarations:
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the chapter owner and
  companion view for the textbook ellipsoid `E(H, v)`;
- `center_mem_affineEllipsoid` in the same file, showing that center-membership is derived from
  that owner rather than stored as separate data;
- `isGreatest_inner_image_spdEllipsoid` in `Chap03/Lemma_3_20`, the canonical centered-ellipsoid
  support-value theorem already stated on the same owner surface.

Best owner abstraction:
- source-facing: the affine half-space inequality on the chapter ellipsoid `E(H, v)`;
- core/canonical: `affineEllipsoid` together with the centered support maximum theorem
  `isGreatest_inner_image_spdEllipsoid`;
- bridge/view: translating `E(H, v)` to `E(H, 0)` and rewriting the affine inequality in terms of
  the support value.

Primitive data:
- the linear functional vector `a`;
- the center `v`;
- the affine bound `b`;
- the positive-definite shape matrix `H`.

Derived API:
- ellipsoid membership via `x ∈ E(H, v)`;
- the centered support bound over `E(H, 0)`;
- the quadratic inequality obtained by squaring that support bound under the nonnegative
  center-slack hypothesis `0 ≤ b - ⟪a, v⟫`.

The previous statement duplicated the owner ellipsoid through its raw quadratic predicate. This
refinement keeps the source-facing inequality theorem, but moves its public surface onto the
existing chapter owner and reuses the centered support theorem upstream instead of reproving the
same geometry locally.
-/

-- Proof sketch: for the forward implication, evaluate the affine form at the boundary point
-- `v + (H *ᵥ a) / √⟪H a, a⟫`, which satisfies the boundary equation
-- `⟪H⁻¹ (x - v), x - v⟫ = 1`; for the reverse
-- implication, write `x = v + y` and apply Cauchy-Schwarz for the inner product induced by
-- `H⁻¹` to bound `⟪a, y⟫` by `√⟪H a, a⟫`.
/-- Lemma 5.4.5.1: for the ellipsoid
`W = {x | ⟪H⁻¹ (x - v), x - v⟫ ≤ 1}` cut out by a positive-definite matrix `H`, the affine
inequality `⟪a, x⟫ ≤ b` holds on all of `W` exactly when the quadratic bound
`⟪a, H a⟫ ≤ (b - ⟪a, v⟫)^2` holds. On the public surface, `W` is the chapter ellipsoid
owner `E(H, v)`. -/
theorem affine_le_on_affineEllipsoid_iff
    (a v : E) (b : ℝ) (H : Mat)
    (hβ : 0 ≤ b - ⟪a, v⟫) (hH : H.PosDef) :
    (∀ x ∈ E(H, v), ⟪a, x⟫ ≤ b) ↔
      ⟪a, H.toEuclideanLin a⟫ ≤ (b - ⟪a, v⟫) ^ (2 : ℕ) := by
  let β := b - ⟪a, v⟫
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using hβ
  have htranslate :
      (∀ x ∈ E(H, v), ⟪a, x⟫ ≤ b) ↔
        ∀ y ∈ E(H, (0 : E)), ⟪a, y⟫ ≤ β := by
    constructor
    · intro hx y hy
      have hmem : v + y ∈ E(H, v) := by
        rw [mem_affineEllipsoid_iff] at hy ⊢
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
      have hxy : ⟪a, v⟫ + ⟪a, y⟫ ≤ b := by
        simpa [inner_add_right] using hx (v + y) hmem
      linarith
    · intro hy x hx
      have hmem : x - v ∈ E(H, (0 : E)) := by
        rw [mem_affineEllipsoid_iff] at hx ⊢
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
      have hxy : ⟪a, x - v⟫ ≤ β := hy (x - v) hmem
      have hxsplit : ⟪a, x⟫ = ⟪a, v⟫ + ⟪a, x - v⟫ := by
        calc
          ⟪a, x⟫ = ⟪a, v + (x - v)⟫ := by simp
          _ = ⟪a, v⟫ + ⟪a, x - v⟫ := by rw [inner_add_right]
      linarith
  have hcentered :
      (∀ y ∈ E(H, (0 : E)), ⟪a, y⟫ ≤ β) ↔
        Real.sqrt ⟪a, H.toEuclideanLin a⟫ ≤ β := by
    have hmax :
        IsGreatest ((fun y : E ↦ ⟪a, y⟫) '' E(H, (0 : E)))
          (Real.sqrt ⟪a, H.toEuclideanLin a⟫) := by
      let _ : Invertible H := hH.isUnit.invertible
      simpa only [Matrix.inv_inv_of_invertible] using
        isGreatest_inner_image_spdEllipsoid H⁻¹ hH.inv a
    constructor
    · intro hy
      rcases hmax.1 with ⟨y, hy_mem, hy_eq⟩
      rw [← hy_eq]
      exact hy y hy_mem
    · intro hmax_le y hy
      exact le_trans (hmax.2 ⟨y, hy, rfl⟩) hmax_le
  have hsqrt :
      Real.sqrt ⟪a, H.toEuclideanLin a⟫ ≤ β ↔
        ⟪a, H.toEuclideanLin a⟫ ≤ β ^ (2 : ℕ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hβ_nonneg, h⟩
  rw [htranslate, hcentered]
  simpa [β] using hsqrt

end
