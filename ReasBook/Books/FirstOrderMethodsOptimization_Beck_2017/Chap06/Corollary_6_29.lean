/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_27
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_41

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open WithLp (ofLp toLp)
open scoped RealInnerProductSpace

section

variable {ι : Type*} [Fintype ι]

local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ ι : Set X) : Set E)
local notation "K" => (toLp 2 '' (Set.Ici (0 : X) : Set X) : Set E)
local notation "e" => (toLp 2 (1 : X) : E)

/- Corollary 6.29 is `source-facing`, but the owner abstraction for the projection statement is the
intrinsic Euclidean product `E = EuclideanSpace ℝ ι`, not the function-space norm on `ι → ℝ`.
Domain sampling for this file uses:
1. mathlib's `stdSimplex ℝ ι` as the canonical simplex owner on coordinates;
2. the intrinsic hyperplane owner `hyperplane` from Definition 1.10;
3. Theorem 6.27's owner-level hyperplane-shift identity
   `projection_mapping_hyperplane_inter_eq_shifted_projection_mapping`;
4. Theorem 6.41's variational characterization of Euclidean projection sets.

Primitive data:
- the Euclidean point `x : E`,
- the scalar shift `μ`,
- the simplex boundary condition on `((x.ofLp - μ • 1)⁺)`.

The coordinate simplex and nonnegative orthant therefore appear only as `bridge/view` data through
`toLp 2`, while the public corollary lives on the Euclidean owner `Δ = toLp 2 '' stdSimplex ℝ ι`.
-/

private lemma mem_hyperplane_ones_iff_sum_eq_one (x : X) :
    toLp 2 x ∈ (hyperplane e 1 : Set E) ↔ ∑ i, x i = 1 := by
  change toLp 2 x ∈ hyperplane (toLp 2 (1 : X)) 1 ↔ _
  rw [mem_hyperplane_iff]
  rw [show inner ℝ (toLp 2 (1 : X)) (toLp 2 x) = x ⬝ᵥ (1 : X) by
    simpa using (EuclideanSpace.inner_toLp_toLp (1 : X) x)]
  simp [dotProduct_one]

-- Proof sketch: the transported simplex is exactly the intersection of the Euclidean hyperplane
-- `⟪e, y⟫ = 1` with the transported nonnegative orthant `K`.
private lemma stdSimplex_image_eq_hyperplane_inter_nonnegativeOrthant :
    Δ = (hyperplane e 1 : Set E) ∩ K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [stdSimplex, Set.mem_setOf_eq] at hx
    exact ⟨(mem_hyperplane_ones_iff_sum_eq_one x).2 hx.2, ⟨x, hx.1, rfl⟩⟩
  · rintro ⟨hyH, hyK⟩
    rcases hyK with ⟨x, hx_nonneg, rfl⟩
    refine ⟨x, ?_, rfl⟩
    rw [stdSimplex, Set.mem_setOf_eq]
    exact ⟨hx_nonneg, (mem_hyperplane_ones_iff_sum_eq_one x).1 hyH⟩

private lemma convex_nonnegativeOrthantImage : Convex ℝ K :=
  (convex_Ici (0 : X)).linear_image ((WithLp.linearEquiv 2 ℝ X).symm.toLinearMap)

private lemma inner_le_zero_of_mem_nonnegativeOrthant
    (z v : X) (hv : v ∈ Set.Ici (0 : X)) :
    inner ℝ (toLp 2 (z - z⁺)) (toLp 2 (v - z⁺)) ≤ 0 := by
  rw [show inner ℝ (toLp 2 (z - z⁺)) (toLp 2 (v - z⁺)) = (v - z⁺) ⬝ᵥ (z - z⁺) by
    simpa using (EuclideanSpace.inner_toLp_toLp (z - z⁺) (v - z⁺))]
  rw [dotProduct]
  exact Finset.sum_nonpos fun i _ ↦ by
    by_cases hzi : 0 ≤ z i
    · have hzpos : z⁺ i = z i := posPart_eq_self.2 hzi
      simp [hzpos]
    · have hznonpos : z i ≤ 0 := le_of_not_ge hzi
      have hzpos : z⁺ i = 0 := posPart_eq_zero.2 hznonpos
      have hvi : 0 ≤ v i := hv i
      have hmul : v i * z i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hvi hznonpos
      simpa [hzpos, mul_comm] using hmul

-- Proof sketch: apply the Euclidean variational criterion from Theorem 6.41 to the transported
-- orthant `K`, using the coordinatewise positive part as the candidate projection point.
private theorem projection_mapping_nonnegativeOrthantImage_eq_singleton_posPart (z : E) :
    P[K] z = {toLp 2 z.ofLp⁺} := by
  -- The positive part lies in the transported orthant, so it is a valid candidate projector.
  have hz : toLp 2 z.ofLp⁺ ∈ K := by
    refine ⟨z.ofLp⁺, ?_, rfl⟩
    simpa using (posPart_nonneg z.ofLp)
  -- Supply the candidate point as the implicit `u` parameter before using Theorem 6.41.
  refine
    (projection_mapping_eq_singleton_iff_inner_le_zero K convex_nonnegativeOrthantImage z
      (u := toLp 2 z.ofLp⁺) hz).2 ?_
  -- Rewrite an arbitrary point of `K` back to coordinates and use the coordinatewise inequality.
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  simpa using inner_le_zero_of_mem_nonnegativeOrthant z.ofLp v hv

-- Proof sketch: rewrite the simplex image `Δ` as the Euclidean hyperplane/orthant intersection,
-- apply Theorem 6.27 to shift the projection problem onto the orthant `K`, and then use the
-- positive-part singleton formula above.
/-- Corollary 6.29: on the intrinsic Euclidean product `E = EuclideanSpace ℝ ι`, the projection
onto the transported standard simplex `Δ = toLp 2 '' stdSimplex ℝ ι` is the singleton
`{toLp 2 ((x.ofLp - μ • 1)⁺)}` whenever the shifted positive-part point has coordinate sum `1`.
For `ι = Fin n`, this is the textbook Euclidean simplex projection formula on `ℝ^n`. -/
theorem projection_mapping_stdSimplex_eq_singleton_posPart_sub_smul_one
    (x : E) (μ : ℝ) (hμ : ∑ i, ((x.ofLp - μ • (1 : X))⁺) i = 1) :
    P[Δ] x = {toLp 2 ((x.ofLp - μ • (1 : X))⁺)} := by
  have horthant :
      P[K] (x - μ • e) = {toLp 2 ((x.ofLp - μ • (1 : X))⁺)} := by
    simpa using projection_mapping_nonnegativeOrthantImage_eq_singleton_posPart (x - μ • e)
  have hsubset : P[K] (x - μ • e) ⊆ (hyperplane e 1 : Set E) := by
    intro y hy
    rw [horthant] at hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact (mem_hyperplane_ones_iff_sum_eq_one _).2 hμ
  calc
    P[Δ] x = P[((hyperplane e 1 : Set E) ∩ K)] x := by
      rw [stdSimplex_image_eq_hyperplane_inter_nonnegativeOrthant]
    _ = P[K] (x - μ • e) := by
      refine projection_mapping_hyperplane_inter_eq_shifted_projection_mapping e 1 K x μ ?_ hsubset
      rw [horthant]
      exact Set.singleton_nonempty _
    _ = {toLp 2 ((x.ofLp - μ • (1 : X))⁺)} := horthant

end
