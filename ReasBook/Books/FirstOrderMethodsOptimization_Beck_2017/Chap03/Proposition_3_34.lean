/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic.Recall
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}
variable {xStar g : Fin n → ℝ}

local notation "Δ" => stdSimplex ℝ (Fin n)

/- Proposition 3.34 is a `bridge/view` item in the simplex-constrained optimality API. The
chapter owner abstraction for feasible-displacement inequalities is the normal cone
`N[Δ](xStar)`; at a feasible point this is Definition 3.3's source-facing cone, built from the
translated-set polar cone `polar_cone (Δ -ᵥ {xStar})`. The primitive data are only the simplex
point `xStar`, the coordinate vector `g`, and the scalar `μ`; the raw inequality
`∀ x ∈ Δ_n, 0 ≤ gᵀ (x - xStar)` is derived from this owner cone-membership condition rather than
treated as a second root notion. -/
-- Semantic recall note: `lean_leansearch` returned only generic convex-analysis hits, so this
-- simplex multiplier criterion remains a chapter-local normal-cone bridge.

recall normal_cone

/-- The simplex multiplier condition says that a coordinate vector `g` is constant on the positive
support of `xStar` with common value `μ`, and that the remaining coordinates are bounded below by
`μ`. -/
def IsStdSimplexMultiplier
    (xStar g : Fin n → ℝ) (μ : ℝ) : Prop :=
  (∀ i : Fin n, 0 < xStar i → g i = μ) ∧
    ∀ i : Fin n, xStar i = 0 → μ ≤ g i

namespace IsStdSimplexMultiplier

lemma eq_of_pos {μ : ℝ} (h : IsStdSimplexMultiplier xStar g μ) (i : Fin n)
    (hi : 0 < xStar i) :
    g i = μ :=
  h.1 i hi

lemma le_of_eq_zero {μ : ℝ} (h : IsStdSimplexMultiplier xStar g μ) (i : Fin n)
    (hi : xStar i = 0) :
    μ ≤ g i :=
  h.2 i hi

end IsStdSimplexMultiplier

/-- Helper for Proposition 3.34: normal-cone membership for `-dotProductEquiv ℝ (Fin n) g` is the
same as the source variational inequality on the simplex. -/
private lemma neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_forall_dotProduct_sub_nonneg
    (hxStar : xStar ∈ Δ) :
    -dotProductEquiv ℝ (Fin n) g ∈ N[Δ](xStar) ↔
      ∀ x ∈ Δ, 0 ≤ dotProduct g (x - xStar) := by
  -- Rewrite normal-cone membership into the displacement inequality from Definition 3.3.
  rw [mem_normal_cone Δ hxStar (-dotProductEquiv ℝ (Fin n) g)]
  constructor
  · intro h x hx
    -- `dotProductEquiv` evaluates as the dot product, so the sign flip becomes `0 ≤ ...`.
    simpa using h x hx
  · intro h x hx
    -- The converse is the same scalar inequality viewed in the owner theorem's sign convention.
    simpa using h x hx

/-- Helper for Proposition 3.34: a point of the simplex has at least one positive coordinate. -/
lemma exists_pos_of_mem_stdSimplex (hxStar : xStar ∈ Δ) :
    ∃ i : Fin n, 0 < xStar i := by
  by_contra hpos
  have hxZero : xStar = 0 := by
    funext i
    exact le_antisymm (le_of_not_gt fun hi ↦ hpos ⟨i, hi⟩) (hxStar.1 i)
  -- If every coordinate vanished, the simplex sum constraint would read `0 = 1`.
  simp [stdSimplex, hxZero] at hxStar

/-- Helper for Proposition 3.34: moving mass from coordinate `i` to coordinate `j` by an amount
`ε` bounded by `xStar i` keeps the point inside the simplex. -/
lemma shiftMass_mem_stdSimplex (hxStar : xStar ∈ Δ) (i j : Fin n) {ε : ℝ}
    (hε_nonneg : 0 ≤ ε) (hε_le : ε ≤ xStar i) :
    xStar + ε • (Pi.single j 1 - Pi.single i 1) ∈ Δ := by
  constructor
  · intro k
    by_cases hk : k = i
    · rw [hk]
      by_cases hij : j = i
      · rw [hij]
        simpa [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply]
          using hxStar.1 i
      · have hnonneg : 0 ≤ xStar i - ε := sub_nonneg.mpr hε_le
        simpa [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, hk, hij]
          using hnonneg
    · by_cases hk' : k = j
      · rw [hk'] at hk
        have hnonneg : 0 ≤ xStar j + ε := add_nonneg (hxStar.1 j) hε_nonneg
        simpa [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, hk, hk']
          using hnonneg
      · simpa [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, hk, hk']
          using hxStar.1 k
  · -- The perturbation preserves the total coordinate sum because it adds one unit and removes one.
    simp_rw [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, hxStar.2, ← Finset.mul_sum]
    simp [Finset.sum_sub_distrib]

/-- Helper for Proposition 3.34: the mass-transfer perturbation turns the variational inequality
into the scalar comparison `ε * (g j - g i)`. -/
lemma dotProduct_shiftMass_sub (i j : Fin n) (ε : ℝ) :
    dotProduct g ((xStar + ε • (Pi.single j 1 - Pi.single i 1)) - xStar) =
      ε * (g j - g i) := by
  -- First cancel the base point, then evaluate the dot product on the two simplex vertices.
  calc
    dotProduct g ((xStar + ε • (Pi.single j 1 - Pi.single i 1)) - xStar)
        = dotProduct g (ε • (Pi.single j 1 - Pi.single i 1)) := by
            simp
    _ = ε * dotProduct g (Pi.single j 1 - Pi.single i 1) := by
          simp [smul_eq_mul]
    _ = ε * (g j - g i) := by
          simp [dotProduct_sub]

-- Proof sketch: for the forward implication, test the variational inequality on simplex points
-- obtained by moving a small amount of mass from one positive coordinate of `xStar` to another
-- coordinate. This shows that all coordinates of `g` on the positive support of `xStar` are equal,
-- while every coordinate of `g` on the zero support is at least that common value. For the reverse
-- implication, expand `dotProduct g (x - xStar)` and use that both `x` and `xStar` have coordinate
-- sum `1`. This is exactly the coordinate form of
-- `-dotProductEquiv ℝ (Fin n) g ∈ N[stdSimplex ℝ (Fin n)](xStar)`, which at a feasible
-- point is the translated-set polar-cone condition from Definition 3.3.
/-- Normal-cone form of the simplex multiplier criterion: for a feasible point
`xStar ∈ stdSimplex ℝ (Fin n)`, the negative Euclidean-dual vector corresponding to `g` lies in the
normal cone of the simplex at `xStar` if and only if `g` satisfies the scalar simplex multiplier
condition. -/
theorem neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier
    (hxStar : xStar ∈ Δ) :
    -dotProductEquiv ℝ (Fin n) g ∈ N[Δ](xStar) ↔
      ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := by
  -- Rewrite once to the source-facing variational inequality and prove the coordinate criterion.
  rw [neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_forall_dotProduct_sub_nonneg
    hxStar]
  constructor
  · intro h
    obtain ⟨i0, hi0⟩ := exists_pos_of_mem_stdSimplex hxStar
    have hcompare : ∀ {i j : Fin n}, 0 < xStar i → g i ≤ g j := by
      intro i j hi
      -- Move all mass available at `i` to `j` to turn the variational inequality into a scalar one.
      have hshift :
          0 ≤ dotProduct g ((xStar + xStar i • (Pi.single j 1 - Pi.single i 1)) - xStar) := by
        exact h _ (shiftMass_mem_stdSimplex hxStar i j (hxStar.1 i) le_rfl)
      have hscalar : 0 ≤ xStar i * (g j - g i) := by
        simpa [dotProduct_shiftMass_sub i j (xStar i)] using hshift
      nlinarith
    refine ⟨g i0, ?_⟩
    constructor
    · intro i hi
      -- Positive-support coordinates compare both ways, so they all equal the common value `g i0`.
      have hleft : g i0 ≤ g i := hcompare hi0
      have hright : g i ≤ g i0 := hcompare hi
      linarith
    · intro i hi
      -- Coordinates on the zero support are bounded below by the positive-support common value.
      exact hcompare hi0
  · rintro ⟨μ, hμ⟩ x hx
    have hcoordLower : ∀ i : Fin n, μ ≤ g i := by
      intro i
      by_cases hi : xStar i = 0
      · exact hμ.le_of_eq_zero i hi
      · have hpos : 0 < xStar i := lt_of_le_of_ne (hxStar.1 i) (Ne.symm hi)
        simp [hμ.eq_of_pos i hpos]
    have hdotLower : μ ≤ dotProduct g x := by
      -- Coordinatewise lower bounds propagate to the dot product because simplex coordinates
      -- are nonnegative.
      have hsum : μ * ∑ i, x i ≤ dotProduct g x := by
        calc
          μ * ∑ i, x i = ∑ i, μ * x i := by
            rw [Finset.mul_sum]
          _ ≤ ∑ i, g i * x i := by
            exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hcoordLower i) (hx.1 i)
          _ = dotProduct g x := by
            simp [dotProduct]
      simpa [hx.2] using hsum
    have hdotStar : dotProduct g xStar = μ := by
      have hcoord : ∀ i : Fin n, g i * xStar i = μ * xStar i := by
        intro i
        by_cases hi : xStar i = 0
        · simp [hi]
        · have hpos : 0 < xStar i := lt_of_le_of_ne (hxStar.1 i) (Ne.symm hi)
          rw [hμ.eq_of_pos i hpos]
      -- On the positive support, `g` equals `μ`; on the zero support, both products vanish.
      calc
        dotProduct g xStar = ∑ i, μ * xStar i := by
          simp [dotProduct, hcoord]
        _ = μ * ∑ i, xStar i := by
          rw [Finset.mul_sum]
        _ = μ := by
          simp [hxStar.2]
    -- Subtract the equality at `xStar` from the lower bound at `x`.
    have hle : dotProduct g xStar ≤ dotProduct g x := by
      calc
        dotProduct g xStar = μ := hdotStar
        _ ≤ dotProduct g x := hdotLower
    simpa [dotProduct_sub] using sub_nonneg.mpr hle

/-- Proposition 3.34: for a point `xStar` of the unit simplex `Δ_n`, the condition
`gᵀ (x - xStar) ≥ 0` for every `x ∈ Δ_n` is equivalent to the existence of a scalar `μ` such that
`g i = μ` whenever `xStar i > 0` and `μ ≤ g i` whenever `xStar i = 0`. This is the source-facing
variational-inequality view of the normal-cone statement
`neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier`. -/
theorem dotProduct_sub_nonneg_on_stdSimplex_iff_exists_multiplier
    (hxStar : xStar ∈ Δ) :
    (∀ x ∈ Δ, 0 ≤ dotProduct g (x - xStar)) ↔
      ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := by
  -- Rewrite the owner theorem back into the source-facing variational inequality.
  rw [← neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_forall_dotProduct_sub_nonneg
    hxStar]
  exact neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier hxStar

end
