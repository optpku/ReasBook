/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_31
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_34

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)

/- Corollary 3.33 is a `source-facing` simplex specialization of the owner constrained-optimality
criterion `isMinOn_iff_exists_subgradient_neg_mem_normal_cone` from Theorem 3.31, together with
the simplex normal-cone bridge
`neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier` from Proposition 3.34.
This file therefore keeps only the simplex-specific statement and reuses the upstream
convex-analysis API directly. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone
recall isMinOn_iff_exists_subgradient_neg_mem_normal_cone_of_proper
recall neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier

-- Proof sketch: apply the constrained convex optimality criterion under the qualification
-- `ri(Δ_n) ∩ ri(dom f) ≠ ∅` to obtain a subgradient whose negation lies in the owner normal cone
-- of the simplex at `xStar`. Transport that dual vector to coordinates by `dotProductEquiv`, and
-- then use Proposition 3.34 to identify the resulting normal-cone condition with the existence of
-- a scalar multiplier that is constant on the positive support of `xStar` and bounded above by the
-- remaining coordinates.
/-- Corollary 3.33: under the relative-interior qualification
`ri(Δ_n) ∩ ri(dom f) ≠ ∅`, a point `xStar ∈ Δ_n = stdSimplex ℝ (Fin n)` minimizes `f` on the unit
simplex if and only if there exist a subgradient vector `g` at `xStar`, identified with the dual
space by `dotProductEquiv`, and a scalar `μ` such that `g i = μ` whenever `xStar i > 0` and
`μ ≤ g i` whenever `xStar i = 0`. -/
theorem isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier
    {f : (Fin n → ℝ) → EReal} (hf : IsProperExtendedRealFunction f)
    (hconv : is_convex_function f)
    (hri : (intrinsicInterior ℝ Δ ∩ intrinsicInterior ℝ (effective_domain f)).Nonempty)
    {xStar : Fin n → ℝ} (hxStar : xStar ∈ Δ) :
    IsMinOn f Δ xStar ↔
      ∃ g : Fin n → ℝ,
        dotProductEquiv ℝ (Fin n) g ∈ subdifferential f xStar ∧
          ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ := by
  have hΔ : Convex ℝ Δ := convex_stdSimplex ℝ (Fin n)
  have howner :
      IsMinOn f Δ xStar ↔
        ∃ g' : Module.Dual ℝ (Fin n → ℝ),
          g' ∈ ∂ f(xStar) ∧ -g' ∈ normal_cone Δ xStar :=
    isMinOn_iff_exists_subgradient_neg_mem_normal_cone_of_proper (f := f) hf hconv hΔ
      (by simpa [Set.inter_comm] using hri) hxStar
  constructor
  · intro hxmin
    rcases howner.mp hxmin with ⟨g', hg', hg'normal⟩
    let g : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g'
    refine ⟨g, ?_, ?_⟩
    · simpa [g] using hg'
    · have hg'normal' :
          -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar := by
        simpa [g] using hg'normal
      have hmult :
          -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar ↔
            ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ :=
        neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier hxStar
      exact hmult.mp hg'normal'
  · rintro ⟨g, hg, μ, hμ⟩
    have hmult :
        -dotProductEquiv ℝ (Fin n) g ∈ normal_cone Δ xStar ↔
          ∃ μ : ℝ, IsStdSimplexMultiplier xStar g μ :=
      neg_dotProductEquiv_mem_normal_cone_stdSimplex_iff_exists_multiplier hxStar
    exact howner.mpr ⟨dotProductEquiv ℝ (Fin n) g, hg, by
      exact hmult.mpr ⟨μ, hμ⟩⟩

end
