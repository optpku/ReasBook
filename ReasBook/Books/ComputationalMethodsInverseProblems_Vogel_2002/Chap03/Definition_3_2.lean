/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Prop_2_34
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.ExactStep
public import Mathlib.Analysis.Calculus.DerivativeTest

public section

noncomputable section

open scoped Topology
open Filter SignType

namespace LineSearch

universe u

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-- Helper for Definition 3.2: a search direction `p_v` is a descent direction
for `J` at `f_v` when the line-search profile strictly decreases for all
sufficiently small positive steps. -/
def IsDescentDirection (J : X → ℝ) (f_v p_v : X) : Prop :=
  ∃ δ > 0, ∀ ⦃τ : ℝ⦄, 0 < τ → τ < δ → profile J f_v p_v τ < profile J f_v p_v 0

/-- Helper for Definition 3.2: the descent-direction predicate is equivalent to
the textbook inequality `J (f_v + τ • p_v) < J f_v` for all sufficiently small
positive `τ`. -/
theorem isDescentDirection_iff {J : X → ℝ} {f_v p_v : X} :
    IsDescentDirection J f_v p_v ↔
      ∃ δ > 0, ∀ ⦃τ : ℝ⦄, 0 < τ → τ < δ → J (f_v + τ • p_v) < J f_v := by
  -- Unfold the profile only at the source-facing inequality surface.
  constructor
  · rintro ⟨δ, hδ, hdesc⟩
    refine ⟨δ, hδ, ?_⟩
    intro τ hτ hτδ
    simpa [profile_apply] using hdesc hτ hτδ
  · rintro ⟨δ, hδ, hdesc⟩
    refine ⟨δ, hδ, ?_⟩
    intro τ hτ hτδ
    simpa [profile_apply] using hdesc hτ hτδ

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Definition 3.2: a negative scalar derivative at `0` forces
strict decrease on a sufficiently small right neighborhood of `0`. -/
lemma strictDecreaseNearZero_of_hasDerivAt_neg {φ : ℝ → ℝ} {φ' : ℝ}
    (hφ : HasDerivAt φ φ' 0) (hneg : φ' < 0) :
    ∃ δ > 0, ∀ ⦃τ : ℝ⦄, 0 < τ → τ < δ → φ τ < φ 0 := by
  -- Normalize to a function vanishing at `0`, so the sign theorem applies directly.
  let ψ : ℝ → ℝ := fun τ ↦ φ τ - φ 0
  have hψ : HasDerivAt ψ φ' 0 := by
    simpa [ψ] using hφ.sub_const (φ 0)
  have hsign : ∀ᶠ x in 𝓝 0, sign (ψ x) = sign (0 - x) := by
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (by simpa [hψ.deriv] using hneg) (by simp [ψ])
  -- Extract an explicit interval around `0` from the neighborhood statement.
  rcases mem_nhds_iff_exists_Ioo_subset.mp hsign with ⟨l, u, hzero, hIoo⟩
  let δ : ℝ := min (-l) u
  have hδ : 0 < δ := by
    refine lt_min ?_ hzero.2
    linarith [hzero.1]
  refine ⟨δ, hδ, ?_⟩
  intro τ hτ hτδ
  have hmem : τ ∈ Set.Ioo l u := by
    refine ⟨lt_trans hzero.1 hτ, lt_of_lt_of_le hτδ (min_le_right _ _)⟩
  have hsignτ : sign (ψ τ) = sign (0 - τ) := hIoo hmem
  have hψneg : ψ τ < 0 := by
    apply (sign_eq_neg_one_iff).mp
    rw [hsignτ]
    exact sign_neg (by linarith)
  have hsub : φ τ - φ 0 < 0 := by
    simpa [ψ] using hψneg
  linarith

/-- Helper for Definition 3.2: a gradient witness differentiates the line-search
profile at `0` with derivative `inner ℝ g p_v`. -/
lemma hasDerivAt_profile_zero_of_hasGradientAt {J : H → ℝ} {f_v g p_v : H}
    (hJ : HasGradientAt J g f_v) :
    HasDerivAt (profile J f_v p_v) (inner ℝ g p_v) 0 := by
  -- Repackage the Chapter 2 line-derivative statement as the scalar profile derivative.
  have hprofile : profile J f_v p_v = fun τ : ℝ ↦ J (f_v + τ • p_v) := by
    funext τ
    exact profile_apply J f_v p_v τ
  rw [hprofile]
  exact hJ.hasLineDerivAt p_v

/-- Definition 3.2. If `J` has gradient `g` at `f_v` and
`inner ℝ g p_v < 0`, then `p_v` is a descent direction for `J` at `f_v`. -/
theorem isDescentDirection_of_hasGradientAt_neg {J : H → ℝ} {f_v g p_v : H}
    (hJ : HasGradientAt J g f_v) (hneg : inner ℝ g p_v < 0) :
    IsDescentDirection J f_v p_v := by
  -- Reduce the source descent condition to strict decrease of the scalar profile.
  obtain ⟨δ, hδ, hdesc⟩ :=
    strictDecreaseNearZero_of_hasDerivAt_neg
      (hφ := hasDerivAt_profile_zero_of_hasGradientAt (p_v := p_v) hJ) hneg
  exact ⟨δ, hδ, fun _ hτ hτδ ↦ hdesc hτ hτδ⟩

/-- Helper for Definition 3.2: if `J` is differentiable at `f_v` and
`inner ℝ (gradient J f_v) p_v < 0`, then `p_v` is a descent direction for `J`
at `f_v`. -/
theorem isDescentDirection_of_inner_gradient_neg {J : H → ℝ} {f_v p_v : H}
    (hJ : DifferentiableAt ℝ J f_v) (hneg : inner ℝ (gradient J f_v) p_v < 0) :
    IsDescentDirection J f_v p_v := by
  -- Specialize the explicit-gradient theorem to the canonical gradient.
  exact isDescentDirection_of_hasGradientAt_neg hJ.hasGradientAt hneg

/-- Helper for Definition 3.2: the steepest-descent direction `-gradient J f_v`
is a descent direction whenever `gradient J f_v ≠ 0`. -/
theorem negGradient_isDescentDirection {J : H → ℝ} {f_v : H}
    (hJ : DifferentiableAt ℝ J f_v) (hgrad : gradient J f_v ≠ 0) :
    IsDescentDirection J f_v (-gradient J f_v) := by
  -- Compute the directional derivative sign of the negative-gradient direction.
  have hself : 0 < inner ℝ (gradient J f_v) (gradient J f_v) := real_inner_self_pos.2 hgrad
  have hneg : inner ℝ (gradient J f_v) (-gradient J f_v) < 0 := by
    simpa [inner_neg_right] using neg_lt_zero.mpr hself
  exact isDescentDirection_of_inner_gradient_neg hJ hneg

end LineSearch

section

universe u

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (J : X → ℝ) (f_v p_v : X) (τ : ℝ)

/- Definition 3.2. The source line-search problem
`min_{τ > 0} J (f_v + τ • p_v)` is the source-facing predicate
`LineSearch.IsExactStep J f_v p_v τ`. Its canonical minimizer component is
`IsMinOn (LineSearch.profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ`, and the
companion source predicate "descent direction" is
`LineSearch.IsDescentDirection`. -/
#check LineSearch.IsExactStep J f_v p_v τ

/- The line-search problem is evaluated through the scalar profile
`LineSearch.profile J f_v p_v`, whose canonical minimizer surface is
`IsMinOn (LineSearch.profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ`. The companion
source-facing owner for the setup is the descent-direction predicate
`LineSearch.IsDescentDirection`. -/
#check LineSearch.profile
#check IsMinOn (LineSearch.profile J f_v p_v) (Set.Ioi (0 : ℝ)) τ
#check LineSearch.IsDescentDirection J f_v p_v

end
