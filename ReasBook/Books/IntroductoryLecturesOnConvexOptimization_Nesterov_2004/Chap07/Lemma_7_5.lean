/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_31
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm OneSidedHullNotation SupportFunction

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.5 lies in Chapter 7's one-sided rounding / scalar interval-maximizer domain.

Sampled owner-style declarations:
- `IsMaxOn`, the canonical mathlib owner for interval maximizers;
- `centralSymmetryRoundingAlphaStar_mem_Ico` and
  `centralSymmetryRoundingObjective_isMaxOn_iff` in `Proposition_7_8`, the nearby chapter scalar
  maximizer pattern with the same interval-feasibility issue;
- `oneSidedRoundingUpdatedMatrix` in `Definition_7_31`, the source-facing matrix-path owner whose
  determinant ratio is encoded by the scalar potential below;
- `convexHullOfWeightedUnitBallAndPoint` and its support-function theorem in `Definition_7_30`,
  the source-facing geometric owner for the one-sided containment statement.

Best owner abstraction:
- source-facing: the one-sided scalar potential `V`, its parameter `σ`, and the critical point
  `α*`;
- core/canonical: `IsMaxOn` on `Set.Ico (0 : ℝ) 1`;
- bridge/view: the ellipsoid-containment and determinant-ratio theorems connecting the scalar owner
  to the matrix-level source objects; the shifted ellipsoid clause is the source-facing theorem,
  and the centered zero-radius specialization is kept as a boundary companion.

Primitive data:
- a positive-definite matrix owner `G`;
- a vector `g`;
- a scalar parameter `α`.

Derived API:
- the auxiliary scalar `σ = (r - n) / (n + 1)`;
- the explicit candidate maximizer `α*`;
- theorem-level interval feasibility, maximizer, value, and lower-bound consequences.
- theorem-level shifted-ellipsoid containment with a zero-radius boundary companion.

The dimension lower bound belongs to the theorem layer rather than the data layer: it is needed for
the interval-maximizer clause, but it is not part of the owner definitions themselves. -/

/-- The logarithmic determinant potential
`V(α) = log (det G(α) / det G(0)) = 2 log (1 + α (r - 1) / 2) + (n - 1) log (1 - α)`
written with the canonical dual radius `r = ‖g‖*_G`. -/
def oneSidedRoundingPotential
    (G : {A : Mat // A.PosDef}) (g : E) (α : ℝ) : ℝ :=
  2 * Real.log (1 + α * ((‖g‖[G,*] - 1) / 2)) +
    ((n : ℝ) - 1) * Real.log (1 - α)

-- Proof sketch: unfold `oneSidedRoundingPotential`.
/-- Expanding `oneSidedRoundingPotential G g α` gives the explicit scalar formula for `V(α)`. -/
theorem oneSidedRoundingPotential_def
    (G : {A : Mat // A.PosDef}) (g : E) (α : ℝ) :
    oneSidedRoundingPotential G g α =
      2 * Real.log (1 + α * ((‖g‖[G,*] - 1) / 2)) +
        ((n : ℝ) - 1) * Real.log (1 - α) :=
  rfl

/-- The canonical quantity `σ = (r - n) / (n + 1)` attached to the dual radius
`r = ‖g‖*_G`. -/
def oneSidedRoundingSigma
    (G : {A : Mat // A.PosDef}) (g : E) : ℝ :=
  (‖g‖[G,*] - (n : ℝ)) / ((n : ℝ) + 1)

-- Proof sketch: unfold `oneSidedRoundingSigma`.
/-- Expanding `oneSidedRoundingSigma G g` recovers `(r - n) / (n + 1)` with `r = ‖g‖*_G`. -/
theorem oneSidedRoundingSigma_def
    (G : {A : Mat // A.PosDef}) (g : E) :
    oneSidedRoundingSigma G g =
      (‖g‖[G,*] - (n : ℝ)) / ((n : ℝ) + 1) :=
  rfl

/-- The candidate maximizer
`α* = (2 / (n + 1)) ((r - n) / (r - 1))`
for the one-sided rounding potential, with `r = ‖g‖*_G`. -/
def oneSidedRoundingAlphaStar
    (G : {A : Mat // A.PosDef}) (g : E) : ℝ :=
  ((2 : ℝ) / ((n : ℝ) + 1)) *
    ((‖g‖[G,*] - (n : ℝ)) / (‖g‖[G,*] - 1))

/-- Helper for Lemma 7.5: on `[0, 1)`, the two logarithmic arguments in
`oneSidedRoundingPotential G g` are strictly positive. -/
lemma oneSidedRoundingPotential_logArgumentsPos
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    0 < 1 - α ∧ 0 < 1 + α * ((‖g‖[G,*] - 1) / 2) := by
  rcases hα with ⟨hα0, hα1⟩
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hr2 : (2 : ℝ) ≤ ‖g‖[G,*] := le_trans hn' hr
  have hcoeff_nonneg : 0 ≤ (‖g‖[G,*] - 1) / 2 := by
    nlinarith
  constructor
  · -- The interval assumption directly yields positivity of the second logarithmic argument.
    linarith
  · -- The coefficient is nonnegative because `‖g‖[G,*] ≥ n ≥ 2`.
    have hterm_nonneg : 0 ≤ α * ((‖g‖[G,*] - 1) / 2) :=
      mul_nonneg hα0 hcoeff_nonneg
    linarith

/-- Helper for Lemma 7.5: the one-sided potential has the expected derivative at every
`α ∈ [0, 1)` where the logarithmic domain is valid. -/
lemma oneSidedRoundingPotential_hasDerivAt
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hlog : 0 < 1 + α * ((‖g‖[G,*] - 1) / 2)) :
    HasDerivAt (oneSidedRoundingPotential G g)
      (((‖g‖[G,*] - 1) / (1 + α * ((‖g‖[G,*] - 1) / 2))) -
        (((n : ℝ) - 1) / (1 - α))) α := by
  let c : ℝ := (‖g‖[G,*] - 1) / 2
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hlog₁ : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x * c)) (c / (1 + α * c)) α := by
    have hinner : HasDerivAt (fun x : ℝ ↦ 1 + x * c) c α := by
      simpa [c, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id α).mul_const c).const_add 1
    exact hinner.log hlog.ne'
  have hscaled₁ :
      HasDerivAt (fun x : ℝ ↦ 2 * Real.log (1 + x * c))
        (2 * (c / (1 + α * c))) α := by
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hlog₁.const_mul (2 : ℝ)
  have hlog₂ : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) ((-1) / (1 - α)) α := by
    have hinner : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) α := by
      simpa using (hasDerivAt_id α).const_sub 1
    exact hinner.log hone_sub_pos.ne'
  have hscaled₂ :
      HasDerivAt (fun x : ℝ ↦ ((n : ℝ) - 1) * Real.log (1 - x))
        (((n : ℝ) - 1) * (((-1) / (1 - α)))) α := by
    exact hlog₂.const_mul ((n : ℝ) - 1)
  have hsum :
      HasDerivAt
        (fun x : ℝ ↦ 2 * Real.log (1 + x * c) + ((n : ℝ) - 1) * Real.log (1 - x))
        (2 * (c / (1 + α * c)) + ((n : ℝ) - 1) * (((-1) / (1 - α)))) α := by
    simpa [Pi.add_apply] using hscaled₁.add hscaled₂
  -- Present the source-facing potential in the same affine-logarithmic normal form as `hsum`.
  change HasDerivAt
    (fun x : ℝ ↦ 2 * Real.log (1 + x * c) + ((n : ℝ) - 1) * Real.log (1 - x))
    (((‖g‖[G,*] - 1) / (1 + α * ((‖g‖[G,*] - 1) / 2))) -
      (((n : ℝ) - 1) / (1 - α))) α
  simpa [oneSidedRoundingPotential, c, sub_eq_add_neg, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Helper for Lemma 7.5: the derivative of the one-sided potential is available as a stable
rewrite lemma on `(0, 1)`. -/
lemma oneSidedRoundingPotential_derivFormula
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (oneSidedRoundingPotential G g) α =
      ((‖g‖[G,*] - 1) / (1 + α * ((‖g‖[G,*] - 1) / 2)) -
        (((n : ℝ) - 1) / (1 - α))) := by
  -- Rewrite the derivative through the explicit `HasDerivAt` computation above.
  have hlog :=
    (oneSidedRoundingPotential_logArgumentsPos G g hn hr ⟨le_of_lt hα.1, hα.2⟩).2
  simpa using
    (oneSidedRoundingPotential_hasDerivAt G g ⟨le_of_lt hα.1, hα.2⟩ hlog).deriv

/-- Helper for Lemma 7.5: multiplying `α*` by the half-gap coefficient gives `σ`. -/
-- TODO: normalize the closed form for `α*` against `σ = (‖g‖[G,*] - n) / (n + 1)` by explicit
-- denominator clearing in the scalar variable `r = ‖g‖[G,*]`.
lemma oneSidedRoundingAlphaStar_mulHalfGap
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2) =
      oneSidedRoundingSigma G g := by
  let r : ℝ := ‖g‖[G,*]
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hr1 : 1 < r := by
    have hr2 : (2 : ℝ) ≤ r := by
      simpa [r] using le_trans hn' hr
    linarith
  have hgap_ne : -1 + r ≠ 0 := by
    linarith
  have hgap_ne' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1.ne'
  -- Clear the single nontrivial denominator `r - 1` in the closed form for `α*`.
  change
    ((2 : ℝ) / ((n : ℝ) + 1) * ((r - (n : ℝ)) / (r - 1))) * ((r - 1) / 2) =
      (r - (n : ℝ)) / ((n : ℝ) + 1)
  field_simp [hgap_ne, hgap_ne']

/-- Helper for Lemma 7.5: the first logarithmic argument at `α*` simplifies to `1 + σ`. -/
lemma oneSidedRoundingAlphaStar_logArgument
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2) =
      1 + oneSidedRoundingSigma G g := by
  -- The half-gap product identity is the exact source-side normalization.
  rw [oneSidedRoundingAlphaStar_mulHalfGap G g hn hr]

/-- Helper for Lemma 7.5: the complementary factor `1 - α*` has the expected closed form. -/
-- TODO: clear denominators in the identity for `1 - α*` after rewriting `α*` in terms of
-- `r = ‖g‖[G,*]`; this is the remaining scalar algebra bridge used by the derivative-zero step.
lemma oneSidedRoundingAlphaStar_one_sub
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    1 - oneSidedRoundingAlphaStar G g =
      (((n : ℝ) - 1) * (‖g‖[G,*] + 1)) /
        (((n : ℝ) + 1) * (‖g‖[G,*] - 1)) := by
  let r : ℝ := ‖g‖[G,*]
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hr1 : 1 < r := by
    have hr2 : (2 : ℝ) ≤ r := by
      simpa [r] using le_trans hn' hr
    linarith
  have hgap_ne : -1 + r ≠ 0 := by
    linarith
  have hgap_ne' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1.ne'
  -- After rewriting `α*` in terms of `r`, the complement `1 - α*` is one rational identity.
  change
    1 - (((2 : ℝ) / ((n : ℝ) + 1)) * ((r - (n : ℝ)) / (r - 1))) =
      (((n : ℝ) - 1) * (r + 1)) / (((n : ℝ) + 1) * (r - 1))
  field_simp [hgap_ne, hgap_ne']
  ring

/-- Helper for Lemma 7.5: the explicit critical point `α*` is feasible for the interval
`[0, 1)`. This auxiliary form is placed before the derivative-zero helper so that the scalar
calculus block does not depend on a later theorem declaration. -/
lemma oneSidedRoundingAlphaStar_memIcoAux
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 := by
  let r : ℝ := ‖g‖[G,*]
  have hα :
      oneSidedRoundingAlphaStar G g =
        ((2 : ℝ) / ((n : ℝ) + 1)) * ((r - (n : ℝ)) / (r - 1)) := by
    simp [oneSidedRoundingAlphaStar, r]
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hr1 : 1 < r := by
    have hr2 : (2 : ℝ) ≤ r := by
      simpa [r] using le_trans hn' hr
    linarith
  have hden_pos : 0 < ((n : ℝ) + 1) * (r - 1) := by
    exact mul_pos (by positivity) (sub_pos.mpr hr1)
  have hlt :
      2 * (r - (n : ℝ)) < ((n : ℝ) + 1) * (r - 1) := by
    nlinarith [show (2 : ℝ) ≤ r by simpa [r] using le_trans hn' hr]
  constructor
  · -- Both factors in the closed form for `α*` are nonnegative.
    rw [hα]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact div_nonneg (sub_nonneg.mpr (by simpa [r] using hr)) (sub_nonneg.mpr hr1.le)
  · -- Clearing denominators reduces the upper bound to the linear inequality
    -- `2 (r - n) < (n + 1) (r - 1)`.
    rw [hα]
    have hrewrite :
        ((2 : ℝ) / ((n : ℝ) + 1)) * ((r - (n : ℝ)) / (r - 1)) =
          (2 * (r - (n : ℝ))) / (((n : ℝ) + 1) * (r - 1)) := by
      field_simp [hr1.ne']
    rw [hrewrite]
    exact (div_lt_one hden_pos).2 hlt

/-- Helper for Lemma 7.5: the ratio `(n - 1) α* / (1 - α*)` is the explicit correction term
`2σ / (1 + σ)`. -/
lemma oneSidedRoundingAlphaStar_ratio
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    ((n : ℝ) - 1) *
        (oneSidedRoundingAlphaStar G g / (1 - oneSidedRoundingAlphaStar G g)) =
      2 * oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g) := by
  let r : ℝ := ‖g‖[G,*]
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
    linarith
  have hr1 : 1 < r := by
    have hr2 : (2 : ℝ) ≤ r := by
      simpa [r] using le_trans hn' hr
    linarith
  have hgap_ne : r - 1 ≠ 0 := sub_ne_zero.mpr hr1.ne'
  have hsum_ne : r + 1 ≠ 0 := by
    linarith
  have hnplus_ne : (n : ℝ) + 1 ≠ 0 := by
    positivity
  have hσarg :
      1 + oneSidedRoundingSigma G g = (r + 1) / ((n : ℝ) + 1) := by
    -- Rewrite `1 + σ` into the scalar variable `r = ‖g‖[G,*]`.
    rw [oneSidedRoundingSigma_def]
    field_simp [hnplus_ne]
    ring
  -- Substitute the closed forms for `α*`, `1 - α*`, and `1 + σ`, then clear denominators.
  rw [oneSidedRoundingAlphaStar_one_sub G g hn hr, oneSidedRoundingAlphaStar, hσarg,
    oneSidedRoundingSigma_def]
  change
    ((n : ℝ) - 1) *
        ((((2 : ℝ) / ((n : ℝ) + 1)) * ((r - (n : ℝ)) / (r - 1))) /
          ((((n : ℝ) - 1) * (r + 1)) / (((n : ℝ) + 1) * (r - 1)))) =
      2 * ((r - (n : ℝ)) / ((n : ℝ) + 1)) / ((r + 1) / ((n : ℝ) + 1))
  field_simp [hgap_ne, hsum_ne, hn1_ne, hnplus_ne]

/-- Helper for Lemma 7.5: the derivative of the one-sided potential is strictly antitone on
`(0, 1)`. -/
lemma oneSidedRoundingPotential_derivStrictAntiOn
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    StrictAntiOn (deriv (oneSidedRoundingPotential G g)) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hr1 : 1 < ‖g‖[G,*] := by
    have hr2 : (2 : ℝ) ≤ ‖g‖[G,*] := le_trans hn' hr
    linarith
  have hgap_pos : 0 < ‖g‖[G,*] - 1 := by
    linarith
  have hcoeff_pos : 0 < (‖g‖[G,*] - 1) / 2 := by
    nlinarith
  have hxlog :=
    (oneSidedRoundingPotential_logArgumentsPos G g hn hr ⟨le_of_lt hx.1, hx.2⟩).2
  have hylog :=
    (oneSidedRoundingPotential_logArgumentsPos G g hn hr ⟨le_of_lt hy.1, hy.2⟩).2
  have hxone : 0 < 1 - x := by
    linarith [hx.2]
  have hyone : 0 < 1 - y := by
    linarith [hy.2]
  have hfirst :
      (‖g‖[G,*] - 1) / (1 + y * ((‖g‖[G,*] - 1) / 2)) <
        (‖g‖[G,*] - 1) / (1 + x * ((‖g‖[G,*] - 1) / 2)) := by
    have hden_lt :
        1 + x * ((‖g‖[G,*] - 1) / 2) <
          1 + y * ((‖g‖[G,*] - 1) / 2) := by
      nlinarith
    exact div_lt_div_of_pos_left hgap_pos hxlog hden_lt
  have hsecond :
      -(((n : ℝ) - 1) / (1 - y)) < -(((n : ℝ) - 1) / (1 - x)) := by
    have hbase :
        ((n : ℝ) - 1) / (1 - x) < ((n : ℝ) - 1) / (1 - y) := by
      have hden_lt : 1 - y < 1 - x := by
        linarith
      exact div_lt_div_of_pos_left hn1_pos hyone hden_lt
    linarith
  -- Each rational summand is strictly decreasing, so their sum is strictly decreasing as well.
  rw [oneSidedRoundingPotential_derivFormula G g hn hr hx,
    oneSidedRoundingPotential_derivFormula G g hn hr hy]
  exact add_lt_add hfirst hsecond

/-- Helper for Lemma 7.5: the derivative of the one-sided potential vanishes at `α*`. -/
lemma oneSidedRoundingPotential_derivEqZeroAtAlphaStar
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    deriv (oneSidedRoundingPotential G g) (oneSidedRoundingAlphaStar G g) = 0 := by
  have hαstar := oneSidedRoundingAlphaStar_memIcoAux G g hn hr
  have hlog :=
    (oneSidedRoundingPotential_logArgumentsPos G g hn hr hαstar).2
  have hformula :
      deriv (oneSidedRoundingPotential G g) (oneSidedRoundingAlphaStar G g) =
        ((‖g‖[G,*] - 1) /
            (1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2)) -
          (((n : ℝ) - 1) / (1 - oneSidedRoundingAlphaStar G g))) := by
    simpa using
      (oneSidedRoundingPotential_hasDerivAt G g hαstar hlog).deriv
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hr1 : 1 < ‖g‖[G,*] := by
    have hr2 : (2 : ℝ) ≤ ‖g‖[G,*] := le_trans hn' hr
    linarith
  have harg₁ :
      1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2) =
        1 + oneSidedRoundingSigma G g :=
    oneSidedRoundingAlphaStar_logArgument G g hn hr
  have harg₂ :=
    oneSidedRoundingAlphaStar_one_sub G g hn hr
  have hσarg :
      1 + oneSidedRoundingSigma G g =
        (‖g‖[G,*] + 1) / ((n : ℝ) + 1) := by
    rw [oneSidedRoundingSigma_def]
    field_simp
    ring
  -- Substitute the closed forms for both denominators and clear the resulting fractions.
  rw [hformula, harg₁, harg₂, hσarg]
  field_simp [hr1.ne', hn1_pos.ne']
  ring

/-- Helper for Lemma 7.5: evaluating `V` at `α*` rewrites the first logarithm to `log (1 + σ)`,
while the second logarithm stays in the stable `log (1 - α*)` form. -/
lemma oneSidedRoundingPotential_alphaStar_sigmaExpansion
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
      2 * Real.log (1 + oneSidedRoundingSigma G g) +
        ((n : ℝ) - 1) *
          Real.log (1 - oneSidedRoundingAlphaStar G g) := by
  -- Rewrite the first logarithmic argument using the source-side identity `α* ((r - 1) / 2) = σ`.
  rw [oneSidedRoundingPotential, oneSidedRoundingAlphaStar_logArgument G g hn hr]

-- Proof sketch: use `2 ≤ n` and `r ≥ n` to obtain `1 < r`, then verify directly that
-- `0 ≤ (2 / (n + 1)) ((r - n) / (r - 1)) < 1`. The `n = 1` boundary is recorded separately by
-- `oneSidedRoundingAlphaStar_eq_if_dualRadius_eq_one_of_dim_one`, which records the separate
-- boundary behavior outside the interior-maximizer range used in Lemma 7.5 (2).
/-- If `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the explicit critical point `α*` lies in
the interval `[0, 1)`. This is the interior-feasibility companion used only in the positive-gap
branch `n ≥ 2`. -/
theorem oneSidedRoundingAlphaStar_mem_Ico
    (G : {A : Mat // A.PosDef}) (g : E) (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 := by
  simpa using oneSidedRoundingAlphaStar_memIcoAux G g hn hr

/-- Boundary companion for Lemma 7.5 (2): in dimension `n = 1`, the closed formula for `α*`
degenerates to `0` at `r = 1` and otherwise collapses to the right endpoint `1` of `[0, 1]`. -/
theorem oneSidedRoundingAlphaStar_eq_if_dualRadius_eq_one_of_dim_one
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : n = 1) :
    oneSidedRoundingAlphaStar G g = if ‖g‖[G,*] = 1 then 0 else 1 := by
  -- Rewrite the closed form for `α*` after substituting the one-dimensional parameter.
  subst hn
  by_cases hr1 : ‖g‖[G,*] = 1
  · -- On the boundary `r = 1`, the numerator vanishes, so the conventionally-defined ratio is `0`.
    simp [oneSidedRoundingAlphaStar, hr1]
  · -- Away from the boundary, the scalar ratio collapses to `1`.
    rw [if_neg hr1, oneSidedRoundingAlphaStar]
    have hgap_ne : ‖g‖[G,*] - 1 ≠ 0 := sub_ne_zero.mpr hr1
    field_simp [hgap_ne]
    ring

/-- Helper for Lemma 7.5: the one-sided updated matrix stays positive definite on `α ∈ [0, 1)`.
-/
lemma oneSidedRoundingUpdatedMatrix_posDef
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (oneSidedRoundingUpdatedMatrix G g α).PosDef := by
  rcases hα with ⟨hα0, hα1⟩
  have hr_nonneg : 0 ≤ ‖g‖[G,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    exact Real.sqrt_nonneg _
  have hr_pos : 0 < ‖g‖[G,*] := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
  have hone_sub_pos : 0 < 1 - α := by
    linarith
  have hcoeff_nonneg :
      0 ≤ (α / ‖g‖[G,*]) +
        (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ) := by
    -- Each summand in the rank-one coefficient is nonnegative on `[0, 1)`.
    have hdiv_nonneg : 0 ≤ α / ‖g‖[G,*] := div_nonneg hα0 hr_pos.le
    have hsquare_nonneg :
        0 ≤ (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ) := by
      positivity
    linarith
  -- Add the nonnegative rank-one term to the positive-definite scaled base matrix.
  rw [oneSidedRoundingUpdatedMatrix_def]
  exact (G.2.smul hone_sub_pos).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star g).smul hcoeff_nonneg)

/-- Helper for Lemma 7.5: the updated quadratic form splits into the base `G`-term and the
rank-one correction along `g`. -/
-- TODO: Rebuild this by expanding `Matrix.toEuclideanLin_apply` directly and isolating the
-- `vecMulVec` quadratic-form computation in a dedicated bridge lemma.
private lemma oneSidedRoundingUpdatedMatrix_quadratic
    (G : {A : Mat // A.PosDef}) (g x : E) (α : ℝ) :
    inner ℝ ((Matrix.toEuclideanLin (oneSidedRoundingUpdatedMatrix G g α)) x) x =
      (1 - α) * ‖x‖[G] ^ (2 : ℕ) +
        ((α / ‖g‖[G,*]) +
            (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) *
          (inner ℝ g x) ^ (2 : ℕ) :=
  by
  -- Expand the updated matrix action into the scaled base term and the rank-one correction.
  calc
    inner ℝ ((Matrix.toEuclideanLin (oneSidedRoundingUpdatedMatrix G g α)) x) x
      = inner ℝ
          ((1 - α) • ((Matrix.toEuclideanLin G.1) x) +
            ((α / ‖g‖[G,*]) +
                (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) •
              ((Matrix.vecMulVec g g).toEuclideanLin x)) x := by
          simp [oneSidedRoundingUpdatedMatrix_def, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    _ =
        inner ℝ ((1 - α) • ((Matrix.toEuclideanLin G.1) x)) x +
          inner ℝ
            (((α / ‖g‖[G,*]) +
                  (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) •
                ((Matrix.vecMulVec g g).toEuclideanLin x)) x := by
          rw [inner_add_left]
    _ =
        (1 - α) * inner ℝ ((Matrix.toEuclideanLin G.1) x) x +
          ((α / ‖g‖[G,*]) +
              (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) *
            inner ℝ ((Matrix.vecMulVec g g).toEuclideanLin x) x := by
          simp [real_inner_smul_left]
    _ =
        (1 - α) * ‖x‖[G] ^ (2 : ℕ) +
          ((α / ‖g‖[G,*]) +
              (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) *
            (inner ℝ g x) ^ (2 : ℕ) := by
          rw [← positiveDefMatrixNorm_sq_eq_matrix_quadratic G x, vecMulVec_quadratic]

/-- Helper for Lemma 7.5: on `α ∈ [0, 1)`, the updated matrix stays positive definite even in the
degenerate zero-radius branch `‖g‖[G,*] = 0`. -/
-- TODO: The zero-radius branch should first prove `g = 0` from the dual-norm bound, then reduce
-- the matrix to `(1 - α) • G.1`; the current imported inner-product lemmas need to be realigned.
private lemma oneSidedRoundingUpdatedMatrix_posDef_of_mem_Ico
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (oneSidedRoundingUpdatedMatrix G g α).PosDef :=
  by
  by_cases hzero : ‖g‖[G,*] = 0
  · rcases hα with ⟨_, hα1⟩
    have hone_sub_pos : 0 < 1 - α := by
      linarith
    have hmatrix :
        oneSidedRoundingUpdatedMatrix G g α = (1 - α) • G.1 := by
      -- On the zero-radius branch, every `α / ‖g‖[G,*]` term vanishes definitionally.
      simp [oneSidedRoundingUpdatedMatrix_def, hzero]
    rw [hmatrix]
    exact G.2.smul hone_sub_pos
  · -- Away from the degenerate branch, reuse the nonzero-radius positive-definiteness theorem.
    exact oneSidedRoundingUpdatedMatrix_posDef G g hzero hα

/-- Helper for Lemma 7.5: squaring the primal norm of the updated matrix yields the scalar
quadratic form used in the support-function comparison. -/
-- TODO: This is a one-line consequence of the quadratic-form bridge once
-- `oneSidedRoundingUpdatedMatrix_quadratic` is restored.
private lemma oneSidedRoundingUpdatedMatrix_primalNorm_sq
    (G : {A : Mat // A.PosDef}) (g x : E) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
      oneSidedRoundingUpdatedMatrix_posDef_of_mem_Ico G g hα⟩] ^ (2 : ℕ) =
      (1 - α) * ‖x‖[G] ^ (2 : ℕ) +
        ((α / ‖g‖[G,*]) +
            (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) *
          (inner ℝ g x) ^ (2 : ℕ) :=
  by
  let updated : {A : Mat // A.PosDef} :=
    ⟨oneSidedRoundingUpdatedMatrix G g α, oneSidedRoundingUpdatedMatrix_posDef_of_mem_Ico G g hα⟩
  -- Rewrite the squared norm through the updated quadratic form and then use the bridge lemma.
  calc
    ‖x‖[updated] ^ (2 : ℕ) =
        inner ℝ ((Matrix.toEuclideanLin updated.1) x) x := by
          simpa [updated] using positiveDefMatrixNorm_sq_eq_matrix_quadratic updated x
    _ = (1 - α) * ‖x‖[G] ^ (2 : ℕ) +
          ((α / ‖g‖[G,*]) +
              (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) *
            (inner ℝ g x) ^ (2 : ℕ) := by
          simpa [updated] using oneSidedRoundingUpdatedMatrix_quadratic G g x α

/-- Helper for Lemma 7.5: translating an affine ellipsoid adds the center pairing to its support
function up to the centered support term. -/
private lemma supportFunction_affineEllipsoid_translate_le
    (H : Mat) (v x : E) :
    ξ[E(H, v)] x ≤ (inner ℝ v x : EReal) + ξ[E(H, (0 : E))] x := by
  rw [supportFunction_apply]
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy0 : y - v ∈ E(H, (0 : E)) := by
    -- Recenter the membership witness so the remaining support term is centered at the origin.
    rw [mem_affineEllipsoid_iff] at hy ⊢
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
  have hsupport :
      ((inner ℝ (y - v) x : ℝ) : EReal) ≤ ξ[E(H, (0 : E))] x := by
    -- The translated residual is one admissible centered support witness.
    rw [supportFunction_apply]
    exact le_sSup ⟨y - v, hy0, rfl⟩
  have hdecomp : v + (y - v) = y := by
    abel
  -- Split the translated pairing into the center term and the centered residual term.
  calc
    ((inner ℝ y x : ℝ) : EReal)
        = ((inner ℝ (v + (y - v)) x : ℝ) : EReal) := by
            exact congrArg (fun z : E ↦ ((inner ℝ z x : ℝ) : EReal)) hdecomp.symm
    _ = ((inner ℝ v x + inner ℝ (y - v) x : ℝ) : EReal) := by
          rw [inner_add_left]
    _ = (inner ℝ v x : EReal) + ((inner ℝ (y - v) x : ℝ) : EReal) := by
          rw [EReal.coe_add]
    _ ≤ (inner ℝ v x : EReal) + ξ[E(H, (0 : E))] x := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hsupport (inner ℝ v x : EReal)

/-- Helper for Lemma 7.5: vanishing weighted dual radius forces the source point to be `0`. -/
private lemma eq_zero_of_dualNorm_eq_zero
    (G : {A : Mat // A.PosDef}) {g : E}
    (hzero : ‖g‖[G,*] = 0) :
    g = 0 := by
  by_contra hg0
  have hquad_nonneg :
      0 ≤ inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
    have hPosLin : (Matrix.toEuclideanLin G.1⁻¹).IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr G.2.inv.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right g
  have hquad_eq_zero :
      inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) = 0 := by
    have hsqrt_eq_zero :
        Real.sqrt (inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g)) = 0 := by
      simpa [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv] using hzero
    exact (Real.sqrt_eq_zero hquad_nonneg).mp hsqrt_eq_zero
  have hg_coord : g.ofLp ≠ 0 := by
    intro hg_coord
    apply hg0
    ext i
    exact congrArg (fun y : Fin n → ℝ ↦ y i) hg_coord
  have hdot_pos : 0 < dotProduct g.ofLp (G.1⁻¹ *ᵥ g.ofLp) :=
    G.2.inv.dotProduct_mulVec_pos hg_coord
  have hinner_eq :
      inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) =
        dotProduct g.ofLp (G.1⁻¹ *ᵥ g.ofLp) := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm] using
      EuclideanSpace.inner_eq_star_dotProduct g ((Matrix.toEuclideanLin G.1⁻¹) g)
  rw [hinner_eq] at hquad_eq_zero
  exact hdot_pos.ne' hquad_eq_zero

/-- Helper for Lemma 7.5: the support of the weighted unit ball `W₁(G)` is the primal norm for
the inverse matrix `G⁻¹`. -/
private lemma supportFunction_weightedUnitBall_eq_coe_invPrimalNorm
    (G : {A : Mat // A.PosDef}) (x : E) :
    ξ[W₁(G)] x = (((‖x‖[⟨G.1⁻¹, G.2.inv⟩] : ℝ)) : EReal) := by
  -- Normalize the source-facing weighted unit ball to the centered affine ellipsoid owner once.
  rw [show W₁(G) = E(G.1⁻¹, (0 : E)) by
    simpa using centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  -- The centered affine ellipsoid support is exactly the primal norm of its defining matrix.
  simpa using supportFunction_affineEllipsoid_zero_eq_coe_primalNorm G.1⁻¹ G.2.inv x

/-- Helper for Lemma 7.5: in the branch `inner ℝ g x ≤ ‖x‖[G]`, the translated centered support
term stays below the base primal norm. -/
private lemma oneSidedShiftedSupport_le_baseNorm_of_inner_le
    (G : {A : Mat // A.PosDef}) (g x : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hcmp : inner ℝ g x ≤ ‖x‖[G]) :
    ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
        ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
          oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩] ≤
      ‖x‖[G] := by
  let r : ℝ := ‖g‖[G,*]
  let a : ℝ := ‖x‖[G]
  let b : ℝ := inner ℝ g x
  let s : ℝ := ((r - 1) / (2 * r)) * α
  let updated : {A : Mat // A.PosDef} :=
    ⟨oneSidedRoundingUpdatedMatrix G g α, oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩
  let updatedIco : {A : Mat // A.PosDef} :=
    ⟨oneSidedRoundingUpdatedMatrix G g α, oneSidedRoundingUpdatedMatrix_posDef_of_mem_Ico G g hα⟩
  have hα0 : 0 ≤ α := hα.1
  have hα1 : α < 1 := hα.2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    exact Real.sqrt_nonneg _
  have hr_pos : 0 < r := by
    exact lt_of_le_of_ne hr_nonneg (by simpa [r] using hr0.symm)
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using (positiveDefMatrixNorm G.1 G.2).apply_nonneg x
  have hupdated_nonneg : 0 ≤ ‖x‖[updated] := by
    simpa [updated] using updated.2.primalSeminorm.apply_nonneg x
  have hupdated_eq : updated = updatedIco := by
    apply Subtype.ext
    simp [updated, updatedIco]
  -- The lower duality estimate comes from applying the dual pairing bound to `-x`.
  have hdual_lower : -b ≤ r * a := by
    have hinner :
        inner ℝ g (-x) ≤ ‖g‖[G,*] * ‖-x‖[G] := by
      simpa [mul_comm] using
        Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G.1 G.2) (-x) g
    simpa [a, b, r] using hinner
  have hgap :
      (a - s * b) ^ (2 : ℕ) - ‖x‖[updated] ^ (2 : ℕ) =
        (α / r) * (a - b) * (r * a + b) := by
    -- Rewrite the updated norm square to isolate the scalar branch identity.
    rw [hupdated_eq]
    dsimp [a, b, r, s, updatedIco]
    rw [oneSidedRoundingUpdatedMatrix_primalNorm_sq G g x hα]
    field_simp [hr0]
    ring
  have hgap_nonneg : 0 ≤ (α / r) * (a - b) * (r * a + b) := by
    have hdiv_nonneg : 0 ≤ α / r := div_nonneg hα0 hr_pos.le
    have hab_nonneg : 0 ≤ a - b := sub_nonneg.mpr hcmp
    have hsum_nonneg : 0 ≤ r * a + b := by
      nlinarith
    exact mul_nonneg (mul_nonneg hdiv_nonneg hab_nonneg) hsum_nonneg
  have hsq :
      ‖x‖[updated] ^ (2 : ℕ) ≤ (a - s * b) ^ (2 : ℕ) := by
    nlinarith [hgap, hgap_nonneg]
  have hright_nonneg : 0 ≤ a - s * b := by
    by_cases hs_nonneg : 0 ≤ s
    · have hs_le_half : s ≤ (1 : ℝ) / 2 := by
        have hcoeff_le :
            (r - 1) / (2 * r) ≤ (1 : ℝ) / 2 := by
          field_simp [hr_pos.ne']
          nlinarith
        have hs_le_alpha :
            s ≤ ((1 : ℝ) / 2) * α := by
          dsimp [s]
          exact mul_le_mul_of_nonneg_right hcoeff_le hα0
        nlinarith
      have hmul : s * b ≤ s * a := mul_le_mul_of_nonneg_left hcmp hs_nonneg
      nlinarith
    · have hs_neg : s < 0 := lt_of_not_ge hs_nonneg
      have hb_lower : -(r * a) ≤ b := by
        nlinarith
      have hmul : s * b ≤ s * (-(r * a)) := by
        exact mul_le_mul_of_nonpos_left hb_lower hs_neg.le
      have hfac_pos : 0 < 1 + s * r := by
        dsimp [s]
        field_simp [hr_pos.ne']
        nlinarith
      have hbase_nonneg : 0 ≤ a - s * (-(r * a)) := by
        calc
          0 ≤ a * (1 + s * r) := mul_nonneg ha_nonneg hfac_pos.le
          _ = a - s * (-(r * a)) := by ring
      nlinarith
  -- Compare squares in the nonnegative regime and then rearrange.
  have hle : ‖x‖[updated] ≤ a - s * b := le_of_sq_le_sq hsq hright_nonneg
  nlinarith

/-- Helper for Lemma 7.5: in the branch `‖x‖[G] ≤ inner ℝ g x`, the translated centered support
term stays below the singleton support `inner ℝ g x`. -/
private lemma oneSidedShiftedSupport_le_inner_of_norm_le_inner
    (G : {A : Mat // A.PosDef}) (g x : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hcmp : ‖x‖[G] ≤ inner ℝ g x) :
    ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
        ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
          oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩] ≤
      inner ℝ g x := by
  let r : ℝ := ‖g‖[G,*]
  let a : ℝ := ‖x‖[G]
  let b : ℝ := inner ℝ g x
  let s : ℝ := ((r - 1) / (2 * r)) * α
  let updated : {A : Mat // A.PosDef} :=
    ⟨oneSidedRoundingUpdatedMatrix G g α, oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩
  let updatedIco : {A : Mat // A.PosDef} :=
    ⟨oneSidedRoundingUpdatedMatrix G g α, oneSidedRoundingUpdatedMatrix_posDef_of_mem_Ico G g hα⟩
  have hα0 : 0 ≤ α := hα.1
  have hα1 : α < 1 := hα.2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    exact Real.sqrt_nonneg _
  have hr_pos : 0 < r := by
    exact lt_of_le_of_ne hr_nonneg (by simpa [r] using hr0.symm)
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using (positiveDefMatrixNorm G.1 G.2).apply_nonneg x
  have hb_nonneg : 0 ≤ b := le_trans ha_nonneg hcmp
  have hupdated_eq : updated = updatedIco := by
    apply Subtype.ext
    simp [updated, updatedIco]
  have hgap :
      ((1 - s) * b) ^ (2 : ℕ) - ‖x‖[updated] ^ (2 : ℕ) =
        (1 - α) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) := by
    -- Rewrite the updated norm square and normalize the right-branch square identity.
    rw [hupdated_eq]
    dsimp [a, b, r, s, updatedIco]
    rw [oneSidedRoundingUpdatedMatrix_primalNorm_sq G g x hα]
    field_simp [hr0]
    ring
  have hgap_nonneg : 0 ≤ (1 - α) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) := by
    have hone_sub_nonneg : 0 ≤ 1 - α := by
      linarith
    have hsq_nonneg : 0 ≤ b ^ (2 : ℕ) - a ^ (2 : ℕ) := by
      nlinarith
    exact mul_nonneg hone_sub_nonneg hsq_nonneg
  have hsq :
      ‖x‖[updated] ^ (2 : ℕ) ≤ ((1 - s) * b) ^ (2 : ℕ) := by
    nlinarith [hgap, hgap_nonneg]
  have hs_lt_one : s < 1 := by
    by_cases hcoeff_nonneg : 0 ≤ (r - 1) / (2 * r)
    · have hcoeff_lt :
          (r - 1) / (2 * r) < (1 : ℝ) / 2 := by
        field_simp [hr_pos.ne']
        nlinarith
      have hs_le :
          s ≤ ((1 : ℝ) / 2) * α := by
        dsimp [s]
        exact mul_le_mul_of_nonneg_right hcoeff_lt.le hα0
      nlinarith
    · have hs_nonpos : s ≤ 0 := by
        dsimp [s]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hcoeff_nonneg) hα0
      linarith
  have hright_nonneg : 0 ≤ (1 - s) * b := by
    nlinarith
  -- Compare squares and then recover the desired linear inequality.
  have hle : ‖x‖[updated] ≤ (1 - s) * b := le_of_sq_le_sq hsq hright_nonneg
  nlinarith

/-- Helper for Lemma 7.5: the translated updated ellipsoid has support bounded by the maximum of
the support of `W[1](G.1)` and the singleton `{g}`. -/
private lemma oneSidedRoundingShiftedSupport_le_max
    (G : {A : Mat // A.PosDef}) (g x : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
        ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
          oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩] ≤
      max ‖x‖[G] (inner ℝ g x) :=
  by
  -- Route correction: the intended closure is by case-splitting on the displayed `max` and
  -- delegating to the two scalar branch lemmas above.
  by_cases hcmp : inner ℝ g x ≤ ‖x‖[G]
  · calc
      ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
          ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
            oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩]
        ≤ ‖x‖[G] :=
          oneSidedShiftedSupport_le_baseNorm_of_inner_le G g x hr0 hα hcmp
      _ ≤ max ‖x‖[G] (inner ℝ g x) := le_max_left _ _
  · have hcmp' : ‖x‖[G] ≤ inner ℝ g x := le_of_not_ge hcmp
    calc
      ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
          ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α,
            oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα⟩]
        ≤ inner ℝ g x :=
          oneSidedShiftedSupport_le_inner_of_norm_le_inner G g x hr0 hα hcmp'
      _ ≤ max ‖x‖[G] (inner ℝ g x) := le_max_right _ _

-- Clause (1) is written directly with the source hull `convexHull ℝ (W[1](G.1) ∪ ({g} : Set E))`
-- rather than the current `Definition_7_30` notation `C_[g](G)`, whose owner packages a
-- different unit ball.
/-- Boundary-safe specialization of Lemma 7.5 (1): when `‖g‖*_G = 0`, the translated formula
reduces to the centered ellipsoid with shape `(1 - α) G`, and the source hull is written directly
as `convexHull ℝ (W[1](G.1) ∪ ({g} : Set E))`. -/
theorem
    centeredOneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint_of_dualNorm_eq_zero
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hzero : ‖g‖[G,*] = 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    W[1]((0 : E), ((1 - α) • G.1)) ⊆
      convexHull ℝ (W[1](G.1) ∪ ({g} : Set E)) := by
  have hg_zero : g = 0 := eq_zero_of_dualNorm_eq_zero G hzero
  subst hg_zero
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hscaledPos : ((1 - α) • G.1).PosDef := G.2.smul hone_sub_pos
  have hBaseCompact : IsCompact (W[1](G.1) : Set E) := by
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      affineEllipsoid_isCompact_of_posDef G.1 G.2 (0 : E)
  have hBaseNonempty : (W[1](G.1) : Set E).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      center_mem_affineEllipsoid G.1 (0 : E)
  have hBaseConvex : Convex ℝ (W[1](G.1) : Set E) := by
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      affineEllipsoid_convex_of_posDef G.1 G.2
  have hscaled_subset_base : W[1]((0 : E), ((1 - α) • G.1)) ⊆ W[1](G.1) := by
    refine subset_of_supportFunction_le_on_domain
      (W[1]((0 : E), ((1 - α) • G.1))) (W[1](G.1))
      hBaseNonempty hBaseCompact.isClosed hBaseConvex ?_
    intro x hxdom
    rw [matrixEllipsoid_one_eq_affineEllipsoid,
      centeredMatrixEllipsoid_one_eq_affineEllipsoid]
    rw [supportFunction_affineEllipsoid_zero_eq_coe_primalNorm ((1 - α) • G.1) hscaledPos,
      supportFunction_affineEllipsoid_zero_eq_coe_primalNorm G.1 G.2]
    change
      ((((‖x‖[⟨(1 - α) • G.1, hscaledPos⟩] : ℝ)) : EReal) ≤
        (((‖x‖[G] : ℝ)) : EReal))
    have hscaled_sq :
        ‖x‖[⟨(1 - α) • G.1, hscaledPos⟩] ^ (2 : ℕ) =
          (1 - α) * ‖x‖[G] ^ (2 : ℕ) := by
      calc
        ‖x‖[⟨(1 - α) • G.1, hscaledPos⟩] ^ (2 : ℕ) =
            inner ℝ ((Matrix.toEuclideanLin ((1 - α) • G.1)) x) x := by
              simpa using
                positiveDefMatrixNorm_sq_eq_matrix_quadratic
                  (⟨(1 - α) • G.1, hscaledPos⟩ : {A : Mat // A.PosDef}) x
        _ = (1 - α) * inner ℝ ((Matrix.toEuclideanLin G.1) x) x := by
              simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, real_inner_smul_left]
        _ = (1 - α) * ‖x‖[G] ^ (2 : ℕ) := by
              rw [← positiveDefMatrixNorm_sq_eq_matrix_quadratic G x]
    have hscaled_le :
        ‖x‖[⟨(1 - α) • G.1, hscaledPos⟩] ≤ ‖x‖[G] := by
      have hone_sub_le_one : 1 - α ≤ 1 := by
        linarith [hα.1]
      have hnorm_nonneg : 0 ≤ ‖x‖[G] := by
        positivity
      have hsq :
          ‖x‖[⟨(1 - α) • G.1, hscaledPos⟩] ^ (2 : ℕ) ≤ ‖x‖[G] ^ (2 : ℕ) := by
        rw [hscaled_sq]
        nlinarith
      exact le_of_sq_le_sq hsq hnorm_nonneg
    exact_mod_cast hscaled_le
  -- Route correction: after collapsing `g = 0`, it is enough to pass through the base ellipsoid.
  refine hscaled_subset_base.trans ?_
  intro x hx
  exact subset_convexHull ℝ (W[1](G.1) ∪ ({(0 : E)} : Set E)) (Or.inl hx)

private theorem
    oneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint_of_dualNorm_ne_zero
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    W[1](((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) • g),
      (oneSidedRoundingUpdatedMatrix G g α)) ⊆
        convexHull ℝ (W[1](G.1) ∪ ({g} : Set E)) := by
  let shift : E := ((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) • g)
  let source : Set E := matrixEllipsoid (oneSidedRoundingUpdatedMatrix G g α) shift 1
  let hull : Set E := convexHull ℝ (W[1](G.1) ∪ ({g} : Set E))
  have hUpdatedPos :
      (oneSidedRoundingUpdatedMatrix G g α).PosDef :=
    oneSidedRoundingUpdatedMatrix_posDef G g hr0 hα
  have hBaseCompact : IsCompact (W[1](G.1) : Set E) := by
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      affineEllipsoid_isCompact_of_posDef G.1 G.2 (0 : E)
  have hBaseConvex : Convex ℝ (W[1](G.1) : Set E) := by
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      affineEllipsoid_convex_of_posDef G.1 G.2
  have hBaseNonempty : (W[1](G.1) : Set E).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      center_mem_affineEllipsoid G.1 (0 : E)
  have hPointNonempty : ({g} : Set E).Nonempty := by
    simp
  have hPointFinite : ({g} : Set E).Finite := by
    simp
  have hPointCompact : IsCompact (convexHull ℝ ({g} : Set E)) :=
    hPointFinite.isCompact_convexHull ℝ
  have hHullCompact :
      IsCompact hull := by
    dsimp [hull]
    rw [convexHull_union hBaseNonempty hPointNonempty, hBaseConvex.convexHull_eq]
    exact convexJoin_isCompact hBaseCompact hPointCompact
  have hHullNonempty :
      hull.Nonempty := by
    rcases hBaseNonempty with ⟨y, hy⟩
    exact ⟨y, by
      dsimp [hull]
      exact subset_convexHull ℝ _ (Or.inl hy)⟩
  have hHullConvex : Convex ℝ hull := by
    dsimp [hull]
    simpa using convex_convexHull ℝ (W[1](G.1) ∪ ({g} : Set E))
  -- Compare the source ellipsoid and the target hull through their support functions.
  refine subset_of_supportFunction_le_on_domain source hull
    hHullNonempty hHullCompact.isClosed hHullConvex ?_
  intro x hxdom
  have hsource :
      ξ[source] x ≤
        (((((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
          ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α, hUpdatedPos⟩]) : ℝ) : EReal) := by
    calc
      ξ[source] x
          = ξ[E(oneSidedRoundingUpdatedMatrix G g α, shift)] x := by
              simp [source, matrixEllipsoid_one_eq_affineEllipsoid]
      _ ≤ (inner ℝ shift x : EReal) +
            ξ[E(oneSidedRoundingUpdatedMatrix G g α, (0 : E))] x :=
              supportFunction_affineEllipsoid_translate_le
                (oneSidedRoundingUpdatedMatrix G g α) shift x
      _ = (inner ℝ shift x : EReal) +
            (((‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α, hUpdatedPos⟩] : ℝ)) : EReal) := by
              rw [supportFunction_affineEllipsoid_zero_eq_coe_primalNorm
                (oneSidedRoundingUpdatedMatrix G g α) hUpdatedPos]
      _ =
          (((((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
            ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α, hUpdatedPos⟩]) : ℝ) : EReal) := by
              rw [show (inner ℝ shift x : EReal) =
                  ((((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x : ℝ)) : EReal) by
                    simp [shift, real_inner_smul_left, mul_comm, mul_left_comm]]
              rw [EReal.coe_add]
  have htarget :
      ξ[hull] x =
        max ((((‖x‖[G] : ℝ)) : EReal)) (inner ℝ g x : EReal) := by
    rw [show hull = convexHull ℝ (W[1](G.1) ∪ ({g} : Set E)) by rfl]
    rw [supportFunction_convexHull_union_eq_max]
    rw [centeredMatrixEllipsoid_one_eq_affineEllipsoid]
    rw [supportFunction_affineEllipsoid_zero_eq_coe_primalNorm G.1 G.2]
    simp [supportFunction_apply]
  have hmax_coe :
      (((max ‖x‖[G] (inner ℝ g x) : ℝ)) : EReal) =
        max ((((‖x‖[G] : ℝ)) : EReal)) (inner ℝ g x : EReal) := by
    by_cases hcompare : ‖x‖[G] ≤ inner ℝ g x
    · rw [max_eq_right hcompare, max_eq_right]
      exact_mod_cast hcompare
    · have hcompare' : inner ℝ g x ≤ ‖x‖[G] := le_of_not_ge hcompare
      rw [max_eq_left hcompare', max_eq_left]
      exact_mod_cast hcompare'
  have hreal :
      (((((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
        ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α, hUpdatedPos⟩]) : ℝ) : EReal) ≤
        max ((((‖x‖[G] : ℝ)) : EReal)) (inner ℝ g x : EReal) := by
    have hreal' :
        (((((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) * inner ℝ g x) +
          ‖x‖[⟨oneSidedRoundingUpdatedMatrix G g α, hUpdatedPos⟩]) : ℝ) : EReal) ≤
          (((max ‖x‖[G] (inner ℝ g x) : ℝ)) : EReal) := by
      exact_mod_cast oneSidedRoundingShiftedSupport_le_max G g x hr0 hα
    exact hreal'.trans_eq hmax_coe
  exact hsource.trans (htarget.symm ▸ hreal)

-- Semantic recall note: no upstream all-cases hull inclusion theorem surfaced for this owner, so
-- the source-faithful API keeps the raw translated ellipsoid surface on the nonzero-radius branch
-- and leaves the zero-radius boundary case as the separate centered companion above.
/-- Lemma 7.5 (1): for every `α ∈ [0, 1)`, if `‖g‖*_G ≠ 0`, then the source one-sided ellipsoid
`W[1]((((r - 1) / (2r)) * α) • g, G(α))` belongs to the source hull `C_g(G)`, written directly as
`convexHull ℝ (W[1](G.1) ∪ ({g} : Set E))`. The zero-radius boundary case is recorded separately by
`centeredOneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint_of_dualNorm_eq_zero`.
-/
theorem oneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    W[1](((((‖g‖[G,*] - 1) / (2 * ‖g‖[G,*])) * α) • g),
      (oneSidedRoundingUpdatedMatrix G g α)) ⊆
        convexHull ℝ (W[1](G.1) ∪ ({g} : Set E)) :=
  oneSidedRoundingEllipsoid_subset_convexHullOfWeightedUnitBallAndPoint_of_dualNorm_ne_zero
    G g hr0 hα

/-- Helper for Lemma 7.5: the determinant ratio of the one-sided updated matrix has the closed
form from equation `(7.u274)`. -/
private lemma oneSidedRoundingUpdatedMatrix_detRatio
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    Matrix.det (oneSidedRoundingUpdatedMatrix G g α) / Matrix.det G.1 =
      (1 - α) ^ (n - 1) * (1 + α * ((‖g‖[G,*] - 1) / 2)) ^ (2 : ℕ) := by
  by_cases hn0 : n = 0
  · -- In dimension `0`, the ambient space is trivial, so `‖g‖[G,*] = 0`, contradicting `hr0`.
    subst hn0
    have hg0 : g = 0 := Subsingleton.elim _ _
    subst hg0
    have hzero : ‖(0 : EuclideanSpace ℝ (Fin 0))‖[G,*] = 0 := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    exact (hr0 (by simpa using hzero)).elim
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
  let r : ℝ := ‖g‖[G,*]
  let c : ℝ :=
    (α / r) + (((r - 1) / 2) ^ (2 : ℕ)) * (α / r) ^ (2 : ℕ)
  let t : ℝ := c / (1 - α)
  have hdetG_unit : IsUnit (Matrix.det G.1) := by
    exact isUnit_iff_ne_zero.mpr (ne_of_gt G.2.det_pos)
  have hdetG_ne : Matrix.det G.1 ≠ 0 := by
    exact ne_of_gt G.2.det_pos
  have hone_sub_ne : 1 - α ≠ 0 := sub_ne_zero.mpr hα.2.ne'
  have hquad_nonneg : 0 ≤ inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
    have hPosLin : (Matrix.toEuclideanLin G.1⁻¹).IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr G.2.inv.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right g
  have hr_sq :
      r ^ (2 : ℕ) = inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g) := by
    dsimp [r]
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv, Real.sq_sqrt hquad_nonneg]
  have hmatrix :
      oneSidedRoundingUpdatedMatrix G g α =
        (1 - α) • (G.1 + t • Matrix.vecMulVec g g) := by
    -- Pull out the scalar factor `(1 - α)` so the remaining determinant is a rank-one update.
    rw [oneSidedRoundingUpdatedMatrix_def]
    ext i j
    dsimp [t, c, r]
    field_simp [hone_sub_ne, hr0]
  have hpow :
      (1 - α) ^ n = (1 - α) ^ (n - 1) * (1 - α) := by
    cases n with
    | zero =>
        cases hn0 rfl
    | succ k =>
        rw [pow_succ, Nat.succ_sub_one]
  have hpow_card :
      (1 - α) ^ Fintype.card (Fin n) = (1 - α) ^ (n - 1) * (1 - α) := by
    simpa using hpow
  have hcore :
      Matrix.det (G.1 + t • Matrix.vecMulVec g g) =
        Matrix.det G.1 * (1 + t * r ^ (2 : ℕ)) := by
    -- Apply the matrix determinant lemma to the rank-one perturbation.
    calc
      Matrix.det (G.1 + t • Matrix.vecMulVec g g)
          = Matrix.det G.1 *
              (1 + Matrix.replicateRow (Fin 1) g.ofLp * G.1⁻¹ *
                Matrix.replicateCol (Fin 1) ((t • g).ofLp)).det := by
              simpa [Matrix.vecMulVec_eq (Fin 1)] using
                (@Matrix.det_add_replicateCol_mul_replicateRow
                  (Fin n) ℝ _ _ _ (Fin 1) inferInstance G.1
                  hdetG_unit ((t • g).ofLp) g.ofLp)
      _ = Matrix.det G.1 * (1 + t * inner ℝ g ((Matrix.toEuclideanLin G.1⁻¹) g)) := by
            rw [oneByOneRankOneCorrection_det G.1 g t]
      _ = Matrix.det G.1 * (1 + t * r ^ (2 : ℕ)) := by
            rw [hr_sq]
  -- Rewrite the determinant ratio, then clear the remaining scalar denominators.
  rw [hmatrix, Matrix.det_smul, hcore]
  rw [hpow_card]
  dsimp [t, c, r]
  field_simp [hdetG_ne, hone_sub_ne, hr0]
  ring

-- Proof sketch: under the explicit nonzero-radius hypothesis, use the private determinant-ratio
-- helper and rewrite the logarithm into the explicit scalar potential.
/-- Under the explicit nonzero-radius hypothesis `r = ‖g‖*_G ≠ 0`, the scalar potential `V(α)`
agrees with the logarithmic determinant ratio `log (det G(α) / det G)` on `α ∈ [0, 1)`. -/
theorem oneSidedRoundingPotential_eq_log_det_ratio
    (G : {A : Mat // A.PosDef}) (g : E) {α : ℝ}
    (hr0 : ‖g‖[G,*] ≠ 0)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    oneSidedRoundingPotential G g α =
      Real.log (Matrix.det (oneSidedRoundingUpdatedMatrix G g α) / Matrix.det G.1) := by
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    have hg0 : g = 0 := Subsingleton.elim _ _
    subst hg0
    have hzero : ‖(0 : EuclideanSpace ℝ (Fin 0))‖[G,*] = 0 := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    exact hr0 (by simpa using hzero)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred hn_pos
  have hr_nonneg : 0 ≤ ‖g‖[G,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    exact Real.sqrt_nonneg _
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hcoeff_lower : -(1 : ℝ) / 2 ≤ (‖g‖[G,*] - 1) / 2 := by
    nlinarith
  have hprod_lower :
      -(α / 2) ≤ α * ((‖g‖[G,*] - 1) / 2) := by
    nlinarith [hα.1, hcoeff_lower]
  have harg_pos : 0 < 1 + α * ((‖g‖[G,*] - 1) / 2) := by
    linarith [hα.2, hprod_lower]
  -- Rewrite the determinant ratio into the product of the two logarithmic factors.
  rw [oneSidedRoundingUpdatedMatrix_detRatio G g hr0 hα, oneSidedRoundingPotential,
    Real.log_mul (pow_ne_zero _ hone_sub_pos.ne') (pow_ne_zero _ harg_pos.ne'),
    Real.log_pow, Real.log_pow, hcast]
  ring

-- The interior calculus arguments live in the branch `2 ≤ n`, so both the helper theorems below
-- and the public source-facing clauses (2)–(5) keep that dimensional side condition explicit.
-- Proof sketch after statement repair: differentiate the explicit formula for
-- `oneSidedRoundingPotential G g` on `[0, 1)`, solve the first-order condition, and use
-- concavity to conclude that the displayed critical point is the maximizer on the interior
-- branch; the excluded low-dimensional boundary behavior is handled separately via
-- `oneSidedRoundingAlphaStar_eq_if_dualRadius_eq_one_of_dim_one`.
/-- Helper for Lemma 7.5 (2): if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies
`r ≥ n`, then the
potential
`V(α) = 2 log (1 + α (r - 1) / 2) + (n - 1) log (1 - α)` attains its maximum on `[0, 1)` at
`α* = (2 / (n + 1)) ((r - n) / (r - 1))`. The one-dimensional boundary behavior is recorded by
`oneSidedRoundingAlphaStar_eq_if_dualRadius_eq_one_of_dim_one`. -/
theorem oneSidedRoundingPotential_isMaxOn_alphaStar_of_two_le
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n) (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    IsMaxOn (oneSidedRoundingPotential G g) (Set.Ico (0 : ℝ) 1)
      (oneSidedRoundingAlphaStar G g) := by
  have hαstar :
      oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 :=
    oneSidedRoundingAlphaStar_memIcoAux G g hn hr
  have hlog :
      0 < 1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2) :=
    (oneSidedRoundingPotential_logArgumentsPos G g hn hr hαstar).2
  have hderivAtRaw :
      HasDerivAt (oneSidedRoundingPotential G g)
        (((‖g‖[G,*] - 1) /
              (1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2)) -
            (((n : ℝ) - 1) / (1 - oneSidedRoundingAlphaStar G g))))
        (oneSidedRoundingAlphaStar G g) :=
    oneSidedRoundingPotential_hasDerivAt G g hαstar hlog
  have hexpr_zero :
      ((‖g‖[G,*] - 1) /
            (1 + oneSidedRoundingAlphaStar G g * ((‖g‖[G,*] - 1) / 2)) -
          (((n : ℝ) - 1) / (1 - oneSidedRoundingAlphaStar G g))) = 0 := by
    -- Match the explicit derivative with the previously normalized vanishing statement.
    rw [← hderivAtRaw.deriv, oneSidedRoundingPotential_derivEqZeroAtAlphaStar G g hn hr]
  have hderivAtStar :
      HasDerivAt (oneSidedRoundingPotential G g) 0 (oneSidedRoundingAlphaStar G g) := by
    simpa [hexpr_zero] using hderivAtRaw
  have hcont :
      ContinuousOn (oneSidedRoundingPotential G g) (Set.Ico (0 : ℝ) 1) := by
    intro α hα
    have hlogα := (oneSidedRoundingPotential_logArgumentsPos G g hn hr hα).2
    exact
      (oneSidedRoundingPotential_hasDerivAt G g hα hlogα).continuousAt.continuousWithinAt
  have hstrictConcave :
      StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (oneSidedRoundingPotential G g) := by
    -- Route correction: reuse the first-derivative monotonicity route from Proposition 7.8.
    have hanti :
        StrictAntiOn (deriv (oneSidedRoundingPotential G g))
          (interior (Set.Ico (0 : ℝ) 1)) := by
      simpa using oneSidedRoundingPotential_derivStrictAntiOn G g hn hr
    exact hanti.strictConcaveOn_of_deriv (convex_Ico (0 : ℝ) 1) hcont
  have hconcave : ConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (oneSidedRoundingPotential G g) :=
    hstrictConcave.concaveOn
  intro β hβ
  rcases lt_trichotomy β (oneSidedRoundingAlphaStar G g) with hlt | heq | hgt
  · -- On the left of `α*`, the secant slope into `α*` is nonnegative.
    have hslope :
        0 ≤
          slope (oneSidedRoundingPotential G g) β
            (oneSidedRoundingAlphaStar G g) := by
      simpa using hconcave.le_slope_of_hasDerivAt hβ hαstar hlt hderivAtStar
    have hden : 0 < oneSidedRoundingAlphaStar G g - β := sub_pos.mpr hlt
    have hnum :
        0 ≤
          oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) -
            oneSidedRoundingPotential G g β := by
      rw [slope_def_field] at hslope
      rcases (div_nonneg_iff.mp hslope) with hcase | hcase
      · exact hcase.1
      · linarith [hden, hcase.2]
    exact sub_nonneg.mp hnum
  · -- Equality is the middle case of the trichotomy.
    simp [heq]
  · -- On the right of `α*`, the secant slope out of `α*` is nonpositive.
    have hslope :
        slope (oneSidedRoundingPotential G g)
            (oneSidedRoundingAlphaStar G g) β ≤
          0 := by
      simpa using hconcave.slope_le_of_hasDerivAt hαstar hβ hgt hderivAtStar
    have hden : 0 < β - oneSidedRoundingAlphaStar G g := sub_pos.mpr hgt
    have hnum :
        oneSidedRoundingPotential G g β -
            oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) ≤
          0 := by
      rw [slope_def_field] at hslope
      rcases (div_nonpos_iff.mp hslope) with hcase | hcase
      · linarith [hden, hcase.2]
      · exact hcase.1
    exact sub_nonpos.mp hnum

/-- Lemma 7.5 (2): if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies `r ≥ n`, then the
explicit critical point `α*` is the maximizer of the source potential on `[0, 1)`. The true
one-dimensional boundary behavior of `α*` is recorded separately by
`oneSidedRoundingAlphaStar_eq_if_dualRadius_eq_one_of_dim_one`. -/
theorem oneSidedRoundingPotential_isMaxOn_alphaStar
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    IsMaxOn (oneSidedRoundingPotential G g) (Set.Ico (0 : ℝ) 1)
      (oneSidedRoundingAlphaStar G g) :=
  oneSidedRoundingPotential_isMaxOn_alphaStar_of_two_le G g hn hr

/-- Helper for Lemma 7.5 (3): if `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then
evaluating the one-sided rounding potential at `α*` gives the closed formula compatible with
`σ = (r - n) / (n + 1)`. -/
theorem oneSidedRoundingPotential_alphaStar_value_of_two_le
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
      2 * Real.log
          ((‖g‖[G,*] + 1) / ((n : ℝ) + 1)) +
        ((n : ℝ) - 1) *
          Real.log
            ((((n : ℝ) - 1) * (‖g‖[G,*] + 1)) /
              (((n : ℝ) + 1) * (‖g‖[G,*] - 1))) := by
  have hσarg :
      1 + oneSidedRoundingSigma G g =
        (‖g‖[G,*] + 1) / ((n : ℝ) + 1) := by
    -- Rewrite `1 + σ` into the scalar variable `r = ‖g‖[G,*]`.
    rw [oneSidedRoundingSigma_def]
    field_simp
    ring
  -- Rewrite the two logarithmic arguments at `α*` into their closed forms.
  rw [oneSidedRoundingPotential_alphaStar_sigmaExpansion G g hn hr, hσarg,
    oneSidedRoundingAlphaStar_one_sub G g hn hr]

/-- Lemma 7.5 (3): if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies `r ≥ n`, then
evaluating the source potential at `α*` gives the closed formula from `(7.u275)`. -/
theorem oneSidedRoundingPotential_alphaStar_value
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
      2 * Real.log
          ((‖g‖[G,*] + 1) / ((n : ℝ) + 1)) +
        ((n : ℝ) - 1) *
          Real.log
            ((((n : ℝ) - 1) * (‖g‖[G,*] + 1)) /
              (((n : ℝ) + 1) * (‖g‖[G,*] - 1))) :=
  oneSidedRoundingPotential_alphaStar_value_of_two_le G g hn hr

-- Proof sketch: rewrite the potential at `α*` in terms of
-- `σ = (r - n) / (n + 1)` and apply the scalar lower bound
-- `log (1 + σ) - σ / (1 + σ) ≤ ...`.
/-- Helper for Lemma 7.5 (4): if `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the
optimal value of the one-sided rounding potential is bounded below by
`2 (log (1 + σ) - σ / (1 + σ))`, where `σ = (r - n) / (n + 1)`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_log_of_two_le
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 *
        (Real.log (1 + oneSidedRoundingSigma G g) -
          oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := by
  have hαmem :
      oneSidedRoundingAlphaStar G g ∈ Set.Ico (0 : ℝ) 1 :=
    oneSidedRoundingAlphaStar_memIcoAux G g hn hr
  have hn1_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by
      exact_mod_cast hn
    linarith
  have hbound_raw :
      -(((n : ℝ) - 1) * Real.log (1 - oneSidedRoundingAlphaStar G g)) ≤
        ((n : ℝ) - 1) *
          (oneSidedRoundingAlphaStar G g /
            (1 - oneSidedRoundingAlphaStar G g)) := by
    have hbase := negLogOneSub_le_div_of_mem_Ico hαmem
    have hmul := mul_le_mul_of_nonneg_left hbase hn1_nonneg
    simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmul
  have hbound :
      -(2 * oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) ≤
        ((n : ℝ) - 1) * Real.log (1 - oneSidedRoundingAlphaStar G g) := by
    rw [oneSidedRoundingAlphaStar_ratio G g hn hr] at hbound_raw
    linarith
  have hvalue :
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) =
        2 * Real.log (1 + oneSidedRoundingSigma G g) +
          ((n : ℝ) - 1) * Real.log (1 - oneSidedRoundingAlphaStar G g) :=
    oneSidedRoundingPotential_alphaStar_sigmaExpansion G g hn hr
  -- Insert the logarithmic lower bound into the explicit value formula at `α*`.
  calc
    2 *
        (Real.log (1 + oneSidedRoundingSigma G g) -
          oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) =
        2 * Real.log (1 + oneSidedRoundingSigma G g) +
          (-(2 * oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g))) := by
            ring
    _ ≤ 2 * Real.log (1 + oneSidedRoundingSigma G g) +
          (((n : ℝ) - 1) * Real.log (1 - oneSidedRoundingAlphaStar G g)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hbound (2 * Real.log (1 + oneSidedRoundingSigma G g))
    _ = oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := by
          rw [← hvalue]

/-- Lemma 7.5 (4): if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies `r ≥ n`, then the
source logarithmic lower bound holds at `α*`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_log
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 *
        (Real.log (1 + oneSidedRoundingSigma G g) -
          oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) :=
  oneSidedRoundingPotential_alphaStar_lower_bound_log_of_two_le G g hn hr

-- Proof sketch: combine `oneSidedRoundingPotential_alphaStar_lower_bound_log_of_two_le` with the
-- scalar
-- estimate
-- `log (1 + σ) - σ / (1 + σ) ≥ σ^2 / ((1 + σ) (2 + σ))`.
/-- Helper for Lemma 7.5 (5): if `2 ≤ n` and `r = ‖g‖*_G` satisfies `r ≥ n`, then the
optimal value of the one-sided rounding potential is bounded below by
`2 σ² / ((1 + σ) (2 + σ))`, where `σ = (r - n) / (n + 1)`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_rational_of_two_le
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 * (oneSidedRoundingSigma G g ^ (2 : ℕ)) /
        ((1 + oneSidedRoundingSigma G g) * (2 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) := by
  have hσ_nonneg : 0 ≤ oneSidedRoundingSigma G g := by
    -- The radius hypothesis `r ≥ n` makes the numerator of `σ = (r - n) / (n + 1)` nonnegative.
    rw [oneSidedRoundingSigma_def]
    exact div_nonneg (sub_nonneg.mpr hr) (by positivity)
  have hgap :
      oneSidedRoundingSigma G g ^ (2 : ℕ) /
          ((1 + oneSidedRoundingSigma G g) * (2 + oneSidedRoundingSigma G g)) ≤
        Real.log (1 + oneSidedRoundingSigma G g) -
          oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g) :=
    sigmaLogGap_ge_rational hσ_nonneg
  have hgap₂ :
      2 * (oneSidedRoundingSigma G g ^ (2 : ℕ)) /
          ((1 + oneSidedRoundingSigma G g) * (2 + oneSidedRoundingSigma G g)) ≤
        2 *
          (Real.log (1 + oneSidedRoundingSigma G g) -
            oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) := by
    have htwo : 0 ≤ (2 : ℝ) := by
      norm_num
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hgap htwo)
  have hlog :
      2 *
          (Real.log (1 + oneSidedRoundingSigma G g) -
            oneSidedRoundingSigma G g / (1 + oneSidedRoundingSigma G g)) ≤
        oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) :=
    oneSidedRoundingPotential_alphaStar_lower_bound_log_of_two_le G g hn hr
  -- Chain the scalar gap estimate with the logarithmic lower bound at `α*`.
  exact le_trans hgap₂ hlog

/-- Lemma 7.5 (5): if `2 ≤ n` and the dual radius `r = ‖g‖*_G` satisfies `r ≥ n`, then the
rational source lower bound holds at `α*`. -/
theorem oneSidedRoundingPotential_alphaStar_lower_bound_rational
    (G : {A : Mat // A.PosDef}) (g : E)
    (hn : 2 ≤ n)
    (hr : (n : ℝ) ≤ ‖g‖[G,*]) :
    2 * (oneSidedRoundingSigma G g ^ (2 : ℕ)) /
        ((1 + oneSidedRoundingSigma G g) * (2 + oneSidedRoundingSigma G g)) ≤
      oneSidedRoundingPotential G g (oneSidedRoundingAlphaStar G g) :=
  oneSidedRoundingPotential_alphaStar_lower_bound_rational_of_two_le G g hn hr

-- Semantic recall: `lean_leansearch` confirmed `IsMaxOn` / `isMaxOn_iff` as the canonical
-- interval-maximizer API, so the source lemma is exposed through public interior theorem surfaces
-- with explicit `2 ≤ n`, while the exact one-dimensional degeneration remains available through
-- the separate boundary companion for `α*`.

end
