/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.LocallyConvex.Separation
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.subgradient

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: the Chapter 8 owner for the affine subgradient inequality on a comparison
-- set is `IsSubgradientAtOn` from `Integer.Chapters.Chap08.subgradient`. Exercise 8.9 uses that
-- canonical owner directly at the whole-space comparison set `Set.univ`.

section Exercise89

variable {n : ℕ}

/-- A vector `s` is a subgradient of `g` at `x` when the affine lower bound defined by `s`
holds on all of `ℝ^n`. This is the whole-space specialization of `IsSubgradientAtOn`. -/
abbrev IsSubgradientAt
    (g : (Fin n → ℝ) → ℝ)
    (x s : Fin n → ℝ) : Prop :=
  IsSubgradientAtOn g Set.univ x s

namespace IsSubgradientAt

/-- A whole-space subgradient yields the affine lower bound at every comparison point. -/
theorem ineq
    {g : (Fin n → ℝ) → ℝ}
    {x s : Fin n → ℝ}
    (hs : IsSubgradientAt g x s)
    (y : Fin n → ℝ) :
    g y ≥ g x + ∑ i, s i * (y i - x i) := by
  have hy : y ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  simpa [IsSubgradientAt, IsSubgradientAtOn] using hs y hy

end IsSubgradientAt

/-- To prove `IsSubgradientAt g x s`, it suffices to establish the affine lower bound at every
comparison point `y`. -/
theorem isSubgradientAt_of_ineq
    {g : (Fin n → ℝ) → ℝ}
    {x s : Fin n → ℝ}
    (hs : ∀ y : Fin n → ℝ, g y ≥ g x + ∑ i, s i * (y i - x i)) :
    IsSubgradientAt g x s := by
  intro y hy
  simpa using hs y

/-- Helper for Exercise 8.9: `Pi.single i t` is the scalar multiple of the `i`-th coordinate
singleton of weight `1`. -/
lemma piSingle_eq_smul_singleOne
    (i : Fin n)
    (t : ℝ) :
    Pi.single i t = t • Pi.single i (1 : ℝ) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [Pi.single_eq_of_ne hji]

/-- Helper for Exercise 8.9: a continuous linear functional on `Fin n → ℝ` is determined by its
values on the coordinate singletons `Pi.single i 1`. -/
lemma continuousLinearMap_apply_eq_sumSingle
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    (y : Fin n → ℝ) :
    ℓ y = ∑ i, ℓ (Pi.single i 1) * y i := by
  -- Expand `y` in the standard basis and apply linearity coordinatewise.
  calc
    ℓ y = ℓ (∑ i, Pi.single i (y i)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ i, ℓ (Pi.single i (y i)) := by
      rw [map_sum]
    _ = ∑ i, ℓ (Pi.single i 1) * y i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [piSingle_eq_smul_singleOne]
      rw [map_smul]
      simp [smul_eq_mul, mul_comm]

/-- Helper for Exercise 8.9: a supporting affine functional with negative scalar coefficient on the
epigraph produces a whole-space subgradient. -/
lemma subgradientOfSupportingFunctional
    {g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    {a : ℝ}
    (ha : a < 0)
    (hsupport : ∀ y : Fin n → ℝ, ℓ y + a * g y ≤ ℓ x + a * g x) :
    ∃ s : Fin n → ℝ, IsSubgradientAt g x s := by
  let b : ℝ := (-a)⁻¹
  let s : Fin n → ℝ := fun i ↦ b * ℓ (Pi.single i 1)
  have hb : 0 < b := by
    have hneg : 0 < -a := by
      linarith
    dsimp [b]
    exact inv_pos.2 hneg
  have hsum (z : Fin n → ℝ) : ∑ i, s i * z i = b * ℓ z := by
    -- Factor the common scalar `b` out of the coordinate expansion of `ℓ`.
    calc
      ∑ i, s i * z i = ∑ i, b * (ℓ (Pi.single i 1) * z i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        dsimp [s]
        rw [mul_assoc]
      _ = b * ∑ i, ℓ (Pi.single i 1) * z i := by
        rw [Finset.mul_sum]
      _ = b * ℓ z := by
        rw [continuousLinearMap_apply_eq_sumSingle]
  refine ⟨s, isSubgradientAt_of_ineq ?_⟩
  intro y
  -- Rearrange the supporting-functional inequality into the standard subgradient bound.
  have hscaled : ℓ y - ℓ x ≤ (-a) * (g y - g x) := by
    linarith [hsupport y]
  have hdiv : b * (ℓ y - ℓ x) ≤ g y - g x := by
    have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hb)
    have hnegane : (-a) ≠ 0 := by
      linarith
    have hcancel : b * (-a) = 1 := by
      dsimp [b]
      exact inv_mul_cancel₀ hnegane
    calc
      b * (ℓ y - ℓ x) ≤ b * ((-a) * (g y - g x)) := hmul
      _ = (b * (-a)) * (g y - g x) := by
        rw [mul_assoc]
      _ = g y - g x := by
        rw [hcancel, one_mul]
  have hsumSub : ∑ i, s i * (y i - x i) = b * (ℓ y - ℓ x) := by
    calc
      ∑ i, s i * (y i - x i) = b * ℓ (y - x) := by
        simpa using hsum (y - x)
      _ = b * (ℓ y - ℓ x) := by
        rw [ℓ.map_sub]
  have : g x + b * (ℓ y - ℓ x) ≤ g y := by
    linarith
  simpa [hsumSub] using this

/-- Helper for Exercise 8.9: a continuous linear functional on `((Fin n → ℝ) × ℝ)` splits into its
horizontal linear part and its scalar coefficient on the final coordinate. -/
lemma productFunctional_apply_eq_linearPart_add_scalarPart
    (f : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (y : Fin n → ℝ)
    (t : ℝ) :
    f (y, t) =
      (f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) y + f (0, 1) * t := by
  have hsmul : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by
    -- Normalize the vertical direction to a scalar multiple of the unit basis vector.
    apply Prod.ext
    · ext i
      simp
    · simp
  -- Split the product-space functional into its horizontal and vertical pieces.
  calc
    f (y, t) = f ((y, 0) + (0, t)) := by
      simp
    _ = f (y, 0) + f (0, t) := by
      rw [map_add]
    _ = (f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) y + f (0, t) := by
      simp
    _ = (f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)) y + f (0, 1) * t := by
      rw [hsmul, map_smul]
      simp [mul_comm]

/-- Helper for Exercise 8.9: a continuous linear functional that is maximized at `x` along both
`x + y` and `x - y` must vanish identically. -/
lemma continuousLinearMap_eq_zero_of_add_le_base_and_sub_le_base
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ)
    (hplus : ∀ y : Fin n → ℝ, ℓ (x + y) ≤ ℓ x)
    (hminus : ∀ y : Fin n → ℝ, ℓ (x - y) ≤ ℓ x) :
    ℓ = 0 := by
  ext y
  -- Compare the support inequalities at `x + y` and `x - y` to force `ℓ y = 0`.
  have hplusLinear := hplus y
  have hminusLinear := hminus y
  have hy_nonpos : ℓ y ≤ 0 := by
    rw [ℓ.map_add] at hplusLinear
    linarith
  have hy_nonneg : 0 ≤ ℓ y := by
    rw [ℓ.map_sub] at hminusLinear
    linarith
  linarith

/-- Helper for Exercise 8.9: a nonzero supporting functional for the graph of `g` must have a
nonzero scalar coefficient on the final coordinate. -/
lemma supportingFunctional_scalarCoeff_ne_zero
    {g : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ}
    (f : ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ)
    (hfne : f ≠ 0)
    (hgraph : ∀ y : Fin n → ℝ, f (y, g y) ≤ f (x, g x)) :
    f (0, 1) ≠ 0 := by
  let ℓ : (Fin n → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  intro ha0
  have hplus : ∀ y : Fin n → ℝ, ℓ (x + y) ≤ ℓ x := by
    intro y
    -- Rewrite graph support through the normalized product-functional coordinates.
    have hy := hgraph (x + y)
    simpa [ℓ, ha0, productFunctional_apply_eq_linearPart_add_scalarPart] using hy
  have hminus : ∀ y : Fin n → ℝ, ℓ (x - y) ≤ ℓ x := by
    intro y
    -- The same normalization handles the `x - y` graph point.
    have hy := hgraph (x - y)
    simpa [ℓ, ha0, productFunctional_apply_eq_linearPart_add_scalarPart] using hy
  have hℓzero : ℓ = 0 :=
    continuousLinearMap_eq_zero_of_add_le_base_and_sub_le_base ℓ x hplus hminus
  have hℓzero_apply (y : Fin n → ℝ) : ℓ y = 0 := by
    simpa using congrArg (fun m : (Fin n → ℝ) →L[ℝ] ℝ => m y) hℓzero
  have hfzero : f = 0 := by
    ext p
    rcases p with ⟨y, t⟩
    -- Once the horizontal part and scalar coefficient vanish, the separator is zero.
    rw [productFunctional_apply_eq_linearPart_add_scalarPart]
    simp [ℓ, ha0, hℓzero_apply y]
  exact hfne hfzero

/-- Helper for Exercise 8.9: every interior point of an epigraph already lies in the strict
epigraph. -/
lemma interior_epigraph_subset_strictEpigraph
    {g : (Fin n → ℝ) → ℝ}
    {p : (Fin n → ℝ) × ℝ}
    (hp : p ∈ Set.interior ({q : ((Fin n → ℝ) × ℝ) | g q.1 ≤ q.2} : Set ((Fin n → ℝ) × ℝ))) :
    p ∈ ({q : ((Fin n → ℝ) × ℝ) | g q.1 < q.2} : Set ((Fin n → ℝ) × ℝ)) := by
  rcases Metric.mem_nhds_iff.mp (IsOpen.mem_nhds isOpen_interior hp) with ⟨ε, hε, hball⟩
  have hmemInterior :
      (p.1, p.2 - ε / 2) ∈
        Set.interior ({q : ((Fin n → ℝ) × ℝ) | g q.1 ≤ q.2} : Set ((Fin n → ℝ) × ℝ)) := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖((0 : Fin n → ℝ), -(ε / 2))‖ < ε
    rw [Prod.norm_def, max_lt_iff]
    constructor
    · simpa using hε
    · simpa [Real.norm_eq_abs, abs_neg] using half_lt_self hε
  have hmem :
      (p.1, p.2 - ε / 2) ∈ ({q : ((Fin n → ℝ) × ℝ) | g q.1 ≤ q.2} : Set ((Fin n → ℝ) × ℝ)) :=
    Set.interior_subset hmemInterior
  rcases p with ⟨x, t⟩
  dsimp at hmem ⊢
  linarith

/-- Exercise 8.9. Every convex function `g : ℝ^n → ℝ` admits a subgradient at each point
`λ_star : ℝ^n`. -/
theorem convex_function_has_subgradient_at
    (g : (Fin n → ℝ) → ℝ)
    (lambdaStar : Fin n → ℝ)
    (hconvex : ConvexOn ℝ Set.univ g) :
    ∃ s : Fin n → ℝ, IsSubgradientAt g lambdaStar s := by
  -- Route correction: separate the boundary point from the closed epigraph directly and only
  -- normalize the separator once through named helper lemmas.
  let A : Set ((Fin n → ℝ) × ℝ) := {p | g p.1 ≤ p.2}
  have hcontOn : ContinuousOn g Set.univ := hconvex.continuousOn isOpen_univ
  have hcont : Continuous g := by
    simpa [continuousOn_univ] using hcontOn
  have hAconvex : Convex ℝ A := by
    simpa [A] using hconvex.convex_epigraph
  have hStrictOpen : IsOpen ({p : ((Fin n → ℝ) × ℝ) | g p.1 < p.2} : Set ((Fin n → ℝ) × ℝ)) := by
    -- The strict epigraph is open because `p ↦ g p.1` and `p ↦ p.2` are continuous.
    have hfst : Continuous fun p : ((Fin n → ℝ) × ℝ) ↦ g p.1 := by
      exact hcont.comp continuous_fst
    exact isOpen_lt hfst continuous_snd
  have hAint : (Set.interior A).Nonempty := by
    have hStrictSubset : ({p : ((Fin n → ℝ) × ℝ) | g p.1 < p.2} : Set ((Fin n → ℝ) × ℝ)) ⊆ A := by
      intro p hp
      exact le_of_lt hp
    have hmemStrict : (lambdaStar, g lambdaStar + 1) ∈ ({p : ((Fin n → ℝ) × ℝ) | g p.1 < p.2} : Set ((Fin n → ℝ) × ℝ)) := by
      simp
    refine ⟨(lambdaStar, g lambdaStar + 1), ?_⟩
    exact interior_maximal hStrictSubset hStrictOpen hmemStrict
  have hxA : (lambdaStar, g lambdaStar) ∉ Set.interior A := by
    intro hx
    have hxStrict := interior_epigraph_subset_strictEpigraph (g := g) hx
    simpa using hxStrict
  obtain ⟨f, hfne, hsupport⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hAconvex hxA hAint
  let ℓ : (Fin n → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) ℝ)
  let a : ℝ := f (0, 1)
  have ha_nonpos : a ≤ 0 := by
    -- Evaluate support at a strictly higher point above `lambdaStar`.
    have hpoint : (lambdaStar, g lambdaStar + 1) ∈ A := by
      simp [A]
    have h := hsupport (lambdaStar, g lambdaStar + 1) hpoint
    have hnormalized :
        ℓ lambdaStar + a * (g lambdaStar + 1) ≤ ℓ lambdaStar + a * g lambdaStar := by
      simpa [ℓ, a, productFunctional_apply_eq_linearPart_add_scalarPart] using h
    have h := hnormalized
    linarith
  have hsupportGraphRaw (y : Fin n → ℝ) :
      f (y, g y) ≤ f (lambdaStar, g lambdaStar) := by
    -- Restrict the separator from the epigraph to actual graph points.
    have hpoint : (y, g y) ∈ A := by
      simp [A]
    exact hsupport (y, g y) hpoint
  have ha_ne : a ≠ 0 := by
    -- The graph support contradiction is now packaged in one dedicated helper.
    simpa [a] using
      supportingFunctional_scalarCoeff_ne_zero (g := g) (x := lambdaStar) f hfne hsupportGraphRaw
  have ha : a < 0 := lt_of_le_of_ne ha_nonpos ha_ne
  have hsupportGraph (y : Fin n → ℝ) :
      ℓ y + a * g y ≤ ℓ lambdaStar + a * g lambdaStar := by
    -- Normalize the graph support inequality into the affine form needed by the subgradient lemma.
    simpa [ℓ, a, productFunctional_apply_eq_linearPart_add_scalarPart] using hsupportGraphRaw y
  exact subgradientOfSupportingFunctional ℓ ha hsupportGraph

end Exercise89
