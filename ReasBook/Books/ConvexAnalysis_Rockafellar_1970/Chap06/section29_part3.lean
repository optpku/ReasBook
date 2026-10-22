/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part2

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Definition 6.29.18: The perturbation function for the generalized convex program `(P)`
associated with a convex bifunction `F` is the extended-real-valued function `inf F` on
`ℝ^m`, defined by sending each perturbation `u` to the infimum of the section `F u`. -/
noncomputable def generalizedConvexProgramPerturbationFunction {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin m → ℝ) → EReal :=
  fun u => sInf (Set.range ((generalizedConvexProgramPerturbation F u).objective))

/-- Definition 6.29.19: A vector `uStar ∈ ℝ^m` is a Kuhn--Tucker vector for the
generalized convex program `(P)` associated with a convex bifunction `F` if the optimal
value `inf F 0` is finite and, equivalently, for every perturbation `u ∈ ℝ^m`, one has
`inf F u + ⟪uStar, u⟫ ≥ inf F 0`. -/
def IsKuhnTuckerVector {m n : ℕ} (F : ConvexBifunction m n) (uStar : Fin m → ℝ) : Prop :=
  generalizedConvexProgramOptimalValue F ≠ ⊤ ∧
    generalizedConvexProgramOptimalValue F ≠ (⊥ : EReal) ∧
      ∀ u : Fin m → ℝ,
        generalizedConvexProgramPerturbationFunction F u +
            (((dotProduct uStar u : ℝ)) : EReal) ≥
          generalizedConvexProgramOptimalValue F

-- Proof sketch: identify `inf F` with the pointwise infimum of the convex sections of the
-- graph function of `F`, so convexity descends from convexity of the bifunction and its
-- effective domain is exactly the set of perturbations with a finite section value. For the
-- Kuhn--Tucker characterization, rewrite the defining inequality for `uStar` as the Euclidean
-- subgradient inequality for the perturbation function at `0`, with sign convention `-uStar`.
/-- Helper for Theorem 6.29.1: the generalized-program optimal value is the perturbation value at
the origin. -/
lemma helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero {m n : ℕ}
    (F : ConvexBifunction m n) :
    generalizedConvexProgramOptimalValue F =
      generalizedConvexProgramPerturbationFunction F 0 := by
  -- Unfold both infimum definitions; at `u = 0` they are the same slice of `F`.
  simp [generalizedConvexProgramOptimalValue, generalizedConvexProgramPerturbationFunction,
    generalizedConvexProgramObjective, generalizedConvexProgramPerturbation,
    generalizedConvexProgram]

/-- Helper for Theorem 6.29.1: the graph function of a convex bifunction is a convex
extended-real-valued function on the product space. -/
lemma helperForTheorem_6_29_1_graphFunction_convex {m n : ℕ}
    (F : ConvexBifunction m n) :
    ConvexERealFunction (graphFunction F.1) := by
  -- This is exactly the bundled convexity inequality for the graph function.
  intro p q a b ha hb hab
  simpa [graphFunction] using F.2 p q a b ha hb hab

/-- Helper for Theorem 6.29.1: the perturbation value at `u` is the infimum of the graph
function over the first-coordinate fiber above `u`. -/
lemma helperForTheorem_6_29_1_perturbation_eq_fiberInf_graphFunction {m n : ℕ}
    (F : ConvexBifunction m n) (u : Fin m → ℝ) :
    generalizedConvexProgramPerturbationFunction F u =
      sInf {z : EReal | ∃ p : (Fin m → ℝ) × (Fin n → ℝ),
        LinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ) p = u ∧ z = graphFunction F.1 p} := by
  -- Rewrite the slice range as the first-coordinate fiber of the graph function.
  rw [generalizedConvexProgramPerturbationFunction]
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(u, x), ?_, rfl⟩
    simp
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨u', x⟩
    simp at hp
    rcases hp with rfl
    exact ⟨x, by simp [generalizedConvexProgramPerturbation, generalizedConvexProgram,
      graphFunction]⟩

/-- Helper for Theorem 6.29.1: the perturbation value is finite exactly when some point in the
corresponding section of `F` has finite value. -/
lemma helperForTheorem_6_29_1_mem_erealDom_iff_exists_finite_slice {m n : ℕ}
    (F : ConvexBifunction m n) (u : Fin m → ℝ) :
    generalizedConvexProgramPerturbationFunction F u < ⊤ ↔
      ∃ x : Fin n → ℝ, F.1 u x < ⊤ := by
  -- Unfold the perturbation infimum and move between the infimum and a displayed slice value.
  rw [generalizedConvexProgramPerturbationFunction]
  constructor
  · intro hu
    rcases (sInf_lt_iff.mp hu) with ⟨z, hzmem, hzlt⟩
    rcases hzmem with ⟨x, rfl⟩
    exact ⟨x, by simpa [generalizedConvexProgramPerturbation, generalizedConvexProgram] using hzlt⟩
  · rintro ⟨x, hx⟩
    have hsInf_le :
        sInf (Set.range ((generalizedConvexProgramPerturbation F u).objective)) ≤
          (generalizedConvexProgramPerturbation F u).objective x := by
      exact sInf_le ⟨x, rfl⟩
    exact lt_of_le_of_lt hsInf_le
      (by simpa [generalizedConvexProgramPerturbation, generalizedConvexProgram] using hx)

/-- Helper for Theorem 6.29.1: Euclidean subgradient membership at the origin is equivalent to
the supporting inequality with sign convention `-uStar`. -/
lemma helperForTheorem_6_29_1_neg_mem_euclideanSubdifferentialAt_zero_iff_supporting_inequality
    {m : ℕ} (h : (Fin m → ℝ) → EReal) (uStar : Fin m → ℝ) :
    (-uStar) ∈ euclideanSubdifferentialAt h 0 ↔
      ∀ u : Fin m → ℝ, h u + (((dotProduct uStar u : ℝ)) : EReal) ≥ h 0 := by
  constructor
  · intro hu u
    -- Unfold the Euclidean subgradient condition into the scalar inequality at `u`.
    have hineq' : IsSubgradientAt h 0 (dotProductEquiv ℝ (Fin m) (-uStar)) := by
      simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hu
    have hineq := hineq' u
    let a : EReal := (((dotProduct uStar u : ℝ)) : EReal)
    have hsub : h 0 - a ≤ h u := by
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        dotProductEquiv_apply_apply, dotProduct_neg] using hineq
    have h1 : a ≠ (⊥ : EReal) ∨ h u ≠ ⊤ := Or.inl (by simp [a])
    have h2 : a ≠ (⊤ : EReal) ∨ h u ≠ (⊥ : EReal) := Or.inl (by simp [a])
    have hadd : h 0 ≤ h u + a := (EReal.sub_le_iff_le_add h1 h2).1 hsub
    simpa [a, add_assoc, add_left_comm, add_comm] using hadd
  · intro hu
    -- Convert the supporting inequality back into the subgradient inequality at `0`.
    have hineq' : IsSubgradientAt h 0 (dotProductEquiv ℝ (Fin m) (-uStar)) := by
      intro u
      let a : EReal := (((dotProduct uStar u : ℝ)) : EReal)
      have h1 : a ≠ (⊥ : EReal) ∨ h u ≠ ⊤ := Or.inl (by simp [a])
      have h2 : a ≠ (⊤ : EReal) ∨ h u ≠ (⊥ : EReal) := Or.inl (by simp [a])
      have hsub : h 0 - a ≤ h u :=
        (EReal.sub_le_iff_le_add h1 h2).2
          (by simpa [a, add_assoc, add_left_comm, add_comm] using hu u)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        dotProductEquiv_apply_apply, dotProduct_neg] using hsub
    simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hineq'

/-- Theorem 6.29.1: For a convex bifunction `F`, the perturbation function `inf F` of the
associated generalized convex program is convex on `ℝ^m`, and its effective domain is
exactly `dom F`. When the optimal value of `(P)` is finite, the Kuhn--Tucker vectors are
precisely the vectors `uStar ∈ ℝ^m` such that `-uStar ∈ ∂(inf F)(0)`. -/
theorem generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker
    {m n : ℕ} (F : ConvexBifunction m n) :
    ConvexFunction (generalizedConvexProgramPerturbationFunction F) ∧
      erealDom (generalizedConvexProgramPerturbationFunction F) = bifunctionEffectiveDomain F.1 ∧
      (IsFiniteEReal (generalizedConvexProgramOptimalValue F) →
        ∀ uStar : Fin m → ℝ,
          IsKuhnTuckerVector F uStar ↔
            -uStar ∈ euclideanSubdifferentialAt
              (generalizedConvexProgramPerturbationFunction F) 0) := by
  constructor
  · -- Approximate the slice infima by actual section values and then apply graph convexity.
    have hgraphConv : ConvexERealFunction (graphFunction F.1) :=
      helperForTheorem_6_29_1_graphFunction_convex F
    have hconvOn :
        ConvexFunctionOn (S := (Set.univ : Set (Fin m → ℝ)))
          (generalizedConvexProgramPerturbationFunction F) := by
      refine
        (convexFunctionOn_univ_iff_strict_inequality
          (f := generalizedConvexProgramPerturbationFunction F)).2 ?_
      intro u1 u2 α β t hu1 hu2 ht0 ht1
      rw [generalizedConvexProgramPerturbationFunction] at hu1 hu2
      rcases (sInf_lt_iff.mp hu1) with ⟨z1, hz1mem, hz1lt⟩
      rcases (sInf_lt_iff.mp hu2) with ⟨z2, hz2mem, hz2lt⟩
      rcases hz1mem with ⟨x1, rfl⟩
      rcases hz2mem with ⟨x2, rfl⟩
      rcases ereal_exists_real_between_of_lt hz1lt with ⟨μ, hμ, hμ_lt⟩
      rcases ereal_exists_real_between_of_lt hz2lt with ⟨v, hv, hv_lt⟩
      have hsInf_le :
          generalizedConvexProgramPerturbationFunction F ((1 - t) • u1 + t • u2) ≤
            F.1 ((1 - t) • u1 + t • u2) ((1 - t) • x1 + t • x2) := by
        exact sInf_le ⟨(1 - t) • x1 + t • x2, by
          simp [generalizedConvexProgramPerturbation, generalizedConvexProgram]⟩
      have hgraph :
          F.1 ((1 - t) • u1 + t • u2) ((1 - t) • x1 + t • x2) ≤
            ((1 - t : ℝ) : EReal) * F.1 u1 x1 + ((t : ℝ) : EReal) * F.1 u2 x2 := by
        simpa [ConvexERealFunction, graphFunction, smul_eq_mul, add_assoc, add_left_comm,
          add_comm] using
          hgraphConv (x := (u1, x1)) (y := (u2, x2))
            (a := 1 - t) (b := t) (sub_nonneg.mpr (le_of_lt ht1)) (le_of_lt ht0) (by ring)
      have hmul1 :
          ((1 - t : ℝ) : EReal) * F.1 u1 x1 ≤ (((1 - t) * μ : ℝ) : EReal) := by
        have hmul1' :
            ((1 - t : ℝ) : EReal) * F.1 u1 x1 ≤
              ((1 - t : ℝ) : EReal) * (μ : EReal) :=
          mul_le_mul_of_nonneg_left hμ
            (by exact_mod_cast sub_nonneg.mpr (le_of_lt ht1))
        simpa [EReal.coe_mul] using hmul1'
      have hmul2 :
          ((t : ℝ) : EReal) * F.1 u2 x2 ≤ ((t * v : ℝ) : EReal) := by
        have hmul2' :
            ((t : ℝ) : EReal) * F.1 u2 x2 ≤ ((t : ℝ) : EReal) * (v : EReal) :=
          mul_le_mul_of_nonneg_left hv (by exact_mod_cast le_of_lt ht0)
        simpa [EReal.coe_mul] using hmul2'
      have hlt_combo :
          (((1 - t) * μ + t * v : ℝ) : EReal) <
            ((1 - t : ℝ) : EReal) * (α : EReal) + ((t : ℝ) : EReal) * (β : EReal) := by
        simpa [EReal.coe_add, EReal.coe_mul] using
          ereal_convex_combo_lt_of_lt (μ := μ) (α := α) (v := v) (β := β) hμ_lt hv_lt ht0 ht1
      calc
        generalizedConvexProgramPerturbationFunction F ((1 - t) • u1 + t • u2)
            ≤ F.1 ((1 - t) • u1 + t • u2) ((1 - t) • x1 + t • x2) := hsInf_le
        _ ≤ ((1 - t : ℝ) : EReal) * F.1 u1 x1 + ((t : ℝ) : EReal) * F.1 u2 x2 := hgraph
        _ ≤ (((1 - t) * μ : ℝ) : EReal) + ((t * v : ℝ) : EReal) := add_le_add hmul1 hmul2
        _ = (((1 - t) * μ + t * v : ℝ) : EReal) := by rw [EReal.coe_add]
        _ < ((1 - t : ℝ) : EReal) * (α : EReal) + ((t : ℝ) : EReal) * (β : EReal) := hlt_combo
    simpa [ConvexFunction] using hconvOn
  constructor
  · -- The effective domain is exactly the set of perturbations with a finite section value.
    ext u
    constructor
    · intro hu
      rcases (helperForTheorem_6_29_1_mem_erealDom_iff_exists_finite_slice F u).1 hu with
        ⟨x, hx⟩
      exact
        (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
          (F := F.1) (u := u)).2 ⟨x, hx⟩
    · intro hu
      rcases
          (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
            (F := F.1) (u := u)).1 hu with
        ⟨x, hx⟩
      exact (helperForTheorem_6_29_1_mem_erealDom_iff_exists_finite_slice F u).2 ⟨x, hx⟩
  · intro hfinite uStar
    -- Rewrite the Kuhn--Tucker inequality using the perturbation value at the origin.
    have hsupport :
        -uStar ∈ euclideanSubdifferentialAt
            (generalizedConvexProgramPerturbationFunction F) 0 ↔
          ∀ u : Fin m → ℝ,
            generalizedConvexProgramPerturbationFunction F u +
                (((dotProduct uStar u : ℝ)) : EReal) ≥
              generalizedConvexProgramPerturbationFunction F 0 :=
      helperForTheorem_6_29_1_neg_mem_euclideanSubdifferentialAt_zero_iff_supporting_inequality
        (h := generalizedConvexProgramPerturbationFunction F) uStar
    constructor
    · intro huKT
      refine hsupport.2 ?_
      intro u
      simpa [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F] using huKT.2.2 u
    · intro hsub
      refine ⟨hfinite.1, hfinite.2, ?_⟩
      intro u
      simpa [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F] using
        (hsupport.1 hsub) u

/-- The one-sided directional derivative of the perturbation function `inf F` at the origin. -/
noncomputable def generalizedConvexProgramOriginDirectionalDerivative {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin m → ℝ) → EReal :=
  upperDirectionalDerivativeAt (generalizedConvexProgramPerturbationFunction F) 0

/-- Helper for Corollary 6.29.1: finiteness of the optimal value is exactly finiteness of the
perturbation function at the origin. -/
lemma helperForCorollary_6_29_1_perturbationAt_zero_finite {m n : ℕ}
    (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    (generalizedConvexProgramPerturbationFunction F) 0 ≠ (⊤ : EReal) ∧
      (generalizedConvexProgramPerturbationFunction F) 0 ≠ (⊥ : EReal) := by
  -- Rewrite the base-point perturbation value as the optimal value and read off finiteness.
  simpa [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F] using hfinite

/-- Helper for Corollary 6.29.1: the negated origin directional derivative remains positively
homogeneous and convex. -/
lemma helperForCorollary_6_29_1_negatedOriginDirectionalDerivative_posHom_convex {m n : ℕ}
    (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    PositivelyHomogeneous
        (fun u : Fin m → ℝ => generalizedConvexProgramOriginDirectionalDerivative F (-u)) ∧
      ConvexFunction
        (fun u : Fin m → ℝ => generalizedConvexProgramOriginDirectionalDerivative F (-u)) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let D : (Fin m → ℝ) → EReal := generalizedConvexProgramOriginDirectionalDerivative F
  have hpConv :
      ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  rcases convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite with
    ⟨_hdir, hposD, hconvD, _hzeroD, _hsymmD⟩
  constructor
  · -- Negating the direction commutes with positive rescaling.
    intro u t ht
    simpa [D, generalizedConvexProgramOriginDirectionalDerivative, neg_smul] using
      hposD (-u) t ht
  · -- Transport epigraph convexity through the linear map `u ↦ -u`.
    rw [ConvexFunction, ConvexFunctionOn] at hconvD ⊢
    intro x hx y hy a b ha hb hab
    have hx' : ((-x.1), x.2) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) D := by
      simpa [epigraph, D, generalizedConvexProgramOriginDirectionalDerivative] using hx
    have hy' : ((-y.1), y.2) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) D := by
      simpa [epigraph, D, generalizedConvexProgramOriginDirectionalDerivative] using hy
    have hxy' := hconvD hx' hy' ha hb hab
    refine ⟨by
      show a • x.1 + b • y.1 ∈ (Set.univ : Set (Fin m → ℝ))
      simp, ?_⟩
    simpa [epigraph, smul_neg, D, generalizedConvexProgramOriginDirectionalDerivative,
      add_comm, add_left_comm, add_assoc] using hxy'.2

/-- Helper for Corollary 6.29.1: a Kuhn--Tucker vector is exactly a linear minorant of the
negated origin directional derivative. -/
lemma helperForCorollary_6_29_1_kuhnTucker_iff_negatedDirectionalDerivative_minorant
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (uStar : Fin m → ℝ) :
    IsKuhnTuckerVector F uStar ↔
      ∀ y : Fin m → ℝ,
        ((dotProduct y uStar : ℝ) : EReal) ≤
          generalizedConvexProgramOriginDirectionalDerivative F (-y) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv :
      ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hKT :
      IsKuhnTuckerVector F uStar ↔
        -uStar ∈ euclideanSubdifferentialAt p 0 :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite uStar
  have hminor :
      -uStar ∈ euclideanSubdifferentialAt p 0 ↔
        ∀ y : Fin m → ℝ,
          ((dotProduct y (-uStar) : ℝ) : EReal) ≤ upperDirectionalDerivativeAt p 0 y := by
    change dotProductEquiv ℝ (Fin m) (-uStar) ∈ subdifferentialAt p 0 ↔ _
    exact
      helperForTheorem_23_2_subgradient_iff_vector_linear_minorant
        p hpConv 0 hpFinite (-uStar)
  constructor
  · intro huStar y
    -- Substitute `-y` into the subgradient minorant to remove the sign on `uStar`.
    have hy :
        ((dotProduct (-y) (-uStar) : ℝ) : EReal) ≤ upperDirectionalDerivativeAt p 0 (-y) :=
      (hminor.1 (hKT.1 huStar)) (-y)
    simpa [p, generalizedConvexProgramOriginDirectionalDerivative] using hy
  · intro hu
    have hminorant :
        ∀ y : Fin m → ℝ,
          ((dotProduct y (-uStar) : ℝ) : EReal) ≤ upperDirectionalDerivativeAt p 0 y := by
      intro y
      -- Replacing `y` by `-y` in the target minorant restores the subgradient form.
      have hy :
          ((dotProduct (-y) uStar : ℝ) : EReal) ≤
            generalizedConvexProgramOriginDirectionalDerivative F (-(-y)) :=
        hu (-y)
      simpa [p, generalizedConvexProgramOriginDirectionalDerivative] using hy
    exact hKT.2 (hminor.2 hminorant)

-- Proof sketch: apply Theorem 6.29.1 to obtain convexity of the perturbation function and the
-- identification of Kuhn--Tucker vectors with the negative subdifferential at the origin. Then
-- invoke the directional-derivative representation theorem for convex functions at finite points:
-- the positive directional limit exists in every direction, defines a positively homogeneous
-- convex function, and the closure of its negated-direction profile is the support function of the
-- corresponding subdifferential set. Transport that subdifferential set through the sign change
-- `uStar ↦ -uStar` using the Kuhn--Tucker characterization.
/-- Corollary 6.29.1: If the optimal value of the generalized convex program `(P)` associated with
a convex bifunction `F` is finite, then the one-sided directional derivative
`u ↦ (inf F)(0; u)` exists for every `u ∈ ℝ^m` and is a positively homogeneous convex function.
Moreover, the Kuhn--Tucker vectors form a closed convex set in `ℝ^m`, and its support function is
the closure of `u ↦ (inf F)(0; -u)`. -/
theorem generalizedConvexProgram_kuhnTuckerVectors_closedConvex_and_support_originDirectionalDerivative
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    (∀ u : Fin m → ℝ,
      ∃ l : EReal,
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction F) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds l) ∧
          generalizedConvexProgramOriginDirectionalDerivative F u = l) ∧
    PositivelyHomogeneous (generalizedConvexProgramOriginDirectionalDerivative F) ∧
    ConvexFunction (generalizedConvexProgramOriginDirectionalDerivative F) ∧
    IsClosed {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
    Convex ℝ {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
    convexFunctionClosure
        (fun u : Fin m → ℝ =>
          generalizedConvexProgramOriginDirectionalDerivative F (-u)) =
      supportFunctionEReal {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let D : (Fin m → ℝ) → EReal := generalizedConvexProgramOriginDirectionalDerivative F
  have hpConv :
      ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  rcases convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite with
    ⟨hdir, hposD, hconvD, hzeroD, _hsymmD⟩
  have hnegProps :
      PositivelyHomogeneous (fun u : Fin m → ℝ => D (-u)) ∧
        ConvexFunction (fun u : Fin m → ℝ => D (-u)) := by
    -- The support theorem applies to the negated-direction profile of the derivative.
    simpa [D, generalizedConvexProgramOriginDirectionalDerivative] using
      helperForCorollary_6_29_1_negatedOriginDirectionalDerivative_posHom_convex F hfinite
  have hnotTop : ¬ ∀ y : Fin m → ℝ, D (-y) = (⊤ : EReal) := by
    -- The derivative vanishes at the origin, so the negated profile is not identically `⊤`.
    intro htop
    have hzeroTop : D 0 = (⊤ : EReal) := by
      simpa using htop 0
    have hzeroTop' : upperDirectionalDerivativeAt p 0 0 = (⊤ : EReal) := by
      simpa [D, generalizedConvexProgramOriginDirectionalDerivative] using hzeroTop
    rw [hzeroD] at hzeroTop'
    simp at hzeroTop'
  rcases
      clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
        (n := m) (f := fun u : Fin m → ℝ => D (-u)) hnegProps.1 hnegProps.2 hnotTop with
    ⟨C, hCclosed, hCconv, hclConv, hCeq⟩
  have hCeqKT :
      C = {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
    -- Identify the support-representing minorant set with the Kuhn--Tucker vectors.
    ext uStar
    simp [hCeq, D, generalizedConvexProgramOriginDirectionalDerivative,
      helperForCorollary_6_29_1_kuhnTucker_iff_negatedDirectionalDerivative_minorant
        F hfinite uStar]
  have hclEqClosure :
      clConv m (fun u : Fin m → ℝ => D (-u)) =
        convexFunctionClosure (fun u : Fin m → ℝ => D (-u)) := by
    -- Convert the Chapter 13 closure `clConv` into the convex-function closure.
    calc
      clConv m (fun u : Fin m → ℝ => D (-u)) =
          fenchelConjugate m (fenchelConjugate m (fun u : Fin m → ℝ => D (-u))) := by
            symm
            simpa using
              (fenchelConjugate_biconjugate_eq_clConv
                (n := m) (f := fun u : Fin m → ℝ => D (-u)))
      _ = convexFunctionClosure (fun u : Fin m → ℝ => D (-u)) := by
            simpa using
              (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
                (n := m) (f := fun u : Fin m → ℝ => D (-u)) hnegProps.2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    -- The origin directional derivative is the limit supplied by Theorem 23.1.
    refine ⟨D u, ?_, rfl⟩
    simpa [p, D, generalizedConvexProgramOriginDirectionalDerivative] using (hdir u).2.1
  · -- The derivative itself is positively homogeneous.
    simpa [D, generalizedConvexProgramOriginDirectionalDerivative] using hposD
  · -- The derivative itself is convex.
    simpa [D, generalizedConvexProgramOriginDirectionalDerivative] using hconvD
  · -- Closedness is inherited from the Chapter 13 representing set after identifying it with the
    -- Kuhn--Tucker set.
    simpa [hCeqKT] using hCclosed
  · refine ⟨?_, ?_⟩
    · -- The same representing set is convex.
      simpa [hCeqKT] using hCconv
    · -- The support function of the Kuhn--Tucker set is the closure of the negated derivative.
      calc
        convexFunctionClosure
            (fun u : Fin m → ℝ =>
              generalizedConvexProgramOriginDirectionalDerivative F (-u)) =
            convexFunctionClosure (fun u : Fin m → ℝ => D (-u)) := by
              rfl
        _ = clConv m (fun u : Fin m → ℝ => D (-u)) := hclEqClosure.symm
        _ = supportFunctionEReal C := hclConv
        _ = supportFunctionEReal {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
              rw [hCeqKT]

end Section29
end Chap06
