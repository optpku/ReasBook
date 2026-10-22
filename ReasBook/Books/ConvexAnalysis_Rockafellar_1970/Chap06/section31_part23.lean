/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part22

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- A closed proper convex function has a minimizer for its quadratic Moreau envelope at every
point. -/
lemma quadraticMoreauEnvelopeMinimizerExists {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ, ∃ x : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x := by
  intro z
  exact (moreau_decomposition_theorem (n := n) f hf_closed hf_proper z).2.2.2.1.exists

-- Proof sketch: specialize Theorem 31.5 to the dual envelope clause, which gives a minimizer of
-- the quadratic Moreau envelope of `f⋆` at every `z`.
/-- A closed proper convex function has a minimizer for the quadratic Moreau envelope of its
Fenchel conjugate at every point. -/
lemma conjugateQuadraticMoreauEnvelopeMinimizerExists {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      ∃ xStar : Fin n → ℝ,
        AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar := by
  intro z
  exact (moreau_decomposition_theorem (n := n) f hf_closed hf_proper z).2.2.2.2.1.exists

/-- The proximation operator `prox(z | f)`, defined as a chosen minimizer of
`x ↦ f x + |z - x|^2 / 2`. -/
noncomputable def proximationOperator {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose (quadraticMoreauEnvelopeMinimizerExists (n := n) f hf_closed hf_proper z)

/-- A chosen minimizer of the quadratic Moreau envelope of `f⋆`. When closed/proper witnesses for
`f⋆` are supplied, a separate theorem identifies this choice with
`proximationOperator (fenchelConjugate n f) ...`. -/
noncomputable def conjugateProximationOperator {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose
    (conjugateQuadraticMoreauEnvelopeMinimizerExists (n := n) f hf_closed hf_proper z)

/-- A decomposition `z = x + x⋆` lying in the graph of the subdifferential of `f`. -/
def IsSubdifferentialGraphDecomposition {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (z x xStar : Fin n → ℝ) : Prop :=
  z = x + xStar ∧ dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x

/-- A point of `C` minimizing the Euclidean distance to `z`. -/
def IsClosestPointInSet {n : ℕ} (C : Set (Fin n → ℝ)) (z x : Fin n → ℝ) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, euclideanNorm (z - x) ≤ euclideanNorm (z - y)

/-- A decomposition of `z` into a vector in a cone `K` and a vector in its polar cone, with
complementary orthogonality. -/
def IsConePolarDecomposition {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (z x xStar : Fin n → ℝ) : Prop :=
  z = x + xStar ∧
    x ∈ (K : Set (Fin n → ℝ)) ∧
      xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
        dotProduct x xStar = 0

/-- A decomposition of `z` into a vector in a subspace and a vector in its orthogonal
complement. -/
def IsOrthogonalSubspaceDecomposition {n : ℕ} (L : Submodule ℝ (Fin n → ℝ))
    (z x xStar : Fin n → ℝ) : Prop :=
  z = x + xStar ∧
    x ∈ (L : Set (Fin n → ℝ)) ∧
      xStar ∈ subspaceOrthogonalComplementSet L

-- Proof sketch: extract from Theorem 31.5 the unique minimizer of the quadratic Moreau envelope
-- of `f` at `z`, identify it with `proximationOperator`, then use the same theorem for `f⋆` to
-- identify `prox(z | f⋆)` with the complementary vector `z - prox(z | f)`. The characterization
-- of primal-dual minimizers in Theorem 31.5 yields the unique graph decomposition
-- `z = x + x⋆` with `x⋆ ∈ ∂f(x)`.
/-- Remark 31.5.1 (Proximation Operator and Unique Decomposition via Theorem 31.5): for a closed
proper convex function `f`, every `z` has a unique decomposition `z = x + x⋆` with
`(x, x⋆)` in the graph of `∂f`. The first component is the minimizer `prox(z | f)` of
`x ↦ f x + |z - x|^2 / 2`, while the complementary term `x⋆ = z - x` is the unique dual
minimizer for the quadratic Moreau envelope of `f⋆`, so `prox(z | f⋆) = z - prox(z | f)` under
the same closed/proper hypotheses on `f`. The indicator, cone, and subspace specializations
mentioned in the text are recorded in separate statements below. -/
theorem moreau_proximation_operator_remark {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      let x := proximationOperator (n := n) f hf_closed hf_proper z
      let xStar := z - x
      AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
        (∃! x0 : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x0) ∧
        proximationOperator (n := n) (fenchelConjugate n f)
          ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2,
            (fenchelConjugate_closedConvex (n := n) (f := f)).1⟩
          (proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper) z = z - x ∧
        IsSubdifferentialGraphDecomposition f z x xStar ∧
        (∃! p : (Fin n → ℝ) × (Fin n → ℝ), IsSubdifferentialGraphDecomposition f z p.1 p.2) := by
  intro z
  let hStarClosed : ClosedConvexFunction (fenchelConjugate n f) :=
    ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2,
      (fenchelConjugate_closedConvex (n := n) (f := f)).1⟩
  let hStarProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  let x := proximationOperator (n := n) f hf_closed hf_proper z
  let y := proximationOperator (n := n) (fenchelConjugate n f) hStarClosed hStarProper z
  change AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
    (∃! x0 : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x0) ∧
    y = z - x ∧ IsSubdifferentialGraphDecomposition f z x (z - x) ∧
    (∃! p : (Fin n → ℝ) × (Fin n → ℝ), IsSubdifferentialGraphDecomposition f z p.1 p.2)
  have hMoreau := moreau_decomposition_theorem (n := n) f hf_closed hf_proper z
  have hPrimalUnique :
      ∃! x0 : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x0 :=
    hMoreau.2.2.2.1
  have hDualUnique :
      ∃! xStar : Fin n → ℝ,
        AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar :=
    hMoreau.2.2.2.2.1
  have hPair := hMoreau.2.2.2.2.2.1
  have hxAttains : AttainsQuadraticMoreauEnvelopeAt (n := n) f z x := by
    simpa [x, proximationOperator] using
      (Classical.choose_spec
        (quadraticMoreauEnvelopeMinimizerExists (n := n) f hf_closed hf_proper z))
  have hyAttains :
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z y := by
    simpa [y, hStarClosed, hStarProper, proximationOperator] using
      (Classical.choose_spec
        (quadraticMoreauEnvelopeMinimizerExists (n := n) (fenchelConjugate n f)
          hStarClosed hStarProper z))
  have hGraphXY :
      z = x + y ∧ dotProductEquiv ℝ (Fin n) y ∈ subdifferentialAt f x :=
    (hPair x y).1 ⟨hxAttains, hyAttains⟩
  have hyEq : y = z - x := by
    rw [hGraphXY.1]
    abel
  have hGraphXSub : IsSubdifferentialGraphDecomposition f z x (z - x) := by
    simpa [IsSubdifferentialGraphDecomposition, hyEq] using hGraphXY
  refine ⟨hxAttains, hPrimalUnique, hyEq, hGraphXSub, ?_⟩
  refine ⟨(x, z - x), hGraphXSub, ?_⟩
  intro p hp
  have hpAttains :
      AttainsQuadraticMoreauEnvelopeAt (n := n) f z p.1 ∧
        AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z p.2 :=
    (hPair p.1 p.2).2 (by
      simpa [IsSubdifferentialGraphDecomposition] using hp)
  apply Prod.ext
  · exact hPrimalUnique.unique hpAttains.1 hxAttains
  · exact (hDualUnique.unique hpAttains.2 hyAttains).trans hyEq

-- Proof sketch: apply the uniqueness of the dual minimizer in Theorem 31.5 to compare the chosen
-- dual minimizer `conjugateProximationOperator` with the decomposition term `z - prox(z | f)`.
/-- The chosen dual minimizer in Moreau's decomposition is the complementary vector
`z - prox(z | f)`. -/
theorem conjugateProximationOperator_eq_sub_proximationOperator {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      conjugateProximationOperator (n := n) f hf_closed hf_proper z =
        z - proximationOperator (n := n) f hf_closed hf_proper z := by
  intro z
  let hStarClosed : ClosedConvexFunction (fenchelConjugate n f) :=
    ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2,
      (fenchelConjugate_closedConvex (n := n) (f := f)).1⟩
  let hStarProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  let y := conjugateProximationOperator (n := n) f hf_closed hf_proper z
  let y0 := proximationOperator (n := n) (fenchelConjugate n f) hStarClosed hStarProper z
  have hDualUnique :
      ∃! xStar : Fin n → ℝ,
        AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar :=
    (moreau_decomposition_theorem (n := n) f hf_closed hf_proper z).2.2.2.2.1
  have hyAttains :
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z y := by
    simpa [y, conjugateProximationOperator] using
      (Classical.choose_spec
        (conjugateQuadraticMoreauEnvelopeMinimizerExists (n := n) f hf_closed hf_proper z))
  have hy0Attains :
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z y0 := by
    simpa [y0, hStarClosed, hStarProper, proximationOperator] using
      (Classical.choose_spec
        (quadraticMoreauEnvelopeMinimizerExists (n := n) (fenchelConjugate n f)
          hStarClosed hStarProper z))
  have hyEq : y = y0 := hDualUnique.unique hyAttains hy0Attains
  have hy0Eq : y0 = z - proximationOperator (n := n) f hf_closed hf_proper z := by
    simpa [y0, hStarClosed, hStarProper] using
      (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z).2.2.1
  exact hyEq.trans hy0Eq

-- Proof sketch: use `fenchelConjugate_closedConvex` and
-- `proper_fenchelConjugate_of_proper` to obtain the closed/proper hypotheses for `f⋆`, then
-- identify both sides as the unique minimizer of the quadratic Moreau envelope of `f⋆` via the
-- previous theorem.
/-- For a closed proper convex function `f`, the proximation operator of `f⋆` is the
complementary term in Moreau's decomposition. -/
theorem fenchelConjugate_proximationOperator_eq_sub_proximationOperator {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      proximationOperator (n := n) (fenchelConjugate n f)
        ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2,
          (fenchelConjugate_closedConvex (n := n) (f := f)).1⟩
        (proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper) z =
        z - proximationOperator (n := n) f hf_closed hf_proper z := by
  intro z
  exact (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z).2.2.1

-- Proof sketch: write `zᵢ = xᵢ + xᵢ⋆` using Remark 31.5.1, where
-- `xᵢ = prox(zᵢ | f)` and `xᵢ⋆ = prox(zᵢ | f⋆)`. Expanding `‖z₁ - z₀‖²` gives the cross term
-- `2 ⟪x₁ - x₀, x₁⋆ - x₀⋆⟫`, and monotonicity of the subdifferential makes that term nonnegative,
-- yielding `‖x₁ - x₀‖ ≤ ‖z₁ - z₀‖`.
/-- Example 31.5.2 (Contraction Property of the Proximation Operator): if `f : ℝ^n → ℝ ∪ {+∞}`
is closed proper convex, then the proximation operator is nonexpansive:
`‖prox(z₁ | f) - prox(z₀ | f)‖ ≤ ‖z₁ - z₀‖` for all `z₀, z₁ ∈ ℝ^n`. -/
theorem proximationOperator_is_nonexpansive {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z0 z1 : Fin n → ℝ,
      euclideanNorm
          (proximationOperator (n := n) f hf_closed hf_proper z1 -
            proximationOperator (n := n) f hf_closed hf_proper z0) ≤
        euclideanNorm (z1 - z0) := by
  intro z0 z1
  let x0 := proximationOperator (n := n) f hf_closed hf_proper z0
  let x1 := proximationOperator (n := n) f hf_closed hf_proper z1
  let y0 := z0 - x0
  let y1 := z1 - x1
  have hgraph0 : IsSubdifferentialGraphDecomposition f z0 x0 y0 := by
    simpa [x0, y0] using
      (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z0).2.2.2.1
  have hgraph1 : IsSubdifferentialGraphDecomposition f z1 x1 y1 := by
    simpa [x1, y1] using
      (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z1).2.2.2.1
  have hmono : 0 ≤ dotProduct (x1 - x0) (y1 - y0) :=
    helperForLemma_26_2_preimageSubdifferential_monotone hf_proper hgraph0.2 hgraph1.2
  have hsum : z1 - z0 = (x1 - x0) + (y1 - y0) := by
    rw [hgraph0.1, hgraph1.1]
    abel
  have hsq :
      dotProduct (x1 - x0) (x1 - x0) ≤ dotProduct (z1 - z0) (z1 - z0) := by
    rw [hsum]
    simp only [dotProduct_add, add_dotProduct]
    rw [dotProduct_comm (y1 - y0) (x1 - x0)]
    nlinarith [dotProduct_self_nonneg (y1 - y0)]
  simpa [x0, x1, euclideanNorm] using Real.sqrt_le_sqrt hsq

-- Proof sketch: specialize the remark to the indicator function of `C`; then the Moreau
-- minimization problem reduces to minimizing the squared distance to `z` over `C`.
/-- For the indicator of a closed convex set `C`, the proximation operator is the closest point in
`C` to the target vector `z`. -/
theorem indicatorFunction_proximationOperator_isClosestPoint {n : ℕ}
    (C : Set (Fin n → ℝ))
    (hC_closed : ClosedConvexFunction (indicatorFunction C))
    (hC_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction C)) :
    ∀ z : Fin n → ℝ,
      IsClosestPointInSet C z
        (proximationOperator (n := n) (indicatorFunction C) hC_closed hC_proper z) := by
  intro z
  let x := proximationOperator (n := n) (indicatorFunction C) hC_closed hC_proper z
  have hgraph :
      IsSubdifferentialGraphDecomposition (indicatorFunction C) z x (z - x) := by
    simpa [x] using
      (moreau_proximation_operator_remark (n := n) (indicatorFunction C)
        hC_closed hC_proper z).2.2.2.1
  have hsub :
      IsSubgradientAt (indicatorFunction C) x (dotProductEquiv ℝ (Fin n) (z - x)) :=
    hgraph.2
  rcases hC_proper.2.1 with ⟨⟨c, μ⟩, hc⟩
  have hcC : c ∈ C := by
    by_contra hcnot
    simp [epigraph, indicatorFunction, hcnot] at hc
  have hxC : x ∈ C := by
    by_contra hxnot
    have hcineq := hsub c
    have hcval : indicatorFunction C c = 0 := by simp [indicatorFunction, hcC]
    have hxval : indicatorFunction C x = ⊤ := by simp [indicatorFunction, hxnot]
    rw [hcval, hxval] at hcineq
    rw [EReal.top_add_coe] at hcineq
    simp at hcineq
  refine ⟨hxC, ?_⟩
  intro y hy
  have hineq := hsub y
  have hyval : indicatorFunction C y = 0 := by simp [indicatorFunction, hy]
  have hxval : indicatorFunction C x = 0 := by simp [indicatorFunction, hxC]
  rw [hyval, hxval] at hineq
  simp only [zero_add] at hineq
  change ((dotProduct (z - x) (y - x) : ℝ) : EReal) ≤ 0 at hineq
  have hdot : dotProduct (z - x) (y - x) ≤ 0 := by
    exact_mod_cast hineq
  have hcross : 0 ≤ dotProduct (z - x) (x - y) := by
    have := neg_nonneg.mpr hdot
    simpa [sub_eq_add_neg, dotProduct_neg] using this
  have hsum : z - y = (z - x) + (x - y) := by abel
  have hsq : dotProduct (z - x) (z - x) ≤ dotProduct (z - y) (z - y) := by
    rw [hsum]
    simp only [dotProduct_add, add_dotProduct]
    rw [dotProduct_comm (x - y) (z - x)]
    nlinarith [dotProduct_self_nonneg (x - y)]
  simpa [euclideanNorm] using Real.sqrt_le_sqrt hsq

-- Proof sketch: specialize the remark to `f = indicatorFunction (K : Set _)`, use the standard
-- conjugacy formula for indicators of closed convex cones, and rewrite the resulting graph
-- decomposition as a cone-polar decomposition.
/-- For the indicator of a closed convex cone `K`, the Moreau decomposition becomes the cone-polar
decomposition, and the Fenchel conjugate is the indicator of the polar cone `Kᵒ`. -/
theorem indicatorFunction_cone_moreauDecomposition {n : ℕ}
    (K : ConvexCone ℝ (Fin n → ℝ))
    (hK_closed : ClosedConvexFunction (indicatorFunction (K : Set (Fin n → ℝ))))
    (hK_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (indicatorFunction (K : Set (Fin n → ℝ)))) :
    ∀ z : Fin n → ℝ,
      let x := proximationOperator (n := n) (indicatorFunction (K : Set (Fin n → ℝ)))
        hK_closed hK_proper z
      let xStar := conjugateProximationOperator (n := n)
        (indicatorFunction (K : Set (Fin n → ℝ))) hK_closed hK_proper z
      fenchelConjugate n (indicatorFunction (K : Set (Fin n → ℝ))) =
          indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ))) ∧
        IsConePolarDecomposition K z x xStar := by
  intro z
  let f := indicatorFunction (K : Set (Fin n → ℝ))
  let x := proximationOperator (n := n) f hK_closed hK_proper z
  let y := conjugateProximationOperator (n := n) f hK_closed hK_proper z
  change fenchelConjugate n f =
      indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ))) ∧
    IsConePolarDecomposition K z x y
  rcases hK_proper.2.1 with ⟨⟨k0, μ⟩, hk0epi⟩
  have hk0K : k0 ∈ (K : Set (Fin n → ℝ)) := by
    by_contra hk0not
    have htop : (⊤ : EReal) ≤ (μ : EReal) := by
      simpa [epigraph, indicatorFunction, hk0not] using hk0epi.2
    simp at htop
  have hKne : (K : Set (Fin n → ℝ)).Nonempty := ⟨k0, hk0K⟩
  have hconj : fenchelConjugate n f =
      indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ))) := by
    calc
      fenchelConjugate n f = supportFunctionEReal (K : Set (Fin n → ℝ)) := by
        simpa [f] using
          (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
            (n := n) (C := (K : Set (Fin n → ℝ))))
      _ = indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ))) := by
        simpa [euclideanPolarCone] using
          (section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar K hKne)
  have hyEq : y = z - x := by
    simpa [f, x, y] using
      (conjugateProximationOperator_eq_sub_proximationOperator
        (n := n) f hK_closed hK_proper z)
  have hgraph : IsSubdifferentialGraphDecomposition f z x (z - x) := by
    simpa [f, x] using
      (moreau_proximation_operator_remark (n := n) f hK_closed hK_proper z).2.2.2.1
  have hgeom :
      x ∈ (K : Set (Fin n → ℝ)) ∧
        z - x ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x (z - x) = 0 := by
    exact (helperForCorollary_23_5_4_indicatorSubgradient_iff_mem_polar_orthogonal
      K hKne x (z - x)).1 hgraph.2
  refine ⟨hconj, ?_⟩
  change z = x + y ∧ x ∈ (K : Set (Fin n → ℝ)) ∧
    y ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧ dotProduct x y = 0
  rw [hyEq]
  exact ⟨hgraph.1, hgeom⟩

-- Proof sketch: specialize the cone case to a subspace `L`, where the polar cone is the
-- orthogonal complement, so the decomposition becomes the usual orthogonal splitting.
/-- For the indicator of a subspace `L`, the Moreau decomposition is the orthogonal decomposition
with respect to `L`. -/
theorem indicatorFunction_subspace_orthogonalDecomposition {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ))
    (hL_closed : ClosedConvexFunction (indicatorFunction (L : Set (Fin n → ℝ))))
    (hL_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (indicatorFunction (L : Set (Fin n → ℝ)))) :
    ∀ z : Fin n → ℝ,
      let x := proximationOperator (n := n) (indicatorFunction (L : Set (Fin n → ℝ)))
        hL_closed hL_proper z
      let xStar := conjugateProximationOperator (n := n)
        (indicatorFunction (L : Set (Fin n → ℝ))) hL_closed hL_proper z
      IsOrthogonalSubspaceDecomposition L z x xStar := by
  intro z
  let f := indicatorFunction (L : Set (Fin n → ℝ))
  let x := proximationOperator (n := n) f hL_closed hL_proper z
  let y := conjugateProximationOperator (n := n) f hL_closed hL_proper z
  change IsOrthogonalSubspaceDecomposition L z x y
  have hyEq : y = z - x := by
    simpa [f, x, y] using
      (conjugateProximationOperator_eq_sub_proximationOperator
        (n := n) f hL_closed hL_proper z)
  have hgraph : IsSubdifferentialGraphDecomposition f z x (z - x) := by
    simpa [f, x] using
      (moreau_proximation_operator_remark (n := n) f hL_closed hL_proper z).2.2.2.1
  rcases hgraph with ⟨hzsum, hsub⟩
  have hIsSub : IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) (z - x)) := hsub
  have hxL : x ∈ (L : Set (Fin n → ℝ)) := by
    by_contra hxnot
    have h0 := hIsSub 0
    simp [f, indicatorFunction, hxnot] at h0
  refine ⟨?_, hxL, ?_⟩
  · rw [hyEq]
    exact hzsum
  · rw [hyEq]
    intro l hl
    have hxl : x + l ∈ (L : Set (Fin n → ℝ)) := L.add_mem hxL hl
    have hxml : x - l ∈ (L : Set (Fin n → ℝ)) := L.sub_mem hxL hl
    have hxml' : x + -l ∈ (L : Set (Fin n → ℝ)) := by
      simpa [sub_eq_add_neg] using hxml
    have hxml'' : -l + x ∈ (L : Set (Fin n → ℝ)) := by
      simpa [add_comm] using hxml'
    have hplus := hIsSub (x + l)
    have hminus := hIsSub (x - l)
    simp only [f, indicatorFunction, hxL, hxl, if_pos,
      dotProductEquiv_apply_apply, add_sub_cancel_left] at hplus
    have hplusReal : dotProduct (z - x) l ≤ 0 := by
      have hplusReal' : 0 + dotProduct (z - x) l ≤ 0 := by
        exact_mod_cast hplus
      simpa using hplusReal'
    have hminusReal : 0 ≤ dotProduct (z - x) l := by
      have hminus' : ((dotProduct (z - x) (-l) : ℝ) : EReal) ≤ 0 := by
        simpa [f, indicatorFunction, hxL, hxml', hxml'', dotProductEquiv_apply_apply,
          sub_eq_add_neg, dotProduct_neg, add_comm] using hminus
      have hminusReal' : dotProduct (z - x) (-l) ≤ 0 := by
        exact_mod_cast hminus'
      simpa [dotProduct_neg] using hminusReal'
    exact le_antisymm hplusReal hminusReal

theorem section31_example_31_5_2 : True := by
  trivial

/-- Helper for Corollary 31.5.1: the canonical Moreau pair determined by `z` belongs to the graph
of `∂ f`. -/
lemma helperForCorollary_31_5_1_inversePair_mem_graph {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z : Fin n → ℝ) :
    ((proximationOperator (n := n) f hf_closed hf_proper z,
        z - proximationOperator (n := n) f hf_closed hf_proper z) :
      (Fin n → ℝ) × (Fin n → ℝ)) ∈
      {p : (Fin n → ℝ) × (Fin n → ℝ) |
        dotProductEquiv ℝ (Fin n) p.2 ∈ subdifferentialAt f p.1} := by
  -- Remark 31.5.1 records the canonical decomposition point in the graph of `∂ f`.
  simpa [IsSubdifferentialGraphDecomposition] using
    (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z).2.2.2.1

/-- Helper for Corollary 31.5.1: any graph point is exactly the canonical Moreau decomposition of
its sum. -/
lemma helperForCorollary_31_5_1_canonicalPair_eq_of_graphPoint {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x xStar : Fin n → ℝ}
    (hx : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    let z := x + xStar
    (proximationOperator (n := n) f hf_closed hf_proper z,
      z - proximationOperator (n := n) f hf_closed hf_proper z) = (x, xStar) := by
  -- Remark 31.5.1 also gives uniqueness of graph decompositions for each `z`.
  dsimp
  have huniq :=
    (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper (x + xStar)).2.2.2.2
  -- The canonical pair supplied by the remark is one decomposition.
  have hcanon :
      IsSubdifferentialGraphDecomposition f (x + xStar)
        (proximationOperator (n := n) f hf_closed hf_proper (x + xStar))
        ((x + xStar) - proximationOperator (n := n) f hf_closed hf_proper (x + xStar)) := by
    exact (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper (x + xStar)).2.2.2.1
  -- The given graph point is another decomposition of the same vector.
  have hgraph : IsSubdifferentialGraphDecomposition f (x + xStar) x xStar := by
    exact ⟨rfl, hx⟩
  exact ExistsUnique.unique huniq hcanon hgraph

/-- Helper for Corollary 31.5.1: the proximation operator is continuous because Example 31.5.2
makes it nonexpansive. -/
lemma helperForCorollary_31_5_1_proximationOperator_continuous {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Continuous (proximationOperator (n := n) f hf_closed hf_proper) := by
  -- Compare the ambient sup norm with the Euclidean norm used by the nonexpansive estimate.
  refine (LipschitzWith.of_dist_le_mul
    (K := ⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩) ?_).continuous
  intro z0 z1
  calc
    dist (proximationOperator (n := n) f hf_closed hf_proper z0)
        (proximationOperator (n := n) f hf_closed hf_proper z1) =
        ‖proximationOperator (n := n) f hf_closed hf_proper z0 -
          proximationOperator (n := n) f hf_closed hf_proper z1‖ := by
          rw [dist_eq_norm]
    _ ≤ euclideanNorm
        (proximationOperator (n := n) f hf_closed hf_proper z0 -
          proximationOperator (n := n) f hf_closed hf_proper z1) := by
      simpa [euclideanNorm] using
        (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm
          (n := n) (proximationOperator (n := n) f hf_closed hf_proper z0 -
            proximationOperator (n := n) f hf_closed hf_proper z1)).1
    _ ≤ euclideanNorm (z0 - z1) :=
      proximationOperator_is_nonexpansive (n := n) f hf_closed hf_proper z1 z0
    _ ≤ Real.sqrt (n : ℝ) * ‖z0 - z1‖ := by
      simpa [euclideanNorm] using
        (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm
          (n := n) (z0 - z1)).2
    _ = Real.sqrt (n : ℝ) * dist z0 z1 := by rw [dist_eq_norm]

/-- Helper for Corollary 31.5.1: the ambient inverse pair map
`z ↦ (prox(z | f), z - prox(z | f))` is continuous. -/
lemma helperForCorollary_31_5_1_inverseMap_continuous {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Continuous (fun z : Fin n → ℝ =>
      ((proximationOperator (n := n) f hf_closed hf_proper z,
        z - proximationOperator (n := n) f hf_closed hf_proper z) :
          (Fin n → ℝ) × (Fin n → ℝ))) := by
  -- The first coordinate is `prox`, and the second is `id - prox`.
  refine
    (helperForCorollary_31_5_1_proximationOperator_continuous
      (n := n) f hf_closed hf_proper).prodMk
      (continuous_id.sub
        (helperForCorollary_31_5_1_proximationOperator_continuous
          (n := n) f hf_closed hf_proper))

-- Proof sketch: use Remark 31.5.1 to get, for each `z`, a unique pair `(x, x⋆)` in the graph of
-- `∂ f` with `z = x + x⋆`, so the addition map from the graph onto `ℝ^n` is bijective. Then use
-- Example 31.5.2 together with the identity `x⋆ = z - prox(z | f)` to obtain continuity of both
-- the addition map and its inverse, yielding the claimed homeomorphism.
/-- Corollary 31.5.1: if `f : ℝ^n → ℝ ∪ {+∞}` is closed proper convex, then the map
`(x, x⋆) ↦ x + x⋆` is a homeomorphism from the graph of `∂ f` onto `ℝ^n`; equivalently, the graph
of the subdifferential of `f` is homeomorphic to `ℝ^n`. -/
theorem subdifferentialGraph_addition_homeomorph {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∃ h :
      {p : (Fin n → ℝ) × (Fin n → ℝ) |
        dotProductEquiv ℝ (Fin n) p.2 ∈ subdifferentialAt f p.1} ≃ₜ (Fin n → ℝ),
      ∀ p, h p = p.1.1 + p.1.2 := by
  refine ⟨{ toEquiv :=
              { toFun := fun p => p.1.1 + p.1.2
                invFun := fun z => ⟨(proximationOperator (n := n) f hf_closed hf_proper z,
                    z - proximationOperator (n := n) f hf_closed hf_proper z),
                  helperForCorollary_31_5_1_inversePair_mem_graph
                    (n := n) f hf_closed hf_proper z⟩
                left_inv := ?_
                right_inv := ?_ }
            continuous_toFun := ?_
            continuous_invFun := ?_ }, ?_⟩
  · intro p
    -- Uniqueness of the graph decomposition identifies the inverse with the original point.
    apply Subtype.ext
    simpa using
      helperForCorollary_31_5_1_canonicalPair_eq_of_graphPoint
        (n := n) f hf_closed hf_proper p.2
  · intro z
    -- The sum of the canonical pair is exactly `z`.
    simp
  · -- The forward map is the restriction of ambient addition on the product.
    exact continuous_subtype_val.fst.add continuous_subtype_val.snd
  · -- The inverse is continuous after lifting the ambient pair map to the subtype.
    exact Continuous.subtype_mk
      (helperForCorollary_31_5_1_inverseMap_continuous (n := n) f hf_closed hf_proper)
      (fun z =>
        helperForCorollary_31_5_1_inversePair_mem_graph (n := n) f hf_closed hf_proper z)
  · intro p
    rfl

/-- A Euclidean set-valued map is monotone if every two graph points satisfy the usual
dot-product monotonicity inequality. -/
def IsMonotoneEuclideanSetValuedMap {n : ℕ}
    (T : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∀ ⦃x y u v : Fin n → ℝ⦄, u ∈ T x → v ∈ T y → 0 ≤ dotProduct (x - y) (u - v)

/-- A Euclidean set-valued map is maximal monotone if it is monotone and every monotone
pointwise enlargement agrees with it. -/
def IsMaximalMonotoneEuclideanSetValuedMap {n : ℕ}
    (T : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  IsMonotoneEuclideanSetValuedMap T ∧
    ∀ S : (Fin n → ℝ) → Set (Fin n → ℝ),
      IsMonotoneEuclideanSetValuedMap S →
      (∀ x : Fin n → ℝ, T x ⊆ S x) →
      ∀ x : Fin n → ℝ, S x ⊆ T x

/-- Helper for Corollary 31.5.2: the Euclideanized subdifferential inherits the standard
monotonicity inequality from the cyclic monotonicity of the convex subdifferential. -/
lemma helperForCorollary_31_5_2_subdifferential_monotone {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsMonotoneEuclideanSetValuedMap
      (fun x : Fin n → ℝ => euclideanSubdifferentialAt (n := n) f x) := by
  intro x y u v hu hv
  -- Rewrite Euclidean subgradient membership as membership in the pulled-back graph used by the
  -- earlier cyclic-monotonicity lemma.
  have hu' :
      u ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
    simpa [euclideanSubdifferentialAt] using hu
  have hv' :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f y) := by
    simpa [euclideanSubdifferentialAt] using hv
  -- Apply the previously established monotonicity statement with the points ordered to match the
  -- target pairing `⟪x - y, u - v⟫`.
  exact
    helperForLemma_26_2_preimageSubdifferential_monotone
      (hproper := hf_proper) (x₀ := y) (x₁ := x) (v₀ := v) (v₁ := u) hv' hu'

/-- Helper for Corollary 31.5.2: every `z` splits as `z = x + u` with
`u ∈ euclideanSubdifferentialAt f x`. -/
lemma helperForCorollary_31_5_2_exists_sum_decomposition {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      ∃ x u : Fin n → ℝ, u ∈ euclideanSubdifferentialAt (n := n) f x ∧ z = x + u := by
  intro z
  let x : Fin n → ℝ := proximationOperator (n := n) f hf_closed hf_proper z
  have hgraph : IsSubdifferentialGraphDecomposition f z x (z - x) := by
    -- Remark 31.5.1 identifies the canonical Moreau pair as a graph point of `∂ f`.
    simpa [x] using (moreau_proximation_operator_remark (n := n) f hf_closed hf_proper z).2.2.2.1
  refine ⟨x, z - x, ?_, ?_⟩
  · -- The second component of the graph decomposition is the required Euclidean subgradient.
    simpa [euclideanSubdifferentialAt] using hgraph.2
  · -- The first component of the graph decomposition is exactly the sum identity.
    exact hgraph.1

/-- Helper for Corollary 31.5.2: in a monotone graph, two points with the same sum `x + v`
must coincide. -/
lemma helperForCorollary_31_5_2_eq_of_monotone_points_with_same_sum {n : ℕ}
    (S : (Fin n → ℝ) → Set (Fin n → ℝ))
    (hSmono : IsMonotoneEuclideanSetValuedMap S)
    {x y u v : Fin n → ℝ}
    (hv : v ∈ S x)
    (hu : u ∈ S y)
    (hSum : x + v = y + u) :
    x = y ∧ v = u := by
  -- Monotonicity gives a nonnegative pairing for the two graph points.
  have hmono :
      0 ≤ dotProduct (x - y) (v - u) :=
    hSmono (x := x) (y := y) (u := v) (v := u) hv hu
  have hxy_sub : x - y = u - v := by
    -- The equal-sum hypothesis rewrites the difference of base points as the difference of the
    -- value components.
    ext i
    have hi := congrFun hSum i
    calc
      (x - y) i = x i - y i := by
        rfl
      _ = (x i + v i) - y i - v i := by
        ring
      _ = (y i + u i) - y i - v i := by
        exact congrArg (fun t : ℝ => t - y i - v i) hi
      _ = u i - v i := by
        ring
      _ = (u - v) i := by rfl
  have huv_neg : u - v = -(v - u) := by
    -- This is the coordinatewise antisymmetry of subtraction.
    ext i
    simp
  have hmono' :
      0 ≤ dotProduct (u - v) (v - u) := by
    -- Substituting the rewritten difference turns the monotonicity pairing into a negative norm
    -- square.
    simpa [hxy_sub] using hmono
  have hpair_eq :
      dotProduct (u - v) (v - u) = -(dotProduct (v - u) (v - u)) := by
    rw [huv_neg]
    unfold dotProduct
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    set t : ℝ := (v - u) i
    have hterm : (-t) * t = -(t * t) := by
      ring
    change (-t) * t = -((t * t))
    exact hterm
  have hpair_nonpos :
      dotProduct (v - u) (v - u) ≤ 0 := by
    linarith [hmono', hpair_eq]
  have hsq_zero : dotProduct (v - u) (v - u) = 0 := by
    have hsq_nonneg : 0 ≤ dotProduct (v - u) (v - u) :=
      dotProduct_self_nonneg (v := v - u)
    linarith [hsq_nonneg, hpair_nonpos]
  have hvu_sub : v - u = 0 :=
    dotProduct_self_eq_zero.mp hsq_zero
  have hvu : v = u :=
    sub_eq_zero.mp hvu_sub
  have hxy : x = y := by
    -- Once the value components agree, cancel them from the equal-sum identity.
    rw [hvu] at hSum
    exact add_right_cancel hSum
  exact ⟨hxy, hvu⟩

/-- Helper for Corollary 31.5.2: any monotone pointwise enlargement of the Euclideanized
subdifferential coincides with it pointwise. -/
lemma helperForCorollary_31_5_2_pointwise_maximality_of_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (S : (Fin n → ℝ) → Set (Fin n → ℝ))
    (hSmono : IsMonotoneEuclideanSetValuedMap S)
    (hSubset : ∀ x : Fin n → ℝ, euclideanSubdifferentialAt (n := n) f x ⊆ S x) :
    ∀ x : Fin n → ℝ, S x ⊆ euclideanSubdifferentialAt (n := n) f x := by
  intro x v hv
  -- Decompose the sum `x + v` through the canonical `Id + ∂f` surjectivity statement.
  rcases
      helperForCorollary_31_5_2_exists_sum_decomposition
        (n := n) f hf_closed hf_proper (x + v) with
    ⟨y, u, huSub, hsum⟩
  have huS : u ∈ S y :=
    hSubset y huSub
  -- Monotonicity of the enlargement forces the two decompositions of `x + v` to be identical.
  rcases
      helperForCorollary_31_5_2_eq_of_monotone_points_with_same_sum
        (n := n) S hSmono hv huS hsum with
    ⟨hxy, hvu⟩
  -- Transport the subdifferential membership back along the equalities.
  simpa [hxy, hvu] using huSub

-- Proof sketch: monotonicity of the subdifferential comes from the convex subgradient
-- inequalities. Maximality follows by Minty's criterion, using Theorem 31.5 and Corollary 31.5.1
-- to show that `Id + ∂f` is onto `ℝ^n`, so no larger monotone graph can strictly contain the
-- graph of `∂f`.
/-- Corollary 31.5.2: if `f : ℝ^n → ℝ ∪ {+∞}` is any closed proper convex function, then its
subdifferential mapping `∂ f`, formalized as `x ↦ euclideanSubdifferentialAt f x`, is a maximal
monotone mapping from `ℝ^n` to `ℝ^n`. -/
theorem subdifferential_is_maximal_monotone {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsMaximalMonotoneEuclideanSetValuedMap
      (fun x : Fin n → ℝ => euclideanSubdifferentialAt (n := n) f x) := by
  constructor
  · -- The subdifferential is monotone in the Euclidean dot-product form.
    exact
      helperForCorollary_31_5_2_subdifferential_monotone
        (n := n) f hf_proper
  · intro S hSmono hSubset
    -- Any monotone enlargement containing `∂f` pointwise collapses back to `∂f` by the Minty
    -- decomposition argument.
    exact
      helperForCorollary_31_5_2_pointwise_maximality_of_subdifferential
        (n := n) f hf_closed hf_proper S hSmono hSubset


end Section31
end Chap06
