/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProximalSubgradient
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitEnergy
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphLimits
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle.Causal

/-- The regularized objective at a proximal point has a finite real value;
the interface is used by `ADMM.leftImage_tendsto` to expose the finite terms
needed by a storage estimate. -/
private theorem proximalValue_isReal {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {z x : Fin n → ℝ} (hx : IsProxPoint φ z x) :
    ∃ r : ℝ,
      φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) = r := by
  -- The finite-value component is exactly the first projection of the
  -- proximal characterization.
  exact (isProxPoint_iff.mp hx).imp fun r h ↦ h.1

/-- Helper for ADMM.leftImage_tendsto: the objective itself has a finite real
value at every proximal point. -/
private theorem proximalObjective_isReal {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {z x : Fin n → ℝ} (hx : IsProxPoint φ z x) :
    ∃ r : ℝ, φ x = r := by
  -- First expose the finite regularized value supplied by proximality.
  obtain ⟨s, hs⟩ := proximalValue_isReal hx
  let q := dotProduct (x - z) (x - z) / 2
  -- Subtracting the finite quadratic term leaves a finite objective value.
  refine ⟨s - q, ?_⟩
  have hs' : φ x + (q : EReal) = (s : EReal) := by
    simpa only [q] using hs
  have hcancel := congrArg (fun a : EReal ↦ a - (q : EReal)) hs'
  simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using hcancel

/-- Convexity bounds an extended-real objective on a segment joining two
points where the objective is finite. -/
private lemma convexObjective_segmentBound {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {x y : Fin n → ℝ} (hx_top : φ x ≠ ⊤) (hy_top : φ y ≠ ⊤)
    {t : ℝ} (ht_zero : 0 ≤ t) (ht_one : t ≤ 1) :
    φ ((1 - t) • x + t • y) ≤
      (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) := by
  -- Realize both finite values as points of the closed convex epigraph.
  have hx : (x, (φ x).toReal) ∈
      {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hx_top (hφ.ne_bot x), le_refl]
  have hy : (y, (φ y).toReal) ∈
      {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hy_top (hφ.ne_bot y), le_refl]
  have hweights : 1 - t + t = 1 := by
    ring
  have hconvex := hφ.epigraph_convex hx hy (sub_nonneg.mpr ht_one) ht_zero hweights
  -- Project the epigraph segment inequality to its objective coordinate.
  simpa only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_mk,
    smul_eq_mul, one_mul, EReal.coe_toReal hx_top (hφ.ne_bot x),
    EReal.coe_toReal hy_top (hφ.ne_bot y)] using hconvex

/-- Proximal minimality for a closed proper convex objective yields the real
support inequality at every finite comparison point. -/
private lemma proximalPoint_supportingInequality {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {center x y : Fin n → ℝ} (hx : IsProxPoint φ center x)
    (hy_top : φ y ≠ ⊤) :
    (φ x).toReal - (φ y).toReal ≤
      dotProduct (center - x) (x - y) := by
  obtain ⟨r, hxvalue, hxmin⟩ := isProxPoint_iff.mp hx
  obtain ⟨cx, hφx⟩ := proximalObjective_isReal hx
  have hx_top : φ x ≠ ⊤ := by
    rw [hφx]
    exact EReal.coe_ne_top cx
  -- Compare the minimizer with points that approach it along the segment to `y`.
  have hbound : ∀ k : ℕ,
      (φ x).toReal - (φ y).toReal ≤
        dotProduct (center - x) (x - y) +
          (1 / ((k : ℝ) + 1)) * (dotProduct (y - x) (y - x) / 2) := by
    intro k
    let t : ℝ := 1 / ((k : ℝ) + 1)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have ht_one : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one]
      · norm_num
      · positivity
    let q : Fin n → ℝ := (1 - t) • x + t • y
    have hsegment : φ q ≤
        (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) := by
      exact convexObjective_segmentBound hφ hx_top hy_top ht_pos.le ht_one
    have hereal := (hxmin q).trans (add_le_add_left hsegment _)
    have hreal :
        (φ x).toReal + dotProduct (x - center) (x - center) / 2 ≤
          ((1 - t) * (φ x).toReal + t * (φ y).toReal) +
            dotProduct (q - center) (q - center) / 2 := by
      have hereal' :
          ((φ x).toReal : EReal) +
              ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) ≤
            (((1 - t) * (φ x).toReal + t * (φ y).toReal : ℝ) : EReal) +
              ((dotProduct (q - center) (q - center) / 2 : ℝ) : EReal) := by
        calc
          ((φ x).toReal : EReal) +
                ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) =
              φ x + ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) := by
                rw [EReal.coe_toReal hx_top (hφ.ne_bot x)]
          _ ≤ _ := hereal
      apply EReal.coe_le_coe_iff.mp
      simpa only [← EReal.coe_add] using hereal'
    have hq_sub : q - center = (x - center) + t • (y - x) := by
      dsimp [q]
      module
    have hlinear :
        dotProduct (x - center) (y - x) =
          dotProduct (center - x) (x - y) := by
      simp only [sub_dotProduct, dotProduct_sub]
      ring
    have hquadratic :
        dotProduct (q - center) (q - center) / 2 =
          dotProduct (x - center) (x - center) / 2 +
            t * dotProduct (center - x) (x - y) +
              t ^ 2 * (dotProduct (y - x) (y - x) / 2) := by
      rw [hq_sub]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (y - x) (x - center)]
      nlinarith [hlinear]
    rw [hquadratic] at hreal
    dsimp [t] at hreal ⊢
    nlinarith
  -- Let the quadratic segment remainder tend to zero.
  have htendsto : Filter.Tendsto
      (fun k : ℕ ↦ dotProduct (center - x) (x - y) +
        (1 / ((k : ℝ) + 1)) * (dotProduct (y - x) (y - x) / 2))
      Filter.atTop (nhds (dotProduct (center - x) (x - y))) := by
    have hconst : Filter.Tendsto
        (fun _ : ℕ ↦ dotProduct (center - x) (x - y)) Filter.atTop
        (nhds (dotProduct (center - x) (x - y))) := tendsto_const_nhds
    simpa only [zero_mul, add_zero] using
      hconst.add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const
        (dotProduct (y - x) (y - x) / 2))
  exact ge_of_tendsto' htendsto hbound

/-- A proximal point of a closed proper convex objective has subgradient equal
to its center minus the proximal point. -/
theorem subgradient_of_proxPoint {n : ℕ}
    {φ : (Fin n → ℝ) → EReal} (hφ : IsClosedProperConvex φ)
    {center x : Fin n → ℝ} (hx : IsProxPoint φ center x) :
    IsSubgradientAt φ (center - x) x := by
  obtain ⟨c, hφx⟩ := proximalObjective_isReal hx
  refine ⟨c, hφx, ?_⟩
  intro y
  by_cases hy_top : φ y = ⊤
  · rw [hy_top]
    exact le_top
  · have hsupport := proximalPoint_supportingInequality hφ hx hy_top
    have hx_toReal : (φ x).toReal = c := by
      rw [hφx]
      exact EReal.toReal_coe c
    have hy_value : φ y = ((φ y).toReal : EReal) := by
      exact (EReal.coe_toReal hy_top (hφ.ne_bot y)).symm
    have hreverse : x - y = -(y - x) := by
      ext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [hφx, hy_value, ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [hx_toReal, hreverse, dotProduct_neg] at hsupport
    linarith

/-- A fixed choice of the unique proximal point of a closed proper convex
objective. This reuses the original project's existence theorem. -/
noncomputable def proximalMap {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin m → ℝ) : Fin m → ℝ :=
  (existsUnique_isProxPoint hφ z).exists.choose

theorem proximalMap_spec {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin m → ℝ) :
    IsProxPoint φ z (proximalMap hφ z) :=
  (existsUnique_isProxPoint hφ z).exists.choose_spec

theorem proximalMap_subgradient {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin m → ℝ) :
    IsSubgradientAt φ (z - proximalMap hφ z) (proximalMap hφ z) :=
  subgradient_of_proxPoint hφ (proximalMap_spec hφ z)

/-- The selected proximal map agrees with every supplied graph point. -/
theorem proximalMap_eq_of_subgradient {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) {z x : Fin m → ℝ}
    (hx : IsSubgradientAt φ (z - x) x) : proximalMap hφ z = x :=
  (existsUnique_isProxPoint hφ z).unique (proximalMap_spec hφ z)
    (isProxPoint_of_subgradient hx)

/-- A zero graph point makes the proximal map fix zero. -/
theorem proximalMap_zero {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (hzero : IsSubgradientAt φ 0 0) :
    proximalMap hφ 0 = 0 :=
  proximalMap_eq_of_subgradient hφ (by simpa using hzero)

/-- Firm nonexpansiveness in the manuscript's coordinate dot product. -/
theorem proximalMap_firm {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z w : Fin m → ℝ) :
    dotProduct (proximalMap hφ z - proximalMap hφ w)
        (proximalMap hφ z - proximalMap hφ w) ≤
      dotProduct (z - w) (proximalMap hφ z - proximalMap hφ w) := by
  have h := ADMM.ConvergenceProof.subgradient_monotone
    (proximalMap_subgradient hφ z) (proximalMap_subgradient hφ w)
  simp only [sub_dotProduct, dotProduct_sub] at h ⊢
  linarith

/-- Firm nonexpansiveness implies the usual squared-distance bound without
changing from coordinate dot products to an unrelated product norm. -/
theorem proximalMap_square_nonexpansive {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z w : Fin m → ℝ) :
    ADMM.ConvergenceProof.coordinateSquare (proximalMap hφ z - proximalMap hφ w) ≤
      ADMM.ConvergenceProof.coordinateSquare (z - w) := by
  let a := z - w
  let b := proximalMap hφ z - proximalMap hφ w
  have hb : 0 ≤ dotProduct b b :=
    Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (b i))
  have hfirm : dotProduct b b ≤ dotProduct a b := proximalMap_firm hφ z w
  have hcs : dotProduct a b ^ 2 ≤ dotProduct a a * dotProduct b b := by
    simpa only [dotProduct, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  change dotProduct b b ≤ dotProduct a a
  by_cases hb0 : dotProduct b b = 0
  · rw [hb0]
    exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (a i))
  · have hbp : 0 < dotProduct b b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_contra h
    have hdiff : 0 < dotProduct b b - dotProduct a a := sub_pos.mpr (lt_of_not_ge h)
    nlinarith [mul_pos hbp hdiff]

/-- Euclidean norm form of the same proximal nonexpansiveness estimate. -/
theorem proximalMap_euclidean_nonexpansive {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z w : Fin m → ℝ) :
    ‖(WithLp.toLp 2 (proximalMap hφ z - proximalMap hφ w) : EuclideanSpace ℝ (Fin m))‖ ≤
      ‖(WithLp.toLp 2 (z - w) : EuclideanSpace ℝ (Fin m))‖ := by
  have h := proximalMap_square_nonexpansive hφ z w
  have hs (x : Fin m → ℝ) :
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ ^ 2 = dotProduct x x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, pow_two]
  unfold ADMM.ConvergenceProof.coordinateSquare at h
  rw [← hs _, ← hs _] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 (proximalMap hφ z - proximalMap hφ w) :
    EuclideanSpace ℝ (Fin m)), norm_nonneg (WithLp.toLp 2 (z - w) :
    EuclideanSpace ℝ (Fin m))]

end ADMM.UnitCircle.Causal
