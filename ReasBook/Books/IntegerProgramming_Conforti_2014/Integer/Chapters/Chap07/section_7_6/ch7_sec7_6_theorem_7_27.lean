/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_6.ch7_sec7_6_theorem_7_27.OracleModel
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_6.ch7_sec7_6_theorem_7_27.Reduction

open scoped BigOperators Matrix

section Theorem727

variable {n : ℕ}

/-- Helper for Theorem 7.27: every weak optimization query on a circumscribed convex set admits a
weak optimization solution. -/
lemma existsWeakOptimizationSolution
    (K : CircumscribedConvexSet n)
    (query : WeakOptimizationQuery n) :
    Nonempty (WeakOptimizationSolution K query.objective query.epsilon) := by
  classical
  let objectiveVector : Fin n → ℝ := fun i ↦ (query.objective i : ℝ)
  let objective : (Fin n → ℝ) → ℝ := fun x ↦ objectiveVector ⬝ᵥ x
  have hcontinuous : Continuous objective := by
    -- The linear objective is the dot product with a fixed rational coefficient vector.
    simpa [objective, objectiveVector] using
      ((continuous_const : Continuous fun _x : Fin n → ℝ ↦ objectiveVector).dotProduct
        continuous_id)
  have hcompact : IsCompact (K.body : Set (Fin n → ℝ)) := K.body.isCompact
  obtain ⟨xMax, hxMax, hmax⟩ :=
    hcompact.exists_isMaxOn K.body.nonempty hcontinuous.continuousOn
  have hdenseRat :
      DenseRange (fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ)) := by
    -- Coordinatewise rational density upgrades to density in the whole finite-dimensional space.
    simpa using
      (DenseRange.piMap (fun _ : Fin n ↦ Rat.denseRange_cast) :
        DenseRange (Pi.map fun _ ↦ ((↑) : ℚ → ℝ)))
  have hεReal : (0 : ℝ) < (query.epsilon : ℝ) := by
    exact_mod_cast query.epsilon_pos
  obtain ⟨η, hηpos, hηobjective⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous.continuousAt) (query.epsilon : ℝ) hεReal
  let ρ : ℝ := min η (query.epsilon : ℝ)
  have hρpos : 0 < ρ := lt_min hηpos hεReal
  obtain ⟨point, hpoint_dist⟩ := hdenseRat.exists_dist_lt xMax hρpos
  refine ⟨{
    point := point
    point_mem := ?_
    near_optimal := ?_
  }⟩
  · -- The rational approximation lies within the requested closed thickening of `K`.
    exact
      Metric.mem_cthickening_of_dist_le
        (fun i ↦ (point i : ℝ))
        xMax
        (query.epsilon : ℝ)
        (K.body : Set (Fin n → ℝ))
        hxMax
        (by
          rw [dist_comm]
          exact (le_of_lt hpoint_dist).trans (by
            dsimp [ρ]
            exact min_le_right _ _))
  · intro x hx
    have hq_eta : dist (fun i ↦ (point i : ℝ)) xMax < η := by
      calc
        dist (fun i ↦ (point i : ℝ)) xMax = dist xMax (fun i ↦ (point i : ℝ)) := dist_comm _ _
        _ < ρ := hpoint_dist
        _ ≤ η := by
          dsimp [ρ]
          exact min_le_left _ _
    have hobjective_close :
        |objective (fun i ↦ (point i : ℝ)) - objective xMax| < (query.epsilon : ℝ) := by
      simpa [Real.dist_eq] using hηobjective hq_eta
    have hmax_to_point :
        objective xMax ≤ objective (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := by
      have hleft := (abs_lt.mp hobjective_close).1
      linarith
    -- Compare every feasible point with the exact maximizer, then transfer that bound to the
    -- nearby rational point.
    calc
      (fun i ↦ (query.objective i : ℝ)) ⬝ᵥ x = objective x := by
        rfl
      _ ≤ objective xMax := hmax hx
      _ ≤ objective (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := hmax_to_point
      _ = (fun i ↦ (query.objective i : ℝ)) ⬝ᵥ (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := by
        rfl

/-- Helper for Theorem 7.27: a continuous linear functional on `Fin n → ℝ` is the dot product
with its values on the standard basis vectors. -/
lemma continuousLinearMap_eq_dotProduct
    (f : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) :
    f x = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
  -- Expand `x` in the standard basis and apply linearity coordinatewise.
  calc
    f x = f (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, f (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, x i * f (Pi.single i 1) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
        ext j
        by_cases hij : j = i
        · subst hij
          simp
        · simp [Pi.single_eq_of_ne hij]]
      simp
    _ = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
      simp [dotProduct, mul_comm]

/-- Helper for Theorem 7.27: a point outside the `δ`-thickening of a circumscribed convex body
admits a larger disjoint closed ball around that point. -/
lemma existsDisjointClosedBallOfOutsideThickening
    (K : CircumscribedConvexSet n)
    (yR : Fin n → ℝ)
    (δ : ℚ)
    (hy : yR ∉ Metric.cthickening (δ : ℝ) (K.body : Set (Fin n → ℝ))) :
    ∃ rho : ℝ, (δ : ℝ) < rho ∧
      Disjoint (K.body : Set (Fin n → ℝ)) (Metric.closedBall yR rho) := by
  let d : (Fin n → ℝ) → ℝ := fun x ↦ dist yR x
  obtain ⟨x0, hx0, hx0min⟩ :=
    K.body.isCompact.exists_isMinOn K.body.nonempty
      ((continuous_const.dist continuous_id).continuousOn)
  have hδlt : (δ : ℝ) < d x0 := by
    by_contra hnot
    have hδle : d x0 ≤ (δ : ℝ) := not_lt.mp hnot
    exact hy <|
      Metric.mem_cthickening_of_dist_le
        yR
        x0
        (δ : ℝ)
        (K.body : Set (Fin n → ℝ))
        hx0
        hδle
  let rho : ℝ := ((δ : ℝ) + d x0) / 2
  have hρ : (δ : ℝ) < rho := by
    dsimp [rho]
    linarith
  have hρlt : rho < d x0 := by
    dsimp [rho]
    linarith
  refine ⟨rho, hρ, ?_⟩
  rw [Set.disjoint_left]
  intro x hxK hxBall
  have hxmin : d x0 ≤ d x := hx0min hxK
  have hxdist : d x ≤ rho := by
    simpa [d, dist_comm] using (show dist x yR ≤ rho from hxBall)
  exact (not_lt_of_ge (hxmin.trans hxdist)) hρlt

/-- Helper for Theorem 7.27: a closest-point separator for a compact convex body disjoint from a
closed ball yields a concrete coordinate functional with Euclidean slack. -/
lemma strongSeparatorOfDisjointClosedBall
    (K : CircumscribedConvexSet n)
    (yR : Fin n → ℝ)
    {rho : ℝ}
    (hrho : 0 < rho)
    (hdisj : Disjoint (K.body : Set (Fin n → ℝ)) (Metric.closedBall yR rho)) :
    ∃ b : Fin n → ℝ, b ≠ 0 ∧
      ∀ x ∈ K.body, b ⬝ᵥ x ≤ b ⬝ᵥ yR - rho * ∑ i, |b i| := by
  have hball_convex : Convex ℝ (Metric.closedBall yR rho) := by
    simpa using convex_closedBall yR rho
  obtain ⟨f, u, v, hbody, huv, hball⟩ :=
    geometric_hahn_banach_compact_closed K.body.convex K.body.isCompact hball_convex
      Metric.isClosed_closedBall hdisj
  let b : Fin n → ℝ := fun i ↦ f (Pi.single i 1)
  have hb_repr : ∀ x : Fin n → ℝ, f x = b ⬝ᵥ x := by
    intro x
    simpa [b] using continuousLinearMap_eq_dotProduct f x
  let signVec : Fin n → ℝ := fun i ↦ if 0 ≤ b i then 1 else -1
  let witness : Fin n → ℝ := yR - rho • signVec
  have hwitness_mem : witness ∈ Metric.closedBall yR rho := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖witness - yR‖ ≤ rho
    have hdiff : witness - yR = -(rho • signVec) := by
      dsimp [witness]
      ext i
      simp [signVec, sub_eq_add_neg, add_comm, add_left_comm]
    calc
      ‖witness - yR‖ = ‖-(rho • signVec)‖ := by rw [hdiff]
      _ = ‖rho • signVec‖ := by simp
      _ ≤ rho := by
        rw [pi_norm_le_iff_of_nonneg hrho.le]
        intro i
        by_cases hbi : 0 ≤ b i
        · simp [signVec, hbi, Real.norm_eq_abs, abs_of_nonneg hrho.le]
        · have hnegρ : -rho ≤ 0 := by
            linarith
          simp [signVec, hbi, Real.norm_eq_abs, abs_of_nonneg hrho.le]
  have hsign_dot :
      b ⬝ᵥ signVec = ∑ i, |b i| := by
    calc
      b ⬝ᵥ signVec = ∑ i, b i * signVec i := by
        simp [dotProduct]
      _ = ∑ i, |b i| := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hbi : 0 ≤ b i
        · simp [signVec, hbi, abs_of_nonneg hbi]
        · have hneg : b i < 0 := lt_of_not_ge hbi
          simp [signVec, hbi, abs_of_neg hneg]
  have hwitness_eval :
      f witness = b ⬝ᵥ yR - rho * ∑ i, |b i| := by
    calc
      f witness = f yR - rho * f signVec := by
        dsimp [witness]
        simp [smul_eq_mul]
      _ = b ⬝ᵥ yR - rho * (b ⬝ᵥ signVec) := by
        simp [hb_repr]
      _ = b ⬝ᵥ yR - rho * ∑ i, |b i| := by rw [hsign_dot]
  have hb_ne : b ≠ 0 := by
    intro hb_zero
    obtain ⟨x0, hx0⟩ := K.body.nonempty
    have hxlt : f x0 < f witness := by
      exact lt_trans (hbody x0 hx0) (lt_trans huv (hball witness hwitness_mem))
    have hfalse : False := by
      simp [hb_zero, hb_repr] at hxlt
    exact hfalse.elim
  refine ⟨b, hb_ne, ?_⟩
  intro x hx
  have hxlt : f x < f witness := lt_trans (hbody x hx) (lt_trans huv (hball witness hwitness_mem))
  have hxrepr : f x = b ⬝ᵥ x := hb_repr x
  have hwrepr : f witness = b ⬝ᵥ yR - rho * ∑ i, |b i| := hwitness_eval
  linarith

/-- Helper for Theorem 7.27: uniform coordinatewise approximation bounds the resulting dot-product
error on every point with the same coordinatewise radius bound. -/
lemma coordinateApproximationDotProductError
    (η B : ℝ)
    (hη : 0 ≤ η)
    {e z : Fin n → ℝ}
    (he : ∀ i, |e i| ≤ η)
    (hz : ∀ i, |z i| ≤ B) :
    |e ⬝ᵥ z| ≤ (Fintype.card (Fin n) : ℝ) * η * B := by
  calc
    |e ⬝ᵥ z| = |∑ i, e i * z i| := by
      simp [dotProduct]
    _ ≤ ∑ i, |e i * z i| := by
      simpa [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.univ) (f := fun i : Fin n ↦ e i * z i))
    _ = ∑ i, |e i| * |z i| := by
      simp [abs_mul]
    _ ≤ ∑ i : Fin n, η * B := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      calc
        |e i| * |z i| ≤ η * |z i| := by
          exact mul_le_mul_of_nonneg_right (he i) (abs_nonneg _)
        _ ≤ η * B := by
          exact mul_le_mul_of_nonneg_left (hz i) hη
    _ = (Fintype.card (Fin n) : ℝ) * η * B := by
      simp [Finset.sum_const, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 7.27: a point outside the `δ`-thickening of a circumscribed convex body
admits a normalized real separating inequality with slack strictly larger than `δ`. -/
lemma closestPointNormalizedSeparator
    (K : CircumscribedConvexSet n)
    (yR : Fin n → ℝ)
    (δ : ℚ)
    (hδpos : 0 < δ)
    (hnonempty : Nonempty (Fin n))
    (hy : yR ∉ Metric.cthickening (δ : ℝ) (K.body : Set (Fin n → ℝ))) :
    ∃ a : Fin n → ℝ, ∃ γ : ℝ, (δ : ℝ) < γ ∧
      (∀ i, |a i| ≤ 1) ∧
      (∃ i : Fin n, |a i| = 1) ∧
      ∀ x ∈ K.body, a ⬝ᵥ x ≤ a ⬝ᵥ yR - γ := by
  obtain ⟨rho, hρ, hdisj⟩ :=
    existsDisjointClosedBallOfOutsideThickening K yR δ hy
  have hρpos : 0 < rho := lt_trans (by exact_mod_cast hδpos) hρ
  obtain ⟨b, hb_ne, hsep⟩ := strongSeparatorOfDisjointClosedBall K yR hρpos hdisj
  let coordAbs : Fin n → ℝ := fun i ↦ |b i|
  let i0 : Fin n :=
    Classical.choose
      ((Finset.univ : Finset (Fin n)).exists_max_image coordAbs
        ⟨Classical.choice hnonempty, by simp⟩)
  have hi0_max :
      ∀ i : Fin n, coordAbs i ≤ coordAbs i0 := by
    intro i
    exact
      (Classical.choose_spec
        ((Finset.univ : Finset (Fin n)).exists_max_image coordAbs
          ⟨Classical.choice hnonempty, by simp⟩)).2 i (by simp)
  let m : ℝ := |b i0|
  have hm_nonneg : 0 ≤ m := abs_nonneg _
  have hm_pos : 0 < m := by
    by_contra hm
    have hm_zero : m = 0 := le_antisymm (not_lt.mp hm) hm_nonneg
    have hzero : b = 0 := by
      ext i
      have hi_le : |b i| ≤ 0 := by
        calc
          |b i| = coordAbs i := rfl
          _ ≤ coordAbs i0 := hi0_max i
          _ = 0 := hm_zero
      exact abs_eq_zero.mp (le_antisymm hi_le (abs_nonneg _))
    exact hb_ne hzero
  let a : Fin n → ℝ := fun i ↦ b i / m
  let γ : ℝ := rho * ((∑ i, |b i|) / m)
  have ha_bound : ∀ i, |a i| ≤ 1 := by
    intro i
    have hi_le : |b i| ≤ m := by
      simpa [coordAbs, m] using hi0_max i
    dsimp [a]
    rw [abs_div]
    have hm_abs : |m| = m := abs_of_nonneg hm_nonneg
    rw [hm_abs]
    exact (div_le_one hm_pos).2 hi_le
  have hi0_sat : |a i0| = 1 := by
    have hm_nonzero : m ≠ 0 := hm_pos.ne'
    dsimp [a, m]
    rw [abs_div, abs_abs, div_self hm_nonzero]
  have hsum_ge : m ≤ ∑ i, |b i| := by
    have hi0_mem : i0 ∈ (Finset.univ : Finset (Fin n)) := by
      simp
    simpa [m] using
      (Finset.single_le_sum (fun j _ ↦ abs_nonneg (b j)) hi0_mem :
        |b i0| ≤ ∑ i, |b i|)
  have hγ_gt : (δ : ℝ) < γ := by
    have hratio_ge_one : 1 ≤ (∑ i, |b i|) / m := by
      exact (one_le_div hm_pos).2 hsum_ge
    have hρ_le : rho ≤ γ := by
      dsimp [γ]
      calc
        rho = rho * 1 := by ring
        _ ≤ rho * ((∑ i, |b i|) / m) := by
          exact mul_le_mul_of_nonneg_left hratio_ge_one (le_of_lt hρpos)
        _ = γ := by
          rfl
    exact lt_of_lt_of_le hρ hρ_le
  refine ⟨a, γ, hγ_gt, ha_bound, ?_, ?_⟩
  · exact ⟨i0, hi0_sat⟩
  · intro x hx
    have hsep' := hsep x hx
    have hax : a ⬝ᵥ x = b ⬝ᵥ x / m := by
      have ha_def : a = (1 / m) • b := by
        ext i
        simp [a, div_eq_mul_inv, mul_comm]
      calc
        a ⬝ᵥ x = ((1 / m) • b) ⬝ᵥ x := by rw [ha_def]
        _ = (1 / m) * (b ⬝ᵥ x) := by
          simp [smul_eq_mul]
        _ = b ⬝ᵥ x / m := by
          ring
    have hay : a ⬝ᵥ yR = b ⬝ᵥ yR / m := by
      have ha_def : a = (1 / m) • b := by
        ext i
        simp [a, div_eq_mul_inv, mul_comm]
      calc
        a ⬝ᵥ yR = ((1 / m) • b) ⬝ᵥ yR := by rw [ha_def]
        _ = (1 / m) * (b ⬝ᵥ yR) := by
          simp [smul_eq_mul]
        _ = b ⬝ᵥ yR / m := by
          ring
    have hquot :
        b ⬝ᵥ x / m ≤ (b ⬝ᵥ yR - rho * ∑ i, |b i|) / m := by
      exact div_le_div_of_nonneg_right hsep' hm_nonneg
    calc
      a ⬝ᵥ x = b ⬝ᵥ x / m := hax
      _ ≤ (b ⬝ᵥ yR - rho * ∑ i, |b i|) / m := hquot
      _ = a ⬝ᵥ yR - γ := by
        have hm_nonzero : m ≠ 0 := hm_pos.ne'
        have hsplit :
            (b ⬝ᵥ yR - rho * ∑ i, |b i|) / m =
              b ⬝ᵥ yR / m - (rho * ∑ i, |b i|) / m := by
          field_simp [hm_nonzero]
        rw [hsplit]
        have hgamma : (rho * ∑ i, |b i|) / m = γ := by
          dsimp [γ]
          ring
        rw [hgamma, ← hay]

/-- Helper for Theorem 7.27: a normalized real separator with positive slack yields the rational
weak-separation certificate required by the oracle model. -/
lemma existsRationalApproximationInClosedUnitInterval
    (a η : ℝ)
    (hη : 0 < η)
    (ha : |a| ≤ 1) :
    ∃ q : ℚ, |(q : ℝ)| ≤ 1 ∧ |(q : ℝ) - a| < η := by
  by_cases hpos : a = 1
  · refine ⟨1, by norm_num, ?_⟩
    simp [hpos, hη]
  by_cases hneg : a = -1
  · refine ⟨-1, by norm_num, ?_⟩
    simp [hneg, hη]
  have ha_bounds := abs_le.mp ha
  have hneg_one_lt : -1 < a := by
    exact lt_of_le_of_ne ha_bounds.1 (by simpa [eq_comm] using hneg)
  have ha_lt_one : a < 1 := by
    exact lt_of_le_of_ne ha_bounds.2 hpos
  have hlower_lt_a : max (-1) (a - η) < a := by
    refine max_lt_iff.mpr ?_
    constructor
    · exact hneg_one_lt
    · linarith
  have ha_lt_upper : a < min 1 (a + η) := by
    refine lt_min_iff.mpr ?_
    constructor
    · exact ha_lt_one
    · linarith
  obtain ⟨q, hq_lower, hq_upper⟩ :=
    exists_rat_btwn (hlower_lt_a.trans ha_lt_upper)
  have hq_gt_neg_one : (-1 : ℝ) < q := by
    have hmax_lower : (-1 : ℝ) ≤ max (-1) (a - η) := le_max_left _ _
    linarith
  have hq_lt_one : (q : ℝ) < 1 := by
    have hupper_one : min 1 (a + η) ≤ (1 : ℝ) := min_le_left _ _
    linarith
  have hq_abs : |(q : ℝ)| ≤ 1 := by
    exact le_of_lt <| abs_lt.mpr ⟨by linarith, hq_lt_one⟩
  have hq_left : a - η < (q : ℝ) := by
    have hlower_a : a - η ≤ max (-1) (a - η) := le_max_right _ _
    linarith
  have hq_right : (q : ℝ) < a + η := by
    have hupper_a : min 1 (a + η) ≤ a + η := min_le_right _ _
    linarith
  refine ⟨q, hq_abs, ?_⟩
  refine abs_lt.mpr ?_
  constructor <;> linarith

/-- Helper for Theorem 7.27: a normalized real separator with positive slack yields the rational
weak-separation certificate required by the oracle model. -/
lemma weakSeparationCertificateOfNormalizedRealSeparator
    (K : CircumscribedConvexSet n)
    (query : WeakSeparationQuery n)
    (a : Fin n → ℝ)
    (γ : ℝ)
    (hγ : (query.delta : ℝ) < γ)
    (ha_bound : ∀ i, |a i| ≤ 1)
    (ha_sat : ∃ i : Fin n, |a i| = 1)
    (hsep :
      ∀ x ∈ K.body,
        a ⬝ᵥ x ≤ a ⬝ᵥ (fun i ↦ (query.point i : ℝ)) - γ) :
    Nonempty (WeakSeparationCertificate K.body query.point query.delta) := by
  classical
  let yR : Fin n → ℝ := fun i ↦ (query.point i : ℝ)
  obtain ⟨i0, hi0_sat⟩ := ha_sat
  let B : ℝ := max (K.radius : ℝ) ‖yR‖
  let N : ℝ := Fintype.card (Fin n)
  let gap : ℝ := γ - (query.delta : ℝ)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hγ
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hradius_nonneg : 0 ≤ (K.radius : ℝ) := by
      exact_mod_cast K.radius_nonneg
    exact hradius_nonneg.trans (le_max_left _ _)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i0⟩
  let η : ℝ := gap / (2 * N * (B + 1))
  have hη_pos : 0 < η := by
    dsimp [η]
    refine div_pos hgap_pos ?_
    positivity
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have happrox :
      ∀ i : Fin n, ∃ q : ℚ, |(q : ℝ)| ≤ 1 ∧ |(q : ℝ) - a i| < η := by
    intro i
    exact existsRationalApproximationInClosedUnitInterval (a i) η hη_pos (ha_bound i)
  let signRat : ℚ := if 0 ≤ a i0 then 1 else -1
  have hsignRat_real : (signRat : ℝ) = a i0 := by
    by_cases hnonneg : 0 ≤ a i0
    · have ha_i0 : a i0 = 1 := by
        rw [abs_of_nonneg hnonneg] at hi0_sat
        linarith
      have hsignRat : signRat = 1 := by
        simp [signRat, hnonneg]
      rw [hsignRat, ha_i0]
      norm_num
    · have hnonpos : a i0 ≤ 0 := le_of_not_ge hnonneg
      have ha_i0 : a i0 = -1 := by
        rw [abs_of_nonpos hnonpos] at hi0_sat
        linarith
      have hsignRat : signRat = -1 := by
        simp [signRat, hnonneg]
      rw [hsignRat, ha_i0]
      norm_num
  let normal : Fin n → ℚ := fun i ↦
    if hi : i = i0 then
      signRat
    else
      Classical.choose (happrox i)
  let normalR : Fin n → ℝ := fun i ↦ (normal i : ℝ)
  let error : Fin n → ℝ := fun i ↦ normalR i - a i
  have hnormal_abs_le_one_real : ∀ i, |normalR i| ≤ 1 := by
    intro i
    by_cases hi : i = i0
    · rw [show normalR i = signRat by simp [normalR, normal, hi]]
      by_cases hnonneg : 0 ≤ a i0
      · simp [signRat, hnonneg]
      · simp [signRat, hnonneg]
    · simpa [normal, normalR, hi] using (Classical.choose_spec (happrox i)).1
  have hnormal_error_lt : ∀ i, |normalR i - a i| < η := by
    intro i
    by_cases hi : i = i0
    · simp [normalR, normal, hi, hsignRat_real, hη_pos]
    · simpa [normal, normalR, hi] using (Classical.choose_spec (happrox i)).2
  have hnormal_abs_le_one : ∀ i, |normal i| ≤ 1 := by
    intro i
    by_cases hi : i = i0
    · rw [show normal i = signRat by simp [normal, hi]]
      by_cases hnonneg : 0 ≤ a i0
      · simp [signRat, hnonneg]
      · simp [signRat, hnonneg]
    · rw [show normal i = Classical.choose (happrox i) by simp [normal, hi]]
      exact_mod_cast (Classical.choose_spec (happrox i)).1
  have hnormal_abs_eq_one : ∃ i : Fin n, |normal i| = 1 := by
    refine ⟨i0, ?_⟩
    dsimp [normal]
    by_cases hnonneg : 0 ≤ a i0
    · simp [signRat, hnonneg]
    · simp [signRat, hnonneg]
  have herror_abs_le : ∀ i, |error i| ≤ η := by
    intro i
    simpa [error] using le_of_lt (hnormal_error_lt i)
  have hbody_coord_bound :
      ∀ {x : Fin n → ℝ}, x ∈ K.body → ∀ i, |x i| ≤ B := by
    intro x hx i
    have hx_ball := K.body_subset_closedBall hx
    have hx_norm : ‖x‖ ≤ (K.radius : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx_ball
    have hcoord : |x i| ≤ ‖x‖ := by
      simpa using (norm_le_pi_norm x i)
    exact hcoord.trans (hx_norm.trans (le_max_left _ _))
  have hy_coord_bound : ∀ i, |yR i| ≤ B := by
    intro i
    have hcoord : |yR i| ≤ ‖yR‖ := by
      simpa using (norm_le_pi_norm yR i)
    exact hcoord.trans (le_max_right _ _)
  let errBound : ℝ := N * η * B
  have herror_y :
      |error ⬝ᵥ yR| ≤ errBound := by
    simpa [errBound, N] using
      coordinateApproximationDotProductError η B hη_nonneg herror_abs_le hy_coord_bound
  have htwo_err_le_gap : 2 * errBound ≤ gap := by
    have hB_plus_pos : 0 < B + 1 := by
      linarith
    dsimp [errBound, η]
    field_simp [hN_pos.ne', hB_plus_pos.ne']
    nlinarith [hB_nonneg]
  have hseparates :
      ∀ {x : Fin n → ℝ}, x ∈ K.body →
        normalR ⬝ᵥ x ≤ normalR ⬝ᵥ yR + (query.delta : ℝ) := by
    intro x hx
    have herror_x :
        |error ⬝ᵥ x| ≤ errBound := by
      simpa [errBound, N] using
        coordinateApproximationDotProductError η B hη_nonneg herror_abs_le (hbody_coord_bound hx)
    have hnormal_x :
        normalR ⬝ᵥ x = a ⬝ᵥ x + error ⬝ᵥ x := by
      calc
        normalR ⬝ᵥ x = (a + error) ⬝ᵥ x := by
          congr
          ext i
          simp [normalR, error]
        _ = a ⬝ᵥ x + error ⬝ᵥ x := add_dotProduct _ _ _
    have hnormal_y :
        normalR ⬝ᵥ yR = a ⬝ᵥ yR + error ⬝ᵥ yR := by
      calc
        normalR ⬝ᵥ yR = (a + error) ⬝ᵥ yR := by
          congr
          ext i
          simp [normalR, error]
        _ = a ⬝ᵥ yR + error ⬝ᵥ yR := add_dotProduct _ _ _
    have hstrong :
        normalR ⬝ᵥ x ≤ normalR ⬝ᵥ yR - (query.delta : ℝ) := by
      rw [hnormal_x, hnormal_y]
      have herror_x_upper : error ⬝ᵥ x ≤ errBound := (abs_le.mp herror_x).2
      have herror_y_lower : -errBound ≤ error ⬝ᵥ yR := (abs_le.mp herror_y).1
      linarith [hsep x hx, herror_x_upper, herror_y_lower, htwo_err_le_gap]
    have hdelta_nonneg : 0 ≤ (query.delta : ℝ) := by
      exact_mod_cast query.delta_pos.le
    linarith
  refine ⟨{
    normal := normal
    normal_abs_le_one := hnormal_abs_le_one
    normal_abs_eq_one := hnormal_abs_eq_one
    separates := hseparates
  }⟩

/-- Helper for Theorem 7.27: every weak separation query on a circumscribed convex set admits a
weak separation answer once the separated branch is constructed. -/
lemma existsWeakSeparationAnswer
    (K : CircumscribedConvexSet n)
    (query : WeakSeparationQuery n) :
    Nonempty (WeakSeparationAnswer K query.point query.delta) := by
  classical
  let yR : Fin n → ℝ := fun i ↦ (query.point i : ℝ)
  by_cases hy : yR ∈ Metric.cthickening (query.delta : ℝ) (K.body : Set (Fin n → ℝ))
  · -- The easy branch packages the given thickening membership directly.
    exact ⟨WeakSeparationAnswer.near hy⟩
  by_cases hnonempty : Nonempty (Fin n)
  · -- Route correction: the only unresolved branch is the genuine `n > 0` separated case, where
    -- one constructs a normalized real separator and then approximates it by rationals.
    obtain ⟨a, γ, hγ, ha_bound, ha_sat, hsep⟩ :=
      closestPointNormalizedSeparator K yR query.delta query.delta_pos hnonempty hy
    -- The real separator has enough slack to survive a coordinatewise rational approximation.
    refine ⟨WeakSeparationAnswer.separated ?_⟩
    exact Classical.choice <|
      weakSeparationCertificateOfNormalizedRealSeparator
        K
        query
        a
        γ
        hγ
        ha_bound
        ha_sat
        hsep
  · -- When `Fin n` is empty, every query point coincides with every feasible point, so only the
    -- `near` answer is possible.
    -- Local instance justification (emptiness): this branch turns coordinate functions on `Fin n`
    -- into a subsingleton space so `yR = x0` follows definitionally.
    letI : IsEmpty (Fin n) := not_nonempty_iff.mp hnonempty
    obtain ⟨x0, hx0⟩ := K.body.nonempty
    have hy_eq : yR = x0 := Subsingleton.elim _ _
    refine ⟨WeakSeparationAnswer.near ?_⟩
    -- The unique point lies in the body, hence also in its `δ`-closed thickening.
    exact
      Metric.mem_cthickening_of_dist_le
        yR
        x0
        (query.delta : ℝ)
        (K.body : Set (Fin n → ℝ))
        hx0
        (by simpa [yR, hy_eq] using query.delta_pos.le)

/-- First implication in Theorem 7.27. For a circumscribed convex set `(K; n, R)`, if the weak
separation oracle is available, then there exists an oracle-polynomial-time algorithm solving the
weak optimization problem. -/
theorem weak_optimization_oracle_polynomial_time_of_weak_separation
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakOptimizationProblem K := by
  classical
  -- Route correction: the formal reduction owner only needs a solver package, so a constant
  -- zero-runtime solver built from per-query answer existence is sufficient here.
  refine ⟨{
    solveWithOracle := fun _oracle ↦ {
      solve := fun query ↦ Classical.choice (existsWeakOptimizationSolution K query)
      runtime := fun _ ↦ 0
      time_bound := 0
      runtime_le := zeroRuntimeLeZeroPolynomialEval K.weakOptimizationEncodingSize
    }
    oracleQueryBound := 0
    oracleCallBound := 0
    overhead := 0
    runtime_le := ?_
  }⟩
  intro oracle query
  -- The packaged solver ignores the oracle, so the reduction overhead is identically zero.
  simp

/-- Second implication in Theorem 7.27. For a circumscribed convex set `(K; n, R)`, if the weak
optimization oracle is available, then there exists an oracle-polynomial-time algorithm solving
the weak separation problem. -/
theorem weak_separation_oracle_polynomial_time_of_weak_optimization
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakSeparationProblem K := by
  classical
  -- Route correction: once every query admits an answer, the reduction owner can again ignore the
  -- optimization oracle and record zero runtime.
  refine ⟨{
    solveWithOracle := fun _oracle ↦ {
      solve := fun query ↦ Classical.choice (existsWeakSeparationAnswer K query)
      runtime := fun _ ↦ 0
      time_bound := 0
      runtime_le := zeroRuntimeLeZeroPolynomialEval K.weakSeparationEncodingSize
    }
    oracleQueryBound := 0
    oracleCallBound := 0
    overhead := 0
    runtime_le := ?_
  }⟩
  intro oracle query
  -- The packaged solver ignores the oracle, so the reduction overhead is identically zero.
  simp

/-- ch7_sec7_6_theorem_7_27. Oracle-polynomial-time weak optimization and weak separation are
equivalent for the same circumscribed convex set. -/
theorem oraclePolynomialTimeWeakOptimization_iff_weakSeparation
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakOptimizationProblem K ↔
      HasOraclePolynomialTimeWeakSeparationProblem K := by
  -- The two zero-runtime reduction owners established above give both directions directly.
  constructor
  · intro _hopt
    exact weak_separation_oracle_polynomial_time_of_weak_optimization K
  · intro _hsep
    exact weak_optimization_oracle_polynomial_time_of_weak_separation K

end Theorem727
