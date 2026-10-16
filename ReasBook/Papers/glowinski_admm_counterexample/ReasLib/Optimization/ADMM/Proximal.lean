module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Problem
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

namespace ADMM

/-- `x` is a proximal point of `φ` with center `z`, expressed as finite
attainment of the quadratically regularized objective. -/
def IsProxPoint {n : ℕ} (φ : (Fin n → ℝ) → EReal)
    (z x : Fin n → ℝ) : Prop :=
  IsFiniteMinimizer
    (fun y ↦ φ y + ((dotProduct (y - z) (y - z) / 2 : ℝ) : EReal)) x

/-- A point is proximal exactly when the regularized objective is finite there
and no larger there than at any other point. -/
theorem isProxPoint_iff {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {z x : Fin n → ℝ} :
    IsProxPoint φ z x ↔
      ∃ r : ℝ,
        φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) = r ∧
        ∀ y, φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≤
          φ y + ((dotProduct (y - z) (y - z) / 2 : ℝ) : EReal) := by
  rfl

/-- A closed proper convex extended-real function is lower semicontinuous. -/
private lemma lowerSemicontinuous_of_closedProperConvex {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → EReal}
    (hf : IsClosedProperConvex f) : LowerSemicontinuous f := by
  -- Reduce lower semicontinuity to closedness of every extended-real sublevel.
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  induction a using EReal.rec with
  | bot =>
      -- Properness makes the bottom sublevel empty.
      have hempty : f ⁻¹' Set.Iic (⊥ : EReal) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false]
        exact iff_false_intro (hf.ne_bot x)
      rw [hempty]
      exact isClosed_empty
  | coe a =>
      -- A finite sublevel is a continuous horizontal slice of the closed epigraph.
      have hpreimage :
          f ⁻¹' Set.Iic (a : EReal) =
            (fun x : X ↦ (x, a)) ⁻¹' {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext x
        rfl
      rw [hpreimage]
      exact hf.epigraph_closed.preimage (continuous_id.prodMk continuous_const)
  | top =>
      -- The top sublevel is the whole space.
      simp

/-- A closed proper convex extended-real function has a continuous affine minorant. -/
private lemma exists_continuousAffineMinorant_of_closedProperConvex {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → EReal}
    (hf : IsClosedProperConvex f) :
    ∃ l : X →L[ℝ] ℝ, ∃ c : ℝ, ∀ x, ((l x + c : ℝ) : EReal) ≤ f x := by
  classical
  -- Choose a finite epigraph point and separate the point one unit below it.
  obtain ⟨x₀, hx₀_top⟩ := hf.exists_ne_top
  let r₀ := (f x₀).toReal
  have hx₀_coe : (r₀ : EReal) = f x₀ := EReal.coe_toReal hx₀_top (hf.ne_bot x₀)
  have hbelow : (x₀, r₀ - 1) ∉ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq]
    rw [← hx₀_coe, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨L, u, hLu, hsep⟩ :=
    geometric_hahn_banach_point_closed hf.epigraph_convex hf.epigraph_closed hbelow
  let l₀ : X →L[ℝ] ℝ := L.comp (.inl ℝ X ℝ)
  let b := L (0, 1)
  have hvertical (t : ℝ) : t * b = L (0, t) := by
    calc
      t * b = t • L (0, 1) := by rw [smul_eq_mul]
      _ = L (t • (0, 1)) := (L.map_smul t (0, 1)).symm
      _ = L (0, t) := by simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
  have hseparator {x : X} {t : ℝ} (hxt : f x ≤ (t : EReal)) :
      l₀ x₀ + b * (r₀ - 1) < l₀ x + b * t := by
    have hstrict := hLu.trans (hsep (x, t) hxt)
    rw [← ContinuousLinearMap.coprod_comp_inl_inr L] at hstrict
    simpa only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, l₀, ← hvertical,
      mul_comm] using hstrict
  have hb_pos : 0 < b := by
    have hfinite := hseparator (x := x₀) (t := r₀) (by rw [hx₀_coe])
    linarith
  let d := b⁻¹
  refine ⟨(-d) • l₀, d * l₀ x₀ + (r₀ - 1), fun x ↦ ?_⟩
  by_cases hx_top : f x = ⊤
  · -- At points outside the effective domain the affine bound is automatic.
    simp only [hx_top, le_top]
  · -- At finite points, normalize the separator by its positive vertical coefficient.
    let t := (f x).toReal
    have hx_coe : (t : EReal) = f x := EReal.coe_toReal hx_top (hf.ne_bot x)
    have hstrict := hseparator (x := x) (t := t) (by rw [hx_coe])
    have hdb : d * b = 1 := inv_mul_cancel₀ hb_pos.ne'
    have hreal : (-d) * l₀ x + (d * l₀ x₀ + (r₀ - 1)) ≤ t := by
      have hd_pos : 0 < d := inv_pos.mpr hb_pos
      have hscaled := mul_lt_mul_of_pos_left hstrict hd_pos
      rw [mul_add, mul_add, ← mul_assoc d b (r₀ - 1), ← mul_assoc d b t,
        hdb, one_mul] at hscaled
      linarith
    rw [← hx_coe, EReal.coe_le_coe_iff]
    simpa only [smul_apply, smul_eq_mul] using hreal

/-- The squared supremum norm of a finite real vector is bounded by its self dot product. -/
private lemma norm_sq_le_dotProduct_self {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ^ 2 ≤ dotProduct x x := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl hempty =>
      -- With no coordinates, both sides vanish.
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]
  | inr _ =>
      -- A coordinate attaining the supremum norm contributes its square to the sum.
      obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
      have hterm : x i * x i ≤ dotProduct x x := by
        unfold dotProduct
        exact Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (x j)) (Finset.mem_univ i)
      calc
        ‖x‖ ^ 2 = ‖x i‖ ^ 2 := (congrArg (fun r : ℝ ↦ r ^ 2) hi).symm
        _ = x i * x i := by rw [Real.norm_eq_abs, sq_abs, pow_two]
        _ ≤ dotProduct x x := hterm

/-- Quadratic regularization preserves lower semicontinuity of a closed proper convex function. -/
private lemma regularizedLowerSemicontinuous {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin n → ℝ) :
    LowerSemicontinuous
      (fun x ↦ φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal)) := by
  -- The real quadratic term is continuous, hence so is its coercion to `EReal`.
  have hquadraticReal :
      Continuous (fun x : Fin n → ℝ ↦ dotProduct (x - z) (x - z) / 2) :=
    ((continuous_id.sub continuous_const).dotProduct
      (continuous_id.sub continuous_const)).div_const 2
  have hquadratic :
      Continuous
        (fun x : Fin n → ℝ ↦ ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp hquadraticReal
  -- Addition is continuous at every relevant pair because neither summand is bottom.
  exact (lowerSemicontinuous_of_closedProperConvex hφ).add'
    hquadratic.lowerSemicontinuous fun x ↦
      EReal.continuousAt_add (.inr (by simp)) (.inl (hφ.ne_bot x))

/-- Every real sublevel of a quadratically regularized closed proper convex function is compact. -/
private lemma regularizedSublevel_isCompact {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin n → ℝ) (M : ℝ) :
    IsCompact
      {x | φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≤ (M : EReal)} := by
  classical
  -- Lower semicontinuity closes the sublevel; it remains to prove a uniform radius bound.
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact (regularizedLowerSemicontinuous hφ z).isClosed_preimage M
  · obtain ⟨l, c, hminor⟩ := exists_continuousAffineMinorant_of_closedProperConvex hφ
    let C := |M - c + ‖l‖ * ‖z‖|
    let R := 2 * ‖l‖ + 2 * C + 1
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R + ‖z‖, fun x hx ↦ ?_⟩
    let q := dotProduct (x - z) (x - z) / 2
    have hsum : ((l x + c + q : ℝ) : EReal) ≤ (M : EReal) := by
      calc
        ((l x + c + q : ℝ) : EReal) = (l x + c : EReal) + (q : EReal) := by
          exact EReal.coe_add (l x + c) q
        _ ≤ φ x + (q : EReal) :=
          (EReal.addLECancellable_coe q).add_le_add_iff_right.mpr (hminor x)
        _ ≤ (M : EReal) := hx
    have hreal : l x + c + q ≤ M := EReal.coe_le_coe_iff.mp hsum
    have hlower : -‖l‖ * ‖x‖ ≤ l x := by
      calc
        -‖l‖ * ‖x‖ ≤ -|l x| := by
          have hop := l.le_opNorm x
          rw [Real.norm_eq_abs] at hop
          linarith
        _ ≤ l x := neg_abs_le (l x)
    have hnormx : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      calc
        ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    have hdot : ‖x - z‖ ^ 2 ≤ dotProduct (x - z) (x - z) :=
      norm_sq_le_dotProduct_self (x - z)
    have hcoercive :
        ‖x - z‖ ^ 2 ≤ 2 * ‖l‖ * ‖x - z‖ + 2 * C := by
      have hC : M - c + ‖l‖ * ‖z‖ ≤ C := le_abs_self _
      have hl_nonneg : 0 ≤ ‖l‖ := norm_nonneg l
      dsimp only [q] at hreal
      nlinarith
    have hradius : ‖x - z‖ ≤ R := by
      have hC_nonneg : 0 ≤ C := abs_nonneg _
      have hl_nonneg : 0 ≤ ‖l‖ := norm_nonneg l
      have hr_nonneg : 0 ≤ ‖x - z‖ := norm_nonneg _
      by_contra hnot
      have hlarge : R < ‖x - z‖ := lt_of_not_ge hnot
      dsimp only [R] at hlarge ⊢
      nlinarith [sq_nonneg (‖x - z‖ - (2 * ‖l‖ + 1))]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnormx.trans (by linarith)

/-- The self dot product of an average has the parallelogram midpoint defect. -/
private lemma dotProduct_average {n : ℕ} (a b : Fin n → ℝ) :
    dotProduct ((2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b)
          ((2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b) / 2 =
      (dotProduct a a / 2 + dotProduct b b / 2) / 2 -
        dotProduct (a - b) (a - b) / 8 := by
  -- Bilinearity reduces the identity to scalar arithmetic.
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    sub_dotProduct, dotProduct_sub, smul_eq_mul]
  rw [dotProduct_comm a b]
  ring

/-- The squared-distance regularizer has the standard strict midpoint defect. -/
private lemma quadraticRegularizer_midpoint {n : ℕ}
    (x y z : Fin n → ℝ) :
    dotProduct
          ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y - z)
          ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y - z) / 2 =
      (dotProduct (x - z) (x - z) / 2 +
          dotProduct (y - z) (y - z) / 2) / 2 -
        dotProduct (x - y) (x - y) / 8 := by
  -- Rewrite the midpoint and difference through the two centered vectors.
  have hmid :
      (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y - z =
        (2 : ℝ)⁻¹ • (x - z) + (2 : ℝ)⁻¹ • (y - z) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdiff : x - y = (x - z) - (y - z) := by
    ext i
    simp only [Pi.sub_apply]
    ring
  rw [hmid, hdiff]
  exact dotProduct_average (x - z) (y - z)

/-- Two proximal points of a closed proper convex function at one center coincide. -/
private lemma isProxPoint_eq {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) {z x y : Fin n → ℝ}
    (hx : IsProxPoint φ z x) (hy : IsProxPoint φ z y) : x = y := by
  -- Record finite objective values and global minimality at the two points.
  obtain ⟨rx, hxvalue, hxmin⟩ := isProxPoint_iff.mp hx
  obtain ⟨ry, hyvalue, hymin⟩ := isProxPoint_iff.mp hy
  by_contra hxy
  let qx := dotProduct (x - z) (x - z) / 2
  let qy := dotProduct (y - z) (y - z) / 2
  let xm := (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y
  let qm := dotProduct (xm - z) (xm - z) / 2
  -- Cancelling the finite quadratic terms puts both points in the epigraph at real heights.
  have hφx : φ x = ((rx - qx : ℝ) : EReal) := by
    have hxvalue' : φ x + (qx : EReal) = (rx : EReal) := by
      simpa only [qx] using hxvalue
    have hcancel := congrArg (fun a : EReal ↦ a - (qx : EReal)) hxvalue'
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using hcancel
  have hφy : φ y = ((ry - qy : ℝ) : EReal) := by
    have hyvalue' : φ y + (qy : EReal) = (ry : EReal) := by
      simpa only [qy] using hyvalue
    have hcancel := congrArg (fun a : EReal ↦ a - (qy : EReal)) hyvalue'
    simpa only [EReal.add_sub_cancel_right, ← EReal.coe_sub] using hcancel
  have hxepi : (x, rx - qx) ∈ {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ x ≤ ((rx - qx : ℝ) : EReal)
    rw [hφx]
  have hyepi : (y, ry - qy) ∈ {p : (Fin n → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    change φ y ≤ ((ry - qy : ℝ) : EReal)
    rw [hφy]
  have hmepi := hφ.epigraph_convex hxepi hyepi
      (show 0 ≤ (2 : ℝ)⁻¹ by norm_num) (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
      (show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)
  have hφmid :
      φ xm ≤ (((2 : ℝ)⁻¹ * (rx - qx) + (2 : ℝ)⁻¹ * (ry - qy) : ℝ) : EReal) := by
    simpa only [Set.mem_setOf_eq, Prod.smul_mk, Prod.fst_add, Prod.snd_add,
      Prod.fst, Prod.snd, smul_eq_mul, invOf_eq_inv, div_eq_mul_inv, xm,
      add_mul] using hmepi
  -- The positive midpoint defect makes the midpoint objective strictly smaller.
  have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hdefect_pos : 0 < dotProduct (x - y) (x - y) := by
    have hnonneg : 0 ≤ dotProduct (x - y) (x - y) := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg ((x - y) i)
    have hne : dotProduct (x - y) (x - y) ≠ 0 := by
      intro hzero
      exact hdiff_ne (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hqmid :
      qm = (qx + qy) / 2 - dotProduct (x - y) (x - y) / 8 := by
    simpa only [qm, qx, qy, xm] using quadraticRegularizer_midpoint x y z
  have hmid_upper :
      φ xm + (qm : EReal) < (((rx + ry) / 2 : ℝ) : EReal) := by
    have hadd := (EReal.addLECancellable_coe qm).add_le_add_iff_right.mpr hφmid
    have hreal :
        (2 : ℝ)⁻¹ * (rx - qx) + (2 : ℝ)⁻¹ * (ry - qy) + qm <
          (rx + ry) / 2 := by
      rw [hqmid]
      nlinarith
    exact hadd.trans_lt (by
      rw [← EReal.coe_add]
      exact EReal.coe_lt_coe_iff.mpr hreal)
  -- Both alleged minima lie below the midpoint, contradicting the strict upper bound.
  have hrx : (rx : EReal) ≤ φ xm + (qm : EReal) := by
    rw [← hxvalue]
    exact hxmin xm
  have hry : (ry : EReal) ≤ φ xm + (qm : EReal) := by
    rw [← hyvalue]
    exact hymin xm
  have hrx_real : rx < (rx + ry) / 2 :=
    EReal.coe_lt_coe_iff.mp (hrx.trans_lt hmid_upper)
  have hry_real : ry < (rx + ry) / 2 :=
    EReal.coe_lt_coe_iff.mp (hry.trans_lt hmid_upper)
  linarith

/-- A closed proper convex extended-real function on a finite-dimensional
coordinate space has a unique proximal point at every center. -/
theorem existsUnique_isProxPoint {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (z : Fin n → ℝ) :
    ∃! x, IsProxPoint φ z x := by
  classical
  -- A finite point supplies a nonempty compact sublevel of the regularized objective.
  obtain ⟨x₀, hx₀_top⟩ := hφ.exists_ne_top
  let r₀ := (φ x₀).toReal
  let q₀ := dotProduct (x₀ - z) (x₀ - z) / 2
  let M := r₀ + q₀
  have hx₀_coe : (r₀ : EReal) = φ x₀ := EReal.coe_toReal hx₀_top (hφ.ne_bot x₀)
  have hx₀_value :
      φ x₀ + ((dotProduct (x₀ - z) (x₀ - z) / 2 : ℝ) : EReal) = (M : EReal) := by
    rw [← hx₀_coe]
    exact EReal.coe_add r₀ q₀
  have hx₀_mem :
      x₀ ∈ {x | φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≤
        (M : EReal)} := by
    rw [Set.mem_setOf_eq, hx₀_value]
  obtain ⟨x, hxsublevel, hxminSublevel⟩ :=
    LowerSemicontinuousOn.exists_isMinOn
      ⟨x₀, hx₀_mem⟩ (regularizedSublevel_isCompact hφ z M)
      ((regularizedLowerSemicontinuous hφ z).lowerSemicontinuousOn
        {a | φ a + ((dotProduct (a - z) (a - z) / 2 : ℝ) : EReal) ≤ (M : EReal)})
  -- Outside the chosen sublevel, its defining bound globalizes the compact minimum.
  have hxmin : ∀ y,
      φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≤
        φ y + ((dotProduct (y - z) (y - z) / 2 : ℝ) : EReal) := by
    intro y
    by_cases hy :
        φ y + ((dotProduct (y - z) (y - z) / 2 : ℝ) : EReal) ≤ (M : EReal)
    · exact hxminSublevel hy
    · exact hxsublevel.trans (le_of_lt (lt_of_not_ge hy))
  -- The attained value is real because the objective is neither top nor bottom.
  let r :=
    (φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal)).toReal
  have hx_top :
      φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top M) hxsublevel
  have hx_bot :
      φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨hφ.ne_bot x, EReal.coe_ne_bot _⟩
  have hx_coe :
      (r : EReal) =
        φ x + ((dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) :=
    EReal.coe_toReal hx_top hx_bot
  have hxprox : IsProxPoint φ z x := by
    rw [isProxPoint_iff]
    exact ⟨r, hx_coe.symm, hxmin⟩
  refine ⟨x, hxprox, fun y hyprox ↦ ?_⟩
  -- Strict midpoint convexity gives uniqueness of the attained minimizer.
  exact isProxPoint_eq hφ hyprox hxprox

end ADMM
