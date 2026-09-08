module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

public section

universe u

open scoped Topology

namespace QConvergence

variable {E : Type u} [NormedAddCommGroup E]

/-- The norm error of the `k`th term of a sequence relative to its proposed limit. -/
def error (x : ℕ → E) (xStar : E) (k : ℕ) : ℝ :=
  ‖x k - xStar‖

/-- Evaluating the error gives the distance-like norm from the proposed limit. -/
theorem error_apply (x : ℕ → E) (xStar : E) (k : ℕ) :
    error x xStar k = ‖x k - xStar‖ := by
  -- Unfold the scalar error at the requested index.
  rfl

/-- A sequence has Q-order at least `p` at `xStar` when it converges there without
eventually becoming stationary and its next error is eventually `O(error ^ p)`. -/
def HasOrderAtLeast (x : ℕ → E) (xStar : E) (p : ℝ) : Prop :=
  Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
    (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
      1 ≤ p ∧
        Asymptotics.IsBigO Filter.atTop (fun k ↦ error x xStar (k + 1))
          (fun k ↦ error x xStar k ^ p)

/-- Q-order at least `p` is equivalently witnessed by one positive constant that
controls every sufficiently late adjacent pair. -/
theorem hasOrderAtLeast_iff (x : ℕ → E) (xStar : E) (p : ℝ) :
    HasOrderAtLeast x xStar p ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          1 ≤ p ∧
            ∃ C > 0, ∀ᶠ k in Filter.atTop,
              error x xStar (k + 1) ≤ C * error x xStar k ^ p := by
  -- The Big-O norm bound is the desired estimate because both error terms are nonnegative.
  simp only [HasOrderAtLeast, Asymptotics.isBigO_iff', Real.norm_eq_abs,
    abs_of_nonneg, error_apply, norm_nonneg, Real.rpow_nonneg]

/-- The eventual power estimate is equivalently expressed by finiteness of the
extended-nonnegative-real limsup of adjacent error ratios. -/
theorem hasOrderAtLeast_iff_limsup_lt_top (x : ℕ → E) (xStar : E) (p : ℝ) :
    HasOrderAtLeast x xStar p ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          1 ≤ p ∧
            Filter.limsup
                (fun k ↦ ENNReal.ofReal
                  (error x xStar (k + 1) / error x xStar k ^ p))
                Filter.atTop < ⊤ := by
  rw [hasOrderAtLeast_iff]
  constructor
  · rintro ⟨hx, hne, hp, C, hC, hbound⟩
    refine ⟨hx, hne, hp, ?_⟩
    have hdenom : ∀ᶠ k in Filter.atTop, 0 < error x xStar k ^ p := by
      filter_upwards [hne] with k hk
      have herr : 0 < error x xStar k := by
        rw [error_apply]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hk)
      exact Real.rpow_pos_of_pos herr p
    have hratio : ∀ᶠ k in Filter.atTop,
        ENNReal.ofReal (error x xStar (k + 1) / error x xStar k ^ p) ≤
          ENNReal.ofReal C := by
      -- Divide the eventual power estimate by its positive denominator.
      filter_upwards [hbound, hdenom] with k hk hkpos
      rw [ENNReal.ofReal_le_ofReal_iff hC.le]
      exact (div_le_iff₀ hkpos).2 hk
    -- A finite eventual upper bound gives a finite limsup.
    exact (Filter.limsup_le_of_le (h := hratio)).trans_lt ENNReal.ofReal_lt_top
  · rintro ⟨hx, hne, hp, hlim⟩
    refine ⟨hx, hne, hp, ?_⟩
    refine ⟨(Filter.limsup
        (fun k ↦ ENNReal.ofReal
          (error x xStar (k + 1) / error x xStar k ^ p))
        Filter.atTop).toReal + 1, by positivity, ?_⟩
    have hlim_ne_top : Filter.limsup
        (fun k ↦ ENNReal.ofReal
          (error x xStar (k + 1) / error x xStar k ^ p))
        Filter.atTop ≠ ⊤ := ne_of_lt hlim
    have hstrict : Filter.limsup
        (fun k ↦ ENNReal.ofReal
          (error x xStar (k + 1) / error x xStar k ^ p))
        Filter.atTop < ENNReal.ofReal
          ((Filter.limsup
            (fun k ↦ ENNReal.ofReal
              (error x xStar (k + 1) / error x xStar k ^ p))
            Filter.atTop).toReal + 1) := by
      calc
        Filter.limsup
            (fun k ↦ ENNReal.ofReal
              (error x xStar (k + 1) / error x xStar k ^ p))
            Filter.atTop = ENNReal.ofReal
              ((Filter.limsup
                (fun k ↦ ENNReal.ofReal
                  (error x xStar (k + 1) / error x xStar k ^ p))
                Filter.atTop).toReal) := (ENNReal.ofReal_toReal hlim_ne_top).symm
        _ < ENNReal.ofReal
              ((Filter.limsup
                (fun k ↦ ENNReal.ofReal
                  (error x xStar (k + 1) / error x xStar k ^ p))
                Filter.atTop).toReal + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    have hratio : ∀ᶠ k in Filter.atTop,
        ENNReal.ofReal (error x xStar (k + 1) / error x xStar k ^ p) <
          ENNReal.ofReal
            ((Filter.limsup
              (fun j ↦ ENNReal.ofReal
                (error x xStar (j + 1) / error x xStar j ^ p))
              Filter.atTop).toReal + 1) :=
      Filter.eventually_lt_of_limsup_lt hstrict
    filter_upwards [hne, hratio] with k hk hkrat
    have herr : 0 < error x xStar k := by
      rw [error_apply]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hk)
    have hdenom : 0 < error x xStar k ^ p := Real.rpow_pos_of_pos herr p
    have hreal : error x xStar (k + 1) / error x xStar k ^ p <
        (Filter.limsup
          (fun j ↦ ENNReal.ofReal
            (error x xStar (j + 1) / error x xStar j ^ p))
          Filter.atTop).toReal + 1 := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hkrat
    -- Enlarge the limsup's real value by one and clear the positive denominator.
    exact (div_le_iff₀ hdenom).1 hreal.le

/-- Every exponent between one and an admissible exponent is also admissible. -/
theorem HasOrderAtLeast.mono {x : ℕ → E} {xStar : E} {p q : ℝ}
    (hp : HasOrderAtLeast x xStar p) (hq_one : 1 ≤ q) (hqp : q ≤ p) :
    HasOrderAtLeast x xStar q := by
  rw [hasOrderAtLeast_iff] at hp ⊢
  rcases hp with ⟨hx, hne, hp_one, C, hC, hbound⟩
  have herror : Filter.Tendsto (fun k ↦ error x xStar k) Filter.atTop (𝓝 0) := by
    -- Continuity of subtraction and norm transports convergence to the scalar error.
    simpa only [error_apply, sub_self, norm_zero] using
      (hx.sub (tendsto_const_nhds (x := xStar))).norm
  have hsmall : ∀ᶠ k in Filter.atTop, error x xStar k ≤ 1 :=
    herror.eventually_le_const zero_lt_one
  refine ⟨hx, hne, hq_one, C, hC, ?_⟩
  filter_upwards [hbound, hsmall] with k hk hk_one
  have hpow : error x xStar k ^ p ≤ error x xStar k ^ q :=
    Real.rpow_le_rpow_of_exponent_ge'
      (by rw [error_apply]; exact norm_nonneg _) hk_one (zero_le_one.trans hq_one) hqp
  -- On the eventual unit ball, lowering the exponent only enlarges the right-hand side.
  exact hk.trans (mul_le_mul_of_nonneg_left hpow hC.le)

/-- The real exponents for which a sequence has the corresponding lower Q-order bound. -/
def admissibleExponents (x : ℕ → E) (xStar : E) : Set ℝ :=
  {p | HasOrderAtLeast x xStar p}

/-- Membership among admissible exponents is exactly the Q-order-at-least predicate. -/
theorem mem_admissibleExponents (x : ℕ → E) (xStar : E) (p : ℝ) :
    p ∈ admissibleExponents x xStar ↔ HasOrderAtLeast x xStar p := by
  -- Membership reduces to the defining predicate of the set.
  rfl

/-- The Q-order is the extended supremum of the admissible real exponents. -/
noncomputable def order (x : ℕ → E) (xStar : E) : ENNReal :=
  sSup (ENNReal.ofReal '' admissibleExponents x xStar)

/-- The Q-order is explicitly the extended supremum of the admissible exponents. -/
theorem order_def (x : ℕ → E) (xStar : E) :
    order x xStar = sSup (ENNReal.ofReal '' admissibleExponents x xStar) := by
  -- Expose the supremum used to define the Q-order.
  rfl

/-- A sequence has Q-order one exactly when exponent one is admissible and every
strictly larger real exponent is inadmissible. -/
theorem order_eq_one_iff (x : ℕ → E) (xStar : E) :
    order x xStar = 1 ↔
      HasOrderAtLeast x xStar 1 ∧ ∀ p : ℝ, 1 < p → ¬HasOrderAtLeast x xStar p := by
  rw [order_def]
  constructor
  · intro horder
    have hpositive : 0 < sSup (ENNReal.ofReal '' admissibleExponents x xStar) := by
      rw [horder]
      exact zero_lt_one
    obtain ⟨a, ha, ha_pos⟩ := lt_sSup_iff.mp hpositive
    rcases ha with ⟨p, hp_mem, rfl⟩
    have hp_order : HasOrderAtLeast x xStar p :=
      (mem_admissibleExponents x xStar p).mp hp_mem
    have hp_one : 1 ≤ p := ((hasOrderAtLeast_iff x xStar p).mp hp_order).2.2.1
    refine ⟨hp_order.mono le_rfl hp_one, ?_⟩
    intro q hq hq_order
    have hq_mem : ENNReal.ofReal q ∈ ENNReal.ofReal '' admissibleExponents x xStar :=
      ⟨q, (mem_admissibleExponents x xStar q).mpr hq_order, rfl⟩
    have hq_le : ENNReal.ofReal q ≤ 1 := (le_sSup hq_mem).trans_eq horder
    have hq_gt : 1 < ENNReal.ofReal q := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hq)).mpr hq
    -- Any admissible exponent above one would force the supremum above one.
    exact (not_lt_of_ge hq_le hq_gt).elim
  · rintro ⟨hone, hno_larger⟩
    apply le_antisymm
    · refine sSup_le ?_
      rintro a ⟨p, hp_mem, rfl⟩
      have hp_order : HasOrderAtLeast x xStar p :=
        (mem_admissibleExponents x xStar p).mp hp_mem
      have hp_lower : 1 ≤ p := ((hasOrderAtLeast_iff x xStar p).mp hp_order).2.2.1
      have hp_upper : p ≤ 1 := le_of_not_gt (fun hp_gt ↦ hno_larger p hp_gt hp_order)
      have hp_eq : p = 1 := le_antisymm hp_upper hp_lower
      -- Thus every element of the supremum set is exactly one.
      simp only [hp_eq, ENNReal.ofReal_one, le_refl]
    · apply le_sSup
      -- Exponent one itself witnesses the reverse inequality.
      exact ⟨1, (mem_admissibleExponents x xStar 1).mpr hone, ENNReal.ofReal_one⟩

/-- Q-superlinear convergence means convergence without eventual stationarity and
little-o decay of the next error relative to the current error. -/
def IsSuperlinear (x : ℕ → E) (xStar : E) : Prop :=
  Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
    (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
      Asymptotics.IsLittleO Filter.atTop (fun k ↦ error x xStar (k + 1))
        (fun k ↦ error x xStar k)

/-- Q-superlinear convergence is characterized by convergence, eventual
nonstationarity, and the canonical little-o relation between adjacent errors. -/
theorem isSuperlinear_iff (x : ℕ → E) (xStar : E) :
    IsSuperlinear x xStar ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          Asymptotics.IsLittleO Filter.atTop (fun k ↦ error x xStar (k + 1))
            (fun k ↦ error x xStar k) := by
  -- This is the public unfolding equation for superlinear convergence.
  rfl

/-- Q-superlinear convergence is equivalently convergence with the adjacent-error
ratio tending to zero. -/
theorem isSuperlinear_iff_ratio (x : ℕ → E) (xStar : E) :
    IsSuperlinear x xStar ↔
      Filter.Tendsto x Filter.atTop (𝓝 xStar) ∧
        (∀ᶠ k in Filter.atTop, x k ≠ xStar) ∧
          Filter.Tendsto (fun k ↦ error x xStar (k + 1) / error x xStar k)
            Filter.atTop (𝓝 0) := by
  rw [isSuperlinear_iff]
  constructor
  · rintro ⟨hx, hne, hlittle⟩
    -- Little-o convergence gives convergence of the adjacent-error quotient.
    exact ⟨hx, hne, hlittle.tendsto_div_nhds_zero⟩
  · rintro ⟨hx, hne, hratio⟩
    refine ⟨hx, hne, (Asymptotics.isLittleO_iff_tendsto' ?_).2 hratio⟩
    -- Eventual nonstationarity makes a zero current error impossible.
    filter_upwards [hne] with k hk
    intro hzero
    simp only [error_apply, norm_eq_zero, sub_eq_zero] at hzero
    exact (hk hzero).elim

section ScalarMultiplication

variable [NormedSpace ℝ E]

/-- Scaling a sequence and its limit by a real scalar scales every error by the
absolute value of that scalar. -/
theorem error_smul (x : ℕ → E) (xStar : E) (c : ℝ) (k : ℕ) :
    error (fun j ↦ c • x j) (c • xStar) k = |c| * error x xStar k := by
  -- Factor the common scalar from the difference and evaluate its norm.
  rw [error_apply, error_apply, ← smul_sub, norm_smul, Real.norm_eq_abs]

/-- Multiplication by a nonzero real scalar preserves and reflects every lower
Q-order bound. -/
theorem hasOrderAtLeast_smul {x : ℕ → E} {xStar : E} {p c : ℝ} (hc : c ≠ 0) :
    HasOrderAtLeast (fun k ↦ c • x k) (c • xStar) p ↔
      HasOrderAtLeast x xStar p := by
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  have habsPow : |c| ^ p ≠ 0 :=
    (Real.rpow_pos_of_pos (abs_pos.mpr hc) p).ne'
  have herrorNonneg (k : ℕ) : 0 ≤ error x xStar k := by
    rw [error_apply]
    exact norm_nonneg _
  have hnonstationary (k : ℕ) : c • x k ≠ c • xStar ↔ x k ≠ xStar :=
    not_congr (smul_right_inj hc)
  have hrpow (k : ℕ) :
      (|c| * error x xStar k) ^ p = |c| ^ p * error x xStar k ^ p := by
    -- Split the power after recording nonnegativity of both factors.
    exact Real.mul_rpow (abs_nonneg c) (herrorNonneg k)
  -- Transport convergence and nonstationarity, then cancel both fixed Big-O factors.
  simp only [HasOrderAtLeast, tendsto_const_smul_iff₀ hc, hnonstationary,
    error_smul, hrpow, Asymptotics.isBigO_const_mul_left_iff habs,
    Asymptotics.isBigO_const_mul_right_iff habsPow]

/-- Multiplication by a nonzero real scalar preserves the set of admissible
Q-order exponents. -/
theorem admissibleExponents_smul {x : ℕ → E} {xStar : E} {c : ℝ} (hc : c ≠ 0) :
    admissibleExponents (fun k ↦ c • x k) (c • xStar) =
      admissibleExponents x xStar := by
  -- Membership in the two sets agrees by scalar invariance of every lower order bound.
  ext p
  rw [mem_admissibleExponents, mem_admissibleExponents, hasOrderAtLeast_smul hc]

/-- Multiplication by a nonzero real scalar preserves the totalized Q-order. -/
theorem order_smul {x : ℕ → E} {xStar : E} {c : ℝ} (hc : c ≠ 0) :
    order (fun k ↦ c • x k) (c • xStar) = order x xStar := by
  -- Equal admissible-exponent sets have the same extended supremum.
  rw [order_def, order_def, admissibleExponents_smul hc]

end ScalarMultiplication

end QConvergence
