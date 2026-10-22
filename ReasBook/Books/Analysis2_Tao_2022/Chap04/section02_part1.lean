/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Classical

section Chap04
section Section02

/-- Definition 4.2.1 (Real analytic at a point): let `E ⊆ ℝ`, `f : E → ℝ`, and `a ∈ E` be an interior point of `E`. The function `f` is real analytic at `a` if there exist `r > 0` and coefficients `c : ℕ → ℝ` such that `(a-r, a+r) ⊆ E`, the power series `∑ c n (x-a)^n` converges for every `x ∈ (a-r, a+r)` (encoding radius of convergence at least `r`), and `f x` equals that series on `(a-r, a+r)`. -/
def IsRealAnalyticAt (E : Set ℝ) (f : E → ℝ) (a : E) : Prop :=
  (a : ℝ) ∈ interior E ∧
    ∃ r : ℝ, 0 < r ∧
        ∃ hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E,
        ∃ c : ℕ → ℝ,
          (∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
            Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n)) ∧
          ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
            f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n

/-- A function on `E` is real analytic on `E` when `E` is open and the function is real analytic at each point of `E`. -/
def IsRealAnalyticOn (E : Set ℝ) (f : E → ℝ) : Prop :=
  IsOpen E ∧ ∀ a : E, IsRealAnalyticAt E f a

/-- A set of real numbers has no isolated points if every `x ∈ E` is a limit point of `E`. -/
def HasNoIsolatedPoints (E : Set ℝ) : Prop :=
  ∀ x ∈ E, x ∈ closure (E \ {x})

/-- Canonical extension of `f : E → ℝ` to `ℝ`, taking value `0` off `E`. -/
noncomputable def SubtypeExtension (E : Set ℝ) (f : E → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ E then f ⟨x, hx⟩ else 0

/-- The first derivative `f' : E → ℝ`, defined by the within-set derivative on `E`. -/
noncomputable def FirstDerivativeSub (E : Set ℝ) (f : E → ℝ) : E → ℝ :=
  fun x => derivWithin (SubtypeExtension E f) E x

/-- Iterated derivatives on `E`: `f^(0)=f` and `f^(n+1)` is the first derivative of `f^(n)`. -/
noncomputable def IteratedDerivativeSub (E : Set ℝ) (f : E → ℝ) : ℕ → E → ℝ
  | 0 => f
  | n + 1 => FirstDerivativeSub E (IteratedDerivativeSub E f n)

/-- A function `f : E → ℝ` is once differentiable on `E` when it is differentiable within `E` at every point of `E`. -/
def IsOnceDifferentiableSub (E : Set ℝ) (f : E → ℝ) : Prop :=
  ∀ x : E, DifferentiableWithinAt ℝ (SubtypeExtension E f) E (x : ℝ)

/-- Definition 4.2.2 (`k`-times differentiability on a set).

(i) once differentiable means differentiable at every point of `E`;
(ii) for `k ≥ 2`, `k`-times differentiable is defined recursively via the derivative;
(iii) iterated derivatives are `f^(0)=f`, `f^(1)=f'`, `f^(k)=((f^(k-1))')`;
(iv) infinitely differentiable (smooth) means `k`-times differentiable for every `k ≥ 0`.

The standing hypothesis that every point of `E` is a limit point of `E` is recorded by
`HasNoIsolatedPoints E` as part of the definition.
-/
def IsKTimesDifferentiableSub (E : Set ℝ) (f : E → ℝ) : ℕ → Prop :=
  fun k =>
    HasNoIsolatedPoints E ∧
      Nat.rec (motive := fun _ => Prop) True
        (fun n ih => IsOnceDifferentiableSub E (IteratedDerivativeSub E f n) ∧ ih) k

/-- A function on `E` is smooth when it is `k`-times differentiable for every `k : ℕ`. -/
def IsSmoothSub (E : Set ℝ) (f : E → ℝ) : Prop :=
  ∀ k : ℕ, IsKTimesDifferentiableSub E f k

/-- The function `x ↦ |x|^3` on `ℝ`. -/
def absCube : ℝ → ℝ :=
  fun x => |x| ^ (3 : ℕ)

/-- Helper for Proposition 4.2.1: rewrite `absCube` using real powers. -/
lemma helperForProposition_4_2_1_absCube_eq_absRpowThree :
    absCube = fun x : ℝ => |x| ^ (3 : ℝ) := by
  funext x
  simp [absCube]

/-- Helper for Proposition 4.2.1: derivative formula for `x ↦ |x|^3`. -/
lemma helperForProposition_4_2_1_hasDerivAt_absCube (x : ℝ) :
    HasDerivAt absCube (3 * x * |x|) x := by
  have hRpow := hasDerivAt_abs_rpow x (by norm_num : (1 : ℝ) < 3)
  have hDerivEq : 3 * |x| ^ ((3 : ℝ) - 2) * x = 3 * x * |x| := by
    calc
      3 * |x| ^ ((3 : ℝ) - 2) * x = 3 * |x| ^ (1 : ℝ) * x := by norm_num
      _ = 3 * |x| * x := by simp [Real.rpow_one]
      _ = 3 * x * |x| := by ring
  have hMain : HasDerivAt (fun y : ℝ => |y| ^ (3 : ℝ)) (3 * x * |x|) x :=
    hRpow.congr_deriv hDerivEq
  simpa [helperForProposition_4_2_1_absCube_eq_absRpowThree] using hMain

/-- Helper for Proposition 4.2.1: derivative formula for `x ↦ x|x|`. -/
lemma helperForProposition_4_2_1_hasDerivAt_xMulAbs (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * |y|) (2 * |x|) x := by
  by_cases hx0 : x = 0
  · subst hx0
    have hZero : HasDerivAt (fun y : ℝ => y * |y|) 0 0 := by
      refine (hasDerivAt_iff_tendsto_slope_zero).2 ?_
      have hAbs : Filter.Tendsto (fun t : ℝ => |t|) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) := by
        have hcont : Continuous (fun t : ℝ => |t|) := continuous_abs
        simpa using hcont.continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds (0 : ℝ))
      have hEq :
          (fun t : ℝ => t⁻¹ • ((0 + t) * |0 + t| - 0 * |0|)) =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
            (fun t : ℝ => |t|) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := by simpa using ht
        calc
          t⁻¹ • ((0 + t) * |0 + t| - 0 * |0|) = t⁻¹ * (t * |t|) := by simp [smul_eq_mul]
          _ = (t⁻¹ * t) * |t| := by ring
          _ = |t| := by simp [ht0]
      have hSlope :
          Filter.Tendsto (fun t : ℝ => t⁻¹ • ((0 + t) * |0 + t| - 0 * |0|))
            (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : ℝ)) :=
        Filter.Tendsto.congr' hEq.symm hAbs
      exact hSlope
    exact hZero.congr_deriv (by simp)
  · by_cases hxpos : 0 < x
    · have hMul : HasDerivAt (fun y : ℝ => y * |y|) (1 * |x| + x * 1) x := by
        exact (hasDerivAt_id x).mul (hasDerivAt_abs_pos hxpos)
      have hDerivEq : 1 * |x| + x * 1 = 2 * |x| := by
        rw [abs_of_pos hxpos]
        ring
      exact hMul.congr_deriv hDerivEq
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hMul : HasDerivAt (fun y : ℝ => y * |y|) (1 * |x| + x * (-1)) x := by
        exact (hasDerivAt_id x).mul (hasDerivAt_abs_neg hxneg)
      have hDerivEq : 1 * |x| + x * (-1) = 2 * |x| := by
        rw [abs_of_neg hxneg]
        ring
      exact hMul.congr_deriv hDerivEq

/-- Helper for Proposition 4.2.1: derivative formula for `deriv absCube`. -/
lemma helperForProposition_4_2_1_hasDerivAt_derivAbsCube (x : ℝ) :
    HasDerivAt (deriv absCube) (6 * |x|) x := by
  have hDerivAbsCube : deriv absCube = fun y : ℝ => 3 * y * |y| := by
    funext y
    exact (helperForProposition_4_2_1_hasDerivAt_absCube y).deriv
  have hCore : HasDerivAt (fun y : ℝ => 3 * y * |y|) (3 * (2 * |x|)) x := by
    simpa [mul_assoc] using (helperForProposition_4_2_1_hasDerivAt_xMulAbs x).const_mul 3
  have hMain : HasDerivAt (deriv absCube) (3 * (2 * |x|)) x := by
    simpa [hDerivAbsCube] using hCore
  exact hMain.congr_deriv (by ring)

/-- Helper for Proposition 4.2.1: the second derivative `x ↦ 6|x|` is not differentiable at `0`. -/
lemma helperForProposition_4_2_1_notDifferentiableAt_zero_secondDeriv :
    ¬DifferentiableAt ℝ (fun x : ℝ => 6 * |x|) 0 := by
  intro h
  have hAbs : DifferentiableAt ℝ (fun x : ℝ => |x|) 0 := by
    simpa [mul_assoc] using h.const_mul (1 / (6 : ℝ))
  exact not_differentiableAt_abs_zero hAbs

/-- Proposition 4.2.1: for `f(x) = |x|^3`, one has
`f'(x) = 3x|x|` and `f''(x) = 6|x|` for all `x ∈ ℝ`; hence `f` is twice
differentiable on `ℝ`, while `f''` is not differentiable at `0`
(equivalently, `f` is not three times differentiable at `0`). -/
theorem absCube_twiceDifferentiable_and_not_threeTimesDifferentiableAt_zero :
    Differentiable ℝ absCube ∧
      Differentiable ℝ (deriv absCube) ∧
        (∀ x : ℝ, deriv absCube x = 3 * x * |x|) ∧
          (∀ x : ℝ, deriv (deriv absCube) x = 6 * |x|) ∧
            ¬DifferentiableAt ℝ (deriv (deriv absCube)) 0 := by
  have hDiffAbsCube : Differentiable ℝ absCube := by
    intro x
    exact (helperForProposition_4_2_1_hasDerivAt_absCube x).differentiableAt
  have hDerivFormula : ∀ x : ℝ, deriv absCube x = 3 * x * |x| := by
    intro x
    exact (helperForProposition_4_2_1_hasDerivAt_absCube x).deriv
  have hHasDerivDerivAbsCube : ∀ x : ℝ, HasDerivAt (deriv absCube) (6 * |x|) x := by
    intro x
    exact helperForProposition_4_2_1_hasDerivAt_derivAbsCube x
  have hDiffDerivAbsCube : Differentiable ℝ (deriv absCube) := by
    intro x
    exact (hHasDerivDerivAbsCube x).differentiableAt
  have hSecondDerivFormula : ∀ x : ℝ, deriv (deriv absCube) x = 6 * |x| := by
    intro x
    exact (hHasDerivDerivAbsCube x).deriv
  have hNotDiffAtZero : ¬DifferentiableAt ℝ (deriv (deriv absCube)) 0 := by
    intro h
    have hEq : deriv (deriv absCube) = fun x : ℝ => 6 * |x| := by
      funext x
      exact hSecondDerivFormula x
    have hContradiction : DifferentiableAt ℝ (fun x : ℝ => 6 * |x|) 0 := by
      simpa [hEq] using h
    exact helperForProposition_4_2_1_notDifferentiableAt_zero_secondDeriv hContradiction
  exact ⟨hDiffAbsCube, hDiffDerivAbsCube, hDerivFormula, hSecondDerivFormula, hNotDiffAtZero⟩

/-- Helper for Proposition 4.2.2: open intervals in `ℝ` have no isolated points. -/
lemma helperForProposition_4_2_2_interval_hasNoIsolatedPoints (a r : ℝ) :
    HasNoIsolatedPoints (Set.Ioo (a - r) (a + r)) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases hx with ⟨hx_left, hx_right⟩
  let t : ℝ := min (ε / 2) ((a + r - x) / 2)
  have ht_pos : 0 < t := by
    unfold t
    refine lt_min ?_ ?_
    · linarith
    · linarith
  refine ⟨x + t, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · constructor
      · linarith
      · have ht_lt : t < a + r - x := by
          have hhalf_pos : 0 < (a + r - x) / 2 := by linarith
          have hle : t ≤ (a + r - x) / 2 := by
            unfold t
            exact min_le_right _ _
          linarith
        linarith
    · have hx_ne : x + t ≠ x := by linarith
      simpa [Set.mem_singleton_iff] using hx_ne
  · have hdist : dist x (x + t) = |t| := by
      rw [Real.dist_eq]
      ring_nf
      simp
    rw [hdist, abs_of_nonneg (le_of_lt ht_pos)]
    have hle : t ≤ ε / 2 := by
      unfold t
      exact min_le_left _ _
    linarith

/-- Helper for Proposition 4.2.2: the `k = 0` termwise coefficient factor is `1`. -/
lemma helperForProposition_4_2_2_kZero_seriesTerm_eq
    (c : ℕ → ℝ) (a x : ℝ) :
    (fun n : ℕ =>
      c (n + 0) *
        ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
          (x - a) ^ n) =
      (fun n : ℕ => c n * (x - a) ^ n) := by
  funext n
  have hne : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  calc
    c (n + 0) *
          ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
            (x - a) ^ n
        = c n * ((Nat.factorial n : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n := by
            simp
    _ = c n * 1 * (x - a) ^ n := by rw [div_self hne]
    _ = c n * (x - a) ^ n := by simp

/-- Helper for Proposition 4.2.2: the target series identity for `k = 0`. -/
lemma helperForProposition_4_2_2_seriesFormula_kZero
    {a r : ℝ} (f : Set.Ioo (a - r) (a + r) → ℝ) (c : ℕ → ℝ)
    (hc :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) :
    ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
      Summable
          (fun n : ℕ =>
            c (n + 0) *
              ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
                (x - a) ^ n) ∧
        IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f 0 ⟨x, hx⟩ =
          ∑' n : ℕ,
            c (n + 0) *
              ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
                (x - a) ^ n := by
  intro x hx
  rcases hc x hx with ⟨hsum, hEq⟩
  have hterm :
      (fun n : ℕ =>
        c (n + 0) *
          ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
            (x - a) ^ n) =
        (fun n : ℕ => c n * (x - a) ^ n) :=
    helperForProposition_4_2_2_kZero_seriesTerm_eq c a x
  have hterm_pointwise :
      ∀ n : ℕ,
        c (n + 0) *
            ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
              (x - a) ^ n =
          c n * (x - a) ^ n := by
    intro n
    exact congrFun hterm n
  have hterm_pointwise_symm :
      ∀ n : ℕ,
        c n * (x - a) ^ n =
          c (n + 0) *
            ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
              (x - a) ^ n := by
    intro n
    exact (hterm_pointwise n).symm
  constructor
  · exact hsum.congr hterm_pointwise_symm
  · calc
      IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f 0 ⟨x, hx⟩
          = ∑' n : ℕ, c n * (x - a) ^ n := by
              simpa [IteratedDerivativeSub] using hEq
      _ = ∑' n : ℕ,
            c (n + 0) *
              ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
                (x - a) ^ n := by
            have htsum :
                (∑' n : ℕ,
                  c (n + 0) *
                    ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) *
                      (x - a) ^ n) =
                  (∑' n : ℕ, c n * (x - a) ^ n) := by
              exact tsum_congr hterm_pointwise
            exact htsum.symm

/-- Helper for Proposition 4.2.2: `IteratedDerivativeSub` agrees pointwise with
`iteratedDerivWithin` on the underlying set. -/
lemma helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin
    (E : Set ℝ) (f : E → ℝ) :
    ∀ k x (hx : x ∈ E),
      IteratedDerivativeSub E f k ⟨x, hx⟩ =
        iteratedDerivWithin k (SubtypeExtension E f) E x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [IteratedDerivativeSub, iteratedDerivWithin_zero, SubtypeExtension, hx]
  | succ k ih =>
      intro x hx
      have hEqOn :
          Set.EqOn
            (SubtypeExtension E (IteratedDerivativeSub E f k))
            (iteratedDerivWithin k (SubtypeExtension E f) E)
            E := by
        intro y hy
        have hyEq := ih y hy
        simpa [SubtypeExtension, hy] using hyEq
      have hEqAt :
          (SubtypeExtension E (IteratedDerivativeSub E f k)) x =
            iteratedDerivWithin k (SubtypeExtension E f) E x := by
        have hxEq := ih x hx
        simpa [SubtypeExtension, hx] using hxEq
      calc
        IteratedDerivativeSub E f (k + 1) ⟨x, hx⟩
            = derivWithin (SubtypeExtension E (IteratedDerivativeSub E f k)) E x := by
                rfl
        _ = derivWithin (iteratedDerivWithin k (SubtypeExtension E f) E) E x := by
              exact derivWithin_congr hEqOn hEqAt
        _ = iteratedDerivWithin (k + 1) (SubtypeExtension E f) E x := by
              rw [iteratedDerivWithin_succ]

/-- Helper for Proposition 4.2.2: smoothness of the ambient extension implies that every
iterated subtype derivative is once differentiable on the set. -/
lemma helperForProposition_4_2_2_isOnceDifferentiableSub_of_contDiffOn
    {E : Set ℝ} (f : E → ℝ)
    (hcont : ContDiffOn ℝ ⊤ (SubtypeExtension E f) E)
    (hunique : UniqueDiffOn ℝ E) :
    ∀ n : ℕ, IsOnceDifferentiableSub E (IteratedDerivativeSub E f n) := by
  intro n x
  have hDiff :
      DifferentiableWithinAt ℝ (iteratedDerivWithin n (SubtypeExtension E f) E) E x := by
    exact (hcont.differentiableOn_iteratedDerivWithin
      (by simpa using (WithTop.coe_lt_top : ((n : ℕ∞) : WithTop ℕ∞) < ⊤)) hunique) x x.property
  have hEqOn :
      Set.EqOn
        (SubtypeExtension E (IteratedDerivativeSub E f n))
        (iteratedDerivWithin n (SubtypeExtension E f) E)
        E := by
    intro y hy
    have hyEq := helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin E f n y hy
    simpa [SubtypeExtension, hy] using hyEq
  have hEqAt :
      (SubtypeExtension E (IteratedDerivativeSub E f n)) x =
        iteratedDerivWithin n (SubtypeExtension E f) E x := by
    have hxEq := helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin E f n x x.property
    simpa [SubtypeExtension, x.property] using hxEq
  exact hDiff.congr hEqOn hEqAt

/-- Helper for Proposition 4.2.2: if all iterated derivatives are once differentiable,
then the recursive notion of `k`-times differentiability holds for every `k`. -/
lemma helperForProposition_4_2_2_isKTimesDifferentiableSub_of_allOnceDifferentiable
    {E : Set ℝ} (f : E → ℝ) (hNoIso : HasNoIsolatedPoints E)
    (hOnce : ∀ n : ℕ, IsOnceDifferentiableSub E (IteratedDerivativeSub E f n)) :
    ∀ k : ℕ, IsKTimesDifferentiableSub E f k := by
  intro k
  refine ⟨hNoIso, ?_⟩
  induction k with
  | zero =>
      simp [IsKTimesDifferentiableSub]
  | succ k ih =>
      simpa [IsKTimesDifferentiableSub] using And.intro (hOnce k) ih

/-- Helper for Proposition 4.2.2: the interval series data gives
`HasFPowerSeriesWithinOnBall` for the canonical extension. -/
lemma helperForProposition_4_2_2_hasFPowerSeriesWithinOnBall_of_seriesData
    {a r : ℝ} (hr : 0 < r) (f : Set.Ioo (a - r) (a + r) → ℝ) (c : ℕ → ℝ)
    (hc :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) :
    HasFPowerSeriesWithinOnBall
      (SubtypeExtension (Set.Ioo (a - r) (a + r)) f)
      (FormalMultilinearSeries.ofScalars ℝ c)
      (Set.Ioo (a - r) (a + r)) a (ENNReal.ofReal r) := by
  refine HasFPowerSeriesWithinOnBall.mk ?_ (ENNReal.ofReal_pos.2 hr) ?_
  · refine ENNReal.le_of_forall_nnreal_lt ?_
    intro q hq
    have hq_real : (q : ℝ) < r := by
      have hq_top : (q : ENNReal) ≠ ⊤ := by simp
      exact (ENNReal.lt_ofReal_iff_toReal_lt hq_top).1 hq
    have hq_nonneg : 0 ≤ (q : ℝ) := by exact q.2
    have hqx : a + (q : ℝ) ∈ Set.Ioo (a - r) (a + r) := by
      constructor
      · linarith
      · linarith
    rcases hc (a + (q : ℝ)) hqx with ⟨hsum_q, hEq_q⟩
    have hsummable_q : Summable (fun n : ℕ => c n * (q : ℝ) ^ n) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum_q
    have hsummable_norm_q : Summable (fun n : ℕ => ‖c n‖ * (q : ℝ) ^ n) := by
      refine (hsummable_q.norm).congr ?_
      intro n
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hq_nonneg n)]
    have hsummable_norm_series :
        Summable (fun n : ℕ => ‖(FormalMultilinearSeries.ofScalars ℝ c n)‖ * (q : ℝ) ^ n) := by
      refine hsummable_norm_q.congr ?_
      intro n
      simp
    exact FormalMultilinearSeries.le_radius_of_summable_norm
      (FormalMultilinearSeries.ofScalars ℝ c) hsummable_norm_series
  · intro y hy_mem hy_ball
    have hy_abs : |y| < r := by
      rw [Metric.mem_eball, edist_dist] at hy_ball
      have hy_dist : dist y 0 < r := (ENNReal.ofReal_lt_ofReal_iff hr).1 hy_ball
      simpa [Real.dist_eq] using hy_dist
    have hy_lt : -r < y ∧ y < r := by
      exact abs_lt.1 hy_abs
    have hxy : a + y ∈ Set.Ioo (a - r) (a + r) := by
      constructor <;> linarith
    rcases hc (a + y) hxy with ⟨hsummable_xy, hEq_xy⟩
    have hSubtype :
        SubtypeExtension (Set.Ioo (a - r) (a + r)) f (a + y) = f ⟨a + y, hxy⟩ := by
      simp [SubtypeExtension, hxy]
    have hHasSum_xy :
        HasSum (fun n : ℕ => c n * ((a + y) - a) ^ n)
          (SubtypeExtension (Set.Ioo (a - r) (a + r)) f (a + y)) := by
      rw [hSubtype, hEq_xy]
      exact hsummable_xy.hasSum
    have hHasSum_y :
        HasSum (fun n : ℕ => c n * y ^ n)
          (SubtypeExtension (Set.Ioo (a - r) (a + r)) f (a + y)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hHasSum_xy
    exact hHasSum_y.congr (by
      intro n
      simp [smul_eq_mul, mul_comm])

/-- Helper for Proposition 4.2.2: one-step coefficient recursion for
`iteratedFDerivSeries` evaluated at all-ones. -/
lemma helperForProposition_4_2_2_iteratedFDerivSeriesCoeffOnes_step
    (c : ℕ → ℝ) (k n : ℕ) :
    (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries (k + 1)).coeff n)
      (fun _ : Fin (k + 1) => (1 : ℝ))
      =
    (n + 1 : ℝ) *
      (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries k).coeff (n + 1))
        (fun _ : Fin k => (1 : ℝ)) := by
  have htail : Fin.tail (fun _ : Fin (k + 1) => (1 : ℝ)) = fun _ : Fin k => (1 : ℝ) := by
    funext i
    simp [Fin.tail]
  rw [show ((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries (k + 1)).coeff n =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ) ℝ).symm
        (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries k).derivSeries.coeff n) by
      rfl]
  simp [continuousMultilinearCurryLeftEquiv_symm_apply,
    FormalMultilinearSeries.derivSeries_coeff_one, nsmul_eq_mul, htail]

/-- Helper for Proposition 4.2.2: closed-form coefficients for
`iteratedFDerivSeries` of `ofScalars`, evaluated at all-ones. -/
lemma helperForProposition_4_2_2_iteratedFDerivSeriesCoeffOnes_closedForm
    (c : ℕ → ℝ) (k n : ℕ) :
    (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries k).coeff n)
      (fun _ : Fin k => (1 : ℝ))
      =
    c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) := by
  induction k generalizing n with
  | zero =>
      have hn : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      calc
        (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries 0).coeff n)
            (fun _ : Fin 0 => (1 : ℝ))
            = c n := by
                change (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries 0) n
                  (fun _ : Fin n => (1 : ℝ))
                  (fun _ : Fin 0 => (1 : ℝ))) = c n
                simp [FormalMultilinearSeries.iteratedFDerivSeries,
                  ContinuousLinearMap.compFormalMultilinearSeries_apply,
                  continuousMultilinearCurryFin0_symm_apply,
                  FormalMultilinearSeries.ofScalars]
        _ = c n * ((Nat.factorial n : ℝ) / (Nat.factorial n : ℝ)) := by
            rw [div_self hn]
            ring
        _ = c (n + 0) * ((Nat.factorial (n + 0) : ℝ) / (Nat.factorial n : ℝ)) := by
            simp
  | succ k ih =>
      rw [helperForProposition_4_2_2_iteratedFDerivSeriesCoeffOnes_step c k n, ih (n + 1)]
      have hn : (Nat.factorial n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hfacn1 : (Nat.factorial (n + 1) : ℝ) = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
        norm_num [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hratio :
          (n + 1 : ℝ) * ((Nat.factorial (n + 1 + k) : ℝ) / (Nat.factorial (n + 1) : ℝ)) =
            ((Nat.factorial (n + 1 + k) : ℝ) / (Nat.factorial n : ℝ)) := by
        rw [hfacn1]
        field_simp [hn]
      calc
        (n + 1 : ℝ) *
            (c (n + 1 + k) * ((Nat.factorial (n + 1 + k) : ℝ) / (Nat.factorial (n + 1) : ℝ)))
            = c (n + 1 + k) *
                ((n + 1 : ℝ) *
                  ((Nat.factorial (n + 1 + k) : ℝ) / (Nat.factorial (n + 1) : ℝ))) := by
                  ring
        _ = c (n + 1 + k) * ((Nat.factorial (n + 1 + k) : ℝ) / (Nat.factorial n : ℝ)) := by
              rw [hratio]
        _ = c (n + (k + 1)) *
              ((Nat.factorial (n + (k + 1)) : ℝ) / (Nat.factorial n : ℝ)) := by
              simp [Nat.add_left_comm, Nat.add_comm]

/-- Helper for Proposition 4.2.2: explicit term formula for
`iteratedFDerivSeries` of `ofScalars`. -/
lemma helperForProposition_4_2_2_iteratedFDerivSeries_term_formula
    (c : ℕ → ℝ) (k n : ℕ) (y : ℝ) :
    (((FormalMultilinearSeries.ofScalars ℝ c).iteratedFDerivSeries k n)
      (fun _ : Fin n => y))
      (fun _ : Fin k => (1 : ℝ))
      = c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * y ^ n := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  calc
    ((p.iteratedFDerivSeries k n) (fun _ : Fin n => y)) (fun _ : Fin k => (1 : ℝ))
        = (((∏ i : Fin n, y) • (p.iteratedFDerivSeries k).coeff n) (fun _ : Fin k => (1 : ℝ))) := by
            simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    _ = (∏ i : Fin n, y) * (((p.iteratedFDerivSeries k).coeff n) (fun _ : Fin k => (1 : ℝ))) := by
          simp [smul_eq_mul]
    _ = y ^ n * (((p.iteratedFDerivSeries k).coeff n) (fun _ : Fin k => (1 : ℝ))) := by
          simp
    _ = y ^ n * (c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ))) := by
          rw [helperForProposition_4_2_2_iteratedFDerivSeriesCoeffOnes_closedForm c k n]
    _ = c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * y ^ n := by
          ring

/-- Helper for Proposition 4.2.2: series formula for `iteratedDerivWithin` on the interval. -/
lemma helperForProposition_4_2_2_iteratedDerivWithin_series_formula
    {a r : ℝ} (hr : 0 < r) (f : Set.Ioo (a - r) (a + r) → ℝ) (c : ℕ → ℝ)
    (hc :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) :
    ∀ k x (hx : x ∈ Set.Ioo (a - r) (a + r)),
      Summable
          (fun n : ℕ =>
            c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n) ∧
        iteratedDerivWithin k (SubtypeExtension (Set.Ioo (a - r) (a + r)) f)
          (Set.Ioo (a - r) (a + r)) x =
          ∑' n : ℕ,
            c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n := by
  intro k x hx
  let E : Set ℝ := Set.Ioo (a - r) (a + r)
  let g : ℝ → ℝ := SubtypeExtension E f
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  let hpow : HasFPowerSeriesWithinOnBall g p E a (ENNReal.ofReal r) :=
    helperForProposition_4_2_2_hasFPowerSeriesWithinOnBall_of_seriesData hr f c hc
  have hSubsetBall : E ⊆ Metric.eball a (ENNReal.ofReal r) := by
    intro y hy
    rcases hy with ⟨hy_left, hy_right⟩
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, abs_sub_comm, ENNReal.ofReal_lt_ofReal_iff hr]
    exact abs_lt.2 (by constructor <;> linarith)
  have ha_mem : a ∈ E := by
    change a ∈ Set.Ioo (a - r) (a + r)
    constructor <;> linarith
  have hAnalyticAux : AnalyticOn ℝ g (insert a E ∩ Metric.eball a (ENNReal.ofReal r)) :=
    hpow.analyticOn
  have hAnalytic : AnalyticOn ℝ g E := by
    refine hAnalyticAux.mono ?_
    intro y hy
    exact ⟨Or.inr hy, hSubsetBall hy⟩
  have hUnique : UniqueDiffOn ℝ E := by
    simpa [E] using uniqueDiffOn_Ioo (a - r) (a + r)
  have hpowk : HasFPowerSeriesWithinOnBall (iteratedFDerivWithin ℝ k g E)
      (p.iteratedFDerivSeries k) E a (ENNReal.ofReal r) :=
    hpow.iteratedFDerivWithin hAnalytic k hUnique ha_mem
  have hxBall : x ∈ Metric.eball a (ENNReal.ofReal r) := by
    rcases hx with ⟨hxL, hxR⟩
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, ENNReal.ofReal_lt_ofReal_iff hr]
    exact abs_lt.2 (by constructor <;> linarith)
  have hHasSumMultilin :
      HasSum (fun n : ℕ => p.iteratedFDerivSeries k n (fun _ : Fin n => x - a))
        (iteratedFDerivWithin ℝ k g E x) := by
    have hy : x ∈ (insert a E) ∩ Metric.eball a (ENNReal.ofReal r) :=
      ⟨Or.inr (by simpa [E] using hx), hxBall⟩
    simpa [E] using hpowk.hasSum_sub (y := x) hy
  let evalOnes : (ℝ [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ) ℝ (fun _ : Fin k => (1 : ℝ))
  have hHasSumScalar :
      HasSum
        (fun n : ℕ =>
          (p.iteratedFDerivSeries k n (fun _ : Fin n => x - a)) (fun _ : Fin k => (1 : ℝ)))
        ((iteratedFDerivWithin ℝ k g E x) (fun _ : Fin k => (1 : ℝ))) := by
    simpa [evalOnes, Function.comp] using
      hHasSumMultilin.map evalOnes evalOnes.continuous
  have hTerm :
      (fun n : ℕ =>
        (p.iteratedFDerivSeries k n (fun _ : Fin n => x - a)) (fun _ : Fin k => (1 : ℝ))) =
      (fun n : ℕ =>
        c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n) := by
    funext n
    simpa [p] using helperForProposition_4_2_2_iteratedFDerivSeries_term_formula c k n (x - a)
  have hHasSumTarget :
      HasSum
        (fun n : ℕ =>
          c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n)
        ((iteratedFDerivWithin ℝ k g E x) (fun _ : Fin k => (1 : ℝ))) := by
    rw [← hTerm]
    exact hHasSumScalar
  constructor
  · exact hHasSumTarget.summable
  · calc
      iteratedDerivWithin k g E x = (iteratedFDerivWithin ℝ k g E x) (fun _ : Fin k => (1 : ℝ)) := by
        symm
        exact iteratedDerivWithin_eq_iteratedFDerivWithin
      _ = ∑' n : ℕ,
            c (n + k) * ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) * (x - a) ^ n := by
          exact hHasSumTarget.tsum_eq.symm

/-- Helper for Proposition 4.2.2: the interval power-series representation implies that all
iterated subtype derivatives are once differentiable. -/
lemma helperForProposition_4_2_2_onceDifferentiable_all_orders_of_analytic
    {a r : ℝ} (hr : 0 < r) (f : Set.Ioo (a - r) (a + r) → ℝ) (c : ℕ → ℝ)
    (hc :
      ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) :
    ∀ n : ℕ,
      IsOnceDifferentiableSub (Set.Ioo (a - r) (a + r))
        (IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f n) := by
  let E : Set ℝ := Set.Ioo (a - r) (a + r)
  let hpow : HasFPowerSeriesWithinOnBall
      (SubtypeExtension E f)
      (FormalMultilinearSeries.ofScalars ℝ c)
      E a (ENNReal.ofReal r) :=
    helperForProposition_4_2_2_hasFPowerSeriesWithinOnBall_of_seriesData hr f c hc
  have ha_mem : a ∈ E := by
    change a ∈ Set.Ioo (a - r) (a + r)
    constructor <;> linarith
  have hSubsetBall : E ⊆ Metric.eball a (ENNReal.ofReal r) := by
    intro x hx
    rcases hx with ⟨hx_left, hx_right⟩
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, abs_sub_comm, ENNReal.ofReal_lt_ofReal_iff hr]
    exact abs_lt.2 (by constructor <;> linarith)
  have hAnalyticAux : AnalyticOn ℝ (SubtypeExtension E f) (insert a E ∩ Metric.eball a (ENNReal.ofReal r)) :=
    hpow.analyticOn
  have hAnalytic : AnalyticOn ℝ (SubtypeExtension E f) E := by
    refine hAnalyticAux.mono ?_
    intro x hx
    exact ⟨Or.inr hx, hSubsetBall hx⟩
  have hUnique : UniqueDiffOn ℝ E := by
    simpa [E] using uniqueDiffOn_Ioo (a - r) (a + r)
  have hContDiff : ContDiffOn ℝ ⊤ (SubtypeExtension E f) E :=
    hAnalytic.contDiffOn hUnique
  simpa [E] using
    helperForProposition_4_2_2_isOnceDifferentiableSub_of_contDiffOn f hContDiff hUnique

/-- Proposition 4.2.2 (Real analytic functions are `k`-times differentiable):
if `f : (a-r, a+r) → ℝ` has a convergent power-series representation
`f(x) = ∑' n, c n * (x-a)^n` on `(a-r, a+r)`, then for every `k : ℕ`,
`f` is `k`-times differentiable on `(a-r, a+r)`, and the `k`-th iterated derivative
has the termwise differentiated series
`∑' n, c (n+k) * ((n+k)! / n!) * (x-a)^n` (equivalently using
`(n+1)(n+2)...(n+k)`, with empty product `1` when `k = 0`). -/
theorem realAnalyticOnInterval_iteratedDerivative_eq_powerSeries
    {a r : ℝ} (hr : 0 < r) (f : Set.Ioo (a - r) (a + r) → ℝ)
    (hseries :
      ∃ c : ℕ → ℝ,
        ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
          Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
            f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) :
    ∃ c : ℕ → ℝ,
      (∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
        Summable (fun n : ℕ => c n * (x - a) ^ n) ∧
          f ⟨x, hx⟩ = ∑' n : ℕ, c n * (x - a) ^ n) ∧
      ∀ k : ℕ,
        IsKTimesDifferentiableSub (Set.Ioo (a - r) (a + r)) f k ∧
          ∀ x (hx : x ∈ Set.Ioo (a - r) (a + r)),
            Summable
              (fun n : ℕ =>
                c (n + k) *
                  ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) *
                    (x - a) ^ n) ∧
              IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f k ⟨x, hx⟩ =
                ∑' n : ℕ,
                  c (n + k) *
                    ((Nat.factorial (n + k) : ℝ) / (Nat.factorial n : ℝ)) *
                      (x - a) ^ n := by
  rcases hseries with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro k
  cases k with
  | zero =>
      constructor
      · have hNoIso : HasNoIsolatedPoints (Set.Ioo (a - r) (a + r)) :=
          helperForProposition_4_2_2_interval_hasNoIsolatedPoints a r
        simpa [IsKTimesDifferentiableSub, hNoIso]
      · intro x hx
        exact helperForProposition_4_2_2_seriesFormula_kZero f c hc x hx
  | succ k =>
      constructor
      · have hNoIso : HasNoIsolatedPoints (Set.Ioo (a - r) (a + r)) :=
          helperForProposition_4_2_2_interval_hasNoIsolatedPoints a r
        have hOnceAll :
            ∀ n : ℕ,
              IsOnceDifferentiableSub (Set.Ioo (a - r) (a + r))
                (IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f n) :=
          helperForProposition_4_2_2_onceDifferentiable_all_orders_of_analytic hr f c hc
        exact
          helperForProposition_4_2_2_isKTimesDifferentiableSub_of_allOnceDifferentiable
            f hNoIso hOnceAll (Nat.succ k)
      · intro x hx
        rcases
          helperForProposition_4_2_2_iteratedDerivWithin_series_formula hr f c hc (Nat.succ k) x hx with
          ⟨hsum, hSeriesWithin⟩
        refine ⟨hsum, ?_⟩
        calc
          IteratedDerivativeSub (Set.Ioo (a - r) (a + r)) f (Nat.succ k) ⟨x, hx⟩
              = iteratedDerivWithin (Nat.succ k)
                  (SubtypeExtension (Set.Ioo (a - r) (a + r)) f)
                  (Set.Ioo (a - r) (a + r)) x := by
                  exact
                    helperForProposition_4_2_2_iteratedDerivativeSub_eq_iteratedDerivWithin
                      (Set.Ioo (a - r) (a + r)) f (Nat.succ k) x hx
          _ = ∑' n : ℕ,
                c (n + Nat.succ k) *
                  ((Nat.factorial (n + Nat.succ k) : ℝ) / (Nat.factorial n : ℝ)) *
                    (x - a) ^ n := hSeriesWithin


end Section02
end Chap04
