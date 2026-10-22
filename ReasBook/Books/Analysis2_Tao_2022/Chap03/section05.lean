/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap03
section Section05

/-- Definition 3.8: (Finite sum of real-valued functions) Let (X,d_X) be a metric
space and let f^{(1)},...,f^{(N)} : X -> Real. The finite sum sum_{i=1}^N f^{(i)} :
X -> Real is defined by (sum_{i=1}^N f^{(i)})(x) = sum_{i=1}^N f^{(i)}(x). -/
def finiteSumRealFunctions {X : Type*} {N : ℕ} (f : Fin N → X → Real) : X → Real :=
  fun x => Finset.univ.sum (fun i => f i x)

/-- The family of three functions `x`, `x^2`, and `x^3` indexed by `Fin 3`. -/
def example351_fi : Fin 3 → ℝ → ℝ :=
  ![(fun x : ℝ => x), (fun x : ℝ => x ^ 2), (fun x : ℝ => x ^ 3)]

/-- Example 3.5.1: Let `f^{(1)}(x) = x`, `f^{(2)}(x) = x^2`, and `f^{(3)}(x) = x^3`.
Define `f := ∑_{i=1}^3 f^{(i)}`, so that `f(x) = x + x^2 + x^3`. -/
def example351_f : ℝ → ℝ :=
  finiteSumRealFunctions example351_fi

/-- The finite sum of `example351_fi` evaluates to `x + x^2 + x^3`. -/
lemma example351_f_apply (x : ℝ) :
    example351_f x = x + x ^ 2 + x ^ 3 := by
  simp [example351_f, finiteSumRealFunctions, example351_fi, Fin.sum_univ_three]

/-- Helper for Text 3.5.2: choose centers and bounds for a bounded family. -/
lemma helperForText_3_5_2_chooseData
    {X Y : Type*} [Nonempty X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (f : Fin n → X → Y)
    (hfb : ∀ i, ∃ y0 : Y, ∃ M : ℝ, ∀ x : X, dist (f i x) y0 ≤ M) :
    ∃ c : Fin n → Y, ∃ B : Fin n → ℝ, ∀ i x, dist (f i x) (c i) ≤ B i := by
  classical
  choose c hc using hfb
  choose B hB using hc
  refine ⟨c, B, ?_⟩
  intro i x
  exact hB i x

/-- Helper for Text 3.5.2: extend a pointwise bound to `max (B i) 0`. -/
lemma helperForText_3_5_2_dist_le_maxBound
    {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} {f : Fin n → X → Y} {c : Fin n → Y} {B : Fin n → ℝ}
    {i : Fin n} {x : X} (h : dist (f i x) (c i) ≤ B i) :
    dist (f i x) (c i) ≤ max (B i) 0 := by
  exact le_trans h (le_max_left _ _)

/-- Helper for Text 3.5.2: dist between sums is bounded by sum of pointwise dists. -/
lemma helperForText_3_5_2_dist_sum_sum_le
    {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (f : Fin n → X → Y) (c : Fin n → Y) (x : X) :
    dist (Finset.univ.sum (fun i => f i x))
      (Finset.univ.sum (fun i => c i))
      ≤ Finset.univ.sum (fun i => dist (f i x) (c i)) := by
  simpa using
    (dist_sum_sum_le (s := Finset.univ) (f := fun i => f i x) (a := fun i => c i))

/-- Helper for Text 3.5.2: sum of pointwise dists is bounded by sum of max bounds. -/
lemma helperForText_3_5_2_sum_dist_le_sum_max
    {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (f : Fin n → X → Y) (c : Fin n → Y) (B : Fin n → ℝ)
    (hcB : ∀ i x, dist (f i x) (c i) ≤ B i) (x : X) :
    Finset.univ.sum (fun i => dist (f i x) (c i))
      ≤ Finset.univ.sum (fun i => max (B i) 0) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  exact helperForText_3_5_2_dist_le_maxBound (hcB i x)

/-- Text 3.5.2: [Finite sums of bounded functions are bounded] Let `X` be a nonempty set and
let `(Y, d_Y)` be a metric space, with `Y` a normed vector space and `d_Y(u,v)=‖u-v‖`.
If `f^{(1)}, …, f^{(n)} ∈ B(X → Y)`, then the pointwise sum
`f(x)=∑_{i=1}^n f^{(i)}(x)` is bounded, hence `f ∈ B(X → Y)`. -/
theorem finiteSum_boundedFunctions
    {X Y : Type*} [Nonempty X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (f : Fin n → X → Y)
    (hfb : ∀ i, ∃ y0 : Y, ∃ M : ℝ, ∀ x : X, dist (f i x) y0 ≤ M) :
    ∃ y0 : Y, ∃ M : ℝ, ∀ x : X,
      dist (Finset.univ.sum (fun i => f i x)) y0 ≤ M := by
  classical
  rcases helperForText_3_5_2_chooseData f hfb with ⟨c, B, hcB⟩
  let y0 : Y := Finset.univ.sum (fun i => c i)
  let M : ℝ := Finset.univ.sum (fun i => max (B i) 0)
  refine ⟨y0, M, ?_⟩
  intro x
  have h1 :
      dist (Finset.univ.sum (fun i => f i x)) (Finset.univ.sum (fun i => c i))
        ≤ Finset.univ.sum (fun i => dist (f i x) (c i)) :=
    helperForText_3_5_2_dist_sum_sum_le f c x
  have h2 :
      Finset.univ.sum (fun i => dist (f i x) (c i))
        ≤ Finset.univ.sum (fun i => max (B i) 0) :=
    helperForText_3_5_2_sum_dist_le_sum_max f c B hcB x
  have h3 :
      dist (Finset.univ.sum (fun i => f i x)) (Finset.univ.sum (fun i => c i))
        ≤ Finset.univ.sum (fun i => max (B i) 0) :=
    le_trans h1 h2
  simpa [y0, M] using h3

/-- Text 3.5.3: [Finite sums of continuous functions are continuous] Let `(X, d_X)` be a metric
space and let `Y` be a normed vector space (with its metric). If
`f^{(1)}, …, f^{(n)} : X → Y` are continuous, then `f := ∑_{i=1}^n f^{(i)}` is continuous. -/
theorem finiteSum_continuousFunctions
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {n : ℕ} (f : Fin n → X → Y) (hfc : ∀ i, Continuous (f i)) :
    Continuous (fun x => Finset.univ.sum (fun i => f i x)) := by
  refine continuous_finset_sum (s := Finset.univ) ?_
  intro i hi
  exact hfc i

/-- Convergence mode for a series of functions: pointwise or uniform. -/
inductive SeriesConvergenceMode
  | pointwise
  | uniform

/-- Partial sum function `S_N(x) = ∑_{n=1}^N f^{(n)}(x)`. -/
def seriesPartialSum {X : Type*} (f : ℕ → X → ℝ) (N : ℕ) : X → ℝ :=
  fun x => (Finset.Icc 1 N).sum (fun n => f n x)

/-- Definition 3.9: [Infinite series of functions] Let `(X,d_X)` be a metric space and let
`(f^{(n)})_{n≥1}` be functions `f^{(n)} : X → ℝ`, with partial sums
`S_N(x) = ∑_{n=1}^N f^{(n)}(x)`. Let `f : X → ℝ`. (i) The series `∑_{n=1}^∞ f^{(n)}`
converges pointwise to `f` on `X` if for every `x ∈ X`, `lim_{N→∞} S_N(x) = f(x)`.
(ii) The series converges uniformly to `f` on `X` if `S_N → f` uniformly on `X`, i.e.
`lim_{N→∞} sup_{x∈X} |S_N(x) - f(x)| = 0`. -/
def seriesConverges {X : Type*} [MetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ) (mode : SeriesConvergenceMode) : Prop :=
  match mode with
  | SeriesConvergenceMode.pointwise =>
      ∀ x, Filter.Tendsto (fun N => seriesPartialSum f N x) Filter.atTop (nhds (g x))
  | SeriesConvergenceMode.uniform =>
      TendstoUniformly (fun N => seriesPartialSum f N) g Filter.atTop

/-- A real-valued function on `X` is bounded if there exists `M ≥ 0` with `|f x| ≤ M` for all `x`. -/
def IsBoundedRealFunction {X : Type*} (f : X → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X, |f x| ≤ M

/-- Definition 3.10: [Sup norm] Let `X` be a set and let `f : X → ℝ` be bounded.
The sup norm (uniform norm) is `‖f‖∞ = sup { |f(x)| : x ∈ X }`, and if `X = ∅`
then `‖f‖∞ = 0`. -/
noncomputable def supNorm {X : Type*} (f : {f : X → ℝ // IsBoundedRealFunction f}) : ℝ :=
  sSup (Set.range fun x => |f.1 x|)

/-- Helper for Text 3.5.4: bounded above range of absolute values. -/
lemma helperForText_3_5_4_bddAbove_range_abs {X : Type*}
    (f : {f : X → ℝ // IsBoundedRealFunction f}) :
    BddAbove (Set.range (fun x : X => |f.1 x|)) := by
  rcases f.2 with ⟨M, _, hM⟩
  refine ⟨M, ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact hM x

/-- Helper for Text 3.5.4: pointwise bound by the sup norm. -/
lemma helperForText_3_5_4_abs_le_supNorm {X : Type*}
    (f : {f : X → ℝ // IsBoundedRealFunction f}) (x : X) :
    |f.1 x| ≤ supNorm f := by
  have hbdd : BddAbove (Set.range (fun x : X => |f.1 x|)) :=
    helperForText_3_5_4_bddAbove_range_abs f
  have hx : |f.1 x| ∈ Set.range (fun x : X => |f.1 x|) := by
    exact ⟨x, rfl⟩
  have hle : |f.1 x| ≤ sSup (Set.range (fun x : X => |f.1 x|)) :=
    le_csSup hbdd hx
  simpa [supNorm] using hle

/-- Text 3.5.4: [Finiteness and nonnegativity of the sup norm] Let `X` be a nonempty
set and let `f : X → ℝ` be bounded. Define `‖f‖∞ := sup_{x∈X} |f(x)|`. Then
`‖f‖∞ ∈ [0,∞)`, in particular it is finite and nonnegative. -/
theorem supNorm_nonneg {X : Type*} [Nonempty X]
    (f : {f : X → ℝ // IsBoundedRealFunction f}) :
    0 ≤ supNorm f := by
  classical
  let x0 : X := Classical.choice (inferInstance : Nonempty X)
  have h0 : 0 ≤ |f.1 x0| := abs_nonneg (f.1 x0)
  have hle : |f.1 x0| ≤ supNorm f := helperForText_3_5_4_abs_le_supNorm f x0
  exact le_trans h0 hle

/-- Helper for Theorem 3.5: rewrite `seriesPartialSum` as a `Finset.range` sum. -/
lemma helperForTheorem_3_5_seriesPartialSum_eq_sum_range_succ
    {X : Type*} (f : ℕ → X → ℝ) (N : ℕ) (x : X) :
    seriesPartialSum f N x = (Finset.range N).sum (fun n => f (n + 1) x) := by
  classical
  have hIcc : (Finset.Icc 1 N) = Finset.Ico 1 (N + 1) := by
    simpa using (Finset.Ico_succ_right_eq_Icc (a := 1) (b := N)).symm
  simp [seriesPartialSum, hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_comm]

/-- Helper for Theorem 3.5: pointwise norm bound by the sup norm. -/
lemma helperForTheorem_3_5_norm_le_supNorm
    {X : Type*} {f0 : X → ℝ} (hbf : IsBoundedRealFunction f0) (x : X) :
    ‖f0 x‖ ≤ supNorm ⟨f0, hbf⟩ := by
  have h := helperForText_3_5_4_abs_le_supNorm (f := ⟨f0, hbf⟩) x
  simpa [Real.norm_eq_abs] using h

/-- Helper for Theorem 3.5: uniform convergence of partial sums to the `tsum`. -/
lemma helperForTheorem_3_5_tendstoUniformly_seriesPartialSum_tsum
    {X : Type*} [MetricSpace X] (f : ℕ → X → ℝ)
    (hbounded : ∀ n, IsBoundedRealFunction (f n))
    (hsum : Summable (fun n => supNorm ⟨f n, hbounded n⟩)) :
    TendstoUniformly (fun N => seriesPartialSum f N)
      (fun x => ∑' n, f (n + 1) x) Filter.atTop := by
  have hsum' : Summable (fun n => supNorm ⟨f (n + 1), hbounded (n + 1)⟩) := by
    simpa [Function.comp] using (Summable.comp_injective hsum Nat.succ_injective)
  have hbound :
      ∀ n x, ‖f (n + 1) x‖ ≤ supNorm ⟨f (n + 1), hbounded (n + 1)⟩ := by
    intro n x
    exact helperForTheorem_3_5_norm_le_supNorm (hbounded (n + 1)) x
  have hunif :
      TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f (n + 1) x)
        (fun x => ∑' n, f (n + 1) x) Filter.atTop :=
    tendstoUniformly_tsum_nat hsum' hbound
  have hcongr :
      (fun N => seriesPartialSum f N) =ᶠ[Filter.atTop]
        (fun N x => ∑ n ∈ Finset.range N, f (n + 1) x) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    funext x
    exact helperForTheorem_3_5_seriesPartialSum_eq_sum_range_succ f N x
  exact (tendstoUniformly_congr hcongr).2 hunif

/-- Helper for Theorem 3.5: continuity of each partial sum. -/
lemma helperForTheorem_3_5_seriesPartialSum_continuous
    {X : Type*} [MetricSpace X] (f : ℕ → X → ℝ)
    (hcont : ∀ n, Continuous (f n)) :
    ∀ N, Continuous (seriesPartialSum f N) := by
  intro N
  unfold seriesPartialSum
  refine (continuous_finset_sum (s := Finset.Icc 1 N) ?_)
  intro n hn
  exact hcont n

/-- Theorem 3.5: [Weierstrass M-test] Let `(X,d)` be a metric space and let
`(f^{(n)})` be a sequence of bounded real-valued continuous functions on `X`.
Assume the series `∑ ‖f^{(n)}‖∞` converges. Then the series of functions
`∑ f^{(n)}` converges uniformly on `X` to a function `f : X → ℝ`, and `f` is
continuous on `X`. -/
theorem weierstrass_M_test {X : Type*} [MetricSpace X] (f : ℕ → X → ℝ)
    (hcont : ∀ n, Continuous (f n))
    (hbounded : ∀ n, IsBoundedRealFunction (f n))
    (hsum : Summable (fun n => supNorm ⟨f n, hbounded n⟩)) :
    ∃ g : X → ℝ,
      seriesConverges f g SeriesConvergenceMode.uniform ∧
      Continuous g := by
  let g : X → ℝ := fun x => ∑' n, f (n + 1) x
  have hunif :
      TendstoUniformly (fun N => seriesPartialSum f N) g Filter.atTop :=
    helperForTheorem_3_5_tendstoUniformly_seriesPartialSum_tsum f hbounded hsum
  have hpartial : ∀ N, Continuous (seriesPartialSum f N) :=
    helperForTheorem_3_5_seriesPartialSum_continuous f hcont
  have hcontg : Continuous g := by
    have h_eventually :
        ∃ᶠ N in Filter.atTop, Continuous (seriesPartialSum f N) :=
      Filter.Frequently.of_forall hpartial
    exact TendstoUniformly.continuous hunif h_eventually
  refine ⟨g, ?_, hcontg⟩
  simpa [seriesConverges] using hunif

/-- The geometric series term function on `(-1,1)` given by `x ↦ x^n`. -/
def geometricSeriesTermOnIoo (n : ℕ) (x : {x : ℝ // x ∈ Set.Ioo (-1) 1}) : ℝ :=
  (x : ℝ) ^ n

/-- The geometric series sum function on `(-1,1)` given by `x ↦ x/(1-x)`. -/
noncomputable def geometricSeriesSumOnIoo (x : {x : ℝ // x ∈ Set.Ioo (-1) 1}) : ℝ :=
  (x : ℝ) / (1 - (x : ℝ))

/-- Helper for Example 3.5.2: closed form for the geometric series partial sum on `(-1,1)`. -/
lemma helperForExample_3_5_2_seriesPartialSum_closedForm
    (x : {x : ℝ // x ∈ Set.Ioo (-1) 1}) (N : ℕ) :
    seriesPartialSum geometricSeriesTermOnIoo N x =
      ((x : ℝ) - (x : ℝ) ^ (N + 1)) / (1 - (x : ℝ)) := by
  have hxne : (x : ℝ) ≠ 1 := ne_of_lt x.2.2
  have hmn : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have hIcc : (Finset.Icc 1 N) = Finset.Ico 1 (N + 1) := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  simp [seriesPartialSum, geometricSeriesTermOnIoo, hIcc, geom_sum_Ico' hxne hmn, pow_one]

/-- Helper for Example 3.5.2: distance from partial sum to limit in closed form. -/
lemma helperForExample_3_5_2_dist_to_limit_closedForm
    (x : {x : ℝ // x ∈ Set.Ioo (-1) 1}) (N : ℕ) :
    dist (seriesPartialSum geometricSeriesTermOnIoo N x) (geometricSeriesSumOnIoo x) =
      |(x : ℝ) ^ (N + 1) / (1 - (x : ℝ))| := by
  have hsum := helperForExample_3_5_2_seriesPartialSum_closedForm x N
  have hcalc : ((x : ℝ) - (x : ℝ) ^ (N + 1)) - (x : ℝ) = - (x : ℝ) ^ (N + 1) := by
    ring
  simp [Real.dist_eq, hsum, geometricSeriesSumOnIoo, div_sub_div_same, hcalc, neg_div, abs_neg]

/-- Helper for Example 3.5.2: pointwise convergence of the geometric series on `(-1,1)`. -/
lemma helperForExample_3_5_2_pointwiseConvergence :
    seriesConverges geometricSeriesTermOnIoo geometricSeriesSumOnIoo
      SeriesConvergenceMode.pointwise := by
  intro x
  have hxabs : |(x : ℝ)| < 1 := (abs_lt).2 x.2
  have hpow0 :
      Filter.Tendsto (fun n : ℕ => (x : ℝ) ^ n) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hxabs
  have hpow :
      Filter.Tendsto (fun n : ℕ => (x : ℝ) ^ (n + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hpow0.comp (Filter.tendsto_add_atTop_nat 1)
  have hnum :
      Filter.Tendsto (fun n : ℕ => (x : ℝ) - (x : ℝ) ^ (n + 1)) Filter.atTop
        (nhds (x : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hpow)
  have hdiv :
      Filter.Tendsto
        (fun n : ℕ => ((x : ℝ) - (x : ℝ) ^ (n + 1)) / (1 - (x : ℝ))) Filter.atTop
        (nhds ((x : ℝ) / (1 - (x : ℝ)))) :=
    hnum.div_const (1 - (x : ℝ))
  simpa [geometricSeriesSumOnIoo, helperForExample_3_5_2_seriesPartialSum_closedForm] using hdiv

/-- Helper for Example 3.5.2: explicit real value `x_N = 1 - 1/2^(N+1)`. -/
noncomputable def helperForExample_3_5_2_xNValue (N : ℕ) : ℝ :=
  1 - 1 / (2 : ℝ) ^ (N + 1)

/-- Helper for Example 3.5.2: the point `x_N` is at least `1/2`. -/
lemma helperForExample_3_5_2_xN_ge_half (N : ℕ) :
    (1 / 2 : ℝ) ≤ helperForExample_3_5_2_xNValue N := by
  have htwo : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hpow_le :
      (1 : ℝ) / (2 : ℝ) ^ (N + 1) ≤ (1 : ℝ) / (2 : ℝ) ^ 1 := by
    exact one_div_pow_le_one_div_pow_of_le (a := (2 : ℝ)) htwo
      (Nat.succ_le_succ (Nat.zero_le N))
  have hpow_le' : (1 : ℝ) / (2 : ℝ) ^ (N + 1) ≤ (1 : ℝ) / (2 : ℝ) := by
    simpa using hpow_le
  dsimp [helperForExample_3_5_2_xNValue]
  linarith

/-- Helper for Example 3.5.2: the point `x_N` lies in `(-1,1)`. -/
lemma helperForExample_3_5_2_xN_mem (N : ℕ) :
    helperForExample_3_5_2_xNValue N ∈ Set.Ioo (-1) 1 := by
  have hx_ge_half : (1 / 2 : ℝ) ≤ helperForExample_3_5_2_xNValue N :=
    helperForExample_3_5_2_xN_ge_half N
  have hx_pos : 0 < helperForExample_3_5_2_xNValue N := by
    linarith
  have hbasepos : (0 : ℝ) < (2 : ℝ) := by
    norm_num
  have hpowpos : 0 < (2 : ℝ) ^ (N + 1) := by
    exact pow_pos hbasepos _
  have hpos : 0 < (1 : ℝ) / (2 : ℝ) ^ (N + 1) := by
    exact one_div_pos.mpr hpowpos
  have hx_lt_one : helperForExample_3_5_2_xNValue N < 1 := by
    dsimp [helperForExample_3_5_2_xNValue]
    linarith
  have hx_gt_negone : (-1 : ℝ) < helperForExample_3_5_2_xNValue N := by
    linarith
  exact ⟨hx_gt_negone, hx_lt_one⟩

/-- Helper for Example 3.5.2: for each `N`, some point has error at least `1/2`. -/
lemma helperForExample_3_5_2_counterexample_large_error (N : ℕ) :
    ∃ x : {x : ℝ // x ∈ Set.Ioo (-1) 1},
      (1 / 2 : ℝ) ≤
        dist (seriesPartialSum geometricSeriesTermOnIoo N x) (geometricSeriesSumOnIoo x) := by
  let xNval : ℝ := helperForExample_3_5_2_xNValue N
  have hxN_mem : xNval ∈ Set.Ioo (-1) 1 := by
    simpa [xNval] using helperForExample_3_5_2_xN_mem N
  let xN : {x : ℝ // x ∈ Set.Ioo (-1) 1} := ⟨xNval, hxN_mem⟩
  refine ⟨xN, ?_⟩
  have hdist :
      dist (seriesPartialSum geometricSeriesTermOnIoo N xN) (geometricSeriesSumOnIoo xN) =
        |xNval ^ (N + 1) / (1 - xNval)| := by
    simpa [xNval] using helperForExample_3_5_2_dist_to_limit_closedForm xN N
  have hx_ge_half : (1 / 2 : ℝ) ≤ xNval := by
    simpa [xNval] using helperForExample_3_5_2_xN_ge_half N
  have hx_nonneg : 0 ≤ xNval := by
    linarith
  have hnum_nonneg : 0 ≤ xNval ^ (N + 1) := by
    exact pow_nonneg hx_nonneg _
  have hx_lt_one : xNval < 1 := hxN_mem.2
  have hden_pos : 0 < 1 - xNval := by
    linarith
  have hden_nonneg : 0 ≤ 1 - xNval := le_of_lt hden_pos
  have hratio_nonneg : 0 ≤ xNval ^ (N + 1) / (1 - xNval) := by
    exact div_nonneg hnum_nonneg hden_nonneg
  have habs :
      |xNval ^ (N + 1) / (1 - xNval)| = xNval ^ (N + 1) / (1 - xNval) := by
    exact abs_of_nonneg hratio_nonneg
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    linarith
  have hpow_le :
      (1 / 2 : ℝ) ^ (N + 1) ≤ xNval ^ (N + 1) := by
    exact pow_le_pow_left₀ hhalf_nonneg hx_ge_half (N + 1)
  have hpow_le' : (1 : ℝ) / (2 : ℝ) ^ (N + 1) ≤ xNval ^ (N + 1) := by
    simpa [one_div_pow] using hpow_le
  have hden_eq : 1 - xNval = (1 : ℝ) / (2 : ℝ) ^ (N + 1) := by
    dsimp [xNval, helperForExample_3_5_2_xNValue]
    ring
  have hineq : 1 - xNval ≤ xNval ^ (N + 1) := by
    simpa [hden_eq] using hpow_le'
  have hratio : (1 : ℝ) ≤ xNval ^ (N + 1) / (1 - xNval) := by
    exact (one_le_div hden_pos).2 hineq
  have hdist_ge_one : (1 : ℝ) ≤
      dist (seriesPartialSum geometricSeriesTermOnIoo N xN) (geometricSeriesSumOnIoo xN) := by
    have habs_le : (1 : ℝ) ≤ |xNval ^ (N + 1) / (1 - xNval)| := by
      simpa [habs] using hratio
    simpa [hdist] using habs_le
  linarith

/-- Example 3.5.2: Pointwise but not uniform convergence of a geometric series.
For `f^{(n)}(x) = x^n` on `(-1,1)`, the series converges pointwise to `x/(1-x)`,
but the convergence is not uniform on `(-1,1)`. -/
theorem example352_pointwise_not_uniform :
    seriesConverges geometricSeriesTermOnIoo geometricSeriesSumOnIoo
        SeriesConvergenceMode.pointwise ∧
      ¬ seriesConverges geometricSeriesTermOnIoo geometricSeriesSumOnIoo
        SeriesConvergenceMode.uniform := by
  refine ⟨helperForExample_3_5_2_pointwiseConvergence, ?_⟩
  intro huniform
  have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by
    norm_num
  have hε := (Metric.tendstoUniformly_iff).1 huniform (1 / 2 : ℝ) hhalfpos
  rcases Filter.eventually_atTop.1 hε with ⟨N, hN⟩
  rcases helperForExample_3_5_2_counterexample_large_error N with ⟨x, hx⟩
  have hN' : dist (geometricSeriesSumOnIoo x)
      (seriesPartialSum geometricSeriesTermOnIoo N x) < (1 / 2 : ℝ) :=
    hN N (le_rfl) x
  have hN'' :
      dist (seriesPartialSum geometricSeriesTermOnIoo N x) (geometricSeriesSumOnIoo x)
        < (1 / 2 : ℝ) := by
    simpa [dist_comm] using hN'
  exact (not_lt_of_ge hx) hN''

/-- Proposition 3.17: If a series of functions converges uniformly to `f` on `X`,
then it converges pointwise to `f` on `X`. -/
theorem seriesConverges_pointwise_of_uniform {X : Type*} [MetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ) :
    seriesConverges f g SeriesConvergenceMode.uniform →
      seriesConverges f g SeriesConvergenceMode.pointwise := by
  intro hunif
  simp [seriesConverges] at hunif ⊢
  intro x
  simpa using (TendstoUniformly.tendsto_at hunif x)

/-- The interval `(-2,1)` as a subtype of `ℝ`. -/
def example356_X : Type := {x : ℝ // x ∈ Set.Ioo (-2 : ℝ) 1}

/-- The function `x ↦ 2x` on `(-2,1)`. -/
def example356_f : example356_X → ℝ :=
  fun x => 2 * x.1

/-- The function `x ↦ 2x` on `(-2,1)` is bounded. -/
lemma example356_f_bounded : IsBoundedRealFunction example356_f := by
  refine ⟨4, by norm_num, ?_⟩
  intro x
  have hx_lower : (-2 : ℝ) ≤ x.1 := le_of_lt x.2.1
  have hx_upper : x.1 ≤ 2 := by
    linarith [x.2.2]
  have hx_abs_le_two : |x.1| ≤ 2 :=
    (abs_le).2 ⟨hx_lower, hx_upper⟩
  calc
    |example356_f x| = |(2 : ℝ) * x.1| := by rfl
    _ = |(2 : ℝ)| * |x.1| := by
      rw [abs_mul]
    _ ≤ |(2 : ℝ)| * 2 :=
      mul_le_mul_of_nonneg_left hx_abs_le_two (abs_nonneg (2 : ℝ))
    _ = 4 := by norm_num

/-- The bounded function `x ↦ 2x` on `(-2,1)` packaged for `supNorm`. -/
def example356_f_boundedSubtype : {f : example356_X → ℝ // IsBoundedRealFunction f} :=
  ⟨example356_f, example356_f_bounded⟩

/-- Pointwise bound for `|2x|` on `(-2,1)`. -/
lemma example356_abs_value_le_four (x : example356_X) :
    |example356_f x| ≤ 4 := by
  have hx_lower : (-2 : ℝ) ≤ x.1 := le_of_lt x.2.1
  have hx_upper : x.1 ≤ 2 := by
    linarith [x.2.2]
  have hx_abs_le_two : |x.1| ≤ 2 :=
    (abs_le).2 ⟨hx_lower, hx_upper⟩
  calc
    |example356_f x| = |(2 : ℝ) * x.1| := by rfl
    _ = |(2 : ℝ)| * |x.1| := by rw [abs_mul]
    _ ≤ |(2 : ℝ)| * 2 :=
      mul_le_mul_of_nonneg_left hx_abs_le_two (abs_nonneg (2 : ℝ))
    _ = 4 := by norm_num

/-- A canonical point near `-2` that still lies in `(-2,1)`. -/
lemma example356_delta_point_mem_Ioo (a : ℝ) (ha : a < 4) :
    let δ : ℝ := min ((4 - a) / 4) 1
    (-2 + δ) ∈ Set.Ioo (-2 : ℝ) 1 := by
  dsimp
  have hratio_pos : 0 < (4 - a) / 4 := by
    nlinarith
  have hδ_pos : 0 < min ((4 - a) / 4) 1 := by
    exact lt_min hratio_pos (by norm_num)
  have hδ_le_one : min ((4 - a) / 4) 1 ≤ 1 := by
    exact min_le_right _ _
  constructor
  · linarith
  · linarith

/-- Any level strictly below `4` is exceeded by `|2x|` at some point of `(-2,1)`. -/
lemma example356_exists_abs_gt_of_lt_four (a : ℝ) (ha : a < 4) :
    ∃ x : example356_X, a < |example356_f x| := by
  let δ : ℝ := min ((4 - a) / 4) 1
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_right _ _
  have hx_mem : (-2 + δ) ∈ Set.Ioo (-2 : ℝ) 1 := by
    simpa [δ] using example356_delta_point_mem_Ioo a ha
  let x : example356_X := ⟨-2 + δ, hx_mem⟩
  have hx_nonpos : -2 + δ ≤ 0 := by
    linarith [hδ_le_one]
  have hmul_nonpos : (2 : ℝ) * (-2 + δ) ≤ 0 := by
    nlinarith [hx_nonpos]
  have h_abs_eq : |example356_f x| = 4 - 2 * δ := by
    calc
      |example356_f x| = |(2 : ℝ) * (-2 + δ)| := by rfl
      _ = -((2 : ℝ) * (-2 + δ)) := by rw [abs_of_nonpos hmul_nonpos]
      _ = 4 - 2 * δ := by ring
  have hδ_le_ratio : δ ≤ (4 - a) / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hratio_le : 2 + a / 2 ≤ 4 - 2 * δ := by
    have haux : 4 - 2 * ((4 - a) / 4) ≤ 4 - 2 * δ := by
      nlinarith [hδ_le_ratio]
    have haux' : 2 + a / 2 = 4 - 2 * ((4 - a) / 4) := by
      ring
    linarith
  have ha_lt_mid : a < 2 + a / 2 := by
    linarith [ha]
  refine ⟨x, ?_⟩
  rw [h_abs_eq]
  linarith

/-- Upper bound `‖x ↦ 2x‖∞ ≤ 4` on `(-2,1)`. -/
lemma example356_supNorm_le_four :
    supNorm example356_f_boundedSubtype ≤ 4 := by
  have hx0_mem : (0 : ℝ) ∈ Set.Ioo (-2 : ℝ) 1 := by
    constructor <;> norm_num
  let x0 : example356_X := ⟨0, hx0_mem⟩
  have hne :
      (Set.range fun x : example356_X => |example356_f x|).Nonempty := by
    exact ⟨|example356_f x0|, ⟨x0, rfl⟩⟩
  have hupper :
      ∀ y ∈ Set.range (fun x : example356_X => |example356_f x|), y ≤ 4 := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact example356_abs_value_le_four x
  have hle :
      sSup (Set.range fun x : example356_X => |example356_f x|) ≤ 4 :=
    csSup_le hne hupper
  simpa [supNorm, example356_f_boundedSubtype] using hle

/-- Example 3.5.6: (Computing the sup norm) For `X = (-2,1)` and `f(x) = 2x`,
the sup norm `‖f‖∞ = sup_{x∈X} |f(x)|` equals `4`. -/
theorem example356_supNorm_eq :
    supNorm example356_f_boundedSubtype = 4 := by
  refine le_antisymm example356_supNorm_le_four ?_
  by_contra hlt
  have hlt' : supNorm example356_f_boundedSubtype < 4 :=
    lt_of_not_ge hlt
  rcases example356_exists_abs_gt_of_lt_four
      (supNorm example356_f_boundedSubtype) hlt' with ⟨x, hxgt⟩
  have hxsup : |example356_f x| ≤ supNorm example356_f_boundedSubtype :=
    helperForText_3_5_4_abs_le_supNorm example356_f_boundedSubtype x
  exact (not_lt_of_ge hxsup) hxgt

/-- The geometric series term function on `[-r,r]` given by `x ↦ x^n`. -/
def geometricSeriesTermOnIcc (r : ℝ) (n : ℕ) (x : {x : ℝ // x ∈ Set.Icc (-r) r}) : ℝ :=
  (x : ℝ) ^ n

/-- The geometric series sum function on `[-r,r]` given by `x ↦ x/(1-x)`. -/
noncomputable def geometricSeriesSumOnIcc (r : ℝ)
    (x : {x : ℝ // x ∈ Set.Icc (-r) r}) : ℝ :=
  (x : ℝ) / (1 - (x : ℝ))

/-- Helper for Example 3.5.8: bound `|x|` by `r` on `[-r,r]`. -/
lemma helperForExample_3_5_8_abs_coe_le_r {r : ℝ}
    (x : {x : ℝ // x ∈ Set.Icc (-r) r}) :
    |(x : ℝ)| ≤ r := by
  exact (abs_le).2 x.2

/-- Helper for Example 3.5.8: bound `|x^n|` by `r^n` on `[-r,r]`. -/
lemma helperForExample_3_5_8_abs_pow_le_r_pow {r : ℝ} (n : ℕ)
    (x : {x : ℝ // x ∈ Set.Icc (-r) r}) :
    |((x : ℝ) ^ n)| ≤ r ^ n := by
  have hle : |(x : ℝ)| ≤ r := helperForExample_3_5_8_abs_coe_le_r x
  have hpow : |(x : ℝ)| ^ n ≤ r ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) hle _
  have hpow' : |(x : ℝ) ^ n| = |(x : ℝ)| ^ n := by
    simp [abs_pow]
  rw [hpow']
  exact hpow

/-- Helper for Example 3.5.8: compute `‖x ↦ x^n‖∞` on `[-r,r]`. -/
lemma helperForExample_3_5_8_supNorm_term_eq_r_pow {r : ℝ} (hr0 : 0 < r)
    (n : ℕ) (h : IsBoundedRealFunction (geometricSeriesTermOnIcc r n)) :
    supNorm ⟨geometricSeriesTermOnIcc r n, h⟩ = r ^ n := by
  have hbdd :
      BddAbove
        (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
          |geometricSeriesTermOnIcc r n x|) :=
    helperForText_3_5_4_bddAbove_range_abs (f := ⟨geometricSeriesTermOnIcc r n, h⟩)
  have hrmem : r ∈ Set.Icc (-r) r := by
    have hr0' : 0 ≤ r := le_of_lt hr0
    have hleft : -r ≤ r := neg_le_self hr0'
    exact ⟨hleft, le_rfl⟩
  let x0 : {x : ℝ // x ∈ Set.Icc (-r) r} := ⟨r, hrmem⟩
  have hne :
      (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
        |geometricSeriesTermOnIcc r n x|).Nonempty := by
    refine ⟨|geometricSeriesTermOnIcc r n x0|, ?_⟩
    exact ⟨x0, rfl⟩
  have hupper :
      ∀ y ∈ Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
        |geometricSeriesTermOnIcc r n x|, y ≤ r ^ n := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact helperForExample_3_5_8_abs_pow_le_r_pow n x
  have hle :
      sSup (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
          |geometricSeriesTermOnIcc r n x|) ≤ r ^ n :=
    csSup_le hne hupper
  have hx0mem :
      |geometricSeriesTermOnIcc r n x0| ∈
        Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
          |geometricSeriesTermOnIcc r n x| := by
    exact ⟨x0, rfl⟩
  have hnonneg : 0 ≤ r ^ n := by
    exact pow_nonneg (le_of_lt hr0) _
  have hx0val : |geometricSeriesTermOnIcc r n x0| = r ^ n := by
    simp [geometricSeriesTermOnIcc, x0, abs_of_nonneg hnonneg]
  have hge :
      r ^ n ≤
        sSup (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
          |geometricSeriesTermOnIcc r n x|) := by
    have hle' :
        |geometricSeriesTermOnIcc r n x0| ≤
          sSup (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
            |geometricSeriesTermOnIcc r n x|) :=
      le_csSup hbdd hx0mem
    simpa [hx0val] using hle'
  have hsup :
      sSup (Set.range fun x : {x : ℝ // x ∈ Set.Icc (-r) r} =>
          |geometricSeriesTermOnIcc r n x|) = r ^ n := by
    exact le_antisymm hle hge
  simpa [supNorm] using hsup

/-- Helper for Example 3.5.8: shifted geometric series on `|x| < 1`. -/
lemma helperForExample_3_5_8_tsum_pow_succ_eq_div {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, x ^ (n + 1)) = x / (1 - x) := by
  have hx' : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  calc
    (∑' n : ℕ, x ^ (n + 1)) = ∑' n : ℕ, x * x ^ n := by
      refine tsum_congr ?_
      intro n
      simp [pow_succ, mul_comm]
    _ = x * ∑' n : ℕ, x ^ n := by
      simpa using (tsum_mul_left (a := x) (f := fun n : ℕ => x ^ n))
    _ = x * (1 - x)⁻¹ := by
      simp [tsum_geometric_of_norm_lt_one hx']
    _ = x / (1 - x) := by
      simp [div_eq_mul_inv]

/-- Example 3.5.8: [Uniform convergence on `[-r,r]` for a geometric series] Let `0 < r < 1`
and define `f^{(n)}(x) = x^n` on `[-r,r]`. Each `f^{(n)}` is continuous and bounded,
with sup norm `‖f^{(n)}‖∞ = r^n`. The series `∑ f^{(n)}` converges uniformly on `[-r,r]`
to `x/(1-x)`, and `∑ x^n` is pointwise but not uniformly convergent on `(-1,1)`. -/
theorem example358_uniform_convergence_geometric_on_Icc {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∀ n, Continuous (geometricSeriesTermOnIcc r n)) ∧
    (∀ n, IsBoundedRealFunction (geometricSeriesTermOnIcc r n)) ∧
    (∀ n, ∃ h : IsBoundedRealFunction (geometricSeriesTermOnIcc r n),
      supNorm ⟨geometricSeriesTermOnIcc r n, h⟩ = r ^ n) ∧
    seriesConverges (geometricSeriesTermOnIcc r) (geometricSeriesSumOnIcc r)
      SeriesConvergenceMode.uniform ∧
    Continuous (geometricSeriesSumOnIcc r) ∧
    (seriesConverges geometricSeriesTermOnIoo geometricSeriesSumOnIoo
        SeriesConvergenceMode.pointwise ∧
      ¬ seriesConverges geometricSeriesTermOnIoo geometricSeriesSumOnIoo
        SeriesConvergenceMode.uniform) := by
  have hcont : ∀ n, Continuous (geometricSeriesTermOnIcc r n) := by
    intro n
    simpa [geometricSeriesTermOnIcc] using (continuous_subtype_val.pow n)
  have hbounded : ∀ n, IsBoundedRealFunction (geometricSeriesTermOnIcc r n) := by
    intro n
    refine ⟨r ^ n, ?_, ?_⟩
    · exact pow_nonneg (le_of_lt hr0) _
    · intro x
      exact helperForExample_3_5_8_abs_pow_le_r_pow n x
  have hsup :
      ∀ n, ∃ h : IsBoundedRealFunction (geometricSeriesTermOnIcc r n),
        supNorm ⟨geometricSeriesTermOnIcc r n, h⟩ = r ^ n := by
    intro n
    refine ⟨hbounded n, ?_⟩
    exact helperForExample_3_5_8_supNorm_term_eq_r_pow hr0 n (hbounded n)
  have hsum :
      Summable (fun n => supNorm ⟨geometricSeriesTermOnIcc r n, hbounded n⟩) := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one (le_of_lt hr0) hr1
    refine hgeom.congr ?_
    intro n
    exact (helperForExample_3_5_8_supNorm_term_eq_r_pow hr0 n (hbounded n)).symm
  have hunif :
      TendstoUniformly (fun N => seriesPartialSum (geometricSeriesTermOnIcc r) N)
        (fun x => ∑' n, geometricSeriesTermOnIcc r (n + 1) x) Filter.atTop :=
    helperForTheorem_3_5_tendstoUniformly_seriesPartialSum_tsum
      (f := geometricSeriesTermOnIcc r) hbounded hsum
  have hsum_ident :
      (fun x => ∑' n, geometricSeriesTermOnIcc r (n + 1) x) =
        geometricSeriesSumOnIcc r := by
    funext x
    have hxabs : |(x : ℝ)| < 1 := by
      exact lt_of_le_of_lt (helperForExample_3_5_8_abs_coe_le_r x) hr1
    simpa [geometricSeriesTermOnIcc, geometricSeriesSumOnIcc] using
      (helperForExample_3_5_8_tsum_pow_succ_eq_div (x := (x : ℝ)) hxabs)
  have hunif' :
      TendstoUniformly (fun N => seriesPartialSum (geometricSeriesTermOnIcc r) N)
        (geometricSeriesSumOnIcc r) Filter.atTop := by
    simpa [hsum_ident] using hunif
  have hseries :
      seriesConverges (geometricSeriesTermOnIcc r) (geometricSeriesSumOnIcc r)
        SeriesConvergenceMode.uniform := by
    simpa [seriesConverges] using hunif'
  have hpartial :
      ∀ N, Continuous (seriesPartialSum (geometricSeriesTermOnIcc r) N) :=
    helperForTheorem_3_5_seriesPartialSum_continuous
      (f := geometricSeriesTermOnIcc r) hcont
  have hcontg : Continuous (geometricSeriesSumOnIcc r) := by
    have h_eventually :
        ∃ᶠ N in Filter.atTop,
          Continuous (seriesPartialSum (geometricSeriesTermOnIcc r) N) :=
      Filter.Frequently.of_forall hpartial
    exact TendstoUniformly.continuous hunif' h_eventually
  refine ⟨hcont, ?_⟩
  refine ⟨hbounded, ?_⟩
  refine ⟨hsup, ?_⟩
  refine ⟨hseries, ?_⟩
  refine ⟨hcontg, ?_⟩
  exact example352_pointwise_not_uniform

end Section05
end Chap03
