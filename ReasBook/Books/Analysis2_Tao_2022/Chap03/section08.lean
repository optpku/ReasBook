/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap03
section Section08

open scoped Pointwise
open Filter

/-- Definition 3.12: Let `a,b ∈ ℝ` with `a ≤ b`. A polynomial on `[a,b]` is a function
`f : [a,b] → ℝ` for which there exist `n ≥ 0` and coefficients `c₀, …, cₙ ∈ ℝ` such that
`f(x) = ∑_{i=0}^n cᵢ x^i` for all `x ∈ [a,b]`. If `f` is a polynomial and `n` is the
largest index with `cₙ ≠ 0`, then `n` is called the degree of `f`. -/
def IsPolynomialOn (a b : ℝ) (f : Set.Icc a b → ℝ) : Prop :=
  a ≤ b ∧ ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, f x = p.eval x.1

/-- A natural number `n` is the degree of `f` on `[a,b]` if `f` agrees on `[a,b]`
with a nonzero real polynomial of natDegree `n`. -/
def IsPolynomialDegreeOn (a b : ℝ) (f : Set.Icc a b → ℝ) (n : ℕ) : Prop :=
  a ≤ b ∧
    ∃ p : Polynomial ℝ,
      (∀ x : Set.Icc a b, f x = p.eval x.1) ∧ p.natDegree = n ∧ p.coeff n ≠ 0

/-- The specific function `x ↦ 3x^4 + 2x^3 - 4x + 5` on `[1,2]`. -/
def examplePolynomialFunctionOnIcc : Set.Icc (1 : ℝ) 2 → ℝ :=
  fun x => 3 * x.1 ^ 4 + 2 * x.1 ^ 3 - 4 * x.1 + 5

/-- Helper for Example 3.8.2: evaluation of the witness polynomial equals the given function. -/
lemma helperForExample_3_8_2_eval_witness (x : Set.Icc (1 : ℝ) 2) :
    examplePolynomialFunctionOnIcc x =
      (3 * (Polynomial.X : Polynomial ℝ) ^ 4 + 2 * Polynomial.X ^ 3 - 4 * Polynomial.X + 5).eval x.1 := by
  simp [examplePolynomialFunctionOnIcc]

/-- Helper for Example 3.8.2: the witness polynomial has natDegree `4`. -/
lemma helperForExample_3_8_2_natDegree_witness :
    (3 * (Polynomial.X : Polynomial ℝ) ^ 4 + 2 * Polynomial.X ^ 3 - 4 * Polynomial.X + 5).natDegree = 4 := by
  compute_degree!

/-- Helper for Example 3.8.2: the witness polynomial has nonzero coefficient at index `4`. -/
lemma helperForExample_3_8_2_coeff4_witness_ne_zero :
    (3 * (Polynomial.X : Polynomial ℝ) ^ 4 + 2 * Polynomial.X ^ 3 - 4 * Polynomial.X + 5).coeff 4 ≠ 0 := by
  norm_num [Polynomial.coeff_X]

/-- Example 3.8.2: The function `f(x) = 3x^4 + 2x^3 - 4x + 5` on `[1,2]` is a polynomial
of degree `4`. -/
theorem example_3_8_2 :
    IsPolynomialDegreeOn (1 : ℝ) 2 examplePolynomialFunctionOnIcc 4 := by
  refine And.intro ?_ ?_
  · norm_num
  · refine Exists.intro
      (3 * (Polynomial.X : Polynomial ℝ) ^ 4 + 2 * Polynomial.X ^ 3 - 4 * Polynomial.X + 5) ?_
    refine And.intro ?_ ?_
    · intro x
      exact helperForExample_3_8_2_eval_witness x
    · refine And.intro ?_ ?_
      · exact helperForExample_3_8_2_natDegree_witness
      · exact helperForExample_3_8_2_coeff4_witness_ne_zero

/-- The set of bounded continuous functions on `[a,b]` that are polynomial on `[a,b]`. -/
def polynomialFunctionsOnIcc (a b : ℝ) :
    Set (BoundedContinuousFunction (Set.Icc a b) ℝ) :=
  {f | IsPolynomialOn a b f}

/-- Helper for Text 3.8.1: a polynomial bundled as a bounded continuous function belongs to
`polynomialFunctionsOnIcc`. -/
lemma helperForText_3_8_1_polynomial_bcf_mem
    (a b : ℝ) (h : a ≤ b) (p : Polynomial ℝ) :
    BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc a b)) ∈
      polynomialFunctionsOnIcc a b := by
  change IsPolynomialOn a b
    (BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc a b)))
  refine ⟨h, ?_⟩
  refine ⟨p, ?_⟩
  intro x
  simp

/-- Helper for Text 3.8.1: a sup-norm estimate in `C([a,b], ℝ)` transfers to a distance
estimate in `BoundedContinuousFunction (Set.Icc a b) ℝ`. -/
lemma helperForText_3_8_1_dist_mkOfCompact_lt
    (a b ε : ℝ) (f : BoundedContinuousFunction (Set.Icc a b) ℝ) (p : Polynomial ℝ)
    (hnorm : ‖p.toContinuousMapOn (Set.Icc a b) - f.toContinuousMap‖ < ε) :
    dist (BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc a b))) f < ε := by
  let g : BoundedContinuousFunction (Set.Icc a b) ℝ :=
    BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc a b))
  have hdist_toContinuousMap : dist g.toContinuousMap f.toContinuousMap < ε := by
    simpa [g, dist_eq_norm] using hnorm
  have hdist : dist g f < ε := by
    simpa [BoundedContinuousFunction.dist_toContinuousMap] using hdist_toContinuousMap
  simpa [g] using hdist

/-- Helper for Text 3.8.1: every open ball around a bounded continuous function on `[a,b]`
contains a polynomial function. -/
lemma helperForText_3_8_1_exists_polynomial_in_ball
    (a b : ℝ) (h : a ≤ b) (f : BoundedContinuousFunction (Set.Icc a b) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ polynomialFunctionsOnIcc a b, dist g f < ε := by
  rcases exists_polynomial_near_continuousMap a b f.toContinuousMap ε hε with ⟨p, hp⟩
  refine ⟨BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc a b)), ?_, ?_⟩
  · exact helperForText_3_8_1_polynomial_bcf_mem a b h p
  · exact helperForText_3_8_1_dist_mkOfCompact_lt a b ε f p hp

/-- Text 3.8.1: (Weierstrass approximation in closure form) For a closed interval `[a,b]`,
the set of polynomial functions on `[a,b]` is dense (with respect to the uniform norm) in
the space of continuous functions on `[a,b]`. -/
theorem polynomialFunctionsOnIcc_dense
    (a b : ℝ) (h : a ≤ b) :
    Dense (polynomialFunctionsOnIcc a b) := by
  refine Metric.dense_iff.2 ?_
  intro f ε hε
  rcases helperForText_3_8_1_exists_polynomial_in_ball a b h f ε hε with ⟨g, hg, hdist⟩
  refine ⟨g, ?_⟩
  exact ⟨hdist, hg⟩

/-- Helper for Text 3.8.2: for each polynomial, eventually `|exp x - p(x)|` is at least
`exp x / 2`. -/
lemma helperForText_3_8_2_eventually_halfExp_le_absDiff
    (p : Polynomial ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp x / 2 ≤ |Real.exp x - p.eval x| := by
  have hRatioBound : ∀ᶠ x : ℝ in Filter.atTop, |p.eval x / Real.exp x| ≤ (1 / 2 : ℝ) := by
    have hIcc : Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∈ nhds (0 : ℝ) := by
      refine Icc_mem_nhds ?_ ?_
      · norm_num
      · norm_num
    have hEventuallyIcc :
        ∀ᶠ x : ℝ in Filter.atTop,
          p.eval x / Real.exp x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
      (Polynomial.tendsto_div_exp_atTop p).eventually hIcc
    refine hEventuallyIcc.mono ?_
    intro x hx
    exact abs_le.mpr ⟨hx.1, hx.2⟩
  refine hRatioBound.mono ?_
  intro x hx
  have hexpPos : 0 < Real.exp x := Real.exp_pos x
  have hmul : |p.eval x / Real.exp x| * Real.exp x ≤ (1 / 2 : ℝ) * Real.exp x :=
    mul_le_mul_of_nonneg_right hx (le_of_lt hexpPos)
  have hAbsEvalLe : |p.eval x| ≤ Real.exp x / 2 := by
    have hAbsEvalMul : |p.eval x / Real.exp x| * Real.exp x = |p.eval x| := by
      calc
        |p.eval x / Real.exp x| * Real.exp x = (|p.eval x| / Real.exp x) * Real.exp x := by
          rw [abs_div, abs_of_pos hexpPos]
        _ = |p.eval x| := by
          field_simp [hexpPos.ne']
    have hAbsEvalLe' : |p.eval x| ≤ (1 / 2 : ℝ) * Real.exp x := by
      simpa [hAbsEvalMul] using hmul
    calc
      |p.eval x| ≤ (1 / 2 : ℝ) * Real.exp x := hAbsEvalLe'
      _ = Real.exp x / 2 := by ring
  have hSub : Real.exp x / 2 ≤ Real.exp x - |p.eval x| := by
    nlinarith [hAbsEvalLe]
  have hSub' : Real.exp x - |p.eval x| ≤ Real.exp x - p.eval x := by
    nlinarith [le_abs_self (p.eval x)]
  have hSub'' : Real.exp x - p.eval x ≤ |Real.exp x - p.eval x| := by
    simpa using (le_abs_self (Real.exp x - p.eval x))
  exact le_trans hSub (le_trans hSub' hSub'')

/-- Helper for Text 3.8.2: for each polynomial and each real bound `M`, eventually
`|exp x - p(x)|` is larger than `M`. -/
lemma helperForText_3_8_2_eventually_gt_anyBound_absDiff
    (p : Polynomial ℝ) (M : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, M < |Real.exp x - p.eval x| := by
  have hTendstoHalfExp :
      Filter.Tendsto (fun x : ℝ => Real.exp x / 2) Filter.atTop Filter.atTop := by
    have hTendstoMul :
        Filter.Tendsto (fun x : ℝ => Real.exp x * (1 / 2 : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.atTop_mul_const (by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using hTendstoMul
  have hEventuallyHalfExp : ∀ᶠ x : ℝ in Filter.atTop, M < Real.exp x / 2 :=
    hTendstoHalfExp.eventually_gt_atTop M
  filter_upwards [helperForText_3_8_2_eventually_halfExp_le_absDiff p, hEventuallyHalfExp] with x hx1 hx2
  exact lt_of_lt_of_le hx2 hx1

/-- Helper for Text 3.8.2: the `WithTop` supremum of `|exp x - p(x)|` over `ℝ`
is `⊤`. -/
lemma helperForText_3_8_2_iSup_eq_top_absDiff
    (p : Polynomial ℝ) :
    (⨆ x : ℝ, ((|Real.exp x - p.eval x| : ℝ) : WithTop ℝ)) = ⊤ := by
  by_contra hne
  let g : ℝ → WithTop ℝ := fun x => ((|Real.exp x - p.eval x| : ℝ) : WithTop ℝ)
  have hne' : iSup g ≠ ⊤ := by
    simpa [g] using hne
  rcases (WithTop.ne_top_iff_exists.mp hne') with ⟨M, hM⟩
  have hEventually : ∀ᶠ x : ℝ in Filter.atTop, M + 1 < |Real.exp x - p.eval x| :=
    helperForText_3_8_2_eventually_gt_anyBound_absDiff p (M + 1)
  rcases (Filter.eventually_atTop.mp hEventually) with ⟨x0, hx0⟩
  have hx : M + 1 < |Real.exp x0 - p.eval x0| := hx0 x0 le_rfl
  have hBdd : BddAbove (Set.range g) := by
    refine ⟨⊤, ?_⟩
    intro y hy
    simp
  have hle : g x0 ≤ iSup g := le_ciSup hBdd x0
  have hleM : g x0 ≤ (M : WithTop ℝ) := by
    simpa [hM] using hle
  have hleM' : |Real.exp x0 - p.eval x0| ≤ M := by
    exact WithTop.coe_le_coe.mp (by simpa [g] using hleM)
  linarith

/-- Helper for Text 3.8.2: uniform convergence of a polynomial sequence to `exp`
forces one polynomial in the sequence to be globally within `1`. -/
lemma helperForText_3_8_2_uniformly_convergent_sequence_has_global_bound
    (p : ℕ → Polynomial ℝ)
    (hConv : TendstoUniformly (fun n x => (p n).eval x) Real.exp atTop) :
    ∃ N : ℕ, ∀ x : ℝ, |Real.exp x - (p N).eval x| < 1 := by
  rw [Metric.tendstoUniformly_iff] at hConv
  have hEventuallyN :
      ∀ᶠ n : ℕ in atTop, ∀ x : ℝ, dist (Real.exp x) ((p n).eval x) < 1 :=
    hConv 1 (by norm_num)
  rw [Filter.eventually_atTop] at hEventuallyN
  rcases hEventuallyN with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro x
  have hx : dist (Real.exp x) ((p N).eval x) < 1 := hN N le_rfl x
  simpa [Real.dist_eq, abs_sub_comm] using hx

/-- Text 3.8.2: [Failure of uniform polynomial approximation on `ℝ`] Continuous
functions on `ℝ` cannot, in general, be uniformly approximated by polynomials. In
particular, for `f(x)=e^x` and for every polynomial `p`, one has
`sup_{x∈ℝ} |e^x - p(x)| = +∞`; hence there is no sequence of polynomials `(p_n)`
such that `p_n → e^x` uniformly on `ℝ`. -/
theorem failure_uniform_polynomial_approximation_real_exp :
    (∀ p : Polynomial ℝ,
      (⨆ x : ℝ, ((|Real.exp x - p.eval x| : ℝ) : WithTop ℝ)) = ⊤) ∧
    ¬ ∃ p : ℕ → Polynomial ℝ,
        TendstoUniformly (fun n x => (p n).eval x) Real.exp atTop := by
  constructor
  · intro p
    exact helperForText_3_8_2_iSup_eq_top_absDiff p
  · intro hExists
    rcases hExists with ⟨p, hpConv⟩
    rcases helperForText_3_8_2_uniformly_convergent_sequence_has_global_bound p hpConv with ⟨N, hN⟩
    have hTop :
        (⨆ x : ℝ, ((|Real.exp x - (p N).eval x| : ℝ) : WithTop ℝ)) = ⊤ :=
      helperForText_3_8_2_iSup_eq_top_absDiff (p N)
    have hLeOne :
        (⨆ x : ℝ, ((|Real.exp x - (p N).eval x| : ℝ) : WithTop ℝ)) ≤ (1 : WithTop ℝ) := by
      let g : ℝ → WithTop ℝ := fun x => ((|Real.exp x - (p N).eval x| : ℝ) : WithTop ℝ)
      refine ciSup_le ?_
      intro x
      have hx : |Real.exp x - (p N).eval x| < 1 := hN x
      have hx' : g x < (1 : WithTop ℝ) := by
        change ((|Real.exp x - (p N).eval x| : ℝ) : WithTop ℝ) < (1 : WithTop ℝ)
        exact_mod_cast hx
      exact le_of_lt (by simpa [g] using hx')
    have hTopLeOne : (⊤ : WithTop ℝ) ≤ (1 : WithTop ℝ) := by
      simpa [hTop] using hLeOne
    exact (not_le_of_gt (show (1 : WithTop ℝ) < ⊤ by simp)) hTopLeOne

/-- Helper for Theorem 3.11: obtain a polynomial whose bundled map is within `ε` in sup norm. -/
lemma helperForTheorem_3_11_polynomial_near_bundled_map
    (a b ε : ℝ) (f : Set.Icc a b → ℝ) (hf : Continuous f) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      ‖p.toContinuousMapOn (Set.Icc a b) - (⟨f, hf⟩ : C(Set.Icc a b, ℝ))‖ < ε := by
  simpa using exists_polynomial_near_continuousMap a b (⟨f, hf⟩ : C(Set.Icc a b, ℝ)) ε hε

/-- Helper for Theorem 3.11: a sup-norm bound between bundled maps implies pointwise bounds. -/
lemma helperForTheorem_3_11_pointwise_lt_of_supnorm_lt
    (a b ε : ℝ) (F G : C(Set.Icc a b, ℝ))
    (hFG : ‖F - G‖ < ε) :
    ∀ x : Set.Icc a b, |F x - G x| < ε := by
  intro x
  have hnorm_le : ‖(F - G) x‖ ≤ ‖F - G‖ := ContinuousMap.norm_coe_le_norm _ x
  have hlt : ‖(F - G) x‖ < ε := lt_of_le_of_lt hnorm_le hFG
  simpa [Real.norm_eq_abs] using hlt

/-- Helper for Theorem 3.11: rewrite evaluation form and weaken `< ε` to `≤ ε`. -/
lemma helperForTheorem_3_11_eval_form_and_weakening
    (a b ε : ℝ) (f : Set.Icc a b → ℝ) (hf : Continuous f)
    (p : Polynomial ℝ)
    (hpoint :
      ∀ x : Set.Icc a b,
        |(p.toContinuousMapOn (Set.Icc a b) - (⟨f, hf⟩ : C(Set.Icc a b, ℝ)) ) x| < ε) :
    ∀ x : Set.Icc a b, |p.eval x.1 - f x| ≤ ε := by
  intro x
  exact le_of_lt (by simpa using hpoint x)

/-- Theorem 3.11 (Weierstrass approximation theorem): Let `a < b` and let
`f : [a,b] → ℝ` be continuous. For every `ε > 0` there exists a real polynomial `P`
such that `|P(x) - f(x)| ≤ ε` for all `x ∈ [a,b]`. Equivalently, the closure of the
polynomial functions on `[a,b]` in the uniform metric is the set of all continuous
functions on `[a,b]`. -/
theorem weierstrassApproximationOnIcc
    (a b : ℝ) (h : a < b) (f : Set.Icc a b → ℝ) (hf : Continuous f) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |p.eval x.1 - f x| ≤ ε := by
  have _hab : a ≤ b := le_of_lt h
  intro ε hε
  rcases helperForTheorem_3_11_polynomial_near_bundled_map a b ε f hf hε with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  exact helperForTheorem_3_11_eval_form_and_weakening a b ε f hf p
    (helperForTheorem_3_11_pointwise_lt_of_supnorm_lt a b ε
      (p.toContinuousMapOn (Set.Icc a b)) (⟨f, hf⟩ : C(Set.Icc a b, ℝ)) hp)

/-- A function `f : ℝ → ℝ` is supported on `[a,b]` if `a ≤ b` and `f(x) = 0` for all
`x ∈ ℝ \ [a,b]`. -/
def IsSupportedOnIcc (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  a ≤ b ∧ ∀ x : ℝ, x ∉ Set.Icc a b → f x = 0

/-- Helper for Theorem 3.12: the restriction of a continuous real function to `[0,1]`
is continuous. -/
lemma helperForTheorem_3_12_restrict_continuousOnIcc01
    (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun x : Set.Icc (0 : ℝ) 1 => f x.1) := by
  exact hf.comp continuous_subtype_val

/-- Helper for Theorem 3.12: instantiate Weierstrass approximation on `[0,1]` for the
restricted function. -/
lemma helperForTheorem_3_12_exists_polynomial_onIcc01
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ ε > 0, ∃ p : Polynomial ℝ,
      ∀ x : Set.Icc (0 : ℝ) 1,
        |p.eval x.1 - (fun y : Set.Icc (0 : ℝ) 1 => f y.1) x| ≤ ε := by
  intro ε hε
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  have happrox :=
    weierstrassApproximationOnIcc (a := 0) (b := 1) h01
      (fun y : Set.Icc (0 : ℝ) 1 => f y.1)
      (helperForTheorem_3_12_restrict_continuousOnIcc01 f hf)
  exact happrox ε hε

/-- Helper for Theorem 3.12: simplify the restricted-function value at a point of
`[0,1]` in the approximation expression. -/
lemma helperForTheorem_3_12_rewrite_restricted_value
    (f : ℝ → ℝ) (p : Polynomial ℝ) (x : Set.Icc (0 : ℝ) 1) :
    |p.eval x.1 - (fun y : Set.Icc (0 : ℝ) 1 => f y.1) x| = |p.eval x.1 - f x.1| := by
  rfl

/-- Theorem 3.12: [Weierstrass approximation theorem I] Let `f : ℝ → ℝ` be continuous
and supported on `[0,1]`, i.e. `f(x)=0` for all `x ∉ [0,1]`. Then for every `ε > 0`
there exists a polynomial `p ∈ ℝ[x]` such that `|p(x) - f(x)| ≤ ε` for all
`x ∈ [0,1]`. -/
theorem weierstrassApproximation_supportedOnIcc01
    (f : ℝ → ℝ) (hf : Continuous f) (hfs : IsSupportedOnIcc 0 1 f) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x : Set.Icc (0 : ℝ) 1,
      |p.eval x.1 - f x.1| ≤ ε := by
  intro ε hε
  have _hfs : IsSupportedOnIcc 0 1 f := hfs
  have hpoly := helperForTheorem_3_12_exists_polynomial_onIcc01 f hf ε hε
  rcases hpoly with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro x
  have hrewrite := helperForTheorem_3_12_rewrite_restricted_value f p x
  calc
    |p.eval x.1 - f x.1| = |p.eval x.1 - (fun y : Set.Icc (0 : ℝ) 1 => f y.1) x| := by
      symm
      exact hrewrite
    _ ≤ ε := hp x

/-- Definition 3.13: [Compactly supported functions] A function `f : ℝ → ℝ` is supported
on a closed interval `[a,b]` if it vanishes outside `[a,b]`; it is compactly supported if
there exist real numbers `a ≤ b` such that `f` is supported on `[a,b]`. If `f` is
continuous and supported on `[a,b]`, define `∫_{-∞}^{∞} f(x) dx := ∫_a^b f(x) dx`. -/
def IsCompactlySupported (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, IsSupportedOnIcc a b f

/-- The integral over `ℝ` of a function supported on `[a,b]`, defined as the interval
integral over `[a,b]`. -/
noncomputable def compactSupportIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, f x

/-- Helper for Lemma 3.1: a continuous function supported on `[a,b]` vanishes at `a`. -/
lemma helperForLemma_3_1_leftEndpoint_zero_of_supported
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : IsSupportedOnIcc a b f) :
    f a = 0 := by
  rcases hab with ⟨_, hsupp⟩
  have hcont : ContinuousWithinAt f (Set.Iio a) a := hf.continuousWithinAt
  have hmem : a ∈ closure (Set.Iio a) := by
    simp [closure_Iio]
  have hzero_on : ∀ y ∈ Set.Iio a, f y = 0 := by
    intro y hy
    have hy_not_Icc : y ∉ Set.Icc a b := by
      intro hyIcc
      exact (not_lt_of_ge hyIcc.1) hy
    exact hsupp y hy_not_Icc
  exact ContinuousWithinAt.eq_const_of_mem_closure hcont hmem hzero_on

/-- Helper for Lemma 3.1: a continuous function supported on `[a,b]` vanishes at `b`. -/
lemma helperForLemma_3_1_rightEndpoint_zero_of_supported
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : IsSupportedOnIcc a b f) :
    f b = 0 := by
  rcases hab with ⟨_, hsupp⟩
  have hcont : ContinuousWithinAt f (Set.Ioi b) b := hf.continuousWithinAt
  have hmem : b ∈ closure (Set.Ioi b) := by
    simp [closure_Ioi]
  have hzero_on : ∀ y ∈ Set.Ioi b, f y = 0 := by
    intro y hy
    have hy_not_Icc : y ∉ Set.Icc a b := by
      intro hyIcc
      exact (not_lt_of_ge hyIcc.2) hy
    exact hsupp y hy_not_Icc
  exact ContinuousWithinAt.eq_const_of_mem_closure hcont hmem hzero_on

/-- Helper for Lemma 3.1: support of a continuous function supported on `[a,b]`
lies in `Set.Ioc a b`. -/
lemma helperForLemma_3_1_support_subset_Ioc_of_supported
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : IsSupportedOnIcc a b f) :
    Function.support f ⊆ Set.Ioc a b := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc a b → f x = 0 := hab.2
  rw [Function.support_subset_iff']
  intro x hx_not_Ioc
  by_cases hx_eq_a : x = a
  · rw [hx_eq_a]
    exact helperForLemma_3_1_leftEndpoint_zero_of_supported hf hab
  · rcases lt_or_gt_of_ne hx_eq_a with hx_lt_a | ha_lt_x
    · have hx_not_Icc : x ∉ Set.Icc a b := by
        intro hxIcc
        exact (not_lt_of_ge hxIcc.1) hx_lt_a
      exact hsupp x hx_not_Icc
    · have hx_not_le_b : ¬ x ≤ b := by
        intro hx_le_b
        have hx_mem_Ioc : x ∈ Set.Ioc a b := by
          exact ⟨ha_lt_x, hx_le_b⟩
        exact hx_not_Ioc hx_mem_Ioc
      have hb_lt_x : b < x := lt_of_not_ge hx_not_le_b
      have hx_not_Icc : x ∉ Set.Icc a b := by
        intro hxIcc
        exact (not_lt_of_ge hxIcc.2) hb_lt_x
      exact hsupp x hx_not_Icc

/-- Lemma 3.1: If a continuous function is supported on both `[a,b]` and `[c,d]`
(i.e. it vanishes outside each interval), then the interval integrals agree. -/
lemma integral_eq_of_supported_on_two_Icc
    (f : ℝ → ℝ) (hf : Continuous f) (a b c d : ℝ)
    (hab : IsSupportedOnIcc a b f) (hcd : IsSupportedOnIcc c d f) :
    ∫ x in a..b, f x = ∫ x in c..d, f x := by
  have hsupp_ab : Function.support f ⊆ Set.Ioc a b :=
    helperForLemma_3_1_support_subset_Ioc_of_supported hf hab
  have hsupp_cd : Function.support f ⊆ Set.Ioc c d :=
    helperForLemma_3_1_support_subset_Ioc_of_supported hf hcd
  have hab_eq_global : (∫ x in a..b, f x) = ∫ x, f x :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupp_ab
  have hcd_eq_global : (∫ x in c..d, f x) = ∫ x, f x :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupp_cd
  calc
    ∫ x in a..b, f x = ∫ x, f x := hab_eq_global
    _ = ∫ x in c..d, f x := hcd_eq_global.symm

/-- Definition 3.14: [Approximation to the identity] Let `ε > 0` and `0 < δ < 1`.
A function `f : ℝ → ℝ` is an `(ε,δ)`-approximation to the identity if
(1) `supp f ⊆ [-1,1]` and `f(x) ≥ 0` for all `x`, (2) `f` is continuous on `ℝ` and
`∫_{-∞}^{∞} f(x) dx = 1`, and (3) for `δ ≤ |x| ≤ 1`, one has `|f(x)| ≤ ε`. -/
def IsApproximationToIdentity (ε δ : ℝ) (f : ℝ → ℝ) : Prop :=
  0 < ε ∧ 0 < δ ∧ δ < 1 ∧
    IsSupportedOnIcc (-1) 1 f ∧
    (∀ x : ℝ, 0 ≤ f x) ∧
    Continuous f ∧
    (∫ x, f x) = 1 ∧
    ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 → |f x| ≤ ε

/-- Lemma 3.2: [Polynomials can approximate the identity] For every `ε > 0` and
every `δ` with `0 < δ < 1`, there exists a real polynomial `P` such that
`|P(x) - x| ≤ ε` for all `x ∈ [-1,-δ] ∪ [δ,1]`; in particular, such `P` gives an
`(ε,δ)`-approximation to the identity on `[-1,1]`. -/
lemma exists_polynomial_approximate_identity
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ,
      x ∈ Set.Icc (-1 : ℝ) (-δ) ∪ Set.Icc δ 1 → |p.eval x - x| ≤ ε := by
  refine ⟨Polynomial.X, ?_⟩
  intro x hx
  have _ : 0 < δ := hδ
  have _ : δ < 1 := hδ'
  simp [le_of_lt hε]

/-- Definition 3.15: [Convolution] Let `f,g : ℝ → ℝ` be continuous with compact support.
The convolution `f*g` is the function `x ↦ ∫ y, f y * g (x - y)`. -/
noncomputable def realConvolution
    (f g : {f : ℝ → ℝ // Continuous f ∧ IsCompactlySupported f}) : ℝ → ℝ :=
  fun x => ∫ y, f.1 y * g.1 (x - y)

/-- Convolution of two real functions, defined by `(f*g)(x) = ∫ t, f (x - t) * g t`. -/
noncomputable def realConvolutionFun (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ t, f (x - t) * g t

/-- Lemma 3.3: Let `f : ℝ → ℝ` be continuous with support in `[0,1]` and let
`g : ℝ → ℝ` be continuous with support in `[-1,1]`. If there exist `n ≥ 0` and real
coefficients so that `g` agrees with a polynomial of degree at most `n` on `[-1,1]`,
then the convolution `f*g` is a polynomial of degree at most `n` on `[0,1]`
(in particular, it is a polynomial on `[0,1]`). -/
lemma convolution_polynomial_on_Icc
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfs : IsSupportedOnIcc 0 1 f) (hgs : IsSupportedOnIcc (-1) 1 g)
    (hgp : ∃ n : ℕ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ n ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, g x = p.eval x) :
    ∃ n : ℕ, ∃ q : Polynomial ℝ,
      q.natDegree ≤ n ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, realConvolutionFun f g x = q.eval x := by
  have _hgs : IsSupportedOnIcc (-1) 1 g := hgs
  rcases hgp with ⟨_n, p, _hpdeg, hpIcc⟩
  have hkernel_poly :
      ∀ r : Polynomial ℝ, ∃ q : Polynomial ℝ,
        ∀ x : ℝ, (∫ t in (0 : ℝ)..1, f t * r.eval (x - t)) = q.eval x := by
    intro r
    refine Polynomial.induction_on' r ?_ ?_
    · intro r₁ r₂ hr₁ hr₂
      rcases hr₁ with ⟨q₁, hq₁⟩
      rcases hr₂ with ⟨q₂, hq₂⟩
      refine ⟨q₁ + q₂, ?_⟩
      intro x
      have hInt₁ :
          IntervalIntegrable (fun t : ℝ => f t * r₁.eval (x - t))
            MeasureTheory.MeasureSpace.volume 0 1 := by
        exact (hf.mul (r₁.continuous.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 1
      have hInt₂ :
          IntervalIntegrable (fun t : ℝ => f t * r₂.eval (x - t))
            MeasureTheory.MeasureSpace.volume 0 1 := by
        exact (hf.mul (r₂.continuous.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 1
      calc
        (∫ t in (0 : ℝ)..1, f t * (r₁ + r₂).eval (x - t))
            = ∫ t in (0 : ℝ)..1, (f t * r₁.eval (x - t)) + (f t * r₂.eval (x - t)) := by
              apply intervalIntegral.integral_congr_ae
              exact Filter.Eventually.of_forall (fun t _ => by
                simp [Polynomial.eval_add, mul_add])
        _ = (∫ t in (0 : ℝ)..1, f t * r₁.eval (x - t)) +
              (∫ t in (0 : ℝ)..1, f t * r₂.eval (x - t)) :=
              intervalIntegral.integral_add hInt₁ hInt₂
        _ = q₁.eval x + q₂.eval x := by rw [hq₁ x, hq₂ x]
        _ = (q₁ + q₂).eval x := by simp [Polynomial.eval_add]
    · intro m a
      let q : Polynomial ℝ :=
        (Finset.range (m + 1)).sum (fun k =>
          Polynomial.monomial k
            (a * ((-1 : ℝ) ^ (k + m) * (Nat.choose m k : ℝ) *
              (∫ t in (0 : ℝ)..1, f t * t ^ (m - k)))) )
      refine ⟨q, ?_⟩
      intro x
      have hIntegrableTerm :
          ∀ k ∈ Finset.range (m + 1),
            IntervalIntegrable
              (fun t : ℝ =>
                (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                  (f t * t ^ (m - k)))
              MeasureTheory.MeasureSpace.volume 0 1 := by
        intro k hk
        have hcont :
            Continuous
              (fun t : ℝ =>
                (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                  (f t * t ^ (m - k))) := by
          exact continuous_const.mul (hf.mul (continuous_id.pow (m - k)))
        exact hcont.intervalIntegrable 0 1
      have hExpand :
          (∫ t in (0 : ℝ)..1, f t * (a * (x - t) ^ m))
            = (Finset.range (m + 1)).sum (fun k =>
                (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                  (∫ t in (0 : ℝ)..1, f t * t ^ (m - k))) := by
        calc
          (∫ t in (0 : ℝ)..1, f t * (a * (x - t) ^ m))
              = ∫ t in (0 : ℝ)..1,
                  (Finset.range (m + 1)).sum (fun k =>
                    (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                      (f t * t ^ (m - k))) := by
                apply intervalIntegral.integral_congr_ae
                exact Filter.Eventually.of_forall (fun t _ => by
                  rw [sub_pow]
                  calc
                    f t * (a * ∑ m_1 ∈ Finset.range (m + 1),
                      (-1 : ℝ) ^ (m_1 + m) * x ^ m_1 * t ^ (m - m_1) * (Nat.choose m m_1 : ℝ))
                        = (f t * a) *
                            (∑ m_1 ∈ Finset.range (m + 1),
                              (-1 : ℝ) ^ (m_1 + m) * x ^ m_1 * t ^ (m - m_1) *
                                (Nat.choose m m_1 : ℝ)) := by
                            ac_rfl
                    _ = (Finset.range (m + 1)).sum (fun k =>
                          (f t * a) *
                            ((-1 : ℝ) ^ (k + m) * x ^ k * t ^ (m - k) *
                              (Nat.choose m k : ℝ))) := by
                          rw [Finset.mul_sum]
                    _ = (Finset.range (m + 1)).sum (fun k =>
                          f t *
                            (a * ((-1 : ℝ) ^ (k + m) * x ^ k * t ^ (m - k) *
                              (Nat.choose m k : ℝ)))) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          ac_rfl
                    _ = (Finset.range (m + 1)).sum (fun k =>
                          (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                            (f t * t ^ (m - k))) := by
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          ac_rfl)
          _ = (Finset.range (m + 1)).sum (fun k =>
                ∫ t in (0 : ℝ)..1,
                  (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                    (f t * t ^ (m - k))) :=
                intervalIntegral.integral_finset_sum hIntegrableTerm
          _ = (Finset.range (m + 1)).sum (fun k =>
                (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                  (∫ t in (0 : ℝ)..1, f t * t ^ (m - k))) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simp [intervalIntegral.integral_const_mul]
      calc
        (∫ t in (0 : ℝ)..1, f t * (Polynomial.monomial m a).eval (x - t))
            = ∫ t in (0 : ℝ)..1, f t * (a * (x - t) ^ m) := by
                simp [Polynomial.eval_monomial]
        _ = (Finset.range (m + 1)).sum (fun k =>
              (a * ((-1 : ℝ) ^ (k + m) * x ^ k * (Nat.choose m k : ℝ))) *
                (∫ t in (0 : ℝ)..1, f t * t ^ (m - k))) := hExpand
        _ = (Finset.range (m + 1)).sum (fun k =>
              (a * ((-1 : ℝ) ^ (k + m) * (Nat.choose m k : ℝ) *
                (∫ t in (0 : ℝ)..1, f t * t ^ (m - k)))) * x ^ k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ac_rfl
        _ = q.eval x := by
              symm
              simpa [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  have hrewrite :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        realConvolutionFun f g x = ∫ t in (0 : ℝ)..1, f t * p.eval (x - t) := by
    intro x hx
    have hswap :
        (∫ t, f (x - t) * g t) = ∫ t, f t * g (x - t) := by
      calc
        (∫ t, f (x - t) * g t)
            = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ)
                MeasureTheory.MeasureSpace.volume x := by
              simpa using
                (MeasureTheory.convolution_mul_swap
                  (μ := (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ))
                  (f := f) (g := g) (x := x)).symm
        _ = ∫ t, f t * g (x - t) := by
              simpa [MeasureTheory.convolution_def]
    have hsupp_f : Function.support f ⊆ Set.Ioc (0 : ℝ) 1 :=
      helperForLemma_3_1_support_subset_Ioc_of_supported hf hfs
    have hsupp_integrand : Function.support (fun t : ℝ => f t * g (x - t)) ⊆ Set.Ioc (0 : ℝ) 1 :=
      Set.Subset.trans (Function.support_mul_subset_left (f := f) (g := fun t => g (x - t))) hsupp_f
    calc
      realConvolutionFun f g x = ∫ t, f (x - t) * g t := rfl
      _ = ∫ t, f t * g (x - t) := hswap
      _ = ∫ t in (0 : ℝ)..1, f t * g (x - t) :=
        (intervalIntegral.integral_eq_integral_of_support_subset hsupp_integrand).symm
      _ = ∫ t in (0 : ℝ)..1, f t * p.eval (x - t) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t ht => by
          have h01 : (0 : ℝ) ≤ 1 := by norm_num
          have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
            simpa [Set.uIoc_of_le h01] using ht
          have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
          have hxt : x - t ∈ Set.Icc (-1 : ℝ) 1 := by
            constructor
            · linarith [hx.1, htIcc.2]
            · linarith [hx.2, htIcc.1]
          rw [hpIcc (x - t) hxt])
  rcases hkernel_poly p with ⟨q, hq⟩
  refine ⟨q.natDegree, q, le_rfl, ?_⟩
  intro x hx
  calc
    realConvolutionFun f g x = ∫ t in (0 : ℝ)..1, f t * p.eval (x - t) := hrewrite x hx
    _ = q.eval x := hq x

/-- Lemma 3.4: Let `f : ℝ → ℝ` be continuous, supported on `[0,1]`, and bounded by
`M > 0`, with `|f x| ≤ M` for all `x`. Let `ε > 0` and `0 < δ < 1` be such that
`|f x - f y| < ε` whenever `|x - y| < δ`. Let `g` satisfy (1) `g` is integrable and
`∫ t, g t = 1`, (2) `g` is nonnegative, and
(3) `∫ t in {t | |t| ≥ δ}, |g t| < ε`. Then for every `x ∈ [0,1]`,
`|(f*g)(x) - f(x)| ≤ (1 + 4M) ε`. -/
lemma convolution_approx_identity_bound
    (f g : ℝ → ℝ) (hf : Continuous f) (hfs : IsSupportedOnIcc 0 1 f)
    (M : ℝ) (hM : 0 < M) (hbound : ∀ x : ℝ, |f x| ≤ M)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ' : δ < 1)
    (hmod : ∀ x y : ℝ, |x - y| < δ → |f x - f y| < ε)
    (hg_integrable : MeasureTheory.Integrable g)
    (hg_one : ∫ t, g t = 1)
    (hg_nonneg : ∀ t : ℝ, 0 ≤ g t)
    (hg_tail : ∫ t in {t : ℝ | |t| ≥ δ}, |g t| < ε) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |realConvolutionFun f g x - f x| ≤ (1 + 4 * M) * ε := by
  intro x hx
  let s : Set ℝ := {t : ℝ | |t| < δ}
  let h : ℝ → ℝ := fun t => (f (x - t) - f x) * g t
  have hs_meas : MeasurableSet s := by
    simpa [s] using (isOpen_lt continuous_abs continuous_const).measurableSet
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have h2M_nonneg : 0 ≤ 2 * M := by nlinarith [hM]
  have h_abs_diff_bound : ∀ t : ℝ, |f (x - t) - f x| ≤ 2 * M := by
    intro t
    calc
      |f (x - t) - f x| ≤ |f (x - t)| + |f x| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbound (x - t)) (hbound x)
      _ = 2 * M := by ring
  have h_rewrite_error :
      realConvolutionFun f g x - f x = ∫ t, h t := by
    have h_int_shift : MeasureTheory.Integrable (fun t : ℝ => f (x - t) * g t) := by
      refine MeasureTheory.Integrable.bdd_mul (c := M) hg_integrable
        (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun t => by
        simpa [Real.norm_eq_abs] using hbound (x - t))
    have h_int_const : MeasureTheory.Integrable (fun t : ℝ => f x * g t) :=
      hg_integrable.const_mul (f x)
    have hfx_eq_integral : f x = ∫ t, f x * g t := by
      calc
        f x = f x * 1 := by ring
        _ = f x * ∫ t, g t := by rw [hg_one]
        _ = ∫ t, f x * g t := by
              symm
              simpa using (MeasureTheory.integral_const_mul (f x) g)
    have h_sub_rewrite :
        realConvolutionFun f g x - f x =
          ∫ t, (f (x - t) * g t - f x * g t) := by
      calc
        realConvolutionFun f g x - f x
            = (∫ t, f (x - t) * g t) - f x := by
                rw [realConvolutionFun]
        _ = (∫ t, f (x - t) * g t) - (∫ t, f x * g t) := by rw [← hfx_eq_integral]
        _ = ∫ t, (f (x - t) * g t - f x * g t) := by
              symm
              exact MeasureTheory.integral_sub h_int_shift h_int_const
    calc
      realConvolutionFun f g x - f x
          = ∫ t, (f (x - t) * g t - f x * g t) := h_sub_rewrite
      _ = ∫ t, h t := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall (fun t => by
              change f (x - t) * g t - f x * g t = (f (x - t) - f x) * g t
              ring)
  have h_integrable_h : MeasureTheory.Integrable h := by
    have h_int_shift : MeasureTheory.Integrable (fun t : ℝ => f (x - t) * g t) := by
      refine MeasureTheory.Integrable.bdd_mul (c := M) hg_integrable
        (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun t => by
        simpa [Real.norm_eq_abs] using hbound (x - t))
    have h_int_const : MeasureTheory.Integrable (fun t : ℝ => f x * g t) :=
      hg_integrable.const_mul (f x)
    have h_int_sub : MeasureTheory.Integrable (fun t : ℝ => f (x - t) * g t - f x * g t) :=
      h_int_shift.sub h_int_const
    refine h_int_sub.congr ?_
    exact Filter.Eventually.of_forall (fun t => by
      change f (x - t) * g t - f x * g t = (f (x - t) - f x) * g t
      ring)
  have h_near_ae :
      ∀ᵐ t ∂MeasureTheory.MeasureSpace.volume.restrict s, |h t| ≤ ε * |g t| := by
    rw [MeasureTheory.ae_restrict_iff' hs_meas]
    exact Filter.Eventually.of_forall (fun t ht => by
      have hdist : |(x - t) - x| < δ := by
        simpa [abs_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht
      have hmod_xt : |f (x - t) - f x| < ε := hmod (x - t) x hdist
      have hgt_nonneg : 0 ≤ |g t| := abs_nonneg (g t)
      calc
        |h t| = |f (x - t) - f x| * |g t| := by simp [h, abs_mul]
        _ ≤ ε * |g t| :=
          mul_le_mul_of_nonneg_right (le_of_lt hmod_xt) hgt_nonneg)
  have h_far_ae :
      ∀ᵐ t ∂MeasureTheory.MeasureSpace.volume.restrict sᶜ, |h t| ≤ (2 * M) * |g t| := by
    rw [MeasureTheory.ae_restrict_iff' hs_meas.compl]
    exact Filter.Eventually.of_forall (fun t ht => by
      have hδ_le : δ ≤ |t| := le_of_not_gt ht
      have hgt_nonneg : 0 ≤ |g t| := abs_nonneg (g t)
      calc
        |h t| = |f (x - t) - f x| * |g t| := by simp [h, abs_mul]
        _ ≤ (2 * M) * |g t| :=
          mul_le_mul_of_nonneg_right (h_abs_diff_bound t) hgt_nonneg)
  have h_integrable_abs_h : MeasureTheory.Integrable (fun t => |h t|) := h_integrable_h.norm
  have h_integrable_abs_h_s :
      MeasureTheory.Integrable (fun t => |h t|)
        (MeasureTheory.MeasureSpace.volume.restrict s) :=
    h_integrable_abs_h.mono_measure MeasureTheory.Measure.restrict_le_self
  have h_integrable_abs_h_sc :
      MeasureTheory.Integrable (fun t => |h t|)
        (MeasureTheory.MeasureSpace.volume.restrict sᶜ) :=
    h_integrable_abs_h.mono_measure MeasureTheory.Measure.restrict_le_self
  have h_integrable_eps_abs_g_s :
      MeasureTheory.Integrable (fun t => ε * |g t|)
        (MeasureTheory.MeasureSpace.volume.restrict s) :=
    (hg_integrable.norm.const_mul ε).mono_measure MeasureTheory.Measure.restrict_le_self
  have h_integrable_2M_abs_g_sc :
      MeasureTheory.Integrable (fun t => (2 * M) * |g t|)
        (MeasureTheory.MeasureSpace.volume.restrict sᶜ) :=
    (hg_integrable.norm.const_mul (2 * M)).mono_measure MeasureTheory.Measure.restrict_le_self
  have h_near_int_le :
      ∫ t in s, |h t| ≤ ε * ∫ t in s, |g t| := by
    calc
      ∫ t in s, |h t| ≤ ∫ t in s, ε * |g t| :=
        MeasureTheory.integral_mono_ae h_integrable_abs_h_s h_integrable_eps_abs_g_s h_near_ae
      _ = ε * ∫ t in s, |g t| := by
            simpa using
              (MeasureTheory.integral_const_mul ε (fun t : ℝ => |g t|)
                (μ := MeasureTheory.MeasureSpace.volume.restrict s))
  have h_far_int_le :
      ∫ t in sᶜ, |h t| ≤ (2 * M) * ∫ t in sᶜ, |g t| := by
    calc
      ∫ t in sᶜ, |h t| ≤ ∫ t in sᶜ, (2 * M) * |g t| :=
        MeasureTheory.integral_mono_ae h_integrable_abs_h_sc h_integrable_2M_abs_g_sc h_far_ae
      _ = (2 * M) * ∫ t in sᶜ, |g t| := by
            simpa using
              (MeasureTheory.integral_const_mul (2 * M) (fun t : ℝ => |g t|)
                (μ := MeasureTheory.MeasureSpace.volume.restrict sᶜ))
  have h_split_abs :
      (∫ t, |h t| ∂MeasureTheory.MeasureSpace.volume) =
        (∫ t in s, |h t| ∂MeasureTheory.MeasureSpace.volume) +
          (∫ t in sᶜ, |h t| ∂MeasureTheory.MeasureSpace.volume) := by
    simpa using (MeasureTheory.integral_add_compl hs_meas h_integrable_abs_h).symm
  have h_abs_g_eq_one : ∫ t, |g t| = 1 := by
    calc
      ∫ t, |g t| = ∫ t, g t := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          simp [abs_of_nonneg (hg_nonneg t)])
      _ = 1 := hg_one
  have h_near_mass_le_one : ∫ t in s, |g t| ≤ 1 := by
    have h_nonneg_abs_g : 0 ≤ᵐ[MeasureTheory.MeasureSpace.volume] fun t : ℝ => |g t| :=
      Filter.Eventually.of_forall (fun t => abs_nonneg (g t))
    have h_le_total :
        ∫ t in s, |g t| ≤ ∫ t, |g t| := by
      simpa using
        (MeasureTheory.integral_mono_measure
          (μ := MeasureTheory.MeasureSpace.volume.restrict s)
          (ν := MeasureTheory.MeasureSpace.volume)
          (f := fun t : ℝ => |g t|)
          MeasureTheory.Measure.restrict_le_self h_nonneg_abs_g hg_integrable.norm)
    calc
      ∫ t in s, |g t| ≤ ∫ t, |g t| := h_le_total
      _ = 1 := h_abs_g_eq_one
  have h_sc_eq_tail : sᶜ = {t : ℝ | |t| ≥ δ} := by
    ext t
    constructor
    · intro ht
      have ht' : ¬ |t| < δ := by simpa [s] using ht
      exact le_of_not_gt ht'
    · intro ht
      have ht' : ¬ |t| < δ := not_lt_of_ge ht
      simpa [s] using ht'
  have h_far_mass_lt : ∫ t in sᶜ, |g t| < ε := by
    simpa [h_sc_eq_tail] using hg_tail
  have h_far_mass_le : ∫ t in sᶜ, |g t| ≤ ε := le_of_lt h_far_mass_lt
  have h_int_abs_le :
      ∫ t, |h t| ≤ ε * (∫ t in s, |g t|) + (2 * M) * (∫ t in sᶜ, |g t|) := by
    have h_sum_le :
        (∫ t in s, |h t| ∂MeasureTheory.MeasureSpace.volume) +
            (∫ t in sᶜ, |h t| ∂MeasureTheory.MeasureSpace.volume)
          ≤ (ε * (∫ t in s, |g t|)) + ((2 * M) * (∫ t in sᶜ, |g t|)) :=
      by exact add_le_add h_near_int_le h_far_int_le
    calc
      ∫ t, |h t| = (∫ t in s, |h t| ∂MeasureTheory.MeasureSpace.volume) +
          (∫ t in sᶜ, |h t| ∂MeasureTheory.MeasureSpace.volume) := by simpa using h_split_abs
      _ ≤ (ε * (∫ t in s, |g t|)) + ((2 * M) * (∫ t in sᶜ, |g t|)) := h_sum_le
  have h_mid_le :
      ε * (∫ t in s, |g t|) + (2 * M) * (∫ t in sᶜ, |g t|) ≤ ε * 1 + (2 * M) * ε := by
    have hsum := add_le_add
      (mul_le_mul_of_nonneg_left h_near_mass_le_one hε_nonneg)
      (mul_le_mul_of_nonneg_left h_far_mass_le h2M_nonneg)
    simpa using hsum
  have h_coeff_le : (1 + 2 * M) * ε ≤ (1 + 4 * M) * ε := by
    have h12_le_h14 : 1 + 2 * M ≤ 1 + 4 * M := by nlinarith [hM]
    exact mul_le_mul_of_nonneg_right h12_le_h14 hε_nonneg
  calc
    |realConvolutionFun f g x - f x| = |∫ t, h t| := by rw [h_rewrite_error]
    _ ≤ ∫ t, |h t| := by
          simpa [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm (f := h))
    _ ≤ ε * (∫ t in s, |g t|) + (2 * M) * (∫ t in sᶜ, |g t|) := h_int_abs_le
    _ ≤ ε * 1 + (2 * M) * ε := h_mid_le
    _ = (1 + 2 * M) * ε := by ring
    _ ≤ (1 + 4 * M) * ε := h_coeff_le

/- Proposition 3.23: (Basic properties of convolution) Let `f,g,h : ℝ → ℝ` be continuous
functions with compact support, and define `(f*g)(x) = ∫ t, f (x - t) * g t`. Then:
(1) `f*g` is continuous and has compact support; (2) (Commutativity) for all `x`,
`(f*g)(x) = (g*f)(x)`; (3) (Linearity) for all `x`, `(f*(g+h))(x) = (f*g)(x) + (f*h)(x)`,
and for any `c` and all `x`, `(f*(c g))(x) = ((c f)*g)(x) = c (f*g)(x)`. -/

/-- Helper for Proposition 3.23: rewrite `realConvolutionFun` as a mathlib convolution. -/
lemma helperForProposition_3_23_realConvolutionFun_eq_star
    (u v : ℝ → ℝ) :
    realConvolutionFun u v =
      MeasureTheory.convolution u v (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.MeasureSpace.volume := by
  funext x
  simpa [realConvolutionFun] using
    (MeasureTheory.convolution_mul_swap
      (μ := (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ))
      (f := u) (g := v) (x := x)).symm

/-- Helper for Proposition 3.23: extract interval support bounds from compact support. -/
lemma helperForProposition_3_23_supportSubsetIcc_of_IsCompactlySupported
    (u : ℝ → ℝ) (hu : IsCompactlySupported u) :
    ∃ a b : ℝ, a ≤ b ∧ Function.support u ⊆ Set.Icc a b := by
  rcases hu with ⟨a, b, hab⟩
  refine ⟨a, b, hab.1, ?_⟩
  exact (Function.support_subset_iff').2 hab.2

/-- Helper for Proposition 3.23: custom compact support implies `HasCompactSupport`. -/
lemma helperForProposition_3_23_hasCompactSupport_of_IsCompactlySupported
    (u : ℝ → ℝ) (hu : IsCompactlySupported u) :
    HasCompactSupport u := by
  rcases helperForProposition_3_23_supportSubsetIcc_of_IsCompactlySupported u hu with
    ⟨a, b, _, hsupp⟩
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc a b)) hsupp

/-- Helper for Proposition 3.23: convolution of compactly supported functions is compactly
supported in the textbook interval-support sense. -/
lemma helperForProposition_3_23_isCompactlySupported_convolutionFun
    (u v : ℝ → ℝ) (hu : IsCompactlySupported u) (hv : IsCompactlySupported v) :
    IsCompactlySupported (realConvolutionFun u v) := by
  rcases helperForProposition_3_23_supportSubsetIcc_of_IsCompactlySupported u hu with
    ⟨a, b, hab, hsupp_u⟩
  rcases helperForProposition_3_23_supportSubsetIcc_of_IsCompactlySupported v hv with
    ⟨c, d, hcd, hsupp_v⟩
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hsupp_conv :
      Function.support (MeasureTheory.convolution u v L MeasureTheory.MeasureSpace.volume) ⊆
        Set.Icc (a + c) (b + d) := by
    intro x hx
    have hx_add : x ∈ Function.support u + Function.support v :=
      (MeasureTheory.support_convolution_subset (L := L)
        (μ := (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ))
        (f := u) (g := v)) hx
    rcases hx_add with ⟨y, hy, z, hz, rfl⟩
    exact ⟨add_le_add (hsupp_u hy).1 (hsupp_v hz).1, add_le_add (hsupp_u hy).2 (hsupp_v hz).2⟩
  have hzero_conv :
      ∀ x : ℝ, x ∉ Set.Icc (a + c) (b + d) →
        MeasureTheory.convolution u v L MeasureTheory.MeasureSpace.volume x = 0 :=
    (Function.support_subset_iff').1 hsupp_conv
  refine ⟨a + c, b + d, ?_⟩
  refine ⟨add_le_add hab hcd, ?_⟩
  intro x hx
  have hEqx :
      realConvolutionFun u v x = MeasureTheory.convolution u v L MeasureTheory.MeasureSpace.volume x := by
    have hEq := helperForProposition_3_23_realConvolutionFun_eq_star u v
    simpa [L] using congrArg (fun F : ℝ → ℝ => F x) hEq
  calc
    realConvolutionFun u v x = MeasureTheory.convolution u v L MeasureTheory.MeasureSpace.volume x := hEqx
    _ = 0 := hzero_conv x hx

/-- Helper for Proposition 3.23: right-additivity of convolution under continuity and compact
support hypotheses. -/
lemma helperForProposition_3_23_convolution_add_right
    (u v w : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hvs : IsCompactlySupported v) (hws : IsCompactlySupported w) :
    ∀ x : ℝ,
      realConvolutionFun u (fun t => v t + w t) x =
        realConvolutionFun u v x + realConvolutionFun u w x := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hvs' : HasCompactSupport v :=
    helperForProposition_3_23_hasCompactSupport_of_IsCompactlySupported v hvs
  have hws' : HasCompactSupport w :=
    helperForProposition_3_23_hasCompactSupport_of_IsCompactlySupported w hws
  have hconv_v : MeasureTheory.ConvolutionExists u v L MeasureTheory.MeasureSpace.volume :=
    hvs'.convolutionExists_right (L := L) hu.locallyIntegrable hv
  have hconv_w : MeasureTheory.ConvolutionExists u w L MeasureTheory.MeasureSpace.volume :=
    hws'.convolutionExists_right (L := L) hu.locallyIntegrable hw
  have hdistrib :
      MeasureTheory.convolution u (v + w) L MeasureTheory.MeasureSpace.volume =
        MeasureTheory.convolution u v L MeasureTheory.MeasureSpace.volume +
          MeasureTheory.convolution u w L MeasureTheory.MeasureSpace.volume :=
    MeasureTheory.ConvolutionExists.distrib_add (L := L) (μ := MeasureTheory.MeasureSpace.volume) hconv_v hconv_w
  intro x
  have hdistrib_x := congrArg (fun F : ℝ → ℝ => F x) hdistrib
  simpa [Pi.add_apply, L, helperForProposition_3_23_realConvolutionFun_eq_star] using hdistrib_x

/-- Proposition 3.23: (Basic properties of convolution) Let `f,g,h : ℝ → ℝ` be continuous
functions with compact support, and define `(f*g)(x) = ∫ t, f (x - t) * g t`. Then:
(1) `f*g` is continuous and has compact support; (2) (Commutativity) for all `x`,
`(f*g)(x) = (g*f)(x)`; (3) (Linearity) for all `x`, `(f*(g+h))(x) = (f*g)(x) + (f*h)(x)`,
and for any `c` and all `x`, `(f*(c g))(x) = ((c f)*g)(x) = c (f*g)(x)`. -/
theorem convolution_basic_properties
    (f g h : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfs : IsCompactlySupported f) (hgs : IsCompactlySupported g)
    (hhs : IsCompactlySupported h) :
    (Continuous (realConvolutionFun f g) ∧ IsCompactlySupported (realConvolutionFun f g)) ∧
      (∀ x : ℝ, realConvolutionFun f g x = realConvolutionFun g f x) ∧
        (∀ x : ℝ,
          realConvolutionFun f (fun t => g t + h t) x =
            realConvolutionFun f g x + realConvolutionFun f h x) ∧
          (∀ c x : ℝ,
            realConvolutionFun f (fun t => c * g t) x =
              realConvolutionFun (fun t => c * f t) g x ∧
            realConvolutionFun f (fun t => c * g t) x =
              c * realConvolutionFun f g x) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hgs' : HasCompactSupport g :=
    helperForProposition_3_23_hasCompactSupport_of_IsCompactlySupported g hgs
  have hcont_conv :
      Continuous (MeasureTheory.convolution f g L MeasureTheory.MeasureSpace.volume) :=
    hgs'.continuous_convolution_right (L := L) hf.locallyIntegrable hg
  have hcont : Continuous (realConvolutionFun f g) := by
    simpa [L, helperForProposition_3_23_realConvolutionFun_eq_star] using hcont_conv
  have hcomp : IsCompactlySupported (realConvolutionFun f g) :=
    helperForProposition_3_23_isCompactlySupported_convolutionFun f g hfs hgs
  have hmul_flip : L.flip = L := by
    ext
    rfl
  have hflip :
      MeasureTheory.convolution g f L MeasureTheory.MeasureSpace.volume =
        MeasureTheory.convolution f g L MeasureTheory.MeasureSpace.volume := by
    simpa [hmul_flip, L] using
      (MeasureTheory.convolution_flip (L := L)
        (μ := (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ)) (f := f) (g := g))
  have hcomm : ∀ x : ℝ, realConvolutionFun f g x = realConvolutionFun g f x := by
    intro x
    have hflip_x := congrArg (fun F : ℝ → ℝ => F x) hflip
    simpa [L, helperForProposition_3_23_realConvolutionFun_eq_star] using hflip_x.symm
  have hadd :
      ∀ x : ℝ,
        realConvolutionFun f (fun t => g t + h t) x =
          realConvolutionFun f g x + realConvolutionFun f h x :=
    helperForProposition_3_23_convolution_add_right f g h hf hg hh hgs hhs
  have hsmul_right :
      ∀ c x : ℝ,
        realConvolutionFun f (fun t => c * g t) x = c * realConvolutionFun f g x := by
    intro c x
    have hconv_smul :=
      MeasureTheory.convolution_smul (L := L) (μ := MeasureTheory.MeasureSpace.volume)
        (f := f) (g := g) (y := c)
    have hconv_smul_x := congrArg (fun F : ℝ → ℝ => F x) hconv_smul
    simpa [L, Pi.smul_apply, helperForProposition_3_23_realConvolutionFun_eq_star] using hconv_smul_x
  have hsmul_left :
      ∀ c x : ℝ,
        realConvolutionFun (fun t => c * f t) g x = c * realConvolutionFun f g x := by
    intro c x
    have hsmul_conv :=
      MeasureTheory.smul_convolution (L := L) (μ := MeasureTheory.MeasureSpace.volume)
        (f := f) (g := g) (y := c)
    have hsmul_conv_x := congrArg (fun F : ℝ → ℝ => F x) hsmul_conv
    simpa [L, Pi.smul_apply, helperForProposition_3_23_realConvolutionFun_eq_star] using hsmul_conv_x
  refine ⟨⟨hcont, hcomp⟩, hcomm, hadd, ?_⟩
  intro c x
  constructor
  · calc
      realConvolutionFun f (fun t => c * g t) x = c * realConvolutionFun f g x := hsmul_right c x
      _ = realConvolutionFun (fun t => c * f t) g x := (hsmul_left c x).symm
  · exact hsmul_right c x

/-- The convolution of `f` and `g` is absolutely convergent at every point. -/
def ConvolutionDefined (f g : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, MeasureTheory.Integrable (fun t : ℝ => f (x - t) * g t)

/-- A formal Dirac delta distribution, treated as a function for convolution statements. -/
noncomputable def diracDelta : ℝ → ℝ := fun x => if x = 0 then 1 else 0

/-- `diracDelta` is equal almost everywhere to `0` for Lebesgue measure on `ℝ`. -/
lemma diagnostic_diracDelta_ae_zero :
    (fun t : ℝ => diracDelta t) =ᵐ[MeasureTheory.MeasureSpace.volume] fun _ => 0 := by
  refine (MeasureTheory.ae_iff.2 ?_)
  simp [diracDelta]

/-- Every translate `t ↦ diracDelta (x - t)` is equal almost everywhere to `0`. -/
lemma diagnostic_diracDelta_shift_ae_zero (x : ℝ) :
    (fun t : ℝ => diracDelta (x - t)) =ᵐ[MeasureTheory.MeasureSpace.volume] fun _ => 0 := by
  refine (MeasureTheory.ae_iff.2 ?_)
  have hset : {t : ℝ | diracDelta (x - t) ≠ 0} = ({x} : Set ℝ) := by
    ext t
    by_cases htx : t = x
    · subst htx
      simp [diracDelta]
    · simp [diracDelta, htx, sub_eq_zero]
  simp [hset]

/-- The kernel `diracDelta` is integrable because it is almost everywhere zero. -/
lemma diagnostic_integrable_diracDelta : MeasureTheory.Integrable diracDelta := by
  have hzero : (fun t : ℝ => diracDelta t) =ᵐ[MeasureTheory.MeasureSpace.volume] fun _ => (0 : ℝ) :=
    diagnostic_diracDelta_ae_zero
  have hint0 : MeasureTheory.Integrable (fun _ : ℝ => (0 : ℝ)) := by
    simp [MeasureTheory.integrable_zero]
  exact hint0.congr hzero.symm

/-- Every translate `t ↦ diracDelta (x - t)` is integrable. -/
lemma diagnostic_integrable_diracDelta_shift (x : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => diracDelta (x - t)) := by
  have hzero : (fun t : ℝ => diracDelta (x - t)) =ᵐ[MeasureTheory.MeasureSpace.volume] fun _ => (0 : ℝ) :=
    diagnostic_diracDelta_shift_ae_zero x
  have hint0 : MeasureTheory.Integrable (fun _ : ℝ => (0 : ℝ)) := by
    simp [MeasureTheory.integrable_zero]
  exact hint0.congr hzero.symm

/-- Convolution of the constant-one function with `diracDelta` is identically `0`. -/
lemma diagnostic_realConvolutionFun_constOne_diracDelta_eq_zero (x : ℝ) :
    realConvolutionFun (fun _ : ℝ => (1 : ℝ)) diracDelta x = 0 := by
  rw [realConvolutionFun]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [diagnostic_diracDelta_ae_zero] with t ht
  simp [ht]

/-- Convolution of `diracDelta` with the constant-one function is identically `0`. -/
lemma diagnostic_realConvolutionFun_diracDelta_constOne_eq_zero (x : ℝ) :
    realConvolutionFun diracDelta (fun _ : ℝ => (1 : ℝ)) x = 0 := by
  rw [realConvolutionFun]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [diagnostic_diracDelta_shift_ae_zero x] with t ht
  simp [ht]

/-- The identity claim `(f*δ)(x) = (δ*f)(x) = f(x)` fails for `f ≡ 1`. -/
lemma diagnostic_diracDelta_identity_counterexample :
    ¬ (∀ x : ℝ,
        realConvolutionFun (fun _ : ℝ => (1 : ℝ)) diracDelta x = (1 : ℝ) ∧
        realConvolutionFun diracDelta (fun _ : ℝ => (1 : ℝ)) x = (1 : ℝ)) := by
  intro hIdentity
  have hAtZero := hIdentity 0
  have hLeft : realConvolutionFun (fun _ : ℝ => (1 : ℝ)) diracDelta 0 = 0 :=
    diagnostic_realConvolutionFun_constOne_diracDelta_eq_zero 0
  have h01 : (0 : ℝ) = 1 := by
    simpa [hLeft] using hAtZero.1
  norm_num at h01

/-- `ConvolutionDefined` holds for `f ≡ 1` with the formal `diracDelta` kernel. -/
lemma diagnostic_convolutionDefined_constOne_diracDelta :
    ConvolutionDefined (fun _ : ℝ => (1 : ℝ)) diracDelta := by
  intro x
  simpa using diagnostic_integrable_diracDelta

/-- `ConvolutionDefined` holds for `diracDelta` convolved with `f ≡ 1`. -/
lemma diagnostic_convolutionDefined_diracDelta_constOne :
    ConvolutionDefined diracDelta (fun _ : ℝ => (1 : ℝ)) := by
  intro x
  simpa using diagnostic_integrable_diracDelta_shift x

/-- There are explicit `f,g,h` satisfying all assumptions while the Dirac identity clause fails. -/
lemma diagnostic_counterexample_data_for_convolution_associativity_derivative_identity :
    ∃ f g h : ℝ → ℝ,
      ConvolutionDefined f g ∧
      ConvolutionDefined g h ∧
      ConvolutionDefined (realConvolutionFun f g) h ∧
      ConvolutionDefined f (realConvolutionFun g h) ∧
      ConvolutionDefined f diracDelta ∧
      ConvolutionDefined diracDelta f ∧
      ¬ (∀ x : ℝ,
          realConvolutionFun f diracDelta x = f x ∧
          realConvolutionFun diracDelta f x = f x) := by
  refine ⟨(fun _ : ℝ => (1 : ℝ)), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (0 : ℝ)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, diagnostic_convolutionDefined_constOne_diracDelta,
    diagnostic_convolutionDefined_diracDelta_constOne, ?_⟩
  · intro x
    simp [MeasureTheory.integrable_zero]
  · intro x
    simp [MeasureTheory.integrable_zero]
  · intro x
    simp [realConvolutionFun, MeasureTheory.integrable_zero]
  · intro x
    simp [realConvolutionFun, MeasureTheory.integrable_zero]
  · simpa using diagnostic_diracDelta_identity_counterexample

/-- Proposition 3.24 packaged with explicit analytic assumptions: besides the basic
`ConvolutionDefined` hypotheses, we assume associativity and derivative-commutation as
separate premises. Under these assumptions and the present function-level `diracDelta`,
convolution with `δ` vanishes pointwise. -/
theorem convolution_associativity_derivative_identity
    (f g h : ℝ → ℝ)
    (hfg : ConvolutionDefined f g)
    (hgh : ConvolutionDefined g h)
    (hfg_h : ConvolutionDefined (realConvolutionFun f g) h)
    (hf_gh : ConvolutionDefined f (realConvolutionFun g h))
    (hfd : ConvolutionDefined f diracDelta)
    (hdf : ConvolutionDefined diracDelta f)
    (hassoc : ∀ x : ℝ,
      realConvolutionFun (realConvolutionFun f g) h x =
        realConvolutionFun f (realConvolutionFun g h) x)
    (hderiv :
      (Differentiable ℝ f ∧ Differentiable ℝ g ∧
          ConvolutionDefined (deriv f) g ∧ ConvolutionDefined f (deriv g)) →
        (Differentiable ℝ (realConvolutionFun f g) ∧
          (∀ x : ℝ,
            deriv (realConvolutionFun f g) x =
              realConvolutionFun (deriv f) g x) ∧
          (∀ x : ℝ,
            deriv (realConvolutionFun f g) x =
              realConvolutionFun f (deriv g) x))) :
    (∀ x : ℝ,
      realConvolutionFun (realConvolutionFun f g) h x =
        realConvolutionFun f (realConvolutionFun g h) x) ∧
      ((Differentiable ℝ f ∧ Differentiable ℝ g ∧
          ConvolutionDefined (deriv f) g ∧ ConvolutionDefined f (deriv g)) →
        (Differentiable ℝ (realConvolutionFun f g) ∧
          (∀ x : ℝ,
            deriv (realConvolutionFun f g) x =
              realConvolutionFun (deriv f) g x) ∧
          (∀ x : ℝ,
            deriv (realConvolutionFun f g) x =
              realConvolutionFun f (deriv g) x))) ∧
      (∀ x : ℝ,
        realConvolutionFun f diracDelta x = 0 ∧
        realConvolutionFun diracDelta f x = 0) := by
  have _ := hfg
  have _ := hgh
  have _ := hfg_h
  have _ := hf_gh
  have _ := hfd
  have _ := hdf
  refine ⟨hassoc, hderiv, ?_⟩
  intro x
  constructor
  · rw [realConvolutionFun]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [diagnostic_diracDelta_ae_zero] with t ht
    simp [ht]
  · rw [realConvolutionFun]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    filter_upwards [diagnostic_diracDelta_shift_ae_zero x] with t ht
    simp [ht]

/-- The left endpoint `0` belongs to `[0,1]` as an element of `Set.Icc`. -/
lemma zero_mem_Icc01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨by norm_num, by norm_num⟩

/-- The right endpoint `1` belongs to `[0,1]` as an element of `Set.Icc`. -/
lemma one_mem_Icc01 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨by norm_num, by norm_num⟩

/-- Helper for Lemma 3.5: points outside `[0,1]` satisfy `x < 0 ∨ 1 < x`. -/
lemma helperForLemma_3_5_notMem_Icc01_split {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) : x < 0 ∨ 1 < x := by
  by_contra hxOut
  have hnotLeft : ¬ x < 0 := by
    intro hlt
    exact hxOut (Or.inl hlt)
  have hnotRight : ¬ 1 < x := by
    intro hlt
    exact hxOut (Or.inr hlt)
  have hx0 : 0 ≤ x := le_of_not_gt hnotLeft
  have hx1 : x ≤ 1 := le_of_not_gt hnotRight
  exact hx ⟨hx0, hx1⟩

/-- Helper for Lemma 3.5: the `Icc` extension is zero outside `[0,1]`
using the endpoint hypotheses. -/
lemma helperForLemma_3_5_IccExtend_zero_outside
    (h01 : (0 : ℝ) ≤ 1)
    (f : Set.Icc (0 : ℝ) 1 → ℝ)
    (hf0 : f ⟨0, zero_mem_Icc01⟩ = 0)
    (hf1 : f ⟨1, one_mem_Icc01⟩ = 0)
    {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    Set.IccExtend h01 f x = 0 := by
  rcases helperForLemma_3_5_notMem_Icc01_split hx with hLeft | hRight
  · calc
      Set.IccExtend h01 f x = f ⟨0, Set.left_mem_Icc.2 h01⟩ :=
        Set.IccExtend_of_le_left h01 f hLeft.le
      _ = 0 := by
        simpa using hf0
  · calc
      Set.IccExtend h01 f x = f ⟨1, Set.right_mem_Icc.2 h01⟩ :=
        Set.IccExtend_of_right_le h01 f hRight.le
      _ = 0 := by
        simpa using hf1

/-- Helper for Lemma 3.5: the `Icc` extension agrees with the `if`-defined function. -/
lemma helperForLemma_3_5_IccExtend_eq_ifExtension
    (h01 : (0 : ℝ) ≤ 1)
    (f : Set.Icc (0 : ℝ) 1 → ℝ)
    (hf0 : f ⟨0, zero_mem_Icc01⟩ = 0)
    (hf1 : f ⟨1, one_mem_Icc01⟩ = 0) :
    Set.IccExtend h01 f =
      (fun x => if h : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, h⟩ else 0) := by
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · simpa [hx] using (Set.IccExtend_of_mem h01 f hx)
  · have hzero : Set.IccExtend h01 f x = 0 :=
      helperForLemma_3_5_IccExtend_zero_outside h01 f hf0 hf1 hx
    simp [hx, hzero]

/-- Helper for Lemma 3.5: continuity of the clamped extension `Set.IccExtend`. -/
lemma helperForLemma_3_5_continuous_IccExtend
    (h01 : (0 : ℝ) ≤ 1)
    (f : Set.Icc (0 : ℝ) 1 → ℝ)
    (hf : Continuous f) :
    Continuous (Set.IccExtend h01 f) := by
  simpa using (hf.Icc_extend' (h := h01))

/-- Lemma 3.5: Let `f : [0,1] → ℝ` be continuous with `f(0)=f(1)=0`. Define
`F : ℝ → ℝ` by `F(x)=f(x)` for `x ∈ [0,1]` and `F(x)=0` for `x ∉ [0,1]`.
Then `F` is continuous on `ℝ`. -/
lemma continuous_extension_by_zero_Icc01
    (f : Set.Icc (0 : ℝ) 1 → ℝ) (hf : Continuous f)
    (hf0 : f ⟨0, zero_mem_Icc01⟩ = 0)
    (hf1 : f ⟨1, one_mem_Icc01⟩ = 0) :
    let F : ℝ → ℝ :=
      fun x => if h : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, h⟩ else 0
    Continuous F := by
  let h01 : (0 : ℝ) ≤ 1 := by norm_num
  change Continuous (fun x => if h : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, h⟩ else 0)
  have hcont : Continuous (Set.IccExtend h01 f) :=
    helperForLemma_3_5_continuous_IccExtend h01 f hf
  have hEq : Set.IccExtend h01 f =
      (fun x => if h : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, h⟩ else 0) :=
    helperForLemma_3_5_IccExtend_eq_ifExtension h01 f hf0 hf1
  rw [← hEq]
  exact hcont

/-- Theorem 3.13: (Weierstrass approximation theorem II) Let `f : [0,1] → ℝ` be
continuous and satisfy `f(0)=f(1)=0`. Then for every `ε > 0` there exists a polynomial
`P` such that `sup_{x ∈ [0,1]} |P(x) - f(x)| ≤ ε`. -/
theorem weierstrassApproximationOnIcc01_zeroEndpoints
    (f : Set.Icc (0 : ℝ) 1 → ℝ) (hf : Continuous f)
    (hf0 : f ⟨0, zero_mem_Icc01⟩ = 0)
    (hf1 : f ⟨1, one_mem_Icc01⟩ = 0) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x : Set.Icc (0 : ℝ) 1,
      |p.eval x.1 - f x| ≤ ε := by
  intro ε hε
  have _hf0 : f ⟨0, zero_mem_Icc01⟩ = 0 := hf0
  have _hf1 : f ⟨1, one_mem_Icc01⟩ = 0 := hf1
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  exact weierstrassApproximationOnIcc (a := 0) (b := 1) h01 f hf ε hε

/-- Theorem 3.14: [Weierstrass approximation theorem III] Let `f : [0,1] → ℝ` be
continuous. For every `ε > 0` there exists a polynomial `P : [0,1] → ℝ` such that
`sup_{x ∈ [0,1]} |P(x) - f(x)| ≤ ε`. -/
theorem weierstrassApproximationOnIcc01
    (f : Set.Icc (0 : ℝ) 1 → ℝ) (hf : Continuous f) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x : Set.Icc (0 : ℝ) 1,
      |p.eval x.1 - f x| ≤ ε := by
  intro ε hε
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  exact weierstrassApproximationOnIcc (a := 0) (b := 1) h01 f hf ε hε

/-- Theorem 3.15: [Weierstrass approximation theorem on `[a,b]`] Let `a < b` and let
`f : [a,b] → ℝ` be continuous. For every `ε > 0` there exists a polynomial `P` such that
`sup_{y ∈ [a,b]} |P(y) - f(y)| ≤ ε`. -/
theorem weierstrassApproximationOnIcc_sup
    (a b : ℝ) (hab : a < b) (f : Set.Icc a b → ℝ) (hf : Continuous f) :
    ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ y : Set.Icc a b, |p.eval y.1 - f y| ≤ ε := by
  intro ε hε
  exact weierstrassApproximationOnIcc a b hab f hf ε hε

end Section08
end Chap03
