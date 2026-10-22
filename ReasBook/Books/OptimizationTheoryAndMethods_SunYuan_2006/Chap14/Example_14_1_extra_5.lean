/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_1

noncomputable section

/- The repository does not carry a local `source/` tree for this item. This file therefore keeps
the explicit dyadic-shell owner from `(14.1.43)`-`(14.1.44)` using the printed source branch on the
positive dyadic shells together with the source symmetry clause on `[-1, 0)`. The accessible book
PDF reproduces that branch together with the later Lipschitz/Clarke/non-extremum claims, but no
authoritative erratum correcting the printed formula was found during statement repair, so this
file leaves that theorem layer unresolved rather than certifying those claims over the literal
printed branch. -/

/-- The interval `[-1, 1]` on which Chapter14 Example 14.1-extra-5 is stated. -/
def example141Extra5Domain : Set ℝ :=
  Set.Icc (-1 : ℝ) 1

/-- The dyadic shell index attached to `x ≠ 0`, obtained from the binary ceiling logarithm of
`|x|⁻¹`. This selects the shell used in the printed branch formula `(14.1.43)`. -/
def example141Extra5DyadicIndex (x : ℝ) : ℤ :=
  Int.clog 2 |x|⁻¹

/-- The nonzero value from the printed branch `(14.1.43)` and the symmetry clause `(14.1.44)`,
written globally using `|x|`: on each nonzero dyadic shell selected by
`example141Extra5DyadicIndex`, the value is
`(-1)^(k + 1) * (1 / 2^(k + 1) - 3 * |x|)`. -/
def example141Extra5NonzeroValue (x : ℝ) : ℝ :=
  let k := example141Extra5DyadicIndex x
  ((-1 : ℝ) ^ (k + 1)) * (((2 : ℝ) ^ (-(k + 1))) - 3 * |x|)

/-- The explicit dyadic-shell function from the printed formulas `(14.1.43)`-`(14.1.44)`, with
`f 0 = 0`, the positive-shell affine branch encoded through `example141Extra5NonzeroValue`, and
the left-side symmetry clause written globally through `|x|`. -/
def example141Extra5Function (x : ℝ) : ℝ :=
  by
    classical
    exact
      if x ∈ example141Extra5Domain then
        if x = 0 then 0 else example141Extra5NonzeroValue x
      else
        0

/-- sun_yuan_otm_ch14_example_14_1_extra_5_0611
Chapter14 Example 14.1-extra-5: for the explicit dyadic-shell function from `(14.1.43)`-`(14.1.44)`,
the textbook claim package consists of a Lipschitz bound on `[-1, 1]`, the Clarke directional
derivative identities `fᵒ(0; ±1) = 3`, and the assertion that `0` is not a local extremum. In
this workspace, that package is kept as the labeled source-facing proposition, while the literal
printed branch remains uncertified because no authoritative erratum correcting the source formula
is available. -/
structure example141Extra5SourceClaim : Prop where
  /-- The textbook package claims a Lipschitz bound on `[-1, 1]`. -/
  lipschitzOnDomain :
    ∃ K : NNReal, LipschitzOnWith K example141Extra5Function example141Extra5Domain
  /-- The right Clarke directional derivative at `0` is the printed value `3`. -/
  clarkeDirectionalDeriv_pos :
    clarkeDirectionalDerivReal example141Extra5Function 0 1 = 3
  /-- The left Clarke directional derivative at `0` is the printed value `3`. -/
  clarkeDirectionalDeriv_neg :
    clarkeDirectionalDerivReal example141Extra5Function 0 (-1) = 3
  /-- The textbook package asserts that `0` is not a local extremum. -/
  not_isLocalExtr :
    ¬ IsLocalExtr example141Extra5Function (0 : ℝ)

namespace example141Extra5SourceClaim

/-- Construct the labeled source-claim package from its four textbook clauses. -/
def ofComponents
    (h_lipschitzOnDomain :
      ∃ K : NNReal, LipschitzOnWith K example141Extra5Function example141Extra5Domain)
    (h_clarkeDirectionalDeriv_pos :
      clarkeDirectionalDerivReal example141Extra5Function 0 1 = 3)
    (h_clarkeDirectionalDeriv_neg :
      clarkeDirectionalDerivReal example141Extra5Function 0 (-1) = 3)
    (h_not_isLocalExtr :
      ¬ IsLocalExtr example141Extra5Function (0 : ℝ)) :
    example141Extra5SourceClaim :=
  { lipschitzOnDomain := h_lipschitzOnDomain
    clarkeDirectionalDeriv_pos := h_clarkeDirectionalDeriv_pos
    clarkeDirectionalDeriv_neg := h_clarkeDirectionalDeriv_neg
    not_isLocalExtr := h_not_isLocalExtr }

end example141Extra5SourceClaim

/-- Unfolding formula for the labeled source claim package of Chapter14 Example 14.1-extra-5. -/
theorem example141Extra5SourceClaim_iff :
    example141Extra5SourceClaim ↔
      (∃ K : NNReal, LipschitzOnWith K example141Extra5Function example141Extra5Domain) ∧
        clarkeDirectionalDerivReal example141Extra5Function 0 1 = 3 ∧
        clarkeDirectionalDerivReal example141Extra5Function 0 (-1) = 3 ∧
        ¬ IsLocalExtr example141Extra5Function (0 : ℝ) := by
  constructor
  · intro h
    exact ⟨h.lipschitzOnDomain, h.clarkeDirectionalDeriv_pos, h.clarkeDirectionalDeriv_neg,
      h.not_isLocalExtr⟩
  · rintro ⟨h_lipschitzOnDomain, h_clarkeDirectionalDeriv_pos, h_clarkeDirectionalDeriv_neg,
      h_not_isLocalExtr⟩
    exact example141Extra5SourceClaim.ofComponents
      h_lipschitzOnDomain
      h_clarkeDirectionalDeriv_pos
      h_clarkeDirectionalDeriv_neg
      h_not_isLocalExtr

/-- Helper for Chapter14 Example 14.1-extra-5: on the first positive dyadic shell
`[1 / 2, 1)`, the binary ceiling-log index is `1`. -/
lemma example141Extra5DyadicIndex_eq_one_of_memFirstShell {x : ℝ}
    (hx : x ∈ Set.Ico (1 / 2 : ℝ) 1) :
    example141Extra5DyadicIndex x = 1 := by
  have hx_pos : 0 < x := by
    linarith [hx.1]
  have h_one_lt_inv : 1 < x⁻¹ := by
    exact (one_lt_inv₀ hx_pos).2 hx.2
  have h_inv_le_two : x⁻¹ ≤ (2 : ℝ) := by
    have h_half_pos : (0 : ℝ) < 1 / 2 := by
      norm_num
    have h_inv_le_half_inv : x⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ hx_pos h_half_pos).2 hx.1
    simpa using h_inv_le_half_inv
  have hceil : ⌈x⁻¹⌉₊ = 2 := by
    exact
      (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).2
        ⟨by simpa using h_one_lt_inv, h_inv_le_two⟩
  -- Reduce the shell index to the ceiling of `x⁻¹`, then evaluate that ceiling on this shell.
  calc
    example141Extra5DyadicIndex x = Int.clog 2 x⁻¹ := by
      simp [example141Extra5DyadicIndex, abs_of_pos hx_pos]
    _ = Nat.clog 2 ⌈x⁻¹⌉₊ := by
      rw [Int.clog_of_one_le_right 2 h_one_lt_inv.le]
    _ = 1 := by
      rw [hceil]
      norm_num [Nat.clog_eq_one (by norm_num : 2 ≤ (2 : ℕ)) (by norm_num : (2 : ℕ) ≤ 2)]

/-- Helper for Chapter14 Example 14.1-extra-5: on the first positive dyadic shell,
`example141Extra5Function` is the affine branch `1 / 4 - 3x`. -/
lemma example141Extra5Function_eq_firstShell {x : ℝ}
    (hx : x ∈ Set.Ico (1 / 2 : ℝ) 1) :
    example141Extra5Function x = (1 / 4 : ℝ) - 3 * x := by
  have hx_mem : x ∈ example141Extra5Domain := by
    constructor
    · linarith [hx.1]
    · exact hx.2.le
  have hx_ne : x ≠ 0 := by
    linarith [hx.1]
  have hx_pos : 0 < x := by
    linarith [hx.1]
  have hindex : example141Extra5DyadicIndex x = 1 :=
    example141Extra5DyadicIndex_eq_one_of_memFirstShell hx
  -- Route correction: hide the `Int.clog` normalization behind the shell index helper,
  -- then evaluate the printed branch at `k = 1`.
  rw [example141Extra5Function, if_pos hx_mem, if_neg hx_ne]
  simp [example141Extra5NonzeroValue, hindex, abs_of_pos hx_pos]
  norm_num

/-- Helper for Chapter14 Example 14.1-extra-5: the literal printed branch takes the value
`5 / 2` at the right endpoint `x = 1`. -/
lemma example141Extra5Function_one :
    example141Extra5Function 1 = 5 / 2 := by
  have h_mem : (1 : ℝ) ∈ example141Extra5Domain := by
    simp [example141Extra5Domain]
  have h_ne : (1 : ℝ) ≠ 0 := by
    norm_num
  -- At `x = 1`, the ceiling-log index collapses to `0`, so the printed branch is explicit.
  rw [example141Extra5Function, if_pos h_mem, if_neg h_ne]
  simp [example141Extra5NonzeroValue, example141Extra5DyadicIndex, Int.clog_one_right]
  norm_num

/-- Helper for Chapter14 Example 14.1-extra-5: once both `x` and `-x` lie in the domain and the
nonzero branch is active, the function is even because it depends only on `|x|`. -/
lemma example141Extra5Function_neg_eq_of_memDomain {x : ℝ}
    (hx : x ∈ example141Extra5Domain)
    (hnegx : -x ∈ example141Extra5Domain)
    (hx_ne : x ≠ 0) :
    example141Extra5Function (-x) = example141Extra5Function x := by
  have hnegx_ne : -x ≠ 0 := by
    exact neg_ne_zero.mpr hx_ne
  -- Both evaluations reduce to the same nonzero branch after `abs_neg`.
  rw [example141Extra5Function, if_pos hnegx, if_neg hnegx_ne]
  rw [example141Extra5Function, if_pos hx, if_neg hx_ne]
  simp [example141Extra5NonzeroValue, example141Extra5DyadicIndex, abs_neg]

/-- Chapter14 Example 14.1-extra-5: the literal printed branch from `(14.1.43)` fails the
textbook Lipschitz claim on `[-1, 1]`, so the later theorem package is not certified here without
an authoritative correction to the source formula. -/
theorem example141Extra5_literalPrintedBranch_notLipschitzOnDomain :
    ¬ ∃ K : NNReal, LipschitzOnWith K example141Extra5Function example141Extra5Domain := by
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (K : ℝ) / 15)
  set x : ℝ := 1 - 1 / ((n : ℝ) + 2) with hx_def
  have hx_shell : x ∈ Set.Ico (1 / 2 : ℝ) 1 := by
    constructor
    · -- The explicit test points approach `1` from the left while staying in the first shell.
      have h_two_le : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have h_n_nonneg : (0 : ℝ) ≤ n := by
          exact_mod_cast Nat.zero_le n
        nlinarith
      have h_frac_le_half : 1 / ((n : ℝ) + 2) ≤ (1 / 2 : ℝ) := by
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h_two_le
      rw [hx_def]
      nlinarith
    · have h_frac_pos : 0 < 1 / ((n : ℝ) + 2) := by
        positivity
      rw [hx_def]
      nlinarith
  have hx_mem : x ∈ example141Extra5Domain := by
    constructor
    · linarith [hx_shell.1]
    · exact hx_shell.2.le
  have h_one_mem : (1 : ℝ) ∈ example141Extra5Domain := by
    simp [example141Extra5Domain]
  have h_lower : (15 / 4 : ℝ) ≤
      |example141Extra5Function x - example141Extra5Function 1| := by
    -- The jump between the left-shell affine branch and the endpoint value stays uniformly large.
    rw [example141Extra5Function_eq_firstShell hx_shell, example141Extra5Function_one, hx_def]
    have h_two_le : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have h_n_nonneg : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      nlinarith
    have h_frac_le_half : 1 / ((n : ℝ) + 2) ≤ (1 / 2 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h_two_le
    have h_neg :
        1 / 4 - 3 * (1 - 1 / ((n : ℝ) + 2)) - 5 / 2 < 0 := by
      nlinarith
    rw [abs_of_neg h_neg]
    nlinarith
  have h_dist_x_one : dist x 1 = 1 / ((n : ℝ) + 2) := by
    -- The test points are exactly `1 / (n + 2)` away from the endpoint `1`.
    rw [Real.dist_eq, hx_def]
    have h_frac_pos : 0 < 1 / ((n : ℝ) + 2) := by
      positivity
    have h_sub_neg : 1 - 1 / ((n : ℝ) + 2) - 1 < 0 := by
      nlinarith
    rw [abs_of_neg h_sub_neg]
    ring
  have h_upper :
      |example141Extra5Function x - example141Extra5Function 1| ≤
        (K : ℝ) / ((n : ℝ) + 2) := by
    -- The assumed Lipschitz estimate bounds the same difference by the endpoint distance.
    calc
      |example141Extra5Function x - example141Extra5Function 1| =
          dist (example141Extra5Function x) (example141Extra5Function 1) := by
            rw [Real.dist_eq]
      _ ≤ (K : ℝ) * dist x 1 := hK.dist_le_mul x hx_mem 1 h_one_mem
      _ = (K : ℝ) / ((n : ℝ) + 2) := by
            rw [h_dist_x_one]
            ring
  have h_small : (K : ℝ) / ((n : ℝ) + 2) < 15 / 4 := by
    have h_pos : 0 < (n : ℝ) + 2 := by
      positivity
    rw [div_lt_iff₀ h_pos]
    nlinarith
  linarith

/-- The defining clause `(14.1.43)` gives `f(0) = 0`. -/
theorem example141Extra5Function_zero :
    example141Extra5Function 0 = 0 := by
  have h_mem : (0 : ℝ) ∈ example141Extra5Domain := by
    simp [example141Extra5Domain]
  -- At the origin, the defining `if` branches reduce directly to the printed value `0`.
  simp [example141Extra5Function, h_mem]

/-- Verified symmetry clause for Chapter14 Example 14.1-extra-5: the source formula satisfies
`f(x) = f(-x)` on `[-1, 0)`. -/
theorem example141Extra5Counterexample_symmOnLeft :
    ∀ x ∈ Set.Ico (-1 : ℝ) 0,
      example141Extra5Function x = example141Extra5Function (-x) := by
  intro x hx
  have hx_mem : x ∈ example141Extra5Domain := by
    constructor
    · exact hx.1
    · linarith [hx.2]
  have hnegx_mem : -x ∈ example141Extra5Domain := by
    constructor
    · linarith [hx.2]
    · linarith [hx.1]
  have hx_ne : x ≠ 0 := by
    linarith [hx.2]
  -- On `[-1, 0)`, both `x` and `-x` stay inside the domain, so the evenness helper applies.
  simpa using (example141Extra5Function_neg_eq_of_memDomain hx_mem hnegx_mem hx_ne).symm

#print axioms example141Extra5DyadicIndex
#print axioms example141Extra5NonzeroValue
#print axioms example141Extra5Function
