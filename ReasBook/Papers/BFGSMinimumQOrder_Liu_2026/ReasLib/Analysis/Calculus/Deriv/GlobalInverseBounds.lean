module

public import ReasLib.Analysis.Calculus.Deriv.GlobalInverse
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

public section

open scoped NNReal BigOperators

namespace Real

/-- A uniform positive lower bound for the derivative of a `C¹` real function
gives the reciprocal uniform bound for the first derivative of its inverse. -/
theorem norm_iteratedDeriv_one_invFun_le {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : ContDiff ℝ 1 f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) (y : ℝ) :
    ‖iteratedDeriv 1 (Function.invFun f) y‖ ≤ (lower⁻¹ : ℝ) := by
  rw [iteratedDeriv_one]
  exact norm_deriv_le_of_lipschitz
    (lipschitzWith_invFun_of_pos_le_deriv (hf.differentiable (by norm_num))
      h_lower_pos h_lower)

/-- If the second derivative of a `C²` real function is bounded by
`secondBound`, then the second derivative of its inverse is bounded by
`secondBound * lower⁻¹ ^ 3`. -/
theorem norm_iteratedDeriv_two_invFun_le {f : ℝ → ℝ} {lower secondBound : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x)
    (h_second : ∀ x, ‖iteratedDeriv 2 f x‖ ≤ (secondBound : ℝ)) (y : ℝ) :
    ‖iteratedDeriv 2 (Function.invFun f) y‖ ≤
      (secondBound * lower⁻¹ ^ 3 : ℝ≥0) := by
  let g := Function.invFun f
  have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hsurj := surjective_of_pos_le_deriv hdiff h_lower_pos h_lower
  have hg : ContDiff ℝ 2 g :=
    contDiff_invFun_of_pos_le_deriv hf (by norm_num) h_lower_pos h_lower
  have hcomp : f ∘ g = id := funext (Function.rightInverse_invFun hsurj)
  have hchain := iteratedDeriv_comp_two (g := f) (f := g) (x := y)
    hf.contDiffAt hg.contDiffAt
  rw [hcomp] at hchain
  have hchain_zero : 0 = iteratedDeriv 2 f (g y) * deriv g y ^ 2 +
      deriv f (g y) * iteratedDeriv 2 g y := by
    simpa [iteratedDeriv_id] using hchain
  have ha_pos : 0 < deriv f (g y) := hlower.trans_le (h_lower (g y))
  have ha_ne : deriv f (g y) ≠ 0 := ne_of_gt ha_pos
  have hformula : iteratedDeriv 2 g y =
      -(iteratedDeriv 2 f (g y) * deriv g y ^ 2) / deriv f (g y) := by
    apply (eq_div_iff ha_ne).2
    nlinarith [hchain_zero]
  have hp : ‖deriv g y‖ ≤ (lower : ℝ)⁻¹ := by
    simpa [g, iteratedDeriv_one, NNReal.coe_inv] using
      norm_iteratedDeriv_one_invFun_le (hf.of_le (by norm_num))
        h_lower_pos h_lower y
  have hnum : ‖iteratedDeriv 2 f (g y)‖ * ‖deriv g y‖ ^ 2 ≤
      (secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 2 := by
    gcongr
    exact h_second (g y)
  have hden : ‖deriv f (g y)‖⁻¹ ≤ (lower : ℝ)⁻¹ := by
    rw [norm_of_nonneg ha_pos.le]
    exact (inv_le_inv₀ ha_pos hlower).2 (h_lower (g y))
  rw [hformula, norm_div, norm_neg, norm_mul, norm_pow, div_eq_mul_inv]
  change _ ≤ (secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 3
  calc
    ‖iteratedDeriv 2 f (g y)‖ * ‖deriv g y‖ ^ 2 * ‖deriv f (g y)‖⁻¹ ≤
        ((secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 2) * (lower : ℝ)⁻¹ := by
      exact mul_le_mul hnum hden (by positivity) (by positivity)
    _ = (secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 3 := by ring

/-- If the second and third derivatives of a `C³` real function have common
bounds, then the third derivative of its inverse obeys the explicit scalar
inverse-function bound. -/
theorem norm_iteratedDeriv_three_invFun_le {f : ℝ → ℝ}
    {lower secondBound thirdBound : ℝ≥0} (hf : ContDiff ℝ 3 f)
    (h_lower_pos : 0 < lower) (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x)
    (h_second : ∀ x, ‖iteratedDeriv 2 f x‖ ≤ (secondBound : ℝ))
    (h_third : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ (thirdBound : ℝ)) (y : ℝ) :
    ‖iteratedDeriv 3 (Function.invFun f) y‖ ≤
      (3 * secondBound ^ 2 * lower⁻¹ ^ 5 + thirdBound * lower⁻¹ ^ 4 : ℝ≥0) := by
  let g := Function.invFun f
  have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hsurj := surjective_of_pos_le_deriv hdiff h_lower_pos h_lower
  have hg : ContDiff ℝ 3 g :=
    contDiff_invFun_of_pos_le_deriv hf (by norm_num) h_lower_pos h_lower
  have hcomp : f ∘ g = id := funext (Function.rightInverse_invFun hsurj)
  have hchain := iteratedDeriv_comp_three (g := f) (f := g) (x := y)
    hf.contDiffAt hg.contDiffAt
  rw [hcomp] at hchain
  have hchain_zero : 0 = iteratedDeriv 3 f (g y) * deriv g y ^ 3 +
      3 * iteratedDeriv 2 f (g y) * iteratedDeriv 2 g y * deriv g y +
      deriv f (g y) * iteratedDeriv 3 g y := by
    simpa [iteratedDeriv_id] using hchain
  have ha_pos : 0 < deriv f (g y) := hlower.trans_le (h_lower (g y))
  have ha_ne : deriv f (g y) ≠ 0 := ne_of_gt ha_pos
  have hformula : iteratedDeriv 3 g y =
      -(iteratedDeriv 3 f (g y) * deriv g y ^ 3 +
        3 * iteratedDeriv 2 f (g y) * iteratedDeriv 2 g y * deriv g y) /
          deriv f (g y) := by
    apply (eq_div_iff ha_ne).2
    nlinarith [hchain_zero]
  have hp : ‖deriv g y‖ ≤ (lower : ℝ)⁻¹ := by
    simpa [g, iteratedDeriv_one, NNReal.coe_inv] using
      norm_iteratedDeriv_one_invFun_le (hf.of_le (by norm_num))
        h_lower_pos h_lower y
  have hq : ‖iteratedDeriv 2 g y‖ ≤
      (secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 3 := by
    simpa [g, NNReal.coe_inv] using
      norm_iteratedDeriv_two_invFun_le (hf.of_le (by norm_num))
        h_lower_pos h_lower h_second y
  have hterm1 : ‖iteratedDeriv 3 f (g y) * deriv g y ^ 3‖ ≤
      (thirdBound : ℝ) * (lower : ℝ)⁻¹ ^ 3 := by
    rw [norm_mul, norm_pow]
    gcongr
    exact h_third (g y)
  have hterm2 :
      ‖3 * iteratedDeriv 2 f (g y) * iteratedDeriv 2 g y * deriv g y‖ ≤
        3 * (secondBound : ℝ) ^ 2 * (lower : ℝ)⁻¹ ^ 4 := by
    simp only [norm_mul, norm_ofNat]
    calc
      3 * ‖iteratedDeriv 2 f (g y)‖ * ‖iteratedDeriv 2 g y‖ * ‖deriv g y‖ ≤
          3 * (secondBound : ℝ) *
            ((secondBound : ℝ) * (lower : ℝ)⁻¹ ^ 3) * (lower : ℝ)⁻¹ := by
        gcongr
        exact h_second (g y)
      _ = 3 * (secondBound : ℝ) ^ 2 * (lower : ℝ)⁻¹ ^ 4 := by ring
  have hden : ‖deriv f (g y)‖⁻¹ ≤ (lower : ℝ)⁻¹ := by
    rw [norm_of_nonneg ha_pos.le]
    exact (inv_le_inv₀ ha_pos hlower).2 (h_lower (g y))
  rw [hformula, norm_div, norm_neg, div_eq_mul_inv]
  change _ ≤ 3 * (secondBound : ℝ) ^ 2 * (lower : ℝ)⁻¹ ^ 5 +
    (thirdBound : ℝ) * (lower : ℝ)⁻¹ ^ 4
  calc
    ‖iteratedDeriv 3 f (g y) * deriv g y ^ 3 +
        3 * iteratedDeriv 2 f (g y) * iteratedDeriv 2 g y * deriv g y‖ *
        ‖deriv f (g y)‖⁻¹ ≤
      (‖iteratedDeriv 3 f (g y) * deriv g y ^ 3‖ +
        ‖3 * iteratedDeriv 2 f (g y) * iteratedDeriv 2 g y * deriv g y‖) *
          ‖deriv f (g y)‖⁻¹ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((thirdBound : ℝ) * (lower : ℝ)⁻¹ ^ 3 +
        3 * (secondBound : ℝ) ^ 2 * (lower : ℝ)⁻¹ ^ 4) *
          (lower : ℝ)⁻¹ := by
      exact mul_le_mul (add_le_add hterm1 hterm2) hden (by positivity) (by positivity)
    _ = 3 * (secondBound : ℝ) ^ 2 * (lower : ℝ)⁻¹ ^ 5 +
        (thirdBound : ℝ) * (lower : ℝ)⁻¹ ^ 4 := by ring


private theorem comp_deriv_bound {f g : ℝ → ℝ}
    {forwardBound inverseBound : ℕ → ℝ≥0} {ν j k : ℕ}
    (hk : 1 ≤ k) (hkj : k < j) (hjν : j ≤ ν)
    (hf : ContDiff ℝ ν f) (hg : ContDiff ℝ ν g)
    (hforward : ∀ r, 2 ≤ r → r ≤ ν → ∀ x,
      ‖iteratedDeriv r f x‖ ≤ (forwardBound r : ℝ))
    (hinverse : ∀ r, 1 ≤ r → r < j → ∀ y,
      ‖iteratedDeriv r g y‖ ≤ (inverseBound r : ℝ)) (y : ℝ) :
    ‖iteratedDeriv k (deriv f ∘ g) y‖ ≤
      (∑ c : OrderedFinpartition k,
        forwardBound (c.length + 1) * ∏ m, inverseBound (c.partSize m) : ℝ≥0) := by
  have hkν : k ≤ ν := le_trans (Nat.le_of_lt hkj) hjν
  have hdf : ContDiff ℝ k (deriv f) :=
    (hf.of_le (by exact_mod_cast (show k + 1 ≤ ν by omega))).deriv'
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast hkν)
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hdf.contDiffAt hgk.contDiffAt le_rfl]
  calc
    ‖∑ c : OrderedFinpartition k,
        iteratedDeriv c.length (deriv f) (g y) *
          ∏ m, iteratedDeriv (c.partSize m) g y‖ ≤
        ∑ c : OrderedFinpartition k,
          ‖iteratedDeriv c.length (deriv f) (g y) *
            ∏ m, iteratedDeriv (c.partSize m) g y‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition k,
        ((forwardBound (c.length + 1) : ℝ) *
          ∏ m, (inverseBound (c.partSize m) : ℝ)) := by
      gcongr with c
      rw [norm_mul, norm_prod]
      apply mul_le_mul
      · rw [← congrFun (iteratedDeriv_succ' (n := c.length) (f := f)) (g y)]
        exact hforward (c.length + 1)
          (by have := c.length_pos (lt_of_lt_of_le Nat.zero_lt_one hk); omega)
          (by have := c.length_le; omega) (g y)
      · gcongr with m
        exact hinverse (c.partSize m) (c.partSize_pos m)
          (lt_of_le_of_lt (c.partSize_le m) hkj) y
      · positivity
      · positivity
    _ = (∑ c : OrderedFinpartition k,
        forwardBound (c.length + 1) * ∏ m, inverseBound (c.partSize m) : ℝ≥0) := by
      norm_cast
/-- A family of `C^ν` real functions with a common positive derivative lower
bound and common higher-order forward derivative bounds admits one family-independent
bound for every inverse derivative through order `ν`. -/
theorem exists_uniform_iteratedDeriv_invFun_bound {I : Type*} {f : I → ℝ → ℝ}
    {lower : ℝ≥0} {forwardBound : ℕ → ℝ≥0} {ν : ℕ} (hν : 1 ≤ ν)
    (h_smooth : ∀ i, ContDiff ℝ ν (f i)) (h_lower_pos : 0 < lower)
    (h_lower : ∀ i x, (lower : ℝ) ≤ deriv (f i) x)
    (h_forward : ∀ j, 2 ≤ j → j ≤ ν → ∀ i x,
      ‖iteratedDeriv j (f i) x‖ ≤ (forwardBound j : ℝ)) :
    ∃ inverseBound : ℕ → ℝ≥0, inverseBound 1 = lower⁻¹ ∧
      ∀ j, 1 ≤ j → j ≤ ν → ∀ i y,
        ‖iteratedDeriv j (Function.invFun (f i)) y‖ ≤ (inverseBound j : ℝ) := by
  classical
  let P : ℕ → ℝ≥0 → Prop := fun j B ↦ ∀ i y,
    ‖iteratedDeriv j (Function.invFun (f i)) y‖ ≤ (B : ℝ)
  have hex : ∀ j, j ≤ ν → 1 ≤ j → ∃ B : ℝ≥0, P j B := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjν hj1
      by_cases hj_eq : j = 1
      · subst j
        refine ⟨lower⁻¹, ?_⟩
        intro i y
        exact norm_iteratedDeriv_one_invFun_le
          ((h_smooth i).of_le (by exact_mod_cast hjν)) h_lower_pos (h_lower i) y
      · have hj2 : 2 ≤ j := by omega
        let b : ℕ → ℝ≥0 := fun r ↦
          if hr : 1 ≤ r ∧ r < j then
            Classical.choose
              (ih r hr.2 (le_trans (Nat.le_of_lt hr.2) hjν) hr.1)
          else 0
        have hb (r : ℕ) (hr1 : 1 ≤ r) (hrj : r < j) : P r (b r) := by
          dsimp [b]
          rw [dif_pos ⟨hr1, hrj⟩]
          exact Classical.choose_spec
            (ih r hrj (le_trans (Nat.le_of_lt hrj) hjν) hr1)
        let n := j - 1
        have hn_pos : 0 < n := by dsimp [n]; omega
        have hnj : n + 1 = j := by dsimp [n]; omega
        let A : ℕ → ℝ≥0 := fun k ↦
          ∑ c : OrderedFinpartition k,
            forwardBound (c.length + 1) * ∏ m, b (c.partSize m)
        let R : ℝ≥0 :=
          ∑ k ∈ (Finset.range (n + 1)).erase 0,
            (n.choose k : ℝ≥0) * A k * b (n - k + 1)
        refine ⟨lower⁻¹ * R, ?_⟩
        intro i y
        let g := Function.invFun (f i)
        have hν' : (1 : ℕ) ≤ ν := le_trans hj1 hjν
        have hfi_diff : Differentiable ℝ (f i) :=
          (h_smooth i).differentiable (by exact_mod_cast (Nat.ne_of_gt hν'))
        have hsurj := surjective_of_pos_le_deriv hfi_diff h_lower_pos (h_lower i)
        have hg : ContDiff ℝ ν g :=
          contDiff_invFun_of_pos_le_deriv (h_smooth i) hν' h_lower_pos (h_lower i)
        have hg_diff : Differentiable ℝ g :=
          hg.differentiable (by exact_mod_cast (Nat.ne_of_gt hν'))
        have hcomp : f i ∘ g = id := funext (Function.rightInverse_invFun hsurj)
        have hprod : (deriv (f i) ∘ g) * deriv g = fun _ ↦ 1 := by
          funext z
          have hz := deriv_comp z hfi_diff.differentiableAt hg_diff.differentiableAt
          rw [hcomp] at hz
          simpa [Function.comp_def] using hz.symm
        have hdfn : ContDiff ℝ n (deriv (f i)) :=
          ((h_smooth i).of_le (by
            exact_mod_cast (show n + 1 ≤ ν by omega))).deriv'
        have hgn : ContDiff ℝ n g :=
          hg.of_le (by exact_mod_cast (show n ≤ ν by omega))
        have hA_smooth : ContDiff ℝ n (deriv (f i) ∘ g) := hdfn.comp hgn
        have hB_smooth : ContDiff ℝ n (deriv g) :=
          (hg.of_le (by exact_mod_cast (show n + 1 ≤ ν by omega))).deriv'
        have hzero : iteratedDeriv n ((deriv (f i) ∘ g) * deriv g) y = 0 := by
          rw [hprod]
          simp [iteratedDeriv_const, hn_pos.ne']
        have hleib := iteratedDeriv_mul (x := y)
          hA_smooth.contDiffAt hB_smooth.contDiffAt
        let term : ℕ → ℝ := fun k ↦
          n.choose k * iteratedDeriv k (deriv (f i) ∘ g) y *
            iteratedDeriv (n - k) (deriv g) y
        have hterm0 : term 0 = deriv (f i) (g y) * iteratedDeriv j g y := by
          dsimp [term]
          rw [← congrFun (iteratedDeriv_succ' (n := n) (f := g)) y, hnj]
          simp [Function.comp_def]
        have hsum :
            (∑ k ∈ (Finset.range (n + 1)).erase 0, term k) +
              deriv (f i) (g y) * iteratedDeriv j g y = 0 := by
          rw [← hterm0, Finset.sum_erase_add _ _ (by simp)]
          calc
            (∑ k ∈ Finset.range (n + 1), term k) =
                iteratedDeriv n ((deriv (f i) ∘ g) * deriv g) y := by
              simpa [term] using hleib.symm
            _ = 0 := hzero
        have ha_pos : 0 < deriv (f i) (g y) := by
          have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
          exact hlower.trans_le (h_lower i (g y))
        have ha_ne : deriv (f i) (g y) ≠ 0 := ne_of_gt ha_pos
        have hformula : iteratedDeriv j g y =
            -(∑ k ∈ (Finset.range (n + 1)).erase 0, term k) /
              deriv (f i) (g y) := by
          apply (eq_div_iff ha_ne).2
          nlinarith [hsum]
        have hterm (k : ℕ) (hk : k ∈ (Finset.range (n + 1)).erase 0) :
            ‖term k‖ ≤ (n.choose k : ℝ) * (A k : ℝ) * (b (n - k + 1) : ℝ) := by
          have hk_ne : k ≠ 0 := (Finset.mem_erase.mp hk).1
          have hk_lt : k < n + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
          have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_ne
          have hAk : ‖iteratedDeriv k (deriv (f i) ∘ g) y‖ ≤ (A k : ℝ) := by
            dsimp [A]
            exact comp_deriv_bound hk1 (by omega) hjν (h_smooth i) hg
              (fun r hr2 hrν x ↦ h_forward r hr2 hrν i x)
              (fun r hr1 hrj z ↦ hb r hr1 hrj i z) y
          have hBk : ‖iteratedDeriv (n - k) (deriv g) y‖ ≤
              (b (n - k + 1) : ℝ) := by
            rw [← congrFun (iteratedDeriv_succ' (n := n - k) (f := g)) y]
            exact hb (n - k + 1) (by omega) (by omega) i y
          dsimp [term]
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          gcongr
          · simpa only [Real.norm_eq_abs] using hAk
          · simpa only [Real.norm_eq_abs] using hBk
        have hrest : ‖∑ k ∈ (Finset.range (n + 1)).erase 0, term k‖ ≤ (R : ℝ) := by
          calc
            ‖∑ k ∈ (Finset.range (n + 1)).erase 0, term k‖ ≤
                ∑ k ∈ (Finset.range (n + 1)).erase 0, ‖term k‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ (Finset.range (n + 1)).erase 0,
                ((n.choose k : ℝ) * (A k : ℝ) * (b (n - k + 1) : ℝ)) := by
              gcongr with k hk
              exact hterm k hk
            _ = (R : ℝ) := by
              dsimp [R]
              norm_cast
        have hden : ‖deriv (f i) (g y)‖⁻¹ ≤ (lower : ℝ)⁻¹ := by
          rw [norm_of_nonneg ha_pos.le]
          have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
          exact (inv_le_inv₀ ha_pos hlower).2 (h_lower i (g y))
        rw [hformula, norm_div, norm_neg, div_eq_mul_inv]
        change _ ≤ (lower : ℝ)⁻¹ * (R : ℝ)
        calc
          _ ≤ (R : ℝ) * (lower : ℝ)⁻¹ :=
            mul_le_mul hrest hden (by positivity) (by positivity)
          _ = (lower : ℝ)⁻¹ * (R : ℝ) := mul_comm _ _
  let B₀ : ℕ → ℝ≥0 := fun j ↦
    if hj : 1 ≤ j ∧ j ≤ ν then Classical.choose (hex j hj.2 hj.1) else 0
  let inverseBound : ℕ → ℝ≥0 := fun j ↦ if j = 1 then lower⁻¹ else B₀ j
  refine ⟨inverseBound, by simp [inverseBound], ?_⟩
  intro j hj1 hjν i y
  by_cases hj : j = 1
  · subst j
    simp only [inverseBound, ↓reduceIte]
    exact norm_iteratedDeriv_one_invFun_le
      ((h_smooth i).of_le (by exact_mod_cast hν)) h_lower_pos (h_lower i) y
  · have hB : P j (B₀ j) := by
      dsimp [B₀]
      rw [dif_pos ⟨hj1, hjν⟩]
      exact Classical.choose_spec (hex j hjν hj1)
    simpa [inverseBound, hj] using hB i y

end Real
