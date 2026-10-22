/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Jensen
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section ToRealJensen

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- Companion bridge for Proposition 2.2: on the effective domain of a proper convex
extended-real-valued function, the textbook simplex Jensen inequality is the standard real-valued
Jensen inequality for `x ↦ (f x).toReal`. -/
theorem toReal_convex_function_jensen_inequality {k : ℕ} [IsProperExtendedRealFunction f]
    (hf : is_convex_function f) (x : Fin k → E) (hx : ∀ i, x i ∈ effective_domain f)
    (w : stdSimplex ℝ (Fin k)) :
    (f (∑ i, w i • x i)).toReal ≤ ∑ i, w i * (f (x i)).toReal := by
  let hf_toReal := convexOn_toReal_of_is_convex_function_of_proper f hf
  have hJensen :
      (f (∑ i, w i • x i)).toReal ≤ ∑ i, w i • (f (x i)).toReal :=
    hf_toReal.map_sum_le
      (fun i _ ↦ stdSimplex.zero_le w i) (stdSimplex.sum_eq_one w) (fun i _ ↦ hx i)
  simpa [smul_eq_mul] using hJensen

end ToRealJensen

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 2.2: a positive simplex weight on a point outside `effective_domain f`
forces the corresponding weighted extended-real value to be `⊤`. -/
private theorem weightedValue_eq_top_of_notMemEffectiveDomain {k : ℕ}
    (x : Fin k → E) (w : stdSimplex ℝ (Fin k)) {i : Fin k}
    (hx : x i ∉ effective_domain f) (hwi : 0 < w i) :
    w i * f (x i) = ⊤ := by
  have htop : f (x i) = ⊤ := by
    rw [mem_effective_domain] at hx
    exact le_antisymm le_top (le_of_not_gt hx)
  -- Outside the effective domain, the function value is `⊤`, and a positive real weight preserves it.
  calc
    w i * f (x i) = (w i : EReal) * ⊤ := by rw [htop]
    _ = ⊤ := by simpa using EReal.coe_mul_top_of_pos hwi

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 2.2: if some point outside `effective_domain f` receives nonzero
weight, then the weighted extended-real sum is `⊤`. -/
private theorem weightedValueSum_eq_top_of_exists_notMemEffectiveDomain {k : ℕ}
    (h_ne_bot : ∀ z, f z ≠ ⊥) (x : Fin k → E) (w : stdSimplex ℝ (Fin k))
    (hbad : ∃ i, x i ∉ effective_domain f ∧ w i ≠ 0) :
    ∑ i, w i * f (x i) = ⊤ := by
  classical
  obtain ⟨i, hi_dom, hi_ne_zero⟩ := hbad
  have hi_pos : 0 < w i := lt_of_le_of_ne (stdSimplex.zero_le w i) hi_ne_zero.symm
  have hi_top : w i * f (x i) = ⊤ :=
    weightedValue_eq_top_of_notMemEffectiveDomain (f := f) x w hi_dom hi_pos
  have htail_ne_bot :
      Finset.sum (Finset.univ.erase i) (fun j ↦ w j * f (x j)) ≠ ⊥ := by
    intro hsum_bot
    have hsum_bot' :
        ∃ j ∈ Finset.univ.erase i, w j * f (x j) = ⊥ := by
      exact (WithBot.sum_eq_bot_iff).mp hsum_bot
    obtain ⟨j, hj_mem, hj_bot⟩ := hsum_bot'
    have hj_nonneg : (0 : EReal) ≤ (w j : EReal) := EReal.coe_nonneg.mpr (stdSimplex.zero_le w j)
    have hj_term_ne_bot : w j * f (x j) ≠ ⊥ := by
      simpa using
        (EReal.mul_ne_bot (w j) (f (x j))).2
          ⟨Or.inl (by simp), Or.inr (h_ne_bot _), Or.inl (by simp), Or.inl hj_nonneg⟩
    exact hj_term_ne_bot hj_bot
  -- Isolate the offending top term and use that the remaining finite sum cannot be `⊥`.
  calc
    ∑ j, w j * f (x j) =
        Finset.sum (Finset.univ.erase i) (fun j ↦ w j * f (x j)) + w i * f (x i) := by
      simpa using
        (Finset.sum_erase_add Finset.univ (fun j ↦ w j * f (x j)) (Finset.mem_univ i)).symm
    _ = Finset.sum (Finset.univ.erase i) (fun j ↦ w j * f (x j)) + ⊤ := by rw [hi_top]
    _ = ⊤ := EReal.add_top_of_ne_bot htail_ne_bot

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 2.2: if every point outside `effective_domain f` has zero weight, then
the simplex weights on the effective-domain support still sum to `1`. -/
private theorem sum_weights_filter_effectiveDomain_eq_one {k : ℕ}
    (x : Fin k → E) (w : stdSimplex ℝ (Fin k))
    (hzero : ∀ i, ¬ f (x i) < ⊤ → w i = 0) :
    Finset.sum (Finset.univ.filter (fun i ↦ f (x i) < ⊤)) w = 1 := by
  have hcompl :
      Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) w = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact hzero i (Finset.mem_filter.mp hi).2
  -- Split the simplex sum into the effective-domain support and its zero-weight complement.
  calc
    Finset.sum (Finset.univ.filter (fun i ↦ f (x i) < ⊤)) w =
        Finset.sum (Finset.univ.filter (fun i ↦ f (x i) < ⊤)) w +
          Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) w := by
      rw [hcompl, add_zero]
    _ = Finset.sum Finset.univ w := by
      simpa using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i ↦ f (x i) < ⊤) w)
    _ = 1 := stdSimplex.sum_eq_one w

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 2.2: on `effective_domain f`, a weighted extended-real term is the
coercion of the corresponding weighted real `toReal` value. -/
private theorem erealWeightedTerm_eq_coe_mul_toReal_of_memEffectiveDomain
    (h_ne_bot : ∀ z, f z ≠ ⊥) {y : E} (hy : y ∈ effective_domain f) {t : ℝ} :
    t * f y = ((t * (f y).toReal : ℝ) : EReal) := by
  have hy_top : f y ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hy)
  -- On the effective domain, replace the `EReal` value by its real coercion and multiply in `ℝ`.
  calc
    t * f y = (t : EReal) * (((f y).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal hy_top (h_ne_bot y)]
    _ = ((t * (f y).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_mul]

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Proposition 2.2: on a finite effective-domain support, the weighted extended-real
sum is the coercion of the corresponding real sum of `toReal` values. -/
private theorem erealWeightedSum_eq_coe_sum_toReal_of_memEffectiveDomain {k : ℕ}
    (s : Finset (Fin k)) (x : Fin k → E) (a : Fin k → ℝ) (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hs : ∀ i ∈ s, x i ∈ effective_domain f) :
    Finset.sum s (fun i ↦ a i * f (x i)) =
      ((Finset.sum s (fun i ↦ a i * (f (x i)).toReal) : ℝ) : EReal) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    simp
  · intro i s hi ih hs_mem
    have hi_mem : x i ∈ effective_domain f := hs_mem i (by simp [hi])
    have hs_tail : ∀ j ∈ s, x j ∈ effective_domain f := by
      intro j hj
      exact hs_mem j (by simp [hj])
    -- Normalize the head term and then apply the inductive hypothesis on the tail.
    calc
      Finset.sum (insert i s) (fun j ↦ a j * f (x j)) =
          a i * f (x i) + Finset.sum s (fun j ↦ a j * f (x j)) := by
        simp [hi]
      _ = ((a i * (f (x i)).toReal : ℝ) : EReal) +
            ((Finset.sum s (fun j ↦ a j * (f (x j)).toReal) : ℝ) : EReal) := by
        rw [erealWeightedTerm_eq_coe_mul_toReal_of_memEffectiveDomain (f := f) h_ne_bot hi_mem,
          ih hs_tail]
      _ = ((a i * (f (x i)).toReal + Finset.sum s (fun j ↦ a j * (f (x j)).toReal) : ℝ) :
            EReal) := by
        rw [← EReal.coe_add]
      _ = ((Finset.sum (insert i s) (fun j ↦ a j * (f (x j)).toReal) : ℝ) : EReal) := by
        simp [hi]

-- Proof sketch: use the convexity of the real epigraph from `hf` and show that the convex
-- combination of the points `(x i, f (x i))` with weights `λ` again belongs to the epigraph. The
-- source convention for extended-real-valued functions excludes `-∞`, so the Lean statement keeps
-- the corresponding side condition `h_ne_bot`. The first coordinate is `∑ i, λ i • x i`, while
-- the second coordinate is `∑ i, λ i * f (x i)`, giving the desired inequality.
/-- Proposition 2.2: Jensen's inequality for a convex extended-real-valued function in the source
convention excluding `-∞`. If `λ : stdSimplex ℝ (Fin k)` is the textbook simplex vector `Δ_k`,
then `f (∑ i, λ i • x i) ≤ ∑ i, λ i * f (x i)`. -/
theorem convex_function_jensen_inequality {k : ℕ} (hf : is_convex_function f)
    (h_ne_bot : ∀ z, f z ≠ ⊥) (x : Fin k → E) (w : stdSimplex ℝ (Fin k)) :
    f (∑ i, w i • x i) ≤ ∑ i, w i * f (x i) := by
  classical
  by_cases hbad : ∃ i, x i ∉ effective_domain f ∧ w i ≠ 0
  · have htop : ∑ i, w i * f (x i) = ⊤ :=
      weightedValueSum_eq_top_of_exists_notMemEffectiveDomain (f := f) h_ne_bot x w hbad
    -- A positive weight outside the effective domain makes the right-hand side equal to `⊤`.
    simpa [htop] using (le_top : f (∑ i, w i • x i) ≤ ⊤)
  · let s : Finset (Fin k) := Finset.univ.filter (fun i ↦ f (x i) < ⊤)
    have hzero : ∀ i, x i ∉ effective_domain f → w i = 0 := by
      intro i hi
      by_contra hwi
      exact hbad ⟨i, hi, hwi⟩
    have hzero_lt : ∀ i, ¬ f (x i) < ⊤ → w i = 0 := by
      intro i hi
      exact hzero i (by simpa [mem_effective_domain] using hi)
    have hsum : Finset.sum s w = 1 :=
      sum_weights_filter_effectiveDomain_eq_one (f := f) x w hzero_lt
    letI := Module.addCommMonoidToAddCommGroup (R := ℝ) (M := E)
    have hconv :
        ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
      convexOn_toReal_of_is_convex_function hf (fun z _ ↦ h_ne_bot z)
    have hnonneg : ∀ i ∈ s, 0 ≤ w i := by
      intro i _hi
      exact stdSimplex.zero_le w i
    have hmem : ∀ i ∈ s, x i ∈ effective_domain f := by
      intro i hi
      simpa [s, mem_effective_domain] using (Finset.mem_filter.mp hi).2
    have hbary_mem : Finset.sum s (fun i ↦ w i • x i) ∈ effective_domain f :=
      by
        simpa using
          (Convex.sum_mem (s := effective_domain f) (t := s) (w := w) (z := x) hconv.1
            hnonneg hsum hmem)
    have hJensen :
        (f (Finset.sum s (fun i ↦ w i • x i))).toReal ≤
          Finset.sum s (fun i ↦ w i * (f (x i)).toReal) := by
      -- Jensen now applies on the filtered support where every point lies in the effective domain.
      simpa [smul_eq_mul] using hconv.map_sum_le hnonneg hsum hmem
    have hpoint_compl :
        Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) (fun i ↦ w i • x i) = 0 := by
      exact Finset.sum_eq_zero fun i hi ↦ by
        rw [hzero_lt i (Finset.mem_filter.mp hi).2, zero_smul]
    have hpoint_top :
        Finset.sum (Finset.univ.filter (fun i ↦ f (x i) = ⊤)) (fun i ↦ w i • x i) = 0 := by
      simpa [not_lt] using hpoint_compl
    have hpoint :
        ∑ i, w i • x i = Finset.sum s (fun i ↦ w i • x i) := by
      -- The indices outside the effective domain carry zero weight in the good branch.
      calc
        ∑ i, w i • x i =
            Finset.sum s (fun i ↦ w i • x i) +
              Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) (fun i ↦ w i • x i) := by
          simpa [s] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun i ↦ f (x i) < ⊤) (fun i ↦ w i • x i)).symm
        _ = Finset.sum s (fun i ↦ w i • x i) := by simpa [hpoint_top, not_lt]
    have hvalue_compl :
        Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) (fun i ↦ w i * f (x i)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simpa [hzero_lt i (Finset.mem_filter.mp hi).2]
    have hvalue_top :
        Finset.sum (Finset.univ.filter (fun i ↦ f (x i) = ⊤)) (fun i ↦ w i * f (x i)) = 0 := by
      simpa [not_lt] using hvalue_compl
    have hvalue :
        ∑ i, w i * f (x i) = Finset.sum s (fun i ↦ w i * f (x i)) := by
      -- The weighted-value sum has the same support reduction as the point sum.
      calc
        ∑ i, w i * f (x i) =
            Finset.sum s (fun i ↦ w i * f (x i)) +
              Finset.sum (Finset.univ.filter (fun i ↦ ¬ f (x i) < ⊤)) (fun i ↦ w i * f (x i)) := by
          simpa [s] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun i ↦ f (x i) < ⊤) (fun i ↦ w i * f (x i))).symm
        _ = Finset.sum s (fun i ↦ w i * f (x i)) := by simpa [hvalue_top, not_lt]
    have hleft :
        ((f (Finset.sum s (fun i ↦ w i • x i))).toReal : EReal) =
          f (Finset.sum s (fun i ↦ w i • x i)) := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hbary_mem))
        (h_ne_bot (Finset.sum s (fun i ↦ w i • x i)))
    have hright :
        Finset.sum s (fun i ↦ w i * f (x i)) =
          ((Finset.sum s (fun i ↦ w i * (f (x i)).toReal) : ℝ) : EReal) :=
      erealWeightedSum_eq_coe_sum_toReal_of_memEffectiveDomain (f := f) s x w h_ne_bot hmem
    have hJensenEReal :
        f (Finset.sum s (fun i ↦ w i • x i)) ≤ Finset.sum s (fun i ↦ w i * f (x i)) := by
      have hcoe :
          ((f (Finset.sum s (fun i ↦ w i • x i))).toReal : EReal) ≤
            ((Finset.sum s (fun i ↦ w i * (f (x i)).toReal) : ℝ) : EReal) := by
        exact_mod_cast hJensen
      -- Convert the real Jensen inequality back to the extended-real statement on the same support.
      calc
        f (Finset.sum s (fun i ↦ w i • x i)) =
            ((f (Finset.sum s (fun i ↦ w i • x i))).toReal : EReal) := by
          symm
          exact hleft
        _ ≤ ((Finset.sum s (fun i ↦ w i * (f (x i)).toReal) : ℝ) : EReal) := hcoe
        _ = Finset.sum s (fun i ↦ w i * f (x i)) := hright.symm
    -- Rewrite the filtered-support inequality back to the original simplex sums.
    calc
      f (∑ i, w i • x i) = f (Finset.sum s (fun i ↦ w i • x i)) := by rw [hpoint]
      _ ≤ Finset.sum s (fun i ↦ w i * f (x i)) := hJensenEReal
      _ = ∑ i, w i * f (x i) := by rw [← hvalue]

end
