/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NewtonDecrement SelfConcordantAuxiliaryFunction
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.16 lies in the finite-dimensional Chapter 5 self-concordant minimization domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, specialized here to the whole-space owner
  `IsSelfConcordantOnWith Set.univ Mf f`;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, likewise specialized to
  `Set.univ`;
* `IsMinOn` and `isMinOn_univ_iff` in mathlib, the canonical owner and textbook bridge for
  whole-space minimizers;
* `isMinOn_iff_eq_sInf_range` from `Chap03/Definition_3_33`, the project owner bridge between
  whole-space attainment and the infimum of `Set.range f`.

Source/core/bridge triage:
* source-facing: bounded-below existence and uniqueness of a global minimizer of `f`;
* core/canonical: `IsSelfConcordantOnWith Set.univ Mf f`,
  `HasPositiveDefiniteHessianOn Set.univ f`, and `IsMinOn f Set.univ x`;
* bridge/view: the attained-infimum identity `f xStar = sInf (Set.range f)`.

Primitive data:
* the ambient objective `f : E → ℝ`;
* self-concordance of `f` on `Set.univ`;
* positive definiteness of its Hessian on `Set.univ`;
* lower boundedness of the range `Set.range f`.

Derived API:
* existence of a global minimizer of `f`;
* uniqueness of that minimizer.

The previous revision incorrectly strengthened the textbook finite-dimensional whole-space
attainment theorem to an arbitrary complete real inner-product space, where bounded below need not
imply attainment. The public owner is restored here to the source-faithful whole-space
finite-dimensional formulation. -/

namespace IsSelfConcordantOnWith

section

variable {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith Set.univ Mf f] [HasPositiveDefiniteHessianOn Set.univ f]

/-- Helper for Theorem 5.1.16: this is the damped Newton orbit on the whole space started from
the origin. -/
def damped_newton_iterate_from_zero
    (f : E → ℝ) (Mg : NNReal) [IsSelfConcordantOnWith Set.univ Mg f]
    [HasPositiveDefiniteHessianOn Set.univ f] : ℕ → E
  | 0 => 0
  | n + 1 =>
      selfConcordantNewtonNextPoint f Mg .damped
        (damped_newton_iterate_from_zero f Mg n)
        (Set.mem_univ _)
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem
          (dom := Set.univ) (f := f) (Set.mem_univ _))

/-- Helper for Theorem 5.1.16: on `Set.univ`, the determinant-based and positive-definite-domain
Newton decrement owners agree. -/
lemma newtonDecrement_det_eq_posDef_univ
    {Mg : NNReal} [IsSelfConcordantOnWith Set.univ Mg f] (x : E) :
    NewtonDecrement.ofDetNeZero Mg f (Set.mem_univ x)
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem
        (dom := Set.univ) (f := f) (Set.mem_univ x)) =
      λ[f; x | Set.mem_univ x] := by
  -- Both Chapter 5 owners expand to the same inverse-Hessian pairing formula.
  calc
    NewtonDecrement.ofDetNeZero Mg f (Set.mem_univ x)
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem
          (dom := Set.univ) (f := f) (Set.mem_univ x)) =
      Real.sqrt (inner ℝ (gradient f x) ((hessian f x).inverse (gradient f x))) := by
        simpa using
          (NewtonDecrement.ofDetNeZero_def Mg f
            (dom := Set.univ) (x := x) (hx := Set.mem_univ x)
            (hH := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem
              (dom := Set.univ) (f := f) (Set.mem_univ x)))
    _ = λ[f; x | Set.mem_univ x] := by
      symm
      simpa using
        (NewtonDecrement.ofPosDefMem_def f x (dom := Set.univ) (hx := Set.mem_univ x))

/-- Helper for Theorem 5.1.16: once the canonical `ω` argument is at least `1`, the textbook
lower bound from Lemma 5.1.5 yields the uniform estimate `ω ≥ 3 / 10`. -/
lemma selfConcordantOmega_ge_three_tenths_of_one_le
    {tω : Set.Ioi (-1 : ℝ)} (htω : 1 ≤ (tω : ℝ)) :
    (3 / 10 : ℝ) ≤ ω tω := by
  -- Specializing Lemma 5.1.5 at the scalar value `t = tω` exposes the rational lower bound.
  have hbounds :=
    selfConcordantOmega_bounds (t := (tω : ℝ)) (by linarith [htω])
  rcases hbounds with ⟨hlower, -⟩
  have hdenom_pos : 0 < 2 * (1 + (2 / 3 : ℝ) * (tω : ℝ)) := by positivity
  have hratio :
      (3 / 10 : ℝ) ≤
        (tω : ℝ) ^ 2 / (2 * (1 + (2 / 3 : ℝ) * (tω : ℝ))) := by
    refine (le_div_iff₀ hdenom_pos).2 ?_
    nlinarith [htω]
  exact hratio.trans (by simpa using hlower)

/-- Helper for Theorem 5.1.16: if the whole-space objective is bounded below, then some point has
Newton decrement smaller than `1 / M_g`. -/
lemma exists_point_newtonDecrement_lt_inv_of_bddBelow
    {Mg : NNReal} [IsSelfConcordantOnWith Set.univ Mg f]
    (hMg : 0 < (Mg : ℝ)) (hbelow : BddBelow (Set.range f)) :
    ∃ x : E, λ[f; x | Set.mem_univ x] < 1 / (Mg : ℝ) := by
  by_contra hnot
  have hlarge : ∀ x : E, 1 / (Mg : ℝ) ≤ λ[f; x | Set.mem_univ x] := by
    intro x
    exact le_of_not_gt (by
      intro hx
      exact hnot ⟨x, hx⟩)
  let xSeq : ℕ → E := damped_newton_iterate_from_zero f Mg
  let c : ℝ := (1 / (Mg : ℝ) ^ (2 : ℕ)) * (3 / 10 : ℝ)
  have hc_pos : 0 < c := by
    -- The fixed decrease amount is positive because `M_g > 0`.
    dsimp [c]
    positivity
  have hstep :
      ∀ n : ℕ, f (xSeq (n + 1)) ≤ f (xSeq n) - c := by
    intro n
    let xn := xSeq n
    let hxn : xn ∈ Set.univ := Set.mem_univ xn
    let hdet : (hessian f xn).det ≠ 0 :=
      HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem
        (dom := Set.univ) (f := f) hxn
    let ωarg := NewtonDecrement.omegaArgOfDetNeZero Mg f hxn hdet
    have hlarge_xn : 1 / (Mg : ℝ) ≤ λ[f; xn | hxn] := by
      simpa [xn, hxn] using hlarge xn
    have hone_le : 1 ≤ (Mg : ℝ) * λ[f; xn | hxn] := by
      have hmul :
          (Mg : ℝ) * (1 / (Mg : ℝ)) ≤ (Mg : ℝ) * λ[f; xn | hxn] := by
        exact mul_le_mul_of_nonneg_left hlarge_xn hMg.le
      have hunit : (Mg : ℝ) * (1 / (Mg : ℝ)) = 1 := by
        field_simp [hMg.ne']
      rw [hunit] at hmul
      exact hmul
    have hωarg_ge : 1 ≤ (ωarg : ℝ) := by
      -- The large-decrement hypothesis forces the canonical `ω` argument to lie beyond `1`.
      simpa [ωarg, xn, hxn, hdet, newtonDecrement_det_eq_posDef_univ (f := f) (Mg := Mg) xn] using
        hone_le
    have hωlower : (3 / 10 : ℝ) ≤ ω ωarg :=
      selfConcordantOmega_ge_three_tenths_of_one_le hωarg_ge
    have hdecrease :
        f (xSeq (n + 1)) ≤
          f (xSeq n) - ((1 / (Mg : ℝ) ^ (2 : ℕ)) * ω ωarg) := by
      -- Theorem 5.1.15 gives the one-step value drop for the damped Newton update.
      have hMg0 : Mg ≠ 0 := by
        exact_mod_cast hMg.ne'
      have hdecrease_raw :
          f (xSeq (n + 1)) ≤
            f (xSeq n) -
              (if Mg = 0 then
                ndec(f, xn, Mg, hxn, hdet) ^ (2 : ℕ) / 2
              else
                (1 / (Mg : ℝ) ^ (2 : ℕ)) * ω ωarg) := by
        simpa [xSeq, xn, hxn, hdet, ωarg, damped_newton_iterate_from_zero] using
          (selfConcordant_dampedNewtonStep_value_decrease
            (Mf := Mg) (f := f) (x := xn) hxn hdet)
      simpa [hMg0] using hdecrease_raw
    have hscaled :
        c ≤ (1 / (Mg : ℝ) ^ (2 : ℕ)) * ω ωarg := by
      dsimp [c]
      exact mul_le_mul_of_nonneg_left hωlower (by positivity)
    linarith
  have hvalue_upper :
      ∀ n : ℕ, f (xSeq n) ≤ f 0 - (n : ℝ) * c := by
    intro n
    induction n with
    | zero =>
        -- At time `0`, the orbit is the origin by definition.
        simp [xSeq, damped_newton_iterate_from_zero, c]
    | succ n ih =>
        have hstep_n := hstep n
        have hsucc : (((n + 1 : ℕ) : ℝ) * c) = (n : ℝ) * c + c := by
          norm_num [Nat.cast_add, add_mul]
        linarith
  rcases hbelow with ⟨m, hm⟩
  have hm_seq : ∀ n : ℕ, m ≤ f (xSeq n) := by
    intro n
    exact hm ⟨xSeq n, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((f 0 - m) / c)
  have hmul : f 0 - m < (n : ℝ) * c := by
    have hmul_raw : ((f 0 - m) / c) * c < (n : ℝ) * c := by
      exact mul_lt_mul_of_pos_right hn hc_pos
    simpa [hc_pos.ne'] using hmul_raw
  have hupper_lt : f (xSeq n) < m := by
    linarith [hvalue_upper n, hmul]
  exact (lt_irrefl m) (lt_of_le_of_lt (hm_seq n) hupper_lt)

/-- Helper for Theorem 5.1.16: a point with Newton decrement below `1 / M_g` yields the unique
whole-space minimizer by Theorem 5.1.13. -/
lemma existsUnique_isMinOn_univ_of_newtonDecrement_lt_inv
    {Mg : NNReal} [IsSelfConcordantOnWith Set.univ Mg f]
    {x : E} (hx : λ[f; x | Set.mem_univ x] < 1 / (Mg : ℝ)) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  -- Theorem 5.1.13 already produces a unique minimizer on the `Set.univ` subtype.
  rcases existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
      (Mf := Mg) (f := f) (dom := Set.univ) (x := x) (Set.mem_univ x) hx with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar.1, hxStar.1, ?_⟩
  intro y hy
  have hy_value : f y = f xStar := by
    have hy_le : f y ≤ f xStar := (isMinOn_univ_iff.mp hy) xStar
    have hxStar_le : f xStar ≤ f y := (isMinOn_univ_iff.mp hxStar.1) y
    exact le_antisymm hy_le hxStar_le
  have hy_bound :
      f x - f y ≤
        (1 / (Mg : ℝ) ^ (2 : ℕ)) *
          ω_* (NewtonDecrement.omegaStarArgOfPosDefMem Mg f x (Set.mem_univ x) hx) := by
    simpa [hy_value] using hxStar.2
  have hy_sub :
      ((⟨y, Set.mem_univ y⟩ : Set.univ) : E) = y := rfl
  have hy_eq_sub : (⟨y, Set.mem_univ y⟩ : Set.univ) = xStar := by
    apply huniq
    simpa [hy_sub] using And.intro hy hy_bound
  exact congrArg Subtype.val hy_eq_sub

-- Proof sketch: boundedness below is expressed by `BddBelow (Set.range f)`, the canonical
-- whole-space image owner. Positive-definite Hessian on `Set.univ` supplies the strict convexity
-- needed for uniqueness once existence is obtained.
/-- Theorem 5.1.16: on a finite-dimensional real inner-product space, if a self-concordant
objective on the whole space has positive-definite Hessian everywhere and is bounded below, then
it attains a unique global minimum. -/
theorem existsUnique_isMinOn_of_bddBelow
    {M0 : NNReal} [IsSelfConcordantOnWith Set.univ M0 f]
    [HasPositiveDefiniteHessianOn Set.univ f]
    (hbelow : BddBelow (Set.range f)) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  -- Route correction: make the implicit self-concordance parameter explicit in the local header
  -- so the enlarged parameter `Mg = M0 + 1` is available inside the theorem body.
  let Mg : NNReal := M0 + 1
  have hMg_le : M0 ≤ Mg := by
    dsimp [Mg]
    exact le_add_of_nonneg_right (by positivity : 0 ≤ (1 : NNReal))
  have hMg_pos : 0 < (Mg : ℝ) := by
    dsimp [Mg]
    positivity
  have hself_Mg : IsSelfConcordantOnWith Set.univ Mg f :=
    IsSelfConcordantOnWith.of_le
      (dom := Set.univ) (f := f) (h := inferInstance) hMg_le
  letI : IsSelfConcordantOnWith Set.univ Mg f := hself_Mg
  -- First find a point with small Newton decrement for the enlarged self-concordance constant.
  rcases exists_point_newtonDecrement_lt_inv_of_bddBelow
      (f := f) (Mg := Mg) hMg_pos hbelow with ⟨x, hx⟩
  -- Then Theorem 5.1.13 upgrades that point to the unique whole-space minimizer.
  exact existsUnique_isMinOn_univ_of_newtonDecrement_lt_inv (f := f) (Mg := Mg) hx

end

end IsSelfConcordantOnWith

end
