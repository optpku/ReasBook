/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_55
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u}

/- Proposition 10.56 is `source-facing`: it fixes the standing assumptions for the S-FISTA model
`H(x) = f(x) + h(x) + g(x)`.

Domain sampling in the surrounding chapter identifies the relevant owners already present in the
workspace:
- `Function.toEReal` from Definition 9.2 for the canonical coercion from the real-valued terms
  `f` and `h` into the extended-real codomain;
- `composite_model_objective` from Definition 10.2, used twice as in Definition 10.55, for the
  underlying three-term objective;
- `unconstrained_problem_solutions` from Definition 8.2 for the optimizer set;
- `is_l_smooth_on`, `is_smoothable`, `IsProperExtendedRealFunction`, `LowerSemicontinuous`,
  `is_convex_function`, and `IsGLB` for the analytic clauses.

Primitive data here are the textbook clauses themselves. The proposition should expose the
regularity of `g` through the usual atomic instances rather than through a one-off conjunction
package. For a chosen smoothing `h_μ`, the canonical chapter owner of the smoothed subproblem is
`IsFastProximalGradientProblem`, so this file should also expose that bridge directly.
-/

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Proposition 10.56: the S-FISTA assumptions are organized into five atomic clauses.
Clause (A): `f` is convex and globally `L_f`-smooth. Clause (B): `h` is `(α, β)`-smoothable.
Clause (C): `g : E → (-∞, ∞]` is proper, closed, convex. Clause (D): each real sublevel set of
`H(x) = f(x) + h(x) + g(x)` is bounded. Clause (E): `XStar = X^*` is the nonempty minimizer set
of `H`, with optimal value `HOpt = H_opt`. -/
class IsSFISTAProblem
    (f h : E → ℝ) (g : E → EReal) (XStar : outParam (Set E)) (HOpt : outParam ℝ)
    (Lf : NNReal) (α β : PosReal) : Prop where
  f_convex : ConvexOn ℝ Set.univ f
  f_smooth : is_l_smooth_on f Set.univ Lf
  h_smoothable : is_smoothable h α β
  g_proper : IsProperExtendedRealFunction g
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  bounded_real_sublevelSets (a : ℝ) :
    Bornology.IsBounded {x | H[f.toEReal, h.toEReal, g] x ≤ (a : EReal)}
  optimal_set_eq : XStar = unconstrained_problem_solutions H[f.toEReal, h.toEReal, g]
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB : IsGLB (Set.range H[f.toEReal, h.toEReal, g]) (HOpt : EReal)

/-- The regularizer in an S-FISTA problem is proper. -/
instance instIsProperExtendedRealFunctionRightOfIsSFISTAProblem
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    IsProperExtendedRealFunction g :=
  hproblem.g_proper

/-- The regularizer in an S-FISTA problem is lower semicontinuous. -/
instance instLowerSemicontinuousRightOfIsSFISTAProblem
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    LowerSemicontinuous g :=
  hproblem.g_closed

/-- An S-FISTA problem yields a `Fact` witness for lower semicontinuity of the regularizer. -/
instance instFactLowerSemicontinuousRightOfIsSFISTAProblem
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    Fact (LowerSemicontinuous g) :=
  ⟨hproblem.g_closed⟩

/-- The regularizer in an S-FISTA problem is convex. -/
instance instIsConvexFunctionRightOfIsSFISTAProblem
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    is_convex_function g :=
  hproblem.g_convex

/-- An S-FISTA problem yields a `Fact` witness for convexity of the regularizer. -/
instance instFactIsConvexFunctionRightOfIsSFISTAProblem
    {f h : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
    {Lf : NNReal} {α β : PosReal}
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    Fact (is_convex_function g) :=
  ⟨hproblem.g_convex⟩

namespace IsSFISTAProblem

section

variable [ProperSpace E]
variable {f h hμ : E → ℝ} {g : E → EReal} {XStar : Set E} {HOpt : ℝ}
variable {Lf : NNReal} {α β μ : PosReal}

/-- Helper for Proposition 10.56: the three-term smoothed objective is exactly the Chapter 10
fast proximal-gradient objective for the real-valued smooth term `x ↦ f x + hμ x`. -/
theorem smoothed_objective_eq_fast_prox_objective :
    H[f.toEReal, hμ.toEReal, g] =
      composite_model_objective (Function.toEReal (fun x ↦ f x + hμ x)) g := by
  -- Unfold both Chapter 10 wrappers to the same nested pointwise sum.
  ext x
  rfl

/-- Helper for Proposition 10.56: global smoothness on `Set.univ` is stable under adding smooth
real-valued terms, with Lipschitz constants adding as expected. -/
theorem is_l_smooth_on_add
    {f₁ f₂ : E → ℝ} {L₁ L₂ : NNReal}
    (hf₁ : is_l_smooth_on f₁ Set.univ L₁)
    (hf₂ : is_l_smooth_on f₂ Set.univ L₂) :
    is_l_smooth_on (fun x ↦ f₁ x + f₂ x) Set.univ (L₁ + L₂) := by
  rw [is_l_smooth_on_iff] at hf₁ hf₂ ⊢
  refine ⟨?_, ?_⟩
  · -- Differentiability is pointwise stable under addition.
    intro x hx
    exact (hf₁.1 x hx).add (hf₂.1 x hx)
  · -- The derivative difference splits into two pieces, so the norms add by the triangle inequality.
    intro x hx y hy
    have hf₁x := hf₁.1 x hx
    have hf₂x := hf₂.1 x hx
    have hf₁y := hf₁.1 y hy
    have hf₂y := hf₂.1 y hy
    have hxy₁ := hf₁.2 x hx y hy
    have hxy₂ := hf₂.2 x hx y hy
    have hfderiv_x :
        fderiv ℝ (fun z ↦ f₁ z + f₂ z) x = fderiv ℝ f₁ x + fderiv ℝ f₂ x := by
      simpa using fderiv_add hf₁x hf₂x
    have hfderiv_y :
        fderiv ℝ (fun z ↦ f₁ z + f₂ z) y = fderiv ℝ f₁ y + fderiv ℝ f₂ y := by
      simpa using fderiv_add hf₁y hf₂y
    have hnorm :
        ‖fderiv ℝ (fun z ↦ f₁ z + f₂ z) x - fderiv ℝ (fun z ↦ f₁ z + f₂ z) y‖ ≤
          ‖fderiv ℝ f₁ x - fderiv ℝ f₁ y‖ + ‖fderiv ℝ f₂ x - fderiv ℝ f₂ y‖ := by
      rw [hfderiv_x, hfderiv_y]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        norm_add_le (fderiv ℝ f₁ x - fderiv ℝ f₁ y) (fderiv ℝ f₂ x - fderiv ℝ f₂ y)
    calc
      ‖fderiv ℝ (fun z ↦ f₁ z + f₂ z) x - fderiv ℝ (fun z ↦ f₁ z + f₂ z) y‖
          ≤ ‖fderiv ℝ f₁ x - fderiv ℝ f₁ y‖ + ‖fderiv ℝ f₂ x - fderiv ℝ f₂ y‖ := hnorm
      _ ≤ (L₁ : ℝ) * ‖x - y‖ + (L₂ : ℝ) * ‖x - y‖ := add_le_add hxy₁ hxy₂
      _ = ((L₁ + L₂ : NNReal) : ℝ) * ‖x - y‖ := by
        simp [add_mul]

/-- Helper for Proposition 10.56: the smoothed objective stays proper because the real-valued
terms are finite everywhere and the regularizer `g` is proper. -/
theorem smoothed_objective_is_proper
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β) :
    IsProperExtendedRealFunction H[f.toEReal, hμ.toEReal, g] := by
  refine ⟨?_, ?_⟩
  · -- No point can have value `-∞` because only the `g`-term could, and properness excludes that.
    intro x
    simp [Function.toEReal, add_assoc, hproblem.g_proper.ne_bot x]
  · -- Any finite point of `g` is also finite for the full smoothed objective.
    rcases hproblem.g_proper.effective_domain_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    refine mem_effective_domain.mpr ?_
    have hsum_top : (f x : EReal) + hμ x ≠ ⊤ := by
      exact (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne
    simpa [Function.toEReal, add_assoc] using
      EReal.add_lt_top hsum_top (mem_effective_domain.mp hx).ne

/-- Helper for Proposition 10.56: coercing the finite smoothed objective value back to `ℝ` and
then to `EReal` recovers the original value. -/
theorem smoothed_objective_coe_toReal_of_mem_effective_domain
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    {x : E} (hx : x ∈ effective_domain H[f.toEReal, hμ.toEReal, g]) :
    (((H[f.toEReal, hμ.toEReal, g] x).toReal : ℝ) : EReal) =
      H[f.toEReal, hμ.toEReal, g] x := by
  -- Effective-domain membership removes `⊤`, and properness removes `⊥`.
  have hne_bot : H[f.toEReal, hμ.toEReal, g] x ≠ ⊥ :=
    (smoothed_objective_is_proper (f := f) (h := h) (hμ := hμ) (g := g) hproblem).ne_bot x
  exact EReal.coe_toReal (mem_effective_domain.mp hx).ne hne_bot

/-- Helper for Proposition 10.56: the smoothed objective is lower semicontinuous because its
real-valued smooth part is continuous and `g` is lower semicontinuous. -/
theorem smoothed_objective_lower_semicontinuous
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ) :
    LowerSemicontinuous H[f.toEReal, hμ.toEReal, g] := by
  -- The real-valued smooth part is continuous because both summands are globally smooth.
  have hcont : Continuous (fun x ↦ f x + hμ x) := by
    refine continuous_iff_continuousAt.2 ?_
    intro x
    exact (hproblem.f_smooth.1 x (by simp)).continuousAt.add
      ((hhμ.smooth.1 x (by simp)).continuousAt)
  have hsmooth_lsc : LowerSemicontinuous (Function.toEReal (fun x ↦ f x + hμ x)) :=
    Function.toEReal_lowerSemicontinuous_of_continuous hcont
  have hsum_lsc :
      LowerSemicontinuous
        (composite_model_objective (Function.toEReal (fun x ↦ f x + hμ x)) g) := by
    -- Addition is continuous at every relevant pair because the real-valued lifted term is finite.
    refine hsmooth_lsc.add' hproblem.g_closed ?_
    intro x
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))
  simpa [smoothed_objective_eq_fast_prox_objective (f := f) (hμ := hμ) (g := g)] using hsum_lsc

/-- Helper for Proposition 10.56: every real sublevel set of the smoothed objective is bounded,
because smoothing shifts the original objective by at most `β μ`. -/
theorem smoothed_objective_bounded_real_sublevel_sets
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ) :
    ∀ a : ℝ, Bornology.IsBounded {x | H[f.toEReal, hμ.toEReal, g] x ≤ (a : EReal)} := by
  intro a
  refine Bornology.IsBounded.subset
    (hproblem.bounded_real_sublevelSets (a + (β : ℝ) * (μ : ℝ))) ?_
  intro x hx
  have hcompare :
      H[f.toEReal, h.toEReal, g] x ≤
        H[f.toEReal, hμ.toEReal, g] x + (((β : ℝ) * (μ : ℝ) : ℝ) : EReal) := by
    -- Only the `h`/`hμ` slot changes, and `hhμ.upper_le` controls that change uniformly.
    have hupper :
        ((h x : ℝ) : EReal) ≤ (((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : ℝ) : EReal) := by
      exact_mod_cast hhμ.upper_le x
    calc
      H[f.toEReal, h.toEReal, g] x
          = ((f x : EReal) + h x) + g x := by
            simp [Function.toEReal, add_assoc]
      _ ≤ ((f x : EReal) + (((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal))) + g x := by
            have hsum_with_g :
                ((h x : EReal) + g x) ≤
                  ((((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal)) + g x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hupper (g x)
            have htotal :
                (((h x : EReal) + g x) + f x) ≤
                  ((((hμ x + (β : ℝ) * (μ : ℝ) : ℝ) : EReal) + g x) + f x) := by
              exact add_le_add_left hsum_with_g (f x : EReal)
            simpa [add_assoc, add_left_comm, add_comm] using htotal
      _ = H[f.toEReal, hμ.toEReal, g] x + (((β : ℝ) * (μ : ℝ) : ℝ) : EReal) := by
            simp [Function.toEReal, add_left_comm, add_comm]
  calc
    H[f.toEReal, h.toEReal, g] x
        ≤ H[f.toEReal, hμ.toEReal, g] x + (((β : ℝ) * (μ : ℝ) : ℝ) : EReal) := hcompare
    _ ≤ (a : EReal) + (((β : ℝ) * (μ : ℝ) : ℝ) : EReal) := by
          simpa [add_comm] using
            add_le_add_left hx ((((β : ℝ) * (μ : ℝ) : ℝ) : EReal))
    _ = ((a + (β : ℝ) * (μ : ℝ) : ℝ) : EReal) := by
          simp

omit [ProperSpace E] in
theorem bounded_real_sublevel_radius
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (a : ℝ) :
    ∃ R : PosReal, ∀ ⦃x : E⦄,
      H[f.toEReal, h.toEReal, g] x ≤ (a : EReal) → ‖x‖ ≤ (R : ℝ) := by
  rcases (hproblem.bounded_real_sublevelSets a).subset_closedBall_lt 0 (0 : E) with
    ⟨R, hR, hball⟩
  refine ⟨⟨R, hR⟩, ?_⟩
  intro x hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hball hx

/-- Bridge/view layer: for a chosen smoothing `h_μ`, Proposition 10.56 supplies the full Chapter
10 fast proximal-gradient assumptions for the smoothed objective `x ↦ f x + h_μ x`, with the
smoothed optimal value produced as an auxiliary output rather than a caller-supplied input. -/
theorem toIsFastProximalGradientProblem
    (hproblem : IsSFISTAProblem f h g XStar HOpt Lf α β)
    (hhμ : IsSmoothApproximation h hμ α β μ) :
    ∃ HμOpt : ℝ,
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ) := by
  let Fμ : E → EReal := H[f.toEReal, hμ.toEReal, g]
  -- The source-proof route is to show the smoothed objective satisfies the Weierstrass hypotheses.
  have hFμ_proper : IsProperExtendedRealFunction Fμ := by
    simpa [Fμ] using smoothed_objective_is_proper
      (f := f) (h := h) (hμ := hμ) (g := g) hproblem
  have hFμ_lsc : LowerSemicontinuous Fμ := by
    simpa [Fμ] using smoothed_objective_lower_semicontinuous
      (f := f) (h := h) (hμ := hμ) (g := g) hproblem hhμ
  have hFμ_bounded : ∀ a : ℝ, Bornology.IsBounded {x | Fμ x ≤ (a : EReal)} := by
    simpa [Fμ] using smoothed_objective_bounded_real_sublevel_sets
      (f := f) (h := h) (hμ := hμ) (g := g) hproblem hhμ
  -- A global minimizer of the smoothed objective exists by bounded real sublevel sets.
  obtain ⟨x, hx, hxmin⟩ :=
    exists_isMinOn_univ_of_bounded_real_sublevelSets Fμ hFμ_proper hFμ_lsc hFμ_bounded
  let HμOpt : ℝ := (Fμ x).toReal
  have hHμOpt_coe : ((HμOpt : ℝ) : EReal) = Fμ x := by
    -- The minimizer lies in the effective domain, so `toReal` is exact at its value.
    simpa [HμOpt, Fμ] using smoothed_objective_coe_toReal_of_mem_effective_domain
      (f := f) (h := h) (hμ := hμ) (g := g) hproblem hx
  have h_f_convex : ConvexOn ℝ Set.univ (fun x ↦ f x + hμ x) := by
    -- Convexity of the smoothed smooth term comes from convexity of `f` and of the approximation.
    exact hproblem.f_convex.add hhμ.convex
  have h_f_smooth :
      is_l_smooth_on (fun x ↦ f x + hμ x) Set.univ
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ) := by
    -- The global smoothness constants of `f` and `hμ` add.
    simpa [PosReal.toNNReal] using is_l_smooth_on_add
      (f₁ := f) (f₂ := hμ) (L₁ := Lf) (L₂ := PosReal.toNNReal α / PosReal.toNNReal μ)
      hproblem.f_smooth hhμ.smooth
  have h_optimal_set_eq :
      unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g] =
        unconstrained_problem_solutions
          (composite_model_objective (Function.toEReal (fun x ↦ f x + hμ x)) g) := by
    -- The optimizer set is transported through the normalization of the objective.
    simp [smoothed_objective_eq_fast_prox_objective (f := f) (hμ := hμ) (g := g)]
  have h_optimal_nonempty :
      (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g]).Nonempty := by
    -- The minimizer returned by Weierstrass belongs to the canonical unconstrained solution set.
    exact ⟨x, mem_unconstrained_problem_solutions_iff.mpr hxmin⟩
  have h_optimal_value_isGLB :
      IsGLB
        (Set.range
          (composite_model_objective (Function.toEReal (fun x ↦ f x + hμ x)) g))
        (HμOpt : EReal) := by
    -- Global minimality identifies the optimum as the greatest lower bound of the range.
    have hglb_smoothed : IsGLB (Set.range Fμ) (HμOpt : EReal) := by
      simpa [hHμOpt_coe] using hxmin.isGLB (by simp : x ∈ (Set.univ : Set E))
    simpa [Fμ, smoothed_objective_eq_fast_prox_objective (f := f) (hμ := hμ) (g := g)] using
      hglb_smoothed
  have h_fast :
      IsFastProximalGradientProblem (fun x ↦ f x + hμ x) g
        (unconstrained_problem_solutions H[f.toEReal, hμ.toEReal, g])
        HμOpt
        (Lf + PosReal.toNNReal α / PosReal.toNNReal μ) := by
    -- Package the smoothed-objective data into the Chapter 10 fast proximal-gradient owner.
    exact
      { g_proper := hproblem.g_proper
        g_closed := hproblem.g_closed
        g_convex := hproblem.g_convex
        f_convex := h_f_convex
        f_smooth := h_f_smooth
        optimal_set_eq := h_optimal_set_eq
        optimal_set_nonempty := h_optimal_nonempty
        optimal_value_isGLB := h_optimal_value_isGLB }
  exact ⟨HμOpt, h_fast⟩

end

end IsSFISTAProblem

end
