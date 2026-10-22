/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_11
import FirstOrderMethodsOptimization_Beck_2017.Chap05.ConjugateFunctionStrongDual
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ω : E → EReal} {C : Set E} {σ : ℝ} {xk xNext gradf : E} {t : ℝ}

/-
Text 9.4 is `source-facing` in the Chapter 9 mirror-descent API. Domain sampling in the relevant
convex-analysis layer points to these existing owners:
- the Definition 9.2 Bregman-potential owner `IsBregmanPotentialOn ω C σ`;
- the Definition 9.2 Bregman-distance formula for the step objective;
- Chapter 3's owner `subdifferential` / `subdifferential_domain` for the constrained optimality
  condition;
- Chapter 4's Fenchel owner `conjugate_function` together with the conjugate-side bridge used to
  pass from constrained subgradient membership to the gradient of the conjugate.

The right abstraction layer is therefore:
- `source-facing`: the canonical Chapter 9 owner `mirror_descent_update_objective` for the mirror
  step over `C`, together with the textbook conjugate conclusion
  `x⁺ = ∇ ω̃∗(∇ω(xᵏ) - t g_f)`;
- `core/canonical`: the constrained potential `ω̃ = ω + δ_ C`;
- `bridge/view`: the Bregman-distance rewrite of the update objective, together with the
  intermediate constrained-subgradient and conjugate-subdifferential formulations.

The primitive data are the Definition 9.2 owner `IsBregmanPotentialOn ω C σ` and the current-point
hypothesis `xk ∈ C ∩ dom(∂ ω)`. The constrained potential and conjugate-side formulations are
derived API from those assumptions; they should not replace the source-facing mirror step as the
main public statement. -/

-- Proof sketch: expand `mirror_descent_update_objective_apply`, rewrite `B[ω] x xk` with
-- `bregmanDistance_def`, and cancel the `x`-independent constant
-- `⟪∇ω(xk), xk⟫ - ω(xk)`.
/-- The Chapter 9 owner `mirror_descent_update_objective` differs from the textbook Bregman-form
mirror-step objective only by the constant `⟪∇ω(x^k), x^k⟫ - ω(x^k)`. -/
theorem mirror_descent_update_objective_add_constant_eq_bregman_form
    (ω : E → EReal) (xk gradf : E) (t : ℝ) :
    (fun x ↦
      mirror_descent_update_objective (fun y ↦ (ω y).toReal) xk gradf t x +
        (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal)) =
      fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk :=
  by
    funext x
    -- Expand both owner spellings and then cancel the constant terms.
    rw [mirror_descent_update_objective_apply, bregmanDistance_def]
    rw [inner_sub_left, inner_sub_right]
    ring

-- Proof sketch: apply
-- `mirror_descent_update_objective_add_constant_eq_bregman_form`; adding a constant preserves
-- minimizers on `C`.
/-- The canonical Chapter 9 one-step owner and the textbook Bregman-form objective have the same
minimizers on `C`. -/
theorem isMinOn_mirror_descent_update_objective_iff_isMinOn_bregman_form
    (ω : E → EReal) (C : Set E) (xk xNext gradf : E) (t : ℝ) :
    (xNext ∈ C ∧
      IsMinOn (mirror_descent_update_objective (fun y ↦ (ω y).toReal) xk gradf t) C xNext) ↔
      (xNext ∈ C ∧ IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext) :=
  by
    let c : ℝ := inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) xk - (ω xk).toReal
    constructor
    · rintro ⟨hxNext, h⟩
      refine ⟨hxNext, ?_⟩
      rw [isMinOn_iff] at h ⊢
      intro y hy
      -- Add the same constant to both sides and rewrite with the Bregman-form identity.
      have hxEq :
          mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t xNext + c =
            inner ℝ (t • gradf) xNext + B[ω] xNext xk := by
        simpa [c] using
          congrFun (mirror_descent_update_objective_add_constant_eq_bregman_form ω xk gradf t) xNext
      have hyEq :
          mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t y + c =
            inner ℝ (t • gradf) y + B[ω] y xk := by
        simpa [c] using
          congrFun (mirror_descent_update_objective_add_constant_eq_bregman_form ω xk gradf t) y
      have hxEqComm :
          c + mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t xNext =
            inner ℝ (t • gradf) xNext + B[ω] xNext xk := by
        simpa [add_comm] using hxEq
      have hyEqComm :
          c + mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t y =
            inner ℝ (t • gradf) y + B[ω] y xk := by
        simpa [add_comm] using hyEq
      have hshift := add_le_add_right (h y hy) c
      rw [hxEqComm, hyEqComm] at hshift
      exact hshift
    · rintro ⟨hxNext, h⟩
      refine ⟨hxNext, ?_⟩
      rw [isMinOn_iff] at h ⊢
      intro y hy
      -- The reverse direction subtracts the same constant from the Bregman-form comparison.
      have hxEq :
          inner ℝ (t • gradf) xNext + B[ω] xNext xk + (-c) =
            mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t xNext := by
        rw [← congrFun (mirror_descent_update_objective_add_constant_eq_bregman_form ω xk gradf t)
          xNext]
        ring
      have hyEq :
          inner ℝ (t • gradf) y + B[ω] y xk + (-c) =
            mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t y := by
        rw [← congrFun (mirror_descent_update_objective_add_constant_eq_bregman_form ω xk gradf t)
          y]
        ring
      have hxEqComm :
          -c + (inner ℝ (t • gradf) xNext + B[ω] xNext xk) =
            mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t xNext := by
        simpa [add_comm] using hxEq
      have hyEqComm :
          -c + (inner ℝ (t • gradf) y + B[ω] y xk) =
            mirror_descent_update_objective (fun z ↦ (ω z).toReal) xk gradf t y := by
        simpa [add_comm] using hyEq
      have hshift := add_le_add_right (h y hy) (-c)
      rw [hxEqComm, hyEqComm] at hshift
      exact hshift

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: for a Bregman potential on `C`, the constrained potential
`ω + δ_ C` has effective domain exactly `C`. -/
lemma effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn
    (hω : IsBregmanPotentialOn ω C σ) :
    effective_domain (ω + δ_ C) = C := by
  ext x
  constructor
  · intro hx
    -- Outside `C`, the indicator contributes `⊤`, so finiteness forces feasibility.
    by_cases hxC : x ∈ C
    · exact hxC
    · have hx_top : (ω + δ_ C) x = ⊤ := by
        simpa [Pi.add_apply, extendedIndicator_of_not_mem hxC] using
          EReal.add_top_of_ne_bot (hω.toIsProperExtendedRealFunction.ne_bot x)
      exact False.elim ((ne_of_lt (mem_effective_domain.mp hx)) hx_top)
  · intro hxC
    -- On `C`, the indicator vanishes and the effective-domain condition reduces to that of `ω`.
    have hxω : x ∈ effective_domain ω := hω.subset_effective_domain hxC
    simpa [Pi.add_apply, extendedIndicator_of_mem hxC] using hxω

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: on feasible points, the constrained potential `ω + δ_ C` has the same
real value as `ω`. -/
lemma toReal_addIndicator_eq_of_mem
    (hxC : xk ∈ C) :
    ((ω + δ_ C) xk).toReal = (ω xk).toReal := by
  -- On `C`, the indicator is `0`, so the constrained value is just the original potential value.
  simp [Pi.add_apply, extendedIndicator_of_mem hxC]

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: once one feasible point is known, the constrained potential
`ω + δ_ C` is proper. -/
lemma constrainedPotential_proper_of_mem
    (hω : IsBregmanPotentialOn ω C σ)
    {x : E} (hx : x ∈ C) :
    IsProperExtendedRealFunction (ω + δ_ C) := by
  constructor
  · intro y
    by_cases hy : y ∈ C
    · simpa [Pi.add_apply, extendedIndicator_of_mem hy] using
        hω.toIsProperExtendedRealFunction.ne_bot y
    · simp [Pi.add_apply, extendedIndicator_of_not_mem hy,
        EReal.add_top_of_ne_bot (hω.toIsProperExtendedRealFunction.ne_bot y)]
  · exact ⟨x, by
      simpa [effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn hω] using hx⟩

/-- Helper for Text 9.4: on feasible points, the Bregman-form mirror objective is the constrained
potential minus the dual pairing with `∇ω(x^k) - t g_f`, up to an `x`-independent constant. -/
lemma mirrorDescentBregmanObjective_eq_constrainedPotential_minus_pairing
    {x : E} (hx : x ∈ C) :
    inner ℝ (t • gradf) x + B[ω] x xk =
      ((ω + δ_ C) x).toReal -
        inner ℝ (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) x +
        (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal) := by
  -- Expand the Bregman distance and collect the `x`-dependent terms into one pairing.
  rw [bregmanDistance_def, toReal_addIndicator_eq_of_mem (ω := ω) (C := C) (xk := x) hx]
  rw [inner_sub_right, inner_sub_left]
  ring

/-- Helper for Text 9.4: on feasible points, the constrained-potential support-gap inequality is
exactly the mirror-descent comparison. -/
lemma constrainedPotentialGap_iff_mirrorDescentComparison
    (hω : IsBregmanPotentialOn ω C σ)
    {y : E} (hxNext : xNext ∈ C) (hy : y ∈ C) :
    (((inner ℝ (∇ (fun z ↦ (ω z).toReal) xk - t • gradf) (y - xNext) : ℝ)) : EReal) ≤
        (ω + δ_ C) y - (ω + δ_ C) xNext ↔
      inner ℝ (t • gradf) xNext + B[ω] xNext xk ≤ inner ℝ (t • gradf) y + B[ω] y xk := by
  let fTilde : E → EReal := ω + δ_ C
  let g0 : E := ∇ (fun z ↦ (ω z).toReal) xk - t • gradf
  have hxNext_eff : xNext ∈ effective_domain fTilde := by
    simpa [fTilde, effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn hω] using hxNext
  have hy_eff : y ∈ effective_domain fTilde := by
    simpa [fTilde, effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn hω] using hy
  have hxNext_val :
      fTilde xNext = ((((fTilde xNext).toReal : ℝ)) : EReal) :=
    (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxNext_eff))
      ((constrainedPotential_proper_of_mem (ω := ω) (C := C) (σ := σ) hω hxNext).ne_bot xNext)).symm
  have hy_val :
      fTilde y = ((((fTilde y).toReal : ℝ)) : EReal) :=
    (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hy_eff))
      ((constrainedPotential_proper_of_mem (ω := ω) (C := C) (σ := σ) hω hxNext).ne_bot y)).symm
  have hgap_real :
      inner ℝ g0 (y - xNext) ≤ (fTilde y).toReal - (fTilde xNext).toReal ↔
        inner ℝ (t • gradf) xNext + B[ω] xNext xk ≤ inner ℝ (t • gradf) y + B[ω] y xk := by
    have hxEq :
        inner ℝ (t • gradf) xNext + B[ω] xNext xk =
          (fTilde xNext).toReal - inner ℝ g0 xNext +
            (inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) xk - (ω xk).toReal) := by
      simpa [fTilde, g0] using
        mirrorDescentBregmanObjective_eq_constrainedPotential_minus_pairing
          (ω := ω) (C := C) (xk := xk) (gradf := gradf) (t := t) hxNext
    have hyEq :
        inner ℝ (t • gradf) y + B[ω] y xk =
          (fTilde y).toReal - inner ℝ g0 y +
            (inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) xk - (ω xk).toReal) := by
      simpa [fTilde, g0] using
        mirrorDescentBregmanObjective_eq_constrainedPotential_minus_pairing
          (ω := ω) (C := C) (xk := xk) (gradf := gradf) (t := t) hy
    have hinner_sub : inner ℝ g0 (y - xNext) = inner ℝ g0 y - inner ℝ g0 xNext := by
      rw [inner_sub_right]
    constructor
    · intro hgap
      linarith
    · intro hcompare
      linarith
  have hgap_ereal :
      (((inner ℝ g0 (y - xNext) : ℝ)) : EReal) ≤ fTilde y - fTilde xNext ↔
        inner ℝ g0 (y - xNext) ≤ (fTilde y).toReal - (fTilde xNext).toReal := by
    constructor
    · intro hgap
      have hgap' :
          (((inner ℝ g0 (y - xNext) : ℝ)) : EReal) ≤
            ((((fTilde y).toReal - (fTilde xNext).toReal : ℝ)) : EReal) := by
        rw [hy_val, hxNext_val] at hgap
        simpa [EReal.coe_sub] using hgap
      exact EReal.coe_le_coe_iff.mp hgap'
    · intro hgap
      have hgap' :
          (((inner ℝ g0 (y - xNext) : ℝ)) : EReal) ≤
            ((((fTilde y).toReal - (fTilde xNext).toReal : ℝ)) : EReal) :=
        EReal.coe_le_coe hgap
      rw [hy_val, hxNext_val]
      simpa [EReal.coe_sub] using hgap'
  simpa [fTilde, g0] using hgap_ereal.trans hgap_real

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: the constrained potential `ω + δ_ C` is proper, lower semicontinuous,
and convex under the standing Bregman-potential and closed-feasible-set assumptions. -/
lemma constrainedPotential_properClosedConvex
    (hC_closed : IsClosed C)
    (hω : IsBregmanPotentialOn ω C σ)
    (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    IsProperExtendedRealFunction (ω + δ_ C) ∧
      LowerSemicontinuous (ω + δ_ C) ∧
      is_convex_function (ω + δ_ C) := by
  have hC_convex : Convex ℝ C := hω.strongConvexOn.1
  have hindicator_ne_bot : ∀ x : E, (δ_ C) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
  have hsum_closed : LowerSemicontinuous (ω + δ_ C) := by
    refine hω.closed.add' hC_closed.lowerSemicontinuous_extendedIndicator ?_
    intro x
    exact EReal.continuousAt_add
      (Or.inr (hindicator_ne_bot x))
      (Or.inl (hω.toIsProperExtendedRealFunction.ne_bot x))
  have hindicator_convex :
      is_convex_function (δ_ C) :=
    extendedIndicator_isConvexFunction_of_convex C hC_convex
  have hsum_convex :
      is_convex_function (ω + δ_ C) := by
    simpa [Pi.add_apply] using
      is_convex_function_pointwise_add
        hω.convex hindicator_convex
        hω.toIsProperExtendedRealFunction.ne_bot hindicator_ne_bot
  refine ⟨?_, hsum_closed, hsum_convex⟩
  constructor
  · intro x
    by_cases hx : x ∈ C
    · simpa [Pi.add_apply, extendedIndicator_of_mem hx] using
        hω.toIsProperExtendedRealFunction.ne_bot x
    · simp [Pi.add_apply, extendedIndicator_of_not_mem hx,
        EReal.add_top_of_ne_bot (hω.toIsProperExtendedRealFunction.ne_bot x)]
  · exact
      ⟨xk, by
        simpa [effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn hω] using hxk.1⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: a primal subgradient of `f` at `x` yields the bidual evaluation
subgradient of `conjugate_function f` at the same dual vector. -/
lemma eval_mem_subdifferential_conjugate_of_mem_subdifferential
    {f : E → EReal} (hf_proper : IsProperExtendedRealFunction f)
    {x : E} {y : Module.Dual ℝ E} (hy : y ∈ ∂f(x)) :
    Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) := by
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hy).1
  have h_ne_bot : ∀ z ∈ effective_domain f, f z ≠ ⊥ := fun z _ ↦ hf_proper.ne_bot z
  have hupper : conjugate_function f y ≤ (y x : EReal) - f x := by
    -- Control each conjugate witness by the supporting hyperplane coming from `hy`.
    rw [conjugate_function_apply]
    refine sSup_le ?_
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ effective_domain f
    · have hsub_real :
          y (z - x) ≤ (f z).toReal - (f x).toReal :=
        subgradient_eval_le_toReal_sub f x z h_ne_bot hx hz hy
      have hpair_real : y z - (f z).toReal ≤ y x - (f x).toReal := by
        have hlin : y (z - x) = y z - y x := by
          simp
        linarith
      have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (ne_of_lt hx) (hf_proper.ne_bot x)).symm
      have hfz_eq : f z = (((f z).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (ne_of_lt hz) (hf_proper.ne_bot z)).symm
      -- Convert the real inequality back to the owner `EReal` form.
      change (y z : EReal) - f z ≤ (y x : EReal) - f x
      rw [hfx_eq, hfz_eq]
      simpa [EReal.coe_sub] using (EReal.coe_le_coe hpair_real)
    · have hztop : f z = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hz))
      simp [hztop]
  have hlower : (y x : EReal) - f x ≤ conjugate_function f y := by
    -- The support value at `x` is one term in the defining supremum of the conjugate.
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self x)
  have hEq : conjugate_function f y = (y x : EReal) - f x :=
    le_antisymm hupper hlower
  have hx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  lift f x to ℝ using ⟨hx_top, hf_proper.ne_bot x⟩ with fx hfx
  have hy_finite :
      conjugate_function f y = (((y x - fx : ℝ)) : EReal) := by
    calc
      conjugate_function f y = (y x : EReal) - ((fx : ℝ) : EReal) := hEq
      _ = (((y x - fx : ℝ)) : EReal) := by simp [EReal.coe_sub]
  have hy_eff : y ∈ effective_domain (conjugate_function f) := by
    -- Fenchel equality identifies the conjugate value with a finite affine support value.
    rw [mem_effective_domain, hy_finite]
    exact EReal.coe_lt_top (y x - fx)
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hy_eff, ?_⟩
  intro y' hy'
  -- The pointwise lower bound in the conjugate definition is exactly the dual-side subgradient
  -- inequality once we rewrite through Fenchel equality at `y`.
  have hy'_lower : (y' x : EReal) - f x ≤ conjugate_function f y' := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self x)
  have hpair :
      conjugate_function f y +
          (((Module.Dual.eval ℝ E x) (y' - y) : ℝ) : EReal) =
        (y' x : EReal) - f x := by
    rw [hy_finite, ← hfx]
    have heval : ((Module.Dual.eval ℝ E x) (y' - y) : ℝ) = y' x - y x := by
      simp [Module.Dual.eval_apply]
    rw [heval]
    change
      (((y x - fx : ℝ)) : EReal) + (((y' x - y x : ℝ)) : EReal) =
        (((y' x : ℝ) - fx : ℝ) : EReal)
    rw [← EReal.coe_add]
    congr 1
    ring
  rw [hpair]
  exact hy'_lower

/-- Helper for Text 9.4: under proper/closed/convex hypotheses, conjugate-side evaluation
subgradient membership transports back to primal subgradient membership. -/
lemma mem_subdifferential_of_eval_mem_subdifferential_conjugate
    {f : E → EReal}
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    {x : E} {y : Module.Dual ℝ E}
    (hy : Module.Dual.eval ℝ E x ∈ ∂(conjugate_function f)(y)) :
    y ∈ ∂ f(x) :=
  by
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hy
    have hconj_ne_bot :
        ∀ z : Module.Dual ℝ E, conjugate_function f z ≠ ⊥ :=
      fun z ↦ conjugate_function_ne_bot_of_proper f hf_proper z
    let φ : Module.Dual ℝ E → EReal := fun z ↦ (z x : EReal) - conjugate_function f z
    have hmax : IsMaxOn φ Set.univ y := by
      rw [isMaxOn_univ_iff]
      intro y'
      by_cases hy' : y' ∈ effective_domain (conjugate_function f)
      · lift conjugate_function f y to ℝ using
          ⟨ne_of_lt hy.1, hconj_ne_bot y⟩ with cy hcy
        lift conjugate_function f y' to ℝ using
          ⟨ne_of_lt hy', hconj_ne_bot y'⟩ with cy' hcy'
        have hineq := hy.2 y' hy'
        have hineq_real :
            cy + ((Module.Dual.eval ℝ E x) (y' - y)) ≤ cy' := by
          have hineq' :
              ((cy : ℝ) : EReal) +
                  ((((Module.Dual.eval ℝ E x) (y' - y) : ℝ)) : EReal) ≤
                ((cy' : ℝ) : EReal) := by
            simpa [hcy, hcy', EReal.coe_add] using hineq
          exact EReal.coe_le_coe_iff.mp hineq'
        have hφ_real : y' x - cy' ≤ y x - cy := by
          have heval :
              ((Module.Dual.eval ℝ E x) (y' - y)) = y' x - y x := by
            simp [Module.Dual.eval_apply]
          linarith
        have hφ_ereal :
            (((y' x - cy' : ℝ)) : EReal) ≤ (((y x - cy : ℝ)) : EReal) :=
          EReal.coe_le_coe hφ_real
        simpa [φ, hcy, hcy', EReal.coe_sub] using hφ_ereal
      · have hy'_top : conjugate_function f y' = ⊤ := by
          exact le_antisymm le_top (not_lt.mp hy')
        simp [φ, hy'_top]
    have hdual_eq :
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          (y x : EReal) - conjugate_function f y := by
      have hmax' : ∀ y' : Module.Dual ℝ E, φ y' ≤ φ y := by
        simpa [isMaxOn_univ_iff] using hmax
      rw [conjugate_function_apply]
      refine le_antisymm ?_ ?_
      · refine sSup_le ?_
        rintro _ ⟨y', rfl⟩
        exact hmax' y'
      · exact le_sSup (Set.mem_range_self y)
    have hbiconj :
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) = f x := by
      simpa [biconjugate_function] using
        congrArg (fun g : E → EReal ↦ g x)
          (biconjugate_function_eq_self_of_proper_closed_convex
            f hf_proper hf_closed hf_convex)
    lift conjugate_function f y to ℝ using
      ⟨ne_of_lt hy.1, hconj_ne_bot y⟩ with cy hcy
    have hfx_eq :
        f x = (((y x - cy : ℝ)) : EReal) := by
      calc
        f x = (y x : EReal) - ((cy : ℝ) : EReal) := by
          simpa [hcy] using (hbiconj.symm.trans hdual_eq)
        _ = (((y x - cy : ℝ)) : EReal) := by simp [EReal.coe_sub]
    have hx : x ∈ effective_domain f := by
      rw [mem_effective_domain, hfx_eq]
      exact EReal.coe_lt_top (y x - cy)
    have hx_bot : f x ≠ ⊥ := hf_proper.ne_bot x
    lift f x to ℝ using ⟨ne_of_lt hx, hx_bot⟩ with fx hfx
    have hfx_real : fx = y x - cy := by
      have hfx_eq' :
          ((fx : ℝ) : EReal) = (((y x - cy : ℝ)) : EReal) := by
        simpa [hfx] using hfx_eq
      exact_mod_cast hfx_eq'
    have hconj_eq :
        conjugate_function f y = (y x : EReal) - f x := by
      have hcy_real : cy = y x - fx := by
        linarith
      calc
        conjugate_function f y = ((cy : ℝ) : EReal) := by symm; exact hcy
        _ = (y x : EReal) - ((fx : ℝ) : EReal) := by
          rw [hcy_real]
          simp [EReal.coe_sub]
        _ = (y x : EReal) - f x := by rw [hfx]
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hx, ?_⟩
    intro z hz
    have hz_pair :
        (y z : EReal) - f z ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self z)
    lift f z to ℝ using ⟨ne_of_lt hz, hf_proper.ne_bot z⟩ with fz hfz
    have hz_pair_real :
        y z - fz ≤ y x - fx := by
      have hz_pair' :
          (((y z - fz : ℝ)) : EReal) ≤ (((y x - fx : ℝ)) : EReal) := by
        simpa [hfz, hconj_eq, hfx, EReal.coe_sub] using hz_pair
      exact EReal.coe_le_coe_iff.mp hz_pair'
    have hsub_real :
        fx + y (z - x) ≤ fz := by
      have hy_eval : y (z - x) = y z - y x := by
        simp
      linarith
    have hsub_ereal :
        (((fx + y (z - x) : ℝ)) : EReal) ≤ ((fz : ℝ) : EReal) := by
      exact EReal.coe_le_coe hsub_real
    simpa [hfx, hfz, EReal.coe_add, ge_iff_le] using hsub_ereal

/-- Helper for Text 9.4: strong convexity of `f` makes its conjugate finite at every dual vector,
transported back from the continuous-dual theorem in Chapter 5. -/
lemma conjugateFunctionFiniteEverywhere_of_proper_closed_strongConvexOn
    {f : E → EReal}
    (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    ∀ y : Module.Dual ℝ E, conjugate_function f y ≠ ⊥ ∧ conjugate_function f y < ⊤ := by
  intro y
  -- Finite dimensionality identifies algebraic and continuous dual vectors.
  simpa [conjugate_function_strongDual] using
    conjugate_function_finite_of_proper_closed_strongConvexOn
      σ hσ f hf_proper hf_closed hstrong
        (LinearMap.toContinuousLinearMap y)

/-- Helper for Text 9.4: the real-valued primal conjugate is differentiable at every point once
the constrained potential is proper, closed, and strongly convex. -/
lemma differentiableAt_primalConjugate_of_proper_closed_strongConvexOn
    {f : E → EReal}
    (hσ : 0 < σ)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (g : E) :
    DifferentiableAt ℝ (fun y : E ↦ (((f∗) y).toReal)) g := by
  have hsmooth :
      is_l_smooth_on
        (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal)
        Set.univ
        (Real.toNNReal (1 / σ)) :=
    is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
      σ hσ f hf_proper hf_closed hstrong
  have hdual :
      DifferentiableAt ℝ
        (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal)
        (toDualMap ℝ E g) :=
    hsmooth.1 _ (by simp)
  -- Compose the differentiable strong-dual conjugate with the Riesz map to return to `E`.
  have hcomp :
      DifferentiableAt ℝ
        (fun y : E ↦ (conjugate_function_strongDual f (toDualMap ℝ E y)).toReal)
        g :=
    by
      let toDualCLM : E →L[ℝ] StrongDual ℝ E :=
        (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
      have htoDual :
          DifferentiableAt ℝ toDualCLM g :=
        toDualCLM.differentiableAt
      simpa [toDualCLM] using hdual.comp g htoDual
  exact hcomp

/-- Helper for Text 9.4: pulling back the bidual evaluation functional along the Riesz map gives
the primal Riesz functional of the same vector. -/
lemma dualMap_riesz_eval_eq_riesz (x : E) :
    (((ContinuousLinearMap.coeLM ℝ).comp
        (InnerProductSpace.toDual ℝ E).toLinearEquiv.toLinearMap).dualMap
        (Module.Dual.eval ℝ E x)) =
      (toDualMap ℝ E x : Module.Dual ℝ E) := by
  ext u
  -- Both linear functionals evaluate to the same inner product.
  change ((InnerProductSpace.toDual ℝ E u : StrongDual ℝ E) : Module.Dual ℝ E) x =
      (toDualMap ℝ E x : Module.Dual ℝ E) u
  change inner ℝ u x = inner ℝ x u
  rw [real_inner_comm]

/-- Helper for Text 9.4: precomposing a convex conjugate with the Riesz map keeps the primal
conjugate `f∗` convex on `E`. -/
lemma primalConjugate_convex
    {f : E → EReal}
    (hconv : is_convex_function (conjugate_function f)) :
    is_convex_function (f∗) := by
  let dualToLinear : E →ₗ[ℝ] Module.Dual ℝ E :=
    (ContinuousLinearMap.coeLM ℝ).comp
      (InnerProductSpace.toDual ℝ E).toLinearEquiv.toLinearMap
  -- Use the Chapter 2 affine-precomposition owner theorem once and then return to the `f∗`
  -- notation.
  have hcomp :
      is_convex_function
        (fun x : E ↦ conjugate_function f (dualToLinear x + 0)) :=
      is_convex_function_precompose_linearMap_add hconv dualToLinear 0
  simpa [conjugate_function_primal, dualToLinear] using hcomp

/-- Helper for Text 9.4: for finite `c` and non-`⊥` summands, the equality `c = a + b` can be
rewritten as `a = c - b`. -/
lemma eqAddIffLeftEqSubOfNeBot
    {a b c : EReal} (ha_ne_bot : a ≠ ⊥) (hb_ne_bot : b ≠ ⊥) (hc_ne_top : c ≠ ⊤) :
    c = a + b ↔ a = c - b := by
  constructor
  · intro hEq
    refine le_antisymm ?_ ?_
    · exact
        (EReal.le_sub_iff_add_le (a := a) (b := b) (c := c)
          (.inl hb_ne_bot) (.inr hc_ne_top)).2 hEq.ge
    · exact
        (EReal.sub_le_iff_le_add (a := c) (b := b) (c := a)
          (.inl hb_ne_bot) (.inr ha_ne_bot)).2 hEq.le
  · intro hEq
    refine le_antisymm ?_ ?_
    · exact
        (EReal.sub_le_iff_le_add (a := c) (b := b) (c := a)
          (.inl hb_ne_bot) (.inr ha_ne_bot)).1 hEq.ge
    · exact
        (EReal.add_le_of_le_sub (a := a) (b := c) (c := b) hEq.le)

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 9.4: for a proper extended-real-valued function, Fenchel--Young equality is
equivalent to primal subgradient membership. -/
lemma pairingEqAddConjugate_iff_memSubdifferential_ofProper
    {f : E → EReal} (hf_proper : IsProperExtendedRealFunction f)
    (x : E) (y : Module.Dual ℝ E) :
    (y x : EReal) = f x + conjugate_function f y ↔ y ∈ ∂ f(x) := by
  constructor
  · intro hEq
    have hconj_ne_bot : conjugate_function f y ≠ ⊥ :=
      conjugate_function_ne_bot_of_proper f hf_proper y
    have hpair_ne_top : (y x : EReal) ≠ ⊤ := EReal.coe_ne_top (y x)
    have hx_top : f x ≠ ⊤ := by
      intro hfx_top
      have hpair_top : (y x : EReal) = ⊤ := by
        rw [hfx_top, EReal.top_add_of_ne_bot hconj_ne_bot] at hEq
        exact hEq
      exact hpair_ne_top hpair_top
    have hx : x ∈ effective_domain f := by
      rw [mem_effective_domain]
      exact lt_top_iff_ne_top.mpr hx_top
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hx, ?_⟩
    intro z hz
    have hz_term : ((y z : EReal) - f z) ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self z)
    have hpair_sub : (y x : EReal) - f x = conjugate_function f y := by
      exact
        ((eqAddIffLeftEqSubOfNeBot
          hconj_ne_bot (hf_proper.ne_bot x) hpair_ne_top).mp
          (by simpa [add_comm] using hEq)).symm
    have hz_pair :
        (y z : EReal) - f z ≤ (y x : EReal) - f x := by
      simpa [hpair_sub] using hz_term
    lift f x to ℝ using ⟨hx_top, hf_proper.ne_bot x⟩ with fx hfx
    lift f z to ℝ using ⟨ne_of_lt hz, hf_proper.ne_bot z⟩ with fz hfz
    have hz_pair_real :
        y z - fz ≤ y x - fx := by
      have hz_pair' :
          (((y z - fz : ℝ)) : EReal) ≤ (((y x - fx : ℝ)) : EReal) := by
        simpa [hfx, hfz, EReal.coe_sub] using hz_pair
      exact EReal.coe_le_coe_iff.mp hz_pair'
    have hsub_real :
        fx + y (z - x) ≤ fz := by
      have hy_eval : y (z - x) = y z - y x := by
        simp
      linarith
    have hsub_ereal :
        (((fx + y (z - x) : ℝ)) : EReal) ≤ ((fz : ℝ) : EReal) :=
      EReal.coe_le_coe hsub_real
    -- Convert the real inequality back to the owner subgradient inequality.
    simpa [hfx, hfz, EReal.coe_add, ge_iff_le] using hsub_ereal
  · intro hy
    have hx : x ∈ effective_domain f := by
      rw [mem_subdifferential] at hy
      exact hy.1
    have hobj :
        conjugate_function f y ≤ (y x : EReal) - f x := by
      rw [conjugate_function_apply]
      refine sSup_le ?_
      rintro _ ⟨z, rfl⟩
      by_cases hz : z ∈ effective_domain f
      · have hsub_real :
            y (z - x) ≤ (f z).toReal - (f x).toReal :=
          subgradient_eval_le_toReal_sub
            f x z (fun w _ ↦ hf_proper.ne_bot w) hx hz hy
        have hpair_real : y z - (f z).toReal ≤ y x - (f x).toReal := by
          have hy_eval : y (z - x) = y z - y x := by
            simp
          linarith
        have hfx_eq : f x = ((((f x).toReal : ℝ)) : EReal) :=
          (EReal.coe_toReal (ne_of_lt hx) (hf_proper.ne_bot x)).symm
        have hfz_eq : f z = ((((f z).toReal : ℝ)) : EReal) :=
          (EReal.coe_toReal (ne_of_lt hz) (hf_proper.ne_bot z)).symm
        change (y z : EReal) - f z ≤ (y x : EReal) - f x
        rw [hfx_eq, hfz_eq]
        simpa [EReal.coe_sub] using (EReal.coe_le_coe hpair_real)
      · have hztop : f z = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hz))
        simp [hztop]
    have hterm : ((y x : EReal) - f x) ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self x)
    have hterm_ne_bot : ((y x : EReal) - f x) ≠ ⊥ := by
      lift f x to ℝ using ⟨ne_of_lt hx, hf_proper.ne_bot x⟩ with fx hfx
      simpa [hfx, EReal.coe_sub] using EReal.coe_ne_bot (y x - fx)
    have hconj_ne_bot : conjugate_function f y ≠ ⊥ := by
      exact bot_lt_iff_ne_bot.mp
        ((bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hterm)
    have hlower : (y x : EReal) ≤ f x + conjugate_function f y := by
      have hlower' : (y x : EReal) ≤ conjugate_function f y + f x := by
        exact
          (EReal.sub_le_iff_le_add (.inl (hf_proper.ne_bot x)) (.inr hconj_ne_bot)).1 hterm
      simpa [add_comm] using hlower'
    have hupper : f x + conjugate_function f y ≤ (y x : EReal) := by
      have hupper' : conjugate_function f y + f x ≤ (y x : EReal) :=
        EReal.add_le_of_le_sub hobj
      simpa [add_comm] using hupper'
    exact le_antisymm hlower hupper

/-- Helper for Text 9.4: after normalizing the primal conjugate through the Riesz map, a
subgradient of `x ↦ ((f∗ x).toReal : EReal)` at `g` is the same as the evaluation subgradient of
`conjugate_function f` at `toDualMap g`. -/
lemma toDualMap_mem_subdifferential_primalConjugate_iff_eval_mem_subdifferential_conjugate
    {f : E → EReal}
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (hfinite : ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤)
    {x g : E} :
    ((toDualMap ℝ E x : Module.Dual ℝ E) ∈
        ∂ (fun y : E ↦ (((f∗) y).toReal : EReal))(g)) ↔
      Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(toDualMap ℝ E g) := by
  let fStarReal : E → EReal := fun z ↦ (((f∗) z).toReal : EReal)
  have hfStarReal_eq (z : E) : fStarReal z = (f∗) z := by
    -- The finiteness hypothesis lets us stay on one `EReal` spelling for the primal conjugate.
    simpa [fStarReal] using
      (EReal.coe_toReal (ne_of_lt (hfinite z).2) (hfinite z).1)
  have hfStarReal_proper : IsProperExtendedRealFunction fStarReal := by
    -- The real-lifted primal conjugate is everywhere finite, hence proper.
    constructor
    · intro z
      simp [fStarReal]
    · refine ⟨g, ?_⟩
      rw [mem_effective_domain, hfStarReal_eq]
      exact (hfinite g).2
  have hleft :
      ((toDualMap ℝ E x : Module.Dual ℝ E) ∈ ∂ fStarReal(g)) ↔
        IsMaxOn
          (fun z : E ↦ (((toDualMap ℝ E x : Module.Dual ℝ E) z : ℝ) : EReal) - fStarReal z)
          Set.univ
          g := by
    have hpair :
        ((toDualMap ℝ E x : Module.Dual ℝ E) ∈ ∂ fStarReal(g)) ↔
          ((((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ)) : EReal) =
            fStarReal g + conjugate_function fStarReal (toDualMap ℝ E x) := by
      -- Route correction: rewrite subgradient membership to the Fenchel equality first.
      simpa using
        (pairingEqAddConjugate_iff_memSubdifferential_ofProper
          (f := fStarReal) hfStarReal_proper g (toDualMap ℝ E x)).symm
    have hsub :
        ((((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ)) : EReal) =
            fStarReal g + conjugate_function fStarReal (toDualMap ℝ E x) ↔
          conjugate_function fStarReal (toDualMap ℝ E x) =
            ((((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ)) : EReal) - fStarReal g := by
      have hpair_ne_top :
          ((((toDualMap ℝ E x : Module.Dual ℝ E) g : ℝ)) : EReal) ≠ ⊤ :=
        EReal.coe_ne_top _
      have hconj_ne_bot :
          conjugate_function fStarReal (toDualMap ℝ E x) ≠ ⊥ :=
        conjugate_function_ne_bot_of_proper fStarReal hfStarReal_proper (toDualMap ℝ E x)
      -- Move the conjugate term to the right so Theorem 4.11 applies directly.
      simpa [add_comm] using
        (eqAddIffLeftEqSubOfNeBot
          hconj_ne_bot (hfStarReal_proper.ne_bot g) hpair_ne_top)
    exact hpair.trans <|
      hsub.trans <|
        (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
          fStarReal g (toDualMap ℝ E x))
  have hright :
      Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(toDualMap ℝ E g) ↔
        IsMaxOn
          (fun y : Module.Dual ℝ E ↦ (y x : EReal) - conjugate_function f y)
          Set.univ
          (toDualMap ℝ E g : Module.Dual ℝ E) := by
    have hmem :
        Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(toDualMap ℝ E g) ↔
          (toDualMap ℝ E g : Module.Dual ℝ E) ∈ ∂ f(x) := by
      constructor
      · intro hy
        exact
          mem_subdifferential_of_eval_mem_subdifferential_conjugate
            hf_proper hf_closed hf_convex hy
      · intro hy
        exact eval_mem_subdifferential_conjugate_of_mem_subdifferential hf_proper hy
    have hpair :
        (toDualMap ℝ E g : Module.Dual ℝ E) ∈ ∂ f(x) ↔
          ((((toDualMap ℝ E g : Module.Dual ℝ E) x : ℝ)) : EReal) =
            f x + conjugate_function f (toDualMap ℝ E g) := by
      -- The primal Fenchel equality packages the subgradient witness on the original owner.
      simpa using
        (pairingEqAddConjugate_iff_memSubdifferential_ofProper
          hf_proper x (toDualMap ℝ E g)).symm
    have hsub :
        ((((toDualMap ℝ E g : Module.Dual ℝ E) x : ℝ)) : EReal) =
            f x + conjugate_function f (toDualMap ℝ E g) ↔
          f x =
            ((((toDualMap ℝ E g : Module.Dual ℝ E) x : ℝ)) : EReal) -
              conjugate_function f (toDualMap ℝ E g) := by
      have hpair_ne_top :
          ((((toDualMap ℝ E g : Module.Dual ℝ E) x : ℝ)) : EReal) ≠ ⊤ :=
        EReal.coe_ne_top _
      have hconj_ne_bot :
          conjugate_function f (toDualMap ℝ E g) ≠ ⊥ :=
        conjugate_function_ne_bot_of_proper f hf_proper (toDualMap ℝ E g)
      -- This is the normal form expected by the dual argmax bridge for `f`.
      exact
        (eqAddIffLeftEqSubOfNeBot
          (hf_proper.ne_bot x) hconj_ne_bot hpair_ne_top)
    exact hmem.trans <|
      hpair.trans <|
      hsub.trans <|
        (self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex
          f hf_proper hf_closed hf_convex x (toDualMap ℝ E g))
  have htoDualMap_surjective :
      Function.Surjective (fun z : E ↦ (toDualMap ℝ E z : Module.Dual ℝ E)) := by
    intro y
    refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap y), ?_⟩
    ext u
    -- Finite dimensionality identifies the algebraic dual with the Riesz image of a primal vector.
    simp
  have hmax_equiv :
      IsMaxOn
          (fun z : E ↦ (((toDualMap ℝ E x : Module.Dual ℝ E) z : ℝ) : EReal) - fStarReal z)
          Set.univ
          g ↔
        IsMaxOn
          (fun y : Module.Dual ℝ E ↦ (y x : EReal) - conjugate_function f y)
          Set.univ
          (toDualMap ℝ E g : Module.Dual ℝ E) := by
    have hobjective_eq (z : E) :
        ((((toDualMap ℝ E x : Module.Dual ℝ E) z : ℝ)) : EReal) - fStarReal z =
          ((toDualMap ℝ E z : Module.Dual ℝ E) x : EReal) -
            conjugate_function f (toDualMap ℝ E z) := by
      -- Both argmax objectives are the same after rewriting the primal conjugate through the
      -- Riesz map and commuting the inner product.
      rw [hfStarReal_eq z, conjugate_function_primal_apply]
      simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
    rw [isMaxOn_univ_iff, isMaxOn_univ_iff]
    constructor
    · intro hgmax y
      rcases htoDualMap_surjective y with ⟨z, hz⟩
      -- After the Riesz change of variables, the two argmax objectives are identical.
      have htarget :
          ((toDualMap ℝ E z : Module.Dual ℝ E) x : EReal) -
              conjugate_function f (toDualMap ℝ E z) ≤
            ((toDualMap ℝ E g : Module.Dual ℝ E) x : EReal) -
              conjugate_function f (toDualMap ℝ E g) := by
        rw [← hobjective_eq z, ← hobjective_eq g]
        exact hgmax z
      simpa [hz] using htarget
    · intro hymax z
      -- The reverse implication is the same normalization read from right to left.
      have htarget :
          ((toDualMap ℝ E z : Module.Dual ℝ E) x : EReal) -
              conjugate_function f (toDualMap ℝ E z) ≤
            ((toDualMap ℝ E g : Module.Dual ℝ E) x : EReal) -
              conjugate_function f (toDualMap ℝ E g) :=
        hymax (toDualMap ℝ E z : Module.Dual ℝ E)
      rw [hobjective_eq z, hobjective_eq g]
      exact htarget
  exact hleft.trans <| hmax_equiv.trans hright.symm

/-- Helper for Text 9.4: pulling the conjugate subdifferential back along the Riesz map turns
evaluation functionals into Euclidean subgradients of the primal conjugate. -/
lemma evalMemSubdifferentialConjugate_iff_memEuclideanSubdifferentialAt_primalConjugate
    {f : E → EReal}
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (hfinite : ∀ y : E, (f∗) y ≠ ⊥ ∧ (f∗) y < ⊤)
    {x g : E} :
    Module.Dual.eval ℝ E x ∈ subdifferential (conjugate_function f) (toDualMap ℝ E g) ↔
      x ∈ euclideanSubdifferentialAt (fun y : E ↦ ((f∗) y).toReal) g := by
  -- Route correction: keep the owner Fenchel bridge separate from the Euclidean bookkeeping.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential]
  exact
    (toDualMap_mem_subdifferential_primalConjugate_iff_eval_mem_subdifferential_conjugate
      hf_proper hf_closed hf_convex hfinite).symm

-- Proof sketch: because `hω.subset_effective_domain` puts `C` inside `effective_domain ω` and
-- `hω.toIsProperExtendedRealFunction` rules out
-- `⊥`, the owner objective
-- `mirror_descent_update_objective (fun y ↦ (ω y).toReal) xk gradf t` on `C` agrees, up to the
-- constant from `isMinOn_mirror_descent_update_objective_iff_isMinOn_bregman_form`, with the
-- unconstrained extended-real objective
-- `x ↦ (ω + δ_C)(x) - ⟪∇ω(xk) - t g_f, x⟫`. Fermat's rule for that constrained potential therefore
-- gives the textbook optimality condition
-- `∇ω(xk) - t g_f ∈ ∂ (ω + δ_C) (x⁺)`, expressed on the chapter's continuous-dual bridge
-- notation `∂ₛ (ω + δ_C)(x⁺)`.
/-- Helper for Text 9.4: if `hω : IsBregmanPotentialOn ω C σ` and `x^k ∈ C ∩ dom(∂ ω)`, then the
Chapter 9 mirror-descent step, encoded in Lean as
`x⁺ ∈ C ∧ IsMinOn (mirror_descent_update_objective ((fun y ↦ (ω y).toReal)) x^k g_f t) C x⁺`,
is equivalent to the constrained subgradient condition
`∇ω(x^k) - t g_f ∈ ∂ (ω + δ_C)(x⁺)`. -/
lemma mirror_descent_step_isMinOn_iff_dual_mem_subdifferential_add_indicator
    (hω : IsBregmanPotentialOn ω C σ)
    (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    (xNext ∈ C ∧
      IsMinOn (mirror_descent_update_objective (fun y ↦ (ω y).toReal) xk gradf t) C xNext) ↔
      toDualMap ℝ E (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) ∈
        ∂ₛ (ω + δ_ C)(xNext) :=
  by
    let fTilde : E → EReal := ω + δ_ C
    let g0 : E := ∇ (fun y ↦ (ω y).toReal) xk - t • gradf
    have hfTilde_proper : IsProperExtendedRealFunction fTilde :=
      constrainedPotential_proper_of_mem (ω := ω) (C := C) (σ := σ) hω hxk.1
    have hdomain : effective_domain fTilde = C :=
      effectiveDomain_addIndicator_eq_of_isBregmanPotentialOn (ω := ω) (C := C) (σ := σ) hω
    constructor
    · intro hstep
      -- Rewrite the mirror step to the Bregman form and then convert that comparison into the
      -- Chapter 6 strong-dual support inequality for `ω + δ_C`.
      rcases
          (isMinOn_mirror_descent_update_objective_iff_isMinOn_bregman_form
            ω C xk xNext gradf t).1 hstep with
        ⟨hxNext, hmin⟩
      have hsupport :
          xNext ∈ effective_domain fTilde ∧
            ∀ y ∈ effective_domain fTilde,
              ((inner ℝ g0 (y - xNext) : ℝ) : EReal) ≤ fTilde y - fTilde xNext := by
        rw [isMinOn_iff] at hmin
        refine ⟨by simpa [fTilde, hdomain] using hxNext, ?_⟩
        intro y hy
        have hyC : y ∈ C := by simpa [fTilde, hdomain] using hy
        exact
          (constrainedPotentialGap_iff_mirrorDescentComparison
            (ω := ω) (C := C) (σ := σ) (xk := xk) (xNext := xNext)
            (gradf := gradf) (t := t) hω hxNext hyC).2
            (hmin y hyC)
      have hsupport_shift :
          xNext ∈ effective_domain fTilde ∧
            ∀ y ∈ effective_domain fTilde,
              (((inner ℝ ((xNext + g0) - xNext) (y - xNext) : ℝ)) : EReal) ≤
                fTilde y - fTilde xNext := by
        refine ⟨hsupport.1, ?_⟩
        intro y hy
        simpa using hsupport.2 y hy
      have hsub :
          toDualMap ℝ E g0 ∈ ∂ₛ fTilde(xNext) := by
        simpa [fTilde, g0] using
          (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le
            fTilde hfTilde_proper (xNext + g0) xNext).2 hsupport_shift
      simpa [fTilde, g0] using hsub
    · intro hsub
      -- Apply the same Chapter 6 bridge in reverse, then return from the Bregman form to the
      -- source-facing mirror-step owner.
      have hsupport_shift :
          xNext ∈ effective_domain fTilde ∧
            ∀ y ∈ effective_domain fTilde,
              (((inner ℝ ((xNext + g0) - xNext) (y - xNext) : ℝ)) : EReal) ≤
                fTilde y - fTilde xNext := by
        exact
          (toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le
            fTilde hfTilde_proper (xNext + g0) xNext).1
            (by simpa [fTilde, g0] using hsub)
      have hsupport :
          xNext ∈ effective_domain fTilde ∧
            ∀ y ∈ effective_domain fTilde,
              ((inner ℝ g0 (y - xNext) : ℝ) : EReal) ≤ fTilde y - fTilde xNext := by
        refine ⟨hsupport_shift.1, ?_⟩
        intro y hy
        simpa using hsupport_shift.2 y hy
      rcases hsupport with ⟨hxNext_eff, hsupport⟩
      have hxNext : xNext ∈ C := by simpa [fTilde, hdomain] using hxNext_eff
      have hbreg :
          xNext ∈ C ∧ IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext := by
        refine ⟨hxNext, ?_⟩
        rw [isMinOn_iff]
        intro y hy
        have hy_eff : y ∈ effective_domain fTilde := by
          simpa [fTilde, hdomain] using hy
        exact
          (constrainedPotentialGap_iff_mirrorDescentComparison
            (ω := ω) (C := C) (σ := σ) (xk := xk) (xNext := xNext)
            (gradf := gradf) (t := t) hω hxNext hy).1
            (hsupport y hy_eff)
      exact
        (isMinOn_mirror_descent_update_objective_iff_isMinOn_bregman_form
          ω C xk xNext gradf t).2 hbreg

-- Proof sketch: combine the constrained-subgradient bridge above with Fenchel conjugacy for
-- `ω̃ = ω + δ_C`. The source assumes `C` is closed, so `δ_C` and hence `ω̃` are closed. Strong
-- convexity of the constrained potential then makes `ω̃∗` differentiable at the dual point, so
-- the singleton subdifferential there is represented by the gradient of `y ↦ ((ω̃∗) y).toReal`.
-- Transporting back through the Riesz map identifies the primal vector `x⁺` with that gradient.
/-- Text 9.4: letting `ω̃ = ω + δ_C`, if `C` is closed, `hω : IsBregmanPotentialOn ω C σ`, and
`x^k ∈ C ∩ dom(∂ ω)`, then the mirror-descent update step, encoded in Lean as
`x⁺ ∈ C ∧ IsMinOn (mirror_descent_update_objective ((fun y ↦ (ω y).toReal)) x^k g_f t) C x⁺`,
is equivalent to the source-facing conjugate formula
`x⁺ = ∇ ω̃∗(∇ω(x^k) - t g_f)`, expressed in Lean via the real-valued restriction of `ω̃∗`. -/
theorem mirror_descent_step_isMinOn_iff_eq_gradient_conjugate_add_indicator
    (hC_closed : IsClosed C)
    (hω : IsBregmanPotentialOn ω C σ)
    (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    (xNext ∈ C ∧
      IsMinOn (mirror_descent_update_objective (fun y ↦ (ω y).toReal) xk gradf t) C xNext) ↔
      xNext =
        ∇ (fun y ↦ ((((ω + δ_ C)∗) y).toReal))
          (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) :=
  by
    let fTilde : E → EReal := ω + δ_ C
    let g0 : E := ∇ (fun y ↦ (ω y).toReal) xk - t • gradf
    have hfTilde_pkg :=
      constrainedPotential_properClosedConvex
        (ω := ω) (C := C) (σ := σ) (xk := xk) hC_closed hω hxk
    have hfTilde_proper : IsProperExtendedRealFunction fTilde := hfTilde_pkg.1
    have hfTilde_closed : LowerSemicontinuous fTilde := hfTilde_pkg.2.1
    have hfTilde_convex : is_convex_function fTilde := hfTilde_pkg.2.2
    have hfTilde_strong :
        StrongConvexOn (effective_domain fTilde) σ (fun x ↦ (fTilde x).toReal) := by
      -- The constrained-potential owner theorem packages the stored strong convexity of `ω`.
      simpa [fTilde] using hω.strongConvexOn_add_indicator
    have hfinite_dual :
        ∀ y : Module.Dual ℝ E,
          conjugate_function fTilde y ≠ ⊥ ∧ conjugate_function fTilde y < ⊤ :=
      conjugateFunctionFiniteEverywhere_of_proper_closed_strongConvexOn
        hω.sigma_pos hfTilde_proper hfTilde_closed hfTilde_strong
    have hfinite_primal :
        ∀ y : E, (fTilde∗) y ≠ ⊥ ∧ (fTilde∗) y < ⊤ := by
      intro y
      constructor
      · change conjugate_function fTilde (toDualMap ℝ E y) ≠ ⊥
        exact (hfinite_dual (toDualMap ℝ E y)).1
      · change conjugate_function fTilde (toDualMap ℝ E y) < ⊤
        exact (hfinite_dual (toDualMap ℝ E y)).2
    have hconv_primal :
        ConvexOn ℝ Set.univ (fun y : E ↦ (((fTilde∗) y).toReal)) := by
      have hconv_eff :
          ConvexOn ℝ (effective_domain (fTilde∗)) (fun y : E ↦ (((fTilde∗) y).toReal)) :=
        convexOn_toReal_of_is_convex_function
          (f := fTilde∗) (conjugate_function_convex fTilde)
          (fun y _ ↦ (hfinite_primal y).1)
      have hdom_univ : effective_domain (fTilde∗) = Set.univ := by
        ext y
        constructor
        · intro _
          simp
        · intro _
          exact (hfinite_primal y).2
      simpa [hdom_univ] using hconv_eff
    have hdiff_primal :
        DifferentiableAt ℝ (fun y : E ↦ (((fTilde∗) y).toReal)) g0 :=
      differentiableAt_primalConjugate_of_proper_closed_strongConvexOn
        hω.sigma_pos hfTilde_proper hfTilde_closed hfTilde_strong g0
    have hsingleton :
        euclideanSubdifferentialAt (fun y : E ↦ (((fTilde∗) y).toReal)) g0 =
          {∇ (fun y : E ↦ (((fTilde∗) y).toReal)) g0} :=
      euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
        hconv_primal hdiff_primal
    constructor
    · intro hstep
      have hsub_strong :
          toDualMap ℝ E g0 ∈ ∂ₛ fTilde(xNext) := by
        -- First pass through the already-established mirror-step/subgradient bridge.
        simpa [fTilde, g0] using
          (mirror_descent_step_isMinOn_iff_dual_mem_subdifferential_add_indicator
            (ω := ω) (C := C) (σ := σ) (xk := xk) (xNext := xNext)
            (gradf := gradf) (t := t) hω hxk).1 hstep
      have hsub_owner :
          (toDualMap ℝ E g0 : Module.Dual ℝ E) ∈ ∂ fTilde(xNext) := by
        simpa [mem_strongDualSubdifferential] using hsub_strong
      have heval_conj :
          Module.Dual.eval ℝ E xNext ∈
            ∂ (conjugate_function fTilde)(toDualMap ℝ E g0) :=
        eval_mem_subdifferential_conjugate_of_mem_subdifferential
          hfTilde_proper hsub_owner
      have hsub_primal :
          xNext ∈ euclideanSubdifferentialAt (fun y : E ↦ (((fTilde∗) y).toReal)) g0 :=
        (evalMemSubdifferentialConjugate_iff_memEuclideanSubdifferentialAt_primalConjugate
          hfTilde_proper hfTilde_closed hfTilde_convex hfinite_primal).1 heval_conj
      -- Proposition 3.14 collapses the Euclidean subdifferential to the conjugate gradient.
      simpa [fTilde, g0, hsingleton] using hsub_primal
    · intro hxEq
      have hxEq' :
          xNext = ∇ (fun y : E ↦ (((fTilde∗) y).toReal)) g0 := by
        simpa [fTilde, g0] using hxEq
      have hsub_primal :
          xNext ∈ euclideanSubdifferentialAt (fun y : E ↦ (((fTilde∗) y).toReal)) g0 := by
        -- Route correction: use the singleton-gradient description before returning to
        -- `∂ (ω + δ_C)`.
        rw [hsingleton]
        simp [hxEq']
      have heval_conj :
          Module.Dual.eval ℝ E xNext ∈
            ∂ (conjugate_function fTilde)(toDualMap ℝ E g0) :=
        (evalMemSubdifferentialConjugate_iff_memEuclideanSubdifferentialAt_primalConjugate
          hfTilde_proper hfTilde_closed hfTilde_convex hfinite_primal).2 hsub_primal
      have hsub_owner :
          (toDualMap ℝ E g0 : Module.Dual ℝ E) ∈ ∂ fTilde(xNext) :=
        mem_subdifferential_of_eval_mem_subdifferential_conjugate
          hfTilde_proper hfTilde_closed hfTilde_convex heval_conj
      have hsub_strong :
          toDualMap ℝ E g0 ∈ ∂ₛ fTilde(xNext) := by
        simpa [mem_strongDualSubdifferential] using hsub_owner
      -- Return to the source-facing mirror-step owner using the same bridge in reverse.
      exact
        (mirror_descent_step_isMinOn_iff_dual_mem_subdifferential_add_indicator
          (ω := ω) (C := C) (σ := σ) (xk := xk) (xNext := xNext)
          (gradf := gradf) (t := t) hω hxk).2
          (by simpa [fTilde, g0] using hsub_strong)

end
