/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.12 is `source-facing` in the chapter Fenchel-conjugacy API. Its owner declarations
are already upstream: `IsProperExtendedRealFunction` and `is_convex_function` from Chapter 2,
the notation owner `∂ f(x)` from Chapter 3, `conjugate_function` from Chapter 4, and the bridge/view
theorems `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`,
`conjugate_function_eq_iff_isMaxOn_pairing_sub_function`, and
`self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex` from the preceding theorem
files. The only extra view language used here is Mathlib's `IsMaxOn`/`IsMinOn` over `Set.univ`, so
this file states only the textbook argmax/argmin characterizations on top of those owners instead
of introducing parallel local set wrappers.

The nonempty-effective-domain part of properness is semantically active for parts (1) and (3):
without it, `f ≡ ⊤` gives an empty subdifferential `∂ f(x)` but every dual vector is an
argmax/minimizer on the right-hand side. For parts (2) and (4), properness is also semantically
active because the
owner bridge
`pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`
requires `IsProperExtendedRealFunction f`: if `f ≡ ⊥`, then `∂ (conjugate_function f)(y)` is empty
while the primal argmax/image set is nonempty. Lower semicontinuity and convexity are still needed
there to identify `f**` with `f`. -/

recall IsProperExtendedRealFunction
recall is_convex_function
recall subdifferential
recall conjugate_function
recall IsMaxOn
recall IsMinOn

/-- Helper for Theorem 4.12: `y ∈ ∂ f(x)` is equivalent to `y` maximizing
`y' ↦ y' x - f*(y')` on the whole dual space. -/
lemma mem_subdifferential_iff_isMaxOn_affine_minus_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (x : E) (y : Module.Dual ℝ E) :
    y ∈ ∂ f(x) ↔
      IsMaxOn (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y := by
  have hyx_ne_top : (y x : EReal) ≠ ⊤ := EReal.coe_ne_top (y x)
  have hconj_ne_bot : conjugate_function f y ≠ ⊥ :=
    conjugateFunctionNeBot_ofProper f hf_proper y
  have hpair :
      y ∈ ∂ f(x) ↔ (y x : EReal) = f x + conjugate_function f y :=
    (pairing_eq_add_conjugate_iff_mem_subdifferential_of_proper f hf_proper x y).symm
  have hsub :
      (y x : EReal) = f x + conjugate_function f y ↔
        f x = (y x : EReal) - conjugate_function f y :=
    eq_add_iff_left_eq_sub_of_ne_bot (hf_proper.ne_bot x) hconj_ne_bot hyx_ne_top
  -- Chain the Fenchel--Young membership criterion with the dual argmax characterization.
  exact hpair.trans <|
    hsub.trans <|
      (self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex
        f hf_proper hf_closed hf_convex x y)

/-- Helper for Theorem 4.12: on `Set.univ`, maximizing the negation of an objective is equivalent
to minimizing the original objective. -/
lemma isMaxOn_univ_neg_iff_isMinOn_univ
    {X : Type*} (φ : X → EReal) (x : X) :
    IsMaxOn (fun z ↦ -φ z) Set.univ x ↔ IsMinOn φ Set.univ x := by
  -- Unfold both whole-space extremality predicates and compare them pointwise by negation.
  rw [isMaxOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx u
    exact EReal.neg_le_neg_iff.1 (hx u)
  · intro hx u
    exact EReal.neg_le_neg_iff.2 (hx u)

-- Proof sketch: combine the Fenchel--Young equality characterization of `y ∈ ∂f(x)` with the
-- biconjugate identity for proper closed convex functions and rewrite the resulting attainment
-- statement using `IsMaxOn ... Set.univ`.
/-- Theorem 4.12 (1): for a proper closed convex extended-real-valued function, the
subdifferential at `x` is exactly the set of dual vectors maximizing `y' ↦ y' x - f*(y')`. -/
theorem subdifferential_eq_argmax_affine_minus_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    ∂ f(x) =
      {y | IsMaxOn (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y} := by
  ext y
  -- Reduce the set equality to the pointwise Fenchel--Young/argmax bridge.
  exact
    mem_subdifferential_iff_isMaxOn_affine_minus_conjugate
      f hf_proper hf_closed hf_convex x y

-- Proof sketch: specialize part (1) at `x = 0`; the affine term `y 0` vanishes, so maximizing
-- `y ↦ y 0 - f*(y)` is exactly minimizing `f*`.
/-- Theorem 4.12 (3): for a proper closed convex extended-real-valued function, the
subdifferential at the origin is exactly the minimizer set of the conjugate `f*`. -/
theorem subdifferential_zero_eq_argmin_conjugate
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    ∂ f(0) =
      {y | IsMinOn (conjugate_function f) Set.univ y} := by
  rw [subdifferential_eq_argmax_affine_minus_conjugate f hf_proper hf_closed hf_convex (0 : E)]
  ext y
  -- At the origin, the affine-minus-conjugate objective is just `-f*`.
  simpa using
    (isMaxOn_univ_neg_iff_isMinOn_univ (φ := conjugate_function f) (x := y))

-- Proof sketch: use the conjugate-side Fenchel--Young equality characterization from
-- `pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate`, then rewrite the primal
-- attainment statement with `conjugate_function_eq_iff_isMaxOn_pairing_sub_function`. Properness
-- is semantically active through the owner bridge on the conjugate side, while closedness and
-- convexity are what identify `f**` with `f`.
/-- Theorem 4.12 (2): for a proper closed convex extended-real-valued function,
the subdifferential of the conjugate at `y` is the image under the canonical double-dual map
`Module.Dual.eval ℝ E` of
the maximizers of `x' ↦ y x' - f(x')`. -/
theorem subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (y : Module.Dual ℝ E) :
    ∂ (conjugate_function f)(y) =
      (Module.Dual.eval ℝ E) ''
        {x | IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x} := by
  have hpointwise :
      ∀ x : E,
        Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) ↔
          IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := by
    intro x
    have hyx_ne_top : (y x : EReal) ≠ ⊤ := EReal.coe_ne_top (y x)
    have hconj_ne_bot : conjugate_function f y ≠ ⊥ :=
      conjugateFunctionNeBot_ofProper f hf_proper y
    have hpair :
        Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) ↔
          (y x : EReal) = f x + conjugate_function f y :=
      (pairing_eq_add_conjugate_iff_eval_mem_subdifferential_conjugate
        f hf_proper hf_closed hf_convex x y).symm
    have hsub :
        (y x : EReal) = f x + conjugate_function f y ↔
          conjugate_function f y = (y x : EReal) - f x := by
      -- Normalize the Fenchel--Young equality into the primal argmax shape.
      simpa [add_comm] using
        (eq_add_iff_left_eq_sub_of_ne_bot hconj_ne_bot (hf_proper.ne_bot x) hyx_ne_top)
    exact hpair.trans <|
      hsub.trans <|
        (conjugate_function_eq_iff_isMaxOn_pairing_sub_function f x y)
  ext z
  constructor
  · intro hz
    let x : E := (Module.evalEquiv ℝ E).symm z
    have hz_eval : Module.Dual.eval ℝ E x = z := by
      -- Rewrite the canonical bidual equivalence back to the evaluation-map spelling.
      change (Module.evalEquiv ℝ E) ((Module.evalEquiv ℝ E).symm z) = z
      exact (Module.evalEquiv ℝ E).apply_symm_apply z
    have hx : IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := by
      -- Route correction: move the double-dual point back to `E`
      -- before applying the pointwise bridge.
      exact (hpointwise x).mp (by simpa [hz_eval] using hz)
    exact ⟨x, hx, hz_eval⟩
  · rintro ⟨x, hx, rfl⟩
    -- Image witnesses are sent back to the subdifferential by the same pointwise bridge.
    exact (hpointwise x).mpr hx

/-- Companion theorem for Theorem 4.12 (2): the canonical double-dual image of `x` lies in
`∂(f∗)(y)` exactly when `x` maximizes `x' ↦ y x' - f(x')` on the whole space. -/
theorem eval_mem_subdifferential_conjugate_iff_isMaxOn_affine_minus
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (y : Module.Dual ℝ E) (x : E) :
    Module.Dual.eval ℝ E x ∈ ∂ (conjugate_function f)(y) ↔
      IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := by
  rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    f hf_proper hf_closed hf_convex y]
  constructor
  · rintro ⟨x', hx', hEval⟩
    have hxEq : x' = x := Module.eval_apply_injective ℝ hEval
    simpa [hxEq] using hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

-- Proof sketch: specialize part (2) at the zero dual vector; the affine objective becomes
-- `x ↦ -f x`, so its maximizers are exactly the minimizers of `f`, then transport them to `E**`
-- by `Module.Dual.eval ℝ E`.
/-- Theorem 4.12 (4): for a proper closed convex extended-real-valued function,
at the zero dual vector the subdifferential of the conjugate is the canonical double-dual image
of the minimizer set of `f`. -/
theorem subdifferential_conjugate_zero_eq_eval_image_argmin
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    ∂ (conjugate_function f)(0) =
      (Module.Dual.eval ℝ E) '' {x | IsMinOn f Set.univ x} := by
  rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
    f hf_proper hf_closed hf_convex (0 : Module.Dual ℝ E)]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    -- At the zero dual vector, maximizing `x ↦ -f x` is the same as minimizing `f`.
    exact
      (isMaxOn_univ_neg_iff_isMinOn_univ (φ := f) (x := x)).mp
        (by simpa using hx)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    -- Convert the minimizer back into the corresponding maximizer of the negated objective.
    simpa using
      (isMaxOn_univ_neg_iff_isMinOn_univ (φ := f) (x := x)).mpr hx

end
