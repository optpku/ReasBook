/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

/- This item reuses the chapter owner `is_convex_function` from Definition 2.6 for convexity of
an extended-real-valued function. -/
recall is_convex_function

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Definition 2.7: under domainwise exclusion of `⊥`, the real epigraph
`{(x, r) | f x ≤ r}` agrees with the epigraph of the finite-valued restriction
`x ↦ (f x).toReal` on `effective_domain f`. -/
private theorem realEpigraph_eq_toRealEpigraphOnEffectiveDomain
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} =
      {p : E × ℝ | p.1 ∈ effective_domain f ∧ (f p.1).toReal ≤ p.2} := by
  ext p
  constructor
  · intro hp
    -- Any point below a real height is automatically in the effective domain.
    have hp_dom : p.1 ∈ effective_domain f := by
      refine mem_effective_domain.mpr ?_
      exact lt_of_le_of_lt hp (by simp)
    refine ⟨hp_dom, ?_⟩
    -- Once `⊥` and `⊤` are excluded, `toReal` preserves the order relation.
    exact EReal.toReal_le_toReal hp (h_ne_bot _ hp_dom) (by simp)
  · rintro ⟨hp_dom, hp_toReal⟩
    have hp_top : f p.1 ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hp_dom)
    -- Rewrite `f p.1` back to the real coercion of its `toReal` value.
    calc
      f p.1 = (((f p.1).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal hp_top (h_ne_bot _ hp_dom)
      _ ≤ (p.2 : EReal) := EReal.coe_le_coe hp_toReal

omit [AddCommMonoid E] [Module ℝ E] in
/-- Helper for Definition 2.7: on the effective domain, the weighted extended-real value is the
coercion of the corresponding weighted real combination of `toReal` values. -/
private theorem weightedValue_eq_coe_toRealCombo
    {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    (h_ne_bot : ∀ z ∈ effective_domain f, f z ≠ ⊥) {t : ℝ} :
    (t : EReal) * f x + (1 - t : EReal) * f y =
      ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
  have hx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  have hy_top : f y ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hy)
  have hsub : (1 - t : EReal) = ((1 - t : ℝ) : EReal) := by
    norm_num
  -- Replace the `EReal` values by coerced real values, then combine the real arithmetic once.
  calc
    (t : EReal) * f x + (1 - t : EReal) * f y =
        (t : EReal) * (((f x).toReal : ℝ) : EReal) +
          (1 - t : EReal) * (((f y).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal hx_top (h_ne_bot _ hx), EReal.coe_toReal hy_top (h_ne_bot _ hy)]
    _ = (((t * (f x).toReal : ℝ) : EReal) +
          (((1 - t) * (f y).toReal : ℝ) : EReal)) := by
      rw [hsub, EReal.coe_mul, EReal.coe_mul]
    _ = ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_add]

/-- Helper for Definition 2.7: properness lets the `toReal` convexity bridge be used before the
public companion theorem is introduced below. -/
private theorem isConvexFunction_iff_convexOnToRealOfProper
    [IsProperExtendedRealFunction f] :
    is_convex_function f ↔ ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := by
  -- Properness supplies the domainwise `⊥` exclusion needed for the epigraph identification.
  rw [is_convex_function_iff_convex_real_epigraph, convexOn_iff_convex_epigraph]
  rw [realEpigraph_eq_toRealEpigraphOnEffectiveDomain (f := f)
    (fun x _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) x)]

/-- Definition 2.7: for a proper extended-real-valued function, convexity is equivalent to the
two-point Jensen inequality along every segment between points of `effective_domain f` with weight
in `[0, 1]`. -/
theorem is_convex_function_iff_segment_ineq [IsProperExtendedRealFunction f] :
    is_convex_function f ↔
      ∀ x ∈ effective_domain f, ∀ y ∈ effective_domain f, ∀ {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤ (t : EReal) * f x + (1 - t : EReal) * f y := by
  constructor
  · intro hf x hx y hy t ht
    have hconv :
        ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
      (isConvexFunction_iff_convexOnToRealOfProper (f := f)).mp hf
    have hsum : t + (1 - t) = 1 := by
      linarith
    have hz : t • x + (1 - t) • y ∈ effective_domain f :=
      hconv.1 hx hy ht.1 (sub_nonneg.mpr ht.2) hsum
    have htoReal :
        (f (t • x + (1 - t) • y)).toReal ≤
          t * (f x).toReal + (1 - t) * (f y).toReal :=
      hconv.2 hx hy ht.1 (sub_nonneg.mpr ht.2) hsum
    -- Translate the real-valued Jensen inequality back into `EReal`.
    calc
      f (t • x + (1 - t) • y) =
          (((f (t • x + (1 - t) • y)).toReal : ℝ) : EReal) := by
        symm
        exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz))
          (IsProperExtendedRealFunction.ne_bot (f := f) _)
      _ ≤ ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) :=
        EReal.coe_le_coe htoReal
      _ = (t : EReal) * f x + (1 - t : EReal) * f y := by
        symm
        exact weightedValue_eq_coe_toRealCombo (f := f) hx hy
          (fun z _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) z)
  · intro hseg
    -- Route correction: the reverse implication is rebuilt through `ConvexOn` on the finite-valued
    -- restriction, then transported back via the properness bridge.
    refine (isConvexFunction_iff_convexOnToRealOfProper (f := f)).mpr ?_
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      have hab' : 1 - a = b := by
        linarith
      have ht : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
      have hsegE :
          f (a • x + (1 - a) • y) ≤
            (a : EReal) * f x + (1 - a : EReal) * f y :=
        hseg x hx y hy ht
      have hweighted_eq :
          (a : EReal) * f x + (1 - a : EReal) * f y =
            ((a * (f x).toReal + (1 - a) * (f y).toReal : ℝ) : EReal) :=
        weightedValue_eq_coe_toRealCombo (f := f) hx hy
          (fun z _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) z) (t := a)
      have hweighted_top :
          (a : EReal) * f x + (1 - a : EReal) * f y < ⊤ := by
        rw [hweighted_eq]
        exact EReal.coe_lt_top _
      -- The right-hand side is finite, so the segment point stays in the effective domain.
      have hz :
          a • x + (1 - a) • y ∈ effective_domain f := by
        refine mem_effective_domain.mpr ?_
        exact lt_of_le_of_lt hsegE hweighted_top
      simpa [hab'] using hz
    · intro x hx y hy a b ha hb hab
      have hab' : 1 - a = b := by
        linarith
      have ht : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, by linarith⟩
      have hsegE :
          f (a • x + (1 - a) • y) ≤
            (a : EReal) * f x + (1 - a : EReal) * f y :=
        hseg x hx y hy ht
      have hweighted_eq :
          (a : EReal) * f x + (1 - a : EReal) * f y =
            ((a * (f x).toReal + (1 - a) * (f y).toReal : ℝ) : EReal) :=
        weightedValue_eq_coe_toRealCombo (f := f) hx hy
          (fun z _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) z) (t := a)
      have hweighted_ne_top :
          (a : EReal) * f x + (1 - a : EReal) * f y ≠ ⊤ := by
        rw [hweighted_eq]
        exact (EReal.coe_lt_top _).ne
      have hweighted_toReal :
          ((a : EReal) * f x + (1 - a : EReal) * f y).toReal =
            a * (f x).toReal + (1 - a) * (f y).toReal := by
        simpa using congrArg EReal.toReal hweighted_eq
      have htoReal :
          (f (a • x + (1 - a) • y)).toReal ≤
            a * (f x).toReal + (1 - a) * (f y).toReal :=
        by
          -- Convert the `EReal` Jensen inequality to the real one after normalizing the RHS once.
          simpa [hweighted_toReal] using
            EReal.toReal_le_toReal hsegE
              (IsProperExtendedRealFunction.ne_bot (f := f) _)
              hweighted_ne_top
      simpa [hab'] using htoReal

namespace is_convex_function

/-- Callable companion to `is_convex_function_iff_segment_ineq`: a proper convex
extended-real-valued function satisfies the textbook two-point Jensen inequality on its effective
domain. -/
theorem segment_ineq [IsProperExtendedRealFunction f] (hf : is_convex_function f)
    {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (t • x + (1 - t) • y) ≤ (t : EReal) * f x + (1 - t : EReal) * f y :=
  (is_convex_function_iff_segment_ineq.mp hf) x hx y hy ht

end is_convex_function

-- Proof sketch: identify the real epigraph from Definition 2.6 with the epigraph of the finite
-- restriction `x ↦ (f x).toReal` on `effective_domain f`; the local hypothesis `h_ne_bot` rules
-- out `-∞` on the domain, and membership in `effective_domain f` rules out `∞`, so
-- `convexOn_iff_convex_epigraph` applies to a genuine real-valued restriction.
/-- Companion bridge: if an extended-real-valued function never takes the value `-∞` on its
effective domain, then the source Jensen formulation is equivalent to convexity of the finite-valued
restriction `x ↦ (f x).toReal` on that domain. -/
theorem is_convex_function_iff_convexOn_toReal
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    is_convex_function f ↔ ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := by
  -- Rewrite both notions into convexity of the same epigraph set.
  rw [is_convex_function_iff_convex_real_epigraph, convexOn_iff_convex_epigraph]
  rw [realEpigraph_eq_toRealEpigraphOnEffectiveDomain (f := f) h_ne_bot]

/-- For a proper extended-real-valued function, the `toReal` bridge needs no extra `-∞`
hypothesis: properness already rules out `⊥` everywhere. -/
theorem is_convex_function_iff_convexOn_toReal_of_proper (f : E → EReal)
    [IsProperExtendedRealFunction f] :
    is_convex_function f ↔ ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := by
  -- Properness supplies the missing `⊥` exclusion required by the generic bridge.
  simpa using is_convex_function_iff_convexOn_toReal (f := f)
    (fun x _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) x)

/-- If a convex extended-real-valued function never takes the value `-∞` on its effective domain,
then its finite-valued restriction is convex on that domain. -/
theorem convexOn_toReal_of_is_convex_function (hf : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := by
  -- This is the forward direction of the bridge already proved above.
  exact (is_convex_function_iff_convexOn_toReal (f := f) h_ne_bot).mp hf

/-- If a proper extended-real-valued function is convex, then its finite-valued restriction is
convex on its effective domain. -/
theorem convexOn_toReal_of_is_convex_function_of_proper (f : E → EReal)
    [IsProperExtendedRealFunction f] (hf : is_convex_function f) :
    ConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) := by
  -- Properness turns the generic bridge into a direct equivalence.
  exact (is_convex_function_iff_convexOn_toReal_of_proper (f := f)).mp hf

-- Proof sketch: the convexity of the effective domain is the set component of
-- the real epigraph under the first-coordinate projection.
/-- If an extended-real-valued function is convex, then its effective domain is a convex set. -/
theorem effective_domain_convex_of_is_convex_function (hf : is_convex_function f) :
    Convex ℝ (effective_domain f) := by
  have hf_epi :
      Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hf
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  have hx_epi : (x, (f x).toReal) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact EReal.le_coe_toReal (ne_of_lt (mem_effective_domain.mp hx))
  have hy_epi : (y, (f y).toReal) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact EReal.le_coe_toReal (ne_of_lt (mem_effective_domain.mp hy))
  -- Project the convexity of the epigraph onto the first coordinate.
  have hcombo :
      f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
    simpa using (convex_iff_add_mem.mp hf_epi) hx_epi hy_epi ha hb hab
  refine mem_effective_domain.mpr ?_
  have htop : ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) < ⊤ := by
    exact EReal.coe_lt_top _
  exact lt_of_le_of_lt hcombo htop

-- Proof sketch: apply `effective_domain_convex_of_is_convex_function` to `hx`, `hy`, and the
-- bounds encoded by `ht`.
/-- If an extended-real-valued function is convex and finite at two points of its effective
domain, then it is also finite at every convex combination of those points with weight in `[0,
1]`. -/
theorem combo_mem_effective_domain_of_is_convex_function (hf : is_convex_function f)
    {x y : E} (hx : x ∈ effective_domain f)
    (hy : y ∈ effective_domain f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • x + (1 - t) • y ∈ effective_domain f := by
  have hconv : Convex ℝ (effective_domain f) :=
    effective_domain_convex_of_is_convex_function hf
  have hsum : t + (1 - t) = 1 := by
    linarith
  -- Apply convexity of the effective domain to the segment coefficients from `ht`.
  exact (convex_iff_add_mem.mp hconv) hx hy ht.1 (sub_nonneg.mpr ht.2) hsum

end
