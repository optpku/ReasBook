/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Theorem 2.8: a real-valued convex function stays convex after coercion to `EReal`.
-/
lemma toERealIsConvexFunction {ω : E → ℝ} (hω : ConvexOn ℝ Set.univ ω) :
    is_convex_function (Real.toEReal ∘ ω) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  -- Identify the `EReal` epigraph with the ordinary real epigraph of `ω`.
  have hEpigraph :
      {p : E × ℝ | (Real.toEReal ∘ ω) p.1 ≤ (p.2 : EReal)} =
        {p : E × ℝ | p.1 ∈ Set.univ ∧ ω p.1 ≤ p.2} := by
    ext p
    simp
  rw [hEpigraph]
  simpa using hω.convex_epigraph

/-- Helper for Theorem 2.8: a strict upper bound on the second-coordinate infimum produces an
actual second-coordinate witness below that bound. -/
lemma existsFiberLtOfSInfRangeLt {f : E × E → EReal} [Nonempty E] {x : E} {a : EReal}
    (h : sInf (Set.range (fun y : E ↦ f (x, y))) < a) :
    ∃ y : E, f (x, y) < a := by
  -- Convert the strict `sInf` inequality into a concrete fiber witness.
  obtain ⟨z, hzmem, hza⟩ := exists_lt_of_csInf_lt
    (s := Set.range (fun y : E ↦ f (x, y)))
    (Set.range_nonempty _)
    h
  rcases hzmem with ⟨y, rfl⟩
  exact ⟨y, hza⟩

/-- Helper for Theorem 2.8: if `z ≤ r + ε` for every `ε > 0`, then `z ≤ r`. -/
lemma erealLeCoeOfForallPosAdd {z : EReal} {r : ℝ}
    (h : ∀ ε > 0, z ≤ ((r + ε : ℝ) : EReal)) : z ≤ (r : EReal) := by
  -- Separate `z` from `r` by a real point and contradict the `ε`-family of bounds.
  by_contra hzr
  have hrz : (r : EReal) < z := lt_of_not_ge hzr
  obtain ⟨s, hrs, hsz⟩ := EReal.exists_between_coe_real hrz
  have hrs' : r < s := EReal.coe_lt_coe_iff.mp hrs
  have hsEq : r + (s - r) = s := by
    ring
  have hzle : z ≤ (s : EReal) := by
    simpa [hsEq] using h (s - r) (sub_pos.mpr hrs')
  exact (not_le.mpr hsz) hzle

/-- Helper for Theorem 2.8: `ε`-approximate minimizers in the second coordinate give an
`ε`-approximate convexity bound for the partial infimum. -/
lemma partialInfimumOnSecondComboLeAddEps {f : E × E → EReal} [Nonempty E]
    (hf : is_convex_function f) {x₁ x₂ : E} {r₁ r₂ a b ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hε : 0 < ε)
    (hx₁ : sInf (Set.range (fun y : E ↦ f (x₁, y))) ≤ (r₁ : EReal))
    (hx₂ : sInf (Set.range (fun y : E ↦ f (x₂, y))) ≤ (r₂ : EReal)) :
    sInf (Set.range (fun y : E ↦ f (a • x₁ + b • x₂, y)))
      ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
  -- Upgrade the endpoint bounds to strict inequalities so `csInf` gives fiber witnesses.
  have hx₁lt : sInf (Set.range (fun y : E ↦ f (x₁, y))) < ((r₁ + ε : ℝ) : EReal) := by
    exact lt_of_le_of_lt hx₁ (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r₁ hε))
  have hx₂lt : sInf (Set.range (fun y : E ↦ f (x₂, y))) < ((r₂ + ε : ℝ) : EReal) := by
    exact lt_of_le_of_lt hx₂ (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r₂ hε))
  obtain ⟨y₁, hy₁⟩ := existsFiberLtOfSInfRangeLt hx₁lt
  obtain ⟨y₂, hy₂⟩ := existsFiberLtOfSInfRangeLt hx₂lt
  have hfepi : Convex ℝ {p : (E × E) × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hf
  have hmem₁ :
      ((((x₁, y₁) : E × E), r₁ + ε) : (E × E) × ℝ) ∈
        {p : (E × E) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact le_of_lt hy₁
  have hmem₂ :
      ((((x₂, y₂) : E × E), r₂ + ε) : (E × E) × ℝ) ∈
        {p : (E × E) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact le_of_lt hy₂
  -- Convexity of the full epigraph controls the convex combination of approximate minimizers.
  have hvalue :
      f (a • x₁ + b • x₂, a • y₁ + b • y₂)
        ≤ ((a * (r₁ + ε) + b * (r₂ + ε) : ℝ) : EReal) := by
    simpa using (convex_iff_add_mem.mp hfepi) hmem₁ hmem₂ ha hb hab
  have hsInf :
      sInf (Set.range (fun y : E ↦ f (a • x₁ + b • x₂, y)))
        ≤ f (a • x₁ + b • x₂, a • y₁ + b • y₂) := by
    exact sInf_le (Set.mem_range_self (a • y₁ + b • y₂))
  have hring : a * (r₁ + ε) + b * (r₂ + ε) = a * r₁ + b * r₂ + ε := by
    nlinarith [hab]
  have hvalue' :
      f (a • x₁ + b • x₂, a • y₁ + b • y₂) ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
    rwa [hring] at hvalue
  exact hsInf.trans hvalue'

/-- Helper for Theorem 2.8: partial minimization in the second coordinate preserves convexity. -/
lemma partialInfimumOnSecondIsConvex {f : E × E → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ sInf (Set.range (fun y : E ↦ f (x, y)))) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    rw [convex_iff_add_mem]
    intro p₁ hp₁ p₂ hp₂ a b ha hb hab
    rcases p₁ with ⟨x₁, r₁⟩
    rcases p₂ with ⟨x₂, r₂⟩
    -- The second-coordinate infimum need not be attained, so work with `ε`-approximate minimizers.
    have happrox : ∀ ε > 0,
        sInf (Set.range (fun y : E ↦ f (a • x₁ + b • x₂, y)))
          ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
      intro ε hε
      exact partialInfimumOnSecondComboLeAddEps hf ha hb hab hε hp₁ hp₂
    exact erealLeCoeOfForallPosAdd happrox
  · have hIsEmpty : IsEmpty E := not_nonempty_iff.mp hE
    rw [convex_iff_add_mem]
    intro p₁ hp₁ p₂ hp₂ a b ha hb hab
    rcases p₁ with ⟨x₁, r₁⟩
    have hp₁' : sInf (Set.range (fun y : E ↦ f (x₁, y))) ≤ (r₁ : EReal) := hp₁
    -- If the fiber is empty, the partial infimum is `⊤`, so the real epigraph has no points.
    have hsInfTop : sInf (Set.range (fun y : E ↦ f (x₁, y))) = (⊤ : EReal) := by
      rw [Set.range_eq_empty_iff.2 hIsEmpty, sInf_empty]
    have htop : (⊤ : EReal) ≤ (r₁ : EReal) := by
      simp [hsInfTop] at hp₁'
    exact (not_lt_of_ge htop (EReal.coe_lt_top r₁)).elim

/-- Helper for Theorem 2.8: the `iInf` form of partial minimization in the second coordinate is
convex. -/
lemma partialIInfOnSecondIsConvex {f : E × E → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ ⨅ y : E, f (x, y)) := by
  simpa using partialInfimumOnSecondIsConvex hf

/-- Helper for Theorem 2.8: the joint kernel `(x, y) ↦ h₁ y + h₂.toEReal (x - y)` is convex once
the `h₁` and `h₂` factors are convex and `h₁` never attains `⊥`. -/
lemma infimalConvolutionKernelConvex (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_convex : is_convex_function h₁) (hh₂ : ConvexOn ℝ Set.univ h₂)
    (h₁_ne_bot : ∀ x, h₁ x ≠ ⊥) :
    is_convex_function (fun p : E × E ↦ h₁ p.2 + (Real.toEReal ∘ h₂) (p.1 - p.2)) := by
  -- Lift the real-valued factor to an extended-real convex function.
  have hh₂_convex : is_convex_function (Real.toEReal ∘ h₂) := toERealIsConvexFunction hh₂
  -- View `p ↦ h₁ p.2` as precomposition with the second projection.
  have hSecond : is_convex_function (fun p : E × E ↦ h₁ p.2) := by
    simpa using
      is_convex_function_precompose_linearMap_add hh₁_convex (LinearMap.snd ℝ E E) (0 : E)
  -- View `p ↦ h₂.toEReal (p.1 - p.2)` as precomposition with the difference map.
  have hDifference :
      is_convex_function (fun p : E × E ↦ (Real.toEReal ∘ h₂) (p.1 - p.2)) := by
    simpa using
      is_convex_function_precompose_linearMap_add hh₂_convex
        (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E) (0 : E)
  -- Combine the two convex factors pointwise.
  exact is_convex_function_pointwise_add hSecond hDifference
    (fun p ↦ h₁_ne_bot p.2) (fun p ↦ by simp)

/-- Helper for Theorem 2.8: if `h₁` takes the value `⊥` somewhere, then the infimal convolution is
everywhere `⊥`. -/
lemma infimalConvolution_eq_bot_of_exists_eq_bot (h₁ : E → EReal) (h₂ : E → ℝ)
    (u : E) (hu : h₁ u = ⊥) (x : E) :
    (h₁ □ (Real.toEReal ∘ h₂)) x = ⊥ := by
  -- Use the witness `u` in the defining infimum.
  rw [infimal_convolution_apply]
  apply le_antisymm
  · exact iInf_le_of_le u (by simpa [hu])
  · exact bot_le

/-- Helper for Theorem 2.8: if the effective domain is empty, then the function is constantly
`⊤`. -/
lemma forall_eq_top_of_not_effectiveDomain_nonempty (h₁ : E → EReal)
    (h_empty : ¬ (effective_domain h₁).Nonempty) :
    ∀ x, h₁ x = ⊤ := by
  intro x
  by_cases hx : h₁ x = ⊤
  · exact hx
  -- Any finite point would contradict emptiness of the effective domain.
  · have hx_mem : x ∈ effective_domain h₁ := by
      rw [mem_effective_domain]
      exact lt_top_iff_ne_top.mpr hx
    exact False.elim (h_empty ⟨x, hx_mem⟩)

-- Proof sketch: consider the jointly convex function `(x, y) ↦ h₁ y + h₂ (x - y)`, obtained by
-- combining the convexity of `h₁` with the convexity of `h₂` under the affine map `(x, y) ↦ x - y`;
-- then apply the partial-minimization theorem to the infimum over the second variable.
/-- Theorem 2.8: if `h₁` is a proper convex extended-real-valued function and `h₂` is a
real-valued convex function, then the infimal convolution
`h₁ □ h₂.toEReal` of `h₁` with the canonical extended-real lift of `h₂`
is convex. -/
theorem infimal_convolution_is_convex_of_proper (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_convex : is_convex_function h₁) (hh₂ : ConvexOn ℝ Set.univ h₂) :
    is_convex_function (h₁ □ (Real.toEReal ∘ h₂)) := by
  -- Build the jointly convex kernel from the source proof.
  have hKernel :
      is_convex_function (fun p : E × E ↦ h₁ p.2 + (Real.toEReal ∘ h₂) (p.1 - p.2)) :=
    infimalConvolutionKernelConvex h₁ h₂ hh₁_convex hh₂ hh₁_proper.ne_bot
  -- Apply partial minimization in the second variable and rewrite the result.
  simpa [infimal_convolution_apply] using
    partialIInfOnSecondIsConvex
      (f := fun p : E × E ↦ h₁ p.2 + (Real.toEReal ∘ h₂) (p.1 - p.2)) hKernel

/-- Companion form: the convexity conclusion for `h₁ □ h₂.toEReal`
does not use the properness assumption on `h₁`. -/
theorem infimal_convolution_is_convex (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_convex : is_convex_function h₁) (hh₂ : ConvexOn ℝ Set.univ h₂) :
    is_convex_function (h₁ □ (Real.toEReal ∘ h₂)) := by
  by_cases hBot : ∃ u, h₁ u = ⊥
  · rcases hBot with ⟨u, hu⟩
    -- Collapse the infimal convolution to the constant-bottom function.
    have hCollapse : (h₁ □ (Real.toEReal ∘ h₂) : E → EReal) = fun _ : E ↦ (⊥ : EReal) := by
      funext x
      exact infimalConvolution_eq_bot_of_exists_eq_bot h₁ h₂ u hu x
    rw [hCollapse, is_convex_function_iff_convex_real_epigraph]
    simpa using (convex_univ : Convex ℝ (Set.univ : Set (E × ℝ)))
  · by_cases hDomain : (effective_domain h₁).Nonempty
    · -- Recover properness from the nonempty domain and the absence of `⊥`.
      have hneBot : ∀ x, h₁ x ≠ ⊥ := by
        intro x hx
        exact hBot ⟨x, hx⟩
      have hProper : IsProperExtendedRealFunction h₁ := {
        ne_bot := hneBot
        effective_domain_nonempty := hDomain
      }
      exact infimal_convolution_is_convex_of_proper h₁ h₂ hProper hh₁_convex hh₂
    · -- Route correction: the remaining nonproper case is the constant-`⊤` branch.
      have hTop : ∀ x, h₁ x = ⊤ :=
        forall_eq_top_of_not_effectiveDomain_nonempty h₁ hDomain
      have hCollapse : (h₁ □ (Real.toEReal ∘ h₂) : E → EReal) = fun _ : E ↦ (⊤ : EReal) := by
        funext x
        rw [infimal_convolution_apply]
        simp [hTop]
      rw [hCollapse, is_convex_function_iff_convex_real_epigraph]
      simpa using (convex_empty : Convex ℝ (∅ : Set (E × ℝ)))

end

end
