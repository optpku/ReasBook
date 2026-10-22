/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid V] [Module ℝ V]

/-- Helper for Theorem 2.7: a strict upper bound on the fiber infimum gives a fiber point below
that bound. -/
lemma exists_fiber_lt_of_sInf_range_lt [Nonempty V]
    {f : E × V → EReal} {x : E} {a : EReal}
    (h : sInf (Set.range (fun y : V ↦ f (x, y))) < a) :
    ∃ y : V, f (x, y) < a := by
  -- Convert the strict `sInf` bound into an actual fiber witness using the standard `csInf` API.
  obtain ⟨z, hzmem, hza⟩ := exists_lt_of_csInf_lt
    (s := Set.range (fun y : V ↦ f (x, y)))
    (Set.range_nonempty _)
    h
  rcases hzmem with ⟨y, rfl⟩
  exact ⟨y, hza⟩

/-- Helper for Theorem 2.7: bounds by `r + ε` for every positive `ε` imply a bound by `r`. -/
lemma ereal_le_coe_of_forall_pos_add {z : EReal} {r : ℝ}
    (h : ∀ ε > 0, z ≤ ((r + ε : ℝ) : EReal)) : z ≤ (r : EReal) := by
  -- Separate `z` from `r` by a real number and use the hypothesis with that positive gap.
  by_contra hzr
  have hrz : (r : EReal) < z := lt_of_not_ge hzr
  obtain ⟨s, hrs, hsz⟩ := EReal.exists_between_coe_real hrz
  have hrs' : r < s := EReal.coe_lt_coe_iff.mp hrs
  have hsEq : r + (s - r) = s := by ring
  have hzle : z ≤ (s : EReal) := by
    simpa [hsEq] using h (s - r) (sub_pos.mpr hrs')
  exact (not_le.mpr hsz) hzle

/-- Helper for Theorem 2.7: an `ε`-approximate pair of fiber minimizers yields an
`ε`-approximate convexity bound for the partial infimum. -/
lemma partialInf_combo_le_addEps_of_epigraph [Nonempty V]
    {f : E × V → EReal} (hf : is_convex_function f)
    {x₁ x₂ : E} {r₁ r₂ a b ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hε : 0 < ε)
    (hx₁ : sInf (Set.range (fun y : V ↦ f (x₁, y))) ≤ (r₁ : EReal))
    (hx₂ : sInf (Set.range (fun y : V ↦ f (x₂, y))) ≤ (r₂ : EReal)) :
    sInf (Set.range (fun y : V ↦ f (a • x₁ + b • x₂, y)))
      ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
  -- Upgrade the endpoint epigraph bounds to strict `rᵢ + ε` bounds so that `csInf` gives witnesses.
  have hx₁lt : sInf (Set.range (fun y : V ↦ f (x₁, y))) < ((r₁ + ε : ℝ) : EReal) := by
    exact lt_of_le_of_lt hx₁ (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r₁ hε))
  have hx₂lt : sInf (Set.range (fun y : V ↦ f (x₂, y))) < ((r₂ + ε : ℝ) : EReal) := by
    exact lt_of_le_of_lt hx₂ (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r₂ hε))
  obtain ⟨y₁, hy₁⟩ := exists_fiber_lt_of_sInf_range_lt hx₁lt
  obtain ⟨y₂, hy₂⟩ := exists_fiber_lt_of_sInf_range_lt hx₂lt
  have hfepi : Convex ℝ {p : (E × V) × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hf
  have hmem₁ :
      ((((x₁, y₁) : E × V), r₁ + ε) : (E × V) × ℝ) ∈ {p : (E × V) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact le_of_lt hy₁
  have hmem₂ :
      ((((x₂, y₂) : E × V), r₂ + ε) : (E × V) × ℝ) ∈ {p : (E × V) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact le_of_lt hy₂
  -- Convexity of the epigraph of `f` controls the convex combination of the approximate minimizers.
  have hvalue :
      f (a • x₁ + b • x₂, a • y₁ + b • y₂)
        ≤ ((a * (r₁ + ε) + b * (r₂ + ε) : ℝ) : EReal) := by
    simpa using (convex_iff_add_mem.mp hfepi) hmem₁ hmem₂ ha hb hab
  have hsInf :
      sInf (Set.range (fun y : V ↦ f (a • x₁ + b • x₂, y)))
        ≤ f (a • x₁ + b • x₂, a • y₁ + b • y₂) := by
    exact sInf_le (Set.mem_range_self (a • y₁ + b • y₂))
  have hring : a * (r₁ + ε) + b * (r₂ + ε) = a * r₁ + b * r₂ + ε := by
    nlinarith [hab]
  have hvalue' :
      f (a • x₁ + b • x₂, a • y₁ + b • y₂) ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
    rwa [hring] at hvalue
  exact hsInf.trans hvalue'

/-- Theorem 2.7: convexity is preserved under partial minimization. In Lean, the source value
function `x ↦ inf_y f (x, y)` is realized as
`x ↦ sInf (Set.range (fun y : V ↦ f (x, y)))`. -/
theorem partial_infimum_is_convex_function
    {f : E × V → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ sInf (Set.range (fun y : V ↦ f (x, y)))) := by
  rw [is_convex_function_iff_convex_real_epigraph]
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    rw [convex_iff_add_mem]
    intro p₁ hp₁ p₂ hp₂ a b ha hb hab
    rcases p₁ with ⟨x₁, r₁⟩
    rcases p₂ with ⟨x₂, r₂⟩
    -- Route correction: the partial infimum need not be attained, so we work with
    -- `ε`-approximate fiber minimizers and then close by letting `ε → 0`.
    have happrox : ∀ ε > 0,
        sInf (Set.range (fun y : V ↦ f (a • x₁ + b • x₂, y)))
          ≤ ((a * r₁ + b * r₂ + ε : ℝ) : EReal) := by
      intro ε hε
      exact partialInf_combo_le_addEps_of_epigraph hf ha hb hab hε hp₁ hp₂
    exact ereal_le_coe_of_forall_pos_add happrox
  · have hIsEmpty : IsEmpty V := not_nonempty_iff.mp hV
    rw [convex_iff_add_mem]
    intro p₁ hp₁ p₂ hp₂ a b ha hb hab
    rcases p₁ with ⟨x₁, r₁⟩
    have hp₁' : sInf (Set.range (fun y : V ↦ f (x₁, y))) ≤ (r₁ : EReal) := hp₁
    -- If the fiber is empty, the partial infimum is `⊤`, so no real epigraph point can exist.
    have hsInfTop : sInf (Set.range (fun y : V ↦ f (x₁, y))) = (⊤ : EReal) := by
      rw [Set.range_eq_empty_iff.2 hIsEmpty, sInf_empty]
    have htop : (⊤ : EReal) ≤ (r₁ : EReal) := by
      simp [hsInfTop] at hp₁'
    exact (not_lt_of_ge htop (EReal.coe_lt_top r₁)).elim

/-- Companion rewriting of `partial_infimum_is_convex_function` in `iInf` notation. -/
theorem partial_iInf_is_convex_function
    {f : E × V → EReal} (hf : is_convex_function f) :
    is_convex_function (fun x ↦ ⨅ y : V, f (x, y)) := by
  simpa using partial_infimum_is_convex_function hf

end
