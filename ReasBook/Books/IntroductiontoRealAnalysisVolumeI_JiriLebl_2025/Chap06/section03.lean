/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap04.section02

section Chap06
section Section03

open Filter
open scoped Topology

/-- Definition 6.3.1: For a set `U ⊆ ℝ²`, a function `F : U → ℝ` is continuous
at `(x, y) ∈ U` if for every sequence `(xₙ, yₙ)` of points of `U` with
`xₙ → x` and `yₙ → y`, we have `F (xₙ, yₙ) → F (x, y)`. It is continuous if it
is continuous at every point of `U`. -/
def sequentialContinuousAt (U : Set (ℝ × ℝ)) (F : U → ℝ) (p : U) : Prop :=
  ∀ s : ℕ → U,
    Tendsto (fun n => (s n).1.1) atTop (𝓝 p.1.1) →
      Tendsto (fun n => (s n).1.2) atTop (𝓝 p.1.2) →
        Tendsto (fun n => F (s n)) atTop (𝓝 (F p))

/-- Sequential continuity on `U` means sequential continuity at every point of
`U`. -/
def sequentialContinuous (U : Set (ℝ × ℝ)) (F : U → ℝ) : Prop :=
  ∀ p : U, sequentialContinuousAt U F p

-- Coordinatewise convergence for a sequence in a subtype of `ℝ × ℝ`.
lemma tendsto_subtype_coord_iff {U : Set (ℝ × ℝ)} {p : U} {s : ℕ → U} :
    Tendsto s atTop (𝓝 p) ↔
      Tendsto (fun n => (s n).1.1) atTop (𝓝 p.1.1) ∧
      Tendsto (fun n => (s n).1.2) atTop (𝓝 p.1.2) := by
  have h1 :
      Tendsto s atTop (𝓝 p) ↔
        Tendsto (fun n => (s n : ℝ × ℝ)) atTop (𝓝 (p : ℝ × ℝ)) := by
    simpa using (tendsto_subtype_rng (f := s) (l := atTop) (x := p))
  refine h1.trans ?_
  simpa using
    (Prod.tendsto_iff (seq := fun n => (s n : ℝ × ℝ)) (f := atTop) (p := (p : ℝ × ℝ)))

/-- On `ℝ × ℝ`, sequential continuity at a point agrees with the usual notion
of continuity at that point. -/
theorem sequentialContinuousAt_iff {U : Set (ℝ × ℝ)} {F : U → ℝ} {p : U} :
    sequentialContinuousAt U F p ↔ ContinuousAt F p := by
  constructor
  · intro h
    have hseq :
        ∀ s : ℕ → U, Tendsto s atTop (𝓝 p) →
          Tendsto (F ∘ s) atTop (𝓝 (F p)) := by
      intro s hs
      have hs' := (tendsto_subtype_coord_iff (s := s) (p := p)).1 hs
      simpa [Function.comp] using h s hs'.1 hs'.2
    have hcont : Tendsto F (𝓝 p) (𝓝 (F p)) :=
      (tendsto_nhds_iff_seq_tendsto).2 hseq
    simpa [ContinuousAt] using hcont
  · intro h s hs1 hs2
    have hs : Tendsto s atTop (𝓝 p) :=
      (tendsto_subtype_coord_iff (s := s) (p := p)).2 ⟨hs1, hs2⟩
    have hcont : Tendsto F (𝓝 p) (𝓝 (F p)) := by
      simpa [ContinuousAt] using h
    simpa [Function.comp] using hcont.comp hs

/-- Sequential continuity on `U` is equivalent to the usual notion of
continuity. -/
theorem sequentialContinuous_iff {U : Set (ℝ × ℝ)} {F : U → ℝ} :
    sequentialContinuous U F ↔ Continuous F := by
  constructor
  · intro h
    refine (continuous_iff_continuousAt).2 ?_
    intro p
    exact (sequentialContinuousAt_iff (U := U) (F := F) (p := p)).1 (h p)
  · intro h p
    have hcont : ContinuousAt F p := (continuous_iff_continuousAt).1 h p
    exact (sequentialContinuousAt_iff (U := U) (F := F) (p := p)).2 hcont

/-- Theorem 6.3.2 (Picard's theorem on existence and uniqueness). Let `I = [a,b]`
and `J = [c,d]` be closed bounded intervals with interiors `(a,b)` and `(c,d)`,
and take `(x₀, y₀) ∈ (a,b) × (c,d)`. If `F : ℝ → ℝ → ℝ` is continuous on
`I × J` and Lipschitz in the second variable with constant `L ≥ 0`, meaning
`|F x y - F x z| ≤ L * |y - z|` for all `x ∈ I` and `y z ∈ J`, then there is
`h > 0` with `[x₀ - h, x₀ + h] ⊆ I` and a unique differentiable function
`f : ℝ → ℝ` with values in `J` satisfying `f x₀ = y₀` and
`f' x = F x (f x)` on `[x₀ - h, x₀ + h]`. -/
theorem picard_existence_uniqueness
    {a b c d : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Ioo c d) (F : ℝ → ℝ → ℝ)
    (hcont :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d))
    (hLip :
      ∃ L, 0 ≤ L ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ∀ z ∈ Set.Icc c d,
        |F x y - F x z| ≤ L * |y - z|) :
    ∃ h, 0 < h ∧ Set.Icc (x₀ - h) (x₀ + h) ⊆ Set.Icc a b ∧
      ∃ f : ℝ → ℝ,
        ContinuousOn f (Set.Icc (x₀ - h) (x₀ + h)) ∧
        (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), f x ∈ Set.Icc c d) ∧
        (∀ x ∈ Set.Ioo (x₀ - h) (x₀ + h), HasDerivAt f (F x (f x)) x) ∧
        f x₀ = y₀ ∧
        ∀ g : ℝ → ℝ,
          ContinuousOn g (Set.Icc (x₀ - h) (x₀ + h)) →
          (∀ x ∈ Set.Icc (x₀ - h) (x₀ + h), g x ∈ Set.Icc c d) →
          (∀ x ∈ Set.Ioo (x₀ - h) (x₀ + h), HasDerivAt g (F x (g x)) x) →
          g x₀ = y₀ →
          Set.EqOn g f (Set.Icc (x₀ - h) (x₀ + h)) := by
  classical
  rcases hx₀ with ⟨hx₀a, hx₀b⟩
  rcases hy₀ with ⟨hy₀c, hy₀d⟩
  -- radius in y
  let α : ℝ := min (y₀ - c) (d - y₀) / 2
  have hyc' : 0 < y₀ - c := sub_pos.mpr hy₀c
  have hyd' : 0 < d - y₀ := sub_pos.mpr hy₀d
  have hαpos : 0 < α := by
    have : 0 < min (y₀ - c) (d - y₀) := lt_min hyc' hyd'
    have : 0 < min (y₀ - c) (d - y₀) / 2 := by nlinarith
    simpa [α] using this
  have hαnonneg : 0 ≤ α := le_of_lt hαpos
  have hball : Metric.closedBall y₀ α ⊆ Set.Icc c d := by
    intro y hy
    have hy' : |y - y₀| ≤ α := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hy
    have hy'' : y ≤ y₀ + α ∧ y₀ ≤ y + α := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (abs_sub_le_iff.1 hy')
    have hαle1 : α ≤ y₀ - c := by
      have hmin0 : 0 ≤ min (y₀ - c) (d - y₀) := le_of_lt (lt_min hyc' hyd')
      have : α ≤ min (y₀ - c) (d - y₀) := by
        simpa [α] using (half_le_self hmin0)
      exact this.trans (min_le_left _ _)
    have hαle2 : α ≤ d - y₀ := by
      have hmin0 : 0 ≤ min (y₀ - c) (d - y₀) := le_of_lt (lt_min hyc' hyd')
      have : α ≤ min (y₀ - c) (d - y₀) := by
        simpa [α] using (half_le_self hmin0)
      exact this.trans (min_le_right _ _)
    have hy_lower : y₀ - α ≤ y := by linarith [hy''.2]
    have hc : c ≤ y₀ - α := by linarith [hαle1]
    have hd : y₀ + α ≤ d := by linarith [hαle2]
    exact ⟨le_trans hc hy_lower, le_trans hy''.1 hd⟩
  -- a uniform bound on F on the big rectangle `I × J`
  have hs : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := (isCompact_Icc).prod (isCompact_Icc)
  rcases hs.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
  let M : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hM : ∀ p ∈ (Set.Icc a b ×ˢ Set.Icc c d), ‖F p.1 p.2‖ ≤ (M : ℝ) := by
    intro p hp
    have := hC p hp
    exact this.trans (le_max_left _ _)
  -- time radius inside `I`
  let hI : ℝ := min (x₀ - a) (b - x₀) / 2
  have hx₀a' : 0 < x₀ - a := sub_pos.mpr hx₀a
  have hx₀b' : 0 < b - x₀ := sub_pos.mpr hx₀b
  have hhIpos : 0 < hI := by
    have : 0 < min (x₀ - a) (b - x₀) := lt_min hx₀a' hx₀b'
    have : 0 < min (x₀ - a) (b - x₀) / 2 := by nlinarith
    simpa [hI] using this
  -- choose `h` small enough for both inclusion and `M * h ≤ α`
  let h : ℝ := min hI (α / ((M : ℝ) + 1))
  have hden : 0 < (M : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (show 0 ≤ (M : ℝ) from M.2) (by norm_num)
  have hpos : 0 < h := lt_min hhIpos (div_pos hαpos hden)
  have hIcc : Set.Icc (x₀ - h) (x₀ + h) ⊆ Set.Icc a b := by
    intro x hx
    have hh : h ≤ hI := min_le_left _ _
    have hmin0 : 0 ≤ min (x₀ - a) (b - x₀) := le_of_lt (lt_min hx₀a' hx₀b')
    have hhI1 : hI ≤ x₀ - a := by
      have : hI ≤ min (x₀ - a) (b - x₀) := by
        simpa [hI] using (half_le_self hmin0)
      exact this.trans (min_le_left _ _)
    have hhI2 : hI ≤ b - x₀ := by
      have : hI ≤ min (x₀ - a) (b - x₀) := by
        simpa [hI] using (half_le_self hmin0)
      exact this.trans (min_le_right _ _)
    have ha0 : a ≤ x₀ - h := by linarith [hh, hhI1]
    have hb0 : x₀ + h ≤ b := by linarith [hh, hhI2]
    exact ⟨le_trans ha0 hx.1, le_trans hx.2 hb0⟩
  have hMh : (M : ℝ) * h ≤ α := by
    have hle : h ≤ α / ((M : ℝ) + 1) := min_le_right _ _
    have hineq : (M : ℝ) * (α / ((M : ℝ) + 1)) ≤ α := by
      have hle' : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := by
        have : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
        exact (div_le_one hden).2 this
      calc
        (M : ℝ) * (α / ((M : ℝ) + 1)) = α * ((M : ℝ) / ((M : ℝ) + 1)) := by ring
        _ ≤ α * 1 := by gcongr
        _ = α := by ring
    have hM0 : 0 ≤ (M : ℝ) := M.2
    exact (mul_le_mul_of_nonneg_left hle hM0).trans hineq
  -- Build `IsPicardLindelof` on `[x₀-h, x₀+h]` with ball radius `α`
  let tmin : ℝ := x₀ - h
  let tmax : ℝ := x₀ + h
  have ht0 : x₀ ∈ Set.Icc tmin tmax := by
    constructor <;> linarith
  let t₀' : Set.Icc tmin tmax := ⟨x₀, ht0⟩
  let aRad : NNReal := ⟨α, hαnonneg⟩
  rcases hLip with ⟨L', hL'0, hL'⟩
  let K : NNReal := ⟨L', hL'0⟩
  have hsub_time : Set.Icc tmin tmax ⊆ Set.Icc a b := by
    simpa [tmin, tmax] using hIcc
  have hcont_small :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc tmin tmax ×ˢ Set.Icc c d) := by
    refine hcont.mono ?_
    intro p hp
    exact ⟨hsub_time hp.1, hp.2⟩
  have hf : IsPicardLindelof (fun t y => F t y) t₀' y₀ aRad 0 M K := by
    refine IsPicardLindelof.mk ?_ ?_ ?_ ?_
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro y hy z hz
      have ht' : t ∈ Set.Icc a b := hsub_time ht
      have hy' : y ∈ Set.Icc c d := by
        have : Metric.closedBall y₀ (aRad : ℝ) ⊆ Set.Icc c d := by
          simpa [aRad] using hball
        exact this hy
      have hz' : z ∈ Set.Icc c d := by
        have : Metric.closedBall y₀ (aRad : ℝ) ⊆ Set.Icc c d := by
          simpa [aRad] using hball
        exact this hz
      have hdist := hL' t ht' y hy' z hz'
      simpa [Real.dist_eq] using hdist
    · intro x hx
      have hx' : x ∈ Set.Icc c d := by
        have : Metric.closedBall y₀ (aRad : ℝ) ⊆ Set.Icc c d := by
          simpa [aRad] using hball
        exact this hx
      simpa using
        (ODE.continuousOn_comp (f := fun t y => F t y)
          (s := Set.Icc tmin tmax) (u := Set.Icc c d)
          (hf := hcont_small) (hα := (continuous_const.continuousOn))
          (hmem := by
            intro t ht
            exact hx'))
    · intro t ht x hx
      have ht' : t ∈ Set.Icc a b := hsub_time ht
      have hx' : x ∈ Set.Icc c d := by
        have : Metric.closedBall y₀ (aRad : ℝ) ⊆ Set.Icc c d := by
          simpa [aRad] using hball
        exact this hx
      have hp : (t, x) ∈ (Set.Icc a b ×ˢ Set.Icc c d) := ⟨ht', hx'⟩
      simpa using hM (t, x) hp
    · simpa [tmin, tmax, t₀', aRad] using hMh
  -- Construct the solution via the fixed point
  have hx_init : y₀ ∈ Metric.closedBall y₀ ((0 : NNReal) : ℝ) := by simp
  obtain ⟨αsol, hαsol⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx_init
  let f : ℝ → ℝ := αsol.compProj
  have hf0 : f x₀ = y₀ := by
    have hx0_mem : x₀ ∈ Set.Icc tmin tmax := ht0
    have hx0_comp : f x₀ = αsol ⟨x₀, hx0_mem⟩ := by
      simpa [f] using (ODE.FunSpace.compProj_of_mem (α := αsol) (t := x₀) hx0_mem)
    have hinit : αsol t₀' = y₀ := by
      have h :=
        congrArg (fun β => β t₀') (show ODE.FunSpace.next hf hx_init αsol = αsol from hαsol)
      simpa [ODE.FunSpace.next_apply₀] using h.symm
    simpa [t₀'] using (hx0_comp.trans hinit)
  have hf_derivWithin :
      ∀ t ∈ Set.Icc tmin tmax, HasDerivWithinAt f (F t (f t)) (Set.Icc tmin tmax) t := by
    intro t ht
    -- Copy mathlib proof of `exists_eq_forall_mem_Icc_hasDerivWithinAt`.
    simpa [f] using (by
      apply ODE.hasDerivWithinAt_picard_Icc t₀'.2 hf.continuousOn_uncurry
        αsol.continuous_compProj.continuousOn
        (fun _ ht' ↦ αsol.compProj_mem_closedBall hf.mul_max_le)
        y₀ ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hαsol]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply])
  have hf_deriv : ∀ t ∈ Set.Ioo tmin tmax, HasDerivAt f (F t (f t)) t := by
    intro t ht
    have hwithin := hf_derivWithin t (Set.Ioo_subset_Icc_self ht)
    exact hwithin.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hf_range : ∀ t ∈ Set.Icc tmin tmax, f t ∈ Set.Icc c d := by
    intro t ht
    have ht' : f t ∈ Metric.closedBall y₀ (aRad : ℝ) := by
      simpa [f] using (αsol.compProj_mem_closedBall hf.mul_max_le (t := t))
    have : Metric.closedBall y₀ (aRad : ℝ) ⊆ Set.Icc c d := by
      simpa [aRad] using hball
    exact this ht'
  -- package the result with uniqueness on `Set.Icc (x₀-h) (x₀+h)`
  refine ⟨h, hpos, ?_, ⟨f, ?_, ?_, ?_, hf0, ?_⟩⟩
  · simpa [tmin, tmax] using hIcc
  · -- continuity on `Set.Icc tmin tmax`
    have : Continuous f := by
      simpa [f] using αsol.continuous_compProj
    exact this.continuousOn
  · intro x hx
    exact hf_range x (by simpa [tmin, tmax] using hx)
  · intro x hx
    exact hf_deriv x hx
  · intro g hgcont hgrange hgderiv hg0
    have hv : ∀ t ∈ Set.Ioo tmin tmax, LipschitzOnWith K (fun y => F t y) (Set.Icc c d) := by
      intro t ht
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro y hy z hz
      have ht' : t ∈ Set.Icc a b := hsub_time (Set.Ioo_subset_Icc_self ht)
      have hdist := hL' t ht' y hy z hz
      simpa [Real.dist_eq] using hdist
    have ht0' : x₀ ∈ Set.Ioo tmin tmax := by
      constructor <;> linarith [hpos]
    have hfcont : ContinuousOn f (Set.Icc tmin tmax) := by
      have : Continuous f := by
        simpa [f] using αsol.continuous_compProj
      exact this.continuousOn
    have hfrange : ∀ t ∈ Set.Ioo tmin tmax, f t ∈ Set.Icc c d := by
      intro t ht
      exact hf_range t (Set.Ioo_subset_Icc_self ht)
    have hgrange' : ∀ t ∈ Set.Ioo tmin tmax, g t ∈ Set.Icc c d := by
      intro t ht
      exact hgrange t (Set.Ioo_subset_Icc_self ht)
    have hEqOn_fg : Set.EqOn f g (Set.Icc tmin tmax) := by
      simpa using
        (ODE_solution_unique_of_mem_Icc (v := fun t y => F t y) (s := fun _ => Set.Icc c d)
          (K := K) (hv := hv) (ht := ht0')
          (hf := hfcont) (hf' := hf_deriv) (hfs := hfrange)
          (hg := hgcont) (hg' := hgderiv) (hgs := hgrange')
          (heq := by simp [hf0, hg0]))
    intro x hx
    symm
    exact hEqOn_fg hx

/-- Example 6.3.3: Applying Picard's theorem to the initial value problem
`f' = f` with `f 0 = 1` (that is, `F x y = y`) produces some `h > 0` with
`h < 1/2` and a function `f : ℝ → ℝ` defined on `[-h, h]` such that
`f' x = f x` on that interval and `f 0 = 1`, and any other solution with the
same initial value agrees with `f` on `[-h, h]`. The function extends globally
as `exp`, so the exponential is the unique global solution with that initial
value. -/
lemma picard_exponential_example :
    ∃ h, 0 < h ∧ h < (1 / 2 : ℝ) ∧
      ∃ f : ℝ → ℝ,
        (∀ x ∈ Set.Icc (-h) h, HasDerivAt f (f x) x) ∧ f 0 = 1 ∧
          ∀ g : ℝ → ℝ,
            (∀ x ∈ Set.Icc (-h) h, HasDerivAt g (g x) x) ∧ g 0 = 1 →
              Set.EqOn g f (Set.Icc (-h) h) := by
  classical
  let F : ℝ → ℝ → ℝ := fun _ y => y
  have hx0 : (0 : ℝ) ∈ Set.Ioo (-1 / 2) (1 / 2) := by
    constructor <;> linarith
  have hy0 : (1 : ℝ) ∈ Set.Ioo (1 / 2) (3 / 2) := by
    constructor <;> linarith
  have hcont :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc (-1 / 2) (1 / 2) ×ˢ Set.Icc (1 / 2) (3 / 2)) := by
    dsimp [F]
    exact (continuousOn_snd :
      ContinuousOn (fun p : ℝ × ℝ => p.2)
        (Set.Icc (-1 / 2) (1 / 2) ×ˢ Set.Icc (1 / 2) (3 / 2)))
  have hLip :
      ∃ L, 0 ≤ L ∧ ∀ x ∈ Set.Icc (-1 / 2) (1 / 2),
        ∀ y ∈ Set.Icc (1 / 2) (3 / 2), ∀ z ∈ Set.Icc (1 / 2) (3 / 2),
          |F x y - F x z| ≤ L * |y - z| := by
    refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy z hz
    simp [F]
  obtain ⟨h0, h0pos, h0sub, f, hfcont, hfrange, hfderiv, hf0, huniq⟩ :=
    picard_existence_uniqueness (a := -1 / 2) (b := 1 / 2) (c := 1 / 2) (d := 3 / 2)
      (x₀ := 0) (y₀ := 1) hx0 hy0 F hcont hLip
  let h : ℝ := min (h0 / 2) (1 / 4)
  have hpos : 0 < h := by
    have h0pos' : 0 < h0 / 2 := by linarith
    have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
    exact lt_min h0pos' hquarter
  have hlt : h < (1 / 2 : ℝ) := by
    have hle : h ≤ (1 / 4 : ℝ) := min_le_right _ _
    linarith
  have hlt_h0 : h < h0 := by
    have hle : h ≤ h0 / 2 := min_le_left _ _
    have h0half : h0 / 2 < h0 := by linarith
    exact lt_of_le_of_lt hle h0half
  refine ⟨h, hpos, hlt, ?_⟩
  refine ⟨f, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 - h0) (0 + h0) := by
      have hx'' : x ∈ Set.Ioo (-h0) h0 := by
        have hneg : -h0 < -h := by linarith [hlt_h0]
        exact ⟨lt_of_lt_of_le hneg hx.1, lt_of_le_of_lt hx.2 hlt_h0⟩
      simpa using hx''
    simpa [F] using (hfderiv x hx')
  · refine ⟨hf0, ?_⟩
    intro g hg
    have hgderiv : ∀ x ∈ Set.Icc (-h) h, HasDerivAt g (g x) x := hg.1
    have hg0 : g 0 = 1 := hg.2
    have hcontg : ContinuousOn g (Set.Icc (-h) h) := by
      intro x hx
      exact (hgderiv x hx).continuousAt.continuousWithinAt
    have hcontf : ContinuousOn f (Set.Icc (-h) h) := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 - h0) (0 + h0) := by
        have hx'' : x ∈ Set.Ioo (-h0) h0 := by
          have hneg : -h0 < -h := by linarith [hlt_h0]
          exact ⟨lt_of_lt_of_le hneg hx.1, lt_of_le_of_lt hx.2 hlt_h0⟩
        simpa using hx''
      have hderiv : HasDerivAt f (f x) x := by
        simpa [F] using (hfderiv x hx')
      exact hderiv.continuousAt.continuousWithinAt
    have hEqOn : Set.EqOn g f (Set.Icc (-h) h) := by
      have hv :
          ∀ t : ℝ, t ∈ Set.Ioo (-h) h →
            LipschitzOnWith (1 : NNReal) (fun y : ℝ => y) (Set.univ : Set ℝ) := by
        intro t ht
        simpa using
          (LipschitzWith.id.lipschitzOnWith (s := (Set.univ : Set ℝ)))
      have ht0 : (0 : ℝ) ∈ Set.Ioo (-h) h := by
        constructor <;> linarith [hpos]
      refine
        ODE_solution_unique_of_mem_Icc (v := fun _ y : ℝ => y)
          (s := fun _ => (Set.univ : Set ℝ)) (K := (1 : NNReal))
          (hv := hv) (ht := ht0) (hf := hcontg) (hf' := ?_)
          (hfs := ?_) (hg := hcontf) (hg' := ?_) (hgs := ?_) (heq := ?_)
      · intro t ht
        exact hgderiv t (Set.Ioo_subset_Icc_self ht)
      · intro t ht
        simp
      · intro t ht
        have ht' : t ∈ Set.Ioo (0 - h0) (0 + h0) := by
          have ht'' : t ∈ Set.Ioo (-h0) h0 := by
            have hneg : -h0 < -h := by linarith [hlt_h0]
            exact ⟨lt_of_lt_of_le hneg (Set.Ioo_subset_Icc_self ht).1,
              lt_of_le_of_lt (Set.Ioo_subset_Icc_self ht).2 hlt_h0⟩
          simpa using ht''
        simpa [F] using (hfderiv t ht')
      · intro t ht
        simp
      · simp [hg0, hf0]
    exact hEqOn

/-- The exponential is the unique globally defined solution of the ODE
`f' = f` satisfying `f 0 = 1`. -/
lemma exp_unique_solution :
    ∃! f : ℝ → ℝ,
      (∀ x : ℝ, HasDerivAt f (f x) x) ∧ f 0 = 1 := by
  refine ⟨Real.exp, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      simpa using (Real.hasDerivAt_exp x)
    · simp
  · intro g hg
    have hgderiv : ∀ x : ℝ, HasDerivAt g (g x) x := hg.1
    have hg0 : g 0 = 1 := hg.2
    funext x
    let a : ℝ := min x 0 - 1
    let b : ℝ := max x 0 + 1
    have ht0 : (0 : ℝ) ∈ Set.Ioo a b := by
      have ha : a < 0 := by
        have hmin : min x 0 ≤ 0 := min_le_right _ _
        linarith [hmin]
      have hb : 0 < b := by
        have hmax : 0 ≤ max x 0 := le_max_right _ _
        linarith [hmax]
      exact ⟨ha, hb⟩
    have hv :
        ∀ t : ℝ, t ∈ Set.Ioo a b →
          LipschitzOnWith (1 : NNReal) (fun y : ℝ => y) (Set.univ : Set ℝ) := by
      intro t ht
      simpa using
        (LipschitzWith.id.lipschitzOnWith (s := (Set.univ : Set ℝ)))
    have hcontg : ContinuousOn g (Set.Icc a b) := by
      intro t ht
      exact (hgderiv t).continuousAt.continuousWithinAt
    have hcontexp : ContinuousOn Real.exp (Set.Icc a b) := by
      intro t ht
      exact (Real.hasDerivAt_exp t).continuousAt.continuousWithinAt
    have hEqOn : Set.EqOn g Real.exp (Set.Icc a b) := by
      refine
        ODE_solution_unique_of_mem_Icc (v := fun _ y : ℝ => y)
          (s := fun _ => (Set.univ : Set ℝ)) (K := (1 : NNReal))
          (hv := hv) (ht := ht0) (hf := hcontg) (hf' := ?_) (hfs := ?_)
          (hg := hcontexp) (hg' := ?_) (hgs := ?_) (heq := ?_)
      · intro t ht
        simpa using (hgderiv t)
      · intro t ht
        simp
      · intro t ht
        simpa using (Real.hasDerivAt_exp t)
      · intro t ht
        simp
      · simp [hg0]
    have hx : x ∈ Set.Icc a b := by
      constructor
      · have hmin : min x 0 ≤ x := min_le_left _ _
        linarith [hmin]
      · have hmax : x ≤ max x 0 := le_max_left _ _
        linarith [hmax]
    exact hEqOn hx

lemma one_sub_ne_zero_of_lt {x : ℝ} (hx : x < 1) : (1 - x) ≠ 0 := by
  exact ne_of_gt (sub_pos.mpr hx)

lemma hasDerivAt_inv_one_sub {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun x : ℝ => (1 - x)⁻¹) ((1 - x) ^ 2)⁻¹ x := by
  have h_inv :
      HasDerivAt (fun y : ℝ => y⁻¹) (-( (1 - x) ^ 2)⁻¹) (1 - x) := by
    simpa using (hasDerivAt_inv (x := 1 - x) (one_sub_ne_zero_of_lt hx))
  have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := by
    simpa using (hasDerivAt_const x (1 : ℝ))
  have h_sub : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using h_const.sub (hasDerivAt_id x)
  simpa using h_inv.comp x h_sub

/-- Example 6.3.4: For the ODE `f' = f ^ 2` with initial condition `f 0 = 1`,
the solution is `f x = (1 - x)⁻¹`, defined on the interval `(-∞, 1)`. The
nonlinearity `y ↦ y^2` is not globally Lipschitz, so the guaranteed existence
interval from Picard's theorem shrinks as the initial value approaches `x = 1`.
-/
lemma quadratic_ode_example :
    ∃ f : ℝ → ℝ,
      (∀ x, x < (1 : ℝ) → HasDerivAt f ((f x) ^ 2) x) ∧
        f 0 = 1 ∧ ∀ x, x < (1 : ℝ) → f x = (1 - x)⁻¹ := by
  refine ⟨fun x => (1 - x)⁻¹, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    have hderiv :
        HasDerivAt (fun x : ℝ => (1 - x)⁻¹) ((1 - x) ^ 2)⁻¹ x :=
      hasDerivAt_inv_one_sub hx
    simpa [inv_pow] using hderiv
  · refine ⟨?_, ?_⟩
    · simp
    · intro x hx
      simp

/-- Example 6.3.5: For the initial value problem `f' x = 2 * √|f x|` with
`f 0 = 0`, the right-hand side `F x y = 2 * √|y|` is continuous but not
Lipschitz in `y`, so uniqueness can fail. The piecewise function
`f x = x^2` for `x ≥ 0` and `f x = -x^2` for `x < 0` is a solution, while the
zero function is another, so a solution exists but is not unique. -/
lemma sqrt_abs_ode_nonunique :
    ∃ f g : ℝ → ℝ,
      f ≠ g ∧ f 0 = 0 ∧ g 0 = 0 ∧
        (∀ x, HasDerivAt f (2 * Real.sqrt (|f x|)) x) ∧
        (∀ x, HasDerivAt g (2 * Real.sqrt (|g x|)) x) := by
  have sqrt_abs_mul_abs (x : ℝ) : Real.sqrt (|x * (|x|)|) = |x| := by
    calc
      Real.sqrt (|x * (|x|)|) = Real.sqrt (|x| * |x|) := by
        simp [abs_mul, abs_abs]
      _ = |x| := by
        simpa using (Real.sqrt_mul_self (abs_nonneg x))
  have hasDerivAt_mul_abs_ne_zero {x : ℝ} (hx : x ≠ 0) :
      HasDerivAt (fun x => x * |x|) (2 * |x|) x := by
    rcases lt_or_gt_of_ne hx with hxlt | hxgt
    · have hmul :
        HasDerivAt (fun x => x * |x|) (1 * |x| + x * (-1)) x :=
        (hasDerivAt_id x).mul (hasDerivAt_abs_neg hxlt)
      simpa [abs_of_neg hxlt, two_mul] using hmul
    · have hmul :
        HasDerivAt (fun x => x * |x|) (1 * |x| + x * 1) x :=
        (hasDerivAt_id x).mul (hasDerivAt_abs_pos hxgt)
      simpa [abs_of_pos hxgt, two_mul] using hmul
  have hasDerivAt_mul_abs_zero : HasDerivAt (fun x : ℝ => x * |x|) 0 0 := by
    have h_abs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    have h_abs' : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 (0 : ℝ)) :=
      h_abs.mono_left nhdsWithin_le_nhds
    have h_eq : (fun t : ℝ => t⁻¹ * (t * |t|)) = fun t => |t| := by
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · simp [ht]
    refine (hasDerivAt_iff_tendsto_slope_zero).2 ?_
    simpa [h_eq] using h_abs'
  refine ⟨fun x => x * |x|, fun _ => 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : (1 : ℝ) = 0 := by
      simpa using congrArg (fun h => h 1) h
    exact one_ne_zero h1
  · simp
  · simp
  · intro x
    by_cases hx : x = 0
    · subst hx
      simpa using hasDerivAt_mul_abs_zero
    · simpa [Real.sqrt_mul_self_eq_abs] using (hasDerivAt_mul_abs_ne_zero (x := x) hx)
  · intro x
    simpa using (hasDerivAt_const x (0 : ℝ))

/-- Example 6.3.6: Let `φ x = 0` when `x` is rational and `φ x = 1` otherwise.
The ODE `y' = φ` has no solution for any initial condition, since the
right-hand side is discontinuous and derivatives have the Darboux property,
so no differentiable function can have `φ` as its derivative. -/
noncomputable def dirichletPhi : ℝ → ℝ := by
  classical
  exact fun x =>
    if x ∈ Set.range (fun r : ℚ => (r : ℝ)) then (0 : ℝ) else 1

lemma dirichletPhi_value_rational {x : ℝ}
    (hx : x ∈ Set.range (fun r : ℚ => (r : ℝ))) :
    dirichletPhi x = 0 := by
  classical
  simp [dirichletPhi, hx]

lemma dirichletPhi_value_irrational {x : ℝ}
    (hx : x ∉ Set.range (fun r : ℚ => (r : ℝ))) :
    dirichletPhi x = 1 := by
  classical
  simp [dirichletPhi, hx]

lemma deriv_eq_dirichletPhi_of_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (h : HasDerivAt f (dirichletPhi x) x) :
    deriv f x = dirichletPhi x := by
  simpa using h.deriv

lemma exists_irrational_in_Ioo_0_1 : ∃ b, 0 < b ∧ b < 1 ∧ Irrational b := by
  rcases exists_irrational_btwn (show (0 : ℝ) < 1 by norm_num) with ⟨b, hb, hb0, hb1⟩
  exact ⟨b, hb0, hb1, hb⟩

/-- No differentiable function can solve the discontinuous ODE `y' = φ` where
`φ` is the Dirichlet function. In particular, there is no solution satisfying
any prescribed initial value. -/
lemma no_solution_dirichlet_ode :
    ¬ ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∀ x, HasDerivAt f (dirichletPhi x) x := by
  classical
  rintro ⟨f, hf, hderiv⟩
  rcases exists_irrational_in_Ioo_0_1 with ⟨b, hb0, hb1, hb_irr⟩
  have hdiff : DifferentiableOn ℝ f (Set.Icc 0 b) := hf.differentiableOn
  have hfa : DifferentiableAt ℝ f 0 := hf.differentiableAt
  have hfb : DifferentiableAt ℝ f b := hf.differentiableAt
  have h0mem : (0 : ℝ) ∈ Set.range (fun r : ℚ => (r : ℝ)) := ⟨0, by simp⟩
  have hdir0 : dirichletPhi 0 = 0 := dirichletPhi_value_rational h0mem
  have hb' : b ∉ Set.range (fun r : ℚ => (r : ℝ)) := by
    simpa [Irrational] using hb_irr
  have hdirb : dirichletPhi b = 1 := dirichletPhi_value_irrational hb'
  have hderiv0 : deriv f 0 = 0 := by
    have h' : deriv f 0 = dirichletPhi 0 :=
      deriv_eq_dirichletPhi_of_hasDerivAt (hderiv 0)
    simpa [hdir0] using h'
  have hderivb : deriv f b = 1 := by
    have h' : deriv f b = dirichletPhi b :=
      deriv_eq_dirichletPhi_of_hasDerivAt (hderiv b)
    simpa [hdirb] using h'
  have hy : deriv f 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < deriv f b := by
    constructor
    · have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      simp [hderiv0]
    · have : (1 / 2 : ℝ) < (1 : ℝ) := by norm_num
      simpa [hderivb] using this
  obtain ⟨c, hc, hderivc⟩ :=
    darboux_deriv (a := 0) (b := b) (y := (1 / 2 : ℝ)) hb0 hdiff hfa hfb (Or.inl hy)
  have hdirc : dirichletPhi c = (1 / 2 : ℝ) := by
    calc
      dirichletPhi c = deriv f c := by
        simpa using (deriv_eq_dirichletPhi_of_hasDerivAt (hderiv c)).symm
      _ = (1 / 2 : ℝ) := hderivc
  by_cases hcrat : c ∈ Set.range (fun r : ℚ => (r : ℝ))
  · have hdirc0 : dirichletPhi c = 0 := dirichletPhi_value_rational hcrat
    have hcontra : (0 : ℝ) ≠ (1 / 2 : ℝ) := by norm_num
    have hdirc' := hdirc
    simp [hdirc0] at hdirc'
  · have hdirc1 : dirichletPhi c = 1 := dirichletPhi_value_irrational hcrat
    have hcontra : (1 : ℝ) ≠ (1 / 2 : ℝ) := by norm_num
    have hdirc' := hdirc
    simp [hdirc1] at hdirc'

end Section03
end Chap06
